import os
import logging
from struct import pack, unpack
from hashlib import md5
from random import random
from Crypto.Cipher import AES
from Crypto.Hash import HMAC, SHA

from fsmsock import proto

def __generate_crc16_table():
    ''' Generates a crc16 lookup table

    .. note:: This will only be generated once
    '''
    result = []
    for byte in range(256):
        crc = 0x0000
        for bit in range(8):
            if (byte ^ crc) & 0x0001:
                crc = (crc >> 1) ^ 0xa001
            else: crc >>= 1
            byte >>= 1
        result.append(crc)
    return result

__crc16_table = __generate_crc16_table()

def computeCRC(data):
    ''' Computes a crc16 on the passed in string. For modbus,
    this is only used on the binary serial protocols (in this
    case RTU).

    The difference between modbus's crc16 and a normal crc16
    is that modbus starts the crc value out at 0xffff.

    :param data: The data to create a crc16 of
    :returns: The calculated CRC
    '''
    crc = 0xffff
    for a in data:
        idx = __crc16_table[(crc ^ a) & 0xff];
        crc = ((crc >> 8) & 0xff) ^ idx
    swapped = ((crc << 8) & 0xff00) | ((crc >> 8) & 0x00ff)
    return swapped

class IpmiUdpClient(proto.base.UdpTransport):
    PAYLOAD_IPMI = 0x00
    PAYLOAD_SOL = 0x01
    PAYLOAD_RMCPPLUSOPENREQ = 0x10
    PAYLOAD_RMCPPLUSOPENRESPONSE = 0x11
    PAYLOAD_RAKP1 = 0x12
    PAYLOAD_RAKP2 = 0x13
    PAYLOAD_RAKP3 = 0x14
    PAYLOAD_RAKP4 = 0x15

    rmcp_codes = {
        1: ("Insufficient resources to create new session (wait for existing "
            "sessions to timeout)"),
        2: "Invalid Session ID",
        3: "Invalid payload type",
        4: "Invalid authentication algorithm",
        5: "Invalid integrity algorithm",
        6: "No matching integrity payload",
        7: "No matching integrity payload",
        8: "Inactive Session ID",
        9: "Invalid role",
        0xa: "Unauthorized role or privilege level requested",
        0xb: "Insufficient resources to create a session at the requested role",
        0xc: "Invalid username length",
        0xd: "Unauthorized name",
        0xe: "Unauthorized GUID",
        0xf: "Invalid integrity check value",
        0x10: "Invalid confidentiality algorithm",
        0x11: "No Cipher suite match with proposed security algorithms",
        0x12: "Illegal or unrecognized parameter",
    }

    def __init__(self, host, interval, user='ADMIN', passwd='ADMIN', cmds=[], vendors={}, sdrs=()):
        self._userid = bytes(user, 'ascii')
        self._useridb = unpack('%dB' % len(self._userid), self._userid)
        self._passwd = bytes(passwd, 'ascii')
        self._kg = self._passwd
        self._send = None
        self._recv = None
        self._padval = tuple(range(1, 16))
        self._cmdidx = 0
        self._cmds = list(cmds)
        self._sdrs = sdrs
        self._vendors = vendors
        super().__init__(host, interval, port=623)

    def __str__(self):
        return 'IPMI({0},{1},{2},{3})'.format(self._host, self._interval, self._state, self._expire)

    def _initsession(self):
        self._logged = False
        self.__random = ()
        self._localsid = unpack('>I', b'YNDX')[0]-1
        self._privlevel = 4 # admin access
        self._confalgo = 0
        self._aeskey = None
        self._integrityalgo = 0
        self._k1 = None
        self._k2 = None
        self._rmcptag = 1
        self._sessionid = b'\x00'*4
        self._authtype = 0
        self._seqlun = 0
        self._sequencenumber = 0
        self._ipmiversion = 1.5
        self._ipmi15only = False
        self._ver = 0
        self._mfg = -1
        self._prod = -1
        self._builtin_sdr = False
        self._sdr_cached = False
        self._rqaddr = 0x81 # per IPMI table 5-4, software ids in the ipmi spec may
                            # be 0x81 through 0x8d.  We'll stick with 0x81 for now,
                            # do not forsee a reason to adjust
        self._cmdidx = 0
        self._send = self._get_channel_auth_cap
        self._recv = None

    def send_buf(self):
#        logging.debug("SEND BUF %s", self._send)
        if self._send != None:
            return self._send()
        return 0

    def process_data(self, data, tm = None):
        self._retries = 0
        if len(data) == 0:
            return False

        self._state = self.READY

        if not (data[0] == 0x06 and data[2] == 0xff and data[3] == 0x07):
            # not valid IPMI
            logging.warning("{0}: Not valid IPMI".format(self._host))
            return False
        if data[4] == 0x00 or data[4] == 0x02:
            # IPMI v1.5
            seqnumber = unpack('<I', data[5:9])[0]
            # check remote seqnumber
            if data[4] != self._authtype:
                # logout
                # BMC responded with mismatch authtype, for the sake of
                # mutual authentication reject it. If this causes 
                # legitimate issues, it's the vendor's fault
                return False
            if self._sessionid != data[9:13]:
                return False
            if data[4] == 0x02:
                authcode = data[13:29]
                sz = data[30]+30
                payload = bytes(unpack('!%dB' % data[29], data[30:sz]))
            else:
                authcode = False
                sz = data[13]+14
                payload = bytes(unpack('!%dB' % data[13], data[14:sz]))
            # TODO: check ipmi15authcode
        elif data[4] == 0x06:
            # IPMI v2.0
            ptype = data[5] & 0b00111111
            if ptype == self.PAYLOAD_RMCPPLUSOPENRESPONSE:
                return self._got_rmcp_response(data)
            elif ptype == self.PAYLOAD_RAKP2:
                return self._got_rakp2(data)
            elif ptype == self.PAYLOAD_RAKP4:
                return self._got_rakp4(data)
            elif ptype == 0: # good old ipmi payload
                # If I'm endorsing a shared secret scheme, then at the very least it
                # needs to do mutual assurance
                if not (data[5] & 0b01000000): # This would be the line that might 
                                               # trip up some insecure BMC 
                                               # implementation
                    return False
                encrypted = 0
                if data[5] & 0b10000000:
                    encrypted = 1
                authcode = data[-12:]
                if self._k1 == None:
                    self._relog()
                    return False
                expectedauthcode = HMAC.new(self._k1, data[4:-12], SHA).digest()[:12]
                if authcode != expectedauthcode:
                    return False #BMC failed to assure integrity to us, drop it
                sid = unpack('<I', data[6:10])[0]
                if sid != self._localsid: #session id mismatch, drop it
                    return False
                #remseqnumber = unpack('<I',rawdata[10:14])[0]
                #if (hasattr(self,'remseqnumber') and 
                #    (remseqnumber < self.remseqnumber) and 
                #    (self.remseqnumber != 0xffffffff)): 
                #    return
                #self.remseqnumber=remseqnumber
                psize = data[14] + (data[15] << 8)
                payload = data[16:16 + psize]
                if encrypted:
                    iv = data[16:32]
                    decrypter = AES.new(self._aeskey,AES.MODE_CBC,iv)
                    payload = decrypter.decrypt(pack('%dB' % len(payload[16:]),
                                                       *payload[16:]))
            else:
                logging.warning("{0}: wrong packet, ptype={1:>#8b}".format(self._host, data[5]))
                return False

        self._seqlun += 4
        self._seqlun &= 0xff

        if self._recv == None:
            return False

        if self._recv(payload):
            return True

        # We're done
        self.stop()
        return False

    def _checksum(self, data): # Two's complement over the data
        csum = sum(data)
        csum = csum ^ 0xff
        csum += 1
        return (csum & 0xff)

    def _make_ipmi_payload(self, netfn, command, data=()):
        seqinc = 7 # IPMI spec forbids gaps bigger than 7 in seq number.
                   # Risk the taboo rather than violate the rules
        # while ((netfn,command,self._seqlun
        header = [0x20, netfn << 2] #figure 13-4, first two bytes are rsaddr and 
                               #netfn, rsaddr is always 0x20 since we are 
                               #addressing BMC
        reqbody = [self._rqaddr, self._seqlun, command]
        reqbody.extend(data)
        headsum = self._checksum(header)
        bodysum = self._checksum(reqbody)
        header.append(headsum)
        header.extend(reqbody)
        header.append(bodysum)
#        logging.debug("IPMI: %02X %02X [%s]" % (netfn, command, reqbody))
        return header

    sdr_types = ( 0x01, 0x04, 0x08 )

    def _got_next_cmd(self, response):
        tm = self._expire - self._interval
#        logging.debug("data:", list(response[5:]))
        self._cmds[self._cmdidx][4](self, response, tm)
        if len(self._cmds) > 0:
            self._cmdidx = (self._cmdidx + 1) % len(self._cmds)
        return not (self._cmdidx == 0)

    def _process_next_cmd(self):
        self._recv = self._got_next_cmd
        if not len(self._cmds):
            self.stop()
            return True
        cmd = self._cmds[self._cmdidx]
#        logging.debug("{0}: RAW command {1} {2}".format(self._host, self._cmdidx, cmd))
        return self._send_ipmi_net_payload(cmd[1], cmd[2], cmd[3])

    def _sdr_is_valid(self, resp):
        return resp[6] == 0 and (resp[8] & 0x20) != 0x20 and (resp[8] & 0x40) == 0x40


    @staticmethod
    def _cmd_got_sessinfo(obj, response, tm):
#        if not obj._sdr_is_valid(response) != 0:
#            return True
#        obj._l.debug("%s %s" % (obj._cmds[obj._cmdidx][0], response[7:]))
        obj.on_data(obj._cmds[obj._cmdidx][0], response[9] & 1, tm)
        return True

    @staticmethod
    def _cmd_got_sensor_reading(obj, resp, tm):
#        obj._l.debug("%s: got READING: %02x %02x V:%x" % (obj._host, resp[6], resp[8], resp[7]))
        if not obj._sdr_is_valid(resp) != 0:
            return True
        t,l,m,b,k2,k1 = obj._cmds[obj._cmdidx][5:]
        val = resp[7]
        result = 0.0
        if t == 1:
            if val & 0x80: val += 1
        if t > 0:
            # make int8_t from uint8_t
            val = unpack('b', pack('B', val))[0]
        if t > 2:
            # Oops! This isn't an analog sensor
            return True
        result = ((m * val) + (b * pow(10, k1))) * pow(10, k2)
#        obj._l.debug("%s %d %lu" % (obj._cmds[self._cmdidx][0], result, tm))
        obj.on_data(obj._cmds[obj._cmdidx][0], result, tm)
        return True

    def _next_sdr_or_cmd(self):
        if not self._sdr_cached:
            self._sdr_idx += 1
            self._sdr_recid = self._sdr_nextid
            process_cmd = self._sdr_idx == self._sdr[2]
        else:
            process_cmd = False
        if process_cmd:
            self._sdr_idx = 0
            self._sdr_cached = True
            self._send = self._process_next_cmd
        else:
            self._send = self._get_sdr_header

    def _got_sdr_record(self, record):
        self._next_sdr_or_cmd()
#        if record[6] != 0:
#            return True
#        logging.debug("%s: SDR <%d> type=%x" % (self._host, len(record), record[17]))
        if len(record) < 58 or not record[17] in self.sdr_types:
            return True
        size = record[51] & 0x1f
        # FIXME: sensor number is not supported (id_code=0)
        name = str(record[52:52+size].upper(), 'ascii')
#        logging.debug("%s: SDR [%s]" % (self._host, name))
        x = self._sdrs.get(name, None)
        if not x == None:
            self.sdr = (name, x)
        else:
            return True
#        logging.debug("REC: owner_id/target=%02x lun=%02x num=%02x unit=%02x linear=%02x mtol=%04x bacc=%x" % (record[9], record[10], record[11], record[24], record[27], unpack('<H', record[28:30])[0], unpack('<I', record[30:34])[0]), record[23:])

        def tos32(val, bits):
            return ((-((val) & (1<<((bits)-1))) | (val)) if (val & ((1<<((bits)-1)))) else (val))

        mtol = unpack('>H', record[28:30])[0]
        bacc = unpack('>I', record[30:34])[0]
        self._cmds.append((self.sdr[1], 0x4, 0x2d,
            # number
            (record[11],),
            # callback function
            IpmiUdpClient._cmd_got_sensor_reading,
            # unit
            record[24] >> 6,
            # linear
            record[27] & 0x7f,
            # __TO_M
            tos32((((mtol & 0xff00) >> 8) | ((mtol & 0xc0) << 2)), 10),
            # __TO_B
            tos32((((bacc & 0xff000000) >> 24) | ((bacc & 0xc00000) >> 14)), 10),
            # __TO_R_EXP
            tos32(((bacc & 0xf0) >> 4), 4),
            # __TO_B_EXP
            tos32((bacc & 0xf), 4)))
        return True

    def _get_sdr_record(self):
        self._recv = self._got_sdr_record
        payload = pack('<2H2B', self._sdr[3], self._sdr_recid, 5, self._sdr_len)
        return self._send_ipmi_net_payload(self._sdr[0], self._sdr[1], payload)

    def _got_sdr_header(self, header):
#        if header[6] != 0:
#            return True
#        logging.debug("%s: got SDR HEADER <%x>" % (self._host, header[12]))
        if header[12] != 0x01: # SDR_RECORD_TYPE_FULL_SENSOR
            self._sdr_nextid = unpack('<H', header[7:9])[0]
            self._next_sdr_or_cmd()
#            logging.debug("NEXT: %02x %02x" % (self._sdr_idx, self._sdr[2]), self._sdr_idx, header[5:], len(header[5:]))
            return True
#        logging.debug("HDR: %02x len=%02d %02x" % (header[12], header[13], self._sdr_recid), header[5:], len(header[5:]))
        self._sdr_len = header[13]
        self._sdr_nextid = unpack('<H', header[7:9])[0]
        self._send = self._get_sdr_record
        return True

    def _get_sdr_header(self):
        self._recv = self._got_sdr_header
        payload = pack('<2H2B', self._sdr[3], self._sdr_recid, 0, 5)
        return self._send_ipmi_net_payload(self._sdr[0], self._sdr[1], payload)

    def _got_sdr_reserve(self, response):
        self._sdr[3] = unpack('<H', response[7:9])[0]
#        logging.debug(("RES: %02x" % self._sdr[3]), response[5:])
#        logging.debug("%s: got SDR RESERVE <%d> %s" % (self._host, self._sdr[3], self._sdr_cached))
        if not self._sdr_cached: # and response[6] == 0:
            self._sdr_recid = 0
            self._sdr_idx = 0
            self._send = self._get_sdr_header
        else:
            self._send = self._process_next_cmd
        return True

    def _get_sdr_reserve(self):
        self._recv = self._got_sdr_reserve
        return self._send_ipmi_net_payload(self._sdr[0], 0x22)

    def _got_sdr_info(self, repo):
        self._sdr[2] = unpack('<H', repo[8:10])[0]
#        logging.debug("%s: got SDR INFO <%d>" % (self._host, self._sdr[2]))
        self._send = self._get_sdr_reserve
        return True

    def _get_sdr_info(self):
        self._recv = self._got_sdr_info
        return self._send_ipmi_net_payload(self._sdr[0], 0x20)

    def timeouted(self, tm = None):
        rc = super().timeouted(tm)
        if rc and len(self._cmds) > 0:
#             logging.debug('%s: timeouted (%s) %d!' % (self._tag, self._host, tm))
             self._cmdidx = (self._cmdidx + 1) % len(self._cmds)
        return rc

    def _got_product_id(self, response):
        if (response[8] & 0x80) == 1:
            if (response[12] & 0x02) == 0:
                self._builtin_sdr = (response[12] & 0x01) == 1
        if self._builtin_sdr:
                        # Func  Rec   Cnt   Rsvd
            self._sdr = [ 0x04, 0x21, 0x00, 0x00 ]
        else:
            self._sdr = [ 0x0a, 0x23, 0x00, 0x00 ]
        self._ver  = unpack('>H', response[9:11])[0]
        self._mfg  = unpack('<I', response[13:16]+b'\x00')[0]
        self._prod = unpack('<H', response[16:18])[0]
#        logging.debug("Ver:", self._ver, "Mfg:", self._mfg, "Prod:", self._prod)
        cmd = self._vendors.get((self._mfg, self._prod))
        if cmd != None:
            self._cmds.extend(cmd)
        # WRND: extend command list with 'session.info' command
#        self._cmds.extend((('session.info', 0x06, 0x3d, unpack('!5B', b'\xff' + self._sessionid), IpmiUdpClient._cmd_got_sessinfo),))

        if len(self._sdrs):
            self._send = self._get_sdr_info
        else:
            self._send = self._process_next_cmd
        self._cmdidx = 0
        return True

    def _get_product_id(self):
        self._recv = self._got_product_id
        return self._send_ipmi_net_payload(0x6, 0x1)

    def _got_priv_level(self, response):
        # errstr=get_ipmi_error(response,suffix=mysuffix)
        self._logged = True
        if len(self._vendors) or len(self._sdrs):
            self._send = self._get_product_id
        else:
            self._send = self._process_next_cmd
        return True

    def _req_priv_level(self):
        self._recv = self._got_priv_level
        return self._send_ipmi_net_payload(0x6, 0x3b, (self._privlevel,))

    def _got_rakp4(self, data):
        if data[16] != self._rmcptag:
            # use rmcp tag to track and reject stale responses
            logging.warning("!rmcptag")
            return False
        if data[17] != 0:
            if data[17] == 2: # and self.logontries:
                # if we retried RAKP3 because 
                # RAKP4 got dropped, BMC can consider it done and we must restart
                self._relog()
                return False
            if data[17] == 8:
                self._relog()
                return False
            if data[17] == 15: # and self.logontries:
                # ignore 15 value if we are 
                # retrying.  xCAT did but I can't recall why exactly
                # TODO(jbjohnso) jog my memory to update the comment
                return False

            logging.warning("%s %s %s %s" % (self._host, self._userid, "err_rakp4", self.rmcp_codes.get(data[17], 'Unrecognized RMCP code %d' % data[17])))
            return False

        localsid = unpack('<I', pack('4B', *data[20:24]))[0]
        if self._localsid != localsid:
            return False

        hmacdata = self._randombytes+\
            pack("<4B", *self._pendingsessionid)+\
            self._remoteguid
        expectedauthcode = HMAC.new(self._sik, hmacdata, SHA).digest()[:12]
        authcode = pack('%dB' % len(data[24:]), *data[24:])
        if authcode != expectedauthcode:
            logging.warning('Invalid RAKP4 integrity code (wrong Kg?)')
            return False

        self._sessionid = self._pendingsessionid
        self._integrityalgo='sha1'
        self._confalgo='aes'
        self._sequencenumber=1

        self._send = self._req_priv_level
        return True

    def _send_rakp3(self):
        self._rmcptag += 1
        #rmcptag, then status 0, then two reserved 0s
        payload = [self._rmcptag, 0, 0, 0]
        payload.extend(self._pendingsessionid)
        hmacdata = self._remoterandombytes+\
            pack("<I", self._localsid)+\
            pack("2B", self._privlevel, len(self._userid))+\
            self._userid
        authcode = HMAC.new(self._passwd, hmacdata, SHA).digest()
        payload.extend(unpack('%dB' % len(authcode), authcode))

        return self._pack_payload(payload, self.PAYLOAD_RAKP3)

    def _got_rakp2(self, data):
        if data[16] != self._rmcptag:
            # use rmcp tag to track and reject stale responses
            logging.warning("!rmcptag")
            return False
        if data[17] != 0: # response code
            if data[17] in (9, 0xd) and self._privlevel == 4:
                # Here the situation is likely that the peer didn't want
                # us to use Operator. Degrade to operator and try again
                self._initsession()
                self._privlevel = 3
                return True

            if data[17] == 2: # invalid sessionid 99% of the time means a retry
                              # scenario invalidated an in-flight transaction
                return False

            logging.warning('%s %s %s %s' % (self._host, self._userid, "err_rakp2", self.rmcp_codes.get(data[17], 'Unrecognized RMCP code %d' % data[17])))
            # data[17] === 13 -> incorrect password
            self._relog()
            return False

        localsid = unpack('<I', pack('4B', *data[20:24]))[0]
        if self._localsid != localsid:
            return False

        self._remoterandombytes = pack('16B',*data[24:40])
        self._remoteguid = pack('16B',*data[40:56])
        userlen = len(self._userid)
        hmacdata = pack("<I4B", localsid, *self._pendingsessionid)+\
            self._randombytes + self._remoterandombytes + self._remoteguid+\
            pack('2B', self._privlevel, userlen) +\
            self._userid
        expectedhash = HMAC.new(self._passwd, hmacdata, SHA).digest()
        givenhash = pack('%dB' % len(data[56:]),*data[56:])
        if givenhash != expectedhash:
            logging.warning("%s %s" % (self._host, "Incorrect password provided"))
            self._relog()
            return False

        #We have now validated that the BMC and client agree on password, time 
        #to store the keys

        self._sik = HMAC.new(self._kg,
                             self._randombytes + self._remoterandombytes +
                             pack('2B', self._privlevel, userlen)+
                             self._userid, SHA).digest()
        self._k1 = HMAC.new(self._sik, b'\x01'*20, SHA).digest()
        self._k2 = HMAC.new(self._sik, b'\x02'*20, SHA).digest()
        self._aeskey = self._k2[0:16]

        self._send = self._send_rakp3
        return True

    def _urandom(self, size):
        if len(self.__random) != size:
            self.__random = os.urandom(size)
        return self.__random

    def _send_rakp1(self):
        self._rmcptag += 1
        self._randombytes = self._urandom(16)
        payload = [self._rmcptag, 0, 0, 0]
        payload.extend(self._pendingsessionid)
        payload.extend(unpack('16B', self._randombytes))
        payload.extend([self._privlevel, 0, 0, len(self._useridb)])
        payload.extend(self._useridb)

        return self._pack_payload(payload, self.PAYLOAD_RAKP1)

    def _got_rmcp_response(self, response):
        if response[16] != self._rmcptag:
            # use rmcp tag to track and reject stale responses
            logging.warning("!rmcptag")
            return False
        if response[17] != 0: # response code
            logging.warning("%s %s %s %s" % (self._host, self._userid, "err_rmcp", self.rmcp_codes.get(response[17], 'Unrecognized RMCP code %d' % response[17])))
            # response[17] == 1 --> incorrect password
            self._relog()
            return False
        self._allowedpriv = response[18]
        localsid = unpack('<I', pack('4B', *response[20:24]))[0]
        if self._localsid != localsid:
            return False

        self._pendingsessionid = response[24:28]
        self._send = self._send_rakp1
        return True

    def _open_rmcpplus_request(self):
        self._authtype = 6
        self._localsid += 1
        self._rmcptag += 1
        data = [
            self._rmcptag,
            0, # request as much privilege as the channel will give us
            0, 0,
            ]
        data.extend(unpack('4B', pack('<I', self._localsid)))
        data.extend([
            0,0,0,8,1,0,0,0, #table 13-17, SHA-1
            1,0,0,8,1,0,0,0, #SHA-1 integrity
            2,0,0,8,1,0,0,0, #AES privacy
            #2,0,0,8,0,0,0,0, #no privacy confalgo
            ])
        return self._pack_payload(data, self.PAYLOAD_RMCPPLUSOPENREQ)

    def _got_channel_auth_cap(self, response):
        # netfn = response[1] >> 2
        # command = response[5]
        # code = response[6]
        # data = response[7:]
        if response[6] == 0xcc:
            #tried ipmi 2.0 against a 1.5 which should work, but some bmcs 
            #thought 'reserved' meant 'must be zero'
            self._ipmi15only = True
            self._send = self._get_channel_auth_cap
            return True

        # TODO: check IPMI error for (netfn, command)

        self._currentchannel = response[7]
        if response[8] & 0b10000000 and response[10] & 0b10: #ipmi 2.0 support
            self._ipmiversion = 2.0
        if self._ipmiversion == 1.5:
            if not (response[8] & 0b100):
                logging.warning("MD5 is required but not enabled/available on target BMC")
                return False
            self._send = self._get_session_challenge
        elif self._ipmiversion == 2.0:
            self._send = self._open_rmcpplus_request
        else:
            return False
        return True

    def _activated_session(self, data):
        self._sessionid = data[7+1:7+5]
        self._sequencenumber = unpack("<I", pack("4B", *data[7+5:7+9]))[0]
        self._send = self._req_priv_level
        return True

    def _activate_session(self):
        rqdata = [2,4]+list(self._challenge)+[1,0,0,0];
        #TODO(jbjohnso): this always requests admin level (1.5)
        self._recv = self._activated_session
        return self._send_ipmi_net_payload(0x6, 0x3a, rqdata)

    def _got_session_challenge(self, response):
        self._sessionid = response[7+0:7+4]
        self._authtype = 2
        self._challenge = response[7+4:-1]
        self._send = self._activate_session
        return True

    def _get_session_challenge(self):
        if len(self._userid) > 16:
            logging.error('Username too long for IPMI, must not exceed 16')
            return False
        padneeded = 16 - len(self._userid)
        reqdata = (2,) + unpack("!16B", self._userid + (b'\x00'*padneeded))
        self._recv = self._got_session_challenge 
        return self._send_ipmi_net_payload(0x6, 0x39, reqdata)

    def _get_channel_auth_cap(self):
        self._recv = self._got_channel_auth_cap
        if self._ipmi15only:
            return self._send_ipmi_net_payload(0x6, 0x38, (0x0e, self._privlevel))
        else:
            return self._send_ipmi_net_payload(0x6, 0x38, (0x8e, self._privlevel))

    def _send_ipmi_net_payload(self, netfn, command, data = ()):
        ipmipayload = self._make_ipmi_payload(netfn, command, data)
        payload_type = self.PAYLOAD_IPMI
        if self._integrityalgo:
            payload_type |=  0b01000000
        if self._confalgo:
            payload_type |=  0b10000000
        try:
          return self._pack_payload(ipmipayload, payload_type)
        except Exception as e:
          traceback.print_exc(file=sys.stdout)

    def _ipmi15authcode(self, payload, checkremotecode=False):
        if self._authtype == 0:  # Only for things prior to auth in ipmi 1.5, not
                                # like 2.0 cipher suite 0
            return ()
        password = self._passwd
        padneeded = 16 - len(password)
        if padneeded < 0:
            raise Exception("Password is too long for ipmi 1.5")
        password += b'\x00'*padneeded
        passdata = unpack("16B", password)
        if checkremotecode:
            seqbytes = unpack("!4B",pack("<I", self._remsequencenumber))
        else:
            seqbytes = unpack("!4B",pack("<I", self._sequencenumber))
        bodydata = list(passdata)
        bodydata.extend(self._sessionid)
        bodydata.extend(tuple(payload))
        bodydata.extend(seqbytes)
        bodydata.extend(passdata)
        dgst = md5(pack("%dB" % len(bodydata), *bodydata)).digest()
        hashdata = unpack("!%dB" % len(dgst), dgst)
        return hashdata

    def _pack_payload(self, payload=None, payload_type=None):
        if payload is None:
            payload = self._lastpayload
        if payload_type is None:
            payload_type = self._last_payload_type
        message = [0x6, 0, 0xff, 0x07] #constant RMCP header for IPMI
        baretype = payload_type & 0b00111111
        self._lastpayload = payload
        self._last_payload_type = payload_type
        message.append(self._authtype)
        if self._ipmiversion == 2.0:
            message.append(payload_type)
            if baretype == 2:
                return 0
#                raise Exception("TODO(jbjohnso): OEM Payloads")
            elif baretype == 1:
                return 0
#                raise Exception("TODO(jbjohnso): SOL Payload")
#            elif baretype not in payload_types.values():
#                raise Exception("Unrecognized payload type %d"%baretype)
            message.extend(self._sessionid)
        message.extend(unpack("!4B",pack("<I",self._sequencenumber)))
#        logging.debug("PACK_PAYLOAD",self._ipmiversion)
        if self._ipmiversion == 1.5:
            message.extend(self._sessionid)
            if not self._authtype == 0:
                message.extend(self._ipmi15authcode(payload))
            message.append(len(payload))
            message.extend(payload)
            totlen = 34 + len(message) #Guessing the ipmi spec means the whole 
                                       #packet and assume no tag in old 1.5 world
            if (totlen in (56,84,112,128,156)):
                message.append(0) #Legacy pad as mandated by ipmi spec
        elif self._ipmiversion == 2.0:
            psize = len(payload)
            if self._confalgo:
                pad = (psize+1) % 16 #pad has to account for one byte field as in
                                     #the _aespad function
                if pad: #if no pad needed, then we take no more action
                    pad = 16-pad
                newpsize = psize+pad+17 #new payload size grew according to pad 
                                        #size, plus pad length, plus 16 byte IV 
                                        #(Table 13-20)
                message.append(newpsize & 0xff)
                message.append(newpsize >> 8);
                iv = self._urandom(16) 
                message.extend(unpack('16B',iv))
                needpad = (len(payload) + 1) % 16
                if needpad:
                    needpad = 16 - needpad
                payload.extend(self._padval[0:needpad])
                payload.append(needpad)
                crypter = AES.new(self._aeskey, AES.MODE_CBC, iv)
                crypted = crypter.encrypt(pack('%dB' % len(payload),
                                               *payload))
                crypted = unpack('%dB' % len(crypted), crypted)
                message.extend(crypted)
            else: #no confidetiality algorithm
                message.append(psize & 0xff)
                message.append(psize >> 8);
                message.extend(payload)
            if self._integrityalgo: #see table 13-8, 
                                    #RMCP+ packet format 
                                    #TODO(jbjohnso): SHA256 which is now allowed
                neededpad=(len(message)-2) % 4
                if neededpad:
                    neededpad = 4 - neededpad
                message.extend([0xff]*neededpad)
                message.append(neededpad)
                message.append(7) #reserved, 7 is the required value for the 
                                  #specification followed
                integdata = message[4:]
                authcode = HMAC.new(self._k1,
                                    pack('%dB' % len(integdata),
                                         *integdata),
                                    SHA).digest()[:12] #SHA1-96 
                                        #per RFC2404 truncates to 96 bits
                message.extend(unpack('12B',authcode))
        self._netpacket = pack('!%dB' % len(message), *message)
        if self._sequencenumber: # seq number of zero will be left alone as it is
                                 # special, otherwise increment
            self._sequencenumber += 1
#        logging.debug("send: %s", self._netpacket)
        return self._write(self._netpacket)

    def connect(self):
        if self.connected() and not self.timeouted():
            return True

        if not super().connect():
            return False

        self._initsession()
        return True

    def disconnect(self):
        if self._logged:
            self._send_ipmi_net_payload(0x6, 0x3c, self._sessionid)
            self._logged = False
        super().disconnect()

    def _relog(self):
        self.disconnect()
        return True

    def on_data(self, point, val, tm):
        pass
