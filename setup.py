#from Cython.Build import cythonize
#from Cython.Distutils import build_ext
from setuptools import setup, find_packages
from distutils.core import Extension

dependency_links = []
install_requires = []

with open('requirements.txt') as f:
    for line in f:
        if line.startswith("#"):
            continue
        if '#egg=' in line:
            dependency_links.append(line)
            continue
        install_requires.append(line)

exts = [
    Extension('proto', sources=['fsmipmi/proto.pyx']),
]

setup(
    name='python-fsmipmi',
    version='0.1',
    description='Finite State Machine IPMI library for Python',
    author='Anton D. Kachalov',
    packages=find_packages(),
    scripts=['fsmitool'],
#    ext_package='fsmipmi',
#    ext_modules=cythonize(exts),
    platforms='any',
    zip_safe=False,
    include_package_data=True,
    dependency_links=dependency_links,
    install_requires=install_requires,
)
