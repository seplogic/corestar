#!/bin/bash

if [ "$UID" -ne "0" ]; then
    echo "This script should be run as root"
    exit 1
fi

if [ -z "$CORESTAR_HOME" ]; then
    echo "CORESTAR_HOME is not set. Please source setenv first."
    exit 1
fi

SCRIPTS=$CORESTAR_HOME/scripts
Z3_URL="http://www0.cs.ucl.ac.uk/staff/J.Villard/pub/z3-e79e1830180c926e231d3c1c6411566e70c0de46.zip"
Z3_ZIP="z3.zip"
TMP=$(mktemp -d)

echo $TMP
cd $TMP

echo "Downloading..."
wget $Z3_URL -O $Z3_ZIP
echo "Extracting..."
unzip $Z3_ZIP
# dos2unix ./configure
tr -d '\r' < configure > configure.unix
cat configure.unix > configure

echo "Building Z3..."
./configure && cd build && make -j 8 && make install
ldconfig

cd .. && ./configure --ml && cd build && make ml
cd ../build/api/ml
cp $SCRIPTS/META.z3 META
ocamlfind install z3 META libz3ml.a z3.a z3.cmi z3.cmx z3enums.cmi z3enums.cmx z3enums.mli z3native.c z3native.cmo z3native.o z3.cma z3.cmo z3.cmxa z3enums.cmo z3enums.o z3.mli z3native.cmi z3native.cmx z3native.mli z3.o
