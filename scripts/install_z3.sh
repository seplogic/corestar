#!/bin/bash

echo "I need root access to install Z3's shared lib."
sudo echo "Thanks."

Z3_URL="https://github.com/Z3Prover/z3/archive/z3-4.4.1.zip"
Z3_ZIP="z3.zip"
TMP=$(mktemp -d)

echo "Working in $TMP"
cd $TMP

echo "Downloading ..."
wget -nv $Z3_URL -O $Z3_ZIP
unzip -q $Z3_ZIP
rm $Z3_ZIP
cd *

echo "Building Z3. This will take a few minutes ..."
./configure > $TMP/0.log && \
cd build && make -j $(nproc) > $TMP/1.log && \
echo "  Installing shared libraries." && \
sudo make install > $TMP/2.log && \
sudo ldconfig && cd .. && \
echo "  Now compiling for OCaml API ..." && \
./configure -p $HOME --ml > $TMP/3.log && \
cd build && make -j $(nproc) > $TMP/4.log && \
make install > $TMP/5.log && \
echo "Done. All OK."
