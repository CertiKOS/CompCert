#!/bin/bash
cp -r ../compcert ../compcertElf ;
cd ../compcertElf ;
make clean ;
rm -rf .git/ ;
rm pack.sh ;
cd .. ;
#tar -cvf compcertElf.tar compcertElf/ ;
zip -r compcertElf.zip compcertElf;
echo "Pack finished"
