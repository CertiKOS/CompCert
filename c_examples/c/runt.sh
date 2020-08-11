#!/bin/sh
for ef in $(ls *.out)
do  
    ./$ef
    echo $?
done
