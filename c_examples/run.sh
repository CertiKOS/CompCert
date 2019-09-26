#!/bin/sh
for ef in $(ls *.o)
do  
    ./$ef
    echo "$ef:" $?
done
