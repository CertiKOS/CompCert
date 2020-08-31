#!/bin/zsh

mkdir -p bench_result
rm -f bench_result/*
for i in $(seq 0 29)
do
    echo $i
    echo "make bench >bench_result/result_$i 2>&1"|sh
done
