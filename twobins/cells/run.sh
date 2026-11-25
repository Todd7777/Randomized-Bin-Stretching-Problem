#!/bin/bash
# bash run.sh: checks the 85 cells of the bound 1183/1000 for three policies on two bins
cd "$(dirname "$0")"; B=1183/1000
python3 -I -B covP1.py $B s3/*.s3 | tail -1
python3 -I -B covP2.py $B s3/*.s3 | tail -1
python3 -I -B mycover.py s3/*.s3 | tail -1
python3 -I -B chk3a.py s3/*.s3 | tail -1
python3 -I -B chk3b.py s3/*.s3 | tail -1
python3 -I -B vchk_k.py --bound $B s3/*.s3 | tail -1
python3 -I -B mychk.py $B s3/*.s3 | tail -1
T=$(mktemp -d); g++ -O2 -std=c++17 -o $T/gcheck ../gcheck.cpp
for f in s3/*.s3; do
  b=$T/$(basename $f .s3); python3 -I -B s3_to_gridcert.py $f $b > /dev/null
  k=$(( $(head -1 $f | cut -d' ' -f2) + 5 ))
  tail -n +2 $b.v0.cert | awk -v k=$k '{$k=""; print}' > $T/m
  s="same moves"
  for c in $b.v*.cert; do
    $T/gcheck $c | cut -d' ' -f1
    tail -n +2 $c | awk -v k=$k '{$k=""; print}' | cmp -s - $T/m || s="different moves"
  done
  echo "$s"
done | sort | uniq -c
rm -rf $T
