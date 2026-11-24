#!/bin/bash
# bash run.sh OUT: builds the four lazy trees and checks each with both checkers
cd "$(dirname "$0")"; O=$1; mkdir -p $O
for m in hedge:hedge late:late aB:Bclosed Ab:Aclosed; do
  a=${m%%:*}; f=$O/${m##*:}.jsonl
  python3 ltprod.py $a $f - 1000000 64 > /dev/null
  echo "$a $(python3 ltcheck.py $a $f | grep -o 'RESULT [A-Z]*') $(python3 vcheck.py $a $f | grep -o 'RESULT [A-Z]*')"
done
