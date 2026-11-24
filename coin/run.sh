#!/bin/bash
# bash run.sh CERTS OUT [JOBS]: both checkers on CERTS/{hedge,late,aB}.jsonl and CERTS/Ab/*.jsonl
cd "$(dirname "$0")"; C=$1; O=$2; N=${3:-8}; mkdir -p $O/1 $O/2
python3 -c 'import itertools,json;P={tuple(json.loads(l.split(" ",1)[1])) for l in open("parts.txt")};print("parts",P==set(itertools.product(*map(range,(2,2,2,4,2,4)))))'
python3 liftcheck.py root
for m in hedge late aB; do python3 liftcheck.py $m $C/$m.jsonl > $O/1/$m.txt; python3 mycheck.py their $m $C/$m.jsonl > $O/2/$m.txt; done
xargs -P $N -L 1 bash -c 'python3 liftcheck.py Ab '$C'/Ab/$0.jsonl "$1" > '$O'/1/Ab_$0.txt' < parts.txt
xargs -P $N -L 1 bash -c 'python3 mycheck.py their Ab '$C'/Ab/$0.jsonl "$1" > '$O'/2/Ab_$0.txt' < parts.txt
for d in 1 2; do echo "checker $d: $(cat $O/$d/*.txt | grep -c 'RESULT PASS') of 259 PASS"; done
