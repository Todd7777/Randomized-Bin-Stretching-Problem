#!/bin/bash
# negtest.sh CERT DIR: three corrupted copies of a hybrid certificate (root dropped, one state dropped, T0 lowered
# by one), each run through a checker. CHK names the checker, CHKOPT its options.
set -u
c="$1"; d="$2"; mkdir -p "$d"; b=$(basename "$c" .txt)
CHK="${CHK:-$(dirname "$0")/relaxcheckg}"
awk 'BEGIN{h=0} /^#/{print;next} h==0{h=1; $NF=$NF-1; print; next} /^0 \|/{next} {print}' "$c" > "$d/${b}_noroot.txt"
maxN=$(awk '/^#/||/^HYB/{next}{if($1>mx)mx=$1}END{print mx}' "$c")
awk -v mx="$maxN" 'BEGIN{h=0;done=0} /^#/{print;next} h==0{h=1; $NF=$NF-1; print; next} $1==mx && !done {done=1; next} {print}' "$c" > "$d/${b}_dropstate.txt"
awk 'BEGIN{h=0} /^#/{print;next} h==0{h=1; $(NF-1)=$(NF-1)-1; print; next} {print}' "$c" > "$d/${b}_T0minus1.txt"
for v in noroot dropstate T0minus1; do printf "%-12s " "$v"; "$CHK" ${CHKOPT:-} "$d/${b}_$v.txt"; echo "   exit $?"; done
