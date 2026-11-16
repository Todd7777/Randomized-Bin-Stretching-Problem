# Randomized Bin Stretching

Exact checks for the bounds in the paper.

```
python3 checks/check_paper_numbers.py
python3 checks/second_replay.py --max-bins 20
```

Python 3. No dependencies.

## W(U) <= 1/5

`verify/` has the verifier, its inputs and the sha256 of the 3580 record files (19 GB, not included). With the records in `rec/`:

```
cd rec
UV_NPROC=64 python3 -B ../verify/uverify.py m 1 5 ../verify/rows.json ../verify/m_d12.top $(sed 's|.*rec/||' ../verify/records.sha256)
```

Needs numpy. Never use `-O`.

## R_2 <= 109/90

`twobins/` has the solver of the rounded game and checkers of its certificates.

```
g++ -O2 -fopenmp -o rg2 twobins/rg2.cpp
g++ -O2 -fopenmp -o icheck twobins/icheck.cpp
./rg2 12 5,3,2 r=3 x2=1 cert=c.txt
./icheck c.txt
```

About 40 GB of memory. `./rg2 9 3,2,1 r=3 x2=1 cert=c.txt` gives 11/9 with 3 GB. `vcheck.cpp` and `rgcheck.py` are two more checkers.
