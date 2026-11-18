# Randomized Bin Stretching

Exact checks for the bounds in the paper.

```
python3 checks/check_paper_numbers.py
python3 checks/second_replay.py --max-bins 20
```

Python 3. No dependencies. `checks/third` is a third solver for some catalogs:

```
cd checks/third
python3 check_complete.py ../cats
python3 check_k49.py ../cats
python3 check_more.py ../cats
python3 check_cap8580.py
```

## W(U) <= 1/5

`verify/` has the verifier, its inputs and the sha256 of the 3580 record files (19 GB, not included). With the records in `rec/`:

```
cd rec
UV_NPROC=64 python3 -B ../verify/uverify.py m 1 5 ../verify/rows.json ../verify/m_d12.top $(sed 's|.*rec/||' ../verify/records.sha256)
```

Needs numpy. Never use `-O` or `PYTHONOPTIMIZE`. The two numbers after `m` are the level 1/5, and the second must be positive.

## R_2 <= 29/24

`twobins/` has the solver of the rounded game and checkers of its certificates.

```
g++ -O2 -fopenmp -o rg2 twobins/rg2.cpp
g++ -O2 -fopenmp -o icheck twobins/icheck.cpp
./rg2 9 3,2,1 r=3 x2=1 cert=c.txt
./icheck c.txt
```

This gives 11/9 with 3 GB. `./rg2 12 3,2,1 r=4 x2=1 cert=c.txt` gives 29/24 (a 74 GB file) and `./rg2 12 5,3,2 r=3 x2=1 cert=c.txt` gives 109/90 with 40 GB. `vcheck.cpp` and `rgcheck.py` are two more checkers.

## Three algorithms: at least 47/40

Every lottery over three deterministic algorithms has an input of expected cost at least 47/40.

```
g++ -O2 -fopenmp -std=c++17 -o gridgame twobins/gridgame.cpp
g++ -O2 -std=c++17 -o gcheck twobins/gcheck.cpp
python3 twobins/cover3.py ./gridgame gg 12,15 47/40 30 960 out 8
```

A few minutes and 5 GB. `./rg2 k w mode=grid` gives the same values. `./gridgame 15 5,3,2 cert=c.txt` also writes a certificate of the value, and `./gcheck c.txt` checks it.

## Two algorithms: at least 29/24

```
python3 twobins/cover2.py ./gridgame 12,15,18,21,24,27 29/24 20 1280 out 4 12
```

Six minutes on 48 cores, 21 GB.

## R_3 <= 83/63

`threebins/` has the solver, two checkers and a simulator for three bins.

```
g++ -O2 -fopenmp -o rg3 threebins/rg3.cpp
g++ -O2 -std=c++17 -fopenmp -o c3a threebins/c3a.cpp
./rg3 6 3 1,1 cert=c.txt
./c3a c.txt
```

This is a fair coin of 4/3: eleven minutes on 16 cores, 6 GB. `./rg3 10 2 1,1 maxgb=80 cert=c.txt` gives a fair coin of 53/40 (an 89 GB file) and `./rg3 9 3 4,3 maxgb=80 cert=c.txt` a lottery of 83/63 (213 GB). Both need several hundred GB of memory. `c3b.cpp` is a second checker (`g++ -O2 -std=c++17 -fopenmp -o c3b threebins/c3b.cpp`, GCC only, about 490 GB for 83/63). `sim3.cpp` runs a lottery on real inputs.
