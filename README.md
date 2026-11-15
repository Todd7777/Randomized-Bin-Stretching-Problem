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
