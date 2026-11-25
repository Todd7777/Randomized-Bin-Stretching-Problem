#!/usr/bin/env python3
# The prior of the group of largest value in a --out file of catval.py.
# python3 best_prior.py VAL.json PRIOR.json [--key x y]
import json, sys
from fractions import Fraction
d = json.load(open(sys.argv[1]))
gs = d["groups"]
if "--key" in sys.argv:
    i = sys.argv.index("--key")
    key = sys.argv[i + 1:i + 3]
    g = [g for g in gs if g["key"] == key][0]
else:
    g = max(gs, key=lambda g: Fraction(g["lower"]))
json.dump({"group": g["key"], "lower": g["lower"], "prior": g["prior"]}, open(sys.argv[2], "w"))
print("group", g["key"], "lower", g["lower"], "support", len(g["prior"]))
