# Every stream of a catalog is needed: without any one of them, replay_catalog.py fails.
# python3 needed.py CATALOG.json BOUND
import importlib.util, json, sys
from fractions import Fraction
from pathlib import Path
spec = importlib.util.spec_from_file_location("replay_catalog", Path(__file__).with_name("replay_catalog.py"))
rc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rc)
seqs = [tuple(Fraction(x) for x in s) for s in json.loads(Path(sys.argv[1]).read_text())]
bound = Fraction(sys.argv[2])
whole = ((Fraction(1, 2), Fraction(1)),)
assert rc.replay(seqs, bound)[0] == whole, "the catalog itself fails"
spare = [k for k in range(len(seqs)) if rc.replay(seqs[:k] + seqs[k + 1:], bound)[0] == whole]
print(f"{len(seqs)} streams; without any one of them the bound {bound} fails: {not spare}")
print("PASS" if not spare else f"FAIL: not needed {spare}")
raise SystemExit(0 if not spare else 1)
