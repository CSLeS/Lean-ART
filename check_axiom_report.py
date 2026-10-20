#!/usr/bin/env python3
"""Enforce the allowed axioms for every published theorem listed in the entry audit.

This complements Lean's kernel check, it does not replace it.
"""
from pathlib import Path
import re
import sys

EXPECTED = {
    "LotteryChoice.representation_of_axioms",
    "LotteryChoice.axioms_of_representation",
    "LotteryChoice.representation_iff",
    "LotteryChoice.delib_iff",
    "LotteryChoice.R_unique",
    "LotteryChoice.u_unique",
    "LotteryChoice.Representation.positiveAffine",
    "LotteryChoice.Paper.representation_iff",
    "LotteryChoice.Paper.deliberation_iff",
    "LotteryChoice.Paper.R_unique",
    "LotteryChoice.Paper.u_unique",
    "LotteryChoice.Representation.positiveAffine_u",
    "LotteryChoice.Representation.positiveAffine_R",
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
pattern = re.compile(r"^'([^']+)' depends on axioms: \[(.*?)\]$")

def main() -> int:
    if len(sys.argv) != 2:
        print("Usage: python3 verification/check_axiom_report.py <lean-output.txt>", file=sys.stderr)
        return 2
    lines = Path(sys.argv[1]).read_text(encoding="utf-8-sig").splitlines()
    found = {}
    for line in lines:
        match = pattern.fullmatch(line.strip())
        if match and match.group(1) in EXPECTED:
            name = match.group(1)
            if name in found:
                print(f"FAIL: Duplicate axiom report for {name}", file=sys.stderr)
                return 1
            reported = {s.strip() for s in match.group(2).split(",") if s.strip()}
            found[name] = reported
    missing = EXPECTED - found.keys()
    if missing:
        print("FAIL: Missing theorem axiom reports:", *sorted(missing), sep="\n  ", file=sys.stderr)
        return 1
    bad = {name: sorted(axioms - ALLOWED) for name, axioms in found.items() if axioms - ALLOWED}
    if bad:
        for name, axioms in bad.items():
            print(f"FAIL: {name} uses disallowed axioms: {axioms}", file=sys.stderr)
        return 1
    print(f"PASS: All {len(EXPECTED)} required theorem declarations depend only on {sorted(ALLOWED)}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
