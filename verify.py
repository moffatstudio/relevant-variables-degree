"""One-minute verification of the exhaustive search behind R_3 = 10.

    python verify.py            # n = 3..8, about a minute in total
    python verify.py --n10      # also n = 10 (about 14 minutes): recovers Xi_3 uniquely
    python verify.py --lean     # also run bash lean/gate.sh (needs elan + lake + Mathlib)

What this checks. It compiles the audited complete search `search/r3search2.c`, reruns it
for n = 3..8 (and, with --n10, n = 10), compares the orbit counts it reports against the
table published in `search/README.md`, and runs the independent checker
`search/verify_solutions.py` on every solution the rerun emits: each solution is re-evaluated
at all 2^n points of the cube and tested against conditions (i), (ii), (iii) of the frozen
finite statement F(n) in `proofs/FINITE_STATEMENT.md`.

What this does NOT rerun: the n = 11 search itself (6 shards, about 2 CPU-hours), whose raw
logs are `search/log2_n11_s*.txt`. F(11) is the computational claim; see search/README.md for
the shard-disjointness argument and the residual trust caveats. Exits non-zero on any failure.
"""
import os
import re
import shutil
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.abspath(__file__))
SEARCH = os.path.join(ROOT, "search")
OUT = os.path.join(SEARCH, "_verify_out")

# Orbit counts published in search/README.md ("Results table").
EXPECTED = {3: 14, 4: 102, 5: 809, 6: 1773, 7: 1060, 8: 213, 10: 1}

FAILS = []


def check(name, got, want):
    ok = got == want
    print("%-56s %-12s expected %-12s %s" % (name, got, want, "ok" if ok else "FAIL"))
    if not ok:
        FAILS.append(name)


def table_from_readme():
    """Re-read the counts out of search/README.md so the table is the single source of truth."""
    counts = {}
    path = os.path.join(SEARCH, "README.md")
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            m = re.match(r"\|\s*(\d+)\s*\|\s*\*{0,2}([\d,]+)\*{0,2}\s*\|", line)
            if m:
                counts[int(m.group(1))] = int(m.group(2).replace(",", ""))
    return counts


def build():
    exe = os.path.join(OUT, "r3search2.exe" if os.name == "nt" else "r3search2")
    gcc = shutil.which("gcc") or shutil.which("cc")
    if gcc is None:
        for cand in (exe, os.path.join(SEARCH, "r3search2.exe"), os.path.join(SEARCH, "r3search2")):
            if os.path.exists(cand):
                print("gcc not found; using the prebuilt binary %s" % cand)
                return cand
        print("FAIL: no C compiler on PATH and no prebuilt binary.\n"
              "      Install gcc (Linux: apt install build-essential; Windows: MSYS2/MinGW-w64)\n"
              "      and rerun, or build by hand: gcc -O2 -o r3search2 search/r3search2.c")
        sys.exit(2)
    print("compiling search/r3search2.c with %s ..." % gcc)
    subprocess.run([gcc, "-O2", "-o", exe, os.path.join(SEARCH, "r3search2.c")], check=True)
    return exe


def run(exe, n):
    t = time.time()
    p = subprocess.run([exe, str(n)], stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                       text=True, check=True)
    dt = time.time() - t
    sols = [ln for ln in p.stdout.splitlines() if ln.startswith("SOL")]
    m = re.search(r"solutions=(\d+)", p.stdout)
    if m is None:
        print(p.stdout[-1000:])
        FAILS.append("n=%d: no summary line" % n)
        return None, None
    reported = int(m.group(1))
    if reported != len(sols):
        FAILS.append("n=%d: summary says %d solutions but %d SOL lines" % (n, reported, len(sols)))
    solfile = os.path.join(OUT, "sol_n%d.txt" % n)
    with open(solfile, "w", encoding="utf-8", newline="\n") as fh:
        fh.write("\n".join(sols) + ("\n" if sols else ""))
    with open(os.path.join(OUT, "log_n%d.txt" % n), "w", encoding="utf-8", newline="\n") as fh:
        fh.write(p.stdout)
    print("    n=%2d  %7.2fs" % (n, dt))
    return reported, solfile


def main():
    os.makedirs(OUT, exist_ok=True)
    ns = [3, 4, 5, 6, 7, 8]
    if "--n10" in sys.argv:
        ns.append(10)

    published = table_from_readme()
    print("== table in search/README.md agrees with the values this script expects")
    for n, want in sorted(EXPECTED.items()):
        check("README.md orbit count, n=%d" % n, published.get(n), want)

    exe = build()

    print("== rerunning the complete search (orbit counts must match the table)")
    solfiles = []
    for n in ns:
        got, solfile = run(exe, n)
        if got is None:
            continue
        check("search orbit count, n=%d" % n, got, EXPECTED[n])
        if os.path.getsize(solfile):
            solfiles.append(solfile)

    print("== independent check of every emitted solution (search/verify_solutions.py)")
    if solfiles:
        p = subprocess.run([sys.executable, os.path.join(SEARCH, "verify_solutions.py")] + solfiles,
                           capture_output=True, text=True)
        print(p.stdout.strip())
        if p.returncode != 0 or re.search(r"TOTAL: \d+ checked, (?!0 failed)", p.stdout):
            FAILS.append("verify_solutions.py reported a failure")
    else:
        FAILS.append("no solutions emitted to check")

    if 10 in ns:
        print("== n = 10 recovers exactly one orbit: the CHS function Xi_3 (F(10) is false)")

    print("== n = 11 (F(11) = 0 solutions) is NOT rerun here: 6 shards, about 2 CPU-hours.")
    print("   Raw logs: search/log2_n11_s0.txt .. s5.txt; argument: search/README.md.")

    if "--lean" in sys.argv:
        print("== Lean gate (lean/gate.sh)")
        if shutil.which("lake") is None:
            print("   lake not on PATH - skipping (install elan, then `cd lean && lake exe cache get`)")
        else:
            p = subprocess.run(["bash", "gate.sh"], cwd=os.path.join(ROOT, "lean"))
            if p.returncode != 0:
                FAILS.append("lean/gate.sh")

    print()
    if FAILS:
        print("FAILED:", FAILS)
        sys.exit(1)
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
