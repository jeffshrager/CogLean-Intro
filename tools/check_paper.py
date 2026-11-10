"""
Check that every Lean name the paper cites exists in this edition.

    python3 tools/check_paper.py [paper/paper.tex] [paper/talk.tex]

A cited name resolves if some declaration's full name ends with it (so `RR.confident_errors`
and `confident_errors` both match `Cog.RR.confident_errors`). `\\lean{...}` arguments that
are expressions (with spaces or `~`) are checked by their first word. Uses the latest audit's
rows.json, so run `tools/audit_layers.py` first after changing declarations.
"""
import glob, json, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
files = sys.argv[1:] or [os.path.join(ROOT, "paper", "paper.tex"), os.path.join(ROOT, "paper", "talk.tex")]
latest = sorted(glob.glob(os.path.join(ROOT, "notes", "audits", "*", "rows.json")))[-1]
names = [r["name"] for r in json.load(open(latest))]
missing = []
for f in files:
    if not os.path.exists(f):
        continue
    for m in re.finditer(r"\\(?:lean|code)\{([^}]*)\}", open(f).read()):
        raw = m.group(1).replace("\\_", "_")
        n = raw.split("~")[0].split()[0] if raw.split() else raw
        if n in ("propext", "Quot.sound", "Classical.choice") or re.match(r"^[A-Z]\.", n):
            continue  # Lean's own axioms; a field of a variable in prose (`F.fact`)
        if "/" in n or n.endswith((".lean", ".md")) or not re.match(r"^[A-Za-z_.][A-Za-z0-9_.'*]*$", n):
            continue  # a file or path, not a declaration
        if m.group(0).startswith("\\code") and "." not in n and "_" not in n:
            continue  # \code{} is also used for plain identifiers in prose
        pat = re.compile(r"(^|\.)" + re.escape(n).replace(r"\*", r"[A-Za-z0-9_']+") + r"$")
        if not any(pat.search(x) for x in names):
            missing.append((os.path.basename(f), n))
missing = sorted(set(missing))
for f, n in missing:
    print(f"{f}: {n}")
print(f"{len(missing)} cited names not found")
sys.exit(1 if missing else 0)
