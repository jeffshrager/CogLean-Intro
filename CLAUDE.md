# Working on CogLean-Intro

CogLean-Intro is a small, self-contained invitation to CogLean for cognitive
scientists who do not know Lean: four demonstrations (the 1984 strategy-choice chapter checked;
Collins & Quillian's impossibility; the multi-digit composition with its ACT-R rival; the
memory theory matrix) and a paper built around them. It is not the main line of CogLean; the
lab repository (`../repo`, github.com/jeffshrager/CogLean) is, and `../CogLean-20261106-Intro`
carries the multi-digit model in full. Keep it small: add only what the four demonstrations
and the paper need.

## Build

- Lean 4.35.0 via elan: `export PATH=$HOME/.elan/bin:$PATH`. Core Lean only; no Mathlib.
- Packages: `CogLib/` (imports nothing), `EPAM/`, `StrategyChoice/`, `ACTR/`,
  `GlobalMatching/`, `SemanticMemory/` (each requires CogLib), `MultiDigit/` (requires CogLib
  and StrategyChoice). `cd <pkg> && lake build`.
- The memory theory matrix: each memory theory proves its laws in `<Theory>/Laws.lean`;
  `python3 tools/gen_matrix.py` regenerates `notes/MATRIX.md` (with the evidence about people
  from `notes/evidence.json`), reading each verdict from the theorem's statement and checking
  axioms.
- Probabilities are core `Rat`; `decide +kernel` evaluates concrete rationals.
- Every theorem fully proved: no `sorry`; only `propext`, `Quot.sound`, `Classical.choice`.
- After changing theorems, regenerate `notes/CATALOG.md` with `python3 tools/gen_catalog.py`
  (from the repo root).
- The paper: `cd paper && make paper.pdf` (twice); `python3 tools/check_paper.py paper/paper.tex`
  checks every cited Lean name against the latest audit's `rows.json`. Rebuild the PDF after
  every substantial edit.
- `.lake/` and LaTeX by-products are excluded through `.git/info/exclude`.

## Layering (`notes/LAYERING_POLICY.md`)

- CogLib holds representations, mechanisms named for what they do, theory-neutral phenomena
  and laws, general theorems, and library facts. No task vocabulary in identifiers, no
  concrete settings except deliberate witnesses.
- Only CogLib declares `namespace Cog`. The others use `EPAM`, `SC`, `ACTR`, `GM`,
  `SemanticMemory` and `MD`.
- CogLib docstrings cite theories by name and source, never packages or files above CogLib.
- A lemma is proved once, in the lowest package that needs it; a theory proves its own laws.
- Run the layer audit at each release: `python3 tools/audit_layers.py <tag>`.

## Conventions

- Explanation, not only validity: phenomena are targets, not premises. A theorem with a law
  or phenomenon among its hypotheses is conditional; say so. Headline docstrings (beginning
  in bold) say which premises are postulates and which are conditions.
- In the paper, every Lean name is fully qualified; theorem conditions are stated honestly;
  matrix rows are "formalized families", never the theories themselves.
- Commit after every successful major change. Push only when asked.
