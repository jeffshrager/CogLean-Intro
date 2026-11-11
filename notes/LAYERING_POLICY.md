# Layering policy

The standard the layer audit (`tools/audit_layers.py`, `tools/AUDIT_BRIEF.md`) checks
CogLean against. Change it deliberately, with a dated entry at the end. The audit reports
departures from this policy; it does not decide them.

## The layers

1. **Lean**: core only. CogLean-Intro uses no Mathlib.
2. **CogLib**: the general library. It imports no other package.
3. **Theories**: one package each (`EPAM/`, `StrategyChoice/`, `ACTR/`). A theory states its
   postulates as choices of CogLib constructs, cited to its sources, with its parameters, its
   phenomena theorems, and the proofs of which laws its mechanisms have.
4. **The application**: `MultiDigit/`, the task model assembled from theories and CogLib,
   with the task's own knowledge.

## What belongs in CogLib

- **Representations**: feature codes, distributions, semantic nets, frames, terms.
- **Mechanisms**, named for what they do, not for the theory that introduced them: a
  discrimination net, an activation memory, sampled retrieval, a decision cycle. A theory's
  name may appear in a docstring as a citation.
- **Theory-neutral phenomena and laws** (`CogLib/Phenomena/`), stated without any mechanism.
- **General theorems**: statements that bind their variables (for every net, every strength
  set, every memory with a law).
- **Library facts**: properties of algorithms and representations that later results need
  (well-formedness, merge properties, bridges).

## What does not belong in CogLib

- **Task knowledge**: arithmetic facts, column procedures, device behavior, particular
  concepts or people.
- **Task vocabulary in identifiers**: names such as `carry`, `digit`, `addend`, `microwave`,
  `ann`, `bob`. In docstrings, task words are acceptable only as examples or citations.
- **Theory parameters and concrete settings**: particular strengths, criteria, encodings, or
  parameter structures with literal values, used to compute a case.
- **Theory-specific glue**: a definition that only one theory or application uses and that
  encodes that theory's commitments rather than a general mechanism.

## Allowed with a note

- **Witness and counterexample instances in CogLib** (closed theorems computed by `decide`),
  when they support a general CogLib claim: for example, that a general theorem's hypothesis
  can be met, or that a law fails. Each is listed in every audit, so it stays a deliberate
  choice.
- **Theory names in CogLib docstrings**, as citations.

## Dependencies

- CogLib requires no package.
- A package requires only CogLib and the packages its `lakefile.toml` declares; there are no
  cycles.
- No package requires Mathlib.

## Names

- Only CogLib declares `namespace Cog`. Theories and the application use their own
  namespaces (`EPAM`, `SC`, `ACTR`, `GM`, `SemanticMemory`, `MD`).
- CogLib docstrings cite theories by name and source, never packages or files above CogLib.

## Placement

- **Duplication.** A lemma proved, under the same name or with the same statement, in two
  packages belongs in the lowest package both depend on, and the copies should cite it.
- **Relabelling.** A theorem in a theory or application package whose proof is a single
  application of a CogLib theorem is acceptable when it states the result in the package's
  own vocabulary (a named instance). The audit lists relabellings so that each is a
  deliberate choice; it is a problem only when the restatement adds nothing and duplicates a
  name.
- **Promotion.** A theorem or definition outside CogLib whose statement mentions only core
  and CogLib constants is a candidate to move down into CogLib.
- **Fan-out.** A CogLib construct used by exactly one package above it may be that package's
  content in disguise. A CogLib construct used by no package above it is either not yet
  exercised or dead.

## Changes

- 2026-11-05: first version (in the CogLean lab).
- 2026-11-10: carried into CogLean-Intro, with `SemanticMemory/` as a further theory package.
- 2026-11-06: adapted for the introductory edition: no Mathlib; the naming rules (only CogLib declares
  `namespace Cog`; CogLib docstrings cite theories, not packages), proposed by the lab's
  baseline audit (finding F012).
