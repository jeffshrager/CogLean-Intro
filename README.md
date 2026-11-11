# CogLean-Intro

> This is the **introduction** to CogLean. The main repository, with the full library, more
> domains and work in progress, is **[jeffshrager/CogLean](https://github.com/jeffshrager/CogLean)**.

**CogLean** is a library of cognitive theory written in the [Lean 4](https://lean-lang.org)
programming language and proof assistant. In Lean, a definition is both a program that runs
and a mathematical object that theorems can be about, so a cognitive model and the formal
claims made about it are the same thing, and the claims are checked by machine. CogLean is
organized on the model of [Mathlib](https://github.com/leanprover-community/mathlib4): mechanisms
are defined once, phenomena are stated without any mechanism, laws are stated against shared
interfaces, and theorems relating them accumulate in a library that anyone can extend.

The premise is simple to state. Once we write down what we already believe about a cognitive
theory with mathematical precision, the theory becomes something we can reason about
mechanically, and we can discover things about it that we did not know: consequences it
entails, phenomena it can never produce, assumptions its authors left unstated, predictions on
which it differs from a rival. Formalization is the necessary first step; discovery is the
payoff. Allen Newell asked how cognitive science could become cumulative. A shared library of
machine-checked relationships between theories and phenomena is one answer: results proved
once stay proved, stay aligned with the models that run, and are available to the next theory
that uses the same constructs.

Two cautions, stated up front. The checker establishes that conclusions follow from premises;
whether the premises are true of people remains the business of experiment. And what is
discovered this way is discovered about the *theories*. Its psychological significance depends
on empirical assumptions, the bridges from what a theorem concerns to what an experiment
measures, which this work tries to keep explicit.

This repository is an **invitation**, written for cognitive scientists who do not know Lean.
No Lean is needed to read the paper; where a few lines appear, each is paraphrased in English
beside it. The paper, [`paper/paper.pdf`](paper/paper.pdf), asks four questions a cognitive
scientist might ask of such a library and answers each with one short, fully proved
demonstration:

1. **Does a theory entail what its authors said?** Siegler and Shrager's 1984 distributions-of-
   associations model: its "nonintuitive prediction" proved, and a claim that needs a condition
   the chapter does not state (`StrategyChoice/`).
2. **Can a theory be shown unable to produce a phenomenon?** Collins and Quillian's hierarchical
   network can never show a typicality effect or a reversal, for every network; the feature-
   comparison model can (`SemanticMemory/`).
3. **Do independently formalized theories compose, and can an explanation be shared or rivalled?**
   EPAM, the DOA model and a column solver compose into a model of three-digit addition; a
   pattern of confident errors is proved for the composition, for every memory with three laws,
   and, by priming, for a simplified ACT-R memory; the two explanations differ on a familiar
   problem, which is an experiment nobody has run (`MultiDigit/`).
4. **Can theories be compared by what they entail?** The memory theory matrix: four formalized
   memory families against six laws of retrieval, every verdict a theorem (`notes/MATRIX.md`).

It is drawn from the [CogLean lab repository](https://github.com/jeffshrager/CogLean), which
carries the multi-digit model in full, along with further domains and work in progress. It is
an introduction, not a replacement for it.

## Packages

| Package | What it holds |
|---|---|
| `CogLib/` | The general library. Representations (features, exact rational distributions, semantic networks); memories (discrimination nets, an activation memory, a strength memory, global matching); processes (discrimination learning, sampled retrieval with a confidence criterion, recognize-retrieve-back up, priming, a decision cycle with repairs); theory-neutral phenomena and laws, with their theorems. It imports no other package. |
| `StrategyChoice/` | The distributions-of-associations model (Siegler & Shrager 1984): postulates, the single-digit trial, its phenomena, what peaking does and does not imply, and its laws. |
| `SemanticMemory/` | Collins & Quillian's hierarchical network and Smith, Shoben & Rips's feature comparison, against theory-neutral laws of sentence verification. |
| `EPAM/`, `ACTR/`, `GlobalMatching/` | Each memory against the laws of retrieval: the rows of the **memory theory matrix**, with DOA's strength memory (`StrategyChoice/Laws`). |
| `MultiDigit/` | Three-digit addition: the composition, the confident-error pattern, the ACT-R rival, and exact values at an illustrative setting. |
| `paper/` | The paper, *CogLean: Towards a Machine-Checkable Library of Cognitive Theory*. |
| `tools/` | The catalog and matrix generators, the layering audit, and the paper's name check. |
| `notes/` | The catalog, the matrix, the evidence record, the layering policy, and the audit. |

## Build

Lean 4.35.0, core only (no Mathlib). With elan installed:

```
cd MultiDigit && lake build      # builds CogLib and StrategyChoice too
cd EPAM && lake build
cd ACTR && lake build
cd GlobalMatching && lake build
cd SemanticMemory && lake build
python3 tools/gen_matrix.py      # regenerates notes/MATRIX.md
python3 tools/gen_catalog.py     # regenerates notes/CATALOG.md
```

Every theorem is fully proved, with no `sorry`, and depends only on Lean's standard axioms
(`propext`, `Quot.sound`, `Classical.choice`). The catalog generator fails on any other axiom.
