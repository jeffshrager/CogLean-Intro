/-
Multi-digit addition: EPAM recognition combined with distributions-of-
associations retrieval, as choices from CogLib.

A child adding two 3-digit numbers may simply *know* the answer to a
familiar problem (100 + 100), or may work it out column by column. The model
nests the distributions-of-associations architecture one level up:

* **Whole-problem retrieval.** An EPAM discrimination net recognizes the
  problem as one of the familiar problems it stores (EPAM D2). Retrieval
  then runs on that problem's distribution of associations (DOA A3).
* **Column backup.** If the problem is not recognized, or retrieval is
  exhausted, the answer is computed some other way, column by column.

| Postulate | CogLib |
|---|---|
| M1 Problem code: features for each digit of each addend | `Encoding`: `code`, `features`, `determines` |
| M2 Recognition: a discrimination net of familiar problems (EPAM D2) | `Cog.Net`, `Net.select`; for any memory, `trialWith` and a `retrieve` |
| M3 Whole-problem retrieval: the recognized problem's associations, a confidence criterion and a search length (DOA A1-A3) | `Cog.search` |
| M4 Column backup, when M2 or M3 fails | `backup`, a distribution of answers per problem |

Nothing here is a table of numbers. The encoding, the net, the strengths,
the criterion, the search length and the backup are all parameters, and the
theorems in `Phenomena.lean` hold for every choice of them.

Simplifications:
* The backup is left abstract: any distribution of answers. The theorems
  hold for every backup. `Integrated.lean` fills it with the column problem
  solver (`Solver.lean`) adding each column by a single-digit DOA trial.
* Strengths are attached to stored codes. A code stores the problem it
  encodes (`select` returns `code q`), so a stored image's "correct" answer
  is `q`'s sum.
-/

import CogLib

namespace MD

open Cog Dist

/-- An addition problem `a + b`; the theorems about digits assume 3-digit
addends (`a, b < 1000`). -/
structure Problem where
  a : Nat
  b : Nat
  deriving Repr, DecidableEq

def Problem.sum (p : Problem) : Nat := p.a + p.b

/-- The problem with its addends swapped. -/
def Problem.swap (p : Problem) : Problem := ⟨p.b, p.a⟩

inductive Addend where
  | first
  | second
  deriving Repr, DecidableEq

inductive Place where
  | hundreds
  | tens
  | units
  deriving Repr, DecidableEq

def Problem.addend (p : Problem) : Addend → Nat
  | .first => p.a
  | .second => p.b

/-- A digit of a number. -/
def digitOf (n : Nat) : Place → Nat
  | .hundreds => n / 100 % 10
  | .tens => n / 10 % 10
  | .units => n % 10

def Problem.digit (p : Problem) (i : Addend) (j : Place) : Nat := digitOf (p.addend i) j

/-- A digit is less than 10. -/
theorem digit_lt (p : Problem) (i : Addend) (j : Place) : p.digit i j < 10 := by
  cases j <;> simp only [Problem.digit, digitOf] <;> exact Nat.mod_lt _ (by decide)

/-- **M1 Problem code.** Each digit of each addend has its own features, and
agreeing on a digit's features means having the same digit. -/
structure Encoding where
  code : Problem → Item
  features : Addend → Place → List Feature
  determines : ∀ p q i j, (∀ f ∈ features i j, (code p).feat f = (code q).feat f) →
    p.digit i j = q.digit i j

/-- The route by which an answer was reached: CogLib's routes
(`Cog.Route`), in this model's words. An answer is stated by retrieval of the
whole problem (`whole`), or computed by the columns (`columns`), the backup. -/
abbrev Route := Cog.Route

@[match_pattern] abbrev Route.whole : Route := Cog.Route.retrieved
@[match_pattern] abbrev Route.columns : Route := Cog.Route.backup

/-- What follows recognition: retrieval on the stored code called up, with
the column backup when it is exhausted, or when nothing is called up. This is
CogLib's `RR.afterRecognition`, with answers in `Nat`. -/
abbrev afterRetrieval (str : Item → Nat → Rat) (as : List Nat) (cc : Rat) (n : Nat)
    (backup : Problem → Dist Nat) (x : Problem) : Option Item → Dist (Route × Nat) :=
  RR.afterRecognition str as cc n backup x

/-- **A trial with any memory** (M2-M4, with M2 left open). `retrieve` says
what a problem's code calls up: a stored code, or nothing, with
probabilities. Then retrieval on the stored code's associations, and the
column backup when retrieval is exhausted or nothing is called up. This is
CogLib's composition `Cog.recognizeRetrieve`, with problem codes from the
encoding and answers in `Nat`. -/
abbrev trialWith (retrieve : Item → Dist (Option Item)) (E : Encoding) (str : Item → Nat → Rat)
    (as : List Nat) (cc : Rat) (n : Nat) (backup : Problem → Dist Nat) (x : Problem) :
    Dist (Route × Nat) :=
  recognizeRetrieve E.code retrieve str as cc n backup x

/-- **A trial** with EPAM's net as the memory. Recognize the problem's code
in the net `N`; if it is recognized as a stored code `y`, retrieve with `y`'s
strengths `str y`, criterion `cc` and search length `n`; if retrieval is
exhausted, or nothing is recognized, use the column backup. -/
def trial (E : Encoding) (N : Net) (str : Item → Nat → Rat) (as : List Nat) (cc : Rat) (n : Nat)
    (backup : Problem → Dist Nat) (x : Problem) : Dist (Route × Nat) :=
  match N.select (E.code x) with
  | none => Dist.bind (backup x) fun r => Dist.pure (.columns, r)
  | some y => Dist.bind (search as (str y) cc 0 n) fun
      | .stated a _ => Dist.pure (.whole, a)
      | .exhausted => Dist.bind (backup x) fun r => Dist.pure (.columns, r)

/-- The EPAM trial is the trial with a discrimination net's retrieval. -/
theorem trial_eq_trialWith (E : Encoding) (N : Net) (str : Item → Nat → Rat) (as : List Nat)
    (cc : Rat) (n : Nat) (backup : Problem → Dist Nat) (x : Problem) :
    trial E N str as cc n backup x = trialWith N.retrieve E str as cc n backup x := by
  unfold trialWith recognizeRetrieve Net.retrieve
  rw [bind_pure_left]
  unfold trial
  cases N.select (E.code x) with
  | none => rfl
  | some y =>
    simp only [RR.afterRecognition]
    congr 1
    funext r
    cases r <;> rfl

/-! ### Events, in this model's words -/

/-- The columns were used. -/
abbrev isColumns : Route × Nat → Bool := RR.isBackup

/-- An answer was stated by retrieval of the whole problem. -/
abbrev isWhole : Route × Nat → Bool := RR.isRetrieved

/-- An answer stated by whole-problem retrieval, with property `P`. -/
abbrev wholeSuch (P : Nat → Bool) : Route × Nat → Bool := RR.retrievedSuch P

/-- A wrong answer to `x`, stated by whole-problem retrieval. -/
abbrev wholeWrong (x : Problem) : Route × Nat → Bool := RR.retrievedWrong Problem.sum x

end MD
