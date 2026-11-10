/-
Representations: feature codes.

A stimulus reaches a cognitive system as a *code*: a vector of binary
features. This is the simplest representation that supports similarity
(agreement on features), discrimination (a feature on which two codes
differ), and partial information (some features known, others not).
-/

import CogLib.Basic

namespace Cog

/-- A feature: an index into a code. -/
abbrev Feature := Nat

/-- A feature code: a list of bits. Features beyond its length read as 0. -/
abbrev Item := List Bool

/-- The value of feature `f` of code `x`. -/
def Item.feat (x : Item) (f : Feature) : Bool := x.getD f false

/-- The features `fs` of a code *determine* a property `P` of what is coded:
two things whose codes agree on `fs` agree on `P`. -/
def Determines {α β : Type} (code : α → Item) (fs : List Feature) (P : α → β) : Prop :=
  ∀ p q, (∀ f ∈ fs, (code p).feat f = (code q).feat f) → P p = P q

/-- The number of features in `fs` on which two codes differ. -/
def mismatches (fs : List Feature) (x y : Item) : Nat :=
  (fs.filter fun f => x.feat f != y.feat f).length

theorem mismatches_self (fs : List Feature) (x : Item) : mismatches fs x x = 0 := by
  simp [mismatches]

/-- The `n`-bit code of `k`, low bit first. -/
def bitCode (n k : Nat) : Item := (List.range n).map fun i => k / 2 ^ i % 2 == 1

/-- All `2^n` codes of `n` bits. -/
def allCodes (n : Nat) : List Item := (List.range (2 ^ n)).map (bitCode n)

/-- The first `n` features, in order. -/
def allFeatures (n : Nat) : List Feature := List.range n

end Cog
