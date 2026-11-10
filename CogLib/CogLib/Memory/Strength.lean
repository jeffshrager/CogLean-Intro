/-
A family of memories: strength with sampling and a criterion (after the
distributions-of-associations model, Siegler & Shrager 1984).

Each stimulus has a strength, which study raises by a fixed increment. A
probe samples stored stimuli in proportion to strength, discounted by `μ`
for each mismatching feature. A sample is stated if its weight clears the
criterion; otherwise sampling is repeated, up to the search length, and then
retrieval fails. Nothing decays, and nothing records when study happened.
-/

import CogLib.Process.SampledRetrieval
import CogLib.Phenomena.RetrievalLaws

namespace Cog

/-- The parameters: the stimuli that can be stored, the features compared,
the discount per mismatch, the increment per study, the criterion and the
search length. -/
structure StrParams where
  items : List Item
  fs : List Feature
  mu : Rat
  inc : Rat
  cc : Rat
  n : Nat

/-- A memory state: each stimulus's strength. -/
abbrev StrState := Item → Rat

namespace StrengthMem

/-- The weight of a stored `y` for the probe `x`. -/
def weight (P : StrParams) (s : StrState) (x : Item) (y : Item) : Rat :=
  s y * P.mu ^ mismatches P.fs x y

/-- **Retrieval**: search the stored stimuli, stating the first sample that
clears the criterion. -/
def retrieve (P : StrParams) (s : StrState) (x : Item) : Dist (Option Item) :=
  Dist.bind (search P.items (weight P s x) P.cc 0 P.n) fun
    | .stated y _ => Dist.pure (some y)
    | .exhausted => Dist.pure none

/-- **Study** raises a stimulus's strength by the increment. -/
def study (P : StrParams) (s : StrState) (y : Item) : StrState :=
  fun z => if z = y then s z + P.inc else s z

end StrengthMem

/-- Strength memory as a retriever. -/
def strRetriever (P : StrParams) : Retriever StrState Item := ⟨StrengthMem.study P, StrengthMem.retrieve P⟩


namespace StrengthMem

theorem study_comm (P : StrParams) (s : StrState) (a b : Item) :
    study P (study P s a) b = study P (study P s b) a := by
  funext z
  simp only [study]
  by_cases ha : z = a <;> by_cases hb : z = b <;> simp [ha, hb] <;> grind

/-- Strength stays 0 for what is never studied. -/
theorem studyAll_unstudied (P : StrParams) (y : Item) :
    ∀ (xs : List Item) (s : StrState), y ∉ xs → (strRetriever P).studyAll s xs y = s y := by
  intro xs
  induction xs with
  | nil => intro s _; rfl
  | cons z xs ih =>
    intro s hy
    simp only [List.mem_cons, not_or] at hy
    show (strRetriever P).studyAll (study P s z) xs y = s y
    rw [ih _ hy.2]
    simp [study, Ne.symm hy.1, hy.1]

end StrengthMem

end Cog
