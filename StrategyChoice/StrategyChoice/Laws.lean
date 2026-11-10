/-
The strength family (strength with sampling and a criterion, the memory of
the distributions-of-associations model) against the laws.

* `orderFree`: has it, for every choice of parameters. Strengths only add.
* `not_certainty`, `not_stability`: lacks them. A similar stimulus competes
  for retrieval.
* `not_recency`: lacks it. Nothing records when study happened.
  `never_recency`: in fact lacks it for every choice of parameters, since it
  is order-free.
* `not_determinate`: lacks it. After 000 and 100, the probe 000 states each
  with positive probability.
* `storedOnly`: has it, for every choice of parameters. Only stimuli with
  strength are sampled, and only study gives strength.
-/

import CogLib

namespace SC

open Cog Laws Dist StrengthMem

/-- **Strength memory is order-free**, for every choice of parameters, from
every state. -/
theorem orderFree (P : StrParams) (s0 : StrState) (U : List Item) :
    OrderFree (strRetriever P) s0 U := by
  intro s _ a _ b _ x
  show StrengthMem.retrieve P (StrengthMem.study P (StrengthMem.study P s a) b) x =
    StrengthMem.retrieve P (StrengthMem.study P (StrengthMem.study P s b) a) x
  rw [study_comm]

/-- The instance for the counterexamples: all eight 3-bit codes, each
mismatch discounting by 3/4, increment 1, criterion 1/2, one search. -/
def P : StrParams := ⟨(allCodes 3), (allFeatures 3), 3 / 4, 1, 1 / 2, 1⟩

/-- Nothing studied. -/
def s0 : StrState := fun _ => 0

/-- **Strength memory lacks certainty.** With 100 studied, 000 just studied
is retrieved by itself with probability 4/7: 100 competes. -/
theorem not_certainty : ¬ Certainty (strRetriever P) s0 (allCodes 3) := by
  intro h
  have := h ((strRetriever P).studyAll s0 [(bitCode 3 1)]) ⟨_, by decide, rfl⟩ ((bitCode 3 0)) (by decide)
  revert this
  decide +kernel

/-- **Strength memory lacks stability.** Studying 100 lowers the chance that
000 retrieves itself from 1 to 4/7. -/
theorem not_stability : ¬ Stability (strRetriever P) s0 (allCodes 3) := by
  intro h
  have := h ((strRetriever P).studyAll s0 [(bitCode 3 0)]) ⟨_, by decide, rfl⟩ ((bitCode 3 0)) (by decide)
    ((bitCode 3 1)) (by decide) (by decide)
  revert this
  decide +kernel

/-- **Strength memory lacks recency.** After 000 and then 110, the probe
010 retrieves each equally often. -/
theorem not_recency : ¬ Recency (allFeatures 3) (strRetriever P) s0 (allCodes 3) := by
  intro h
  have := h [] (by decide) ((bitCode 3 0)) (by decide) ((bitCode 3 3)) (by decide) (by decide) (by decide)
    (by decide) ((bitCode 3 2)) (by decide)
  revert this
  decide +kernel

/-- **Strength memory is not determinate.** -/
theorem not_determinate : ¬ Determinate (strRetriever P) s0 (allCodes 3) :=
  not_determinate_of_two _ _ _ _ ⟨[(bitCode 3 0), (bitCode 3 1)], by decide, rfl⟩ ((bitCode 3 0)) ((bitCode 3 0)) ((bitCode 3 1))
    (by decide) (by decide +kernel) (by decide +kernel)

/-- **Strength memory retrieves only what was studied**, for every choice of
parameters. -/
theorem storedOnly (P : StrParams) (U : List Item) : StoredOnly (strRetriever P) s0 U := by
  intro xs _ x y hy
  have hzero : (strRetriever P).studyAll s0 xs y = 0 := studyAll_unstudied P y xs s0 hy
  show prob (StrengthMem.retrieve P _ x) _ = 0
  have hr : ∀ s : StrState, StrengthMem.retrieve P s x = Dist.bind (search P.items (StrengthMem.weight P s x) P.cc 0 P.n)
      fun r => Dist.pure (match r with | .stated a _ => some a | .exhausted => none) := by
    intro s
    unfold StrengthMem.retrieve
    congr
    funext r
    cases r <;> rfl
  rw [hr, prob_bind_pure]
  apply prob_search_zero
  · simp only [StrengthMem.weight]; rw [hzero]; exact Rat.zero_mul _
  · intro a k hak; simpa using hak
  · rfl

/-- **Strength memory never has recency**, for every choice of parameters and from
every state, wherever recency can be tested: two distinct stimuli and a probe
equally similar to both. It is order-free, and no order-free memory is
recent (`not_recency_of_orderFree`). -/
theorem never_recency (P : StrParams) (s0 : StrState) (fs : List Feature) (U : List Item) (a b x : Item)
    (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b) (hx : mismatches fs x a = mismatches fs x b) :
    ¬ Recency fs (strRetriever P) s0 U :=
  not_recency_of_orderFree fs _ s0 U (orderFree P s0 U) a b x ha hb hab hx

end SC
