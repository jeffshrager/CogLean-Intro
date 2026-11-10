/-
The global-matching family (after MINERVA 2, Hintzman 1984) against the laws.

* `orderFree`: has it, for every choice of parameters. The echo is a sum over
  traces.
* `not_certainty`, `not_stability`: lacks them. Enough traces of a neighbour
  outweigh a stimulus's own.
* `not_recency`: lacks it. Nothing records when study happened.
  `never_recency`: in fact lacks it for every choice of parameters, since it
  is order-free.
* `determinate`: has it, for every width. The echo is a single code.
* `not_storedOnly`: lacks it. Probed with the centre of three studied
  variants, memory returns the centre, never studied.

On the first four laws, global matching has the same row as strength memory.
Only stored-only retrieval separates them.
-/

import CogLib

namespace GM

open Cog Laws Dist GlobalMatch

/-- **Global matching is order-free**, for every width, from every state. -/
theorem orderFree (P : GMParams) (s0 : GMState) (U : List Item) :
    OrderFree (gmRetriever P) s0 U := by
  intro s _ a _ b _ x
  show retrieve P ((s ++ [a]) ++ [b]) x = retrieve P ((s ++ [b]) ++ [a]) x
  have hI : intensity P ((s ++ [a]) ++ [b]) x = intensity P ((s ++ [b]) ++ [a]) x :=
    sum_append_swap s a b _
  have hE : echo P ((s ++ [a]) ++ [b]) x = echo P ((s ++ [b]) ++ [a]) x := by
    unfold echo
    congr 1
    funext f
    rw [show content P ((s ++ [a]) ++ [b]) x f = content P ((s ++ [b]) ++ [a]) x f from
      sum_append_swap s a b _]
  unfold retrieve
  rw [hI, hE]

/-- Three features. -/
def P : GMParams := ⟨3⟩

/-- **Global matching lacks certainty.** After 27 traces of 000, a trace of
100 just stored: probed with 100, the echo is 000. -/
theorem not_certainty : ¬ Certainty (gmRetriever P) [] (allCodes 3) := by
  intro h
  have := h ((gmRetriever P).studyAll [] (List.replicate 27 ((bitCode 3 0)))) ⟨_, by decide, rfl⟩
    ((bitCode 3 1)) (by decide)
  revert this
  decide +kernel

/-- **Global matching lacks stability.** With 100 and 26 traces of 000, 100
retrieves itself; one more trace of 000 and it retrieves 000. -/
theorem not_stability : ¬ Stability (gmRetriever P) [] (allCodes 3) := by
  intro h
  have := h ((gmRetriever P).studyAll [] ((bitCode 3 1) :: List.replicate 26 ((bitCode 3 0))))
    ⟨_, by decide, rfl⟩ ((bitCode 3 1)) (by decide) ((bitCode 3 0)) (by decide) (by decide)
  revert this
  decide +kernel

/-- **Global matching lacks recency.** After 000 and then 110, the probe 010
returns 000, the earlier. -/
theorem not_recency : ¬ Recency (allFeatures 3) (gmRetriever P) [] (allCodes 3) := by
  intro h
  have := h [] (by decide) ((bitCode 3 0)) (by decide) ((bitCode 3 3)) (by decide) (by decide) (by decide)
    (by decide) ((bitCode 3 2)) (by decide)
  revert this
  decide +kernel

/-- **Global matching retrieves what was never studied.** After 110, 101 and
011, the probe 111 returns 111. -/
theorem not_storedOnly : ¬ StoredOnly (gmRetriever P) [] (allCodes 3) := by
  intro h
  have := h [(bitCode 3 3), (bitCode 3 5), (bitCode 3 6)] (by decide) ((bitCode 3 7)) ((bitCode 3 7)) (by decide)
  revert this
  decide +kernel

/-- **Global matching is determinate**, for every width, from every state. -/
theorem determinate (P : GMParams) (s0 : GMState) (U : List Item) :
    Determinate (gmRetriever P) s0 U := by
  intro s _ x
  show ∃ r, retrieve P s x = Dist.pure r
  unfold retrieve
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- **Global matching never has recency**, for every choice of parameters and from
every state, wherever recency can be tested: two distinct stimuli and a probe
equally similar to both. It is order-free, and no order-free memory is
recent (`not_recency_of_orderFree`). -/
theorem never_recency (P : GMParams) (s0 : GMState) (fs : List Feature) (U : List Item) (a b x : Item)
    (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b) (hx : mismatches fs x a = mismatches fs x b) :
    ¬ Recency fs (gmRetriever P) s0 U :=
  not_recency_of_orderFree fs _ s0 U (orderFree P s0 U) a b x ha hb hab hx

end GM
