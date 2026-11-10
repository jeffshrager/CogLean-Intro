/-
The activation family (ACT-R's declarative memory, decay 1 and temperature 1)
against the laws.

Regime: from an empty memory, with a positive failure weight `θ` and a
positive discount `μ` per mismatch.

* `never_certainty`, `never_stability`, `never_orderFree`,
  `never_determinate`: lacks them for *every* positive failure weight (and
  nonnegative discount), not only at the setting `P` of the counterexamples
  `not_certainty` and the others.
* `recency`: has it, for every such choice of parameters. Of two stimuli
  studied last, the later is retrieved more often (twice as often, in fact).
* `not_certainty`: lacks it. Retrieval can fail.
* `not_stability`: lacks it. Uses decay, and new chunks compete.
* `not_orderFree`: lacks it. The order of study sets the ages of the uses.
* `not_determinate`: lacks it. After 000 and 100, the probe 000 retrieves each
  with positive probability.
* `storedOnly`: has it, for every choice of parameters. Only chunks are
  retrieved, and a chunk is made only by study.
-/

import CogLib

namespace ACTR

open Cog Laws Dist Act

/-- An empty memory. -/
def empty : ActState := ⟨0, []⟩

/-! ### Counterexamples -/

/-- All eight 3-bit codes compared, each mismatch halving the weight, failure
weight 1/10. -/
def P : ActParams := ⟨(allFeatures 3), 1 / 2, 1 / 10⟩

/-- **Activation lacks certainty**: 000, just studied, is retrieved by itself
with probability 10/11. -/
theorem not_certainty : ¬ Certainty (actRetriever P) empty (allCodes 3) := by
  intro h
  have := h empty ⟨[], by decide, rfl⟩ ((bitCode 3 0)) (by decide)
  revert this
  decide +kernel

/-- **Activation lacks stability**: studying 100 after 000 changes the chance
that 000 retrieves itself. -/
theorem not_stability : ¬ Stability (actRetriever P) empty (allCodes 3) := by
  intro h
  have := h ((actRetriever P).studyAll empty [(bitCode 3 0)]) ⟨_, by decide, rfl⟩ ((bitCode 3 0)) (by decide)
    ((bitCode 3 1)) (by decide) (by decide)
  revert this
  decide +kernel

/-- **Activation is not order-free**: 000 then 100 leaves memory retrieving
differently from 100 then 000. -/
theorem not_orderFree : ¬ OrderFree (actRetriever P) empty (allCodes 3) := by
  intro h
  have := h empty ⟨[], by decide, rfl⟩ ((bitCode 3 0)) (by decide) ((bitCode 3 1)) (by decide) ((bitCode 3 0))
  revert this
  decide +kernel

/-- **Activation is not determinate.** -/
theorem not_determinate : ¬ Determinate (actRetriever P) empty (allCodes 3) :=
  not_determinate_of_two _ _ _ _ ⟨[(bitCode 3 0), (bitCode 3 1)], by decide, rfl⟩ ((bitCode 3 0)) ((bitCode 3 0)) ((bitCode 3 1))
    (by decide) (by decide +kernel) (by decide +kernel)

/-! ### Recency, in general -/

section Recency

variable (Q : ActParams)

/-- The chance of retrieving a code that has exactly one chunk, `c`, among the
last ones. -/
theorem pRet_last (cs : List Chunk) (now : Nat) (c c' : Chunk) (x : Item)
    (hcs : c.code ∉ cs.map Chunk.code) (hc' : c'.code ≠ c.code) :
    (pRet (actRetriever Q) ⟨now, cs ++ [c, c']⟩ x c.code =
      Act.chunkWeight Q now x c / total (Act.outcomes ⟨now, cs ++ [c, c']⟩)
        (Act.weight Q ⟨now, cs ++ [c, c']⟩ x)) ∧
    (pRet (actRetriever Q) ⟨now, cs ++ [c', c]⟩ x c.code =
      Act.chunkWeight Q now x c / total (Act.outcomes ⟨now, cs ++ [c', c]⟩)
        (Act.weight Q ⟨now, cs ++ [c', c]⟩ x)) := by
  have hfil : cs.filter (fun d => d.code == c.code) = [] := by
    rw [List.filter_eq_nil_iff]
    intro d hd
    have : d.code ≠ c.code := fun h => hcs (List.mem_map.mpr ⟨d, hd, h⟩)
    simpa using this
  have hcs' : ∀ o ∈ cs.map (fun d => some d.code), (o == some c.code) = false := by
    intro o ho
    simp only [List.mem_map] at ho
    obtain ⟨d, hd, rfl⟩ := ho
    have : d.code ≠ c.code := fun h => hcs (List.mem_map.mpr ⟨d, hd, h⟩)
    simpa using this
  have hne : (c'.code == c.code) = false := by simpa using hc'
  constructor
  · show prob (Act.retrieve Q _ x) _ = _
    rw [Act.prob_retrieve]
    congr 1
    simp only [Act.outcomes, List.map_append, List.map_cons, List.map_nil, strengthIn,
      strengthIn_append, strengthIn_none _ _ _ hcs', Act.weight, List.filter_append, hfil,
      List.filter_cons, hne, beq_self_eq_true, ite_true, Bool.false_eq_true, ite_false,
      List.filter_nil, List.nil_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    grind
  · show prob (Act.retrieve Q _ x) _ = _
    rw [Act.prob_retrieve]
    congr 1
    simp only [Act.outcomes, List.map_append, List.map_cons, List.map_nil, strengthIn,
      strengthIn_append, strengthIn_none _ _ _ hcs', Act.weight, List.filter_append, hfil,
      List.filter_cons, hne, beq_self_eq_true, ite_true, Bool.false_eq_true, ite_false,
      List.filter_nil, List.nil_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    grind

/-- **Activation has recency**, from an empty memory, for every positive
discount and failure weight: of two stimuli studied last, neither studied
before, a probe equally similar to both retrieves the later twice as often
as the earlier. -/
theorem recency (U : List Item) (hμ : 0 < Q.mu) (hθ : 0 < Q.theta) :
    Recency Q.fs (actRetriever Q) empty U := by
  intro xs _ a _ b _ hab ha hb x hm
  -- The memory before `a` and `b`.
  let s1 := (actRetriever Q).studyAll empty xs
  have hcodes : ∀ c ∈ s1.chunks.map Chunk.code, c ∈ xs := by
    intro c hc
    rcases codes_studyAll Q xs empty c hc with h | h
    · simp [codes, empty] at h
    · exact h
  have ha1 : a ∉ s1.chunks.map Chunk.code := fun h => ha (hcodes a h)
  have hb1 : b ∉ s1.chunks.map Chunk.code := fun h => hb (hcodes b h)
  have hs : (actRetriever Q).studyAll empty (xs ++ [a, b]) =
      ⟨s1.now + 2, s1.chunks ++ [⟨a, [s1.now]⟩, ⟨b, [s1.now + 1]⟩]⟩ := by
    have e1 : (actRetriever Q).studyAll empty (xs ++ [a, b]) =
        Act.study (Act.study s1 a) b := by
      simp only [Retriever.studyAll, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rfl
    rw [e1]
    have hb2 : b ∉ (s1.chunks ++ [(⟨a, [s1.now]⟩ : Chunk)]).map Chunk.code := by
      simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, not_or]
      exact ⟨hb1, fun h => hab h.symm⟩
    simp only [Act.study, addUse_new _ _ _ ha1]
    rw [addUse_new _ _ _ hb2]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [hs]
  have hpa := (pRet_last Q s1.chunks (s1.now + 2) ⟨a, [s1.now]⟩ ⟨b, [s1.now + 1]⟩ x ha1
    (fun h => hab h.symm)).1
  have hpb := (pRet_last Q s1.chunks (s1.now + 2) ⟨b, [s1.now + 1]⟩ ⟨a, [s1.now]⟩ x hb1
    hab).2
  simp only at hpa hpb
  rw [hpa, hpb]
  have hT := total_pos Q ⟨s1.now + 2, s1.chunks ++ [⟨a, [s1.now]⟩, ⟨b, [s1.now + 1]⟩]⟩ x
    (Rat.le_of_lt hμ) hθ
  have hpow := pow_pos' Q.mu hμ (mismatches Q.fs x a)
  have hwa : Act.chunkWeight Q (s1.now + 2) x ⟨a, [s1.now]⟩ = 1 / 2 * Q.mu ^ mismatches Q.fs x a := by
    have h2 : s1.now + 2 - s1.now = 2 := by omega
    simp [Act.chunkWeight, Act.baseWeight, h2]
    grind
  have hwb : Act.chunkWeight Q (s1.now + 2) x ⟨b, [s1.now + 1]⟩ = Q.mu ^ mismatches Q.fs x a := by
    have h1 : s1.now + 2 - (s1.now + 1) = 1 := by omega
    simp [Act.chunkWeight, Act.baseWeight, hm, h1]
    grind
  rw [hwa, hwb]
  generalize total _ _ = T at hT ⊢
  generalize Q.mu ^ mismatches Q.fs x a = w at hpow ⊢
  rw [Rat.div_def, Rat.div_def]
  have hT' : 0 < T⁻¹ := Rat.inv_pos.mpr hT
  have : 1 / 2 * w < w := by grind
  exact Rat.mul_lt_mul_of_pos_right this hT'

/-- **Activation retrieves only what was studied**, for every choice of
parameters. -/
theorem storedOnly (U : List Item) : StoredOnly (actRetriever Q) empty U := by
  intro xs _ x y hy
  show prob (Act.retrieve Q _ x) _ = 0
  rw [Act.prob_retrieve]
  have hz : strengthIn (Act.outcomes ((actRetriever Q).studyAll empty xs))
      (Act.weight Q ((actRetriever Q).studyAll empty xs) x) (· == some y) = 0 := by
    apply strengthIn_none
    intro o ho
    simp only [Act.outcomes, List.mem_cons, List.mem_map] at ho
    rcases ho with rfl | ⟨c, hc, rfl⟩
    · rfl
    · have hcx : c.code ∈ xs := by
        rcases codes_studyAll Q xs empty c.code (List.mem_map.mpr ⟨c, hc, rfl⟩) with h | h
        · simp [codes, empty] at h
        · exact h
      have : c.code ≠ y := fun e => hy (e ▸ hcx)
      simpa using this
  rw [hz, Rat.div_def, Rat.zero_mul]

/-! ### Never, for every parameter setting

Each counterexample above is for one setting. These show the law fails for
every setting with a positive failure weight (and, where it matters, a
nonnegative discount), on any `U` with one or two stimuli. -/

theorem pRet_single (now : Nat) (c : Chunk) (x : Item) :
    pRet (actRetriever Q) ⟨now, [c]⟩ x c.code =
      Act.chunkWeight Q now x c / (Q.theta + Act.chunkWeight Q now x c) := by
  show prob (Act.retrieve Q _ x) _ = _
  rw [Act.prob_retrieve]
  simp [Act.outcomes, strengthIn, total, Act.weight]
  grind

theorem total_two (now : Nat) (c c' : Chunk) (x : Item) (h : c'.code ≠ c.code) :
    total (Act.outcomes ⟨now, [c, c']⟩) (Act.weight Q ⟨now, [c, c']⟩ x) =
      Q.theta + Act.chunkWeight Q now x c + Act.chunkWeight Q now x c' := by
  have h' : c.code ≠ c'.code := fun e => h e.symm
  simp [Act.outcomes, strengthIn, total, Act.weight, h, h']
  grind

theorem cw_self (now t : Nat) (y : Item) :
    Act.chunkWeight Q now y ⟨y, [t]⟩ = 1 / ((now - t : Nat) : Rat) := by
  simp [Act.chunkWeight, Act.baseWeight, mismatches_self, Rat.add_zero]

theorem cw_other (now t : Nat) (x y : Item) :
    Act.chunkWeight Q now x ⟨y, [t]⟩ = 1 / ((now - t : Nat) : Rat) * Q.mu ^ mismatches Q.fs x y := by
  simp [Act.chunkWeight, Act.baseWeight, Rat.add_zero]

/-- After one study, an item retrieves itself with probability `1/(θ + 1)`. -/
theorem pRet_once (y : Item) :
    pRet (actRetriever Q) (Act.study empty y) y y = 1 / (Q.theta + 1) := by
  have := pRet_single Q 1 ⟨y, [0]⟩ y
  simp only [cw_self] at this
  have e : (1 : Rat) / 1 = 1 := by decide +kernel
  show pRet (actRetriever Q) ⟨1, [⟨y, [0]⟩]⟩ y y = _
  rw [this]
  have e1 : (((1 - 0 : Nat)) : Rat) = 1 := by decide +kernel
  rw [e1, e]

/-- After `a` then `b`, the probe `a` retrieves `a` with probability
`(1/2)/(θ + 1/2 + μ^m)`, and after `b` then `a`, with `1/(θ + μ^m/2 + 1)`. -/
theorem pRet_pair (a b : Item) (hab : a ≠ b) :
    pRet (actRetriever Q) (Act.study (Act.study empty a) b) a a =
        (1 / 2) / (Q.theta + 1 / 2 + Q.mu ^ mismatches Q.fs a b) ∧
      pRet (actRetriever Q) (Act.study (Act.study empty b) a) a a =
        1 / (Q.theta + 1 / 2 * Q.mu ^ mismatches Q.fs a b + 1) := by
  have e1 : Act.study (Act.study empty a) b = ⟨2, [⟨a, [0]⟩, ⟨b, [1]⟩]⟩ := by
    simp [Act.study, empty, Act.addUse, hab]
  have e2 : Act.study (Act.study empty b) a = ⟨2, [⟨b, [0]⟩, ⟨a, [1]⟩]⟩ := by
    simp [Act.study, empty, Act.addUse, Ne.symm hab]
  have hl := pRet_last Q [] 2 ⟨a, [0]⟩ ⟨b, [1]⟩ a (by simp) (Ne.symm hab)
  have hl2 := pRet_last Q [] 2 ⟨a, [1]⟩ ⟨b, [0]⟩ a (by simp) (Ne.symm hab)
  simp only [List.nil_append] at hl hl2
  rw [e1, e2, hl.1, hl2.2, total_two Q 2 _ _ a (Ne.symm hab), total_two Q 2 _ _ a hab,
    cw_self, cw_self, cw_other, cw_other]
  constructor
  · congr 1 <;> simp <;> grind
  · congr 1 <;> simp <;> grind

/-- **Activation never has certainty**: for every positive failure weight and
nonnegative discount, on any nonempty `U`. -/
theorem never_certainty (hθ : 0 < Q.theta) (U : List Item) (y : Item) (hy : y ∈ U) :
    ¬ Certainty (actRetriever Q) empty U := by
  intro h
  have h1 := h empty ⟨[], by simp, rfl⟩ y hy
  change pRet (actRetriever Q) (Act.study empty y) y y = 1 at h1
  rw [pRet_once] at h1
  have := mul_eq_mul_of_div_eq 1 (Q.theta + 1) 1 1 (by grind) (by decide) (by rw [h1]; decide +kernel)
  grind

/-- **Activation never has stability**: for every positive failure weight and
nonnegative discount, on any `U` with two stimuli. -/
theorem never_stability (hθ : 0 < Q.theta) (hμ : 0 ≤ Q.mu) (U : List Item) (y z : Item)
    (hy : y ∈ U) (hz : z ∈ U) (hyz : y ≠ z) : ¬ Stability (actRetriever Q) empty U := by
  intro h
  have h1 := h (Act.study empty y) ⟨[y], by simp [hy], rfl⟩ y hy z hz (Ne.symm hyz)
  change pRet (actRetriever Q) (Act.study (Act.study empty y) z) y y =
    pRet (actRetriever Q) (Act.study empty y) y y at h1
  rw [(pRet_pair Q y z hyz).1, pRet_once] at h1
  have hw := Rat.pow_nonneg (n := mismatches Q.fs y z) hμ
  have := mul_eq_mul_of_div_eq _ _ _ _ (by grind) (by grind) h1
  grind

/-- **Activation is never order-free**: for every positive failure weight and
nonnegative discount, on any `U` with two stimuli. -/
theorem never_orderFree (hθ : 0 < Q.theta) (hμ : 0 ≤ Q.mu) (U : List Item) (a b : Item)
    (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b) : ¬ OrderFree (actRetriever Q) empty U := by
  intro h
  have h1 := congrArg (fun d => prob d (· == some a)) (h empty ⟨[], by simp, rfl⟩ a ha b hb a)
  change pRet (actRetriever Q) (Act.study (Act.study empty a) b) a a =
    pRet (actRetriever Q) (Act.study (Act.study empty b) a) a a at h1
  rw [(pRet_pair Q a b hab).1, (pRet_pair Q a b hab).2] at h1
  have hw := Rat.pow_nonneg (n := mismatches Q.fs a b) hμ
  have := mul_eq_mul_of_div_eq _ _ _ _ (by grind) (by grind) h1
  grind

/-- **Activation is never determinate**: for every positive failure weight,
on any nonempty `U`. A stimulus just studied may be retrieved, or retrieval
may fail. -/
theorem never_determinate (hθ : 0 < Q.theta) (U : List Item) (y : Item) (hy : y ∈ U) :
    ¬ Determinate (actRetriever Q) empty U := by
  intro h
  obtain ⟨r, hr⟩ := h (Act.study empty y) ⟨[y], by simp [hy], rfl⟩ y
  cases r with
  | some w => exact Act.retrieve_not_certain Q _ y w hr
  | none =>
    have h1 := pRet_once Q y
    have h0 : pRet (actRetriever Q) (Act.study empty y) y y = 0 := by
      change Act.retrieve Q _ y = _ at hr
      show prob (Act.retrieve Q _ y) _ = 0
      rw [hr, prob_pure]; rfl
    rw [h0] at h1
    have := mul_eq_mul_of_div_eq 0 1 1 (Q.theta + 1) (by decide) (by grind) (by rw [← h1]; decide +kernel)
    grind

end Recency

end ACTR
