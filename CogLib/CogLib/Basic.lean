/-
Basic facts about rationals and lists that the library uses throughout.
Core Lean's `Rat` has few order lemmas; these fill the gaps, once.
-/

namespace Cog

theorem sum_nonneg (l : List Rat) (h : ∀ r ∈ l, 0 ≤ r) : 0 ≤ l.sum := by
  induction l with
  | nil => simp
  | cons r l ih =>
    simp only [List.sum_cons]
    have h1 := h r (List.mem_cons_self ..)
    have h2 := ih fun q hq => h q (List.mem_cons_of_mem r hq)
    grind

theorem sum_replicate (j : Nat) (a : Rat) : (List.replicate j a).sum = (j : Rat) * a := by
  induction j with
  | zero => simp
  | succ j ih => simp [List.replicate_succ, ih]; grind

theorem pow_pos' (m : Rat) (h : 0 < m) : ∀ k : Nat, 0 < m ^ k
  | 0 => by rw [Rat.pow_zero]; decide
  | k + 1 => by rw [Rat.pow_succ]; exact Rat.mul_pos (pow_pos' m h k) h

theorem pow_le_pow_of_le {x y : Rat} (n : Nat) (h0 : 0 ≤ x) (h : x ≤ y) : x ^ n ≤ y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Rat.pow_succ, Rat.pow_succ]
    have hx : 0 ≤ x ^ n := Rat.pow_nonneg h0
    have hy : 0 ≤ y ^ n := Rat.le_trans hx ih
    have h1 : x ^ n * x ≤ y ^ n * x := Rat.mul_le_mul_of_nonneg_right ih h0
    have h2 : y ^ n * x ≤ y ^ n * y := Rat.mul_le_mul_of_nonneg_left h hy
    exact Rat.le_trans h1 h2

theorem div_nonneg' {a b : Rat} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by
  rw [Rat.div_def]
  apply Rat.mul_nonneg ha
  by_cases h : b = 0
  · subst h; rw [Rat.inv_zero]; exact Rat.le_refl
  · exact Rat.le_of_lt (Rat.inv_pos.mpr (Rat.lt_of_le_of_ne hb (Ne.symm h)))

/-- Comparing quotients by cross-multiplying. -/
theorem div_le_div_cross {a b c d : Rat} (hb : 0 < b) (hd : 0 < d) (h : a * d ≤ c * b) :
    a / b ≤ c / d := by
  have hb' : b ≠ 0 := by grind
  have hd' : d ≠ 0 := by grind
  have e1 : a / b = (a * d) * (b * d)⁻¹ := by grind
  have e2 : c / d = (c * b) * (b * d)⁻¹ := by grind
  rw [e1, e2]
  apply Rat.mul_le_mul_of_nonneg_right h
  exact Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hb hd))

/-- Cross-multiplying an equality of fractions. -/
theorem mul_eq_mul_of_div_eq (a b c d : Rat) (hb : b ≠ 0) (hd : d ≠ 0) (h : a / b = c / d) : a * d = c * b := by
  calc a * d = a / b * b * d := by rw [Rat.div_mul_cancel hb]
    _ = c / d * d * b := by rw [h]; grind
    _ = c * b := by rw [Rat.div_mul_cancel hd]

theorem sum_zero (l : List Rat) (h : ∀ r ∈ l, r = 0) : l.sum = 0 := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    simp only [List.sum_cons, h r (List.mem_cons_self ..),
      ih fun q hq => h q (List.mem_cons_of_mem r hq)]
    grind

theorem sum_append_swap {α : Type} (s : List α) (a b : α) (g : α → Rat) :
    (((s ++ [a]) ++ [b]).map g).sum = (((s ++ [b]) ++ [a]).map g).sum := by
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  grind

end Cog
