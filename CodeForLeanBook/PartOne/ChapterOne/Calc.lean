import Mathlib

-- calc mode
-- induction
theorem AMGM (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a * b) ≤ (a + b) / 2 := by
  have := calc (a + b) /2 - √(a * b)
    _ = (√a ^ 2 + √b^2) / 2 - √(a * b) := by
      rw [Real.sq_sqrt hb, Real.sq_sqrt ha]
    _ = (√a - √b) ^2 / 2 + √a * √b - √(a * b) := by ring
    _ = (√a - √b) ^2 / 2 + √(a * b) - √(a * b) := by
      rw [Real.sqrt_mul]; assumption
    _ = (√a - √b) ^2 / 2 := by ring
    _ ≥ 0 := by
      apply div_nonneg
      · exact sq_nonneg (√a - √b)
      · norm_num
  linarith


theorem AMGM' (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a * b) ≤ (a + b) / 2 := by
  rw [calc √(a * b) ≤ (a + b) / 2
    _ ↔ a * b ≤ ((a + b) / 2) ^ 2 := by
      rw [Real.sqrt_le_iff]
      simp only [and_iff_right_iff_imp]
      intro _
      linarith
    _ ↔ a * b ≤ (a ^ 2 + b ^ 2 + 2 * a * b) / 4 := by ring
    _ ↔ 0 ≤ (a ^ 2 + b ^ 2 + 2 * a * b) / 4 - a * b := by exact Iff.symm sub_nonneg
    _ ↔ 0 ≤ (a - b) ^ 2 / 4 := by ring]
  have ineq : 0 ≤ (a - b) ^ 2  := by exact sq_nonneg (a - b)
  positivity

example (a b c d : ℝ) : False := by
  have ineq := calc a
    _ ≥ b := by sorry
    _ = c := by sorry
    _ ≥ d := by sorry
  -- a = b ≥ c ≥ d
  sorry

#check Nat.cauchy_induction

-- Lean Fin n: 0,...,n-1 n numbers
-- x_1, x_2, ..., x_n


example (n : ℕ) : n + 1 + 1 = n + 2 := rfl
example (n : ℕ) : n + 1 + 1 = 1 + n + 1 := rfl

theorem AMGM_full (n : ℕ)
      (x : Fin (n + 1) → ℝ) (hx : ∀ i, 0 ≤ x i) :
      (∏ i, x i)^(1/(n + 1) : ℝ) ≤ (∑ i, x i) / (n + 1) := by
  induction n using Nat.cauchy_induction (seed := 1) (f := (fun n => 2 * n + 1)) with
  | h n ih =>
    set x_last := (∑ i : Fin (n + 1), x i) / (n + 1) with x_last_eq
    have x_last_nonneg : 0 ≤ x_last := by
      apply div_nonneg
      · apply Finset.sum_nonneg
        intro i hi
        exact hx i
      · positivity
    have ih := ih (Fin.cons x_last x) (by
      intro i
      induction i using Fin.inductionOn
      · simp only [Fin.cons_zero]
        assumption
      · simp only [Fin.cons_succ]
        exact hx _)
    rw [show ((n + 1 : ℕ) : ℝ) + 1 = (n + 2) by
      simp only [Nat.cast_add, Nat.cast_one]
      ring] at ih
    have eq : (∑ i : Fin (n +  2), Fin.cons x_last x i) / (n + 2 : ℝ) = x_last := by
      sorry
    rw [eq] at ih
    conv_rhs at ih => rw [x_last_eq]
    -- without loss of generality
    wlog h_pos : ∀ i, 0 < x i
    · simp only [not_forall, not_lt] at h_pos
      rcases h_pos with ⟨i, hi⟩
      have hi' : x i = 0 := by linarith [hx i]
      have lhs : (∏ i, x i)  = 0 := by
        apply Finset.prod_eq_zero (i := i)
        · simp
        · assumption
      simp only [lhs, one_div, ge_iff_le]
      rw [Real.zero_rpow]
      · assumption

      · simp only [ne_eq, inv_eq_zero]
        positivity

    have mono : MonotoneOn (fun r : ℝ => r ^ (n + 2 : ℝ)) {x | 0 ≤ x} := by
      sorry

    have ineq : ∏ i, Fin.cons x_last x i ≤ x_last ^ (n + 2 : ℝ) := by
      have ineq := mono sorry sorry ih
      simp only [Fin.prod_cons, one_div, ge_iff_le] at ineq ⊢
      rw [Real.rpow_inv_rpow] at ineq
      · exact ineq
      · sorry
      · sorry
    simp only [Fin.prod_cons] at ineq
    rw [show x_last ^ (n + 2 : ℝ) = x_last ^ (n + 2) by
      rw [← Real.rpow_natCast]
      simp, pow_succ'] at ineq
    rw [mul_le_mul_left] at ineq
    · have mono' : MonotoneOn (fun r : ℝ => r ^ (1 / (n + 1) : ℝ)) {x | 0 ≤ x} := by
        sorry
      have ineq' := mono' sorry sorry ineq
      simp only [one_div] at ineq'
      rw [show x_last ^ (n + 1) = x_last ^ (n + 1 : ℝ) by norm_cast] at ineq'
      rw [Real.rpow_rpow_inv] at ineq'

      · simp only [one_div, ge_iff_le]
        exact ineq'
      · sorry
      · sorry

    · sorry
  | hs =>
    simp only [Nat.reduceAdd, Fin.prod_univ_two, Fin.isValue, Nat.cast_one, one_div,
      Fin.sum_univ_two]
    sorry
  | hf n hn ih =>
    refine ⟨?_, ?_⟩
    · omega
    · -- x_0, x_1, ..., x_{2n + 1}
      -- X := x_0, x_1, ..., x_{n}, Y := x_{n + 1}, ..., x_{2n+1}
      -- y0 x_{n + 1}, y1 x_{n + 2}
      intro x hx
      let X : Fin (n + 1) → ℝ := x ∘ Fin.castLE (by omega)
      let Y : Fin (n + 1) → ℝ := x ∘ Fin.castLE (by omega) ∘ Fin.natAdd (n + 1)
      have ihX := ih X sorry
      have ihY := ih Y sorry

      have eq0 : (∏ i, X i) * (∏ i, Y i) = ∏ i, x i := by
        have : ∏ i, x i = (∏ i : Fin (n + 1) ⊕ Fin (n + 1), (x ∘ Fin.cast (by omega) ∘ (finSumFinEquiv)) i) := by sorry
        rw [Fintype.prod_sum_type] at this
        rw [this]
        rfl

      have eq1 : ∑ i, x i = ∑ i, X i + ∑ i, Y i := by
        have : ∑ i, x i = (∑ i : Fin (n + 1) ⊕ Fin (n + 1), (x ∘ Fin.cast (by omega) ∘ (finSumFinEquiv)) i) := by sorry
        rw [Fintype.sum_sum_type] at this
        rw [this]
        rfl

      sorry




#check Nat.rec
example (n : ℕ) : 2 * (∑ i : Fin n, (i : ℕ)) = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [add_tsub_cancel_right]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    calc 2 * (∑ i : Fin n, (i : ℕ) + n)
      _ = 2 * ∑ i : Fin n, (i : ℕ) + 2 * n := by ring
      _ = n * (n - 1) + 2 * n := by rw [ih]
      _ = (n + 1) * n := by
        rw [Nat.mul_sub, mul_one]
        rw [← Nat.sub_add_comm]
        · rw [Nat.add_sub_assoc]
          · rw [show 2 * n - n = n by rw [two_mul]; exact Nat.add_sub_self_left n n]
            ring
          · linarith
        · exact Nat.le_mul_self n









-----------------------
open CategoryTheory CategoryTheory.Limits MonoidalCategory
noncomputable def huarongdao {ℱ : Type*} [Category ℱ] [MonoidalCategory ℱ] [SymmetricCategory ℱ]
    (A B C : ℱ) : A ⊗ (B ⊗ C) ≅ (C ⊗ B) ⊗ A :=
  calc A ⊗ (B ⊗ C)
  _ ≅ (A ⊗ B) ⊗ C := (α_ _ _ _).symm
  _ ≅ C ⊗ (A ⊗ B) := (β_ _ _)
  _ ≅ C ⊗ (B ⊗ A) := Iso.refl _ ⊗ᵢ (β_ _ _)
  _ ≅ (C ⊗ B) ⊗ A := (α_ _ _ _).symm


open TensorProduct
example (R : Type) [CommRing R] (A B C : ModuleCat R) (a : A) (b : B) (c : C) :
    (huarongdao A B C).hom (a ⊗ₜ (b ⊗ₜ c)) = (c ⊗ₜ b) ⊗ₜ a := rfl

example (A B C : Type) (a : A) (b : B) (c : C) :
    (huarongdao A B C).hom (a, (b, c)) = ((c, b), a) := rfl


example (R A B C : Type) [CommRing R]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C] :
    A ⊗[R] (B ⊗[R] C) ≃ₗ[R] (C ⊗[R] B) ⊗[R] A :=
  calc A ⊗[R] B ⊗[R] C
  _ ≃ₗ[R] (A ⊗[R] B) ⊗[R] C := sorry
  _ ≃ₗ[R] (B ⊗[R] A) ⊗[R] C := sorry
  _ ≃ₗ[R] C ⊗[R] (B ⊗[R] A) := sorry
  _ ≃ₗ[R] (C ⊗[R] B) ⊗[R] A := sorry

#check Trans
example : ℕ ≃ ℕ × ℕ := by exact (Denumerable.eqv _).symm

example : ℕ × ℕ ≃ ℚ :=
  calc ℕ × ℕ
    _ ≃ ℕ := (Denumerable.eqv _)
    _ ≃ ℚ := (Denumerable.eqv _).symm

noncomputable def huarongdao' {ℱ : Type*} [Category ℱ] [MonoidalCategory ℱ] [SymmetricCategory ℱ]
    (A B C D : ℱ) :
    (A ⊗ B ⊗ 𝟙_ℱ) ⊗ (𝟙_ℱ ⊗ C ⊗ D) ≅
    (A ⊗ D) ⊗ (C ⊗ B) := sorry

example (R : Type) [CommRing R] (r₁ r₂ : R)
    (A B C D : ModuleCat.{0} R) (a : A) (b : B) (c : C) (d : D)  :
    (huarongdao' A B C D).hom ((a ⊗ₜ (b ⊗ₜ r₁)) ⊗ₜ (r₂ ⊗ₜ (c ⊗ₜ d))) =
    (r₁ • a ⊗ₜ d) ⊗ₜ (r₂ • c ⊗ₜ b) := by rfl




example : {n : ℕ | Even n} ≃ ℚ × ℚ :=
  calc ({n : ℕ | Even n} : Type)
    _ ≃ ℕ :=
      { toFun n := n.1 / 2
        invFun n := ⟨2 * n, by simp⟩
        left_inv := by rintro ⟨_, ⟨m, rfl⟩⟩; grind
        right_inv := by intro n; simp }
    _ ≃ ℚ × ℚ := (Denumerable.eqv _).symm


example (p : ℕ) [Fact <| Nat.Prime p] (a : ZMod p) (h : a ≠ 0) :
    a ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h

instance : Fact (Nat.Prime 71) where
  out := by decide

example : 1234 ^ 123456 ≡ 10^17 [MOD 71] := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow]
  sorry
  -- calc (1234 : ZMod 71) ^ 123456
