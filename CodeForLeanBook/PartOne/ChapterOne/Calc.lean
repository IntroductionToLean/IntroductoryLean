import Mathlib

theorem AMGM (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a * b) ≤ (a + b) / 2 := by
  have := calc (a + b) / 2 - √(a * b)
    _ = (√a ^ 2 + √b ^ 2 - 2 * √a * √b + 2 * √a * √b) / 2 - √(a * b) := by
      simp [Real.sq_sqrt ha, Real.sq_sqrt hb]
    _ = (√a - √b) ^ 2 / 2 + √a * √b - √(a * b) := by ring
    _ = (√a - √b) ^ 2 / 2 + √(a * b) - √(a * b) := by rw [Real.sqrt_mul ha]
    _ = (√a - √b) ^ 2 / 2 := by ring
    _ ≥ 0 := div_nonneg (sq_nonneg _) (by norm_num)
  linarith


theorem AMGM' (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a * b) ≤ (a + b) / 2 := by
  rw [calc √(a * b) ≤ (a + b) / 2
    _ ↔ a * b ≤ ((a + b) / 2) ^ 2 := by
      simp only [Real.sqrt_le_iff, and_iff_right_iff_imp]
      intro h
      linarith
    _ ↔ a * b ≤ a ^ 2 / 4 + b ^ 2 / 4 + a * b / 2 := by ring_nf
    _ ↔ 0 ≤ a ^ 2 / 4 + b ^ 2 / 4 - a * b / 2 := by rw [← sub_nonneg]; ring_nf
    _ ↔ 0 ≤ ((a - b) / 2) ^ 2 := by ring_nf
    _ ↔ true := by
      simp only [iff_true]
      exact sq_nonneg ((a - b) / 2)]



example (a b c d : ℝ) : False := by
  have ineq := calc a
    _ = b := by sorry
    _ ≥ c := by sorry
    _ ≤ d := by sorry
  sorry

open CategoryTheory CategoryTheory.Limits MonoidalCategory
noncomputable def huarongdao {ℱ : Type*} [Category ℱ] [MonoidalCategory ℱ] [SymmetricCategory ℱ]
    (A B C : ℱ) : A ⊗ (B ⊗ C) ≅ (C ⊗ B) ⊗ A :=
  calc A ⊗ B ⊗ C
  _ ≅ (A ⊗ B) ⊗ C := (α_ A B C).symm
  _ ≅ (B ⊗ A) ⊗ C := β_ _ _ ⊗ᵢ Iso.refl _
  _ ≅ C ⊗ (B ⊗ A) := β_ (B ⊗ A) C
  _ ≅ (C ⊗ B) ⊗ A := (α_ C B A).symm

open TensorProduct
example (R : Type) [CommRing R] (A B C : ModuleCat R) (a : A) (b : B) (c : C) :
    (huarongdao A B C).hom (a ⊗ₜ (b ⊗ₜ c)) = (c ⊗ₜ b) ⊗ₜ a := rfl


example (A B C : Type) (a : A) (b : B) (c : C) :
    (huarongdao A B C).hom (a, (b, c)) = ((c, b), a) := rfl


-- example (R A B C : Type) [CommRing R]
--     [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
--     [Module R A] [Module R B] [Module R C] :
--     A ⊗[R] (B ⊗[R] C) ≃ₗ[R] (C ⊗[R] B) ⊗[R] A :=
--   calc A ⊗[R] B ⊗[R] C
--   _ ≃ₗ[R] (A ⊗[R] B) ⊗[R] C := sorry
--   _ ≃ₗ[R] (B ⊗[R] A) ⊗[R] C := sorry
--   _ ≃ₗ[R] C ⊗[R] (B ⊗[R] A) := sorry
--   _ ≃ₗ[R] (C ⊗[R] B) ⊗[R] A := sorry


-- exercise
noncomputable def huarongdao' {ℱ : Type*} [Category ℱ] [MonoidalCategory ℱ] [SymmetricCategory ℱ]
    (A B C D : ℱ) :
    (A ⊗ B ⊗ 𝟙_ℱ) ⊗ (𝟙_ℱ ⊗ C ⊗ D) ≅
    (A ⊗ D) ⊗ (C ⊗ B) := sorry

-- example (R : Type) [CommRing R] (r₁ r₂ : R)
--     (A B C D : ModuleCat.{0} R) (a : A) (b : B) (c : C) (d : D)  :
--     (huarongdao' A B C D).hom ((a ⊗ₜ (b ⊗ₜ r₁)) ⊗ₜ (r₂ ⊗ₜ (c ⊗ₜ d))) =
--     (r₁ • a ⊗ₜ d) ⊗ₜ (r₂ • c ⊗ₜ b) := rfl

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

-- Exercise
example : 1234 ^ 123456 ≡ 10 ^ 17 [MOD 71] := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_pow]
  calc (1234 : ZMod 71) ^ 123456
    _ = 10 ^ 17 := by sorry
