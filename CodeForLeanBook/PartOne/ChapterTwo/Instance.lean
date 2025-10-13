import Mathlib

variable (F : Type) [Field F]

example : IsEmpty (Units F ≃* Multiplicative F) := by
  by_contra r
  simp only [not_isEmpty_iff] at r
  obtain ⟨g⟩ := r
  have h1 : g 1 = Multiplicative.ofAdd 0 := by simp
  let a := (g (-1)).toAdd
  have eq1 := calc 2 • a
    _ = 2 • (g (-1)).toAdd := rfl
    _ = (g (-1)).toAdd + (g (-1)).toAdd := by rw [two_nsmul]
    _ = (g (-1) * g (-1)).toAdd := by simp
    _ = (g ((-1) * (-1))).toAdd := by rw [g.map_mul]
    _ = (g 1).toAdd := by simp
    _ = Multiplicative.toAdd 1 := by simp
    _ = 0 := by simp
  simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_eq_zero] at eq1
  sorry
