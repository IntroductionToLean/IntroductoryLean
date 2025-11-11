import Mathlib

namespace nt
#check Int.ModEq
#check Nat.ModEq

def a (n : ℕ) : ℤ :=
  2 ^ (2 * n + 1) - 2 ^ (n + 1) + 1

example (k : ℕ) : a (4 * k) ≡ 1 [ZMOD 5] :=
  calc a (4 * k)
    _ ≡ 2 ^ (8 * k + 1) - 2 ^ (4 * k + 1) + 1 [ZMOD 5] := by
      simp only [a]
      congr 1
      ring
    _ ≡ (2 ^ 4) ^ (2 * k) * 2 - (2 ^ 4) ^ k * 2 + 1 [ZMOD 5] := by
      simp only [pow_add, pow_mul, Int.reducePow, pow_one, Int.ModEq.refl]
    _ ≡ 1 ^ (2 * k) * 2 - 1 ^ k * 2 + 1 [ZMOD 5] := by
      gcongr
      · rfl
      · rfl
    _ ≡ 2 - 2 + 1 [ZMOD 5] := by
      gcongr;
      · simp
      · simp
    _ ≡ 1 [ZMOD 5] := by
      simp

example (n : ℕ) (hn : 2 ≤ n) : n ^ 2 + 5 ≤ (n + 1) ^ 2  := by
  calc n ^ 2 + 5
    _ = n ^ 2 + 2 * 2 + 1 := by ring
    _ ≤ n ^ 2 + 2 * n + 1 := by gcongr
    _ = (n + 1) ^ 2 := by ring

theorem totient_dvd_factorial (n : ℕ) (hn : 0 < n) : n.totient ∣ n.factorial := by
  let s := Nat.factorization n
  have eq1 : n.totient = (∏ p ∈ s.support, p ^ (s p - 1)) * (∏ p ∈ s.support, (p - 1)) := by
    rw [Nat.totient_eq_prod_factorization (by omega), ← Finset.prod_mul_distrib]
    rfl
  have eq2 : n.factorial = n * (n - 1).factorial := by
    conv_lhs => rw [show n = n - 1 + 1 by omega, Nat.factorial_succ, show n - 1 + 1 = n by omega]

  rw [eq1, eq2]
  gcongr
  · rw [show n = ∏ p ∈ s.support, p ^ (s p) from
      Nat.factorization_prod_pow_eq_self (n := n) (by omega) |>.symm]
    apply Finset.prod_dvd_prod_of_dvd
    intro p hp
    exact Nat.pow_dvd_pow _ (by omega)
  · rw [show (n - 1).factorial = ∏ j ∈ Finset.Ico 1 n, j by sorry]
    rw [show ∏ p ∈ s.support, (p - 1) = ∏ j ∈ Finset.Ico 1 n with j + 1 ∈ s.support, j by
      fapply Finset.prod_bij
      · exact fun p _ => p - 1
      · intro p hp
        simp only [Nat.support_factorization, Nat.mem_primeFactors, ne_eq, Finset.mem_filter,
          Finset.mem_Ico, s] at hp ⊢
        have p_ineq1 : 2 ≤ p := hp.1.two_le
        have p_ineq2 : p ≤ n := by
          exact Nat.le_of_dvd (by omega) hp.2.1
        simp only [show p - 1 + 1 = p by omega]
        exact ⟨⟨by omega, by omega⟩, hp.1, hp.2.1, by omega⟩
      · intro p hp q hq h
        simp only [Nat.support_factorization, Nat.mem_primeFactors, ne_eq, s] at hp hq ⊢
        have p_ineq : 2 ≤ p := hp.1.two_le
        have q_ineq : 2 ≤ q := hq.1.two_le
        omega
      · rintro i hi
        simp only [Finsupp.mem_support_iff, ne_eq, Finset.mem_filter, Finset.mem_Ico] at hi
        exact ⟨i + 1, by simpa using hi.2, by omega⟩
      · simp]
    apply Finset.prod_dvd_prod_of_subset
    simp

-------------


#check ZMod

variable (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]

#synth Field (ZMod p)

#check ZMod.val

#check ZMod.intCast_eq_intCast_iff
#check ZMod.natCast_eq_natCast_iff

section

@[simps]
def sq : (ZMod p)ˣ →* (ZMod p)ˣ :=
  { toFun := fun x => x ^ 2
    map_one' := by simp
    map_mul' x y := by ext; simpa using by ring }

example : Set.ncard { x : (ZMod p)ˣ | IsSquare x } = (p - 1) / 2 := by
  have set_eq : { x : (ZMod p)ˣ | IsSquare x } = MonoidHom.range (sq p) := by
    ext x; simp [IsSquare, pow_two, eq_comm]
  rw [set_eq]

  have card_eq₀ : Set.ncard {x : (ZMod p)ˣ | x ^ 2 = 1} = 2 := by
    rw [show {x : (ZMod p)ˣ | x ^ 2 = 1} = {1, -1} by
      ext x
      simp only [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, sq_eq_one_iff,
        Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Units.val_neg]]
    rw [Set.ncard_insert_of_notMem, Set.ncard_singleton]
    sorry
  rw [Set.ncard_eq_toFinset_card, Set.Finite.toFinset_setOf] at card_eq₀

  let e : (ZMod p)ˣ ⧸ MonoidHom.ker (sq p) ≃* MonoidHom.range (sq p) :=
    QuotientGroup.quotientKerEquivRange _

  have card_eq₁ := Fintype.card_congr e.toEquiv

  have card_eq₂ :
      Fintype.card ((ZMod p)ˣ ⧸ MonoidHom.ker (sq p)) = (p - 1) / 2 := by
    have eq := (MonoidHom.ker (sq p)).card_eq_card_quotient_mul_card_subgroup
    simp only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, MonoidHom.mem_ker,
      sq_apply] at eq
    rw [Nat.totient_prime Fact.out, Fintype.subtype_card, card_eq₀] at eq
    omega


  rw [← card_eq₂, card_eq₁, Set.ncard_eq_toFinset_card, eq_comm]
  rw [Fintype.card_subtype]
  congr 1
  ext x
  simp

end

end nt
