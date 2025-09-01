import Mathlib

variable (n : ℕ)

def nextPrime : ℕ := Nat.minFac (Nat.factorial n + 1)

lemma nextPrime_prime : Nat.Prime (nextPrime n) := by
  fapply Nat.minFac_prime
  simp only [ne_eq, Nat.add_eq_right]
  exact Nat.factorial_ne_zero n

lemma nextPrime_ge : n ≤ nextPrime n := by
  by_contra! ineq
  have h₁ :  nextPrime n ∣ Nat.factorial n := by
    refine Nat.dvd_factorial ?_ ?_
    · exact Nat.minFac_pos ..
    · linarith
  have h₂ : nextPrime n ∣ 1 := by
    rw [Nat.dvd_add_iff_right h₁]
    exact Nat.minFac_dvd ..
  have h₃ : ¬ nextPrime n ∣ 1 := Nat.Prime.not_dvd_one (nextPrime_prime n)
  contradiction


theorem exists_infinite_primes : ∃ p, n ≤ p ∧ Nat.Prime p := by
  use nextPrime n
  fconstructor
  · exact nextPrime_ge n
  · exact nextPrime_prime n

-- 此文件改编自 Mathlib 的 `Nat.exists_infinite_primes`。
