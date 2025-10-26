import Mathlib

open Filter Topology

#check Filter

#check Filter.atTop

#check nhds


example : Tendsto (fun n : ℕ => (1 / n : ℝ)) atTop (𝓝 0) := by
  rw [tendsto_atTop_nhds]
  intro U mem oU
  rw [Metric.isOpen_iff] at oU
  obtain ⟨r, r_pos, ball_subset⟩ := oU _ mem
  obtain ⟨N, hN⟩ := exists_lt_nsmul r_pos 1
  use max N 1
  intro n hn
  apply ball_subset
  simp only [one_div, Metric.mem_ball, dist_zero_right, norm_inv, RCLike.norm_natCast] at hn ⊢
  rw [inv_lt_iff_one_lt_mul₀]
  · rw [nsmul_eq_mul, mul_comm] at hN
    refine lt_of_lt_of_le hN ?_
    gcongr
    omega
  · simp only [Nat.cast_pos]
    omega


example : Tendsto (fun x : ℝ => 1 / x) (𝓝[>] 0) atTop := by
  rw [tendsto_atTop]
  intro R
  wlog hR : 0 < R
  · simp only [not_lt] at hR
    apply eventually_of_mem (U := Set.Ioi 0)
    · exact self_mem_nhdsWithin
    · intro x hx
      simp only [Set.mem_Ioi] at hx
      refine le_trans hR ?_
      positivity
  rw [eventually_nhdsWithin_iff, eventually_nhds_iff]
  simp only [one_div]
  use Set.Ioo (-1/R) (1 / R)
  refine ⟨?_, ?_, (by simpa using ⟨by simp [neg_div]; linarith, by linarith⟩)⟩
  · intro r hr1 hr2
    simp only [one_div, Set.mem_Ioo, Set.mem_Ioi] at hr1 hr2
    rw [le_inv_comm₀]
    · linarith [hr1.2]
    · assumption
    · assumption
  · exact isOpen_Ioo

lemma s1 : Summable (fun n : ℕ => 1 / ((n + 1) * (n + 2) : ℝ)) := by
  fapply Summable.of_nonneg_of_le
  · exact fun n => 1 / (n + 1)^2
  · intro n; positivity
  · intro n
    rw [div_le_div_iff_of_pos_left]
    · rw [pow_two]; gcongr; simp
    · norm_num
    · positivity
    · positivity
  · simpa using Real.summable_one_div_nat_add_rpow 1 2

#check Real.summable_one_div_nat_add_rpow

example : ∑' n : ℕ, (1 / ((n + 1) * (n + 2)) : ℝ) = 1 := by
  suffices : Tendsto (fun n => ∑ i ∈ Finset.range n, 1 / ((i + 1) * (i + 2) : ℝ)) atTop (𝓝 1)
  · exact tendsto_nhds_unique s1.tendsto_sum_tsum_nat this

  rw [tendsto_congr (f₂ := fun n => ∑ i ∈ Finset.range n, (1 / (i + 1) - 1 / (i + 2) : ℝ))
    (fun n => Finset.sum_congr rfl fun i hi => by field_simp; norm_num)]

  rw [tendsto_congr (f₂ := fun n =>
    ∑ i ∈ Finset.range n, (1 / (i + 1) : ℝ) -
    ∑ i ∈ Finset.range n, (1 / (i + 2) : ℝ)) (fun n => Finset.sum_sub_distrib _ _)]

  rw [← tendsto_add_atTop_iff_nat 1]

  rw [tendsto_congr (f₂ := fun n =>
    1 + ∑ i ∈ Finset.range n, (1 / (i + 2) : ℝ) -
    (∑ i ∈ Finset.range (n + 1), (1 / (i + 2) : ℝ))) (fun n => by
    simp only [one_div, Finset.sum_range_succ', Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero,
      zero_add, inv_one, sub_left_inj]
    ring_nf)]

  rw [tendsto_congr (f₂ := fun n =>
    1 + ∑ i ∈ Finset.range n, (1 / (i + 2) : ℝ) -
    ((∑ i ∈ Finset.range n, (1 / (i + 2) : ℝ)) + 1 / (n + 2))) (fun n => by
    rw [Finset.sum_range_succ])]

  rw [tendsto_congr (f₂ := fun n : ℕ => (1 - 1 / (n + 2 : ℕ) : ℝ)) (fun n => by simp; ring)]

  rw [tendsto_add_atTop_iff_nat (f := fun n : ℕ => 1 - (1 / n : ℝ)) 2]
  rw [show 𝓝 (1 : ℝ) = 𝓝 (1 - 0) by ring]
  rw [tendsto_const_sub_iff]
  exact tendsto_one_div_atTop_nhds_zero_nat

open Real

example (n : ℕ) (x : ℝ) :
    deriv (fun x : ℝ => sin x ^ n) x =  n * sin x ^ (n - 1) * cos x :=
  calc deriv (fun x : ℝ => sin x ^ n) x
    _ = deriv (sin ^ n) x := by rfl
    _ = n * sin x ^ (n - 1) * deriv sin x := by rw [deriv_pow]; exact differentiableAt_sin
    _ = n * sin x ^ (n - 1) * cos x := by rw [Real.deriv_sin]


example (n : ℕ) (x : ℝ) :
    deriv (fun x : ℝ => sin (x ^ n)) x = n * cos (x ^ n) * x ^ (n - 1) :=
  calc deriv (fun x : ℝ => sin (x ^ n)) x
    _ = deriv (sin ∘ fun x : ℝ => x ^ n) x := by rfl
    _ = deriv sin (x ^ n) * deriv (fun x : ℝ => x ^ n) x := by
      rw [deriv_comp]
      · exact differentiableAt_sin
      · exact differentiableAt_pow n
    _ = cos (x ^ n) * n * x ^ (n - 1) := by
      simp only [Real.deriv_sin, differentiableAt_fun_id, deriv_fun_pow, deriv_id'', mul_one]
      ring
    _ = _ := by ring

example (x : ℝ) (hx : 0 < x) : deriv (fun x : ℝ => x ^ x) x = x ^ x + x ^ x * log x :=
  sorry
