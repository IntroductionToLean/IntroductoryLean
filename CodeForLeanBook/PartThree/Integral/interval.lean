import Mathlib

open MeasureTheory Real Filter

example : ∫ x in (0)..1, x = 1 / 2 := by sorry

#check Set.uIcc

#check intervalIntegral.integral_eq_sub_of_hasDerivAt

#check intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto

lemma deriv_log_div (n : ℕ) :
    Set.EqOn
      (deriv (fun x : ℝ => log x / x))
      (fun x => (1 - log x) / (x ^ 2))
      (Set.Icc 1 n) := by
  intro x hx
  simp only [Set.mem_Icc] at hx ⊢
  rw [deriv_fun_div (differentiableOn_log.differentiableAt (by simpa using by linarith))
    (by fun_prop) (by linarith)]
  simp only [deriv_log', deriv_id'', mul_one]
  have x0 : x ≠ 0 := by linarith
  field_simp

lemma integral_log_div (n : ℕ) (hn : 2 ≤ n) :
    ∫ x in (1)..n, log x / x = (log n) ^ 2 / 2 := by
  have eq := intervalIntegral.integral_deriv_comp_smul_deriv
    (g := fun x => x ^ 2 / 2) (g' := id)
    (f := log) (f' := fun x => 1 / x)
    (a := 1) (b := n)
    (by
      rw [Set.uIcc_of_le (by norm_cast; linarith)]
      simp only [Set.mem_Icc, one_div, and_imp]
      intro x hx1 hx2
      exact hasDerivAt_log (by linarith))
    (by
      rw [Set.uIcc_of_le (by norm_cast; linarith)]
      simp only [Set.mem_Icc, id_eq, and_imp]
      intro x hx1 hx2
      simpa using hasDerivAt_pow 2 (log x) |>.div_const 2 )
    (ContinuousOn.div₀ (by fun_prop) (by fun_prop) (by
      rw [Set.uIcc_of_le (by norm_cast; linarith)]
      simp only [Set.mem_Icc, id_eq, and_imp]
      intros
      linarith))
    (by fun_prop)
  simp only [one_div, Function.comp_apply, id_eq, smul_eq_mul, log_one, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div, sub_zero] at eq
  rw [← eq]
  refine intervalIntegral.integral_congr ?_
  intro x hx
  simpa using by field_simp

lemma sum0 (n : ℕ) (hn : 2 ≤ n) (f : ℝ → ℝ) :
    ∑ k ∈ Finset.Ico 1 n, ((f k + f (k + 1)) / 2) =
    (∑ i ∈ Finset.Ico 1 (n + 1), f i) - ((f 1 + f n) / 2) := by
  calc ∑ k ∈ Finset.Ico 1 n, ((f k + f (k + 1)) / 2)
    _ = ∑ k ∈ Finset.Ico 1 (n + 1), ((f k + f (k + 1)) / 2) -
      ((f n + f (n + 1)) / 2) := by rw [Finset.sum_Ico_succ_top (by linarith)]; ring
    _ = (∑ k ∈ Finset.Ico 1 (n + 1), f k / 2)
      + (∑ k ∈ Finset.Ico 1 (n + 1), f (k + 1) / 2) - ((f n + f (n + 1)) / 2) := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
      ring
    _ = (∑ k ∈ Finset.Ico (0 + 1) (n + 1), f k / 2)
      + (∑ k ∈ Finset.Ico 1 (n + 1), f (k + 1) / 2) - ((f n + f (n + 1)) / 2) := by rfl
    _ = (∑ k ∈ Finset.Ico 0 n, f (k + 1) / 2)
      + (∑ k ∈ Finset.Ico 1 (n + 1), f (k + 1) / 2) - ((f n + f (n + 1)) / 2) := by
      congr 2
      rw [← Finset.sum_Ico_add]
      refine Finset.sum_congr rfl ?_
      intros
      simpa using by ring_nf
    _ = ((∑ k ∈ Finset.Ico 0 n, f (k + 1) / 2)
      + (∑ k ∈ Finset.Ico 0 n, f (k + 1) / 2)
      - f 1 / 2
      + f (n + 1) / 2 )
      - ((f n + f (n + 1)) / 2) := by
      congr 1
      rw [Finset.sum_Ico_succ_top (by linarith)]
      rw [Finset.sum_eq_sum_Ico_succ_bot (by linarith)]
      simpa using by ring
     _ = ((∑ k ∈ Finset.Ico 0 n, f (k + 1) / 2)
      + (∑ k ∈ Finset.Ico 0 n, f (k + 1) / 2))
      - f 1 / 2
      + f (n + 1) / 2
      - ((f n + f (n + 1)) / 2) := by ring
    _ = (∑ i ∈ Finset.Ico 0 n, f (i + 1))
      - f 1 / 2
      + f (n + 1) / 2
      - ((f n + f (n + 1)) / 2):= by
      congr 3
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intros
      field_simp
    _ = (∑ i ∈ Finset.Ico (0 + 1) (n + 1), f i)
      - f 1 / 2
      + f (n + 1) / 2
      - ((f n + f (n + 1)) / 2):= by
      congr 1
      rw [← Finset.sum_Ico_add]
      simpa using Finset.sum_congr rfl fun _ _ => by ring_nf
    _ = (∑ i ∈ Finset.Ico 1 (n + 1), f i)
      - (f 1 + f n) / 2 := by ring

lemma EM (n : ℕ) (hn : 2 ≤ n) (f : ℝ → ℝ)
    (continuous_f : ContinuousOn f (Set.Icc 1 n))
    (diff_f : DifferentiableOn ℝ f (Set.Ioo 1 n))
    (continuous_deriv_f : ContinuousOn (deriv f) (Set.Icc 1 n)) :
    ∑ k ∈ Finset.Ico 1 (n + 1), f k =
    (f 1 + f n) / 2 + (∫ x in (1)..n, f x) + (∫ x in (1)..n, deriv f x * (x - ⌊x⌋ - 2⁻¹)) := by
  have eq0 (k : ℕ) (hk : k ∈ Finset.Ico 1 n) :
      ∫ x in (k : ℝ)..(k + 1 : ℝ), (x - k - 2⁻¹) * deriv f x =
      (f k + f (k + 1)) / 2 - ∫ x in (k : ℝ)..(k + 1 : ℝ), f x := by
    rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (u := fun x => x - k - 2⁻¹) (u' := 1)
      (v := f) (v' := deriv f) (a := k) (b := k + 1)
      (by fun_prop)
      (by
        refine continuous_f |>.mono (Set.Icc_subset_Icc
          (by simp at hk ⊢; exact_mod_cast hk.1)
          (by simp at hk ⊢; norm_cast; linarith)))
      (by simpa using fun x _ _ => hasDerivAt_id' x)
      (by
        simp only [Finset.mem_Ico, le_add_iff_nonneg_right, zero_le_one, inf_of_le_left,
          sup_of_le_right, Set.mem_Ioo, hasDerivAt_deriv_iff, and_imp] at hk ⊢
        intro x hx1 hx2
        refine diff_f.differentiableAt <| Ioo_mem_nhds (lt_of_le_of_lt (by exact_mod_cast hk.1) hx1)
          (lt_of_lt_of_le hx2 (by norm_cast; exact hk.2)))
      (ContinuousOn.intervalIntegrable <| by fun_prop)
      (ContinuousOn.intervalIntegrable <| by
        simp only [le_add_iff_nonneg_right, zero_le_one, Set.uIcc_of_le]
        refine continuous_deriv_f.mono (Set.Icc_subset_Icc
          (by simp at hk ⊢; exact_mod_cast hk.1)
          (by simp at hk ⊢; norm_cast; linarith)))]
    simp only [add_sub_cancel_left, sub_self, zero_sub, neg_mul, sub_neg_eq_add, Pi.one_apply,
      one_mul, sub_left_inj]
    field_simp
    ring

  have eq1 : ∫ x in (1)..n, (x - ⌊x⌋ - 2⁻¹) * deriv f x =
      ∑ k ∈ Finset.Ico 1 n, ∫ x in (k : ℝ)..(k + 1 : ℝ), (x - k - 2⁻¹) * deriv f x := by
      have eq0 := intervalIntegral.sum_integral_adjacent_intervals_Ico (a := Nat.cast)
        (m := 1) (n := n) (f := fun x => (x - ⌊x⌋ - 2⁻¹) * deriv f x) (μ := volume) (by linarith)
        (by
          simp only [Set.mem_Ico, Nat.cast_add, Nat.cast_one, and_imp]
          intro k hk0 hk1
          refine IntervalIntegrable.mul_continuousOn ?_
            (continuous_deriv_f.mono (Set.Icc_subset_Icc
              (by simp at hk0 ⊢; exact_mod_cast hk0)
              (by simp at hk0 ⊢; norm_cast)))
          refine .sub (.sub intervalIntegral.intervalIntegrable_id ?_) intervalIntegrable_const
          refine .congr (f := fun x => (k : ℝ)) intervalIntegrable_const ?_
          fapply eventually_of_mem (U := Set.Ioo (k : ℝ) (k + 1 : ℝ))
          · simp only [le_add_iff_nonneg_right, zero_le_one, Set.uIoc_of_le, measurableSet_Ioc,
            ae_restrict_eq, mem_inf_iff, mem_principal]
            refine ⟨{(k + 1 : ℝ)}ᶜ, by simp [mem_ae_iff], _, (by rfl), ?_⟩
            ext x
            simp only [Set.mem_Ioo, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
              Set.mem_Ioc]
            constructor
            · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1, h2.le⟩
            · rintro ⟨h1, h2, h3⟩; exact ⟨h2, lt_of_le_of_ne h3 h1⟩
          · simp only [Set.mem_Ioo, and_imp]
            intro x hx1 hx2
            symm
            rw [Int.floor_eq_on_Ico k]
            · simp
            · simpa using ⟨by linarith, by linarith⟩)
      norm_cast at eq0
      rw [← eq0]
      refine Finset.sum_congr rfl ?_
      simp only [Finset.mem_Ico, Nat.cast_add, Nat.cast_one, and_imp]
      intro k hk0 hk1
      refine intervalIntegral.integral_congr_ae ?_
      refine eventually_of_mem (U := {(k + 1 : ℝ)}ᶜ) (by simp [mem_ae_iff]) ?_
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, le_add_iff_nonneg_right, zero_le_one,
        Set.uIoc_of_le, Set.mem_Ioc, mul_eq_mul_right_iff, sub_left_inj,
        and_imp]
      intro x hx0 hx1 hx2
      left
      rw [Int.floor_eq_on_Ico k]
      · simp
      · simpa using ⟨by linarith, lt_of_le_of_ne hx2 hx0⟩

  have eq2 := calc ∫ x in (1)..n, (x - ⌊x⌋ - 2⁻¹) * deriv f x
    _ = ∑ k ∈ Finset.Ico 1 n, ((f k + f (k + 1)) / 2 - ∫ x in (k : ℝ)..(k + 1 : ℝ), f x) := by
      rw [eq1]
      exact Finset.sum_congr rfl eq0
    _ = (∑ k ∈ Finset.Ico 1 n, ((f k + f (k + 1)) / 2))
      - ∑ k ∈ Finset.Ico 1 n, (∫ x in (k : ℝ)..(k + 1 : ℝ), f x) := by rw [Finset.sum_sub_distrib]
    _ = (∑ k ∈ Finset.Ico 1 n, ((f k + f (k + 1)) / 2))
      - ∫ x in (1)..n, f x := by
      congr 1
      have eq0 := intervalIntegral.sum_integral_adjacent_intervals_Ico (a := Nat.cast)
        (m := 1) (n := n) (f := f) (μ := volume) (by linarith)
        (by
          simp only [Set.mem_Ico, Nat.cast_add, Nat.cast_one, and_imp]
          intro k hk0 hk1
          refine ContinuousOn.intervalIntegrable <| continuous_f.mono ?_
          simpa using Set.Icc_subset_Icc (by simp at hk0 ⊢; exact_mod_cast hk0) (by norm_cast))
      norm_cast at eq0
      simp [← eq0]
    _ = ((∑ k ∈ Finset.Ico 1 (n + 1), f k) - (f 1 + f n) / 2)
      - ∫ x in (1)..n, f x := by congr 1; rw [sum0 n hn f]

  grind
