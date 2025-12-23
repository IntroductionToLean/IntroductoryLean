import Mathlib

suppress_compilation

open Real Filter Topology MeasureTheory

def T (N : ℕ) : ℝ :=
  ∑ ⟨m, n⟩ ∈ (Finset.Ico 1 (N + 1) ×ˢ Finset.Ico 1 (N + 1)),
    1 / (m * n * (m + n))

lemma T_eq (N : ℕ) :
    T N =
    ∫ x in (0)..1, x⁻¹ *
        (∑ m ∈ Finset.Ico 1 (N + 1), x^m / m) *
        (∑ n ∈ Finset.Ico 1 (N + 1), x^n / n) := by
  calc T N
    _ = ∑ ⟨m, n⟩ ∈ (Finset.Ico 1 (N + 1) ×ˢ Finset.Ico 1 (N + 1)),
          1 / (m * n * (m + n)) := rfl
    _ = ∑ ⟨m, n⟩ ∈ (Finset.Ico 1 (N + 1) ×ˢ Finset.Ico 1 (N + 1)),
          ∫ x in (0)..1, 1 / (m * n) * x^(m + n - 1) := by
      refine Finset.sum_congr rfl ?_
      simp only [Finset.mem_product, Finset.mem_Ico, one_div, mul_inv_rev,
        intervalIntegral.integral_const_mul, integral_pow, one_pow, ne_eq, Nat.add_eq_zero,
        one_ne_zero, and_false, not_false_eq_true, zero_pow, sub_zero, and_imp, Prod.forall]
      intro m n hm0 hm1 hn0 hn1
      rw [Nat.cast_sub (by omega)]
      field_simp
      ring
    _ = ∫ x in (0)..1, ∑ ⟨m, n⟩ ∈ (Finset.Ico 1 (N + 1) ×ˢ Finset.Ico 1 (N + 1)),
          1 / (m * n) * x^(m + n - 1) := by
      rw [intervalIntegral.integral_finset_sum]
      simp
    _ = ∫ x in (0)..1, x⁻¹ *
        (∑ m ∈ Finset.Ico 1 (N + 1), x^m / m) *
        (∑ n ∈ Finset.Ico 1 (N + 1), x^n / n) := by
      refine intervalIntegral.integral_congr_ae ?_
      refine .of_forall ?_
      intro x hx
      simp only [zero_le_one, Set.uIoc_of_le, Set.mem_Ioc, one_div, mul_inv_rev,
        Finset.mul_sum] at hx ⊢
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl fun m hm => ?_
      simp only [Finset.sum_mul]
      refine Finset.sum_congr rfl fun n hn => ?_
      simp only [Finset.mem_Ico] at hm hn ⊢
      have : (m : ℝ) ≠ 0 := by norm_cast; omega
      have : (n : ℝ) ≠ 0 := by norm_cast; omega
      have : x ≠ 0 := by linarith

      field_simp
      ring_nf
      rw [← pow_succ', show m + n - 1 + 1 = m + n by omega]
      ring

lemma T_eq' :
    T =
    fun N : ℕ => ∫ x in (0)..1, x⁻¹ *
        (∑ m ∈ Finset.Ico 1 (N + 1), x^m / m) *
        (∑ n ∈ Finset.Ico 1 (N + 1), x^n / n) :=
  funext T_eq

lemma intervalIntegrable_fact (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    IntervalIntegrable (fun x => log (1 - x) ^ 2 / x) volume a b := by
  refine ContinuousOn.intervalIntegrable <| .div₀ (.pow (.comp continuousOn_log (by fun_prop) ?_) _)
    (by fun_prop) ?_
  · intro x hx
    rw [Set.uIcc_of_le hab] at hx
    simp only [Set.mem_Icc, Set.mem_compl_iff, Set.mem_singleton_iff, sub_eq_zero] at hx ⊢
    rintro rfl
    linarith
  · rw [Set.uIcc_of_le hab]
    simp only [Set.mem_Icc, ne_eq, and_imp]
    rintro _ _ _ rfl
    linarith

lemma useful_ineq (a : ℝ) : a ≤ 1 - a ↔ a ≤ 2⁻¹ := ⟨fun _ => by linarith, fun _ => by linarith⟩

lemma useful_ineq' (a : ℝ) : 1 - a ≤ a ↔ 2⁻¹ ≤ a := ⟨fun _ => by linarith, fun _ => by linarith⟩

lemma bddAbove_integral_fact (n : ℕ) :
    ∫ x in (1 / (n + 2) : ℝ)..(1 - 1 / (n + 2) : ℝ), (log (1 - x) ^ 2) / x ≤
    2⁻¹ + (log 2 ^ 2 + 2 * log 2 + 2) := by
  calc ∫ x in (1 / (n + 2) : ℝ)..(1 - 1 / (n + 2) : ℝ), (log (1 - x) ^ 2) / x
    _ = (∫ x in (1 / (n + 2) : ℝ)..(1 / 2), (log (1 - x) ^ 2) / x)
      + ∫ x in (1 / 2)..(1 - 1 / (n + 2) : ℝ), (log (1 - x) ^ 2) / x := by
      rw [intervalIntegral.integral_add_adjacent_intervals] <;>
      apply intervalIntegrable_fact
      any_goals positivity
      any_goals norm_num
      any_goals norm_cast; omega
      any_goals simp [← useful_ineq', useful_ineq]; gcongr; norm_cast; omega
    _ ≤ (∫ x in (1 / (n + 2) : ℝ)..(1 / 2), 4 * x)
      + ∫ x in (1 / 2)..(1 - 1 / (n + 2) : ℝ), (log (1 - x) ^ 2) / x := by
      gcongr
      refine intervalIntegral.integral_mono_ae_restrict (by simp; gcongr; norm_cast; omega) ?_
        (ContinuousOn.intervalIntegrable (by fun_prop)) ?_

      · apply intervalIntegrable_fact
        any_goals positivity
        any_goals norm_num
        any_goals simp; gcongr; norm_cast; omega
      · refine eventually_of_mem (self_mem_ae_restrict measurableSet_Icc) ?_
        simp only [one_div, Set.mem_Icc, and_imp]
        intro x hx1 hx2
        have ineq1 : -2 * x ≤ log (1 - x) := by
          let h : ℝ → ℝ := fun t => log (1 - t) + 2 * t
          have m : MonotoneOn h (Set.Icc 0 2⁻¹) := by
            fapply monotoneOn_of_deriv_nonneg
            · exact convex_Icc ..
            · refine .add (.comp continuousOn_log (by fun_prop) ?_) (by fun_prop)
              rintro x ⟨hx0, hx1⟩
              simp only [Set.mem_compl_iff, Set.mem_singleton_iff, sub_eq_zero] at hx0 hx1 ⊢
              rintro rfl
              norm_num at hx1
            · simp only [interior_Icc]
              refine .add (.comp differentiableOn_log (by fun_prop) ?_) (by fun_prop)
              rintro x ⟨hx0, hx1⟩
              simp only [Set.mem_compl_iff, Set.mem_singleton_iff, sub_eq_zero] at hx0 hx1 ⊢
              rintro rfl
              norm_num at hx1
            · simp only [interior_Icc, Set.mem_Ioo, and_imp, h]
              intro x hx0 hx1
              rw [deriv_fun_add _ (by fun_prop),
                show (fun t => log (1 - t)) = log ∘ _ by rfl, deriv_comp, deriv_const_mul,
                deriv_id'', show (HSub.hSub 1 : ℝ → ℝ) = fun t => 1 - t by rfl, deriv_const_sub]
              · simp only [deriv_log', deriv_id'', mul_neg, mul_one, le_neg_add_iff_add_le,
                add_zero, h]
                rw [inv_le_comm₀ (by linarith) (by norm_num)]
                simpa [← useful_ineq', useful_ineq] using hx1.le
              any_goals fun_prop
              · exact differentiableAt_log (by linarith)
              · refine (differentiableOn_log.comp (by fun_prop) (s := {1}ᶜ) ?_).differentiableAt ?_
                · intro x hx
                  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, sub_eq_zero, h] at hx ⊢
                  tauto
                · simp only [compl_singleton_mem_nhds_iff, ne_eq, h]
                  linarith

          specialize @m 0 (by simp) x (by simpa using ⟨le_trans (by positivity) hx1, ‹_›⟩)
            (le_trans (by positivity) hx1)
          simp only [sub_zero, log_one, mul_zero, add_zero, h] at m
          linarith

        have ineq2 : - log (1 - x) ≤ 2 * x := by linarith
        calc log (1 - x) ^ 2 / x
          _ = (- log (1 - x)) * (- log (1 - x)) / x := by ring
          _ ≤ (2 * x) * (2 * x) / x := by
            gcongr
            · exact le_trans (by positivity) hx1
            · simp only [Left.nonneg_neg_iff]
              apply log_nonpos
              · linarith
              · simpa using le_trans (by positivity) hx1
            · simpa using le_trans (by positivity) hx1
          _ = 4 * x := by
            have : x ≠ 0 := by rintro rfl; simp at hx1; norm_cast at hx1
            field_simp
            ring
    _ ≤ (∫ x in (0)..(1 / 2), 4 * x)
      + ∫ x in (1 / 2)..(1 - 1 / (n + 2) : ℝ), (log (1 - x) ^ 2) / x := by
      gcongr
      fapply intervalIntegral.integral_mono_interval
      any_goals rfl
      any_goals positivity
      any_goals gcongr; norm_cast; omega
      any_goals exact ContinuousOn.intervalIntegrable <| by fun_prop
      refine eventually_of_mem (self_mem_ae_restrict measurableSet_Ioc) ?_
      simpa using by intros; positivity
    _ = 2⁻¹ + ∫ x in (1 / 2)..(1 - 1 / (n + 2) : ℝ), (log (1 - x) ^ 2) / x := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      ring
    _ ≤ 2⁻¹ + ∫ x in (1 / 2)..(1 - 1 / (n + 2) : ℝ), (log (1 - x) ^ 2) * 2 := by
      gcongr
      refine intervalIntegral.integral_mono_ae_restrict
        (by simpa [← useful_ineq', useful_ineq] using by gcongr; norm_cast; omega)
        (intervalIntegrable_fact _ _ ?_ ?_ ?_)
        ?_
        ?_
      any_goals norm_num1

      · simp only [one_div, sub_lt_self_iff, inv_pos]
        norm_cast
        omega
      · simp only [one_div, ← useful_ineq', sub_sub_cancel, useful_ineq]
        gcongr
        norm_cast
        omega
      · refine ContinuousOn.intervalIntegrable <|
          .mul (.pow (.comp continuousOn_log (by fun_prop) ?_) _) (by fun_prop)
        rw [Set.uIcc_of_le (by simp [← useful_ineq', useful_ineq]; gcongr; norm_cast; omega)]
        rintro x ⟨hx0, hx1⟩
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, sub_eq_zero]
        rintro rfl
        simp only [one_div, le_sub_self_iff, inv_nonpos] at hx1
        norm_cast at hx1
      · refine eventually_of_mem (self_mem_ae_restrict measurableSet_Icc) ?_
        simp only [one_div, Set.mem_Icc, div_inv_eq_mul, and_imp]
        intro x hx0 hx1
        rw [div_eq_mul_inv]
        gcongr
        rwa [inv_le_comm₀]
        · refine lt_of_lt_of_le (by norm_num) hx0
        · norm_num
    _ = 2⁻¹ + 2 * ∫ x in (1 / 2)..(1 - 1 / (n + 2) : ℝ), (log (1 - x) ^ 2) := by
      rw [intervalIntegral.integral_mul_const, mul_comm]
    _ = 2⁻¹ + 2 * (-∫ x in (1 / 2)..(1 / (n + 2) : ℝ), log x ^ 2) := by
      have eq0 := intervalIntegral.integral_comp_mul_deriv'
        (f := fun x => 1 - x) (f' := fun x => -1)
        (g := fun x => log x ^ 2) (a := 1 / 2) (b := 1 - 1 / (n + 2))
        (by
          intro x hx
          convert hasDerivAt_const x (1 : ℝ) |>.sub <| hasDerivAt_id x using 1
          simp)
        (by fun_prop)
        (by
          refine .pow (continuousOn_log.mono ?_) _
          rintro _ ⟨x, hx, rfl⟩
          simp only [one_div, Set.mem_compl_iff, Set.mem_singleton_iff, sub_eq_zero] at hx ⊢
          rintro rfl
          rw [Set.uIcc_of_le
            (by simpa [← useful_ineq', useful_ineq] using by gcongr; norm_cast; omega)] at hx
          simp only [Set.mem_Icc, le_sub_self_iff, inv_nonpos] at hx
          linarith)
      simp only [Function.comp_apply, mul_neg, mul_one, one_div, intervalIntegral.integral_neg,
        show 1 - (2⁻¹ : ℝ) = 2⁻¹ by norm_num, sub_sub_cancel, add_right_inj] at eq0 ⊢
      rw [← eq0]
      ring
    _ = 2⁻¹ + 2 * ∫ x in (1 / (n + 2) : ℝ)..(1 / 2), log x ^ 2 := by
      congr 2
      rw [intervalIntegral.integral_symm, neg_neg]
    _ = 2⁻¹
      + 2 *
        (2⁻¹ * (log 2 ^ 2 + 2 * log 2 + 2)
          - (n + 2 : ℝ)⁻¹ * (log (n + 2) ^ 2 + 2 * log (n + 2) + 2)) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := 1 / (n + 2)) (b := 1 / 2)
        (f := fun x => x * (log x ^ 2 - 2 * log x + 2))
        (f' := fun x => log x ^ 2)
        (by
          rw [Set.uIcc_of_le
            (by simpa [← useful_ineq', useful_ineq] using by gcongr; norm_cast; omega)]
          simp only [one_div, Set.mem_Icc, and_imp]
          intro x hx0 hx1
          have d := hasDerivAt_log (x := x) (by rintro rfl; simp at hx0; norm_cast at hx0)
          convert hasDerivAt_id x |>.mul <|
            d.pow 2 |>.sub <| d.const_mul 2 |>.sub (hasDerivAt_const x 2) using 1
          · ext x; simpa using by left; ring
          · simp only [Pi.sub_apply, Pi.pow_apply, one_mul, id_eq, Nat.cast_ofNat,
            Nat.add_one_sub_one, pow_one, sub_zero]
            have : x ≠ 0 := by rintro rfl; simp at hx0; norm_cast at hx0
            field_simp)]
      · simp
      · refine ContinuousOn.intervalIntegrable <| .pow (continuousOn_log.mono ?_) _
        rw [Set.uIcc_of_le
          (by simpa [← useful_ineq', useful_ineq] using by gcongr; norm_cast; omega)]
        rintro x ⟨hx0, hx1⟩
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, sub_eq_zero]
        rintro rfl
        simp only [one_div, inv_nonpos] at hx0
        norm_cast at hx0
    _ = 2⁻¹
      + ((log 2 ^ 2 + 2 * log 2 + 2)
          - 2 * (log (n + 2) ^ 2 / (n + 2) + 2 * log (n + 2) / (n + 2) + 2 / (n + 2))) := by
      field_simp; ring
    _ ≤ 2⁻¹ + (log 2 ^ 2 + 2 * log 2 + 2) := by
      have : 0 ≤ 2 * (log (n + 2) ^ 2 / (n + 2) + 2 * log (n + 2) / (n + 2) + 2 / (n + 2)) := by
        simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
        refine add_nonneg (add_nonneg ?_ (mul_nonneg ?_ ?_)) ?_
        any_goals positivity
        any_goals norm_num
        apply log_nonneg
        norm_cast
        omega
      linarith


lemma limit_integral_fact :
    ∃ L : ℝ, Tendsto (fun n : ℕ => ∫ x in (1 / (n + 2) : ℝ)..(1 - 1 / (n + 2) : ℝ),
      (log (1 - x) ^ 2) / x) atTop (𝓝 L) := by
  fapply Real.tendsto_of_bddAbove_monotone
  · refine ⟨2⁻¹ + (log 2 ^ 2 + 2 * log 2 + 2), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact bddAbove_integral_fact x
  · intro m n hmn
    dsimp only
    fapply intervalIntegral.integral_mono_interval
    · gcongr
    · simp only [one_div, le_sub_iff_add_le, ← two_mul]
      rw [mul_inv_le_iff₀, one_mul]
      all_goals
      · norm_cast; omega
    · gcongr
    · refine eventually_of_mem (self_mem_ae_restrict measurableSet_Ioc) ?_
      simp only [Set.mem_Ioo, and_imp]
      rintro x ⟨hx0, hx1⟩
      have : 0 < x := lt_trans (by simpa using by norm_cast; omega) hx0
      positivity
    · apply intervalIntegrable_fact
      any_goals positivity
      any_goals simp [useful_ineq]
      any_goals gcongr
      any_goals norm_cast; omega

lemma integral_calc_aux0 (n : ℕ) :
    ∫ u in ((n + 2)⁻¹)..(n + 2), (u ^ 2 * rexp (-u)) / (1 - rexp (-u)) =
    ∫ x in (1 - rexp (- (n + 2 : ℝ)⁻¹))..(1 - rexp (- (n + 2 : ℝ))), (log (1 - x) ^ 2) / x := by
  have ineq : (n + 2 : ℝ)⁻¹ ≤ n + 2 := by
    rw [inv_le_iff_one_le_mul₀ (by norm_cast; omega)]
    norm_cast
    change 0 < _ * _
    positivity
  have eq0 := intervalIntegral.integral_comp_mul_deriv'
      (f := fun x => 1 - rexp (-x))
      (f' := fun x => rexp (-x))
      (g := fun x => (log (1 - x) ^ 2) / x)
      (a := (n + 2)⁻¹) (b := n + 2)
      (by
        rw [Set.uIcc_of_le ineq]
        intro x hx
        have d0 := Real.hasDerivAt_exp _ |>.comp _ <| hasDerivAt_neg x
        have d1 := hasDerivAt_const x (1 : ℝ) |>.sub d0
        convert d1 using 1
        simp)
      (by fun_prop)
      (by
        rw [Set.uIcc_of_le ineq]
        refine .div₀ (.pow (.comp continuousOn_log (by fun_prop) ?_) _) (by fun_prop) ?_
        · rintro _ ⟨x, hx, rfl⟩
          simp only [Set.mem_Icc, sub_sub_cancel, Set.mem_compl_iff, Set.mem_singleton_iff,
            exp_ne_zero, not_false_eq_true] at hx ⊢
        · rintro _ ⟨x, hx, rfl⟩
          simp only [Set.mem_Icc, ne_eq, sub_eq_zero, eq_comm (a := (1 : ℝ)), exp_eq_one_iff,
            neg_eq_zero] at hx ⊢
          rintro rfl
          simp only [inv_nonpos] at hx
          linarith)
  simp only [Function.comp_apply, sub_sub_cancel, log_exp, even_two, Even.neg_pow, neg_add_rev,
    one_div] at eq0 ⊢
  convert eq0 using 1
  refine intervalIntegral.integral_congr_ae ?_
  refine .of_forall ?_
  rw [Set.uIoc_of_le ineq]
  intros
  ring


#check AECover.integrable_of_integral_tendsto_of_nonneg_ae

lemma integrable_fact :
    IntervalIntegrable (fun x => log (1 - x) ^ 2 / x) volume (0 : ℝ) 1 := by
  obtain ⟨L, L_spec⟩ := limit_integral_fact
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by simp)]
  change Integrable _ _
  fapply AECover.integrable_of_integral_tendsto_of_nonneg_ae
    (l := atTop (α := ℕ)) (φ := fun n => Set.Icc (1 / (n + 2 : ℝ)) (1 - 1 / (n + 2 : ℝ)))
    (I := L)
  · refine ⟨?_, fun n => measurableSet_Icc⟩
    refine eventually_of_mem  (self_mem_ae_restrict measurableSet_Ioo) ?_
    intro x hx
    simp only [Set.mem_Ioo, one_div, Set.mem_Ico, eventually_atTop, ge_iff_le] at hx ⊢
    obtain ⟨N, N_pos, N_spec⟩ := Real.exists_nat_pos_inv_lt hx.1
    obtain ⟨M, M_pos, M_spec⟩ := Real.exists_nat_pos_inv_lt (show 0 < 1 - x by linarith)
    refine ⟨N + M + 1, fun n hn => ⟨le_trans ?_ N_spec.le, ?_⟩⟩
    · gcongr; norm_cast; omega
    · rw [lt_sub_iff_add_lt] at M_spec
      rw [le_sub_iff_add_le]
      refine le_trans ?_ M_spec.le
      rw [add_comm]
      gcongr
      norm_cast
      omega
  · intro i
    refine ContinuousOn.integrableOn_Icc <| .div₀
      (.pow (.comp continuousOn_log (by fun_prop) ?_) _) (by fun_prop) ?_
    · intro x hx
      simp only [one_div, Set.mem_Icc, Set.mem_compl_iff, Set.mem_singleton_iff,
        sub_eq_zero] at hx ⊢
      rintro rfl
      simp only [le_sub_self_iff, inv_nonpos] at hx
      norm_cast at hx
      omega
    · simp only [one_div, Set.mem_Icc, ne_eq, and_imp]
      rintro _ h _ rfl
      simp only [inv_nonpos] at h
      norm_cast at h
  · refine eventually_of_mem (self_mem_ae_restrict measurableSet_Ioo) ?_
    simp only [Set.mem_Ioo, and_imp]
    intro x hx0 hx1
    positivity
  · refine L_spec.congr ?_
    intro n
    rw [intervalIntegral.integral_of_le]
    · rw [integral_Ioc_eq_integral_Ioo, integral_Icc_eq_integral_Ioo]
      simp only [one_div, measurableSet_Ioo, Measure.restrict_restrict]
      rw [Set.inter_eq_left.2]
      refine Set.Ioo_subset_Ioo ?_ ?_
      · positivity
      · simpa using by norm_cast; omega
    · simp only [one_div, le_sub_iff_add_le, ← two_mul]
      rw [mul_inv_le_iff₀, one_mul]
      all_goals
      · norm_cast; omega

#check intervalIntegral.tendsto_integral_filter_of_dominated_convergence
lemma T_lim0 :
    Tendsto T atTop (𝓝 <| ∫ x in (0)..1, (log (1 - x) ^ 2) / x) := by
  rw [T_eq']
  fapply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
  · exact fun x => log (1 - x) ^ 2 / x
  · refine .of_forall fun _ => by fun_prop
  · refine .of_forall fun n => eventually_of_mem (U := {1}ᶜ) (by simp [mem_ae_iff]) ?_
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, zero_le_one, Set.uIoc_of_le, Set.mem_Ioc,
      norm_mul, norm_inv, norm_eq_abs, and_imp]
    intro x hx0 hx1 hx2
    rw [show log (1 - x) ^ 2 / x = |x⁻¹| * -log (1 - x) * -log (1 - x) by
      rw [abs_of_nonneg (by positivity)]; ring,
      abs_inv]
    gcongr
    · have : log (1 - x) < 0 := by
        apply log_neg
        · simpa using lt_of_le_of_ne ‹_› ‹_›
        · linarith
      refine mul_nonneg (inv_nonneg.2 <| abs_nonneg _) ?_
      simpa using this.le
    all_goals
    · rw [abs_of_nonneg (by positivity)]
      have lim0 := Complex.hasSum_taylorSeries_neg_log (z := x)
        (by simpa [abs_lt] using ⟨by linarith, lt_of_le_of_ne ‹_› ‹_›⟩)
      have lim1 := Complex.hasSum_re lim0
      simp only [← Complex.ofReal_pow, Complex.div_natCast_re, Complex.ofReal_re, Complex.neg_re,
        Complex.log_re] at lim1
      rw [show log ‖1-(x:ℂ)‖ = log |1 - x| by norm_cast, abs_of_nonneg (by linarith)] at lim1
      refine lim1.summable.sum_le_tsum (Finset.Ico 1 (n + 1))
        (by simpa using by intros; positivity) |>.trans <| le_of_eq lim1.tsum_eq
  · exact integrable_fact
  · refine eventually_of_mem (U := {1}ᶜ) (by simp [mem_ae_iff]) ?_
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, zero_le_one, Set.uIoc_of_le, Set.mem_Ioc,
      and_imp]
    intro x hx1 hx2 hx3
    rw [show nhds (log (1 - x) ^ 2 / x) = nhds (x⁻¹ * -log (1 - x) * -log (1 - x)) by ring_nf]
    refine .mul (.mul tendsto_const_nhds ?_) ?_
    all_goals
    · have lim0 := Complex.hasSum_taylorSeries_neg_log (z := x)
        (by simpa [abs_lt] using ⟨by linarith, lt_of_le_of_ne ‹_› ‹_›⟩)
      have lim1 := Complex.hasSum_re lim0
      simp only [← Complex.ofReal_pow, Complex.div_natCast_re, Complex.ofReal_re, Complex.neg_re,
        Complex.log_re] at lim1
      rw [show log ‖1-(x:ℂ)‖ = log |1 - x| by norm_cast, abs_of_nonneg (by linarith)] at lim1
      rw [hasSum_iff_tendsto_nat_of_nonneg (by intros; positivity),
        ← tendsto_add_atTop_iff_nat 1] at lim1
      refine lim1.congr ?_
      intro n
      rw [Finset.sum_range_eq_add_Ico ]
      · simp
      · simp

#check AECover.integrable_of_integral_bounded_of_nonneg_ae

#check AECover.integral_tendsto_of_countably_generated

lemma integral_calc0_integrable :
    Integrable (fun u ↦ u ^ 2 * rexp (-u) / (1 - rexp (-u))) (volume.restrict (Set.Ioi 0)) := by
  fapply AECover.integrable_of_integral_bounded_of_nonneg_ae
    (l := atTop (α := ℕ))
    (φ := fun n => Set.Icc ((n + 2 : ℝ)⁻¹) (n + 2))
    (μ := volume.restrict (Set.Ioi 0))
    (f := fun u => (u ^ 2 * rexp (-u)) / (1 - rexp (-u)))
    ⟨by
      refine eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) ?_
      simp only [Set.mem_Ioi, Set.mem_Icc, eventually_atTop, ge_iff_le]
      intro x hx
      obtain ⟨N, N_spec⟩ := exists_nat_gt x
      obtain ⟨M, M_pos, M_spec⟩ := Real.exists_nat_pos_inv_lt hx
      refine ⟨M + N + 1, fun n hn => ⟨?_, ?_⟩⟩
      · rw [inv_le_iff_one_le_mul₀ (by norm_cast; omega)]
        rw [inv_lt_iff_one_lt_mul₀ (by exact_mod_cast M_pos)] at M_spec
        refine le_of_lt <| lt_of_lt_of_le M_spec ?_
        gcongr
        rify at hn
        linarith
      · refine le_of_lt <| lt_of_lt_of_le N_spec ?_
        norm_cast
        omega, fun _ => measurableSet_Icc⟩

  · exact ∫ x in (0)..1, (log (1 - x) ^ 2) / x
  · intro n
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    refine .div₀ (by fun_prop) (by fun_prop) ?_
    simp only [Set.mem_Icc, ne_eq, sub_eq_zero, eq_comm (a := (1 : ℝ)), exp_eq_one_iff, neg_eq_zero,
      and_imp]
    rintro x hx0 hx1 rfl
    simp only [inv_nonpos] at hx0
    norm_cast at hx0
  · refine eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) ?_
    intro x hx
    refine div_nonneg ?_ ?_
    · positivity
    · simpa using hx.le
  · refine .of_forall ?_
    intro n
    have eq := integral_calc_aux0 n
    have ineq : (n + 2 : ℝ)⁻¹ ≤ n + 2 := by
      rw [inv_le_iff_one_le_mul₀ (by norm_cast; omega)]
      norm_cast
      change 0 < _ * _
      positivity
    rw [intervalIntegral.integral_of_le ineq,
      ← integral_Icc_eq_integral_Ioc] at eq
    simp only [neg_add_rev] at eq
    rw [Measure.restrict_restrict_of_subset (by
      intro x
      simp only [Set.mem_Icc, Set.mem_Ioi, and_imp]
      intro hx0 hx1
      refine lt_of_lt_of_le ?_ hx0
      simpa using by norm_cast; omega), eq]
    fapply intervalIntegral.integral_mono_interval
    · simpa using by norm_cast; omega
    · simp only [tsub_le_iff_right]
      rw [show ∀ a b c : ℝ, a - b + c = a - (b - c) by intros; ring]
      simp only [le_sub_self_iff, tsub_le_iff_right, zero_add, exp_le_exp, add_neg_le_iff_le_add,
        le_neg_add_iff_add_le]
      exact ineq
    · simpa using by positivity
    · refine eventually_of_mem (self_mem_ae_restrict measurableSet_Ioc) ?_
      simp only [Set.mem_Ioc, Pi.zero_apply, and_imp]
      intro x hx0 hx1
      positivity
    · exact integrable_fact

#check AECover.integral_tendsto_of_countably_generated

lemma integral_calc0_aux1 :
    Tendsto (fun n : ℕ => ∫ u in ((n + 2)⁻¹)..(n + 2), (u ^ 2 * rexp (-u)) / (1 - rexp (-u)))
      atTop (𝓝 <| ∫ u in Set.Ioi 0, (u ^ 2 * rexp (-u)) / (1 - rexp (-u))) := by
  have :=
    AECover.integral_tendsto_of_countably_generated
      (l := atTop (α := ℕ))
      (φ := fun n => Set.Icc ((n + 2 : ℝ)⁻¹) (n + 2))
      (μ := volume.restrict (Set.Ioi 0))
      (f := fun u => (u ^ 2 * rexp (-u)) / (1 - rexp (-u)))
      ⟨by
        refine eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) ?_
        simp only [Set.mem_Ioi, Set.mem_Icc, eventually_atTop, ge_iff_le]
        intro x hx
        obtain ⟨N, N_spec⟩ := exists_nat_gt x
        obtain ⟨M, M_pos, M_spec⟩ := Real.exists_nat_pos_inv_lt hx
        refine ⟨M + N + 1, fun n hn => ⟨?_, ?_⟩⟩
        · rw [inv_le_iff_one_le_mul₀ (by norm_cast; omega)]
          rw [inv_lt_iff_one_lt_mul₀ (by exact_mod_cast M_pos)] at M_spec
          refine le_of_lt <| lt_of_lt_of_le M_spec ?_
          gcongr
          rify at hn
          linarith
        · refine le_of_lt <| lt_of_lt_of_le N_spec ?_
          norm_cast
          omega, fun _ => measurableSet_Icc⟩
      integral_calc0_integrable
  simp only [measurableSet_Icc, Measure.restrict_restrict] at this ⊢
  convert this using 1
  ext n
  have ineq : (n + 2 : ℝ)⁻¹ ≤ n + 2 := by
    rw [inv_le_iff_one_le_mul₀ (by norm_cast; omega)]
    norm_cast
    change 0 < _ * _
    positivity
  rw [intervalIntegral.integral_of_le ineq]
  rw [← integral_Icc_eq_integral_Ioc]
  congr
  simp only [Set.left_eq_inter]
  intro x hx
  simp only [Set.mem_Icc, Set.mem_Ioi] at hx ⊢
  refine lt_of_lt_of_le ?_ hx.1
  simpa using by norm_cast; omega

lemma integral_calc0_aux2 :
    Tendsto
      (fun n : ℕ => ∫ x in (1 - rexp (- (n + 2 : ℝ)⁻¹))..(1 - rexp (- (n + 2 : ℝ))),
        (log (1 - x) ^ 2) / x)
      atTop (𝓝 <| ∫ x in (0)..1, (log (1 - x) ^ 2) / x) := by
  have :=
    AECover.integral_tendsto_of_countably_generated
      (l := atTop (α := ℕ))
      (φ := fun n => Set.Icc (1 - rexp (- (n + 2 : ℝ)⁻¹)) (1 - rexp (- (n + 2 : ℝ))))
      (μ := volume.restrict (Set.Ioo 0 1))
      (f := fun x => (log (1 - x) ^ 2) / x)
      (MeasureTheory.aecover_Ioo_of_Icc
        (by
          rw [show 𝓝 (0 : ℝ) = 𝓝 (1 - 1) by simp]
          refine .sub tendsto_const_nhds ?_
          have lim0 : Tendsto rexp (nhds 0) (nhds 1) := by
            simpa using continuous_exp.tendsto 0
          have lim1 : Tendsto (fun n : ℕ => -(n + 2 : ℝ)⁻¹) atTop (𝓝 0) := by
            rw [show 𝓝 (0 : ℝ) = 𝓝 (-0) by simp]
            refine .neg ?_
            have lim1 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
              tendsto_inverse_atTop_nhds_zero_nat
            rw [← tendsto_add_atTop_iff_nat 2] at lim1
            simpa using lim1
          exact lim0.comp lim1)
        (by
          rw [show 𝓝 (1 : ℝ) = 𝓝 (1 - 0) by simp]
          refine .sub tendsto_const_nhds ?_
          have lim0 := Real.tendsto_exp_neg_atTop_nhds_zero
          have lim1 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
            tendsto_natCast_atTop_atTop
          rw [← tendsto_add_atTop_iff_nat 2] at lim1
          simp only [Nat.cast_add, Nat.cast_ofNat] at lim1
          exact lim0.comp lim1))
      (by
        have := integrable_fact
        rwa [intervalIntegrable_iff_integrableOn_Ioo_of_le (by simp)] at this)

  simp only [neg_add_rev, measurableSet_Icc, Measure.restrict_restrict] at this ⊢
  convert this using 1
  · ext n
    rw [intervalIntegral.integral_of_le (by
      gcongr
      simp only [add_neg_le_iff_le_add, le_neg_add_iff_add_le]
      rw [inv_le_iff_one_le_mul₀ (by norm_cast; omega)]
      norm_cast
      change 0 < _ * _
      positivity),
      ← integral_Icc_eq_integral_Ioc]
    congr 2
    simp only [Set.left_eq_inter]
    rintro x ⟨hx0, hx1⟩
    simp only [tsub_le_iff_right, Set.mem_Ioo] at hx0 hx1 ⊢
    constructor

    · rw [← sub_le_iff_le_add] at hx0
      refine lt_of_lt_of_le ?_ hx0
      simpa using by norm_cast; omega
    · refine lt_of_le_of_lt hx1 ?_
      simpa using by positivity

  · congr 1
    rw [intervalIntegral.integral_of_le (by simp), integral_Ioc_eq_integral_Ioo]


lemma integral_calc0 :
    ∫ u in Set.Ioi 0, (u ^ 2 * rexp (-u)) / (1 - rexp (-u)) =
    ∫ x in (0)..1, (log (1 - x) ^ 2) / x := by
  have lim0 := integral_calc0_aux1
  have lim1 := integral_calc0_aux2
  simp_rw [integral_calc_aux0] at lim0
  exact tendsto_nhds_unique lim0 lim1

lemma integral_calc1 :
    ∫ u in Set.Ioi 0, (u ^ 2 * rexp (-u)) / (1 - rexp (-u)) =
    ∫ u in Set.Ioi 0, u ^ 2 * (∑' n : ℕ, rexp (- (n + 1) * u)) := by
  refine integral_congr_ae ?_
  refine eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) ?_
  simp only [Set.mem_Ioi]
  intro x hx
  rw [mul_div_assoc]
  congr
  have eq0 := calc (∑' n : ℕ, rexp (- (n + 1) * x))
    _ = ∑' n : ℕ, rexp (- x) ^ n * rexp (- x) := by
      refine tsum_congr ?_
      intro n
      rw [← pow_succ, ← exp_nat_mul]
      simpa using by ring
    _ = rexp (- x) * ∑' n : ℕ, rexp (- x) ^ n := by
      rw [tsum_mul_right, mul_comm]


  have eq1 := geom_series_mul_neg (rexp (-x)) (by simpa)
  have eq2 : ∑' (i : ℕ), rexp (-x) ^ i = 1 / (1 - rexp (-x)) := by
    rw [eq_div_iff, eq1]
    simp only [ne_eq, sub_eq_zero]
    rw [eq_comm]
    rw [exp_eq_one_iff]
    linarith
  rw [eq2] at eq0
  rw [eq0]
  ring

lemma integral_calc2 :
    ∫ u in Set.Ioi 0, (u ^ 2 * rexp (-u)) / (1 - rexp (-u)) =
    ∫ u in Set.Ioi 0, (∑' n : ℕ, u ^ 2 * rexp (- (n + 1) * u)) := by
  rw [integral_calc1]
  refine integral_congr_ae ?_
  refine eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) ?_
  simp only [Set.mem_Ioi]
  intro x hx
  rw [tsum_mul_left]
