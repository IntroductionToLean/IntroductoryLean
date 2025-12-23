import mathlib
import CodeForLeanBook.PartThree.Integral.interval

open Real Filter Topology MeasureTheory

suppress_compilation

def I (N : ℕ) : ℝ := ∫ x in (1)..N, (1 - log x) / x^2 * (x - ⌊x⌋ - 2⁻¹)

local notation:max "I∞" => ∫ x in Set.Ioi 1, (1 - log x) / x^2 * (x - ⌊x⌋ - 2⁻¹)

#check intervalIntegral_tendsto_integral_Ioi
#check integrableOn_Ioi_deriv_of_nonneg

lemma log_div_integrableOn : IntegrableOn (fun x ↦ log x / x ^ 2) (Set.Ioi 1) := by
  fapply integrableOn_Ioi_deriv_of_nonneg
  · exact fun x => - (log x + 1) / x
  · exact 0
  · refine .div (.neg <| .add ?_ (Continuous.continuousWithinAt (by fun_prop)))
      (Continuous.continuousWithinAt (by fun_prop)) (by norm_num)
    refine continuousOn_log.mono (by simp) |>.continuousWithinAt (by simp)
  · simp only [Set.mem_Ioi, neg_add_rev]
    intro x hx
    have := hasDerivAt_log (by linarith : x ≠ 0) |>.neg
      |>.add (hasDerivAt_const x (-1)) |>.div (hasDerivAt_id' x) (by linarith)
    convert this using 1
    · ext x
      simpa using by ring
    · field_simp
  · simp only [Set.mem_Ioi]
    intro x hx
    refine div_nonneg ?_ (by positivity)
    rw [log_nonneg_iff]
    all_goals linarith
  · rw [show nhds (0 : ℝ) = nhds (-(0 + 0)) by simp]
    simp_rw [neg_div, add_div]
    refine .neg <| .add ?_ ?_
    · simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by simp)
    · rw [show HDiv.hDiv (1 : ℝ) = fun x => x⁻¹ by ext; simp]
      exact tendsto_inv_atTop_zero

lemma one_div_sq_integrableOn : IntegrableOn (fun x : ℝ ↦ 1 / x ^ 2) (Set.Ioi 1) := by
  fapply integrableOn_Ioi_deriv_of_nonneg
  · exact fun x => - 1 / x
  · exact 0
  · refine .div (Continuous.continuousWithinAt <| by fun_prop)
      (Continuous.continuousWithinAt <| by fun_prop) (by simp)
  · simp only [Set.mem_Ioi, one_div]
    intro x hx
    convert hasDerivAt_inv (by linarith : x ≠ 0) |>.neg using 1
    · ext; field_simp
    · field_simp
  · simp only [Set.mem_Ioi, one_div, inv_nonneg]
    intros
    positivity
  · rw [show nhds (0 : ℝ) = nhds (-0) by simp]
    simp_rw [neg_div]
    refine .neg ?_
    rw [show HDiv.hDiv (1 : ℝ) = fun x => x⁻¹ by ext; simp]
    exact tendsto_inv_atTop_zero

lemma I_converges :
    Tendsto I atTop (𝓝 I∞) := by
  refine intervalIntegral_tendsto_integral_Ioi
      (f := fun x => (1 - log x) / x^2 * (x - ⌊x⌋ - 2⁻¹)) (μ := volume)
      (a := 1) (b := fun n : ℕ => n)
      (l := atTop) ?_ tendsto_natCast_atTop_atTop
  fapply Integrable.mono (g := fun x => 2⁻¹ * (log x + 1) / x ^ 2)
  · simp_rw [mul_div_assoc, add_div]
    refine .const_mul (.add log_div_integrableOn one_div_sq_integrableOn) _
  · refine .mul (ContinuousOn.aestronglyMeasurable (.div₀ (.sub (by fun_prop)
      (continuousOn_log.mono ?_)) (by fun_prop) ?_) measurableSet_Ioi)
      (.sub (by fun_prop) (by fun_prop))
    · intro x hx
      simp only [Set.mem_Ioi, Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
      linarith
    · simp only [Set.mem_Ioi, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
      intros
      linarith
  · refine eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) ?_
    simp only [Set.mem_Ioi, norm_mul, norm_div, norm_eq_abs, norm_pow, sq_abs, abs_abs, norm_inv]
    intro x hx
    calc |1 - log x| / x ^ 2 * |x - ⌊x⌋ - 2⁻¹|
      _ ≤ |log x + 1| / x ^ 2 * |x - ⌊x⌋ - 2⁻¹| := by
        gcongr ?_ / _ * _
        fapply abs_le_abs
        · simp only [tsub_le_iff_right]
          ring_nf
          simp only [le_add_iff_nonneg_right, Nat.ofNat_pos, mul_nonneg_iff_of_pos_right]
          apply log_nonneg
          linarith
        · simp only [neg_sub, tsub_le_iff_right]
          linarith
      _ = (log x + 1) / x ^ 2 * |x - ⌊x⌋ - 2⁻¹| := by
        congr
        rw [abs_of_nonneg]
        have : 0 ≤ log x := log_nonneg (by linarith)
        positivity
      _ ≤ (log x + 1) / x ^ 2 * (2⁻¹) := by
        gcongr
        · have : 0 ≤ log x := log_nonneg (by linarith)
          positivity
        simp only [Int.self_sub_floor]
        rw [abs_le]
        simp only [neg_le_sub_iff_le_add, le_add_iff_nonneg_left, Int.fract_nonneg,
          tsub_le_iff_right, true_and]
        rw [show (2⁻¹ : ℝ) + (2⁻¹ : ℝ) = 1 by norm_num]
        exact Int.fract_lt_one _ |>.le
    rw [abs_of_nonneg (by norm_num), abs_of_nonneg (by
        have : 0 ≤ log x := log_nonneg (by linarith)
        positivity)]
    ring_nf
    rfl

lemma EM_special (n : ℕ) (hn : 2 ≤ n) :
    ∑ i ∈ Finset.Ico 1 (n + 1), log i / i =
    log n / (2 * n) + log n ^ 2 / 2 +
    ∫ x in (1)..n, (1 - log x) / x^2 * (x - ⌊x⌋ - 2⁻¹) := by
  have eq0 := EM n hn (f := fun x => log x / x)
    (.div₀ (continuousOn_log.mono (by simp)) (by fun_prop) (by
      simp only [Set.mem_Icc, ne_eq, and_imp]
      intros
      linarith))
    (.div (differentiableOn_log.mono (by simp)) (by fun_prop) (by
      simp only [Set.mem_Ioo, ne_eq, and_imp]
      intros
      linarith))
    (ContinuousOn.congr (h' := deriv_log_div n) <| .div₀ (.sub (by fun_prop)
      (continuousOn_log.mono (by simp))) (by fun_prop) (by
      simp only [Set.mem_Icc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
        and_imp]
      intros
      linarith))
  simp only [log_one, zero_div, zero_add] at eq0
  rw [integral_log_div n hn] at eq0

  rw [eq0]
  congr 1
  · congr 1; field_simp; left; ring
  · refine intervalIntegral.integral_congr ?_
    intro x hx
    simp only [Int.self_sub_floor, mul_eq_mul_right_iff]
    rw [Set.uIcc_of_le (by norm_cast; linarith)] at hx
    left
    rwa [deriv_log_div n]

def E (N : ℕ) : ℝ := (∑ k ∈ Finset.Ico 1 (N + 1), log k / k) - (log N) ^ 2 / 2

lemma E_eq (n : ℕ) (hn : 2 ≤ n) :
    E n = log n / (2 * n) + I n := by
  delta E I
  rw [EM_special n hn, show ∀ a b c : ℝ, (a + b + c) - b = a + c by intros; ring]

lemma E_eq' (n : ℕ) :
    E (n + 2) = log (n + 2) / (2 * (n + 2)) + I (n + 2) := by
  have hn : 2 ≤ n + 2 := by omega
  rw [E_eq (n + 2) hn]
  simp

lemma E_converges : Tendsto E atTop (𝓝 I∞) := by
  rw [show nhds I∞ = nhds ((1 / 2) * 0 + I∞) by simp, ← tendsto_add_atTop_iff_nat 2]
  simp_rw [E_eq']
  refine .add ?_ (by rw [tendsto_add_atTop_iff_nat 2]; exact I_converges)
  simp_rw [show (fun n : ℕ => log (n + 2) / (2 * (n + 2))) =
    fun n : ℕ => (1 / 2) * (log (n + 2 : ℕ) / (n + 2 : ℕ)) by ext n; field_simp]
  refine .mul tendsto_const_nhds ?_
  rw [tendsto_add_atTop_iff_nat (f := fun n : ℕ => log n / n) 2]
  have lim0 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by simp)
  simp only [pow_one, one_mul, add_zero] at lim0
  have lim1 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  exact lim0.comp lim1
