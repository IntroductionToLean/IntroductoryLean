import Mathlib


#check NumberField

variable (K : Type*) [Field K] [NumberField K]

#check NumberField.RingOfIntegers

open NumberField

open NumberField
#check 𝓞 K


example : ℤ = 𝓞 ℚ := by sorry

noncomputable example : ℤ ≃ₐ[ℤ] 𝓞 ℚ := IsIntegralClosure.equiv ℤ ℤ ℚ _


#synth IsFractionRing (𝓞 K) K

#synth IsIntegralClosure (𝓞 K) ℤ K


namespace example1

open IntermediateField Complex

#check IntermediateField.adjoin
#check ℚ⟮I⟯

open Polynomial
abbrev i1 : 𝓞 ℚ⟮I⟯ :=
  ⟨⟨I, mem_adjoin_simple_self ℚ I⟩, ⟨X^2 + C 1, monic_X_pow_add_C _ (by norm_num), by simpa using by ext; simp⟩⟩

instance : Fact (Irreducible (X ^ 2 + 1 : ℚ[X])) where
  out := irreducible_of_degree_le_three_of_not_isRoot
    (by erw [natDegree_X_pow_add_C (n := 2) (r := (1 : ℚ))]; simp)  <| by
    intro r
    simp only [IsRoot.def, eval_add, eval_pow, eval_X, eval_one]
    intro rid
    have eq0 : r ^ 2 = -1 := by grind
    have eq1 : 0 ≤ r ^ 2 := by exact sq_nonneg r
    grind

noncomputable example : 𝓞 (AdjoinRoot (X ^ 2 + 1 : ℚ[X])) :=
  ⟨AdjoinRoot.root _, ⟨X^2 + 1, monic_X_pow_add_C _ (by norm_num), by
    have := AdjoinRoot.isRoot_root (X ^ 2 + 1 : ℚ[X])
    simpa using this⟩⟩

noncomputable def B : Module.Basis (Fin 2) ℚ ℚ⟮I⟯ :=
  .mk (v := ![1, ⟨I, mem_adjoin_simple_self ℚ I⟩])
    (by
      rw [linearIndependent_fin2]
      simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, ne_eq, Subtype.ext_iff,
        ZeroMemClass.coe_zero, I_ne_zero, not_false_eq_true, SetLike.mk_smul_mk,
        Matrix.cons_val_zero, OneMemClass.coe_one, true_and]
      rintro a eq
      simp only [Algebra.smul_def, eq_ratCast] at eq
      by_cases ha : a = 0
      · subst ha; simp at eq
      have eq' : I = a⁻¹ := by
        have ha' : (a : ℂ) ≠ 0 := by simpa using ha
        field_simp
        grind
      have eq'' : I.im = 0 := by
        rw [eq']
        norm_cast
      simp at eq'')
    (by
      rintro ⟨x, (hx : x ∈ IntermediateField.toSubalgebra _)⟩ -
      rw [IntermediateField.adjoin_simple_toSubalgebra_of_integral (isIntegral_rat_I)] at hx
      have hx' : x ∈ Subalgebra.toSubmodule (Algebra.adjoin ℚ {I}) := hx
      rw [Algebra.adjoin_eq_span ℚ {I}] at hx'
      rw [show (Submonoid.closure {I} : Set ℂ) = {1, I, -I, -1} by
        ext x
        simp only [SetLike.mem_coe, Submonoid.mem_closure_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        constructor
        · rintro ⟨n, rfl⟩
          rw [Complex.I_pow_eq_pow_mod n]
          obtain (h|h|h|h) : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
            grind
          any_goals rw [h]; simp
        · rintro (rfl|rfl|rfl|rfl)
          · use 4; simp
          · use 1; simp
          · use 3; simp
          · use 2; simp] at hx'
      rw [show Submodule.span ℚ {1, I, -I, -1} = Submodule.span ℚ {1, I} by
        refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (by grind))
        rintro x (rfl|rfl|rfl|rfl)
        any_goals simpa using Submodule.subset_span (by simp)] at hx'
      simp only [Submodule.mem_span_pair, Rat.smul_one_eq_cast, Matrix.range_cons,
        Matrix.range_empty, Set.union_empty, Set.union_singleton, SetLike.mk_smul_mk] at hx' ⊢
      obtain ⟨a, b, ha, hb, rfl⟩ := hx'
      use b, a
      ext
      simpa using by ring)


instance : NumberField ℚ⟮I⟯ where
  to_charZero := charZero ℚ⟮I⟯
  to_finiteDimensional := FiniteDimensional.of_fintype_basis B


@[simp]
lemma B0 : B 0 = 1 := by simp [B]

@[simp]
lemma B1 : B 1 = ⟨I, mem_adjoin_simple_self ℚ I⟩ := by simp [B]

@[simp]
lemma B_repr_I :
    B.repr ⟨I, mem_adjoin_simple_self ℚ I⟩ =
    fun₀ | 0 => 0 | 1 => 1 := by
  apply_fun B.repr.symm using LinearEquiv.injective B.repr.symm
  simp

@[simp]
lemma B_repr_1 : B.repr (1 : ℚ⟮I⟯) = fun₀ | 1 => 0 | 0 => 1 := by
  apply_fun B.repr.symm using LinearEquiv.injective B.repr.symm
  simp

@[simp]
lemma B_leftMulMatrix :
    Algebra.leftMulMatrix B ⟨I, mem_adjoin_simple_self ℚ I⟩ =
    !![0, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j
  any_goals simp [Algebra.leftMulMatrix_eq_repr_mul, show (⟨-1, _⟩ : ℚ⟮I⟯) = -1 by rfl]

@[simp]
lemma norm_eq1 : Algebra.norm ℚ (⟨I, mem_adjoin_simple_self ℚ I⟩ : ℚ⟮I⟯) = 1 := by
  rw [Algebra.norm_eq_matrix_det B, Matrix.det_fin_two]
  simp

example : Algebra.trace ℚ _ (⟨I, mem_adjoin_simple_self ℚ I⟩ : ℚ⟮I⟯) = 0 := by
  rw [Algebra.trace_eq_matrix_trace B]
  simp

#check RingOfIntegers.norm
example : RingOfIntegers.norm ℚ i1 = 1 := by
  ext
  simp [i1]

#check AdjoinRoot.powerBasis
@[simp]
lemma norm_eq2 : Algebra.norm ℚ (AdjoinRoot.root (X ^ 2 + 1 : ℚ[X])) = 1 := by
  let B := AdjoinRoot.powerBasis (f := (X ^ 2 + 1 : ℚ[X])) (X_pow_add_C_ne_zero (by norm_num) _)

  have dim_eq : B.dim = 2 := by simp [B]; exact natDegree_X_pow_add_C
  have gen_eq : B.gen = AdjoinRoot.root (X ^ 2 + 1 : ℚ[X]) := by simp [B]
  rcases B with ⟨gen, dim, B, hB⟩
  simp only at *
  subst gen_eq
  subst dim
  rw [Algebra.norm_eq_matrix_det B, Matrix.det_fin_two]
  have eq0 : AdjoinRoot.root (X ^ 2 + 1 : ℚ[X]) ^ 2 = -1 := by
    have := AdjoinRoot.isRoot_root (X ^ 2 + 1 : ℚ[X])
    simp only [Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_one, IsRoot.def,
      eval_add, eval_pow, eval_X, eval_one] at this
    grind
  simp_rw [pow_two] at eq0
  have B_repr_1 : B.repr 1 = fun₀ | 1 => 0 | 0 => 1 := by
    apply_fun B.repr.symm using LinearEquiv.injective B.repr.symm
    simp [hB]
  have B_repr_gen : B.repr (AdjoinRoot.root (X ^ 2 + 1 : ℚ[X])) =
      fun₀ | 0 => 0 | 1 => 1 := by
    apply_fun B.repr.symm using LinearEquiv.injective B.repr.symm
    simp [hB]
  simp [eq0, Algebra.leftMulMatrix_eq_repr_mul B, hB, B_repr_1, B_repr_gen]

noncomputable def i2 : 𝓞 (AdjoinRoot (X ^ 2 + 1 : ℚ[X])) :=
  ⟨AdjoinRoot.root _, ⟨X^2 + 1, monic_X_pow_add_C _ (by norm_num), by
    have := AdjoinRoot.isRoot_root (X ^ 2 + 1 : ℚ[X])
    simpa using this⟩⟩

example : RingOfIntegers.norm ℚ i2 = 1 := by
  ext
  simp [i2]

end example1
