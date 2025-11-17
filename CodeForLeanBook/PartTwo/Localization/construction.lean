import Mathlib

suppress_compilation

namespace loc

variable {R : Type} [CommRing R] (S T : Submonoid R)
variable (M : Type) [AddCommGroup M] [Module R M]

#check Localization S

#synth CommRing (Localization S)

#check LocalizedModule S M

#synth Module R (LocalizedModule S M)

#synth Module (Localization S) (LocalizedModule S M)


example (r r' : R) (s s' : S) :
    Localization.mk r s + Localization.mk r' s' =
    Localization.mk (s * r' + s' * r) (s * s') := by
  rw [Localization.add_mk]

example (r r' : R) (s s' : S) :
    Localization.mk r s * Localization.mk r' s' =
    Localization.mk (r * r') (s * s') := by
  rw [Localization.mk_mul]

example (m m' : M) (s s' : S) :
    LocalizedModule.mk m s + LocalizedModule.mk m' s' =
    LocalizedModule.mk (s' • m + s • m') (s * s') := by
  rw [LocalizedModule.mk_add_mk]

example (r : R) (m : M) (s : S) :
    r • LocalizedModule.mk m s =
    LocalizedModule.mk (r • m) s := by
  rw [LocalizedModule.smul'_mk]

example (r : R) (m : M) (s s' : S) :
    Localization.mk r s • LocalizedModule.mk m s' =
    LocalizedModule.mk (r • m) (s * s') := by
  rw [LocalizedModule.mk_smul_mk]

#check Localization.induction_on

#check LocalizedModule.induction_on

#check algebraMap R (Localization S)


#check IsLocalization.lift

def ex01 : Localization (nonZeroDivisors ℤ) →+* ℚ :=
IsLocalization.lift (M := nonZeroDivisors ℤ) (g := algebraMap ℤ ℚ) (by
  rintro ⟨z, hz⟩
  simpa using hz)

example : Function.Injective ex01 := by
  rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
  intro x hx
  induction x using Localization.induction_on with | H x =>
  rcases x with ⟨x, ⟨y, hy⟩⟩
  simp only [mem_nonZeroDivisors_iff_ne_zero, ne_eq, FractionRing.mk_eq_div, eq_intCast,
    RingHom.mem_ker, map_div₀, map_intCast, div_eq_zero_iff, Rat.intCast_eq_zero, Ideal.mem_bot,
    Int.cast_eq_zero] at hy hx ⊢
  exact hx

example : Function.Surjective ex01 := by
  rintro ⟨m, n, hn, hmn⟩
  refine ⟨Localization.mk m ⟨n, ?_⟩, ?_⟩
  · simpa using hn
  · simp only [FractionRing.mk_eq_div, eq_intCast, map_natCast, map_div₀, map_intCast]
    apply Rat.ext
    · erw [Rat.num_div_eq_of_coprime]
      · omega
      · simpa
    · zify
      erw [Rat.den_div_eq_of_coprime]
      · omega
      · simpa

#check isLocalization_iff

-- instance : IsLocalization (nonZeroDivisors ℤ) ℚ := sorry

#check isLocalizedModule_iff

#check IsLocalizedModule.lift

open TensorProduct

instance : IsLocalizedModule S (Algebra.ofId R (Localization S)).toLinearMap where
  map_units s := by
    rw [isUnit_iff_exists]
    let φ : Localization S →ₗ[R] Localization S :=
    { toFun x := x.liftOn (fun r t => Localization.mk r (s * t)) (by
        intro r r' t t'
        simp only [Localization.r_iff_exists, Subtype.exists, exists_prop,
          Localization.mk_eq_mk_iff, Submonoid.coe_mul, forall_exists_index, and_imp]
        intro s' hs' H
        refine ⟨s', hs', ?_⟩
        rw [← mul_assoc, ← mul_assoc, mul_comm s' s, mul_assoc, mul_assoc, H]
        ring)
      map_add' := by
        intros x y
        induction x using Localization.induction_on with | H x =>
        induction y using Localization.induction_on with | H y =>
        rcases x with ⟨x, ⟨tx, hs⟩⟩
        rcases y with ⟨y, ⟨ty, ht⟩⟩
        simp only [Localization.add_mk, Submonoid.mk_mul_mk, Localization.liftOn_mk,
          Submonoid.coe_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists, Subtype.exists,
          exists_prop]
        exact ⟨1, by simp, by ring⟩
      map_smul' := by
        intros r x
        induction x using Localization.induction_on with | H x =>
        rcases x with ⟨x, ⟨s, hs⟩⟩
        simp [Localization.smul_mk, Localization.liftOn_mk] }
    refine ⟨φ, ?_, ?_⟩
    all_goals
    · ext x
      induction x using Localization.induction_on with | H x =>
      rcases x with ⟨x, ⟨t, ht⟩⟩
      simp only [Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, Localization.liftOn_mk,
        Module.algebraMap_end_apply, Localization.smul_mk, smul_eq_mul, Module.End.one_apply,
        Localization.mk_eq_mk_iff, Localization.r_iff_exists, Submonoid.coe_mul, Subtype.exists,
        exists_prop, φ]
      exact ⟨1, by simp, by ring⟩
  surj' := by
    intro x
    induction x using Localization.induction_on with | H x =>
    rcases x with ⟨x, ⟨t, ht⟩⟩
    refine ⟨(x, ⟨t, ht⟩), ?_⟩
    simp [Localization.smul_mk, ← Localization.mk_one_eq_algebraMap, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists]
  exists_of_eq := by
    rintro r r' eq
    simp only [AlgHom.toLinearMap_apply, Algebra.ofId_apply, ← Localization.mk_one_eq_algebraMap,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists, OneMemClass.coe_one, one_mul,
      Subtype.exists, exists_prop] at eq
    obtain ⟨c, hc, eq⟩ := eq
    exact ⟨⟨c, hc⟩, eq⟩

def divByAux (s : S) : R →ₗ[R] Localization S :=
{ toFun r := Localization.mk r s
  map_add' := by intro r r'; simp [Localization.add_mk_self]
  map_smul' := by intro r x; simp [Localization.smul_mk] }

def divBy (s : S) : Localization S →ₗ[R] Localization S :=
IsLocalizedModule.lift S
  ((Algebra.ofId R (Localization S)).toLinearMap)
  (divByAux (s := s))
  (by
    intro t
    rw [isUnit_iff_exists]
    refine ⟨⟨⟨(· * Localization.mk 1 t), by simp [add_mul]⟩, by simp⟩, ?_, ?_⟩
    all_goals
    · ext x
      induction x using Localization.induction_on with | H x =>
      rcases x with ⟨x, ⟨tx, htx⟩⟩
      simp only [Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, Localization.mk_mul,
        mul_one, Module.algebraMap_end_apply, Localization.smul_mk, smul_eq_mul,
        Module.End.one_apply, Localization.mk_eq_mk_iff, Localization.r_iff_exists,
        Submonoid.coe_mul, Subtype.exists, exists_prop]
      exact ⟨1, by simp, by ring⟩)

@[simp]
lemma divBy_apply (r : R) (s t : S) :
    divBy S s (Localization.mk r t) = Localization.mk r (s * t) := by
  delta divBy
  generalize_proofs _ _ _ _ _ h
  have ht := h t
  rw [Module.End.isUnit_iff] at ht
  apply_fun _ using ht.injective
  simp only [Module.algebraMap_end_apply]
  rw [← map_smul, Localization.smul_mk, Localization.smul_mk]
  simp only [smul_eq_mul,
    show Localization.mk (t * r) t = Localization.mk r 1 by
      simp [Localization.mk_eq_mk_iff, Localization.r_iff_exists],
    show Localization.mk (t * r) (s * t) = Localization.mk r s by
      simpa [Localization.mk_eq_mk_iff, Localization.r_iff_exists] using ⟨1, by simp, by ring⟩]
  exact IsLocalizedModule.lift_apply S
    ((Algebra.ofId R (Localization S)).toLinearMap) (divByAux (s := s)) h r


def ex02 : LocalizedModule S M →ₗ[R] Localization S ⊗[R] M :=
IsLocalizedModule.lift S (LocalizedModule.mkLinearMap S M)
  { toFun m := 1 ⊗ₜ m
    map_add' := by simp [tmul_add]
    map_smul' := by simp }
  (by
    intro s
    rw [isUnit_iff_exists]
    refine ⟨TensorProduct.map (divBy (s := s)) LinearMap.id, ?_, ?_⟩
    all_goals
    · ext x m
      induction x using Localization.induction_on with | H x =>
      rcases x with ⟨x, ⟨tx, htx⟩⟩
      simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
        Module.End.mul_apply, map_tmul, divBy_apply, LinearMap.id_coe, id_eq,
        Module.algebraMap_end_apply, smul_tmul', Localization.smul_mk, smul_eq_mul,
        Module.End.one_apply]
      congr 1
      simpa [Localization.mk_eq_mk_iff, Localization.r_iff_exists] using ⟨1, by simp, by ring⟩)

def ex03 : (Localization S ⊗[R] M) →ₗ[R] LocalizedModule S M :=
  TensorProduct.lift <| IsLocalizedModule.lift S ((Algebra.ofId R (Localization S)).toLinearMap)
    { toFun r := r • LocalizedModule.mkLinearMap S M
      map_add' := by simp [add_smul]
      map_smul' := by simp [mul_smul] } <| by
    rintro ⟨s, hs⟩
    rw [isUnit_iff_exists]
    refine ⟨⟨⟨fun f => LocalizedModule.divBy ⟨s, hs⟩ ∘ₗ f, by simp [LinearMap.comp_add]⟩,
      by simp [LinearMap.comp_smul]⟩, ?_, ?_⟩
    all_goals
    · ext φ m
      simp only [Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, Module.algebraMap_end_apply,
        LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply, LocalizedModule.divBy_apply,
        Module.End.one_apply]
      set x := φ m
      clear_value x
      induction x using LocalizedModule.induction_on with | h m x =>
      simpa [LocalizedModule.liftOn_mk, LocalizedModule.smul'_mk, LocalizedModule.mk_eq] using
        ⟨1, by simp, by simp [mul_smul]⟩


def ex04 : LocalizedModule S M ≃ₗ[R] Localization S ⊗[R] M :=
  LinearEquiv.ofLinear (ex02 ..) (ex03 ..)
    sorry sorry

def ex05 : Localization (S ⊔ T) →+* Localization (S.map (algebraMap R (Localization T))) :=
  IsLocalization.lift (M := S ⊔ T) (g := algebraMap R _) <| by
    rintro ⟨x, hx⟩
    rw [← SetLike.mem_coe, Submonoid.coe_sup] at hx
    rcases hx with ⟨s, hs, t, ht, rfl⟩
    simp only [map_mul, IsUnit.mul_iff] at hx ⊢
    constructor
    · rw [isUnit_iff_exists]
      refine ⟨Localization.mk 1 ⟨algebraMap _ _ s, by simpa using ⟨s, hs, rfl⟩⟩, ?_, ?_⟩
      · simp only [← Localization.mk_one_eq_algebraMap, ← Algebra.smul_def, Localization.smul_mk]
        rw [← Algebra.algebraMap_eq_smul_one, ← Localization.mk_one]
        simp [Localization.mk_one_eq_algebraMap]
      · rw [mul_comm]
        simp only [← Localization.mk_one_eq_algebraMap, ← Algebra.smul_def, Localization.smul_mk]
        rw [← Algebra.algebraMap_eq_smul_one, ← Localization.mk_one]
        simp [Localization.mk_one_eq_algebraMap]
    · rw [isUnit_iff_exists]
      refine ⟨Localization.mk (Localization.mk 1 ⟨t, ht⟩) ⟨1, by simp⟩, ?_, ?_⟩
      · simp [← Algebra.smul_def, Localization.smul_mk]
      · rw [mul_comm]
        simp [← Algebra.smul_def, Localization.smul_mk]

def ex06 : Localization (S.map (algebraMap R (Localization T))) →+* Localization (S ⊔ T) :=
  IsLocalization.lift (M := S.map (algebraMap R (Localization T)))
    (g := IsLocalization.map (M := T) (T := S ⊔ T) _ (RingHom.id _)
      (by erw [Submonoid.comap_id]; exact le_sup_of_le_right fun ⦃x⦄ a ↦ a)) <| by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    simp only [IsLocalization.map_eq, RingHom.id_apply]
    rw [isUnit_iff_exists]
    refine ⟨Localization.mk 1 ⟨x, Submonoid.mem_sup_left hx⟩, ?_, ?_⟩
    · simp [← Algebra.smul_def, Localization.smul_mk]
    · rw [mul_comm]; simp [← Algebra.smul_def, Localization.smul_mk]


def ex07 : Localization (S ⊔ T) ≃+* Localization (S.map (algebraMap R (Localization T))) :=
  RingEquiv.ofHomInv (ex05 ..) (ex06 ..) sorry sorry


end loc
