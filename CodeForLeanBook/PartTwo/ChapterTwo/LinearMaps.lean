import Mathlib

section over_commring

variable (R : Type) [CommRing R]
variable (ι : Type) [DecidableEq ι]
variable (A : ι → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
variable (B : Type) [AddCommGroup B] [Module R B]

open DirectSum

example : ((⨁ i, A i) →ₗ[R] B) ≃ₗ[R] (Π i : ι, A i →ₗ[R] B) :=
LinearEquiv.ofLinear
  { toFun f i := f ∘ₗ DirectSum.lof R ι A i
    map_add' := by intro f g; ext i a; rfl
    map_smul' := by intro r f; ext i a; rfl }
  { toFun f := DirectSum.toModule _ _ _ f
    map_add' f g := by ext; simp
    map_smul' r f := by ext; simp }
  (by ext f i a; simp)
  (by ext f i a; simp)

end over_commring

noncomputable section basis

variable {F : Type} [Field F]
variable {V : Type} [AddCommGroup V] [Module F V]
variable {n : ℕ} (B : Module.Basis (Fin n) F V)

def endToMatrix : Module.End F V → Matrix (Fin n) (Fin n) F :=
  fun f => Matrix.of fun i j => B.equivFun (f (B j)) i

lemma endToMatrix_spec (f : Module.End F V) :
    B.equivFun ∘ₗ f = (endToMatrix B f).mulVecLin ∘ₗ B.equivFun := by
  apply B.ext
  intro j
  ext i
  simp [Matrix.mulVec, dotProduct, Finsupp.single_apply]
  rfl

lemma endToMatrix_spec' (f : Module.End F V) :
    B.equivFun ∘ₗ f ∘ₗ B.equivFun.symm = (endToMatrix B f).mulVecLin := by
  rw [← LinearMap.comp_assoc, endToMatrix_spec, LinearMap.comp_assoc, LinearEquiv.comp_symm,
   LinearMap.comp_id]

lemma endToMatrix_spec'' (f : Module.End F V) :
    f = B.equivFun.symm ∘ₗ (endToMatrix B f).mulVecLin ∘ₗ B.equivFun := by
  rw [← endToMatrix_spec, LinearEquiv.symm_comp_cancel_left]

lemma endToMatrix_mul (f g : Module.End F V) :
    endToMatrix B (f * g) = endToMatrix B f * endToMatrix B g := by
  have eq₁ := calc (endToMatrix B (f * g)).mulVecLin
    _ = B.equivFun ∘ₗ (f * g) ∘ₗ B.equivFun.symm := endToMatrix_spec' B (f * g) |>.symm
    _ = B.equivFun ∘ₗ (f ∘ₗ (B.equivFun.symm ∘ₗ B.equivFun.toLinearMap) ∘ₗ g) ∘ₗ B.equivFun.symm := by
      rw [B.equivFun.symm_comp, LinearMap.id_comp]; rfl
    _ = (B.equivFun ∘ₗ f ∘ₗ B.equivFun.symm) ∘ₗ (B.equivFun.toLinearMap ∘ₗ g ∘ₗ B.equivFun.symm) := by
      simp [LinearMap.comp_assoc, LinearEquiv.symm_comp_cancel_left]
    _ = (endToMatrix B f).mulVecLin ∘ₗ (endToMatrix B g).mulVecLin := by
      rw [endToMatrix_spec' B f, endToMatrix_spec' B g]
  apply Matrix.ext_of_mulVec_single
  intro i
  have eq₂ := congr($eq₁ (Pi.single i 1))
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_single, MulOpposite.op_one, one_smul,
    LinearMap.coe_comp, Function.comp_apply] at eq₂ ⊢
  rw [eq₂]
  ext j
  simp [Matrix.mul_apply, Matrix.mulVec, Matrix.col, dotProduct]

def matrixToEnd (M : Matrix (Fin n) (Fin n) F) : Module.End F V :=
  B.equivFun.symm ∘ₗ M.mulVecLin ∘ₗ B.equivFun

def endEquivMatrix :
    Module.End F V ≃* Matrix (Fin n) (Fin n) F where
  toFun := endToMatrix B
  invFun := matrixToEnd B
  left_inv := by
    intro f
    rw [matrixToEnd, ← endToMatrix_spec'']
  right_inv := by
    intro M
    have eq₁ := calc (endToMatrix B (matrixToEnd B M)).mulVecLin
      _ = B.equivFun ∘ₗ (matrixToEnd B M) ∘ₗ B.equivFun.symm :=
        endToMatrix_spec' B (matrixToEnd B M) |>.symm
      _ = B.equivFun ∘ₗ (B.equivFun.symm.toLinearMap ∘ₗ M.mulVecLin ∘ₗ B.equivFun) ∘ₗ B.equivFun.symm.toLinearMap := by rfl
      _ = (B.equivFun ∘ₗ B.equivFun.symm.toLinearMap) ∘ₗ M.mulVecLin ∘ₗ (B.equivFun ∘ₗ B.equivFun.symm.toLinearMap) := by
        simp [LinearMap.comp_assoc, B.equivFun.comp_symm_cancel_left]
      _ = M.mulVecLin := by
        simp [LinearMap.id_comp, LinearMap.comp_id]
    apply Matrix.ext_of_mulVec_single
    intro i
    have eq₂ := congr($eq₁ (Pi.single i 1))
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_single, MulOpposite.op_one, one_smul] at eq₂ ⊢
    rw [eq₂]
  map_mul' := endToMatrix_mul B
end basis
