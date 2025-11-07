import Mathlib

/-
category R-mod

category Matrix(R)-mod

-/

variable (R : Type) [Ring R]
variable (Q : Type) [AddCommGroup Q] [Module R Q]

variable (n : ℕ)

-- Q^n Fin n -> Q
instance : SMul (Matrix (Fin n) (Fin n) R) (Fin n → Q) where
  smul M v i := ∑ j, M i j • v j

@[simp]
lemma smul_apply (M : Matrix (Fin n) (Fin n) R) (v : Fin n → Q) (i : Fin n) :
    (M • v) i = ∑ j, M i j • v j := rfl

#check Module

instance : MulAction (Matrix (Fin n) (Fin n) R) (Fin n → Q) where
  one_smul v := by
    ext i
    simp [Matrix.one_apply]
  mul_smul := by
    intro M N v
    ext i
    simp only [smul_apply, Matrix.mul_apply, Finset.sum_smul, mul_smul, Finset.smul_sum]
    rw [Finset.sum_comm]

instance : DistribMulAction (Matrix (Fin n) (Fin n) R) (Fin n → Q) where
  smul_zero := by
    intro M
    ext
    simp
  smul_add := by
    intro M v w
    ext i
    simp [smul_add, Finset.sum_add_distrib]

instance : Module (Matrix (Fin n) (Fin n) R) (Fin n → Q) where
  add_smul := by
    intro M N v
    ext i
    simp [add_smul, Finset.sum_add_distrib]
  zero_smul := by
    intro v
    ext i
    simp

-- Q →ₗ[R] Q'
-- Q^n →ₗ[Matrix (Fin n) (Fin n) R] Qⁿ


-- instance : Module (Matrix (Fin n) (Fin n) R) (Fin n → Q) where
--   smul M v i := ∑ j, M i j • v j
--   one_smul v := by
--     ext i
--     change ∑ _, _ = _
--     simp [Matrix.one_apply]
--   mul_smul M N v := by
--     ext i
--     change ∑ _, _ = ∑ _, _ • (∑ _, _)
--     simp only [Matrix.mul_apply, Finset.sum_smul, mul_smul, Finset.smul_sum]
--     rw [Finset.sum_comm]
--   smul_zero M := by
--     ext i
--     change ∑ _, _ = 0
--     simp
--   smul_add M v w := by
--     ext i
--     change ∑ _, _ =  (∑ j, M i j • v j) + (∑ _, _)
--     simp [smul_add, Finset.sum_add_distrib]
--   add_smul M N v := by
--     ext i
--     change ∑ _, _ = (∑ j, M i j • v j) + (∑ _, _)
--     simp [add_smul, Finset.sum_add_distrib]
--   zero_smul v := by
--     ext i
--     change ∑ _, _ = 0
--     simp

-- variable (Q' : Type) [AddCommGroup Q'] [Module R Q']
-- variable (f : Q →ₗ[R] Q')

-- example : (Fin n → Q) →ₗ[Matrix (Fin n) (Fin n) R] (Fin n → Q') :=
-- { toFun := fun v i => f (v i)
--   map_add' := by intro v w; ext i; simp
--   map_smul' := by
--     intro M v
--     ext i
--     change f (∑ j, M i j • v j) = ∑ j, _
--     simp }

variable (P : Type) [AddCommGroup P] [Module (Matrix (Fin n) (Fin n) R) P] [NeZero n]

-- -- P as R-module r • p => [r, 000; 0, r, 000; 0 0 r 00]

-- def asMod (P : Type) [AddCommGroup P] [Module (Matrix (Fin n) (Fin n) R) P] [NeZero n] := P

-- instance : AddCommGroup (asMod R n P) :=
--   inferInstanceAs (AddCommGroup P)

-- instance : Module (Matrix (Fin n) (Fin n) R) (asMod R n P) :=
--     inferInstanceAs (Module (Matrix (Fin n) (Fin n) R) P)


-- instance : Module R (asMod R n P) where
--   smul r p := Matrix.diagonal (fun i : Fin n => r) • p
--   one_smul := _
--   mul_smul := _
--   smul_zero := _
--   smul_add := _
--   add_smul := _
--   zero_smul := _


abbrev mod : Set P  :=
  Set.range (fun p : P => Matrix.single (0 : Fin n) (0 : Fin n) (1 : R) • p)

instance : AddCommGroup (mod R n P) := sorry

instance : Module R (mod R n P) := sorry

-- P →ₗ[Matrix n n R] P'
-- mod P ->ₗ[R] mod P'

#check DecidableRel
-- ℚ

set_option maxHeartbeats 0 in
example : 2 ^ 100 = 1267650600228229401496703205376 := by


-- open Classical in
example : Nat.sqrt 4 = 2 := by
  -- letI : DecidableEq ℕ := Classical.decEq ℕ
  decide
