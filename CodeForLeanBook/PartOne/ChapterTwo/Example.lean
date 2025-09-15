import Mathlib

open scoped Classical

structure PointedSet where
  t : Type
  base : t

instance : CoeSort PointedSet Type where
  coe T := T.t

@[ext]
structure PointedFunc (S T : PointedSet) where
  toFun : S → T
  preserves' : toFun S.base = T.base

instance (S T : PointedSet) : FunLike (PointedFunc S T) S T where
  coe f := f.toFun
  coe_injective' := by
    rintro ⟨f, _⟩ ⟨g, _⟩ rfl
    rfl

@[simp]
lemma PointedFunc.preserves {S T : PointedSet} (f : PointedFunc S T) :
  f S.base = T.base := f.preserves'

@[simps]
def S0 : PointedSet where
  t := Bool
  base := true

abbrev PointedSet.InternalHom (S T : PointedSet) : PointedSet where
  t := PointedFunc S T
  base := ⟨fun _ => T.base, rfl⟩

def PointedSet.Product (S T : PointedSet) : PointedSet where
  t := S × T
  base := (S.base, T.base)

@[simp]
def baseInProduct {S T : PointedSet} (x : S.Product T) : Prop :=
  x.1 = S.base ∨ x.2 = T.base

inductive smashedRel (S T : PointedSet) (x y : S × T) : Prop
| base (_ : baseInProduct x ∧ baseInProduct y )
| eq (_ : x = y)

lemma smashedRel_equivalence (S T : PointedSet) :
    Equivalence (smashedRel S T) where
  refl _ := .eq rfl
  symm
  | .base h => .base h.symm
  | .eq h => .eq h.symm
  trans
  | .base h, .base h' => .base <| by tauto
  | .base h, .eq h' => .base <| by aesop
  | .eq h, .base h' => .base <| by aesop
  | .eq h, .eq h' => .eq <| by aesop

def smashedSetoid (S T : PointedSet) : Setoid (S.Product T) where
  r := smashedRel S T
  iseqv := smashedRel_equivalence S T

@[simp]
lemma smashedSetoid_rel {S T : PointedSet} (x y : S.Product T) :
    smashedSetoid S T x y  ↔ smashedRel _ _ x y := by simp [smashedSetoid]

@[simps]
def PointedSet.Smash (S T : PointedSet) : PointedSet where
  t := Quotient (smashedSetoid S T)
  base := ⟦(S.base, T.base)⟧

example (A B C : PointedSet) :
    PointedFunc (A.Smash B) C ≃ PointedFunc A (B.InternalHom C) where
  toFun f :=
    { toFun a :=
      { toFun b := f ⟦(a, b)⟧
        preserves' := by
          convert f.preserves
          simp only [PointedSet.Smash_t, PointedSet.Smash_base, Quotient.eq, smashedSetoid_rel]
          exact .base (by simp) }
      preserves' := by
        rw [PointedFunc.ext_iff]
        ext
        simp only [PointedSet.Smash_t]
        convert f.preserves
        simp only [PointedSet.Smash_base, Quotient.eq, smashedSetoid_rel]
        exact .base (by simp) }
  invFun f :=
  { toFun a := a.recOn (fun a => f a.1 a.2) <| by
      rintro ⟨a, b⟩ ⟨a', b'⟩ (h|h)
      · aesop
      · aesop
    preserves' := by
      change f A.base B.base = C.base
      simp }
  left_inv := by
    rintro f
    ext x
    induction x using Quotient.inductionOn with | h x =>
    rfl
  right_inv _ := rfl

example (A : PointedSet) : A.Smash S0 ≃ A where
  toFun x := x.recOn (fun| (a, true) => A.base | (a, false) => a) <| by
      rintro ⟨a, ⟨⟩|⟨⟩⟩ ⟨a', ⟨⟩|⟨⟩⟩ (h|h) <;> aesop
  invFun := fun a ↦ ⟦(a, false)⟧
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with | h x =>
    rcases x with ⟨a, ⟨⟩|⟨⟩⟩
    · simp only [PointedSet.Smash_t, S0_t, Quotient.eq]
      exact .eq rfl
    · simp only [PointedSet.Smash_t, S0_t, Quotient.eq]
      refine .base ?_
      simp only [baseInProduct, S0_t, S0_base, Bool.false_eq_true, or_false, or_true, and_true]
      rfl
  right_inv _ := by rfl
