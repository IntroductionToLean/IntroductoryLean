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

abbrev PointedSet.InternalHom (S T : PointedSet) : PointedSet where
  t := PointedFunc S T
  base := ⟨fun _ => T.base, rfl⟩

instance (S T : PointedSet) : FunLike (PointedFunc S T) S T where
  coe f := f.toFun
  coe_injective' := by
    rintro ⟨f, _⟩ ⟨g, _⟩ rfl
    rfl

@[simp]
lemma PointedFunc.preserves {S T : PointedSet} (f : PointedFunc S T) :
  f S.base = T.base := f.preserves'

def PointedSet.product (S T : PointedSet) : PointedSet where
  t := S × T
  base := (S.base, T.base)

@[simp]
def baseInProduct {S T : PointedSet} (x : S.product T) : Prop :=
  x.1 = S.base ∨ x.2 = T.base

@[simp]
def smashedRel (S T : PointedSet) (x y : S × T) : Prop :=
  (baseInProduct x ∧ baseInProduct y) ∨ x = y

lemma smashedRel_equivalence (S T : PointedSet) :
    Equivalence (smashedRel S T) := by
  refine ⟨?_, ?_, ?_⟩
  · tauto
  · simp; tauto
  · rintro x y z (hxy|rfl) (hyz|rfl)
    · left; tauto
    · left; tauto
    · left; tauto
    · right; tauto

def smashedSetoid (S T : PointedSet) : Setoid (S.product T) where
  r := smashedRel S T
  iseqv := smashedRel_equivalence S T

@[simp]
lemma smashedSetoid_rel {S T : PointedSet} (x y : S.product T) :
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
          simp }
      preserves' := by
        rw [PointedFunc.ext_iff]
        ext
        simp only [PointedSet.Smash_t]
        convert f.preserves
        simp }
  invFun f :=
  { toFun := Quotient.rec (fun a => f a.1 a.2) <| by
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
