import Mathlib

def PreZHat : Type := Π (n : ℕ), ZMod n
example : Type := ∀ (n : ℕ), ZMod n
example : Type := (n : ℕ) → ZMod n

def FunctionType1 (α β : Type) : Type := α → β
def FunctionType2 (α β : Type) : Type := Π (a : α), β

example : FunctionType1 = FunctionType2 := rfl

example : (fun x : ZMod 4 ↦ (2 * x + 1) ^ 2) = (fun x : ZMod 4 ↦ 1) := by
  ext x
  ring_nf
  simp [show (4 : ZMod 4) = 0 by rfl]

example (X Y Z : Type) (f : X → Y) (g : Y → Z) (H : Function.Injective <| g ∘ f) :
    Function.Injective f := by
  intros x x' h
  apply_fun g at h
  exact H h
