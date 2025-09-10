inductive F2 : Type
| zero : F2
| one : F2

#check F2.rec

/-
Lean 中自然数已经被定义了
inductive Nat : Type
| zero : Nat
| succ (n : Nat): Nat
-/

#check Nat.rec


def Nat.factorial : Nat → Nat :=
Nat.rec 1 (fun n factorial_n ↦ (n + 1) * factorial_n)

#eval Nat.factorial 10

def Nat.factorial'
| 0 => 1
| succ n => (n + 1) * (factorial' n)

#eval Nat.factorial' 10

inductive Integer : Type
| nonneg : Nat → Integer
| neg : Nat → Integer


-- def Or.swap (P Q : Prop) : Or P Q → Or Q P := Or.rec _ _

#check Exists

inductive Exists' {α : Type} (p : α → Prop) : Prop
| intro (w : α) (h : p w) : Exists' p
