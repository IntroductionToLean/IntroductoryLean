import Mathlib

section module_over_ring

variable (R S : Type) [Ring R] [Ring S]

#synth Module R R

-- 左模
variable (M : Type) [AddCommGroup M] [Module R M]
variable (N : Type) [AddCommGroup N] [Module R N]
variable {ι : Type} (P : ι → Type) [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]

#synth Module R (M × N)
#synth Module R (Π i, P i)

open DirectSum
#synth Module R (⨁ i : ι, P i)

-- 右模
variable (Q : Type) [AddCommGroup Q] [Module Rᵐᵒᵖ Q]

-- bimodule
variable (B : Type) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B] [SMulCommClass R Sᵐᵒᵖ B]

open MulOpposite
example (r : R) (s : S) (b : B) :
    r • (op s) • b = op s • r • b := by rw [smul_comm]

end module_over_ring

section module_over_commring

variable (R : Type) [CommRing R]

variable (M : Type) [AddCommGroup M] [Module R M]
variable (N : Type) [AddCommGroup N] [Module R N]
variable {ι : Type} (P : ι → Type) [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]


#synth Module R (M →ₗ[R] N)

open TensorProduct
#synth Module R (M ⊗[R] N)
#synth Module R (⨂[R] i : ι, P i)

end module_over_commring


section vector_space_over_field

variable (F : Type) [Field F]
variable (V : Type) [AddCommGroup V] [Module F V]
variable [FiniteDimensional F V]

#check Module.finrank F V

end vector_space_over_field

section matrix

variable (R : Type) [Ring R]
variable {𝔪 𝔫 : Type}

#check Matrix 𝔪 𝔫 R


example : Matrix (Fin 3) (Fin 4) ℤ :=
!![1, 2, 3, 4;
   5, 6, 7, 8;
   9, 10, 11, 12]

end matrix
