import Mathlib

namespace nt

@[ext]
structure Zsqrt (d : ℤ) where
  re : ℤ
  im : ℤ

/--
a + b√d  + a' + b'√d  = (a + a') + (b + b')√d
-/
instance (d : ℤ) : Add (Zsqrt d) where
  add x y := ⟨x.re + y.re, x.im + y.im⟩

@[simp]
lemma add_re (d : ℤ) (x y : Zsqrt d) : (x + y).re = x.re + y.re := rfl

@[simp]
lemma add_im (d : ℤ) (x y : Zsqrt d) : (x + y).im = x.im + y.im := rfl


instance (d : ℤ) : Zero (Zsqrt d) where
  zero := ⟨0, 0⟩

@[simp]
lemma zero_re (d : ℤ) : (0 : Zsqrt d).re = 0 := rfl

@[simp]
lemma zero_im (d : ℤ) : (0 : Zsqrt d).im = 0 := rfl

instance (d : ℤ) : Neg (Zsqrt d) where
  neg x := ⟨-x.re, -x.im⟩

@[simp]
lemma neg_re (d : ℤ) (x : Zsqrt d) : (-x).re = -x.re := rfl

@[simp]
lemma neg_im (d : ℤ) (x : Zsqrt d) : (-x).im = -x.im := rfl

/--
(a + b√d)(a' + b'√d) = (aa' + dbb') + (ab' + a'b)√d
-/
instance (d : ℤ) : Mul (Zsqrt d) where
  mul x y := ⟨x.re * y.re + d * x.im * y.im, x.re * y.im + x.im * y.re⟩

@[simp]
lemma mul_re (d : ℤ) (x y : Zsqrt d) :
    (x * y).re = x.re * y.re + d * x.im * y.im := rfl

@[simp]
lemma mul_im (d : ℤ) (x y : Zsqrt d) :
    (x * y).im = x.re * y.im + x.im * y.re := rfl

instance (d : ℤ) : One (Zsqrt d) where
  one := ⟨1, 0⟩

@[simp]
lemma one_re (d : ℤ) : (1 : Zsqrt d).re = 1 := rfl
@[simp]
lemma one_im (d : ℤ) : (1 : Zsqrt d).im = 0 := rfl

instance (d : ℤ) : AddCommGroup (Zsqrt d) where
  add_assoc := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    ext <;>
    simp [add_assoc]
  zero_add := by
    rintro ⟨a, b⟩
    ext <;>
    simp
  add_zero := by
    rintro ⟨a, b⟩
    ext <;>
    simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := by
    rintro ⟨a, b⟩
    ext <;>
    simp
  add_comm := by
    rintro ⟨a, b⟩ ⟨c, d⟩
    ext <;>
    simp [add_comm]

instance (d : ℤ) : CommRing (Zsqrt d) where
  left_distrib := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    ext <;>
    simpa using by ring
  right_distrib := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    ext <;>
    simpa using by ring
  zero_mul := by
    rintro ⟨a, b⟩
    ext <;>
    simp
  mul_zero := by
    rintro ⟨a, b⟩
    ext <;>
    simp
  mul_assoc := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    ext <;>
    simpa using by ring
  one := ⟨1, 0⟩
  one_mul := by
    rintro ⟨a, b⟩
    ext <;>
    simp
  mul_one := by
    rintro ⟨a, b⟩
    ext <;>
    simp
  mul_comm := by
    rintro ⟨a, b⟩ ⟨c, d⟩
    ext <;>
    simpa using by ring

instance (d : ℤ) : Nontrivial (Zsqrt d) where
  exists_pair_ne := ⟨0, 1, by
    intro r
    simp [Zsqrt.ext_iff] at r⟩


@[simp]
lemma intCast_re (d : ℤ) (n : ℤ) : (n : Zsqrt d).re = n := sorry
@[simp]
lemma intCast_im (d : ℤ) (n : ℤ) : (n : Zsqrt d).im = 0 := sorry

open Polynomial

abbrev toQuotPoly (d : ℤ) : ℤ[X] →+* Zsqrt d := Polynomial.aeval (⟨0, 1⟩ : Zsqrt d) |>.toRingHom

lemma ker_toQuotPoly (d : ℤ) :
    RingHom.ker (toQuotPoly d) = Ideal.span {X ^ 2 - Polynomial.C d} := by
  ext p
  simp only [AlgHom.toRingHom_eq_coe, RingHom.mem_ker, RingHom.coe_coe, eq_intCast]
  constructor
  · intro h
    have eq : p = p %ₘ (X ^ 2 - C d) + (X ^ 2 - C d) * (p /ₘ (X ^ 2 - C d))  := by
      rw [Polynomial.modByMonic_add_div]
      apply Polynomial.monic_X_pow_sub_C
      simp
    have := congr($(eq).aeval (⟨0, 1⟩ : Zsqrt d))
    simp only [h, eq_intCast, map_add, map_mul, aeval_sub, map_pow, aeval_X,
      show (⟨0, 1⟩ : Zsqrt d) ^ 2 = d by ext <;> simp [pow_two], map_intCast, sub_self, zero_mul,
      add_zero] at this
    -- p %ₘ (X ^ 2 - C d) can not have degree 1 so it must be zero
    sorry
  · intro h
    rw [Ideal.mem_span_singleton] at h
    obtain ⟨p, rfl⟩ := h
    sorry



end nt
