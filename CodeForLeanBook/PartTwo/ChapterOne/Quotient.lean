import Mathlib

suppress_compilation

variable {G : Type} [Group G] (H : Subgroup G) [H.Normal]

open Pointwise

structure QGroup : Type where
  carrier : Set G
  isCoset : ∃ g : G, carrier = g • H

namespace QGroup

variable {H}

instance : SetLike (QGroup H) G where
  coe C := C.carrier
  coe_injective' := by
    intro C D; cases C; cases D; simp

@[ext]
lemma ext {C D : QGroup H} (h : (C : Set G) = D) : C = D := by
  cases C; cases D; simp at h; simp [h]

def out (C : QGroup H) : G := Classical.choose C.isCoset

@[simp]
lemma out_spec (C : QGroup H) : C.out • H = (C : Set G) :=
  Classical.choose_spec C.isCoset |>.symm

lemma mem_iff_out (C : QGroup H) (g : G) : g ∈ C ↔ ∃ h ∈ H, g = C.out • h := by
  rw [← SetLike.mem_coe, ← C.out_spec, Set.mem_smul_set]
  tauto

variable (H) in
def gen (g : G) : QGroup H :=
  ⟨g • H, ⟨g, rfl⟩⟩


lemma gen_def (g : G) : (gen H g : Set G) = g • H := rfl

@[simp]
lemma mem_gen_iff (g : G) {x : G} : x ∈ gen H g ↔ ∃ h ∈ H, x = g * h := by
  rw [← SetLike.mem_coe, gen_def, Set.mem_smul_set]
  tauto

@[simp]
lemma gen_out (C : QGroup H) : gen H C.out = C := by
  ext g
  simp only [SetLike.mem_coe, mem_gen_iff]
  rw [C.mem_iff_out]
  rfl

@[simp]
lemma mem_out_gen (g : G) {x : G} : x ∈ ((gen H g).out • H : Set G) ↔ x ∈ (g • H : Set G) := by
  simp [Set.mem_smul_set, eq_comm]


@[elab_as_elim]
theorem gen_induction {P : QGroup H → Prop}
    (h : ∀ g : G, P (gen H g)) :
    ∀ C : QGroup H, P C := by
  intro C
  rw [← C.gen_out]
  tauto

@[simp]
theorem gen_eq_iff (g : G) (C : QGroup H) : gen H g = C ↔ g ∈ C := by
  constructor
  · rintro rfl
    simp
  · intro h
    rw [C.mem_iff_out] at h
    obtain ⟨x, hx, rfl⟩ := h
    ext y
    simp only [smul_eq_mul, SetLike.mem_coe, mem_gen_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [C.mem_iff_out]
      use x * y, mul_mem hx hy
      simp [mul_assoc]
    · rw [C.mem_iff_out]
      rintro ⟨y, hy, rfl⟩
      use x⁻¹ * y, mul_mem (H.inv_mem hx) hy
      simp [mul_assoc]

theorem gen_eq_gen_iff (g g' : G) : gen H g = gen H g' ↔ g⁻¹ * g' ∈ H := by
  fconstructor
  · intro h
    rw [gen_eq_iff] at h
    obtain ⟨x, hx, (rfl : g' * x = g)⟩ := h

    rw [show (g' * x)⁻¹ * g' = x⁻¹ by group]
    exact inv_mem hx
  · rintro h
    rw [gen_eq_iff]
    simp only [mem_gen_iff]
    refine ⟨_, inv_mem h, ?_⟩
    simp


theorem eq_or_disjoint (C D : QGroup H) : C = D ∨ (C.carrier ∩ D) = ∅ := by
  by_cases eq : C = D
  · tauto
  · right
    contrapose! eq
    induction C using gen_induction with | h c =>
    induction D using gen_induction with | h d =>
    obtain ⟨x, ⟨z₁, hz₁, (eq₁ : _ * _ = _)⟩, ⟨z₂, hz₂, (eq₂ : _ * _ = _)⟩⟩ := eq
    rw [gen_eq_gen_iff]
    have := calc  c⁻¹ * d
      _ = (z₁ * x⁻¹) * d := by rw [← eq₁]; simp
      _ = (z₁ * x⁻¹) * (x * z₂⁻¹) := by rw [← eq₂]; simp
      _ = z₁ * z₂⁻¹ := by group
    rw [this]
    exact mul_mem hz₁ (inv_mem hz₂)


theorem eq_of_not_disjoint (C D : QGroup H) (x : G) (hC : x ∈ C) (hD : x ∈ D) : C = D := by
  refine eq_or_disjoint C D |>.rec id ?_
  contrapose!
  intro h
  exact ⟨x, hC, hD⟩

instance : One (QGroup H) where
  one := ⟨H, ⟨1, by simp⟩⟩

lemma one_def : ((1 : QGroup H) : Set G) = H := rfl

@[simp]
lemma mem_one_iff {g : G} : g ∈ (1 : QGroup H) ↔ g ∈ H := Iff.rfl

@[simp]
lemma gen_one : gen H 1 = 1 := by
  ext g
  simp

instance : Mul (QGroup H) where
  mul C D := ⟨C.out • D.out • H, ⟨C.out * D.out, by simp [mul_smul, out_spec]⟩⟩

lemma mul_def (C D : QGroup H) :
    ((C * D : QGroup H) : Set G) = C.out • D.out • H := rfl

lemma mul_def' (C D : QGroup H) :
    ((C * D : QGroup H) : Set G) = C.out • D := by
  rw [mul_def, out_spec]

@[simp]
lemma gen_mul_gen (g g' : G) : gen H g * gen H g' = gen H (g * g') := by
  apply eq_of_not_disjoint _ _ (g * g')
  · rw [← SetLike.mem_coe, mul_def']
    rw [Set.mem_smul_set]
    refine ⟨(gen H g).out ⁻¹ * g * g', ?_, by simp [mul_assoc]⟩
    rw [SetLike.mem_coe, mem_gen_iff]
    refine ⟨g'⁻¹ * (gen H g).out⁻¹ * g * g', ?_, by simp [mul_assoc]⟩
    rw [mul_assoc g'⁻¹]
    apply Subgroup.Normal.conj_mem' inferInstance
    rw [show (gen H g).out⁻¹ * g = (g⁻¹ * (gen H g).out)⁻¹ by group, inv_mem_iff]
    rw [← gen_eq_gen_iff]
    simp only [gen_out]
  · exact ⟨1, by simp⟩

lemma mul_one' (C : QGroup H) : C * 1 = C := by
  induction C using gen_induction with | h g =>
  rw [← gen_one, gen_mul_gen, mul_one]

lemma one_mul' (C : QGroup H) : 1 * C = C := by
  induction C using gen_induction with | h g =>
  rw [← gen_one, gen_mul_gen, one_mul]

lemma mul_assoc' (C D E : QGroup H) : (C * D) * E = C * (D * E) := by
  induction C using gen_induction with | h g =>
  induction D using gen_induction with | h g' =>
  induction E using gen_induction with | h g'' =>
  simp [gen_mul_gen, mul_assoc]

instance : Inv (QGroup H) where
  inv C := ⟨C.out⁻¹ • H, ⟨C.out⁻¹, rfl⟩⟩

lemma gen_inv (g : G) : (gen H g)⁻¹ = gen H g⁻¹ := by
  symm
  rw [gen_eq_iff]
  change _ ∈ ((gen H g).out⁻¹ • H : Set G)
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp only [inv_inv, smul_eq_mul, SetLike.mem_coe]
  rw [Subgroup.Normal.mem_comm_iff inferInstance, ← gen_eq_gen_iff]
  simp

lemma inv_mul_cancel' (C : QGroup H) : C⁻¹ * C = 1 := by
  induction C using gen_induction with | h g =>
  simp [gen_inv, gen_mul_gen]

instance : Group (QGroup H) where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  inv_mul_cancel := inv_mul_cancel'

end QGroup

variable {X Y : Type} [Group X] [Group Y] (f : X →* Y)

@[simps apply]
def QGroup.kerToImage : QGroup f.ker →* f.range where
  toFun C := ⟨f C.out, ⟨C.out, rfl⟩⟩
  map_one' := by
    ext1
    simp only [OneMemClass.coe_one]
    have mem : out (1 : QGroup f.ker) ∈ (out (1 : QGroup f.ker) • f.ker : Set X) := by
      rw [Set.mem_smul_set]
      use 1, one_mem _
      simp
    simpa using mem
  map_mul' := by
    intro x y
    induction x using QGroup.gen_induction with | h x =>
    induction y using QGroup.gen_induction with | h y =>
    ext1
    simp only [gen_mul_gen, Subgroup.coe_mul, ← map_mul]

    have mem : (gen f.ker x).out * (gen f.ker y).out ∈ gen f.ker (x * y) := by
      rw [← gen_eq_iff, ← gen_mul_gen]
      simp
    simp only [mem_gen_iff, MonoidHom.mem_ker] at mem
    obtain ⟨z, hz, hz'⟩ := mem
    rw [hz', map_mul, hz, mul_one]

    have mem : (gen f.ker (x * y)).out ∈ ((gen f.ker (x * y)).out • f.ker : Set X) := by
      rw [Set.mem_smul_set]
      refine ⟨1, by simp⟩

    simp only [out_spec, SetLike.mem_coe, mem_gen_iff, MonoidHom.mem_ker] at mem
    obtain ⟨w, hw, hw'⟩ := mem
    rw [hw', map_mul, hw, mul_one]

example : Function.Injective (QGroup.kerToImage f) := by
  intro C D h
  induction C using QGroup.gen_induction with | h x =>
  induction D using QGroup.gen_induction with | h y =>
  simp only [QGroup.kerToImage_apply, Subtype.mk.injEq] at h
  rw [QGroup.gen_eq_gen_iff]
  simp only [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
  have : (QGroup.gen f.ker x).out ∈ ((QGroup.gen f.ker x).out • f.ker : Set X):= by
    rw [Set.mem_smul_set]
    refine ⟨1, by simp⟩
  simp only [QGroup.out_spec, SetLike.mem_coe, QGroup.mem_gen_iff, MonoidHom.mem_ker] at this
  obtain ⟨z, hz, hz'⟩ := this
  rw [hz', map_mul, hz, mul_one] at h

  have : (QGroup.gen f.ker y).out ∈ ((QGroup.gen f.ker y).out • f.ker : Set X):= by
    rw [Set.mem_smul_set]
    refine ⟨1, by simp⟩
  simp only [QGroup.out_spec, SetLike.mem_coe, QGroup.mem_gen_iff, MonoidHom.mem_ker] at this
  obtain ⟨w, hw, hw'⟩ := this
  rw [hw', map_mul, hw, mul_one] at h
  exact h

example : Function.Surjective (QGroup.kerToImage f) := by
  rintro ⟨_, ⟨x, rfl⟩⟩
  use QGroup.gen f.ker x
  simp only [QGroup.kerToImage_apply, Subtype.mk.injEq]
  have : (QGroup.gen f.ker x).out ∈ ((QGroup.gen f.ker x).out • f.ker : Set X):= by
    rw [Set.mem_smul_set]
    refine ⟨1, by simp⟩
  simp only [QGroup.out_spec, SetLike.mem_coe, QGroup.mem_gen_iff, MonoidHom.mem_ker] at this
  obtain ⟨z, hz, hz'⟩ := this
  rw [hz', map_mul, hz, mul_one]
