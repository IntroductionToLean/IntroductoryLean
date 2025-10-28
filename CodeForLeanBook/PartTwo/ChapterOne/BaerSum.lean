import Mathlib

variable (A B : Type) [AddCommGroup A] [AddCommGroup B]

variable {B} in
def AddSubgroup.pullback {E E' : Type} [AddCommGroup E] [AddCommGroup E']
    (g : E →+ B) (g' : E' →+ B) : AddSubgroup (E × E') where
  carrier := { (e, e') | g e = g' e'  }
  add_mem' := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ (h: g a = g' b) (h': g a' = g' b')
    simp [h, h']
  zero_mem' := by simp
  neg_mem' := by simp

@[simp]
lemma AddSubgroup.mem_pullback {E E' : Type} [AddCommGroup E] [AddCommGroup E']
    (g : E →+ B) (g' : E' →+ B) (x : E × E') :
    x ∈ AddSubgroup.pullback g g' ↔ g x.1 = g' x.2 := Iff.rfl

structure PreExtension where
  carrier : Type
  [ab : AddCommGroup carrier]
  f : A →+ carrier
  g : carrier →+ B
  injective : Function.Injective f
  surjective : Function.Surjective g
  exact : Function.Exact f g -- image f = ker g

instance : CoeSort (PreExtension A B) Type where
  coe := PreExtension.carrier

instance (E : PreExtension A B) : AddCommGroup E := E.ab

namespace PreExtension

variable {A B}

@[simps f g]
def zero : PreExtension A B where
  carrier := A × B
  ab := inferInstance
  f := AddMonoidHom.inl A B
  g := AddMonoidHom.snd A B
  injective := by rintro a a' ⟨⟩; rfl
  surjective b := ⟨(0, b), rfl⟩
  exact := by
    rintro ⟨a, b⟩
    simp [eq_comm]

@[simps f g]
def neg (E : PreExtension A B) : PreExtension A B where
  carrier := E
  ab := inferInstance
  f := - E.f
  g := E.g
  injective := by
    intro a a'
    simp only [AddMonoidHom.neg_apply, neg_inj]
    apply E.injective
  surjective := by
    intro b
    obtain ⟨e, he⟩ := E.surjective (-b)
    use -e
    simp [he]
  exact a := by
    simp only [E.exact a, Set.mem_range, AddMonoidHom.neg_apply]
    fconstructor
    · rintro ⟨y, hy⟩
      refine ⟨-y, by simp [hy]⟩

/--
E.g ×_A E'.g / ⟨(E.f a, -E'.f a)⟩
-/
@[simps f g]
def add (E E' : PreExtension A B) : PreExtension A B where
  carrier :=
    AddSubgroup.pullback E.g E'.g ⧸
    (AddMonoidHom.prod E.f (-E'.f) |>.range).addSubgroupOf _
  ab := inferInstance
  f :=
  { toFun a := QuotientAddGroup.mk' _ ⟨(E.f a, 0), by
    simp only [AddSubgroup.mem_pullback, map_zero]
    exact congr($(E.exact.comp_eq_zero) a)
    ⟩
    map_zero' := by
      simpa [AddSubgroup.mem_addSubgroupOf] using ⟨0, by simp, by simp⟩
    map_add' a a' := Quotient.sound <| by simp }
  g := QuotientAddGroup.lift _
    { toFun e := E.g e.1.1
      map_zero' := by simp
      map_add' :=  by
        rintro ⟨⟨e1, e1'⟩, (h : _ = _)⟩ ⟨⟨e2, e2'⟩, (h' : _ = _)⟩
        simp } <| by
    rintro ⟨⟨e, e'⟩, (h : _ = _)⟩ ⟨x, rfl, rfl⟩
    simp only [AddMonoidHom.neg_apply, AddMonoidHom.mem_ker, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    exact congr($(E.exact.comp_eq_zero) _)
  injective := by
    rintro a a' h
    simp only [QuotientAddGroup.mk'_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
    rw [QuotientAddGroup.eq] at h
    apply_fun E.f using E.injective
    simp only [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, NegMemClass.coe_neg, Prod.neg_mk,
      neg_zero, Prod.mk_add_mk, add_zero, AddMonoidHom.mem_range, AddMonoidHom.prod_apply,
      AddMonoidHom.neg_apply, Prod.mk.injEq, neg_eq_zero] at h
    obtain ⟨x, hx, x_eq⟩ := h
    rw [← show E'.f 0 = 0 by simp] at x_eq
    have := E'.injective x_eq
    subst this
    rw [map_zero, neg_add_eq_sub, eq_comm, sub_eq_zero] at hx
    exact hx.symm
  surjective := by
    intro b
    obtain ⟨e, he⟩ := E.surjective b
    obtain ⟨e', he'⟩ := E'.surjective b
    use QuotientAddGroup.mk' _ ⟨(e, e'), by simp [he, he']⟩
    simp [he]
  exact := by
    intro a
    induction a using QuotientAddGroup.induction_on with | H a =>
    rcases a with ⟨⟨a, b⟩, ha⟩
    simp only [AddSubgroup.mem_pullback, QuotientAddGroup.lift_mk, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, QuotientAddGroup.mk'_apply, Set.mem_range] at ha ⊢
    constructor
    · rintro h
      have h' : E'.g b = 0 := by
        rw [← ha]
        exact h
      obtain ⟨a, rfl⟩ := E.exact a |>.1 h
      obtain ⟨a', rfl⟩ := E'.exact b |>.1 h'
      use a + a'
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      simp only [map_add, AddSubgroup.coe_add, NegMemClass.coe_neg, Prod.neg_mk, neg_add_rev,
        neg_zero, Prod.mk_add_mk, neg_add_cancel_right, zero_add, AddMonoidHom.mem_range,
        AddMonoidHom.prod_apply, AddMonoidHom.neg_apply, Prod.mk.injEq]
      use -a'
      simp
    · rintro ⟨x, hx⟩
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at hx
      simp only [AddSubgroup.coe_add, NegMemClass.coe_neg, Prod.neg_mk, neg_zero, Prod.mk_add_mk,
        zero_add, AddMonoidHom.mem_range, AddMonoidHom.prod_apply, AddMonoidHom.neg_apply,
        Prod.mk.injEq] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simp only [map_neg] at ha
      rw [show E'.g (E'.f y) = 0 from congr($(E'.exact.comp_eq_zero) y)] at ha
      simp [ha]

end PreExtension

variable {A B} (E₁ E₂ E₃ E₄ : PreExtension A B)

structure PreExtensionHom extends E₁ →+ E₂ where
  comm_f : toAddMonoidHom.comp E₁.f = E₂.f
  comm_g : E₂.g.comp toAddMonoidHom = E₁.g

namespace PreExtensionHom

instance : FunLike (PreExtensionHom E₁ E₂) E₁ E₂ where
  coe h := h.toAddMonoidHom
  coe_injective' := by rintro ⟨⟨⟨h, _⟩, _⟩, _, _⟩ ⟨⟨⟨h, _⟩, _⟩, _, _⟩ rfl; rfl

instance : AddHomClass (PreExtensionHom E₁ E₂) E₁ E₂ where
  map_add h := h.toAddMonoidHom.map_add

instance : ZeroHomClass (PreExtensionHom E₁ E₂) E₁ E₂ where
  map_zero h := h.toAddMonoidHom.map_zero

instance : AddMonoidHomClass (PreExtensionHom E₁ E₂) E₁ E₂ where

@[simp]
lemma comm_f_apply (h : PreExtensionHom E₁ E₂) (a : A) :
    h (E₁.f a) = E₂.f a := congr($h.comm_f a)

@[simp]
lemma comm_g_apply (h : PreExtensionHom E₁ E₂) (e : E₁) :
    E₂.g (h e) = E₁.g e := congr($h.comm_g e)

def id (E : PreExtension A B) : PreExtensionHom E E where
  toAddMonoidHom := AddMonoidHom.id E
  comm_f := rfl
  comm_g := rfl

@[simp]
lemma id_apply (x : E₁) : (PreExtensionHom.id E₁) x = x := rfl

@[simps! toAddMonoidHom]
def comp {E₁ E₂ E₃ : PreExtension A B}
    (h₁ : PreExtensionHom E₂ E₃) (h₂ : PreExtensionHom E₁ E₂) : PreExtensionHom E₁ E₃ where
  toAddMonoidHom := h₁.toAddMonoidHom.comp h₂.toAddMonoidHom
  comm_f := by rw [AddMonoidHom.comp_assoc, h₂.comm_f, h₁.comm_f]
  comm_g := by rw [← AddMonoidHom.comp_assoc, h₁.comm_g, h₂.comm_g]

@[simp]
lemma comp_apply {E₁ E₂ E₃ : PreExtension A B}
    (h₁ : PreExtensionHom E₂ E₃) (h₂ : PreExtensionHom E₁ E₂) (x : E₁) :
    (h₁.comp h₂) x = h₁ (h₂ x) := rfl

@[ext]
lemma ext {h₁ h₂ : PreExtensionHom E₁ E₂} (H : ∀ x, h₁ x = h₂ x) : h₁ = h₂ := DFunLike.ext h₁ h₂ H

lemma comp_assoc {E₁ E₂ E₃ E₄ : PreExtension A B}
    (h₁ : PreExtensionHom E₃ E₄) (h₂ : PreExtensionHom E₂ E₃) (h₃ : PreExtensionHom E₁ E₂) :
    (h₁.comp h₂).comp h₃ = h₁.comp (h₂.comp h₃) := by
  ext x
  simp

@[simp]
lemma comp_id (h : PreExtensionHom E₁ E₂) : h.comp (PreExtensionHom.id E₁) = h := by
  ext x; simp

@[simp]
lemma id_comp (h : PreExtensionHom E₁ E₂) : (PreExtensionHom.id E₂).comp h = h := by
  ext x; simp

variable {E₁ E₂ E₃ E₄} in
@[simps toAddMonoidHom]
def add (h₁ : PreExtensionHom E₁ E₂) (h₂ : PreExtensionHom E₃ E₄) :
    PreExtensionHom (.add E₁ E₃) (.add E₂ E₄) where
  toAddMonoidHom :=
    QuotientAddGroup.map _ _ (AddMonoidHom.prodMap h₁ h₂ |>.restrict _ |>.codRestrict _ (by
      rintro ⟨⟨e, e'⟩, h⟩
      simp only [AddMonoidHom.restrict_apply, AddMonoidHom.coe_prodMap, AddMonoidHom.coe_coe,
        Prod.map_apply, AddSubgroup.mem_pullback, comm_g_apply]
      exact h)) <| by
      rintro ⟨⟨e, e'⟩, (h : _ = _)⟩ ⟨x, rfl, rfl⟩
      simp only [AddMonoidHom.neg_apply, AddSubgroup.mem_comap, AddMonoidHom.codRestrict_apply,
        AddMonoidHom.restrict_apply, AddMonoidHom.coe_prodMap, AddMonoidHom.coe_coe, Prod.map_apply,
        comm_f_apply, map_neg, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range,
        AddMonoidHom.prod_apply, Prod.mk.injEq, neg_inj]
      use x
  comm_f := by ext x; refine QuotientAddGroup.eq.2 ?_; simp
  comm_g := by
    ext x
    obtain ⟨⟨⟨e, e'⟩, (hx : _ = _)⟩, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
    -- refine QuotientAddGroup.eq.1 ?_
    simp only [PreExtension.add_g, QuotientAddGroup.mk'_apply, AddMonoidHom.coe_comp,
      Function.comp_apply]
    -- refine QuotientAddGroup.mk'_eq_mk'.1 ?_
    erw [QuotientAddGroup.map_mk', AddMonoidHom.codRestrict_apply]
    simp only [AddMonoidHom.restrict_apply, AddMonoidHom.coe_prodMap, AddMonoidHom.coe_coe,
      Prod.map_apply]
    erw [QuotientAddGroup.lift_mk']
    change E₂.g (h₁ _) = E₁.g e
    rw [h₁.comm_g_apply]

@[simp]
lemma add_apply {h₁ : PreExtensionHom E₁ E₂} {h₂ : PreExtensionHom E₃ E₄} (x : E₁ × E₃) (hx) :
    (h₁.add h₂) ⟦⟨x, hx⟩⟧= ⟦⟨(h₁ x.1, h₂ x.2), (by simpa)⟩⟧ := rfl

variable {E₂' : PreExtension A B} in
lemma comp_add
    (h₁ : PreExtensionHom E₁ E₂)
    (h₁' : PreExtensionHom E₂ E₂')
    (h₂ : PreExtensionHom E₃ E₄) :
    (h₁'.comp h₁).add h₂ =
    (h₁'.add h₂).comp (h₁.add (.id _)) := by
  ext ⟨a, b⟩
  simp only [comp_apply]
  rfl

variable {E₁' E₂' E₃' : PreExtension A B} in
lemma add_comp_add
    (h₁ : PreExtensionHom E₁ E₂)
    (h₁' : PreExtensionHom E₁' E₂')
    (h₂ : PreExtensionHom E₂ E₃)
    (h₂' : PreExtensionHom E₂' E₃') :
    (h₂.add h₂').comp (h₁.add h₁') =
    (h₂.comp h₁).add (h₂'.comp h₁') := by
  ext ⟨a, b⟩
  simp
  rfl

@[simp]
lemma id_add_id (E₁ E₂ : PreExtension A B) :
    (PreExtensionHom.id E₁).add (PreExtensionHom.id E₂) = PreExtensionHom.id (E₁.add E₂) := by
  ext ⟨a, b⟩; simp; rfl

variable {E₁ E₂} in
@[simps toAddMonoidHom]
def neg (h : PreExtensionHom E₁ E₂) : PreExtensionHom E₁.neg E₂.neg where
  toAddMonoidHom := h.toAddMonoidHom
  comm_f := by simp [h.comm_f]
  comm_g := by simp [h.comm_g]

@[simp]
lemma neg_apply (h : PreExtensionHom E₁ E₂) (x : E₁) :
  h.neg x = h x := rfl

lemma neg_comp (h₁ : PreExtensionHom E₁ E₂) (h₂ : PreExtensionHom E₂ E₃) :
    h₂.neg.comp h₁.neg = (h₂.comp h₁).neg := by
  ext x; simp

end PreExtensionHom

structure PreExtensionIso where
  hom : PreExtensionHom E₁ E₂
  inv : PreExtensionHom E₂ E₁
  hom_inv_id : hom.comp inv = .id _
  inv_hom_id : inv.comp hom = .id _

namespace PreExtensionIso

def refl (E : PreExtension A B) : PreExtensionIso E E where
  hom := PreExtensionHom.id E
  inv := PreExtensionHom.id E
  hom_inv_id := rfl
  inv_hom_id := rfl

variable {E₁ E₂ E₃}
def symm (h : PreExtensionIso E₁ E₂) : PreExtensionIso E₂ E₁ where
  hom := h.inv
  inv := h.hom
  hom_inv_id := h.inv_hom_id
  inv_hom_id := h.hom_inv_id

def trans (h₁ : PreExtensionIso E₁ E₂) (h₂ : PreExtensionIso E₂ E₃) : PreExtensionIso E₁ E₃ where
  hom := PreExtensionHom.comp h₂.hom h₁.hom
  inv := PreExtensionHom.comp h₁.inv h₂.inv
  hom_inv_id := by
    rw [← PreExtensionHom.comp_assoc, PreExtensionHom.comp_assoc _ _ h₁.inv, h₁.hom_inv_id,
      PreExtensionHom.comp_id, h₂.hom_inv_id]
  inv_hom_id := by
    rw [← PreExtensionHom.comp_assoc, PreExtensionHom.comp_assoc _ _ h₂.hom, h₂.inv_hom_id,
      PreExtensionHom.comp_id, h₁.inv_hom_id]

def addZero (E : PreExtension A B) :
    PreExtensionIso E (E.add .zero) where
  hom :=
  { toFun e := QuotientAddGroup.mk' _ ⟨(e, (0, E.g e)), by
      simp only [PreExtension.zero_g, AddSubgroup.mem_pullback]
      rfl⟩
    map_zero' := by simp only [PreExtension.zero_g, PreExtension.zero_f, map_zero,
      QuotientAddGroup.mk'_apply]; rfl
    map_add' := by
      intro e e'
      simp only [PreExtension.zero_g, PreExtension.zero_f, map_add, QuotientAddGroup.mk'_apply]
      erw [QuotientAddGroup.eq]
      simp only [PreExtension.zero_g, AddMemClass.mk_add_mk, Prod.mk_add_mk]
      rw [AddSubgroup.mem_addSubgroupOf]
      simp only [AddSubgroup.coe_add, NegMemClass.coe_neg, Prod.neg_mk, neg_add_rev, Prod.mk_add_mk,
        AddMonoidHom.mem_range, AddMonoidHom.prod_apply, Prod.mk.injEq]
      use 0
      constructor
      · simp only [map_zero]
        abel
      erw [AddMonoidHom.neg_apply]
      change - (0, 0) = (_, _)
      simp only [Prod.neg_mk, neg_zero, Prod.mk.injEq]
      constructor
      · change 0 = -0 + (0 + 0)
        abel
      · change 0 = -(E.g e + E.g e') + (E.g e + E.g e')
        abel
    comm_f := by
      simp only [PreExtension.zero_g, PreExtension.zero_f, QuotientAddGroup.mk'_apply,
        PreExtension.add_f]
      ext a
      simp only [AddMonoidHom.coe_comp, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply]
      erw [QuotientAddGroup.eq]
      rw [AddSubgroup.mem_addSubgroupOf]
      simp only [AddSubgroup.coe_add, NegMemClass.coe_neg, Prod.neg_mk, Prod.mk_add_mk,
        neg_add_cancel, add_zero, AddMonoidHom.mem_range, AddMonoidHom.prod_apply, Prod.mk.injEq]
      use 0
      constructor
      · simp
      change -(0, 0) = _
      ext
      · change -0 = -0
        rfl
      · change -0 = - (E.g (E.f a))
        simp only [neg_zero, zero_eq_neg]
        have := E.exact.comp_eq_zero
        have := congr_fun this a
        exact this
    comm_g := by sorry }
  inv :=
  { __ := QuotientAddGroup.lift _
      (AddMonoidHom.restrict (AddMonoidHom.coprod (AddMonoidHom.id _) (E.f.comp <| AddMonoidHom.fst A B)) _)
      (by
        simp only [PreExtension.zero_g, PreExtension.zero_f, AddMonoidHom.ker_restrict]
        rintro ⟨⟨e, ⟨a, b⟩⟩, (rfl : E.g e = b)⟩ h
        rw [AddSubgroup.mem_addSubgroupOf] at h
        simp only [AddMonoidHom.mem_range, AddMonoidHom.prod_apply, Prod.mk.injEq] at h
        obtain ⟨x, rfl, (hx : -(x, 0) = _)⟩ := h
        simp only [Prod.neg_mk, neg_zero, Prod.mk.injEq] at hx
        have := hx.1
        subst this
        clear hx
        rw [AddSubgroup.mem_addSubgroupOf]
        simp)
    comm_f := sorry
    comm_g := sorry }
  hom_inv_id := by

    ext x
    induction x using QuotientAddGroup.induction_on with | H x =>
    rcases x with ⟨⟨e, ⟨a, b⟩⟩, (rfl : E.g e = b)⟩
    simp only [PreExtension.zero_g, PreExtension.zero_f, QuotientAddGroup.mk'_apply,
      PreExtensionHom.comp_apply, PreExtensionHom.id_apply]
    change QuotientAddGroup.mk' _ _ = QuotientAddGroup.mk' _ _
    erw [QuotientAddGroup.eq]
    rw [AddSubgroup.mem_addSubgroupOf]
    simp only [AddSubgroup.coe_add, NegMemClass.coe_neg, Prod.neg_mk, Prod.mk_add_mk]
    erw [QuotientAddGroup.lift_mk']
    erw [AddMonoidHom.restrict_apply]
    simp only [AddMonoidHom.coprod_apply, AddMonoidHom.id_apply, AddMonoidHom.coe_comp,
      AddMonoidHom.coe_fst, Function.comp_apply, neg_add_rev, neg_add_cancel_right, map_add,
      AddMonoidHom.mem_range, AddMonoidHom.prod_apply, Prod.mk.injEq]
    use - a
    simp only [map_neg, true_and]
    change (_, _) = (_, _)
    erw [AddMonoidHom.neg_apply]
    rw [AddMonoidHom.inl_apply]
    simp only [Prod.neg_mk, neg_zero, neg_neg, Prod.mk.injEq, right_eq_add]
    constructor
    · exact neg_zero
    change 0 = -(E.g e + E.g (E.f a)) + E.g e
    have : E.g (E.f a) = 0 := by sorry
    rw [this]
    abel
  inv_hom_id := _
  -- hom :=
  -- { toFun e := QuotientAddGroup.mk' _ ⟨(e, ⟨0, E.g e⟩), by simp; rfl⟩
  --   map_zero' := by simp only [map_zero]; rfl
  --   map_add' := by
  --     intro e e'
  --     simp only [PreExtension.zero_g, PreExtension.zero_f, map_add, QuotientAddGroup.mk'_apply]
  --     refine QuotientAddGroup.eq.2 ?_
  --     simp? [AddSubgroup.mem_addSubgroupOf]
  --     refine ⟨0, by simp only [map_zero]; abel, Prod.ext ?_ ?_⟩

  --     · simp only [map_zero, Prod.fst_zero]
  --       change (0 : A) = -0 + (0 + 0)
  --       simp
  --     · simp only [map_zero, Prod.snd_zero]
  --       change 0 = -(_ + _) + (_ + _)
  --       abel
  --   comm_f := by
  --     ext a
  --     simp only [PreExtension.zero_g, PreExtension.zero_f, QuotientAddGroup.mk'_apply,
  --       AddMonoidHom.coe_comp, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply,
  --       PreExtension.add_f]
  --     erw [QuotientAddGroup.eq]
  --     simp only [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, NegMemClass.coe_neg,
  --       Prod.neg_mk, Prod.mk_add_mk, neg_add_cancel, add_zero, AddMonoidHom.mem_range,
  --       AddMonoidHom.prod_apply, Prod.mk.injEq]
  --     use 0
  --     simp only [map_zero, zero_eq_neg, true_and]
  --     rw [show E.g (E.f a) = 0 from congr($(E.exact.comp_eq_zero) a)]
  --     rfl
  --   comm_g := by rfl }
  -- inv :=
  -- { toAddMonoidHom := QuotientAddGroup.lift _
  --     (AddMonoidHom.restrict
  --       (AddMonoidHom.coprod (AddMonoidHom.id _) (E.f.comp <| AddMonoidHom.fst _ _))
  --       _)
  --     (by
  --       rintro ⟨⟨e, ⟨a, b⟩⟩, (h : E.g e = b)⟩ h'
  --       rw [AddSubgroup.mem_addSubgroupOf] at h'
  --       simp only [PreExtension.zero_f, AddMonoidHom.mem_range, AddMonoidHom.prod_apply,
  --         Prod.mk.injEq] at h'
  --       obtain ⟨x, rfl, hx⟩ := h'
  --       rw [show E.g (E.f x) = 0 from congr($(E.exact.comp_eq_zero) x)] at h
  --       subst h
  --       simp only [PreExtension.zero_g, AddMonoidHom.ker_restrict]
  --       rw [AddSubgroup.mem_addSubgroupOf]
  --       simp only [AddMonoidHom.mem_ker, AddMonoidHom.coprod_apply, AddMonoidHom.id_apply,
  --         AddMonoidHom.coe_comp, AddMonoidHom.coe_fst, Function.comp_apply]
  --       change (- x, -0) = (a, 0) at hx
  --       simp only [neg_zero, Prod.mk.injEq, and_true] at hx
  --       subst hx
  --       simp)
  --   comm_f := by
  --     ext a
  --     simp only [PreExtension.zero_g, PreExtension.zero_f, PreExtension.add_f,
  --       QuotientAddGroup.mk'_apply, AddMonoidHom.coe_comp, Function.comp_apply]
  --     erw [QuotientAddGroup.lift_mk']
  --     erw [AddMonoidHom.restrict_apply]
  --     simp
  --   comm_g := by
  --     ext x
  --     induction x using QuotientAddGroup.induction_on with | H x =>
  --     rcases x with ⟨⟨e, ⟨a, b⟩⟩, (rfl : E.g e = b)⟩
  --     simp only [PreExtension.zero_g, PreExtension.zero_f, AddMonoidHom.coe_comp,
  --       Function.comp_apply, PreExtension.add_g]
  --     change E.g (_ + _) = _
  --     simp only [AddMonoidHom.id_comp, AddSubmonoidClass.subtype_apply, AddMonoidHom.coe_fst,
  --       AddMonoidHom.coe_comp, AddMonoidHom.coe_snd, Function.comp_apply, map_add]
  --     rw [show E.g (E.f a) = 0 by rw [← Function.comp_apply (f := E.g), E.exact.comp_eq_zero]; rfl]
  --     simp only [add_zero]
  --     rfl }
  -- hom_inv_id := by
  --   ext x
  --   induction x using QuotientAddGroup.induction_on with | H x =>
  --   rcases x with ⟨⟨e, ⟨a, b⟩⟩, (rfl : E.g e = b)⟩
  --   simp only [PreExtension.zero_g, PreExtension.zero_f, QuotientAddGroup.mk'_apply,
  --     PreExtensionHom.comp_apply, PreExtensionHom.id_apply]
  --   change QuotientAddGroup.mk' _ _ = QuotientAddGroup.mk' _ _
  --   refine QuotientAddGroup.eq.2 ?_
  --   rw [AddSubgroup.mem_addSubgroupOf]
  --   dsimp only [AddSubgroup.coe_add, NegMemClass.coe_neg, Prod.neg_mk, Prod.mk_add_mk]
  --   erw [QuotientAddGroup.lift_mk']
  --   erw [AddMonoidHom.restrict_apply]
  --   simp only [AddMonoidHom.coprod_apply, AddMonoidHom.id_apply, AddMonoidHom.coe_comp,
  --     AddMonoidHom.coe_fst, Function.comp_apply, neg_add_rev, neg_add_cancel_right, map_add,
  --     AddMonoidHom.mem_range, AddMonoidHom.prod_apply, Prod.mk.injEq]
  --   use - a
  --   simp only [map_neg, true_and]
  --   change (_, _) = (_, _)
  --   erw [AddMonoidHom.neg_apply]
  --   rw [AddMonoidHom.inl_apply]
  --   simp only [Prod.neg_mk, neg_zero, neg_neg, Prod.mk.injEq, right_eq_add]
  --   constructor
  --   · exact neg_zero
  --   change 0 = -(E.g e + E.g (E.f a)) + E.g e
  --   sorry
  -- inv_hom_id := by
  --   simp only [PreExtension.zero_g, PreExtension.zero_f, QuotientAddGroup.mk'_apply]
  --   ext e
  --   simp only [PreExtensionHom.comp_apply, PreExtensionHom.id_apply]
  --   erw [QuotientAddGroup.lift_mk']
  --   erw [AddMonoidHom.restrict_apply]
  --   simp only [AddMonoidHom.coprod_apply, AddMonoidHom.id_apply, AddMonoidHom.coe_comp,
  --     AddMonoidHom.coe_fst, Function.comp_apply, map_zero, add_zero]
  --   rintro ⟨⟨e, ⟨a, b⟩⟩, (rfl : _ = b)⟩ h
  --   rw [AddSubgroup.mem_addSubgroupOf] at h
  --   simp only [AddMonoidHom.mem_range, AddMonoidHom.prod_apply, Prod.mk.injEq] at h
  --   obtain ⟨x, rfl, (hx : (_, _) = (_, _))⟩ := h
  --   simp only [Prod.mk.injEq] at hx
  --   rcases hx with ⟨rfl, hx⟩
  --   change -0 = _ at hx
  --   simp only [AddMonoidHom.ker_restrict]
  --   rw [AddSubgroup.mem_addSubgroupOf]
  --   simp only [AddMonoidHom.mem_ker, AddMonoidHom.coprod_apply, AddMonoidHom.id_apply,
  --     AddMonoidHom.coe_comp, AddMonoidHom.coe_fst, Function.comp_apply, map_neg]
  --   change E.f x + -E.f x = 0
  --   rw [add_neg_cancel]

#check QuotientAddGroup.lift
#check QuotientAddGroup.map

def addAssoc (E₁ E₂ E₃ : PreExtension A B) :
    PreExtensionIso (E₁.add (E₂.add E₃)) ((E₁.add E₂).add E₃) := sorry

end PreExtensionIso

variable (A B) in
abbrev Extension :=  Quotient (α := PreExtension A B)
  { r E₁ E₂ := Nonempty (PreExtensionIso E₁ E₂)
    iseqv :=
    { refl E := ⟨PreExtensionIso.refl E⟩
      symm := Nonempty.map PreExtensionIso.symm
      trans := by intro _ _ _ ⟨e⟩ ⟨e'⟩; exact ⟨e.trans e'⟩ } }

instance : Zero (Extension A B) where
  zero := Quotient.mk'' .zero

instance : Add (Extension A B) where
  add := Quotient.map₂ PreExtension.add <| by
    rintro E E' ⟨e⟩ F F' ⟨f⟩
    refine ⟨⟨.add e.hom f.hom, .add e.inv f.inv, ?_, ?_⟩⟩
    · rw [PreExtensionHom.add_comp_add, e.hom_inv_id, f.hom_inv_id, PreExtensionHom.id_add_id]
    · rw [PreExtensionHom.add_comp_add, e.inv_hom_id, f.inv_hom_id, PreExtensionHom.id_add_id]

instance : Neg (Extension A B) where
  neg := Quotient.map PreExtension.neg <| by
    rintro E E' ⟨e⟩
    refine ⟨⟨e.hom.neg, e.inv.neg, ?_, ?_⟩⟩
    · rw [PreExtensionHom.neg_comp, e.hom_inv_id]; rfl
    · rw [PreExtensionHom.neg_comp, e.inv_hom_id]; rfl

-- instance : AddCommGroup (Extension A B) where
--   add_assoc E₁ E₂ E₃ := Quotient.inductionOn₃ E₁ E₂ E₃ <| fun E₁ E₂ E₃ =>
--     Quotient.sound ⟨PreExtensionIso.addAssoc _ _ _ |>.symm⟩
--   zero_add E := Quotient.inductionOn E <| fun E => sorry
--   add_zero := _
--   nsmul := nsmulRec
--   neg := _
--   sub_eq_add_neg := _
--   zsmul := zsmulRec
--   neg_add_cancel := _
--   add_comm := _
