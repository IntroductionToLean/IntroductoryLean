import Mathlib

namespace comb

#check Fintype

#check Finite

#check Finset

#check Set.Finite

#check Finset.card

#check Set.ncard

#check Set.encard

#check Set.toFinset_card

#check Set.Finite.fintype

#check Fintype.finite

#check Fintype.ofFinite

#check Nat.card

#check Fintype.card_congr

lemma Finset.cons_eq_cons {α : Type} (s t : Finset α) (a : α) (hs : a ∉ s) (ht : a ∉ t) :
    Finset.cons a s hs = Finset.cons a t ht ↔ s = t := by
  constructor
  · intro eq
    ext x
    constructor
    · intro hxs
      have m := eq ▸ Finset.subset_cons hs hxs
      simp only [Finset.mem_cons] at m
      refine m.resolve_left ?_
      rintro rfl
      contradiction
    · intro hxt
      have m := eq.symm ▸ Finset.subset_cons ht hxt
      simp only [Finset.mem_cons] at m
      refine m.resolve_left ?_
      rintro rfl
      contradiction
  · rintro rfl; rfl
#check Sum.rec
example (n k : ℕ) :
    (n + 1).choose (k + 1) = n.choose k + n.choose (k + 1) := by
  have lhs_eq : (n + 1).choose (k + 1) =
      (Finset.powersetCard (k + 1) (Finset.univ (α := Fin (n + 1)))).card := by
    simp only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  let e :
      Finset.powersetCard k (Finset.univ (α := Fin n)) ⊕
      Finset.powersetCard (k + 1) (Finset.univ (α := Fin n)) →
      Finset.powersetCard (k + 1) (Finset.univ (α := Fin (n + 1))) :=
    Sum.rec
      (fun s => ⟨Finset.cons (Fin.last _) (s.1.map ⟨Fin.castSucc, Fin.castSucc_injective n⟩) (by simp),
        by simpa [-Finset.coe_mem] using s.2⟩)
      (fun s => ⟨s.1.map ⟨Fin.castSucc, Fin.castSucc_injective n⟩,
        by simpa [-Finset.coe_mem] using s.2⟩)
  have inj : Function.Injective e := by
    rintro (⟨s, hs⟩|⟨s, hs⟩) (⟨t, ht⟩|⟨t, ht⟩) h
    · simp only [Subtype.mk.injEq, Sum.inl.injEq, e] at h ⊢

      rw [Finset.cons_eq_cons] at h
      simpa [Finset.map_inj] using h
    · simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at hs ht

      simp only [Subtype.mk.injEq, reduceCtorEq, e] at h ⊢
      have m := h ▸ Finset.mem_cons_self _ _
      simp at m
    · simp only [Subtype.mk.injEq, reduceCtorEq, e] at h ⊢
      have m := h.symm ▸ Finset.mem_cons_self _ _
      simp at m
    · simpa [e] using h

  have surj : Function.Surjective e := by
    intro ⟨s, hs⟩
    by_cases h : Fin.last _ ∈ s
    · refine ⟨Sum.inl ⟨(s.erase (Fin.last _)).attach.map ⟨fun x => x.1.castPred (by
        have := x.2
        simp only [Finset.mem_erase, ne_eq] at this
        exact this.1), ?_⟩, ?_⟩, ?_⟩
      · rintro ⟨i, hi⟩ ⟨j, hj⟩
        simp
      · simp only [Finset.mem_powersetCard, Finset.subset_univ, Finset.card_map,
        Finset.card_attach, true_and]
        rw [Finset.card_erase_of_mem h]
        simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at hs
        simp [hs]
      · ext i
        simp only [Finset.cons_eq_insert, Finset.mem_insert, Finset.mem_map, Finset.mem_attach,
          Function.Embedding.coeFn_mk, true_and, Subtype.exists, Finset.mem_erase, ne_eq, e]
        constructor
        · rintro (rfl|⟨_, ⟨⟨j, ⟨h1, h2⟩, rfl⟩, rfl⟩⟩)
          · exact h
          · simpa
        · intro hi
          by_cases i_eq : i = Fin.last _
          · left; exact i_eq
          · right
            exact ⟨i.castPred i_eq, ⟨i, ⟨i_eq, hi⟩, rfl⟩, by simp⟩
    · refine ⟨Sum.inr ⟨s.attach.map ⟨fun x => x.1.castPred (by
        have := x.2
        simp only at this
        intro eq
        rw [eq] at this
        contradiction), ?_⟩, ?_⟩, ?_⟩
      · rintro ⟨i, hi⟩ ⟨j, hj⟩; simp
      · simpa using hs
      · ext x
        simp only [Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk, true_and,
          Subtype.exists, e]
        constructor
        · rintro ⟨i, ⟨i, hi, rfl⟩, rfl⟩
          simpa
        · intro hx
          refine ⟨x.castPred (by aesop), ⟨x, hx, rfl⟩, by simp⟩

  have bij : Function.Bijective e := ⟨inj, surj⟩
  have card_eq := Fintype.card_congr (Equiv.ofBijective e bij)
  simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and, Fintype.card_sum,
    Fintype.card_finset_len, Fintype.card_fin] at card_eq
  exact card_eq.symm


example (m n r : ℕ) : (m + n).choose r = ∑ k ∈ Finset.range (r + 1),
    m.choose k * n.choose (r - k) := by
  classical

  let e₁ :
      Finset.powersetCard r (Finset.univ (α := Fin (m + n))) ≃
      Finset.powersetCard r (Finset.univ (α := Fin m ⊕ Fin n)) :=
    { toFun s := ⟨s.1.map finSumFinEquiv.symm.toEmbedding, by simpa [-Finset.coe_mem] using s.2⟩
      invFun s := ⟨s.1.map finSumFinEquiv.toEmbedding, by simpa [-Finset.coe_mem] using s.2⟩
      left_inv s := by simp [Finset.map_map]
      right_inv s := by simp [Finset.map_map] }

  let e₂ : Finset.powersetCard r (Finset.univ (α := Fin m ⊕ Fin n)) ≃
    { p : Finset (Fin m) × Finset (Fin n) | p.1.card + p.2.card = r } :=
    { toFun s := ⟨⟨Finset.univ.filter fun i => Sum.inl i ∈ s.1,
        Finset.univ.filter fun i => Sum.inr i ∈ s.1⟩, by
          have eq := s.2
          simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at eq
          simp only [Set.mem_setOf_eq]
          conv_rhs => rw [← eq]
          rw [← Finset.card_disjSum]
          rw [Finset.card_equiv]
          · rfl
          · simp⟩
      invFun s := ⟨Finset.disjUnion
          (s.1.1.map ⟨Sum.inl, Sum.inl_injective⟩)
          (s.1.2.map ⟨Sum.inr, Sum.inr_injective⟩)
          (by rw [Finset.disjoint_iff_ne]; aesop), by
        simp only [Set.mem_setOf_eq, Finset.mem_powersetCard, Finset.subset_univ,
          Finset.card_disjUnion, Finset.card_map, true_and]
        exact s.2⟩
      left_inv := by
        rintro ⟨s, hs⟩
        simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and, Finset.disjUnion_eq_union,
          Subtype.mk.injEq] at hs ⊢
        ext x
        aesop
      right_inv := by
        rintro ⟨⟨s, t⟩, h⟩
        simp }

  let e₃ : { p : Finset (Fin m) × Finset (Fin n) | p.1.card + p.2.card = r } ≃
    Σ k : Fin (r + 1), { p : Finset (Fin m) × Finset (Fin n) | p.1.card = k ∧ p.2.card = r - k } :=
    { toFun x := ⟨⟨x.1.1.card, by have : _ = _  := x.2; omega⟩, ⟨⟨x.1.1, x.1.2⟩, rfl, by
        have : _ = _ := x.2; simpa using by omega⟩⟩
      invFun x := ⟨x.2.1, by
        simp only [Set.coe_setOf, Set.mem_setOf_eq, x.2.2.1, x.2.2.2]
        omega⟩
      left_inv := by rintro ⟨⟨s, t⟩, h⟩; simp
      right_inv := by
        rintro ⟨⟨k, hk⟩, ⟨⟨s, t⟩, (rfl : _ = k), h⟩⟩
        simp at h ⊢ }

  let e₄ :
    (Σ k : Fin (r + 1), { p : Finset (Fin m) × Finset (Fin n) | p.1.card = k ∧ p.2.card = r - k }) ≃
    Σ k : Fin (r + 1), Finset.powersetCard k (Finset.univ (α := Fin m)) ×
      Finset.powersetCard (r - k) (Finset.univ (α := Fin n)) :=
    { toFun x := ⟨x.1, ⟨⟨x.2.1.1, by simp [x.2.2.1]⟩, ⟨x.2.1.2, by simp [x.2.2.2]⟩⟩⟩
      invFun x := ⟨x.1, ⟨⟨x.2.1, x.2.2⟩, by simpa [-Finset.coe_mem] using x.2.1.2, by
        simpa [-Finset.coe_mem] using x.2.2.2⟩⟩
      left_inv := by
        rintro ⟨⟨k, hk⟩, ⟨⟨s, t⟩, ⟨(rfl : _ = k), h⟩⟩⟩; simp
      right_inv := by
        rintro ⟨⟨k, hk⟩, ⟨⟨s, hs⟩, ⟨t, ht⟩⟩⟩; simp }

  let e := e₁.trans <| e₂.trans <| e₃.trans e₄
  have := Fintype.card_congr e
  simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and, Fintype.card_finset_len,
    Fintype.card_fin, Fintype.card_sigma, Fintype.card_prod] at this
  rw [this]
  exact Eq.symm (Finset.sum_range fun i ↦ m.choose i * n.choose (r - i))

end comb


namespace gen

open PowerSeries

#check PowerSeries.coeff_C_mul
#check PowerSeries.coeff_X_pow_mul'

lemma eq0 : -(1 - X : PowerSeries ℝ)⁻¹ = .mk fun _ => -1 := by
  rw [neg_eq_iff_eq_neg, eq_comm, PowerSeries.eq_inv_iff_mul_eq_one (by simp), mul_comm]
  ext n
  simp only [mul_neg, sub_mul, one_mul, neg_sub, map_sub, coeff_mk, sub_neg_eq_add, coeff_one]
  rw [show X = X ^ 1 by ring, coeff_X_pow_mul']
  simp only [coeff_mk]
  by_cases n0 : n = 0
  · subst n0; simp
  rw [if_neg n0]
  rw [if_pos (by omega)]
  simp

lemma eq1 : (1 - 2 * X : PowerSeries ℝ)⁻¹ = .mk fun n => 2 ^ n := by
  rw [eq_comm, PowerSeries.eq_inv_iff_mul_eq_one (by simp), mul_comm]
  ext n
  simp only [show (2 : PowerSeries ℝ) = C ℝ 2 from rfl, sub_mul, one_mul, mul_assoc, map_sub,
    coeff_mk, coeff_C_mul, coeff_one]
  rw [show X = X ^ 1 by ring, coeff_X_pow_mul']
  simp only [coeff_mk, mul_ite, mul_zero]
  by_cases n0 : n = 0
  · subst n0; simp
  rw [if_neg n0]
  rw [if_pos (by omega)]
  rw [show (2 : ℝ) ^ n = 2 ^ (n - 1 + 1) by congr 1; omega]
  ring


def f : ℕ → ℤ
| 0 => 1
| 1 => 3
| n + 2 => 3 * f (n + 1) - 2 * f n

@[simp]
lemma f_def (n : ℕ) : f (n + 2) = 3 * f (n + 1) - 2 * f n := by
  rw [f]

def F : PowerSeries ℝ := .mk fun n => f n

lemma F_eqn : F = - (1 - X)⁻¹ + 2 * (1 - 2 * X)⁻¹ := by
  calc F
    _ = (1 - 3 * X + 2 * X ^ 2)⁻¹ := by
      rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp), mul_comm]
      ext n
      simp only [show (3 : PowerSeries ℝ) = C ℝ 3 from rfl,
        show (2 : PowerSeries ℝ) = C ℝ 2 from rfl, add_mul, sub_mul, one_mul, mul_assoc, map_add,
        map_sub, coeff_C_mul, coeff_X_pow_mul', mul_ite, mul_zero, coeff_one]
      rw [show X = X ^ 1 by ring, coeff_X_pow_mul']
      simp only [mul_ite, mul_zero]
      by_cases n0 : n = 0
      · subst n0; simp [F, f]
      rw [if_neg n0]
      by_cases n1 : n = 1
      · subst n1; simp [F, f]
      have h : 2 ≤ n := by omega
      rw [if_pos h, if_pos (by omega)]
      simp only [F, coeff_mk]
      rw [show f n = f (n - 2 + 2) by congr 1; omega, f_def]
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
      rw [show n - 2 + 1 = n - 1 by omega]
      simp
    _ = - (1 - X)⁻¹ + 2 * (1 - 2 * X)⁻¹ := by
      symm
      rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp), add_mul, neg_mul]
      have eq1 : (1 - X : PowerSeries ℝ)⁻¹ * (1 - 3 * X + 2 * X ^ 2) = 1 - 2 * X := by
        rw [mul_comm, eq_comm, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
        ring
      have eq2 : (1 - 2 * X : PowerSeries ℝ)⁻¹ * (1 - 3 * X + 2 * X ^ 2) = 1 - X := by
        rw [mul_comm, eq_comm, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
        ring
      rw [eq1, mul_assoc, eq2]
      ring


lemma f_eq (n : ℕ) : f n = 2 ^ (n + 1) - 1 := by
  have := F_eqn
  have eq := congr($(F_eqn).coeff ℝ n)
  rw [map_add, eq1, eq0, coeff_mk, show (2 : PowerSeries ℝ) = C ℝ 2 by rfl, coeff_C_mul,
    coeff_mk] at eq
  simp only [F, coeff_mk] at eq
  rify
  rw [eq]
  ring

end gen
