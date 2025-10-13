import Mathlib

variable (G H : Type) [Group G] [Group H] (φ : G →* H)

def quotKerToImage : G ⧸ φ.ker →* φ.range :=
  QuotientGroup.lift _ φ.rangeRestrict (by simp)

variable (G : Type) [Group G] (H N : Subgroup G) [N.Normal]

open Pointwise

def quotIntersect :
    H ⧸ (N.subgroupOf H) →*
    ((H ⊔ N : Subgroup G) : Type) ⧸ (N.subgroupOf (H ⊔ N)) :=
  QuotientGroup.map _ _ (Subgroup.inclusion (by simp)) (by simp)


variable (G : Type) [Group G] (N : Subgroup G) [N.Normal] (M : Subgroup G) [M.Normal] (h : N ≤ M)

def quotQuotToQuot : (G ⧸ N) ⧸ (Subgroup.map (QuotientGroup.mk' N) M) →* G ⧸ M :=
  QuotientGroup.lift _ _ (by sorry)
