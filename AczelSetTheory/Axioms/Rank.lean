/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Axioms/Rank.lean
-- Rango de Von Neumann de un conjunto finito hereditario.
--
-- Público:
--   rank        : HFSet → ℕ₀        -- función de rango
--   rank_empty  : rank ∅ = 𝟘
--   rank_insert : x ∉ A → rank (insert x A) = max (σ (rank x)) (rank A)
--   mem_rank_lt : ∀ a b, a ∈ b → rank a < rank b
--   mem_wf      : WellFounded (· ∈ · : HFSet → HFSet → Prop)
-- Ver también: VN/RankVN.lean para rank_vN

import AczelSetTheory.Operations.Cardinal
import AczelSetTheory.Axioms.Adjunction
import AczelSetTheory.Axioms.Induction

open Peano

namespace HFSet

-- ==================================================================
-- Implementación interna por recursión mutual estructural
-- ==================================================================

mutual
  private def rankNorm : CList → ℕ₀
    | .mk xs => rankNormList xs
  private def rankNormList : PList CList → ℕ₀
    | .nil        => (𝟘 : ℕ₀)
    | .cons x rest => max (σ (rankNorm x)) (rankNormList rest)
end

private def rankCList (a : CList) : ℕ₀ := rankNorm (CList.normalize a)

private theorem rankCList_congr {A B : CList} (h : CList.extEq A B = true) :
    rankCList A = rankCList B := by
  simp only [rankCList, CList.normalize_eq_of_extEq h]

-- ==================================================================
-- Definición pública: rank : HFSet → ℕ₀
-- ==================================================================

def rank (A : HFSet) : ℕ₀ :=
  Quotient.liftOn A rankCList (fun _ _ h => rankCList_congr h)

-- ==================================================================
-- rank del conjunto vacío
-- ==================================================================

theorem rank_empty : rank empty = (𝟘 : ℕ₀) := by
  show rankCList CList.empty = (𝟘 : ℕ₀)
  simp only [rankCList, CList.normalize_empty]
  rfl

-- ==================================================================
-- Lema auxiliar: rankNormList conmuta con orderedInsert (caso fresh)
-- ==================================================================

private theorem rankNormList_orderedInsert_fresh (x : CList) (xs : PList CList)
    (hx : ∀ y, PList.Mem y xs → CList.extEq x y = false) :
    rankNormList (CList.orderedInsert x xs) =
      max (σ (rankNorm x)) (rankNormList xs) := by
  induction xs with
  | nil =>
    simp only [CList.orderedInsert, rankNormList]
  | cons z zs ih =>
    have hxz : CList.extEq x z = false := hx z PList.Mem.head
    simp only [CList.orderedInsert]
    by_cases hlt : CList.lt x z = true
    · rw [if_pos hlt]; rfl
    · rw [if_neg hlt, if_neg (Bool.eq_false_iff.mp hxz)]
      simp only [rankNormList]
      rw [ih (fun w hw => hx w (PList.Mem.tail hw))]
      rw [← max_assoc, max_comm (σ (rankNorm z)) (σ (rankNorm x)), max_assoc]

-- ==================================================================
-- rank de insert: rank(insert x A) = max(σ(rank x), rank A) si x ∉ A
-- ==================================================================

private theorem rankCList_insert (xc : CList) (a : CList)
    (h_nm : CList.mem xc a = false) :
    rankCList (insertCList xc a) = max (σ (rankCList xc)) (rankCList a) := by
  cases h_norm : CList.normalize a with | mk xs₀ =>
  have h_sorted := normalize_sorted h_norm
  have h_nodup  := normalize_nodup h_norm
  have h_hall : ∀ y, PList.Mem y xs₀ → CList.normalize y = y :=
    fun y hy => CList.normalize_fixed_of_mem_normalize a xs₀ h_norm y hy
  let xc₀ := CList.normalize xc
  have hxc₀_norm : CList.normalize xc₀ = xc₀ := CList.normalize_idem xc
  have h_nm' : CList.mem xc₀ (CList.mk xs₀) = false := by
    rw [Bool.eq_false_iff]
    intro h_pos
    have h_xc₀_in_a : CList.mem xc₀ a = true :=
      mem_resp_right xc₀ (CList.mk xs₀) a
        (by rw [CList.extEq_comm]; rw [← h_norm]; exact CList.extEq_normalize a) h_pos
    have h_xc_in_a : CList.mem xc a = true :=
      (mem_resp_left xc xc₀ a (CList.extEq_normalize xc)).mpr h_xc₀_in_a
    exact absurd h_xc_in_a (by simp [h_nm])
  have h_fresh : ∀ y, PList.Mem y xs₀ → CList.extEq xc₀ y = false := by
    intro y hy
    rw [Bool.eq_false_iff]
    intro h_eq
    have : CList.mem xc₀ (CList.mk xs₀) = true := by
      rw [CList.mem_eq_any]
      exact (PList.any_eq_true _ _).mpr ⟨y, hy, h_eq⟩
    exact absurd this (by simp [h_nm'])
  have h_ins_eq : CList.normalize (insertCList xc a) =
      CList.normalize (CList.mk (PList.cons xc₀ xs₀)) := by
    apply CList.normalize_eq_of_extEq
    show CList.extEq (insertCList xc a) (insertCList xc₀ (CList.mk xs₀)) = true
    apply insertCList_extEq
    · exact CList.extEq_normalize xc
    · rw [← h_norm]; exact CList.extEq_normalize a
  simp only [rankCList, h_ins_eq,
    CList.normalize_cons_fresh xc₀ xs₀ hxc₀_norm h_sorted h_nodup h_fresh h_hall, h_norm]
  show rankNormList (CList.orderedInsert xc₀ xs₀) = max (σ (rankNorm xc₀)) (rankNormList xs₀)
  exact rankNormList_orderedInsert_fresh xc₀ xs₀ h_fresh

theorem rank_insert (x A : HFSet) (h : x ∉ A) :
    rank (insert x A) = max (σ (rank x)) (rank A) := by
  rcases Quotient.exists_rep x with ⟨xc, rfl⟩
  rcases Quotient.exists_rep A with ⟨a, rfl⟩
  show rankCList (insertCList xc a) = max (σ (rankCList xc)) (rankCList a)
  have h_nm : CList.mem xc a = false := by
    cases h_mem : CList.mem xc a with
    | false => rfl
    | true  => exact absurd h_mem h
  exact rankCList_insert xc a h_nm

-- ==================================================================
-- Lema auxiliar: insert b A = A cuando b ∈ A
-- ==================================================================

private theorem insert_mem_eq' {b A : HFSet} (h : b ∈ A) : insert b A = A :=
  extensionality _ _ fun x =>
    ⟨fun hx => by
       rcases (mem_insert x b A).mp hx with rfl | hxA
       · exact h
       · exact hxA,
     fun hx => (mem_insert x b A).mpr (Or.inr hx)⟩

-- ==================================================================
-- mem_rank_lt: si a ∈ b entonces rank a < rank b
-- ==================================================================

theorem mem_rank_lt : ∀ (a b : HFSet), a ∈ b → rank a < rank b := by
  have key : ∀ b a, a ∈ b → rank a < rank b :=
    eps_induction (fun b => ∀ a, a ∈ b → rank a < rank b)
      (fun a ha => absurd ha (not_mem_empty a))
      (fun A x ih a ha => by
        rcases (mem_insert a x A).mp ha with hax | haA
        · rw [hax]
          by_cases hxA : x ∈ A
          · rw [insert_mem_eq' hxA]; exact ih x hxA
          · rw [rank_insert x A hxA]
            exact lt_of_lt_of_le (lt_self_σ_self (rank x)) (le_max_left _ _)
        · have h_rankA := ih a haA
          by_cases hxA : x ∈ A
          · rw [insert_mem_eq' hxA]; exact h_rankA
          · rw [rank_insert x A hxA]
            exact lt_of_lt_of_le h_rankA (le_max_right _ _))
  intro a b h
  exact key b a h

-- ==================================================================
-- WellFounded de ∈ en HFSet, vía Subrelation.wf
-- ==================================================================

instance mem_wf : WellFounded (· ∈ · : HFSet → HFSet → Prop) :=
  Subrelation.wf (fun {a b} h => mem_rank_lt a b h) (InvImage.wf rank well_founded_lt)

end HFSet
