/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import AczelSetTheory.Operations.Cardinal
import AczelSetTheory.Operations.Powerset
import AczelSetTheory.Notation
import AczelSetTheory.Axioms.Succ
import AczelSetTheory.Axioms.Adjunction

open Peano

namespace HFSet

-- ==================================================================
-- Cardinalidad del conjunto vacío
-- ==================================================================

theorem card_empty : card empty = (𝟘 : ℕ₀) := by
  show cardCList CList.empty = (𝟘 : ℕ₀)
  unfold cardCList
  rw [CList.normalize_empty]
  rfl

-- ==================================================================
-- Cardinalidad de insert: carta(insert x A) = σ(card A) when x ∉ A
-- ==================================================================

theorem card_insert (x A : HFSet) (h : x ∉ A) : card (insert x A) = σ (card A) := by
  rcases Quotient.exists_rep x with ⟨xc, rfl⟩
  rcases Quotient.exists_rep A with ⟨a, rfl⟩
  -- Reduce to CList level
  show cardCList (insertCList xc a) = σ (cardCList a)
  -- Get not-mem at CList level: CList.mem xc a = false
  have h_nm : CList.mem xc a = false := by
    cases h_mem : CList.mem xc a with
    | false => rfl
    | true  => exact absurd h_mem h
  -- Get the canonical list xs₀ from normalize a
  cases h_norm : CList.normalize a with | mk xs₀ =>
  -- Properties of xs₀
  have h_sorted := normalize_sorted h_norm
  have h_nodup  := normalize_nodup h_norm
  have h_hall   : ∀ y, PList.Mem y xs₀ → CList.normalize y = y :=
    fun y hy => CList.normalize_fixed_of_mem_normalize a xs₀ h_norm y hy
  -- xc₀ = normalize xc
  let xc₀ := CList.normalize xc
  have hxc₀_norm : CList.normalize xc₀ = xc₀ := CList.normalize_idem xc
  -- xc₀ is not in xs₀ (derived from h_nm via extEq compatibility)
  have h_nm' : CList.mem xc₀ (CList.mk xs₀) = false := by
    rw [Bool.eq_false_iff]
    intro h_pos
    -- xc₀ ∈ xs₀ → xc₀ ∈ a (since extEq a (mk xs₀))
    have h_extEq_a_xs₀ : CList.extEq a (CList.mk xs₀) = true := by
      rw [← h_norm]; exact CList.extEq_normalize a
    have h_xc₀_in_a : CList.mem xc₀ a = true :=
      mem_resp_right xc₀ (CList.mk xs₀) a
        (by rwa [CList.extEq_comm]) h_pos
    -- xc ∈ a (since extEq xc xc₀)
    have h_xc_in_a : CList.mem xc a = true :=
      (mem_resp_left xc xc₀ a (CList.extEq_normalize xc)).mpr h_xc₀_in_a
    exact absurd h_xc_in_a (by simp [h_nm])
  -- Freshness: ∀ y ∈ xs₀, extEq xc₀ y = false
  have h_fresh : ∀ y, PList.Mem y xs₀ → CList.extEq xc₀ y = false := by
    intro y hy
    rw [Bool.eq_false_iff]
    intro h_eq
    have : CList.mem xc₀ (CList.mk xs₀) = true := by
      rw [CList.mem_eq_any]
      exact (PList.any_eq_true _ _).mpr ⟨y, hy, h_eq⟩
    exact absurd this (by simp [h_nm'])
  -- Reduce normalize (insertCList xc a) to normalize (CList.mk (.cons xc₀ xs₀))
  have h_ins_eq : CList.normalize (insertCList xc a) =
      CList.normalize (CList.mk (PList.cons xc₀ xs₀)) := by
    apply CList.normalize_eq_of_extEq
    show CList.extEq (insertCList xc a) (insertCList xc₀ (CList.mk xs₀)) = true
    apply insertCList_extEq
    · exact CList.extEq_normalize xc
    · rw [← h_norm]; exact CList.extEq_normalize a
  -- Apply normalize_cons_fresh
  simp only [cardCList, h_ins_eq,
    CList.normalize_cons_fresh xc₀ xs₀ hxc₀_norm h_sorted h_nodup h_fresh h_hall]
  -- Apply length_orderedInsert_fresh
  rw [CList.length_orderedInsert_fresh xc₀ xs₀ h_fresh, h_norm]

-- ==================================================================
-- Cardinalidad del sucesor: card(succ A) = σ(card A)
-- ==================================================================

/-- El sucesor de Von Neumann `succ A = A ∪ {A}` añade exactamente
    un elemento nuevo (A ∉ A por Fundación), así que su cardinalidad
    es el sucesor de la de A. -/
theorem card_succ (A : HFSet) : card (succ A) = σ (card A) := by
  have h_eq : succ A = insert A A := by
    apply extensionality
    intro x
    rw [mem_succ, mem_insert]
    exact Or.comm
  rw [h_eq]
  exact card_insert A A (not_mem_self A)

-- ==================================================================
-- Cardinalidad del conjunto potencia: card(powerset A) = 2^(card A)
-- ==================================================================

theorem card_powerset (A : HFSet) : card (powerset A) = pow 𝟚 (card A) := by
  rcases Quotient.exists_rep A with ⟨a, rfl⟩
  show cardCList (powersetCList a) = pow 𝟚 (cardCList a)
  -- Get canonical form xs₀
  cases h_norm : CList.normalize a with | mk xs₀ =>
  -- Properties of xs₀
  have h_sorted := normalize_sorted h_norm
  have h_nodup  := normalize_nodup h_norm
  have h_hall   : ∀ y, PList.Mem y xs₀ → CList.normalize y = y :=
    fun y hy => CList.normalize_fixed_of_mem_normalize a xs₀ h_norm y hy
  -- The list of subsets
  let l := (CList.sublists xs₀).map CList.mk
  have h_nodup_l : CList.Nodup l := CList.sublists_nodup_mk xs₀ h_nodup
  have h_norm_l  : CList.normalizePList l = l :=
    normalizePList_id l (fun y hy => by
      rw [PList.Mem_map] at hy
      obtain ⟨zs, hz, rfl⟩ := hy
      exact CList.sublists_norm xs₀ h_sorted h_nodup h_hall zs hz)
  -- RHS: cardCList a = PList.length xs₀
  have h_card_a : cardCList a = PList.length xs₀ := by
    simp only [cardCList, h_norm]
  rw [h_card_a]
  -- LHS: reduce normalize (powersetCList a) to normalize (CList.mk l)
  simp only [cardCList]
  rw [CList.normalize_eq_of_extEq (powersetCList_extEq a (CList.mk xs₀)
        (by rw [← h_norm]; exact CList.extEq_normalize a))]
  -- powersetCList (CList.mk xs₀) = CList.mk l definitionally
  -- normalize (CList.mk l) = CList.mk (insertionSort (dedup (normalizePList l)))
  change PList.length (CList.insertionSort (CList.dedup (CList.normalizePList l))) =
         pow 𝟚 (PList.length xs₀)
  rw [h_norm_l, CList.dedup_id_of_nodup l h_nodup_l,
      CList.length_insertionSort_nodup l h_nodup_l]
  -- PList.length l = PList.length (sublists xs₀)
  simp only [l, PList.length_map]
  exact CList.length_sublists xs₀

-- ==================================================================
-- Cardinalidad cero: card A = 0 ↔ A = ∅
-- ==================================================================

theorem card_eq_zero_iff {A : HFSet} : card A = (𝟘 : ℕ₀) ↔ A = empty := by
  constructor
  · intro h
    rcases Quotient.exists_rep A with ⟨a, rfl⟩
    apply Quotient.sound
    show CList.extEq a CList.empty = true
    -- Reducir a normalize a = normalize empty
    rw [CList.extEq_iff_normalize_eq, CList.normalize_empty]
    -- Goal: CList.normalize a = CList.empty
    cases h_norm : CList.normalize a with | mk xs =>
    have h_len : PList.length xs = (𝟘 : ℕ₀) := by
      have : cardCList a = PList.length xs := by simp only [cardCList, h_norm]
      exact this ▸ h
    have xs_nil : xs = PList.nil := (PList.length_eq_zero_iff_nil xs).mp h_len
    subst xs_nil
    -- CList.normalize a = CList.mk PList.nil = CList.empty definitionally
    rfl
  · intro h
    rw [h, card_empty]

end HFSet
