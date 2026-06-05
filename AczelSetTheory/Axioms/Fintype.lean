/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Axioms/Fintype.lean
-- Tipos finitos y conjuntos finitos propios del proyecto (sin Mathlib).
--
-- Públicos:
--   Finset α              : subconjunto finito de α (val : List α, nodup)
--   Fintype α             : clase de tipos finitos (elems : List α, complete)
--   HFSet.toList A        : lista de los elementos de A (sin duplicados)
--   HFSet.mem_toList      : x ∈ A.toList ↔ x ∈ A
--   HFSet.nodup_toList    : A.toList.Nodup
--   HFSet.toFinset A      : Finset HFSet de los elementos de A
--   HFSet.mem_toFinset    : x ∈ A.toFinset ↔ x ∈ A
--   HFSet.membership_fintype : Fintype {x // x ∈ A}

import AczelSetTheory.Axioms.OrdinalNat
import AczelSetTheory.PList.Lemmas

-- ==================================================================
-- Finset: subconjunto finito (análogo local, sin Mathlib)
-- ==================================================================

/-- Subconjunto finito de un tipo: lista de valores sin repetición. -/
structure Finset (α : Type) where
  val   : List α
  nodup : val.Nodup

namespace Finset

instance {α} : Membership α (Finset α) where
  mem s x := x ∈ s.val

end Finset

-- ==================================================================
-- Fintype: clase de tipos finitos (análogo local, sin Mathlib)
-- ==================================================================

/-- Un tipo finito tiene una lista explícita de todos sus elementos. -/
class Fintype (α : Type) where
  elems    : List α
  complete : ∀ x : α, x ∈ elems

-- ==================================================================
-- HFSet.toList y lemas de membresía y nodup
-- ==================================================================

namespace HFSet

open CList

-- ------------------------------------------------------------------
-- Función auxiliar: CList → List HFSet
-- ------------------------------------------------------------------

/-- Convierte la forma normal de una CList en lista de HFSets. -/
private def reprToList : CList → List HFSet
  | .mk xs => xs.toList.map (Quotient.mk CList.Setoid)

/-- Lista canónica de los elementos de A (vía representante normalizado). -/
def toList (A : HFSet) : List HFSet :=
  reprToList A.repr

-- ------------------------------------------------------------------
-- Lemas auxiliares privados
-- ------------------------------------------------------------------

/-- PList.Mem ↔ List.mem vía PList.toList. -/
private theorem plist_Mem_iff_list_mem {α : Type} (z : α) (xs : PList α) :
    PList.Mem z xs ↔ z ∈ xs.toList := by
  induction xs with
  | nil  => simp [PList.not_mem_nil]
  | cons h t ih =>
    simp only [PList.toList_cons, List.mem_cons, PList.Mem_cons_iff, ih]

/-- CList.mem x (.mk ys) = PList.any (extEq x) ys. -/
private theorem clist_mem_eq_plist_any (x : CList) (ys : PList CList) :
    CList.mem x (.mk ys) = PList.any (fun z => CList.extEq x z) ys := by
  induction ys with
  | nil      => simp [CList.mem_nil, PList.any_nil]
  | cons y t ih => rw [CList.mem_cons, PList.any_cons, ih]

-- ------------------------------------------------------------------
-- mem_toList
-- ------------------------------------------------------------------

theorem mem_toList (x A : HFSet) : x ∈ A.toList ↔ x ∈ A := by
  rcases Quotient.exists_rep A with ⟨ac, rfl⟩
  rcases Quotient.exists_rep x with ⟨xc, rfl⟩
  -- Reescribir toList con have+rfl (evita re-elab con Quotient.lift_mk)
  have h_toList : HFSet.toList (Quotient.mk CList.Setoid ac) =
      reprToList (CList.normalize ac) := rfl
  rw [h_toList]
  -- Extraer los hijos de normalize ac
  obtain ⟨xs, hxs⟩ : ∃ xs, CList.normalize ac = .mk xs := by
    cases h : CList.normalize ac with | mk ys => exact ⟨ys, rfl⟩
  rw [hxs]
  simp only [reprToList, List.mem_map]
  -- El RHS se reduce definitoriamente a CList.mem xc ac = true
  constructor
  · -- → : ∃ z ∈ xs.toList, ⟦z⟧ = ⟦xc⟧  →  mem xc ac = true
    rintro ⟨z, hz_list, hz_eq⟩
    show CList.mem xc ac = true
    -- hz_eq : ⟦z⟧ = ⟦xc⟧  →  extEq z xc = true
    have hzx : CList.extEq z xc = true := Quotient.exact hz_eq
    -- z ∈ xs (como PList.Mem)
    have hz_mem : PList.Mem z xs := (plist_Mem_iff_list_mem z xs).mpr hz_list
    -- mem z (.mk xs) = true
    have hm_z : CList.mem z (.mk xs) = true := by
      rw [clist_mem_eq_plist_any]
      exact (PList.any_eq_true _ _).mpr ⟨z, hz_mem, CList.extEq_refl z⟩
    -- mem xc (.mk xs) = true (via mem_resp_left z xc)
    have hm_xc : CList.mem xc (.mk xs) = true :=
      (mem_resp_left z xc (.mk xs) hzx).mp hm_z
    -- mem xc (normalize ac) = true
    rw [← hxs] at hm_xc
    -- mem xc ac = true (vía extEq_normalize en sentido inverso)
    exact mem_resp_right xc (CList.normalize ac) ac
      (by rw [CList.extEq_comm]; exact CList.extEq_normalize ac) hm_xc
  · -- ← : mem xc ac = true  →  ∃ z ∈ xs.toList, ⟦z⟧ = ⟦xc⟧
    intro hm
    have hm' : CList.mem xc ac = true := hm
    -- mem xc (normalize ac) = true
    have hm_norm : CList.mem xc (CList.normalize ac) = true :=
      mem_resp_right xc ac (CList.normalize ac) (CList.extEq_normalize ac) hm'
    rw [hxs, clist_mem_eq_plist_any] at hm_norm
    obtain ⟨z, hz_mem, hxz⟩ := (PList.any_eq_true _ _).mp hm_norm
    exact ⟨z, (plist_Mem_iff_list_mem z xs).mp hz_mem, (Quotient.sound hxz).symm⟩

-- ------------------------------------------------------------------
-- nodup_toList
-- ------------------------------------------------------------------

/-- Si CList.Nodup ys, entonces (ys.toList.map ⟦·⟧).Nodup. -/
private theorem nodup_map_quotient (ys : PList CList) :
    CList.Nodup ys → (ys.toList.map (Quotient.mk CList.Setoid)).Nodup := by
  induction ys with
  | nil  => intro _; exact List.nodup_nil
  | cons y t ih =>
    intro h
    -- Descomponer CList.Nodup (.cons y t)
    have hfresh : ∀ z, PList.Mem z t → CList.extEq y z = false := h.1
    have ht_nodup : CList.Nodup t := h.2
    simp only [PList.toList_cons, List.map_cons, List.nodup_cons]
    refine ⟨?_, ih ht_nodup⟩
    -- Probar ⟦y⟧ ∉ t.toList.map ⟦·⟧
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨z, hz_list, hz_eq⟩ := hmem
    -- hz_eq : ⟦z⟧ = ⟦y⟧  →  extEq z y = true
    have hext_true : CList.extEq z y = true := Quotient.exact hz_eq
    -- z ∈ t  →  extEq y z = false
    have hz_mem_t : PList.Mem z t := (plist_Mem_iff_list_mem z t).mpr hz_list
    have hext_false : CList.extEq y z = false := hfresh z hz_mem_t
    -- extEq z y = extEq y z (por extEq_comm) = false  →  contradicción
    rw [CList.extEq_comm] at hext_true
    rw [hext_false] at hext_true
    exact absurd hext_true (by decide)

theorem nodup_toList (A : HFSet) : A.toList.Nodup := by
  rcases Quotient.exists_rep A with ⟨ac, rfl⟩
  show (reprToList (CList.normalize ac)).Nodup
  obtain ⟨xs, hxs⟩ : ∃ xs, CList.normalize ac = .mk xs := by
    cases h : CList.normalize ac with | mk ys => exact ⟨ys, rfl⟩
  rw [hxs]
  exact nodup_map_quotient xs (normalize_nodup hxs)

-- ==================================================================
-- HFSet.toFinset y mem_toFinset
-- ==================================================================

/-- El Finset de los elementos de A. -/
def toFinset (A : HFSet) : Finset HFSet :=
  ⟨A.toList, A.nodup_toList⟩

theorem mem_toFinset (x A : HFSet) : x ∈ A.toFinset ↔ x ∈ A := by
  show x ∈ A.toList ↔ x ∈ A
  exact mem_toList x A

-- ==================================================================
-- Instancia Fintype {x // x ∈ A}
-- ==================================================================

instance membership_fintype (A : HFSet) : Fintype {x // x ∈ A} where
  elems := A.toList.filterMap (fun y =>
    if hy : y ∈ A then some ⟨y, hy⟩ else none)
  complete := fun ⟨x, hx⟩ => by
    rw [List.mem_filterMap]
    exact ⟨x, (mem_toList x A).mpr hx, by rw [dif_pos hx]⟩

end HFSet
