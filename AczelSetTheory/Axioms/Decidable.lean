/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import AczelSetTheory.HFSets
import AczelSetTheory.Axioms.Foundation

namespace HFSet

/-- La membresía en HFSet es decidible (heredada de CList.mem : Bool). -/
instance mem_decidable
    (x A : HFSet) :
    Decidable (x ∈ A) :=
  Quotient.recOnSubsingleton₂ x A fun xc ac =>
    show Decidable (CList.mem xc ac = true) from
    match CList.mem xc ac with
    | true  => isTrue rfl
    | false => isFalse nofun

/-- Cuantificador existencial acotado decidible para HFSet. -/
instance existsMem_decidable
    (A : HFSet) (P : HFSet → Prop) [DecidablePred P] :
    Decidable (∃ x, x ∈ A ∧ P x) :=
  Quotient.recOnSubsingleton A fun ac =>
    match ac with
    | CList.mk xs =>
      let f : CList → Bool := fun c => decide (P (Quotient.mk CList.Setoid c))
      if h : PList.any f xs = true
      then isTrue (by
        rw [PList.any_eq_true] at h
        obtain ⟨c, hc_mem, hc_p⟩ := h
        exact ⟨Quotient.mk CList.Setoid c,
               CList.mem_of_plist_mem c xs hc_mem,
               of_decide_eq_true hc_p⟩)
      else isFalse (by
        intro ⟨x, hx_mem, hx_p⟩
        rcases Quotient.exists_rep x with ⟨xc, rfl⟩
        obtain ⟨y, hy_mem, hy_eq⟩ := CList.mem_exists_plist_mem xc xs hx_mem
        have hxy : Quotient.mk CList.Setoid xc = Quotient.mk CList.Setoid y :=
          Quotient.sound hy_eq
        rw [hxy] at hx_p
        have hfy : f y = true := decide_eq_true hx_p
        exact h ((PList.any_eq_true _ _).mpr ⟨y, hy_mem, hfy⟩))

end HFSet
