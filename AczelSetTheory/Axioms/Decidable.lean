import AczelSetTheory.HFSets
import AczelSetTheory.Axioms.Foundation

namespace HFSet

/-- La membresía en HFSet es decidible (heredada de CList.mem : Bool). -/
instance mem_decidable
  (x A : HFSet) :
    Decidable (x ∈ A)
      :=
  Quotient.recOnSubsingleton₂ x A fun xc ac =>
    show Decidable (CList.mem xc ac = true) from
    match CList.mem xc ac with
    | true  => isTrue rfl
    | false => isFalse nofun

/-- Cuantificador existencial acotado decidible para HFSet. -/
instance existsMem_decidable
  (A : HFSet) (P : HFSet → Prop) [DecidablePred P] :
    Decidable (∃ x, x ∈ A ∧ P x)
      :=
  Quotient.recOnSubsingleton A fun ac =>
    match ac with
    | CList.mk xs =>
      let f : CList → Bool := fun c => decide (P (Quotient.mk CList.Setoid c))
      if h : xs.any f = true
      then isTrue (by
        rw [List.any_eq_true] at h
        obtain ⟨c, hc_list, hc_p⟩ := h
        exact ⟨Quotient.mk CList.Setoid c,
               CList.mem_of_list_mem c xs hc_list,
               of_decide_eq_true hc_p⟩)
      else isFalse (by
        intro ⟨x, hx_mem, hx_p⟩
        rcases Quotient.exists_rep x with ⟨xc, rfl⟩
        obtain ⟨y, hy_list, hy_eq⟩ := CList.mem_exists_list_mem xc xs hx_mem
        have hxy : Quotient.mk CList.Setoid xc = Quotient.mk CList.Setoid y :=
          Quotient.sound hy_eq
        rw [hxy] at hx_p
        have hfy : f y = true := decide_eq_true hx_p
        exact h (List.any_eq_true.mpr ⟨y, hy_list, hfy⟩))

end HFSet
