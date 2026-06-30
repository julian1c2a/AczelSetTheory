import AczelSetTheory.VN.SymGroupVN

namespace VN

open HFSet
open Peano Peano.FSet Peano.FSetFunction

noncomputable section

theorem mem_SymHF_iff (A f : HFSet) :
  f ∈ SymHF A ↔ f ⊆ HFSet.cartProd A A ∧ isBijective f A A := by
  have : DecidablePred (fun f => isBijective f A A) := fun _ => Classical.propDecidable _
  rw [SymHF, HFSet.mem_sep_iff, HFSet.mem_powerset_iff]

theorem isBijective_subset_cartProd {f A B : HFSet} (hf : isBijective f A B) :
  f ⊆ HFSet.cartProd A B := by
  intro p hp
  have h_func := isBijective_isFunction hf
  -- si p ∈ f, y f es función, p = ⟪a, b⟫ con a ∈ A, b ∈ B.
  have h_rel := h_func.1
  obtain ⟨a, b, rfl⟩ := h_rel p hp
  have h_dom : a ∈ domain f := mem_domain_of_mem f a b hp
  have h_ran : b ∈ range f := mem_range_of_mem f a b hp
  rw [isBijective_domain_eq hf] at h_dom
  rw [isBijective_range_eq hf] at h_ran
  exact mem_cartProd_pair a b A B h_dom h_ran

def SymHFGroup_test (A : HFSet) : HFAlgebra.HFGroup where
  G := SymHF A
  op := fun f g => f ∘f g
  e := HFSet.idFunc A
  inv := fun f => f⁻¹ᵣ
  e_mem := by
    rw [mem_SymHF_iff]
    exact ⟨isBijective_subset_cartProd isBijective_idFunc, isBijective_idFunc⟩
  op_closed := fun {f g} hf hg => by
    rw [mem_SymHF_iff] at hf hg ⊢
    have h_bij := isBijective_funComp hf.2 hg.2
    exact ⟨isBijective_subset_cartProd h_bij, h_bij⟩
  inv_closed := fun {f} hf => by
    rw [mem_SymHF_iff] at hf ⊢
    have h_bij := isBijective_relInv hf.2
    exact ⟨isBijective_subset_cartProd h_bij, h_bij⟩
  op_assoc := fun {f g h} _ _ _ => by
    exact funComp_assoc (f:=f) (g:=g) (h:=h)
  op_id_left := fun {f} hf => by
    rw [mem_SymHF_iff] at hf
    exact idFunc_funComp_eq (isBijective_isTotalFunction hf.2)
  op_inv_left := fun {f} hf => by
    rw [mem_SymHF_iff] at hf
    exact relInv_funComp_idFunc (isBijective_isTotalFunction hf.2)

end

end VN
