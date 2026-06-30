import AczelSetTheory.Operations.FunctionComp
import AczelSetTheory.Operations.Identity
import AczelSetTheory.Operations.Inverse
import AczelSetTheory.Algebra.Group
import AczelSetTheory.Axioms.Bijection

open HFSet

noncomputable section

def SymHF (A : HFSet) : HFSet :=
  have : DecidablePred (fun f => isBijective f A A) := fun _ => Classical.propDecidable _
  HFSet.sep (HFSet.powerset (HFSet.cartProd A A))
    (fun f => isBijective f A A)

theorem mem_SymHF_iff (A f : HFSet) :
  f ∈ SymHF A ↔ f ⊆ HFSet.cartProd A A ∧ isBijective f A A := by
  have : DecidablePred (fun f => isBijective f A A) := fun _ => Classical.propDecidable _
  rw [SymHF, HFSet.mem_sep_iff, HFSet.mem_powerset_iff]

theorem isBijective_subset_cartProd {f A B : HFSet} (hf : isBijective f A B) :
  f ⊆ HFSet.cartProd A B := by
  intro p hp
  have h_func := isBijective_isFunction hf
  have h_rel := h_func.1
  obtain ⟨a, b, rfl⟩ := h_rel p hp
  have h_dom : a ∈ domain f := mem_domain_of_mem f a b hp
  have h_ran : b ∈ range f := mem_range_of_mem f a b hp
  rw [isBijective_domain_eq hf] at h_dom
  rw [isBijective_range_eq hf] at h_ran
  exact mem_cartProd_pair a b A B h_dom h_ran

theorem funComp_assoc_symm (f g h : HFSet) : (f ∘f g) ∘f h = f ∘f (g ∘f h) := by
  apply extensionality; intro p
  constructor
  · intro hp
    obtain ⟨a, u, c, rfl, hau_h, huc_fg⟩ := mem_funComp.mp hp
    rw [mem_funComp_pair] at huc_fg
    obtain ⟨b, hub_g, hbc_f⟩ := huc_fg
    rw [mem_funComp_pair]
    exact ⟨b, mem_funComp_pair.mpr ⟨u, hau_h, hub_g⟩, hbc_f⟩
  · intro hp
    obtain ⟨a, b, c, rfl, hab_gh, hbc_f⟩ := mem_funComp.mp hp
    rw [mem_funComp_pair] at hab_gh
    obtain ⟨u, hau_h, hub_g⟩ := hab_gh
    rw [mem_funComp_pair]
    exact ⟨u, hau_h, mem_funComp_pair.mpr ⟨b, hub_g, hbc_f⟩⟩

def SymHFGroup (A : HFSet) : HFAlgebra.HFGroup where
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
  op_assoc := fun {f g h} _ _ _ => funComp_assoc_symm f g h
  op_id_left := fun {f} hf => by
    rw [mem_SymHF_iff] at hf
    exact idFunc_funComp_eq (isBijective_isTotalFunction hf.2)
  op_inv_left := fun {f} hf => by
    rw [mem_SymHF_iff] at hf
    exact relInv_funComp_idFunc (isBijective_isTotalFunction hf.2)

end
