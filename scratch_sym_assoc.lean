import AczelSetTheory.VN.SymGroupVN

namespace VN

open HFSet
open Peano Peano.FSet Peano.FSetFunction

noncomputable section

theorem funComp_assoc (f g h : HFSet) : f ∘f (g ∘f h) = (f ∘f g) ∘f h := by
  apply extensionality; intro x
  constructor
  · intro hx
    obtain ⟨a, b, c, rfl, hab_gh, hbc_f⟩ := mem_funComp.mp hx
    obtain ⟨a', u, b', h_eq, hau_h, hub_g⟩ := mem_funComp.mp hab_gh
    -- ⟪a,b⟫ = ⟪a',b'⟫ implies a = a' and b = b'
    have h_a_eq : a = a' := (orderedPair_eq_iff a b a' b').mp h_eq |>.1
    have h_b_eq : b = b' := (orderedPair_eq_iff a b a' b').mp h_eq |>.2
    subst h_a_eq
    subst h_b_eq
    apply mem_funComp.mpr
    exact ⟨a', u, c, rfl, hau_h, mem_funComp.mpr ⟨u, b', c, rfl, hub_g, hbc_f⟩⟩
  · intro hx
    obtain ⟨a, u, c, rfl, hau_h, huc_fg⟩ := mem_funComp.mp hx
    obtain ⟨u', b, c', h_eq, hub_g, hbc_f⟩ := mem_funComp.mp huc_fg
    have h_u_eq : u = u' := (orderedPair_eq_iff u c u' c').mp h_eq |>.1
    have h_c_eq : c = c' := (orderedPair_eq_iff u c u' c').mp h_eq |>.2
    subst h_u_eq
    subst h_c_eq
    apply mem_funComp.mpr
    exact ⟨a, b, c', rfl, mem_funComp.mpr ⟨a, u', b, rfl, hau_h, hub_g⟩, hbc_f⟩

end

end VN
