import AczelSetTheory.Algebra.Group
import AczelSetTheory.Axioms.Separation
import AczelSetTheory.Axioms.Decidable
import AczelSetTheory.Axioms.Powerset

namespace HFAlgebra

def isSubgroupProp (grp : HFGroup) (H : HFSet) : Prop :=
  (∀ x ∈ H, x ∈ grp.G) ∧
  grp.e ∈ H ∧
  (∀ x ∈ H, ∀ y ∈ H, grp.op x y ∈ H) ∧
  (∀ x ∈ H, grp.inv x ∈ H)

instance isSubgroupProp_decidable (grp : HFGroup) (H : HFSet) :
    Decidable (isSubgroupProp grp H) :=
  haveI _inst1 : Decidable (∀ x ∈ H, x ∈ grp.G) := inferInstance
  haveI _inst2 : Decidable (grp.e ∈ H) := inferInstance
  haveI _inst3 : Decidable (∀ x ∈ H, ∀ y ∈ H, grp.op x y ∈ H) := inferInstance
  haveI _inst4 : Decidable (∀ x ∈ H, grp.inv x ∈ H) := inferInstance
  instDecidableAnd

theorem exists_subgroup_iff_powerset (grp : HFGroup) (P : HFSet → Prop) :
    (∃ sub : HFSubgroup grp, P sub.H) ↔
    (∃ H ∈ HFSet.powerset grp.G, isSubgroupProp grp H ∧ P H) := by
  constructor
  · intro ⟨sub, hP⟩
    refine ⟨sub.H, ?_, ?_, hP⟩
    · rw [HFSet.mem_powerset]
      intro x hx
      exact sub.H_sub hx
    · exact ⟨fun hx => sub.H_sub hx, sub.e_mem, fun x hx y hy => sub.op_closed hx hy, fun x hx => sub.inv_closed hx⟩
  · intro ⟨H, hpow, hsub, hP⟩
    have hsubset : ∀ x ∈ H, x ∈ grp.G := by
      intro x hx
      rw [HFSet.mem_powerset] at hpow
      exact hpow x hx
    let sub : HFSubgroup grp := {
      H := H
      H_sub := fun {x} hx => hsubset x hx
      e_mem := hsub.2.1
      op_closed := fun {a b} ha hb => hsub.2.2.1 _ ha _ hb
      inv_closed := fun {a} ha => hsub.2.2.2 _ ha
    }
    exact ⟨sub, hP⟩

instance existsSubgroup_decidable (grp : HFGroup) (P : HFSet → Prop) [DecidablePred P] :
    Decidable (∃ sub : HFSubgroup grp, P sub.H) :=
  decidable_of_iff (∃ H ∈ HFSet.powerset grp.G, isSubgroupProp grp H ∧ P H)
    (exists_subgroup_iff_powerset grp P).symm

end HFAlgebra
