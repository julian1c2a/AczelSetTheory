import AczelSetTheory.Axioms.Separation

namespace HFSet

-- Is x ∈ B decidable? Let's check with an instance.
instance instDecidableMem (x A : HFSet) : Decidable (x ∈ A) := by
  -- Not sure if it's already there
  sorry

def inter (A B : HFSet) : HFSet :=
  sep A (fun x => x ∈ B)

def setminus (A B : HFSet) : HFSet :=
  sep A (fun x => ¬(x ∈ B))

end HFSet
