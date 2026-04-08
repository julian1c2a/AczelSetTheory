import AczelSetTheory.HFSets

namespace HFSet

/-- La membresía en HFSet es decidible (heredada de CList.mem : Bool). -/
instance mem_decidable (x A : HFSet) : Decidable (x ∈ A) :=
  Quotient.recOnSubsingleton₂ x A fun xc ac =>
    show Decidable (CList.mem xc ac = true) from
    match CList.mem xc ac with
    | true  => isTrue rfl
    | false => isFalse nofun

end HFSet
