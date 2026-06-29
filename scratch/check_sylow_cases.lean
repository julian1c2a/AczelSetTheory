import AczelSetTheory.Algebra.Sylow

namespace HFAlgebra
open Peano Peano.Arith

theorem test (grp' : HFGroup) (p' m : ℕ₀) : True := by
  let P (H : HFSet) : Prop := HFSet.card H ≠ HFSet.card grp'.G ∧ p' ^ (σ m) ∣ HFSet.card H
  haveI : DecidablePred P := inferInstance
  haveI : Decidable (∃ sub : HFSubgroup grp', P sub.H) := inferInstance
  by_cases h_proper : ∃ sub : HFSubgroup grp', HFSet.card sub.H ≠ HFSet.card grp'.G ∧ p' ^ (σ m) ∣ HFSet.card sub.H
  · exact trivial
  · exact trivial

end HFAlgebra

#print axioms HFAlgebra.test
