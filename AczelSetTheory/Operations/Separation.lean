import AczelSetTheory.HFSets
import AczelSetTheory.CList.Filter

namespace HFSet

/-- Filtra una lista nativa evaluando la proposición P bajada a Booleano en cada elemento -/
def filterCList
  (P : HFSet → Prop) [DecidablePred P] (A : CList) :
    CList
      :=
  match A with
  | CList.mk xs => CList.mk (xs.filter (fun c => decide (P (Quotient.mk CList.Setoid c))))

theorem filterCList_extEq_extEq
  (P : HFSet → Prop) [DecidablePred P] (A₁ A₂ : CList) (hA : CList.extEq A₁ A₂ = true) :
    CList.extEq (filterCList P A₁) (filterCList P A₂) = true
      := by
  cases A₁ with | mk xs₁ =>
  cases A₂ with | mk xs₂ =>
  have hP_resp : CList.P_respects (fun c => decide (P (Quotient.mk CList.Setoid c))) := by
    intro x y heq
    have hQuot : Quotient.mk CList.Setoid x = Quotient.mk CList.Setoid y := Quotient.sound heq
    simp only [hQuot]
  exact CList.extEq_filter (fun c => decide (P (Quotient.mk CList.Setoid c))) hP_resp xs₁ xs₂ hA

/-- Axioma de Separación (Subconjuntos) -/
def sep
  (A : HFSet) (P : HFSet → Prop) [DecidablePred P] :
    HFSet
      :=
  Quotient.liftOn A
    (fun a => Quotient.mk CList.Setoid (filterCList P a))
    (fun A₁ A₂ hA => by
      apply Quotient.sound
      exact filterCList_extEq_extEq P A₁ A₂ hA)

end HFSet
