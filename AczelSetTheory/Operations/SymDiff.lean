import AczelSetTheory.Operations.Setminus
import AczelSetTheory.Operations.Union

namespace HFSet

/-- Diferencia simétrica a nivel CList: A △ B = (A \ B) ∪ (B \ A) -/
def symDiffCList (a b : CList) : CList :=
  CList.union (setminusCList a b) (setminusCList b a)

theorem symDiffCList_extEq
  (a₁ a₂ b₁ b₂ : CList)
  (ha : CList.extEq a₁ a₂ = true)
  (hb : CList.extEq b₁ b₂ = true) :
    CList.extEq (symDiffCList a₁ b₁) (symDiffCList a₂ b₂) = true := by
  unfold symDiffCList
  exact CList.union_extEq
    (setminusCList a₁ b₁) (setminusCList a₂ b₂)
    (setminusCList b₁ a₁) (setminusCList b₂ a₂)
    (setminusCList_extEq_extEq a₁ a₂ b₁ b₂ ha hb)
    (setminusCList_extEq_extEq b₁ b₂ a₁ a₂ hb ha)

/-- Operación Diferencia Simétrica (A △ B) para HFSet -/
def symDiff (A B : HFSet) : HFSet :=
  Quotient.liftOn₂ A B
    (fun a b => Quotient.mk CList.Setoid (symDiffCList a b))
    (fun a₁ b₁ a₂ b₂ ha hb => by
      apply Quotient.sound
      exact symDiffCList_extEq a₁ a₂ b₁ b₂ ha hb)

end HFSet
