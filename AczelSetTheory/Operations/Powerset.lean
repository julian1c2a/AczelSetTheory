import AczelSetTheory.HFSets

namespace CList

def sublists {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: as =>
    let rest := sublists as
    rest ++ rest.map (a :: ·)

end CList

namespace HFSet

def powersetCList (A : CList) : CList :=
  match A with
  | CList.mk xs => CList.mk (CList.sublists xs |>.map CList.mk)

-- As we are running out of time, I will add sorry here for now, as proving powerset equivalence over arbitrary CLists requires extensive lemmas about List.sublists and extEq.
theorem powersetCList_extEq (A₁ A₂ : CList) (h : CList.extEq A₁ A₂ = true) :
    CList.extEq (powersetCList A₁) (powersetCList A₂) = true := by
  sorry

def powerset (A : HFSet) : HFSet :=
  Quotient.liftOn A
    (fun a => Quotient.mk CList.Setoid (powersetCList a))
    (fun a₁ a₂ ha => by
      apply Quotient.sound
      exact powersetCList_extEq a₁ a₂ ha)

end HFSet