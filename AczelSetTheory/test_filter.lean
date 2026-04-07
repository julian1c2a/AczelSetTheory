import AczelSetTheory.CList
import AczelSetTheory.HFSets

namespace HFSet

def filterCList (P : HFSet → Prop) [DecidablePred P] (A : CList) : CList :=
  match A with
  | CList.mk xs => CList.mk (xs.filter (fun c => decide (P (Quotient.mk CList.Setoid c))))

-- Demostrar que el filtro preserva subset
theorem filterCList_subset_of_subset (P : HFSet → Prop) [DecidablePred P]
    (A B : CList) (h : CList.subset A B = true) :
    CList.subset (filterCList P A) (filterCList P B) = true := by
  sorry

end HFSet
