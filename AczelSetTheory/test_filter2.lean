import AczelSetTheory.CList
import AczelSetTheory.HFSets

namespace HFSet

def filterCList (P : HFSet → Prop) [DecidablePred P] (A : CList) : CList :=
  match A with
  | CList.mk xs => CList.mk (xs.filter (fun c => decide (P (Quotient.mk CList.Setoid c))))

theorem filterCList_subset (P : HFSet → Prop) [DecidablePred P] (xs : List CList) :
    CList.subset (filterCList P (CList.mk xs)) (CList.mk xs) = true := by
  induction xs with
  | nil =>
    simp only [filterCList, List.filter_nil, CList.subset_nil]
  | cons z zs ih =>
    simp only [filterCList, List.filter_cons]
    split
    · next hz =>
      simp only [CList.subset_cons, Bool.and_eq_true]
      -- we need to prove: mem z (z :: zs) && subset (filterCList zs) (z :: zs)
      sorry
    · next hz =>
      -- subset (filterCList zs) (z :: zs)
      sorry

theorem filterCList_mem_of_mem (P : HFSet → Prop) [DecidablePred P] (x : CList) (xs : List CList)
    (h : CList.mem x (CList.mk xs) = true) (hP : P (Quotient.mk CList.Setoid x)) :
    CList.mem x (filterCList P (CList.mk xs)) = true := by
  sorry
end HFSet
