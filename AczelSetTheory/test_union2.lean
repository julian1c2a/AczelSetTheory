import AczelSetTheory.CList.ExtEq

namespace CList

lemma mem_union (z a1 b1 : List CList) :
    mem z (mk (a1 ++ b1)) = true ↔ mem z (mk a1) = true ∨ mem z (mk b1) = true := by
  induction a1 with
  | nil =>
    simp [mem_nil]
  | cons x xs ih =>
    simp [mem_cons]
    rw [ih]
    tauto

end CList
