import AczelSetTheory.CList.ExtEq

namespace CList

def union (A B : CList) : CList :=
  match A, B with
  | mk xs, mk ys => mk (xs ++ ys)

theorem mem_union (z A B : CList) :
    mem z (union A B) = true ↔ mem z A = true ∨ mem z B = true := by
  cases A with | mk xs =>
  cases B with | mk ys =>
  induction xs with
  | nil =>
    simp only [union, List.nil_append, mem_nil, Bool.false_or, false_or]
  | cons x xs ih =>
    simp only [union, List.cons_append, mem_cons, Bool.or_eq_true]
    rw [ih]
    -- (extEq z x ∨ mem z xs) ∨ mem z ys ↔ extEq z x ∨ (mem z xs ∨ mem z ys)
    tauto

theorem subset_union_left (A B : CList) :
    subset A (union A B) = true := by
  cases A with | mk xs =>
  cases B with | mk ys =>
  induction xs with
  | nil => simp [subset_nil]
  | cons x xs ih =>
    simp only [union, List.cons_append, subset_cons, Bool.and_eq_true]
    have hz : mem x (union (mk (x :: xs)) (mk ys)) = true := by
      rw [mem_union]
      simp [mem_cons, extEq_refl]
    exact ⟨hz, subset_mono _ x _ ih⟩

-- Wait, subset_mono changes: subset A B -> subset A (insert x B). We need to prove `subset A (union A B)`.
-- Let's just use `subset_iff_forall_mem_clist` which we have in HFSets!
-- Wait, `subset_iff` is in HFSets. Let's move it to `CList.ExtEq` or just prove it simply.

end CList
