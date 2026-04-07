import AczelSetTheory.CList.ExtEq

namespace CList

-- UNION
def union (A B : CList) : CList :=
  match A, B with
  | mk xs, mk ys => mk (xs ++ ys)

lemma mem_union (z A B : CList) :
    mem z (union A B) = true ↔ mem z A = true ∨ mem z B = true := by
  cases A with | mk xs =>
  cases B with | mk ys =>
  induction xs with
  | nil => simp [union, mem_nil]
  | cons x xs ih =>
    simp [union, mem_cons]
    rw [ih]
    tauto

-- BIG UNION
def sUnion (A : CList) : CList :=
  match A with
  | mk xs => mk (xs.bind (fun (mk ys) => ys))

lemma mem_sUnion (z A : CList) :
    mem z (sUnion A) = true ↔ ∃ Y, mem Y A = true ∧ mem z Y = true := by
  cases A with | mk xs =>
  induction xs with
  | nil =>
    simp [sUnion, mem_nil]
  | cons x xs ih =>
    cases x with | mk y =>
    simp [sUnion, mem_cons]
    rw [mem_union z (mk y) (sUnion (mk xs))] -- We can rewrite using a similar lemma for bind
    -- mem z (mk (y ++ xs.bind ...)) ↔ mem z (mk y) ∨ mem z (mk (xs.bind ...))
  sorry

-- DIFF
def diff (A B : CList) : CList :=
  match A with
  | mk xs => mk (xs.filter (fun c => not (mem c B)))

lemma mem_diff (z A B : CList) :
    mem z (diff A B) = true ↔ mem z A = true ∧ mem z B = false := by
  cases A with | mk xs =>
  -- Filter lemma...
  sorry
end CList
