/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import AczelSetTheory.HFSets
import Peano.PeanoNat.Combinatorics.Pow

open Peano

namespace HFSet

def cardCList (a : CList) : ℕ₀ :=
  match CList.normalize a with
  | CList.mk xs => PList.length xs

theorem cardCList_congr {a b : CList} (h : CList.extEq a b = true) :
    cardCList a = cardCList b := by
  simp only [cardCList, CList.normalize_eq_of_extEq h]

def card (A : HFSet) : ℕ₀ :=
  Quotient.liftOn A cardCList (fun _ _ h => cardCList_congr h)

-- ==================================================================
-- Helpers for Cardinal axioms
-- ==================================================================

theorem normalize_sorted {a : CList} {xs : PList CList}
    (h : CList.normalize a = CList.mk xs) : CList.Sorted xs := by
  cases a with | mk ys =>
  have hrfl : CList.normalize (CList.mk ys) =
      CList.mk (CList.insertionSort (CList.dedup (CList.normalizePList ys))) := rfl
  rw [hrfl] at h
  exact CList.mk.inj h ▸ CList.insertionSort_sorted (CList.dedup (CList.normalizePList ys))

theorem normalize_nodup {a : CList} {xs : PList CList}
    (h : CList.normalize a = CList.mk xs) : CList.Nodup xs := by
  cases a with | mk ys =>
  have hrfl : CList.normalize (CList.mk ys) =
      CList.mk (CList.insertionSort (CList.dedup (CList.normalizePList ys))) := rfl
  rw [hrfl] at h
  exact CList.mk.inj h ▸
    CList.insertionSort_nodup (CList.dedup (CList.normalizePList ys)) (CList.dedup_nodup _)

theorem normalizePList_id (l : PList CList)
    (h : ∀ y, PList.Mem y l → CList.normalize y = y) :
    CList.normalizePList l = l := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    show PList.cons (CList.normalize y) (CList.normalizePList ys) = PList.cons y ys
    congr 1
    · exact h y PList.Mem.head
    · exact ih (fun z hz => h z (PList.Mem.tail hz))

end HFSet
