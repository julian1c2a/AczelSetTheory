import AczelSetTheory.CList.Filter
import AczelSetTheory.HFSets

namespace CList

-- Setminus
def setminus (A B : CList) : CList :=
  match A with
  | mk xs => mk (xs.filter (fun x => !(mem x B)))

theorem setminus_P_respects (B : CList) :
    P_respects (fun x => !(mem x B)) := by
  intro x y hxy
  have h_mem : mem x B = mem y B := by
    apply Bool.eq_iff_iff.mpr
    exact HFSet.mem_resp_left x y B hxy
  rw [h_mem]

theorem mem_setminus (z A B : CList) :
    mem z (setminus A B) = true ↔ mem z A = true ∧ mem z B = false := by
  cases A with | mk xs =>
  simp only [setminus]
  constructor
  · intro hz
    have hz2 := subset_filter (fun x => !(mem x B)) xs
    have hz_A : mem z (mk xs) = true := mem_subset z _ _ hz hz2
    -- We need to show mem z B = false.
    -- Wait, from mem z (filter) we somehow know P z = true. But the theorem filter_subset only gives subset.
    -- We should destruct mem z (filter) properly.
    sorry
  · rintro ⟨hA, hB⟩
    have hnot : (!(mem z B)) = true := by rw [hB, Bool.not_false]
    exact CList.mem_filter_of_mem _ (setminus_P_respects B) z xs hA hnot

end CList
