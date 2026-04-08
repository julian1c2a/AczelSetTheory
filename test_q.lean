import AczelSetTheory.HFSets
example : HFSet.repr HFSet.empty = CList.empty := by
  unfold HFSet.repr HFSet.empty
  change CList.normalize CList.empty = CList.empty
  unfold CList.normalize CList.empty
  simp [CList.dedup, CList.dedupAux, CList.insertionSort]
