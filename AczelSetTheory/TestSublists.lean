import AczelSetTheory.HFSets

def sublists {α} : List α → List (List α)
  | [] => [[]]
  | a :: as => let res := sublists as; res ++ res.map (a :: ·)
