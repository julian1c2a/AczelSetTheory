import AczelSetTheory.HFSets

namespace HFSet

/-- Construye el par {a, b} a nivel CList. -/
def mkPair (a b : CList) : CList := CList.mk [a, b]

/-- El par {a, b} a nivel HFSet. -/
def pair (a b : HFSet) : HFSet :=
  Quotient.liftOn₂ a b
    (fun x y => Quotient.mk CList.Setoid (mkPair x y))
    (fun x₁ y₁ x₂ y₂ hx hy => by
      apply Quotient.sound
      show CList.extEq (mkPair x₁ y₁) (mkPair x₂ y₂) = true
      simp only [mkPair, CList.extEq_def, Bool.and_eq_true]
      constructor
      · -- subset (mk [x₁, y₁]) (mk [x₂, y₂])
        rw [CList.subset_cons, Bool.and_eq_true]
        constructor
        · rw [CList.mem_cons, CList.mem_cons, CList.mem_nil, Bool.or_false, Bool.or_eq_true]
          exact Or.inl hx
        · rw [CList.subset_cons, Bool.and_eq_true]
          constructor
          · rw [CList.mem_cons, CList.mem_cons, CList.mem_nil, Bool.or_false, Bool.or_eq_true]
            exact Or.inr hy
          · exact CList.subset_nil _
      · -- subset (mk [x₂, y₂]) (mk [x₁, y₁])
        rw [CList.subset_cons, Bool.and_eq_true]
        constructor
        · rw [CList.mem_cons, CList.mem_cons, CList.mem_nil, Bool.or_false, Bool.or_eq_true]
          have : CList.extEq x₂ x₁ = true := by rw [CList.extEq_comm]; exact hx
          exact Or.inl this
        · rw [CList.subset_cons, Bool.and_eq_true]
          constructor
          · rw [CList.mem_cons, CList.mem_cons, CList.mem_nil, Bool.or_false, Bool.or_eq_true]
            have : CList.extEq y₂ y₁ = true := by rw [CList.extEq_comm]; exact hy
            exact Or.inr this
          · exact CList.subset_nil _
    )

end HFSet
