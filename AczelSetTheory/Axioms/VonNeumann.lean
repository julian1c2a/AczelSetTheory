import AczelSetTheory.Axioms.Succ

namespace HFSet

-- ==================================================================
-- Conjuntos transitivos
-- ==================================================================

/-- Un conjunto es transitivo si todo elemento suyo es subconjunto suyo. -/
def isTransitive
  (A : HFSet) :
    Prop
      :=
  ∀ x, x ∈ A → x ⊆ A

theorem isTransitive_empty :
    isTransitive empty
      := by
  intro x hx
  exact absurd hx (not_mem_empty x)

theorem isTransitive_succ
  (A : HFSet) (hT : isTransitive A) :
    isTransitive (succ A)
      := by
  intro x hx
  rcases (mem_succ x A).mp hx with h | h
  · exact subset_trans x A (succ A) (hT x h) (A_subset_succ_A A)
  · rw [h]; exact A_subset_succ_A A

-- ==================================================================
-- Números naturales de Von Neumann
-- ==================================================================

/-- Predicado inductivo: n es un número natural de Von Neumann.
    Se construye a partir de ∅ y la función sucesor. -/
inductive isNat : HFSet → Prop where
  | zero : isNat empty
  | succ {n : HFSet} : isNat n → isNat (succ n)

theorem isNat_zero :
    isNat empty
      :=
  isNat.zero

theorem isNat_succ {n : HFSet}
  (h : isNat n) :
    isNat (succ n)
      :=
  isNat.succ h

theorem isNat_zero_or_succ {n : HFSet}
  (hn : isNat n) :
    n = empty ∨ ∃ m, isNat m ∧ n = succ m
      := by
  cases hn with
  | zero => exact Or.inl rfl
  | succ hk => exact Or.inr ⟨_, hk, rfl⟩

theorem isNat_isTransitive {n : HFSet}
  (hn : isNat n) :
    isTransitive n
      := by
  induction hn with
  | zero => exact isTransitive_empty
  | succ _ ih => exact isTransitive_succ _ ih

theorem isNat_mem_isNat {n m : HFSet}
  (hn : isNat n) (hm : m ∈ n) :
    isNat m
      := by
  induction hn generalizing m with
  | zero => exact absurd hm (not_mem_empty m)
  | succ hk ih =>
    rcases (mem_succ m _).mp hm with h | h
    · exact ih h
    · rw [h]; exact hk

theorem isNat_pred {n : HFSet}
  (hn : isNat (succ n)) :
    isNat n
      :=
  isNat_mem_isNat hn (A_mem_succ_A n)

theorem isNat_induction {n : HFSet}
  (P : HFSet → Prop) (h0 : P empty)
  (hs : ∀ k, isNat k → P k → P (succ k))
  (hn : isNat n) :
    P n
      := by
  induction hn with
  | zero => exact h0
  | succ hk ih => exact hs _ hk ih

end HFSet
