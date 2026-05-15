/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import AczelSetTheory.Axioms.Adjunction
import AczelSetTheory.Axioms.Foundation

namespace HFSet

-- ─────────────────────────────────────────────────────────────────
-- ε-Inducción simple (sobre la estructura PList del representante)
-- ─────────────────────────────────────────────────────────────────

private theorem eps_induction_aux (P : HFSet → Prop)
    (h_empty : P empty)
    (h_adj : ∀ A b, P A → P (insert b A))
    (xs : PList CList) : P (Quotient.mk CList.Setoid (CList.mk xs)) := by
  induction xs with
  | nil => exact h_empty
  | cons y ys ih =>
    have heq : Quotient.mk CList.Setoid (CList.mk (.cons y ys)) =
               insert (Quotient.mk CList.Setoid y)
                      (Quotient.mk CList.Setoid (CList.mk ys)) := rfl
    rw [heq]
    exact h_adj _ _ ih

/-- ε-Inducción simple: `P ∅` y `∀ A b, P A → P (insert b A)` implican `∀ A, P A`.
    Todo HFSet se construye desde ∅ mediante adjunciones sucesivas. -/
theorem eps_induction (P : HFSet → Prop)
    (h_empty : P empty)
    (h_adj : ∀ A b, P A → P (insert b A)) : ∀ A, P A := by
  intro A
  rcases Quotient.exists_rep A with ⟨c, rfl⟩
  cases c with | mk xs =>
  exact eps_induction_aux P h_empty h_adj xs

-- ─────────────────────────────────────────────────────────────────
-- ε-Inducción fuerte (bien-fundación de ∈)
-- ─────────────────────────────────────────────────────────────────

private theorem strong_eps_induction_aux (P : HFSet → Prop)
    (h : ∀ A, (∀ x, x ∈ A → P x) → P A)
    (n : ℕ₀) : ∀ (c : CList), CList.cSize c ≤ n → P (Quotient.mk CList.Setoid c) := by
  induction n with
  | zero =>
    intro c hle
    cases c with | mk xs =>
    simp only [CList.cSize_mk] at hle
    exact absurd hle (by omega₀)
  | succ m ih_m =>
    intro c hle
    cases c with | mk xs =>
    apply h
    intro x hx
    rcases Quotient.exists_rep x with ⟨xc, rfl⟩
    -- hx : CList.mem xc (CList.mk xs) = true
    obtain ⟨y, hy_mem, hy_eq⟩ := CList.mem_exists_plist_mem xc xs hx
    have hcSize_y : CList.cSize y ≤ m := by
      have hlt := CList.cSize_lt_of_mem hy_mem
      simp only [CList.cSize_mk] at hle hlt
      omega₀
    have hP_y := ih_m y hcSize_y
    rw [Quotient.sound hy_eq]
    exact hP_y

/-- ε-Inducción fuerte: si para todo conjunto A, la hipótesis de que todos sus
    elementos satisfacen P implica P A, entonces P vale para todo HFSet.
    Equivale a la bien-fundación de la relación ∈ sobre HFSet. -/
theorem strong_eps_induction (P : HFSet → Prop)
    (h : ∀ A, (∀ x, x ∈ A → P x) → P A) : ∀ A, P A := by
  intro A
  rcases Quotient.exists_rep A with ⟨c, rfl⟩
  exact strong_eps_induction_aux P h (CList.cSize c) c (by omega₀)

end HFSet
