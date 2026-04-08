import AczelSetTheory.Axioms.Union
import AczelSetTheory.Axioms.Singleton
import AczelSetTheory.Axioms.Foundation
import AczelSetTheory.Axioms.Subset

namespace HFSet

-- ==================================================================
-- Definición del sucesor de Von Neumann
-- ==================================================================

/-- El sucesor de Von Neumann: succ A = A ∪ {A} -/
def succ (A : HFSet) : HFSet := union A (singleton A)

theorem mem_succ (x A : HFSet) : x ∈ succ A ↔ x ∈ A ∨ x = A := by
  unfold succ; rw [mem_union x A (singleton A), mem_singleton x A]

theorem A_mem_succ_A (A : HFSet) : A ∈ succ A :=
  (mem_succ A A).mpr (Or.inr rfl)

theorem mem_succ_of_mem (x A : HFSet) (h : x ∈ A) : x ∈ succ A :=
  (mem_succ x A).mpr (Or.inl h)

theorem A_subset_succ_A (A : HFSet) : A ⊆ succ A :=
  fun x hx => mem_succ_of_mem x A hx

-- ==================================================================
-- El sucesor no es vacío
-- ==================================================================

theorem succ_ne_empty (A : HFSet) : succ A ≠ empty := by
  intro h
  exact not_mem_empty A (h ▸ A_mem_succ_A A)

-- ==================================================================
-- Consecuencias de Foundation: no auto-pertenencia
-- ==================================================================

/-- Ningún conjunto se contiene a sí mismo. -/
theorem not_mem_self (A : HFSet) : ¬ (A ∈ A) := by
  intro hAA
  have hne : singleton A ≠ empty := by
    intro h; exact not_mem_empty A (h ▸ (mem_singleton A A).mpr rfl)
  obtain ⟨x, hx_mem, hx_disj⟩ := foundation (singleton A) hne
  have hxA : x = A := (mem_singleton x A).mp hx_mem
  rw [hxA] at hx_disj
  exact hx_disj A hAA ((mem_singleton A A).mpr rfl)

/-- No existen ciclos de longitud 2: si A ∈ B entonces B ∉ A. -/
theorem no_mem_cycle2 (A B : HFSet) (hAB : A ∈ B) (hBA : B ∈ A) : False := by
  have hne : pair A B ≠ empty := by
    intro h; exact not_mem_empty A (h ▸ (mem_pair A A B).mpr (Or.inl rfl))
  obtain ⟨x, hx_mem, hx_disj⟩ := foundation (pair A B) hne
  rcases (mem_pair x A B).mp hx_mem with hxA | hxB
  · rw [hxA] at hx_disj
    exact hx_disj B hBA ((mem_pair B A B).mpr (Or.inr rfl))
  · rw [hxB] at hx_disj
    exact hx_disj A hAB ((mem_pair A A B).mpr (Or.inl rfl))

-- ==================================================================
-- Inyectividad del sucesor
-- ==================================================================

theorem succ_injective (A B : HFSet) (h : succ A = succ B) : A = B := by
  have h1 : A ∈ B ∨ A = B := by
    have : A ∈ succ B := by rw [← h]; exact A_mem_succ_A A
    exact (mem_succ A B).mp this
  have h2 : B ∈ A ∨ B = A := by
    have : B ∈ succ A := by rw [h]; exact A_mem_succ_A B
    exact (mem_succ B A).mp this
  rcases h1 with hAB | hAB
  · rcases h2 with hBA | hBA
    · exact (no_mem_cycle2 A B hAB hBA).elim
    · rw [hBA] at hAB; exact (not_mem_self A hAB).elim
  · exact hAB

end HFSet
