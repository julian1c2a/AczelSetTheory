/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Operations.Product
import AczelSetTheory.Axioms.Powerset
import AczelSetTheory.Axioms.Separation
import AczelSetTheory.Axioms.Pair
import AczelSetTheory.Axioms.Singleton
import AczelSetTheory.Axioms.OrderedPair
import AczelSetTheory.Axioms.Union
import AczelSetTheory.Axioms.Relation
import AczelSetTheory.Axioms.Function

namespace HFSet

-- ==================================================================
-- Lema auxiliar de universo
-- ==================================================================

/-- Si a ∈ A y b ∈ B entonces ⟪a, b⟫ ∈ 𝒫(𝒫(A ∪ B)). -/
private theorem prodHF_mem_universe {A B a b : HFSet} (ha : a ∈ A) (hb : b ∈ B) :
    ⟪a, b⟫ ∈ powerset (powerset (union A B)) := by
  rw [mem_powerset]
  intro x hx
  rw [mem_powerset]
  unfold orderedPair at hx
  have hxab := (mem_pair x (singleton a) (pair a b)).mp hx
  cases hxab with
  | inl h =>
    rw [h]
    intro y hy
    rw [mem_singleton] at hy
    exact hy ▸ (mem_union a A B).mpr (Or.inl ha)
  | inr h =>
    rw [h]
    intro y hy
    have hya := (mem_pair y a b).mp hy
    cases hya with
    | inl h2 => exact h2 ▸ (mem_union a A B).mpr (Or.inl ha)
    | inr h2 => exact h2 ▸ (mem_union b A B).mpr (Or.inr hb)

-- ==================================================================
-- Caracterización de prodHF
-- ==================================================================

/-- Caracterización del producto cartesiano:
    p ∈ A ×ₛ B ↔ ∃ a b, a ∈ A ∧ b ∈ B ∧ p = ⟪a, b⟫. -/
theorem mem_prodHF {A B p : HFSet} :
    p ∈ A ×ₛ B ↔ ∃ a b, a ∈ A ∧ b ∈ B ∧ p = ⟪a, b⟫ := by
  unfold HFSet.prodHF
  rw [mem_sep]
  constructor
  · rintro ⟨_, a, ha, b, hb, rfl⟩; exact ⟨a, b, ha, hb, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩; exact ⟨prodHF_mem_universe ha hb, a, ha, b, hb, rfl⟩

/-- Membresía en forma de par ordenado:
    ⟪a, b⟫ ∈ A ×ₛ B ↔ a ∈ A ∧ b ∈ B. -/
theorem mem_prodHF_pair {A B a b : HFSet} :
    ⟪a, b⟫ ∈ A ×ₛ B ↔ a ∈ A ∧ b ∈ B := by
  rw [mem_prodHF]
  constructor
  · rintro ⟨c, d, hc, hd, heq⟩
    have hcd := (orderedPair_eq_iff a b c d).mp heq
    exact ⟨hcd.1 ▸ hc, hcd.2 ▸ hd⟩
  · rintro ⟨ha, hb⟩
    exact ⟨a, b, ha, hb, rfl⟩

-- ==================================================================
-- Propiedades estructurales
-- ==================================================================

/-- El producto cartesiano es una relación. -/
theorem prodHF_isRelation {A B : HFSet} : isRelation (A ×ₛ B) := by
  intro p hp
  rcases mem_prodHF.mp hp with ⟨a, b, _, _, rfl⟩
  exact ⟨a, b, rfl⟩

/-- Si ⟪a, b⟫ ∈ A ×ₛ B entonces a ∈ A. -/
theorem fst_of_mem_prodHF {A B a b : HFSet} (h : ⟪a, b⟫ ∈ A ×ₛ B) : a ∈ A :=
  (mem_prodHF_pair.mp h).1

/-- Si ⟪a, b⟫ ∈ A ×ₛ B entonces b ∈ B. -/
theorem snd_of_mem_prodHF {A B a b : HFSet} (h : ⟪a, b⟫ ∈ A ×ₛ B) : b ∈ B :=
  (mem_prodHF_pair.mp h).2

-- ==================================================================
-- Casos vacíos
-- ==================================================================

/-- El producto cartesiano con el vacío a la izquierda es vacío. -/
theorem prodHF_empty_left {B : HFSet} : empty ×ₛ B = empty := by
  apply extensionality; intro p
  rw [mem_prodHF]
  constructor
  · rintro ⟨_, _, ha, _, _⟩; exact absurd ha (not_mem_empty _)
  · intro h; exact absurd h (not_mem_empty _)

/-- El producto cartesiano con el vacío a la derecha es vacío. -/
theorem prodHF_empty_right {A : HFSet} : A ×ₛ empty = empty := by
  apply extensionality; intro p
  rw [mem_prodHF]
  constructor
  · rintro ⟨_, _, _, hb, _⟩; exact absurd hb (not_mem_empty _)
  · intro h; exact absurd h (not_mem_empty _)

-- ==================================================================
-- Relación con funciones totales
-- ==================================================================

/-- Toda función total f : A → B es subconjunto de A ×ₛ B. -/
theorem isTotalFunction_subset_prodHF {f A B : HFSet}
    (hf : isTotalFunction f A B) :
    ∀ p, p ∈ f → p ∈ A ×ₛ B := by
  intro p hp
  rcases hf.1.1 p hp with ⟨a, b, rfl⟩
  rw [mem_prodHF_pair]
  exact ⟨hf.2.1 ▸ (mem_domain_iff f a).mpr ⟨b, hp⟩,
         hf.2.2 b ((mem_range_iff f b).mpr ⟨a, hp⟩)⟩

end HFSet
