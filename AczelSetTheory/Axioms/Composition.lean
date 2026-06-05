/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Operations.Composition
import AczelSetTheory.Axioms.Relation
import AczelSetTheory.Axioms.Separation
import AczelSetTheory.Axioms.Union
import AczelSetTheory.Axioms.Pair
import AczelSetTheory.Axioms.Singleton
import AczelSetTheory.Axioms.OrderedPair

namespace HFSet

-- Si ⟪a,b⟫ ∈ R entonces a,b ∈ ⋃⋃R
theorem fst_in (a b R : HFSet) (h : ⟪a, b⟫ ∈ R) : a ∈ sUnion (sUnion R) := by
  have h1 : singleton a ∈ ⟪a, b⟫ :=
    (mem_pair (singleton a) (singleton a) (pair a b)).mpr (Or.inl rfl)
  have h2 : singleton a ∈ sUnion R :=
    (mem_sUnion (singleton a) R).mpr ⟨⟪a, b⟫, h, h1⟩
  exact (mem_sUnion a (sUnion R)).mpr ⟨singleton a, h2, (mem_singleton a a).mpr rfl⟩

theorem snd_in (a b R : HFSet) (h : ⟪a, b⟫ ∈ R) : b ∈ sUnion (sUnion R) := by
  have h1 : pair a b ∈ ⟪a, b⟫ :=
    (mem_pair (pair a b) (singleton a) (pair a b)).mpr (Or.inr rfl)
  have h2 : pair a b ∈ sUnion R :=
    (mem_sUnion (pair a b) R).mpr ⟨⟪a, b⟫, h, h1⟩
  exact (mem_sUnion b (sUnion R)).mpr ⟨pair a b, h2, (mem_pair b a b).mpr (Or.inr rfl)⟩

-- ==================================================================
-- Lemas sobre imageRel
-- ==================================================================

/-- Caracterización de la imagen relacional:
    b ∈ imageRel R A ↔ ∃ a ∈ A, ⟪a, b⟫ ∈ R. -/
theorem mem_imageRel {R A b : HFSet} :
    b ∈ imageRel R A ↔ ∃ a, a ∈ A ∧ ⟪a, b⟫ ∈ R := by
  unfold imageRel
  rw [mem_sep]
  constructor
  · rintro ⟨_, a, haA, habR⟩
    exact ⟨a, haA, habR⟩
  · rintro ⟨a, haA, habR⟩
    exact ⟨snd_in a b R habR, a, haA, habR⟩

/-- La imagen relacional de cualquier conjunto bajo ∅ es vacía. -/
theorem imageRel_empty_rel {A : HFSet} : imageRel empty A = empty := by
  apply extensionality; intro x
  rw [mem_imageRel]
  constructor
  · rintro ⟨_, _, h⟩; exact absurd h (not_mem_empty _)
  · intro h; exact absurd h (not_mem_empty _)

/-- La imagen de ∅ bajo cualquier relación es vacía. -/
theorem imageRel_empty_set {R : HFSet} : imageRel R empty = empty := by
  apply extensionality; intro x
  rw [mem_imageRel]
  constructor
  · rintro ⟨_, ha, _⟩; exact absurd ha (not_mem_empty _)
  · intro h; exact absurd h (not_mem_empty _)

-- ==================================================================
-- Lemas sobre relComp
-- ==================================================================

/-- Caracterización de relComp: c ∈ S ∘ᵣ R ↔ ∃ a b, ⟪a,b⟫ ∈ R ∧ ⟪b,c⟫ ∈ S. -/
theorem mem_relComp {R S c : HFSet} :
    c ∈ S ∘ᵣ R ↔ ∃ a b, ⟪a, b⟫ ∈ R ∧ ⟪b, c⟫ ∈ S := by
  unfold HFSet.relComp
  rw [mem_sep]
  constructor
  · rintro ⟨_, a, _, b, _, habR, hbcS⟩
    exact ⟨a, b, habR, hbcS⟩
  · rintro ⟨a, b, habR, hbcS⟩
    exact ⟨snd_in b c S hbcS, a, fst_in a b R habR, b, snd_in a b R habR, habR, hbcS⟩

/-- La composición con ∅ a la izquierda es vacía. -/
theorem relComp_empty_left {R : HFSet} : empty ∘ᵣ R = empty := by
  apply extensionality; intro x
  rw [mem_relComp]
  constructor
  · rintro ⟨_, _, _, h⟩; exact absurd h (not_mem_empty _)
  · intro h; exact absurd h (not_mem_empty _)

/-- La composición con ∅ a la derecha es vacía. -/
theorem relComp_empty_right {S : HFSet} : S ∘ᵣ empty = empty := by
  apply extensionality; intro x
  rw [mem_relComp]
  constructor
  · rintro ⟨_, _, h, _⟩; exact absurd h (not_mem_empty _)
  · intro h; exact absurd h (not_mem_empty _)

end HFSet
