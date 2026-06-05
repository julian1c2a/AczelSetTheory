/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Operations.Restriction
import AczelSetTheory.Axioms.Composition
import AczelSetTheory.Axioms.Separation
import AczelSetTheory.Axioms.Subset
import AczelSetTheory.Axioms.OrderedPair

namespace HFSet

-- ==================================================================
-- Lemas sobre restrict
-- ==================================================================

/-- Caracterización de la restricción:
    p ∈ R ↾ A ↔ p ∈ R ∧ ∃ a b, p = ⟪a, b⟫ ∧ a ∈ A. -/
theorem mem_restrict {R A p : HFSet} :
    p ∈ (R ↾ A) ↔ p ∈ R ∧ ∃ a b, p = ⟪a, b⟫ ∧ a ∈ A := by
  unfold HFSet.restrict
  rw [mem_sep]
  constructor
  · rintro ⟨hpR, a, haA, b, _, heq⟩
    exact ⟨hpR, a, b, heq, haA⟩
  · rintro ⟨hpR, a, b, heq, haA⟩
    exact ⟨hpR, a, haA, b, snd_in a b R (heq ▸ hpR), heq⟩

/-- La restricción preserva la pertenencia a R. -/
theorem restrict_subset {R A : HFSet} : (R ↾ A) ⊆ R := by
  intro p hp
  exact ((mem_restrict).mp hp).1

/-- Si R es relación, R ↾ A también lo es. -/
theorem restrict_isRelation {R A : HFSet} (hR : isRelation R) : isRelation (R ↾ A) := by
  intro p hp
  exact hR p (restrict_subset p hp)

/-- Pertenencia en la restricción en forma par ordenado. -/
theorem mem_restrict_pair {R A a b : HFSet} :
    ⟪a, b⟫ ∈ (R ↾ A) ↔ ⟪a, b⟫ ∈ R ∧ a ∈ A := by
  constructor
  · intro hp
    obtain ⟨h, a', b', heq, ha'⟩ := mem_restrict.mp hp
    have ⟨ha, _⟩ := (orderedPair_eq_iff a b a' b').mp heq
    exact ⟨h, ha ▸ ha'⟩
  · rintro ⟨h, haA⟩
    exact mem_restrict.mpr ⟨h, a, b, rfl, haA⟩

-- ==================================================================
-- Lemas sobre preimage
-- ==================================================================

/-- Caracterización de la preimagen:
    a ∈ preimage R B ↔ ∃ b ∈ B, ⟪a, b⟫ ∈ R. -/
theorem mem_preimage {R B a : HFSet} :
    a ∈ preimage R B ↔ ∃ b, b ∈ B ∧ ⟪a, b⟫ ∈ R := by
  unfold HFSet.preimage
  rw [mem_sep]
  constructor
  · rintro ⟨_, b, hbB, habR⟩
    exact ⟨b, hbB, habR⟩
  · rintro ⟨b, hbB, habR⟩
    exact ⟨fst_in a b R habR, b, hbB, habR⟩

/-- La preimagen de ∅ es ∅. -/
theorem preimage_empty_set {R : HFSet} : preimage R empty = empty := by
  apply extensionality; intro x
  rw [mem_preimage]
  constructor
  · rintro ⟨_, hb, _⟩; exact absurd hb (not_mem_empty _)
  · intro h; exact absurd h (not_mem_empty _)

end HFSet
