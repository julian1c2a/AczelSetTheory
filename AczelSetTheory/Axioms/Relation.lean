/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Operations.Relation
import AczelSetTheory.Axioms.Separation
import AczelSetTheory.Axioms.Union
import AczelSetTheory.Axioms.Pair
import AczelSetTheory.Axioms.Singleton
import AczelSetTheory.Axioms.OrderedPair

namespace HFSet

-- ==================================================================
-- Lemas auxiliares: componentes de pares ordenados en ⋃⋃R
-- ==================================================================

/-- Si ⟪a, b⟫ ∈ R entonces a ∈ ⋃⋃R. -/
private theorem fst_mem_sUnion_sUnion
  (a b R : HFSet) (h : ⟪a, b⟫ ∈ R) :
    a ∈ sUnion (sUnion R)
      := by
  -- {a} ∈ ⟪a, b⟫
  have h_sa : singleton a ∈ ⟪a, b⟫ :=
    (mem_pair (singleton a) (singleton a) (pair a b)).mpr (Or.inl rfl)
  -- {a} ∈ ⋃R
  have h_sa_sR : singleton a ∈ sUnion R :=
    (mem_sUnion (singleton a) R).mpr ⟨⟪a, b⟫, h, h_sa⟩
  -- a ∈ {a}
  have h_a_sa : a ∈ singleton a :=
    (mem_singleton a a).mpr rfl
  -- a ∈ ⋃⋃R
  exact (mem_sUnion a (sUnion R)).mpr ⟨singleton a, h_sa_sR, h_a_sa⟩

/-- Si ⟪a, b⟫ ∈ R entonces b ∈ ⋃⋃R. -/
private theorem snd_mem_sUnion_sUnion
  (a b R : HFSet) (h : ⟪a, b⟫ ∈ R) :
    b ∈ sUnion (sUnion R)
      := by
  -- {a, b} ∈ ⟪a, b⟫
  have h_ab : pair a b ∈ ⟪a, b⟫ :=
    (mem_pair (pair a b) (singleton a) (pair a b)).mpr (Or.inr rfl)
  -- {a, b} ∈ ⋃R
  have h_ab_sR : pair a b ∈ sUnion R :=
    (mem_sUnion (pair a b) R).mpr ⟨⟪a, b⟫, h, h_ab⟩
  -- b ∈ {a, b}
  have h_b_ab : b ∈ pair a b :=
    (mem_pair b a b).mpr (Or.inr rfl)
  -- b ∈ ⋃⋃R
  exact (mem_sUnion b (sUnion R)).mpr ⟨pair a b, h_ab_sR, h_b_ab⟩

-- ==================================================================
-- Teoremas de membresía para domain y range
-- ==================================================================

/-- a ∈ domain R ↔ ∃ b, ⟪a, b⟫ ∈ R (cuando R es relación). -/
theorem mem_domain_iff
  (R a : HFSet) :
    a ∈ domain R ↔ ∃ b, ⟪a, b⟫ ∈ R
      := by
  unfold domain
  rw [mem_sep]
  constructor
  · rintro ⟨_, b, _, hab⟩
    exact ⟨b, hab⟩
  · rintro ⟨b, hab⟩
    exact ⟨fst_mem_sUnion_sUnion a b R hab,
           b, snd_mem_sUnion_sUnion a b R hab, hab⟩

/-- b ∈ range R ↔ ∃ a, ⟪a, b⟫ ∈ R (cuando R es relación). -/
theorem mem_range_iff
  (R b : HFSet) :
    b ∈ range R ↔ ∃ a, ⟪a, b⟫ ∈ R
      := by
  unfold range
  rw [mem_sep]
  constructor
  · rintro ⟨_, a, _, hab⟩
    exact ⟨a, hab⟩
  · rintro ⟨a, hab⟩
    exact ⟨snd_mem_sUnion_sUnion a b R hab,
           a, fst_mem_sUnion_sUnion a b R hab, hab⟩

-- ==================================================================
-- Domain y range del vacío
-- ==================================================================

/-- El dominio de ∅ es ∅. -/
theorem domain_empty :
    domain empty = empty
      := by
  apply extensionality
  intro x
  constructor
  · intro hx
    unfold domain at hx
    rw [mem_sep] at hx
    exact absurd hx.1 (not_mem_empty x)
  · intro hx
    exact absurd hx (not_mem_empty x)

/-- El rango de ∅ es ∅. -/
theorem range_empty :
    range empty = empty
      := by
  apply extensionality
  intro x
  constructor
  · intro hx
    unfold range at hx
    rw [mem_sep] at hx
    exact absurd hx.1 (not_mem_empty x)
  · intro hx
    exact absurd hx (not_mem_empty x)

-- ==================================================================
-- El vacío es una relación
-- ==================================================================

/-- El conjunto vacío es una relación. -/
theorem isRelation_empty :
    isRelation empty
      := by
  intro z hz
  exact absurd hz (not_mem_empty z)

end HFSet
