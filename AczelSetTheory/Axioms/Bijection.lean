/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Axioms.Function
import AczelSetTheory.Axioms.Restriction

namespace HFSet

-- ==================================================================
-- Inyectividad
-- ==================================================================

/-- El conjunto vacío es inyectivo. -/
theorem isInjective_empty :
    isInjective empty
      := by
  intro a₁ a₂ b h₁ _
  exact absurd h₁ (not_mem_empty _)

/-- La restricción de una función inyectiva es inyectiva. -/
theorem isInjective_restrict
    {f A : HFSet} (hf : isInjective f) :
    isInjective (f ↾ A)
      := by
  intro a₁ a₂ b h₁ h₂
  exact hf a₁ a₂ b
    (restrict_subset ⟪a₁, b⟫ h₁)
    (restrict_subset ⟪a₂, b⟫ h₂)

-- ==================================================================
-- Sobreyectividad
-- ==================================================================

/-- Toda función es trivialmente sobreyectiva sobre el conjunto vacío. -/
theorem isSurjective_empty_codomain
    (f : HFSet) :
    isSurjective f empty
      := by
  intro b hb
  exact absurd hb (not_mem_empty b)

/-- Toda función es sobreyectiva sobre su rango. -/
theorem isSurjective_range
    (f : HFSet) :
    isSurjective f (range f)
      := by
  intro b hb
  exact (mem_range_iff f b).mp hb

/-- Para una función total de A en B:
    f es sobreyectiva sobre B ↔ range f = B. -/
theorem isSurjective_iff_range_eq
    {f A B : HFSet} (hf : isTotalFunction f A B) :
    isSurjective f B ↔ range f = B
      := by
  constructor
  · intro hs
    apply extensionality; intro b
    constructor
    · intro hb
      exact hf.2.2 b hb
    · intro hb
      exact (mem_range_iff f b).mpr (hs b hb)
  · intro hr b hb
    rw [← hr] at hb
    rwa [mem_range_iff] at hb

-- ==================================================================
-- Biyectividad: construcción y descomposición
-- ==================================================================

/-- Introducción de biyectividad a partir de sus tres componentes. -/
theorem isBijective_intro
    {f A B : HFSet}
    (hf : isTotalFunction f A B) (hi : isInjective f) (hs : isSurjective f B) :
    isBijective f A B
      :=
  ⟨hf, hi, hs⟩

/-- Una función biyectiva es una función total. -/
theorem isBijective_isTotalFunction
    {f A B : HFSet} (hf : isBijective f A B) :
    isTotalFunction f A B
      :=
  hf.1

/-- Una función biyectiva es una función (relación univaluada). -/
theorem isBijective_isFunction
    {f A B : HFSet} (hf : isBijective f A B) :
    isFunction f
      :=
  hf.1.1

/-- Una función biyectiva es inyectiva. -/
theorem isBijective_isInjective
    {f A B : HFSet} (hf : isBijective f A B) :
    isInjective f
      :=
  hf.2.1

/-- Una función biyectiva es sobreyectiva sobre B. -/
theorem isBijective_isSurjective
    {f A B : HFSet} (hf : isBijective f A B) :
    isSurjective f B
      :=
  hf.2.2

/-- El dominio de una función biyectiva es A. -/
theorem isBijective_domain_eq
    {f A B : HFSet} (hf : isBijective f A B) :
    domain f = A
      :=
  hf.1.2.1

/-- El rango de una función biyectiva es B. -/
theorem isBijective_range_eq
    {f A B : HFSet} (hf : isBijective f A B) :
    range f = B
      :=
  (isSurjective_iff_range_eq hf.1).mp hf.2.2

-- ==================================================================
-- El vacío como biyección canónica
-- ==================================================================

/-- El conjunto vacío es una biyección de ∅ en ∅. -/
theorem isBijective_empty :
    isBijective empty empty empty
      := by
  refine ⟨⟨isFunction_empty, domain_empty, ?_⟩, isInjective_empty,
          isSurjective_empty_codomain empty⟩
  intro b hb
  rw [range_empty] at hb
  exact absurd hb (not_mem_empty b)

end HFSet
