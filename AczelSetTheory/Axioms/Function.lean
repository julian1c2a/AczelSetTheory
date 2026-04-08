/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Operations.Function
import AczelSetTheory.Axioms.Relation

namespace HFSet

-- ==================================================================
-- Especificación de apply
-- ==================================================================

/-- apply f a h produce el único b con ⟪a, b⟫ ∈ f. -/
theorem apply_mem
  (f a : HFSet) (h : ∃ b, ⟪a, b⟫ ∈ f) :
    ⟪a, apply f a h⟫ ∈ f
      :=
  Classical.choose_spec h

/-- Si f es función y ⟪a, b⟫ ∈ f, entonces apply f a = b. -/
theorem apply_eq_of_mem
  (f a b : HFSet) (hf : isFunction f) (hab : ⟪a, b⟫ ∈ f) :
    apply f a ⟨b, hab⟩ = b
      := by
  have h_spec := apply_mem f a ⟨b, hab⟩
  exact hf.2 a _ _ h_spec hab

/-- Si f es función total sobre A, entonces a ∈ A implica ⟪a, apply f a⟫ ∈ f. -/
theorem totalFunction_apply_mem
  (f A B a : HFSet) (hf : isTotalFunction f A B) (ha : a ∈ A) :
    ⟪a, apply f a ((mem_domain_iff f a).mp (hf.2.1 ▸ ha))⟫ ∈ f
      :=
  apply_mem f a _

-- ==================================================================
-- El vacío es una función
-- ==================================================================

/-- El conjunto vacío es una función. -/
theorem isFunction_empty :
    isFunction empty
      := by
  refine ⟨isRelation_empty, ?_⟩
  intro a b₁ b₂ h₁ _
  exact absurd h₁ (not_mem_empty _)

-- ==================================================================
-- Inyectividad y sobreyectividad
-- ==================================================================

/-- f es inyectiva: si ⟪a₁, b⟫ ∈ f y ⟪a₂, b⟫ ∈ f, entonces a₁ = a₂. -/
def isInjective
  (f : HFSet) :
    Prop
      :=
  ∀ a₁ a₂ b, ⟪a₁, b⟫ ∈ f → ⟪a₂, b⟫ ∈ f → a₁ = a₂

/-- f es sobreyectiva sobre B: todo b ∈ B tiene un preimagen en f. -/
def isSurjective
  (f B : HFSet) :
    Prop
      :=
  ∀ b, b ∈ B → ∃ a, ⟪a, b⟫ ∈ f

/-- f es biyectiva de A en B. -/
def isBijective
  (f A B : HFSet) :
    Prop
      :=
  isTotalFunction f A B ∧ isInjective f ∧ isSurjective f B

-- ==================================================================
-- Propiedades básicas de funciones
-- ==================================================================

/-- Si f es función y ⟪a, b₁⟫ ∈ f y ⟪a, b₂⟫ ∈ f, entonces b₁ = b₂. -/
theorem isFunction_unique
  (f a b₁ b₂ : HFSet) (hf : isFunction f) (h₁ : ⟪a, b₁⟫ ∈ f) (h₂ : ⟪a, b₂⟫ ∈ f) :
    b₁ = b₂
      :=
  hf.2 a b₁ b₂ h₁ h₂

/-- Si ⟪a, b⟫ ∈ f entonces a ∈ domain f. -/
theorem mem_domain_of_mem
  (f a b : HFSet) (h : ⟪a, b⟫ ∈ f) :
    a ∈ domain f
      :=
  (mem_domain_iff f a).mpr ⟨b, h⟩

/-- Si ⟪a, b⟫ ∈ f entonces b ∈ range f. -/
theorem mem_range_of_mem
  (f a b : HFSet) (h : ⟪a, b⟫ ∈ f) :
    b ∈ range f
      :=
  (mem_range_iff f b).mpr ⟨a, h⟩

end HFSet
