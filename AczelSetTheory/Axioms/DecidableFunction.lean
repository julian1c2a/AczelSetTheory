/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Axioms.Decidable
import AczelSetTheory.Axioms.Function
import AczelSetTheory.Axioms.Relation

namespace HFSet

-- ==================================================================
-- Relaciones
-- ==================================================================

theorem isRelation_iff_bounded (R : HFSet) :
    isRelation R ↔ ∀ p, p ∈ R → ∃ a, a ∈ sUnion (sUnion R) ∧ ∃ b, b ∈ sUnion (sUnion R) ∧ p = ⟪a, b⟫ := by
  constructor
  · intro h p hp
    obtain ⟨a, b, rfl⟩ := h p hp
    exact ⟨a, fst_mem_sUnion_sUnion a b R hp, b, snd_mem_sUnion_sUnion a b R hp, rfl⟩
  · intro h p hp
    obtain ⟨a, _, b, _, hp_eq⟩ := h p hp
    exact ⟨a, b, hp_eq⟩

instance instDecidableIsRelation (R : HFSet) : Decidable (isRelation R) :=
  decidable_of_iff _ (isRelation_iff_bounded R).symm

-- ==================================================================
-- Funciones
-- ==================================================================

theorem isFunction_iff_bounded (f : HFSet) :
    isFunction f ↔ isRelation f ∧ 
      ∀ a, a ∈ sUnion (sUnion f) → 
      ∀ b₁, b₁ ∈ sUnion (sUnion f) → 
      ∀ b₂, b₂ ∈ sUnion (sUnion f) → 
      ⟪a, b₁⟫ ∈ f → ⟪a, b₂⟫ ∈ f → b₁ = b₂ := by
  constructor
  · intro ⟨hrel, hfun⟩
    refine ⟨hrel, fun a _ b₁ _ b₂ _ => hfun a b₁ b₂⟩
  · intro ⟨hrel, hfun_bnd⟩
    refine ⟨hrel, fun a b₁ b₂ h1 h2 => ?_⟩
    have ha := fst_mem_sUnion_sUnion a b₁ f h1
    have hb1 := snd_mem_sUnion_sUnion a b₁ f h1
    have hb2 := snd_mem_sUnion_sUnion a b₂ f h2
    exact hfun_bnd a ha b₁ hb1 b₂ hb2 h1 h2

instance instDecidableIsFunction (f : HFSet) : Decidable (isFunction f) :=
  decidable_of_iff _ (isFunction_iff_bounded f).symm

-- ==================================================================
-- Totalidad
-- ==================================================================

theorem isTotalFunction_iff_bounded (f A B : HFSet) :
    isTotalFunction f A B ↔ isFunction f ∧ domain f = A ∧ range f ⊆ B := by
  rfl

instance instDecidableIsTotalFunction (f A B : HFSet) : Decidable (isTotalFunction f A B) :=
  decidable_of_iff _ (isTotalFunction_iff_bounded f A B).symm

-- ==================================================================
-- Inyectividad
-- ==================================================================

theorem isInjective_iff_bounded (f : HFSet) :
    isInjective f ↔ 
      ∀ a₁, a₁ ∈ sUnion (sUnion f) → 
      ∀ a₂, a₂ ∈ sUnion (sUnion f) → 
      ∀ b, b ∈ sUnion (sUnion f) → 
      ⟪a₁, b⟫ ∈ f → ⟪a₂, b⟫ ∈ f → a₁ = a₂ := by
  constructor
  · intro hinj a₁ _ a₂ _ b _
    exact hinj a₁ a₂ b
  · intro hbnd a₁ a₂ b h1 h2
    have ha1 := fst_mem_sUnion_sUnion a₁ b f h1
    have ha2 := fst_mem_sUnion_sUnion a₂ b f h2
    have hb := snd_mem_sUnion_sUnion a₁ b f h1
    exact hbnd a₁ ha1 a₂ ha2 b hb h1 h2

instance instDecidableIsInjective (f : HFSet) : Decidable (isInjective f) :=
  decidable_of_iff _ (isInjective_iff_bounded f).symm

-- ==================================================================
-- Sobreyectividad
-- ==================================================================

theorem isSurjective_iff_bounded (f B : HFSet) :
    isSurjective f B ↔ ∀ b, b ∈ B → ∃ a, a ∈ sUnion (sUnion f) ∧ ⟪a, b⟫ ∈ f := by
  constructor
  · intro hsur b hb
    obtain ⟨a, ha⟩ := hsur b hb
    exact ⟨a, fst_mem_sUnion_sUnion a b f ha, ha⟩
  · intro hbnd b hb
    obtain ⟨a, _, ha_in⟩ := hbnd b hb
    exact ⟨a, ha_in⟩

instance instDecidableIsSurjective (f B : HFSet) : Decidable (isSurjective f B) :=
  decidable_of_iff _ (isSurjective_iff_bounded f B).symm

-- ==================================================================
-- Biyectividad
-- ==================================================================

theorem isBijective_iff_bounded (f A B : HFSet) :
    isBijective f A B ↔ isTotalFunction f A B ∧ isInjective f ∧ isSurjective f B := by
  rfl

instance instDecidableIsBijective (f A B : HFSet) : Decidable (isBijective f A B) :=
  decidable_of_iff _ (isBijective_iff_bounded f A B).symm

end HFSet
