/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Axioms.Composition
import AczelSetTheory.Axioms.FunctionComp
import AczelSetTheory.Axioms.Identity
import AczelSetTheory.Axioms.Intersection
import AczelSetTheory.Axioms.Union

namespace HFSet

-- ==================================================================
-- Propiedades básicas de imageRel para funciones
-- ==================================================================

/-- La imagen de cualquier conjunto está contenida en el rango de la relación. -/
theorem imageRel_subset_range {f A : HFSet} :
    imageRel f A ⊆ range f := by
  intro b hb
  rw [mem_imageRel] at hb
  obtain ⟨a, _, hab⟩ := hb
  exact (mem_range_iff f b).mpr ⟨a, hab⟩

/-- La imagen es monótona en el conjunto fuente:
    A ⊆ B → imageRel f A ⊆ imageRel f B. -/
theorem imageRel_mono {f A B : HFSet} (h : A ⊆ B) :
    imageRel f A ⊆ imageRel f B := by
  intro b hb
  rw [mem_imageRel] at hb ⊢
  obtain ⟨a, haA, hab⟩ := hb
  exact ⟨a, h a haA, hab⟩

/-- La imagen se distribuye sobre la unión:
    imageRel f (A ∪ B) = imageRel f A ∪ imageRel f B. -/
theorem imageRel_union {f A B : HFSet} :
    imageRel f (union A B) = union (imageRel f A) (imageRel f B) := by
  apply extensionality; intro b
  constructor
  · intro hb
    rw [mem_imageRel] at hb
    obtain ⟨a, haAB, hab⟩ := hb
    rw [mem_union a A B] at haAB
    rw [mem_union b (imageRel f A) (imageRel f B)]
    cases haAB with
    | inl h => exact Or.inl (mem_imageRel.mpr ⟨a, h, hab⟩)
    | inr h => exact Or.inr (mem_imageRel.mpr ⟨a, h, hab⟩)
  · intro hb
    rw [mem_union b (imageRel f A) (imageRel f B)] at hb
    rw [mem_imageRel]
    cases hb with
    | inl h =>
      rw [mem_imageRel] at h
      obtain ⟨a, haA, hab⟩ := h
      exact ⟨a, (mem_union a A B).mpr (Or.inl haA), hab⟩
    | inr h =>
      rw [mem_imageRel] at h
      obtain ⟨a, haB, hab⟩ := h
      exact ⟨a, (mem_union a A B).mpr (Or.inr haB), hab⟩

/-- La imagen del dominio completo es el rango:
    imageRel f (domain f) = range f. -/
theorem imageRel_domain_eq_range {f : HFSet} :
    imageRel f (domain f) = range f := by
  apply extensionality; intro b
  constructor
  · intro hb
    rw [mem_imageRel] at hb
    obtain ⟨a, _, hab⟩ := hb
    exact (mem_range_iff f b).mpr ⟨a, hab⟩
  · intro hb
    rw [mem_range_iff] at hb
    obtain ⟨a, hab⟩ := hb
    rw [mem_imageRel]
    exact ⟨a, (mem_domain_iff f a).mpr ⟨b, hab⟩, hab⟩

/-- La imagen permanece dentro del codominio para funciones totales:
    isTotalFunction f dom cod → ∀ A, imageRel f A ⊆ cod. -/
theorem imageRel_codomain {f dom cod : HFSet}
    (hf : isTotalFunction f dom cod) (A : HFSet) :
    imageRel f A ⊆ cod := by
  intro b hb
  rw [mem_imageRel] at hb
  obtain ⟨a, _, hab⟩ := hb
  exact hf.2.2 b ((mem_range_iff f b).mpr ⟨a, hab⟩)

-- ==================================================================
-- Composición e identidad
-- ==================================================================

/-- La imagen conmuta con la composición funcional:
    imageRel (f ∘f g) A = imageRel f (imageRel g A). -/
theorem imageRel_funComp {f g A : HFSet} :
    imageRel (f ∘f g) A = imageRel f (imageRel g A) := by
  apply extensionality; intro b
  constructor
  · intro hb
    rw [mem_imageRel] at hb
    obtain ⟨a, haA, hb'⟩ := hb
    rw [mem_funComp_pair] at hb'
    obtain ⟨c, hag, hcf⟩ := hb'
    rw [mem_imageRel]
    exact ⟨c, mem_imageRel.mpr ⟨a, haA, hag⟩, hcf⟩
  · intro hb
    rw [mem_imageRel] at hb
    obtain ⟨c, hcgA, hcf⟩ := hb
    rw [mem_imageRel] at hcgA
    obtain ⟨a, haA, hag⟩ := hcgA
    rw [mem_imageRel]
    exact ⟨a, haA, mem_funComp_pair.mpr ⟨c, hag, hcf⟩⟩

/-- La imagen bajo la función identidad es la intersección con el dominio:
    imageRel (idFunc A) B = B ∩ A. -/
theorem imageRel_idFunc {A B : HFSet} :
    imageRel (idFunc A) B = inter B A := by
  apply extensionality; intro b
  constructor
  · intro hb
    rw [mem_imageRel] at hb
    obtain ⟨c, hcB, hcb⟩ := hb
    rw [mem_idFunc_pair] at hcb
    exact (mem_inter B A b).mpr ⟨hcb.1 ▸ hcB, hcb.1 ▸ hcb.2⟩
  · intro hb
    rw [mem_inter] at hb
    rw [mem_imageRel]
    exact ⟨b, hb.1, mem_idFunc_pair.mpr ⟨rfl, hb.2⟩⟩

end HFSet
