/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Axioms/CardImage.lean
-- Cardinalidad de imágenes por funciones-clase inyectivas.
--
-- Público:
--   HFSet.card_classImage_inj    : si f : HFSet → HFSet es inyectiva sobre A y
--                                  f(A) ⊆ B, entonces
--                                  card (sep B (λ y, ∃ x ∈ A, y = f x)) = card A
--   HFSet.card_eq_of_classBij    : variante "biyección hacia B"
--                                  si f : HFSet → HFSet es inyectiva sobre A,
--                                  f(A) ⊆ B y todo b ∈ B tiene preimagen en A,
--                                  entonces card A = card B.
--
-- Nota técnica:
--   Trabajamos con "funciones-clase" `f : HFSet → HFSet` (lambdas Lean), no con
--   funciones-como-HFSet (relaciones). Esta versión es la que necesitan los
--   teoremas algebraicos (orbit-stabilizer, conteo de cosetes) donde la función
--   ya viene dada como una expresión en Lean.

import AczelSetTheory.Axioms.Cardinal
import AczelSetTheory.Axioms.Induction
import AczelSetTheory.Axioms.Separation

namespace HFSet

-- ─────────────────────────────────────────────────────────────────
-- §1. Cardinalidad de la imagen-clase de un conjunto bajo
--     una función inyectiva
-- ─────────────────────────────────────────────────────────────────

/-- Si `f : HFSet → HFSet` es una función-clase con `f(A) ⊆ B` e inyectiva sobre
    `A`, entonces el conjunto-imagen `{ y ∈ B | ∃ x ∈ A, y = f x }` tiene la
    misma cardinalidad que `A`. -/
theorem card_classImage_inj
    (f : HFSet → HFSet) (B : HFSet) :
    ∀ A : HFSet,
      (∀ x, x ∈ A → f x ∈ B) →
      (∀ x y, x ∈ A → y ∈ A → f x = f y → x = y) →
      card (sep B (fun y => ∃ x ∈ A, y = f x)) = card A := by
  apply eps_induction
      (fun A =>
        (∀ x, x ∈ A → f x ∈ B) →
        (∀ x y, x ∈ A → y ∈ A → f x = f y → x = y) →
        card (sep B (fun y => ∃ x ∈ A, y = f x)) = card A)
  · -- Base: A = ∅
    intro _ _
    have hempty : sep B (fun y => ∃ x ∈ (empty : HFSet), y = f x) = empty := by
      apply extensionality; intro y
      rw [mem_sep]
      exact ⟨fun ⟨_, x, hx, _⟩ => absurd hx (not_mem_empty x),
             fun hy => absurd hy (not_mem_empty y)⟩
    rw [hempty, card_empty]
  · -- Paso: A = insert b A'
    intro A' b IH hinto hinj
    have hbA : b ∈ insert b A' := mem_insert_self b A'
    have hfb_B : f b ∈ B := hinto b hbA
    have hinto' : ∀ x, x ∈ A' → f x ∈ B :=
      fun x hx => hinto x ((mem_insert x b A').mpr (Or.inr hx))
    have hinj' : ∀ x y, x ∈ A' → y ∈ A' → f x = f y → x = y :=
      fun x y hx hy h => hinj x y
        ((mem_insert x b A').mpr (Or.inr hx))
        ((mem_insert y b A').mpr (Or.inr hy)) h
    by_cases hbA' : b ∈ A'
    · -- b ∈ A': insert b A' = A'
      have heq : insert b A' = A' := by
        apply extensionality; intro x
        rw [mem_insert]
        exact ⟨fun h => h.elim (fun he => he ▸ hbA') id, Or.inr⟩
      rw [heq]
      exact IH hinto' hinj'
    · -- b ∉ A': paso principal
      -- S = sep B (...over insert b A'),  S' = sep B (...over A')
      -- Mostrar S = insert (f b) S' y f b ∉ S'.
      have hS_eq :
          sep B (fun y => ∃ x ∈ insert b A', y = f x) =
            insert (f b) (sep B (fun y => ∃ x ∈ A', y = f x)) := by
        apply extensionality; intro y
        rw [mem_insert, mem_sep, mem_sep]
        constructor
        · rintro ⟨hyB, x, hxA, hy⟩
          rcases (mem_insert x b A').mp hxA with rfl | hxA'
          · exact Or.inl hy
          · exact Or.inr ⟨hyB, x, hxA', hy⟩
        · rintro (rfl | ⟨hyB, x, hxA', hy⟩)
          · exact ⟨hfb_B, b, hbA, rfl⟩
          · exact ⟨hyB, x, (mem_insert x b A').mpr (Or.inr hxA'), hy⟩
      have hfb_not :
          f b ∉ sep B (fun y => ∃ x ∈ A', y = f x) := by
        intro hmem
        rw [mem_sep] at hmem
        obtain ⟨_, x, hxA', hfb_eq⟩ := hmem
        have hxA_in : x ∈ insert b A' := (mem_insert x b A').mpr (Or.inr hxA')
        have hbx : b = x := hinj b x hbA hxA_in hfb_eq
        exact hbA' (hbx ▸ hxA')
      rw [hS_eq, card_insert _ _ hfb_not, IH hinto' hinj',
          card_insert _ _ hbA']

-- ─────────────────────────────────────────────────────────────────
-- §2. Igualdad de cardinales vía biyección clase A → B
-- ─────────────────────────────────────────────────────────────────

/-- Igualdad de cardinales por biyección clase: si `f : HFSet → HFSet` es
    inyectiva sobre `A`, lleva `A` en `B` y todo elemento de `B` tiene
    preimagen en `A`, entonces `card A = card B`. -/
theorem card_eq_of_classBij
    {A B : HFSet} {f : HFSet → HFSet}
    (hf_into : ∀ x, x ∈ A → f x ∈ B)
    (hf_inj  : ∀ x y, x ∈ A → y ∈ A → f x = f y → x = y)
    (hf_surj : ∀ y, y ∈ B → ∃ x ∈ A, y = f x) :
    card A = card B := by
  have hB_eq : sep B (fun y => ∃ x ∈ A, y = f x) = B := by
    apply extensionality; intro y
    rw [mem_sep]
    exact ⟨fun h => h.1, fun hy => ⟨hy, hf_surj y hy⟩⟩
  have hcard := card_classImage_inj f B A hf_into hf_inj
  rw [hB_eq] at hcard
  exact hcard.symm

end HFSet
