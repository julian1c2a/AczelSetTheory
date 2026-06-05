/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Axioms/Ordinal.lean
-- Ordinales de Von Neumann dentro de HFSet.
--
-- Definición:  isOrdinal A  :=  isTransSet A  ∧  tricotomía de ∈ en A
--
-- Público:
--   isOrdinal            : HFSet → Prop
--   isOrdinal_empty      : isOrdinal ∅
--   isOrdinal_succ       : isOrdinal A → isOrdinal (succ A)
--   isNat_isOrdinal      : isNat A → isOrdinal A
--   isOrdinal_mem        : isOrdinal A → x ∈ A → isOrdinal x
--
-- Nota: isOrdinal A ↔ isNat A en HFSet (los únicos ordinales en V_ω son
-- los naturales de Von Neumann), pero la dirección isOrdinal → isNat requiere
-- infraestructura de cardinalidad adicional y se dejará para un módulo futuro.

import AczelSetTheory.Axioms.VonNeumann
import AczelSetTheory.Axioms.Induction

namespace HFSet

-- ==================================================================
-- Definición
-- ==================================================================

/-- Un conjunto es un ordinal de Von Neumann si es transitivo y
    la relación de pertenencia satisface tricotomía en él. -/
def isOrdinal (A : HFSet) : Prop :=
  isTransSet A ∧ ∀ x y, x ∈ A → y ∈ A → x ∈ y ∨ x = y ∨ y ∈ x

-- ==================================================================
-- Lema auxiliar de fundación: imposibilidad de ciclos de longitud 3
-- ==================================================================

/-- No puede haber ciclos de pertenencia de longitud 3:
    A ∈ B, B ∈ C, C ∈ A es imposible. -/
private theorem no_mem_cycle3 (A B C : HFSet)
    (hAB : A ∈ B) (hBC : B ∈ C) (hCA : C ∈ A) : False := by
  -- El conjunto testigo S = {A, B, C}
  have hS_ne : insert A (insert B (singleton C)) ≠ empty := insert_ne_empty A _
  obtain ⟨x, hx_mem, hx_disj⟩ :=
    foundation (insert A (insert B (singleton C))) hS_ne
  -- Clasificamos x según si es A, B, o C
  rcases (mem_insert x A (insert B (singleton C))).mp hx_mem with hxA | hx_rest
  · -- x = A  ⟹  C ∈ x (por hCA) y C ∈ S
    -- hxA : x = A
    -- hCA : C ∈ A   →   C ∈ x  (reescribiendo A por x)
    have hCx : C ∈ x := hxA.symm ▸ hCA
    have hCS : C ∈ insert A (insert B (singleton C)) :=
      (mem_insert C A (insert B (singleton C))).mpr (Or.inr
        ((mem_insert C B (singleton C)).mpr (Or.inr
          ((mem_singleton C C).mpr rfl))))
    exact hx_disj C hCx hCS
  · rcases (mem_insert x B (singleton C)).mp hx_rest with hxB | hx_sing
    · -- x = B  ⟹  A ∈ x (por hAB) y A ∈ S
      have hAx : A ∈ x := hxB.symm ▸ hAB
      have hAS : A ∈ insert A (insert B (singleton C)) :=
        (mem_insert A A (insert B (singleton C))).mpr (Or.inl rfl)
      exact hx_disj A hAx hAS
    · -- x = C  ⟹  B ∈ x (por hBC) y B ∈ S
      have hxC : x = C := (mem_singleton x C).mp hx_sing
      have hBx : B ∈ x := hxC.symm ▸ hBC
      have hBS : B ∈ insert A (insert B (singleton C)) :=
        (mem_insert B A (insert B (singleton C))).mpr (Or.inr
          ((mem_insert B B (singleton C)).mpr (Or.inl rfl)))
      exact hx_disj B hBx hBS

-- ==================================================================
-- Teoremas principales
-- ==================================================================

theorem isOrdinal_empty : isOrdinal empty :=
  ⟨isTransSet_empty, fun x _ hx => absurd hx (not_mem_empty x)⟩

theorem isOrdinal_succ {A : HFSet} (hA : isOrdinal A) : isOrdinal (succ A) := by
  obtain ⟨hT, htri⟩ := hA
  refine ⟨isTransSet_succ A hT, ?_⟩
  intro x y hx hy
  rcases (mem_succ x A).mp hx with hxA | hxeqA
  · -- x ∈ A
    rcases (mem_succ y A).mp hy with hyA | hyeqA
    · -- y ∈ A: tricotomía en A
      exact htri x y hxA hyA
    · -- y = A: x ∈ A = y  →  x ∈ y
      exact Or.inl (hyeqA.symm ▸ hxA)
  · -- x = A
    rcases (mem_succ y A).mp hy with hyA | hyeqA
    · -- y ∈ A = x  →  y ∈ x
      exact Or.inr (Or.inr (hxeqA.symm ▸ hyA))
    · -- y = A = x  →  x = y
      exact Or.inr (Or.inl (hxeqA.trans hyeqA.symm))

/-- Todo natural de Von Neumann es un ordinal. -/
theorem isNat_isOrdinal {n : HFSet} (hn : isNat n) : isOrdinal n := by
  induction hn with
  | zero  => exact isOrdinal_empty
  | succ _ ih => exact isOrdinal_succ ih

/-- Los elementos de un ordinal son ordinales. -/
theorem isOrdinal_mem {A x : HFSet} (hA : isOrdinal A) (hx : x ∈ A) : isOrdinal x := by
  obtain ⟨hT, htri⟩ := hA
  -- x ⊆ A (ya que A es transitivo y x ∈ A)
  have hxA : x ⊆ A := hT x hx
  constructor
  · -- Transitividad de x: z ∈ x → z ⊆ x
    intro z hz
    -- z ∈ x ⊆ A
    have hzA : z ∈ A := hxA z hz
    -- z ⊆ A (A transitivo, z ∈ A)
    have hzA' : z ⊆ A := hT z hzA
    -- ∀ w ∈ z, w ∈ x
    intro w hw
    have hwA : w ∈ A := hzA' w hw
    -- Tricotomía de A sobre w y x
    rcases htri w x hwA hx with h | h | h
    · exact h  -- w ∈ x ✓
    · -- h : w = x ⟹ x ∈ z y z ∈ x, ciclo de longitud 2
      exact absurd (h ▸ hw) (no_mem_cycle2 z x hz)
    · -- h : x ∈ w, hw : w ∈ z, hz : z ∈ x → ciclo de longitud 3
      exact (no_mem_cycle3 x w z h hw hz).elim
  · -- Tricotomía en x: u, v ∈ x → u ∈ v ∨ u = v ∨ v ∈ u
    intro u v hu hv
    exact htri u v (hxA u hu) (hxA v hv)

end HFSet
