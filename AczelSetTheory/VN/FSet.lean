/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/FSet.lean
-- Inmersión de ℕ₀FSet en HFSet mediante vN.
--
-- Convierte un conjunto finito de naturales de Peano (ℕ₀FSet)
-- en un HFSet aplicando vN elemento a elemento.
--
-- Contenido:
--   fsetToHFSet           : ℕ₀FSet → HFSet
--   fsetToHFSet_empty     : fsetToHFSet ℕ₀FSet.empty = ∅
--   fsetToHFSet_singleton : fsetToHFSet (ℕ₀FSet.singleton n) = {vN n}
--   mem_fsetToHFSet       : x ∈ fsetToHFSet S ↔ ∃ n ∈ S, x = vN n
--   vN_mem_fsetToHFSet_iff: vN n ∈ fsetToHFSet S ↔ n ∈ S
--   fsetToHFSet_injective : Function.Injective fsetToHFSet

import AczelSetTheory.VN.Injective
import AczelSetTheory.VN.IsNat
import Peano.PeanoNat.ListsAndSets.FSet

open Peano Peano.FSet

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Definición
-- ─────────────────────────────────────────────────────────────────

/-- Convierte un `ℕ₀FSet` en un `HFSet` aplicando `vN` a cada elemento.
    Resultado: unión de los singletons `{vN n}` para cada `n ∈ S`. -/
def fsetToHFSet (S : ℕ₀FSet) : HFSet :=
  S.elems.foldl (fun acc n => HFSet.union acc (HFSet.singleton (vN n))) HFSet.empty

-- ─────────────────────────────────────────────────────────────────
-- Auxiliar: caracterización de pertenencia vía foldl
-- ─────────────────────────────────────────────────────────────────

private theorem mem_foldl_union_singleton (x : HFSet) (l : List ℕ₀) (acc : HFSet) :
    x ∈ l.foldl (fun a n => HFSet.union a (HFSet.singleton (vN n))) acc ↔
    x ∈ acc ∨ ∃ n ∈ l, x = vN n := by
  induction l generalizing acc with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl_cons, ih, HFSet.mem_union, HFSet.mem_singleton]
    constructor
    · rintro ((hacc | hhead) | ⟨n, hn, hx⟩)
      · exact Or.inl hacc
      · exact Or.inr ⟨h, List.mem_cons_self, hhead⟩
      · exact Or.inr ⟨n, List.mem_cons_of_mem h hn, hx⟩
    · rintro (hacc | ⟨n, hn, hx⟩)
      · exact Or.inl (Or.inl hacc)
      · rcases List.mem_cons.mp hn with rfl | hn'
        · exact Or.inl (Or.inr hx)
        · exact Or.inr ⟨n, hn', hx⟩

-- ─────────────────────────────────────────────────────────────────
-- Propiedades principales
-- ─────────────────────────────────────────────────────────────────

/-- El conjunto vacío se mapea al conjunto vacío. -/
@[simp]
theorem fsetToHFSet_empty : fsetToHFSet ℕ₀FSet.empty = HFSet.empty := rfl

/-- El singleton `{n}` se mapea al singleton `{vN n}`. -/
theorem fsetToHFSet_singleton (n : ℕ₀) :
    fsetToHFSet (ℕ₀FSet.singleton n) = HFSet.singleton (vN n) := by
  have helems : (ℕ₀FSet.singleton n).elems = [n] := rfl
  simp only [fsetToHFSet, helems, List.foldl_cons, List.foldl_nil]
  exact HFSet.empty_union _

/-- Caracterización de pertenencia: `x ∈ fsetToHFSet S ↔ ∃ n ∈ S, x = vN n`. -/
theorem mem_fsetToHFSet (x : HFSet) (S : ℕ₀FSet) :
    x ∈ fsetToHFSet S ↔ ∃ n ∈ S, x = vN n := by
  have h := mem_foldl_union_singleton x S.elems HFSet.empty
  simp only [HFSet.not_mem_empty, false_or] at h
  exact h

/-- Versión orientada: `vN n ∈ fsetToHFSet S ↔ n ∈ S`. -/
theorem vN_mem_fsetToHFSet_iff (n : ℕ₀) (S : ℕ₀FSet) :
    vN n ∈ fsetToHFSet S ↔ n ∈ S := by
  rw [mem_fsetToHFSet]
  constructor
  · rintro ⟨m, hm, heq⟩
    exact vN_injective heq ▸ hm
  · intro hn
    exact ⟨n, hn, rfl⟩

/-- `fsetToHFSet` es inyectiva: conjuntos distintos de ℕ₀ dan HFSets distintos. -/
theorem fsetToHFSet_injective : Function.Injective (fsetToHFSet : ℕ₀FSet → HFSet) := by
  intro S₁ S₂ h
  apply FSet.eq_of_mem_iff'
  intro n
  change n ∈ S₁ ↔ n ∈ S₂
  rw [← vN_mem_fsetToHFSet_iff n S₁, ← vN_mem_fsetToHFSet_iff n S₂]
  exact ⟨fun h' => h ▸ h', fun h' => h.symm ▸ h'⟩

end VN
