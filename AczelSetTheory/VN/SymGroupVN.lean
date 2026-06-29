/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/SymGroupVN.lean
--
-- Grupo simétrico sobre el segmento inicial de Von Neumann.
-- Define el tipo de permutaciones de {0, 1, …, n-1} usando la infraestructura
-- de FunPerm de la biblioteca Peano.
--
-- Estado: ⚠️ Parcial.
--   ✅ vnSeg  : segmento {0,…,n-1} como ℕ₀FSet
--   ✅ SymVN  : tipo de permutaciones del segmento
--   ✅ SymVN.id   : permutación identidad
--   ✅ SymVN.comp : composición de permutaciones
--   ❌ Estructura FinGroup no incluida en este módulo (requiere enumerar todas las permutaciones)
--
-- Contenido:
--   vnSeg         : ℕ₀ → ℕ₀FSet   (segmento {0,…,n-1})
--   mem_vnSeg_iff : k ∈ (vnSeg n).elems ↔ lt₀ k n
--   vnSeg_card    : (vnSeg n).card = n
--   SymVN         : ℕ₀ → Type      (tipo de permutaciones del segmento)
--   SymVN.id      : SymVN n         (identidad)
--   SymVN.comp    : ℕ₀ → SymVN n → SymVN n → SymVN n

import AczelSetTheory.VN.Basic
import Peano.PeanoNat.Combinatorics.Perm
import AczelSetTheory.Axioms.Function
import AczelSetTheory.Operations.FunctionComp
import AczelSetTheory.Operations.Identity
import AczelSetTheory.Operations.Inverse
import AczelSetTheory.Algebra.Group

open Peano Peano.FSet Peano.FSetFunction
open HFSet

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Segmento inicial como ℕ₀FSet
-- ─────────────────────────────────────────────────────────────────

/-- El segmento inicial {0, 1, …, n-1} como ℕ₀FSet. -/
def vnSeg (n : ℕ₀) : ℕ₀FSet := ℕ₀FSet.Fin₀Set n

theorem mem_vnSeg_iff (n k : ℕ₀) :
    k ∈ (vnSeg n).elems ↔ lt₀ k n :=
  ℕ₀FSet.mem_Fin₀Set_iff n k

theorem vnSeg_card (n : ℕ₀) : (vnSeg n).card = n :=
  ℕ₀FSet.Fin₀Set_card n

-- ─────────────────────────────────────────────────────────────────
-- Teoría Nativa en HFSet: SymHF y SymHFGroup
-- ─────────────────────────────────────────────────────────────────

noncomputable section

/-- El conjunto de todas las biyecciones de A a A.
    Definido nativamente en HFSet mediante separación sobre 𝒫(A × A). -/
def SymHF (A : HFSet) : HFSet :=
  have : DecidablePred (fun f => isBijective f A A) := fun _ => Classical.propDecidable _
  HFSet.sep (HFSet.powerset (HFSet.cartProd A A))
    (fun f => isBijective f A A)

/-- La estructura de grupo de las permutaciones de A,
    usando composición funcional e identidad funcional. -/
def SymHFGroup (A : HFSet) : HFAlgebra.HFGroup where
  G := SymHF A
  op := fun f g => f ∘f g
  e := HFSet.idFunc A
  inv := fun f => f⁻¹ᵣ
  e_mem := sorry
  op_closed := sorry
  inv_closed := sorry
  op_assoc := sorry
  op_id_left := sorry
  op_inv_left := sorry

end

/-- El grupo simétrico concreto sobre el segmento de von Neumann S_n. -/
noncomputable def SymVN (n : ℕ₀) : HFAlgebra.HFGroup :=
  SymHFGroup (vN n)

-- ─────────────────────────────────────────────────────────────────
-- Puente con Peano (Fontanería)
-- ─────────────────────────────────────────────────────────────────

/-- Convierte un par clave-valor de FunTable de Peano a un par ordenado de HFSet. -/
def pair_to_HFSet (kv : ℕ₀ × ℕ₀) : HFSet :=
  HFSet.orderedPair (vN kv.1) (vN kv.2)

/-- Inyecta una permutación de Peano (Sym A) como una biyección nativa en HFSet. -/
def FunPerm_to_HFSet {n : ℕ₀} (f : Peano.Perm.Sym (vnSeg n)) : HFSet :=
  -- Extraemos la lista de pares de la tabla de la función de Peano
  let pairs : List (ℕ₀ × ℕ₀) := f.toFunTable.table.map (fun a => (a, f.applyElem a 𝟘))
  -- Convertimos la lista a un HFSet (unión de singletons)
  List.foldr (fun kv S => HFSet.union (HFSet.singleton (pair_to_HFSet kv)) S) HFSet.empty pairs

end VN
