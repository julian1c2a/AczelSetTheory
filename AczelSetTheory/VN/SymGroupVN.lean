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

open Peano Peano.FSet Peano.FSetFunction

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
-- Tipo de permutaciones del segmento
-- ─────────────────────────────────────────────────────────────────

/-- El tipo de permutaciones biyectivas del segmento {0, 1, …, n-1}. -/
def SymVN (n : ℕ₀) : Type := FunPerm (vnSeg n)

-- ─────────────────────────────────────────────────────────────────
-- Operaciones del grupo simétrico
-- ─────────────────────────────────────────────────────────────────

/-- La permutación identidad del segmento {0, …, n-1}. -/
def SymVN.id (n : ℕ₀) : SymVN n := FunPerm.id (vnSeg n)

/-- Composición de dos permutaciones. El valor por defecto 𝟘 cubre
    elementos fuera del rango (no ocurre en permutaciones válidas). -/
def SymVN.comp (n : ℕ₀) (g f : SymVN n) : SymVN n :=
  Perm.FunPerm.comp g f 𝟘

theorem SymVN.comp_def (n : ℕ₀) (g f : SymVN n) :
    SymVN.comp n g f = Perm.FunPerm.comp g f 𝟘 := rfl

-- ─────────────────────────────────────────────────────────────────
-- Nota de alcance: estructura FinGroup
-- ─────────────────────────────────────────────────────────────────
-- Para construir la estructura de grupo finito se necesita:
-- 1. Enumerar todas las permutaciones como FSet (SymVN n)
-- 2. Probar que card de ese conjunto es factorial n
--    (requiere Perm.card_Sym, no materializado aún en Peano)
-- 3. Verificar los axiomas de grupo: asociatividad, identidad, inversas

end VN
