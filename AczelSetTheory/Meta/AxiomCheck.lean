/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Meta/AxiomCheck.lean
-- Gate de compilación constructiva (ADR-018 / PLANNING-CONSTRUCTIVE.md).
-- `#assert_no_classical sym` falla el build si `sym` depende de `Classical.choice`.
-- Objetivo de footprint del proyecto: #print axioms ⊆ {propext, Quot.sound}.
--
-- A medida que las fases del plan saneen módulos, se añaden aquí sus símbolos
-- clave. NO está importado en el barrel raíz hasta que la raíz (CList.evalOp,
-- Fase 1) sea constructiva; mientras tanto se compila con
--   lake build AczelSetTheory.Meta.AxiomCheck

import Lean.Elab.Command
import Lean.Util.CollectAxioms

import AczelSetTheory.CList.Basic
import AczelSetTheory.HFSets
import AczelSetTheory.Axioms.Setminus
import AczelSetTheory.Axioms.Function
import AczelSetTheory.Combinatorics.Counting
import AczelSetTheory.Integers.Bezout
import AczelSetTheory.Integers.MobiusLiouville
import AczelSetTheory.Algebra.Sylow
import AczelSetTheory.Axioms.WellOrder

set_option autoImplicit false

namespace AczelSetTheory.Meta

open Lean Elab Command

/-- Falla en tiempo de compilación si la declaración depende de `Classical.choice`. -/
elab "#assert_no_classical " id:ident : command => do
  let name ← resolveGlobalConstNoOverload id
  let axioms ← Lean.collectAxioms name
  if axioms.contains ``Classical.choice then
    throwError "'{name}' depende de Classical.choice — reescribir constructivamente (ADR-018)"

end AczelSetTheory.Meta

-- ─────────────────────────────────────────────────────────────────
-- Símbolos constructivos verificados.
-- ─────────────────────────────────────────────────────────────────

-- Base CList (línea base 2026-06-10)
#assert_no_classical CList.cSize
#assert_no_classical CList.lt

-- Fase 1 (2026-06-10): cimiento saneado al pasar evalOp y el bloque mutuo
-- de transitividad (ExtEq) de medida aritmética ponderada a LEXICOGRÁFICA.
#assert_no_classical CList.evalOp
#assert_no_classical CList.extEq
#assert_no_classical CList.mem
#assert_no_classical CList.subset
#assert_no_classical CList.mem_subset
#assert_no_classical CList.extEq_trans
#assert_no_classical HFSet.subset_iff_forall_mem_clist
#assert_no_classical HFSet.extensionality
#assert_no_classical HFSet.not_mem_empty
#assert_no_classical HFSet.mem_setminus

-- Fase 3 (2026-06-10): conversión de `Classical.byContradiction`/`em` a
-- `Decidable.byContradiction`/`by_cases` decidible en 6 ficheros + cadena McKay.
#assert_no_classical HFSet.setminus_setminus_of_subset
#assert_no_classical HFSet.snd_orderedPair_eq'
#assert_no_classical HFSet.exists_collision_of_card_lt
#assert_no_classical HFSet.eq_of_subset_of_card_eq
#assert_no_classical HFSet.not_surjective_of_card_ne
#assert_no_classical HFAlgebra.cauchy_minimal
#assert_no_classical HFAlgebra.succ_n_dvd_card_mckayFixedPoints

-- Fase 4 (C1 y C2, 2026-06-29): cierre de los últimos obstáculos de decidibilidad.
#assert_no_classical HFSet.wf_induction
#assert_no_classical HFSet.wo_induction
#assert_no_classical HFSet.no_infinite_descent
#assert_no_classical HFAlgebra.sylow_first

-- ─────────────────────────────────────────────────────────────────
-- PENDIENTES (Fase 3):
--   • Heredado de peanolib: módulos no constructivos (FSet/Perm/Sign/…) si se usan.
-- ─────────────────────────────────────────────────────────────────
