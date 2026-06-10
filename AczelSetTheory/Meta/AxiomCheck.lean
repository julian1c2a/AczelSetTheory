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

-- ─────────────────────────────────────────────────────────────────
-- PENDIENTES (Fase 3 — aún dependen de Classical vía byContradiction/em/
-- propDecidable): HFSet.wf_induction (WellOrder), Combinatorics.pigeonhole,
-- sylow_first, Bezout.*, MobiusLiouville.*, Topology.Interior.*, etc.
-- ─────────────────────────────────────────────────────────────────
