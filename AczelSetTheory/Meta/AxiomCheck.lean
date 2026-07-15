/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Meta/AxiomCheck.lean
-- ════════════════════════════════════════════════════════════════════════════
-- Gate de compilación constructiva EXHAUSTIVO (ADR-018 / estilo Peano
-- `ConstructiveCheck.lean`).  Reescrito 2026-07-15 (ver INFORME-AUDITORIA-2026-07-15.md).
--
-- La versión anterior solo vigilaba ~30 símbolos seleccionados a mano y daba una
-- FALSA sensación de seguridad: una auditoría por barrido exhaustivo encontró 11
-- símbolos con footprint no-constructivo (9 con `Classical.choice`, 2 más con solo
-- `native_decide`) que el gate curado NO cubría.
--
-- Este gate recorre TODA declaración propia de AczelSetTheory (cuyo módulo de
-- definición está bajo `AczelSetTheory.*`) vía `Lean.collectAxioms` y FALLA el build
-- si alguna introduce un axioma fuera del footprint diana `{propext, Quot.sound}`
-- (+ `sorryAx` tolerado como deuda de los 14 `sorry` activos de Rationals/Reals, que
-- el compilador ya avisa aparte), SALVO las excepciones baseline documentadas abajo.
--
-- Detecta el "Classical OCULTO" invisible a `grep 'Classical\.'`:
--   • primitivas del núcleo Lean 4.31 (`String.drop`/`extract`/`toList` → Classical.choice);
--   • `by_cases`/`decide`/`omega`/`simp` sobre una proposición SIN instancia `Decidable`
--     en contexto → `Classical.propDecidable` → `Classical.choice`, sin que la palabra
--     "Classical" aparezca en el código fuente;
--   • `native_decide` (axioma de confianza en el compilador), heredado de Peano.
-- ════════════════════════════════════════════════════════════════════════════

import Lean.Elab.Command
import Lean.Util.CollectAxioms

-- El barrido necesita ver TODAS las declaraciones: se importan todos los barrels de
-- subsistema (los mismos que el barrel raíz `AczelSetTheory.lean`, líneas 11–25),
-- MENOS el propio barrel raíz — que importa este módulo el último — para evitar el ciclo.
import AczelSetTheory.PList
import AczelSetTheory.Axioms
import AczelSetTheory.CList
import AczelSetTheory.Operations
import AczelSetTheory.HFSets
import AczelSetTheory.HFList
import AczelSetTheory.HFListOps
import AczelSetTheory.Notation
import AczelSetTheory.VN
import AczelSetTheory.Algebra
import AczelSetTheory.Integers
import AczelSetTheory.Rationals
import AczelSetTheory.Reals
import AczelSetTheory.Topology
import AczelSetTheory.Combinatorics

set_option autoImplicit false

namespace AczelSetTheory.Meta

open Lean Elab Command

-- ─────────────────────────────────────────────────────────────────
-- Herramienta puntual (se conserva): #assert_no_classical <ident>
-- ─────────────────────────────────────────────────────────────────

/-- Falla en tiempo de compilación si la declaración depende de `Classical.choice`.
    Útil para comprobar un símbolo concreto; el gate real es el barrido exhaustivo
    `#assert_constructive_footprint` de abajo. -/
elab "#assert_no_classical " id:ident : command => do
  let name ← resolveGlobalConstNoOverload id
  let axioms ← Lean.collectAxioms name
  if axioms.contains ``Classical.choice then
    throwError "'{name}' depende de Classical.choice — reescribir constructivamente (ADR-018)"

-- ─────────────────────────────────────────────────────────────────
-- Gate exhaustivo
-- ─────────────────────────────────────────────────────────────────

/-- Axiomas tolerados sin marcar un símbolo como no-constructivo.
    `propext`/`Quot.sound` son el footprint diana (no-clásicos, intuicionistas).
    `sorryAx` se tolera: es la deuda de los 14 `sorry` activos (Rationals/Reals),
    ya avisada por el compilador (`declaration uses sorry`). El gate NO es un
    detector de `sorry` — su cometido es `Classical`/`native_decide` (ADR-018). -/
private def allowedAxioms : List Name := [``propext, ``Quot.sound, ``sorryAx]

/-- BASELINE de excepciones — símbolos con footprint no-constructivo tolerados.
    **✅ VACÍA desde 2026-07-15**: los 11 símbolos de la auditoría original
    (INFORME-AUDITORIA-2026-07-15.md §5.3) están TODOS saneados. Todo el proyecto —
    incluida la dependencia Peano — tiene footprint ⊆ {propext, Quot.sound} (+ sorryAx
    de los 14 sorry activos). El gate FALLA si aparece cualquier violación nueva.

    Historial del saneo (baseline 11 → 0):
    - Clase B nativa (7): `orbitOf_eq_or_disjoint` (inter=∅+nonempty_of_ne_empty),
      `interior_exterior_boundary_partition` (instancias Decidable isInteriorPt/isExteriorPt),
      `mem_wf`+`mem_rank_lt` (import Axioms.Decidable), `get_ext`+`FinList.extEq`
      (dicotomía `Order.lt_or_ge` vs `by_cases` sobre `<` de ℕ₀), `HFMatrixRing` (en cascada).
    - Clase A heredada de Peano (4): `vN_wilson`/`vN_wilson_modEq`/`vN_totient_one`/`vN_totient_two`
      — saneadas AGUAS ARRIBA en Peano (commit `9b6241d`, ADR-017): `Wilson.wilson` (los 3 lemas
      `List.erase` clásicos del core Lean 4.31 reemplazados + native_decide del caso p=3 eliminado)
      y `Totient.totient_{one,two}` (native_decide → prueba constructiva). -/
private def baselineNonConstructive : List Name := []

/-- Barrido exhaustivo: para CADA declaración propia de AczelSetTheory verifica que su
    footprint de axiomas ⊆ `allowedAxioms`. Falla si un símbolo FUERA del baseline tiene
    algún axioma no permitido (Classical.choice, native_decide, etc.); avisa si un símbolo
    DEL baseline ya está limpio (para retirarlo). -/
elab "#assert_constructive_footprint" : command => do
  let env ← getEnv
  let mods := env.header.moduleNames
  let baseline := baselineNonConstructive
  let mut violations : Array (Name × Name) := #[]   -- (símbolo nuevo, axioma ofensor)
  let mut staleBaseline : Array Name := #[]         -- en baseline pero ya limpio
  let mut scanned : Nat := 0
  for (name, _info) in env.constants.toList do
    if name.isInternalDetail then continue
    let some modIdx := env.const2ModIdx[name]? | continue
    unless (`AczelSetTheory).isPrefixOf mods[modIdx.toNat]! do continue
    scanned := scanned + 1
    let axs ← collectAxioms name
    let bad := axs.filter (fun a => !allowedAxioms.contains a)
    let isBaseline := baseline.contains name
    if bad.isEmpty then
      if isBaseline then staleBaseline := staleBaseline.push name
    else
      unless isBaseline do
        for a in bad do
          violations := violations.push (name, a)
  unless staleBaseline.isEmpty do
    logWarning m!"[gate] {staleBaseline.size} excepción(es) del baseline ya están LIMPIAS — retirar de `baselineNonConstructive`:\n{staleBaseline.toList}"
  unless violations.isEmpty do
    throwError m!"[gate] {violations.size} axioma(s) no-constructivo(s) NUEVO(s) fuera del baseline \
      (footprint diana ⊆ propext + Quot.sound (+ sorryAx tolerado)):\n{violations.toList}\n\
      → reescribir constructivamente (ADR-018); o, si es una excepción legítima e \
      inevitable, añadir a `baselineNonConstructive` con su justificación."
  logInfo m!"[gate] OK — {scanned} declaraciones propias verificadas; \
    footprint ⊆ propext + Quot.sound (+ sorryAx) salvo {baseline.length} excepción(es) baseline documentadas."

#assert_constructive_footprint

end AczelSetTheory.Meta
