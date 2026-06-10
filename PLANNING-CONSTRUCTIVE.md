# Plan — Pureza constructiva (cero `Classical`) + ℕ₀/peanolib puro

**Creado:** 2026-06-10
**Autor:** Julián Calderón Almendros
**Estado:** 🟢 EN EJECUCIÓN (arranque Fase 0+1)
**Decisión asociada:** [ADR-018](DECISIONS.md)

> **Objetivo:** `#print axioms` de todo símbolo ⊆ `{propext, Quot.sound}` (cero `Classical.*`),
> y dependencia matemática exclusiva de `ℕ₀`/peanolib (nunca `Nat` de Lean salvo kernel).

---

## 1. Diagnóstico verificado (2026-06-10)

| Hecho | Evidencia (`#print axioms`) |
|---|---|
| peanolib es constructivo | `Peano.Add.add_comm → [propext]`; `Peano.Order.le_total → sin axiomas` |
| WF-recursion no es clásica per se | `def f` (term. `Nat`) → `[propext]`; `tsize` (term. `sizeOf` anidado) → `[propext, Quot.sound]` |
| `CList.lt` (medida `sizeOf` pura) es limpio | `[propext, Quot.sound]` |
| **Raíz**: `CList.evalOp` (medida ponderada `sizeOf·3 + opWeight`) | `[propext, Classical.choice, Quot.sound]` |
| Herencia universal | `extEq`, `extensionality`, `pigeonhole`, `HFMatrixRing`, `choose` → todos con `Classical.choice` |
| **Fix axiom-free**: split estructural `mem`/`subset`/`eq` | experimento standalone → *"does not depend on any axioms"* |

**Causa raíz:** el paso `.eq→.subset` de `evalOp` mantiene el argumento estructural y solo
decrece el peso `opWeight`; la terminación por medida aritmética no-estructural sobre `Nat`
es lo que arrastra `Classical.choice`. **Fix:** `eq A B := subset A B && subset B A` (no
recursivo); `subset` recurre estructural sobre el 1er arg llamando a `mem`; `mem` recurre
sobre `A`. Ninguna necesita `termination_by` ponderado.

---

## 2. Inventario de focos

### 2.1 Raíz estructural (Fase 1)

- [`CList/Basic.lean`](AczelSetTheory/CList/Basic.lean): `evalOp` → `mem`/`subset`/`eq`.
- Reparaciones en cascada: `CList/{ExtEq, SetEquiv, Order, Sort, Normalize}`, `HFSets.lean`.

### 2.2 `Classical.*` explícito — 8 ficheros

| Fichero | Uso | Dificultad |
|---|---|---|
| `Axioms/Setminus.lean` | `byContradiction` ×1 | baja |
| `Axioms/Function.lean` | `em` ×1 | baja |
| `Topology/Interior.lean` | `byContradiction` ×1 | baja |
| `Combinatorics/Counting.lean` | `byContradiction` ×6 | media |
| `Integers/Bezout.lean` | `byContradiction` ×2 | media |
| `Integers/MobiusLiouville.lean` | `byContradiction` ×1 | media |
| `Axioms/WellOrder.lean` | `byContradiction` + `propDecidable` ×6 | media-alta (predicados `P : HFSet→Prop`) |
| `Algebra/Sylow.lean` | `byContradiction` ×3 | alta (módulo denso) |

(`VN/QuotientGroupVN.lean:30` = comentario obsoleto, no uso real → corregir.)
(`Axioms/Choice.lean` tiene `open Classical` pero `choose` ya es `def` computable.)

### 2.3 `Nat`/`sizeOf` → ℕ₀/`cSize` (Fase 2)

- `termination_by … sizeOf … : Nat` en `CList/{Basic, ExtEq, Normalize, Order, Sort}`, `Integers/{Bezout, PadicVal}`.
- `Nat` explícito en 10 ficheros (incl. `HFMatrix`, `OrdinalNat`, `VN/Arithmetic`, `PList/{Lemmas,Omega0}`).
- Reemplazo: `cSize : ℕ₀` + `omega₀`. Excepciones técnicas inevitables se listan en §5.

---

## 3. Fases

| Fase | Contenido | Salida | Estado |
|---|---|---|---|
| **0** | Verificador `#assert_no_classical` (`Lean.collectAxioms`) | `AczelSetTheory/Meta/AxiomCheck.lean` | ✅ 2026-06-10 |
| **1** | Saneo de la raíz: medidas de terminación **lexicográficas** en vez de aritméticas ponderadas | `evalOp`/`extEq`/`extensionality` y axiomas Zermelo limpios; `Classical.choice` deja de ser universal | ✅ 2026-06-10 |
| **2** | Medidas de terminación a `cSize`/ℕ₀ + erradicar `Nat` evitable | 0 `Nat` salvo excepciones §5 | ⏳ |
| **3** | Eliminar `Classical.*` en los 8 ficheros (orden por dificultad) | 0 `Classical.*` en fuente | ⏳ |
| **4** | Cierre: ampliar gate a todo el árbol, comentario QuotientGroupVN, docs, AUDIT-MATRIX con columna `Classical.choice` | invariante constructivo activo | 🟡 parcial (gate en barrel raíz) |

> **Hallazgo clave de Fase 1 (revisa el diagnóstico):** la causa NO era la WF-recursion
> ni `sizeOf` ni `Nat`, sino la **codificación aritmética ponderada** de la medida
> (`(sizeOf·k)+peso`). Experimento decisivo: `termination_by (n*3 + w op)` →
> `Classical.choice`; `termination_by (n, w op)` (lexicográfica) → `[propext, Quot.sound]`.
> **Fix quirúrgico, sin reescribir cuerpos:** pasar las dos medidas ponderadas
> (`CList.evalOp` y el bloque mutuo de transitividad en `CList/ExtEq.lean`) a medidas
> **lexicográficas** `(Σ sizeOf, fase)`. Resultado: cimiento `CList`→`HFSet` constructivo;
> `Classical.choice` queda **localizado** en los 8 ficheros de Fase 3. Build 242 jobs ✅.

---

## 4. Estrategia de conversión de `Classical` → constructivo

En HF casi todo predicado es **decidible** (membership/subset/eq son `Bool`). Patrones:

- `Classical.byContradiction (fun h => …)` con `P` decidible → `Decidable.byContradiction` o
  `by_cases h : P` constructivo vía la instancia `Decidable P`.
- `Classical.em P` → `Decidable.em P` / `if h : P then … else …`.
- `Classical.propDecidable` → aportar la instancia `Decidable`/`DecidablePred` real (en HF existe).
- `Axioms/WellOrder`: minimización por `cSize` (rango ℕ₀ bien fundado, constructivo) en lugar de
  `propDecidable` sobre `P` arbitrario; o exigir `[DecidablePred P]`.

---

## 5. Excepciones técnicas de `Nat` (a confirmar durante ejecución)

`Nat` solo permitido, aislado y documentado, en:

- `sizeOf` del kernel cuando un `termination_by` estructural no sea expresable con `cSize`
  (objetivo: que NO ocurra; `cSize` debería bastar).
- Literales/índices internos de tácticas (`omega`, `decide`) — preferir `omega₀`.
- Interfaz con APIs de Lean core que devuelven `Nat` (minimizar; envolver en ℕ₀ vía `Λ`/`Ψ`).

Cualquier `Nat` superviviente queda registrado aquí con su justificación.

---

## 6. Invariante y verificación

- Tras cada fase: `lake build AczelSetTheory` (0 errores/warnings) **y** `#assert_no_classical`
  sobre símbolos clave (extensionality, vN, HFMatrixRing, sylow_first…).
- Meta final: el gate `#assert_no_classical` cubre todo el árbol y falla el build ante cualquier
  regresión a `Classical.choice`.

---

*Documento vivo. Actualizar tras cada fase con símbolos saneados y excepciones registradas.*
