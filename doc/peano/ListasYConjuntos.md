# Refactorización de Listas y Conjuntos en Peano

*Última actualización: 2026-04-27*

Este documento registra la estrategia de refactorización arquitectónica para los módulos de listas y conjuntos. Las Fases 1–3 están **completadas**. La Fase 4 es trabajo futuro.

---

## Estado de fases

| Fase | Descripción | Estado |
|------|-------------|--------|
| 1 | Consolidación: ListList.lean → List.lean | ✅ DONE (2026-04-27) |
| 2 | StrictLinearOrder α typeclass | ✅ DONE (2026-04-27) |
| 3 | sortedInsert y FSet genéricos | ✅ DONE (2026-04-27) |
| 4 | UnivVal — universo recursivo | ❌ Futuro |

---

## Fase 1 — Consolidación ✅

`ListList.lean` solo añadía instancias de typeclasses a tipos ya definidos en `List.lean`, fragmentando la definición de los tipos de sus comportamientos.

**Acciones realizadas:**
- Todas las secciones de `ListList.lean` (§11–15: instancias LE, LT, DecidableRel, Repr) movidas al final de `List.lean`.
- `ListList.lean` eliminado.
- Imports actualizados. Build: 52 → 51 jobs.

Análogamente, `FSetFSet.lean` fusionado en `FSet.lean`.

---

## Fase 2 — StrictLinearOrder ✅

`sortedInsert` en `FSet.lean` estaba acoplado a `ℕ₀` por depender de tricotomía y transitividad específicas de naturales.

**Acciones realizadas:**
- `StrictLinearOrder α` typeclass definida en `StrictOrder.lean`: campos `decLt`, `irrefl`, `trans`, `trich`.
- Asimetría derivada como lema (irrefl + trans → asymm).
- `instIrreflLTOfSLO`: instancia bridge `IrreflLT α` desde `StrictLinearOrder α`.
- Instancias para `ℕ₀`, `Tuple ℕ₀ n`: `instStrictLinearOrderTuple`.
- Torre de tipos verificada en `TestTorre.lean`: `FSet (Tuple ℕ₀ n)`, `List (FSet (List ℕ₀))`, `FSet (FSet ℕ₀)`, etc.

---

## Fase 3 — FSet genérico ✅

**Acciones realizadas:**
- `sortedInsert {α : Type} [LT α] [DecidableEq α] [StrictLinearOrder α] : α → List α → List α` en `List.lean`.
- `sorted_sortedInsert` y `mem_sortedInsert_iff` generalizados.
- `FSet α` genérico para cualquier `α` con `StrictLinearOrder α`.
- `FinGroup (α) [DecidableEq α] [LT α] [StrictLinearOrder α]` con `carrier : FSet α` (ver ADR-010).

---

## Fase 4 — UnivVal (futuro) ❌

`PeanoVal` codifica manualmente cada nivel de anidamiento, causando explosión combinatoria en `DecidableEq` y `LT` (36 casos). Propuesta futura:

```lean4
inductive UnivVal {α α₁ α₂ : Type} : Type where
  | ofScalar (lvl : Level) (x : Level.toType lvl) : UnivVal
  | ofTuple  (n : ℕ₀) (t : Tuple n)               : UnivVal
  | ofList   (xs : List UnivVal)                   : UnivVal
```

**Cuándo**: Después de completar la ruta Wielandt y cerrar los axiomas privados de Sylow. Es trabajo independiente de la combinatoria.
