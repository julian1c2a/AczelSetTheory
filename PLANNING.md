# PLANNING — AczelSetTheory

**Last updated:** 2026-06-02
**Author:** Julián Calderón Almendros

> Plan de largo plazo para AczelSetTheory. Cada fase es ejecutable de forma
> independiente. Las dependencias entre fases están marcadas explícitamente.
> El detalle inmediato vive en NEXT_STEPS.md.
>
> **Contexto histórico**: El proyecto predecesor Peano fue puesto en feature-freeze
> el 2026-05-10. Su hoja de ruta original se conserva en
> [doc/peano/INTUICIONES.md](doc/peano/INTUICIONES.md) y la documentación de
> referencia de sus módulos en `doc/REFERENCE-{Arithmetic,Combinatorics,Foundation,
> GroupTheory,ListsAndSets,NumberTheory,Prelim}.md`.

---

## ⚠️ Directiva maestra (2026-05-30): Peano congelado — teoría nueva en Aczel

**Peano (`peanolib`) no desarrollará más teoría "hacia arriba".** Solo se admite trabajo
fundacional/metamatemático: la aritmética de Robinson `Q` y su extensión
**ROBINSON_PlusPlus**. **Toda la teoría matemática nueva** (conteo, signatura de
permutaciones, álgebra adicional, topología, …) se construye **directamente sobre `HFSet`
en AczelSetTheory**, en la capa nativa — *no* vía el transporte `congrArg vN` de los
módulos `VN/`. La combinatoria nueva vive en `AczelSetTheory/Combinatorics/` (paralela a
`Algebra/`, `Topology/`). Los stubs `VN/CountingVN.lean`, `VN/SignVN.lean` (espejos de
stubs de Peano que ya no se materializarán) son huérfanos → re-etiquetar o retirar.
Ver `DECISIONS.md` → ADR-000.

---

## ✅ Check-in (2026-06-02) — Sprint C1/C2 cerrado

- Cierre de deuda textual `TODO/PEND/FIXME` en:
  - `Topology/{Basic,Interior,Neighborhoods,Separation,Subspace}.lean`
  - `Algebra/Sylow.lean`
  - `Algebra/Action.lean`
  - `VN/{ActionVN,CorrespondenceTheoremVN,PermVN,SymGroupVN}.lean`
- Auditoría regenerada: `AUDIT-MODULE-MATRIX.md` con `noncomputable def: 0` y `TODO/PEND/FIXME: 0` en `.lean`.
- Riesgo residual priorizado: `placeholder/stub` en módulos VN de paridad.

## ✅ Check-in (2026-06-02) — Sprint D1 (bloque VN inicial) cerrado

- Reducción de `placeholder/stub` en:
  - `VN/PermVN.lean`
  - `VN/OrbitVN.lean`
  - `VN/CountingVN.lean`
  - `VN/SignVN.lean`
- Auditoría regenerada bloque a bloque en `AUDIT-MODULE-MATRIX.md`.
- Nuevo residual global: `Modulos con placeholder/stub: 7`.

## ✅ Check-in (2026-06-02) — Sprint D2 (bloque VN residual) cerrado

- Reducción final de `placeholder/stub` en:
  - `VN/ActionVN.lean`
  - `VN/CorrespondenceTheoremVN.lean`
  - `VN/FirstIsomorphismVN.lean`
  - `VN/SecondIsomorphismVN.lean`
  - `VN/ThirdIsomorphismVN.lean`
  - `VN/QuotientGroupVN.lean`
  - `VN/NormalSubgroupVN.lean`
- Auditoría regenerada tras cada cierre individual en `AUDIT-MODULE-MATRIX.md`.
- Nuevo residual global: `Modulos con placeholder/stub: 0`.

### Reestimación rápida

- Paridad base cerrada para métricas de `TODO/PEND/FIXME`.
- Paridad base cerrada para métricas de `placeholder/stub` en VN.
- Próximo hito operativo: retomar extensiones de Fase B (paridad sustantiva pendiente y teoría nueva nativa en `Combinatorics/`).

---

## 🎯 Tesis del proyecto (2026-05-29)

> **AczelSetTheory debe recubrir completamente todos los teoremas de Peano**, y
> extenderlos hacia teorías que Peano no podía expresar (axiomática Zermelo,
> álgebra abstracta, topología, jerarquía aritmética). El criterio de éxito es:
> *para cada teorema `T` demostrado en Peano sobre `ℕ₀`, existe un teorema
> equivalente `T_vN` (o `T_HF`) demostrado en AczelSetTheory*.

Esta tesis se refleja en `doc/REFERENCE-Paridad-Peano-Aczel.md` como tabla viva.

### Estado de paridad (2026-05-29)

| Bloque | ✅ Portado | ⚠️ Parcial | ❌ Pendiente |
|---|---|---|---|
| Aritmética base + orden (§1) | 17/18 | 1 (WellFounded) | 0 |
| Combinatoria numérica (§2) | 7/12 | 0 | 5 (Counting, Perm, Sign, Orbit, …) |
| GroupTheory (§3) | 18 abstractos ✅ | 0 ⚠️ | 0 ❌ |
| Teoría de números (§4) | 5/5 | 0 | 0 |
| Fundamentos (§5) | 5/5 | 0 | 0 |
| Listas/Conjuntos finitos (§6) | 3/3 | 1 (EquivRel) | 0 |
| Enteros (§7) | 7 módulos | 0 | 0 |

**Total estimado:** ~46 ✅ / ~2 ⚠️ / ~8 ❌ sobre ~56 módulos sustantivos de Peano.

> Avance respecto a 2026-06-03: GroupTheory §3 pasó a
> `17 abstractos ✅ / 0 ⚠️ / 1 ❌` tras completar Sylow I y Sylow II (`sylowConjugate`, sorry
> cerrado vía teorema del punto fijo del p-grupo, 2026-06-04).

---

## Principios de diseño

1. **Computabilidad estricta en HFSet.** Todo lo que se define debe ser
   computable. Se evitan `noncomputable` y `Classical` salvo que la teoría
   lo exija inevitablemente (p.ej. Axioma de Elección ya probado).
2. **Pureza fundacional.** El proyecto no depende de Mathlib ni del core de
   Lean para sus *pruebas*. Se puede usar el núcleo de Lean para *tipos*
   (inductivos, `Type`, `Prop`, `Sort`) pero los lemas se prueban aquí.
3. **ℕ₀ como natural propio.** El tipo `ℕ₀` de Peano es el natural canónico
   del proyecto. `Nat` de Lean solo aparece como tipo técnico de apoyo donde
   sea estrictamente inevitable.
4. **Notaciones:** `vN` para la función de von Neumann, `VN` para su
   namespace. Los constructores de `ℕ₀`: `𝟘` (zero), `σ n` (succ).
5. **Paridad antes que extensión.** *(Nuevo, 2026-05-28)* Cerrar paridad
   Peano tiene prioridad sobre añadir teorías nuevas en HFSet (anillos no
   conmutativos, módulos avanzados, topología algebraica…). Razón: el valor
   del proyecto descansa en ser *superconjunto verificado* de Peano.

---

## Hoja de ruta a largo plazo (PROPUESTA 2026-05-28)

### 🅰️ FASE A — Cierre de Paridad Peano (próximas ~14–18 sesiones)

Detalle táctico en `NEXT_STEPS.md`. Orden de ejecución aprobado (2026-05-28):

1. **M1** — H1 Counting.
2. **M4 (1ª parte)** — H6 NormalSubgroup (puente VN) *[adelantado para desbloquear M5]*.
3. **M2** — H2 Perm + H3 Sign *(paralelizable con M3)*.
4. **M3** — H5 Action + H4 Orbit.
5. **M4 (2ª parte)** — H7 QuotientGroup.
6. **M5** — H8/H9/H10 bundle `IsomorphismsVN.lean` + H11 Correspondence separado.
7. **M6** ✅ — H13/H14/H15 Sylow. *(Sylow I 2026-06-03: `sylow_first` ✅; Sylow II 2026-06-04: `sylowConjugate` ✅ — sorry cerrado con teorema punto fijo del p-grupo; Sylow III ✅)*
8. **M7** ✅ — H12 Zassenhaus. *(2026-06-05: `zassenhaus_bijection` ✅, build limpio en `AczelSetTheory.Algebra.Zassenhaus`).*
9. **MFUTURE** — Schreier, Jordan-Hölder (fuera del alcance de paridad; aplazados).

**🎉 FASE A COMPLETA (2026-06-05):** Todos los milestones M1–M7 cerrados. La paridad Peano queda cerrada en §1–§7.

**Criterio de cierre:** tabla §1–§7 del REFERENCE de paridad con 0 ❌.

### 🅱️ FASE B — Consolidación post-paridad (~6–8 sesiones)

Una vez cerrada la paridad, atacar las extensiones naturales que Peano no podía expresar pero que cierran el discurso aritmético:

1. **B1. ℚ₀ extendido**: densidad, completitud parcial, valor absoluto, métrica `|p−q|`.
2. **B2. Bridge `ℤ₀ ↔ HFInt`** (si todavía hay drift entre ambos): unificación.
3. **B3. Anillos cocientes concretos** sobre HFRing: `ℤ₀/(n)`, anillos de matrices `Mₙ(ℤ₀)` (uso de `FinList`/`NPow`).
4. **B4. Documentación de cierre**: revisar `THOUGHTS.md`, congelar `REFERENCE-Paridad-Peano-Aczel.md` con sello "Paridad completa".

### 🅲️ FASE C — Decisión: ¿extender HF o saltar a ASet₁? (punto de inflexión)

Aquí se decide la estrategia de los próximos 12+ meses. Tres opciones (no excluyentes):

- **C1. Profundizar en HFSet.** Topología avanzada (compacidad, conexidad sobre HF), categorías pequeñas, álgebra homológica truncada. *Pros:* todo computable. *Contras:* limitado a finitos.
- **C2. Comenzar ASet₁ (Δ⁰₁).** Subconjuntos decidibles infinitos (incluye ω, ℕ₀ como HFSet infinito). Permite hablar de funciones `ℕ₀ → ℕ₀`, sucesiones, límites. *Ver §Largo Plazo más abajo.*
- **C3. Atacar ZFC vía W-Types** (Estrategia C de THOUGHTS.md). *Más ambicioso, más arriesgado.*

**Mi recomendación tentativa:** C2 (ASet₁) por ser el incremento natural y el que abre análisis real computable.

### 🅳️ FASE D — Largo plazo (12+ meses)

Lo que ya está documentado en este mismo archivo en §"Largo Plazo": ASet₁, Jerarquía Aritmética, ZFC. Sin cambio respecto a la versión 2026-05-22.

---

## Preguntas abiertas para discutir

> **Resueltas el 2026-05-28** — registro de decisiones:
>
> 1. **Prioridad "Paridad antes que Extensión":** **aceptada.** Procedemos con Fase A íntegra antes de Fase B.
> 2. **Sylow:** **se mantiene dentro del bloque mínimo** (M6). Es parte de la paridad Peano completa.
> 3. **Punto de inflexión C:** **se mantiene** para discutir al cierre de Fase A. Escribiremos mini-RFC C1/C2/C3 tras M7.
> 4. **⚠️ embebidos:** **se auditarán** (tarea T1 en `NEXT_STEPS.md`) antes de tocar ℚ₀ extendido en Fase B; decisión caso por caso.
> 5. **Cadencia de check-in:** **acordada.** Actualizar `PLANNING.md` y `REFERENCE-Paridad-Peano-Aczel.md` tras cada milestone con lecciones aprendidas + recálculo de estimación (tarea T3).

Ver `NEXT_STEPS.md` para el plan de ejecución detallado de Fase A con todas las decisiones tácticas adicionales (paralelización, especialización de iso theorems, `PermVN := SymVN`, bundle).

---

## Estado actual (snapshot 2026-05-29)

- **133 módulos Lean (no-barrel) + 9 barrels = 142 total, 0 sorry, 0 axiomas privados.**
- **Algebra/**: 20 módulos incluyendo `Sylow.lean` con D.4.D McKay completo (§1–§27).
- Fases históricas 1–5 **completadas**. Detalle abajo se conserva como histórico.

### Completado

**CList** (8 módulos): Basic, ExtEq, Filter, SetEquiv, Order, Sort, Normalize, barrel.

- Refactorizado completamente a `PList CList` / `ℕ₀` (Fase 2 ✅).

**PList** (4 módulos): Basic, Lemmas, Omega0, Fin0.

- `omega₀` tactic disponible. Fase 1 ✅.

**HFSet** (1 módulo): cociente extensional sobre CList.

**Axiomas Zermelo** completos: Extensionalidad, Vacío, Par, Unión, Separación,
Intersección, Setminus, Potencia, Fundación, Singleton.

**Relaciones y funciones** (Fase 10 ✅): Par Ordenado, isRelation, domain/range,
isFunction, isTotalFunction, apply, relInv, restrict, preimage, relComp,
imageRel, image (reemplazo), FunctionComp, Identity, Product (×ₛ), Bijection.

**Producto Cartesiano computable** (Fase 7 ✅): `cartProd` / `×ₕ` a nivel CList
y HFSet. `CartProd.lean` + `Axioms/CartProd.lean`.

**Potencia n-aria** (NPow): `nPow A n` = Aⁿ como potencia cartesiana iterada.
`Operations/NPow.lean` + `Axioms/NPow.lean`.

**HFList / FinList**: `HFList = PList HFSet`, `FinList n = {l : HFList // l.length = n}`.
Infrastructura de n-tuplas tipadas estáticamente.

**Embedding vN** (Fases 3–5 ✅): `vN : ℕ₀ → HFSet` inyectivo, aritmética
transportada (addVN, mulVN, subVN, divVN, powVN, factorialVN, rank, card),
`VN/CardVN.lean`. `Axioms/OrdinalNat.lean`: `isOrdinal ↔ isNat` en V_ω.

**Fintype** (F1+F2): `Finset`, `Fintype`, `HFSet.toList`, `HFSet.toFinset`,
`membership_fintype`.

### Pendiente (medio plazo)

- **[B1]** Teoría de FinList / HFList: igualdad extensional n-tuplas, concatenación, slice.
- **[B2]** Transporte VN de más operaciones de Peanolib (mcd, mcm, divisibilidad, primalidad).
- **[B3]** Teoría de relaciones de orden: preorden, orden parcial, orden total, orden bien fundado — exhaustiva como infraestructura para fases futuras.
- **[C]** Plan y discusión ASet₁ antes de comenzar la implementación.

**Dependencia actual:** `Init.Data.List.Basic` eliminada. Dependencia: `Peano` (library externa).

---

## Fase 1 — Dependencia Peano + PList + omega₀

> Prerrequisito de todas las fases siguientes.
> No toca código existente. Solo añade archivos nuevos.

### 1.1 Lakefile: añadir Peano como dependencia

Archivo: `lakefile.lean`

```lean
require peanolib from git
  "https://github.com/julian1c2a/Peano.git" @ "master"
```

Verificar: `lake update && lake build` compila 0 errores.

**Qué importamos de Peano:**

- `ℕ₀` (tipo inductivo con `𝟘` y `σ`)
- `PeanoNatArith` (suma `+₀`, producto `*₀`, orden `≤₀`)
- `Isomorph` (isomorfismo `Λ : ℕ₀ → ℕ`, `Ψ : ℕ → ℕ₀` con preservación de operaciones)
- `FSet` (conjunto finito ordenado basado en `List`)

### 1.2 PList: listas propias con ℕ₀

Archivo: `AczelSetTheory/PList/Basic.lean`

```lean
namespace PList

inductive PList (α : Type) : Type where
  | nil  : PList α
  | cons : α → PList α → PList α

def length : PList α → ℕ₀
  | nil      => 𝟘
  | cons _ t => σ (length t)

def map (f : α → β) : PList α → PList β
  | nil      => nil
  | cons h t => cons (f h) (map f t)

def any (p : α → Bool) : PList α → Bool
  | nil      => false
  | cons h t => p h || any p t

def filter (p : α → Bool) : PList α → PList α
  | nil      => nil
  | cons h t => if p h then cons h (filter p t) else filter p t

def foldl (f : β → α → β) (init : β) : PList α → β
  | nil      => init
  | cons h t => foldl f (f init h) t

def append : PList α → PList α → PList α
  | nil,      ys => ys
  | cons h t, ys => cons h (append t ys)

def flatMap (f : α → PList β) : PList α → PList β
  | nil      => nil
  | cons h t => append (f h) (flatMap f t)

end PList
```

Lemas necesarios (en `PList/Lemmas.lean`):

- `length_nil`, `length_cons`
- `mem_cons`, `mem_nil` (predicado `PList.Mem`)
- `map_cons`, `filter_cons`
- `length_append`, `mem_append`
- `length_map`, `mem_map`
- `mem_filter`
- `flatMap_nil`, `flatMap_cons`, `mem_flatMap`

**Propiedad clave:** `PList` es isomorfa a `List` de Lean. El isomorfismo
`plistToList : PList α → List α` y su inverso permiten transferir lemas de
`List` puntualmente si fuera necesario durante la transición.

### 1.3 omega₀: táctica puente ℕ₀ → omega

Archivo: `AczelSetTheory/PList/Omega0.lean`

El isomorfismo `Λ : ℕ₀ → ℕ` de Peano preserva `+`, `*`, `≤`, `<`. Esto
permite construir una táctica que convierte metas sobre `ℕ₀` a metas sobre
`ℕ` y aplica `omega`:

```lean
-- Instancia de simp para transportar via Λ
@[simp] lemma Λ_add (m n : ℕ₀) : Λ (m +₀ n) = Λ m + Λ n := ...
@[simp] lemma Λ_le  (m n : ℕ₀) : m ≤₀ n ↔ Λ m ≤ Λ n     := ...
@[simp] lemma Λ_lt  (m n : ℕ₀) : m <₀ n ↔ Λ m < Λ n     := ...
@[simp] lemma Λ_zero : Λ 𝟘 = 0                          := ...
@[simp] lemma Λ_succ (n : ℕ₀) : Λ (σ n) = Λ n + 1       := ...

macro "omega₀" : tactic =>
  `(tactic| (simp only [← Nat.lt_iff_add_one_le,
               Λ_add, Λ_le, Λ_lt, Λ_zero, Λ_succ,
               ← Λ_injective.eq_iff]
             omega))
```

Los lemas de preservación ya existen en `Peano/Isomorph.lean`; solo hay que
conectarlos como simp-lemmas.

---

## Fase 2 — Refactorización de CList (Opción B completa)

> **Coste:** alto. **Beneficio:** pureza fundacional total. No usar `List`
> de Init ni `Nat` de Lean en ningún lema o prueba del proyecto.
>
> **Prerrequisito:** Fase 1 completa.

### 2.0 Clave arquitectónica

`PList` está definida **antes** de `CList`. Por tanto:

```lean
inductive CList : Type where
  | mk : PList CList → CList
```

Es un inductivo estándar (no mutual). `PList CList` es válido porque `PList`
es un tipo polimórfico ya definido — no hay violación de positividad.

### 2.1 CList/Basic.lean

Cambios:

- Eliminar `import Init.Data.List.Basic`
- Añadir `import AczelSetTheory.PList.Basic`
- `mk : PList CList → CList`
- `cSize : CList → ℕ₀` (retorna `ℕ₀` en lugar de `Nat`)
- `cSizePList : PList CList → ℕ₀` (auxiliar mutual)
- Todas las funciones que usaban `List.any`, `List.map`, etc. pasan a `PList.any`, `PList.map`
- Pruebas de terminación: `omega₀` en lugar de `omega`

Funciones afectadas:

- `cSize` / `cSizeList` → `cSize` / `cSizePList`
- `dedupAux`, `dedup`
- `orderedInsert`, `insertionSort`
- `normalize`
- `evalOp`

### 2.2 CList/ExtEq.lean

Cambios:

- Lemas que usan `List.mem_cons` → `PList.mem_cons`
- Lemas de tamaño que usan `Nat.lt` → `ℕ₀.lt` (o `<₀`)

### 2.3 CList/SetEquiv.lean, Order.lean, Sort.lean, Normalize.lean, Filter.lean

Cambios análogos: reemplazar referencias a `List.*` y `Nat.*` por `PList.*`
y `ℕ₀.*`. Los argumentos `omega` se reemplazan con `omega₀` o con lemas
explícitos de `PeanoNatArith`.

### 2.4 Estimación de coste

| Módulo             | Líneas | Cambio estimado | Dificultad |
|--------------------|--------|-----------------|------------|
| CList/Basic.lean   | ~185   | Alto            | Media      |
| CList/ExtEq.lean   | ~?     | Medio           | Baja       |
| CList/SetEquiv.lean| ~?     | Bajo            | Baja       |
| CList/Order.lean   | ~?     | Bajo            | Baja       |
| CList/Sort.lean    | ~?     | Medio           | Baja       |
| CList/Normalize.lean| ~?    | Medio           | Media      |
| CList/Filter.lean  | ~?     | Bajo            | Baja       |

El cambio más delicado es `evalOp` en Basic.lean porque su terminación
depende de aritmética sobre `cSize`. Con `omega₀` disponible, la prueba
estructural es idéntica a la actual.

---

## Fase 3 — Embedding vN: ℕ₀ → HFSet

> **Prerrequisito:** Fase 1 (Peano dep). Fase 2 recomendada pero no estricta.

### 3.1 Definición de vN

Archivo: `AczelSetTheory/VN/Basic.lean`

```lean
namespace VN

def vN : ℕ₀ → HFSet
  | 𝟘    => ∅
  | σ n  => vN n ∪ {[ vN n ]}

-- Propiedades inmediatas
theorem vN_zero : vN 𝟘 = ∅ := rfl
theorem vN_succ (n : ℕ₀) : vN (σ n) = vN n ∪ {[ vN n ]} := rfl
theorem vN_succ_ne_empty (n : ℕ₀) : vN (σ n) ≠ ∅ := ...
theorem mem_vN_succ (x n : ℕ₀) :
    x ∈ vN (σ n) ↔ x = vN n ∨ x ∈ vN n := ...

end VN
```

### 3.2 Inyectividad

Archivo: `AczelSetTheory/VN/Injective.lean`

```lean
namespace VN

theorem vN_injective : Function.Injective vN
-- Prueba por inducción sobre ℕ₀:
-- vN m = vN n → m = n
-- Caso base: vN 𝟘 = ∅. Ningún vN (σ k) = ∅ (por vN_succ_ne_empty).
-- Inductivo: vN (σ m) = vN (σ n) → por extensionalidad → vN m ∈ vN (σ n)
--   y vN n ∈ vN (σ m) → por no-membresía-propia (Foundation) → m = n.

end VN
```

### 3.3 vN es biyección sobre su imagen (los naturales de von Neumann)

Archivo: `AczelSetTheory/VN/IsNat.lean`

```lean
-- Predicado "es un natural de von Neumann"
def VN.IsVNNat (x : HFSet) : Prop := ∃ n : ℕ₀, vN n = x

-- La imagen de vN es exactamente los VNNat
theorem VN.mem_range_iff (x : HFSet) :
    VN.IsVNNat x ↔ x = ∅ ∨ ∃ y, VN.IsVNNat y ∧ x = y ∪ {[ y ]} := ...
```

### 3.4 Transporte aritmético

Archivo: `AczelSetTheory/VN/Arithmetic.lean`

Las operaciones aritméticas sobre HFSet para naturales de von Neumann se
definen set-teóricamente y se prueba que corresponden a las de ℕ₀:

```lean
-- Suma von Neumann (definición recursiva sobre IsVNNat)
-- add_vN n 𝟘     = n
-- add_vN n (σ m) = σ (add_vN n m)  (en términos de vN)
theorem vN_add (m n : ℕ₀) :
    vN (m +₀ n) = add_vN (vN m) (vN n) := ...

-- Orden
theorem vN_le_iff (m n : ℕ₀) :
    m ≤₀ n ↔ vN m ⊆ vN n := ...

-- Membresía como orden estricto
theorem mem_vN_iff_lt (m n : ℕ₀) :
    vN m ∈ vN n ↔ m <₀ n := ...
```

---

## Fase 4 — Embedding FSet ℕ₀ → HFSet

> **Prerrequisito:** Fase 3 (vN disponible).

Archivo: `AczelSetTheory/VN/FSet.lean`

```lean
namespace VN

-- Convierte un FSet ℕ₀ en un HFSet usando vN
def fsetToHFSet (S : FSet ℕ₀) : HFSet :=
  S.elems.foldl (fun acc n => acc ∪ {[ vN n ]}) ∅

theorem mem_fsetToHFSet (x : HFSet) (S : FSet ℕ₀) :
    x ∈ fsetToHFSet S ↔ ∃ n ∈ S, x = vN n := ...

theorem fsetToHFSet_injective : Function.Injective fsetToHFSet := ...

-- Preserva operaciones de FSet
theorem fsetToHFSet_union (S T : FSet ℕ₀) :
    fsetToHFSet (S ∪ T) = fsetToHFSet S ∪ fsetToHFSet T := ...

theorem fsetToHFSet_inter (S T : FSet ℕ₀) :
    fsetToHFSet (S ∩ T) = fsetToHFSet S ∩ fsetToHFSet T := ...

end VN
```

---

## Fase 5 — Transporte de Peano a HFSet

> **Prerrequisito:** Fases 3 y 4.
> **Objetivo:** "Todo lo válido en Peano es válido en HFSet" como teoremas
> formales. No reescribir Peano — transportar vía vN.

### 5.1 Axiomas de Peano como teoremas sobre vN

Archivo: `AczelSetTheory/VN/PeanoAxioms.lean`

```lean
namespace VN

-- PA1: vN 𝟘 ≠ vN (σ n)
theorem vN_zero_ne_succ (n : ℕ₀) : vN 𝟘 ≠ vN (σ n) :=
  fun h => absurd h (by simp [vN_zero, vN_succ, union_ne_empty])

-- PA2: vN es inyectiva (= succ_injective para vN)
-- ya en Fase 3: vN_injective

-- PA3: Inducción (se hereda de eps_induction sobre HFSet restringida a IsVNNat,
--   o directamente de ℕ₀-induction transportada via vN)
theorem vN_induction (P : HFSet → Prop)
    (h0 : P (vN 𝟘))
    (hs : ∀ n : ℕ₀, P (vN n) → P (vN (σ n))) :
    ∀ n : ℕ₀, P (vN n) := ...

end VN
```

### 5.2 Aritmética

Archivo: `AczelSetTheory/VN/PeanoArith.lean`

Transporte sistemático de:

- `add_comm`, `add_assoc`, `add_zero`, `zero_add`
- `mul_comm`, `mul_assoc`, `mul_zero`, `zero_mul`, `mul_one`
- `add_mul`, `mul_add` (distributividad)
- `le_antisymm`, `le_trans`, `le_total`

Estrategia: aplicar `vN` a ambos lados del lema de Peano y usar los
teoremas de transporte de Fase 3.4.

---

## Fase 6 — Continuación de HFSet puro (Fases 7–11)

> Estas fases existían antes de la integración Peano. Se retoman después
> de que la infraestructura PList/vN esté estable. Ver NEXT_STEPS.md
> para el detalle de cada una.

| Fase | Contenido | Prereq |
|------|-----------|--------|
| 7    | Adjunción, ε-inducción, Producto Cartesiano | Actual |
| 8    | Decidabilidad, Álgebra Boole, Anillo Booleano | Fase 7 |
| 9    | vN naturales internos (succ_HFSet, isNat) | Fase 3 o 7 |
| 10   | Relaciones y funciones como HFSets | Fase 4, 8 |
| 11   | Reemplazo, Elección (ya probados parcialmente) | Fase 10 |

---

## Largo Plazo — ASet₁, Jerarquía Aritmética, ZFC

> Estos módulos no pertenecen a HFSet. Son extensiones futuras separadas.
> Quedan documentados en THOUGHTS.md §3.

### ASet₁ (Nivel 1, Δ⁰₁)

```lean
-- Nuevo proyecto: AczelSetTheory₁ (o sub-lib separada)
inductive CList₁ where
  | mk  : PList CList₁ → CList₁      -- conjunto finito de ASet₁
  | inf : (HFSet → Bool) → CList₁    -- subconjunto decidible de HFSet

def ASet₁ := Quotient CList₁.Setoid
```

Captura: HF(V_ω ∪ Δ⁰₁). Incluye ω = `inf (fun _ => true)`.
Prerrequisito: Fases 1–5 completas, infraestructura estable.

### Jerarquía Aritmética (Niveles 2, 3, ...)

Estrategia B (§3.5 THOUGHTS.md):

```lean
-- Nivel 2
inductive CList₂ where
  | mk  : PList CList₂ → CList₂
  | inf : (ASet₁ → Bool) → CList₂    -- ASet₁ ya definido ✓
def ASet₂ := Quotient CList₂.Setoid
```

Cada nivel es un `inductive` válido porque el nivel anterior ya está definido.
Captura Δ⁰ₙ iterando la construcción.

### ZFC via W-Types (Estrategia C)

Para transfinite ordinals, cardinals, y la jerarquía constructible de Gödel
más allá de U_ω. Ver THOUGHTS.md §3.5 Estrategia C y §3.7.

La ruta es: AczelSetTheory → ASet₁ → ... → U_ω → W-Types → ZFC.
El proyecto ZfcSetTheory (hermano) ya implementa el extremo ZFC.

---

## Decisiones de diseño registradas

| Decisión | Justificación |
|----------|---------------|
| `vN` para la función, `VN` para namespace | Notación estándar de teoría de conjuntos, lowerCamelCase (REGLA 8) |
| `PList` antes de `CList` (no mutual) | Evita mutual inductive; `PList` es genérico e independiente de `CList` |
| `cSize : CList → ℕ₀` | Pureza: no depender de `Nat` de Lean en lemas de CList |
| `omega₀` via `Λ`-isomorfismo | Reutiliza `omega` de Lean sin recaer en `ℕ` en enunciados |
| `FSet ℕ₀ → HFSet` antes que `PList CList → HFSet` | FSet ya es una forma normal canónica; la composición `FSet → HFSet` es directa |
| No migrar Peano completo, solo embedding | ~600 símbolos en Peano; el embedding da toda la potencia teórica sin reescritura |

---

## Árbol de dependencias de módulos (objetivo)

```
Peano (dep externa)
  ↓
AczelSetTheory/PList/Basic.lean        (ℕ₀, PList)
AczelSetTheory/PList/Omega0.lean       (omega₀ tactic)
  ↓
AczelSetTheory/CList/Basic.lean        (PList CList, ℕ₀-based cSize)
AczelSetTheory/CList/*.lean            (refactored)
  ↓
AczelSetTheory/HFSets.lean
AczelSetTheory/Operations/*.lean
AczelSetTheory/Axioms/*.lean
  ↓
AczelSetTheory/VN/Basic.lean           (vN : ℕ₀ → HFSet)
AczelSetTheory/VN/Injective.lean
AczelSetTheory/VN/Arithmetic.lean
AczelSetTheory/VN/IsNat.lean
AczelSetTheory/VN/FSet.lean
AczelSetTheory/VN/PeanoAxioms.lean
AczelSetTheory/VN/PeanoArith.lean
  ↓
[Fase 7–11: HFSet puro ampliado]
  ↓
[ASet₁, jerarquía, ZFC — futuro]
```
