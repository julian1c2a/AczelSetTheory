# PLANNING — AczelSetTheory

**Last updated:** 2026-05-11
**Author:** Julián Calderón Almendros

> Plan de largo plazo para AczelSetTheory. Cada fase es ejecutable de forma
> independiente. Las dependencias entre fases están marcadas explícitamente.
> El detalle inmediato vive en NEXT_STEPS.md.

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

---

## Estado actual (2026-05-11)

- **22 módulos Lean, 0 sorry.**
- CList completo (7 sub-módulos).
- HFSet: tipo cociente sobre CList, membresía extensional, 0 sorry.
- Axiomas Zermelo completos: Extensionalidad, Vacío, Par, Unión, Separación,
  Intersección, Setminus, Potencia, Fundación, Singleton, Par Ordenado.
- Fases pendientes en HFSet puro: 7 (Adjunción, ε-inducción, Prod Cartesiano),
  8 (Decidabilidad, Álgebra Boole), 9–11 (Naturales vN internos, Relaciones,
  Reemplazo, Elección).

**Dependencia actual:** solo `Init.Data.List.Basic` de Lean. El objetivo es
eliminar esta dependencia progresivamente en favor de PList/ℕ₀.

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
@[simp] lemma Λ_le  (m n : ℕ₀) : m ≤₀ n ↔ Λ m ≤ Λ n    := ...
@[simp] lemma Λ_lt  (m n : ℕ₀) : m <₀ n ↔ Λ m < Λ n    := ...
@[simp] lemma Λ_zero : Λ 𝟘 = 0                           := ...
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
