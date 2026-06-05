# NONCOMPUTABLE INSTANCES — AczelSetTheory

**Fecha de inventario**: 22 de mayo de 2026 (inventario histórico)
**Última verificación**: 3 de junio de 2026
**Herramienta**: `grep -r "noncomputable" AczelSetTheory/`
**Total encontrado (2026-06-03)**: **0 ocurrencias reales** (única mención: comentario en `VN/QuotientGroupVN.lean:31`)

> **Estado actual:** Las 25 entradas del inventario histórico (mayo 2026) han sido eliminadas
> en el Sprint B (mayo-junio 2026). El proyecto mantiene el invariante `noncomputable def: 0`.
> La tabla histórica se conserva a continuación como referencia de las decisiones de diseño.

---

## Tabla resumen (inventario histórico — mayo 2026, ya resuelto)

| # | Archivo | Definición | Razón raíz | Fijable |
|---|---------|-----------|------------|---------|
| 1 | `Operations/OrderedPair.lean:19` | `fst` | `Classical.choose` | Difícil |
| 2 | `Operations/OrderedPair.lean:24` | `snd` | `Classical.choose` | Difícil |
| 3 | `Operations/Function.lean:27` | `apply` | `Classical.choose` | Difícil |
| 4 | `Operations/Identity.lean:14` | `HFSet.idFunc` | `∃` no acotado en `sep` | Fácil |
| 5 | `Operations/Product.lean:15` | `HFSet.prodHF` | `∃` no acotado en `sep` | Fácil |
| 6 | `Operations/Composition.lean:14` | `HFSet.relComp` | `∃` no acotado en `sep` | Fácil |
| 7 | `Operations/Composition.lean:23` | `HFSet.imageRel` | `∃` no acotado en `sep` | Fácil |
| 8 | `Operations/FunctionComp.lean:14` | `HFSet.funComp` | `∃` no acotado en `sep` | Fácil |
| 9 | `Operations/Inverse.lean:14` | `HFSet.relInv` | `∃` no acotado en `sep` | Fácil |
| 10 | `Operations/Restriction.lean:10` | `HFSet.restrict` | `∃` no acotado en `sep` | Fácil |
| 11 | `Operations/Restriction.lean:19` | `HFSet.preimage` | `∃` acotado (ya fijable) | Trivial |
| 12 | `Topology/Interior.lean:34` | `HFTopSpace.interior` | `∀ x ∈ U, x ∈ A` en `sep` | Fácil |
| 13 | `Topology/Interior.lean:83` | `HFTopSpace.closure` | cascada de `interior` | Fácil |
| 14 | `Topology/Interior.lean:123` | `HFTopSpace.exterior` | cascada de `interior` | Fácil |
| 15 | `Topology/Interior.lean:133` | `HFTopSpace.boundary` | cascada de `interior`/`closure` | Fácil |
| 16 | `Topology/Neighborhoods.lean:50` | `HFTopSpace.toNeighborSpace` | `∃ U ∈ τ, ... ∧ U ⊆ N` en `sep` | Fácil |
| 17 | `Topology/Neighborhoods.lean:111` | `HFNeighborSpace.toTopSpace` | `∀ x ∈ U, U ∈ 𝒩(x)` en `sep` | Fácil |
| 18 | `Topology/Subspace.lean:22` | `HFTopSpace.preimage` | `f x ∈ V` en `sep` + `open Classical` | Trivial |
| 19 | `Topology/Subspace.lean:33` | `HFTopSpace.subspace` | `∃ U ∈ τ, V = U ∩ A` en `sep` | Fácil |
| 20 | `Topology/Subspace.lean:126` | `HFContinuous.id` | cascada de `HFTopSpace.preimage` | Trivial |
| 21 | `Topology/Subspace.lean:144` | `HFContinuous.comp` | cascada de `HFTopSpace.preimage` | Trivial |
| 22 | `Integers/MobiusLiouville.lean:84` | `squarefree_decidable` (inst.) | `Classical.propDecidable _` explícito | Medio |
| 23 | `Integers/MobiusLiouville.lean:87` | `mobius` | cascada de `squarefree_decidable` | Medio |
| 24 | `Integers/MobiusLiouville.lean:95` | `liouville` | cascada de `squarefree_decidable` | Medio |
| 25 | `VN/HFGroupVN.lean:57` | `imageGroup` | `FSet.image` y `HFSet.card` de Peano | Externo |

---

## Grupo 1 — `Classical.choose` (genuinamente no computables)

Estas tres definiciones usan `Classical.choose` para extraer testigos de proposiciones
existenciales. No hay una vía de síntesis de instancias que ayude: la operación en sí
es clásica porque la existencia no viene acompañada de un algoritmo de búsqueda.

### 1.1 `fst` y `snd` — `Operations/OrderedPair.lean`

```lean
noncomputable def fst (p : HFSet) (h : ∃ a b, p = ⟪a, b⟫) : HFSet :=
  Classical.choose h

noncomputable def snd (p : HFSet) (h : ∃ a b, p = ⟪a, b⟫) : HFSet :=
  Classical.choose (Classical.choose_spec h)
```

**Por qué son no computables**: `Classical.choose h` devuelve el `a` de la prueba
existencial `h : ∃ a, ∃ b, p = ⟪a,b⟫`, pero sin especificar cómo encontrarlo.

**Lo que haría falta para quitarlos**: Rediseñar completamente la interfaz.
`HFSet` es hereditariamente finito, por lo que `a = ⋂ p` (la intersección de
todos los elementos de `p`) da `a` de forma computable, y
`b` es el único elemento de `⋃ p \ {a}` cuando `p = ⟪a, b⟫`. Las definiciones
alternativas serían:

```lean
def fst (p : HFSet) : HFSet := HFSet.sInter p
def snd (p : HFSet) : HFSet :=
  let a := fst p
  (HFSet.sep (HFSet.sUnion p) (fun x => x ≠ a)).choose -- sigue noncomputable...
```

La dificultad real es que la definición Kuratowski `⟪a,b⟫ = {{a}, {a,b}}` no
facilita una decodificación directamente computable en Lean 4 sin una prueba
de corrección fuerte. La alternativa más limpia sería añadir una función:

```lean
-- Itera sobre los elementos de p buscando el par
def decodePair (p : HFSet) : Option (HFSet × HFSet) := ...
```

y reformular `fst`/`snd` devolviendo `Option` o con precondición en una
forma que Lean pueda evaluar. **Coste estimado: alto.** Todos los sitios
de uso de `fst`/`snd` tendrían que actualizarse.

---

### 1.2 `apply` — `Operations/Function.lean`

```lean
noncomputable def apply (f a : HFSet) (h : ∃ b, ⟪a, b⟫ ∈ f) : HFSet :=
  Classical.choose h
```

**Por qué es no computable**: igual que `fst`/`snd`, extrae el `b` de la existencia
`∃ b, ⟪a,b⟫ ∈ f` con `Classical.choose`.

**Lo que haría falta**: Para HFSet esta función SÍ es computable algorítmicamente
— basta iterar sobre los elementos de `f` buscando el par `⟪a, _⟫`. La
definición computable sería:

```lean
def apply (f a : HFSet) (h : ∃ b, ⟪a, b⟫ ∈ f) : HFSet :=
  -- existsMem_decidable nos da el testigo computado,
  -- pero Classical.choose_spec no es suficiente...
  -- Se necesita una función que itere: findPair f a
```

En concreto, habría que añadir a `HFSets` una función tipo:

```lean
-- Encuentra b tal que ⟪a, b⟫ ∈ f, iterando sobre elementos de f
def HFSet.applyRel (f a : HFSet) : HFSet := ...
```

usando `Quotient.recOnSubsingleton` sobre `f` para iterar. **Coste estimado:
medio-alto** (nueva función en `HFSets.lean` + prueba de corrección).

---

## Grupo 2 — `sep` con cuantificadores existenciales no acotados (fijables)

Todos estos archivos usan el patrón:

```lean
open Classical in
noncomputable def ... :=
  HFSet.sep universo (fun x => ∃ a b, ...)
```

La instancia `existsMem_decidable` (en `Axioms/Decidable.lean`) ya proporciona
`Decidable (∃ x ∈ A, P x)`, pero solo cuando el cuantificador está **acotado**
(`∃ x ∈ A, ...`). Los predicados actuales tienen cuantificadores libres
`∃ a b, ...` sin mencionar en qué conjunto viven `a` y `b`.

El mecanismo de Lean: para que `HFSet.sep universo P` sea computable,
`P` debe tener instancia `[DecidablePred P]`. Eso requiere
`∀ x, Decidable (P x)`. Con cuantificadores libres no acotados, Lean no sabe
cómo construir ese `Decidable`, y cae al `Classical.propDecidable` (noncomputable)
activado por `open Classical`.

**Solución general**: reescribir el predicado acotando los cuantificadores al
conjunto del que sabemos que provienen los testigos. La cadena de síntesis es:

```
DecidableEq HFSet        (OrdinalNat.lean, ya disponible)
  ↓
existsMem_decidable A P  (Decidable.lean, ya disponible)
  ↓
DecidablePred (fun x => ∃ a ∈ A, Q a x)
  ↓
HFSet.sep computable
```

Adicionalmente hay que añadir `import AczelSetTheory.Axioms.OrdinalNat`
(para `DecidableEq HFSet`) y eliminar `open Classical in`.

---

### 2.1 `HFSet.idFunc` — `Operations/Identity.lean`

```lean
open Classical in
noncomputable def HFSet.idFunc (A : HFSet) : HFSet :=
  HFSet.sep
    (HFSet.powerset (HFSet.powerset A))
    (fun p => ∃ a, a ∈ A ∧ p = HFSet.orderedPair a a)
```

**Problema**: `∃ a, a ∈ A ∧ p = orderedPair a a` es un existencial con
`a` libre, no acotado de la forma `∃ a ∈ A, ...`.

**Fix**: reescribir el predicado:

```lean
-- Antes: ∃ a, a ∈ A ∧ p = orderedPair a a
-- Después:
(fun p => ∃ a ∈ A, p = HFSet.orderedPair a a)
```

Semánticamente idéntico. Lean puede sintetizar
`existsMem_decidable A (fun a => p = orderedPair a a)` si tiene
`DecidableEq HFSet` (via `OrdinalNat`).

---

### 2.2 `HFSet.prodHF` — `Operations/Product.lean`

```lean
open Classical in
noncomputable def HFSet.prodHF (A B : HFSet) : HFSet :=
  HFSet.sep
    (HFSet.powerset (HFSet.powerset (HFSet.union A B)))
    (fun p => ∃ a b, a ∈ A ∧ b ∈ B ∧ p = HFSet.orderedPair a b)
```

**Problema**: `∃ a b, ...` con `a` y `b` ambos libres.

**Fix**: anidar los cuantificadores acotados:

```lean
(fun p => ∃ a ∈ A, ∃ b ∈ B, p = HFSet.orderedPair a b)
```

La síntesis: `existsMem_decidable A (fun a => ∃ b ∈ B, p = orderedPair a b)`
con `existsMem_decidable B (fun b => p = orderedPair a b)`.

---

### 2.3 `HFSet.imageRel` — `Operations/Composition.lean`

```lean
open Classical in
noncomputable def HFSet.imageRel (R A : HFSet) : HFSet :=
  HFSet.sep (HFSet.sUnion (HFSet.sUnion R)) (fun b => ∃ a, a ∈ A ∧ ⟪a, b⟫ ∈ R)
```

**Problema**: `∃ a, a ∈ A ∧ ...` con `a` libre (forma sin `∈ A` integrado).

**Fix**: reescribir directamente (el predicado ya acota `a` a `A`, solo falta
la sintaxis):

```lean
(fun b => ∃ a ∈ A, ⟪a, b⟫ ∈ R)
```

Síntesis: `existsMem_decidable A (fun a => ⟪a, b⟫ ∈ R)` + `mem_decidable`. ✓

---

### 2.4 `HFSet.relComp` — `Operations/Composition.lean`

```lean
open Classical in
noncomputable def HFSet.relComp (S R : HFSet) : HFSet :=
  HFSet.sep (HFSet.sUnion (HFSet.sUnion S)) (fun c => ∃ a b, ⟪a, b⟫ ∈ R ∧ ⟪b, c⟫ ∈ S)
```

**Problema**: `∃ a b, ⟪a,b⟫ ∈ R ∧ ⟪b,c⟫ ∈ S` — `a` y `b` completamente libres.

**Fix**: `a` y `b` están en `⋃⋃R` (porque `⟪a,b⟫ ∈ R` implica
`{a},{a,b} ∈ ⋃R`, de donde `a,b ∈ ⋃⋃R`). Acotamos:

```lean
let UR2 := HFSet.sUnion (HFSet.sUnion R)
(fun c => ∃ a ∈ UR2, ∃ b ∈ UR2, ⟪a, b⟫ ∈ R ∧ ⟪b, c⟫ ∈ S)
```

**Nota**: hay que añadir `let UR2 := ...` o usar la expresión inline.
El universo sigue siendo `⋃⋃S` (segundo componente de los pares de S), correcto.

---

### 2.5 `HFSet.funComp` — `Operations/FunctionComp.lean`

```lean
open Classical in
noncomputable def HFSet.funComp (f g : HFSet) : HFSet :=
  HFSet.sep
    (HFSet.powerset (HFSet.powerset
      (HFSet.union (HFSet.sUnion (HFSet.sUnion f)) (HFSet.sUnion (HFSet.sUnion g)))))
    (fun p => ∃ a b c, p = ⟪a, c⟫ ∧ ⟪a, b⟫ ∈ g ∧ ⟪b, c⟫ ∈ f)
```

**Problema**: tres cuantificadores libres `∃ a b c, ...`.

**Fix**: `a`, `b` están en `⋃⋃g`; `c` está en `⋃⋃f`. Acotamos:

```lean
let Ug2 := HFSet.sUnion (HFSet.sUnion g)
let Uf2 := HFSet.sUnion (HFSet.sUnion f)
(fun p => ∃ a ∈ Ug2, ∃ b ∈ Ug2, ∃ c ∈ Uf2, p = ⟪a, c⟫ ∧ ⟪a, b⟫ ∈ g ∧ ⟪b, c⟫ ∈ f)
```

Síntesis anidada de `existsMem_decidable` tres veces.

---

### 2.6 `HFSet.relInv` — `Operations/Inverse.lean`

```lean
open Classical in
noncomputable def HFSet.relInv (R : HFSet) : HFSet :=
  HFSet.sep
    (HFSet.powerset (HFSet.powerset (HFSet.sUnion (HFSet.sUnion R))))
    (fun p => ∃ a b, ⟪a, b⟫ ∈ R ∧ p = ⟪b, a⟫)
```

**Problema**: `a` y `b` libres; provienen de `⋃⋃R`.

**Fix**:

```lean
let UR2 := HFSet.sUnion (HFSet.sUnion R)
(fun p => ∃ a ∈ UR2, ∃ b ∈ UR2, ⟪a, b⟫ ∈ R ∧ p = ⟪b, a⟫)
```

---

### 2.7 `HFSet.restrict` — `Operations/Restriction.lean`

```lean
open Classical in
noncomputable def HFSet.restrict (R A : HFSet) : HFSet :=
  HFSet.sep R (fun p => ∃ a b, p = ⟪a, b⟫ ∧ a ∈ A)
```

**Problema**: `a` y `b` libres; `p ∈ R` implica que `a, b ∈ ⋃⋃R`.

**Fix**: acotamos `a` en `A` (que es lo que queremos) y `b` en `⋃⋃R`:

```lean
let UR2 := HFSet.sUnion (HFSet.sUnion R)
(fun p => ∃ a ∈ A, ∃ b ∈ UR2, p = ⟪a, b⟫)
```

---

### 2.8 `HFSet.preimage` (Operations) — `Operations/Restriction.lean`

```lean
open Classical in
noncomputable def HFSet.preimage (R B : HFSet) : HFSet :=
  HFSet.sep (HFSet.sUnion (HFSet.sUnion R)) (fun a => ∃ b, b ∈ B ∧ ⟪a, b⟫ ∈ R)
```

**Problema**: `∃ b, b ∈ B ∧ ...` — cuantificador libre (sintaxis sin `∈ B`).

**Fix** (el más trivial del Grupo 2):

```lean
(fun a => ∃ b ∈ B, ⟪a, b⟫ ∈ R)
```

Síntesis directa: `existsMem_decidable B (fun b => ⟪a, b⟫ ∈ R)` + `mem_decidable`. ✓

---

## Grupo 3 — Topología (fijables con `forallMem_decidable` + `existsMem_decidable`)

La causa raíz de todos los `noncomputable` de topología es **`open Classical`
al nivel del módulo** (`Topology/Subspace.lean` y `Topology/Interior.lean`).
Con `open Classical`, Lean activa la instancia `scoped instance propDecidable`
de `Classical`, y la usa para cualquier `[Decidable]` que necesite sintetizar
en los predicados de `sep`. Como `propDecidable` es `noncomputable`,
toda definición que la use lo hereda.

Ahora que tenemos:

- `forallMem_decidable` (añadido en esta sesión) — para `∀ x ∈ A, P x`
- `existsMem_decidable` — para `∃ x ∈ A, P x`
- `mem_decidable` — para `x ∈ A`

todos los predicados de topología son computables.

**Fix general para el Grupo 3**: en cada archivo afectado,

1. Eliminar `open Classical` (o el `open Classical in` local)
2. Añadir `import AczelSetTheory.Axioms.OrdinalNat` si se necesita `DecidableEq HFSet`
3. Asegurarse de que los imports transitivos incluyen `Axioms/Decidable.lean`

---

### 3.1 `HFTopSpace.interior` — `Topology/Interior.lean`

```lean
noncomputable def HFTopSpace.interior (ts : HFTopSpace) (A : HFSet) : HFSet :=
  HFSet.sep ts.τ (fun U => U ⊆ A)
```

**Problema**: `U ⊆ A` es `∀ x ∈ U, x ∈ A`, que requiere
`Decidable (∀ x ∈ U, x ∈ A)`. Sin `forallMem_decidable`, Lean cae a
`Classical.propDecidable`.

**Fix**: con `forallMem_decidable` disponible (ya en `Axioms/Decidable.lean`),
`DecidablePred (fun U => U ⊆ A)` se sintetiza automáticamente:

```
forallMem_decidable U (fun x => x ∈ A)   ← mem_decidable x A
```

Solo hay que quitar `noncomputable` y asegurarse de que `open Classical`
no está activo en el contexto.

---

### 3.2 `HFTopSpace.closure` — `Topology/Interior.lean`

```lean
noncomputable def HFTopSpace.closure (ts : HFTopSpace) (A : HFSet) : HFSet :=
  HFSet.setminus ts.X (ts.interior (HFSet.setminus ts.X A))
```

**Problema**: cascada directa de `interior`. Si `interior` es `noncomputable`,
`closure` también lo es.

**Fix**: quitar `noncomputable` de `interior` primero, después de `closure`.
`HFSet.setminus` ya es computable (es un `sep` con `DecidablePred` trivial).

---

### 3.3 `HFTopSpace.exterior` y `HFTopSpace.boundary` — `Topology/Interior.lean`

```lean
noncomputable def HFTopSpace.exterior (ts : HFTopSpace) (A : HFSet) : HFSet :=
  ts.interior (HFSet.setminus ts.X A)

noncomputable def HFTopSpace.boundary (ts : HFTopSpace) (A : HFSet) : HFSet :=
  HFSet.setminus (ts.closure A) (ts.interior A)
```

**Problema**: ambas son cascadas de `interior`/`closure`.

**Fix**: misma solución que 3.1 y 3.2.

---

### 3.4 `HFTopSpace.toNeighborSpace` — `Topology/Neighborhoods.lean`

```lean
noncomputable def HFTopSpace.toNeighborSpace (ts : HFTopSpace) : HFNeighborSpace where
  X  := ts.X
  𝒩  := fun x =>
           HFSet.sep (HFSet.powerset ts.X)
             (fun N => ∃ U, U ∈ ts.τ ∧ x ∈ U ∧ U ⊆ N)
```

**Problema**: el predicado `∃ U, U ∈ ts.τ ∧ x ∈ U ∧ U ⊆ N` contiene:

- Un existencial no acotado sobre `U`
- `U ⊆ N` (cuantificador universal)

**Fix**:

```lean
(fun N => ∃ U ∈ ts.τ, x ∈ U ∧ U ⊆ N)
```

Síntesis:

```
existsMem_decidable ts.τ (fun U => x ∈ U ∧ U ⊆ N)
  ← instDecidableAnd
      (mem_decidable x U)
      (forallMem_decidable U (fun z => z ∈ N))
```

---

### 3.5 `HFNeighborSpace.toTopSpace` — `Topology/Neighborhoods.lean`

```lean
noncomputable def HFNeighborSpace.toTopSpace (ns : HFNeighborSpace) : HFTopSpace where
  X  := ns.X
  τ  := HFSet.sep (HFSet.powerset ns.X) (fun U => ∀ x, x ∈ U → U ∈ ns.𝒩 x)
```

**Problema**: `∀ x, x ∈ U → U ∈ ns.𝒩 x` — cuantificador universal no acotado.

**Fix**:

```lean
(fun U => ∀ x ∈ U, U ∈ ns.𝒩 x)
```

Síntesis:

```
forallMem_decidable U (fun x => U ∈ ns.𝒩 x)
  ← mem_decidable U (ns.𝒩 x)
```

(asumiendo que `ns.𝒩 x : HFSet`, lo que es el caso por la definición de `HFNeighborSpace`)

---

### 3.6 `HFTopSpace.preimage` — `Topology/Subspace.lean`

```lean
open Classical  -- módulo completo

noncomputable def HFTopSpace.preimage (ts : HFTopSpace) (f : HFSet → HFSet) (V : HFSet) : HFSet :=
  HFSet.sep ts.X (fun x => f x ∈ V)
```

**Problema**: el predicado `fun x => f x ∈ V` necesita
`[DecidablePred (fun x => f x ∈ V)]`. `f x ∈ V` es `Decidable` vía
`mem_decidable (f x) V`. Sin `open Classical`, Lean sintetiza esto correctamente.

**Fix** (el más trivial del Grupo 3):

```lean
-- Solo quitar open Classical del módulo o del def
def HFTopSpace.preimage (ts : HFTopSpace) (f : HFSet → HFSet) (V : HFSet) : HFSet :=
  HFSet.sep ts.X (fun x => f x ∈ V)
```

No hace falta cambiar nada más: `mem_decidable (f x) V` siempre está disponible.

---

### 3.7 `HFTopSpace.subspace` — `Topology/Subspace.lean`

```lean
noncomputable def HFTopSpace.subspace (ts : HFTopSpace) (A : HFSet) (hA : A ⊆ ts.X) :
    HFTopSpace where
  X  := A
  τ  := HFSet.sep (HFSet.powerset A) (fun V => ∃ U, U ∈ ts.τ ∧ V = HFSet.inter U A)
```

**Problema**: `∃ U, U ∈ ts.τ ∧ V = inter U A` — `U` no acotado.

**Fix**:

```lean
(fun V => ∃ U ∈ ts.τ, V = HFSet.inter U A)
```

Síntesis: `existsMem_decidable ts.τ (fun U => V = inter U A)` + `DecidableEq HFSet`. ✓

---

### 3.8 `HFContinuous.id` y `HFContinuous.comp` — `Topology/Subspace.lean`

```lean
noncomputable def id (ts : HFTopSpace) : HFContinuous ts ts where
  f             := fun x => x
  f_mem         := fun hx => hx
  preimage_open := by ...   -- usa ts.preimage internamente
```

**Problema**: aunque el único campo DATA (`f := fun x => x`) es computable,
la demostración de `preimage_open` contiene el término
`ts.preimage (fun x => x) V : HFSet` (tipo `HFSet`, no `Prop`), que aparece
en el cuerpo del término de prueba. Como `HFTopSpace.preimage` era
`noncomputable`, Lean propaga esa marca a toda la definición, incluyendo el
campo `f` aunque este sea trivialmente computable.

**Mecanismo**: en Lean 4, la marca `noncomputable` se propaga si CUALQUIER
subexpresión de tipo no-`Prop` referencia un símbolo `noncomputable`,
incluso dentro de un bloque `by` que prueba una `Prop`. El término
`ts.preimage f V : HFSet` aparece dentro del `by` para
`preimage_open : ∀ {V}, V ∈ τ → ts.preimage f V ∈ τ`, y como es un `HFSet`
(no una `Prop`), activa la propagación.

**Fix**: quitar `noncomputable` de `HFTopSpace.preimage` (ver 3.6). Una vez
que `preimage` es computable, `id` y `comp` se pueden marcar sin
`noncomputable` sin más cambios.

---

## Grupo 4 — `squarefree` sin test computable (fijable con esfuerzo medio)

### 4.1 `squarefree_decidable`, `mobius`, `liouville` — `Integers/MobiusLiouville.lean`

```lean
private noncomputable instance (n : ℕ₀) : Decidable (squarefree n) :=
  Classical.propDecidable _

noncomputable def mobius (n : ℕ₀) : ℤ₀ :=
  if squarefree n then negOnePow (Omega_prime n) else 0

noncomputable def liouville (n : ℕ₀) : ℤ₀ :=
  negOnePow (Omega_prime n)
```

**Problema**: `squarefree n` (n es libre de cuadrados) no tiene instancia
`Decidable` computable en este proyecto. Se usa `Classical.propDecidable _`
como atajo. Como `mobius` hace `if squarefree n then ...`, necesita
`[Decidable (squarefree n)]`, que se cubre con la instancia private. Al ser
`propDecidable` noncomputable, toda la cadena lo es.

**Nota sobre `liouville`**: `liouville n = negOnePow (Omega_prime n)` no usa
`squarefree` directamente, pero Lean la marca `noncomputable` igualmente.
Esto es una **cascada indebida**: `Omega_prime` debería ser computable (es
contar factores primos con multiplicidad). Habría que verificar si
`Omega_prime` es computable por sí mismo.

**Lo que haría falta**:

**Para `squarefree`**: implementar `squarefree_decidable_computable`:

```lean
-- squarefree n ↔ ∀ p ≤ n, ¬(p * p ∣ n ∧ 1 < p)
-- Requiere: decidibilidad de divisibilidad en ℕ₀ (ya disponible)
--           e iteración acotada sobre p ≤ n
instance squarefree_decidable (n : ℕ₀) : Decidable (squarefree n) :=
  -- Implementar la búsqueda acotada
  ...
```

La definición de `squarefree` en la librería Peano determina exactamente qué
forma tiene. Si `squarefree n ↔ ∀ p, p ∣ n → ¬(p * p ∣ n ∧ p ≠ 1)`, y la
divisibilidad es decidible en `ℕ₀`, entonces se puede construir la instancia
computable iterando `p` hasta `n`.

**Para `liouville`**: verificar si `Omega_prime` es computable. Si lo es,
eliminar `noncomputable` directamente.

---

## Grupo 5 — `imageGroup` (cascada de Peano)

### 5.1 `imageGroup` — `VN/HFGroupVN.lean`

```lean
noncomputable def imageGroup (G : ℕ₀FinGroup) : FinGroup HFSet where
  carrier := FSet.image vN G.carrier
  id      := vN G.id
  op      := { toFun := fun x y => vN (G.op (HFSet.card x) (HFSet.card y)), ... }
  inv     := { toFun := fun x => vN (G.inv (HFSet.card x)), ... }
  ...
```

**Problema**: el `noncomputable` proviene de una o varias de estas fuentes:

1. **`FSet.image`** (Peano): si la función `FSet.image` de Peano está marcada
   `noncomputable` en la librería `peanolib`, se propaga.
2. **`HFSet.card`**: la función `card : HFSet → ℕ₀` que convierte un HFSet en
   su cardinal (número de elementos) podría ser `noncomputable` si depende de
   algún `Classical.choose` interno.
3. **`FinGroup` de Peano**: si la estructura `FinGroup ℕ₀` usa algún campo
   `noncomputable` en Peano.

**Diagnóstico exacto**: ejecutar

```
set_option trace.Elab.definition.body true in
#check @imageGroup
```

o buscar qué símbolo concreto de Peano activa la marca.

**Lo que haría falta**: depende del resultado del diagnóstico.

- Si es `FSet.image`: o bien usar una función alternativa computable, o bien
  solicitar al mantenedor de `peanolib` que marque `FSet.image` como
  computable.
- Si es `HFSet.card`: revisar su implementación en `VN/CardVN.lean` y hacer
  la parte noncomputable computable.
- Es posible que sea **inevitablemente noncomputable** si la representación
  interna de `ℕ₀FinGroup` en Peano usa `Classical`.

---

## Plan de acción ordenado por esfuerzo

### Inmediato (trivial — solo quitar `open Classical` y reescribir sintaxis)

1. `Operations/Restriction.lean` — `preimage`: `∃ b, b ∈ B ∧ ...` → `∃ b ∈ B, ...`
2. `Topology/Subspace.lean` — `HFTopSpace.preimage`: quitar `open Classical`

### Fácil (reescribir predicados a formas acotadas)

3. `Operations/Identity.lean` — `idFunc`
2. `Operations/Product.lean` — `prodHF`
3. `Operations/Composition.lean` — `imageRel`, `relComp`
4. `Operations/FunctionComp.lean` — `funComp`
5. `Operations/Inverse.lean` — `relInv`
6. `Operations/Restriction.lean` — `restrict`
7. `Topology/Interior.lean` — `interior` → cascada: `closure`, `exterior`, `boundary`
8. `Topology/Neighborhoods.lean` — `toNeighborSpace`, `toTopSpace`
9. `Topology/Subspace.lean` — `subspace` → cascada: `id`, `comp`

### Medio (requiere nueva implementación)

12. `Integers/MobiusLiouville.lean` — implementar `instance : Decidable (squarefree n)`
    usando divisibilidad decidible en `ℕ₀`

### Difícil / Externo

13. `VN/HFGroupVN.lean` — `imageGroup`: diagnosticar fuente exacta en Peano
2. `Operations/OrderedPair.lean` — `fst`, `snd`: rediseñar con función de decodificación
3. `Operations/Function.lean` — `apply`: rediseñar con `applyRel` computable

---

## Infraestructura de soporte ya disponible

Tras la sesión del 22/05/2026, las siguientes instancias están en
`AczelSetTheory/Axioms/Decidable.lean` y son **computables**:

```lean
-- Membresía
instance mem_decidable (x A : HFSet) : Decidable (x ∈ A)

-- Existencial acotado
instance existsMem_decidable (A : HFSet) (P : HFSet → Prop) [DecidablePred P] :
    Decidable (∃ x, x ∈ A ∧ P x)

-- Universal acotado  ← NUEVO (sesión 22/05/2026)
instance forallMem_decidable (A : HFSet) (P : HFSet → Prop) [DecidablePred P] :
    Decidable (∀ x, x ∈ A → P x)
```

Y en `AczelSetTheory/Axioms/OrdinalNat.lean`:

```lean
-- Igualdad decidible en HFSet
instance : DecidableEq HFSet
```

Estos tres bloques (más `instDecidableAnd`, `instDecidableNot` de Lean core)
son suficientes para hacer computables todos los elementos del **Grupo 2**
y del **Grupo 3**.
