# Next Steps

**Last updated:** 2026-05-11

The project compiles on Lean 4.29.0 with **0 sorry, 22 modules**.
Full Zermelo axioms derived. Architecture split: Operations/ + Axioms/.
See PLANNING.md for the full long-term roadmap.

---

## CURRENT PRIORITY — Fase 1: Peano Integration Foundation

> Objetivo: incorporar Peano como dependencia y construir la infraestructura
> propia (PList + omega₀) que soporta el resto del plan.
> No modifica ningún archivo existente hasta el paso 1.4.

---

### 1.1 Lakefile — añadir Peano

**Archivo:** `lakefile.lean`

```lean
require peanolib from git
  "https://github.com/julian1c2a/Peano.git" @ "master"
```

**Verificación:** `lake update && lake build` sin errores.

**Imports que usaremos:**

```lean
import Peano.PeanoNatLib.PeanoNatAxioms   -- ℕ₀, 𝟘, σ
import Peano.PeanoNatLib.PeanoNatArith    -- +₀, *₀
import Peano.PeanoNatLib.PeanoNatOrder    -- ≤₀, <₀
import Peano.Isomorph                     -- Λ : ℕ₀ → ℕ, Ψ : ℕ → ℕ₀
import Peano.ListsAndSets.FSet            -- FSet α
```

---

### 1.2 PList — lista propia con ℕ₀

**Archivo:** `AczelSetTheory/PList/Basic.lean`

Tipo inductivo polimórfico propio, usando `ℕ₀` en todas las funciones
que cuentan o indexan:

```lean
import Peano.PeanoNatLib.PeanoNatAxioms
import Peano.PeanoNatLib.PeanoNatArith

namespace PList

inductive PList (α : Type) : Type where
  | nil  : PList α
  | cons : α → PList α → PList α

def length : PList α → ℕ₀
  | nil      => 𝟘
  | cons _ t => σ (length t)

def mem [BEq α] (x : α) : PList α → Bool
  | nil      => false
  | cons h t => h == x || mem x t

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

-- Puente hacia List de Lean (solo para transferencia temporal durante Fase 2)
def toList : PList α → List α
  | nil      => []
  | cons h t => h :: toList t

def ofList : List α → PList α
  | []      => nil
  | h :: t  => cons h (ofList t)

end PList
```

**Archivo:** `AczelSetTheory/PList/Lemmas.lean`

Lemas requeridos por la Fase 2 (reescritura de CList):

```lean
-- Membresía
PList.mem_nil    : mem x nil = false
PList.mem_cons   : mem x (cons h t) = (h == x || mem x t)
PList.mem_append : mem x (append l₁ l₂) = (mem x l₁ || mem x l₂)
PList.mem_map    : mem y (map f l) ↔ ∃ x, mem x l ∧ f x = y

-- Longitud
PList.length_nil    : length nil = 𝟘
PList.length_cons   : length (cons h t) = σ (length t)
PList.length_append : length (append l₁ l₂) = length l₁ +₀ length l₂
PList.length_map    : length (map f l) = length l

-- filter
PList.mem_filter    : mem x (filter p l) ↔ mem x l ∧ p x = true

-- flatMap
PList.mem_flatMap   : mem y (flatMap f l) ↔ ∃ x, mem x l ∧ mem y (f x)
```

**Archivo:** `AczelSetTheory/PList.lean` (barrel)

```lean
import AczelSetTheory.PList.Basic
import AczelSetTheory.PList.Lemmas
```

---

### 1.3 omega₀ — táctica puente

**Archivo:** `AczelSetTheory/PList/Omega0.lean`

```lean
import Peano.Isomorph   -- Λ : ℕ₀ → ℕ y lemas de preservación

-- Lemas simp para transportar via Λ
-- (los nombres exactos dependen de Peano/Isomorph.lean — verificar)
@[simp] lemma Λ_zero       : Λ 𝟘 = 0                      := ...
@[simp] lemma Λ_succ (n)   : Λ (σ n) = Λ n + 1            := ...
@[simp] lemma Λ_add  (m n) : Λ (m +₀ n) = Λ m + Λ n      := ...
@[simp] lemma Λ_le   (m n) : m ≤₀ n ↔ Λ m ≤ Λ n          := ...
@[simp] lemma Λ_lt   (m n) : m <₀ n ↔ Λ m < Λ n          := ...
@[simp] lemma Λ_inj  (m n) : Λ m = Λ n ↔ m = n           := ...

-- Táctica
macro "omega₀" : tactic =>
  `(tactic| (simp only [Λ_zero, Λ_succ, Λ_add, Λ_le, Λ_lt, Λ_inj]; omega))
```

**Nota:** Antes de escribir los `...`, leer `Peano/Isomorph.lean` para
confirmar los nombres exactos de los lemas de preservación (`Λ_bij`,
`Λ_succ`, etc.) que ya existen en ese módulo.

---

### 1.4 Actualizar AczelSetTheory.lean (barrel raíz)

```lean
import AczelSetTheory.PList
-- (los imports existentes permanecen intactos)
```

---

## NEXT — Fase 2: Refactorización de CList

> **Prerrequisito:** Fase 1 completa y compilando.
> No empezar hasta que `omega₀` esté verificado en al menos un ejemplo.

### 2.0 Cambio central en CList/Basic.lean

```text
mk : List CList → CList    →    mk : PList CList → CList
cSize : CList → Nat        →    cSize : CList → ℕ₀
```

Orden de ataque:

1. `CList/Basic.lean` — cambio de tipo + funciones + pruebas de terminación
2. `CList/ExtEq.lean` — adaptar lemas de membresía
3. `CList/Order.lean` — adaptar orden (usa `cSize`)
4. `CList/SetEquiv.lean` — adaptar Nodup/SetEquiv
5. `CList/Sort.lean` — adaptar insertionSort
6. `CList/Normalize.lean` — adaptar normalize
7. `CList/Filter.lean` — adaptar filter

**Regla:** completar cada sub-módulo con 0 sorry antes de pasar al siguiente.

---

## NEXT — Fase 3: vN embedding

> **Prerrequisito:** Fase 1 (Peano dep) + HFSets.lean estable.
> Puede hacerse en paralelo con Fase 2 si se trabaja sobre los archivos
> de HFSet sin tocar CList.

### Archivos a crear

| Archivo | Contenido |
| --- | --- |
| `AczelSetTheory/VN/Basic.lean` | `vN : ℕ₀ → HFSet`, `vN_zero`, `vN_succ`, `mem_vN_succ` |
| `AczelSetTheory/VN/Injective.lean` | `vN_injective` |
| `AczelSetTheory/VN/IsNat.lean` | `VN.IsVNNat`, `mem_range_iff` |
| `AczelSetTheory/VN/Arithmetic.lean` | `vN_add`, `vN_le_iff`, `mem_vN_iff_lt` |
| `AczelSetTheory/VN/FSet.lean` | `fsetToHFSet`, `mem_fsetToHFSet` |
| `AczelSetTheory/VN/PeanoAxioms.lean` | Axiomas de Peano como teoremas sobre vN |
| `AczelSetTheory/VN/PeanoArith.lean` | Transporte add_comm, mul_assoc, etc. |
| `AczelSetTheory/VN.lean` | Barrel |

---

## Fases 7–11 (HFSet puro, diferidas)

> Estas fases siguen siendo válidas y necesarias. Se retoman
> después de que la infraestructura Peano/PList/vN esté estable.
> El detalle completo de cada fase permanece a continuación.

---

### Phase 7: Adjunción, Inducción ε, Producto Cartesiano

#### 7a. Axioma de Adjunción

**Archivo:** `Axioms/Adjunction.lean`

**Teoremas:**

1. `mem_insert (x b A : HFSet) : x ∈ insert b A ↔ x = b ∨ x ∈ A`
2. `insert_ne_empty (b A : HFSet) : insert b A ≠ empty`
3. `mem_insert_self (b A : HFSet) : b ∈ insert b A`

**Dependencias:** `Notation.lean` (insert ya existe)
**Dificultad:** Baja.

---

#### 7b. Inducción ε

**Archivo:** `Axioms/Induction.lean`

**Teoremas:**

1. `eps_induction (P : HFSet → Prop) (h_empty : P empty)
       (h_adj : ∀ A b, P A → P (insert b A)) : ∀ A, P A`
2. `strong_eps_induction (P : HFSet → Prop)
       (h : ∀ A, (∀ x, x ∈ A → P x) → P A) : ∀ A, P A`

**Estrategia:** inducción sobre `cSize` a nivel CList.
**Dependencias:** `Axioms/Adjunction.lean`
**Dificultad:** Media-baja.

---

#### 7c. Producto Cartesiano

**Archivos:** `Operations/CartProd.lean` + `Axioms/CartProd.lean`

```lean
def cartProdCList (A B : CList) : CList :=
  match A, B with
  | mk as, mk bs =>
    mk (as.flatMap (fun a => bs.map (fun b => mkOrderedPairCList a b)))
```

**Lemas CList:**

1. `mkOrderedPairCList_extEq`
2. `cartProdCList_extEq`
3. `mem_cartProdCList_iff`

**Lema HFSet:**

1. `mem_cartProd (z A B : HFSet) :
     z ∈ cartProd A B ↔ ∃ a b, a ∈ A ∧ b ∈ B ∧ z = ⟪a, b⟫`
2. `cartProd_empty_left`, `cartProd_empty_right`

**Dependencias:** `Operations/OrderedPair.lean`, `Axioms/Foundation.lean`
**Dificultad:** Media.

**Orden:** 7a → 7b → 7c (paralelo a 7b).

---

### Phase 8: Decidabilidad, Álgebra Boole, Anillo Booleano

| Paso | Bloque | Archivo | Depende de | Dificultad |
| --- | --- | --- | --- | --- |
| 8.0 | Decidable | `Axioms/Decidable.lean` | HFSets, CList/Basic | Baja |
| 8a | Subset | `Axioms/Subset.lean` | Union, Intersection | Baja |
| 8b | Lattice | `Axioms/Lattice.lean` | 8a | Baja (~17 teoremas) |
| 8c | Boolean Algebra | `Axioms/BooleanAlgebra.lean` | 8.0, 8a, 8b | Media-baja |
| 8d | Boolean Ring | `Axioms/BooleanRing.lean` | 8.0, 8b, 8c | Media |

**Total fase 8:** ~42 teoremas. Todos por `extensionality` + `mem_*` + lógica.

---

### Phase 9: Von Neumann Natural Numbers (interno en HFSet)

> **Nota:** con el embedding `vN : ℕ₀ → HFSet` de Fase 3, esta fase
> queda integrada. `succ_HFSet` = `vN ∘ σ ∘ vN⁻¹` sobre la imagen.
> Se mantiene aquí para referencia de la construcción interna autónoma.

**Archivos:** `Operations/Succ.lean`, `Axioms/Succ.lean`

```lean
succ A = A ∪ {A}
mem_succ : x ∈ succ A ↔ x ∈ A ∨ x = A
succ_injective
succ_ne_empty
not_mem_self   (de Foundation)
isNat_zero, isNat_succ, isNat_induction
add_vN, mul_vN  (recursivas sobre isNat)
```

---

### Phase 10: Relations and Functions

**Definiciones:**

- `isRelation R A B` — `R ⊆ A × B`
- `isFunction f A B`
- `domain f`, `range f`, `apply f a`

**Archivos:** `Operations/Relation.lean`, `Operations/Function.lean`,
`Axioms/Relation.lean`, `Axioms/Function.lean`

---

### Phase 11: Advanced axioms (ya parcialmente completos)

- Reemplazo: ✅ Complete (`Axioms/Replacement.lean`)
- Elección: ✅ Complete (`Axioms/Choice.lean`)

---

## Hitos completados

- ✅ CList foundations: 7 sub-módulos (Basic, ExtEq, SetEquiv, Order, Sort, Normalize, Filter)
- ✅ `normalize_eq_of_extEq` — último sorry de CList eliminado
- ✅ HFSet quotient type con `repr` y `empty`
- ✅ `HFSet.Mem` y instancia `Membership`
- ✅ Extensionalidad
- ✅ Vacío, Par, Unión, Big Unión, Separación, Intersección, Setminus, Potencia
- ✅ Diferencia Simétrica
- ✅ Fundación (Regularidad)
- ✅ Singleton
- ✅ Par Ordenado (Kuratowski): `⟪a, b⟫ = ⟪c, d⟫ ↔ a = c ∧ b = d`
- ✅ Arquitectura: `Operations/` + `Axioms/`
- ✅ Sistema de notación completo: `∅`, `{[a,b]}`, `{[a]}`, `{[x ∈ A <|> P]}`, `⟪a,b⟫`, numerales vN 0–9
- ✅ Reemplazo (`Axioms/Replacement.lean`)
- ✅ Elección (`Axioms/Choice.lean`)
