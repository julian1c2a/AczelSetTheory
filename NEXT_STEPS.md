# Next Steps

**Last updated:** 2026-04-08

The project compiles on Lean 4.29.0 with **0 sorry**.
All 8 Zermelo axioms (Extensionality, Empty Set, Pairs, Union, Separation, Intersection, Setminus, Powerset)
plus Foundation, Symmetric Difference, Singleton, and Ordered Pair injectivity
are fully derived as theorems over the `HFSet` quotient type.

---

## Completed milestones

- ✅ CList foundations: 7 sub-modules (Basic, ExtEq, SetEquiv, Order, Sort, Normalize, Filter)
- ✅ `normalize_eq_of_extEq` proven — last CList sorry eliminated
- ✅ HFSet quotient type with `repr` and `empty`
- ✅ `HFSet.Mem` and `Membership` instance (in notation)
- ✅ Extensionality: ∀ A B, (∀ x, x ∈ A ↔ x ∈ B) → A = B
- ✅ Empty Set: ∀ x, x ∉ ∅
- ✅ Pairs: x ∈ {a, b} ↔ x = a ∨ x = b
- ✅ Union: z ∈ A ∪ B ↔ z ∈ A ∨ z ∈ B  (`HFSet.mem_union`)
- ✅ Big Union: z ∈ ⋃ A ↔ ∃ Y ∈ A, z ∈ Y  (`HFSet.mem_sUnion`)
- ✅ Separation: x ∈ sep A P ↔ x ∈ A ∧ P x  (`HFSet.mem_sep`)
- ✅ Intersection: x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B  (`HFSet.mem_inter`)
- ✅ Setminus: x ∈ A ∖ B ↔ x ∈ A ∧ x ∉ B  (`HFSet.mem_setminus`)
- ✅ Powerset: B ∈ 𝒫(A) ↔ ∀ x, x ∈ B → x ∈ A  (`HFSet.mem_powerset`)
- ✅ Symmetric Difference: x ∈ symDiff A B ↔ (x ∈ A ∧ x ∉ B) ∨ (x ∈ B ∧ x ∉ A)  (`HFSet.mem_symDiff`)
- ✅ Foundation (Regularity): A ≠ ∅ → ∃ x ∈ A, ∀ y ∈ x, y ∉ A  (`HFSet.foundation`)
- ✅ Singleton: x ∈ {a} ↔ x = a  (`HFSet.mem_singleton`)
- ✅ Ordered Pair (Kuratowski): ⟪a, b⟫ = ⟪c, d⟫ ↔ a = c ∧ b = d  (`HFSet.orderedPair_eq_iff`)
- ✅ Architecture split: `Operations/` (CList-level) + `Axioms/` (HFSet-level)
- ✅ Notation system: emptyset, {[a,b]}, {[a]}, {[x in A <|> P]}, ⟪a, b⟫, von Neumann numerals 0-9

---

## Phase 6: Foundation, Singleton, Ordered Pairs ✅ COMPLETADA

- ✅ 6a. Foundation (Regularity) — `Axioms/Foundation.lean`
- ✅ 6b. Singleton — `Axioms/Singleton.lean`
- ✅ 6c. Ordered Pairs (Kuratowski) — `Operations/OrderedPair.lean` + `Axioms/OrderedPair.lean`

---

## Phase 7: Adjunción, Inducción ε, Producto Cartesiano

### 7a. Axioma de Adjunción (Adjunction)

> "Dados conjuntos A y b, existe el conjunto A ∪ {b}"

**Estado actual**: Ya existe `insert : HFSet → HFSet → HFSet` en `Notation.lean`, que hace
`insertCList x (mk ys) = mk (x :: ys)`. Falta el teorema de membresía al nivel HFSet.

**Archivo**: `Axioms/Adjunction.lean`

**Teoremas a probar**:

1. `mem_insert (x b A : HFSet) : x ∈ insert b A ↔ x = b ∨ x ∈ A`
   - Estrategia: bajar a representantes CList con `Quotient.exists_rep`, usar `CList.mem_cons`
     - `Bool.or_eq_true`, y `Quotient.sound`/`Quotient.exact` para el salto `extEq ↔ =`.
2. `insert_ne_empty (b A : HFSet) : insert b A ≠ empty`
   - Consecuencia directa de `mem_insert` + `not_mem_empty`.
3. `mem_insert_self (b A : HFSet) : b ∈ insert b A`
   - Caso particular de `mem_insert` con `Or.inl rfl`.

**Dependencias**: `Notation.lean` (para `insert`, `insertCList`), `HFSets.lean`

**Dificultad**: Baja. Solo hay que escribir el puente CList → HFSet de `mem_cons`.

---

### 7b. Inducción ε (∈-Induction, forma de Peano para HFSet)

> *Si P(∅) y ∀ A b, P(A) → P(insert b A), entonces ∀ A, P(A).*
>
> Esto es el análogo exacto de la recurrencia de Peano para conjuntos hereditariamente finitos:
> ∅ juega el papel de 0, e `insert` juega el papel de `succ`.

**Archivo**: `Axioms/Induction.lean`

**Teoremas a probar**:

1. `eps_induction (P : HFSet → Prop) (h_empty : P empty)
       (h_adj : ∀ A b, P A → P (insert b A)) : ∀ A, P A`
   - Estrategia: inducción sobre `n ≥ cSize a` a nivel CList (patrón Nat descendente,
     como en Foundation).
   - Caso base: `mk []` es `empty` → usar `h_empty`.
   - Caso inductivo: `mk (x :: xs)` →
     - `insertCList x (mk xs) = mk (x :: xs)` por definición de `insertCList`.
     - Por tanto `⟦mk (x :: xs)⟧ = insert ⟦x⟧ ⟦mk xs⟧` a nivel HFSet.
     - `cSize (mk xs) < cSize (mk (x :: xs))` por aritmética de `cSize`.
     - HI da `P ⟦mk xs⟧`, y `h_adj` da `P (insert ⟦x⟧ ⟦mk xs⟧)`.
   - Punto clave: `insertCList x (mk xs) = mk (x :: xs)` es *definitional* en CList,
     así que la igualdad HFSet es `rfl` al quotientar.

2. (Variante fuerte, opcional) `strong_eps_induction (P : HFSet → Prop)
       (h : ∀ A, (∀ x, x ∈ A → P x) → P A) : ∀ A, P A`
   - Equivalente al axioma de Fundación. Prueba por inducción sobre `cSize`.
   - Caso base: `mk []` → la premisa `∀ x ∈ ∅, P x` vale trivialmente → `P ∅`.
   - Caso inductivo: Para cada `y ∈ mk (x :: xs)`, `cSize y < cSize (mk (x :: xs))`
     por `cSize_lt_of_mem`, luego la HI da `P y`.

**Dependencias**: `Axioms/Adjunction.lean`, `HFSets.lean`, `CList/Basic.lean` (para `cSize`)

**Dificultad**: Media-baja. El esqueleto inductivo sobre CList es directo;
el paso de `insertCList` a `insert` es definitional.

---

### 7c. Producto Cartesiano

**Archivos**: `Operations/CartProd.lean` + `Axioms/CartProd.lean`

#### 7c-i. Definición computacional (`Operations/CartProd.lean`)

```
cartProd A B = { ⟪a, b⟫ | a ∈ A, b ∈ B }
```

No podemos usar `sep` directamente (necesitaría un superconjunto sobre el cual filtrar,
y eso implicaría construir `𝒫(𝒫(A ∪ B))` antes). En su lugar, construimos computacionalmente
a nivel CList:

```lean
def mkOrderedPairCList (a b : CList) : CList :=
  mkPair (mkPair a a) (mkPair a b)

def cartProdCList (A B : CList) : CList :=
  match A, B with
  | mk as, mk bs =>
    mk (as.flatMap (fun a => bs.map (fun b => mkOrderedPairCList a b)))
```

Lemas necesarios a nivel CList:

1. `mkOrderedPairCList_extEq`: si `extEq a₁ a₂` y `extEq b₁ b₂`,
   entonces `extEq (mkOrderedPairCList a₁ b₁) (mkOrderedPairCList a₂ b₂)`.
   - Depende de `mkPair_extEq` (ya probado implícitamente en `Operations/Pair.lean`,
     habrá que extraerlo o re-probarlo).

2. `cartProdCList_extEq`: si `extEq A₁ A₂` y `extEq B₁ B₂`,
   entonces `extEq (cartProdCList A₁ B₁) (cartProdCList A₂ B₂)`.
   - Estrategia: probar que la membresía CList se preserva en ambas direcciones.
   - Lema intermedio: `mem_cartProdCList_iff (z A B : CList) :
     mem z (cartProdCList A B) = true ↔
     ∃ a b, mem a A = true ∧ mem b B = true ∧ extEq z (mkOrderedPairCList a b) = true`
   - Este lema requiere trabajar con `List.mem_flatMap` y `List.mem_map`,
     conectando `List.Mem` (estructural) con `CList.mem` (extensional).
     Se usan los puentes `mem_exists_list_mem` y `mem_of_list_mem` de `Foundation.lean`.

3. Levantar a HFSet:

   ```lean
   def cartProd (A B : HFSet) : HFSet :=
     Quotient.liftOn₂ A B
       (fun a b => ⟦cartProdCList a b⟧)
       (fun _ _ _ _ ha hb => Quotient.sound (cartProdCList_extEq ... ha hb))
   ```

#### 7c-ii. Axioma de membresía (`Axioms/CartProd.lean`)

Teoremas a probar:

1. `mem_cartProd (z A B : HFSet) :
     z ∈ cartProd A B ↔ ∃ a b, a ∈ A ∧ b ∈ B ∧ z = ⟪a, b⟫`
   - Estrategia: bajar a CList con `Quotient.exists_rep`, usar `mem_cartProdCList_iff`,
     traducir `extEq` a `=` via `Quotient.sound`.

2. `cartProd_empty_left (B : HFSet) : cartProd empty B = empty`
   - Directo: `cartProdCList (mk []) B = mk []`.

3. `cartProd_empty_right (A : HFSet) : cartProd A empty = empty`
   - Directo: `flatMap ... [] = []`.

**Dependencias**: `Operations/Pair.lean` (para `mkPair`), `Operations/OrderedPair.lean`,
`CList/Basic.lean`, `Axioms/Foundation.lean` (para `mem_exists_list_mem`, `mem_of_list_mem`)

**Dificultad**: Media. La prueba de `cartProdCList_extEq` es la parte más laboriosa:
requiere conectar `List.flatMap`/`List.map` con la membresía extensional.
El lema `mem_cartProdCList_iff` es el punto central de dificultad.

**Alternativa simplificada** (si `flatMap` resulta incómodo):
Definir un `mapCList (f : CList → CList) (A : CList) : CList` a nivel lista,
y construir `cartProdCList A B = sUnion (mapCList (fun a => mapCList (fun b => mkOrderedPairCList a b) B) A)`,
reutilizando `sUnion_extEq` existente. Esto evita manejar `flatMap` directamente,
pero introduce una indirección adicional.

---

### Orden de implementación

| Paso | Bloque | Archivos | Depende de |
|------|--------|----------|------------|
| **1** | 7a — Adjunción | `Axioms/Adjunction.lean` | `Notation.lean` (insert ya existe) |
| **2** | 7b — Inducción ε | `Axioms/Induction.lean` | 7a |
| **3** | 7c — Producto Cartesiano | `Operations/CartProd.lean` + `Axioms/CartProd.lean` | `Operations/OrderedPair.lean` |

Justificación del orden:

- Adjunción es trivial (completar lo que ya existe: `insert` sin `mem_insert`).
- Inducción ε solo necesita Adjunción y es independiente de Producto Cartesiano.
- Producto Cartesiano es la pieza más laboriosa (flatMap + extEq) e independiente de Inducción.

---

## Phase 8: Decidabilidad, Álgebra Booleana y Anillo Booleano

Objetivo: desarrollar la teoría algebraica completa sobre `HFSet`, dividida en cinco bloques:

- **8.0**: Decidabilidad de la membresía a nivel HFSet.
- **8a**: Prerrequisito — `Subset` a nivel HFSet + propiedades básicas.
- **8b**: Retículo distributivo acotado — propiedades algebraicas de `∪`, `∩`, `∅` sobre todos los HFSets
  (los postulados de Huntington que NO requieren complemento).
- **8c**: Álgebra de Boole sobre `𝒫(U)` — para un conjunto fijo `U`, el complemento relativo
  `compl U X = setminus U X` permite completar los postulados de Huntington.
- **8d**: Anillo booleano — `(symDiff, ∩, ∅)` forma un anillo conmutativo con unidad sobre `𝒫(U)`.

---

### 8.0. Decidabilidad de la membresía en HFSet

**Estado actual**: `CList.mem : CList → CList → Bool` es decidible computacionalmente.
`HFSet.Mem` está definido vía `Quotient.lift₂` sobre `CList.mem`. Sin embargo, no existe
una instancia `Decidable (x ∈ A)` a nivel HFSet, lo que impide usar `by_cases (x ∈ A)`
sin `Classical.em`.

**Archivo**: `HFSets.lean` (añadir al final) o `Axioms/Decidable.lean` (archivo propio)

**Definiciones y teoremas**:

1. `instance mem_decidable (x A : HFSet) : Decidable (x ∈ A)`
   - Estrategia: bajar a representantes CList con `Quotient.exists_rep` (o `Quotient.inductionOn₂`),
     evaluar `CList.mem xc ac` (que es `Bool`), y usar `Bool.decEq` / `decide`:

     ```lean
     instance mem_decidable (x A : HFSet) : Decidable (x ∈ A) :=
       Quotient.recOnSubsingleton₂ x A fun xc ac =>
         match h : CList.mem xc ac with
         | true  => isTrue  (by show CList.mem xc ac = true; exact h)
         | false => isFalse (by show ¬ (CList.mem xc ac = true); rw [h]; simp)
     ```

   - **Alternativa**: si `HFSet.Mem` se define como `CList.mem xc ac = true` (vía `Quotient.lift₂`),
     la decidibilidad es directa porque `Bool` es decidible.

2. `instance eq_decidable (A B : HFSet) : DecidableEq HFSet`
   - Estrategia: `A = B ↔ A.repr = B.repr` (por `canonicalEq_iff_eq`), y `CList` tiene
     `DecidableEq` (estructural sobre listas). Así: decidir `A.repr = B.repr` decide `A = B`.
   - Alternativamente, usar `extEq` sobre representantes.

**Consecuencias**:

- `by_cases (x ∈ A)` funciona sin `Classical.em` en todas las pruebas posteriores.
- `Decidable (A ⊆ B)` se deriva automáticamente (∀ finito sobre membresía decidible),
  aunque para `∀ x, x ∈ A → x ∈ B` necesitaríamos un `Fintype` o recorrer la CList.
- Habilita `decide` / `Decidable.decide` para verificación computacional de proposiciones
  sobre conjuntos concretos.

**Dependencias**: `HFSets.lean`, `CList/Basic.lean`

**Dificultad**: Baja. El punto clave es elegir la función `Quotient.recOnSubsingleton₂`
para asegurar que `Decidable` es una `Subsingleton` y el Quotient lo acepta.

---

### 8a. Prerrequisito: Subset a nivel HFSet

**Estado actual**: `CList.subset` (Bool) y `subset_refl`, `subset_trans`, `subset_iff_forall_mem_clist`
existen en `CList/ExtEq.lean` y `CList/SetEquiv.lean`. No existe `Subset` a nivel HFSet.

**Archivo**: `Axioms/Subset.lean`

**Definiciones y teoremas**:

1. `def Subset (A B : HFSet) : Prop := ∀ x, x ∈ A → x ∈ B`
2. `instance : HasSubset HFSet := ⟨Subset⟩` — habilita notación `⊆`
3. `subset_iff (A B : HFSet) : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B` — desplegado trivial
4. `subset_refl (A : HFSet) : A ⊆ A`
5. `subset_trans (A B C : HFSet) : A ⊆ B → B ⊆ C → A ⊆ C`
6. `subset_antisymm (A B : HFSet) : A ⊆ B → B ⊆ A → A = B` — via `extensionality`
7. `empty_subset (A : HFSet) : empty ⊆ A` — via `not_mem_empty`
8. `subset_union_left (A B : HFSet) : A ⊆ union A B`
9. `subset_union_right (A B : HFSet) : B ⊆ union A B`
10. `inter_subset_left (A B : HFSet) : inter A B ⊆ A`
11. `inter_subset_right (A B : HFSet) : inter A B ⊆ B`
12. `subset_inter (A B C : HFSet) : A ⊆ B → A ⊆ C → A ⊆ inter B C`

**Estrategia**: Todos se prueban directamente con `intro x hx`, `rw [mem_union]`/`rw [mem_inter]`,
y lógica proposicional. No necesitan bajar a CList.

**Dependencias**: `Axioms/Union.lean`, `Axioms/Intersection.lean`, `HFSets.lean` (extensionality)

**Dificultad**: Baja.

---

### 8b. Retículo distributivo acotado (HFSets generales)

Los HFSets con `(∪, ∩, ∅)` forman un **retículo distributivo acotado inferiormente**.
No es un álgebra de Boole porque no existe un elemento máximo universal (no hay "conjunto de todos los conjuntos"),
y por tanto no hay complemento absoluto.

Los postulados de Huntington que SÍ se cumplen son todos los referidos a `∪` e `∩`.

**Archivo**: `Axioms/Lattice.lean`

**Teoremas a probar** (divididos en grupos):

#### Conmutatividad

1. `union_comm (A B : HFSet) : union A B = union B A`
   - Por `extensionality`: `x ∈ union A B ↔ x ∈ union B A` via `mem_union` + `Or.comm`.
2. `inter_comm (A B : HFSet) : inter A B = inter B A`
   - Análogo con `mem_inter` + `And.comm`.

#### Asociatividad

1. `union_assoc (A B C : HFSet) : union (union A B) C = union A (union B C)`
   - `mem_union` dos veces + `Or.assoc`.
2. `inter_assoc (A B C : HFSet) : inter (inter A B) C = inter A (inter B C)`
   - `mem_inter` dos veces + `And.assoc`.

#### Idempotencia

1. `union_idem (A : HFSet) : union A A = A`
   - `mem_union` + `Or.idem`.
2. `inter_idem (A : HFSet) : inter A A = A`
   - `mem_inter` + `And.idem` (`⟨fun ⟨h, _⟩ => h, fun h => ⟨h, h⟩⟩`).

#### Absorción (Huntington)

1. `union_inter_absorb (A B : HFSet) : union A (inter A B) = A`
   - `→`: `mem_union` da `x ∈ A ∨ (x ∈ A ∧ x ∈ B)` → `x ∈ A` en ambos casos.
   - `←`: `Or.inl`.
2. `inter_union_absorb (A B : HFSet) : inter A (union A B) = A`
   - `→`: `x ∈ A ∧ (x ∈ A ∨ x ∈ B)` → `x ∈ A` por `.1`.
   - `←`: `⟨h, Or.inl h⟩`.

#### Distributividad

1. `union_inter_distrib (A B C : HFSet) : union A (inter B C) = inter (union A B) (union A C)`
   - `extensionality` + `mem_union`/`mem_inter` + lógica proposicional:
     `a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c)`.
2. `inter_union_distrib (A B C : HFSet) : inter A (union B C) = union (inter A B) (inter A C)`
    - Análogo: `a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c)`.

#### Elemento neutro

1. `union_empty (A : HFSet) : union A empty = A`
    - `mem_union` + `not_mem_empty` → el disyunto derecho es siempre falso.
2. `empty_union (A : HFSet) : union empty A = A`
    - Consecuencia de `union_comm` + `union_empty`.
3. `inter_empty (A : HFSet) : inter A empty = empty`
    - `mem_inter` + `not_mem_empty` → la conjunción es siempre falsa.
4. `empty_inter (A : HFSet) : inter empty A = empty`
    - Consecuencia de `inter_comm` + `inter_empty`.

#### Setminus como "complemento relativo" (propiedades básicas)

1. `setminus_self (A : HFSet) : setminus A A = empty`
    - `mem_setminus` → `x ∈ A ∧ x ∉ A` es absurdo.
2. `setminus_empty (A : HFSet) : setminus A empty = A`
    - `mem_setminus` + `not_mem_empty` (el `¬ x ∈ ∅` siempre vale).
3. `empty_setminus (A : HFSet) : setminus empty A = empty`
    - `mem_setminus` + `not_mem_empty`.

**Estrategia general**: Todos estos teoremas siguen el mismo patrón:
`apply extensionality; intro x; rw [mem_..., mem_...]; constructor <;> intro h <;> [lógica]`.
Son 17 teoremas pero todos mecánicos y de dificultad baja.

**Dependencias**: `Axioms/Union.lean`, `Axioms/Intersection.lean`, `Axioms/Setminus.lean`,
`HFSets.lean` (extensionality, not_mem_empty)

**Dificultad**: Baja. Todos son reescrituras + proposiciones de lógica elemental.

---

### 8c. Álgebra de Boole sobre 𝒫(U)

Para un conjunto fijo `U : HFSet`, definimos el complemento relativo y probamos que
`(𝒫(U), ∪, ∩, compl_U, ∅, U)` satisface los postulados completos de Huntington,
es decir, es un **álgebra de Boole**.

**Archivo**: `Axioms/BooleanAlgebra.lean`

**Definiciones**:

1. `def compl (U X : HFSet) : HFSet := setminus U X`
   - Notación opcional: ninguna global (para evitar ambigüedad), se usa `compl U X` explícitamente.

**Precondición clave**: muchos teoremas requieren la hipótesis `hX : X ⊆ U` (es decir, `X ∈ 𝒫(U)`).

**Teoremas a probar**:

#### Postulados de Huntington para complemento

1. `compl_mem_powerset (U X : HFSet) (hX : X ⊆ U) : compl U X ⊆ U`
   - `mem_setminus` → `x ∈ U ∧ x ∉ X` → `x ∈ U`.
   - Es decir: el complemento relativo permanece en `𝒫(U)`.

2. `union_compl (U X : HFSet) (hX : X ⊆ U) : union X (compl U X) = U`
   - `→`: ambos disyuntos dan `x ∈ U` (el primero por `hX`, el segundo por def. de `compl`).
   - `←`: `x ∈ U` → por `mem_decidable`: si `x ∈ X` entonces `Or.inl`;
     si `x ∉ X` entonces `Or.inr` (por `mem_setminus`).
   - **Nota**: Usa `mem_decidable` de 8.0 (no necesita `Classical.em`).

3. `inter_compl (U X : HFSet) (hX : X ⊆ U) : inter X (compl U X) = empty`
   - `mem_inter` + `mem_setminus` → `x ∈ X ∧ (x ∈ U ∧ x ∉ X)` → contradicción.

4. `compl_compl (U X : HFSet) (hX : X ⊆ U) : compl U (compl U X) = X`
   - `mem_setminus` dos veces + doble negación (`¬¬(x ∈ X) ↔ x ∈ X`, decidible vía `mem_decidable`).

5. `compl_empty (U : HFSet) : compl U empty = U`
   - Caso particular de `setminus_empty`.

6. `compl_self (U : HFSet) : compl U U = empty`
   - Caso particular de `setminus_self`.

#### Leyes de De Morgan

1. `compl_union (U A B : HFSet) (hA : A ⊆ U) (hB : B ⊆ U) :
     compl U (union A B) = inter (compl U A) (compl U B)`
   - `extensionality` + `mem_setminus`/`mem_union`/`mem_inter` +
     De Morgan proposicional: `x ∈ U ∧ ¬(x ∈ A ∨ x ∈ B) ↔ (x ∈ U ∧ ¬x ∈ A) ∧ (x ∈ U ∧ ¬x ∈ B)`.
   - Requiere `hA`/`hB` para la dirección `←` (asegurar `x ∈ U`).

2. `compl_inter (U A B : HFSet) (hA : A ⊆ U) (hB : B ⊆ U) :
     compl U (inter A B) = union (compl U A) (compl U B)`
   - Análogo con De Morgan: `x ∈ U ∧ ¬(x ∈ A ∧ x ∈ B) ↔ (x ∈ U ∧ ¬x ∈ A) ∨ (x ∈ U ∧ ¬x ∈ B)`.
   - La dirección `←` necesita: si `x ∈ U ∧ ¬ x ∈ A`, entonces `¬ (x ∈ A ∧ x ∈ B)`.
   - La dirección `→` necesita `mem_decidable` para descomponer `¬ (∧)`.

#### Propiedades adicionales del complemento

1. `compl_subset_swap (U A B : HFSet) (hA : A ⊆ U) (hB : B ⊆ U) :
     A ⊆ B ↔ compl U B ⊆ compl U A`
   - Contrapositivo: `x ∈ A → x ∈ B` ↔ `x ∉ B → x ∉ A`.

2. `union_compl_inter (U A B : HFSet) (hA : A ⊆ U) (hB : B ⊆ U) :
      union (inter A B) (inter A (compl U B)) = A`
    - Factorización: `A ∩ B ∪ A ∩ B^c = A ∩ (B ∪ B^c) = A ∩ U = A`.
    - Usa `inter_union_distrib` (de 8b), `union_compl`, `inter` con `U`.
    - Necesita también: `inter_full`: `inter A U = A` cuando `A ⊆ U` (lema auxiliar).

**Lemas auxiliares necesarios** (se pueden poner en este mismo archivo):

- `inter_full (U A : HFSet) (hA : A ⊆ U) : inter A U = A`
  - `mem_inter` → `x ∈ A ∧ x ∈ U`; `←` usa `hA`.
- `full_inter (U A : HFSet) (hA : A ⊆ U) : inter U A = A`
  - Por `inter_comm` + `inter_full`.

**Estrategia general**: Misma que en 8b — `extensionality` + reescritura con `mem_*` + lógica.
La instancia `mem_decidable` de 8.0 se usa para De Morgan y doble negación.

**Dependencias**: Fase 8.0 (Decidable), Fase 8a (Subset), Fase 8b (Lattice), `Axioms/Setminus.lean`

**Dificultad**: Media-baja. Las pruebas son mecánicas pero las hipótesis `hX : X ⊆ U`
añaden un poco de gestión extra respecto a 8b.

---

### 8d. Anillo booleano via `symDiff` e `∩`

El anillo booleano es la estructura `(𝒫(U), △, ∩, ∅, U)` donde:

- **Suma**: `symDiff A B` (diferencia simétrica), con neutro `∅`.
- **Producto**: `inter A B` (intersección), con unidad `U`.

**Archivo**: `Axioms/BooleanRing.lean`

**Teoremas a probar**:

#### Grupo abeliano `(symDiff, ∅)`

1. `symDiff_comm (A B : HFSet) : symDiff A B = symDiff B A`
   - `mem_symDiff` + `Or.comm` sobre los dos disyuntos.

2. `symDiff_assoc (A B C : HFSet) : symDiff (symDiff A B) C = symDiff A (symDiff B C)`
   - `extensionality` + `mem_symDiff` tres veces.
   - La parte proposicional: `((a ∧ ¬b) ∨ (b ∧ ¬a)) xor c ↔ a xor ((b ∧ ¬c) ∨ (c ∧ ¬b))`.
   - **Estrategia**: expandir completamente con `mem_symDiff`, `mem_union`, `mem_setminus`,
     y usar `tauto` o análisis de casos con `mem_decidable`:
     `by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;> by_cases hC : x ∈ C <;> simp_all`.
   - **Dificultad**: Este es el teorema más laborioso del bloque. La prueba proposicional
     requiere 8 casos (2³ combinaciones de pertenencia).

3. `symDiff_empty (A : HFSet) : symDiff A empty = A`
   - `mem_symDiff` + `not_mem_empty`: el primer disyunto da `x ∈ A ∧ True`, el segundo `x ∈ ∅ ∧ ...` es absurdo.

4. `empty_symDiff (A : HFSet) : symDiff empty A = A`
   - Por `symDiff_comm` + `symDiff_empty`.

5. `symDiff_self (A : HFSet) : symDiff A A = empty`
   - `mem_symDiff` → `(x ∈ A ∧ x ∉ A) ∨ (x ∈ A ∧ x ∉ A)` → ambos absurdos.
   - Es decir: cada elemento es su propio inverso aditivo (`A △ A = ∅`).

#### Monoide `(∩, U)` sobre 𝒫(U)

Los teoremas `inter_comm`, `inter_assoc` ya están en 8b.

1. `inter_full (U A : HFSet) (hA : A ⊆ U) : inter A U = A`
   - Ya definido como lema auxiliar en 8c (unidad del producto).

#### Distributividad del producto sobre la suma

1. `inter_symDiff_distrib (A B C : HFSet) :
     inter A (symDiff B C) = symDiff (inter A B) (inter A C)`
   - `extensionality` + `mem_inter`/`mem_symDiff`.
   - Proposicional: `a ∧ ((b ∧ ¬c) ∨ (c ∧ ¬b)) ↔ (a ∧ b ∧ ¬(a ∧ c)) ∨ (a ∧ c ∧ ¬(a ∧ b))`.
   - **Estrategia**: `by_cases` sobre `x ∈ A`, `x ∈ B`, `x ∈ C` (8 casos, usa `mem_decidable`).

#### Propiedad característica del anillo booleano

1. `inter_self_eq (A : HFSet) : inter A A = A`
   - Ya es `inter_idem` de 8b. En un anillo booleano esto dice `a² = a` (idempotencia del producto),
     que es la propiedad que distingue anillos booleanos de anillos conmutativos generales.

#### Conexión con álgebra de Boole (teorema puente)

1. `symDiff_eq_union_setminus (A B : HFSet) :
     symDiff A B = setminus (union A B) (inter A B)`
   - `extensionality` + `mem_symDiff`/`mem_setminus`/`mem_union`/`mem_inter`.
   - Proposicional: `(a ∧ ¬b) ∨ (b ∧ ¬a) ↔ (a ∨ b) ∧ ¬(a ∧ b)`.

2. `symDiff_via_compl (U A B : HFSet) (hA : A ⊆ U) (hB : B ⊆ U) :
      symDiff A B = union (inter A (compl U B)) (inter B (compl U A))`
    - Conecta la definición set-teórica con la del álgebra de Boole.
    - Proposicional directa con `mem_setminus` y la definición de `compl`.

**Dependencias**: Fase 8.0 (Decidable), Fase 8b (Lattice), Fase 8c (BooleanAlgebra),
`Axioms/SymDiff.lean`

**Dificultad**: Media. `symDiff_assoc` e `inter_symDiff_distrib` son las pruebas más
laboriosas (8 casos cada una), pero la estrategia `by_cases` con `mem_decidable` es mecánica.

---

### Orden de implementación de la Fase 8

| Paso | Bloque | Archivo | Depende de | Dificultad |
|------|--------|---------|------------|------------|
| **0** | 8.0 — Decidable | `HFSets.lean` o `Axioms/Decidable.lean` | HFSets, CList/Basic | Baja |
| **1** | 8a — Subset | `Axioms/Subset.lean` | Union, Intersection | Baja |
| **2** | 8b — Lattice | `Axioms/Lattice.lean` | 8a, Union, Intersection, Setminus | Baja |
| **3** | 8c — Boolean Algebra | `Axioms/BooleanAlgebra.lean` | 8.0, 8a, 8b, Setminus | Media-baja |
| **4** | 8d — Boolean Ring | `Axioms/BooleanRing.lean` | 8.0, 8b, 8c, SymDiff | Media |

**Estimación total**: ~42 teoremas (incluyendo decidabilidad), todos demostrables por
`extensionality` + reescritura `mem_*` + lógica. El bloque más exigente es 8d por las
pruebas de asociatividad/distributividad con 8 ramas cada una, pero `mem_decidable`
permite `by_cases` sin axiomas clásicos.

---

## Phase 9: Von Neumann Natural Numbers

### 9a. Successor function

**Definition**: `succ A = A cup {A}` (using `union` and `singleton`)

**Key theorems**:

1. `mem_succ : x in succ A <-> x in A or x = A`
2. `succ_injective : succ A = succ B -> A = B`
3. `succ_ne_empty : succ A != emptyset`
4. `not_mem_self : not (A in A)` (follows from Foundation)

**Files**: `Operations/Succ.lean`, `Axioms/Succ.lean`

### 9b. Natural number predicate

**Definition**: Inductive characterization of "is a natural number" via transitive sets + Foundation.

```lean
def isNat : HFSet -> Prop
| x => x = emptyset or exists y, isNat y and x = succ y
```

Or alternatively: `isTransitive A and (forall x in A, isTransitive x)`

**Key theorems**:

1. `isNat_zero : isNat 0`
2. `isNat_succ : isNat n -> isNat (succ n)`
3. `isNat_induction : isNat n -> P 0 -> (forall k, isNat k -> P k -> P (succ k)) -> P n`

### 9c. Arithmetic operations

**Definitions** (recursive over `isNat`):

1. `add (m n : HFSet) : HFSet` — m + 0 = m, m + succ(n) = succ(m + n)
2. `mul (m n : HFSet) : HFSet` — m *0 = 0, m* succ(n) = m * n + m

**Key theorems**:

- `add_zero`, `add_succ`, `add_comm`, `add_assoc`
- `mul_zero`, `mul_succ`, `mul_comm`, `mul_assoc`, `mul_dist`

**Challenge**: These definitions require well-founded recursion or a recursion principle for `isNat`. Since membership is well-founded in HFSets, we can use `cSize` as termination measure.

**Files**: `Operations/Nat.lean`, `Axioms/Nat.lean`

---

## Phase 10: Relations and Functions

### 10a. Relations and functions

**Definitions**:

- `isRelation R A B` — R subseteq prod A B
- `isFunction f A B` — isRelation f A B and forall a in A, exists! b, orderedPair a b in f
- `domain f`, `range f`
- `apply f a` — the unique b such that orderedPair a b in f

**Files**: `Operations/Relation.lean`, `Operations/Function.lean`,
`Axioms/Relation.lean`, `Axioms/Function.lean`

---

## Phase 11: Advanced axioms

### 11a. Replacement axiom

**Statement**: If F is a function-class and A is a set, then {F(x) | x in A} is a set.

In our finite setting, this is provable by induction on the size of A, using `sep` and `union`.

**Status**: ✅ Complete

**Definitions**:

- `image f A` — image of set A under function/relation f: `{b ∈ range f | ∃ a ∈ A, ⟪a, b⟫ ∈ f}`

**Theorems**:

- `mem_image (f A y)` — `y ∈ image f A ↔ ∃ x, x ∈ A ∧ ⟪x, y⟫ ∈ f`
- `image_empty (f)` — `image f ∅ = ∅`
- `image_of_empty (A)` — `image ∅ A = ∅`
- `image_subset_range (f A y)` — `y ∈ image f A → y ∈ range f`
- `apply_mem_image (f A x)` — function application lands in image
- `image_totalFunction_subset (f A B y)` — image under total function is subset of codomain

**Files**: `Operations/Replacement.lean`, `Axioms/Replacement.lean`

### 11b. Axiom of Choice

In hereditarily finite sets, Choice is derivable from the well-ordering of CList (already established via `lt_total`). For any family of non-empty finite sets, we can computably select an element from each.

**Proof strategy**: Use `lt`-minimal element selection (already implicit in the CList ordering).

**Status**: ✅ Complete

**Definitions**:

- `choose A h` — (noncomputable) selects an element from non-empty A

**Theorems**:

- `nonempty_of_ne_empty (A)` — `A ≠ ∅ → ∃ x, x ∈ A`
- `choose_mem (A h)` — `choose A h ∈ A`
- `choice_principle (F)` — meta-level AC: `∃ f, ∀ A ∈ F, f A ∈ A`

**Files**: `Axioms/Choice.lean`

---

## Future directions

- Decidability of further HFSet predicates beyond `Mem` (e.g., `Decidable (A ⊆ B)` via CList traversal)
- Computable functions HFSet -> HFSet (eval framework)
- Connection to Peano arithmetic via the von Neumann encoding
- Formal verification of set-theoretic constructions (ordinals, cardinals)
