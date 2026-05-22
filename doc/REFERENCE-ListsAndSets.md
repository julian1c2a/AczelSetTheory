# REFERENCE — ListsAndSets

> **Proyecto**: Peano
> **Rama**: `migracion_de_REFERENCE`
> **Fecha**: 2026-05-10
> **Nodo**: `doc/REFERENCE-ListsAndSets.md`
> **Volver al índice**: [REFERENCE.md](../REFERENCE.md)

---

## Módulos cubiertos

| Archivo | Namespace | Descripción |
| --- | --- | --- |
| `Peano/PeanoNat/ListsAndSets/List.lean` | `Peano.List` | Tipos de lista, orden lex, Sorted, instancias |
| `Peano/PeanoNat/ListsAndSets/FSet.lean` | `Peano.FSet` | Conjuntos finitos canonizados (listas ordenadas) |
| `Peano/PeanoNat/ListsAndSets/FSetFunction.lean` | `Peano.FSetFunction` | Funciones entre conjuntos finitos; cardinalidad |
| `Peano/PeanoNat/ListsAndSets/EquivRel.lean` | `Peano.EquivRel` | Relaciones de equivalencia sobre dominios finitos |

Cada módulo tiene un bloque `export` explícito que re-exporta sus símbolos públicos al scope `Peano`.

---

## Módulo: List

**Archivo**: `Peano/PeanoNat/ListsAndSets/List.lean`
**Namespace**: `Peano.List`

El módulo provee infraestructura para listas Lean 4 sobre tipos de Peano: órdenes, instancias, aliases de tipos de lista, y tipos suma. La mayoría son **instancias** o **aliases** (`abbrev`); solo se documentan en detalle los símbolos estructurales.

---

### §1. Instancias de `DecidableEq` / Órdenes sobre `ℕ₁`, `ℕ₂`

| Símbolo | Tipo | Descripción |
| --- | --- | --- |
| `instDecidableEqN1` | `instance` | `DecidableEq ℕ₁` |
| `instDecidableEqN2` | `instance` | `DecidableEq ℕ₂` |
| `instLTN1` | `instance` | `LT ℕ₁` — lift de `lt₀` |
| `instLEN1` | `instance` | `LE ℕ₁` — lift de `le₀` |
| `instLTN2` | `instance` | `LT ℕ₂` — lift de `LT ℕ₁` |
| `instLEN2` | `instance` | `LE ℕ₂` — lift de `LE ℕ₁` |
| `decidableLtN1` | `instance` | `Decidable (a < b : ℕ₁)` |
| `decidableLeN1` | `instance` | `Decidable (a ≤ b : ℕ₁)` |
| `decidableLtN2` | `instance` | `Decidable (a < b : ℕ₂)` |
| `decidableLeN2` | `instance` | `Decidable (a ≤ b : ℕ₂)` |
| `instStrictLinearOrderNat1` | `instance` | `StrictLinearOrder ℕ₁` |
| `instStrictLinearOrderNat2` | `instance` | `StrictLinearOrder ℕ₂` |

---

### §2. Orden lexicográfico sobre `ℕ₂ × ℕ₁`

- **Importancia**: `@importance: medium`

| Símbolo | Tipo | Descripción |
| --- | --- | --- |
| `lexLt` | `def` | Orden lex: `(a₁, b₁) < (a₂, b₂)` si `a₁ < a₂` o bien `a₁ = a₂ ∧ b₁ < b₂` |
| `instLTProdN2N1` | `instance` | `LT (ℕ₂ × ℕ₁)` usando `lexLt` |
| `decidableLexLt` | `instance` | `Decidable (lexLt p q)` |

---

### §3. `lengthₚ`

- **Tipo**: `def`
- **Módulo**: `Peano/PeanoNat/ListsAndSets/List.lean`
- **Namespace**: `Peano.List`
- **Importancia**: `@importance: medium`
- **Computable**: ✅
- **Firma Lean 4**:

  ```lean
  def lengthₚ : List α → ℕ₀
    | []      => 𝟘
    | _ :: t  => σ (lengthₚ t)
  ```

- **Notación matemática**: La longitud de una lista como elemento de $\mathbb{N}_0$ (en lugar del `Nat` de Lean 4).

| Símbolo | Descripción |
| --- | --- |
| `lengthₚ_nil` | `lengthₚ [] = 𝟘` |
| `lengthₚ_cons` | `lengthₚ (a :: l) = σ (lengthₚ l)` |

---

### §4. `Sorted`

- **Tipo**: `def` (predicado inductivo)
- **Módulo**: `Peano/PeanoNat/ListsAndSets/List.lean`
- **Namespace**: `Peano.List`
- **Importancia**: `@importance: high`
- **Firma Lean 4**:

  ```lean
  def Sorted (r : α → α → Prop) : List α → Prop
    | []      => True
    | [_]     => True
    | a :: b :: t => r a b ∧ Sorted r (b :: t)
  ```

- **Descripción**: Inductivo que certifica que una lista está `r`-ordenada. Instancia clave: `Sorted (· < ·)` es el invariante de `FSet`.

| Símbolo | Descripción |
| --- | --- |
| `sorted_nil` | `Sorted r []` |
| `sorted_singleton` | `Sorted r [a]` |

---

### §5. Aliases de tipos de lista

- **Importancia**: `@importance: medium`

| Símbolo | Definición | Descripción |
| --- | --- | --- |
| `decidableMemList` | `instance` | `Decidable (a ∈ l)` para listas decidibles |
| `Nat0List` | `abbrev` | `List ℕ₀` |
| `Nat1List` | `abbrev` | `List ℕ₁` |
| `Nat2List` | `abbrev` | `List ℕ₂` |
| `FactList` | `abbrev` | `List (ℕ₂ × ℕ₁)` — listas de pares (primo, exponente) |
| `Fin₀` | `abbrev` | `{ n : ℕ₀ // lt₀ n m }` — segmento inicial de ℕ₀ |
| `instDecidableEqFin0` | `instance` | `DecidableEq (Fin₀ m)` |
| `DigitList` | `abbrev` | `List (Fin₀ b)` — dígitos en base `b` |
| `TupleList` | `abbrev` | `List ℕ₀` — longitud variable de tuplas |
| `NatsTupleList` | `abbrev` | `List ℕ₀` |
| `GTupleList` | `abbrev` | `List (Nat0List)` — tuplas genéricas |
| `HTupleList` | `abbrev` | alias heterogéneo |

---

### §6. `PeanoVal`

- **Tipo**: `inductive`
- **Módulo**: `Peano/PeanoNat/ListsAndSets/List.lean`
- **Namespace**: `Peano.List`
- **Importancia**: `@importance: medium`
- **Computable**: ✅
- **Descripción**: Tipo suma `ℕ₀ ⊕ ℕ₁ ⊕ ℕ₂` para listas heterogéneas. Permite mezclar valores de distintos tipos de Peano en una sola lista.

| Símbolo | Descripción |
| --- | --- |
| `instDecidableEqPeanoVal` | `DecidableEq PeanoVal` |
| `PeanoValList` | `abbrev` — `List PeanoVal` |
| `peanoValEncode` | Codificación `PeanoVal → List Nat` (canónica) |
| `instLTPeanoVal` / `instLEPeanoVal` | Orden total sobre `PeanoVal` |
| `instDecidableRelLtPeanoVal` / `instDecidableRelLePeanoVal` | Decidabilidad de órdenes |
| `instReprPeanoVal` | `Repr PeanoVal` |

---

### §7. `getDₚ` / `List.indexOfₚ`

- **Importancia**: `@importance: medium`

| Símbolo | Firma resumida | Descripción |
| --- | --- | --- |
| `getDₚ` | `getDₚ (l : List α) (i : ℕ₀) (d : α) : α` | Acceso seguro a la posición `i`, devuelve `d` si fuera de rango |
| `getDₚ_cons_zero` | `getDₚ (a :: l) 𝟘 d = a` | Base de la recursión |
| `getDₚ_cons_succ` | `getDₚ (a :: l) (σ i) d = getDₚ l i d` | Paso recursivo |
| `getDₚ_mem` | `i ∈ range → getDₚ l i d ∈ l` | Elemento en la lista |
| `List.indexOfₚ` | `indexOfₚ (l : List α) (a : α) : ℕ₀` | Primera posición de `a` en `l` |
| `List.indexOfₚ_nil` | `indexOfₚ [] a = 𝟘` | Convención: 𝟘 si no está |
| `List.indexOfₚ_cons_eq` | `indexOfₚ (a :: _) a = 𝟘` | Elemento al inicio |
| `List.indexOfₚ_cons_ne` | `h : a ≠ b → indexOfₚ (b :: l) a = σ (indexOfₚ l a)` | |
| `getDₚ_indexOfₚ` | `a ∈ l → getDₚ l (indexOfₚ l a) d = a` | Coherencia get/indexOf |
| `List.indexOfₚ_lt_length` | `a ∈ l → lt₀ (indexOfₚ l a) (lengthₚ l)` | Cota del índice |

---

### §8. Orden `natsKindLt` y variantes

- **Importancia**: `@importance: low`

| Símbolo | Tipo | Descripción |
| --- | --- | --- |
| `natsKindLt` | `def` | Orden sobre `PeanoVal` que prioriza por "tipo" (ℕ₀ < ℕ₁ < ℕ₂) |
| `instLTNats` / `instLENats` | `instance` | LT/LE para listas de `PeanoVal` |
| `instDecidableRelLtNats` / `instDecidableRelLeNats` | `instance` | Decidabilidad |

---

### §9. Instancias de orden sobre `List`

- **Importancia**: `@importance: low`

| Símbolo | Descripción |
| --- | --- |
| `instIrreflListLt` | Irreflexividad del orden lex sobre `List` |
| `instAsymmListLt` | Asimetría del orden lex sobre `List` |
| `instTrichotomousListLt` | Tricotomía del orden lex sobre `List` |
| `instLEList` | `LE (List α)` — `l ≤ m ↔ l < m ∨ l = m` |
| `instDecidableLeList` | Decidabilidad de `l ≤ m` |

---

## Módulo: FSet

**Archivo**: `Peano/PeanoNat/ListsAndSets/FSet.lean`
**Namespace**: `Peano.FSet`

---

### §10. `FSet`

- **Tipo**: `structure`
- **Módulo**: `Peano/PeanoNat/ListsAndSets/FSet.lean`
- **Namespace**: `Peano.FSet`
- **Importancia**: `@importance: high`
- **Computable**: ✅
- **Firma Lean 4**:

  ```lean
  structure FSet (α : Type) [DecidableEq α] [LT α] where
    elems  : List α
    sorted : Sorted (· < ·) elems
  ```

- **Notación matemática**: Conjunto finito en forma canónica: una lista estrictamente ordenada sin duplicados. La canonicidad garantiza `FSet.ext`.
- **Descripción**: La estructura fundamental para conjuntos finitos decidibles en Peano. Los alias `ℕ₀FSet`, `ℕ₁FSet`, `ℕ₂FSet` son casos particulares con `α = ℕ₀, ℕ₁, ℕ₂`.

---

### §11. `FSet.ext` / `FSet.eq_of_mem_iff`

- **Importancia**: `@importance: high`

| Símbolo | Firma resumida |
| --- | --- |
| `FSet.ext` | `s₁.elems = s₂.elems → s₁ = s₂` |
| `FSet.eq_of_mem_iff` | `(∀ x, x ∈ s₁.elems ↔ x ∈ s₂.elems) → s₁ = s₂` (requiere `StrictLinearOrder`) |
| `FSet.eq_of_mem_iff'` | Variante bidireccional más directa de `eq_of_mem_iff` |

---

### §12. Aliases de tipos de `FSet`

- **Importancia**: `@importance: medium`

| Símbolo | Tipo subyacente | Descripción |
| --- | --- | --- |
| `ℕ₀FSet` | `FSet ℕ₀` | Conjunto finito de naturales de Peano |
| `ℕ₁FSet` | `FSet ℕ₁` | Conjunto finito de `ℕ₁ = { n : ℕ₀ // 𝟙 ≤ n }` |
| `ℕ₂FSet` | `FSet ℕ₂` | Conjunto finito de `ℕ₂ = { p : ℕ₁ // es primo }` |
| `NatsFSet` | `FSet PeanoVal` | Conjunto finito heterogéneo |
| `FactFSet` | `FSet (ℕ₂ × ℕ₁)` | Conjunto de factorizaciones (clave = primo, valor = exponente) |

---

### §13. `UniqueKeys` / `SortedByKey`

- **Tipo**: `def` (proposiciones)
- **Importancia**: `@importance: medium`
- **Firmas Lean 4**:

  ```lean
  def UniqueKeys (l : FactList) : Prop := ...
  def SortedByKey (l : FactList) : Prop := ...
  theorem sortedByKey_imp_uniqueKeys (l : FactList) (h : SortedByKey l) : UniqueKeys l
  ```

- **Descripción**: Invariantes para `FactFSet`: las claves (primos) no se repiten y están ordenadas.

---

### §14. `sortedInsert` y variantes

- **Importancia**: `@importance: medium`

| Símbolo | Firma resumida | Descripción |
| --- | --- | --- |
| `sortedInsert` | `α → List α → List α` | Inserción ordenada en lista |
| `mem_sortedInsert_iff` | `x ∈ sortedInsert a l ↔ x = a ∨ x ∈ l` | Pertenencia tras inserción |
| `sorted_sortedInsert` | `Sorted r l → Sorted r (sortedInsert a l)` | Preserva `Sorted` |
| `sortedInsertFSet` | `α → FSet α → FSet α` | Inserción en `FSet` |
| `sortFSetList` | `List α → FSet α` | Construye `FSet` a partir de lista |
| `mem_sortedInsertFSet_iff` | Lema de pertenencia para `sortedInsertFSet` | |
| `sorted_sortedInsertFSet` / `sorted_sortFSetList` | Preservan `Sorted` | |
| `mem_sortFSetList_iff` | `x ∈ (sortFSetList l).elems ↔ x ∈ l` | |

---

### §15. Operaciones sobre `FactFSet`

- **Importancia**: `@importance: medium`

| Símbolo | Descripción |
| --- | --- |
| `sortedByKey_factListAddFactor` | Insertar un factor nuevo preserva `SortedByKey` |
| `uniqueKeys_factListAddFactor` | Insertar un factor nuevo preserva `UniqueKeys` |

---

### §16. Aliases de tipos de `FSet` para tuplas

- **Importancia**: `@importance: low`

| Símbolo | Descripción |
| --- | --- |
| `TupleFSet` | `FSet TupleList` |
| `NatsTupleFSet` | `FSet NatsTupleList` |
| `GTupleFSet` | `FSet GTupleList` |
| `HTupleFSet` | `FSet HTupleList` |
| `ℕ₀FSet.Fin₀Set` | `FSet (Fin₀ m)` — segmento finito `{0,...,m-1}` como `FSet` |
| `ℕ₀FSet.mem_Fin₀Set_iff` | `x ∈ Fin₀Set m ↔ lt₀ x m` |
| `ℕ₀FSet.Fin₀Set_card` | `card (Fin₀Set m) = Ψ m` |

---

### §17. `FSet.ofList` / Operaciones de conjunto

- **Importancia**: `@importance: high`

| Símbolo | Firma resumida | Descripción |
| --- | --- | --- |
| `FSet.ofList` | `List α → FSet α` | Construye `FSet` eliminando duplicados y ordenando |
| `FSet.mem_ofList_iff` | `x ∈ (FSet.ofList l).elems ↔ x ∈ l` | |
| `FSet.insert` | `α → FSet α → FSet α` | Inserción decidible en `FSet` |
| `mem_insert_iff` | `x ∈ (FSet.insert a s).elems ↔ x = a ∨ x ∈ s.elems` | |
| `FSet.union` | `FSet α → FSet α → FSet α` | Unión de conjuntos finitos |
| `mem_union_iff` | `x ∈ (s ∪ t).elems ↔ x ∈ s.elems ∨ x ∈ t.elems` | |
| `FSet.inter` | `FSet α → FSet α → FSet α` | Intersección |
| `mem_inter_iff` | `x ∈ (s ∩ t).elems ↔ x ∈ s.elems ∧ x ∈ t.elems` | |
| `FSet.image` | `(α → β) → FSet α → FSet β` | Imagen directa |
| `mem_image_iff` | `y ∈ (FSet.image f s).elems ↔ ∃ x ∈ s.elems, f x = y` | |
| `FSet.quotient` | `FSet α → EquivRelOn A → FSet (FSet α)` | Conjunto cociente |
| `mem_quotient_classes` | Lema de pertenencia a clases del cociente | |

---

### §18. Aliases de `FSet` de listas

| Símbolo | Descripción |
| --- | --- |
| `Nat0ListFSet` / `Nat1ListFSet` / `Nat2ListFSet` / `NatsListFSet` | `FSet` de distintos tipos de lista |
| `TupleListFSet` / `NatsTupleListFSet` / `GTupleListFSet` / `HTupleListFSet` | `FSet` de listas de tuplas |
| `PeanoValFSet` | `FSet PeanoVal` |
| `Nat0FSetFSet` | `FSet (ℕ₀FSet)` — conjunto de conjuntos |

---

### §19. Variantes de inserción (prima)

| Símbolo | Descripción |
| --- | --- |
| `sortedInsert'` / `sortList'` | Variantes alternativas de inserción/ordenación |
| `mem_sortedInsert'_iff` / `sorted_sortedInsert'` / `sorted_sortList'` / `mem_sortList'_iff` | Lemas correspondientes |

---

## Módulo: FSetFunction

**Archivo**: `Peano/PeanoNat/ListsAndSets/FSetFunction.lean`
**Namespace**: `Peano.FSetFunction`

---

### §20. `MapOn`

- **Tipo**: `structure`
- **Módulo**: `Peano/PeanoNat/ListsAndSets/FSetFunction.lean`
- **Namespace**: `Peano.FSetFunction`
- **Importancia**: `@importance: high`
- **Computable**: ✅
- **Firma Lean 4**:

  ```lean
  structure MapOn {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
      (A : FSet α) (B : FSet β) where
    toFun       : α → β
    map_carrier : ∀ a, a ∈ A.elems → toFun a ∈ B.elems
  ```

- **Notación matemática**: Una función $f : A \to B$ entre conjuntos finitos que lleva elementos de $A$ a elementos de $B$.

---

### §21. Composición e identidad de `MapOn`

| Símbolo | Firma resumida | Descripción |
| --- | --- | --- |
| `MapOn.comp` | `MapOn B C → MapOn A B → MapOn A C` | Composición |
| `MapOn.id` | `MapOn A A` | Identidad |
| `MapOn.comp_id` | `f.comp MapOn.id = f` | Cancelación por la derecha |
| `MapOn.id_comp` | `MapOn.id.comp f = f` | Cancelación por la izquierda |
| `MapOn.comp_assoc` | Asociatividad de composición | |

---

### §22. Propiedades de `MapOn`

- **Importancia**: `@importance: high`

| Símbolo | Descripción |
| --- | --- |
| `InjectiveOn` | `∀ a b ∈ A, f a = f b → a = b` |
| `SurjectiveOn` | `∀ b ∈ B, ∃ a ∈ A, f a = b` |
| `MapOn.Injective` | `InjectiveOn f.toFun A` |
| `MapOn.Surjective` | `SurjectiveOn f.toFun A B` |
| `MapOn.Bijective` | `f.Injective ∧ f.Surjective` |
| `MapOn.comp_injective` | Composición de inyecciones es inyección |
| `MapOn.comp_surjective` | Composición de sobreyecciones es sobreyección |
| `MapOn.comp_bijective` | Composición de biyecciones es biyección |
| `MapOn.id_injective` | `id` es inyectivo |
| `MapOn.id_surjective` | `id` es sobreyectivo |
| `MapOn.id_bijective` | `id` es biyectivo |
| `MapOn.injective_of_comp_injective` | Si `g∘f` es inyectiva, `f` es inyectiva |
| `MapOn.surjective_of_comp_surjective` | Si `g∘f` es sobreyectiva, `g` es sobreyectiva |

---

### §23. `MapOn.Im`

- **Tipo**: `def`
- **Módulo**: `Peano/PeanoNat/ListsAndSets/FSetFunction.lean`
- **Namespace**: `Peano.FSetFunction`
- **Importancia**: `@importance: medium`
- **Firma Lean 4**:

  ```lean
  def MapOn.Im {A : FSet α} {B : FSet β} (f : MapOn A B) : FSet β :=
    FSet.image f.toFun A
  ```

- **Descripción**: La imagen de $f$ como subconjunto finito de $B$.

---

### §24. Inversas de `MapOn`

- **Importancia**: `@importance: high`

| Símbolo | Descripción |
| --- | --- |
| `MapOn.rightInverse` | `g : MapOn B A` tal que `f ∘ g = id_B` |
| `MapOn.rightInverse_prop` | Verificación de la propiedad |
| `MapOn.rightInverse_injective` | La inversa por la derecha es inyectiva |
| `MapOn.leftInverse` | `g : MapOn B A` tal que `g ∘ f = id_A` |
| `MapOn.leftInverse_prop` | Verificación de la propiedad |
| `MapOn.leftInverse_surjective` | La inversa por la izquierda es sobreyectiva |
| `MapOn.injective_of_has_leftInverse` | Si tiene inversa izq., es inyectiva |
| `MapOn.injective_iff_has_leftInverse` | Equivalencia |
| `MapOn.surjective_of_has_rightInverse` | Si tiene inversa der., es sobreyectiva |
| `MapOn.surjective_iff_has_rightInverse` | Equivalencia |
| `MapOn.inverse` | La inversa canónica de una biyección |
| `MapOn.inverse_left_prop` / `MapOn.inverse_right_prop` | Propiedades de la inversa |
| `MapOn.inverse_injective` / `MapOn.inverse_surjective` / `MapOn.inverse_bijective` | La inversa de una biyección es biyectiva |
| `MapOn.inverse_inverse` | `(f⁻¹)⁻¹ = f` |
| `MapOn.comp_inverse_left` / `MapOn.comp_inverse_right` | `f⁻¹ ∘ f = id` y `f ∘ f⁻¹ = id` |

---

### §25. Cardinales e inyecciones / sobreyecciones

- **Importancia**: `@importance: high`

| Símbolo | Descripción |
| --- | --- |
| `card_image_of_injective` | `f` inyectiva → `card (Im f) = card A` |
| `injective_of_card_image` | `card (Im f) = card A` → `f` inyectiva |
| `card_image_of_surjective` | `f : A → B` sobreyectiva → `card (Im f) = card B` |
| `surjective_of_card_image` | `card (Im f) = card B` → `f` sobreyectiva |
| `card_le_of_injective` | `f` inyectiva → `card A ≤ card B` |
| `card_le_of_surjective` | `f` sobreyectiva → `card B ≤ card A` |
| `not_injective_of_card_lt` | `card A > card B` → no hay inyección `A → B` |
| `collision_of_card_lt` | **Principio del palomar**: `card A > card B → ∃ a₁ ≠ a₂, f a₁ = f a₂` |
| `card_eq_of_injections` | Existen inyecciones mutuas → `card A = card B` |
| `card_eq_of_surjections` | Existen sobreyecciones mutuas → `card A = card B` |
| `MapOn.Bijective.card_eq` | `f` biyectiva → `card A = card B` |

---

### §26. Equivalencias inyec./sobre./biject. cuando `card A = card B`

- **Importancia**: `@importance: high`

| Símbolo | Descripción |
| --- | --- |
| `MapOn.injective_iff_surjective_of_card_eq` | Inyectiva ↔ Sobreyectiva (cuando `card A = card B`) |
| `MapOn.injective_iff_bijective_of_card_eq` | Inyectiva ↔ Biyectiva |
| `MapOn.surjective_iff_bijective_of_card_eq` | Sobreyectiva ↔ Biyectiva |
| `MapOn.leftInverse_eq_inverse_of_card_eq` | La inversa izquierda = inversa canónica |
| `MapOn.leftInverse_right_prop_of_card_eq` | La inversa izq. es también inversa der. |
| `MapOn.rightInverse_eq_inverse_of_card_eq` | La inversa derecha = inversa canónica |
| `MapOn.rightInverse_left_prop_of_card_eq` | La inversa der. es también inversa izq. |

---

### §27. Endomorfismos (`MapOn A A`)

- **Importancia**: `@importance: medium`

| Símbolo | Descripción |
| --- | --- |
| `MapOn.endo_injective_iff_surjective` | En endomorfismos: inyectiva ↔ sobreyectiva |
| `MapOn.endo_injective_iff_bijective` | Inyectiva ↔ biyectiva |
| `MapOn.endo_surjective_iff_bijective` | Sobreyectiva ↔ biyectiva |
| `MapOn.endo_bijective_of_injective` | Inyectiva → biyectiva |
| `MapOn.endo_bijective_of_surjective` | Sobreyectiva → biyectiva |
| `MapOn.endo_leftInverse_eq_inverse` | En endomorfismos: inversa izq. = inversa canónica |
| `MapOn.endo_leftInverse_right_prop` | La inversa izq. también es inversa der. |
| `MapOn.endo_rightInverse_eq_inverse` | En endomorfismos: inversa der. = inversa canónica |
| `MapOn.endo_rightInverse_left_prop` | La inversa der. también es inversa izq. |

---

### §28. `Perm`

- **Tipo**: `def`
- **Módulo**: `Peano/PeanoNat/ListsAndSets/FSetFunction.lean`
- **Namespace**: `Peano.FSetFunction`
- **Importancia**: `@importance: high`
- **Firma Lean 4**:

  ```lean
  def Perm (A : FSet α) : Type := { f : MapOn A A // f.Bijective }
  ```

- **Notación matemática**: El grupo simétrico $\mathrm{Sym}(A)$ — las permutaciones biyectivas de $A$.

| Símbolo | Descripción |
| --- | --- |
| `Perm.injective` | Toda permutación es inyectiva |
| `Perm.surjective` | Toda permutación es sobreyectiva |
| `Perm.id` | Permutación identidad |
| `Perm.comp` | Composición de permutaciones |
| `Perm.comp_id_fn` / `Perm.id_comp_fn` | Cancelación por identidad |
| `Perm.inv` | Inversa de una permutación |
| `Perm.inv_left` / `Perm.inv_right` | `f⁻¹ ∘ f = id` y `f ∘ f⁻¹ = id` |
| `Perm.inv_inv` | `(f⁻¹)⁻¹ = f` |
| `Perm.comp_inv_left` / `Perm.comp_inv_right` | Propiedades de composición con inversa |
| `Perm.comp_assoc` | Asociatividad |

---

### §29. `MapOn.PreIm` / fibras / restricciones

- **Importancia**: `@importance: medium`

| Símbolo | Descripción |
| --- | --- |
| `MapOn.PreIm` | Preimagen de un elemento: `{a ∈ A \| f a = b}` |
| `MapOn.mem_PreIm_iff` | `x ∈ PreIm f b ↔ x ∈ A ∧ f x = b` |
| `MapOn.PreIm_full` | `⊔ (PreIm f b) = A` (unión de preimágenes = dominio) |
| `MapOn.card_PreIm_le` | `card (PreIm f b) ≤ card A` |
| `MapOn.fiber` | Fibra de `f` sobre `b`: `{a ∈ A \| f a = b}` |
| `MapOn.mem_fiber_iff` | Lema de pertenencia a fibra |
| `MapOn.card_fiber_le_one_of_injective` | Si `f` inyectiva, `card (fiber f b) ≤ 1` |
| `MapOn.restrict` | Restricción de `f : MapOn A B` a subconjunto de `A` |
| `MapOn.restrict_injective` | La restricción de una inyección es inyección |
| `MapOn.mem_Im_restrict` | Pertenencia a la imagen de la restricción |
| `card_eq_mul_of_uniform_fibers` | Si todas las fibras tienen cardinalidad `k`: `card A = k · card B` |

---

### §30. `BinOpOn`

- **Tipo**: `def`
- **Módulo**: `Peano/PeanoNat/ListsAndSets/FSetFunction.lean`
- **Namespace**: `Peano.FSetFunction`
- **Importancia**: `@importance: medium`
- **Firma Lean 4**:

  ```lean
  def BinOpOn (A : FSet α) : Type :=
    { f : α → α → α // ∀ a b, a ∈ A.elems → b ∈ A.elems → f a b ∈ A.elems }
  ```

- **Descripción**: Una operación binaria cerrada sobre el conjunto finito `A` — base para la teoría de grupos finitos.

---

### §31. `FunTable` / `FunPerm`

- **Importancia**: `@importance: medium`

| Símbolo | Descripción |
| --- | --- |
| `FunTable` | Representación tabular de un endomorfismo `A → A` (lista de pares) |
| `FunTable.apply` | Evaluar un `FunTable` en un elemento |
| `FunTable.applyElem` | Versión con prueba de pertenencia |
| `FunTable.applyElem_mem` | `applyElem f a ∈ A` |
| `FunTable.id` | Tabla identidad |
| `FunTable.comp` | Composición de tablas |
| `FunPerm` | Permutación representada como `FunTable` biyectiva |
| `FunPerm.id` | Permutación identidad como `FunPerm` |
| `FunPerm.applyElem_injective` | La evaluación de `FunPerm` es inyectiva |

---

### §32. Lemas de lista (nodup, sort)

- **Importancia**: `@importance: low`

| Símbolo | Descripción |
| --- | --- |
| `sorted_nodup` | Lista `Sorted` implica sin duplicados (`Nodup`) |
| `nodup_map_of_inj_on` | Función inyectiva sobre lista sin dup → imagen sin dup |
| `perm_of_nodup_subset_same_length` | Dos listas sin dup, misma longitud, una ⊆ otra → son permutación |
| `perm_map_of_injective_on_nodup` | Mapa inyectivo sobre lista sin dup produce permutación |

---

## Módulo: EquivRel

**Archivo**: `Peano/PeanoNat/ListsAndSets/EquivRel.lean`
**Namespace**: `Peano.EquivRel`

---

### §33. `EquivRelOn`

- **Tipo**: `structure`
- **Módulo**: `Peano/PeanoNat/ListsAndSets/EquivRel.lean`
- **Namespace**: `Peano.EquivRel`
- **Importancia**: `@importance: high`
- **Computable**: ✅ (con `decRel`)
- **Firma Lean 4**:

  ```lean
  structure EquivRelOn {α : Type} [DecidableEq α] [LT α]
      (A : FSet α) where
    rel      : α → α → Prop
    decRel   : DecidableRel rel
    refl_on  : ∀ a, a ∈ A.elems → rel a a
    symm_on  : ∀ a b, a ∈ A.elems → b ∈ A.elems → rel a b → rel b a
    trans_on : ∀ a b c,
      a ∈ A.elems → b ∈ A.elems → c ∈ A.elems →
      rel a b → rel b c → rel a c
  ```

- **Notación matemática**: Una relación de equivalencia $\sim$ restringida al dominio finito $A$. Las leyes se exigen solo para elementos de $A$.

---

### §34. `EquivRelOn.classOf`

- **Tipo**: `def`
- **Módulo**: `Peano/PeanoNat/ListsAndSets/EquivRel.lean`
- **Namespace**: `Peano.EquivRel`
- **Importancia**: `@importance: high`
- **Computable**: ✅
- **Firma Lean 4**:

  ```lean
  def EquivRelOn.classOf {A : FSet α} (R : EquivRelOn A) (a : α) : FSet α :=
    A.filter (fun x => decide (R.rel a x))
  ```

- **Notación matemática**: La clase de equivalencia $[a]_R = \{x \in A \mid a \sim x\}$.

---

### §35. Lemas base sobre `classOf`

- **Importancia**: `@importance: high`

| Símbolo | Descripción |
| --- | --- |
| `EquivRelOn.mem_classOf_iff` | `x ∈ classOf R a ↔ x ∈ A ∧ R.rel a x` |
| `EquivRelOn.classOf_nonempty_of_mem` | `a ∈ A → a ∈ classOf R a` |
| `EquivRelOn.classOf_subset_domain` | `x ∈ classOf R a → x ∈ A` |
| `EquivRelOn.rel_of_mem_classOf` | `x ∈ classOf R a → R.rel a x` |
| `EquivRelOn.mem_classOf_of_rel` | `x ∈ A ∧ R.rel a x → x ∈ classOf R a` |
| `EquivRelOn.classOf_eq_of_mem_classOf` | `x ∈ classOf R a → classOf R x = classOf R a` |
| `EquivRelOn.mem_classOf_iff_of_rel` | `R.rel a b → (x ∈ classOf R a ↔ x ∈ classOf R b)` |
| `EquivRelOn.classOf_eq_or_disjoint` | Dos clases son iguales o disjuntas |

---

### §36. `EquivRelOn.ClassFamily` / `classes`

- **Importancia**: `@importance: high`

| Símbolo | Descripción |
| --- | --- |
| `EquivRelOn.ClassFamily` | El tipo de la familia de clases de equivalencia de `R` |
| `EquivRelOn.canonicalClassFamily` | Representante canónico de la familia de clases |
| `EquivRelOn.classes` | Conjunto de todas las clases: `FSet (FSet α)` |
| `EquivRelOn.mem_classes_iff` | `C ∈ classes R ↔ ∃ a ∈ A, C = classOf R a` |
| `EquivRelOn.classOf_mem_classes_of_mem` | `a ∈ A → classOf R a ∈ classes R` |
| `EquivRelOn.mem_classes_elim` | Toda clase tiene un representante |
| `EquivRelOn.classes_cover` | Las clases cubren `A`: `⊔ classes R = A` |

---

## Resumen de símbolos principales (todos los módulos)

| Símbolo | Módulo | Tipo | Importance |
| --- | --- | --- | --- |
| `Sorted` | List | `def` | high |
| `lengthₚ` | List | `def` | medium |
| `PeanoVal` | List | `inductive` | medium |
| `getDₚ` / `List.indexOfₚ` | List | `def` | medium |
| `FSet` | FSet | `structure` | high |
| `FSet.ext` / `eq_of_mem_iff` | FSet | `theorem` | high |
| `FSet.ofList` / `.insert` / `.union` / `.inter` / `.image` | FSet | `def` | high |
| `FSet.quotient` | FSet | `def` | medium |
| `MapOn` | FSetFunction | `structure` | high |
| `MapOn.Injective` / `.Surjective` / `.Bijective` | FSetFunction | `def` | high |
| `MapOn.Im` | FSetFunction | `def` | medium |
| `MapOn.inverse` | FSetFunction | `def` | high |
| `Perm` | FSetFunction | `def` | high |
| `BinOpOn` | FSetFunction | `def` | medium |
| `card_eq_mul_of_uniform_fibers` | FSetFunction | `theorem` | medium |
| `collision_of_card_lt` | FSetFunction | `theorem` | high |
| `EquivRelOn` | EquivRel | `structure` | high |
| `EquivRelOn.classOf` | EquivRel | `def` | high |
| `EquivRelOn.classes` | EquivRel | `def` | high |
| `EquivRelOn.classes_cover` | EquivRel | `theorem` | high |
