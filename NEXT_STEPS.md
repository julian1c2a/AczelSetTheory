# Next Steps

**Last updated:** 2026-05-17

The project compiles on Lean 4.29.0 with **0 sorry, 85 modules**.
Full Zermelo axioms derived. Architecture: CList/ + Operations/ + Axioms/ + PList/ + VN/.
See PLANNING.md for the full long-term roadmap.

---

## ✅ COMPLETED (2026-05-17) — B1: Axioms/Rank + VN/RankVN: rango de Von Neumann

- **Axioms/Rank.lean**: `rank : HFSet → ℕ₀` (rango de Von Neumann), `rank_empty : rank ∅ = 𝟘`, `rank_insert (x A h) : rank (insert x A) = max (σ (rank x)) (rank A)`. Implementado con recursión mutual estructural sobre `CList` normalizado.
- **VN/RankVN.lean**: `rank_vN (n : ℕ₀) : HFSet.rank (vN n) = n` — el embedding vN preserva el rango. Prueba por inducción Peano usando `rank_insert`, `not_mem_self`, `max_comm`, `max_eq_of_lt`, `lt_succ_self`.

---

## ✅ COMPLETED (2026-05-17) — A1/A2/A3/C1: VN/PowVN, SubVN, DivVN, FactorialVN

- **VN/PowVN.lean**: `powVN (m n : ℕ₀) : HFSet := vN (m ^ n)` — transporte de la potenciación Peano. 14 teoremas: `powVN_def`, `powVN_zero`, `powVN_succ`, `vN_pow`, `vN_pow_zero`, `vN_pow_one`, `vN_one_pow`, `vN_zero_pow`, `vN_pow_add`, `vN_mul_pow`, `vN_pow_pow`, `vN_pow_two`, `vN_pow_ne_zero`.
- **VN/SubVN.lean**: sustracción acotada (monus) transportada vía `congrArg vN`. 12 teoremas: `vN_sub_zero`, `vN_zero_sub`, `vN_sub_self`, `vN_succ_sub_one`, `vN_sub_succ_succ`, `vN_add_k_sub_k`, `vN_sub_k_add_k`, `vN_add_sub_assoc`, `sub_le_vN_self`, `sub_pos_of_lt_vN`, `vN_succ_sub`, `vN_sub_succ_left`.
- **VN/DivVN.lean**: división euclidiana transportada. 6 teoremas: `vN_divMod_spec`, `div_le_vN_self`, `div_lt_vN_self`, `mod_lt_vN`, `mod_of_lt_vN`, `div_of_lt_vN`.
- **VN/FactorialVN.lean**: `factVN (n : ℕ₀) : HFSet := vN (factorial n)` — transporte del factorial de Peano. 10 teoremas: `factVN_def`, `vN_factorial_zero`, `vN_factorial_one`, `vN_factorial_two`, `vN_factorial_succ`, `vN_factorial_pos`, `vN_factorial_ge_one`, `vN_factorial_ne_zero`, `vN_factorial_mono`, `vN_factorial_le_succ`.

---

## ✅ COMPLETED (2026-05-17) — Axioms/NPow: membresía de la potencia cartesiana n-aria

- **Axioms/NPow.lean**: `mem_nPow_zero (t A) : t ∈ nPow A 𝟘 ↔ t = empty`, `mem_nPow_succ (t A n) : t ∈ nPow A (σ n) ↔ ∃ s ∈ nPow A n, ∃ a ∈ A, t = ⟪s, a⟫`.
- Agrega la caracterización de membresía axiomática (vs las ecuaciones de reducción en `Operations/NPow.lean`).

---

## ✅ COMPLETED (2026-05-16) — Axioms/Fintype: tipos finitos scratch-built (F1+F2)

- **Axioms/Fintype.lean**: `Finset α` (estructura `{val : List α, nodup}`), `Fintype α` (clase `{elems, complete}`), `HFSet.toList`, `HFSet.toFinset` (convierte HFSet en Finset HFSet), `HFSet.membership_fintype` (instancia `Fintype {x // x ∈ A}`).
- Sin dependencia de Mathlib. Teoremas: `mem_toList`, `nodup_toList`, `mem_toFinset`.

---

## ✅ COMPLETED (2026-05-16) — Phase 7e: OrdinalNat + NPow

- **Axioms/OrdinalNat.lean**: `card_le_of_subset : A ⊆ B → card A ≤ card B`, `isOrdinal_isNat : isOrdinal A → isNat A`, `isOrdinal_iff_isNat : isOrdinal A ↔ isNat A` (en V_ω los ordinales son exactamente los naturales de von Neumann).
- **Operations/NPow.lean**: `nPow : HFSet → ℕ₀ → HFSet`, `nPow_zero : nPow A 𝟭 = singleton empty`, `nPow_succ : nPow A (σ n) = nPow A n ×ₕ A`.

---

## ✅ COMPLETED (2026-05-16) — Ordinal predicate + Cardinal-VN bridge

- **Axioms/Ordinal.lean**: `isOrdinal` (transitivity + ∈-trichotomy), theorems: `isOrdinal_empty`, `isOrdinal_succ`, `isNat_isOrdinal`, `isOrdinal_mem`
- **Axioms/Cardinal.lean** (+1): `card_eq_zero_iff` (↔ empty)
- **VN/CardVN.lean**: `card_vN (n : ℕ₀) : HFSet.card (vN n) = n` (VN embedding preserves cardinality)

---

## ✅ COMPLETED (2026-05-15) — Fase 4 + Fase 5: FSet embedding + Peano Axioms/Arith

- **VN/FSet.lean**: `fsetToHFSet : ℕ₀FSet → HFSet`, `mem_fsetToHFSet`, `vN_mem_fsetToHFSet_iff`, `fsetToHFSet_injective`
- **VN/PeanoAxioms.lean**: PA1/PA2/PA3 as pure HFSet theorems + vN bridge (`vN_zero_ne_succ`, `vN_succ_injective_vN`, `vN_induction`)
- **VN/PeanoArith.lean**: `addVN` (set-theoretic iteration of succ), `vN_add` transport theorem, all arithmetic laws via `congrArg vN`
- **VN.lean**: barrel updated (7 modules total)

---

## ✅ COMPLETED (2026-05-15) — Fase 2: Refactorización de CList

- **CList/Basic.lean**: `mk : PList CList → CList` (antes `List`), `cSize : CList → ℕ₀` (antes `Nat`)
- Todos los submódulos (ExtEq, Order, SetEquiv, Sort, Normalize, Filter): sin `Init.Data.List.Basic`, sin uso de `List.*`
- `Nat` residual en `termination_by`/`decreasing_by` es inevitable: `sizeOf` de Lean 4 siempre retorna `Nat`

---

## ✅ COMPLETED (2026-05-14) — Function composition, identity, product, image

- **Operations/FunctionComp.lean**: `funComp`, notation `∘f` (infixl:90)
- **Operations/Identity.lean**: `idFunc`
- **Operations/Product.lean**: `prodHF`, notation `×ₛ` (infixl:80)
- **Axioms/FunctionComp.lean**: 10 theorems (composition preserves functions, injectivity, surjectivity, bijectivity)
- **Axioms/Identity.lean**: 15 theorems (identity laws, `funComp_idFunc_eq`, `idFunc_funComp_eq`, `relInv_idFunc`)
- **Axioms/Product.lean**: 8 theorems (membership, projections, empty product)
- **Axioms/Image.lean**: 7 theorems (`imageRel_funComp`, `imageRel_idFunc`, monotonicity, union)

---

## CURRENT PRIORITY — Fase 1: Peano Integration Foundation

> Objetivo: incorporar Peano como dependencia y construir la infraestructura
> propia (PList + omega₀) que soporta el resto del plan.

---

### ✅ 1.1 Lakefile — añadir Peano

Completado. `lakefile.lean` actualizado con `require peanolib from git`.

---

### ✅ 1.2 PList — lista propia con ℕ₀

Completado. Archivos creados:

- `AczelSetTheory/PList/Basic.lean` — tipo `PList (α : Type)`, `length : PList α → ℕ₀`,
  `map`, `filter`, `foldl`, `foldr`, `append`, `flatMap`, `reverse`, `zipWith`,
  `mem [DecidableEq]` (Bool), `Mem` (Prop), `Membership` instance, `toList`/`ofList`
- `AczelSetTheory/PList/Lemmas.lean` — lemas `@[simp]` + `length_append` (usa `add`
  no `+` por la ambigüedad de elaboración), `length_toList`, `length_filter_le`
- `AczelSetTheory/PList.lean` — barrel

**Nota técnica:** `export Peano.Add(add, ...)` en `Peano.PeanoNat.Add` coloca la
función `add` directamente en el namespace `Peano`. Con `open Peano`, el operador `+`
y la función `add` son dos caminos de elaboración distintos para el mismo valor, lo que
causa ambigüedad. Solución: usar `add n m` en lugar de `n + m` en los enunciados de
lemas que involucren longitudes.

---

### ✅ 1.3 omega₀ — táctica puente

Completado. `AczelSetTheory/PList/Omega0.lean` creado.

**Implementación real (vía Ψ : ℕ₀ → ℕ, no Λ):**

La API de Peano usa `Ψ : ℕ₀ → ℕ` para transportar a `Nat`, no `Λ`.
Los lemas puente viven en `namespace PList.Omega0` (sin `@[simp]` global):

```lean
PList.Omega0.ψ_eq_iff  : n = m   ↔ Ψ n = Ψ m       -- Peano.Axioms.Ψ_inj
PList.Omega0.ψ_le_iff  : n ≤ m   ↔ Ψ n ≤ Ψ m       -- isomorph_Ψ_le.symm
PList.Omega0.ψ_lt_iff  : n < m   ↔ Ψ n < Ψ m       -- StrictOrder.isomorph_Ψ_lt
PList.Omega0.ψ_zero    : Ψ 𝟘 = 0                    -- isomorph_0_Ψ
PList.Omega0.ψ_succ    : Ψ (σ n) = Nat.succ (Ψ n)  -- isomorph_σ_Ψ
PList.Omega0.ψ_add     : Ψ (add n m) = Ψ n + Ψ m   -- isomorph_Ψ_add
```

**Nota técnica:** `ψ_add` usa `@HAdd.hAdd Nat Nat Nat instHAdd` en lugar de
`+` para evitar la ambigüedad del `Coe Nat ℕ₀` y garantizar que `omega`
reconozca la suma (omega no reconoce `Nat.add`).

15 tests verificados en `section omega₀_tests`.

---

### 1.4 Actualizar AczelSetTheory.lean (barrel raíz)

```lean
import AczelSetTheory.PList
-- (los imports existentes permanecen intactos)
```

---

## ✅ COMPLETED — Fase 3 + Fase 4 + Fase 5: vN embedding + FSet + Peano

- **VN/Basic.lean**: `vN : ℕ₀ → HFSet`, `vN_zero`, `vN_succ`
- **VN/Injective.lean**: `vN_injective`
- **VN/IsNat.lean**: `isNat_iff_range`
- **VN/Arithmetic.lean**: `mem_vN_iff_lt`, `vN_mono`, `vN_le_iff_subset`
- **VN/FSet.lean**: `fsetToHFSet`, `mem_fsetToHFSet`, `fsetToHFSet_injective` ✅
- **VN/PeanoAxioms.lean**: PA1/PA2/PA3 pure HFSet + vN bridge ✅
- **VN/PeanoArith.lean**: `addVN`, `vN_add`, full arithmetic transport ✅
- **VN.lean**: barrel (7 modules)

Además: HFList.lean, PList/Fin0.lean, Axioms/VonNeumann.lean, Axioms/Succ.lean, Axioms/Singleton.lean, Axioms/Subset.lean, Axioms/Foundation.lean, Axioms/Relation.lean, Axioms/Function.lean, Axioms/Inverse.lean, Axioms/Composition.lean, Axioms/Bijection.lean, Axioms/Restriction.lean, Axioms/Decidable.lean, Axioms/BooleanAlgebra.lean, Axioms/BooleanRing.lean, Axioms/Cardinal.lean, Axioms/Lattice.lean, Axioms/SymDiff.lean, Axioms/OrderedPair.lean.

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
