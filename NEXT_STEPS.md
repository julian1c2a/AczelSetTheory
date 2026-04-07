# Next Steps

**Last updated:** 2026-04-10

The project compiles on Lean 4.29.0 with **0 sorry**.
All 8 Zermelo axioms (Extensionality, Empty Set, Pairs, Union, Separation, Intersection, Setminus, Powerset)
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
- ✅ **Powerset: B ∈ 𝒫(A) ↔ ∀ x, x ∈ B → x ∈ A  (`HFSet.mem_powerset`)**
- ✅ Architecture split: `Operations/` (CList-level) + `Axioms/` (HFSet-level)
- ✅ Notation system: emptyset, {[a,b]}, {[a]}, {[x in A <|> P]}, von Neumann numerals 0-9

---

## Phase 6: Foundation (Regularity) and Singleton/Ordered Pairs

### 6a. Foundation (Regularity) axiom

**Statement**:

```
forall A != emptyset, exists x in A, x cap A = emptyset
```

**Proof strategy**: Well-founded induction on `cSize`. For any non-empty A, pick the element `x in A` with minimal `cSize`. Then for any `y in x cap A`, we'd have `cSize y < cSize x` (by `cSize_lt_of_mem`), contradicting minimality.

**Implementation plan**:

1. Define `minCSize (A : CList) : CList` — element with smallest cSize in a non-empty CList
2. Prove `minCSize_mem : A != empty -> mem (minCSize A) A = true`
3. Prove `minCSize_is_min : mem y A = true -> cSize (minCSize A) <= cSize y`
4. Prove `foundation : A != empty -> exists x in A, inter x A = empty`
5. Store in `Axioms/Foundation.lean`

**Dependencies**: `Operations/Intersection.lean`, `Axioms/Intersection.lean`, `HFSets.lean`

### 6b. Singleton properties

**Statement**: `mem_singleton : x in {a} <-> x = a`

**Implementation**: Follows from `mem_pair` since `singleton a = pair a a`.

**File**: Extend `Notation.lean` or create `Axioms/Singleton.lean`.

### 6c. Ordered pairs (Kuratowski)

**Definition**: `orderedPair a b = {{a}, {a, b}}`

**Key theorems**:

1. `orderedPair_eq_iff : orderedPair a b = orderedPair c d <-> a = c and b = d`
2. `fst (orderedPair a b) = a`
3. `snd (orderedPair a b) = b`

**Proof of injectivity**: Use `extensionality` + `mem_pair` + `mem_singleton` to case-split on membership.

**Implementation plan**:

1. Create `Operations/OrderedPair.lean`: define `orderedPair`, `fst`, `snd` at CList level, lift to HFSet
2. Create `Axioms/OrderedPair.lean`: prove `orderedPair_eq_iff`, `fst_orderedPair`, `snd_orderedPair`

**Dependencies**: `Axioms/Pair.lean`, `Notation.lean` (for singleton)

---

## Phase 7: Von Neumann Natural Numbers

### 7a. Successor function

**Definition**: `succ A = A cup {A}` (using `union` and `singleton`)

**Key theorems**:

1. `mem_succ : x in succ A <-> x in A or x = A`
2. `succ_injective : succ A = succ B -> A = B`
3. `succ_ne_empty : succ A != emptyset`
4. `not_mem_self : not (A in A)` (follows from Foundation)

**Files**: `Operations/Succ.lean`, `Axioms/Succ.lean`

### 7b. Natural number predicate

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

### 7c. Arithmetic operations

**Definitions** (recursive over `isNat`):

1. `add (m n : HFSet) : HFSet` — m + 0 = m, m + succ(n) = succ(m + n)
2. `mul (m n : HFSet) : HFSet` — m *0 = 0, m* succ(n) = m * n + m

**Key theorems**:

- `add_zero`, `add_succ`, `add_comm`, `add_assoc`
- `mul_zero`, `mul_succ`, `mul_comm`, `mul_assoc`, `mul_dist`

**Challenge**: These definitions require well-founded recursion or a recursion principle for `isNat`. Since membership is well-founded in HFSets, we can use `cSize` as termination measure.

**Files**: `Operations/Nat.lean`, `Axioms/Nat.lean`

---

## Phase 8: Cartesian Product and Relations

### 8a. Cartesian product

**Definition**: `prod A B = {[p in P(P(A cup B)) <|> exists a in A, exists b in B, p = orderedPair a b]}`

Or more practically via CList-level construction iterating over elements.

**Key theorem**: `mem_prod : p in prod A B <-> exists a b, a in A and b in B and p = orderedPair a b`

### 8b. Relations and functions

**Definitions**:

- `isRelation R A B` — R subseteq prod A B
- `isFunction f A B` — isRelation f A B and forall a in A, exists! b, orderedPair a b in f
- `domain f`, `range f`
- `apply f a` — the unique b such that orderedPair a b in f

**Files**: `Operations/CartesianProduct.lean`, `Operations/Relation.lean`, `Operations/Function.lean`

---

## Phase 9: Advanced axioms

### 9a. Replacement axiom

**Statement**: If F is a function-class and A is a set, then {F(x) | x in A} is a set.

In our finite setting, this is provable by induction on the size of A, using `sep` and `union`.

### 9b. Axiom of Choice

In hereditarily finite sets, Choice is derivable from the well-ordering of CList (already established via `lt_total`). For any family of non-empty finite sets, we can computably select an element from each.

**Proof strategy**: Use `lt`-minimal element selection (already implicit in the CList ordering).

---

## Future directions

- Decidability proofs for all HFSet predicates
- Computable functions HFSet -> HFSet (eval framework)
- Connection to Peano arithmetic via the von Neumann encoding
- Formal verification of set-theoretic constructions (ordinals, cardinals)
