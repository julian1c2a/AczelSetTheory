# AczelSetTheory

## Aczel's Set Theory in Lean 4

**Author**: Julián Calderón Almendros
**License**: MIT
**Lean version**: v4.30.0
**Build status**: ✅ 0 `sorry` — 0 `noncomputable` — 0 errors, 0 warnings — 182 `.lean` files (~28 800 LOC), build 241 jobs
**Roadmap**: FASE A (paridad Peano) ✅ completa · FASE B (consolidación) 8/9 milestones cerrados (solo resta M8B: cierre documental)

---

### What it is

This repository formalizes Aczel's constructive set theory in Lean 4. The central object is `CList` — a computable representation of hereditarily finite sets as nested lists — together with a provably correct normalization procedure that yields canonical representatives. The quotient type `HFSet` identifies extensionally equal `CList`s.

The Zermelo axioms (Extensionality, Empty Set, Pairs, Union, Separation, Intersection, Setminus, Powerset) are **derived as theorems**, not postulated.

Key properties of this set theory:

- **Computable**: every *definition* is decidable and executable — **0 `noncomputable def`** across the whole library, including the hereditarily-finite choice function `HFSet.choose` (a plain `def`)
- **No axiom of infinity**: natural numbers are constructed from sets (`vN : ℕ₀ → HFSet`)
- **Well-founded recursion and induction** over sets (`∈` is well-founded)
- **Axiom-free foundations**: the Zermelo axioms are derived theorems, not postulates
- **Standard axiom footprint**: theorems reduce to `{propext, Classical.choice, Quot.sound}` — the same set as ordinary Lean/Mathlib developments. `Classical.choice` is used only for *propositional* reasoning (excluded middle via `byContradiction`/`em`) and enters structurally at the `CList.extEq` foundation (well-founded recursion); it is never used to make non-computable selections. Verifiable per theorem with `#print axioms`

### Derived Zermelo Axioms

| Axiom | Theorem | Statement | Status |
|-------|---------|-----------|--------|
| Extensionality | `HFSet.extensionality` | ∀ A B, (∀ x, x ∈ A ↔ x ∈ B) → A = B | ✅ |
| Empty Set | `HFSet.not_mem_empty` | ∀ x, x ∉ ∅ | ✅ |
| Pairs | `HFSet.mem_pair` | x ∈ {a, b} ↔ x = a ∨ x = b | ✅ |
| Union | `HFSet.mem_sUnion` | x ∈ ⋃ A ↔ ∃ B ∈ A, x ∈ B | ✅ |
| Separation | `HFSet.mem_sep` | x ∈ sep A P ↔ x ∈ A ∧ P x | ✅ |
| Intersection | `HFSet.mem_inter` | x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B | ✅ |
| Setminus | `HFSet.mem_setminus` | x ∈ A \ B ↔ x ∈ A ∧ x ∉ B | ✅ |
| Powerset | `HFSet.mem_powerset` | B ∈ 𝒫 A ↔ ∀ x, x ∈ B → x ∈ A | ✅ |

### Module structure

```
AczelSetTheory/
  CList/             — Computable hereditarily-finite lists (7 sub-modules)
    Basic.lean       — CList type, cSize : ℕ₀, dedup, insertionSort, normalize
    ExtEq.lean       — Extensional equality (reflexivity, transitivity, commutativity)
    SetEquiv.lean    — Nodup, SetEquiv, dedup properties
    Order.lean       — lt: irreflexivity, antisymmetry, totality, transitivity
    Sort.lean        — Sorted, insertionSort preserves sorted/nodup/setEquiv
    Normalize.lean   — Idempotency, uniqueness (sorted_nodup_setEquiv_eq)
    Filter.lean      — filter preserves extEq (P_respects, extEq_filter)
  PList/             — Polymorphic list over ℕ₀, Peano bridge (4 sub-modules)
    Basic.lean       — PList α, length : ℕ₀, map, filter, flatMap, mem
    Lemmas.lean      — @[simp] lemmas, length_append, mem_append, mem_filter
    Omega0.lean      — ψ_* bridge lemmas enabling omega₀ tactic
    Fin0.lean        — Fin₀ n type, decidable equality, PList.get
  HFSets.lean        — HFSet quotient type, membership, extensionality, empty, pairs
  HFList.lean        — Ordered sequences of HFSets (PList HFSet)
  Notation.lean      — ∅, {[a,b]}, {[a]}, {[x ∈ A <|> P]}, ⟪a,b⟫, numerals 0–9
  Operations/        — CList-level constructors lifted to HFSet (21 sub-modules)
    Union, Intersection, Setminus, Separation, Pair, Powerset, SymDiff,
    OrderedPair, Relation, Function, Inverse, Restriction, Composition,
    Replacement, Cardinal, FunctionComp, Identity, Product, CartProd, NPow, Order
  Axioms/            — HFSet-level axioms and theorems (41 sub-modules)
    Union, Intersection, Setminus, Separation, Pair, Powerset, Singleton,
    SymDiff, OrderedPair, Foundation, Decidable, Subset, Lattice,
    BooleanAlgebra, BooleanRing, Succ, VonNeumann, Choice, Cardinal,
    Relation, Function, Bijection, Inverse, Composition, Restriction,
    Replacement, FunctionComp, Identity, Product, Image, Adjunction,
    Induction, CartProd, Ordinal, OrdinalNat, Fintype, NPow, Rank,
    Order, WellOrder, LinearOrder
  VN/                — Von Neumann embedding vN : ℕ₀ → HFSet (49 sub-modules)
    Basic, Injective, IsNat, Arithmetic, FSet, PeanoAxioms, PeanoArith,
    PowVN, SubVN, DivVN, FactorialVN, CardVN, RankVN, GcdVN, FibVN, BinomVN,
    SummationVN, SqrtVN, LogVN, DigitsVN, ModEqVN, TotientVN, PrimesVN,
    CantorPairingVN, PairingVN, NewtonBinomVN, ProductVN, GodelBetaVN,
    HFGroupVN, ProdBridgeVN, MapBridgeVN, ListBridgeVN,
    PrimeVN, FermatVN, CRTVN, InitialityVN, LatticeVN, ActionVN, OrbitVN,
    PermVN, SignVN, SymGroupVN, CountingVN, NormalSubgroupVN, QuotientGroupVN,
    FirstIsomorphismVN, SecondIsomorphismVN, ThirdIsomorphismVN,
    CorrespondenceTheoremVN
  Algebra/           — Native algebraic structures in HFSet (23 sub-modules)
    Group, Subgroup, GroupHom, NormalSubgroup, Ring, CosetCount, Monoid, RingHom,
    Field, Module, LinearSpace, Lattice, Action, CosetAction, QuotientGroup,
    FirstIsomorphism, SecondIsomorphism, ThirdIsomorphism, CorrespondenceTheorem,
    Sylow, Zassenhaus, QuotientRing, HFMatrix
  Integers/          — Integer type ℤ₀ + ℚ₀ (9 sub-modules + Rationals/)
    Basic, Order, Functions, Arithmetic, Bijection, PadicVal, MobiusLiouville,
    Canonical, Bezout, ZModN, Rationals/{AbsVal, Density, IsCauchy}
  Combinatorics/     — Native finite combinatorics in HFSet (1 sub-module)
    Counting  — pigeonhole, inclusion–exclusion (2 and 3 sets), card lemmas
  Topology/          — Topological spaces over HFSet (5 sub-modules)
    Basic, Interior, Subspace, Neighborhoods, Separation
```

### What it covers

Beyond the Zermelo axioms, the library includes:

| Area | Highlights |
|------|-----------|
| **Von Neumann arithmetic** | `vN : ℕ₀ → HFSet`; GCD, Fibonacci, binomial, totient, Cantor pairing, Gödel beta, primes (TFA, Gauss lemma), Fermat–Wilson, CRT; Peano-system initiality (`InitialityVN`) |
| **Abstract algebra** | `HFGroup`, `HFSubgroup`, `HFGroupHom`, `HFNormalSubgroup`, `HFRing`, `HFField`, `HFModule`, quotient groups, three isomorphism theorems, correspondence theorem, **Zassenhaus' butterfly lemma** |
| **Group actions & Sylow** | `HFGroupAction`, orbits, stabilizers, orbit-stabilizer (via Lagrange); McKay's combinatorial proof of Cauchy's theorem; **Sylow I + II** (`sylow_first`, `sylowConjugate` via the p-group fixed-point theorem) |
| **Rings, fields & matrices** | Generic quotient ring `R/I` (`HFIdeal`, `HFRing.quotient`); `ℤ/nℤ` ring and `ℤ/pℤ` field (`ZModN`, `ZModFieldP`, inverse via Fermat); n×n matrix ring `HFMatrixRing` over any `HFRing` |
| **Integers & rationals** | `ℤ₀ = Quotient (ℕ₀×ℕ₀)`, commutative ring laws, order, GCD, p-adic valuation, Möbius μ, Liouville λ, Bézout, canonical representative; `ℚ₀` with absolute value, density, dyadic Cauchy sequences |
| **Combinatorics** | Native pigeonhole principle, inclusion–exclusion (2 and 3 sets), cardinality/injectivity/surjectivity lemmas (`Combinatorics/Counting`) |
| **Order theory** | Preorder, partial/total/well order; `wf_induction`, `no_infinite_descent` |
| **Topology** | `HFTopSpace`, interior/closure/boundary, subspace topology, continuous maps, neighborhood spaces, separation axioms T₀–T₄ |



| Type | Definition | Module |
|------|-----------|--------|
| `CList` | `inductive CList \| mk : PList CList → CList` | Basic |
| `HFSet` | `Quotient CList.Setoid` | HFSets |

### Core pipeline

```
CList  ──normalize──▶  CList (canonical form)
  │                                  │
  └──Quotient.mk──▶  HFSet ◀──repr──┘
```

1. **`normalize`**: recursively normalizes children, deduplicates, sorts → canonical form
2. **`normalize_idem`**: normalization is idempotent
3. **`normalize_eq_of_extEq`**: extensionally equal CLists have the same normal form
4. **`HFSet.repr`**: extracts the canonical representative via `Quotient.lift`
5. **`HFSet.Mem`**: membership lifted to quotient via `Quotient.liftOn₂`

### Building

```bash
lake build AczelSetTheory
```

Requires Lean v4.30.0 (see `lean-toolchain`).

### Running

```bash
lake build Main && lake env lean --run Main.lean
```

### Documentation

- [AI-GUIDE.md](AI-GUIDE.md) — Documentation protocol and naming conventions
- [REFERENCE.md](REFERENCE.md) — Complete technical reference (all definitions, theorems, signatures)
- [NAMING-CONVENTIONS.md](NAMING-CONVENTIONS.md) — Extended naming rules and symbol dictionary
- [CHANGELOG.md](CHANGELOG.md) — Change history
- [CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md) — Project status overview
- [DEPENDENCIES.md](DEPENDENCIES.md) — Module dependency diagram (initial-phase scope; use `lake graph` for the full graph)
- [NEXT_STEPS.md](NEXT_STEPS.md) — Development roadmap (tactical)
- [PLANNING.md](PLANNING.md) / [PLANNING-FASE-B.md](PLANNING-FASE-B.md) — Long-term roadmap and FASE B milestone tracking
- [AUDIT-MODULE-MATRIX.md](AUDIT-MODULE-MATRIX.md) — Per-module audit (LOC, sorry/axiom/noncomputable counts)

### Documentación heredada de Peano

AczelSetTheory es el continuador natural del proyecto [Peano](https://github.com/julian1c2a/Peano) (en feature-freeze desde 2026-05-10). La documentación de referencia de Peano se ha integrado en `doc/`:

**Referencias temáticas (doc/):**

- [doc/REFERENCE-Arithmetic.md](doc/REFERENCE-Arithmetic.md) — Add, Sub, Mul, Div, Pow, Primos
- [doc/REFERENCE-Combinatorics.md](doc/REFERENCE-Combinatorics.md) — Factorial, Binom, Newton
- [doc/REFERENCE-Foundation.md](doc/REFERENCE-Foundation.md) — PureAxioms, CantorPairing, GodelBeta
- [doc/REFERENCE-GroupTheory.md](doc/REFERENCE-GroupTheory.md) — Group, Subgroup, Cosets, Sylow I–III
- [doc/REFERENCE-ListsAndSets.md](doc/REFERENCE-ListsAndSets.md) — FSet, FSetFunction, EquivRel
- [doc/REFERENCE-NumberTheory.md](doc/REFERENCE-NumberTheory.md) — ModEq, Totient, CRT, Fermat, Wilson
- [doc/REFERENCE-Prelim.md](doc/REFERENCE-Prelim.md) — Prelim, ExistsUnique, Tuples

**Documentos de diseño únicos (doc/peano/):**

- [doc/peano/README.md](doc/peano/README.md) — Índice y contexto del directorio
- [doc/peano/INTUICIONES.md](doc/peano/INTUICIONES.md) — Intuiciones matemáticas y filosóficas
- [doc/peano/PEANO_MATHLIB_COMPARE.md](doc/peano/PEANO_MATHLIB_COMPARE.md) — Comparativa con Mathlib
- [doc/peano/CAUCHY_MCKAY_PROOF.md](doc/peano/CAUCHY_MCKAY_PROOF.md) — Prueba de Cauchy vía McKay
- [doc/peano/FERMAT_PROOF.md](doc/peano/FERMAT_PROOF.md) — Prueba del pequeño teorema de Fermat

**Historial completo de Peano:** [CHANGELOG-PEANO.md](CHANGELOG-PEANO.md)

---

### Credits

- Peter Aczel — *Non-Well-Founded Sets* (foundational theory)
- Lean 4 / Mathlib community — language and conventions
- AI assistance: Claude (Anthropic), GitHub Copilot
