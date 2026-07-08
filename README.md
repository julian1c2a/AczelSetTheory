# AczelSetTheory

## Aczel's Set Theory in Lean 4

**Author**: JuliÃ¡n CalderÃ³n Almendros
**License**: MIT
**Lean version**: v4.30.0
**Build status**: âœ… 9 `sorry` â€” 0 `noncomputable` â€” 0 errors, 0 warnings â€” 200 `.lean` files (~33 500 LOC), build 255 jobs
**Roadmap**: FASE A (paridad Peano) âœ… completa Â· FASE B (consolidaciÃ³n) âœ… completa Â· FASE C (anÃ¡lisis real) ðŸš§ en curso

---

### What it is

This repository formalizes Aczel's constructive set theory in Lean 4. The central object is `CList` â€” a computable representation of hereditarily finite sets as nested lists â€” together with a provably correct normalization procedure that yields canonical representatives. The quotient type `HFSet` identifies extensionally equal `CList`s.

The Zermelo axioms (Extensionality, Empty Set, Pairs, Union, Separation, Intersection, Setminus, Powerset) are **derived as theorems**, not postulated.

Key properties of this set theory:

- **Computable**: every *definition* is decidable and executable â€” **0 `noncomputable def`** across the whole library, including the hereditarily-finite choice function `HFSet.choose` (a plain `def`)
- **No axiom of infinity**: natural numbers are constructed from sets (`vN : â„•â‚€ â†’ HFSet`)
- **Well-founded recursion and induction** over sets (`âˆˆ` is well-founded)
- **Axiom-free foundations**: the Zermelo axioms are derived theorems, not postulates
- **Standard axiom footprint**: theorems reduce to `{propext, Classical.choice, Quot.sound}` â€” the same set as ordinary Lean/Mathlib developments. `Classical.choice` is used only for *propositional* reasoning (excluded middle via `byContradiction`/`em`) and enters structurally at the `CList.extEq` foundation (well-founded recursion); it is never used to make non-computable selections. Verifiable per theorem with `#print axioms`

### Derived Zermelo Axioms

| Axiom | Theorem | Statement | Status |
|-------|---------|-----------|--------|
| Extensionality | `HFSet.extensionality` | âˆ€ A B, (âˆ€ x, x âˆˆ A â†” x âˆˆ B) â†’ A = B | âœ… |
| Empty Set | `HFSet.not_mem_empty` | âˆ€ x, x âˆ‰ âˆ… | âœ… |
| Pairs | `HFSet.mem_pair` | x âˆˆ {a, b} â†” x = a âˆ¨ x = b | âœ… |
| Union | `HFSet.mem_sUnion` | x âˆˆ â‹ƒ A â†” âˆƒ B âˆˆ A, x âˆˆ B | âœ… |
| Separation | `HFSet.mem_sep` | x âˆˆ sep A P â†” x âˆˆ A âˆ§ P x | âœ… |
| Intersection | `HFSet.mem_inter` | x âˆˆ A âˆ© B â†” x âˆˆ A âˆ§ x âˆˆ B | âœ… |
| Setminus | `HFSet.mem_setminus` | x âˆˆ A \ B â†” x âˆˆ A âˆ§ x âˆ‰ B | âœ… |
| Powerset | `HFSet.mem_powerset` | B âˆˆ ð’« A â†” âˆ€ x, x âˆˆ B â†’ x âˆˆ A | âœ… |

### Module structure

```
AczelSetTheory/
  CList/             â€” Computable hereditarily-finite lists (7 sub-modules)
    Basic.lean       â€” CList type, cSize : â„•â‚€, dedup, insertionSort, normalize
    ExtEq.lean       â€” Extensional equality (reflexivity, transitivity, commutativity)
    SetEquiv.lean    â€” Nodup, SetEquiv, dedup properties
    Order.lean       â€” lt: irreflexivity, antisymmetry, totality, transitivity
    Sort.lean        â€” Sorted, insertionSort preserves sorted/nodup/setEquiv
    Normalize.lean   â€” Idempotency, uniqueness (sorted_nodup_setEquiv_eq)
    Filter.lean      â€” filter preserves extEq (P_respects, extEq_filter)
  PList/             â€” Polymorphic list over â„•â‚€, Peano bridge (4 sub-modules)
    Basic.lean       â€” PList Î±, length : â„•â‚€, map, filter, flatMap, mem
    Lemmas.lean      â€” @[simp] lemmas, length_append, mem_append, mem_filter
    Omega0.lean      â€” Ïˆ_* bridge lemmas enabling omegaâ‚€ tactic
    Fin0.lean        â€” Finâ‚€ n type, decidable equality, PList.get
  HFSets.lean        â€” HFSet quotient type, membership, extensionality, empty, pairs
  HFList.lean        â€” Ordered sequences of HFSets (PList HFSet)
  Notation.lean      â€” âˆ…, {[a,b]}, {[a]}, {[x âˆˆ A <|> P]}, âŸªa,bâŸ«, numerals 0â€“9
  Operations/        â€” CList-level constructors lifted to HFSet (21 sub-modules)
    Union, Intersection, Setminus, Separation, Pair, Powerset, SymDiff,
    OrderedPair, Relation, Function, Inverse, Restriction, Composition,
    Replacement, Cardinal, FunctionComp, Identity, Product, CartProd, NPow, Order
  Axioms/            â€” HFSet-level axioms and theorems (41 sub-modules)
    Union, Intersection, Setminus, Separation, Pair, Powerset, Singleton,
    SymDiff, OrderedPair, Foundation, Decidable, Subset, Lattice,
    BooleanAlgebra, BooleanRing, Succ, VonNeumann, Choice, Cardinal,
    Relation, Function, Bijection, Inverse, Composition, Restriction,
    Replacement, FunctionComp, Identity, Product, Image, Adjunction,
    Induction, CartProd, Ordinal, OrdinalNat, Fintype, NPow, Rank,
    Order, WellOrder, LinearOrder
  VN/                â€” Von Neumann embedding vN : â„•â‚€ â†’ HFSet (49 sub-modules)
    Basic, Injective, IsNat, Arithmetic, FSet, PeanoAxioms, PeanoArith,
    PowVN, SubVN, DivVN, FactorialVN, CardVN, RankVN, GcdVN, FibVN, BinomVN,
    SummationVN, SqrtVN, LogVN, DigitsVN, ModEqVN, TotientVN, PrimesVN,
    CantorPairingVN, PairingVN, NewtonBinomVN, ProductVN, GodelBetaVN,
    HFGroupVN, ProdBridgeVN, MapBridgeVN, ListBridgeVN,
    PrimeVN, FermatVN, CRTVN, InitialityVN, LatticeVN, ActionVN, OrbitVN,
    PermVN, SignVN, SymGroupVN, CountingVN, NormalSubgroupVN, QuotientGroupVN,
    FirstIsomorphismVN, SecondIsomorphismVN, ThirdIsomorphismVN,
    CorrespondenceTheoremVN
  Algebra/           â€” Native algebraic structures in HFSet (23 sub-modules)
    Group, Subgroup, GroupHom, NormalSubgroup, Ring, CosetCount, Monoid, RingHom,
    Field, Module, LinearSpace, Lattice, Action, CosetAction, QuotientGroup,
    FirstIsomorphism, SecondIsomorphism, ThirdIsomorphism, CorrespondenceTheorem,
    Sylow, Zassenhaus, QuotientRing, HFMatrix
  Integers/          â€” Integer type â„¤â‚€ (12 sub-modules)
    Basic, Order, Functions, Arithmetic, Bijection, PadicVal, MobiusLiouville,
    Canonical, Bezout, ZModN, HFInt, HFIntOps
  Rationals/         â€” Rational type â„šâ‚€ and analytic theory (18 sub-modules)
    Basic, AbsVal, Density, IsCauchy, Inv, Bisection, Canonical, Convergence,
    PowOrder, RationalLog, Roots, CauchySeqAlgebra, Archimedean, Irrational,
    HFRat, HFRatOps, HFRatCauchy, MinAdd
  Combinatorics/     â€” Native finite combinatorics in HFSet (1 sub-module)
    Counting  â€” pigeonhole, inclusionâ€“exclusion (2 and 3 sets), card lemmas
  Topology/          â€” Topological spaces over HFSet (5 sub-modules)
    Basic, Interior, Subspace, Neighborhoods, Separation
```

### What it covers

Beyond the Zermelo axioms, the library includes:

| Area | Highlights |
|------|-----------|
| **Von Neumann arithmetic** | `vN : â„•â‚€ â†’ HFSet`; GCD, Fibonacci, binomial, totient, Cantor pairing, GÃ¶del beta, primes (TFA, Gauss lemma), Fermatâ€“Wilson, CRT; Peano-system initiality (`InitialityVN`) |
| **Abstract algebra** | `HFGroup`, `HFSubgroup`, `HFGroupHom`, `HFNormalSubgroup`, `HFRing`, `HFField`, `HFModule`, quotient groups, three isomorphism theorems, correspondence theorem, **Zassenhaus' butterfly lemma** |
| **Group actions & Sylow** | `HFGroupAction`, orbits, stabilizers, orbit-stabilizer (via Lagrange); McKay's combinatorial proof of Cauchy's theorem; **Sylow I + II** (`sylow_first`, `sylowConjugate` via the p-group fixed-point theorem) |
| **Rings, fields & matrices** | Generic quotient ring `R/I` (`HFIdeal`, `HFRing.quotient`); `â„¤/nâ„¤` ring and `â„¤/pâ„¤` field (`ZModN`, `ZModFieldP`, inverse via Fermat); nÃ—n matrix ring `HFMatrixRing` over any `HFRing` |
| **Integers & rationals** | `â„¤â‚€ = Quotient (â„•â‚€Ã—â„•â‚€)`, commutative ring laws, order, GCD, p-adic valuation, MÃ¶bius Î¼, Liouville Î», BÃ©zout, canonical representative; `â„šâ‚€` with absolute value, density, dyadic Cauchy sequences |
| **Combinatorics** | Native pigeonhole principle, inclusionâ€“exclusion (2 and 3 sets), cardinality/injectivity/surjectivity lemmas (`Combinatorics/Counting`) |
| **Order theory** | Preorder, partial/total/well order; `wf_induction`, `no_infinite_descent` |
| **Topology** | `HFTopSpace`, interior/closure/boundary, subspace topology, continuous maps, neighborhood spaces, separation axioms Tâ‚€â€“Tâ‚„ |



| Type | Definition | Module |
|------|-----------|--------|
| `CList` | `inductive CList \| mk : PList CList â†’ CList` | Basic |
| `HFSet` | `Quotient CList.Setoid` | HFSets |

### Core pipeline

```
CList  â”€â”€normalizeâ”€â”€â–¶  CList (canonical form)
  â”‚                                  â”‚
  â””â”€â”€Quotient.mkâ”€â”€â–¶  HFSet â—€â”€â”€reprâ”€â”€â”˜
```

1. **`normalize`**: recursively normalizes children, deduplicates, sorts â†’ canonical form
2. **`normalize_idem`**: normalization is idempotent
3. **`normalize_eq_of_extEq`**: extensionally equal CLists have the same normal form
4. **`HFSet.repr`**: extracts the canonical representative via `Quotient.lift`
5. **`HFSet.Mem`**: membership lifted to quotient via `Quotient.liftOnâ‚‚`

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

- [AI-GUIDE.md](AI-GUIDE.md) â€” Documentation protocol and naming conventions
- [REFERENCE.md](REFERENCE.md) â€” Complete technical reference (all definitions, theorems, signatures)
- [NAMING-CONVENTIONS.md](NAMING-CONVENTIONS.md) â€” Extended naming rules and symbol dictionary
- [CHANGELOG.md](CHANGELOG.md) â€” Change history
- [CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md) â€” Project status overview
- [DEPENDENCIES.md](DEPENDENCIES.md) â€” Module dependency diagram (initial-phase scope; use `lake graph` for the full graph)
- [NEXT_STEPS.md](NEXT_STEPS.md) â€” Development roadmap (tactical)
- [PLANNING.md](PLANNING.md) / [PLANNING-FASE-B.md](PLANNING-FASE-B.md) â€” Long-term roadmap and FASE B milestone tracking
- [AUDIT-MODULE-MATRIX.md](AUDIT-MODULE-MATRIX.md) â€” Per-module audit (LOC, sorry/axiom/noncomputable counts)

### DocumentaciÃ³n heredada de Peano

AczelSetTheory es el continuador natural del proyecto [Peano](https://github.com/julian1c2a/Peano) (en feature-freeze desde 2026-05-10). La documentaciÃ³n de referencia de Peano se ha integrado en `doc/`:

**Referencias temÃ¡ticas (doc/):**

- [doc/REFERENCE-Arithmetic.md](doc/REFERENCE-Arithmetic.md) â€” Add, Sub, Mul, Div, Pow, Primos
- [doc/REFERENCE-Combinatorics.md](doc/REFERENCE-Combinatorics.md) â€” Factorial, Binom, Newton
- [doc/REFERENCE-Foundation.md](doc/REFERENCE-Foundation.md) â€” PureAxioms, CantorPairing, GodelBeta
- [doc/REFERENCE-GroupTheory.md](doc/REFERENCE-GroupTheory.md) â€” Group, Subgroup, Cosets, Sylow Iâ€“III
- [doc/REFERENCE-ListsAndSets.md](doc/REFERENCE-ListsAndSets.md) â€” FSet, FSetFunction, EquivRel
- [doc/REFERENCE-NumberTheory.md](doc/REFERENCE-NumberTheory.md) â€” ModEq, Totient, CRT, Fermat, Wilson
- [doc/REFERENCE-Prelim.md](doc/REFERENCE-Prelim.md) â€” Prelim, ExistsUnique, Tuples

**Documentos de diseÃ±o Ãºnicos (doc/peano/):**

- [doc/peano/README.md](doc/peano/README.md) â€” Ãndice y contexto del directorio
- [doc/peano/INTUICIONES.md](doc/peano/INTUICIONES.md) â€” Intuiciones matemÃ¡ticas y filosÃ³ficas
- [doc/peano/PEANO_MATHLIB_COMPARE.md](doc/peano/PEANO_MATHLIB_COMPARE.md) â€” Comparativa con Mathlib
- [doc/peano/CAUCHY_MCKAY_PROOF.md](doc/peano/CAUCHY_MCKAY_PROOF.md) â€” Prueba de Cauchy vÃ­a McKay
- [doc/peano/FERMAT_PROOF.md](doc/peano/FERMAT_PROOF.md) â€” Prueba del pequeÃ±o teorema de Fermat

**Historial completo de Peano:** [CHANGELOG-PEANO.md](CHANGELOG-PEANO.md)

---

### Credits

- Peter Aczel â€” *Non-Well-Founded Sets* (foundational theory)
- Lean 4 / Mathlib community â€” language and conventions
- AI assistance: Claude (Anthropic), GitHub Copilot
