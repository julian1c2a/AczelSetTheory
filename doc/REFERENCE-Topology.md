# REFERENCE — Topology

Módulo: `AczelSetTheory.Topology`  
Namespace: `HFTopology`  
Barrel: `AczelSetTheory/Topology.lean`

---

## Topology.Basic

**Fuente:** `AczelSetTheory/Topology/Basic.lean`

### Estructura

```lean
structure HFTopSpace where
  X          : HFSet                          -- conjunto base
  τ          : HFSet                          -- colección de abiertos
  τ_sub      : ∀ {U}, U ∈ τ → U ⊆ X
  empty_mem  : HFSet.empty ∈ τ
  univ_mem   : X ∈ τ
  sUnion_mem : ∀ {F}, F ⊆ τ → HFSet.sUnion F ∈ τ
  inter_mem  : ∀ {U V}, U ∈ τ → V ∈ τ → HFSet.inter U V ∈ τ
```

### Predicados

```lean
def HFTopSpace.isClosed (ts : HFTopSpace) (A : HFSet) : Prop :=
  HFSet.setminus ts.X A ∈ ts.τ
```

### Teoremas

| Nombre | Enunciado |
|--------|-----------|
| `union_mem` | `U ∈ ts.τ → V ∈ ts.τ → HFSet.union U V ∈ ts.τ` |
| `empty_sub` | `HFSet.empty ⊆ U` |
| `closed_empty` | `ts.isClosed HFSet.empty` |
| `closed_univ` | `ts.isClosed ts.X` |
| `closed_inter` | `ts.isClosed A → ts.isClosed B → ts.isClosed (HFSet.inter A B)` |
| `closed_union` | `ts.isClosed A → ts.isClosed B → ts.isClosed (HFSet.union A B)` |

---

## Topology.Interior

**Fuente:** `AczelSetTheory/Topology/Interior.lean`

### Definiciones

```lean
noncomputable def HFTopSpace.interior (ts : HFTopSpace) (A : HFSet) : HFSet :=
  HFSet.sUnion (HFSet.sep ts.τ (fun U => U ⊆ A))

noncomputable def HFTopSpace.closure (ts : HFTopSpace) (A : HFSet) : HFSet :=
  HFSet.setminus ts.X (ts.interior (HFSet.setminus ts.X A))

noncomputable def HFTopSpace.exterior (ts : HFTopSpace) (A : HFSet) : HFSet :=
  ts.interior (HFSet.setminus ts.X A)

noncomputable def HFTopSpace.boundary (ts : HFTopSpace) (A : HFSet) : HFSet :=
  HFSet.setminus (ts.closure A) (ts.interior A)

def HFTopSpace.isInteriorPt (ts : HFTopSpace) (x A : HFSet) : Prop := x ∈ ts.interior A
def HFTopSpace.isExteriorPt (ts : HFTopSpace) (x A : HFSet) : Prop := x ∈ ts.exterior A
def HFTopSpace.isBoundaryPt (ts : HFTopSpace) (x A : HFSet) : Prop := x ∈ ts.boundary A
def HFTopSpace.isAccumulationPt (ts : HFTopSpace) (x A : HFSet) : Prop :=
  x ∈ ts.X ∧ ∀ U, U ∈ ts.τ → x ∈ U → ∃ y, y ∈ A ∧ y ∈ U ∧ y ≠ x
def HFTopSpace.isAdherencePt (ts : HFTopSpace) (x A : HFSet) : Prop :=
  x ∈ ts.X ∧ ∀ U, U ∈ ts.τ → x ∈ U → ∃ y, y ∈ A ∧ y ∈ U
def HFTopSpace.isIsolatedPt (ts : HFTopSpace) (x A : HFSet) : Prop :=
  x ∈ A ∧ ∃ U, U ∈ ts.τ ∧ x ∈ U ∧ ∀ y, y ∈ A → y ∈ U → y = x
```

### Teoremas — Interior

| Nombre | Enunciado |
|--------|-----------|
| `mem_interior` | `x ∈ ts.interior A ↔ ∃ U, U ∈ ts.τ ∧ U ⊆ A ∧ x ∈ U` |
| `interior_subset` | `ts.interior A ⊆ A` |
| `interior_open` | `ts.interior A ∈ ts.τ` |
| `interior_largest` | `U ∈ ts.τ → U ⊆ A → U ⊆ ts.interior A` (mayor abierto) |
| `interior_eq_of_open` | `A ∈ ts.τ → ts.interior A = A` |

### Teoremas — Clausura

| Nombre | Enunciado |
|--------|-----------|
| `closure_closed` | `ts.isClosed (ts.closure A)` |
| `subset_closure` | `A ⊆ ts.X → A ⊆ ts.closure A` |
| `closure_eq_of_closed` | `ts.isClosed A → A ⊆ ts.X → ts.closure A = A` |

### Teoremas — Exterior

| Nombre | Enunciado |
|--------|-----------|
| `exterior_open` | `ts.exterior A ∈ ts.τ` |

### Teoremas — Clasificación de puntos

| Nombre | Enunciado |
|--------|-----------|
| `isInteriorPt_iff` | `ts.isInteriorPt x A ↔ x ∈ ts.interior A` |
| `accumulation_is_adherence` | `ts.isAccumulationPt x A → ts.isAdherencePt x A` |
| `isolated_not_accumulation` | `ts.isIsolatedPt x A → ¬ts.isAccumulationPt x A` |
| `isAdherencePt_iff_mem_closure` | `(hA : A ⊆ ts.X) → ts.isAdherencePt x A ↔ x ∈ ts.closure A` |
| `interior_exterior_boundary_partition` | `A ⊆ ts.X → ∀ x ∈ ts.X, exactamente uno de: interior/exterior/frontera` |

---

## Topology.Neighborhoods

**Fuente:** `AczelSetTheory/Topology/Neighborhoods.lean`

### Estructura

```lean
structure HFNeighborSpace where
  X         : HFSet
  𝒩         : HFSet → HFSet          -- sistema de entornos: x ↦ 𝒩(x)
  𝒩_sub     : ∀ {x N : HFSet}, x ∈ X → N ∈ 𝒩 x → N ⊆ X
  point_mem : ∀ {x N : HFSet}, x ∈ X → N ∈ 𝒩 x → x ∈ N
  univ_mem  : ∀ {x : HFSet}, x ∈ X → X ∈ 𝒩 x
  up_closed : ∀ {x N M : HFSet}, x ∈ X → N ∈ 𝒩 x → N ⊆ M → M ⊆ X → M ∈ 𝒩 x
  inter_mem : ∀ {x N M : HFSet}, x ∈ X → N ∈ 𝒩 x → M ∈ 𝒩 x → HFSet.inter N M ∈ 𝒩 x
  interior  : ∀ {x N : HFSet}, x ∈ X → N ∈ 𝒩 x →
                ∃ M, M ∈ 𝒩 x ∧ M ⊆ N ∧ ∀ {y : HFSet}, y ∈ M → N ∈ 𝒩 y
```

### Conversiones

```lean
noncomputable def HFTopSpace.toNeighborSpace (ts : HFTopSpace) : HFNeighborSpace
-- 𝒩(x) = {N ⊆ X | ∃ U ∈ τ, x ∈ U ∧ U ⊆ N}

noncomputable def HFNeighborSpace.toTopSpace (ns : HFNeighborSpace) : HFTopSpace
-- τ = {U ⊆ X | ∀ x ∈ U, U ∈ 𝒩(x)}
```

### Teoremas de equivalencia

| Nombre | Enunciado |
|--------|-----------|
| `toNeighborSpace_toTopSpace_τ` | `ts.toNeighborSpace.toTopSpace.τ = ts.τ` |
| `toTopSpace_toNeighborSpace_𝒩` | `(hx : x ∈ ns.X) → ns.toTopSpace.toNeighborSpace.𝒩 x = ns.𝒩 x` |

---

## Topology.Subspace

**Fuente:** `AczelSetTheory/Topology/Subspace.lean`

### Definiciones

```lean
noncomputable def HFTopSpace.preimage (ts : HFTopSpace) (f : HFSet → HFSet) (V : HFSet) : HFSet :=
  HFSet.sep ts.X (fun x => f x ∈ V)

noncomputable def HFTopSpace.subspace (ts : HFTopSpace) (A : HFSet) (hA : A ⊆ ts.X) : HFTopSpace
-- τ_A = {V ⊆ A | ∃ U ∈ τ, V = U ∩ A}

structure HFContinuous (ts₁ ts₂ : HFTopSpace) where
  f             : HFSet → HFSet
  f_mem         : ∀ {x}, x ∈ ts₁.X → f x ∈ ts₂.X
  preimage_open : ∀ {V}, V ∈ ts₂.τ → ts₁.preimage f V ∈ ts₁.τ
```

### Teoremas

| Nombre | Enunciado |
|--------|-----------|
| `mem_preimage` | `x ∈ ts.preimage f V ↔ x ∈ ts.X ∧ f x ∈ V` |
| `HFContinuous.id` | Aplicación identidad es continua |
| `HFContinuous.comp` | Composición de continuas es continua |
| `preimage_inter` | `ts₁.preimage f (V₁ ∩ V₂) = ts₁.preimage f V₁ ∩ ts₁.preimage f V₂` |

---

## Estado

**0 sorries.** Módulo completo. Última actualización: 2026-05-22.
