# Technical Reference — VN (von Neumann Embedding)

**Last updated:** 2026-05-14
**Parent:** [../REFERENCE.md](../REFERENCE.md)
**Related:** [REFERENCE-HFSets.md](REFERENCE-HFSets.md) | [REFERENCE-Algebra.md](REFERENCE-Algebra.md) | [REFERENCE-PList.md](REFERENCE-PList.md)

@axiom_system: AczelSetTheory
@importance: high

---

## Overview

`VN` provides the concrete embedding of Peano naturals (`ℕ₀`) into `HFSet` via
the von Neumann ordinal construction. The map `vN : ℕ₀ → HFSet` is defined
recursively as `vN 𝟘 = ∅` and `vN (σ n) = succ (vN n) = vN n ∪ {vN n}`.

This layer proves injectivity, characterises the image as exactly the
`HFSet.isNat` sets (defined in [REFERENCE-Algebra.md](REFERENCE-Algebra.md)),
and establishes order-preservation (`∈` ↔ `<`).

**Primary namespace:** `VN`
**External dependency:** `ℕ₀` = `PeanoNat` from `.lake/packages/peanolib`.

| # | File | Status |
|---|------|--------|
| 64 | `AczelSetTheory/VN/Basic.lean` | ✅ Complete |
| 65 | `AczelSetTheory/VN/Injective.lean` | ✅ Complete |
| 66 | `AczelSetTheory/VN/IsNat.lean` | ✅ Complete |
| 67 | `AczelSetTheory/VN/Arithmetic.lean` | ✅ Complete |

---

## 4. Definitions

### 4.42 VN/Basic.lean — `namespace VN`

#### 4.42.1 `VN.vN`

```lean
def VN.vN : ℕ₀ → HFSet
  | 𝟘    => HFSet.empty
  | σ n  => HFSet.succ (vN n)
```

- **Math**: vN(0) = ∅; vN(n+1) = vN(n) ∪ {vN(n)}
- Computable, structurally recursive.

---

## 6. Theorems

### 6.45 VN/Basic.lean — `namespace VN`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `vN_zero` | `vN 𝟘 = HFSet.empty` |
| 2 | `vN_succ` | `(n : ℕ₀) → vN (σ n) = HFSet.succ (vN n)` |
| 3 | `vN_succ_ne_empty` | `(n : ℕ₀) → vN (σ n) ≠ HFSet.empty` |
| 4 | `mem_vN_succ` | `(x : HFSet) → (n : ℕ₀) → (x ∈ vN (σ n) ↔ x ∈ vN n ∨ x = vN n)` |
| 5 | `vN_mem_vN_succ` | `(n : ℕ₀) → vN n ∈ vN (σ n)` |
| 6 | `vN_subset_vN_succ` | `(n : ℕ₀) → vN n ⊆ vN (σ n)` |

### 6.46 VN/Injective.lean — `namespace VN`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `vN_injective` | `Function.Injective vN` |

### 6.47 VN/IsNat.lean — `namespace VN`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `isNat_vN` | `(n : ℕ₀) → HFSet.isNat (vN n)` |
| 2 | `vN_mem_range` | `{A : HFSet} → (h : HFSet.isNat A) → ∃ n : ℕ₀, vN n = A` |
| 3 | `isNat_iff_range` | `(A : HFSet) → (HFSet.isNat A ↔ ∃ n : ℕ₀, vN n = A)` |

### 6.48 VN/Arithmetic.lean — `namespace VN`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `mem_vN_iff_lt` | `(m n : ℕ₀) → (vN m ∈ vN n ↔ m < n)` |
| 2 | `vN_mono` | `(m n : ℕ₀) → (h : m ≤ n) → vN m ⊆ vN n` |
| 3 | `vN_le_iff_subset` | `(m n : ℕ₀) → (m ≤ n ↔ vN m ⊆ vN n)` |

---

## 7. Exports per Module

### VN/Basic.lean

`VN.vN`, `VN.vN_zero`, `VN.vN_succ`, `VN.vN_succ_ne_empty`, `VN.mem_vN_succ`, `VN.vN_mem_vN_succ`, `VN.vN_subset_vN_succ`

### VN/Injective.lean

`VN.vN_injective`

### VN/IsNat.lean

`VN.isNat_vN`, `VN.vN_mem_range`, `VN.isNat_iff_range`

### VN/Arithmetic.lean

`VN.mem_vN_iff_lt`, `VN.vN_mono`, `VN.vN_le_iff_subset`
