# Technical Reference — VN (von Neumann Embedding)

**Last updated:** 2026-05-16
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
| 68 | `AczelSetTheory/VN/FSet.lean` | ✅ Complete |
| 69 | `AczelSetTheory/VN/PeanoAxioms.lean` | ✅ Complete |
| 70 | `AczelSetTheory/VN/PeanoArith.lean` | ✅ Complete |
| 76 | `AczelSetTheory/VN/CardVN.lean` | ✅ Complete |

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

#### 4.42.2 `VN.addVN` — `VN/PeanoArith.lean`

```lean
def VN.addVN (A : HFSet) : ℕ₀ → HFSet
  | .zero   => A
  | .succ n => HFSet.succ (addVN A n)
```

- **Math**: addVN(A, 0) = A; addVN(A, n+1) = succ(addVN(A, n))
- Applies `HFSet.succ` exactly `n` times starting from `A`.
- Computable, structurally recursive.
- Key theorem: `vN (add m n) = addVN (vN m) n`

#### 4.42.3 `VN.fsetToHFSet` — `VN/FSet.lean`

```lean
def VN.fsetToHFSet (S : ℕ₀FSet) : HFSet :=
  S.elems.foldl (fun acc n => HFSet.union acc (HFSet.singleton (vN n))) HFSet.empty
```

- **Math**: φ(S) = ⋃ {vN(n) ∣ n ∈ S}
- Requires `import Peano.PeanoNat.ListsAndSets.FSet` and `open Peano Peano.FSet`.
- Computable.
- Membership: `x ∈ fsetToHFSet S ↔ ∃ n ∈ S, x = vN n`
- Injective (uses `FSet.eq_of_mem_iff'`).

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

### 6.49 VN/FSet.lean — `namespace VN`

**Imports:** `AczelSetTheory.VN.Injective`, `AczelSetTheory.VN.IsNat`, `Peano.PeanoNat.ListsAndSets.FSet`
**Opens:** `Peano`, `Peano.FSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `fsetToHFSet_empty` | `fsetToHFSet ℕ₀FSet.empty = HFSet.empty` |
| 2 | `fsetToHFSet_singleton` | `(n : ℕ₀) → fsetToHFSet (ℕ₀FSet.singleton n) = HFSet.singleton (vN n)` |
| 3 | `mem_fsetToHFSet` | `(x : HFSet) → (S : ℕ₀FSet) → (x ∈ fsetToHFSet S ↔ ∃ n ∈ S, x = vN n)` |
| 4 | `vN_mem_fsetToHFSet_iff` | `(n : ℕ₀) → (S : ℕ₀FSet) → (vN n ∈ fsetToHFSet S ↔ n ∈ S)` |
| 5 | `fsetToHFSet_injective` | `Function.Injective (fsetToHFSet : ℕ₀FSet → HFSet)` |

### 6.50 VN/PeanoAxioms.lean — `namespace VN`

**Imports:** `AczelSetTheory.VN.Injective`, `AczelSetTheory.VN.IsNat`
**Opens:** `Peano`

**Nivel HFSet.isNat (axiomas PA puros):**

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `isNat_succ_ne_zero` | `(A : HFSet) → HFSet.isNat A → HFSet.succ A ≠ HFSet.empty` |
| 2 | `isNat_succ_injective` | `(A B : HFSet) → HFSet.isNat A → HFSet.isNat B → HFSet.succ A = HFSet.succ B → A = B` |
| 3 | `isNat_induction` | `(P : HFSet → Prop) → P HFSet.empty → (∀ k, HFSet.isNat k → P k → P (HFSet.succ k)) → (n : HFSet) → HFSet.isNat n → P n` |

**Nivel vN (transporte a imagen de vN):**

| # | Theorem | Lean signature |
|---|---------|---------------|
| 4 | `vN_zero_ne_succ` | `(n : ℕ₀) → vN 𝟘 ≠ vN (σ n)` |
| 5 | `vN_succ_injective_vN` | `(m n : ℕ₀) → vN (σ m) = vN (σ n) → m = n` |
| 6 | `vN_induction` | `(P : HFSet → Prop) → P (vN 𝟘) → (∀ n : ℕ₀, P (vN n) → P (vN (σ n))) → (n : ℕ₀) → P (vN n)` |

### 6.51 VN/PeanoArith.lean — `namespace VN`

**Imports:** `AczelSetTheory.VN.Arithmetic`, `AczelSetTheory.VN.PeanoAxioms`
**Opens:** `Peano`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `addVN_zero` | `(A : HFSet) → addVN A 𝟘 = A` |
| 2 | `addVN_succ` | `(A : HFSet) → (n : ℕ₀) → addVN A (σ n) = HFSet.succ (addVN A n)` |
| 3 | `vN_add` | `(m n : ℕ₀) → vN (add m n) = addVN (vN m) n` |
| 4 | `vN_add_comm` | `(m n : ℕ₀) → vN (add m n) = vN (add n m)` |
| 5 | `vN_add_assoc` | `(m n k : ℕ₀) → vN (add (add m n) k) = vN (add m (add n k))` |
| 6 | `vN_add_zero` | `(m : ℕ₀) → vN (add m 𝟘) = vN m` |
| 7 | `vN_zero_add` | `(m : ℕ₀) → vN (add 𝟘 m) = vN m` |
| 8 | `vN_mul_comm` | `(m n : ℕ₀) → vN (mul m n) = vN (mul n m)` |
| 9 | `vN_mul_assoc` | `(m n k : ℕ₀) → vN (mul (mul m n) k) = vN (mul m (mul n k))` |
| 10 | `vN_mul_zero` | `(m : ℕ₀) → vN (mul m 𝟘) = vN 𝟘` |
| 11 | `vN_zero_mul` | `(m : ℕ₀) → vN (mul 𝟘 m) = vN 𝟘` |
| 12 | `vN_mul_one` | `(m : ℕ₀) → vN (mul m 𝟙) = vN m` |
| 13 | `vN_one_mul` | `(m : ℕ₀) → vN (mul 𝟙 m) = vN m` |
| 14 | `vN_mul_add` | `(m n k : ℕ₀) → vN (mul m (add n k)) = vN (add (mul m n) (mul m k))` |
| 15 | `vN_add_mul` | `(m n k : ℕ₀) → vN (mul (add m n) k) = vN (add (mul m k) (mul n k))` |

### 6.57 VN/CardVN.lean — `namespace VN`

**Imports:** `AczelSetTheory.VN.IsNat`
**Opens:** `Peano`, `VN`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `card_vN` | `(n : ℕ₀) : HFSet.card (vN n) = n` |

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

### VN/FSet.lean

`VN.fsetToHFSet`, `VN.fsetToHFSet_empty`, `VN.fsetToHFSet_singleton`,
`VN.mem_fsetToHFSet`, `VN.vN_mem_fsetToHFSet_iff`, `VN.fsetToHFSet_injective`

### VN/PeanoAxioms.lean

`VN.isNat_succ_ne_zero`, `VN.isNat_succ_injective`, `VN.isNat_induction`,
`VN.vN_zero_ne_succ`, `VN.vN_succ_injective_vN`, `VN.vN_induction`

### VN/PeanoArith.lean

`VN.addVN`, `VN.addVN_zero`, `VN.addVN_succ`, `VN.vN_add`,
`VN.vN_add_comm`, `VN.vN_add_assoc`, `VN.vN_add_zero`, `VN.vN_zero_add`,
`VN.vN_mul_comm`, `VN.vN_mul_assoc`, `VN.vN_mul_zero`, `VN.vN_zero_mul`,
`VN.vN_mul_one`, `VN.vN_one_mul`, `VN.vN_mul_add`, `VN.vN_add_mul`

### VN/CardVN.lean

`VN.card_vN`
