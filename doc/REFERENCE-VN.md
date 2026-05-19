# Technical Reference — VN (von Neumann Embedding)

**Last updated:** 2026-05-18
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
| 79 | `AczelSetTheory/VN/PowVN.lean` | ✅ Complete |
| 80 | `AczelSetTheory/VN/SubVN.lean` | ✅ Complete |
| 81 | `AczelSetTheory/VN/DivVN.lean` | ✅ Complete |
| 82 | `AczelSetTheory/VN/FactorialVN.lean` | ✅ Complete |
| 84 | `AczelSetTheory/VN/RankVN.lean` | ✅ Complete |
| 85 | `AczelSetTheory/VN/GcdVN.lean` | ✅ Complete |
| 86 | `AczelSetTheory/VN/FibVN.lean` | ✅ Complete |
| 87 | `AczelSetTheory/VN/BinomVN.lean` | ✅ Complete |

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

#### 4.42.4 `VN.powVN` — `VN/PowVN.lean`

```lean
def VN.powVN (m n : ℕ₀) : HFSet := vN (m ^ n)
```

- **Math**: powVN(m, n) = vN(m^n) — imagen directa de la potenciación de Peano bajo vN.
- Computable, definitionally equal to `vN (m ^ n)`.
- Key theorem: `powVN_def : powVN m n = vN (m ^ n)` (`@[simp]`)

#### 4.42.5 `VN.factVN` — `VN/FactorialVN.lean`

```lean
def VN.factVN (n : ℕ₀) : HFSet := vN (factorial n)
```

- **Math**: factVN(n) = vN(n!) — imagen directa del factorial de Peano bajo vN.
- Requires `import Peano.PeanoNat.Combinatorics.Factorial`.
- Computable.
- Key theorem: `factVN_def : factVN n = vN (factorial n)`

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

### 6.59 VN/PowVN.lean — `namespace VN`

**Imports:** `AczelSetTheory.VN.PeanoArith`
**Opens:** `Peano`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `powVN_def` | `(m n : ℕ₀) : powVN m n = vN (m ^ n)` (`@[simp]`) |
| 2 | `powVN_zero` | `(m : ℕ₀) : powVN m 𝟘 = vN 𝟙` (`@[simp]`) |
| 3 | `powVN_succ` | `(m n : ℕ₀) : powVN m (σ n) = vN (mul (m ^ n) m)` (`@[simp]`) |
| 4 | `vN_pow` | `(m n : ℕ₀) : vN (m ^ n) = powVN m n` |
| 5 | `vN_pow_zero` | `(m : ℕ₀) : vN (m ^ 𝟘) = vN 𝟙` |
| 6 | `vN_pow_succ` | `(m n : ℕ₀) : vN (m ^ σ n) = vN (mul (m ^ n) m)` |
| 7 | `vN_pow_one` | `(m : ℕ₀) : vN (m ^ 𝟙) = vN m` |
| 8 | `vN_one_pow` | `(n : ℕ₀) : vN (𝟙 ^ n) = vN 𝟙` |
| 9 | `vN_zero_pow` | `{n : ℕ₀} (h : n ≠ 𝟘) : vN (𝟘 ^ n) = vN 𝟘` |
| 10 | `vN_pow_add` | `(m n k : ℕ₀) : vN (m ^ add n k) = vN (mul (m ^ n) (m ^ k))` |
| 11 | `vN_mul_pow` | `(m n k : ℕ₀) : vN (mul (m ^ k) (n ^ k)) = vN ((mul m n) ^ k)` |
| 12 | `vN_pow_pow` | `(m n k : ℕ₀) : vN ((m ^ n) ^ k) = vN (m ^ mul n k)` |
| 13 | `vN_pow_two` | `(m : ℕ₀) : vN (m ^ 𝟒) = vN (mul m m)` |
| 14 | `vN_pow_ne_zero` | `{m : ℕ₀} (h : m ≠ 𝟘) (n : ℕ₀) : vN (m ^ n) ≠ vN 𝟘` |

### 6.60 VN/SubVN.lean — `namespace VN`

**Imports:** `AczelSetTheory.VN.PeanoArith`
**Opens:** `Peano`, `Peano.Sub`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `vN_sub_zero` | `(n : ℕ₀) : vN (sub n 𝟘) = vN n` |
| 2 | `vN_zero_sub` | `(n : ℕ₀) : vN (sub 𝟘 n) = vN 𝟘` |
| 3 | `vN_sub_self` | `(n : ℕ₀) : vN (sub n n) = vN 𝟘` |
| 4 | `vN_succ_sub_one` | `(n : ℕ₀) : vN (sub (σ n) 𝟙) = vN n` |
| 5 | `vN_sub_succ_succ` | `(a b : ℕ₀) : vN (sub a b) = vN (sub (σ a) (σ b))` |
| 6 | `vN_add_k_sub_k` | `(n k : ℕ₀) : vN (sub (add k n) k) = vN n` |
| 7 | `vN_sub_k_add_k` | `(n k : ℕ₀) (h : le₀ k n) : vN (add (sub n k) k) = vN n` |
| 8 | `vN_add_sub_assoc` | `(n m k : ℕ₀) (h : le₀ k n) : vN (add (sub n k) m) = vN (sub (add n m) k)` |
| 9 | `sub_le_vN_self` | `(n m : ℕ₀) : le₀ (sub n m) n` |
| 10 | `sub_pos_of_lt_vN` | `{n m : ℕ₀} (h : lt₀ m n) : lt₀ 𝟘 (sub n m)` |
| 11 | `vN_succ_sub` | `(n m : ℕ₀) (h : le₀ (σ m) n) : vN (sub n (σ m)) = vN (τ (sub n m))` |
| 12 | `vN_sub_succ_left` | `(n k : ℕ₀) (h : le₀ k n) : vN (sub (σ n) k) = vN (σ (sub n k))` |

### 6.61 VN/DivVN.lean — `namespace VN`

**Imports:** `AczelSetTheory.VN.PeanoArith`
**Opens:** `Peano`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `vN_divMod_spec` | `(a b : ℕ₀) (h : b ≠ 𝟘) : vN a = vN (add (mul (div a b) b) (mod a b))` |
| 2 | `div_le_vN_self` | `(a b : ℕ₀) (h : b ≠ 𝟘) : le₀ (div a b) a` |
| 3 | `div_lt_vN_self` | `(a b : ℕ₀) (h_b : lt₀ 𝟙 b) (h_a : a ≠ 𝟘) : lt₀ (div a b) a` |
| 4 | `mod_lt_vN` | `(a b : ℕ₀) (h : b ≠ 𝟘) : lt₀ (mod a b) b` |
| 5 | `mod_of_lt_vN` | `(a b : ℕ₀) (h : lt₀ a b) : mod a b = a` |
| 6 | `div_of_lt_vN` | `(a b : ℕ₀) (h : lt₀ a b) : div a b = 𝟘` |

### 6.62 VN/FactorialVN.lean — `namespace VN`

**Imports:** `AczelSetTheory.VN.PeanoArith`, `Peano.PeanoNat.Combinatorics.Factorial`
**Opens:** `Peano`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `factVN_def` | `(n : ℕ₀) : factVN n = vN (factorial n)` |
| 2 | `vN_factorial_zero` | `vN (factorial 𝟘) = vN 𝟙` |
| 3 | `vN_factorial_one` | `vN (factorial 𝟙) = vN 𝟙` |
| 4 | `vN_factorial_two` | `vN (factorial 𝟒) = vN 𝟒` |
| 5 | `vN_factorial_succ` | `(n : ℕ₀) : vN (factorial (σ n)) = vN (mul (factorial n) (σ n))` |
| 6 | `vN_factorial_pos` | `(n : ℕ₀) : lt₀ 𝟘 (factorial n)` |
| 7 | `vN_factorial_ge_one` | `(n : ℕ₀) : le₀ 𝟙 (factorial n)` |
| 8 | `vN_factorial_ne_zero` | `(n : ℕ₀) : factVN n ≠ vN 𝟘` |
| 9 | `vN_factorial_mono` | `{m n : ℕ₀} (h : le₀ m n) : le₀ (factorial m) (factorial n)` |
| 10 | `vN_factorial_le_succ` | `(n : ℕ₀) : le₀ (factorial n) (factorial (σ n))` |

### 6.63 VN/RankVN.lean — `namespace VN`

**Imports:** `AczelSetTheory.VN.IsNat`
**Opens:** `Peano`, `VN`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `rank_vN` | `(n : ℕ₀) : HFSet.rank (vN n) = n` |

### 6.64 VN/GcdVN.lean — `namespace VN`

**Imports:** `AczelSetTheory.VN.PeanoArith`, `Peano.PeanoNat.Arith`
**Opens:** `Peano`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `gcdVN_def` | `(m n : ℕ₀) : gcdVN m n = vN (gcd m n)` |
| 2 | `lcmVN_def` | `(m n : ℕ₀) : lcmVN m n = vN (lcm m n)` |
| 3 | `vN_gcd_comm` | `(m n : ℕ₀) : vN (gcd m n) = vN (gcd n m)` |
| 4 | `vN_gcd_zero_right` | `(m : ℕ₀) : vN (gcd m 𝟘) = vN m` |
| 5 | `vN_gcd_zero_left` | `(m : ℕ₀) : vN (gcd 𝟘 m) = vN m` |
| 6 | `vN_gcd_one_right` | `(m : ℕ₀) : vN (gcd m 𝟙) = vN 𝟙` |
| 7 | `vN_gcd_one_left` | `(m : ℕ₀) : vN (gcd 𝟙 m) = vN 𝟙` |
| 8 | `vN_gcd_self` | `(m : ℕ₀) : vN (gcd m m) = vN m` |
| 9 | `vN_gcd_assoc` | `(m n k : ℕ₀) : vN (gcd (gcd m n) k) = vN (gcd m (gcd n k))` |
| 10 | `vN_gcd_mul_lcm` | `(m n : ℕ₀) : vN (mul (gcd m n) (lcm m n)) = vN (mul m n)` |
| 11 | `vN_lcm_comm` | `(m n : ℕ₀) : vN (lcm m n) = vN (lcm n m)` |
| 12 | `vN_lcm_zero_left` | `(m : ℕ₀) : vN (lcm 𝟘 m) = vN 𝟘` |
| 13 | `vN_lcm_zero_right` | `(m : ℕ₀) : vN (lcm m 𝟘) = vN 𝟘` |
| 14 | `vN_lcm_self` | `(m : ℕ₀) : vN (lcm m m) = vN m` |
| 15 | `gcdVN_ne_zero_left` | `{m n : ℕ₀} (hm : m ≠ 𝟘) : gcdVN m n ≠ vN 𝟘` |
| 16 | `gcdVN_ne_zero_right` | `{m n : ℕ₀} (hn : n ≠ 𝟘) : gcdVN m n ≠ vN 𝟘` |

### 6.65 VN/FibVN.lean — `namespace VN`

**Imports:** `AczelSetTheory.VN.PeanoArith`, `Peano.PeanoNat.Combinatorics.Fibonacci`
**Opens:** `Peano`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `fibVN_def` | `(n : ℕ₀) : fibVN n = vN (fib n)` |
| 2 | `vN_fib_zero` | `vN (fib 𝟘) = vN 𝟘` |
| 3 | `vN_fib_one` | `vN (fib 𝟙) = vN 𝟙` |
| 4 | `vN_fib_two` | `vN (fib 𝟚) = vN 𝟙` |
| 5 | `vN_fib_succ_succ` | `(n : ℕ₀) : vN (fib (σ (σ n))) = vN (add (fib n) (fib (σ n)))` |

### 6.66 VN/BinomVN.lean — `namespace VN`

**Imports:** `AczelSetTheory.VN.PeanoArith`, `Peano.PeanoNat.Combinatorics.Binom`
**Opens:** `Peano`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `binomVN_def` | `(n k : ℕ₀) : binomVN n k = vN (binom n k)` |
| 2 | `vN_binom_zero_zero` | `vN (binom 𝟘 𝟘) = vN 𝟙` |
| 3 | `vN_binom_zero_succ` | `(k : ℕ₀) : vN (binom 𝟘 (σ k)) = vN 𝟘` |
| 4 | `vN_binom_succ_zero` | `(n : ℕ₀) : vN (binom (σ n) 𝟘) = vN 𝟙` |
| 5 | `vN_binom_pascal` | `(n k : ℕ₀) : vN (binom (σ n) (σ k)) = vN (add (binom n k) (binom n (σ k)))` |
| 6 | `vN_binom_n_zero` | `(n : ℕ₀) : vN (binom n 𝟘) = vN 𝟙` |
| 7 | `vN_binom_n_one` | `(n : ℕ₀) : vN (binom n 𝟙) = vN n` |
| 8 | `vN_binom_self` | `(n : ℕ₀) : vN (binom n n) = vN 𝟙` |
| 9 | `vN_binom_eq_zero_gt` | `{n k : ℕ₀} (h : lt₀ n k) : vN (binom n k) = vN 𝟘` |

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

### VN/PowVN.lean

`VN.powVN`, `VN.powVN_def`, `VN.powVN_zero`, `VN.powVN_succ`,
`VN.vN_pow`, `VN.vN_pow_zero`, `VN.vN_pow_succ`, `VN.vN_pow_one`,
`VN.vN_one_pow`, `VN.vN_zero_pow`, `VN.vN_pow_add`, `VN.vN_mul_pow`,
`VN.vN_pow_pow`, `VN.vN_pow_two`, `VN.vN_pow_ne_zero`

### VN/SubVN.lean

`VN.vN_sub_zero`, `VN.vN_zero_sub`, `VN.vN_sub_self`, `VN.vN_succ_sub_one`,
`VN.vN_sub_succ_succ`, `VN.vN_add_k_sub_k`, `VN.vN_sub_k_add_k`,
`VN.vN_add_sub_assoc`, `VN.sub_le_vN_self`, `VN.sub_pos_of_lt_vN`,
`VN.vN_succ_sub`, `VN.vN_sub_succ_left`

### VN/DivVN.lean

`VN.vN_divMod_spec`, `VN.div_le_vN_self`, `VN.div_lt_vN_self`,
`VN.mod_lt_vN`, `VN.mod_of_lt_vN`, `VN.div_of_lt_vN`

### VN/FactorialVN.lean

`VN.factVN`, `VN.factVN_def`, `VN.vN_factorial_zero`, `VN.vN_factorial_one`,
`VN.vN_factorial_two`, `VN.vN_factorial_succ`, `VN.vN_factorial_pos`,
`VN.vN_factorial_ge_one`, `VN.vN_factorial_ne_zero`,
`VN.vN_factorial_mono`, `VN.vN_factorial_le_succ`

### VN/RankVN.lean

`VN.rank_vN`

### VN/GcdVN.lean

`VN.gcdVN`, `VN.lcmVN`, `VN.gcdVN_def`, `VN.lcmVN_def`,
`VN.vN_gcd_comm`, `VN.vN_gcd_zero_right`, `VN.vN_gcd_zero_left`,
`VN.vN_gcd_one_right`, `VN.vN_gcd_one_left`, `VN.vN_gcd_self`, `VN.vN_gcd_assoc`,
`VN.vN_gcd_mul_lcm`, `VN.vN_lcm_comm`, `VN.vN_lcm_zero_left`, `VN.vN_lcm_zero_right`,
`VN.vN_lcm_self`, `VN.gcdVN_ne_zero_left`, `VN.gcdVN_ne_zero_right`

### VN/FibVN.lean

`VN.fibVN`, `VN.fibVN_def`,
`VN.vN_fib_zero`, `VN.vN_fib_one`, `VN.vN_fib_two`, `VN.vN_fib_succ_succ`

### VN/BinomVN.lean

`VN.binomVN`, `VN.binomVN_def`,
`VN.vN_binom_zero_zero`, `VN.vN_binom_zero_succ`, `VN.vN_binom_succ_zero`,
`VN.vN_binom_pascal`, `VN.vN_binom_n_zero`, `VN.vN_binom_n_one`,
`VN.vN_binom_self`, `VN.vN_binom_eq_zero_gt`
