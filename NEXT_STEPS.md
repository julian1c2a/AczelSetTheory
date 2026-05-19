# Next Steps

**Last updated:** 2026-05-20

The project compiles on Lean 4.29.0 with **0 sorry, 114 non-barrel modules**.
Full Zermelo axioms derived. Architecture: CList/ + Operations/ + Axioms/ + PList/ + VN/ + Algebra/ + Integers/.
See PLANNING.md for the long-term roadmap.

---

## CURRENT PRIORITIES (2026-05-20)

### [B2-cont] Álgebra: Subgrupo, Homomorfismo, Anillo

Continuación de la cadena de álgebra nativa en HFSet:

- **`Algebra/Subgroup.lean`**: `HFSubgroup`, lema de Lagrange
- **`Algebra/GroupHom.lean`**: `HFGroupHom`, primer teorema de isomorfismo
- **`Algebra/Ring.lean`**: `HFRing` (o usar ℤ₀ como ejemplo concreto)

### [D] Funciones multiplicativas: μ de Möbius, λ de Liouville

Ahora que ℤ₀ funciona, se pueden transportar las funciones multiplicativas:

- `vN_mobius` (función de Möbius μ : ℕ₀ → ℤ₀)
- `vN_liouville` (función de Liouville λ : ℕ₀ → ℤ₀)

### [C] Plan y discusión ASet₁ antes de implementar

Antes de implementar, planear la arquitectura:

- Decisión `CList₁`: `mk : PList CList₁ → CList₁` | `inf : (HFSet → Bool) → CList₁`
- Definición de `extEq₁`, `normalize₁`, `ASet₁ = Quotient CList₁.Setoid`
- Qué infraestructura se reutiliza vs. se generaliza
- Cómo representar ω = `inf (fun _ => true)` y los conjuntos Δ⁰₁

---

## ✅ COMPLETED (2026-05-20) — Integers/Basic.lean: ℤ₀ como cociente

- **`Integers/Basic.lean`**: `ℤ₀ = Quotient intSetoid` donde `intEq (a,b) (c,d) ↔ a+d = b+c`.
  Representante canónico: `normalize p = if p.2 ≤ p.1 then (p.1-p.2, 0) else (0, p.2-p.1)`.
  Instancias: `Zero`, `One`, `Add`, `Neg`, `Mul`, `Sub`.
  18 leyes de anillo conmutativo (tipos escritos con `Add.add`/`Mul.mul` para evitar
  conflicto con la notación global Peano `notation a "+" b => Peano.Add.add a b`).
  Embedding: `ofNat : ℕ₀ → ℤ₀` inyectivo, `ofNat_add`, `ofNat_mul`.
  **0 sorry. Build ✅.**
- **Barrel fix**: `HFListOps.lean` añadido a `AczelSetTheory.lean` (era módulo huérfano).

---

## ✅ COMPLETED (2026-05-19) — Algebra/Group.lean + Axioms/LinearOrder.lean

- **`Algebra/Group.lean`** (`namespace HFAlgebra`): `HFGroup` con axiomas mínimos izquierdos
  (`op_assoc`, `op_id_left`, `op_inv_left`). 10 lemas derivados:
  `op_inv_left_apply`, `left_cancel`, `op_inv_right`, `op_id_right`, `right_cancel`,
  `inv_inv`, `inv_e`, `inv_op`, `unique_id`, `unique_inv`.
  Estrategia: idempotente `c·c=c` para probar `op_inv_right`; luego `right_cancel`.
- **`Axioms/LinearOrder.lean`**: `instance : LT HFSet` vía `CList.lt` en representantes
  canónicos; `instance : StrictLinearOrder HFSet` con `decLt`, `irrefl`, `trans`, `trich`.

---

## ✅ COMPLETED (2026-05-19) — Fase A: aritmética completa en HFSet

- **`VN/ModEqVN.lean`** (extendido): `ModEq_HF`, notación `≡ₕ [MODHF]`, 12 teoremas
  (`vN_modEq_refl/symm/trans/add/mul/pow`, `vN_mod_eq_zero_iff_dvd`, etc.)
- **`VN/TotientVN.lean`** (extendido): `vN_totient_le`, `vN_totient_pos` (total 6 teoremas)
- **`VN/PrimeVN.lean`** (nuevo): `dvd_HF`, `prime_HF`, `coprime_HF`; `vN_dvd/prime/coprime_iff`;
  `vN_prime_ne_zero/one`; **Lema de Gauss** (`vN_coprime_dvd_of_dvd_mul`);
  **TFA existencia** (`vN_exists_prime_factorization`);
  **TFA unicidad** (`vN_unique_prime_factorization`); 15 teoremas.
- **`VN/FermatVN.lean`** (nuevo): **Pequeño Teorema de Fermat** (`vN_fermat_little`,
  `vN_fermat_modEq`); **Teorema de Wilson** (`vN_wilson`, `vN_wilson_modEq`).
- **`VN/CRTVN.lean`** (nuevo): **Teorema Chino del Resto** (`vN_chinese_remainder`).

---

## ✅ COMPLETED (2026-05-19) — VN bridges

- **`VN/HFGroupVN.lean`**: `imageGroup : ℕ₀FinGroup → FinGroup HFSet`,
  transporte de `gpow`/`order` al tipo HFSet.
- **`VN/ProdBridgeVN.lean`**: `prodBridge : ℕ₀ × ℕ₀ → HFSet` vía par de Kuratowski.
- **`VN/MapBridgeVN.lean`**: `mapBridge : MapOn A B → HFSet` como grafo.
- **`VN/ListBridgeVN.lean`**: `listBridge : List ℕ₀ → HFSet` como grafo índice-valor.

---

## ✅ COMPLETED (2026-05-19) — VN grupos 1+2+3: transport completo

12 nuevos módulos VN (0 sorries, barrel actualizado a 35 módulos):

| Módulo | Peano source | Exporta |
| ------ | ----------- | ------- |
| `SummationVN` | `Combinatorics/Summation` | `finSumVN`, 8 teoremas |
| `SqrtVN` | `PeanoNat/Sqrt` | `sqrtVN`, `sqrtRemVN`, `csqrtVN`, 7 teoremas |
| `LogVN` | `PeanoNat/Log` | `logVN`, `logRemVN`, `clogVN`, 7 teoremas |
| `DigitsVN` | `PeanoNat/Digits` | `numDigitsVN`, `ofDigitsVN`, 4 teoremas |
| `ModEqVN` | `NumberTheory/ModEq` | `ModEq_HF`, 12 teoremas |
| `TotientVN` | `NumberTheory/Totient` | `totientVN`, 6 teoremas |
| `PrimesVN` | `PeanoNat/Primes` | `smallestDivisorVN` |
| `CantorPairingVN` | `Foundation/CantorPairing` | `pairVN`, `fstVN`, `sndVN`, 6 teoremas |
| `PairingVN` | `PeanoNat/Pairing` | `cantorPairVN`, 5 teoremas |
| `NewtonBinomVN` | `Combinatorics/NewtonBinom` | `binomTermVN`, 4 teoremas |
| `ProductVN` | `Combinatorics/Product` | `finProdVN`, 7 teoremas |
| `GodelBetaVN` | `Foundation/GodelBeta` | `betaVN`, `vN_beta_of_lt` |

---

## ✅ COMPLETED (2026-05-19) — B3: Order relation theory

- **`Operations/Order.lean`** (nuevo, 24 definiciones):
  `isReflexive`, `isIrreflexive`, `isSymmetric`, `isAntisymmetric`, `isTransitive`,
  `isConnected`, `isTotal`, `isTrichotomous`, `isPreorder`, `isEquivRel`,
  `isPartialOrder`, `isStrictOrder`, `isTotalOrder`, `isStrictTotalOrder`,
  `isMinimum`, `isMaximum`, `isMinimal`, `isMaximal`,
  `isLowerBound`, `isUpperBound`, `isInfimum`, `isSupremum`,
  `isWellFounded`, `isStrictlyWellFounded`, `isWellOrder`.
- **`Axioms/Order.lean`** (nuevo, ~28 teoremas):
  Cadena de implicaciones, casos vacíos (11), unicidad (4), minimal/maximal (3), restricción (13).
- **`Axioms/WellOrder.lean`** (nuevo, 4 teoremas):
  `wf_induction`, `minimum_in_nonempty`, `wo_induction`, `no_infinite_descent`.

---

## ✅ COMPLETED (2026-05-18) — B2: VN transport + HFList/FinList theory

- **`VN/GcdVN.lean`**: `gcdVN`, `lcmVN`, 13 teoremas.
- **`VN/FibVN.lean`**: `fibVN`, 4 teoremas.
- **`VN/BinomVN.lean`**: `binomVN`, 8 teoremas.
- **`HFList.lean`** (extendido): `FinList.append/map/zipWith/head/tail`, lemas de round-trip.
- **`HFListOps.lean`** (nuevo): `HFList.toHFSet`, `FinList.toHFSet`, `mem_toHFSet`.

---

## ✅ COMPLETED (2026-05-18) — B1: Axioms/Rank + VN/RankVN

- **`Axioms/Rank.lean`**: `rank : HFSet → ℕ₀`, `rank_empty`, `rank_insert`.
- **`VN/RankVN.lean`**: `rank_vN (n : ℕ₀) : rank (vN n) = n`.

---

## ✅ COMPLETED (2026-05-17) — A1/A2/A3/C1: VN arithmetic transport

- **`VN/PowVN.lean`**: `powVN`, 14 teoremas.
- **`VN/SubVN.lean`**: sustracción acotada, 12 teoremas.
- **`VN/DivVN.lean`**: división euclidiana, 6 teoremas.
- **`VN/FactorialVN.lean`**: `factVN`, 10 teoremas.

---

## ✅ COMPLETED — Phases 1–7g (all prior foundations)

All CList, PList, HFSet, Operations, Axioms, VN foundations complete.
See git log for details.
