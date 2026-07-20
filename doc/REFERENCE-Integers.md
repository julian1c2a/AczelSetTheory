# Technical Reference — Integers `ℤ₀` / `ℤ₀cls` & Modular Arithmetic

**Last updated:** 2026-07-20 (ADR-023: nodo dedicado extraído de `REFERENCE-Arithmetic.md`;
los 14 módulos del subsistema `Integers/` proyectados al estándar §4/§6/§7 con firmas exactas;
renombrado `ℤ₀`/`ℤ₀cls`/`ℤ₀can` + capa struct completa)
**Parent:** [../REFERENCE.md](../REFERENCE.md)
**Related:** [REFERENCE-Arithmetic.md](REFERENCE-Arithmetic.md) | [REFERENCE-Rationals.md](REFERENCE-Rationals.md) | [REFERENCE-Algebra.md](REFERENCE-Algebra.md)

@axiom_system: AczelSetTheory
@importance: high

---

## Overview

Los enteros `ℤ` construidos sobre `ℕ₀` (peanolib), y ℤ/nℤ. Tras **ADR-023** hay tres
presentaciones, y el nombre titular lo lleva la estructura que usa el consumidor:

| Tipo | Rol |
| --- | --- |
| **`ℤ₀`** | **titular**: estructura que empaqueta `cls` + `pair` + su prueba de coherencia `hEq` |
| `ℤ₀cls` | la clase de equivalencia (`Quotient intSetoid`, con `intEq (a,b) (c,d) ↔ a+d = b+c`) |
| `ℤ₀can` | el par canónico normalizado (`{ p : ℕ₀ × ℕ₀ // p.1 = 𝟘 ∨ p.2 = 𝟘 }`) |

**Primary namespaces:** `ℤ₀`, `ℤ₀cls`, `ℤ₀can`, `HFAlgebra` (ZModN)

| # | File | Namespace | Status |
| --- | ------ | -------- | -------- |
| 97 | `AczelSetTheory/Integers/Basic.lean` | `ℤ₀cls` | ✅ Complete |
| 98 | `AczelSetTheory/Integers/Order.lean` | `ℤ₀cls` | ✅ Complete |
| 99 | `AczelSetTheory/Integers/Functions.lean` | `ℤ₀cls` | ✅ Complete |
| 100 | `AczelSetTheory/Integers/Arithmetic.lean` | `ℤ₀cls` | ✅ Complete |
| 101 | `AczelSetTheory/Integers/Bijection.lean` | `ℤ₀cls` | ✅ Complete |
| 102 | `AczelSetTheory/Integers/PadicVal.lean` | raíz (sobre `ℕ₀`) | ✅ Complete |
| 103 | `AczelSetTheory/Integers/MobiusLiouville.lean` | `ℤ₀cls` | ✅ Complete |
| 104 | `AczelSetTheory/Integers/Bezout.lean` | `ℤ₀cls` | ✅ Complete (0 sorry) |
| 104b | `AczelSetTheory/Integers/Canonical.lean` | `ℤ₀cls` | ✅ Complete (0 sorry) |
| 104c | `AczelSetTheory/Integers/Z0.lean` | `ℤ₀can`, `ℤ₀` | ✅ Complete |
| 104d | `AczelSetTheory/Integers/Z0Ops.lean` | `ℤ₀` | ✅ Complete |
| 104e | `AczelSetTheory/Integers/Z0Order.lean` | `ℤ₀` | ✅ Complete |
| 104f | `AczelSetTheory/Integers/Z0NumberTheory.lean` | `ℤ₀` | ✅ Complete |
| 109 | `AczelSetTheory/Integers/ZModN.lean` | `HFAlgebra` | ✅ Complete |

> **Regla (8)** — *nada que no esté probado entra en REFERENCE*. Todo el subsistema `Integers/`
> es **libre de `sorry`** (`sorryAx ∉ collectAxioms`, verificado por el gate exhaustivo
> `Meta/AxiomCheck.lean`, ADR-020). Los `bezout`/`bezout_coprime` generales de `ℤ₀cls` y los
> `canonicalRep_*`, que la documentación antigua marcaba como pendientes (M4B), están hoy cerrados.

## Jerarquía de Dependencias

```
-- capa de la clase ℤ₀cls --
Basic → Order → Functions ─┬→ Arithmetic
                            └→ Bijection
Basic → PadicVal → MobiusLiouville
Basic, Arithmetic, Order → Bezout
Basic → Canonical

-- capa del struct ℤ₀ (titular; empaqueta cls + par canónico) --
Basic, Canonical, Functions, Arithmetic, Bezout → Z0 → Z0Ops ─┬→ Z0Order
                                                               └→ Z0NumberTheory

-- ℤ/nℤ como HFRing/HFField finito --
Algebra/{Ring,Field}, VN/*, Peano.NumberTheory.{ModEq,Wilson} → ZModN
```

---

## 4. Definitions

### 4.97 Integers/Basic.lean — `namespace ℤ₀cls`

Los enteros como cociente `(ℕ₀ × ℕ₀) / intEq`.

```lean
def intEq (p q : ℕ₀ × ℕ₀) : Prop
def ℤ₀cls := Quotient intSetoid
abbrev mk (p : ℕ₀ × ℕ₀) : ℤ₀cls
def normalize (p : ℕ₀ × ℕ₀) : ℕ₀ × ℕ₀
def repr (z : ℤ₀cls) : ℕ₀ × ℕ₀
def negOne : ℤ₀cls
def ofNat (n : ℕ₀) : ℤ₀cls
def addRaw (p q : ℕ₀ × ℕ₀) : ℕ₀ × ℕ₀
def negRaw (p : ℕ₀ × ℕ₀) : ℕ₀ × ℕ₀
```

- **Math**: `intEq (a,b) (c,d)` ⟺ a+d = b+c · `mk p` = [p] · `normalize`/`repr` = representante canónico (un componente 𝟘) vía resta truncada · `negOne` = [(𝟘,𝟙)] = −1 · `ofNat n` = [(n,𝟘)] (embedding ℕ₀ ↪ ℤ) · `addRaw`/`negRaw` = ops sobre representantes.
- Computables. Instancias: `Zero`, `One`, `Add`, `Neg`, `Mul`, `Sub`, `DecidableEq` sobre `ℤ₀cls`.

### 4.98 Integers/Order.lean — `namespace ℤ₀cls`

Orden total de `ℤ₀cls` (las instancias `LE`/`LT` viven en `Basic`). Solo teoremas (§6.98).

### 4.99 Integers/Functions.lean — `namespace ℤ₀cls`

```lean
def sign (z : ℤ₀cls) : ℤ₀cls
def abs (z : ℤ₀cls) : ℤ₀cls
def toNat (z : ℤ₀cls) : ℕ₀
def succZ (z : ℤ₀cls) : ℤ₀cls
def predZ (z : ℤ₀cls) : ℤ₀cls
def powZ (z : ℤ₀cls) : ℕ₀ → ℤ₀cls
```

- **Math**: `sign z` ∈ {−1,0,1} · `abs z` = |z| · `toNat z` = z.repr.1 (parte positiva) · `succZ`/`predZ` = z±1 · `powZ z n` = zⁿ.
- Todas computables.

### 4.100 Integers/Arithmetic.lean — `namespace ℤ₀cls`

```lean
def divZ (a b : ℤ₀cls) : ℤ₀cls
def modZ (a b : ℤ₀cls) : ℤ₀cls
def gcdZ (a b : ℤ₀cls) : ℤ₀cls
def lcmZ (a b : ℤ₀cls) : ℤ₀cls
def isPrimeZ (z : ℤ₀cls) : Prop
```

- **Math**: división truncada, módulo, gcd/lcm (≥ 0), y `isPrimeZ z` = `Prime (toNat z)`.
- Computables.

### 4.101 Integers/Bijection.lean — `namespace ℤ₀cls`

```lean
def encode (z : ℤ₀cls) : ℕ₀
def decode (n : ℕ₀) : ℤ₀cls
```

- **Math**: biyección `ℤ₀cls ≃ ℕ₀` vía emparejamiento de Cantor sobre el representante.
- Computables.

### 4.102 Integers/PadicVal.lean — `namespace` raíz (sobre `ℕ₀`)

```lean
def padicVal (p n : ℕ₀) : ℕ₀
def squarefree (n : ℕ₀) : Prop
def Omega_prime (n : ℕ₀) : ℕ₀
```

- **Math**: `padicVal p n` = vₚ(n) (exponente de p en n) · `squarefree n` ⟺ ∀p primo, vₚ(n) ≤ 1 · `Omega_prime n` = Ω(n) (número de factores primos con multiplicidad).
- Computables; `padicVal`/`Omega_prime` con recursión bien fundada (`termination_by`).

### 4.103 Integers/MobiusLiouville.lean — `namespace ℤ₀cls`

```lean
def negOnePow (k : ℕ₀) : ℤ₀cls
def mobius (n : ℕ₀) : ℤ₀cls
def liouville (n : ℕ₀) : ℤ₀cls
```

- **Math**: `negOnePow k` = (−1)ᵏ · `mobius` = μ(n) (0 si no es libre de cuadrados, si no (−1)^Ω) · `liouville` = λ(n) = (−1)^Ω(n).
- Computables.

### 4.104 Integers/Bezout.lean — `namespace ℤ₀cls`

```lean
def extEuclidNat (a b : ℕ₀) : ℤ₀cls × ℤ₀cls
def bezoutCoeffs (a b : ℤ₀cls) : ℤ₀cls × ℤ₀cls
```

- **Math**: algoritmo extendido de Euclides (coeficientes en `ℤ₀cls`) y coeficientes de Bézout para enteros (por descomposición de signo).
- Computables (`extEuclidNat` con `termination_by b`).

### 4.104b Integers/Canonical.lean — `namespace ℤ₀cls`

```lean
def canonicalRep (p : ℕ₀ × ℕ₀) : ℕ₀ × ℕ₀
```

- **Math**: representante canónico `(p.1−p.2, 𝟘)` si p.2 ≤ p.1, si no `(𝟘, p.2−p.1)`.
- Computable.

### 4.104c Integers/Z0.lean — `namespace ℤ₀can` + `namespace ℤ₀`

El tipo entero **titular** `ℤ₀`, que empaqueta la clase, su representante canónico y la coherencia.

```lean
def ℤ₀can := { p : ℕ₀ × ℕ₀ // p.1 = 𝟘 ∨ p.2 = 𝟘 }
def ℤ₀can.ofCls (z : ℤ₀cls) : ℤ₀can        -- z ↦ z.repr
def ℤ₀can.toCls (p : ℤ₀can) : ℤ₀cls        -- p ↦ p.1 − p.2
structure ℤ₀ where
  cls  : ℤ₀cls
  pair : ℤ₀can
  hEq  : pair.val = cls.repr
def ℤ₀.ofCls (z : ℤ₀cls) : ℤ₀
def ℤ₀.ofCls' (p : ℤ₀can) : ℤ₀
def ℤ₀.negOne : ℤ₀
def ℤ₀.ofNat (n : ℕ₀) : ℤ₀
```

- **Math**: `ℤ₀` = clase + representante canónico + coherencia · `ofCls`/`ofCls'` construyen desde la clase o el par · `negOne` = −1 · `ofNat` = embedding ℕ₀ ↪ ℤ₀.
- **Subtipos** (con su `Coe … ℤ₀`): `NonZero` (ℤ₀^*), `Units` ({1,−1}), `Kernel` ({0,1,−1}), `OutKernel`, `Pos`, `Neg`, `NonNeg`.
- Instancias algebraicas de `ℤ₀can` y `ℤ₀`: `Zero`, `One`, `Add`, `Mul`, `Neg`, `Sub`, `LE`, `LT`
  (+ decidibles), la **coerción** `Coe ℕ₀ ℤ₀` (= `ofNat`) y la **olvidadiza** `Coe ℤ₀ ℤ₀cls` (= `.cls`).

### 4.104d Integers/Z0Ops.lean — `namespace ℤ₀`

```lean
def sign (a : ℤ₀) : ℤ₀            def abs (a : ℤ₀) : ℤ₀           def toNat (a : ℤ₀) : ℕ₀
def succ (a : ℤ₀) : ℤ₀           def pred (a : ℤ₀) : ℤ₀          def pow (a : ℤ₀) (n : ℕ₀) : ℤ₀
def div (a b : ℤ₀) : ℤ₀          def mod (a b : ℤ₀) : ℤ₀         def gcd (a b : ℤ₀) : ℤ₀
def lcm (a b : ℤ₀) : ℤ₀          def isPrime (a : ℤ₀) : Prop     def bezoutCoeffs (a b : ℤ₀) : ℤ₀ × ℤ₀
def gcdNatRight/gcdNatLeft/lcmNatRight/lcmNatLeft/bezoutCoeffsNatRight/bezoutCoeffsNatLeft (…)
```

- **Math**: todas `ofCls (ℤ₀cls.op …)` (o `toNat`/`isPrime` que aterrizan directamente); elevan la aritmética de `ℤ₀cls` al struct. Variantes `*Nat*` mezclan un argumento `ℕ₀`.
- Computables. Acompañadas del homomorfismo `.cls` `@[simp]` y los lemas de dominio (§6.104d).

### 4.104e Integers/Z0Order.lean — `namespace ℤ₀`

Anillo conmutativo **ordenado** `ℤ₀`. Sin defs; solo bridges de orden sobre `ℤ₀cls` (§6.104e).

### 4.104f Integers/Z0NumberTheory.lean — `namespace ℤ₀`

```lean
def negOnePow (k : ℕ₀) : ℤ₀      def mobius (n : ℕ₀) : ℤ₀       def liouville (n : ℕ₀) : ℤ₀
def encode (z : ℤ₀) : ℕ₀         def decode (n : ℕ₀) : ℤ₀
```

- **Math**: paridad con la teoría de números de `ℤ₀cls` (Möbius, Liouville) y la biyección `ℤ₀ ≃ ℕ₀`, empaquetadas sobre el struct.
- Computables. `mobius_sq` NO se proyecta: su `Decidable (squarefree)` es `private` en `MobiusLiouville`.

### 4.109 Integers/ZModN.lean — `namespace HFAlgebra`

```lean
def ZModN (n : ℕ₀) (hn : n ≠ 𝟘) : HFRing
def ZModFieldP (p : ℕ₀) (hp : Peano.Arith.Prime p) : HFField
```

- **Math**: ℤ/nℤ como `HFRing` finito sobre el ordinal de von Neumann `vN n` (ops módulo n vía puente `card`/`vN`); para p primo, `ZModFieldP` es el cuerpo con inverso `modInv` (Fermat/Wilson, ADR-016).
- Computables.

## 6. Theorems

### 6.97 Integers/Basic.lean — `namespace ℤ₀cls`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `mk_eq_iff` | `{p q : ℕ₀ × ℕ₀} : mk p = mk q ↔ intEq p q` |
| 2 | `add_mk` | `(p q : ℕ₀ × ℕ₀) : HAdd.hAdd (mk p) (mk q) = mk (addRaw p q)` |
| 3 | `neg_mk` | `(p : ℕ₀ × ℕ₀) : Neg.neg (mk p) = mk (negRaw p)` |
| 4 | `mul_mk` | `(p q : ℕ₀ × ℕ₀) : HMul.hMul (mk p) (mk q) = mk (mulRaw p q)` |
| 5 | `normalize_intEq` | `(p : ℕ₀ × ℕ₀) : add (normalize p).1 p.2 = add (normalize p).2 p.1` |
| 6 | `normalize_is_intEq` | `(p : ℕ₀ × ℕ₀) : intEq (normalize p) p` |
| 7 | `repr_mk` | `(p : ℕ₀ × ℕ₀) : repr (mk p) = normalize p` |
| 8 | `mk_repr` | `(a : ℤ₀cls) : mk a.repr = a` |
| 9 | `repr_normalized` | `(a : ℤ₀cls) : a.repr.1 = 𝟘 ∨ a.repr.2 = 𝟘` |
| 10 | `repr_inj` | `{a b : ℤ₀cls} (h : a.repr = b.repr) : a = b` |
| 11 | `repr_add_intEq` | `(a b : ℤ₀cls) : add (HAdd.hAdd a b).repr.1 (add a.repr.2 b.repr.2) = add (HAdd.hAdd a b).repr.2 (add a.repr.1 b.repr.1)` |
| 12 | `repr_neg_intEq` | `(a : ℤ₀cls) : add (Neg.neg a).repr.1 a.repr.1 = add (Neg.neg a).repr.2 a.repr.2` |
| 13 | `repr_ofNat` | `(n : ℕ₀) : (ofNat n).repr = (n, 𝟘)` |
| 14 | `add_comm` | `(a b : ℤ₀cls) : Add.add a b = Add.add b a` |
| 15 | `add_assoc` | `(a b c : ℤ₀cls) : Add.add (Add.add a b) c = Add.add a (Add.add b c)` |
| 16 | `zero_add` | `(a : ℤ₀cls) : Add.add 0 a = a` |
| 17 | `add_zero` | `(a : ℤ₀cls) : Add.add a 0 = a` |
| 18 | `add_neg_self` | `(a : ℤ₀cls) : Add.add a (Neg.neg a) = 0` |
| 19 | `neg_add_self` | `(a : ℤ₀cls) : Add.add (Neg.neg a) a = 0` |
| 20 | `neg_neg` | `(a : ℤ₀cls) : Neg.neg (Neg.neg a) = a` |
| 21 | `mul_comm` | `(a b : ℤ₀cls) : Mul.mul a b = Mul.mul b a` |
| 22 | `mul_assoc` | `(a b c : ℤ₀cls) : Mul.mul (Mul.mul a b) c = Mul.mul a (Mul.mul b c)` |
| 23 | `one_mul` | `(a : ℤ₀cls) : Mul.mul 1 a = a` |
| 24 | `mul_one` | `(a : ℤ₀cls) : Mul.mul a 1 = a` |
| 25 | `zero_mul` | `(a : ℤ₀cls) : Mul.mul 0 a = 0` |
| 26 | `mul_zero` | `(a : ℤ₀cls) : Mul.mul a 0 = 0` |
| 27 | `left_distrib` | `(a b c : ℤ₀cls) : Mul.mul a (Add.add b c) = Add.add (Mul.mul a b) (Mul.mul a c)` |
| 28 | `right_distrib` | `(a b c : ℤ₀cls) : Mul.mul (Add.add a b) c = Add.add (Mul.mul a c) (Mul.mul b c)` |
| 29 | `neg_mul` | `(a b : ℤ₀cls) : Mul.mul (Neg.neg a) b = Neg.neg (Mul.mul a b)` |
| 30 | `mul_neg` | `(a b : ℤ₀cls) : Mul.mul a (Neg.neg b) = Neg.neg (Mul.mul a b)` |
| 31 | `ofNat_zero` | `ofNat 𝟘 = 0` |
| 32 | `ofNat_one` | `ofNat 𝟙 = 1` |
| 33 | `ofNat_add` | `(m n : ℕ₀) : ofNat (Peano.Add.add m n) = Add.add (ofNat m) (ofNat n)` |
| 34 | `ofNat_mul` | `(m n : ℕ₀) : ofNat (Peano.Mul.mul m n) = Mul.mul (ofNat m) (ofNat n)` |
| 35 | `ofNat_injective` | `{m n : ℕ₀} (h : ofNat m = ofNat n) : m = n` |
| 36 | `mul_left_cancel_ofNat` | `{k : ℕ₀} (hk : k ≠ 𝟘) {x y : ℤ₀cls} (h : Mul.mul (ofNat k) x = Mul.mul (ofNat k) y) : x = y` |
| 37 | `repr_mul_ofNat_intEq` | `(a : ℤ₀cls) (k : ℕ₀) : Peano.Add.add (HMul.hMul a (ofNat k)).repr.1 (Peano.Mul.mul a.repr.2 k) = Peano.Add.add (HMul.hMul a (ofNat k)).repr.2 (Peano.Mul.mul a.repr.1 k)` |

### 6.98 Integers/Order.lean — `namespace ℤ₀cls`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `le_iff` | `(a b : ℤ₀cls) : a ≤ b ↔ Peano.Order.le₀ (Peano.Add.add a.repr.1 b.repr.2) (Peano.Add.add b.repr.1 a.repr.2)` |
| 2 | `le_refl` | `(a : ℤ₀cls) : a ≤ a` |
| 3 | `le_antisymm` | `{a b : ℤ₀cls} (h1 : a ≤ b) (h2 : b ≤ a) : a = b` |
| 4 | `le_trans` | `{a b c : ℤ₀cls} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c` |
| 5 | `le_total` | `(a b : ℤ₀cls) : a ≤ b ∨ b ≤ a` |
| 6 | `lt_iff_le_not_le` | `(a b : ℤ₀cls) : a < b ↔ a ≤ b ∧ ¬ b ≤ a` |
| 7 | `zero_le_ofNat` | `(n : ℕ₀) : (0 : ℤ₀cls) ≤ ofNat n` |
| 8 | `ofNat_le` | `{m n : ℕ₀} (h : (m : ℕ₀) ≤ n) : ofNat m ≤ ofNat n` |
| 9 | `le_ofNat_iff` | `{m n : ℕ₀} : ofNat m ≤ ofNat n ↔ (m : ℕ₀) ≤ n` |
| 10 | `ofNat_lt` | `{m n : ℕ₀} (h : (m : ℕ₀) ≤ n) (hne : m ≠ n) : ofNat m < ofNat n` |
| 11 | `add_le_add_left` | `(a b c : ℤ₀cls) (h : b ≤ c) : Add.add a b ≤ Add.add a c` |
| 12 | `add_le_add_right` | `{b c : ℤ₀cls} (h : b ≤ c) (a : ℤ₀cls) : Add.add b a ≤ Add.add c a` |
| 13 | `add_lt_add_left` | `(a b c : ℤ₀cls) (h : b < c) : Add.add a b < Add.add a c` |
| 14 | `add_lt_add_right` | `{b c : ℤ₀cls} (h : b < c) (a : ℤ₀cls) : Add.add b a < Add.add c a` |
| 15 | `neg_le_neg` | `{a b : ℤ₀cls} (h : a ≤ b) : -b ≤ -a` |
| 16 | `le_of_lt` | `{a b : ℤ₀cls} (h : a < b) : a ≤ b` |
| 17 | `lt_of_le_of_lt` | `{a b c : ℤ₀cls} (h1 : a ≤ b) (h2 : b < c) : a < c` |
| 18 | `lt_of_lt_of_le` | `{a b c : ℤ₀cls} (h1 : a < b) (h2 : b ≤ c) : a < c` |
| 19 | `mul_pos` | `{a b : ℤ₀cls} (ha : 0 < a) (hb : 0 < b) : 0 < Mul.mul a b` |
| 20 | `ofNat_pos_of_ne_zero` | `{n : ℕ₀} (hn : n ≠ 𝟘) : (0 : ℤ₀cls) < ofNat n` |
| 21 | `nonneg_eq_ofNat` | `{a : ℤ₀cls} (h : 0 ≤ a) : a = ofNat a.repr.1` |
| 22 | `mul_le_mul_right_ofNat_pos` | `{k : ℕ₀} (hk : k ≠ 𝟘) (a b : ℤ₀cls) : Mul.mul a (ofNat k) ≤ Mul.mul b (ofNat k) ↔ a ≤ b` |
| 23 | `mul_le_mul_left_ofNat_pos` | `{k : ℕ₀} (hk : k ≠ 𝟘) (a b : ℤ₀cls) : Mul.mul (ofNat k) a ≤ Mul.mul (ofNat k) b ↔ a ≤ b` |
| 24 | `mul_le_mul_right_of_nonneg` | `{a b c : ℤ₀cls} (h1 : a ≤ b) (h2 : 0 ≤ c) : Mul.mul a c ≤ Mul.mul b c` |
| 25 | `mul_le_mul_left_of_nonneg` | `{a b c : ℤ₀cls} (h1 : a ≤ b) (h2 : 0 ≤ c) : Mul.mul c a ≤ Mul.mul c b` |
| 26 | `mul_nonneg` | `{a b : ℤ₀cls} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ Mul.mul a b` |
| 27 | `mul_nonpos_of_nonneg_of_nonpos` | `{a b : ℤ₀cls} (ha : 0 ≤ a) (hb : b ≤ 0) : Mul.mul a b ≤ 0` |
| 28 | `mul_nonneg_of_nonpos_of_nonpos` | `{a b : ℤ₀cls} (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ Mul.mul a b` |

### 6.99 Integers/Functions.lean — `namespace ℤ₀cls`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `sign_zero` | `sign (0 : ℤ₀cls) = 0` |
| 2 | `sign_ofNat` | `(n : ℕ₀) (hn : n ≠ 𝟘) : sign (ofNat n) = 1` |
| 3 | `sign_neg` | `(z : ℤ₀cls) (hz : z < 0) : sign z = -1` |
| 4 | `abs_ofNat` | `(n : ℕ₀) : abs (ofNat n) = ofNat n` |
| 5 | `abs_nonneg` | `(z : ℤ₀cls) : 0 ≤ abs z` |
| 6 | `abs_neg` | `(z : ℤ₀cls) : abs (-z) = abs z` |
| 7 | `abs_eq_zero_iff` | `{z : ℤ₀cls} : abs z = 0 ↔ z = 0` |
| 8 | `toNat_ofNat` | `(n : ℕ₀) : toNat (ofNat n) = n` |
| 9 | `toNat_neg` | `(n : ℕ₀) : toNat (Neg.neg (ofNat n)) = 𝟘` |
| 10 | `succZ_pred` | `(z : ℤ₀cls) : predZ (succZ z) = z` |
| 11 | `predZ_succ` | `(z : ℤ₀cls) : succZ (predZ z) = z` |
| 12 | `powZ_zero` | `(z : ℤ₀cls) : powZ z 𝟘 = 1` |
| 13 | `powZ_succ` | `(z : ℤ₀cls) (n : ℕ₀) : powZ z (σ n) = Mul.mul (powZ z n) z` |
| 14 | `powZ_one` | `(z : ℤ₀cls) : powZ z 𝟙 = z` |
| 15 | `eq_ofNat_toNat_abs_or_neg` | `(a : ℤ₀cls) : a = ofNat (toNat (abs a)) ∨ a = Neg.neg (ofNat (toNat (abs a)))` |
| 16 | `ofNat_eq_neg_ofNat_implies_zero` | `(A C : ℕ₀) (h : ofNat A = - ofNat C) : A = 𝟘 ∧ C = 𝟘` |
| 17 | `peano_bound_eq` | `(a c : ℤ₀cls) (b d : ℕ₁) (h : Mul.mul a (ℤ₀cls.ofNat d.val) = Mul.mul c (ℤ₀cls.ofNat b.val)) : div (ℤ₀cls.toNat (ℤ₀cls.abs a)) b.val = div (ℤ₀cls.toNat (ℤ₀cls.abs c)) d.val` |

### 6.100 Integers/Arithmetic.lean — `namespace ℤ₀cls`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `divZ_zero_right` | `(z : ℤ₀cls) : divZ z 0 = 0` |
| 2 | `divZ_zero_left` | `(b : ℤ₀cls) : divZ 0 b = 0` |
| 3 | `gcdZ_comm` | `(a b : ℤ₀cls) : gcdZ a b = gcdZ b a` |
| 4 | `gcdZ_ofNat` | `(m n : ℕ₀) : gcdZ (ofNat m) (ofNat n) = ofNat (Peano.Arith.gcd m n)` |
| 5 | `gcdZ_zero_right` | `(n : ℕ₀) : gcdZ (ofNat n) 0 = ofNat n` |
| 6 | `gcdZ_zero_left` | `(n : ℕ₀) : gcdZ 0 (ofNat n) = ofNat n` |
| 7 | `lcmZ_comm` | `(a b : ℤ₀cls) : lcmZ a b = lcmZ b a` |
| 8 | `lcmZ_ofNat` | `(m n : ℕ₀) : lcmZ (ofNat m) (ofNat n) = ofNat (Peano.Arith.lcm m n)` |
| 9 | `isPrimeZ_ofNat` | `(n : ℕ₀) : isPrimeZ (ofNat n) ↔ Peano.Arith.Prime n` |

### 6.101 Integers/Bijection.lean — `namespace ℤ₀cls`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `ofNat_sub_repr` | `(z : ℤ₀cls) : Add.add (ofNat z.repr.1) (Neg.neg (ofNat z.repr.2)) = z` |
| 2 | `decode_encode` | `(z : ℤ₀cls) : decode (encode z) = z` |
| 3 | `encode_injective` | `{a b : ℤ₀cls} (h : encode a = encode b) : a = b` |

### 6.102 Integers/PadicVal.lean — `namespace` raíz

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `padicVal_zero_right` | `(p : ℕ₀) : padicVal p 𝟘 = 𝟘` |
| 2 | `padicVal_of_not_cond` | `{p n : ℕ₀} (h : ¬ (le₀ 𝟚 p ∧ n ≠ 𝟘 ∧ p ∣ n)) : padicVal p n = 𝟘` |
| 3 | `padicVal_succ_dvd` | `{p n : ℕ₀} (hp : le₀ 𝟚 p) (hn : n ≠ 𝟘) (hdvd : p ∣ n) : padicVal p n = σ (padicVal p (n / p))` |
| 4 | `padicVal_prime_self` | `{p : ℕ₀} (hp : Peano.Arith.Prime p) : padicVal p p = 𝟙` |
| 5 | `padicVal_prime_of_ndvd` | `{p q : ℕ₀} (hp : Prime p) (hq : Prime q) (hne : p ≠ q) : padicVal p q = 𝟘` |
| 6 | `squarefree_one` | `squarefree 𝟙` |
| 7 | `squarefree_prime` | `{p : ℕ₀} (hp : Peano.Arith.Prime p) : squarefree p` |
| 8 | `not_squarefree_prime_sq` | `{p : ℕ₀} (hp : Prime p) : ¬ squarefree (mul p p)` |
| 9 | `Omega_prime_zero` | `Omega_prime 𝟘 = 𝟘` |
| 10 | `Omega_prime_one` | `Omega_prime 𝟙 = 𝟘` |
| 11 | `Omega_prime_prime` | `{p : ℕ₀} (hp : Peano.Arith.Prime p) : Omega_prime p = 𝟙` |
| 12 | `Omega_prime_mul_prime` | `{m p : ℕ₀} (hp : Prime p) (hm : m ≠ 𝟘) : Omega_prime (Peano.Mul.mul m p) = σ (Omega_prime m)` |
| 13 | `Omega_prime_mul` | `{m n : ℕ₀} (hm : m ≠ 𝟘) (hn : n ≠ 𝟘) : Omega_prime (Peano.Mul.mul m n) = Peano.Add.add (Omega_prime m) (Omega_prime n)` |

### 6.103 Integers/MobiusLiouville.lean — `namespace ℤ₀cls`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `negOnePow_zero` | `negOnePow 𝟘 = 1` |
| 2 | `negOnePow_succ` | `(k : ℕ₀) : negOnePow (σ k) = Neg.neg (negOnePow k)` |
| 3 | `negOnePow_one` | `negOnePow 𝟙 = negOne` |
| 4 | `negOnePow_two` | `negOnePow 𝟚 = 1` |
| 5 | `negOnePow_add` | `(a b : ℕ₀) : negOnePow (Peano.Add.add a b) = Mul.mul (negOnePow a) (negOnePow b)` |
| 6 | `negOnePow_mul_self` | `(k : ℕ₀) : Mul.mul (negOnePow k) (negOnePow k) = 1` |
| 7 | `mobius_one` | `mobius 𝟙 = 1` |
| 8 | `liouville_one` | `liouville 𝟙 = 1` |
| 9 | `mobius_prime` | `{p : ℕ₀} (hp : Peano.Arith.Prime p) : mobius p = negOne` |
| 10 | `liouville_prime` | `{p : ℕ₀} (hp : Peano.Arith.Prime p) : liouville p = negOne` |
| 11 | `mobius_prime_sq` | `{p : ℕ₀} (hp : Prime p) : mobius (Peano.Mul.mul p p) = 0` |
| 12 | `liouville_sq` | `(n : ℕ₀) : Mul.mul (liouville n) (liouville n) = 1` |
| 13 | `liouville_ne_zero` | `(n : ℕ₀) : liouville n ≠ 0` |
| 14 | `mobius_eq_liouville_of_squarefree` | `{n : ℕ₀} (h : squarefree n) : mobius n = liouville n` |
| 15 | `mobius_sq` | `(n : ℕ₀) : Mul.mul (mobius n) (mobius n) = if squarefree n then 1 else 0` |
| 16 | `liouville_mul` | `{m n : ℕ₀} (hm : m ≠ 𝟘) (hn : n ≠ 𝟘) : liouville (Peano.Mul.mul m n) = Mul.mul (liouville m) (liouville n)` |
| 17 | `liouville_prime_pow` | `{p k : ℕ₀} (hp : Peano.Arith.Prime p) : liouville (Peano.Pow.pow p k) = negOnePow k` |

### 6.104 Integers/Bezout.lean — `namespace ℤ₀cls`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `bezout_ofNat` | `(a b : ℕ₀) : ∃ x y : ℤ₀cls, Add.add (Mul.mul (ofNat a) x) (Mul.mul (ofNat b) y) = ofNat (gcd a b)` |
| 2 | `bezout_coprime_ofNat` | `{a b : ℕ₀} (h : gcd a b = 𝟙) : ∃ x y : ℤ₀cls, Add.add (Mul.mul (ofNat a) x) (Mul.mul (ofNat b) y) = 1` |
| 3 | `bezout` | `(a b : ℤ₀cls) : ∃ x y : ℤ₀cls, Add.add (Mul.mul a x) (Mul.mul b y) = gcdZ a b` |
| 4 | `bezout_coprime` | `{a b : ℤ₀cls} (h : gcdZ a b = 1) : ∃ x y : ℤ₀cls, Add.add (Mul.mul a x) (Mul.mul b y) = 1` |
| 5 | `extEuclidNat_spec` | `(a b : ℕ₀) : Add.add (Mul.mul (ofNat a) (extEuclidNat a b).1) (Mul.mul (ofNat b) (extEuclidNat a b).2) = ofNat (Peano.Arith.gcd a b)` |

### 6.104b Integers/Canonical.lean — `namespace ℤ₀cls`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `canonicalRep_equiv` | `(p : ℕ₀ × ℕ₀) : intEq p (canonicalRep p)` |
| 2 | `canonicalRep_unique` | `{p q : ℕ₀ × ℕ₀} (h : intEq p q) : canonicalRep p = canonicalRep q` |
| 3 | `canonicalRep_idempotent` | `(p : ℕ₀ × ℕ₀) : canonicalRep (canonicalRep p) = canonicalRep p` — `@[simp]` |

### 6.104c Integers/Z0.lean — `namespace ℤ₀can` + `namespace ℤ₀`

Homomorfismo `@[simp]`: `cls_zero`, `cls_one`, `cls_negOne`, `cls_add`, `cls_mul`, `cls_neg`, `cls_sub`.

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `ℤ₀can.toCls_ofCls` | `(z : ℤ₀cls) : toCls (ofCls z) = z` |
| 2 | `ℤ₀can.ofCls_toCls` | `(p : ℤ₀can) : ofCls (toCls p) = p` |
| 3 | `ℤ₀can.add_comm` | `(a b : ℤ₀can) : Add.add a b = Add.add b a` |
| 4 | `ℤ₀can.add_assoc` | `(a b c : ℤ₀can) : Add.add (Add.add a b) c = Add.add a (Add.add b c)` |
| 5 | `ℤ₀.ofCls_cls` | `(z : ℤ₀cls) : (ofCls z).cls = z` |
| 6 | `ℤ₀.ext` | `(a b : ℤ₀) (h : a.cls = b.cls) : a = b` — `@[ext]` |
| 7 | `ℤ₀.add_comm` / `add_assoc` / `zero_add` / `add_zero` / `add_neg_self` / `neg_add_self` / `neg_neg` | leyes aditivas (firmas idénticas a §6.97, sobre `ℤ₀`) |
| 8 | `ℤ₀.mul_comm` / `mul_assoc` / `one_mul` / `mul_one` / `zero_mul` / `mul_zero` / `left_distrib` / `right_distrib` / `neg_mul` / `mul_neg` | leyes multiplicativas (sobre `ℤ₀`) |
| 9 | `ℤ₀.le_iff_cls` | `(a b : ℤ₀) : a ≤ b ↔ a.cls ≤ b.cls` |
| 10 | `ℤ₀.lt_iff_cls` | `(a b : ℤ₀) : a < b ↔ a.cls < b.cls` |

### 6.104d Integers/Z0Ops.lean — `namespace ℤ₀`

Homomorfismo `@[simp]`: `cls_ofNat`, `cls_sign`, `cls_abs`, `cls_succ`, `cls_pred`, `cls_pow`, `cls_div`, `cls_mod`, `cls_gcd`, `cls_lcm`, `toNat_eq_cls`. Puentes: `isPrime_iff_cls`, `eq_iff_cls`, `ne_zero_iff_cls`.

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `sign_zero` | `sign 0 = 0` |
| 2 | `sign_ofNat` | `(n : ℕ₀) (hn : n ≠ 𝟘) : sign (ofNat n) = 1` |
| 3 | `sign_neg` | `(a : ℤ₀) (ha : a < 0) : sign a = -1` |
| 4 | `abs_ofNat` | `(n : ℕ₀) : abs (ofNat n) = ofNat n` |
| 5 | `abs_nonneg` | `(a : ℤ₀) : 0 ≤ abs a` |
| 6 | `abs_neg` | `(a : ℤ₀) : abs (-a) = abs a` |
| 7 | `toNat_ofNat` | `(n : ℕ₀) : toNat (ofNat n) = n` |
| 8 | `toNat_neg` | `(n : ℕ₀) : toNat (- ofNat n) = 𝟘` |
| 9 | `succ_pred` | `(a : ℤ₀) : pred (succ a) = a` |
| 10 | `pred_succ` | `(a : ℤ₀) : succ (pred a) = a` |
| 11 | `pow_zero` | `(a : ℤ₀) : pow a 𝟘 = 1` |
| 12 | `pow_succ` | `(a : ℤ₀) (n : ℕ₀) : pow a (σ n) = Mul.mul (pow a n) a` |
| 13 | `pow_one` | `(a : ℤ₀) : pow a 𝟙 = a` |
| 14 | `div_zero_right` | `(a : ℤ₀) : div a 0 = 0` |
| 15 | `div_zero_left` | `(b : ℤ₀) : div 0 b = 0` |
| 16 | `gcd_comm` | `(a b : ℤ₀) : gcd a b = gcd b a` |
| 17 | `gcd_ofNat` | `(m n : ℕ₀) : gcd (ofNat m) (ofNat n) = ofNat (Peano.Arith.gcd m n)` |
| 18 | `gcd_zero_right` | `(n : ℕ₀) : gcd (ofNat n) 0 = ofNat n` |
| 19 | `gcd_zero_left` | `(n : ℕ₀) : gcd 0 (ofNat n) = ofNat n` |
| 20 | `lcm_comm` | `(a b : ℤ₀) : lcm a b = lcm b a` |
| 21 | `lcm_ofNat` | `(m n : ℕ₀) : lcm (ofNat m) (ofNat n) = ofNat (Peano.Arith.lcm m n)` |
| 22 | `isPrime_ofNat` | `(n : ℕ₀) : isPrime (ofNat n) ↔ Peano.Arith.Prime n` |
| 23 | `bezout` | `(a b : ℤ₀) : ∃ x y : ℤ₀, Add.add (Mul.mul a x) (Mul.mul b y) = gcd a b` |
| 24 | `bezout_coprime` | `{a b : ℤ₀} (h : gcd a b = 1) : ∃ x y : ℤ₀, Add.add (Mul.mul a x) (Mul.mul b y) = 1` |

### 6.104e Integers/Z0Order.lean — `namespace ℤ₀`

Bridges de orden (anillo conmutativo ordenado). Firmas paralelas a §6.98 pero sobre `ℤ₀`:
`le_refl`, `le_antisymm`, `le_trans`, `le_total`, `lt_iff_le_not_le`, `le_of_lt`,
`lt_of_le_of_lt`, `lt_of_lt_of_le`, `add_le_add_left`, `add_le_add_right`, `add_lt_add_left`,
`add_lt_add_right`, `neg_le_neg`, `mul_pos`, `mul_nonneg`, `mul_le_mul_right_of_nonneg`,
`mul_le_mul_left_of_nonneg` (17 lemas). Los de suma/producto usan `Add.add`/`Mul.mul` explícito.

### 6.104f Integers/Z0NumberTheory.lean — `namespace ℤ₀`

Homomorfismo `@[simp]`: `cls_negOnePow`, `cls_mobius`, `cls_liouville`, `encode_eq`, `cls_decode`.

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `abs_eq_zero_iff` | `{z : ℤ₀} : abs z = 0 ↔ z = 0` |
| 2 | `eq_ofNat_toNat_abs_or_neg` | `(a : ℤ₀) : a = ofNat (toNat (abs a)) ∨ a = Neg.neg (ofNat (toNat (abs a)))` |
| 3 | `negOnePow_zero` / `negOnePow_succ` / `negOnePow_one` / `negOnePow_two` / `negOnePow_add` / `negOnePow_mul_self` | (−1)ᵏ sobre `ℤ₀` (firmas paralelas a §6.103) |
| 4 | `mobius_one` / `mobius_prime` / `mobius_prime_sq` | Möbius sobre `ℤ₀` |
| 5 | `liouville_one` / `liouville_prime` / `liouville_sq` / `liouville_ne_zero` / `liouville_mul` / `liouville_prime_pow` | Liouville sobre `ℤ₀` |
| 6 | `mobius_eq_liouville_of_squarefree` | `{n : ℕ₀} (h : squarefree n) : mobius n = liouville n` |
| 7 | `decode_encode` | `(z : ℤ₀) : decode (encode z) = z` |
| 8 | `encode_injective` | `{a b : ℤ₀} (h : encode a = encode b) : a = b` |

### 6.109 Integers/ZModN.lean — `namespace HFAlgebra`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `ZModN_mul_comm` | `(n : ℕ₀) (hn : n ≠ 𝟘) (x y : HFSet) : (ZModN n hn).mul x y = (ZModN n hn).mul y x` |

## 7. Exports per Module

Fuente de verdad: las **declaraciones no-`private`** (AI-GUIDE §11-14, reformulada por ADR-021).
Ningún módulo lleva bloque `export` (nombres como `add`, `mul`, `gcd`, `sign`, `abs` colisionarían
con los alias a raíz de Peano y entre `ℤ₀`/`ℤ₀cls`).

- **Basic** (`ℤ₀cls`): `intEq`, `ℤ₀cls`, `mk`, `normalize`, `repr`, `negOne`, `ofNat`, `addRaw`, `negRaw`; instancias `Zero`/`One`/`Add`/`Neg`/`Mul`/`Sub`/`DecidableEq`; los 37 teoremas de §6.97.
- **Order** (`ℤ₀cls`): los 28 teoremas de §6.98.
- **Functions** (`ℤ₀cls`): `sign`, `abs`, `toNat`, `succZ`, `predZ`, `powZ`; los 17 teoremas de §6.99.
- **Arithmetic** (`ℤ₀cls`): `divZ`, `modZ`, `gcdZ`, `lcmZ`, `isPrimeZ`; los 9 teoremas de §6.100.
- **Bijection** (`ℤ₀cls`): `encode`, `decode`; los 3 teoremas de §6.101.
- **PadicVal** (raíz): `padicVal`, `squarefree`, `Omega_prime`; los 13 teoremas de §6.102.
- **MobiusLiouville** (`ℤ₀cls`): `negOnePow`, `mobius`, `liouville`; los 17 teoremas de §6.103.
- **Bezout** (`ℤ₀cls`): `extEuclidNat`, `bezoutCoeffs`; los 5 teoremas de §6.104.
- **Canonical** (`ℤ₀cls`): `canonicalRep`; los 3 teoremas de §6.104b.
- **Z0** (`ℤ₀can`, `ℤ₀`): tipo `ℤ₀` (struct) + `ℤ₀can`, `ofCls`/`ofCls'`/`toCls`/`negOne`/`ofNat`, subtipos `NonZero`/`Units`/`Kernel`/`OutKernel`/`Pos`/`Neg`/`NonNeg`; instancias algebraicas/decidibles y coerciones (`Coe ℕ₀ ℤ₀`, `Coe ℤ₀ ℤ₀cls`); teoremas de §6.104c.
- **Z0Ops** (`ℤ₀`): `sign`/`abs`/`toNat`/`succ`/`pred`/`pow`/`div`/`mod`/`gcd`/`lcm`/`isPrime`/`bezoutCoeffs` (+ variantes `*Nat*`); teoremas de §6.104d.
- **Z0Order** (`ℤ₀`): los 17 teoremas de §6.104e.
- **Z0NumberTheory** (`ℤ₀`): `negOnePow`, `mobius`, `liouville`, `encode`, `decode`; teoremas de §6.104f.
- **ZModN** (`HFAlgebra`): `ZModN`, `ZModFieldP`; `ZModN_mul_comm`.
