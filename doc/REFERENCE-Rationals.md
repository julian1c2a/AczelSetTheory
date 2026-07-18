# Technical Reference — Rationals `ℚ₀` / `ℚ₀cls` & Constructive Cauchy Analysis

**Last updated:** 2026-07-18 (ADR-023: migración del anexo legacy al estándar §4/§6/§7 — los
22 módulos del subsistema `Rationals/` + `Reals/` proyectados con firmas exactas; renombrado
`ℚ₀`/`ℚ₀cls`/`ℚ₀can`)
**Parent:** [../REFERENCE.md](../REFERENCE.md)
**Related:** [REFERENCE-Arithmetic.md](REFERENCE-Arithmetic.md) | [REFERENCE-Algebra.md](REFERENCE-Algebra.md) | [REFERENCE-Paridad-Peano-Aczel.md](REFERENCE-Paridad-Peano-Aczel.md)

@axiom_system: AczelSetTheory
@importance: high

---

## Overview

El cuerpo ordenado de los racionales y su análisis de Cauchy diádico constructivo. Tras
**ADR-023** hay tres presentaciones, y el nombre titular lo lleva la que usa el consumidor:

| Tipo | Rol |
| --- | --- |
| **`ℚ₀`** | **titular**: estructura que empaqueta `cls` + `pair` + su prueba de coherencia `hEq` |
| `ℚ₀cls` | la clase de equivalencia (`Quotient ratSetoid`) |
| `ℚ₀can` | el par canónico (coprimo) |

Aquí se pliega también el subsistema **`Reals/`** (`namespace ℝ₀`): son *propiedades sobre
`ℚ₀`* (la incompletitud métrica), **no** un tipo — el cociente `HFReal` aún no existe (es el
FRENTE 1 de [NEXT-STEPS.md](../NEXT-STEPS.md)). Tendrá nodo propio cuando exista.

**Primary namespaces:** `ℚ₀`, `ℚ₀cls`, `ℚ₀can`, `ℝ₀`

| # | File | Status |
| --- | ------ | -------- |
| 105 | `AczelSetTheory/Rationals/Basic.lean` | ✅ Complete |
| 106 | `AczelSetTheory/Rationals/AbsVal.lean` | ✅ Complete |
| 107 | `AczelSetTheory/Rationals/IsCauchy.lean` | ✅ Complete |
| 108 | `AczelSetTheory/Rationals/Density.lean` | 🚧 Skeleton (0 declaraciones) |
| 108b | `AczelSetTheory/Rationals/Inv.lean` | ✅ Complete |
| 108c | `AczelSetTheory/Rationals/Convergence.lean` | ✅ Complete |
| 108d | `AczelSetTheory/Rationals/Bisection.lean` | ✅ Complete |
| 108e | `AczelSetTheory/Rationals/Canonical.lean` | ✅ Complete |
| 108f | `AczelSetTheory/Rationals/PowOrder.lean` | ✅ Complete |
| 108g | `AczelSetTheory/Rationals/RationalLog.lean` | ✅ Complete |
| 108h | `AczelSetTheory/Rationals/Roots.lean` | ✅ Complete |
| 108i | `AczelSetTheory/Rationals/CauchySeqAlgebra.lean` | ✅ Complete |
| 108j | `AczelSetTheory/Rationals/Archimedean.lean` | ✅ Complete |
| 108k | `AczelSetTheory/Rationals/Irrational.lean` | 🚧 Progress — 24/27 teoremas proyectados (3 sorry: `newton_seq_step_bound`, `newton_seq_eventually_lt`, `newton_seq_apart_gt`) |
| 108l | `AczelSetTheory/Rationals/Q0.lean` | ✅ Complete |
| 108m | `AczelSetTheory/Rationals/Q0Ops.lean` | ✅ Complete |
| 108n | `AczelSetTheory/Rationals/Q0Cauchy.lean` | ✅ Complete |
| 108o | `AczelSetTheory/Rationals/Q0CauchyAlgebra.lean` | ✅ Complete (22/22 proyectados) |
| 108p | `AczelSetTheory/Rationals/MinAdd.lean` | ✅ Complete |
| 108q | `AczelSetTheory/Rationals/Series.lean` | 🚧 Progress — 3/11 proyectados (6 sorry) |
| 108r | `AczelSetTheory/Rationals/Polynomial.lean` | 🚧 Progress — 11/17 proyectados (4 sorry) |
| 108s | `AczelSetTheory/Reals/Incompleteness.lean` | 🚧 Progress — 1/5 proyectados (3 sorry) |

> **Regla (8)** — *nada que no esté probado entra en REFERENCE*. Los símbolos cuyo footprint
> contiene `sorryAx` (directa **o indirectamente**) **no se documentan aquí**: ni firma, ni
> entrada en tabla. El criterio es mecánico (`sorryAx ∉ collectAxioms(símbolo)`, comprobado con
> `#print axioms`), no sintáctico: p.ej. en `Irrational.lean` el `sorry` vive solo en
> `newton_seq_step_bound`, pero contamina también a `newton_seq_eventually_lt` y
> `newton_seq_apart_gt` (que lo invocan) — los tres se omiten; el resto del módulo (incluidos
> `newton_seq_telescope`, `newton_seq_anti` y `newton_seq_apart_lt`) es limpio y sí se proyecta.
> El inventario de los 14 `sorry` vive en
> [CURRENT-STATUS-PROJECT.md](../CURRENT-STATUS-PROJECT.md) §Known Sorry Locations y
> [NEXT-STEPS.md](../NEXT-STEPS.md) (fuente única).

## Jerarquía de Dependencias

```
Basic → AbsVal → Density
Basic → Inv → CauchySeqAlgebra
AbsVal, PowOrder → IsCauchy → Convergence → Bisection → Roots
Bisection → Archimedean → Irrational
Convergence → RationalLog
Canonical
Q0 → Q0Ops → Q0Cauchy → Q0CauchyAlgebra
Q0Ops → Series ; Q0 → Polynomial
Q0Cauchy, Irrational → Reals/Incompleteness
```

---

## 4. Definitions

### 4.105 Rationals/Basic.lean — `namespace ℚ₀cls`

Los racionales como cociente `(ℤ₀cls × ℕ₁) / ~`, con `ℕ₁` los positivos de peanolib.

```lean
def den1 : ℕ₁
def mulDen (b d : ℕ₁) : ℕ₁
def ℚ₀cls := Quotient ratSetoid
def mk (a : ℤ₀cls) (b : ℕ₁) : ℚ₀cls
def boundNat (q : ℚ₀cls) : ℕ₀
def ofInt (z : ℤ₀cls) : ℚ₀cls
def ofNat₀ (n : ℕ₀) : ℚ₀cls
```

- **Math**: `mk a b` = a/b · `ofInt z` = z/1 · `ofNat₀ n` = n/1 · `boundNat q` = un N con |q| ≤ N (= ⌊|num|/den⌋+1) · `mulDen` = b·d.
- Todas computables, sin `termination_by`.
- Instancias algebraicas: `Zero`, `One`, `Add`, `Neg`, `Mul`, `Sub`, `LE`, `LT` sobre `ℚ₀cls`,
  más las decidibles `DecidableEq`, `DecidableLE`, `DecidableLT`.

### 4.106 Rationals/AbsVal.lean — `namespace ℚ₀cls`

#### 4.106.1 `ℚ₀cls.absVal`

```lean
def absVal (q : ℚ₀cls) : ℚ₀cls := if 0 ≤ q then q else -q
```

- **Math**: |q|
- Computable (el `if` decide sobre `0 ≤ q`, que es `Decidable`).

### 4.107 Rationals/IsCauchy.lean — `namespace ℚ₀cls`

```lean
def pow2_den (n : ℕ₀) : ℕ₁
def pow2 (n : ℕ₀) : ℚ₀cls
def IsCauchy (f : ℕ₀ → ℚ₀cls) : Prop
def IsCauchy₂ (f : ℕ₀ → ℚ₀cls) : Prop
```

- **Math**: `pow2 n` = 1/2ⁿ (con `pow2_den n` = 2ⁿ el denominador) · `IsCauchy f` ⟺ ∀ n m, |f n − f m| ≤ 1/2^(min n m) · `IsCauchy₂ f` ⟺ ∀ n ≤ m, |f m − f n| ≤ 1/2ⁿ.
- Todas computables, sin `termination_by`.

### 4.108 Rationals/Density.lean — `namespace ℚ₀cls`

Esqueleto (0 declaraciones): reserva el nodo `midpoint`/densidad de `ℚ₀cls`, aún sin contenido probado. Nada que proyectar bajo la regla 8.

### 4.108b Rationals/Inv.lean — `namespace ℚ₀cls`

#### 4.108b.1 `ℚ₀cls.inv`

```lean
def inv (a : ℚ₀cls) : ℚ₀cls
```

- **Math**: q⁻¹ (= 1/q; `inv 0 = 0` por convención)
- Computable. Instancias: `Inv ℚ₀cls` (⟨inv⟩) y `Div ℚ₀cls` (a·b⁻¹).

### 4.108c Rationals/Convergence.lean — `namespace ℚ₀cls`

```lean
def IsBounded (f : ℕ₀ → ℚ₀cls) : Prop
def ConvergesTo (f : ℕ₀ → ℚ₀cls) (L : ℚ₀cls) : Prop
def IsConvergent (f : ℕ₀ → ℚ₀cls) : Prop
```

- **Math**: `IsBounded f` ⟺ ∃ M, ∀ n, |f n| ≤ M · `ConvergesTo f L` ⟺ ∀ n, |f n − L| ≤ 1/2^(n+1) · `IsConvergent f` ⟺ ∃ L, f → L.
- Computables, sin `termination_by`.

### 4.108d Rationals/Bisection.lean — `namespace ℚ₀cls`

#### 4.108d.1 `ℚ₀cls.bisectSeq`

```lean
def bisectSeq (g : ℕ₀ → ℚ₀cls → Bool) (a₀ : ℚ₀cls) : ℕ₀ → ℚ₀cls
```

- **Math**: bisección diádica dinámica; en el paso σn añade el bit 1/2^(n+1) si el decisor `g` lo aprueba.
- Computable, recursión estructural sobre `ℕ₀`.

### 4.108e Rationals/Canonical.lean — `namespace ℚ₀cls`

```lean
def reduce (p : ℤ₀cls × ℕ₁) : ℤ₀cls × ℕ₁
def repr : ℚ₀cls → ℤ₀cls × ℕ₁
def num (r : ℚ₀cls) : ℤ₀cls
def den (r : ℚ₀cls) : ℕ₁
```

- **Math**: `reduce (n,d)` = (sign n·(|n|/g), d/g) con g = gcd |n| d · `repr r` = representante canónico reducido · `num`/`den` = numerador (con signo) y denominador (positivo) canónicos.
- Computables, sin `termination_by`.

### 4.108g Rationals/RationalLog.lean — `namespace ℚ₀cls`

```lean
def oddIdx (j : ℕ₀) : ℕ₀
def artanhTerm (u : ℚ₀cls) (j : ℕ₀) : ℚ₀cls
def artanhSeq (u : ℚ₀cls) : ℕ₀ → ℚ₀cls
```

- **Math**: `oddIdx j` = 2j+1 · `artanhTerm u j` = u^(2j+1)/(2j+1) · `artanhSeq u k` = Σ_{j=0}^{k} u^(2j+1)/(2j+1) (sumas parciales de artanh).
- Computables, sin `termination_by`.

### 4.108h Rationals/Roots.lean — `namespace ℚ₀cls`

```lean
def pow (x : ℚ₀cls) : ℕ₀ → ℚ₀cls
def newton_raphson_step (q : ℚ₀cls) (n : Peano.ℕ₂) (x : ℚ₀cls) : ℚ₀cls
def newton_raphson_seq (q : ℚ₀cls) (n : Peano.ℕ₂) : ℕ₀ → ℚ₀cls
```

- **Math**: `pow x n` = xⁿ · `newton_raphson_step q n x` = (1/n)·((n−1)·x + q/x^(n−1)) (constante si q∈{0,1}) · `newton_raphson_seq q n` = iteración con semilla x₀ = q (aproxima ⁿ√q).
- Computables, recursión estructural.

### 4.108i Rationals/CauchySeqAlgebra.lean — `namespace ℚ₀cls`

Álgebra de sucesiones de Cauchy sobre la **clase** `ℚ₀cls` (contraparte de `ℚ₀` en 108o).

#### 4.108i.1 `ℚ₀cls.CauchySeq` y relación de equivalencia

```lean
def CauchySeq := { f : ℕ₀ → ℚ₀cls // ℚ₀cls.IsCauchy f }
def CauchySeq.Equiv (f g : CauchySeq) : Prop
```

- **Math**: sucesiones de Cauchy en `ℚ₀cls`; `f ∼ g` ⟺ ∀k ∃N ∀m≥N, |f(m)−g(m)| ≤ 2⁻ᵏ.

#### 4.108i.2 Operaciones de anillo y acotación

```lean
def CauchySeq.add (f g : CauchySeq) : CauchySeq
def CauchySeq.neg (f : CauchySeq) : CauchySeq
def CauchySeq.sub (f g : CauchySeq) : CauchySeq
def CauchySeq.IsBounded (f : CauchySeq) : Prop
def CauchySeq.boundVal (f : CauchySeq) : ℚ₀cls
def CauchySeq.mulBound (f g : CauchySeq) : ℕ₀
def CauchySeq.mul (f g : CauchySeq) : CauchySeq
```

- **Math**: (f+g)(n) = f(σn)+g(σn) · (−f)(n) = −f(n) · f−g = f+(−g) · `boundVal f` = 2⁰+|f(0)| · (f·g)(n) = f(n+K)·g(n+K) con K = `mulBound f g`.
- Instancias: `Add`, `Neg`, `Sub`, `Mul` sobre `CauchySeq`.

#### 4.108i.3 Orden constructivo (positividad y apartness)

```lean
structure CauchySeq.Pos (f : CauchySeq) where
  k     : ℕ₀
  N     : ℕ₀
  proof : ∀ m, Peano.Order.le₀ N m → ℚ₀cls.pow2 k ≤ f.val m
def CauchySeq.LT (f g : CauchySeq) : Prop
def CauchySeq.LE (f g : CauchySeq) : Prop
def CauchySeq.ApartZero (f : CauchySeq) : Type
def CauchySeq.ApartZero.k (f : CauchySeq) (h : CauchySeq.ApartZero f) : ℕ₀
def CauchySeq.ApartZero.N (f : CauchySeq) (h : CauchySeq.ApartZero f) : ℕ₀
```

- **Math**: `Pos f` = testigo constructivo de f ≫ 0 (cota 2⁻ᵏ superada desde N) · `f < g` ⟺ `Nonempty (Pos (g−f))` · `f ≤ g` ⟺ ¬(g < f) · `ApartZero f` = `Pos f ⊕ Pos (−f)` (f # 0, dato en `Type`) · `.k`/`.N` extraen el testigo.
- Instancias: `LT`, `LE` sobre `CauchySeq`.

#### 4.108i.4 Inverso y división (requieren apartness)

```lean
def CauchySeq.invBound (f : CauchySeq) (h : CauchySeq.ApartZero f) : ℕ₀
def CauchySeq.inv (f : CauchySeq) (h : CauchySeq.ApartZero f) : CauchySeq
def CauchySeq.div (f g : CauchySeq) (h : CauchySeq.ApartZero g) : CauchySeq
```

- **Math**: `invBound` = N+2k · (f⁻¹)(n) = (f(n+K))⁻¹ · f/g = f·g⁻¹. Definidos **solo** con testigo de apartness `g # 0`.

### 4.108k Rationals/Irrational.lean — `namespace ℤ₀cls` + `namespace ℚ₀cls`

```lean
def powN1 (b : ℕ₁) (n : ℕ₀) : ℕ₁
def pow_bound (x y : ℚ₀cls) : ℕ₀ → ℚ₀cls
```

- **Math**: `powN1 b n` = bⁿ como `ℕ₁` (denominador no nulo) · `pow_bound x y`: B₀=0, B_{σk} = x·Bₖ + yᵏ (factor de la identidad xⁿ−yⁿ = (x−y)·Bₙ).
- Computables. **Nota (regla 8)**: `newton_seq_step_bound`, `newton_seq_eventually_lt` y `newton_seq_apart_gt` **no se proyectan** (footprint con `sorryAx`).

### 4.108l Rationals/Q0.lean — `namespace ℤ₀` + `namespace ℚ₀can` + `namespace ℚ₀`

El tipo racional **titular** `ℚ₀`, que empaqueta la clase, su representante canónico y la coherencia.

#### 4.108l.1 Auxiliar sobre `ℤ₀` y par canónico `ℚ₀can`

```lean
def ℤ₀.absNat (a : ℤ₀) : ℕ₀ := ℤ₀cls.toNat (ℤ₀cls.abs a.cls)
def ℚ₀can := { p : ℤ₀ × ℕ₁ // (p.1 = 0 ∧ p.2.val = 𝟙) ∨ (p.1 ≠ 0 ∧ Peano.Arith.gcd (p.1.absNat) p.2.val = 𝟙) }
def ℚ₀can.ofCls (q : ℚ₀cls) : ℚ₀can
def ℚ₀can.toCls (p : ℚ₀can) : ℚ₀cls := ℚ₀cls.mk p.val.1.cls p.val.2
```

- **Math**: `ℚ₀can` = pares (num,den) reducidos (gcd=1) · `ℚ₀can.ofCls` reduce una clase a su representante · `ℚ₀can.toCls` reinterpreta el par como clase num/den.

#### 4.108l.2 La estructura `ℚ₀`

```lean
structure ℚ₀ where
  cls  : ℚ₀cls
  pair : ℚ₀can
  hEq  : ℚ₀can.toCls pair = cls
def ℚ₀.ofCls (q : ℚ₀cls) : ℚ₀
def ℚ₀.ofCls' (p : ℚ₀can) : ℚ₀
def ℚ₀.absVal (q : ℚ₀) : ℚ₀ := ofCls (ℚ₀cls.absVal q.cls)
```

- **Math**: `ℚ₀` = clase + representante canónico + prueba de coherencia · `ofCls`/`ofCls'` construyen desde la clase o el par · `absVal` = |q|.
- Instancias algebraicas de `ℚ₀can` y `ℚ₀`: `Zero`, `One`, `Add`, `Mul`, `Neg`, `Sub`, `LE`, `LT`
  (+ `DecidableEq`/`DecidableLE`/`DecidableLT`), y la **coerción olvidadiza** `Coe ℚ₀ ℚ₀cls` (= `.cls`).

#### 4.108l.3 Subtipos estructurados

```lean
def ℚ₀.NonZero  := { x : ℚ₀ // x ≠ 0 }
abbrev ℚ₀.Units := NonZero
def ℚ₀.Kernel    := { x : ℚ₀ // x = 0 ∨ x = 1 ∨ x = -1 }
def ℚ₀.OutKernel := { x : ℚ₀ // x ≠ 0 ∧ x ≠ 1 ∧ x ≠ -1 }
def ℚ₀.Pos    := { x : ℚ₀ // 0 < x }
def ℚ₀.Neg    := { x : ℚ₀ // x < 0 }
def ℚ₀.NonNeg := { x : ℚ₀ // 0 ≤ x }
def ℚ₀.PuncturedUnitBall := { x : ℚ₀ // 0 < absVal x ∧ absVal x < 1 }
def ℚ₀.OutsideBall       := { x : ℚ₀ // 1 < absVal x }
```

- **Math**: ℚ₀^*, unidades (= NonZero, por ser cuerpo), kernel {0,1,−1} y su complemento, estrictamente pos/neg, no negativos, y las bolas 0<|x|<1 / |x|>1. Cada uno con su `Coe … ℚ₀` (= `Subtype.val`).

### 4.108m Rationals/Q0Ops.lean — `namespace ℚ₀`

```lean
def ℚ₀.pow (a : ℚ₀) (n : ℕ₀) : ℚ₀
def ℚ₀.ofNat₀ (n : ℕ₀) : ℚ₀
def ℚ₀.ofInt (z : ℤ₀) : ℚ₀
```

- **Math**: aⁿ, y las inclusiones ℕ₀ ↪ ℚ₀ / ℤ₀ ↪ ℚ₀. Elevadas explícitamente desde `ℚ₀cls`.
- Computables. Instancias: `Inv ℚ₀`, `Div ℚ₀`.

### 4.108n Rationals/Q0Cauchy.lean — `namespace ℚ₀`

```lean
def pow2 (n : ℕ₀) : ℚ₀
def IsCauchy (f : ℕ₀ → ℚ₀) : Prop
def IsCauchy₂ (f : ℕ₀ → ℚ₀) : Prop
def toClsSeq (f : ℕ₀ → ℚ₀) : ℕ₀ → ℚ₀cls := fun n => (f n).cls
def CauchySeq := { f : ℕ₀ → ℚ₀ // IsCauchy f }
```

- **Math**: `pow2 n` = 2⁻ⁿ en `ℚ₀` · `IsCauchy`/`IsCauchy₂` = análogos sobre `ℚ₀` · `toClsSeq` proyecta n ↦ (f n).cls · `CauchySeq` = sucesiones de Cauchy en `ℚ₀`.
- Computables, sin `termination_by`.

### 4.108o Rationals/Q0CauchyAlgebra.lean — `namespace ℚ₀`

Álgebra de sucesiones de Cauchy en `ℚ₀` **sin usar cocientes**: las operaciones se definen
sobre la estructura y se transportan a `ℚ₀cls` vía `toClsCauchySeq`.

#### 4.108o.1 `ℚ₀.CauchySeq.Equiv`

```lean
def CauchySeq.Equiv (f g : CauchySeq) : Prop
```

- **Math**: f ≈ g ⟺ ∀k ∃N ∀m≥N, |f(m) − g(m)| ≤ 2⁻ᵏ
- Computable. Sin `termination_by`.

#### 4.108o.2 `ℚ₀.CauchySeq.ConvergesTo`

```lean
def CauchySeq.ConvergesTo (f : CauchySeq) (q : ℚ₀) : Prop
```

- **Math**: f → q ⟺ ∀k ∃N ∀m≥N, |f(m) − q| ≤ 2⁻ᵏ
- Computable.

#### 4.108o.3 `ℚ₀.toClsCauchySeq`

```lean
def toClsCauchySeq (f : CauchySeq) : ℚ₀cls.CauchySeq
```

- **Math**: transporte ℚ₀-CauchySeq ⟶ ℚ₀cls-CauchySeq (paso a clases)
- Computable.

#### 4.108o.4–8 Operaciones de anillo sobre `CauchySeq`

```lean
def CauchySeq.add (f g : CauchySeq) : CauchySeq
def CauchySeq.neg (f : CauchySeq) : CauchySeq
def CauchySeq.sub (f g : CauchySeq) : CauchySeq
def CauchySeq.mulBound (f g : CauchySeq) : ℕ₀
def CauchySeq.mul (f g : CauchySeq) : CauchySeq
```

- **Math**: (f+g)(n) = f(n)+g(n) · (−f)(n) = −f(n) · (f−g)(n) = f(n)−g(n) · (f·g)(n) = f(n)·g(n)
- Todas computables. `mulBound` es la cota común usada para probar que el producto es de Cauchy.
- Instancias: `Add CauchySeq`, `Neg CauchySeq`, `Sub CauchySeq`, `Mul CauchySeq` (vía `_root_`).

#### 4.108o.9 `ℚ₀.CauchySeq.Pos`

```lean
structure CauchySeq.Pos (f : CauchySeq) where
  k     : ℕ₀
  N     : ℕ₀
  proof : ∀ m, Peano.Order.le₀ N m → pow2 k ≤ f.val m
```

- **Math**: f ≫ 0 — testigo constructivo de positividad: una cota 2⁻ᵏ y un índice N a partir del cual f la supera.
- Estructura (dato, no Prop): es un **testigo**, no una proposición.

#### 4.108o.10 `ℚ₀.CauchySeq.ApartZero`

```lean
def CauchySeq.ApartZero (f : CauchySeq) : Type
```

- **Math**: f # 0 ⟺ (f ≫ 0) ⊎ (−f ≫ 0) — apartness constructiva del cero
- Computable. Devuelve `Type` (suma de testigos), no `Prop`: es la noción constructiva de «≠ 0».

#### 4.108o.11–12 Transporte de testigos

```lean
def toClsPos {f : CauchySeq} (p : CauchySeq.Pos f) : ℚ₀cls.CauchySeq.Pos (toClsCauchySeq f)
def toClsApartZero {f : CauchySeq} (h : CauchySeq.ApartZero f) : ℚ₀cls.CauchySeq.ApartZero (toClsCauchySeq f)
```

- Computables.

#### 4.108o.13–15 Inverso y división (requieren apartness)

```lean
def CauchySeq.invBound (f : CauchySeq) (h : CauchySeq.ApartZero f) : ℕ₀
def CauchySeq.inv (f : CauchySeq) (h : CauchySeq.ApartZero f) : CauchySeq
def CauchySeq.div (f g : CauchySeq) (h : CauchySeq.ApartZero g) : CauchySeq
```

- **Math**: f⁻¹ y f/g, definidos **solo** con testigo de apartness `g # 0` — no basta `¬(g = 0)`.
- Computables. `invBound` acota el denominador para garantizar Cauchy.

### 4.108q Rationals/Series.lean — `namespace ℚ₀cls` + `namespace ℚ₀`

```lean
def ℚ₀cls.sum (f : ℕ₀ → ℚ₀cls) : ℕ₀ → ℚ₀cls
def ℚ₀.sum (f : ℕ₀ → ℚ₀) (n : ℕ₀) : ℚ₀
```

- **Math**: Σᵢ₌₀ⁿ f(i) — suma parcial
- Computables, recursión estructural sobre `ℕ₀`, sin `termination_by`.

### 4.108r Rationals/Polynomial.lean — `namespace ℚ₀` + `namespace ℚ₀.Polynomial`

```lean
def trimZeros (l : PList ℚ₀) : PList ℚ₀
def Polynomial := { l : PList ℚ₀ // trimZeros l = l }
def Polynomial.zero : Polynomial
def Polynomial.degree (p : Polynomial) : ℕ₀
def Polynomial.addList  (l1 l2 : PList ℚ₀) : PList ℚ₀
def Polynomial.smulList (c : ℚ₀) (l : PList ℚ₀) : PList ℚ₀
def Polynomial.mulList  (l1 l2 : PList ℚ₀) : PList ℚ₀
def Polynomial.evalList (l : PList ℚ₀) (x : ℚ₀) : ℚ₀
def Polynomial.eval (p : Polynomial) (x : ℚ₀) : ℚ₀
def Polynomial.monomialList (c : ℚ₀) (k : ℕ₀) : PList ℚ₀
```

- **Math**: polinomio ≔ lista de coeficientes en forma normal (sin ceros a la cabeza);
  `eval p x` = Σᵢ cᵢ·xⁱ (Horner); `degree` = |coefs| − 1.
- Todas computables, recursión estructural, sin `termination_by`.
- Instancia: `Zero Polynomial`.
- **Nota**: `add`, `smul`, `mul`, `monomial` y las instancias `Add`/`Mul` **no se proyectan**:
  su componente-prueba de canonicalización es `sorry` (los 4 son la **misma** obligación —
  idempotencia de `trimZeros` — un solo lema los cerraría y liberaría también las 2 instancias).

### 4.108s Reals/Incompleteness.lean — `namespace ℝ₀`

```lean
def sqrt2Seq : ℕ₀ → ℚ₀
```

- **Math**: la sucesión de Newton–Raphson hacia √2 sobre `ℚ₀`
- Computable. Único símbolo del módulo libre de `sorry`.

## 6. Theorems

### 6.105 Rationals/Basic.lean — `namespace ℚ₀cls`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `mk_eq_iff` | `(a c : ℤ₀cls) (b d : ℕ₁) : mk a b = mk c d ↔ Mul.mul a (ℤ₀cls.ofNat d.val) = Mul.mul c (ℤ₀cls.ofNat b.val)` |
| 2 | `zero_def` | `(0 : ℚ₀cls) = mk 0 den1` |
| 3 | `one_def` | `(1 : ℚ₀cls) = mk 1 den1` |
| 4 | `mk_eq_zero_iff` | `{a : ℤ₀cls} {b : ℕ₁} : mk a b = 0 ↔ a = 0` |
| 5 | `add_mk` | `(a c : ℤ₀cls) (b d : ℕ₁) : Add.add (mk a b) (mk c d) = mk (Add.add (Mul.mul a (ℤ₀cls.ofNat d.val)) (Mul.mul c (ℤ₀cls.ofNat b.val))) (mulDen b d)` |
| 6 | `mul_mk` | `(a c : ℤ₀cls) (b d : ℕ₁) : Mul.mul (mk a b) (mk c d) = mk (Mul.mul a c) (mulDen b d)` |
| 7 | `ofNat₀_eq_mk` | `(n : ℕ₀) : ofNat₀ n = mk (ℤ₀cls.ofNat n) den1` |
| 8 | `add_comm` | `(a b : ℚ₀cls) : Add.add a b = Add.add b a` |
| 9 | `add_assoc` | `(a b c : ℚ₀cls) : Add.add (Add.add a b) c = Add.add a (Add.add b c)` |
| 10 | `zero_add` | `(a : ℚ₀cls) : Add.add 0 a = a` |
| 11 | `add_zero` | `(a : ℚ₀cls) : Add.add a 0 = a` |
| 12 | `add_neg_self` | `(a : ℚ₀cls) : Add.add a (Neg.neg a) = 0` |
| 13 | `neg_add_self` | `(a : ℚ₀cls) : Add.add (Neg.neg a) a = 0` |
| 14 | `mul_comm` | `(a b : ℚ₀cls) : a * b = b * a` |
| 15 | `mul_assoc` | `(a b c : ℚ₀cls) : a * b * c = a * (b * c)` |
| 16 | `one_mul` | `(a : ℚ₀cls) : 1 * a = a` |
| 17 | `mul_one` | `(a : ℚ₀cls) : a * 1 = a` |
| 18 | `zero_mul` | `(a : ℚ₀cls) : 0 * a = 0` |
| 19 | `mul_zero` | `(a : ℚ₀cls) : a * 0 = 0` |
| 20 | `left_distrib` | `(a b c : ℚ₀cls) : a * Add.add b c = Add.add (a * b) (a * c)` |
| 21 | `right_distrib` | `(a b c : ℚ₀cls) : Add.add a b * c = Add.add (a * c) (b * c)` |
| 22 | `neg_mul` | `(a b : ℚ₀cls) : Neg.neg a * b = Neg.neg (a * b)` |
| 23 | `mul_neg` | `(a b : ℚ₀cls) : a * Neg.neg b = Neg.neg (a * b)` |
| 24 | `mk_le_mk` | `(a c : ℤ₀cls) (b d : ℕ₁) : (mk a b ≤ mk c d) ↔ Mul.mul a (ℤ₀cls.ofNat d.val) ≤ Mul.mul c (ℤ₀cls.ofNat b.val)` |
| 25 | `ofNat₀_le_ofNat₀` | `{n m : ℕ₀} (h : Peano.Order.le₀ n m) : ofNat₀ n ≤ ofNat₀ m` |
| 26 | `le_refl` | `(a : ℚ₀cls) : a ≤ a` |
| 27 | `le_antisymm` | `{a b : ℚ₀cls} (h1 : a ≤ b) (h2 : b ≤ a) : a = b` |
| 28 | `le_trans` | `{a b c : ℚ₀cls} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c` |
| 29 | `le_total` | `(a b : ℚ₀cls) : a ≤ b ∨ b ≤ a` |
| 30 | `ofInt_injective` | `{a b : ℤ₀cls} (h : ofInt a = ofInt b) : a = b` |
| 31 | `neg_zero` | `Neg.neg (0 : ℚ₀cls) = 0` |
| 32 | `neg_neg` | `(q : ℚ₀cls) : Neg.neg (Neg.neg q) = q` |
| 33 | `neg_le_neg` | `{a b : ℚ₀cls} (h : a ≤ b) : Neg.neg b ≤ Neg.neg a` |
| 34 | `neg_add` | `(a b : ℚ₀cls) : Neg.neg (Add.add a b) = Add.add (Neg.neg a) (Neg.neg b)` |
| 35 | `zero_le_iff_num_nonneg` | `(p : ℤ₀cls × ℕ₁) : ((0 : ℚ₀cls) ≤ (mk p.1 p.2 : ℚ₀cls)) ↔ (0 : ℤ₀cls) ≤ p.1` |
| 36 | `mul_nonneg` | `{a b : ℚ₀cls} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b` |
| 37 | `mul_nonpos_of_nonneg_of_nonpos` | `{a b : ℚ₀cls} (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0` |
| 38 | `mul_nonneg_of_nonpos_of_nonpos` | `{a b : ℚ₀cls} (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b` |
| 39 | `add_le_add_left` | `{a b : ℚ₀cls} (h : a ≤ b) (c : ℚ₀cls) : Add.add c a ≤ Add.add c b` |
| 40 | `add_le_add_right` | `{a b : ℚ₀cls} (h : a ≤ b) (c : ℚ₀cls) : Add.add a c ≤ Add.add b c` |
| 41 | `add_le_add` | `{a b c d : ℚ₀cls} (h1 : a ≤ b) (h2 : c ≤ d) : Add.add a c ≤ Add.add b d` |
| 42 | `mul_le_mul_right_of_nonneg` | `{a b c : ℚ₀cls} (h1 : a ≤ b) (h2 : 0 ≤ c) : Mul.mul a c ≤ Mul.mul b c` |
| 43 | `mul_le_mul_left_of_nonneg` | `{a b c : ℚ₀cls} (h1 : a ≤ b) (h2 : 0 ≤ c) : Mul.mul c a ≤ Mul.mul c b` |
| 44 | `mul_le_mul` | `{a b c d : ℚ₀cls} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ a) (h4 : 0 ≤ c) : Mul.mul a c ≤ Mul.mul b d` |

### 6.106 Rationals/AbsVal.lean — `namespace ℚ₀cls`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `absVal_of_nonneg` | `{q : ℚ₀cls} (h : 0 ≤ q) : absVal q = q` |
| 2 | `absVal_of_nonpos` | `{q : ℚ₀cls} (h : q ≤ 0) : absVal q = -q` |
| 3 | `absVal_zero` | `absVal (0 : ℚ₀cls) = 0` |
| 4 | `absVal_nonneg` | `(q : ℚ₀cls) : 0 ≤ absVal q` |
| 5 | `absVal_idempotent` | `(q : ℚ₀cls) : absVal (absVal q) = absVal q` |
| 6 | `absVal_neg` | `(q : ℚ₀cls) : absVal (Neg.neg q) = absVal q` |
| 7 | `absVal_zero_iff` | `(q : ℚ₀cls) : absVal q = 0 ↔ q = 0` |
| 8 | `absVal_sub_comm` | `(a b : ℚ₀cls) : absVal (a - b) = absVal (b - a)` |
| 9 | `absVal_mul` | `(a b : ℚ₀cls) : absVal (a * b) = absVal a * absVal b` |
| 10 | `le_absVal` | `(q : ℚ₀cls) : q ≤ absVal q` |
| 11 | `neg_le_absVal` | `(q : ℚ₀cls) : Neg.neg q ≤ ℚ₀cls.absVal q` |
| 12 | `absVal_add_le` | `(a b : ℚ₀cls) : absVal (a + b) ≤ absVal a + absVal b` |
| 13 | `absVal_mul_sub_mul` | `(a b c d : ℚ₀cls) : absVal (a * b - c * d) ≤ Add.add (absVal a * absVal (b - d)) (absVal d * absVal (a - c))` |
| 14 | `le_div_add_one_mul` | `(a b : ℕ₀) (hb : b ≠ 𝟘) : le₀ a (mul (add (div a b) 𝟙) b)` |
| 15 | `le_abs_self` | `(z : ℤ₀cls) : z ≤ ℤ₀cls.abs z` |
| 16 | `neg_le_abs_self` | `(z : ℤ₀cls) : -z ≤ ℤ₀cls.abs z` |
| 17 | `le_boundNat` | `(q : ℚ₀cls) : absVal q ≤ ofNat₀ (boundNat q)` |

### 6.107 Rationals/IsCauchy.lean — `namespace ℚ₀cls`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `pow2_den_succ` | `(n : ℕ₀) : (pow2_den (σ n)).val = Peano.Mul.mul (pow2_den n).val (σ (σ 𝟘))` |
| 2 | `pow2_nonneg` | `(n : ℕ₀) : (0 : ℚ₀cls) ≤ pow2 n` |
| 3 | `pow2_succ_add` | `(n : ℕ₀) : Add.add (pow2 (σ n)) (pow2 (σ n)) = pow2 n` |
| 4 | `pow2_add` | `(n m : ℕ₀) : pow2 (Peano.Add.add n m) = Mul.mul (pow2 n) (pow2 m)` |
| 5 | `pow2_le_one` | `(k : ℕ₀) : pow2 k ≤ ofNat₀ 𝟙` |
| 6 | `pow2_ne_zero` | `(k : ℕ₀) : ℚ₀cls.pow2 k ≠ 0` |
| 7 | `pow2_bound` | `(K : ℕ₀) : Mul.mul (ofNat₀ K) (pow2 K) ≤ ofNat₀ 𝟙` |
| 8 | `isCauchy_iff_isCauchy₂` | `(f : ℕ₀ → ℚ₀cls) : IsCauchy f ↔ IsCauchy₂ f` |

### 6.108b Rationals/Inv.lean — `namespace ℚ₀cls`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `inv_mk` | `(a : ℤ₀cls) (b : ℕ₁) : (mk a b)⁻¹ = mk (invRaw (a, b)).1 (invRaw (a, b)).2` |
| 2 | `mul_inv_cancel` | `{q : ℚ₀cls} (h : q ≠ 0) : q * q⁻¹ = 1` |
| 3 | `inv_mul_cancel` | `{q : ℚ₀cls} (h : q ≠ 0) : q⁻¹ * q = 1` |
| 4 | `inv_unique` | `{x y : ℚ₀cls} (hx : x ≠ 0) (h : x * y = 1) : y = x⁻¹` |
| 5 | `one_ne_zero` | `(1 : ℚ₀cls) ≠ 0` |
| 6 | `inv_mul_inv` | `(x y : ℚ₀cls) (hx : x ≠ 0) (hy : y ≠ 0) : (x * y)⁻¹ = x⁻¹ * y⁻¹` |
| 7 | `inv_sub_inv_eq` | `(x y : ℚ₀cls) (hx : x ≠ 0) (hy : y ≠ 0) : x⁻¹ - y⁻¹ = (y - x) * (x * y)⁻¹` |
| 8 | `inv_nonneg` | `{x : ℚ₀cls} (hx : 0 ≤ x) (h_ne : x ≠ 0) : 0 ≤ x⁻¹` |
| 9 | `inv_le_one` | `{q : ℚ₀cls} (hq : 1 ≤ q) : q⁻¹ ≤ 1` |

### 6.108c Rationals/Convergence.lean — `namespace ℚ₀cls`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `pow2_step` | `(n : ℕ₀) : pow2 (σ n) ≤ pow2 n` |
| 2 | `pow2_add_le` | `(a d : ℕ₀) : pow2 (Peano.Add.add a d) ≤ pow2 a` |
| 3 | `pow2_le_of_le` | `{a b : ℕ₀} (h : Peano.Order.le₀ a b) : pow2 b ≤ pow2 a` |
| 4 | `isBounded_of_isCauchy` | `{f : ℕ₀ → ℚ₀cls} (h : IsCauchy f) : IsBounded f` |
| 5 | `isCauchy₂_of_convergesTo` | `{f : ℕ₀ → ℚ₀cls} {L : ℚ₀cls} (h : ConvergesTo f L) : IsCauchy₂ f` |
| 6 | `isCauchy_of_convergesTo` | `{f : ℕ₀ → ℚ₀cls} {L : ℚ₀cls} (h : ConvergesTo f L) : IsCauchy f` |
| 7 | `isCauchy_of_isConvergent` | `{f : ℕ₀ → ℚ₀cls} (h : IsConvergent f) : IsCauchy f` |
| 8 | `isBounded_of_convergesTo` | `{f : ℕ₀ → ℚ₀cls} {L : ℚ₀cls} (h : ConvergesTo f L) : IsBounded f` |
| 9 | `isBounded_of_isConvergent` | `{f : ℕ₀ → ℚ₀cls} (h : IsConvergent f) : IsBounded f` |
| 10 | `eq_zero_of_le_pow2_all` | `∀ {q : ℚ₀cls}, 0 ≤ q → (∀ n : ℕ₀, q ≤ pow2 n) → q = 0` |
| 11 | `convergesTo_unique` | `{f : ℕ₀ → ℚ₀cls} {L₁ L₂ : ℚ₀cls} (h1 : ConvergesTo f L₁) (h2 : ConvergesTo f L₂) : L₁ = L₂` |

### 6.108d Rationals/Bisection.lean — `namespace ℚ₀cls`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `isCauchy_of_dyadic_step` | `{f : ℕ₀ → ℚ₀cls} (h : ∀ k : ℕ₀, absVal (f (σ k) - f k) ≤ pow2 (σ k)) : IsCauchy f` |
| 2 | `bisectSeq_succ` | `(g : ℕ₀ → ℚ₀cls → Bool) (a₀ : ℚ₀cls) (n : ℕ₀) : bisectSeq g a₀ (σ n) = bif g n (bisectSeq g a₀ n) then Add.add (bisectSeq g a₀ n) (pow2 (σ n)) else bisectSeq g a₀ n` |
| 3 | `bisectSeq_isCauchy` | `(g : ℕ₀ → ℚ₀cls → Bool) (a₀ : ℚ₀cls) : IsCauchy (bisectSeq g a₀)` |

### 6.108e Rationals/Canonical.lean — `namespace ℚ₀cls`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `self_eq_sign_mul_toNat_abs` | `(z : ℤ₀cls) : z = Mul.mul (ℤ₀cls.sign z) (ℤ₀cls.ofNat (ℤ₀cls.toNat (ℤ₀cls.abs z)))` |
| 2 | `reduce_ratEq` | `(p : ℤ₀cls × ℕ₁) : Mul.mul p.1 (ℤ₀cls.ofNat (reduce p).2.val) = Mul.mul (reduce p).1 (ℤ₀cls.ofNat p.2.val)` |
| 3 | `reduce_reduced` | `(p : ℤ₀cls × ℕ₁) : Coprime (ℤ₀cls.toNat (ℤ₀cls.abs (reduce p).1)) (reduce p).2.val` |
| 4 | `reduce_unique` | `(p q : ℤ₀cls × ℕ₁) (h : Mul.mul p.1 (ℤ₀cls.ofNat q.2.val) = Mul.mul q.1 (ℤ₀cls.ofNat p.2.val)) : reduce p = reduce q` |
| 5 | `mk_repr` | `(r : ℚ₀cls) : mk (repr r).1 (repr r).2 = r` |
| 6 | `repr_inj` | `{a b : ℚ₀cls} (h : repr a = repr b) : a = b` |
| 7 | `repr_reduced` | `(r : ℚ₀cls) : Coprime (ℤ₀cls.toNat (ℤ₀cls.abs (repr r).1)) (repr r).2.val` |

### 6.108f Rationals/PowOrder.lean — `namespace ℚ₀cls`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `pow_zero` | `(x : ℚ₀cls) : pow x 𝟘 = 1` |
| 2 | `pow_succ` | `(x : ℚ₀cls) (n : ℕ₀) : pow x (σ n) = x * pow x n` |
| 3 | `pow_one` | `(x : ℚ₀cls) : pow x 𝟙 = x` |
| 4 | `pow_add` | `(x : ℚ₀cls) (m n : ℕ₀) : pow x (Peano.Add.add m n) = pow x m * pow x n` |
| 5 | `zero_le_one` | `(0 : ℚ₀cls) ≤ 1` |
| 6 | `pow_nonneg` | `{x : ℚ₀cls} (hx : 0 ≤ x) (n : ℕ₀) : 0 ≤ pow x n` |
| 7 | `pow_le_pow_left` | `{x y : ℚ₀cls} (hx : 0 ≤ x) (hxy : x ≤ y) (n : ℕ₀) : pow x n ≤ pow y n` |
| 8 | `one_le_pow` | `{x : ℚ₀cls} (hx : 1 ≤ x) (n : ℕ₀) : 1 ≤ pow x n` |
| 9 | `absVal_pow` | `(x : ℚ₀cls) (n : ℕ₀) : absVal (pow x n) = pow (absVal x) n` |

### 6.108g Rationals/RationalLog.lean — `namespace ℚ₀cls`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `pow2_zero` | `pow2 𝟘 = 1` |
| 2 | `pow_pow2_one` | `(m : ℕ₀) : pow (pow2 𝟙) m = pow2 m` |
| 3 | `pow_absVal_le_pow2` | `{u : ℚ₀cls} (hu : absVal u ≤ pow2 𝟙) (m : ℕ₀) : pow (absVal u) m ≤ pow2 m` |
| 4 | `oddIdx_ne_zero` | `(j : ℕ₀) : oddIdx j ≠ 𝟘` |
| 5 | `ofNat₀_ne_zero` | `{m : ℕ₀} (hm : m ≠ 𝟘) : ofNat₀ m ≠ 0` |
| 6 | `self_le_oddIdx` | `(j : ℕ₀) : Peano.Order.le₀ j (oddIdx j)` |
| 7 | `one_le_ofNat₀_oddIdx` | `(j : ℕ₀) : (1 : ℚ₀cls) ≤ ofNat₀ (oddIdx j)` |
| 8 | `artanhTerm_bound` | `{u : ℚ₀cls} (hu : absVal u ≤ pow2 𝟙) (k : ℕ₀) : absVal (artanhTerm u (σ k)) ≤ pow2 (σ k)` |
| 9 | `artanhSeq_step` | `{u : ℚ₀cls} (hu : absVal u ≤ pow2 𝟙) (k : ℕ₀) : absVal (artanhSeq u (σ k) - artanhSeq u k) ≤ pow2 (σ k)` |
| 10 | `artanhSeq_isCauchy` | `{u : ℚ₀cls} (hu : absVal u ≤ pow2 𝟙) : IsCauchy (artanhSeq u)` |

### 6.108h Rationals/Roots.lean — `namespace ℚ₀cls`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `ofNat₀_add` | `(n m : ℕ₀) : ofNat₀ (Peano.Add.add n m) = Add.add (ofNat₀ n) (ofNat₀ m)` |
| 2 | `ofNat₀_mul` | `(n m : ℕ₀) : ofNat₀ (Peano.Mul.mul n m) = Mul.mul (ofNat₀ n) (ofNat₀ m)` |
| 3 | `ofNat₀_nonneg` | `(n : ℕ₀) : (0:ℚ₀cls) ≤ ofNat₀ n` |
| 4 | `square_nonneg` | `(x : ℚ₀cls) : (0:ℚ₀cls) ≤ Mul.mul x x` |
| 5 | `le_add_of_nonneg_right` | `{a b : ℚ₀cls} (hb : 0 ≤ b) : a ≤ Add.add a b` |
| 6 | `bernoulli_ineq` | `(x : ℚ₀cls) (hx : (0:ℚ₀cls) ≤ Add.add (1:ℚ₀cls) x) (n : ℕ₀) : Add.add (1:ℚ₀cls) (Mul.mul (ofNat₀ n) x) ≤ pow (Add.add (1:ℚ₀cls) x) n` |
| 7 | `lt_of_le_of_ne` | `{a b : ℚ₀cls} (h_le : a ≤ b) (h_ne : a ≠ b) : a < b` |
| 8 | `pos_of_gt_zero` | `{a : ℚ₀cls} (h : 0 < a) : 0 ≤ a ∧ a ≠ 0` |
| 9 | `inv_ne_zero` | `{a : ℚ₀cls} (h : a ≠ 0) : a⁻¹ ≠ 0` |
| 10 | `inv_pos` | `{a : ℚ₀cls} (h : 0 < a) : 0 < a⁻¹` |
| 11 | `add_nonneg` | `{a b : ℚ₀cls} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ Add.add a b` |
| 12 | `eq_neg_of_add_eq_zero_pub` | `{x y : ℚ₀cls} (h : Add.add x y = 0) : x = -y` |
| 13 | `add_pos_of_nonneg_of_pos` | `{a b : ℚ₀cls} (ha : 0 ≤ a) (hb : 0 < b) : 0 < Add.add a b` |
| 14 | `add_pos` | `{a b : ℚ₀cls} (ha : 0 < a) (hb : 0 < b) : 0 < Add.add a b` |
| 15 | `eq_zero_of_mul_eq_zero` | `{a b : ℚ₀cls} (h : a * b = 0) (hb : b ≠ 0) : a = 0` |
| 16 | `mul_pos_pub` | `{a b : ℚ₀cls} (ha : 0 < a) (hb : 0 < b) : 0 < a * b` |
| 17 | `zero_lt_one` | `(0:ℚ₀cls) < 1` |
| 18 | `pow_pos` | `{x : ℚ₀cls} (k : ℕ₀) (hx : 0 < x) : 0 < pow x k` |
| 19 | `ofNat₀_inj_zero` | `{n : ℕ₀} (h : ofNat₀ n = 0) : n = 0` |
| 20 | `ofNat₀_pos` | `{k : ℕ₀} (hk : k ≠ 0) : 0 < ofNat₀ k` |
| 21 | `newton_seq_pos` | `(q : ℚ₀cls) (n : Peano.ℕ₂) (hq : 0 < q) (k : ℕ₀) : 0 < newton_raphson_seq q n k` |
| 22 | `le_of_add_le_add_right` | `{a b c : ℚ₀cls} (h : Add.add a c ≤ Add.add b c) : a ≤ b` |
| 23 | `le_add_right` | `(a b : ℚ₀cls) (hb : 0 ≤ b) : a ≤ Add.add a b` |
| 24 | `le_add_left` | `(a b : ℚ₀cls) (ha : 0 ≤ a) : b ≤ Add.add a b` |
| 25 | `le_of_lt` | `{a b : ℚ₀cls} (h : a < b) : a ≤ b` |
| 26 | `le_w_sq_add_one` | `{w : ℚ₀cls} (hw : 0 ≤ w) : w ≤ Add.add (Mul.mul w w) 1` |
| 27 | `bernoulli_ineq_alt2` | `(w : ℚ₀cls) (hw : 0 ≤ w) (n : ℕ₀) : Add.add (1:ℚ₀cls) (Mul.mul (ofNat₀ n) w) ≤ Add.add (pow w n) (ofNat₀ n)` |
| 28 | `one_pow` | `(n : ℕ₀) : pow (1:ℚ₀cls) n = (1:ℚ₀cls)` |
| 29 | `pow_ne_zero_of_pos` | `{x : ℚ₀cls} (hx : 0 < x) (n : ℕ₀) : pow x n ≠ 0` |
| 30 | `pow_mul_distrib` | `(a b : ℚ₀cls) (n : ℕ₀) : pow (Mul.mul a b) n = Mul.mul (pow a n) (pow b n)` |
| 31 | `pow_inv` | `(b : ℚ₀cls) (hb : 0 < b) (n : ℕ₀) : pow (inv b) n = inv (pow b n)` |
| 32 | `newton_seq_pow_ge` | `(q : ℚ₀cls) (n : Peano.ℕ₂) (hq : 0 < q) (k : ℕ₀) : q ≤ pow (newton_raphson_seq q n (σ k)) n.val.val` |
| 33 | `newton_seq_monotone` | `(q : ℚ₀cls) (n : Peano.ℕ₂) (hq : 0 < q) (k : ℕ₀) : newton_raphson_seq q n (σ (σ k)) ≤ newton_raphson_seq q n (σ k)` |
| 34 | `newton_seq_le_x1` | `(q : ℚ₀cls) (n : ℕ₂) (hq : 0 < q) (k : ℕ₀) : newton_raphson_seq q n (σ k) ≤ newton_raphson_seq q n 1` |

### 6.108i Rationals/CauchySeqAlgebra.lean — `namespace ℚ₀cls`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `CauchySeq.Equiv_refl` | `(f : CauchySeq) : CauchySeq.Equiv f f` |
| 2 | `CauchySeq.Equiv_symm` | `{f g : CauchySeq} (h : CauchySeq.Equiv f g) : CauchySeq.Equiv g f` |
| 3 | `CauchySeq.Equiv_trans` | `{f g h : CauchySeq} (h1 : CauchySeq.Equiv f g) (h2 : CauchySeq.Equiv g h) : CauchySeq.Equiv f h` |
| 4 | `CauchySeq.isBounded_of_isCauchy` | `(f : CauchySeq) : CauchySeq.IsBounded f` |
| 5 | `CauchySeq.boundVal_prop` | `(f : CauchySeq) (n : ℕ₀) : ℚ₀cls.absVal (f.val n) ≤ f.boundVal` |
| 6 | `cauchy_mul_is_cauchy` | `(f g : CauchySeq) (K : ℕ₀) (hK : CauchySeq.mulBound f g ≤ K) : ℚ₀cls.IsCauchy (fun n => f.val (Peano.Add.add n K) * g.val (Peano.Add.add n K))` |
| 7 | `ApartZero_absVal_bound` | `(f : CauchySeq) (h : CauchySeq.ApartZero f) (m : ℕ₀) (hm : Peano.Order.le₀ (CauchySeq.ApartZero.N f h) m) : ℚ₀cls.pow2 (CauchySeq.ApartZero.k f h) ≤ ℚ₀cls.absVal (f.val m)` |
| 8 | `mul_ne_zero` | `{x y : ℚ₀cls} (hx : x ≠ 0) (hy : y ≠ 0) : x * y ≠ 0` |
| 9 | `absVal_ne_zero` | `{x : ℚ₀cls} (hx : x ≠ 0) : ℚ₀cls.absVal x ≠ 0` |
| 10 | `absVal_one` | `ℚ₀cls.absVal 1 = 1` |
| 11 | `absVal_inv` | `(x : ℚ₀cls) (hx : x ≠ 0) : ℚ₀cls.absVal (x⁻¹) = (ℚ₀cls.absVal x)⁻¹` |
| 12 | `absVal_inv_sub_inv` | `(x y : ℚ₀cls) (hx : x ≠ 0) (hy : y ≠ 0) : ℚ₀cls.absVal (x⁻¹ - y⁻¹) = ℚ₀cls.absVal (y - x) * (ℚ₀cls.absVal x * ℚ₀cls.absVal y)⁻¹` |
| 13 | `inv_bound_lemma` | `(x y d p Z : ℚ₀cls) (hx : 0 ≤ x) (hy : 0 ≤ y) (_hd : 0 ≤ d) (hp : 0 ≤ p) (hZ_pos : 0 ≤ Z) (hZ_nz : Z ≠ 0) (h_Z_le : Z ≤ x * y) (h_diff : d ≤ p * Z) : d * (x * y)⁻¹ ≤ p` |
| 14 | `cauchy_inv_is_cauchy` | `(f : CauchySeq) (h : CauchySeq.ApartZero f) : ℚ₀cls.IsCauchy (fun n => (f.val (Peano.Add.add n (CauchySeq.invBound f h)))⁻¹)` |

### 6.108j Rationals/Archimedean.lean — `namespace` raíz (usa `open ℤ₀cls ℚ₀cls`)

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `le_ofNat_repr_fst` | `(a : ℤ₀cls) : a ≤ ofNat a.repr.1` |
| 2 | `int_not_le_zero_implies_ge_one` | `(a : ℤ₀cls) (h : ¬ a ≤ 0) : (1:ℤ₀cls) ≤ a` |
| 3 | `int_lt_add_of_pos` | `{a b : ℤ₀cls} (hb : 0 < b) : a < Add.add a b` |
| 4 | `int_lt_of_le_of_lt` | `{a b c : ℤ₀cls} (hab : a ≤ b) (hbc : b < c) : a < c` |
| 5 | `int_lt_of_lt_of_le` | `{a b c : ℤ₀cls} (hab : a < b) (hbc : b ≤ c) : a < c` |
| 6 | `int_zero_lt_one` | `(0:ℤ₀cls) < (1:ℤ₀cls)` |
| 7 | `archimedean_int` | `(p1 q1 : ℤ₀cls) (p2 q2 : ℕ₀) (hx : ¬ p1 ≤ 0) (hq2_ne : q2 ≠ 𝟘) : ∃ N : ℕ₀, ¬ Mul.mul (ofNat N) (Mul.mul p1 (ofNat q2)) ≤ Mul.mul q1 (ofNat p2)` |
| 8 | `archimedean` | `(x y : ℚ₀cls) : 0 < x → ∃ N : ℕ₀, y < Mul.mul (ofNat₀ N) x` |

### 6.108k Rationals/Irrational.lean — `namespace ℤ₀cls` + `namespace ℚ₀cls`

> Se omiten (regla 8, `sorryAx` en su footprint): `newton_seq_step_bound`,
> `newton_seq_eventually_lt`, `newton_seq_apart_gt`.

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `ℤ₀cls.int_sep_lemma` | `(x y : ℤ₀cls) (h : x ≠ y) : (1:ℤ₀cls) ≤ ℤ₀cls.abs (Sub.sub x y)` |
| 2 | `ℤ₀cls.int_sep_pow_lemma` | `(a b m : ℤ₀cls) (n : ℕ₀) (h : ℤ₀cls.powZ a n ≠ Mul.mul m (ℤ₀cls.powZ b n)) : (1:ℤ₀cls) ≤ ℤ₀cls.abs (Sub.sub (ℤ₀cls.powZ a n) (Mul.mul m (ℤ₀cls.powZ b n)))` |
| 3 | `powN1_zero` | `(b : ℕ₁) : powN1 b 𝟘 = den1` |
| 4 | `pow_mk` | `(a : ℤ₀cls) (b : ℕ₁) (n : ℕ₀) : pow (mk a b) n = mk (ℤ₀cls.powZ a n) (powN1 b n)` |
| 5 | `ofInt_eq_mk` | `(m : ℤ₀cls) : ofInt m = mk m den1` |
| 6 | `powZ_ofNat_eq` | `(b : ℕ₀) (n : ℕ₀) : ℤ₀cls.ofNat (Peano.Pow.pow b n) = ℤ₀cls.powZ (ℤ₀cls.ofNat b) n` |
| 7 | `rational_not_root` | `(a : ℤ₀cls) (b : ℕ₁) (m : ℤ₀cls) (n : ℕ₀) (h_irr : ∀ a' b', ℤ₀cls.powZ a' n ≠ Mul.mul m (ℤ₀cls.powZ (ℤ₀cls.ofNat b') n)) : pow (mk a b) n ≠ ofInt m` |
| 8 | `add_sub_cancel'` | `(x y : ℚ₀cls) : Add.add y (Sub.sub x y) = x` |
| 9 | `mul_assoc_mul` | `(a b c : ℚ₀cls) : Mul.mul (Mul.mul a b) c = Mul.mul a (Mul.mul b c)` |
| 10 | `mul_comm_mul` | `(a b : ℚ₀cls) : Mul.mul a b = Mul.mul b a` |
| 11 | `add_assoc_add` | `(a b c : ℚ₀cls) : Add.add (Add.add a b) c = Add.add a (Add.add b c)` |
| 12 | `add_comm_add` | `(a b : ℚ₀cls) : Add.add a b = Add.add b a` |
| 13 | `pow_sub_eq` | `(x y : ℚ₀cls) (n : ℕ₀) : pow x n = Add.add (pow y n) (Mul.mul (Sub.sub x y) (pow_bound x y n))` |
| 14 | `pow_nonneg` | `(y : ℚ₀cls) (hy : 0 ≤ y) (n : ℕ₀) : 0 ≤ pow y n` |
| 15 | `pow_bound_nonneg` | `(x y : ℚ₀cls) (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ₀) : 0 ≤ pow_bound x y n` |
| 16 | `pow_bound_mono` | `(x1 x2 y : ℚ₀cls) (hx1 : 0 ≤ x1) (hy : 0 ≤ y) (h : x1 ≤ x2) (n : ℕ₀) : pow_bound x1 y n ≤ pow_bound x2 y n` |
| 17 | `pow_bound_pos_succ` | `(x y : ℚ₀cls) (hx : 0 < x) (hy : 0 ≤ y) (k : ℕ₀) : 0 < pow_bound x y (σ k)` |
| 18 | `pow_bound_pos` | `(x y : ℚ₀cls) (hx : 0 < x) (hy : 0 ≤ y) (n : ℕ₀) (hn : n ≠ 0) : 0 < pow_bound x y n` |
| 19 | `sub_pos_of_lt` | `{a b : ℚ₀cls} (h : b < a) : 0 < Sub.sub a b` |
| 20 | `sub_nonneg_of_mul_nonneg` | `(A B c : ℚ₀cls) (hB : 0 ≤ B) (hc : 0 < c) (h_mul : c ≤ Mul.mul A B) : 0 ≤ A` |
| 21 | `newton_seq_apart_lt` | `(q r : ℚ₀cls) (n : ℕ₂) (hq : 0 < q) (hr : 0 ≤ r) (h : pow r n.val.val < q) : ∃ N : ℕ₀, ∃ δ > (0:ℚ₀cls), ∀ k, Peano.Order.le₀ N k → δ ≤ Sub.sub (newton_raphson_seq q n k) r` |
| 22 | `newton_seq_succ_le` | `(q : ℚ₀cls) (n : ℕ₂) (hq : 0 < q) (k : ℕ₀) (h1 : Peano.Order.le₀ 1 k) : newton_raphson_seq q n (σ k) ≤ newton_raphson_seq q n k` |
| 23 | `newton_seq_anti` | `(q : ℚ₀cls) (n : ℕ₂) (hq : 0 < q) (N k : ℕ₀) (h1 : Peano.Order.le₀ 1 N) (hk : Peano.Order.le₀ N k) : newton_raphson_seq q n k ≤ newton_raphson_seq q n N` |
| 24 | `newton_seq_telescope` | `(f : ℕ₀ → ℚ₀cls) (delta : ℚ₀cls) (_h_delta : 0 < delta) (h_step : ∀ k : ℕ₀, Peano.Order.le₀ 1 k → Add.add (f (σ k)) delta ≤ f k) : ∀ k : ℕ₀, Add.add (f (σ k)) (Mul.mul (ofNat₀ k) delta) ≤ f 1` |

### 6.108l Rationals/Q0.lean — `namespace ℚ₀can` + `namespace ℚ₀`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `ℚ₀can.toCls_ofCls` | `(q : ℚ₀cls) : toCls (ofCls q) = q` |
| 2 | `ℚ₀can.ofCls_toCls` | `(p : ℚ₀can) : ofCls (toCls p) = p` |
| 3 | `ℚ₀can.add_comm` | `(a b : ℚ₀can) : Add.add a b = Add.add b a` |
| 4 | `ℚ₀can.add_assoc` | `(a b c : ℚ₀can) : Add.add (Add.add a b) c = Add.add a (Add.add b c)` |
| 5 | `ℚ₀.gcd_eq_one_of_coprime` | `{a b : ℕ₀} (h : Peano.Arith.Coprime a b) : Peano.Arith.gcd a b = 𝟙` |
| 6 | `ℚ₀.div_one` | `(a : ℕ₀) : a / 𝟙 = a` |
| 7 | `ℚ₀.ext` | `(a b : ℚ₀) (h : a.cls = b.cls) : a = b` |
| 8 | `ℚ₀.add_comm` | `(a b : ℚ₀) : Add.add a b = Add.add b a` |
| 9 | `ℚ₀.add_assoc` | `(a b c : ℚ₀) : Add.add (Add.add a b) c = Add.add a (Add.add b c)` |
| 10 | `ℚ₀.zero_add` | `(a : ℚ₀) : Add.add 0 a = a` |
| 11 | `ℚ₀.add_zero` | `(a : ℚ₀) : Add.add a 0 = a` |
| 12 | `ℚ₀.add_neg_self` | `(a : ℚ₀) : Add.add a (Neg.neg a) = 0` |
| 13 | `ℚ₀.neg_add_self` | `(a : ℚ₀) : Add.add (Neg.neg a) a = 0` |
| 14 | `ℚ₀.mul_comm` | `(a b : ℚ₀) : Mul.mul a b = Mul.mul b a` |
| 15 | `ℚ₀.mul_assoc` | `(a b c : ℚ₀) : Mul.mul (Mul.mul a b) c = Mul.mul a (Mul.mul b c)` |
| 16 | `ℚ₀.one_mul` | `(a : ℚ₀) : Mul.mul 1 a = a` |
| 17 | `ℚ₀.mul_one` | `(a : ℚ₀) : Mul.mul a 1 = a` |
| 18 | `ℚ₀.zero_mul` | `(a : ℚ₀) : Mul.mul 0 a = 0` |
| 19 | `ℚ₀.mul_zero` | `(a : ℚ₀) : Mul.mul a 0 = 0` |
| 20 | `ℚ₀.left_distrib` | `(a b c : ℚ₀) : Mul.mul a (Add.add b c) = Add.add (Mul.mul a b) (Mul.mul a c)` |
| 21 | `ℚ₀.right_distrib` | `(a b c : ℚ₀) : Mul.mul (Add.add a b) c = Add.add (Mul.mul a c) (Mul.mul b c)` |
| 22 | `ℚ₀.neg_mul` | `(a b : ℚ₀) : Mul.mul (Neg.neg a) b = Neg.neg (Mul.mul a b)` |
| 23 | `ℚ₀.mul_neg` | `(a b : ℚ₀) : Mul.mul a (Neg.neg b) = Neg.neg (Mul.mul a b)` |
| 24 | `ℚ₀.cls_zero` | `(0 : ℚ₀).cls = 0` — `@[simp]` |
| 25 | `ℚ₀.cls_one` | `(1 : ℚ₀).cls = 1` — `@[simp]` |
| 26 | `ℚ₀.cls_add` | `(a b : ℚ₀) : (a + b).cls = a.cls + b.cls` — `@[simp]` |
| 27 | `ℚ₀.cls_mul` | `(a b : ℚ₀) : (a * b).cls = a.cls * b.cls` — `@[simp]` |
| 28 | `ℚ₀.cls_neg` | `(a : ℚ₀) : (-a).cls = -a.cls` — `@[simp]` |
| 29 | `ℚ₀.cls_sub` | `(a b : ℚ₀) : (a - b).cls = a.cls - b.cls` — `@[simp]` |
| 30 | `ℚ₀.le_iff_cls` | `(a b : ℚ₀) : a ≤ b ↔ a.cls ≤ b.cls` |
| 31 | `ℚ₀.lt_iff_cls` | `(a b : ℚ₀) : a < b ↔ a.cls < b.cls` |
| 32 | `ℚ₀.le_pair_iff` | `(a b : ℚ₀) : a ≤ b ↔ a.pair ≤ b.pair` |
| 33 | `ℚ₀.lt_pair_iff` | `(a b : ℚ₀) : a < b ↔ a.pair < b.pair` |

### 6.108n Rationals/Q0Cauchy.lean — `namespace ℚ₀`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `isCauchy_iff_q0_isCauchy` | `(f : ℕ₀ → ℚ₀) : IsCauchy f ↔ ℚ₀cls.IsCauchy (toClsSeq f)` |

### 6.108o Rationals/Q0CauchyAlgebra.lean — `namespace ℚ₀`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `toClsSeq_add` | `(f g : ℕ₀ → ℚ₀) : toClsSeq (fun n => f n + g n) = fun n => toClsSeq f n + toClsSeq g n` |
| 2 | `toClsSeq_neg` | `(f : ℕ₀ → ℚ₀) : toClsSeq (fun n => -f n) = fun n => -toClsSeq f n` |
| 3 | `toClsSeq_sub` | `(f g : ℕ₀ → ℚ₀) : toClsSeq (fun n => f n - g n) = fun n => toClsSeq f n - toClsSeq g n` |

### 6.108p Rationals/MinAdd.lean — `namespace Peano.Arith`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `min_add_add_right` | `(n m k : ℕ₀) : Lattice.min (Add.add n k) (Add.add m k) = Add.add (Lattice.min n m) k` |
| 2 | `min_add_add_left` | `(k n m : ℕ₀) : Lattice.min (Add.add k n) (Add.add k m) = Add.add k (Lattice.min n m)` |

### 6.108q Rationals/Series.lean — `namespace ℚ₀`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `cls_sum` | `(f : ℕ₀ → ℚ₀) (n : ℕ₀) : (sum f n).cls = ℚ₀cls.sum (fun i => (f i).cls) n` |

*(sin secciones 6.108r/6.108s: `Polynomial` e `Incompleteness` no tienen ningún teorema libre de `sorry`)*

## 7. Exports per Module

Estos módulos **no llevan bloque `export`**: por **ADR-021** el bloque es opcional y selectivo,
y solo procede con símbolos de **nombre único en el proyecto** — mientras que los de aquí
(`sum`, `add`, `mul`, `inv`, `pow`, `CauchySeq`, `add_comm`, `le_refl`…) son justamente los que
colisionarían con los alias a raíz de Peano y entre `ℚ₀`/`ℚ₀cls`. La fuente de verdad de esta
proyección son las **declaraciones no-`private`** (AI-GUIDE §11-14, reformulada por ADR-021).

### Rationals/Basic.lean — `ℚ₀cls`

Tipos/defs: `den1`, `mulDen`, `ℚ₀cls`, `mk`, `boundNat`, `ofInt`, `ofNat₀`.
Instancias: `Zero`, `One`, `Add`, `Neg`, `Mul`, `Sub`, `LE`, `LT`, `DecidableEq`, `DecidableLE`, `DecidableLT`.
Teoremas: los 44 de §6.105 (`mk_eq_iff`…`mul_le_mul`).

### Rationals/AbsVal.lean — `ℚ₀cls`

`absVal` (+ los 17 teoremas de §6.106, incl. `absVal_add_le`, `absVal_mul`, `absVal_zero_iff`, `le_boundNat`).

### Rationals/IsCauchy.lean — `ℚ₀cls`

`pow2_den`, `pow2`, `IsCauchy`, `IsCauchy₂` (+ los 8 teoremas de §6.107).

### Rationals/Density.lean — `ℚ₀cls`

(esqueleto — sin símbolos exportables)

### Rationals/Inv.lean — `ℚ₀cls`

`inv`, instancias `Inv`/`Div` (+ los 9 teoremas de §6.108b).

### Rationals/Convergence.lean — `ℚ₀cls`

`IsBounded`, `ConvergesTo`, `IsConvergent` (+ los 11 teoremas de §6.108c).

### Rationals/Bisection.lean — `ℚ₀cls`

`bisectSeq` (+ `isCauchy_of_dyadic_step`, `bisectSeq_succ`, `bisectSeq_isCauchy`).

### Rationals/Canonical.lean — `ℚ₀cls`

`reduce`, `repr`, `num`, `den` (+ los 7 teoremas de §6.108e).

### Rationals/PowOrder.lean — `ℚ₀cls`

(sin defs) los 9 teoremas de §6.108f (`pow_zero`…`absVal_pow`).

### Rationals/RationalLog.lean — `ℚ₀cls`

`oddIdx`, `artanhTerm`, `artanhSeq` (+ los 10 teoremas de §6.108g).

### Rationals/Roots.lean — `ℚ₀cls`

`pow`, `newton_raphson_step`, `newton_raphson_seq` (+ los 34 teoremas de §6.108h).

### Rationals/CauchySeqAlgebra.lean — `ℚ₀cls`

`CauchySeq` (+ `.Equiv`, `.add`, `.neg`, `.sub`, `.IsBounded`, `.boundVal`, `.mulBound`, `.mul`,
`.Pos`, `.LT`, `.LE`, `.ApartZero`(`.k`/`.N`), `.invBound`, `.inv`, `.div`), instancias
`Add`/`Neg`/`Sub`/`Mul`/`LT`/`LE`, + los 14 teoremas de §6.108i.

### Rationals/Archimedean.lean — raíz (`open ℤ₀cls ℚ₀cls`)

Los 8 teoremas de §6.108j (`le_ofNat_repr_fst`…`archimedean`).

### Rationals/Irrational.lean — `ℤ₀cls` + `ℚ₀cls`

`powN1`, `pow_bound` (+ los 24 teoremas limpios de §6.108k).
**No exportables** (regla 8): `newton_seq_step_bound`, `newton_seq_eventually_lt`, `newton_seq_apart_gt`.

### Rationals/Q0.lean — `ℤ₀` + `ℚ₀can` + `ℚ₀`

`ℤ₀.absNat`, `ℚ₀can` (`.ofCls`, `.toCls`), `ℚ₀` (struct: `.cls`, `.pair`, `.hEq`), `ℚ₀.ofCls`,
`ℚ₀.ofCls'`, `ℚ₀.absVal`, subtipos `NonZero`/`Units`/`Kernel`/`OutKernel`/`Pos`/`Neg`/`NonNeg`/
`PuncturedUnitBall`/`OutsideBall`; instancias algebraicas y decidibles de `ℚ₀can`/`ℚ₀`, coerciones
de subtipos y `Coe ℚ₀ ℚ₀cls`; + los 33 teoremas de §6.108l.

### Rationals/Q0Ops.lean — `ℚ₀`

`ℚ₀.pow`, `ℚ₀.ofNat₀`, `ℚ₀.ofInt`, instancias `Inv`/`Div` (sin teoremas).

### Rationals/Q0Cauchy.lean — `ℚ₀`

`pow2`, `IsCauchy`, `IsCauchy₂`, `toClsSeq`, `CauchySeq` (+ `isCauchy_iff_q0_isCauchy`).

### Rationals/Q0CauchyAlgebra.lean — `ℚ₀`

`ℚ₀.CauchySeq.Equiv`, `ℚ₀.CauchySeq.ConvergesTo`, `ℚ₀.toClsCauchySeq`, `ℚ₀.toClsSeq_add`,
`ℚ₀.toClsSeq_neg`, `ℚ₀.toClsSeq_sub`, `ℚ₀.CauchySeq.add`, `ℚ₀.CauchySeq.neg`,
`ℚ₀.CauchySeq.sub`, `ℚ₀.CauchySeq.mulBound`, `ℚ₀.CauchySeq.mul`, `ℚ₀.CauchySeq.Pos`,
`ℚ₀.CauchySeq.ApartZero`, `ℚ₀.toClsPos`, `ℚ₀.toClsApartZero`, `ℚ₀.CauchySeq.invBound`,
`ℚ₀.CauchySeq.inv`, `ℚ₀.CauchySeq.div` (+ instancias `Add`/`Neg`/`Sub`/`Mul`)

### Rationals/MinAdd.lean — `Peano.Arith`

`min_add_add_right`, `min_add_add_left`.

### Rationals/Series.lean — `ℚ₀cls` + `ℚ₀`

`ℚ₀cls.sum`, `ℚ₀.sum`, `ℚ₀.cls_sum`

### Rationals/Polynomial.lean — `ℚ₀`

`ℚ₀.trimZeros`, `ℚ₀.Polynomial`, `ℚ₀.Polynomial.zero`, `ℚ₀.Polynomial.degree`,
`ℚ₀.Polynomial.addList`, `ℚ₀.Polynomial.smulList`, `ℚ₀.Polynomial.mulList`,
`ℚ₀.Polynomial.evalList`, `ℚ₀.Polynomial.eval`, `ℚ₀.Polynomial.monomialList` (+ instancia `Zero`)

### Reals/Incompleteness.lean — `ℝ₀`

`ℝ₀.sqrt2Seq`