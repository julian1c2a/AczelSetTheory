# Technical Reference — Rationals `ℚ₀` / `ℚ₀cls` & Constructive Cauchy Analysis

**Last updated:** 2026-07-16 (ADR-023: renombrado `ℚ₀`/`ℚ₀cls`/`ℚ₀can`; proyección de
`Q0CauchyAlgebra`, `Series`, `Polynomial` y el subsistema `Reals/`)
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
| 108o | `AczelSetTheory/Rationals/Q0CauchyAlgebra.lean` | ✅ Complete (22/22 proyectados) |
| 108q | `AczelSetTheory/Rationals/Series.lean` | 🚧 Progress — 3/11 proyectados (6 sorry) |
| 108r | `AczelSetTheory/Rationals/Polynomial.lean` | 🚧 Progress — 11/17 proyectados (4 sorry) |
| 108s | `AczelSetTheory/Reals/Incompleteness.lean` | 🚧 Progress — 1/5 proyectados (3 sorry) |

> **Regla (8)** — *nada que no esté probado entra en REFERENCE*. Los símbolos cuyo footprint
> contiene `sorryAx` (directa **o indirectamente**) **no se documentan aquí**: ni firma, ni
> entrada en tabla. El inventario de los 14 `sorry` vive en
> [CURRENT-STATUS-PROJECT.md](../CURRENT-STATUS-PROJECT.md) §Known Sorry Locations y
> [NEXT-STEPS.md](../NEXT-STEPS.md) (fuente única). Criterio mecánico:
> `sorryAx ∉ collectAxioms(símbolo)`.

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

### 6.108o Rationals/Q0CauchyAlgebra.lean — `namespace ℚ₀`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `toClsSeq_add` | `(f g : ℕ₀ → ℚ₀) : toClsSeq (fun n => f n + g n) = fun n => toClsSeq f n + toClsSeq g n` |
| 2 | `toClsSeq_neg` | `(f : ℕ₀ → ℚ₀) : toClsSeq (fun n => -f n) = fun n => -toClsSeq f n` |
| 3 | `toClsSeq_sub` | `(f g : ℕ₀ → ℚ₀) : toClsSeq (fun n => f n - g n) = fun n => toClsSeq f n - toClsSeq g n` |

### 6.108q Rationals/Series.lean — `namespace ℚ₀`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `cls_sum` | `(f : ℕ₀ → ℚ₀) (n : ℕ₀) : (sum f n).cls = ℚ₀cls.sum (fun i => (f i).cls) n` |

*(sin secciones 6.108r/6.108s: `Polynomial` e `Incompleteness` no tienen ningún teorema libre de `sorry`)*

## 7. Exports per Module

Estos módulos **no llevan bloque `export`**: por **ADR-021** el bloque es opcional y selectivo,
y solo procede con símbolos de **nombre único en el proyecto** — mientras que los de aquí
(`sum`, `add`, `mul`, `inv`, `CauchySeq`…) son justamente los que colisionarían con los alias
a raíz de Peano y entre `ℚ₀`/`ℚ₀cls`. La fuente de verdad de esta proyección son las
**declaraciones no-`private`** (AI-GUIDE §11-14, reformulada por ADR-021).

### Rationals/Q0CauchyAlgebra.lean

`ℚ₀.CauchySeq.Equiv`, `ℚ₀.CauchySeq.ConvergesTo`, `ℚ₀.toClsCauchySeq`, `ℚ₀.toClsSeq_add`,
`ℚ₀.toClsSeq_neg`, `ℚ₀.toClsSeq_sub`, `ℚ₀.CauchySeq.add`, `ℚ₀.CauchySeq.neg`,
`ℚ₀.CauchySeq.sub`, `ℚ₀.CauchySeq.mulBound`, `ℚ₀.CauchySeq.mul`, `ℚ₀.CauchySeq.Pos`,
`ℚ₀.CauchySeq.ApartZero`, `ℚ₀.toClsPos`, `ℚ₀.toClsApartZero`, `ℚ₀.CauchySeq.invBound`,
`ℚ₀.CauchySeq.inv`, `ℚ₀.CauchySeq.div` (+ instancias `Add`/`Neg`/`Sub`/`Mul`)

### Rationals/Series.lean

`ℚ₀cls.sum`, `ℚ₀.sum`, `ℚ₀.cls_sum`

### Rationals/Polynomial.lean

`ℚ₀.trimZeros`, `ℚ₀.Polynomial`, `ℚ₀.Polynomial.zero`, `ℚ₀.Polynomial.degree`,
`ℚ₀.Polynomial.addList`, `ℚ₀.Polynomial.smulList`, `ℚ₀.Polynomial.mulList`,
`ℚ₀.Polynomial.evalList`, `ℚ₀.Polynomial.eval`, `ℚ₀.Polynomial.monomialList` (+ instancia `Zero`)

### Reals/Incompleteness.lean

`ℝ₀.sqrt2Seq`

---

# Anexo — proyección legacy (formato pre-2026-07)

> ⚠️ Lo que sigue está en el formato antiguo (`**[Q1]**`, `## Módulo:`), anterior al estándar
> de `REFERENCE-Algebra.md`. Su **contenido es válido** (todo probado, cumple la regla 8), pero
> su **forma no**. Migrarlo a §4/§6/§7 es tarea pendiente — ver `NEXT-STEPS.md`.
> No lo tomes como referencia de formato.

---

## Módulo: `AczelSetTheory/Rationals/Basic.lean`

**Namespace:** `ℚ₀cls`
**Descripción:** Números racionales como cociente $\mathbb{Z}_0 \times \{n : \mathbb{N}_0 \mid n \neq 0\}$. 

### Tipo y construcción
**[Q1]** `ℚ₀cls : Type` — Tipo de los racionales Peano. `Quotient ratSetoid`.
**[Q2]** `ℚ₀cls.mk (z : ℤ₀cls) (d : {n : ℕ₀ // n ≠ 𝟘}) : ℚ₀cls`
**[Q3]** `ℚ₀cls.ofInt (z : ℤ₀cls) : ℚ₀cls` — Embedding $z/1$.
**[Q4]** `ℚ₀cls.ofNat₀ (n : ℕ₀) : ℚ₀cls` — Embedding $n/1$.

### Instancias algebraicas
- `Zero ℚ₀cls`, `One ℚ₀cls`, `Add ℚ₀cls`, `Neg ℚ₀cls`, `Mul ℚ₀cls`, `Sub ℚ₀cls`
- `LE ℚ₀cls`, `LT ℚ₀cls`

---

## Módulo: `AczelSetTheory/Rationals/AbsVal.lean`
**Descripción:** Valor absoluto sobre ℚ₀cls.

**[AV1]** `ℚ₀cls.absVal (q : ℚ₀cls) : ℚ₀cls`
- `ℚ₀cls.absVal_zero_iff`: `absVal q = 0 ↔ q = 0`
- `ℚ₀cls.absVal_add_le`: Desigualdad triangular.
- `ℚ₀cls.absVal_mul`: `absVal (a * b) = absVal a * absVal b`

---

## Módulo: `AczelSetTheory/Rationals/IsCauchy.lean`
**Descripción:** Sucesiones de Cauchy diádicas (`IsCauchy` y `IsCauchy₂`).
**[C1]** `ℚ₀cls.pow2 (n : ℕ₀) : ℚ₀cls` — `1 / 2^n`.
**[C2]** `ℚ₀cls.IsCauchy (f : ℕ₀ → ℚ₀cls) : Prop` — `∀ n m, absVal (f n - f m) ≤ pow2 (min n m)`.

---

## Módulo: `AczelSetTheory/Rationals/Density.lean`
**Descripción:** Densidad de ℚ₀cls.
- `ℚ₀cls.midpoint (a b : ℚ₀cls) : ℚ₀cls` — $(a + b) / 2$.

---

## Módulo: `AczelSetTheory/Rationals/Inv.lean`
**Descripción:** Inverso multiplicativo en `ℚ₀cls`.

---

## Módulo: `AczelSetTheory/Rationals/Convergence.lean`
**Descripción:** Teoría de límites y sucesiones acotadas.
- **[L1]** `IsBounded (f : ℕ₀ → ℚ₀cls) : Prop` — `∃ B, ∀ n, absVal (f n) ≤ B`
- **[L2]** `ConvergesTo (f : ℕ₀ → ℚ₀cls) (L : ℚ₀cls) : Prop`
- **[L3]** `IsConvergent (f : ℕ₀ → ℚ₀cls) : Prop`
- **Teoremas clave:** Convergente implica acotada; Convergente implica de Cauchy.

---

## Módulo: `AczelSetTheory/Rationals/Bisection.lean`
**Descripción:** Método de bisección. 
- Define sucesiones de intervalos anidados `[a_n, b_n]` tales que la longitud decae exponencialmente y ambas sucesiones son de Cauchy y convergen al mismo límite.

---

## Módulo: `AczelSetTheory/Rationals/Canonical.lean`
**Descripción:** Representación canónica de racionales reducidos (coprimos).
- Proyección a su forma irreducible vía GCD.

---

## Módulo: `AczelSetTheory/Rationals/PowOrder.lean`
**Descripción:** Potencias de racionales y su interacción con el orden.

---

## Módulo: `AczelSetTheory/Rationals/RationalLog.lean`
**Descripción:** Expansión en serie para logaritmos vía `artanh`.
- Define las bases para logaritmos racionales analíticos.

---

## Módulo: `AczelSetTheory/Rationals/Roots.lean`
**Descripción:** Extracción de raíces por métodos numéricos aproximados.

---

## Módulo: `AczelSetTheory/Rationals/CauchySeqAlgebra.lean`
**Descripción:** Estructura de álgebra para las sucesiones de Cauchy.

---

## Módulo: `AczelSetTheory/Rationals/Archimedean.lean`
**Descripción:** Propiedad arquimediana explícita para ℚ₀cls.

**Teoremas Principales:**
- `theorem archimedean (x y : ℚ₀cls) : 0 < x → ∃ N : ℕ₀, y < Mul.mul (ofNat₀ N) x`

---

## Módulo: `AczelSetTheory/Rationals/Irrational.lean`
**Descripción:** Construcción formal de irracionales aproximados mediante sucesiones racionales sin límite exacto en ℚ₀cls (ej: convergencia por Newton-Raphson a $\sqrt{2}$).

**Teoremas Principales:**
- `theorem newton_seq_eventually_lt (q r : ℚ₀cls) (n : ℕ₂) (hq : 0 < q) (hr : 0 ≤ r) (h : q < pow r n.val.val) : ∃ N : ℕ₀, And (Peano.Order.le₀ 1 N) (newton_raphson_seq q n N < r)`
- `theorem newton_seq_apart_gt (q r : ℚ₀cls) (n : ℕ₂) (hq : 0 < q) (hr : 0 ≤ r) (h : q < pow r n.val.val) : ∃ N : ℕ₀, ∃ δ > (0:ℚ₀cls), ∀ k, Peano.Order.le₀ N k → δ ≤ Sub.sub r (newton_raphson_seq q n k)`
- `theorem newton_seq_apart_lt (q r : ℚ₀cls) (n : ℕ₂) (hq : 0 < q) (h : pow r n.val.val < q) : ∃ N : ℕ₀, ∃ δ > (0:ℚ₀cls), ∀ k, Peano.Order.le₀ N k → δ ≤ Sub.sub (newton_raphson_seq q n k) r`

---

## Módulo: `AczelSetTheory/Rationals/Q0.lean`
**Descripción:** Tipo racional estructurado `ℚ₀` que expone un racional exento de constructores internos dependientes de setoides a nivel visual, empleando pares coprimos (`ℚ₀can`).

---

## Módulo: `AczelSetTheory/Rationals/Q0Ops.lean`
**Descripción:** Operaciones algebraicas (`inv`, `div`, `absVal`, `pow`, `ofInt`, `ofNat₀`) sobre `ℚ₀`, elevadas explícitamente desde `ℚ₀cls`.

---

## Módulo: `AczelSetTheory/Rationals/Q0Cauchy.lean`
**Descripción:** Sucesiones de Cauchy para `ℚ₀` e inter-operabilidad con las sucesiones de Cauchy en `ℚ₀cls`. Exporta `ℚ₀.CauchySeq` y `ℚ₀.IsCauchy`.

---

## Módulo: `AczelSetTheory/Rationals/MinAdd.lean`
**Descripción:** Lemas auxiliares de suma y mínimo (`min_add_add_right`, `min_add_add_left`), posibilitando compilación correcta de operaciones algebraicas límite.

