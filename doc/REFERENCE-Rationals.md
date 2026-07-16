# Referencia Analítica — AczelSetTheory

Este documento detalla la formalización del cuerpo ordenado de los racionales `ℚ₀cls` y su teoría analítica en `AczelSetTheory/Rationals/`. 

## Jerarquía de Dependencias
```
Basic → AbsVal → Density
Basic → Inv → CauchySeqAlgebra
AbsVal, PowOrder → IsCauchy → Convergence → Bisection → Roots
Bisection → Archimedean → Irrational
Convergence → RationalLog
Canonical
```

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

