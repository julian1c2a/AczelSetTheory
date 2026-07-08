# Referencia Analítica — AczelSetTheory

Este documento detalla la formalización del cuerpo ordenado de los racionales `ℚ₀` y su teoría analítica en `AczelSetTheory/Rationals/`. 

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

**Namespace:** `ℚ₀`
**Descripción:** Números racionales como cociente $\mathbb{Z}_0 \times \{n : \mathbb{N}_0 \mid n \neq 0\}$. 

### Tipo y construcción
**[Q1]** `ℚ₀ : Type` — Tipo de los racionales Peano. `Quotient ratSetoid`.
**[Q2]** `ℚ₀.mk (z : ℤ₀) (d : {n : ℕ₀ // n ≠ 𝟘}) : ℚ₀`
**[Q3]** `ℚ₀.ofInt (z : ℤ₀) : ℚ₀` — Embedding $z/1$.
**[Q4]** `ℚ₀.ofNat₀ (n : ℕ₀) : ℚ₀` — Embedding $n/1$.

### Instancias algebraicas
- `Zero ℚ₀`, `One ℚ₀`, `Add ℚ₀`, `Neg ℚ₀`, `Mul ℚ₀`, `Sub ℚ₀`
- `LE ℚ₀`, `LT ℚ₀`

---

## Módulo: `AczelSetTheory/Rationals/AbsVal.lean`
**Descripción:** Valor absoluto sobre ℚ₀.

**[AV1]** `ℚ₀.absVal (q : ℚ₀) : ℚ₀`
- `ℚ₀.absVal_zero_iff`: `absVal q = 0 ↔ q = 0`
- `ℚ₀.absVal_add_le`: Desigualdad triangular.
- `ℚ₀.absVal_mul`: `absVal (a * b) = absVal a * absVal b`

---

## Módulo: `AczelSetTheory/Rationals/IsCauchy.lean`
**Descripción:** Sucesiones de Cauchy diádicas (`IsCauchy` y `IsCauchy₂`).
**[C1]** `ℚ₀.pow2 (n : ℕ₀) : ℚ₀` — `1 / 2^n`.
**[C2]** `ℚ₀.IsCauchy (f : ℕ₀ → ℚ₀) : Prop` — `∀ n m, absVal (f n - f m) ≤ pow2 (min n m)`.

---

## Módulo: `AczelSetTheory/Rationals/Density.lean`
**Descripción:** Densidad de ℚ₀.
- `ℚ₀.midpoint (a b : ℚ₀) : ℚ₀` — $(a + b) / 2$.

---

## Módulo: `AczelSetTheory/Rationals/Inv.lean`
**Descripción:** Inverso multiplicativo en `ℚ₀`.

---

## Módulo: `AczelSetTheory/Rationals/Convergence.lean`
**Descripción:** Teoría de límites y sucesiones acotadas.
- **[L1]** `IsBounded (f : ℕ₀ → ℚ₀) : Prop` — `∃ B, ∀ n, absVal (f n) ≤ B`
- **[L2]** `ConvergesTo (f : ℕ₀ → ℚ₀) (L : ℚ₀) : Prop`
- **[L3]** `IsConvergent (f : ℕ₀ → ℚ₀) : Prop`
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
**Descripción:** Propiedad arquimediana explícita para ℚ₀.

---

## Módulo: `AczelSetTheory/Rationals/Irrational.lean`
**Descripción:** Construcción formal de irracionales aproximados mediante sucesiones racionales sin límite exacto en ℚ₀ (ej: convergencia por Newton-Raphson a $\sqrt{2}$).

---

## Módulo: `AczelSetTheory/Rationals/HFRat.lean`
**Descripción:** Tipo racional estructurado `HFRat` que expone un racional exento de constructores internos dependientes de setoides a nivel visual, empleando pares coprimos (`ℚ₀'`).

---

## Módulo: `AczelSetTheory/Rationals/HFRatOps.lean`
**Descripción:** Operaciones algebraicas (`inv`, `div`, `absVal`, `pow`, `ofInt`, `ofNat₀`) sobre `HFRat`, elevadas explícitamente desde `ℚ₀`.

---

## Módulo: `AczelSetTheory/Rationals/HFRatCauchy.lean`
**Descripción:** Sucesiones de Cauchy para `HFRat` e inter-operabilidad con las sucesiones de Cauchy en `ℚ₀`. Exporta `HFRat.CauchySeq` y `HFRat.IsCauchy`.

---

## Módulo: `AczelSetTheory/Rationals/MinAdd.lean`
**Descripción:** Lemas auxiliares de suma y mínimo (`min_add_add_right`, `min_add_add_left`), posibilitando compilación correcta de operaciones algebraicas límite.

