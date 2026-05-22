# Comparación Técnica: Peano vs. Mathlib4

## Aritmética de Naturales, Decidibilidad y Módulos Relacionados

**Fecha:** 2026-04-17 (actualizado desde 2026-04-09)
**Autor:** Análisis sobre el proyecto de Julián Calderón Almendros
**Rama analizada:** `makingdecidable` (51 build jobs, 6 sorry en grupo finito)
**Versión Mathlib4 referenciada:** master (abril 2026)

---

## 0. Resumen Ejecutivo

El proyecto Peano es una formalización **desde cero** de la aritmética de Peano sobre el tipo
inductivo `ℕ₀`. Mathlib4 usa `Nat` (el tipo nativo del kernel de Lean 4) e integra la aritmética
de naturales en una jerarquía algebraica abstracta de cientos de archivos. Las diferencias son de
naturaleza fundamentalmente **arquitectónica**: mismo territorio matemático, estrategias de diseño
completamente distintas.

---

## 1. Tipo Base

### 1.1. Peano: `ℕ₀`

```lean
-- Peano/PeanoNat.lean
inductive ℕ₀ : Type
  | zero : ℕ₀
  | succ : ℕ₀ → ℕ₀
```

Tipo inductivo **propio** del proyecto. Los 8 axiomas de Peano se prueban explícitamente como
teoremas a partir de la definición inductiva. Se introducen dos isomorfismos explícitos con `Nat`:

| Función | Tipo | Dirección |
|---------|------|-----------|
| `Λ` | `ℕ₀ → ℕ` | Peano → kernel |
| `Ψ` | `ℕ → ℕ₀` | kernel → Peano |

`Λ` y `Ψ` se usan para transferir teoremas entre `ℕ₀` y `Nat` cuando conviene (especialmente
para probar decidibilidad y orden bien fundado). Los isomorfismos aparecen como prefijo en los
nombres: `isomorph_Λ_lt`, `isomorph_Ψ_gcd`, etc.

**Notación especial:** `𝟘`, `𝟙`, `𝟚`, `𝟛` para los primeros naturales; `σ n` para el sucesor.

### 1.2. Mathlib4/Lean4 Core: `Nat`

```lean
-- Init/Prelude.lean (Lean4 kernel)
inductive Nat : Type
  | zero : Nat
  | succ : Nat → Nat
```

`Nat` **es** el tipo del kernel. La computación es primitiva: el kernel evalúa `2 + 3 = 5` por
reducción directa sin ningún teorema. `DecidableEq Nat` y `Decidable (n ≤ m)` son **instancias
del kernel**, no requieren prueba en espacio de usuario.

**Consecuencia clave:** en Lean 4, `decide : Nat.Prime 7` se evalúa en tiempo de elaboración sin
ningún código adicional. En Peano, requiere instancias `Decidable` explícitas más una función
booleana certificada.

---

## 2. Decidibilidad

### 2.1. Peano: Puente booleano explícito

La estrategia sistemática adoptada en la rama `makingdecidable`:

**Paso 1.** Definir una función booleana estructuralmente recursiva:

```lean
def blt (n m : ℕ₀) : Bool :=
  match n, m with
  | _       , ℕ₀.zero  => false
  | ℕ₀.zero , σ _      => true
  | σ n'    , σ m'     => blt n' m'
```

**Paso 2.** Probar la equivalencia con la relación proposicional:

```lean
theorem blt_iff_Lt (n m : ℕ₀) : blt n m = true ↔ Lt n m
theorem nblt_iff_nLt (n m : ℕ₀) : blt n m = false ↔ ¬ Lt n m
```

**Paso 3.** Construir la instancia `Decidable` usando el bridge:

```lean
instance decidableLt (n m : ℕ₀) : Decidable (Lt n m) :=
  if h : blt n m then isTrue ((blt_iff_Lt n m).mp h)
  else isFalse (fun hlt => h ((blt_iff_Lt n m).mpr hlt))
```

Se aplica el mismo patrón para `Gt`, `Le`, `Ge`. La instancia `decidableGe` usa `decEq` (de
`deriving DecidableEq` en `ℕ₀`) internamente.

**Instancias adicionales (Order.lean):**

```lean
def bexLe (P : ℕ₀ → Bool) : ℕ₀ → Bool
  | 𝟘    => P 𝟘
  | σ n' => P (σ n') || bexLe P n'

def decidableBExLe_of_bool (P : ℕ₀ → Prop) (Pb : ℕ₀ → Bool)
    (h_iff : ∀ k, Pb k = true ↔ P k) (n : ℕ₀) :
    Decidable (∃ k, Le k n ∧ P k)
```

Esta última es esencial para hacer decidible búsquedas acotadas (divisores, factores primos, etc.).

**Módulo de reexportación:** `Decidable.lean` agrega todas las instancias en un único punto de
importación sin añadir definiciones nuevas.

### 2.2. Mathlib4/Lean4 Core: Instancias del kernel

Las comparaciones sobre `Nat` son decidibles por construcción. El kernel de Lean 4 define:

```lean
-- Init/Data/Nat/Basic.lean
instance : DecidableEq Nat := Nat.decEq
instance (n m : Nat) : Decidable (n ≤ m) := Nat.decLe n m
instance (n m : Nat) : Decidable (n < m) := Nat.decLt n m
```

Implementadas en C++ en el kernel; no hay código Lean que probar. `n ≤ m` para `Nat` se reduce a
`Nat.ble n m = true` por definición.

En Mathlib, la decidibilidad se propaga automáticamente a cualquier proposición que mencione `Nat`
mediante síntesis de instancias. Por ejemplo, `Nat.decidablePrime` existe y permite `decide` en
primality tests:

```lean
instance Nat.decidablePrime (n : ℕ) : Decidable (Nat.Prime n)
-- Implementado vía Nat.minFac: n es primo ↔ n.minFac = n ∧ 2 ≤ n
```

**Contraste arquitectónico:** Peano necesita 4 archivos y ~200 líneas para instalar decidibilidad
en relaciones de orden. En Lean 4, es una línea de `deriving` o está en el kernel.

---

## 3. Orden y Estructura de Orden

### 3.1. Peano

| Relación | Definición | Bool. |
|----------|-----------|-------|
| `Lt n m` | match estructural recursivo | `blt` |
| `Gt n m` | match estructural recursivo | `bgt` |
| `Le n m` | `Lt n m ∨ n = m` | `ble` |
| `Ge n m` | `Lt m n ∨ n = m` | `bge` |

Teoremas principales: `lt_irrefl`, `lt_trans`, `lt_asymm`, `trichotomy` (completa), `le_antisymm`,
`le_total`, `lt_iff_le_not_le`. La tricotomía se prueba explícitamente.

`le'` es una definición alternativa por match estructural de `Le`, con prueba de equivalencia
(`Le_iff_le'`). Sirve para ciertas pruebas por inducción.

Instancias de clases: `LT ℕ₀ := ⟨Lt⟩`, `LE ℕ₀ := ⟨Le⟩`.

**Sin integración con `LinearOrder`:** el proyecto no instancia `LinearOrder ℕ₀`, lo que significa
que los lemas abstractos de Mathlib sobre órdenes lineales (`lt_or_ge`, `le_max_left`, etc.) no se
aplican automáticamente a `ℕ₀`.

### 3.2. Mathlib4

`Nat` tiene instancia `LinearOrder` completa, derivada del kernel. Esto implica automáticamente:

- `le_total : ∀ a b : ℕ, a ≤ b ∨ b ≤ a`
- `lt_or_ge`, `le_or_lt`
- Compatibilidad con `min`, `max` (instancia `Lattice`)
- `sup_eq_max`, `inf_eq_min`
- Toda la jerarquía de `Order.lean` en Mathlib aplica a `ℕ`

El `LinearOrder` de `Nat` además satisface `WellFoundedOrder Nat` y `WellFoundedRelation Nat`.

---

## 4. Buen Orden y Recursión

### 4.1. Peano

```lean
-- WellFounded.lean
instance : SizeOf ℕ₀ where sizeOf := Ψ

theorem acc_lt_wf (n : ℕ₀) : Acc Lt n
theorem well_founded_lt : WellFounded Lt
theorem well_ordering_principle (P : ℕ₀ → Prop)
    (hne : ∃ n, P n) : ∃! n, P n ∧ ∀ m, P m → Le n m
```

La prueba de `acc_lt_wf` usa la función de isomorfismo `Ψ` para reducir el buen orden de `ℕ₀` al
de `Nat`. La instancia `SizeOf` es lo que Lean 4 necesita para verificar terminación automática.

### 4.2. Mathlib4

`WellFounded Nat.lt` está en el kernel de Lean 4. `Nat.strongRecOn`, `Nat.strongInductionOn` están
disponibles en `Init`. La recursión bien fundada sobre `Nat` no requiere prueba en espacio de
usuario; el elaborador la resuelve automáticamente mediante `termination_by`.

---

## 5. Aritmética Básica

### 5.1. Peano (Módulos Add, Sub, Mul, Div)

| Operación | Módulo | Definición |
|-----------|--------|-----------|
| `add n m` | `Add.lean` | Recursión en `m` |
| `sub n m` con prueba `h : Le m n` | `Sub.lean` | Resta exacta con certificado |
| `mul n m` | `Mul.lean` | `Σ_{i<m} n` por add |
| `div n m`, `mod n m` | `Div.lean` | División euclidiana con terminación explícita |

**Subtracción exacta vs. saturada:** Peano distingue `sub n m (h : Le m n) : ℕ₀` (resta exacta,
requiere prueba) de la resta saturada `n - m` (donde `n - m = 0` si `m > n`). Mathlib solo tiene
resta saturada para `Nat`. Esto hace los lemas de Peano más precisos pero más verbosos.

Notaciones del proyecto: `n -( h ) m` para la resta exacta (con prueba `h`), `n - m` para la
saturada.

### 5.2. Mathlib4

- `Nat.add`, `Nat.mul`: definición del kernel, computable
- `Nat.sub`: **truncated** (saturante): `n - m = 0` cuando `n < m`
- `Nat.div`, `Nat.mod`: por recursión bien fundada, en `Init`
- Integración con `CommSemiring Nat`, `OrderedSemiring Nat`, `CanonicallyOrderedCommSemiring Nat`

La aritmética de `Nat` se trata como instancia de estructuras algebraicas abstractas, lo que permite
aplicar automáticamente lemas de `Algebra.Ring` a `ℕ`. En Peano, cada lema algebraico se prueba
directamente sobre `ℕ₀`.

---

## 6. Divisibilidad y MCD

### 6.1. Peano

```lean
-- Arith.lean
def Divides (a b : ℕ₀) : Prop := ∃ k : ℕ₀, b = mul a k
infix:50 " ∣ " => Divides
notation:50 a " ∤ " b => ¬ Divides a b
infix:50 " ∣₁ " => Divides₁   -- variante para ℕ₁

def IsGCD (a b d : ℕ₀) : Prop := d ∣ a ∧ d ∣ b ∧ ∀ e, e ∣ a → e ∣ b → e ∣ d
def Coprime (a b : ℕ₀) : Prop := IsGCD a b 1
def gcd (a b : ℕ₀) : ℕ₀            -- algoritmo de Euclides
def lcm (a b : ℕ₀) : ℕ₀
def dividesb (d n : ℕ₀) : Bool     -- función booleana computable
```

**Identidad de Bezout:** probada directamente sobre `ℕ₀`:

```lean
theorem bezout_natform {a b : ℕ₀} (hg : IsGCD a b d) :
    ∃ x y : ℕ₀, add (mul a x) (mul b y) = d ∨
                add (mul b y) (mul a x) = d
```

(Bezout en ℕ₀ requiere disyunción de signos, ya que no hay enteros negativos. Es la forma natural
sobre ℕ.)

Teoremas exportados: ~60, incluyendo `gcd_comm`, `gcd_assoc`, `gcd_zero_left`, `dvd_gcd`,
`gcd_mul_lcm`, `IsGCD_gcd`, `coprime_dvd_of_dvd_mul` (Gauss).

**Variante `ℕ₁` (naturales positivos):** definiciones `Divides₁`, `IsGCD₁`, `gcd₁`, `Coprime₁`
para evitar casos `n = 0` en ciertos contextos.

### 6.2. Mathlib4

- `Nat.dvd` es la instancia de `Dvd Nat` del kernel, no una definición propia
- `Nat.gcd`: algoritmo de Euclides, definido en `Batteries.Data.Nat.Gcd` (antes `Init`)
- `Nat.Coprime`: definida como `Nat.gcd m n = 1` (no vía `IsGCD`)
- `Nat.lcm m n = m * n / Nat.gcd m n`

Bezout para `Nat`: no existe directamente como `ax + by = gcd(a,b)` (requeriría ℤ). En Mathlib
se usa `Int.gcd_eq_gcd_ab : ∃ u v : ℤ, ↑(Nat.gcd m n) = ↑m * u + ↑n * v`.

Teoremas en `Mathlib.Data.Nat.GCD`:

- `Nat.gcd_greatest`, `Nat.gcd_comm`, `Nat.gcd_assoc`
- `Nat.Coprime.dvd_mul_right`, `Nat.Coprime.dvd_mul_left` (Euclid's lemma via coprimality)
- `Nat.Coprime.dvd_of_dvd_mul_right` (equivalente al lema de Gauss de Peano)
- Adicionalmente: `pow_sub_one_gcd_pow_sub_one` (identidad GCD-potencias)

Mathlib tiene también `GCDMonoid` y `UniqueFactorizationMonoid` como clases abstractas que `Nat`
instancia, permitiendo reusar teoremas en cualquier UFD.

---

## 7. Números Primos

### 7.1. Peano

```lean
-- Primes.lean  (namespace Peano.Primes)
def Prime (p : ℕ₀) : Prop       -- tiene exactamente dos divisores
def Irreducible (p : ℕ₀) : Prop -- no factorizable en no-unidades
def HasExactlyTwoDivisors (n : ℕ₀) : Prop
subtype ℙ := {n : ℕ₂ // Prime n.val.val}  -- primos certificados

def smallestDivisor (n : ℕ₀) : ℕ₀  -- factor primo mínimo (computable)
def factorize (n : ℕ₂) : ...        -- factorización en lista de primos
```

Teoremas clave:

- `prime_iff_irreducible` (equivalencia de las dos definiciones)
- `prime_iff_has_exactly_two_divisors`
- `exists_prime_divisor`
- `exists_prime_factorization`
- `unique_prime_factorization` (Teorema Fundamental de la Aritmética)
- `prime_dvd_product_list` (Euclid's lemma sobre listas)

**Pendiente (1 sorry):** Un paso auxiliar en `exists_prime_factorization` relacionado con
aritmética de resta saturada.

**Sin:** Teorema de Euclides (infinitos primos), `n`-ésimo primo, función de Euler `φ`, criba.

### 7.2. Mathlib4

```lean
-- Mathlib.Data.Nat.Prime.Defs
def Nat.Prime (p : ℕ) : Prop := Irreducible p
-- donde Irreducible viene de Mathlib.Algebra.Prime.Defs

def Nat.minFac (n : ℕ) : ℕ  -- factor primo mínimo, computable
-- Nat.minFac_prime, Nat.minFac_dvd, Nat.minFac_pos

instance Nat.decidablePrime (n : ℕ) : Decidable (Nat.Prime n)
-- implementado: n.Prime ↔ n.minFac = n ∧ 2 ≤ n

subtype Nat.Primes := {p : ℕ // p.Prime}
```

Módulos de primos en Mathlib (cada uno es un archivo separado):

| Archivo | Contenido |
|---------|-----------|
| `Prime/Defs` | Definición, `not_prime_zero/one`, `prime_def`, `prime_def_le_sqrt` |
| `Prime/Basic` | `prime_mul_iff`, `Prime.dvd_iff_eq`, `Prime.eq_two_or_odd` |
| `Prime/Factorial` | Relación `n!` con primos, Bertrand |
| `Prime/Infinite` | `Nat.exists_infinite_primes` (Euclides: ∀n, ∃p≥n, p primo) |
| `Prime/Nth` | El n-ésimo primo `Nat.nth Prime`, su densidad |
| `Prime/Pow` | Primos y potencias, `Nat.Prime.pow_dvd_of_dvd_pow` |
| `Factorization/Basic` | `Nat.factorization : ℕ →₀ ℕ` (Finsupp, exponents map) |
| `Factorization/Defs` | Definición de `factorization` vía `Nat.minFac` recursivo |
| `GCD/Prime` | GCD y primos, `Nat.Coprime.prime_dvd_iff` |

La factorización prima en Mathlib usa `Finsupp ℕ ℕ` (función con soporte finito): `p ↦ vp(n)` (valuación p-ádica). Esto permite:

```lean
theorem Nat.factorization_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    (m * n).factorization = m.factorization + n.factorization
```

En Peano, la factorización devuelve una `List ℕ₀`.

---

## 8. Potencia

### 8.1. Peano

```lean
-- Combinatorics/Pow.lean  (namespace Peano.Pow)
def pow (n m : ℕ₀) : ℕ₀    -- recursión en m
infix:80 " ^ " => pow
```

27 teoremas exportados: `pow_zero`, `pow_succ`, `one_pow`, `pow_add_eq_mul_pow`,
`pow_pow_eq_pow_mul`, `pow_ne_zero`, `pow_eq_zero_iff`, `pow_lt_mono_exp`, etc.

### 8.2. Mathlib4

`Nat.pow` está en el kernel, instancia de `HPow Nat Nat Nat`. La jerarquía algebraica da:

- `pow_add`, `pow_mul`, `mul_pow`, `one_pow` gratis desde `Monoid`
- `pow_le_pow_right`, `pow_lt_pow_left`, `pow_lt_pow_right` desde `OrderedSemiring`
- Lemas específicos en `Mathlib.Data.Nat.Defs` y en archivos de álgebra abstracta

La ventaja de Mathlib: `pow_comm` (conmutatividad en monoides conmutativos) aplica
automáticamente a `ℕ`, `ℤ`, `ℝ`, `ℂ`, etc. sin repetir pruebas.

---

## 9. Factorial

### 9.1. Peano

```lean
-- Combinatorics/Factorial.lean  (namespace Peano.Factorial)
def factorial : ℕ₀ → ℕ₀
  | 𝟘    => 𝟙
  | σ n' => mul (factorial n') (σ n')
```

10 teoremas: `factorial_zero`, `factorial_one`, `factorial_two`, `factorial_succ`,
`factorial_pos`, `factorial_ne_zero`, `factorial_ge_one`, `factorial_le_succ`,
`factorial_le_mono`, `factorial_ge_one`.

No hay notación especial (no equivalente a `n!`).

### 9.2. Mathlib4

```lean
-- Mathlib.Data.Nat.Factorial.Basic
def Nat.factorial : ℕ → ℕ
  | 0       => 1
  | succ n  => succ n * factorial n
scoped notation:10000 n "!" => Nat.factorial n
-- Nota: se usa (n)! para evitar confusión con Bool.not
```

Mathlib tiene **más variantes** y **más teoremas**:

- `Nat.ascFactorial n k` — producto `n * (n+1) * ... * (n+k-1)`
- `Nat.descFactorial n k` — producto `n * (n-1) * ... * (n-k+1)`
- `Nat.doubleFact n` — doble factorial `n!!`
- `Nat.superFactorial n` — superfactorial `sf(n) = 1! * 2! * ... * n!`
- `factorial_dvd_factorial`, `dvd_factorial`, `factorial_mul_pow_le_factorial`
- `factorial_lt` (bicondicional completo con hipótesis `0 < n`)
- `factorial_inj` (inyectividad para `n > 1`)
- `lt_factorial_self` (para `n ≥ 3`)

---

## 10. Coeficientes Binomiales y Binomio de Newton

### 10.1. Peano

```lean
-- Combinatorics/Binom.lean  (namespace Peano.Binom)
def binom : ℕ₀ → ℕ₀ → ℕ₀
  | _    , 𝟘    => 𝟙
  | 𝟘    , σ _  => 𝟘
  | σ n' , σ k' => add (binom n' k') (binom n' (σ k'))
notation "C(" n ", " k ")" => binom n k
```

14 teoremas: `binom_zero_zero`, `binom_zero_succ`, `binom_succ_zero`, `binom_pascal`,
`binom_n_zero`, `binom_n_one`, `binom_one`, `binom_succ_n_by_n`, `binom_eq_zero_of_gt`,
`binom_self`, `binom_pos`, `binom_mul_factorials`.

```lean
-- Combinatorics/NewtonBinom.lean  (namespace Peano.NewtonBinom)
def binomTerm (a b n k : ℕ₀) := mul (mul C(n, k) (pow a k)) (pow b (sub n k ...))

theorem newton_binom (a b n : ℕ₀) :
    pow (add a b) n = finSum (binomTerm a b n) n
```

El binomio de Newton se prueba directamente sobre `ℕ₀`. También:

- `sum_binom_eq_pow_two` : Σ C(n,k) = 2^n
- `pow_add_split` : n^(m+k) = n^m * n^k
- `exists_nm_growth` : ∃ n m, ∀ k ≥ 1, (n+k)^m < n^(m+k)

### 10.2. Mathlib4

```lean
-- Mathlib.Data.Nat.Choose.Basic
def Nat.choose : ℕ → ℕ → ℕ
  | _, 0     => 1
  | 0, _+1   => 0
  | n+1, k+1 => choose n k + choose n (k+1)
-- Mismo patrón Pascal que Peano
```

Mathlib tiene **muchos más teoremas** distribuidos en múltiples archivos:

| Archivo | Teoremas adicionales |
|---------|---------------------|
| `Choose/Basic` | `choose_symm`, `choose_eq_factorial_div_factorial`, `choose_le_middle`, `multichoose` |
| `Choose/Bounds` | Cotas ajustadas: `choose_le_pow`, `choose_le_pow_of_lt_half`, `choose_lt_pow_of_lt_half` |
| `Choose/Dvd` | `Prime.dvd_choose_add` (un primo p divide C(n+m, n) si p divide n+m pero no n ni m) |
| `Choose/Factorization` | `Nat.factorization_choose` en términos de valuaciones p-ádicas |
| `Choose/Vandermonde` | Identidad de Vandermonde: `∑ C(m,k) * C(n,r-k) = C(m+n,r)` |
| `Choose/Sum` | `Nat.add_pow` (Binomio de Newton generalizado) |
| `Choose/Lucas` | Teorema de Lucas sobre `C(n,k) mod p` |

El Binomio de Newton en Mathlib está en la jerarquía algebraica abstracta:

```lean
-- Mathlib.RingTheory.Binomial
theorem add_pow {R : Type*} [CommSemiring R] (x y : R) (n : ℕ) :
    (x + y) ^ n = ∑ k ∈ Finset.range (n + 1), x ^ k * y ^ (n - k) * n.choose k
```

Aplica a `ℕ`, `ℤ`, `ℝ`, `ℂ`, polinomios, etc. La versión de Peano es solo para `ℕ₀`.

---

## 11. Logaritmo

### 11.1. Peano

```lean
-- PeanoNat/Log.lean  (namespace Peano.Log)
def logMod (b n : ℕ₀) : ℕ₀ × ℕ₀   -- devuelve (⌊log_b n⌋, n - b^⌊log_b n⌋)
def log    (b n : ℕ₀) : ℕ₀          -- = (logMod b n).1
def logRem (b n : ℕ₀) : ℕ₀          -- = (logMod b n).2
```

Algoritmo: **división sucesiva lineal** (`n / b` en cada paso).  
Terminación: `isomorph_Ψ_lt` reduce a bien orden de `Nat`.

11 teoremas: `log_zero`, `logRem_zero`, `log_one`, `log_of_lt`, `logMod_spec`, `log_upper_bound`.

### 11.2. Mathlib4

```lean
-- Mathlib.Data.Nat.Log
def Nat.log (b n : ℕ) : ℕ
  := if b ≤ 1 then 0 else (go b n).2 where
  go : ℕ → ℕ → ℕ × ℕ  -- cuadra b en cada paso: go (b*b) fuel
```

Algoritmo: **cuadrado iterado** (`go (b*b) fuel`). Para `Nat.log 2 (2^1000000)` es
exponencialmente más rápido que la división lineal. Terminación: `fuel` se pasa como cota superior.

Mathlib tiene **además** `Nat.clog b n` (logaritmo techo, menor `k` con `n ≤ b^k`), que Peano no
tiene.

Teoremas adicionales de Mathlib no presentes en Peano:

- `Nat.log_lt_iff_lt_pow`, `Nat.log_pos_iff`
- `Nat.log_add_one_le`, `Nat.log_mono_right`, `Nat.log_pow`
- `Nat.clog_pos`, `Nat.clog_le_iff_le_pow`
- Adjunción: `b ^ Nat.log b n ≤ n < b ^ (Nat.log b n + 1)`

---

## 12. Raíz Cuadrada

### 12.1. Peano

```lean
-- PeanoNat/Sqrt.lean  (namespace Peano.Sqrt)
def sqrtMod (n : ℕ₀) : ℕ₀ × ℕ₀   -- devuelve (⌊√n⌋, n - ⌊√n⌋²)
def sqrt    (n : ℕ₀) : ℕ₀          -- = (sqrtMod n).1
def sqrtRem (n : ℕ₀) : ℕ₀          -- = (sqrtMod n).2
```

Algoritmo: **substracción de cuadrados** (`n - (2k+1)` en cada paso, contando cuántos caben).  
10 teoremas: `sqrt_zero`, `sqrtRem_zero`, `sqrt_one`, `sqrtMod_spec`, `sqrtRem_lt`, `sqrt_upper_bound`.

La especificación completa: `n = (sqrt n)² + sqrtRem n` y `sqrtRem n < 2*(sqrt n) + 1`.

### 12.2. Mathlib4

```lean
-- Mathlib.Data.Nat.Sqrt (vía Batteries)
def Nat.sqrt (n : ℕ) : ℕ
-- Newton's method: iterate (k + n/k) / 2 starting from n
```

Algoritmo: **método de Newton** (converge cuadráticamente). Terminación: cota AM-GM.  
Más eficiente que el método de Peano para entradas grandes.

Mathlib también tiene `Nat.NthRoot` (raíz n-ésima) en `Mathlib.Data.Nat.NthRoot.Defs`:

```lean
def Nat.nthRoot (k n : ℕ) : ℕ  -- ⌊n^(1/k)⌋
```

No presente en Peano.

---

## 13. Arquitectura y Modularidad

### 13.1. Peano

| Aspecto | Descripción |
|---------|-------------|
| **Número de archivos** | ~20 módulos `.lean` |
| **Granularidad** | Un módulo por tema matemático (Add, Mul, Div, Primes, etc.) |
| **Dependencias** | Cadena lineal: Axioms → StrictOrder → Order → ... → NewtonBinom |
| **Integración algebraica** | Ninguna (no instancia `CommSemiring`, `LinearOrder`, etc.) |
| **Sistema de locks** | Un archivo activo a la vez; módulos completos "frozen" permanentemente |
| **Export blocks** | Obligatorios; lista explícita de todo lo público en cada módulo |
| **REFERENCE.md** | Documento de referencia completo, actualizado con cada módulo |
| **Notaciones propias** | `𝟘`, `𝟙`, `σ`, `C(n,k)`, `∑ k ≤ n`, `blt`, `bgt`, `ble`, `bge` |

**Filosofía:** máxima transparencia y trazabilidad. Cada definición tiene su justificación,
notación documentada, y status de completitud. El costo es no poder reutilizar automáticamente
el ecosistema de Mathlib.

### 13.2. Mathlib4

| Aspecto | Descripción |
|---------|-------------|
| **Número de archivos (solo Nat)** | >80 archivos en `Mathlib/Data/Nat/` |
| **Granularidad** | Por teorema o grupo pequeño de teoremas relacionados |
| **Dependencias** | DAG complejo; imports de álgebra abstracta en todos los niveles |
| **Integración algebraica** | Total: `Nat` instancia `LinearOrderedCommMonoidWithZero`, `CanonicallyOrderedCommSemiring`, `UniqueFactorizationMonoid`, `GCDMonoid`, etc. |
| **Barrel files** | `Mathlib/Data/Nat.lean` importa todo el subdirectorio |
| **Notaciones** | `n!`, `n.choose k`, `n ∣ m`, `n.gcd m`, estándares de Lean4 |
| **Reutilización** | Todo lema abstracto (álgebra, orden, topología) aplica automáticamente |

**Filosofía:** generalización máxima. Cada definición es la instancia de una clase abstracta. El
costo es una curva de aprendizaje alta y una jerarquía de imports muy profunda.

---

## 14. Tácticas: Brecha Práctica Significativa

Una diferencia de impacto inmediato en productividad que no aparece en ninguna definición pero
afecta cada prueba.

### 14.1. Tácticas ausentes en Peano, disponibles en Mathlib

**`omega`** — Decisor de aritmética lineal sobre `Nat` e `Int`. Cierra automáticamente cualquier
meta que sea consecuencia de hipótesis lineales:

```lean
-- Mathlib: un línea
theorem add_lt_of_lt_sub {a b c : Nat} (h : a < c - b) (hbc : b ≤ c) : a + b < c := by omega

-- Peano equivalente: inducción manual + varios lemas de Add/Sub
```

Sin `omega`, el proyecto Peano requiere inducción estructural explícita para muchas desigualdades
que son trivialmente aritméticas. Es la brecha táctica más costosa en tiempo de prueba.

**`norm_num`** — Decisor numérico: `norm_num` cierra `2^10 = 1024`, `Nat.Prime 97`, etc. por
reducción en tiempo de elaboración. En Peano, estos hechos requieren una secuencia de `rfl` o
`simp` con los lemas construidos manualmente.

**`decide`** — Evalúa cualquier proposición decidible en tiempo de elaboración. Sobre `Nat`
funciona directamente (el kernel reduce); sobre `ℕ₀` requiere primero instalar todas las
instancias `Decidable` de la rama `makingdecidable`.

**`gcongr`** — Congruencia con monotonía: cierra `a^n ≤ b^n` dado `a ≤ b` y `0 < n`. En
Peano cada caso requiere el teorema correspondiente de Pow.lean.

**`positivity`** — Demuestra automáticamente `0 < expr` y `0 ≤ expr` para expresiones
aritméticas compuestas.

### 14.2. `Nat.find`

```lean
-- Mathlib.Data.Nat.Find
def Nat.find {p : Nat → Prop} [DecidablePred p] (h : ∃ n, p n) : Nat
-- Devuelve el mínimo n con p n, computacionalmente

Nat.find_spec  (h : ∃ n, p n) : p (Nat.find h)
Nat.find_min   (h : ∃ n, p n) : ∀ m < Nat.find h, ¬ p m
Nat.find_min'  (h : ∃ n, p n) (hm : p m) : Nat.find h ≤ m
```

En Peano, `smallestDivisor` (Primes.lean) es una instancia ad-hoc. No existe un combinador
general equivalente a `Nat.find` para predicados decidibles arbitrarios.

### 14.3. Casting (`Nat.cast`)

```lean
-- Mathlib: Nat.cast : Nat → α  para cualquier AddMonoidWithOne α
-- Permite probar: (n : Nat) → (↑n : ℤ) + (↑m : ℤ) = ↑(n + m)
-- Sirve para transferir resultados de Nat a ℤ, ℚ, ℝ, etc.
theorem Nat.cast_add, Nat.cast_mul, Nat.cast_pow ...
```

Peano tiene los isomorfismos `Λ`/`Ψ` (solo entre `ℕ₀` y `Nat`), pero no hay casting hacia
tipos arbitrarios como ℤ o ℝ.

---

## 15. Tabla Comparativa de Funcionalidades

| Funcionalidad | Peano | Mathlib4 | Notas |
|---------------|-------|----------|-------|
| Tipo natural | `ℕ₀` (propio) | `Nat` (kernel) | |
| Axiomas de Peano | Probados explícitamente | Incorporados en el kernel | |
| Decidabilidad `<`, `≤` | Bridge booleano explícito | Kernel / `Init` | Peano: ~200 líneas más |
| `DecidablePrime` | Sí (`DecidableRel Prime`) | Sí (`minFac`) | |
| Bezout sobre ℕ | Sí (disjuntivo) | No (solo sobre ℤ) | |
| `LinearOrder` instancia | No | Sí | |
| `CommSemiring` instancia | No | Sí | |
| `GCDMonoid` instancia | No | Sí | |
| `UniqueFactorizationMonoid` | No | Sí | |
| Factorial | Sí (básico, 10 thms) | Sí (completo, 30+ thms) | Mathlib tiene `ascFactorial`, `descFactorial`, `doubleFact` |
| Binomial (Pascal) | Sí | Sí | |
| Newton (sobre ℕ) | Sí | Sí (`Choose/Sum`) | |
| Newton (abstracto: CommSemiring) | No | Sí (`add_pow`) | |
| Vandermonde | No | Sí | |
| Lucas mod p | No | Sí | |
| Logaritmo piso | Sí (lineal) | Sí (binario, más rápido) + `clog` | |
| Raíz cuadrada piso | Sí (substracción) | Sí (Newton, más rápido) | |
| Raíz n-ésima | No | Sí (`NthRoot`) | |
| Infinitud de primos | No | Sí (`exists_infinite_primes`) | |
| n-ésimo primo | No | Sí (`Nat.nth Prime`) | |
| Función de Euler `φ` | Sí (`totient`) | Sí (`Nat.totient`) | |
| Criba de Eratóstenes | No | Indirectamente | |
| Teorema Fundamental Aritmética | Sí (lista) | Sí (`Finsupp`) | |
| Valuaciones p-ádicas `vp(n)` | No | Sí (`Nat.factorization`) | |
| Congruencias `n ≡ m [MOD k]` | Sí (`ModEq`) | Sí (`Nat.ModEq`) | |
| Fibonacci | Sí (`fib`) | Sí (`Nat.fib`) | |
| Teorema Chino del Resto | Sí (`chinese_remainder`) | Sí | |
| Pequeño Fermat | Sí (`fermat_little`) | Sí | |
| Conjuntos finitos | Sí (`FSet` quotient) | Sí (`Finset`) | |
| Funciones sobre FSet | Sí (`MapOn`, ~90 decl.) | Sí (Mathlib extenso) | |
| Permutaciones | Sí (`Perm`, 1 sorry) | Sí (`Equiv.Perm`) | |
| Principio del palomar | Sí (`pigeonhole`) | Sí | |
| Dígitos en base b | Sí (`digits`) | Sí (`Nat.digits`) | |
| Función de emparejamiento | Sí (`pair`/`unpair`) | Sí (`Nat.pair`) | |
| Números de Catalan | No | Sí | |
| `Nat.find` (mínimo decidible) | No | Sí | |
| Tácticas `omega`, `norm_num` | No aplican a `ℕ₀` | Sí (sobre `Nat`) | Brecha práctica mayor |
| `Nat.cast` (hacia ℤ, ℝ, etc.) | No | Sí | |
| Predecesor seguro `ρ n (h: n≠0)` | Sí | No (solo `Nat.pred` total) | Exclusivo Peano |
| Operaciones bit a bit | No | Sí (`Nat.testBit`, `Nat.bitwise`) | |

---

## 16. Diferencias de Notación

| Concepto | Peano | Mathlib4 |
|----------|-------|----------|
| Sucesor | `σ n` | `n.succ` o `n + 1` |
| Cero | `𝟘` | `0` |
| Uno | `𝟙` | `1` |
| Menor estricto | `Lt n m` + `n < m` vía LT | `n < m` vía LT |
| `n!` | No hay notación | `(n)!` |
| Binomial | `C(n, k)` | `n.choose k` |
| GCD | `gcd a b` | `Nat.gcd m n` o `m.gcd n` |
| Divisibilidad | `a ∣ b` (definida en Arith) | `a ∣ b` (del kernel) |
| Primo | `Prime p` (Peano.Primes) | `Nat.Prime p` |
| Suma acotada | `finSum f n` | `∑ k in Finset.range (n+1), f k` |
| Log | `log b n` | `Nat.log b n` |
| Sqrt | `sqrt n` | `Nat.sqrt n` |
| Resto con prueba | `n -( h ) m` | No existe (solo saturada) |

---

## 16. Conclusiones

### Lo que Peano tiene y Mathlib no (o no de esta forma)

1. **Bezout sobre ℕ en forma natural:** `∃ x y, a*x + b*y = gcd(a,b) ∨ b*y + a*x = gcd(a,b)`.
   Mathlib trabaja Bezout sobre ℤ; en ℕ la disjunción de signos es inevitable y Peano la trata
   explícitamente.

2. **Isomorfismo bidireccional explícito ℕ₀ ↔ ℕ:** los teoremas `isomorph_Λ_*` e `isomorph_Ψ_*`
   son puentes formalmente certificados. En Mathlib, `ℕ` es el tipo primitivo; no hay un
   isomorfismo análogo hacia afuera.

3. **Resta exacta con certificado:** `n -( h ) m` donde `h : Le m n`. En Mathlib no existe esta
   noción; la resta saturada es la única opción para `Nat`.

4. **`sqrtMod` y `logMod` como pares:** la devolución simultánea de `(valor, resto)` y su
   especificación conjunta. Mathlib tiene solo el valor.

5. **Newton's theorem directo sobre ℕ₀** (sin instanciar CommSemiring).

6. **Predecesor seguro `ρ`:** en Peano, el predecesor requiere una prueba `h : n ≠ 0`, haciendo
   imposible su aplicación incorrecta. `Nat.pred` en Lean4 devuelve `0` para `Nat.pred 0` (total
   y silenciosamente incorrecto en ciertos contextos).

7. **Axiomas de Peano como teoremas nombrados:** `Axioms.lean` hace explícitos los 8 axiomas
   clásicos como teoremas identificables. Mathlib los absorbe implícitamente en el tipo inductivo.

### Lo que Mathlib tiene y Peano no alcanza

1. **Tácticas `omega` y `norm_num`:** `omega` cierra en una línea cualquier desigualdad lineal
   sobre `Nat`; `norm_num` decide hechos numéricos concretos. Sobre `ℕ₀` ninguna de las dos
   funciona directamente. Esta es posiblemente la diferencia de productividad más visible.

2. **Jerarquía algebraica:** `ℕ` es simultáneamente `CommSemiring`, `LinearOrder`,
   `GCDMonoid`, `UniqueFactorizationMonoid`, y docenas más. Cada teorema abstracto se hereda
   automáticamente.

3. **Decidibilidad trivial:** `Nat.Prime`, `Nat.Coprime`, `n ∣ m`, y cualquier predicado
   computable son decidibles sin prueba adicional.

4. **`Nat.find`:** mínimo `n` satisfaciendo un predicado decidible, con certificados de
   minimalidad. No existe equivalente general en Peano.

5. **Factorización como `Finsupp`:** representación funcional de la factorización prima,
   con álgebra de exponentes (`factorization_mul`, `factorization_pow`).

6. **Logaritmo binario eficiente** (cuadrado iterado) y **logaritmo techo** (`clog`).

7. **Teoremas avanzados de combinatoria:** Vandermonde, Lucas, bounds precisos de `choose`.

8. **Teorema de Euclides** (infinitud de primos), **n-ésimo primo**, **función `φ`**,
   **congruencias**, **Fibonacci**, **Teorema Chino del Resto**.

9. **Generalidad:** Newton's Binomial en cualquier `CommSemiring`; GCD en cualquier `GCDMonoid`.

10. **`Nat.cast`:** coerción certificada de `Nat` hacia `ℤ`, `ℚ`, `ℝ`, cualquier
    `AddMonoidWithOne`. Permite transferir resultados de aritmética natural a otros tipos.

### Evaluación global

El proyecto Peano cubre solidamente el núcleo de la aritmética elemental de ℕ desde fundamentos
explícitos. La rama `makingdecidable` añade el puente booleano que Lean 4 da gratis a `Nat`,
consolidando la computabilidad del proyecto. La brecha con Mathlib no es de *corrección* ni de
*rigor* —ambas son formalizaciones correctas— sino de *escala*, *generalidad* y *ecosistema*:
Mathlib tiene decenas de años-persona de trabajo acumulado, integrando la aritmética de ℕ en
una teoría matemática mucho más amplia.

<!-- AUTO-UPDATE-2026-04-17-START -->
## Actualizacion de estado - 2026-04-17

- Estado del build: compila en el estado actual de la rama makingdecidable.
- Lagrange: cerrado en Sylow/Cosets con conteo por fibras y clases de cosets.
- GroupAction: sorries cerrados en orbit_stabilizer y orbits_partition.
- Sylow I: caso base n=0 cerrado; estructura separada en paso de Cauchy y paso de elevacion.
- Nota temporal: cauchy_minimal se apoya en un axioma explicito cauchy_minimal_axiom para continuar el desarrollo.
- Pendientes activos en Sylow: sylow_lift_from_cauchy, sylow_second, sylow_third.
- Objetivo proximo: reemplazar cauchy_minimal_axiom por demostracion interna y completar Sylow I.

<!-- AUTO-UPDATE-2026-04-17-END -->

