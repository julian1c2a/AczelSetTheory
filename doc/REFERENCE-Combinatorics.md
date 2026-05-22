# REFERENCE — Combinatorics

> **Proyecto**: Peano
> **Rama**: `migracion_de_REFERENCE`
> **Fecha**: 2026-05-10
> **Nodo**: `doc/REFERENCE-Combinatorics.md`
> **Volver al índice**: [REFERENCE.md](../REFERENCE.md)

---

## Módulos cubiertos

| Archivo | Namespace | Descripción |
| --- | --- | --- |
| `Peano/PeanoNat/Combinatorics/Pow.lean` | `Peano.Pow` | Potenciación sobre ℕ₀ |
| `Peano/PeanoNat/Combinatorics/Factorial.lean` | `Peano.Factorial` | Factorial y propiedades |
| `Peano/PeanoNat/Combinatorics/Summation.lean` | `Peano.Summation` | Sumas finitas y sumas de listas |
| `Peano/PeanoNat/Combinatorics/Product.lean` | `Peano.Product`, `Peano.Factorization` | Productos finitos y factorizaciones |
| `Peano/PeanoNat/Combinatorics/Fibonacci.lean` | `Peano.Fibonacci` | Sucesión de Fibonacci |
| `Peano/PeanoNat/Combinatorics/Binom.lean` | `Peano.Binom` | Coeficientes binomiales |
| `Peano/PeanoNat/Combinatorics/NewtonBinom.lean` | `Peano.NewtonBinom` | Binomio de Newton |
| `Peano/PeanoNat/Combinatorics/Perm.lean` | `Peano.Perm` | Permutaciones (FunPerm, Sym) |
| `Peano/PeanoNat/Combinatorics/Group.lean` | `Peano.Group` | Grupos finitos, subgrupos, potencias, orden |
| `Peano/PeanoNat/Combinatorics/Counting.lean` | `Peano.Counting` | Principios de conteo (stub) |
| `Peano/PeanoNat/Combinatorics/Sign.lean` | `Peano.Sign` | Signatura (stub) |
| `Peano/PeanoNat/Combinatorics/Orbit.lean` | `Peano.Orbit` | Órbitas (stub) |

Los módulos GroupTheory (First/Second/ThirdIsomorphism, QuotientGroup, CorrespondenceTheorem, NormalSubgroup, Action, Sylow) están documentados en [REFERENCE-GroupTheory.md](REFERENCE-GroupTheory.md).

---

## Módulo: Pow

**Archivo**: `Peano/PeanoNat/Combinatorics/Pow.lean`  
**Namespace**: `Peano.Pow`  
**Instancia registrada**: `instance : Pow ℕ₀ ℕ₀` usando `pow`. Sintaxis `a ^ b`.

---

### §1. `pow`

- **Tipo**: `def`
- **Módulo**: `Peano/PeanoNat/Combinatorics/Pow.lean`
- **Namespace**: `Peano.Pow`
- **Importancia**: `@importance: high`
- **Computable**: ✅
- **Firma Lean 4**:

  ```lean
  def pow : ℕ₀ → ℕ₀ → ℕ₀
    | _, .zero   => 𝟙
    | a, .succ n => mul (pow a n) a
  ```

- **Notación matemática**: $a^n$ con $a^0 = 1$ y $a^{n+1} = a^n \cdot a$.
- **Notación Lean**: `a ^ b` (via instancia `Pow ℕ₀ ℕ₀`)
- **Terminación**: `termination_by b`

---

### §2. Lemas fundamentales de `pow`

- **Importancia**: `@importance: high`

| Símbolo | Enunciado resumido |
| --- | --- |
| `pow_zero` | `a ^ 𝟘 = 𝟙` |
| `zero_pow` | `𝟘 < n → 𝟘 ^ n = 𝟘` |
| `one_pow` | `𝟙 ^ n = 𝟙` |
| `pow_one` | `a ^ 𝟙 = a` |
| `pow_succ` | `a ^ σ n = (a ^ n) * a` |
| `pow_ne_zero` | `a ≠ 𝟘 → a ^ n ≠ 𝟘` |
| `pow_two` | `a ^ 𝟚 = a * a` |

---

### §3. Lemas de monotonía y comparación de `pow`

- **Importancia**: `@importance: medium`

| Símbolo | Enunciado resumido |
| --- | --- |
| `pow_gt` | `1 < a → n ≤ m → a ^ n ≤ a ^ m` |
| `pow_ge_one` | `a ≠ 𝟘 → 𝟙 ≤ a ^ n` |
| `pow_lt_succ_base` | `a ^ n < σ a ^ n` |
| `pow_lt_succ_base_strong` | Versión fuerte de la cota anterior |
| `pow_lt_succ_exp` | `1 < a → n < a ^ n` |
| `pow_lt_mono_exp` | `1 < a ∧ m < n → a ^ m < a ^ n` |
| `pow_le_pow_right` | `a ≤ b → a ^ n ≤ b ^ n` |
| `pow_lt_mono_base` | `n ≠ 𝟘 ∧ a < b → a ^ n < b ^ n` |
| `pow_le_pow_left` | `m ≤ n ∧ 1 ≤ a → a ^ m ≤ a ^ n` |

---

### §4. Lemas algebraicos de `pow`

- **Importancia**: `@importance: medium`

| Símbolo | Enunciado resumido |
| --- | --- |
| `pow_add_eq_mul_pow` | `a ^ (m + n) = a ^ m * a ^ n` |
| `mul_pow_n_m_pow_k_m_eq_pow_nk_m` | `a ^ n * a ^ k = a ^ (n + k)` |
| `pow_pow_eq_pow_mul` | `(a ^ m) ^ n = a ^ (m * n)` |
| `pow_eq_zero_iff` | `a ^ n = 𝟘 ↔ a = 𝟘 ∧ n ≠ 𝟘` |
| `one_lt_pow` | `1 < a ∧ n ≠ 𝟘 → 1 < a ^ n` |
| `pow_eq_one_iff` | `a ^ n = 𝟙 ↔ (a = 𝟙 ∨ n = 𝟘)` |
| `pow_mul_comm` | `a ^ n * b ^ n = (a * b) ^ n` |
| `isomorph_Ψ_pow` | Compatibilidad con la función de isomorfismo Ψ |
| `isomorph_Λ_pow` | Compatibilidad con la función de isomorfismo Λ |

---

## Módulo: Factorial

**Archivo**: `Peano/PeanoNat/Combinatorics/Factorial.lean`  
**Namespace**: `Peano.Factorial`

---

### §5. `factorial`

- **Tipo**: `def`
- **Módulo**: `Peano/PeanoNat/Combinatorics/Factorial.lean`
- **Namespace**: `Peano.Factorial`
- **Importancia**: `@importance: high`
- **Computable**: ✅
- **Firma Lean 4**:

  ```lean
  def factorial : ℕ₀ → ℕ₀
    | .zero   => 𝟙
    | .succ n => mul (succ n) (factorial n)
  ```

- **Notación matemática**: $n! = 1 \cdot 2 \cdots n$, con $0! = 1$.
- **Terminación**: `termination_by n`

---

### §6. Lemas de `factorial`

- **Importancia**: `@importance: high`

| Símbolo | Enunciado resumido |
| --- | --- |
| `factorial_zero` | `factorial 𝟘 = 𝟙` |
| `factorial_one` | `factorial 𝟙 = 𝟙` |
| `factorial_two` | `factorial 𝟚 = 𝟚` |
| `factorial_succ` | `factorial (σ n) = (σ n) * factorial n` |
| `factorial_pos` | `𝟙 ≤ factorial n` |
| `factorial_ne_zero` | `factorial n ≠ 𝟘` |
| `factorial_ge_one` | `𝟙 ≤ factorial n` |
| `factorial_le_succ` | `factorial n ≤ factorial (σ n)` |
| `factorial_le_mono` | `m ≤ n → factorial m ≤ factorial n` |

---

## Módulo: Summation

**Archivo**: `Peano/PeanoNat/Combinatorics/Summation.lean`  
**Namespace**: `Peano.Summation`

---

### §7. `finSum`

- **Tipo**: `def`
- **Módulo**: `Peano/PeanoNat/Combinatorics/Summation.lean`
- **Namespace**: `Peano.Summation`
- **Importancia**: `@importance: high`
- **Computable**: ✅
- **Firma Lean 4**:

  ```lean
  def finSum (n : ℕ₀) (f : ℕ₀ → ℕ₀) : ℕ₀
    | .zero   => 𝟘
    | .succ n => add (finSum n f) (f n)
  ```

- **Notación matemática**: $\sum_{i=0}^{n-1} f(i)$.

---

### §8. Lemas de `finSum`

- **Importancia**: `@importance: high`

| Símbolo | Enunciado resumido |
| --- | --- |
| `finSum_zero` | `finSum 𝟘 f = 𝟘` |
| `finSum_succ` | `finSum (σ n) f = finSum n f + f n` |
| `finSum_zero_fn` | `finSum n (fun _ => 𝟘) = 𝟘` |
| `finSum_add_fn` | `finSum n (f + g) = finSum n f + finSum n g` |
| `finSum_mul_const` | `finSum n (fun i => k * f i) = k * finSum n f` |
| `finSum_mul_const_right` | `finSum n (fun i => f i * k) = finSum n f * k` |
| `finSum_le_of_le` | `(∀ i, f i ≤ g i) → finSum n f ≤ finSum n g` |
| `finSum_pos` | `n ≠ 𝟘 ∧ (∀ i, 𝟘 < f i) → 𝟘 < finSum n f` |
| `finSum_const` | `finSum n (fun _ => k) = n * k` |
| `finSum_succ_left` | `finSum (σ n) f = f 𝟘 + finSum n (fun i => f (σ i))` |
| `finSum_reverse` | `finSum n f = finSum n (fun i => f (n - 𝟙 - i))` |

---

### §9. `sum_list` y variantes

- **Importancia**: `@importance: medium`

| Símbolo | Firma resumida | Descripción |
| --- | --- | --- |
| `sum_list` | `List ℕ₀ → ℕ₀` | Suma de una lista de ℕ₀ |
| `sum_list_nil` | `sum_list [] = 𝟘` | |
| `sum_list_cons` | `sum_list (a :: l) = a + sum_list l` | |
| `sum_list_append` | `sum_list (l ++ m) = sum_list l + sum_list m` | |
| `sum_list_singleton` | `sum_list [a] = a` | |

---

## Módulo: Product / Factorization

**Archivo**: `Peano/PeanoNat/Combinatorics/Product.lean`  
**Namespaces**: `Peano.Product`, `Peano.Factorization`

---

### §10. `product_list` y `finProd`

- **Importancia**: `@importance: medium`

| Símbolo | Firma resumida | Descripción |
| --- | --- | --- |
| `product_list` | `List ℕ₀ → ℕ₀` | Producto de una lista |
| `product_nil` | `product_list [] = 𝟙` | Base |
| `product_cons` | `product_list (a :: l) = a * product_list l` | Paso |
| `product_append` | `product_list (l ++ m) = product_list l * product_list m` | |
| `product_list_singleton` | `product_list [a] = a` | |
| `finProd` | `(n : ℕ₀) → (ℕ₀ → ℕ₀) → ℕ₀` | $\prod_{i=0}^{n-1} f(i)$ |
| `finProd_zero` | `finProd 𝟘 f = 𝟙` | |
| `finProd_succ` | `finProd (σ n) f = finProd n f * f n` | |
| `finProd_one_fn` | `finProd n (fun _ => 𝟙) = 𝟙` | |
| `finProd_zero_fn` | Si alguna `f i = 𝟘` → `finProd = 𝟘` | |
| `finProd_succ_left` | Variante desde la izquierda | |

---

### §11. Factorizaciones: `factorValue` y `product_factorization`

- **Importancia**: `@importance: medium`

| Símbolo | Firma resumida | Descripción |
| --- | --- | --- |
| `factorValue` | `FactFSet → ℕ₂ → ℕ₀` | Valor del exponente del primo `p` en la factorización |
| `product_factorization` | `FactFSet → ℕ₀` | Valor numérico de la factorización: $\prod p^e$ |
| `product_factorization_empty` | `product_factorization ∅ = 𝟙` | |
| `product_factorization_singleton` | `product_factorization {(p,e)} = p ^ e` | |

---

## Módulo: Fibonacci

**Archivo**: `Peano/PeanoNat/Combinatorics/Fibonacci.lean`  
**Namespace**: `Peano.Fibonacci`

---

### §12. `fib` / `fibPair` / `fibList`

- **Tipo**: `def`
- **Módulo**: `Peano/PeanoNat/Combinatorics/Fibonacci.lean`
- **Namespace**: `Peano.Fibonacci`
- **Importancia**: `@importance: medium`
- **Computable**: ✅
- **Firma Lean 4**:

  ```lean
  def fibPair : ℕ₀ → ℕ₀ × ℕ₀
    | .zero   => (𝟙, 𝟘)
    | .succ n => let (a, b) := fibPair n; (a + b, a)

  def fib (n : ℕ₀) : ℕ₀ := (fibPair n).1

  def fibList (n : ℕ₀) : List ℕ₀ := (List.range n).map fib
  ```

- **Notación matemática**: $F_0 = 0, F_1 = 1, F_{n+2} = F_n + F_{n+1}$.
- **Nota**: `fibPair` evita la doble recursión; la implementación es lineal.

| Símbolo | Enunciado resumido |
| --- | --- |
| `fib_zero` | `fib 𝟘 = 𝟘` (con la convención $F_0 = 0$) |
| `fib_one` | `fib 𝟙 = 𝟙` |
| `fib_succ_succ` | `fib (σ (σ n)) = fib n + fib (σ n)` |
| `fib_two` | `fib 𝟚 = 𝟙` |
| `fibList_zero` | `fibList 𝟘 = []` |
| `fibList_succ` | `fibList (σ n) = fibList n ++ [fib n]` |

---

## Módulo: Binom

**Archivo**: `Peano/PeanoNat/Combinatorics/Binom.lean`  
**Namespace**: `Peano.Binom`

---

### §13. `binom`

- **Tipo**: `def`
- **Módulo**: `Peano/PeanoNat/Combinatorics/Binom.lean`
- **Namespace**: `Peano.Binom`
- **Importancia**: `@importance: high`
- **Computable**: ✅
- **Firma Lean 4**:

  ```lean
  def binom : ℕ₀ → ℕ₀ → ℕ₀
    | _, .zero         => 𝟙
    | .zero, .succ _   => 𝟘
    | .succ n, .succ k => binom n k + binom n (succ k)
  ```

- **Notación matemática**: $\binom{n}{k}$ — el coeficiente binomial.
- **Terminación**: recursión estructural sobre ambos argumentos.

---

### §14. Lemas de `binom`

- **Importancia**: `@importance: high`

| Símbolo | Enunciado resumido |
| --- | --- |
| `binom_zero_zero` | `binom 𝟘 𝟘 = 𝟙` |
| `binom_zero_succ` | `binom 𝟘 (σ k) = 𝟘` |
| `binom_succ_zero` | `binom (σ n) 𝟘 = 𝟙` |
| `binom_pascal` | `binom (σ n) (σ k) = binom n k + binom n (σ k)` (triángulo de Pascal) |
| `binom_n_zero` | `binom n 𝟘 = 𝟙` |
| `binom_n_one` | `binom n 𝟙 = n` |
| `binom_eq_zero_of_gt` | `k > n → binom n k = 𝟘` |
| `binom_self` | `binom n n = 𝟙` |
| `binom_pos` | `k ≤ n → 𝟘 < binom n k` |
| `binom_one` | `binom 𝟙 k = ...` |
| `binom_succ_n_by_n` | `binom (σ n) n = σ n` |
| `binom_mul_factorials` | `binom n k * k! * (n-k)! = n!` |
| `prime_dvd_binom_prime` | `p` primo, `0 < k < p` → `p ∣ binom p k` |
| `binom_prime_row` | Todos los `binom p k` con `0 < k < p` son divisibles por `p` |
| `binom_pr_p_mod` | `binom (p·r) p ≡ r [MOD p]` |
| `binom_pow_p_mod` | Relación entre potencias y binomiales módulo `p` |

---

## Módulo: NewtonBinom

**Archivo**: `Peano/PeanoNat/Combinatorics/NewtonBinom.lean`  
**Namespace**: `Peano.NewtonBinom`

---

### §15. Binomio de Newton

- **Importancia**: `@importance: high`

| Símbolo | Firma resumida | Descripción |
| --- | --- | --- |
| `binomTerm` | `ℕ₀ → ℕ₀ → ℕ₀ → ℕ₀ → ℕ₀` | Término k del binomio: `binom(n,k) * a^(n-k) * b^k` |
| `binomTerm_zero` | `binomTerm n a b 𝟘 = a^n` | Término k=0 |
| `binomTerm_self` | `binomTerm n a b n = b^n` | Término k=n |
| `newton_binom` | `(a+b)^n = finSum (σ n) (binomTerm n a b)` | **Binomio de Newton** |
| `sum_binom_eq_pow_two` | `∑_{k=0}^{n} binom n k = 2^n` | Suma de la fila de Pascal |
| `pow_add_split` | `(a+b)^n = ∑_k binom(n,k) * a^k * b^(n-k)` | Forma alternativa |
| `exists_nm_growth` | Lema de crecimiento exponencial: $\exists n, m$ con $n^m$ acotado | |

---

## Módulo: Perm

**Archivo**: `Peano/PeanoNat/Combinatorics/Perm.lean`  
**Namespace**: `Peano.Perm`

El módulo está en construcción (§3-§4 marcados como TODO). Solo documenta los símbolos completados.

---

### §16. `FunPerm.comp` / `Sym`

- **Importancia**: `@importance: medium`

| Símbolo | Firma resumida | Descripción |
| --- | --- | --- |
| `FunPerm.comp` | `FunPerm A → FunPerm A → FunPerm A` | Composición de dos permutaciones (como `FunTable`) |
| `Sym` | `abbrev Sym (A : ℕ₀FSet) := FunPerm A` | El grupo simétrico de `A` (como tipo) |
| `card_Sym` | `factorial A.card = factorial A.card` | Placeholder (la cardinalidad `\|Sym A\| = n!` es trabajo futuro) |

---

## Módulo: Group

**Archivo**: `Peano/PeanoNat/Combinatorics/Group.lean`  
**Namespace**: `Peano.Group`

---

### §17. `FinGroup`

- **Tipo**: `structure`
- **Módulo**: `Peano/PeanoNat/Combinatorics/Group.lean`
- **Namespace**: `Peano.Group`
- **Importancia**: `@importance: high`
- **Computable**: ✅ (con `DecidableEq`)
- **Firma Lean 4**:

  ```lean
  structure FinGroup (α : Type) [DecidableEq α] [LT α] [StrictLinearOrder α] where
    carrier  : FSet α
    op       : BinOpOn carrier
    id       : α
    inv      : MapOn carrier carrier
    id_in    : id ∈ carrier.elems
    op_assoc : ∀ a b c, a ∈ carrier → b ∈ carrier → c ∈ carrier →
                 op (op a b) c = op a (op b c)
    op_id    : ∀ a, a ∈ carrier → op a id = a ∧ op id a = a
    op_inv   : ∀ a, a ∈ carrier → op a (inv a) = id ∧ op (inv a) a = id
  ```

- **Notación matemática**: Un grupo finito $(G, \cdot, e, {}^{-1})$ donde $G$ es un `FSet`.
- **Alias**: `ℕ₀FinGroup = FinGroup ℕ₀`

---

### §18. Lemas elementales de `FinGroup`

- **Importancia**: `@importance: high`

| Símbolo | Enunciado resumido |
| --- | --- |
| `id_unique` | El neutro es único |
| `inv_mem` | `a ∈ G → G.inv a ∈ G` |
| `op_mem` | `a, b ∈ G → G.op a b ∈ G` |
| `op_cancel_left` | `a·x = a·y → x = y` |
| `op_cancel_right` | `x·a = y·a → x = y` |
| `inv_inv_eq` | `G.inv (G.inv a) = a` |
| `inv_id_eq` | `G.inv G.id = G.id` |
| `inv_op_eq` | `G.inv (G.op a b) = G.op (G.inv b) (G.inv a)` |
| `inv_unique` | Unicidad del inverso: si `a·b = id ∧ b·a = id` → `b = G.inv a` |

---

### §19. `gpow` — potencia iterada

- **Tipo**: `def` (noncomputable para `order`)
- **Importancia**: `@importance: high`
- **Firma Lean 4**:

  ```lean
  def gpow (G : FinGroup α) (g : α) : ℕ₀ → α
    | .zero   => G.id
    | .succ n => G.op (gpow G g n) g
  ```

- **Notación matemática**: $g^n$ en el grupo $G$.

| Símbolo | Enunciado resumido |
| --- | --- |
| `gpow_zero` | `gpow G g 𝟘 = G.id` |
| `gpow_succ` | `gpow G g (σ n) = G.op (gpow G g n) g` |
| `gpow_one` | `gpow G g 𝟙 = g` (si `g ∈ G`) |
| `gpow_mem` | `gpow G g n ∈ G.carrier` para todo `n` |
| `gpow_add` | `gpow G g (m + n) = G.op (gpow G g m) (gpow G g n)` |
| `gpow_comm_single` | `G.op g (gpow G g n) = G.op (gpow G g n) g` |
| `gpow_inv` | `gpow G (G.inv g) n = G.inv (gpow G g n)` |
| `gpow_mul_order_eq_id` | `gpow G g (k * ord(g)) = G.id` |
| `gpow_mod_order` | `gpow G g n = gpow G g (n mod ord(g))` |

---

### §20. `order` — orden de un elemento

- **Tipo**: `noncomputable def`
- **Módulo**: `Peano/PeanoNat/Combinatorics/Group.lean`
- **Namespace**: `Peano.Group`
- **Importancia**: `@importance: high`
- **Computable**: ❌ (usa WOP clásico)
- **Firma Lean 4**:

  ```lean
  noncomputable def order (G : FinGroup α) (g : α) (hg : g ∈ G.carrier.elems) : ℕ₀
  ```

- **Notación matemática**: $\mathrm{ord}(g)$ — el mínimo $n > 0$ tal que $g^n = e$.

| Símbolo | Enunciado resumido |
| --- | --- |
| `order_pos` | `0 < ord(g)` |
| `gpow_order_eq_id` | `g^(ord(g)) = G.id` |
| `order_ne_zero` | `ord(g) ≠ 𝟘` |
| `order_minimal` | `g^m = id ∧ m > 0 → ord(g) ≤ m` |
| `order_le_card` | `ord(g) ≤ \|G\|` |

---

### §21. `Subgroup`

- **Tipo**: `structure`
- **Módulo**: `Peano/PeanoNat/Combinatorics/Group.lean`
- **Namespace**: `Peano.Group`
- **Importancia**: `@importance: high`
- **Firma Lean 4**:

  ```lean
  structure Subgroup (G : FinGroup α) where
    carrier    : FSet α
    nonempty   : ∃ a, a ∈ carrier.elems
    subset     : ∀ a, a ∈ carrier.elems → a ∈ G.carrier.elems
    op_closed  : ∀ a b, a ∈ carrier.elems → b ∈ carrier.elems → G.op a b ∈ carrier.elems
    id_in      : G.id ∈ carrier.elems
    inv_closed : ∀ a, a ∈ carrier.elems → G.inv a ∈ carrier.elems
  ```

- **Notación matemática**: $H \leq G$.

---

### §22. Lemas y constructores de `Subgroup`

- **Importancia**: `@importance: high`

| Símbolo | Descripción |
| --- | --- |
| `Subgroup.op_inv_closed` | `a, b ∈ H → G.op a (G.inv b) ∈ H` |
| `subgroup_of_op_inv_closed` | Constructor por criterio de un paso (no vacío + `a·b⁻¹ ∈ S`) |
| `trivialSubgroup` | El subgrupo trivial `{e}` |
| `improperSubgroup` | El subgrupo impropio `G` como subgrupo de sí mismo |
| `Subgroup.IsTrivial` | `H.carrier.card = 𝟙` |
| `Subgroup.IsProper` | `H.carrier.card ≠ G.carrier.card` |
| `Subgroup.IsNormal` | `∀ g ∈ G, ∀ n ∈ N, g·n·g⁻¹ ∈ N` |
| `trivialSubgroup_normal` | El subgrupo trivial es normal |
| `improperSubgroup_normal` | El subgrupo impropio es normal |

---

### §23. Subgrupos cíclicos y normalidad

- **Importancia**: `@importance: high`

| Símbolo | Descripción |
| --- | --- |
| `cyclicCarrier` | `FSet` de las potencias de `g` en `G` |
| `cyclicCarrier_id_in` | `G.id ∈ cyclicCarrier G g` |
| `cyclicCarrier_mem_iff` | Caracterización de `cyclicCarrier` |
| `cyclicSubgroup` | Subgrupo cíclico `⟨g⟩` (via criterio de un paso) |
| `cyclicSubgroup'` | Construcción directa de `⟨g⟩` |
| `Subgroup.inter` | Intersección de dos subgrupos |
| `Subgroup.inter_subset_left` / `inter_subset_right` | Inclusiones de la intersección |
| `Subgroup.inter_normal_of_normal` | Intersección de normales es normal |
| `Subgroup.ext_carrier` | Extensionalidad: igualdad de soportes → igualdad |
| `instDecidableEqSubgroup` | `DecidableEq (Subgroup G)` |
| `instLTSubgroup` | `LT (Subgroup G)` |

---

### §24. `GroupHom`

- **Tipo**: `structure`
- **Módulo**: `Peano/PeanoNat/Combinatorics/Group.lean`
- **Namespace**: `Peano.Group`
- **Importancia**: `@importance: high`
- **Firma Lean 4**:

  ```lean
  structure GroupHom (G H : FinGroup α) where
    map     : MapOn G.carrier H.carrier
    map_op  : ∀ a b, a ∈ G.carrier → b ∈ G.carrier →
                map (G.op a b) = H.op (map a) (map b)
    map_id  : map G.id = H.id
    map_inv : ∀ a, a ∈ G.carrier → map (G.inv a) = H.inv (map a)
  ```

- **Notación matemática**: Un homomorfismo de grupos $\phi : G \to H$ que preserva la operación, el neutro y la inversa.

---

## Módulos stub (sin exportaciones formales)

Los siguientes módulos están declarados pero contienen solo secciones comentadas o marcadores TODO. No exportan símbolos:

| Módulo | Namespace | Estado |
| --- | --- | --- |
| `Counting.lean` | `Peano.Counting` | Stub — §1–3 vacíos |
| `Sign.lean` | `Peano.Sign` | Stub — §1–3 vacíos |
| `Orbit.lean` | `Peano.Orbit` | Stub — §1–2 vacíos |

---

## Resumen de símbolos exportados por módulo

| Módulo | Símbolos clave | Importance |
| --- | --- | --- |
| `Pow` | `pow`, `pow_zero`, `pow_succ`, `pow_add_eq_mul_pow`, `pow_pow_eq_pow_mul` | high |
| `Factorial` | `factorial`, `factorial_succ`, `factorial_pos` | high |
| `Summation` | `finSum`, `finSum_succ`, `finSum_const`, `sum_list` | high |
| `Product` | `product_list`, `finProd`, `finProd_succ` | medium |
| `Factorization` | `factorValue`, `product_factorization` | medium |
| `Fibonacci` | `fib`, `fibPair`, `fib_succ_succ` | medium |
| `Binom` | `binom`, `binom_pascal`, `binom_mul_factorials`, `prime_dvd_binom_prime` | high |
| `NewtonBinom` | `newton_binom`, `sum_binom_eq_pow_two`, `binomTerm` | high |
| `Group` | `FinGroup`, `Subgroup`, `GroupHom`, `gpow`, `order`, `cyclicSubgroup` | high |
