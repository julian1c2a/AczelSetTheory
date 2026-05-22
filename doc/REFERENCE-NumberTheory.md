# REFERENCE — NumberTheory

> **Proyecto**: Peano
> **Rama**: `migracion_de_REFERENCE`
> **Fecha**: 2026-05-10
> **Nodo**: `doc/REFERENCE-NumberTheory.md`
> **Volver al índice**: [REFERENCE.md](../REFERENCE.md)

---

## Módulos cubiertos

| Archivo | Namespace exportado | Descripción |
| --- | --- | --- |
| `Peano/PeanoNat/NumberTheory/ModEq.lean` | `Peano.ModEq` | Congruencia modular |
| `Peano/PeanoNat/NumberTheory/Totient.lean` | `Peano.Totient` | Función de Euler φ |
| `Peano/PeanoNat/NumberTheory/ChineseRemainder.lean` | `Peano.CRT` | Teorema Chino del Residuo |
| `Peano/PeanoNat/NumberTheory/Fermat.lean` | `Peano.Fermat` | Pequeño Teorema de Fermat |
| `Peano/PeanoNat/NumberTheory/Wilson.lean` | `Peano.Wilson` | Teorema de Wilson |

**Axioma**: `@axiom_system: Peano`
**Importaciones clave**: `Peano.PeanoNat.Arith`, `Peano.PeanoNat.Primes`, `Peano.PeanoNat.Combinatorics.Pow`

---

## Módulo: ModEq

### §1. Lemas auxiliares de `mod`

Estos lemas se exportan porque otros módulos los necesitan directamente.

---

#### §1.1. `mod_zero_right`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/ModEq.lean`
- **Namespace**: `Peano.ModEq`
- **Importancia**: `@importance: medium`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  theorem mod_zero_right (a : ℕ₀) : mod a 𝟘 = 𝟘
  ```

- **Notación matemática**: $a \bmod 0 = 0$ (por definición de `divMod`).

---

#### §1.2. `mod_zero_left`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/ModEq.lean`
- **Namespace**: `Peano.ModEq`
- **Importancia**: `@importance: medium`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  theorem mod_zero_left (n : ℕ₀) : mod 𝟘 n = 𝟘
  ```

- **Notación matemática**: $0 \bmod n = 0$.

---

#### §1.3. `mod_self`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/ModEq.lean`
- **Namespace**: `Peano.ModEq`
- **Importancia**: `@importance: medium`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  theorem mod_self (n : ℕ₀) : mod n n = 𝟘
  ```

- **Notación matemática**: $n \bmod n = 0$.

---

#### §1.4. `mod_mod`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/ModEq.lean`
- **Namespace**: `Peano.ModEq`
- **Importancia**: `@importance: medium`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  theorem mod_mod (a n : ℕ₀) : mod (mod a n) n = mod a n
  ```

- **Notación matemática**: $(a \bmod n) \bmod n = a \bmod n$ (idempotencia).

---

#### §1.5. `add_mod`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/ModEq.lean`
- **Namespace**: `Peano.ModEq`
- **Importancia**: `@importance: medium`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  theorem add_mod (a b n : ℕ₀) :
      mod (add a b) n = mod (add (mod a n) (mod b n)) n
  ```

- **Notación matemática**: $(a + b) \bmod n = ((a \bmod n) + (b \bmod n)) \bmod n$.

---

#### §1.6. `mul_mod`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/ModEq.lean`
- **Namespace**: `Peano.ModEq`
- **Importancia**: `@importance: medium`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  theorem mul_mod (a b n : ℕ₀) :
      mod (mul a b) n = mod (mul (mod a n) (mod b n)) n
  ```

- **Notación matemática**: $(a \cdot b) \bmod n = ((a \bmod n) \cdot (b \bmod n)) \bmod n$.

---

### §2. `ModEq` — Definición principal

- **Tipo**: `def`
- **Módulo**: `Peano/PeanoNat/NumberTheory/ModEq.lean`
- **Namespace**: `Peano.ModEq`
- **Importancia**: `@importance: high`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  def ModEq (n a b : ℕ₀) : Prop := mod a n = mod b n
  ```

- **Notación matemática**: $a \equiv b \pmod{n}$ si y solo si $a \bmod n = b \bmod n$.
- **Notación Lean**: `a ≡ b [MOD n]` (precedencia 50)

---

### §3. Relación de equivalencia

#### §3.1. `modEq_refl`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/ModEq.lean`
- **Namespace**: `Peano.ModEq`
- **Importancia**: `@importance: high`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  theorem modEq_refl (n a : ℕ₀) : a ≡ a [MOD n]
  ```

---

#### §3.2. `modEq_symm`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/ModEq.lean`
- **Namespace**: `Peano.ModEq`
- **Importancia**: `@importance: high`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  theorem modEq_symm {n a b : ℕ₀} (h : a ≡ b [MOD n]) : b ≡ a [MOD n]
  ```

---

#### §3.3. `modEq_trans`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/ModEq.lean`
- **Namespace**: `Peano.ModEq`
- **Importancia**: `@importance: high`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  theorem modEq_trans {n a b c : ℕ₀} (h1 : a ≡ b [MOD n]) (h2 : b ≡ c [MOD n]) :
      a ≡ c [MOD n]
  ```

---

### §4. Compatibilidad con operaciones

#### §4.1. `modEq_add`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/ModEq.lean`
- **Namespace**: `Peano.ModEq`
- **Importancia**: `@importance: high`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  theorem modEq_add {n a b c d : ℕ₀}
      (h1 : a ≡ b [MOD n]) (h2 : c ≡ d [MOD n]) :
      add a c ≡ add b d [MOD n]
  ```

- **Notación matemática**: Si $a \equiv b$ y $c \equiv d \pmod{n}$, entonces $a + c \equiv b + d \pmod{n}$.

---

#### §4.2. `modEq_mul`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/ModEq.lean`
- **Namespace**: `Peano.ModEq`
- **Importancia**: `@importance: high`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  theorem modEq_mul {n a b c d : ℕ₀}
      (h1 : a ≡ b [MOD n]) (h2 : c ≡ d [MOD n]) :
      mul a c ≡ mul b d [MOD n]
  ```

- **Notación matemática**: Si $a \equiv b$ y $c \equiv d \pmod{n}$, entonces $a \cdot c \equiv b \cdot d \pmod{n}$.

---

#### §4.3. `modEq_pow`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/ModEq.lean`
- **Namespace**: `Peano.ModEq`
- **Importancia**: `@importance: high`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  theorem modEq_pow {n a b : ℕ₀} (k : ℕ₀)
      (h : a ≡ b [MOD n]) :
      pow a k ≡ pow b k [MOD n]
  ```

- **Notación matemática**: Si $a \equiv b \pmod{n}$, entonces $a^k \equiv b^k \pmod{n}$.

---

### §5. Conexión con divisibilidad

#### §5.1. `mod_eq_zero_iff_dvd`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/ModEq.lean`
- **Namespace**: `Peano.ModEq`
- **Importancia**: `@importance: high`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  theorem mod_eq_zero_iff_dvd {a n : ℕ₀} (h_n : n ≠ 𝟘) :
      mod a n = 𝟘 ↔ n ∣ a
  ```

- **Notación matemática**: $a \bmod n = 0 \iff n \mid a$ (para $n \neq 0$).

---

#### §5.2. `modEq_zero_iff_dvd`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/ModEq.lean`
- **Namespace**: `Peano.ModEq`
- **Importancia**: `@importance: high`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  theorem modEq_zero_iff_dvd {a n : ℕ₀} (h_n : n ≠ 𝟘) :
      a ≡ 𝟘 [MOD n] ↔ n ∣ a
  ```

- **Notación matemática**: $a \equiv 0 \pmod{n} \iff n \mid a$.

---

#### §5.3. `modEq_zero_of_dvd`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/ModEq.lean`
- **Namespace**: `Peano.ModEq`
- **Importancia**: `@importance: medium`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  theorem modEq_zero_of_dvd {a n : ℕ₀} (h_n : n ≠ 𝟘) (h : n ∣ a) :
      a ≡ 𝟘 [MOD n]
  ```

---

### §6. Propiedades adicionales

#### §6.1. `modEq_mod`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/ModEq.lean`
- **Namespace**: `Peano.ModEq`
- **Importancia**: `@importance: medium`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  theorem modEq_mod (a n : ℕ₀) : a ≡ mod a n [MOD n]
  ```

- **Notación matemática**: $a \equiv (a \bmod n) \pmod{n}$.

---

#### §6.2. `modEq_one`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/ModEq.lean`
- **Namespace**: `Peano.ModEq`
- **Importancia**: `@importance: medium`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  theorem modEq_one (a b : ℕ₀) : a ≡ b [MOD 𝟙]
  ```

- **Notación matemática**: Todo par es congruente módulo 1: $a \equiv b \pmod{1}$.

---

#### §6.3. `modEq_add_right`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/ModEq.lean`
- **Namespace**: `Peano.ModEq`
- **Importancia**: `@importance: medium`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  theorem modEq_add_right (a n : ℕ₀) : a ≡ add a n [MOD n]
  ```

- **Notación matemática**: $a \equiv a + n \pmod{n}$ (sumar el módulo no cambia la clase).

---

#### §6.4. `instDecidableModEq`

- **Tipo**: `instance`
- **Módulo**: `Peano/PeanoNat/NumberTheory/ModEq.lean`
- **Namespace**: `Peano.ModEq`
- **Importancia**: `@importance: medium`
- **Computable**: ✅
- **Firma Lean 4**:

  ```lean
  instance instDecidableModEq (n a b : ℕ₀) : Decidable (ModEq n a b)
  ```

- **Descripción**: La congruencia modular es decidible (se reduce a igualdad de `mod`).

---

## Módulo: Totient

### §7. `totient`

- **Tipo**: `def`
- **Módulo**: `Peano/PeanoNat/NumberTheory/Totient.lean`
- **Namespace**: `Peano.Totient`
- **Importancia**: `@importance: high`
- **Computable**: ✅
- **Firma Lean 4**:

  ```lean
  def totient (n : ℕ₀) : ℕ₀ :=
    lengthₚ ((range_from_one n).filter (fun d => decide (gcd d n = 𝟙)))
  ```

- **Notación matemática**: $\varphi(n) = |\{k \in \{1,\ldots,n\} \mid \gcd(k,n)=1\}|$ (función de Euler).
- **Dependencias directas**: `lengthₚ`, `range_from_one`, `gcd` (de `Arith`)

---

### §8. `totient_zero`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/Totient.lean`
- **Namespace**: `Peano.Totient`
- **Importancia**: `@importance: low`
- **Firma Lean 4**:

  ```lean
  theorem totient_zero : totient 𝟘 = 𝟘
  ```

- **Notación matemática**: $\varphi(0) = 0$.

---

### §9. `totient_one`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/Totient.lean`
- **Namespace**: `Peano.Totient`
- **Importancia**: `@importance: low`
- **Firma Lean 4**:

  ```lean
  theorem totient_one : totient 𝟙 = 𝟙
  ```

- **Notación matemática**: $\varphi(1) = 1$.

---

### §10. `totient_two`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/Totient.lean`
- **Namespace**: `Peano.Totient`
- **Importancia**: `@importance: low`
- **Firma Lean 4**:

  ```lean
  theorem totient_two : totient 𝟚 = 𝟙
  ```

- **Notación matemática**: $\varphi(2) = 1$.

---

### §11. `totient_le`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/Totient.lean`
- **Namespace**: `Peano.Totient`
- **Importancia**: `@importance: medium`
- **Firma Lean 4**:

  ```lean
  theorem totient_le (n : ℕ₀) : le₀ (totient n) n
  ```

- **Notación matemática**: $\varphi(n) \leq n$.

---

### §12. `totient_pos`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/Totient.lean`
- **Namespace**: `Peano.Totient`
- **Importancia**: `@importance: medium`
- **Firma Lean 4**:

  ```lean
  theorem totient_pos {n : ℕ₀} (h : n ≠ 𝟘) : le₀ 𝟙 (totient n)
  ```

- **Notación matemática**: $\varphi(n) \geq 1$ para todo $n \geq 1$.

---

### §13. `totient_prime`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/Totient.lean`
- **Namespace**: `Peano.Totient`
- **Importancia**: `@importance: high`
- **Firma Lean 4**:

  ```lean
  theorem totient_prime {p : ℕ₀} (hp : Arith.Prime p) :
      totient p = sub p 𝟙
  ```

- **Notación matemática**: Si $p$ es primo, $\varphi(p) = p - 1$.

---

### §14. `instDecidableEqTotient`

- **Tipo**: `instance`
- **Módulo**: `Peano/PeanoNat/NumberTheory/Totient.lean`
- **Namespace**: `Peano.Totient`
- **Importancia**: `@importance: low`
- **Computable**: ✅
- **Firma Lean 4**:

  ```lean
  instance instDecidableEqTotient (n : ℕ₀) (m : ℕ₀) : Decidable (totient n = m)
  ```

---

### §15. Lemas auxiliares exportados (lista)

Los siguientes lemas se exportan de `Peano.Totient` por ser usados en pruebas externas. Importancia `@importance: low` salvo indicación.

| Símbolo | Tipo | Descripción |
| --- | --- | --- |
| `lengthₚ_append` | `theorem` | `lengthₚ (l ++ l') = add (lengthₚ l) (lengthₚ l')` |
| `lengthₚ_singleton` | `theorem` | `lengthₚ [a] = 𝟙` |
| `lengthₚ_range_from_one` | `theorem` | `lengthₚ (range_from_one n) = n` |
| `lengthₚ_filter_le` | `theorem` | Longitud del filtrado ≤ longitud original |
| `filter_append_singleton` | `theorem` | Distribución de `filter` sobre `append` con singleton |
| `filter_all_true` | `theorem` | Si todos satisfacen el predicado, `filter` no elimina nada |
| `mem_range_from_one_pos` | `theorem` | `k ∈ range_from_one n → k ≠ 𝟘` |
| `mem_range_from_one_le` | `theorem` | `k ∈ range_from_one n → le₀ k n` |

---

## Módulo: ChineseRemainder

### §16. `chinese_remainder`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/ChineseRemainder.lean`
- **Namespace**: `Peano.CRT`
- **Importancia**: `@importance: high`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  theorem chinese_remainder {m n : ℕ₀} (hcop : Coprime m n) (a b : ℕ₀) :
      ∃ x : ℕ₀, ModEq m x a ∧ ModEq n x b
  ```

- **Notación matemática**: **Teorema Chino del Residuo**: dados $m, n$ coprimos, para cualesquiera $a, b \in \mathbb{N}_0$ existe $x$ tal que $x \equiv a \pmod{m}$ y $x \equiv b \pmod{n}$.
- **Estrategia de prueba**: Identidad de Bézout (`bezout_natform`) para construir el inverso modular explícito.
- **Dependencias directas**: `Peano.Arith.Coprime`, `Peano.Arith.bezout_natform`, `Peano.ModEq`

---

## Módulo: Fermat

### §17. `fermat_little_theorem`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/Fermat.lean`
- **Namespace**: `Peano.Fermat`
- **Importancia**: `@importance: high`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  theorem fermat_little_theorem (a p : ℕ₀) (hp : Arith.Prime p) :
      mod (pow a p) p = mod a p
  ```

- **Notación matemática**: **Pequeño Teorema de Fermat**: para todo primo $p$ y todo $a \in \mathbb{N}_0$, $a^p \equiv a \pmod{p}$.
- **Estrategia de prueba**: Inducción sobre $a$. En el paso inductivo, se aplica el Binomio de Newton: $(a+1)^p = \sum_{k=0}^{p} \binom{p}{k} a^k$; los términos con $0 < k < p$ son divisibles por $p$ (primo divide a $\binom{p}{k}$).
- **Dependencias directas**: `Peano.NewtonBinom`, `Peano.Binom`, `Peano.Factorial`, `Peano.Totient`, `Peano.ModEq`

---

## Módulo: Wilson

### §18. `wilson`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/NumberTheory/Wilson.lean`
- **Namespace**: `Peano.Wilson`
- **Importancia**: `@importance: high`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  theorem wilson {p : ℕ₀} (hp : Prime p) : p ∣ add (factorial (sub p 𝟙)) 𝟙
  ```

- **Notación matemática**: **Teorema de Wilson**: para todo primo $p$, $p \mid (p-1)! + 1$, equivalentemente $(p-1)! \equiv -1 \pmod{p}$.
- **Estrategia de prueba**:
  1. Definir `modInv p a = pow a (sub p 𝟚) mod p` (privada).
  2. Probar `pow a (sub p 𝟙) ≡ 1 [MOD p]` (desde Fermat + cancelación).
  3. Probar que `modInv` es involución sobre `{1,…,p-1}`.
  4. Emparejar `{2,…,p-2}` via `modInv` (sin puntos fijos), cada par ≡ 1.
  5. Concluir $(p-2)! \equiv 1$ y $(p-1)! \equiv p-1 \equiv -1 \pmod{p}$.
- **Dependencias directas**: `Peano.Fermat`, `Peano.Factorial`, `Peano.ModEq`, `Peano.Primes`

---

## Resumen de exports

| Símbolo | Módulo | Tipo | Importance |
| --- | --- | --- | --- |
| `mod_zero_right` | ModEq | `theorem` | medium |
| `mod_zero_left` | ModEq | `theorem` | medium |
| `mod_self` | ModEq | `theorem` | medium |
| `mod_mod` | ModEq | `theorem` | medium |
| `add_mod` | ModEq | `theorem` | medium |
| `mul_mod` | ModEq | `theorem` | medium |
| `ModEq` | ModEq | `def` | high |
| `modEq_refl` | ModEq | `theorem` | high |
| `modEq_symm` | ModEq | `theorem` | high |
| `modEq_trans` | ModEq | `theorem` | high |
| `modEq_add` | ModEq | `theorem` | high |
| `modEq_mul` | ModEq | `theorem` | high |
| `modEq_pow` | ModEq | `theorem` | high |
| `mod_eq_zero_iff_dvd` | ModEq | `theorem` | high |
| `modEq_zero_iff_dvd` | ModEq | `theorem` | high |
| `modEq_zero_of_dvd` | ModEq | `theorem` | medium |
| `modEq_mod` | ModEq | `theorem` | medium |
| `modEq_one` | ModEq | `theorem` | medium |
| `modEq_add_right` | ModEq | `theorem` | medium |
| `instDecidableModEq` | ModEq | `instance` | medium |
| `totient` | Totient | `def` | high |
| `totient_zero` | Totient | `theorem` | low |
| `totient_one` | Totient | `theorem` | low |
| `totient_two` | Totient | `theorem` | low |
| `totient_le` | Totient | `theorem` | medium |
| `totient_pos` | Totient | `theorem` | medium |
| `totient_prime` | Totient | `theorem` | high |
| `instDecidableEqTotient` | Totient | `instance` | low |
| `lengthₚ_append` | Totient | `theorem` | low |
| `lengthₚ_singleton` | Totient | `theorem` | low |
| `lengthₚ_range_from_one` | Totient | `theorem` | low |
| `lengthₚ_filter_le` | Totient | `theorem` | low |
| `filter_append_singleton` | Totient | `theorem` | low |
| `filter_all_true` | Totient | `theorem` | low |
| `mem_range_from_one_pos` | Totient | `theorem` | low |
| `mem_range_from_one_le` | Totient | `theorem` | low |
| `chinese_remainder` | ChineseRemainder | `theorem` | high |
| `fermat_little_theorem` | Fermat | `theorem` | high |
| `wilson` | Wilson | `theorem` | high |
