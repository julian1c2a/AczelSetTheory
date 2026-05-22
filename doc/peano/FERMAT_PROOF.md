> **ARCHIVADO — 2026-04-27**
> Implementado en `Peano/PeanoNat/NumberTheory/Fermat.lean` (2026-04-15). Sin sorry.
> Este archivo se conserva como registro histórico de la estrategia de prueba.

---

# Demostración detallada del pequeño teorema de Fermat en Peano/Lean4

> **Estado (2026-04-15):** ✅ **Implementado** en `Peano/PeanoNat/NumberTheory/Fermat.lean`.
> La prueba sigue exactamente la estrategia descrita abajo: reducción a coprimalidad →
> teorema de Euler → totient de primo → sustitución. Completamente constructiva, sin sorry.

## 1. Enunciado formal

Sea $p$ un número primo ($p \in \mathbb{N}_0$, $p \geq 2$) y $a \in \mathbb{N}_0$ tal que $p$ no divide a $a$ ($\neg\, p \mid a$). Entonces:

$$
a^{p-1} \equiv 1 \pmod{p}
$$

En notación Lean/Peano:

```lean
Prime p → ¬Divides p a → ModEq p (pow a (sub p 𝟙)) 𝟙
```

## 2. Estrategia general

La demostración sigue el enfoque clásico usando el grupo multiplicativo de unidades módulo $p$ y el hecho de que el conjunto $S = \{1, 2, ..., p-1\}$ es permutado por la multiplicación por $a$ cuando $\gcd(a, p) = 1$.

En Lean/Peano, se evita el lenguaje de grupos y se trabaja con propiedades elementales de la función totiente, la función potencia y la aritmética modular.

### Pasos principales

1. **Reducción a coprimalidad**: Si $p$ es primo y $p \nmid a$, entonces $\gcd(a, p) = 1$.
2. **Aplicar el teorema de Euler**: Si $\gcd(a, n) = 1$, entonces $a^{\varphi(n)} \equiv 1 \pmod{n}$.
3. **Calcular $\varphi(p)$**: Si $p$ es primo, $\varphi(p) = p-1$.
4. **Concluir**: $a^{p-1} \equiv 1 \pmod{p}$.

## 3. Desglose detallado de la prueba

### 3.1. Lemas y dependencias necesarias

- **Definiciones**:
  - `Prime p` (primalidad)
  - `Divides p a` (divisibilidad)
  - `ModEq p x y` (congruencia)
  - `pow a k` (potencia)
  - `totient n` (función de Euler)
- **Lemas previos**:
  - `gcd_eq_one_of_prime_not_dvd` : Si $p$ primo y $p \nmid a$, entonces $\gcd(a, p) = 1$.
  - `euler_theorem` : Si $\gcd(a, n) = 1$, entonces $a^{\varphi(n)} \equiv 1 \pmod{n}$.
  - `totient_prime` : $\varphi(p) = p-1$ si $p$ es primo.

### 3.2. Paso a paso

#### Paso 1: Reducción a coprimalidad

- Hipótesis: $p$ primo, $p \nmid a$.
- Por la definición de primo, $\gcd(a, p) = 1$.
- En Lean: usar `gcd_eq_one_of_prime_not_dvd hp hnp`.

#### Paso 2: Aplicar el teorema de Euler

- Por el teorema de Euler: $a^{\varphi(p)} \equiv 1 \pmod{p}$ si $\gcd(a, p) = 1$.
- En Lean: usar `euler_theorem hgcd`.

#### Paso 3: Calcular $\varphi(p)$

- Por la propiedad de la función totiente: $\varphi(p) = p-1$ si $p$ es primo.
- En Lean: usar `totient_prime hp`.

#### Paso 4: Sustitución y conclusión

- Sustituir en la congruencia: $a^{p-1} \equiv 1 \pmod{p}$.
- En Lean: reescribir la potencia usando la igualdad de la función totiente.

## 4. Esquema de la prueba en Lean

```lean
theorem fermat_little (hp : Prime p) (hnp : ¬Divides p a) :
  ModEq p (pow a (sub p 𝟙)) 𝟙 :=
by
  have hgcd : Coprime a p := gcd_eq_one_of_prime_not_dvd hp hnp
  have heuler := euler_theorem hgcd
  rw [totient_prime hp] at heuler
  exact heuler
```

## 5. Comentarios sobre constructividad

- La prueba es completamente constructiva en Lean/Peano, ya que todas las funciones y propiedades (potencia, totiente, primalidad, coprimalidad, congruencia) están definidas de manera efectiva.
- No se usa teoría de grupos ni argumentos de cardinalidad abstractos.

## 6. Referencias Lean/Peano

- `Peano/PeanoNat/NumberTheory/Fermat.lean` ✅ implementado
- `Peano/PeanoNat/NumberTheory/Totient.lean` ✅ implementado
- `Peano/PeanoNat/NumberTheory/ModEq.lean` ✅ implementado
- `Peano/PeanoNat/Primes.lean` (primalidad, coprimalidad)
- `Peano/PeanoNat/Combinatorics/Pow.lean` (potencias)

## 7. Posibles extensiones

- Demostración de la unicidad del inverso multiplicativo módulo $p$.
- Generalización a números compuestos (teorema de Euler).
- Demostración alternativa usando el grupo de permutaciones de $\{1, ..., p-1\}$.

---

**Fin del plan detallado para la demostración del pequeño teorema de Fermat en Peano/Lean4.**

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

