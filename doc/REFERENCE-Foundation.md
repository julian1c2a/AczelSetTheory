# REFERENCE — Foundation

> **Proyecto**: Peano
> **Rama**: `migracion_de_REFERENCE`
> **Fecha**: 2026-05-10
> **Nodo**: `doc/REFERENCE-Foundation.md`
> **Volver al índice**: [REFERENCE.md](../REFERENCE.md)

---

## Módulos cubiertos

| Archivo | Namespace | Descripción |
| --- | --- | --- |
| `Peano/PeanoNat/Foundation/PeanoSystem.lean` | `Peano.Foundation` | Álgebras de Peano y morfismos |
| `Peano/PeanoNat/Foundation/Initiality.lean` | `Peano.Foundation` | ℕ₀ como objeto inicial |
| `Peano/PeanoNat/Foundation/CantorPairing.lean` | `Peano.Foundation` | Apareamiento de Cantor ℕ₀ × ℕ₀ ≅ ℕ₀ |
| `Peano/PeanoNat/Foundation/GodelBeta.lean` | `Peano.Foundation` | Función β de Gödel; codificación de listas |
| `Peano/PeanoNat/Foundation/PureAxioms.lean` | `Peano.Foundation` | Sistema axiomático puro ℕ₀_pa |
| `Peano/PeanoNat/Foundation/Foundation.lean` | — | Fachada (re-importa los anteriores) |

**Axioma**: `@axiom_system: Peano`
**Bloque `export` explícito**: `GodelBeta.lean` línea 666 — exporta 8 símbolos de `Peano.Foundation`.
El resto de símbolos son públicos en `Peano.Foundation.*` pero requieren calificación completa.

---

## Módulo: PeanoSystem

### §1. `PeanoSystem`

- **Tipo**: `structure`
- **Módulo**: `Peano/PeanoNat/Foundation/PeanoSystem.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: high`
- **Computable**: ✅ (definición computable; algunos campos pueden ser noncomputable en instancias)
- **Firma Lean 4**:

  ```lean
  structure PeanoSystem where
    N        : Type 0
    zero     : N
    succ     : N → N
    inj      : ∀ m n : N, succ m = succ n → m = n
    discr    : ∀ n : N, zero ≠ succ n
    ind      : ∀ P : N → Prop, P zero → (∀ n, P n → P (succ n)) → ∀ n, P n
    prim_rec : ∀ {A : Type 0} (a : A) (f : A → A),
                 ExistsUnique (fun h : N → A => h zero = a ∧ ∀ n, h (succ n) = f (h n))
  ```

- **Notación matemática**: Una *álgebra de Peano* o *NNO* (Natural Numbers Object): un tipo $N$ con constante $0_N$, función $s_N : N \to N$, inyectividad, discriminación, inducción y recursión primitiva.
- **Descripción**: El campo `prim_rec` es la propiedad universal del NNO. Permite construir morfismos hacia cualquier otro sistema de Peano y probar la unicidad del isomorfismo.

---

### §2. `PeanoMorphism`

- **Tipo**: `structure`
- **Módulo**: `Peano/PeanoNat/Foundation/PeanoSystem.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: high`
- **Computable**: ✅
- **Firma Lean 4**:

  ```lean
  @[ext]
  structure PeanoMorphism (A B : PeanoSystem) where
    map       : A.N → B.N
    pres_zero : map A.zero = B.zero
    pres_succ : ∀ n : A.N, map (A.succ n) = B.succ (map n)
  ```

- **Notación matemática**: Un morfismo de álgebras de Peano: una función $f : A.N \to B.N$ que preserva el cero y el sucesor.
- **Nota**: Tiene `@[ext]` — dos morfismos son iguales si coinciden en `map`.

---

### §3. `isPeanoIso`

- **Tipo**: `def`
- **Módulo**: `Peano/PeanoNat/Foundation/PeanoSystem.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: high`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  def isPeanoIso (A B : PeanoSystem) (f : PeanoMorphism A B) : Prop :=
    ∃ g : PeanoMorphism B A,
      (∀ x : A.N, g.map (f.map x) = x) ∧
      (∀ y : B.N, f.map (g.map y) = y)
  ```

- **Notación matemática**: $f$ es un isomorfismo de álgebras de Peano si tiene inverso bilateral $g$.

---

### §4. `compMorph`

- **Tipo**: `def`
- **Módulo**: `Peano/PeanoNat/Foundation/PeanoSystem.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: medium`
- **Computable**: ✅
- **Firma Lean 4**:

  ```lean
  def compMorph {A B C : PeanoSystem}
      (g : PeanoMorphism B C) (f : PeanoMorphism A B) : PeanoMorphism A C
  ```

- **Notación matemática**: Composición $g \circ f$ de morfismos de Peano.

---

### §5. `idMorph`

- **Tipo**: `def`
- **Módulo**: `Peano/PeanoNat/Foundation/PeanoSystem.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: medium`
- **Computable**: ✅
- **Firma Lean 4**:

  ```lean
  def idMorph (A : PeanoSystem) : PeanoMorphism A A
  ```

- **Notación matemática**: El morfismo identidad $\mathrm{id}_A$ en un álgebra de Peano.

---

## Módulo: Initiality

### §6. `ℕ₀_prim_rec`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/Foundation/Initiality.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: high`
- **Firma Lean 4**:

  ```lean
  theorem ℕ₀_prim_rec {A : Type 0} (a : A) (f : A → A) :
      ExistsUnique (fun h : ℕ₀ → A => h 𝟘 = a ∧ ∀ n, h (σ n) = f (h n))
  ```

- **Notación matemática**: El principio de recursión primitiva: dados $a \in A$ y $f : A \to A$, existe una única función $h : \mathbb{N}_0 \to A$ con $h(0) = a$ y $h(n+1) = f(h(n))$.
- **Dependencias directas**: `Peano.Prelim.ExistsUnique`

---

### §7. `ℕ₀_PeanoSystem`

- **Tipo**: `def`
- **Módulo**: `Peano/PeanoNat/Foundation/Initiality.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: high`
- **Computable**: ✅
- **Firma Lean 4**:

  ```lean
  def ℕ₀_PeanoSystem : PeanoSystem
  ```

- **Descripción**: La instancia de `PeanoSystem` cuyo tipo subyacente es `ℕ₀`, con `zero = 𝟘`, `succ = ℕ₀.succ`, y todos los axiomas verificados.

---

### §8. `ℕ₀_to`

- **Tipo**: `def`
- **Módulo**: `Peano/PeanoNat/Foundation/Initiality.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: high`
- **Computable**: ✅
- **Firma Lean 4**:

  ```lean
  def ℕ₀_to (A : PeanoSystem) : ℕ₀ → A.N
    | .zero   => A.zero
    | .succ n => A.succ (ℕ₀_to A n)
  ```

- **Notación matemática**: El único morfismo de funciones $\mathbb{N}_0 \to A.N$ que preserva la estructura de Peano.

---

### §9. `ℕ₀_to_morph`

- **Tipo**: `def`
- **Módulo**: `Peano/PeanoNat/Foundation/Initiality.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: medium`
- **Computable**: ✅
- **Firma Lean 4**:

  ```lean
  def ℕ₀_to_morph (A : PeanoSystem) : PeanoMorphism ℕ₀_PeanoSystem A
  ```

- **Descripción**: `ℕ₀_to A` empaquetado como `PeanoMorphism`.

---

### §10. `ℕ₀_initial`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/Foundation/Initiality.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: high`
- **Firma Lean 4**:

  ```lean
  theorem ℕ₀_initial (A : PeanoSystem) :
      ExistsUnique (fun h : ℕ₀ → A.N => h 𝟘 = A.zero ∧ ∀ n, h (σ n) = A.succ (h n))
  ```

- **Notación matemática**: **Inicialidad de ℕ₀**: existe un único morfismo de funciones de $\mathbb{N}_0$ hacia cualquier sistema de Peano $A$.

---

### §11. `morph_fn`

- **Tipo**: `noncomputable def`
- **Módulo**: `Peano/PeanoNat/Foundation/Initiality.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: high`
- **Computable**: ❌ (noncomputable — usa `choose_unique`)
- **Firma Lean 4**:

  ```lean
  noncomputable def morph_fn (A B : PeanoSystem) : A.N → B.N :=
    choose_unique (A.prim_rec B.zero B.succ)
  ```

- **Notación matemática**: El único morfismo canónico de funciones entre dos sistemas de Peano arbitrarios $A \to B$.
- **Dependencias directas**: `Peano.Prelim.Classical.choose_unique`

---

### §12. `morph_as_morph`

- **Tipo**: `noncomputable def`
- **Módulo**: `Peano/PeanoNat/Foundation/Initiality.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: medium`
- **Computable**: ❌
- **Firma Lean 4**:

  ```lean
  noncomputable def morph_as_morph (A B : PeanoSystem) : PeanoMorphism A B
  ```

- **Descripción**: `morph_fn A B` empaquetado como `PeanoMorphism A B`.

---

### §13. `peano_unique`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/Foundation/Initiality.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: high`
- **Firma Lean 4**:

  ```lean
  theorem peano_unique (A B : PeanoSystem) :
      ExistsUnique (fun f : PeanoMorphism A B => isPeanoIso A B f)
  ```

- **Notación matemática**: **Unicidad de la estructura de Peano**: cualesquiera dos sistemas de Peano son únicamente isomorfos. El isomorfismo canónico es `morph_as_morph A B`.

---

## Módulo: CantorPairing

### §14. `triag`

- **Tipo**: `def`
- **Módulo**: `Peano/PeanoNat/Foundation/CantorPairing.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: medium`
- **Computable**: ✅
- **Firma Lean 4**:

  ```lean
  def triag (n : ℕ₀) : ℕ₀ := mul n (σ n) / 𝟚
  ```

- **Notación matemática**: El $n$-ésimo número triangular $T(n) = \dfrac{n(n+1)}{2}$.

---

### §15. `triag_zero` / `triag_succ`

- **Tipo**: `theorem` (x2)
- **Módulo**: `Peano/PeanoNat/Foundation/CantorPairing.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: low`
- **Firmas Lean 4**:

  ```lean
  theorem triag_zero : triag 𝟘 = 𝟘
  theorem triag_succ (n : ℕ₀) : triag (σ n) = add (triag n) (σ n)
  ```

- **Notación matemática**: $T(0) = 0$ y $T(n+1) = T(n) + (n+1)$.

---

### §16. `pair`

- **Tipo**: `def`
- **Módulo**: `Peano/PeanoNat/Foundation/CantorPairing.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: high`
- **Computable**: ✅
- **Firma Lean 4**:

  ```lean
  def pair (m n : ℕ₀) : ℕ₀ := add (triag (add m n)) m
  ```

- **Notación matemática**: La función de apareamiento de Cantor $\langle m, n \rangle = T(m+n) + m$.

---

### §17. `antidiag`

- **Tipo**: `def`
- **Módulo**: `Peano/PeanoNat/Foundation/CantorPairing.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: medium`
- **Computable**: ✅ (usa `choose` — noncomputable en el fondo si se extrae el testigo)
- **Firma Lean 4**:

  ```lean
  def antidiag (z : ℕ₀) : ℕ₀
  ```

- **Notación matemática**: La antidiagonal de $z$: el único $d$ tal que $T(d) \leq z < T(d+1)$. Satisface `antidiag (pair m n) = add m n`.

---

### §18. `fst` / `snd`

- **Tipo**: `def` (x2)
- **Módulo**: `Peano/PeanoNat/Foundation/CantorPairing.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: high`
- **Computable**: ✅
- **Firmas Lean 4**:

  ```lean
  def fst (z : ℕ₀) : ℕ₀ := sub z (triag (antidiag z))
  def snd (z : ℕ₀) : ℕ₀ := sub (antidiag z) (fst z)
  ```

- **Notación matemática**: Las proyecciones de la función de apareamiento de Cantor:
  $\pi_1(z) = z - T(\mathrm{antidiag}(z))$,
  $\pi_2(z) = \mathrm{antidiag}(z) - \pi_1(z)$.

---

### §19. `pair_fst` / `pair_snd` / `pair_surj`

- **Tipo**: `theorem` (x3)
- **Módulo**: `Peano/PeanoNat/Foundation/CantorPairing.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: high`
- **Firmas Lean 4**:

  ```lean
  theorem pair_fst (m n : ℕ₀) : fst (pair m n) = m
  theorem pair_snd (m n : ℕ₀) : snd (pair m n) = n
  theorem pair_surj (z : ℕ₀) : pair (fst z) (snd z) = z
  ```

- **Notación matemática**: La biyección $\langle\cdot,\cdot\rangle : \mathbb{N}_0 \times \mathbb{N}_0 \to \mathbb{N}_0$ con inversas $\pi_1, \pi_2$. Junto con `pair_fst` y `pair_snd` se obtiene el isomorfismo completo $\mathbb{N}_0 \times \mathbb{N}_0 \cong \mathbb{N}_0$.

---

### §20. Lemas auxiliares de CantorPairing (lista)

| Símbolo | Firma resumida | Importance |
| --- | --- | --- |
| `triag_strict_mono` | `lt₀ m n → lt₀ (triag m) (triag n)` | low |
| `triag_le_of_le` | `le₀ m n → le₀ (triag m) (triag n)` | low |
| `triag_le_pair` | `le₀ (triag (add m n)) (pair m n)` | low |
| `pair_lt_triag_succ` | `lt₀ (pair m n) (triag (σ (add m n)))` | low |
| `antidiag_spec` | `le₀ (triag (antidiag z)) z ∧ lt₀ z (triag (σ (antidiag z)))` | low |
| `antidiag_pair` | `antidiag (pair m n) = add m n` | medium |

---

## Módulo: GodelBeta

### §21. `beta`

- **Tipo**: `def`
- **Módulo**: `Peano/PeanoNat/Foundation/GodelBeta.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: high`
- **Computable**: ✅
- **Firma Lean 4**:

  ```lean
  def beta (c b i : ℕ₀) : ℕ₀ := mod c (add 𝟙 (mul (σ i) b))
  ```

- **Notación matemática**: La función $\beta$ de Gödel: $\beta(c, b, i) = c \bmod (1 + (i+1) \cdot b)$.
- **Descripción**: Mecanismo de codificación de secuencias finitas. Gödel usó esta función para codificar listas de enteros como pares de enteros en la prueba del Teorema de Incompletitud.
- **Notas**: `beta` está en el bloque `export Peano.Foundation (...)` — accesible sin calificación.

---

### §22. `beta_lt`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/Foundation/GodelBeta.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: medium`
- **Firma Lean 4**:

  ```lean
  theorem beta_lt (c b i : ℕ₀) : lt₀ (beta c b i) (add 𝟙 (mul (σ i) b))
  ```

- **Notación matemática**: $\beta(c, b, i) < 1 + (i+1) \cdot b$ (el resto es estrictamente menor que el divisor).

---

### §23. `beta_of_lt`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/Foundation/GodelBeta.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: medium`
- **Firma Lean 4**:

  ```lean
  theorem beta_of_lt (a b i : ℕ₀) (h : lt₀ a (add 𝟙 (mul (σ i) b))) :
      beta a b i = a
  ```

- **Notación matemática**: Si $a < 1 + (i+1) \cdot b$, entonces $\beta(a, b, i) = a$.

---

### §24. `godel_beta_seq`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/Foundation/GodelBeta.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: high`
- **Firma Lean 4**:

  ```lean
  theorem godel_beta_seq (n : ℕ₀) (a : ℕ₀ → ℕ₀) :
      ∃ c b : ℕ₀, ∀ i, le₀ i n → beta c b i = a i
  ```

- **Notación matemática**: **Teorema de Representación de Gödel**: para cualquier secuencia finita $a_0, \ldots, a_n$ existen $c, b \in \mathbb{N}_0$ tales que $\beta(c, b, i) = a_i$ para todo $i \leq n$.
- **Estrategia de prueba**: Se usa el Teorema Chino del Residuo para encontrar $c$ que satisface simultáneamente $n+1$ congruencias. La coprimidad de los módulos $1+(i+1)b$ se garantiza eligiendo $b = (n+1)!$.
- **Dependencias directas**: `Peano.CRT.chinese_remainder`, `Peano.Factorial.factorial`, `Peano.Foundation.CantorPairing`

---

### §25. `encodeList`

- **Tipo**: `noncomputable def`
- **Módulo**: `Peano/PeanoNat/Foundation/GodelBeta.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: high`
- **Computable**: ❌ (noncomputable — usa `Classical.choose`)
- **Firma Lean 4**:

  ```lean
  noncomputable def encodeList (l : List ℕ₀) : ℕ₀
  ```

- **Notación matemática**: Codifica una lista $[a_0, \ldots, a_{n-1}]$ como un único $z \in \mathbb{N}_0$ usando `pair (c, b)` tal que $\beta(c, b, i) = a_i$.

---

### §26. `decodeList`

- **Tipo**: `def`
- **Módulo**: `Peano/PeanoNat/Foundation/GodelBeta.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: high`
- **Computable**: ✅
- **Firma Lean 4**:

  ```lean
  def decodeList (z : ℕ₀) : ℕ₀ → List ℕ₀
    | .zero   => []
    | .succ k => decodeList z k ++ [beta (fst z) (snd z) k]
  ```

- **Notación matemática**: Dado el código $z$ y la longitud $n$, reconstruye la lista $[\beta(\pi_1(z), \pi_2(z), 0), \ldots, \beta(\pi_1(z), \pi_2(z), n-1)]$.

---

### §27. `list_decode_length`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/Foundation/GodelBeta.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: low`
- **Firma Lean 4**:

  ```lean
  theorem list_decode_length (z n : ℕ₀) :
      (decodeList z n).length = Ψ n
  ```

- **Descripción**: La lista decodificada tiene exactamente $\Psi(n)$ elementos (donde $\Psi$ es el isomorfismo $\mathbb{N}_0 \to \mathbb{N}$ de `Isomorph.lean`).

---

### §28. `encode_decode`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/Foundation/GodelBeta.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: high`
- **Firma Lean 4**:

  ```lean
  theorem encode_decode (l : List ℕ₀) :
      decodeList (encodeList l) (Λ l.length) = l
  ```

- **Notación matemática**: **Teorema de fidelidad**: `decodeList ∘ encodeList = id` — decodificar lo que se codificó devuelve la lista original.
- **Dependencias directas**: `godel_beta_seq`, `pair_fst`, `pair_snd`, `Peano.Isomorph.Λ`, `Peano.Isomorph.Ψ`

---

## Módulo: PureAxioms

### §29. `PurePA`

- **Tipo**: `noncomputable def`
- **Módulo**: `Peano/PeanoNat/Foundation/PureAxioms.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: medium`
- **Computable**: ❌ (noncomputable — construido sobre axiomas opacos)
- **Firma Lean 4**:

  ```lean
  noncomputable def PurePA : PeanoSystem
  ```

- **Descripción**: El sistema de Peano puramente axiomático: tipo `ℕ₀_pa` con `zero_pa`, `succ_pa` declarados como `axiom`. Permite demostrar la compatibilidad entre el tipo inductivo `ℕ₀` y la presentación axiomática de los números naturales.

---

### §30. `pa_parity`

- **Tipo**: `theorem`
- **Módulo**: `Peano/PeanoNat/Foundation/PureAxioms.lean`
- **Namespace**: `Peano.Foundation`
- **Importancia**: `@importance: high`
- **Firma Lean 4**:

  ```lean
  theorem pa_parity :
      ExistsUnique (fun f : PeanoMorphism ℕ₀_PeanoSystem PurePA =>
        isPeanoIso ℕ₀_PeanoSystem PurePA f)
  ```

- **Notación matemática**: **Teorema de Paridad Formal**: existe un único isomorfismo entre el tipo inductivo $\mathbb{N}_0$ y el sistema axiomático puro $\mathbb{N}_{0,\mathrm{pa}}$.
- **Estrategia de prueba**: Instancia directa de `peano_unique ℕ₀_PeanoSystem PurePA`.
- **Interpretación**: Los axiomas declarados con `axiom` de Lean 4 y el tipo inductivo `ℕ₀` son el mismo objeto matemático. Corolario: $\omega$ (los naturales de von Neumann en ZFC) es isomorfo a `ℕ₀` via la cadena $\omega \cong \mathrm{PurePA} \cong \mathbb{N}_0$.

---

## Resumen de exports explícitos

El bloque `export Peano.Foundation (...)` en `GodelBeta.lean` exporta los siguientes 8 símbolos directamente al scope raíz:

| Símbolo | Tipo | Importance |
| --- | --- | --- |
| `beta` | `def` | high |
| `beta_lt` | `theorem` | medium |
| `beta_of_lt` | `theorem` | medium |
| `godel_beta_seq` | `theorem` | high |
| `encodeList` | `noncomputable def` | high |
| `decodeList` | `def` | high |
| `list_decode_length` | `theorem` | low |
| `encode_decode` | `theorem` | high |

## Resumen de símbolos públicos (todos los módulos)

| Símbolo | Módulo | Tipo | Importance |
| --- | --- | --- | --- |
| `PeanoSystem` | PeanoSystem | `structure` | high |
| `PeanoMorphism` | PeanoSystem | `structure` | high |
| `isPeanoIso` | PeanoSystem | `def` | high |
| `compMorph` | PeanoSystem | `def` | medium |
| `idMorph` | PeanoSystem | `def` | medium |
| `ℕ₀_prim_rec` | Initiality | `theorem` | high |
| `ℕ₀_PeanoSystem` | Initiality | `def` | high |
| `ℕ₀_to` | Initiality | `def` | high |
| `ℕ₀_to_morph` | Initiality | `def` | medium |
| `ℕ₀_initial` | Initiality | `theorem` | high |
| `morph_fn` | Initiality | `noncomputable def` | high |
| `morph_as_morph` | Initiality | `noncomputable def` | medium |
| `peano_unique` | Initiality | `theorem` | high |
| `triag` | CantorPairing | `def` | medium |
| `pair` | CantorPairing | `def` | high |
| `antidiag` | CantorPairing | `def` | medium |
| `fst` | CantorPairing | `def` | high |
| `snd` | CantorPairing | `def` | high |
| `pair_fst` | CantorPairing | `theorem` | high |
| `pair_snd` | CantorPairing | `theorem` | high |
| `pair_surj` | CantorPairing | `theorem` | high |
| `beta` | GodelBeta | `def` | high |
| `beta_lt` | GodelBeta | `theorem` | medium |
| `beta_of_lt` | GodelBeta | `theorem` | medium |
| `godel_beta_seq` | GodelBeta | `theorem` | high |
| `encodeList` | GodelBeta | `noncomputable def` | high |
| `decodeList` | GodelBeta | `def` | high |
| `list_decode_length` | GodelBeta | `theorem` | low |
| `encode_decode` | GodelBeta | `theorem` | high |
| `PurePA` | PureAxioms | `noncomputable def` | medium |
| `pa_parity` | PureAxioms | `theorem` | high |
