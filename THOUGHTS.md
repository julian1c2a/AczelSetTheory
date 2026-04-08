# Thoughts — AczelSetTheory

**Last updated:** 2026-04-10 00:00
**Author**: Julián Calderón Almendros

> This is an informal design journal. Record ideas, alternatives considered,
> open questions, and future directions here. Not normative — purely exploratory.
> Useful for AI context on "why" decisions were made.

---

## Nuevos pensamientos

- **Powerset resuelto — filter como testigo de sublistas**: La clave para probar `powersetCList_extEq` fue demostrar primero `mem_powersetCList` (y ∈ powerset(A) ↔ y ⊆ A) como lema intermedio. La dirección difícil (←) se resolvió usando `xs.filter (fun z => mem z y)` como testigo sublista. Esta técnica reutiliza toda la infraestructura de `CList/Filter.lean` (`P_respects`, `extEq_filter`, `filter_in_sublists`) en lugar de intentar construir una correspondencia directa entre sublistas de A₁ y A₂. Lección: cuando la correspondencia directa es combinatoriamente compleja, buscar una **caracterización semántica** (aquí: subset) que simplifique la prueba de extEq a transitividad.
- **Separación Arquitectónica (Operations vs Axioms)**: Con la formalización de Union, Intersection, y Setminus, quedó claro que era beneficioso separar la definición de la operación computacional (Operations/) de los axiomas conceptuales tipo Zermelo (Axioms/). Esta estructura facilita la localización de fallos en Lean 4.
- **Setminus como herramienta para el Axioma de Regularidad / Buena Fundación**: Implementar la diferencia simétrica (Setminus) va a resultar esencial para enunciar la Regularidad, ya que este requiere quitar elementos (o calcular intersecciones vacías).
- **El reto de Powerset**: Al contrario que con Union que requiere "aplanar" listas, o Intersection que descarta elementos, el Conjunto Potencia (powersetCList) es constructivamente intensivo porque requiere construir explícitamente $2^N$ sublistas y probar que extensionalmente se corresponden. Requerirá su propio módulo auxiliar.
- **Axioma de Elección**: Sigue estando la duda si el Axioma de Elección es derivable en sets hereditariamente finitos, tal cual pasa en ZF con modelos restringidos. Veremos.

- **[1.] Posible ampliación del esquema de conjuntos** Supongamos que definimos de forma inductiva un tipo de conjuntos que son o bien un HFSet
o bien un conjunto extensional de HFSets más una predicado de pertenencia de HFSets o los nuevos Sets construidos que cumplan con ese predicado de pertenencia. ¿Esto daría lugar a conjuntos computables, aunque posiblemente infinitos? Por ejemplo, podemos definir $V_ω := \{[ x | x \text{ es un } HFSet ]\}$ y luego $V_{Succ(ω)} := \{[ x | x ∈ V_ω ∨ x = V_ω ]\}$

---

## [1.] Análisis profundo: extensión del universo HFSet

### 1.1. Contexto matemático

Lo que actualmente tenemos formalizado es $V_\omega$ — la colección de todos los conjuntos
hereditariamente finitos (HFSet). Es un hecho bien conocido que $V_\omega$ es:

- Un **conjunto admisible** (modelo de Kripke-Platek, KP).
- Equivalente a $L_\omega$ (la jerarquía constructible de Gödel truncada en $\omega$).
- Un modelo de ZF menos el axioma de infinitud (ZF$^{-\infty}$).
- Contable ($|V_\omega| = \aleph_0$), aunque es un conjunto infinito.

La pregunta de [1.] es: **¿cómo extender este universo más allá de $V_\omega$ manteniendo
computabilidad?**

### 1.2. Lo que dice la teoría de conjuntos

La jerarquía de Von Neumann extiende $V_\omega$ así:
$$V_{\omega+1} = \mathcal{P}(V_\omega)$$
Pero $|V_{\omega+1}| = 2^{\aleph_0}$ — incontable. **No se pueden enumerar todos los subconjuntos
de $V_\omega$.** Esto hace que $V_{\omega+1}$ sea computacionalmente intratable como un todo.

La alternativa es la **jerarquía constructible** de Gödel:
$$L_{\omega+1} = \text{Def}(L_\omega)$$
donde $\text{Def}(X)$ son los subconjuntos de $X$ **definibles por fórmulas de primer orden**
con parámetros de $X$ y cuantificadores acotados a $X$. Crucialmente:

- $L_{\omega+1}$ es contable (solo hay contablemente muchas fórmulas).
- $L_{\omega+1} \subsetneq V_{\omega+1}$ (faltan los subconjuntos no-definibles).
- Los subconjuntos de $\omega$ en $L_{\omega+1}$ son **exactamente los subconjuntos aritméticos**
  (jerarquía aritmética: $\Sigma^0_n$, $\Pi^0_n$ para todo $n$).
- Si se sube a $L_{\omega_1^{CK}}$ (ordinal de Church-Kleene), se obtienen los conjuntos
  **hiperaritméticos** ($\Delta^1_1$), que son "el límite natural de lo computable iterado".

### 1.3. La propuesta original: HFSet + predicados

La idea era:

```
inductive ASet where
  | fin : HFSet → ASet
  | ext : (ASet → Prop) → ASet
```

con membresía: `x ∈ ext P ↔ P x`.

Esto es esencialmente construir $L_{\omega+1}$ si restringimos `P` a predicados definibles.
Pero tiene problemas fundamentales en Lean 4:

1. **Universo**: `ASet → Prop` vive en el mismo nivel de tipo que `ASet`, lo que crea
   circularidad — Lean rechazaría el `inductive` por estricta positividad.
2. **Extensionalidad**: Dos `ext P₁` y `ext P₂` deben ser iguales iff
   `∀ x, P₁ x ↔ P₂ x`. Requiere cociente, pero cocientar un tipo con funciones
   en el argumento negativo es delicado (similar a los problemas de setoides).
3. **Decidibilidad**: No hay garantía de que `P : ASet → Prop` sea decidible.

### 1.4. La propuesta nueva: CList ampliada con ω como símbolo primitivo

La idea refinada es añadir ω como un átomo:

```lean
inductive CList₁ where
  | mk : List CList₁ → CList₁
  | omega : CList₁
```

donde `omega` representa al conjunto $\omega = V_\omega$ (la colección de todos los HFSets).
La membresía sería:

- `x ∈ mk xs` := existe `y ∈ xs` con `extEq₁ x y = true` (como ahora).
- `x ∈ omega` := `x` es (la imagen de) algún `HFSet`.

#### ¿Qué se obtiene?

Se obtiene **HF({ω})** — los conjuntos hereditariamente finitos con un urelemento ω.
Es decir: **conjuntos finitos cuyos elementos pueden ser HFSets clásicos o el propio
símbolo ω, o cualquier combinación finita de estos.** Ejemplos:

- `{ω}` — el singleton que contiene a ω
- `{∅, ω}` — un par
- `{{ω}, ∅}` — ω solo aparece dentro de un subconjunto
- `{ω, {ω}}` — ω y su singleton (= succ(ω) en estilo Von Neumann)

#### ¿Qué NO se obtiene?

**No se obtiene $V_{\omega+1}$**. Para eso se necesitarían subconjuntos **infinitos** de
$V_\omega$ (como "el conjunto de todos los ordinales pares"), y con listas finitas
no se pueden representar. Lo que se obtiene está más cerca de
$\text{HF} \cup \{\omega\} \cup \text{HF}(\{\omega\})$ — finito en estructura,
solo que ω es un "punto gordo" que contiene infinidad interna.

#### El problema de la membresía en ω

Para que `x ∈ omega` sea decidible, se necesita un mapeo computable:

- Una función `embed : CList → CList₁` que inyecte los HFSets originales.
- Un predicado decidible `isHFSet : CList₁ → Bool` que distinga CList₁-términos
  que son imagen de HFSets puros (no contienen `omega` en su árbol).

Esto ES factible: `isHFSet (mk xs) = xs.all isHFSet` y `isHFSet omega = false`.
Luego `x ∈ omega ↔ isHFSet x = true`.

**Pero esto tiene una consecuencia curiosa**: la membresía en `omega` es decidible
por inspección sintáctica, no por enumeración de todos los HFSets. Funciona
porque la información de "qué es un HFSet" está codificada en la estructura
del término CList₁.

### 1.5. Iteración: CList₂, CList₃

Se puede iterar:

```lean
inductive CList₂ where
  | mk : List CList₂ → CList₂
  | omega : CList₂      -- = V_ω
  | omega₁ : CList₂     -- = V_{ω+1}^{fin} = HFSet₁ (conjunto de todos los CList₁-sets)
```

Cada nivel añade un "átomo grande" que representa la colección del nivel anterior.
Pero cada nivel solo captura los **subconjuntos finitos** del universo previo,
no el powerset completo. Así:

| Nivel | Tipo | Universo capturado |
|-------|------|-------------------|
| CList | `HFSet` | $V_\omega$ |
| CList₁ | `HFSet₁` | $\text{HF}(\{V_\omega\})$ — finito sobre $V_\omega$ |
| CList₂ | `HFSet₂` | $\text{HF}(\{V_\omega, \text{HF}_1\})$ |
| ... | ... | ... |

Esto NO escala hasta $V_{\omega+\omega}$ porque cada paso solo añade un átomo,
no todos los subconjuntos.

### 1.6. La alternativa real: CList indexada por ordinales + streams

Para capturar subconjuntos infinitos (y así realmente construir $V_{\omega+1}$),
se necesitaría reemplazar `List` por algo que admita infinitud:

```lean
-- Boceto conceptual (NO implementable directamente como inductive)
inductive ASet where
  | fin : List ASet → ASet        -- conjuntos finitos (como ahora)
  | inf : (HFSet → Bool) → ASet   -- subconjuntos decidibles de V_ω
```

Aquí `inf P` representaría `{x ∈ V_ω | P x = true}`, un subconjunto decidible
de los HFSets. Esto captura exactamente los **subconjuntos computables** de $V_\omega$,
que forma una clase estrictamente más pequeña que $L_{\omega+1}$:

$$\text{Comp}(V_\omega) \subsetneq L_{\omega+1} \subsetneq V_{\omega+1}$$

Los elementos de $\text{Comp}(V_\omega)$ son los conjuntos decidibles de HFSets — aquellos
cuya función característica es computable (recursiva total).

**Ventajas:**

- `HFSet → Bool` es un tipo válido en Lean 4 (no hay violación de positividad).
- La membresía es decidible por definición (`x ∈ inf P ↔ P x = true`).
- La extensionalidad se puede obtener via `Quotient` con `R P Q := ∀ x, P x = Q x`.
- Se pueden mezclar conjuntos finitos (`fin`) e infinitos decidibles (`inf`).

**Desafíos:**

- La extensionalidad entre `fin xs` e `inf P` requiere comprobar que tienen los
  mismos elementos, lo cual involucra cuantificación sobre todos los HFSets.
- La igualdad no es decidible en general (comparar dos `inf P Q` requiere
  `∀ x : HFSet, P x = Q x` — cuantificación sobre un dominio infinito).
- El powerset de un `inf` ya no es representable en este esquema
  (necesitaría `(HFSet → Bool) → Bool`, que es de un tipo superior).

### 1.7. Conexión con marcos teóricos establecidos

| Marco teórico | Relación con la propuesta |
|---------------|--------------------------|
| **KP (Kripke-Platek)** | $V_\omega$ (nuestro HFSet) es el admisible mínimo. KP$\omega$ (con axioma de infinito) da $L_{\omega_1^{CK}}$, que contiene todos los conjuntos hiperaritméticos. |
| **Jerarquía constructible $L_\alpha$** | $L_\omega = V_\omega = HFSet$. $L_{\omega+1}$ = subconjuntos aritméticos de $\omega$. Para todo $n$ finito, $L_n = V_n$. |
| **Conjuntos admisibles (Barwise 1975)** | Un conjunto admisible es un conjunto transitivo que modela KP. La propuesta de CList₁ produce un conjunto transitivo que contiene a $V_\omega$ como elemento, pero NO es admisible (faltaría $\Delta_0$-Collection). |
| **HF(A) — HF con urelementos** | CList₁ con $\omega$ es exactamente $\text{HF}(\{V_\omega\})$. Bien estudiado en la literatura (Barwise & Moss, "Vicious Circles"). |
| **Teoría constructiva CZF (Aczel)** | En CZF, los conjuntos se construyen via reglas constructivas. La propuesta de `inf : (HFSet → Bool) → ASet` es compatible con CZF si se requiere decidibilidad. |

### 1.8. Recomendación para el proyecto

**Paso conservador (recomendado primero):** Implementar CList₁ con `omega` como
urelemento. Esto es:

- Técnicamente factible en Lean 4 (inductive limpio, sin violaciones de positividad).
- Permite formalizar el axioma de infinitud: $\omega \in V$.
- Da práctica con la maquinaria extensional antes de abordar subconjuntos infinitos.

**Paso ambicioso (futuro):** Implementar el esquema `fin + inf` con predicados
`HFSet → Bool`. Esto requiere resolver:

- Extensionalidad mixta (fin vs inf).
- Decidir si la igualdad será proposicional (via cociente) o computacional.
- Posiblemente indexar por niveles ordinales para subir más allá de $V_{\omega+1}$.

### 1.9. Referencias clave

- **Barwise, J. (1975)**. *Admissible Sets and Structures*. Springer. — Referencia
  canónica para conjuntos admisibles y KP.
- **Devlin, K. (1984)**. *Constructibility*. Springer. — Jerarquía constructible
  $L_\alpha$, fine structure.
- **Barwise, J. & Moss, L. (1996)**. *Vicious Circles*. CSLI. — HF con urelementos,
  conjuntos no bien fundados.
- **Kirby, L. (2009)**. "Finitary Set Theory". *Notre Dame J. Formal Logic* 50(3). —
  Axiomatización constructiva de HF.
- **Ackermann, W. (1937)**. "Die Widerspruchsfreiheit der allgemeinen Mengenlehre". —
  Codificación de HF en naturales (codificación de Ackermann).

---
