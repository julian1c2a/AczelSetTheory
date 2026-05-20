# Thoughts — AczelSetTheory

**Last updated:** 2026-05-20 00:00
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

## [2.] Estudio profundo: Nivel 1 — el esquema `fin + inf`

### 2.1. Definición formal

El **Nivel 1** extiende `HFSet` (= $V_\omega$) añadiendo un constructor para
subconjuntos decidibles de $V_\omega$:

```lean
inductive CList₊ where
  | mk  : List CList₊ → CList₊          -- conjuntos finitos (como CList actual)
  | inf : (HFSet → Bool) → CList₊        -- subconjuntos decidibles de V_ω
```

y el tipo cociente correspondiente sería `ASet := Quotient CList₊.Setoid`.

#### ¿Es válido en Lean 4?

**Sí.** La comprobación de positividad estricta se supera:

- `mk : List CList₊ → CList₊` — `CList₊` aparece dentro de `List`, que es un
  contenedor estrictamente positivo. ✓
- `inf : (HFSet → Bool) → CList₊` — `HFSet → Bool` es un tipo completamente
  ajeno a `CList₊`. No hay ocurrencia de `CList₊` en posición negativa. ✓

Esto contrasta con la propuesta original (§1.3) donde `ASet → Prop` ponía al
tipo siendo definido en posición negativa.

### 2.2. Semántica de membresía

La membresía `x ∈ₛ t` se define por casos sobre `t`:

| Forma de `t` | `x ∈ₛ t` iff |
|---------------|---------------|
| `mk xs` | `∃ y ∈ xs, extEq₊ x y` (como ahora con CList) |
| `inf P` | `∃ h : HFSet, embed h ≡ x ∧ P h = true` |

donde `embed : HFSet → CList₊` inyecta los HFSets "puros" (via su representación
CList) al nuevo tipo, y `≡` denota igualdad extensional en `CList₊`.

#### El embedding

```lean
def embed : CList → CList₊
  | CList.mk xs => CList₊.mk (xs.map embed)
```

Cada HFSet se convierte en un `CList₊` puro (sin nodos `inf`). Un predicado
`isPure : CList₊ → Bool` detecta si un término carece de `inf`:

```lean
def isPure : CList₊ → Bool
  | mk xs => xs.all isPure
  | inf _ => false
```

#### Simplificación de membresía en `inf`

Como la membresía en `inf P` solo admite HFSets (no `inf`-términos), se simplifica:

```
x ∈ₛ inf P  ↔  isPure x ∧ P (project x) = true
```

donde `project : CList₊ → HFSet` es la inversa parcial de `embed` (definida
solo sobre términos puros). Alternativamente, se eleva `P` via composición:

```lean
def liftP (P : HFSet → Bool) : CList₊ → Bool
  | mk xs => P (⊧ mk xs ⊧)   -- solo si isPure
  | inf _ => false
```

**Consecuencia clave**: Los elementos de `inf P` son siempre HFSets. Un `inf Q`
**nunca es miembro** de otro `inf P`. Los `inf`-términos son "conjuntos de techo":
contienen HFSets pero no se contienen entre sí (salvo que estén dentro de un `mk`).

### 2.3. Extensionalidad

Dos `CList₊` son extensionalmente iguales iff tienen los mismos miembros:

$$t_1 \equiv t_2 \iff \forall x : \text{CList}_+, \; (x \in_s t_1 \leftrightarrow x \in_s t_2)$$

Casos relevantes:

| Comparación | Condición de igualdad |
|-------------|----------------------|
| `mk xs ≡ mk ys` | Como ahora: mismos miembros (recursivo sobre listas) |
| `inf P ≡ inf Q` | `∀ h : HFSet, P h = Q h` (igualdad funcional pointwise) |
| `mk xs ≡ inf P` | Cada `y ∈ xs` es un HFSet puro con `P (project y) = true`, **y** para todo `h` con `P h = true` existe `y ∈ xs` con `embed h ≡ y` |

#### El caso mixto `mk ≡ inf`

`mk xs ≡ inf P` exige que la lista finita `xs` enumere **exactamente** los
HFSets que satisfacen `P`. Esto solo es posible si `P` tiene un conjunto finito
de testigos, y `xs` los lista todos (módulo extEq). En la práctica esto significa:

- Si `P` es verdadero en infinitos HFSets, entonces **ningún** `mk xs` es
  extensionalmente igual a `inf P`.
- Si `P` es verdadero en exactamente $\{h_1, \ldots, h_k\}$, entonces
  `mk [embed h₁, ..., embed hₖ]` es la única clase extensional equivalente.

#### ¿Es decidible la igualdad extensional?

- **`mk` vs `mk`**: Sí, decidible (como ahora — recursión sobre listas finitas).
- **`inf` vs `inf`**: **NO en general.** `∀ h : HFSet, P h = Q h` requiere
  cuantificación sobre un dominio infinito (todos los HFSets). Es co-r.e. pero
  no decidible en general. Sin embargo, en Lean 4 se trabaja con igualdad
  proposicional via `Quotient`, así que no se necesita decidibilidad — solo
  la existencia de la relación.
- **`mk` vs `inf`**: **NO decidible.** Requiere verificar si `P` tiene exactamente
  los testigos de `xs`, lo cual involucra cuantificación universal sobre HFSets.

**Conclusión**: La igualdad extensional en Nivel 1 **no es decidible**. El tipo
cociente `ASet` existe proposicionalmente, pero `DecidableEq ASet` no se puede
derivar. Esto es un cambio fundamental respecto a `HFSet` donde `DecidableEq`
es total.

### 2.4. Operaciones sobre conjuntos

#### 2.4.1. Operaciones entre `inf`-conjuntos

Estas son las operaciones limpias, donde el esquema `fin + inf` brilla:

| Operación | Definición | Tipo |
|-----------|-----------|------|
| $A \cup B$ | `inf (fun h => P h \|\| Q h)` | $\text{Comp}(V_\omega)$ |
| $A \cap B$ | `inf (fun h => P h && Q h)` | $\text{Comp}(V_\omega)$ |
| $A \setminus B$ | `inf (fun h => P h && !Q h)` | $\text{Comp}(V_\omega)$ |
| $\omega \setminus A$ | `inf (fun h => !P h)` | $\text{Comp}(V_\omega)$ |

La clausura booleana es perfecta: **los subconjuntos decidibles de $V_\omega$ forman
un álgebra de Boole**, cerrada bajo complemento (relativo a $\omega$), unión e
intersección. Esto corresponde a la clase $\Delta^0_1$ en la jerarquía aritmética.

#### 2.4.2. Operaciones mixtas (fin + inf)

| Operación | Definición | Complejidad |
|-----------|-----------|-------------|
| `mk xs ∪ inf P` | Requiere combinar una lista finita con un predicado | Ver abajo |
| `mk xs ∩ inf P` | `mk (xs.filter (fun y => isPure y && P (project y)))` | OK si xs finita |
| `∅ ∪ inf P` | `inf P` | Trivial |
| `{a} ∪ inf P` | Si `a` es HFSet: `inf (fun h => P h \|\| h == project a)` | OK |
| `{a} ∪ inf P` | Si `a` es `inf Q`: `mk [inf Q, inf P]` — pero ¿qué es esto? | Problemático |

El caso `mk xs ∪ inf P` cuando `xs` contiene `inf`-conjuntos como elementos
no se puede reducir a un solo `inf` (porque los `inf`-conjuntos no son HFSets).
La unión debe permanecer como `mk (inf P :: xs)` — una lista que contiene un
`inf`-término como elemento. Esto es válido estructuralmente pero distinto de un
`inf`-conjunto.

#### 2.4.3. Separación (Comprehension)

Para `inf P` y un predicado decidible `Q : HFSet → Prop`:

$$\{x \in \text{inf } P \mid Q\, x\} = \text{inf } (\lambda h.\; P\, h\; \&\&\; Q\, h)$$

Funciona perfectamente siempre que `Q` sea decidible sobre HFSets.

Para `mk xs` y un predicado decidible `Q : CList₊ → Prop`:

$$\{x \in \text{mk } xs \mid Q\, x\} = \text{mk } (xs.\text{filter}\; Q)$$

Como ahora. La Separación se preserva íntegramente.

#### 2.4.4. Powerset

Aquí el esquema **falla** para conjuntos infinitos:

- $\mathcal{P}(\text{mk } xs)$: Como ahora — `mk (sublists xs)`. Funciona (finito). ✓
- $\mathcal{P}(\text{inf } P)$: Necesitaría representar **todos los subconjuntos
  decidibles** de `{h | P h}`. Esto requeriría un constructor
  `inf₂ : ((HFSet → Bool) → Bool) → CList₊`, es decir un predicado sobre
  predicados. **Esto no está en el tipo `CList₊`.** ✗

$\mathcal{P}(\omega)$ tiene cardinalidad $2^{\aleph_0}$ — incontable. Incluso
restringiéndonos a subconjuntos decidibles, $|\text{Comp}(V_\omega)| = \aleph_0$
(contablemente muchos programas), pero **la colección de subconjuntos decidibles
de $\text{Comp}(V_\omega)$ ya no es representable** en el esquema.

**Conclusión**: El axioma de Powerset falla en Nivel 1 para conjuntos infinitos.
Esto es consistente con KP (Kripke-Platek), que **no incluye Powerset**.

#### 2.4.5. Unión generalizada (⋃)

- $\bigcup (\text{mk } xs)$: Se aplana la lista y se unen los miembros. Si algún
  `xᵢ = inf P`, entonces los miembros de `inf P` (HFSets con `P h = true`) se
  vierten en el resultado. Esto es computable.
- $\bigcup (\text{inf } P)$: Cada miembro de `inf P` es un HFSet $h$. Los miembros
  de $h$ son también HFSets. Entonces:
  $$\bigcup (\text{inf } P) = \text{inf } (\lambda h.\; \exists h' : \text{HFSet},\; P\, h' \;\wedge\; h \in h')$$
  Este predicado es decidible porque `h ∈ h'` es decidible (ambos son HFSets)
  y la cuantificación `∃ h'` puede acotarse: solo necesitamos buscar entre los
  elementos de `h` como posibles contenedores. **Pero no**: necesitamos buscar entre **todos** los `h'` con `P h' = true`, que pueden ser infinitos.

  Sin embargo, `h ∈ h'` implica que cierto encoding de `h` es "menor" que el de `h'` en la codificación de Ackermann. Dado un `h` fijo, la pregunta "¿existe un `h'` con `P h'` tal que `h ∈ h'`?" requiere buscar entre infinitos candidatos `h'`. Esto es $\Sigma^0_1$ en general (r.e., no decidible).

  **Problema**: $\bigcup (\text{inf } P)$ podría no ser decidible, solo
  recursivamente enumerable. Si `P` es la función característica de un conjunto
  decidible, la unión generalizada puede salirse de la clase decidible.

  ¿Es esto salvable? Sí, con una restricción: si exigimos que `P` solo sea
  verdadero en HFSets de rango acotado, o si definimos $\bigcup$ solo para
  `mk`-conjuntos (dejando `⋃(inf P)` como operación parcial o no representable).

### 2.5. Axiomas de ZF: verificación para Nivel 1

| Axioma | ¿Se cumple? | Comentario |
|--------|-------------|------------|
| **Extensionalidad** | ✓ | Por definición del cociente |
| **Conjunto vacío** | ✓ | `mk []` o `inf (fun _ => false)` |
| **Par** | ✓ | `mk [a, b]` para cualesquiera `a, b : CList₊` |
| **Unión** | ✓ parcial | `⋃(mk xs)` siempre funciona. `⋃(inf P)` puede ser no-decidible |
| **Infinitud** | ✓ | `inf (fun _ => true)` representa $\omega = V_\omega$ |
| **Separación** | ✓ | `sep` sobre `inf P` con predicado decidible: `inf (P && Q)` |
| **Reemplazo** | ⚠ | Aplicar $f$ a todos los elementos de `inf P` requiere que $f$ preserve HFSets y sea computable |
| **Powerset** | ✗ | $\mathcal{P}(\text{inf } P)$ no es representable |
| **Fundación** | ✓ | Los `inf`-conjuntos contienen solo HFSets (bien fundados por §Foundation actual). No hay cadena $\in$ infinita descendente |

**Nota sobre Fundación**: Un `inf P` tiene como miembros solo HFSets, que son
árboles de rango finito. Ninguna cadena $\in$-descendente puede pasar indefinidamente por `inf`-conjuntos porque $\text{inf } P \ni h \ni h' \ni \ldots$ se reduce a una cadena dentro de HFSets, que termina por rango finito.

### 2.6. Caracterización matemática

**Teorema informal.** El universo de Nivel 1 es:

$$U_1 = \text{HF}\bigl(V_\omega \cup \text{Comp}(V_\omega)\bigr)$$

donde $\text{Comp}(V_\omega) = \{S \subseteq V_\omega \mid S \text{ es decidible}\}$
y $\text{HF}(X)$ denota los conjuntos hereditariamente finitos sobre un conjunto
base $X$.

Los elementos de $U_1$ son:

- **Nivel base**: Todos los HFSets (= elementos de $V_\omega$).
- **Nivel inf**: Todos los subconjuntos decidibles de $V_\omega$. Estos incluyen
  $\omega$ mismo, el conjunto de pares, los primos (codificados), etc.
- **Nivel mixto**: Conjuntos finitos cuyos elementos pueden ser HFSets o
  inf-conjuntos. Ejemplo: $\{\omega, \emptyset, \text{primos}\}$.

Nótese que **$U_1$ no se cierra bajo powerset infinito**. El powerset de $\omega$
requeriría todos los subconjuntos decidibles (= $\text{Comp}(V_\omega)$ como
conjunto), pero $\text{Comp}(V_\omega)$ mismo no es un elemento de $U_1$ — es
una clase propia respecto a $U_1$.

#### Conexión con la jerarquía aritmética

Los subconjuntos decidibles de $V_\omega \cong \omega$ corresponden exactamente a
la clase $\Delta^0_1$ de la jerarquía aritmética de Kleene-Mostowski:

$$\text{Comp}(V_\omega) = \Delta^0_1$$

Los conjuntos $\Sigma^0_1$ (r.e.) y $\Pi^0_1$ (co-r.e.) **no están** en $U_1$
directamente, porque requieren predicados semi-decidibles (`HFSet → Prop` sin
`Bool` totalmente definido).

#### Cardinalidades

| Colección | Cardinalidad |
|-----------|-------------|
| $V_\omega$ (HFSets) | $\aleph_0$ |
| $\text{Comp}(V_\omega)$ (decidibles) | $\aleph_0$ (contablemente muchos programas) |
| $U_1$ (Nivel 1 completo) | $\aleph_0$ |
| $V_{\omega+1} = \mathcal{P}(V_\omega)$ | $2^{\aleph_0}$ |
| $L_{\omega+1} = \text{Def}(V_\omega)$ | $\aleph_0$ |

Así, $U_1 \subsetneq L_{\omega+1} \subsetneq V_{\omega+1}$:

- $U_1$ solo tiene subconjuntos **decidibles** de $V_\omega$.
- $L_{\omega+1}$ tiene todos los subconjuntos **aritméticos** (definibles en primer
  orden): $\Sigma^0_n$, $\Pi^0_n$ para todo $n$.
- $V_{\omega+1}$ tiene **todos** los subconjuntos, incluyendo los no-definibles.

### 2.7. Esquema de implementación en Lean 4

```lean
-- Paso 1: Tipo pre-cociente
inductive CList₊ where
  | mk  : List CList₊ → CList₊
  | inf : (HFSet → Bool) → CList₊

-- Paso 2: Igualdad extensional (Prop, no decidible)
def CList₊.extEq : CList₊ → CList₊ → Prop := ...  -- ∀ x, x ∈ₛ a ↔ x ∈ₛ b

-- Paso 3: Cociente
instance : Setoid CList₊ := ⟨CList₊.extEq, ...⟩
def ASet := Quotient CList₊.instSetoid

-- Paso 4: Membresía (elevada al cociente)
def ASet.mem : ASet → ASet → Prop := Quotient.lift₂ CList₊.mem ...

-- Paso 5: Operaciones
def ASet.union : ASet → ASet → ASet := ...
def ASet.inter : ASet → ASet → ASet := ...
def ASet.sep : ASet → (ASet → Prop) → [DecidablePred] → ASet := ...

-- El axioma de infinitud:
def omega : ASet := ⟦CList₊.inf (fun _ => true)⟧
-- ω contiene todos los HFSets
```

#### Dificultades de implementación

1. **`extEq` no es decidible**: Se define como `Prop`, no como `Bool`. El cociente
   existe proposicionalmente (Lean 4 soporta `Quotient` con relaciones Prop).
   Pero `Quotient.lift` requiere probar que la función respeta la relación, y
   estas pruebas involucran cuantificación sobre todos los HFSets.

2. **Membresía recursiva**: `mem x (mk xs)` se define recursivamente sobre
   `CList₊`, pero `mem x (inf P)` necesita `embed⁻¹(x)` — la proyección de `x`
   a HFSet (solo definida si `isPure x`). Esto requiere un recursor bien fundado
   que maneje ambos casos.

3. **Pruebas de respeto para Quotient.lift**: Cada operación elevada al cociente
   necesita una prueba de que respeta `extEq`. Para `union` entre `inf`-conjuntos
   es simple (igualdad pointwise). Para operaciones mixtas, las pruebas son más
   elaboradas.

4. **Normalización**: A diferencia de HFSet donde `normalize` produce una forma
   canónica, en `CList₊` no hay normalización decidible para `inf`-conjuntos
   (por indecidibilidad de `extEq`).

---

## [3.] Estudio profundo: Nivel 1+ — iteración indexada por $\mathbb{N}$

### 3.1. Motivación

El Nivel 1 (§2) añade subconjuntos decidibles de $V_\omega$, pero no puede
representar subconjuntos decidibles de esos mismos conjuntos. Por ejemplo:

- El conjunto "todos los subconjuntos decidibles de $\omega$ que contienen al 0"
  es un subconjunto de $\text{Comp}(V_\omega)$, pero no es un elemento de $U_1$.
- $\mathcal{P}(\text{primos})$ necesitaría predicados sobre HFSets que son
  subconjuntos de primos — representable como `inf`, pero $\mathcal{P}(\omega)$
  como colección de `inf`-conjuntos no lo es.

La **iteración** resuelve esto: cada nivel permite subconjuntos decidibles del
nivel anterior.

### 3.2. Definición matemática recursiva

$$U_0 = V_\omega \quad (\text{= HFSet actual})$$
$$U_{n+1} = \text{HF}\bigl(U_n \cup \text{Comp}(U_n)\bigr)$$
$$U_\omega = \bigcup_{n < \omega} U_n$$

donde $\text{Comp}(X) = \{S \subseteq X \mid \text{la membresía en } S \text{ es decidible}\}$.

En cada paso:

- $U_n$ está dado (tipo base del nivel $n$).
- $\text{Comp}(U_n)$ son los subconjuntos de $U_n$ con función característica
  computable (como función $U_n \to \text{Bool}$).
- $\text{HF}(\cdots)$ envuelve todo en conjuntos hereditariamente finitos para
  permitir combinaciones finitas.

#### Los primeros niveles explícitos

| Nivel | Universo | Contiene |
|-------|----------|----------|
| $U_0$ | $V_\omega$ | $\emptyset, \{∅\}, \{∅,\{∅\}\}, \ldots$ — todos los HFSets finitos |
| $U_1$ | $\text{HF}(V_\omega \cup \text{Comp}(V_\omega))$ | Todo lo de $U_0$ + subconj. decidibles de $V_\omega$ (primos, pares, etc.) + combinaciones finitas |
| $U_2$ | $\text{HF}(U_1 \cup \text{Comp}(U_1))$ | Todo lo de $U_1$ + subconj. decidibles de $U_1$ (p.ej. "todos los subconj. decidibles de $\omega$ que contienen al $0$") |
| $U_3$ | $\text{HF}(U_2 \cup \text{Comp}(U_2))$ | Todo lo de $U_2$ + subconj. decidibles de $U_2$ |

#### Concretamente, ¿qué hay en $U_2$?

Un elemento de $\text{Comp}(U_1)$ es un subconjunto decidible de $U_1$, es decir,
una función $U_1 \to \text{Bool}$. Un ejemplo concreto:

- Sea $S = \{A \in U_1 \mid A \text{ es un inf-conjunto y } 0 \in A\}$.
  Esto es decidible si la membresía en $A$ lo es (y lo es por construcción de $U_1$).
  Entonces $S \in \text{Comp}(U_1) \subseteq U_2$.

- Sea $T = \{A \in U_1 \mid A \text{ es finito y } |A| \leq 3\}$.
  `|A|` es computable para `mk xs` (longitud de la lista tras normalización),
  y para `inf P` no hay un tamaño computable en general. Pero si `T` se
  restringe a los `mk`-conjuntos, sí es decidible.

### 3.3. Conexión con la jerarquía aritmética

La iteración $U_0, U_1, U_2, \ldots$ tiene una correspondencia precisa con los
niveles de la jerarquía aritmética, pero **relativizada**:

| Nivel | Subconjuntos de $\omega$ capturados | Clase aritmética |
|-------|-------------------------------------|------------------|
| $U_0$ | Solo los finitos y cofinitos (como HFSets) | $\Delta^0_0$ (primitiva recursiva) |
| $U_1$ | Todos los decidibles: función car. total computable | $\Delta^0_1$ (recursivo) |
| $U_2$ | Decidibles relativos a un $\Delta^0_1$-oráculo | $\Delta^0_2$ (computable en el salto de Turing) |
| $U_n$ | Decidibles relativos a un $\Delta^0_{n-1}$-oráculo | $\Delta^0_n$ |
| $U_\omega$ | Todos los aritméticos | $\bigcup_n \Delta^0_n$ = aritmético |

**¡Esto es notable!** $U_\omega$ captura exactamente los conjuntos de la
**jerarquía aritmética completa**, que es:

$$U_\omega \cap \mathcal{P}(\omega) = \bigcup_{n \geq 1} \Delta^0_n = \text{Aritmético}$$

La correspondencia se da mediante el **salto de Turing** (Turing jump). El salto
$\emptyset'$ (problema de parada para máquinas de Turing) está en $\Sigma^0_1$
pero no en $\Delta^0_1$. Sin embargo, cualquier conjunto decidible relativizado
a $\emptyset'$ está en $\Delta^0_2$. Y así sucesivamente:

- $\Delta^0_1$: decidible.
- $\Delta^0_2$: decidible con oráculo $\emptyset'$.
- $\Delta^0_n$: decidible con oráculo $\emptyset^{(n-1)}$ (salto iterado).

El **Teorema de Post** establece que $\Sigma^0_n \cup \Pi^0_n \subsetneq \Delta^0_{n+1}$, y un conjunto es $\Delta^0_n$ iff es decidible relativo a $\emptyset^{(n-1)}$.

#### ¿Es exacta la correspondencia?

No del todo. La correspondencia exacta depende de lo que signifique "decidible"
en $U_n$. Si interpretamos `ASet n → Bool` como **todas** las funciones totales
(no solo las computables), entonces $\text{Comp}(U_n)$ son todos los subconjuntos
de $U_n$ (porque en Lean 4, `X → Bool` incluye funciones no computables via
`Classical.choice`).

Para que la correspondencia aritmética sea exacta, necesitaríamos restringir
`inf` a funciones **computables**, lo cual requiere una noción de computabilidad
formalizada — un refinamiento que va más allá del proyecto actual, pero que es
teóricamente claro.

En la práctica de Lean 4, `X → Bool` incluye funciones definidas por recursión
estructural y pattern matching, que son todas computables. Las funciones no
computables solo aparecen si se usa `Classical.choice` o `Decidable.decide` con
instancias no constructivas. Así, si se evita `Classical` en la definición de
predicados, la correspondencia aritmética se mantiene informalmente.

### 3.4. Lean 4: el obstáculo de positividad estricta

La definición natural sería:

```lean
-- INTENTO (rechazado por Lean 4):
inductive ASet : Nat → Type where
  | fin  : List (ASet n) → ASet n
  | lift : ASet n → ASet (n + 1)
  | inf  : (ASet n → Bool) → ASet (n + 1)
```

**Lean 4 rechaza esto.** El constructor `inf` tiene `ASet n` en posición negativa
(a la izquierda de `→`). Aunque el índice `n` difiere de `n + 1`, la familia
`ASet` aparece en posición negativa, violando la positividad estricta.

Esto NO es un detalle técnico menor: es una restricción fundamental de tipos
inductivos que previene paradojas (como la paradoja de Russell en sistemas con
tipos auto-referentes).

### 3.5. Estrategias de implementación para Nivel 1+

#### Estrategia A: Definición recursiva nivel a nivel

```lean
def ASet : Nat → Type
  | 0     => HFSet
  | n + 1 => Quotient (@instSetoid (ASetPre n))

-- Pre-tipo para el nivel n+1:
inductive ASetPre (n : Nat) where
  | fin : List (ASetPre n) → ASetPre n
  | lift : ASet n → ASetPre n
  | inf : (ASet n → Bool) → ASetPre n
```

**Problema**: `ASet` y `ASetPre` son mutuamente recursivos. `ASet (n+1)` se define
en términos de `ASetPre n`, que a su vez menciona `ASet n`. Lean 4 no soporta
definiciones recursivas de tipos donde el caso recursivo es un `inductive` (los
inductivos deben ser definidos al top-level, no dentro de una recursión).

#### Estrategia B: Cada nivel como tipo separado

```lean
-- Nivel 0
-- Ya definido: HFSet (= Quotient CList.Setoid)

-- Nivel 1
inductive CList₁ where
  | mk  : List CList₁ → CList₁
  | inf : (HFSet → Bool) → CList₁
def ASet₁ := Quotient CList₁.Setoid  -- extEq₁ como relación

-- Nivel 2
inductive CList₂ where
  | mk  : List CList₂ → CList₂
  | inf : (ASet₁ → Bool) → CList₂
def ASet₂ := Quotient CList₂.Setoid

-- Nivel 3 ...
```

**Ventajas**: Cada nivel es un `inductive` válido en Lean 4 (positividad estricta
se respeta porque `ASet₁` es un tipo ya definido cuando se define `CList₂`).

**Desventajas**:

- Se necesitan infinitos niveles para $U_\omega$ — imposible definir finitamente.
- Cada nivel requiere repetir la maquinaria: `extEq`, `Quotient`, `mem`, `union`, etc.
- No se puede cuantificar uniformemente sobre "todos los niveles".

**Factibilidad**: Perfectamente viable para un número finito fijo de niveles
(digamos 2 o 3). Impracticable para $U_\omega$.

#### Estrategia C: W-tipo con decodificación

Los **W-tipos** (tipos inductivos bien fundados) generalizan los árboles:

```lean
-- W A B = árboles donde cada nodo de tipo a : A tiene B a hijos
inductive W (A : Type) (B : A → Type) where
  | mk : (a : A) → (B a → W A B) → W A B
```

Se puede codificar una jerarquía indexada usando:

```lean
-- Código para el tipo de nodos de nivel n
def Code : Nat → Type
  | 0     => Unit              -- HFSet: un solo tipo de nodo
  | n + 1 => Code n ⊕ (Decode n → Bool)   -- fin ⊕ inf

-- Decodificación: el tipo representado por un código
def Decode : Nat → Type
  | 0     => HFSet
  | n + 1 => W (Code (n + 1)) (Branches (n + 1))
```

Este enfoque "Tarski-style" (universo à la Tarski) es más complejo pero evita
la violación de positividad. Requiere un trabajo de ingeniería considerable.

#### Estrategia D: Tipo inductivo-recursivo (no soportado nativamente)

En Agda, se podría usar un tipo inductivo-recursivo:

```agda
mutual
  data ASet : ℕ → Set where
    fin : List (ASet n) → ASet n
    inf : (ASet n → Bool) → ASet (suc n)

  -- Junto con una función de decodificación definida simultáneamente
```

Lean 4 **no soporta** tipos inductivo-recursivos. Se tendría que simular con
`unsafe` + `implementedBy`, o con una codificación indirecta.

### 3.6. ¿Qué axiomas cumple $U_\omega$?

Suponiendo que se construye $U_\omega = \bigcup_n U_n$:

| Axioma | ¿Se cumple? | Justificación |
|--------|-------------|---------------|
| **Extensionalidad** | ✓ | Por cociente en cada nivel |
| **Vacío** | ✓ | `fin [] ∈ U_0 ⊆ U_\omega` |
| **Par** | ✓ | `{a, b}` vive en $U_{\max(n_a, n_b)}$ |
| **Unión** | ✓ parcial | Para `mk`-conjuntos sí. Para `inf`-conjuntos, depende (ver §2.4.5) |
| **Infinitud** | ✓ | `inf (fun _ => true) ∈ U_1` |
| **Separación** | ✓ | Con predicado decidible del nivel adecuado |
| **Powerset** | ✓ para $U_n$ | $\mathcal{P}_{\text{dec}}(U_n) \subseteq U_{n+1}$. Pero $\mathcal{P}(U_\omega)$ escapa |
| **Reemplazo** | ⚠ | Requiere que la función de reemplazo mapee entre niveles apropiados |
| **Fundación** | ✓ | Cada nivel está bien fundado por inducción sobre $n + $ rango HFSet |

**Observación clave sobre Powerset**: En $U_\omega$, para cada $A \in U_n$:

$$\mathcal{P}_{\text{dec}}(A) \in U_{n+1}$$

Esto da un **Powerset decidible**: no el powerset completo, pero sí todos los
subconjuntos con membresía decidible. Esto es suficiente para muchas
construcciones matemáticas (y es exactamente lo que captura la jerarquía
aritmética iterada).

### 3.7. ¿Qué captura $U_\omega$ matemáticamente?

$$U_\omega = \bigcup_{n < \omega} U_n$$

En términos de la jerarquía constructible de Gödel:

$$V_\omega = L_\omega \subseteq U_\omega \subseteq L_{\omega+\omega}$$

Más precisamente, los subconjuntos de $\omega$ en $U_\omega$ son exactamente los
**conjuntos aritméticos** — aquellos definibles en la aritmética de Peano con
cuantificadores sobre naturales:

$$U_\omega \cap \mathcal{P}(\omega) = \bigcup_n \Delta^0_n$$

Esto es estrictamente más pequeño que los conjuntos **hiperaritméticos**
($\Delta^1_1$), que se obtendrían al iterar transfinitamente hasta el ordinal
$\omega_1^{CK}$ (ordinal de Church-Kleene).

#### Inclusiones estrictas

$$V_\omega \subsetneq U_\omega \subsetneq L_{\omega_1^{CK}} \subsetneq L_{\omega_1} \subsetneq V_{\omega+1}$$

| Universo | Conjuntos de naturales | Cardinalidad |
|----------|----------------------|-------------|
| $V_\omega$ | Solo finitos/cofinitos | $\aleph_0$ |
| $U_\omega$ | Aritméticos ($\bigcup_n \Delta^0_n$) | $\aleph_0$ |
| $L_{\omega_1^{CK}}$ | Hiperaritméticos ($\Delta^1_1$) | $\aleph_0$ |
| $L_{\omega_1}$ | Todos los contable-definibles | $\aleph_0$ |
| $V_{\omega+1}$ | Todos ($\mathcal{P}(\omega)$) | $2^{\aleph_0}$ |

### 3.8. ¿Merece la pena la complejidad?

#### Argumentos a favor de Nivel 1+ ($U_\omega$)

1. **Completitud aritmética**: Captura todos los conjuntos definibles en aritmética de primer orden — un universo natural desde el punto de vista de la lógica computacional.
2. **Powerset decidible iterado**: Cada nivel tiene powerset decidible. Muchas construcciones de la matemática (espacios de funciones, topología puntual) solo necesitan subconjuntos decidibles.
3. **Jerarquía natural**: La indexación por $\mathbb{N}$ proporciona una estructura
   de "complejidad" que puede ser útil para razonar sobre definibilidad.

#### Argumentos en contra

1. **Complejidad de implementación alta**: Incluso con la Estrategia B (niveles explícitos), cada nivel replica toda la infraestructura.
2. **No se alcanza $U_\omega$ finitamente**: En Lean 4 solo podemos definir $U_n$ para $n$ concretos. El límite $U_\omega$ requeriría un tipo dependiente o una codificación Tarski compleja.
3. **Marginalidad**: Para la mayoría de las construcciones matemáticas interesantes (análisis, topología, álgebra), se necesita $V_{\omega+1}$ completo o al menos los conjuntos hiperaritméticos. $U_\omega$ es "demasiado" para conjuntos finitos pero "insuficiente" para el análisis.
4. **Igualdad no decidible**: A partir de $U_1$, la igualdad deja de ser decidible. Se pierde el carácter computacional que hace especial a HFSet.

### 3.9. Comparación: Nivel 1 vs Nivel 1+

| Criterio | Nivel 1 (`fin + inf`) | Nivel 1+ ($U_n$ indexado) |
|----------|----------------------|---------------------------|
| **Lean 4 factible** | ✓ Sí (inductive directo) | ⚠ Solo niveles explícitos finitos |
| **Positividad estricta** | ✓ | ✗ (como familia indexada) |
| **DecidableEq** | ✗ (perdido) | ✗ (perdido desde $n \geq 1$) |
| **Axioma de infinitud** | ✓ | ✓ |
| **Powerset** | ✗ (para inf-conjuntos) | ✓ parcial (nivel-a-nivel) |
| **Separación decidible** | ✓ | ✓ |
| **Universo matemático** | $\text{HF}(V_\omega \cup \Delta^0_1)$ | $\bigcup_n \text{HF}(U_{n-1} \cup \Delta^0_n)$ |
| **Esfuerzo de implementación** | Moderado | Alto |
| **Reutilización de HFSet** | Alta (HFSet intacto) | Alta (HFSet = nivel 0) |
| **Elegancia teórica** | Buena (un paso natural) | Excelente (cierre aritmético) |

### 3.10. Recomendación

**Para este proyecto, Nivel 1 es la elección correcta como siguiente paso.**

Razones:

1. Es directamente implementable en Lean 4 como un solo `inductive`.
2. Proporciona el axioma de infinitud — el axioma que más falta hace.
3. La pérdida de `DecidableEq` es inevitable en cualquier extensión a infinito.
4. La infraestructura desarrollada (membresía, extensionalidad, cociente, operaciones)
   se transfiere bien desde HFSet.
5. Nivel 1+ puede construirse **sobre** Nivel 1 en el futuro si se desea.

El Nivel 1+ queda documentado como dirección futura y marco teórico. Si alguna
vez se necesita ir más allá de $\Delta^0_1$, la Estrategia B (niveles explícitos)
permite definir `ASet₂` y `ASet₃` sin tocar `ASet₁`.

### 3.11. Dudas abiertas

- Supongamos que además de admitir el conjunto `ω` como urelemento, admitimos también los conjuntos de la forma `{x ∈ ω | P(x)}` (`axioma de separación`) o alguna forma más fuerte como el `axioma de reemplazo`, dónde todo lo que pedimos es que `P` sea decidible y computable para cada `x`. Esto nos permitiría construir subconjuntos decidibles de `ω` y avanzaríamos sobre la jerarquía de construibles. Solo veo el problema de que no conozco la codificación posible. ¿Nos permitría llegar más lejos. ¿O habría que avanzar a los `W-Trees`?

#### 3.11.1. Respuesta: separación/reemplazo sobre ω no llega a Nivel 2

**Separación `{x ∈ ω | P(x)}` con P decidible**: ya está capturada por el constructor `inf : (HFSet → Bool) → CList₁` de Nivel 1. La codificación usa los ordinales de von Neumann ya presentes en el proyecto (`𝟘`–`𝟡`):

```lean
{x ∈ ω | P(x)}  ≅  inf (fun a => isVonNeumann a && P (toNat a))
```

No hay ganancia: la separación sobre ω con predicados decidibles no sale de Δ⁰₁.

**Reemplazo `{F(x) | x ∈ ω}` con F : ℕ → HFSet computable**: la imagen de F es un conjunto computably-enumerable (Σ⁰₁). Hay conjuntos Σ⁰₁ \ Δ⁰₁ (p.ej. ∅′ = problema de la parada), así que el reemplazo sobre ω sí añade algo respecto a Nivel 1 puro.
Pero Σ⁰₁ ⊊ Δ⁰₂, así que **no llegamos a Nivel 2**.

**Para llegar a Nivel 2** se necesita `inf : (ASet₁ → Bool) → CList₂` — predicados
sobre el universo Nivel 1 entero, no solo sobre ω. El dominio del `inf` debe ser el
tipo `ASet₁`, no `ℕ`. Esto es la Estrategia B (§3.5): definir `CList₂` con `ASet₁`
como tipo de índice.

**W-Trees**: son una herramienta de **codificación en Lean 4** (Estrategia C, §3.5)
para definir la familia indexada `ASet n` sin violar positividad estricta. No son un
universo matemático distinto; son necesarios solo si se quiere U_ω en un único tipo.
La pregunta sobre separación/reemplazo es independiente de si se usan W-trees.

**Resumen**:

| Extensión                       | Captura        | ¿Sale de Nivel 1?           |
|---------------------------------|----------------|-----------------------------|
| Separación sobre ω (P : Bool)   | Δ⁰₁            | No (ya en Nivel 1)          |
| Reemplazo sobre ω (F : ℕ → HFS) | Δ⁰₁ ∪ Σ⁰₁      | Marginalmente (Σ⁰₁ ⊊ Δ⁰₂)   |
| Predicados sobre U₁             | Δ⁰₂            | Sí (= Nivel 2)              |

### 3.12. Referencias adicionales

- **Post, E. L. (1944)**. "Recursively enumerable sets of positive integers and
  their decision problems". *Bull. AMS* 50. — Teorema de Post y jerarquía aritmética.
- **Rogers, H. Jr. (1967)**. *Theory of Recursive Functions and Effective Computability*.
  MIT Press. — Referencia canónica para la jerarquía aritmética y salto de Turing.
- **Soare, R. (1987)**. *Recursively Enumerable Sets and Degrees*. Springer. —
  Tratamiento moderno de la teoría de la recursión.
- **Hyland, J. M. E. (1982)**. "The Effective Topos". *Brouwer Centenary Symposium*.
  — Topos efectivo: marco categórico para la computabilidad, donde los objetos
  llevan datos de realizabilidad.
- **Moschovakis, Y. N. (1980)**. *Descriptive Set Theory*. North-Holland. —
  Jerarquías descriptivas (aritmética → analítica → proyectiva).
- **Kleene, S. C. (1943)**. "Recursive predicates and quantifiers". *Trans. AMS* 53.
  — Definición original de la jerarquía aritmética.

---

## [4.] Decisión de diseño: alcance del proyecto AczelSetTheory

**Fecha**: 2026-04-08
**Decisión**: Nivel 1 simple (`fin + inf`).

### 4.1. Contexto de proyectos

Este proyecto (**AczelSetTheory**) es uno de cuatro que eventualmente se fusionarán:

| Proyecto | Alcance | Universo |
|----------|---------|----------|
| **AczelSetTheory** (este) | Conjuntos hereditariamente finitos + extensión decidible | $V_\omega$ → $U_1 = \text{HF}(V_\omega \cup \Delta^0_1)$ |
| **ZFC** (futuro) | Teoría de conjuntos ZFC completa | $V$ (clase universal) |
| **Peano** (existente) | Números naturales de Peano | $\omega$ |
| **MK+CAC** (futuro) | Morse-Kelley + Axioma de Elección Contable | Clases y conjuntos |

### 4.2. Rol de AczelSetTheory en el ecosistema

AczelSetTheory explora el fragmento **computacionalmente decidible** de la teoría
de conjuntos:

- **$V_\omega$ (Phases 1–11)**: Conjuntos hereditariamente finitos. Todo es
  decidible: membresía, igualdad, subconjunto, operaciones. Equivalente a
  ZF$^{-\infty}$ (ZF sin infinitud). Axioma de Elección derivable.

- **$U_1$ (Phase futura)**: Extensión con `inf : (HFSet → Bool) → CList₊`.
  Membresía decidible, igualdad **no** decidible. Captura $\Delta^0_1$ — los
  subconjuntos recursivos de $\omega$. Axioma de infinitud disponible.
  Powerset solo para conjuntos finitos.

Lo que AczelSetTheory **no** pretende cubrir:

- Conjuntos no computables ($\Sigma^0_1$, jerarquía analítica, etc.)
- Powerset completo sobre infinitos
- Grandes cardinales, forcing, independencia
- Axiomas que requieran $V_{\omega+1}$ o superior

Estos quedan para el proyecto **ZFC**.

### 4.3. Beneficios de la separación

1. **AczelSetTheory queda autocontenido**: todo dentro de $V_\omega$ (y eventualmente $U_1$) es computable y verificable algorítmicamente.
2. **Interface limpia con Peano**: La codificación von Neumann ($n \mapsto \{0, 1, \ldots, n-1\}$) ya está desarrollada. Al fusionar, Peano se recibe como subestructura de $V_\omega$.
3. **ZFC reutiliza la infraestructura**: Las definiciones de relación, función,
   inyectiva, suryectiva, biyectiva, etc., se transfieren directamente — solo
   cambia el tipo base de `HFSet` a un tipo axiomático `Set`.
4. **MK+CAC complementa**: Donde AczelSetTheory usa `Classical.choice` para
   funciones (Phase 10: `noncomputable def apply`), MK+CAC proporcionará una
   teoría de clases más expresiva con el Axioma de Elección Contable.

---

## [5.] Algunas ideas propuestas para pensar

- En principio, tenemos la opciónd e tener formas más expresivas de lo que ya tenemos. Por ejemplo, podemos usar HFSet (cualquier tipo de contenido), HFList (cualquier tipo de contenido), HFGraph A -> B, HFFun A -> B, HFNat 45, HFTup A B C, y quizás algunos más. Me pregunto sic onseguiríamos una teoría más expresiva teniendo también un HFAlpha, esto es, un tipo alfabeto 'UNICODE' que contenga todos los caracteres posibles. Habría que distinguir los caracteres de las cifras numéricas, o los caracteres usadose en la propia codificación. Expreso a continuación mi idea. Habría que encontrar el tipo de conjunto que constituirían los caracteres, y luego definir un constructor `HFAlpha : (Char -> Bool) -> HFAlpha` que permita construir conjuntos de caracteres a partir de predicados decidibles sobre caracteres. En principio podríamos verlos como `HFAlpha : Fin (2^24)-1 -> HFAlpha` (asumiendo un alfabeto de 24 bits, creo, para `UNICODE`), pero esto no es tan flexible como permitir cualquier subconjunto decidible de caracteres. Si posteriormente queremos definir los caracteres LaTeX, podríamos usar algo más complejo, básicamente un `ASCII (7 bits) strings -> LaTeX sobre ASCII mínimo -> HFAlpha`, por ejemplo.

```lean
inductive Element : Type
  | HFList : HFList -> Element
  | HFFun : (A B : HFSet) -> (A -> B) -> Element
  | HFGraph : (A B : HFSet) -> (A -> B) -> Element
  | HFNat : Nat -> Element
  | HFTup : (A B C : HFSet) -> (A × B × C) -> Element
  | HFAlpha : (k : Nat) -> (h : k < (2^24)) -> (Char -> Bool) -> Element

inductive EHFset : Type -- Las propiedades deben ser decidibles, es decir, `Prop` debe ser `Bool`, las funciones `computables`, etc. para que el conjunto resultante sea decidible.
  | mk : HFSet -> EHFSet -- CONJUNTO HEREDITARIAMENTE FINITO NORMALIZADO
  | mk : EHFSet -> Prop -> EHFSet -- SEPARACIÓN DADA EL CONJUNTO Y LA PROPIEDAD
  | mk : HFFun -> EHFSet -> EHFSet -> EHFSet -- REEMPLAZO
  | mk_pair : EHFSet -> EHFSet -> EHFSet -- PAR
  | mk_union : EHFSet -> EHFSet -> EHFSet -- UNIÓN BINARIA (se podría flexibilizar con un constructor de n-aria unión)
  | mk_bigunion : EHFSet -> EHFSet -- UNIÓN DE UN CONJUNTO
  | mk_inter : EHFSet -> EHFSet -> EHFSet -- INTERSECCIÓN BINARIA (se podría flexibilizar con un constructor de n-aria intersección)
  | mk_biginter : EHFSet -> EHFSet -- INTERSECCIÓN DE UN CONJUNTO
  | mk_diff : EHFSet -> EHFSet -> EHFSet -- DIFERENCIA
  | mk_symmdiff : EHFSet -> EHFSet -> EHFSet -- DIFERENCIA SIMÉTRICA
  | mk_powset : EHFSet -> Prop -> EHFSet -- SEPARACIÓN DADA EL CONJUNTO Y LA PROPIEDAD PARA EL POWERSET
  | mk_powset : Prop -> EHFSet -> EHFSet -- REEMPLAZO PARA EL POWERSET
  | mk_powset : EHFSet -> EHFSet -- POWERSET
  | mk_cart : EHFSet -> EHFSet -> EHFSet -- PRODUCTO CARTESIANO (se podría flexibilizar con un constructor de n-ario producto cartesiano)
  | mk : EHFFun {A B : EHFSet} (A -> B) -> EHFSet -- CONJUNTO DE FUNCIONES ENTRE DOS CONJUNTOS
  | mk : EHFGraph {A B : EHFSet} (A -> B) -> EHFSet -- CONJUNTO DE GRAFOS ENTRE DOS CONJUNTOS
  | mk : HFFin n -> EHFSet -- CONJUNTO DE LOS N PRIMEROS NÚMEROS NATURALES
  | ... -- Otros constructores posibles, como el de conjuntos de caracteres a partir de predicados decidibles sobre caracteres, y funciones computables entre EHFSet, etc.
  | mkfromlist : HFList -> EHFSet
  | mkfromfun : (f : EHFFun) (A B : EHFSet) -> EHFSet
  | mkfromgraph : (f : EHFGraph) (A B : EHFSet) -> EHFSet
  | mkfromnat : Nat -> EHFSet
  | mkfromtup : (A B C : EHFSet) -> (A × B × C) -> EHFSet -- flexbilizar para un número cualquiera de componentes
  | mkchar : (k : Nat) -> ((h : k < (2^24)) -> (Char -> Bool)) -> EHFSet -- El 24 es poi UNICODE, pero se podría flexibilizar para admitir cualquier alfabeto decidible de caracteres.
  | mkstring : HFList EHFAlpha -> EHFSet
  ```

  En el tipo inductivo de `EHFSet`, cada cosa que nos ea EHFSet, podría ser un `Element`. La idea no es obtener un universo de conjuntos más grande, sino un universo de conjuntos más expresivo, que permita representar objetos matemáticos más complejos (funciones, grafos, tuplas, caracteres, etc.) como elementos de conjuntos. Esto podría facilitar la codificación de objetos matemáticos dentro de la teoría de conjuntos, y permitir una representación más directa de conceptos matemáticos comunes. Sin embargo, habría que asegurarse de que las propiedades decidibles y las funciones computables se mantengan para garantizar que el universo resultante siga siendo decidible.


## [6.] Funciones que faltan por definir

### [6.1] Funciones multiplicativas clásicas

#### Diagnóstico: base disponible en Peano

| Primitivo | Estado |
|-----------|--------|
| `gcd`, `lcm`, `coprime` | ✅ en Peano + HFSet |
| `Prime`, `isPrimeb` (Bool) | ✅ en Peano + HFSet |
| `smallestDivisor n` | ✅ en Peano (computable) |
| `totient φ` | ✅ en Peano + HFSet |
| FTA (existencia + unicidad) | ✅ en Peano + HFSet |
| `factorize n → FactFSet` | ✅ en Peano pero **opaco** |

**Brecha crítica:** `FactFSet` es una estructura interna sin API pública — no se puede extraer el exponente de cada factor primo. Para construir funciones multiplicativas necesitamos `vp(n)` (valuación p-ádica), que hay que construir desde cero.

```RESPUESTA JULIÁN
FactFSet: ¿se te ocurre una API pública para poder usar la factorización sin exponer la estructura interna? Por ejemplo, podríamos definir (sobre FactFSet) una función `padicVal : ℕ → ℕ₀` que devuelva el exponente de un primo dado en la factorización de n. Esto nos permitiría definir funciones multiplicativas clásicas como `squarefree`, `rad`, `ω(n)`, `Ω(n)`, etc., sin necesidad de exponer la estructura interna de FactFSet. La implementación de `padicVal` podría ser recursiva, dividiendo repetidamente por el primo p hasta que ya no sea divisible.
```

```PROPUESTA JULIÁN
NECESITAMOS UN TIPO COMO \Nat₀, \Nat₁, \Nat₂ pero para primos, \Primes, un subtipo de \Nat\_2 que contenga solo los números primos. Luego, `padicVal : \Primes → \Nat₀` sería una función que, dado un primo p, devuelve el exponente de p en la factorización de n. Esto nos permitiría definir funciones multiplicativas clásicas como `squarefree`, `rad`, `ω(n)`, `Ω(n)`, etc., sin necesidad de exponer la estructura interna de FactFSet. La implementación de `padicVal` podría ser recursiva, dividiendo repetidamente por el primo p hasta que ya no sea divisible.
Esto nos daría un mejor FactFSet.
NECESITAMOS definir un PRIMORIAL `primorial n = ∏_{p ≤ n} p` que nos permita generar los primos necesarios para la factorización. Esto también nos ayudaría a definir funciones multiplicativas clásicas como `squarefree`, `rad`, `ω(n)`, `Ω(n)`, etc., sin necesidad de exponer la estructura interna de FactFSet. La implementación de `padicVal` podría ser recursiva, dividiendo repetidamente por el primo p hasta que ya no sea divisible.
NOS FALTA LA PRUEBA DE QUE DADOS LOS PRIMEROS N PRIMOS, EXISTE UN PRIMO MAYOR COMO EL PRIMORIAL DE N + 1, QUE NOS GARANTIZA QUE SIEMPRE PODEMOS ENCONTRAR LOS PRIMOS NECESARIOS PARA LA FACTORIZACIÓN DE CUALQUIER N. Esto también nos ayudaría a definir funciones multiplicativas clásicas como `squarefree`, `rad`, `ω(n)`, `Ω(n)`, etc., sin necesidad de exponer la estructura interna de FactFSet. La implementación de `padicVal` podría ser recursiva, dividiendo repetidamente por el primo p hasta que ya no sea divisible.  
```

```RESPUESTA JULIÁN
Efectivamente no tenemos los tipos enteros y los racionales. No los definimos en Peano pensando que sería más natural tenerlos aquí, pero es cierto que para funciones multiplicativas como μ y λ, el signo es crucial. Para μ(n), el valor es 0 si n no es squarefree, y (-1)^ω(n) si n es squarefree. Para λ(n), el valor es (-1)^Ω(n). Sin un tipo de enteros con signo, no podemos representar estos valores directamente.
Tenemos que definir los enteros en AczelSetTheory, así como todo lo que teníamos previsto en Peano, pero aquí, Aczel sucede a Peano en desarrollo activo.
```

PENSAMIENTOS JULIÁN SOBRE $\mathbb{Z}_0$

Aparte de la creación del tipo de enteros $\mathbb{Z}_0$, esto es, el establecimiento de la relación de equivalencia entre pares de naturales, concretamente $∀ a,b ∈ \mathbb{N}_0 × \mathbb{N}_0, a \mathcal{E} b ⟺ π₁ a + π₂ b = π₂ a + π₁ b$. A partir de aquí, el tipo de los enteros $\mathbb{Z}_0 := (\mathbb{N}_0 × \mathbb{N}_0) / \mathcal{E}$, y la definición de las operaciones de suma, resta, multiplicación, etc., sobre $\mathbb{Z}_0$ es relativamente directa. Sin embargo, hay que tener cuidado con la implementación de estas operaciones para asegurarse de que respetan la relación de equivalencia $\mathcal{E}$ y que se comportan como se espera para los enteros y los naturales embebidos en los enteros. Además habrá que crear la relación de orden lineal sobre $\mathbb{Z}_0$ y demostrar que es un orden total compatible con las operaciones definidas. Además tendremos que dar un representante canónico de la clase de equivalencia para cada entero, que será aquel representantes que que tenga la forma $⟨ n, 0 ⟩$ o $⟨ 0, n ⟩$ dependiendo de si el entero es positivo o negativo, respectivamente. Esto nos permitirá definir la función `toInt : ℕ₀ → ℤ₀` que mapea cada natural a su representante canónico en los enteros, y la función `toNat : ℤ₀ → ℕ₀` que mapea cada entero a su valor absoluto como natural.

Resumiendo esta primera parte:
- Definir la relación de equivalencia $\mathcal{E}$ sobre $\mathbb{N}_0 × \mathbb{N}_0$.
- Definir el tipo de enteros $\mathbb{Z}_0$ como el cociente de $\mathbb{N}_0 × \mathbb{N}_0$ por la relación $\mathcal{E}$.
- Definir el representante canónico de cada clase de equivalencia en $\mathbb{Z}_0$.
- Establcer las funciones `toInt` y `toNat` para mapear entre $\mathbb{N}_0$ y $\mathbb{Z}_0$, demostrando que son inversas entre sí, y que `toInt` es inyectiva. Demostrar que cada natural representa su propia clase de euivalencia, es decir, `toInt n` representa la clase de equivalencia de $⟨ n, 0 ⟩$.
- Definir la relación de orden total sobre $\mathbb{Z}_0$.
- Demostrar que `toInt` es un orden-embedding, es decir, que preserva el orden entre $\mathbb{N}_0$ y $\mathbb{Z}_0`. Demostrar que el orden total se preserva exactamente, es decir, que para cada $a, b ∈ \mathbb{Z}_0$, $a ≤ b$, $a ≥ 0, b≥ 0$ si y solo si `toNat a ≤ toNat b`. También para el orden estricto.
- Definir la operación de suma y de resta sobre $\mathbb{Z}_0$ y demostrar que es compatible con la relación de equivalencia, y con la relación de orden. Demostrar que conforma un grupo abeliano, cíclico, ${⟨ 1_{mathbb{Z}_0} ⟩}_{mathbb{Z}_0} = \mathbb{Z}_0$ y que `toInt` es un homomorfismo de grupos inyectivo (no totalmente porque $\mathbb{N}_0$ no es un grupo, sino un monoide conmutativo). Mostrar cual es el neutro y el inverso del a unidad. Mostrar el inverso aditivo de cualquier entero.
- Definir la operación de multiplicación sobre $\mathbb{Z}_0$ y demostrar que es compatible con la relación de equivalencia, y con la relación de orden. Demostrar que conforma un anillo conmutativo con unidad, y que `toInt` es un homomorfismo de anillos inyectivo (no totalmente porque $\mathbb{N}_0$ no es un anillo, sino un semianillo conmutativo). Mostrar cual es el neutro multiplicativo. Mostrar que el producto de dos enteros negativos es positivo, el producto de un entero negativo por uno positivo es negativo, y el producto de dos enteros positivos es positivo.
- Definir la función `neg`, `abs`, `sign` y `square` sobre $\mathbb{Z}_0$, y las principales propiedades de estas funciones. Mostrar que `neg` es un homomorfismo de grupos, que `abs` es un homomorfismo de monoides conmutativos, y que `sign` es un homomorfismo de monoides conmutativos a la multiplicación de signos. Mostrar que `square` es una función que preserva el orden, y que el cuadrado de cualquier entero es positivo o cero.


#### Mapa de capas

```
CAPA 0 — Primitivo clave
─────────────────────────
padicVal p n = exp. de p en n
(recursión: div repetida por p)

CAPA 1 — Sin signo, puras ℕ₀
─────────────────────────────
squarefree n   ↔  ∀p primo, padicVal p n ≤ 1
rad n          =  ∏ {p primo | p∣n}          (radical)
ω(n)           =  |{p primo | p∣n}|           (distintos)
Ω(n)           =  Σ_p padicVal p n            (con mult.)
divisors n     =  [d : ℕ₀ | d∣n, d∈[1..n]]
d(n) = τ(n)    =  |divisors n|
σ(n)           =  Σ_{d∣n} d
σ_k(n)         =  Σ_{d∣n} d^k
Jordan J_k(n)  =  n^k ∏_{p∣n} (1 − p^{−k})

CAPA 2 — Requieren signo (ℤ o codificación)
────────────────────────────────────────────
μ(n)   = 0 si !squarefree,  (-1)^ω(n) si squarefree
λ(n)   = (-1)^Ω(n)          (Liouville)

CAPA 3 — Teoría de convolución
───────────────────────────────
IsMultiplicative f   =  gcd m n = 1 → f(mn)=f(m)f(n)
(f ★ g)(n) = Σ_{d∣n} f(d)·g(n/d)   (Dirichlet)
Inversión de Möbius: f = μ ★ (f ★ 1)
```

#### Árbol de dependencias

```
padicVal p n          ← base de todo
    │
    ├── squarefree n  (∀p primo, padicVal p n ≤ 1)
    │       └── μ(n)  (0 si !squarefree, (-1)^ω(n) si squarefree)
    │
    ├── rad n         (∏ primos p con p∣n)
    │
    ├── ω(n)          (# de primos distintos que dividen n)
    │       └── λ(n)  (solo si hay ℤ; (-1)^Ω(n))
    │
    ├── Ω(n)          (# de factores primos con multiplicidad)
    │
    └── divisors n    (lista de todos los divisores)
            ├── d(n) = τ(n)   (# de divisores)
            ├── σ(n)           (suma de divisores)
            └── σ_k(n)         (suma de d^k)
```

#### Funciones con signo: decisión abierta

| Función | Valores | ¿Hay ℤ en Peano? |
|---------|---------|------------------|
| μ(n) | −1, 0, 1 | **No** — solo ℕ₀ |
| λ(n) | −1, 1 | **No** |

Para μ y λ hay tres caminos:
- **(a)** Usar el `Int` nativo de Lean: `μ : ℕ₀ → ℤ`, transporte directo.
- **(b)** Codificación `Bool × ℕ₀` (signo + magnitud). Más engorroso.
- **(c)** Definir solo predicados (`μ_pos`, `μ_neg`, `μ_zero`) como `Prop`. Sin extraer el entero.

Los caminos (a) y (c) son los limpios. El proyecto hasta ahora es 100% ℕ₀; entrar en ℤ es un cambio de registro.

#### Propuesta de fases

| Fase | Contenido | Dificultad |
|------|-----------|------------|
| **C1** | `padicVal`, `squarefree`, `rad`, `ω`, `Ω` | Media |
| **C2** | `divisors`, `d(n)=τ`, `σ`, `σ_k` | Media |
| **C3** | `μ` y `λ` (con decisión de signo) | Alta |
| **C4** | `IsMultiplicative`, convolución de Dirichlet, inversión de Möbius | Muy alta |
| **C5** | Transport de todo lo anterior a HFSet vía vN | Baja (patrón establecido) |

C1+C2 son directamente factibles con lo que ya hay. C3 depende de la decisión sobre ℤ. C4 es territorio de formalización seria (Mathlib-level).

#### Decisiones de diseño pendientes

1. **¿Dónde implementar `padicVal`, `divisors`, `d`, `σ`?**
   - **Opción A — En Peano** (añadir módulos a peanolib): garantiza que los resultados son lemas Peano transportables con el patrón `congrArg vN`. Consistente con Fermat, Wilson y CRT.
   - **Opción B — Directamente en AczelSetTheory** usando los primitivos de HFSet (`filter`, `card`, etc.): más rápido, pero rompe la simetría del proyecto.

2. **Para μ y λ: ¿`Int` nativo de Lean o solo predicados?**

3. **¿Llegar hasta la inversión de Möbius (C4), o solo las funciones individuales con sus propiedades clave?**

---

### [6.2] Computabilidad y decidabilidad en Peano

Peano tiene un módulo central `Peano.PeanoNat.Decidable` que agrega toda la infraestructura. El inventario es más rico de lo esperado.

#### Lo que existe en Peano

**Instancias para ℕ₀:**

```lean
DecidableEq ℕ₀           -- via deriving
BEq ℕ₀, Repr ℕ₀          -- via deriving
DecidableRel (@LT.lt ℕ₀)
DecidableRel (@LE.le ℕ₀)
Ord ℕ₀                    -- compare
```

**Instancias para predicados numéricos:**

```lean
decidablePrime     : Decidable (Prime n)       -- Primes.lean
decidableIsEven    : Decidable (IsEven n)      -- Arith.lean
decidableIsOdd     : Decidable (IsOdd n)       -- Arith.lean
instDecidableModEq : Decidable (ModEq n a b)   -- NumberTheory/ModEq.lean
```

**Funciones Bool (las "audit functions"):**

```lean
isPrimeb  (n : ℕ₀)      : Bool  -- ble₀ 𝟚 n && decide (smallestDivisor n = n)
dividesb  (d n : ℕ₀)    : Bool  -- decide ((n % d) = 𝟘)
blt₀, bgt₀, ble₀, bge₀ : Bool  -- comparaciones
```

**Instancias para estructuras derivadas:**

```lean
DecidableEq ℕ₁, DecidableEq ℕ₂
DecidableEq (List ℕ₀)
DecidableEq (Fin₀ m)
DecidableEq (FSet ℕ₀)
DecidableEq (Tuple α n), DecidableEq (HTuple ts)
```

#### Brechas en Peano

- No existe `Decidable (a ∣ b)` como instancia — solo `dividesb` Bool.
- No existe `dividesb_iff_divides` (teorema de equivalencia Bool ↔ Prop).
- No existe `isCoprimeB`.

#### Lo que habría que añadir en AczelSetTheory

Un módulo `Axioms/Computability.lean` (o extender el existente `Axioms/Decidable.lean`) con instancias decidibles para los predicados HFSet que ya tenemos:

```lean
-- Derivadas directamente vía vN + instancias Peano
instance : Decidable (dvd_HF (vN n) (vN m))        -- via dividesb
instance : Decidable (prime_HF (vN n))              -- via decidablePrime
instance : Decidable (coprime_HF (vN n) (vN m))    -- via decide (gcd n m = 𝟙)
instance : Decidable (vN a ≡ₕ vN b [MODHF vN n])  -- via instDecidableModEq

-- Funciones de evaluación directa (#eval)
def isPrimeb_HF  (x : HFSet) : Bool
def dividesb_HF  (a b : HFSet) : Bool
```

Esto permitiría usar `decide` y `#eval` directamente sobre predicados HFSet.