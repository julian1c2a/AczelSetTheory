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

1. **Completitud aritmética**: Captura todos los conjuntos definibles en aritmética
   de primer orden — un universo natural desde el punto de vista de la lógica
   computacional.
2. **Powerset decidible iterado**: Cada nivel tiene powerset decidible. Muchas
   construcciones de la matemática (espacios de funciones, topología puntual) solo
   necesitan subconjuntos decidibles.
3. **Jerarquía natural**: La indexación por $\mathbb{N}$ proporciona una estructura
   de "complejidad" que puede ser útil para razonar sobre definibilidad.

#### Argumentos en contra

1. **Complejidad de implementación alta**: Incluso con la Estrategia B (niveles
   explícitos), cada nivel replica toda la infraestructura.
2. **No se alcanza $U_\omega$ finitamente**: En Lean 4 solo podemos definir $U_n$
   para $n$ concretos. El límite $U_\omega$ requeriría un tipo dependiente o
   una codificación Tarski compleja.
3. **Marginalidad**: Para la mayoría de las construcciones matemáticas interesantes
   (análisis, topología, álgebra), se necesita $V_{\omega+1}$ completo o al menos
   los conjuntos hiperaritméticos. $U_\omega$ es "demasiado" para conjuntos finitos
   pero "insuficiente" para el análisis.
4. **Igualdad no decidible**: A partir de $U_1$, la igualdad deja de ser decidible.
   Se pierde el carácter computacional que hace especial a HFSet.

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

### 3.11. Referencias adicionales

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
