# Plan de demostración: `normalizar_eq_of_eq` y lemmas auxiliares

## Estado actual del archivo

| Teorema | Estado | Ubicación |
|---|---|---|
| `reducirDuplicados_nodup` | ✅ Completo | L303–353 |
| `SetEquiv.refl/symm/trans` | ✅ Completo | L363–375 |
| `pertenece_eq_any` | ✅ Completo | L379–395 |
| `esIgual_mk_iff_setEquiv` | ✅ Completo | L403–488 |
| `reducirDuplicados_set_equiv_self` | ✅ Completo | L493–576 |
| `normalizar_eq_of_eq` | ⚠️ Un `sorry` | L602–658 |
| `CList.Setoid` | ✅ Completo | L582–590 |
| `CSet.repr` | ✅ (depende del sorry) | L668 |

El único bloqueo es el `sorry` en la línea 649:

```lean
have h_canon_eq : ordenarLista (reducirDuplicados (Ax.map normalizar)) =
                  ordenarLista (reducirDuplicados (Bx.map normalizar)) := by
  sorry
```

---

## Análisis del problema

### Contexto disponible dentro del `sorry`

Al llegar a ese punto dentro de `normalizar_eq_of_eq` (caso `A = mk Ax`, `B = mk Bx`), ya se tienen:

- `h_equiv_Ax_Bx : SetEquiv Ax Bx`
- `h_equiv_map : SetEquiv (Ax.map normalizar) (Bx.map normalizar)`
- `h_equiv_reduced : SetEquiv l₁ l₂` donde `l₁ = reducirDuplicados (Ax.map normalizar)`,
  `l₂ = reducirDuplicados (Bx.map normalizar)`
- `h_nodup1 : Nodup l₁`
- `h_nodup2 : Nodup l₂`
- **IH de `normalizar_eq_of_eq`**: para `a ∈ Ax, b ∈ Bx` con `esIgual a b = true`,
  se tiene `normalizar a = normalizar b` (porque `cSize a + cSize b < cSize A + cSize B`).

### ¿Por qué el `sorry` es difícil?

La dificultad central es que `esMenor` **no está bien definido en clases de equivalencia** de `esIgual`.
Ejemplo concreto:
- `A  = mk [∅, {∅}]` tiene `cSize 7`
- `A' = mk [{∅}, ∅]` tiene `cSize 7` (mismos elementos, distinto orden)
- `esIgual A A' = true` pero los estructurales son distintos
- Para un tercero `X` con `cSize 4`, tendríamos `esMenor A X = false` y `esMenor A' X = false`
  igual, pero esto puede diferir para otros `X`.

Esto significa que si `ordenarLista` produce una lista en la que algún elemento `esIgual` a otro
but no `=` (propositional), el resultado final puede diferir aunque los elementos sean el mismo "conjunto".

**La clave**: Los elementos de `l₁` y `l₂` son **todos outputs de `normalizar`**, no `CList` arbitrarios.
Si podemos probar que en ese contexto `esIgual na nb = true → na = nb` (igualdad proposicional),
entonces `l₁` y `l₂` son permutaciones propositionales la una de la otra, y `ordenarLista` daría
el mismo resultado.

---

## Estrategia de demostración

### Pieza 1: Idempotencia de `normalizar`

```lean
theorem normalizar_idem (A : CList) : normalizar (normalizar A) = normalizar A
```

**Por qué es suficiente**: Con esto, dentro del caso inductivo:
- Elementos de `l₁`: `na = normalizar a` para `a ∈ Ax`.
- IH aplicada a `(na, nb)` (donde `na = normalizar a, nb = normalizar b` con `a ∈ Ax, b ∈ Bx`):
  - `cSize na ≤ cSize a < cSize A`, `cSize nb ≤ cSize b < cSize B`, así que `cSize na + cSize nb < cSize A + cSize B`. ✓
  - Si `esIgual na nb = true`, la IH da `normalizar na = normalizar nb`.
  - Por idempotencia: `normalizar na = na` y `normalizar nb = nb`.
  - Luego `na = nb`. ✓

**Prueba de idempotencia** (por inducción sobre `cSize A`):

Caso base `A = mk []`: trivial.

Caso inductivo `A = mk xs`:
1. `normalizar A = mk ys` donde `ys = ordenarLista (reducirDuplicados (xs.map normalizar))`.
2. `normalizar (normalizar A) = normalizar (mk ys) = mk (ordenarLista (reducirDuplicados (ys.map normalizar)))`.
3. Por IH sobre `x ∈ xs`: `normalizar (normalizar x) = normalizar x`.
4. Luego `ys.map normalizar = ys.map (fun y => normalizar y)`. Pero cada `y ∈ ys` es de la forma
   `normalizar x`, así `normalizar y = normalizar (normalizar x) = normalizar x = y`.
   **Conclusión**: `ys.map normalizar = ys`.
5. Entonces `reducirDuplicados (ys.map normalizar) = reducirDuplicados ys`.
6. Como `ys = ordenarLista (...)`, por el lema **Nodup-de-ordenarLista**: `Nodup ys`.
7. Por el lema **reducirDuplicados-id-sobre-Nodup**: `reducirDuplicados ys = ys`.
8. Como `ys = ordenarLista (...)`, por el lema **ordenarLista-fijo-punto-de-Sorted**:
   `ordenarLista ys = ys` (pues `Sorted ys` y `Nodup ys`).
9. Por tanto `normalizar (normalizar A) = mk ys = normalizar A`. ✓

**Cota de terminación** de la inducción: `cSize A` (no `cSize A + cSize B` como en el teorema principal).
Para `x ∈ xs`, `cSize x < cSize (mk xs) = cSize A`. ✓

**Lema auxiliar necesario para el paso 4**: Para `x ∈ xs`,
`cSize (normalizar x) ≤ cSize x` (normalizar no aumenta el tamaño). Ver Pieza 3.

---

### Pieza 2: Lemas sobre `ordenarLista`

#### L1: `Nodup (ordenarLista l)`
```lean
theorem ordenarLista_nodup (l : List CList) : Nodup (ordenarLista l)
```
Prueba: Por inducción. `ordenarLista l = insertarOrdenado x (ordenarLista xs)`.
- Por IH: `Nodup (ordenarLista xs)`.
- `insertarOrdenado` comprueba `esIgual x y` antes de insertar → no añade duplicados.
- Formalmente: si `y ∈ ordenarLista xs` y `esIgual x y = true`, entonces `insertarOrdenado x (ordenarLista xs)` **no** incluye `x` (la rama `esIgual x y` retorna `y :: ys` sin `x`).

**Sub-lema**: `∀ y ∈ ordenarLista xs, esIgual x y = true → x ∉ insertarOrdenado x (ordenarLista xs)`.
(En realidad basta probar que `insertarOrdenado` es nodup si la lista entrada es nodup y `x` no está.)

#### L2: `Sorted (ordenarLista l)`
```lean
-- Definición
def Sorted : List CList → Prop
  | [] | [_] => True
  | a :: b :: rest => esMenor a b = true ∧ Sorted (b :: rest)

theorem ordenarLista_sorted (l : List CList) : Sorted (ordenarLista l)
```
Prueba: Por inducción. El llave es demostrar que `insertarOrdenado x ys` produce una lista `Sorted`
si `Sorted ys`. Eso requiere saber que si `esMenor x y = false ∧ esIgual x y = false`, entonces
`esMenor y x = true` (totalidad de `esMenor`).

**Dependencia**: requiere totality de `esMenor` (ver Pieza 4).

#### L3: `reducirDuplicados l = l` cuando `Nodup l`
```lean
theorem reducirDuplicados_id_of_nodup (l : List CList) (h : Nodup l) : reducirDuplicados l = l
```
Prueba: Por inducción fuerte sobre `l` con el auxiliar paramétrico:
```
∀ vistos, Nodup l → (∀ x ∈ l, ¬ vistos.any (fun v => esIgual x v) = true) →
  reducirDuplicadosAux l vistos = l
```
La condición dice "ningún elemento de l ya está en vistos". En el caso base con vistos = [], trivialmente cierto.

#### L4: `ordenarLista l = l` cuando `Sorted l` y `Nodup l`
```lean
theorem ordenarLista_id_of_sorted_nodup (l : List CList) (h_s : Sorted l) (h_nd : Nodup l) :
    ordenarLista l = l
```
Prueba: Por inducción.
- `l = []`: trivial.
- `l = [x]`: `insertarOrdenado x [] = [x]`. ✓
- `l = x :: y :: rest`:
  - `h_s` da `esMenor x y = true` y `Sorted (y :: rest)`.
  - Por IH: `ordenarLista (y :: rest) = y :: rest`.
  - `ordenarLista l = insertarOrdenado x (y :: rest)`.
  - Como `esMenor x y = true`, `insertarOrdenado x (y :: rest) = x :: y :: rest = l`. ✓

---

### Pieza 3: Normalizar no aumenta el tamaño

```lean
theorem normalizar_cSize_le (A : CList) : cSize (normalizar A) ≤ cSize A
```
Prueba: Por inducción sobre `cSize A`.

`cSize (normalizar (mk xs)) = 1 + cSizeList (ordenarLista (reducirDuplicados (xs.map normalizar)))`

- `cSizeList (xs.map normalizar) = Σ_{x ∈ xs} (1 + cSize (normalizar x))` (por inducción en la lista).
- Por IH: `cSize (normalizar x) ≤ cSize x` para `x ∈ xs`.
- Luego `cSizeList (xs.map normalizar) ≤ cSizeList xs`.
- `reducirDuplicados` solo puede quitar elementos: `cSizeList (reducirDuplicados l) ≤ cSizeList l`.
- `ordenarLista` también puede quitar duplicados (vía `insertarOrdenado` cuando `esIgual x y`):
  `cSizeList (ordenarLista l) ≤ cSizeList l`.
- En total: `cSize (normalizar (mk xs)) ≤ 1 + cSizeList xs = cSize (mk xs)`. ✓

**Nota**: para los lemas sobre `cSizeList`, se necesitan:
```lean
lemma cSizeList_reducirDuplicados_le (l : List CList) : cSizeList (reducirDuplicados l) ≤ cSizeList l
lemma cSizeList_ordenarLista_le (l : List CList) : cSizeList (ordenarLista l) ≤ cSizeList l
lemma cSizeList_map_normalizar (xs : List CList) :
    cSizeList (xs.map normalizar) = Σ_{...}  -- expresión concreta usando List.sum
```

---

### Pieza 4: Propiedades de `esMenor`

Son necesarias para los lemas L1 y L2.

#### P1: Irreflexividad
```lean
theorem esMenor_irrefl (A : CList) : esMenor A A = false
```
Prueba: Por la definición, `cSize A = cSize A`, así que caemos en el caso estructural.
El caso `mk [] vs mk []` retorna `false`. El caso recursivo usa `esIgual x x = true` (por `esIgual_refl`),
así que `esMenor (mk xs) (mk ys)` cuando `xs = ys` siempre devuelve `false` (por IH).

#### P2: Asimetría
```lean
theorem esMenor_asymm (A B : CList) : esMenor A B = true → esMenor B A = false
```
Prueba: Por definición de `esMenor`. Si `cSize A < cSize B`, entonces `cSize B > cSize A` y retorna `false`. ✓
Si `cSize A = cSize B`, la prueba es más delicada (caso recursivo), requiere inducción.

#### P3: Totalidad
```lean
theorem esMenor_total (A B : CList) : esIgual A B = false → esMenor A B = true ∨ esMenor B A = true
```
Prueba: Si `cSize A ≠ cSize B`, un caso trivialmente es `true`. Si `cSize A = cSize B`, hay que hacer
inducción estructural. Cuidado: el caso `mk (x::xs) vs mk (y::ys)` divide por `esIgual x y`, que puede
ser true o false. Si es false, vemos si `esMenor x y` o `esMenor y x`. Por IH de `esMenor` para elementos
menores, la totalidad es recursiva.

**Esta es la propiedad más difícil de formalizar** porque `esMenor` está definido por una recursión
bien fundada, no estructural. Posiblemente requiera un lema `termination_by` propio.

---

### Pieza 5: Unicidad de listas ordenadas sin duplicados

```lean
theorem sorted_nodup_setequiv_eq (l₁ l₂ : List CList)
    (hs1 : Sorted l₁) (hs2 : Sorted l₂)
    (hn1 : Nodup l₁) (hn2 : Nodup l₂)
    (h : SetEquiv l₁ l₂) : l₁ = l₂
```

Con la idempotencia de `normalizar` establecida Y la hipótesis de que los elementos son
**todos normalized** (i.e., outputs de `normalizar`), la demostración procede así:

- Por `SetEquiv`: para cada `x ∈ l₁` existe `y ∈ l₂` con `esIgual x y = true`.
- Como `x, y` son elementos normalizados (en contexto del lema principal), la IH del teorema principal
  da `normalizar x = normalizar y`. Por idempotencia `x = y`.
- Así `l₁` y `l₂` son el mismo conjunto finito de elementos **propositional mente**.
- Con `Sorted` y `Nodup`, son la misma lista.

La demostración formal sería por inducción en `l₁`:
- Si `l₁ = []`: `SetEquiv [] l₂ → l₂ = []`.
- Si `l₁ = x :: xs`: el primer elemento `x` es el mínimo (pues `Sorted l₁`). Por `SetEquiv`,
  `x` aparece en `l₂`; sea `y ∈ l₂` con `x = y` (prop. igual, por el argumento de arriba).
  Como `l₂` está ordenada, `y` debe ser su primer elemento. Luego `l₁` y `l₂` tienen el mismo primer
  elemento. Aplicar IH a las colas.

Para probar "el primer elemento de `l₂` debe ser `y`": si `y` no es el primero (digamos que
`z` es el primero de `l₂` con `esMenor z y`), entonces `z ∈ l₂` está en `l₁` por `SetEquiv`,
pero `z < x` en `l₁` (ordenado), contradiciendo que `x` es el primero de `l₁`. Esto usa
transitivity + totality de `esMenor`.

**NOTA**: Este argumento usa propiedades de `esMenor` (transitivity, totality). Si el "contexto normalizado"
permite usar igualdad proposicional como `esMenor`, la prueba se simplifica: básicamente es que
listas distintas propositional-mente y ordenadas por la misma función total determinista son distintas.

---

## Plan de implementación (orden de ataque)

```
1. normalizar_cSize_le                    (Pieza 3)
   └── cSizeList_reducirDuplicados_le
   └── cSizeList_ordenarLista_le

2. esMenor_irrefl                         (Pieza 4 / P1)

3. esMenor_total                          (Pieza 4 / P3)  ← más difícil

4. ordenarLista_sorted                    (Pieza 2 / L2)  ← necesita P3

5. ordenarLista_nodup                     (Pieza 2 / L1)

6. reducirDuplicados_id_of_nodup          (Pieza 2 / L3)

7. ordenarLista_id_of_sorted_nodup        (Pieza 2 / L4)

8. normalizar_idem                        (Pieza 1)       ← necesita 5,6,7

9. Prueba del sorry en normalizar_eq_of_eq:
   - Usar idempotencia (8) + IH para probar
     esIgual na nb → na = nb  para na ∈ l₁, nb ∈ l₂
   - Usar esta igualdad proposicional + sorted_nodup_setequiv_eq
     o demostrar directamente la permutación y determinismo de ordenarLista
```

---

## Problema de la medida de terminación en `normalizar_eq_of_eq`

El teorema usa `termination_by cSize A + cSize B`. Esto causa un problema potencial:

Para aplicar la IH de idempotencia dentro del caso inductivo de `normalizar_eq_of_eq`, necesitamos
aplicar `normalizar_eq_of_eq` a `(normalizar a, normalizar b)` donde `a ∈ Ax, b ∈ Bx`. Para eso:

- `cSize (normalizar a) ≤ cSize a < cSize A`  (por `normalizar_cSize_le` y por `a ∈ Ax`)
- `cSize (normalizar b) ≤ cSize b < cSize B`  (por `normalizar_cSize_le` y por `b ∈ Bx`)
- **Luego**: `cSize (normalizar a) + cSize (normalizar b) < cSize A + cSize B`. ✓

Esto **funciona** con la medida actual `cSize A + cSize B`.

Para la idempotencia de `normalizar` se usará `cSize A` (un solo argumento) como medida.

---

## Ruta alternativa más corta (si el orden total es difícil)

Si los lemas de `esMenor` resultan muy difíciles de formalizar, hay una **ruta alternativa** que evita
la unicidad de listas ordenadas:

### Idea: Probar `List.Perm l₁ l₂` (permutación proposicional) para luego usar `ordenarLista` determinista

Con idempotencia establecida, sabemos que los elementos de `l₁` y `l₂` son el mismo conjunto proposicional.
Con `Nodup` (proposicional, ya que `esIgual = eq` para normalizados), son el mismo multiconjunto.
Luego `List.Perm l₁ l₂` se puede intentar construir directamente.

Y para `List.Perm l₁ l₂ → ordenarLista l₁ = ordenarLista l₂`:
- Probar por inducción en la permutación (intercambio de adyacentes, etc.).
- O usar: `ordenarLista l₁ = ordenarLista l₂ ↔ List.Perm (ordenarLista l₁) (ordenarLista l₂)`
  (ya que ambos son sorted nodup, son iguales iff permutación).

Esta ruta también requiere cierto trabajo pero puede ser más modular.

---

## Resumen: lo que bloquea el `sorry`

El sorry en `normalizar_eq_of_eq` se resuelve con esta cadena:

```
esIgual A B  →  normalizar A = normalizar B

Prueba:
  normalizar A = mk (ordenarLista (reducirDuplicados (Ax.map normalizar)))
  normalizar B = mk (ordenarLista (reducirDuplicados (Bx.map normalizar)))

  Necesitamos: ordenarLista l₁ = ordenarLista l₂
    donde l₁ ≈ l₂ (SetEquiv) y Nodup l₁, Nodup l₂

  Paso clave: elementos de l₁ y l₂ son normalizados →
    esIgual na nb = true → na = nb (proposicional)     [requiere idempotencia]

  Con eso: l₁ y l₂ son permutaciones del mismo conjunto proposicional

  Con sorted + nodup: listas iguales                   [requiere esMenor total + transitivo]
```

Los dos grandes lemas independientes a demostrar son:
1. **`normalizar_idem`**: `normalizar (normalizar A) = normalizar A`
2. **Totality/transitivity de `esMenor`** (o sortedness + uniqueness de forma más directa)
