> **ARCHIVADO — 2026-04-27**
> Todo el contenido de este plan fue implementado y cerrado en `Sylow.lean` (sesiones 2026-04-20–23).
> `cauchy_minimal` está demostrado sin sorry. `mckay_orbit_count`, `mckay_orbit_remove`, infraestructura McKay — todos cerrados.
> Este archivo se conserva como registro histórico del razonamiento que llevó a la implementación.

---

# Plan detallado y comentado: cierre de Cauchy por McKay

## Objetivo

Cerrar la última pieza pendiente en la formalización de Cauchy minimal:

- eliminar el `sorry` de la etapa McKay,
- probar formalmente la divisibilidad
  - `p ∣ |{ g : G | g^p = e }|`,
- y usarlo para concluir existencia de elemento de orden `p`.

Este plan está pensado para el archivo principal de Sylow/Cauchy y para el estado actual del repo (infraestructura de acción de grupos, órbitas, estabilizadores y conteo ya disponible).

## Estado actual resumido

- La infraestructura auxiliar (acciones, órbitas, estabilizadores, cosets, cardinalidades) ya compila.
- El proyecto compila sin errores fatales, pero aún queda el paso McKay como hueco lógico final en la cadena de Cauchy minimal.
- El archivo de trabajo activo es:
  - [Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Sylow.lean](Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Sylow.lean)

## Idea matemática (comentada)

Se usa la acción cíclica sobre p-tuplas de producto identidad:

1. Considerar el conjunto
   - `X := { (x_0, ..., x_{p-1}) : G^p | x_0 * ... * x_{p-1} = e }`.
2. El grupo cíclico `C_p` (o el subgrupo generado por la rotación) actúa por desplazamiento cíclico de coordenadas.
3. Las órbitas tienen tamaño `1` o múltiplo de `p` (por primalidad y estructura del estabilizador en una acción de orden `p`).
4. Los puntos fijos de la rotación son exactamente las tuplas constantes `(g, ..., g)` con `g^p = e`.
5. Contando módulo `p`:
   - `|X| ≡ |Fix| (mod p)`.
6. Como `|X| = |G|^(p-1)` (determinando la última coordenada por las primeras `p-1`), y `p ∣ |G|`, entonces `p ∣ |X|`.
7. Luego `p ∣ |Fix|`, pero `|Fix| = |{ g : G | g^p = e }|`.
8. Separando la identidad, se obtiene un elemento no trivial con `g^p = e`; por minimalidad/argumento previo, su orden es `p`.

## Plan de formalización en Lean (paso a paso)

### Fase 1: fijar tipos y conjuntos finitos

1. Definir (o reutilizar) el tipo de p-tuplas que usa la librería (lista de longitud `p`, función `Fin p -> G`, o estructura local equivalente).
2. Definir el predicado de producto identidad sobre tuplas.
3. Definir el subconjunto finito `X` con ese predicado.

Comentario técnico:

- Conviene escoger la representación de tupla que ya tenga mejor soporte de `FSet`/cardinalidad en el repo para evitar coerciones largas.

### Fase 2: construir la acción cíclica

1. Definir la rotación de tuplas.
2. Probar que preserva el predicado de producto identidad.
3. Instanciar la acción del grupo cíclico (o del generador con iteración) sobre `X`.

Comentario técnico:

- Si ya hay abstracción de `GroupAction` en [Peano/PeanoNat/Combinatorics/GroupTheory/Action.lean](Peano/PeanoNat/Combinatorics/GroupTheory/Action.lean), engancharse a ella para heredar órbitas/estabilizador/orbit-stabilizer.

### Fase 3: aritmética de órbitas módulo p

1. Probar que toda órbita no fija tiene cardinal múltiplo de `p`.
2. Usar partición por órbitas para obtener:
   - `|X| = |Fix| + p * k` para algún `k`.
3. Concluir:
   - `|X| ≡ |Fix| [ZMOD p]`.

Comentario técnico:

- Aquí hay dos estilos posibles:
  - vía ecuación explícita de suma de cardinales de órbitas,
  - o vía lema de congruencia ya existente si está en `Action`.
- Elegir el que minimice nuevas pruebas auxiliares.

### Fase 4: identificar puntos fijos

1. Probar equivalencia:
   - `tuple` fija por rotación `↔` todos los componentes iguales.
2. Probar que, para tupla constante `(g,...,g)`, pertenecer a `X` equivale a `g^p = e`.
3. Construir biyección finita:
   - `Fix ≃ { g : G | g^p = e }`.
4. Concluir igualdad de cardinalidades.

Comentario técnico:

- Esta fase suele ser el corazón del trabajo de reescritura (rotación e índices).
- Es recomendable separar en lemas cortos con nombres estables para reutilizar en futuras pruebas de Sylow.

### Fase 5: cardinalidad de X

1. Probar `|X| = |G|^(p-1)` mediante:
   - elección libre de primeras `p-1` coordenadas,
   - última coordenada determinada para que el producto total sea `e`.
2. Aplicar `p ∣ |G|` para deducir `p ∣ |X|`.

Comentario técnico:

- Si ya existe un lema de conteo equivalente en combinatoria, reutilizarlo para no reabrir prueba de bijectividad.

### Fase 6: cerrar McKay y Cauchy minimal

1. Con congruencia de Fase 3 y divisibilidad de Fase 5, derivar:
   - `p ∣ |Fix|`.
2. Reemplazar `|Fix|` por `|{ g | g^p = e }|` (Fase 4).
3. Obtener lema final McKay:
   - `p ∣ |{ g : G | g^p = e }|`.
4. Integrarlo donde estaba el `sorry`.
5. Cerrar `cauchy_minimal` con el encadenamiento ya existente.

## Estructura sugerida de lemas (nombres orientativos)

- `rotate_preserves_prodEqOne`
- `orbit_card_dvd_p_or_fixed` (o variante)
- `card_X_congr_card_fix_mod_p`
- `fixed_iff_constant`
- `card_fix_eq_card_powEqId`
- `card_X_eq_cardG_pow_pred`
- `mckay_p_dvd_powEqId` (sin `sorry`)

## Criterio de terminado

Se considera cerrado cuando se cumpla todo esto:

- `mckay_p_dvd_powEqId` queda 100% probado (sin `sorry`).
- `cauchy_minimal` queda 100% probado (sin `sorry`).
- Build limpio:
  - `lake build`
- Validación de avisos:
  - sin advertencias de `sorry` en la ruta de Sylow/Cauchy.

## Riesgos y mitigaciones

- Riesgo: fricción por representación de tuplas.
  - Mitigación: elegir desde el inicio la forma que mejor interactúe con `FSet` y cardinalidad en el repo.
- Riesgo: demasiada complejidad en un solo lemma.
  - Mitigación: dividir en lemas miniatura de 10-30 líneas y probarlos incrementalmente.
- Riesgo: congruencias modulares verbosas.
  - Mitigación: encapsular una sola vez la aritmética de órbitas en un lema dedicado y reutilizar.

## Checklist operativo

- [ ] Definir/confirmar `X` y la acción cíclica sobre `X`.
- [ ] Probar descomposición de cardinal de `X` en fijos + múltiplos de `p`.
- [ ] Probar identificación `Fix` con `{g | g^p = e}`.
- [ ] Probar `|X| = |G|^(p-1)`.
- [ ] Deducir divisibilidad `p ∣ |Fix|`.
- [ ] Sustituir `sorry` en `mckay_p_dvd_powEqId`.
- [ ] Ejecutar build completo y verificación de warnings.

---
Documento de planificación creado para ejecutar el cierre final y dejar Cauchy-McKay completamente formalizado.
