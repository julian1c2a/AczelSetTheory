# Plan de demostración: Powerset

## Estado actual del archivo (2026-04-07 00:00)

Build: **⚠️ Pasa con warnings** por 2 sorry.

| Teorema | Estado | Ubicación |
|---|---|---|
| powersetCList_extEq | ⚠️ 1 sorry | Operations/Powerset.lean |
| mem_powerset | ⚠️ 1 sorry | Axioms/Powerset.lean |

El bloqueo es probar que extEq A B → extEq (powersetCList A) (powersetCList B).

---

## Análisis del problema

### La dificultad de Powerset
El conjunto potencia está definido utilizando la función generadora de sublistas List.sublists.
Al comparar dos listas CList que son extensionalmente iguales (xtEq A B = true), necesitamos demostrar que mapear sublists sobre ellas y encapsular los resultados produce listas extensionalmente equivalentes de conjuntos.

### Pieza 1: Lemas sobre CList.sublists
Requeriríamos:
- Lemas de map sobre sublists: CList.sublists_map
- Monotonía: Si todo x ∈ A cumple x ∈ B, entonces toda sublista de A genera correspondencia estricta en las sublistas de B.

### Pieza 2: El axioma base mem_powerset
Una vez probado powersetCList_extEq, aplicaremos el Quotient.sound y el respeto de la igualdad extensional para definir HFSet.powerset.
A partir de ahí, la demostración de mem_powerset (B ∈ powerset A ↔ ∀ x ∈ B, x ∈ A) recaerá sobre el comportamiento constructivo de CList.sublists y su relación con CList.mem.

---

## Plan de implementación (Próxima sesión)

1. Crear infraestructura de List.sublists (lemas que expliquen su comportamiento bajo List.mem).
2. Demostrar monotonías extensionales de CList bajo sublistas.
3. Resolver powersetCList_extEq.
4. Extender a mem_powerset.