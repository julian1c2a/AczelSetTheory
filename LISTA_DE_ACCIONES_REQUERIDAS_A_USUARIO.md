# Lista de Acciones Requeridas al Usuario — Peano Library

**Fecha de cierre:** 2026-05-21  
**Estado:** ✅ COMPLETADO — No quedan acciones pendientes.

## Resumen de lo resuelto

| Acción | Descripción | Estado |
| ------ | ----------- | ------ |
| 1 | `smallestDivisor_not_dvd_of_lt` público en Peano | ✅ ya existía en rev actual |
| 2 | `smallestDivisor_prime` público en Peano | ✅ ya existía en rev actual |
| 3 | `prime_dvd_mul` público en Peano | ✅ ya existía en rev actual |
| 4 | `smallestDivisor_le_of_prime_dvd` público en Peano | ✅ ya existía en rev actual |
| 5 | `mul_div_of_dvd_left` público en Peano | ✅ ya existía en rev actual |
| 6 | Actualizar `lake-manifest.json` | ✅ no fue necesario (rev `9493fe0` ya tenía todo) |
| 7a | Probar `Omega_prime_mul` sin sorry | ✅ probado en sesión 2026-05-21 |
| 7b | Probar `Omega_prime_mul_prime` sin sorry | ✅ probado en sesión 2026-05-21 |

## Estrategia usada en 7a/7b

Los teoremas 1–5 de Peano resultaron ya presentes en la revisión fijada.
Las pruebas de `Omega_prime_mul_prime` y `Omega_prime_mul` se completaron
directamente en `AczelSetTheory/Integers/PadicVal.lean` usando:

- **`Omega_prime_step`** (privado): `rw [Omega_prime.eq_1, dif_pos hn]`  
  — clave para reescribir `Omega_prime n` solo en el lado izquierdo del goal.
- **`mul_div_cancel_right'`** (privado): `mul m n / n = m` cuando `n ≠ 0`.
- **`div_ne_zero_of_dvd`** (privado): `n/q ≠ 0` cuando `q ∣ n`, `q ≠ 0`, `n ≠ 0`.

## Estado del build

```text
lake build AczelSetTheory.Integers.PadicVal     → ✅ 0 errores, 0 warnings
lake build AczelSetTheory.Integers.MobiusLiouville → ✅ (heredado)
```

`liouville_mul` y `liouville_prime_pow` en `MobiusLiouville.lean` compilan
correctamente al apoyarse en `Omega_prime_mul`.
