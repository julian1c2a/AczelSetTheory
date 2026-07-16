#!/bin/bash
# gen-audit-matrix.bash — Regenerate AUDIT-MODULE-MATRIX.md from the real module tree
#
# Usage: bash gen-audit-matrix.bash        (o: make audit)
#
# Recorre PROJECT_NAME/ y emite la matriz de auditoria modulo a modulo: lineas y
# conteos de sorry/admit/axiom/noncomputable + marcadores textuales.
#
# Los conteos de sorry/admit/axiom/noncomputable se calculan sobre el fuente DESPOJADO
# de comentarios de linea (`--`) y de bloque (`/- -/`, anidados) — es el contrato que la
# propia matriz declara en su nota. `check-sorry.bash` NO sirve para esto: usa
# `grep -c 'sorry'` crudo (cuenta prosa) y excluye `_template.lean`.
#
# GATE (ADR-022): el frente de `sorry` aceptado esta declarado abajo en SORRY_BASELINE.
# El script FALLA (exit 1) si aparece un `sorry` fuera del frente o por encima de su
# cota, y AVISA si una cota quedo obsoleta (el frente solo puede encoger).
#
# Ver AI-GUIDE.md (9), ADR-020 (gate de axiomas) y ADR-022 (invariante O6).

set -e

# Detect project name from lakefile.lean
# Supports both «Name» and "Name" syntax; prefers lean_lib (correct case) over package
PROJECT_NAME=$(grep -E 'lean_lib\s+«([^»]+)»' lakefile.lean 2>/dev/null | sed 's/.*«\(.*\)».*/\1/' | head -1)
if [ -z "$PROJECT_NAME" ]; then
    PROJECT_NAME=$(grep -E '^lean_lib\s+"([^"]+)"' lakefile.lean 2>/dev/null | sed 's/.*"\(.*\)".*/\1/' | head -1)
fi
if [ -z "$PROJECT_NAME" ]; then
    PROJECT_NAME=$(grep -E 'package\s+«([^»]+)»' lakefile.lean 2>/dev/null | sed 's/.*«\(.*\)».*/\1/' | head -1)
fi
if [ -z "$PROJECT_NAME" ]; then
    PROJECT_NAME=$(grep -E '^package\s+"([^"]+)"' lakefile.lean 2>/dev/null | sed 's/.*"\(.*\)".*/\1/' | head -1)
fi
if [ -z "$PROJECT_NAME" ]; then
    echo "Error: Could not detect project name from lakefile.lean"
    exit 1
fi

MODULE_DIR="${PROJECT_NAME}"
OUT="AUDIT-MODULE-MATRIX.md"

# ─────────────────────────────────────────────────────────────────
# DEUDA ACEPTADA — frente activo Rationals/Reals (ADR-022).
# Semantica: actual <= cota  => OK · actual > cota o fichero no listado => FAIL.
# El frente SOLO puede encoger: al cerrar un sorry, bajar el numero aqui.
# ─────────────────────────────────────────────────────────────────
declare -A SORRY_BASELINE=(
  ["${MODULE_DIR}/Rationals/Series.lean"]=6
  ["${MODULE_DIR}/Rationals/Polynomial.lean"]=4
  ["${MODULE_DIR}/Reals/Incompleteness.lean"]=3
  ["${MODULE_DIR}/Rationals/Irrational.lean"]=1
)

# ─────────────────────────────────────────────────────────────────
# Despojador de comentarios: escaner char-a-char con estado persistente
# entre lineas (maneja bloques /- -/ ANIDADOS y multilinea, doc-comments
# /-- -/, `--` a media linea, y literales de cadena "…" con escapes).
# ─────────────────────────────────────────────────────────────────
STRIP_PROG='
BEGIN { depth = 0; inStr = 0 }
{
  line = $0; out = ""; i = 1; n = length(line)
  while (i <= n) {
    c2 = substr(line, i, 2); c1 = substr(line, i, 1)
    if (depth > 0) {
      if (c2 == "/-") { depth++; i += 2; continue }
      if (c2 == "-/") { depth--; i += 2; continue }
      i++; continue
    }
    if (inStr) {
      if (c1 == "\\") { i += 2; continue }
      if (c1 == "\"") { inStr = 0; i++; continue }
      i++; continue
    }
    if (c2 == "/-") { depth++; i += 2; continue }
    if (c2 == "--") { break }
    if (c1 == "\"") { inStr = 1; i++; continue }
    out = out c1; i++
  }
  print out
}'

TOTAL_FILES=0
TOTAL_LINES=0
TOTAL_SORRY=0
TOTAL_ADMIT=0
TOTAL_AXIOM=0
TOTAL_NONCOMP=0
MOD_TODO=0
MOD_STUB=0
ROWS=""
VIOLATIONS=""
STALE=""

# LC_ALL=C sort reproduce el orden historico de la matriz ('.'<'\\'<'_')
while IFS= read -r FILE; do
    TOTAL_FILES=$((TOTAL_FILES + 1))

    LINES=$(wc -l < "$FILE" | tr -d ' ')
    STRIPPED=$(awk "$STRIP_PROG" "$FILE")

    N_SORRY=$(printf '%s' "$STRIPPED" | grep -o '\bsorry\b' | wc -l | tr -d ' ')
    N_ADMIT=$(printf '%s' "$STRIPPED" | grep -o '\badmit\b' | wc -l | tr -d ' ')
    N_AXIOM=$(printf '%s' "$STRIPPED" | grep -oE '(^|[^A-Za-z_.])axiom[[:space:]]' | wc -l | tr -d ' ')
    N_NONCOMP=$(printf '%s' "$STRIPPED" | grep -o '\bnoncomputable\b' | wc -l | tr -d ' ')

    # Marcadores textuales: viven en comentarios -> se cuentan sobre el fuente CRUDO.
    # -w es obligatorio: sin el, "TODOS" en prosa da falso positivo.
    N_TODO=$(grep -cwE 'TODO|FIXME|PENDIENTE' "$FILE" 2>/dev/null || true)
    N_STUB=$(grep -ciwE 'placeholder|stub' "$FILE" 2>/dev/null || true)
    [ "$N_TODO" -gt 0 ] && MOD_TODO=$((MOD_TODO + 1))
    [ "$N_STUB" -gt 0 ] && MOD_STUB=$((MOD_STUB + 1))

    # Subsistema: primer componente de directorio; si es top-level, el propio fichero
    REL="${FILE#${MODULE_DIR}/}"
    if [[ "$REL" == */* ]]; then SUB="${REL%%/*}"; else SUB="$REL"; fi

    # Estado + gate
    STATE="OK"
    if [ "$N_AXIOM" -gt 0 ] || [ "$N_ADMIT" -gt 0 ] || [ "$N_NONCOMP" -gt 0 ]; then
        STATE="VIOLA O6"
        VIOLATIONS="${VIOLATIONS}  - ${FILE}: axiom=${N_AXIOM} admit=${N_ADMIT} noncomputable=${N_NONCOMP}"$'\n'
    elif [ "$N_SORRY" -gt 0 ]; then
        CAP="${SORRY_BASELINE[$FILE]:-0}"
        if [ "$N_SORRY" -gt "$CAP" ]; then
            STATE="SORRY:${N_SORRY} (REGRESION)"
            VIOLATIONS="${VIOLATIONS}  - ${FILE}: ${N_SORRY} sorry (cota declarada: ${CAP})"$'\n'
        else
            STATE="SORRY:${N_SORRY} (frente activo)"
        fi
    fi
    # Aviso: cota obsoleta (el frente encogio y nadie bajo el numero)
    if [ -n "${SORRY_BASELINE[$FILE]+x}" ] && [ "$N_SORRY" -lt "${SORRY_BASELINE[$FILE]}" ]; then
        STALE="${STALE}  - ${FILE}: ${N_SORRY} < cota ${SORRY_BASELINE[$FILE]} — bajar la cota en SORRY_BASELINE"$'\n'
    fi

    WINPATH=$(printf '%s' "$FILE" | tr '/' '\\')
    ROWS="${ROWS}| ${WINPATH} | ${SUB} | ${LINES} | ${N_SORRY} | ${N_ADMIT} | ${N_AXIOM} | ${N_NONCOMP} | ${N_TODO} | ${N_STUB} | ${STATE} |"$'\n'

    TOTAL_LINES=$((TOTAL_LINES + LINES))
    TOTAL_SORRY=$((TOTAL_SORRY + N_SORRY))
    TOTAL_ADMIT=$((TOTAL_ADMIT + N_ADMIT))
    TOTAL_AXIOM=$((TOTAL_AXIOM + N_AXIOM))
    TOTAL_NONCOMP=$((TOTAL_NONCOMP + N_NONCOMP))
done < <(find "$MODULE_DIR" -name "*.lean" | LC_ALL=C sort)

# Unlock output if locked
WAS_LOCKED=false
if grep -Fxq "$OUT" locked_files.txt 2>/dev/null; then
    WAS_LOCKED=true
    bash git-lock.bash unlock "$OUT"
fi

{
    echo "# Matriz de Auditoria Modulo por Modulo"
    echo ""
    echo "Generado: $(date +%F) por \`gen-audit-matrix.bash\` (\`make audit\`)"
    echo ""
    echo "## Resumen Global"
    echo ""
    echo "- Archivos Lean: ${TOTAL_FILES}"
    echo "- Lineas totales: ${TOTAL_LINES}"
    if [ "$TOTAL_SORRY" -gt 0 ]; then
        echo "- sorry: ${TOTAL_SORRY}  (deuda aceptada del frente activo Rationals/Reals — ver ADR-022)"
    else
        echo "- sorry: 0"
    fi
    echo "- admit: ${TOTAL_ADMIT}"
    echo "- axiom: ${TOTAL_AXIOM}"
    echo "- noncomputable def: ${TOTAL_NONCOMP}"
    echo "- Modulos con TODO/FIXME/PENDIENTE: ${MOD_TODO}"
    echo "- Modulos con placeholder/stub: ${MOD_STUB}"
    echo ""
    echo "> Nota: los conteos de sorry/admit/axiom/noncomputable se calculan tras"
    echo "> despojar comentarios de linea (\`--\`) y de bloque (\`/- -/\`, anidados); las menciones"
    echo "> de esas palabras en prosa/comentarios no se contabilizan."
    echo ">"
    echo "> Los \`sorry\` estan acotados y declarados en \`SORRY_BASELINE\` (gen-audit-matrix.bash);"
    echo "> \`make audit\` FALLA si aparece uno fuera del frente o por encima de su cota (ADR-022)."
    echo "> El invariante duro 0 axiom / 0 admit / 0 noncomputable (O6a) no admite excepciones."
    echo ""
    echo "## Matriz"
    echo ""
    echo "| Modulo | Subsistema | Lineas | sorry | admit | axiom | noncomputable def | TODO/FIXME/PEND | placeholder/stub | Estado |"
    echo "|---|---|---:|---:|---:|---:|---:|---:|---:|---|"
    printf '%s' "$ROWS"
} > "$OUT"

if [ "$WAS_LOCKED" = true ]; then
    bash git-lock.bash lock "$OUT"
fi

# Report
if [ -n "$STALE" ]; then
    echo "⚠️  Cotas de SORRY_BASELINE obsoletas (el frente encogio):"
    printf '%s' "$STALE"
fi

if [ -n "$VIOLATIONS" ]; then
    echo "❌ $OUT generada, pero el gate FALLA (ADR-022):"
    printf '%s' "$VIOLATIONS"
    exit 1
fi

echo "✅ Generada $OUT: ${TOTAL_FILES} ficheros / ${TOTAL_LINES} lineas / ${TOTAL_SORRY} sorry (todos dentro del frente declarado)"
echo "   axiom: ${TOTAL_AXIOM} · admit: ${TOTAL_ADMIT} · noncomputable: ${TOTAL_NONCOMP} · TODO: ${MOD_TODO} · stub: ${MOD_STUB}"
