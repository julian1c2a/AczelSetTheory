#!/bin/bash
# update-toolchain.bash — Probar y actualizar Lean a una versión (por defecto, la
#                         última estable publicada) verificando la librería completa.
#
# Uso:
#   bash update-toolchain.bash            # consulta la última estable y la prueba
#   bash update-toolchain.bash v4.30.0    # prueba una versión concreta
#   bash update-toolchain.bash --check    # solo informa si hay una versión más nueva
#
# En éxito: commitea el lean-toolchain actualizado.
# En fallo: restaura la versión previa y sale con código 1.
#
# NOTA: verifica `lake build AczelSetTheory` (toda la librería), no solo el
#       ejecutable por defecto. La dependencia `peanolib` se recompila con el
#       nuevo toolchain; si su master no es compatible, el build fallará y se
#       revertirá (peanolib se actualiza por separado en su propio repo).

set -euo pipefail

CURRENT=$(cat lean-toolchain)

# ── Resolver la versión objetivo ────────────────────────────────────────────
CHECK_ONLY=0
if [ "${1:-}" = "--check" ]; then
    CHECK_ONLY=1
    set --   # descartar el flag para caer en la rama de "consulta automática"
fi

if [ $# -ge 1 ]; then
    TARGET="$1"
else
    echo "Consultando la última versión estable de Lean 4 (GitHub releases)..."
    # /releases/latest devuelve la última release NO marcada como prerelease.
    TARGET=$(curl -fsSL https://api.github.com/repos/leanprover/lean4/releases/latest \
        | sed -n 's/.*"tag_name": *"\([^"]*\)".*/\1/p' | head -1)
    if [ -z "$TARGET" ]; then
        echo "❌ No se pudo obtener la última versión (¿sin red o rate-limit de la API?)." >&2
        exit 1
    fi
fi

NEW="leanprover/lean4:$TARGET"

# ── Comparar con la versión actual ──────────────────────────────────────────
if [ "$NEW" = "$CURRENT" ]; then
    echo "✅ Ya estás en la última versión estable ($CURRENT). Nada que hacer."
    exit 0
fi

echo "Actual:   $CURRENT"
echo "Objetivo: $NEW"

if [ "$CHECK_ONLY" -eq 1 ]; then
    echo "ℹ️  Hay una versión más nueva disponible: $TARGET (ejecuta sin --check para probarla)."
    exit 0
fi

# ── Instalar, probar y commitear/revertir ───────────────────────────────────
echo "Instalando toolchain $TARGET..."
elan toolchain install "leanprover/lean4:$TARGET"

echo "$NEW" > lean-toolchain

echo "Compilando la librería completa (lake build AczelSetTheory)..."
if lake build AczelSetTheory; then
    echo ""
    echo "✅ Build OK con $NEW"
    git add lean-toolchain
    git commit -m "chore: actualizar lean toolchain a $TARGET"
    echo "✅ Commit hecho."
    echo "ℹ️  Recuerda: la dependencia peanolib (repo Peano) puede necesitar el"
    echo "    mismo bump de toolchain — actualízala allí y haz 'lake update peanolib'."
else
    echo ""
    echo "❌ Build falló con $NEW. Restaurando $CURRENT."
    echo "$CURRENT" > lean-toolchain
    exit 1
fi
