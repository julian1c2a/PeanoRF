#!/bin/bash
# check-sorry.bash — Find all sorry statements in .lean files
#
# ⚠️ Cuenta `sorry` como TOKEN: excluye `sorryAx`, las menciones entre backticks
#    (`sorry` en prosa y docstrings) y las lineas de comentario. Contarlas daba falsos
#    positivos — un modulo de metaprogramacion que habla de `sorry` no tiene sorries.
#
# Usage:
#   bash check-sorry.bash           # check all .lean files
#   bash check-sorry.bash staged    # check only staged files (for CI)
#   bash check-sorry.bash Module    # check files matching pattern

set -e

MODE="${1:-all}"
TOTAL=0
FILES_WITH_SORRY=0

if [ "$MODE" = "staged" ]; then
    LEAN_FILES=$(git diff --cached --name-only | grep '\.lean$' || true)
elif [ "$MODE" = "all" ]; then
    LEAN_FILES=$(find . -name "*.lean" ! -name "_template.lean" ! -path "./.lake/*" | sort)
else
    LEAN_FILES=$(find . -name "*${MODE}*.lean" ! -path "./.lake/*" | sort)
fi

if [ -z "$LEAN_FILES" ]; then
    echo "No .lean files found."
    exit 0
fi

echo "=== sorry report ==="
while IFS= read -r FILE; do
    [ -z "$FILE" ] && continue
    [ ! -f "$FILE" ] && continue
    COUNT=$(grep -cE '(^|[^a-zA-Z_`])sorry([^a-zA-Z_`]|$)' "$FILE" 2>/dev/null | head -1 || true)
    COUNT="${COUNT//[^0-9]/}"
    COUNT="${COUNT:-0}"
    if [ "$COUNT" -gt 0 ] 2>/dev/null; then
        echo ""
        echo "📄 $FILE ($COUNT sorry)"
        grep -nE '(^|[^a-zA-Z_`])sorry([^a-zA-Z_`]|$)' "$FILE" | sed 's/^/   /'
        TOTAL=$((TOTAL + COUNT))
        FILES_WITH_SORRY=$((FILES_WITH_SORRY + 1))
    fi
done <<< "$LEAN_FILES"

echo ""
if [ "$TOTAL" -eq 0 ]; then
    echo "✅ No sorry found."
else
    echo "⚠️  Total: $TOTAL sorry in $FILES_WITH_SORRY file(s)."
fi

# ============================================================================
# [S2] CENSO DE AGUJEROS DE CONFIANZA — aviso de FOL, 2026-09-23 (PRF-049 §5)
# ============================================================================
#
# ⚠️ El gate `PeanoRF/Meta/AxiomCheck.lean` NO es un detector de `sorry` (lo dice su
#    propio docstring: `sorryAx` está en `allowedAxioms` a proposito). Quien lo detecta es
#    [S1], de arriba. Pero `sorry` no es el unico modo de meter algo que el kernel no ha
#    comprobado, y esos otros NO los miraba nadie:
#
#      native_decide      delega en el compilador: fuera del kernel
#      unsafe             se salta la comprobacion de terminacion y de tipos
#      opaque             declara sin definir
#      @[implemented_by]  sustituye la definicion en tiempo de ejecucion
#      @[extern]          idem, por FFI
#
# 🔑 Se anade con el arbol en CERO, que es cuando un trinquete sirve de algo. Si algun dia
#    hace falta uno legitimo, la via es sancionarlo en una ADR y nombrarlo AQUI — no
#    ablandar el patron.
#
# ⚠️ `partial` NO esta en la lista a proposito: no es un agujero de confianza, solo impide
#    reducir. Meterlo daria rojos que no dicen nada.

HOLES=0
HOLES_FILES=0
HOLE_RE='(^|[^a-zA-Z_`])native_decide([^a-zA-Z_`]|$)|^[[:space:]]*(unsafe|opaque)[[:space:]]|@\[implemented_by|@\[extern'

echo ""
echo "=== censo de agujeros de confianza ==="
while IFS= read -r FILE; do
    [ -z "$FILE" ] && continue
    [ ! -f "$FILE" ] && continue
    HC=$(grep -cE "$HOLE_RE" "$FILE" 2>/dev/null | head -1 || true)
    HC="${HC//[^0-9]/}"
    HC="${HC:-0}"
    if [ "$HC" -gt 0 ] 2>/dev/null; then
        echo ""
        echo "📄 $FILE ($HC agujero(s))"
        grep -nE "$HOLE_RE" "$FILE" | sed 's/^/   /'
        HOLES=$((HOLES + HC))
        HOLES_FILES=$((HOLES_FILES + 1))
    fi
done <<< "$LEAN_FILES"

echo ""
if [ "$HOLES" -eq 0 ]; then
    echo "✅ Sin agujeros de confianza (native_decide / unsafe / opaque / implemented_by / extern)."
else
    echo "⛔ Total: $HOLES agujero(s) de confianza en $HOLES_FILES fichero(s)."
    exit 1
fi

if [ "$TOTAL" -ne 0 ]; then
    exit 1
fi
