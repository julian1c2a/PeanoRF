#!/usr/bin/env bash
# sondeos/check_C_smoke.bash — prueba del control [C] de `check-doc-sync.bash`
#
# 🚨 POR QUÉ EXISTE. Este proyecto tiene medido que **un control no probado puede ser
# vacuo**: `[B]` estuvo apagado quince días con `SYMBOL_PREFIXES` vacío, `[D]` daba verde
# con seis documentos de fecha falsa, y `[C]` —hasta el 2026-09-22— daba verde con dos
# módulos de 62 declaraciones sin proyectar. La regla que salió de ahí:
#
#   **probar el control con un caso POSITIVO y uno NEGATIVO en la misma pasada.**
#
# Probar solo que salta deja sin medir la mitad que importa; probar solo que pasa no mide
# nada. Este script hace las dos, ocho veces, y **restaura** el árbol al terminar.
#
# ⚠️ No va en la CI: cada caso ejecuta `check-doc-sync.bash --quick` entero (~25 s), y la
# CI ya ejecuta el control de verdad. Esto es la EVIDENCIA de que el control no es vacuo,
# y se corre a mano cuando se toca `[C]`.
#
# Uso:  bash sondeos/check_C_smoke.bash
# Sale 0 si el patrón es el esperado (✓ en los positivos, ✗ en los negativos).

set -u
cd "$(dirname "$0")/.." || exit 2

BK=$(mktemp -d)
trap 'cp "$BK/root.md" REFERENCE.md; cp "$BK/ha.md" doc/REFERENCE-HA.md; cp "$BK/calc.md" doc/REFERENCE-Calculus.md; rm -rf "$BK"' EXIT

cp REFERENCE.md            "$BK/root.md"
cp doc/REFERENCE-HA.md     "$BK/ha.md"
cp doc/REFERENCE-Calculus.md "$BK/calc.md"

restore() {
  cp "$BK/root.md" REFERENCE.md
  cp "$BK/ha.md"   doc/REFERENCE-HA.md
  cp "$BK/calc.md" doc/REFERENCE-Calculus.md
}

# Devuelve solo el bloque [C] del control.
runC() { bash check-doc-sync.bash --quick 2>&1 | sed -n '/\[C\] PROY/,/\[D\] MARCAS/p'; }

RC=0
# esperado: "verde" o "rojo"
caso() {
  local titulo=$1 esperado=$2
  echo
  echo "### $titulo"
  local out; out=$(runC)
  echo "$out" | LC_ALL=C grep -E '✗|✓' | sed 's/^/  /'
  if echo "$out" | LC_ALL=C grep -q '✗'; then
    [ "$esperado" = "rojo" ] || { echo "  🚨 ESPERABA VERDE Y SALIÓ ROJO"; RC=1; }
  else
    [ "$esperado" = "verde" ] || { echo "  🚨 ESPERABA ROJO Y SALIÓ VERDE — el control es VACUO aquí"; RC=1; }
  fi
  restore
}

caso "0 · POSITIVO — nada tocado" verde

awk '!/^\| `HA\/Model.lean` \| `PeanoRF.HA`/' REFERENCE.md > "$BK/t" && cp "$BK/t" REFERENCE.md
caso "1 · NEGATIVO — sin FILA en la tabla §1.1" rojo

LC_ALL=C sed -i 's|^## 2.4 `HA/Model.lean`.*|## 2.4 El modelo|' doc/REFERENCE-HA.md
caso "2 · NEGATIVO — sin ENCABEZADO de sección" rojo

LC_ALL=C grep -v '(../PeanoRF/HA/Model.lean)' doc/REFERENCE-HA.md > "$BK/t" && cp "$BK/t" doc/REFERENCE-HA.md
caso "3 · NEGATIVO — sin línea \`**Fichero**\`" rojo

LC_ALL=C sed -i 's|(../PeanoRF/HA/Arith.lean)|(../PeanoRF/HA/Aritmetica.lean)|' doc/REFERENCE-HA.md
caso "4 · NEGATIVO — enlace a un .lean que no existe" rojo

LC_ALL=C sed -i 's|](../REFERENCE.md)|](../NADA.md)|g' doc/REFERENCE-Calculus.md
caso "5 · NEGATIVO — un nodo deja de enlazar al índice raíz" rojo

# ⭐ La regresión que importa: el agujero de la SUBCADENA. Se borra TODO lo de
# `Calculus/Subst.lean` dejando `Calculus/SubstDerives.lean` documentado. El control viejo
# —`grep -q "Subst"`— daba VERDE porque `Subst` casa dentro de `SubstDerives`.
awk '!/^\| `Calculus\/Subst.lean` \|/' REFERENCE.md > "$BK/t" && cp "$BK/t" REFERENCE.md
LC_ALL=C sed -i 's|^## 2.6 `Calculus/Subst.lean`.*|## 2.6 sustitución paralela|' doc/REFERENCE-Calculus.md
LC_ALL=C grep -v '(../PeanoRF/Calculus/Subst.lean)' doc/REFERENCE-Calculus.md > "$BK/t" && cp "$BK/t" doc/REFERENCE-Calculus.md
caso "6 · REGRESIÓN — subcadena: Subst borrado, SubstDerives intacto" rojo

caso "7 · POSITIVO — tras restaurar" verde

echo
if [ "$RC" = "0" ]; then
  echo "✅ [C] NO ES VACUO: verde en los dos positivos y rojo en los seis negativos."
else
  echo "❌ El control no se comporta como se afirma. Ver los 🚨 de arriba."
fi
exit "$RC"
