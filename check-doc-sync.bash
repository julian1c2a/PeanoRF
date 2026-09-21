#!/bin/bash
# check-doc-sync.bash — detecta documentación DESINCRONIZADA del código real.
#
# Versión GENÉRICA de la plantilla: detecta sola la librería del proyecto desde
# `lakefile.lean` y no presupone ninguna estructura de capas. Lo que sí es específico
# de cada proyecto va en el bloque «CONFIGURACIÓN» de abajo — ajústalo al adoptar.
#
# Nace de dos fallos reales, ambos caros (ver AI-GUIDE.md §27):
#
#   1. Los documentos de estado se actualizan por su BANNER y no por su CUERPO.
#      `CURRENT-STATUS-PROJECT.md` llegó a tener un banner correcto y, tres líneas
#      más abajo, una tabla que decía «113 jobs, 99 módulos». Un ADR llevó un mes
#      diciendo «no implementado» sobre algo hecho.
#   2. Se citan como vigentes símbolos que YA NO EXISTEN en el código.
#
# [A1] (línea de cifras canónicas), [C] y [D] son OBJETIVOS y rompen el check. [A2] (cifras
# sueltas en la prosa de cabecera) y [B] (símbolos muertos) son AVISOS que piden juicio: hay
# menciones legítimas de cifras y símbolos que ya no son los vigentes — históricas,
# planificadas, descartadas. ⚠️ Y si el control NO PUEDE MEDIR, es rojo, no verde.
# [E] comprueba que todo módulo del árbol está DENTRO del entorno del gate de pureza:
# uno que no llegue hasta él por imports no se verifica, y el gate no lo dice.
#
# Uso:
#   bash check-doc-sync.bash            # comprobación completa
#   bash check-doc-sync.bash --quick    # sin `lake build`
#   bash check-doc-sync.bash --fix-hint # además, sugiere el sed de cada corrección
#
# Salida: 0 si todo cuadra, 1 si hay desincronización.

set -uo pipefail
cd "$(dirname "$0")"

QUICK=0
HINT=0
for a in "$@"; do
  case "$a" in
    --quick)     QUICK=1 ;;
    --fix-hint)  HINT=1 ;;
    -h|--help)   sed -n '2,24p' "$0"; exit 0 ;;
    *) echo "opción desconocida: $a" >&2; exit 2 ;;
  esac
done

# ═══ CONFIGURACIÓN (ajustar por proyecto) ═══════════════════════════════════
#
# Documentos AUTORITATIVOS: los que describen el ESTADO ACTUAL y por tanto deben
# cuadrar con el código. Quedan fuera, y con razón, los de diario, diseño e historia
# (CHANGELOG, THOUGHTS, PLAN-*, AUDIT-*): sus cifras y símbolos son obsoletos POR
# DISEÑO, y marcarlos convertiría el control en ruido.
AUTHORITATIVE_BASE="REFERENCE.md CURRENT-STATUS-PROJECT.md DEPENDENCIES.md DECISIONS.md README.md NEXT-STEPS.md"

# [B] Prefijos de los símbolos del proyecto que se citan en la prosa entre `backticks`.
# Vacío ⇒ se salta el control [B].
#
# ✅ ACTIVADO el 2026-09-21. Estuvo vacío desde el 2026-09-06 «hasta que existan familias
# propias» — y para entonces ya había quince. Un control desactivado «de momento» es un
# control desactivado.
#
# ⚠️ Lo que [B] caza es la dirección OPUESTA a la que parece: un símbolo **citado en un doc
# autoritativo que no existe en el árbol**. NO caza lo contrario — declarado y sin usar —,
# que es lo que le pasó a la capa `LQ` y por eso va etiquetada a mano en `HA/Domain.lean`.
SYMBOL_PREFIXES='derivesI_|slash|isHarrop|Slash|numeralI_|collapse|grounded|Grounded'
SYMBOL_PREFIXES="$SYMBOL_PREFIXES"'|eqI_|specI|subst|upS|consS|compS|liftS|singleS|fdepth'
SYMBOL_PREFIXES="$SYMBOL_PREFIXES"'|ClosedQTerm|closed_|addI_|succI_|hyps_cons|ctx_weaken'
SYMBOL_PREFIXES="$SYMBOL_PREFIXES"'|consist|notP_syn|notNotP_syn|coreAxioms|zeroS|LQ'
SYMBOL_PREFIXES="$SYMBOL_PREFIXES"'|qDisjunction|qExistence|haDisjunction|disjunction_|existence_'
SYMBOL_PREFIXES="$SYMBOL_PREFIXES"'|ax|Derives|LK|Prf|numeral|liftTerm|liftFormula|inductionFormula'

# Directorios extra de declaraciones VIVAS (fuera de la librería: dependencias locales,
# cuarentenas, sondeos). Separados por espacios; los inexistentes se ignoran.
# Aquí: los árboles de las tres dependencias sibling, para que [B] no marque como
# muerto un símbolo que vive aguas arriba.
EXTRA_DECL_DIRS='../FOL/FOL ../ROBINSON_PlusPlus/ROBINSON_PlusPlus ../Peano/Peano'

# [E] Marcador que el gate de pureza imprime con los módulos que tiene en su entorno.
# Vacío ⇒ se salta el control [E]. Ver PeanoRF/Meta/AxiomCheck.lean.
# ⚠️ Nace de un fallo real (2026-09-17): `Calculus/Consistency` se creó, entró en el build
# y el gate siguió diciendo «OK» sobre los 8 módulos que sí veía. El import a AxiomCheck es
# una LISTA A MANO, y una lista a mano que no se actualiza no da error: da silencio.
GATE_SCOPE_MARKER='[gate · alcance]'
# Módulos que legítimamente NO aparecen en ese alcance: el propio módulo del gate (se está
# elaborando cuando lo imprime) y las plantillas.
GATE_SCOPE_EXEMPT='PeanoRF.Meta.AxiomCheck PeanoRF._template'
# ═══════════════════════════════════════════════════════════════════════════

# ─── 0. DETECCIÓN DEL PROYECTO (misma lógica que gen-root.bash) ─────────────
LIB=$(grep -E 'lean_lib\s+«([^»]+)»' lakefile.lean 2>/dev/null | sed 's/.*«\(.*\)».*/\1/' | head -1)
[ -z "$LIB" ] && LIB=$(grep -E '^lean_lib\s+"([^"]+)"' lakefile.lean 2>/dev/null | sed 's/.*"\(.*\)".*/\1/' | head -1)
[ -z "$LIB" ] && LIB=$(grep -E 'package\s+«([^»]+)»' lakefile.lean 2>/dev/null | sed 's/.*«\(.*\)».*/\1/' | head -1)
[ -z "$LIB" ] && LIB=$(grep -E '^package\s+"([^"]+)"' lakefile.lean 2>/dev/null | sed 's/.*"\(.*\)".*/\1/' | head -1)
if [ -z "$LIB" ] || [ ! -d "$LIB" ]; then
  echo "❌ No se pudo detectar el directorio de la librería desde lakefile.lean." >&2
  exit 2
fi

# ─── 1. VERDAD DEL CÓDIGO ────────────────────────────────────────────────────
MODULES=$(find "$LIB" -name '*.lean' ! -name '_template.lean' 2>/dev/null | wc -l)
# ⚠️ Se excluyen las menciones entre BACKTICKS (`sorry` en prosa y docstrings) además
# de las líneas de comentario: contarlas daba 1 donde había 0 y rompía el check [A].
SORRY=$(grep -rE '(^|[^a-zA-Z_`])sorry([^a-zA-Z_`]|$)' "$LIB" --include=*.lean 2>/dev/null \
        | grep -vE '^[^:]*:\s*(--|/-|-/|\*)' | wc -l)
AXIOMS=$(grep -rhE '^axiom ' "$LIB" --include=*.lean 2>/dev/null | wc -l)

BUILDLOG=$(mktemp)
if [ "$QUICK" = "1" ]; then
  JOBS=""
  : > "$BUILDLOG"
else
  # ⚠️ La salida del build se GUARDA, no se tira: de ella salen dos cosas, la cifra de
  # `jobs` y el ALCANCE que publica el gate (control [E]).
  lake build > "$BUILDLOG" 2>&1 || true
  JOBS=$(grep -oE "Build completed successfully \([0-9]+ jobs\)" "$BUILDLOG" | grep -oE "[0-9]+" || true)
fi

echo "════ VERDAD DEL CÓDIGO ($LIB) ════"
printf "  módulos         : %s\n" "$MODULES"
printf "  sorry           : %s\n" "$SORRY"
printf "  axiom de Lean   : %s\n" "$AXIOMS"
[ -n "$JOBS" ] && printf "  build jobs      : %s\n" "$JOBS"
echo

DOCS="$AUTHORITATIVE_BASE $(ls doc/REFERENCE-*.md 2>/dev/null)"
FAIL=0

# ─── 2. [A] CIFRAS ───────────────────────────────────────────────────────────
# Reescrito el 2026-09-17 tras una auditoría que encontró este control en el PEOR de los
# estados posibles: daba VERDE cuando no podía medir, y ROJO por falsos positivos cuando
# sí podía. Las dos mitades están arregladas por separado.
echo "════ [A] CIFRAS ════"
A_FAIL=0
A_WARN=0

# ── [A0] ¿SE PUEDE MEDIR? ────────────────────────────────────────────────────
# 🔑 El fallo que esto cierra: sin `lake` en el PATH, `JOBS` quedaba VACÍO, el control de
# cifras se SALTABA entero y el script anunciaba «✓ sin cifras obsoletas» con exit 0. Un
# control que no puede medir y da verde es peor que no tenerlo: con ese verde vacuo se
# empujó un commit que tenía este mismo check en rojo. Si no se puede medir, es ROJO.
if [ "$QUICK" = "1" ]; then
  echo "  ⚠️  jobs: NO COMPROBADO (--quick, y eso lo has pedido tú)"
elif [ -z "$JOBS" ]; then
  echo "  ✗ jobs: NO MEDIBLE — ¿está 'lake' en el PATH? (elan: ~/.elan/bin)"
  echo "      Un control que no mide NO es un control verde. Esto es CONTROL VACÍO."
  A_FAIL=1
fi

# ── [A1] LA LÍNEA DE CIFRAS CANÓNICAS (AI-GUIDE §27) — BLOQUEANTE ────────────
# Las cifras se comprueban contra UNA línea de forma fija, no contra la prosa. La prosa
# de un documento de estado habla también del pasado —«el build bajó de 25 a 21 jobs»,
# «las insignias anteriores decían 22 jobs»— y contra eso no hay lista de excluyentes
# que valga: cada salto de línea vuelve a romperla. Medido: 2 falsos positivos, 0
# verdaderos. La convención existe justamente para no tener que adivinar.
CANON_FILE=CURRENT-STATUS-PROJECT.md
CANON_RE='[0-9]+ jobs · [0-9]+ módulos propios · [0-9]+ `?sorry`? vigentes · [0-9]+ `?axiom`? propios'
CANON=$(grep -oE "$CANON_RE" "$CANON_FILE" 2>/dev/null | head -1)
if [ -z "$CANON" ]; then
  echo "  ✗ falta la LÍNEA DE CIFRAS CANÓNICAS en $CANON_FILE (AI-GUIDE §27):"
  echo "        N jobs · N módulos propios · N sorry vigentes · N axiom propios"
  echo "      Sin ella este control no comprueba NADA. CONTROL VACÍO, no verde."
  A_FAIL=1
else
  # shellcheck disable=SC2046
  set -- $(echo "$CANON" | grep -oE '[0-9]+')
  CANON_FAIL=0
  canon_cmp () {   # $1 = lo que dice el doc   $2 = lo real   $3 = etiqueta
    if [ -n "$2" ] && [ "$1" != "$2" ]; then
      echo "  ✗ $3: la línea canónica dice $1, real $2"
      CANON_FAIL=1; A_FAIL=1
    fi
  }
  canon_cmp "${1:-}" "$JOBS"    "jobs"
  canon_cmp "${2:-}" "$MODULES" "módulos propios"
  canon_cmp "${3:-}" "$SORRY"   "sorry vigentes"
  canon_cmp "${4:-}" "$AXIOMS"  "axiom propios"
  [ "$CANON_FAIL" = "0" ] && echo "  ✓ línea canónica al día: $CANON"
fi

# ── [A2] EL RESTO DE LA CABECERA — AVISO, no bloqueante ──────────────────────
# Se sigue mirando la prosa de las primeras 100 líneas de cada doc autoritativo, porque
# ahí han aparecido cifras podridas de verdad. Pero como no sabe distinguir una
# afirmación de un recuerdo, AVISA y no rompe. Más abajo están los registros de logros,
# donde «93 jobs» es historia correcta.
HEADREGION=$(mktemp)
: > "$HEADREGION"
for d in $DOCS; do
  [ -e "$d" ] || continue
  head -100 "$d" | sed "s|^|$d:|" >> "$HEADREGION"
done

# ⚠️ Los patrones se pasan SIEMPRE entre comillas SIMPLES: un backtick dentro de
#    comillas dobles lo ejecuta bash como sustitución de comando y el patrón queda roto.
warn_num () {   # $1 = regex con grupo numérico   $2 = valor correcto   $3 = etiqueta
  local pat="$1" good="$2" label="$3" hits n
  [ -z "$good" ] && return 0
  # Se descartan: menciones históricas, aproximaciones (~40), rangos (40-50) y ejemplos.
  hits=$(grep -nE "$pat" "$HEADREGION" 2>/dev/null \
         | grep -viE "hist[oó]rico|previo|anterior|antes|era |fueron|→|->|en su momento|entonces|ya no|baj[oó]|subi[oó]|20[0-9]{2}-[0-9]{2}-[0-9]{2}|~|p\. ej|ejemplo|umbral|[0-9]+-[0-9]+" || true)
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    n=$(echo "$line" | grep -oE "$pat" | grep -oE "[0-9]+" | head -1)
    if [ -n "$n" ] && [ "$n" != "$good" ]; then
      echo "  ⚠️  $label: dice $n, real $good — ¿afirmación o recuerdo?"
      echo "      ${line:0:150}"
      A_WARN=1
    fi
  done <<< "$hits"
  return 0
}
warn_num '[0-9]+ jobs' "$JOBS" "jobs"
warn_num '[0-9]+ módulos propios' "$MODULES" "módulos propios"
warn_num '[0-9]+ `?sorry`? (vigentes|propios|restantes|reales)' "$SORRY" "sorry"
warn_num '[0-9]+ `?axiom`? propios' "$AXIOMS" "axiom propios"
rm -f "$HEADREGION"
[ "$A_WARN" = "0" ] && echo "  ✓ sin cifras sospechosas en la prosa de cabecera"
[ "$A_FAIL" = "0" ] || FAIL=1

# ─── 3. [B] SÍMBOLOS MUERTOS ─────────────────────────────────────────────────
# Un símbolo está MUERTO si se cita en un doc AUTORITATIVO pero ninguna declaración
# del árbol activo empieza por él.
#
# Dos calibraciones aprendidas al estrenar este control:
#   * Sólo se miran los docs AUTORITATIVOS. Los de diseño e historia citan por diseño
#     cosas que ya no están, y marcarlos sería ruido.
#   * Se compara por PREFIJO, no por igualdad: la prosa abrevia (`ax_C3` por
#     `ax_C3_concat_assoc`), y eso es legítimo. Un símbolo de verdad muerto no
#     prefija nada.
echo
echo "════ [B] SÍMBOLOS MUERTOS — AVISO, requiere juicio ════"
if [ -z "$SYMBOL_PREFIXES" ]; then
  echo "  — desactivado (SYMBOL_PREFIXES vacío en la CONFIGURACIÓN de este script)"
else
  echo "   (no rompe el check: hay menciones legítimas en secciones de diseño e historia.)"
  B_FAIL=0
  # Marcadores que hacen LEGÍTIMA la mención de un símbolo inexistente:
  #   (a) se declara retirado;  (b) es hipotético/propuesto/descartado;  (c) va en una
  #   entrada fechada (histórico por diseño);  (d) es un OBJETIVO declarado.
  DEAD_MARKER='YA NO EXISTE|NO EXISTEN|retirad|RETIRADO|eliminad|borrad|legacy|histórico|ANTERIORES|🗑️|muert|tampoco existe|inexistente|desapareci|ya no son|se borró'
  DEAD_MARKER="$DEAD_MARKER"'|propuest|candidat|hipot[eé]tic|har[ií]a falta|si se |habr[ií]a que|añadir |descartad|no existe|NO EXISTE|sin materializar|20[0-9]{2}-[0-9]{2}-[0-9]{2}'
  DEAD_MARKER="$DEAD_MARKER"'|falta|FALTA|construir|objetivo|medir|sin medir|pendiente|⏳|abiert|necesita|exige|pide|TAREA|hace falta'
  DECLS=$(mktemp)
  # shellcheck disable=SC2086
  grep -rhoE "(theorem|lemma|def|abbrev|axiom|noncomputable def|structure|inductive) +[A-Za-z_][A-Za-z0-9_']*" \
       "$LIB" $EXTRA_DECL_DIRS --include=*.lean 2>/dev/null \
       | awk '{print $NF}' | sort -u > "$DECLS"
  # shellcheck disable=SC2086
  CANDS=$(grep -rhoE '`('"$SYMBOL_PREFIXES"')[A-Za-z0-9_'"'"']+`' $DOCS 2>/dev/null | tr -d '`' | sort -u)
  for sym in $CANDS; do
    grep -qE "^${sym}" "$DECLS" && continue
    # shellcheck disable=SC2086
    bad=$(grep -rn "\`${sym}\`" $DOCS 2>/dev/null | grep -vE "$DEAD_MARKER" || true)
    if [ -n "$bad" ]; then
      echo "  ✗ \`$sym\` no existe en el árbol activo, y se cita sin marcar como retirado:"
      echo "$bad" | head -2 | sed 's/^/      /' | cut -c1-140
      B_FAIL=1
    fi
  done
  rm -f "$DECLS"
  # [B] NO marca FAIL: es un aviso. [A], [C] y [D] sí son objetivos y sí lo marcan.
  # Razón: un control que grita lobo se acaba ignorando, y ése era justo el fallo que
  # este script existe para evitar.
  [ "$B_FAIL" = "0" ] && echo "  ✓ ningún símbolo muerto citado como vigente" \
                      || echo "  ⚠️  revisar los de arriba: ¿es una afirmación de que YA ESTÁ, o una mención histórica/planificada?"
fi

# ─── 4. [C] PROYECCIÓN: ¿está cada módulo en el catálogo? ────────────────────
echo
echo "════ [C] PROYECCIÓN (AI-GUIDE §1/§14) ════"
C_FAIL=0
while IFS= read -r f; do
  [ -e "$f" ] || continue
  m=$(basename "$f" .lean)
  if ! grep -q "$m" REFERENCE.md doc/REFERENCE-*.md 2>/dev/null; then
    echo "  ✗ $m NO aparece en el catálogo REFERENCE.md §1"
    C_FAIL=1
  fi
done < <(find "$LIB" -name '*.lean' ! -name '_template.lean' 2>/dev/null | sort)
[ "$C_FAIL" = "0" ] && echo "  ✓ todo módulo aparece en su catálogo" || FAIL=1

# ─── 5. [D] MARCAS DE TIEMPO (AI-GUIDE §22) ─────────────────────────────────
echo
echo "════ [D] MARCAS DE TIEMPO ════"
D_FAIL=0
# ⚠️ Comprobar que la marca EXISTA no es comprobar que sea CIERTA. El 2026-09-19 este
# control daba verde con SEIS documentos fechados hasta trece días antes de su último
# cambio commiteado — REFERENCE, PLANNING, DECISIONS, AI-GUIDE, CURRENT-STATUS y
# NEXT-STEPS —, incluido un DECISIONS.md que decía 09-06 con cuatro ADR nuevos dentro.
# Un control que mira la FORMA y no el CONTENIDO es un control que da verde sin comprobar.
# 🚨 Y la frescura se lee de `git log`, que MIENTE en un checkout SHALLOW: con un solo
# commit de historia git atribuye CUALQUIER fichero a HEAD, y todo documento cuya marca
# sea anterior al último push da falso positivo. Le pasó a este proyecto el 2026-09-19 —
# la CI se puso en rojo con `DEPENDENCIES.md`, que el commit ni siquiera tocaba. La cura
# es `fetch-depth: 0` en el workflow Y esta guarda: si el repo es shallow, el control NO
# se puede medir, y falta de medida es ROJO (AI-GUIDE §27.1), nunca un salto silencioso.
if [ "$(git rev-parse --is-shallow-repository 2>/dev/null || echo unknown)" != "false" ]; then
  echo "  ✗ NO MEDIBLE: el repositorio es SHALLOW (o no es un repo git)."
  echo "      \`git log\` atribuiría cualquier fichero a HEAD y este control mentiría."
  echo "      Cura: \`fetch-depth: 0\` en el checkout. CONTROL VACÍO, no verde."
  D_FAIL=1
else
  for f in REFERENCE.md doc/REFERENCE-*.md CURRENT-STATUS-PROJECT.md DEPENDENCIES.md \
           PLANNING.md NEXT-STEPS.md DECISIONS.md AI-GUIDE.md; do
    [ -e "$f" ] || continue
    if ! grep -qE '\*\*(Last updated|Última actualización):\*\*' "$f"; then
      echo "  ✗ $f sin marca de tiempo"; D_FAIL=1; continue
    fi
    MARK=$(grep -oE '\*\*(Last updated|Última actualización):\*\* *[0-9]{4}-[0-9]{2}-[0-9]{2}' "$f" \
           | head -1 | grep -oE '[0-9]{4}-[0-9]{2}-[0-9]{2}' || true)
    [ -n "$MARK" ] || continue          # marca sin fecha ISO: no se puede medir
    LAST=$(git log -1 --format=%ad --date=short -- "$f" 2>/dev/null || true)
    [ -n "$LAST" ] || continue          # sin historia todavía
    if [ "$MARK" \< "$LAST" ]; then
      echo "  ✗ $f dice $MARK, pero su último cambio commiteado es $LAST"
      D_FAIL=1
    fi
  done
fi
[ "$D_FAIL" = "0" ] \
  && echo "  ✓ marca de tiempo presente y NO anterior al último cambio" \
  || FAIL=1

# ─── 6. [E] ALCANCE DEL GATE ────────────────────────────────────────────────
# Todo módulo del árbol tiene que estar DENTRO del entorno del gate de pureza. Si no
# llega hasta él por imports, sus declaraciones no se verifican — y el gate no lo dice:
# sigue anunciando «OK» sobre las que sí ve, que es la peor forma de fallar.
echo
echo "════ [E] ALCANCE DEL GATE ════"
if [ -z "$GATE_SCOPE_MARKER" ]; then
  echo "  — desactivado (GATE_SCOPE_MARKER vacío en la CONFIGURACIÓN de este script)"
elif [ "$QUICK" = "1" ]; then
  echo "  ⚠️  NO COMPROBADO (--quick: sin build no hay salida del gate que leer)"
else
  SCOPE=$(sed -n "/$(printf '%s' "$GATE_SCOPE_MARKER" | sed 's/[][\.*^$/]/\\&/g')/,/\[gate\] OK/p" "$BUILDLOG" || true)
  if [ -z "$SCOPE" ]; then
    echo "  ✗ el gate NO publicó su alcance ('$GATE_SCOPE_MARKER' no aparece en el build)."
    echo "      O el gate no corrió, o se le quitó la línea. CONTROL VACÍO, no verde."
    FAIL=1
  else
    E_FAIL=0
    while IFS= read -r f; do
      [ -z "$f" ] && continue
      M=$(echo "${f%.lean}" | sed 's|/|.|g')
      case " $GATE_SCOPE_EXEMPT " in *" $M "*) continue ;; esac
      echo "$SCOPE" | grep -qF "$M" || {
        echo "  ✗ $M está en el árbol pero FUERA del alcance del gate"
        echo "      → añade 'import $M' en PeanoRF/Meta/AxiomCheck.lean"
        E_FAIL=1
      }
    done <<< "$(find "$LIB" -name '*.lean' ! -name '_template.lean' 2>/dev/null | sed 's|^\./||')"
    if [ "$E_FAIL" = "0" ]; then
      N=$(find "$LIB" -name '*.lean' ! -name '_template.lean' 2>/dev/null | wc -l)
      echo "  ✓ los $N módulos del árbol están dentro del alcance del gate"
    else
      FAIL=1
    fi
  fi
fi
rm -f "$BUILDLOG"

# ─── RESUMEN ────────────────────────────────────────────────────────────────
echo
if [ "$FAIL" = "0" ]; then
  echo "✅ DOCUMENTACIÓN SINCRONIZADA."
else
  echo "❌ HAY DESINCRONIZACIÓN — corregir ANTES de commitear."
  if [ "$HINT" = "1" ]; then
    echo
    echo "Sugerencias de sed (revisar antes de aplicar):"
    [ -n "$JOBS" ] && echo "  sed -i -E 's/[0-9]+ jobs/$JOBS jobs/g' *.md doc/*.md"
    echo "  sed -i -E 's/[0-9]+ módulos propios/$MODULES módulos propios/g' *.md doc/*.md"
  fi
  echo
  echo "⚠️  Recordatorio: NO basta con arreglar el banner. Comprobar también el CUERPO"
  echo "    (tablas resumen, §Próximos pasos, notas de auditoría antiguas)."
fi
exit "$FAIL"
