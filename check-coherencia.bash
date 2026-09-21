#!/bin/bash
# check-coherencia.bash — detecta que los DOCUMENTOS SE CONTRADIGAN ENTRE SÍ.
#
# Nace de un fallo real del 2026-09-18. Los cinco controles de `check-doc-sync.bash` daban
# VERDE mientras:
#
#   · `CURRENT-STATUS-PROJECT.md` se CONTRADECÍA A SÍ MISMO sobre H3ter — un bloque decía
#     «etapa 1 hecha» y veinte líneas más abajo otro decía «falta el lema que cierra H3ter»,
#     afirmación ya medida como falsa;
#   · `PLANNING.md` no tenía a H3ter EN EL ROADMAP, con el hito llevando un día de trabajo.
#
# Aquellos controles miran CIFRAS, CATÁLOGO, MARCAS DE TIEMPO y ALCANCE. Ninguno mira si dos
# afirmaciones se contradicen, y por eso esto hace falta aparte.
#
# ⚠️⚠️ LO QUE ESTE SCRIPT NO PUEDE COMPROBAR, Y LO DICE EN SU SALIDA
# Una afirmación puede ser FALSA sin contradecir a ninguna otra — y hoy dos de los cinco
# descuadres eran de ese tipo. Eso lo caza una LECTURA, no un grep. Este control cubre la
# parte mecanizable y **declara explícitamente la que no**, porque un control que calla lo
# que no mira es indistinguible de uno que no mira nada (AI-GUIDE §27.1).
#
# Uso:   bash check-coherencia.bash
# Salida: 0 si [F] cuadra, 1 si no. [G] es AVISO y no rompe.

set -uo pipefail
cd "$(dirname "$0")"

# ═══ CONFIGURACIÓN ══════════════════════════════════════════════════════════
# Dónde vive la tabla de hitos, y cómo se reconoce una fila suya.
ROADMAP_FILE="PLANNING.md"
ROADMAP_ROW='^\| \*\*(H[0-9]+(bis|ter|′)?)\*\* \|'
# El corpus donde un hito puede mencionarse. Los diarios quedan fuera: CHANGELOG cita hitos
# pasados por diseño.
CORPUS="REFERENCE.md CURRENT-STATUS-PROJECT.md DECISIONS.md README.md NEXT-STEPS.md PLANNING.md sondeos/README.md"
# Para [G] se excluye `DECISIONS.md`: un ADR **narra su contexto histórico** por diseño
# («al cerrar H3bis anuncié que quedaba a un lema…»), igual que el CHANGELOG. Calibrado el
# 2026-09-18 en la primera ejecución: de 3 avisos, 2 eran ADRs narrando el pasado y 1 era un
# hallazgo real. Sin esta exclusión el control grita en falso, y un control que grita en
# falso deja de leerse.
CORPUS_G="REFERENCE.md CURRENT-STATUS-PROJECT.md README.md NEXT-STEPS.md sondeos/README.md"
# Patrón de un identificador de hito.
MILESTONE='H[0-9]+(bis|ter|′)?'
# ═══════════════════════════════════════════════════════════════════════════

FAIL=0

# ─── [F] REGISTRO DE HITOS — BLOQUEANTE ─────────────────────────────────────
# Todo hito mencionado en el corpus tiene que tener FILA en el roadmap. Es el control [C]
# (todo módulo en su catálogo) aplicado a los hitos, y es el que habría cazado que H3ter no
# estuviera en PLANNING.
echo "════ [F] REGISTRO DE HITOS ════"
if [ ! -e "$ROADMAP_FILE" ]; then
  echo "  ✗ no existe $ROADMAP_FILE — no hay roadmap contra el que comparar. CONTROL VACÍO."
  FAIL=1
else
  REGISTERED=$(grep -oE "$ROADMAP_ROW" "$ROADMAP_FILE" 2>/dev/null \
               | grep -oE "$MILESTONE" | sort -u)
  # shellcheck disable=SC2086
  MENTIONED=$(grep -rhoE "\b$MILESTONE\b" $CORPUS 2>/dev/null | sort -u)

  if [ -z "$REGISTERED" ]; then
    echo "  ✗ el roadmap de $ROADMAP_FILE no tiene NINGUNA fila reconocible."
    echo "      ¿cambió el formato de la tabla? CONTROL VACÍO, no verde."
    FAIL=1
  elif [ -z "$MENTIONED" ]; then
    echo "  ⚠️  ningún documento del corpus menciona un hito — control VACÍO."
  else
    F_FAIL=0
    while IFS= read -r h; do
      [ -z "$h" ] && continue
      echo "$REGISTERED" | grep -qx "$h" || {
        echo "  ✗ $h se menciona pero NO está en el roadmap de $ROADMAP_FILE:"
        # shellcheck disable=SC2086
        grep -rnE "\b$h\b" $CORPUS 2>/dev/null | grep -v "^$ROADMAP_FILE:" | head -3 \
          | sed 's/^/      /' | cut -c1-140
        F_FAIL=1
      }
    done <<< "$MENTIONED"
    if [ "$F_FAIL" = "0" ]; then
      N=$(echo "$REGISTERED" | wc -l)
      echo "  ✓ los $N hitos mencionados tienen fila en el roadmap"
    else
      FAIL=1
    fi
  fi
fi

# ─── [G] ESTADO CONTRA PROSA — AVISO, requiere juicio ───────────────────────
# Un hito marcado ✅ del que la prosa dice «falta»/«pendiente», o uno NO cerrado del que la
# prosa dice «cerrado»/«conseguido». Es el patrón exacto del descuadre del 2026-09-18.
# ⚠️ AVISO y no error: hay menciones legítimas («falta X, que es de H4»).
echo
echo "════ [G] ESTADO CONTRA PROSA — AVISO, requiere juicio ════"
PEND='falta|faltan|pendiente|queda|quedan|por (hacer|cerrar|empezar)|sin (hacer|cerrar)|abiert'
DONE='cerrad|conseguid|hecho|completad|terminad|🏁'
G_WARN=0
if [ -n "${REGISTERED:-}" ]; then
  while IFS= read -r h; do
    [ -z "$h" ] && continue
    ROW=$(grep -E "^\| \*\*$h\*\* \|" "$ROADMAP_FILE" 2>/dev/null | head -1)
    [ -z "$ROW" ] && continue
    # shellcheck disable=SC2086
    # 🚨 `LC_ALL=C` por si algún día el roadmap marca con un emoji de 4 bytes: bajo
    # `es_ES.UTF-8` grep falla en SILENCIO con ésos (medido el 2026-09-21). ✅ es de 3 y hoy
    # casa, pero el día que alguien ponga 🏁 este control se invierte sin avisar.
    if echo "$ROW" | LC_ALL=C grep -q '✅'; then
      HITS=$(grep -rnE "\b$h\b" $CORPUS_G 2>/dev/null | grep -iE "$PEND" | grep -viE '~~|anterior|hist|antes de|ya no' || true)
      LABEL="está ✅ en el roadmap pero la prosa habla de pendiente"
    else
      HITS=$(grep -rnE "\b$h\b" $CORPUS_G 2>/dev/null | grep -iE "$DONE" | grep -viE '~~|etapa|parcial|no est|NO |falso' || true)
      LABEL="NO está ✅ en el roadmap pero la prosa lo da por cerrado"
    fi
    if [ -n "$HITS" ]; then
      echo "  ⚠️  $h: $LABEL"
      echo "$HITS" | head -3 | sed 's/^/        /' | cut -c1-150
      G_WARN=1
    fi
  done <<< "$REGISTERED"
fi
[ "$G_WARN" = "0" ] && echo "  ✓ ningún hito con estado y prosa en desacuerdo"

# ─── LO QUE ESTE CONTROL NO MIRA ────────────────────────────────────────────
echo
echo "════ ⚠️  LO QUE ESTE CONTROL NO MIRA ════"
cat <<'NOTA'
  Una afirmación puede ser FALSA sin contradecir a ninguna otra, y eso NO lo caza un grep.
  ARQUETIPOS ya cazados — ejemplos de lo que se le escapa, NO hallazgos vigentes:

    · una medición que contesta bien a una pregunta que resultó demasiado estrecha;
    · una decisión ya tomada que el plan sigue presentando como abierta (2026-09-19: la
      tabla de riesgos de `PLANNING.md` ofrecía `DerivesL` o Craig, resueltos el 09-18);
    · un texto que deja leer que una pieza cierra algo que sólo cierra a medias;
    · un BANNER que se quedó en el hito anterior (2026-09-19: decía «siguiente, H4» con
      tres etapas de H3ter hechas). ⚠️ Ése lo señalaba [G], y se despachó DOS VECES como
      «falso positivo conocido»: lo era el 09-17 y dejó de serlo después.

  ⇒ Tras este script, la PASADA DE LECTURA del comando /armoniza no es opcional.
NOTA

echo
if [ "$FAIL" = "0" ]; then
  echo "✅ COHERENCIA [F] OK — y los avisos de [G] hay que adjudicarlos uno a uno."
else
  echo "❌ HAY INCOHERENCIA — corregir ANTES de commitear."
fi
exit "$FAIL"
