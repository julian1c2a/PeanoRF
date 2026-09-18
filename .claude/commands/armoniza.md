---
description: Comprueba que los documentos no se contradigan ENTRE SÍ, y deja el repositorio coherente
---

Deja la documentación **coherente consigo misma**, no sólo cuadrada con el código. Delega en
dos scripts y termina con una pasada de lectura que **no es opcional**.

## Por qué existe, aparte de `/docsync`

`/docsync` comprueba que los documentos cuadren con el **código**: cifras, catálogo de
módulos, marcas de tiempo, alcance del gate. El 2026-09-18 sus cinco controles daban VERDE
mientras:

* `CURRENT-STATUS-PROJECT.md` **se contradecía a sí mismo** sobre H3ter — un bloque decía
  «etapa 1 hecha» y veinte líneas más abajo otro decía «falta el lema que cierra H3ter»,
  afirmación ya medida como falsa esa misma tarde;
* `PLANNING.md` **no tenía el hito en el roadmap**, con un día entero de trabajo hecho;
* `NEXT-STEPS.md` conservaba, del plan del 6 de septiembre, una sección «H3 ❌ Pendiente»
  cuyo plan incluía «soundness por inducción sobre los constructores de `Derives`» — que
  **ADR-017 declaró imposible**. Doce días de deriva.

Ningún control lo veía porque **ninguno mira si dos afirmaciones se contradicen**.

## Qué hacer

1. **`bash check-doc-sync.bash`** y dejarlo en verde ([A1], [C], [D], [E] rompen; [A2] y [B]
   son avisos que piden juicio). Si no está en verde, arreglarlo **antes** de seguir: no
   tiene sentido armonizar afirmaciones sobre cifras que mienten.

2. **`bash check-coherencia.bash`**.
   * **[F] REGISTRO DE HITOS** rompe: todo hito mencionado tiene que tener fila en el
     roadmap de `PLANNING.md`. Es el control [C] aplicado a los hitos.
   * **[G] ESTADO CONTRA PROSA** es aviso: un hito ✅ del que la prosa dice «falta», o uno
     no cerrado que la prosa da por hecho. **Adjudicar cada uno**: la co-ocurrencia en una
     misma línea produce falsos positivos legítimos («H3bis cerrado; siguiente, H4»).

3. ⚠️ **LA PASADA DE LECTURA.** Lo que ningún script caza: **una afirmación puede ser falsa
   sin contradecir a ninguna otra.** Leer, con estas preguntas, los documentos
   autoritativos y `sondeos/README.md`:

   | pregunta | arquetipo real (2026-09-18) |
   |---|---|
   | ¿el **banner** dice lo mismo que el cuerpo? | «teoría propia por empezar» veinte líneas encima de un hito conseguido |
   | ¿hay una **sección entera** del plan original sin tocar? | «H3 ❌ Pendiente» con un plan que un ADR había declarado imposible |
   | ¿alguna **medición** contesta a una pregunta que quedó estrecha? | «H3ter es viable por el port» — cierto, y la pregunta era otra |
   | ¿se presenta como **abierta** una decisión ya tomada? | la elección de diseño de la etapa 2 |
   | ¿algún texto deja **leer de más**? | una pieza que cierra *una* de dos, redactada como si cerrara las dos |

4. **Informar en el chat distinguiendo hallazgos reales de ruido descartado**, y decir
   explícitamente qué quedó sin comprobar.

## La regla que gobierna esto

Un control que **calla lo que no mira** es indistinguible de uno que no mira nada
(AI-GUIDE §27.1). Por eso `check-coherencia.bash` imprime, siempre, la lista de lo que se le
escapa — y por eso el paso 3 va en el comando y no en la buena voluntad de quien lo ejecuta.

⚠️ Y al corregir, la regla de oro de §27 sigue mandando: **no basta con arreglar el banner.**
