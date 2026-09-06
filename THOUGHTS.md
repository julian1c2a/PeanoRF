# Thoughts — PeanoRF

**Última actualización:** 2026-09-06 14:00
**Autor**: Julián Calderón Almendros

> Diario de diseño informal. Ideas, alternativas consideradas, preguntas abiertas.
> **No es normativo** — lo vinculante vive en `DECISIONS.md`. Sirve para que una IA (o
> un yo futuro) entienda el *por qué* de lo que hay.
>
> Este fichero queda fuera del control `check-doc-sync.bash`: sus cifras y símbolos son
> históricos por diseño.

---

## Filosofía de diseño

- **Constructivismo en los dos niveles.** La lógica formalizada es intuicionista y las
  pruebas que la verifican son constructivas. Son dos exigencias, no una.
- **No reconstruir el cimiento.** Tres proyectos hermanos ya tienen la lógica (`FOL`), la
  aritmética de Robinson (`ROBINSON_PlusPlus`) y los naturales (`peanolib`). Este proyecto
  se apoya en ellos; cada línea que los duplique es deuda (ADR-010).
- **No importar frentes abiertos.** Se importan capas concretas, no barrels completos: un
  proyecto hermano trabajando en rojo no debe romper este build (ADR-012).

---

## Ideas y alternativas

### 2026-09-06 — Arranque del proyecto

Se creó desde `lean4-project-template`, pero la plantilla se había quedado atrás respecto
a los proyectos que nacieron de ella. Lo que estaba más al día y se ha traído (y devuelto
a la plantilla):

| De dónde | Qué | Por qué importaba |
|---|---|---|
| ROBINSON_PlusPlus | `check-doc-sync.bash` + AI-GUIDE §27 | Nació de dos fallos reales: un `CURRENT-STATUS` con el banner correcto y una tabla mintiendo tres líneas más abajo; un ADR un mes entero diciendo «no implementado» sobre algo hecho |
| ROBINSON_PlusPlus | `WORKFLOW.md` con el modo IA como flujo principal | La versión anterior presentaba `git-lock.bash` como obligatorio, y en varios repos `locked_files.txt` llevaba vacío desde el primer commit |
| AczelSetTheory | Banner de MANDATORIES obligatorias en `AI-GUIDE.md` | Las reglas vinculantes no son deducibles del código; una guía universal no puede conocerlas, pero sí puede obligar a leerlas |
| AczelSetTheory | MANDATORIES en tabla con columna «Verificación» | Una MANDATORY sin verificación mecánica es una intención, no una regla |
| AczelSetTheory | `update-toolchain.bash` con `--check` y reversión | — |

**Decisión sobre `Prelim.lean`**: la plantilla traía su propio `ExistsUnique` y la
notación `∃!`. Se retiró. Peano ya lo tiene, y dos definiciones idénticas en dos
namespaces son dos constantes que no componen — una trampa ya sufrida en la familia
(ADR-010).

---

### 2026-09-06 (tarde) — La directiva fundacional, y lo que la medición cambió

El autor fijó la directiva: **pureza constructiva e intuicionista**, y `ℕ₀` de peanolib
como natural. Con el matiz decisivo: *«ROB no tiene pureza constructiva en el nivel meta,
pero lo tendrá en no mucho tardar. Lo importante es que sí tiene pureza constructiva a
nivel lenguaje objeto»*.

Ese matiz es lo que obligó a separar **dos ejes** en vez de escribir una sola regla. Y la
separación no es cosmética: los dos ejes se violan por separado. Se puede demostrar
clásicamente en Lean un teorema sobre una lógica intuicionista (viola el eje meta, no el
objeto), y se puede usar eliminación de doble negación *dentro* de la teoría formalizada
con una prueba de Lean impecablemente constructiva (viola el objeto, no el meta).

Antes de escribir la MANDATORY se midió el footprint real (`sondeos/`), y hubo tres
sorpresas, dos buenas y una mala:

* **Buena**: de los 13 `axiom` de FOL, **solo 3 son clásicos**. Es fácil confundirse aquí
  — `raa` *suena* clásico y no lo es (es introducción de ¬), y `gen` es la ω-regla, que es
  infinitaria pero no clásica. Meterlas en el saco de lo prohibido habría amputado el
  proyecto por un malentendido de nomenclatura.
* **Buena**: los tres clásicos **solo se usan desde Completeness/Compacity**. Como esa
  mitad no se importa, M-1 pasa de ser disciplina a ser imposible por construcción.
* **Mala**: `RPP.Minimal.Axioms.axioms` — el conjunto de axiomas de Q⁺⁺ — arrastra
  `Classical.choice`. O sea que **hoy cualquier teorema sobre Q⁺⁺ hereda Classical**. Es
  exactamente la deuda META que el autor dice que va a saldar; entretanto el gate la
  cuenta en cada build en vez de dejarla disolverse.

**La lección cara del día**: el gate, en su primera versión, **no mordía**. Toleraba
`Classical.choice` por nombre de axioma, así que un `Classical.em` escrito por mí pasaba
etiquetado como «deuda heredada de RPP». Lo destapó un smoke test, no una relectura. Es la
misma forma de fallo que el patrón de `check-doc-sync.bash` que no encontraba su frase y
daba verde: **un control no está terminado hasta que se le ha visto fallar** (ADR-015).

### 2026-09-06 (noche) — El alcance, y la trampa que casi se cuela con él

El autor explicó el proyecto: volcar Peano a FOL⁼+ROB++ como espejo, PeanoRF fundacional
y Peano computacional, con vistas a servir de meta-lenguaje. Antes de escribirlo en el
roadmap hubo que medir, y la medición cambió el diseño.

**Lo que apareció**: `Full/Induction.lean:166` postula
`axiom ax_induction : axioms ⊢ inductionFormula φ`. Bajo un `⊢` finitario ese enunciado
es falso — Q no demuestra inducción — y sólo tiene sentido en la lectura ω que el propio
FOL declara. Con **99 de 521 declaraciones de ROB++ (19 %)** pasando por ω-reglas, heredar
`Full/` sin más habría hecho que PeanoRF **no fuera HA sino aritmética verdadera**: el
espejo seguiría funcionando, pero el contenido fundacional se desdibuja y el meta-lenguaje
se vuelve imposible (`⊢` deja de ser r.e.).

Lo interesante es que **no se ve por el nombre**. `raa` suena a lógica clásica y es
introducción de ¬; `gen` es la ω-regla, infinitaria pero intuicionista. Un gate que
mezclara «clásico» con «infinitario» habría prohibido de más por un malentendido de
nomenclatura, y habría amputado el proyecto. De ahí el **tercer eje** separado.

**Y una mina que este proyecto activaría**: `raa`/`imp_intro` tienen premisas META que se
cumplen vacíamente. La soundness que PeanoRF va a construir es justo el ingrediente que
convertiría eso en contradicción. ROB++ se libra porque enuncia Gödel con `Prf` finitaria
y no con `¬(axioms ⊢ ·)` — un detalle de diseño que parece deliberado y que conviene no
deshacer aguas arriba.

**Lo mejor de la jornada**: Peano al completo mide **2193/2207 limpias (99,4 %)**. El
volcado es viable; lo caro no será la pureza, será aritmetizar las estructuras (grupos,
Sylow, `FSet`).

---

## Preguntas abiertas

- [x] ~~¿Qué es exactamente «Peano desde ROB y FOL»?~~ → espejo de Peano en FOL⁼+ROB++,
      núcleo **HA finitaria** (ADR-016), con la inducción **en el conjunto de axiomas**.
- [ ] **¿Hasta dónde llega el volcado?** El núcleo aritmético es directo; grupos, Sylow y
      `FSet` exigen aritmetizar las estructuras. ¿Merece la pena, o el espejo se queda en
      la aritmética y la parte estructural vive sólo en Peano?
- [ ] **¿Qué instancias de inducción hacen falta de verdad?** Con contextos finitos (M-8)
      esto se mide solo: IΔ₀ vs IΣ₁ vs HA completa. Es contenido fundacional gratis.
- [x] ~~¿Pureza constructiva?~~ → **SÍ, en dos ejes** (ADR-013).
- [ ] **¿Política de axiomas propios?** Hoy 0. La regla se escribe antes del primero.
- [ ] **Nivel objeto vs. nivel meta**: ¿qué convención de nombres los distingue a simple
      vista? En ROBINSON_PlusPlus esta frontera ha sido fuente recurrente de trampas
      (una definición que parece la misma en dos namespaces, un orden que resuelve al
      objeto en vez de al meta…). Ahora hay una razón más: **el gate distingue los dos
      ejes, y quien escribe también debería poder hacerlo de un vistazo.**

---

## Lecciones heredadas de los proyectos hermanos

Vienen de la familia, no de este proyecto — pero aplican desde el primer día:

- **El compilador no verifica la prosa.** Un docstring puede prometer generalidad que el
  código ya no tiene. Por eso existe §27.
- **Al contar una familia de símbolos, hay que contarla entera.** Un recuento por un solo
  prefijo dio una cifra falsa que circuló meses por cuatro documentos.
- **Un `axiom` sin ADR puede hacer inconsistente la teoría objeto.** Ocurrió:
  `axioms ⊢ ⊥`. La regla salió de ahí, no de la teoría.
- **Asociatividad y conmutatividad de `+` son AXIOMAS en Q⁺⁺**, no teoremas: no intentar
  probarlas por inducción si se trabaja contra esa capa.
