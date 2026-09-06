# Decisiones de Diseño — PeanoRF

**Última actualización:** 2026-09-06
**Autor**: Julián Calderón Almendros

Registro de decisiones arquitectónicas (ADR) de este proyecto. Cada entrada documenta
*qué* se decidió y *por qué*, para referencia futura.

> **Este fichero es el lugar de lo específico de ESTE proyecto.** Lo universal
> (aplicable a cualquier proyecto nacido de esta plantilla) vive en `AI-GUIDE.md`. Si
> una regla solo tiene sentido para este proyecto concreto (una directiva fundacional
> como "cero `Classical`", una elección de representación matemática, un mandato sobre
> qué tipo base usar), documéntala aquí — en la sección **MANDATORIES** si es una
> directiva no negociable, o como un ADR normal si es una decisión de diseño reversible.

---

## ⚠️ MANDATORIES (reglas vinculantes de este proyecto — lectura obligatoria)

Estas reglas son **vinculantes**, no preferencias de estilo. Su incumplimiento es un
**defecto de build**. [`AI-GUIDE.md`](AI-GUIDE.md) redirige obligatoriamente aquí antes
de tocar cualquier `.lean`. **Cada regla enlaza a su ADR justificativo y declara cómo se
verifica** — una MANDATORY sin verificación mecánica es una intención, no una regla.

| # | MANDATORY | ADR | Verificación |
|---|---|---|---|
| **M-1** | **La lógica de nivel OBJETO es INTUICIONISTA.** Ninguna declaración propia puede depender de los tres axiomas clásicos de FOL: `MetaRules.dne`, `Theorems.Neg.dne`, `Theorems.Quantifiers.forall_not_impl_exists_not`. **Sin baseline ni excepción**: es la tesis del proyecto. | [ADR-013](#adr-013) | gate `PeanoRF/Meta/AxiomCheck.lean`, **eje objeto** — error de build. Probado con smoke test |
| **M-2** | **Las PRUEBAS EN LEAN son constructivas.** Footprint diana `#print axioms ⊆ {propext, Quot.sound}`. Prohibido `Classical.byContradiction`/`em`/`propDecidable`/`choice`/`choose`, `open Classical` y `native_decide`. Medidas de terminación **lexicográficas**, nunca aritméticas ponderadas. | [ADR-013](#adr-013) | gate, **eje meta** — error de build. La deuda HEREDADA de RPP se tolera con aviso y recuento, y solo si entra por una dependencia (procedencia, no nombre) |
| **M-3** | **`ℕ₀` de peanolib siempre, nunca `Nat`** de Lean salvo kernel estrictamente inevitable (`sizeOf`, literales internos, `omega`), y nunca en enunciados. | [ADR-014](#adr-014) | revisión + `grep -n '\bNat\b'` |
| **M-4** | **No redefinir lo que ya existe aguas arriba** (`ExistsUnique`, `∃!`/`∃¹`, `ℕ₀`, `Term`/`Formula`/`⊢`). Se importa, no se copia. | [ADR-010](#adr-010-no-se-redefine-infraestructura-que-ya-existe-aguas-arriba) | revisión + `grep` de las familias duplicadas |
| **M-5** | **No importar barrels completos** de RPP ni de Peano. Y en particular: **PROHIBIDO importar `FOL.Semantics`, `FOL.Soundness`, `FOL.Completeness`, `FOL.Compacity`** — ahí vive todo lo clásico de FOL. | [ADR-012](#adr-012-se-importan-capas-concretas-no-barrels-completos), [ADR-013](#adr-013) | revisión de `import` + el gate (el uso, no el import, es lo que rompe) |
| **M-6** | **Las cuatro librerías van en el mismo toolchain** (hoy `v4.31.0`). Un bump se hace en las cuatro a la vez, o no se hace. | [ADR-011](#adr-011-las-tres-dependencias-son-rutas-locales-no-from-git) | `cat ../{FOL,ROBINSON_PlusPlus,Peano}/lean-toolchain` |
| **M-7** | **El NÚCLEO es FINITARIO**: `⊢` recursivamente enumerable. Prohibidas las cinco ω-reglas de FOL (`imp_intro`, `gen`, `raa`, `or_elim`, `ex_elim`) y los cuatro meta-axiomas de RPP que postulan `axioms ⊢ φ` para esquemas que Q⁺⁺ no demuestra. Permitidas **sólo** bajo `PeanoRF.Omega.*`. | [ADR-016](#adr-016) | gate, **eje finitario** — error de build fuera de la capa ω; recuento dentro. Probado con smoke test |
| **M-8** | **La inducción entra en el CONJUNTO DE AXIOMAS**, nunca como `axiom : axioms ⊢ inductionFormula φ`. Contextos finitos `axioms ++ [inst₁…instₖ] ⊢ φ`. | [ADR-016](#adr-016) | gate (`ax_induction` está en la lista ω) + revisión |
| **M-9** | **NO demostrar soundness de `Derives` para derivaciones con `raa`/`imp_intro`.** La soundness se prueba **sólo del fragmento finitario**. | [ADR-016](#adr-016) | revisión del enunciado de soundness + M-7 |

> ⏳ **Todavía abierta en parte: la política de axiomas propios.** ADR-016 ya fija lo
> principal — **la inducción NO se postula como `axiom : axioms ⊢ φ`** (M-8), que es
> exactamente la forma que toma aguas arriba. Lo que queda por escribir es la regla para
> un `axiom` de Lean de otra naturaleza. Si este proyecto va a declarar
> algún `axiom` de Lean (por ejemplo, para el esquema de inducción como esquema de nivel
> objeto), la regla de sanción — ADR obligatorio + justificación en un `AXIOMS.md` — se
> escribe **antes del primero**, no después. En ROBINSON_PlusPlus un `axiom` sancionado sin
> ADR llegó a hacer la teoría objeto **inconsistente** (`axioms ⊢ ⊥`). Hoy el proyecto
> tiene **0 `axiom` propios** y esa es la posición de partida.

---

## ADR-001: Sin dependencia de Mathlib

**Fecha**: 2026-09-06
**Estado**: Aceptado

**Decisión**: este proyecto no depende de Mathlib.

**Justificación**: [explicar por qué — objetivo educativo, rendimiento, evitar el
desgaste de la API de Mathlib, etc.]

**Consecuencias**: toda la infraestructura necesaria (`ExistsUnique`, decidibilidad,
etc.) se construye desde cero.

---

## ADR-002: `autoImplicit = false`

**Fecha**: 2026-09-06
**Estado**: Aceptado

**Decisión**: `moreServerArgs := #["-DautoImplicit=false"]` en `lakefile.lean`.

**Justificación**: las anotaciones de tipo explícitas evitan problemas accidentales de
polimorfismo de universos y hacen el código más legible y mantenible.

**Consecuencias**: todas las variables deben declararse o anotarse explícitamente.

---

## ADR-003: Sistema de bloqueo de archivos

**Fecha**: 2026-09-06
**Estado**: Aceptado

**Decisión**: usar `git-lock.bash` + `locked_files.txt`/`frozen_files.txt` + hook
`pre-commit` para prevenir ediciones accidentales de módulos terminados.

**Justificación**: las pruebas de Lean 4 son frágiles — cambios pequeños en módulos
terminados pueden romper pruebas dependientes. El sistema de bloqueo hace esto
explícito y mecánico en vez de depender de la memoria del desarrollador.

**Consecuencias**: el flujo de trabajo exige bloquear/desbloquear ficheros (ver
`AI-GUIDE.md` §20-21). **Debe usarse de verdad** — un sistema documentado pero con las
listas siempre vacías no aporta nada (lección aprendida en la auditoría cruzada de
2026-07-12: en varios proyectos hermanos llevaba vacío desde el primer commit).

---

## ADR-004: Convenciones de nombres Mathlib

**Fecha**: 2026-09-06
**Estado**: Aceptado

**Decisión**: todos los identificadores siguen las convenciones de nombres de
Mathlib4, documentadas en `NAMING-CONVENTIONS.md`.

**Justificación**: consistencia con el ecosistema Lean 4 más amplio. Hace los teoremas
localizables por patrón de nombre (`mem_X_iff`, `sujeto_predicado`). Facilita una
futura integración con Mathlib si se desea.

**Consecuencias**: puede requerir migración de nombres existentes. Ver
`NAMING-CONVENTIONS.md` para el diccionario completo y las 12 reglas de formación.
`REFERENCE.md` §0 da una referencia rápida.

---

## ADR-005: Namespace plano por fichero — los directorios organizan, no anidan namespaces

**Fecha**: 2026-07-12 (corrige una versión anterior de este ADR que proponía
mirroring completo de directorio; revertido tras auditar la práctica real en Peano)
**Estado**: Aceptado

**Decisión**: cada fichero `.lean` recibe **un namespace propio de un solo nivel**
bajo el namespace raíz del proyecto: `PeanoRF/Foo/Bar.lean` →
`namespace PeanoRF.Bar` (**no** `PeanoRF.Foo.Bar`). El nombre del namespace
suele coincidir con el nombre del fichero (el concepto matemático que trata), no con
su ruta completa. Los subdirectorios (`Foo/`) son **puramente organizativos** —
agrupan ficheros por tema para navegación humana — y **no** determinan el namespace.

Dentro de un mismo fichero puede haber sub-namespaces **más finos** que distingan
sub-conceptos (p. ej. `PeanoRF.FSet.ℕ₀FSet`, `PeanoRF.FSet.TupleFSet` dentro
de `FSet.lean`) — eso sí está permitido y es el "grano más fino" que complementa la
regla, siempre que quede documentado en el propio fichero.

**Regla derivada — un namespace no se comparte entre ficheros distintos**: si dos
ficheros de un mismo directorio (p. ej. `GroupTheory/Action.lean` y
`GroupTheory/NormalSubgroup.lean`) declaran literalmente el mismo namespace interno
(`namespace GroupTheory`), es casi siempre un descuido, no una decisión — mezcla las
declaraciones de ambos ficheros en un único namespace, dificulta saber qué fichero
define qué símbolo, y arrastra colisiones de nombre silenciosas. Cada fichero
consigue su propio namespace y usa `open Project.OtroFichero` para acceder a lo que
necesite de sus dependencias.

**Justificación**: es la convención que ya sigue de facto la mayoría del código real
de los proyectos de este ecosistema (verificado por auditoría exhaustiva en Peano,
2026-07-12: 57/57 ficheros de producción usaban `Peano.<Concepto>` plano, nunca la
ruta completa de directorio) — codificar aquí lo que el código ya hace evita que la
documentación contradiga la práctica real. Un mapeo 1:1 directorio↔namespace se
vuelve verboso y fragil en proyectos con más de 3-4 niveles de subdirectorios
temáticos (`Combinatorics/GroupTheory/Sylow/Sylow.lean` → `Peano.Sylow`, no
`Peano.Combinatorics.GroupTheory.Sylow.Sylow`).

**Consecuencias**: `new-module.bash` crea el fichero en el subdirectorio indicado
pero declara el namespace con el nombre del fichero, no la ruta completa.
`gen-root.bash` sigue escaneando subdirectorios recursivamente para los `import`,
pero eso es independiente del namespace. Al revisar un PR/commit que introduce un
namespace nuevo, comprobar que ningún otro fichero ya lo usa (`grep -rn "namespace
PeanoRF.NombreElegido"` antes de crear el fichero).

---

## ADR-006: Subdirectorios temáticos para la organización de módulos

**Fecha**: 2026-09-06
**Estado**: Aceptado

**Decisión**: agrupar módulos relacionados en subdirectorios temáticos
(`UpperCamelCase`) en vez de mantenerlos todos sueltos en la raíz del proyecto.

**Justificación**: más allá de un puñado de módulos, una carpeta plana deja de ser
navegable. Los subdirectorios temáticos (p. ej. `Algebra/`, `NumberTheory/`,
`Topology/`) hacen explícita la arquitectura matemática del proyecto.

**Consecuencias**: cada subdirectorio con 2+ módulos requiere un barrel (`AI-GUIDE.md`
§18). Ver también ADR-005.

---

## ADR-007: Árbol de documentación `doc/REFERENCE-{tema}.md`

**Fecha**: 2026-09-06
**Estado**: Aceptado

**Decisión**: `REFERENCE.md` es solo el índice raíz; el detalle exhaustivo de cada
subsistema vive en nodos temáticos bajo `doc/REFERENCE-{tema}.md`, con navegación
fuerte bidireccional entre índice y nodos, y entre nodos relacionados entre sí.

**Justificación**: un único `REFERENCE.md` monolítico deja de ser navegable (y de
poder proyectarse de forma incremental) mucho antes de los 100 módulos. Partirlo por
subsistema mantiene cada nodo manejable y evita que sesiones de trabajo aisladas
tengan que cargar todo el proyecto para encontrar una firma.

**Consecuencias**: cada subsistema nuevo lo bastante grande necesita su propio nodo
(`AI-GUIDE.md` §0.5). El comando `proyecta`/`repasa_y_proyecta` debe mantener los
enlaces cruzados al día.

---

## ADR-008: Sistema de anotaciones en REFERENCE.md

**Fecha**: 2026-09-06
**Estado**: Aceptado

**Decisión**: las entradas de REFERENCE.md incluyen anotaciones `@axiom_system` y
`@importance`.

**Justificación**: ayuda a los asistentes de IA a priorizar qué módulos/teoremas
cargar como contexto. Da una clasificación rápida sin tener que leer el código del
módulo.

**Consecuencias**: las anotaciones deben mantenerse al actualizar módulos. Ver
`AI-GUIDE.md` (Sistema de anotaciones para REFERENCE.md).

---

## ADR-009: `NAMING-CONVENTIONS.md` como fichero separado

**Fecha**: 2026-09-06
**Estado**: Aceptado

**Decisión**: las convenciones de nombres viven en un `NAMING-CONVENTIONS.md`
dedicado, con un resumen en `AI-GUIDE.md` y en `REFERENCE.md` §0.

**Justificación**: el diccionario completo con 12 reglas y tablas de migración es
demasiado extenso para `AI-GUIDE.md`. Un fichero separado permite ejemplos detallados
sin sobrecargar la guía principal.

**Consecuencias**: tres lugares referencian el naming: `NAMING-CONVENTIONS.md`
(canónico), `AI-GUIDE.md` (resumen), `REFERENCE.md` §0 (guía de lectura rápida). Los
tres deben mantenerse sincronizados — si divergen, `NAMING-CONVENTIONS.md` es
autoritativo.

---

## ADR-010: No se redefine infraestructura que ya existe aguas arriba

**Fecha**: 2026-09-06
**Estado**: Aceptado

**Decisión**: `PeanoRF/Prelim.lean` **no** redefine `ExistsUnique` ni las notaciones
`∃!`/`∃¹`, aunque la plantilla los traiga. Se usan los de `Peano.Prelim`. La regla
general: si un concepto ya existe en `FOL`, `ROBINSON_PlusPlus` o `Peano`, aquí se
importa, no se copia.

**Justificación**: dos definiciones idénticas en dos namespaces distintos son **dos
constantes que no componen** — no son defeq para el elaborador, y ningún lema probado
sobre una sirve para la otra. El coste no se paga al escribirlas (son diez líneas):
se paga meses después, cuando hace falta un puente `rfl` por cada teorema que las
cruce. Es una trampa **ya sufrida** en la familia de proyectos, no un riesgo teórico.

**Consecuencias**:
- `Prelim.lean` queda sin declaraciones propias mientras no haga falta ninguna.
- Antes de definir algo, se comprueba si ya existe aguas arriba.
- Si hace falta una variante distinta de algo existente, se declara **como variante**,
  con su ADR y su lema puente, no como redefinición silenciosa.

---

## ADR-011: Las tres dependencias son rutas locales, no `from git`

**Fecha**: 2026-09-06
**Estado**: Aceptado

**Decisión**: `lakefile.lean` declara `require FOL from "../FOL"`,
`require ROBINSON_PlusPlus from "../ROBINSON_PlusPlus"` y
`require peanolib from "../Peano"`. El paquete se llama **`PeanoRF`**, que **no**
coincide con el directorio `Peano-from-ROB-n-FOL` — los guiones no son identificadores
Lean válidos.

**Justificación**: este proyecto se desarrolla **a la vez** que sus dependencias. Con
`from git` se trabajaría contra el último push, no contra el árbol real, y cada cambio
aguas arriba exigiría un push + `lake update` antes de poder usarlo. Con rutas locales,
el ciclo es inmediato.

**Consecuencias**:
- Las cuatro librerías deben compartir toolchain (`v4.31.0` hoy): M-3.
- FOL se compila **siempre desde el proyecto que lo requiere**, nunca con
  `cd ../FOL && lake build`.
- El proyecto no es clonable en aislamiento: hace falta el árbol `lean4/` completo. Si
  algún día debe serlo, se cambia a `from git` con revisiones fijadas, y se documenta.
- Lake deduplica FOL: lo requerimos nosotros y también ROBINSON_PlusPlus, ambos desde
  la misma ruta.

---

## ADR-012: Se importan capas concretas, no barrels completos

**Fecha**: 2026-09-06
**Estado**: Aceptado

**Decisión**: de `ROBINSON_PlusPlus` se importa `Minimal.Axioms` (y lo que se necesite
de `Minimal/`), no el barrel `ROBINSON_PlusPlus`. De `Peano` se importa
`PeanoNat.Axioms`, no el barrel `Peano`. De `FOL`, el barrel completo sí — es la base
lógica, es pequeña y está estable.

**Justificación**: dos razones independientes, y cada una bastaría.

1. **Coste**: el barrel de ROBINSON_PlusPlus arrastra la capa `Meta/` entera
   (aritmetización, Gödel, ~89 módulos); el de Peano arrastra teoría de grupos, Sylow y
   primos. Nada de eso se usa aquí.
2. **Frentes abiertos**: ROBINSON_PlusPlus trabaja en ramas donde el árbol está en rojo
   de forma **conocida y localizada**. Importar el barrel completo hace que un frente
   abierto aguas arriba rompa este build sin que nada haya cambiado aquí.

**Consecuencias**: cada módulo importa lo que necesita, y ampliar el *import surface* es
una decisión consciente que se anota en `DEPENDENCIES.md` §1.

---

## ADR-013: Pureza constructiva en DOS EJES — objeto intuicionista, meta constructivo

**Fecha**: 2026-09-06
**Estado**: Aceptado (directiva del autor, fundacional)

**Decisión**: la pureza constructiva de este proyecto se exige en **dos ejes distintos**,
y distinguirlos no es una sutileza — es lo que hace la directiva cumplible:

* **Eje OBJETO** — la lógica *formalizada* es intuicionista. Prohibido usar los axiomas
  clásicos de nivel objeto de FOL. **Duro, sin baseline.**
* **Eje META** — las *pruebas en Lean* son constructivas, footprint diana
  `⊆ {propext, Quot.sound}`. **Duro para lo nuestro, con deuda heredada tolerada
  temporalmente.**

**Justificación**: el valor del proyecto descansa en que la aritmética que construye sea
intuicionista *como teoría*, no solo verificada por un asistente que por dentro usa
elección. Los dos ejes se pueden violar por separado — se puede probar clásicamente en
Lean un teorema sobre una lógica intuicionista, y al revés — así que hacen falta dos
controles, no uno.

**La medición que lo hace viable** (`sondeos/README.md`, 2026-09-06; los `import` no
demuestran nada, solo `#print axioms`):

* `FOL` declara **13 `axiom`**, de los que solo **3 son clásicos de nivel objeto**
  (`MetaRules.dne`, `Theorems.Neg.dne`, `Theorems.Quantifiers.forall_not_impl_exists_not`).
  Las cinco meta-reglas (`imp_intro`, `gen`, `raa`, `or_elim`, `ex_elim`) **no** son
  clásicas: `raa` es introducción de ¬ pese a su nombre, y `gen` es la ω-regla
  (infinitaria, no clásica). Las otras cinco son de completitud.
* Los tres clásicos **solo se usan desde la mitad modelo-teórica** de FOL
  (Completeness/Compacity). Como no la importamos (M-5), violar M-1 exige un `import`
  deliberado: la pureza de nivel objeto sale casi gratis.
* `Peano` (`PeanoNat.Axioms`): **192/192 declaraciones limpias, 0 `axiom`**. El cimiento
  aritmético ya cumple la diana.
* `ROBINSON_PlusPlus.Minimal.Axioms`: **44 de 313 arrastran `Classical.choice`, y entre
  ellas `axioms` misma** — el conjunto de axiomas de Q⁺⁺ — vía las funciones de
  codificación `strCodeM`/`termCodeM`/`formCodeM`, que usan primitivas `String` del
  núcleo de Lean 4.31. Hoy **cualquier** teorema sobre Q⁺⁺ hereda `Classical.choice`.

**Consecuencias**:

- RPP **no es constructivo a nivel meta todavía, pero sí lo es a nivel objeto**, y su
  autor va a sanear el nivel meta. Esa deuda se tolera con aviso y recuento en el gate
  (`inheritedMetaDebt`), **nunca en silencio**, y se convierte en error poniendo
  `metaDebtIsError := true` el día que RPP esté limpio.
- La tolerancia va por **procedencia, no por nombre de axioma**: solo cuenta como
  heredado lo que entra atravesando una constante de `FOL`/`ROBINSON_PlusPlus`/`Peano`.
  Un `Classical.em` puesto por nuestra propia prueba es ERROR aunque el axioma se llame
  igual. (Esto no es teoría: la primera versión del gate toleraba por nombre y un smoke
  test la atravesó sin despeinarse — ver ADR-015.)
- El *import surface* de FOL se estrecha a la mitad demostrativa (ADR-012, M-5).

---

## ADR-014: `ℕ₀` de peanolib como único natural

**Fecha**: 2026-09-06
**Estado**: Aceptado (directiva del autor)

**Decisión**: el natural del proyecto es **`ℕ₀`** (`peanolib`, `Peano.PeanoNat`). `Nat` de
Lean solo puede aparecer como tipo técnico de kernel estrictamente inevitable (`sizeOf`,
literales internos, `omega`), **nunca en enunciados ni como dependencia matemática**.

**Justificación**: `Nat` trae su propia teoría y sus propios lemas; mezclarlo con `ℕ₀`
reproduce exactamente el problema de ADR-010 a mayor escala — dos aritméticas que no
componen y un peaje de coerciones. Además `ℕ₀` está medido limpio (192/192), así que la
elección no cuesta nada en el eje meta.

**Consecuencias**:
- Aritmética y orden se toman de peanolib; las metas numéricas con `omega₀`, no `omega`.
- ⚠️ Cuidado con el `+` global de Peano en `termination_by`: anotar `(… : Nat)` o anidar
  `Nat.add` para evitar la coerción `Nat → ℕ₀` (trampa heredada de AczelSetTheory).
- Reutilizar los subtipos públicos de peanolib (`ℕ₁`, `ℕ₂`, …), no redefinirlos (M-4).

---

## ADR-015: El gate se prueba con smoke tests, porque un gate no probado puede ser vacuo

**Fecha**: 2026-09-06
**Estado**: Aceptado

**Decisión**: `PeanoRF/Meta/AxiomCheck.lean` se verifica inyectando temporalmente una
declaración que **debe** hacerlo fallar, una por eje, y comprobando que falla. Se repite
tras cualquier cambio en la lógica del gate.

**Justificación**: no es celo, es una corrección de un fallo real ocurrido al escribirlo.
La primera versión tolerapa `Classical.choice` **por nombre de axioma**, con el argumento
de que llegaba heredado de RPP. El smoke test — `open Classical in theorem smoke (p : Prop)
: p ∨ ¬p := em p` — **pasó el gate como «deuda heredada»**. Un control que no puede
distinguir nuestra propia lógica clásica de la de una dependencia no controla nada, y lo
peor es que da verde: se parece a estar cumpliendo la MANDATORY.

La misma clase de fallo que `check-doc-sync.bash` tuvo con las cifras (un patrón que no
encuentra su frase da verde sin comprobar nada, AI-GUIDE §27). **Regla general del
proyecto: un control nuevo no está terminado hasta que se le ha visto fallar.**

**Consecuencias**: el gate clasifica por procedencia (recorrido hacia atrás por las
declaraciones propias hasta la frontera con las dependencias), y ambos ejes tienen su
smoke test documentado en el propio fichero.

---

## ADR-016: El núcleo es HA FINITARIA; la ω-lógica vive en una capa aparte

**Fecha**: 2026-09-06
**Estado**: Aceptado

### Contexto: qué es este proyecto

PeanoRF vuelca el proyecto **Peano** al lenguaje **FOL⁼ + ROB++**, de forma puramente
constructiva: un **espejo** en el que las propiedades que se demuestren para PeanoRF se
conserven en Peano. No es una duplicación — **PeanoRF es la versión fundacional y Peano
la computacional** — y en último término PeanoRF debe poder servir de **meta-lenguaje**
para los proyectos FOL y ROB++.

Esos tres objetivos no piden lo mismo del cálculo, y ahí está la decisión.

### El problema

`ROBINSON_PlusPlus/Full/Induction.lean:166` declara:

```lean
axiom ax_induction (φ : Formula) : axioms ⊢ inductionFormula φ
```

Postula que el **esquema de inducción es derivable del conjunto de axiomas de Q⁺⁺**. Con
un `⊢` finitario ese enunciado es **falso** — Q no demuestra inducción. Es coherente sólo
bajo la lectura que el propio `FOL/MetaRules.lean` declara en su docstring: *«axiomatizan
"demostrabilidad = verdad en el modelo estándar"; el sistema resultante es ω-lógica,
estrictamente más fuerte que FOL⁼ finitaria»*.

**Medición** (`sondeos/omega_probe.lean`, 2026-09-06; 521 declaraciones de ROB++
Minimal+Full):

| | |
|---|---:|
| arrastran alguna ω-regla o meta-axioma | **99 (19 %)** |
| `gen` · `ex_elim` · `or_elim` · `imp_intro` · `raa` | 70 · 64 · 64 · 42 · 13 |
| usan lógica **clásica** de nivel objeto | **0** |
| decls que dependen de `ax_induction` | 30 |

La segunda fila desde abajo confirma la tesis: **ROB++ es intuicionista a nivel objeto**.
Pero **no es finitario**.

### La consecuencia sobre los tres objetivos

Si PeanoRF se construye sobre ROB++/Full tal cual, PeanoRF **no es HA: es ω-lógica sobre
Q⁺⁺**, es decir, aritmética verdadera. Y eso afecta a cada objetivo de forma distinta:

| Objetivo | Bajo ω-lógica |
|---|---|
| **Espejo** (transferir a Peano) | ✅ funciona — ω-lógica es sólida para ℕ |
| **Fundacional** | ⚠️ se desdibuja — donde `⊢` = verdad en ℕ no hay teoría, hay modelo |
| **Meta-lenguaje** | ❌ imposible — `⊢` no es r.e.; no hay checker para una regla con infinitas premisas |

### El peligro concreto (no teórico)

`raa` e `imp_intro` toman premisas **META** (`Γ ⊢ A → Γ ⊢ B`), que se cumplen
**vacíamente** cuando la premisa no es derivable. En cuanto este proyecto demuestre
soundness de `Derives` hacia ℕ₀, basta un testigo de no-derivabilidad `¬(axioms ⊢ ψ)`
con ψ verdadera para que `raa` dé `axioms ⊢ ¬ψ` y soundness lo convierta en `¬⟦ψ⟧`:
contradicción.

**ROBINSON_PlusPlus no está afectado**, y no por suerte: enuncia Gödel I con `Prf` — la
demostrabilidad **aritmetizada y finitaria** (`goedel_first_numeral : ConsistentOmega →
¬ Prf godelCN`) — y su puente `prf_to_derives` va en un solo sentido. Nunca produce
`¬(axioms ⊢ φ)`. **Pero PeanoRF es justo el proyecto que fabricaría el ingrediente que
falta**: la interpretación. De ahí M-9.

### Decisión

1. **Núcleo `PeanoRF.*` = HA finitaria.** Sólo los constructores inductivos de `Derives`
   (natural deduction intuicionista: el propio `FOL.lean` la etiqueta así, con `bot_elim`
   como única regla de ⊥). Prohibidas las ω-reglas y los meta-axiomas (M-7).
2. **La inducción entra en el CONJUNTO DE AXIOMAS** (M-8), no como derivabilidad
   postulada. Cada derivación usa **finitas** instancias: `axioms ++ [inst₁…instₖ] ⊢ φ`.
   Ventaja lateral y grande: queda registrado **qué instancias hace falta** en cada
   teorema — contabilidad al estilo de matemática inversa (IΔ₀ vs IΣ₁ vs HA completa),
   que es contenido fundacional de primera y sale gratis del diseño.
3. **Capa `PeanoRF.Omega.*`** (`PeanoRF/Omega/Basic.lean`), donde las ω-reglas están
   permitidas y **contadas** en cada build. Sirve para reusar `Full/` sabiendo lo que
   cuesta: lo que pase por ahí vale para el espejo, no para lo fundacional ni para el
   meta-lenguaje.
4. **La soundness se demuestra sólo del fragmento finitario** (M-9).

**Sustitutos finitarios**, que el propio docstring de FOL ya identifica:
`imp_intro`→`Derives.intro_impl` · `raa`→`intro_impl` sobre `¬A = A ⇒ ⊥` ·
`or_elim`→`Derives.elim_or` · `ex_elim`→`Derives.elim_ex` · `gen`→`Derives.intro_forall`.

### Por qué un TERCER eje en el gate, y no una ampliación del primero

Porque **finitario ≠ constructivo**. `raa`, `gen`, `or_elim`, `ex_elim` e `imp_intro`
**no son clásicas**: `raa` es introducción de ¬ pese al nombre, y `gen` es la ω-regla,
infinitaria pero intuicionista. Meterlas en el eje objeto habría sido un error de
diagnóstico por nomenclatura, y habría amputado el proyecto por un malentendido.
Son ejes independientes y se violan por separado.

### Consecuencias

- ROB++/Full **no se puede consumir tal cual** en el núcleo: el 19 % de sus resultados
  entra por la capa ω, o se reprueba finitariamente sobre el conjunto de axiomas con
  inducción. Es el coste principal del proyecto, y está cuantificado.
- El espejo hacia Peano no se pierde: la capa ω sigue sirviendo para transferir.
- PeanoRF conserva los fenómenos de Gödel (con `⊢` r.e.), que es condición necesaria para
  que tenga sentido como meta-lenguaje.
- ⚠️ **Techo de Gödel II**: PeanoRF podrá ser metateoría de FOL⁼ y de Q⁺⁺ — estrictamente
  más débiles — pero **nunca de sí misma**. La arquitectura es una jerarquía, no un
  círculo, y se dice aquí para que nadie lo intente.

---

## Plantilla para nuevas decisiones

## ADR-NNN: [Título]

**Fecha**: 2026-09-06
**Estado**: [Propuesto | Aceptado | Obsoleto | Sustituido por ADR-XXX]

**Contexto**: [¿Por qué hace falta esta decisión?]

**Decisión**: [¿Qué se decidió?]

**Justificación**: [¿Por qué esta opción frente a las alternativas?]

**Consecuencias**: [¿Cuáles son las contrapartidas?]
