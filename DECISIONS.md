# Decisiones de Diseño — PeanoRF

**Última actualización:** 2026-09-23
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
| **M-5** | **No importar barrels completos** de RPP ni de Peano. Y en particular: **PROHIBIDO importar `FOL.Completeness` y `FOL.Compacity`.** `FOL.Semantics`/`Soundness0` SÍ se permiten desde 2026-09-16 (ADR-019: `satisfies` no tiene footprint; lo clásico está en la prueba, no en la semántica). | [ADR-012](#adr-012-se-importan-capas-concretas-no-barrels-completos), [ADR-013](#adr-013) | revisión de `import` + el gate (el uso, no el import, es lo que rompe) |
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

## ADR-017: El sujeto es `⊢ᵢ` propio, no `Derives` ni `Derives₀`

**Fecha**: 2026-09-16
**Estado**: Aceptado

**Contexto**: entre el 6 y el 16 de septiembre, ROBINSON_PlusPlus declaró **las cinco
nociones de derivabilidad** (`REFERENCE.md §0bis`) y FOL estrenó un estrato entero. Dos
hechos nuevos invalidan la base sobre la que se construyó H2:

1. **`FOL.Derives` no puede tener solidez.** `FOL/cuarentena/Inconsistencia.lean` prueba
   `inconsistencia_de_cualquier_solidez`: *cualquier* testigo del enunciado de solidez para
   `⊢` da `False`. Está habitado por 7 axiomas y declarado **HERRAMIENTA** (ADR-024 de RPP):
   ningún metateorema significa lo que dice sobre él. ⇒ De `axioms ⊢ φ` **jamás** se podrá
   concluir que φ es verdadera en ℕ₀, y ahí muere el espejo, que es el proyecto.
   Es M-9 confirmado y llevado más lejos por el autor de aguas arriba.
2. **La ω-regla es ahora un CONSTRUCTOR** (`Derives.gen_rule`), no un axioma. `⊢` dejó de
   ser r.e. **por construcción**, y el eje finitario del gate se quedó ciego sin avisar
   (ver ADR-018).

**Y `Derives₀` tampoco sirve**: tiene 0 habitantes-axioma y `derives0_soundness` en el
build, pero trae `dne_rule`, `dne_schema` y `forall_not_ex_not` **como constructores** —
es clásico por diseño, porque su cometido era la completitud. Adoptarlo convertiría a
PeanoRF en espejo de PA, no de HA, contra M-1.

**Decisión**: `PeanoRF.Calculus.Derivesᵢ` (`⊢ᵢ`) = los **18 constructores no clásicos** de
`Derives₀`, con el puente `derivesI_to_derives0` probado por inducción (legítima: 0
habitantes-axioma, footprint `[propext]`). Todo H2 migra ahí.

**Justificación**: es el único punto del retículo que cumple las tres condiciones a la vez
— 0 habitantes-axioma (inducción legítima), finitario (`⊢` r.e.) e intuicionista (M-1).
No existe aguas arriba (comprobado), así que M-4 no lo prohíbe.

**Consecuencias**:
- La solidez de `⊢ᵢ` sale de componer el puente con `derives0_soundness`, que ya está en el
  build ⇒ **H3 queda en gran parte adelantado**.
- **Coste medido**: los teoremas de `⊢` no bajan a `⊢ᵢ`, sólo suben. Hubo que reprobar
  `symm`, `trans`, `congr_succ` y `spec` — **cinco lemas**, mismas pruebas con los
  constructores renombrados (`PeanoRF/Calculus/Eq.lean`).
- Los teoremas de ROBINSON_PlusPlus siguen siendo consumibles **en una dirección**: lo
  nuestro entra en su mundo vía `derivesI_to_derives`; lo suyo no entra en el nuestro.

---

## ADR-018: El control de CONSTRUCTORES, porque `#print axioms` es ciego

**Fecha**: 2026-09-16
**Estado**: Aceptado

**Decisión**: el gate añade un **cuarto control** que recorre el término de prueba
buscando constructores prohibidos (`forbiddenConstructors`), además de los tres ejes que
miden footprint.

**Justificación**: `collectAxioms` ve axiomas, **no constructores**. Cuando aguas arriba
`FOL.MetaRules.gen` pasó a ser el constructor `Derives.gen_rule`, su footprint quedó en
`[propext]` y **el eje finitario dejó de vigilar la ω-regla**: el contador de la capa ω
bajó de 5 a 4 usos y el gate siguió diciendo OK. Es el fallo de ADR-015 otra vez —un
control que da verde sin comprobar— pero esta vez por **deriva aguas arriba**, no por un
error al escribirlo.

ROBINSON_PlusPlus ya había nombrado la causa general en su regla **M-11**: «`#print axioms`
es CIEGO» a los habitantes de un inductivo, y por eso tiene `check-estratos.bash` **además
de** `check-footprints.bash`. No son el mismo control y ninguno sustituye al otro.

### ⚠️ Addendum (mismo día): el primer smoke test era INVÁLIDO, y el control estaba ciego

Al estrenar el control se probó con `def smoke := @Derives₀.dne_rule` — y pasó. Pero el
recorrido usaba `ConstantInfo.value?`, que en Lean 4.31 devuelve **`none` para TEOREMAS**.
⇒ El walker veía sólo los TIPOS, no los términos de prueba, y por tanto **el control de
constructores Y el de procedencia estaban ciegos para casi todo lo que vigilan**, porque
casi todo son teoremas. El smoke test usaba un `def`, cuyo valor sí está, y lo enmascaró.

Se destapó al escribir `derivesI_soundness`: el gate no reconocía su `Classical.choice`
como heredado. Arreglado leyendo `.thmInfo v => v.value` explícitamente, y **re-probado con
un TEOREMA**, que ahora sí se caza.

🔑 **Lección, y es la generalización de ADR-015**: un smoke test tiene que usar la **misma
clase de declaración** que el control vigila. Un control puede pasar su prueba y seguir
siendo vacuo para el caso real.

### 🔁 Reescrito el 2026-09-17: de lista POR NOMBRE a descubrimiento POR TIPO

La lista de constructores prohibidos **caducó tres veces en dos días**, y la auditoría del
2026-09-17 lo dejó medido:

| qué pasó | efecto |
|---|---|
| `FOL.MetaRules.gen` → constructor `Derives.gen_rule` | el eje finitario dejó de verla |
| `Derives` movió sus clásicas de axiomas de `MetaRules` a **constructores propios** | sin vigilar |
| aparecieron `Derives₁` y `Derives₂`, cada uno con **su copia** de las tres clásicas | sin vigilar |

**9 de 12 constructores clásicos quedaron ciegos.** El eje objeto —que es la tesis del
proyecto— cubría una cuarta parte del terreno.

🔑 **El defecto no era la lista: era su POLARIDAD.** Una lista de prohibidos deja pasar
todo lo que no nombra, y aguas arriba crece más rápido de lo que se actualiza.

**El criterio nuevo, estructural:**

1. Se **descubren por TIPO** las relaciones de derivabilidad: inductivos de tipo
   `List Formula → Formula → Prop`. Mismo criterio que `check-estratos.bash` de RPP
   —clasificar por el TIPO, no por el nombre—, y por eso **un cálculo nuevo aparece solo**.
2. Los constructores de **nuestro** `Derivesᵢ` son la referencia.
3. **Todo constructor de otro cálculo cuyo nombre corto no esté entre los de `Derivesᵢ` es
   una regla que no tenemos** ⇒ prohibido en el núcleo. Los tres clásicos
   (`dne_rule`, `dne_schema`, `forall_not_ex_not`), **en ninguna parte, ni en la capa ω**.

⇒ **El silencio significa PROHIBIDO, no permitido.** Un `Derives₃` futuro entra vigilado
sin tocar el fichero.

⚠️ Los puentes (`derivesI_to_derives0`) siguen pasando: usan `Derives₀.hyp`,
`Derives₀.intro_impl`… y esos nombres cortos **sí** están en `Derivesᵢ`. Lo que no pasa es
exactamente lo que `⊢ᵢ` no tiene.

**Y el gate publica un INVENTARIO en cada build** — cuántas relaciones ha detectado y
cuántos constructores ajenos vigila. Sin eso, un cálculo nuevo entra en silencio aunque
esté vigilado.

**Probado** (ADR-015) con un **teorema** que usa `Derives₁.dne_rule` — un constructor que la
lista vieja **no contenía** — y otro que usa `Derives.gen_rule`: los caza los dos y los
clasifica (`OBJETO` vs `FINITARIO/AJENO`).

### 🔁 Revisión b (2026-09-17, tarde): el tipo, por TELESCOPIO

La misma auditoría, repetida por la tarde con la pregunta de siempre —**¿sobre cuánto del
terreno actúa?**— encontró que el criterio por tipo de la mañana reconocía **una forma
fija**, `List Formula → Formula → Prop`. En 24 h aguas arriba había aparecido lo que no
cabe en esa forma:

| relación | tipo | ctors |
|---|---|---|
| `LK₀`, `LKc` (FOL, ADR-046/052) | `List Formula → List Formula → Prop` | 14 + 15 |
| `LKh` (FOL, Hauptsatz) | `Nat → List Formula → List Formula → Prop` | 14 |
| `Prf`, `Prf₀` (RPP, Hilbert) | `Formula → Prop` | 7 + 17 |

**Cinco relaciones, 67 constructores, invisibles.** Medido: un teorema con `LK₀.ax` y otro
con **`LKc.cut`** —la regla de corte— pasaban sin una palabra.

🔑 **La misma lección un nivel más arriba**: el silencio volvía a significar
*permitido*, ahora por la forma del tipo en lugar de por el nombre. Corregir la polaridad
de la lista no sirve de nada si el conjunto sobre el que se aplica se fija a mano.

Y una segunda medición, peor: **la última lista POR NOMBRE que quedaba** —la que decide
qué constructor es *clásico*— dejaba entrar la doble negación en la capa ω. `PrfH.p3` es
`((A ⇒ ⊥) ⇒ ⊥) ⇒ A`, o sea la DNE con otro nombre; como `p3` no estaba en la lista,
se clasificaba «FINITARIO/AJENO» y la capa ω lo toleraba. Con un teorema que probaba ese
esquema dentro de `PeanoRF.Omega`, el gate imprimía:

```text
[gate] OK — 86 declaraciones propias verificadas. Eje objeto: intuicionista puro
```

**El criterio, en su forma actual:**

1. **Descubrimiento por TELESCOPIO**: inductivo **recursivo**, que menciona `Formula`,
   que acaba en `Prop` y **todos** cuyos argumentos son `Formula`, `List Formula` o `Nat`.
   La recursividad es lo que separa un cálculo de un predicado auxiliar (`LocalRule`,
   `EqInstance`); `mentionsFormula`, lo que impide que entre `Nat.le`.
2. **CLÁSICO por lo que la regla DICE**: se busca el patrón de la doble negación en el
   TIPO del constructor, en sus dos escrituras (`neg (neg A)` y `((A ⇒ ⊥) ⇒ ⊥)`), más
   el esquema `(¬∀A) ⇒ ∃¬A`. La lista por nombre queda como **refuerzo**: sólo añade.
3. **La capa ω deja de ser un comodín**: ya no basta con estar en `PeanoRF.Omega.*`; el
   constructor tiene que estar además en `omegaAllowedForeignCtors` — hoy **vacía**. La
   capa ω relaja en EFECTIVIDAD (M-7), nunca en la lógica objeto (M-1).
4. **El inventario publica los CASI-CANDIDATOS**: recursivos que hablan de fórmulas y
   acaban en `Prop` pero cuyo telescopio se rechazó. Si algún día aparece ahí algo que
   sí es un cálculo, **se ve** en vez de no existir.

**Medido después** (`sondeos/audit_2026-09-17b.lean`, con los seis módulos importados):
**11 relaciones detectadas, 90 constructores ajenos vigilados, 14 clásicos**. Los cuatro
smoke tests —`LK₀.ax`, `LKc.cut`, `PrfH.p3`, `Prf.p3`— cazados; y el contraejemplo
`Derives₀.hyp` sigue **pasando**, que es lo que mantiene vivos los puentes.

**Consecuencias**:
- Probado con smoke test en los dos ejes (ADR-015) **y con las dos clases de declaración**:
  detecta `Derives₀.dne_rule` y `Derives.gen_rule` donde el footprint no ve nada.
- ✅ **Deuda SALDADA el 2026-09-17**: ya no es por nombre, es por tipo (arriba).
- **Regla general**: cuando una dependencia cambia la naturaleza de un símbolo (axioma →
  constructor), los controles que lo vigilaban **caducan en silencio**. Revisarlos forma
  parte de ponerse al día, no es opcional.

---

## ADR-019: M-5 se enmienda con una medición — lo clásico no está en la semántica

**Fecha**: 2026-09-16
**Estado**: Aceptado

**Decisión**: se permite importar `FOL.Semantics` y `FOL.Soundness0`. `FOL.Completeness` y
`FOL.Compacity` siguen **prohibidas**.

**Justificación**, medida (`sondeos/h3_probe.lean`):

| símbolo | footprint |
|---|---|
| `FOL.Metamath.Semantics.satisfies` | **ninguno** |
| `FOL.Metamath.Soundness0.derives0_soundness` | `propext, Classical.choice, Quot.sound` |

M-5 se escribió el 2026-09-06 con la medición de entonces: la mitad modelo-teórica de FOL
era clásica en bloque. La medición de hoy la matiza — **lo clásico no está en la semántica,
está en la PRUEBA**. La definición `satisfies` es limpia; importarla no cuesta nada.

**Consecuencias**:
- El teorema de transferencia (`derivesI_soundness`) se puede escribir hoy.
- Usarlo arrastra `Classical.choice` heredado, que el gate contabiliza por procedencia.
### 🏁 La conjetura de este ADR es CIERTA — y el camino hasta comprobarlo importa

**Resultado final (2026-09-16):**

| símbolo | footprint |
|---|---|
| **`PeanoRF.Calculus.derivesI_soundness`** | **`propext, Quot.sound`** ✅ |
| **`PeanoRF.Calculus.derivesI_consistent`** | **`propext, Quot.sound`** ✅ |
| `FOL.Metamath.Soundness0.derives0_soundness` | + `Classical.choice` |

⇒ 🏁 **La solidez de la lógica intuicionista, demostrada intuicionistamente.** Y el
`Classical.choice` que le queda a `derives0_soundness` es **exactamente el precio de sus
tres reglas clásicas**, ahora que la maquinaria semántica compartida está limpia.

### ⚠️ Pero primero se midió mal, y la lección es cara

La inducción directa sobre los 18 constructores salió **sucia**, y se registró la conjetura
como REFUTADA. Era falso: la medición estaba **contaminada** por un `Classical` que no tenía
nada que ver con la lógica clásica.

Toda la suciedad de la semántica entraba por **un solo lema**, `shift_updateEnv_comm`, y
dentro de él por **una sola línea** — un `omega` cerrando por contradicción una meta de
tipo `D`, es decir **fuera del lenguaje de omega**:

```lean
| zero => omega                                                      -- ⛔ Classical.choice
| zero => exact absurd (Nat.le_zero.mp (Nat.not_lt.mp h1)).symm h2   -- ✅ cero axiomas
```

🔑 **`omega` sobre metas ARITMÉTICAS es limpio** (`propext, Quot.sound`); **sobre metas
fuera de su lenguaje, descargadas por contradicción, mete `Classical.choice`.** Instancia
NUEVA del «Classical oculto» de §27, distinta de las ya documentadas en la familia.

🔑 **Lección de método**: *una medición de footprint sólo refuta una conjetura sobre lógica
si el resto de la cadena está limpio.* Refutar con la cadena sucia es refutar el ruido. Los
sospechosos descartados uno a uno (`by_cases`, `rcases`, `simp`, `rw`, `funext`, `dsimp`,
las dicotomías de `Nat`) eran todos inocentes: el culpable no aparecía porque no se buscó
**por ramas** hasta el final.

---

## ADR-020: La consistencia de `⊢ᵢ`, también por la vía SINTÁCTICA

**Fecha**: 2026-09-17
**Estado**: Aceptado

**Contexto**: `derivesI_consistent` (ADR-019) sale de la solidez: si `[] ⊢ᵢ ⊥`, entonces
`⊥` sería verdadera en todo modelo. Funciona y mide limpio — pero para llegar **necesita un
modelo**, es decir, presupone justamente la clase de objeto de la que la teoría formal
pretende hablar. Para un proyecto cuyo cometido es fundacional, eso es una dependencia que
conviene poder evitar, aunque no se note en el footprint.

El 2026-09-17 aguas arriba cerró `FOL.Finitary0.derives0_consistent_fin` (su ADR-053): la
consistencia de `⊢₀` por la vía sintáctica — pasar a un cálculo de secuentes y comprobar
que ningún secuente **sin corte** concluye `⊥`.

**Decisión**: añadir `Calculus/Consistency.lean` con `consistI_syn`, el mismo enunciado por
composición del puente `⊢ᵢ → ⊢₀` con ese teorema. Las dos rutas conviven; ninguna sustituye
a la otra.

**Justificación**: son **dos hechos distintos** aunque el enunciado coincida. Uno dice «no
hay derivación de ⊥ porque ⊥ no es verdadera en ningún modelo»; el otro, «no hay derivación
de ⊥, y punto, mirando sólo la forma de las derivaciones». Para el espejo de PeanoRF importa
tener el segundo.

**Consecuencias**:
- ⚠️ **La cifra no mejora**: ambas miden `[propext, Quot.sound]`. Se documenta así, y
  explícitamente, porque la tentación de vender el módulo como una mejora de footprint
  sería exactamente el tipo de afirmación que este proyecto mide antes de escribir.
  `#print axioms` **no distingue** «usa un modelo» de «no lo usa» — misma ceguera que M-11.
- ⛔ **No es la consistencia de HA.** Es la de la lógica, con contexto **vacío**. La de HA
  es Gentzen y pide inducción hasta `ε₀`, fuera del núcleo finitario (ADR-016). Decirlo en
  el módulo no es pedantería: confundirlas sería demostrar de más justo donde M-9 vigila.
- El import de `FOL.Finitary0` mete en el entorno `LK₀`, `LKc`, `LKh`, `Derives₁` y
  `Derives₂`. El inventario del gate pasa de 3 relaciones a **7**, y las vigila todas: es
  exactamente para esto que el descubrimiento es por telescopio (ADR-018 rev. b).
- El build pasa de 30 a **42 jobs**.
- ⭐ `notP_syn` (que `⊢ᵢ` no prueba un átomo) es **la mitad** de la separación que persigue
  H3bis: con la propiedad de disyunción, mata una de las dos ramas de `P ∨ ¬P`.

---

## ADR-021: El gate publica su ALCANCE, porque su lista de imports es una lista a mano

**Fecha**: 2026-09-17
**Estado**: Aceptado

**Contexto**: el gate barre toda declaración cuyo módulo empiece por `PeanoRF`, pero
**sólo las que están en su entorno**, y su entorno lo fijan los `import` escritos a mano en
la cabecera de `Meta/AxiomCheck.lean` (no puede importar el barrel raíz: sería un ciclo).

Medido el 2026-09-17: al crear `Calculus/Consistency.lean` el build pasó a 42 jobs y todo
salió verde — y el gate siguió diciendo **«80 declaraciones propias verificadas»** sobre los
ocho módulos que sí veía. Las dos declaraciones nuevas **no las vigilaba nadie**, y nada
lo dijo.

🔑 Es la patología del día otra vez: una lista mantenida a mano cuyo **silencio significa
«no vigilado»**, y encima con el gate anunciando OK.

**Decisión**: dos piezas, porque una sola no cierra.

1. El gate **publica su ALCANCE** en cada build: cuántos módulos propios tiene en el
   entorno, y cuáles.
2. `check-doc-sync.bash` gana el control **[E]**, BLOQUEANTE: cada `.lean` del árbol
   (menos plantillas y el propio módulo del gate) tiene que aparecer en ese alcance; si no,
   dice exactamente qué `import` falta.

**Justificación**: la alternativa «acordarse de añadir el import» es la que acaba de fallar.
Publicar el alcance sin comprobarlo tampoco basta: sería una cifra más que nadie lee. El
que manda es [E], y lo que el gate publica es su **entrada**.

**Consecuencias**:
- Probado (ADR-015) retirando el import a propósito: [E] responde
  `✗ PeanoRF.Calculus.Consistency está en el árbol pero FUERA del alcance del gate`.
- [E] **no funciona con `--quick`** — sin build no hay salida del gate que leer — y lo dice
  en vez de callarse, como el resto de controles desde esta mañana.
- `check-doc-sync.bash` guarda ahora la salida del build en un temporal en vez de tirarla:
  de ahí salen la cifra de `jobs` y el alcance.
- ⚠️ Es un control **propio de este proyecto**: va tras `GATE_SCOPE_MARKER`, vacío en la
  plantilla, y ahí el control se anuncia como desactivado.

---

## ADR-022: La propiedad de disyunción, y por qué se intercaló antes que H4

**Fecha**: 2026-09-17
**Estado**: Aceptado

**Contexto**: al inventariar los 22 teoremas del proyecto salió un hecho incómodo:
**ninguno fallaba clásicamente**. Todos valían palabra por palabra para `⊢₀`, porque sólo
usan los 18 constructores compartidos. Sustituyendo `⊢ᵢ` por `⊢₀` en todo el árbol, **todo
seguía compilando**. La tesis del proyecto —«PeanoRF es HA y no PA»— era arquitectónica: la
sostenían la elección de cálculo y el gate, no una demostración.

**Decisión**: intercalar **H3bis** antes de H4 y demostrar la **propiedad de disyunción** y
la **de existencia** por la barra de Kleene, y con ellas la separación `⊢ᵢ ≠ ⊢₀`.

**Justificación**: automatizar el volcado (H4) antes de tener un solo teorema que
justifique por qué este espejo merece existir es optimizar el transporte antes de saber qué
se transporta. Y las dos propiedades **son** la tesis: PA no tiene ninguna de las dos.

**Consecuencias**:
- 🏁 `derivesI_ne_derives0 : ∃φ, ([] ⊢₀ φ) ∧ ¬([] ⊢ᵢ φ)`, en `[propext, Quot.sound]`.
  El testigo es `P ∨ ¬P`, que `⊢₀` prueba **sin `Classical.choice`** por la vía H de FOL.
- La propiedad de **existencia** es la sombra sintáctica de la realizabilidad (ADR-016): el
  testigo `t` **es** el cálculo que el lado Peano del espejo tendría que ejecutar. H6 deja
  de ser una aspiración y pasa a tener un enunciado del que colgar.
- Costó **tres módulos de infraestructura**: `Subst` (álgebra σ), `SubstDerives`
  (`⊢ᵢ` cerrado bajo sustitución) y el grueso de `Slash`.

---

## ADR-023: La regla de Leibniz en un índice cualquiera se DERIVA, no se pide

**Fecha**: 2026-09-17
**Estado**: Aceptado

**Contexto**: el último caso de L2 —`Derivesᵢ.subst`— pedía que la barra fuera invariante
bajo sustituciones **demostrablemente iguales**. Los casos atómicos, `∧`, `∨` y `→` salían;
el del cuantificador se atascaba: `Derivesᵢ.subst` sustituye sólo en el **índice 0**, y al
entrar bajo un `∀` el índice en que dos sustituciones difieren pasa del 0 al 1.

Se contemplaron dos salidas: derivar la regla aquí, o pedirla aguas arriba — `Derives₀`
tiene el mismo `subst` clavado en 0, así que el problema es suyo también.

**Decisión**: derivarla. `leibniz_at` en `Calculus/SubstDerives.lean`.

**Justificación**: **no hace falta un axioma ni un encargo**, sólo el álgebra σ que ya
existía. Se abstrae la variable `k` al índice 0 con
`θ n = if n = k then #0 else liftTerm 0 (ρ₁ n)`, y entonces `substF ρ f` es literalmente
`(substF θ f)[ρ k / 0]` — con lo que la regla de índice 0 ya vale. Doce líneas.

**Consecuencias**:
- ✅ El encargo a FOL se queda sólo con la sustitución paralela y `formulaComplexity`.
  ⚠️ **Corrección del 2026-09-18**: la primera redacción decía «se resta del encargo», y
  eso era falso — la regla de Leibniz indexada **nunca estuvo** en
  `doc/ENCARGO-FOL-2026-09-17.md`. Nunca llegó a pedirse porque se derivó antes. El
  encargo se actualiza por otra razón: lo que pedía **ya está implementado aquí**.
- ⚠️ Y queda la observación aprovechable para ellos: cuando quieran la propiedad de
  disyunción para su cálculo, `Derives₀.subst` les planteará exactamente el mismo problema,
  y la misma solución sirve.

---

## ADR-024: `HA.ctx` sobre `coreAxioms` — y el eje META pasa de aviso a ERROR

**Fecha**: 2026-09-18
**Estado**: Aceptado

**Contexto**: desde el 2026-09-06, `metaDebtIsError` estaba en `false` y el gate toleraba
con aviso que 10–14 declaraciones heredaran `Classical.choice` de ROBINSON_PlusPlus. La
deuda se daba por inevitable hasta que RPP sanease su nivel meta (`String → List Char`,
paso 4 de su plan §7).

El agente de RPP lo midió punto por punto y **corrigió el diagnóstico**: de los 109
constituyentes de `axioms`, sólo **cinco** arrastran `Classical.choice`
(`ax_vpf_ind`, `ax_vpf_listInd`, `ax_tc_zero`, `ax_tc_succ`, `ax_lineWF_listInd`), la causa
raíz es `strCodeM s := charsCodeM s.toList` (la puerta es `String.toList`), y —lo decisivo—
**`coreAxioms` no depende de ningún axioma**.

**Decisión**: `ctx insts = coreAxioms ++ insts.map inductionFormula`, y
`metaDebtIsError := true`.

**Justificación**: **no es un truco de footprint, es una corrección.** Los cinco axiomas
sucios son axiomas sobre el **verificador object de demostraciones** de RPP. Tenían tan poco
que hacer en el contexto de la Aritmética de Heyting como en el de cualquier otra teoría
aritmética: `ctx` los arrastraba por usar la lista grande, no porque HA los necesitara. HA
es `coreAxioms` más la inducción, y ahora el código lo dice.

**Consecuencias**:
- ⭐ **Deuda META heredada: de 14 declaraciones a CERO.** Todo el proyecto mide
  `⊆ {propext, Quot.sound}`. `PeanoRF.HA.ctx` **no depende de ningún axioma**.
- ⭐ `metaDebtIsError := true`: el eje META deja de avisar y **rompe el build**. Probado
  (ADR-015) con un módulo temporal que usa la lista grande:
  `[gate · EJE META] 1 axioma(s) no-constructivo(s)… [(PeanoRF.HA.smokeDebt, Classical.choice)]`
- ✅ **RPP deja de estar en nuestro camino crítico.** Su migración `String → List Char` —y
  la duda de su §7.5 sobre tener que hacerla dos veces si entra LS ascendente— pasa a ser
  decisión suya por sus razones, no por las nuestras.
- ⚠️ **Cambia la teoría, y hay que decirlo**: `ctx` ya no incluye los axiomas del
  verificador. Para HA eso es lo correcto, pero si algún día PeanoRF quisiera hablar de la
  demostrabilidad object de RPP (H7), habría que volver a meterlos **explícitamente y con su
  coste medido**, no por arrastre.
- 🔑 La lección general: **la deuda que parecía matemática era de empaquetado.** Doce días
  de aviso tolerado se resolvieron cambiando qué lista se importa. Vino de que otro proyecto
  midiera SU puerta en vez de aceptar nuestro diagnóstico de la nuestra.

---

## ADR-025: La barra es relativa a la TEORÍA — y `ha_ctx_slashed` no sale con la barra actual

**Fecha**: 2026-09-18
**Estado**: Aceptado (etapa 1 de H3ter)

**Contexto**: al cerrar H3bis anuncié que la DP **para HA** quedaba «a un lema»,
`ha_ctx_slashed`, porque L2 ya estaba enunciada para contexto arbitrario. **Era falso, y el
error fue mirar la firma de L2 sin mirar qué significaba `Slash` sobre un axioma.**

`Slash` estaba clavada a `[]`: `Slash g` para un axioma de HA significa «derivable desde
nada». Con eso, `ha_ctx_slashed` no es difícil — es **falso**.

Y al parametrizar aparece el obstáculo de verdad: la cláusula `∀` de nuestra barra
cuantifica sobre **todos los términos**. En `coreAxioms` está
`ax19_lt_trichotomy : ∀a∀b (a<b ∨ a=b ∨ b<a)`, y barrarlo exigiría una rama derivable
para cada par de términos — para dos variables libres no hay ninguna, y si la hubiera
`derivesI_soundness` daría el absurdo.

**Decisión** (etapa 1): `Slash T f` toma la teoría como parámetro, y los resultados de
H3bis pasan a ser **instancias `T = []`** de teoremas generales:

```lean
disjunction_property_of_slashed : (∀ g ∈ T, Slash T g) → T ⊢ᵢ A ∨ B → T ⊢ᵢ A ∨ T ⊢ᵢ B
```

**Justificación**: la parametrización es requisito de cualquier variante de H3ter, no tiene
decisión de diseño pendiente, y **conserva H3bis exactamente** (la hipótesis es vacía para
`T = []`). Deja el hito en **una hipótesis con tipo exacto** en vez de en una intuición.

**Consecuencias**:
- ✅ H3bis intacto: `disjunction_property`, `existence_property` y `derivesI_ne_derives0`
  miden lo mismo y dicen lo mismo.
- ⚠️ El caso base de `cut_context` deja de ser la identidad: con `T` arbitraria hace falta
  **debilitar** de `[]` a `T`. Con `T = []` era `id`, y por eso no se veía.
- ⏳ **Etapa 2 pendiente, y con decisión de diseño**: restringir las cláusulas `∀`/`∃` a
  **numerales**, que es la barra de Kleene de verdad. Hacerlo con un parámetro de dominio
  (`Slash T D`) conserva el H3bis actual en toda su fuerza; hacerlo a secas lo debilita a
  sentencias del lenguaje.
- 📏 **Etapa 3, medida**: de los 34 axiomas de `coreAxioms`, **25** tienen matriz atómica
  (barra = derivabilidad, `specI`), ~4 son `⇒`/`⇔` con partes atómicas, y **5** piden
  decidir en el meta y construir la derivación: `ax19_lt_trichotomy`, `ax21_mod2_range`,
  `ax13_lt_def`, `ax_L3_in_concat`, `ax29_sub_witness`. Más el esquema de inducción.
- 🔑 La lección: **una firma que encaja no es un teorema que sale.** L2 aceptaba contexto
  arbitrario, y de ahí concluí que la DP de HA estaba a un lema. Faltaba mirar el
  *significado* del predicado sobre los elementos de ese contexto.

---

## ADR-026: Un control para lo que los otros cinco no miran — la coherencia ENTRE documentos

**Fecha**: 2026-09-18
**Estado**: Aceptado

**Contexto**: el 2026-09-18, tras una pasada de ARMONIZA hecha a mano, los cinco controles
de `check-doc-sync.bash` daban **verde** mientras había tres contradicciones vivas:

* `CURRENT-STATUS-PROJECT.md` se contradecía **a sí mismo** sobre H3ter;
* `PLANNING.md` no tenía el hito **en el roadmap**, con un día de trabajo hecho;
* `NEXT-STEPS.md` conservaba, del plan del 2026-09-06, una sección «H3 ❌ Pendiente» cuyo
  plan incluía «soundness por inducción sobre los constructores de `Derives`» — que
  **ADR-017 declaró imposible**. Doce días de deriva.

Los cinco miran **cifras, catálogo, marcas de tiempo y alcance**: la relación de los
documentos con el **código**. Ninguno mira la relación de los documentos **entre sí**.

**Decisión**: `check-coherencia.bash` + el comando `/armoniza`, con la división **declarada**
entre lo mecanizable y lo que no lo es.

* **[F] REGISTRO DE HITOS — BLOQUEANTE**: todo hito mencionado en el corpus tiene fila en el
  roadmap. Es el control [C] (todo módulo en su catálogo) aplicado a los hitos.
* **[G] ESTADO CONTRA PROSA — AVISO**: un hito ✅ del que la prosa dice «falta», o uno no
  cerrado que la prosa da por hecho.
* **La pasada de LECTURA**, en el comando, con cinco preguntas y su arquetipo real.

**Justificación**: de los tres descuadres, **dos eran mecanizables y uno no**. La tentación
era escribir un script que pareciera cubrirlos todos; eso habría producido exactamente lo
que este proyecto lleva dos días cazando: **un control que da verde sin comprobar**. La
alternativa honesta es cubrir lo que se puede y **declarar en la salida lo que no** — por
eso el script imprime siempre su lista de puntos ciegos.

🔑 **Una afirmación puede ser FALSA sin contradecir a ninguna otra.** Eso lo caza una
lectura, no un grep, y por eso el paso 3 está en el comando y no en la buena voluntad.

**Consecuencias**:
- ⭐ **Cazó un hallazgo real en su PRIMERA ejecución**: la sección H3 de `NEXT-STEPS.md`,
  que llevaba doce días contradiciendo a ADR-017 y que la pasada de lectura de esa misma
  tarde **no había visto**.
- Probado (ADR-015) mencionando en un documento un identificador de hito **sin fila en el
  roadmap**: el control lo caza y sale con 1.
- ⚠️ Y cazó acto seguido **este mismo ADR**, porque la primera redacción escribía el
  identificador de prueba **literalmente**. Reformulado. Es el mismo bucle de calibración de
  siempre: un control recién nacido primero muerde lo que no debe.
- ⚠️ [G] calibrado el mismo día: `DECISIONS.md` queda **fuera** de su barrido, porque un ADR
  narra su contexto histórico por diseño — igual que el CHANGELOG. De 3 avisos, 2 eran ADRs
  contando el pasado. **Un control que grita en falso deja de leerse**, y entonces da igual
  que funcione.
- ⚠️ Queda un falso positivo conocido: la co-ocurrencia en una misma línea
  («H3bis cerrado; siguiente, H4»). Se adjudica a mano; es el precio de que [G] sea aviso.

---

## ADR-027: El dominio de la barra es una CLAUSURA, no una lista de términos

**Fecha**: 2026-09-18
**Estado**: Aceptado

**Contexto**: la barra `Slash T` cuantificaba sus cláusulas de `∀`/`∃` sobre **todos** los
términos. Para H3bis (`T = []`) eso basta, pero para la DP de **HA** no: `ax19_lt_trichotomy`
afirma la tricotomía para todo `x`, `y`, y barrarla exigiría decidir `x < y` para términos de
los que HA no sabe nada. Hacía falta un parámetro de dominio, `Slash T D`.

**Decisión**: `D : Term → Prop`, y en L2 **no se pide que `D` sea nada en concreto**: se pide
una sola propiedad, la **clausura bajo sustitución**

```lean
hDsub : ∀ ρ, (∀ n, D (ρ n)) → ∀ t : Term, D (substT ρ t)
```

**Justificación**: es exactamente lo que los casos `elim_forall` e `intro_ex` necesitan, y
nada más. Fijar `D = ClosedQTerm` dentro de `Slash.lean` habría metido la capa HA dentro de
la capa lógica —y, de paso, `Numerals` se construye DESPUÉS de `Slash`, así que ni se
podía—. Con el parámetro, `Slash.lean` no sabe qué es Q⁺⁺ y **H3bis sobrevive intacto** como
la instancia `D = fun _ => True`, donde la clausura es trivial.

⚠️ **Y la clausura, tal cual, es FALSA para `ClosedQTerm`**: `t` puede llevar símbolos ajenos
o aridades erróneas, y entonces `substT ρ t` también. Eso **no es un defecto del diseño**:
es la misma verdad que midió `junk_probe`, y lo que obliga a la **forma (c)** de L2 — que la
barra se afirme de la instancia COLAPSADA. La versión verdadera,
`closed_collapse_subst : (∀n, D (ρ n)) → ∀ t, D (collapseT LQ (substT ρ t))`, está demostrada
en `HA/Domain.lean`.

**Consecuencias**:
- ✅ H3bis (`disjunction_property`, `existence_property`, `derivesI_ne_derives0`) intacto y
  con el mismo footprint `[propext, Quot.sound]`.
- `existence_property_of_slashed` ahora devuelve **el testigo CON su pertenencia a `D`**;
  `existence_property` la descarta, porque en `D = fun _ => True` no dice nada.
- ⚠️ El dominio obligó a meter la **aridad** en la signatura del colapso (ADR-028).
- ⏳ Falta la forma (c). Hasta que esté, `D = ClosedQTerm` **no se puede instanciar**: la
  hipótesis `hDsub` no se cumple. Queda dicho aquí para que nadie lo lea de más.

---

## ADR-028: La signatura del colapso lleva la ARIDAD

**Fecha**: 2026-09-18
**Estado**: Aceptado

**Contexto**: `collapseT` tomaba `L : String → Bool` — sólo el **nombre** del símbolo.

**Decisión**: `L : String → Nat → Bool`, aplicado a `ts.length`.

**Justificación**: medido, no argumentado. `Term.func add_sym [zero]` —`+` con UN
argumento— es un término legítimo de la sintaxis, es cerrado y lleva sólo símbolos de Q⁺⁺,
pero **no es un `ClosedQTerm`**: sus constructores fijan la aridad. Y con razón, porque Q⁺⁺
**no tiene ningún axioma sobre él** y por tanto no es demostrablemente igual a ningún
numeral — que es lo único que la etapa 3 le pide al dominio. El colapso anterior lo dejaba
pasar intacto.

El contraejemplo vive en **producción** (`HA.not_closed_add_unary`), no en el cuaderno de
sondeos, porque es lo que justifica el diseño.

**Consecuencias**:
- Precio **medido**: tres lemas de longitud (`collapseTs_length`, `liftTerms_length`,
  `substTerms_length`) más `substTs_length` en `Subst.lean`. Las conmutaciones **no cambian
  de forma** y `derivesI_collapse` conserva su `[propext, Quot.sound]`.
- ⚠️ Una signatura sin aridad es un control que **da verde sin comprobar** aplicado a la
  sintaxis: deja pasar lo que dice filtrar. Misma familia que
  [[feedback-polaridad-de-los-controles]].

---

## ADR-029: La FORMA (c) — L2 barra la instancia COLAPSADA

**Fecha**: 2026-09-18
**Estado**: Aceptado

**Contexto**: con `Slash T D` (ADR-027), el caso `elim_forall` de L2 pedía `D (substT ρ t)`
para un `t` **arbitrario**. Con `D = ClosedQTerm` eso es **falso**: si `t` lleva un símbolo
ajeno, `substT ρ t` también. Y `derivesI_collapse` **no lo arregla por sí solo**, porque
actúa sobre derivaciones enteras y L2 por dentro no sabe que la derivación venga colapsada.

Tres formas se consideraron, y se **midieron** antes de escribir nada
(`sondeos/collapse_parallel_probe.lean`):

| | qué exige | veredicto |
|---|---|---|
| (a) `D = ClosedQTerm` + L2 restringida a derivaciones limpias | un cálculo `DerivesL` indexado — **hipotético, descartado, nunca existió** | ⛔ la ruta cara |
| (b) `D` cerrado bajo `substT ρ` para `t` arbitrario | `D` ⊇ todos los términos sin variables | ⛔ `ax19` vuelve a fallar |
| (c) que L2 barre la instancia **colapsada** | una conmutación más | ⭐ la buena |

**Decisión**: (c).

```lean
slash_of_derives : Γ ⊢ᵢ f → ∀ ρ, (…) → Slash T D (collapseF L (substF ρ f))
```

con dos hipótesis sobre el dominio: `hDfix` (el colapso lo fija) y `hDsub` (el colapso de
`substT ρ t` cae en él). **Las dos están demostradas en `HA/Domain.lean` y encajan sin
adaptador ninguno.**

**Justificación**: el colapso viaja dentro de la inducción, así que todo se queda en el
lenguaje solo, y arriba no se pierde nada porque para una sentencia del lenguaje el colapso
y la sustitución son la identidad. ⭐ **Y H3bis no se debilita**: con `L` total el colapso es
la identidad (`collapseF_trivial`) y con `D` total la clausura es trivial, así que
`disjunction_property` sale con el enunciado LITERAL de antes.

**Consecuencias**:
- 🏁 `qDisjunctionProperty` y `qExistenceProperty`: la DP y la EP para **cualquier
  teoría de Q⁺⁺ cuyos axiomas estén barrados**. `[propext, Quot.sound]`.
  ⚠️ **Enmienda del 2026-09-21**: cuando se escribió este ADR el segundo se llamaba
  `qExistenceProperty_numeral` — RETIRADO, ya no existe — y daba el testigo **igual a un
  numeral**. Al rehacer el
  dominio sobre `Grounded LQpp` —trece símbolos, no cinco— el testigo pasó a estar
  **anclado**, que es más débil, y aquel teorema se retiró. La cláusula del numeral vuelve
  cuando esté `hNum`.
- La hipótesis «`A ∨ B` es una sentencia del lenguaje» va como **una sola ecuación**,
  `collapseF LQ (substF zeroS (A ∨ B)) = A ∨ B`. Comprobado que **no es vacía**.
- El caso `rewrite_at` obligó a una pieza más: `collapseF_substF`, la conmutación con la
  sustitución **paralela**, porque `slash_rewrite` está enunciada sobre `substF`.
- ⏳ Queda sólo la etapa 3: `hT` para los 34 axiomas de `coreAxioms`.

---

## ADR-030: La marca de tiempo tiene que ser CIERTA, no sólo estar

**Fecha**: 2026-09-19
**Estado**: Aceptado

**Contexto**: en la pasada de ARMONIZA del 2026-09-19, con `check-doc-sync.bash` y
`check-coherencia.bash` **los dos en verde**, la lectura encontró **seis documentos con la
fecha falsa**:

| | dice | último cambio commiteado |
|---|---|---|
| `REFERENCE.md` | 2026-09-16 | 2026-09-18 |
| `PLANNING.md` | 2026-09-16 | 2026-09-18 |
| `CURRENT-STATUS-PROJECT.md` | 2026-09-17 | 2026-09-18 |
| `NEXT-STEPS.md` | 2026-09-17 | 2026-09-18 |
| `DECISIONS.md` | **2026-09-06** | 2026-09-18 |
| `AI-GUIDE.md` | **2026-09-06** | 2026-09-18 |

El de `DECISIONS.md` es el que duele: **trece días de desfase con cuatro ADR nuevos dentro**
(026 a 029). El control [D] daba ✓ porque comprobaba que la marca **existiera**.

**Decisión**: [D] compara la marca con `git log -1 --format=%ad --date=short -- <fichero>` y
**rompe** si la marca es anterior. Y amplía su lista a `PLANNING.md`, `NEXT-STEPS.md`,
`DECISIONS.md` y `AI-GUIDE.md`, que no estaban.

**Justificación**: 🔑 es **la cuarta forma de dar verde sin comprobar**, y la más sutil de
las cuatro ([[feedback-polaridad-de-los-controles]]): las otras tres callan (lista de
prohibidos incompleta), fijan la respuesta a mano (forma de tipo clavada) o no pueden medir
(`lake` fuera del PATH). Ésta **mira, pero mira la FORMA en vez del CONTENIDO**. Un fichero
con marca de tiempo mentirosa es peor que uno sin marca: el segundo se nota.

**Consecuencias**:
- ✅ Probado (ADR-015) contra la realidad del día: sacó los seis a la primera ejecución.
- ⚠️ Lo caza **un commit tarde**: compara contra el último cambio *commiteado*, no contra el
  árbol de trabajo. Se eligió así a propósito — el `mtime` en Windows + Dropbox es ruido.
- 🚨 **ENMIENDA del 2026-09-21: `git log` MIENTE en un checkout SHALLOW.** Con profundidad
  1 git atribuye CUALQUIER fichero a HEAD, así que todo documento cuya marca sea anterior al
  último push da falso positivo. **La CI se puso en rojo el mismo día** con `DEPENDENCIES.md`,
  que el commit ni siquiera tocaba — y la sesión se cerró diciendo «verde» sin mirarla. Cura,
  las **dos** cosas: `fetch-depth: 0` en el workflow **y** una guarda
  `git rev-parse --is-shallow-repository` que pone `[D]` en ROJO si falta, porque una sola se
  puede deshacer sin que nadie lo note. Probada contra un clon `--depth 1` real.
  🔑 Arreglé un control que miraba la FORMA en vez del CONTENIDO y lo sustituí por uno que
  es cierto en local y miente en remoto. **Un control nuevo no está probado hasta que se ha
  visto correr donde va a correr.**
- ⚠️ En la misma pasada se relajó la redacción de la fila de H3ter en `PLANNING.md` para
  quitar un `✅` interior que hacía gritar en falso a [G]. **Un control que grita en falso
  deja de leerse** (ADR-026).

---

## ADR-031: El telescopio del gate reconoce la sintaxis GENÉRICA — y la CI deja de correr `--quick`

**Fecha**: 2026-09-21
**Estado**: Aceptado

**Contexto**: auditoría externa de FOL/ROB++/Peano. FOL generizó su sintaxis por el símbolo
(sus ADR-069/071) y `Derives₀` pasó a ser

```lean
inductive Derives₀ {Sym : Type} : List (FormulaG Sym) → FormulaG Sym → Prop
```

El parámetro va IMPLÍCITO, así que la notación `⊢₀` sigue valiendo y **PeanoRF compiló sin
enterarse**. Pero el criterio POR TELESCOPIO de `AxiomCheck.lean` miraba la **constante
`Formula`**, y `FormulaG Sym` no lo es. Medido:

| | 2026-09-18 | 2026-09-21 (antes del arreglo) |
|---|---|---|
| relaciones vigiladas | 6 | 6, **pero sin `Derives₀`** |
| constructores ajenos | **45** | **42** |
| de ellos CLÁSICOS | **12** | **9** |

⛔ Y `mentionsFormula` fallaba por lo mismo, así que `Derives₀` **ni siquiera salía como
casi-candidato**: la red de seguridad que existe «para que el hueco se VEA» estaba agujereada
por la misma causa. `Derives₀` es el cálculo contra el que se define la tesis
(`derivesI_ne_derives0`) y el que el propio docstring del gate nombra como una de las reglas
que este gate existe para vigilar.

**Decisión**:
1. `isFormulaLike t := t.isConstOf `Formula || t.isAppOfArity `FormulaG 1`, usado en
   `isObjectArgType` y en `mentionsFormula`.
2. El telescopio **atraviesa los binders cuyo tipo es un sort** (`{Sym : Type}`): no son
   argumentos del lenguaje objeto, son su parametrización.
3. **La CI deja de correr `check-doc-sync.bash --quick`**. Con `--quick` el script se salta
   `[A] jobs` y `[E] alcance del gate` — y lo dice, pero **decirlo no es comprobarlo**.
   `[E]` es justo el control que caza que el gate se haya quedado ciego.

**Justificación**: es la **tercera reincidencia** del mismo patrón
([[feedback-polaridad-de-los-controles]]), ahora por **generización aguas arriba**. Las dos
anteriores fueron listas por nombre y forma de tipo fijada a mano; ésta es una forma de tipo
que dejó de ser la vigente porque el vecino la cambió debajo.

**Consecuencias**:
- ✅ Cifras restauradas **exactamente** a las de antes de la generización: 7 relaciones,
  **45 constructores, 12 clásicos**. Que coincidan al dígito es lo que prueba que el arreglo
  repone la cobertura y no inventa nada.
- ✅ **Probado** (ADR-015) con un teorema que usa `Derives₀.dne_rule`: el gate lo caza como
  `OBJETO` y rompe el build. Revertido.
- ✅ Comprobado antes de quitar `--quick`: el segundo `lake build` sale del caché y Lean
  **reproduce los `logInfo`**, así que `[E]` mide igual. No cuesta tiempo.
- ⚠️ **No hubo brecha**: PeanoRF usa 18 constructores de `Derives₀`, ninguno clásico. Lo que
  estuvo apagado tres días fue la guardia, no la tesis.
- ⏳ Riesgo vivo: FOL seguirá generizando (`Derives₁`, `Derives₂`, `LK*`). El criterio ya los
  cubre, pero **el que hay que mirar en cada auditoría es el CONTADOR**, no el verde.

---

## ADR-032: `[H]` — declarado y sin uso, la dirección que faltaba

**Fecha**: 2026-09-21
**Estado**: Aceptado

**Contexto**: `[B]` caza un símbolo **citado en la prosa que no existe en el árbol**. La
dirección contraria —**existe en el árbol y nadie lo usa**— no la miraba ningún control, y
por ahí se coló la capa `LQ` de `HA/Domain.lean`: ~130 líneas que tras rediseñar el dominio
sobre `Grounded LQpp` sólo se usaban **entre sí**. Hizo falta una auditoría a mano, y lo que
una auditoría a mano encuentra una vez lo vuelve a perder la siguiente.

**Decisión**: control `[H]`, con la polaridad puesta donde importa. No pregunta «¿está esto
muerto?» —eso no se puede decidir— sino **«¿está usado O ETIQUETADO?»**. Hay tres razones
legítimas para que algo no se use, y las tres se **declaran**:

| | qué significa | ejemplo |
|---|---|---|
| 🏁 `ENTREGABLE` | es un RESULTADO, no una pieza | `derivesI_ne_derives0`, `succ_add` |
| 🏗️ `ANDAMIO` | sin uso hoy, con destino escrito | `closed_term_eq_numeral` (espera a `hNum`) |
| ⛔ `EVIDENCIA` | sostiene una decisión de diseño | `not_closed_add_unary` (ADR-028) |

Es **AVISO**, no objetivo, por la regla de ADR-026: un control que grita en falso deja de
leerse. Y se excluyen los `@[simp]` y las instancias, que **se usan sin nombrarse** y por
tanto no se pueden medir así.

**Justificación**: código sin uso y **sin etiqueta** se lee como código en uso. El silencio
vuelve a significar SOSPECHOSO, que es la polaridad de todo este proyecto.

**Consecuencias**:
- ✅ Siete hallazgos en su primera ejecución, **todos legítimos y ninguno basura**: cuatro
  entregables que nadie usa porque son resultados, y tres andamios. Todos etiquetados.
- ✅ **Probado en las dos direcciones a la vez** (ADR-015): con un teorema sin marcador
  —lo caza— y otro con él —lo exime—, en la misma pasada.
- ⚠️ Delató que **`closed_term_eq_numeral` se quedó sin consumidor** el 2026-09-18, cuando
  se retiró `qExistenceProperty_numeral`. Nadie lo había notado.
- 🚨 **Y destapó una trampa del entorno**: ver abajo.

---

## ADR-033: `grep` falla en SILENCIO con los emoji de 4 bytes

**Fecha**: 2026-09-21
**Estado**: Aceptado

**Contexto**: el marcador de `[H]` no eximía a `existence_property`, que lleva un `🏁` en su
docstring. Medido:

| | bytes | `grep` | `LC_ALL=C grep` |
|---|---|---|---|
| `✅` `⏳` `⛔` | 3 | ✓ | ✓ |
| `🏁` `🏗` `🗑` `🔶` | 4 | **✗** | ✓ |

Bajo `es_ES.UTF-8`, el `grep` de este entorno casa los emoji del plano básico y **falla sin
decir nada** con los del plano astral. Un patrón que no casa nunca es una **alternativa
muerta dentro de una alternancia**, y nadie se entera: el control sigue dando verde.

**Decisión**: `LC_ALL=C grep` en los tres sitios donde un control compara contra marcadores:
`[H]` (`UNUSED_MARKERS`), `[B]` (`DEAD_MARKER`, que lleva `🗑`) y `[G]` de
`check-coherencia.bash` (que hoy usa `✅`, de 3 bytes, y funciona — pero el día que alguien
marque el roadmap con `🏁` el control se invierte sin avisar).

**Justificación**: es **la quinta forma de dar verde sin comprobar**, y no es del código sino
del ENTORNO. No basta con escribir bien el control: hay que comprobar que la herramienta con
la que se escribe hace lo que uno cree. Familia de «`σ` no es un identificador válido» y de
«`∧` está tomada por `FormulaG`»: el error no se parece a su causa, aquí porque **no hay
error**.

**Consecuencias**:
- ⚠️ `[B]` llevaba desde su nacimiento con `🗑` como alternativa muerta en `DEAD_MARKER`.
  Impacto bajo —hay diez alternativas más— pero era un agujero silencioso.
- ✅ Preferir **palabras ASCII** (`ANDAMIO`, `EVIDENCIA`, `ENTREGABLE`) como marcador
  primario, y el emoji como adorno legible. Un marcador que hay que reconocer por su glifo
  es un marcador frágil.

---

## ADR-034: `hInd` cae por HARROP — y lo que el atajo NO cubre

**Fecha**: 2026-09-21
**Estado**: Aceptado

**Contexto**: de las cinco hipótesis de `haDisjunctionProperty_core`, dos eran mecánicas
(`hInd`, `hlift`) y tres de fondo (`hcon`, `hNum`, `hIn`).

**Medición**: `inductionFormula φ` es `φ[0] ⇒ ((∀(φ ⇒ φ[σ])) ⇒ ∀φ)`. En la clase de Harrop
el **antecedente de `⇒` da igual** y el consecuente final es `∀φ`, luego

```lean
theorem isHarrop_inductionFormula (φ : Formula) :
    isHarrop (inductionFormula φ) = isHarrop φ := rfl
```

— por iota, **sin depender de ningún axioma**. Comprobado además por `#eval` en las dos
direcciones: `(true, true)` para una instancia atómica y `(false, false)` para una con `∨`.

**Decisión**: `slash_inductions` descarga `hInd` para instancias de Harrop con
`slash_of_isHarrop`, **sólo con la consistencia**. Y `inductions_lift` + `ctx_lift` descargan
`hlift`. Las dos se reducen a una condición **por instancia** que para una instancia concreta
es `rfl`.

**⛔ Lo que el atajo NO cubre, y va dicho en el módulo**: vale para instancias **de Harrop**.
Una instancia con `∨` o `∃` —que es lo interesante de la inducción en HA— **no** es de
Harrop, y ahí no hay atajo. Lo que cae barato es el esquema para las instancias que hoy
existen, no el esquema en general.

**Consecuencias**:
- 🏁 `haDisjunctionProperty_harrop`: la DP de HA con `hInd` y `hlift` descargadas. Quedan
  **tres**, y las tres son de fondo.
- ✅ **Y NO es vacuo, medido**: `haDisjunctionProperty_zeroAdd` lo instancia con `phiZeroAdd`
  —`0 + x = x`, la instancia que el proyecto usa de verdad— y **las tres condiciones por
  instancia salen por `rfl`**. Un teorema con hipótesis insatisfacibles es cierto y hueco;
  éste tiene testigo.
- ⏳ Lo que queda: `hcon` (Gödel, permanente), `hNum` (evaluar 8 de los 13 símbolos sobre
  numerales) y `hIn` (pide inducción sobre listas).

---

## ADR-035: `hNum` es INALCANZABLE sobre el lenguaje completo — y el fragmento donde sí sale

**Fecha**: 2026-09-21
**Estado**: Aceptado

**Contexto**: tras descargar `hInd` y `hlift` (ADR-034) quedaban tres hipótesis. Antes de
atacar `hNum` —«todo término anclado es demostrablemente igual a un numeral»— se midió qué
determina de verdad Q⁺⁺ sobre los ocho símbolos no aritméticos.

**⛔ Y no es alcanzable. Para `−` es directamente FALSA**:

> `−` aparece **en UN único axioma de los 34** (`ax29_sub_witness`), condicionado a `x ≤ y`:
> `∀x∀y. (x ≤ y) ⇒ (x + (y − x) = y)`.

Q⁺⁺ **no dice nada** de `5̄ − 7̄`. Ningún numeral es demostrablemente igual a ese término, y
no por falta de ingenio: **por falta de axioma**. Los otros siete (`√`, `/₂`, `%₂`, `::`,
`##`, `Π_p`, `τ`) están caracterizados por desigualdades, ecuaciones condicionadas o
recursiones sobre la estructura de lista, y evaluarlos pide **inducción en el objeto** — que
además no sería de Harrop, así que el atajo de ADR-034 tampoco valdría.

**⛔ Y no se arregla encogiendo el dominio**: `L` tiene que FIJAR los axiomas (si no, `hT` es
insatisfacible y el teorema sale cierto y vacío, ADR-029), y `D` tiene que contener todos los
términos cerrados de `L`. Con 34 axiomas, `L` son 13 símbolos y `D` los incluye todos.

**Decisión**: encoger **la TEORÍA**, no el dominio. `arithAxioms` (`HA/Fragment.lean`), los
**17 de los 34** cuyos símbolos de función son sólo `0 σ + * ^`. Medido, no elegido:

| | cómo se comprueba |
|---|---|
| son **17** | `arithAxioms_length`, `rfl` |
| son **sentencias del lenguaje de los numerales** | `arithAxioms_sentences`, `rfl` |
| sólo **dos** no son de Harrop: `ax13` y `ax19` | `arithAxioms_hard`, `rfl` |

**Justificación**: sobre ese fragmento todo encaja y **ya está hecho**:
- `hNum` **es `closed_term_eq_numeral`**, que habla exactamente de esos cinco símbolos;
- los dos axiomas duros que quedan **ya están barrados** (`slash_ax13`, `slash_ax19`);
- **`hIn` desaparece**: los dos axiomas que la pedían no son aritméticos. El único que
  menciona `∈` es `ax_L1_in_nil` — y es de Harrop, porque `nil` **es** `zero`.

⇒ **Sobre el fragmento queda UNA sola hipótesis: `hcon`.**

⭐ Y cierra un círculo: la capa `LQ`, etiquetada como ANDAMIO el 2026-09-21 por no tener uso
portante, **es la signatura de este fragmento**. El andamio era el camino.

**Consecuencias**:
- ⚠️ La DP para **HA completa** queda condicionada a `hNum`/`hIn`, y ahora se sabe que no es
  cuestión de trabajo: **el fragmento es el techo de este método sobre Q⁺⁺**.
- ⏳ Falta construir la DP del fragmento. Pide parametrizar por el contexto lo que hoy está
  clavado a `ctx` (`numeralI_add/mul/pow`, `closed_term_eq_numeral`, `numeralI_ne/lt/not_lt`),
  igual que ya lo está la familia `addI_*`.
- ⛔⛔ **RECTIFICADO el 2026-09-21 por ADR-039.** Aquí se escribió que `hcon` «no es una
  deuda, es el precio, y es demostrable que no se puede pagar por dentro — Gödel II lo
  dice», y de ahí se dedujo que se quedaba **para siempre**. **La deducción es falsa.**
  Gödel II dice que HA no prueba su PROPIA consistencia, no que no la pruebe nadie: un
  modelo estándar sobre `ℕ` la descarga, y `hcon_fragment` lo hace. Lo único que se
  sostiene de aquel párrafo es que el pago **no puede venir del propio cálculo**, sino de
  la semántica. ⚠️ La reserva sí sigue viva: el Gödel de ROB++ será sobre `⊢`/`axioms`,
  no sobre `⊢ᵢ`/`arithAxioms`, y transportarlo no es automático.

---

## ADR-036: la DP del FRAGMENTO ARITMÉTICO, con una sola hipótesis

**Fecha**: 2026-09-21
**Estado**: Aceptado

**Contexto**: ADR-035 midió que `hNum` sobre los trece símbolos es inalcanzable, y señaló el
fragmento aritmético (17 de los 34 axiomas) como el techo real del método. Faltaba
construirlo.

**Decisión**: `ctxA insts := arithAxioms ++ insts.map inductionFormula`, con dominio
`Grounded LQ`, y **generalizar por CONTEXTO** lo que estaba clavado a `ctx`:

| antes | ahora |
|---|---|
| `numeralI_add/mul/pow`, `closed_term_eq_numeral` sobre `ctx []` | `{Γ}` + `hΓ : ∀ g ∈ arithAxioms, Γ ⊢ᵢ g` |
| `numeralI_ne/lt/not_lt` sobre `ctx insts` | idem |
| `slash_ax13`, `slash_ax19` sobre `ctx insts` y `LQpp` | `{Γ}` + `(L)` + `hΓ` |
| `grounded_numeralM` clavado a `LQpp` | `(L) (hs : L succ_sym 1 = true)` |

⭐ La familia `hΓ` pasó de `coreAxioms` a `arithAxioms` **sin tocar una sola cadena de
pertenencia**: los índices 0–11 coinciden en las dos listas. Eso no es suerte, es que
`coreAxioms` empieza por el núcleo aritmético.

**La pieza que faltaba**: `closed_of_grounded : Grounded LQ t → ClosedQTerm t`. `Grounded` y
`ClosedQTerm` describen lo mismo desde dos lados —por CLAUSURAS y por CONSTRUCTORES— y esta
dirección convierte `closed_term_eq_numeral` en `hNum`.

**Resultado**:

```lean
qDisjunctionProperty_arith : ¬(ctxA [] ⊢ᵢ ⊥) →
  collapseF LQ (substF zeroS (A ∨ B)) = A ∨ B →
  ctxA [] ⊢ᵢ A ∨ B → (ctxA [] ⊢ᵢ A) ∨ (ctxA [] ⊢ᵢ B)
```

**UNA sola hipótesis de fondo: la consistencia** —⛔ y desde ADR-039 **ninguna**, porque
`hcon_fragment` la descarga con un modelo estándar—. `hNum` dejó de serlo y es `hNum_fragment`;
`hIn` no aparece; `hInd` es vacía y `hlift` sale por `rfl`. Todo en `[propext, Quot.sound]`.

**Consecuencias**:
- 🏁 Es el teorema al que llevaba H3ter, con el alcance que la medición permite y no el que
  se había anunciado. La DP para HA **completa** sigue condicionada, y ADR-035 dice por qué
  no es cuestión de trabajo.
- ⭐ La generalización por contexto es mejora en sí: los lemas valen ahora en `ctx`, en `ctxA`
  y en cualquier contexto que satisfaga el fragmento — incluidos los **extendidos** que
  aparecen dentro de `elim_ex`.
- ⚠️ `ctx_weaken` quedó sin uso al desaparecer la necesidad de debilitar desde `ctx []`.
  Etiquetado como ANDAMIO; `[H]` lo habría cazado de no hacerlo.
- 🔑 Y una de método: `injection h with a b` **cierra la meta** cuando la ecuación resultante
  es la meta. El `exact` que venía detrás daba «No goals to be solved», que no se parece a
  su causa.

---

## ADR-037: el fragmento NO es maximal — `τ` entra, y el mapa de por qué los demás no

**Fecha**: 2026-09-21
**Estado**: Aceptado

**Contexto**: ADR-035 fijó el fragmento aritmético (17 axiomas, 5 símbolos) como «el techo
real del método». **Eso era demasiado grueso**, y medirlo lo dejó claro.

**Medición**, símbolo a símbolo:

| | axiomas | ¿de Harrop? | ¿determina el numeral? |
|---|---|---|---|
| `τ` | `ax25 : τ 0 = 0`, `ax26 : ∀n. τ(σn) = n` | ✅ los dos | ✅ **sin inducción ninguna** |
| `%₂` | ax16, ax21, ax24 | ✅ ax16, ax24; ⛔ ax21 | ✅ con inducción **meta** + consistencia |
| `/₂` | ax17 | ✅ | ⛔ pide cancelación de `+` y `·` |
| `√` | ax14, ax15 (desigualdades) | ⛔ ax14 | ⛔ habría que casar sobre `√n̄`, que es un término |
| `::` | ax_L0 | ✅ | ⛔ **`pair` usa `/₂`** (medido) |
| `##`, `Π_p` | recursión sobre lista | ✅ | ⛔ pide saber si un numeral es `nil` o `cons` |
| `−` | **ax29, y sólo ése**, con `x ≤ y` | ✅ | ⛔ la teoría **calla** fuera de `x ≤ y` |

**Decisión**: añadir `τ`. `LQt`, `arithTAxioms` (19), `ctxT`, y
`qDisjunctionProperty_arithT` con **la misma única hipótesis**.

**Justificación**: `τ` es el caso límpio de lo que el método puede: sus dos axiomas son una
**recursión primitiva completa** —base y paso—, así que `τ n̄` se evalúa por un caso del
meta, no por inducción. `numeralI_pred` mide **`[propext]`**, sin `Quot.sound` siquiera.

🔑 **El criterio que sale de aquí, y es lo reutilizable**: un símbolo entra si sus axiomas
lo definen por **recursión sobre el constructor** (`0` / `σ`). `τ` y `%₂` lo hacen; `/₂`, `√`
y `−` están **caracterizados por propiedades**, no definidos por recursión, y de una
caracterización no se despeja sin inducción en el objeto.

**Consecuencias**:
- ✅ 19 axiomas, 6 símbolos, y `arithTAxioms_hard` mide que **añadir `τ` no añade dureza**.
- ⏳ `%₂` es el siguiente, y llevaría a 22 de 34.
- ⚠️ **Tres de las casillas ⛔ son ARGUMENTOS, no mediciones**: que `−` esté subdeterminado
  pide separar dos modelos; que `√` y `/₂` no se dejen pide un teorema de imposibilidad.
  Queda escrito como deuda, igual que la no-derivabilidad del contraejemplo de `junk_probe`.
  ✅ **La de `−` está PAGADA** desde el 2026-09-21 (ADR-039): `sub_neither` la mide, y no
  con dos modelos sueltos sino con **uno parametrizado**. Quedan `√` y `/₂`.
- ⛔⛔ **REFUTADO también para `::` el 2026-09-22 (ADR-044)**, y **por corolario del
  anterior**: el bloqueo de `::` era «`pair` usa `/₂`», o sea una DEPENDENCIA, no una
  propiedad suya. Al caer `/₂` cayó con él.
- ⛔⛔ **REFUTADO para `/₂` el 2026-09-22 (ADR-042)**: la razón que da esta tabla —«pide
  cancelación de `+` y `·`»— es falsa, y `/₂` está **en el fragmento** desde entonces
  (`numeralI_div2`). El criterio de este ADR resulta **suficiente pero no necesario**.
- 🚨 **Y sobre esas dos, el 2026-09-22 apareció contraevidencia MEDIDA** —ver
  `sondeos/sqrt_div2_probe.lean`—. El ⛔ de `/₂` decía «pide cancelación de `+` y `·`»; la
  cancelación **no hace falta**, porque la caracterización se despeja **por el ORDEN**: la
  tricotomía contra el numeral candidato más monotonía de la suma, que sale de `ax13` sin
  inducción. Y la pieza que se daba por ausente —«todo `x` es `0` o sucesor», que Robinson
  Q **postula** y `coreAxioms` no tiene— **se DERIVA**: `zeroI_or_succ`, en
  `[propext, Quot.sound]`. ⏳ El veredicto de las dos casillas queda **abierto hasta
  terminar la cadena**; lo que ya no se sostiene es la razón que se dio.
  â **La de `−` estÃ¡ PAGADA** desde el 2026-09-21 (ADR-039): `sub_neither` la mide, y no
  con dos modelos sueltos sino con **uno parametrizado**. Quedan `√` y `/₂`.

---

## ADR-038: `%₂` entra — 22 de 34, y el criterio de ADR-037 confirmado

**Fecha**: 2026-09-21
**Estado**: Aceptado

**Contexto**: ADR-037 fijó el criterio —un símbolo entra si sus axiomas lo **definen por
recursión sobre el constructor**— y predijo que `%₂` entraría. Construido.

**Cómo entra `%₂`**, que cuesta un poco más verlo que `τ`:

* **base**: `ax24 : ∀x∀y. (x = 2·y) ⇒ (%₂x = 0)` instanciada en `(0,0)`, con `0 = 2·0` vía
  `ax8`;
* **paso `0 → 1`**: la dirección `⇒` de `ax16 : ∀x. (%₂x = 0) ⇔ (%₂(σx) = 1)`;
* **paso `1 → 0`**: `ax16` **no lo da**. Se saca de `ax21` (la disyunción) **refutando** la
  otra rama con `numeralI_ne`.

⭐ **Y la refutación va DENTRO de una rama de `elim_or`, bajo hipótesis** — así que
`numeralI_mod2` **no necesita la consistencia**. Es el mismo patrón de `ax_L2_in_cons`:
cuando una de las ramas se puede refutar localmente, la disyunción del objeto entrega la
otra sin pagar `hcon`. La consistencia sí la necesita `slash_ax21`, que es otra cosa.

**Resultado**: `LQtm` (7 símbolos), `arithTMAxioms` (22), `qDisjunctionProperty_arithTM`.
`arithTMAxioms_hard` mide que `%₂` añade **un** duro, `ax21`, **y ya estaba barrado**.

**Consecuencias**:
- 🏁 **22 de los 34**, con la misma única hipótesis de fondo —⛔ y desde ADR-039, **con
  ninguna**: `hcon_fragment` la descarga.
- ✅ El criterio de ADR-037 queda **confirmado por una segunda instancia**, no sólo
  enunciado.
- ⏳ Los cinco que faltan (`/₂`, `√`, `::`, `##`, `Π_p`, `−`) están **caracterizados**, no
  definidos por recursión. Ahí el método se para, y ADR-037 dice por qué.

---

## ADR-039: un MODELO estándar ⇒ `hcon` DESCARGADA, y `−` MEDIDO

**Fecha**: 2026-09-21
**Estado**: Aceptado. ⚠️ **Rectifica ADR-035 y ADR-036**, y **paga una de las tres deudas
de ADR-037**.

**Contexto**: ADR-035 y ADR-036 escribieron que la consistencia del fragmento «no es una
deuda, es el precio, y es demostrable que no se puede pagar por dentro — Gödel II lo dice»,
y de ahí concluyeron que `hcon` **se quedaba como hipótesis para siempre**. NEXT-STEPS lo
repitió en su tabla, `Fragment.lean` en su encabezado, y la memoria en su índice.

⛔ **La conclusión no se seguía.** Gödel II dice que HA no prueba su **propia**
consistencia. No dice que no la pruebe nadie: se demuestra en cualquier metalenguaje que
exceda la teoría, y Lean la excede de sobra. Se confundió «no demostrable DENTRO» con «no
demostrable». Lo que sí se sostiene de aquella frase —y es lo que hay que conservar— es que
**el pago no puede venir de una derivación del propio cálculo**: tiene que venir de la
semántica.

⭐ Y el patrón ya estaba en el árbol un piso más abajo desde H3: `derivesI_consistent`
descarga la consistencia de la **lógica** exhibiendo un modelo de un punto. No se vio que
subía.

**Decisión**: `PeanoRF/HA/Model.lean`. Un **único** modelo con un parámetro:

```lean
def natModelK (k : Nat) : Model Nat where
  func s ds := if s = succ_sym then ds.headD 0 + 1 else … else if s = sub_sym then
    (if ds.tail.headD 0 ≤ ds.headD 0 then ds.headD 0 - ds.tail.headD 0 else k) else 0
  rel s ds := And (s = lt_sym) (ds.headD 0 < ds.tail.headD 0)
```

`natModelK_sat` verifica los **23** axiomas —los 22 de `arithTMAxioms` más
`ax29_sub_witness`— **para todo `k`**. El parámetro hace dos trabajos de golpe:

| con `k` fijo | `hcon_fragment` ⇒ **`qDisjunctionProperty_arithTM_final`, sin hipótesis** |
|---|---|
| **variando `k`** | `sub_neither` ⇒ **`5̄ − 7̄` es indeterminado**, y `hNum_false_on_sub` |

**Justificación**: la segunda mitad es la que no se veía venir. ADR-037 dejó **tres
casillas ⛔ que eran ARGUMENTOS y no mediciones**, y una era `−`. La forma de medirla —dos
modelos que sólo difieren en `sub` fuera del rango— resultó ser **el mismo modelo** que
descarga `hcon`, porque el axioma `ax29_sub_witness` condiciona `−` a `x ≤ y` y deja el
resto libre: *el valor de `5̄ − 7̄` en el modelo **es** el parámetro*.

⇒ `sub_neither n` da las **dos** direcciones: la teoría no demuestra `5̄ − 7̄ = n̄` (falla en
`k = n+1`) **ni** su negación (falla en `k = n`). Eso es «indeterminado» en el sentido
fuerte, y está medido.

**Resultado**, todo en `[propext, Quot.sound]`:

```lean
hcon_fragment                        : ¬(ctxTM [] ⊢ᵢ ⊥)
qDisjunctionProperty_arithTM_final   : ctxTM [] ⊢ᵢ A ∨ B → (ctxTM [] ⊢ᵢ A) ∨ (ctxTM [] ⊢ᵢ B)
sub_neither (n)                      : ¬(subAxioms ⊢ᵢ 5̄−7̄ = n̄) ∧ ¬(subAxioms ⊢ᵢ ¬(5̄−7̄ = n̄))
hNum_false_on_sub                    : ¬(∀ t, Grounded LQpp t → ∃ n, subAxioms ⊢ᵢ t = n̄)
```

**Consecuencias**:
- 🏁🏁🏁 **La DP del fragmento aritmético de Q⁺⁺ es un teorema INCONDICIONAL.** 22 de los
  34 axiomas de `coreAxioms`, siete símbolos, **cero hipótesis**.
- ⛔ **El alcance de la medición de `−` es `subAxioms` (23), no `coreAxioms` (34).** Subirlo
  pide un modelo de `coreAxioms` entero —listas, pares de Cantor, `√`, `Π_p`—, que este
  proyecto no tiene. Queda **dicho**, no supuesto. Es exactamente el error que ADR-037
  cometió y este ADR no repite.
- ⏳ De las tres casillas de ADR-037 quedan **dos**: `√` y `/₂`. Y el camino está claro —un
  modelo que las mueva—, sólo que ninguna de las dos es libre como `−`: sus axiomas son
  desigualdades que sí acotan.
- 🔑 **De método, y es lo reutilizable**: «la teoría no dice nada de `t`» se mide
  **parametrizando el modelo por el valor de `t`**, no exhibiendo dos modelos sueltos. Un
  parámetro es más fuerte y más corto que un par.
- ⚠️ `omega` aparece en cinco metas y **todas son aritméticas** (`<`, `≤`, `+`, `%`): el
  footprint se midió y sale `[propext, Quot.sound]`. No es el caso de
  `shift_updateEnv_comm`, donde `omega` cerraba por contradicción una meta que no era
  aritmética. La regla de [[feedback-omega-classical]] sigue en pie: **medir, no suponer**.
- ⚠️ En `Model.lean` la notación `∧` es `Formula.and` (la de FOL), así que la conjunción de
  Lean va escrita `And` a mano. Costó el primer error de compilación del módulo.

---

## ADR-040: `REFERENCE.md` ARBOLIZADO — índice raíz + tres nodos temáticos

**Fecha**: 2026-09-22
**Estado**: Aceptado. Cumple por fin **ADR-007** y **AI-GUIDE §0.5**.

**Contexto**: AI-GUIDE §0.5 dice, con esas palabras, que `REFERENCE.md` **nunca** debe
crecer como fichero único: el índice raíz lleva el catálogo y los nodos temáticos van en
`doc/REFERENCE-{tema}.md`. El documento llevaba **1024 líneas** y documentaba el detalle de
los 18 módulos él solo — el síntoma exacto que la regla nombra. La deuda se declaró el
2026-09-21 dentro del propio documento; aquí se paga.

**Decisión**: el corte por **subsistema**, que es el que el proyecto ya usa para todo lo
demás (el gate, los namespaces, el grafo de imports):

| nodo | qué cubre | módulos |
|---|---|---|
| `doc/REFERENCE-Meta.md` | contacto, **gate de pureza**, capa ω | `Prelim`, `Meta/AxiomCheck`, `Omega/Basic` |
| `doc/REFERENCE-Calculus.md` | `⊢ᵢ`, solidez, consistencia, sustitución, colapso, **la barra** | los 8 de `Calculus/` |
| `doc/REFERENCE-HA.md` | axiomas, numerales, dominio, los 34 barrados, **fragmento y modelo** | los 7 de `HA/` |

El índice raíz baja de **1024 a 286 líneas** y se queda con lo que un índice debe tener:
§0 convenciones, §1 catálogo (una fila por `.lean`, **con enlace a su nodo**), §2 grafo de
dependencias, §3 **mapa de navegación**, §4 los teoremas de cabecera, §5 punteros a
notaciones y exports, §6 estado de proyección.

**Justificación de tres detalles que no son obvios**:

1. **`Prelim.lean` va a `Meta`, no a un nodo propio.** No es teoría: es la superficie de
   importación, y la superficie de importación es asunto del gate — M-5 (qué se puede
   importar) y el eje META (qué arrastra lo importado) se leen juntos o no se leen.
2. **§4, los teoremas de cabecera, se queda en el RAÍZ.** Cruza los tres nodos, y es
   justamente lo que alguien busca al abrir el índice. Un mapa de navegación que no dice qué
   se demuestra obliga a abrir los tres.
3. ⚠️ **Los enlaces del catálogo van al FICHERO, sin ancla.** Un ancla de Markdown depende
   de cómo el renderizador normalice backticks, puntos y símbolos como `⊢ᵢ` o `ℕ`, y no es
   comprobable sin renderizar. **Un ancla rota es una cita a algo que no existe** — la misma
   familia que `[B]` vigila. El número de sección va en el texto del enlace y lo confirma la
   tabla §1 del propio nodo.

**Navegación fuerte**, que es lo que §0.5 exige y lo que hace que el árbol no se deshoje:
cada nodo abre con enlace **⬆️ al raíz** y **↔️ a los dos hermanos**, lista sus módulos con
enlace al `.lean`, cada sección repite el enlace al fichero que documenta, y cierra con un
«**lo que este nodo NO cubre**» que apunta a dónde sí está. Los **29 enlaces relativos** se
verificaron uno a uno contra el disco antes de commitear.

**Consecuencias**:
- ✅ `check-doc-sync.bash` ya estaba preparado: `DOCS` incluye `doc/REFERENCE-*.md` y los
  controles `[B]`, `[C]` y `[D]` los recorren. **No hubo que tocar el script.**
- ⚠️ **`[C]` sigue mirando la FILA y no la SECCIÓN**, y arbolizar no lo arregla: comprueba
  que el nombre del módulo aparezca en el raíz **o** en cualquier nodo. Endurecerlo sigue
  siendo decisión aparte, y está escrito en `NEXT-STEPS.md` y en el §6.1 del raíz.
- 🔑 **Cuándo cortar el siguiente nodo, para no repetir la deuda**: el criterio no es el
  número de líneas sino **el de módulos que hay que atravesar para encontrar lo suyo**. Si
  `HA/` pasa de la docena, el corte va por capas —axiomas y numerales por un lado, barra y
  fragmento por otro— y **antes** de añadir la fila trece, no después.
- ⛔ Se verificó que **no se perdió contenido**: las 65 líneas del documento viejo que no
  aparecen en el árbol son todas reescrituras deliberadas —filas de tabla que ganaron
  columna, los ítems de cumplimiento, el párrafo de la deuda ahora retirada y un ancla
  interna que se arregló—. Ninguna es detalle de módulo.

---

## ADR-041: `[C]` endurecido — de «¿se menciona?» a «¿está proyectado?»

**Fecha**: 2026-09-22
**Estado**: Aceptado. Cierra la deuda abierta en ADR-040.

**Contexto**: `[C]` se llamaba «proyección» y hacía esto:

```bash
m=$(basename "$f" .lean)
grep -q "$m" REFERENCE.md doc/REFERENCE-*.md || FAIL
```

Eso no comprueba la proyección: comprueba que **el nombre aparezca en algún sitio**.
Proyectar un `.lean` es, por AI-GUIDE §12, **trasladar todo lo público a su nodo**. Dos
agujeros, y los dos se midieron, no se supusieron:

1. **`HA/Fragment.lean` (47 declaraciones) y `HA/Model.lean` (15) pasaron TRES DÍAS en
   verde** con una fila en la tabla §1 y **ninguna sección**. Lo cazó una pasada de lectura,
   no el script.
2. ⭐ **El `grep` era por SUBCADENA**: `Subst` casa dentro de `SubstDerives`, así que
   `Calculus/Subst.lean` aprobaba **gracias a la mención de otro módulo**. Un módulo podía
   faltar entero de la documentación y dar verde por el nombre de su vecino. Este segundo
   agujero no lo había visto nadie; salió al escribir el reemplazo.

**Decisión**: `[C]` pide ahora **tres** cosas, las tres objetivas:

| | qué exige |
|---|---|
| **[C1]** CATÁLOGO | fila propia en la **tabla §1.1** del índice raíz —la sección se acota con `awk`, no vale una fila de otra tabla— con la **ruta completa entre backticks** |
| **[C2]** SECCIÓN | un **encabezado** que lo nombre, en el raíz o en un nodo, **más** la línea `**Fichero**: [...](../<LIB>/<ruta>)` |
| **[C3]** NAVEGACIÓN | cada nodo enlaza ⬆️ al raíz, el raíz enlaza a cada nodo, y **todo enlace relativo del árbol resuelve a un fichero que existe** |

⭐ **La pieza que hace el control posible es la línea `**Fichero**`** (AI-GUIDE §0.5, añadida
aquí como convención). El encabezado dice «aquí está»; el enlace dice «y es **este**
fichero», y el control **lo resuelve contra el disco**. Sin ella no hay forma de saber si una
sección documenta el módulo o solo lo nombra de pasada: un encabezado suelto es una promesa.

**Justificación de dos detalles**:

* ⚠️ **Todo se compara con `grep -F`, y no es cosmético.** La primera versión escapaba la
  ruta para meterla en una ERE, y **el escapado salió mal en este entorno**:
  `sed 's/…/\&/g'` devolvió `HA/Model&lean` en vez de `HA/Model\.lean`. El patrón no casaba
  nada y los 18 módulos dieron ✗. Se vio porque el fallo fue ruidoso — **el falso POSITIVO
  de la misma clase habría sido mudo**. Cadena literal y nada de escapar.
* **[C3] entra en `[C]` y no en un control nuevo** porque es la misma pregunta: la
  proyección tiene que apuntar a cosas que existen. Un enlace roto es una cita a algo que no
  existe, que es lo que vigila `[B]` para los símbolos.

**Probado con casos POSITIVOS y NEGATIVOS en la misma pasada** —la regla que este proyecto
aprendió a fuerza de controles vacíos— y **la prueba queda en el árbol**, no en el chat:
`sondeos/check_C_smoke.bash` la vuelve a correr entera y falla si el control deja de
comportarse como aquí se afirma.
proyecto aprendió a fuerza de controles vacíos:

| caso | qué se rompe | resultado |
|---|---|---|
| 0 | nada | ✓ verde |
| 1 | se quita la fila de `HA/Model.lean` de §1.1 | ✗ [C1] |
| 2 | se quita el encabezado de su sección | ✗ [C2] |
| 3 | se quita su línea `**Fichero**` | ✗ [C2] |
| 4 | se apunta un `**Fichero**` a un `.lean` inexistente | ✗ [C3] |
| 5 | un nodo deja de enlazar al índice raíz | ✗ [C3] |
| **6** | **regresión del agujero de la subcadena**: se borra todo lo de `Calculus/Subst.lean` dejando `SubstDerives` documentado | ✗ — **antes daba verde** |
| 7 | se restaura todo | ✓ verde |

**Consecuencias**:
- ✅ La deuda «`[C]` mira la fila y no la sección», abierta en ADR-040 y anotada en
  `NEXT-STEPS.md`, queda **cerrada**.
- ⚠️ **Lo que `[C]` sigue sin mirar**: que el CONTENIDO de la sección esté al día. Una
  sección puede existir, enlazar bien y describir el módulo de hace un mes. Eso no lo caza
  un grep — lo caza la pasada de lectura, y por eso `/armoniza` no es opcional.
- 🔑 De método, y vale para el próximo control: **la exigencia hay que poder anclarla a algo
  que el documento declare a propósito**. `[C]` solo se pudo endurecer porque se inventó una
  línea —`**Fichero**`— que existe *para ser comprobada*. Un control sobre prosa libre es un
  control sobre la forma.

---

## ADR-042: el ORDEN en producción — `/₂` entra, y ADR-037 queda REFUTADO

**Fecha**: 2026-09-22
**Estado**: Aceptado. ⛔ **Corrige el veredicto de ADR-037 para `/₂`** y su criterio.

**Contexto**: ADR-037 clasificó los símbolos de Q⁺⁺ en dos clases —los **definidos por
recursión sobre el constructor** (`τ`, `%₂`), que entran en el fragmento, y los
**caracterizados por propiedades** (`/₂`, `√`, `−`), que no— y cerró `/₂` con esta razón:

> «`/₂` pide cancelación de `+` y `·`».

⛔ **Es falso.** No hace falta cancelar nada. La cancelación es la herramienta de quien
mira `ax17` como una ecuación a despejar; mirada como lo que es —una caracterización dentro
de un **orden total y discreto**— se resuelve por **tricotomía contra el candidato**.

**Decisión**: `PeanoRF/HA/Order.lean`, el orden de Q⁺⁺ sobre términos **anclados** (hasta
hoy sólo existía sobre numerales), y con él `/₂` dentro del fragmento.

| pieza | qué es |
|---|---|
| `exI_of_ltI` / `ltI_of_add` | las dos direcciones de `ax13` para términos anclados |
| ⭐ `notI_lt_zero` | nada es menor que cero — `t + σk = 0` choca con `ax5` + `ax2` |
| ⭐⭐ `zeroI_or_succ` | **todo término anclado es `0` o sucesor** |
| ⭐ `ltI_add_right` | monotonía estricta de `+`: `(a+c)+σj = (a+σj)+c = b+c` |
| `mulI_two` | `t·2̄ = t+t` |
| ⭐⭐ `ltI_mul_two` | monotonía por `2̄`, **sin transitividad** |
| ⭐ `notI_add_succ_self` · `ltI_trans` | 🏗️ andamio de `√` |

**Resultado**, todo en `[propext, Quot.sound]`:

```lean
numeralI_div2                      : ⊢ᵢ /₂ n̄ = (n/2)‾
qDisjunctionProperty_arithTD_final : la DP de 23 axiomas, SIN HIPÓTESIS
```

**Justificación de los dos hallazgos que importan**:

1. ⭐⭐ **`zeroI_or_succ` es el axioma 3 de Robinson Q, y aquí se DERIVA.** `coreAxioms` no
   lo tiene, y de esa ausencia venía la impresión de que sin él no se despeja. Sale de la
   tricotomía: la rama `t < 0` la refuta `notI_lt_zero`, y la rama `0 < t` da el testigo
   por la dirección ⇒ de `ax13` más `0 + x = x`.
   ⚠️ Y `0 + x = x` **no es `zero_add`**: aquél cuantifica sobre `x` y por eso pide una
   instancia de inducción; aquí el término está **fijo** y basta `ax6` + `ax4`. La
   diferencia entre **esquema** e **instancia** es lo que hacía parecer cara esta pieza.
2. 🔑 **El truco que evita la transitividad.** Para `a < b ⇒ a·2̄ < b·2̄` lo natural es
   encadenar `a+a < b+a < b+b`. No hace falta: de `y + σj = k̄` se **calcula**
   `k̄·2̄ = y·2̄ + σ(σj + j)`, que es **ya** la forma que `ax13` pide. Menos piezas y menos
   hipótesis, y por eso `/₂` cerró sin `ltI_trans`.

⭐ **Y una medida de lo que costaba antes**: `addI_succ_ne` —«ningún numeral es `x + σy`»—
necesitaba **inducción META** y el proyecto la llamó «la pieza que costó». Sobre términos
anclados el mismo enunciado es `notI_add_succ_self` y sale **gratis**, porque `x + σy = x`
es justo `x < x`. El orden hace barato lo que la recursión hacía caro.

**Consecuencias**:
- 🏁 **23 de los 34 axiomas**, ocho símbolos, **cero hipótesis** — el modelo de ADR-039 se
  extendió con `/₂` y `ax17` (una meta de `omega`) y descarga también este `hcon`.
- ⛔ **El criterio de ADR-037 es SUFICIENTE pero NO NECESARIO.** «Definido por recursión
  sobre el constructor» sigue garantizando la entrada; `/₂` entra sin cumplirlo, porque su
  caracterización lo **acota por los dos lados**. Lo que decide no es la forma del axioma
  sino si deja al término encajonado en un orden total y discreto.
- ⏳ **`√` queda abierto y ahora con herramientas**: sus dos desigualdades piden
  `a<b → a·a<b·b` —mismo truco, poniendo el factor anclado delante para distribuir— y
  tratar el `≤` de `ax14`, que es una disyunción. Dos de sus tres piezas ya están puestas.
- ⚠️ La deuda que esto deja escrita: **ADR-037 sigue en el árbol con su tabla original**, y
  la tabla es la que se cita. Queda anotada ahí la corrección, con puntero a este ADR.
- 🔑 De método, y es lo caro de aprender: **una razón dada para cerrar una casilla no es una
  medición**. ADR-037 midió bien lo que midió (qué axiomas son de Harrop, qué símbolos
  aparecen dónde) y **argumentó** el resto. Los tres argumentos han caído ya dos veces —`−`
  con ADR-039, `/₂` con éste—.

---

## ADR-043: la CI dice CONTRA QUÉ compiló, y distingue el entorno del código

**Fecha**: 2026-09-22
**Estado**: Aceptado. Cierra dos deudas abiertas en la auditoría del mismo día.

**Contexto**: dos fallos de la misma familia, los dos medidos el 2026-09-22.

1. ⛔ **Un verde no decía contra qué lo era.** El workflow clona FOL, ROB++ y Peano en
   `ref: master`, que es **flotante**. Ese día las tres se movieron —FOL generificó
   `Model (D)` a `ModelG (S D)`, y `HA/Model.lean` usa `Model Nat` **directamente**— y no
   había forma de saber qué builds pasados cubrían ese cambio y cuáles no. Es el mismo
   agujero por el que el 2026-09-21 el gate se quedó ciego ante `Derives₀`: **aguas arriba
   se mueve y aquí no queda rastro**.
2. ⛔ **Un rojo no decía si era del proyecto.** El paso `Install Lean toolchain` se quedó
   **20 minutos** colgado descargando y murió con «error during download / Recv failure:
   Connection reset by peer». La CI salió **roja sin que el código ni aguas arriba tuvieran
   nada que ver**, y el relanzamiento pasó en **1m41s**. Sin reloj, una caída de red se come
   el runner entero; sin reintento, se come además la sesión de quien la mira.

**Decisión**:

* **Certificar el CUARTETO** —`PeanoRF`, `FOL`, `ROBINSON_PlusPlus`, `Peano`— con su SHA y
  el asunto de su último commit, en el `GITHUB_STEP_SUMMARY`. Con **`if: always()`**, porque
  el certificado hace más falta cuando el build sale rojo.
* **Reintento con reloj** en el toolchain: `timeout 300` por intento (mata el cuelgue), tres
  intentos con espera creciente (absorben lo transitorio), `timeout-minutes: 20` de tope
  duro, y un `::error::` final que **dice cómo distinguir** una caída de red de un fallo
  real. Y `timeout-minutes: 5` en la instalación de elan, por la misma razón.

**Justificación**:

* ⚠️ **Certificar NO es fijar, y la diferencia es una decisión.** Fijar los SHA quitaría el
  ruido, pero también dejaría de avisarnos de que aguas arriba nos rompió hasta el día que
  subiéramos el pin — y este proyecto **quiere** enterarse pronto: `master` flotante es lo
  que hizo que la generificación de `Model` se midiera el mismo día. Se registra y se sigue
  flotando, a propósito.
* Aguas arriba hace lo mismo: FOL certifica el par `(FOL@sha, RPP@sha)` desde su ADR-073.
  Aquí son cuatro porque son cuatro las que entran en el build.
* 🔑 **El reintento NO debilita el control.** Tres fallos seguidos siguen dando rojo; lo que
  cambia es que un fallo **transitorio** deja de disfrazarse de fallo del proyecto. Probado
  con los cuatro casos antes de subir —éxito al primer intento, recuperación tras dos
  fallos (el caso real), rojo tras tres, y `timeout` matando un cuelgue con `rc=124`—.

**Consecuencias**:
- ✅ A partir de ahora, **cada run publica el cuarteto**: un rojo se puede atribuir y un
  verde se puede citar.
- ⚠️ **Lo que esto NO arregla**: que aguas arriba rompa. Sigue pudiendo pasar y seguirá
  saliendo en rojo — pero ahora el certificado dice **contra qué SHA**, que es lo que
  convierte un rojo en un diagnóstico.
- 🔑 De método, y es lo reutilizable: **un control que no distingue «el sujeto falló» de
  «el instrumento falló» no es un control, es ruido con suerte.** Es la misma lección que
  «falta de medida es ROJO, no verde» (AI-GUIDE §27.1) mirada por el otro lado: si el
  instrumento puede fallar por su cuenta, el resultado tiene que decir cuál de los dos fue.
- ⚠️ Y una honesta sobre esta sesión: al ver el rojo dije que la CI «estaba reconstruyendo
  FOL y RPP desde cero contra los HEAD nuevos». **Era falso** — el job murió en el primer
  paso y nunca clonó nada. Diagnosticar antes de leer el log es exactamente lo que este ADR
  viene a hacer innecesario.

---

## ADR-044: `::` entra POR COMPOSICIÓN — 24 de 34, y el segundo ⛔ de ADR-037 que cae solo

**Fecha**: 2026-09-22
**Estado**: Aceptado. ⛔ **Refuta el veredicto de ADR-037 para `::`**, y lo hace **sin
trabajo nuevo**.

**Contexto**: ADR-037 bloqueó `::` con esta razón, y la razón era **correcta**:

> «`::` ⛔ — **`pair` usa `/₂`** (medido)».

Lo que no se vio es que eso no es una propiedad de `::`, sino una **dependencia**. En RPP:

```lean
pair x y        = cantor_func x y = div2 (cantor_poly x y)
cantor_poly x y = (x+y)·σ(x+y) + 2·y          -- sólo `+`, `·`, `σ`, `2`
ax_L0_cons_def  : ∀x∀y.  x :: y = pair x (σy)
```

⇒ el bloqueo de `::` estaba **condicionado** al de `/₂`. Cuando ADR-042 determinó `/₂`, el
de `::` cayó por sí solo, y nadie lo notó hasta ir a mirarlo.

**Decisión**: `LQtdc`, `arithTDCAxioms` (24 = los 23 más `ax_L0_cons_def`), `numeralI_cons`,
y el modelo extendido con `::` ⇒ `qDisjunctionProperty_arithTDC_final`.

**Justificación**: la demostración de `numeralI_cons` **no tiene ninguna idea nueva**. Es
`ax_L0` instanciado, `numeralI_add`/`numeralI_mul` bajando `cantor_poly` a numeral, y
`numeralI_div2` cerrando. Salió a la primera, que es lo que se espera de una composición.

⭐ En el modelo, `ax_L0` sale por **`trivial`**: `::` se interpreta como el emparejamiento de
Cantor —que es exactamente lo que `pair` desarrolla—, así que los dos lados del axioma son
**el mismo término**. No hay nada que demostrar porque no hay nada que elegir.

**Resultado**, todo en `[propext, Quot.sound]`:

```lean
numeralI_cons                       : ⊢ᵢ m̄ :: n̄ = (cantor(m, n+1))‾
qDisjunctionProperty_arithTDC_final : la DP de 24 axiomas, SIN HIPÓTESIS
```

**Consecuencias**:
- 🏁 **24 de los 34 axiomas**, **nueve símbolos**, cero hipótesis.
- ⛔⛔ **Segundo veredicto de ADR-037 refutado, y el tercero de sus cinco ⛔ que cae.** Van
  `−` (ADR-039, medido negativo), `/₂` (ADR-042, demostrado) y `::` (aquí, por corolario).
- 🔑 **Y la lección de método es la que más va a servir**: ADR-037 puso en una sola columna
  ⛔ dos cosas distintas, y la diferencia es **semántica**:
  * `−` está **libre**: `ax29` lo condiciona a `x ≤ y` y fuera de ahí ningún modelo lo fija.
    Ahí los modelos **deciden**, y deciden que no.
  * `/₂`, `√` y `::` están **determinados en TODO modelo** — `ax17` fija `/₂n` una vez
    fijado `%₂n`, y `ax14`+`ax15` encajonan `√n` entre dos cuadrados consecutivos. Para
    éstos **la técnica de modelos no puede dar nunca un negativo**: o se demuestra, o se
    deja abierto.
  ⇒ un ⛔ de «no encontramos la prueba» **no es** un ⛔ de «no está determinado», y ADR-037
  los escribió iguales. De sus cinco, **sólo uno** era del segundo tipo.
- ⚠️ **Y una dependencia que conviene tener escrita**: `::` dependía de `/₂`, y nadie lo
  anotó como tal. Antes de dar un símbolo por cerrado hay que mirar **de qué otro depende**,
  porque el día que se abra el otro, éste se abre con él y no salta ningún control.
- ⏳ Quedan `√` —que no es composición: pide la forma ∀ de `zeroI_or_succ`— y `##`/`Π_p`,
  que son recursiones sobre lista y piden saber si un numeral es `nil` o `cons`.

---

## ADR-045: `√` entra — 26 de 34, y el primer DURO que el fragmento mete

**Fecha**: 2026-09-22
**Estado**: Aceptado. Cierra la última casilla de ADR-037 que se podía cerrar demostrando.

**Contexto**: `numeralI_sqrt` ya medía que `√` está **determinado**. Meterlo en el fragmento
no era trámite, por tres razones que se midieron antes de empezar:

1. **El núcleo de Lean no trae `Nat.sqrt`** —vive en Mathlib, que aquí no hay—, y
   `numOf_of_LQ…` necesita **calcular** el numeral, no sólo razonar con uno dado.
2. ⛔ **`ax14_sqrt_le` NO es de Harrop**: `le a b` es la disyunción `a < b ∨ a = b`. Es el
   **primer axioma duro** que el fragmento incorpora sin tenerlo ya barrado de antes —
   `ax13`, `ax19` y `ax21` entraron con sus escalones, pero ya estaban resueltos—.
3. El **modelo** tiene que interpretar `√` y verificar las dos desigualdades.

**Decisión**, en tres piezas:

| | |
|---|---|
| `isqrt` + `isqrt_le` + `lt_isqrt_succ` | la raíz entera del META, **escrita aquí**: búsqueda lineal descendente con combustible, y con `fuel = n` basta porque `n < (n+1)²` |
| `slash_ax14` **generalizado** | estaba clavado a `ctx insts` y `LQpp`; pasa a `{Γ} (L) (hΓ)`, como ya se hizo con `ax13`, `ax19` y `ax21` |
| `LQtdcs` · `arithTDCSAxioms` (26) · `ctxS` · el modelo con `√` | el escalón, y `hcon_fragmentS` que lo deja **incondicional** |

**Justificación de la forma del enunciado**: `numeralI_sqrt` toma `k` **con sus dos cotas
como hipótesis** en vez de llamar a `isqrt`. Es más general —vale para cualquier testigo— y
**separa la aritmética del META de la derivación del OBJETO**, que es justo lo que este
proyecto quiere poder auditar por separado. `isqrt` sólo aparece donde hace falta calcular.

⭐ En el modelo, los dos axiomas de `√` son **exactamente las dos cotas de `isqrt`**: `ax15`
es `lt_isqrt_succ` y `ax14` es `isqrt_le` partido en las dos ramas de la disyunción con
`Nat.eq_or_lt_of_le`. No hay nada que inventar.

**Resultado**, todo en `[propext, Quot.sound]`:

```lean
qDisjunctionProperty_arithTDCS_final : la DP de 26 axiomas, SIN HIPÓTESIS
```

**Consecuencias**:
- 🏁 **26 de los 34 axiomas**, **diez símbolos**, cero hipótesis.
- 🏁🏁 **Las CINCO casillas ⛔ de ADR-037 que se podían cerrar están cerradas**: `−` en
  negativo y medido (ADR-039), `/₂` (042), `::` (044) y `√` (045) demostrados.
- ⛔ **Lo que queda fuera son los cinco axiomas de lista (`##`, `Π_p`, `ax_L2`, `ax_L3`) y
  `ax29`**, y las dos razones son distintas: `−` está **medido como imposible**; los de
  lista piden **inducción sobre listas**, que `coreAxioms` no tiene.
- 📋 **Tablero**: `doc/TABLERO-FRAGMENTO.md` pone los 34 axiomas y los 14 símbolos con su
  estado y su razón, y sus cifras las verifica el kernel en `sondeos/audit_fragmento.lean`.
  Es el documento a mirar antes de decidir el paso siguiente.
- 🔑 De método: **generalizar `slash_ax14` fue la tercera vez** que un lema clavado a
  `ctx`/`LQpp` hubo que abrirlo a `{Γ}`/`L`. Los que quedan clavados —`slash_axL2`,
  `slash_axL3`— lo pedirán también el día que se intenten. Escribirlos parametrizados desde
  el principio habría salido más barato.

---

## ADR-046: los cinco de lista NO piden inducción — la codificación no es SOBREYECTIVA

**Fecha**: 2026-09-22
**Estado**: Aceptado en su parte **medida**; la consecuencia queda ⏳ abierta y dicha.

**Contexto**: el proyecto lleva escrito —en ADR-037, en `SlashAxioms.lean`, en NEXT-STEPS y
en el tablero— que `##`, `Π_p`, `ax_L2_in_cons` y `ax_L3_in_concat` quedan fuera del
fragmento porque

> «piden saber si un numeral es `nil` o `cons`, y eso es **inducción sobre listas**, que
> `coreAxioms` no tiene».

⛔ **Eso es un ARGUMENTO**, y en esta familia los argumentos han salido mal cuatro veces:
`−` (ADR-039), `/₂` (042), `::` (044) y `√` (045). Al medirlo, sale mal la quinta.

**Lo medido** (`sondeos/listas_probe.lean`, verificado por el kernel):

```lean
two_le_consNat  : ∀ h t, 2 ≤ consNat h t
one_ne_consNat  : ∀ h t, consNat h t ≠ 1
```

En Q⁺⁺, `nil` **es** `zero` y `cons h t = pair h (σt) = π(h, t+1)`. Escribiendo
`consNat h t = T(h+t+1) + (t+1)` con `T` triangular, los valores de `cons` son

```
s=1 → 2 · s=2 → 4,5 · s=3 → 7,8,9 · s=4 → 11..14 · …
```

es decir **todos los naturales menos `{0, 1, 3, 6, 10, …}`**. Y `0` es `nil`.

⇒ 🔑 **`1`, `3`, `6`, `10`, … no son NI `[]` NI `h::t`.** La codificación de listas **no es
sobreyectiva**, y por tanto «todo término es `[]` o un `::`» **es FALSO en el modelo
estándar**.

**Decisión**: corregir el diagnóstico en todos los sitios donde está escrito. El obstáculo
**no es** que falte un esquema de inducción para demostrar esa disyunción: es que **no hay
nada que demostrar**, porque la disyunción es falsa. Un esquema de inducción sobre listas no
la arreglaría, porque el problema no está en las listas sino en los **códigos que no son
listas**.

**Justificación de por qué importa la diferencia**: cambia de clase el problema.

| clase | qué se puede hacer | ejemplos |
|---|---|---|
| **libre** — ningún modelo lo fija | los modelos dan un **negativo medible** | `−`, y **probablemente los cinco de lista** |
| **determinado en todo modelo** | o se demuestra, o se deja abierto | `/₂`, `√`, `::` |

Mientras el diagnóstico era «falta inducción», la conclusión natural era *esperar a un
sistema más fuerte*. Con el diagnóstico correcto, lo que toca es **medir el negativo**, que
es una tarea acotada y que este proyecto ya sabe hacer (`sub_neither`).

**Consecuencias**:
- ⏳ **Lo que falta, y queda dicho**: que de la no-sobreyectividad se siga que `∈`, `##` y
  `Π_p` están **libres** sobre esos códigos. Pide dos modelos que difieran ahí, y para
  tenerlos hacen falta dos piezas concretas:
  * la **inyectividad del emparejamiento de Cantor**, que es lo que hace bien definida la
    recursión de `∈` sobre los códigos que sí son listas;
  * una relación `MemN` inductiva (`head`/`tail`) y una variante que además valga en `1`:
    las dos cumplen `ax_L1` —porque `1 ≠ 0`— y `ax_L2` —porque `1` no es un `cons`—, y
    difieren en `x ∈ 1̄`.
- ⚠️ **`ax_C3_concat_assoc` es la que puede estropear la medición**, y hay que mirarla: a
  diferencia de `ax_C1`/`ax_C2`, la asociatividad **sí** dice algo sobre la basura. El
  cálculo a mano sale —basta que la basura absorba por la izquierda—, pero **eso no está
  medido** y no se puede dar por bueno.
- 🔑 De método, y van cinco: **«no lo sabemos hacer» y «no está determinado» se escriben
  igual y no son lo mismo.** Este proyecto ha confundido las dos cinco veces en la misma
  tabla. La regla que sale: antes de cerrar una casilla, preguntar **si el modelo estándar
  la decide**; si la decide, es demostrable o abierta, nunca «imposible».

---

## ADR-047: la respuesta de FOL — lo que nos corrige, lo que nos frena y lo que no nos alcanza

**Fecha**: 2026-09-23
**Estado**: Aceptado. ⬜ Dos puntos quedan a decisión del propietario.
**Origen**: respuesta del agente de FOL al informe de auditoría del 2026-09-23.

**Contexto**: la auditoría del 2026-09-23 encontró duplicación entre PeanoRF y ROB++ y
pidió a FOL el estado del encargo. La respuesta llegó el mismo día, verificó nuestras siete
afirmaciones comprobables, y trae tres cosas que no podíamos saber.

### 1 · ⬜ Lo que nos FRENA: la codificación de listas va a cambiar

ADR-093 de ROB++ (`sondeos/CantorSobreyectivo.lean`, verificado aquí: existe y compila con
`cantorN_surj`, `sin_basura`, `cola_decrece`): `ax_L0_cons_def` dice hoy
`cons a b = pair a (σb)`, y el `σ` sólo está para que `cons h t ≠ nil`. Sacándolo fuera
—`cons a b = σ (pair a b)`— **el Cantor pelado es sobreyectivo** y `σ∘pair` es biyección
`ℕ² → ℕ≥1` con `nil = 0` fuera de la imagen ⇒ **todo número es `nil` o un `cons`**.

⛔⛔ **Eso tumbaría nuestro ADR-046.** Reclasificamos los cinco axiomas de lista de «piden
inducción» a «probablemente LIBRES sobre la basura» **porque hay basura**. Sin basura,
vuelven a la casilla «determinados», y lo que había que **medir** pasa a ser lo que hay que
**demostrar**.

**Decisión**: ⬜ **no fijar `consNat` ni tocar la línea de listas** hasta que el propietario
decida sobre `ax_L0_cons_def`. Y cuando caiga, **revisar ADR-046 en cualquiera de los dos
sentidos**.

🔑 De método: **una medición puede caducar porque cambie el objeto medido, no porque
estuviera mal hecha.** ADR-046 está bien medido sobre la codificación de hoy, y eso no lo
protege de un cambio de codificación. Lo que hay que escribir al lado de una medición es
**de qué depende**.

### 2 · ✅ Lo que nos CORRIGE, y es más preciso que lo nuestro

Escribimos que lo que nos salva del ADR-088 de ROB++ —`Prf` no es sólido respecto del modelo
estándar— es que «nuestro modelo no usa ningún esquema de inducción». Cierto, **pero no es
la razón**: la basura está igual en nuestro modelo, porque nuestro `consNat` **es** su
`consN` (probado, `sondeos/audit_2026-09-23.lean`).

✅ Lo que nos protege es **que ningún axioma de `coreAxioms` afirma que todo elemento del
dominio sea `nil` o un `cons`**. La inducción es el mecanismo por el que la basura se vuelve
letal, no su causa. Aceptado y escrito donde toca.

### 3 · ✅ Lo que NO nos alcanza, y está medido

ADR-092 de FOL: el modelo canónico (`FOL/Canonical0.lean:162-176`) toma
`IsMaximalConsistent₀ S` como hipótesis ya en `termSetoid` ⇒ **usarlo para probar
consistencia es circular**. Verificado ahí.

⇒ **No nos llega, y no por argumento**:

```
módulos prohibidos en el entorno: []      -- Canonical0, Completeness, Compacity
total de módulos importados: 2302
```

Nuestro modelo es `natModelK : Model Nat`, **concreto y escrito a mano**, verificado axioma a
axioma sobre `ℕ`. 🔑 **Un modelo canónico consume consistencia; uno concreto la produce** —
y es exactamente por eso que `derivesI_consistent` y `hcon_fragment*` son el mismo patrón a
dos alturas.

### 4 · ⛔ Lo que nosotros escribimos mal

«El encargo a FOL sigue sin contestar: no nos mencionan en ningún documento». **Falso**:
`FOL/SequentSound0.lean:70` nos cita por nombre en producción, y ese hit **ya había salido
en la auditoría del 2026-09-21**. Se escribió la frase más ancha igual.

⚠️ Y su corrección también trae un error de atribución, medido: las cuatro referencias `.md`
que listan —ADR-047, ADR-061, ADR-065, `NEXT-STEPS.md:762`— **son de ROB++, no de FOL**.
`grep -rn "PeanoRF" ../FOL --include=*.md` da **cero**.

🔑 La regla que nos devuelven y que tomamos: **una ausencia se mide con un `grep`**. Las dos
veces de este párrafo lo confirman, en las dos direcciones.

### 5 · ⬜ Las dos decisiones del propietario

1. **§2 del encargo — la sustitución paralela.** FOL entra hoy en congelación. Nuestra
   recomendación: **que NO entre hoy**. Congelar un árbol con un módulo recién metido en su
   núcleo sintáctico es peor que no meterlo; seguimos manteniendo `Calculus/Subst.lean`
   aquí, con la duplicación declarada en ADR-010, y se revisa al descongelar. Si hay margen
   para medir antes, su ofrecimiento —alcance, footprint, y si mueve alguno de los 147
   vigilados— es el número que decide.
2. **`ax_L0_cons_def`** — no es nuestra decisión, pero nos cambia el plan. Pedida
   notificación.

**Consecuencias**:
- ✅ **§3 del encargo, ACEPTADO por FOL**: `formulaComplexity` y `complexity_substFormula`
  bajan a un módulo base ⇒ se puede **planificar la retirada de `fdepth`**. Anotado como
  deuda con fecha en su ciclo de cierre.
- ⏳ **La línea de listas queda congelada por nuestra parte**, no por falta de camino sino
  porque el objeto va a cambiar.
- 📄 La respuesta completa, en `doc/RESPUESTA-FOL-2026-09-23.md`.
- 🔑 Y una de método que vale para las dos direcciones: **este intercambio corrigió a los dos
  lados el mismo día.** Nosotros les dijimos dos veces que algo suyo era falso y una lo era;
  ellos nos han dicho una y lo era. Un informe que publica sus refutaciones se puede leer
  sin re-medirlo — y los dos lo estamos haciendo.

---

## PRF-048: la DP de `Derives₀` es FALSA — y el fragmento que FOL quiere construir YA EXISTE

**Fecha**: 2026-09-23
**Estado**: Aceptado. ⬜ Una decisión del propietario: §2 del encargo **REABRE**.
**Origen**: segunda respuesta del agente de FOL, el mismo día, tras decidir ir a por la
propiedad de disyunción.
**Prefijo**: ⚠️ a partir de aquí las ADR de este proyecto llevan **`PRF-`** y las de ROB++
`RPP-`, a petición de FOL: hay **dos ADR-047** distintas sobre esta misma relación y se
estaban citando la una por la otra.

**Contexto**: FOL decidió ir a por la propiedad de disyunción y, antes de construir,
**refutó el objetivo tal como nosotros se lo habíamos escrito**. Su contraejemplo está
compilado en net-0 y lo hemos verificado pieza a pieza en su árbol.

### 1 · ⛔ Lo que escribimos mal, y es un error nuestro de bulto

`doc/ENCARGO-FOL-2026-09-17.md` decía dos veces —cabecera y §4— «la **propiedad de
disyunción** para `Derives₀`». **Es falso**, y no por matiz: `Derives₀` es deducción natural
**clásica**, y la DP es la marca de lo intuicionista. Verificado en su árbol, las dos
mitades del contraejemplo:

| pieza | dónde, medido | qué da |
|---|---|---|
| `derives0_em_ctx` | `FOL/Propositional0.lean:79` | `Δ ⊢₀ A ∨ ¬A` para **todo** `Δ`, por `dne_rule` |
| `derives0_not_complete` | `FOL/Soundness0.lean:235` | `∃A, ¬([] ⊢₀ A) ∧ ¬([] ⊢₀ ¬A)` |

Para ese `A`: `[] ⊢₀ A ∨ ¬A` y ninguno de los dos disyuntos es derivable. ⛔ **Es una
refutación, no una objeción**, y la aceptamos entera.

⚠️ Y lo que la hace nuestra y no suya: nuestro propio §5 del encargo **sí** distingue —dice
que lo demostrado es la DP de `⊢ᵢ` sobre contexto vacío— y añade que lo decimos «porque es
el tipo de matiz que se pierde al citar de segunda mano». **Se perdió en el párrafo de
arriba del mismo documento.** Es la séptima forma de dar verde sin comprobar, otra vez del
agente y no de un script: un documento puede refutarse a sí mismo dos secciones más abajo y
ningún control mira eso.

**Decisión**: corregido el encargo en los dos sitios, con el porqué y las dos referencias,
en vez de borrar la frase.

### 2 · 🏁 Lo que les devolvemos, y es más de lo que piden: el cálculo ya está escrito

FOL plantea construir `Derives₀ᵢ = Derives₀` menos los tres constructores clásicos, y lo
cotiza como «un cálculo nuevo más una metateoría». **Medido hoy, ese cálculo es literalmente
`PeanoRF.Calculus.Derivesᵢ`**:

```
FOL/Derives0.lean:98   Derives₀  → 21 constructores
                       menos dne_rule, dne_schema, forall_not_ex_not
PeanoRF/Calculus/DerivesI.lean:66  Derivesᵢ → 18, el MISMO conjunto, nombre por nombre
PeanoRF/Calculus/DerivesI.lean     derivesI_to_derives0 : (Γ ⊢ᵢ f) → (Γ ⊢₀ f)
```

y su DP está demostrada: `PeanoRF.Calculus.disjunction_property`, más la de existencia.

### 3 · ✅ Sus dos incógnitas, contestadas — y las dos se evaporan por la MISMA razón

**(a) ¿Tiene igualdad nuestro `⊢ᵢ`?** ⭐ **SÍ, las tres cosas que temen**: `refl`, `subst`
**y** `rewrite_at` son constructores nuestros, y la DP está probada **con ellos dentro**. Lo
que cuesta cada uno, medido en `PeanoRF/Calculus/Slash.lean`:

| caso | qué pide | dónde |
|---|---|---|
| `refl` | nada — `Slash` de una ecuación **es** «`T ⊢ᵢ` la ecuación» | `:774` |
| `subst` | ⭐ **`slash_eq_congr`**: la barra es invariante bajo sustituciones **demostrablemente iguales** | `:581`, usado en `:777` |
| `rewrite_at` | `slash_rewrite` + que `LocalRule` sea intuicionista (sólo `commuteImpl`) | `:435`, usado en `:765` |

**(b) ¿Última regla o secuentes?** ⛔ **Ninguna de las dos: es la BARRA DE KLEENE**, y ésa
es la respuesta que les ahorra el sondeo. `Slash T D : Formula → Prop` se define por
recursión bien fundada sobre la fórmula (`Slash.lean:147`), y el teorema es
`slash_of_derives` (`:681`): *toda derivación desde un contexto barrado barra su
conclusión*, por **inducción sobre la derivación**. La DP sale de la ecuación de `∨`.

🔑 **Y por eso las dos incógnitas que cotizan se caen a la vez**: la hipótesis inductiva no
es «la última regla fue `orR`», es «la conclusión está barrada». **No se mira la forma del
secuente en ningún punto** ⇒ multi-conclusión, `implR`/`allR`/`struct` y la
especialización del Hauptsatz a `|Δ| ≤ 1` **no aparecen en la prueba**. Y la igualdad no es
una trampa sino tres casos más de la misma inducción, que ya están escritos.

⚠️ **El precio, que sí lo hay y no es el que temen**: la pieza cara es `slash_eq_congr`,
porque el cuantificador obliga a generalizar sobre **todas** las sustituciones —el índice en
que dos sustituciones difieren sube al pasar bajo un `∀`—. Eso es exactamente lo que ya les
avisamos en §4 del encargo, y **es lo único de aquello que sigue en pie**.

### 4 · ⬜ §2 REABRE, y ahora con razón medida

FOL dice que con este objetivo `Subst.lean` deja de ser un módulo huérfano. **Confirmado, y
podemos decir por qué exactamente**: el `∀ ρ` va **dentro** de la inducción de
`slash_of_derives` —sin cuantificar sobre todas las sustituciones, el caso `intro_forall` no
cierra—, y eso **es** el álgebra de sustitución paralela. `leibniz_at` es su consecuencia y
es lo que hace andar el caso atómico de `slash_eq_congr`.

⭐ Y **§3 deja de ser un favor que nos hacen**: `Slash` se define por recursión bien fundada
en `fdepth` y `decreasing_by` usa `fdepth_subst`. Sus dos lemas —`formulaComplexity` y
`complexity_substFormula` (`FOL/Canonical0.lean:299,313`, vivos, detrás de la cadena
clásica)— son **precisamente** los que la definición de la barra necesita. Si FOL toma esta
ruta, los necesita **para sí misma**, no para que nosotros retiremos un duplicado.

**Decisión**: ⬜ **recomendación revisada, y es la contraria a la de esta mañana** (PRF-047 §7):
con consumidor dentro de FOL, **§2 debería entrar**, y §3 con ella. El sello no se pone
hasta tenerlas. Sigue siendo decisión del propietario.

**Justificación**: esta mañana la recomendación era «que no entre», y el argumento era *«congelar
un árbol con un módulo recién metido en su núcleo sintáctico es peor que no meterlo»*. Ese
argumento valía para un módulo **sin consumidor**. Con consumidor, lo que se congelaría es
un árbol al que le falta la infraestructura de su propio siguiente objetivo.

**Consecuencias**:
- ⚠️ **Lo que NO se traslada tal cual, y hay que decirlo**: su `Derives₀` es hoy polimórfico
  (`{Sym : Type}`, `FOL/Derives0.lean:98`) y nuestro `Derivesᵢ` es monomórfico sobre
  `Formula = FormulaG String` (`FOL/FOL.lean:44`). Generalizar los 18 constructores parece
  mecánico —ninguno menciona `String`—, pero **la capa de colapso de `Slash.lean` sí lo
  lleva** (`L : String → Nat → Bool`). ⭐ Para la DP de la LÓGICA sobre `[]` eso es vacuo: ahí
  `L` es total y el colapso es la identidad (`collapseF_trivial`). Es la divergencia de
  polimorfismo que llevamos vigilando desde el 2026-09-22, y **éste es el primer sitio donde
  cuesta algo**.
- ⛔ **Lo que seguimos sin tener, y no lo vendemos**: nuestra DP es de la **lógica** sobre
  contexto vacío, y la de HA sólo para el **fragmento de 26 axiomas**. Para `coreAxioms`
  entero siguen `hNum` y `hIn` como hipótesis, y `hNum` está **medida como falsa** para `−`.
- 📄 La respuesta completa, en `doc/RESPUESTA-FOL-2026-09-23b.md`.

---

## PRF-049: la propuesta (C) — SÍ, pero son SIETE módulos y la «única línea» es la que no puede viajar

**Fecha**: 2026-09-23
**Estado**: ⬜ **Recomendación. La decisión del reparto es del propietario.**
**Origen**: RPP-098 §5, sancionada por el propietario en ROB++, y enviada como propuesta en
`../FOL/RESPUESTA-PEANORF-2026-09-23.md` §1. **FOL no se sella hasta que contestemos.**

**Contexto**: FOL y ROB++ midieron que `PeanoRF/Calculus/DerivesI.lean` es literalmente
`Derives₀` menos los tres constructores clásicos y que `Slash.lean` prueba la DP que FOL
quería, y proponen **(C): que `Subst.lean`, `DerivesI.lean` y `Slash.lean` bajen a FOL**,
porque son sobre `FOL.Formula` y `FOL.Derives0`, no sobre HA. Su medida del acoplamiento con
RPP y Peano: «**una sola línea**, `Collapse.lean:72`».

### 1 · ✅ La dirección es correcta, y es nuestro propio argumento

Es el §2 de nuestro encargo llevado a su consecuencia: *«es infraestructura de SINTAXIS, no de
nuestro cálculo»*. ADR-010/M-4 prohíben duplicar el núcleo del lenguaje, y `Subst.lean` lo
duplicaba. La DP debe vivir donde vive su sujeto.

### 2 · ⚠️ Pero la propuesta está mal medida **en los dos sentidos**

**Más GRANDE**: `Slash.lean:7-10` importa `Consistency`, `SubstDerives`, `Eq` y `Collapse`.
⇒ son **7 de los 8** módulos de `Calculus/` (todo menos `Soundness`): **114 de nuestras 442
declaraciones**, 2 487 de 2 668 líneas. Su frase «lo que os quedaríais: `Collapse`,
`Consistency`, `Eq`» es **incompatible** con llevarse `Slash`.

**Más BARATA**: de los siete, **seis tienen CERO acoplamiento de código** con RPP/Peano. Los
hits de `Subst` (l. 48-49) y `DerivesI` (l. 18, 145) están **en comentarios**;
`SubstDerives`, `Consistency` y `Slash` dan cero absoluto; y los 7 de `Eq.lean` son **un solo
lema**, `eqI_congr_succ`, que **`Slash` no usa** — de `Eq` sólo usa `eqI_symm` y `specI`,
lógica pura.

### 3 · ⛔ Y la condición que BLOQUEA

`Collapse.lean:61` hace `open ROBINSON_PlusPlus.Minimal.Axioms` para el `zero` al que colapsa
todo símbolo fuera de la signatura. Medido: **RPP importa FOL**
(`ROBINSON_PlusPlus/Minimal/Axioms.lean:7`) y **FOL no importa RPP** (cero en todo `FOL/`).

⇒ ese `open` dentro de FOL sería un **CICLO**. 🔑 **La «única línea de acoplamiento» que
midieron no es una línea barata: es la única que no puede viajar.**

⭐ Y no hay contenido detrás: `zero` es `.func "0" []`, sintaxis pura de FOL que *casualmente*
se define en RPP, y lo único que `Collapse.lean` usa de él es que sea **cerrado** (su propio
docstring, l. 42). Salidas: que FOL defina su `zeroT`, o —mejor— **parametrizar `collapseT`
por el término por defecto**. Ofrecido hacerlo aquí antes de entregar.

### 4 · ⚠️ El aviso de calendario

`Slash.lean` es **frente abierto**: `hIn`, el modelo de `coreAxioms` entero, y la línea de
listas congelada esperando `ax_L0_cons_def`. El `git-lock.bash` de FOL permite **añadir** por
`*Ext.lean`, no **cambiar** — y lo que H3ter puede pedir es cambiar el **enunciado**: el
parámetro `T` de `Slash` se añadió el 2026-09-18 justo porque sin él la DP de HA no se podía
enunciar.

**Decisión**: ⬜ **recomendamos un reparto en DOS TIEMPOS**:

| | qué | cuándo |
|---|---|---|
| ahora | `Subst`, `DerivesI`, `SubstDerives`, `Consistency` (44 decls) | ✅ hoy |
| después | `Eq` sin `eqI_congr_succ`, `Collapse` parametrizado, `Slash` | ⏳ al cerrar H3ter, **o** hoy si `Slash` queda fuera del freeze |

**Justificación**: la parte «ahora» no tiene ni acoplamiento ni frente abierto, así que
retirarla es ganancia pura y sin riesgo. La parte «después» es la que puede cambiar de
enunciado, y meterla en un árbol sellado convierte cada paso de H3ter en una negociación.

### 5 · ✅ Su §4.1, aceptado a medias — y el hueco real, TAPADO hoy

Su aviso: «vuestro gate no es un detector de `sorry`, `sorryAx` está en `allowedAxioms`».
**Cierto, y está escrito ahí mismo**: el docstring de `AxiomCheck.lean:138-140` dice
literalmente que este gate no es un detector de `sorry`. Quien lo detecta es
`check-sorry.bash`, uno de los siete controles, en la CI.

⭐ **Pero su censo de agujeros de confianza sí era un hueco real.** Añadido como **[S2]** a
`check-sorry.bash`: `native_decide`, `unsafe`, `opaque`, `@[implemented_by]`, `@[extern]`.
El árbol da **cero** — que es cuando un trinquete sirve—, y **está probado en los dos
sentidos** (exit 1 con cada uno de los tres probados; exit 0 limpio). ⚠️ `partial` queda
fuera a propósito: no es un agujero de confianza.

**Consecuencias**:
- ⬜ Tres cosas pedidas al propietario: el reparto, la forma de quitar el `open` de
  `Collapse`, y —si va todo hoy— que `Slash.lean` quede **fuera del freeze**.
- ⚠️ Si (C) sale, **114 declaraciones salen del alcance de nuestro gate de tres ejes**, y en
  particular del control de constructores por telescopio, que es lo que hace **medible** la
  tesis del proyecto. Los 18 constructores de `Derivesᵢ` pasarían de propios a **ajenos
  vigilados** (hoy el censo tiene 45 ajenos, 12 clásicos). Hay que actualizar el censo en el
  mismo movimiento, o la pureza deja de estar medida — y **falta de medida = ROJO**.
- 📄 La respuesta completa, en `doc/RESPUESTA-FOL-2026-09-23c.md`.
- 🔑 Y una de método, que va con las otras: **medir el acoplamiento de un módulo por el de su
  import no es medirlo** (lo escribieron ellos) — pero tampoco basta contar los hits: hay que
  mirar si están en el **código** o en un **comentario**, y **hacia dónde va la flecha de
  dependencia**. Seis de siete eran comentarios; el que no lo era, era un ciclo.

---

## Plantilla para nuevas decisiones

## ADR-NNN: [Título]

**Fecha**: 2026-09-06
**Estado**: [Propuesto | Aceptado | Obsoleto | Sustituido por ADR-XXX]

**Contexto**: [¿Por qué hace falta esta decisión?]

**Decisión**: [¿Qué se decidió?]

**Justificación**: [¿Por qué esta opción frente a las alternativas?]

**Consecuencias**: [¿Cuáles son las contrapartidas?]
