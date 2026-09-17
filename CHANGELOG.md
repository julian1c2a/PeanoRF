# Changelog

**Last updated:** 2026-09-17
**Author**: Julián Calderón Almendros

All notable changes to this project will be documented in this file.

Format based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

> Este fichero es un **diario**: sus cifras y símbolos son históricos por diseño y
> quedan deliberadamente fuera del control `check-doc-sync.bash` (AI-GUIDE §27).

---

## [Unreleased]

### 🏁🏁🏁 2026-09-17 (f) · H3bis CERRADO — `⊢ᵢ` no es `⊢₀`, y ahora es un teorema

```
derivesI_ne_derives0 : ∃ φ, ([] ⊢₀ φ) ∧ ¬([] ⊢ᵢ φ)      [propext, Quot.sound]
```

**El primer teorema del proyecto que falla clásicamente.** Hasta hoy los 22 teoremas de
PeanoRF valían palabra por palabra para `⊢₀`; la tesis era arquitectónica, no demostrada.

- 🏁 **`disjunction_property`** — `[] ⊢ᵢ A ∨ B ⟹ [] ⊢ᵢ A` ó `[] ⊢ᵢ B`.
- 🏁 **`existence_property`** — de un existencial demostrado sale un TESTIGO. Es la sombra
  sintáctica de la realizabilidad: ese testigo **es** el cálculo del lado Peano (ADR-016).
- **L2** (`slash_of_derives`), los 18 casos, con el `∀ ρ` dentro de la inducción.
- ⭐ **`leibniz_at`** — la regla de Leibniz en un índice CUALQUIERA, **derivada** de la de
  índice 0 con el álgebra σ (ADR-023). Era el último obstáculo, y **no hizo falta pedir
  nada aguas arriba**: doce líneas abstrayendo la variable `k` al índice 0.
- **`slash_eq_congr`** — la barra no distingue términos demostrablemente iguales.
- `notNotP_syn` — la otra mitad de la separación, por la vía sintáctica de FOL.

Todo en **`[propext, Quot.sound]`**. El testigo de la separación es `P ∨ ¬P`, que `⊢₀`
prueba **sin `Classical.choice`** (`FOL.Propositional0.derives0_em_ctx`).

ADR-022 (por qué H3bis se intercaló antes que H4) y ADR-023 (Leibniz indexado se deriva).

**45 jobs · 12 módulos · 0 sorry · 154 declaraciones vigiladas.** Sin tocar FOL ni RPP.

### 2026-09-17 (e) · H3bis: el prerrequisito, demostrado — y el gate muerde sobre código propio

**`Calculus/Subst.lean`** — sustitución PARALELA sobre la sintaxis de FOL⁼
- `substT`/`substF`, `upS`, `consS`, `compS`, y las dos identificaciones que la conectan con
  el cálculo: `liftFormula` y `substFormula` **son** sustituciones paralelas.
- ⚠️ Deuda declarada: es infraestructura de SINTAXIS, o sea de FOL. **Medido: no la tienen.**
  Escrito para que puedan adoptarlo tal cual (`doc/ENCARGO-FOL-2026-09-17.md`).
- ⚠️ Las sustituciones se llaman `ρ` porque **`σ` no es identificador válido**: `peanolib`
  la declara como notación para `ℕ₀.succ`. El error no se parece nada a su causa.

**`Calculus/SubstDerives.lean`** — `derivesI_subst`: **`⊢ᵢ` es cerrado bajo sustitución**
- Los 18 casos, con el `∀ ρ` DENTRO de la inducción. Hermano de `FOL.Lift0.derives0_lift`.
- Incluye la navegación (`subst_getAt?`, `subst_replaceAt`, `subst_localRule`) que
  `rewrite_at` exige.

**`Calculus/Slash.lean`** — `slash_rewrite`: **la barra sobrevive a la reescritura local**
- El caso que no se ve venir: `LocalRule` sólo tiene `commuteImpl`, pero se aplica en una
  posición cualquiera. Va como EQUIVALENCIA porque la posición puede caer a la izquierda de
  una implicación, donde la dirección se invierte.
- Más el álgebra de posiciones (`getAt_replaceAt`, `replaceAt_self`, `replaceAt_replaceAt`).

**⭐ El gate cazó un `Classical.choice` NUESTRO**, por primera vez
- `upS_singleS` lo metía por un `simp` a secas, y contaminaba **siete** declaraciones aguas
  abajo. Reescrito con `if_pos`/`if_neg` explícitos. Misma familia que el `omega` de
  ADR-019: una táctica automática decidiendo sin instancia `Decidable` puesta a mano.

**⏳ Falta UN caso de L2**: la regla de Leibniz (`subst`), porque sustituye sólo en el
índice 0 y bajo un `∀` el índice se mueve. Las dos salidas están escritas en el módulo.
⛔ Sin `sorry`: el proyecto lleva 0 y esa cifra es un control, no un adorno.

Cifras: **45 jobs · 12 módulos · 0 sorry · 147 declaraciones vigiladas**. Sin tocar FOL ni RPP.

### 2026-09-17 (d) · H3bis arranca: la barra de Kleene

**`Calculus/Slash.lean`** — módulo nuevo, PARCIAL y declarado como tal
- `fdepth` + `fdepth_subst` (sustituir no cambia la complejidad), `Slash` por recursión
  bien fundada, sus ocho ecuaciones, **L1** `slash_derives` y `cut_context`.
- Todo mide `[propext]` o `[propext, Quot.sound]`.
- ⏳ **Falta L2**, y el obstáculo está localizado: el enunciado hay que generalizarlo
  **sobre sustituciones**, lo que pide **sustitución paralela** sobre la sintaxis.
  **Medido: FOL no la tiene** — sólo sustitución de una variable. Es infraestructura de
  sintaxis, o sea suya (ADR-010): va como ENCARGO, no como parche.
- ⚠️ El primer diagnóstico —«hace falta indexar por altura, como `LKh`»— era **falso**;
  desarrollar los casos lo descartó. Queda escrito en el módulo porque el descarte informa.

**Por qué este hito**: de los 22 teoremas del proyecto, **ninguno fallaba clásicamente**.
Sustituyendo `⊢ᵢ` por `⊢₀` en todo el árbol, todo seguía compilando. La tesis era
arquitectónica; la propiedad de disyunción la convierte en teorema.

Cifras: **43 jobs · 10 módulos · 0 sorry**. Sin tocar FOL ni ROBINSON_PlusPlus.

### 2026-09-17 (c) · la consistencia sin semántica, y el gate que no veía un módulo

**`Calculus/Consistency.lean`** (ADR-020) — módulo nuevo
- `consistI_syn : ¬([] ⊢ᵢ ⊥)` por la vía **sintáctica**: puente `⊢ᵢ → ⊢₀` compuesto con
  `FOL.Finitary0.derives0_consistent_fin` (secuentes sin corte). **Ni un modelo en toda la
  cadena.** ⚠️ La cifra no mejora — las dos rutas miden `[propext, Quot.sound]`— y eso se
  dice en el módulo: `#print axioms` no distingue «usa un modelo» de «no lo usa».
- ⛔ No es la consistencia de HA (Gentzen, `ε₀`): el contexto es vacío.
- `notP_syn`: `⊢ᵢ` tampoco prueba un átomo. Es media separación `⊢ᵢ ≠ ⊢₀`.

**El gate no veía el módulo nuevo** (ADR-021)
- Sus imports son una lista a mano; `Consistency` entró en el build y el gate siguió
  diciendo «80 declaraciones verificadas» sobre los ocho módulos que sí veía.
- El gate publica ahora su **ALCANCE**, y `check-doc-sync.bash` gana el control **[E]**,
  bloqueante, que lo compara con los ficheros del árbol y dice qué `import` falta.
  Probado retirando el import a propósito.

**Al día**: REFERENCE §1.1 y §3.3quinquies; §3.3quater estaba **desfasada** (decía
`Classical.choice` y «conjetura abierta» sobre algo cerrado el 16). Cifras canónicas:
**42 jobs · 9 módulos · 0 sorry · 0 axiom**. Gate: 7 relaciones de derivabilidad vigiladas.

Sin tocar FOL ni ROBINSON_PlusPlus.

### 2026-09-17 (tarde) · auditoría de COBERTURA — el gate deja de reconocer una sola forma

**Gate** (ADR-018 rev. b, `PeanoRF/Meta/AxiomCheck.lean`)
- Descubrimiento de relaciones de derivabilidad **por TELESCOPIO** en lugar de por la
  forma fija `List Formula → Formula → Prop`. Medía 6 de 11: fuera quedaban `LK₀`, `LKc`,
  `LKh` (FOL, secuentes y Hauptsatz) y `Prf`, `Prf₀` (RPP, Hilbert) — **67 constructores**.
- **CLÁSICO se decide por el TIPO del constructor** (patrón de la doble negación en sus
  dos escrituras, más `(¬∀A) ⇒ ∃¬A`). La lista por nombre queda como refuerzo.
  Lo forzó medir que `PrfH.p3` —que **es** la DNE— pasaba dentro de la capa ω.
- La capa ω exige ahora `omegaAllowedForeignCtors` (**vacía**): estar en `PeanoRF.Omega.*`
  ya no basta.
- El inventario publica además los **casi-candidatos** rechazados por el telescopio.

**`check-doc-sync.bash`**
- **Si no puede medir, es ROJO.** Sin `lake` en el `PATH` se saltaba [A] y daba exit 0.
- [A] se parte: la **línea canónica** bloquea; la prosa de cabecera sólo avisa.

**Limpieza**
- `git rm CRASH` (fichero ajeno colado por un `git add -A` en `b786238`).
- Retirado un argumento `simp` no usado en `PeanoRF/HA/Arith.lean`.

Sin cambios en FOL ni en ROBINSON_PlusPlus. Footprints propios re-medidos: **sin cambios**.

### Changed (2026-09-16) — ⚠️ EL SUJETO CAMBIA: todo H2 migra a `⊢ᵢ` (ADR-017)

Aguas arriba, en diez días, ROBINSON_PlusPlus declaró **las cinco nociones de
derivabilidad** (`REFERENCE.md §0bis`) y FOL estrenó un estrato entero. Dos hechos
invalidan la base sobre la que se construyó H2:

1. ⛔ **`FOL.Derives` NO PUEDE TENER SOLIDEZ.** `FOL/cuarentena/Inconsistencia.lean`
   demuestra `inconsistencia_de_cualquier_solidez`: *cualquier* testigo del enunciado da
   `False`. 7 axiomas habitantes, declarado **HERRAMIENTA**. De `axioms ⊢ φ` no se concluye
   nada sobre ℕ₀ ⇒ el espejo moría ahí. Es **M-9 confirmado** y llevado más lejos.
2. ⛔ **La ω-regla es ahora un CONSTRUCTOR** (`Derives.gen_rule`), no un axioma.

Y `Derives₀` tampoco sirve: 0 habitantes-axioma y solidez en el build, pero `dne_rule`,
`dne_schema` y `forall_not_ex_not` son **constructores** ⇒ clásico ⇒ espejo de PA, no de HA.

- **`PeanoRF/Calculus/DerivesI.lean`** — `⊢ᵢ`: los 18 constructores no clásicos de
  `Derives₀`. Único punto con **0 habitantes-axioma + finitario + intuicionista**.
  `derivesI_to_derives0` (footprint `propext`) se prueba por inducción **legítima**.
- **`PeanoRF/Calculus/Eq.lean`** — el coste de la migración: cinco lemas reprobados
  (`eqI_refl/symm/trans/congr_succ`, `specI`). Los teoremas de `⊢` no bajan a `⊢ᵢ`.
- `HA/Axioms.lean` y `HA/Arith.lean` migrados enteros.

### Added (2026-09-16) — H2 CERRADO: el caso con parámetro

- **`succ_add`**: `∀x. σa + x = σ(a + x)`, con `Closed a`.
- **`HA.Closed`** — y es la parte fina del resultado: `liftTerm 0 a = a` **NO basta**.
  `inductionFormula` usa `liftFormula 1 φ`, así que hacen falta las invariancias **a todo
  nivel y bajo sustitución**. Con parámetro **abierto** no hay generalización finitaria:
  habría que meter la **clausura universal** de la instancia en el contexto. Eso es lo que
  compraba la ω-regla, y es el primer sitio donde ADR-016 cuesta algo de verdad.
- **ADR-018 — cuarto control del gate, a nivel de CONSTRUCTOR.**

### Fixed (2026-09-16) — el gate se había quedado ciego SIN AVISAR

`FOL.MetaRules.gen` pasó de axioma a constructor ⇒ footprint `[propext]` ⇒ **el eje
finitario dejó de vigilar la ω-regla**: el contador de la capa ω bajó de 5 a 4 usos y el
gate siguió diciendo OK. Es ADR-015 otra vez, pero por **deriva aguas arriba**. Arreglado
con el control de constructores, probado con smoke test en los dos ejes.

**Regla general que sale de aquí**: cuando una dependencia cambia la naturaleza de un
símbolo (axioma → constructor), los controles que lo vigilaban **caducan en silencio**.

### Measured (2026-09-16)

| símbolo | footprint |
|---|---|
| `PeanoRF.HA.succ_add` (sobre `⊢ᵢ`) | `propext, Classical.choice, Quot.sound` |
| `ROBINSON_PlusPlus.Full.succ_add_prim` (sobre `⊢`) | + **`MetaRules.imp_intro`, `ax_induction_prim`** |
| `PeanoRF.Calculus.derivesI_to_derives0` | `propext` |

---

### Added (2026-09-06, H2) — el conjunto de axiomas de HA

- **`PeanoRF/HA/Axioms.lean`** — HA axiomatizada **sin postular derivabilidad** (M-8):
  `ctx insts = axioms ++ insts.map inductionFormula`. La instancia de inducción entra por
  `Derives.hyp`, no por un `axiom` de Lean. Con `ax'`, `ind`, `mono`, `induction_object`.
- 🔑 **`gen_closed`** — sobre un contexto **cerrado**, la generalización es finitaria
  (`Derives.intro_forall`): **la ω-regla `gen` no hace falta**. La hipótesis se cumple por
  cómputo del kernel — `axioms_lift : axioms.map (liftFormula 0) = axioms` es un `rfl`,
  porque los axiomas de Q⁺⁺ son sentencias cerradas. Footprint de `gen_closed`: `[propext]`.
- **`PeanoRF/HA/Arith.lean`** — `zero_add` (`∀x. 0 + x = x`) **reprobado sin ω-reglas y sin
  `ax_induction`**. El tipo declara la instancia de inducción usada: contabilidad de
  matemática inversa que sale gratis del diseño.
- Verificaciones puntuales `#assert_finitary` / `#assert_intuitionistic` sobre `zero_add`,
  `induction_object` y `gen_closed`, en el gate.
- `sondeos/lift_probe.lean` y `sondeos/h2_probe.lean`.

### Measured (2026-09-06, H2) — el coste de prescindir de la ω

| símbolo | footprint |
|---|---|
| `PeanoRF.HA.zero_add` (finitario) | `propext, Classical.choice, Quot.sound` |
| `ROBINSON_PlusPlus.Full.zero_add` (ω) | + **`MetaRules.gen`, `MetaRules.imp_intro`, `ax_induction`** |
| `PeanoRF.HA.gen_closed` | `propext` |

**Tres axiomas menos, misma estructura de prueba y sin reformular matemática.** El
`Classical.choice` que queda es la deuda META heredada de la codificación `String` de RPP.

⚠️ La medición es de un caso **sin parámetro libre**. El caso con parámetro (`succ_add`,
`add_comm`) sigue pendiente y es donde el manejo de índices De Bruijn puede morder.

---

### Added (2026-09-06, noche) — alcance fijado, ADR-016 y capa ω

- **Alcance del proyecto definido** (`PLANNING.md` reescrito): PeanoRF vuelca Peano al
  lenguaje FOL⁼ + ROB++ como **espejo** — PeanoRF fundacional, Peano computacional —, que
  visto de cerca es una **interpretación de realizabilidad**. Objetivo último: servir de
  meta-lenguaje para FOL y ROB++, con su techo explícito (Gödel II).
- **ADR-016 — el núcleo es HA FINITARIA; la ω-lógica vive en una capa aparte.**
  Nace de dos hechos medidos: `Full/Induction.lean:166` postula
  `axiom ax_induction : axioms ⊢ inductionFormula φ` (falso bajo un `⊢` finitario: Q no
  demuestra inducción), y **99 de 521 declaraciones de ROB++ (19 %) pasan por ω-reglas**.
  Sin la separación, PeanoRF no sería HA sino ω-lógica = aritmética verdadera, con `⊢` no
  r.e. — lo que mata el objetivo de meta-lenguaje y desdibuja el fundacional.
- **MANDATORIES M-7, M-8, M-9**: núcleo finitario · la inducción entra en el **conjunto de
  axiomas** · la soundness se demuestra **sólo del fragmento finitario**.
- **`PeanoRF/Omega/Basic.lean`** — capa ω declarada, aislada y **contada** en cada build.
  Cinco alias sancionados (`gen`, `imp_intro`, `raa`, `or_elim`, `ex_elim`).
- **Tercer eje en el gate** (finitario) + comando `#assert_finitary`. Probado en los dos
  sentidos: error fuera de la capa ω, recuento dentro (hoy 5).
- `sondeos/omega_probe.lean` y `sondeos/peano_probe.lean`.

### Measured (2026-09-06, noche)

| Medición | Resultado |
|---|---|
| ROB++ (Minimal+Full, 521 decls) | **99 (19 %)** con ω-reglas · **0 con lógica clásica** |
| desglose | `gen` 70 · `ex_elim` 64 · `or_elim` 64 · `imp_intro` 42 · `raa` 13 |
| `axiom` de Lean en ROB++ | 5, de los que 4 son meta-axiomas de esquema (`ax_induction` con **30** dependientes) |
| **Peano al completo** | **2207 decls · 2193 limpias (99,4 %)** · las 14 sucias en `Initiality` (7), `Prelim.Classical` (5), `PureAxioms` (2) |

La última fila es la que hace viable el volcado: **Peano ya es constructivo** salvo un
0,6 % localizado y nombrado.

### Note (2026-09-06, noche) — un peligro identificado, no un bug

`raa` e `imp_intro` toman premisas META (`Γ ⊢ A → Γ ⊢ B`), satisfacibles **vacíamente**.
Con una soundness de `Derives` hacia ℕ₀ y un testigo `¬(axioms ⊢ ψ)` con ψ verdadera se
derivaría `¬⟦ψ⟧`. **ROBINSON_PlusPlus no está afectado**: enuncia Gödel I con `Prf`
(aritmetizada, finitaria) y su puente `prf_to_derives` va en un solo sentido. Pero PeanoRF
es el proyecto que fabricaría el ingrediente que falta — de ahí M-9.

---

### Added (2026-09-06, tarde) — directiva fundacional y gate de pureza

- **MANDATORIES M-1..M-6 fijadas** (ADR-013, ADR-014). Las dos fundacionales:
  - **M-1 — la lógica de nivel OBJETO es INTUICIONISTA.** Prohibidos los tres axiomas
    clásicos de FOL (`MetaRules.dne`, `Theorems.Neg.dne`,
    `Theorems.Quantifiers.forall_not_impl_exists_not`). Sin baseline ni excepción.
  - **M-2 — las pruebas en Lean son CONSTRUCTIVAS**, diana `⊆ {propext, Quot.sound}`.
  - **M-3 — `ℕ₀` de peanolib** como único natural.
- **`PeanoRF/Meta/AxiomCheck.lean`** — gate de compilación de dos ejes, corre en cada
  `lake build`. Comandos `#assert_no_classical`, `#assert_intuitionistic`,
  `#assert_constructive_footprint`.
- **`sondeos/`** — mediciones fuera del build. `axiom_probe.lean` inventaría el footprint
  de las dependencias; `sondeos/README.md` guarda la medición que fundamenta ADR-013.

### Changed (2026-09-06, tarde)

- **Import surface de FOL estrechado a la mitad demostrativa** (M-5): fuera
  `FOL.Semantics`, `FOL.Soundness`, `FOL.Completeness`, `FOL.Compacity`. Ahí viven los 52
  `Classical.choice` de FOL y los únicos usos de sus tres axiomas clásicos. Build:
  25 → **21 jobs**.

### Fixed (2026-09-06, tarde)

- **El gate no mordía.** Su primera versión toleraba `Classical.choice` **por nombre de
  axioma** (con el argumento de que llegaba heredado de RPP), y un smoke test
  — `open Classical in theorem smoke (p : Prop) : p ∨ ¬p := em p` — lo atravesó
  clasificado como «deuda heredada». Ahora la tolerancia va **por procedencia**: solo
  cuenta como heredado lo que entra atravesando una constante de
  `FOL`/`ROBINSON_PlusPlus`/`Peano`. Ambos ejes verificados con smoke test (ADR-015).

### Measured (2026-09-06) — solo `#print axioms` mide; los `import` no

| Librería | Decls | Limpias | Nota |
|---|---:|---:|---|
| `Peano` (`PeanoNat.Axioms`) | 192 | **192** | 0 `axiom` — el cimiento ya cumple la diana |
| `FOL` (barrel completo) | 397 | 332 | 13 `axiom`, de los que **solo 3 son clásicos**; todos los usos, en la mitad que no importamos |
| `RPP.Minimal.Axioms` | 313 | 269 | ⚠️ `axioms` misma arrastra `Classical.choice` vía las primitivas `String` de la codificación |

---

### Added (2026-09-06)

- **Andamiaje inicial del proyecto**, generado desde `lean4-project-template` y
  enriquecido con lo aprendido en los proyectos hermanos (ROBINSON_PlusPlus, Peano,
  FOL, AczelSetTheory), que iban por delante de la plantilla:
  - `AI-GUIDE.md` **§27** — control de sincronía documentación ↔ código, con la regla
    de oro «no basta con arreglar el banner» (viene de ROBINSON_PlusPlus, 2026-08-23).
  - `AI-GUIDE.md` — banner de **lectura obligatoria de `DECISIONS.md` §MANDATORIES**
    antes de tocar cualquier `.lean` (viene de AczelSetTheory).
  - `check-doc-sync.bash` — versión **genérica** del control de ROBINSON_PlusPlus:
    detecta la librería desde `lakefile.lean` y concentra lo específico del proyecto en
    un bloque `CONFIGURACIÓN`. Controles [A] cifras, [B] símbolos muertos (aviso),
    [C] proyección, [D] marcas de tiempo.
  - `WORKFLOW.md` — reescrito con el **modo IA como flujo principal** y `git-lock.bash`
    como modo humano legacy (viene de ROBINSON_PlusPlus, 2026-06-05).
  - `DECISIONS.md` — sección MANDATORIES en **formato tabla con columna de
    verificación** (viene de AczelSetTheory).
  - `update-toolchain.bash` — versión con `--check`, consulta de la última estable y
    reversión automática (viene de AczelSetTheory).
  - `Makefile` — targets `docsync` / `docsync-quick`; guarda de `VERSION`.
  - `.claude/commands/docsync.md` — comando `/docsync`.
- `lakefile.lean` con las tres dependencias locales: `FOL`, `ROBINSON_PlusPlus`,
  `peanolib`. Toolchain v4.31.0, el mismo de las tres.
- `PeanoRF/Prelim.lean` — punto único de contacto con las librerías aguas arriba.
- Build verificado: 25 jobs, 0 `sorry` (hoy 21 tras estrechar el import de FOL).

### Pending

- **Definir el alcance matemático del proyecto** (Fase 0 de `NEXT-STEPS.md`). Hasta
  entonces, `REFERENCE.md`, `DEPENDENCIES.md` y `PLANNING.md` documentan solo el
  andamiaje, y lo dicen explícitamente.
- Poner `metaDebtIsError := true` cuando ROBINSON_PlusPlus sea constructivo a nivel meta.

---

## Versioning Conventions

- **MAJOR**: Breaking API changes or new foundational axiom
- **MINOR**: New backward-compatible functionality
- **PATCH**: Bug fixes and backward-compatible corrections

## Links

- [Repository](https://github.com/julian1c2a/PeanoRF)
- [Issues](https://github.com/julian1c2a/PeanoRF/issues)
