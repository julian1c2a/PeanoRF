# Current Project Status — PeanoRF

**Última actualización:** 2026-09-21
**Autor**: Julián Calderón Almendros

> 🚨 **AUDITORÍA EXTERNA 2026-09-21** — con los tres controles locales en verde, la **CI
> llevaba dos días en ROJO** (mi propio control `[D]` miente bajo checkout shallow) y **el
> gate se había quedado ciego a `Derives₀`** porque FOL generizó su sintaxis: 45
> constructores vigilados → 42, y 12 clásicos → 9, sin que este proyecto cambiara nada.
> Las dos cosas arregladas y **probadas** (ADR-030 enmendado, ADR-031). No hubo brecha en la
> tesis; lo que estuvo apagado fue la guardia. Y se activó `[B]` —que cazó **dos teoremas
> anunciados que no existían**— y se escribió `[H]`, la dirección contraria (ADR-032). Van
> **siete controles**, y una trampa nueva medida: `grep` falla en silencio con los emoji de
> 4 bytes (ADR-033).
>
> **Estado: H3bis cerrado — la separación `⊢ᵢ ≠ ⊢₀` es un TEOREMA.**
> **H3ter en curso: los 34 axiomas de `coreAxioms` ya están BARRADOS; falta el esquema
> de inducción.**
> PeanoRF vuelca Peano al lenguaje FOL⁼ + ROB++ de forma constructiva: un **espejo** donde
> lo demostrado se conserva en Peano (`PLANNING.md` §1). El **núcleo es HA finitaria** y la
> ω-lógica vive aislada y contada en `PeanoRF.Omega.*` (**ADR-016**).
> 🏁 **H3: la solidez de `⊢ᵢ` es CONSTRUCTIVA** — `derivesI_soundness` mide
> `[propext, Quot.sound]`. El espejo no sólo es un teorema: es un teorema intuicionista.
>
> **H2 CERRADO** (2026-09-16), y sobre un cálculo nuevo. Aguas arriba se demostró que
> `FOL.Derives` **no puede tener solidez** (`inconsistencia_de_cualquier_solidez`): es
> HERRAMIENTA, no SUJETO. Todo H2 se ha **migrado a `⊢ᵢ`**, el cálculo intuicionista
> finitario de `PeanoRF/Calculus/DerivesI.lean` (ADR-017). `zero_add` y **`succ_add` (el
> caso con parámetro)** están probados ahí, sin ω-reglas y sin `ax_induction`.
>
> **Cifras canónicas** (las verifica `check-doc-sync.bash`, AI-GUIDE §27):
> **50 jobs · 17 módulos propios · 0 sorry vigentes · 0 axiom propios**.
>
> 🏁🏁🏁 **H3bis CONSEGUIDO — `⊢ᵢ` NO es `⊢₀`, y ahora es un TEOREMA.**
>
> ```
> derivesI_ne_derives0 : ∃ φ, ([] ⊢₀ φ) ∧ ¬([] ⊢ᵢ φ)      [propext, Quot.sound]
> ```
>
> Hasta el 2026-09-17 los 22 teoremas que el proyecto tenía entonces valían **palabra por
> palabra** para `⊢₀`:
> sustituyendo `⊢ᵢ` por `⊢₀` en todo el árbol, todo seguía compilando. La tesis —«PeanoRF
> es HA y no PA»— era **arquitectónica**: la sostenían la elección de cálculo y el gate, no
> una demostración. Ya no.
>
> Detrás van la **propiedad de disyunción** (`disjunction_property`) y la **de existencia**
> (`existence_property`), y la segunda es la sombra sintáctica de la realizabilidad: el
> testigo de un existencial demostrado **es** el cálculo que el lado Peano del espejo
> tendría que ejecutar.
>
> ⭐⭐ **DEUDA META HEREDADA: CERO** (2026-09-18, ADR-024). `HA.ctx` pasa de `axioms` a
> **`coreAxioms`**, que es net-0 — y no es un truco de footprint: los cinco axiomas sucios
> eran del **verificador object de demostraciones** de RPP y no pintaban nada en el contexto
> de la Aritmética de Heyting. Todo el proyecto mide ahora `⊆ {propext, Quot.sound}`, y
> **`metaDebtIsError := true`**: el eje META deja de avisar y rompe el build. Lo destapó el
> agente de RPP midiendo SU puerta en vez de aceptar mi diagnóstico de la mía.
>
> ⛔ **H3ter: el enunciado ingenuo es FALSO, y está medido** (2026-09-18).
> `ctx [] ⊢ᵢ (foo < bar ∨ foo = bar ∨ bar < foo)` **es derivable** con `foo`, `bar` símbolos
> ajenos al lenguaje: `Term` es genérica y `elim_forall` instancia con cualquier término. Y
> ninguna rama lo es. ⇒ **HA sobre la sintaxis genérica NO tiene la propiedad de
> disyunción**; el teorema de Kleene es sobre SU lenguaje.
> (`sondeos/junk_probe.lean`; la no-derivabilidad de las ramas es argumento por solidez,
> **no medida todavía**. Informado a FOL y RPP: `doc/HALLAZGO-SINTAXIS-GENERICA-2026-09-18.md`.)
>
> ✅ **Etapa 1 hecha** (ADR-025): la barra es **relativa a la teoría**, `Slash T f`, y H3bis
> queda como su instancia `T = []` — intacto. El teorema general es
> `disjunction_property_of_slashed : (∀ g ∈ T, Slash T g) → T ⊢ᵢ A ∨ B → T ⊢ᵢ A ∨ T ⊢ᵢ B`.
>
> ✅ **Etapa 2, pieza (b) HECHA** (2026-09-18): **`derivesI_collapse`**. De una derivación
> que instancia con símbolos ajenos sale otra que no lo hace, con el mismo contexto y la
> misma conclusión colapsados. `[propext, Quot.sound]`, y las conmutaciones en `[propext]`.
> ⇒ El contraejemplo deja de ser obstáculo y pasa a ser **lo que justifica la restricción**.
>
> ✅ **Etapa 2, pieza (1) HECHA** (2026-09-18): **`Slash T D`**, la barra con parámetro de
> **dominio**. Las cláusulas de `∀` y `∃` cuantifican sobre `D`, no sobre todos los términos
> — sin eso `ax19_lt_trichotomy` no se puede barrar. H3bis **sobrevive** como la instancia
> `D = fun _ => True`, **intacto y con el mismo footprint**.
>
> ⚠️ `D` entra en L2 como una **CLAUSURA**, `hDsub : ∀ ρ, (∀n, D (ρ n)) → ∀t, D (substT ρ t)`,
> que es lo que piden `elim_forall` e `intro_ex`. Con `D = ClosedQTerm` esa clausura es
> **FALSA**, y por eso hace falta el colapso delante: `HA/Domain.lean` demuestra
> `closed_collapse_subst`, su versión con `collapseT LQ`.
>
> 🏁🏁 **ETAPA 2 CERRADA** (2026-09-18): **la FORMA (c)**. L2 demuestra la barra de la
> instancia **COLAPSADA**, `Slash T D (collapseF L (substF ρ f))`, y con ella las dos
> clausuras de `HA/Domain.lean` encajan **sin adaptador ninguno**:
>
> ```
> qDisjunctionProperty : (∀ g ∈ T, Slash T ClosedQTerm (…g…)) → T ⊢ᵢ A ∨ B → T ⊢ᵢ A ∨ T ⊢ᵢ B
> qExistenceProperty_numeral : … → ∃ t, ClosedQTerm t ∧ (∃n, ⊢ᵢ t =eq n̅) ∧ T ⊢ᵢ A[t]
> ```
>
> ⭐ **La DP para CUALQUIER teoría de Q⁺⁺ cuyos axiomas estén barrados**, y el testigo de la
> existencia sale **demostrablemente igual a un NUMERAL**. Todo en `[propext, Quot.sound]`.
>
> ⚠️ La hipótesis «`A ∨ B` es una sentencia del lenguaje» va como **una sola ecuación**,
> `collapseF LQ (substF zeroS (A ∨ B)) = A ∨ B` — cerrada porque la sustitución no la toca,
> del lenguaje porque el colapso no la toca. Comprobado que **no es vacía**, con un ejemplo
> que la cumple por `rfl`.
>
> 🏁 **ETAPA 3, primera mitad** (2026-09-18): **28 de los 34 axiomas caen de un solo
> lema** — los de **HARROP**, donde la barra COINCIDE con la derivabilidad. Y con ellos,
>
> ```
> haDisjunctionProperty : la DP de HA reducida a TRES obligaciones, y ni una más
> ```
>
> 1. la **consistencia** de la teoría — el precio clásico de la barra, no demostrable aquí;
> 2. 🏁 **LOS 6 YA ESTÁN** (`HA/SlashAxioms.lean`): `ax13`, `ax14`, `ax19`, `ax21`,
>    `ax_L2` y `ax_L3`. ⇒ **34 de 34.**
> 3. ✅ **el esquema de inducción — DESCARGADO** (2026-09-21, ADR-034) para instancias de
>    **Harrop**, que es lo que `isHarrop (inductionFormula φ) = isHarrop φ` (por `rfl`,
>    **sin axiomas**) permite. Y con él `hlift`. ⇒ `haDisjunctionProperty_harrop`, y una
>    instancia trabajada con `phiZeroAdd` donde las tres condiciones salen por `rfl`: **no
>    es vacuo**. ⛔ El atajo NO cubre instancias con `∨` o `∃`.
>
> ⇒ **Quedan TRES hipótesis**: `hcon`, `hNum` y `hIn`.
>
> ⛔ **Y medido el 2026-09-21: `hNum` sobre el lenguaje COMPLETO es INALCANZABLE, y para `−`
> es FALSA.** `−` aparece **en un único axioma de los 34**, y condicionado a `x ≤ y`: Q⁺⁺ no
> dice nada de `5̄ − 7̄`. No es falta de ingenio, es falta de axioma.
>
> ✅ **Lo que SÍ se alcanza — el FRAGMENTO ARITMÉTICO** (`HA/Fragment.lean`): **17 de los 34**
> axiomas usan sólo `0 σ + * ^`; **son sentencias del lenguaje de los numerales** (por `rfl`);
> de ellos **sólo dos no son de Harrop** —`ax13` y `ax19`— y **los dos ya están barrados**.
> Ahí `hNum` **ya está demostrada**: es `closed_term_eq_numeral`. Y **`hIn` desaparece**.
> ⇒ **Sobre el fragmento queda UNA sola hipótesis: `hcon`.**
>
> ⭐ La capa `LQ`, etiquetada como ANDAMIO por no tener uso portante, resulta ser **la
> signatura de ese fragmento**. El andamio era el camino.
>
> 🏁🏁🏁 **Y LA DP DEL FRAGMENTO YA ESTÁ** (2026-09-21, ADR-036):
>
> ```
> qDisjunctionProperty_arith : ¬(ctxA [] ⊢ᵢ ⊥) → ctxA [] ⊢ᵢ A ∨ B → ⊢ᵢ A ó ⊢ᵢ B
> ```
>
> **Una sola hipótesis: la consistencia.** `hNum` dejó de ser hipótesis y es un teorema
> (`hNum_fragment`, vía `closed_of_grounded`); `hIn` no aparece; `hInd` y `hlift` salen por
> `rfl`. Todo en `[propext, Quot.sound]`.
>
> ⚠️ **Y el fragmento de 17 NO es maximal.** `τ` entra casi gratis — `ax25` y `ax26` son de
> Harrop y **determinan `τ` sobre todo numeral SIN inducción ninguna**. Hecho:
> `qDisjunctionProperty_arithT`, **19 axiomas, 6 símbolos y la misma única hipótesis**.
> ✅ **`%₂` también HECHO**: `qDisjunctionProperty_arithTM`, **22 de los 34**, siete
> símbolos, la misma única hipótesis. ⭐ Y evaluarlo **NO necesitó consistencia**: la
> refutación va dentro de una rama de `elim_or`, bajo hipótesis. ⛔ `/₂` bloquea a
> `::`, `##` y `Π_p` (porque `pair` usa `/₂`, medido), `√` no se deja fijar, y `−` está
> **subdeterminado**: aparece en UN solo axioma y condicionado.
>
> 🏁🏁 `haDisjunctionProperty_core`: **la DP de HA con `coreAxioms` YA DESCARGADO**.
> Lo que queda va como hipótesis, **todas dichas y ninguna escondida**:
>
> | hipótesis | qué es | ¿se puede demostrar aquí? |
> |---|---|---|
> | `hcon` | la consistencia de la teoría | ⛔ no (Gödel) |
> | `hlift` | el contexto invariante bajo levantamiento | ✅ si las instancias son cerradas |
> | `hNum` | todo término anclado es demostrablemente un numeral | ⏳ faltan 8 de los 13 símbolos |
> | `hIn` | `∈` decidible sobre términos anclados | ⛔ pide inducción sobre listas |
> | `hInd` | el esquema de inducción barrado | ⏳ |
>
> ⚠️ Dos correcciones que salió de medir: (a) la lista dura es de **6**, no de 5, y no es la
> que estaba escrita — `ax29_sub_witness` SÍ es de Harrop, y `ax14_sqrt_le` y
> `ax_L2_in_cons` NO lo son; (b) **`LQ` no servía**: tiene 5 símbolos y los axiomas usan
> **13**, así que colapsar con ella los mutila. El dominio pasó a `Grounded LQpp`, definido
> **por sus dos clausuras** en vez de por un inductivo, y así vale para cualquier signatura.
>
> ⏳ **Etapa 3**, medida: de los 34 axiomas de `coreAxioms`, **25** salen con `specI`, ~4 con
> `elim_impl`, y **5** piden decidir en el meta (`ax19`, `ax21`, `ax13`, `ax_L3`, `ax29`).
> Más el esquema de inducción. ✅ `closed_term_eq_numeral` ya está (`HA/Numerals.lean`).
>
> ⛔ **Las dos son de la LÓGICA `⊢ᵢ`, sobre contexto VACÍO — no son las de HA.** Son las
> marcas que en general separan HA de PA, pero **para HA no se siguen**: las instancias de
> inducción viven en `HA.ctx`, y barrar el esquema de inducción es el caso difícil y está
> sin hacer. Misma reserva que lleva `consistI_syn`; se corrigió el 2026-09-18 al
> reauditar, porque el listón sube igual para los resultados que gustan.
>
> ⚠️ Al construirlo, el gate cazó un `Classical.choice` **propio** — un `simp` en
> `upS_singleS` — que contaminaba siete declaraciones. Reescrito con `if_pos`/`if_neg`
> explícitos. Es la primera vez que el eje META muerde sobre código nuestro.
>
> 🔎 **Auditoría del 2026-09-17 (tarde)**: el gate está verde y los footprints no se
> han movido, pero la auditoría de **cobertura** encontró dos agujeros y los cerró
> (ADR-018 rev. b): el criterio por tipo reconocía **una forma fija** y dejaba fuera
> `LK₀`/`LKc`/`LKh`/`Prf`/`Prf₀` — **67 constructores**; y la última lista por nombre
> dejaba pasar la **DNE en la capa ω** (`PrfH.p3`). Ahora: descubrimiento por
> **telescopio**, clásico **por lo que la regla dice**, capa ω con lista explícita
> (vacía), e inventario que publica también los **casi-candidatos**.
>
> ⚠️ **La cifra de `jobs` NO es un invariante del proyecto**: depende de qué dependencias
> locales haya que reconstruir. El 2026-09-16 osciló entre 30 y 31 según el estado de la
> caché de FOL, y el control [A] dio VERDE con la cifra desfasada. Las otras tres sí son
> invariantes; ésta se lee con esa reserva.

---

## Resumen ejecutivo

| Métrica | Valor |
|--------|-------|
| Módulos propios | 17 (`Prelim`, `Calculus/{DerivesI,Eq,Soundness,Consistency,Slash,Subst,SubstDerives,Collapse}`, `Meta/AxiomCheck`, `Omega/Basic`, `HA/{Axioms,Arith,Numerals,Domain,SlashAxioms,Fragment}`) |
| Módulos con 0 `sorry` | 17 / 17 |
| Teoremas propios | 202 |
| Definiciones propias | 9 (el álgebra de sustituciones, `fdepth`, `Slash`) |
| Notaciones propias | 0 |
| `axiom` de Lean propios | 0 |
| Build | ✅ 50 jobs (ver la reserva del banner) |
| Lean | v4.31.0 |
| Dependencias | `FOL`, `ROBINSON_PlusPlus`, `peanolib` (rutas locales) |
| Convención de nombres | Mathlib-style (ver `NAMING-CONVENTIONS.md`) |

---

## Estado por módulo

| Módulo | Teoremas | Definiciones | Sorry | Estado |
|--------|----------|-------------|-------|--------|
| `PeanoRF/Prelim.lean` | 0 | 0 | 0 | 🔄 In progress |
| `PeanoRF/Meta/AxiomCheck.lean` | 0 | 0 | 0 | ✅ Completo (gate de 3 ejes en producción) |
| `PeanoRF/Omega/Basic.lean` | 0 | 5 | 0 | ✅ Capa ω declarada (5 alias sancionados) |
| `PeanoRF/HA/Axioms.lean` | 7 | 1 | 0 | ✅ Conjunto de axiomas + `gen_closed` |
| `PeanoRF/HA/Arith.lean` | 2 | 2 | 0 | ✅ `zero_add` y `succ_add` sobre `⊢ᵢ` |
| `PeanoRF/Calculus/DerivesI.lean` | 2 | 1 | 0 | ✅ El cálculo `⊢ᵢ` + puentes |
| `PeanoRF/Calculus/Eq.lean` | 5 | 0 | 0 | ✅ Igualdad sobre `⊢ᵢ` |
| `PeanoRF/Calculus/Soundness.lean` | 2 | 0 | 0 | 🏁 **H3**: solidez **CONSTRUCTIVA** (`propext, Quot.sound`) |

*Códigos*: ✅ Completo · 🧊 Congelado · 🔶 Parcial · 🔄 En curso · ❌ Pendiente

---

## Estado de las dependencias (2026-09-06)

| Proyecto | Rama | Toolchain | Nota |
|---|---|---|---|
| `FOL` | `master` | v4.31.0 | Verde. 13 `axiom`, de los que **3 son clásicos de nivel objeto** y solo se usan desde la mitad modelo-teórica, que NO importamos (M-5) |
| `ROBINSON_PlusPlus` | `via-c-adr020` | v4.31.0 | Frente abierto con parada **conocida y localizada** en `Meta/MpCodePrf.lean`; `master` verde. Solo importamos `Minimal/` (ADR-012). ⚠️ **No constructivo a nivel META todavía** (44/313 con `Classical.choice`, incluida `axioms`); sí a nivel objeto. Deuda contabilizada por el gate |
| `Peano` | `master` | v4.31.0 | Verde. **192/192 declaraciones limpias, 0 `axiom`** — el cimiento aritmético ya cumple la diana |

---

## Logros recientes

- Proyecto creado desde `lean4-project-template` y **enriquecido** con lo que los
  proyectos hermanos habían aprendido después de la última propagación (2026-07-12):
  el control `check-doc-sync.bash` (§27), el banner de MANDATORIES obligatorias, el
  `WORKFLOW` centrado en el modo IA, y las MANDATORIES en formato tabla verificable.
- Las mejoras se han devuelto también a `lean4-project-template` en su forma genérica.
- Build verde con las tres dependencias enganchadas por ruta local.
- **Directiva fundacional fijada** (2026-09-06): pureza constructiva en dos ejes y `ℕ₀`
  como único natural — M-1..M-3, ADR-013/014.
- **Gate de pureza en producción y PROBADO** con smoke tests en los dos ejes (ADR-015).
  Al probarlo se encontró y corrigió un fallo real: toleraba `Classical.choice` por
  nombre de axioma, de modo que un `Classical.em` propio pasaba como deuda heredada.
- **Import surface de FOL estrechado** a la mitad demostrativa: fuera Semantics,
  Soundness, Completeness y Compacity (donde vive todo lo clásico).
  El build bajó de 25 a 21 jobs.
- **Alcance fijado y ADR-016**: el núcleo es **HA finitaria**; la ω-lógica queda aislada
  en `PeanoRF.Omega.*`. Nace de medir que **99 de 521 declaraciones de ROB++ (19 %)
  pasan por ω-reglas**, y de que `Full/Induction.lean` postula
  `axiom ax_induction : axioms ⊢ inductionFormula φ` — falso bajo un `⊢` finitario.
- **Tercer eje en el gate** (finitario), con smoke test en los dos sentidos: error fuera
  de la capa ω, recuento dentro (hoy 5).
- **H2 · la inducción deja de ser un axioma.** `HA.ctx insts = axioms ++ instancias`, y la
  instancia entra por `Derives.hyp`. Medido:

| símbolo | footprint |
|---|---|
| `PeanoRF.HA.zero_add` (finitario) | `propext, Classical.choice, Quot.sound` |
| `ROBINSON_PlusPlus.Full.zero_add` (ω) | `propext, Classical.choice, Quot.sound,` **`FOL.MetaRules.gen, FOL.MetaRules.imp_intro, ROBINSON_PlusPlus.Full.ax_induction`** |
| `PeanoRF.HA.gen_closed` | `propext` |

La versión finitaria **elimina tres axiomas**: la ω-regla, la meta-regla de implicación y
la derivabilidad postulada de la inducción. El `Classical.choice` que queda es la deuda
META heredada de la codificación `String` de RPP, no nuestra.

---

## Trabajo pendiente

- [x] ~~**H2 completo**~~ → `⊢ᵢ`, `ctx`, `gen_closed`, `Closed`, `zero_add` y `succ_add`.
- [x] ~~**H3 · transferencia**~~ → `derivesI_soundness` y `derivesI_consistent`, heredando
      `derives0_soundness`. **El espejo ya es un teorema.**
- [x] ~~**H3 · inducción directa**~~ → hecha, 18 casos. Pero **no basta**: la conjetura de
      ADR-019 era falsa.
- [x] ~~**H3 · el último `Classical`**~~ → 🏁 **RESUELTO**. Estaba en **una línea** de
      `FOL.Metamath.Semantics.shift_updateEnv_comm`: un `omega` cerrando por contradicción
      una meta **fuera de su lenguaje** (de tipo `D`). Sustituido por `absurd`.
      ⇒ **`derivesI_soundness : propext, Quot.sound`** — la solidez de la lógica
      intuicionista, demostrada intuicionistamente.
- [x] ~~El arreglo de FOL~~ → aceptado y commiteado allí (`6d47e5b`), blindado en su
      `check-footprints.bash`.
- [x] ~~`forbiddenConstructors` por NOMBRE~~ → **reescrito POR TIPO** (ADR-018, 2026-09-17)
      tras una auditoría que midió **9 de 12 constructores clásicos sin vigilar**. El gate
      publica ahora un **inventario** de las relaciones de derivabilidad que detecta.
- [x] ~~El tipo, por UNA FORMA FIJA~~ → **por TELESCOPIO** (ADR-018 rev. b, 2026-09-17
      tarde). Medía 6 relaciones de 11; `LK₀`, `LKc`, `LKh`, `Prf` y `Prf₀` quedaban fuera
      — **67 constructores**. Ahora ve las 11 y vigila 90.
- [x] ~~Clásico por NOMBRE~~ → **por lo que la regla DICE** (el patrón de la doble
      negación en el tipo). Lo forzó medir que `PrfH.p3` —la DNE con otro nombre— pasaba
      **dentro de la capa ω**, con el gate imprimiendo «intuicionista puro».
- [x] ~~La capa ω como comodín~~ → ahora exige entrada explícita en
      `omegaAllowedForeignCtors`, **vacía**. Relaja en efectividad (M-7), nunca en M-1.
- [x] ~~`check-doc-sync.bash` daba VERDE VACUO~~ → sin `lake` en el `PATH` se saltaba el
      control [A] entero y anunciaba «sin cifras obsoletas» con exit 0, sobre un árbol que
      con `lake` daba exit 1. **Con ese verde vacuo se empujó `67b0d50`.** Ahora: no poder
      medir es ROJO, las cifras se comprueban contra la **línea canónica**, y la prosa de
      cabecera sólo avisa (medía 2 falsos positivos y 0 verdaderos).
- [x] ~~`CRASH` versionado~~ → fichero basura de un programa ajeno, colado en `b786238`
      por un `git add -A`. Retirado. ⚠️ Es la misma queja de proceso que llegó de FOL.
- [ ] ⬜ Aguas arriba, sin resolver (de FOL): la causa del `Classical` en `Theorems.Eq` (3)
      y `Tactics.tryMem` (sin medir).
- [ ] `add_comm`, `mul_*` — ya sin incógnitas de método.
- [x] ~~Alcance del proyecto~~ → fijado (`PLANNING.md` §1).
- [x] ~~Pureza constructiva~~ → **M-1 y M-2** (ADR-013), con gate probado.
- [x] ~~Qué naturales~~ → **M-3**: `ℕ₀` de peanolib (ADR-014).
- [ ] Política de axiomas propios para `axiom` de naturaleza distinta a M-8.
- [x] ~~Poner `metaDebtIsError := true`~~ → **hecho el 2026-09-18** (ADR-024), y sin
      esperar a RPP: la deuda no era matemática, era de empaquetado.
- [ ] Configurar `SYMBOL_PREFIXES` en `check-doc-sync.bash` cuando existan familias de
      símbolos propias.

---

## Arquitectura

```text
PeanoRF/
├── Prelim.lean            # Nivel 0: contacto con FOL / ROBINSON_PlusPlus / Peano
├── Meta/
│   └── AxiomCheck.lean    # Gate de 3 ejes — corre en cada build
└── Omega/
    └── Basic.lean         # Capa ω declarada, aislada y contada (ADR-016)
sondeos/                   # Mediciones fuera del build (no cuentan como módulos)
```

---

## Fases de desarrollo

| Fase | Descripción | Estado |
|-------|-------------|--------|
| H0 Andamiaje | Plantilla, dependencias, build verde | ✅ |
| H1 Directiva | Pureza constructiva + gate de 3 ejes | ✅ |
| H2 Axiomas HA | Q⁺⁺ + inducción como axiomas (M-8), sobre `⊢ᵢ` | ✅ |
| H3 Interpretación | `⟦·⟧` en ℕ₀ + soundness finitaria (M-9) | ❌ |
| H4 Reflexión | `⌜·⌝` + adecuación + táctica | ❌ |
| H5–H7 | Volcado, realizabilidad, metateoría | ❌ |

> Ver [NEXT-STEPS.md](NEXT-STEPS.md) para el detalle.

---

**Autor**: Julián Calderón Almendros
*Última actualización: 2026-09-19*

[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)
