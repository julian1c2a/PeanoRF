# `sondeos/` — mediciones fuera del build

**Última actualización:** 2026-09-22

Ficheros de medición y experimento. **No forman parte de la librería** (`lakefile.lean`
no los incluye) y por tanto no rompen el build ni entran en el recuento de módulos.
Se ejecutan a mano:

```bash
lake env lean sondeos/axiom_probe.lean
bash sondeos/check_C_smoke.bash        # los que son shell, no Lean
```

## Ficheros

| Sondeo | Qué mide |
|---|---|
| `axiom_probe.lean` | Footprint de axiomas de FOL / RPP / Peano |
| `omega_probe.lean` | **Carga de las meta-reglas ω** en ROB++ (Minimal+Full) e inventario de sus `axiom` |
| `peano_probe.lean` | Footprint constructivo de **todo** Peano (2207 decls) |
| `lift_probe.lean` | **H2**: ¿es el contexto de axiomas invariante bajo `liftFormula 0`? |
| `h2_probe.lean` | **H2**: footprint de `zero_add` finitario vs. el de ROB++ |
| `h2b_probe.lean` | **2026-09-16**: qué meta-reglas siguen siendo `axiom` aguas arriba |
| `h2c_probe.lean` | **2026-09-16**: footprint de `succ_add` (caso con parámetro) sobre `⊢ᵢ` |
| `param_probe.lean` | **2026-09-16**: 🔑 qué hipótesis exige el parámetro para que el contexto sea cerrado |
| ⭐ `check_C_smoke.bash` | **2026-09-22**: que el control `[C]` de `check-doc-sync.bash` **NO ES VACUO** — ocho casos, dos positivos y seis negativos, incluida la regresión del agujero de la subcadena |

⚠️ `peano_probe.lean` tuvo que anotar `Nat` a mano (`Nat.add`, `Nat.sub`): con `Peano`
importado, el `+` global resuelve a `ℕ₀` y el término queda ambiguo. Es la trampa que ya
documentaba AczelSetTheory.

## `axiom_probe.lean`

Inventario del footprint de axiomas de las tres librerías aguas arriba. Existe porque
**los `import` no demuestran nada**: la única medida del footprint es `#print axioms` /
`Lean.collectAxioms`.

Comandos que define:

| Comando | Qué hace |
|---|---|
| `#probe <Raíz>` | Cuenta declaraciones limpias vs. sucias bajo un prefijo de módulo, con el desglose de axiomas ofensores |
| `#dirty <Raíz>` | Lista TODAS las declaraciones sucias, agrupadas por módulo |
| `#axioms_of <Raíz>` | Inventario de los `axiom` declarados bajo un prefijo |
| `#dependents <ax> under <Raíz>` | Qué declaraciones dependen de un axioma concreto |
| `#fp <símbolo>` | Footprint exacto de un símbolo |

## Medición del 2026-09-06 (la que fundamenta ADR-013)

| Librería | Decls | Limpias | Con footprint extra |
|---|---:|---:|---|
| `Peano` (`PeanoNat.Axioms`) | 192 | **192** | 0 — y **0 `axiom`** declarados |
| `FOL` (barrel completo) | 397 | 332 | 65 · 52 con `Classical.choice` · 13 `axiom` |
| `ROBINSON_PlusPlus.Minimal.Axioms` | 313 | 269 | 44 con `Classical.choice` · 1 `axiom` |

**Los tres hallazgos que decidieron el diseño del gate:**

1. **Los 13 `axiom` de FOL se reparten en tres grupos, y solo uno es clásico.**
   - **Clásicos de nivel objeto (3)**: `MetaRules.dne`, `Theorems.Neg.dne`,
     `Theorems.Quantifiers.forall_not_impl_exists_not`.
   - **Meta-reglas admisibles (5)**: `imp_intro`, `gen` (ω-regla: infinitaria, no
     clásica), `raa` (es introducción de ¬, intuicionista pese al nombre), `or_elim`,
     `ex_elim`.
   - **Completitud (5)**: `formula_enum`, `formula_enum_surj`, `termEqv_func_congr`,
     `termEqv_rel_congr`, `henkin_extension_lemma`.
2. **Los tres clásicos están CONFINADOS a la mitad modelo-teórica.** `MetaRules.dne` no
   lo usa nadie; `Theorems.Neg.dne` solo `Completeness.completeness`;
   `forall_not_impl_exists_not` solo Completeness/Compacity. Como este proyecto **no
   importa** `FOL.Semantics/Soundness/Completeness/Compacity`, la pureza intuicionista
   de nivel objeto sale casi gratis: violarla exige un `import` deliberado.
3. **`ROBINSON_PlusPlus.Minimal.Axioms.axioms` — el conjunto de axiomas de Q⁺⁺ —
   arrastra `Classical.choice`**, vía las funciones de codificación `strCodeM`,
   `termCodeM`, `formCodeM` (primitivas `String` del núcleo de Lean 4.31). O sea:
   **cualquier** teorema sobre Q⁺⁺ lo hereda hoy. Es deuda de nivel META aguas arriba,
   que el autor va a saldar; el gate la tolera con aviso y recuento
   (`inheritedMetaDebt`), nunca en silencio.

Repetir la medición cuando ROBINSON_PlusPlus se sanee, y entonces poner
`metaDebtIsError := true` en `PeanoRF/Meta/AxiomCheck.lean`.

---

## Medición del 2026-09-06 (b) — la carga ω de ROB++ (`omega_probe.lean`)

Sobre **521 declaraciones** de `ROBINSON_PlusPlus` (Minimal + los 11 módulos de Full):

| Regla | Decls que la arrastran |
|---|---:|
| `FOL.MetaRules.gen` (ω-regla) | 70 |
| `FOL.MetaRules.ex_elim` | 64 |
| `FOL.MetaRules.or_elim` | 64 |
| `FOL.MetaRules.imp_intro` | 42 |
| `FOL.MetaRules.raa` | 13 |
| **alguna de las anteriores** | **99 (19 %)** |
| `dne` / `Theorems.Neg.dne` / `forall_not_impl_exists_not` | **0** |

**Dos conclusiones, una excelente y una que decide la arquitectura:**

1. ✅ **ROB++ es intuicionista a nivel objeto, y está VERIFICADO**: cero usos de lógica
   clásica en 521 declaraciones.
2. ⚠️ **ROB++ NO es finitario**: el 19 % pasa por meta-reglas ω. Y son ω de verdad, no
   por descuido — el propio docstring de `FOL/MetaRules.lean` lo dice: *«axiomatizan
   "demostrabilidad = verdad en el modelo estándar"; el sistema resultante es ω-lógica,
   estrictamente más fuerte que FOL⁼ finitaria»*.

**Los 5 `axiom` de Lean de ROB++**: `Minimal.Axioms.ax_axiomsCodeT_eq`,
`Minimal.Theorems.Block8.ax_p_tfa`, `Full.ax_induction` (**30 decls dependen de él**),
`Full.ax_list_induction`, `Full.ax_mod2_alternation`.

🔑 `Full/Induction.lean:166` declara `axiom ax_induction (φ) : axioms ⊢ inductionFormula φ`
— es decir, postula que el esquema de inducción **es derivable del conjunto de axiomas de
Q⁺⁺**. Con un `⊢` finitario eso sería falso (Q no prueba inducción); es coherente sólo bajo
la lectura ω-lógica, donde `⊢` = verdad en ℕ. **De aquí sale la decisión de diseño más
importante de PeanoRF** (ver ADR pendiente y `PLANNING.md`).

---

## Medición del 2026-09-06 (c) — Peano al completo (`peano_probe.lean`)

**2207 declaraciones · 2193 limpias (99,4 %) · 14 sucias.** Las 14 llevan
`Classical.choice` y están confinadas a tres módulos, los tres explícitos sobre lo que son:

| Módulo | Decls sucias |
|---|---:|
| `Peano.PeanoNat.Foundation.Initiality` | 7 |
| `Peano.Prelim.Classical` | 5 |
| `Peano.PeanoNat.Foundation.PureAxioms` | 2 |

**Conclusión: «volcar Peano al completo» es viable desde el punto de vista de la pureza
constructiva.** Peano ya es constructivo salvo por un 0,6 % localizado y nombrado.


---

## Medición del 2026-09-06 (d) — H2, el coste de prescindir de la ω

`lift_probe.lean` responde la pregunta que decidía la viabilidad: **sí**, los axiomas de
Q⁺⁺ son sentencias cerradas y `axioms.map (liftFormula 0) = axioms` se demuestra por
**`rfl`** (cómputo del kernel). Lo mismo para la instancia de inducción de una `φ` concreta
con sólo `#0` libre. Eso hace usable `Derives.intro_forall` — el constructor finitario — en
lugar de la ω-regla `gen`.

`h2_probe.lean` mide el resultado sobre `zero_add`:

| símbolo | footprint |
|---|---|
| `PeanoRF.HA.zero_add` (finitario) | `propext, Classical.choice, Quot.sound` |
| `ROBINSON_PlusPlus.Full.zero_add` (ω) | + **`MetaRules.gen`, `MetaRules.imp_intro`, `ax_induction`** |
| `PeanoRF.HA.gen_closed` | `propext` |

**Tres axiomas menos, misma estructura de prueba.** El `Classical.choice` restante es la
deuda META heredada de la codificación `String` de RPP, no del método.

⚠️ **Alcance de esta medición**: `zero_add` no tiene parámetro libre. El caso con parámetro
(`succ_add`, `add_comm`) está sin medir y es donde la codificación *lift-aware* existe.
No extrapolar el «coste cero» sin comprobarlo.


---

## Medición del 2026-09-16 — el parámetro, y qué cuesta exactamente

`param_probe.lean` aísla la pregunta que decidía H2 con parámetro: **¿es cerrado el
contexto cuando la instancia de inducción lleva un parámetro `a`?**

| caso | resultado |
|---|---|
| `a := zero` (cerrado concreto) | ✅ sale por **`rfl`**, igual que en `zero_add` |
| `a` arbitrario con `liftTerm 0 a = a` | ⛔ **NO basta** — quedan las invariancias de nivel **1** |
| `a` con `∀k. liftTerm k a = a` | ⛔ aún faltan las de **sustitución** |
| `a` con lift **y** subst invariantes (`HA.Closed a`) | ✅ |

**Por qué el nivel 1**: `inductionFormula` usa `liftFormula 1 φ`, así que el parámetro
aparece levantado a nivel 1 dentro de la instancia. Una sola hipótesis de nivel 0 deja la
mitad del trabajo sin hacer, y el `simp` se para con las metas a la vista.

⇒ **Con parámetro ABIERTO no hay generalización finitaria.** Haría falta meter en el
contexto la **clausura universal** de la instancia de inducción. Eso es lo que la ω-regla
compraba, y es el primer sitio donde la disciplina de ADR-016 cuesta algo de verdad.

`h2c_probe.lean` mide el resultado:

| símbolo | footprint |
|---|---|
| `PeanoRF.HA.succ_add` (sobre `⊢ᵢ`) | `propext, Classical.choice, Quot.sound` |
| `ROBINSON_PlusPlus.Full.succ_add_prim` (sobre `⊢`) | + **`MetaRules.imp_intro`, `ax_induction_prim`** |
| `PeanoRF.Calculus.derivesI_to_derives0` | `propext` |


---

## Medición del 2026-09-16b — H3: dónde está de verdad el `Classical`

Se conjeturó (ADR-019) que el `Classical.choice` de `derives0_soundness` era **exactamente**
el precio de las tres reglas clásicas de `⊢₀`. Se hizo la prueba directa de
`derivesI_soundness` por inducción sobre los 18 constructores no clásicos de `⊢ᵢ`, y
**la conjetura se refuta**: sigue saliendo `Classical.choice`.

`h3b_probe.lean` localiza el origen:

| símbolo | footprint |
|---|---|
| `evalTerm` · `evalFormula` · `rule_soundness` | **ninguno** |
| `replaceAt_soundness` | `propext` |
| **`contextSatisfies_lift_zero`** | `propext, Classical.choice, Quot.sound` |
| **`eval_substFormula_zero`** | `propext, Classical.choice, Quot.sound` |
| **`eval_liftFormula_zero`** | `propext, Classical.choice, Quot.sound` |

🔑 **El `Classical` viene de los tres lemas de levantamiento y sustitución de la semántica**,
no de las reglas clásicas ni de la evaluación. Quitar `dne_rule` y compañía era **necesario
pero no suficiente**.

⇒ Los tres son hechos **puramente combinatorios** sobre índices de De Bruijn; casi seguro un
`Classical` **oculto** (§27), no esencial. Saneados, `derivesI_soundness` pasa a
`⊆ {propext, Quot.sound}` **sin tocar el fichero**. El obstáculo queda reducido de «toda la
solidez de `⊢₀`» a **tres lemas con nombre**.


---

## Medición del 2026-09-16c — la caza del último `Classical`: RESUELTA

Localizado: **toda** la contaminación de la semántica entra por **un solo lema**,
`FOL.Metamath.Semantics.shift_updateEnv_comm`. Aguas abajo todo hereda; aguas arriba
(nivel término) todo está limpio.

**Lo que NO es la causa**, descartado por medición (cada uno limpio en aislamiento):

| candidato | footprint aislado |
|---|---|
| `by_cases` · `rcases` · `obtain` · `cases` | ninguno |
| `omega` | `propext, Quot.sound` |
| `simp` (conjunto por defecto) sobre un `if` | `propext` |
| `if_pos` / `if_neg` | ninguno |
| `funext` | `Quot.sound` |
| `dsimp [updateEnv]` | ninguno |
| `Nat.lt_or_ge` · `Nat.not_lt` · `Nat.eq_or_lt_of_le` | ninguno |
| `updateEnv` · `shiftEnv` (definiciones) | ninguno |
| `open Classical` de fichero | no existe en `Semantics.lean` ni en `FOL.lean` |

⛔ **Y sin embargo el lema ensamblado sale sucio.** Se reescribió la prueba dos veces de
forma independiente —dicotomías constructivas + `simp`, y dicotomías + `rw [if_pos/if_neg]`
puro— y **las dos siguen arrastrando `Classical.choice`**.

### 🏁 Resuelto — estaba en UNA LÍNEA

`pp.explicit` sobre la meta tras el `dsimp` mostró que **todas** las instancias son reales
(`n.decLt c`, `instDecidableEqNat`): ni rastro de `Classical.propDecidable`. Luego lo metía
una táctica al cerrar. La bisección **por ramas** lo localizó:

| rama | footprint |
|---|---|
| `n < c` | `propext, Quot.sound` |
| `n = c` | `propext, Quot.sound` |
| **`c < n`** | **+ `Classical.choice`** |

Lo único propio de esa rama era el cierre del caso imposible:

```lean
| zero => omega                                                      -- ⛔ Classical.choice
| zero => exact absurd (Nat.le_zero.mp (Nat.not_lt.mp h1)).symm h2   -- ✅ cero axiomas
```

🔑 **`omega` sobre metas ARITMÉTICAS es limpio; sobre metas fuera de su lenguaje —aquí, de
tipo `D`— descargadas por contradicción, mete `Classical.choice`.** Medido:

| | |
|---|---|
| `omega` con meta `(1:Nat) = 2` desde hipótesis contradictoria | `propext, Quot.sound` |
| `omega` con meta `v 0 = d'` desde hipótesis contradictoria | **+ `Classical.choice`** |
| `absurd h (Nat.not_lt_zero c)` | **ningún axioma** |

**Resultado**: toda la semántica de fórmulas pasa a `[propext, Quot.sound]`, y con ella
`derivesI_soundness` y `derivesI_consistent`.

⚠️ **Por qué la primera conclusión fue errónea**: se midió la conjetura de ADR-019 sobre una
cadena contaminada. *Una medición de footprint sólo refuta una conjetura sobre lógica si el
resto de la cadena está limpio.*


---

## Medición del 2026-09-17 (b) — auditoría de COBERTURA del gate

La pregunta no era si el control funciona, sino **sobre cuánto del terreno actúa**. Ficheros:
`audit_2026-09-17b.lean` (cobertura y smoke tests) y `audit_2026-09-17c.lean` (re-medición
de footprints propios tras 18 commits de FOL y 15 de RPP en 24 h).

### Lo medido ANTES (criterio `List Formula → Formula → Prop`)

| | relaciones | constructores |
|---|---|---|
| el gate VE | 6 — `Derives`, `Derives₀`, `Derivesᵢ`, `Derives₁`, `Derives₂`, **`PrfH`** | 23 vigilados |
| el gate está CIEGO | 5 — `LK₀`, `LKc`, `LKh`, `Prf`, `Prf₀` | **67 sin vigilar** |

Y los smoke tests `LK₀.ax` y `LKc.cut` **pasaban sin una palabra**. `PrfH` —que nunca
estuvo en ninguna lista— apareció sola: el descubrimiento por tipo sí funcionaba, dentro
de su forma.

### La medición que obligó a tocar la clasificación

Con un módulo **temporal** en la capa ω que probaba `((A ⇒ ⊥) ⇒ ⊥) ⇒ A` vía `PrfH.p3`:

```text
[gate] OK — 86 declaraciones propias verificadas. Eje objeto: intuicionista puro
```

🔑 `p3` **es** la DNE con otro nombre. La última lista por nombre la clasificaba como
«FINITARIO/AJENO» y la capa ω la toleraba — justo la capa que relaja.

### Lo medido DESPUÉS (criterio por TELESCOPIO + clásico por el tipo)

```text
[gate · inventario] 11 relaciones de derivabilidad detectadas POR TELESCOPIO:
  [Derives, LKh, Derives₀, Derivesᵢ, LK₀, PrfH, Prf, Derives₂, LKc, Derives₁, Prf₀]
  ⇒ 90 constructores ajenos vigilados, de ellos 14 CLÁSICOS
[gate · inventario] ⚠️ 2 casi-candidato(s) que el telescopio RECHAZÓ:
  [FOL.Canonical0.PointwiseEqv, FOL.Derives2.PwEq]
```

Los cuatro smoke tests cazados (`LK₀.ax`, `LKc.cut`, `PrfH.p3`, `Prf.p3`), y el
contraejemplo `Derives₀.hyp` **pasando**, que es lo que mantiene vivos los puentes. Y con
un módulo temporal usando `Derives.gen_rule` dentro de `PeanoRF.Omega`:

```text
[gate · CONSTRUCTORES] 1 uso(s) de constructores prohibidos:
  [(PeanoRF.Omega.smokeGen, (Derives.gen_rule, FINITARIO/AJENO))]
```

⇒ la capa ω ya no es comodín.

### Re-medición de los footprints propios — sin cambios

| declaración | footprint |
|---|---|
| `derivesI_to_derives0`, `derivesI_to_derives`, `gen_closed`, `specI` | `[propext]` |
| `derivesI_soundness`, `derivesI_consistent`, `eqI_symm`, `eqI_trans` | `[propext, Quot.sound]` |
| `zero_add`, `succ_add`, `induction_object` | `+ Classical.choice` (deuda heredada de RPP) |

`Derives₀` conserva sus 21 constructores ⇒ `⊢ᵢ` sigue siendo exactamente `⊢₀` menos las
tres clásicas, y el puente sigue en pie.


---

## Medición del 2026-09-18 — ¿es viable **H3ter** (la DP para HA) por la vía barata?

Ficheros: `numerals_probe.lean` (footprints de la capa de numerales de RPP) y
`numeralI_spike.lean` (el port de `numeral_add` a `⊢ᵢ`).

### La pregunta

H3ter —la propiedad de disyunción **para HA**, no sólo para la lógica— se reduce a **un
lema**: `ha_ctx_slashed`, porque L2 ya está enunciada para contexto arbitrario. Su caso
duro, las instancias de inducción, pide que **todo término cerrado sea demostrablemente
igual a un numeral**, y eso pide los homomorfismos `numeral_add`/`numeral_mul`/`numeral_pow`.
¿Se pueden reusar los de ROBINSON_PlusPlus?

### ⛔ Reusar: IMPOSIBLE, y no por el footprint

Todos están enunciados sobre **`⊢`** (`FOL.Derives`):

```lean
theorem numeral_add (a b : Nat) : axioms ⊢ (add (numeral a) (numeral b) =eq numeral (a + b))
```

`⊢` es la HERRAMIENTA, no el SUJETO (ADR-017), y el puente va `⊢ᵢ → ⊢₀ → ⊢` **en un solo
sentido**. Lo suyo no baja a lo nuestro. La vía barata no existe, y no por contaminación
sino por el cálculo.

### 📏 Los footprints, que sí dicen algo útil

| símbolo (RPP) | footprint | ¿ω? |
|---|---|---|
| `numeral` / `numeralM` (def) | **ningún axioma** — es sintaxis pura | — |
| `numeral_add` | `propext, Classical.choice, Quot.sound` | **no** |
| `numeral_mul` | idem | **no** |
| `numeral_pow` | idem | **no** |
| `numeral_lt` | idem | **no** |
| `numeral_ne` | **+ `ex_elim, imp_intro, raa, ax_induction_prim`** | ⛔ **sí** |

⭐ Los tres homomorfismos que hacen falta van por **inducción META**, no por `ax_induction`,
y salen limpios de ω. El único contaminado es `numeral_ne` —la **distinción** de numerales—
y **no está en el camino**: para «término cerrado = numeral» no hace falta.

El `Classical.choice` es la deuda heredada de siempre (viene de `axioms`, por la
codificación `String`), no de las pruebas.

### ✅ Portar: BARATO, y esto está medido, no estimado

`numeralI_spike.lean` porta `numeral_add` a `⊢ᵢ`. **22 líneas, a la primera**, copiando el
patrón de `HA/Arith.lean`:

```
'PeanoRF.HA.numeralI_add' depends on axioms: [propext, Classical.choice, Quot.sound]
```

El **mismo** footprint que la versión de RPP sobre `⊢`. Los ingredientes ya estaban todos:
`ax'` da cualquier axioma de Q⁺⁺, `specI` instancia, y `eqI_trans`/`eqI_congr_succ` cierran.
Y `numeralM` vive en la capa **Minimal**, que ya importábamos — coste de import **cero**.

### Veredicto

⚠️ **SUPERADO EL MISMO DÍA**: esta medición contestó bien a su pregunta —el port es
barato— pero la pregunta era demasiado estrecha. Ver «Medición del 2026-09-18 (d)»: el
enunciado de H3ter era falso, y no por los numerales.

**El port es viable.** El lenguaje de Q⁺⁺ tiene cinco símbolos de función
(`zero`, `succ`, `add`, `mul`, `pow`; `one`/`two` son abreviaturas), así que son **tres
homomorfismos** que portar, los tres del mismo patrón que el spike.

⚠️ Lo que sigue siendo incógnita es `closed_term_eq_numeral` —inducción sobre la estructura
del término—, que es nuestra y nueva. Pero **no tiene bloqueo aguas arriba**, que era
justo lo que esta medición venía a decidir.


---

## Medición del 2026-09-18 (b) — el gate contra un cálculo que NO existía al escribirlo

`audit_2026-09-18.lean`. FOL estrenó `LKp` la noche anterior (`Craig0.lean`, su ADR-063:
Maehara + interpolación de Craig). El criterio **por telescopio** se escribió el 17 sin
saber que `LKp` iba a existir.

```
[gate · inventario] 8 relaciones POR TELESCOPIO: [… FOL.Craig0.LKp …]
                    ⇒ 58 constructores ajenos vigilados, de ellos 12 CLÁSICOS
error: 'smoke_lkp' usa 1 constructor(es) que ⊢ᵢ NO tiene: [FOL.Craig0.LKp.ax]
```

**Sin tocar `AxiomCheck.lean`.** Primera validación del criterio contra un cálculo posterior
a su escritura — justo lo que las tres versiones anteriores no aguantaron.

---

## Medición del 2026-09-18 (c) — `coreAxioms`, y la deuda que no era matemática

`coreaxioms_probe.lean`, `core_after.lean`. La apuntó el agente de RPP midiendo SU puerta.

```
ROBINSON_PlusPlus.Minimal.Axioms.axioms      →  [propext, Classical.choice, Quot.sound]
ROBINSON_PlusPlus.Minimal.Axioms.coreAxioms  →  does not depend on any axioms
```

De los 109 constituyentes de `axioms` sólo cinco arrastran `Classical.choice`, y son del
**verificador object de demostraciones**. `coreAxioms` trae los seis que usamos.

⇒ `HA.ctx` pasa a `coreAxioms` (ADR-024): `PeanoRF.HA.ctx` **sin axiomas**, toda la capa HA
en `[propext, Quot.sound]`, deuda heredada **de 14 a 0**, y `metaDebtIsError := true`.

🔑 **Doce días de aviso tolerado se resolvieron cambiando qué lista se importa.**

---

## Medición del 2026-09-18 (d) — ⛔ el enunciado de H3ter es FALSO

`junk_probe.lean`.

```lean
theorem junk_trichotomy :
    ctx [] ⊢ᵢ (lt foo bar ∨ foo = bar ∨ lt bar foo)     -- [propext]
```

`foo`, `bar` son `Term.func "foo" []`: **no son símbolos del lenguaje de Q⁺⁺**. Pero `Term`
es genérica y `elim_forall` instancia con cualquier término, así que `ax19_lt_trichotomy` se
instancia en basura y es derivable.

⚠️ **Mitad medido, mitad argumentado.** La derivabilidad está medida. Que **ninguna rama**
sea derivable es argumento por solidez con dos modelos (`foo↦0,bar↦1` y al revés);
formalizable con `derivesI_soundness`, **no formalizado**.

⇒ **HA sobre la sintaxis genérica no tiene la propiedad de disyunción.** El teorema de
Kleene es sobre SU lenguaje. Informado a FOL y RPP en
`doc/HALLAZGO-SINTAXIS-GENERICA-2026-09-18.md`, con la pregunta de si su Craig les da la
eliminación de símbolos ajenos.


---

## Medición del 2026-09-18 (e) — ⭐ el COLAPSO conmuta: la ruta barata de H3ter existe

`collapse_probe.lean`. La pregunta: el obstáculo de H3ter es que `elim_forall` instancia con
símbolos ajenos al lenguaje (medición (d)). La ruta cara sería un cálculo paralelo
`DerivesL`. La barata es **transformar** la derivación en vez de restringirla:

```lean
derivesI_collapse : Γ ⊢ᵢ f  →  Γ.map (collapseF L) ⊢ᵢ collapseF L f
```

donde `collapseT L` manda a `zero` todo símbolo fuera de la signatura `L` y **no toca las
variables**. En `elim_forall`, una instanciación con basura pasa a ser una con
`collapseT L t`, que sí es del lenguaje.

Ese lema necesita **dos conmutaciones**, y eran la única incógnita:

```
'collapseF_lift'       depends on axioms: [propext]
'collapseF_subst'      depends on axioms: [propext]
'collapseT_numeralM'   depends on axioms: [propext]
```

⭐ **Las dos salen, a la primera, y ni siquiera arrastran `Quot.sound`.** El caso que podía
fallar —`∀`/`∃`, donde la sustitución entra bajo la ligadura como
`substFormula (v+1) (liftTerm 0 s)`— se cierra con la conmutación del levantamiento.

⭐ Y está **parametrizado por la signatura** `L : String → Bool`, no clavado a Q⁺⁺: las
conmutaciones no dependen de qué símbolos se conserven. Lo único que se usa del reemplazo es
que sea **cerrado** (`zero` no tiene argumentos, luego lift y subst lo dejan igual por `rfl`).

⚠️ Los predicados ajenos **no** se colapsan, y es deliberado: la barra de un átomo es su
derivabilidad, sin testigo. El obstáculo era la instanciación de `∀`/`∃` con **términos**
ajenos, no los predicados.

⇒ **La ruta está abierta.** Falta `derivesI_collapse`, que es una inducción sobre los 18
constructores con estas conmutaciones en la mano — la misma forma que `derivesI_subst`.
Y no depende de FOL: su ADR-065 mide que el puente a `LKp` **no tiene camino barato**
(«parametrizar `Hauptsatz0`… un módulo de 1 256 l., ESTIMADO alto»), así que esperar a
Craig era mala apuesta.

---

## 2026-09-18 (g) · `collapse_parallel_probe.lean` — ¿cierra `elim_forall` con el colapso DENTRO del enunciado?

**La pregunta.** La etapa 2 de H3ter quiere `Slash T D` con `D = ClosedQTerm`. Su caso
`elim_forall` pide entonces `D (substT ρ t)` para un `t` **arbitrario**, que es inalcanzable:
si `t` lleva un símbolo ajeno, `substT ρ t` también. Y **`derivesI_collapse` no lo arregla por
sí solo**: actúa sobre derivaciones enteras, y L2 por dentro no sabe que la derivación venga
colapsada. La forma candidata (c) era que L2 demostrara la barra de la instancia **colapsada**,

```
slash_of_derives : Γ ⊢ᵢ f → ∀ ρ, (…) → Slash T D (collapseF L (substF ρ f))
```

con lo que la obligación pasa a ser `D (collapseT L (substT ρ t))`.

### Q1 · ¿conmuta el colapso con la sustitución PARALELA?

```
'collapseF_substF'  depends on axioms: [propext, Quot.sound]
```

✅ Sí, con `collapseS L ρ := fun n => collapseT L (ρ n)`. El caso de la ligadura sale de
`collapseS L (upS ρ) = upS (collapseS L ρ)`, que en el índice 0 es `rfl` y en `n+1` es
exactamente `collapseT_lift`, ya demostrado el (e).

### Q3 · ¿el colapso FIJA el dominio? (lo que pide `intro_forall`)

```
'collapseT2_fix'  depends on axioms: [propext]
```

✅ `ClosedQTerm u → collapseT LQ2 u = u`, por inducción sobre `ClosedQTerm`.

### Q2 · ⭐⭐ la obligación de `elim_forall`

```
'q2_term'  depends on axioms: [propext, Quot.sound]

q2_term (ρ : Subst) (hρ : ∀ n, ClosedQTerm (ρ n)) :
    ∀ t : Term, ClosedQTerm (collapseT2 LQ2 (substT ρ t))
```

✅ **Con `ρ` valuada en el dominio, el colapso de `substT ρ t` está en el dominio para `t`
ARBITRARIO** — símbolos ajenos y aridades erróneas incluidos. Es exactamente lo que
`elim_forall` pedirá en la forma (c). ⇒ **La forma (c) es la buena.**

### ⛔ El hallazgo: la signatura tiene que llevar la ARIDAD

`collapseT` toma hoy `L : String → Bool`, **sólo el nombre del símbolo**. Eso no basta:

```
contraejemplo_aridad : ¬ ClosedQTerm (Term.func add_sym [zero])      [propext]
contraejemplo_colapso : collapseT LQ (Term.func add_sym [zero])
                          = Term.func add_sym [zero]                 [propext]
```

`+` aplicado a **un** argumento es un término legítimo de la sintaxis, es cerrado y lleva
sólo símbolos de Q⁺⁺ — pero **no es un `ClosedQTerm`**, porque los constructores de
`ClosedQTerm` fijan también la aridad. Y Q⁺⁺ no tiene ningún axioma sobre él, así que
**tampoco es demostrablemente igual a un numeral**: no puede estar en `D`. El colapso de hoy
lo deja pasar intacto.

⇒ **`collapseT` hay que generalizarlo a `L : String → Nat → Bool`**, con el predicado
aplicado a `ts.length`. El coste medido es **dos lemas de longitud** (`collapseTs2_length`,
`substTs_length`, tres líneas cada uno) más el mismo `by_cases` que ya había; las
conmutaciones no cambian de forma.

### ⚠️ Trampa de notación: `∧` y `∨` NO se pueden escribir bajo `open FOL`

`open FOL` las tiene tomadas por la conjunción y la disyunción de `FormulaG`. Escribir
`(s = zero_sym ∧ ts.length = 0)` da **`unexpected token '='; expected ')', ',' or ':'`**, un
error que no se parece nada a su causa — la misma familia que el `σ` de `peanolib`
(`unexpected token 'σ'`). Leerlas está bien (las que vienen de `injEq`, `rcases`…);
escribirlas, no. Se rodea con `Or`/`And` explícitos, o reformulando el enunciado para no
necesitarlas (aquí: `LQ2 s args.length = true` en vez de una disyunción de conjunciones).
