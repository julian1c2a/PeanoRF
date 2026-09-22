# REFERENCE · HA — la Aritmética de Heyting, el fragmento y el modelo

**Last updated:** 2026-09-22
**Autor**: Julián Calderón Almendros

> **Nodo temático del sistema REFERENCE** (AI-GUIDE §0.5).
> ⬆️ Índice raíz: **[REFERENCE.md](../REFERENCE.md)** · catálogo de los 18 módulos, grafo de
> dependencias y teoremas de cabecera.
> ↔️ Nodos hermanos: **[REFERENCE-Calculus.md](REFERENCE-Calculus.md)** (el cálculo `⊢ᵢ` y la
> barra `Slash T D`, sobre los que se construye todo lo de aquí) ·
> **[REFERENCE-Meta.md](REFERENCE-Meta.md)** (contacto, gate y capa ω).

---

## 1. Qué cubre este nodo

La **teoría**: los axiomas de HA sobre `⊢ᵢ`, los numerales, el dominio de la barra, los
axiomas barrados, el fragmento aritmético donde la propiedad de disyunción sí sale, y el
modelo estándar sobre `ℕ` que descarga la consistencia.

| módulo | qué es | § |
|---|---|---|
| [`PeanoRF/HA/Domain.lean`](../PeanoRF/HA/Domain.lean) | el dominio `Grounded`, definido **por sus clausuras** | 2.1 |
| [`PeanoRF/HA/SlashAxioms.lean`](../PeanoRF/HA/SlashAxioms.lean) | 🏁🏁 los **34** axiomas de `coreAxioms` barrados | 2.2 |
| [`PeanoRF/HA/Order.lean`](../PeanoRF/HA/Order.lean) | 🏁 **el orden sobre términos anclados** — la herramienta que refutó ADR-037 | 2.3 |
| [`PeanoRF/HA/Fragment.lean`](../PeanoRF/HA/Fragment.lean) | el **fragmento aritmético**: 17 → 19 → 22 → **23** | 2.4 |
| [`PeanoRF/HA/Model.lean`](../PeanoRF/HA/Model.lean) | 🏁 el modelo sobre `ℕ`: `hcon` descargada, `−` medido | 2.5 |
| [`PeanoRF/HA/Axioms.lean`](../PeanoRF/HA/Axioms.lean) | el conjunto de axiomas, `gen_closed`, `Closed` | 2.6 |
| [`PeanoRF/HA/Numerals.lean`](../PeanoRF/HA/Numerals.lean) | los numerales y el puente sintaxis ↔ `ℕ` | 2.7 |
| [`PeanoRF/HA/Arith.lean`](../PeanoRF/HA/Arith.lean) | `zero_add` y `succ_add`, el primer teorema finitario | 2.8 |

⛔ **Lo primero que hay que saber de este nodo**: el enunciado ingenuo de H3ter —«HA tiene
la propiedad de disyunción»— es **falso** sobre la sintaxis genérica de FOL, y está medido.
Por eso el **dominio** (`Grounded L`) y el **colapso** (`collapseF L`) están en el enunciado
de los teoremas y no en la letra pequeña. El detalle, en §2.1 y en el índice raíz.

---

## 2. Módulos

## 2.1 `HA/Domain.lean` — el dominio de la barra

**Fichero**: [`PeanoRF/HA/Domain.lean`](../PeanoRF/HA/Domain.lean)

**Namespace**: `PeanoRF.HA`
**Dependencies**: `PeanoRF.Calculus.{Collapse,Subst}`, `PeanoRF.HA.Numerals`, `Calculus.Slash`
**Last updated**: 2026-09-21
**Status**: ✅ Completo
**@importance**: **foundational**

| nombre | enunciado | footprint |
|---|---|---|
| 🏗️ `LQ` y su capa (§1–§2) | los cinco símbolos de los NUMERALES, con aridad. ⚠️ **Sin uso portante desde el rediseño a `Grounded LQpp`**: se conserva como EVIDENCIA (`not_closed_add_unary`, ADR-028) y ANDAMIO para `hNum` | — |
| `collapse_fix_closed` | `ClosedQTerm u → collapseT LQ u = u` | `propext` |
| ⛔ `not_closed_add_unary` | `¬ ClosedQTerm (func add_sym [zero])` | `propext` |
| `closed_of_LQ` | símbolo admitido + argumentos en el dominio ⟹ dominio | `propext, Quot.sound` |
| ⭐⭐ `closed_collapse_subst` | `(∀n, D (ρ n)) → ∀ t, D (collapseT LQ (substT ρ t))` | `propext, Quot.sound` |
| `LQpp` | la signatura COMPLETA de Q⁺⁺: **trece** símbolos, medidos sobre `coreAxioms` | — |
| `zeroS` / `zeroS_grounded` | la sustitución que cierra, todo índice a `zero` | — |
| 🏗️ `closed_grounded` | `ClosedQTerm t → Grounded LQpp t` — ANDAMIO para `hNum`, sin uso hoy | `propext` |
| 🏁 **`qDisjunctionProperty`** | la DP para **cualquier teoría de Q⁺⁺** con los axiomas barrados | `propext, Quot.sound` |
| 🏁 **`qExistenceProperty`** | la EP, con el testigo **anclado** (`Grounded LQpp`) | `propext, Quot.sound` |
| `eq_of_map_self` | de `l.map f = l` a `∀ g ∈ l, f g = g` | `propext` |
| ⭐ `coreAxioms_sentence` | **los 34 axiomas son sentencias del lenguaje**, por `rfl` | `propext` |
| ⭐⭐ `slash_coreAxioms_harrop` | los 28 de Harrop caen solos, sólo con la consistencia | `propext, Quot.sound` |
| 🏁🏁 **`haDisjunctionProperty`** | la DP de HA reducida a TRES obligaciones | `propext, Quot.sound` |

⚠️ **`qExistenceProperty_numeral` y `closed_zeroS` NO EXISTEN.** Se anunciaron aquí el
2026-09-18 y se retiraron del código el mismo día al rehacer §3 sobre `Grounded LQpp`; la
tabla se quedó con las filas. Lo destapó el control `[B]` en su primera ejecución
(2026-09-21), tres días después, y es exactamente lo que `[B]` existe para cazar.

**Para qué**: la barra de H3ter lleva un parámetro de dominio `Slash T D`, y L2 necesita
**dos clausuras** de ese dominio: que el colapso lo **fije** (caso `intro_forall`) y que el
colapso de `substT ρ t` **caiga** en él para `t` arbitrario (caso `elim_forall`). Las dos
están aquí, medidas antes de escribir L2 (`sondeos/collapse_parallel_probe.lean`).

⛔ **Por qué la signatura lleva la ARIDAD.** `collapseT` tomaba `L : String → Bool`, sólo el
nombre. `+` con UN argumento es un término legítimo, cerrado y con símbolos de Q⁺⁺ — pero
**Q⁺⁺ no tiene ningún axioma sobre él**, luego no es demostrablemente igual a ningún numeral,
que es lo único que la etapa 3 le pide al dominio. `not_closed_add_unary` lo deja medido en
producción, no en el cuaderno.

⚠️ Aquí **no se pueden escribir `∧`, `∨` ni `g ∈ T`**: `open FOL` tiene tomadas las dos primeras por `FormulaG`, y `∈` está sobrecargada de forma que elabora su lado derecho como un TIPO. Se escriben `And`/`Or` y `List.Mem g T`. La familia del `σ` de `peanolib`.
`(s = zero_sym ∧ n = 0)` da `unexpected token =` — la familia del `σ` de `peanolib`.

---

## 2.2 `HA/SlashAxioms.lean` — los axiomas que NO son de Harrop

**Fichero**: [`PeanoRF/HA/SlashAxioms.lean`](../PeanoRF/HA/SlashAxioms.lean)

**Namespace**: `PeanoRF.HA`
**Dependencies**: `PeanoRF.HA.Domain`
**Last updated**: 2026-09-18
**Status**: ✅ 6 de 6

| nombre | enunciado | footprint |
|---|---|---|
| `ctx_weaken` | lo demostrado sin inducción vale con ella | `propext` |
| `numeralI_lt` | `a < b ⟹ ⊢ᵢ ā < b̄` — por la dirección ⇐ de `ax13` | `propext, Quot.sound` |
| ⭐ `numeralI_ne` | `a ≠ b ⟹ ⊢ᵢ ¬(ā = b̄)` — **constructivo** | `propext, Quot.sound` |
| ⭐⭐ `slash_ax19` | `ax19_lt_trichotomy` barrado bajo `hNum` | `propext, Quot.sound` |
| ⭐ `slash_ax21` | `ax21_mod2_range` — bajo `hNum` **y consistencia** | `propext, Quot.sound` |
| ⭐ `slash_axL2` | `ax_L2_in_cons` — bajo `hNum`, **sin consistencia** | `propext, Quot.sound` |
| ⭐ `numeralI_not_lt` | `b ≤ a ⟹ ⊢ᵢ ¬(ā < b̄)` — pide `hlift` | `propext, Quot.sound` |
| ⭐⭐ `addI_succ_ne` | **ningún numeral es `x + σy`** — inducción META | `propext, Quot.sound` |
| ⭐ `slash_ax13` / `slash_ax14` | los dos que pedían refutar una desigualdad | `propext, Quot.sound` |
| `slash_axL3` | `ax_L3_in_concat` — bajo `hIn` | `propext, Quot.sound` |
| 🏁🏁 **`slash_coreAxioms`** | **los 34 axiomas barrados** | `propext, Quot.sound` |
| 🏁🏁🏁 **`haDisjunctionProperty_core`** | la DP de HA con `coreAxioms` descargado | `propext, Quot.sound` |
| ⭐ `isHarrop_inductionFormula` | `isHarrop (inductionFormula φ) = isHarrop φ` — por `rfl`, **sin axiomas** | — |
| 🏁 `slash_inductions` / `inductions_lift` | `hInd` y `hlift` descargadas para instancias de Harrop | `propext, Quot.sound` |
| 🏁🏁🏁 **`haDisjunctionProperty_harrop`** | …y quedan **tres** hipótesis, las tres de fondo | `propext, Quot.sound` |
| ✅ **`haDisjunctionProperty_zeroAdd`** | la instancia trabajada con `phiZeroAdd`: **no es vacuo** | `propext, Quot.sound` |

**El patrón de los seis**: barrar una disyunción pide **elegir rama**, y eso es una decisión
en el META. `hNum` baja los términos del dominio a numerales, se decide sobre números, y la
decisión sube al objeto por Leibniz (`eqI_rw_atom2_l`/`_r`, la reescritura dentro de un
PREDICADO, que no existía).

⚠️ **`hNum` va como hipótesis y no se esconde**: `closed_term_eq_numeral` la da para los
cinco símbolos de los numerales, pero el lenguaje tiene trece. Falta evaluar `√`, `/₂`,
`%₂`, `τ`, `−`, `::`, `##` y `Π_p` sobre numerales dentro de Q⁺⁺.

⭐ **`numeralI_ne` es nuestro**: aguas arriba `numeral_ne` arrastra `Classical` (medido el
2026-09-16). Éste se construye con `ax2` (`σx ≠ 0`) en las bases y `ax3` (`σ` inyectiva) en
el paso, y mide `[propext, Quot.sound]`.

**Lo que falta, y es lo único**:

| hipótesis | qué es | ¿se puede demostrar aquí? |
|---|---|---|
| ✅ `hcon` | la consistencia de la teoría | 🏁 **SÍ, y está hecho** (2026-09-21, ADR-039): `hcon_fragment` en `HA/Model.lean`. ⛔ Aquí ponía «no (Gödel)» y **era falso**: Gödel II es sobre la teoría probando su PROPIA consistencia |
| `hlift` | el contexto invariante bajo levantamiento | ✅ si las instancias son cerradas |
| `hNum` | todo término anclado es demostrablemente un numeral | ⏳ faltan `√`, `/₂`, `%₂`, `τ`, `−`, `::`, `##`, `Π_p` |
| `hIn` | `∈` decidible sobre términos anclados | ⛔ pide inducción sobre listas |

⚠️ **`hIn` es hipótesis, no teorema.** `ax_L2_in_cons` se pudo cerrar sin ella porque una de
sus dos ramas es una IGUALDAD, refutable con `numeralI_ne`; en `ax_L3_in_concat` las dos
ramas son `∈` y no hay nada que refutar bajando a numerales.

---

## 2.3 `HA/Order.lean` — el ORDEN sobre términos anclados

**Fichero**: [`PeanoRF/HA/Order.lean`](../PeanoRF/HA/Order.lean)

**Namespace**: `PeanoRF.HA`
**Dependencies**: `PeanoRF.HA.SlashAxioms`
**Last updated**: 2026-09-22
**Status**: 🏁 la herramienta que refutó ADR-037

⛔ **Por qué existe.** Hasta el 2026-09-22 el orden de Q⁺⁺ sólo se manejaba **sobre
numerales** (`numeralI_lt`, `numeralI_ne`, `numeralI_not_lt`, `addI_succ_ne`). Para un
término cualquiera —un `√n̄`, un `/₂n̄`— no había nada, y ADR-037 dedujo de ahí que los
símbolos «caracterizados por propiedades» no se despejan sin inducción. **Era falso.**

| nombre | enunciado | footprint |
|---|---|---|
| `ax13I` / `ax18I` / `ax19I` | los tres axiomas del orden, instanciables | — |
| `exI_of_ltI` | la dirección ⇒ de `ax13` para términos anclados | `propext, Quot.sound` |
| `ltI_of_add` | la dirección ⇐ | `propext, Quot.sound` |
| `ltI_irrefl` | `ax18` instanciado | `propext` |
| ⭐ `notI_lt_zero` | **nada es menor que cero** — `t + σk = 0` choca con `ax5` + `ax2` | `propext, Quot.sound` |
| `zeroI_add` | `0 + t = t` **sin** instancia de inducción: el término está fijo | `propext, Quot.sound` |
| ⭐⭐ **`zeroI_or_succ`** | **todo término anclado es `0` o un sucesor** | `propext, Quot.sound` |
| `addI_assoc` | asociatividad, con el primer argumento anclado | `propext, Quot.sound` |
| `grounded_add` | el anclaje sobrevive a la suma | `propext, Quot.sound` |
| ⭐ **`ltI_add_right`** | **monotonía estricta de `+`** | `propext, Quot.sound` |
| `mulI_zero` · `mulI_succ` · `mulI_comm` · `mulI_distrib` | el producto, instanciado | `propext, Quot.sound` |
| `mulI_two` | `t·2̄ = t + t` | `propext, Quot.sound` |
| ⭐⭐ **`ltI_mul_two`** | **monotonía por `2̄`, SIN transitividad** | `propext, Quot.sound` |
| ⭐ `notI_add_succ_self` | ningún término anclado cumple `x + σy = x` | **`propext`** |
| `ltI_trans` | transitividad de `<` | `propext, Quot.sound` |

⭐⭐ **`zeroI_or_succ` es lo que Robinson Q POSTULA** (su axioma 3) y `coreAxioms` no tiene.
Se deriva de la tricotomía: la rama `t < 0` la refuta `notI_lt_zero`, y la rama `0 < t` da
el testigo por la dirección ⇒ de `ax13` más `0 + x = x`.

⚠️ `0 + x = x` **no es `zero_add`**. Aquél cuantifica sobre `x` y por eso pide una instancia
de inducción; aquí el término está **fijo**, y basta `ax6` + `ax4`. La diferencia es
exactamente la que separa «esquema» de «instancia», y es la que hacía parecer cara esta
pieza.

🔑 **El truco que evita la transitividad** (`ltI_mul_two`): para `a < b ⇒ a·2̄ < b·2̄` lo
natural sería encadenar `a+a < b+a < b+b`. No hace falta — de `y + σj = k̄` se **calcula**
`k̄·2̄ = y·2̄ + σ(σj + j)`, que es ya la forma que `ax13` pide. Menos piezas y menos
hipótesis.

⭐ **Y `notI_add_succ_self` mide lo que costaba lo mismo con numerales**: `addI_succ_ne`
necesita **inducción META**; aquí sale gratis, porque `x + σy = x` es justo `x < x`.

⚠️ **Todo pide `Grounded`**, y varios lemas además `hlift`: al cruzar el binder de `∃` de
`ax13` los términos se levantan y el contexto también. Para numerales eso lo deshacen
`liftTerm_numeralM`/`substTerm_numeralM`; para un término cualquiera, las dos clausuras del
dominio.

---

## 2.4 `HA/Fragment.lean` — el FRAGMENTO donde la DP sí sale

**Fichero**: [`PeanoRF/HA/Fragment.lean`](../PeanoRF/HA/Fragment.lean)

**Namespace**: `PeanoRF.HA`
**Dependencies**: `PeanoRF.HA.SlashAxioms`
**Last updated**: 2026-09-21
**Status**: ✅ tres fragmentos encajados, 17 → 19 → 22

⛔ **La medición que manda el módulo**: `hNum` sobre los **trece** símbolos de Q⁺⁺ es
inalcanzable, y para `−` es **falsa** — ese símbolo aparece en **un solo axioma**
(`ax29_sub_witness`) y condicionado a `x ≤ y`. Lo que sí sale es un fragmento, y crece.

| | signatura | axiomas | teorema |
|---|---|---|---|
| **A** | `LQ` = `0 σ + * ^` | `arithAxioms` (17) | `qDisjunctionProperty_arith` |
| **T** | `LQt` = A `+ τ` | `arithTAxioms` (19) | `qDisjunctionProperty_arithT` |
| **TM** | `LQtm` = T `+ %₂` | `arithTMAxioms` (22) | `qDisjunctionProperty_arithTM` |

**Evidencia, toda por `rfl`** — el kernel verifica las cifras y las dos propiedades que el
fragmento necesita:

| nombre | qué mide |
|---|---|
| `arithAxioms_length` | son **17** |
| `arithAxioms_sentences` / `arithTAxioms_sentences` / `arithTMAxioms_sentences` | cada lista es **invariante bajo `collapseF L ∘ substF zeroS`**: son sentencias de SU lenguaje |
| `arithAxioms_hard` | de los 17, sólo `ax13_lt_def` y `ax19_lt_trichotomy` no son de Harrop |
| `arithTAxioms_hard` | ⭐ **`τ` no añade dureza**: la lista dura no cambia |
| `arithTMAxioms_hard` | `%₂` añade **uno**, `ax21`, **y ya estaba barrado** |

**Las piezas portantes**:

| nombre | enunciado | footprint |
|---|---|---|
| ⭐ `closed_of_grounded` (+ `_list`) | `Grounded LQ t → ClosedQTerm t` — el puente entre las dos descripciones del dominio, **por clausuras** y **por constructores** | `propext, Quot.sound` |
| `ctxA` / `ctxT` / `ctxTM` | `arith*Axioms ++ insts.map inductionFormula` | — |
| `axA'` / `axT'` / `axTM'` | todo axioma del fragmento es hipótesis del contexto | — |
| `hNum_fragment` / `hNumT_fragment` / `hNumTM_fragment` | 🏁 **`hNum` deja de ser hipótesis**: es un teorema sobre el fragmento | `propext, Quot.sound` |
| ⭐ `numeralI_pred` | `⊢ᵢ τ n̄ = (n-1)‾` — **sin inducción en el objeto** | **`propext`** solo |
| ⭐ `numeralI_mod2` | `⊢ᵢ %₂ n̄ = (n%2)‾` — inducción **META**, y ⭐ **sin consistencia** | `propext, Quot.sound` |
| `numOf_grounded` / `numOfM_grounded` (+ `_list`) | todo término anclado en la signatura extendida es demostrablemente un numeral | `propext, Quot.sound` |
| `arithT_of_arith` / `arithTM_of_arithT` / `arithTM_of_arith` | los contextos crecen: lo que valía en A vale en T y en TM | — |
| `slash_arithAxioms` / `slash_arithTAxioms` / `slash_arithTMAxioms` | ⭐⭐ los 17 / 19 / **22** axiomas **barrados** | `propext, Quot.sound` |
| `qDisjunctionPropertyA` / `…T` / `…TM` | la DP con instancias de inducción | `propext, Quot.sound` |
| 🏁🏁🏁 **`qDisjunctionProperty_arithTM`** | **22 de los 34, con una sola hipótesis: la consistencia** | `propext, Quot.sound` |

🔑 **El criterio que sale de medir, y es lo reutilizable**: un símbolo entra en el fragmento
si sus axiomas lo **definen por recursión sobre el constructor** (`0` / `σ`). `τ` y `%₂` lo
hacen. `/₂`, `√` y `−` están **caracterizados por propiedades** —desigualdades, ecuaciones
condicionadas—, y de una caracterización no se despeja sin inducción en el objeto.

⭐ Y cierra un círculo: la capa `LQ`, etiquetada ANDAMIO por no tener uso portante, **es la
signatura del fragmento A**. El andamio era el camino.

➡️ La hipótesis que queda —la consistencia— **cae** en §2.4, `HA/Model.lean`.

---

## 2.5 `HA/Model.lean` — el modelo estándar sobre `ℕ`

**Fichero**: [`PeanoRF/HA/Model.lean`](../PeanoRF/HA/Model.lean)

**Namespace**: `PeanoRF.HA`
**Dependencies**: `PeanoRF.HA.Fragment`, `PeanoRF.Calculus.Soundness`
**Last updated**: 2026-09-21
**Status**: 🏁 `hcon` descargada, y `−` medido

**Un solo modelo con un parámetro**, y el parámetro hace **dos** trabajos:

```lean
def natModelK (k : Nat) : Model Nat where
  func s ds :=
    if s = succ_sym then ds.headD 0 + 1
    else … else if s = sub_sym then
      (if ds.tail.headD 0 ≤ ds.headD 0 then ds.headD 0 - ds.tail.headD 0 else k)
    else 0
  rel s ds := And (s = lt_sym) (ds.headD 0 < ds.tail.headD 0)
```

⭐ `−` va al **monus dentro del rango que `ax29_sub_witness` fija** (`b ≤ a`) y a `k`
**fuera**. El axioma no dice nada de `a − b` con `a < b`, así que ahí el valor es libre — y
eso es lo que convierte el modelo en una **familia**.

| nombre | enunciado | footprint |
|---|---|---|
| `subAxioms` | `arithTMAxioms ++ [ax29_sub_witness]` — los 22 más **el único axioma de `coreAxioms` que menciona `−`** | — |
| `natModelK` | el modelo, parametrizado | — |
| ⭐⭐ `natModelK_sat` | **los 23 axiomas son verdaderos en `natModelK k`, para TODO `k`** | `propext, Quot.sound` |
| `natModel_sat` | los 22 del fragmento, con `k = 0` | `propext, Quot.sound` |
| 🏁 **`hcon_fragment`** | **`ctxTM []` no deriva `⊥`** — por `derivesI_soundness` | `propext, Quot.sound` |
| 🏁🏁🏁 **`qDisjunctionProperty_arithTM_final`** | **la DP del fragmento, SIN NINGUNA HIPÓTESIS** | `propext, Quot.sound` |
| `evalT_zero` / `evalT_succ` / `evalT_sub` | las tres ecuaciones de evaluación que sostienen la sección 4 | `propext, Quot.sound` |
| `eval_numeralM` | en el modelo, los numerales denotan lo que parecen | `propext, Quot.sound` |
| ⭐ `eval_sub_5_7` | **el valor de `5̄ − 7̄` ES el parámetro** | `propext, Quot.sound` |
| ⛔ `sub_neither_of_valid` | la medición **en forma general**: toda teoría válida en `natModelK k` para todo `k` deja `5̄ − 7̄` indeterminado | `propext, Quot.sound` |
| ⛔ **`sub_neither`** | sobre `subAxioms`: **ni `⊢ᵢ 5̄−7̄ = n̄` ni `⊢ᵢ ¬(5̄−7̄ = n̄)`**, para ningún `n` | `propext, Quot.sound` |
| `grounded_sub_5_7` | el testigo está anclado en la signatura **completa** (`LQpp`) | `propext, Quot.sound` |
| ⛔⛔ **`hNum_false_on_sub`** | **`hNum` sobre la signatura completa es FALSA**, con testigo | `propext, Quot.sound` |

⛔ **`∈` se interpreta como siempre falso.** No es un truco: es exactamente lo que
`ax_L1_in_nil` (`∀x. ¬(x ∈ [])`) pide, y es lo único que esta teoría dice de `∈` — los
axiomas `ax_L2_in_cons`/`ax_L3_in_concat` se quedaron fuera de los 23. Igual con `√`, `/₂`,
`::`, `##`, `Π_p`: no se mencionan, así que caen al `else`. **Un modelo sólo tiene que
satisfacer los axiomas que hay.**

⛔ **Alcance de la medición de `−`: `subAxioms` son 23, no los 34 de `coreAxioms`.** Subirlo
pide un modelo de `coreAxioms` entero —listas, pares de Cantor, `√`, `Π_p`—, que este
proyecto no tiene. Queda **dicho y no supuesto**.

🔑 **De método**: «la teoría no dice nada de `t`» se mide **parametrizando el modelo por el
valor de `t`**, no exhibiendo dos modelos sueltos. Un parámetro es más fuerte y más corto.

⚠️ **Dos trampas del módulo**:
* en este archivo la notación `∧` es `Formula.and` (la de FOL), así que la conjunción de
  Lean va escrita **`And`** a mano;
* `omega` aparece en cinco metas y **las cinco son aritméticas** (`<`, `≤`, `+`, `%`).
  Footprint **medido**, no argumentado — ver el encabezado de `Calculus/Soundness.lean`
  para el caso en que `omega` sí contamina.

---

## 2.6 `HA/Axioms.lean` — el conjunto de axiomas de HA

**Fichero**: [`PeanoRF/HA/Axioms.lean`](../PeanoRF/HA/Axioms.lean)

**Namespace**: `PeanoRF.HA`
**Last updated**: 2026-09-06 21:00
**Status**: ✅ Completo
**@axiom_system**: HA finitaria (Q⁺⁺ + esquema de inducción **en el contexto**)
**@importance**: high

Axiomatiza HA **sin postular derivabilidad** (M-8). Compárese con
`ROBINSON_PlusPlus.Full.ax_induction`, que declara `axiom : axioms ⊢ inductionFormula φ`.

**Definición central**:

```lean
def ctx (insts : List Formula) : List Formula :=
  axioms ++ insts.map inductionFormula
```

`insts` es la lista de fórmulas cuyas instancias de inducción entran en el contexto. Es
finita por construcción — eso es lo que hace de HA una teoría r.e. y no ω-lógica — y queda
**en el tipo de cada teorema**: se lee del enunciado qué inducción hizo falta.

**Teoremas** (todos genéricos en `insts`):

| Nombre | Enunciado |
|---|---|
| `mem_ctx_of_mem_axioms` | `f ∈ axioms → f ∈ ctx insts` |
| `ax'` | `f ∈ axioms → ctx insts ⊢ᵢ f` |
| `ind` | `φ ∈ insts → ctx insts ⊢ᵢ inductionFormula φ` |
| `mono` | `insts ⊆ insts' → ctx insts ⊢ᵢ ψ → ctx insts' ⊢ᵢ ψ` |
| `axioms_lift` | `axioms.map (liftFormula 0) = axioms` (por `rfl`: los axiomas son sentencias cerradas) |
| `ctx_lift` | el contexto entero es cerrado si lo son las instancias |
| **`gen_closed`** | **`Γ.map (liftFormula 0) = Γ → Γ ⊢ᵢ A → Γ ⊢ᵢ ∀A`** |
| `Closed` (structure) | `a` invariante bajo `liftTerm k` **y** bajo `substTerm k t`, para todo `k`, `t` |
| `closed_zero` | `Closed zero` |
| `induction_object` | inducción object-level, con la instancia tomada del contexto |

⚠️ **`Closed` es la hipótesis exacta del caso con PARÁMETRO**, y no es la ingenua.
`liftTerm 0 a = a` **no basta**: `inductionFormula` usa `liftFormula 1 φ`, así que el
parámetro aparece levantado a nivel 1 dentro de la instancia, y además sustituido. Con un
parámetro **abierto** no hay generalización finitaria: haría falta meter en el contexto la
**clausura universal** de la instancia. Medido en `sondeos/param_probe.lean`.

🔑 **`gen_closed` es el resultado central**: sobre un contexto cerrado la generalización es
finitaria (`Derives.intro_forall`), luego **la ω-regla `gen` no hace falta**. Lo que `gen`
obtiene de infinitas premisas `Γ ⊢ A[n]`, esto lo obtiene de una prueba uniforme con la
variable libre. Su footprint es `[propext]`.

---

## 2.7 `HA/Numerals.lean` — numerales, y el puente sintaxis ↔ `ℕ`

**Fichero**: [`PeanoRF/HA/Numerals.lean`](../PeanoRF/HA/Numerals.lean)

**Namespace**: `PeanoRF.HA`
**Dependencies**: `PeanoRF.HA.Axioms`
**Last updated**: 2026-09-18
**Status**: ✅ Completo
**@importance**: **foundational**

| nombre | notación matemática | footprint |
|---|---|---|
| `numeralI_add` | `̃a + ̃b = (a+b)̃` | `propext, Classical.choice, Quot.sound` |
| `numeralI_mul` | `̃a · ̃b = (a·b)̃` | idem |
| `numeralI_pow` | `̃a ^ ̃b = (a^b)̃` | idem |
| `ClosedQTerm` | los términos del lenguaje **sin variables** | — |
| ⭐ **`closed_term_eq_numeral`** | `t` cerrado `⟹ ∃n, ctx [] ⊢ᵢ t = ̃n` | idem |

**Por qué se reprobó en vez de reusar** (medido el 2026-09-18, `sondeos/numerals_probe.lean`):
la capa de RPP está enunciada sobre **`⊢`**, la HERRAMIENTA, y el puente va `⊢ᵢ → ⊢₀ → ⊢`
**en un solo sentido** (ADR-017). No es contaminación — `numeral_add`/`mul`/`pow` salen
limpios de ω allí también — es el cálculo.

⭐ El port es barato porque las tres van por **inducción META**: el contexto es `ctx []`, los
axiomas de Q⁺⁺ y nada más. **Ni una instancia de inducción objeto, ni una ω-regla.**

⚠️ Se usa `numeralM` de la capa **Minimal**, no `Full.numeral`: el segundo arrastraría
`Full/Induction.lean` y con él `ax_induction` a la superficie de import.

⚠️ `ClosedQTerm` no es «cerrado» a secas: un `Term.func "foo" []` no tiene variables y **no
es de este lenguaje**. Son los cinco símbolos de Q⁺⁺.

▶ **Para qué**: la cláusula `∀` de la barra de Kleene cuantifica sobre **todos** los
términos cerrados, y la inducción meta sólo alcanza a los numerales. Este lema cierra ese
hueco, y `slash_eq_congr` (H3bis) transporta la barra a través de la igualdad.

⚠️ **Pero no basta para H3ter**, y conviene no leerlo de más: `ClosedQTerm` captura los
términos **del lenguaje** sin variables, y el 2026-09-18 se midió que la sintaxis ambiente
es más grande — `elim_forall` instancia con símbolos ajenos y rompe la DP de HA
(`sondeos/junk_probe.lean`). Este módulo resuelve una de las dos piezas de la etapa 2, no
las dos.

---

## 2.8 `HA/Arith.lean` — primer teorema finitario

**Fichero**: [`PeanoRF/HA/Arith.lean`](../PeanoRF/HA/Arith.lean)

**Namespace**: `PeanoRF.HA`
**Last updated**: 2026-09-06 21:00
**Status**: 🔄 In progress
**@importance**: high

```lean
def phiZeroAdd : Formula := add zero (.var 0) =eq (.var 0)
theorem zero_add : ctx [phiZeroAdd] ⊢ Formula.forall phiZeroAdd
```

`∀x. 0 + x = x` **sin ω-reglas y sin `ax_induction`**. El tipo declara la única instancia
de inducción usada.

**La medición que justifica ADR-016** (`sondeos/h2_probe.lean`):

| símbolo | footprint |
|---|---|
| `PeanoRF.HA.zero_add` | `propext, Classical.choice, Quot.sound` |
| `ROBINSON_PlusPlus.Full.zero_add` | los tres anteriores **+ `MetaRules.gen` + `MetaRules.imp_intro` + `ax_induction`** |

**Tres axiomas menos, misma matemática.** El `Classical.choice` restante es la deuda META
heredada de la codificación `String` de RPP.

---
## 3. Teoremas

| Teorema | Enunciado matemático | Instancias |
|---|---|---|
| `zero_add` | `HA ⊢ᵢ ∀x. 0 + x = x` | `[phiZeroAdd]` |
| `succ_add` | `HA ⊢ᵢ ∀x. σa + x = σ(a + x)`, con `Closed a` | `[phiSuccAdd a]` |

**Footprint medido** (`sondeos/h2c_probe.lean`, 2026-09-16):

| símbolo | footprint |
|---|---|
| `PeanoRF.HA.succ_add` | `propext, Classical.choice, Quot.sound` |
| `ROBINSON_PlusPlus.Full.succ_add_prim` | + **`MetaRules.imp_intro`, `ax_induction_prim`** |
| `PeanoRF.Calculus.derivesI_to_derives0` | `propext` |

---
## 4. Exports

```lean
-- PeanoRF.HA
ctx  ax'  ind  mono  induction_object  gen_closed  Closed   -- HA/Axioms.lean
arithAxioms  arithAxioms_sub                                -- el fragmento vive aquí
numeralI_add  numeralI_mul  numeralI_pow                    -- HA/Numerals.lean
closed_term_eq_numeral                                      -- hNum sobre los numerales
LQ  LQpp  zeroS  zeroS_grounded  closed_grounded              -- HA/Domain.lean
qDisjunctionProperty  qExistenceProperty  haDisjunctionProperty
slash_coreAxioms  haDisjunctionProperty_core                -- HA/SlashAxioms.lean
LQt  LQtm  arithTAxioms  arithTMAxioms  ctxA  ctxT  ctxTM   -- HA/Fragment.lean
qDisjunctionProperty_arith  ..._arithT  ..._arithTM
subAxioms  natModelK  hcon_fragment                         -- HA/Model.lean
qDisjunctionProperty_arithTM_final  sub_neither  hNum_false_on_sub
```

---

## 5. Lo que este nodo NO cubre

* el cálculo `⊢ᵢ`, su solidez, su consistencia sintáctica y la **definición** de la barra
  `Slash T D` ⇒ **[REFERENCE-Calculus.md](REFERENCE-Calculus.md)**;
* el gate que mide los footprints de estas tablas ⇒ **[REFERENCE-Meta.md](REFERENCE-Meta.md)**;
* la tabla de teoremas de cabecera de H3/H3bis/H3ter, con **lo que no dicen** ⇒
  **[REFERENCE.md](../REFERENCE.md)** §4.

---

⬆️ **[Volver al índice raíz](../REFERENCE.md)**
