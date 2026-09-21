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

### 2026-09-21 (b) · ⭐ el control que faltaba: `[H]`, declarado y sin uso

`[B]` caza un símbolo **citado** que no existe; `[H]` caza uno que **existe** y nadie usa.
Era la dirección por la que se coló la capa `LQ`, que hizo falta auditar a mano.

🔑 **La polaridad es todo**: no pregunta «¿está muerto?» sino **«¿está usado O ETIQUETADO?»**.
Tres razones legítimas, y las tres se declaran: 🏁 `ENTREGABLE`, 🏗️ `ANDAMIO`, ⛔ `EVIDENCIA`.
AVISO, no objetivo. Excluye `@[simp]` e instancias, que se usan sin nombrarse.

**Siete hallazgos a la primera, todos legítimos**: cuatro entregables que nadie usa porque
son resultados (`derivesI_to_derives`, `derivesI_consistent`, `succ_add`, `mono`) y tres
andamios (`eqI_congr_fun1`, `closed_zero`, `closed_term_eq_numeral`). Todos etiquetados.

⚠️ De paso delató que **`closed_term_eq_numeral` se quedó sin consumidor el 2026-09-18**, al
retirarse `qExistenceProperty_numeral`. Nadie lo había notado.

✅ **Probado en las dos direcciones a la vez** (ADR-015): un teorema sin marcador —lo caza—
y otro con él —lo exime—, en la misma pasada.

### 🚨 Y la QUINTA forma de dar verde sin comprobar: el `grep` del entorno

El marcador no eximía a `existence_property`, que lleva un 🏁. Medido:

| | bytes | `grep` | `LC_ALL=C grep` |
|---|---|---|---|
| `✅` `⏳` `⛔` | 3 | ✓ | ✓ |
| `🏁` `🏗` `🗑` `🔶` | 4 | **✗** | ✓ |

Bajo `es_ES.UTF-8`, `grep` casa los emoji del plano básico y **falla sin decir nada** con los
del astral. Un patrón que no casa nunca es una **alternativa muerta**, y el control sigue en
verde — `[B]` llevaba desde su nacimiento con `🗑` muerto en `DEAD_MARKER`.

⇒ `LC_ALL=C grep` en los tres sitios donde se comparan marcadores (`[H]`, `[B]` y el `✅` de
`[G]`, que hoy funciona pero se invertiría el día que alguien marque con 🏁). Y palabras
ASCII como marcador primario. ADR-032 y ADR-033.

🔑 No basta con escribir bien el control: hay que comprobar que **la herramienta hace lo
que uno cree**. Esta quinta no es del código, es del ENTORNO.

**49 jobs · 16 módulos · 0 sorry · 267 declaraciones.**

### 2026-09-21 · 🚨 auditoría externa — la CI en rojo y el gate ciego, con los controles en verde

Auditoría de lectura de FOL, ROB++ y Peano, y después de PeanoRF. Los tres controles
locales daban verde. Debajo había dos cosas serias.

**1 · La CI llevaba dos días en ROJO, y la causa era el control que añadí el 09-19.**
`[D]` lee la frescura con `git log -1 -- <fichero>`, y `actions/checkout@v4` hace un checkout
**shallow**: con un commit de historia git atribuye CUALQUIER fichero a HEAD. Falló con
`DEPENDENCIES.md`, que el commit ni siquiera tocaba. ⇒ `fetch-depth: 0` en el workflow **y**
una guarda `is-shallow-repository` que pone `[D]` en ROJO si falta — las dos, porque una sola
se deshace sin que nadie lo note. **Probada contra un clon `--depth 1` real.**
🔑 Y la lección: cerré la sesión diciendo «verde» sin mirar la CI ni una vez.

**2 · El gate se había quedado CIEGO al cálculo de la tesis.** FOL generizó su sintaxis por el
símbolo (sus ADR-069/071) y `Derives₀` pasó a `{Sym : Type} : List (FormulaG Sym) → …`. El
telescopio miraba la constante `Formula` ⇒ **21 constructores, 3 de ellos clásicos, dejaron
de estar vigilados**, y `mentionsFormula` fallaba igual, así que ni salía como
casi-candidato. Medido: **45 constructores → 42 y 12 clásicos → 9** sin cambiar una línea.

⇒ `isFormulaLike` reconoce `Formula` y `FormulaG _`, y el telescopio **atraviesa los binders
de sort**. Cifras restauradas **al dígito**: 7 relaciones, 45 constructores, 12 clásicos.
✅ **Probado** con un teorema que usa `Derives₀.dne_rule`: el gate lo caza como `OBJETO`.
⚠️ No hubo brecha — PeanoRF usa 18 constructores de `Derives₀`, ninguno clásico.

**3 · La CI deja de correr `--quick`**, que se saltaba `[A] jobs` y `[E] alcance del gate`.
Anunciarlo no es comprobarlo, y `[E]` es justo el que caza (2). Medido antes: el segundo
build sale del caché y Lean **reproduce los `logInfo`**, así que `[E]` mide igual.

**4 · La capa `LQ` queda marcada como EVIDENCIA y ANDAMIO.** Sin uso portante desde el
rediseño a `Grounded LQpp`: sólo se usa entre sí. Se queda — `not_closed_add_unary` es la
evidencia de ADR-028, el resto es por donde se empezará `hNum` — pero ahora lo **dice**,
porque el control `[B]` de símbolos muertos está desactivado y nada lo diría si no.

**De los vecinos**: Peano congelado (ADR-018, julio); ROB++ con la superficie que usamos
congelada desde el 09-16; **FOL en plena generización por el símbolo** — es el que se mueve
debajo. ADR-030 (enmienda) y ADR-031.

**5 · Control `[B]` ACTIVADO**, y cazó **seis** a la primera. Llevaba vacío desde el
2026-09-06 «hasta que existan familias de símbolos propias» — y para entonces ya había
quince. Lo que encontró, todo en documentos AUTORITATIVOS:

* ⛔ **`qExistenceProperty_numeral` NO EXISTE** y lo anunciaban `REFERENCE`, `NEXT-STEPS` y
  ADR-029, con 🏁 y footprint. Se retiró del código el 09-18 al rehacer el dominio sobre
  `Grounded LQpp`; las tres tablas se quedaron con la fila. **Tres días anunciando un
  teorema que no está.**
* ⛔ **`closed_zeroS` NO EXISTE**, y también tenía fila en `REFERENCE`.
* `zeroS_closed` → se llama `zeroS_grounded`.
* `Derives0` escrito con cero ASCII en vez de `Derives₀`.
* El `DerivesL` de ADR-029 es hipotético y descartado: marcado como tal.
* Y de propina, sin que `[B]` lo viera: el `@importance` de la sección de `Domain.lean`
  estaba **mutilado** (`****:`) por un reemplazo mal hecho.

⚠️ Lo que `[B]` **no** caza es la dirección contraria — declarado y sin usar —, que es lo
que le pasó a la capa `LQ`. Lo dije al revés en el informe de auditoría: ese control no
existe, y por eso la capa va etiquetada a mano.

**49 jobs · 16 módulos · 0 sorry · 267 declaraciones.**

### 2026-09-19 · ARMONIZA — los dos controles en verde, y seis fechas falsas debajo

Pasada de lectura con `check-doc-sync` y `check-coherencia` **los dos en verde**. Hallazgos
reales, ninguno mecanizable por los controles tal y como estaban:

1. ⚠️ **SEIS documentos con la marca de tiempo FALSA** — `REFERENCE` y `PLANNING` decían
   09-16, `CURRENT-STATUS` y `NEXT-STEPS` 09-17, y **`DECISIONS` y `AI-GUIDE` decían 09-06
   con cuatro ADR nuevos dentro**. [D] comprobaba que la marca **existiera**.
   ⇒ **ADR-030**: ahora la compara con `git log -1 --date=short` y **rompe** si es anterior.
   🔑 Es la **cuarta forma de dar verde sin comprobar**, y la más sutil: las otras tres
   callan o no miden; ésta **mira la FORMA en vez del CONTENIDO**.
2. El **banner** de `CURRENT-STATUS` decía «siguiente, H4» con **tres etapas de H3ter
   hechas**. ⚠️ Lo señalaba [G], y se despachó **dos veces** como «falso positivo conocido»:
   lo era el 09-17 y dejó de serlo después. **Un aviso que se adjudica por costumbre deja de
   ser un aviso.**
3. El **roadmap** de `PLANNING` daba H3ter como «etapa 1 ✅, etapas 2–3 abiertas». Las tres
   están hechas.
4. La **tabla de riesgos** de `PLANNING` seguía ofreciendo `DerivesL` o Craig para restringir
   al lenguaje — una decisión ya tomada, y resuelta el 09-18 **sin ninguna de las dos**.
5. `check-coherencia.bash` imprimía su lista de puntos ciegos **fechada el 2026-09-18** como
   si fuera actual, y al menos uno ya no existía. Reescrita como **arquetipos**, no
   hallazgos, con los dos nuevos de hoy dentro.
6. «22 teoremas» en el banner, sin fecha, cuando hoy son 147. Fechado.

Ruido descartado: ninguno — el único aviso de [G] resultó ser real. Y el falso positivo que
SÍ apareció fue de cosecha propia: un `✅` dentro de la fila de H3ter hacía a [G] gritar; se
reescribió, porque **un control que grita en falso deja de leerse** (ADR-026).

Sin cambios en el código. **49 jobs · 16 módulos · 0 sorry · 267 declaraciones.**

### 2026-09-18 (k) · 🏁🏁 los SEIS duros, y con ellos los 34 axiomas de `coreAxioms`

Por orden de la tabla, y todos en `[propext, Quot.sound]`:

* **`ax21_mod2_range`** — `hNum` da `k̄` con `⊢ᵢ %₂t = k̄`, pero no dice que `k` sea 0 ó 1: si
  `k ≥ 2`, las dos ramas del axioma dan `⊥`. Aquí la **consistencia deja de ser decorativa**.
* **`ax_L2_in_cons`** — y **sin** consistencia: una de las dos ramas es una IGUALDAD,
  refutable con `numeralI_ne`, y la disyunción del objeto entrega la otra.
* **`ax13_lt_def`** — el primero que exige **construir** y no sólo elegir: si `n < m` el
  testigo es `m-n-1`; si no, `numeralI_not_lt` refuta.
* **`ax14_sqrt_le`** — `≤` es `< ∨ =`, por eso no era de Harrop pese a parecer atómico.
* **`ax_L3_in_concat`** — bajo `hIn`, la decidibilidad de `∈`. ⚠️ **Hipótesis, no teorema.**

⭐⭐ **La pieza que costó**: `addI_succ_ne` — *ningún numeral es `x + σy`*. Q⁺⁺ no prueba la
cancelación de la suma (eso pide inducción en el objeto), pero **para un numeral concreto la
recursión META la sustituye**: `σc̄ + σj = σc̄` se reduce por conmutatividad, `ax5` y la
inyectividad de `σ` a `c̄ + σj = c̄`, que es la hipótesis de inducción. La base la cierra `ax2`.
De ahí sale `numeralI_not_lt`, que es lo que `ax13` y `ax14` pedían.

🏁🏁 **`slash_coreAxioms`**: los 34 axiomas barrados. Y **`haDisjunctionProperty_core`**: la
DP de HA con `coreAxioms` YA DESCARGADO. Lo que queda va como hipótesis, todas dichas:

| | qué es | ¿aquí? |
|---|---|---|
| `hcon` | consistencia de la teoría | ⛔ no (Gödel) |
| `hlift` | contexto invariante bajo levantamiento | ✅ si las instancias son cerradas |
| `hNum` | todo anclado es demostrablemente un numeral | ⏳ faltan 8 de los 13 símbolos |
| `hIn` | `∈` decidible sobre anclados | ⛔ pide inducción sobre listas |
| `hInd` | el esquema de inducción barrado | ⏳ |

⚠️ `hlift` apareció sola: dentro de `elim_ex` el contexto **se levanta**, y los axiomas
tienen que seguir estando. `coreAxioms` lo es (`axioms_lift`); las instancias, sólo si son
cerradas. Por eso los lemas de instancia van parametrizados por `hΓ` y no fijados a `ctx`.

**49 jobs · 16 módulos · 0 sorry · 267 declaraciones · deuda heredada 0.**

### 2026-09-18 (j) · ⭐⭐ etapa 3 — Harrop tumba 28 de 34, y `ax19` cae por medición

**La pieza**: `slash_of_isHarrop`. Para una fórmula de **Harrop**, estar barrada no es más
que ser derivable. La clase se lee de los casos de la barra, mirando cuáles NO piden testigo:
`atom`/`eq` sí, `a ∧ b` si ambas, **`a ⇒ b` si lo es `b` — el antecedente da igual**, `∀a` si
lo es `a`, y `⊥` **si `T` es consistente**. `∨` y `∃`, no.

Medido sobre `coreAxioms`: **28 de los 34**. Y con ellos, `haDisjunctionProperty`: la DP de
HA reducida a **tres obligaciones** — consistencia, los 6 no-Harrop, y el esquema de
inducción.

⭐⭐ **Y uno de los seis ya está**: `slash_ax19`, el axioma que motivó todo el parámetro de
dominio. `hNum` baja los términos a numerales, `Nat.lt_trichotomy` decide **en el meta**, y
`numeralI_lt` + la reescritura dentro de un PREDICADO suben la decisión al objeto.

⭐ **`numeralI_ne` constructivo**: aguas arriba `numeral_ne` arrastra `Classical`. Éste se
construye con `ax2` y `ax3` y mide `[propext, Quot.sound]`.

⚠️ **DOS CORRECCIONES que salieron de medir, no de estimar**:

* La lista dura es de **SEIS**, no de cinco, y no es la que estaba escrita:
  `ax29_sub_witness` **sí** es de Harrop, y `ax14_sqrt_le` y `ax_L2_in_cons` **no** lo son.
* ⛔ **`LQ` no servía para HA**: tiene los 5 símbolos de los numerales y los axiomas usan
  **trece**. Colapsar con `LQ` los mutila ⇒ `hT` sería insatisfacible y el teorema, cierto y
  vacío. Cazado porque `coreAxioms.map (collapseF LQ ∘ substF zeroS) = coreAxioms` **no
  cerraba por `rfl`**.

⇒ El dominio se rediseñó: **`Grounded L t` se define POR SUS DOS CLAUSURAS** —el colapso lo
fija, ninguna sustitución lo toca— en vez de por un inductivo por lenguaje. Así
`grounded_fix` y `grounded_collapse_subst` son literalmente lo que L2 pide, para cualquier
signatura.

**49 jobs · 16 módulos · 0 sorry · 248 declaraciones · deuda heredada 0.**

### 2026-09-18 (i) · 🏁🏁 la FORMA (c) — la etapa 2 de H3ter, CERRADA

L2 demuestra ahora la barra de la instancia **COLAPSADA**:

```lean
slash_of_derives (T) (D) (L)
    (hDfix : ∀ u, D u → collapseT L u = u)
    (hDsub : ∀ ρ, (∀n, D (ρ n)) → ∀ t, D (collapseT L (substT ρ t)))
    (h : Γ ⊢ᵢ f) : … → Slash T D (collapseF L (substF ρ f))
```

El colapso viaja **dentro** de la inducción, así que la obligación de `elim_forall` pasa de
`D (substT ρ t)` —falsa para `ClosedQTerm`— a `D (collapseT L (substT ρ t))`, que sí sale.
Y `hDfix`/`hDsub` **son exactamente** `collapse_fix_closed` y `closed_collapse_subst` de
`HA/Domain.lean`, sin adaptador ninguno.

🏁 **Lo que esto da** (`HA/Domain.lean`, todo en `[propext, Quot.sound]`):

```
qDisjunctionProperty       : axiomas barrados → T ⊢ᵢ A ∨ B → T ⊢ᵢ A ∨ T ⊢ᵢ B
qExistenceProperty         : … → ∃ t, ClosedQTerm t ∧ T ⊢ᵢ A[t]
⭐ qExistenceProperty_numeral : …y ese testigo es demostrablemente igual a un NUMERAL
```

La DP y la EP **para cualquier teoría de Q⁺⁺ cuyos axiomas estén barrados**.

⭐ **H3bis NO se debilita**: con `L` total el colapso es la identidad (`collapseF_trivial`) y
con `D` total la clausura es trivial, así que `disjunction_property`, `existence_property` y
`derivesI_ne_derives0` salen con el enunciado literal de antes y el mismo footprint.

⚠️ La hipótesis «`A ∨ B` es una sentencia del lenguaje» va como **una sola ecuación**,
`collapseF LQ (substF zeroS (A ∨ B)) = A ∨ B`. Comprobado que **no es vacía**, con un ejemplo
que la cumple por `rfl` — una hipótesis insatisfacible haría el teorema cierto y vacío.

⚠️ `rewrite_at` pidió una pieza más: **`collapseF_substF`**, la conmutación con la
sustitución PARALELA, porque `slash_rewrite` está enunciada sobre `substF`. Ya estaba medida
en el sondeo (g).

⚠️ Trampa nueva: **`g ∈ T` no se puede escribir en `HA/Domain.lean`** — `∈` está sobrecargada
y elabora su lado derecho como un TIPO (`type expected, got (T : List Formula)`). Se escribe
`List.Mem g T`. La tercera de la familia, tras el `σ` de `peanolib` y el `∧`/`∨` de `FOL`.

⏳ Queda **sólo la etapa 3**: `hT` para los 34 axiomas de `coreAxioms`.

**48 jobs · 15 módulos · 0 sorry · 225 declaraciones · deuda heredada 0.**

### 2026-09-18 (h) · ⭐ `Slash T D` — la barra con parámetro de DOMINIO

La pieza (1) de la etapa 2 de H3ter. Las cláusulas de `∀` y `∃` de la barra cuantifican
sobre `D`, no sobre todos los términos:

```lean
| .forall a => (T ⊢ᵢ ∀a) ∧ (∀ t, D t → Slash T D (a[t]))
| .ex a     => ∃ t, D t ∧ Slash T D (a[t])
```

Sin eso **`ax19_lt_trichotomy` no se puede barrar**: su `∀` recorre términos de los que HA
no sabe nada, y la DP de HA no se podía ni enunciar.

✅ **H3bis intacto**: `disjunction_property`, `existence_property` y
`derivesI_ne_derives0` salen como la instancia `D = fun _ => True`, con el mismo
`[propext, Quot.sound]`.

⚠️ **`D` entra en L2 como una CLAUSURA, no como una lista** (ADR-027):

```lean
hDsub : ∀ ρ, (∀ n, D (ρ n)) → ∀ t, D (substT ρ t)
```

que es exactamente lo que piden `elim_forall` e `intro_ex`. Con `D = ClosedQTerm` esa
clausura es **FALSA** —`t` puede llevar símbolos ajenos—, y eso **no es un defecto**: es lo
que obliga a la **forma (c)**, que L2 afirme la barra de la instancia COLAPSADA. La versión
verdadera, `closed_collapse_subst`, ya está en `HA/Domain.lean`.

⚠️ `existence_property_of_slashed` devuelve ahora el testigo **con** su pertenencia a `D`.

⏳ Hasta que esté la forma (c), `D = ClosedQTerm` **no se puede instanciar**. Queda dicho
para que no se lea de más.

**48 jobs · 15 módulos · 0 sorry.**

### 2026-09-18 (g) · la signatura del colapso lleva la ARIDAD, y el dominio ya está cerrado

**`collapseT` pasa de `L : String → Bool` a `L : String → Nat → Bool`**, con el predicado
aplicado a `ts.length`. El contraejemplo que lo obliga está en producción, no en el cuaderno:

```
not_closed_add_unary : ¬ ClosedQTerm (Term.func add_sym [zero])      [propext]
```

`+` con UN argumento es un término legítimo de la sintaxis, cerrado y con símbolos de Q⁺⁺ —
pero Q⁺⁺ no tiene ningún axioma sobre él, luego no es demostrablemente igual a ningún
numeral, que es lo único que la etapa 3 le pide al dominio. El colapso anterior lo dejaba
pasar. Precio medido: tres lemas de longitud; las conmutaciones no cambiaron de forma, y
**`derivesI_collapse` conserva su `[propext, Quot.sound]`**.

**Módulo nuevo `HA/Domain.lean`** con las **dos clausuras que L2 pedirá**, medidas antes de
escribir L2 (`sondeos/collapse_parallel_probe.lean`):

```
collapse_fix_closed   : ClosedQTerm u → collapseT LQ u = u                  [propext]
closed_collapse_subst : (∀n, D (ρ n)) → ∀ t, D (collapseT LQ (substT ρ t))  [propext, Quot.sound]
```

⭐⭐ La segunda es la que cierra `elim_forall`: con `ρ` valuada en el dominio, el colapso de
`substT ρ t` cae en el dominio **para `t` arbitrario** — símbolos ajenos y aridades erróneas
incluidos. ⇒ La forma (c) de L2 (demostrar la barra de la instancia **colapsada**) es la
buena, y el cálculo indexado por el lenguaje queda descartado por medición.

⚠️ Trampa nueva, de la familia del `σ`: bajo `open FOL` **no se pueden escribir `∧` ni `∨`**,
que las tiene tomadas `FormulaG`. `(s = zero_sym ∧ n = 0)` da `unexpected token =`.

**48 jobs · 15 módulos · 0 sorry · 212 declaraciones · deuda heredada 0.**

### 2026-09-18 (f) · ⭐ `derivesI_collapse` — la etapa 2 de H3ter pierde su pieza cara

```
derivesI_collapse : Γ ⊢ᵢ f → Γ.map (collapseF L) ⊢ᵢ collapseF L f   [propext, Quot.sound]
```

De una derivación que instancia con símbolos **ajenos al lenguaje** sale otra que no lo hace,
con el mismo contexto y la misma conclusión colapsados. Las cinco conmutaciones previas, en
**`[propext]`**.

⇒ El contraejemplo del `junk_probe` deja de ser un obstáculo y pasa a ser **lo que justifica
restringir al lenguaje**. La ruta cara —un cálculo paralelo `DerivesL`— **no hace falta**.

⭐ Sale más barato que `derivesI_subst` porque el colapso **no cambia al entrar bajo una
ligadura**, así que su navegación de `rewrite_at` no va indexada por `posDepth`.

⚠️ **Nota de aguas arriba**: FOL migró hoy la sintaxis a `inductive FormulaG (S : Type)` con
`abbrev Formula := FormulaG String` (su ADR-065/066, el parámetro genérico de símbolos). Es
**compatible hacia atrás** y nuestro build no se enteró — 47 jobs verdes —, pero conviene
saberlo: `Formula.impl` sigue resolviendo por el `abbrev`, y el constructor real es
`FormulaG.impl`.

**47 jobs · 14 módulos · 0 sorry · 201 declaraciones · deuda heredada 0.**

### 2026-09-18 (e) · un control para lo que los otros cinco no miran

**`check-coherencia.bash`** + el comando **`/armoniza`** (ADR-026, AI-GUIDE §28).

§27 comprueba que los documentos cuadren con el CÓDIGO. Esto comprueba que cuadren ENTRE
SÍ. El 2026-09-18, con los cinco controles en verde, había tres contradicciones vivas.

* **[F] REGISTRO DE HITOS**, bloqueante: todo hito mencionado tiene fila en el roadmap.
* **[G] ESTADO CONTRA PROSA**, aviso: un hito ✅ del que la prosa dice «falta», o al revés.
* **La pasada de lectura**, en el comando, porque *una afirmación puede ser falsa sin
  contradecir a ninguna otra* — y eso no lo caza un grep. El script **imprime siempre lo
  que NO mira**.

⭐ **Cazó un hallazgo real en su primera ejecución**: la sección «H3 ❌ Pendiente» de
`NEXT-STEPS.md`, del plan del 6 de septiembre, cuyo plan incluía «soundness por inducción
sobre los constructores de `Derives`» — que **ADR-017 declaró imposible**. Doce días de
deriva que la pasada de lectura de esa misma tarde no había visto.

Probado (ADR-015) mencionando un identificador de hito sin fila en el roadmap: exit 1.
⚠️ Y cazó acto seguido su propio ADR, que escribía ese identificador literalmente.
Y [G] calibrado el mismo día excluyendo
`DECISIONS.md`, porque un ADR narra su contexto histórico por diseño.

### 2026-09-18 (d) · H3ter etapa 1: la barra, relativa a la TEORÍA

**`Slash T f`** — la teoría pasa a ser parámetro (ADR-025). Estaba clavada a `[]`, lo que
bastaba para H3bis pero **hacía imposible enunciar la DP para HA**: `Slash g` para un
axioma significaba «derivable desde nada».

```lean
disjunction_property_of_slashed : (∀ g ∈ T, Slash T g) → T ⊢ᵢ A ∨ B → T ⊢ᵢ A ∨ T ⊢ᵢ B
```

✅ **H3bis intacto**: `disjunction_property`, `existence_property` y `derivesI_ne_derives0`
son ahora instancias `T = []` — hipótesis vacía — y miden lo mismo.

⚠️ Un detalle que sólo aparece al parametrizar: el caso base de `cut_context` deja de ser
la identidad y necesita **debilitamiento** de `[]` a `T`.

⛔ **Y destapó que `ha_ctx_slashed` no sale con esta barra.** Su cláusula `∀` cuantifica
sobre todos los términos, y `ax19_lt_trichotomy : ∀a∀b (a<b ∨ a=b ∨ b<a)` exigiría una
rama derivable para dos variables libres. No es difícil: es **falso**. La barra de Kleene
para una teoría va sobre **numerales** — y ahí entra `closed_term_eq_numeral`.

📏 Medido sobre los 34 axiomas de `coreAxioms`: **25** con matriz atómica (barra =
derivabilidad), ~4 `⇒`/`⇔` con partes atómicas, y **5** que piden decidir en el meta.

### ⭐⭐ 2026-09-18 (c) · deuda META heredada: de 14 declaraciones a CERO

`HA.ctx` pasa de `axioms` a **`coreAxioms`** (ADR-024). Lo destapó el agente de RPP
midiendo SU puerta en vez de aceptar mi diagnóstico de la mía: de los 109 constituyentes de
`axioms` sólo cinco arrastran `Classical.choice`, y **`coreAxioms` no depende de ninguno**.

```
PeanoRF.HA.ctx                 →  does not depend on any axioms
zero_add / succ_add / numeralI_*  →  [propext, Quot.sound]
```

⭐ **No es un truco de footprint, es una corrección**: los cinco sucios son axiomas del
verificador object de demostraciones de RPP, y no pintaban nada en el contexto de la
Aritmética de Heyting. `ctx` los arrastraba por usar la lista grande.

⭐ **`metaDebtIsError := true`** — llevaba en `false` desde el 2026-09-06. El eje META deja
de avisar y **rompe el build**. Probado (ADR-015) con un módulo temporal que usa la lista
grande: el gate lo rechaza.

✅ Y RPP deja de estar en nuestro camino crítico: su migración `String → List Char` pasa a
ser decisión suya por sus razones. Respuesta en `doc/RESPUESTA-RPP-2026-09-18.md`.

⚠️ Cambia la teoría y se dice: si algún día H7 quiere hablar de la demostrabilidad object
de RPP, esos axiomas vuelven **explícitamente y con su coste medido**, no por arrastre.

### 2026-09-18 (b) · H3ter arranca: los numerales sobre `⊢ᵢ`, y `closed_term_eq_numeral`

**`Calculus/Eq.lean`** — congruencia GENÉRICA por símbolo de función
- `eqI_congr_fun1`, `eqI_congr_fun2_l`, `eqI_congr_fun2_r`, `eqI_congr_fun2`. Las
  operaciones son `Term.func s […]`, así que **una prueba por aridad** cubre `add`, `mul`,
  `pow` y las que vengan, en vez de seis copias del patrón de `eqI_congr_succ`.
  Footprint `[propext, Quot.sound]`.

**`HA/Numerals.lean`** — módulo nuevo
- `numeralI_add`, `numeralI_mul`, `numeralI_pow` — los tres homomorfismos, por inducción
  META: contexto `ctx []`, **ni una instancia de inducción objeto, ni una ω-regla**.
- `ClosedQTerm` + ⭐ **`closed_term_eq_numeral`**: todo término del lenguaje sin variables
  es demostrablemente un numeral. Es el ingrediente que le falta a H3ter.
- ⚠️ Reprobado, no reusado: la capa de RPP está sobre `⊢` y el puente va en un solo
  sentido. Medido antes (`sondeos/numerals_probe.lean`), no supuesto.

**46 jobs · 13 módulos · 0 sorry · 180 declaraciones vigiladas.** Sin tocar FOL ni RPP.

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
