# Next Steps — PeanoRF

**Última actualización:** 2026-09-22
**Autor**: Julián Calderón Almendros

> Fases de desarrollo a corto y medio plazo. Para el rumbo largo, ver
> [PLANNING.md](PLANNING.md).

---

## 🎯 SIGUIENTE SESIÓN

> 🏁🏁🏁 **LA DP DEL FRAGMENTO ES INCONDICIONAL — 26 de los 34 axiomas**, diez símbolos,
> **ninguna hipótesis** (`qDisjunctionProperty_arithTDCS_final`). 22 el 2026-09-21 con
> ADR-039 —cuando `hcon` cayó con un modelo estándar sobre `ℕ`—, luego 23 (`/₂`, ADR-042),
> 24 (`::`, ADR-044) y 26 (`√`, ADR-045). Y el mismo modelo, parametrizado por el valor de
> `−` fuera del rango de `ax29`, **mide** que `5̄ − 7̄` es indeterminado.
>
> 📋 **Cuadro de mando: [doc/TABLERO-FRAGMENTO.md](doc/TABLERO-FRAGMENTO.md)** — los 34
> axiomas y los 14 símbolos con su estado y su razón.
>
> ▶ **Punto de reanudación**: el **modelo de `coreAxioms` entero** —subiría la medición de
> `−` de 27 axiomas a 34 y haría MEDIBLE la no-derivabilidad de las ramas de `junk_probe`—
> y las dos deudas no matemáticas. ⛔ Lo que NO tiene camino por aquí son los cinco de
> lista: piden inducción sobre listas, que `coreAxioms` no tiene.

**H3ter — y lo primero es mirar si FOL ha contestado.**

⛔ **El enunciado ingenuo de H3ter es FALSO, y está medido** (`sondeos/junk_probe.lean`):

```lean
ctx [] ⊢ᵢ (lt foo bar ∨ foo = bar ∨ lt bar foo)      -- derivable, [propext]
```

con `foo`, `bar` símbolos **ajenos al lenguaje**. `Term` es genérica y `elim_forall`
instancia con cualquier término. Ninguna rama es derivable (argumento por solidez, **no
formalizado**). ⇒ HA sobre la sintaxis genérica **no tiene** la propiedad de disyunción.

### Lo hecho

✅ **Etapa 1** (ADR-025): la barra es relativa a la teoría. H3bis = instancia `T = []`,
intacto. Teorema general:

```lean
disjunction_property_of_slashed : (∀ g ∈ T, Slash T g) → T ⊢ᵢ A ∨ B → T ⊢ᵢ A ∨ T ⊢ᵢ B
```

✅ `closed_term_eq_numeral` y los tres homomorfismos (`HA/Numerals.lean`).

### Etapa 2 — decidida, y con DOS piezas, no una

1. ✅ **Parámetro de dominio `Slash T D` — HECHO** (`Calculus/Slash.lean`). Las cláusulas
   de `∀` y `∃` cuantifican sobre `D`. H3bis sobrevive como la instancia
   `D = fun _ => True`, con el mismo footprint `[propext, Quot.sound]`.
   Y con él, las **dos clausuras del dominio** ya medidas en `HA/Domain.lean`.
2. ✅ **Restringir las derivaciones al lenguaje — HECHO** (`Calculus/Collapse.lean`):
   **`derivesI_collapse`**. No hizo falta ni un `DerivesL` paralelo ni esperar a Craig: se
   **transforma** la derivación en vez de restringirla. Y la espera habría sido mala
   apuesta — el ADR-065 de RPP mide que el puente a `LKp` no tiene camino barato.

✅ **FORMA (c) — HECHA** (`Calculus/Slash.lean`). L2 demuestra ahora la barra de la
instancia **COLAPSADA**:

```lean
slash_of_derives (T) (D) (L)
    (hDfix : ∀ u, D u → collapseT L u = u)
    (hDsub : ∀ ρ, (∀n, D (ρ n)) → ∀ t, D (collapseT L (substT ρ t)))
    (h : Γ ⊢ᵢ f) : ∀ ρ, (∀n, D (ρ n)) → (∀ g ∈ Γ, Slash T D (collapseF L (substF ρ g)))
      → Slash T D (collapseF L (substF ρ f))
```

y las dos clausuras de `HA/Domain.lean` **son exactamente `hDfix` y `hDsub`**, sin adaptador.
De ahí salen `qDisjunctionProperty` y `qExistenceProperty` — la DP y la EP para
**cualquier teoría de Q⁺⁺ cuyos axiomas estén barrados**, con el testigo **anclado**
(`Grounded LQpp`). ⚠️ **No «igual a un numeral»**: eso lo decía esta línea y dejó de ser
cierto el 2026-09-18, cuando el dominio pasó de los cinco símbolos de los numerales a los
**trece** del lenguaje. La cláusula del numeral vuelve cuando esté `hNum`.

⭐ Y **H3bis no se debilitó**: con `L` total el colapso es la identidad (`collapseF_trivial`)
y con `D` total la clausura es trivial, así que `disjunction_property` y `existence_property`
salen con el enunciado literal de antes y el mismo `[propext, Quot.sound]`.

⚠️ El caso `rewrite_at` fue el que pidió la pieza extra: para aplicar `slash_rewrite`, que
está enunciada sobre `substF`, hay que mover el colapso al otro lado ⇒ **`collapseF_substF`**,
la conmutación con la sustitución PARALELA, que el sondeo (g) ya había medido.

### Etapa 3 — 🏁 LOS 34, HECHA

✅ **28 por HARROP** (`slash_of_isHarrop`) y ✅ **los 6 duros uno a uno**: `ax13`, `ax14`,
`ax19`, `ax21`, `ax_L2`, `ax_L3`. De ahí `slash_coreAxioms` y

```lean
haDisjunctionProperty_core : la DP de HA con `coreAxioms` YA DESCARGADO
```

#### Lo que queda, y es lo único

| hipótesis | qué es | siguiente paso |
|---|---|---|
| ✅ `hInd` | **HECHO** (ADR-034): `isHarrop (inductionFormula φ) = isHarrop φ` por `rfl`. ⛔ Para instancias de Harrop; con `∨` o `∃` no hay atajo |
| `hNum` | todo anclado es demostrablemente un numeral | evaluar `√`, `/₂`, `%₂`, `τ`, `−`, `::`, `##`, `Π_p` sobre numerales; algunas piden inducción |
| ✅ `hlift` | **HECHO**: `inductions_lift` + `ctx_lift`, reducido a una condición por instancia que es `rfl` |
| `hIn` | `∈` decidible sobre anclados | ⛔ pide inducción sobre listas; puede que nunca salga de Q⁺⁺ sola |
| ✅ `hcon` | la consistencia de la teoría | 🏁 **DESCARGADA el 2026-09-21** (ADR-039): `hcon_fragment`, por un modelo estándar sobre `ℕ` y `derivesI_soundness`. ⛔ Aquí ponía «se queda para siempre, Gödel II» — **era falso**: Gödel II dice que HA no prueba su PROPIA consistencia |

### ⚠️ Deudas vivas

- 📋 **`doc/TABLERO-FRAGMENTO.md`** es el cuadro de mando: los 34 axiomas y los 14 símbolos
  con su estado y su razón, y las cifras verificadas por el kernel en
  `sondeos/audit_fragmento.lean`. **Mirarlo antes de decidir el siguiente paso.**
- **Formalizar la no-derivabilidad de las ramas** del contraejemplo. Hoy es argumento por
  solidez; en esta familia un argumento no es una medición. ⭐ Y desde ADR-039 se sabe **con
  qué herramienta**: un modelo. `sub_neither` es la plantilla.
- 🔶 **`√`** — EN CURSO. ✅ **`/₂` CERRADO el 2026-09-22 y EN PRODUCCIÓN** (ADR-042):
  `PeanoRF/HA/Order.lean` + `numeralI_div2` + `qDisjunctionProperty_arithTD_final`, **23 de
  los 34 axiomas sin ninguna hipótesis**. Lo que queda de esta deuda es `√`, con dos de sus
  tres piezas puestas y marcadas 🏗️ ANDAMIO.
  (Historia de cómo se llegó, `sondeos/sqrt_div2_probe.lean`.) ⛔ Y lo primero
  que salió es que **la razón que daba ADR-037 no se sostiene**: decía que `/₂` «pide
  cancelación de `+` y `·`», y la cancelación no hace falta — la caracterización se despeja
  **por el ORDEN**. Medido ya, todo en `[propext, Quot.sound]`:
  · `exI_of_ltI` / la dirección ⇒ de `ax13` para términos **anclados**;
  · `notI_lt_zero` — nada es menor que cero (`ax5` + `ax2`);
  · ⭐⭐ **`zeroI_or_succ`** — «todo término anclado es `0` o sucesor», **que Robinson Q
    POSTULA** (su axioma 3) y `coreAxioms` **no tiene**: se deriva de la tricotomía.
  🏁 **`/₂` RESUELTO el 2026-09-22, y en contra de ADR-037: SÍ está determinado.**
  `numeralI_div2 : ⊢ᵢ /₂ n̄ = (n/2)‾`, en `[propext, Quot.sound]`. La cadena que lo cierra:
  `addI_assoc` · `ltI_of_add` · ⭐ `ltI_add_right` (monotonía de `+`) · `mulI_two`
  (`t·2̄ = t+t`) · ⭐⭐ `ltI_mul_two` — que **evita la transitividad**: de `y + σj = k̄` se
  calcula `k̄·2̄ = y·2̄ + σ(σj + j)`, que es ya la forma que `ax13` pide.
  🏁 **`√`: LAS TRES PIEZAS PUESTAS** el 2026-09-22 (`Order.lean` §8–§9), todas en
  `[propext, Quot.sound]`: `notI_lt_succ_of_lt` · ⭐ `ltI_succ_le` (**discreción**: entre `a`
  y `σa` no hay nada) · ⭐ `ltI_mul_self` (**monotonía del cuadrado**).
  ⛔ Y **la puerta NO era la que anuncié**: dije que hacía falta la forma ∀ de
  `zeroI_or_succ` para instanciarla en el testigo de un `elim_ex`; no hace falta ninguna
  forma ∀ — la discreción sale de la tricotomía sobre `σa` vs `b`, **anclados los dos**.
  ⭐ Lo que sí destrabó todo fue quitar un `Grounded` que sobraba en `addI_assoc` y
  `mulI_distrib`: el doble levantamiento de `forall_3` lo deshace `FOL.substTerm_liftLift`,
  que estaba en el mismo fichero que el lema que sí usábamos.
  🏁🏁 **`numeralI_sqrt` HECHO** el 2026-09-22 (`Order.lean` §10–§11), en
  `[propext, Quot.sound]`: **`√` está DETERMINADO**, y con eso caen las CINCO casillas ⛔ de
  ADR-037 que se podían cerrar —`−` medida negativa, `/₂`, `::` y `√` demostrados—.
  Los tres auxiliares de `≤` (`notI_lt_of_le`, `leI_mul_self`, `leI_trans`) salen de
  `ltI_trans` + `ltI_mul_self` + `ltI_irrefl`, y dan uso portante a lo que estaba 🏗️.
  ⚠️ **El núcleo de Lean no trae `Nat.sqrt`** (vive en Mathlib), así que el enunciado toma
  `k` con sus dos cotas. Más general, y separa la aritmética del meta de la derivación.
  🏁🏁 **METIDO EN EL FRAGMENTO el 2026-09-22** (ADR-045): **26 de los 34, sin hipótesis**.
  Las tres piezas que costaba: `isqrt` propia con sus dos cotas (Lean no trae `Nat.sqrt`),
  `slash_ax14` **generalizado** de `ctx`/`LQpp` a `{Γ}`/`L` —la tercera vez—, y el modelo
  interpretando `√` con `isqrt`, donde los dos axiomas resultan ser **exactamente las dos
  cotas**.
  ⇒ **Las CINCO casillas ⛔ de ADR-037 que se podían cerrar están cerradas.**
  📋 Estado completo en **`doc/TABLERO-FRAGMENTO.md`**.

  (anterior) ⏳ Queda `√`, y ya con dos de sus tres piezas puestas: ⭐ `notI_add_succ_self` —ningún
  término anclado cumple `x + σy = x`, que para NUMERALES costó inducción meta
  (`addI_succ_ne`) y para términos anclados sale **gratis**: es `x < x` por `ax13`, y `ax18`
  lo prohíbe— y `ltI_trans`. Falta `a<b → a·a<b·b` y tratar el `≤` de `ax14`, que es una
  disyunción.
- ⛔ **El alcance de `sub_neither` es `subAxioms` (23), no `coreAxioms` (34).** Subirlo pide
  un modelo de `coreAxioms` entero: listas, pares de Cantor, `√`, `Π_p`.
- ✅ ~~`[C]` mira la FILA, no la SECCIÓN~~ **endurecido el 2026-09-22** (ADR-041): pide fila
  en §1.1, sección con encabezado, línea `**Fichero**` resuelta contra el disco y navegación
  en los dos sentidos. De paso cerró un segundo agujero que nadie había visto: el `grep` era
  por SUBCADENA y `Calculus/Subst.lean` aprobaba por la mención de `SubstDerives`.
  ⚠️ **Lo que sigue sin mirar**: que el CONTENIDO de la sección esté al día. Eso es la pasada
  de lectura, no un grep.
- ✅ ~~`REFERENCE.md` pasa de las mil líneas~~ **arbolizado el 2026-09-22** (ADR-040): índice
  raíz de 286 líneas + `doc/REFERENCE-{Meta,Calculus,HA}.md`. 🔑 Y el criterio para el corte
  siguiente: **no es el número de líneas sino el de módulos que hay que atravesar**; si `HA/`
  pasa de la docena, se corta por capas **antes** de añadir la fila trece.
- `Calculus/Subst.lean` y `fdepth`: infraestructura de sintaxis duplicada (ADR-010),
  ofrecida en `doc/ENCARGO-FOL-2026-09-17.md`. ⏳ **Sin contestar al 2026-09-22**: FOL no
  menciona PeanoRF en ningún documento, y de lo pedido sólo existe `formulaComplexity`
  (en `Canonical0.lean`, que M-5 **prohíbe importar**).
- ✅ ~~La CI no deja constancia de contra qué compiló~~ **CERRADO el 2026-09-22** (ADR-043):
  el workflow certifica el **cuarteto** (`PeanoRF`, `FOL`, `RPP`, `Peano`) con SHA y asunto,
  con `if: always()`. Y de paso el toolchain va con **reintento y reloj**, porque ese mismo
  día una caída de red dio 20 minutos de runner y un rojo que no era del proyecto.
  ⚠️ **Certificar no es fijar**, y es deliberado: seguimos en `master` flotante para
  enterarnos pronto de que aguas arriba nos rompe.
- ⚠️ **Divergencia de polimorfismo con FOL, VIVA**: siete ficheros de FOL son ya genéricos
  en `Sym` —los ficheros `FOL/{FOL,DecEq,Derives0,Eigenvariable,Rename,Semantics,
  SymClasses}.lean` de aguas arriba, no símbolos nuestros— y PeanoRF importa **cinco**. Hoy no cuesta nada porque cada paso lleva su
  `abbrev` (`Term`, `Formula`, `Model`); el riesgo es el paso que no lo lleve.
- ✅ ~~`SYMBOL_PREFIXES` vacío ⇒ control [B] apagado~~ activado el 2026-09-21, con 15+ familias.
- ✅ ~~`metaDebtIsError := true`~~ hecho el 2026-09-18 (ADR-024). Deuda heredada: **0**.

⚠️ Y la comprobación de siempre antes de escribir nada: **re-medir**.

---

## H2 · El conjunto de axiomas de HA  ✅ CERRADO (2026-09-16)

- [x] `HA.ctx`, `ax'`, `ind`, `mono`, `induction_object`.
- [x] 🔑 **`gen_closed`**: sobre contexto cerrado la generalización es finitaria.
- [x] **`zero_add`** (sin parámetro) y **`succ_add`** (con parámetro).
- [x] ⚠️ **Migrado entero a `⊢ᵢ`** (ADR-017): `FOL.Derives` resultó no poder tener solidez.
- [x] **`HA.Closed`** — la hipótesis exacta del caso con parámetro.

**Lo aprendido, y es lo que hay que recordar**: el parámetro **sí** cuesta, y el precio está
localizado. `liftTerm 0 a = a` no basta porque `inductionFormula` usa `liftFormula 1 φ`.
Con parámetro **abierto** haría falta la **clausura universal** de la instancia en el
contexto — eso es exactamente lo que compraba la ω-regla.

---

## H3 · La interpretación  ✅ CERRADO (2026-09-16)

🏁 **`derivesI_soundness` mide `[propext, Quot.sound]`**: la solidez de la lógica
intuicionista, demostrada intuicionistamente. Y `derivesI_consistent` con ella.

⚠️ **Esta sección decía otra cosa hasta el 2026-09-18**, y la decía desde el plan original
del 6 de septiembre: «❌ Pendiente», con las casillas sin marcar y un plan que incluía
«soundness por inducción **sobre los constructores de `Derives`**» — que **ADR-017 declaró
imposible**: `FOL.Derives` no puede tener solidez. Doce días de deriva que ningún control
veía, y la cazó `check-coherencia.bash` [G] en su primera ejecución.

Cómo salió de verdad:

- [x] La interpretación es la de `FOL.Metamath.Semantics`, no una propia: M-5 se enmendó
      **con una medición** (ADR-019) — `satisfies` no tiene footprint; lo clásico estaba en
      la *prueba* de `Soundness0`.
- [x] **Inducción directa sobre los 18 constructores de `⊢ᵢ`**, no sobre `Derives`.
- [x] El último `Classical` era **un `omega`** en `shift_updateEnv_comm`, corregido aguas
      arriba (`6d47e5b`).
- [x] ➕ **H3′** (2026-09-17): `consistI_syn`, la consistencia **sin semántica**, por los
      secuentes sin corte de FOL (ADR-020).

**Y el peligro de M-9 sigue vigente**: la solidez se enuncia sobre `⊢ᵢ`, que **no tiene**
`raa` ni `imp_intro`. Con ellas, un testigo de no-derivabilidad daría una contradicción
(ADR-016 §«El peligro concreto»). Es la razón de que el eje finitario del gate exista.

---

## H4 · Reflexión: generar el espejo  ❌ Pendiente

- [ ] `⌜·⌝` de un fragmento de Lean sobre `ℕ₀` a `Formula`.
- [ ] Adecuación `⟦⌜P⌝⟧ ↔ P`.
- [ ] Táctica que genere el enunciado objeto desde un teorema de Peano.

**Por qué antes de volcar nada**: transcribir a mano lo que luego se generará es trabajo
tirado, y un espejo escrito a mano se desincroniza igual que un documento.

---

## H5+ · Volcado, realizabilidad, metateoría

Ver [PLANNING.md](PLANNING.md) §6.

---

## Deuda medida y contabilizada (no bloqueante)

| Qué | Dónde | Qué la cierra |
|---|---|---|
| 99/521 decls de ROB++ (19 %) pasan por ω-reglas | aguas arriba | Reprobar finitariamente lo que compense; el resto, a `PeanoRF.Omega.*` |
| RPP no es constructivo a nivel **meta**: `Minimal.Axioms.axioms` arrastra `Classical.choice` vía primitivas `String` | aguas arriba | El autor lo sanea → `metaDebtIsError := true` y re-medir |
| ⚠️ El control de constructores va **por NOMBRE**: un constructor nuevo aguas arriba no se vigila | `forbiddenConstructors` | Medir por TIPO, como `check-estratos.bash` de RPP |
| `add_comm`, `mul_*` sin volcar — ya **sin incógnitas de método** | `HA/Arith.lean` | Trabajo mecánico |
| `SYMBOL_PREFIXES` vacío ⇒ control **[B]** de `check-doc-sync.bash` desactivado | `check-doc-sync.bash` | Que existan familias de símbolos propias |
| Sin remoto en GitHub | — | `gh repo create` |

---

## Resumen de hitos

| Hito | Descripción | Estado |
|---|---|---|
| H0 | Andamiaje | ✅ |
| H1 | Directiva fundacional + gate de 3 ejes | ✅ |
| H2 | Conjunto de axiomas de HA, sobre `⊢ᵢ` | ✅ |
| H3 | Interpretación + soundness finitaria | ❌ |
| H4 | Reflexión y adecuación | ❌ |
| H5 | Volcado del núcleo aritmético | ❌ |
| H6 | Realizabilidad explícita | ❌ |
| H7 | Metateoría / checker verificado | ❌ |

