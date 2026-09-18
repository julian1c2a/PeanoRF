# Next Steps — PeanoRF

**Última actualización:** 2026-09-17
**Autor**: Julián Calderón Almendros

> Fases de desarrollo a corto y medio plazo. Para el rumbo largo, ver
> [PLANNING.md](PLANNING.md).

---

## 🎯 SIGUIENTE SESIÓN

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
De ahí salen `qDisjunctionProperty` y `qExistenceProperty_numeral` — la DP y la EP para
**cualquier teoría de Q⁺⁺ cuyos axiomas estén barrados**, con el testigo demostrablemente
igual a un numeral.

⭐ Y **H3bis no se debilitó**: con `L` total el colapso es la identidad (`collapseF_trivial`)
y con `D` total la clausura es trivial, así que `disjunction_property` y `existence_property`
salen con el enunciado literal de antes y el mismo `[propext, Quot.sound]`.

⚠️ El caso `rewrite_at` fue el que pidió la pieza extra: para aplicar `slash_rewrite`, que
está enunciada sobre `substF`, hay que mover el colapso al otro lado ⇒ **`collapseF_substF`**,
la conmutación con la sustitución PARALELA, que el sondeo (g) ya había medido.

### Etapa 3 — ya medida

De los **34 axiomas de `coreAxioms`**: **25** con matriz atómica (barra = derivabilidad
⇒ `specI`), ~4 `⇒`/`⇔` con partes atómicas, y **5** que piden decidir en el meta y construir
la derivación: `ax19_lt_trichotomy`, `ax21_mod2_range`, `ax13_lt_def`, `ax_L3_in_concat`,
`ax29_sub_witness`. `numeral_lt` existe aguas arriba y es ω-limpio; `numeral_ne` —el
contaminado— sigue fuera del camino. **Más el esquema de inducción.**

### ⚠️ Deudas vivas

- **Formalizar la no-derivabilidad de las ramas** del contraejemplo. Hoy es argumento por
  solidez; en esta familia un argumento no es una medición.
- `Calculus/Subst.lean` y `fdepth`: infraestructura de sintaxis duplicada (ADR-010),
  ofrecida en `doc/ENCARGO-FOL-2026-09-17.md`.
- `SYMBOL_PREFIXES` vacío ⇒ control [B] de docsync apagado.
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

