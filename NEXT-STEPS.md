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

1. **Parámetro de dominio `Slash T D`** — elegido: conserva H3bis en toda su fuerza. `D`
   serán los términos cerrados del lenguaje (`ClosedQTerm`, ya definido).
2. **Restringir las derivaciones al lenguaje** — pieza nueva que el contraejemplo obliga a
   añadir. `D` dice sobre qué cuantifica la barra; esto dice qué usa la derivación por
   dentro, y son cosas distintas. Dos rutas:
   * un `DerivesL` paralelo con su puente — trabajo nuestro, sin bloqueo;
   * ⭐ **eliminación de símbolos ajenos** (`Γ ⊢ φ` con todo en `L` ⇒ hay derivación sin
     términos fuera de `L`) — **preguntado a FOL**, que cerró Maehara + Craig el 17
     (`LKp`, su ADR-063). Si se lo da su maquinaria, nos ahorra un cálculo entero.

⚠️ **Primero mirar si han contestado** (`doc/HALLAZGO-SINTAXIS-GENERICA-2026-09-18.md`).
Si no, la ruta del `DerivesL` no depende de nadie.

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

## H3 · La interpretación en ℕ₀  ❌ Pendiente

**Objetivo**: `⟦·⟧ : Formula → Env ℕ₀ → Prop` y `soundness` **del fragmento finitario**
(M-9). Aquí el espejo deja de ser metáfora y pasa a ser teorema de transferencia.

- [ ] `⟦·⟧` para `Term` y `Formula`, constructiva, sin tocar `FOL.Semantics` (M-5).
- [ ] Interpretación de los axiomas de Q⁺⁺ como verdades sobre `ℕ₀`.
- [ ] `soundness` por inducción **sobre los constructores de `Derives`**.
- [ ] ⚠️ **Enunciarla de modo que NO cubra `raa`/`imp_intro`** (M-9): con ellas, un testigo
      de no-derivabilidad daría una contradicción. Ver ADR-016 §«El peligro concreto».

**Dependencias**: H2. **Complejidad**: media-alta.

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
