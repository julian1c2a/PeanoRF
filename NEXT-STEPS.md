# Next Steps — PeanoRF

**Última actualización:** 2026-09-17
**Autor**: Julián Calderón Almendros

> Fases de desarrollo a corto y medio plazo. Para el rumbo largo, ver
> [PLANNING.md](PLANNING.md).

---

## 🎯 SIGUIENTE SESIÓN

**H4 — reflexión `⌈·⌉` + adecuación + táctica.** Ahora sí toca: el espejo ya tiene un
teorema que justifica su existencia (`derivesI_ne_derives0`, H3bis), así que automatizar el
volcado deja de ser optimizar el transporte antes de saber qué se transporta.

La alternativa sigue siendo el volcado a mano de `add_comm`/`mul_*` (H5), que **no tiene
incógnitas de método**; PLANNING pone H4 antes por la razón de siempre — volcar a mano lo
que luego se generará es trabajo tirado.

### Lo que quedó cerrado el 2026-09-17

| | |
|---|---|
| H3′ | consistencia SIN semántica (`consistI_syn`) |
| **H3bis** | **propiedad de disyunción, de existencia, y `derivesI_ne_derives0`** |
| infraestructura | álgebra σ, `derivesI_subst`, `leibniz_at`, la barra entera |

### ⚠️ Deudas vivas

- **`Calculus/Subst.lean` es infraestructura de SINTAXIS duplicada** (ADR-010). Sigue
  pedida en `doc/ENCARGO-FOL-2026-09-17.md`. ✅ Del encargo **se resta** la regla de Leibniz
  indexada: resultó derivable (ADR-023).
- `formulaComplexity` detrás de la cadena clásica ⇒ `fdepth` duplicado. Mismo encargo.
- `metaDebtIsError := true` cuando RPP sanee su nivel meta (hoy 10 decls).
- `SYMBOL_PREFIXES` vacío ⇒ control [B] de docsync apagado.

⚠️ Y la comprobación de siempre antes de escribir nada: **re-medir**. FOL se mueve rápido.

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
