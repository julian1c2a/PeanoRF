# Next Steps — PeanoRF

**Última actualización:** 2026-09-17
**Autor**: Julián Calderón Almendros

> Fases de desarrollo a corto y medio plazo. Para el rumbo largo, ver
> [PLANNING.md](PLANNING.md).

---

## 🎯 SIGUIENTE SESIÓN

**H3ter — cerrar la propiedad de disyunción para HA. Queda UN lema.**

L2 ya está enunciada para contexto arbitrario, así que la DP de HA se reduce a:

> **`ha_ctx_slashed`** : `∀ g ∈ ctx insts, Slash (substF ρ g)`

y `ctx insts = axioms ++ insts.map inductionFormula`, o sea **dos familias**:

1. **Los axiomas de Q⁺⁺** — finitos, de cabeza atómica o universal-atómica. Deberían salir
   de la propia derivabilidad, como los casos atómicos de `slash_eq_congr`.
2. **Las instancias de inducción** — el caso clásico difícil. Dado el antecedente barrado
   salen `Slash φ(0)` y el paso, y por inducción meta sobre `n` sale `Slash φ(σⁿ0)`. Pero la
   cláusula `∀` de la barra cuantifica sobre **todos** los términos cerrados ⇒
   ✅ **`closed_term_eq_numeral` (hecho el 2026-09-18)** + `slash_eq_congr` (H3bis) cierran
   ese paso.

### ✅ Hecho y medido el 2026-09-18

| pieza | dónde |
|---|---|
| congruencia genérica por símbolo de función | `Calculus/Eq.lean` |
| `numeralI_add` / `_mul` / `_pow` (inducción META, sin ω) | `HA/Numerals.lean` |
| ⭐ `closed_term_eq_numeral` | `HA/Numerals.lean` |

⚠️ **Medido antes de escribir**: reusar la capa de RPP era imposible — está sobre `⊢` y el
puente va en un solo sentido —, pero el port sale limpio de ω. Ver `sondeos/README.md`.

### ⚠️ Deudas vivas

- `Calculus/Subst.lean` y `fdepth`: infraestructura de sintaxis duplicada (ADR-010),
  ofrecida en `doc/ENCARGO-FOL-2026-09-17.md`.
- `metaDebtIsError := true` cuando RPP sanee su nivel meta (hoy **14** decls; subía de 10
  porque los numerales tocan `axioms`).
- `SYMBOL_PREFIXES` vacío ⇒ control [B] de docsync apagado.

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
