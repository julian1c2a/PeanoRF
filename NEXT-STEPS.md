# Next Steps — PeanoRF

**Última actualización:** 2026-09-17
**Autor**: Julián Calderón Almendros

> Fases de desarrollo a corto y medio plazo. Para el rumbo largo, ver
> [PLANNING.md](PLANNING.md).

---

## 🎯 SIGUIENTE SESIÓN

**H3bis — cerrar L2. Queda UN caso, y está identificado.**

Hecho y medido (todo en `[propext]` / `[propext, Quot.sound]`):

| pieza | dónde |
|---|---|
| álgebra de sustitución paralela (`substF`, `upS`, `consS`, `compS`, comp/id/lift) | `Calculus/Subst.lean` |
| **`derivesI_subst`** — `⊢ᵢ` cerrado bajo sustitución, 18 casos | `Calculus/SubstDerives.lean` |
| **`slash_rewrite`** — la barra sobrevive a `rewrite_at` | `Calculus/Slash.lean` |
| L1, `cut_context`, `derives_empty_of_slashed` | `Calculus/Slash.lean` |

**Lo que falta**: el caso `Derivesᵢ.subst` de L2 — la regla de Leibniz. Hace falta que la
barra sea invariante bajo sustituciones **probablemente iguales**; los casos atómicos,
`∧`, `∨` y `→` salen, y **el que se atasca es el cuantificador**: `subst` sustituye sólo en
el **índice 0** y bajo un `∀` el índice pasa al 1.

⇒ Hace falta la regla de Leibniz **en un índice cualquiera**:
`[] ⊢ᵢ x = y → [] ⊢ᵢ f[x/k] → [] ⊢ᵢ f[y/k]`.

Dos salidas, y la elección es de diseño:

1. **Derivarla aquí** con el álgebra σ que ya existe (permutar los índices 0 y k). No toca
   ni el cálculo ni FOL.
2. **Pedirla aguas arriba**: `Derives₀` tiene el mismo `subst` fijado en 0, así que es
   problema suyo también. Encaja con el encargo ya abierto.

Después de L2: la propiedad de disyunción es inmediata, y con `notP_syn` sale la separación
`⊢ᵢ ≠ ⊢₀` — el primer teorema del proyecto que **falla clásicamente**.

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
