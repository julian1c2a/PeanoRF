# Next Steps — PeanoRF

**Última actualización:** 2026-09-06 21:00
**Autor**: Julián Calderón Almendros

> Fases de desarrollo a corto y medio plazo. Para el rumbo largo, ver
> [PLANNING.md](PLANNING.md).

---

## 🎯 SIGUIENTE SESIÓN

**Terminar H2: el volcado con PARÁMETRO.** La infraestructura está y `zero_add` ya está
reprobado sin ω; lo que falta por medir es el caso con parámetro libre (`succ_add`,
`add_comm`), donde el manejo de índices De Bruijn es de verdad el que muerde.

---

## H2 · El conjunto de axiomas de HA  🔄 Infraestructura ✅, volcado en curso

**Objetivo**: axiomatizar HA sobre Q⁺⁺ **sin** postular derivabilidad (M-8).

- [x] **Contextos finitos**: `HA.ctx insts = axioms ++ insts.map inductionFormula`. Cada
      teorema declara en su tipo qué instancias usa. Se reutiliza `Full.inductionFormula`
      (M-4), que ya trae la codificación *lift-aware* correcta.
- [x] `ax'`, `ind`, `mono`, `induction_object` — la instancia de inducción entra por
      `Derives.hyp`, **no por un `axiom` de Lean**.
- [x] 🔑 **`gen_closed`**: sobre un contexto cerrado la generalización es finitaria.
      `axioms_lift : axioms.map (liftFormula 0) = axioms` sale por **`rfl`** — los axiomas
      de Q⁺⁺ son sentencias cerradas y el kernel lo computa. Footprint: `[propext]`.
- [x] **`zero_add` reprobado finitariamente**. Medición:

      | símbolo | footprint |
      |---|---|
      | `HA.zero_add` | `propext, Classical.choice, Quot.sound` |
      | `Full.zero_add` | + `MetaRules.gen`, `MetaRules.imp_intro`, `ax_induction` |

      **Tres axiomas menos, misma estructura de prueba.**

- [ ] **`succ_add` / `add_comm` — el caso CON PARÁMETRO.** `zero_add` no tiene parámetro
      libre; ahí la ω no aportaba nada. El caso con parámetro es donde la codificación
      *lift-aware* existe, y donde hay que ver si `gen_closed` basta o hace falta una
      versión con contexto parametrizado.
- [ ] Decidir si `insts` debe ser un **predicado decidible** (`isInductionInstance`) además
      de una lista. Hoy la lista basta y es más informativa; el predicado hará falta cuando
      se aritmetice la propia teoría (H7).

**Lo aprendido**: la ruta finitaria no exigió reformular ninguna matemática. Lo único que
cambia es que la hipótesis de inducción entra por el contexto en vez de por una función
meta, y que el paso se prueba con `#0` libre en vez de con un término arbitrario.

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
| `SYMBOL_PREFIXES` vacío ⇒ control **[B]** de `check-doc-sync.bash` desactivado | `check-doc-sync.bash` | Que existan familias de símbolos propias |
| Sin remoto en GitHub | — | `gh repo create` |

---

## Resumen de hitos

| Hito | Descripción | Estado |
|---|---|---|
| H0 | Andamiaje | ✅ |
| H1 | Directiva fundacional + gate de 3 ejes | ✅ |
| H2 | Conjunto de axiomas de HA | 🔄 infraestructura ✅ |
| H3 | Interpretación + soundness finitaria | ❌ |
| H4 | Reflexión y adecuación | ❌ |
| H5 | Volcado del núcleo aritmético | ❌ |
| H6 | Realizabilidad explícita | ❌ |
| H7 | Metateoría / checker verificado | ❌ |
