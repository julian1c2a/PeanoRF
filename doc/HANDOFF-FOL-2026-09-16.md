# Handoff → FOL · Un `Classical.choice` evitable en `Semantics.lean`

**Fecha:** 2026-09-16
**Origen:** PeanoRF (`github.com/julian1c2a/PeanoRF`), hito H3
**Para:** quien trabaje en `FOL`
**Estado:** el arreglo está **aplicado y sin commitear** en `FOL/FOL/Semantics.lean`

---

## 1. Qué hay que arreglar (una línea)

`FOL/FOL/Semantics.lean`, dentro de `shift_updateEnv_comm` (≈ línea 153):

```lean
        cases n with
-       | zero => omega
+       | zero => exact absurd (Nat.le_zero.mp (Nat.not_lt.mp h1)).symm h2
        | succ m => rfl
```

Es el cierre de un caso **imposible** (`¬(0 < c)` y `¬(0 = c)` se contradicen). Nada más
cambia: mismo enunciado, mismo resto de la prueba.

⚠️ `FOL/Semantics.lean` **no** está en `locked_files.txt` ni en `frozen_files.txt`, así que
el cambio no viola el protocolo de bloqueo.

---

## 2. Por qué importa

Ese `omega` era **el único `Classical.choice` de toda la semántica de fórmulas**. De él
heredaban `eval_liftFormula_ext`, `eval_substFormula_ext`, `contextSatisfies_lift_zero`,
`eval_liftFormula_zero`, `eval_substFormula_zero` y todo lo que dependa de ellos.

**Medido, antes y después:**

| símbolo | antes | después |
|---|---|---|
| `shift_updateEnv_comm` | `propext, Classical.choice, Quot.sound` | **`propext, Quot.sound`** |
| `eval_liftFormula_ext` | + `Classical.choice` | **limpio** |
| `eval_substFormula_ext` | + `Classical.choice` | **limpio** |
| `contextSatisfies_lift_zero` | + `Classical.choice` | **limpio** |
| `FOL.Semantics` (módulo entero) | 7 decls sucias | **0** |

Aguas abajo, en PeanoRF, eso convirtió `derivesI_soundness` —la solidez del fragmento
intuicionista— en **`[propext, Quot.sound]`**. Y deja el `Classical.choice` de
`derives0_soundness` como **exactamente el precio de sus tres reglas clásicas**
(`dne_rule`, `dne_schema`, `forall_not_ex_not`), que es lo que su propio docstring
afirmaba y ahora está medido.

---

## 3. 🔑 El patrón general, que es lo reutilizable

> **`omega` sobre metas ARITMÉTICAS es limpio. Sobre metas FUERA DE SU LENGUAJE,
> descargadas por contradicción, mete `Classical.choice`.**

Medido con tres casos mínimos:

| prueba | footprint |
|---|---|
| `(h : c < 0) : (1:Nat) = 2 := by omega` | `propext, Quot.sound` |
| `(h : c < 0) : v 0 = d' := by omega` ← meta de tipo `D` | **+ `Classical.choice`** |
| `(h : c < 0) : v 0 = d' := absurd h (Nat.not_lt_zero c)` | **ningún axioma** |

Es una instancia **nueva** del «Classical oculto» (AI-GUIDE §27), distinta de las ya
documentadas en la familia (las medidas de terminación ponderadas de AczelSetTheory).

**Regla práctica**: cuando `omega` cierre un caso imposible cuya meta **no** es aritmética,
sustituirlo por `absurd`/`False.elim` explícito. El caso típico es exactamente éste: un
`cases` que genera una rama imposible y se despacha con `omega` por comodidad.

---

## 4. Cómo verificarlo de forma independiente

No hace falta creerse nada de lo anterior:

```bash
# desde un proyecto que requiera FOL (p. ej. PeanoRF o ROBINSON_PlusPlus):
lake env lean - <<'EOF'
import FOL.Semantics
#print axioms FOL.Metamath.Semantics.shift_updateEnv_comm
#print axioms FOL.Metamath.Semantics.eval_substFormula_ext
EOF
```

⚠️ **Compilar siempre desde el proyecto que requiere FOL**, nunca con `cd FOL && lake build`.

---

## 5. Lo que queda sucio en FOL, y cuánto de ello es legítimo

Con el arreglo puesto, **90 declaraciones** de FOL siguen con `Classical.choice`:

| módulo | decls | ¿legítimo? |
|---|---:|---|
| `FOL.Canonical0` | 27 | ✅ sí — completitud es clásica |
| `FOL.HenkinLimit0` | 17 | ✅ sí |
| `FOL.Fresh0` | 15 | ✅ probablemente |
| `FOL.Lindenbaum0` | 12 | ✅ sí |
| `FOL.Enumeration` | 6 | ✅ probablemente |
| `FOL.Soundness0` | 5 | ✅ **sí, y ahora es exacto**: las tres reglas clásicas |
| `FOL.Henkin0` | 1 | ✅ sí |
| **`FOL.Theorems.Eq`** | **3** | ⚠️ **SOSPECHOSO** |
| **`FOL.Rename`** | **3** | ⚠️ parcialmente |
| **`FOL.Tactics`** | **1** | ⚠️ **SOSPECHOSO** |

**Los sospechosos, con nombre:**

* `FOL.substTerm_subst_comm_succ`, `FOL.substTerms_subst_comm_succ`,
  `FOL.subst_subst_comm_succ` — son lemas de **conmutación de sustituciones De Bruijn**,
  puramente combinatorios: no hay razón para que necesiten lógica clásica. Muy probable
  que sea el mismo patrón del `omega`.
* `FOL.Tactics.tryMem` — una táctica de pertenencia; mismo comentario.
* `FOL.Rename.invOf` / `invOf_spec` — aquí sí puede ser legítimo (un inverso construido por
  elección); `derives0_rename_conservative` heredaría de ellos.

⚠️ **No los he medido en detalle**: son candidatos para revisar con el mismo método
(bisección por ramas + `#print axioms`), no diagnósticos cerrados.

**Lo que ganaría FOL si los tres de `Theorems.Eq` son el mismo patrón**: la mitad
demostrativa de FOL⁼ quedaría **constructiva de punta a punta**, y el `Classical` quedaría
confinado exactamente donde debe estar — en la mitad modelo-teórica.

---

## 6. Cómo se encontró (por si el método sirve)

1. `#print axioms` sobre la cadena completa → el nivel término estaba limpio, el de fórmulas
   no ⇒ la raíz estaba en el primer lema de fórmulas.
2. `set_option pp.explicit true` + `trace_state` tras el `dsimp` → **todas** las instancias
   `Decidable` de la meta eran las reales (`Nat.decLt`, `instDecidableEqNat`). Ni rastro de
   `Classical.propDecidable` ⇒ no era un problema de síntesis de instancias.
3. Se descartaron uno a uno, **midiendo cada uno en aislamiento**: `by_cases`, `rcases`,
   `obtain`, `cases`, `simp` (conjunto por defecto), `rw [if_pos/if_neg]`, `funext`,
   `dsimp`, `Nat.lt_or_ge`, `Nat.not_lt`, `Nat.eq_or_lt_of_le`. **Todos limpios.**
4. **Bisección por RAMAS** del lema: de las tres, sólo `c < n` estaba sucia.
5. Dentro de esa rama, lo único propio era el `omega` del caso imposible.

⚠️ **Aviso de método**: en el paso 3 se concluyó erróneamente que la conjetura de partida
era falsa, porque la cadena seguía sucia. *Una medición de footprint sólo refuta una
conjetura sobre lógica si el resto de la cadena está limpio.* Refutar con la cadena sucia es
refutar ruido.
