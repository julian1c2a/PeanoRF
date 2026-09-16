# Handoff → FOL · Un `Classical.choice` evitable en `Semantics.lean`

**Fecha:** 2026-09-16
**Origen:** PeanoRF (`github.com/julian1c2a/PeanoRF`), hito H3
**Para:** quien trabaje en `FOL`
**Estado:** ✅ **ACEPTADO, verificado de forma independiente y commiteado en FOL**
(`6d47e5b`). El agente de FOL lo **blindó** además metiendo cuatro de las declaraciones en
su `check-footprints.bash` (69 → 73 titulares): si alguien reintroduce el `omega`, el
control rompe. *Una mejora sin control es una mejora prestada.*

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
| **`FOL.Theorems.Eq`** | **3** | ⛔ **causa NO localizada** — no es el patrón del `omega` (ver abajo) |
| `FOL.Rename` | 3 | probablemente legítimo (`invOf` por elección) |
| `FOL.Tactics` | 1 | ⬜ **sin medir** |

**Los sospechosos, con nombre — ⚠️ REVISADO 2026-09-16 tras la medición de FOL:**

| símbolo | veredicto |
|---|---|
| `FOL.substTerm_subst_comm_succ` · `substTerms_subst_comm_succ` · `subst_subst_comm_succ` | ⛔ **NO es el mismo patrón** — conjetura **refutada** |
| `FOL.Rename.invOf` / `invOf_spec` | probablemente legítimo (inverso por elección); `derives0_rename_conservative` hereda |
| `FOL.Tactics.tryMem` | ⬜ **sin medir** |

⛔ **Corrección.** Este informe afirmaba que los tres `subst_*_comm_succ` eran «muy probable
que sea el mismo patrón». **Es falso, y está medido**: sus `omega` están todos dentro de
`show ¬ k = j from by omega`, es decir **sobre metas aritméticas** — el lado **limpio** de
la regla del §3. El agente de FOL midió además, en el entorno de imports de ese fichero:

| pieza | footprint |
|---|---|
| `Nat.lt_trichotomy` · `rcases` · `congr 1` | ningún axioma |
| `by omega` sobre `¬ k = j` | `propext, Quot.sound` |
| `simp [substTerm, show ¬ k = j from by omega]` | `propext, Quot.sound` |

⬜ **La causa no está localizada.** Hace falta **bisección por ramas** (§6 paso 4). Y aplica
el aviso de método de este mismo informe: *refutar con la cadena sucia es refutar ruido*,
así que se declara **conjetura refutada**, no diagnóstico alternativo.

🔑 **Lección para quien escriba el próximo informe de traspaso**: marcar como «muy probable»
algo medido sólo por analogía es exactamente el error que este informe advierte en su §6.
Un candidato sin medir se etiqueta ⬜ **sin medir**, no «probable».

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

---

## 7. ⚠️ Nota de proceso — asumida

El arreglo llegó **aplicado y sin commitear en el árbol compartido**. El agente de FOL hizo
varios `git add -A` ese día: pudo colarse en un commit suyo con un mensaje que no lo
menciona, y estuvo cerca.

**Un cambio ajeno sin commitear en un árbol compartido es indistinguible de uno propio.**

**Regla adoptada para la próxima vez**: parche (`git format-patch` / diff adjunto), rama
propia, o avisar **antes** de tocar el árbol. Nunca dejarlo suelto.
