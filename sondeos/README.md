# `sondeos/` — mediciones fuera del build

**Última actualización:** 2026-09-06 21:00

Ficheros de medición y experimento. **No forman parte de la librería** (`lakefile.lean`
no los incluye) y por tanto no rompen el build ni entran en el recuento de módulos.
Se ejecutan a mano:

```bash
lake env lean sondeos/axiom_probe.lean
```

## Ficheros

| Sondeo | Qué mide |
|---|---|
| `axiom_probe.lean` | Footprint de axiomas de FOL / RPP / Peano |
| `omega_probe.lean` | **Carga de las meta-reglas ω** en ROB++ (Minimal+Full) e inventario de sus `axiom` |
| `peano_probe.lean` | Footprint constructivo de **todo** Peano (2207 decls) |
| `lift_probe.lean` | **H2**: ¿es el contexto de axiomas invariante bajo `liftFormula 0`? |
| `h2_probe.lean` | **H2**: footprint de `zero_add` finitario vs. el de ROB++ |

⚠️ `peano_probe.lean` tuvo que anotar `Nat` a mano (`Nat.add`, `Nat.sub`): con `Peano`
importado, el `+` global resuelve a `ℕ₀` y el término queda ambiguo. Es la trampa que ya
documentaba AczelSetTheory.

## `axiom_probe.lean`

Inventario del footprint de axiomas de las tres librerías aguas arriba. Existe porque
**los `import` no demuestran nada**: la única medida del footprint es `#print axioms` /
`Lean.collectAxioms`.

Comandos que define:

| Comando | Qué hace |
|---|---|
| `#probe <Raíz>` | Cuenta declaraciones limpias vs. sucias bajo un prefijo de módulo, con el desglose de axiomas ofensores |
| `#dirty <Raíz>` | Lista TODAS las declaraciones sucias, agrupadas por módulo |
| `#axioms_of <Raíz>` | Inventario de los `axiom` declarados bajo un prefijo |
| `#dependents <ax> under <Raíz>` | Qué declaraciones dependen de un axioma concreto |
| `#fp <símbolo>` | Footprint exacto de un símbolo |

## Medición del 2026-09-06 (la que fundamenta ADR-013)

| Librería | Decls | Limpias | Con footprint extra |
|---|---:|---:|---|
| `Peano` (`PeanoNat.Axioms`) | 192 | **192** | 0 — y **0 `axiom`** declarados |
| `FOL` (barrel completo) | 397 | 332 | 65 · 52 con `Classical.choice` · 13 `axiom` |
| `ROBINSON_PlusPlus.Minimal.Axioms` | 313 | 269 | 44 con `Classical.choice` · 1 `axiom` |

**Los tres hallazgos que decidieron el diseño del gate:**

1. **Los 13 `axiom` de FOL se reparten en tres grupos, y solo uno es clásico.**
   - **Clásicos de nivel objeto (3)**: `MetaRules.dne`, `Theorems.Neg.dne`,
     `Theorems.Quantifiers.forall_not_impl_exists_not`.
   - **Meta-reglas admisibles (5)**: `imp_intro`, `gen` (ω-regla: infinitaria, no
     clásica), `raa` (es introducción de ¬, intuicionista pese al nombre), `or_elim`,
     `ex_elim`.
   - **Completitud (5)**: `formula_enum`, `formula_enum_surj`, `termEqv_func_congr`,
     `termEqv_rel_congr`, `henkin_extension_lemma`.
2. **Los tres clásicos están CONFINADOS a la mitad modelo-teórica.** `MetaRules.dne` no
   lo usa nadie; `Theorems.Neg.dne` solo `Completeness.completeness`;
   `forall_not_impl_exists_not` solo Completeness/Compacity. Como este proyecto **no
   importa** `FOL.Semantics/Soundness/Completeness/Compacity`, la pureza intuicionista
   de nivel objeto sale casi gratis: violarla exige un `import` deliberado.
3. **`ROBINSON_PlusPlus.Minimal.Axioms.axioms` — el conjunto de axiomas de Q⁺⁺ —
   arrastra `Classical.choice`**, vía las funciones de codificación `strCodeM`,
   `termCodeM`, `formCodeM` (primitivas `String` del núcleo de Lean 4.31). O sea:
   **cualquier** teorema sobre Q⁺⁺ lo hereda hoy. Es deuda de nivel META aguas arriba,
   que el autor va a saldar; el gate la tolera con aviso y recuento
   (`inheritedMetaDebt`), nunca en silencio.

Repetir la medición cuando ROBINSON_PlusPlus se sanee, y entonces poner
`metaDebtIsError := true` en `PeanoRF/Meta/AxiomCheck.lean`.

---

## Medición del 2026-09-06 (b) — la carga ω de ROB++ (`omega_probe.lean`)

Sobre **521 declaraciones** de `ROBINSON_PlusPlus` (Minimal + los 11 módulos de Full):

| Regla | Decls que la arrastran |
|---|---:|
| `FOL.MetaRules.gen` (ω-regla) | 70 |
| `FOL.MetaRules.ex_elim` | 64 |
| `FOL.MetaRules.or_elim` | 64 |
| `FOL.MetaRules.imp_intro` | 42 |
| `FOL.MetaRules.raa` | 13 |
| **alguna de las anteriores** | **99 (19 %)** |
| `dne` / `Theorems.Neg.dne` / `forall_not_impl_exists_not` | **0** |

**Dos conclusiones, una excelente y una que decide la arquitectura:**

1. ✅ **ROB++ es intuicionista a nivel objeto, y está VERIFICADO**: cero usos de lógica
   clásica en 521 declaraciones.
2. ⚠️ **ROB++ NO es finitario**: el 19 % pasa por meta-reglas ω. Y son ω de verdad, no
   por descuido — el propio docstring de `FOL/MetaRules.lean` lo dice: *«axiomatizan
   "demostrabilidad = verdad en el modelo estándar"; el sistema resultante es ω-lógica,
   estrictamente más fuerte que FOL⁼ finitaria»*.

**Los 5 `axiom` de Lean de ROB++**: `Minimal.Axioms.ax_axiomsCodeT_eq`,
`Minimal.Theorems.Block8.ax_p_tfa`, `Full.ax_induction` (**30 decls dependen de él**),
`Full.ax_list_induction`, `Full.ax_mod2_alternation`.

🔑 `Full/Induction.lean:166` declara `axiom ax_induction (φ) : axioms ⊢ inductionFormula φ`
— es decir, postula que el esquema de inducción **es derivable del conjunto de axiomas de
Q⁺⁺**. Con un `⊢` finitario eso sería falso (Q no prueba inducción); es coherente sólo bajo
la lectura ω-lógica, donde `⊢` = verdad en ℕ. **De aquí sale la decisión de diseño más
importante de PeanoRF** (ver ADR pendiente y `PLANNING.md`).

---

## Medición del 2026-09-06 (c) — Peano al completo (`peano_probe.lean`)

**2207 declaraciones · 2193 limpias (99,4 %) · 14 sucias.** Las 14 llevan
`Classical.choice` y están confinadas a tres módulos, los tres explícitos sobre lo que son:

| Módulo | Decls sucias |
|---|---:|
| `Peano.PeanoNat.Foundation.Initiality` | 7 |
| `Peano.Prelim.Classical` | 5 |
| `Peano.PeanoNat.Foundation.PureAxioms` | 2 |

**Conclusión: «volcar Peano al completo» es viable desde el punto de vista de la pureza
constructiva.** Peano ya es constructivo salvo por un 0,6 % localizado y nombrado.


---

## Medición del 2026-09-06 (d) — H2, el coste de prescindir de la ω

`lift_probe.lean` responde la pregunta que decidía la viabilidad: **sí**, los axiomas de
Q⁺⁺ son sentencias cerradas y `axioms.map (liftFormula 0) = axioms` se demuestra por
**`rfl`** (cómputo del kernel). Lo mismo para la instancia de inducción de una `φ` concreta
con sólo `#0` libre. Eso hace usable `Derives.intro_forall` — el constructor finitario — en
lugar de la ω-regla `gen`.

`h2_probe.lean` mide el resultado sobre `zero_add`:

| símbolo | footprint |
|---|---|
| `PeanoRF.HA.zero_add` (finitario) | `propext, Classical.choice, Quot.sound` |
| `ROBINSON_PlusPlus.Full.zero_add` (ω) | + **`MetaRules.gen`, `MetaRules.imp_intro`, `ax_induction`** |
| `PeanoRF.HA.gen_closed` | `propext` |

**Tres axiomas menos, misma estructura de prueba.** El `Classical.choice` restante es la
deuda META heredada de la codificación `String` de RPP, no del método.

⚠️ **Alcance de esta medición**: `zero_add` no tiene parámetro libre. El caso con parámetro
(`succ_add`, `add_comm`) está sin medir y es donde la codificación *lift-aware* existe.
No extrapolar el «coste cero» sin comprobarlo.
