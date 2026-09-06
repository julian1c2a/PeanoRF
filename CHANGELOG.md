# Changelog

**Last updated:** 2026-09-06 21:00
**Author**: Julián Calderón Almendros

All notable changes to this project will be documented in this file.

Format based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

> Este fichero es un **diario**: sus cifras y símbolos son históricos por diseño y
> quedan deliberadamente fuera del control `check-doc-sync.bash` (AI-GUIDE §27).

---

## [Unreleased]

### Added (2026-09-06, H2) — el conjunto de axiomas de HA

- **`PeanoRF/HA/Axioms.lean`** — HA axiomatizada **sin postular derivabilidad** (M-8):
  `ctx insts = axioms ++ insts.map inductionFormula`. La instancia de inducción entra por
  `Derives.hyp`, no por un `axiom` de Lean. Con `ax'`, `ind`, `mono`, `induction_object`.
- 🔑 **`gen_closed`** — sobre un contexto **cerrado**, la generalización es finitaria
  (`Derives.intro_forall`): **la ω-regla `gen` no hace falta**. La hipótesis se cumple por
  cómputo del kernel — `axioms_lift : axioms.map (liftFormula 0) = axioms` es un `rfl`,
  porque los axiomas de Q⁺⁺ son sentencias cerradas. Footprint de `gen_closed`: `[propext]`.
- **`PeanoRF/HA/Arith.lean`** — `zero_add` (`∀x. 0 + x = x`) **reprobado sin ω-reglas y sin
  `ax_induction`**. El tipo declara la instancia de inducción usada: contabilidad de
  matemática inversa que sale gratis del diseño.
- Verificaciones puntuales `#assert_finitary` / `#assert_intuitionistic` sobre `zero_add`,
  `induction_object` y `gen_closed`, en el gate.
- `sondeos/lift_probe.lean` y `sondeos/h2_probe.lean`.

### Measured (2026-09-06, H2) — el coste de prescindir de la ω

| símbolo | footprint |
|---|---|
| `PeanoRF.HA.zero_add` (finitario) | `propext, Classical.choice, Quot.sound` |
| `ROBINSON_PlusPlus.Full.zero_add` (ω) | + **`MetaRules.gen`, `MetaRules.imp_intro`, `ax_induction`** |
| `PeanoRF.HA.gen_closed` | `propext` |

**Tres axiomas menos, misma estructura de prueba y sin reformular matemática.** El
`Classical.choice` que queda es la deuda META heredada de la codificación `String` de RPP.

⚠️ La medición es de un caso **sin parámetro libre**. El caso con parámetro (`succ_add`,
`add_comm`) sigue pendiente y es donde el manejo de índices De Bruijn puede morder.

---

### Added (2026-09-06, noche) — alcance fijado, ADR-016 y capa ω

- **Alcance del proyecto definido** (`PLANNING.md` reescrito): PeanoRF vuelca Peano al
  lenguaje FOL⁼ + ROB++ como **espejo** — PeanoRF fundacional, Peano computacional —, que
  visto de cerca es una **interpretación de realizabilidad**. Objetivo último: servir de
  meta-lenguaje para FOL y ROB++, con su techo explícito (Gödel II).
- **ADR-016 — el núcleo es HA FINITARIA; la ω-lógica vive en una capa aparte.**
  Nace de dos hechos medidos: `Full/Induction.lean:166` postula
  `axiom ax_induction : axioms ⊢ inductionFormula φ` (falso bajo un `⊢` finitario: Q no
  demuestra inducción), y **99 de 521 declaraciones de ROB++ (19 %) pasan por ω-reglas**.
  Sin la separación, PeanoRF no sería HA sino ω-lógica = aritmética verdadera, con `⊢` no
  r.e. — lo que mata el objetivo de meta-lenguaje y desdibuja el fundacional.
- **MANDATORIES M-7, M-8, M-9**: núcleo finitario · la inducción entra en el **conjunto de
  axiomas** · la soundness se demuestra **sólo del fragmento finitario**.
- **`PeanoRF/Omega/Basic.lean`** — capa ω declarada, aislada y **contada** en cada build.
  Cinco alias sancionados (`gen`, `imp_intro`, `raa`, `or_elim`, `ex_elim`).
- **Tercer eje en el gate** (finitario) + comando `#assert_finitary`. Probado en los dos
  sentidos: error fuera de la capa ω, recuento dentro (hoy 5).
- `sondeos/omega_probe.lean` y `sondeos/peano_probe.lean`.

### Measured (2026-09-06, noche)

| Medición | Resultado |
|---|---|
| ROB++ (Minimal+Full, 521 decls) | **99 (19 %)** con ω-reglas · **0 con lógica clásica** |
| desglose | `gen` 70 · `ex_elim` 64 · `or_elim` 64 · `imp_intro` 42 · `raa` 13 |
| `axiom` de Lean en ROB++ | 5, de los que 4 son meta-axiomas de esquema (`ax_induction` con **30** dependientes) |
| **Peano al completo** | **2207 decls · 2193 limpias (99,4 %)** · las 14 sucias en `Initiality` (7), `Prelim.Classical` (5), `PureAxioms` (2) |

La última fila es la que hace viable el volcado: **Peano ya es constructivo** salvo un
0,6 % localizado y nombrado.

### Note (2026-09-06, noche) — un peligro identificado, no un bug

`raa` e `imp_intro` toman premisas META (`Γ ⊢ A → Γ ⊢ B`), satisfacibles **vacíamente**.
Con una soundness de `Derives` hacia ℕ₀ y un testigo `¬(axioms ⊢ ψ)` con ψ verdadera se
derivaría `¬⟦ψ⟧`. **ROBINSON_PlusPlus no está afectado**: enuncia Gödel I con `Prf`
(aritmetizada, finitaria) y su puente `prf_to_derives` va en un solo sentido. Pero PeanoRF
es el proyecto que fabricaría el ingrediente que falta — de ahí M-9.

---

### Added (2026-09-06, tarde) — directiva fundacional y gate de pureza

- **MANDATORIES M-1..M-6 fijadas** (ADR-013, ADR-014). Las dos fundacionales:
  - **M-1 — la lógica de nivel OBJETO es INTUICIONISTA.** Prohibidos los tres axiomas
    clásicos de FOL (`MetaRules.dne`, `Theorems.Neg.dne`,
    `Theorems.Quantifiers.forall_not_impl_exists_not`). Sin baseline ni excepción.
  - **M-2 — las pruebas en Lean son CONSTRUCTIVAS**, diana `⊆ {propext, Quot.sound}`.
  - **M-3 — `ℕ₀` de peanolib** como único natural.
- **`PeanoRF/Meta/AxiomCheck.lean`** — gate de compilación de dos ejes, corre en cada
  `lake build`. Comandos `#assert_no_classical`, `#assert_intuitionistic`,
  `#assert_constructive_footprint`.
- **`sondeos/`** — mediciones fuera del build. `axiom_probe.lean` inventaría el footprint
  de las dependencias; `sondeos/README.md` guarda la medición que fundamenta ADR-013.

### Changed (2026-09-06, tarde)

- **Import surface de FOL estrechado a la mitad demostrativa** (M-5): fuera
  `FOL.Semantics`, `FOL.Soundness`, `FOL.Completeness`, `FOL.Compacity`. Ahí viven los 52
  `Classical.choice` de FOL y los únicos usos de sus tres axiomas clásicos. Build:
  25 → **21 jobs**.

### Fixed (2026-09-06, tarde)

- **El gate no mordía.** Su primera versión toleraba `Classical.choice` **por nombre de
  axioma** (con el argumento de que llegaba heredado de RPP), y un smoke test
  — `open Classical in theorem smoke (p : Prop) : p ∨ ¬p := em p` — lo atravesó
  clasificado como «deuda heredada». Ahora la tolerancia va **por procedencia**: solo
  cuenta como heredado lo que entra atravesando una constante de
  `FOL`/`ROBINSON_PlusPlus`/`Peano`. Ambos ejes verificados con smoke test (ADR-015).

### Measured (2026-09-06) — solo `#print axioms` mide; los `import` no

| Librería | Decls | Limpias | Nota |
|---|---:|---:|---|
| `Peano` (`PeanoNat.Axioms`) | 192 | **192** | 0 `axiom` — el cimiento ya cumple la diana |
| `FOL` (barrel completo) | 397 | 332 | 13 `axiom`, de los que **solo 3 son clásicos**; todos los usos, en la mitad que no importamos |
| `RPP.Minimal.Axioms` | 313 | 269 | ⚠️ `axioms` misma arrastra `Classical.choice` vía las primitivas `String` de la codificación |

---

### Added (2026-09-06)

- **Andamiaje inicial del proyecto**, generado desde `lean4-project-template` y
  enriquecido con lo aprendido en los proyectos hermanos (ROBINSON_PlusPlus, Peano,
  FOL, AczelSetTheory), que iban por delante de la plantilla:
  - `AI-GUIDE.md` **§27** — control de sincronía documentación ↔ código, con la regla
    de oro «no basta con arreglar el banner» (viene de ROBINSON_PlusPlus, 2026-08-23).
  - `AI-GUIDE.md` — banner de **lectura obligatoria de `DECISIONS.md` §MANDATORIES**
    antes de tocar cualquier `.lean` (viene de AczelSetTheory).
  - `check-doc-sync.bash` — versión **genérica** del control de ROBINSON_PlusPlus:
    detecta la librería desde `lakefile.lean` y concentra lo específico del proyecto en
    un bloque `CONFIGURACIÓN`. Controles [A] cifras, [B] símbolos muertos (aviso),
    [C] proyección, [D] marcas de tiempo.
  - `WORKFLOW.md` — reescrito con el **modo IA como flujo principal** y `git-lock.bash`
    como modo humano legacy (viene de ROBINSON_PlusPlus, 2026-06-05).
  - `DECISIONS.md` — sección MANDATORIES en **formato tabla con columna de
    verificación** (viene de AczelSetTheory).
  - `update-toolchain.bash` — versión con `--check`, consulta de la última estable y
    reversión automática (viene de AczelSetTheory).
  - `Makefile` — targets `docsync` / `docsync-quick`; guarda de `VERSION`.
  - `.claude/commands/docsync.md` — comando `/docsync`.
- `lakefile.lean` con las tres dependencias locales: `FOL`, `ROBINSON_PlusPlus`,
  `peanolib`. Toolchain v4.31.0, el mismo de las tres.
- `PeanoRF/Prelim.lean` — punto único de contacto con las librerías aguas arriba.
- Build verificado: 25 jobs, 0 `sorry` (hoy 21 tras estrechar el import de FOL).

### Pending

- **Definir el alcance matemático del proyecto** (Fase 0 de `NEXT-STEPS.md`). Hasta
  entonces, `REFERENCE.md`, `DEPENDENCIES.md` y `PLANNING.md` documentan solo el
  andamiaje, y lo dicen explícitamente.
- Poner `metaDebtIsError := true` cuando ROBINSON_PlusPlus sea constructivo a nivel meta.

---

## Versioning Conventions

- **MAJOR**: Breaking API changes or new foundational axiom
- **MINOR**: New backward-compatible functionality
- **PATCH**: Bug fixes and backward-compatible corrections

## Links

- [Repository](https://github.com/julian1c2a/Peano-from-ROB-n-FOL)
- [Issues](https://github.com/julian1c2a/Peano-from-ROB-n-FOL/issues)
