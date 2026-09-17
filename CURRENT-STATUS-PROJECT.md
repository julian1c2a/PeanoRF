# Current Project Status — PeanoRF

**Última actualización:** 2026-09-17
**Autor**: Julián Calderón Almendros

> **Estado: alcance FIJADO; gate de tres ejes en producción; teoría propia por empezar.**
> PeanoRF vuelca Peano al lenguaje FOL⁼ + ROB++ de forma constructiva: un **espejo** donde
> lo demostrado se conserva en Peano (`PLANNING.md` §1). El **núcleo es HA finitaria** y la
> ω-lógica vive aislada y contada en `PeanoRF.Omega.*` (**ADR-016**).
> 🏁 **H3: la solidez de `⊢ᵢ` es CONSTRUCTIVA** — `derivesI_soundness` mide
> `[propext, Quot.sound]`. El espejo no sólo es un teorema: es un teorema intuicionista.
>
> **H2 CERRADO** (2026-09-16), y sobre un cálculo nuevo. Aguas arriba se demostró que
> `FOL.Derives` **no puede tener solidez** (`inconsistencia_de_cualquier_solidez`): es
> HERRAMIENTA, no SUJETO. Todo H2 se ha **migrado a `⊢ᵢ`**, el cálculo intuicionista
> finitario de `PeanoRF/Calculus/DerivesI.lean` (ADR-017). `zero_add` y **`succ_add` (el
> caso con parámetro)** están probados ahí, sin ω-reglas y sin `ax_induction`.
>
> **Cifras canónicas** (las verifica `check-doc-sync.bash`, AI-GUIDE §27):
> **45 jobs · 12 módulos propios · 0 sorry vigentes · 0 axiom propios**.
>
> ⭐ **H3bis en marcha, y con un hallazgo del propio gate**: está demostrado que **`⊢ᵢ` es
> cerrado bajo sustitución paralela** (`derivesI_subst`, los 18 casos) y que **la barra
> sobrevive a `rewrite_at`** (`slash_rewrite`). Falta **un caso de L2**: la regla de
> Leibniz, porque `subst` sustituye sólo en el índice 0 y bajo un `∀` el índice se mueve.
> ⚠️ Al construirlo, el gate cazó un `Classical.choice` **propio** — un `simp` en
> `upS_singleS` — que contaminaba siete declaraciones. Reescrito con `if_pos`/`if_neg`
> explícitos. Es la primera vez que el eje META muerde sobre código nuestro.
>
> 🔎 **Auditoría del 2026-09-17 (tarde)**: el gate está verde y los footprints no se
> han movido, pero la auditoría de **cobertura** encontró dos agujeros y los cerró
> (ADR-018 rev. b): el criterio por tipo reconocía **una forma fija** y dejaba fuera
> `LK₀`/`LKc`/`LKh`/`Prf`/`Prf₀` — **67 constructores**; y la última lista por nombre
> dejaba pasar la **DNE en la capa ω** (`PrfH.p3`). Ahora: descubrimiento por
> **telescopio**, clásico **por lo que la regla dice**, capa ω con lista explícita
> (vacía), e inventario que publica también los **casi-candidatos**.
>
> ⚠️ **La cifra de `jobs` NO es un invariante del proyecto**: depende de qué dependencias
> locales haya que reconstruir. El 2026-09-16 osciló entre 30 y 31 según el estado de la
> caché de FOL, y el control [A] dio VERDE con la cifra desfasada. Las otras tres sí son
> invariantes; ésta se lee con esa reserva.

---

## Resumen ejecutivo

| Métrica | Valor |
|--------|-------|
| Módulos propios | 12 (`Prelim`, `Calculus/{DerivesI,Eq,Soundness,Consistency,Slash,Subst,SubstDerives}`, `Meta/AxiomCheck`, `Omega/Basic`, `HA/{Axioms,Arith}`) |
| Módulos con 0 `sorry` | 12 / 12 |
| Teoremas propios | 60 |
| Definiciones propias | 8 (el álgebra de sustituciones) |
| Notaciones propias | 0 |
| `axiom` de Lean propios | 0 |
| Build | ✅ 45 jobs (ver la reserva del banner) |
| Lean | v4.31.0 |
| Dependencias | `FOL`, `ROBINSON_PlusPlus`, `peanolib` (rutas locales) |
| Convención de nombres | Mathlib-style (ver `NAMING-CONVENTIONS.md`) |

---

## Estado por módulo

| Módulo | Teoremas | Definiciones | Sorry | Estado |
|--------|----------|-------------|-------|--------|
| `PeanoRF/Prelim.lean` | 0 | 0 | 0 | 🔄 In progress |
| `PeanoRF/Meta/AxiomCheck.lean` | 0 | 0 | 0 | ✅ Completo (gate de 3 ejes en producción) |
| `PeanoRF/Omega/Basic.lean` | 0 | 5 | 0 | ✅ Capa ω declarada (5 alias sancionados) |
| `PeanoRF/HA/Axioms.lean` | 7 | 1 | 0 | ✅ Conjunto de axiomas + `gen_closed` |
| `PeanoRF/HA/Arith.lean` | 2 | 2 | 0 | ✅ `zero_add` y `succ_add` sobre `⊢ᵢ` |
| `PeanoRF/Calculus/DerivesI.lean` | 2 | 1 | 0 | ✅ El cálculo `⊢ᵢ` + puentes |
| `PeanoRF/Calculus/Eq.lean` | 5 | 0 | 0 | ✅ Igualdad sobre `⊢ᵢ` |
| `PeanoRF/Calculus/Soundness.lean` | 2 | 0 | 0 | 🏁 **H3**: solidez **CONSTRUCTIVA** (`propext, Quot.sound`) |

*Códigos*: ✅ Completo · 🧊 Congelado · 🔶 Parcial · 🔄 En curso · ❌ Pendiente

---

## Estado de las dependencias (2026-09-06)

| Proyecto | Rama | Toolchain | Nota |
|---|---|---|---|
| `FOL` | `master` | v4.31.0 | Verde. 13 `axiom`, de los que **3 son clásicos de nivel objeto** y solo se usan desde la mitad modelo-teórica, que NO importamos (M-5) |
| `ROBINSON_PlusPlus` | `via-c-adr020` | v4.31.0 | Frente abierto con parada **conocida y localizada** en `Meta/MpCodePrf.lean`; `master` verde. Solo importamos `Minimal/` (ADR-012). ⚠️ **No constructivo a nivel META todavía** (44/313 con `Classical.choice`, incluida `axioms`); sí a nivel objeto. Deuda contabilizada por el gate |
| `Peano` | `master` | v4.31.0 | Verde. **192/192 declaraciones limpias, 0 `axiom`** — el cimiento aritmético ya cumple la diana |

---

## Logros recientes

- Proyecto creado desde `lean4-project-template` y **enriquecido** con lo que los
  proyectos hermanos habían aprendido después de la última propagación (2026-07-12):
  el control `check-doc-sync.bash` (§27), el banner de MANDATORIES obligatorias, el
  `WORKFLOW` centrado en el modo IA, y las MANDATORIES en formato tabla verificable.
- Las mejoras se han devuelto también a `lean4-project-template` en su forma genérica.
- Build verde con las tres dependencias enganchadas por ruta local.
- **Directiva fundacional fijada** (2026-09-06): pureza constructiva en dos ejes y `ℕ₀`
  como único natural — M-1..M-3, ADR-013/014.
- **Gate de pureza en producción y PROBADO** con smoke tests en los dos ejes (ADR-015).
  Al probarlo se encontró y corrigió un fallo real: toleraba `Classical.choice` por
  nombre de axioma, de modo que un `Classical.em` propio pasaba como deuda heredada.
- **Import surface de FOL estrechado** a la mitad demostrativa: fuera Semantics,
  Soundness, Completeness y Compacity (donde vive todo lo clásico).
  El build bajó de 25 a 21 jobs.
- **Alcance fijado y ADR-016**: el núcleo es **HA finitaria**; la ω-lógica queda aislada
  en `PeanoRF.Omega.*`. Nace de medir que **99 de 521 declaraciones de ROB++ (19 %)
  pasan por ω-reglas**, y de que `Full/Induction.lean` postula
  `axiom ax_induction : axioms ⊢ inductionFormula φ` — falso bajo un `⊢` finitario.
- **Tercer eje en el gate** (finitario), con smoke test en los dos sentidos: error fuera
  de la capa ω, recuento dentro (hoy 5).
- **H2 · la inducción deja de ser un axioma.** `HA.ctx insts = axioms ++ instancias`, y la
  instancia entra por `Derives.hyp`. Medido:

| símbolo | footprint |
|---|---|
| `PeanoRF.HA.zero_add` (finitario) | `propext, Classical.choice, Quot.sound` |
| `ROBINSON_PlusPlus.Full.zero_add` (ω) | `propext, Classical.choice, Quot.sound,` **`FOL.MetaRules.gen, FOL.MetaRules.imp_intro, ROBINSON_PlusPlus.Full.ax_induction`** |
| `PeanoRF.HA.gen_closed` | `propext` |

La versión finitaria **elimina tres axiomas**: la ω-regla, la meta-regla de implicación y
la derivabilidad postulada de la inducción. El `Classical.choice` que queda es la deuda
META heredada de la codificación `String` de RPP, no nuestra.

---

## Trabajo pendiente

- [x] ~~**H2 completo**~~ → `⊢ᵢ`, `ctx`, `gen_closed`, `Closed`, `zero_add` y `succ_add`.
- [x] ~~**H3 · transferencia**~~ → `derivesI_soundness` y `derivesI_consistent`, heredando
      `derives0_soundness`. **El espejo ya es un teorema.**
- [x] ~~**H3 · inducción directa**~~ → hecha, 18 casos. Pero **no basta**: la conjetura de
      ADR-019 era falsa.
- [x] ~~**H3 · el último `Classical`**~~ → 🏁 **RESUELTO**. Estaba en **una línea** de
      `FOL.Metamath.Semantics.shift_updateEnv_comm`: un `omega` cerrando por contradicción
      una meta **fuera de su lenguaje** (de tipo `D`). Sustituido por `absurd`.
      ⇒ **`derivesI_soundness : propext, Quot.sound`** — la solidez de la lógica
      intuicionista, demostrada intuicionistamente.
- [x] ~~El arreglo de FOL~~ → aceptado y commiteado allí (`6d47e5b`), blindado en su
      `check-footprints.bash`.
- [x] ~~`forbiddenConstructors` por NOMBRE~~ → **reescrito POR TIPO** (ADR-018, 2026-09-17)
      tras una auditoría que midió **9 de 12 constructores clásicos sin vigilar**. El gate
      publica ahora un **inventario** de las relaciones de derivabilidad que detecta.
- [x] ~~El tipo, por UNA FORMA FIJA~~ → **por TELESCOPIO** (ADR-018 rev. b, 2026-09-17
      tarde). Medía 6 relaciones de 11; `LK₀`, `LKc`, `LKh`, `Prf` y `Prf₀` quedaban fuera
      — **67 constructores**. Ahora ve las 11 y vigila 90.
- [x] ~~Clásico por NOMBRE~~ → **por lo que la regla DICE** (el patrón de la doble
      negación en el tipo). Lo forzó medir que `PrfH.p3` —la DNE con otro nombre— pasaba
      **dentro de la capa ω**, con el gate imprimiendo «intuicionista puro».
- [x] ~~La capa ω como comodín~~ → ahora exige entrada explícita en
      `omegaAllowedForeignCtors`, **vacía**. Relaja en efectividad (M-7), nunca en M-1.
- [x] ~~`check-doc-sync.bash` daba VERDE VACUO~~ → sin `lake` en el `PATH` se saltaba el
      control [A] entero y anunciaba «sin cifras obsoletas» con exit 0, sobre un árbol que
      con `lake` daba exit 1. **Con ese verde vacuo se empujó `67b0d50`.** Ahora: no poder
      medir es ROJO, las cifras se comprueban contra la **línea canónica**, y la prosa de
      cabecera sólo avisa (medía 2 falsos positivos y 0 verdaderos).
- [x] ~~`CRASH` versionado~~ → fichero basura de un programa ajeno, colado en `b786238`
      por un `git add -A`. Retirado. ⚠️ Es la misma queja de proceso que llegó de FOL.
- [ ] ⬜ Aguas arriba, sin resolver (de FOL): la causa del `Classical` en `Theorems.Eq` (3)
      y `Tactics.tryMem` (sin medir).
- [ ] `add_comm`, `mul_*` — ya sin incógnitas de método.
- [x] ~~Alcance del proyecto~~ → fijado (`PLANNING.md` §1).
- [x] ~~Pureza constructiva~~ → **M-1 y M-2** (ADR-013), con gate probado.
- [x] ~~Qué naturales~~ → **M-3**: `ℕ₀` de peanolib (ADR-014).
- [ ] Política de axiomas propios para `axiom` de naturaleza distinta a M-8.
- [ ] Poner `metaDebtIsError := true` cuando ROBINSON_PlusPlus se sanee a nivel meta.
- [ ] Configurar `SYMBOL_PREFIXES` en `check-doc-sync.bash` cuando existan familias de
      símbolos propias.

---

## Arquitectura

```text
PeanoRF/
├── Prelim.lean            # Nivel 0: contacto con FOL / ROBINSON_PlusPlus / Peano
├── Meta/
│   └── AxiomCheck.lean    # Gate de 3 ejes — corre en cada build
└── Omega/
    └── Basic.lean         # Capa ω declarada, aislada y contada (ADR-016)
sondeos/                   # Mediciones fuera del build (no cuentan como módulos)
```

---

## Fases de desarrollo

| Fase | Descripción | Estado |
|-------|-------------|--------|
| H0 Andamiaje | Plantilla, dependencias, build verde | ✅ |
| H1 Directiva | Pureza constructiva + gate de 3 ejes | ✅ |
| H2 Axiomas HA | Q⁺⁺ + inducción como axiomas (M-8), sobre `⊢ᵢ` | ✅ |
| H3 Interpretación | `⟦·⟧` en ℕ₀ + soundness finitaria (M-9) | ❌ |
| H4 Reflexión | `⌜·⌝` + adecuación + táctica | ❌ |
| H5–H7 | Volcado, realizabilidad, metateoría | ❌ |

> Ver [NEXT-STEPS.md](NEXT-STEPS.md) para el detalle.

---

**Autor**: Julián Calderón Almendros
*Última actualización: 2026-09-17*

[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)
