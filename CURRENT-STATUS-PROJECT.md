# Current Project Status — PeanoRF

**Última actualización:** 2026-09-06 21:00
**Autor**: Julián Calderón Almendros

> **Estado: alcance FIJADO; gate de tres ejes en producción; teoría propia por empezar.**
> PeanoRF vuelca Peano al lenguaje FOL⁼ + ROB++ de forma constructiva: un **espejo** donde
> lo demostrado se conserva en Peano (`PLANNING.md` §1). El **núcleo es HA finitaria** y la
> ω-lógica vive aislada y contada en `PeanoRF.Omega.*` (**ADR-016**).
> **H2 entregado en su parte crítica**: el conjunto de axiomas de HA existe, la
> generalización finitaria `gen_closed` está probada, y `zero_add` está **reprobado sin
> ω-reglas y sin `ax_induction`** — tres axiomas menos que la versión de ROB++.
>
> **Cifras canónicas** (las verifica `check-doc-sync.bash`, AI-GUIDE §27):
> **25 jobs · 5 módulos propios · 0 sorry vigentes · 0 axiom propios**.

---

## Resumen ejecutivo

| Métrica | Valor |
|--------|-------|
| Módulos propios | 5 (`Prelim`, `Meta/AxiomCheck`, `Omega/Basic`, `HA/Axioms`, `HA/Arith`) |
| Módulos con 0 `sorry` | 5 / 5 |
| Teoremas propios | 8 |
| Definiciones propias | 0 |
| Notaciones propias | 0 |
| `axiom` de Lean propios | 0 |
| Build | ✅ 25 jobs |
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
| `PeanoRF/HA/Arith.lean` | 1 | 1 | 0 | 🔄 Primer teorema finitario (`zero_add`) |

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
  Soundness, Completeness y Compacity (donde vive todo lo clásico). El build bajó de
  25 a 21 jobs.
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

- [x] ~~**H2 · infraestructura**~~ → `ctx`, `ax'`, `ind`, `mono`, `induction_object`,
      `gen_closed`, y `zero_add` reprobado finitariamente.
- [ ] **H2 · resto**: reprobar el siguiente escalón de `Full/Induction` (`succ_add`,
      `add_comm`, `mul_*`) para medir el coste con **parámetro**, no sólo sin él.
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
| H2 Axiomas HA | Q⁺⁺ + inducción como axiomas (M-8) | 🔄 infraestructura ✅, volcado en curso |
| H3 Interpretación | `⟦·⟧` en ℕ₀ + soundness finitaria (M-9) | ❌ |
| H4 Reflexión | `⌜·⌝` + adecuación + táctica | ❌ |
| H5–H7 | Volcado, realizabilidad, metateoría | ❌ |

> Ver [NEXT-STEPS.md](NEXT-STEPS.md) para el detalle.

---

**Autor**: Julián Calderón Almendros
*Última actualización: 2026-09-06 21:00*

[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)
