# PeanoRF

[![Lean 4](https://img.shields.io/badge/Lean-v4.31.0-blue)](https://leanprover.github.io/)
[![Build Status](https://img.shields.io/badge/build-22%20jobs%20passing-brightgreen)](CURRENT-STATUS-PROJECT.md)
[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)
[![Sorry](https://img.shields.io/badge/sorry-0-brightgreen)](CURRENT-STATUS-PROJECT.md)

> **Estado**: alcance fijado, gate de tres ejes en producción, teoría propia por empezar.
> Siguiente hito: **H2, el conjunto de axiomas de HA**. Ver
> [PLANNING.md](PLANNING.md) y [NEXT-STEPS.md](NEXT-STEPS.md).

Aritmética de Peano en Lean 4, construida sobre **ROBINSON_PlusPlus** (Q⁺⁺) y **FOL**
(lógica de primer orden con igualdad), sin Mathlib.

*(Directorio: `Peano-from-ROB-n-FOL`. El paquete y la librería se llaman `PeanoRF`
porque los guiones no son identificadores Lean válidos — ADR-011.)*

## Descripción

PeanoRF **vuelca el proyecto Peano al lenguaje FOL⁼ + ROB++**, de forma puramente
constructiva. El resultado es un **espejo**: lo que se demuestre para PeanoRF se conserva
en Peano. No es duplicación, es división del trabajo —

| | PeanoRF | Peano (`peanolib`) |
|---|---|---|
| Nivel | **objeto**: fórmulas de FOL⁼ y derivaciones | **meta**: tipos y funciones de Lean |
| Papel | **fundacional** | **computacional** |
| Responde | *¿qué se demuestra, y desde qué axiomas?* | *¿qué se calcula?* |

— que es, mirada de cerca, una interpretación de **realizabilidad**: los realizadores de
las pruebas de PeanoRF viven en Peano. El desarrollo completo, en [PLANNING.md](PLANNING.md).

**El núcleo es HA finitaria** (`⊢` recursivamente enumerable); la ω-lógica que ROB++ usa
en el 19 % de sus resultados vive aislada y contada en `PeanoRF.Omega.*` — **ADR-016**.

## ⚠️ MANDATORIES — leer [DECISIONS.md](DECISIONS.md) antes de tocar cualquier `.lean`

Reglas **vinculantes**: incumplirlas es un defecto de build, no una preferencia de estilo.

| # | Regla | Cómo se verifica |
|---|---|---|
| **M-1** | La lógica de nivel **OBJETO** es **intuicionista**. Prohibidos los tres axiomas clásicos de FOL. **Sin excepción** | gate, eje objeto |
| **M-2** | Las pruebas en Lean son **constructivas**: `#print axioms ⊆ {propext, Quot.sound}` | gate, eje meta |
| **M-3** | **`ℕ₀`** de peanolib siempre, nunca `Nat` | revisión + grep |
| **M-4** | No redefinir lo que ya existe aguas arriba | revisión |
| **M-5** | No importar barrels completos; **prohibido** `FOL.Semantics/Soundness/Completeness/Compacity` | revisión + gate |
| **M-6** | Las cuatro librerías, en el mismo toolchain | `cat */lean-toolchain` |
| **M-7** | El **núcleo es FINITARIO**: prohibidas las 5 ω-reglas de FOL y los 4 meta-axiomas de ROB++, salvo bajo `PeanoRF.Omega.*` | gate, eje finitario |
| **M-8** | La **inducción entra en el conjunto de axiomas**, nunca como `axiom : axioms ⊢ φ` | gate + revisión |
| **M-9** | **No** demostrar soundness para derivaciones con `raa`/`imp_intro` | revisión + M-7 |

El gate es [`PeanoRF/Meta/AxiomCheck.lean`](PeanoRF/Meta/AxiomCheck.lean) y corre en **cada
`lake build`**. Distingue **tres ejes** porque se violan por separado: se puede demostrar
clásicamente en Lean un teorema sobre una lógica intuicionista (viola meta, no objeto), y
`raa`/`gen` no son clásicas pero sí infinitarias (violan el finitario, no el objeto).

## Dependencias

| Paquete | Ruta | Qué aporta |
|---|---|---|
| `FOL` | `../FOL` | `Term`, `Formula`, `Derives (⊢)`, sustitución De Bruijn, reglas de igualdad, tácticas |
| `ROBINSON_PlusPlus` | `../ROBINSON_PlusPlus` | Aritmética de Robinson Q extendida sobre FOL⁼; aritmetización y Gödel |
| `peanolib` | `../Peano` | `ℕ₀` como tipo inductivo, axiomas de Peano **demostrados** |

⚠️ Son **rutas locales**, no `from git` (ADR-011): hace falta el árbol `lean4/` completo,
y las cuatro librerías deben compartir toolchain. Detalles en
[DEPENDENCIES.md](DEPENDENCIES.md).

## Módulos

| Módulo | Namespace | Dependencias | Estado |
|--------|-----------|--------------|--------|
| `Prelim.lean` | `PeanoRF.Prelim` | FOL (mitad demostrativa), `ROBINSON_PlusPlus.Minimal.Axioms`, `Peano.PeanoNat.Axioms` | 🔄 En curso |
| `Meta/AxiomCheck.lean` | `PeanoRF.Meta` | `PeanoRF.Prelim`, `PeanoRF.Omega.Basic` | ✅ Gate de 3 ejes |
| `Omega/Basic.lean` | `PeanoRF.Omega` | `PeanoRF.Prelim` | ✅ Capa ω declarada |

## Estructura

```text
PeanoRF/
├── Prelim.lean            # Punto único de contacto con las librerías aguas arriba
├── Meta/
│   └── AxiomCheck.lean    # Gate de 3 ejes (M-1, M-2, M-7)
├── Omega/
│   └── Basic.lean         # Capa ω: aislada y contada (ADR-016)
└── _template.lean         # Plantilla de módulo (no se importa)
PeanoRF.lean                  # Módulo raíz (generado por gen-root.bash)
sondeos/                      # Mediciones fuera del build (footprint de axiomas)
doc/                          # Nodos REFERENCE-{tema}.md (ADR-007), vacío por ahora
```

## Requisitos

- **Lean 4 v4.31.0** (gestionado por `elan`)
- Los tres proyectos sibling clonados en `../FOL`, `../ROBINSON_PlusPlus`, `../Peano`

## Compilar

```bash
lake build          # 22 jobs, con el gate de 3 ejes incluido
```

## Flujo de trabajo

```bash
make new NAME=ModuleName    # crear módulo nuevo desde plantilla
make build                  # compilar
make sorry                  # buscar sorrys
make docsync                # comprobar que la doc cuadra con el código (AI-GUIDE §27)
bash gen-root.bash          # regenerar los imports raíz

lake env lean sondeos/axiom_probe.lean   # re-medir el footprint de las dependencias
```

> Ver [WORKFLOW.md](WORKFLOW.md) para el flujo completo.

## Documentación

| Documento | Propósito |
|----------|---------|
| [AI-GUIDE.md](AI-GUIDE.md) | ⭐ **Leer primero**: estándares de documentación, formato, comandos formales |
| [DECISIONS.md](DECISIONS.md) | 🚨 **MANDATORIES + ADRs — obligatorio antes de tocar cualquier `.lean`** |
| [WORKFLOW.md](WORKFLOW.md) | Flujo de desarrollo (modo IA + modo humano legacy) |
| [REFERENCE.md](REFERENCE.md) | Referencia técnica: definiciones, teoremas, notaciones |
| [NAMING-CONVENTIONS.md](NAMING-CONVENTIONS.md) | Diccionario Mathlib-style y 12 reglas de formación de nombres |
| [DEPENDENCIES.md](DEPENDENCIES.md) | Grafo de dependencias (externas e internas) |
| [CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md) | Estado y métricas actuales |
| [NEXT-STEPS.md](NEXT-STEPS.md) | Fases de desarrollo |
| [PLANNING.md](PLANNING.md) | Rumbo a largo plazo |
| [CHANGELOG.md](CHANGELOG.md) | Historia de cambios |
| [THOUGHTS.md](THOUGHTS.md) | Diario de diseño (no normativo) |

## Convenciones de nombres

Estilo [Mathlib4](https://leanprover-community.github.io/contribute/naming.html).
Referencia completa en [NAMING-CONVENTIONS.md](NAMING-CONVENTIONS.md).

| Entidad | Convención | Ejemplo |
|--------|------------|---------|
| Módulo | `UpperCamelCase` | `CoreAxioms.lean` |
| Namespace | `UpperCamelCase` | `PeanoRF.Topic` |
| Tipo / predicado Prop | `UpperCamelCase` | `IsSet`, `IsFun` |
| Función / def de valor | `lowerCamelCase` | `powerset`, `dom` |
| Axioma | `TAG_ShortName` | `PA_Ind` |
| Teorema | `sujeto_predicado` | `add_comm`, `mem_pair_iff` |

## Licencia

MIT. Ver [LICENSE](LICENSE).

## Autor

Julián Calderón Almendros

---

*Última actualización: 2026-09-06 18:00*
