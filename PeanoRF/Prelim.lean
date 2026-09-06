/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- This is the foundational module. All other modules import it.
--
-- @axiom_system: FOL⁼ intuicionista (vía FOL, sin la mitad modelo-teórica) + Q⁺⁺
-- @importance: high

-- ── FOL: SOLO el cálculo de pruebas, NO la mitad modelo-teórica ──────────────
-- Se importa módulo a módulo, y NO el barrel `FOL`, para dejar fuera
-- `FOL.Semantics`, `FOL.Soundness`, `FOL.Completeness` y `FOL.Compacity`.
-- Medido (sondeos/axiom_probe.lean, 2026-09-06): ahí viven los 52 `Classical.choice`
-- de FOL y los 5 axiomas de completitud, y es el ÚNICO sitio desde el que se usan los
-- tres axiomas CLÁSICOS de nivel objeto. Dejarla fuera hace la contaminación
-- imposible por construcción, no solo improbable (ADR-013).
import FOL.FOL
import FOL.MetaRules
import FOL.Tactics
import FOL.Deduction
import FOL.Theorems.Derived
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Quantifiers

-- ── Aritmética ──────────────────────────────────────────────────────────────
import ROBINSON_PlusPlus.Minimal.Axioms
import Peano.PeanoNat.Axioms

/-! # Prelim — punto único de contacto con las librerías aguas arriba

  Este módulo **no define nada propio todavía**: su única función hoy es fijar el
  *import surface* del proyecto y dejar por escrito por qué es el que es.

  ## Por qué no se redefine infraestructura aquí

  La plantilla trae un `Prelim.lean` con su propio `ExistsUnique` y la notación `∃!`.
  **Aquí se ha retirado deliberadamente**: `Peano.Prelim` ya define esa misma
  infraestructura, y dos definiciones idénticas en dos namespaces distintos son **dos
  constantes que no componen** — no son defeq para el elaborador, y cada lema probado
  sobre una es inútil sobre la otra. El coste no se paga al escribirlas, sino meses
  después, cuando hace falta un puente `rfl` por cada teorema que las cruce.
  Ver `DECISIONS.md` ADR-010.

  ## Por qué estos imports y no los barrels completos

  * De FOL, **el cálculo de pruebas y no la semántica** (ver el bloque de imports).
  * De ROBINSON_PlusPlus, **solo la capa `Minimal`**: el barrel completo arrastra la
    capa `Meta/` (aritmetización, Gödel), que es cara y hoy está en pleno frente de
    trabajo — no se importa lo que no se necesita.
  * De Peano, **solo los axiomas de ℕ₀**: el barrel completo arrastra toda la teoría
    de arriba (grupos, Sylow, primos…), ajena a este proyecto.

  El gate `PeanoRF/Meta/AxiomCheck.lean` vigila que esta disciplina se cumpla en las
  pruebas, no solo en los imports: los imports no demuestran nada (`AI-GUIDE.md` §27,
  y la lección «sólo `#print axioms`»).

  Cuando el alcance del proyecto esté fijado, esta lista se revisa y se documenta el
  cambio en `DEPENDENCIES.md`.
-/

namespace PeanoRF.Prelim

-- Las definiciones preliminares propias del proyecto van aquí.

end PeanoRF.Prelim
