/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: PeanoRF.Prelim (add more as needed)
-- @axiom_system: none
-- @importance: medium

import PeanoRF.Prelim
-- import PeanoRF.OtherModule

-- Disponible vía Prelim (sin re-importar):
--   FOL           — Term, Formula, Derives (⊢), sustitución, tácticas
--   ROBINSON_PlusPlus.Minimal.Axioms — lenguaje y axiomas de Q⁺⁺
--   Peano.PeanoNat.Axioms            — ℕ₀ y su API básica
--   ExistsUnique / ∃! / ∃¹ y su API  — vienen de `Peano.Prelim`, NO se redefinen aquí
--                                      (ADR-010: dos copias serían dos constantes
--                                      distintas que no componen)
--   ⚠️ Consulta DECISIONS.md §MANDATORIES antes de usar `Classical.*`.

namespace PeanoRF.ModuleName

-- ============================================================
-- Section 1: Definitions
-- ============================================================
-- Naming: UpperCamelCase for Prop predicates (IsXxx)
--         lowerCamelCase for functions/constructors

-- def myDef : Type := ...

-- ============================================================
-- Section 2: Basic Properties
-- ============================================================
-- Naming: subject_predicate pattern (snake_case)
--         Suffixes: _iff, _eq, _of_, _mem, _subset, _ne

-- theorem myTheorem : ... := by ...

-- ============================================================
-- Section 3: Advanced Theorems
-- ============================================================
-- Naming: conclusion_of_hypothesis pattern
--         Use .mp/.mpr for iff directions

-- ============================================================
-- Section 4: Exports (AI-GUIDE.md §17)
-- ============================================================
-- List ALL public (non-private) declarations alphabetically.
-- This block goes AFTER end namespace, at top level.
-- Notation/syntax propagates automatically — do not list here.

end PeanoRF.ModuleName

export PeanoRF.ModuleName (
  -- myDef
  -- myTheorem
)
