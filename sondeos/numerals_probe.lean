-- SONDEO 2026-09-18 — ¿es viable H3ter por la vía barata (reusar la capa de numerales)?
--
-- Dos preguntas independientes:
--   (a) ¿qué footprint tienen `numeral_add`/`numeral_mul`? (¿ω-reglas? ¿ax_induction?)
--   (b) ¿sobre qué derivabilidad están enunciados? ⚠️ Si es `⊢`, NO nos sirven: el puente
--       va ⊢ᵢ → ⊢₀ → ⊢ en UN SOLO sentido (ADR-017).
import ROBINSON_PlusPlus.Full.Numerals
import PeanoRF.HA.Arith

#print axioms ROBINSON_PlusPlus.Full.numeral_add
#print axioms ROBINSON_PlusPlus.Full.numeral_mul
#print axioms ROBINSON_PlusPlus.Full.numeral_lt
#print axioms ROBINSON_PlusPlus.Full.numeral_ne
#print axioms ROBINSON_PlusPlus.Full.numeral
#print axioms ROBINSON_PlusPlus.Full.numeral_pow
