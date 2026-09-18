-- SONDEO 2026-09-18 — la salida que apunta RPP: ¿nos basta `coreAxioms`?
import PeanoRF.HA.Numerals
open ROBINSON_PlusPlus.Minimal.Axioms
#print axioms ROBINSON_PlusPlus.Minimal.Axioms.axioms
#print axioms ROBINSON_PlusPlus.Minimal.Axioms.coreAxioms

-- ¿están los seis que usamos?
example : ax4_add_zero ∈ coreAxioms := by simp [coreAxioms]
example : ax5_add_succ ∈ coreAxioms := by simp [coreAxioms]
example : ax8_mul_zero ∈ coreAxioms := by simp [coreAxioms]
example : ax9_mul_succ ∈ coreAxioms := by simp [coreAxioms]
example : ax_pow_zero ∈ coreAxioms := by simp [coreAxioms]
example : ax_pow_succ ∈ coreAxioms := by simp [coreAxioms]
