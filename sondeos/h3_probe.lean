-- SONDEO H3 — ¿es CONSTRUCTIVA la solidez de ⊢ᵢ?
-- La conjetura de ADR-019: el Classical.choice de derives0_soundness es exactamente
-- el precio de los tres constructores clásicos de ⊢₀.
import Lean.Util.CollectAxioms
import PeanoRF.Calculus.Soundness
import FOL.Soundness0
open Lean

#print axioms PeanoRF.Calculus.derivesI_soundness
#print axioms PeanoRF.Calculus.derivesI_consistent
#print axioms FOL.Metamath.Soundness0.derives0_soundness
#print axioms FOL.Metamath.Semantics.satisfies
