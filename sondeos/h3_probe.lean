-- SONDEO H3 — ¿cuánto cuesta heredar la solidez de aguas arriba?
-- Decide si M-5 (prohibido importar FOL.Semantics) se enmienda con una medición
-- o si hay que construir una interpretación propia en ℕ₀.
import Lean.Util.CollectAxioms
import FOL.Soundness0
open Lean

#print axioms derives0_soundness
#print axioms FOL.Metamath.Semantics.satisfies
#check @derives0_soundness
#check @FOL.Metamath.Semantics.satisfies
#check @FOL.Metamath.Semantics.Model
