-- SONDEO H3b — ¿DE DÓNDE sale el Classical.choice, si no es de las reglas clásicas?
import Lean.Util.CollectAxioms
import FOL.Semantics
open Lean FOL.Metamath.Semantics

-- Los lemas de la semántica que usa la prueba de solidez:
#print axioms FOL.Metamath.Semantics.contextSatisfies_lift_zero
#print axioms FOL.Metamath.Semantics.eval_substFormula_zero
#print axioms FOL.Metamath.Semantics.eval_liftFormula_zero
#print axioms FOL.Metamath.Semantics.rule_soundness
#print axioms FOL.Metamath.Semantics.replaceAt_soundness
-- y la evaluación misma:
#print axioms FOL.Metamath.Semantics.evalFormula
#print axioms FOL.Metamath.Semantics.evalTerm
