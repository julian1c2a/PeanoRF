-- SONDEO H3c — ¿es shift_updateEnv_comm la ÚNICA raíz del Classical en la semántica?
import Lean.Util.CollectAxioms
import FOL.Semantics
open Lean FOL.Metamath.Semantics
-- nivel TÉRMINO (¿limpio?)
#print axioms FOL.Metamath.Semantics.eval_liftTerm_ext
#print axioms FOL.Metamath.Semantics.eval_substTerm_ext
#print axioms FOL.Metamath.Semantics.eval_liftTerms_ext
#print axioms FOL.Metamath.Semantics.eval_substTerms_ext
-- la raíz sospechosa y su cadena
#print axioms FOL.Metamath.Semantics.shift_updateEnv_comm
#print axioms FOL.Metamath.Semantics.eval_liftFormula_ext
#print axioms FOL.Metamath.Semantics.shift_updateEnv_subst_comm
#print axioms FOL.Metamath.Semantics.eval_substFormula_ext
