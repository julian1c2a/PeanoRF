-- SONDEO H2b — ¿es cerrado el contexto cuando la instancia de inducción lleva PARÁMETRO?
import PeanoRF.HA.Axioms
open FOL PeanoRF.Calculus PeanoRF.HA
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Full (inductionFormula)
set_option maxRecDepth 100000

def phiP (a : Term) : Formula :=
  add (succ (liftTerm 0 a)) (.var 0) =eq succ (add (liftTerm 0 a) (.var 0))

-- (1) Con `a` CERRADO (`zero`): ¿sale por rfl como en zero_add?
example : (ctx [phiP zero]).map (liftFormula 0) = ctx [phiP zero] := by rfl

-- (2) Con `a` ARBITRARIO: ¿qué hace falta?
-- (2b) la hipótesis CORRECTA: `a` cerrado a TODO nivel, no sólo al 0.
example (a : Term) (ha : ∀ k, liftTerm k a = a) (hs : ∀ k t, substTerm k t a = a) :
    ([phiP a].map inductionFormula).map (liftFormula 0) = [phiP a].map inductionFormula := by
  simp [phiP, inductionFormula, liftFormula, liftTerm, substFormula, substTerm, substTerms,
    add, succ, zero, ha, hs, liftTerms, substTerms]
