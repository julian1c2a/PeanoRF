-- SONDEO H2 — ¿es el contexto de axiomas invariante bajo liftFormula 0?
-- Es la pieza que decide si `Derives.intro_forall` (finitario) es usable en vez de la ω-regla.
import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Full.Induction

open FOL ROBINSON_PlusPlus.Minimal.Axioms

set_option maxRecDepth 100000

-- (1) ¿Son cerrados los axiomas? Prueba por cómputo del kernel.
example : axioms.map (liftFormula 0) = axioms := by rfl

-- (2) ¿Y la instancia de inducción para una φ concreta con sólo #0 libre?
def phi0 : Formula := add zero (.var 0) =eq (.var 0)

example : liftFormula 0 (ROBINSON_PlusPlus.Full.inductionFormula phi0)
        = ROBINSON_PlusPlus.Full.inductionFormula phi0 := by rfl
