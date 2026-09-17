-- SONDEO 2026-09-17 (e) — ¿cuánto cuesta la consistencia SIN semántica?
import PeanoRF.Calculus.DerivesI
import FOL.Finitary0
open FOL PeanoRF.Calculus

#print axioms FOL.Finitary0.derives0_consistent_fin

/-- Consistencia de `⊢ᵢ` por la vía SINTÁCTICA: ni un modelo en toda la cadena. -/
theorem consistI_syn : Not (([] : List Formula) ⊢ᵢ Formula.bottom) :=
  fun h => FOL.Finitary0.derives0_consistent_fin (derivesI_to_derives0 h)

#print axioms consistI_syn

/-- Y que `⊢ᵢ` tampoco prueba un átomo — o sea que no es trivial por arriba. -/
theorem notP_syn : Not (([] : List Formula) ⊢ᵢ Formula.atom "P" []) :=
  fun h => FOL.Finitary0.derives0_not_P_fin (derivesI_to_derives0 h)

#print axioms notP_syn
