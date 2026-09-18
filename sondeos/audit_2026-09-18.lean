-- AUDITORÍA 2026-09-18 — ¿ve el gate un cálculo que NO EXISTÍA cuando se escribió?
--
-- FOL estrenó anoche `LKp` (FOL/Craig0.lean, ADR-063: Maehara + interpolación de Craig).
-- El criterio por TELESCOPIO se escribió el 2026-09-17 sin saber que `LKp` iba a existir.
-- Si el gate lo ve SIN QUE NADIE TOQUE AxiomCheck.lean, la tesis de ADR-018 rev.b se
-- sostiene; si no lo ve, ha caducado por cuarta vez.
import FOL.Craig0
import PeanoRF.Meta.AxiomCheck
open FOL PeanoRF.Calculus

#assert_constructive_footprint

/-- Y la prueba dura: un teorema que usa un constructor de `LKp`. -/
theorem smoke_lkp (Γ Δ : List Formula) (A : Formula) (h1 : A ∈ Γ) (h2 : A ∈ Δ) :
    FOL.Craig0.LKp Γ Δ :=
  FOL.Craig0.LKp.ax Γ Δ A h1 h2

#assert_no_forbidden_ctor smoke_lkp
