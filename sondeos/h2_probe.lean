-- SONDEO H2 — footprint exacto de la prueba finitaria de zero_add.
--   lake env lean sondeos/h2_probe.lean
import Lean.Util.CollectAxioms
import PeanoRF.HA.Arith
import ROBINSON_PlusPlus.Full.Induction
open Lean

#print axioms PeanoRF.HA.zero_add
#print axioms PeanoRF.HA.gen_closed
#print axioms ROBINSON_PlusPlus.Full.zero_add
