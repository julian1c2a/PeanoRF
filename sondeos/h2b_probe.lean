-- SONDEO — ¿qué ha cambiado aguas arriba desde 2026-09-06?
import Lean.Util.CollectAxioms
import PeanoRF.HA.Arith
import ROBINSON_PlusPlus.Full.Induction
open Lean
-- ¿cuáles de las 5 meta-reglas siguen siendo `axiom`?
#print axioms FOL.MetaRules.gen
#print axioms FOL.MetaRules.imp_intro
#print axioms FOL.MetaRules.raa
#print axioms FOL.MetaRules.or_elim
#print axioms FOL.MetaRules.ex_elim
-- el cambio clave anunciado en REFERENCE de RPP
#print axioms ROBINSON_PlusPlus.Full.ax_induction
#print axioms PeanoRF.HA.zero_add
