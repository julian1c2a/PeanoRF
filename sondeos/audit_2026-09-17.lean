-- AUDITORÍA 2026-09-17 — estado de aguas arriba y de la lista del gate
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import FOL
import ROBINSON_PlusPlus.Minimal.Axioms
import PeanoRF.Calculus.Soundness
import PeanoRF.HA.Arith
open Lean Elab Command

/-- Lista los constructores de un inductivo. -/
elab "#ctors_of " id:ident : command => do
  let n ← resolveGlobalConstNoOverload id
  let env ← getEnv
  match env.find? n with
  | some (.inductInfo iv) => logInfo m!"{n}: {iv.ctors.length} ctors
  {iv.ctors}"
  | _ => logInfo m!"{n}: no es inductivo"

#ctors_of Derives
#ctors_of Derives₀
#ctors_of Derives₁
#ctors_of Derives₂
#ctors_of PeanoRF.Calculus.Derivesᵢ

/-- Recuento de Classical.choice por módulo bajo un prefijo. -/
elab "#dirty " root:ident : command => do
  let env ← getEnv
  let mods := env.header.moduleNames
  let r := root.getId
  let mut n : Nat := 0
  for (nm, _) in env.constants.toList do
    if nm.isInternalDetail then continue
    let some i := env.const2ModIdx[nm]? | continue
    unless r.isPrefixOf mods[i.toNat]! do continue
    if (← collectAxioms nm).contains ``Classical.choice then n := n + 1
  logInfo m!"{r}: {n} decls con Classical.choice"

#dirty FOL
#dirty ROBINSON_PlusPlus

-- el resultado propio, ¿sigue en pie?
#print axioms PeanoRF.Calculus.derivesI_soundness
#print axioms PeanoRF.HA.zero_add
#print axioms PeanoRF.HA.succ_add
