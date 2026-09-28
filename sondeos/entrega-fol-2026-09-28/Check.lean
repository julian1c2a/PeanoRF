import Lean
import Spike.Slash
open Lean Elab Command in
elab "#spike_audit" : command => do
  let env ← getEnv
  let mut n := 0
  let mut bad : Array (Name × Array Name) := #[]
  let mut seen : Std.HashSet Name := {}
  for (c, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`Spike).isPrefixOf mod do continue
    if c.isInternal then continue
    n := n + 1
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do seen := seen.insert a
    if axs.any (fun a => a != ``propext && a != ``Quot.sound) then bad := bad.push (c, axs)
  logInfo m!"constantes Spike (no internas): {n}; axiomas vistos: {seen.toList}; fuera de [propext, Quot.sound]: {bad.size} {bad.toList.take 10}"
#spike_audit
#print axioms PeanoRF.Calculus.derivesI_ne_derives0
#print axioms PeanoRF.Calculus.disjunction_property
#print axioms PeanoRF.Calculus.existence_property
#print axioms PeanoRF.Calculus.slash_of_derives
