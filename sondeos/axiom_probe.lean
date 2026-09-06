-- SONDEO TEMPORAL — inventario de AXIOMAS declarados aguas arriba y su alcance.
-- Se ejecuta con:  lake env lean probe_axioms.lean
import Lean.Elab.Command
import Lean.Util.CollectAxioms

import FOL
import ROBINSON_PlusPlus.Minimal.Axioms
import Peano.PeanoNat.Axioms

set_option autoImplicit false

open Lean Elab Command

/-- Todos los `axiom` declarados bajo un prefijo de módulo. -/
elab "#axioms_of " root:ident : command => do
  let env ← getEnv
  let mods := env.header.moduleNames
  let rootName := root.getId
  let mut found : Array (Name × Name) := #[]
  for (name, info) in env.constants.toList do
    if name.isInternalDetail then continue
    let some modIdx := env.const2ModIdx[name]? | continue
    let m := mods[modIdx.toNat]!
    unless rootName.isPrefixOf m do continue
    if let .axiomInfo _ := info then
      found := found.push (name, m)
  logInfo m!"══ {found.size} `axiom` bajo {rootName}:\n{found.toList}"

/-- Cuántas declaraciones (bajo cualquier prefijo dado) dependen de un axioma concreto. -/
elab "#dependents " ax:ident " under " root:ident : command => do
  let env ← getEnv
  let mods := env.header.moduleNames
  let axName ← resolveGlobalConstNoOverload ax
  let rootName := root.getId
  let mut hits : Array Name := #[]
  for (name, _info) in env.constants.toList do
    if name.isInternalDetail then continue
    let some modIdx := env.const2ModIdx[name]? | continue
    unless rootName.isPrefixOf mods[modIdx.toNat]! do continue
    let axs ← collectAxioms name
    if axs.contains axName then hits := hits.push name
  logInfo m!"{axName} ← {hits.size} decls bajo {rootName}: {hits.toList}"

#axioms_of FOL
#axioms_of ROBINSON_PlusPlus
#axioms_of Peano

#dependents FOL.MetaRules.dne under FOL
#dependents FOL.Theorems.Neg.dne under FOL
#dependents FOL.Theorems.Quantifiers.forall_not_impl_exists_not under FOL
