-- SONDEO — ¿cuánto de ROB++ depende de las META-REGLAS ω de FOL?
--
-- La pregunta decide qué teoría es realmente PeanoRF. Las cinco meta-reglas
-- (`imp_intro`, `gen`, `raa`, `or_elim`, `ex_elim`) son ω-reglas: con ellas
-- `⊢` deja de ser recursivamente enumerable y el sistema pasa a ser ω-lógica
-- («demostrabilidad = verdad en ℕ», como dice el propio docstring de FOL).
-- Si ROB++/Full las usa de forma pervasiva, PeanoRF NO es HA: es aritmética verdadera.
--
--   lake env lean sondeos/omega_probe.lean
import Lean.Elab.Command
import Lean.Util.CollectAxioms

import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Full.Induction
import ROBINSON_PlusPlus.Full.StrongInduction
import ROBINSON_PlusPlus.Full.Numerals
import ROBINSON_PlusPlus.Full.Bounded
import ROBINSON_PlusPlus.Full.Divisibility
import ROBINSON_PlusPlus.Full.Division
import ROBINSON_PlusPlus.Full.Mod2
import ROBINSON_PlusPlus.Full.Primality
import ROBINSON_PlusPlus.Full.PrimeFactor
import ROBINSON_PlusPlus.Full.Factorization
import ROBINSON_PlusPlus.Full.Lists

set_option autoImplicit false

open Lean Elab Command

/-- Para cada meta-regla ω, cuántas declaraciones bajo `root` la arrastran. -/
elab "#omega_load " root:ident : command => do
  let env ← getEnv
  let mods := env.header.moduleNames
  let rootName := root.getId
  let metaRules : List Name :=
    [ `FOL.MetaRules.imp_intro, `FOL.MetaRules.gen, `FOL.MetaRules.raa
    , `FOL.MetaRules.or_elim, `FOL.MetaRules.ex_elim
    , `FOL.MetaRules.dne, `FOL.Theorems.Neg.dne
    , `FOL.Theorems.Quantifiers.forall_not_impl_exists_not ]
  let mut total : Nat := 0
  let mut anyOmega : Nat := 0
  let mut perRule : Std.HashMap Name Nat := {}
  let mut cleanNames : Array Name := #[]
  for (name, _info) in env.constants.toList do
    if name.isInternalDetail then continue
    let some modIdx := env.const2ModIdx[name]? | continue
    unless rootName.isPrefixOf mods[modIdx.toNat]! do continue
    total := total + 1
    let axs ← collectAxioms name
    let mut hit := false
    for r in metaRules do
      if axs.contains r then
        perRule := perRule.insert r (perRule.getD r 0 + 1)
        hit := true
    if hit then anyOmega := anyOmega + 1
    else if cleanNames.size < 10 then cleanNames := cleanNames.push name
  logInfo m!"══ {rootName}: {total} decls · {anyOmega} arrastran alguna meta-regla ω/clásica\n\
    por regla: {perRule.toList}\n\
    ejemplos SIN meta-reglas: {cleanNames.toList}"

#omega_load ROBINSON_PlusPlus

/-- Inventario de `axiom` de Lean bajo un prefijo. -/
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
    if let .axiomInfo _ := info then found := found.push (name, m)
  logInfo m!"══ {found.size} `axiom` bajo {rootName}:
{found.toList}"

/-- Cuántas decls bajo `root` dependen de un axioma concreto. -/
elab "#dependents " ax:ident " under " root:ident : command => do
  let env ← getEnv
  let mods := env.header.moduleNames
  let axName ← resolveGlobalConstNoOverload ax
  let rootName := root.getId
  let mut n : Nat := 0
  for (name, _info) in env.constants.toList do
    if name.isInternalDetail then continue
    let some modIdx := env.const2ModIdx[name]? | continue
    unless rootName.isPrefixOf mods[modIdx.toNat]! do continue
    let axs ← collectAxioms name
    if axs.contains axName then n := n + 1
  logInfo m!"{axName} ← {n} decls bajo {rootName}"

#axioms_of ROBINSON_PlusPlus
#dependents ROBINSON_PlusPlus.Full.ax_induction under ROBINSON_PlusPlus

-- ¿Y los teoremas concretos que un "Peano volcado" necesitaría de verdad?
elab "#fp " id:ident : command => do
  let name ← resolveGlobalConstNoOverload id
  let axs ← collectAxioms name
  logInfo m!"{name} : {axs.toList}"
