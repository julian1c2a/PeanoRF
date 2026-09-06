-- SONDEO — ¿es TODO Peano constructivo? Acota el alcance de "volcar Peano al completo".
--   lake env lean sondeos/peano_probe.lean
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Peano

set_option autoImplicit false
open Lean Elab Command

private def allowed : List Name := [``propext, ``Quot.sound]

elab "#peano_scan" : command => do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut total : Nat := 0
  let mut clean : Nat := 0
  let mut offenders : Std.HashMap Name Nat := {}
  let mut dirtyMods : Std.HashMap Name Nat := {}
  for (name, _info) in env.constants.toList do
    if name.isInternalDetail then continue
    let some modIdx := env.const2ModIdx[name]? | continue
    let m := mods[modIdx.toNat]!
    unless (`Peano).isPrefixOf m do continue
    total := Nat.add total 1
    let axs ← collectAxioms name
    let bad := axs.filter (fun a => !allowed.contains a)
    if bad.isEmpty then clean := Nat.add clean 1
    else
      dirtyMods := dirtyMods.insert m (Nat.add (dirtyMods.getD m 0) 1)
      for a in bad do offenders := offenders.insert a (Nat.add (offenders.getD a 0) 1)
  logInfo m!"══ Peano COMPLETO: {total} decls · {clean} limpias · {Nat.sub total clean} sucias\n\
    ofensores: {offenders.toList}\n\
    módulos afectados: {dirtyMods.toList}"

#peano_scan
