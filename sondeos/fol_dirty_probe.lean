-- ¿Qué queda con Classical.choice en FOL tras el arreglo de shift_updateEnv_comm?
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import FOL
open Lean Elab Command

elab "#dirty " root:ident : command => do
  let env ← getEnv
  let mods := env.header.moduleNames
  let rootName := root.getId
  let mut byMod : Std.HashMap Name (Array Name) := {}
  let mut total : Nat := 0
  for (name, _info) in env.constants.toList do
    if name.isInternalDetail then continue
    let some i := env.const2ModIdx[name]? | continue
    let m := mods[i.toNat]!
    unless rootName.isPrefixOf m do continue
    let axs ← collectAxioms name
    if axs.contains ``Classical.choice then
      byMod := byMod.insert m ((byMod.getD m #[]).push name)
      total := total + 1
  let rows := byMod.toList.map (fun (m, ns) => s!"  {m} ({ns.size}): {ns.toList}")
  logInfo m!"══ {total} decls con Classical.choice bajo {rootName}\n{String.intercalate "\n" rows}"

#dirty FOL.Theorems
#dirty FOL.Rename
#dirty FOL.Tactics
