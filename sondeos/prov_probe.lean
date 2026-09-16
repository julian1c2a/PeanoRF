-- SONDEO — ¿por qué la procedencia no reconoce a derives0_soundness como dependencia?
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import PeanoRF.Calculus.Soundness
open Lean Elab Command

elab "#diag " id:ident : command => do
  let env ← getEnv
  let mods := env.header.moduleNames
  let n ← resolveGlobalConstNoOverload id
  let modName := match env.const2ModIdx[n]? with
    | some i => mods[i.toNat]!
    | none => `NINGUNO
  let refs := match env.find? n with
    | some info =>
      (info.type.getUsedConstants ++ (match info.value? with | some v => v.getUsedConstants | none => #[]))
    | none => #[]
  logInfo m!"{n}\n  módulo: {modName}\n  ¿value? presente: {(env.find? n).any (fun i => i.value?.isSome)}\n  refs directas: {refs.toList.take 12}"

#diag PeanoRF.Calculus.derivesI_soundness
#diag FOL.Metamath.Soundness0.derives0_soundness
