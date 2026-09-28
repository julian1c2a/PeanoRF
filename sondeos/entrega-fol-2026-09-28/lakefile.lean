import Lake
open Lake DSL

-- Sondeo PRF: los siete de PeanoRF/Calculus contra FOL SOLO. Sin RPP, sin Peano.
package «FOLSpike» where
  moreServerArgs := #["-DautoImplicit=false"]

require FOL from "../../../FOL"

@[default_target]
lean_lib «Spike» where
  globs := #[.submodules `Spike]
