import Lake
open Lake DSL

-- PeanoRF — aritmética de Peano construida sobre ROBINSON_PlusPlus y FOL.
-- El nombre del paquete NO puede coincidir con el del directorio
-- (`Peano-from-ROB-n-FOL` lleva guiones, que no son identificadores Lean válidos).
package «PeanoRF» where
  -- Disable auto-implicit to enforce explicit type annotations everywhere
  moreServerArgs := #["-DautoImplicit=false"]

-- ── Dependencias externas (proyectos sibling locales) ────────────────────────
--
-- ⚠️ Las tres son rutas LOCALES, no `from git`: se trabaja contra el árbol de
--    trabajo real de cada proyecto, no contra su último push. Las tres deben estar
--    en el mismo toolchain que este proyecto (hoy v4.31.0).
--
-- ⚠️ FOL se compila SIEMPRE desde el proyecto que lo requiere (aquí, o ROBINSON_PlusPlus),
--    nunca con `cd ../FOL && lake build`.

-- FOL: lógica de primer orden con igualdad.
-- Provee: Term, Formula, Derives (⊢), sustitución, reglas de igualdad, tácticas.
require FOL from "../FOL"

-- ROBINSON_PlusPlus: aritmética de Robinson Q extendida + aritmetización/Gödel.
-- Requiere FOL a su vez, desde la misma ruta `../FOL` (Lake deduplica).
require ROBINSON_PlusPlus from "../ROBINSON_PlusPlus"

-- peanolib: los naturales ℕ₀ de Peano (el paquete se llama `peanolib`; su lib, `Peano`).
require peanolib from "../Peano"

-- ─────────────────────────────────────────────────────────────────────────────

@[default_target]
lean_lib «PeanoRF» where
