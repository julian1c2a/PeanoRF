/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.HA.Axioms

/-! # Primer teorema de HA por vía FINITARIA

  `zero_add` (`∀x. 0 + x = x`) reprobado **sin ω-reglas y sin `ax_induction`**, para medir
  el coste real de la disciplina de ADR-016.

  ## Qué se sustituye

  | En `ROBINSON_PlusPlus.Full.Induction` | Aquí |
  |---|---|
  | `axiom ax_induction : axioms ⊢ inductionFormula φ` | `HA.ind`: la instancia está **en el contexto** |
  | `MetaRules.gen` (ω-regla) | `HA.gen_closed` (`Derives.intro_forall` + contexto cerrado) |
  | `MetaRules.imp_intro` (premisa meta) | `Derives.intro_impl` (hipótesis en contexto) |
  | `Minimal.Axioms.ax` (clavado a `axioms`) | `HA.ax'` (cualquier contexto de HA) |

  El resto de la prueba —`spec`, `eq_congr_succ`, `derive_eq_trans`— ya era finitario y se
  reutiliza **sin cambios**: son genéricos en `Γ`.

  ## El coste medido

  La estructura de la prueba es la MISMA. Lo único que cambia es que el paso de inducción
  se hace con la variable `#0` libre en vez de con un término arbitrario `n`, y que la
  hipótesis de inducción entra por el contexto en vez de por una función meta. **No hubo
  que reformular ninguna matemática.** Ver `NEXT-STEPS.md` H2 para la lectura de esto.
-/

namespace PeanoRF.HA

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms

set_option maxRecDepth 100000

/-- `φ(x) ≡ 0 + x = x`, con `#0` libre. -/
def phiZeroAdd : Formula := add zero (.var 0) =eq (.var 0)

/-- **`∀x. 0 + x = x` en HA, por vía finitaria.**

    Declara en su tipo la única instancia de inducción que usa: `[phiZeroAdd]`. Esa lista
    es la contabilidad de matemática inversa que ADR-016 pretendía — se lee del enunciado
    qué hizo falta. -/
theorem zero_add : ctx [phiZeroAdd] ⊢ Formula.forall phiZeroAdd := by
  -- La instancia de inducción sale del CONTEXTO, no de un `axiom` de Lean.
  refine induction_object (List.mem_singleton_self _) ?base ?step
  case base =>
    -- `φ(0)` es `0 + 0 = 0`, que es `ax4_add_zero` especializado en `0`.
    show ctx [phiZeroAdd] ⊢ (add zero zero =eq zero)
    have h4 : ctx [phiZeroAdd] ⊢ ax4_add_zero := ax' (by simp [axioms])
    have h := spec h4 zero
    simp [substFormula, substTerm, substTerms, add, zero] at h
    exact h
  case step =>
    -- Generalización FINITARIA: el contexto es cerrado, luego basta probar el cuerpo
    -- con `#0` libre. Aquí es donde `MetaRules.gen` resultaba innecesaria.
    refine gen_closed (by rfl) ?_
    -- Implicación FINITARIA: la hipótesis de inducción entra en el contexto.
    refine Derives.intro_impl _ _ _ ?_
    -- Contexto extendido con la hipótesis de inducción.
    have wk : ∀ {ψ : Formula}, ctx [phiZeroAdd] ⊢ ψ →
        (phiZeroAdd :: ctx [phiZeroAdd]) ⊢ ψ := fun {ψ} h =>
      Derives.weakening (ctx [phiZeroAdd]) (phiZeroAdd :: ctx [phiZeroAdd]) ψ h
        (fun _ hx => List.mem_cons_of_mem _ hx)
    -- La hipótesis de inducción: `0 + #0 = #0`.
    have hn : (phiZeroAdd :: ctx [phiZeroAdd]) ⊢ (add zero (.var 0) =eq (.var 0)) :=
      Derives.hyp _ _ (by simp [phiZeroAdd])
    -- Meta: `0 + σ#0 = σ#0`.
    show (phiZeroAdd :: ctx [phiZeroAdd]) ⊢ (add zero (succ (.var 0)) =eq succ (.var 0))
    -- `ax5_add_succ` especializado: `0 + σ#0 = σ(0 + #0)`.
    have h5 : (phiZeroAdd :: ctx [phiZeroAdd]) ⊢
        (add zero (succ (.var 0)) =eq succ (add zero (.var 0))) := by
      have h5' : ctx [phiZeroAdd] ⊢ ax5_add_succ := ax' (by simp [axioms])
      have hh := wk (spec (spec h5' zero) (.var 0))
      simp [substFormula, substTerm, substTerms, add, succ, zero,
            FOL.substTerm_liftTerm] at hh
      exact hh
    exact FOL.derive_eq_trans h5 (eq_congr_succ hn)

end PeanoRF.HA
