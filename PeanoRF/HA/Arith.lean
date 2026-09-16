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
  | `MetaRules.gen` (ω-regla) | `HA.gen_closed` (`Derivesᵢ.intro_forall` + contexto cerrado) |
  | `MetaRules.imp_intro` (premisa meta) | `Derivesᵢ.intro_impl` (hipótesis en contexto) |
  | `Minimal.Axioms.ax` (clavado a `axioms`) | `HA.ax'` (cualquier contexto de HA) |
  | `FOL.Derives` (HERRAMIENTA, sin solidez posible) | **`⊢ᵢ`** (SUJETO: 0 axiomas habitantes, intuicionista) |

  El resto de la prueba —`specI`, `eqI_congr_succ`, `eqI_trans`— hubo que **reprobarlo en
  `⊢ᵢ`** (`PeanoRF/Calculus/Eq.lean`): aguas arriba existe, pero enunciado sobre `⊢`, y los
  teoremas de `⊢` no bajan a `⊢ᵢ` — sólo suben. Son tres lemas, y las pruebas son las
  mismas con los constructores renombrados.

  ## El coste medido

  La estructura de la prueba es la MISMA. Lo único que cambia es que el paso de inducción
  se hace con la variable `#0` libre en vez de con un término arbitrario `n`, y que la
  hipótesis de inducción entra por el contexto en vez de por una función meta. **No hubo
  que reformular ninguna matemática.** Ver `NEXT-STEPS.md` H2 para la lectura de esto.
-/

namespace PeanoRF.HA

open FOL
open PeanoRF.Calculus
open ROBINSON_PlusPlus.Minimal.Axioms

set_option maxRecDepth 100000

/-- `φ(x) ≡ 0 + x = x`, con `#0` libre. -/
def phiZeroAdd : Formula := add zero (.var 0) =eq (.var 0)

/-- **`∀x. 0 + x = x` en HA, por vía finitaria.**

    Declara en su tipo la única instancia de inducción que usa: `[phiZeroAdd]`. Esa lista
    es la contabilidad de matemática inversa que ADR-016 pretendía — se lee del enunciado
    qué hizo falta. -/
theorem zero_add : ctx [phiZeroAdd] ⊢ᵢ Formula.forall phiZeroAdd := by
  -- La instancia de inducción sale del CONTEXTO, no de un `axiom` de Lean.
  refine induction_object (List.mem_singleton_self _) ?base ?step
  case base =>
    -- `φ(0)` es `0 + 0 = 0`, que es `ax4_add_zero` especializado en `0`.
    show ctx [phiZeroAdd] ⊢ᵢ (add zero zero =eq zero)
    have h4 : ctx [phiZeroAdd] ⊢ᵢ ax4_add_zero := ax' (by simp [axioms])
    have h := specI h4 zero
    simp [substFormula, substTerm, substTerms, add, zero] at h
    exact h
  case step =>
    -- Generalización FINITARIA: el contexto es cerrado, luego basta probar el cuerpo
    -- con `#0` libre. Aquí es donde `MetaRules.gen` resultaba innecesaria.
    refine gen_closed (by rfl) ?_
    -- Implicación FINITARIA: la hipótesis de inducción entra en el contexto.
    refine Derivesᵢ.intro_impl _ _ _ ?_
    -- Contexto extendido con la hipótesis de inducción.
    have wk : ∀ {ψ : Formula}, ctx [phiZeroAdd] ⊢ᵢ ψ →
        (phiZeroAdd :: ctx [phiZeroAdd]) ⊢ᵢ ψ := fun {ψ} h =>
      Derivesᵢ.weakening (ctx [phiZeroAdd]) (phiZeroAdd :: ctx [phiZeroAdd]) ψ h
        (fun _ hx => List.mem_cons_of_mem _ hx)
    -- La hipótesis de inducción: `0 + #0 = #0`.
    have hn : (phiZeroAdd :: ctx [phiZeroAdd]) ⊢ᵢ (add zero (.var 0) =eq (.var 0)) :=
      Derivesᵢ.hyp _ _ (by simp [phiZeroAdd])
    -- Meta: `0 + σ#0 = σ#0`.
    show (phiZeroAdd :: ctx [phiZeroAdd]) ⊢ᵢ (add zero (succ (.var 0)) =eq succ (.var 0))
    -- `ax5_add_succ` especializado: `0 + σ#0 = σ(0 + #0)`.
    have h5 : (phiZeroAdd :: ctx [phiZeroAdd]) ⊢ᵢ
        (add zero (succ (.var 0)) =eq succ (add zero (.var 0))) := by
      have h5' : ctx [phiZeroAdd] ⊢ᵢ ax5_add_succ := ax' (by simp [axioms])
      have hh := wk (specI (specI h5' zero) (.var 0))
      simp [substFormula, substTerm, substTerms, add, succ, zero,
            FOL.substTerm_liftTerm] at hh
      exact hh
    exact eqI_trans h5 (eqI_congr_succ hn)

/-! ### `succ_add` — el caso CON PARÁMETRO

  `∀x. σa + x = σ(a + x)`, con `a` un término **parámetro**. Es el caso que `zero_add` no
  medía: ahí no había parámetro libre, y por eso la ω-regla no aportaba nada.
-/

/-- `φₐ(x) ≡ σa + x = σ(a + x)`, con `#0` libre y el parámetro `a` levantado. -/
def phiSuccAdd (a : Term) : Formula :=
  add (succ (liftTerm 0 a)) (.var 0) =eq succ (add (liftTerm 0 a) (.var 0))

/-- **`∀x. σa + x = σ(a+x)` en HA, por vía finitaria.**

    ⚠️ **Con hipótesis `Closed a`**, y ésa es la medición que faltaba. El parámetro **sí**
    cuesta, y el precio está localizado: la generalización finitaria exige contexto cerrado,
    y con un parámetro el contexto sólo lo es si el parámetro lo es. `liftTerm 0 a = a` **no
    basta** — hacen falta las invariancias a todo nivel y bajo sustitución, porque
    `inductionFormula` usa `liftFormula 1 φ`. Con un parámetro ABIERTO no hay generalización
    finitaria: habría que meter en el contexto la **clausura universal** de la instancia. -/
theorem succ_add (a : Term) (hc : Closed a) :
    ctx [phiSuccAdd a] ⊢ᵢ Formula.forall (phiSuccAdd a) := by
  refine induction_object (List.mem_singleton_self _) ?base ?step
  case base =>
    show ctx [phiSuccAdd a] ⊢ᵢ substFormula 0 zero (phiSuccAdd a)
    simp only [phiSuccAdd, substFormula, substTerm, substTerms, add, succ, zero,
      FOL.substTerm_liftTerm]
    have h4 : ctx [phiSuccAdd a] ⊢ᵢ ax4_add_zero := ax' (by simp [axioms])
    have hA : ctx [phiSuccAdd a] ⊢ᵢ (add (succ a) zero =eq succ a) := by
      have hh := specI h4 (succ a)
      simp [substFormula, substTerm, substTerms, add, zero, succ] at hh
      exact hh
    have hB : ctx [phiSuccAdd a] ⊢ᵢ (add a zero =eq a) := by
      have hh := specI h4 a
      simp [substFormula, substTerm, substTerms, add, zero] at hh
      exact hh
    exact eqI_trans hA (eqI_symm (eqI_congr_succ hB))
  case step =>
    refine gen_closed (ctx_lift (by simp [phiSuccAdd, ROBINSON_PlusPlus.Full.inductionFormula,
      substFormula, substTerm, substTerms, liftFormula, liftTerm, liftTerms, add, succ, zero,
      hc.lift, hc.subst])) ?_
    refine Derivesᵢ.intro_impl _ _ _ ?_
    have wk : ∀ {ψ : Formula}, ctx [phiSuccAdd a] ⊢ᵢ ψ →
        (phiSuccAdd a :: ctx [phiSuccAdd a]) ⊢ᵢ ψ := fun {ψ} h =>
      Derivesᵢ.weakening (ctx [phiSuccAdd a]) (phiSuccAdd a :: ctx [phiSuccAdd a]) ψ h
        (fun _ hx => List.mem_cons_of_mem _ hx)
    have ih : (phiSuccAdd a :: ctx [phiSuccAdd a]) ⊢ᵢ
        (add (succ a) (.var 0) =eq succ (add a (.var 0))) := by
      have h := Derivesᵢ.hyp (phiSuccAdd a :: ctx [phiSuccAdd a]) (phiSuccAdd a) (by simp)
      simpa [phiSuccAdd, hc.lift, hc.subst] using h
    -- ⚠️ El objetivo se reduce APARTE, no con `simp only` sobre la meta: desplegar
    -- `add`/`succ` a `Term.func` deja la meta en una forma que ya no casa con los lemas
    -- de igualdad, que hablan de `add`/`succ`.
    have goal_eq : substFormula 0 (succ (.var 0)) (liftFormula 1 (phiSuccAdd a))
        = (add (succ a) (succ (.var 0)) =eq succ (add a (succ (.var 0)))) := by
      simp [phiSuccAdd, substFormula, substTerm, substTerms, liftFormula, liftTerm,
        liftTerms, add, succ, hc.lift, hc.subst, FOL.substTerm_liftTerm]
    show (phiSuccAdd a :: ctx [phiSuccAdd a]) ⊢ᵢ
      substFormula 0 (succ (.var 0)) (liftFormula 1 (phiSuccAdd a))
    rw [goal_eq]
    have h5' : ctx [phiSuccAdd a] ⊢ᵢ ax5_add_succ := ax' (by simp [axioms])
    have h5sa : (phiSuccAdd a :: ctx [phiSuccAdd a]) ⊢ᵢ
        (add (succ a) (succ (.var 0)) =eq succ (add (succ a) (.var 0))) := by
      have hh := wk (specI (specI h5' (succ a)) (.var 0))
      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
      exact hh
    have h5a : (phiSuccAdd a :: ctx [phiSuccAdd a]) ⊢ᵢ
        (add a (succ (.var 0)) =eq succ (add a (.var 0))) := by
      have hh := wk (specI (specI h5' a) (.var 0))
      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
      exact hh
    exact eqI_trans (eqI_trans h5sa (eqI_congr_succ ih)) (eqI_symm (eqI_congr_succ h5a))

end PeanoRF.HA
