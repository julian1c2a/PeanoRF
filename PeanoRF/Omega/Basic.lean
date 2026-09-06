/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.Prelim

/-! # La capa ω — declarada, aislada y contable

  **Todo lo que viva bajo `PeanoRF.Omega.*` está fuera del núcleo finitario** (M-7,
  ADR-016). El gate `PeanoRF/Meta/AxiomCheck.lean` permite aquí las ω-reglas de FOL y los
  meta-axiomas de ROBINSON_PlusPlus, y las **cuenta** en cada build; en cualquier otro
  módulo son error.

  ## Por qué existe esta capa en vez de prohibir la ω sin más

  ROB++ usa ω-reglas en 99 de sus 521 declaraciones (19 %, medido 2026-09-06). Prohibirlas
  del todo tiraría por la borda buena parte de `Full/`. La capa permite **reusar ese
  trabajo sabiendo exactamente lo que cuesta**: cada resultado que pase por aquí queda
  marcado como perteneciente a ω-lógica y no a HA.

  ## Qué se pierde al cruzar esta frontera

  En ω-lógica `⊢` **no es recursivamente enumerable**: no hay checker posible para una
  regla con infinitas premisas. Un teorema de esta capa:

  * **sirve** para el espejo hacia Peano (ω-lógica es sólida para ℕ);
  * **no sirve** como contenido fundacional (donde `⊢` = verdad en ℕ no hay teoría, hay
    modelo) ni como pieza del meta-lenguaje (ADR-016 §3).

  ## ⚠️ La regla que NUNCA debe cruzarse

  **No demostrar soundness de `Derives` hacia ℕ₀ para derivaciones que usen `raa` o
  `imp_intro`.** Sus premisas son meta (`Γ ⊢ A → Γ ⊢ B`) y se cumplen VACÍAMENTE cuando la
  premisa no es derivable: con un testigo de no-derivabilidad `¬(axioms ⊢ ψ)` para ψ
  verdadera, `raa` da `axioms ⊢ ¬ψ` y soundness lo convierte en `¬⟦ψ⟧`. La soundness se
  demuestra **sólo del fragmento finitario** (ADR-016 §2).

  ## Puntos de entrada sancionados

  Las ω-reglas se usan **a través de estos alias**, no directamente: así toda dependencia
  de la capa ω es visible en el nombre y el gate la contabiliza.
-/

namespace PeanoRF.Omega

open FOL

/-- ω-regla de generalización: de `∀ n : Term, Γ ⊢ A[n]` concluye `Γ ⊢ ∀A`.
    **Infinitaria.** El sustituto finitario es `Derives.intro_forall`. -/
abbrev gen := @FOL.MetaRules.gen

/-- Introducción de `⇒` con premisa META. El sustituto finitario es
    `Derives.intro_impl` (hipótesis en contexto). ⚠️ Premisa vacuamente satisfacible. -/
abbrev imp_intro := @FOL.MetaRules.imp_intro

/-- Introducción de `¬` con premisa META. Intuicionista, pero infinitaria en su
    justificación. Sustituto finitario: `Derives.intro_impl` sobre `¬A = A ⇒ ⊥`.
    ⚠️ Premisa vacuamente satisfacible. -/
abbrev raa := @FOL.MetaRules.raa

/-- Eliminación de `∨` con premisas META. Sustituto finitario: `Derives.elim_or`. -/
abbrev or_elim := @FOL.MetaRules.or_elim

/-- Eliminación de `∃` con premisas META. Sustituto finitario: `Derives.elim_ex`. -/
abbrev ex_elim := @FOL.MetaRules.ex_elim

end PeanoRF.Omega
