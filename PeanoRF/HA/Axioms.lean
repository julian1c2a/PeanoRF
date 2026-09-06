/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.Prelim
import ROBINSON_PlusPlus.Full.Induction

/-! # HA — el conjunto de axiomas, y la generalización finitaria

  **H2 del roadmap.** Aquí se axiomatiza HA sobre Q⁺⁺ **sin postular derivabilidad**
  (MANDATORY M-8) y se demuestra la pieza que hace innecesaria la ω-regla.

  ## El problema que resuelve

  `ROBINSON_PlusPlus/Full/Induction.lean` declara

  ```lean
  axiom ax_induction (φ : Formula) : axioms ⊢ inductionFormula φ
  ```

  que postula que la inducción es **derivable del conjunto de axiomas de Q⁺⁺**. Bajo un
  `⊢` finitario eso es falso: Q no demuestra inducción. Aquí la inducción **no se postula:
  se pone en el contexto**, que es donde viven los axiomas de una teoría (ADR-016).

  ## La convención: contextos finitos

  `ctx insts = axioms ++ insts.map inductionFormula`. Cada teorema declara **qué instancias
  de inducción usa**, y eso queda registrado en su tipo. No es burocracia: es contabilidad
  al estilo de matemática inversa — se puede leer si un resultado necesitó IΔ₀, IΣ₁ o HA
  completa sin más que mirar `insts`.

  ## 🔑 El resultado central: `gen_closed`

  **Sobre un contexto CERRADO, la generalización es finitaria.** `Derives.intro_forall`
  pide `Γ.map (liftFormula 0) ⊢ A`; si `Γ` es cerrado, `Γ.map (liftFormula 0) = Γ` y basta
  `Γ ⊢ A`. Es decir: **la ω-regla `gen` no hace falta** para este uso.

  Y la hipótesis se cumple por CÓMPUTO DEL KERNEL: `axioms_lift` es un `rfl` (los axiomas
  de Q⁺⁺ son sentencias cerradas), y para cada instancia concreta también.

  Ésa es la medida real del coste de prescindir de la ω en este frente: **cero**.
-/

namespace PeanoRF.HA

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Full (inductionFormula)

set_option maxRecDepth 100000

/-! ### El contexto de HA -/

/-- **El conjunto de axiomas de HA**: los de Q⁺⁺ más las instancias del esquema de
    inducción que el teorema declare usar.

    `insts` es la lista de fórmulas `φ` (con `#0` libre) cuyas instancias de inducción
    entran en el contexto. Es finita **por construcción**: cada derivación usa finitas
    instancias, que es justo lo que hace de HA una teoría r.e. y no ω-lógica. -/
def ctx (insts : List Formula) : List Formula :=
  axioms ++ insts.map inductionFormula

/-- Los axiomas de Q⁺⁺ están en todo contexto de HA. -/
theorem mem_ctx_of_mem_axioms {insts : List Formula} {f : Formula}
    (h : f ∈ axioms) : f ∈ ctx insts :=
  List.mem_append_left _ h

/-- Un axioma de Q⁺⁺ es derivable en cualquier contexto de HA. Análogo finitario de
    `Minimal.Axioms.ax`, que estaba clavado al contexto `axioms`. -/
theorem ax' {insts : List Formula} {f : Formula} (h : f ∈ axioms) : ctx insts ⊢ f :=
  Derives.hyp _ f (mem_ctx_of_mem_axioms h)

/-- **La instancia de inducción es una HIPÓTESIS, no un axioma de Lean.**
    Compárese con `ROBINSON_PlusPlus.Full.ax_induction`, que la postula. -/
theorem ind {insts : List Formula} {φ : Formula} (h : φ ∈ insts) :
    ctx insts ⊢ inductionFormula φ :=
  Derives.hyp _ _ (List.mem_append_right _ (List.mem_map_of_mem h))

/-- Monotonía: ampliar la lista de instancias conserva lo derivado. Permite componer
    teoremas que declararon instancias distintas. -/
theorem mono {insts insts' : List Formula} {ψ : Formula}
    (hsub : insts ⊆ insts') (h : ctx insts ⊢ ψ) : ctx insts' ⊢ ψ := by
  refine Derives.weakening _ _ _ h ?_
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact mem_ctx_of_mem_axioms hx
  · obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hx
    exact List.mem_append_right _ (List.mem_map_of_mem (hsub hφ))

/-! ### Generalización finitaria — el sustituto de la ω-regla -/

/-- Los axiomas de Q⁺⁺ son **sentencias cerradas**: `liftFormula 0` los deja igual.
    Se demuestra por cómputo del kernel sobre la lista concreta. -/
theorem axioms_lift : axioms.map (liftFormula 0) = axioms := by rfl

/-- Si las instancias de inducción declaradas son cerradas, el contexto entero lo es. -/
theorem ctx_lift {insts : List Formula}
    (h : (insts.map inductionFormula).map (liftFormula 0) = insts.map inductionFormula) :
    (ctx insts).map (liftFormula 0) = ctx insts := by
  unfold ctx
  rw [List.map_append, axioms_lift, h]

/-- **Generalización FINITARIA.** Sobre un contexto cerrado, de `Γ ⊢ A` se concluye
    `Γ ⊢ ∀A` usando sólo el constructor `Derives.intro_forall`.

    Es el sustituto de la ω-regla `FOL.MetaRules.gen` (prohibida por M-7), y muestra que
    para este uso la ω **no aportaba nada**: lo que `gen` obtiene de infinitas premisas
    `Γ ⊢ A[n]`, esto lo obtiene de una sola prueba uniforme con la variable libre. -/
theorem gen_closed {Γ : List Formula} {A : Formula}
    (hclosed : Γ.map (liftFormula 0) = Γ) (h : Γ ⊢ A) : Γ ⊢ Formula.forall A :=
  Derives.intro_forall Γ A (by rw [hclosed]; exact h)

/-! ### Inducción object-level, finitaria

  Mismo empaquetado que `ROBINSON_PlusPlus.Full.induction_object`, pero la fórmula de
  inducción sale del CONTEXTO (`ind`) en vez de un `axiom` de Lean. -/

/-- **Inducción sobre `φ`**, con la instancia tomada del contexto. -/
theorem induction_object {insts : List Formula} {φ : Formula} (hmem : φ ∈ insts)
    (base : ctx insts ⊢ substFormula 0 zero φ)
    (step : ctx insts ⊢ Formula.forall
              (Formula.impl φ (substFormula 0 (succ (.var 0)) (liftFormula 1 φ)))) :
    ctx insts ⊢ Formula.forall φ := by
  have hind := ind hmem
  simp only [inductionFormula] at hind
  exact Derives.elim_impl _ _ _ (Derives.elim_impl _ _ _ hind base) step

end PeanoRF.HA
