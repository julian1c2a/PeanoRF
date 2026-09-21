/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.Calculus.Eq
import ROBINSON_PlusPlus.Full.Induction

/-! # HA — el conjunto de axiomas, y la generalización finitaria

  **H2 del roadmap.** Axiomatiza HA sobre Q⁺⁺ **sin postular derivabilidad** (M-8) y
  demuestra la pieza que hace innecesaria la ω-regla.

  ⚠️ **Migrado a `⊢ᵢ` el 2026-09-16** (ADR-017). La primera versión vivía sobre
  `FOL.Derives`, que aguas arriba resultó ser HERRAMIENTA y no SUJETO: *cualquier* testigo
  de su solidez da `False` (`FOL/cuarentena/Inconsistencia.lean`). Sobre aquel cálculo
  `zero_add` era una derivación correcta de la que **no se podía concluir nada sobre ℕ₀**,
  y ahí moría el espejo. Ver `PeanoRF/Calculus/DerivesI.lean`.

  ## El problema que resuelve

  `ROBINSON_PlusPlus/Full/Induction.lean` declaraba `ax_induction` postulando que la
  inducción es **derivable del conjunto de axiomas de Q⁺⁺** — falso bajo un `⊢` finitario.
  (Desde 2026-09-10 el axioma se llama `ax_induction_prim` y está sobre `primAxioms`, pero
  sigue siendo un axioma postulado.) Aquí la inducción **no se postula: se pone en el
  contexto**, que es donde viven los axiomas de una teoría (ADR-016).

  ## La convención: contextos finitos

  `ctx insts = coreAxioms ++ insts.map inductionFormula`. Cada teorema declara **qué instancias
  de inducción usa**, y eso queda registrado en su tipo — contabilidad al estilo de
  matemática inversa: se lee si un resultado necesitó IΔ₀, IΣ₁ o HA completa.

  ## 🔑 El resultado central: `gen_closed`

  **Sobre un contexto CERRADO, la generalización es finitaria.** `Derivesᵢ.intro_forall`
  pide `Γ.map (liftFormula 0) ⊢ᵢ A`; si `Γ` es cerrado, `Γ.map (liftFormula 0) = Γ` y basta
  `Γ ⊢ᵢ A`. La hipótesis se cumple por CÓMPUTO DEL KERNEL: `axioms_lift` es un `rfl`.
-/

/-! ### ⚠️ Por qué `coreAxioms` y no `axioms` (cambiado el 2026-09-18)

  `ROBINSON_PlusPlus.Minimal.Axioms.axioms` tiene **109 constituyentes**, y cinco de ellos
  —`ax_vpf_ind`, `ax_vpf_listInd`, `ax_tc_zero`, `ax_tc_succ`, `ax_lineWF_listInd`—
  arrastran `Classical.choice`. La causa, medida por el agente de RPP: `strCodeM s :=
  charsCodeM s.toList`, y la puerta es **`String.toList`**; `charsCodeM` sobre `List Char`
  es net-0. Es deuda de implementación del núcleo, no matemática.

  ⭐ `coreAxioms` **no depende de ningún axioma** (medido), y contiene los 33 axiomas
  aritméticos y de listas de Q⁺⁺ — incluidos los seis que este proyecto usa.

  🔑 **Y el cambio no es un truco de footprint: es una corrección.** Los cinco sucios son
  axiomas sobre el **verificador object de demostraciones** (la maquinaria de Gödel de RPP).
  Tenían tan poco que hacer en el contexto de la Aritmética de Heyting como en el de
  cualquier otra teoría aritmética: `ctx` los arrastraba por usar la lista grande, no
  porque HA los necesitara. HA es `coreAxioms` más la inducción, y ahora lo dice.

  ⇒ Toda la capa HA pasa a `[propext, Quot.sound]`. La deuda META heredada, que había
  llegado a 14 declaraciones, **se queda en 0**.
-/

namespace PeanoRF.HA

open FOL
open PeanoRF.Calculus
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Full (inductionFormula)

set_option maxRecDepth 100000

/-! ### El contexto de HA -/

/-- **El conjunto de axiomas de HA**: los de Q⁺⁺ más las instancias del esquema de
    inducción que el teorema declare usar. Finito por construcción — eso es lo que hace de
    HA una teoría r.e. y no ω-lógica. -/
def ctx (insts : List Formula) : List Formula :=
  coreAxioms ++ insts.map inductionFormula

/-- Los axiomas de Q⁺⁺ están en todo contexto de HA. -/
theorem mem_ctx_of_mem_axioms {insts : List Formula} {f : Formula}
    (h : f ∈ coreAxioms) : f ∈ ctx insts :=
  List.mem_append_left _ h

/-- Un axioma de Q⁺⁺ es derivable **intuicionistamente** en cualquier contexto de HA. -/
theorem ax' {insts : List Formula} {f : Formula} (h : f ∈ coreAxioms) : ctx insts ⊢ᵢ f :=
  Derivesᵢ.hyp _ f (mem_ctx_of_mem_axioms h)

/-- **La instancia de inducción es una HIPÓTESIS, no un axioma de Lean.** -/
theorem ind {insts : List Formula} {φ : Formula} (h : φ ∈ insts) :
    ctx insts ⊢ᵢ inductionFormula φ :=
  Derivesᵢ.hyp _ _ (List.mem_append_right _ (List.mem_map_of_mem h))

/-- Monotonía en las instancias.

    🏁 **ENTREGABLE**: parte de la API de `ctx`. Nada del árbol la usa todavía porque
    todos los teoremas fijan sus instancias de una vez. -/
theorem mono {insts insts' : List Formula} {ψ : Formula}
    (hsub : insts ⊆ insts') (h : ctx insts ⊢ᵢ ψ) : ctx insts' ⊢ᵢ ψ := by
  refine Derivesᵢ.weakening _ _ _ h ?_
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact mem_ctx_of_mem_axioms hx
  · obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hx
    exact List.mem_append_right _ (List.mem_map_of_mem (hsub hφ))

/-! ### El FRAGMENTO ARITMÉTICO

    ⛔ Vive aquí y no en `HA/Fragment.lean` por una razón de orden: los homomorfismos de
    numerales (`HA/Numerals.lean`) tienen que poder hablar de él, y `Numerals` va antes.
    Las **mediciones** que lo justifican sí están en `Fragment`. -/

/-- Los 17 axiomas de `coreAxioms` cuyos símbolos de función son sólo `0`, `σ`, `+`, `*`, `^`.
    Medidos, no elegidos: `sondeos/fragmento_probe.lean`. -/
def arithAxioms : List Formula :=
  [ax2_peano_succ_neq_zero, ax3_peano_succ_inj, ax4_add_zero, ax5_add_succ,
   ax6_add_comm, ax7_add_assoc, ax8_mul_zero, ax9_mul_succ,
   ax10_mul_comm, ax11_mul_assoc, ax12_mul_distrib, ax13_lt_def,
   ax18_lt_irrefl, ax19_lt_trichotomy, ax_L1_in_nil, ax_pow_zero, ax_pow_succ]

/-- El fragmento es parte de Q⁺⁺: todo lo suyo es derivable donde lo sea `coreAxioms`.

    🏗️ **ANDAMIO**: sin uso hoy; es la pieza por la que entra el fragmento cuando se
    construya su DP. -/
theorem arithAxioms_sub : ∀ g, List.Mem g arithAxioms → List.Mem g coreAxioms := by
  intro g hg
  simp only [arithAxioms] at hg
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.head _
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.head _)
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))
  cases hg


/-! ### Generalización finitaria — el sustituto de la ω-regla -/

/-- Los axiomas de Q⁺⁺ son **sentencias cerradas**: `liftFormula 0` los deja igual.
    Se demuestra por cómputo del kernel sobre la lista concreta. -/
theorem axioms_lift : coreAxioms.map (liftFormula 0) = coreAxioms := by rfl

/-- Si las instancias declaradas son cerradas, el contexto entero lo es. -/
theorem ctx_lift {insts : List Formula}
    (h : (insts.map inductionFormula).map (liftFormula 0) = insts.map inductionFormula) :
    (ctx insts).map (liftFormula 0) = ctx insts := by
  unfold ctx
  rw [List.map_append, axioms_lift, h]

/-- **Generalización FINITARIA.** Sobre un contexto cerrado, de `Γ ⊢ᵢ A` se concluye
    `Γ ⊢ᵢ ∀A` usando sólo el constructor `Derivesᵢ.intro_forall`.

    Es el sustituto de la ω-regla (hoy `Derives.gen_rule`, un **constructor** de `⊢`, que
    por eso el footprint no ve): lo que la ω obtiene de infinitas premisas `Γ ⊢ A[n]`, esto
    lo obtiene de una sola prueba uniforme con la variable libre. -/
theorem gen_closed {Γ : List Formula} {A : Formula}
    (hclosed : Γ.map (liftFormula 0) = Γ) (h : Γ ⊢ᵢ A) : Γ ⊢ᵢ Formula.forall A :=
  Derivesᵢ.intro_forall Γ A (by rw [hclosed]; exact h)

/-! ### Parámetros cerrados — lo que cuesta el caso con parámetro

  `gen_closed` exige el contexto cerrado. Si la instancia de inducción lleva un **parámetro**
  `a`, el contexto sólo es cerrado cuando `a` lo es — y «cerrado» aquí significa invariante
  bajo lift **a todo nivel** y bajo sustitución, no sólo `liftTerm 0 a = a`.

  Medido (`sondeos/param_probe.lean`, 2026-09-16): con `liftTerm 0 a = a` **no basta** —
  quedan pendientes las invariancias de nivel 1, porque `inductionFormula` usa
  `liftFormula 1 φ`. Con las dos condiciones de abajo, sale. -/

/-- Término **cerrado**: invariante bajo lift a cualquier nivel y bajo cualquier sustitución.
    Es la hipótesis exacta que pide la generalización finitaria con parámetro. -/
structure Closed (a : Term) : Prop where
  lift  : ∀ k, liftTerm k a = a
  subst : ∀ k t, substTerm k t a = a

/-- `zero` es cerrado. (El caso `a := zero` sale además por `rfl` directo.)

    🏗️ **ANDAMIO**: el testigo más simple de `Closed`, para quien instancie `succ_add`
    y compañía con un parámetro concreto. -/
theorem closed_zero : Closed zero := ⟨fun _ => rfl, fun _ _ => rfl⟩

/-! ### Inducción object-level, finitaria -/

/-- **Inducción sobre `φ`**, con la instancia tomada del contexto. -/
theorem induction_object {insts : List Formula} {φ : Formula} (hmem : φ ∈ insts)
    (base : ctx insts ⊢ᵢ substFormula 0 zero φ)
    (step : ctx insts ⊢ᵢ Formula.forall
              (Formula.impl φ (substFormula 0 (succ (.var 0)) (liftFormula 1 φ)))) :
    ctx insts ⊢ᵢ Formula.forall φ := by
  have hind := ind hmem
  simp only [inductionFormula] at hind
  exact Derivesᵢ.elim_impl _ _ _ (Derivesᵢ.elim_impl _ _ _ hind base) step

end PeanoRF.HA
