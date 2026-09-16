/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.Calculus.DerivesI
import FOL.Semantics

/-! # H3 · Solidez de `⊢ᵢ` — el espejo hecho teorema

  **El teorema de transferencia.** De `Γ ⊢ᵢ f` se sigue que `f` es válida: verdadera en
  **todo** modelo de `Γ`, y en particular en el estándar. Es el enunciado que convierte
  «espejo» en un hecho matemático, y el que `FOL.Derives` **no podía tener** (ADR-017):
  cualquier testigo de su solidez da `False`.

  ## ⛔ La conjetura de ADR-019 era FALSA, y la medición localiza el obstáculo real

  La primera versión heredaba la solidez componiendo con `derives0_soundness`, y con ella
  `Classical.choice`. La conjetura era que ese `Classical` fuese **exactamente** el precio
  de los tres constructores clásicos de `⊢₀`, y que una inducción directa sobre nuestros 18
  saliera limpia.

  **Se probó la inducción directa, y NO sale limpia.** Medido (`sondeos/h3b_probe.lean`):

  | símbolo | footprint |
  |---|---|
  | `evalTerm`, `evalFormula`, `rule_soundness` | **ninguno** |
  | `replaceAt_soundness` | `propext` |
  | **`contextSatisfies_lift_zero`** | `propext, Classical.choice, Quot.sound` |
  | **`eval_substFormula_zero`** | `propext, Classical.choice, Quot.sound` |
  | **`eval_liftFormula_zero`** | `propext, Classical.choice, Quot.sound` |

  ⇒ 🔑 **El `Classical` no viene de las reglas clásicas: viene de los tres lemas de
  LEVANTAMIENTO Y SUSTITUCIÓN de la semántica.** Quitar `dne_rule` y compañía es
  **necesario pero no suficiente**.

  ## ⭐ Por qué esta prueba vale igualmente, y mucho

  Los tres lemas culpables son hechos **puramente combinatorios** sobre índices de De Bruijn
  y evaluación — no hay nada clásico en su contenido. Todo apunta a un `Classical` **oculto**
  del tipo que documenta `AI-GUIDE` §27: un `by_cases` sobre una comparación de `Nat` sin
  instancia `Decidable` a la vista.

  ⇒ Esta prueba es **constructive-ready**: el día que esos tres lemas se saneen —aquí o
  aguas arriba— `derivesI_soundness` pasa a `⊆ {propext, Quot.sound}` **sin tocar una línea
  de este fichero**. Y ya no depende de `Soundness0`, así que el obstáculo está reducido de
  «toda la solidez de `⊢₀`» a **tres lemas con nombre**.

  ## Procedencia de la prueba

  Los 18 casos son los de `FOL/Soundness0.lean`, que a su vez los rescató de
  `FOL/cuarentena/Soundness.lean`. Ninguno cambia de contenido: cada regla de deducción
  natural intuicionista es semánticamente válida sin ayuda clásica. Lo único que cambia es
  **el tipo sobre el que se induce** — que es, dicho por el autor de aguas arriba, la
  lección de M-11:

  > *«Cuando un teorema cae por M-11, su demostración suele estar bien: lo que hay que
  > cambiar es el sujeto.»*

  ## ⚠️ Nota sobre M-5 (ADR-019)

  Este módulo importa `FOL.Semantics`, que M-5 prohibía en bloque. La prohibición se enmendó
  **con una medición**: `satisfies` no tiene footprint; lo clásico estaba en la *prueba* de
  `Soundness0`, no en la semántica. Y este módulo ya no importa `Soundness0`.
-/

namespace PeanoRF.Calculus

open FOL
open FOL.Metamath.Semantics

set_option autoImplicit false

local notation:50 Γ " ⊨ " f => FOL.Metamath.Semantics.satisfies Γ f

/-- **Solidez de `⊢ᵢ`**: lo intuicionistamente derivable es válido.

    Inducción sobre los **18** constructores — legítima porque `Derivesᵢ` **no tiene
    habitantes-axioma** (M-11). Ningún CASO usa lógica clásica; el `Classical.choice` del
    footprint entra por tres lemas de la semántica (ver el encabezado del módulo). -/
theorem derivesI_soundness {Γ : List Formula} {f : Formula} (h : Γ ⊢ᵢ f) : Γ ⊨ f := by
  induction h with
  | hyp Γ' f' hIn =>
    intro D M v hΓ
    exact hΓ f' hIn
  | intro_impl Γ' A B _ ih =>
    intro D M v hΓ hA
    apply ih D M v
    intro f' hf'
    cases hf' with
    | head _ => exact hA
    | tail _ hTail => exact hΓ f' hTail
  | elim_impl Γ' A B _ _ ih_impl ih_A =>
    intro D M v hΓ
    exact (ih_impl D M v hΓ) (ih_A D M v hΓ)
  | intro_and Γ' A B _ _ ihA ihB =>
    intro D M v hΓ
    exact ⟨ihA D M v hΓ, ihB D M v hΓ⟩
  | elim_and_l Γ' A B _ ih =>
    intro D M v hΓ
    exact (ih D M v hΓ).left
  | elim_and_r Γ' A B _ ih =>
    intro D M v hΓ
    exact (ih D M v hΓ).right
  | intro_or_l Γ' A B _ ih =>
    intro D M v hΓ
    exact Or.inl (ih D M v hΓ)
  | intro_or_r Γ' A B _ ih =>
    intro D M v hΓ
    exact Or.inr (ih D M v hΓ)
  | elim_or Γ' A B C _ _ _ ih_or ih_A ih_B =>
    intro D M v hΓ
    cases ih_or D M v hΓ with
    | inl hA =>
      apply ih_A D M v
      intro f' hf'
      cases hf' with
      | head _ => exact hA
      | tail _ hTail => exact hΓ f' hTail
    | inr hB =>
      apply ih_B D M v
      intro f' hf'
      cases hf' with
      | head _ => exact hB
      | tail _ hTail => exact hΓ f' hTail
  | intro_forall Γ' A _ ih =>
    intro D M v hΓ d
    have hCtx : contextSatisfies M (shiftEnv v d) (Γ'.map (liftFormula 0)) :=
      (contextSatisfies_lift_zero M v d).mpr hΓ
    exact ih D M (shiftEnv v d) hCtx
  | elim_forall Γ' A t _ ih =>
    intro D M v hΓ
    have hForall := ih D M v hΓ
    have hEval := hForall (evalTerm M v t)
    exact (eval_substFormula_zero M v t A).mpr hEval
  | intro_ex Γ' A t _ ih =>
    intro D M v hΓ
    have hA := ih D M v hΓ
    have hEval := (eval_substFormula_zero M v t A).mp hA
    exact ⟨evalTerm M v t, hEval⟩
  | elim_ex Γ' A B _ _ ih_ex ih_B =>
    intro D M v hΓ
    have hEx := ih_ex D M v hΓ
    obtain ⟨d, hd⟩ := hEx
    have hCtx : contextSatisfies M (shiftEnv v d) (A :: Γ'.map (liftFormula 0)) := by
      intro f' hf'
      cases hf' with
      | head _ => exact hd
      | tail _ hTail => exact (contextSatisfies_lift_zero M v d).mpr hΓ f' hTail
    have hB := ih_B D M (shiftEnv v d) hCtx
    exact (eval_liftFormula_zero M v d B).mp hB
  -- ⚠️ `bot_elim` es *ex falso*, INTUICIONISTA. No confundir con la doble negación: de una
  -- contradicción se sigue todo sin ayuda clásica ninguna.
  | bot_elim Γ' A _ ih =>
    intro D M v hΓ
    have hBot := ih D M v hΓ
    contradiction
  | weakening Γ' Γ'' f' _ hSubset ih =>
    intro D M v hΓ
    apply ih D M v
    intro g hg
    exact hΓ g (hSubset g hg)
  | rewrite_at Γ' f' f'' p sub sub' _ h_get h_rule h_replace ih =>
    intro D M v hΓ
    have hEvalF := ih D M v hΓ
    have hSubEq : ∀ v', evalFormula M v' sub ↔ evalFormula M v' sub' :=
      fun v' => rule_soundness M h_rule v'
    have hEquiv := replaceAt_soundness M v h_get hSubEq
    rw [h_replace]
    exact hEquiv.mp hEvalF
  | refl Γ' t =>
    intro D M v _
    rfl
  | subst Γ' t1 t2 f' _ _ ih_eq ih_f =>
    intro D M v hΓ
    have heq := ih_eq D M v hΓ
    have hf := ih_f D M v hΓ
    have h1 := (eval_substFormula_zero M v t1 f').mp hf
    have heq_eval : evalTerm M v t1 = evalTerm M v t2 := heq
    rw [heq_eval] at h1
    exact (eval_substFormula_zero M v t2 f').mpr h1

/-- **Consistencia de `⊢ᵢ`**: no se deriva `⊥` sin hipótesis.

    Primer corolario de la solidez, y el que justifica todo lo demás: si `[] ⊢ᵢ ⊥`, `⊥`
    sería verdadera en cualquier modelo, y basta exhibir uno. -/
theorem derivesI_consistent (h : ([] : List Formula) ⊢ᵢ Formula.bottom) : False := by
  have hv := derivesI_soundness h
  exact hv Unit ⟨fun _ _ => (), fun _ _ => True⟩ (fun _ => ())
    (fun _ hf => absurd hf (List.not_mem_nil))

end PeanoRF.Calculus
