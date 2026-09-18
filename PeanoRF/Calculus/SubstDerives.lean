/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.Calculus.Subst
import PeanoRF.Calculus.DerivesI
import FOL.Eigenvariable

/-! # `⊢ᵢ` es cerrado bajo SUSTITUCIÓN PARALELA

  El lema que L2 necesita y que no existe aguas arriba ni podría: **el cálculo es nuestro**.
  Lo que sí se toma prestado es la forma de la prueba: `FOL.Lift0.derives0_lift` hace lo
  mismo para el levantamiento, y este módulo es su hermano con `ρ` en lugar de `k`.

  > `Γ ⊢ᵢ f  ⟹  ∀ ρ, (Γ.map (substF ρ)) ⊢ᵢ substF ρ f`

  ⚠️ **El `∀ ρ` va DENTRO de la inducción**, igual que el `∀ k` de `derives0_lift`: en
  `intro_forall`, `elim_ex` y `rewrite_at` la hipótesis inductiva se usa con **otra**
  sustitución (`upS ρ`, o `upS` iterada tantas veces como ligaduras haya atravesado la
  posición). Sacarlo fuera rompe la prueba, y es exactamente la razón por la que L2 pedía
  sustitución paralela.

  ## Las tres piezas de navegación

  `rewrite_at` reescribe **en una posición** del árbol, y una posición puede meterse bajo
  cuantificadores. Por eso las tres primeras lemas van indexadas por `posDepth p`: a esa
  profundidad, la sustitución que actúa ya no es `ρ` sino `upS` iterada. Es el mismo patrón
  de `FOL.Lift0.lift_getAt?`, con `upSn` donde ellos llevan `k + posDepth p`.
-/

namespace PeanoRF.Calculus

open FOL
open FOL.Eigenvariable   -- `posDepth`

set_option autoImplicit false

/-- `upS` iterada: la sustitución que actúa `n` ligaduras más adentro. -/
def upSn : Nat → Subst → Subst
  | 0,     ρ => ρ
  | n + 1, ρ => upSn n (upS ρ)

/-! ## Navegación: `substF` conmuta con posiciones -/

theorem subst_getAt? : ∀ (p : Pos) (ρ : Subst) (f : Formula),
    getAt? (substF ρ f) p = (getAt? f p).map (substF (upSn (posDepth p) ρ)) := by
  intro p
  induction p with
  | root => intro ρ f; simp [getAt?, posDepth, upSn]
  | left p' ih => intro ρ f; cases f <;> simp only [getAt?, substF, ih, posDepth] <;> rfl
  | right p' ih => intro ρ f; cases f <;> simp only [getAt?, substF, ih, posDepth] <;> rfl
  | body p' ih =>
      intro ρ f
      cases f <;> simp only [getAt?, substF, ih, posDepth, upSn] <;> rfl

theorem subst_replaceAt : ∀ (p : Pos) (ρ : Subst) (f newSub : Formula),
    replaceAt (substF ρ f) p (substF (upSn (posDepth p) ρ) newSub)
      = substF ρ (replaceAt f p newSub) := by
  intro p
  induction p with
  | root => intro ρ f n; simp [replaceAt, posDepth, upSn]
  | left p' ih => intro ρ f n; cases f <;> simp only [replaceAt, substF, ih, posDepth]
  | right p' ih => intro ρ f n; cases f <;> simp only [replaceAt, substF, ih, posDepth]
  | body p' ih =>
      intro ρ f n
      cases f <;> simp only [replaceAt, substF, posDepth, upSn, ih]

theorem subst_localRule (ρ : Subst) {A B : Formula} (h : LocalRule A B) :
    LocalRule (substF ρ A) (substF ρ B) := by
  cases h with
  | commuteImpl A B C =>
      exact LocalRule.commuteImpl (substF ρ A) (substF ρ B) (substF ρ C)

/-! ## Las dos identidades que usan los cuantificadores -/

/-- El contexto levantado de `intro_forall` conmuta con la sustitución. -/
theorem map_subst_lift (ρ : Subst) (Γ : List Formula) :
    (Γ.map (liftFormula 0)).map (substF (upS ρ))
      = (Γ.map (substF ρ)).map (liftFormula 0) := by
  induction Γ with
  | nil => rfl
  | cons g Γ' ih => simp only [List.map_cons, substF_upS_lift, ih]

private theorem compS_singleS_liftS (x : Term) :
    compS (singleS 0 x) (liftS 0) = Term.var := by
  funext k
  simp [compS, liftS, singleS, substT, Nat.not_lt_zero, show k + 1 > 0 by omega]

/-- ⭐ **Sustituir conmuta con instanciar.** Es la identidad de `elim_forall`, `intro_ex`
    y de los dos `subst` de la igualdad. -/
theorem substF_substFormula (ρ : Subst) (t : Term) (f : Formula) :
    substF ρ (substFormula 0 t f) = substFormula 0 (substT ρ t) (substF (upS ρ) f) := by
  have key : compS ρ (singleS 0 t) = compS (singleS 0 (substT ρ t)) (upS ρ) := by
    funext n
    cases n with
    | zero => simp [compS, singleS, upS, substT]
    | succ m =>
        simp only [compS, singleS, upS, show ¬ (m + 1 = 0) by omega,
          show m + 1 > 0 by omega, if_false, if_true, substT]
        rw [← substT_liftS 0 (ρ m), substT_comp, compS_singleS_liftS, substT_var_id]
        congr 1
  rw [← substF_singleS f 0 t, substF_comp, ← substF_singleS _ 0 (substT ρ t),
    substF_comp, key]

/-! ## ⭐⭐ El lema -/

/-- **`⊢ᵢ` es cerrado bajo sustitución paralela.**

    ⚠️ El `∀ ρ` va **dentro**: en `intro_forall`, `elim_ex` y `rewrite_at` la hipótesis
    inductiva se usa con otra sustitución. -/
theorem derivesI_subst {Γ : List Formula} {φ : Formula} (h : Γ ⊢ᵢ φ) :
    ∀ ρ : Subst, (Γ.map (substF ρ)) ⊢ᵢ substF ρ φ := by
  induction h with
  | hyp Γ' f' hIn => intro ρ; exact Derivesᵢ.hyp _ _ (List.mem_map_of_mem hIn)
  | intro_impl Γ' A B _ ih => intro ρ; exact Derivesᵢ.intro_impl _ _ _ (ih ρ)
  | elim_impl Γ' A B _ _ ih1 ih2 => intro ρ; exact Derivesᵢ.elim_impl _ _ _ (ih1 ρ) (ih2 ρ)
  | intro_and Γ' A B _ _ ih1 ih2 => intro ρ; exact Derivesᵢ.intro_and _ _ _ (ih1 ρ) (ih2 ρ)
  | elim_and_l Γ' A B _ ih => intro ρ; exact Derivesᵢ.elim_and_l _ _ _ (ih ρ)
  | elim_and_r Γ' A B _ ih => intro ρ; exact Derivesᵢ.elim_and_r _ _ _ (ih ρ)
  | intro_or_l Γ' A B _ ih => intro ρ; exact Derivesᵢ.intro_or_l _ _ _ (ih ρ)
  | intro_or_r Γ' A B _ ih => intro ρ; exact Derivesᵢ.intro_or_r _ _ _ (ih ρ)
  | elim_or Γ' A B C _ _ _ ih1 ih2 ih3 =>
      intro ρ; exact Derivesᵢ.elim_or _ _ _ _ (ih1 ρ) (ih2 ρ) (ih3 ρ)
  | intro_forall Γ' A _ ih =>
      intro ρ
      refine Derivesᵢ.intro_forall _ _ ?_
      rw [← map_subst_lift ρ Γ']
      exact ih (upS ρ)
  | elim_forall Γ' A t _ ih =>
      intro ρ
      rw [substF_substFormula]
      exact Derivesᵢ.elim_forall _ _ (substT ρ t) (ih ρ)
  | intro_ex Γ' A t _ ih =>
      intro ρ
      refine Derivesᵢ.intro_ex _ (substF (upS ρ) A) (substT ρ t) ?_
      rw [← substF_substFormula]
      exact ih ρ
  | elim_ex Γ' A B _ _ ih1 ih2 =>
      intro ρ
      refine Derivesᵢ.elim_ex _ (substF (upS ρ) A) _ (ih1 ρ) ?_
      have h2 := ih2 (upS ρ)
      rw [List.map_cons, map_subst_lift, substF_upS_lift] at h2
      exact h2
  | bot_elim Γ' A _ ih => intro ρ; exact Derivesᵢ.bot_elim _ _ (ih ρ)
  | weakening Γ' Γ'' f' _ hSub ih =>
      intro ρ
      refine Derivesᵢ.weakening _ _ _ (ih ρ) ?_
      intro x hx
      rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact List.mem_map_of_mem (hSub y hy)
  | rewrite_at Γ' f f' p sub sub' _ hget hrule heq ih =>
      intro ρ
      refine Derivesᵢ.rewrite_at _ (substF ρ f) _ p
        (substF (upSn (posDepth p) ρ) sub) (substF (upSn (posDepth p) ρ) sub')
        (ih ρ) ?_ (subst_localRule _ hrule) ?_
      · rw [subst_getAt?, hget]; rfl
      · rw [heq, ← subst_replaceAt]
  | refl Γ' t => intro ρ; exact Derivesᵢ.refl _ (substT ρ t)
  | subst Γ' t₁ t₂ f _ _ ih1 ih2 =>
      intro ρ
      rw [substF_substFormula]
      refine Derivesᵢ.subst _ (substT ρ t₁) (substT ρ t₂) (substF (upS ρ) f) (ih1 ρ) ?_
      rw [← substF_substFormula]
      exact ih2 ρ


/-! ## ⭐⭐ La regla de Leibniz en un índice CUALQUIERA

    `Derivesᵢ.subst` sustituye sólo en el índice 0, y eso bastaba mientras no hubiera
    cuantificadores por medio: bajo un `∀`, el índice en el que dos sustituciones difieren
    pasa del 0 al 1, y la regla deja de aplicar. Era el último obstáculo de L2.

    🔑 **Y se deriva, no hace falta pedirla.** El truco es aislar la variable `k`:
    se abstrae con `θ`, que manda `k ↦ #0` y levanta todo lo demás, y entonces `substF ρ f`
    es literalmente `(substF θ f)[ρ k / 0]` — con lo que la regla de índice 0 ya vale. Todo
    el trabajo lo hace el álgebra de `Subst.lean`. -/
theorem leibniz_at (T : List Formula) (k : Nat) (f : Formula) (ρ₁ ρ₂ : Subst)
    (hagree : ∀ n, n ≠ k → ρ₁ n = ρ₂ n)
    (heq : T ⊢ᵢ Formula.eq (ρ₁ k) (ρ₂ k))
    (hd : T ⊢ᵢ substF ρ₁ f) :
    T ⊢ᵢ substF ρ₂ f := by
  -- `θ` abstrae la variable `k` al índice 0 y levanta el resto.
  let θ : Subst := fun n => if n = k then Term.var 0 else liftTerm 0 (ρ₁ n)
  have key : ∀ ρ : Subst, (∀ n, n ≠ k → ρ₁ n = ρ n) → compS (singleS 0 (ρ k)) θ = ρ := by
    intro ρ hag
    funext n
    by_cases h : n = k
    · subst h
      show substT (singleS 0 (ρ n)) (if n = n then Term.var 0 else liftTerm 0 (ρ₁ n)) = ρ n
      rw [if_pos rfl]
      show singleS 0 (ρ n) 0 = ρ n
      rfl
    · show substT (singleS 0 (ρ k)) (if n = k then Term.var 0 else liftTerm 0 (ρ₁ n)) = ρ n
      rw [if_neg h, ← substT_liftS 0 (ρ₁ n), substT_comp, compS_singleS_liftS,
        substT_var_id]
      exact hag n h
  have h1 : compS (singleS 0 (ρ₁ k)) θ = ρ₁ := key ρ₁ (fun _ _ => rfl)
  have h2 : compS (singleS 0 (ρ₂ k)) θ = ρ₂ := key ρ₂ hagree
  have e1 : substFormula 0 (ρ₁ k) (substF θ f) = substF ρ₁ f := by
    rw [← substF_singleS _ 0 (ρ₁ k), substF_comp, h1]
  have e2 : substFormula 0 (ρ₂ k) (substF θ f) = substF ρ₂ f := by
    rw [← substF_singleS _ 0 (ρ₂ k), substF_comp, h2]
  rw [← e2]
  exact Derivesᵢ.subst T (ρ₁ k) (ρ₂ k) (substF θ f) heq (by rw [e1]; exact hd)

end PeanoRF.Calculus
