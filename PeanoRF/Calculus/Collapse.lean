/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.Calculus.DerivesI

/-! # El COLAPSO de símbolos ajenos — `⊢ᵢ` es cerrado bajo él

  **El obstáculo que este módulo retira.** `Term` de FOL es genérica: `Term.func s ts` admite
  cualquier `s : String`, mientras que el lenguaje de Q⁺⁺ tiene cinco símbolos. Y
  `elim_forall` instancia con **cualquier** término. Medido el 2026-09-18
  (`sondeos/junk_probe.lean`):

  ```lean
  ctx [] ⊢ᵢ (lt foo bar ∨ foo = bar ∨ lt bar foo)     -- foo, bar ajenos al lenguaje
  ```

  y ninguna rama es derivable ⇒ **HA sobre la sintaxis genérica no tiene la propiedad de
  disyunción**. El teorema de Kleene es sobre SU lenguaje.

  ## La salida: transformar la derivación, no restringirla

  La ruta cara era un cálculo paralelo `DerivesL` con su puente. La barata es ésta:

  > `derivesI_collapse : Γ ⊢ᵢ f → Γ.map (collapseF L) ⊢ᵢ collapseF L f`

  `collapseT L` manda a `zero` todo símbolo fuera de la signatura `L` y **no toca las
  variables**. En `elim_forall`, una instanciación con basura pasa a ser una con
  `collapseT L t`, que sí es del lenguaje; y `collapseF L` **deja fijos** los axiomas de
  `coreAxioms` y cualquier fórmula del lenguaje.

  ⇒ De una derivación que usa símbolos ajenos sale otra que no los usa, con el mismo contexto
  y la misma conclusión.

  ## Dos decisiones, y las dos se midieron antes de escribir

  * **Parametrizado por la signatura** `L : String → Bool`, no clavado a Q⁺⁺: las
    conmutaciones no dependen de qué símbolos se conserven. Lo único que se usa del
    reemplazo es que sea **cerrado** — `zero` no tiene argumentos, luego lift y subst lo
    dejan igual por `rfl`.
  * **Los predicados ajenos NO se colapsan**, y es deliberado: la barra de un átomo es su
    derivabilidad, sin testigo. El obstáculo eran los **términos**.

  ## Por qué sale más barato que `derivesI_subst`

  Porque **el colapso no cambia al entrar bajo una ligadura**: `collapseF L (∀a)` es
  `∀ (collapseF L a)`, con la misma `L`. La sustitución, en cambio, pasa a `upS ρ`, y por eso
  su versión de la navegación de `rewrite_at` va indexada por `posDepth` y ésta no.

  ⚠️ No depende de FOL. Su ADR-065 mide que el puente a `LKp` **no tiene camino barato**
  («parametrizar `Hauptsatz0`… un módulo de 1 256 l., ESTIMADO alto»), así que esperar a que
  la interpolación de Craig diera la eliminación de símbolos ajenos era mala apuesta.
-/

namespace PeanoRF.Calculus

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms

set_option autoImplicit false

/-! ## El colapso -/

mutual
/-- Todo símbolo fuera de la signatura `L` colapsa a `zero`. Las variables no se tocan — y
    eso es lo que hace que conmute con la sustitución. -/
def collapseT (L : String → Bool) : Term → Term
  | .var n     => .var n
  | .func s ts => if L s then .func s (collapseTs L ts) else zero

def collapseTs (L : String → Bool) : List Term → List Term
  | []      => []
  | t :: ts => collapseT L t :: collapseTs L ts
end

/-- En las fórmulas sólo se colapsan los TÉRMINOS. Un predicado ajeno no da problema: la
    barra de un átomo es su derivabilidad, sin testigo. -/
def collapseF (L : String → Bool) : Formula → Formula
  | .bottom    => .bottom
  | .atom p ts => .atom p (collapseTs L ts)
  | .eq t u    => .eq (collapseT L t) (collapseT L u)
  | .impl a b  => .impl (collapseF L a) (collapseF L b)
  | .forall a  => .forall (collapseF L a)
  | .and a b   => .and (collapseF L a) (collapseF L b)
  | .or a b    => .or (collapseF L a) (collapseF L b)
  | .ex a      => .ex (collapseF L a)

/-! ## 1 · Conmuta con el levantamiento -/

mutual
theorem collapseT_lift (L : String → Bool) : ∀ (c : Nat) (t : Term),
    collapseT L (liftTerm c t) = liftTerm c (collapseT L t) := by
  intro c t
  cases t with
  | var n => by_cases h : n < c <;> simp [collapseT, liftTerm, h]
  | func s ts =>
      by_cases h : L s
      · simp only [liftTerm, collapseT, if_pos h]
        exact congrArg _ (collapseTs_lift L c ts)
      · simp [liftTerm, collapseT, if_neg h, zero, liftTerms]

theorem collapseTs_lift (L : String → Bool) : ∀ (c : Nat) (ts : List Term),
    collapseTs L (liftTerms c ts) = liftTerms c (collapseTs L ts) := by
  intro c ts
  cases ts with
  | nil => rfl
  | cons t ts' =>
      simp only [liftTerms, collapseTs, List.cons.injEq]
      exact ⟨collapseT_lift L c t, collapseTs_lift L c ts'⟩
end

theorem collapseF_lift (L : String → Bool) : ∀ (f : Formula) (c : Nat),
    collapseF L (liftFormula c f) = liftFormula c (collapseF L f) := by
  intro f
  induction f with
  | bottom => intro _; rfl
  | atom p ts => intro c; simp only [liftFormula, collapseF, collapseTs_lift]
  | eq t u => intro c; simp only [liftFormula, collapseF, collapseT_lift]
  | impl a b iha ihb => intro c; simp only [liftFormula, collapseF, iha, ihb]
  | and a b iha ihb => intro c; simp only [liftFormula, collapseF, iha, ihb]
  | or a b iha ihb => intro c; simp only [liftFormula, collapseF, iha, ihb]
  | «forall» a ih => intro c; simp only [liftFormula, collapseF, ih]
  | ex a ih => intro c; simp only [liftFormula, collapseF, ih]

/-! ## 2 · Conmuta con la sustitución -/

mutual
theorem collapseT_subst (L : String → Bool) : ∀ (v : Nat) (s t : Term),
    collapseT L (substTerm v s t) = substTerm v (collapseT L s) (collapseT L t) := by
  intro v s t
  cases t with
  | var n =>
      by_cases h1 : n = v
      · simp [collapseT, substTerm, h1]
      · by_cases h2 : n > v <;> simp [collapseT, substTerm, h1, h2]
  | func c ts =>
      by_cases h : L c
      · simp only [substTerm, collapseT, if_pos h]
        exact congrArg _ (collapseTs_subst L v s ts)
      · simp [substTerm, collapseT, if_neg h, zero, substTerms]

theorem collapseTs_subst (L : String → Bool) : ∀ (v : Nat) (s : Term) (ts : List Term),
    collapseTs L (substTerms v s ts) = substTerms v (collapseT L s) (collapseTs L ts) := by
  intro v s ts
  cases ts with
  | nil => rfl
  | cons t ts' =>
      simp only [substTerms, collapseTs, List.cons.injEq]
      exact ⟨collapseT_subst L v s t, collapseTs_subst L v s ts'⟩
end

/-- ⭐ El caso `∀`/`∃` es el que podía fallar: ahí la sustitución entra bajo la ligadura como
    `substFormula (v+1) (liftTerm 0 s)`, y hace falta la conmutación del levantamiento. -/
theorem collapseF_subst (L : String → Bool) : ∀ (f : Formula) (v : Nat) (s : Term),
    collapseF L (substFormula v s f) = substFormula v (collapseT L s) (collapseF L f) := by
  intro f
  induction f with
  | bottom => intro _ _; rfl
  | atom p ts => intro v s; simp only [substFormula, collapseF, collapseTs_subst]
  | eq t u => intro v s; simp only [substFormula, collapseF, collapseT_subst]
  | impl a b iha ihb => intro v s; simp only [substFormula, collapseF, iha, ihb]
  | and a b iha ihb => intro v s; simp only [substFormula, collapseF, iha, ihb]
  | or a b iha ihb => intro v s; simp only [substFormula, collapseF, iha, ihb]
  | «forall» a ih => intro v s; simp only [substFormula, collapseF, ih, collapseT_lift]
  | ex a ih => intro v s; simp only [substFormula, collapseF, ih, collapseT_lift]

/-! ## 3 · Navegación — y aquí se nota que el colapso no cambia bajo la ligadura

    Compárese con `subst_getAt?`/`subst_replaceAt` en `SubstDerives.lean`, que van indexadas
    por `posDepth p` porque la sustitución sí cambia al entrar en un cuantificador. Aquí no
    hace falta índice ninguno. -/

theorem collapse_getAt? (L : String → Bool) : ∀ (p : Pos) (f : Formula),
    getAt? (collapseF L f) p = (getAt? f p).map (collapseF L) := by
  intro p
  induction p with
  | root => intro f; simp [getAt?]
  | left p' ih => intro f; cases f <;> simp only [getAt?, collapseF, ih] <;> rfl
  | right p' ih => intro f; cases f <;> simp only [getAt?, collapseF, ih] <;> rfl
  | body p' ih => intro f; cases f <;> simp only [getAt?, collapseF, ih] <;> rfl

theorem collapse_replaceAt (L : String → Bool) : ∀ (p : Pos) (f newSub : Formula),
    replaceAt (collapseF L f) p (collapseF L newSub) = collapseF L (replaceAt f p newSub) := by
  intro p
  induction p with
  | root => intro f n; simp [replaceAt]
  | left p' ih => intro f n; cases f <;> simp only [replaceAt, collapseF, ih]
  | right p' ih => intro f n; cases f <;> simp only [replaceAt, collapseF, ih]
  | body p' ih => intro f n; cases f <;> simp only [replaceAt, collapseF, ih]

theorem collapse_localRule (L : String → Bool) {A B : Formula} (h : LocalRule A B) :
    LocalRule (collapseF L A) (collapseF L B) := by
  cases h with
  | commuteImpl A B C =>
      exact LocalRule.commuteImpl (collapseF L A) (collapseF L B) (collapseF L C)

theorem map_collapse_lift (L : String → Bool) (Γ : List Formula) :
    (Γ.map (liftFormula 0)).map (collapseF L) = (Γ.map (collapseF L)).map (liftFormula 0) := by
  induction Γ with
  | nil => rfl
  | cons g Γ' ih => simp only [List.map_cons, collapseF_lift, ih]

/-! ## 4 · ⭐⭐ El lema -/

/-- **`⊢ᵢ` es cerrado bajo el colapso de símbolos ajenos.**

    De una derivación que instancia con símbolos fuera de la signatura `L` sale otra que no
    lo hace, con el mismo contexto colapsado y la misma conclusión colapsada.

    ⚠️ A diferencia de `derivesI_subst`, la signatura **no cambia** a lo largo de la
    inducción: el colapso atraviesa las ligaduras sin transformarse. Por eso aquí no hay
    `∀ L` dentro ni navegación indexada por profundidad. -/
theorem derivesI_collapse (L : String → Bool) {Γ : List Formula} {φ : Formula}
    (h : Γ ⊢ᵢ φ) : (Γ.map (collapseF L)) ⊢ᵢ collapseF L φ := by
  induction h with
  | hyp Γ' f' hIn => exact Derivesᵢ.hyp _ _ (List.mem_map_of_mem hIn)
  | intro_impl Γ' A B _ ih => exact Derivesᵢ.intro_impl _ _ _ ih
  | elim_impl Γ' A B _ _ ih1 ih2 => exact Derivesᵢ.elim_impl _ _ _ ih1 ih2
  | intro_and Γ' A B _ _ ih1 ih2 => exact Derivesᵢ.intro_and _ _ _ ih1 ih2
  | elim_and_l Γ' A B _ ih => exact Derivesᵢ.elim_and_l _ _ _ ih
  | elim_and_r Γ' A B _ ih => exact Derivesᵢ.elim_and_r _ _ _ ih
  | intro_or_l Γ' A B _ ih => exact Derivesᵢ.intro_or_l _ _ _ ih
  | intro_or_r Γ' A B _ ih => exact Derivesᵢ.intro_or_r _ _ _ ih
  | elim_or Γ' A B C _ _ _ ih1 ih2 ih3 => exact Derivesᵢ.elim_or _ _ _ _ ih1 ih2 ih3
  | intro_forall Γ' A _ ih =>
      refine Derivesᵢ.intro_forall _ _ ?_
      rw [← map_collapse_lift]
      exact ih
  | elim_forall Γ' A t _ ih =>
      rw [collapseF_subst]
      exact Derivesᵢ.elim_forall _ _ (collapseT L t) ih
  | intro_ex Γ' A t _ ih =>
      refine Derivesᵢ.intro_ex _ (collapseF L A) (collapseT L t) ?_
      rw [← collapseF_subst]
      exact ih
  | elim_ex Γ' A B _ _ ih1 ih2 =>
      refine Derivesᵢ.elim_ex _ (collapseF L A) _ ih1 ?_
      rw [List.map_cons, map_collapse_lift, collapseF_lift] at ih2
      exact ih2
  | bot_elim Γ' A _ ih => exact Derivesᵢ.bot_elim _ _ ih
  | weakening Γ' Γ'' f' _ hSub ih =>
      refine Derivesᵢ.weakening _ _ _ ih ?_
      intro x hx
      rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact List.mem_map_of_mem (hSub y hy)
  | rewrite_at Γ' f f' p sub sub' _ hget hrule heq ih =>
      refine Derivesᵢ.rewrite_at _ (collapseF L f) _ p
        (collapseF L sub) (collapseF L sub') ih ?_ (collapse_localRule L hrule) ?_
      · rw [collapse_getAt?, hget]; rfl
      · rw [heq, ← collapse_replaceAt]
  | refl Γ' t => exact Derivesᵢ.refl _ (collapseT L t)
  | subst Γ' t₁ t₂ f _ _ ih1 ih2 =>
      rw [collapseF_subst]
      refine Derivesᵢ.subst _ (collapseT L t₁) (collapseT L t₂) (collapseF L f) ih1 ?_
      rw [← collapseF_subst]
      exact ih2

end PeanoRF.Calculus
