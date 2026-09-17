/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.Calculus.Consistency

/-! # H3bis · La BARRA DE KLEENE — hacia la propiedad de disyunción

  **Por qué este módulo es el que falta.** PeanoRF tiene hoy 22 teoremas propios y
  **ninguno falla clásicamente**: todos valen palabra por palabra para `⊢₀`, porque sólo
  usan los 18 constructores que los dos cálculos comparten. Si alguien sustituyera `⊢ᵢ`
  por `⊢₀` en todo el proyecto, **todo seguiría compilando**. La tesis —«PeanoRF es HA y
  no PA»— es hasta ahora arquitectónica: la sostienen la elección de cálculo y el gate,
  no un teorema.

  La **propiedad de disyunción** es el primer enunciado que rompe esa simetría:

  > `[] ⊢ᵢ A ∨ B  ⟹  [] ⊢ᵢ A  ó  [] ⊢ᵢ B`

  `⊢₀` **no la tiene**: prueba `P ∨ ¬P` sin probar ninguna de las dos ramas. Con ella y con
  `notP_syn` (`Consistency.lean`) sale la separación `⊢ᵢ ≠ ⊢₀` como teorema.

  ## El método: la barra

  `Slash f` («la teoría vacía barra `f`») se define por recursión en la COMPLEJIDAD de `f`,
  no en su estructura: el caso `∀` baja a `substFormula 0 t a`, que no es subtérmino de
  `∀a`. De ahí `fdepth` y `fdepth_subst`.

  Una vez definida, la propiedad de disyunción es inmediata de dos lemas:

  | lema | enunciado | estado |
  |---|---|---|
  | **L1** `slash_derives` | `Slash f → [] ⊢ᵢ f` | ✅ aquí |
  | **L2** `slash_of_derives` | `Γ ⊢ᵢ f` y `Γ` barrado ⟹ `Slash f` | ⏳ ver §L2 |

  ## ⚠️ §L2 — lo que falta, y cuál es EXACTAMENTE el obstáculo

  L2 es una inducción sobre la derivación, y con el enunciado ingenuo **dos casos no
  cierran**:

  * `intro_forall`: de `Γ.map (lift 0) ⊢ᵢ A` hay que sacar `∀t, Slash (A[t])`. La
    derivación de `A[t]` existe (`intro_forall` y luego `elim_forall`), pero **no es una
    subderivación**: la hipótesis de inducción no la alcanza.
  * `elim_ex`: el testigo `t` que da la barra hay que meterlo en la segunda premisa, y otra
    vez la derivación resultante no es subderivación.

  El primer diagnóstico fue «hace falta indexar por ALTURA, como `LKh` en el Hauptsatz».
  **Es falso**, y desarrollar los casos lo deja claro. Lo que hace falta es **generalizar
  el enunciado sobre SUSTITUCIONES**:

  > `Γ ⊢ᵢ f ⟹ ∀ σ cerrante, (∀ g ∈ Γ, Slash (gσ)) → Slash (fσ)`

  Con esa forma, el caso `intro_forall` se cierra **con la misma inducción estructural**:
  la meta es `∀t, Slash (A[σ⁺][0↦t])`, que es `Slash (A(t·σ))`, o sea la hipótesis de
  inducción de la premisa **con otra sustitución** — y la HI está cuantificada sobre todas.
  No hacen falta alturas.

  ⇒ El prerrequisito real es la **SUSTITUCIÓN PARALELA** sobre la sintaxis:
  `substT : (Nat → Term) → Term → Term` y su versión para fórmulas, con el álgebra
  habitual (`up`, composición, y la compatibilidad con `liftFormula`/`substFormula`, que
  son las que aparecen en las reglas de `⊢ᵢ`).

  ⚠️ **Medido el 2026-09-17: FOL no la tiene.** Sólo hay sustitución de UNA variable
  (`substFormula`, `substTerms`) y `liftN`. Y es infraestructura de SINTAXIS, o sea suya y
  no nuestra (ADR-010): reimplementarla aquí sería duplicar el núcleo del lenguaje. Va como
  **encargo a FOL**, no como parche.

  Lo que sí es nuestro, y viene después: el lema de que `⊢ᵢ` es cerrado bajo sustitución,
  y L2.

  ## ⚠️ Segundo encargo a FOL, menor

  Bajar `formulaComplexity` y `complexity_substFormula` de `FOL/Canonical0.lean` a un
  módulo base: hoy viven detrás de la cadena clásica de completitud
  (`Canonical0 → Soundness0`), que M-5/ADR-019 mantiene fuera de nuestro import surface.
  Por eso `fdepth` está **duplicado** aquí — deuda declarada, no descuido (M-4).
-/

namespace PeanoRF.Calculus

open FOL

set_option autoImplicit false

/-! ## La complejidad lógica de una fórmula -/

/-- Complejidad lógica: cuántos conectivos y cuantificadores hay que atravesar.

    ⚠️ **Duplica `FOL.Canonical0.formulaComplexity`**, y es deuda declarada, no descuido:
    el original vive detrás de la cadena clásica de completitud. Ver el encabezado. -/
def fdepth : Formula → Nat
  | .bottom    => 0
  | .atom _ _  => 0
  | .eq _ _    => 0
  | .impl a b  => max (fdepth a) (fdepth b) + 1
  | .and a b   => max (fdepth a) (fdepth b) + 1
  | .or a b    => max (fdepth a) (fdepth b) + 1
  | .forall a  => fdepth a + 1
  | .ex a      => fdepth a + 1

/-- 🔑 **Sustituir no cambia la complejidad.** Sin esto la barra no está bien definida: su
    caso `∀` baja a `substFormula 0 t a`, que no es subtérmino de `∀a`. -/
@[simp] theorem fdepth_subst (v : Nat) (t : Term) (f : Formula) :
    fdepth (substFormula v t f) = fdepth f := by
  induction f generalizing v t with
  | bottom => rfl
  | atom _ _ => rfl
  | eq _ _ => rfl
  | impl _ _ ih1 ih2 => simp only [fdepth, substFormula, ih1, ih2]
  | and _ _ ih1 ih2 => simp only [fdepth, substFormula, ih1, ih2]
  | or _ _ ih1 ih2 => simp only [fdepth, substFormula, ih1, ih2]
  | «forall» _ ih => simp only [fdepth, substFormula, ih]
  | ex _ ih => simp only [fdepth, substFormula, ih]

/-! ## La barra -/

/-- **La barra de Kleene sobre la teoría vacía.**

    Léase `Slash f` como «`f` es demostrable *y además* lo es por la razón correcta»: una
    disyunción barrada tiene una rama barrada, un existencial barrado tiene un testigo. Es
    justo lo que una prueba clásica de `P ∨ ¬P` no puede dar. -/
def Slash : Formula → Prop
  | .bottom     => False
  | .atom p ts  => ([] : List Formula) ⊢ᵢ Formula.atom p ts
  | .eq t u     => ([] : List Formula) ⊢ᵢ Formula.eq t u
  | .and a b    => Slash a ∧ Slash b
  | .or a b     => Slash a ∨ Slash b
  | .impl a b   => (([] : List Formula) ⊢ᵢ Formula.impl a b) ∧ (Slash a → Slash b)
  | .forall a   => (([] : List Formula) ⊢ᵢ Formula.forall a) ∧
                     ∀ t : Term, Slash (substFormula 0 t a)
  | .ex a       => ∃ t : Term, Slash (substFormula 0 t a)
termination_by f => fdepth f
decreasing_by
  all_goals simp only [fdepth, fdepth_subst]
  all_goals omega

/-! ### Las ecuaciones de la barra

    `Slash` se define por recursión BIEN FUNDADA (en `fdepth`), así que **no reduce
    definicionalmente**: `Slash (.and a b)` no es juzgacionalmente `Slash a ∧ Slash b`. Hay
    que desplegarla con sus ecuaciones, y por eso van aquí una a una. -/

@[simp] theorem slash_bottom : Slash Formula.bottom ↔ False := by rw [Slash]

@[simp] theorem slash_atom (p : String) (ts : List Term) :
    Slash (Formula.atom p ts) ↔ (([] : List Formula) ⊢ᵢ Formula.atom p ts) := by rw [Slash]

@[simp] theorem slash_eq (t u : Term) :
    Slash (Formula.eq t u) ↔ (([] : List Formula) ⊢ᵢ Formula.eq t u) := by rw [Slash]

@[simp] theorem slash_and (a b : Formula) :
    Slash (Formula.and a b) ↔ (Slash a ∧ Slash b) := by rw [Slash]

@[simp] theorem slash_or (a b : Formula) :
    Slash (Formula.or a b) ↔ (Slash a ∨ Slash b) := by rw [Slash]

@[simp] theorem slash_impl (a b : Formula) :
    Slash (Formula.impl a b) ↔
      ((([] : List Formula) ⊢ᵢ Formula.impl a b) ∧ (Slash a → Slash b)) := by rw [Slash]

@[simp] theorem slash_forall (a : Formula) :
    Slash (Formula.forall a) ↔
      ((([] : List Formula) ⊢ᵢ Formula.forall a) ∧
        ∀ t : Term, Slash (substFormula 0 t a)) := by rw [Slash]

@[simp] theorem slash_ex (a : Formula) :
    Slash (Formula.ex a) ↔ ∃ t : Term, Slash (substFormula 0 t a) := by rw [Slash]

/-! ## L1 · lo barrado es derivable -/

/-- **L1.** La barra implica la derivabilidad. Los casos `∧`, `∨` y `∃` recurren, y por eso
    esta prueba también va por complejidad. -/
theorem slash_derives : ∀ f : Formula, Slash f → (([] : List Formula) ⊢ᵢ f)
  | .bottom,   h => (slash_bottom.mp h).elim
  | .atom _ _, h => (slash_atom _ _).mp h
  | .eq _ _,   h => (slash_eq _ _).mp h
  | .impl a b, h => ((slash_impl a b).mp h).1
  | .forall a, h => ((slash_forall a).mp h).1
  | .and a b,  h =>
      Derivesᵢ.intro_and _ a b
        (slash_derives a ((slash_and a b).mp h).1)
        (slash_derives b ((slash_and a b).mp h).2)
  | .or a b,   h =>
      match (slash_or a b).mp h with
      | Or.inl ha => Derivesᵢ.intro_or_l _ a b (slash_derives a ha)
      | Or.inr hb => Derivesᵢ.intro_or_r _ a b (slash_derives b hb)
  | .ex a,     h =>
      match (slash_ex a).mp h with
      | ⟨t, ht⟩ => Derivesᵢ.intro_ex _ a t (slash_derives (substFormula 0 t a) ht)
termination_by f => fdepth f
decreasing_by
  all_goals simp only [fdepth, fdepth_subst]
  all_goals omega

/-! ## El corte del contexto -/

/-- **Corte del contexto.** Si cada hipótesis es derivable sin hipótesis, el contexto sobra.

    Es la pieza que convierte «`Γ ⊢ᵢ f` con `Γ` barrado» en «`[] ⊢ᵢ f`», y hace falta en
    todos los casos de L2 que concluyen una implicación, un `∀` o un átomo. -/
theorem cut_context : ∀ (Γ : List Formula) (f : Formula),
    (∀ g, g ∈ Γ → (([] : List Formula) ⊢ᵢ g)) → (Γ ⊢ᵢ f) → (([] : List Formula) ⊢ᵢ f)
  | [], _, _, hd => hd
  | g :: Γ', f, hall, hd =>
      have hgf : Γ' ⊢ᵢ Formula.impl g f := Derivesᵢ.intro_impl Γ' g f hd
      have hg : ([] : List Formula) ⊢ᵢ g := hall g (List.Mem.head _)
      have hrest : ∀ x, x ∈ Γ' → (([] : List Formula) ⊢ᵢ x) :=
        fun x hx => hall x (List.Mem.tail _ hx)
      Derivesᵢ.elim_impl _ g f (cut_context Γ' (Formula.impl g f) hrest hgf) hg

end PeanoRF.Calculus
