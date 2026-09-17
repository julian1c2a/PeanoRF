/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.Calculus.Consistency
import PeanoRF.Calculus.SubstDerives

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
open FOL.Eigenvariable   -- `posDepth`

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


/-! ## L2 · toda derivación desde un contexto barrado barra su conclusión

    Tres piezas antes del lema: el corte del contexto compuesto con la clausura bajo
    sustitución, el álgebra de posiciones que `rewrite_at` necesita, y la invariancia de la
    barra por reescritura local — que es el caso que no se ve venir. -/

/-- Si cada hipótesis está barrada bajo `ρ`, cada una es derivable sin hipótesis. -/
theorem slashed_ctx_derivable {Γ : List Formula} {ρ : Subst}
    (hall : ∀ g, g ∈ Γ → Slash (substF ρ g)) :
    ∀ x, x ∈ Γ.map (substF ρ) → (([] : List Formula) ⊢ᵢ x) := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact slash_derives _ (hall y hy)

/-- Desde un contexto barrado, lo derivable lo es **sin contexto**: `cut_context` compuesto
    con la clausura de `⊢ᵢ` bajo sustitución. -/
theorem derives_empty_of_slashed {Γ : List Formula} {f : Formula} (h : Γ ⊢ᵢ f) (ρ : Subst)
    (hall : ∀ g, g ∈ Γ → Slash (substF ρ g)) : ([] : List Formula) ⊢ᵢ substF ρ f :=
  cut_context _ _ (slashed_ctx_derivable hall) (derivesI_subst h ρ)

/-! ### Álgebra de posiciones -/

/-- `LocalRule` es simétrica: conmutar dos veces devuelve el original. -/
theorem localRule_symm {A B : Formula} (h : LocalRule A B) : LocalRule B A := by
  cases h with
  | commuteImpl A B C => exact LocalRule.commuteImpl B A C

theorem getAt_replaceAt : ∀ (p : Pos) (f x sub : Formula),
    getAt? f p = some sub → getAt? (replaceAt f p x) p = some x := by
  intro p
  induction p with
  | root => intro f x sub _; simp [replaceAt, getAt?]
  | left p' ih =>
      intro f x sub h
      cases f <;> simp only [getAt?, replaceAt] at h ⊢ <;>
        first | exact ih _ x sub h | simp at h
  | right p' ih =>
      intro f x sub h
      cases f <;> simp only [getAt?, replaceAt] at h ⊢ <;>
        first | exact ih _ x sub h | simp at h
  | body p' ih =>
      intro f x sub h
      cases f <;> simp only [getAt?, replaceAt] at h ⊢ <;>
        first | exact ih _ x sub h | simp at h

theorem replaceAt_self : ∀ (p : Pos) (f sub : Formula),
    getAt? f p = some sub → replaceAt f p sub = f := by
  intro p
  induction p with
  | root => intro f sub h; simp only [getAt?, Option.some.injEq] at h; simp [replaceAt, h]
  | left p' ih =>
      intro f sub h
      cases f <;> simp only [getAt?, replaceAt] at h ⊢ <;>
        first | rw [ih _ sub h] | simp at h
  | right p' ih =>
      intro f sub h
      cases f <;> simp only [getAt?, replaceAt] at h ⊢ <;>
        first | rw [ih _ sub h] | simp at h
  | body p' ih =>
      intro f sub h
      cases f <;> simp only [getAt?, replaceAt] at h ⊢ <;>
        first | rw [ih _ sub h] | simp at h

theorem replaceAt_replaceAt : ∀ (p : Pos) (f x y : Formula),
    replaceAt (replaceAt f p x) p y = replaceAt f p y := by
  intro p
  induction p with
  | root => intro f x y; simp [replaceAt]
  | left p' ih => intro f x y; cases f <;> simp only [replaceAt, ih]
  | right p' ih => intro f x y; cases f <;> simp only [replaceAt, ih]
  | body p' ih => intro f x y; cases f <;> simp only [replaceAt, ih]

/-- La reescritura local, transportada a través de una sustitución. -/
theorem derives_rewrite_subst {p : Pos} {f sub sub' : Formula} {ρ : Subst}
    (hd : ([] : List Formula) ⊢ᵢ substF ρ f)
    (hget : getAt? f p = some sub) (hrule : LocalRule sub sub') :
    ([] : List Formula) ⊢ᵢ substF ρ (replaceAt f p sub') := by
  refine Derivesᵢ.rewrite_at _ _ _ p (substF (upSn (posDepth p) ρ) sub)
    (substF (upSn (posDepth p) ρ) sub') hd ?_ (subst_localRule _ hrule) ?_
  · rw [subst_getAt?, hget]; rfl
  · rw [← subst_replaceAt]

/-- Y de vuelta, que es lo que hace falta en las posiciones contravariantes. -/
theorem derives_rewrite_back {p : Pos} {f sub sub' : Formula} {ρ : Subst}
    (hget : getAt? f p = some sub) (hrule : LocalRule sub sub')
    (hd : ([] : List Formula) ⊢ᵢ substF ρ (replaceAt f p sub')) :
    ([] : List Formula) ⊢ᵢ substF ρ f := by
  have h1 : getAt? (replaceAt f p sub') p = some sub' := getAt_replaceAt p f sub' sub hget
  have h2 := derives_rewrite_subst hd h1 (localRule_symm hrule)
  rwa [replaceAt_replaceAt, replaceAt_self p f sub hget] at h2

/-! ### La barra sobrevive a `rewrite_at` -/

/-- ⭐ **La barra es invariante por reescritura local.**

    El caso que no se ve venir. `LocalRule` sólo tiene `commuteImpl`
    (`A ⇒ B ⇒ C ↝ B ⇒ A ⇒ C`), pero se aplica **en una posición cualquiera** del árbol, y la
    barra no es una propiedad de la fórmula entera sino de su estructura.

    Va como **equivalencia**, no como implicación, porque la posición puede caer a la
    IZQUIERDA de una implicación y ahí la dirección se invierte. Y el `∀ ρ` va **dentro**,
    porque bajo un cuantificador la sustitución que actúa ya no es `ρ`. -/
theorem slash_rewrite : ∀ (p : Pos) (sub sub' : Formula), LocalRule sub sub' →
    ∀ (f : Formula) (ρ : Subst), getAt? f p = some sub →
      (Slash (substF ρ f) ↔ Slash (substF ρ (replaceAt f p sub'))) := by
  intro p
  induction p with
  | root =>
      intro sub sub' hrule f ρ hget
      simp only [getAt?, Option.some.injEq] at hget
      subst hget
      simp only [replaceAt]
      cases hrule with
      | commuteImpl A B C =>
          have hcomm : ∀ X Y Z : Formula, ([] : List Formula) ⊢ᵢ
              Formula.impl X (Formula.impl Y Z) →
              ([] : List Formula) ⊢ᵢ Formula.impl Y (Formula.impl X Z) := by
            intro X Y Z hd
            exact Derivesᵢ.rewrite_at _ _ _ Pos.root _ _ hd rfl
              (LocalRule.commuteImpl X Y Z) rfl
          simp only [substF, slash_impl]
          constructor
          · rintro ⟨hd, himp⟩
            refine ⟨hcomm _ _ _ hd, fun hb => ?_⟩
            exact ⟨Derivesᵢ.elim_impl _ _ _ (hcomm _ _ _ hd) (slash_derives _ hb),
              fun ha => (himp ha).2 hb⟩
          · rintro ⟨hd, himp⟩
            refine ⟨hcomm _ _ _ hd, fun ha => ?_⟩
            exact ⟨Derivesᵢ.elim_impl _ _ _ (hcomm _ _ _ hd) (slash_derives _ ha),
              fun hb => (himp hb).2 ha⟩
  | left p' ih =>
      intro sub sub' hrule f ρ hget
      cases f with
      | impl a b =>
          have hg : getAt? a p' = some sub := hget
          have hab := ih sub sub' hrule a ρ hg
          have hfwd := fun hd => derives_rewrite_subst (p := Pos.left p')
            (f := Formula.impl a b) (ρ := ρ) hd hget hrule
          have hbwd := fun hd => derives_rewrite_back (p := Pos.left p')
            (f := Formula.impl a b) (ρ := ρ) hget hrule hd
          simp only [replaceAt, substF, slash_impl] at hfwd hbwd ⊢
          constructor
          · rintro ⟨hd, himp⟩
            exact ⟨hfwd hd, fun ha' => himp (hab.mpr ha')⟩
          · rintro ⟨hd, himp⟩
            exact ⟨hbwd hd, fun ha => himp (hab.mp ha)⟩
      | and a b =>
          have hg : getAt? a p' = some sub := hget
          have hab := ih sub sub' hrule a ρ hg
          simp only [replaceAt, substF, slash_and]
          exact ⟨fun h => ⟨hab.mp h.1, h.2⟩, fun h => ⟨hab.mpr h.1, h.2⟩⟩
      | or a b =>
          have hg : getAt? a p' = some sub := hget
          have hab := ih sub sub' hrule a ρ hg
          simp only [replaceAt, substF, slash_or]
          exact ⟨fun h => h.imp hab.mp id, fun h => h.imp hab.mpr id⟩
      | bottom => simp [getAt?] at hget
      | atom _ _ => simp [getAt?] at hget
      | eq _ _ => simp [getAt?] at hget
      | «forall» _ => simp [getAt?] at hget
      | ex _ => simp [getAt?] at hget
  | right p' ih =>
      intro sub sub' hrule f ρ hget
      cases f with
      | impl a b =>
          have hg : getAt? b p' = some sub := hget
          have hab := ih sub sub' hrule b ρ hg
          have hfwd := fun hd => derives_rewrite_subst (p := Pos.right p')
            (f := Formula.impl a b) (ρ := ρ) hd hget hrule
          have hbwd := fun hd => derives_rewrite_back (p := Pos.right p')
            (f := Formula.impl a b) (ρ := ρ) hget hrule hd
          simp only [replaceAt, substF, slash_impl] at hfwd hbwd ⊢
          constructor
          · rintro ⟨hd, himp⟩
            exact ⟨hfwd hd, fun ha => hab.mp (himp ha)⟩
          · rintro ⟨hd, himp⟩
            exact ⟨hbwd hd, fun ha => hab.mpr (himp ha)⟩
      | and a b =>
          have hg : getAt? b p' = some sub := hget
          have hab := ih sub sub' hrule b ρ hg
          simp only [replaceAt, substF, slash_and]
          exact ⟨fun h => ⟨h.1, hab.mp h.2⟩, fun h => ⟨h.1, hab.mpr h.2⟩⟩
      | or a b =>
          have hg : getAt? b p' = some sub := hget
          have hab := ih sub sub' hrule b ρ hg
          simp only [replaceAt, substF, slash_or]
          exact ⟨fun h => h.imp id hab.mp, fun h => h.imp id hab.mpr⟩
      | bottom => simp [getAt?] at hget
      | atom _ _ => simp [getAt?] at hget
      | eq _ _ => simp [getAt?] at hget
      | «forall» _ => simp [getAt?] at hget
      | ex _ => simp [getAt?] at hget
  | body p' ih =>
      intro sub sub' hrule f ρ hget
      cases f with
      | «forall» a =>
          have hg : getAt? a p' = some sub := hget
          have hfwd := fun hd => derives_rewrite_subst (p := Pos.body p')
            (f := Formula.forall a) (ρ := ρ) hd hget hrule
          have hbwd := fun hd => derives_rewrite_back (p := Pos.body p')
            (f := Formula.forall a) (ρ := ρ) hget hrule hd
          simp only [replaceAt, substF, slash_forall] at hfwd hbwd ⊢
          constructor
          · rintro ⟨hd, hall⟩
            refine ⟨hfwd hd, fun t => ?_⟩
            rw [substFormula_upS]
            exact (ih sub sub' hrule a (consS t ρ) hg).mp
              (by rw [← substFormula_upS]; exact hall t)
          · rintro ⟨hd, hall⟩
            refine ⟨hbwd hd, fun t => ?_⟩
            rw [substFormula_upS]
            exact (ih sub sub' hrule a (consS t ρ) hg).mpr
              (by rw [← substFormula_upS]; exact hall t)
      | ex a =>
          have hg : getAt? a p' = some sub := hget
          simp only [replaceAt, substF, slash_ex]
          constructor
          · rintro ⟨t, ht⟩
            refine ⟨t, ?_⟩
            rw [substFormula_upS]
            exact (ih sub sub' hrule a (consS t ρ) hg).mp
              (by rw [← substFormula_upS]; exact ht)
          · rintro ⟨t, ht⟩
            refine ⟨t, ?_⟩
            rw [substFormula_upS]
            exact (ih sub sub' hrule a (consS t ρ) hg).mpr
              (by rw [← substFormula_upS]; exact ht)
      | bottom => simp [getAt?] at hget
      | atom _ _ => simp [getAt?] at hget
      | eq _ _ => simp [getAt?] at hget
      | impl _ _ => simp [getAt?] at hget
      | and _ _ => simp [getAt?] at hget
      | or _ _ => simp [getAt?] at hget


/-! ## ⏳ Lo que falta de L2, y es UN caso

    Con `slash_rewrite`, `derivesI_subst` y `cut_context` en la mano, **diecisiete de los
    dieciocho casos de L2 son mecánicos**. El que no lo es, y conviene decirlo con nombre y
    apellidos, es `Derivesᵢ.subst` — la regla de Leibniz:

    > `Γ ⊢ᵢ t₁ = t₂ → Γ ⊢ᵢ f[t₁/0] → Γ ⊢ᵢ f[t₂/0]`

    Para L2 hace falta: de `Slash (substF ρ (f[t₁/0]))` y `[] ⊢ᵢ t₁ρ = t₂ρ`, concluir
    `Slash (substF ρ (f[t₂/0]))`. Por el álgebra de `Subst.lean` eso es exactamente

    > `Slash (substF (consS x ρ) f) → Slash (substF (consS y ρ) f)`  con `[] ⊢ᵢ x = y`,

    o sea: **la barra es invariante bajo sustituciones probablemente iguales**. Es verdad,
    y se demuestra por inducción en `fdepth f`. Los casos atómicos salen de la propia regla
    `Derivesᵢ.subst`; `∧`, `∨`, `→` salen de la hipótesis de inducción (con `→` pidiendo la
    dirección contraria, que da `eqI_symm`).

    ⛔ **El caso que se atasca es el cuantificador.** Bajo un `∀`, las dos sustituciones
    dejan de diferir en el índice 0 y pasan a diferir en el 1 — y `Derivesᵢ.subst`
    **sólo sustituye en el índice 0**. Hace falta la regla de Leibniz **en un índice
    cualquiera**:

    > `[] ⊢ᵢ x = y → [] ⊢ᵢ f[x/k] → [] ⊢ᵢ f[y/k]`

    Dos salidas, y la elección es de diseño, no técnica:

    1. **Derivarla aquí** con el álgebra σ que ya existe: hace falta la permutación de los
       índices `0` y `k`, y reescribir `f[x/k]` como `(f∘swap)[x/0]`. Es trabajo, pero no
       toca ni el cálculo ni FOL.
    2. **Pedirla aguas arriba**: `Derives₀` tiene el mismo `subst` fijado en 0, así que el
       problema es suyo también en cuanto quieran la propiedad de disyunción. Encaja con el
       encargo ya abierto (`doc/ENCARGO-FOL-2026-09-17.md`).

    ⚠️ Lo que NO se hace es meter un `sorry` para enseñar L2 antes de tiempo: el proyecto
    lleva 0 y esa cifra es un control, no un adorno. -/

end PeanoRF.Calculus
