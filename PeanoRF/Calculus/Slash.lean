/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.Calculus.Consistency
import PeanoRF.Calculus.SubstDerives
import PeanoRF.Calculus.Eq
import PeanoRF.Calculus.Collapse

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

  `Slash T D f` («la teoría `T` barra `f`, con los testigos tomados de `D`») se define por
  recursión en la COMPLEJIDAD de `f`,
  no en su estructura: el caso `∀` baja a `substFormula 0 t a`, que no es subtérmino de
  `∀a`. De ahí `fdepth` y `fdepth_subst`.

  Una vez definida, la propiedad de disyunción es inmediata de dos lemas:

  | lema | enunciado | estado |
  |---|---|---|
  | **L1** `slash_derives` | `Slash T D f → [] ⊢ᵢ f` | ✅ aquí |
  | **L2** `slash_of_derives` | `Γ ⊢ᵢ f` y `Γ` barrado ⟹ `Slash T D f` | ✅ aquí |

  ## 🔁 Los DOS parámetros, y por qué cada uno

  * **`T`, la teoría** (etapa 1 de H3ter): sin ella, `Slash g` para un axioma de HA
    significaba «derivable desde nada», que es falso, y la DP de HA no se podía ni enunciar.
  * **`D`, el dominio** (etapa 2, 2026-09-18): las cláusulas de `∀` y `∃` cuantifican sobre
    los términos de `D`, no sobre todos. Sin ello **`ax19_lt_trichotomy` no se puede barrar**:
    su `∀` recorre términos de los que HA no sabe nada.

  `D` entra en L2 como una **clausura**, no como una lista de términos:

  > `hDsub : ∀ ρ, (∀ n, D (ρ n)) → ∀ t, D (substT ρ t)`

  Es lo que piden `elim_forall` e `intro_ex`, que instancian con `substT ρ t` para un `t`
  ARBITRARIO. ⚠️ Con `D = ClosedQTerm` esa clausura es **FALSA** —`t` puede llevar símbolos
  ajenos y aridades erróneas—, y ahí entra el colapso: `HA.Domain` demuestra la versión con
  `collapseT LQ` delante (`closed_collapse_subst`), que es la que usará la **forma (c)** de
  L2. Mientras tanto, H3bis vive en `D = fun _ => True`, donde la clausura es trivial.

  ## ⚠️ §L2 — lo que falta, y cuál es EXACTAMENTE el obstáculo

  L2 es una inducción sobre la derivación, y con el enunciado ingenuo **dos casos no
  cierran**:

  * `intro_forall`: de `Γ.map (lift 0) ⊢ᵢ A` hay que sacar `∀t, Slash T D (A[t])`. La
    derivación de `A[t]` existe (`intro_forall` y luego `elim_forall`), pero **no es una
    subderivación**: la hipótesis de inducción no la alcanza.
  * `elim_ex`: el testigo `t` que da la barra hay que meterlo en la segunda premisa, y otra
    vez la derivación resultante no es subderivación.

  El primer diagnóstico fue «hace falta indexar por ALTURA, como `LKh` en el Hauptsatz».
  **Es falso**, y desarrollar los casos lo deja claro. Lo que hace falta es **generalizar
  el enunciado sobre SUSTITUCIONES**:

  > `Γ ⊢ᵢ f ⟹ ∀ σ cerrante, (∀ g ∈ Γ, Slash T D (gσ)) → Slash T D (fσ)`

  Con esa forma, el caso `intro_forall` se cierra **con la misma inducción estructural**:
  la meta es `∀t, Slash T D (A[σ⁺][0↦t])`, que es `Slash T D (A(t·σ))`, o sea la hipótesis de
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

    Léase `Slash T D f` como «`f` es demostrable *y además* lo es por la razón correcta»: una
    disyunción barrada tiene una rama barrada, un existencial barrado tiene un testigo. Es
    justo lo que una prueba clásica de `P ∨ ¬P` no puede dar. -/
def Slash (T : List Formula) (D : Term → Prop) : Formula → Prop
  | .bottom     => False
  | .atom p ts  => T ⊢ᵢ Formula.atom p ts
  | .eq t u     => T ⊢ᵢ Formula.eq t u
  | .and a b    => Slash T D a ∧ Slash T D b
  | .or a b     => Slash T D a ∨ Slash T D b
  | .impl a b   => (T ⊢ᵢ Formula.impl a b) ∧ (Slash T D a → Slash T D b)
  | .forall a   => (T ⊢ᵢ Formula.forall a) ∧
                     (∀ t : Term, D t → Slash T D (substFormula 0 t a))
  | .ex a       => ∃ t : Term, And (D t) (Slash T D (substFormula 0 t a))
termination_by f => fdepth f
decreasing_by
  all_goals simp only [fdepth, fdepth_subst]
  all_goals omega

/-! ### Las ecuaciones de la barra

    `Slash T D` se define por recursión BIEN FUNDADA (en `fdepth`), así que **no reduce
    definicionalmente**: `Slash T D (.and a b)` no es juzgacionalmente `Slash T D a ∧ Slash T D b`. Hay
    que desplegarla con sus ecuaciones, y por eso van aquí una a una. -/

@[simp] theorem slash_bottom (T : List Formula) (D : Term → Prop) : Slash T D Formula.bottom ↔ False := by rw [Slash]

@[simp] theorem slash_atom (T : List Formula) (D : Term → Prop) (p : String) (ts : List Term) :
    Slash T D (Formula.atom p ts) ↔ (T ⊢ᵢ Formula.atom p ts) := by rw [Slash]

@[simp] theorem slash_eq (T : List Formula) (D : Term → Prop) (t u : Term) :
    Slash T D (Formula.eq t u) ↔ (T ⊢ᵢ Formula.eq t u) := by rw [Slash]

@[simp] theorem slash_and (T : List Formula) (D : Term → Prop) (a b : Formula) :
    Slash T D (Formula.and a b) ↔ (Slash T D a ∧ Slash T D b) := by rw [Slash]

@[simp] theorem slash_or (T : List Formula) (D : Term → Prop) (a b : Formula) :
    Slash T D (Formula.or a b) ↔ (Slash T D a ∨ Slash T D b) := by rw [Slash]

@[simp] theorem slash_impl (T : List Formula) (D : Term → Prop) (a b : Formula) :
    Slash T D (Formula.impl a b) ↔
      ((T ⊢ᵢ Formula.impl a b) ∧ (Slash T D a → Slash T D b)) := by rw [Slash]

@[simp] theorem slash_forall (T : List Formula) (D : Term → Prop) (a : Formula) :
    Slash T D (Formula.forall a) ↔
      ((T ⊢ᵢ Formula.forall a) ∧
        (∀ t : Term, D t → Slash T D (substFormula 0 t a))) := by rw [Slash]

@[simp] theorem slash_ex (T : List Formula) (D : Term → Prop) (a : Formula) :
    Slash T D (Formula.ex a) ↔
      ∃ t : Term, And (D t) (Slash T D (substFormula 0 t a)) := by rw [Slash]

/-! ## L1 · lo barrado es derivable -/

/-- **L1.** La barra implica la derivabilidad. Los casos `∧`, `∨` y `∃` recurren, y por eso
    esta prueba también va por complejidad. -/
theorem slash_derives (T : List Formula) (D : Term → Prop) : ∀ f : Formula, Slash T D f → (T ⊢ᵢ f)
  | .bottom,   h => ((slash_bottom T D).mp h).elim
  | .atom _ _, h => (slash_atom T D _ _).mp h
  | .eq _ _,   h => (slash_eq T D _ _).mp h
  | .impl a b, h => ((slash_impl T D a b).mp h).1
  | .forall a, h => ((slash_forall T D a).mp h).1
  | .and a b,  h =>
      Derivesᵢ.intro_and _ a b
        (slash_derives T D a ((slash_and T D a b).mp h).1)
        (slash_derives T D b ((slash_and T D a b).mp h).2)
  | .or a b,   h =>
      match (slash_or T D a b).mp h with
      | Or.inl ha => Derivesᵢ.intro_or_l _ a b (slash_derives T D a ha)
      | Or.inr hb => Derivesᵢ.intro_or_r _ a b (slash_derives T D b hb)
  | .ex a,     h =>
      match (slash_ex T D a).mp h with
      | ⟨t, _, ht⟩ => Derivesᵢ.intro_ex _ a t (slash_derives T D (substFormula 0 t a) ht)
termination_by f => fdepth f
decreasing_by
  all_goals simp only [fdepth, fdepth_subst]
  all_goals omega

/-! ## ⭐ Las fórmulas de HARROP — donde la barra COINCIDE con la derivabilidad

    La etapa 3 de H3ter pide barrar los 33 axiomas de `coreAxioms`, y hacerlo uno a uno
    sería absurdo. Casi todos caen de un solo lema, y la razón es clásica: **para una fórmula
    de Harrop, estar barrada no es más que ser derivable.**

    La clase se lee de los casos de la barra, mirando cuáles NO piden testigo:

    | conectiva | la barra pide | ¿vale? |
    |---|---|---|
    | `atom`, `eq` | la derivabilidad, y nada más | ✅ |
    | `a ∧ b` | las dos barradas | ✅ si lo son `a` y `b` |
    | `a ⇒ b` | derivable, y `∣a → ∣b` | ✅ si lo es **`b`** — el antecedente da igual |
    | `∀a` | derivable, y `∣a[t]` para todo `t` del dominio | ✅ si lo es `a` |
    | `a ∨ b` | **una rama barrada** | ⛔ |
    | `∃a` | **un testigo** | ⛔ |
    | `⊥` | `False` | ✅ **si `T` es consistente** — y ése es todo el precio |

    ⭐ Que el antecedente de `⇒` sea libre es lo que hace la clase grande: se usa L1 para
    bajar de `∣a` a `⊢ᵢ a`, y de ahí `elim_impl`. Es el único sitio donde L1 trabaja.

    ⛔ **Lo que esto NO cubre**, y es exactamente la lista dura que la medición anunció:
    `ax19_lt_trichotomy` (una `∨`), `ax21_mod2_range` (otra), `ax13_lt_def`,
    `ax_L3_in_concat` y `ax29_sub_witness` (un `∃`). Esos piden decidir en el meta. -/

/-- La clase de Harrop, como PREDICADO DECIDIBLE: así cada axioma se comprueba con `decide`
    en vez de con una prueba a mano. -/
def isHarrop : Formula → Bool
  | .bottom    => true
  | .atom _ _  => true
  | .eq _ _    => true
  | .and a b   => isHarrop a && isHarrop b
  | .impl _ b  => isHarrop b
  | .forall a  => isHarrop a
  | .or _ _    => false
  | .ex _      => false

/-- Sustituir no saca de la clase. Hace falta en el caso `∀`, que baja a `a[t]`. -/
@[simp] theorem isHarrop_subst (v : Nat) (t : Term) : ∀ f : Formula,
    isHarrop (substFormula v t f) = isHarrop f := by
  intro f
  induction f generalizing v t with
  | bottom => rfl
  | atom _ _ => rfl
  | eq _ _ => rfl
  | impl _ _ _ ih2 => simp only [substFormula, isHarrop, ih2]
  | and _ _ ih1 ih2 => simp only [substFormula, isHarrop, ih1, ih2]
  | or _ _ _ _ => rfl
  | «forall» _ ih => simp only [substFormula, isHarrop, ih]
  | ex _ _ => rfl

/-- ⭐⭐ **Para una fórmula de Harrop, derivable ⟹ barrada.**

    Va por complejidad, como la barra misma: el caso `∀` baja a `a[t]`, que no es subtérmino.
    El dominio `D` no interviene — la cláusula `∀ t, D t → …` sólo se hace más fácil cuanto
    menor sea `D`. -/
theorem slash_of_isHarrop (T : List Formula) (D : Term → Prop)
    (hcon : ¬ (T ⊢ᵢ Formula.bottom)) :
    ∀ f : Formula, isHarrop f = true → (T ⊢ᵢ f) → Slash T D f
  | .bottom,    _,  hd => absurd hd hcon
  | .or _ _,    hH, _  => Bool.noConfusion hH
  | .ex _,      hH, _  => Bool.noConfusion hH
  | .atom p ts, _,  hd => (slash_atom T D p ts).mpr hd
  | .eq t u,    _,  hd => (slash_eq T D t u).mpr hd
  | .and a b,   hH, hd => by
      simp only [isHarrop, Bool.and_eq_true] at hH
      exact (slash_and T D a b).mpr
        ⟨slash_of_isHarrop T D hcon a hH.1 (Derivesᵢ.elim_and_l _ a b hd),
         slash_of_isHarrop T D hcon b hH.2 (Derivesᵢ.elim_and_r _ a b hd)⟩
  | .impl a b,  hH, hd => by
      simp only [isHarrop] at hH
      exact (slash_impl T D a b).mpr ⟨hd, fun ha =>
        slash_of_isHarrop T D hcon b hH (Derivesᵢ.elim_impl _ a b hd (slash_derives T D a ha))⟩
  | .forall a,  hH, hd => by
      simp only [isHarrop] at hH
      exact (slash_forall T D a).mpr ⟨hd, fun t _ =>
        slash_of_isHarrop T D hcon (substFormula 0 t a) (by rw [isHarrop_subst]; exact hH)
          (Derivesᵢ.elim_forall _ a t hd)⟩
termination_by f => fdepth f
decreasing_by
  all_goals simp only [fdepth, fdepth_subst]
  all_goals omega

/-! ## El corte del contexto -/

/-- **Corte del contexto.** Si cada hipótesis es derivable DESDE LA TEORÍA, el contexto
    sobra: lo derivable desde `Γ` lo es desde `T`.

    Es la pieza que convierte «`Γ ⊢ᵢ f` con `Γ` barrado» en «`T ⊢ᵢ f`», y hace falta en
    todos los casos de L2 que concluyen una implicación, un `∀` o un átomo.

    ⚠️ El caso base ya no es `hd` a secas: con `T` arbitraria hay que **debilitar** de `[]`
    a `T`. Con `T = []` era `id`, y por eso no se veía. -/
theorem cut_context (T : List Formula) : ∀ (Γ : List Formula) (f : Formula),
    (∀ g, g ∈ Γ → (T ⊢ᵢ g)) → (Γ ⊢ᵢ f) → (T ⊢ᵢ f)
  | [], _, _, hd => Derivesᵢ.weakening [] T _ hd (fun _ hx => absurd hx List.not_mem_nil)
  | g :: Γ', f, hall, hd =>
      have hgf : Γ' ⊢ᵢ Formula.impl g f := Derivesᵢ.intro_impl Γ' g f hd
      have hg : T ⊢ᵢ g := hall g (List.Mem.head _)
      have hrest : ∀ x, x ∈ Γ' → (T ⊢ᵢ x) :=
        fun x hx => hall x (List.Mem.tail _ hx)
      Derivesᵢ.elim_impl _ g f (cut_context T Γ' (Formula.impl g f) hrest hgf) hg


/-! ## L2 · toda derivación desde un contexto barrado barra su conclusión

    Tres piezas antes del lema: el corte del contexto compuesto con la clausura bajo
    sustitución, el álgebra de posiciones que `rewrite_at` necesita, y la invariancia de la
    barra por reescritura local — que es el caso que no se ve venir. -/

/-- Si cada hipótesis está barrada bajo `ρ` **y colapsada**, cada una es derivable sin
    hipótesis. La lista lleva los dos `map` porque así la deja `derivesI_collapse` aplicado
    a `derivesI_subst`. -/
theorem slashed_ctx_derivable (T : List Formula) (D : Term → Prop) (L : String → Nat → Bool)
    {Γ : List Formula} {ρ : Subst}
    (hall : ∀ g, g ∈ Γ → Slash T D (collapseF L (substF ρ g))) :
    ∀ x, x ∈ (Γ.map (substF ρ)).map (collapseF L) → (T ⊢ᵢ x) := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
  rcases List.mem_map.mp hy with ⟨z, hz, rfl⟩
  exact slash_derives T D _ (hall z hz)

/-- Desde un contexto barrado, lo derivable lo es **sin contexto**: `cut_context` compuesto
    con las dos clausuras de `⊢ᵢ` — bajo sustitución **y bajo colapso**. -/
theorem derives_empty_of_slashed (T : List Formula) (D : Term → Prop) (L : String → Nat → Bool)
    {Γ : List Formula} {f : Formula}
    (h : Γ ⊢ᵢ f) (ρ : Subst)
    (hall : ∀ g, g ∈ Γ → Slash T D (collapseF L (substF ρ g))) :
    T ⊢ᵢ collapseF L (substF ρ f) :=
  cut_context T _ _ (slashed_ctx_derivable T D L hall)
    (derivesI_collapse L (derivesI_subst h ρ))

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
theorem derives_rewrite_subst (T : List Formula) {p : Pos} {f sub sub' : Formula} {ρ : Subst}
    (hd : T ⊢ᵢ substF ρ f)
    (hget : getAt? f p = some sub) (hrule : LocalRule sub sub') :
    T ⊢ᵢ substF ρ (replaceAt f p sub') := by
  refine Derivesᵢ.rewrite_at _ _ _ p (substF (upSn (posDepth p) ρ) sub)
    (substF (upSn (posDepth p) ρ) sub') hd ?_ (subst_localRule _ hrule) ?_
  · rw [subst_getAt?, hget]; rfl
  · rw [← subst_replaceAt]

/-- Y de vuelta, que es lo que hace falta en las posiciones contravariantes. -/
theorem derives_rewrite_back (T : List Formula) {p : Pos} {f sub sub' : Formula} {ρ : Subst}
    (hget : getAt? f p = some sub) (hrule : LocalRule sub sub')
    (hd : T ⊢ᵢ substF ρ (replaceAt f p sub')) :
    T ⊢ᵢ substF ρ f := by
  have h1 : getAt? (replaceAt f p sub') p = some sub' := getAt_replaceAt p f sub' sub hget
  have h2 := derives_rewrite_subst T hd h1 (localRule_symm hrule)
  rwa [replaceAt_replaceAt, replaceAt_self p f sub hget] at h2

/-! ### La barra sobrevive a `rewrite_at` -/

/-- ⭐ **La barra es invariante por reescritura local.**

    El caso que no se ve venir. `LocalRule` sólo tiene `commuteImpl`
    (`A ⇒ B ⇒ C ↝ B ⇒ A ⇒ C`), pero se aplica **en una posición cualquiera** del árbol, y la
    barra no es una propiedad de la fórmula entera sino de su estructura.

    Va como **equivalencia**, no como implicación, porque la posición puede caer a la
    IZQUIERDA de una implicación y ahí la dirección se invierte. Y el `∀ ρ` va **dentro**,
    porque bajo un cuantificador la sustitución que actúa ya no es `ρ`. -/
theorem slash_rewrite (T : List Formula) (D : Term → Prop) : ∀ (p : Pos) (sub sub' : Formula), LocalRule sub sub' →
    ∀ (f : Formula) (ρ : Subst), getAt? f p = some sub →
      (Slash T D (substF ρ f) ↔ Slash T D (substF ρ (replaceAt f p sub'))) := by
  intro p
  induction p with
  | root =>
      intro sub sub' hrule f ρ hget
      simp only [getAt?, Option.some.injEq] at hget
      subst hget
      simp only [replaceAt]
      cases hrule with
      | commuteImpl A B C =>
          have hcomm : ∀ X Y Z : Formula, T ⊢ᵢ
              Formula.impl X (Formula.impl Y Z) →
              T ⊢ᵢ Formula.impl Y (Formula.impl X Z) := by
            intro X Y Z hd
            exact Derivesᵢ.rewrite_at _ _ _ Pos.root _ _ hd rfl
              (LocalRule.commuteImpl X Y Z) rfl
          simp only [substF, slash_impl]
          constructor
          · rintro ⟨hd, himp⟩
            refine ⟨hcomm _ _ _ hd, fun hb => ?_⟩
            exact ⟨Derivesᵢ.elim_impl _ _ _ (hcomm _ _ _ hd) (slash_derives T D _ hb),
              fun ha => (himp ha).2 hb⟩
          · rintro ⟨hd, himp⟩
            refine ⟨hcomm _ _ _ hd, fun ha => ?_⟩
            exact ⟨Derivesᵢ.elim_impl _ _ _ (hcomm _ _ _ hd) (slash_derives T D _ ha),
              fun hb => (himp hb).2 ha⟩
  | left p' ih =>
      intro sub sub' hrule f ρ hget
      cases f with
      | impl a b =>
          have hg : getAt? a p' = some sub := hget
          have hab := ih sub sub' hrule a ρ hg
          have hfwd := fun hd => derives_rewrite_subst T (p := Pos.left p')
            (f := Formula.impl a b) (ρ := ρ) hd hget hrule
          have hbwd := fun hd => derives_rewrite_back T (p := Pos.left p')
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
          have hfwd := fun hd => derives_rewrite_subst T (p := Pos.right p')
            (f := Formula.impl a b) (ρ := ρ) hd hget hrule
          have hbwd := fun hd => derives_rewrite_back T (p := Pos.right p')
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
          have hfwd := fun hd => derives_rewrite_subst T (p := Pos.body p')
            (f := Formula.forall a) (ρ := ρ) hd hget hrule
          have hbwd := fun hd => derives_rewrite_back T (p := Pos.body p')
            (f := Formula.forall a) (ρ := ρ) hget hrule hd
          simp only [replaceAt, substF, slash_forall] at hfwd hbwd ⊢
          constructor
          · rintro ⟨hd, hall⟩
            refine ⟨hfwd hd, fun t hDt => ?_⟩
            rw [substFormula_upS]
            exact (ih sub sub' hrule a (consS t ρ) hg).mp
              (by rw [← substFormula_upS]; exact hall t hDt)
          · rintro ⟨hd, hall⟩
            refine ⟨hbwd hd, fun t hDt => ?_⟩
            rw [substFormula_upS]
            exact (ih sub sub' hrule a (consS t ρ) hg).mpr
              (by rw [← substFormula_upS]; exact hall t hDt)
      | ex a =>
          have hg : getAt? a p' = some sub := hget
          simp only [replaceAt, substF, slash_ex]
          constructor
          · rintro ⟨t, hDt, ht⟩
            refine ⟨t, hDt, ?_⟩
            rw [substFormula_upS]
            exact (ih sub sub' hrule a (consS t ρ) hg).mp
              (by rw [← substFormula_upS]; exact ht)
          · rintro ⟨t, hDt, ht⟩
            refine ⟨t, hDt, ?_⟩
            rw [substFormula_upS]
            exact (ih sub sub' hrule a (consS t ρ) hg).mpr
              (by rw [← substFormula_upS]; exact ht)
      | bottom => simp [getAt?] at hget
      | atom _ _ => simp [getAt?] at hget
      | eq _ _ => simp [getAt?] at hget
      | impl _ _ => simp [getAt?] at hget
      | and _ _ => simp [getAt?] at hget
      | or _ _ => simp [getAt?] at hget




/-! ## La barra es invariante bajo sustituciones PROBABLEMENTE iguales -/

/-- ⭐⭐ **El último ingrediente de L2.**

    Si dos sustituciones coinciden salvo en un índice, y en ese índice los términos son
    **demostrablemente iguales**, la barra no distingue entre ellas.

    La derivabilidad la transporta `leibniz_at`; el resto es inducción en la complejidad de
    la fórmula. Va como **equivalencia** porque el caso `→` necesita la dirección contraria,
    y el índice **sube a `k+1`** al entrar bajo un cuantificador — que es exactamente la
    razón por la que hizo falta Leibniz en un índice cualquiera. -/
theorem slash_eq_congr (T : List Formula) (D : Term → Prop) : ∀ (A : Formula) (k : Nat) (ρ₁ ρ₂ : Subst),
    (∀ n, n ≠ k → ρ₁ n = ρ₂ n) →
    (T ⊢ᵢ Formula.eq (ρ₁ k) (ρ₂ k)) →
    (Slash T D (substF ρ₁ A) ↔ Slash T D (substF ρ₂ A))
  | .bottom, _, _, _, _, _ => Iff.rfl
  | .atom p ts, k, ρ₁, ρ₂, hag, heq => by
      simp only [substF, slash_atom]
      exact ⟨fun h => leibniz_at T k (Formula.atom p ts) ρ₁ ρ₂ hag heq h,
        fun h => leibniz_at T k (Formula.atom p ts) ρ₂ ρ₁
          (fun n hn => (hag n hn).symm) (eqI_symm heq) h⟩
  | .eq t u, k, ρ₁, ρ₂, hag, heq => by
      simp only [substF, slash_eq]
      exact ⟨fun h => leibniz_at T k (Formula.eq t u) ρ₁ ρ₂ hag heq h,
        fun h => leibniz_at T k (Formula.eq t u) ρ₂ ρ₁
          (fun n hn => (hag n hn).symm) (eqI_symm heq) h⟩
  | .and a b, k, ρ₁, ρ₂, hag, heq => by
      have iha := slash_eq_congr T D a k ρ₁ ρ₂ hag heq
      have ihb := slash_eq_congr T D b k ρ₁ ρ₂ hag heq
      simp only [substF, slash_and]
      exact ⟨fun h => ⟨iha.mp h.1, ihb.mp h.2⟩, fun h => ⟨iha.mpr h.1, ihb.mpr h.2⟩⟩
  | .or a b, k, ρ₁, ρ₂, hag, heq => by
      have iha := slash_eq_congr T D a k ρ₁ ρ₂ hag heq
      have ihb := slash_eq_congr T D b k ρ₁ ρ₂ hag heq
      simp only [substF, slash_or]
      exact ⟨fun h => h.imp iha.mp ihb.mp, fun h => h.imp iha.mpr ihb.mpr⟩
  | .impl a b, k, ρ₁, ρ₂, hag, heq => by
      have iha := slash_eq_congr T D a k ρ₁ ρ₂ hag heq
      have ihb := slash_eq_congr T D b k ρ₁ ρ₂ hag heq
      have hfw : T ⊢ᵢ substF ρ₁ (Formula.impl a b) →
          T ⊢ᵢ substF ρ₂ (Formula.impl a b) :=
        fun h => leibniz_at T k (Formula.impl a b) ρ₁ ρ₂ hag heq h
      have hbw : T ⊢ᵢ substF ρ₂ (Formula.impl a b) →
          T ⊢ᵢ substF ρ₁ (Formula.impl a b) :=
        fun h => leibniz_at T k (Formula.impl a b) ρ₂ ρ₁
          (fun n hn => (hag n hn).symm) (eqI_symm heq) h
      simp only [substF, slash_impl] at hfw hbw ⊢
      exact ⟨fun h => ⟨hfw h.1, fun ha => ihb.mp (h.2 (iha.mpr ha))⟩,
        fun h => ⟨hbw h.1, fun ha => ihb.mpr (h.2 (iha.mp ha))⟩⟩
  | .forall a, k, ρ₁, ρ₂, hag, heq => by
      have hag' : ∀ (t : Term) (n : Nat), n ≠ k + 1 →
          consS t ρ₁ n = consS t ρ₂ n := by
        intro t n hn
        cases n with
        | zero => rfl
        | succ m => exact hag m (by omega)
      have heq' : ∀ t : Term, T ⊢ᵢ
          Formula.eq (consS t ρ₁ (k + 1)) (consS t ρ₂ (k + 1)) := fun _ => heq
      have hfw : T ⊢ᵢ substF ρ₁ (Formula.forall a) →
          T ⊢ᵢ substF ρ₂ (Formula.forall a) :=
        fun h => leibniz_at T k (Formula.forall a) ρ₁ ρ₂ hag heq h
      have hbw : T ⊢ᵢ substF ρ₂ (Formula.forall a) →
          T ⊢ᵢ substF ρ₁ (Formula.forall a) :=
        fun h => leibniz_at T k (Formula.forall a) ρ₂ ρ₁
          (fun n hn => (hag n hn).symm) (eqI_symm heq) h
      simp only [substF, slash_forall] at hfw hbw ⊢
      constructor
      · rintro ⟨hd, hall⟩
        refine ⟨hfw hd, fun t hDt => ?_⟩
        rw [substFormula_upS]
        exact (slash_eq_congr T D a (k + 1) (consS t ρ₁) (consS t ρ₂) (hag' t) (heq' t)).mp
          (by rw [← substFormula_upS]; exact hall t hDt)
      · rintro ⟨hd, hall⟩
        refine ⟨hbw hd, fun t hDt => ?_⟩
        rw [substFormula_upS]
        exact (slash_eq_congr T D a (k + 1) (consS t ρ₁) (consS t ρ₂) (hag' t) (heq' t)).mpr
          (by rw [← substFormula_upS]; exact hall t hDt)
  | .ex a, k, ρ₁, ρ₂, hag, heq => by
      have hag' : ∀ (t : Term) (n : Nat), n ≠ k + 1 →
          consS t ρ₁ n = consS t ρ₂ n := by
        intro t n hn
        cases n with
        | zero => rfl
        | succ m => exact hag m (by omega)
      have heq' : ∀ t : Term, T ⊢ᵢ
          Formula.eq (consS t ρ₁ (k + 1)) (consS t ρ₂ (k + 1)) := fun _ => heq
      simp only [substF, slash_ex]
      constructor
      · rintro ⟨t, hDt, ht⟩
        refine ⟨t, hDt, ?_⟩
        rw [substFormula_upS]
        exact (slash_eq_congr T D a (k + 1) (consS t ρ₁) (consS t ρ₂) (hag' t) (heq' t)).mp
          (by rw [← substFormula_upS]; exact ht)
      · rintro ⟨t, hDt, ht⟩
        refine ⟨t, hDt, ?_⟩
        rw [substFormula_upS]
        exact (slash_eq_congr T D a (k + 1) (consS t ρ₁) (consS t ρ₂) (hag' t) (heq' t)).mpr
          (by rw [← substFormula_upS]; exact ht)
termination_by A => fdepth A
decreasing_by
  all_goals simp only [fdepth]
  all_goals omega


/-! ## ⭐⭐⭐ L2, y con ella la propiedad de disyunción -/

/-- **L2.** Toda derivación desde un contexto barrado barra su conclusión.

    ⚠️ El `∀ ρ` va **dentro** de la inducción, y ésa es toda la historia: en `intro_forall`
    la meta pide la hipótesis inductiva de la premisa **con otra sustitución**, y sin
    cuantificar sobre todas no hay manera. -/
theorem slash_of_derives (T : List Formula) (D : Term → Prop) (L : String → Nat → Bool)
    (hDfix : ∀ u : Term, D u → collapseT L u = u)
    (hDsub : ∀ (ρ : Subst), (∀ n, D (ρ n)) → ∀ t : Term, D (collapseT L (substT ρ t)))
    {Γ : List Formula} {f : Formula} (h : Γ ⊢ᵢ f) :
    ∀ ρ : Subst, (∀ n, D (ρ n)) →
      (∀ g, g ∈ Γ → Slash T D (collapseF L (substF ρ g))) →
      Slash T D (collapseF L (substF ρ f)) := by
  induction h with
  | hyp Γ' f' hIn => intro ρ hρ hall; exact hall f' hIn
  | intro_impl Γ' A B d ih =>
      intro ρ hρ hall
      refine (slash_impl T D (collapseF L (substF ρ A)) (collapseF L (substF ρ B))).mpr
        ⟨derives_empty_of_slashed T D L (Derivesᵢ.intro_impl Γ' A B d) ρ hall, fun ha => ?_⟩
      refine ih ρ hρ (fun g hg => ?_)
      rcases List.mem_cons.mp hg with rfl | hg'
      · exact ha
      · exact hall g hg'
  | elim_impl Γ' A B _ _ ih1 ih2 =>
      intro ρ hρ hall
      exact ((slash_impl T D _ _).mp (ih1 ρ hρ hall)).2 (ih2 ρ hρ hall)
  | intro_and Γ' A B _ _ ih1 ih2 =>
      intro ρ hρ hall; exact (slash_and T D _ _).mpr ⟨ih1 ρ hρ hall, ih2 ρ hρ hall⟩
  | elim_and_l Γ' A B _ ih => intro ρ hρ hall; exact ((slash_and T D _ _).mp (ih ρ hρ hall)).1
  | elim_and_r Γ' A B _ ih => intro ρ hρ hall; exact ((slash_and T D _ _).mp (ih ρ hρ hall)).2
  | intro_or_l Γ' A B _ ih => intro ρ hρ hall; exact (slash_or T D _ _).mpr (Or.inl (ih ρ hρ hall))
  | intro_or_r Γ' A B _ ih => intro ρ hρ hall; exact (slash_or T D _ _).mpr (Or.inr (ih ρ hρ hall))
  | elim_or Γ' A B C _ _ _ ih1 ih2 ih3 =>
      intro ρ hρ hall
      rcases (slash_or T D _ _).mp (ih1 ρ hρ hall) with ha | hb
      · refine ih2 ρ hρ (fun g hg => ?_)
        rcases List.mem_cons.mp hg with rfl | hg'
        · exact ha
        · exact hall g hg'
      · refine ih3 ρ hρ (fun g hg => ?_)
        rcases List.mem_cons.mp hg with rfl | hg'
        · exact hb
        · exact hall g hg'
  | intro_forall Γ' A d ih =>
      intro ρ hρ hall
      refine (slash_forall T D (collapseF L (substF (upS ρ) A))).mpr
        ⟨derives_empty_of_slashed T D L (Derivesᵢ.intro_forall Γ' A d) ρ hall, fun t hDt => ?_⟩
      rw [← hDfix t hDt, ← collapseF_subst, substFormula_upS]
      have hρ2 : ∀ n, D (consS t ρ n) := by
        intro n
        cases n with
        | zero => exact hDt
        | succ m => exact hρ m
      refine ih (consS t ρ) hρ2 (fun g hg => ?_)
      rcases List.mem_map.mp hg with ⟨y, hy, rfl⟩
      rw [substF_lift_consS]
      exact hall y hy
  | elim_forall Γ' A t _ ih =>
      intro ρ hρ hall
      rw [substF_substFormula, collapseF_subst]
      exact ((slash_forall T D _).mp (ih ρ hρ hall)).2
        (collapseT L (substT ρ t)) (hDsub ρ hρ t)
  | intro_ex Γ' A t _ ih =>
      intro ρ hρ hall
      refine (slash_ex T D (collapseF L (substF (upS ρ) A))).mpr
        ⟨collapseT L (substT ρ t), hDsub ρ hρ t, ?_⟩
      rw [← collapseF_subst, ← substF_substFormula]
      exact ih ρ hρ hall
  | elim_ex Γ' A B _ _ ih1 ih2 =>
      intro ρ hρ hall
      rcases (slash_ex T D _).mp (ih1 ρ hρ hall) with ⟨t, hDt, ht⟩
      have hρ2 : ∀ n, D (consS t ρ n) := by
        intro n
        cases n with
        | zero => exact hDt
        | succ m => exact hρ m
      have ht2 : Slash T D (collapseF L (substF (consS t ρ) A)) := by
        rw [← substFormula_upS, collapseF_subst, hDfix t hDt]
        exact ht
      have h2 : Slash T D (collapseF L (substF (consS t ρ) (liftFormula 0 B))) := by
        refine ih2 (consS t ρ) hρ2 (fun g hg => ?_)
        rcases List.mem_cons.mp hg with rfl | hg'
        · exact ht2
        · rcases List.mem_map.mp hg' with ⟨y, hy, rfl⟩
          rw [substF_lift_consS]
          exact hall y hy
      rwa [substF_lift_consS] at h2
  | bot_elim Γ' A _ ih => intro ρ hρ hall; exact ((slash_bottom T D).mp (ih ρ hρ hall)).elim
  | weakening Γ' Γ'' f' _ hSub ih =>
      intro ρ hρ hall; exact ih ρ hρ (fun g hg => hall g (hSub g hg))
  | rewrite_at Γ' f f' p sub sub' _ hget hrule heq ih =>
      intro ρ hρ hall
      have ihc : Slash T D (substF (collapseS L ρ) (collapseF L f)) := by
        rw [← collapseF_substF]; exact ih ρ hρ hall
      have hget2 : getAt? (collapseF L f) p = some (collapseF L sub) := by
        rw [collapse_getAt?, hget]; rfl
      rw [heq, collapseF_substF, ← collapse_replaceAt]
      exact (slash_rewrite T D p (collapseF L sub) (collapseF L sub')
        (collapse_localRule L hrule) (collapseF L f) (collapseS L ρ) hget2).mp ihc
  | refl Γ' t =>
      intro ρ hρ hall
      exact (slash_eq T D _ _).mpr (Derivesᵢ.refl _ (collapseT L (substT ρ t)))
  | subst Γ' t₁ t₂ A _ _ ih1 ih2 =>
      intro ρ hρ hall
      have heq : T ⊢ᵢ Formula.eq (collapseT L (substT ρ t₁)) (collapseT L (substT ρ t₂)) :=
        (slash_eq T D _ _).mp (ih1 ρ hρ hall)
      have h1 := ih2 ρ hρ hall
      rw [substF_substFormula, collapseF_subst, collapseF_substF, collapseS_upS,
        substFormula_upS] at h1 ⊢
      exact (slash_eq_congr T D (collapseF L A) 0
        (consS (collapseT L (substT ρ t₁)) (collapseS L ρ))
        (consS (collapseT L (substT ρ t₂)) (collapseS L ρ))
        (fun n hn => by cases n with
                        | zero => exact absurd rfl hn
                        | succ m => rfl) heq).mp h1

/-! ## 🏁 Las dos propiedades, y la separación

    ## 🔁 La barra es relativa a la TEORÍA (etapa 1 de H3ter, 2026-09-18)

  `Slash T D f` lleva la teoría como parámetro. Antes estaba clavada a `[]`, y eso bastaba
  para H3bis —que es el caso `T = []`— pero **hacía imposible enunciar la DP para HA**:
  `Slash g` para un axioma de HA significaba «derivable desde nada», que es falso.

  Con el parámetro, el teorema general es

  > `disjunction_property_of_slashed : (∀ g ∈ T, Slash T D g) → T ⊢ᵢ A ∨ B → T ⊢ᵢ A ∨ T ⊢ᵢ B`

  y H3bis es su instancia `T = []`, donde la hipótesis es **vacía**. H3ter es la instancia
  `T = ctx insts`, y lo único que le falta es esa hipótesis: **`ha_ctx_slashed`**.

  ⚠️ Un detalle que sólo aparece al parametrizar: el caso base de `cut_context` deja de ser
  la identidad y necesita **debilitamiento** de `[]` a `T`. Con `T = []` era `id`, y por eso
  no se veía.

  ## ⛔ Y lo que la etapa 1 destapó: `ha_ctx_slashed` NO sale con esta barra

  La cláusula `∀` de esta barra cuantifica sobre **todos los términos**, variables libres
  incluidas. Y en `coreAxioms` está

  ```lean
  ax19_lt_trichotomy : ∀a ∀b (a < b  ∨  a = b  ∨  b < a)
  ```

  Barrarlo exigiría que para **cada** par de términos una rama fuese derivable. Para dos
  variables libres no lo es ninguna — y si lo fuera, por generalización HA probaría
  `∀x∀y. x<y`, que `derivesI_soundness` refuta. Igual con `ax13_lt_def`, cuyo `⇔` tiene un
  `∃` a la derecha: barrar un existencial pide **testigo**.

  🔑 No es un defecto: **la barra de Kleene para una TEORÍA cuantifica sobre términos
  cerrados**, no sobre todos. La nuestra cuantifica sobre todos porque para la lógica pura
  eso funciona y da más. Para HA hace falta la restricción — y ahí es donde entra
  `closed_term_eq_numeral` (`HA/Numerals.lean`).

  ⛔ **Y hay una segunda pieza, que el 2026-09-18 resultó obligatoria.** Restringir la barra
  no basta, porque `Term` es GENÉRICA: `Term.func s ts` admite cualquier `s`, y
  `elim_forall` instancia con cualquier término. Medido en `sondeos/junk_probe.lean`:

  ```lean
  ctx [] ⊢ᵢ (lt foo bar ∨ foo = bar ∨ lt bar foo)      -- derivable, con foo, bar ajenos
  ```

  y ninguna rama lo es ⇒ **HA sobre la sintaxis genérica no tiene la propiedad de
  disyunción**. `D` dice sobre qué cuantifica la barra; hace falta además decir **qué usa la
  derivación por dentro**. Ver `doc/HALLAZGO-SINTAXIS-GENERICA-2026-09-18.md`.

  📏 **Medido sobre los 34 axiomas de `coreAxioms`**: 25 tienen matriz atómica (la barra
  se reduce a derivabilidad ⇒ `specI`), ~4 son `⇒`/`⇔` con partes atómicas, y **5 piden
  decidir en el meta y construir la derivación** (`ax19`, `ax21`, `ax13`, `ax_L3`, `ax29`).

  ## ⛔ Lo que esto NO es, y decirlo importa

    Las dos propiedades se demuestran sobre **CONTEXTO VACÍO**: son las de la **lógica**
    `⊢ᵢ`, no las de **HA**.

    Para HA **no se siguen**. Las instancias de inducción viven en `HA.ctx` (ADR-016), y L2
    sólo da la barra de la conclusión **si cada hipótesis del contexto está barrada**. Barrar
    el esquema de inducción es precisamente el caso difícil, y no está hecho.

    🔁 Desde el 2026-09-18 el enunciado GENERAL sí existe: `HA.qDisjunctionProperty` da la
    DP para cualquier teoría de Q⁺⁺ **con los axiomas barrados como hipótesis**. Eso no cierra
    nada de HA por sí solo — descargar esa hipótesis para `coreAxioms` más el esquema de
    inducción **es** la etapa 3, y sigue pendiente. Lo que cambia es que ya no hay incógnita
    de método entre una cosa y la otra.

    ⚠️ Es la misma reserva que lleva escrita `Calculus/Consistency.lean` para `consistI_syn`
    — y esa se escribió el mismo día que ésta se olvidó. Queda anotado: **el listón sube
    igual para los resultados que gustan.** De un enunciado sobre `[]` a uno sobre `HA.ctx`
    hay exactamente el trabajo que separa M-9 de una afirmación de más.

    Lo que SÍ queda demostrado, y es lo que sostiene la tesis: **`⊢ᵢ` y `⊢₀` no son el
    mismo cálculo** (`derivesI_ne_derives0`). Eso sí es sobre contexto vacío y sí es un
    teorema. -/

/-- 🏁 **LA PROPIEDAD DE DISYUNCIÓN, relativa a una teoría barrada y a un dominio.**

    ⭐ **La forma (c)**: la barra se afirma de la instancia **COLAPSADA**, y por eso el
    enunciado pide que `A ∨ B` sea **punto fijo** de `collapseF L ∘ substF ρ₀` — que es la
    manera precisa de decir «cerrada y del lenguaje», en una sola hipótesis en vez de dos
    predicados. Sin ella el teorema de Kleene no es cierto: `sondeos/junk_probe.lean` da un
    contraejemplo con símbolos ajenos.

    ⛔ **No es la de HA**: ver la reserva de la sección. -/
theorem disjunction_property_of_slashed (T : List Formula) (D : Term → Prop)
    (L : String → Nat → Bool)
    (hDfix : ∀ u : Term, D u → collapseT L u = u)
    (hDsub : ∀ (ρ : Subst), (∀ n, D (ρ n)) → ∀ t : Term, D (collapseT L (substT ρ t)))
    (ρ₀ : Subst) (hρ₀ : ∀ n, D (ρ₀ n))
    (hT : ∀ g, g ∈ T → Slash T D (collapseF L (substF ρ₀ g)))
    {A B : Formula}
    (hAB : collapseF L (substF ρ₀ (Formula.or A B)) = Formula.or A B)
    (h : T ⊢ᵢ Formula.or A B) :
    (T ⊢ᵢ A) ∨ (T ⊢ᵢ B) := by
  have hs := slash_of_derives T D L hDfix hDsub h ρ₀ hρ₀ hT
  rw [hAB] at hs
  rcases (slash_or T D A B).mp hs with ha | hb
  · exact Or.inl (slash_derives T D A ha)
  · exact Or.inr (slash_derives T D B hb)

/-- 🏁 **H3bis**: el caso `T = []`, `D` total y `L` total.

    ⭐ Con la signatura TOTAL el colapso es la identidad (`collapseF_trivial`) y con `D`
    total la clausura es trivial, así que **el enunciado vuelve a ser literalmente el de
    antes**: la forma (c) generaliza H3bis, no lo debilita. -/
theorem disjunction_property {A B : Formula}
    (h : ([] : List Formula) ⊢ᵢ Formula.or A B) :
    (([] : List Formula) ⊢ᵢ A) ∨ (([] : List Formula) ⊢ᵢ B) := by
  refine disjunction_property_of_slashed [] (fun _ => True) (fun _ _ => true)
    (fun u _ => collapseT_trivial _ (fun _ _ => rfl) u) (fun _ _ _ => trivial)
    Term.var (fun _ => trivial) (fun _ hg => absurd hg List.not_mem_nil) ?_ h
  rw [substF_id]
  exact collapseF_trivial _ (fun _ _ => rfl) _

/-- 🏁 **LA PROPIEDAD DE EXISTENCIA** — de un existencial demostrado sale un TESTIGO, **y el
    testigo está en el dominio**.

    Es la sombra sintáctica de la realizabilidad (ADR-016): el testigo `t` es el cómputo que
    el lado Peano del espejo tendría que ejecutar. Con `D = ClosedQTerm` ese testigo será,
    además, demostrablemente igual a un numeral (`closed_term_eq_numeral`). -/
theorem existence_property_of_slashed (T : List Formula) (D : Term → Prop)
    (L : String → Nat → Bool)
    (hDfix : ∀ u : Term, D u → collapseT L u = u)
    (hDsub : ∀ (ρ : Subst), (∀ n, D (ρ n)) → ∀ t : Term, D (collapseT L (substT ρ t)))
    (ρ₀ : Subst) (hρ₀ : ∀ n, D (ρ₀ n))
    (hT : ∀ g, g ∈ T → Slash T D (collapseF L (substF ρ₀ g)))
    {A : Formula}
    (hA : collapseF L (substF ρ₀ (Formula.ex A)) = Formula.ex A)
    (h : T ⊢ᵢ Formula.ex A) :
    ∃ t : Term, And (D t) (T ⊢ᵢ substFormula 0 t A) := by
  have hs := slash_of_derives T D L hDfix hDsub h ρ₀ hρ₀ hT
  rw [hA] at hs
  rcases (slash_ex T D A).mp hs with ⟨t, hDt, ht⟩
  exact ⟨t, hDt, slash_derives T D _ ht⟩

/-- 🏁 **H3bis**: el caso `T = []`, `D` total y `L` total. -/
theorem existence_property {A : Formula}
    (h : ([] : List Formula) ⊢ᵢ Formula.ex A) :
    ∃ t : Term, ([] : List Formula) ⊢ᵢ substFormula 0 t A := by
  have hfix : collapseF (fun _ _ => true) (substF Term.var (Formula.ex A)) = Formula.ex A := by
    rw [substF_id]
    exact collapseF_trivial _ (fun _ _ => rfl) _
  rcases existence_property_of_slashed [] (fun _ => True) (fun _ _ => true)
    (fun u _ => collapseT_trivial _ (fun _ _ => rfl) u) (fun _ _ _ => trivial)
    Term.var (fun _ => trivial) (fun _ hg => absurd hg List.not_mem_nil) hfix h
    with ⟨t, _, ht⟩
  exact ⟨t, ht⟩

/-- `⊢ᵢ` no prueba `¬P` — la otra mitad de la separación. Misma vía sintáctica que
    `notP_syn`, con la valuación `true` en vez de `false`. -/
theorem notNotP_syn : ¬ (([] : List Formula) ⊢ᵢ neg (Formula.atom "P" [])) := by
  intro h
  have hc := FOL.NDtoLK0.ndToLK
    (FOL.Derives2.derives0_iff_derives2.mp (derivesI_to_derives0 h))
  rcases FOL.Finitary0.lkc_tval hc true
    (fun _ hx => absurd hx List.not_mem_nil) with ⟨x, hx, hv⟩
  cases hx with
  | head => exact absurd hv (by simp [FOL.Finitary0.tval, neg])
  | tail _ hm => exact absurd hm List.not_mem_nil

/-- 🏁🏁🏁 **LA SEPARACIÓN: `⊢ᵢ` NO es `⊢₀`.**

    El primer teorema de este proyecto que **falla clásicamente**. Hasta hoy los 22
    teoremas de PeanoRF valían palabra por palabra para `⊢₀`: sustituyendo `⊢ᵢ` por `⊢₀` en
    todo el árbol, todo seguía compilando, y la tesis —«PeanoRF es HA y no PA»— la sostenían
    la elección de cálculo y el gate, no una demostración.

    Ya no. `P ∨ ¬P` es derivable en `⊢₀` (`FOL.Propositional0.derives0_em_ctx`, y **sin
    `Classical.choice`**) y **no lo es en `⊢ᵢ`**: por la propiedad de disyunción tendría que
    serlo `P` o `¬P`, y ninguna lo es. -/
theorem derivesI_ne_derives0 :
    ∃ φ : Formula, (([] : List Formula) ⊢₀ φ) ∧ ¬ (([] : List Formula) ⊢ᵢ φ) := by
  refine ⟨Formula.or (Formula.atom "P" []) (neg (Formula.atom "P" [])),
    FOL.Propositional0.derives0_em_ctx [] (Formula.atom "P" []), ?_⟩
  intro h
  rcases disjunction_property h with hP | hnP
  · exact notP_syn hP
  · exact notNotP_syn hnP

end PeanoRF.Calculus
