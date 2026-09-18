/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.Calculus.DerivesI
import PeanoRF.Calculus.Subst

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
def collapseT (L : String → Nat → Bool) : Term → Term
  | .var n     => .var n
  | .func s ts => if L s ts.length then .func s (collapseTs L ts) else zero

def collapseTs (L : String → Nat → Bool) : List Term → List Term
  | []      => []
  | t :: ts => collapseT L t :: collapseTs L ts
end

/-- En las fórmulas sólo se colapsan los TÉRMINOS. Un predicado ajeno no da problema: la
    barra de un átomo es su derivabilidad, sin testigo. -/
def collapseF (L : String → Nat → Bool) : Formula → Formula
  | .bottom    => .bottom
  | .atom p ts => .atom p (collapseTs L ts)
  | .eq t u    => .eq (collapseT L t) (collapseT L u)
  | .impl a b  => .impl (collapseF L a) (collapseF L b)
  | .forall a  => .forall (collapseF L a)
  | .and a b   => .and (collapseF L a) (collapseF L b)
  | .or a b    => .or (collapseF L a) (collapseF L b)
  | .ex a      => .ex (collapseF L a)

/-! ## 0 · Las longitudes, que es lo que la ARIDAD obliga a mirar

    ⛔ Medido el 2026-09-18 (`sondeos/collapse_parallel_probe.lean`): una signatura que sólo
    mira el NOMBRE del símbolo **no basta**. `func add_sym [zero]` —`+` con UN argumento— es
    un término legítimo de la sintaxis, cerrado y con símbolos de Q⁺⁺, pero Q⁺⁺ no tiene
    ningún axioma sobre él, luego no es demostrablemente igual a ningún numeral. Si el
    colapso lo deja pasar, el dominio de la barra de H3ter no se puede cerrar.

    ⇒ `L` toma también la **aridad**, y el precio son estos tres lemas. -/

theorem collapseTs_length (L : String → Nat → Bool) :
    ∀ ts : List Term, (collapseTs L ts).length = ts.length := by
  intro ts
  induction ts with
  | nil => rfl
  | cons t ts0 ih => simp only [collapseTs, List.length_cons, ih]

theorem liftTerms_length : ∀ (c : Nat) (ts : List Term),
    (liftTerms c ts).length = ts.length := by
  intro c ts
  induction ts with
  | nil => rfl
  | cons t ts0 ih => simp only [liftTerms, List.length_cons, ih]

theorem substTerms_length : ∀ (v : Nat) (s : Term) (ts : List Term),
    (substTerms v s ts).length = ts.length := by
  intro v s ts
  induction ts with
  | nil => rfl
  | cons t ts0 ih => simp only [substTerms, List.length_cons, ih]

/-! ## 1 · Conmuta con el levantamiento -/

mutual
theorem collapseT_lift (L : String → Nat → Bool) : ∀ (c : Nat) (t : Term),
    collapseT L (liftTerm c t) = liftTerm c (collapseT L t) := by
  intro c t
  cases t with
  | var n => by_cases h : n < c <;> simp [collapseT, liftTerm, h]
  | func s ts =>
      by_cases h : L s ts.length
      · simp only [liftTerm, collapseT, liftTerms_length, if_pos h]
        exact congrArg _ (collapseTs_lift L c ts)
      · simp [liftTerm, collapseT, liftTerms_length, if_neg h, zero, liftTerms]

theorem collapseTs_lift (L : String → Nat → Bool) : ∀ (c : Nat) (ts : List Term),
    collapseTs L (liftTerms c ts) = liftTerms c (collapseTs L ts) := by
  intro c ts
  cases ts with
  | nil => rfl
  | cons t ts' =>
      simp only [liftTerms, collapseTs, List.cons.injEq]
      exact ⟨collapseT_lift L c t, collapseTs_lift L c ts'⟩
end

theorem collapseF_lift (L : String → Nat → Bool) : ∀ (f : Formula) (c : Nat),
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
theorem collapseT_subst (L : String → Nat → Bool) : ∀ (v : Nat) (s t : Term),
    collapseT L (substTerm v s t) = substTerm v (collapseT L s) (collapseT L t) := by
  intro v s t
  cases t with
  | var n =>
      by_cases h1 : n = v
      · simp [collapseT, substTerm, h1]
      · by_cases h2 : n > v <;> simp [collapseT, substTerm, h1, h2]
  | func c ts =>
      by_cases h : L c ts.length
      · simp only [substTerm, collapseT, substTerms_length, if_pos h]
        exact congrArg _ (collapseTs_subst L v s ts)
      · simp [substTerm, collapseT, substTerms_length, if_neg h, zero, substTerms]

theorem collapseTs_subst (L : String → Nat → Bool) : ∀ (v : Nat) (s : Term) (ts : List Term),
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
theorem collapseF_subst (L : String → Nat → Bool) : ∀ (f : Formula) (v : Nat) (s : Term),
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

theorem collapse_getAt? (L : String → Nat → Bool) : ∀ (p : Pos) (f : Formula),
    getAt? (collapseF L f) p = (getAt? f p).map (collapseF L) := by
  intro p
  induction p with
  | root => intro f; simp [getAt?]
  | left p' ih => intro f; cases f <;> simp only [getAt?, collapseF, ih] <;> rfl
  | right p' ih => intro f; cases f <;> simp only [getAt?, collapseF, ih] <;> rfl
  | body p' ih => intro f; cases f <;> simp only [getAt?, collapseF, ih] <;> rfl

theorem collapse_replaceAt (L : String → Nat → Bool) : ∀ (p : Pos) (f newSub : Formula),
    replaceAt (collapseF L f) p (collapseF L newSub) = collapseF L (replaceAt f p newSub) := by
  intro p
  induction p with
  | root => intro f n; simp [replaceAt]
  | left p' ih => intro f n; cases f <;> simp only [replaceAt, collapseF, ih]
  | right p' ih => intro f n; cases f <;> simp only [replaceAt, collapseF, ih]
  | body p' ih => intro f n; cases f <;> simp only [replaceAt, collapseF, ih]

theorem collapse_localRule (L : String → Nat → Bool) {A B : Formula} (h : LocalRule A B) :
    LocalRule (collapseF L A) (collapseF L B) := by
  cases h with
  | commuteImpl A B C =>
      exact LocalRule.commuteImpl (collapseF L A) (collapseF L B) (collapseF L C)

theorem map_collapse_lift (L : String → Nat → Bool) (Γ : List Formula) :
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
theorem derivesI_collapse (L : String → Nat → Bool) {Γ : List Formula} {φ : Formula}
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

/-! ## 5 · El colapso contra la sustitución PARALELA

    Lo pide el caso `rewrite_at` de L2 en su **forma (c)**: con el colapso delante hay que
    poder mover `collapseF L` al otro lado de `substF ρ` para aplicar `slash_rewrite`, que
    está enunciada sobre `substF`. Medido en `sondeos/collapse_parallel_probe.lean`. -/

/-- El colapso de una sustitución, punto a punto. -/
def collapseS (L : String → Nat → Bool) (ρ : Subst) : Subst := fun n => collapseT L (ρ n)

/-- ⭐ El caso que podía fallar: bajo la ligadura. En el índice 0 es `rfl`, y en `n+1` es
    exactamente `collapseT_lift`. -/
theorem collapseS_upS (L : String → Nat → Bool) (ρ : Subst) :
    collapseS L (upS ρ) = upS (collapseS L ρ) := by
  funext n
  cases n with
  | zero => rfl
  | succ m => exact collapseT_lift L 0 (ρ m)

mutual
theorem collapseT_substT (L : String → Nat → Bool) : ∀ (ρ : Subst) (t : Term),
    collapseT L (substT ρ t) = substT (collapseS L ρ) (collapseT L t) := by
  intro ρ t
  cases t with
  | var n => rfl
  | func s ts =>
      by_cases h : L s ts.length
      · simp only [substT, collapseT, substTs_length, if_pos h]
        exact congrArg _ (collapseTs_substTs L ρ ts)
      · simp [substT, collapseT, substTs_length, if_neg h, zero, substTs]

theorem collapseTs_substTs (L : String → Nat → Bool) : ∀ (ρ : Subst) (ts : List Term),
    collapseTs L (substTs ρ ts) = substTs (collapseS L ρ) (collapseTs L ts) := by
  intro ρ ts
  cases ts with
  | nil => rfl
  | cons t ts0 =>
      simp only [substTs, collapseTs, List.cons.injEq]
      exact ⟨collapseT_substT L ρ t, collapseTs_substTs L ρ ts0⟩
end

theorem collapseF_substF (L : String → Nat → Bool) : ∀ (f : Formula) (ρ : Subst),
    collapseF L (substF ρ f) = substF (collapseS L ρ) (collapseF L f) := by
  intro f
  induction f with
  | bottom => intro _; rfl
  | atom p ts => intro ρ; simp only [substF, collapseF, collapseTs_substTs]
  | eq t u => intro ρ; simp only [substF, collapseF, collapseT_substT]
  | impl a b iha ihb => intro ρ; simp only [substF, collapseF, iha, ihb]
  | and a b iha ihb => intro ρ; simp only [substF, collapseF, iha, ihb]
  | or a b iha ihb => intro ρ; simp only [substF, collapseF, iha, ihb]
  | «forall» a ih => intro ρ; simp only [substF, collapseF, ih, collapseS_upS]
  | ex a ih => intro ρ; simp only [substF, collapseF, ih, collapseS_upS]

/-! ## 6 · La signatura TOTAL no colapsa nada

    Es lo que mantiene H3bis exactamente donde estaba: la propiedad de disyunción de la
    LÓGICA es la instancia de la forma (c) con `L = fun _ _ => true`, donde el colapso es la
    identidad y el enunciado vuelve a ser el de antes, literalmente. -/

mutual
theorem collapseT_trivial (L : String → Nat → Bool) (hL : ∀ s n, L s n = true) :
    ∀ t : Term, collapseT L t = t := by
  intro t
  cases t with
  | var n => rfl
  | func s ts =>
      simp only [collapseT, if_pos (hL s ts.length)]
      exact congrArg _ (collapseTs_trivial L hL ts)

theorem collapseTs_trivial (L : String → Nat → Bool) (hL : ∀ s n, L s n = true) :
    ∀ ts : List Term, collapseTs L ts = ts := by
  intro ts
  cases ts with
  | nil => rfl
  | cons t ts0 =>
      simp only [collapseTs, List.cons.injEq]
      exact ⟨collapseT_trivial L hL t, collapseTs_trivial L hL ts0⟩
end

theorem collapseF_trivial (L : String → Nat → Bool) (hL : ∀ s n, L s n = true) :
    ∀ f : Formula, collapseF L f = f := by
  intro f
  induction f with
  | bottom => rfl
  | atom p ts => simp only [collapseF, collapseTs_trivial L hL]
  | eq t u => simp only [collapseF, collapseT_trivial L hL]
  | impl a b iha ihb => simp only [collapseF, iha, ihb]
  | and a b iha ihb => simp only [collapseF, iha, ihb]
  | or a b iha ihb => simp only [collapseF, iha, ihb]
  | «forall» a ih => simp only [collapseF, ih]
  | ex a ih => simp only [collapseF, ih]

/-! ## 7 · Términos ANCLADOS — el dominio de la barra, definido por sus clausuras

    ⭐ La forma (c) de L2 no pide que el dominio sea una lista de términos: pide **dos
    clausuras**. Así que lo más barato es definir el dominio POR ellas — y entonces valen
    para cualquier signatura, sin una inducción por lenguaje.

    `Grounded L t` dice las dos cosas a la vez: `t` no tiene símbolos fuera de `L` (el
    colapso lo fija) y no tiene variables libres (ninguna sustitución lo toca). -/

/-- El colapso es **idempotente**. Sale sin hipótesis sobre `L`: en la rama negativa los dos
    lados dan `zero` se conserve `0` o no. -/
theorem collapseT_zero (L : String → Nat → Bool) : collapseT L zero = zero := by
  by_cases h : L zero_sym 0
  · simp only [zero, collapseT, List.length_nil, if_pos h, collapseTs]
  · simp only [zero, collapseT, List.length_nil, if_neg h]

mutual
theorem collapseT_idem (L : String → Nat → Bool) : ∀ t : Term,
    collapseT L (collapseT L t) = collapseT L t := by
  intro t
  cases t with
  | var n => rfl
  | func s ts =>
      by_cases h : L s ts.length
      · simp only [collapseT, if_pos h, collapseTs_length]
        exact congrArg _ (collapseTs_idem L ts)
      · simp only [collapseT, if_neg h]
        exact collapseT_zero L

theorem collapseTs_idem (L : String → Nat → Bool) : ∀ ts : List Term,
    collapseTs L (collapseTs L ts) = collapseTs L ts := by
  intro ts
  cases ts with
  | nil => rfl
  | cons t ts0 =>
      simp only [collapseTs, List.cons.injEq]
      exact ⟨collapseT_idem L t, collapseTs_idem L ts0⟩
end

/-- **El dominio, definido por sus clausuras.** Sin símbolos fuera de `L` y sin variables
    libres, dicho de la única manera que L2 va a usar. -/
def Grounded (L : String → Nat → Bool) (t : Term) : Prop :=
  And (collapseT L t = t) (∀ ρ : Subst, substT ρ t = t)

theorem grounded_zero (L : String → Nat → Bool) : Grounded L zero :=
  ⟨collapseT_zero L, fun _ => rfl⟩

/-- Lo que L2 pide en `intro_forall`. Es la primera componente, tal cual. -/
theorem grounded_fix (L : String → Nat → Bool) {u : Term} (h : Grounded L u) :
    collapseT L u = u := h.1

/-- ⭐⭐ **Lo que L2 pide en `elim_forall`.** Con `ρ` anclada, el colapso de `substT ρ t` está
    anclado **para `t` arbitrario**: el colapso mata los símbolos ajenos y `ρ` mata las
    variables. -/
theorem grounded_collapse_subst (L : String → Nat → Bool) (ρ : Subst)
    (hρ : ∀ n, Grounded L (ρ n)) : ∀ t : Term, Grounded L (collapseT L (substT ρ t)) := by
  intro t
  refine ⟨collapseT_idem L _, fun τ => ?_⟩
  have hfix : compS τ (collapseS L ρ) = collapseS L ρ := by
    funext n
    show substT τ (collapseT L (ρ n)) = collapseT L (ρ n)
    rw [(hρ n).1]
    exact (hρ n).2 τ
  rw [collapseT_substT, substT_comp, hfix, ← collapseT_substT]

/-- Un término anclado no se levanta. -/
theorem grounded_liftTerm (L : String → Nat → Bool) {t : Term} (h : Grounded L t) (c : Nat) :
    liftTerm c t = t := by
  rw [← substT_liftS c t]; exact h.2 (liftS c)

/-- Ni se sustituye. Las dos son la segunda componente vista con otras gafas, y son las que
    hacen manejables los cálculos de de Bruijn sobre términos del dominio. -/
theorem grounded_substTerm (L : String → Nat → Bool) {t : Term} (h : Grounded L t)
    (v : Nat) (s : Term) : substTerm v s t = t := by
  rw [← substT_singleS v s t]; exact h.2 (singleS v s)

end PeanoRF.Calculus