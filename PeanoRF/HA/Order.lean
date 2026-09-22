/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.HA.SlashAxioms

/-! # El ORDEN de Q⁺⁺ sobre términos ANCLADOS — y lo que se creía que faltaba

  Hasta el 2026-09-22 el proyecto trataba el orden de Q⁺⁺ como algo que sólo se manejaba
  **sobre numerales**: `numeralI_lt`, `numeralI_ne`, `numeralI_not_lt`, `addI_succ_ne`.
  Para un término cualquiera —un `√n̄`, un `/₂n̄`— no había nada, y ADR-037 dedujo de ahí que
  los símbolos «caracterizados por propiedades» no se dejaban despejar sin inducción.

  ⛔ **Eso era falso, y este módulo es la medida.** El orden de Q⁺⁺ es **total** (`ax19`) y
  su `<` está **definido por la resta** (`ax13`), y con esas dos cosas todo lo que hace
  falta sale **sin inducción en el objeto y sin cancelación**:

  | | |
  |---|---|
  | `exI_of_ltI` / `ltI_of_add` | las dos direcciones de `ax13` para términos anclados |
  | `notI_lt_zero` | **nada es menor que cero** — `t + σk = 0` choca con `ax5` + `ax2` |
  | ⭐⭐ `zeroI_or_succ` | **todo término anclado es `0` o un sucesor** |
  | ⭐ `ltI_add_right` | monotonía estricta de `+` |
  | ⭐⭐ `ltI_mul_two` | monotonía por `2̄`, **sin transitividad** |
  | ⭐ `notI_add_succ_self` | ningún término anclado cumple `x + σy = x` |
  | `ltI_trans` | transitividad |

  ## ⭐⭐ `zeroI_or_succ`: lo que Robinson Q POSTULA, aquí se DERIVA

  El axioma 3 de Q es «todo `x` es `0` o un sucesor». `coreAxioms` **no lo tiene**, y de esa
  ausencia venía la impresión de que sin él no se despeja de una caracterización. Sale de la
  tricotomía: la rama `t < 0` la refuta `notI_lt_zero`, y la rama `0 < t` da el testigo por
  la dirección ⇒ de `ax13` más `0 + x = x`.

  ⚠️ `0 + x = x` NO es `zero_add`. Aquél cuantifica sobre `x` y por eso pide una instancia
  de inducción; aquí el término está **fijo**, y basta `ax6` + `ax4`.

  ## 🔑 El truco que evita la transitividad

  Para `a < b ⇒ a·2̄ < b·2̄` lo natural sería encadenar `a+a < b+a < b+b`. No hace falta: de
  `y + σj = k̄` se **calcula** `k̄·2̄ = y·2̄ + σ(σj + j)`, y eso es ya exactamente la forma que
  `ax13` pide. Menos piezas y menos hipótesis.

  ## ⚠️ Por qué todo pide `Grounded`

  Los axiomas se instancian con `specI`, y al cruzar el binder de `∃` de `ax13` los términos
  se **levantan**. Para numerales eso lo deshacen `liftTerm_numeralM`/`substTerm_numeralM`;
  para un término cualquiera lo deshacen las **dos clausuras del dominio**
  (`grounded_liftTerm`, `grounded_substTerm`), que es justo lo que `Grounded` es.

  Y varios lemas piden además que el contexto sea invariante bajo levantamiento (`hlift`):
  dentro de `elim_ex` el contexto se levanta y los axiomas tienen que seguir estando.
-/

namespace PeanoRF.HA

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open PeanoRF.Calculus

set_option autoImplicit false
set_option linter.unusedSimpArgs false

variable {Γ : List Formula}

/-- Pertenencia a `arithAxioms` sin escribir la cadena de `tail` a mano. -/
local macro "memA" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

/-! ## 1 · Los tres axiomas del orden, accesibles -/

theorem ax13I (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g) : Γ ⊢ᵢ ax13_lt_def :=
  hΓ ax13_lt_def (by memA)

theorem ax18I (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g) : Γ ⊢ᵢ ax18_lt_irrefl :=
  hΓ ax18_lt_irrefl (by memA)

theorem ax19I (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g) : Γ ⊢ᵢ ax19_lt_trichotomy :=
  hΓ ax19_lt_trichotomy (by memA)

/-! ## 2 · La dirección ⇒ de `ax13`, y con ella `¬(t < 0)`

    ⭐ **Es la pieza que abre todo lo demás.** Con ella la tricotomía se vuelve utilizable
    sobre términos y no sólo sobre numerales. -/

/-- La dirección ⇒ de `ax13` para términos anclados. -/
theorem exI_of_ltI (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (L : String → Nat → Bool) {a b : Term} (ha : Grounded L a) (hb : Grounded L b) :
    Γ ⊢ᵢ Formula.impl (lt a b)
      (Formula.ex (Formula.eq (add a (succ (Term.var 0))) b)) := by
  have hi := specI (specI (ax13I hΓ) a) b
  have h2 := Derivesᵢ.elim_and_l _ _ _ hi
  simpa [ax13_lt_def, forall_2, substFormula, substTerms, substTerm, lt, add, succ,
    iff, grounded_liftTerm L ha, grounded_liftTerm L hb,
    grounded_substTerm L ha, grounded_substTerm L hb] using h2

/-- ⭐ **Nada es menor que cero.** `t + σk = 0` choca con `ax5` (que lo vuelve `σ(t+k)`) y
    `ax2` (que dice que ningún sucesor es cero). Sin inducción. -/
theorem notI_lt_zero (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (hlift : Γ.map (liftFormula 0) = Γ)
    (L : String → Nat → Bool) {t : Term} (ht : Grounded L t) :
    Γ ⊢ᵢ Formula.impl (lt t zero) Formula.bottom := by
  refine Derivesᵢ.intro_impl _ (lt t zero) Formula.bottom ?_
  have hex := Derivesᵢ.elim_impl _ _ _
    (Derivesᵢ.weakening _ _ _ (exI_of_ltI hΓ L ht (grounded_zero L))
      (fun _ hz => List.Mem.tail _ hz))
    (Derivesᵢ.hyp _ _ (List.Mem.head _))
  refine Derivesᵢ.elim_ex _ _ _ hex ?_
  simp only [List.map_cons, hlift, liftFormula, liftTerms, lt, zero,
    grounded_liftTerm L ht]
  have hΓ1 : ∀ g, List.Mem g arithAxioms →
      (Formula.eq (add t (succ (Term.var 0))) zero :: lt t zero :: Γ) ⊢ᵢ g :=
    hyps_cons (hyps_cons hΓ (lt t zero)) (Formula.eq (add t (succ (Term.var 0))) zero)
  have hA : (Formula.eq (add t (succ (Term.var 0))) zero :: lt t zero :: Γ) ⊢ᵢ
      Formula.eq (add t (succ (Term.var 0))) zero := Derivesᵢ.hyp _ _ (List.Mem.head _)
  exact Derivesᵢ.elim_impl _ _ _
    (succI_ne_zero hΓ1 (add t (Term.var 0)))
    (eqI_trans (eqI_symm (addI_succ hΓ1 t (Term.var 0))) hA)


/-! ## 3 · ⭐⭐ «Todo término es 0 o sucesor» — que en Q es un AXIOMA

    Robinson Q lo postula (su axioma 3). `coreAxioms` **no lo tiene**, y ADR-037 dio por
    hecho que sin él no se despeja de una caracterización. Pero **se deriva**: la
    tricotomía contra `0` da tres ramas, la primera la refuta `notI_lt_zero`, y la tercera
    da el testigo por la dirección ⇒ de `ax13` más `0 + x = x` (que sale de `ax6` + `ax4`,
    sin inducción). -/

/-- `0 + t = t`, por conmutatividad y `ax4`. Sin inducción: `zero_add` del proyecto pide una
    instancia de inducción porque cuantifica sobre `x`; para un `t` FIJO basta `ax6`. -/
theorem zeroI_add (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g) (t : Term) :
    Γ ⊢ᵢ Formula.eq (add zero t) t :=
  eqI_trans (addI_comm hΓ zero t) (addI_zero hΓ t)

/-- ⭐⭐ **Todo término anclado es cero o un sucesor.**

    ⛔ **EVIDENCIA**, y por eso no la usa nadie todavía: es la medición que refuta la
    premisa de ADR-037. Se daba por hecho que sin el axioma 3 de Robinson Q no se despeja
    de una caracterización; aquí está derivado. Lo que SÍ usa el fragmento es la cadena de
    monotonía, que no pasa por este lema. -/
theorem zeroI_or_succ (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (hlift : Γ.map (liftFormula 0) = Γ)
    (L : String → Nat → Bool) {t : Term} (ht : Grounded L t) :
    Γ ⊢ᵢ Formula.or (Formula.eq t zero)
                    (Formula.ex (Formula.eq t (succ (Term.var 0)))) := by
  have htri := specI (specI (ax19I hΓ) t) zero
  have htri' : Γ ⊢ᵢ Formula.or (lt t zero)
      (Formula.or (Formula.eq t zero) (lt zero t)) := by
    simpa [ax19_lt_trichotomy, forall_2, substFormula, substTerms, substTerm, lt, zero,
      grounded_liftTerm L ht, grounded_substTerm L ht] using htri
  refine Derivesᵢ.elim_or _ _ _ _ htri' ?_ ?_
  · -- `t < 0` es imposible.
    exact Derivesᵢ.bot_elim _ _ (Derivesᵢ.elim_impl _ _ _
      (Derivesᵢ.weakening _ _ _ (notI_lt_zero hΓ hlift L ht)
        (fun _ hz => List.Mem.tail _ hz))
      (Derivesᵢ.hyp _ _ (List.Mem.head _)))
  refine Derivesᵢ.elim_or _ _ _ _ (Derivesᵢ.hyp _ _ (List.Mem.head _)) ?_ ?_
  · -- `t = 0`.
    exact Derivesᵢ.intro_or_l _ _ _ (Derivesᵢ.hyp _ _ (List.Mem.head _))
  · -- `0 < t` ⇒ testigo.
    refine Derivesᵢ.intro_or_r _ _ _ ?_
    have hex := Derivesᵢ.elim_impl _ _ _
      (Derivesᵢ.weakening Γ
        (lt zero t :: Formula.or (Formula.eq t zero) (lt zero t) :: Γ) _
        (exI_of_ltI hΓ L (grounded_zero L) ht)
        (fun _ hz => List.Mem.tail _ (List.Mem.tail _ hz)))
      (Derivesᵢ.hyp _ _ (List.Mem.head _))
    refine Derivesᵢ.elim_ex _ _ _ hex ?_
    simp only [List.map_cons, hlift, liftFormula, liftTerms, liftTerm, zero, succ,
      grounded_liftTerm L ht]
    refine Derivesᵢ.intro_ex _ _ (Term.var 0) ?_
    simp (config := { decide := true }) only [substFormula, substTerms, substTerm, succ,
      Nat.reduceAdd, ite_true, ite_false, grounded_substTerm L ht]
    have hΓ1 : ∀ g, List.Mem g arithAxioms →
        (Formula.eq (add zero (succ (Term.var 0))) t
          :: liftFormula 0 (lt zero t)
          :: Formula.or (Formula.eq t zero) (liftFormula 0 (lt zero t)) :: Γ) ⊢ᵢ g :=
      hyps_cons (hyps_cons (hyps_cons hΓ _) _) _
    exact eqI_trans (eqI_symm (Derivesᵢ.hyp _ _ (List.Mem.head _)))
      (zeroI_add hΓ1 (succ (Term.var 0)))




/-! ## 4 · La cadena de MONOTONÍA

    Con `ax13` en las dos direcciones, la monotonía de la suma es un cálculo: si
    `a + σj = b`, entonces `(a+c) + σj = (a+σj) + c = b + c`. **Ni cancelación ni
    inducción.** -/

/-- Asociatividad de `+` (`ax7`), para términos CUALESQUIERA.

    ⚠️ Esto pidió `Grounded` en el primer argumento hasta el 2026-09-22, y **no hacía
    falta**: el estorbo era el doble levantamiento que deja `forall_3`
    —`substTerm 1 (liftTerm 0 u) (liftTerm 0 (liftTerm 0 t))`—, y aguas arriba existe el
    lema que lo deshace, `FOL.substTerm_liftLift`. Una hipótesis de más durante un día por
    no haber buscado el lema que ya estaba. -/
theorem addI_assoc (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g) (t u v : Term) :
    Γ ⊢ᵢ Formula.eq (add (add t u) v) (add t (add u v)) := by
  have h := specI (specI (specI (hΓ ax7_add_assoc (by memA)) t) u) v
  simpa (config := { decide := true }) only [ax7_add_assoc, forall_3, substFormula,
    substTerms, substTerm, ite_true, ite_false, Nat.reduceAdd, add,
    substTerm_liftTerm, substTerm_liftLift] using h

/-- La dirección ⇐ de `ax13`, ya como teorema. -/
theorem ltI_of_add (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (L : String → Nat → Bool) {a b : Term} (ha : Grounded L a) (hb : Grounded L b)
    (k : Term) (h : Γ ⊢ᵢ Formula.eq (add a (succ k)) b) :
    Γ ⊢ᵢ lt a b := by
  have hi := specI (specI (ax13I hΓ) a) b
  have hback : Γ ⊢ᵢ
      Formula.impl (Formula.ex (Formula.eq (add a (succ (Term.var 0))) b)) (lt a b) := by
    have h2 := Derivesᵢ.elim_and_r _ _ _ hi
    simpa [ax13_lt_def, forall_2, substFormula, substTerms, substTerm, lt, add, succ,
      iff, grounded_liftTerm L ha, grounded_liftTerm L hb,
      grounded_substTerm L ha, grounded_substTerm L hb] using h2
  refine Derivesᵢ.elim_impl _ _ _ hback ?_
  refine Derivesᵢ.intro_ex _ _ k ?_
  simpa [substFormula, substTerms, substTerm, add, succ,
    grounded_substTerm L ha, grounded_substTerm L hb] using h

/-- El anclaje sobrevive a la suma, si la signatura admite `+`. -/
theorem grounded_add {L : String → Nat → Bool} (hs : L add_sym 2 = true)
    {t u : Term} (ht : Grounded L t) (hu : Grounded L u) : Grounded L (add t u) :=
  grounded_func2 L hs ht hu

/-- ⭐ **Monotonía estricta de la suma por la derecha.** -/
theorem ltI_add_right (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (hlift : Γ.map (liftFormula 0) = Γ)
    {L : String → Nat → Bool} (hs : L add_sym 2 = true) {a b c : Term}
    (ha : Grounded L a) (hb : Grounded L b) (hc : Grounded L c) :
    Γ ⊢ᵢ Formula.impl (lt a b) (lt (add a c) (add b c)) := by
  refine Derivesᵢ.intro_impl _ (lt a b) _ ?_
  have hex := Derivesᵢ.elim_impl _ _ _
    (Derivesᵢ.weakening _ _ _ (exI_of_ltI hΓ L ha hb)
      (fun _ hz => List.Mem.tail _ hz))
    (Derivesᵢ.hyp _ _ (List.Mem.head _))
  refine Derivesᵢ.elim_ex _ _ _ hex ?_
  simp only [List.map_cons, hlift, liftFormula, liftTerms, liftTerm, lt, add,
    grounded_liftTerm L ha, grounded_liftTerm L hb, grounded_liftTerm L hc]
  have hΓ1 : ∀ g, List.Mem g arithAxioms →
      (Formula.eq (add a (succ (Term.var 0))) b :: lt a b :: Γ) ⊢ᵢ g :=
    hyps_cons (hyps_cons hΓ (lt a b)) (Formula.eq (add a (succ (Term.var 0))) b)
  have hA : (Formula.eq (add a (succ (Term.var 0))) b :: lt a b :: Γ) ⊢ᵢ
      Formula.eq (add a (succ (Term.var 0))) b := Derivesᵢ.hyp _ _ (List.Mem.head _)
  have hstep : (Formula.eq (add a (succ (Term.var 0))) b :: lt a b :: Γ) ⊢ᵢ
      Formula.eq (add (add a c) (succ (Term.var 0)))
                 (add (add a (succ (Term.var 0))) c) :=
    eqI_trans (addI_assoc hΓ1 a c (succ (Term.var 0)))
      (eqI_trans (eqI_congr_fun2_r add_sym a (addI_comm hΓ1 c (succ (Term.var 0))))
        (eqI_symm (addI_assoc hΓ1 a (succ (Term.var 0)) c)))
  exact ltI_of_add hΓ1 L (grounded_add hs ha hc) (grounded_add hs hb hc) (Term.var 0)
    (eqI_trans hstep (eqI_congr_fun2_l add_sym c hA))


/-! ## 5 · El producto: `t·2̄ = t + t` y la distributividad -/

theorem mulI_zero (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g) (t : Term) :
    Γ ⊢ᵢ Formula.eq (mul t zero) zero := by
  have h := specI (hΓ ax8_mul_zero (by memA)) t
  simpa (config := { decide := true }) only [ax8_mul_zero, forall_, substFormula,
    substTerms, substTerm, ite_true, ite_false, mul, zero] using h

theorem mulI_succ (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g) (t u : Term) :
    Γ ⊢ᵢ Formula.eq (mul t (succ u)) (add (mul t u) t) := by
  have h := specI (specI (hΓ ax9_mul_succ (by memA)) t) u
  simpa (config := { decide := true }) only [ax9_mul_succ, forall_2, substFormula,
    substTerms, substTerm, ite_true, ite_false, Nat.reduceAdd, mul, add, succ,
    substTerm_liftTerm] using h

theorem mulI_comm (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g) (t u : Term) :
    Γ ⊢ᵢ Formula.eq (mul t u) (mul u t) := by
  have h := specI (specI (hΓ ax10_mul_comm (by memA)) t) u
  simpa (config := { decide := true }) only [ax10_mul_comm, forall_2, substFormula,
    substTerms, substTerm, ite_true, ite_false, Nat.reduceAdd, mul,
    substTerm_liftTerm] using h

/-- Distributividad por la IZQUIERDA (`ax12`), para términos cualesquiera. Misma historia
    que `addI_assoc`: el `Grounded` que pedía sobraba. -/
theorem mulI_distrib (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g) (t u v : Term) :
    Γ ⊢ᵢ Formula.eq (mul t (add u v)) (add (mul t u) (mul t v)) := by
  have h := specI (specI (specI (hΓ ax12_mul_distrib (by memA)) t) u) v
  simpa (config := { decide := true }) only [ax12_mul_distrib, forall_3, substFormula,
    substTerms, substTerm, ite_true, ite_false, Nat.reduceAdd, mul, add,
    substTerm_liftTerm, substTerm_liftLift] using h

/-- ⭐ `t · 2̄ = t + t`. Sale de `ax9`, `ax8` y `0 + x = x`, sin inducción. -/
theorem mulI_two (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g) (t : Term) :
    Γ ⊢ᵢ Formula.eq (mul t (numeralM 2)) (add t t) := by
  have h1 : Γ ⊢ᵢ Formula.eq (mul t (numeralM 2)) (add (mul t (numeralM 1)) t) :=
    mulI_succ hΓ t (numeralM 1)
  have h2 : Γ ⊢ᵢ Formula.eq (mul t (numeralM 1)) (add (mul t zero) t) :=
    mulI_succ hΓ t zero
  have h3 : Γ ⊢ᵢ Formula.eq (add (mul t zero) t) (add zero t) :=
    eqI_congr_fun2_l add_sym t (mulI_zero hΓ t)
  have h4 : Γ ⊢ᵢ Formula.eq (mul t (numeralM 1)) t :=
    eqI_trans h2 (eqI_trans h3 (zeroI_add hΓ t))
  exact eqI_trans h1 (eqI_congr_fun2_l add_sym t h4)


/-! ## 6 · ⭐⭐ Monotonía del producto por `2̄` — SIN transitividad

    El truco que evita la cadena `a+a < b+a < b+b`: de `y + σj = k̄` se calcula
    `k̄·2̄ = y·2̄ + σ(σj + j)`, y **eso es ya la forma que `ax13` pide**. -/

theorem ltI_mul_two (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (hlift : Γ.map (liftFormula 0) = Γ)
    {L : String → Nat → Bool} (hm : L mul_sym 2 = true) (hsu : L succ_sym 1 = true)
    {y k : Term} (hy : Grounded L y) (hk : Grounded L k) :
    Γ ⊢ᵢ Formula.impl (lt y k) (lt (mul y (numeralM 2)) (mul k (numeralM 2))) := by
  have h2g : Grounded L (numeralM 2) := grounded_numeralM L hsu 2
  refine Derivesᵢ.intro_impl _ (lt y k) _ ?_
  have hex := Derivesᵢ.elim_impl _ _ _
    (Derivesᵢ.weakening _ _ _ (exI_of_ltI hΓ L hy hk)
      (fun _ hz => List.Mem.tail _ hz))
    (Derivesᵢ.hyp _ _ (List.Mem.head _))
  refine Derivesᵢ.elim_ex _ _ _ hex ?_
  simp only [List.map_cons, hlift, liftFormula, liftTerms, liftTerm, lt, mul,
    grounded_liftTerm L hy, grounded_liftTerm L hk, grounded_liftTerm L h2g]
  have hΓ1 : ∀ g, List.Mem g arithAxioms →
      (Formula.eq (add y (succ (Term.var 0))) k :: lt y k :: Γ) ⊢ᵢ g :=
    hyps_cons (hyps_cons hΓ (lt y k)) (Formula.eq (add y (succ (Term.var 0))) k)
  have hA : (Formula.eq (add y (succ (Term.var 0))) k :: lt y k :: Γ) ⊢ᵢ
      Formula.eq (add y (succ (Term.var 0))) k := Derivesᵢ.hyp _ _ (List.Mem.head _)
  -- `k·2 = (y + σ#0)·2 = 2·(y+σ#0) = 2·y + 2·σ#0 = y·2 + σ#0·2`
  have e1 : (Formula.eq (add y (succ (Term.var 0))) k :: lt y k :: Γ) ⊢ᵢ
      Formula.eq (mul k (numeralM 2)) (mul (add y (succ (Term.var 0))) (numeralM 2)) :=
    eqI_congr_fun2_l mul_sym (numeralM 2) (eqI_symm hA)
  have e2 : (Formula.eq (add y (succ (Term.var 0))) k :: lt y k :: Γ) ⊢ᵢ
      Formula.eq (mul (add y (succ (Term.var 0))) (numeralM 2))
                 (mul (numeralM 2) (add y (succ (Term.var 0)))) :=
    mulI_comm hΓ1 (add y (succ (Term.var 0))) (numeralM 2)
  have e3 : (Formula.eq (add y (succ (Term.var 0))) k :: lt y k :: Γ) ⊢ᵢ
      Formula.eq (mul (numeralM 2) (add y (succ (Term.var 0))))
                 (add (mul (numeralM 2) y) (mul (numeralM 2) (succ (Term.var 0)))) :=
    mulI_distrib hΓ1 (numeralM 2) y (succ (Term.var 0))
  have e4 : (Formula.eq (add y (succ (Term.var 0))) k :: lt y k :: Γ) ⊢ᵢ
      Formula.eq (add (mul (numeralM 2) y) (mul (numeralM 2) (succ (Term.var 0))))
                 (add (mul y (numeralM 2)) (mul (succ (Term.var 0)) (numeralM 2))) :=
    eqI_trans (eqI_congr_fun2_l add_sym _ (mulI_comm hΓ1 (numeralM 2) y))
      (eqI_congr_fun2_r add_sym (mul y (numeralM 2))
        (mulI_comm hΓ1 (numeralM 2) (succ (Term.var 0))))
  -- `σ#0 · 2 = σ#0 + σ#0 = σ(σ#0 + #0)`
  have e5 : (Formula.eq (add y (succ (Term.var 0))) k :: lt y k :: Γ) ⊢ᵢ
      Formula.eq (mul (succ (Term.var 0)) (numeralM 2))
                 (succ (add (succ (Term.var 0)) (Term.var 0))) :=
    eqI_trans (mulI_two hΓ1 (succ (Term.var 0)))
      (addI_succ hΓ1 (succ (Term.var 0)) (Term.var 0))
  have efin : (Formula.eq (add y (succ (Term.var 0))) k :: lt y k :: Γ) ⊢ᵢ
      Formula.eq (add (mul y (numeralM 2)) (succ (add (succ (Term.var 0)) (Term.var 0))))
                 (mul k (numeralM 2)) :=
    eqI_symm (eqI_trans e1 (eqI_trans e2 (eqI_trans e3
      (eqI_trans e4 (eqI_congr_fun2_r add_sym (mul y (numeralM 2)) e5)))))
  exact ltI_of_add hΓ1 L (grounded_func2 L hm hy h2g) (grounded_func2 L hm hk h2g)
    (add (succ (Term.var 0)) (Term.var 0)) efin

/-! ## 7 · Irreflexividad, discreción y transitividad

    ⏳ Las dos últimas están puestas mirando a `√`, que se caracteriza por DOS desigualdades
    (`ax14`: `(√n)² ≤ n`, `ax15`: `n < (σ√n)²`) y por eso pide lo que `/₂` se pudo saltar. -/

/-- `ax18` instanciado: nada es menor que sí mismo. -/
theorem ltI_irrefl (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (L : String → Nat → Bool) {t : Term} (ht : Grounded L t) :
    Γ ⊢ᵢ Formula.impl (lt t t) Formula.bottom := by
  have h := specI (ax18I hΓ) t
  simpa (config := { decide := true }) only [ax18_lt_irrefl, forall_, neg, substFormula,
    substTerms, substTerm, ite_true, ite_false, lt] using h

/-- ⭐ **Ningún término anclado cumple `x + σy = x`.** `addI_succ_ne` hacía esto para
    numerales, con inducción META. Para términos anclados sale GRATIS: `x + σy = x` es
    justo `x < x` por `ax13`, y `ax18` lo prohíbe.

    ✅ Y desde el 2026-09-22 tiene uso portante: es lo que refuta la tercera rama de
    `notI_lt_succ_of_lt`, o sea lo que hace DISCRETO el orden. -/
theorem notI_add_succ_self (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (L : String → Nat → Bool) {x : Term} (hx : Grounded L x) (y : Term) :
    Γ ⊢ᵢ Formula.impl (Formula.eq (add x (succ y)) x) Formula.bottom := by
  refine Derivesᵢ.intro_impl _ (Formula.eq (add x (succ y)) x) Formula.bottom ?_
  have hΓ1 : ∀ g, List.Mem g arithAxioms →
      (Formula.eq (add x (succ y)) x :: Γ) ⊢ᵢ g :=
    hyps_cons hΓ (Formula.eq (add x (succ y)) x)
  exact Derivesᵢ.elim_impl _ _ _ (ltI_irrefl hΓ1 L hx)
    (ltI_of_add hΓ1 L hx hx y (Derivesᵢ.hyp _ _ (List.Mem.head _)))

/-- ⭐ **Transitividad de `<`.** `a+σj=b` y `b+σi=c` dan `a + σ(j + σi) = c`.

    ✅ `/₂` se pudo cerrar SIN transitividad (ver `ltI_mul_two`), pero las dos desigualdades
    de `√` la piden, y ahí la usan `notI_lt_of_le` y `leI_trans`. -/
theorem ltI_trans (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (hlift : Γ.map (liftFormula 0) = Γ)
    {L : String → Nat → Bool} {a b c : Term}
    (ha : Grounded L a) (hb : Grounded L b) (hc : Grounded L c) :
    Γ ⊢ᵢ Formula.impl (lt a b) (Formula.impl (lt b c) (lt a c)) := by
  refine Derivesᵢ.intro_impl _ (lt a b) _ ?_
  refine Derivesᵢ.intro_impl _ (lt b c) _ ?_
  have hex1 := Derivesᵢ.elim_impl _ _ _
    (Derivesᵢ.weakening Γ (lt b c :: lt a b :: Γ) _ (exI_of_ltI hΓ L ha hb)
      (fun _ hz => List.Mem.tail _ (List.Mem.tail _ hz)))
    (Derivesᵢ.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
  refine Derivesᵢ.elim_ex _ _ _ hex1 ?_
  simp only [List.map_cons, hlift, liftFormula, liftTerms, liftTerm, lt,
    grounded_liftTerm L ha, grounded_liftTerm L hb, grounded_liftTerm L hc]
  have hex2 := Derivesᵢ.elim_impl _ _ _
    (Derivesᵢ.weakening Γ
      (Formula.eq (add a (succ (Term.var 0))) b :: lt b c :: lt a b :: Γ) _
      (exI_of_ltI hΓ L hb hc)
      (fun _ hz => List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ hz))))
    (Derivesᵢ.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
  refine Derivesᵢ.elim_ex _ _ _ hex2 ?_
  simp (config := { decide := true }) only [List.map_cons, hlift, liftFormula, liftTerms,
    liftTerm, lt, add, succ, Nat.reduceAdd, ite_true, ite_false,
    grounded_liftTerm L ha, grounded_liftTerm L hb, grounded_liftTerm L hc]
  have hΓ2 : ∀ g, List.Mem g arithAxioms →
      (Formula.eq (add b (succ (Term.var 0))) c
        :: Formula.eq (add a (succ (Term.var 1))) b
        :: lt b c :: lt a b :: Γ) ⊢ᵢ g :=
    hyps_cons (hyps_cons (hyps_cons (hyps_cons hΓ _) _) _) _
  have hC : (Formula.eq (add b (succ (Term.var 0))) c
        :: Formula.eq (add a (succ (Term.var 1))) b
        :: lt b c :: lt a b :: Γ) ⊢ᵢ Formula.eq (add b (succ (Term.var 0))) c :=
    Derivesᵢ.hyp _ _ (List.Mem.head _)
  have hB : (Formula.eq (add b (succ (Term.var 0))) c
        :: Formula.eq (add a (succ (Term.var 1))) b
        :: lt b c :: lt a b :: Γ) ⊢ᵢ Formula.eq (add a (succ (Term.var 1))) b :=
    Derivesᵢ.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  refine ltI_of_add hΓ2 L ha hc (add (succ (Term.var 1)) (Term.var 0)) ?_
  refine eqI_trans ?_ (eqI_trans (eqI_congr_fun2_l add_sym (succ (Term.var 0)) hB) hC)
  exact eqI_trans
    (eqI_congr_fun2_r add_sym a
      (eqI_symm (addI_succ hΓ2 (succ (Term.var 1)) (Term.var 0))))
    (eqI_symm (addI_assoc hΓ2 a (succ (Term.var 1)) (succ (Term.var 0))))


/-! ## 8 · ⭐ DISCRECIÓN del orden — y sin la forma ∀ de `zeroI_or_succ`

    `a < b → σa ≤ b`. La vía es la tricotomía sobre `σa` vs `b`, **los dos anclados**, y
    refutar la tercera rama: de `a < b` y `b < σa` sale `σ(a+W) = σa`, `ax3` da `a + W = a`,
    y eso es lo que `notI_add_succ_self` prohíbe. -/

theorem notI_lt_succ_of_lt (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (hlift : Γ.map (liftFormula 0) = Γ)
    {L : String → Nat → Bool} (hs : L succ_sym 1 = true) {a b : Term}
    (ha : Grounded L a) (hb : Grounded L b) :
    Γ ⊢ᵢ Formula.impl (lt a b) (Formula.impl (lt b (succ a)) Formula.bottom) := by
  have hsa : Grounded L (succ a) := grounded_func1 L hs ha
  refine Derivesᵢ.intro_impl _ (lt a b) _ ?_
  refine Derivesᵢ.intro_impl _ (lt b (succ a)) _ ?_
  have hex1 := Derivesᵢ.elim_impl _ _ _
    (Derivesᵢ.weakening Γ (lt b (succ a) :: lt a b :: Γ) _ (exI_of_ltI hΓ L ha hb)
      (fun _ hz => List.Mem.tail _ (List.Mem.tail _ hz)))
    (Derivesᵢ.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
  refine Derivesᵢ.elim_ex _ _ _ hex1 ?_
  simp only [List.map_cons, hlift, liftFormula, liftTerms, liftTerm, lt, succ,
    grounded_liftTerm L ha, grounded_liftTerm L hb]
  have hex2 := Derivesᵢ.elim_impl _ _ _
    (Derivesᵢ.weakening Γ
      (Formula.eq (add a (succ (Term.var 0))) b :: lt b (succ a) :: lt a b :: Γ) _
      (exI_of_ltI hΓ L hb hsa)
      (fun _ hz => List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ hz))))
    (Derivesᵢ.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
  refine Derivesᵢ.elim_ex _ _ _ hex2 ?_
  simp (config := { decide := true }) only [List.map_cons, hlift, liftFormula, liftTerms,
    liftTerm, lt, add, succ, Nat.reduceAdd, ite_true, ite_false,
    grounded_liftTerm L ha, grounded_liftTerm L hb]
  have hΓ2 : ∀ g, List.Mem g arithAxioms →
      (Formula.eq (add b (succ (Term.var 0))) (succ a)
        :: Formula.eq (add a (succ (Term.var 1))) b
        :: lt b (succ a) :: lt a b :: Γ) ⊢ᵢ g :=
    hyps_cons (hyps_cons (hyps_cons (hyps_cons hΓ _) _) _) _
  have hC : (Formula.eq (add b (succ (Term.var 0))) (succ a)
        :: Formula.eq (add a (succ (Term.var 1))) b
        :: lt b (succ a) :: lt a b :: Γ) ⊢ᵢ
      Formula.eq (add b (succ (Term.var 0))) (succ a) :=
    Derivesᵢ.hyp _ _ (List.Mem.head _)
  have hB : (Formula.eq (add b (succ (Term.var 0))) (succ a)
        :: Formula.eq (add a (succ (Term.var 1))) b
        :: lt b (succ a) :: lt a b :: Γ) ⊢ᵢ
      Formula.eq (add a (succ (Term.var 1))) b :=
    Derivesᵢ.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  -- `σa = b + σ#0 = (a + σ#1) + σ#0 = a + (σ#1 + σ#0) = a + σ(σ#1 + #0) = σ(a + (σ#1 + #0))`
  have e1 := eqI_symm hC
  have e2 := eqI_congr_fun2_l add_sym (succ (Term.var 0)) (eqI_symm hB)
  have e3 := addI_assoc hΓ2 a (succ (Term.var 1)) (succ (Term.var 0))
  have e4 := eqI_congr_fun2_r add_sym a
    (addI_succ hΓ2 (succ (Term.var 1)) (Term.var 0))
  have e5 := addI_succ hΓ2 a (add (succ (Term.var 1)) (Term.var 0))
  have hchain : (Formula.eq (add b (succ (Term.var 0))) (succ a)
        :: Formula.eq (add a (succ (Term.var 1))) b
        :: lt b (succ a) :: lt a b :: Γ) ⊢ᵢ
      Formula.eq (succ a) (succ (add a (add (succ (Term.var 1)) (Term.var 0)))) :=
    eqI_trans e1 (eqI_trans e2 (eqI_trans e3 (eqI_trans e4 e5)))
  -- `ax3` ⇒ `a = a + (σ#1 + #0)`; y `σ#1 + #0 = σ(#0 + #1)`
  have hinj : (Formula.eq (add b (succ (Term.var 0))) (succ a)
        :: Formula.eq (add a (succ (Term.var 1))) b
        :: lt b (succ a) :: lt a b :: Γ) ⊢ᵢ
      Formula.eq a (add a (add (succ (Term.var 1)) (Term.var 0))) :=
    Derivesᵢ.elim_impl _ _ _
      (succI_inj hΓ2 a (add a (add (succ (Term.var 1)) (Term.var 0)))) hchain
  have hW : (Formula.eq (add b (succ (Term.var 0))) (succ a)
        :: Formula.eq (add a (succ (Term.var 1))) b
        :: lt b (succ a) :: lt a b :: Γ) ⊢ᵢ
      Formula.eq (add (succ (Term.var 1)) (Term.var 0))
                 (succ (add (Term.var 0) (Term.var 1))) :=
    eqI_trans (addI_comm hΓ2 (succ (Term.var 1)) (Term.var 0))
      (addI_succ hΓ2 (Term.var 0) (Term.var 1))
  exact Derivesᵢ.elim_impl _ _ _
    (notI_add_succ_self hΓ2 L ha (add (Term.var 0) (Term.var 1)))
    (eqI_symm (eqI_trans hinj (eqI_congr_fun2_r add_sym a hW)))


/-- ⭐ **DISCRECIÓN**: entre `a` y `σa` no hay nada.

    ✅ Uso portante desde el mismo día: es lo que convierte `s < k̄` en `σs ≤ k̄` dentro de
    `numeralI_sqrt`. -/
theorem ltI_succ_le (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (hlift : Γ.map (liftFormula 0) = Γ)
    {L : String → Nat → Bool} (hs : L succ_sym 1 = true) {a b : Term}
    (ha : Grounded L a) (hb : Grounded L b) :
    Γ ⊢ᵢ Formula.impl (lt a b)
      (Formula.or (lt (succ a) b) (Formula.eq (succ a) b)) := by
  have hsa : Grounded L (succ a) := grounded_func1 L hs ha
  refine Derivesᵢ.intro_impl _ (lt a b) _ ?_
  have hΓ1 : ∀ g, List.Mem g arithAxioms → (lt a b :: Γ) ⊢ᵢ g := hyps_cons hΓ (lt a b)
  have htri := specI (specI (ax19I hΓ1) (succ a)) b
  have htri' : (lt a b :: Γ) ⊢ᵢ Formula.or (lt (succ a) b)
      (Formula.or (Formula.eq (succ a) b) (lt b (succ a))) := by
    simpa [ax19_lt_trichotomy, forall_2, substFormula, substTerms, substTerm, lt,
      grounded_liftTerm L hsa, grounded_liftTerm L hb,
      grounded_substTerm L hsa, grounded_substTerm L hb] using htri
  refine Derivesᵢ.elim_or _ _ _ _ htri' ?_ ?_
  · exact Derivesᵢ.intro_or_l _ _ _ (Derivesᵢ.hyp _ _ (List.Mem.head _))
  refine Derivesᵢ.elim_or _ _ _ _ (Derivesᵢ.hyp _ _ (List.Mem.head _)) ?_ ?_
  · exact Derivesᵢ.intro_or_r _ _ _ (Derivesᵢ.hyp _ _ (List.Mem.head _))
  · refine Derivesᵢ.bot_elim _ _ ?_
    refine Derivesᵢ.elim_impl _ _ _
      (Derivesᵢ.elim_impl _ _ _
        (Derivesᵢ.weakening Γ
          (lt b (succ a) :: Formula.or (Formula.eq (succ a) b) (lt b (succ a))
            :: lt a b :: Γ) _
          (notI_lt_succ_of_lt hΓ hlift hs ha hb)
          (fun _ hz => List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ hz))))
        (Derivesᵢ.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
      (Derivesᵢ.hyp _ _ (List.Mem.head _))


/-! ## 9 · ⭐ Monotonía del CUADRADO

    De `a + σj = b` se calcula `b·b = a·a + σ(W)`: el `σ` sale de `b·σj = b·j + b` y de
    `b = a + σj`, reasociando hasta dejar el `σj` al final y aplicando `ax5`. Mismo truco
    que `ltI_mul_two`, y por la misma razón: la forma que `ax13` pide se **construye**.

    ⚠️ El marcador va en el docstring del TEOREMA y no aquí: `[H]` mira el docstring de
    declaración inmediato, y una cabecera de SECCIÓN no exime a nada — para eso se ajustó
    el 2026-09-21. (Y los delimitadores no se pueden citar literalmente: los comentarios de
    Lean **anidan**, así que escribirlos aquí dejaría el comentario sin cerrar.) -/

/-- ⭐ **Monotonía estricta del cuadrado**: `a < b ⟹ a·a < b·b`.

    ✅ Uso portante desde el mismo día, vía `leI_mul_self`. -/
theorem ltI_mul_self (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (hlift : Γ.map (liftFormula 0) = Γ)
    {L : String → Nat → Bool} (hm : L mul_sym 2 = true) {a b : Term}
    (ha : Grounded L a) (hb : Grounded L b) :
    Γ ⊢ᵢ Formula.impl (lt a b) (lt (mul a a) (mul b b)) := by
  refine Derivesᵢ.intro_impl _ (lt a b) _ ?_
  have hex := Derivesᵢ.elim_impl _ _ _
    (Derivesᵢ.weakening _ _ _ (exI_of_ltI hΓ L ha hb)
      (fun _ hz => List.Mem.tail _ hz))
    (Derivesᵢ.hyp _ _ (List.Mem.head _))
  refine Derivesᵢ.elim_ex _ _ _ hex ?_
  simp only [List.map_cons, hlift, liftFormula, liftTerms, liftTerm, lt, mul,
    grounded_liftTerm L ha, grounded_liftTerm L hb]
  have hΓ1 : ∀ g, List.Mem g arithAxioms →
      (Formula.eq (add a (succ (Term.var 0))) b :: lt a b :: Γ) ⊢ᵢ g :=
    hyps_cons (hyps_cons hΓ (lt a b)) (Formula.eq (add a (succ (Term.var 0))) b)
  have hB : (Formula.eq (add a (succ (Term.var 0))) b :: lt a b :: Γ) ⊢ᵢ
      Formula.eq (add a (succ (Term.var 0))) b := Derivesᵢ.hyp _ _ (List.Mem.head _)
  -- `b·a = a·a + a·σ#0`
  have hba : (Formula.eq (add a (succ (Term.var 0))) b :: lt a b :: Γ) ⊢ᵢ
      Formula.eq (mul b a) (add (mul a a) (mul a (succ (Term.var 0)))) :=
    eqI_trans (mulI_comm hΓ1 b a)
      (eqI_trans (eqI_congr_fun2_r mul_sym a (eqI_symm hB))
        (mulI_distrib hΓ1 a a (succ (Term.var 0))))
  -- `b·σ#0 = (b·#0 + a) + σ#0`
  have hbs : (Formula.eq (add a (succ (Term.var 0))) b :: lt a b :: Γ) ⊢ᵢ
      Formula.eq (mul b (succ (Term.var 0)))
                 (add (add (mul b (Term.var 0)) a) (succ (Term.var 0))) :=
    eqI_trans (mulI_succ hΓ1 b (Term.var 0))
      (eqI_trans (eqI_congr_fun2_r add_sym (mul b (Term.var 0)) (eqI_symm hB))
        (eqI_symm (addI_assoc hΓ1 (mul b (Term.var 0)) a (succ (Term.var 0)))))
  -- el corchete `a·σ#0 + b·σ#0 = σ(X + #0)`
  have hbr : (Formula.eq (add a (succ (Term.var 0))) b :: lt a b :: Γ) ⊢ᵢ
      Formula.eq (add (mul a (succ (Term.var 0))) (mul b (succ (Term.var 0))))
        (succ (add (add (mul a (succ (Term.var 0))) (add (mul b (Term.var 0)) a))
                   (Term.var 0))) :=
    eqI_trans (eqI_congr_fun2_r add_sym (mul a (succ (Term.var 0))) hbs)
      (eqI_trans (eqI_symm (addI_assoc hΓ1 (mul a (succ (Term.var 0)))
                             (add (mul b (Term.var 0)) a) (succ (Term.var 0))))
        (addI_succ hΓ1 (add (mul a (succ (Term.var 0))) (add (mul b (Term.var 0)) a))
          (Term.var 0)))
  -- `b·b = a·a + σ(X + #0)`
  have hfin : (Formula.eq (add a (succ (Term.var 0))) b :: lt a b :: Γ) ⊢ᵢ
      Formula.eq (mul b b)
        (add (mul a a)
          (succ (add (add (mul a (succ (Term.var 0))) (add (mul b (Term.var 0)) a))
                     (Term.var 0)))) :=
    eqI_trans (eqI_congr_fun2_r mul_sym b (eqI_symm hB))
      (eqI_trans (mulI_distrib hΓ1 b a (succ (Term.var 0)))
        (eqI_trans (eqI_congr_fun2_l add_sym (mul b (succ (Term.var 0))) hba)
          (eqI_trans (addI_assoc hΓ1 (mul a a) (mul a (succ (Term.var 0)))
                       (mul b (succ (Term.var 0))))
            (eqI_congr_fun2_r add_sym (mul a a) hbr))))
  exact ltI_of_add hΓ1 L (grounded_func2 L hm ha ha) (grounded_func2 L hm hb hb)
    (add (add (mul a (succ (Term.var 0))) (add (mul b (Term.var 0)) a)) (Term.var 0))
    (eqI_symm hfin)


/-! ## 10 · Los tres auxiliares de `≤`

    `le p q` es `lt p q ∨ p = q`, así que todo lo de aquí es un `elim_or` y un caso de
    igualdad que se cierra reescribiendo DENTRO del predicado (`eqI_rw_atom2_*`). -/

/-- `p ≤ q` y `q < p` se contradicen. -/
theorem notI_lt_of_le (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (hlift : Γ.map (liftFormula 0) = Γ)
    {L : String → Nat → Bool} {p q : Term} (hp : Grounded L p) (hq : Grounded L q)
    (hle : Γ ⊢ᵢ Formula.or (lt p q) (Formula.eq p q))
    (hlt : Γ ⊢ᵢ lt q p) : Γ ⊢ᵢ Formula.bottom := by
  refine Derivesᵢ.elim_or _ _ _ _ hle ?_ ?_
  · -- `p < q` y `q < p` ⇒ `q < q`
    have hΓ1 : ∀ g, List.Mem g arithAxioms → (lt p q :: Γ) ⊢ᵢ g := hyps_cons hΓ (lt p q)
    have hqp : (lt p q :: Γ) ⊢ᵢ lt q p :=
      Derivesᵢ.weakening _ _ _ hlt (fun _ hz => List.Mem.tail _ hz)
    have htr := Derivesᵢ.elim_impl _ _ _
      (Derivesᵢ.elim_impl _ _ _
        (Derivesᵢ.weakening Γ (lt p q :: Γ) _ (ltI_trans hΓ hlift hq hp hq)
          (fun _ hz => List.Mem.tail _ hz))
        hqp)
      (Derivesᵢ.hyp _ _ (List.Mem.head _))
    exact Derivesᵢ.elim_impl _ _ _ (ltI_irrefl hΓ1 L hq) htr
  · -- `p = q` ⇒ `q < p` se vuelve `q < q`
    have hΓ1 : ∀ g, List.Mem g arithAxioms → (Formula.eq p q :: Γ) ⊢ᵢ g :=
      hyps_cons hΓ (Formula.eq p q)
    have hqp : (Formula.eq p q :: Γ) ⊢ᵢ lt q p :=
      Derivesᵢ.weakening _ _ _ hlt (fun _ hz => List.Mem.tail _ hz)
    exact Derivesᵢ.elim_impl _ _ _ (ltI_irrefl hΓ1 L hq)
      (eqI_rw_atom2_r lt_sym q (Derivesᵢ.hyp _ _ (List.Mem.head _)) hqp)

/-- `p ≤ q` ⇒ `p·p ≤ q·q`. -/
theorem leI_mul_self (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (hlift : Γ.map (liftFormula 0) = Γ)
    {L : String → Nat → Bool} (hm : L mul_sym 2 = true) {p q : Term}
    (hp : Grounded L p) (hq : Grounded L q)
    (hle : Γ ⊢ᵢ Formula.or (lt p q) (Formula.eq p q)) :
    Γ ⊢ᵢ Formula.or (lt (mul p p) (mul q q)) (Formula.eq (mul p p) (mul q q)) := by
  refine Derivesᵢ.elim_or _ _ _ _ hle ?_ ?_
  · refine Derivesᵢ.intro_or_l _ _ _ ?_
    exact Derivesᵢ.elim_impl _ _ _
      (Derivesᵢ.weakening Γ (lt p q :: Γ) _ (ltI_mul_self hΓ hlift hm hp hq)
        (fun _ hz => List.Mem.tail _ hz))
      (Derivesᵢ.hyp _ _ (List.Mem.head _))
  · refine Derivesᵢ.intro_or_r _ _ _ ?_
    exact eqI_congr_fun2 mul_sym (Derivesᵢ.hyp _ _ (List.Mem.head _))
      (Derivesᵢ.hyp _ _ (List.Mem.head _))

/-- `≤` es transitiva. Cuatro casos, y los tres con alguna igualdad se cierran
    reescribiendo. -/
theorem leI_trans (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (hlift : Γ.map (liftFormula 0) = Γ)
    {L : String → Nat → Bool} {p q r : Term}
    (hp : Grounded L p) (hq : Grounded L q) (hr : Grounded L r)
    (h1 : Γ ⊢ᵢ Formula.or (lt p q) (Formula.eq p q))
    (h2 : Γ ⊢ᵢ Formula.or (lt q r) (Formula.eq q r)) :
    Γ ⊢ᵢ Formula.or (lt p r) (Formula.eq p r) := by
  refine Derivesᵢ.elim_or _ _ _ _ h1 ?_ ?_
  · -- `p < q`
    have h2' : (lt p q :: Γ) ⊢ᵢ Formula.or (lt q r) (Formula.eq q r) :=
      Derivesᵢ.weakening _ _ _ h2 (fun _ hz => List.Mem.tail _ hz)
    refine Derivesᵢ.elim_or _ _ _ _ h2' ?_ ?_
    · -- `p < q < r`
      refine Derivesᵢ.intro_or_l _ _ _ ?_
      exact Derivesᵢ.elim_impl _ _ _
        (Derivesᵢ.elim_impl _ _ _
          (Derivesᵢ.weakening Γ (lt q r :: lt p q :: Γ) _ (ltI_trans hΓ hlift hp hq hr)
            (fun _ hz => List.Mem.tail _ (List.Mem.tail _ hz)))
          (Derivesᵢ.hyp _ _ (List.Mem.tail _ (List.Mem.head _))))
        (Derivesᵢ.hyp _ _ (List.Mem.head _))
    · -- `p < q = r`
      refine Derivesᵢ.intro_or_l _ _ _ ?_
      exact eqI_rw_atom2_r lt_sym p (Derivesᵢ.hyp _ _ (List.Mem.head _))
        (Derivesᵢ.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
  · -- `p = q`
    have h2' : (Formula.eq p q :: Γ) ⊢ᵢ Formula.or (lt q r) (Formula.eq q r) :=
      Derivesᵢ.weakening _ _ _ h2 (fun _ hz => List.Mem.tail _ hz)
    refine Derivesᵢ.elim_or _ _ _ _ h2' ?_ ?_
    · -- `p = q < r`
      refine Derivesᵢ.intro_or_l _ _ _ ?_
      exact eqI_rw_atom2_l lt_sym r
        (eqI_symm (Derivesᵢ.hyp _ _ (List.Mem.tail _ (List.Mem.head _))))
        (Derivesᵢ.hyp _ _ (List.Mem.head _))
    · -- `p = q = r`
      refine Derivesᵢ.intro_or_r _ _ _ ?_
      exact eqI_trans (Derivesᵢ.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
        (Derivesᵢ.hyp _ _ (List.Mem.head _))


/-! ## 11 · 🏁 `√` SOBRE NUMERALES — la última casilla de ADR-037 que se podía cerrar

    `ax14` y `ax15` **encajonan** `√n` entre dos cuadrados consecutivos, y en un orden total
    y discreto eso lo determina. La tricotomía contra el candidato cierra las dos ramas
    malas, cada una con una cadena de `≤` y `ax18` al final. -/

theorem ax14I (h14 : Γ ⊢ᵢ ax14_sqrt_le) (L : String → Nat → Bool)
    {t : Term} (ht : Grounded L t) :
    Γ ⊢ᵢ Formula.or (lt (mul (sqrt t) (sqrt t)) t)
                    (Formula.eq (mul (sqrt t) (sqrt t)) t) := by
  have h := specI h14 t
  simpa (config := { decide := true }) only [ax14_sqrt_le, forall_, le, sq, substFormula,
    substTerms, substTerm, ite_true, ite_false, lt, mul, sqrt,
    grounded_substTerm L ht] using h

theorem ax15I (h15 : Γ ⊢ᵢ ax15_lt_succ_sqrt) (L : String → Nat → Bool)
    {t : Term} (ht : Grounded L t) :
    Γ ⊢ᵢ lt t (mul (succ (sqrt t)) (succ (sqrt t))) := by
  have h := specI h15 t
  simpa (config := { decide := true }) only [ax15_lt_succ_sqrt, forall_, sq, substFormula,
    substTerms, substTerm, ite_true, ite_false, lt, mul, sqrt, succ,
    grounded_substTerm L ht] using h

/-! ## 🏁 `numeralI_sqrt` — con `k` como PARÁMETRO y sus dos cotas

    ⚠️ El núcleo de Lean **no trae `Nat.sqrt`** (vive en Mathlib, que aquí no hay), así que
    el enunciado toma `k` y sus dos hipótesis. Más general, y separa la aritmética del meta
    de la derivación del objeto. -/

/-- 🏁 **`√n̄` ES demostrablemente `k̄`**, para el único `k` con `k² ≤ n < (k+1)²`.

    🏁 **ENTREGABLE**: es la medición de que `√` está DETERMINADO —la última casilla de
    ADR-037 que se podía cerrar demostrando—, y todavía no la consume el fragmento: para eso
    hace falta meter `ax14`/`ax15` en la lista, y `ax14` **no es de Harrop**. -/
theorem numeralI_sqrt (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (h14 : Γ ⊢ᵢ ax14_sqrt_le) (h15 : Γ ⊢ᵢ ax15_lt_succ_sqrt)
    (hlift : Γ.map (liftFormula 0) = Γ)
    {L : String → Nat → Bool} (hm : L mul_sym 2 = true) (hsu : L succ_sym 1 = true)
    (hsq : L sqrt_sym 1 = true)
    (n k : Nat) (hk1 : k * k ≤ n) (hk2 : n < (k + 1) * (k + 1)) :
    Γ ⊢ᵢ Formula.eq (sqrt (numeralM n)) (numeralM k) := by
  have hng : Grounded L (numeralM n) := grounded_numeralM L hsu n
  have hkg : Grounded L (numeralM k) := grounded_numeralM L hsu k
  have hsg : Grounded L (sqrt (numeralM n)) := grounded_func1 L hsq hng
  have hssg : Grounded L (succ (sqrt (numeralM n))) := grounded_func1 L hsu hsg
  have hskg : Grounded L (numeralM (k + 1)) := grounded_numeralM L hsu (k + 1)
  -- `k̄·k̄ ≤ n̄`
  have hkn : Γ ⊢ᵢ Formula.or (lt (mul (numeralM k) (numeralM k)) (numeralM n))
      (Formula.eq (mul (numeralM k) (numeralM k)) (numeralM n)) := by
    have hmul := numeralI_mul hΓ k k
    rcases Nat.lt_or_ge (k * k) n with hlt | hge
    · exact Derivesᵢ.intro_or_l _ _ _
        (eqI_rw_atom2_l lt_sym (numeralM n) (eqI_symm hmul) (numeralI_lt hΓ hlt))
    · have heq : k * k = n := by omega
      exact Derivesᵢ.intro_or_r _ _ _ (by rw [heq] at hmul; exact hmul)
  -- `n̄ < (k+1)‾·(k+1)‾`
  have hnk : Γ ⊢ᵢ lt (numeralM n) (mul (numeralM (k + 1)) (numeralM (k + 1))) :=
    eqI_rw_atom2_r lt_sym (numeralM n) (eqI_symm (numeralI_mul hΓ (k + 1) (k + 1)))
      (numeralI_lt hΓ hk2)
  -- tricotomía de `√n̄` contra `k̄`
  have htri := specI (specI (ax19I hΓ) (sqrt (numeralM n))) (numeralM k)
  have htri' : Γ ⊢ᵢ Formula.or (lt (sqrt (numeralM n)) (numeralM k))
      (Formula.or (Formula.eq (sqrt (numeralM n)) (numeralM k))
                  (lt (numeralM k) (sqrt (numeralM n)))) := by
    simpa [ax19_lt_trichotomy, forall_2, substFormula, substTerms, substTerm, lt,
      grounded_liftTerm L hsg, grounded_liftTerm L hkg,
      grounded_substTerm L hsg, grounded_substTerm L hkg] using htri
  refine Derivesᵢ.elim_or _ _ _ _ htri' ?_ ?_
  · -- `√n̄ < k̄` ⇒ `σ√n̄ ≤ k̄` ⇒ `(σ√n̄)² ≤ k̄² ≤ n̄`, contra `ax15`
    refine Derivesᵢ.bot_elim _ _ ?_
    have hΓ1 : ∀ g, List.Mem g arithAxioms →
        (lt (sqrt (numeralM n)) (numeralM k) :: Γ) ⊢ᵢ g :=
      hyps_cons hΓ (lt (sqrt (numeralM n)) (numeralM k))
    have hW : ∀ {f : Formula}, Γ ⊢ᵢ f → (lt (sqrt (numeralM n)) (numeralM k) :: Γ) ⊢ᵢ f :=
      fun hf => Derivesᵢ.weakening _ _ _ hf (fun _ hz => List.Mem.tail _ hz)
    have hlift1 : (lt (sqrt (numeralM n)) (numeralM k) :: Γ).map (liftFormula 0)
        = lt (sqrt (numeralM n)) (numeralM k) :: Γ := by
      simp only [List.map_cons, hlift, liftFormula, liftTerms, lt,
        grounded_liftTerm L hsg, grounded_liftTerm L hkg]
    have hsucc := Derivesᵢ.elim_impl _ _ _
      (hW (ltI_succ_le hΓ hlift hsu hsg hkg)) (Derivesᵢ.hyp _ _ (List.Mem.head _))
    have hsq1 := leI_mul_self hΓ1 hlift1 hm hssg hkg hsucc
    have hle := leI_trans hΓ1 hlift1 (grounded_func2 L hm hssg hssg)
      (grounded_func2 L hm hkg hkg) hng hsq1 (hW hkn)
    exact notI_lt_of_le hΓ1 hlift1 (grounded_func2 L hm hssg hssg) hng
      hle (hW (ax15I h15 L hng))
  refine Derivesᵢ.elim_or _ _ _ _ (Derivesᵢ.hyp _ _ (List.Mem.head _)) ?_ ?_
  · exact Derivesᵢ.hyp _ _ (List.Mem.head _)
  · -- `k̄ < √n̄` ⇒ `σk̄ ≤ √n̄` ⇒ `(σk̄)² ≤ (√n̄)² ≤ n̄`, contra `n < (k+1)²`
    refine Derivesᵢ.bot_elim _ _ ?_
    have hΓ3 : ∀ g, List.Mem g arithAxioms →
        (lt (numeralM k) (sqrt (numeralM n))
          :: Formula.or (Formula.eq (sqrt (numeralM n)) (numeralM k))
               (lt (numeralM k) (sqrt (numeralM n))) :: Γ) ⊢ᵢ g :=
      hyps_cons (hyps_cons hΓ _) _
    have hW3 : ∀ {f : Formula}, Γ ⊢ᵢ f →
        (lt (numeralM k) (sqrt (numeralM n))
          :: Formula.or (Formula.eq (sqrt (numeralM n)) (numeralM k))
               (lt (numeralM k) (sqrt (numeralM n))) :: Γ) ⊢ᵢ f :=
      fun hf => Derivesᵢ.weakening _ _ _ hf
        (fun _ hz => List.Mem.tail _ (List.Mem.tail _ hz))
    have hlift3 : (lt (numeralM k) (sqrt (numeralM n))
          :: Formula.or (Formula.eq (sqrt (numeralM n)) (numeralM k))
               (lt (numeralM k) (sqrt (numeralM n))) :: Γ).map (liftFormula 0)
        = lt (numeralM k) (sqrt (numeralM n))
          :: Formula.or (Formula.eq (sqrt (numeralM n)) (numeralM k))
               (lt (numeralM k) (sqrt (numeralM n))) :: Γ := by
      simp only [List.map_cons, hlift, liftFormula, liftTerms, lt,
        grounded_liftTerm L hsg, grounded_liftTerm L hkg]
    have hsucc := Derivesᵢ.elim_impl _ _ _
      (hW3 (ltI_succ_le hΓ hlift hsu hkg hsg)) (Derivesᵢ.hyp _ _ (List.Mem.head _))
    have hsq3 := leI_mul_self hΓ3 hlift3 hm hskg hsg hsucc
    have hle := leI_trans hΓ3 hlift3 (grounded_func2 L hm hskg hskg)
      (grounded_func2 L hm hsg hsg) hng hsq3 (hW3 (ax14I h14 L hng))
    exact notI_lt_of_le hΓ3 hlift3 (grounded_func2 L hm hskg hskg) hng hle (hW3 hnk)



end PeanoRF.HA
