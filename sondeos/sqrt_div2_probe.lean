-- SONDEO 2026-09-22 — ¿están `√` y `/₂` DETERMINADOS sobre numerales?
--
-- ADR-037 puso ⛔ en las dos casillas y lo dejó dicho como ARGUMENTO: «`/₂` pide
-- cancelación de `+` y `·`», «`√` habría que casar sobre `√n̄`, que es un término».
-- Este sondeo mide si ese argumento se sostiene, porque hay una vía que no se probó:
--
--   `√` y `/₂` están caracterizados por el ORDEN. Y el orden de Q⁺⁺ es TOTAL (ax19) y
--   compatible con la suma: de `a < b` sale `a + c < b + c` por ax13 SIN inducción. Si eso
--   va, la tricotomía contra el numeral candidato cierra los dos casos malos por ax18.
--
-- ⚠️ Donde la vía se rompería: Q⁺⁺ **no tiene** el axioma «todo x es 0 o sucesor» (Q sí lo
-- tiene; `coreAxioms` no). La apuesta es que NO hace falta como axioma porque se DERIVA:
--   · `x < 0` es imposible — `x + σk = 0` choca con ax5 + ax2;
--   · luego la tricotomía contra `0` da `x = 0 ∨ 0 < x`;
--   · y `0 < x` da `x = σi` por ax13 + ax4 + ax6.
--
-- Uso: lake env lean sondeos/sqrt_div2_probe.lean

import PeanoRF.HA.Fragment
open FOL PeanoRF.Calculus ROBINSON_PlusPlus.Minimal.Axioms
namespace PeanoRF.HA

set_option autoImplicit false
set_option linter.unusedSimpArgs false

variable {Γ : List Formula}

/-- Pertenencia a `arithAxioms` sin escribir la cadena de `tail` a mano. -/
local macro "memA" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

/-! ## Paso 0 · los axiomas del orden, accesibles -/

theorem ax13I (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g) : Γ ⊢ᵢ ax13_lt_def :=
  hΓ ax13_lt_def (by memA)

theorem ax18I (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g) : Γ ⊢ᵢ ax18_lt_irrefl :=
  hΓ ax18_lt_irrefl (by memA)

theorem ax19I (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g) : Γ ⊢ᵢ ax19_lt_trichotomy :=
  hΓ ax19_lt_trichotomy (by memA)

/-! ## Paso 1 · la dirección ⇐ de `ax13` para términos ANCLADOS

    `numeralI_lt` ya la usa, pero clavada a numerales: los lifts se van con
    `liftTerm_numeralM`. Para un término cualquiera hacen falta las dos clausuras del
    dominio, que es justo lo que `Grounded` da (`grounded_liftTerm`, `grounded_substTerm`). -/

example (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
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


/-! ## Paso 2 · la dirección ⇒ de `ax13`, y con ella `¬(t < 0)`

    ⭐ **Éste es el paso que decide el sondeo.** Si sale, Q⁺⁺ demuestra «todo x es 0 o
    sucesor» —que en Q es un AXIOMA y aquí no está— y con eso el orden se vuelve manejable:
    `0 ≤ x` para todo `x`, luego `x ≤ x + m`, luego monotonía, luego la tricotomía contra
    el numeral candidato cierra `√` y `/₂`. -/

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


/-! ## Paso 3 · ⭐⭐ **«todo término es 0 o sucesor»** — que en Q es un AXIOMA

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

/-- ⭐⭐ **Todo término anclado es cero o un sucesor.** -/
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




/-! ## Paso 4 · la cadena de MONOTONÍA

    Con `ax13` en las dos direcciones, la monotonía de la suma es un cálculo: si
    `a + σj = b`, entonces `(a+c) + σj = (a+σj) + c = b + c`. **Ni cancelación ni
    inducción.** -/

/-- Asociatividad de `+` para términos ANCLADOS (`ax7`). El anclaje hace falta por los
    `liftTerm` anidados que deja `forall_3`, que `substTerm_liftTerm` sola no deshace. -/
theorem addI_assoc (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (L : String → Nat → Bool) {t : Term} (ht : Grounded L t) (u v : Term) :
    Γ ⊢ᵢ Formula.eq (add (add t u) v) (add t (add u v)) := by
  have h := specI (specI (specI (hΓ ax7_add_assoc (by memA)) t) u) v
  simpa (config := { decide := true }) only [ax7_add_assoc, forall_3, substFormula,
    substTerms, substTerm, ite_true, ite_false, Nat.reduceAdd, add,
    substTerm_liftTerm, grounded_liftTerm L ht, grounded_substTerm L ht] using h

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
    eqI_trans (addI_assoc hΓ1 L ha c (succ (Term.var 0)))
      (eqI_trans (eqI_congr_fun2_r add_sym a (addI_comm hΓ1 c (succ (Term.var 0))))
        (eqI_symm (addI_assoc hΓ1 L ha (succ (Term.var 0)) c)))
  exact ltI_of_add hΓ1 L (grounded_add hs ha hc) (grounded_add hs hb hc) (Term.var 0)
    (eqI_trans hstep (eqI_congr_fun2_l add_sym c hA))


/-! ## Paso 5 · el producto: `t·2̄ = t + t` y la distributividad por la derecha -/

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

/-- Distributividad por la IZQUIERDA (`ax12`), con el primer argumento anclado. -/
theorem mulI_distrib (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (L : String → Nat → Bool) {t : Term} (ht : Grounded L t) (u v : Term) :
    Γ ⊢ᵢ Formula.eq (mul t (add u v)) (add (mul t u) (mul t v)) := by
  have h := specI (specI (specI (hΓ ax12_mul_distrib (by memA)) t) u) v
  simpa (config := { decide := true }) only [ax12_mul_distrib, forall_3, substFormula,
    substTerms, substTerm, ite_true, ite_false, Nat.reduceAdd, mul, add,
    substTerm_liftTerm, grounded_liftTerm L ht, grounded_substTerm L ht] using h

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


/-! ## Paso 6 · ⭐⭐ monotonía del producto por `2̄` — SIN transitividad

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
    mulI_distrib hΓ1 L h2g y (succ (Term.var 0))
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


/-! ## Paso 7 · 🏁 `/₂` SOBRE NUMERALES — el veredicto

    `ax17` da `(/₂ n̄)·2̄ + %₂ n̄ = n̄`, y `numeralI_mod2` ya fija `%₂ n̄`. La tricotomía
    contra `(n/2)‾` cierra las dos ramas malas por monotonía + `ax18`.

    ⛔ **Y con esto el ⛔ de ADR-037 para `/₂` queda refutado**: no hacía falta cancelar
    nada. -/

theorem ltI_irrefl (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (L : String → Nat → Bool) {t : Term} (ht : Grounded L t) :
    Γ ⊢ᵢ Formula.impl (lt t t) Formula.bottom := by
  have h := specI (ax18I hΓ) t
  simpa (config := { decide := true }) only [ax18_lt_irrefl, forall_, neg, substFormula,
    substTerms, substTerm, ite_true, ite_false, lt] using h

/-- `ax17` instanciado en un término anclado. -/
theorem ax17I (h17 : Γ ⊢ᵢ ax17_div_mod_eq) (L : String → Nat → Bool)
    {t : Term} (ht : Grounded L t) :
    Γ ⊢ᵢ Formula.eq (add (mul (div2 t) (numeralM 2)) (mod2 t)) t := by
  have h := specI h17 t
  simpa (config := { decide := true }) only [ax17_div_mod_eq, forall_, substFormula,
    substTerms, substTerm, ite_true, ite_false, add, mul, div2, mod2, two, one, zero,
    succ, numeralM, grounded_substTerm L ht] using h

/-- 🏁 **`/₂ n̄` ES demostrablemente `(n/2)‾`.** -/
theorem numeralI_div2 (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (hTM : ∀ g, List.Mem g arithTMAxioms → Γ ⊢ᵢ g)
    (h17 : Γ ⊢ᵢ ax17_div_mod_eq)
    (hlift : Γ.map (liftFormula 0) = Γ)
    {L : String → Nat → Bool} (hm : L mul_sym 2 = true) (ha2 : L add_sym 2 = true)
    (hsu : L succ_sym 1 = true) (hd : L div2_sym 1 = true) (n : Nat) :
    Γ ⊢ᵢ Formula.eq (div2 (numeralM n)) (numeralM (n / 2)) := by
  have hng : Grounded L (numeralM n) := grounded_numeralM L hsu n
  have hyg : Grounded L (div2 (numeralM n)) := grounded_func1 L hd hng
  have hkg : Grounded L (numeralM (n / 2)) := grounded_numeralM L hsu (n / 2)
  -- (1) `(/₂ n̄)·2̄ + (n%2)‾ = n̄`
  have hy : Γ ⊢ᵢ Formula.eq
      (add (mul (div2 (numeralM n)) (numeralM 2)) (numeralM (n % 2))) (numeralM n) :=
    eqI_trans (eqI_congr_fun2_r add_sym (mul (div2 (numeralM n)) (numeralM 2))
      (eqI_symm (numeralI_mod2 hTM n))) (ax17I h17 L hng)
  -- (2) `(n/2)‾·2̄ + (n%2)‾ = n̄`
  have hk : Γ ⊢ᵢ Formula.eq
      (add (mul (numeralM (n / 2)) (numeralM 2)) (numeralM (n % 2))) (numeralM n) := by
    have hmul := numeralI_mul hΓ (n / 2) 2
    have hadd := numeralI_add hΓ (n / 2 * 2) (n % 2)
    rw [show n / 2 * 2 + n % 2 = n from by omega] at hadd
    exact eqI_trans (eqI_congr_fun2_l add_sym (numeralM (n % 2)) hmul) hadd
  -- (3) tricotomía
  have htri := specI (specI (ax19I hΓ) (div2 (numeralM n))) (numeralM (n / 2))
  have htri' : Γ ⊢ᵢ Formula.or (lt (div2 (numeralM n)) (numeralM (n / 2)))
      (Formula.or (Formula.eq (div2 (numeralM n)) (numeralM (n / 2)))
                  (lt (numeralM (n / 2)) (div2 (numeralM n)))) := by
    simpa [ax19_lt_trichotomy, forall_2, substFormula, substTerms, substTerm, lt,
      grounded_liftTerm L hyg, grounded_liftTerm L hkg,
      grounded_substTerm L hyg, grounded_substTerm L hkg] using htri
  -- una rama mala, parametrizada por el lado
  have bad : ∀ (p q : Term), Grounded L p → Grounded L q →
      Γ ⊢ᵢ Formula.eq (add (mul p (numeralM 2)) (numeralM (n % 2))) (numeralM n) →
      Γ ⊢ᵢ Formula.eq (add (mul q (numeralM 2)) (numeralM (n % 2))) (numeralM n) →
      (lt p q :: Γ) ⊢ᵢ Formula.bottom := by
    intro p q hp hq hep heq
    have hΓ1 : ∀ g, List.Mem g arithAxioms → (lt p q :: Γ) ⊢ᵢ g := hyps_cons hΓ (lt p q)
    have hlt2 := Derivesᵢ.elim_impl _ _ _
      (Derivesᵢ.weakening _ _ _
        (ltI_mul_two hΓ hlift hm hsu hp hq) (fun _ hz => List.Mem.tail _ hz))
      (Derivesᵢ.hyp _ _ (List.Mem.head _))
    have hmono := Derivesᵢ.elim_impl _ _ _
      (Derivesᵢ.weakening _ _ _
        (ltI_add_right hΓ hlift ha2 (L := L) (grounded_func2 L hm hp
          (grounded_numeralM L hsu 2)) (grounded_func2 L hm hq
          (grounded_numeralM L hsu 2)) (grounded_numeralM L hsu (n % 2)))
        (fun _ hz => List.Mem.tail _ hz))
      hlt2
    -- `p·2̄ + r̄ < q·2̄ + r̄`, y los dos lados son `n̄`
    have hepW : (lt p q :: Γ) ⊢ᵢ Formula.eq
        (add (mul p (numeralM 2)) (numeralM (n % 2))) (numeralM n) :=
      Derivesᵢ.weakening _ _ _ hep (fun _ hz => List.Mem.tail _ hz)
    have heqW : (lt p q :: Γ) ⊢ᵢ Formula.eq
        (add (mul q (numeralM 2)) (numeralM (n % 2))) (numeralM n) :=
      Derivesᵢ.weakening _ _ _ heq (fun _ hz => List.Mem.tail _ hz)
    have hnn : (lt p q :: Γ) ⊢ᵢ lt (numeralM n) (numeralM n) :=
      eqI_rw_atom2_r lt_sym (numeralM n) heqW (eqI_rw_atom2_l lt_sym _ hepW hmono)
    exact Derivesᵢ.elim_impl _ _ _
      (ltI_irrefl hΓ1 L (grounded_numeralM L hsu n)) hnn
  -- las tres ramas
  refine Derivesᵢ.elim_or _ _ _ _ htri' ?_ ?_
  · exact Derivesᵢ.bot_elim _ _ (bad _ _ hyg hkg hy hk)
  refine Derivesᵢ.elim_or _ _ _ _ (Derivesᵢ.hyp _ _ (List.Mem.head _)) ?_ ?_
  · exact Derivesᵢ.hyp _ _ (List.Mem.head _)
  · exact Derivesᵢ.bot_elim _ _ (Derivesᵢ.weakening _ _ _ (bad _ _ hkg hyg hk hy)
      (fun _ hz => match hz with
        | List.Mem.head _ => List.Mem.head _
        | List.Mem.tail _ h => List.Mem.tail _ (List.Mem.tail _ h)))



/-! ## Paso 8 · hacia `√`: lo que el cuadrado pide

    `√` se caracteriza por DOS desigualdades (`ax14`: `(√n)² ≤ n`, `ax15`: `n < (σ√n)²`), así
    que hace falta monotonía del CUADRADO y la transitividad que `/₂` se pudo saltar. -/

/-- ⭐ **Ningún término anclado cumple `x + σy = x`.** `addI_succ_ne` hacía esto para
    numerales, con inducción META. Para términos anclados sale GRATIS: `x + σy = x` es
    justo `x < x` por `ax13`, y `ax18` lo prohíbe. -/
theorem notI_add_succ_self (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (L : String → Nat → Bool) {x : Term} (hx : Grounded L x) (y : Term) :
    Γ ⊢ᵢ Formula.impl (Formula.eq (add x (succ y)) x) Formula.bottom := by
  refine Derivesᵢ.intro_impl _ (Formula.eq (add x (succ y)) x) Formula.bottom ?_
  have hΓ1 : ∀ g, List.Mem g arithAxioms →
      (Formula.eq (add x (succ y)) x :: Γ) ⊢ᵢ g :=
    hyps_cons hΓ (Formula.eq (add x (succ y)) x)
  exact Derivesᵢ.elim_impl _ _ _ (ltI_irrefl hΓ1 L hx)
    (ltI_of_add hΓ1 L hx hx y (Derivesᵢ.hyp _ _ (List.Mem.head _)))

/-- ⭐ **Transitividad de `<`.** `a+σj=b` y `b+σi=c` dan `a + σ(j + σi) = c`. -/
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
    (eqI_symm (addI_assoc hΓ2 L ha (succ (Term.var 1)) (succ (Term.var 0))))

end PeanoRF.HA

#print axioms PeanoRF.HA.numeralI_div2
#print axioms PeanoRF.HA.notI_add_succ_self
#print axioms PeanoRF.HA.ltI_trans
