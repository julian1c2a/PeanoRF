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


end PeanoRF.HA

#print axioms PeanoRF.HA.notI_lt_zero
#print axioms PeanoRF.HA.zeroI_or_succ
