/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.HA.Domain
import PeanoRF.HA.Arith

/-! # Los axiomas que NO son de Harrop — barrarlos uno a uno

  `HA/Domain.lean` deja la propiedad de disyunción de HA en tres obligaciones, y **28 de los
  34 axiomas caen solos** por ser de Harrop. Éste es el módulo de los **6 que no**:

  | axioma | por qué no es de Harrop |
  |---|---|
  | `ax13_lt_def` | `n < m ⇔ ∃k. n + σk = m` — un `∃` en el consecuente |
  | `ax14_sqrt_le` | `√x · √x ≤ x`, y **`le a b` es `a < b ∨ a = b`** |
  | `ax19_lt_trichotomy` | `n < m ∨ n = m ∨ m < n` |
  | `ax21_mod2_range` | `%₂x = 0 ∨ %₂x = 1` |
  | `ax_L2_in_cons` | `x ∈ y::l ⇔ (x = y ∨ x ∈ l)` |
  | `ax_L3_in_concat` | `x ∈ l ## m ⇔ (x ∈ l ∨ x ∈ m)` |

  ## La forma que tienen todos

  Barrar una disyunción pide **elegir una rama**, y eso es una decisión en el META. La
  herramienta es siempre la misma: si todo término del dominio es demostrablemente igual a
  un **numeral**, la decisión se toma sobre números y la derivación se reconstruye por
  Leibniz. Eso es `hNum`, que va como hipótesis mientras no esté demostrada:

  > `hNum : ∀ t, Grounded LQpp t → ∃ n, ctx insts ⊢ᵢ (t =eq numeralM n)`

  ⚠️ **`hNum` no es gratis y no se esconde.** `closed_term_eq_numeral` la da para los cinco
  símbolos de los numerales, pero el lenguaje tiene **trece**: falta evaluar `√`, `/₂`, `%₂`,
  `τ`, `−`, `::`, `##` y `Π_p` sobre numerales dentro de Q⁺⁺, y algunas de esas
  evaluaciones necesitan instancias del esquema de inducción.
-/

namespace PeanoRF.HA

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open PeanoRF.Calculus
open ROBINSON_PlusPlus.Full (inductionFormula)

set_option autoImplicit false

/-! ## 1 · Debilitamiento desde `ctx []` -/

/-- El contexto de HA satisface el **fragmento aritmético**: es lo que deja usar los
    homomorfismos de numerales, que desde el 2026-09-21 van parametrizados por el contexto
    y no clavados a `ctx []`. -/
theorem arith_ctx {insts : List Formula} : ∀ g, List.Mem g arithAxioms → ctx insts ⊢ᵢ g :=
  fun g hg => ax' (arithAxioms_sub g hg)

/-- Lo demostrado sin instancias de inducción vale con ellas.

    🏗️ **ANDAMIO**: quedó sin uso el 2026-09-21, cuando los homomorfismos de numerales
    pasaron a ir parametrizados por el contexto y ya no hubo que debilitar desde `ctx []`. -/
theorem ctx_weaken {insts : List Formula} {f : Formula} (h : ctx [] ⊢ᵢ f) :
    ctx insts ⊢ᵢ f := by
  refine Derivesᵢ.weakening _ _ _ h ?_
  intro x hx
  exact mem_ctx_of_mem_axioms (by simpa [ctx] using hx)

/-! ## 2 · `n < m` en el objeto, decidido en el meta

    Es la primera pieza reutilizable: la dirección `⇐` de `ax13_lt_def` convierte un testigo
    aritmético en una desigualdad, y el testigo lo da `numeralI_add`. -/

theorem numeralI_lt {Γ : List Formula} (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g) {a b : Nat} (h : a < b) :
    Γ ⊢ᵢ lt (numeralM a) (numeralM b) := by
  have h13 : Γ ⊢ᵢ ax13_lt_def := hΓ ax13_lt_def (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))
  have hi := specI (specI h13 (numeralM a)) (numeralM b)
  have hback : Γ ⊢ᵢ
      Formula.impl (Formula.ex (Formula.eq (add (numeralM a) (succ (Term.var 0)))
                                           (numeralM b)))
                   (lt (numeralM a) (numeralM b)) := by
    have := Derivesᵢ.elim_and_r _ _ _ hi
    simpa [ax13_lt_def, forall_2, substFormula, substTerms, substTerm, lt, add, succ,
      iff, substTerm_numeralM, liftTerm_numeralM] using this
  refine Derivesᵢ.elim_impl _ _ _ hback ?_
  refine Derivesᵢ.intro_ex _ _ (numeralM (b - a - 1)) ?_
  have harith : a + (b - a - 1 + 1) = b := by omega
  have hadd := (numeralI_add hΓ a (b - a - 1 + 1))
  rw [harith] at hadd
  simpa [substFormula, substTerms, substTerm, add, succ, numeralM,
    substTerm_numeralM] using hadd

/-! ## 3 · ⭐ `ax19_lt_trichotomy` — el axioma que motivó todo el dominio

    Es el emblemático: su `∀` recorre términos de los que HA no sabe nada, y por eso hizo
    falta el parámetro de dominio (ADR-027). Con el dominio en la mano, barrarlo es
    **decidir la tricotomía en el meta** y reconstruir la derivación por Leibniz. -/

/-- ⭐⭐ **`ax19` barrado**, bajo la única hipótesis de que el dominio se evalúe a numerales.

    El patrón es el de los seis: `hNum` baja los dos términos a numerales, `Nat.lt_trichotomy`
    decide **en el meta**, y `numeralI_lt` + la reescritura dentro del predicado suben la
    decisión al objeto. -/
theorem slash_ax19 {Γ : List Formula} (L : String → Nat → Bool) (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (hNum : ∀ t : Term, Grounded L t →
      ∃ n : Nat, Γ ⊢ᵢ (Formula.eq t (numeralM n))) :
    Slash (Γ) (Grounded L) ax19_lt_trichotomy := by
  have hax : Γ ⊢ᵢ ax19_lt_trichotomy := hΓ ax19_lt_trichotomy (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))
  refine (slash_forall _ _ _).mpr ⟨hax, fun t hDt => ?_⟩
  have h1 := specI hax t
  simp only [substFormula, grounded_liftTerm L hDt] at h1 ⊢
  refine (slash_forall _ _ _).mpr ⟨h1, fun u hDu => ?_⟩
  simp only [substFormula, substTerms, substTerm, lt, reduceIte,
    grounded_substTerm L hDt]
  obtain ⟨n, hn⟩ := hNum t hDt
  obtain ⟨m, hm⟩ := hNum u hDu
  rcases Nat.lt_trichotomy n m with hlt | heq | hgt
  · refine (slash_or _ _ _ _).mpr (Or.inl ((slash_atom _ _ _ _).mpr ?_))
    exact eqI_rw_atom2_r lt_sym t (eqI_symm hm)
      (eqI_rw_atom2_l lt_sym (numeralM m) (eqI_symm hn) (numeralI_lt hΓ hlt))
  · subst heq
    refine (slash_or _ _ _ _).mpr (Or.inr ((slash_or _ _ _ _).mpr
      (Or.inl ((slash_eq _ _ _ _).mpr ?_))))
    exact eqI_trans hn (eqI_symm hm)
  · refine (slash_or _ _ _ _).mpr (Or.inr ((slash_or _ _ _ _).mpr
      (Or.inr ((slash_atom _ _ _ _).mpr ?_))))
    exact eqI_rw_atom2_r lt_sym u (eqI_symm hn)
      (eqI_rw_atom2_l lt_sym (numeralM n) (eqI_symm hm) (numeralI_lt hΓ hgt))

/-! ## 4 · ⭐ `n ≠ m` en el objeto — la versión CONSTRUCTIVA

    ⚠️ Aguas arriba existe `numeral_ne`, pero **arrastra `Classical`** (medido el 2026-09-16),
    así que no sirve en este árbol. Ésta se construye a mano con los dos axiomas de Peano que
    Q⁺⁺ tiene: `ax2` (`σx ≠ 0`) para las bases y `ax3` (`σ` inyectiva) para el paso. -/

/-- `⊢ᵢ ¬(n̄ = m̄)` cuando `n ≠ m`. Inducción META en el primero, generalizando el segundo. -/
theorem numeralI_ne {Γ : List Formula}
    (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g) : ∀ {a b : Nat}, a ≠ b →
    Γ ⊢ᵢ neg (Formula.eq (numeralM a) (numeralM b)) := by
  intro a
  induction a with
  | zero =>
      intro b hne
      match b with
      | 0 => exact absurd rfl hne
      | k + 1 =>
          have h2 : Γ ⊢ᵢ ax2_peano_succ_neq_zero := hΓ ax2_peano_succ_neq_zero (List.Mem.head _)
          have hi := specI h2 (numeralM k)
          simp only [substFormula, substTerms, substTerm, reduceIte,
            neg, succ, zero] at hi
          refine Derivesᵢ.intro_impl _ (Formula.eq (numeralM 0) (numeralM (k + 1)))
            Formula.bottom ?_
          refine Derivesᵢ.elim_impl _ (Formula.eq (succ (numeralM k)) zero)
            Formula.bottom ?_ ?_
          · exact Derivesᵢ.weakening _ _ _ hi (fun x hx => List.Mem.tail _ hx)
          · exact eqI_symm (Derivesᵢ.hyp _ _ (List.Mem.head _))
  | succ j ih =>
      intro b hne
      match b with
      | 0 =>
          have h2 : Γ ⊢ᵢ ax2_peano_succ_neq_zero := hΓ ax2_peano_succ_neq_zero (List.Mem.head _)
          have hi := specI h2 (numeralM j)
          simpa only [forall_, substFormula, substTerms, substTerm, reduceIte,
            neg, succ, zero, numeralM, substTerm_numeralM] using hi
      | k + 1 =>
          have h3 : Γ ⊢ᵢ ax3_peano_succ_inj := hΓ ax3_peano_succ_inj (List.Mem.tail _ (List.Mem.head _))
          have hi := specI (specI h3 (numeralM j)) (numeralM k)
          simp only [substFormula, substTerms, substTerm,
            reduceIte, succ, substTerm_numeralM, liftTerm_numeralM] at hi
          have hIH := ih (b := k) (by omega)
          refine Derivesᵢ.intro_impl _ (Formula.eq (numeralM (j + 1)) (numeralM (k + 1)))
            Formula.bottom ?_
          refine Derivesᵢ.elim_impl _ (Formula.eq (numeralM j) (numeralM k))
            Formula.bottom ?_ ?_
          · exact Derivesᵢ.weakening _ _ _ hIH (fun x hx => List.Mem.tail _ hx)
          · refine Derivesᵢ.elim_impl _ (Formula.eq (succ (numeralM j)) (succ (numeralM k)))
              (Formula.eq (numeralM j) (numeralM k)) ?_ (Derivesᵢ.hyp _ _ (List.Mem.head _))
            exact Derivesᵢ.weakening _ _ _ hi (fun x hx => List.Mem.tail _ hx)

/-! ## 5 · `ax21_mod2_range` — decidir el resto en el meta, y descartar lo imposible

    `∀x. %₂x = 0 ∨ %₂x = 1`. `hNum` da un numeral `k̄` con `⊢ᵢ %₂t = k̄`, pero **no dice que
    `k` sea 0 ó 1**: eso hay que descartarlo. Y se descarta con la propia disyunción del
    axioma más `numeralI_ne` — si `k ≥ 2`, las dos ramas dan `⊥`, lo que contradice la
    consistencia.

    ⚠️ Aquí es donde la consistencia deja de ser decorativa: es lo que convierte «la teoría
    demuestra que `%₂t` vale 0 ó 1» en «**yo sé cuál de los dos**». -/
theorem slash_ax21 {Γ : List Formula} (L : String → Nat → Bool)
    (hm : L mod2_sym 1 = true)
    (haxA : Γ ⊢ᵢ ax21_mod2_range) (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (hcon : ¬ (Γ ⊢ᵢ Formula.bottom))
    (hNum : ∀ t : Term, Grounded L t →
      ∃ n : Nat, Γ ⊢ᵢ (Formula.eq t (numeralM n))) :
    Slash (Γ) (Grounded L) ax21_mod2_range := by
  have hax : Γ ⊢ᵢ ax21_mod2_range := haxA
  refine (slash_forall _ _ _).mpr ⟨hax, fun t hDt => ?_⟩
  have h1 := specI hax t
  refine (slash_or _ _ _ _).mpr ?_
  obtain ⟨k, hk⟩ := hNum (mod2 t) (grounded_func1 L hm hDt)
  match k, hk with
  | 0, hk => exact Or.inl ((slash_eq _ _ _ _).mpr hk)
  | 1, hk => exact Or.inr ((slash_eq _ _ _ _).mpr hk)
  | (n + 2), hk =>
      refine absurd ?_ hcon
      refine Derivesᵢ.elim_or _ (Formula.eq (mod2 t) zero) (Formula.eq (mod2 t) one)
        Formula.bottom h1 ?_ ?_
      · refine Derivesᵢ.elim_impl _ (Formula.eq (numeralM (n + 2)) (numeralM 0))
          Formula.bottom
          (Derivesᵢ.weakening _ _ _ (numeralI_ne hΓ (a := n + 2) (b := 0) (by omega))
            (fun x hx => List.Mem.tail _ hx)) ?_
        exact eqI_trans
          (eqI_symm (Derivesᵢ.weakening _ _ _ hk (fun x hx => List.Mem.tail _ hx)))
          (Derivesᵢ.hyp _ _ (List.Mem.head _))
      · refine Derivesᵢ.elim_impl _ (Formula.eq (numeralM (n + 2)) (numeralM 1))
          Formula.bottom
          (Derivesᵢ.weakening _ _ _ (numeralI_ne hΓ (a := n + 2) (b := 1) (by omega))
            (fun x hx => List.Mem.tail _ hx)) ?_
        exact eqI_trans
          (eqI_symm (Derivesᵢ.weakening _ _ _ hk (fun x hx => List.Mem.tail _ hx)))
          (Derivesᵢ.hyp _ _ (List.Mem.head _))

/-! ## 6 · `ax_L2_in_cons` — la disyunción se resuelve SIN decidir el predicado

    `∀x∀y∀l. (x ∈ y::l ⇔ (x = y ∨ x ∈ l))`. La dirección `⇐` es el argumento de Harrop: el
    consecuente es atómico. La `⇒` pide elegir rama, **y aquí no hace falta decidir `∈`**:
    basta decidir `x = y` sobre numerales. Si son iguales, primera rama; si no, `numeralI_ne`
    **refuta** la primera y la disyunción del objeto entrega la segunda.

    ⭐ Ése es el patrón que `ax_L3_in_concat` **no** tiene: allí las dos ramas son `∈`, y no
    hay nada que refutar sin decidir el predicado.

    ⚠️ Y no hace falta la consistencia: la contradicción se usa **bajo la hipótesis `x = y`**,
    dentro de una rama de `elim_or`, no en la teoría. -/
theorem slash_axL2 {insts : List Formula}
    (hNum : ∀ t : Term, Grounded LQpp t →
      ∃ n : Nat, ctx insts ⊢ᵢ (Formula.eq t (numeralM n))) :
    Slash (ctx insts) (Grounded LQpp) ax_L2_in_cons := by
  have hax : ctx insts ⊢ᵢ ax_L2_in_cons := ax' (by simp [coreAxioms])
  simp only [ax_L2_in_cons, forall_3, iff, lor, In, cons] at hax ⊢
  refine (slash_forall _ _ _).mpr ⟨hax, fun x hDx => ?_⟩
  have h1 := specI hax x
  simp (config := { decide := true }) only [substFormula, substTerms, substTerm,
    ite_true, ite_false, grounded_liftTerm LQpp hDx] at h1 ⊢
  refine (slash_forall _ _ _).mpr ⟨h1, fun y hDy => ?_⟩
  have h2 := specI h1 y
  simp (config := { decide := true }) only [substFormula, substTerms, substTerm,
    ite_true, ite_false, Nat.reduceAdd, grounded_liftTerm LQpp hDy,
    grounded_substTerm LQpp hDx] at h2 ⊢
  refine (slash_forall _ _ _).mpr ⟨h2, fun l hDl => ?_⟩
  have h3 := specI h2 l
  simp (config := { decide := true }) only [substFormula, substTerms, substTerm,
    ite_true, ite_false, grounded_substTerm LQpp hDx,
    grounded_substTerm LQpp hDy] at h3 ⊢
  refine (slash_and _ _ _ _).mpr ⟨?_, ?_⟩
  · refine (slash_impl _ _ _ _).mpr ⟨Derivesᵢ.elim_and_l _ _ _ h3, fun hA => ?_⟩
    have hdis : ctx insts ⊢ᵢ
        Formula.or (Formula.eq x y) (Formula.atom in_sym [x, l]) :=
      Derivesᵢ.elim_impl _ _ _ (Derivesᵢ.elim_and_l _ _ _ h3)
        ((slash_atom _ _ _ _).mp hA)
    obtain ⟨n, hn⟩ := hNum x hDx
    obtain ⟨m, hm⟩ := hNum y hDy
    by_cases hnm : n = m
    · subst hnm
      exact (slash_or _ _ _ _).mpr
        (Or.inl ((slash_eq _ _ _ _).mpr (eqI_trans hn (eqI_symm hm))))
    · refine (slash_or _ _ _ _).mpr (Or.inr ((slash_atom _ _ _ _).mpr ?_))
      refine Derivesᵢ.elim_or _ (Formula.eq x y) (Formula.atom in_sym [x, l])
        (Formula.atom in_sym [x, l]) hdis ?_ (Derivesᵢ.hyp _ _ (List.Mem.head _))
      refine Derivesᵢ.bot_elim _ _ ?_
      refine Derivesᵢ.elim_impl _ (Formula.eq (numeralM n) (numeralM m)) Formula.bottom
        (Derivesᵢ.weakening _ _ _ (numeralI_ne arith_ctx hnm) (fun _ hz => List.Mem.tail _ hz)) ?_
      exact eqI_trans
        (eqI_symm (Derivesᵢ.weakening _ _ _ hn (fun _ hz => List.Mem.tail _ hz)))
        (eqI_trans (Derivesᵢ.hyp _ _ (List.Mem.head _))
          (Derivesᵢ.weakening _ _ _ hm (fun _ hz => List.Mem.tail _ hz)))
  · refine (slash_impl _ _ _ _).mpr ⟨Derivesᵢ.elim_and_r _ _ _ h3, fun hB => ?_⟩
    exact (slash_atom _ _ _ _).mpr
      (Derivesᵢ.elim_impl _ _ _ (Derivesᵢ.elim_and_r _ _ _ h3)
        (slash_derives _ _ _ hB))

/-! ## 7 · Las instancias de los axiomas de la suma, en un contexto CUALQUIERA

    ⚠️ Parametrizadas por `hΓ` en vez de fijadas a `ctx insts`, y no por gusto: dentro de
    `elim_ex` el contexto es `A :: Γ.map (liftFormula 0)`, y ahí los axiomas no est\u00e1n
    literalmente — hay que meterlos por la invariancia de `Γ` bajo levantamiento. Con `hΓ`
    los mismos lemas sirven a los dos lados. -/

theorem addI_zero {Γ : List Formula} (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g) (t : Term) :
    Γ ⊢ᵢ (Formula.eq (add t zero) t) := by
  have h := specI (hΓ ax4_add_zero (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) t
  simpa (config := { decide := true }) only [ax4_add_zero, forall_, substFormula,
    substTerms, substTerm, ite_true, ite_false, add, zero] using h

theorem addI_succ {Γ : List Formula} (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g) (t u : Term) :
    Γ ⊢ᵢ (Formula.eq (add t (succ u)) (succ (add t u))) := by
  have h := specI (specI (hΓ ax5_add_succ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) t) u
  simpa (config := { decide := true }) only [ax5_add_succ, forall_2, substFormula,
    substTerms, substTerm, ite_true, ite_false, Nat.reduceAdd, add, succ,
    substTerm_liftTerm] using h

theorem addI_comm {Γ : List Formula} (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g) (t u : Term) :
    Γ ⊢ᵢ (Formula.eq (add t u) (add u t)) := by
  have h := specI (specI (hΓ ax6_add_comm (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))) t) u
  simpa (config := { decide := true }) only [ax6_add_comm, forall_2, substFormula,
    substTerms, substTerm, ite_true, ite_false, Nat.reduceAdd, add,
    substTerm_liftTerm] using h

theorem succI_ne_zero {Γ : List Formula} (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (t : Term) : Γ ⊢ᵢ Formula.impl (Formula.eq (succ t) zero) Formula.bottom := by
  have h := specI (hΓ ax2_peano_succ_neq_zero (List.Mem.head _)) t
  simpa (config := { decide := true }) only [ax2_peano_succ_neq_zero, forall_, neg,
    substFormula, substTerms, substTerm, ite_true, ite_false, succ, zero] using h

theorem succI_inj {Γ : List Formula} (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g) (t u : Term) :
    Γ ⊢ᵢ Formula.impl (Formula.eq (succ t) (succ u)) (Formula.eq t u) := by
  have h := specI (specI (hΓ ax3_peano_succ_inj (List.Mem.tail _ (List.Mem.head _))) t) u
  simpa (config := { decide := true }) only [ax3_peano_succ_inj, forall_2, substFormula,
    substTerms, substTerm, ite_true, ite_false, Nat.reduceAdd, succ,
    substTerm_liftTerm] using h

/-- Los axiomas sobreviven a meter una hipótesis en el contexto. -/
theorem hyps_cons {Γ : List Formula} (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (A : Formula) : ∀ g, List.Mem g arithAxioms → (A :: Γ) ⊢ᵢ g :=
  fun g hg => Derivesᵢ.weakening _ _ _ (hΓ g hg) (fun _ hz => List.Mem.tail _ hz)

/-! ## 8 · ⭐⭐ Ningún numeral es `x + σy`

    Es la pieza que faltaba para `ax13`, y la única que necesita **inducción meta sobre el
    numeral**. Q⁺⁺ no prueba la cancelación de la suma —eso pide inducción en el objeto—,
    pero **para un numeral concreto** la recursión meta la sustituye: `σc̄ + σj = σc̄` se
    reduce por conmutatividad, `ax5` y la inyectividad de `σ` a `c̄ + σj = c̄`, que es la
    hipótesis de inducción. La base la cierra `ax2`. -/
theorem addI_succ_ne {Γ : List Formula} (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g) :
    ∀ (b : Nat) (j : Term), Γ ⊢ᵢ Formula.impl
      (Formula.eq (add (numeralM b) (succ j)) (numeralM b)) Formula.bottom := by
  intro b
  induction b with
  | zero =>
      intro j
      refine Derivesᵢ.intro_impl _
        (Formula.eq (add (numeralM 0) (succ j)) (numeralM 0)) Formula.bottom ?_
      have hΔ := hyps_cons hΓ (Formula.eq (add (numeralM 0) (succ j)) (numeralM 0))
      have hhyp : (Formula.eq (add (numeralM 0) (succ j)) (numeralM 0)) :: Γ ⊢ᵢ
          Formula.eq (add zero (succ j)) zero := Derivesᵢ.hyp _ _ (List.Mem.head _)
      exact Derivesᵢ.elim_impl _ _ _ (succI_ne_zero hΔ j)
        (eqI_trans (eqI_symm (eqI_trans (addI_comm hΔ zero (succ j))
          (addI_zero hΔ (succ j)))) hhyp)
  | succ c ih =>
      intro j
      refine Derivesᵢ.intro_impl _
        (Formula.eq (add (numeralM (c + 1)) (succ j)) (numeralM (c + 1))) Formula.bottom ?_
      have hΔ := hyps_cons hΓ
        (Formula.eq (add (numeralM (c + 1)) (succ j)) (numeralM (c + 1)))
      have hhyp : (Formula.eq (add (numeralM (c + 1)) (succ j)) (numeralM (c + 1))) :: Γ ⊢ᵢ
          Formula.eq (add (succ (numeralM c)) (succ j)) (succ (numeralM c)) :=
        Derivesᵢ.hyp _ _ (List.Mem.head _)
      have h3 : _ ⊢ᵢ Formula.eq (succ (add (succ j) (numeralM c))) (succ (numeralM c)) :=
        eqI_trans (eqI_symm (eqI_trans (addI_comm hΔ (succ (numeralM c)) (succ j))
          (addI_succ hΔ (succ j) (numeralM c)))) hhyp
      have h4 := Derivesᵢ.elim_impl _ _ _
        (succI_inj hΔ (add (succ j) (numeralM c)) (numeralM c)) h3
      exact Derivesᵢ.elim_impl _ _ _
        (Derivesᵢ.weakening _ _ _ (ih j) (fun _ hz => List.Mem.tail _ hz))
        (eqI_trans (addI_comm hΔ (numeralM c) (succ j)) h4)

/-- Asociatividad, con los dos primeros argumentos NUMERALES. Basta para lo que hace falta y
    evita pelearse con el doble levantamiento de `forall_3`. -/
theorem addI_assoc_num {Γ : List Formula} (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (p q : Nat) (v : Term) :
    Γ ⊢ᵢ (Formula.eq (add (add (numeralM p) (numeralM q)) v)
                     (add (numeralM p) (add (numeralM q) v))) := by
  have h := specI (specI (specI (hΓ ax7_add_assoc
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.head _))))))) (numeralM p)) (numeralM q)) v
  simpa (config := { decide := true }) only [ax7_add_assoc, forall_3, substFormula,
    substTerms, substTerm, ite_true, ite_false, Nat.reduceAdd, add,
    substTerm_numeralM, liftTerm_numeralM] using h

/-- Los numerales están anclados: sólo llevan `0` y `σ`, y no tienen variables. -/
theorem grounded_numeralM (L : String → Nat → Bool) (hs : L succ_sym 1 = true) :
    ∀ n : Nat, Grounded L (numeralM n) := by
  intro n
  induction n with
  | zero => exact grounded_zero L
  | succ k ih => exact grounded_func1 L hs ih

/-! ## 9 · ⭐ `¬(ā < b̄)` cuando `b ≤ a`

    Es la otra mitad de `numeralI_lt`, y la que cuesta: hay que **refutar** una desigualdad,
    no construirla. Por la dirección `⇒` de `ax13` la hipótesis da un testigo `k` con
    `ā + σk = b̄`; escribiendo `ā = b̄ + d̄` (que es `numeralI_add`, con `d = a - b`) y usando
    asociatividad y `ax5`, eso se convierte en `b̄ + σ(d̄ + k) = b̄` — justo lo que
    `addI_succ_ne` prohíbe.

    ⚠️ **Pide que el contexto sea invariante bajo levantamiento**, y va dicho como hipótesis:
    dentro de `elim_ex` el contexto se levanta, y los axiomas tienen que seguir estando.
    `coreAxioms` lo es (`axioms_lift`); las instancias de inducción, sólo si son cerradas. -/
theorem numeralI_not_lt {Γ : List Formula} (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (hlift : Γ.map (liftFormula 0) = Γ)
    {a b : Nat} (hba : b ≤ a) :
    Γ ⊢ᵢ Formula.impl (lt (numeralM a) (numeralM b)) Formula.bottom := by
  have h13 : Γ ⊢ᵢ ax13_lt_def := hΓ ax13_lt_def (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))
  have hi := specI (specI h13 (numeralM a)) (numeralM b)
  have hfwd : Γ ⊢ᵢ
      Formula.impl (lt (numeralM a) (numeralM b))
        (Formula.ex (Formula.eq (add (numeralM a) (succ (Term.var 0))) (numeralM b))) := by
    have := Derivesᵢ.elim_and_l _ _ _ hi
    simpa [ax13_lt_def, forall_2, substFormula, substTerms, substTerm, lt, add, succ,
      iff, substTerm_numeralM, liftTerm_numeralM] using this
  refine Derivesᵢ.intro_impl _ (lt (numeralM a) (numeralM b)) Formula.bottom ?_
  have hex := Derivesᵢ.elim_impl _ _ _
    (Derivesᵢ.weakening _ _ _ hfwd (fun _ hz => List.Mem.tail _ hz))
    (Derivesᵢ.hyp _ _ (List.Mem.head _))
  refine Derivesᵢ.elim_ex _ _ _ hex ?_
  simp only [List.map_cons, hlift, liftFormula, liftTerms, lt, liftTerm_numeralM]
  have hΓ1 : ∀ g, List.Mem g arithAxioms →
      (Formula.eq (add (numeralM a) (succ (Term.var 0))) (numeralM b)
      :: lt (numeralM a) (numeralM b) :: Γ) ⊢ᵢ g :=
    hyps_cons (hyps_cons (hΓ)
      (lt (numeralM a) (numeralM b)))
      (Formula.eq (add (numeralM a) (succ (Term.var 0))) (numeralM b))
  have hA : (Formula.eq (add (numeralM a) (succ (Term.var 0))) (numeralM b)
      :: lt (numeralM a) (numeralM b) :: Γ) ⊢ᵢ Formula.eq (add (numeralM a) (succ (Term.var 0))) (numeralM b) :=
    Derivesᵢ.hyp _ _ (List.Mem.head _)
  have hbd : (Formula.eq (add (numeralM a) (succ (Term.var 0))) (numeralM b)
      :: lt (numeralM a) (numeralM b) :: Γ) ⊢ᵢ Formula.eq (add (numeralM b) (numeralM (a - b))) (numeralM a) := by
    have h := (numeralI_add hΓ b (a - b))
    rw [show b + (a - b) = a from by omega] at h
    exact Derivesᵢ.weakening _ _ _ h
      (fun _ hz => List.Mem.tail _ (List.Mem.tail _ hz))
  have hstep2 : (Formula.eq (add (numeralM a) (succ (Term.var 0))) (numeralM b)
      :: lt (numeralM a) (numeralM b) :: Γ) ⊢ᵢ Formula.eq
      (add (add (numeralM b) (numeralM (a - b))) (succ (Term.var 0))) (numeralM b) :=
    eqI_trans (eqI_congr_fun2_l add_sym (succ (Term.var 0)) hbd) hA
  have hcomb : (Formula.eq (add (numeralM a) (succ (Term.var 0))) (numeralM b)
      :: lt (numeralM a) (numeralM b) :: Γ) ⊢ᵢ Formula.eq
      (add (add (numeralM b) (numeralM (a - b))) (succ (Term.var 0)))
      (add (numeralM b) (succ (add (numeralM (a - b)) (Term.var 0)))) :=
    eqI_trans (addI_assoc_num hΓ1 b (a - b) (succ (Term.var 0)))
      (eqI_congr_fun2_r add_sym (numeralM b)
        (addI_succ hΓ1 (numeralM (a - b)) (Term.var 0)))
  exact Derivesᵢ.elim_impl _ _ _
    (addI_succ_ne hΓ1 b (add (numeralM (a - b)) (Term.var 0)))
    (eqI_trans (eqI_symm hcomb) hstep2)

/-! ## 10 · ⭐⭐ `ax13_lt_def` — construir el testigo, o refutar la desigualdad

    `∀n∀m. (n < m ⇔ ∃k. n + σk = m)`. La dirección `⇐` es el argumento de Harrop. La `⇒`
    pide un **testigo**, y es el primer sitio donde la barra exige construir algo y no sólo
    elegir rama: `hNum` baja `t` y `u` a numerales, y si `n < m` el testigo es `m-n-1`,
    con `numeralI_add` dando la ecuación. Si no, `numeralI_not_lt` refuta la hipótesis y la
    consistencia cierra. -/
theorem slash_ax13 {Γ : List Formula} (L : String → Nat → Bool)
    (hs : L succ_sym 1 = true) (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (hlift : Γ.map (liftFormula 0) = Γ)
    (hcon : ¬ (Γ ⊢ᵢ Formula.bottom))
    (hNum : ∀ t : Term, Grounded L t →
      ∃ n : Nat, Γ ⊢ᵢ (Formula.eq t (numeralM n))) :
    Slash (Γ) (Grounded L) ax13_lt_def := by
  have hax : Γ ⊢ᵢ ax13_lt_def := hΓ ax13_lt_def (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))
  simp only [ax13_lt_def, forall_2, iff, lt] at hax ⊢
  refine (slash_forall _ _ _).mpr ⟨hax, fun t hDt => ?_⟩
  have h1 := specI hax t
  simp (config := { decide := true }) only [substFormula, substTerms, substTerm,
    ite_true, ite_false, Nat.reduceAdd, grounded_liftTerm L hDt] at h1 ⊢
  refine (slash_forall _ _ _).mpr ⟨h1, fun u hDu => ?_⟩
  have h2 := specI h1 u
  simp (config := { decide := true }) only [substFormula, substTerms, substTerm,
    ite_true, ite_false, Nat.reduceAdd, add, succ,
    grounded_substTerm L hDt, grounded_liftTerm L hDu] at h2 ⊢
  refine (slash_and _ _ _ _).mpr ⟨?_, ?_⟩
  · refine (slash_impl _ _ _ _).mpr ⟨Derivesᵢ.elim_and_l _ _ _ h2, fun hA => ?_⟩
    have hlt : Γ ⊢ᵢ Formula.atom lt_sym [t, u] := (slash_atom _ _ _ _).mp hA
    obtain ⟨n, hn⟩ := hNum t hDt
    obtain ⟨m, hm⟩ := hNum u hDu
    by_cases hnm : n < m
    · refine (slash_ex _ _ _).mpr ⟨numeralM (m - n - 1), grounded_numeralM L hs _, ?_⟩
      have hadd : Γ ⊢ᵢ Formula.eq
          (add (numeralM n) (numeralM (m - n - 1 + 1))) (numeralM m) := by
        have h := (numeralI_add hΓ n (m - n - 1 + 1))
        rw [show n + (m - n - 1 + 1) = m from by omega] at h
        exact h
      simp (config := { decide := true }) only [substFormula, substTerms, substTerm,
        ite_true, ite_false, grounded_substTerm L hDt, grounded_substTerm L hDu]
      exact (slash_eq _ _ _ _).mpr
        (eqI_trans (eqI_trans
          (eqI_congr_fun2_l add_sym (succ (numeralM (m - n - 1))) hn) hadd) (eqI_symm hm))
    · refine absurd ?_ hcon
      exact Derivesᵢ.elim_impl _ _ _ (numeralI_not_lt hΓ hlift (by omega))
        (eqI_rw_atom2_r lt_sym (numeralM n) hm (eqI_rw_atom2_l lt_sym u hn hlt))
  · refine (slash_impl _ _ _ _).mpr ⟨Derivesᵢ.elim_and_r _ _ _ h2, fun hB => ?_⟩
    exact (slash_atom _ _ _ _).mpr
      (Derivesᵢ.elim_impl _ _ _ (Derivesᵢ.elim_and_r _ _ _ h2)
        (slash_derives _ _ _ hB))

/-! ## 11 · `ax14_sqrt_le` — la desigualdad NO estricta

    `∀x. √x·√x ≤ x`, y **`le a b` es `a < b ∨ a = b`**: por eso no es de Harrop, aunque a
    simple vista parezca atómico. Con las tres piezas numéricas ya en la mano
    —`numeralI_lt`, `numeralI_not_lt` y `numeralI_ne`— la tricotomía del meta decide, y el
    caso imposible lo cierra la consistencia contra las DOS ramas del axioma. -/
theorem slash_ax14 {Γ : List Formula} (L : String → Nat → Bool)
    (hsu : L succ_sym 1 = true) (hsq : L sqrt_sym 1 = true) (hm : L mul_sym 2 = true)
    (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (hax0 : Γ ⊢ᵢ ax14_sqrt_le)
    (hlift : Γ.map (liftFormula 0) = Γ)
    (hcon : ¬ (Γ ⊢ᵢ Formula.bottom))
    (hNum : ∀ t : Term, Grounded L t →
      ∃ n : Nat, Γ ⊢ᵢ (Formula.eq t (numeralM n))) :
    Slash Γ (Grounded L) ax14_sqrt_le := by
  have hax : Γ ⊢ᵢ ax14_sqrt_le := hax0
  simp only [ax14_sqrt_le, forall_, le, sq, lt] at hax ⊢
  refine (slash_forall _ _ _).mpr ⟨hax, fun t hDt => ?_⟩
  have h1 := specI hax t
  simp (config := { decide := true }) only [substFormula, substTerms, substTerm,
    ite_true, ite_false, mul, sqrt] at h1 ⊢
  have hDs : Grounded L (mul (sqrt t) (sqrt t)) :=
    grounded_func2 L hm (grounded_func1 L hsq hDt) (grounded_func1 L hsq hDt)
  obtain ⟨p, hp⟩ := hNum (mul (sqrt t) (sqrt t)) hDs
  obtain ⟨q, hq⟩ := hNum t hDt
  rcases Nat.lt_trichotomy p q with hlt | heq | hgt
  · refine (slash_or _ _ _ _).mpr (Or.inl ((slash_atom _ _ _ _).mpr ?_))
    exact eqI_rw_atom2_r lt_sym _ (eqI_symm hq)
      (eqI_rw_atom2_l lt_sym (numeralM q) (eqI_symm hp) (numeralI_lt hΓ hlt))
  · subst heq
    exact (slash_or _ _ _ _).mpr
      (Or.inr ((slash_eq _ _ _ _).mpr (eqI_trans hp (eqI_symm hq))))
  · refine absurd ?_ hcon
    refine Derivesᵢ.elim_or _ (Formula.atom lt_sym [mul (sqrt t) (sqrt t), t])
      (Formula.eq (mul (sqrt t) (sqrt t)) t) Formula.bottom h1 ?_ ?_
    · refine Derivesᵢ.elim_impl _ _ _
        (Derivesᵢ.weakening _ _ _ (numeralI_not_lt hΓ hlift (Nat.le_of_lt hgt))
          (fun _ hz => List.Mem.tail _ hz)) ?_
      exact eqI_rw_atom2_r lt_sym (numeralM p)
        (Derivesᵢ.weakening _ _ _ hq (fun _ hz => List.Mem.tail _ hz))
        (eqI_rw_atom2_l lt_sym t
          (Derivesᵢ.weakening _ _ _ hp (fun _ hz => List.Mem.tail _ hz))
          (Derivesᵢ.hyp _ _ (List.Mem.head _)))
    · refine Derivesᵢ.elim_impl _ _ _
        (Derivesᵢ.weakening _ _ _ (numeralI_ne hΓ (a := p) (b := q) (by omega))
          (fun _ hz => List.Mem.tail _ hz)) ?_
      exact eqI_trans
        (eqI_symm (Derivesᵢ.weakening _ _ _ hp (fun _ hz => List.Mem.tail _ hz)))
        (eqI_trans (Derivesᵢ.hyp _ _ (List.Mem.head _))
          (Derivesᵢ.weakening _ _ _ hq (fun _ hz => List.Mem.tail _ hz)))

/-! ## 12 · ⛔ `ax_L3_in_concat` — el que NO tiene ruta numérica

    `∀x∀l∀m. x ∈ l##m ⇔ (x ∈ l ∨ x ∈ m)`. La dirección `⇐` es Harrop. La `⇒` pide elegir
    rama, **y las dos ramas son `∈`**: no hay nada que refutar bajando a numerales, como sí
    lo había en `ax_L2_in_cons`, donde una de las ramas era una igualdad.

    ⚠️ Por eso aquí aparece una hipótesis NUEVA, `hIn`, y hay que decir qué es: la
    **decidibilidad de `∈` sobre términos anclados**, el análogo para el otro predicado de lo
    que `hNum` (+ `numeralI_ne` + consistencia) da para la igualdad.

    ⛔ **`hIn` NO está demostrada, y no se sigue de Q⁺⁺**: haría falta que la teoría probara
    que todo término es `[]` o un `::`, y eso es inducción sobre listas — un esquema que
    `coreAxioms` no tiene. Queda, como `hNum`, en el enunciado y a la vista. -/
theorem slash_axL3 {insts : List Formula}
    (hIn : ∀ x l : Term, Grounded LQpp x → Grounded LQpp l →
      Or (ctx insts ⊢ᵢ Formula.atom in_sym [x, l])
         (ctx insts ⊢ᵢ Formula.impl (Formula.atom in_sym [x, l]) Formula.bottom)) :
    Slash (ctx insts) (Grounded LQpp) ax_L3_in_concat := by
  have hax : ctx insts ⊢ᵢ ax_L3_in_concat := ax' (by simp [coreAxioms])
  simp only [ax_L3_in_concat, forall_3, iff, lor, In, concat] at hax ⊢
  refine (slash_forall _ _ _).mpr ⟨hax, fun x hDx => ?_⟩
  have h1 := specI hax x
  simp (config := { decide := true }) only [substFormula, substTerms, substTerm,
    ite_true, ite_false, grounded_liftTerm LQpp hDx] at h1 ⊢
  refine (slash_forall _ _ _).mpr ⟨h1, fun l hDl => ?_⟩
  have h2 := specI h1 l
  simp (config := { decide := true }) only [substFormula, substTerms, substTerm,
    ite_true, ite_false, Nat.reduceAdd, grounded_liftTerm LQpp hDl,
    grounded_substTerm LQpp hDx] at h2 ⊢
  refine (slash_forall _ _ _).mpr ⟨h2, fun m hDm => ?_⟩
  have h3 := specI h2 m
  simp (config := { decide := true }) only [substFormula, substTerms, substTerm,
    ite_true, ite_false, grounded_substTerm LQpp hDx,
    grounded_substTerm LQpp hDl] at h3 ⊢
  refine (slash_and _ _ _ _).mpr ⟨?_, ?_⟩
  · refine (slash_impl _ _ _ _).mpr ⟨Derivesᵢ.elim_and_l _ _ _ h3, fun hA => ?_⟩
    have hdis : ctx insts ⊢ᵢ
        Formula.or (Formula.atom in_sym [x, l]) (Formula.atom in_sym [x, m]) :=
      Derivesᵢ.elim_impl _ _ _ (Derivesᵢ.elim_and_l _ _ _ h3)
        ((slash_atom _ _ _ _).mp hA)
    rcases hIn x l hDx hDl with hyes | hno
    · exact (slash_or _ _ _ _).mpr (Or.inl ((slash_atom _ _ _ _).mpr hyes))
    · refine (slash_or _ _ _ _).mpr (Or.inr ((slash_atom _ _ _ _).mpr ?_))
      refine Derivesᵢ.elim_or _ (Formula.atom in_sym [x, l]) (Formula.atom in_sym [x, m])
        (Formula.atom in_sym [x, m]) hdis ?_ (Derivesᵢ.hyp _ _ (List.Mem.head _))
      refine Derivesᵢ.bot_elim _ _ ?_
      exact Derivesᵢ.elim_impl _ _ _
        (Derivesᵢ.weakening _ _ _ hno (fun _ hz => List.Mem.tail _ hz))
        (Derivesᵢ.hyp _ _ (List.Mem.head _))
  · refine (slash_impl _ _ _ _).mpr ⟨Derivesᵢ.elim_and_r _ _ _ h3, fun hB => ?_⟩
    exact (slash_atom _ _ _ _).mpr
      (Derivesᵢ.elim_impl _ _ _ (Derivesᵢ.elim_and_r _ _ _ h3)
        (slash_derives _ _ _ hB))

/-! ## 13 · 🏁🏁 LOS 34, y con ellos la DP de HA

    Aquí se cierra la etapa 3. De los 34 axiomas de `coreAxioms`, **28 caen por Harrop** y
    **los 6 restantes están demostrados uno a uno** arriba. Lo que queda fuera va como
    hipótesis, **todas dichas y ninguna escondida**:

    | hipótesis | qué es | ¿se puede demostrar aquí? |
    |---|---|---|
    | `hcon` | la consistencia de la teoría | ⛔ no (Gödel) |
    | `hlift` | el contexto es invariante bajo levantamiento | ✅ si las instancias son cerradas |
    | `hNum` | todo término anclado es demostrablemente un numeral | ⏳ falta evaluar 8 de los 13 símbolos |
    | `hIn` | `∈` es decidible sobre términos anclados | ⛔ pide inducción sobre listas |
    | `hInd` | el esquema de inducción está barrado | ⏳ |
-/

/-- ⭐⭐ **Los 34 axiomas de `coreAxioms`, barrados.** -/
theorem slash_coreAxioms {insts : List Formula}
    (hlift : (ctx insts).map (liftFormula 0) = ctx insts)
    (hcon : ¬ (ctx insts ⊢ᵢ Formula.bottom))
    (hNum : ∀ t : Term, Grounded LQpp t →
      ∃ n : Nat, ctx insts ⊢ᵢ (Formula.eq t (numeralM n)))
    (hIn : ∀ x l : Term, Grounded LQpp x → Grounded LQpp l →
      Or (ctx insts ⊢ᵢ Formula.atom in_sym [x, l])
         (ctx insts ⊢ᵢ Formula.impl (Formula.atom in_sym [x, l]) Formula.bottom)) :
    ∀ g, List.Mem g coreAxioms → Slash (ctx insts) (Grounded LQpp) g := by
  intro g hg
  simp only [coreAxioms] at hg
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax2_peano_succ_neq_zero rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax3_peano_succ_inj rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax4_add_zero rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax5_add_succ rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax6_add_comm rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax7_add_assoc rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax8_mul_zero rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax9_mul_succ rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax10_mul_comm rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax11_mul_assoc rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax12_mul_distrib rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_ax13 LQpp (by decide) arith_ctx hlift hcon hNum
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_ax14 LQpp (by decide) (by decide) (by decide) arith_ctx
      (ax' (by simp [coreAxioms])) hlift hcon hNum
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax15_lt_succ_sqrt rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax16_mod2_succ rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax17_div_mod_eq rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax18_lt_irrefl rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_ax19 LQpp arith_ctx hNum
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_ax21 LQpp (by decide) (ax' (by simp [coreAxioms])) arith_ctx hcon hNum
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax24_mod2_of_even rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax25_pred_zero rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax26_pred_succ rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax_L0_cons_def rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax_L1_in_nil rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_axL2 hNum
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax_C1_concat_nil rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax_C2_concat_cons rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax_C3_concat_assoc rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_axL3 hIn
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax29_sub_witness rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax_pow_zero rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax_pow_succ rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax_prodp_nil rfl (ax' (by simp [coreAxioms]))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax_prodp_cons rfl (ax' (by simp [coreAxioms]))
  cases hg

/-- 🏁🏁🏁 **LA PROPIEDAD DE DISYUNCIÓN PARA HA**, con `coreAxioms` YA descargado.
    Sólo queda el esquema de inducción, más las cuatro hipótesis de la tabla. -/
theorem haDisjunctionProperty_core {insts : List Formula}
    (hlift : (ctx insts).map (liftFormula 0) = ctx insts)
    (hcon : ¬ (ctx insts ⊢ᵢ Formula.bottom))
    (hNum : ∀ t : Term, Grounded LQpp t →
      ∃ n : Nat, ctx insts ⊢ᵢ (Formula.eq t (numeralM n)))
    (hIn : ∀ x l : Term, Grounded LQpp x → Grounded LQpp l →
      Or (ctx insts ⊢ᵢ Formula.atom in_sym [x, l])
         (ctx insts ⊢ᵢ Formula.impl (Formula.atom in_sym [x, l]) Formula.bottom))
    (hInd : ∀ g, List.Mem g (insts.map inductionFormula) →
      Slash (ctx insts) (Grounded LQpp) (collapseF LQpp (substF zeroS g)))
    {A B : Formula}
    (hAB : collapseF LQpp (substF zeroS (Formula.or A B)) = Formula.or A B)
    (h : ctx insts ⊢ᵢ Formula.or A B) :
    Or (ctx insts ⊢ᵢ A) (ctx insts ⊢ᵢ B) := by
  refine haDisjunctionProperty insts hcon (fun g hcore _ => ?_) hInd hAB h
  rw [coreAxioms_sentence g hcore]
  exact slash_coreAxioms hlift hcon hNum hIn g hcore

/-! ## 14 · 🏁 `hInd` y `hlift` — el esquema de inducción, y el contexto cerrado

    Las dos hipótesis baratas de `haDisjunctionProperty_core`, y las dos se reducen a una
    condición **por instancia** que para una instancia concreta se comprueba con `rfl`.

    ⭐ **El atajo de `hInd`, medido**: `inductionFormula φ` es
    `φ[0] ⇒ ((∀(φ ⇒ φ[σ])) ⇒ ∀φ)`. En Harrop el antecedente de `⇒` **da igual** y el
    consecuente final es `∀φ`, luego

    > `isHarrop (inductionFormula φ) = isHarrop φ`, y es `rfl`.

    ⇒ **Si la instancia es de Harrop, el esquema entero lo es** y cae con
    `slash_of_isHarrop`, sólo con la consistencia. No hace falta nada nuevo.

    ⛔ **Y lo que el atajo NO da, que conviene decirlo**: vale para instancias de Harrop.
    Una instancia con `∨` o `∃` —que es lo interesante de la inducción en HA— **no** es de
    Harrop, y ahí no hay atajo ninguno. Lo que cae barato es el esquema para las instancias
    que hoy existen, no el esquema en general. -/

/-- ⭐ El esquema hereda Harrop de su instancia. Por iota, sin prueba. -/
theorem isHarrop_inductionFormula (φ : Formula) :
    isHarrop (inductionFormula φ) = isHarrop φ := rfl

/-- 🏁 **`hInd` para instancias de Harrop.** -/
theorem slash_inductions {insts : List Formula}
    (hcon : ¬ (ctx insts ⊢ᵢ Formula.bottom))
    (hH : ∀ φ, List.Mem φ insts → isHarrop φ = true)
    (hs : ∀ φ, List.Mem φ insts →
      collapseF LQpp (substF zeroS (inductionFormula φ)) = inductionFormula φ) :
    ∀ g, List.Mem g (insts.map inductionFormula) →
      Slash (ctx insts) (Grounded LQpp) (collapseF LQpp (substF zeroS g)) := by
  intro g hg
  obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hg
  rw [hs φ hφ]
  exact slash_of_isHarrop _ _ hcon _
    (by rw [isHarrop_inductionFormula]; exact hH φ hφ) (ind hφ)

/-- 🏁 **`hlift`**: si cada instancia da un esquema cerrado, el contexto entero lo es.
    `axioms_lift` pone los 34 axiomas; esto pone las instancias. -/
theorem inductions_lift : ∀ (insts : List Formula),
    (∀ φ, List.Mem φ insts → liftFormula 0 (inductionFormula φ) = inductionFormula φ) →
    (insts.map inductionFormula).map (liftFormula 0) = insts.map inductionFormula := by
  intro insts
  induction insts with
  | nil => intro _; rfl
  | cons a l ih =>
      intro h
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨h a (List.Mem.head _), ih (fun φ hφ => h φ (List.Mem.tail _ hφ))⟩

/-- 🏁🏁🏁 **LA DP DE HA con `hInd` y `hlift` YA DESCARGADAS.** Quedan tres hipótesis, y
    las tres son de fondo: `hcon` (Gödel), `hNum` y `hIn`. -/
theorem haDisjunctionProperty_harrop (insts : List Formula)
    (hcon : ¬ (ctx insts ⊢ᵢ Formula.bottom))
    (hH : ∀ φ, List.Mem φ insts → isHarrop φ = true)
    (hs : ∀ φ, List.Mem φ insts →
      collapseF LQpp (substF zeroS (inductionFormula φ)) = inductionFormula φ)
    (hL : ∀ φ, List.Mem φ insts →
      liftFormula 0 (inductionFormula φ) = inductionFormula φ)
    (hNum : ∀ t : Term, Grounded LQpp t →
      ∃ n : Nat, ctx insts ⊢ᵢ (Formula.eq t (numeralM n)))
    (hIn : ∀ x l : Term, Grounded LQpp x → Grounded LQpp l →
      Or (ctx insts ⊢ᵢ Formula.atom in_sym [x, l])
         (ctx insts ⊢ᵢ Formula.impl (Formula.atom in_sym [x, l]) Formula.bottom))
    {A B : Formula}
    (hAB : collapseF LQpp (substF zeroS (Formula.or A B)) = Formula.or A B)
    (h : ctx insts ⊢ᵢ Formula.or A B) :
    Or (ctx insts ⊢ᵢ A) (ctx insts ⊢ᵢ B) :=
  haDisjunctionProperty_core (ctx_lift (inductions_lift insts hL)) hcon hNum hIn
    (slash_inductions hcon hH hs) hAB h

/-! ### ⭐ Que las hipótesis por instancia NO sean vacías, medido

    Un teorema con hipótesis insatisfacibles es cierto y hueco. Con la instancia que el
    proyecto usa de verdad —`phiZeroAdd`, o sea `0 + x = x`— **las tres salen por `rfl`**:
    es de Harrop porque es una ecuación, y su esquema es una sentencia del lenguaje. -/

theorem phiZeroAdd_harrop : isHarrop phiZeroAdd = true := rfl

theorem phiZeroAdd_lift :
    liftFormula 0 (inductionFormula phiZeroAdd) = inductionFormula phiZeroAdd := rfl

theorem phiZeroAdd_sentence :
    collapseF LQpp (substF zeroS (inductionFormula phiZeroAdd))
      = inductionFormula phiZeroAdd := rfl

/-- 🏁🏁🏁 **LA DP DE HA CON UNA INSTANCIA DE INDUCCIÓN REAL.** Todo lo mecánico está
    descargado; quedan exactamente las tres de fondo: `hcon` (Gödel), `hNum` y `hIn`. -/
theorem haDisjunctionProperty_zeroAdd
    (hcon : ¬ (ctx [phiZeroAdd] ⊢ᵢ Formula.bottom))
    (hNum : ∀ t : Term, Grounded LQpp t →
      ∃ n : Nat, ctx [phiZeroAdd] ⊢ᵢ (Formula.eq t (numeralM n)))
    (hIn : ∀ x l : Term, Grounded LQpp x → Grounded LQpp l →
      Or (ctx [phiZeroAdd] ⊢ᵢ Formula.atom in_sym [x, l])
         (ctx [phiZeroAdd] ⊢ᵢ Formula.impl (Formula.atom in_sym [x, l]) Formula.bottom))
    {A B : Formula}
    (hAB : collapseF LQpp (substF zeroS (Formula.or A B)) = Formula.or A B)
    (h : ctx [phiZeroAdd] ⊢ᵢ Formula.or A B) :
    Or (ctx [phiZeroAdd] ⊢ᵢ A) (ctx [phiZeroAdd] ⊢ᵢ B) := by
  refine haDisjunctionProperty_harrop [phiZeroAdd] hcon ?_ ?_ ?_ hNum hIn hAB h
  · intro φ hφ; cases hφ with
    | head => exact phiZeroAdd_harrop
    | tail _ hx => cases hx
  · intro φ hφ; cases hφ with
    | head => exact phiZeroAdd_sentence
    | tail _ hx => cases hx
  · intro φ hφ; cases hφ with
    | head => exact phiZeroAdd_lift
    | tail _ hx => cases hx

end PeanoRF.HA
