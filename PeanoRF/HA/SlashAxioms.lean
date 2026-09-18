/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.HA.Domain

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

set_option autoImplicit false

/-! ## 1 · Debilitamiento desde `ctx []` -/

/-- Lo demostrado sin instancias de inducción vale con ellas. Es lo que deja usar
    `numeralI_add` y compañía, que están enunciados sobre `ctx []`. -/
theorem ctx_weaken {insts : List Formula} {f : Formula} (h : ctx [] ⊢ᵢ f) :
    ctx insts ⊢ᵢ f := by
  refine Derivesᵢ.weakening _ _ _ h ?_
  intro x hx
  exact mem_ctx_of_mem_axioms (by simpa [ctx] using hx)

/-! ## 2 · `n < m` en el objeto, decidido en el meta

    Es la primera pieza reutilizable: la dirección `⇐` de `ax13_lt_def` convierte un testigo
    aritmético en una desigualdad, y el testigo lo da `numeralI_add`. -/

theorem numeralI_lt {insts : List Formula} {a b : Nat} (h : a < b) :
    ctx insts ⊢ᵢ lt (numeralM a) (numeralM b) := by
  have h13 : ctx insts ⊢ᵢ ax13_lt_def := ax' (by simp [coreAxioms])
  have hi := specI (specI h13 (numeralM a)) (numeralM b)
  have hback : ctx insts ⊢ᵢ
      Formula.impl (Formula.ex (Formula.eq (add (numeralM a) (succ (Term.var 0)))
                                           (numeralM b)))
                   (lt (numeralM a) (numeralM b)) := by
    have := Derivesᵢ.elim_and_r _ _ _ hi
    simpa [ax13_lt_def, forall_2, substFormula, substTerms, substTerm, lt, add, succ,
      iff, substTerm_numeralM, liftTerm_numeralM] using this
  refine Derivesᵢ.elim_impl _ _ _ hback ?_
  refine Derivesᵢ.intro_ex _ _ (numeralM (b - a - 1)) ?_
  have harith : a + (b - a - 1 + 1) = b := by omega
  have hadd := ctx_weaken (insts := insts) (numeralI_add a (b - a - 1 + 1))
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
theorem slash_ax19 {insts : List Formula}
    (hNum : ∀ t : Term, Grounded LQpp t →
      ∃ n : Nat, ctx insts ⊢ᵢ (Formula.eq t (numeralM n))) :
    Slash (ctx insts) (Grounded LQpp) ax19_lt_trichotomy := by
  have hax : ctx insts ⊢ᵢ ax19_lt_trichotomy := ax' (by simp [coreAxioms])
  refine (slash_forall _ _ _).mpr ⟨hax, fun t hDt => ?_⟩
  have h1 := specI hax t
  simp only [substFormula, grounded_liftTerm LQpp hDt] at h1 ⊢
  refine (slash_forall _ _ _).mpr ⟨h1, fun u hDu => ?_⟩
  simp only [substFormula, substTerms, substTerm, lt, reduceIte,
    grounded_substTerm LQpp hDt]
  obtain ⟨n, hn⟩ := hNum t hDt
  obtain ⟨m, hm⟩ := hNum u hDu
  rcases Nat.lt_trichotomy n m with hlt | heq | hgt
  · refine (slash_or _ _ _ _).mpr (Or.inl ((slash_atom _ _ _ _).mpr ?_))
    exact eqI_rw_atom2_r lt_sym t (eqI_symm hm)
      (eqI_rw_atom2_l lt_sym (numeralM m) (eqI_symm hn) (numeralI_lt hlt))
  · subst heq
    refine (slash_or _ _ _ _).mpr (Or.inr ((slash_or _ _ _ _).mpr
      (Or.inl ((slash_eq _ _ _ _).mpr ?_))))
    exact eqI_trans hn (eqI_symm hm)
  · refine (slash_or _ _ _ _).mpr (Or.inr ((slash_or _ _ _ _).mpr
      (Or.inr ((slash_atom _ _ _ _).mpr ?_))))
    exact eqI_rw_atom2_r lt_sym u (eqI_symm hn)
      (eqI_rw_atom2_l lt_sym (numeralM n) (eqI_symm hm) (numeralI_lt hgt))

/-! ## 4 · ⭐ `n ≠ m` en el objeto — la versión CONSTRUCTIVA

    ⚠️ Aguas arriba existe `numeral_ne`, pero **arrastra `Classical`** (medido el 2026-09-16),
    así que no sirve en este árbol. Ésta se construye a mano con los dos axiomas de Peano que
    Q⁺⁺ tiene: `ax2` (`σx ≠ 0`) para las bases y `ax3` (`σ` inyectiva) para el paso. -/

/-- `⊢ᵢ ¬(n̄ = m̄)` cuando `n ≠ m`. Inducción META en el primero, generalizando el segundo. -/
theorem numeralI_ne {insts : List Formula} : ∀ {a b : Nat}, a ≠ b →
    ctx insts ⊢ᵢ neg (Formula.eq (numeralM a) (numeralM b)) := by
  intro a
  induction a with
  | zero =>
      intro b hne
      match b with
      | 0 => exact absurd rfl hne
      | k + 1 =>
          have h2 : ctx insts ⊢ᵢ ax2_peano_succ_neq_zero := ax' (by simp [coreAxioms])
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
          have h2 : ctx insts ⊢ᵢ ax2_peano_succ_neq_zero := ax' (by simp [coreAxioms])
          have hi := specI h2 (numeralM j)
          simpa only [forall_, substFormula, substTerms, substTerm, reduceIte,
            neg, succ, zero, numeralM, substTerm_numeralM] using hi
      | k + 1 =>
          have h3 : ctx insts ⊢ᵢ ax3_peano_succ_inj := ax' (by simp [coreAxioms])
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

end PeanoRF.HA
