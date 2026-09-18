/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.Calculus.Collapse
import PeanoRF.Calculus.Subst
import PeanoRF.HA.Numerals

/-! # El DOMINIO de la barra — `ClosedQTerm` y la signatura de Q⁺⁺

  La barra de H3ter va a llevar un parámetro de dominio, `Slash T D`: sus cláusulas de `∀` y
  `∃` cuantifican sobre los términos de `D`, no sobre todos. Sin eso, `ax19_lt_trichotomy`
  no se puede barrar, porque su `∀` recorre términos de los que HA no sabe nada.

  Este módulo fija `D = ClosedQTerm` y demuestra **las dos propiedades de clausura que L2
  pedirá**, medidas antes de escribir nada (`sondeos/collapse_parallel_probe.lean`):

  | lo que pide L2 | aquí |
  |---|---|
  | `intro_forall` | `collapse_fix_closed` — el colapso **fija** el dominio |
  | `elim_forall`  | ⭐⭐ `closed_collapse_subst` — el colapso de `substT ρ t` **cae** en el dominio, para `t` ARBITRARIO |

  ## ⛔ Por qué la signatura lleva la ARIDAD

  `collapseT` tomaba `L : String → Bool`, sólo el nombre del símbolo. **No basta**, y está
  medido:

  ```lean
  contraejemplo_aridad : ¬ ClosedQTerm (Term.func add_sym [zero])
  ```

  `+` aplicado a UN argumento es un término legítimo de la sintaxis, es cerrado y lleva sólo
  símbolos de Q⁺⁺ — pero los constructores de `ClosedQTerm` fijan también la aridad, y con
  razón: **Q⁺⁺ no tiene ningún axioma sobre él**, luego tampoco es demostrablemente igual a
  ningún numeral, que es lo único que la etapa 3 le pide al dominio. Si el colapso lo dejara
  pasar, el dominio no se podría cerrar.

  ## ⚠️ Aquí no se pueden escribir `∧` ni `∨`

  `open FOL` las tiene tomadas por la conjunción y la disyunción de `FormulaG`. Escribir
  `(s = zero_sym ∧ n = 0)` da `unexpected token '='`, que no se parece nada a su causa — la
  misma familia que el `σ` de `peanolib`. Leerlas está bien; escribirlas, no.
-/

namespace PeanoRF.HA

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open PeanoRF.Calculus

set_option autoImplicit false

/-! ## La signatura de Q⁺⁺, con aridad -/

/-- Los cinco símbolos de Q⁺⁺ **con su aridad**. Todo lo demás colapsa a `zero`. -/
def LQ (s : String) (n : Nat) : Bool :=
  (s == zero_sym && n == 0) || (s == succ_sym && n == 1) ||
  ((s == add_sym || s == mul_sym || s == pow_sym) && n == 2)

/-! ## 1 · El colapso FIJA el dominio — lo que pide `intro_forall` -/

theorem collapse_fix_closed : ∀ {u : Term}, ClosedQTerm u → collapseT LQ u = u := by
  intro u h
  induction h with
  | zero =>
      have hL : LQ zero_sym 0 = true := by decide
      simp only [zero, collapseT, List.length_nil, if_pos hL, collapseTs]
  | succ a _ ih =>
      have hL : LQ succ_sym 1 = true := by decide
      simp only [succ, collapseT, List.length_cons, List.length_nil, if_pos hL,
        collapseTs, ih]
  | add a b _ _ iha ihb =>
      have hL : LQ add_sym 2 = true := by decide
      simp only [add, collapseT, List.length_cons, List.length_nil, if_pos hL,
        collapseTs, iha, ihb]
  | mul a b _ _ iha ihb =>
      have hL : LQ mul_sym 2 = true := by decide
      simp only [mul, collapseT, List.length_cons, List.length_nil, if_pos hL,
        collapseTs, iha, ihb]
  | pow a b _ _ iha ihb =>
      have hL : LQ pow_sym 2 = true := by decide
      simp only [pow, collapseT, List.length_cons, List.length_nil, if_pos hL,
        collapseTs, iha, ihb]

/-- ⛔ **El contraejemplo que obligó a meter la aridad en la signatura.** Se deja en
    producción, no en el cuaderno de sondeos, porque es lo que justifica el diseño. -/
theorem not_closed_add_unary : ¬ ClosedQTerm (Term.func add_sym [zero]) := by
  intro h
  have heq := collapse_fix_closed h
  have hL : ¬ (LQ add_sym ([zero] : List Term).length = true) := by decide
  rw [collapseT, if_neg hL] at heq
  simp only [zero] at heq
  injection heq with h1 _
  exact absurd h1 (by decide)

/-! ## 2 · ⭐⭐ El colapso de una sustitución CAE en el dominio — lo que pide `elim_forall` -/

/-- Un símbolo admitido por `LQ`, con sus argumentos en el dominio, da un `ClosedQTerm`.
    Es donde la aridad hace todo el trabajo. -/
theorem closed_of_LQ : ∀ (s : String) (args : List Term),
    LQ s args.length = true → (∀ t ∈ args, ClosedQTerm t) →
    ClosedQTerm (Term.func s args) := by
  intro s args hL hargs
  match args with
  | [] =>
      simp only [List.length_nil, LQ, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hL
      rcases hL with (⟨h1, _⟩ | ⟨_, h2⟩) | ⟨_, h2⟩
      · subst h1; exact ClosedQTerm.zero
      · exact absurd h2 (by decide)
      · exact absurd h2 (by decide)
  | [a] =>
      simp only [List.length_cons, List.length_nil, LQ, Bool.or_eq_true,
        Bool.and_eq_true, beq_iff_eq] at hL
      rcases hL with (⟨_, h2⟩ | ⟨h1, _⟩) | ⟨_, h2⟩
      · exact absurd h2 (by decide)
      · subst h1; exact ClosedQTerm.succ a (hargs a (List.Mem.head _))
      · exact absurd h2 (by decide)
  | [a, b] =>
      simp only [List.length_cons, List.length_nil, LQ, Bool.or_eq_true,
        Bool.and_eq_true, beq_iff_eq] at hL
      have ha := hargs a (List.Mem.head _)
      have hb := hargs b (List.Mem.tail _ (List.Mem.head _))
      rcases hL with (⟨_, h2⟩ | ⟨_, h2⟩) | ⟨h1, _⟩
      · exact absurd h2 (by decide)
      · exact absurd h2 (by decide)
      · rcases h1 with (h1 | h1) | h1
        · subst h1; exact ClosedQTerm.add a b ha hb
        · subst h1; exact ClosedQTerm.mul a b ha hb
        · subst h1; exact ClosedQTerm.pow a b ha hb
  | a :: b :: c :: rest =>
      exfalso
      simp only [List.length_cons, LQ, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hL
      rcases hL with (⟨_, h2⟩ | ⟨_, h2⟩) | ⟨_, h2⟩ <;> omega

mutual
/-- ⭐⭐ **La clausura que cierra `elim_forall`.** Con `ρ` valuada en el dominio, el colapso
    de `substT ρ t` está en el dominio **para un `t` arbitrario** — símbolos ajenos y
    aridades erróneas incluidos. Es lo que hace innecesario un cálculo indexado por el
    lenguaje. -/
theorem closed_collapse_subst (ρ : Subst) (hρ : ∀ n, ClosedQTerm (ρ n)) :
    ∀ t : Term, ClosedQTerm (collapseT LQ (substT ρ t)) := by
  intro t
  cases t with
  | var n =>
      show ClosedQTerm (collapseT LQ (ρ n))
      rw [collapse_fix_closed (hρ n)]
      exact hρ n
  | func s ts =>
      have ih := closed_collapse_substs ρ hρ ts
      show ClosedQTerm (collapseT LQ (Term.func s (substTs ρ ts)))
      rw [collapseT]
      by_cases hL : LQ s (substTs ρ ts).length = true
      · rw [if_pos hL]
        refine closed_of_LQ s _ ?_ ih
        rw [collapseTs_length]
        exact hL
      · rw [if_neg hL]
        exact ClosedQTerm.zero

theorem closed_collapse_substs (ρ : Subst) (hρ : ∀ n, ClosedQTerm (ρ n)) :
    ∀ (ts : List Term), ∀ u ∈ collapseTs LQ (substTs ρ ts), ClosedQTerm u := by
  intro ts
  cases ts with
  | nil => intro u hu; cases hu
  | cons t ts0 =>
      intro u hu
      show ClosedQTerm u
      rcases hu with _ | ⟨_, hu0⟩
      · exact closed_collapse_subst ρ hρ t
      · exact closed_collapse_substs ρ hρ ts0 u hu0
end

/-- El dominio **no es vacío**: la sustitución constante `zero` lo valúa. Es la que instancia
    L2 en el nivel de arriba, donde la fórmula es una sentencia. -/
theorem closed_zeroS : ∀ n : Nat, ClosedQTerm ((fun _ => zero : Subst) n) :=
  fun _ => ClosedQTerm.zero

end PeanoRF.HA
