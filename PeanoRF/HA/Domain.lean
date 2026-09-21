/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.Calculus.Collapse
import PeanoRF.Calculus.Subst
import PeanoRF.Calculus.Slash
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
open ROBINSON_PlusPlus.Full (inductionFormula)

set_option autoImplicit false

/-! # ⚠️ §1–§2 SON EVIDENCIA Y ANDAMIO, NO MAQUINARIA EN PRODUCCIÓN

    **Auditado el 2026-09-21**: desde que el dominio pasó a `Grounded LQpp` (§3), toda esta
    capa de cinco símbolos **no tiene ningún uso portante**. `LQ`, `collapse_fix_closed`,
    `closed_of_LQ`, `closed_collapse_subst` y `closed_collapse_substs` sólo se usan **entre
    sí**; las menciones que aparecen en `Calculus/Slash.lean` son PROSA, no código.

    Se queda, y por dos razones distintas que conviene no confundir:

    | | por qué sigue aquí |
    |---|---|
    | ⛔ `not_closed_add_unary` | **EVIDENCIA**. Es el contraejemplo que obligó a meter la ARIDAD en la signatura del colapso (ADR-028). Vive en producción a propósito: es lo que justifica el diseño, y en el cuaderno de sondeos se perdería |
    | 🏗️ el resto | **ANDAMIO**. `hNum` —la hipótesis que falta de H3ter— dice que todo término anclado es demostrablemente igual a un numeral, y `closed_term_eq_numeral` sólo habla de estos cinco símbolos. Cuando se ataque `hNum`, esta capa es por donde se empieza |

    🔑 Y queda dicho porque **nada lo diría si no**: el control `[B]` de símbolos muertos
    de `check-doc-sync.bash` está **desactivado** (`SYMBOL_PREFIXES` vacío). Código sin uso
    y sin etiqueta se lee como código en uso, que es otra forma de dejar leer de más. -/

/-! ## La signatura de Q⁺⁺ (los cinco de los numerales), con aridad -/

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

/-! ## 3 · La signatura COMPLETA de Q⁺⁺, y el dominio sobre ella

    ⛔ **`LQ` no sirve para HA, y está medido.** `LQ` tiene los cinco símbolos de los
    numerales, pero los 34 axiomas de `coreAxioms` usan **trece**:

    ```
    0/0  []/0  σ/1  √/1  /₂/1  %₂/1  τ/1  Π_p/1  +/2  */2  ^/2  −/2  ::/2  ##/2
    ```

    (y dos predicados, `</2` y `∈/2`, que no se colapsan). Colapsar con `LQ` **mutila** casi
    todos los axiomas, así que la hipótesis `hT` sobre `LQ` sería insatisfacible para HA y el
    teorema, cierto y vacío. Por eso el dominio de trabajo va sobre `LQpp`.

    ⭐ Y el dominio ya no es un inductivo por lenguaje sino **sus dos clausuras**
    (`Calculus.Grounded`), que es todo lo que L2 mira. Así vale para cualquier signatura sin
    volver a demostrar nada. -/

/-- La signatura COMPLETA de Q⁺⁺, con aridades. Medida sobre `coreAxioms`, no supuesta. -/
def LQpp (s : String) (n : Nat) : Bool :=
  (s == zero_sym && n == 0) || (s == nil_sym && n == 0) ||
  ((s == succ_sym || s == sqrt_sym || s == div2_sym || s == mod2_sym
     || s == pred_sym || s == prodp_sym) && n == 1) ||
  ((s == add_sym || s == mul_sym || s == pow_sym || s == sub_sym
     || s == cons_sym || s == concat_sym) && n == 2)

/-- La sustitución que cierra: todo índice a `zero`. Es la que instancia el nivel de arriba,
    donde la fórmula es una **sentencia** y por tanto ninguna variable llega a usarse.

    ⚠️ **`g ∈ T` no se puede escribir en este módulo**: en este ámbito `∈` está sobrecargada
    —es el predicado `In` de Q⁺⁺, uno de los dos que se miden arriba— y elabora el lado
    derecho como un TIPO (`type expected, got (T : List Formula)`). Se escribe
    `List.Mem g T`, que es a lo que reduce. La tercera de la familia, tras el `σ` de
    `peanolib` y el `∧`/`∨` de `FOL`. -/
def zeroS : Subst := fun _ => zero

theorem zeroS_grounded : ∀ n, Grounded LQpp (zeroS n) := fun _ => grounded_zero LQpp

/-- Todo `ClosedQTerm` está anclado en la signatura completa. Es el puente con
    `closed_term_eq_numeral`, que sólo habla de los cinco símbolos de los numerales.

    🏗️ **ANDAMIO, sin uso portante hoy** (auditado el 2026-09-21): se escribió para
    `hNum` y `hNum` todavía no está. Es la dirección fácil del puente; la difícil —que todo
    `Grounded LQpp` sea demostrablemente un numeral— es la que falta, y pide evaluar los
    ocho símbolos que no son de los numerales. -/
theorem closed_grounded : ∀ {t : Term}, ClosedQTerm t → Grounded LQpp t := by
  intro t h
  induction h with
  | zero => exact grounded_zero LQpp
  | succ a _ ih =>
      exact ⟨by simp only [succ, collapseT, List.length_cons, List.length_nil,
              if_pos (by decide : LQpp succ_sym 1 = true), collapseTs, ih.1],
             fun ρ => by simp only [succ, substT, substTs, ih.2 ρ]⟩
  | add a b _ _ iha ihb =>
      exact ⟨by simp only [add, collapseT, List.length_cons, List.length_nil,
              if_pos (by decide : LQpp add_sym 2 = true), collapseTs, iha.1, ihb.1],
             fun ρ => by simp only [add, substT, substTs, iha.2 ρ, ihb.2 ρ]⟩
  | mul a b _ _ iha ihb =>
      exact ⟨by simp only [mul, collapseT, List.length_cons, List.length_nil,
              if_pos (by decide : LQpp mul_sym 2 = true), collapseTs, iha.1, ihb.1],
             fun ρ => by simp only [mul, substT, substTs, iha.2 ρ, ihb.2 ρ]⟩
  | pow a b _ _ iha ihb =>
      exact ⟨by simp only [pow, collapseT, List.length_cons, List.length_nil,
              if_pos (by decide : LQpp pow_sym 2 = true), collapseTs, iha.1, ihb.1],
             fun ρ => by simp only [pow, substT, substTs, iha.2 ρ, ihb.2 ρ]⟩

/-! ## 4 · 🏁 La propiedad de disyunción para una teoría de Q⁺⁺ -/

/-- 🏁 **La DP para cualquier teoría de Q⁺⁺ cuyos axiomas estén barrados.**

    `hAB` dice, en una sola ecuación, que `A ∨ B` es una **sentencia del lenguaje**: cerrada
    (la sustitución no la toca) y sin símbolos ajenos (el colapso no la toca). ⛔ Sin ella el
    enunciado es FALSO — `sondeos/junk_probe.lean`. -/
theorem qDisjunctionProperty (T : List Formula)
    (hT : ∀ g, List.Mem g T → Slash T (Grounded LQpp) (collapseF LQpp (substF zeroS g)))
    {A B : Formula}
    (hAB : collapseF LQpp (substF zeroS (Formula.or A B)) = Formula.or A B)
    (h : T ⊢ᵢ Formula.or A B) :
    (T ⊢ᵢ A) ∨ (T ⊢ᵢ B) :=
  disjunction_property_of_slashed T (Grounded LQpp) LQpp
    (fun _ hu => grounded_fix LQpp hu) (grounded_collapse_subst LQpp)
    zeroS zeroS_grounded hT hAB h

/-- 🏁 **La propiedad de existencia**, con el testigo **anclado**: cerrado y del lenguaje. -/
theorem qExistenceProperty (T : List Formula)
    (hT : ∀ g, List.Mem g T → Slash T (Grounded LQpp) (collapseF LQpp (substF zeroS g)))
    {A : Formula}
    (hA : collapseF LQpp (substF zeroS (Formula.ex A)) = Formula.ex A)
    (h : T ⊢ᵢ Formula.ex A) :
    ∃ t : Term, And (Grounded LQpp t) (T ⊢ᵢ substFormula 0 t A) :=
  existence_property_of_slashed T (Grounded LQpp) LQpp
    (fun _ hu => grounded_fix LQpp hu) (grounded_collapse_subst LQpp)
    zeroS zeroS_grounded hT hA h

/-! ## 5 · 🏁 HA: la DP reducida a TRES obligaciones, y ni una más

    Aquí se ve qué queda de verdad. `ctx insts = coreAxioms ++ insts.map inductionFormula`,
    y de los 34 axiomas de `coreAxioms` **28 caen solos** por ser de Harrop. Lo que resta va
    como hipótesis explícitas:

    1. **la consistencia de la teoría** — el precio clásico de la barra de Kleene, y no es
       demostrable aquí (Gödel);
    2. **los 6 axiomas que no son de Harrop**, medidos: `ax13_lt_def`, `ax14_sqrt_le`,
       `ax19_lt_trichotomy`, `ax21_mod2_range`, `ax_L2_in_cons`, `ax_L3_in_concat`;
    3. **el esquema de inducción**.

    ⚠️ La lista de (2) **corrige la estimación anterior**, que decía cinco y nombraba
    `ax29_sub_witness`: `ax29` sí es de Harrop, y en cambio `ax14_sqrt_le` y `ax_L2_in_cons`
    no lo son. La medición manda. -/

theorem eq_of_map_self {f : Formula → Formula} : ∀ (l : List Formula), l.map f = l →
    ∀ g, List.Mem g l → f g = g := by
  intro l
  induction l with
  | nil => intro _ g hg; cases hg
  | cons a l0 ih =>
      intro h g hg
      simp only [List.map_cons, List.cons.injEq] at h
      cases hg with
      | head => exact h.1
      | tail _ hg0 => exact ih h.2 g hg0

/-- ⭐ **Los 34 axiomas son sentencias del lenguaje de Q⁺⁺**: ni variables libres ni símbolos
    ajenos. Comprobado por `rfl`, no supuesto. -/
theorem coreAxioms_sentence (g : Formula) (hg : List.Mem g coreAxioms) :
    collapseF LQpp (substF zeroS g) = g :=
  eq_of_map_self (f := fun g => collapseF LQpp (substF zeroS g)) coreAxioms (by rfl) g hg

/-- ⭐⭐ **28 de los 34: los de Harrop caen solos.** Sólo hace falta la consistencia. -/
theorem slash_coreAxioms_harrop {insts : List Formula}
    (hcon : ¬ (ctx insts ⊢ᵢ Formula.bottom))
    (g : Formula) (hg : List.Mem g coreAxioms) (hH : isHarrop g = true) :
    Slash (ctx insts) (Grounded LQpp) (collapseF LQpp (substF zeroS g)) := by
  rw [coreAxioms_sentence g hg]
  exact slash_of_isHarrop (ctx insts) (Grounded LQpp) hcon g hH (ax' hg)

/-- 🏁🏁 **LA PROPIEDAD DE DISYUNCIÓN PARA HA**, con lo que falta puesto como hipótesis y
    nada escondido. -/
theorem haDisjunctionProperty (insts : List Formula)
    (hcon : ¬ (ctx insts ⊢ᵢ Formula.bottom))
    (hHard : ∀ g, List.Mem g coreAxioms → isHarrop g = false →
      Slash (ctx insts) (Grounded LQpp) (collapseF LQpp (substF zeroS g)))
    (hInd : ∀ g, List.Mem g (insts.map inductionFormula) →
      Slash (ctx insts) (Grounded LQpp) (collapseF LQpp (substF zeroS g)))
    {A B : Formula}
    (hAB : collapseF LQpp (substF zeroS (Formula.or A B)) = Formula.or A B)
    (h : ctx insts ⊢ᵢ Formula.or A B) :
    (ctx insts ⊢ᵢ A) ∨ (ctx insts ⊢ᵢ B) := by
  refine qDisjunctionProperty (ctx insts) (fun g hg => ?_) hAB h
  rcases List.mem_append.mp hg with hcore | hind
  · by_cases hH : isHarrop g = true
    · exact slash_coreAxioms_harrop hcon g hcore hH
    · exact hHard g hcore (by simpa using hH)
  · exact hInd g hind

end PeanoRF.HA
