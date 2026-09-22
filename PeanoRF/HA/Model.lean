/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.HA.Fragment
import PeanoRF.Calculus.Soundness

/-! # 🏁 Un MODELO ESTÁNDAR del fragmento — `hcon` DESCARGADA, y `−` MEDIDO

  ⚠️ **Rectificación, 2026-09-21.** Hasta hoy este proyecto escribió —en ADR-034, ADR-035,
  ADR-036, en varios encabezados y en la memoria— que la consistencia del fragmento
  «se queda como hipótesis PARA SIEMPRE, porque Gödel II». **La segunda mitad es cierta;
  la primera era falsa, y la conclusión no se seguía.**

  Gödel II dice que **HA no prueba su propia consistencia**. No dice que no la pruebe
  nadie: la consistencia de una teoría aritmética se demuestra en un metalenguaje que la
  exceda, y Lean lo excede de sobra. Se confundió «no demostrable DENTRO» con «no
  demostrable». Lo que sí queda intacto de aquella frase: **la consistencia no se paga con
  una derivación del propio cálculo**, y por eso el pago tiene que venir de la semántica.

  ⭐ Y el patrón ya estaba en el árbol un piso más abajo: `derivesI_consistent` descarga la
  consistencia de la **lógica** exhibiendo un modelo de un punto. Esto hace exactamente lo
  mismo un piso más arriba, con `ℕ`.

  ## Qué se construye

  Un **único** modelo, con un parámetro: `natModelK k` es `ℕ` con sus operaciones, y `k`
  es el valor que se le da a `−` **fuera del rango que el axioma `ax29_sub_witness` fija**.
  El parámetro hace los dos trabajos de golpe:

  | | |
  |---|---|
  | `natModelK_sat` | los **23** axiomas son verdaderos en `natModelK k`, **para todo `k`** |
  | `hcon_fragment` | con `k = 0` ⇒ de `ctxTM []` no se deriva `⊥`, por `derivesI_soundness` |
  | **`qDisjunctionProperty_arithTM_final`** | ⇒ **la DP del fragmento, INCONDICIONAL** |
  | `sub_neither` | variando `k` ⇒ **`5̄ − 7̄` no es demostrablemente igual a ningún numeral, ni demostrablemente distinto de ninguno** |
  | **`hNum_false_on_sub`** | ⇒ **`hNum` sobre la signatura completa es FALSA**, con testigo |

  ⚠️ `∈` se interpreta como **siempre falso**. No es un truco: es exactamente lo que
  `ax_L1_in_nil` (`∀x. ¬(x ∈ [])`) pide, y es lo **único** que la teoría de aquí dice de
  `∈` —los axiomas `ax_L2_in_cons`/`ax_L3_in_concat`, que sí lo obligarían, se quedaron
  fuera de los 23—. Igual con `√`, `/₂`, `::`, `##`, `Π_p`: **no se mencionan**, así que el
  modelo los manda al `else` y les da `0`. Un modelo sólo tiene que satisfacer los axiomas
  que hay.

  ## ⛔ El alcance exacto de la medición de `−`

  Lo que se mide es sobre `subAxioms` = los 22 del fragmento **más `ax29_sub_witness`**,
  que es **el único axioma de `coreAxioms` que menciona `−`**. Para subirlo de 23 a los 34
  haría falta un modelo de `coreAxioms` entero —listas, pares de Cantor, `√`, `Π_p`—, que
  este proyecto todavía no tiene. **Eso queda dicho y no supuesto.**

  ## El precio, medido

  La única táctica pesada es `omega`, y sólo en las metas donde la aritmética de `ℕ` no es
  una ecuación de definición: `ax13` (las dos direcciones), `ax16`, `ax21`, `ax24` y
  `ax29`. ⚠️ Todas son metas **aritméticas de verdad** —`<`, `≤`, `+`, `%`— y por tanto
  dentro del lenguaje de `omega`: no es el caso de `shift_updateEnv_comm`, donde `omega`
  cerraba por contradicción una meta que no era aritmética y metía `Classical.choice` (ver
  el encabezado de `PeanoRF/Calculus/Soundness.lean`). El footprint queda **medido**, no
  argumentado, en `PeanoRF/Meta/AxiomCheck.lean`.
-/

namespace PeanoRF.HA

open FOL
open FOL.Metamath.Semantics
open ROBINSON_PlusPlus.Minimal.Axioms
open PeanoRF.Calculus

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## 1 · El modelo, con `−` como parámetro -/

/-- Los 26 del fragmento más el **único** axioma de `coreAxioms` que menciona `−`. -/
def subAxioms : List Formula := arithTDCSAxioms ++ [ax29_sub_witness]

/-- **El modelo estándar, con un parámetro.** Los siete símbolos que `LQtm` admite —`0`,
    `σ`, `+`, `*`, `^`, `τ`, `%₂`— van a las operaciones de `ℕ`, y `<` al orden.

    ⭐ `−` va al monus **dentro del rango que `ax29_sub_witness` fija** (`b ≤ a`) y a `k`
    **fuera**. Eso es lo que hace del modelo una familia: el axioma no dice nada de `a − b`
    con `a < b`, así que ahí el valor es libre.

    Lo demás cae al `else`: la teoría de este módulo no lo menciona.

    ⚠️ `And` va escrito a mano: en este archivo la notación `∧` es `Formula.and`, la de
    FOL, no la conjunción de Lean. -/
def natModelK (k : Nat) : Model Nat where
  func s ds :=
    if s = succ_sym then ds.headD 0 + 1
    else if s = add_sym then ds.headD 0 + ds.tail.headD 0
    else if s = mul_sym then ds.headD 0 * ds.tail.headD 0
    else if s = pow_sym then ds.headD 0 ^ ds.tail.headD 0
    else if s = pred_sym then ds.headD 0 - 1
    else if s = mod2_sym then ds.headD 0 % 2
    else if s = div2_sym then ds.headD 0 / 2
    else if s = sqrt_sym then isqrt (ds.headD 0)
    else if s = cons_sym then
      ((ds.headD 0 + (ds.tail.headD 0 + 1)) * ((ds.headD 0 + (ds.tail.headD 0 + 1)) + 1)
        + 2 * (ds.tail.headD 0 + 1)) / 2
    else if s = sub_sym then
      (if ds.tail.headD 0 ≤ ds.headD 0 then ds.headD 0 - ds.tail.headD 0 else k)
    else 0
  rel s ds := And (s = lt_sym) (ds.headD 0 < ds.tail.headD 0)

/-- La táctica que convierte una fórmula de la teoría en un enunciado de `ℕ`: despliega el
    axioma, la evaluación, el modelo y los símbolos, y `+decide` cierra las comparaciones
    entre literales de `String` (`"+" = "σ"` y compañía), que `simp` sola no decide. -/
local macro "evalNat" : tactic =>
  `(tactic| simp +decide only [ax2_peano_succ_neq_zero, ax3_peano_succ_inj, ax4_add_zero,
      ax5_add_succ, ax6_add_comm, ax7_add_assoc, ax8_mul_zero, ax9_mul_succ, ax10_mul_comm,
      ax11_mul_assoc, ax12_mul_distrib, ax13_lt_def, ax18_lt_irrefl, ax19_lt_trichotomy,
      ax_L1_in_nil, ax_pow_zero, ax_pow_succ, ax25_pred_zero, ax26_pred_succ,
      ax16_mod2_succ, ax21_mod2_range, ax24_mod2_of_even, ax17_div_mod_eq,
      ax_L0_cons_def, ax14_sqrt_le, ax15_lt_succ_sqrt,
      ax29_sub_witness,
      forall_, forall_2, forall_3, neg, iff, ex, evalFormula, evalTerm,
      evalTerms, natModelK, shiftEnv, zero, succ, add, mul, pow, pred, mod2, div2, sub,
      cons, pair, cantor_func, cantor_poly, sqrt, sq, lt, le,
      In, nil, one, two, zero_sym, succ_sym, add_sym, mul_sym, pow_sym, pred_sym, mod2_sym,
      sub_sym, lt_sym, in_sym, List.headD, List.tail, reduceIte])

/-! ## 2 · Los 23 axiomas, verdaderos en `ℕ` — para todo `k` -/

/-- ⭐⭐ **Los 23 axiomas son verdaderos en `natModelK k`, sea cual sea `k`.**

    Uno por uno, en el mismo orden que `slash_arithTMAxioms`. Diecisiete salen por `rfl` o
    por un lema del núcleo de `Nat`; cinco necesitan `omega`, y las cinco son metas
    aritméticas. El vigesimotercero, `ax29`, es el que usa el parámetro —y sólo lo usa en
    la rama que el axioma **no** constriñe—. -/
theorem natModelK_sat (k : Nat) (v : Nat → Nat) :
    ∀ g, List.Mem g subAxioms → evalFormula (natModelK k) v g := by
  intro g hg
  simp only [subAxioms, arithTDCSAxioms, arithTDCAxioms, arithTDAxioms, arithTMAxioms,
    arithTAxioms, arithAxioms] at hg
  rcases hg with _ | ⟨_, hg⟩
  · evalNat; intro d h; exact Nat.succ_ne_zero d h
  rcases hg with _ | ⟨_, hg⟩
  · evalNat; intro d e h; exact Nat.succ.inj h
  rcases hg with _ | ⟨_, hg⟩
  · evalNat; intro d; rfl
  rcases hg with _ | ⟨_, hg⟩
  · evalNat; intro d e; rfl
  rcases hg with _ | ⟨_, hg⟩
  · evalNat; intro d e; exact Nat.add_comm d e
  rcases hg with _ | ⟨_, hg⟩
  · evalNat; intro a b c; exact Nat.add_assoc a b c
  rcases hg with _ | ⟨_, hg⟩
  · evalNat; intro d; rfl
  rcases hg with _ | ⟨_, hg⟩
  · evalNat; intro d e; rfl
  rcases hg with _ | ⟨_, hg⟩
  · evalNat; intro d e; exact Nat.mul_comm d e
  rcases hg with _ | ⟨_, hg⟩
  · evalNat; intro a b c; exact Nat.mul_assoc a b c
  rcases hg with _ | ⟨_, hg⟩
  · evalNat; intro a b c; exact Nat.mul_add a b c
  rcases hg with _ | ⟨_, hg⟩
  · -- `ax13_lt_def`: `n < m ⇔ ∃j, n + σj = m`. El testigo es `m - n - 1`.
    evalNat
    intro n m
    refine And.intro (fun h => ⟨m - n - 1, ?_⟩) (fun h => And.intro trivial ?_)
    · have hlt := h.2; omega
    · obtain ⟨j, hj⟩ := h; omega
  rcases hg with _ | ⟨_, hg⟩
  · evalNat; intro d h; exact Nat.lt_irrefl d h.2
  rcases hg with _ | ⟨_, hg⟩
  · -- `ax19_lt_trichotomy`, constructivamente: `Nat.lt_or_ge` + `Nat.eq_or_lt_of_le`.
    evalNat
    intro n m
    rcases Nat.lt_or_ge n m with h | h
    · exact Or.inl (And.intro trivial h)
    · rcases Nat.eq_or_lt_of_le h with h2 | h2
      · exact Or.inr (Or.inl h2.symm)
      · exact Or.inr (Or.inr (And.intro trivial h2))
  rcases hg with _ | ⟨_, hg⟩
  · -- `ax_L1_in_nil`: `∈` es siempre falso, y eso es justo lo que el axioma pide.
    evalNat; intro d h; exact h.1
  rcases hg with _ | ⟨_, hg⟩
  · evalNat; intro d; rfl
  rcases hg with _ | ⟨_, hg⟩
  · evalNat; intro d e; rfl
  rcases hg with _ | ⟨_, hg⟩
  · evalNat
  rcases hg with _ | ⟨_, hg⟩
  · evalNat; intro d; rfl
  rcases hg with _ | ⟨_, hg⟩
  · evalNat; intro d; exact And.intro (fun _ => by omega) (fun _ => by omega)
  rcases hg with _ | ⟨_, hg⟩
  · evalNat; intro d; omega
  rcases hg with _ | ⟨_, hg⟩
  · evalNat; intro d e h; omega
  rcases hg with _ | ⟨_, hg⟩
  · -- `ax17_div_mod_eq`: `(d/2)·2 + d%2 = d`, que es aritmética de `ℕ`.
    evalNat; intro d; omega
  rcases hg with _ | ⟨_, hg⟩
  · -- `ax_L0_cons_def`: `d :: e = pair d (σe)`. En el modelo los dos lados son **el mismo
    -- término**: `::` se interpreta como el emparejamiento de Cantor, que es lo que
    -- `pair` desarrolla.
    evalNat; intro d e; trivial
  rcases hg with _ | ⟨_, hg⟩
  · -- `ax14_sqrt_le`: `(⌊√d⌋)² ≤ d`, y el `≤` del objeto es una DISYUNCIÓN.
    evalNat
    intro d
    rcases Nat.eq_or_lt_of_le (isqrt_le d) with he | hl
    · exact Or.inr he
    · exact Or.inl (And.intro trivial hl)
  rcases hg with _ | ⟨_, hg⟩
  · -- `ax15_lt_succ_sqrt`: `d < (⌊√d⌋+1)²`.
    evalNat; intro d; exact And.intro trivial (lt_isqrt_succ d)
  rcases hg with _ | ⟨_, hg⟩
  · -- `ax29_sub_witness`: el parámetro `k` vive en la rama `¬(e ≤ d)`, que la hipótesis
    -- del axioma excluye. Por eso el axioma vale **para todo `k`**.
    evalNat
    intro d e h
    have hle : e ≤ d := by
      rcases h with h | h
      · exact Nat.le_of_lt h.2
      · exact Nat.le_of_eq h
    rw [if_pos hle]
    omega
  cases hg

/-- Los 22 del fragmento, en el modelo con `k = 0`. -/
theorem natModel_sat (v : Nat → Nat) :
    ∀ g, List.Mem g arithTMAxioms → evalFormula (natModelK 0) v g :=
  fun g hg => natModelK_sat 0 v g (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ hg))))

/-- Los 23 del fragmento con `/₂`, en el modelo con `k = 0`. -/
theorem natModelD_sat (v : Nat → Nat) :
    ∀ g, List.Mem g arithTDAxioms → evalFormula (natModelK 0) v g :=
  fun g hg => natModelK_sat 0 v g (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ hg)))

/-- Los 24 del fragmento con `::`, en el modelo con `k = 0`. -/
theorem natModelC_sat (v : Nat → Nat) :
    ∀ g, List.Mem g arithTDCAxioms → evalFormula (natModelK 0) v g :=
  fun g hg => natModelK_sat 0 v g (List.mem_append_left _ (List.mem_append_left _ hg))

/-- Los 26 del fragmento con `√`, en el modelo con `k = 0`. -/
theorem natModelS_sat (v : Nat → Nat) :
    ∀ g, List.Mem g arithTDCSAxioms → evalFormula (natModelK 0) v g :=
  fun g hg => natModelK_sat 0 v g (List.mem_append_left _ hg)

/-! ## 3 · 🏁 `hcon` descargada, y la DP sin hipótesis -/

/-- 🏁 **La consistencia del fragmento, DEMOSTRADA.** Si `ctxTM []` derivase `⊥`, por
    `derivesI_soundness` `⊥` sería verdadera en todo modelo del contexto —y `natModelK 0`
    lo es—. Pero `evalFormula _ _ ⊥` es `False`. -/
theorem hcon_fragment : Not (ctxTM [] ⊢ᵢ Formula.bottom) := by
  intro h
  have hv := derivesI_soundness h
  refine hv Nat (natModelK 0) (fun _ => 0) (fun f hf => ?_)
  have hf2 : f ∈ arithTMAxioms := by simpa [ctxTM] using hf
  exact natModel_sat _ f hf2

/-- 🏁🏁🏁 **LA DP DEL FRAGMENTO, INCONDICIONAL.** Sin `hcon`, sin `hInd`, sin `hNum`, sin
    `hlift`, sin `hIn`: **sin hipótesis**.

    De toda disyunción cerrada del lenguaje del fragmento que la teoría demuestre, la teoría
    demuestra uno de los dos lados. Veintidós de los treinta y cuatro axiomas de
    `coreAxioms`, siete símbolos, y nada que suponer. -/
theorem qDisjunctionProperty_arithTM_final {A B : Formula}
    (hAB : collapseF LQtm (substF zeroS (Formula.or A B)) = Formula.or A B)
    (h : ctxTM [] ⊢ᵢ Formula.or A B) :
    Or (ctxTM [] ⊢ᵢ A) (ctxTM [] ⊢ᵢ B) :=
  qDisjunctionProperty_arithTM hcon_fragment hAB h

/-! ## 4 · ⛔ `−`, INDETERMINADO — medido, no argumentado -/

/-- `0` denota cero. -/
theorem evalT_zero (k : Nat) (v : Nat → Nat) : evalTerm (natModelK k) v zero = 0 := by
  simp +decide only [zero, evalTerm, evalTerms, natModelK, zero_sym, succ_sym, add_sym,
    mul_sym, pow_sym, pred_sym, mod2_sym, sub_sym, List.headD, List.tail, reduceIte]

/-- `σ` denota el sucesor. -/
theorem evalT_succ (k : Nat) (v : Nat → Nat) (t : Term) :
    evalTerm (natModelK k) v (succ t) = evalTerm (natModelK k) v t + 1 := by
  simp +decide only [succ, evalTerm, evalTerms, natModelK, succ_sym, List.headD, List.tail,
    reduceIte]

/-- ⭐ `−` denota el monus **dentro del rango**, y el parámetro `k` **fuera**. Esta es la
    ecuación que hace toda la medición de la sección. -/
theorem evalT_sub (k : Nat) (v : Nat → Nat) (t u : Term) :
    evalTerm (natModelK k) v (sub t u)
      = (if evalTerm (natModelK k) v u ≤ evalTerm (natModelK k) v t
          then evalTerm (natModelK k) v t - evalTerm (natModelK k) v u else k) := by
  simp +decide only [sub, evalTerm, evalTerms, natModelK, succ_sym, add_sym, mul_sym,
    pow_sym, pred_sym, mod2_sym, sub_sym, List.headD, List.tail, reduceIte]

/-- En `natModelK k` los numerales denotan lo que parecen. -/
theorem eval_numeralM (k : Nat) (v : Nat → Nat) : ∀ n : Nat,
    evalTerm (natModelK k) v (numeralM n) = n := by
  intro n
  induction n with
  | zero => exact evalT_zero k v
  | succ m ih =>
    show evalTerm (natModelK k) v (succ (numeralM m)) = m + 1
    rw [evalT_succ, ih]

/-- ⭐ **El valor de `5̄ − 7̄` en el modelo ES el parámetro.** `7 ≤ 5` es falso, así que cae
    en la rama que `ax29_sub_witness` deja libre. -/
theorem eval_sub_5_7 (k : Nat) (v : Nat → Nat) :
    evalTerm (natModelK k) v (sub (numeralM 5) (numeralM 7)) = k := by
  rw [evalT_sub, eval_numeralM, eval_numeralM, if_neg (by decide)]

/-- ⛔ **La medición, en forma general.** Toda teoría cuyos axiomas sean verdaderos en
    `natModelK k` **para todo `k`** deja `5̄ − 7̄` indeterminado: para ningún numeral
    demuestra la igualdad, y para ninguno demuestra la desigualdad.

    La demostración no argumenta nada sobre «qué axiomas hay»: mide dos modelos —`k = n + 1`
    y `k = n`— y aplica `derivesI_soundness`. -/
theorem sub_neither_of_valid {Γ : List Formula}
    (hΓ : ∀ (k : Nat) (v : Nat → Nat) (g : Formula), List.Mem g Γ →
      evalFormula (natModelK k) v g) (n : Nat) :
    And (Not (Γ ⊢ᵢ Formula.eq (sub (numeralM 5) (numeralM 7)) (numeralM n)))
        (Not (Γ ⊢ᵢ neg (Formula.eq (sub (numeralM 5) (numeralM 7)) (numeralM n)))) := by
  refine And.intro (fun h => ?_) (fun h => ?_)
  · -- En el modelo `k = n + 1` la igualdad diría `n + 1 = n`.
    have hv := derivesI_soundness h Nat (natModelK (n + 1)) (fun _ => 0)
      (fun f hf => hΓ (n + 1) _ f hf)
    have hn : n + 1 = n := by
      simpa only [evalFormula, eval_sub_5_7, eval_numeralM] using hv
    omega
  · -- En el modelo `k = n` la desigualdad diría `n ≠ n`.
    have hv := derivesI_soundness h Nat (natModelK n) (fun _ => 0)
      (fun f hf => hΓ n _ f hf)
    refine hv ?_
    simp only [evalFormula, eval_sub_5_7, eval_numeralM]

/-- ⛔ **`5̄ − 7̄` es indeterminado sobre `subAxioms`**: los 22 del fragmento más el único
    axioma de `coreAxioms` que menciona `−`. -/
theorem sub_neither (n : Nat) :
    And (Not (subAxioms ⊢ᵢ Formula.eq (sub (numeralM 5) (numeralM 7)) (numeralM n)))
        (Not (subAxioms ⊢ᵢ neg (Formula.eq (sub (numeralM 5) (numeralM 7)) (numeralM n)))) :=
  sub_neither_of_valid (fun k v g hg => natModelK_sat k v g hg) n

/-- `5̄ − 7̄` está anclado en la signatura **completa** de Q⁺⁺: `LQpp` admite `−` con
    aridad 2, y el término es cerrado. -/
theorem grounded_sub_5_7 : Grounded LQpp (sub (numeralM 5) (numeralM 7)) :=
  grounded_func2 LQpp (by decide)
    (grounded_numeralM LQpp (by decide) 5) (grounded_numeralM LQpp (by decide) 7)

/-- ⛔⛔ **`hNum` sobre la signatura completa es FALSA — y con testigo.**

    Esto es lo que ADR-037 dejó como *argumento* («`−` sólo aparece en un axioma, y
    condicionado a `x ≤ y`»). Aquí está **medido**: el testigo es `5̄ − 7̄`, y lo que lo
    refuta son dos modelos y `derivesI_soundness`. -/
theorem hNum_false_on_sub :
    Not (∀ t : Term, Grounded LQpp t →
      ∃ n : Nat, subAxioms ⊢ᵢ Formula.eq t (numeralM n)) := by
  intro hNum
  obtain ⟨n, hn⟩ := hNum (sub (numeralM 5) (numeralM 7)) grounded_sub_5_7
  exact (sub_neither n).1 hn



/-! ## 5 · 🏁 El fragmento con `/₂` — 23 de 34, también incondicional -/

/-- 🏁 **La consistencia del fragmento con `/₂`.** Mismo modelo, mismo argumento. -/
theorem hcon_fragmentD : Not (ctxD [] ⊢ᵢ Formula.bottom) := by
  intro h
  have hv := derivesI_soundness h
  refine hv Nat (natModelK 0) (fun _ => 0) (fun f hf => ?_)
  have hf2 : f ∈ arithTDAxioms := by simpa [ctxD] using hf
  exact natModelD_sat _ f hf2

/-- 🏁🏁🏁 **LA DP DEL FRAGMENTO CON `/₂`, INCONDICIONAL** — **23 de los 34** axiomas de
    `coreAxioms`, ocho símbolos, **cero hipótesis**.

    ⛔ Y `/₂` entra **contra lo que ADR-037 dio por cerrado**: no hizo falta cancelación
    ninguna, sólo el orden (`PeanoRF/HA/Order.lean`). -/
theorem qDisjunctionProperty_arithTD_final {A B : Formula}
    (hAB : collapseF LQtd (substF zeroS (Formula.or A B)) = Formula.or A B)
    (h : ctxD [] ⊢ᵢ Formula.or A B) :
    Or (ctxD [] ⊢ᵢ A) (ctxD [] ⊢ᵢ B) :=
  qDisjunctionProperty_arithTD hcon_fragmentD hAB h


/-! ## 6 · 🏁 El fragmento con `::` — 24 de 34, también incondicional -/

/-- 🏁 **La consistencia del fragmento con `::`.** El modelo interpreta `::` como el
    emparejamiento de Cantor, que es lo que `pair` desarrolla, así que `ax_L0` sale por
    `trivial`: los dos lados son el mismo término. -/
theorem hcon_fragmentC : Not (ctxC [] ⊢ᵢ Formula.bottom) := by
  intro h
  have hv := derivesI_soundness h
  refine hv Nat (natModelK 0) (fun _ => 0) (fun f hf => ?_)
  have hf2 : f ∈ arithTDCAxioms := by simpa [ctxC] using hf
  exact natModelC_sat _ f hf2

/-- 🏁🏁🏁 **LA DP DEL FRAGMENTO CON `::`, INCONDICIONAL** — **24 de los 34** axiomas de
    `coreAxioms`, nueve símbolos, **cero hipótesis**.

    ⛔ Y `::` entra **por COMPOSICIÓN**: ADR-037 lo bloqueaba porque «`pair` usa `/₂`», y ese
    bloqueo cayó solo en cuanto `/₂` quedó determinado (ADR-042). Sin una línea de teoría
    nueva. -/
theorem qDisjunctionProperty_arithTDC_final {A B : Formula}
    (hAB : collapseF LQtdc (substF zeroS (Formula.or A B)) = Formula.or A B)
    (h : ctxC [] ⊢ᵢ Formula.or A B) :
    Or (ctxC [] ⊢ᵢ A) (ctxC [] ⊢ᵢ B) :=
  qDisjunctionProperty_arithTDC hcon_fragmentC hAB h


/-! ## 7 · 🏁 El fragmento con `√` — 26 de 34, también incondicional -/

/-- 🏁 **La consistencia del fragmento con `√`.** El modelo interpreta `√` con la `isqrt`
    del meta, y sus dos axiomas son justo las dos cotas de `isqrt`. -/
theorem hcon_fragmentS : Not (ctxS [] ⊢ᵢ Formula.bottom) := by
  intro h
  have hv := derivesI_soundness h
  refine hv Nat (natModelK 0) (fun _ => 0) (fun f hf => ?_)
  have hf2 : f ∈ arithTDCSAxioms := by simpa [ctxS] using hf
  exact natModelS_sat _ f hf2

/-- 🏁🏁🏁 **LA DP DEL FRAGMENTO CON `√`, INCONDICIONAL** — **26 de los 34** axiomas de
    `coreAxioms`, diez símbolos, **cero hipótesis**.

    ⛔ Y es el primero que mete en el fragmento un axioma **DURO**: `ax14_sqrt_le` no es de
    Harrop —`le a b` es `a < b ∨ a = b`— y hay que barrarlo con `slash_ax14`, que para esto
    hubo que generalizar de `ctx`/`LQpp` a `{Γ}`/`L`. -/
theorem qDisjunctionProperty_arithTDCS_final {A B : Formula}
    (hAB : collapseF LQtdcs (substF zeroS (Formula.or A B)) = Formula.or A B)
    (h : ctxS [] ⊢ᵢ Formula.or A B) :
    Or (ctxS [] ⊢ᵢ A) (ctxS [] ⊢ᵢ B) :=
  qDisjunctionProperty_arithTDCS hcon_fragmentS hAB h

end PeanoRF.HA
