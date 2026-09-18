/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.HA.Axioms

/-! # Numerales sobre `⊢ᵢ` — y todo término cerrado es uno de ellos

  **El puente entre la sintaxis y `ℕ`**, y el ingrediente que le falta a H3ter (la
  propiedad de disyunción **para HA**, no sólo para la lógica).

  ## Por qué hubo que reprobarlo, y no es pereza de nadie

  ROBINSON_PlusPlus tiene esta capa entera (`Full/Numerals.lean`), y sus pruebas son las
  que se copian aquí. Pero está enunciada sobre **`⊢`**:

  ```lean
  theorem numeral_add (a b : Nat) : axioms ⊢ (add (numeral a) (numeral b) =eq numeral (a+b))
  ```

  `⊢` es la HERRAMIENTA, no el SUJETO (ADR-017), y el puente va `⊢ᵢ → ⊢₀ → ⊢` **en un solo
  sentido**. Lo suyo no baja a lo nuestro. ⚠️ No es contaminación —medido el 2026-09-18,
  `numeral_add`/`mul`/`pow` salen **limpios de ω**— es el cálculo.

  ⭐ Y el port es barato porque las tres van por **inducción META**, no por `ax_induction`:
  el contexto es `ctx []`, o sea los axiomas de Q⁺⁺ y nada más. Ni una instancia de
  inducción objeto.

  ## `numeralM`, no `numeral`

  Se usa `ROBINSON_PlusPlus.Minimal.Axioms.numeralM`, que vive en la capa **Minimal** —la
  que ya importábamos— y no `Full.numeral`, que arrastraría `Full/Induction.lean` y con él
  `ax_induction` a nuestra superficie de import. Son la misma función (`σⁿ(0)`).

  ## Lo que falta de `closed_term_eq_numeral`, dicho con precisión

  ⚠️ No es «todo término cerrado»: un `Term.func "foo" []` es cerrado y no es de este
  lenguaje. El enunciado es sobre los términos **del lenguaje de Q⁺⁺ sin variables**, que
  es lo que captura `ClosedQTerm`: cinco símbolos (`zero`, `succ`, `add`, `mul`, `pow`).
-/

namespace PeanoRF.HA

open FOL
open PeanoRF.Calculus
open ROBINSON_PlusPlus.Minimal.Axioms

set_option autoImplicit false

/-! ## Los tres homomorfismos -/

/-- `ctx [] ⊢ᵢ numeral a + numeral b = numeral (a + b)`. Inducción META en `b`. -/
theorem numeralI_add (a b : Nat) :
    ctx [] ⊢ᵢ (add (numeralM a) (numeralM b) =eq numeralM (a + b)) := by
  induction b with
  | zero =>
      have h4 : ctx [] ⊢ᵢ ax4_add_zero := ax' (by simp [coreAxioms])
      have h := specI h4 (numeralM a)
      simp [substFormula, substTerm, substTerms, add, zero] at h
      exact h
  | succ k ih =>
      have h5' : ctx [] ⊢ᵢ ax5_add_succ := ax' (by simp [coreAxioms])
      have h5 : ctx [] ⊢ᵢ
          (add (numeralM a) (succ (numeralM k)) =eq succ (add (numeralM a) (numeralM k))) := by
        have hh := specI (specI h5' (numeralM a)) (numeralM k)
        simp [substFormula, substTerm, substTerms, add, succ,
              FOL.substTerm_liftTerm] at hh
        exact hh
      exact eqI_trans h5 (eqI_congr_succ ih)

/-- `ctx [] ⊢ᵢ numeral a · numeral b = numeral (a · b)`. Inducción META en `b`. -/
theorem numeralI_mul (a b : Nat) :
    ctx [] ⊢ᵢ (mul (numeralM a) (numeralM b) =eq numeralM (a * b)) := by
  induction b with
  | zero =>
      have h8 : ctx [] ⊢ᵢ ax8_mul_zero := ax' (by simp [coreAxioms])
      have h := specI h8 (numeralM a)
      simp [substFormula, substTerm, substTerms, mul, zero] at h
      exact h
  | succ k ih =>
      -- `a * (k+1) = a*k + a` es DEFINICIONAL en `Nat`, así que la meta ya está en forma.
      show ctx [] ⊢ᵢ (mul (numeralM a) (succ (numeralM k)) =eq numeralM (a * k + a))
      have h9' : ctx [] ⊢ᵢ ax9_mul_succ := ax' (by simp [coreAxioms])
      have h9 : ctx [] ⊢ᵢ (mul (numeralM a) (succ (numeralM k)) =eq
                           add (mul (numeralM a) (numeralM k)) (numeralM a)) := by
        have hh := specI (specI h9' (numeralM a)) (numeralM k)
        simp [substFormula, substTerm, substTerms, mul, add, succ,
              FOL.substTerm_liftTerm] at hh
        exact hh
      have hcongr : ctx [] ⊢ᵢ (add (mul (numeralM a) (numeralM k)) (numeralM a) =eq
                               add (numeralM (a * k)) (numeralM a)) :=
        eqI_congr_fun2_l add_sym (numeralM a) ih
      exact eqI_trans (eqI_trans h9 hcongr) (numeralI_add (a * k) a)

/-- `ctx [] ⊢ᵢ (numeral a)^(numeral b) = numeral (a ^ b)`. Inducción META en `b`. -/
theorem numeralI_pow (a b : Nat) :
    ctx [] ⊢ᵢ (pow (numeralM a) (numeralM b) =eq numeralM (a ^ b)) := by
  induction b with
  | zero =>
      have hp : ctx [] ⊢ᵢ ax_pow_zero := ax' (by simp [coreAxioms])
      have h := specI hp (numeralM a)
      simp [substFormula, substTerm, substTerms, pow, zero, one, succ] at h
      exact h
  | succ k ih =>
      show ctx [] ⊢ᵢ (pow (numeralM a) (succ (numeralM k)) =eq numeralM (a ^ k * a))
      have hp' : ctx [] ⊢ᵢ ax_pow_succ := ax' (by simp [coreAxioms])
      have hp : ctx [] ⊢ᵢ (pow (numeralM a) (succ (numeralM k)) =eq
                           mul (pow (numeralM a) (numeralM k)) (numeralM a)) := by
        have hh := specI (specI hp' (numeralM a)) (numeralM k)
        simp [substFormula, substTerm, substTerms, pow, mul, succ,
              FOL.substTerm_liftTerm] at hh
        exact hh
      have hcongr : ctx [] ⊢ᵢ (mul (pow (numeralM a) (numeralM k)) (numeralM a) =eq
                               mul (numeralM (a ^ k)) (numeralM a)) :=
        eqI_congr_fun2_l mul_sym (numeralM a) ih
      exact eqI_trans (eqI_trans hp hcongr) (numeralI_mul (a ^ k) a)

/-! ## Los términos CERRADOS del lenguaje de Q⁺⁺ -/

/-- Los términos del lenguaje de Q⁺⁺ **sin variables**.

    ⚠️ No es «cerrado» a secas: `Term.func "foo" []` no tiene variables y **no** es de este
    lenguaje. Los cinco símbolos son los de `Minimal/Axioms.lean`; `one` y `two` son
    abreviaturas de `succ`, así que no necesitan constructor. -/
inductive ClosedQTerm : Term → Prop where
  | zero : ClosedQTerm zero
  | succ : ∀ t, ClosedQTerm t → ClosedQTerm (succ t)
  | add  : ∀ t u, ClosedQTerm t → ClosedQTerm u → ClosedQTerm (add t u)
  | mul  : ∀ t u, ClosedQTerm t → ClosedQTerm u → ClosedQTerm (mul t u)
  | pow  : ∀ t u, ClosedQTerm t → ClosedQTerm u → ClosedQTerm (pow t u)

/-- ⭐⭐ **Todo término cerrado del lenguaje es demostrablemente un numeral.**

    Es el ingrediente que H3ter necesita: la cláusula `∀` de la barra de Kleene cuantifica
    sobre **todos** los términos cerrados, y la inducción meta sólo alcanza a los numerales.
    Este lema es el que cierra ese hueco — y `slash_eq_congr` (H3bis) es lo que transporta
    la barra a través de la igualdad.

    La prueba es inducción sobre la estructura del término, y cada caso binario es
    `congruencia + homomorfismo`. -/
theorem closed_term_eq_numeral : ∀ {t : Term}, ClosedQTerm t →
    ∃ n : Nat, ctx [] ⊢ᵢ (t =eq numeralM n) := by
  intro t h
  induction h with
  | zero => exact ⟨0, eqI_refl zero⟩
  | succ t _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, eqI_congr_succ hn⟩
  | add t u _ _ iht ihu =>
      obtain ⟨m, hm⟩ := iht
      obtain ⟨n, hn⟩ := ihu
      exact ⟨m + n, eqI_trans (eqI_congr_fun2 add_sym hm hn) (numeralI_add m n)⟩
  | mul t u _ _ iht ihu =>
      obtain ⟨m, hm⟩ := iht
      obtain ⟨n, hn⟩ := ihu
      exact ⟨m * n, eqI_trans (eqI_congr_fun2 mul_sym hm hn) (numeralI_mul m n)⟩
  | pow t u _ _ iht ihu =>
      obtain ⟨m, hm⟩ := iht
      obtain ⟨n, hn⟩ := ihu
      exact ⟨m ^ n, eqI_trans (eqI_congr_fun2 pow_sym hm hn) (numeralI_pow m n)⟩

end PeanoRF.HA
