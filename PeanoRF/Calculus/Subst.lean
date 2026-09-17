/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.Prelim

/-! # Sustitución PARALELA sobre la sintaxis de FOL⁼

  **Por qué existe este módulo, y por qué duele que exista.** Es infraestructura de
  SINTAXIS, o sea de FOL, no de PeanoRF: ADR-010 dice que no se redefine lo que ya está
  aguas arriba. Pero **medido el 2026-09-17, aguas arriba no está**: en todo el árbol
  activo de FOL sólo hay sustitución de UNA variable (`substFormula`, `substTerms`) y
  `liftN`. Va pedido en `doc/ENCARGO-FOL-2026-09-17.md`; mientras tanto, esto.

  ⚠️ **Deuda declarada, con salida escrita**: este módulo está hecho para que FOL pueda
  adoptarlo tal cual. El día que lo haga, aquí sólo quedan los `export`.

  ## Para qué hace falta

  Para la propiedad de disyunción (H3bis). El lema L2 —`Γ ⊢ᵢ f` con `Γ` barrado ⟹
  `Slash f`— **no cierra** con inducción estructural si el enunciado no se generaliza
  sobre sustituciones:

  > `Γ ⊢ᵢ f ⟹ ∀ ρ, (∀ g ∈ Γ, Slash (gρ)) → Slash (fρ)`

  En el caso `intro_forall` la meta es `∀t, Slash ((A·upS ρ)[t/0])`, que por el álgebra de
  abajo es `Slash (A · consS t ρ)`: **la hipótesis de inducción de la premisa con otra
  sustitución**. Y la HI está cuantificada sobre todas. Con una sola variable eso no se
  puede ni enunciar.

  ## El plan de la construcción, sin circularidades

  El orden importa: `substT_comp` a nivel de TÉRMINOS **no necesita `upS`** (los términos
  no tienen ligaduras), y de ahí sale todo lo demás.

  1. `substT_liftS`, `substT_singleS` — las dos operaciones de FOL **son** sustituciones
     paralelas. Es lo que conecta este módulo con su calculo.
  2. `substT_comp` — trivial: en `.var n` es la definición de `compS`.
  3. `substT_upS_lift` — vía 1 + 2, sin inducción nueva.
  4. `upS_compS`, `upS_liftS`, `upS_singleS` — puro `funext`.
  5. Las tres versiones para fórmulas, por inducción, usando 4 en los casos `∀`/`∃`.

  ## ⚠️ Por qué las sustituciones se llaman `ρ` y no `σ`

  Porque **`σ` no es un identificador válido en este proyecto**: `peanolib` la declara como
  NOTACIÓN (`notation "σ" n:max => ℕ₀.succ n`, `Peano/PeanoNat.lean`), y como `Prelim`
  importa `Peano.PeanoNat.Axioms`, el símbolo es un token reservado en todo el árbol. El
  error que da es `unexpected token 'σ'; expected '_' or identifier`, que no se parece
  nada a su causa. Queda anotado aquí para el siguiente que lo intente.
-/

namespace PeanoRF.Calculus

open FOL

set_option autoImplicit false

/-! ## Definiciones -/

/-- Una sustitución paralela: a cada índice de De Bruijn, un término. -/
abbrev Subst := Nat → Term

/-- `consS t ρ` — «`t` en el índice 0, `ρ` desplazada». Es la extensión que usa el caso
    `intro_forall` de L2. -/
def consS (t : Term) (ρ : Subst) : Subst
  | 0     => t
  | n + 1 => ρ n

/-- `upS ρ` — `ρ` atravesando UNA ligadura: el índice 0 queda intacto y el resto se
    levanta. Es lo único no trivial de la sustitución paralela. -/
def upS (ρ : Subst) : Subst
  | 0     => Term.var 0
  | n + 1 => liftTerm 0 (ρ n)

mutual
/-- Sustitución paralela en términos. -/
def substT (ρ : Subst) : Term → Term
  | .var n     => ρ n
  | .func f ts => .func f (substTs ρ ts)

/-- Sustitución paralela en listas de términos. -/
def substTs (ρ : Subst) : List Term → List Term
  | []      => []
  | t :: ts => substT ρ t :: substTs ρ ts
end

/-- Sustitución paralela en fórmulas. El caso de los cuantificadores es el que manda: se
    entra bajo la ligadura con `upS`. -/
def substF (ρ : Subst) : Formula → Formula
  | .bottom    => .bottom
  | .atom p ts => .atom p (substTs ρ ts)
  | .eq t u    => .eq (substT ρ t) (substT ρ u)
  | .impl a b  => .impl (substF ρ a) (substF ρ b)
  | .forall a  => .forall (substF (upS ρ) a)
  | .and a b   => .and (substF ρ a) (substF ρ b)
  | .or a b    => .or (substF ρ a) (substF ρ b)
  | .ex a      => .ex (substF (upS ρ) a)

/-- Composición: `compS ρ τ` aplica primero `τ` y luego `ρ`. -/
def compS (ρ τ : Subst) : Subst := fun n => substT ρ (τ n)

/-- `liftFormula c` **como** sustitución paralela. -/
def liftS (c : Nat) : Subst := fun n => if n < c then Term.var n else Term.var (n + 1)

/-- `substFormula v s` **como** sustitución paralela. ⚠️ Reproduce la convención de FOL,
    que **decrementa** los índices mayores que `v`: sustituir cierra la ligadura. -/
def singleS (v : Nat) (s : Term) : Subst :=
  fun n => if n = v then s else if n > v then Term.var (n - 1) else Term.var n

/-! ## 1 · Las operaciones de FOL son sustituciones paralelas (nivel término) -/

mutual
theorem substT_liftS : ∀ (c : Nat) (t : Term), substT (liftS c) t = liftTerm c t := by
  intro c t
  cases t with
  | var n => by_cases h : n < c <;> simp [substT, liftTerm, liftS, h]
  | func f ts => simp only [substT, liftTerm]; exact congrArg _ (substTs_liftS c ts)

theorem substTs_liftS : ∀ (c : Nat) (ts : List Term), substTs (liftS c) ts = liftTerms c ts := by
  intro c ts
  cases ts with
  | nil => rfl
  | cons t ts' =>
      simp only [substTs, liftTerms, List.cons.injEq]
      exact ⟨substT_liftS c t, substTs_liftS c ts'⟩
end

mutual
theorem substT_singleS : ∀ (v : Nat) (s t : Term),
    substT (singleS v s) t = substTerm v s t := by
  intro v s t
  cases t with
  | var n =>
      by_cases h1 : n = v
      · simp [substT, substTerm, singleS, h1]
      · by_cases h2 : n > v <;> simp [substT, substTerm, singleS, h1, h2]
  | func f ts => simp only [substT, substTerm]; exact congrArg _ (substTs_singleS v s ts)

theorem substTs_singleS : ∀ (v : Nat) (s : Term) (ts : List Term),
    substTs (singleS v s) ts = substTerms v s ts := by
  intro v s ts
  cases ts with
  | nil => rfl
  | cons t ts' =>
      simp only [substTs, substTerms, List.cons.injEq]
      exact ⟨substT_singleS v s t, substTs_singleS v s ts'⟩
end

/-! ## 2 · Composición en términos — sin `upS`, y por eso sin circularidad -/

mutual
theorem substT_comp : ∀ (ρ τ : Subst) (t : Term),
    substT ρ (substT τ t) = substT (compS ρ τ) t := by
  intro ρ τ t
  cases t with
  | var n => rfl
  | func f ts => simp only [substT]; exact congrArg _ (substTs_comp ρ τ ts)

theorem substTs_comp : ∀ (ρ τ : Subst) (ts : List Term),
    substTs ρ (substTs τ ts) = substTs (compS ρ τ) ts := by
  intro ρ τ ts
  cases ts with
  | nil => rfl
  | cons t ts' =>
      simp only [substTs, List.cons.injEq]
      exact ⟨substT_comp ρ τ t, substTs_comp ρ τ ts'⟩
end

/-! ## 3 · `upS` contra el levantamiento -/

/-- 🔑 La identidad puntual de la que sale todo: entrar bajo una ligadura y luego levantar
    es lo mismo que levantar y luego entrar. -/
theorem compS_upS_liftS (ρ : Subst) : compS (upS ρ) (liftS 0) = compS (liftS 0) ρ := by
  funext n
  simp only [compS, liftS]
  simp only [Nat.not_lt_zero, if_false]
  exact (substT_liftS 0 (ρ n)).symm

theorem substT_upS_lift (ρ : Subst) (t : Term) :
    substT (upS ρ) (liftTerm 0 t) = liftTerm 0 (substT ρ t) := by
  rw [← substT_liftS 0 t, substT_comp, compS_upS_liftS, ← substT_comp, substT_liftS]

theorem upS_compS (ρ τ : Subst) : upS (compS ρ τ) = compS (upS ρ) (upS τ) := by
  funext n
  cases n with
  | zero => rfl
  | succ m => simpa [upS, compS] using (substT_upS_lift ρ (τ m)).symm

theorem upS_liftS (c : Nat) : upS (liftS c) = liftS (c + 1) := by
  funext n
  cases n with
  | zero => simp [upS, liftS]
  | succ m =>
      by_cases h : m < c <;>
        simp [upS, liftS, h, liftTerm, Nat.succ_lt_succ_iff, Nat.not_lt_zero]

theorem upS_singleS (v : Nat) (s : Term) :
    upS (singleS v s) = singleS (v + 1) (liftTerm 0 s) := by
  funext n
  cases n with
  | zero =>
      simp only [upS, singleS, if_neg (show ¬ (0 = v + 1) by omega),
        if_neg (show ¬ (0 > v + 1) by omega)]
  | succ m =>
      -- ⚠️ Escrito con `simp only` + `if_pos`/`if_neg` EXPLÍCITOS, no con `simp` a secas.
      -- Medido el 2026-09-17: la versión con `simp` metía `Classical.choice`, y el gate la
      -- cazó (era el ÚNICO foco, y contaminaba siete declaraciones aguas abajo). Misma
      -- familia que el hallazgo del `omega` de ADR-019: una táctica automática decidiendo
      -- una condición sin instancia `Decidable` puesta a mano.
      simp only [upS, singleS]
      rcases Nat.lt_trichotomy m v with h | h | h
      · rw [if_neg (show ¬ (m = v) by omega), if_neg (show ¬ (m > v) by omega),
          if_neg (show ¬ (m + 1 = v + 1) by omega),
          if_neg (show ¬ (m + 1 > v + 1) by omega), liftTerm,
          if_neg (show ¬ (m < 0) by omega)]
      · rw [if_pos h, if_pos (show m + 1 = v + 1 by omega)]
      · rw [if_neg (show ¬ (m = v) by omega), if_pos h,
          if_neg (show ¬ (m + 1 = v + 1) by omega),
          if_pos (show m + 1 > v + 1 by omega), liftTerm,
          if_neg (show ¬ (m - 1 < 0) by omega), show m - 1 + 1 = m + 1 - 1 by omega]

/-! ## 4 · Las tres identidades a nivel de fórmula -/

theorem substF_liftS : ∀ (f : Formula) (c : Nat), substF (liftS c) f = liftFormula c f := by
  intro f
  induction f with
  | bottom => intro _; rfl
  | atom p ts => intro c; simp only [substF, liftFormula, substTs_liftS]
  | eq t u => intro c; simp only [substF, liftFormula, substT_liftS]
  | impl a b iha ihb => intro c; simp only [substF, liftFormula, iha, ihb]
  | and a b iha ihb => intro c; simp only [substF, liftFormula, iha, ihb]
  | or a b iha ihb => intro c; simp only [substF, liftFormula, iha, ihb]
  | «forall» a ih => intro c; simp only [substF, liftFormula, upS_liftS, ih]
  | ex a ih => intro c; simp only [substF, liftFormula, upS_liftS, ih]

theorem substF_singleS : ∀ (f : Formula) (v : Nat) (s : Term),
    substF (singleS v s) f = substFormula v s f := by
  intro f
  induction f with
  | bottom => intro _ _; rfl
  | atom p ts => intro v s; simp only [substF, substFormula, substTs_singleS]
  | eq t u => intro v s; simp only [substF, substFormula, substT_singleS]
  | impl a b iha ihb => intro v s; simp only [substF, substFormula, iha, ihb]
  | and a b iha ihb => intro v s; simp only [substF, substFormula, iha, ihb]
  | or a b iha ihb => intro v s; simp only [substF, substFormula, iha, ihb]
  | «forall» a ih => intro v s; simp only [substF, substFormula, upS_singleS, ih]
  | ex a ih => intro v s; simp only [substF, substFormula, upS_singleS, ih]

theorem substF_comp : ∀ (f : Formula) (ρ τ : Subst),
    substF ρ (substF τ f) = substF (compS ρ τ) f := by
  intro f
  induction f with
  | bottom => intro _ _; rfl
  | atom p ts => intro ρ τ; simp only [substF, substTs_comp]
  | eq t u => intro ρ τ; simp only [substF, substT_comp]
  | impl a b iha ihb => intro ρ τ; simp only [substF, iha, ihb]
  | and a b iha ihb => intro ρ τ; simp only [substF, iha, ihb]
  | or a b iha ihb => intro ρ τ; simp only [substF, iha, ihb]
  | «forall» a ih => intro ρ τ; simp only [substF, ih, upS_compS]
  | ex a ih => intro ρ τ; simp only [substF, ih, upS_compS]

/-! ## 5 · Los corolarios que usa L2 -/

mutual
theorem substT_var_id : ∀ t : Term, substT Term.var t = t := by
  intro t
  cases t with
  | var n => rfl
  | func f ts => simp only [substT]; exact congrArg _ (substTs_var_id ts)

theorem substTs_var_id : ∀ ts : List Term, substTs Term.var ts = ts := by
  intro ts
  cases ts with
  | nil => rfl
  | cons t ts' =>
      simp only [substTs, List.cons.injEq]
      exact ⟨substT_var_id t, substTs_var_id ts'⟩
end

/-- `upS` fija la sustitución identidad. -/
theorem upS_var : upS (Term.var : Subst) = Term.var := by
  funext n
  cases n with
  | zero => rfl
  | succ m => simp [upS, liftTerm, Nat.not_lt_zero]

/-- La sustitución identidad no hace nada. -/
theorem substF_id : ∀ f : Formula, substF Term.var f = f := by
  intro f
  induction f with
  | bottom => rfl
  | atom p ts => simp only [substF, substTs_var_id]
  | eq t u => simp only [substF, substT_var_id]
  | impl a b iha ihb => simp only [substF, iha, ihb]
  | and a b iha ihb => simp only [substF, iha, ihb]
  | or a b iha ihb => simp only [substF, iha, ihb]
  | «forall» a ih => simp only [substF, upS_var, ih]
  | ex a ih => simp only [substF, upS_var, ih]

/-- ⭐ **Levantar y luego sustituir con `t` en el índice 0 es sustituir sin `t`.** Es la
    identidad que hace que el contexto levantado de `intro_forall` se comporte. -/
theorem substF_lift_consS (ρ : Subst) (t : Term) (f : Formula) :
    substF (consS t ρ) (liftFormula 0 f) = substF ρ f := by
  have h : compS (consS t ρ) (liftS 0) = ρ := by
    funext n
    simp [compS, liftS, consS, substT, Nat.not_lt_zero]
  rw [← substF_liftS f 0, substF_comp, h]

/-- ⭐⭐ **La identidad clave de `intro_forall`**: entrar bajo la ligadura y luego
    instanciar con `t` es sustituir con `t` en cabeza. -/
theorem substFormula_upS (ρ : Subst) (t : Term) (f : Formula) :
    substFormula 0 t (substF (upS ρ) f) = substF (consS t ρ) f := by
  rw [← substF_singleS _ 0 t, substF_comp]
  congr 1
  funext n
  cases n with
  | zero => simp [compS, consS, upS, substT, singleS]
  | succ m =>
      simp only [compS, consS, upS]
      rw [← substT_liftS 0 (ρ m), substT_comp]
      have : compS (singleS 0 t) (liftS 0) = Term.var := by
        funext k
        simp [compS, liftS, singleS, substT, Nat.not_lt_zero,
          show k + 1 > 0 by omega]
      rw [this]
      exact substT_var_id (ρ m)

/-- `substF` conmuta con el levantamiento del contexto. -/
theorem substF_upS_lift (ρ : Subst) (f : Formula) :
    substF (upS ρ) (liftFormula 0 f) = liftFormula 0 (substF ρ f) := by
  rw [← substF_liftS f 0, substF_comp, ← substF_liftS (substF ρ f) 0, substF_comp]
  congr 1
  exact compS_upS_liftS ρ

end PeanoRF.Calculus
