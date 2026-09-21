/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.Calculus.DerivesI

/-! # Igualdad sobre `⊢ᵢ`

  Simetría, transitividad y congruencia del sucesor, **reprobadas en el cálculo
  intuicionista**. Aguas arriba existen (`FOL.derive_eq_symm`, `FOL.derive_eq_trans`,
  `Minimal.Axioms.eq_congr_succ`) pero están enunciadas sobre `⊢`, que es HERRAMIENTA
  (ADR-017): sus teoremas no bajan a `⊢ᵢ`, sólo suben.

  Ése es el coste real de la migración, y es este fichero: **tres lemas**. Las pruebas son
  las de aguas arriba con los constructores renombrados — `subst` y `refl` existen igual en
  `⊢ᵢ`, y ninguna usaba lógica clásica ni ω.
-/

namespace PeanoRF.Calculus

open FOL

set_option autoImplicit false

variable {Γ : List Formula}

/-- Reflexividad. -/
theorem eqI_refl (t : Term) : Γ ⊢ᵢ (Formula.eq t t) := Derivesᵢ.refl Γ t

/-- Simetría. La `f` testigo es `#0 = t₁↑`: sustituyendo `t₁` da `t₁ = t₁` (que es `refl`)
    y sustituyendo `t₂` da `t₂ = t₁`. -/
theorem eqI_symm {t₁ t₂ : Term} (h : Γ ⊢ᵢ (Formula.eq t₁ t₂)) : Γ ⊢ᵢ (Formula.eq t₂ t₁) := by
  have hS1 : substFormula 0 t₁ (Formula.eq (.var 0) (liftTerm 0 t₁)) = Formula.eq t₁ t₁ := by
    change Formula.eq (substTerm 0 t₁ (.var 0)) (substTerm 0 t₁ (liftTerm 0 t₁))
         = Formula.eq t₁ t₁
    rw [substTerm_liftTerm t₁ 0 t₁]
    rfl
  have hS2 : substFormula 0 t₂ (Formula.eq (.var 0) (liftTerm 0 t₁)) = Formula.eq t₂ t₁ := by
    change Formula.eq (substTerm 0 t₂ (.var 0)) (substTerm 0 t₂ (liftTerm 0 t₁))
         = Formula.eq t₂ t₁
    rw [substTerm_liftTerm t₁ 0 t₂]
    rfl
  have hbase : Γ ⊢ᵢ substFormula 0 t₁ (Formula.eq (.var 0) (liftTerm 0 t₁)) := by
    rw [hS1]; exact Derivesᵢ.refl Γ t₁
  have := Derivesᵢ.subst Γ t₁ t₂ (Formula.eq (.var 0) (liftTerm 0 t₁)) h hbase
  rwa [hS2] at this

/-- Transitividad. Testigo `t₁↑ = #0`. -/
theorem eqI_trans {t₁ t₂ t₃ : Term}
    (h12 : Γ ⊢ᵢ (Formula.eq t₁ t₂)) (h23 : Γ ⊢ᵢ (Formula.eq t₂ t₃)) :
    Γ ⊢ᵢ (Formula.eq t₁ t₃) := by
  have hS2 : substFormula 0 t₂ (Formula.eq (liftTerm 0 t₁) (.var 0)) = Formula.eq t₁ t₂ := by
    change Formula.eq (substTerm 0 t₂ (liftTerm 0 t₁)) (substTerm 0 t₂ (.var 0))
         = Formula.eq t₁ t₂
    rw [substTerm_liftTerm t₁ 0 t₂]
    rfl
  have hS3 : substFormula 0 t₃ (Formula.eq (liftTerm 0 t₁) (.var 0)) = Formula.eq t₁ t₃ := by
    change Formula.eq (substTerm 0 t₃ (liftTerm 0 t₁)) (substTerm 0 t₃ (.var 0))
         = Formula.eq t₁ t₃
    rw [substTerm_liftTerm t₁ 0 t₃]
    rfl
  have hbase : Γ ⊢ᵢ substFormula 0 t₂ (Formula.eq (liftTerm 0 t₁) (.var 0)) := by
    rw [hS2]; exact h12
  have := Derivesᵢ.subst Γ t₂ t₃ (Formula.eq (liftTerm 0 t₁) (.var 0)) h23 hbase
  rwa [hS3] at this

/-- Congruencia del sucesor. Testigo `σ(t₁↑) = σ#0`. -/
theorem eqI_congr_succ {t₁ t₂ : Term} (h : Γ ⊢ᵢ (Formula.eq t₁ t₂)) :
    Γ ⊢ᵢ (Formula.eq (ROBINSON_PlusPlus.Minimal.Axioms.succ t₁)
                     (ROBINSON_PlusPlus.Minimal.Axioms.succ t₂)) := by
  open ROBINSON_PlusPlus.Minimal.Axioms in
  have hS1 : substFormula 0 t₁ (Formula.eq (succ (liftTerm 0 t₁)) (succ (.var 0)))
           = Formula.eq (succ t₁) (succ t₁) := by
    change Formula.eq (succ (substTerm 0 t₁ (liftTerm 0 t₁))) (succ (substTerm 0 t₁ (.var 0)))
         = Formula.eq (succ t₁) (succ t₁)
    rw [substTerm_liftTerm t₁ 0 t₁]
    rfl
  open ROBINSON_PlusPlus.Minimal.Axioms in
  have hS2 : substFormula 0 t₂ (Formula.eq (succ (liftTerm 0 t₁)) (succ (.var 0)))
           = Formula.eq (succ t₁) (succ t₂) := by
    change Formula.eq (succ (substTerm 0 t₂ (liftTerm 0 t₁))) (succ (substTerm 0 t₂ (.var 0)))
         = Formula.eq (succ t₁) (succ t₂)
    rw [substTerm_liftTerm t₁ 0 t₂]
    rfl
  open ROBINSON_PlusPlus.Minimal.Axioms in
  have hbase : Γ ⊢ᵢ substFormula 0 t₁ (Formula.eq (succ (liftTerm 0 t₁)) (succ (.var 0))) := by
    rw [hS1]; exact Derivesᵢ.refl Γ _
  open ROBINSON_PlusPlus.Minimal.Axioms in
  have := Derivesᵢ.subst Γ t₁ t₂ (Formula.eq (succ (liftTerm 0 t₁)) (succ (.var 0))) h hbase
  rwa [hS2] at this

/-- Especialización de un `∀` con un término (alias de `elim_forall`, para leer igual que
    el `spec` de ROBINSON_PlusPlus). -/
theorem specI {A : Formula} (h : Γ ⊢ᵢ Formula.forall A) (t : Term) :
    Γ ⊢ᵢ substFormula 0 t A :=
  Derivesᵢ.elim_forall Γ A t h



/-! ## Congruencia GENÉRICA por símbolo de función

    `eqI_congr_succ` está escrita a mano para `succ`. Con tres símbolos binarios en el
    lenguaje de Q⁺⁺ (`add`, `mul`, `pow`) repetir el patrón seis veces sería tonto: las
    operaciones son `Term.func s […]`, así que **una sola prueba por aridad** las cubre
    todas, presentes y futuras. -/

/-- Congruencia para un símbolo UNARIO. Testigo `f(t₁↑) = f(#0)`.

    🏗️ **ANDAMIO**: hoy sólo se usan las binarias (`add`, `mul`, `pow`). Ésta existe
    porque la familia se hizo **por aridad y no por símbolo**, a propósito: `σ`, `√`, `τ`,
    `%₂`, `/₂` y `Π_p` son unarios y la van a necesitar. -/
theorem eqI_congr_fun1 (s : String) {t₁ t₂ : Term} (h : Γ ⊢ᵢ (Formula.eq t₁ t₂)) :
    Γ ⊢ᵢ (Formula.eq (Term.func s [t₁]) (Term.func s [t₂])) := by
  have hS1 : substFormula 0 t₁ (Formula.eq (Term.func s [liftTerm 0 t₁])
                                            (Term.func s [Term.var 0]))
           = Formula.eq (Term.func s [t₁]) (Term.func s [t₁]) := by
    change Formula.eq (Term.func s [substTerm 0 t₁ (liftTerm 0 t₁)])
                      (Term.func s [substTerm 0 t₁ (Term.var 0)])
         = Formula.eq (Term.func s [t₁]) (Term.func s [t₁])
    rw [substTerm_liftTerm t₁ 0 t₁]
    rfl
  have hS2 : substFormula 0 t₂ (Formula.eq (Term.func s [liftTerm 0 t₁])
                                            (Term.func s [Term.var 0]))
           = Formula.eq (Term.func s [t₁]) (Term.func s [t₂]) := by
    change Formula.eq (Term.func s [substTerm 0 t₂ (liftTerm 0 t₁)])
                      (Term.func s [substTerm 0 t₂ (Term.var 0)])
         = Formula.eq (Term.func s [t₁]) (Term.func s [t₂])
    rw [substTerm_liftTerm t₁ 0 t₂]
    rfl
  have hbase : Γ ⊢ᵢ substFormula 0 t₁ (Formula.eq (Term.func s [liftTerm 0 t₁])
                                                   (Term.func s [Term.var 0])) := by
    rw [hS1]; exact Derivesᵢ.refl Γ _
  have := Derivesᵢ.subst Γ t₁ t₂
    (Formula.eq (Term.func s [liftTerm 0 t₁]) (Term.func s [Term.var 0])) h hbase
  rwa [hS2] at this

/-- Congruencia en el argumento IZQUIERDO de un símbolo binario. -/
theorem eqI_congr_fun2_l (s : String) {t₁ t₂ : Term} (u : Term)
    (h : Γ ⊢ᵢ (Formula.eq t₁ t₂)) :
    Γ ⊢ᵢ (Formula.eq (Term.func s [t₁, u]) (Term.func s [t₂, u])) := by
  have hS1 : substFormula 0 t₁ (Formula.eq (Term.func s [liftTerm 0 t₁, liftTerm 0 u])
                                            (Term.func s [Term.var 0, liftTerm 0 u]))
           = Formula.eq (Term.func s [t₁, u]) (Term.func s [t₁, u]) := by
    change Formula.eq (Term.func s [substTerm 0 t₁ (liftTerm 0 t₁),
                                    substTerm 0 t₁ (liftTerm 0 u)])
                      (Term.func s [substTerm 0 t₁ (Term.var 0),
                                    substTerm 0 t₁ (liftTerm 0 u)])
         = Formula.eq (Term.func s [t₁, u]) (Term.func s [t₁, u])
    rw [substTerm_liftTerm t₁ 0 t₁, substTerm_liftTerm u 0 t₁]
    rfl
  have hS2 : substFormula 0 t₂ (Formula.eq (Term.func s [liftTerm 0 t₁, liftTerm 0 u])
                                            (Term.func s [Term.var 0, liftTerm 0 u]))
           = Formula.eq (Term.func s [t₁, u]) (Term.func s [t₂, u]) := by
    change Formula.eq (Term.func s [substTerm 0 t₂ (liftTerm 0 t₁),
                                    substTerm 0 t₂ (liftTerm 0 u)])
                      (Term.func s [substTerm 0 t₂ (Term.var 0),
                                    substTerm 0 t₂ (liftTerm 0 u)])
         = Formula.eq (Term.func s [t₁, u]) (Term.func s [t₂, u])
    rw [substTerm_liftTerm t₁ 0 t₂, substTerm_liftTerm u 0 t₂]
    rfl
  have hbase : Γ ⊢ᵢ substFormula 0 t₁
      (Formula.eq (Term.func s [liftTerm 0 t₁, liftTerm 0 u])
                  (Term.func s [Term.var 0, liftTerm 0 u])) := by
    rw [hS1]; exact Derivesᵢ.refl Γ _
  have := Derivesᵢ.subst Γ t₁ t₂
    (Formula.eq (Term.func s [liftTerm 0 t₁, liftTerm 0 u])
                (Term.func s [Term.var 0, liftTerm 0 u])) h hbase
  rwa [hS2] at this

/-- Congruencia en el argumento DERECHO de un símbolo binario. -/
theorem eqI_congr_fun2_r (s : String) (t : Term) {u₁ u₂ : Term}
    (h : Γ ⊢ᵢ (Formula.eq u₁ u₂)) :
    Γ ⊢ᵢ (Formula.eq (Term.func s [t, u₁]) (Term.func s [t, u₂])) := by
  have hS1 : substFormula 0 u₁ (Formula.eq (Term.func s [liftTerm 0 t, liftTerm 0 u₁])
                                            (Term.func s [liftTerm 0 t, Term.var 0]))
           = Formula.eq (Term.func s [t, u₁]) (Term.func s [t, u₁]) := by
    change Formula.eq (Term.func s [substTerm 0 u₁ (liftTerm 0 t),
                                    substTerm 0 u₁ (liftTerm 0 u₁)])
                      (Term.func s [substTerm 0 u₁ (liftTerm 0 t),
                                    substTerm 0 u₁ (Term.var 0)])
         = Formula.eq (Term.func s [t, u₁]) (Term.func s [t, u₁])
    rw [substTerm_liftTerm t 0 u₁, substTerm_liftTerm u₁ 0 u₁]
    rfl
  have hS2 : substFormula 0 u₂ (Formula.eq (Term.func s [liftTerm 0 t, liftTerm 0 u₁])
                                            (Term.func s [liftTerm 0 t, Term.var 0]))
           = Formula.eq (Term.func s [t, u₁]) (Term.func s [t, u₂]) := by
    change Formula.eq (Term.func s [substTerm 0 u₂ (liftTerm 0 t),
                                    substTerm 0 u₂ (liftTerm 0 u₁)])
                      (Term.func s [substTerm 0 u₂ (liftTerm 0 t),
                                    substTerm 0 u₂ (Term.var 0)])
         = Formula.eq (Term.func s [t, u₁]) (Term.func s [t, u₂])
    rw [substTerm_liftTerm t 0 u₂, substTerm_liftTerm u₁ 0 u₂]
    rfl
  have hbase : Γ ⊢ᵢ substFormula 0 u₁
      (Formula.eq (Term.func s [liftTerm 0 t, liftTerm 0 u₁])
                  (Term.func s [liftTerm 0 t, Term.var 0])) := by
    rw [hS1]; exact Derivesᵢ.refl Γ _
  have := Derivesᵢ.subst Γ u₁ u₂
    (Formula.eq (Term.func s [liftTerm 0 t, liftTerm 0 u₁])
                (Term.func s [liftTerm 0 t, Term.var 0])) h hbase
  rwa [hS2] at this

/-- Congruencia en LOS DOS argumentos, componiendo por transitividad. -/
theorem eqI_congr_fun2 (s : String) {t₁ t₂ u₁ u₂ : Term}
    (h1 : Γ ⊢ᵢ (Formula.eq t₁ t₂)) (h2 : Γ ⊢ᵢ (Formula.eq u₁ u₂)) :
    Γ ⊢ᵢ (Formula.eq (Term.func s [t₁, u₁]) (Term.func s [t₂, u₂])) :=
  eqI_trans (eqI_congr_fun2_l s u₁ h1) (eqI_congr_fun2_r s t₂ h2)


/-! ## Reescritura dentro de un PREDICADO

    Las congruencias de arriba son para símbolos de FUNCIÓN: de `t₁ = t₂` sacan
    `f(t₁) = f(t₂)`. Para un predicado no hay ecuación que sacar — hay que **transportar la
    derivación**, que es lo que hace la regla `subst` directamente. Lo pide la etapa 3:
    decidido en el meta que `n < m`, se obtiene `⊢ᵢ n̄ < m̄` y hay que llevarlo a `⊢ᵢ t < u`
    sabiendo `⊢ᵢ t = n̄` y `⊢ᵢ u = m̄`. -/

/-- Reescritura en el argumento IZQUIERDO de un predicado binario. -/
theorem eqI_rw_atom2_l (p : String) {t₁ t₂ : Term} (u : Term)
    (h : Γ ⊢ᵢ (Formula.eq t₁ t₂)) (hb : Γ ⊢ᵢ Formula.atom p [t₁, u]) :
    Γ ⊢ᵢ Formula.atom p [t₂, u] := by
  have hS1 : substFormula 0 t₁ (Formula.atom p [Term.var 0, liftTerm 0 u])
           = Formula.atom p [t₁, u] := by
    change Formula.atom p [substTerm 0 t₁ (Term.var 0), substTerm 0 t₁ (liftTerm 0 u)]
         = Formula.atom p [t₁, u]
    rw [substTerm_liftTerm u 0 t₁]
    rfl
  have hS2 : substFormula 0 t₂ (Formula.atom p [Term.var 0, liftTerm 0 u])
           = Formula.atom p [t₂, u] := by
    change Formula.atom p [substTerm 0 t₂ (Term.var 0), substTerm 0 t₂ (liftTerm 0 u)]
         = Formula.atom p [t₂, u]
    rw [substTerm_liftTerm u 0 t₂]
    rfl
  have hbase : Γ ⊢ᵢ substFormula 0 t₁ (Formula.atom p [Term.var 0, liftTerm 0 u]) := by
    rw [hS1]; exact hb
  have := Derivesᵢ.subst Γ t₁ t₂ (Formula.atom p [Term.var 0, liftTerm 0 u]) h hbase
  rwa [hS2] at this

/-- Reescritura en el argumento DERECHO de un predicado binario. -/
theorem eqI_rw_atom2_r (p : String) (t : Term) {u₁ u₂ : Term}
    (h : Γ ⊢ᵢ (Formula.eq u₁ u₂)) (hb : Γ ⊢ᵢ Formula.atom p [t, u₁]) :
    Γ ⊢ᵢ Formula.atom p [t, u₂] := by
  have hS1 : substFormula 0 u₁ (Formula.atom p [liftTerm 0 t, Term.var 0])
           = Formula.atom p [t, u₁] := by
    change Formula.atom p [substTerm 0 u₁ (liftTerm 0 t), substTerm 0 u₁ (Term.var 0)]
         = Formula.atom p [t, u₁]
    rw [substTerm_liftTerm t 0 u₁]
    rfl
  have hS2 : substFormula 0 u₂ (Formula.atom p [liftTerm 0 t, Term.var 0])
           = Formula.atom p [t, u₂] := by
    change Formula.atom p [substTerm 0 u₂ (liftTerm 0 t), substTerm 0 u₂ (Term.var 0)]
         = Formula.atom p [t, u₂]
    rw [substTerm_liftTerm t 0 u₂]
    rfl
  have hbase : Γ ⊢ᵢ substFormula 0 u₁ (Formula.atom p [liftTerm 0 t, Term.var 0]) := by
    rw [hS1]; exact hb
  have := Derivesᵢ.subst Γ u₁ u₂ (Formula.atom p [liftTerm 0 t, Term.var 0]) h hbase
  rwa [hS2] at this

end PeanoRF.Calculus
