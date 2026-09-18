-- SPIKE 2026-09-18 — ¿es BARATO portar la capa de numerales a `⊢ᵢ`?
-- Se porta `numeral_add`, que aguas arriba va por INDUCCIÓN META (no necesita
-- `ax_induction`), usando `numeralM` de la capa Minimal —que ya importamos— y nuestros
-- propios lemas de igualdad.
import PeanoRF.HA.Arith
open FOL PeanoRF.Calculus ROBINSON_PlusPlus.Minimal.Axioms
namespace PeanoRF.HA
set_option autoImplicit false

theorem numeralI_add (a b : Nat) :
    ctx [] ⊢ᵢ (add (numeralM a) (numeralM b) =eq numeralM (a + b)) := by
  induction b with
  | zero =>
      have h4 : ctx [] ⊢ᵢ ax4_add_zero := ax' (by simp [axioms])
      have h := specI h4 (numeralM a)
      simp [substFormula, substTerm, substTerms, add, zero] at h
      exact h
  | succ k ih =>
      have h5' : ctx [] ⊢ᵢ ax5_add_succ := ax' (by simp [axioms])
      have h5 : ctx [] ⊢ᵢ
          (add (numeralM a) (succ (numeralM k)) =eq succ (add (numeralM a) (numeralM k))) := by
        have hh := specI (specI h5' (numeralM a)) (numeralM k)
        simp [substFormula, substTerm, substTerms, add, succ, zero,
              FOL.substTerm_liftTerm] at hh
        exact hh
      exact eqI_trans h5 (eqI_congr_succ ih)

end PeanoRF.HA
#print axioms PeanoRF.HA.numeralI_add
