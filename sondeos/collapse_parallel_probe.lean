-- ════════════════════════════════════════════════════════════════════════════
-- SONDEO 2026-09-18 (g) — ¿cierra el `elim_forall` de L2 con el colapso DENTRO
-- del enunciado, y conmuta el colapso con la sustitución PARALELA?
--
-- La etapa 2 de H3ter quiere `Slash T D` con `D = ClosedQTerm`. El caso `elim_forall` de
-- L2 pide entonces `D (substT ρ t)` para un `t` ARBITRARIO — inalcanzable, porque `t`
-- puede llevar símbolos ajenos. `derivesI_collapse` no lo arregla por sí solo: actúa sobre
-- derivaciones enteras, y L2 por dentro no sabe que la derivación venga colapsada.
--
-- La forma (c): que L2 demuestre la barra de la instancia COLAPSADA —
--
--     slash_of_derives : Γ ⊢ᵢ f → ∀ ρ, (...) → Slash T D (collapseF L (substF ρ f))
--
-- y entonces la obligación pasa a ser `D (collapseT L (substT ρ t))`, que SÍ debería salir.
-- Este sondeo lo mide, y de paso la conmutación paralela que la forma (c) usa.
--
-- Q1 · ¿conmuta `collapseF` con `substF` (paralela)?
-- Q2 · `elim_forall`: ¿`ClosedQTerm (collapseT L (substT ρ t))` con ρ D-valuada?
-- Q3 · `intro_forall`: ¿`ClosedQTerm u → collapseT L u = u`?
-- ════════════════════════════════════════════════════════════════════════════
import PeanoRF.Calculus.Collapse
import PeanoRF.Calculus.Slash
import PeanoRF.HA.Numerals

open FOL ROBINSON_PlusPlus.Minimal.Axioms
open PeanoRF.Calculus PeanoRF.HA

namespace PeanoRF.SondeoG

set_option autoImplicit false

/-! ## Q1 · El colapso contra la sustitución PARALELA -/

/-- El colapso de una sustitución, punto a punto. -/
def collapseS (L : String → Bool) (ρ : Subst) : Subst := fun n => collapseT L (ρ n)

theorem collapseS_upS (L : String → Bool) (ρ : Subst) :
    collapseS L (upS ρ) = upS (collapseS L ρ) := by
  funext n
  cases n with
  | zero => rfl
  | succ m => exact collapseT_lift L 0 (ρ m)

mutual
theorem collapseT_substT (L : String → Bool) : ∀ (ρ : Subst) (t : Term),
    collapseT L (substT ρ t) = substT (collapseS L ρ) (collapseT L t) := by
  intro ρ t
  cases t with
  | var n => rfl
  | func s ts =>
      by_cases h : L s
      · simp only [substT, collapseT, if_pos h]
        exact congrArg _ (collapseTs_substTs L ρ ts)
      · simp [substT, collapseT, if_neg h, zero, substTs]

theorem collapseTs_substTs (L : String → Bool) : ∀ (ρ : Subst) (ts : List Term),
    collapseTs L (substTs ρ ts) = substTs (collapseS L ρ) (collapseTs L ts) := by
  intro ρ ts
  cases ts with
  | nil => rfl
  | cons t ts' =>
      simp only [substTs, collapseTs, List.cons.injEq]
      exact ⟨collapseT_substT L ρ t, collapseTs_substTs L ρ ts'⟩
end

theorem collapseF_substF (L : String → Bool) : ∀ (f : Formula) (ρ : Subst),
    collapseF L (substF ρ f) = substF (collapseS L ρ) (collapseF L f) := by
  intro f
  induction f with
  | bottom => intro _; rfl
  | atom p ts => intro ρ; simp only [substF, collapseF, collapseTs_substTs]
  | eq t u => intro ρ; simp only [substF, collapseF, collapseT_substT]
  | impl a b iha ihb => intro ρ; simp only [substF, collapseF, iha, ihb]
  | and a b iha ihb => intro ρ; simp only [substF, collapseF, iha, ihb]
  | or a b iha ihb => intro ρ; simp only [substF, collapseF, iha, ihb]
  | «forall» a ih => intro ρ; simp only [substF, collapseF, ih, collapseS_upS]
  | ex a ih => intro ρ; simp only [substF, collapseF, ih, collapseS_upS]

/-! ## Q2 · La obligación de `elim_forall` — y el hallazgo de la ARIDAD

    `D = ClosedQTerm`. Si `ρ` toma valores en `D`, ¿está `collapseT L (substT ρ t)` en `D`
    para un `t` ARBITRARIO? Con la signatura tal y como `collapseT` la toma hoy —un
    predicado sobre el NOMBRE del símbolo, `L : String → Bool`— **NO**.

    ⚠️ Aquí NO se puede escribir `∧` ni `∨`: `open FOL` las tiene tomadas por la
    conjunción y la disyunción de `FormulaG`. Leerlas está bien; escribirlas, no. -/

/-- La signatura de Q⁺⁺ tal y como `collapseT` la toma hoy: sólo el nombre del símbolo. -/
def LQ (s : String) : Bool :=
  s == zero_sym || s == succ_sym || s == add_sym || s == mul_sym || s == pow_sym

/-- La signatura CON ARIDAD, que es lo que el dominio `ClosedQTerm` exige de verdad. -/
def LQ2 (s : String) (n : Nat) : Bool :=
  (s == zero_sym && n == 0) || (s == succ_sym && n == 1) ||
  ((s == add_sym || s == mul_sym || s == pow_sym) && n == 2)

mutual
def collapseT2 (L : String → Nat → Bool) : Term → Term
  | .var n     => .var n
  | .func s ts => if L s ts.length then .func s (collapseTs2 L ts) else zero

def collapseTs2 (L : String → Nat → Bool) : List Term → List Term
  | []      => []
  | t :: ts => collapseT2 L t :: collapseTs2 L ts
end

theorem collapseTs2_length (L : String → Nat → Bool) :
    ∀ ts : List Term, (collapseTs2 L ts).length = ts.length := by
  intro ts
  induction ts with
  | nil => rfl
  | cons t ts' ih => simp only [collapseTs2, List.length_cons, ih]

theorem substTs_length : ∀ (ρ : Subst) (ts : List Term),
    (substTs ρ ts).length = ts.length := by
  intro ρ ts
  induction ts with
  | nil => rfl
  | cons t ts' ih => simp only [substTs, List.length_cons, ih]

/-! ### Q3 · El colapso FIJA el dominio (lo que pide `intro_forall`) -/

theorem collapseT2_fix : ∀ {u : Term}, ClosedQTerm u → collapseT2 LQ2 u = u := by
  intro u h
  induction h with
  | zero =>
      have hL : LQ2 zero_sym 0 = true := by decide
      simp only [zero, collapseT2, List.length_nil, if_pos hL, collapseTs2]
  | succ a _ ih =>
      have hL : LQ2 succ_sym 1 = true := by decide
      simp only [succ, collapseT2, List.length_cons, List.length_nil, if_pos hL,
        collapseTs2, ih]
  | add a b _ _ iha ihb =>
      have hL : LQ2 add_sym 2 = true := by decide
      simp only [add, collapseT2, List.length_cons, List.length_nil, if_pos hL,
        collapseTs2, iha, ihb]
  | mul a b _ _ iha ihb =>
      have hL : LQ2 mul_sym 2 = true := by decide
      simp only [mul, collapseT2, List.length_cons, List.length_nil, if_pos hL,
        collapseTs2, iha, ihb]
  | pow a b _ _ iha ihb =>
      have hL : LQ2 pow_sym 2 = true := by decide
      simp only [pow, collapseT2, List.length_cons, List.length_nil, if_pos hL,
        collapseTs2, iha, ihb]

/-! ### ⛔ El contraejemplo: la signatura sin aridad NO basta -/

/-- `+` aplicado a UN argumento es un término legítimo de la sintaxis, es cerrado y lleva
    sólo símbolos de Q⁺⁺ — pero **no es un `ClosedQTerm`**, porque los constructores de
    `ClosedQTerm` fijan también la ARIDAD. -/
theorem contraejemplo_aridad : ¬ ClosedQTerm (Term.func add_sym [zero]) := by
  intro h
  have heq := collapseT2_fix h
  have hL : ¬ (LQ2 add_sym ([zero] : List Term).length = true) := by decide
  rw [collapseT2, if_neg hL] at heq
  simp only [zero] at heq
  injection heq with h1 _
  exact absurd h1 (by decide)

/-- Y el colapso de hoy no lo crea: lo **conserva**, porque `LQ` no mira la aridad. -/
theorem contraejemplo_colapso :
    collapseT LQ (Term.func add_sym [zero]) = Term.func add_sym [zero] := by
  have h : LQ add_sym = true := by decide
  have hz : LQ zero_sym = true := by decide
  simp only [collapseT, if_pos h, zero, if_pos hz, collapseTs]

/-! ### Q2 · La obligación, con la signatura con aridad -/

/-- Un símbolo admitido por `LQ2`, con sus argumentos en el dominio, da un `ClosedQTerm`.
    Es donde la aridad hace TODO el trabajo. -/
theorem closed_of_LQ2 : ∀ (s : String) (args : List Term),
    LQ2 s args.length = true → (∀ t ∈ args, ClosedQTerm t) →
    ClosedQTerm (Term.func s args) := by
  intro s args hL hargs
  match args with
  | [] =>
      simp only [List.length_nil, LQ2, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq] at hL
      rcases hL with (⟨h1, _⟩ | ⟨_, h2⟩) | ⟨_, h2⟩
      · subst h1; exact ClosedQTerm.zero
      · exact absurd h2 (by decide)
      · exact absurd h2 (by decide)
  | [a] =>
      simp only [List.length_cons, List.length_nil, LQ2, Bool.or_eq_true,
        Bool.and_eq_true, beq_iff_eq] at hL
      rcases hL with (⟨_, h2⟩ | ⟨h1, _⟩) | ⟨_, h2⟩
      · exact absurd h2 (by decide)
      · subst h1; exact ClosedQTerm.succ a (hargs a (List.Mem.head _))
      · exact absurd h2 (by decide)
  | [a, b] =>
      simp only [List.length_cons, List.length_nil, LQ2, Bool.or_eq_true,
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
      simp only [List.length_cons, LQ2, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq] at hL
      rcases hL with (⟨_, h2⟩ | ⟨_, h2⟩) | ⟨_, h2⟩ <;> omega

mutual
/-- ⭐⭐ **LA MEDICIÓN.** Con `ρ` valuada en el dominio, el colapso de `substT ρ t` está en
    el dominio **para `t` arbitrario** — incluidos los términos con símbolos ajenos y con
    aridades erróneas. Es exactamente lo que `elim_forall` pedirá en la forma (c). -/
theorem q2_term (ρ : Subst) (hρ : ∀ n, ClosedQTerm (ρ n)) :
    ∀ t : Term, ClosedQTerm (collapseT2 LQ2 (substT ρ t)) := by
  intro t
  cases t with
  | var n =>
      show ClosedQTerm (collapseT2 LQ2 (ρ n))
      rw [collapseT2_fix (hρ n)]
      exact hρ n
  | func s ts =>
      have ih := q2_list ρ hρ ts
      show ClosedQTerm (collapseT2 LQ2 (Term.func s (substTs ρ ts)))
      rw [collapseT2]
      by_cases hL : LQ2 s (substTs ρ ts).length = true
      · rw [if_pos hL]
        refine closed_of_LQ2 s _ ?_ ih
        rw [collapseTs2_length]
        exact hL
      · rw [if_neg hL]
        exact ClosedQTerm.zero

theorem q2_list (ρ : Subst) (hρ : ∀ n, ClosedQTerm (ρ n)) :
    ∀ (ts : List Term), ∀ u ∈ collapseTs2 LQ2 (substTs ρ ts), ClosedQTerm u := by
  intro ts
  cases ts with
  | nil => intro u hu; cases hu
  | cons t ts' =>
      intro u hu
      show ClosedQTerm u
      rcases hu with _ | ⟨_, hu'⟩
      · exact q2_term ρ hρ t
      · exact q2_list ρ hρ ts' u hu'
end

end PeanoRF.SondeoG

#print axioms PeanoRF.SondeoG.collapseF_substF
#print axioms PeanoRF.SondeoG.collapseT2_fix
#print axioms PeanoRF.SondeoG.contraejemplo_aridad
#print axioms PeanoRF.SondeoG.contraejemplo_colapso
#print axioms PeanoRF.SondeoG.q2_term
