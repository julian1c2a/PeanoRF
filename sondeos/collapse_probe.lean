-- ════════════════════════════════════════════════════════════════════════════
-- SONDEO 2026-09-18 (e) — ¿conmuta el COLAPSO de símbolos ajenos con lift y subst?
--
-- El obstáculo de H3ter: `Term` es genérica, y `elim_forall` instancia con símbolos que no
-- son del lenguaje de Q⁺⁺ (`sondeos/junk_probe.lean`). La ruta cara sería un cálculo
-- paralelo `DerivesL`. La barata, si conmuta: TRANSFORMAR la derivación en vez de
-- restringirla —
--
--     derivesI_collapse : Γ ⊢ᵢ f  →  Γ.map (collapseF L) ⊢ᵢ collapseF L f
--
-- por inducción sobre los 18 constructores, igual que `derivesI_subst`. En `elim_forall`,
-- una instanciación con basura `t` pasa a ser una con `collapseT L t`, que SÍ es del
-- lenguaje; y `collapseF L` deja fijos los axiomas de `coreAxioms`.
--
-- ⚠️ Ese lema necesita DOS conmutaciones, y son la única incógnita. Este sondeo las mide.
-- Si salen, la ruta está abierta; si no, se sabe antes de escribir el lema grande.
--
-- ⭐ Se parametriza por la signatura `L : String → Bool` en vez de clavarla a Q⁺⁺: las
-- conmutaciones no dependen de QUÉ símbolos se conserven, y así el resultado vale para
-- cualquier lenguaje. Lo único que se usa del reemplazo es que sea CERRADO (`zero` no
-- tiene argumentos, luego lift y subst lo dejan igual por `rfl`).
-- ════════════════════════════════════════════════════════════════════════════
import PeanoRF.HA.Numerals
open FOL ROBINSON_PlusPlus.Minimal.Axioms

namespace PeanoRF.Collapse

set_option autoImplicit false

/-! ## El colapso -/

mutual
/-- Todo símbolo fuera de la signatura `L` colapsa a `zero`. Las variables no se tocan —
    y eso es lo que hace que conmute con la sustitución. -/
def collapseT (L : String → Bool) : Term → Term
  | .var n     => .var n
  | .func s ts => if L s then .func s (collapseTs L ts) else zero

def collapseTs (L : String → Bool) : List Term → List Term
  | []      => []
  | t :: ts => collapseT L t :: collapseTs L ts
end

/-- En las fórmulas sólo se colapsan los TÉRMINOS. Un predicado ajeno no da problema: la
    barra de un átomo es su derivabilidad, sin testigo — el obstáculo era la instanciación
    de `∀`/`∃` con términos ajenos. -/
def collapseF (L : String → Bool) : Formula → Formula
  | .bottom    => .bottom
  | .atom p ts => .atom p (collapseTs L ts)
  | .eq t u    => .eq (collapseT L t) (collapseT L u)
  | .impl a b  => .impl (collapseF L a) (collapseF L b)
  | .forall a  => .forall (collapseF L a)
  | .and a b   => .and (collapseF L a) (collapseF L b)
  | .or a b    => .or (collapseF L a) (collapseF L b)
  | .ex a      => .ex (collapseF L a)

/-! ## 1 · El colapso conmuta con el LEVANTAMIENTO -/

mutual
theorem collapseT_lift (L : String → Bool) : ∀ (c : Nat) (t : Term),
    collapseT L (liftTerm c t) = liftTerm c (collapseT L t) := by
  intro c t
  cases t with
  | var n => by_cases h : n < c <;> simp [collapseT, liftTerm, h]
  | func s ts =>
      by_cases h : L s
      · simp only [liftTerm, collapseT, if_pos h]
        exact congrArg _ (collapseTs_lift L c ts)
      · simp [liftTerm, collapseT, if_neg h, zero, liftTerms]

theorem collapseTs_lift (L : String → Bool) : ∀ (c : Nat) (ts : List Term),
    collapseTs L (liftTerms c ts) = liftTerms c (collapseTs L ts) := by
  intro c ts
  cases ts with
  | nil => rfl
  | cons t ts' =>
      simp only [liftTerms, collapseTs, List.cons.injEq]
      exact ⟨collapseT_lift L c t, collapseTs_lift L c ts'⟩
end

theorem collapseF_lift (L : String → Bool) : ∀ (f : Formula) (c : Nat),
    collapseF L (liftFormula c f) = liftFormula c (collapseF L f) := by
  intro f
  induction f with
  | bottom => intro _; rfl
  | atom p ts => intro c; simp only [liftFormula, collapseF, collapseTs_lift]
  | eq t u => intro c; simp only [liftFormula, collapseF, collapseT_lift]
  | impl a b iha ihb => intro c; simp only [liftFormula, collapseF, iha, ihb]
  | and a b iha ihb => intro c; simp only [liftFormula, collapseF, iha, ihb]
  | or a b iha ihb => intro c; simp only [liftFormula, collapseF, iha, ihb]
  | «forall» a ih => intro c; simp only [liftFormula, collapseF, ih]
  | ex a ih => intro c; simp only [liftFormula, collapseF, ih]

/-! ## 2 · El colapso conmuta con la SUSTITUCIÓN -/

mutual
theorem collapseT_subst (L : String → Bool) : ∀ (v : Nat) (s t : Term),
    collapseT L (substTerm v s t) = substTerm v (collapseT L s) (collapseT L t) := by
  intro v s t
  cases t with
  | var n =>
      by_cases h1 : n = v
      · simp [collapseT, substTerm, h1]
      · by_cases h2 : n > v <;> simp [collapseT, substTerm, h1, h2]
  | func c ts =>
      by_cases h : L c
      · simp only [substTerm, collapseT, if_pos h]
        exact congrArg _ (collapseTs_subst L v s ts)
      · simp [substTerm, collapseT, if_neg h, zero, substTerms]

theorem collapseTs_subst (L : String → Bool) : ∀ (v : Nat) (s : Term) (ts : List Term),
    collapseTs L (substTerms v s ts) = substTerms v (collapseT L s) (collapseTs L ts) := by
  intro v s ts
  cases ts with
  | nil => rfl
  | cons t ts' =>
      simp only [substTerms, collapseTs, List.cons.injEq]
      exact ⟨collapseT_subst L v s t, collapseTs_subst L v s ts'⟩
end

/-- ⭐⭐ **La conmutación que decide la ruta.** El caso `∀`/`∃` es el que podía fallar: ahí
    la sustitución entra bajo la ligadura como `substFormula (v+1) (liftTerm 0 s)`, y hace
    falta que el colapso conmute también con ese levantamiento. -/
theorem collapseF_subst (L : String → Bool) : ∀ (f : Formula) (v : Nat) (s : Term),
    collapseF L (substFormula v s f) = substFormula v (collapseT L s) (collapseF L f) := by
  intro f
  induction f with
  | bottom => intro _ _; rfl
  | atom p ts => intro v s; simp only [substFormula, collapseF, collapseTs_subst]
  | eq t u => intro v s; simp only [substFormula, collapseF, collapseT_subst]
  | impl a b iha ihb => intro v s; simp only [substFormula, collapseF, iha, ihb]
  | and a b iha ihb => intro v s; simp only [substFormula, collapseF, iha, ihb]
  | or a b iha ihb => intro v s; simp only [substFormula, collapseF, iha, ihb]
  | «forall» a ih =>
      intro v s
      simp only [substFormula, collapseF, ih, collapseT_lift]
  | ex a ih =>
      intro v s
      simp only [substFormula, collapseF, ih, collapseT_lift]

/-! ## 3 · Y lo que el lema grande necesitará además: el colapso FIJA el lenguaje -/

/-- Un numeral es del lenguaje, luego el colapso lo deja igual. Es el caso testigo de que
    `collapseF` fija los axiomas de `coreAxioms`. -/
theorem collapseT_numeralM (L : String → Bool)
    (hz : L zero_sym = true) (hs : L succ_sym = true) :
    ∀ n : Nat, collapseT L (numeralM n) = numeralM n := by
  intro n
  induction n with
  | zero => simp [collapseT, numeralM, zero, hz, collapseTs]
  | succ k ih =>
      simp only [numeralM, succ, collapseT, if_pos hs, collapseTs, ih]

end PeanoRF.Collapse

#print axioms PeanoRF.Collapse.collapseF_lift
#print axioms PeanoRF.Collapse.collapseF_subst
#print axioms PeanoRF.Collapse.collapseT_numeralM
