/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.HA.Order

/-! # El FRAGMENTO ARITMÉTICO de Q⁺⁺ — donde la DP de HA sí se alcanza

  ⛔ **Medido el 2026-09-21: `hNum` sobre el lenguaje COMPLETO es inalcanzable, y para `−`
  es directamente FALSA.**

  `hNum` dice que todo término anclado es demostrablemente igual a un numeral. Sobre los
  **trece** símbolos de Q⁺⁺ eso no se sostiene, y el caso límite lo decide solo:

  > `−` aparece **en UN único axioma de los 34** (`ax29_sub_witness`), y ese axioma lo
  > condiciona a `x ≤ y`: `∀x∀y. (x ≤ y) ⇒ (x + (y − x) = y)`.

  ⇒ Q⁺⁺ **no dice nada** de `5̄ − 7̄`. Ningún numeral es demostrablemente igual a ese término,
  y no por falta de ingenio: por falta de axioma. Y los otros siete no aritméticos (`√`, `/₂`,
  `%₂`, `::`, `##`, `Π_p`, y `τ` salvo por su recursión) están caracterizados por
  propiedades —desigualdades, ecuaciones condicionadas, recursiones sobre la estructura de
  lista— que **no permiten evaluar sin inducción en el objeto**, y la inducción que haría
  falta no es de Harrop.

  ## Lo que SÍ se alcanza, medido

  | | |
  |---|---|
  | **17 de los 34** axiomas son puramente aritméticos (`0`, `σ`, `+`, `*`, `^`) | `arithAxioms` |
  | y **son sentencias del lenguaje de los numerales** | `arithAxioms_sentences`, por `rfl` |
  | de los 17, **sólo DOS no son de Harrop** | `ax13_lt_def` y `ax19_lt_trichotomy` |
  | y **los dos ya están barrados** | `slash_ax13`, `slash_ax19` |

  ⭐ Y sobre este fragmento `hNum` **ya está demostrada**: es `closed_term_eq_numeral`, que
  habla exactamente de los cinco símbolos de los numerales. La capa `LQ` —que el 2026-09-21
  se etiquetó como ANDAMIO por no tener uso portante— resulta ser **la signatura de este
  fragmento**. El andamio era el camino.

  ⭐⭐ Y `hIn` **desaparece**: los dos axiomas que la pedían (`ax_L2_in_cons`,
  `ax_L3_in_concat`) no son aritméticos y no están aquí. El único que menciona `∈` es
  `ax_L1_in_nil` (`∀x. ¬(x ∈ 0)`, porque `nil` **es** `zero`), y ése es de Harrop.

  ⇒ **Queda una sola hipótesis: `hcon`** — 🏁 y desde el 2026-09-21, **ninguna**:
  `PeanoRF/HA/Model.lean` la descarga con un modelo estándar sobre `ℕ`, y
  `qDisjunctionProperty_arithTM_final` es **incondicional** (ADR-039).

  ⛔ Aquí ponía que `hcon` «no es una deuda: Gödel II dice que es el precio exacto y que no
  se puede pagar por dentro». **La segunda mitad es cierta y la conclusión era falsa**:
  Gödel II dice que HA no prueba su PROPIA consistencia, no que no la pruebe nadie. El pago
  no viene del cálculo, viene de la semántica.
-/

namespace PeanoRF.HA

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open PeanoRF.Calculus
open ROBINSON_PlusPlus.Full (inductionFormula)

set_option autoImplicit false

/-- ⛔ **EVIDENCIA**: la cifra, verificada por el kernel. -/
theorem arithAxioms_length : arithAxioms.length = 17 := rfl

/-- ⛔ **EVIDENCIA.** ⭐ **Son sentencias del lenguaje de los NUMERALES**: ni variables libres ni símbolos
    fuera de los cinco. Por `rfl`, no por argumento. -/
theorem arithAxioms_sentences :
    arithAxioms.map (fun g => collapseF LQ (substF zeroS g)) = arithAxioms := by rfl

/-- ⛔ **EVIDENCIA.** ⭐ **De los 17, sólo dos no son de Harrop** — y los dos ya están barrados. -/
theorem arithAxioms_hard :
    arithAxioms.filter (fun g => !isHarrop g) = [ax13_lt_def, ax19_lt_trichotomy] := by rfl

/-! ## 4 · ⭐ Anclado en `LQ` ⇒ `ClosedQTerm` — y con ello `hNum` para el fragmento

    `Grounded LQ` y `ClosedQTerm` describen lo mismo desde dos lados: el primero por
    CLAUSURAS (el colapso lo fija, ninguna sustitución lo toca), el segundo por
    CONSTRUCTORES. Ésta es la dirección que faltaba, y con ella `closed_term_eq_numeral`
    **es** `hNum` sobre el fragmento. -/

mutual
theorem closed_of_grounded : ∀ {t : Term}, Grounded LQ t → ClosedQTerm t := by
  intro t h
  cases t with
  | var n =>
      exfalso
      have hc : (zero : Term) = Term.var n := h.2 (fun _ => zero)
      rw [zero] at hc
      exact Term.noConfusion hc
  | func s ts =>
      by_cases hL : LQ s ts.length = true
      · have hall := h.1
        rw [collapseT, if_pos hL] at hall
        injection hall with _ hts
        refine closed_of_LQ s ts hL ?_
        exact closed_of_grounded_list ts hts (fun ρ => by
          have hx := h.2 ρ; simp only [substT] at hx; injection hx)
      · exfalso
        have hall := h.1
        rw [collapseT, if_neg hL, zero] at hall
        injection hall with h1 h2
        exact hL (by rw [← h1, ← h2]; decide)

theorem closed_of_grounded_list : ∀ (ts : List Term), collapseTs LQ ts = ts →
    (∀ ρ : Subst, substTs ρ ts = ts) → ∀ u, List.Mem u ts → ClosedQTerm u := by
  intro ts hc hs
  cases ts with
  | nil => intro u hu; cases hu
  | cons t ts0 =>
      rw [collapseTs] at hc
      injection hc with hc1 hc2
      intro u hu
      cases hu with
      | head =>
          exact closed_of_grounded ⟨hc1, fun ρ => by
            have hx := hs ρ; simp only [substTs] at hx; injection hx⟩
      | tail _ hu0 =>
          exact closed_of_grounded_list ts0 hc2 (fun ρ => by
            have hx := hs ρ; simp only [substTs] at hx; injection hx) u hu0
end

/-! ## 5 · 🏁🏁🏁 LA DP DEL FRAGMENTO — con UNA sola hipótesis

    Aquí se cierra. Sobre `ctxA`, con dominio `Grounded LQ`:

    | | |
    |---|---|
    | los 15 de Harrop | `slash_of_isHarrop`, sólo con la consistencia |
    | `ax13` y `ax19` | ya barrados, generalizados por contexto y signatura |
    | `hNum` | **NO es hipótesis: es `hNum_fragment`**, vía `closed_of_grounded` |
    | `hIn` | **no aparece**: sus dos axiomas no son aritméticos |
    | `hInd`, `hlift` | por instancia, `rfl` para una instancia concreta |

    ⇒ **Queda `hcon`, y nada más.** -/

/-- El contexto del fragmento: los 17 aritméticos más las instancias declaradas. -/
def ctxA (insts : List Formula) : List Formula :=
  arithAxioms ++ insts.map inductionFormula

theorem axA' {insts : List Formula} {g : Formula} (h : List.Mem g arithAxioms) :
    ctxA insts ⊢ᵢ g := Derivesᵢ.hyp _ _ (List.mem_append_left _ h)

/-- 🏗️ **ANDAMIO**: sin uso mientras `insts = []` sea el caso que se instancia. Es la
    puerta por la que entran las instancias de inducción al fragmento. -/
theorem indA {insts : List Formula} {φ : Formula} (h : List.Mem φ insts) :
    ctxA insts ⊢ᵢ inductionFormula φ :=
  Derivesᵢ.hyp _ _ (List.mem_append_right _ (List.mem_map_of_mem h))

/-- ⭐⭐ **`hNum` PARA EL FRAGMENTO — y no es hipótesis, es un TEOREMA.** Es
    `closed_term_eq_numeral` mirado a través de `closed_of_grounded`. -/
theorem hNum_fragment {insts : List Formula} : ∀ t : Term, Grounded LQ t →
    ∃ n : Nat, ctxA insts ⊢ᵢ (Formula.eq t (numeralM n)) :=
  fun _ ht => closed_term_eq_numeral (fun _ hg => axA' hg) (closed_of_grounded ht)

/-- Cada axioma del fragmento es punto fijo del colapso y la sustitución. -/
theorem arithAxioms_sentence (g : Formula) (hg : List.Mem g arithAxioms) :
    collapseF LQ (substF zeroS g) = g :=
  eq_of_map_self (f := fun g => collapseF LQ (substF zeroS g)) arithAxioms
    arithAxioms_sentences g hg

/-- ⭐⭐ **Los 17 axiomas del fragmento, barrados.** -/
theorem slash_arithAxioms {insts : List Formula}
    (hlift : (ctxA insts).map (liftFormula 0) = ctxA insts)
    (hcon : Not (ctxA insts ⊢ᵢ Formula.bottom)) :
    ∀ g, List.Mem g arithAxioms → Slash (ctxA insts) (Grounded LQ) g := by
  have hA : ∀ g, List.Mem g arithAxioms → ctxA insts ⊢ᵢ g := fun _ hg => axA' hg
  intro g hg
  simp only [arithAxioms] at hg
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax2_peano_succ_neq_zero rfl (axA' (List.Mem.head _))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax3_peano_succ_inj rfl (axA' (List.Mem.tail _ (List.Mem.head _)))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax4_add_zero rfl (axA' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax5_add_succ rfl (axA' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax6_add_comm rfl (axA' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax7_add_assoc rfl (axA' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax8_mul_zero rfl (axA' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax9_mul_succ rfl (axA' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax10_mul_comm rfl (axA' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax11_mul_assoc rfl (axA' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax12_mul_distrib rfl (axA' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_ax13 LQ (by decide) hA hlift hcon hNum_fragment
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax18_lt_irrefl rfl (axA' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_ax19 LQ hA hNum_fragment
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax_L1_in_nil rfl (axA' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax_pow_zero rfl (axA' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax_pow_succ rfl (axA' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))
  cases hg

/-- 🏁🏁🏁 **LA PROPIEDAD DE DISYUNCIÓN DEL FRAGMENTO ARITMÉTICO DE Q⁺⁺.**

    Con `hInd` y `hlift` reducidas a una condición por instancia, `hNum` demostrada y `hIn`
    desaparecida, **la única hipótesis de fondo que queda es la consistencia**. -/
theorem qDisjunctionPropertyA (insts : List Formula)
    (hlift : (ctxA insts).map (liftFormula 0) = ctxA insts)
    (hcon : Not (ctxA insts ⊢ᵢ Formula.bottom))
    (hInd : ∀ g, List.Mem g (insts.map inductionFormula) →
      Slash (ctxA insts) (Grounded LQ) (collapseF LQ (substF zeroS g)))
    {A B : Formula}
    (hAB : collapseF LQ (substF zeroS (Formula.or A B)) = Formula.or A B)
    (h : ctxA insts ⊢ᵢ Formula.or A B) :
    Or (ctxA insts ⊢ᵢ A) (ctxA insts ⊢ᵢ B) := by
  refine disjunction_property_of_slashed (ctxA insts) (Grounded LQ) LQ
    (fun _ hu => grounded_fix LQ hu) (grounded_collapse_subst LQ)
    zeroS (fun _ => grounded_zero LQ) (fun g hg => ?_) hAB h
  rcases List.mem_append.mp hg with hcore | hind
  · rw [arithAxioms_sentence g hcore]
    exact slash_arithAxioms hlift hcon g hcore
  · exact hInd g hind

/-- 🏁🏁🏁 **LA DP DEL FRAGMENTO SIN INSTANCIAS DE INDUCCIÓN** — y aquí no queda nada por
    descargar **salvo la consistencia**: `hInd` es vacía y `hlift` sale por `rfl`.

    Es el teorema al que llevaba H3ter: la propiedad de disyunción para una teoría
    aritmética de verdad, con el dominio, el colapso y la barra hechos, y **una sola
    hipótesis de fondo**. -/
theorem qDisjunctionProperty_arith
    (hcon : Not (ctxA [] ⊢ᵢ Formula.bottom))
    {A B : Formula}
    (hAB : collapseF LQ (substF zeroS (Formula.or A B)) = Formula.or A B)
    (h : ctxA [] ⊢ᵢ Formula.or A B) :
    Or (ctxA [] ⊢ᵢ A) (ctxA [] ⊢ᵢ B) := by
  refine qDisjunctionPropertyA [] (by rfl) hcon ?_ hAB h
  intro g hg
  cases hg

/-! ## 6 · ⭐ EL FRAGMENTO CRECE: `τ`

    ⚠️ **El fragmento de 17 no es maximal**, y decir lo contrario sería dejar leer de más.
    `τ` entra casi gratis, y por una razón que se ve en sus dos axiomas:

    > `ax25 : τ 0 = 0`   y   `ax26 : ∀n. τ(σn) = n`

    Los dos son **de Harrop** (medido) y entre los dos **determinan `τ` sobre todo numeral
    SIN inducción ninguna**: el caso `0` es `ax25` tal cual, y el caso `σk̄` es `ax26`
    instanciada. Compárese con `/₂`, caracterizado por una ecuación de la que no se despeja
    sin cancelación — y la cancelación pide inducción en el objeto. -/

/-- La signatura del fragmento, con `τ`. -/
def LQt (s : String) (n : Nat) : Bool := LQ s n || (s == pred_sym && n == 1)

def arithTAxioms : List Formula := arithAxioms ++ [ax25_pred_zero, ax26_pred_succ]

/-- ⛔ **EVIDENCIA**: los 19 son sentencias del lenguaje extendido. Por `rfl`. -/
theorem arithTAxioms_sentences :
    arithTAxioms.map (fun g => collapseF LQt (substF zeroS g)) = arithTAxioms := by rfl

/-- ⛔ **EVIDENCIA**: añadir `τ` NO añade dureza — los duros siguen siendo los mismos dos. -/
theorem arithTAxioms_hard :
    arithTAxioms.filter (fun g => !isHarrop g) = [ax13_lt_def, ax19_lt_trichotomy] := by rfl

/-- El fragmento con `τ` sigue dentro de Q⁺⁺.

    🏗️ **ANDAMIO**: sin uso hoy, igual que `arithAxioms_sub`. Es la pieza por la que el
    fragmento se conecta con la teoría entera cuando haga falta. -/
theorem arithTAxioms_sub : ∀ g, List.Mem g arithTAxioms → List.Mem g coreAxioms := by
  intro g hg
  simp only [arithTAxioms, arithAxioms, List.append] at hg
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.head _
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.head _)
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))
  cases hg

/-- ⭐ **`τ n̄` se evalúa DIRECTAMENTE**: `ax25` para el cero, `ax26` para el sucesor.
    Ninguna inducción, ni meta ni objeto. -/
theorem numeralI_pred {Γ : List Formula}
    (hΓ : ∀ g, List.Mem g arithTAxioms → Γ ⊢ᵢ g) :
    ∀ n : Nat, Γ ⊢ᵢ (Formula.eq (pred (numeralM n)) (numeralM (n - 1))) := by
  intro n
  match n with
  | 0 => exact hΓ ax25_pred_zero (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))
  | k + 1 =>
      show Γ ⊢ᵢ (Formula.eq (pred (succ (numeralM k))) (numeralM k))
      have h26 := specI (hΓ ax26_pred_succ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))) (numeralM k)
      simpa (config := { decide := true }) only [substFormula,
        substTerms, substTerm, ite_true, ite_false, pred, succ,
        substTerm_numeralM] using h26

/-- Del fragmento extendido se sigue el básico. -/
theorem arithT_of_arith {Γ : List Formula}
    (hΓ : ∀ g, List.Mem g arithTAxioms → Γ ⊢ᵢ g) :
    ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g :=
  fun g hg => hΓ g (List.mem_append_left _ hg)

/-- Los SEIS símbolos admitidos, con sus argumentos ya evaluados, dan un numeral.
    Es donde cada símbolo paga su evaluación: `σ` por congruencia, `τ` por `numeralI_pred`,
    y los tres binarios por sus homomorfismos. -/
theorem numOf_of_LQt {Γ : List Formula}
    (hΓ : ∀ g, List.Mem g arithTAxioms → Γ ⊢ᵢ g) :
    ∀ (sy : String) (args : List Term), LQt sy args.length = true →
    (∀ u, List.Mem u args → ∃ n : Nat, Γ ⊢ᵢ (Formula.eq u (numeralM n))) →
    ∃ n : Nat, Γ ⊢ᵢ (Formula.eq (Term.func sy args) (numeralM n)) := by
  intro sy args hL hargs
  match args with
  | [] =>
      simp only [List.length_nil, LQt, LQ, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq] at hL
      rcases hL with ((⟨h1, _⟩ | ⟨_, h2⟩) | ⟨_, h2⟩) | ⟨_, h2⟩
      · subst h1; exact ⟨0, eqI_refl zero⟩
      · exact absurd h2 (by decide)
      · exact absurd h2 (by decide)
      · exact absurd h2 (by decide)
  | [a] =>
      obtain ⟨n, hn⟩ := hargs a (List.Mem.head _)
      simp only [List.length_cons, List.length_nil, LQt, LQ, Bool.or_eq_true,
        Bool.and_eq_true, beq_iff_eq] at hL
      rcases hL with ((⟨_, h2⟩ | ⟨h1, _⟩) | ⟨_, h2⟩) | ⟨h1, _⟩
      · exact absurd h2 (by decide)
      · subst h1; exact ⟨n + 1, eqI_congr_succ hn⟩
      · exact absurd h2 (by decide)
      · subst h1
        exact ⟨n - 1, eqI_trans (eqI_congr_fun1 pred_sym hn) (numeralI_pred hΓ n)⟩
  | [a, b] =>
      obtain ⟨m, hm⟩ := hargs a (List.Mem.head _)
      obtain ⟨n, hn⟩ := hargs b (List.Mem.tail _ (List.Mem.head _))
      simp only [List.length_cons, List.length_nil, LQt, LQ, Bool.or_eq_true,
        Bool.and_eq_true, beq_iff_eq] at hL
      rcases hL with ((⟨_, h2⟩ | ⟨_, h2⟩) | ⟨h1, _⟩) | ⟨_, h2⟩
      · exact absurd h2 (by decide)
      · exact absurd h2 (by decide)
      · rcases h1 with (h1 | h1) | h1
        · subst h1
          exact ⟨m + n, eqI_trans (eqI_congr_fun2 add_sym hm hn)
            (numeralI_add (arithT_of_arith hΓ) m n)⟩
        · subst h1
          exact ⟨m * n, eqI_trans (eqI_congr_fun2 mul_sym hm hn)
            (numeralI_mul (arithT_of_arith hΓ) m n)⟩
        · subst h1
          exact ⟨m ^ n, eqI_trans (eqI_congr_fun2 pow_sym hm hn)
            (numeralI_pow (arithT_of_arith hΓ) m n)⟩
      · exact absurd h2 (by decide)
  | a :: b :: c :: rest =>
      exfalso
      simp only [List.length_cons, LQt, LQ, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq] at hL
      rcases hL with ((⟨_, h2⟩ | ⟨_, h2⟩) | ⟨_, h2⟩) | ⟨_, h2⟩ <;> omega

/-! ### ⭐⭐ `hNum` para el fragmento con `τ` -/

mutual
theorem numOf_grounded {Γ : List Formula}
    (hΓ : ∀ g, List.Mem g arithTAxioms → Γ ⊢ᵢ g) :
    ∀ {t : Term}, Grounded LQt t → ∃ n : Nat, Γ ⊢ᵢ (Formula.eq t (numeralM n)) := by
  intro t h
  cases t with
  | var n =>
      exfalso
      have hc : (zero : Term) = Term.var n := h.2 (fun _ => zero)
      rw [zero] at hc
      exact Term.noConfusion hc
  | func sy ts =>
      by_cases hL : LQt sy ts.length = true
      · have hall := h.1
        rw [collapseT, if_pos hL] at hall
        injection hall with _ hts
        refine numOf_of_LQt hΓ sy ts hL ?_
        exact numOf_grounded_list hΓ ts hts (fun ρ => by
          have hx := h.2 ρ; simp only [substT] at hx; injection hx)
      · exfalso
        have hall := h.1
        rw [collapseT, if_neg hL, zero] at hall
        injection hall with h1 h2
        exact hL (by rw [← h1, ← h2]; decide)

theorem numOf_grounded_list {Γ : List Formula}
    (hΓ : ∀ g, List.Mem g arithTAxioms → Γ ⊢ᵢ g) :
    ∀ (ts : List Term), collapseTs LQt ts = ts → (∀ ρ : Subst, substTs ρ ts = ts) →
    ∀ u, List.Mem u ts → ∃ n : Nat, Γ ⊢ᵢ (Formula.eq u (numeralM n)) := by
  intro ts hc hs
  cases ts with
  | nil => intro u hu; cases hu
  | cons t ts0 =>
      rw [collapseTs] at hc
      injection hc with hc1 hc2
      intro u hu
      cases hu with
      | head =>
          exact numOf_grounded hΓ ⟨hc1, fun ρ => by
            have hx := hs ρ; simp only [substTs] at hx; injection hx⟩
      | tail _ hu0 =>
          exact numOf_grounded_list hΓ ts0 hc2
            (fun ρ => by have hx := hs ρ; simp only [substTs] at hx; injection hx) u hu0
end

/-! ## 7 · 🏁 LA DP DEL FRAGMENTO CON `τ` — 19 axiomas, y la misma única hipótesis -/

def ctxT (insts : List Formula) : List Formula :=
  arithTAxioms ++ insts.map inductionFormula

theorem axT' {insts : List Formula} {g : Formula} (h : List.Mem g arithTAxioms) :
    ctxT insts ⊢ᵢ g := Derivesᵢ.hyp _ _ (List.mem_append_left _ h)

theorem arithTAxioms_sentence (g : Formula) (hg : List.Mem g arithTAxioms) :
    collapseF LQt (substF zeroS g) = g :=
  eq_of_map_self (f := fun g => collapseF LQt (substF zeroS g)) arithTAxioms
    arithTAxioms_sentences g hg

/-- ⭐⭐ `hNum` para el fragmento con `τ`. Tampoco es hipótesis. -/
theorem hNumT_fragment {insts : List Formula} : ∀ t : Term, Grounded LQt t →
    ∃ n : Nat, ctxT insts ⊢ᵢ (Formula.eq t (numeralM n)) :=
  fun _ ht => numOf_grounded (fun _ hg => axT' hg) ht

/-- ⭐⭐ **Los 19 axiomas del fragmento con `τ`, barrados.** -/
theorem slash_arithTAxioms {insts : List Formula}
    (hlift : (ctxT insts).map (liftFormula 0) = ctxT insts)
    (hcon : Not (ctxT insts ⊢ᵢ Formula.bottom)) :
    ∀ g, List.Mem g arithTAxioms → Slash (ctxT insts) (Grounded LQt) g := by
  have hA : ∀ g, List.Mem g arithTAxioms → ctxT insts ⊢ᵢ g := fun _ hg => axT' hg
  intro g hg
  simp only [arithTAxioms, arithAxioms, List.append] at hg
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax2_peano_succ_neq_zero rfl (axT' (List.Mem.head _))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax3_peano_succ_inj rfl (axT' (List.Mem.tail _ (List.Mem.head _)))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax4_add_zero rfl (axT' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax5_add_succ rfl (axT' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax6_add_comm rfl (axT' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax7_add_assoc rfl (axT' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax8_mul_zero rfl (axT' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax9_mul_succ rfl (axT' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax10_mul_comm rfl (axT' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax11_mul_assoc rfl (axT' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax12_mul_distrib rfl (axT' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_ax13 LQt (by decide) (arithT_of_arith hA) hlift hcon hNumT_fragment
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax18_lt_irrefl rfl (axT' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_ax19 LQt (arithT_of_arith hA) hNumT_fragment
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax_L1_in_nil rfl (axT' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax_pow_zero rfl (axT' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax_pow_succ rfl (axT' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax25_pred_zero rfl (axT' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax26_pred_succ rfl (axT' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))
  cases hg

/-- 🏁🏁🏁 **LA DP DEL FRAGMENTO CON `τ`.** Mismo enunciado, un símbolo más y dos
    axiomas más, **y la misma única hipótesis de fondo**. -/
theorem qDisjunctionPropertyT (insts : List Formula)
    (hlift : (ctxT insts).map (liftFormula 0) = ctxT insts)
    (hcon : Not (ctxT insts ⊢ᵢ Formula.bottom))
    (hInd : ∀ g, List.Mem g (insts.map inductionFormula) →
      Slash (ctxT insts) (Grounded LQt) (collapseF LQt (substF zeroS g)))
    {A B : Formula}
    (hAB : collapseF LQt (substF zeroS (Formula.or A B)) = Formula.or A B)
    (h : ctxT insts ⊢ᵢ Formula.or A B) :
    Or (ctxT insts ⊢ᵢ A) (ctxT insts ⊢ᵢ B) := by
  refine disjunction_property_of_slashed (ctxT insts) (Grounded LQt) LQt
    (fun _ hu => grounded_fix LQt hu) (grounded_collapse_subst LQt)
    zeroS (fun _ => grounded_zero LQt) (fun g hg => ?_) hAB h
  rcases List.mem_append.mp hg with hcore | hind
  · rw [arithTAxioms_sentence g hcore]
    exact slash_arithTAxioms hlift hcon g hcore
  · exact hInd g hind

/-- 🏁🏁🏁 **Sin instancias de inducción: la consistencia y nada más.** -/
theorem qDisjunctionProperty_arithT
    (hcon : Not (ctxT [] ⊢ᵢ Formula.bottom))
    {A B : Formula}
    (hAB : collapseF LQt (substF zeroS (Formula.or A B)) = Formula.or A B)
    (h : ctxT [] ⊢ᵢ Formula.or A B) :
    Or (ctxT [] ⊢ᵢ A) (ctxT [] ⊢ᵢ B) := by
  refine qDisjunctionPropertyT [] (by rfl) hcon ?_ hAB h
  intro g hg
  cases hg

/-! ## 8 · ⭐ EL FRAGMENTO CRECE OTRA VEZ: `%₂`

    `%₂` también está **definido por recursión sobre el constructor**, aunque cuesta un poco
    más verlo: `ax24` da la base (vía `x = 2·0`) y `ax16` el paso, en la forma
    `(%₂x = 0) ⇔ (%₂(σx) = 1)`. El caso `1 → 0` no lo da `ax16` directamente: se saca
    **refutando** la otra rama de `ax21` con `numeralI_ne`.

    ⭐ Y la refutación va **dentro de una rama de `elim_or`**, bajo hipótesis — así que
    **NO hace falta la consistencia** para evaluar `%₂`. Sí la necesita `slash_ax21`, que es
    otra cosa. -/

def LQtm (s : String) (n : Nat) : Bool := LQt s n || (s == mod2_sym && n == 1)

def arithTMAxioms : List Formula :=
  arithTAxioms ++ [ax16_mod2_succ, ax21_mod2_range, ax24_mod2_of_even]

/-- ⛔ **EVIDENCIA**: los 22 son sentencias del lenguaje extendido. -/
theorem arithTMAxioms_sentences :
    arithTMAxioms.map (fun g => collapseF LQtm (substF zeroS g)) = arithTMAxioms := by rfl

/-- ⛔ **EVIDENCIA**: `%₂` añade UN duro, `ax21`, y ya estaba barrado. -/
theorem arithTMAxioms_hard :
    arithTMAxioms.filter (fun g => !isHarrop g)
      = [ax13_lt_def, ax19_lt_trichotomy, ax21_mod2_range] := by rfl

theorem arithTM_of_arithT {Γ : List Formula}
    (hΓ : ∀ g, List.Mem g arithTMAxioms → Γ ⊢ᵢ g) :
    ∀ g, List.Mem g arithTAxioms → Γ ⊢ᵢ g :=
  fun g hg => hΓ g (List.mem_append_left _ hg)

theorem arithTM_of_arith {Γ : List Formula}
    (hΓ : ∀ g, List.Mem g arithTMAxioms → Γ ⊢ᵢ g) :
    ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g :=
  fun g hg => arithT_of_arith (arithTM_of_arithT hΓ) g hg

/-- ⭐⭐ **`%₂ n̄` se evalúa**, por inducción META y sin consistencia. -/
theorem numeralI_mod2 {Γ : List Formula}
    (hΓ : ∀ g, List.Mem g arithTMAxioms → Γ ⊢ᵢ g) :
    ∀ n : Nat, Γ ⊢ᵢ (Formula.eq (mod2 (numeralM n)) (numeralM (n % 2))) := by
  have h16 : ∀ t : Term, Γ ⊢ᵢ (Formula.and
      (Formula.impl (Formula.eq (mod2 t) zero) (Formula.eq (mod2 (succ t)) one))
      (Formula.impl (Formula.eq (mod2 (succ t)) one) (Formula.eq (mod2 t) zero))) := by
    intro t
    have hh := specI (hΓ ax16_mod2_succ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))) t
    simpa (config := { decide := true }) only [substFormula, substTerms, substTerm,
      ite_true, ite_false, mod2, succ, zero, one, iff] using hh
  have h21 : ∀ t : Term, Γ ⊢ᵢ (Formula.or (Formula.eq (mod2 t) zero)
      (Formula.eq (mod2 t) one)) := by
    intro t
    have hh := specI (hΓ ax21_mod2_range (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))) t
    simpa (config := { decide := true }) only [substFormula, substTerms, substTerm,
      ite_true, ite_false, mod2, zero, one, succ] using hh
  intro n
  induction n with
  | zero =>
      have h24 := specI (specI (hΓ ax24_mod2_of_even (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))) zero) zero
      have h24' : Γ ⊢ᵢ (Formula.impl (Formula.eq zero (mul two zero))
          (Formula.eq (mod2 zero) zero)) := by
        simpa (config := { decide := true }) only [substFormula, substTerms, substTerm,
          ite_true, ite_false, mod2, mul, zero, two, one, succ,
          substTerm_liftTerm] using h24
      have h8 := specI (hΓ ax8_mul_zero (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))) two
      have h8' : Γ ⊢ᵢ (Formula.eq (mul two zero) zero) := by
        simpa (config := { decide := true }) only [substFormula, substTerms, substTerm,
          ite_true, ite_false, mul, zero, two, one, succ] using h8
      exact Derivesᵢ.elim_impl _ _ _ h24' (eqI_symm h8')
  | succ k ih =>
      by_cases hk : k % 2 = 0
      · show Γ ⊢ᵢ (Formula.eq (mod2 (succ (numeralM k))) (numeralM ((k + 1) % 2)))
        rw [show (k + 1) % 2 = 1 by omega]
        refine Derivesᵢ.elim_impl _ _ _ (Derivesᵢ.elim_and_l _ _ _ (h16 (numeralM k))) ?_
        rw [hk] at ih
        exact ih
      · show Γ ⊢ᵢ (Formula.eq (mod2 (succ (numeralM k))) (numeralM ((k + 1) % 2)))
        rw [show (k + 1) % 2 = 0 by omega]
        refine Derivesᵢ.elim_or _ (Formula.eq (mod2 (succ (numeralM k))) zero)
          (Formula.eq (mod2 (succ (numeralM k))) one)
          (Formula.eq (mod2 (succ (numeralM k))) zero) (h21 (succ (numeralM k)))
          (Derivesᵢ.hyp _ _ (List.Mem.head _)) ?_
        refine Derivesᵢ.bot_elim _ _ ?_
        have hne := numeralI_ne (arithTM_of_arith hΓ) (a := 1) (b := 0) (by omega)
        have h16w : (Formula.eq (mod2 (succ (numeralM k))) one :: Γ) ⊢ᵢ
            Formula.impl (Formula.eq (mod2 (succ (numeralM k))) one)
                         (Formula.eq (mod2 (numeralM k)) zero) :=
          Derivesᵢ.weakening _ _ _ (Derivesᵢ.elim_and_r _ _ _ (h16 (numeralM k)))
            (fun _ hx => List.Mem.tail _ hx)
        have hstep := Derivesᵢ.elim_impl _ _ _ h16w
          (Derivesᵢ.hyp _ _ (List.Mem.head _))
        have hih : (Formula.eq (mod2 (succ (numeralM k))) one :: Γ) ⊢ᵢ
            (Formula.eq (mod2 (numeralM k)) one) := by
          rw [show k % 2 = 1 by omega] at ih
          exact Derivesᵢ.weakening _ _ _ ih (fun _ hx => List.Mem.tail _ hx)
        refine Derivesᵢ.elim_impl _ (Formula.eq (numeralM 1) (numeralM 0)) Formula.bottom
          (Derivesᵢ.weakening _ _ _ hne (fun _ hx => List.Mem.tail _ hx)) ?_
        exact eqI_trans (eqI_symm hih) hstep

/-- Los SIETE símbolos admitidos, con sus argumentos evaluados, dan un numeral. -/
theorem numOf_of_LQtm {Γ : List Formula}
    (hΓ : ∀ g, List.Mem g arithTMAxioms → Γ ⊢ᵢ g) :
    ∀ (sy : String) (args : List Term), LQtm sy args.length = true →
    (∀ u, List.Mem u args → ∃ n : Nat, Γ ⊢ᵢ (Formula.eq u (numeralM n))) →
    ∃ n : Nat, Γ ⊢ᵢ (Formula.eq (Term.func sy args) (numeralM n)) := by
  intro sy args hL hargs
  match args with
  | [] =>
      simp only [List.length_nil, LQtm, LQt, LQ, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq] at hL
      rcases hL with (((⟨h1, _⟩ | ⟨_, h2⟩) | ⟨_, h2⟩) | ⟨_, h2⟩) | ⟨_, h2⟩
      · subst h1; exact ⟨0, eqI_refl zero⟩
      all_goals exact absurd h2 (by decide)
  | [a] =>
      obtain ⟨n, hn⟩ := hargs a (List.Mem.head _)
      simp only [List.length_cons, List.length_nil, LQtm, LQt, LQ, Bool.or_eq_true,
        Bool.and_eq_true, beq_iff_eq] at hL
      rcases hL with (((⟨_, h2⟩ | ⟨h1, _⟩) | ⟨_, h2⟩) | ⟨h1, _⟩) | ⟨h1, _⟩
      · exact absurd h2 (by decide)
      · subst h1; exact ⟨n + 1, eqI_congr_succ hn⟩
      · exact absurd h2 (by decide)
      · subst h1
        exact ⟨n - 1, eqI_trans (eqI_congr_fun1 pred_sym hn)
          (numeralI_pred (arithTM_of_arithT hΓ) n)⟩
      · subst h1
        exact ⟨n % 2, eqI_trans (eqI_congr_fun1 mod2_sym hn) (numeralI_mod2 hΓ n)⟩
  | [a, b] =>
      obtain ⟨m, hm⟩ := hargs a (List.Mem.head _)
      obtain ⟨n, hn⟩ := hargs b (List.Mem.tail _ (List.Mem.head _))
      simp only [List.length_cons, List.length_nil, LQtm, LQt, LQ, Bool.or_eq_true,
        Bool.and_eq_true, beq_iff_eq] at hL
      rcases hL with (((⟨_, h2⟩ | ⟨_, h2⟩) | ⟨h1, _⟩) | ⟨_, h2⟩) | ⟨_, h2⟩
      · exact absurd h2 (by decide)
      · exact absurd h2 (by decide)
      · rcases h1 with (h1 | h1) | h1
        · subst h1
          exact ⟨m + n, eqI_trans (eqI_congr_fun2 add_sym hm hn)
            (numeralI_add (arithTM_of_arith hΓ) m n)⟩
        · subst h1
          exact ⟨m * n, eqI_trans (eqI_congr_fun2 mul_sym hm hn)
            (numeralI_mul (arithTM_of_arith hΓ) m n)⟩
        · subst h1
          exact ⟨m ^ n, eqI_trans (eqI_congr_fun2 pow_sym hm hn)
            (numeralI_pow (arithTM_of_arith hΓ) m n)⟩
      · exact absurd h2 (by decide)
      · exact absurd h2 (by decide)
  | a :: b :: c :: rest =>
      exfalso
      simp only [List.length_cons, LQtm, LQt, LQ, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq] at hL
      rcases hL with (((⟨_, h2⟩ | ⟨_, h2⟩) | ⟨_, h2⟩) | ⟨_, h2⟩) | ⟨_, h2⟩ <;> omega

mutual
theorem numOfM_grounded {Γ : List Formula}
    (hΓ : ∀ g, List.Mem g arithTMAxioms → Γ ⊢ᵢ g) :
    ∀ {t : Term}, Grounded LQtm t → ∃ n : Nat, Γ ⊢ᵢ (Formula.eq t (numeralM n)) := by
  intro t h
  cases t with
  | var n =>
      exfalso
      have hc : (zero : Term) = Term.var n := h.2 (fun _ => zero)
      rw [zero] at hc
      exact Term.noConfusion hc
  | func sy ts =>
      by_cases hL : LQtm sy ts.length = true
      · have hall := h.1
        rw [collapseT, if_pos hL] at hall
        injection hall with _ hts
        refine numOf_of_LQtm hΓ sy ts hL ?_
        exact numOfM_grounded_list hΓ ts hts (fun ρ => by
          have hx := h.2 ρ; simp only [substT] at hx; injection hx)
      · exfalso
        have hall := h.1
        rw [collapseT, if_neg hL, zero] at hall
        injection hall with h1 h2
        exact hL (by rw [← h1, ← h2]; decide)

theorem numOfM_grounded_list {Γ : List Formula}
    (hΓ : ∀ g, List.Mem g arithTMAxioms → Γ ⊢ᵢ g) :
    ∀ (ts : List Term), collapseTs LQtm ts = ts → (∀ ρ : Subst, substTs ρ ts = ts) →
    ∀ u, List.Mem u ts → ∃ n : Nat, Γ ⊢ᵢ (Formula.eq u (numeralM n)) := by
  intro ts hc hs
  cases ts with
  | nil => intro u hu; cases hu
  | cons t ts0 =>
      rw [collapseTs] at hc
      injection hc with hc1 hc2
      intro u hu
      cases hu with
      | head =>
          exact numOfM_grounded hΓ ⟨hc1, fun ρ => by
            have hx := hs ρ; simp only [substTs] at hx; injection hx⟩
      | tail _ hu0 =>
          exact numOfM_grounded_list hΓ ts0 hc2
            (fun ρ => by have hx := hs ρ; simp only [substTs] at hx; injection hx) u hu0
end

/-! ## 9 · 🏁 LA DP DEL FRAGMENTO CON `τ` Y `%₂` — 22 de 34 -/

def ctxTM (insts : List Formula) : List Formula :=
  arithTMAxioms ++ insts.map inductionFormula

theorem axTM' {insts : List Formula} {g : Formula} (h : List.Mem g arithTMAxioms) :
    ctxTM insts ⊢ᵢ g := Derivesᵢ.hyp _ _ (List.mem_append_left _ h)

theorem arithTMAxioms_sentence (g : Formula) (hg : List.Mem g arithTMAxioms) :
    collapseF LQtm (substF zeroS g) = g :=
  eq_of_map_self (f := fun g => collapseF LQtm (substF zeroS g)) arithTMAxioms
    arithTMAxioms_sentences g hg

theorem hNumTM_fragment {insts : List Formula} : ∀ t : Term, Grounded LQtm t →
    ∃ n : Nat, ctxTM insts ⊢ᵢ (Formula.eq t (numeralM n)) :=
  fun _ ht => numOfM_grounded (fun _ hg => axTM' hg) ht

/-- ⭐⭐ **Los 22 axiomas, barrados.** -/
theorem slash_arithTMAxioms {insts : List Formula}
    (hlift : (ctxTM insts).map (liftFormula 0) = ctxTM insts)
    (hcon : Not (ctxTM insts ⊢ᵢ Formula.bottom)) :
    ∀ g, List.Mem g arithTMAxioms → Slash (ctxTM insts) (Grounded LQtm) g := by
  have hA : ∀ g, List.Mem g arithTMAxioms → ctxTM insts ⊢ᵢ g := fun _ hg => axTM' hg
  intro g hg
  simp only [arithTMAxioms, arithTAxioms, arithAxioms, List.append] at hg
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax2_peano_succ_neq_zero rfl (axTM' (List.Mem.head _))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax3_peano_succ_inj rfl (axTM' (List.Mem.tail _ (List.Mem.head _)))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax4_add_zero rfl (axTM' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax5_add_succ rfl (axTM' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax6_add_comm rfl (axTM' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax7_add_assoc rfl (axTM' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax8_mul_zero rfl (axTM' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax9_mul_succ rfl (axTM' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax10_mul_comm rfl (axTM' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax11_mul_assoc rfl (axTM' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax12_mul_distrib rfl (axTM' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_ax13 LQtm (by decide) (arithTM_of_arith hA) hlift hcon hNumTM_fragment
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax18_lt_irrefl rfl (axTM' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_ax19 LQtm (arithTM_of_arith hA) hNumTM_fragment
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax_L1_in_nil rfl (axTM' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax_pow_zero rfl (axTM' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax_pow_succ rfl (axTM' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax25_pred_zero rfl (axTM' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax26_pred_succ rfl (axTM' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax16_mod2_succ rfl (axTM' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_ax21 LQtm (by decide) (axTM' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))) (arithTM_of_arith hA) hcon hNumTM_fragment
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax24_mod2_of_even rfl (axTM' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))
  cases hg

/-- 🏁🏁🏁 **LA DP DEL FRAGMENTO CON `τ` Y `%₂`** — 22 de los 34 axiomas, siete símbolos,
    y **la misma única hipótesis**. -/
theorem qDisjunctionPropertyTM (insts : List Formula)
    (hlift : (ctxTM insts).map (liftFormula 0) = ctxTM insts)
    (hcon : Not (ctxTM insts ⊢ᵢ Formula.bottom))
    (hInd : ∀ g, List.Mem g (insts.map inductionFormula) →
      Slash (ctxTM insts) (Grounded LQtm) (collapseF LQtm (substF zeroS g)))
    {A B : Formula}
    (hAB : collapseF LQtm (substF zeroS (Formula.or A B)) = Formula.or A B)
    (h : ctxTM insts ⊢ᵢ Formula.or A B) :
    Or (ctxTM insts ⊢ᵢ A) (ctxTM insts ⊢ᵢ B) := by
  refine disjunction_property_of_slashed (ctxTM insts) (Grounded LQtm) LQtm
    (fun _ hu => grounded_fix LQtm hu) (grounded_collapse_subst LQtm)
    zeroS (fun _ => grounded_zero LQtm) (fun g hg => ?_) hAB h
  rcases List.mem_append.mp hg with hcore | hind
  · rw [arithTMAxioms_sentence g hcore]
    exact slash_arithTMAxioms hlift hcon g hcore
  · exact hInd g hind

/-- 🏁🏁🏁 **Sin instancias de inducción: la consistencia y nada más.** -/
theorem qDisjunctionProperty_arithTM
    (hcon : Not (ctxTM [] ⊢ᵢ Formula.bottom))
    {A B : Formula}
    (hAB : collapseF LQtm (substF zeroS (Formula.or A B)) = Formula.or A B)
    (h : ctxTM [] ⊢ᵢ Formula.or A B) :
    Or (ctxTM [] ⊢ᵢ A) (ctxTM [] ⊢ᵢ B) := by
  refine qDisjunctionPropertyTM [] (by rfl) hcon ?_ hAB h
  intro g hg
  cases hg

/-! ## 10 · 🏁 `/₂` ENTRA — 23 de 34, y ADR-037 refutado

  ADR-037 cerró `/₂` con «pide cancelación de `+` y `·`». **No hace falta cancelar nada**:
  `ax17` caracteriza `/₂` por una ecuación cuyo otro término (`%₂`) ya está determinado, y
  lo que falta se despeja **por el ORDEN** —`PeanoRF/HA/Order.lean`—.

  ⭐ El criterio de ADR-037 —«entra el que está definido por recursión sobre el
  constructor»— resulta ser **suficiente pero no necesario**. `/₂` no está definido por
  recursión y entra igual, porque la caracterización lo **acota por los dos lados** en un
  orden total y discreto. -/

def LQtd (s : String) (n : Nat) : Bool := LQtm s n || (s == div2_sym && n == 1)

def arithTDAxioms : List Formula := arithTMAxioms ++ [ax17_div_mod_eq]

/-- ⛔ **EVIDENCIA**: los 23 son sentencias del lenguaje extendido. -/
theorem arithTDAxioms_sentences :
    arithTDAxioms.map (fun g => collapseF LQtd (substF zeroS g)) = arithTDAxioms := by rfl

/-- ⛔ **EVIDENCIA**: `/₂` **no añade dureza** — `ax17` es de Harrop. -/
theorem arithTDAxioms_hard :
    arithTDAxioms.filter (fun g => !isHarrop g)
      = [ax13_lt_def, ax19_lt_trichotomy, ax21_mod2_range] := by rfl

theorem arithTD_of_arithTM {Γ : List Formula}
    (hΓ : ∀ g, List.Mem g arithTDAxioms → Γ ⊢ᵢ g) :
    ∀ g, List.Mem g arithTMAxioms → Γ ⊢ᵢ g :=
  fun g hg => hΓ g (List.mem_append_left _ hg)

theorem arithTD_of_arith {Γ : List Formula}
    (hΓ : ∀ g, List.Mem g arithTDAxioms → Γ ⊢ᵢ g) :
    ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g :=
  fun g hg => arithTM_of_arith (arithTD_of_arithTM hΓ) g hg

/-- `ax17` instanciado en un término anclado. -/
theorem ax17I {Γ : List Formula} (h17 : Γ ⊢ᵢ ax17_div_mod_eq)
    (L : String → Nat → Bool) {t : Term} (ht : Grounded L t) :
    Γ ⊢ᵢ Formula.eq (add (mul (div2 t) (numeralM 2)) (mod2 t)) t := by
  have h := specI h17 t
  simpa (config := { decide := true }) only [ax17_div_mod_eq, forall_, substFormula,
    substTerms, substTerm, ite_true, ite_false, add, mul, div2, mod2, two, one, zero,
    succ, numeralM, grounded_substTerm L ht] using h

/-- 🏁 **`/₂ n̄` ES demostrablemente `(n/2)‾`.** `ax17` da `(/₂n̄)·2̄ + %₂n̄ = n̄`,
    `numeralI_mod2` fija `%₂n̄`, y la tricotomía contra `(n/2)‾` cierra las dos ramas malas:
    cada una produce `n̄ < n̄`, que `ax18` prohíbe. -/
theorem numeralI_div2 {Γ : List Formula} (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g)
    (hTM : ∀ g, List.Mem g arithTMAxioms → Γ ⊢ᵢ g)
    (h17 : Γ ⊢ᵢ ax17_div_mod_eq)
    (hlift : Γ.map (liftFormula 0) = Γ)
    {L : String → Nat → Bool} (hm : L mul_sym 2 = true) (ha2 : L add_sym 2 = true)
    (hsu : L succ_sym 1 = true) (hd : L div2_sym 1 = true) (n : Nat) :
    Γ ⊢ᵢ Formula.eq (div2 (numeralM n)) (numeralM (n / 2)) := by
  have hng : Grounded L (numeralM n) := grounded_numeralM L hsu n
  have hyg : Grounded L (div2 (numeralM n)) := grounded_func1 L hd hng
  have hkg : Grounded L (numeralM (n / 2)) := grounded_numeralM L hsu (n / 2)
  -- (1) `(/₂ n̄)·2̄ + (n%2)‾ = n̄`
  have hy : Γ ⊢ᵢ Formula.eq
      (add (mul (div2 (numeralM n)) (numeralM 2)) (numeralM (n % 2))) (numeralM n) :=
    eqI_trans (eqI_congr_fun2_r add_sym (mul (div2 (numeralM n)) (numeralM 2))
      (eqI_symm (numeralI_mod2 hTM n))) (ax17I h17 L hng)
  -- (2) `(n/2)‾·2̄ + (n%2)‾ = n̄`
  have hk : Γ ⊢ᵢ Formula.eq
      (add (mul (numeralM (n / 2)) (numeralM 2)) (numeralM (n % 2))) (numeralM n) := by
    have hmul := numeralI_mul hΓ (n / 2) 2
    have hadd := numeralI_add hΓ (n / 2 * 2) (n % 2)
    rw [show n / 2 * 2 + n % 2 = n from by omega] at hadd
    exact eqI_trans (eqI_congr_fun2_l add_sym (numeralM (n % 2)) hmul) hadd
  -- (3) tricotomía
  have htri := specI (specI (ax19I hΓ) (div2 (numeralM n))) (numeralM (n / 2))
  have htri' : Γ ⊢ᵢ Formula.or (lt (div2 (numeralM n)) (numeralM (n / 2)))
      (Formula.or (Formula.eq (div2 (numeralM n)) (numeralM (n / 2)))
                  (lt (numeralM (n / 2)) (div2 (numeralM n)))) := by
    simpa [ax19_lt_trichotomy, forall_2, substFormula, substTerms, substTerm, lt,
      grounded_liftTerm L hyg, grounded_liftTerm L hkg,
      grounded_substTerm L hyg, grounded_substTerm L hkg] using htri
  -- una rama mala, parametrizada por el lado
  have bad : ∀ (p q : Term), Grounded L p → Grounded L q →
      Γ ⊢ᵢ Formula.eq (add (mul p (numeralM 2)) (numeralM (n % 2))) (numeralM n) →
      Γ ⊢ᵢ Formula.eq (add (mul q (numeralM 2)) (numeralM (n % 2))) (numeralM n) →
      (lt p q :: Γ) ⊢ᵢ Formula.bottom := by
    intro p q hp hq hep heq
    have hΓ1 : ∀ g, List.Mem g arithAxioms → (lt p q :: Γ) ⊢ᵢ g := hyps_cons hΓ (lt p q)
    have hlt2 := Derivesᵢ.elim_impl _ _ _
      (Derivesᵢ.weakening _ _ _
        (ltI_mul_two hΓ hlift hm hsu hp hq) (fun _ hz => List.Mem.tail _ hz))
      (Derivesᵢ.hyp _ _ (List.Mem.head _))
    have hmono := Derivesᵢ.elim_impl _ _ _
      (Derivesᵢ.weakening _ _ _
        (ltI_add_right hΓ hlift ha2 (L := L) (grounded_func2 L hm hp
          (grounded_numeralM L hsu 2)) (grounded_func2 L hm hq
          (grounded_numeralM L hsu 2)) (grounded_numeralM L hsu (n % 2)))
        (fun _ hz => List.Mem.tail _ hz))
      hlt2
    -- `p·2̄ + r̄ < q·2̄ + r̄`, y los dos lados son `n̄`
    have hepW : (lt p q :: Γ) ⊢ᵢ Formula.eq
        (add (mul p (numeralM 2)) (numeralM (n % 2))) (numeralM n) :=
      Derivesᵢ.weakening _ _ _ hep (fun _ hz => List.Mem.tail _ hz)
    have heqW : (lt p q :: Γ) ⊢ᵢ Formula.eq
        (add (mul q (numeralM 2)) (numeralM (n % 2))) (numeralM n) :=
      Derivesᵢ.weakening _ _ _ heq (fun _ hz => List.Mem.tail _ hz)
    have hnn : (lt p q :: Γ) ⊢ᵢ lt (numeralM n) (numeralM n) :=
      eqI_rw_atom2_r lt_sym (numeralM n) heqW (eqI_rw_atom2_l lt_sym _ hepW hmono)
    exact Derivesᵢ.elim_impl _ _ _
      (ltI_irrefl hΓ1 L (grounded_numeralM L hsu n)) hnn
  -- las tres ramas
  refine Derivesᵢ.elim_or _ _ _ _ htri' ?_ ?_
  · exact Derivesᵢ.bot_elim _ _ (bad _ _ hyg hkg hy hk)
  refine Derivesᵢ.elim_or _ _ _ _ (Derivesᵢ.hyp _ _ (List.Mem.head _)) ?_ ?_
  · exact Derivesᵢ.hyp _ _ (List.Mem.head _)
  · exact Derivesᵢ.bot_elim _ _ (Derivesᵢ.weakening _ _ _ (bad _ _ hkg hyg hk hy)
      (fun _ hz => match hz with
        | List.Mem.head _ => List.Mem.head _
        | List.Mem.tail _ h => List.Mem.tail _ (List.Mem.tail _ h)))


/-- `ax17` es el último de los 23. -/
theorem axD17 {Γ : List Formula} (hΓ : ∀ g, List.Mem g arithTDAxioms → Γ ⊢ᵢ g) :
    Γ ⊢ᵢ ax17_div_mod_eq :=
  hΓ ax17_div_mod_eq (by repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

/-- ⭐ Evaluar un símbolo de `LQtd` sobre argumentos ya evaluados. La estructura vieja no se
    rehace: si el símbolo ya estaba en `LQtm`, se delega; si no, es `/₂` con aridad 1. -/
theorem numOf_of_LQtd {Γ : List Formula}
    (hΓ : ∀ g, List.Mem g arithTDAxioms → Γ ⊢ᵢ g)
    (hlift : Γ.map (liftFormula 0) = Γ) :
    ∀ (sy : String) (args : List Term), LQtd sy args.length = true →
    (∀ u, List.Mem u args → ∃ n : Nat, Γ ⊢ᵢ (Formula.eq u (numeralM n))) →
    ∃ n : Nat, Γ ⊢ᵢ (Formula.eq (Term.func sy args) (numeralM n)) := by
  intro sy args hL hargs
  by_cases hTM : LQtm sy args.length = true
  · exact numOf_of_LQtm (arithTD_of_arithTM hΓ) sy args hTM hargs
  · have hdiv : And (sy = div2_sym) (args.length = 1) := by
      simp only [LQtd, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hL
      rcases hL with h | h
      · exact absurd h hTM
      · exact h
    obtain ⟨hsy, hlen⟩ := hdiv
    match args, hlen with
    | [a], _ =>
        obtain ⟨n, hn⟩ := hargs a (List.Mem.head _)
        subst hsy
        refine ⟨n / 2, eqI_trans (eqI_congr_fun1 div2_sym hn) ?_⟩
        exact numeralI_div2 (arithTD_of_arith hΓ) (arithTD_of_arithTM hΓ) (axD17 hΓ)
          hlift (L := LQtd) (by decide) (by decide) (by decide) (by decide) n

mutual
/-- ⭐ `hNum` para la signatura con `/₂`. -/
theorem numOfD_grounded {Γ : List Formula}
    (hΓ : ∀ g, List.Mem g arithTDAxioms → Γ ⊢ᵢ g)
    (hlift : Γ.map (liftFormula 0) = Γ) :
    ∀ {t : Term}, Grounded LQtd t → ∃ n : Nat, Γ ⊢ᵢ (Formula.eq t (numeralM n)) := by
  intro t h
  cases t with
  | var n =>
      exfalso
      have hc : (zero : Term) = Term.var n := h.2 (fun _ => zero)
      rw [zero] at hc
      exact Term.noConfusion hc
  | func sy ts =>
      by_cases hL : LQtd sy ts.length = true
      · have hall := h.1
        rw [collapseT, if_pos hL] at hall
        injection hall with _ hts
        refine numOf_of_LQtd hΓ hlift sy ts hL ?_
        exact numOfD_grounded_list hΓ hlift ts hts (fun ρ => by
          have hx := h.2 ρ; simp only [substT] at hx; injection hx)
      · exfalso
        have hall := h.1
        rw [collapseT, if_neg hL, zero] at hall
        injection hall with h1 h2
        exact hL (by rw [← h1, ← h2]; decide)

theorem numOfD_grounded_list {Γ : List Formula}
    (hΓ : ∀ g, List.Mem g arithTDAxioms → Γ ⊢ᵢ g)
    (hlift : Γ.map (liftFormula 0) = Γ) :
    ∀ (ts : List Term), collapseTs LQtd ts = ts → (∀ ρ : Subst, substTs ρ ts = ts) →
    ∀ u, List.Mem u ts → ∃ n : Nat, Γ ⊢ᵢ (Formula.eq u (numeralM n)) := by
  intro ts hc hs
  cases ts with
  | nil => intro u hu; cases hu
  | cons t ts0 =>
      rw [collapseTs] at hc
      injection hc with hc1 hc2
      intro u hu
      cases hu with
      | head =>
          exact numOfD_grounded hΓ hlift ⟨hc1, fun ρ => by
            have hx := hs ρ; simp only [substTs] at hx; injection hx⟩
      | tail _ hu0 =>
          exact numOfD_grounded_list hΓ hlift ts0 hc2
            (fun ρ => by have hx := hs ρ; simp only [substTs] at hx; injection hx) u hu0
end


/-! ### La DP del fragmento con `/₂` — 23 de 34 -/

def ctxD (insts : List Formula) : List Formula :=
  arithTDAxioms ++ insts.map inductionFormula

theorem axD' {insts : List Formula} {g : Formula} (h : List.Mem g arithTDAxioms) :
    ctxD insts ⊢ᵢ g := Derivesᵢ.hyp _ _ (List.mem_append_left _ h)

theorem arithTDAxioms_sentence (g : Formula) (hg : List.Mem g arithTDAxioms) :
    collapseF LQtd (substF zeroS g) = g :=
  eq_of_map_self (f := fun g => collapseF LQtd (substF zeroS g)) arithTDAxioms
    arithTDAxioms_sentences g hg

theorem hNumD_fragment {insts : List Formula}
    (hlift : (ctxD insts).map (liftFormula 0) = ctxD insts) : ∀ t : Term, Grounded LQtd t →
    ∃ n : Nat, ctxD insts ⊢ᵢ (Formula.eq t (numeralM n)) :=
  fun _ ht => numOfD_grounded (fun _ hg => axD' hg) hlift ht

/-- ⭐⭐ **Los 23 axiomas, barrados.** El vigesimotercero, `ax17`, es de Harrop. -/
theorem slash_arithTDAxioms {insts : List Formula}
    (hlift : (ctxD insts).map (liftFormula 0) = ctxD insts)
    (hcon : Not (ctxD insts ⊢ᵢ Formula.bottom)) :
    ∀ g, List.Mem g arithTDAxioms → Slash (ctxD insts) (Grounded LQtd) g := by
  have hA : ∀ g, List.Mem g arithTDAxioms → ctxD insts ⊢ᵢ g := fun _ hg => axD' hg
  intro g hg
  simp only [arithTDAxioms, arithTAxioms, arithAxioms, List.append] at hg
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax2_peano_succ_neq_zero rfl (axD' (List.Mem.head _))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax3_peano_succ_inj rfl (axD' (List.Mem.tail _ (List.Mem.head _)))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax4_add_zero rfl (axD' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax5_add_succ rfl (axD' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax6_add_comm rfl (axD' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax7_add_assoc rfl (axD' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax8_mul_zero rfl (axD' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax9_mul_succ rfl (axD' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax10_mul_comm rfl (axD' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax11_mul_assoc rfl (axD' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax12_mul_distrib rfl (axD' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_ax13 LQtd (by decide) (arithTD_of_arith hA) hlift hcon (hNumD_fragment hlift)
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax18_lt_irrefl rfl (axD' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_ax19 LQtd (arithTD_of_arith hA) (hNumD_fragment hlift)
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax_L1_in_nil rfl (axD' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax_pow_zero rfl (axD' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax_pow_succ rfl (axD' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax25_pred_zero rfl (axD' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax26_pred_succ rfl (axD' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax16_mod2_succ rfl (axD' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_ax21 LQtd (by decide) (axD' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))) (arithTD_of_arith hA) hcon (hNumD_fragment hlift)
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax24_mod2_of_even rfl (axD' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))
  rcases hg with _ | ⟨_, hg⟩
  · exact slash_of_isHarrop _ _ hcon ax17_div_mod_eq rfl (axD' (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))
  cases hg


/-- 🏁 La DP del fragmento con `/₂`, con instancias de inducción. -/
theorem qDisjunctionPropertyD (insts : List Formula)
    (hlift : (ctxD insts).map (liftFormula 0) = ctxD insts)
    (hcon : Not (ctxD insts ⊢ᵢ Formula.bottom))
    (hInd : ∀ g, List.Mem g (insts.map inductionFormula) →
      Slash (ctxD insts) (Grounded LQtd) (collapseF LQtd (substF zeroS g)))
    {A B : Formula}
    (hAB : collapseF LQtd (substF zeroS (Formula.or A B)) = Formula.or A B)
    (h : ctxD insts ⊢ᵢ Formula.or A B) :
    Or (ctxD insts ⊢ᵢ A) (ctxD insts ⊢ᵢ B) := by
  refine disjunction_property_of_slashed (ctxD insts) (Grounded LQtd) LQtd
    (fun _ hu => grounded_fix LQtd hu) (grounded_collapse_subst LQtd)
    zeroS (fun _ => grounded_zero LQtd) (fun g hg => ?_) hAB h
  rcases List.mem_append.mp hg with hcore | hind
  · rw [arithTDAxioms_sentence g hcore]
    exact slash_arithTDAxioms hlift hcon g hcore
  · exact hInd g hind

/-- 🏁🏁🏁 **23 de los 34** — sin instancias de inducción: la consistencia y nada más. -/
theorem qDisjunctionProperty_arithTD
    (hcon : Not (ctxD [] ⊢ᵢ Formula.bottom))
    {A B : Formula}
    (hAB : collapseF LQtd (substF zeroS (Formula.or A B)) = Formula.or A B)
    (h : ctxD [] ⊢ᵢ Formula.or A B) :
    Or (ctxD [] ⊢ᵢ A) (ctxD [] ⊢ᵢ B) := by
  refine qDisjunctionPropertyD [] (by rfl) hcon ?_ hAB h
  intro g hg
  cases hg

end PeanoRF.HA
