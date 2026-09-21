/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.HA.SlashAxioms

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

  ⇒ **Queda una sola hipótesis: `hcon`.** Y ésa no es una deuda: Gödel II —que ROB++ va a
  demostrar— dice que es el precio exacto y que no se puede pagar por dentro.
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

end PeanoRF.HA
