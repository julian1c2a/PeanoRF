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

set_option autoImplicit false

/-- Los 17 axiomas de `coreAxioms` cuyos símbolos de función son sólo `0`, `σ`, `+`, `*`, `^`.
    Medidos, no elegidos: `sondeos/fragmento_probe.lean`. -/
def arithAxioms : List Formula :=
  [ax2_peano_succ_neq_zero, ax3_peano_succ_inj, ax4_add_zero, ax5_add_succ,
   ax6_add_comm, ax7_add_assoc, ax8_mul_zero, ax9_mul_succ,
   ax10_mul_comm, ax11_mul_assoc, ax12_mul_distrib, ax13_lt_def,
   ax18_lt_irrefl, ax19_lt_trichotomy, ax_L1_in_nil, ax_pow_zero, ax_pow_succ]

/-- ⛔ **EVIDENCIA**: la cifra, verificada por el kernel. -/
theorem arithAxioms_length : arithAxioms.length = 17 := rfl

/-- ⛔ **EVIDENCIA.** ⭐ **Son sentencias del lenguaje de los NUMERALES**: ni variables libres ni símbolos
    fuera de los cinco. Por `rfl`, no por argumento. -/
theorem arithAxioms_sentences :
    arithAxioms.map (fun g => collapseF LQ (substF zeroS g)) = arithAxioms := by rfl

/-- ⛔ **EVIDENCIA.** ⭐ **De los 17, sólo dos no son de Harrop** — y los dos ya están barrados. -/
theorem arithAxioms_hard :
    arithAxioms.filter (fun g => !isHarrop g) = [ax13_lt_def, ax19_lt_trichotomy] := by rfl

/-- El fragmento es parte de Q⁺⁺: todo lo suyo es derivable donde lo sea `coreAxioms`.

    🏗️ **ANDAMIO**: sin uso hoy; es la pieza por la que entra el fragmento cuando se
    construya su DP. -/
theorem arithAxioms_sub : ∀ g, List.Mem g arithAxioms → List.Mem g coreAxioms := by
  intro g hg
  simp only [arithAxioms] at hg
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
  cases hg

end PeanoRF.HA
