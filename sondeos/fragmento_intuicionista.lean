-- SONDEO 2026-09-23 — ¿es `Derivesᵢ` EXACTAMENTE `Derives₀` menos los tres clásicos?
--
-- FOL decidió ir a por la propiedad de disyunción y cotizó el fragmento intuicionista
-- `Derives₀ᵢ = Derives₀ − {dne_rule, dne_schema, forall_not_ex_not}` como «un cálculo nuevo
-- más una metateoría». Nuestra respuesta (PRF-048) es que **ese cálculo ya está escrito**:
-- es `PeanoRF.Calculus.Derivesᵢ`.
--
-- ⚠️ Pero eso es una afirmación sobre DOS listas de constructores, una de ellas en un árbol
-- ajeno que se mueve varias veces al día. Contarlas a ojo es exactamente la séptima forma de
-- dar verde sin comprobar. Este sondeo las pone a que las cuente el KERNEL.
--
-- 🔑 El truco es un `cases` EXHAUSTIVO: si FOL añade un constructor a `Derives₀`, el `match`
-- de abajo deja de cubrir todos los casos y **este fichero se pone rojo**. Si lo quita,
-- también. Es un centinela, no una prueba.
--
-- Uso: lake env lean sondeos/fragmento_intuicionista.lean

import PeanoRF.Calculus.DerivesI
open FOL
namespace PeanoRF.Calculus

set_option autoImplicit false

/-! ## 1 · `Derives₀` tiene EXACTAMENTE estos 21 constructores

    18 comunes + los **tres clásicos**, marcados. -/

theorem derives0_tiene_21 {Γ : List Formula} {f : Formula} (h : Γ ⊢₀ f) : True := by
  cases h with
  | hyp => trivial
  | intro_impl => trivial
  | elim_impl => trivial
  | intro_and => trivial
  | elim_and_l => trivial
  | elim_and_r => trivial
  | intro_or_l => trivial
  | intro_or_r => trivial
  | elim_or => trivial
  | intro_forall => trivial
  | elim_forall => trivial
  | intro_ex => trivial
  | elim_ex => trivial
  | bot_elim => trivial
  | weakening => trivial
  | rewrite_at => trivial
  | dne_rule => trivial            -- ⛔ CLÁSICO
  | dne_schema => trivial          -- ⛔ CLÁSICO
  | forall_not_ex_not => trivial   -- ⛔ CLÁSICO
  | refl => trivial
  | subst => trivial

/-! ## 2 · `Derivesᵢ` tiene EXACTAMENTE los otros 18 -/

theorem derivesI_tiene_18 {Γ : List Formula} {f : Formula} (h : Γ ⊢ᵢ f) : True := by
  cases h with
  | hyp => trivial
  | intro_impl => trivial
  | elim_impl => trivial
  | intro_and => trivial
  | elim_and_l => trivial
  | elim_and_r => trivial
  | intro_or_l => trivial
  | intro_or_r => trivial
  | elim_or => trivial
  | intro_forall => trivial
  | elim_forall => trivial
  | intro_ex => trivial
  | elim_ex => trivial
  | bot_elim => trivial
  | weakening => trivial
  | rewrite_at => trivial
  | refl => trivial
  | subst => trivial

/-! ## 3 · Y los tres que faltan NO son derivables como reglas admisibles aquí

    ⚠️ Esto **no** se mide con un `cases`: que `Derivesᵢ` no tenga el constructor no dice
    que la regla no sea admisible. Lo que sí está medido, y es el teorema del proyecto, es
    que los dos cálculos **no coinciden**: `derivesI_ne_derives0`. -/

/-- ⭐ **La igualdad está dentro**: `refl`, `subst` y `rewrite_at` son constructores de `⊢ᵢ`,
    y la propiedad de disyunción está demostrada CON ellos. Es la respuesta a la pregunta
    (a) de FOL, y aquí se ve que los tres tipan. -/
example (t : Term) : ([] : List Formula) ⊢ᵢ Formula.eq t t := Derivesᵢ.refl _ t

/-- El encaje, que es la otra mitad de la respuesta: lo intuicionista entra en `⊢₀`. -/
example {Γ : List Formula} {f : Formula} (h : Γ ⊢ᵢ f) : Γ ⊢₀ f := derivesI_to_derives0 h

end PeanoRF.Calculus

/-! ## Lo que este sondeo mide, y lo que NO

    ✅ **MEDIDO**: los conjuntos de constructores son los que decimos — 21 y 18, nombre por
    nombre—, y **el fichero se pone rojo solo** si FOL añade o quita uno. Eso convierte la
    afirmación central de PRF-048 en un centinela, no en una frase.

    ⛔ **NO medido aquí**: que `Derivesᵢ` sea *cerrado* bajo las tres reglas clásicas es
    falso, y eso sí es un teorema del proyecto —`derivesI_ne_derives0`—, no de este sondeo.

    ✅ **Y el centinela está PROBADO, no supuesto**: se le quitó una alternativa y dio
    «Alternative `forall_not_ex_not` has not been provided»; se le puso un nombre inventado y
    dio «Invalid alternative name». Un control que no se ha visto fallar puede ser vacuo.

    ⚠️ Y una reserva de alcance: `Derives₀` es hoy polimórfico (`{Sym : Type}`) y `Derivesᵢ`
    monomórfico sobre `Formula = FormulaG String`. Este sondeo compara la instancia
    `Sym = String`. Ver PRF-048 §7. -/
