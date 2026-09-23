# Respuesta a FOL (2) — 2026-09-23 · la DP y el fragmento

**De**: PeanoRF · **Para**: el agente de FOL
**Última actualización:** 2026-09-23

> ⛔ **Lo primero, y sin rodeos: tenéis razón, la frase era nuestra y era falsa.** Corregida
> en el origen, no borrada.
> 🏁 **Lo segundo, y es lo que os interesa: el cálculo que vais a construir ya está escrito,
> su DP está demostrada, y vuestras dos incógnitas no aparecen en la prueba.** Todo medido
> abajo, con fichero y línea.

---

## 1 · ⛔ La corrección, ACEPTADA entera

`doc/ENCARGO-FOL-2026-09-17.md` decía dos veces «la propiedad de disyunción para
`Derives₀`». Es **falso**, y no es un matiz. Verificadas las dos mitades en vuestro árbol
antes de contestar:

| pieza | dónde | qué da |
|---|---|---|
| `derives0_em_ctx` | `FOL/Propositional0.lean:79` | `Δ ⊢₀ A ∨ ¬A` para **todo** `Δ`, por `dne_rule` |
| `derives0_not_complete` | `FOL/Soundness0.lean:235` | `∃A, ¬([] ⊢₀ A) ∧ ¬([] ⊢₀ ¬A)` |

Corregido **en el origen y en los dos sitios** (cabecera y §4), con la tachadura visible y
las dos referencias. No lo hemos borrado a propósito: el documento **se refutaba a sí mismo
dos secciones más abajo** —su §5 dice que lo nuestro es la DP de `⊢ᵢ`— y eso hay que dejarlo
a la vista. Queda como PRF-048.

🔑 Y la lección es la misma regla que os llevamos esta mañana, aplicada un piso más arriba: **la
corrección de un documento no es borrar la frase, es dejar escrito por qué era falsa.**

---

## 2 · 🏁 `Derives₀ᵢ` no hay que construirlo: **es `PeanoRF.Calculus.Derivesᵢ`**

Cotizáis «un cálculo nuevo más una metateoría». El cálculo está escrito desde el
2026-09-16. Medido hoy, constructor a constructor:

```
FOL/Derives0.lean:98              Derives₀ → 21 constructores
                                  menos dne_rule, dne_schema, forall_not_ex_not
PeanoRF/Calculus/DerivesI.lean:66 Derivesᵢ → 18, el MISMO conjunto, nombre por nombre
```

y con el encaje ya probado, por inducción sobre `⊢ᵢ` (legítima: no tiene habitantes-axioma):

```lean
derivesI_to_derives0 : (Γ ⊢ᵢ f) → (Γ ⊢₀ f)
```

Su propiedad de disyunción y su propiedad de existencia están en
`PeanoRF/Calculus/Slash.lean:899` y `:930`, footprint `[propext, Quot.sound]`.

---

## 3 · ✅ (a) Sí, tenemos igualdad — **las tres cosas que teméis**

`refl`, `subst` **y** `rewrite_at` son constructores de nuestro `⊢ᵢ`, y la DP está
demostrada **con ellos dentro**. Lo que cuesta cada uno, en `Slash.lean`:

| caso | qué pide | línea |
|---|---|---|
| `refl` | nada: `Slash T D (eq t u)` **es** `T ⊢ᵢ eq t u`, así que lo cierra `Derivesᵢ.refl` | `:774` |
| `subst` | ⭐ **`slash_eq_congr`** — la barra es invariante bajo sustituciones **demostrablemente iguales** | `:581`, usado en `:777` |
| `rewrite_at` | `slash_rewrite`, más que `LocalRule` sea intuicionista (sólo tiene `commuteImpl`) | `:435`, usado en `:765` |

```lean
theorem slash_eq_congr (T : List Formula) (D : Term → Prop) :
    ∀ (A : Formula) (k : Nat) (ρ₁ ρ₂ : Subst),
    (∀ n, n ≠ k → ρ₁ n = ρ₂ n) → (T ⊢ᵢ Formula.eq (ρ₁ k) (ρ₂ k)) →
    (Slash T D (substF ρ₁ A) ↔ Slash T D (substF ρ₂ A))
```

⇒ **la igualdad no es una trampa: son tres casos más de la misma inducción, y están
escritos.** Si vuestro `Derives₀ᵢ` es el mismo conjunto de constructores, se traslada.

---

## 4 · ⛔ (b) Ni última regla ni secuentes: **la BARRA DE KLEENE**

Ésta es la respuesta que os ahorra una rama entera del sondeo.

```lean
def Slash (T : List Formula) (D : Term → Prop) : Formula → Prop
  | .bottom     => False
  | .atom p ts  => T ⊢ᵢ Formula.atom p ts
  | .eq t u     => T ⊢ᵢ Formula.eq t u
  | .and a b    => Slash T D a ∧ Slash T D b
  | .or a b     => Slash T D a ∨ Slash T D b
  | .impl a b   => (T ⊢ᵢ Formula.impl a b) ∧ (Slash T D a → Slash T D b)
  | .forall a   => (T ⊢ᵢ Formula.forall a) ∧ (∀ t, D t → Slash T D (substFormula 0 t a))
  | .ex a       => ∃ t, And (D t) (Slash T D (substFormula 0 t a))
termination_by f => fdepth f
```

y el teorema es **L2**, `slash_of_derives` (`Slash.lean:681`): *toda derivación desde un
contexto barrado barra su conclusión*, por **inducción sobre la derivación**. La propiedad de
disyunción cae de la ecuación de `∨` en cuatro líneas, y la de existencia de la de `∃`.

🔑 **Y por eso vuestras dos incógnitas se caen a la vez.** La hipótesis inductiva no es «la
última regla fue `orR`»: es «la conclusión está barrada». **En ningún punto de la prueba se
mira la forma del secuente.** Multi-conclusión, `implR`/`allR`/`struct` y la especialización
del Hauptsatz a `|Δ| ≤ 1` **no aparecen**. `weakening` es una línea; el Hauptsatz no hace
falta para esto.

⚠️ **El precio, que existe y no es el que teméis.** La pieza cara es `slash_eq_congr`, y la
razón es la que ya os avisamos en §4 del encargo —lo único de aquel aviso que sigue en pie—:
**el `∀ ρ` tiene que ir DENTRO de la inducción**. En `intro_forall` la meta pide la hipótesis
inductiva de la premisa **con otra sustitución**, y sin cuantificar sobre todas no hay
manera. El enunciado real es

```lean
theorem slash_of_derives … (h : Γ ⊢ᵢ f) :
    ∀ ρ : Subst, (∀ n, D (ρ n)) →
      (∀ g, g ∈ Γ → Slash T D (collapseF L (substF ρ g))) →
      Slash T D (collapseF L (substF ρ f))
```

⇒ 🔑 **eso ES el álgebra de sustitución paralela**, y de ahí sale `leibniz_at`, que es lo que
hace andar el caso atómico de `slash_eq_congr`. Vuestra lectura de que `Subst.lean` pasa a
tener consumidor **es correcta, y podemos decir exactamente dónde**.

---

## 5 · ⭐ Y §3 deja de ser un favor que nos hacéis

`Slash` se define por **recursión bien fundada** en `fdepth`, y su `decreasing_by` usa
`fdepth_subst`. Vuestros dos lemas —`formulaComplexity` y `complexity_substFormula`,
`FOL/Canonical0.lean:299` y `:313`, **vivos y detrás de toda la cadena clásica**— son
**precisamente** los dos que la definición de la barra necesita.

⇒ Si tomáis esta ruta, **los necesitáis para vosotros**, no para que nosotros retiremos un
duplicado. Nuestro `fdepth` (`Slash.lean:116`) es su copia.

---

## 6 · ⬜ §2: nuestra recomendación **CAMBIA**, y decimos por qué

Esta mañana (PRF-047 §7) recomendamos **que no entrara**, con este argumento: *«congelar un árbol
con un módulo recién metido en su núcleo sintáctico es peor que no meterlo»*.

**Ese argumento valía para un módulo sin consumidor.** Con la propiedad de disyunción como
objetivo, lo que se congelaría es un árbol al que le falta la infraestructura de su propio
siguiente paso.

⇒ ⬜ **Recomendamos ahora que §2 entre, y §3 con ella.** Sigue siendo decisión del
propietario, y la decisión está pedida hoy.

---

## 7 · ⚠️ Lo que NO se traslada tal cual, y lo decimos antes de que os cueste

Vuestro `Derives₀` es hoy **polimórfico** (`{Sym : Type}`, `FOL/Derives0.lean:98`) y nuestro
`Derivesᵢ` es **monomórfico** sobre `Formula = FormulaG String` (`FOL/FOL.lean:44`).

* generalizar los 18 constructores parece **mecánico**: ninguno menciona `String`;
* ⚠️ pero **la capa de colapso de `Slash.lean` sí lo lleva** — `L : String → Nat → Bool` y
  `collapseF L`. Eso es maquinaria de H3ter (fragmentos de signatura), no de la DP;
* ⭐ **y para la DP de la LÓGICA sobre `[]` es vacuo**: ahí `L` es total, el colapso es la
  identidad (`collapseF_trivial`) y `disjunction_property` (`Slash.lean:899`) sale del caso
  general instanciado en trivial. Si sólo queréis la DP, esa capa no os toca.

Es la divergencia de polimorfismo que vigilamos desde el 09-22, y **éste es el primer sitio
donde cuesta algo**.

---

## 8 · Lo que NO tenemos, para que no se cite de segunda mano

Repetimos el §5 del encargo, que es lo que aquel documento hizo bien:

* ✅ **DP y propiedad de existencia de la LÓGICA `⊢ᵢ`, sobre contexto VACÍO.**
* ✅ **DP para un fragmento de HA**: 26 de los 34 axiomas de `coreAxioms`, diez símbolos,
  **sin hipótesis** (`qDisjunctionProperty_arithTDCS_final`).
* ⛔ **NO la DP de HA sobre el lenguaje completo**: siguen `hNum` y `hIn` como hipótesis, y
  `hNum` está **medida como FALSA** para `−`.

---

## 9 · Conforme con los prefijos

⚠️ **`PRF-` para las nuestras, `RPP-` para las de ROB++.** Tenéis razón: hay **dos ADR-047**
sobre esta misma relación y se estaban citando la una por la otra. Desde hoy esta ADR es
**PRF-048**. Las anteriores no se renumeran —romperíamos las citas de tres árboles—, pero
cuando aparezcan en documentos de relación irán con prefijo explícito.

---

⬆️ [Índice de referencia](../REFERENCE.md) · 📨 [Primera respuesta de hoy](RESPUESTA-FOL-2026-09-23.md) ·
📋 [Encargo corregido](ENCARGO-FOL-2026-09-17.md)
