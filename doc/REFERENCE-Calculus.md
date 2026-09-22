# REFERENCE · Calculus — el cálculo `⊢ᵢ`, su solidez y la barra de Kleene

**Last updated:** 2026-09-22
**Autor**: Julián Calderón Almendros

> **Nodo temático del sistema REFERENCE** (AI-GUIDE §0.5).
> ⬆️ Índice raíz: **[REFERENCE.md](../REFERENCE.md)** · catálogo de los 18 módulos, grafo de
> dependencias y teoremas de cabecera.
> ↔️ Nodos hermanos: **[REFERENCE-HA.md](REFERENCE-HA.md)** (la Aritmética de Heyting, que se
> construye sobre este cálculo) · **[REFERENCE-Meta.md](REFERENCE-Meta.md)** (contacto, gate
> y capa ω).

---

## 1. Qué cubre este nodo

El **cálculo sujeto** y todo lo que se demuestra sobre él: solidez, consistencia,
sustitución, colapso y la barra de Kleene.

| módulo | qué es | § |
|---|---|---|
| [`PeanoRF/Calculus/DerivesI.lean`](../PeanoRF/Calculus/DerivesI.lean) | **`⊢ᵢ`**, 18 constructores, ninguno clásico | 2.1 |
| [`PeanoRF/Calculus/Eq.lean`](../PeanoRF/Calculus/Eq.lean) | igualdad y especialización sobre `⊢ᵢ` | 2.2 |
| [`PeanoRF/Calculus/Soundness.lean`](../PeanoRF/Calculus/Soundness.lean) | 🏁 **H3**: la solidez, demostrada **constructivamente** | 2.3 |
| [`PeanoRF/Calculus/Consistency.lean`](../PeanoRF/Calculus/Consistency.lean) | la consistencia **sin un solo modelo** | 2.4 |
| [`PeanoRF/Calculus/Slash.lean`](../PeanoRF/Calculus/Slash.lean) | 🏁🏁🏁 **H3bis**: la barra, y `⊢ᵢ ≠ ⊢₀` | 2.5 |
| [`PeanoRF/Calculus/Subst.lean`](../PeanoRF/Calculus/Subst.lean) | el álgebra de sustituciones **paralelas** | 2.6 |
| [`PeanoRF/Calculus/SubstDerives.lean`](../PeanoRF/Calculus/SubstDerives.lean) | `⊢ᵢ` cerrado bajo sustitución | 2.7 |
| [`PeanoRF/Calculus/Collapse.lean`](../PeanoRF/Calculus/Collapse.lean) | el colapso de símbolos ajenos, y `Grounded` | 2.8 |

⚠️ **`Derivesᵢ` es el SUJETO, no la herramienta.** `FOL.Derives` resultó **no poder tener
solidez** (`inconsistencia_de_cualquier_solidez`, aguas arriba): es herramienta. Todo lo que
este proyecto afirma se afirma sobre `⊢ᵢ` (ADR-017).

---

## 2. Módulos

## 2.1 `Calculus/DerivesI.lean` — `⊢ᵢ`, el cálculo SUJETO

**Fichero**: [`PeanoRF/Calculus/DerivesI.lean`](../PeanoRF/Calculus/DerivesI.lean)

**Namespace**: `PeanoRF.Calculus`
**Dependencies**: `PeanoRF.Prelim`, `FOL.Derives0`
**Last updated**: 2026-09-16
**Status**: ✅ Completo
**@axiom_system**: ninguno — **0 habitantes-axioma** (por eso se puede inducir sobre él)
**@importance**: **foundational**

El objeto central del proyecto (ADR-017). Deducción natural **intuicionista, finitaria y
sin habitantes-axioma**: los 21 constructores de `FOL.Derives₀` menos los tres clásicos.

**Definición**:

```lean
inductive Derivesᵢ : List Formula → Formula → Prop
infix:50 " ⊢ᵢ " => Derivesᵢ
```

**Los 18 constructores**, por familias:

| familia | constructores |
|---|---|
| hipótesis | `hyp` |
| implicación | `intro_impl`, `elim_impl` |
| conjunción | `intro_and`, `elim_and_l`, `elim_and_r` |
| disyunción | `intro_or_l`, `intro_or_r`, `elim_or` |
| cuantificadores | `intro_forall`, `elim_forall`, `intro_ex`, `elim_ex` |
| ⊥ | `bot_elim` (*ex falso*, intuicionista — **no** es doble negación) |
| estructural | `weakening`, `rewrite_at` |
| igualdad | `refl`, `subst` |

⛔ **Los tres que NO están, y por qué**: `dne_rule`, `dne_schema` y `forall_not_ex_not`
son clásicos (M-1). Y la ω-regla `gen_rule` tampoco, porque `Derives₀` ya la había
dejado fuera (M-7).

**Teoremas**:

| nombre | notación matemática | firma Lean 4 | footprint |
|---|---|---|---|
| `derivesI_to_derives0` | `Γ ⊢ᵢ f  ⟹  Γ ⊢₀ f` | `(Γ ⊢ᵢ f) → (Γ ⊢₀ f)` | `propext` |
| `derivesI_to_derives` | `Γ ⊢ᵢ f  ⟹  Γ ⊢ f` | `(Γ ⊢ᵢ f) → (Γ ⊢ f)` | `propext` |

⭐ `derivesI_to_derives0` se prueba **por inducción sobre `⊢ᵢ`**, y esa inducción es
legítima precisamente porque el inductivo no tiene habitantes-axioma (M-11 de RPP). Sobre
`⊢` sería ilegítima.

⚠️ **Las recíprocas NO valen, y a propósito.** `⊢₀` tiene las tres reglas clásicas y `⊢`
tiene además la ω-regla y 7 habitantes-axioma. La asimetría **es** la tesis del proyecto:
lo nuestro entra en su mundo, lo suyo no entra en el nuestro.

---

## 2.2 `Calculus/Eq.lean` — igualdad sobre `⊢ᵢ`

**Fichero**: [`PeanoRF/Calculus/Eq.lean`](../PeanoRF/Calculus/Eq.lean)

**Namespace**: `PeanoRF.Calculus`
**Dependencies**: `PeanoRF.Calculus.DerivesI`
**Last updated**: 2026-09-16
**Status**: ✅ Completo
**@importance**: high

El **coste medido de la migración** (ADR-017): aguas arriba estos lemas existen, pero
enunciados sobre `⊢`, y los teoremas de `⊢` no bajan a `⊢ᵢ` — sólo suben. Son cinco, y
las pruebas son las mismas con los constructores renombrados.

| nombre | notación matemática | firma Lean 4 |
|---|---|---|
| `eqI_refl` | `Γ ⊢ᵢ t = t` | `(t : Term) → Γ ⊢ᵢ (Formula.eq t t)` |
| `eqI_symm` | `Γ ⊢ᵢ t₁ = t₂  ⟹  Γ ⊢ᵢ t₂ = t₁` | `Γ ⊢ᵢ (.eq t₁ t₂) → Γ ⊢ᵢ (.eq t₂ t₁)` |
| `eqI_trans` | `t₁ = t₂, t₂ = t₃  ⟹  t₁ = t₃` | `Γ ⊢ᵢ (.eq t₁ t₂) → Γ ⊢ᵢ (.eq t₂ t₃) → Γ ⊢ᵢ (.eq t₁ t₃)` |
| `eqI_congr_succ` | `t₁ = t₂  ⟹  σt₁ = σt₂` | `Γ ⊢ᵢ (.eq t₁ t₂) → Γ ⊢ᵢ (.eq (succ t₁) (succ t₂))` |
| `specI` | `Γ ⊢ᵢ ∀A  ⟹  Γ ⊢ᵢ A[t]` | `Γ ⊢ᵢ (.forall A) → (t : Term) → Γ ⊢ᵢ substFormula 0 t A` |

Las tres primeras usan la misma táctica: un testigo `f` con `#0` y `liftTerm 0 t₁`, y
`Derivesᵢ.subst` + `Derivesᵢ.refl`. `specI` es un alias de `elim_forall`.

---

## 2.3 `Calculus/Soundness.lean` — H3, el teorema de transferencia

**Fichero**: [`PeanoRF/Calculus/Soundness.lean`](../PeanoRF/Calculus/Soundness.lean)

**Namespace**: `PeanoRF.Calculus`
**Dependencies**: `PeanoRF.Calculus.DerivesI`, `FOL.Semantics`
**Last updated**: 2026-09-17
**Status**: ✅ Completo
**@importance**: **foundational**

| nombre | notación matemática | firma Lean 4 | footprint |
|---|---|---|---|
| `derivesI_soundness` | `Γ ⊢ᵢ f ⟹ Γ ⊨ f` | `(Γ ⊢ᵢ f) → satisfies Γ f` | **`propext, Quot.sound`** |
| `derivesI_consistent` | `[] ⊬ᵢ ⊥` | `([] ⊢ᵢ ⊥) → False` | **`propext, Quot.sound`** |

**Esto es el espejo hecho teorema**: de `HA ⊢ᵢ φ` se sigue que φ es verdadera en todo
modelo, y en particular en el estándar. Es exactamente lo que `FOL.Derives` **no podía
tener** (ADR-017).

🏁 **Cerrado el 2026-09-16.** La prueba es una **inducción directa sobre los 18
constructores**, no la composición con `derives0_soundness`. La conjetura de ADR-019 —que
el `Classical.choice` era el precio exacto de las tres reglas clásicas— se dio primero por
REFUTADA sobre una cadena contaminada y resultó CIERTA: el `Classical` venía de un `omega`
en `FOL.Metamath.Semantics.shift_updateEnv_comm`, ya corregido aguas arriba (`6d47e5b`).

---

## 2.4 `Calculus/Consistency.lean` — consistencia SIN semántica

**Fichero**: [`PeanoRF/Calculus/Consistency.lean`](../PeanoRF/Calculus/Consistency.lean)

**Namespace**: `PeanoRF.Calculus`
**Dependencies**: `PeanoRF.Calculus.DerivesI`, `FOL.Finitary0`
**Last updated**: 2026-09-17
**Status**: ✅ Completo
**@importance**: **foundational**

| nombre | notación matemática | firma Lean 4 | footprint |
|---|---|---|---|
| `consistI_syn` | `[] ⊬ᵢ ⊥` | `([] ⊢ᵢ ⊥) → False` | `propext, Quot.sound` |
| `notP_syn` | `[] ⊬ᵢ P` | `([] ⊢ᵢ atom "P" []) → False` | `propext, Quot.sound` |

El mismo enunciado que `derivesI_consistent`, por la vía **puramente sintáctica**: el
puente `⊢ᵢ → ⊢₀` compuesto con `FOL.Finitary0.derives0_consistent_fin`, que aguas arriba
sale de pasar a un cálculo de secuentes y ver que **ningún secuente sin corte concluye
`⊥`**. En toda la cadena no aparece un modelo.

⚠️ **La cifra NO mejora**: las dos rutas miden `[propext, Quot.sound]`. Lo que cambia es de
qué depende la prueba, y `#print axioms` **no distingue** «usa un modelo» de «no lo usa»
— la misma clase de ceguera que M-11.

⛔ **No es la consistencia de HA**, que es el teorema de Gentzen y pide inducción hasta
`ε₀`: fuera del núcleo finitario (ADR-016). Aquí el contexto es **vacío**.

⭐ `notP_syn` es **la mitad** de la separación `⊢ᵢ` ≠ `⊢₀` que persigue H3bis.

---

## 2.5 `Calculus/Slash.lean` — H3bis, la barra de Kleene

**Fichero**: [`PeanoRF/Calculus/Slash.lean`](../PeanoRF/Calculus/Slash.lean)

**Namespace**: `PeanoRF.Calculus`
**Dependencies**: `PeanoRF.Calculus.Consistency`
**Last updated**: 2026-09-17
**Status**: ✅ Completo — 🏁 **H3bis cerrado**
**@importance**: **foundational**

| nombre | notación matemática | firma Lean 4 | footprint |
|---|---|---|---|
| `fdepth` | complejidad lógica | `Formula → Nat` | — |
| `fdepth_subst` | `‖f[t/v]‖ = ‖f‖` | `fdepth (substFormula v t f) = fdepth f` | `propext` |
| `Slash` | `∣_{T,D} f` | `List Formula → (Term → Prop) → Formula → Prop` (recursión en `fdepth`) | `propext, Quot.sound` |
| `slash_derives` (**L1**) | `∣ f ⟹ ⊢ᵢ f` | `Slash f → ([] ⊢ᵢ f)` | `propext, Quot.sound` |
| `cut_context` | `Γ` derivable ⟹ `Γ` sobra | `(∀ g ∈ Γ, [] ⊢ᵢ g) → (Γ ⊢ᵢ f) → ([] ⊢ᵢ f)` | `propext` |
| **`slash_rewrite`** | la barra sobrevive a `rewrite_at` | — | `propext, Quot.sound` |
| `derives_empty_of_slashed` | contexto barrado ⇒ sin contexto | — | `propext, Quot.sound` |

⚠️ **Los DOS parámetros.** `T` es la teoría (etapa 1 de H3ter); `D` es el **dominio**
(etapa 2, 2026-09-18): las cláusulas de `∀` y `∃` cuantifican sobre `D`, no sobre todos los
términos. Sin `D`, **`ax19_lt_trichotomy` no se puede barrar** — su `∀` recorre términos de
los que HA no sabe nada. H3bis es la instancia `T = []`, `D = fun _ => True`.

⚠️ `D` entra en L2 como una **clausura**, `hDsub : ∀ ρ, (∀n, D (ρ n)) → ∀t, D (substT ρ t)`,
que es lo que piden `elim_forall` e `intro_ex`. Con `D = ClosedQTerm` esa clausura es
**FALSA**, y por eso falta aún la **forma (c)** — que L2 demuestre la barra de la instancia
COLAPSADA. Las obligaciones están medidas en `HA/Domain.lean` y en
`sondeos/collapse_parallel_probe.lean`.

**El objetivo**: la propiedad de disyunción, `[] ⊢ᵢ A ∨ B ⟹ [] ⊢ᵢ A ó [] ⊢ᵢ B`. Es el
**primer enunciado del proyecto que falla para `⊢₀`** — que prueba `P ∨ ¬P` sin probar
ninguna rama — y con `notP_syn` da la separación `⊢ᵢ ≠ ⊢₀` como teorema.

| **`slash_eq_congr`** | la barra no distingue términos demostrablemente iguales | `propext, Quot.sound` |
| **`slash_of_derives`** (**L2**, forma (c)) | `Γ ⊢ᵢ f`, `ρ` valuada en `D` y `Γ` barrado `⟹` `∣ (fρ)ᴸ` — la instancia **colapsada** | `propext, Quot.sound` |
| `collapseF_substF` | el colapso conmuta con la sustitución **paralela** — lo pide `rewrite_at` | `propext, Quot.sound` |
| `collapseF_trivial` | con `L` total el colapso es la identidad — **es lo que deja H3bis intacto** | `propext` |
| **`disjunction_property_of_slashed`** | DP relativa a una teoría barrada — H3bis es su caso `T = []` | `propext, Quot.sound` |
| 🏁 **`disjunction_property`** | `[] ⊢ᵢ A ∨ B ⟹ [] ⊢ᵢ A` ó `[] ⊢ᵢ B` — ⛔ contexto VACÍO, no HA | `propext, Quot.sound` |
| 🏁 **`existence_property`** | `[] ⊢ᵢ ∃A ⟹ ∃t, [] ⊢ᵢ A[t]` — ⛔ contexto VACÍO, no HA | `propext, Quot.sound` |
| `notNotP_syn` | `[] ⊬ᵢ ¬P` | `propext, Quot.sound` |
| 🏁🏁🏁 **`derivesI_ne_derives0`** | `∃φ, [] ⊢₀ φ ∧ [] ⊬ᵢ φ` | `propext, Quot.sound` |

⛔ **Las dos propiedades son de la LÓGICA, sobre contexto VACÍO.** Para **HA** no se
siguen: las instancias de inducción viven en `HA.ctx` y L2 exige que cada hipótesis del
contexto esté barrada — barrar el esquema de inducción es el caso difícil, y está sin
hacer. (Reserva añadida el 2026-09-18 al reauditar: faltaba, y la análoga de `consistI_syn`
se había escrito el mismo día.)

🏁 **Cerrado el 2026-09-17.** El testigo de la separación es `P ∨ ¬P`: `⊢₀` lo prueba
(`FOL.Propositional0.derives0_em_ctx`, y **sin `Classical.choice`**) y `⊢ᵢ` no, porque por la
propiedad de disyunción tendría que probar `P` o `¬P`, y ninguna lo es.

⭐ **El último obstáculo y cómo cayó**: el caso `Derivesᵢ.subst` de L2 pedía que la barra
fuera invariante bajo sustituciones demostrablemente iguales, y el caso del cuantificador se
atascaba porque `subst` sustituye sólo en el **índice 0**. La regla de Leibniz **en un
índice cualquiera** resulta **derivable** de la de índice 0 con el álgebra σ: se abstrae la
variable `k` al índice 0 y se vuelve (`leibniz_at`, §2.7). No hizo falta pedir nada
aguas arriba.

---

## 2.6 `Calculus/Subst.lean` — sustitución PARALELA

**Fichero**: [`PeanoRF/Calculus/Subst.lean`](../PeanoRF/Calculus/Subst.lean)

**Namespace**: `PeanoRF.Calculus`
**Dependencies**: `PeanoRF.Prelim`
**Last updated**: 2026-09-17
**Status**: ✅ Completo — ⚠️ **deuda declarada**: es infraestructura de SINTAXIS, o sea de FOL
**@importance**: **foundational**

| nombre | notación | firma |
|---|---|---|
| `substT` / `substTs` / `substF` | `tρ`, `fρ` | `Subst → Term/List Term/Formula → …` |
| `upS` / `consS` / `compS` | `ρ⁺`, `t·ρ`, `ρ∘τ` | las tres operaciones del álgebra |
| `liftS` / `singleS` | — | `liftFormula` y `substFormula` **como** sustituciones paralelas |
| `substF_comp`, `substF_id`, `substF_lift_consS`, `substFormula_upS`, `substF_upS_lift` | — | el álgebra |

Todo en `[propext]` / `[propext, Quot.sound]`. **FOL no tiene esto** (medido): sólo
sustitución de una variable. Pedido en `doc/ENCARGO-FOL-2026-09-17.md`; el módulo está
escrito para que puedan adoptarlo tal cual.

⚠️ **Las sustituciones se llaman `ρ`, no `σ`**: `peanolib` declara `σ` como NOTACIÓN
(`ℕ₀.succ`), así que no es un identificador válido en este árbol.

---

## 2.7 `Calculus/SubstDerives.lean` — `⊢ᵢ` cerrado bajo sustitución

**Fichero**: [`PeanoRF/Calculus/SubstDerives.lean`](../PeanoRF/Calculus/SubstDerives.lean)

**Namespace**: `PeanoRF.Calculus`
**Dependencies**: `Calculus.Subst`, `Calculus.DerivesI`, `FOL.Eigenvariable`
**Last updated**: 2026-09-17
**Status**: ✅ Completo
**@importance**: **foundational**

| nombre | notación matemática | footprint |
|---|---|---|
| `subst_getAt?` / `subst_replaceAt` / `subst_localRule` | navegación bajo `ρ` | `propext, Quot.sound` |
| `substF_substFormula` | `(f[t])ρ = (fρ⁺)[tρ]` | `propext, Quot.sound` |
| **`derivesI_subst`** | `Γ ⊢ᵢ f ⟹ Γρ ⊢ᵢ fρ` | `propext, Quot.sound` |
| ⭐ **`leibniz_at`** | Leibniz en un índice CUALQUIERA | `propext, Quot.sound` |

Hermano de `FOL.Lift0.derives0_lift`, con `ρ` donde ellos llevan `k`. ⚠️ El `∀ ρ` va
**dentro** de la inducción: en `intro_forall`, `elim_ex` y `rewrite_at` la hipótesis
inductiva se usa con otra sustitución.

---

## 2.8 `Calculus/Collapse.lean` — el colapso de símbolos ajenos

**Fichero**: [`PeanoRF/Calculus/Collapse.lean`](../PeanoRF/Calculus/Collapse.lean)

**Namespace**: `PeanoRF.Calculus`
**Dependencies**: `PeanoRF.Calculus.DerivesI`
**Last updated**: 2026-09-18
**Status**: ✅ Completo
**@importance**: **foundational**

| nombre | notación matemática | footprint |
|---|---|---|
| `collapseT` / `collapseF` | todo símbolo fuera de `L` ↦ `zero` | — |
| `collapseF_lift` / `collapseF_subst` | conmuta con lift y subst | `propext` |
| `collapse_getAt?` / `collapse_replaceAt` / `collapse_localRule` | navegación | `propext` |
| ⭐⭐ **`derivesI_collapse`** | `Γ ⊢ᵢ f ⟹ Γᴸ ⊢ᵢ fᴸ` | `propext, Quot.sound` |

**El obstáculo que retira**: `Term` es genérica y `elim_forall` instancia con cualquier
término, así que HA deriva instancias de sus axiomas sobre símbolos ajenos
(`sondeos/junk_probe.lean`) ⇒ **la DP falla sobre la sintaxis ambiente**. El colapso
**transforma** la derivación en vez de restringirla: una instanciación con basura pasa a ser
una con `collapseT L t`, que sí es del lenguaje.

⭐ **Sale más barato que `derivesI_subst`** porque el colapso **no cambia al entrar bajo una
ligadura**: `collapseF L (∀a) = ∀ (collapseF L a)`, con la misma `L`. Por eso su navegación
no va indexada por `posDepth` y la de la sustitución sí.

⚠️ Parametrizado por la signatura `L : String → Bool`, no clavado a Q⁺⁺. Y los **predicados**
ajenos no se colapsan, a propósito: la barra de un átomo es su derivabilidad, sin testigo.

---
## 3. Teoremas


| Teorema | Enunciado |
|---|---|
| `derivesI_to_derives0` | `Γ ⊢ᵢ f → Γ ⊢₀ f` — inducción sobre `⊢ᵢ`, legítima (0 habitantes-axioma) |
| `derivesI_to_derives` | `Γ ⊢ᵢ f → Γ ⊢ f` |
| `eqI_refl` · `eqI_symm` · `eqI_trans` · `eqI_congr_succ` · `specI` | igualdad y especialización sobre `⊢ᵢ` |


---

## 4. Notaciones

| Símbolo | Expande a | Módulo | Precedencia |
|---|---|---|---|
| `Γ ⊢ᵢ f` | `PeanoRF.Calculus.Derivesᵢ Γ f` | `Calculus/DerivesI.lean` | `infix:50` |

Misma precedencia que `⊢` (FOL) y `⊢₀` (`Derives₀`), a propósito: los tres se leen igual
y se distinguen sólo por el subíndice, que es el estrato.

---
## 5. Exports

```lean
-- PeanoRF.Calculus
Derivesᵢ                  -- el inductivo (18 constructores)
Γ ⊢ᵢ f                    -- notación (infix:50)
derivesI_to_derives0     -- puente a ⊢₀  ⇒  solidez heredada
derivesI_to_derives      -- puente a ⊢   ⇒  consumo de RPP en la dirección correcta
eqI_refl  eqI_symm  eqI_trans  eqI_congr_succ  specI
```

---

## 6. Lo que este nodo NO cubre

* los axiomas de HA, el dominio de la barra, el fragmento y el modelo sobre `ℕ` ⇒
  **[REFERENCE-HA.md](REFERENCE-HA.md)**. ⚠️ La barra vive aquí (`Slash T D`), pero **barrar
  los axiomas** es trabajo del nodo HA;
* el gate de pureza que mide los footprints que aparecen en estas tablas ⇒
  **[REFERENCE-Meta.md](REFERENCE-Meta.md)**;
* el grafo de dependencias completo y los teoremas de cabecera ⇒ **[REFERENCE.md](../REFERENCE.md)**.

---

⬆️ **[Volver al índice raíz](../REFERENCE.md)**
