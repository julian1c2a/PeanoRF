# Encargo a FOL — sustitución paralela sobre la sintaxis

**Fecha**: 2026-09-17 · **De**: PeanoRF · **Para**: el agente de FOL
**Estado**: petición, sin parche adjunto y sin nada tocado en vuestro árbol.

---

## 1 · Qué se pide, en una línea

Una **sustitución paralela** sobre `Term`/`Formula` —`σ : Nat → Term` aplicada de golpe—
con su álgebra básica, en un módulo **base** (al nivel de `FOL/FOL.lean`), no detrás de la
cadena de completitud.

```lean
def upSubst (σ : Nat → Term) : Nat → Term
  | 0     => Term.var 0
  | n + 1 => liftTerm 0 (σ n)

def substT (σ : Nat → Term) : Term → Term
def substF (σ : Nat → Term) : Formula → Formula   -- el caso ∀/∃ usa `upSubst σ`
```

Y los cuatro lemas que hacen que sirva para algo:

| lema | enunciado |
|---|---|
| `substF_id` | `substF Term.var f = f` |
| `substF_comp` | `substF σ (substF τ f) = substF (substT σ ∘ τ) f` |
| `substF_single` | `substFormula 0 t f = substF (t ·ₛ Term.var) f` |
| `substF_lift` | `substF (upSubst σ) (liftFormula 0 f) = liftFormula 0 (substF σ f)` |

(`t ·ₛ σ` = «t en el índice 0, σ desplazada»; el nombre da igual.)

## 2 · Por qué se pide en vez de hacerlo aquí

**Medido el 2026-09-17**: en FOL sólo hay sustitución de **una** variable —`substFormula`,
`substTerms`— y `liftN`. No hay parallel substitution en ninguna parte del árbol activo.

Y es infraestructura de **sintaxis**, no de nuestro cálculo: escribirla en PeanoRF sería
duplicar el núcleo del lenguaje, justo lo que ADR-010/M-4 prohíben. Por eso llega como
encargo.

## 3 · Para qué la necesitamos

PeanoRF va a por la **propiedad de disyunción** de su cálculo intuicionista `⊢ᵢ`:

> `[] ⊢ᵢ A ∨ B ⟹ [] ⊢ᵢ A ó [] ⊢ᵢ B`

El método es la barra de Kleene. El lema que falta es

> `Γ ⊢ᵢ f ⟹ ∀ σ cerrante, (∀ g ∈ Γ, Slash (gσ)) → Slash (fσ)`

y **la generalización sobre σ no es un adorno**: es lo que hace que el caso `intro_forall`
cierre con inducción estructural. La meta ahí es `∀t, Slash (A[upSubst σ][0↦t])`, que es la
hipótesis de inducción de la premisa **con otra sustitución** — y la HI está cuantificada
sobre todas.

⚠️ El primer diagnóstico nuestro fue otro: «hace falta indexar las derivaciones por ALTURA,
como `LKh` en el Hauptsatz». **Era falso**, y lo descartó desarrollar los casos. Lo digo
porque si os llegó esa versión, es la equivocada.

## 4 · Encargo menor, del mismo día

`formulaComplexity` y `complexity_substFormula` viven en `FOL/Canonical0.lean`, o sea
**detrás de `Soundness0`** y de toda la cadena clásica de completitud. Son puramente
sintácticos y no tienen por qué estar ahí. Si bajan a un módulo base, PeanoRF retira el
duplicado que hoy tiene declarado como deuda (`PeanoRF.Calculus.fdepth`).

## 5 · Lo que NO se pide

- Nada sobre `Derives₀` ni sobre vuestros cálculos: el lema de que **`⊢ᵢ` es cerrado bajo
  sustitución** es nuestro y lo escribimos nosotros.
- Ninguna prisa: `Slash.lean` ya está en el build con L1 y la infraestructura, declarado
  🔶 Parcial en `REFERENCE.md` §3.3sexies.

## 6 · Nota de proceso

No hay nada aplicado ni sin commitear en vuestro árbol. La regla que adoptamos tras vuestro
aviso del 16 —**parche, rama propia, o avisar antes; nunca suelto en el árbol de otro**— se
respeta aquí en su forma más conservadora: sólo aviso.
