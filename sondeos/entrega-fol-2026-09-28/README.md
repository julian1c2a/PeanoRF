# Sondeo · la entrega (C), compilada contra FOL solo

**Última actualización:** 2026-09-28

Los siete módulos de `PeanoRF/Calculus/` que bajan a FOL (`Subst`, `DerivesI`, `SubstDerives`,
`Consistency`, `Eq`, `Collapse`, `Slash`), **tal como quedan en PRF-050** (`99ee4de`), con un
único cambio: los imports hermanos pasan de `PeanoRF.Calculus.` a `Spike.`.

**El control es el compilador**: este proyecto tiene **un solo `require`**, `FOL`, así que
cualquier import de RPP o de Peano rompe su build. Es la condición del propietario de FOL
(«FOL no depende de nada más allá de sí mismo»), comprobable desde nuestro árbol.

```bash
cd sondeos/entrega-fol-2026-09-28 && lake build && lake env lean Check.lean
```

Medido el 2026-09-28 contra FOL@`b919b57`: build verde (25 jobs) y **240 constantes, todas en
`[propext, Quot.sound]`** (`Check.lean` las recorre todas, compañeras generadas incluidas).
`Check.lean` está probado en los dos sentidos: con un `Classical.em` metido a propósito da 1
fuera.

Complementa, no sustituye, la medición de PRF-050: allí se compilaron los siete **dentro de una
copia de FOL** (`f2f7188`) y el cierre de imports resultó ser exactamente la cadena de quince
módulos de FOL. Aquella no se puede relanzar desde este repositorio; ésta sí.

⚠️ **De qué depende**: de FOL@`b919b57`, y en particular de lo que la carta 3 de FOL §3 garantiza
hasta la entrega (`posDepth`, las definiciones de `FOL.FOL`, `Derives₀` y sus 18 constructores).
Si FOL cambia algo de eso, esta medición caduca aunque esté bien hecha.
