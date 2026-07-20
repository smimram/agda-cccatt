Unbiased cartesian closed categories formalized in Agda
=======================================================

This is the formalization associated to the paper [_An unbiased simply typed combinatory logic_](http://www.lix.polytechnique.fr/Labo/Samuel.Mimram/docs/mimram_cccatt.pdf). More precisely, we show the equivalence between

1. our calculus of unbiased combinators and
2. simply typed combinatory logic.

There are two variants where the second calculus is either

- [combinatory logic](combinatory-logic)
- [categorical combinators](categorical-combinators)

The first one follows more closely the paper but lacks the formalization of pasting schemes (which are simply postulated in [Ty.agda](combinators/Ty.agda)). The second one has no postulate.

The *combinatory logic* formalization consists mainly of the following files:

- [Ty.agda](combinatory-logic/Ty.agda): type variables, types, type substitutions,
- [CL.agda](combinatory-logic/CL.agda): simply typed combinatory logic,
- [CT.agda](combinatory-logic/CT.agda): unbiased combinators,
- [Equivalence.agda](combinatory-logic/Equivalence.agda): the equivalence between the above two.

The *categorical combinators* formalization consists mainly of the following files:

- [Ty.agda](categorical-combinators/Ty.agda): type variables, types, type substitutions,
- [PS.agda](categorical-combinators/PS.agda): pasting schemes,
- [CC.agda](categorical-combinators/CC.agda): categorical combinators,
- [CCNF.agda](categorical-combinators/CCPS.agda): weak normalization of categorical combinators,
- [CCPS.agda](categorical-combinators/CCPS.agda): pasting schemes are uniquely inhabited in categorical combinators,
- [CT.agda](categorical-combinators/CC.agda): unbiased combinators,
- [Equivalence.agda](categorical-combinators/Equivalence.agda): the equivalence between the above two.

We have also tried a [cubical approach](experiments/cubical) which did not go through.
