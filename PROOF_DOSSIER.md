# Submitted proof route

This document is a navigation aid and mathematical synopsis. The exact hypotheses and proofs are the unedited Lean sources. It does not replace an independent check of those sources or their imported results. Module paths below are relative to this packet; all direct imports are indexed in [metadata/MODULE_INDEX.json](metadata/MODULE_INDEX.json).

## Definitions and source function

The actual coefficient, unit compatibility, ideal descent and convergent series are defined in `AngularCharacter` and `AngularSeries`. `AngularFamilyContinuation` constructs the continued L-function from the primitive source and finite Euler factors. The submitted statement is attached to this function, rather than to an unspecified analytic surrogate. `AngularPhysicalPublicStatementCheck` checks the public type and identifies the right-half-plane series explicitly.

## Actual zero supremum

[AngularPhysicalZeroSupremum.lean](lean/AngularPhysicalZeroSupremum.lean) defines beta(n) as the supremum of the actual zero real parts over characters with |k|<=n, in Re(s)>0 and away from the principal pole, with 1/2 adjoined to make the set nonempty. Absolute convergence and the Euler product in Re(s)>1 give beta(n)<=1. The associated reciprocal is holomorphic to the right of this actual supremum. The definition does not assume the claimed numerical boundary.

## Physical probe and analytic estimates

[AngularPhysicalFinalAssembly.lean](lean/AngularPhysicalFinalAssembly.lean), definition `normalizedProbe`, specifies the compensated physical probe, its prime pools and slots, its scales Z^(17/48) and Z^(23/48), and its source/ray normalizer. The same function is used in both estimates below.

| Claim or transformation | Exact source entry point |
|---|---|
| Actual physical detector contraction, with constant before the target and explicit conductor factor | [AngularPhysicalDetectorActualPhysicalContraction](lean/AngularPhysicalDetectorActualPhysicalContraction.lean) |
| Principal residue, correction and normalized signal comparison | [AngularPhysicalPrincipalResidueBound](lean/AngularPhysicalPrincipalResidueBound.lean), [AngularPhysicalPrincipalNormalized](lean/AngularPhysicalPrincipalNormalized.lean) |
| Numerical parameter existence and positive saving | [AngularPhysicalDetectorActualBandParameters](lean/AngularPhysicalDetectorActualBandParameters.lean), [AngularPhysicalDetectorActualSignalBudget](lean/AngularPhysicalDetectorActualSignalBudget.lean) |
| Joining the detector estimate to the actual signal | [AngularPhysicalDetectorActualSignalContraction](lean/AngularPhysicalDetectorActualSignalContraction.lean) |
| Actual angular coefficient and finite residual coefficient | [AngularPhysicalLowRow](lean/AngularPhysicalLowRow.lean), [AngularPhysicalLowFiniteBase](lean/AngularPhysicalLowFiniteBase.lean), [AngularPhysicalLowRay](lean/AngularPhysicalLowRay.lean) |
| Completed inverse energy and selected physical energy | [AngularLowOriginalEnergy](lean/AngularLowOriginalEnergy.lean), [AngularPhysicalLowSelectedBound](lean/AngularPhysicalLowSelectedBound.lean) |
| Physical inverse normalization, Gram identity and total Gaussian sum | [AngularPhysicalLowPhysicalInverseBound](lean/AngularPhysicalLowPhysicalInverseBound.lean), [AngularPhysicalLowTupleGram](lean/AngularPhysicalLowTupleGram.lean), [AngularPhysicalLowGaussianSum](lean/AngularPhysicalLowGaussianSum.lean) |
| Normalized physical low bound | [AngularPhysicalLowNormalized](lean/AngularPhysicalLowNormalized.lean) |

For each fixed positive angular order n and target eta of order -n, the submitted low estimate gives J_eta(Z)=O_eta(Z^(3/16+loss)) for every loss>0. Its hypotheses specify prime support, source exclusions, profiles and normalization. The high comparison gives

    J_eta(Z) - signal_eta(Z)
        = O_eta(Z^(beta(n) - 11/16 - delta)),    delta > 0.

The parameter delta is fixed before eta. The final magnitude constant may depend on eta. Earlier in the chain, the detector-minus-principal estimate places its constant before eta with an explicit conductor-squared factor. These quantifier statements are different and should be read from their declarations.

The signal uses the excluded target and `PhysicalPrincipalResidue.sourceCorrection`. Analyticity and its distance-at-most-1/2 bound from 1 are supplied in `AngularPhysicalPrincipalResidueBound`. The source and profile witnesses used by the final assembly are supplied by [AngularPhysicalFixedWitnesses](lean/AngularPhysicalFixedWitnesses.lean) and the pinned `ParametersFixedSource` module. The source-header graph leads from these aggregate statements to the reflection, Poisson, moment induction, sieve, count and contour proofs they invoke.

## Mellin implication and removal of exclusions

In a proposed counterexample cap beta(n)>7/8, the final assembly chooses loss=(beta(n)-7/8)/2. Since 3/16=7/8-11/16, the low and high estimates have the form required by `PhysicalSignal.nonprincipal_nonzero_of_probe_bounds` in [AngularPhysicalSignalIdentity](lean/AngularPhysicalSignalIdentity.lean). Its conclusion is nonvanishing in Re(s)>beta(n)-m for a positive margin m fixed before the target. The exact margin is `Supremum.continuationMargin`; its positivity and boundary inequalities are explicit hypotheses and lemmas in that route.

[AngularPhysicalAnalyticDeletion](lean/AngularPhysicalAnalyticDeletion.lean) identifies the excluded L-function with the original function times finite Euler factors, first by the convergent series and then by analytic continuation for nonzero angular order. Nonvanishing of the excluded function therefore implies nonvanishing of the original function in the required region.

## Signed finite-cap closure

[AngularPhysicalCapClosure](lean/AngularPhysicalCapClosure.lean) gives the conditional closure with `NegativeOrderImprovement` as a stated premise. The final assembly **supplies this premise** using the preceding estimates and witnesses. The k=0 case is identified exactly with the pinned finite-order theorem; nonzero positive order is transported by the actual conjugation identity. Induction over n combines smaller orders with the improvement for the two top signs and contradicts the definition of beta(n) if beta(n)>7/8.

The final public theorem has no remaining analytic supplier parameter. The source of that claim, its successful compilation log, and the separately written expected-type check are all included for examination. This description does not substitute for verifying that the implication is valid.

## Norm twists and pole translation

[AngularPhysicalNormTwistNonvanishing](lean/AngularPhysicalNormTwistNonvanishing.lean) applies the existing physical norm-twist identities to the untwisted statement. For N^(+i tau) the argument shifts by -i tau; for N^(-i tau) it shifts by +i tau. Real parts are unchanged. The pole exclusions become 1+i tau and 1-i tau respectively, and coefficient and convergent-series identities are included in the same file.
