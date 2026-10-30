import AngularPhysicalSecondChildFamily
import AngularPhysicalCanonicalRadial

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PhysicalBlock
open SecondFamily ChildState CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentSecondOriginalChildren (sourceRadial)
open CenteredMomentFirstAmplificationChoice (ballProfile ballProfile_nonneg)
open CenteredMomentSecondHeightFamily (fixedBadMask)
local notation "O" => ActualEisensteinCubic.O

lemma sourceRadial_eq_canonical {η:AngularCharacter}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→AngularCharacter}
    (h:Family η C D hC hD U τ)(χ:RayCharacter)(Q:Ideal O)(m:O)
    (hm:m≠0)(hml:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:O)∣m)(n:Fin 4→ℤ):
    sourceRadial (ExceptionalRows.nonexceptional η χ Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))
      ballProfile (dyadicScale (n 1)) (dyadicScale_pos _) (fun _z=>ballProfile_nonneg _)=
      canonicalRadial (τ χ) Q n:=by
  have he:ExceptionalRows.nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)=
      (fun z=>z≠0 ∧ ¬ExceptionalRows.FixedInducingRow (τ χ) Q fixedBadMask 1 z):=by
    funext z
    exact propext (h.nonexceptional_iff χ Q m z hm hml hm2)
  simp only [canonicalRadial,he]

end OAI.SevenEighths.Angular.PhysicalBlock

#print axioms OAI.SevenEighths.Angular.PhysicalBlock.sourceRadial_eq_canonical
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalBlock.sourceRadial_eq_canonical
