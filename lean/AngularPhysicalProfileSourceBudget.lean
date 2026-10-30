import AngularPhysicalProfilePhysicalHeight
import AngularPhysicalOriginalPairData

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace OAI.SevenEighths.Angular.FiniteProfileExceptionalPhysical
open PlainRows DetectorAmplitude ExceptionalAmplitudePair FiniteProfileExceptional
open FiniteProfileExceptionalCommon CommonExceptionalSource
open PlainRows.CommonRows (Input withHeight)
open CenteredMomentFiniteProfileExceptional CenteredMomentHeckeWindowEnergy
open CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
universe u

open MeasureTheory
open FiniteProfileExceptionalPhysical ChildRows RayFourExpansion
open CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondHeightFamily (fixedBadMask)
open CenteredMomentSecondSectorColumns CenteredMomentSecondScaled CenteredMomentChildAssembly
open CenteredMomentRowNorm CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentForcing
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentLogDyadic
open CenteredMomentSmooth CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentHeckeColumnWindow
local instance {κ:Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

def sourceBudget {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Cr M:ℝ):ℝ:=
  K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
    Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
      (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
      2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ*
    ((1+2*Real.pi)^(4*J)*profileMass Sprofile s.toData s.toData p p J*
      frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm))*ExceptionalAmplitudePair.volume s.toData*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2

lemma sourceBudget_nonneg {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Cr M:ℝ)(hK:0≤K)(hZ:0≤Z)(hCr:0≤Cr):
    0≤sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M:=by
  have hp:=profileMass_nonneg Sprofile s.toData s.toData p p J
  have hf:=frozenProfile_nonneg s
  have hv:0≤ExceptionalAmplitudePair.volume s.toData:=(volume_pos s.toData).le
  unfold sourceBudget
  positivity

end OAI.SevenEighths.Angular.FiniteProfileExceptionalPhysical

#print axioms OAI.SevenEighths.Angular.FiniteProfileExceptionalPhysical.sourceBudget_nonneg
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FiniteProfileExceptionalPhysical.sourceBudget_nonneg
