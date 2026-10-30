import AngularPhysicalSecondDiscardedEnergy

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.PlainRows.SecondSource
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentLiveDomain
open CenteredMomentOriginalChildEnergy CenteredMomentFirstSectors CenteredMomentCommonSectors
open IdealMobiusDivisorSum ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentFourier CenteredMomentPoisson CenteredMomentSupportedCorrelation
open CenteredMomentRowNorm CenteredMomentSecondDiagonal
open CenteredMomentSecondSourceEnergy (secondSourceKernel)
open CenteredMomentSecondSourcePoisson (secondSourceKernel_poisson)
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceZeroEnergy CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceSecondZeroEnergy
  (secondZeroEnergy_filter sourceGenerator_span sourceGenerator_primary sourceGenerator_injective
   profileCoefficient_dvd)
local notation "O" => ActualEisensteinCubic.O

open CenteredMomentSecondTail CenteredMomentFirstScale CenteredMomentSectorLocalization
open CenteredMomentSecondLocalization (secondRetainedPair secondSourceKernel_split)
def secondRetainedEnergy (η : AngularCharacter) (t : ℝ) (S : Finset (Ideal O))
    (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*heightCoeff η t I)*star (c J*heightCoeff η t J))*
      secondRetainedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ

theorem sourceGaussEnergy_localized (η : AngularCharacter) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :
    CenteredMomentOriginalChildEnergy.sourceGaussEnergy S β (heightCoeff η t) W K=
      ((K:ℂ)*paperRadialFourier W 0)*sourceSecondZero S β η t+
      secondRetainedEnergy η t S β W K Tsec Z ξ+
      secondDiscardedEnergy η t S β W K Tsec Z ξ := by
  rw [sourceGaussEnergy_poisson η t S β W K hK]
  unfold sourceSecondZero secondZeroEnergy secondRetainedEnergy secondDiscardedEnergy
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  have he := secondSourceKernel_split I J (Finset.mem_filter.mp I.property).2
    (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ hK
  rw [secondSourceKernel_poisson I J (Finset.mem_filter.mp I.property).2
    (Finset.mem_filter.mp J.property).2 W K hK] at he
  simp only [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2,
    primary_span_supported J (Finset.mem_filter.mp J.property).2]
  convert congrArg (fun x : ℂ => ((β I*heightCoeff η t I)*star (β J*heightCoeff η t J))*x) he using 1 <;> ring

end OAI.SevenEighths.Angular.PlainRows.SecondSource

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.sourceGaussEnergy_localized
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.sourceGaussEnergy_localized
