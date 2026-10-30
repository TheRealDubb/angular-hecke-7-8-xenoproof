import AngularPhysicalSecondSourceSectors

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
theorem sourceGaussEnergy_poisson (τ : AngularCharacter) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    sourceGaussEnergy S β (heightCoeff τ t) W K=
      ∑ I : supportedColumns S,∑ J : supportedColumns S,
        ((β I*heightCoeff τ t I)*star (β J*heightCoeff τ t J))*
          ((K:ℂ)/((Real.sqrt (Ideal.absNorm (I:Ideal O):ℝ):ℂ)*(Real.sqrt (Ideal.absNorm (J:Ideal O):ℝ):ℂ)))*
            ∑' h : O,actualCorrelation (sourceGenerator S I) (sourceGenerator S J)
              (sourceGenerator_supported S I) (sourceGenerator_supported S J) (-h)*
              paperRadialFourier W (K*‖eisEmbedding h‖^2/
                ‖eisEmbedding (sourceGenerator S I*sourceGenerator S J)‖^2) := by
  rw [sourceGaussEnergy,gaussEnergy_poisson _ _ _ _ W K hK]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2,
    primary_span_supported J (Finset.mem_filter.mp J.property).2]
  ring

end OAI.SevenEighths.Angular.PlainRows.SecondSource

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.sourceGaussEnergy_poisson
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.sourceGaussEnergy_poisson
