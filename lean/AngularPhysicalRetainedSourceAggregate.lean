import AngularPhysicalRetainedSourceFrequency

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

open PhysicalBlock
open CenteredMomentCompleteCommon CenteredMomentSecondSectorColumns CenteredMomentSupport
open CenteredMomentSecondSourceRetained (retainedKernel retainedKernel_eq retainedKernel_physical)
open CenteredMomentSecondSectorRetained (physicalKernel)
open CenteredMomentSecondRetainedPair (physical_pair_summable)
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentSecondRetainedAggregate (commonLabels_supported)
theorem original_retained_energy_GV (η : AngularCharacter) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ))
    (K Tsec Z ξ : ℝ) (hK : 0<K) :
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑ p : commonLabels (supportedColumns S) (supportedColumns S),
        heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
          ∑ U : Finset (CommonIndex p.val.1 p.val.2),∑' h : O,
            if canonicalPartition p.val.1 p.val.2 U
                (nonunitFrequencyGenerator p.val.1 p.val.2 U*h) then
              sectorFrequency η t S β p.val.1 p.val.2
                (commonLabels_supported S _ _ p.property).1
                (commonLabels_supported S _ _ p.property).2
                (physicalKernel p.val.1 p.val.2 W K (frequencyRadius Tsec Z ξ))
                ((commonFrequencyGenerator p.val.1 p.val.2*
                  nonunitFrequencyGenerator p.val.1 p.val.2 U)*h) else 0 := by
  rw [retainedEnergy_common_sectors]
  rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro p hp
  exact original_retained_sector_GV η t S β p.val.1 p.val.2
    (commonLabels_supported S _ _ p.property).1 (commonLabels_supported S _ _ p.property).2
    (commonLabels_data _ _ _ _ p.property).2.2 W K Tsec Z ξ hK

end OAI.SevenEighths.Angular.PlainRows.SecondSource

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.original_retained_energy_GV
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.original_retained_energy_GV
