import AngularPhysicalSecondLocalization
import AngularPhysicalSecondSectorRetained
import OAI.NumberTheory.DirichletL.Moments.SecondRetainedAggregate

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
theorem retainedEnergy_common_sectors (η : AngularCharacter) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) :
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑ p∈commonLabels (supportedColumns S) (supportedColumns S),
        ∑ q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
          ((β q.1*heightCoeff η t q.1)*star (β q.2*heightCoeff η t q.2))*
            retainedKernel q.1 q.2 W K Tsec Z ξ := by
  let F := fun I J : Ideal O=>((β I*heightCoeff η t I)*star (β J*heightCoeff η t J))*
    retainedKernel I J W K Tsec Z ξ
  have he : secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑ I : supportedColumns S,∑ J : supportedColumns S,F I J := by
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only [F]
    rw [retainedKernel_eq I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2]
  rw [he]
  have hj (I : Ideal O) : (∑ J : supportedColumns S,F I J)=∑ J∈supportedColumns S,F I J :=
    Finset.sum_coe_sort _ _
  simp_rw [hj]
  rw [Finset.sum_coe_sort (supportedColumns S) (fun I=>∑ J∈supportedColumns S,F I J)]
  exact sum_common_sectors _ _ F

theorem retained_sector_independent (η : AngularCharacter) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((β q.1*heightCoeff η t q.1)*star (β q.2*heightCoeff η t q.2))*
        retainedKernel q.1 q.2 W K Tsec Z ξ)=
      heightCoeff η t C*star (heightCoeff η t D)*
        ∑ I : sectorPool C hC S,∑ J : sectorPool D hD S,
          if IsCoprime (I:Ideal O) (J:Ideal O) then
            ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
              retainedKernel (C*I) (D*J) W K Tsec Z ξ else 0 := by
  rw [←independent_sector_pools C D hC hD hCD S
    (fun I J=>((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
      retainedKernel (C*I) (D*J) W K Tsec Z ξ)]
  rw [pairSector_double_sum C D hC hD hCD _ _
    (fun I hI=>(Finset.mem_filter.mp hI).2.1) (fun I hI=>(Finset.mem_filter.mp hI).2.1)
    (fun I J=>((β I*heightCoeff η t I)*star (β J*heightCoeff η t J))*
      retainedKernel I J W K Tsec Z ξ)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  split_ifs <;> simp only [heightCoeff_mul,star_mul,mul_zero]
  ring

end OAI.SevenEighths.Angular.PlainRows.SecondSource

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.retainedEnergy_common_sectors
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.retainedEnergy_common_sectors

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.retained_sector_independent
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.retained_sector_independent
