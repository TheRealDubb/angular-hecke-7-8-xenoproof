import AngularPhysicalFirstSectorEnergy
import OAI.NumberTheory.DirichletL.Moments.FirstRetainedSector

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace OAI.SevenEighths.Angular.PlainRows.FirstPhysical
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSourceRow CenteredMomentFirstSectorLocalization CenteredMomentFirstCommonFourierTransport
open PlainRows CenteredMomentCommonSectors
open CenteredMomentFirstSectors CenteredMomentCompleteCommon CenteredMomentSecondSectorColumns
open CenteredMomentHeckeColumnWindow
open CenteredMomentSupport CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

open CenteredMomentFirstRetainedSector (retainedKernel retainedKernel_eq)

theorem retainedEnergy_common_sectors (η : AngularCharacter) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    PlainRows.retainedEnergy η m A t S β W K X Z ξ=
      ∑ p∈commonLabels (supportedColumns S) (supportedColumns S),
        ∑ q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
          ((β q.1*rowWeight η m A 1 t q.1)*star (β q.2*rowWeight η m A 1 t q.2))*
            retainedKernel q.1 q.2 W K X Z ξ := by
  let F := fun I J : Ideal O=>((β I*rowWeight η m A 1 t I)*star (β J*rowWeight η m A 1 t J))*
    retainedKernel I J W K X Z ξ
  have he : PlainRows.retainedEnergy η m A t S β W K X Z ξ=
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

theorem retained_sector_independent (η : AngularCharacter) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((β q.1*rowWeight η m A 1 t q.1)*star (β q.2*rowWeight η m A 1 t q.2))*
        retainedKernel q.1 q.2 W K X Z ξ)=
      rowWeight η m A 1 t C*star (rowWeight η m A 1 t D)*
        ∑ I : sectorPool C hC S,∑ J : sectorPool D hD S,
          if IsCoprime (I:Ideal O) (J:Ideal O) then
            ((β (C*I)*rowWeight η m A 1 t I)*star (β (D*J)*rowWeight η m A 1 t J))*
              retainedKernel (C*I) (D*J) W K X Z ξ else 0 := by
  rw [←independent_sector_pools C D hC hD hCD S
    (fun I J=>((β (C*I)*rowWeight η m A 1 t I)*star (β (D*J)*rowWeight η m A 1 t J))*
      retainedKernel (C*I) (D*J) W K X Z ξ)]
  rw [pairSector_double_sum C D hC hD hCD _ _
    (fun I hI=>(Finset.mem_filter.mp hI).2.1) (fun I hI=>(Finset.mem_filter.mp hI).2.1)
    (fun I J=>((β I*rowWeight η m A 1 t I)*star (β J*rowWeight η m A 1 t J))*
      retainedKernel I J W K X Z ξ)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  split_ifs <;> simp only [map_mul,star_mul,mul_zero]
  ring

end OAI.SevenEighths.Angular.PlainRows.FirstPhysical

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.retainedEnergy_common_sectors
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.retainedEnergy_common_sectors

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.retained_sector_independent
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.retained_sector_independent
