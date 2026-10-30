import AngularPhysicalFirstAllocation
import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceOriginalColumn

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows.FirstPhysical
open CanonicalQuadraticSieve ConcretePrimeRowBridge CanonicalRowCompletion
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationLiveMask CenteredMomentLiveDomain CenteredMomentRemainingBox
open CenteredMomentGaussEnergy CenteredMomentSourceAllocationEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentSecondHeightFamily CenteredMomentCommonPuncture CenteredMomentOriginalChildEnergy
open CenteredMomentFirstPhysicalSource (allocatedData allocated_pools allocated_profile
  columns element element_supported column_supported)
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]

open CenteredMomentChildAssembly
open CenteredMomentSecondSectorColumns IdealMobiusDivisorSum
open CenteredMomentFirstPhysicalSource (columns_gauss_polynomial columns_gauss_polynomial_filter)
local instance angularFirstOriginalColumnDecEq : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem first_column_original_data (D:OriginalData ι)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (C:Ideal O)(hC:Supported C)(hseed:D.s∣C)(τ:AngularCharacter)(t T:ℝ)(L:Ideal O)
    (a:columns C C hC.1 D.columns→ℂ)
    (ha:∀I:columns C C hC.1 D.columns,
      a I=(if L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I)(z:O):
    (Real.sqrt T:ℂ)⁻¹*gaussPolynomial Finset.univ (element C C hC.1 D.columns)
      (element_supported C C hC.1 D.columns) a z=
      ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
        gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported (allocatedData D C L B).columns)
          (Amplification.originalCoefficient (allocatedData D C L B) τ fixedBadMask t T) z:=by
  rw [funext ha,columns_gauss_polynomial C hC D.columns
    (fun I=>(if L∣I then D.beta (C*I) else 0)*heightCoeff τ t I) z]
  have he:(fun I:supportedColumns (residualPool C hC.1 D.columns)=>
      if IsCoprime C (I:Ideal O) then
        (if L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I else 0)=
      (fun I:supportedColumns (residualPool C hC.1 D.columns)=>
        (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I):=by
    funext I
    by_cases hc:IsCoprime C (I:Ideal O) <;> by_cases hl:L∣(I:Ideal O) <;> simp [hc,hl]
  rw [he]
  exact normalized_common_gauss_allocation D hS hp C hC hseed τ t T L z

theorem first_column_original_data_filter (D:OriginalData ι)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)(hQC:primeSupport Q=primeSupport C)
    (hseed:D.s∣C)(τ:AngularCharacter)(t T:ℝ)(L:Ideal O)
    (a:columns Q C hC.1 D.columns→ℂ)
    (ha:∀I:columns Q C hC.1 D.columns,
      a I=(if L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I)(z:O):
    (Real.sqrt T:ℂ)⁻¹*gaussPolynomial Finset.univ (element Q C hC.1 D.columns)
      (element_supported Q C hC.1 D.columns) a z=
      ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
        gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported (allocatedData D C L B).columns)
          (Amplification.originalCoefficient (allocatedData D C L B) τ fixedBadMask t T) z:=by
  rw [funext ha,columns_gauss_polynomial_filter Q C hC D.columns
    (fun I=>(if L∣I then D.beta (C*I) else 0)*heightCoeff τ t I) z]
  have he:(fun I:supportedColumns (residualPool C hC.1 D.columns)=>
      if IsCoprime Q (I:Ideal O) then
        (if L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I else 0)=
      (fun I:supportedColumns (residualPool C hC.1 D.columns)=>
        (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I):=by
    funext I
    rw [coprime_of_same_support Q C I hQ hC.1 (Finset.mem_filter.mp I.property).2.1 hQC]
    by_cases hc:IsCoprime C (I:Ideal O) <;> by_cases hl:L∣(I:Ideal O) <;> simp [hc,hl]
  rw [he]
  exact normalized_common_gauss_allocation D hS hp C hC hseed τ t T L z

end OAI.SevenEighths.Angular.PlainRows.FirstPhysical

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.first_column_original_data
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.first_column_original_data

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.first_column_original_data_filter
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.first_column_original_data_filter
