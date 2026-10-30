import AngularPhysicalFirstFixedPair
import AngularPhysicalFirstAllocation
import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedFamily

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

open CenteredMomentFirstPhysicalSource (beta_coprime extracted_mask_redundant)
open CenteredMomentFirstColumns RayFourExpansion CompletedGauss
open CenteredMomentChildAssembly
local instance angularFirstFixedDivisorDecEq : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem fixed_divisor_column (s:OriginalData ι)(η τ:AngularCharacter)(C:Ideal O)
    (F:O→ℂ)(ξ:RayCharacter)
    (hτ:∀I:Ideal O,Supported I→∀t:ℝ,heightCoeff τ t I=
      rowWeight η fixedBadMask 1 1 t I*(F (primaryGenerator I)*rayCharacter ξ (primaryGenerator I)))
    (L I:Ideal O)(hI:Supported I)(t:ℝ):
    divisorCoefficient L (fun J:Ideal O=>primaryGenerator J)
      (fun J=>s.beta (C*J)*rowWeight η (fixedBadMask*idealGenerator s.R) 1 1 t J*
        F (primaryGenerator J)) ξ I=
      (if L∣I then s.beta (C*I) else 0)*heightCoeff τ t I:=by
  have hh:=divisor_column_masked η τ F ξ hτ (idealGenerator s.R) L I hI (fun J=>s.beta (C*J)) t
  rw [extracted_mask_redundant] at hh
  exact hh

end OAI.SevenEighths.Angular.PlainRows.FirstPhysical

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.fixed_divisor_column
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.fixed_divisor_column
