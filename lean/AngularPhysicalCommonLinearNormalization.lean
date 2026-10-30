import AngularPhysicalCommonLiveRectangle
import OAI.NumberTheory.DirichletL.Moments.CommonRawCost

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.CommonExceptionalSource
open PlainRows ExceptionalMaskedSource ExceptionalAmplitudePair
open PlainRows.CommonRows (Input alloc_ne commonData)
open CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAddedZeroUniform CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentRowNorm
open CenteredMomentRestrictedSource CenteredMomentRestrictedDomain CenteredMomentAmplificationLiveMask
open CenteredMomentCommonRawScale CenteredMomentCommonRawCost
open CenteredMomentSecondHeightFamily (fixedBadMask)
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
def commonScalar (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):ℂ:=
  (Real.sqrt (rawReduction B.val s.P):ℂ)⁻¹*frozenCoefficient B.val C R s.ν s.W s.P

theorem common_volume (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):
    volume (commonData s C R B)=remainingRaw B.val (s.X₁*s.X₂) s.P:=by
  dsimp only [volume,commonData,remainingRaw,plainNorm]
  ring

theorem source_normalized (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (hseed:seed∣C)(z:O):
    (Real.sqrt (volume s.toData):ℂ)⁻¹*sourceColumn s C hC R seed L z=
      ∑B:actualAllocations s.pools C,commonScalar s C R B*maskedAmplitude (commonData s C R B) L z:=by
  rw [source_column_allocation s C hC R seed L hseed z,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  rw [live_column_rectangle]
  have hv:=volume_pos (commonData s C R B)
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have he:volume (commonData s C R B)*rawReduction B.val s.P=volume s.toData:=by
    rw [common_volume]
    exact raw_scale_identity B.val (alloc_ne s C B) (s.X₁*s.X₂) s.P
  have hs:Real.sqrt (volume s.toData)=Real.sqrt (volume (commonData s C R B))*
      Real.sqrt (rawReduction B.val s.P):=by rw [←he,Real.sqrt_mul hv.le]
  unfold commonScalar maskedAmplitude
  change (Real.sqrt (volume s.toData):ℂ)⁻¹*(_*_) =
    ((Real.sqrt (rawReduction B.val s.P):ℂ)⁻¹*_)*
      ((Real.sqrt (volume (commonData s C R B)):ℂ)⁻¹*_)
  rw [hs,Complex.ofReal_mul,mul_inv_rev]
  ring

theorem commonScalar_sq (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):
    ‖commonScalar s C R B‖^2=
      ‖frozenCoefficient B.val C R s.ν s.W s.P‖^2/rawReduction B.val s.P:=
  CenteredMomentDivisorRawEnergy.normalized_norm_sq _
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) _

theorem commonScalar_sq_bound (s:Input ι)(C R:Ideal O)(hC:C≠0)(B:actualAllocations s.pools C):
    ‖commonScalar s C R B‖^2≤
      ((∏i,s.M i)^2*(max 1 s.upper)^Fintype.card ι)/(Ideal.absNorm C:ℝ):=by
  rw [commonScalar_sq]
  exact frozen_normalized_cost B.val (alloc_ne s C B) C R hC
    (Finset.mem_filter.mp B.property).2 s.ν s.W s.P s.M s.P_pos s.ν_bound s.W_bound
    s.M_ge_one s.lower s.upper s.lower_pos s.slot_support

end OAI.SevenEighths.Angular.CommonExceptionalSource

#print axioms OAI.SevenEighths.Angular.CommonExceptionalSource.common_volume
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CommonExceptionalSource.common_volume

#print axioms OAI.SevenEighths.Angular.CommonExceptionalSource.source_normalized
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CommonExceptionalSource.source_normalized

#print axioms OAI.SevenEighths.Angular.CommonExceptionalSource.commonScalar_sq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CommonExceptionalSource.commonScalar_sq

#print axioms OAI.SevenEighths.Angular.CommonExceptionalSource.commonScalar_sq_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CommonExceptionalSource.commonScalar_sq_bound
