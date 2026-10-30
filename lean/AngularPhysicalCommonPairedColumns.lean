import AngularPhysicalCommonLinearNormalization

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
variable {κ:Type*} [Fintype κ] [DecidableEq κ]
def normalizedColumn (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(z:O):ℂ:=
  (Real.sqrt (volume s.toData):ℂ)⁻¹*sourceColumn s C hC R seed L z

theorem norm_column (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (hseed:seed∣C)(z:O):
    ‖normalizedColumn s C hC R seed L z‖≤
      ∑B:actualAllocations s.pools C,‖commonScalar s C R B‖*
        ‖maskedAmplitude (commonData s C R B) L z‖:=by
  unfold normalizedColumn
  rw [source_normalized s C hC R seed L hseed]
  simpa only [norm_mul] using norm_sum_le
    (Finset.univ:Finset (actualAllocations s.pools C))
    (fun B=>commonScalar s C R B*maskedAmplitude (commonData s C R B) L z)

theorem paired_columns (s:Input ι)(v:Input κ)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (R seed L:Ideal O)(hsC:seed∣C)(hsD:seed∣D)(rows:Finset O):
    (∑z∈rows,‖normalizedColumn s C hC R seed L z‖*‖normalizedColumn v D hD R seed L z‖)≤
      ∑B:actualAllocations s.pools C,∑E:actualAllocations v.pools D,
        (‖commonScalar s C R B‖*‖commonScalar v D R E‖)*
          ∑z∈rows,‖maskedAmplitude (commonData s C R B) L z‖*
            ‖maskedAmplitude (commonData v D R E) L z‖:=by
  calc
    _≤∑z∈rows,(∑B:actualAllocations s.pools C,‖commonScalar s C R B‖*
        ‖maskedAmplitude (commonData s C R B) L z‖)*
      (∑E:actualAllocations v.pools D,‖commonScalar v D R E‖*
        ‖maskedAmplitude (commonData v D R E) L z‖):=by
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul (norm_column s C hC R seed L hsC z)
        (norm_column v D hD R seed L hsD z) (norm_nonneg _)
        (Finset.sum_nonneg (fun B _=>mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _=_:=by
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_comm (s:=rows) (t:=Finset.univ)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro B hB
      apply Finset.sum_congr rfl
      intro E hE
      apply Finset.sum_congr rfl
      intro z hz
      ring

end OAI.SevenEighths.Angular.CommonExceptionalSource

#print axioms OAI.SevenEighths.Angular.CommonExceptionalSource.norm_column
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CommonExceptionalSource.norm_column

#print axioms OAI.SevenEighths.Angular.CommonExceptionalSource.paired_columns
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CommonExceptionalSource.paired_columns
