import AngularPhysicalCommonPairedColumns

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
theorem whole_paired_columns (s:Input ι)(v:Input κ)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (R seed:Ideal O)(hsC:seed∣C)(hsD:seed∣D)(Ds:Finset (Ideal O))(rows:Finset O):
    (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
      ‖normalizedColumn s C hC R seed L z‖*‖normalizedColumn v D hD R seed L z‖)≤
      ∑B:actualAllocations s.pools C,∑E:actualAllocations v.pools D,
        (‖commonScalar s C R B‖*‖commonScalar v D R E‖)*
          ∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
            ‖maskedAmplitude (commonData s C R B) L z‖*
              ‖maskedAmplitude (commonData v D R E) L z‖:=by
  calc
    _≤∑L∈Ds,‖(moebius L:ℂ)‖*
      ∑B:actualAllocations s.pools C,∑E:actualAllocations v.pools D,
        (‖commonScalar s C R B‖*‖commonScalar v D R E‖)*
          ∑z∈rows,‖maskedAmplitude (commonData s C R B) L z‖*
            ‖maskedAmplitude (commonData v D R E) L z‖:=
      Finset.sum_le_sum (fun L hL=>mul_le_mul_of_nonneg_left
        (paired_columns s v C D hC hD R seed L hsC hsD rows) (norm_nonneg _))
    _=_:=by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro B hB
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro E hE
      apply Finset.sum_congr rfl
      intro L hL
      apply Finset.sum_congr rfl
      intro z hz
      ring

end OAI.SevenEighths.Angular.CommonExceptionalSource

#print axioms OAI.SevenEighths.Angular.CommonExceptionalSource.whole_paired_columns
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CommonExceptionalSource.whole_paired_columns
