import AngularPhysicalCommonLinearColumns

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
theorem live_column_rectangle (s:Input ι)(C R L:Ideal O)(B:actualAllocations s.pools C)(z:O):
    liveColumn s C R L B z=
      PlainRows.maskedRectangle
        (commonData s C R B).η (commonData s C R B).m (commonData s C R B).A z
        (commonData s C R B).t (commonData s C R B).slots (commonData s C R B).coefficient L
        (commonData s C R B).W₁ (commonData s C R B).W₂
        (commonData s C R B).X₁ (commonData s C R B).X₂
        (commonData s C R B).Y₁ (commonData s C R B).Y₂:=by
  unfold liveColumn
  rw [CenteredMomentCanonicalRetainedSource.liveBox_original_pools]
  have hc₁:=plainCoverage_residualPool (s.pools (Sum.inr 0)) s.W₁ 1 _
    (alloc_ne s C B (Sum.inr 0)) s.X₁ s.Y₁ s.coverage₁
  have hc₂:=plainCoverage_residualPool (s.pools (Sum.inr 1)) s.W₂ 1 _
    (alloc_ne s C B (Sum.inr 1)) s.X₂ s.Y₂ s.coverage₂
  simp only [one_mul] at hc₁ hc₂
  have he:=PlainRows.source_polynomial_eq_maskedRectangle
    s.η fixedBadMask 1 z s.t (dvd_mul_right _ _) (dvd_mul_left _ _)
    (commonData s C R B).slots
    (residualPool (B.val (Sum.inr 0)) (alloc_ne s C B _) (s.pools (Sum.inr 0)))
    (residualPool (B.val (Sum.inr 1)) (alloc_ne s C B _) (s.pools (Sum.inr 1)))
    (R*C) L (commonData s C R B).ν (commonData s C R B).W (commonData s C R B).P
    s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (B.val (Sum.inr 0)) (B.val (Sum.inr 1)) hc₁ hc₂
  rw [height_source_row]
  convert he using 1 <;> simp only [maskedLiveProfile,commonData,one_mul,Input.pools,Sum.elim_inl]
  all_goals rfl

end OAI.SevenEighths.Angular.CommonExceptionalSource

#print axioms OAI.SevenEighths.Angular.CommonExceptionalSource.live_column_rectangle
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CommonExceptionalSource.live_column_rectangle
