import AngularPhysicalCommonExceptionalCoordinates
import AngularPhysicalFixedRowMask

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.CommonExceptionalSource
open PlainRows ExceptionalMaskedSource ExceptionalAmplitudePair DetectorAmplitude ExceptionalSourceShell
open PlainRows.CommonRows (Input alloc_ne alloc_norm_pos commonData)
open ExceptionalRows CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentCommonRawScale CenteredMomentCommonRawCost CenteredMomentAllocationCost
open CenteredMomentCommonProfile CenteredMomentSourceMass CenteredMomentAddedZeroUniform
open CenteredMomentExceptionalAmplitudePair (Tests)
open CenteredMomentSecondHeightFamily (fixedBadMask fixedBadMask_ne_zero)
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
theorem common_mask_inducing (s:Input ι)(C R Q:Ideal O)(hC:C≠0)(hR:R≠0)
    (B:actualAllocations s.pools C)(z:O)(hz:z≠0):
    FixedInducingRow (commonData s C R B).η Q (commonData s C R B).m
      (commonData s C R B).A z ↔ FixedInducingRow s.η Q fixedBadMask 1 z:=by
  exact fixedInducingRow_mul_mask_iff s.η Q fixedBadMask (idealGenerator (R*C)) 1 z
    fixedBadMask_ne_zero (idealGenerator_ne_zero _ (mul_ne_zero hR hC)) one_ne_zero hz
    (dvd_mul_right _ _) (dvd_mul_left _ _)

theorem common_conductor (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C)(z:O):
    AngularRowClosure.rowConductorBound (commonData s C R B).η (commonData s C R B).m 1
      ((commonData s C R B).A*z)=
      s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:=by
  simp only [commonData,AngularRowClosure.rowConductorBound,one_mul,
    ←Ideal.span_singleton_mul_span_singleton,span_idealGenerator,map_mul,Ideal.span_singleton_one,Ideal.absNorm_top,one_pow]
  ring

theorem common_admissible (s:Input ι)(p:Tests)(C R Q:Ideal O)(hC:C≠0)(hR:R≠0)
    (B:actualAllocations s.pools C)(Z width r:ℝ)(hZ:1<Z)(z:O)(hz:z≠0)
    (hP:∀i,1≤s.P i)(hex:FixedInducingRow s.η Q fixedBadMask 1 z)
    (hcond:(s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
      (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^width)
    (hW₁:s.W₁=p.profile 0)(hW₂:s.W₂=p.profile 1)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    Admissible (commonData s C R B) p Q Z width
      (r-Real.logb Z (Ideal.absNorm C:ℝ)) z:=by
  refine ⟨fun i=>hP i.val,?_,one_ne_zero,hz,?_,?_,?_,?_,hW₁,hW₂,?_,?_,?_,?_⟩
  · exact mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero _ (mul_ne_zero hR hC))
  · exact (dvd_mul_right _ _).trans (dvd_mul_right _ _)
  · exact (dvd_mul_left _ _).trans (dvd_mul_right _ _)
  · rw [common_conductor]
    simpa only [Nat.cast_mul] using hcond
  · exact (common_mask_inducing s C R Q hC hR B z hz).mpr hex
  · exact extracted_lower s C hC B (Sum.inr 0) Z r s.X₁ hZ hX₁
  · exact extracted_lower s C hC B (Sum.inr 1) Z r s.X₂ hZ hX₂
  · exact extracted_lower s C hC B (Sum.inr 0) Z r s.Y₁ hZ hY₁
  · exact extracted_lower s C hC B (Sum.inr 1) Z r s.Y₂ hZ hY₂

end OAI.SevenEighths.Angular.CommonExceptionalSource

#print axioms OAI.SevenEighths.Angular.CommonExceptionalSource.common_mask_inducing
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CommonExceptionalSource.common_mask_inducing

#print axioms OAI.SevenEighths.Angular.CommonExceptionalSource.common_conductor
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CommonExceptionalSource.common_conductor

#print axioms OAI.SevenEighths.Angular.CommonExceptionalSource.common_admissible
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CommonExceptionalSource.common_admissible
