import AngularPhysicalSecondChildFamily
import AngularPhysicalPlainReflected
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology
namespace OAI.SevenEighths.Angular.SecondFamily
open PlainRows ChildRows ExceptionalRows PhysicalBlock
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalLedger CenteredMomentPartitionNorm
open CenteredMomentSecondHeightFamily (fixedBadMask fixedBadMask_ne_zero)
open CenteredMomentSecondRadicalBudget (fixedFactor fixedFactor_pos)
open CenteredMomentSecondLiveBlock (liveRows liveRows_geometry liveRows_weight)
open CenteredMomentSectorLocalization
open CenteredMomentSecondExceptionalFamily (span_thirty_six_norm selected_nonunit_norm live_norm_le_four_radius)
local notation "O" => ActualEisensteinCubic.O
theorem reflected_modulus_bound (τ:AngularCharacter) :
    (reflected τ).modulus.absNorm≤1296*τ.modulus.absNorm := by
  have h := AngularRowClosure.finiteTwist_conductor_bound τ (HeckeUnitRows.character (-1:Oˣ))
  change (reflected τ).modulus.absNorm≤τ.modulus.absNorm*(Ideal.span {(36:O)}).absNorm at h
  simpa only [span_thirty_six_norm,mul_comm] using h

end OAI.SevenEighths.Angular.SecondFamily

#print axioms OAI.SevenEighths.Angular.SecondFamily.reflected_modulus_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondFamily.reflected_modulus_bound
