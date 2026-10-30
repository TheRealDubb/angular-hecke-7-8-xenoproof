import AngularPhysicalExceptionalFamilyGates

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
def expandedConductor (τ:AngularCharacter)(R C:Ideal O)(z:O):ℕ :=
  τ.modulus.absNorm*(Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
    (R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm

def expandedFactor (η:AngularCharacter):ℕ :=
  1296*η.modulus.absNorm*fixedFactor*(Ideal.span {fixedBadMask}).absNorm*
    (Ideal.span {(72:O)}).absNorm

theorem expanded_conductor_bounds {η:AngularCharacter}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→AngularCharacter}
    (h:Family η C D hC hD U τ)(hCD:primeSupport C=primeSupport D)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
    (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U radius rows W K n≠0)
    (χ ξ:RayCharacter)(R:Ideal O)(z:O) :
    expandedConductor (τ χ) R C z≤
      expandedFactor η*R.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm ∧
    expandedConductor (reflected (τ ξ)) R D z≤
      expandedFactor η*R.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm := by
  have hl := (h.physical_conductor_bounds hCD t S β radius rows W K hK n hne χ).2
  have hr := (h.physical_conductor_bounds hCD t S β radius rows W K hK n hne ξ).1
  have hl' : (τ χ).modulus.absNorm≤1296*(η.modulus.absNorm*fixedFactor*D.absNorm) := by
    exact hl.trans (Nat.le_mul_of_pos_left _ (by norm_num))
  have hr' := (reflected_modulus_bound (τ ξ)).trans (Nat.mul_le_mul_left 1296 hr)
  constructor
  · calc
      expandedConductor (τ χ) R C z≤
        (1296*(η.modulus.absNorm*fixedFactor*D.absNorm))*
          (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          (R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm := by
            unfold expandedConductor
            gcongr
      _=_ := by unfold expandedFactor;ring
  · calc
      expandedConductor (reflected (τ ξ)) R D z≤
        (1296*(η.modulus.absNorm*fixedFactor*C.absNorm))*
          (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          (R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm := by
            unfold expandedConductor
            gcongr
      _=_ := by unfold expandedFactor;ring

end OAI.SevenEighths.Angular.SecondFamily

#print axioms OAI.SevenEighths.Angular.SecondFamily.expanded_conductor_bounds
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondFamily.expanded_conductor_bounds
