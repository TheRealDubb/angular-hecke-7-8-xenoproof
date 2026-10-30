import AngularPhysicalExceptionalReflectedConductor

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
namespace Family
variable {η:AngularCharacter} {C D:Ideal O} {hC:Supported C} {hD:Supported D}
  {U:Finset (CommonIndex C D)} {τ:RayCharacter→AngularCharacter}
theorem paired_inducing_iff (h:Family η C D hC hD U τ) (χ ξ:RayCharacter)
    (Q:Ideal O) (hQ:Q≤Ideal.span {(72:O)}) (m z:O) (hm:m≠0) (hz:z≠0)
    (hml:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m) :
    FixedInducingRow (τ χ) Q fixedBadMask 1 z ↔
      FixedInducingRow (τ ξ) Q fixedBadMask 1 (-z) :=
  (h.inducing_iff χ Q m z hm hz hml hm2).symm.trans
    ((ExceptionalRows.fixedInducingRow_reflection_iff η χ ξ Q hQ m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z hml hm2).trans
      (h.inducing_iff ξ Q m (-z) hm (neg_ne_zero.mpr hz) hml hm2))

theorem both_inducing (h:Family η C D hC hD U τ) (χ ξ:RayCharacter)
    (Q:Ideal O) (hQ:Q≤Ideal.span {(72:O)}) (m z:O) (hm:m≠0) (hz:z≠0)
    (hml:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m)
    (hex:FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) :
    FixedInducingRow (τ χ) Q fixedBadMask 1 z ∧
      FixedInducingRow (reflected (τ ξ)) Q fixedBadMask 1 z := by
  have hleft := (h.inducing_iff χ Q m z hm hz hml hm2).mp hex
  refine ⟨hleft,?_⟩
  exact (reflected_inducing (τ ξ) Q fixedBadMask 1 z (dvd_mul_right _ _) (dvd_mul_left _ _)).mp
    ((h.paired_inducing_iff χ ξ Q hQ m z hm hz hml hm2).mp hleft)

theorem reflected_height_eq (h:Family η C D hC hD U τ) (ξ:RayCharacter)
    (I:Ideal O)(hI:Supported I)(hi:IsCoprime C I ∨ IsCoprime D I)(t:ℝ) :
    heightCoeff (reflected (τ ξ)) t I=heightCoeff η t I*
      idealRowHom (-(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)) I*
      rayCharacter ξ (primaryGenerator I) := by
  have hneg : idealRowHom (-(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)) I=
      idealRowHom (-1) I*idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I := by
    rw [show -(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)=
      (-1)*(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) by ring]
    exact idealRowHom_argument_mul _ _ _
  rw [reflected_height _ _ _ hI,h.height_eq ξ I hI hi t,hneg]
  ring

theorem live_both_inducing (h:Family η C D hC hD U τ) (χ ξ:RayCharacter)
    (Q:Ideal O)(hQ:Q≤Ideal.span {(72:O)})(m z:O)(hm:m≠0)
    (hml:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:O)∣m)
    (radius:ℝ)(rows:Finset O)(hz:z∈liveRows C D U radius rows)
    (hex:FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) :
    z≠0 ∧ FixedInducingRow (τ χ) Q fixedBadMask 1 z ∧
      FixedInducingRow (reflected (τ ξ)) Q fixedBadMask 1 z := by
  have hz0 := (liveRows_geometry C D U radius rows z hz).2.1
  exact ⟨hz0,h.both_inducing χ ξ Q hQ m z hm hz0 hml hm2 hex⟩

theorem physical_conductor_bounds (h:Family η C D hC hD U τ)
    (hCD:primeSupport C=primeSupport D)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
    (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)(χ:RayCharacter) :
    (τ χ).modulus.absNorm≤η.modulus.absNorm*fixedFactor*C.absNorm ∧
    (τ χ).modulus.absNorm≤η.modulus.absNorm*fixedFactor*D.absNorm := by
  have hN := (h.physical_budget t S β R rows W K hK n hne χ).1
  obtain ⟨h₁,h₂⟩ := selected_nonunit_norm C D hC hD hCD U
  constructor
  · exact hN.trans <| by
      simpa only [mul_assoc] using (Nat.mul_le_mul_left (η.modulus.absNorm*fixedFactor) h₁)
  · exact hN.trans <| by
      simpa only [mul_assoc] using (Nat.mul_le_mul_left (η.modulus.absNorm*fixedFactor) h₂)

end Family
end OAI.SevenEighths.Angular.SecondFamily

#print axioms OAI.SevenEighths.Angular.SecondFamily.Family.paired_inducing_iff
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondFamily.Family.paired_inducing_iff

#print axioms OAI.SevenEighths.Angular.SecondFamily.Family.both_inducing
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondFamily.Family.both_inducing

#print axioms OAI.SevenEighths.Angular.SecondFamily.Family.reflected_height_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondFamily.Family.reflected_height_eq

#print axioms OAI.SevenEighths.Angular.SecondFamily.Family.live_both_inducing
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondFamily.Family.live_both_inducing

#print axioms OAI.SevenEighths.Angular.SecondFamily.Family.physical_conductor_bounds
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondFamily.Family.physical_conductor_bounds
