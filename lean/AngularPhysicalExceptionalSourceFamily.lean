import AngularPhysicalSecondEnergySplit
import AngularPhysicalExceptionalRowsPair
import AngularPhysicalUniformExceptionalFamily

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.SecondExceptionalSourceFamily
open PlainRows.SecondSource PhysicalBlock SecondFamily SecondExceptionalKernel ChildRows ExceptionalRows
open CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondHeightFamily (fixedBadMask)
open CenteredMomentHeckeColumnWindow
open CenteredMomentSecondEnergySplit (sourceRows sourceRows_nonzero)
open CenteredMomentSecondLiveBlock (liveRows liveRows_weight)
local notation "O" => ActualEisensteinCubic.O

lemma exceptional_part_nonzero (η:AngularCharacter)(χ₀:RayCharacter)(Q:Ideal O)(m:O)
    (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ)(z:O)
    (hz:z∈partRows true η χ₀ Q m C D U R):z≠0:=
  sourceRows_nonzero C D U R z (Finset.mem_filter.mp hz).1

lemma exceptional_part_inducing (η:AngularCharacter)(χ₀:RayCharacter)(Q:Ideal O)(m:O)
    (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ)(z:O)
    (hz:z∈partRows true η χ₀ Q m C D U R):
    FixedInducingRow (childCharacter η χ₀) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z:=
  (Finset.mem_filter.mp hz).2

lemma actual_family_both_rows (η:AngularCharacter)(χ₀:RayCharacter)(Q:Ideal O)
    (hQ:Q≤Ideal.span {(72:O)})(m:O)(hm:m≠0)
    (hml:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:O)∣m)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (τ:RayCharacter→AngularCharacter)(hf:Family η C D hC hD U τ)(R:ℝ):
    (∀χ:RayCharacter,∀z∈partRows true η χ₀ Q m C D U R,
      FixedInducingRow (τ χ) Q fixedBadMask 1 z) ∧
    (∀χ:RayCharacter,∀z∈partRows true η χ₀ Q m C D U R,
      FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)):=by
  have hz0:=exceptional_part_nonzero η χ₀ Q m C D U R
  have hex:=exceptional_part_inducing η χ₀ Q m C D U R
  constructor
  · intro χ z hz
    have hh:=(exceptional_rows_pair η χ₀ χ χ Q hQ m _ hml hm2 _ hex).1 z hz
    exact (hf.inducing_iff χ Q m z hm (hz0 z hz) hml hm2).mp hh
  · intro χ z hz
    have hh:=(exceptional_rows_pair η χ₀ χ (χ⁻¹) Q hQ m _ hml hm2 _ hex).2 z hz
    simp only [inv_inv] at hh
    exact (hf.inducing_iff χ Q m (-z) hm (neg_ne_zero.mpr (hz0 z hz)) hml hm2).mp hh

lemma exceptional_part_live (η:AngularCharacter)(χ₀:RayCharacter)(Q:Ideal O)(m:O)
    (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ):
    liveRows C D U R (partRows true η χ₀ Q m C D U R)=
      partRows true η χ₀ Q m C D U R:=by
  apply Finset.filter_eq_self.mpr
  intro z hz
  exact liveRows_weight C D U R _ z (Finset.mem_filter.mp hz).1

end OAI.SevenEighths.Angular.SecondExceptionalSourceFamily

#print axioms OAI.SevenEighths.Angular.SecondExceptionalSourceFamily.exceptional_part_nonzero
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondExceptionalSourceFamily.exceptional_part_nonzero

#print axioms OAI.SevenEighths.Angular.SecondExceptionalSourceFamily.exceptional_part_inducing
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondExceptionalSourceFamily.exceptional_part_inducing

#print axioms OAI.SevenEighths.Angular.SecondExceptionalSourceFamily.actual_family_both_rows
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondExceptionalSourceFamily.actual_family_both_rows

#print axioms OAI.SevenEighths.Angular.SecondExceptionalSourceFamily.exceptional_part_live
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondExceptionalSourceFamily.exceptional_part_live
