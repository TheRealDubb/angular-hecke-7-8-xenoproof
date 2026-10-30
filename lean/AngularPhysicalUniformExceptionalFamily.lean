import AngularPhysicalExceptionalUniformConductor

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
open CenteredMomentSecondExceptionalFamilyUniform (fixedExpandedCost fixedExpandedCost_pos)
theorem exists_uniform_exceptional_family (ε:ℝ)(hε:0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀(η:AngularCharacter)(C D:Ideal O)(hC:Supported C)(hD:Supported D),
    primeSupport C=primeSupport D→∀U:Finset (CommonIndex C D),
    ∃τ:RayCharacter→AngularCharacter,Family η C D hC hD U τ ∧
    ∀Z:ℝ,Z₀≤Z→∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U radius rows W K n≠0→
    ∀(χ ξ:RayCharacter)(R:Ideal O)(c d r m q:ℝ),
    (η.modulus.absNorm:ℝ)≤Z^q→(C.absNorm:ℝ)≤Z^c→(D.absNorm:ℝ)≤Z^d→
    (R.absNorm:ℝ)≤Z^r→ radius≤Z^m→∀z∈liveRows C D U radius rows,
    0<radius ∧ z≠0 ∧ 1≤normValue z ∧
    (expandedConductor (τ χ) R C z:ℝ)≤Z^(c+d+r+m+q+ε) ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤Z^(c+d+r+m+q+ε) := by
  obtain ⟨Z₀,hZ₀,hcaps⟩ := eventually_uniform_live_caps ε hε
  refine ⟨Z₀,hZ₀,?_⟩
  intro η C D hC hD hCD U
  obtain ⟨τ,hτ⟩ := exists_exceptional_family η C D hC hD hCD U
  refine ⟨τ,hτ,?_⟩
  intro Z hZ
  exact hcaps Z hZ η C D hC hD hCD U τ hτ

end OAI.SevenEighths.Angular.SecondFamily

#print axioms OAI.SevenEighths.Angular.SecondFamily.exists_uniform_exceptional_family
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondFamily.exists_uniform_exceptional_family
