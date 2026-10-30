import AngularPhysicalRetainedNormalized

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.AllocatedNatural
open PlainRows NaturalRows Dyadic CommonMask
open CenteredMomentRetainedProfile CenteredMomentLattice
open CenteredMomentDivisorAllocation
open CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle CenteredMomentDivisorRaw
open CenteredMomentCommonMaskEnergy (heightCoefficient heightCoefficient_norm)
open CenteredMomentAllocatedNaturalSource (Plain rawScale rawScale_pos raw_same_product)
local notation "O" => ActualEisensteinCubic.O
lemma polynomial_zero (χ : AngularCharacter) (X : ℝ) :
    Dyadic.polynomial χ false (0 : 𝓢(ℝ,ℂ)) X 0 0=0 := by
  simp [Dyadic.polynomial,Dyadic.summand]

theorem retained_normalized (η : AngularCharacter) (z : O) (hz : z≠0) (R : Ideal O) (hR : R≠0)
    {α : Type*} [Fintype α] [DecidableEq α] (V₁ V₂ : Plain)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (t U₁ U₂ : ℝ) (hU₁ : 0<U₁) (hU₂ : 0<U₂) :
    retainedPositiveRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z V₁.W V₂.W pool β P t U₁ U₂=
      (((clippedScale U₁):ℂ)^(Complex.I*t)*((clippedScale U₂):ℂ)^(Complex.I*t))*
        (Dyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₁.profile U₁ hU₁ t) (clippedScale U₁) 0 0 *
         Dyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₂.profile U₂ hU₂ t) (clippedScale U₂) 0 0 *
         ∏i,naturalSlot (excluded (naturalRow η z hz).character R) (pool i) (heightCoefficient (β i) t) (P i)) := by
  by_cases h₁ : 1≤U₁*V₁.b
  · by_cases h₂ : 1≤U₂*V₂.b
    · rw [V₁.profile_retained U₁ hU₁ t h₁,V₂.profile_retained U₂ hU₂ t h₂]
      exact original_retained_normalized (naturalRow η z hz) R hR _ _ _ _ _ _ V₁.a_pos V₂.a_pos
        V₁.support V₂.support V₁.smooth V₂.smooth pool β P hP t U₁ U₂ hU₁ hU₂ h₁ h₂
    · rw [original_retained_zero η _ 1 z V₁.W V₂.W V₁.b V₂.b
        (fun _ h=>(V₁.support h).2) (fun _ h=>(V₂.support h).2) pool β P t U₁ U₂ hU₁ hU₂
        (Or.inr (lt_of_not_ge h₂)),V₂.profile_zero U₂ hU₂ t (lt_of_not_ge h₂),polynomial_zero]
      simp
  · rw [original_retained_zero η _ 1 z V₁.W V₂.W V₁.b V₂.b
      (fun _ h=>(V₁.support h).2) (fun _ h=>(V₂.support h).2) pool β P t U₁ U₂ hU₁ hU₂
      (Or.inl (lt_of_not_ge h₁)),V₁.profile_zero U₁ hU₁ t (lt_of_not_ge h₁),polynomial_zero]
    simp

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem allocated_normalized (η : AngularCharacter) (z : O) (hz : z≠0) (R : Ideal O) (hR : R≠0)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    allocatedPositiveRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z t pool β P D a V₁.W V₂.W X₁ X₂=
      (((clippedScale (rawScale D a X₁ 0)):ℂ)^(Complex.I*t)*
       ((clippedScale (rawScale D a X₂ 1)):ℂ)^(Complex.I*t))*
        (Dyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t) (clippedScale (rawScale D a X₁ 0)) 0 0 *
         Dyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t) (clippedScale (rawScale D a X₂ 1)) 0 0 *
         ∏i∈liveIndices D a,naturalSlot (excluded (naturalRow η z hz).character R)
           (pool i) (heightCoefficient (β i) t) (P i)) := by
  have h:=retained_normalized η z hz R hR V₁ V₂
    (fun i : liveIndices D a=>pool i) (fun i : liveIndices D a=>β i) (fun i : liveIndices D a=>P i)
    (fun i=>hP i) t _ _ (rawScale_pos D a X₁ hX₁ 0) (rawScale_pos D a X₂ hX₂ 1)
  have hp': (∏i : liveIndices D a,naturalSlot (excluded (naturalRow η z hz).character R)
      (pool i) (heightCoefficient (β i) t) (P i))=
      ∏i∈liveIndices D a,naturalSlot (excluded (naturalRow η z hz).character R)
      (pool i) (heightCoefficient (β i) t) (P i) := Finset.prod_coe_sort (liveIndices D a) (fun i : α=>naturalSlot (excluded (naturalRow η z hz).character R) (pool i) (heightCoefficient (β i) t) (P i))
  rw [hp'] at h
  exact h

def child (χ : AngularCharacter) (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (D₁ D₂ : Finset (Ideal O)) (J : Finset α) : ℂ :=
  Dyadic.polynomial χ false (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t)
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
  Dyadic.polynomial χ false (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t)
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
  ∏i∈liveIndices D a\J,naturalSlot χ (pool i) (heightCoefficient (β i) t) (P i)


theorem child_character_order (η:AngularCharacter)(z:O)(hz:z≠0) :
    (naturalRow η z hz).character.k.natAbs=η.k.natAbs :=
  congrArg Int.natAbs (naturalRow η z hz).angular_type

end OAI.SevenEighths.Angular.AllocatedNatural

#print axioms OAI.SevenEighths.Angular.AllocatedNatural.allocated_normalized
#print axioms OAI.SevenEighths.Angular.AllocatedNatural.child_character_order
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AllocatedNatural.child_character_order
