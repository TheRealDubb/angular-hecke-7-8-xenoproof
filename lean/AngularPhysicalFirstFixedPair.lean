import AngularPhysicalFirstMaskedFamily
import AngularPhysicalFirstPresentation
import AngularPhysicalRelativeFiniteProduct

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.PlainRows.FirstPhysical
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentSecondHeightFamily CenteredMomentCanonicalFirst CenteredMomentFirstColumns
open CenteredMomentFirstCanonicalFamily CenteredMomentCommonSupport CenteredMomentPrimitive
open CenteredMomentFirstPhysicalSource (fixedPresentationCost)
open RayFourExpansion CompletedGauss
local notation "O" => ActualEisensteinCubic.O

structure FixedPair (η:AngularCharacter)(C D:Ideal O)(hC:Supported C)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayCharacter) where
  left : AngularCharacter
  right : AngularCharacter
  left_type : left.k=η.k
  right_type : right.k=η.k
  left_modulus : left.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
    Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}
  right_modulus : right.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
    Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}
  left_height : ∀I:Ideal O,Supported I→∀t:ℝ,
    heightCoeff left t I=rowWeight η fixedBadMask 1 1 t I*
      (leftCoefficient (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
        (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
          (activeExponent C D)) (primaryGenerator I)*rayCharacter ξ₁ (primaryGenerator I))
  right_height : ∀I:Ideal O,Supported I→∀t:ℝ,
    heightCoeff right t I=rowWeight η fixedBadMask 1 1 t I*
      (rightCoefficient (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
        (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
          (activeExponent C D)) (primaryGenerator I)*rayCharacter ξ₂ (primaryGenerator I))

def fixedPair (η:AngularCharacter)(C D:Ideal O)(hC:Supported C)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayCharacter):FixedPair η C D hC E ξ₁ ξ₂:=
  Classical.choice (by
    obtain ⟨τ₁,τ₂,hk₁,hk₂,hM₁,hM₂,h₁,h₂,_,_⟩:=exists_canonical_masked_pair η C D hC E ξ₁ ξ₂
    exact ⟨⟨τ₁,τ₂,hk₁,hk₂,hM₁,hM₂,h₁,h₂⟩⟩)

theorem FixedPair.conductor_caps {η:AngularCharacter}{C D:Ideal O}{hC:Supported C}
    {E:Finset (CommonIndex C D)}{ξ₁ ξ₂:RayCharacter}(F:FixedPair η C D hC E ξ₁ ξ₂):
    (F.left.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2 ∧
    (F.right.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2:=
  fixed_pair_presentation_caps η F.left F.right C D E F.left_modulus F.right_modulus


/-- Both constructed first children cancel the same fixed inverse-anchor slot.
This keeps the signed type, rather than just the absolute angular order. -/
theorem FixedPair.relative_slots_cancel {η:AngularCharacter} {C D:Ideal O} {hC:Supported C}
    {E:Finset (CommonIndex C D)} {ξ₁ ξ₂:RayCharacter} (F:FixedPair η C D hC E ξ₁ ξ₂)
    (Ω:AngularCharacter) (hη:η.k=Ω.k) (θ:HeckeFamily.Character) :
    F.left.k+(RelativePrime.relativeCharacter Ω θ).k=0 ∧
      F.right.k+(RelativePrime.relativeCharacter Ω θ).k=0 :=
  ⟨RelativePrime.inverse_anchor_cancels_type Ω F.left (F.left_type.trans hη) θ,
   RelativePrime.inverse_anchor_cancels_type Ω F.right (F.right_type.trans hη) θ⟩

end OAI.SevenEighths.Angular.PlainRows.FirstPhysical

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.FixedPair.conductor_caps
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.FixedPair.conductor_caps

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.FixedPair.relative_slots_cancel
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.FixedPair.relative_slots_cancel
