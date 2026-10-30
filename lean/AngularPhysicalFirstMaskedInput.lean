import AngularPhysicalFirstMaskedFamily
import AngularPhysicalPlainChildSource
import OAI.NumberTheory.DirichletL.Moments.FirstMaskedInput

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows.FirstPhysical.MaskedInput
open CanonicalQuadraticSieve ConcretePrimeRowBridge CommonRows ChildInputs
open CenteredMomentSourceProfileMass CenteredMomentSourceMass CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationLiveMask CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceRow
open CenteredMomentRemainingBox CenteredMomentSourceLiveColumn CenteredMomentSecondHeightFamily
open CenteredMomentOriginalChildEnergy
open CenteredMomentFirstMaskedFamily (maskedSource)
open CenteredMomentFirstMaskedInput (column_combined_mask)
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]
local instance angularFirstMaskedInputDecEq {κ:Type*} : DecidableEq κ := Classical.decEq _
local instance angularFirstMaskedInputSumDecEq : DecidableEq (ι⊕Fin 2) := Classical.decEq _

lemma input_combined_mask (s : Input ι) (R T seed : Ideal O) :
    maskedSource (idealGenerator T) (original s R seed).beta =
      (original s (R*T) seed).beta := by
  simpa only [OriginalData.beta, OriginalData.profile, original] using
    column_combined_mask (Fintype.piFinset s.pools) R T seed s.ν s.W s.P
      s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1

lemma normalized_input_mask (s : Input ι) (R T seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (sourceGaussEnergy (original s R seed).columns
      (maskedSource (idealGenerator T) (original s R seed).beta)
      (heightCoeff s.η s.t) W K).re / volume s =
      normalizedGaussSource s (R*T) seed W K := by
  rw [input_combined_mask]
  rfl

lemma child_input_combined_mask (s : Input ι) (C R T seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ) :
    maskedSource (idealGenerator T)
      (original (child s C R B τ t) (R*C) seed).beta =
      (original (child s C (R*T) B τ t) ((R*T)*C) seed).beta := by
  rw [input_combined_mask]
  simp only [OriginalData.beta, OriginalData.profile, original, child, commonData, Input.pools,
    mul_assoc, mul_comm C T]

lemma normalized_child_mask (s : Input ι) (C R T seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (sourceGaussEnergy (original (child s C R B τ t) (R*C) seed).columns
      (maskedSource (idealGenerator T)
        (original (child s C R B τ t) (R*C) seed).beta)
      (heightCoeff τ t) W K).re / volume (child s C R B τ t) =
      childNormalizedGaussSource s C (R*T) seed B τ t W K := by
  have hcolumns :
      (original (child s C R B τ t) (R*C) seed).columns =
        (original (child s C (R*T) B τ t) ((R*T)*C) seed).columns :=
    (child_columns s C R seed B τ t).1.symm.trans (child_columns s C (R*T) seed B τ t).1
  have hvolume : volume (child s C R B τ t) = volume (child s C (R*T) B τ t) := by
    simp only [volume, child, commonData]
  unfold childNormalizedGaussSource normalizedGaussSource
  rw [child_input_combined_mask, hcolumns, hvolume, child_character, child_height]

end OAI.SevenEighths.Angular.PlainRows.FirstPhysical.MaskedInput

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.MaskedInput.input_combined_mask
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.MaskedInput.input_combined_mask

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.MaskedInput.normalized_input_mask
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.MaskedInput.normalized_input_mask

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.MaskedInput.child_input_combined_mask
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.MaskedInput.child_input_combined_mask

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.MaskedInput.normalized_child_mask
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.MaskedInput.normalized_child_mask
