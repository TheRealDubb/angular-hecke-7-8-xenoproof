import AngularPhysicalNaturalRow
import AngularPhysicalPlainSummability
import OAI.NumberTheory.DirichletL.Moments.RadialEligibleEnergy

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular
open PlainRows ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentPositiveSummability (bounded_radial_summable)
open CenteredMomentAbsoluteEnergy (radial_norm_summable)
open CenteredMomentCounting (norm_tsum_ideal_ball)
open CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => ActualEisensteinCubic.O

open CenteredMomentSecondHeightFamily (fixedBadMask)
open ConcretePrimeRowBridge
namespace NaturalRows
lemma NaturalRow.masked_plain {η : AngularCharacter} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (W : ℝ→ℂ) (t X : ℝ) :
    rowTwistedSum η (fixedBadMask*idealGenerator R) 1 z W t X=
      twistedIdealSum (excluded F.character R) W t X := by
  exact rowTwistedSum_eq η (excluded F.character R) (fixedBadMask*idealGenerator R) 1 z
    (by simpa only [one_mul] using F.masked_element R hR) W t X

lemma NaturalRow.masked_slot {η : AngularCharacter} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (S : Finset (Ideal O)) (β : Ideal O→ℂ) (t : ℝ) :
    rowSlot η (fixedBadMask*idealGenerator R) 1 z S β t=
      ∑I∈S,β I*(excluded F.character R).idealHom I*(I.absNorm:ℂ)^(Complex.I*t) := by
  unfold rowSlot
  apply Finset.sum_congr rfl
  intro I hI
  rw [F.masked_ideal R hR I,one_mul]

theorem NaturalRow.masked_positive {ι : Type*} [instι:Fintype ι] [decι:DecidableEq ι]
    {η : AngularCharacter} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ)
    (P : ι→ℝ) (t X₁ X₂ : ℝ) :
    positiveSlotRow η (fixedBadMask*idealGenerator R) 1 z W₁ W₂ S β P t X₁ X₂=
      (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹*
        ((twistedIdealSum (excluded F.character R) W₁ t X₁*
          twistedIdealSum (excluded F.character R) W₂ t X₂)*
          ∏i,∑I∈S i,β i I*(excluded F.character R).idealHom I*(I.absNorm:ℂ)^(Complex.I*t)) := by
  simp only [positiveSlotRow,F.masked_plain R hR,F.masked_slot R hR]

theorem NaturalRow.masked_retained {ι : Type*} [instι:Fintype ι] [decι:DecidableEq ι]
    {η : AngularCharacter} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ)
    (P : ι→ℝ) (t X₁ X₂ : ℝ) :
    retainedPositiveRow η (fixedBadMask*idealGenerator R) 1 z W₁ W₂ S β P t X₁ X₂=
      (Real.sqrt (clippedScale X₁*clippedScale X₂*∏i,P i):ℂ)⁻¹*
        ((twistedIdealSum (excluded F.character R) (dilated W₁ (clipDilation X₁)) t (clippedScale X₁)*
          twistedIdealSum (excluded F.character R) (dilated W₂ (clipDilation X₂)) t (clippedScale X₂))*
          ∏i,∑I∈S i,β i I*(excluded F.character R).idealHom I*(I.absNorm:ℂ)^(Complex.I*t)) := by
  exact F.masked_positive R hR _ _ S β P t _ _


end NaturalRows

end OAI.SevenEighths.Angular

#print axioms OAI.SevenEighths.Angular.NaturalRows.NaturalRow.masked_positive
#print axioms OAI.SevenEighths.Angular.NaturalRows.NaturalRow.masked_retained
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalRows.NaturalRow.masked_retained
