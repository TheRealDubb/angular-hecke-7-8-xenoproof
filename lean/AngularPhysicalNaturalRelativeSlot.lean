import AngularPhysicalFixedAnchorPrimeQuarter
import AngularPhysicalCommonMaskEnergy

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace OAI.SevenEighths.Angular.RelativeFloor
open RelativePrime PlainRows NaturalRows ExceptionalRows CommonMask
open CenteredMomentCommonMaskEnergy (heightCoefficient)
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentSecondHeightFamily (fixedBadMask)
local notation "O" => ActualEisensteinCubic.O
lemma natural_slot_eq {η : AngularCharacter} {z : O} (F : NaturalRow η z)
    (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P t : ℝ) :
    naturalSlot F.character pool (heightCoefficient β t) P=
      normalizedSlot η fixedBadMask 1 z pool β t P := by
  unfold naturalSlot normalizedSlot rowSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [F.ideal]
  simp only [heightCoefficient,one_mul]
  ring

end OAI.SevenEighths.Angular.RelativeFloor

#print axioms OAI.SevenEighths.Angular.RelativeFloor.natural_slot_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativeFloor.natural_slot_eq
