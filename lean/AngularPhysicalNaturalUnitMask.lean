import AngularPhysicalNaturalRowDictionary

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.NaturalRows
open PlainRows ConcretePrimeRowBridge
open CenteredMomentSecondHeightFamily (fixedBadMask)
local notation "O" => ActualEisensteinCubic.O

lemma excluded_one_ideal (χ:AngularCharacter) (I:Ideal O) :
    (excluded χ 1).idealHom I=χ.idealHom I := by
  simp only [excluded_ideal χ 1 one_ne_zero,isCoprime_one_right,ite_true]

lemma natural_unit_mask_coefficient {η:AngularCharacter} {z:O} (F:NaturalRow η z) (I:Ideal O) :
    η.idealHom I*CanonicalRowCompletion.idealRowHom ((fixedBadMask*idealGenerator 1)^6*z) I=
      η.idealHom I*CanonicalRowCompletion.idealRowHom (fixedBadMask^6*z) I := by
  rw [←F.masked_ideal 1 one_ne_zero,excluded_one_ideal,F.ideal]

lemma natural_unit_mask_positive {ι:Type*} [Fintype ι] [DecidableEq ι]
    {η:AngularCharacter} {z:O} (F:NaturalRow η z) (W₁ W₂:ℝ→ℂ)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ) (t X₁ X₂:ℝ) :
    positiveSlotRow η (fixedBadMask*idealGenerator 1) 1 z W₁ W₂ S β P t X₁ X₂=
      positiveSlotRow η fixedBadMask 1 z W₁ W₂ S β P t X₁ X₂ := by
  simp only [positiveSlotRow,rowTwistedSum,rowSlot,one_mul,natural_unit_mask_coefficient F]

end OAI.SevenEighths.Angular.NaturalRows

#print axioms OAI.SevenEighths.Angular.NaturalRows.excluded_one_ideal
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalRows.excluded_one_ideal

#print axioms OAI.SevenEighths.Angular.NaturalRows.natural_unit_mask_coefficient
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalRows.natural_unit_mask_coefficient

#print axioms OAI.SevenEighths.Angular.NaturalRows.natural_unit_mask_positive
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalRows.natural_unit_mask_positive
