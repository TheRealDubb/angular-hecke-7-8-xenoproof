import AngularPhysicalSourceMomentData
import AngularPhysicalNaturalCharacter
noncomputable section
open scoped Classical
namespace OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource
open NaturalRows
open CenteredMomentSecondHeightFamily
open HeckeInverseAmplification (FreeRow)
open ProbeHighRowFamily (momentElement)
local notation "O" => ActualEisensteinCubic.O
attribute [local irreducible] AngularCharacter.idealHom naturalRow
theorem source_moment_natural_coeff (eta : AngularCharacter) (u : FreeRow) (I : Ideal O) :
    ((SourceRows.momentData eta).character (momentElement u)).idealHom I =
      (naturalCharacter eta u.val).idealHom I := by
  rw [SourceRows.momentData_coeff,naturalCharacter_eq eta u.val u.property.1,
    NaturalRow.ideal]
  rw [show ProbeHighRowFamily.rowMaskElement=fixedBadMask by
    unfold ProbeHighRowFamily.rowMaskElement fixedBadMask; exact mul_comm _ _]


end OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.source_moment_natural_coeff
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.source_moment_natural_coeff
