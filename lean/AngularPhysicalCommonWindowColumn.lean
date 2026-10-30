import AngularPhysicalWholeWindowPair
import AngularPhysicalCommonPairedColumns
import AngularPhysicalCommonHeightEnvelope
import OAI.NumberTheory.DirichletL.Moments.CommonWindowColumn

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace OAI.SevenEighths.Angular.CommonExceptionalSource
open PlainRows ExceptionalAmplitudePair ExceptionalWindow
open PlainRows.CommonRows (Input withHeight)
open CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentFirstSectors CenteredMomentRowNorm CenteredMomentHeckeColumnWindow
open CenteredMomentSmooth
open CenteredMomentExceptionalWholeWindow (rowPolynomial_factor)
open CenteredMomentCommonWindowColumn (sourceGenerator_span)
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _
def columns (s:Input ι)(C:Ideal O)(hC:Supported C):Finset (Ideal O):=
  residualPool C hC.1 (finiteColumns (Fintype.piFinset s.pools))

def coefficient (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (I:supportedColumns (columns s C hC)):ℂ:=
  (Real.sqrt (volume s.toData):ℂ)⁻¹*
    (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then
      finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) (C*I) else 0)

def windowColumn (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (η:AngularCharacter)(t θ X:ℝ)(V:ℝ→ℂ)(z:O):ℂ:=
  rowPolynomial Finset.univ (sourceGenerator (columns s C hC))
    (fun I=>coefficient s C hC R seed L I*heightCoeff η t I*
      columnPhase V (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) z

theorem coefficient_polynomial (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (η:AngularCharacter)(t:ℝ)(z:O):
    rowPolynomial Finset.univ (sourceGenerator (columns s C hC))
      (fun I=>coefficient s C hC R seed L I*heightCoeff η t I) z=
      normalizedColumn (withHeight s η t) C hC R seed L z:=by
  unfold normalizedColumn sourceColumn
  dsimp only [withHeight,Input.pools,columns]
  simp only [coefficient,mul_assoc,rowPolynomial_factor,Input.pools,columns]
  rfl

end OAI.SevenEighths.Angular.CommonExceptionalSource

#print axioms OAI.SevenEighths.Angular.CommonExceptionalSource.coefficient_polynomial
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CommonExceptionalSource.coefficient_polynomial
