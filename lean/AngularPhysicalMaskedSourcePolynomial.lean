import AngularPhysicalMaskedAmplitude
import AngularPhysicalPlainSourceEnergy

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace OAI.SevenEighths.Angular.ExceptionalMaskedSource
open PlainRows DetectorAmplitude ExceptionalAmplitudePair ExceptionalShell ExceptionalSourceShell
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorExtraction
open CenteredMomentDivisorRectangle CenteredMomentDetectorDictionary UniqueFactorizationMonoid
open CenteredMomentExceptionalAmplitudePair (Tests)
open CanonicalQuadraticSieve ConcretePrimeRowBridge CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRectangle
open CenteredMomentSecondHeightFamily (fixedBadMask)
local notation "O" => ActualEisensteinCubic.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]
theorem source_polynomial_eq (s:Data ι)(S₁ S₂:Finset (Ideal O))(R D B₁ B₂:Ideal O)
    (X₁ X₂ Y₁ Y₂:ℝ)
    (hm:s.m=fixedBadMask*idealGenerator R)(hA:s.A=1)
    (hX₁:s.X₁=X₁/Ideal.absNorm B₁)(hX₂:s.X₂=X₂/Ideal.absNorm B₂)
    (hY₁:s.Y₁=Y₁/Ideal.absNorm B₁)(hY₂:s.Y₂=Y₂/Ideal.absNorm B₂)
    (hc₁:PlainCoverage S₁ s.W₁ B₁ X₁ Y₁)(hc₂:PlainCoverage S₂ s.W₂ B₂ X₂ Y₂)(z:O):
    (Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
      rowPolynomial Finset.univ (sourceGenerator (finiteColumns (tuplePool s.slots S₁ S₂)))
        (fun I: supportedColumns (finiteColumns (tuplePool s.slots S₁ S₂))=>
          finiteColumnCoefficient (tuplePool s.slots S₁ S₂)
            (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ D) I*
              heightCoeff s.η s.t I) z=maskedAmplitude s D z:=by
  rw [height_source_row]
  rw [PlainRows.source_polynomial_eq_maskedRectangle
    s.η fixedBadMask 1 z s.t (dvd_mul_right _ _) (dvd_mul_left _ _)
    s.slots S₁ S₂ R D s.ν s.W s.P s.W₁ s.W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hc₁ hc₂]
  simp only [maskedAmplitude,hm,hA,hX₁,hX₂,hY₁,hY₂]
  rfl

end OAI.SevenEighths.Angular.ExceptionalMaskedSource

#print axioms OAI.SevenEighths.Angular.ExceptionalMaskedSource.source_polynomial_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ExceptionalMaskedSource.source_polynomial_eq
