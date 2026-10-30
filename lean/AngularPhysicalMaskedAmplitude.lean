import AngularPhysicalExceptionalProfileMass

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
def maskedAmplitude (s:Data ι)(D:Ideal O)(z:O):ℂ:=
  (Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
    maskedRectangle s.η s.m s.A z s.t s.slots s.coefficient D s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂

theorem maskedAmplitude_eq (s:Data ι)(D:Ideal O)(hD:Squarefree D)(z:O):
    maskedAmplitude s D z=∑a∈s.toSource.active D,amplitude s D a z:=by
  unfold maskedAmplitude
  rw [masked_eq_active_allocations s.η s.m s.A z s.t s.slots s.coefficient D hD
    s.W₁ s.W₂ s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ s.support₁ s.support₂
    s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos,Finset.mul_sum]
  rfl

end OAI.SevenEighths.Angular.ExceptionalMaskedSource

#print axioms OAI.SevenEighths.Angular.ExceptionalMaskedSource.maskedAmplitude_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ExceptionalMaskedSource.maskedAmplitude_eq
