import AngularPhysicalExceptionalFamilyGates
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalKernel

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace OAI.SevenEighths.Angular.SecondExceptionalKernel
open PlainRows ChildRows ExceptionalRows
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSupport CenteredMomentRestrictedEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentSmooth CenteredMomentSupportedCorrelation CenteredMomentMobiusRegroup
open CenteredMomentSecondExceptionalKernel (whole_kernel_actual_second_pair)
local notation "O" => ActualEisensteinCubic.O
theorem exceptional_rows_pair (η:AngularCharacter)(χ₀ χ ξ:RayCharacter)(Q:Ideal O)
    (hQ:Q≤Ideal.span {(72:O)})(m A:O)(hmLam:ConcretePrimeRowBridge.goodLambda∣m)
    (hm2:(2:O)∣m)(rows:Finset O)
    (hrows:∀z∈rows,FixedInducingRow (childCharacter η χ₀) Q m A z):
    (∀z∈rows,FixedInducingRow (childCharacter η χ) Q m A z) ∧
    (∀z∈rows,FixedInducingRow (childCharacter η (ξ⁻¹)) Q m A (-z)):=by
  constructor
  · intro z hz
    have hh:=ExceptionalRows.fixedInducingRow_reflected
      η χ₀ χ₀ Q hQ m A z hmLam hm2 (hrows z hz)
    simpa only [neg_neg] using
      ExceptionalRows.fixedInducingRow_reflected
        η χ₀ χ Q hQ m A (-z) hmLam hm2 hh
  · intro z hz
    exact ExceptionalRows.fixedInducingRow_reflected
      η χ₀ (ξ⁻¹) Q hQ m A z hmLam hm2 (hrows z hz)

end OAI.SevenEighths.Angular.SecondExceptionalKernel

#print axioms OAI.SevenEighths.Angular.SecondExceptionalKernel.exceptional_rows_pair
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondExceptionalKernel.exceptional_rows_pair
