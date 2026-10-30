import AngularPhysicalSecondSupportedEnvelope

set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.PhysicalBlock
open PlainRows PlainRows.CommonRows PlainRows.RadialEnergy
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentSecondOriginalChildren (sourceRadial)
open Filter
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
def core (s:Input ι) (C:Ideal O) (C0 Z δ E:ℝ) : ℝ :=
  C0*Z^δ*(profileCost s*E)*(s.X₁*s.X₂*∏i,s.P i)/(Ideal.absNorm C:ℝ)

omit [DecidableEq ι] in
lemma envelope_eq_core (s:Input ι) (C L:Ideal O) (C0 Z δ E:ℝ) :
    envelope s C L C0 Z δ E=core s C C0 Z δ E/(Ideal.absNorm L:ℝ):=by
  unfold envelope core;ring

end OAI.SevenEighths.Angular.PhysicalBlock

#print axioms OAI.SevenEighths.Angular.PhysicalBlock.envelope_eq_core
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalBlock.envelope_eq_core
