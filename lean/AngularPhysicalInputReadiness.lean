import AngularPhysicalChildEventualCaps
import OAI.NumberTheory.DirichletL.Moments.FirstSecondInputGates

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission
open CommonRows ChildInputs ChildSourceCaps FirstAnnularInput
open CanonicalQuadraticSieve CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
open CenteredMomentSectorLocalization
open CenteredMomentFirstSecondInputGates (exponent)
open CenteredMomentAmplificationChildSourceCaps
  (geometry geometry_ge_one norm_ge_one puncture_norm eventual_geometry polynomial_caps)
local notation "O" => ActualEisensteinCubic.O
local instance AngularInputReadinessDecEq {κ:Type*} : DecidableEq κ := Classical.decEq _
structure Ready {ι:Type*}[Fintype ι](s:Input ι)(R:Ideal O)(K Z ξ B:ℝ):Prop where
  puncture_ne : R≠0
  scale_pos : 0<K
  volume_cap : volume s≤Z^B
  source_nonneg : 0≤sourceRadius s
  source_cap : sourceRadius s≤Z^B
  conductor_cap : (s.η.modulus.absNorm:ℝ)≤Z^B
  puncture_cap : (R.absNorm:ℝ)≤Z^B
  nominal_pos : 0<nominal s K
  nominal_cap : nominal s K≤Z^B
  frequency_pos : 0<frequencyRadius (nominal s K) Z ξ
  frequency_cap : frequencyRadius (nominal s K) Z ξ≤Z^B

theorem normalized_zero {ι:Type*}[Fintype ι](s:Input ι)(R seed:Ideal O)
    (hz:∀I:Ideal O,(original s R seed).beta I=0)(W:𝓢(ℝ,ℂ))(K:ℝ):
    normalizedGaussSource s R seed W K=0:=by
  simp [normalizedGaussSource,sourceGaussEnergy,gaussEnergy,gaussPolynomial,hz]

end OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.normalized_zero
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.normalized_zero
