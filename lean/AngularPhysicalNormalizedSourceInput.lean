import AngularPhysicalActiveAmplification

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows.FirstAnnularInput
open CommonRows ChildInputs Amplification
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalChildEnergy CenteredMomentSecondHeightFamily
open CenteredMomentHeckeColumnWindow CenteredMomentGaussNormalization
open CenteredMomentSourceRow CenteredMomentCommonAllocationSum
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]
theorem normalized_input_coefficient (s:Input ι)(R seed:Ideal O)
    (W:𝓢(ℝ,ℂ))(H:ℝ):
    (gaussEnergy Finset.univ (sourceGenerator (original s R seed).columns)
      (sourceGenerator_supported (original s R seed).columns)
      (originalCoefficient (original s R seed) s.η fixedBadMask s.t (volume s)) W H).re=
      normalizedGaussSource s R seed W H:=by
  unfold originalCoefficient normalizedGaussSource sourceGaussEnergy
  rw [show (fun I:supportedColumns (original s R seed).columns=>
      (Real.sqrt (volume s):ℂ)⁻¹*((original s R seed).beta I*
        PlainRows.rowWeight s.η fixedBadMask 1 1 s.t I))=
      (fun I:supportedColumns (original s R seed).columns=>(Real.sqrt (volume s):ℂ)⁻¹*
        ((original s R seed).beta I*heightCoeff s.η s.t I)) by
    funext I
    rw [←heightCoeff_eq_fixed_rowWeight s.η s.t I (Finset.mem_filter.mp I.property).2]]
  exact gaussEnergy_central _ _ _ _ (volume s) (volume_pos s) W H

theorem normalized_child_coefficient (s:Input ι)(C R seed:Ideal O)
    (B:actualAllocations s.pools C)(τ:AngularCharacter)(t:ℝ)(W:𝓢(ℝ,ℂ))(H:ℝ):
    (gaussEnergy Finset.univ (sourceGenerator (original (child s C R B τ t) (R*C) seed).columns)
      (sourceGenerator_supported (original (child s C R B τ t) (R*C) seed).columns)
      (originalCoefficient (original (child s C R B τ t) (R*C) seed) τ fixedBadMask t
        (volume (child s C R B τ t))) W H).re=
      childNormalizedGaussSource s C R seed B τ t W H:=
  normalized_input_coefficient (child s C R B τ t) (R*C) seed W H

end OAI.SevenEighths.Angular.PlainRows.FirstAnnularInput

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstAnnularInput.normalized_input_coefficient
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstAnnularInput.normalized_input_coefficient

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstAnnularInput.normalized_child_coefficient
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstAnnularInput.normalized_child_coefficient
