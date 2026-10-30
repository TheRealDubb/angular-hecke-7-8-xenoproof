import AngularPhysicalNormalizedSourceInput

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
def activeInput (s:Input ι):Input ι:={s with
  slots:=fun i=>(s.slots i).filter (fun I=>s.W i ((I.absNorm:ℝ)/s.P i)≠0)
  prime:=fun i I hI=>s.prime i I (Finset.mem_filter.mp hI).1
  coefficient_bound:=fun i I hI=>s.coefficient_bound i I (Finset.mem_filter.mp hI).1}

lemma original_active (s:Input ι)(R seed:Ideal O):
    original (activeInput s) R seed=(original s R seed).active:=by
  unfold original OriginalData.active
  congr 1
  funext j
  cases j <;> rfl

lemma active_volume (s:Input ι):volume (activeInput s)=volume s:=rfl

lemma active_normalized (s:Input ι)(R seed:Ideal O)(W:𝓢(ℝ,ℂ))(H:ℝ):
    normalizedGaussSource (activeInput s) R seed W H=normalizedGaussSource s R seed W H:=by
  rw [←normalized_input_coefficient,←normalized_input_coefficient,original_active]
  exact congrArg Complex.re (Amplification.active_gaussEnergy (original s R seed) s.η fixedBadMask s.t (volume s) W H)

end OAI.SevenEighths.Angular.PlainRows.FirstAnnularInput

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstAnnularInput.original_active
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstAnnularInput.original_active

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstAnnularInput.active_volume
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstAnnularInput.active_volume

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstAnnularInput.active_normalized
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstAnnularInput.active_normalized
