import AngularPhysicalFirstRetainedSector
import OAI.NumberTheory.DirichletL.Moments.FirstRetainedActive

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace OAI.SevenEighths.Angular.PlainRows.FirstPhysical
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstRetainedSector CenteredMomentSourceRow PlainRows
open CenteredMomentFirstSectors CenteredMomentSupportedCorrelation
open CenteredMomentActiveSource (activeSource supportedColumns_active)
local notation "O"=>ActualEisensteinCubic.O


theorem retained_energy_sum (η:AngularCharacter)(m A:O)(t:ℝ)(S:Finset (Ideal O))
    (β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    PlainRows.retainedEnergy η m A t S β W K X Z ξ=
      ∑I∈supportedColumns S,∑J∈supportedColumns S,
        ((β I*rowWeight η m A 1 t I)*star (β J*rowWeight η m A 1 t J))*
          CenteredMomentFirstRetainedSector.retainedKernel I J W K X Z ξ:=by
  unfold PlainRows.retainedEnergy
  conv_rhs=>rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro I hI
  conv_rhs=>rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [retainedKernel_eq I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2]

theorem retained_energy_active (η:AngularCharacter)(m A:O)(t:ℝ)(S:Finset (Ideal O))
    (β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    PlainRows.retainedEnergy η m A t (activeSource S β) β W K X Z ξ=
      PlainRows.retainedEnergy η m A t S β W K X Z ξ:=by
  rw [retained_energy_sum,retained_energy_sum,supportedColumns_active]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hi:β I=0
  · simp [hi]
  · rw [ite_eq_left hi]
    apply Finset.sum_congr rfl
    intro J hJ
    by_cases hj:β J=0 <;> simp [hj]

end OAI.SevenEighths.Angular.PlainRows.FirstPhysical

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.retained_energy_sum
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.retained_energy_sum

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.retained_energy_active
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.retained_energy_active
