import AngularPhysicalSecondBlock
import OAI.NumberTheory.DirichletL.Moments.SecondLiveBlock

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PhysicalBlock
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalWindow CenteredMomentSecondSectorRetained
open CenteredMomentSectorLocalization
open CenteredMomentSecondLiveBlock (liveRows)
local notation "O" => ActualEisensteinCubic.O
lemma physicalBlock_live_rows (η:AngularCharacter) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (C D:Ideal O) (hC:Supported C) (hD:Supported D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R (liveRows C D U R rows) W K n:=by
  unfold physicalBlock liveRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hr:retainedWeight R
      (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))=0
  · simp only [hr,ne_eq,not_true_eq_false,physicalKernel,Complex.ofReal_zero,
      mul_zero,zero_mul,Finset.sum_const_zero,ite_self]
  · simp only [hr,ne_eq,not_false_eq_true,ite_true]

lemma physicalBlock_row_split (η:AngularCharacter) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (C D:Ideal O) (hC:Supported C) (hD:Supported D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ) (p:O→Prop):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R ((liveRows C D U R rows).filter p) W K n+
      physicalBlock η t S β C D hC hD U R ((liveRows C D U R rows).filter (fun z=>¬p z)) W K n:=by
  rw [physicalBlock_live_rows η t S β C D hC hD U R rows W K n]
  unfold physicalBlock
  exact (Finset.sum_filter_add_sum_filter_not _ p _).symm


end OAI.SevenEighths.Angular.PhysicalBlock

#print axioms OAI.SevenEighths.Angular.PhysicalBlock.physicalBlock_live_rows
#print axioms OAI.SevenEighths.Angular.PhysicalBlock.physicalBlock_row_split
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalBlock.physicalBlock_row_split
