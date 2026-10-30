import AngularPhysicalMaskedAmplitude
import OAI.NumberTheory.DirichletL.Moments.WholeDivisorShell

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
variable {κ:Type u} [Fintype κ] [DecidableEq κ]
theorem paired_masked_le (s:Data ι)(v:Data κ)(D:Ideal O)(hD:Squarefree D)(rows:Finset O):
    (∑z∈rows,‖maskedAmplitude s D z‖*‖maskedAmplitude v D z‖)≤
      ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
        ∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖:=by
  calc
    _≤∑z∈rows,(∑a∈s.toSource.active D,‖amplitude s D a z‖)*
        (∑b∈v.toSource.active D,‖amplitude v D b z‖):=by
      apply Finset.sum_le_sum
      intro z hz
      rw [maskedAmplitude_eq s D hD,maskedAmplitude_eq v D hD]
      exact mul_le_mul (norm_sum_le _ _) (norm_sum_le _ _) (norm_nonneg _)
        (Finset.sum_nonneg (fun a _=>norm_nonneg _))
    _=_:=by
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_comm (s:=rows) (t:=s.toSource.active D)]
      exact Finset.sum_comm

theorem whole_masked_le (s:Data ι)(v:Data κ)(Ds:Finset (Ideal O))(rows:Finset O):
    (∑D∈Ds,‖(moebius D:ℂ)‖*∑z∈rows,‖maskedAmplitude s D z‖*‖maskedAmplitude v D z‖)≤
      ∑D∈Ds,‖(moebius D:ℂ)‖*∑a∈s.toSource.active D,∑b∈v.toSource.active D,
        ∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖:=by
  apply Finset.sum_le_sum
  intro D hD
  by_cases hμ:(moebius D:ℂ)=0
  · simp [hμ]
  · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply paired_masked_le s v D
    exact CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero D hμ

end OAI.SevenEighths.Angular.ExceptionalMaskedSource

#print axioms OAI.SevenEighths.Angular.ExceptionalMaskedSource.paired_masked_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ExceptionalMaskedSource.paired_masked_le

#print axioms OAI.SevenEighths.Angular.ExceptionalMaskedSource.whole_masked_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ExceptionalMaskedSource.whole_masked_le
