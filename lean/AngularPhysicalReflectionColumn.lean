import AngularPhysicalReflectionMass
import OAI.NumberTheory.DirichletL.Moments.ReflectionTailMass

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.ReflectionMass
open CenteredMomentReflectionDeletion (SmoothIdeal norm subset_product_moebius)
open CenteredMomentReflectionMass (weight smooth_summable smooth_mass_le_euler weight_nonneg
  deletion_mass localMass euler_mass_subpower unitSmooth)
open PlainDeletion (reflectedTerm)
open UniqueFactorizationMonoid IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

theorem coefficient_column_bound (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O))(_hS : ∀P∈S,Prime P)
      (η ηi : AngularCharacter)(f : Finset (Ideal O)→SmoothIdeal S→ℂ)(B : ℝ),0≤B →
      (∀D∈S.powerset,∀H,‖f D H‖≤B) →
      (∀D∈S.powerset,Summable (fun H=>coefficient η ηi S D H*f D H)) ∧
      ‖∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient η ηi S D H*f D H‖≤
        C*(Ideal.absNorm (∏P∈S,P):ℝ)^ε*B := by
  obtain ⟨C,hC,hbound⟩ := reflection_mass_subpower ε hε
  refine ⟨C,hC,?_⟩
  intro S hS η ηi f B hB hf
  have hs (D : Finset (Ideal O)) (hD : D∈S.powerset) :
      Summable (fun H : SmoothIdeal S=>‖coefficient η ηi S D H*f D H‖) := by
    apply ((coefficient_summable_norm η ηi S hS D (Finset.mem_powerset.mp hD)).mul_right B).of_nonneg_of_le
      (fun _=>norm_nonneg _)
    intro H
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hf D hD H) (norm_nonneg _)
  refine ⟨fun D hD=>(hs D hD).of_norm,?_⟩
  calc
    _≤∑D∈S.powerset,∑'H : SmoothIdeal S,‖coefficient η ηi S D H*f D H‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun D hD=>norm_tsum_le_tsum_norm (hs D hD)))
    _≤∑D∈S.powerset,(∑'H : SmoothIdeal S,‖coefficient η ηi S D H‖)*B := by
      apply Finset.sum_le_sum
      intro D hD
      rw [←tsum_mul_right]
      apply (hs D hD).tsum_le_tsum _
        ((coefficient_summable_norm η ηi S hS D (Finset.mem_powerset.mp hD)).mul_right B)
      intro H
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hf D hD H) (norm_nonneg _)
    _≤_ := by
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hbound S hS η ηi).2 hB


end OAI.SevenEighths.Angular.ReflectionMass

#print axioms OAI.SevenEighths.Angular.ReflectionMass.coefficient_column_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ReflectionMass.coefficient_column_bound
