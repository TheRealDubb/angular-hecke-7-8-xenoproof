import AngularPhysicalAnnularFourierRay

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace OAI.SevenEighths.Angular.AnnularFourier
open FourierBridge EisensteinSchwartzPoisson

theorem absolute_order_euler_bound (angularOrder:ℕ) (a b:ℝ) (ha:0<a) (A J:ℕ) :
    ∃(S:Finset (ℕ×ℕ))(C:ℝ),0<C ∧ ∀k:ℤ,k.natAbs=angularOrder →
      ∀(W:𝓢(ℝ,ℂ))(j:ℕ),j≤J → ∀x:ℝ,0≤x →
      (1+x)^A*‖LocalLogFourier.eulerDeriv (profile k a b ha W) j x‖≤
        C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨S₁,C₁,hC₁,h₁⟩:=profile_euler_weighted_bound (angularOrder:ℤ) a b ha A J
  obtain ⟨S₂,C₂,hC₂,h₂⟩:=profile_euler_weighted_bound (-(angularOrder:ℤ)) a b ha A J
  refine ⟨S₁∪S₂,C₁+C₂,by positivity,?_⟩
  intro k hk W j hj x hx
  have hS₁:S₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) W≤
      (S₁∪S₂).sup (schwartzSeminormFamily ℝ ℝ ℂ) W:=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_left) W
  have hS₂:S₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) W≤
      (S₁∪S₂).sup (schwartzSeminormFamily ℝ ℝ ℂ) W:=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) W
  rcases Int.natAbs_eq_iff.mp hk with rfl|rfl
  · exact (h₁ W j hj x hx).trans (mul_le_mul (by linarith) hS₁ (apply_nonneg _ _) (by positivity))
  · exact (h₂ W j hj x hx).trans (mul_le_mul (by linarith) hS₂ (apply_nonneg _ _) (by positivity))

end OAI.SevenEighths.Angular.AnnularFourier

#print axioms OAI.SevenEighths.Angular.AnnularFourier.absolute_order_euler_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AnnularFourier.absolute_order_euler_bound
