import AngularPhysicalAnnularFourierAbsoluteOrder
import OAI.NumberTheory.DirichletL.Moments.ComparisonReflection

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace OAI.SevenEighths.Angular.AnnularFourier
open FourierBridge EisensteinSchwartzPoisson

theorem absolute_order_height_control (angularOrder:ℕ) (a b:ℝ) (ha:0<a) (A J:ℕ) :
    ∃n:ℕ,∀W:ℝ→ℂ,∀hs:Function.support W⊆Set.Icc a b,∀hW:ContDiff ℝ ∞ W,
      ∃C:ℝ,0<C ∧ ∀k:ℤ,k.natAbs=angularOrder → ∀t:ℝ,∀j:ℕ,j≤J → ∀x:ℝ,0≤x →
      (1+x)^A*‖LocalLogFourier.eulerDeriv
        (profile k a b ha (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t)) j x‖≤
          C*(1+‖t‖)^n := by
  obtain ⟨S,C,hC,hbound⟩:=absolute_order_euler_bound angularOrder a b ha A J
  obtain ⟨n,hn⟩:=CompletedHeight.normTwistedSource_uniform_degree a b ha S
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨D,hD,hDb⟩:=hn W hs hW
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro k hk t j hj x hx
  exact (hbound k hk _ j hj x hx).trans
    ((mul_le_mul_of_nonneg_left (hDb t) hC.le).trans_eq (by ring))

end OAI.SevenEighths.Angular.AnnularFourier

#print axioms OAI.SevenEighths.Angular.AnnularFourier.absolute_order_height_control
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AnnularFourier.absolute_order_height_control
