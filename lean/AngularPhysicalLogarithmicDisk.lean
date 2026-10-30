import AngularPhysicalRegularGrowth
import AngularPhysicalEulerLog

/-! Local disk control. The disk zero-free condition is explicit;
no global angular zero-supremum or numerical target is used. -/
noncomputable section
open scoped Classical Topology
open Set Metric Complex
namespace OAI.SevenEighths.Angular.PhysicalLogarithmic
open PhysicalLogarithmicInput

theorem disk_control (n : ℕ) (e ε : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (hε : 0 < ε) :
    ∃ D B : ℝ, 0 < D ∧ 0 ≤ B ∧ ∀ χ : AngularCharacter, χ.k.natAbs ≤ n →
      FiniteFourier.IsPrimitiveOnIdeals χ.residue → ∀ a t : ℝ,
      1/2 ≤ a → a ≤ 1 →
      (∀ z ∈ ball ((2:ℂ)+t*I) (2-a-2*e), regular χ z ≠ 0) →
      (∀ z ∈ closedBall ((2:ℂ)+t*I) (2-a-6*e),
        ‖regular χ z‖+‖(regular χ z)⁻¹‖ ≤ D*(complexity χ t)^ε) ∧
      (∀ z ∈ closedBall ((2:ℂ)+t*I) (2-a-8*e),
        ‖deriv (regular χ) z / regular χ z‖ ≤ B*Real.log (complexity χ t)) := by
  obtain ⟨M,hM,hpoly⟩ := exists_uniform_polynomial_exponent n
  obtain ⟨D,hD,hcontrol⟩ := LogarithmicControl.logarithmic_control
    he he' innerBound_ge_one hM hε
  refine ⟨D,LogarithmicControl.outerConstant e innerBound M/(2*e),hD,?_,?_⟩
  · have hB := LogarithmicControl.outerConstant_ge_one he he' innerBound_ge_one hM
    positivity
  · intro χ hn hp a t ha ha' hzero
    obtain ⟨hE,hEL,hEb⟩ := actual_inner_log χ t
    exact hcontrol a (complexity χ t) (regular χ) (eulerLog χ) ((2:ℂ)+t*I)
      ha ha' (complexity_ge_exp χ t) (regular_disk_differentiable χ ha he) hzero
      (hpoly χ hn hp a e t ha he) hE hEL hEb


end OAI.SevenEighths.Angular.PhysicalLogarithmic

#print axioms OAI.SevenEighths.Angular.PhysicalLogarithmic.disk_control
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLogarithmic.disk_control
