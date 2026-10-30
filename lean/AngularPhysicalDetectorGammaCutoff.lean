import AngularPhysicalAnalyticSeries
import OAI.NumberTheory.DirichletL.GammaZeroDetector

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Complex
namespace OAI.SevenEighths.Angular.PhysicalGammaDetector
open FamilyContinuation GammaZeroDetector
def cutoffTerm (χ : AngularCharacter) (V : ℝ → ℂ) (D : ℝ) (J : Ideal O) (s : ℂ) : ℂ :=
  Dyadic.coefficient χ true J * V ((J.absNorm : ℝ)/D) *
    CubicEisenstein.fullIdealWeight s J

def cutoff (χ : AngularCharacter) (V : ℝ → ℂ) (D : ℝ) (s : ℂ) : ℂ :=
  ∑ J ∈ cutoffSet D, cutoffTerm χ V D J s

@[simp] theorem cutoffTerm_zero (χ : AngularCharacter) (V : ℝ → ℂ) (D : ℝ) (s : ℂ) :
    cutoffTerm χ V D 0 s = 0 := by
  simp [cutoffTerm, CubicEisenstein.fullIdealWeight]

theorem cutoffTerm_eq (χ : AngularCharacter) (V : ℝ → ℂ) (D : ℝ) {J : Ideal O}
    (hJ : J ≠ 0) (s : ℂ) :
    cutoffTerm χ V D J s = (UniqueFactorizationMonoid.moebius J : ℂ) *
      χ.idealHom J * V ((J.absNorm : ℝ)/D) * (J.absNorm : ℂ)^(-s) := by
  rw [cutoffTerm, CubicEisenstein.fullIdealWeight, ite_eq_right hJ]
  rfl

theorem cutoff_eq_tsum (χ : AngularCharacter) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) :
    cutoff χ V D s = ∑' J : Ideal O, cutoffTerm χ V D J s := by
  symm
  apply tsum_eq_sum
  intro J hJ
  by_cases hzero : J = 0
  · subst J; exact cutoffTerm_zero χ V D s
  · have hn : 2*D < (J.absNorm : ℝ) := by
      by_contra h
      exact hJ ((mem_cutoffSet hD.le).mpr ⟨hzero, le_of_not_gt h⟩)
    have hv := hV ((J.absNorm : ℝ)/D) ((le_div_iff₀ hD).mpr hn.le)
    simp [cutoffTerm, hv]

theorem cutoffTerm_entire (χ : AngularCharacter) (V : ℝ → ℂ) (D : ℝ) (J : Ideal O) :
    Differentiable ℂ (cutoffTerm χ V D J) := by
  by_cases hJ : J = 0
  · subst J
    have he : cutoffTerm χ V D 0 = fun _ : ℂ => 0 := funext (cutoffTerm_zero χ V D)
    rw [he]
    exact differentiable_const 0
  · have hn : (J.absNorm : ℂ) ≠ 0 := by
      exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hJ
    unfold cutoffTerm
    simp only [CubicEisenstein.fullIdealWeight, ite_eq_right hJ]
    exact (differentiable_id.neg.const_cpow (Or.inl hn)).const_mul _

theorem cutoff_entire (χ : AngularCharacter) (V : ℝ → ℂ) (D : ℝ) :
    Differentiable ℂ (cutoff χ V D) := by
  exact Differentiable.fun_sum fun J _ => cutoffTerm_entire χ V D J

theorem cutoffTerm_norm_le (χ : AngularCharacter) (V : ℝ → ℂ) (D : ℝ)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {s : ℂ} (hs : 0 ≤ s.re) (J : Ideal O) :
    ‖cutoffTerm χ V D J s‖ ≤ 1 := by
  by_cases hJ : J = 0
  · subst J
    rw [cutoffTerm_zero, norm_zero]
    norm_num
  · have hnorm : 1 ≤ (J.absNorm : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
    have hw : ‖CubicEisenstein.fullIdealWeight s J‖ ≤ 1 := by
      rw [CubicEisenstein.fullIdealWeight, ite_eq_right hJ]
      have hn : 0 < (J.absNorm : ℝ) := by linarith
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn, neg_re]
      exact (Real.rpow_le_rpow_of_exponent_le hnorm (neg_nonpos.mpr hs)).trans_eq (Real.rpow_zero _)
    rw [cutoffTerm, norm_mul, norm_mul]
    calc
      _ ≤ (1 : ℝ)*1*1 := by gcongr; exact Dyadic.coefficient_norm_le χ true J; exact hV _
      _ = 1 := by norm_num

theorem cutoff_norm_le (χ : AngularCharacter) (V : ℝ → ℂ) {D : ℝ} (hD : 1 ≤ D)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖cutoff χ V D s‖ ≤ 256*D := by
  have hcount := DescentFiberCost.finite_ideal_count_real (cutoffSet D) (2*D) (by linarith)
    (fun J hJ => ((mem_cutoffSet (by linarith : 0 ≤ D)).mp hJ).1)
    (fun J hJ => ((mem_cutoffSet (by linarith : 0 ≤ D)).mp hJ).2)
  calc
    _ ≤ ∑ J ∈ cutoffSet D, ‖cutoffTerm χ V D J s‖ := norm_sum_le _ _
    _ ≤ ∑ _J ∈ cutoffSet D, (1 : ℝ) := Finset.sum_le_sum (fun J _ => cutoffTerm_norm_le χ V D hV hs J)
    _ = ((cutoffSet D).card : ℝ) := by simp
    _ ≤ 256*D := by linarith


end OAI.SevenEighths.Angular.PhysicalGammaDetector


#print axioms OAI.SevenEighths.Angular.PhysicalGammaDetector.cutoffTerm_zero
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalGammaDetector.cutoffTerm_zero

#print axioms OAI.SevenEighths.Angular.PhysicalGammaDetector.cutoffTerm_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalGammaDetector.cutoffTerm_eq

#print axioms OAI.SevenEighths.Angular.PhysicalGammaDetector.cutoff_eq_tsum
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalGammaDetector.cutoff_eq_tsum

#print axioms OAI.SevenEighths.Angular.PhysicalGammaDetector.cutoffTerm_entire
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalGammaDetector.cutoffTerm_entire

#print axioms OAI.SevenEighths.Angular.PhysicalGammaDetector.cutoff_entire
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalGammaDetector.cutoff_entire

#print axioms OAI.SevenEighths.Angular.PhysicalGammaDetector.cutoffTerm_norm_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalGammaDetector.cutoffTerm_norm_le

#print axioms OAI.SevenEighths.Angular.PhysicalGammaDetector.cutoff_norm_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalGammaDetector.cutoff_norm_le
