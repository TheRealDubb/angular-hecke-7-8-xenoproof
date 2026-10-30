import AngularPhysicalDetectorHighProduct
import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationRows
import OAI.NumberTheory.DirichletL.Detector.InitialMajorant

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
open ActualEisensteinCubic CubicEisenstein ProbePhysical ProbeMellinBoundary
open HeckeFamily HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def fullHighCoefficient (S : Finset (Ideal O)) (D : Ideal O) (η : AngularCharacter)
    (mask : NonzeroFrequency→ℂ) (x w z : ℂ) (p : FullHighIndex) : ℂ :=
  mask p.1*frequencyWeight z p.1*
    markedIdealHighSummand S D η p.1.val x w z p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2

lemma fullHighCoefficient_norm_le (S : Finset (Ideal O)) (D : Ideal O) (η : AngularCharacter)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1) (x w z : ℂ)
    (σ υ ξ : ℝ) (hx : x.re=σ) (hw : w.re=υ) (hz : z.re=ξ) (p : FullHighIndex) :
    ‖fullHighCoefficient S D η mask x w z p‖≤ initialHighMajorant σ υ ξ p := by
  unfold fullHighCoefficient
  rw [norm_mul,norm_mul]
  have hb := (markedIdealHighSummand_norm_le S D η p.1.val x w z p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2).trans
    (bareIdealHighSummand_norm_le η p.1.val x w z p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2)
  calc
    _ ≤ (1*‖frequencyWeight z p.1‖)*highAbsoluteMajorant x w z p.2 :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hm _) (norm_nonneg _)) hb (norm_nonneg _) (by positivity)
    _ = initialHighMajorant σ υ ξ p := by
      rw [one_mul,frequencyWeight_norm_eq_of_re z (ξ:ℂ) hz,
        highAbsoluteMajorant_eq_of_re x w z (σ:ℂ) (υ:ℂ) (ξ:ℂ) hx hw hz]
      rfl

lemma fullHighCoefficient_continuous (S : Finset (Ideal O)) (D : Ideal O) (η : AngularCharacter)
    (mask : NonzeroFrequency→ℂ) (p : FullHighIndex) :
    Continuous (fun q : (ℂ × ℂ) × ℂ => fullHighCoefficient S D η mask q.1.1 q.1.2 q.2 p) := by
  have hH : (elementNorm p.1.val:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (elementNorm_pos _ p.1.property).ne'
  unfold fullHighCoefficient frequencyWeight markedIdealHighSummand bareIdealHighSummand
  have hc : Continuous (fun q : (ℂ × ℂ) × ℂ => (elementNorm p.1.val:ℂ)^(-q.2)) :=
    continuous_snd.neg.const_cpow (Or.inl hH)
  have h1 : Continuous (fun q : (ℂ × ℂ) × ℂ => fullIdealWeight (q.1.1+1/2) p.2.1.1) :=
    (ProbeRow.fullIdealWeight_continuous _).comp (by fun_prop)
  have h2 : Continuous (fun q : (ℂ × ℂ) × ℂ => fullIdealWeight (1+3*q.1.1) p.2.1.2) :=
    (ProbeRow.fullIdealWeight_continuous _).comp (by fun_prop)
  have h3 : Continuous (fun q : (ℂ × ℂ) × ℂ => fullIdealWeight q.1.2 p.2.2.1) :=
    (ProbeRow.fullIdealWeight_continuous _).comp (by fun_prop)
  have h4 : Continuous (fun q : (ℂ × ℂ) × ℂ => fullIdealWeight (6*q.2) p.2.2.2) :=
    (ProbeRow.fullIdealWeight_continuous _).comp (by fun_prop)
  exact (continuous_const.mul hc).mul
    (continuous_const.mul ((((continuous_const.mul h1).mul h2).mul h3).mul h4))


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.fullHighCoefficient_norm_le

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.fullHighCoefficient_continuous
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.fullHighCoefficient_continuous
