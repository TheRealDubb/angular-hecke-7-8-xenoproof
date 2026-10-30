import AngularPhysicalLowFiniteBase
import OAI.NumberTheory.DirichletL.Detector.LowPuncture

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section
open scoped Classical
namespace OAI.SevenEighths.Angular.PhysicalLow
open ProbeRow ProbeCompleted CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic CanonicalCoefficientClass ActualEisensteinCubic ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma lowAngularBase_zero_of_not_coprime (η : AngularCharacter) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s}))
    (χ : RayCharacter) (n : O) (hc : ¬IsCoprime B n) : lowAngularBase η C B D s hs χ n=0 := by
  have hm : coprimalityMask B n=(0:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=0;rw [ite_eq_right hc]
  change ((rayMonoid χ n*PhysicalDetectorProbe.targetMonoid η n)*star (C.residueMonoid n*
      ((((1:O→*ℂ) n*coprimalityMask B n)*
        numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported n)*
        movingNumeratorRow D.numeratorGood D.numeratorSupported n)))*sexticReciprocityPhase s n=0
  rw [hm]
  simp only [mul_zero,zero_mul,star_zero]

lemma lowAngularRow_eq_primary (η : AngularCharacter) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (s : O) (hs : Supported (Ideal.span {s})) (χ : RayCharacter) (z n : O) (hpn : λ₀^2∣n-1) :
    rowTwist (lowAngularBase η C B D s hs χ) B 1 z n=
      (coprimalityMask B*(rayMonoid χ*PhysicalDetectorProbe.rowCoefficient η C.Xi s hs z)) n := by
  by_cases hc : IsCoprime B n
  · have hn := supported_of_coprime_bad B n hBL hB2 hc
    have hm : coprimalityMask B n=(1:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=1;rw [ite_eq_left hc]
    rw [rowTwist_extract_sixth_mask _ _ _ _ _ hn,lowAngularBase_eq_primary η C B D hBL hB2 s hs χ n hn hpn hc]
    simp only [MonoidHom.mul_apply,hm,mul_one,one_pow,one_mul]
    change (rayMonoid χ n*((PhysicalDetectorProbe.targetMonoid η n*star (C.Xi n))*sexticReciprocityPhase s n))*
      idealRowHom z (Ideal.span {n})=rayMonoid χ n*
        (((PhysicalDetectorProbe.targetMonoid η n*star (C.Xi n))*sexticReciprocityPhase s n)*idealRowHom z (Ideal.span {n}))
    ring
  · have hm : coprimalityMask B n=(0:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=0;rw [ite_eq_right hc]
    change lowAngularBase η C B D s hs χ n*idealRowHom (B^6*1^4*z) (Ideal.span {n})=
      coprimalityMask B n*(rayMonoid χ n*PhysicalDetectorProbe.rowCoefficient η C.Xi s hs z n)
    rw [lowAngularBase_zero_of_not_coprime η C B D s hs χ n hc,hm,zero_mul,zero_mul]


end OAI.SevenEighths.Angular.PhysicalLow

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowAngularBase_zero_of_not_coprime

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowAngularRow_eq_primary
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLow.lowAngularRow_eq_primary
