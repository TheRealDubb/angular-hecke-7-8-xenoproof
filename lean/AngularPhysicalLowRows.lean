import AngularPhysicalLowCompletion
import OAI.NumberTheory.DirichletL.Detector.PhysicalRows

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

def physicalRowMonoid (η : AngularCharacter) (C : CalibrationData) (r : PhysicalRowIndex) : O→*ℂ :=
  PhysicalDetectorProbe.rowCoefficient η C.Xi (primaryGenerator r.1.val)
    ((supported_span_primaryGenerator_iff r.1.val).mpr r.1.property) r.2

lemma physicalRowMonoid_norm (η : AngularCharacter) (C : CalibrationData)
    (r : PhysicalRowIndex) (n : O) : ‖physicalRowMonoid η C r n‖≤1 :=
  PhysicalDetectorProbe.rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one _ _ r.2 n

theorem markedPhysicalProbe_eq_rows (η : AngularCharacter) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ→ℂ) (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) :
    PhysicalDetectorProbe.markedPhysicalProbe η C D W0 W1 X Y Z=
      ∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 X Y r*
        verticalIntegral 4 (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*spectralRow C.excluded D (physicalRowMonoid η C r) t) := by
  have hf := physicalRowWeight_mul_summable C W0 W1 hW0 hW1 X Y hX hY
    (fun r=>verticalIntegral 4 (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*spectralRow C.excluded D (physicalRowMonoid η C r) t))
  rw [hf.tsum_prod]
  unfold PhysicalDetectorProbe.markedPhysicalProbe
  rw [←tsum_mul_left]
  apply tsum_congr
  intro s
  by_cases hc : ∀P∈C.excluded,¬P∣s.val
  · simp only [physicalRowWeight,physicalRowMonoid]
    try dsimp only
    simp only [ite_eq_left hc]
    rw [←tsum_mul_left,←tsum_mul_left]
    apply tsum_congr
    intro m
    ring
  · simp only [physicalRowWeight]
    try dsimp only
    simp only [ite_eq_right hc,zero_mul,mul_zero,tsum_zero]

theorem markedPhysicalProbe_eq_gaussian_rows (η : AngularCharacter) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ→ℂ) (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    PhysicalDetectorProbe.markedPhysicalProbe η C D W0 W1 X Y Z=
      ∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 X Y r*
        correctedCompletedT C.excluded D (physicalRowMonoid η C r) gaussianCompletedProfile Z := by
  rw [markedPhysicalProbe_eq_rows η C D W0 W1 hW0 hW1 X Y Z hX hY]
  apply tsum_congr
  intro r
  rw [spectralRow_eq_gaussianCompleted _ _ _ (physicalRowMonoid_norm η C r) 4 (by norm_num) Z hZ]


end OAI.SevenEighths.Angular.PhysicalLow

#print axioms OAI.SevenEighths.Angular.PhysicalLow.physicalRowMonoid_norm

#print axioms OAI.SevenEighths.Angular.PhysicalLow.markedPhysicalProbe_eq_rows

#print axioms OAI.SevenEighths.Angular.PhysicalLow.markedPhysicalProbe_eq_gaussian_rows
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLow.markedPhysicalProbe_eq_gaussian_rows
