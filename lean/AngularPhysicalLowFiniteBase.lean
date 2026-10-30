import AngularPhysicalLowRow
import AngularIdealFactor
import OAI.NumberTheory.DirichletL.Detector.LowPeriod

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section
open scoped Classical
namespace OAI.SevenEighths.Angular.PhysicalLow
open ProbeRow CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic CanonicalCoefficientClass ProbePhysical
open CubicEisenstein CubicEisenstein.AngularCompletedCoefficient CubicEisenstein.AngularCanonicalCoefficient
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def finiteLowBase (η : AngularCharacter) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s}))
    (χ : RayCharacter) : O→*ℂ :=
  rayMonoid χ*finiteResidueHom η*conjugateMonoid (periodicCalibrationXi C B D)*reciprocityPhaseMonoid s hs

def lowBaseModulus (η : AngularCharacter) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) : Id :=
  η.modulus*(Ideal.span {C.generator}*calibrationRowModulus C B D)*Ideal.span {(4:O)}

lemma lowBaseModulus_ne_zero (η : AngularCharacter) (C : CalibrationData) (B : O) (hB : B≠0)
    (D : GoodMaskRowData B 1 C.generator) : lowBaseModulus η C B D≠0 := by
  unfold lowBaseModulus
  apply mul_ne_zero
  · exact mul_ne_zero η.modulus_ne_bot (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero)
      (calibrationRowModulus_ne_zero C B hB D))
  · apply Ideal.span_singleton_eq_bot.not.mpr
    norm_num

lemma finiteLowBase_periodic (η : AngularCharacter) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s})) (χ : RayCharacter) :
    FactorsModulo (lowBaseModulus η C B D) (finiteLowBase η C B D s hs χ) := by
  intro x y hxy
  have h4 : (4:O)∣x-y := Ideal.mem_span_singleton.mp (Ideal.mul_le_right hxy)
  have hη : finiteResidueHom η x=finiteResidueHom η y := by
    apply congrArg η.residue
    exact Ideal.Quotient.eq.mpr (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have hc := periodicCalibrationXi_periodic C B D x y (Ideal.mul_le_right (Ideal.mul_le_left hxy))
  change ((rayMonoid χ x*finiteResidueHom η x)*star (periodicCalibrationXi C B D x))*
      sexticReciprocityPhase s x=
    ((rayMonoid χ y*finiteResidueHom η y)*star (periodicCalibrationXi C B D y))*sexticReciprocityPhase s y
  rw [hη,hc,sexticReciprocityPhase_congr_right s x y h4]
  have hr : rayMonoid χ x=rayMonoid χ y := rayCharacter_eq_of_mod_four χ x y h4
  rw [hr]

lemma finiteLowBase_norm (η : AngularCharacter) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s}))
    (χ : RayCharacter) (a : O) : ‖finiteLowBase η C B D s hs χ a‖≤1 := by
  have hr : ‖rayMonoid χ a‖≤1 := FiniteRayExpansion.norm_char_le_one χ _
  change ‖((rayMonoid χ a*finiteResidueHom η a)*star (periodicCalibrationXi C B D a))*sexticReciprocityPhase s a‖≤1
  simp only [norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) ((mul_le_of_le_one_left (norm_nonneg _) ((mul_le_of_le_one_left (norm_nonneg _) hr).trans (finiteResidueHom_norm_le_one η a))).trans (periodicCalibrationXi_norm C B D a))).trans (sexticReciprocityPhase_norm s a)


def lowAngularBase (η : AngularCharacter) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s}))
    (χ : RayCharacter) : O→*ℂ :=
  rayMonoid χ*PhysicalDetectorProbe.targetMonoid η*conjugateMonoid (periodicCalibrationXi C B D)*reciprocityPhaseMonoid s hs

/-- Only finiteLowBase is periodic. The full base keeps the actual angular
factor, including its natural zero at the origin for positive order. -/
theorem lowAngularBase_eq_negative_twist (η : AngularCharacter) (order : ℕ)
    (hk : η.k= -(order:ℤ)) (horder : 0<order) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s}))
    (χ : RayCharacter) :
    lowAngularBase η C B D s hs χ=negativeAngularTwist (finiteLowBase η C B D s hs χ) order := by
  have he : PhysicalDetectorProbe.targetMonoid η=negativeAngularTwist (finiteResidueHom η) order :=
    AngularIdealFactor.actual_negative_element η order hk (Or.inl (Nat.ne_of_gt horder))
  unfold lowAngularBase finiteLowBase
  rw [he]
  ext n
  change (rayMonoid χ n*(star (alpha n)^order*finiteResidueHom η n)*
      star (periodicCalibrationXi C B D n))*sexticReciprocityPhase s n=
    star (alpha n)^order*((rayMonoid χ n*finiteResidueHom η n)*
      star (periodicCalibrationXi C B D n)*sexticReciprocityPhase s n)
  ring

lemma lowAngularBase_eq_primary (η : AngularCharacter) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (s : O) (hs : Supported (Ideal.span {s})) (χ : RayCharacter)
    (n : O) (hn : Supported (Ideal.span {n})) (hpn : λ₀^2∣n-1) (hc : IsCoprime B n) :
    lowAngularBase η C B D s hs χ n=(rayMonoid χ*physicalRowBase η C.Xi s hs) n := by
  change ((rayMonoid χ n*PhysicalDetectorProbe.targetMonoid η n)*star (periodicCalibrationXi C B D n))*sexticReciprocityPhase s n=
    rayMonoid χ n*((PhysicalDetectorProbe.targetMonoid η n*star (C.Xi n))*sexticReciprocityPhase s n)
  rw [periodicCalibrationXi_eq_primary C B D hBL hB2 n hn hpn hc]
  ring

end OAI.SevenEighths.Angular.PhysicalLow

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowBaseModulus_ne_zero

#print axioms OAI.SevenEighths.Angular.PhysicalLow.finiteLowBase_periodic

#print axioms OAI.SevenEighths.Angular.PhysicalLow.finiteLowBase_norm

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowAngularBase_eq_negative_twist

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowAngularBase_eq_primary
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLow.lowAngularBase_eq_primary
