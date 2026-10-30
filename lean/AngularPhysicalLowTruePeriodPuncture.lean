import OAI.NumberTheory.DirichletL.Detector.LowTruePeriodPuncture
import AngularPhysicalLowPeriodFilter

namespace OAI

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section
open scoped Classical
namespace SevenEighths.Angular.PhysicalLow
open ProbePhysical
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss RayFourExpansion SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma physicalRayAngularBase_support (η : AngularCharacter) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (σ : RayRing) (χ : RayCharacter)
    (n : O) (hn : physicalRayAngularBase η S hS σ χ n≠0) :
    IsCoprime (Ideal.span {n}) (lowPeriodIdeal η S hS) := by
  let C := calibrationForSet S hS
  let D := calibrationLowData S hS
  change ((rayMonoid χ n*η.elementCoeff n)*
    star (C.residueMonoid n*CanonicalRowCompletion.actualPeriodicRow 1 C.generator
      D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported n))*
      _≠0 at hn
  have ha := left_ne_zero_of_mul hn
  have heta := right_ne_zero_of_mul (left_ne_zero_of_mul ha)
  have hres := left_ne_zero_of_mul (star_ne_zero.mp (right_ne_zero_of_mul ha))
  have hc : IsCoprime C.generator n := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    exact ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp
      (C.residue.apply_ne_zero_iff.mp hres)).symm
  exact lowBaseModulus_coprime η C D (calibration_generator_bad S hS hbad).1
    (calibration_generator_bad S hS hbad).2 n hc heta

def lowTruePeriodGenerator (η : AngularCharacter) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : O := ConcretePrimeRowBridge.idealGenerator (lowPeriodIdeal η S hS)

lemma lowPeriodIdeal_ne_zero (η : AngularCharacter) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowPeriodIdeal η S hS≠0 := by
  unfold lowPeriodIdeal
  apply mul_ne_zero
  · exact lowBaseModulus_ne_zero η _ _ (calibrationForSet S hS).generator_ne_zero _
  · apply Ideal.span_singleton_eq_bot.not.mpr
    norm_num

lemma lowTruePeriodGenerator_ne_zero (η : AngularCharacter) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowTruePeriodGenerator η S hS≠0 :=
  ConcretePrimeRowBridge.idealGenerator_ne_zero _ (lowPeriodIdeal_ne_zero η S hS)

lemma lowTruePeriodGenerator_span (η : AngularCharacter) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : Ideal.span {lowTruePeriodGenerator η S hS}=lowPeriodIdeal η S hS :=
  ConcretePrimeRowBridge.span_idealGenerator _

lemma physicalRayAngularBase_zero_true_puncture (η : AngularCharacter) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (σ : RayRing) (χ : RayCharacter)
    (n : O) (hn : ¬IsCoprime (lowTruePeriodGenerator η S hS) n) :
    physicalRayAngularBase η S hS σ χ n=0 := by
  by_contra hh
  apply hn
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [lowTruePeriodGenerator_span]
  exact (physicalRayAngularBase_support η S hS hbad σ χ n hh).symm

theorem physical_row_absorb_true_period (η : AngularCharacter) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (σ : RayRing) (χ : RayCharacter)
    (f z : O) :
    rowTwist (physicalRayAngularBase η S hS σ χ)
      ((calibrationForSet S hS).generator*lowTruePeriodGenerator η S hS) f z=
    rowTwist (physicalRayAngularBase η S hS σ χ) (calibrationForSet S hS).generator f z := by
  exact InverseReflectedPhase.rowTwist_absorb_puncture _ _ _ f z
    (calibration_generator_bad S hS hbad).1 (calibration_generator_bad S hS hbad).2
    (physicalRayAngularBase_zero_true_puncture η S hS hbad σ χ)

lemma physical_true_period_residual_coprime (η : AngularCharacter) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (I F : Id) :
    IsCoprime (lowPeriodIdeal η S hS)
      (rowResidualPart I
        (Ideal.span {(calibrationForSet S hS).generator*lowTruePeriodGenerator η S hS}*F)) := by
  apply InverseReflectedPhase.rowResidualPart_coprime_enlarged_period
  rw [lowTruePeriodGenerator_span]

def lowReflectionPeriod (η : AngularCharacter) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : Id :=
  lowBaseModulus η (calibrationForSet S hS) (calibrationForSet S hS).generator (calibrationLowData S hS)

lemma lowReflectionPeriod_ne_zero (η : AngularCharacter) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowReflectionPeriod η S hS≠0 :=
  lowBaseModulus_ne_zero η _ _ (calibrationForSet S hS).generator_ne_zero _

lemma lowReflectionPeriod_actual (η : AngularCharacter) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (χ : RayCharacter) :
    CanonicalCoefficientClass.FactorsModulo (lowReflectionPeriod η S hS) (physicalRayFiniteBase η S hS σ χ) ∧
      ∀n : O,‖physicalRayFiniteBase η S hS σ χ n‖≤1 := by
  exact ⟨finiteLowBase_periodic η _ _ _ _ _ χ,finiteLowBase_norm η _ _ _ _ _ χ⟩

def lowReflectionMask (η : AngularCharacter) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : O :=
  (calibrationForSet S hS).generator*lowTruePeriodGenerator η S hS

lemma lowReflectionMask_ne_zero (η : AngularCharacter) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowReflectionMask η S hS≠0 :=
  mul_ne_zero (calibrationForSet S hS).generator_ne_zero (lowTruePeriodGenerator_ne_zero η S hS)

lemma lowReflectionMask_bad (η : AngularCharacter) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) :
    ConcretePrimeRowBridge.goodLambda∣lowReflectionMask η S hS ∧ (2:O)∣lowReflectionMask η S hS := by
  exact ⟨dvd_mul_of_dvd_left (calibration_generator_bad S hS hbad).1 _,
    dvd_mul_of_dvd_left (calibration_generator_bad S hS hbad).2 _⟩

lemma lowReflectionMask_period (η : AngularCharacter) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowPeriodIdeal η S hS∣Ideal.span {lowReflectionMask η S hS} := by
  rw [lowReflectionMask,←Ideal.span_singleton_mul_span_singleton,lowTruePeriodGenerator_span]
  exact dvd_mul_left _ _

lemma physical_markedCompletedT_absorb_true_period (η : AngularCharacter) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (σ : RayRing) (χ : RayCharacter)
    (f z : O) (W : ℝ→ℂ) (X : ℝ) (mark : Id→ℂ) :
    InverseMoment.markedCompletedT
      (rowTwist (physicalRayAngularBase η S hS σ χ) (lowReflectionMask η S hS) f z) W X mark=
    InverseMoment.markedCompletedT
      (rowTwist (physicalRayAngularBase η S hS σ χ) (calibrationForSet S hS).generator f z) W X mark := by
  rw [lowReflectionMask,physical_row_absorb_true_period η S hS hbad σ χ]

end SevenEighths.Angular.PhysicalLow
end

end OAI

#print axioms OAI.SevenEighths.Angular.PhysicalLow.physicalRayAngularBase_support

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowPeriodIdeal_ne_zero

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowTruePeriodGenerator_ne_zero

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowTruePeriodGenerator_span

#print axioms OAI.SevenEighths.Angular.PhysicalLow.physicalRayAngularBase_zero_true_puncture

#print axioms OAI.SevenEighths.Angular.PhysicalLow.physical_row_absorb_true_period

#print axioms OAI.SevenEighths.Angular.PhysicalLow.physical_true_period_residual_coprime

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowReflectionPeriod_ne_zero

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowReflectionPeriod_actual

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowReflectionMask_ne_zero

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowReflectionMask_bad

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowReflectionMask_period

#print axioms OAI.SevenEighths.Angular.PhysicalLow.physical_markedCompletedT_absorb_true_period
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLow.physical_markedCompletedT_absorb_true_period
