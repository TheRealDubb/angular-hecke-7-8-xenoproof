import AngularPhysicalLowRows
import OAI.NumberTheory.DirichletL.Detector.LowRay

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

lemma rowCoefficient_congr_ray (η : AngularCharacter) (Xi : O→*ℂ)
    (s r : PhysicalRayElement) (h : physicalRay s.val=physicalRay r.val) (m : O) :
    PhysicalDetectorProbe.rowCoefficient η Xi s.val s.property m=PhysicalDetectorProbe.rowCoefficient η Xi r.val r.property m := by
  apply MonoidHom.ext
  intro n
  rw [PhysicalDetectorProbe.rowCoefficient_apply,PhysicalDetectorProbe.rowCoefficient_apply]
  have hd : (4:O)∣s.val-r.val := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  have he : sexticReciprocityPhase s.val n=sexticReciprocityPhase r.val n := by
    unfold sexticReciprocityPhase
    rw [QuadraticGaussRay.residue_eq_of_four_dvd_sub s.val r.val hd]
  rw [he]

def physicalRayRowMonoid (η : AngularCharacter) (C : CalibrationData)
    (σ : RayRing) (m : O) : O→*ℂ :=
  PhysicalDetectorProbe.rowCoefficient η C.Xi (physicalRayRepresentative σ).val (physicalRayRepresentative σ).property m

lemma physicalRowMonoid_eq_ray (η : AngularCharacter) (C : CalibrationData) (r : PhysicalRowIndex) :
    physicalRowMonoid η C r=physicalRayRowMonoid η C (physicalIdealRay r.1) r.2 := by
  let s : PhysicalRayElement :=
    ⟨primaryGenerator r.1.val,(supported_span_primaryGenerator_iff r.1.val).mpr r.1.property⟩
  exact rowCoefficient_congr_ray η C.Xi s (physicalRayRepresentative (physicalRay s.val))
    (physicalRayRepresentative_spec s).symm r.2

lemma physicalRayRowMonoid_norm (η : AngularCharacter) (C : CalibrationData)
    (σ : RayRing) (m n : O) : ‖physicalRayRowMonoid η C σ m n‖≤1 :=
  PhysicalDetectorProbe.rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one _ _ m n

def physicalRayFiniteBase (η : AngularCharacter) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (χ : RayCharacter) : O→*ℂ :=
  finiteLowBase η (calibrationForSet S hS) (calibrationForSet S hS).generator
    (calibrationLowData S hS) (physicalRayRepresentative σ).val
      (physicalRayRepresentative σ).property χ

theorem physicalRayFiniteBase_uniform (η : AngularCharacter) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) :
    ∃L : Id,L≠0 ∧ ∀σ : RayRing,∀χ : RayCharacter,
      FactorsModulo L (physicalRayFiniteBase η S hS σ χ) ∧
      ∀n : O,‖physicalRayFiniteBase η S hS σ χ n‖≤1 := by
  refine ⟨lowBaseModulus η (calibrationForSet S hS) (calibrationForSet S hS).generator (calibrationLowData S hS),
    lowBaseModulus_ne_zero η _ _ (calibrationForSet S hS).generator_ne_zero _,?_⟩
  intro σ χ
  exact ⟨finiteLowBase_periodic η _ _ _ _ _ χ,finiteLowBase_norm η _ _ _ _ _ χ⟩

def physicalRayAngularBase (η : AngularCharacter) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (χ : RayCharacter) : O→*ℂ :=
  lowAngularBase η (calibrationForSet S hS) (calibrationForSet S hS).generator
    (calibrationLowData S hS) (physicalRayRepresentative σ).val
      (physicalRayRepresentative σ).property χ

theorem physicalRayRow_eq_angular_inverse (η : AngularCharacter)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (σ : RayRing) (m : O) (D : Id) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (T : ℝ) (hT : 0<T) :
    correctedCompletedT S D (physicalRayRowMonoid η (calibrationForSet S hS) σ m) W T=
      ∑χ : RayCharacter,correctionCoeff χ*
        InverseMoment.markedCompletedT
          (rowTwist (physicalRayAngularBase η S hS σ χ) (calibrationForSet S hS).generator 1 m)
          W T (fun A=>if D∣A then (1:ℂ) else 0) :=
  correctedPhysicalRow_eq_angular_inverse η S hS hbad
    (physicalRayRepresentative σ).val (physicalRayRepresentative σ).property m D W hW T hT
      (calibrationLowData S hS)


theorem physicalRayAngularBase_eq_twist (η : AngularCharacter) (order : ℕ)
    (hk : η.k= -(order:ℤ)) (horder : 0<order) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (χ : RayCharacter) :
    physicalRayAngularBase η S hS σ χ=
      CubicEisenstein.AngularCanonicalCoefficient.negativeAngularTwist (physicalRayFiniteBase η S hS σ χ) order :=
  lowAngularBase_eq_negative_twist η order hk horder _ _ _ _ _ χ

end OAI.SevenEighths.Angular.PhysicalLow

#print axioms OAI.SevenEighths.Angular.PhysicalLow.rowCoefficient_congr_ray

#print axioms OAI.SevenEighths.Angular.PhysicalLow.physicalRowMonoid_eq_ray

#print axioms OAI.SevenEighths.Angular.PhysicalLow.physicalRayRowMonoid_norm

#print axioms OAI.SevenEighths.Angular.PhysicalLow.physicalRayFiniteBase_uniform

#print axioms OAI.SevenEighths.Angular.PhysicalLow.physicalRayRow_eq_angular_inverse

#print axioms OAI.SevenEighths.Angular.PhysicalLow.physicalRayAngularBase_eq_twist
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLow.physicalRayAngularBase_eq_twist
