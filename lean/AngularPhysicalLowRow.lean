import AngularPhysicalDetectorPhysicalProbe
import OAI.NumberTheory.DirichletL.Detector.LowRow

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section
open scoped Classical
namespace OAI.SevenEighths.Angular.PhysicalLow
open ProbeRow ProbeCompleted CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def physicalRowBase (η : AngularCharacter) (Xi : O→*ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) : O→*ℂ :=
  PhysicalDetectorProbe.targetMonoid η*conjugateMonoid Xi*reciprocityPhaseMonoid s hs

lemma physicalRowBase_norm (η : AngularCharacter) (Xi : O→*ℂ)
    (hXi : ∀a,‖Xi a‖≤1) (s : O) (hs : Supported (Ideal.span {s})) (a : O) :
    ‖physicalRowBase η Xi s hs a‖≤1 := by
  change ‖(PhysicalDetectorProbe.targetMonoid η a*star (Xi a))*sexticReciprocityPhase s a‖≤1
  rw [norm_mul,norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) ((mul_le_of_le_one_left (norm_nonneg _) (PhysicalDetectorProbe.targetMonoid_norm_le_one η a)).trans (hXi a))).trans (sexticReciprocityPhase_norm s a)

lemma ray_rowCoefficient_eq_rowTwist (η : AngularCharacter) (Xi : O→*ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m f z n : O) (hn : n=m^6*f^4*z)
    (χ : RayCharacter) :
    rayMonoid χ*PhysicalDetectorProbe.rowCoefficient η Xi s hs n=
      rowTwist (rayMonoid χ*physicalRowBase η Xi s hs) m f z := by
  subst n
  ext a
  change rayMonoid χ a*((PhysicalDetectorProbe.targetMonoid η a*star (Xi a))*sexticReciprocityPhase s a*
      idealRowHom (m^6*f^4*z) (Ideal.span {a}))=
    (rayMonoid χ a*((PhysicalDetectorProbe.targetMonoid η a*star (Xi a))*sexticReciprocityPhase s a))*
      idealRowHom (m^6*f^4*z) (Ideal.span {a})
  ring

theorem correctedPhysicalRow_eq_inverse_rows (η : AngularCharacter) (Xi : O→*ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m f z n : O) (hn : n=m^6*f^4*z)
    (S : Finset Id) (D : Id) (W : ℝ→ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0<X) :
    correctedCompletedT S D (PhysicalDetectorProbe.rowCoefficient η Xi s hs n) W X=
      ∑χ : RayCharacter,correctionCoeff χ*
        InverseMoment.markedCompletedT (rowTwist (rayMonoid χ*physicalRowBase η Xi s hs) m f z)
          W X (wholeIdealMask S D) := by
  rw [correctedCompletedT_ray_expansion S D _ W hW X hX]
  apply Finset.sum_congr rfl
  intro χ _
  rw [markedCompletedT_eq_inverse S D _ W hW X hX,ray_rowCoefficient_eq_rowTwist η Xi s hs m f z n hn χ]


end OAI.SevenEighths.Angular.PhysicalLow

#print axioms OAI.SevenEighths.Angular.PhysicalLow.physicalRowBase_norm

#print axioms OAI.SevenEighths.Angular.PhysicalLow.ray_rowCoefficient_eq_rowTwist

#print axioms OAI.SevenEighths.Angular.PhysicalLow.correctedPhysicalRow_eq_inverse_rows
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLow.correctedPhysicalRow_eq_inverse_rows
