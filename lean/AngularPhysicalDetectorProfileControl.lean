import AngularPhysicalVolumeHeight
import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceDetectorProfile

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
namespace OAI.SevenEighths.Angular.DetectorSource
open TwistedVolume PrimaryVolume PlainRows AnnularSchwartz PlaneVolume
open CenteredMomentLattice CenteredMomentMask CenteredMomentTwist
open CenteredMomentHeight
open EisensteinSchwartzPoisson IdealMobiusDivisorSum ConcretePrimeRowBridge
open CenteredMomentNaturalFixedRaySource CenteredMomentDetectorDictionary
open CenteredMomentHeckeVolume (fixedPeriod fixedPeriod_ne_zero)
local notation "O" => ActualEisensteinCubic.O

theorem detector_volumeControl_uniform (angularType : ℤ) (ε B : ℝ)
    (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z → ∀χ : AngularCharacter,
      (χ.modulus.absNorm:ℝ)≤Z^B → ∀reverse : Bool,∀n : ℕ,n≤2 →
      ∀σ∈Set.Icc (0:ℝ) 1,∀t h : ℝ,
      volumeControl angularType Q χ (1/4) (9/4) (by norm_num)
        (detectorNormProfile reverse n σ t h)≤C*Z^ε*(1+‖t‖+‖h‖)^J := by
  obtain ⟨S,F,hF,hfourier⟩ := annular_fourier_control angularType (1/4) (9/4) (by norm_num)
  obtain ⟨J,A,hA,hprofile⟩ := detectorNormProfile_uniform S
  obtain ⟨D,hD,hdiv⟩ := polynomial_mask_divisor_bound ε B hε hB
  refine ⟨J,?_⟩
  intro Q
  let mass : ℝ := Nat.card (O⧸Ideal.span {fixedPeriod Q})
  have hmass : 0≤mass := Nat.cast_nonneg _
  have he := nonzeroLatticeEnvelopeConstant_nonneg
  let K : ℝ := D*mass*nonzeroLatticeEnvelopeConstant*F*A
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨1+K,by linarith,?_⟩
  intro Z hZ χ hχ reverse n hn σ hσ t h
  have hf : fourierControl (annularCLM angularType (1/4) (9/4) (by norm_num)
      (detectorNormProfile reverse n σ t h)) ≤ F*(A*(1+‖t‖+‖h‖)^J) :=
    (hfourier _).trans (mul_le_mul_of_nonneg_left (hprofile reverse n hn σ hσ t h) hF.le)
  have herr : volumeControl angularType Q χ (1/4) (9/4) (by norm_num)
      (detectorNormProfile reverse n σ t h) ≤
      (D*Z^ε)*(mass*(nonzeroLatticeEnvelopeConstant*(F*(A*(1+‖t‖+‖h‖)^J)))) := by
    unfold volumeControl
    rw [mul_assoc]
    apply mul_le_mul (hdiv Z hZ χ.modulus χ.modulus_ne_bot hχ)
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf he) hmass)
    · exact mul_nonneg hmass (mul_nonneg he (fourierControl_nonneg _))
    · exact mul_nonneg hD.le (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  calc
    _≤(D*Z^ε)*(mass*(nonzeroLatticeEnvelopeConstant*(F*(A*(1+‖t‖+‖h‖)^J)))) := herr
    _=K*Z^ε*(1+‖t‖+‖h‖)^J := by dsimp [K];ring
    _≤(1+K)*Z^ε*(1+‖t‖+‖h‖)^J := by gcongr;linarith
end OAI.SevenEighths.Angular.DetectorSource

#print axioms OAI.SevenEighths.Angular.DetectorSource.detector_volumeControl_uniform
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.DetectorSource.detector_volumeControl_uniform
