import AngularPhysicalDetectorInitialState
import AngularPhysicalPositiveNormalized
import AngularPhysicalCoefficientTransfer

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace OAI.SevenEighths.Angular.PhysicalDetectorInitial
open NaturalRows PlainRows CommonMask Dyadic RelativePrime
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentEnergyBands (length)
open CenteredMomentDetectorDictionary
open CenteredMomentDetectorEnergyInitialState (detectorProfiles)
open HeckeDetectorRowwisePolynomial (logProfile)
open HeckeDetectorDyadicProfiles (positiveAnnular)
local notation "O" => ActualEisensteinCubic.O

theorem natural_positive_zero {ι:Type*}[Fintype ι][DecidableEq ι]
    {η:AngularCharacter} {z:O} (F:NaturalRow η z)
    (W₁ W₂:ℝ→ℂ) (pool:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ)
    (P:ι→ℝ) (hP:∀i,0<P i) (X₁ X₂:ℝ) (hX₁:0<X₁) (hX₂:0<X₂):
    positiveSlotRow η CenteredMomentSecondHeightFamily.fixedBadMask 1 z
      W₁ W₂ pool β P 0 X₁ X₂=
    polynomial F.character false W₁ X₁ 0 0*polynomial F.character false W₂ X₂ 0 0*
      ∏i,naturalSlot F.character (pool i) (β i) (P i) := by
  have hplain (W:ℝ→ℂ) (X:ℝ):
      rowTwistedSum η CenteredMomentSecondHeightFamily.fixedBadMask 1 z W 0 X=
        twistedIdealSum F.character W 0 X :=
    rowTwistedSum_eq η F.character _ 1 z (by simpa only [one_mul] using F.element) W 0 X
  have hslot (i:ι):rowSlot η CenteredMomentSecondHeightFamily.fixedBadMask 1 z
      (pool i) (β i) 0=∑I∈pool i,F.character.idealHom I*β i I := by
    unfold rowSlot
    apply Finset.sum_congr rfl
    intro I hI
    rw [F.ideal]
    simp only [one_mul,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one]
    ring
  have hn:(Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹=
      (Real.sqrt X₁:ℂ)⁻¹*(Real.sqrt X₂:ℂ)⁻¹*∏i,(Real.sqrt (P i):ℂ)⁻¹ := by
    rw [Real.sqrt_mul (mul_pos hX₁ hX₂).le,Real.sqrt_mul hX₁.le,
      Real.sqrt_prod _ (fun i _=>(hP i).le),Complex.ofReal_mul,Complex.ofReal_mul,
      Complex.ofReal_prod,mul_inv_rev,mul_inv_rev,Finset.prod_inv_distrib]
    ring
  rw [PlainRows.plain_zero_height _ _ X₁ hX₁,PlainRows.plain_zero_height _ _ X₂ hX₂]
  simp only [positiveSlotRow,hplain,hslot,naturalSlot,Finset.prod_mul_distrib,hn]
  ring

theorem detector_profile_norm (χ:AngularCharacter) (reverse:Bool) (j:ℕ)
    (D σ t:ℝ) (hD:0<D):
    ‖polynomial (if reverse then χ.conjugate else χ) false
        ((logProfile^[j]) positiveAnnular) D σ t‖=
      ‖polynomial χ false (detectorSchwartz reverse j σ t) D 0 0‖ := by
  have hc:∀I:Ideal O,(if reverse then χ.conjugate else χ).idealHom I=
      if reverse then star (χ.idealHom I) else χ.idealHom I := by
    intro I
    cases reverse <;> simp [AngularCharacter.conjugate_idealHom]
  rw [CoefficientTransfer.norm_of_oriented_coefficients _ χ reverse hc false _ D σ t hD]
  have hp:(detectorSchwartz reverse j σ t:ℝ→ℂ)=
      HeckeInverseAmplification.twistProfile
        (HeckeDetectorCoefficientTransfer.orientedProfile reverse ((logProfile^[j]) positiveAnnular))
        σ (HeckeDetectorCoefficientTransfer.orientedFrequency reverse t) := by
    funext x
    exact detectorSchwartz_apply _ _ _ _ _
  rw [hp,InverseAmplification.polynomial_twistProfile]


end OAI.SevenEighths.Angular.PhysicalDetectorInitial

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorInitial.natural_positive_zero
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorInitial.natural_positive_zero

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorInitial.detector_profile_norm
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorInitial.detector_profile_norm
