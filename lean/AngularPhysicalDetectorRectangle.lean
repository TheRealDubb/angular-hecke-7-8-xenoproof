import AngularPhysicalDetectorProfileControl
import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceDetectorCancellation

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
theorem detector_rectangle_uniform (angularType : ℤ) (ε B : ℝ) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,Q≠0 → ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
      ∀η χ ψ : AngularCharacter,ψ.k=angularType → (χ.modulus.absNorm:ℝ)≤Z^B → Q≤ψ.modulus →
      PrimaryVolume.InducedBy χ ψ → ∀m A z : O,goodLambda∣m → (2:O)∣m →
      (∀n,χ.elementCoeff n=CanonicalRowCompletion.rowTwist η.elementHom.toMonoidHom m 1 (A*z) n) →
      ∀r₁ r₂ : Bool,∀j k : ℕ,j≤2 → k≤2 → ∀σ₁∈Set.Icc (0:ℝ) 1,∀σ₂∈Set.Icc (0:ℝ) 1,
      ∀t₁ t₂ h X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹*(
        twistedIdealSum χ (detectorSchwartz r₁ j σ₁ t₁) h X₁*twistedIdealSum χ (detectorSchwartz r₂ k σ₂ t₂) h X₂-
        twistedIdealSum χ (detectorSchwartz r₁ j σ₁ t₁) h Y₁*twistedIdealSum χ (detectorSchwartz r₂ k σ₂ t₂) h Y₂)‖≤
        C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J*(Real.sqrt T/L) := by
  obtain ⟨J,hJ⟩:=detector_volumeControl_uniform angularType ε B hε hB
  obtain ⟨A0,hA0,habs⟩:=detectorSchwartz_absolute
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hvolume⟩:=hJ Q
  refine ⟨4608*C*A0,by positivity,?_⟩
  intro Z hZ η χ ψ htype hχ hQψ hind m A z hml hm2 hrow r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
    t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  let E:=volumeControl angularType Q χ (1/4) (9/4) (by norm_num) (detectorNormProfile r₁ j σ₁ t₁ h)+
    volumeControl angularType Q χ (1/4) (9/4) (by norm_num) (detectorNormProfile r₂ k σ₂ t₂ h)
  let H:=1+‖t₁‖+‖t₂‖+‖h‖
  have hH : 0≤H:=by dsimp [H];positivity
  have hp₁ : (1+‖t₁‖+‖h‖)^J≤H^J := pow_le_pow_left₀ (by positivity) (by dsimp [H];linarith [abs_nonneg t₂]) J
  have hp₂ : (1+‖t₂‖+‖h‖)^J≤H^J := pow_le_pow_left₀ (by positivity) (by dsimp [H];linarith [abs_nonneg t₁]) J
  have hE : E≤2*C*Z^ε*H^J := by
    have h₁:=(hvolume Z hZ χ hχ r₁ j hj σ₁ hσ₁ t₁ h).trans
      (mul_le_mul_of_nonneg_left
        hp₁
        (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans hZ) _)))
    have h₂:=(hvolume Z hZ χ hχ r₂ k hk σ₂ hσ₂ t₂ h).trans
      (mul_le_mul_of_nonneg_left
        hp₂
        (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans hZ) _)))
    dsimp only [E]
    linarith
  have hraw:=actual_twisted_rectangle_saving η χ ψ Q hQ hQψ hind m A z hml hm2 hrow
    (detectorSchwartz r₁ j σ₁ t₁) (detectorSchwartz r₂ k σ₂ t₂)
    (1/4) (9/4) (1/4) (9/4) A0 A0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hA0.le hA0.le (detectorSchwartz_support _ _ _ _) (detectorSchwartz_support _ _ _ _)
    ((detectorSchwartz r₁ j σ₁ t₁).smooth ⊤) ((detectorSchwartz r₂ k σ₂ t₂).smooth ⊤)
    (habs r₁ j hj σ₁ hσ₁ t₁) (habs r₂ k hk σ₂ hσ₂ t₂)
    h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  rw [htype] at hraw
  have hT : 0<T:=hpX ▸ mul_pos (lt_of_lt_of_le hL hX₁) (lt_of_lt_of_le hL hX₂)
  have hn:=CenteredMoment.normalized_centered_saving _ T L (128*((9/4)*A0+(9/4)*A0)) E hT hraw
  have hr : 0≤Real.sqrt T/L:=div_nonneg (Real.sqrt_nonneg _) hL.le
  calc
    _≤4*E*(128*((9/4)*A0+(9/4)*A0))*(Real.sqrt T/L) := hn
    _≤4*(2*C*Z^ε*H^J)*(128*((9/4)*A0+(9/4)*A0))*(Real.sqrt T/L) := by
      gcongr
    _=_ := by dsimp [H];ring

end OAI.SevenEighths.Angular.DetectorSource

#print axioms OAI.SevenEighths.Angular.DetectorSource.detector_rectangle_uniform
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.DetectorSource.detector_rectangle_uniform
