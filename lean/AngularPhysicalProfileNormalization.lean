import AngularPhysicalProfileVolumeControl
import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalNormalize

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.FiniteProfileExceptional
open TwistedVolume PrimaryVolume PlainRows AnnularSchwartz PlaneVolume
open CenteredMomentLattice CenteredMomentMask CenteredMomentTwist CenteredMomentHeight
open EisensteinSchwartzPoisson IdealMobiusDivisorSum
open CenteredMomentFiniteProfileExceptional
open CenteredMomentHeckeVolume (fixedPeriod fixedPeriod_ne_zero)
local notation "O" => ActualEisensteinCubic.O

theorem twistedIdealSum_profile_smul (χ : AngularCharacter) (W : 𝓢(ℝ,ℂ))
    (c t X : ℝ) : twistedIdealSum χ (c • W : 𝓢(ℝ,ℂ)) t X = (c:ℂ)*twistedIdealSum χ W t X := by
  unfold twistedIdealSum
  rw [←tsum_mul_left]
  apply tsum_congr
  intro I
  change _ * ((c:ℂ) * W _) = (c:ℂ) * (_ * W _)
  ring

theorem twistedIdealSum_normalized (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S)
    (χ : AngularCharacter) (W : 𝓢(ℝ,ℂ)) (t X : ℝ) :
    twistedIdealSum χ W t X = (sourceControl S W:ℂ)*
      twistedIdealSum χ (normalizedProfile S W) t X := by
  rw [←twistedIdealSum_profile_smul,normalizedProfile_reconstruct S hS W]
end OAI.SevenEighths.Angular.FiniteProfileExceptional

#print axioms OAI.SevenEighths.Angular.FiniteProfileExceptional.twistedIdealSum_profile_smul
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FiniteProfileExceptional.twistedIdealSum_profile_smul

#print axioms OAI.SevenEighths.Angular.FiniteProfileExceptional.twistedIdealSum_normalized
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FiniteProfileExceptional.twistedIdealSum_normalized
