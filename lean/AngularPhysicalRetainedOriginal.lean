import AngularPhysicalOriginalRetainedReflection
import AngularPhysicalReflectedTruncation
import AngularPhysicalDeletedReflectedTail
import AngularPhysicalAnnularTwistedSource

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.OriginalReflectionApproximation
open CenteredMomentReflectionDeletion (DecayTwo SmoothIdeal norm norm_pos)
open CenteredMomentRetainedReflection (masked_decayTwo)
open CenteredMomentReflectionTailMass (dual_scale_bounds)
open CenteredMomentSectorLocalization CenteredMomentNaturalPrimitive
open ReflectionMass AnnularFourier NaturalReflection RetainedReflection ReflectedSeries
open CenteredMomentReflectedTruncation (retainedAnnuli)
open CenteredMomentReflectedAnnuli (annularProfile)
local notation "O" => ActualEisensteinCubic.O

def finiteAnnularColumn (η : AngularCharacter) (F : ℝ→ℂ) (R Y : ℝ) : ℂ :=
  if hY : 0<Y then ∑n∈retainedAnnuli R Y hY,(Real.sqrt (dyadicScale n):ℂ)*
    Dyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 else 0

lemma finiteAnnularColumn_eq (η : AngularCharacter) (F : ℝ→ℂ) (hF : DecayTwo F)
    (R Y : ℝ) (hY : 0<Y) : finiteAnnularColumn η F R Y=
      Dyadic.polynomial η false (fun x=>(retainedWeight R x:ℂ)*F x) Y 0 0 := by
  rw [finiteAnnularColumn,dite_eq_left hY]
  exact (retained_finite_series η F hF R Y hY).symm

def retainedOriginal (χ ψ:AngularCharacter) (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hs:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W) (X R t:ℝ) : ℂ :=
  let S := redundantSet χ.modulus ψ.modulus
  ∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient ψ ψ.conjugate S D H*
    finiteAnnularColumn χ.conjugate
      (profile ψ.k a b ha (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t)) R
      ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val))

lemma radical_le_original (χ ψ : AngularCharacter)
    (hcap : ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm) :
    (Ideal.absNorm (redundantIdeal χ.modulus ψ.modulus):ℝ)≤(χ.modulus.absNorm:ℝ) := by
  have hp : 1≤ψ.modulus.absNorm := Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  exact_mod_cast (show (redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm by
    nlinarith)


end OAI.SevenEighths.Angular.OriginalReflectionApproximation

#print axioms OAI.SevenEighths.Angular.OriginalReflectionApproximation.finiteAnnularColumn_eq
#print axioms OAI.SevenEighths.Angular.OriginalReflectionApproximation.radical_le_original
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.OriginalReflectionApproximation.radical_le_original
