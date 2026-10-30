import AngularPhysicalAllocatedRayGeometry
import AngularPhysicalAnchoredInput

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows.AllocatedRayDictionary
open CommonRows RelativePrime InductionEnergy
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation
open CenteredMomentRetainedProfile HeckePrimeAnnular
open CenteredMomentCommonMaskEnergy (heightCoefficient)
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentAllocatedNaturalSource (Plain rawScale rawScale_pos)
local notation "O" => ActualEisensteinCubic.O
variable {α:Type*} [Fintype α] [DecidableEq α]

variable (M:Ideal O) [NeZero M]
local instance angularAllocatedRayMatchFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
structure Matches (s : Input α) (η₀ : AngularCharacter)
    (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ)
    (W : ℝ → ℂ) (bslot Z : ℝ) : Prop where
  parent_type : s.η.k=η₀.k
  character : ∀ i I, s.ν i I = (rayRelativeCharacter M H hH η₀ (θ i)).idealHom I
  profile : ∀ i y, s.W i y = W y * (y : ℂ)^(-HeckeDyadic.shift (σ i) (freq i))
  pool : ∀ i, s.slots i = primePool M H bslot (Z^(w i))
  scale : ∀ i, s.P i = Z^(w i)


variable {M H hH}
variable {s:Input α} {η₀:AngularCharacter} {θ:α→RayQuotient.Characters M H}
  {w σ freq:α→ℝ} {W:ℝ→ℂ} {bslot Z:ℝ}
  (h:Matches M H hH s η₀ θ w σ freq W bslot Z)
include h
omit [DecidableEq α] in
lemma common_coefficient (τ : AngularCharacter) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (i : CenteredMomentCommonProfile.liveIndices B.val)
    (I : Ideal O) :
    (commonData (withHeight s τ v) C R B).coefficient i I =
      (rayRelativeCharacter M H hH η₀ (θ i.val)).idealHom I *
        annularWeight W (Z^(w i.val)) (σ i.val) (freq i.val) I := by
  change s.ν i.val I * s.W i.val ((I.absNorm : ℝ) / s.P i.val) = _
  rw [h.character, h.profile, h.scale]
  rfl

omit [DecidableEq α] in
lemma common_height_coefficient (τ : AngularCharacter) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (i : CenteredMomentCommonProfile.liveIndices B.val)
    (I : Ideal O) (hI : I ≠ 0) :
    heightCoefficient ((commonData (withHeight s τ v) C R B).coefficient i) v I =
      ((Z^(w i.val) : ℝ) : ℂ)^(Complex.I*v) *
        ((rayRelativeCharacter M H hH η₀ (θ i.val)).idealHom I *
          annularWeight W (Z^(w i.val)) (σ i.val) (v+freq i.val) I) := by
  have he : (commonData (withHeight s τ v) C R B).coefficient i =
      fun I => (rayRelativeCharacter M H hH η₀ (θ i.val)).idealHom I *
        annularWeight W (Z^(w i.val)) (σ i.val) (freq i.val) I :=
    funext (common_coefficient h τ v C R B i)
  rw [he]
  exact CenteredMomentEnergySlotHeight.height_coefficient _ W _ _ _ v
    (h.scale i.val ▸ s.P_pos i.val) I hI

omit [DecidableEq α] in
lemma scale_phase_norm (i : α) (v : ℝ) :
    ‖((Z^(w i) : ℝ) : ℂ)^(Complex.I*v)‖ = 1 := by
  simpa using Complex.norm_cpow_eq_rpow_re_of_pos (h.scale i ▸ s.P_pos i) (Complex.I*v)


theorem matches_carries : FixedAnchor.Carries M H hH η₀ θ s :=
  ⟨h.parent_type,h.character⟩

end OAI.SevenEighths.Angular.PlainRows.AllocatedRayDictionary

#print axioms OAI.SevenEighths.Angular.PlainRows.AllocatedRayDictionary.common_coefficient
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AllocatedRayDictionary.common_coefficient

#print axioms OAI.SevenEighths.Angular.PlainRows.AllocatedRayDictionary.common_height_coefficient
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AllocatedRayDictionary.common_height_coefficient

#print axioms OAI.SevenEighths.Angular.PlainRows.AllocatedRayDictionary.scale_phase_norm
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AllocatedRayDictionary.scale_phase_norm

#print axioms OAI.SevenEighths.Angular.PlainRows.AllocatedRayDictionary.matches_carries
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AllocatedRayDictionary.matches_carries
