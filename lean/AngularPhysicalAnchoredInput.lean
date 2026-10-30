import AngularPhysicalFixedRayAnchor
import AngularPhysicalPlainChildSource

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.PlainRows.FixedAnchor
open RelativePrime CommonRows ChildInputs
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentCommonProfile
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentFirstAmplificationChoice
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]
variable (M:Ideal O) [NeZero M]
local instance angularAnchoredInputFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
local instance angularAnchoredInputDecEq : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The actual coefficient equality is required on every ideal, including support zeros. -/
structure Carries (Ω:AngularCharacter) (θ:ι→RayQuotient.Characters M H)
    (s:Input ι) : Prop where
  parent_type : s.η.k=Ω.k
  slot_coeff : ∀i I,s.ν i I=(rayRelativeCharacter M H hH Ω (θ i)).idealHom I

variable {M H hH} {Ω:AngularCharacter} {θ:ι→RayQuotient.Characters M H} {s:Input ι}

theorem Carries.child (hs:Carries M H hH Ω θ s)
    (C R:Ideal O) (B:actualAllocations s.pools C) (τ:AngularCharacter) (t:ℝ)
    (hτ:τ.k=s.η.k) :
    Carries M H hH Ω (fun i:liveIndices B.val=>θ i.val) (ChildInputs.child s C R B τ t) := by
  refine ⟨hτ.trans hs.parent_type,?_⟩
  intro i I
  exact hs.slot_coeff i.val I

theorem Carries.slot_cancellation (hs:Carries M H hH Ω θ s) (i:ι) :
    s.η.k+(rayRelativeCharacter M H hH Ω (θ i)).k=0 :=
  ray_inverse_anchor_cancels_type M H hH Ω s.η hs.parent_type (θ i)

theorem Carries.literal_slot (hs:Carries M H hH Ω θ s) (i:ι) (I:Ideal O) :
    s.ν i I=star (Ω.idealHom I)*RayQuotient.idealCharacter M H hH (θ i) I :=
  (hs.slot_coeff i I).trans (rayRelativeCharacter_coeff M H hH Ω (θ i) I)

theorem Carries.original_profile (hs:Carries M H hH Ω θ s)
    (R seed:Ideal O) (v:Tuple ι) :
    (original s R seed).profile v=
      profileCoefficient R (fun i I=>(rayRelativeCharacter M H hH Ω (θ i)).idealHom I)
        s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v := by
  have he:s.ν=(fun i I=>(rayRelativeCharacter M H hH Ω (θ i)).idealHom I) :=
    funext (fun i=>funext (hs.slot_coeff i))
  change profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v=_
  rw [he]

theorem Carries.source_coefficient (hs:Carries M H hH Ω θ s) (R seed I:Ideal O) :
    CommonRows.coefficient s R seed I=
      finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R
          (fun i J=>(rayRelativeCharacter M H hH Ω (θ i)).idealHom J)
          s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) I := by
  have he:s.ν=(fun i J=>(rayRelativeCharacter M H hH Ω (θ i)).idealHom J) :=
    funext (fun i=>funext (hs.slot_coeff i))
  unfold CommonRows.coefficient
  rw [he]

theorem Carries.child_source_coefficient (hs:Carries M H hH Ω θ s)
    (C R seed:Ideal O) (B:actualAllocations s.pools C) (τ:AngularCharacter) (t:ℝ)
    (hτ:τ.k=s.η.k) (I:Ideal O) :
    let u:=ChildInputs.child s C R B τ t
    (original u (R*C) seed).beta I=
      finiteColumnCoefficient (Fintype.piFinset u.pools)
        (profileCoefficient (R*C)
          (fun (i:liveIndices B.val) J=>(rayRelativeCharacter M H hH Ω (θ i.val)).idealHom J)
          u.W u.P u.W₁ u.W₂ u.X₁ u.X₂ u.Y₁ u.Y₂ 1 1 seed) I := by
  exact (hs.child C R B τ t hτ).source_coefficient (R*C) seed I

end OAI.SevenEighths.Angular.PlainRows.FixedAnchor

#print axioms OAI.SevenEighths.Angular.PlainRows.FixedAnchor.Carries.child
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FixedAnchor.Carries.child

#print axioms OAI.SevenEighths.Angular.PlainRows.FixedAnchor.Carries.slot_cancellation
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FixedAnchor.Carries.slot_cancellation

#print axioms OAI.SevenEighths.Angular.PlainRows.FixedAnchor.Carries.literal_slot
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FixedAnchor.Carries.literal_slot

#print axioms OAI.SevenEighths.Angular.PlainRows.FixedAnchor.Carries.original_profile
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FixedAnchor.Carries.original_profile

#print axioms OAI.SevenEighths.Angular.PlainRows.FixedAnchor.Carries.source_coefficient
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FixedAnchor.Carries.source_coefficient

#print axioms OAI.SevenEighths.Angular.PlainRows.FixedAnchor.Carries.child_source_coefficient
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FixedAnchor.Carries.child_source_coefficient
