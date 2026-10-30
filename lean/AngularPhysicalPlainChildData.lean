import AngularPhysicalOriginalSourceIdentity
import OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows.ChildInputs
open CommonRows CanonicalQuadraticSieve ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceRectangle CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform CenteredMomentRemainingBox
open CenteredMomentAmplificationAllocationCost CenteredMomentAmplificationAllocationScale
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationShortening
open CenteredMomentAmplificationLiveMask CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalChildEnergy CenteredMomentSecondHeightFamily
open CenteredMomentFirstSectors CenteredMomentRectangle CenteredMomentExtraction
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [instι:Fintype ι]
local instance angularPlainChildDataDecEq {κ:Type*} : DecidableEq κ := Classical.decEq _

def original (s : Input ι) (R seed : Ideal O) : OriginalData ι where
  S := s.pools
  R := R
  s := seed
  nu := s.ν
  slot := s.W
  lengths := s.P
  W₁ := s.W₁
  W₂ := s.W₂
  X₁ := s.X₁
  X₂ := s.X₂
  Y₁ := s.Y₁
  Y₂ := s.Y₂
  B₁ := 1
  B₂ := 1

theorem residual_ne (S : Finset (Ideal O)) (hS : ∀I∈S,I≠0)
    (B : Ideal O) (hB : B≠0) : ∀I∈residualPool B hB S,I≠0 := by
  intro I hI
  exact right_ne_zero_of_mul (hS (B*I) ((mem_residualPool B hB S I).mp hI))

theorem residual_one (S : Finset (Ideal O)) (h : (1:Ideal O)≠0) :
    residualPool 1 h S=S := by
  ext I
  simp only [mem_residualPool,one_mul]

theorem residual_coverage (S : Finset (Ideal O)) (W : ℝ→ℂ)
    (B : Ideal O) (hB : B≠0) (X Y : ℝ) (h : PlainCoverage S W 1 X Y) :
    PlainCoverage (residualPool B hB S) W 1 (X/B.absNorm) (Y/B.absNorm) := by
  have he := plainCoverage_residualPool S W 1 B hB X Y h
  intro I hi
  apply he I
  simpa only [one_mul,map_mul,map_one,Nat.cast_mul,Nat.cast_one,mul_one,div_div_eq_mul_div,mul_comm] using hi

def child (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : AngularCharacter) (t : ℝ) : Input (liveIndices B.val) where
  toData := {commonData s C R B with η:=τ,t:=t}
  plain₁ := residualPool (B.val (Sum.inr 0)) (alloc_ne s C B _) s.plain₁
  plain₂ := residualPool (B.val (Sum.inr 1)) (alloc_ne s C B _) s.plain₂
  plain₁_ne := residual_ne s.plain₁ s.plain₁_ne _ _
  plain₂_ne := residual_ne s.plain₂ s.plain₂_ne _ _
  coverage₁ := residual_coverage s.plain₁ s.W₁ _ _ _ _ s.coverage₁
  coverage₂ := residual_coverage s.plain₂ s.W₂ _ _ _ _ s.coverage₂
  ν_bound := fun i=>s.ν_bound i.val
  W_bound := fun i=>s.W_bound i.val
  lower := s.lower
  upper := s.upper
  lower_pos := s.lower_pos
  lower_le := fun i=>s.lower_le i.val
  upper_ge := fun i=>s.upper_ge i.val

@[simp] theorem child_modulus (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : AngularCharacter) (t : ℝ) : (child s C R B τ t).m=fixedBadMask*idealGenerator (R*C) := rfl

@[simp] theorem child_character (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : AngularCharacter) (t : ℝ) : (child s C R B τ t).η=τ := rfl

@[simp] theorem child_height (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : AngularCharacter) (t : ℝ) : (child s C R B τ t).t=t := rfl

theorem live_slot_one (B : Tuple ι) (i : liveIndices B) : B (Sum.inl i.val)=1 :=
  (Finset.mem_filter.mp i.property).2


theorem child_k (s:Input ι) (C R:Ideal O) (B:actualAllocations s.pools C)
    (τ:AngularCharacter) (t:ℝ) : (child s C R B τ t).η.k=τ.k := rfl

theorem child_order (s:Input ι) (C R:Ideal O) (B:actualAllocations s.pools C)
    (τ:AngularCharacter) (t:ℝ) (hτ:τ.k=s.η.k) :
    (child s C R B τ t).η.k.natAbs=s.η.k.natAbs := congrArg Int.natAbs hτ

end OAI.SevenEighths.Angular.PlainRows.ChildInputs

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildInputs.child_order
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildInputs.child_order
