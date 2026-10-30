import AngularPhysicalPlainChildGeometry

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
local instance angularPlainChildSourceDecEq {κ:Type*} : DecidableEq κ := Classical.decEq _

def originalChildEnergy (D : OriginalData ι) (τ : RayCharacter → AngularCharacter)
    (p : O) (n : ℕ) (t T K : ℝ) : ℝ :=
  let C := (Ideal.span {p})^(n+1)
  (16*(n+2:ℝ)*localErrorCost p n) *
    ((∑ χ : RayCharacter,∑ B : actualAllocations D.S C,
      (sourceGaussEnergy
        (finiteColumns (liveBox D.S B (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1))
        (finiteColumnCoefficient
          (liveBox D.S B (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1)
          (maskedLiveProfile B C D.R D.s D.nu D.slot D.lengths D.W₁ D.W₂
            D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂))
        (heightCoeff (τ χ) t) ballProfile K).re) /
      (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)))

theorem originalChildEnergy_nonneg (D : OriginalData ι) (τ : RayCharacter → AngularCharacter)
    (p : O) (n : ℕ) (t T K : ℝ) (hT : 0≤T) (hK : 0<K) :
    0≤originalChildEnergy D τ p n t T K := by
  apply mul_nonneg (mul_nonneg (by positivity) (localErrorCost_nonneg p n))
  apply div_nonneg _ (div_nonneg hT (by positivity))
  exact Finset.sum_nonneg (fun χ _ => Finset.sum_nonneg (fun B _ =>
    CenteredMomentGaussNormalization.sourceGaussEnergy_nonneg _ _ _ ballProfile K hK (fun _ => ballProfile_nonneg _)))

theorem child_columns (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : AngularCharacter) (t : ℝ) :
    finiteColumns (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)=
      (original (child s C R B τ t) (R*C) seed).columns ∧
    finiteColumnCoefficient
      (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)
      (maskedLiveProfile B C R seed s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1)=
      (original (child s C R B τ t) (R*C) seed).beta := by
  dsimp only [OriginalData.columns, OriginalData.beta, original]
  rw [child_tuplePool s C R B τ t,child_profile s C R seed B τ t]
  dsimp only [original]
  constructor
  · apply congrArg finiteColumns
    ext v
    simp only [Fintype.mem_piFinset]
  · apply congrArg (fun S => finiteColumnCoefficient S _)
    ext v
    simp only [Fintype.mem_piFinset]

theorem child_gauss_source (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : AngularCharacter) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy
      (finiteColumns (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1))
      (finiteColumnCoefficient
        (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)
        (maskedLiveProfile B C R seed s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1))
      (heightCoeff τ t) W K=
    sourceGaussEnergy (original (child s C R B τ t) (R*C) seed).columns
      (original (child s C R B τ t) (R*C) seed).beta
      (heightCoeff (child s C R B τ t).η (child s C R B τ t).t) W K := by
  obtain ⟨hcols,hcoeff⟩ := child_columns s C R seed B τ t
  rw [hcols,hcoeff]
  rfl

def normalizedGaussSource (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  (sourceGaussEnergy (original s R seed).columns (original s R seed).beta
    (heightCoeff s.η s.t) W K).re / volume s

def childNormalizedGaussSource (s : Input ι) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  normalizedGaussSource (child s C R B τ t) (R*C) seed W K

theorem original_childEnergy_eq_inputs (s : Input ι) (R seed : Ideal O)
    (τ : RayCharacter→AngularCharacter) (p : O) (hp : p≠0)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime (Ideal.span {p}) I)
    (n : ℕ) (t K : ℝ) :
    originalChildEnergy (original s R seed) τ p n t (volume s) K=
      (16*(n+2:ℝ)*localErrorCost p n)*
        ∑χ:RayCharacter,∑B:actualAllocations s.pools ((Ideal.span {p})^(n+1)),
          childNormalizedGaussSource s ((Ideal.span {p})^(n+1)) R seed B (τ χ) t ballProfile K := by
  have hQ : (Ideal.span {p}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr hp
  unfold originalChildEnergy
  simp only [original,Finset.sum_div]
  apply congrArg (fun x : ℝ => (16*(n+2:ℝ)*localErrorCost p n)*x)
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro B hB
  unfold childNormalizedGaussSource normalizedGaussSource
  rw [child_volume s (Ideal.span {p}) hQ (n+1) hslot R B (τ χ) t,
    child_gauss_source s ((Ideal.span {p})^(n+1)) R seed B (τ χ) t ballProfile K]


end OAI.SevenEighths.Angular.PlainRows.ChildInputs

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildInputs.original_childEnergy_eq_inputs
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildInputs.original_childEnergy_eq_inputs
