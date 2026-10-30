import AngularPhysicalAllocatedRadialChildren

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.AllocatedRadial
open AllocatedNatural PlainRows PlainRows.CommonRows PlainRows.RadialEnergy
open NaturalRows CommonMask Dyadic ChildRows ExceptionalRows ConcreteTraceCRT MeasureTheory
open CenteredMomentRetainedProfile CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentOriginalRadialComparison (radialEnergy)
open CenteredMomentAllocatedNaturalRadial (profile_support)
open CenteredMomentAllocatedNaturalSource (Plain rawScale rawScale_pos raw_same_product primeSupport_product_radical)
open CenteredMomentCommonMaskEnergy (heightCoefficient heightCoefficient_norm positive_height_phase_norm)
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => ActualEisensteinCubic.O
variable {α:Type*} [Fintype α] [DecidableEq α]
omit [DecidableEq α] in
lemma common_nonzero (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C) : C≠0 := by
  rw [←(Finset.mem_filter.mp B.property).2]
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>alloc_ne s C B i)

lemma child_energy_eq_radial (s : Data α) (r : Radial) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (α⊕Fin 2))) :
    childEnergy s r D a=
      radialEnergy (fun z=>allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P
        D a s.W₁ s.W₂ s.X₁ s.X₂) r.keep r.profile r.scale+
      radialEnergy (fun z=>allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P
        D a s.W₁ s.W₂ s.Y₁ s.Y₂) r.keep r.profile r.scale := by
  have hx:=PlainRows.allocated_positive_summable s.η s.m s.A s.t
    s.W₁ s.W₂ s.b₁ s.b₂ s.X₁ s.X₂ s.support₁ s.support₂ s.X₁_pos s.X₂_pos
    s.slots s.coefficient s.P D a r.keep r.profile r.scale r.scale_pos
  have hy:=PlainRows.allocated_positive_summable s.η s.m s.A s.t
    s.W₁ s.W₂ s.b₁ s.b₂ s.Y₁ s.Y₂ s.support₁ s.support₂ s.Y₁_pos s.Y₂_pos
    s.slots s.coefficient s.P D a r.keep r.profile r.scale r.scale_pos
  unfold childEnergy radialEnergy
  rw [←hx.tsum_add hy]
  apply tsum_congr
  intro z
  unfold Radial.weight
  split_ifs <;> ring

def CommonBound (b M : α→ℝ) (C₀ ε : ℝ) : Prop :=
  ∀s : Input α,(∀i,s.hi i≤b i) → (∀i,s.M i≤M i) →
    ∀(τ : AngularCharacter) (v : ℝ) (C R : Ideal O),R≠0 → ∀B : actualAllocations s.pools C,
    ∀(L : Ideal O) (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),
    ∀V₁ V₂ : Plain,V₁.W=s.W₁ → V₂.W=s.W₂ → ∀r : Radial,(∀z,r.keep z → z≠0) →
    ∀E₁ E₂ : ℝ,0≤E₁ → 0≤E₂ →
    (∀D₁∈(CompletedGauss.primeSupport (R*C)).powerset,
     ∀D₂∈(CompletedGauss.primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      radialEnergy (fun z=>commonChild s τ v C R B L a V₁ V₂ true z D₁ D₂ J) r.keep r.profile r.scale≤E₁) →
    (∀D₁∈(CompletedGauss.primeSupport (R*C)).powerset,
     ∀D₂∈(CompletedGauss.primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      radialEnergy (fun z=>commonChild s τ v C R B L a V₁ V₂ false z D₁ D₂ J) r.keep r.profile r.scale≤E₂) →
    childEnergy (commonData (withHeight s τ v) C R B) r L a≤
      C₀*(Ideal.absNorm (R*C).radical:ℝ)^ε*(E₁+E₂)

theorem actual_common_radial_energy (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C₀ : ℝ,0<C₀ ∧ CommonBound b M C₀ ε := by
  obtain ⟨C₀,hC₀,hbound⟩:=uniform_shared b M hM ε hε
  refine ⟨C₀,hC₀,?_⟩
  intro s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ r hkeep E₁ E₂ hE₁ hE₂ hleft hright
  let d:=commonData (withHeight s τ v) C R B
  have hRC : R*C≠0:=mul_ne_zero hR (common_nonzero s C B)
  have hb:=hbound (CenteredMomentCommonProfile.liveIndices B.val) (liveIndices L a)
  have hβ : ∀i,∀I∈d.slots i,‖d.coefficient i I‖≤M i := by
    intro i I hI
    exact (d.coefficient_bound i I hI).trans (hMs i)
  have hs : ∀i,∀I∈d.slots i,d.coefficient i I≠0 → (I.absNorm:ℝ)≤b i*d.P i := by
    intro i I _ hn
    have hW : d.W i ((I.absNorm:ℝ)/d.P i)≠0 := right_ne_zero_of_mul hn
    have hnorm : (I.absNorm:ℝ)≤d.hi i*d.P i :=
      (div_le_iff₀ (d.P_pos i)).mp (d.support i hW).2
    exact hnorm.trans (mul_le_mul_of_nonneg_right (hhi i) (s.P_pos i).le)
  have hl:=allocated_radial_bound (fun i : CenteredMomentCommonProfile.liveIndices B.val=>b i)
    (fun i=>M i) C₀ ε L a hb τ (R*C) hRC V₁ V₂ d.slots d.coefficient d.P
    d.prime d.P_pos hβ hs v d.X₁ d.X₂ d.X₁_pos d.X₂_pos r hkeep E₁ hE₁ hleft
  have hr:=allocated_radial_bound (fun i : CenteredMomentCommonProfile.liveIndices B.val=>b i)
    (fun i=>M i) C₀ ε L a hb τ (R*C) hRC V₁ V₂ d.slots d.coefficient d.P
    d.prime d.P_pos hβ hs v d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos r hkeep E₂ hE₂ hright
  rw [child_energy_eq_radial]
  have hh:=add_le_add hl hr
  rw [←mul_add] at hh
  simpa only [d,commonData,withHeight,hV₁,hV₂] using hh

lemma nonexceptional_nonzero (η : AngularCharacter) (χ : RayFourExpansion.RayCharacter)
    (Q : Ideal O) (m A z : O)
    (hz : ExceptionalRows.nonexceptional η χ Q m A z) : z≠0 := hz.1

theorem uniform_initial_common_radial_energy (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C₀ : ℝ,0<C₀ ∧ ∀T : Finset α,CommonBound (fun i : T=>b i) (fun i : T=>M i) C₀ ε := by
  have he (T : Finset α) : ∃C₀ : ℝ,0<C₀ ∧ CommonBound (fun i : T=>b i) (fun i : T=>M i) C₀ ε :=
    actual_common_radial_energy (fun i : T=>b i) (fun i : T=>M i) (fun i=>hM i) ε hε
  choose C hC hb using he
  let C₀ : ℝ:=1+∑T : Finset α,C T
  have hsum : 0≤∑T : Finset α,C T:=Finset.sum_nonneg (fun T _=>(hC T).le)
  refine ⟨C₀,by dsimp [C₀];linarith,?_⟩
  intro T s hhi hMs τ v I R hR B L a V₁ V₂ hV₁ hV₂ r hkeep E₁ E₂ hE₁ hE₂ hleft hright
  have hCB : C T≤C₀ := by
    have hh:=Finset.single_le_sum (fun T _=>(hC T).le) (Finset.mem_univ T)
    dsimp [C₀];linarith
  exact (hb T s hhi hMs τ v I R hR B L a V₁ V₂ hV₁ hV₂ r hkeep E₁ E₂ hE₁ hE₂ hleft hright).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (add_nonneg hE₁ hE₂))

lemma common_raw_same_product (s : Input α) (τ : AngularCharacter) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))) :
    let d:=commonData (withHeight s τ v) C R B
    rawScale L a d.X₁ 0*rawScale L a d.X₂ 1=rawScale L a d.Y₁ 0*rawScale L a d.Y₂ 1 :=
  raw_same_product L a _ _ _ _ (commonData (withHeight s τ v) C R B).same_product.symm

theorem original_nonexceptional_common_radial_energy (b M : α→ℝ) (hM : ∀i,0≤M i)
    (ε : ℝ) (hε : 0<ε) :
    ∃C₀ : ℝ,0<C₀ ∧ ∀s : Input α,(∀i,s.hi i≤b i) → (∀i,s.M i≤M i) →
    ∀(τ : AngularCharacter) (v : ℝ) (C R : Ideal O),R≠0 → ∀B : actualAllocations s.pools C,
    ∀(L : Ideal O) (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),
    ∀V₁ V₂ : Plain,V₁.W=s.W₁ → V₂.W=s.W₂ → ∀(η : AngularCharacter) (χ : RayFourExpansion.RayCharacter) (Q : Ideal O) (m A : O)
      (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H)
      (hΦ : ∀z : O,0≤(Φ (CenteredMomentSectorLocalization.normValue z/H)).re),
    let r:=CenteredMomentSecondOriginalChildren.sourceRadial
      (ExceptionalRows.nonexceptional η χ Q m A) Φ H hH hΦ

    ∀E₁ E₂ : ℝ,0≤E₁ → 0≤E₂ →
    (∀D₁∈(CompletedGauss.primeSupport (R*C)).powerset,
     ∀D₂∈(CompletedGauss.primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      radialEnergy (fun z=>commonChild s τ v C R B L a V₁ V₂ true z D₁ D₂ J) r.keep r.profile r.scale≤E₁) →
    (∀D₁∈(CompletedGauss.primeSupport (R*C)).powerset,
     ∀D₂∈(CompletedGauss.primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      radialEnergy (fun z=>commonChild s τ v C R B L a V₁ V₂ false z D₁ D₂ J) r.keep r.profile r.scale≤E₂) →
    childEnergy (commonData (withHeight s τ v) C R B) r L a≤
      C₀*(Ideal.absNorm (R*C).radical:ℝ)^ε*(E₁+E₂) := by
  obtain ⟨C₀,hC₀,hb⟩:=actual_common_radial_energy b M hM ε hε
  refine ⟨C₀,hC₀,?_⟩
  intro s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ η χ Q m A Φ H hH hΦ r
    E₁ E₂ hE₁ hE₂ hleft hright
  exact hb s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ r
    (fun _ hz=>hz.1) E₁ E₂ hE₁ hE₂ hleft hright

end OAI.SevenEighths.Angular.AllocatedRadial

#print axioms OAI.SevenEighths.Angular.AllocatedRadial.actual_common_radial_energy
#print axioms OAI.SevenEighths.Angular.AllocatedRadial.uniform_initial_common_radial_energy
#print axioms OAI.SevenEighths.Angular.AllocatedRadial.original_nonexceptional_common_radial_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AllocatedRadial.original_nonexceptional_common_radial_energy
