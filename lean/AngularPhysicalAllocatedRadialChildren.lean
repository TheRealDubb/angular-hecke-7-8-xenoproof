import AngularPhysicalAllocatedRadialShared
import AngularPhysicalCommonHeightEnvelope

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
def commonChild (s : Input α) (τ : AngularCharacter) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (V₁ V₂ : Plain) (left : Bool) (z : O) (D₁ D₂ : Finset (Ideal O))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) : ℂ :=
  let d:=commonData (withHeight s τ v) C R B
  if left then child (naturalCharacter τ z) L a V₁ V₂ d.slots d.coefficient d.P v
    d.X₁ d.X₂ d.X₁_pos d.X₂_pos D₁ D₂ J
  else child (naturalCharacter τ z) L a V₁ V₂ d.slots d.coefficient d.P v
    d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos D₁ D₂ J

lemma common_rawScale (s : Input α) (τ : AngularCharacter) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))) :
    rawScale L a (commonData (withHeight s τ v) C R B).X₁ 0=
      s.X₁/(Ideal.absNorm (B.val (Sum.inr 0)*CenteredMomentDivisorRectangle.selectedPlain L a 0):ℝ) := by
  simp only [rawScale,commonData,withHeight,map_mul,Nat.cast_mul,div_div]

theorem common_allocated_normalized (s : Input α) (τ : AngularCharacter) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (hRC : R*C≠0) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (V₁ V₂ : Plain) (hV₁ : V₁.W=s.W₁) (hV₂ : V₂.W=s.W₂) (z : O) (hz : z≠0) :
    let d:=commonData (withHeight s τ v) C R B
    allocatedPositiveRow d.η d.m d.A z d.t d.slots d.coefficient d.P L a d.W₁ d.W₂ d.X₁ d.X₂=
      (((clippedScale (rawScale L a d.X₁ 0)):ℂ)^(Complex.I*v)*
       ((clippedScale (rawScale L a d.X₂ 1)):ℂ)^(Complex.I*v))*
       (polynomial (excluded (naturalCharacter τ z) (R*C)) false
          (V₁.profile _ (rawScale_pos L a d.X₁ d.X₁_pos 0) v) (clippedScale (rawScale L a d.X₁ 0)) 0 0*
        polynomial (excluded (naturalCharacter τ z) (R*C)) false
          (V₂.profile _ (rawScale_pos L a d.X₂ d.X₂_pos 1) v) (clippedScale (rawScale L a d.X₂ 1)) 0 0*
        ∏i∈liveIndices L a,naturalSlot (excluded (naturalCharacter τ z) (R*C))
          (d.slots i) (heightCoefficient (d.coefficient i) v) (d.P i)) := by
  dsimp only
  rw [naturalCharacter_eq τ z hz]
  have hh:=allocated_normalized τ z hz (R*C) hRC L a V₁ V₂
    (commonData (withHeight s τ v) C R B).slots
    (commonData (withHeight s τ v) C R B).coefficient
    (commonData (withHeight s τ v) C R B).P
    (commonData (withHeight s τ v) C R B).P_pos v
    (commonData (withHeight s τ v) C R B).X₁ (commonData (withHeight s τ v) C R B).X₂
    (commonData (withHeight s τ v) C R B).X₁_pos (commonData (withHeight s τ v) C R B).X₂_pos
  simpa only [hV₁,hV₂,commonData,withHeight] using hh

theorem allocated_radial_bound (b M : α→ℝ) (C₀ ε : ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (hb : Shared (liveIndices D a) b M C₀ ε)
    (η : AngularCharacter) (R : Ideal O) (hR : R≠0) (V₁ V₂ : Plain)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (hprime : ∀i,∀I∈pool i,Prime I) (hP : ∀i,0<P i)
    (hβ : ∀i,∀I∈pool i,‖β i I‖≤M i)
    (hs : ∀i,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤b i*P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (r : Radial) (hkeep : ∀z,r.keep z → z≠0) (E : ℝ) (hE : 0≤E)
    (hchild : ∀D₁∈(CompletedGauss.primeSupport R).powerset,
      ∀D₂∈(CompletedGauss.primeSupport R).powerset,∀J∈(liveIndices D a).powerset,
      radialEnergy (fun z=>child (naturalCharacter η z) D a V₁ V₂ pool β P t X₁ X₂
        hX₁ hX₂ D₁ D₂ J) r.keep r.profile r.scale≤E) :
    radialEnergy (fun z=>allocatedPositiveRow η
      (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z t pool β P D a V₁.W V₂.W X₁ X₂) r.keep r.profile r.scale≤
        C₀*(Ideal.absNorm R.radical:ℝ)^ε*E := by
  have hh:=hb (CompletedGauss.primeSupport R) (CenteredMomentNaturalRowSource.support_prime R) (naturalCharacter η)
    (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t)
    (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t)
    (clippedScale (rawScale D a X₁ 0)) (clippedScale (rawScale D a X₂ 1))
    (V₁.a/max 1 V₁.b) (max 1 V₁.b) (V₂.a/max 1 V₂.b) (max 1 V₂.b)
    pool (fun i=>heightCoefficient (β i) t) P r.keep r.profile r.scale E
    (by unfold clippedScale;positivity) (by unfold clippedScale;positivity)
    (by positivity) (by positivity) (profile_support V₁ _ _ t) (profile_support V₂ _ _ t)
    (fun i _=>hprime i) (fun i _=>hP i)
    (fun i _ I hi=>by rw [heightCoefficient_norm _ _ _ (hprime i I hi).ne_zero];exact hβ i I hi)
    (fun i _ I hi hn=>hs i I hi (left_ne_zero_of_mul hn)) r.scale_pos r.nonneg hE hchild
  rw [←primeSupport_product_radical R hR]
  convert hh using 1
  unfold radialEnergy
  apply tsum_congr
  intro z
  split_ifs with hz
  · dsimp only
    rw [allocated_normalized η z (hkeep z hz) R hR D a V₁ V₂ pool β P hP t X₁ X₂ hX₁ hX₂,
      naturalCharacter_eq η z (hkeep z hz)]
    have hphase (U : ℝ) : ‖((clippedScale U):ℂ)^(Complex.I*t)‖=1 :=
      positive_height_phase_norm _ _ (by unfold clippedScale;positivity)
    simp only [excluded,norm_mul,hphase,one_mul]
  · rfl

theorem natural_child_summable (η : AngularCharacter) (R : Ideal O)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : D₁⊆CompletedGauss.primeSupport R)
    (hD₂ : D₂⊆CompletedGauss.primeSupport R) (J : Finset α) (r : Radial) :
    Summable (fun z=>if r.keep z then
      ‖child (naturalCharacter η z) D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ D₁ D₂ J‖^2*
        (r.profile (‖eisEmbedding z‖^2/r.scale)).re else 0) := by
  have hn (S : Finset (Ideal O)) (hS : S⊆CompletedGauss.primeSupport R) :
      (0:ℝ)<Ideal.absNorm (∏I∈S,I) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr (fun I hI=>(CenteredMomentNaturalRowSource.support_prime R I (hS hI)).ne_zero)))
  obtain ⟨PB,hPB,hbound⟩:=slots_bounded (liveIndices D a\J) pool (fun i=>heightCoefficient (β i) t) P
  exact pair_radial_summable (naturalCharacter η)
    (fun z=>∏i∈liveIndices D a\J,naturalSlot (naturalCharacter η z) (pool i) (heightCoefficient (β i) t) (P i))
    (fun _=>0) (fun _=>0)
    (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t) (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t)
    (V₁.a/max 1 V₁.b) (max 1 V₁.b) (V₂.a/max 1 V₂.b) (max 1 V₂.b)
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)) PB
    (by positivity) (by positivity) (div_pos (by unfold clippedScale;positivity) (hn D₁ hD₁))
    (div_pos (by unfold clippedScale;positivity) (hn D₂ hD₂))
    (profile_support V₁ _ _ t) (profile_support V₂ _ _ t) (fun z=>hbound (naturalCharacter η z))
    r.keep r.profile r.scale r.scale_pos

end OAI.SevenEighths.Angular.AllocatedRadial

#print axioms OAI.SevenEighths.Angular.AllocatedRadial.common_allocated_normalized
#print axioms OAI.SevenEighths.Angular.AllocatedRadial.allocated_radial_bound
#print axioms OAI.SevenEighths.Angular.AllocatedRadial.natural_child_summable
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AllocatedRadial.natural_child_summable
