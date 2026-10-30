import AngularPhysicalAllocatedNormalized
import AngularPhysicalPlainCommonData
import OAI.NumberTheory.DirichletL.Moments.AllocatedChildCapacity

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows.AllocatedChildCapacity
open CommonRows CommonMask AllocatedNatural
open CenteredMomentAllocatedNaturalSource (Plain rawScale rawScale_pos)
open CenteredMomentRetainedProfile CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentDivisorRectangle CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentAllocatedChildCapacity
  (plainLogs remainingLogs clippingLoss clipped_pair_log clipping_loss_bound excess_le raw_volume)
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
def preVolume (s : Data ι) : ℝ := s.X₁*s.X₂*∏i,s.P i

omit [DecidableEq ι] in
lemma preVolume_pos (s : Data ι) : 0<preVolume s :=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=>s.P_pos i))

theorem allocated_survives (s : Data ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (z : O)
    (X₁ X₂ : ℝ) (h₁ : 0<X₁) (h₂ : 0<X₂)
    (hne : allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0) :
    1≤rawScale D a X₁ 0*s.b₁ ∧ 1≤rawScale D a X₂ 1*s.b₂ := by
  have hz (hs : rawScale D a X₁ 0*s.b₁<1 ∨ rawScale D a X₂ 1*s.b₂<1) : False := by
    apply hne
    exact AllocatedNatural.original_retained_zero s.η s.m s.A z _ _ _ _
      s.support₁ s.support₂ (fun i : liveIndices D a=>s.slots i)
      (fun i : liveIndices D a=>s.coefficient i) (fun i : liveIndices D a=>s.P i)
      s.t _ _ (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1) hs
  constructor
  · exact le_of_not_gt (fun hh=>hz (Or.inl hh))
  · exact le_of_not_gt (fun hh=>hz (Or.inr hh))

theorem paired_capacity (s : Data ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z κ M : ℝ) (hZ : 1<Z) (hκ : (1/6:ℝ)≤κ) (hP : ∀i,1≤s.P i) :
    let bound := max (Real.logb Z (preVolume s)-Real.logb Z (formalReductionFactor D a s.P)-M+
      (6*κ-1)*(∑i,Real.logb Z (s.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂)) 0
    (∀z,allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ s.X₁ s.X₂≠0 →
      max (plainLogs D a Z s.X₁ s.X₂+6*κ*remainingLogs D a Z s.P-M) 0≤bound) ∧
    (∀z,allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ s.Y₁ s.Y₂≠0 →
      max (plainLogs D a Z s.Y₁ s.Y₂+6*κ*remainingLogs D a Z s.P-M) 0≤bound) := by
  constructor
  · intro z hn
    obtain ⟨h₁,h₂⟩ := allocated_survives s D a z s.X₁ s.X₂ s.X₁_pos s.X₂_pos hn
    exact excess_le D a Z _ _ _ _ κ M hZ s.X₁_pos s.X₂_pos s.P hP hκ h₁ h₂
  · intro z hn
    obtain ⟨h₁,h₂⟩ := allocated_survives s D a z s.Y₁ s.Y₂ s.Y₁_pos s.Y₂_pos hn
    have hb := excess_le D a Z _ _ _ _ κ M hZ s.Y₁_pos s.Y₂_pos s.P hP hκ h₁ h₂
    simpa only [s.same_product,preVolume] using hb

theorem allocated_clipping (s : Data ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (z : O)
    (Z X₁ X₂ : ℝ) (hZ : 1<Z) (h₁ : 0<X₁) (h₂ : 0<X₂)
    (hne : allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0) :
    plainLogs D a Z X₁ X₂=Real.logb Z (rawScale D a X₁ 0)+Real.logb Z (rawScale D a X₂ 1)+
      clippingLoss Z (rawScale D a X₁ 0) (rawScale D a X₂ 1) ∧
    0≤clippingLoss Z (rawScale D a X₁ 0) (rawScale D a X₂ 1) ∧
    clippingLoss Z (rawScale D a X₁ 0) (rawScale D a X₂ 1)≤Real.logb Z (max 1 s.b₁*max 1 s.b₂) := by
  obtain ⟨hs₁,hs₂⟩ := allocated_survives s D a z X₁ X₂ h₁ h₂ hne
  exact ⟨clipped_pair_log Z _ _ hZ (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1),
    clipping_loss_bound Z _ _ _ _ hZ (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1) hs₁ hs₂⟩

end OAI.SevenEighths.Angular.PlainRows.AllocatedChildCapacity

#print axioms OAI.SevenEighths.Angular.PlainRows.AllocatedChildCapacity.preVolume_pos
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AllocatedChildCapacity.preVolume_pos

#print axioms OAI.SevenEighths.Angular.PlainRows.AllocatedChildCapacity.allocated_survives
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AllocatedChildCapacity.allocated_survives

#print axioms OAI.SevenEighths.Angular.PlainRows.AllocatedChildCapacity.paired_capacity
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AllocatedChildCapacity.paired_capacity

#print axioms OAI.SevenEighths.Angular.PlainRows.AllocatedChildCapacity.allocated_clipping
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AllocatedChildCapacity.allocated_clipping
