import AngularPhysicalNormalizedActiveInput
import AngularPhysicalOriginalColumnSupport
import OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps
open CommonRows ChildInputs
open ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentFirstAmplificationChoice CenteredMomentHeckeColumnWindow
open CenteredMomentCommonAllocationSum CenteredMomentCommonRawScale
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
open CenteredMomentSourceMass CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
open CenteredMomentAmplificationChildSourceCaps (geometry geometry_ge_one norm_ge_one live_card_le)
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]
local instance angularChildSourceVolumeDecEq {κ:Type*} : DecidableEq κ := Classical.decEq _
lemma allocation_product (s : Input ι) (C : Ideal O) (B : actualAllocations s.pools C) :
    finiteTupleProduct B.val=C := (Finset.mem_filter.mp B.property).2

lemma allocation_ne (s : Input ι) (C : Ideal O) (B : actualAllocations s.pools C) : C≠0 := by
  rw [←allocation_product s C B]
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>alloc_ne s C B i)

theorem common_volume (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : AngularCharacter) (t : ℝ) :
    CommonRows.volume (child s C R B τ t)=
      CommonRows.volume s/rawReduction B.val s.P := by
  have hh:=raw_scale_identity B.val (alloc_ne s C B) (s.X₁*s.X₂) s.P
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  apply (eq_div_iff hr.ne').mpr
  change _ = CommonRows.volume s at hh
  rw [←hh]
  congr 1
  unfold CommonRows.volume child commonData remainingRaw plainNorm
  dsimp only
  ring

theorem common_volume_le (N : ℕ) (b : ℝ) (hb : 1≤b) (s : Input ι)
    (hcard : Fintype.card ι≤N) (hs : s.upper≤b)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0) :
    CommonRows.volume (child s C R B τ t)≤
      b^N*CommonRows.volume s/(C.absNorm:ℝ) := by
  have hc:=norm_ge_one C (allocation_ne s C B)
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have hn:=(actual_reduction_norm B.val (alloc_ne s C B) C R (allocation_product s C B)
    s.ν s.W s.P s.P_pos s.lower b s.lower_pos
    (fun i x hx=>⟨(s.slot_support i hx).1,((s.slot_support i hx).2).trans hs⟩) hne).2
  rw [max_eq_right hb] at hn
  have hn':(C.absNorm:ℝ)≤b^N*rawReduction B.val s.P := hn.trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hb hcard) hr.le)
  rw [common_volume]
  apply (div_le_div_iff₀ hr (zero_lt_one.trans_le hc)).mpr
  nlinarith [CommonRows.volume_pos s]

theorem frozen_zero (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (hz : frozenCoefficient B.val C R s.ν s.W s.P=0) (f : O→ℂ) (z : O) :
    frozenCoefficient B.val C R s.ν s.W s.P*f z=0 := by rw [hz,zero_mul]

theorem radius_le (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 0≤b₁) (_h₂ : 0≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (hhi : ∀i,0≤s.hi i) (hhib : ∀i,s.hi i≤b)
    (hs₁ : 0≤s.b₁) (hs₂ : 0≤s.b₂) (hb₁ : s.b₁≤b₁) (hb₂ : s.b₂≤b₂) :
    0≤CommonRows.sourceRadius s ∧ CommonRows.sourceRadius s≤(b^N*b₁*b₂)*CommonRows.volume s := by
  have hp:0≤∏i,s.hi i:=Finset.prod_nonneg (fun i _=>hhi i)
  have hp':(∏i,s.hi i)≤b^N := by
    calc
      _ ≤ ∏i:ι,b := Finset.prod_le_prod₀ (fun i _=>hhi i) (fun i _=>hhib i)
      _ = b^Fintype.card ι := by simp
      _ ≤ b^N := pow_le_pow_right₀ hb hc
  have hpp:=mul_le_mul (mul_le_mul hp' hb₁ hs₁ (pow_nonneg (zero_le_one.trans hb) _)) hb₂ hs₂
    (mul_nonneg (pow_nonneg (zero_le_one.trans hb) _) h₁)
  change 0≤_ ∧ _≤_
  have he:CommonRows.sourceRadius s=((∏i,s.hi i)*s.b₁*s.b₂)*CommonRows.volume s := by
    unfold CommonRows.sourceRadius CommonRows.volume; ring
  rw [he]
  exact ⟨mul_nonneg (mul_nonneg (mul_nonneg hp hs₁) hs₂)
    (CommonRows.volume_pos s).le,
    mul_le_mul_of_nonneg_right hpp (CommonRows.volume_pos s).le⟩

theorem original_beta (s : Input ι) (R seed : Ideal O) :
    (original s R seed).beta=coefficient s R seed := rfl

theorem child_column_norm (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : AngularCharacter) (t : ℝ) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (I : Ideal O)
    (hne : (original (child s C R B τ t) (R*C) seed).beta I≠0) :
    I≠0 ∧ seed∣I ∧ (I.absNorm:ℝ)≤CommonRows.sourceRadius (child s C R B τ t) := by
  rw [original_beta] at hne
  have hn:=original_column_norm (child s C R B τ t) (R*C) seed I hz₁ hz₂ hne
  exact ⟨hn.1,original_column_mask _ _ _ I hne,hn.2⟩

def nominal (s : Input ι) (K : ℝ) : ℝ := CommonRows.volume s^2/K

lemma nominal_pos (s : Input ι) (K : ℝ) (hK : 0<K) : 0<nominal s K :=
  div_pos (sq_pos_of_pos (CommonRows.volume_pos s)) hK

lemma nominal_lower (s : Input ι) (K : ℝ) :
    (CommonRows.volume s)^2/K≤nominal s K := le_rfl

lemma nominal_upper (s : Input ι) (K G H : ℝ) (hK : 0<K) (_hG : 0≤G) (_hH : 0≤H)
    (h : CommonRows.volume s≤G*H) :
    nominal s K≤G^2*H^2/K := by
  unfold nominal
  exact div_le_div_of_nonneg_right (by nlinarith [CommonRows.volume_pos s]) hK.le

def Endpoints (b b₁ b₂ : ℝ) (s : Input ι) : Prop :=
  s.upper≤b ∧ (∀i,0≤s.hi i) ∧ 0≤s.b₁ ∧ s.b₁≤b₁ ∧ 0≤s.b₂ ∧ s.b₂≤b₂

lemma endpoints_child (b b₁ b₂ : ℝ) (s : Input ι) (h : Endpoints b b₁ b₂ s)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ) :
    Endpoints b b₁ b₂ (child s C R B τ t) :=
  ⟨h.1,fun i=>h.2.1 i.val,h.2.2⟩

lemma radius_bound (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s) :
    0≤CommonRows.sourceRadius s ∧
    CommonRows.sourceRadius s≤
      (b^N*b₁*b₂)*CommonRows.volume s :=
  radius_le N b b₁ b₂ hb (zero_le_one.trans h₁) (zero_le_one.trans h₂) s hc he.2.1
    (fun i=>(s.upper_ge i).trans he.1) he.2.2.1 he.2.2.2.2.1 he.2.2.2.1 he.2.2.2.2.2

end OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.allocation_product
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.allocation_product

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.allocation_ne
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.allocation_ne

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.common_volume
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.common_volume

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.common_volume_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.common_volume_le

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.frozen_zero
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.frozen_zero

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.radius_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.radius_le

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.original_beta
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.original_beta

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.child_column_norm
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.child_column_norm

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.nominal_pos
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.nominal_pos

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.nominal_lower
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.nominal_lower

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.nominal_upper
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.nominal_upper

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.endpoints_child
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.endpoints_child

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.radius_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.radius_bound
