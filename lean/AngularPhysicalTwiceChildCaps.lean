import AngularPhysicalChildSourceVolume

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
open CenteredMomentAmplificationChildSourceCaps
  (geometry geometry_ge_one norm_ge_one live_card_le puncture_norm eventual_geometry polynomial_caps)
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]
local instance AngularTwiceChildCapsDecEq {κ:Type*} : DecidableEq κ := Classical.decEq _
def twiceChild (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : AngularCharacter) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : AngularCharacter) (v : ℝ) :=
  child (child s C R B τ t) (Q^k) (R*C) Bp υ v

theorem twiceChild_data (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : AngularCharacter) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : AngularCharacter) (v : ℝ) :
    (twiceChild s C R B τ t Q k Bp υ v).η=υ ∧
    (twiceChild s C R B τ t Q k Bp υ v).t=v ∧
    (twiceChild s C R B τ t Q k Bp υ v).m=
      fixedBadMask*idealGenerator ((R*C)*(Q^k)) := ⟨rfl,rfl,rfl⟩

theorem twice_volume (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : AngularCharacter) (t : ℝ) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : AngularCharacter) (v : ℝ) :
    CommonRows.volume (twiceChild s C R B τ t Q k Bp υ v)=
      CommonRows.volume s/(rawReduction B.val s.P*(Q.absNorm:ℝ)^k) := by
  rw [twiceChild,child_volume _ Q hQ k hslot,common_volume,div_div]

theorem twice_caps (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : AngularCharacter) (v : ℝ) :
    let d:=twiceChild s C R B τ t Q k Bp υ v;
    let H:=CommonRows.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k);
    0<H ∧ 0≤CommonRows.sourceRadius d ∧
    CommonRows.volume d≤geometry N b b₁ b₂*H ∧
    CommonRows.sourceRadius d≤geometry N b b₁ b₂*H := by
  dsimp only
  have hC:=norm_ge_one C (allocation_ne s C B)
  have hNp:0<(Q.absNorm:ℝ)^k:=pow_pos (zero_lt_one.trans_le (norm_ge_one Q hQ)) k
  have hH:0<CommonRows.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k):=
    div_pos (CommonRows.volume_pos s)
      (mul_pos (zero_lt_one.trans_le hC) hNp)
  have hv:CommonRows.volume (twiceChild s C R B τ t Q k Bp υ v)≤
      b^N*(CommonRows.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)) := by
    rw [twiceChild,child_volume _ Q hQ k hslot]
    exact (div_le_div_of_nonneg_right (common_volume_le N b hb s hc he.1 C R B τ t hne) hNp.le).trans_eq (by ring)
  have hc1:= (live_card_le B.val).trans hc
  have hc2:= (live_card_le Bp.val).trans hc1
  have hep:=endpoints_child b b₁ b₂ _ (endpoints_child b b₁ b₂ s he C R B τ t) (Q^k) (R*C) Bp υ v
  have hr:=radius_bound N b b₁ b₂ hb h₁ h₂ _ hc2 hep
  have hbf:0≤b^N*b₁*b₂:=by positivity
  have hpow: b^N≤geometry N b b₁ b₂ := by
    have hp:1≤b^N:=one_le_pow₀ hb
    unfold geometry
    rw [show 2*N=N+N by omega,pow_add]
    have hh:1≤b₁*b₂:=by nlinarith
    nlinarith
  refine ⟨hH,hr.1,hv.trans (mul_le_mul_of_nonneg_right hpow hH.le),?_⟩
  exact hr.2.trans ((mul_le_mul_of_nonneg_left hv hbf).trans_eq (by
    unfold geometry; rw [show 2*N=N+N by omega,pow_add];ring))

theorem twice_column (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s)
    (C R seed : Ideal O) (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : AngularCharacter) (v : ℝ)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (I : Ideal O)
    (hI : (original (twiceChild s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed).beta I≠0) :
    I≠0 ∧ seed∣I ∧ (I.absNorm:ℝ)≤geometry N b b₁ b₂*
      (CommonRows.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)) := by
  have hi:=child_column_norm (child s C R B τ t) (Q^k) (R*C) seed Bp υ v hz₁ hz₂ I hI
  have hcap:=twice_caps N b b₁ b₂ hb h₁ h₂ s hc he C R B τ t hne Q hQ k hslot Bp υ v
  exact ⟨hi.1,hi.2.1,hi.2.2.trans hcap.2.2.2⟩

theorem twice_nominal (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : AngularCharacter) (v K : ℝ) (hK : 0<K) :
    let d:=twiceChild s C R B τ t Q k Bp υ v;
    0<nominal d K ∧ CommonRows.volume d^2/K=nominal d K ∧
    nominal d K≤(geometry N b b₁ b₂)^2*
      (CommonRows.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k))^2/K := by
  have hcap:=twice_caps N b b₁ b₂ hb h₁ h₂ s hc he C R B τ t hne Q hQ k hslot Bp υ v
  exact ⟨nominal_pos _ K hK,rfl,nominal_upper _ K _ _ hK
    (zero_le_one.trans (geometry_ge_one N b b₁ b₂ hb h₁ h₂)) hcap.1.le hcap.2.2.1⟩

end OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.twiceChild_data
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.twiceChild_data

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.twice_volume
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.twice_volume

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.twice_caps
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.twice_caps

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.twice_column
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.twice_column

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.twice_nominal
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.twice_nominal
