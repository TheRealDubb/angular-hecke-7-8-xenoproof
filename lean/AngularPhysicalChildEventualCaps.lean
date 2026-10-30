import AngularPhysicalChildPunctureBounds

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
local instance AngularChildEventualCapsDecEq {κ:Type*} : DecidableEq κ := Classical.decEq _
theorem eventual_twice_caps (N : ℕ) (b b₁ b₂ ε : ℝ)
    (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂) (hε : 0<ε) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{ι:Type*}[Fintype ι],∀(s:Input ι),
    Fintype.card ι≤N → Endpoints b b₁ b₂ s →
    ∀(C R:Ideal O)(B:actualAllocations s.pools C)(τ:AngularCharacter)(t:ℝ),
    frozenCoefficient B.val C R s.ν s.W s.P≠0 →
    ∀(Q:Ideal O),Q≠0 → ∀k:ℕ,
    (∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I) →
    ∀(Bp:actualAllocations (child s C R B τ t).pools (Q^k))(υ:AngularCharacter)(v K A D ξ:ℝ),
    0<K → CommonRows.volume s≤Z^A → K⁻¹≤Z^D →
    let d:=twiceChild s C R B τ t Q k Bp υ v;
    CommonRows.volume d≤Z^(A+ε) ∧
    0≤CommonRows.sourceRadius d ∧
    CommonRows.sourceRadius d≤Z^(A+ε) ∧
    0<nominal d K ∧ nominal d K≤Z^(2*A+D+ε) ∧
    0<frequencyRadius (nominal d K) Z ξ ∧
    frequencyRadius (nominal d K) Z ξ≤Z^(2*A+D+ε+ξ/2) := by
  filter_upwards [eventual_geometry (geometry N b b₁ b₂) ε (geometry_ge_one N b b₁ b₂ hb h₁ h₂) hε] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ s hc he C R B τ t hne Q hQ k hslot Bp υ v K A D ξ hK hVp hKp
  have hcap:=twice_caps N b b₁ b₂ hb h₁ h₂ s hc he C R B τ t hne Q hQ k hslot Bp υ v
  have hd:1≤(C.absNorm:ℝ)*(Q.absNorm:ℝ)^k := by
    have hc:=norm_ge_one C (allocation_ne s C B)
    have hq:1≤(Q.absNorm:ℝ)^k:=one_le_pow₀ (norm_ge_one Q hQ)
    nlinarith
  have hH:CommonRows.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)≤
      CommonRows.volume s :=
    div_le_self (CommonRows.volume_pos s).le hd
  have hm:=mul_le_mul_of_nonneg_left hH (zero_le_one.trans (geometry_ge_one N b b₁ b₂ hb h₁ h₂))
  have hh:=polynomial_caps (geometry N b b₁ b₂) _ _ _ K Z A D ε ξ
    (geometry_ge_one N b b₁ b₂ hb h₁ h₂) hZ.1 hZ.2.2
    (CommonRows.volume_pos s)
    (CommonRows.volume_pos _) hcap.2.1 hK
    (hcap.2.2.1.trans hm) (hcap.2.2.2.trans hm) hVp hKp
  exact ⟨hh.1,hcap.2.1,hh.2.1,nominal_pos _ K hK,hh.2.2⟩

theorem plain_zero (s : Input ι) (a₁ a₂ b₁ b₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support s.W₁⊆Set.Icc a₁ b₁)
    (hs₂ : Function.support s.W₂⊆Set.Icc a₂ b₂) : s.W₁ 0=0 ∧ s.W₂ 0=0 := by
  constructor
  · by_contra hn; exact (not_le_of_gt ha₁) (hs₁ hn).1
  · by_contra hn; exact (not_le_of_gt ha₂) (hs₂ hn).1

theorem twice_slots_ge_one (s : Input ι) (hs : ∀i,1≤s.P i)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ)
    (Q : Ideal O) (k : ℕ) (Bp : actualAllocations (child s C R B τ t).pools (Q^k))
    (υ : AngularCharacter) (v : ℝ) : ∀i,1≤(twiceChild s C R B τ t Q k Bp υ v).P i :=
  fun i=>hs i.val.val

theorem child_source_zero (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : AngularCharacter) (t : ℝ) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsmall : CommonRows.sourceRadius (child s C R B τ t)<1)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    CenteredMomentOriginalChildEnergy.sourceGaussEnergy (original (child s C R B τ t) (R*C) seed).columns
      (original (child s C R B τ t) (R*C) seed).beta (heightCoeff τ t) W K=0 := by
  have hz (I:Ideal O):(original (child s C R B τ t) (R*C) seed).beta I=0 := by
    by_contra hn
    have hh:=child_column_norm s C R seed B τ t hz₁ hz₂ I hn
    exact (not_le_of_gt hsmall) ((norm_ge_one I hh.1).trans hh.2.2)
  simp [CenteredMomentOriginalChildEnergy.sourceGaussEnergy,CenteredMomentGaussEnergy.gaussEnergy,
    CenteredMomentGaussEnergy.gaussPolynomial,hz]

theorem eventual_live_puncture (N : ℕ) (b b₁ b₂ ε : ℝ)
    (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂) (hε : 0<ε) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{ι:Type*}[Fintype ι],∀(s:Input ι),
    Fintype.card ι≤N → Endpoints b b₁ b₂ s →
    ∀(C R seed:Ideal O)(B:actualAllocations s.pools C)(τ:AngularCharacter)(t:ℝ),
    frozenCoefficient B.val C R s.ν s.W s.P≠0 →
    ∀(Q:Ideal O),Q≠0 → ∀k:ℕ,
    (∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I) →
    ∀(Bp:actualAllocations (child s C R B τ t).pools (Q^k))(υ:AngularCharacter)(v A P:ℝ),
    s.W₁ 0=0 → s.W₂ 0=0 → CommonRows.volume s≤Z^A →
    (R.absNorm:ℝ)≤Z^P →
    (∃I:Ideal O,(original (twiceChild s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed).beta I≠0) →
    (((R*C)*(Q^k)).absNorm:ℝ)≤Z^(A+P+ε) := by
  filter_upwards [eventual_geometry (geometry N b b₁ b₂) ε (geometry_ge_one N b b₁ b₂ hb h₁ h₂) hε] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ s hc he C R seed B τ t hne Q hQ k hslot Bp υ v A P hz₁ hz₂ hVp hRp ⟨I,hI⟩
  have hn:=(live_puncture_bound N b b₁ b₂ hb h₁ h₂ s hc he C R seed B τ t hne Q hQ k hslot Bp υ v hz₁ hz₂ I hI).2
  have hg:=geometry_ge_one N b b₁ b₂ hb h₁ h₂
  have hm:=mul_le_mul (mul_le_mul hRp hZ.2.1 (zero_le_one.trans hg)
    (Real.rpow_nonneg (by linarith : 0≤Z) P)) hVp
    (CommonRows.volume_pos s).le
    (mul_nonneg (Real.rpow_nonneg (by linarith : 0≤Z) P) (Real.rpow_nonneg (by linarith : 0≤Z) ε))
  apply hn.trans (hm.trans_eq ?_)
  rw [←Real.rpow_add (by linarith : 0<Z),←Real.rpow_add (by linarith : 0<Z)]
  congr 1;ring

end OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.eventual_twice_caps
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.eventual_twice_caps

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.plain_zero
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.plain_zero

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.twice_slots_ge_one
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.twice_slots_ge_one

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.child_source_zero
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.child_source_zero

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.eventual_live_puncture
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.eventual_live_puncture
