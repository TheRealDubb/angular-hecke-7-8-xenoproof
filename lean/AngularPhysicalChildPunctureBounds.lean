import AngularPhysicalTwiceChildCaps

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
local instance AngularChildPunctureBoundsDecEq {κ:Type*} : DecidableEq κ := Classical.decEq _
theorem live_puncture_bound (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s)
    (C R seed : Ideal O) (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : AngularCharacter) (v : ℝ)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (I : Ideal O)
    (hI : (original (twiceChild s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed).beta I≠0) :
    (C.absNorm:ℝ)*(Q.absNorm:ℝ)^k≤geometry N b b₁ b₂*CommonRows.volume s ∧
    (((R*C)*(Q^k)).absNorm:ℝ)≤(R.absNorm:ℝ)*geometry N b b₁ b₂*CommonRows.volume s := by
  have hi:=twice_column N b b₁ b₂ hb h₁ h₂ s hc he C R seed B τ t hne Q hQ k hslot Bp υ v hz₁ hz₂ I hI
  have hh:1≤geometry N b b₁ b₂*(CommonRows.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)):=
    (norm_ge_one I hi.1).trans hi.2.2
  have hd:0<(C.absNorm:ℝ)*(Q.absNorm:ℝ)^k:=mul_pos
    (zero_lt_one.trans_le (norm_ge_one C (allocation_ne s C B)))
    (pow_pos (zero_lt_one.trans_le (norm_ge_one Q hQ)) k)
  rw [←mul_div_assoc] at hh
  have hn:=(le_div_iff₀ hd).mp hh
  simp only [one_mul] at hn
  refine ⟨hn,?_⟩
  rw [puncture_norm]
  nlinarith [mul_le_mul_of_nonneg_left hn (show (0:ℝ)≤R.absNorm by positivity)]

end OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.live_puncture_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildSourceCaps.live_puncture_bound
