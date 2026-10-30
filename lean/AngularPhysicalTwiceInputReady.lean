import AngularPhysicalInputReadiness

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission
open CommonRows ChildInputs ChildSourceCaps FirstAnnularInput
open CanonicalQuadraticSieve CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
open CenteredMomentSectorLocalization
open CenteredMomentFirstSecondInputGates (exponent)
open CenteredMomentAmplificationChildSourceCaps
  (geometry geometry_ge_one norm_ge_one puncture_norm eventual_geometry polynomial_caps)
local notation "O" => ActualEisensteinCubic.O
local instance AngularTwiceInputReadyDecEq {κ:Type*} : DecidableEq κ := Classical.decEq _
theorem eventually_twice_ready (N:ℕ)(b b₁ b₂ ε:ℝ)
    (hb:1≤b)(hb₁:1≤b₁)(hb₂:1≤b₂)(hε:0<ε):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤N → Endpoints b b₁ b₂ s →
    ∀(C R seed:Ideal O)(B:actualAllocations s.pools C)(τ:AngularCharacter)(t:ℝ),
    R≠0 → frozenCoefficient B.val C R s.ν s.W s.P≠0 →
    ∀(Q:Ideal O),Q≠0 → ∀k:ℕ,
    (∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)→
    ∀(Bp:actualAllocations (child s C R B τ t).pools (Q^k))(υ:AngularCharacter)(v K A D P q ξ:ℝ),
    0<K → 0≤ξ → s.W₁ 0=0 → s.W₂ 0=0 →
    volume s≤Z^A → K⁻¹≤Z^D → (R.absNorm:ℝ)≤Z^P → (υ.modulus.absNorm:ℝ)≤Z^q →
    (∃I:Ideal O,(original (twiceChild s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed).beta I≠0)→
    Ready (twiceChild s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) K Z ξ (exponent A D P q ε ξ):=by
  filter_upwards [eventual_twice_caps N b b₁ b₂ ε hb hb₁ hb₂ hε,
    eventual_live_puncture N b b₁ b₂ ε hb hb₁ hb₂ hε] with Z hc hp
  refine ⟨hc.1,?_⟩
  intro ι _ s hs he C R seed B τ t hR hB Q hQ k hslot Bp υ v K A D P q ξ
    hK hξ hz₁ hz₂ hV hKi hRN hυ hlive
  have hh:=hc.2 s hs he C R B τ t hB Q hQ k hslot Bp υ v K A D ξ hK hV hKi
  have hr:=hp.2 s hs he C R seed B τ t hB Q hQ k hslot Bp υ v A P hz₁ hz₂ hV hRN hlive
  have h₁:A+ε≤exponent A D P q ε ξ:=le_max_left _ _
  have h₂:2*A+D+ε+ξ/2≤exponent A D P q ε ξ:=
    (le_max_left _ _).trans (le_max_right _ _)
  have h₃:A+P+ε≤exponent A D P q ε ξ:=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h₄:q≤exponent A D P q ε ξ:=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hpow {x y:ℝ}(h:x≤y):Z^x≤Z^y:=Real.rpow_le_rpow_of_exponent_le hc.1.le h
  refine ⟨mul_ne_zero (mul_ne_zero hR (allocation_ne s C B)) (pow_ne_zero k hQ),hK,
    hh.1.trans (hpow h₁),hh.2.1,hh.2.2.1.trans (hpow h₁),
    hυ.trans (hpow h₄),hr.trans (hpow h₃),hh.2.2.2.1,
    hh.2.2.2.2.1.trans (hpow ((by linarith : 2*A+D+ε≤2*A+D+ε+ξ/2).trans h₂)),
    hh.2.2.2.2.2.1,hh.2.2.2.2.2.2.trans (hpow h₂)⟩

end OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.eventually_twice_ready
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.eventually_twice_ready
