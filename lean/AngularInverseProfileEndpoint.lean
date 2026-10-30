import AngularInverseRowwiseEndpoint
import AngularFixedInverseProfiles
import AngularPhysicalCoefficientTransfer

/-! This theorem discharges the endpoint's RawMoment premises using actual
angular raw moments. The chosen angular order is fixed before every live height.
It is not the detector-count feedback or zero-free theorem. -/
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace OAI.SevenEighths.Angular.InverseAmplification
open OAI.SevenEighths.Angular.Dyadic InverseRows RawCompact
open HeckeInverseAmplification (FreeRow sourceExponent scaleProfile twistProfile logTest
  conjugate_profile_support conjugate_profile_smooth)
open HeckeDetectorCoefficientTransfer (orientedProfile)
open HeckeDetectorInverseFiberCount (inverseTest)

theorem fixed_profile_rowwise_endpoint (angularOrder : ℕ)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a b B : ℝ) (ha : 0<a) (hab : a≤b) (hB : 0<B)
    (hφs : Function.support φ⊆Ioo a b) (hφB : ∀ y,φ y≤B)
    (R ε : ℝ) (hR : 0≤R) (hε : 0<ε) :
    ∃ J : ℕ, ∃ U₀ : ℝ, 1<U₀ ∧
      ∀ data : RowData, data.η.k=(angularOrder:ℤ) → ∃ C : ℝ, 0<C ∧
      ∀ U : ℝ, U₀≤U → ∀ (r : ℝ) (rows : Finset FreeRow)
        (reverse : Bool) (tstar height : ℝ) (σ freq : FreeRow→ℝ),
      0≤r → r≤R → 0≤height →
      (∀ u∈rows, ((Ideal.span {u.val}).absNorm:ℝ)≤U) →
      (∀ u∈rows, σ u∈Icc (0:ℝ) 1) → (∀ u∈rows, freq u∈Icc (-height) height) →
      (∑ u∈rows, ‖polynomial (data.character ⟨u.val,u.property.1⟩) true
        (orientedProfile reverse (inverseTest U tstar r)) (U^r) (σ u) (freq u)‖^2) ≤
        C*(1+height)^J*U^(sourceExponent r+ε) := by
  obtain ⟨c,κ,K,hc,hc1,hκ,hK,he⟩ := no_slot_rowwise_endpoint M H hH S
    φ hφ hφc hφp hφ0 hφne a b B ha hab hB hφs hφB R ε hR hε
  obtain ⟨J,hprofiles⟩ := RawProfiles.fixed_raw_profiles angularOrder c κ hc hκ
  obtain ⟨U₁,hU₁⟩ := eventually_atTop.mp he
  refine ⟨J+1,max 2 U₁,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro data hk
  obtain ⟨A,hA,hraw⟩ := hprofiles data hk
  refine ⟨12*A*max 1 K,by positivity,?_⟩
  intro U hU r rows reverse tstar height σ freq hr hrR hheight hrows hσ hfreq
  have hUone : 1<U := lt_of_lt_of_le
    (lt_of_lt_of_le (by norm_num : (1:ℝ)<2) (le_max_left _ _)) hU
  have hUp : 0<U := zero_lt_one.trans hUone
  let V := orientedProfile reverse (inverseTest U tstar r)
  have hs : Function.support V⊆Icc (1/4:ℝ) (9/4) := by
    have hh := HeckeDetectorDyadicActual.inverse_profile_support (U^tstar) (U^r)
    cases reverse
    · exact hh
    · simpa only [V,orientedProfile,Bool.true_eq,ite_true,conjugate_profile_support,inverseTest] using hh
  have hV : ContDiff ℝ ∞ V := by
    have hh := HeckeDetectorDyadicActual.inverse_profile_smooth (U^tstar) (U^r)
    cases reverse
    · exact hh
    · exact conjugate_profile_smooth _ hh
  have hen := hU₁ U ((le_max_right _ _).trans hU) r data rows V (1/4) (9/4)
    (A*(1+height)^J) height σ freq hr hrR (by positivity) hheight
    (by norm_num) (by norm_num) hs hV hrows hσ hfreq
    (fun n hn s hs t ht => hraw reverse n hn U hUp tstar r s hs height t hheight ht)
  refine hen.trans ?_
  calc
    12*(1+height)*(A*(1+height)^J*K*U^(sourceExponent r+ε)) ≤
        12*(1+height)*(A*(1+height)^J*max 1 K*U^(sourceExponent r+ε)) := by
      gcongr
      exact le_max_right _ _
    _ = (12*A*max 1 K)*(1+height)^(J+1)*U^(sourceExponent r+ε) := by
      rw [pow_succ]
      ring

#print axioms fixed_profile_rowwise_endpoint
set_option pp.deepTerms true in
#check fixed_profile_rowwise_endpoint
end OAI.SevenEighths.Angular.InverseAmplification
