import AngularPhysicalFirstCommonReady

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace OAI.SevenEighths.Angular.FirstPhysicalAdmission
open CanonicalQuadraticSieve ConcreteTraceCRT ConcretePrimeRowBridge ActualEisensteinCubic
open PlainRows PlainRows.CommonRows PlainRows.ChildInputs PlainRows.ChildSourceCaps
open PlainRows.FirstSourceAdmission PlainRows.FirstAnnularInput PlainRows.FirstPhysical
open PlainRows.AmplifiedRayDictionary InputParentCapacity ChildRows
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentSourceMass CenteredMomentCanonicalFirst CenteredMomentFirstScale
open CenteredMomentSectorLocalization CenteredMomentSecondHeightFamily
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstPhysicalSource (fixedPresentationCost fixedPresentationCost_pos)
open CenteredMomentFirstSourceConductorCaps (original_factor_caps rayCost rayCost_nonneg)
open CenteredMomentFirstPhysicalDyadicRows (activeRows row_log_window)
open CenteredMomentFirstWholeKernel (windows)
open CenteredMomentFirstAmplifiedRadiusLower
open CenteredMomentEnergyFirstLiveAdmission (columnIdeal oppositeIdeal columnMainRadius columnErrorRadius
  readyBudget common_exponent_le error_exponent_le lower_profile_zero)
open CenteredMomentFirstSecondInputGates (commonExponent)
open CenteredMomentAmplificationChildSourceCaps (live_card_le geometry geometry_ge_one
  norm_ge_one eventual_geometry polynomial_caps)
open CenteredMomentSecondInputCapacitySource (lowerFactor)
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationActiveFactor
open CenteredMomentLogDyadic CenteredMomentRowNorm
open AmplifiedRadical
open SecondSourcePower (actual_lower_support)
open CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local instance angularSuccessorLiveSupportDecEq {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
theorem block_activeRows (η : AngularCharacter) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O→ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) :
    block η m A t S c C D hC hD E rows W (fun _=>logAnnulus) K
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) =
    block η m A t S c C D hC hD E (activeRows rows n) W (fun _=>logAnnulus) K
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  unfold block activeRows
  dsimp only
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hd : h∈dyadRows (n 1)
  · simp only [hd,ite_true]
  · have hw : dyadicWeight (n 1) (normValue h)=0 := by
      simpa only [mem_dyadRows,not_not] using hd
    simp only [hd,windows,row_log_window,hw,Complex.ofReal_zero,
      mul_zero,zero_mul,ite_self,Finset.sum_const_zero]

theorem first_block_active_rows_nonempty
    (η : AngularCharacter) (m A : O) (t : ℝ) (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (E : Finset (CommonIndex C D)) (rows : Finset O) (W : 𝓢(ℝ,ℂ))
    (K : ℝ) (n : Fin 4 → ℤ)
    (hne : block η m A t S c C D hC hD E rows W (fun _ => logAnnulus) K
      (dyadicScale (n 0)) (dyadicScale (n 1))
      (dyadicScale (n 2)) (dyadicScale (n 3)) ≠ 0) :
    (activeRows rows n).Nonempty := by
  by_contra h
  have he : activeRows rows n = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  apply hne
  rw [block_activeRows, he]
  simp only [block, Finset.sum_empty, mul_zero]

lemma ready_mono {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Input ι) (R : Ideal O)
    (K Z ξ B B' : ℝ) (hZ : 1 ≤ Z) (hB : B ≤ B')
    (h : Ready s R K Z ξ B) : Ready s R K Z ξ B' := by
  have hp := Real.rpow_le_rpow_of_exponent_le hZ hB
  exact ⟨h.puncture_ne,h.scale_pos,h.volume_cap.trans hp,h.source_nonneg,
    h.source_cap.trans hp,h.conductor_cap.trans hp,h.puncture_cap.trans hp,
    h.nominal_pos,h.nominal_cap.trans hp,h.frequency_pos,h.frequency_cap.trans hp⟩

theorem main_lower_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (l a : ℝ) (hl : 0 < l) (ha : 0 < a)
    (s : Input ι) (hc : Fintype.card ι ≤ N) (hs : l ≤ s.lower)
    (hW₁ : ∀ x, s.W₁ x ≠ 0 → a ≤ x) (hW₂ : ∀ x, s.W₂ x ≠ 0 → a ≤ x)
    (C R seed : Ideal O) (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ) :
    ∀ I : Ideal O, coefficient (child s C R B τ t) (R*C) seed I ≠ 0 →
      lowerFactor N l a * volume (child s C R B τ t) ≤ (I.absNorm : ℝ) := by
  intro I hI
  exact actual_lower_support N l a hl ha (child s C R B τ t)
    ((live_card_le B.val).trans hc) hs hW₁ hW₂ (R*C) seed I hI

theorem error_lower_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (l a : ℝ) (hl : 0 < l) (ha : 0 < a)
    (s : Input ι) (hc : Fintype.card ι ≤ N) (hs : l ≤ s.lower)
    (hW₁ : ∀ x, s.W₁ x ≠ 0 → a ≤ x) (hW₂ : ∀ x, s.W₂ x ≠ 0 → a ≤ x)
    (C R seed : Ideal O) (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : AngularCharacter) (v : ℝ) :
    ∀ I : Ideal O, coefficient (errorInput s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed I ≠ 0 →
      lowerFactor N l a * volume (errorInput s C R B τ t Q k Bp υ v) ≤ (I.absNorm : ℝ) := by
  intro I hI
  exact actual_lower_support N l a hl ha (errorInput s C R B τ t Q k Bp υ v)
    ((live_card_le Bp.val).trans ((live_card_le B.val).trans hc))
    hs hW₁ hW₂ ((R*C)*(Q^k)) seed I hI

theorem eventual_parent_radius (N : ℕ) (b b₁ b₂ : ℝ)
    (hb : 1 ≤ b) (hb₁ : 1 ≤ b₁) (hb₂ : 1 ≤ b₂) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
      ∀ s : Input ι, Fintype.card ι ≤ N → Endpoints b b₁ b₂ s →
      ∀ A : ℝ, volume s ≤ Z^A → sourceRadius s ≤ Z^(A+1) := by
  let G := b^N*b₁*b₂
  have hG : 1 ≤ G := by
    have hp : 1 ≤ b^N := one_le_pow₀ hb
    dsimp [G]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hp hb₁) hb₂
  filter_upwards [eventual_geometry G 1 hG (by norm_num)] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro ι _ _ s hc he A hV
  have hr := (radius_bound N b b₁ b₂ hb hb₁ hb₂ s hc he).2
  have hg : G ≤ Z := by simpa only [Real.rpow_one] using hZ.2.1
  apply hr.trans
  calc
    G * volume s ≤ Z * Z^A := mul_le_mul hg hV (volume_pos s).le (zero_lt_one.trans hZ.1).le
    _ = Z^(A+1) := by rw [Real.rpow_add_one (zero_lt_one.trans hZ.1).ne']; ring


end OAI.SevenEighths.Angular.FirstPhysicalAdmission

#print axioms OAI.SevenEighths.Angular.FirstPhysicalAdmission.block_activeRows
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalAdmission.block_activeRows

#print axioms OAI.SevenEighths.Angular.FirstPhysicalAdmission.first_block_active_rows_nonempty
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalAdmission.first_block_active_rows_nonempty

#print axioms OAI.SevenEighths.Angular.FirstPhysicalAdmission.ready_mono
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalAdmission.ready_mono

#print axioms OAI.SevenEighths.Angular.FirstPhysicalAdmission.main_lower_support
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalAdmission.main_lower_support

#print axioms OAI.SevenEighths.Angular.FirstPhysicalAdmission.error_lower_support
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalAdmission.error_lower_support

#print axioms OAI.SevenEighths.Angular.FirstPhysicalAdmission.eventual_parent_radius
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalAdmission.eventual_parent_radius
