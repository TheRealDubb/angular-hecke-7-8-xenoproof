import AngularPhysicalFirstLiveSupport

noncomputable section
set_option maxHeartbeats 600000
open scoped Classical BigOperators SchwartzMap
open Filter
open OAI.SevenEighths.CenteredMomentEnergyBands (length)
open OAI.SevenEighths.CenteredMomentActiveSource
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
local instance angularSuccessorMainPacketDecEq {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
theorem eventually_main_packet (N : ℕ) (b b₁ b₂ l a A P : ℝ)
    (hb : 1 ≤ b) (hb₁ : 1 ≤ b₁) (hb₂ : 1 ≤ b₂)
    (hl : 0 < l) (ha : 0 < a) (hA : 0 ≤ A) (hP : 0 ≤ P) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
      ∀ s : Input ι, Fintype.card ι ≤ N → Endpoints b b₁ b₂ s → l ≤ s.lower →
      (∀ x, s.W₁ x ≠ 0 → a ≤ x) → (∀ x, s.W₂ x ≠ 0 → a ≤ x) →
      ∀ κ : ℝ, 1/6 ≤ κ → (∀ i, 1 ≤ s.P i) →
      length Z s.X₁ + length Z s.X₂ + 6*κ*(∑ i, Real.logb Z (s.P i)) ≤ A →
      (s.η.modulus.absNorm : ℝ) ≤ Z^A →
      ∀ R seed : Ideal O, R ≠ 0 → (R.absNorm : ℝ) ≤ Z^P → Squarefree seed →
      ∀ C D : Ideal O, ∀ hC : Supported C, ∀ hD : Supported D,
      (C,D) ∈ CenteredMomentFirstSectors.commonLabels
        (CenteredMomentSourceRow.supportedColumns (activeSource
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)))
        (CenteredMomentSourceRow.supportedColumns (activeSource
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed))) →
      ∀ E : Finset (CommonIndex C D), ∀ ξ₁ ξ₂ : RayCharacter,
      ∀ F : FixedPair s.η C D hC E ξ₁ ξ₂, ∀ τ : AngularCharacter, τ = F.left ∨ τ = F.right →
      ∀ K Csec Tsec σ ξ reserve : ℝ, 0 < K → 0 < Csec → 0 ≤ σ → 0 ≤ ξ → ξ ≤ 1 →
      0 ≤ reserve →
      Tsec ≤ Csec * firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E}) K (volume s) →
      ∀ rows : Finset O, ∀ W : 𝓢(ℝ,ℂ), ∀ n : Fin 4 → ℤ,
      Retained (frequencyRadius Tsec Z ξ) (n 1) →
      block s.η (fixedBadMask*idealGenerator R) 1 s.t
        (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)
        C D hC hD E rows W (fun _ => logAnnulus) K
        (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3)) ≠ 0 →
      ∀ side : Bool, ∀ B : actualAllocations s.pools (columnIdeal C D side), ∀ t : ℝ,
      frozenCoefficient B.val (columnIdeal C D side) R s.ν s.W s.P ≠ 0 →
      let Km := columnMainRadius C D E K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve side
      Ready (child s (columnIdeal C D side) R B τ t) (R*columnIdeal C D side) Km Z ξ (readyBudget A P) ∧
      (∀ I : Ideal O, coefficient (child s (columnIdeal C D side) R B τ t) (R*columnIdeal C D side) seed I ≠ 0 →
        lowerFactor N l a * volume (child s (columnIdeal C D side) R B τ t) ≤ (I.absNorm : ℝ)) := by
  filter_upwards [eventually_common_ready N b b₁ b₂ 1 hb hb₁ hb₂ (by norm_num),
    eventual_parent_radius N b b₁ b₂ hb hb₁ hb₂,
    eventually_caps 1 (by norm_num)] with Z hready hradius hchars
  refine ⟨hready.1, ?_⟩
  intro ι _ _ s hc he hs hW₁ hW₂ κ hκ hPs hcapacity hη R seed hR hRN hseed
    C D hC hD hlabel E ξ₁ ξ₂ F τ hτ K Csec Tsec σ ξ reserve hK hCsec hσ hξ hξ1
    hreserve hsec rows W n hn hblock side B t hB
  dsimp only
  have hz := hready.1
  have hV := original_volume_cap s Z κ A hz hκ hPs hcapacity
  have hH := hradius.2 s hc he A hV
  have hz₁ := lower_profile_zero s.W₁ a ha hW₁
  have hz₂ := lower_profile_zero s.W₂ a ha hW₂
  have hcdata := actual_common_gates s R seed hseed hz₁ hz₂ C D hlabel
  have hCN := hcdata.2.2.2.2.2.1.trans hH
  have hJN : ((columnIdeal C D side).absNorm : ℝ) ≤ Z^(A+1) := by
    cases side
    · exact hCN
    · exact hcdata.2.2.2.2.2.2.trans hH
  have ht := hchars.2 s.η C D hC E ξ₁ ξ₂ F A (A+1) hη hCN
  have htau : (τ.modulus.absNorm : ℝ) ≤ Z^(3*A+3) := by
    have hx : (τ.modulus.absNorm : ℝ) ≤ Z^(A+2*(A+1)+1) := by
      rcases hτ with rfl | rfl
      · exact ht.1
      · exact ht.2.1
    simpa only [show A+2*(A+1)+1 = 3*A+3 by ring] using hx
  have hE : Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E} ≠ 0 := by
    exact Ideal.span_singleton_eq_bot.not.mpr (primeSubsetGenerator_ne_zero _ _)
  have hne := first_block_active_rows_nonempty s.η (fixedBadMask*idealGenerator R) 1 s.t
    _ _ C D hC hD E rows W K n hblock
  have hrec := (active_row_reciprocals C D _ hE K (volume s) Z Csec Tsec ξ
    (Real.logb Z ((oppositeIdeal C D side).absNorm : ℝ))
    (Real.logb Z ((columnIdeal C D side).absNorm : ℝ)) σ reserve
    hK (volume_pos s) hz hCsec hσ hreserve hsec rows n hn hne 1 1).1
  have hKm : 0 < columnMainRadius C D E K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve side := by
    unfold columnMainRadius mainCommonRadius
    positivity
  have hKmInv : (columnMainRadius C D E K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve side)⁻¹ ≤ Z^(0 : ℝ) := by
    simpa only [columnMainRadius,nominalLog,Real.rpow_zero] using hrec
  have hr := hready.2 s hc he (columnIdeal C D side) R B τ t hR hB _ A 0 P (A+1) (3*A+3) ξ
    hKm hξ hV hKmInv hRN hJN htau
  exact ⟨ready_mono _ _ _ Z ξ _ _ hz.le (common_exponent_le A P ξ hA hP hξ1) hr,
    main_lower_support N l a hl ha s hc hs hW₁ hW₂ (columnIdeal C D side) R seed B τ t⟩


end OAI.SevenEighths.Angular.FirstPhysicalAdmission

#print axioms OAI.SevenEighths.Angular.FirstPhysicalAdmission.eventually_main_packet
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalAdmission.eventually_main_packet
