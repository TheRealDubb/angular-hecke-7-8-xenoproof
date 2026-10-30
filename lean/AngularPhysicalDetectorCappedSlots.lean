import AngularPhysicalDetectorCappedRectangle

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.DetectorSource
open PlainRows ExceptionalRows AngularRowClosure ConcretePrimeRowBridge
open CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentCounting CenteredMomentTwist CenteredMomentLattice
open CenteredMomentHeckeSlots (whole_product_normalization)
local notation "O" => ActualEisensteinCubic.O
theorem detector_capped_slots_uniform (angularType : ℤ) (ε B : ℝ) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,Q≠0 → ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],∀Z : ℝ,1≤Z →
      ∀η : AngularCharacter,η.k=angularType → ∀m A z : O,m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^B → FixedInducingRow η Q m A z →
      ∀S : ι→Finset (Ideal O),∀β : ι→Ideal O→ℂ,∀p b M : ι→ℝ,
      (∀i,0<p i) → (∀i,0≤b i) → (∀i,0≤M i) →
      (∀i,∀P∈S i,‖β i P‖≤M i) → (∀i,∀P∈S i,β i P≠0 → (P.absNorm:ℝ)≤b i*p i) →
      ∀r₁ r₂ : Bool,∀j k : ℕ,j≤2 → k≤2 → ∀σ₁∈Set.Icc (0:ℝ) 1,∀σ₂∈Set.Icc (0:ℝ) 1,
      ∀t₁ t₂ h X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖centeredSlotRow η m A z (detectorSchwartz r₁ j σ₁ t₁) (detectorSchwartz r₂ k σ₂ t₂)
        S β p h X₁ X₂ Y₁ Y₂ T‖≤
        C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J*(∏i,128*b i*M i)*(Real.sqrt (T*∏i,p i)/max 1 L) := by
  obtain ⟨J,hJ⟩:=detector_capped_rectangle_uniform angularType ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro ι inst Z hZ η htype m A z hm hA hz hml hm2 hcond hex S β p b M hp hb hM hβ hN
    r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂ t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0<T:=hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hslots (i : ι) : ‖rowSlot η m A z (S i) (β i) h‖≤(128*b i*M i)*p i := by
    convert rowSlot_bound η m A z (S i) (β i) h (b i*p i) (M i)
      (mul_nonneg (hb i) (hp i).le) (hM i) (hβ i) (hN i) using 1 ; ring
  exact whole_product_normalization _ (fun i=>rowSlot η m A z (S i) (β i) h)
    (fun i=>128*b i*M i) p (C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J) T (max 1 L)
    (by positivity) hT (zero_lt_one.trans_le (le_max_left _ _))
    (fun i=>mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hM i)) hp hslots
    (hbound Z hZ η htype m A z hm hA hz hml hm2 hcond hex r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
      t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY)

end OAI.SevenEighths.Angular.DetectorSource

#print axioms OAI.SevenEighths.Angular.DetectorSource.detector_capped_slots_uniform
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.DetectorSource.detector_capped_slots_uniform
