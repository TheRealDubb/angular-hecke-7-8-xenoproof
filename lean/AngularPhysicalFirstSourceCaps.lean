import AngularPhysicalAmplifiedRayMatches
import AngularPhysicalAmplifiedRadicalFamily
import AngularPhysicalSecondInputSupport
import AngularPhysicalActiveErrorReady
import AngularPhysicalInputParentCapacity
import OAI.NumberTheory.DirichletL.Energy.FirstLiveAdmission

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
local instance angularSuccessorSourceCapsDecEq {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
theorem fixed_pair_caps (η : AngularCharacter) (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter)
    (F : FixedPair η C D hC E ξ₁ ξ₂) :
    (F.left.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2 ∧
    (F.right.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2 := by
  have h:=original_factor_caps C D hC E
  have hb : fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2≤
      fixedPresentationCost*(η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2 := by
    have hf:=fixedPresentationCost_pos.le
    nlinarith [mul_le_mul h.1 h.2 (sq_nonneg _) (Nat.cast_nonneg C.absNorm),
      mul_nonneg hf (Nat.cast_nonneg η.modulus.absNorm)]
  exact ⟨F.conductor_caps.1.trans hb,F.conductor_caps.2.trans hb⟩

theorem radical_once_cap (ρ υ : AngularCharacter) (χ : RayCharacter) (p : O) (hp : p≠0) (k : ℕ)
    (hυ : υ.modulus.absNorm≤radicalBound (childCharacter ρ χ) fixedBadMask p k) :
    (υ.modulus.absNorm:ℝ)≤rayCost*(ρ.modulus.absNorm:ℝ)*(Ideal.span {p}).absNorm := by
  have hP : (1:ℕ)≤(Ideal.span {p}).absNorm := Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp))
  have ht : (if k=0 then 1 else (Ideal.span {p}).absNorm)≤(Ideal.span {p}).absNorm := by
    split_ifs <;> omega
  have hr:=SecondFamily.child_modulus_bound ρ χ
  have hn : υ.modulus.absNorm≤
      (ρ.modulus.absNorm*(Ideal.span {(12:O)}).absNorm)*
      (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*(Ideal.span {p}).absNorm := by
    apply hυ.trans
    unfold radicalBound
    gcongr
  have hh : (υ.modulus.absNorm:ℝ)≤
      ((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
      (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*(Ideal.span {p}).absNorm := by
    exact_mod_cast hn
  convert hh using 1 ; unfold rayCost fixedPresentationCost ; ring

theorem fixed_error_cap (η : AngularCharacter) (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter)
    (F : FixedPair η C D hC E ξ₁ ξ₂) (ρ υ : AngularCharacter)
    (hρ : ρ=F.left ∨ ρ=F.right) (χ : RayCharacter) (p : O) (hp : p≠0) (k : ℕ)
    (hυ : υ.modulus.absNorm≤radicalBound (childCharacter ρ χ) fixedBadMask p k) :
    (υ.modulus.absNorm:ℝ)≤(rayCost*fixedPresentationCost)*
      (η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2*(Ideal.span {p}).absNorm := by
  have hf:=fixed_pair_caps η C D hC E ξ₁ ξ₂ F
  have hr : (ρ.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2 := by
    rcases hρ with rfl|rfl
    · exact hf.1
    · exact hf.2
  apply (radical_once_cap ρ υ χ p hp k hυ).trans
  have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr rayCost_nonneg)
    (Nat.cast_nonneg (Ideal.span {p}).absNorm)
  convert hh using 1 ; ring

theorem eventually_caps (ε : ℝ) (hε : 0<ε) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀η: AngularCharacter,∀(C D:Ideal O)(hC:Supported C),
    ∀(E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayCharacter)(F:FixedPair η C D hC E ξ₁ ξ₂),
    ∀q B:ℝ,(η.modulus.absNorm:ℝ)≤Z^q→(C.absNorm:ℝ)≤Z^B→
    (F.left.modulus.absNorm:ℝ)≤Z^(q+2*B+ε) ∧
    (F.right.modulus.absNorm:ℝ)≤Z^(q+2*B+ε) ∧
    ∀(ρ υ: AngularCharacter), (ρ=F.left∨ρ=F.right)→∀(χ:RayCharacter)(p:O),p≠0→
    ∀(k:ℕ)(r:ℝ),υ.modulus.absNorm≤radicalBound (childCharacter ρ χ) fixedBadMask p k→
    ((Ideal.span {p}).absNorm:ℝ)≤Z^r→(υ.modulus.absNorm:ℝ)≤Z^(q+2*B+r+ε) := by
  have he := (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε))
    (max fixedPresentationCost (rayCost*fixedPresentationCost))
  filter_upwards [he,eventually_gt_atTop (1:ℝ)] with Z hconst hZ
  refine ⟨hZ,?_⟩
  intro η C D hC E ξ₁ ξ₂ F q B hη hCcap
  have hz : 0<Z:=zero_lt_one.trans hZ
  have hm:=fixed_pair_caps η C D hC E ξ₁ ξ₂ F
  have hb : fixedPresentationCost*(η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2≤Z^(q+2*B+ε) := by
    calc
      _≤Z^ε*Z^q*(Z^B)^2 := by
        gcongr
        exact (le_max_left _ _).trans hconst
      _=_ := by rw [←Real.rpow_natCast,←Real.rpow_mul hz.le,←Real.rpow_add hz,←Real.rpow_add hz];congr 1;ring
  refine ⟨hm.1.trans hb,hm.2.trans hb,?_⟩
  intro ρ υ hρ χ p hp k r hυ hP
  apply (fixed_error_cap η C D hC E ξ₁ ξ₂ F ρ υ hρ χ p hp k hυ).trans
  calc
    _≤Z^ε*Z^q*(Z^B)^2*Z^r := by
      gcongr
      exact (le_max_right _ _).trans hconst
    _=_ := by rw [←Real.rpow_natCast,←Real.rpow_mul hz.le,←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz];congr 1;ring


end OAI.SevenEighths.Angular.FirstPhysicalAdmission

#print axioms OAI.SevenEighths.Angular.FirstPhysicalAdmission.fixed_pair_caps
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalAdmission.fixed_pair_caps

#print axioms OAI.SevenEighths.Angular.FirstPhysicalAdmission.radical_once_cap
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalAdmission.radical_once_cap

#print axioms OAI.SevenEighths.Angular.FirstPhysicalAdmission.fixed_error_cap
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalAdmission.fixed_error_cap

#print axioms OAI.SevenEighths.Angular.FirstPhysicalAdmission.eventually_caps
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalAdmission.eventually_caps
