import AngularPhysicalSharpInput
noncomputable section
set_option maxHeartbeats 1000000
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.AmplifiedRadical
open AngularRowClosure ChildRows CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentAmplificationShortening CenteredMomentFixedRay
open CenteredMomentAmplificationGlobal
open CenteredMomentSourceRow CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceSmoothedAllocation CenteredMomentGaussNormalization
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationErrorPool CenteredMomentAmplificationSourceDomain
open CenteredMomentAmplificationChildEnergy CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationLiveMask CenteredMomentAddedZeroUniform
open CenteredMomentSourceProfileMass CenteredMomentSourceMass CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationFamily
  (amplificationPhase amplificationPhase_expansion amplificationPhase_norm)
open CenteredMomentAmplificationActiveFamily (actual_error_energy_active)
local notation "O" => ActualEisensteinCubic.O
local instance angularSuccessorAllocationPowerSumDecEq {ι:Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

open PlainRows PlainRows.Amplification PlainRows.ChildInputs
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationEligibility CenteredMomentPrimeElements
open Filter
open CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstScale
open CenteredMomentPrimePool
open PlainRows.CommonRows PlainRows.FirstAnnularInput
open SecondSourcePower
open CenteredMomentCommonProfile CenteredMomentAmplificationAllocationCost
open CenteredMomentSecondHeightFamily
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _
lemma child_mass_eq (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (B : actualAllocations s.pools (Q^k)) (τ : AngularCharacter) (t : ℝ) :
    mass (child s (Q^k) R B τ t)=mass s := by
  change (∏i:liveIndices B.val,s.M i.val)=∏i,s.M i
  rw [Finset.prod_coe_sort,prime_slots_live s Q hQ k hslot B]

lemma allocations_card (s : Input ι) (Q : Ideal O) (hQ : Prime Q) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) :
    Fintype.card (actualAllocations s.pools (Q^k))≤k+1 := by
  simpa only [Fintype.card_coe] using actual_amplification_allocations_card s.pools Q hQ k
    (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩)

theorem power_sum_eq (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (τ : actualAllocations s.pools (Q^k)→AngularCharacter)
    (t : actualAllocations s.pools (Q^k)→ℝ) (α : ℝ) :
    (∑B:actualAllocations s.pools (Q^k),
      volume (child s (Q^k) R B (τ B) (t B))^α*mass (child s (Q^k) R B (τ B) (t B))^2)=
    Fintype.card (actualAllocations s.pools (Q^k))*
      (volume s/(Q.absNorm:ℝ)^k)^α*mass s^2 := by
  simp_rw [child_volume s Q hQ k hslot,child_mass_eq s Q hQ k hslot]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

theorem power_sum_le (s : Input ι) (Q : Ideal O) (hQ : Prime Q) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (τ : actualAllocations s.pools (Q^k)→AngularCharacter)
    (t : actualAllocations s.pools (Q^k)→ℝ) (α : ℝ) :
    (∑B:actualAllocations s.pools (Q^k),
      volume (child s (Q^k) R B (τ B) (t B))^α*mass (child s (Q^k) R B (τ B) (t B))^2)≤
    ((k+1:ℕ):ℝ)*(volume s/(Q.absNorm:ℝ)^k)^α*mass s^2 := by
  rw [power_sum_eq s Q hQ.ne_zero k hslot R τ t α]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_right _
    (Real.rpow_nonneg (div_nonneg (volume_pos s).le (pow_nonneg (Nat.cast_nonneg _) k)) α)
  exact_mod_cast allocations_card s Q hQ k hslot

theorem budget_sum_le (s : Input ι) (Q : Ideal O) (hQ : Prime Q) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (τ : actualAllocations s.pools (Q^k)→AngularCharacter)
    (t : actualAllocations s.pools (Q^k)→ℝ)
    (n : ℕ) (a α : Fin n→ℝ) (ha : ∀j,0≤a j) :
    (∑B:actualAllocations s.pools (Q^k),
      (∑j,a j*volume (child s (Q^k) R B (τ B) (t B))^(α j))*
        mass (child s (Q^k) R B (τ B) (t B))^2)≤
    ((k+1:ℕ):ℝ)*(∑j,a j*(volume s/(Q.absNorm:ℝ)^k)^(α j))*mass s^2 := by
  simp_rw [child_volume s Q hQ.ne_zero k hslot,child_mass_eq s Q hQ.ne_zero k hslot]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hs : 0≤∑j,a j*(volume s/(Q.absNorm:ℝ)^k)^(α j) :=
    Finset.sum_nonneg (fun j _=>mul_nonneg (ha j)
      (Real.rpow_nonneg (div_nonneg (volume_pos s).le (pow_nonneg (Nat.cast_nonneg _) k)) _))
  have hc : (Fintype.card (actualAllocations s.pools (Q^k)):ℝ)≤k+1 := by
    exact_mod_cast allocations_card s Q hQ k hslot
  calc
    _≤((k:ℝ)+1)*((∑j,a j*(volume s/(Q.absNorm:ℝ)^k)^(α j))*mass s^2) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hs (sq_nonneg _))
    _=_ := by push_cast;ring

theorem error_budget_sum_le (s : Input ι) (Q : Ideal O) (hQ : Prime Q) (k : ℕ)
    (hk : k=1 ∨ k=6 ∨ k=7)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (τ : actualAllocations s.pools (Q^k)→AngularCharacter)
    (t : actualAllocations s.pools (Q^k)→ℝ)
    (n : ℕ) (a α : Fin n→ℝ) (ha : ∀j,0≤a j) :
    (∑B:actualAllocations s.pools (Q^k),
      (∑j,a j*volume (child s (Q^k) R B (τ B) (t B))^(α j))*
        mass (child s (Q^k) R B (τ B) (t B))^2)≤
    8*(∑j,a j*(volume s/(Q.absNorm:ℝ)^k)^(α j))*mass s^2 := by
  apply (budget_sum_le s Q hQ k hslot R τ t n a α ha).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_right _
    (Finset.sum_nonneg (fun j _=>mul_nonneg (ha j)
      (Real.rpow_nonneg (div_nonneg (volume_pos s).le (pow_nonneg (Nat.cast_nonneg _) k)) _)))
  rcases hk with rfl|rfl|rfl <;> norm_num


end OAI.SevenEighths.Angular.AmplifiedRadical

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.child_mass_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.child_mass_eq

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.allocations_card
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.allocations_card

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.power_sum_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.power_sum_eq

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.power_sum_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.power_sum_le

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.budget_sum_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.budget_sum_le

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.error_budget_sum_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.error_budget_sum_le
