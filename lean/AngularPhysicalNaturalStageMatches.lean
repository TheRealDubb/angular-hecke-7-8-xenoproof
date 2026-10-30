import AngularPhysicalNaturalSourceInput
import AngularPhysicalAllocatedRayMatches
import OAI.NumberTheory.DirichletL.Energy.NaturalInputMatches
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.NaturalStage
open PlainRows PlainRows.CommonRows RelativePrime InductionEnergy EnergyState
open HeckePrimeAnnular CenteredMomentPrimeSlot CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyNaturalInputMatches
  (profile profile_support profile_zero profile_norm profileBound profileBound_ge_one norm_profile_le)
local notation "O" => ActualEisensteinCubic.O
section Input
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (Q : Ideal O) [NeZero Q]
local instance : Finite (O ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne Q)
variable (H : Subgroup (O ⧸ Q)ˣ) (hH : RayOrthogonality.globalUnits Q ≤ H)
variable (η₀ : AngularCharacter) (θ : ι → RayQuotient.Characters Q H)
variable (W : ℝ → ℂ) (hW : Continuous W)
variable (aslot bslot lo hi : ℝ) (haslot : 0 < aslot)
variable (hWs : Function.support W ⊆ Set.Icc aslot bslot)
variable (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)
variable {angularOrder:ℕ} {Z Bmask bΦ a b : ℝ}
variable (state : NaturalState angularOrder Z Bmask bΦ) (p : Profiles a b) (ha : 0 < a)
variable (t X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
variable (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hsame : Y₁ * Y₂ = X₁ * X₂)

def input : Input ι :=
  PlainRows.CommonRows.naturalInput state p ha
    (fun i => primePool Q H bslot (Z^(w i)))
    (fun _ _ hI => (Finset.mem_filter.mp hI).2.1)
    (fun i => rayRelativeCharacter Q H hH η₀ (θ i))
    (fun i => profile W (σ i) (freq i)) (fun i => Z^(w i))
    (fun _ => profileBound W hW aslot bslot lo hi haslot hWs)
    (fun _ => Real.rpow_pos_of_pos (zero_lt_one.trans_le state.base_ge_one) _)
    (fun _ => profileBound_ge_one W hW aslot bslot lo hi haslot hWs)
    aslot bslot haslot (fun i => profile_support W aslot bslot hWs (σ i) (freq i))
    (fun i => norm_profile_le W hW aslot bslot lo hi haslot hWs (σ i) (hσ i) (freq i))
    t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame

local notation "inp" => input Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame

theorem input_matches (htype:state.character.k=η₀.k) :
    PlainRows.AllocatedRayDictionary.Matches Q H hH inp η₀ θ w σ freq W bslot Z := by
  exact ⟨htype,fun _ _=>rfl,fun _ _=>rfl,fun _=>rfl,fun _=>rfl⟩

lemma lower_eq : (inp).lower = aslot := rfl
lemma upper_eq : (inp).upper = bslot := rfl
lemma slot_control_eq (i : ι) :
    (inp).M i = profileBound W hW aslot bslot lo hi haslot hWs := rfl
lemma character_eq : (inp).η = state.character := rfl
lemma mask_eq : (inp).m = state.mask := rfl
lemma height_eq : (inp).t = t := rfl
lemma first_rectangle_eq : (inp).X₁ = X₁ ∧ (inp).X₂ = X₂ := ⟨rfl, rfl⟩
lemma second_rectangle_eq : (inp).Y₁ = Y₁ ∧ (inp).Y₂ = Y₂ := ⟨rfl, rfl⟩

theorem coefficient_eq (i : ι) (I : Ideal O) :
    (inp).toData.coefficient i I =
      (rayRelativeCharacter Q H hH η₀ (θ i)).idealHom I *
        annularWeight W (Z^(w i)) (σ i) (freq i) I := rfl

theorem positive_row_eq (z : O) :
    positiveSlotRow (inp).η state.mask 1 z (inp).W₁ (inp).W₂ (inp).slots
      (inp).toData.coefficient (inp).P (inp).t (inp).X₁ (inp).X₂ =
    positiveSlotRow state.character state.mask 1 z (p.profile 0) (p.profile 1)
      (fun i => primePool Q H bslot (Z^(w i)))
      (fun i I => (rayRelativeCharacter Q H hH η₀ (θ i)).idealHom I *
        annularWeight W (Z^(w i)) (σ i) (freq i) I)
      (fun i => Z^(w i)) t X₁ X₂ := rfl

theorem energy_eq :
    energy (inp).η state.mask 1 (inp).t (inp).W₁ (inp).W₂ (inp).slots
      (inp).toData.coefficient (inp).P (inp).X₁ (inp).X₂
      state.radial.keep state.radial.profile state.radial.scale =
    energy state.character state.mask 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool Q H bslot (Z^(w i)))
      (fun i I => (rayRelativeCharacter Q H hH η₀ (θ i)).idealHom I *
        annularWeight W (Z^(w i)) (σ i) (freq i) I)
      (fun i => Z^(w i)) X₁ X₂
      state.radial.keep state.radial.profile state.radial.scale := rfl

theorem reference_energy_eq :
    energy (inp).η state.mask 1 (inp).t (inp).W₁ (inp).W₂ (inp).slots
      (inp).toData.coefficient (inp).P (inp).Y₁ (inp).Y₂
      state.radial.keep state.radial.profile state.radial.scale =
    energy state.character state.mask 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool Q H bslot (Z^(w i)))
      (fun i I => (rayRelativeCharacter Q H hH η₀ (θ i)).idealHom I *
        annularWeight W (Z^(w i)) (σ i) (freq i) I)
      (fun i => Z^(w i)) Y₁ Y₂
      state.radial.keep state.radial.profile state.radial.scale := rfl

end Input

end OAI.SevenEighths.Angular.NaturalStage

#print axioms OAI.SevenEighths.Angular.NaturalStage.input_matches
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalStage.input_matches

#print axioms OAI.SevenEighths.Angular.NaturalStage.lower_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalStage.lower_eq

#print axioms OAI.SevenEighths.Angular.NaturalStage.upper_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalStage.upper_eq

#print axioms OAI.SevenEighths.Angular.NaturalStage.slot_control_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalStage.slot_control_eq

#print axioms OAI.SevenEighths.Angular.NaturalStage.character_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalStage.character_eq

#print axioms OAI.SevenEighths.Angular.NaturalStage.mask_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalStage.mask_eq

#print axioms OAI.SevenEighths.Angular.NaturalStage.height_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalStage.height_eq

#print axioms OAI.SevenEighths.Angular.NaturalStage.first_rectangle_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalStage.first_rectangle_eq

#print axioms OAI.SevenEighths.Angular.NaturalStage.second_rectangle_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalStage.second_rectangle_eq

#print axioms OAI.SevenEighths.Angular.NaturalStage.coefficient_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalStage.coefficient_eq

#print axioms OAI.SevenEighths.Angular.NaturalStage.positive_row_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalStage.positive_row_eq

#print axioms OAI.SevenEighths.Angular.NaturalStage.energy_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalStage.energy_eq

#print axioms OAI.SevenEighths.Angular.NaturalStage.reference_energy_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalStage.reference_energy_eq
