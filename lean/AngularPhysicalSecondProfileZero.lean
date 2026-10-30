import AngularPhysicalSecondTupleZero

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.PlainRows.SecondSource
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentLiveDomain
open CenteredMomentOriginalChildEnergy CenteredMomentFirstSectors CenteredMomentCommonSectors
open IdealMobiusDivisorSum ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentFourier CenteredMomentPoisson CenteredMomentSupportedCorrelation
open CenteredMomentRowNorm CenteredMomentSecondDiagonal
open CenteredMomentSecondSourceEnergy (secondSourceKernel)
open CenteredMomentSecondSourcePoisson (secondSourceKernel_poisson)
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceZeroEnergy CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceSecondZeroEnergy
  (secondZeroEnergy_filter sourceGenerator_span sourceGenerator_primary sourceGenerator_injective
   profileCoefficient_dvd)
local notation "O" => ActualEisensteinCubic.O
theorem profile_second_zero_energy (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (η : AngularCharacter) (t : ℝ) (R : Ideal O) (ν : ι→Ideal O→ℂ),
      (∀ j I,‖ν j I‖≤1) → ∀ (Wslot : ι→ℝ→ℂ) (P D b : ι→ℝ)
      (W₁ W₂ : ℝ→ℂ) (D₁ D₂ b₁ b₂ : ℝ),
      (∀ j,0≤D j) → 0≤D₁ → 0≤D₂ → (∀ j,0≤b j) → 0≤b₁ → 0≤b₂ →
      (∀ j x,‖Wslot j x‖≤D j) → (∀ x,‖W₁ x‖≤D₁) → (∀ x,‖W₂ x‖≤D₂) →
      (∀ j,Wslot j 0=0) → W₁ 0=0 → W₂ 0=0 →
      (∀ j x,Wslot j x≠0→x≤b j) → (∀ x,W₁ x≠0→x≤b₁) → (∀ x,W₂ x≠0→x≤b₂) →
      ∀ (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 → s≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Tuple ι),
      let Traw := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)
      let L := (∏ j,b j)*b₁*b₂
      let E := sourceSecondZero (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) η t
      (L*Traw<1 → E=0) ∧ ∀ κ : ℂ,
        ‖(κ/(Traw:ℂ))*E‖≤C*‖κ‖*(2*D₁*D₂*(∏ j,D j))^2*(1+L)^(1+ε)*Traw^ε/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := normalized_tuple_second_zero_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ hi η t R ν hν Wslot P D b W₁ W₂ D₁ D₂ b₁ b₂
    hD hD₁ hD₂ hb hb₁ hb₂ hslot h₁ h₂ hz hz₁ hz₂ hs hs₁ hs₂
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY S Traw L E
  let β := profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hβ (v : Tuple ι) : ‖β v‖≤2*D₁*D₂*(∏ j,D j) :=
    profileCoefficient_norm_le R ν hν Wslot P D W₁ W₂ D₁ D₂ hD hD₁ hD₂
      hslot h₁ h₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hn₁ : (0:ℝ)<Ideal.absNorm B₁ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₁)
  have hn₂ : (0:ℝ)<Ideal.absNorm B₂ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₂)
  have hraw : 0<Traw := mul_pos (div_pos hT (mul_pos hn₁ hn₂)) (Finset.prod_pos (fun j _=>hP j))
  have hL : 0≤L := mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun j _=>hb j)) hb₁) hb₂
  have hN (v : Tuple ι) (hv : β v≠0) : (Ideal.absNorm (finiteTupleProduct v):ℝ)≤L*Traw := by
    have hh := profileCoefficient_product_bound R ν Wslot P b W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s
      hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hz hz₁ hz₂ hs hs₁ hs₂ v hv
    exact hh.2.trans_eq (by dsimp only [L,Traw];ring)
  refine ⟨?_,?_⟩
  · intro hsmall
    apply sourceSecondZero_eq_zero_of_subunit _ _ η t (L*Traw) hsmall
    intro I hI hn
    obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
    rw [←he]
    exact hN v hv0
  · exact (hbound hi S β η t (2*D₁*D₂*(∏ j,D j)) (1+L) Traw
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hD₁) hD₂) (Finset.prod_nonneg (fun j _=>hD j)))
      (by linarith) hraw (fun v _ _=>hβ v) s hsz
      (fun v _ hv=>profileCoefficient_dvd R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v hv)
      (fun v _ hv=>(hN v hv).trans (mul_le_mul_of_nonneg_right (by linarith : L≤1+L) hraw.le))).2

end OAI.SevenEighths.Angular.PlainRows.SecondSource

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.profile_second_zero_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.profile_second_zero_energy
