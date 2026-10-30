import AngularPhysicalSecondProfileZero

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
theorem bounded_profile_second_zero_energy (N : ℕ) (ε : ℝ) (hε : 0<ε)
    (D b : ℝ) (hD : 0≤D) (hb : 0≤b) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (η : AngularCharacter) (t : ℝ) (R : Ideal O) (ν : ι→Ideal O→ℂ),
      (∀ j I,‖ν j I‖≤1) → ∀ (Wslot : ι→ℝ→ℂ) (P : ι→ℝ) (W₁ W₂ : ℝ→ℂ),
      (∀ j x,‖Wslot j x‖≤D) → (∀ x,‖W₁ x‖≤D) → (∀ x,‖W₂ x‖≤D) →
      (∀ j,Wslot j 0=0) → W₁ 0=0 → W₂ 0=0 →
      (∀ j x,Wslot j x≠0→x≤b) → (∀ x,W₁ x≠0→x≤b) → (∀ x,W₂ x≠0→x≤b) →
      ∀ (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 → s≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Tuple ι),
      let Traw := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)
      let E := sourceSecondZero (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) η t
      (b^(Fintype.card ι+2)*Traw<1 → E=0) ∧ ∀ κ : ℂ,
        ‖(κ/(Traw:ℂ))*E‖≤C*‖κ‖*Traw^ε/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C₀,hC₀,hmain⟩ := profile_second_zero_energy N ε hε
  let B := 2*D*D*(1+D)^N
  let L := (1+b)^(N+2)
  let C := C₀*(1+B^2)*(1+L)^(1+ε)
  have hB : 0≤B := by dsimp [B];positivity
  have hL : 0≤L := by dsimp [L];positivity
  have hC : 0<C := mul_pos (mul_pos hC₀ (by positivity)) (Real.rpow_pos_of_pos (by linarith) _)
  refine ⟨C,hC,?_⟩
  intro ι _ hi η t R ν hν Wslot P W₁ W₂ hslot h₁ h₂ hz hz₁ hz₂ hs hs₁ hs₂
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY S Traw E
  have hTpos : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hraw0 : 0≤Traw := mul_nonneg (div_nonneg hTpos.le (by positivity))
    (Finset.prod_nonneg (fun j _=>(hP j).le))
  have hh := hmain hi η t R ν hν Wslot P (fun _=>D) (fun _=>b) W₁ W₂ D D b b
    (fun _=>hD) hD hD (fun _=>hb) hb hb hslot h₁ h₂ hz hz₁ hz₂ hs hs₁ hs₂
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY S
  dsimp only at hh
  simp only [Finset.prod_const,Finset.card_univ] at hh
  have heL : b^Fintype.card ι*b*b=b^(Fintype.card ι+2) := by
    rw [pow_add,pow_two];ring
  rw [heL] at hh
  refine ⟨hh.1,?_⟩
  intro κ
  have hBbound : 2*D*D*D^Fintype.card ι≤B := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (pow_le_pow_left₀ hD (by linarith) _).trans (pow_le_pow_right₀ (by linarith) hi)
  have hLbound : b^(Fintype.card ι+2)≤L :=
    (pow_le_pow_left₀ hb (by linarith) _).trans (pow_le_pow_right₀ (by linarith) (by omega))
  have hpow : (1+b^(Fintype.card ι+2))^(1+ε)≤(1+L)^(1+ε) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have hcoef : C₀*(2*D*D*D^Fintype.card ι)^2*(1+b^(Fintype.card ι+2))^(1+ε)≤C := by
    dsimp only [C]
    apply mul_le_mul _ hpow (by positivity) (by positivity)
    apply mul_le_mul_of_nonneg_left _ hC₀.le
    exact (pow_le_pow_left₀ (by positivity) hBbound 2).trans (by linarith)
  apply (hh.2 κ).trans
  calc
    _ = (C₀*(2*D*D*D^Fintype.card ι)^2*(1+b^(Fintype.card ι+2))^(1+ε))*
        (‖κ‖*Traw^ε/(Ideal.absNorm s:ℝ)) := by ring
    _ ≤ C*(‖κ‖*Traw^ε/(Ideal.absNorm s:ℝ)) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = _ := by ring

end OAI.SevenEighths.Angular.PlainRows.SecondSource

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.bounded_profile_second_zero_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.bounded_profile_second_zero_energy
