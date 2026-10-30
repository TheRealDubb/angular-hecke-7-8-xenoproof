import AngularPhysicalSecondBoundedProfileZero

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
theorem smooth_subset_source_second_zero_energy {α : Type*} (F : Finset α)
    (Wslot : α→ℝ→ℂ) (W₁ W₂ : ℝ→ℂ) (a b : α→ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈F,0<a j) (hb : ∀ j∈F,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j∈F,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈F,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ J : Finset α,J⊆F →
      ∀ (η : AngularCharacter) (t : ℝ) (R : Ideal O) (ν : α→Ideal O→ℂ),
      (∀ j∈J,∀ I,‖ν j I‖≤1) → ∀ (P : α→ℝ)
      (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 → s≠0 →
      X₁*X₂=T → Y₁*Y₂=T →
      ∀ (pools : (J⊕Fin 2)→Finset (Ideal O)) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ),
      let S := Fintype.piFinset pools
      let Traw := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j)
      let Y := (∏ j∈J,b j)*b₁*b₂*Traw
      let E := sourceSecondZero (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R (fun j : J=>ν j.val)
          (fun j : J=>Wslot j.val) (fun j : J=>P j.val) W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) η t
      (Y<1 → E=0) ∧
        ‖(((K:ℂ)*EisensteinSchwartzPoisson.paperRadialFourier Φ 0)/(Traw:ℂ))*E‖≤
          C*‖(K:ℂ)*EisensteinSchwartzPoisson.paperRadialFourier Φ 0‖*Traw^ε/(Ideal.absNorm s:ℝ) := by
  choose D hD hDb hz hsb using fun j : F => smooth_annular_bound
    (Wslot j.val) (a j.val) (b j.val) (ha j.val j.property)
    (hsSlot j.val j.property) (hWslot j.val j.property)
  obtain ⟨D₁,hD₁,hDb₁,hz₁,hsb₁⟩ := smooth_annular_bound W₁ a₁ b₁ ha₁ hs₁ hW₁
  obtain ⟨D₂,hD₂,hDb₂,hz₂,hsb₂⟩ := smooth_annular_bound W₂ a₂ b₂ ha₂ hs₂ hW₂
  let Dmax := 1+D₁+D₂+∑ j : F,D j
  let bmax := 1+b₁+b₂+∑ j : F,b j.val
  have hDs : 0≤∑ j : F,D j := Finset.sum_nonneg (fun j _=>hD j)
  have hbs : 0≤∑ j : F,b j.val := Finset.sum_nonneg (fun j _=>hb j.val j.property)
  have hDmax : 0≤Dmax := by dsimp only [Dmax];linarith
  have hbmax : 0≤bmax := by dsimp only [bmax];linarith
  have hD₁max : D₁≤Dmax := by dsimp only [Dmax];linarith
  have hD₂max : D₂≤Dmax := by dsimp only [Dmax];linarith
  have hb₁max : b₁≤bmax := by dsimp only [bmax];linarith
  have hb₂max : b₂≤bmax := by dsimp only [bmax];linarith
  have hDj (j : F) : D j≤Dmax := by
    have h := Finset.single_le_sum (fun k (_ : k∈(Finset.univ : Finset F))=>hD k) (Finset.mem_univ j)
    dsimp only [Dmax]
    linarith
  have hbj (j : F) : b j.val≤bmax := by
    have h := Finset.single_le_sum (fun k (_ : k∈(Finset.univ : Finset F))=>hb k.val k.property) (Finset.mem_univ j)
    dsimp only [bmax]
    linarith
  obtain ⟨C,hC,hbound⟩ := bounded_profile_second_zero_energy F.card ε hε Dmax bmax hDmax hbmax
  refine ⟨C,hC,?_⟩
  intro J hJ η t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY pools Φ K S Traw Y E
  let β := profileCoefficient R (fun j : J=>ν j.val) (fun j : J=>Wslot j.val) (fun j : J=>P j.val)
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hcard : Fintype.card J≤F.card := by simpa only [Fintype.card_coe] using Finset.card_le_card hJ
  have hh := hbound hcard η t R (fun j : J=>ν j.val) (fun j I=>hν j.val j.property I)
    (fun j : J=>Wslot j.val) (fun j : J=>P j.val) W₁ W₂
    (fun j x=>(hDb ⟨j.val,hJ j.property⟩ x).trans (hDj ⟨j.val,hJ j.property⟩))
    (fun x=>(hDb₁ x).trans hD₁max) (fun x=>(hDb₂ x).trans hD₂max)
    (fun j=>hz ⟨j.val,hJ j.property⟩) hz₁ hz₂
    (fun j x hx=>(hsb ⟨j.val,hJ j.property⟩ x hx).trans (hbj ⟨j.val,hJ j.property⟩))
    (fun x hx=>(hsb₁ x hx).trans hb₁max) (fun x hx=>(hsb₂ x hx).trans hb₂max)
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j=>hP j.val j.property)
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY S
  dsimp only at hh
  rw [Finset.prod_coe_sort] at hh
  refine ⟨?_,hh.2 ((K:ℂ)*EisensteinSchwartzPoisson.paperRadialFourier Φ 0)⟩
  intro hsmall
  apply sourceSecondZero_eq_zero_of_subunit _ _ η t Y hsmall
  intro I hI hn
  obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
  have hN := profileCoefficient_product_bound R (fun j : J=>ν j.val)
    (fun j : J=>Wslot j.val) (fun j : J=>P j.val) (fun j : J=>b j.val)
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j=>hP j.val j.property)
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY (fun j=>hz ⟨j.val,hJ j.property⟩) hz₁ hz₂
    (fun j=>hsb ⟨j.val,hJ j.property⟩) hsb₁ hsb₂ v hv0
  rw [←he]
  exact hN.2.trans_eq (by rw [Finset.prod_coe_sort,Finset.prod_coe_sort];dsimp only [Y,Traw];ring)

end OAI.SevenEighths.Angular.PlainRows.SecondSource

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.smooth_subset_source_second_zero_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.smooth_subset_source_second_zero_energy
