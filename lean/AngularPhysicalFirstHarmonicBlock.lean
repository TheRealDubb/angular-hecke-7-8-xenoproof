import AngularPhysicalFirstAnnularBlock
import AngularPhysicalSecondSourceZero
import OAI.NumberTheory.DirichletL.Moments.FirstDivisorCommonBound

noncomputable section
set_option maxHeartbeats 1000000
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
universe u
namespace OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion CompletedGauss RayFourExpansion
open PlainRows PlainRows.CommonRows PlainRows.ChildInputs PlainRows.FirstPhysical
open CenteredMomentCommonSupport CenteredMomentCanonicalFirst CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentGaussEnergy CenteredMomentChildAssembly CenteredMomentMobiusRegroup
open CenteredMomentActiveSource CenteredMomentRowNorm CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalDyadicAssembly (Blocks effectiveScale)
open CenteredMomentFirstPhysicalSource (columns column_supported element element_span scalar
  inactiveWeight fixedPresentationCost fixedPresentationCost_pos)
open CenteredMomentFirstWholeKernel (windows)
open CenteredMomentFirstDiscardedEnergy (inactiveSubsets)
open CenteredMomentSecondRetainedRows CenteredMomentSecondHeightFamily
open CenteredMomentSecondWindowBudget CenteredMomentSecondHarmonicBudget
open CenteredMomentFirstMixedAllowance CenteredMomentRankinRadical
open CenteredMomentFirstInactiveRadicalMass (actual_inactive_radical_mass inactiveWeight_nonneg)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
open CenteredMomentFirstDivisorCommonBound
  (pairMajorant pairMajorant_nonneg gaussEnergy_pair_bound coarse coarse_nonneg)
open CenteredMomentFirstDivisorSupport (supported_harmonic_mass)
lemma commonEnergy_coarse (s : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (τ : AngularCharacter) (v : ℝ) :
    (commonEnergy s C hC τ v L W K).re≤coarse s C hC L W K := by
  apply gaussEnergy_pair_bound _ _ _ _ _ _ W K hK
  intro I hI
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (PlainRows.SecondSource.heightCoeff_norm_le_one τ v I
      (Finset.mem_filter.mp I.property).2.1)


theorem actual_supported_annular_block (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃ Cbound : ℝ, 0≤Cbound ∧ ∀ {ι : Type u} [Fintype ι],
    ∀ (η : AngularCharacter) (s : OriginalData ι) (t : ℝ)
      (C D : Ideal O) (hC : Supported C) (hD : Supported D),
    primeSupport C=primeSupport D → ∀ (E : Finset (CommonIndex C D))
      (rows : Finset O) (K : ℝ), 0<K → ∀ n : Fin 4→ℤ,
    ∀ Hsource : ℝ,(∀I,s.beta I≠0→(I.absNorm:ℝ)≤Hsource) →
    ∀ E₁ E₂ : ℝ,0≤E₁ → 0≤E₂ →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), (L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L → ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s C hC (fixedPair η C D hC E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (E₁/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₁)) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), (L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L → ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s D hD (fixedPair η C D hC E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (E₂/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₂)) →
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay *
      ‖block η (fixedBadMask*idealGenerator s.R) 1 t s.columns s.beta C D hC hD E rows W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
          (dyadicScale (n 2)) (dyadicScale (n 3))‖ ≤
      ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cbound*
        (∑ L∈(divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
          (fun b=>Ideal.span {element C D hD.1 s.columns b})).filter
            (fun L=>(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ)),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖/(L.absNorm:ℝ))*
            (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
  obtain ⟨Cb,hCb,hbound⟩:=actual_annular_block_from_common_energy W decay J₁ J₂
  refine ⟨Cb,hCb,?_⟩
  intro ι inst η s t C D hC hD hCD E rows K hK n Hsource hβ E₁ E₂ hE₁ hE₂ hleft hright
  let live (L : Ideal O) : Prop := (L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ)
  let U := CenteredMomentFirstAnnularMajorant.profile
  let H := dyadicScale (n 1)
  let active (L : Ideal O) : Prop := live L ∧ (UniqueFactorizationMonoid.moebius L:ℂ)≠0
  let F₁ (L : Ideal O) := if active L then E₁/(L.absNorm:ℝ) else coarse s C hC L U H
  let F₂ (L : Ideal O) := if active L then E₂/(L.absNorm:ℝ) else if live L then coarse s D hD L U H else 0
  have hF₁ (L : Ideal O) : 0≤F₁ L := by
    dsimp only [F₁]; split_ifs
    · exact div_nonneg hE₁ (Nat.cast_nonneg _)
    · exact coarse_nonneg _ _ _ _ _ _
  have hF₂ (L : Ideal O) : 0≤F₂ L := by
    dsimp only [F₂]; split_ifs
    · exact div_nonneg hE₂ (Nat.cast_nonneg _)
    · exact coarse_nonneg _ _ _ _ _ _
    · exact le_rfl
  have hh:=hbound η s t C D hC hD hCD E rows K hK n F₁ F₂
    (fun L _=>hF₁ L) (fun L _=>hF₂ L)
    (by
      intro L hL χ v
      by_cases hl:active L
      · simpa only [F₁,ite_eq_left hl] using hleft L hL hl.1 (CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero L hl.2) χ v
      · apply (commonEnergy_coarse s C hC L U H (dyadicScale_pos _) _ v).trans
        rw [show F₁ L=coarse s C hC L U H from ite_eq_right hl]
        exact le_mul_of_one_le_right (coarse_nonneg _ _ _ _ _ _)
          (one_le_pow₀ (by linarith [norm_nonneg v])))
    (by
      intro L hL χ v
      by_cases hl:active L
      · simpa only [F₂,ite_eq_left hl] using hright L hL hl.1 (CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero L hl.2) χ v
      · by_cases hc:live L
        · apply (commonEnergy_coarse s D hD L U H (dyadicScale_pos _) _ v).trans
          simp only [F₂,ite_eq_right hl,ite_eq_left hc]
          exact le_mul_of_one_le_right (coarse_nonneg _ _ _ _ _ _) (one_le_pow₀ (by linarith [norm_nonneg v]))
        · rw [commonEnergy_zero s D hD Hsource hβ L (lt_of_not_ge hc)]
          simp only [F₂,ite_eq_right hl,ite_eq_right hc,Complex.zero_re,zero_mul,le_refl])
  let Ds:=divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
    (fun b=>Ideal.span {element C D hD.1 s.columns b})
  have he : (∑L∈Ds,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
      (windowBudget J₁ t (F₁ L)*windowBudget J₂ t (F₂ L))) =
      (∑L∈Ds.filter live,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖/(L.absNorm:ℝ))*
        (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
    rw [Finset.sum_mul,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro L hL
    by_cases hμ:(UniqueFactorizationMonoid.moebius L:ℂ)=0
    · simp only [hμ,norm_zero,zero_mul,zero_div,ite_self]
    · by_cases hl:live L
      · have ha:active L:=⟨hl,hμ⟩
        simp only [F₁,F₂,ite_eq_left ha,live,ite_eq_left hl]
        rw [CenteredMomentSecondHarmonicBudget.paired_divisor J₁ J₂ t E₁ E₂ _ (Nat.cast_nonneg _)]
        ring
      · have ha:¬active L:=fun hh=>hl hh.1
        simp only [F₂,ite_eq_right ha,live,ite_eq_right hl,windowBudget,Real.sqrt_zero,zero_mul,mul_zero]
  exact hh.trans_eq (by rw [he]; ring)

theorem actual_supported_annular_harmonic (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ)
    (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃ Cbound : ℝ, 0<Cbound ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀ {ι : Type u} [Fintype ι],
    ∀ (η : AngularCharacter) (s : OriginalData ι) (t : ℝ)
      (C D : Ideal O) (hC : Supported C) (hD : Supported D),
    primeSupport C=primeSupport D → ∀ (E : Finset (CommonIndex C D))
      (rows : Finset O) (K : ℝ), 0<K → ∀ n : Fin 4→ℤ,
    ∀ Hsource : ℝ,(∀I,s.beta I≠0→(I.absNorm:ℝ)≤Hsource) →
    Hsource/(D.absNorm:ℝ)≤Z^B → ∀ E₁ E₂ : ℝ,0≤E₁ → 0≤E₂ →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), (L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L → ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s C hC (fixedPair η C D hC E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (E₁/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₁)) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), (L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L → ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s D hD (fixedPair η C D hC E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (E₂/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₂)) →
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay *
      ‖block η (fixedBadMask*idealGenerator s.R) 1 t s.columns s.beta C D hC hD E rows W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
          (dyadicScale (n 2)) (dyadicScale (n 3))‖ ≤
      ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cbound*Z^δ*
        (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
  obtain ⟨Cb,hCb,hbound⟩:=actual_supported_annular_block W decay J₁ J₂
  obtain ⟨Cm,hCm,hmass⟩:=supported_harmonic_mass B δ hB hδ
  refine ⟨(Cb+1)*Cm,mul_pos (by linarith) hCm,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι inst η s t C D hC hD hCD E rows K hK n Hsource hβ hcap E₁ E₂ hE₁ hE₂ hleft hright
  have hh:=hbound η s t C D hC hD hCD E rows K hK n Hsource hβ E₁ E₂ hE₁ hE₂ hleft hright
  have hm:=hZ.2 (divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
    (fun b=>Ideal.span {element C D hD.1 s.columns b})) D Hsource hcap
  have hW : 0≤windowBudget J₁ t E₁*windowBudget J₂ t E₂ :=
    mul_nonneg (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _)
  have hz : 0≤Z^δ := Real.rpow_nonneg ((zero_lt_one.trans hZ.1).le) _
  calc
    _ ≤ _ := hh
    _ ≤ ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cb*(Cm*Z^δ)*
        (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
      gcongr
    _ ≤ _ := by
      have hc : Cb≤Cb+1 := by linarith
      calc
        _ = ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cb*Cm*Z^δ*
          (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by ring
        _ ≤ ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*(Cb+1)*Cm*Z^δ*
          (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by gcongr
        _ = _ := by ring


end OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.commonEnergy_coarse
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.commonEnergy_coarse

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.actual_supported_annular_block
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.actual_supported_annular_block

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.actual_supported_annular_harmonic
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.actual_supported_annular_harmonic
