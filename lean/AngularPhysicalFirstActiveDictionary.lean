import AngularPhysicalFirstSourceReduction
import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalActiveDictionary

noncomputable section
set_option maxHeartbeats 1000000
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
universe u
namespace OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion CompletedGauss RayFourExpansion
open PlainRows PlainRows.CommonRows PlainRows.FirstPhysical
open CenteredMomentCommonSupport CenteredMomentCanonicalFirst CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentGaussEnergy CenteredMomentChildAssembly CenteredMomentMobiusRegroup
open CenteredMomentActiveSource CenteredMomentRowNorm CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalDyadicAssembly (Blocks effectiveScale)
open CenteredMomentFirstPhysicalSource (columns column_supported element element_span scalar
  inactiveWeight)
open CenteredMomentFirstWholeKernel (windows)
open CenteredMomentFirstDiscardedEnergy (inactiveSubsets)
open CenteredMomentSecondRetainedRows CenteredMomentSecondHeightFamily
local notation "O" => ActualEisensteinCubic.O
open CenteredMomentFirstPhysicalActiveDictionary
  (primary_supported column_pair_sum_active)
open CenteredMomentFirstWholeKernel CenteredMomentFirstFrequency
open CenteredMomentFirstReduced CenteredMomentSupportedCorrelation
open CenteredMomentCompleteCommon CenteredMomentActive
open CenteredMomentFirstSectorTransform (commonLabels_supported)
def physicalTerm (η : AngularCharacter) (m A : O) (t : ℝ) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ)
    (h : O) (I J : Ideal O) : ℂ :=
  if hI : Supported I then if hJ : Supported J then
    let na:=CompletedGauss.primaryGenerator I
    let nb:=CompletedGauss.primaryGenerator J
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
    let k:=K/‖eisEmbedding e‖^2
    let r:=activeConductor C D
    if IsCoprime I J then
      (tripleRow na nb r (supportedModulusCharacter na (primary_supported I hI))
        (supportedModulusCharacter nb (primary_supported J hJ))⁻¹ (activeFunction C D hC) e *
      ((k/‖eisEmbedding (na*(nb*r))‖^2:ℝ):ℂ)*
      tripleFourier na nb r
        (supported_element_ne_zero _ (primary_supported I hI))
        (supported_element_ne_zero _ (primary_supported J hJ))
        (finitePrimeModulus_ne_zero _) (supportedModulusCharacter na (primary_supported I hI))
        (supportedModulusCharacter nb (primary_supported J hJ))⁻¹ (activeFunction C D hC) h)*
      (coefficient η m A t β C I*star (coefficient η m A t β D J))*
      windows V (k/‖eisEmbedding r‖^2) (‖eisEmbedding h‖^2)
        (‖eisEmbedding na‖^2) (‖eisEmbedding nb‖^2) K₀ H₀ A₀ B₀*
      EisensteinSchwartzPoisson.paperRadialFourier W
        (k*‖eisEmbedding h‖^2/‖eisEmbedding (na*(nb*r))‖^2)
    else 0
  else 0 else 0

theorem physicalTerm_zero_left (η : AngularCharacter) (m A : O) (t : ℝ) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ)
    (h : O) (I J : Ideal O) (hi : β (C*I)=0) :
    physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J=0 := by
  simp only [physicalTerm,PlainRows.FirstPhysical.coefficient,hi,zero_mul,mul_zero]
  split_ifs <;> rfl

theorem physicalTerm_zero_right (η : AngularCharacter) (m A : O) (t : ℝ) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ)
    (h : O) (I J : Ideal O) (hj : β (D*J)=0) :
    physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J=0 := by
  simp only [physicalTerm,PlainRows.FirstPhysical.coefficient,hj,zero_mul,star_zero,mul_zero]
  split_ifs <;> rfl

theorem block_eq_ideal_sums (η : AngularCharacter) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block η m A t S β C D hC hD E rows W V K K₀ H₀ A₀ B₀=
      inactiveWeight C D E * ∑h∈rows,
        ∑I∈columns C C hC.1 S,∑J∈columns C D hD.1 S,
          physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J := by
  unfold block
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  calc
    _=∑I:columns C C hC.1 S,∑J:columns C D hD.1 S,
        physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J := by
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro J hJ
      simp only [physicalTerm,dite_eq_left (column_supported C C hC.1 S I),
        dite_eq_left (column_supported C D hD.1 S J),element]
      rfl
    _=_ := by
      simp_rw [Finset.sum_coe_sort]
      exact Finset.sum_coe_sort (columns C C hC.1 S)
        (fun I=>∑J∈columns C D hD.1 S,
          physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J)

theorem block_active (η : AngularCharacter) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block η m A t (activeSource S β) β C D hC hD E rows W V K K₀ H₀ A₀ B₀=
      block η m A t S β C D hC hD E rows W V K K₀ H₀ A₀ B₀ := by
  rw [block_eq_ideal_sums,block_eq_ideal_sums]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  exact column_pair_sum_active C D hC.1 hD.1 S β
    (physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h)
    (fun I J hi=>physicalTerm_zero_left η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J hi)
    (fun I J hj=>physicalTerm_zero_right η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J hj)

theorem block_active_ne_zero_iff (η : AngularCharacter) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block η m A t (activeSource S β) β C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0 ↔
      block η m A t S β C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0 := by
  rw [block_active]

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _


open CenteredMomentSectorLocalization CenteredMomentLogDyadic

theorem original_dyadic_block_active (s : Input ι) (R seed : Ideal O)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) :
    let β:=PlainRows.CommonRows.coefficient s R seed
    block s.η m A t (activeSource S β) β C D hC hD E rows W
      (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3))=
    block s.η m A t S β C D hC hD E rows W
      (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  apply block_active

theorem original_sector_active (s : Input ι) (R seed : Ideal O)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    sector s R seed m A t
        (activeSource S (PlainRows.CommonRows.coefficient s R seed))
        C D hC hD W K X Z ξ=
      sector s R seed m A t S C D hC hD W K X Z ξ := by
  unfold sector
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only
  apply Finset.sum_congr rfl
  intro n hn
  apply block_active

theorem original_sectorMass_active (s : Input ι) (R seed : Ideal O)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    sectorMass s R seed m A t
        (activeSource S (PlainRows.CommonRows.coefficient s R seed))
        C D hC hD W K X Z ξ=
      sectorMass s R seed m A t S C D hC hD W K X Z ξ := by
  unfold sectorMass
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only
  apply Finset.sum_congr rfl
  intro n hn
  rw [block_active]

theorem active_sectorMass_sum (s : Input ι) (R seed : Ideal O)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (Φ : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    let T:=activeSource S (PlainRows.CommonRows.coefficient s R seed)
    (∑p:commonLabels (supportedColumns T) (supportedColumns T),
      sectorMass s R seed m A t T p.val.1 p.val.2
        (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K X Z ξ)=
    ∑p:commonLabels (supportedColumns T) (supportedColumns T),
      sectorMass s R seed m A t S p.val.1 p.val.2
        (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K X Z ξ := by
  dsimp only
  apply Finset.sum_congr rfl
  intro p hp
  exact original_sectorMass_active s R seed m A t S _ _ _ _ Φ K X Z ξ

theorem physicalMass_full_source [DecidableEq ι] (s : Input ι) (R seed : Ideal O)
    (m A : O) (Φ : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    PlainRows.FirstPhysical.physicalMass s R seed m A Φ K Z ξ=
      let S:=CenteredMomentSourceMass.finiteColumns (Fintype.piFinset s.pools)
      let β:=PlainRows.CommonRows.coefficient s R seed
      let T:=activeSource S β
      ∑p:commonLabels (supportedColumns T) (supportedColumns T),
        sectorMass s R seed m A s.t S p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K
          (PlainRows.CommonRows.volume s) Z ξ := by
  exact active_sectorMass_sum s R seed m A s.t
    (CenteredMomentSourceMass.finiteColumns (Fintype.piFinset s.pools)) Φ K
    (PlainRows.CommonRows.volume s) Z ξ


end OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.physicalTerm_zero_left
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.physicalTerm_zero_left

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.physicalTerm_zero_right
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.physicalTerm_zero_right

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.block_eq_ideal_sums
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.block_eq_ideal_sums

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.block_active
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.block_active

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.block_active_ne_zero_iff
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.block_active_ne_zero_iff

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.original_dyadic_block_active
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.original_dyadic_block_active

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.original_sector_active
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.original_sector_active

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.original_sectorMass_active
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.original_sectorMass_active

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.active_sectorMass_sum
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.active_sectorMass_sum

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.physicalMass_full_source
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.physicalMass_full_source
