import AngularPhysicalFirstSourceGeometry
import AngularPhysicalFirstActiveDictionary
import OAI.NumberTheory.DirichletL.Moments.FirstReferenceSource

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
open CenteredMomentFirstPhysicalDyadicCount (original_local_blocks_subpower)
open CenteredMomentSecondRetainedAggregate (commonLabels_supported)
open PlainRows.FirstPhysical.Support
local instance successorPhysicalSourceSumDecEq {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
theorem original_input_local_blocks_subpower {ι:Type*}[Fintype ι][DecidableEq ι]
    (hi:ι→ℝ)(b₁ b₂ B ξ ε:ℝ)(hB:0≤B)(hξ:0≤ξ)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀s:Input ι,(∀i,|s.hi i|≤hi i)→|s.b₁|≤b₁→|s.b₂|≤b₂→0<sourceRadius s→
      ∀(C D:Ideal O),C≠0→D≠0→∀(E:Finset (CommonIndex C D))(K:ℝ),
      0<K→PlainRows.CommonRows.volume s≤Z^B→K⁻¹≤Z^B→
      (Fintype.card (Blocks (effectiveScale C D E K)
        (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K (PlainRows.CommonRows.volume s)) Z ξ)
        (sourceRadius s/Ideal.absNorm C) (sourceRadius s/Ideal.absNorm D)):ℝ)≤C₀*Z^ε := by
  obtain ⟨C₀,hC₀,hcount⟩:=original_local_blocks_subpower B (B+1) ξ ε
    hB (by positivity) hξ hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount,Filter.eventually_ge_atTop (1:ℝ),
    Filter.eventually_ge_atTop ((∏i,hi i)*b₁*b₂)] with Z hcount hZ hfixed
  intro s hhi hb₁ hb₂ hH C D hC hD E K hK hV hKi
  exact hcount C D hC hD E K _ _ hK (PlainRows.CommonRows.volume_pos s).le hH hV hKi
    (input_radius_cap hi b₁ b₂ B Z s hhi hb₁ hb₂ hZ hfixed hV)


variable {ι:Type*} [Fintype ι] [DecidableEq ι]
def radicalWeight (s:Input ι)(R seed:Ideal O)(p:Labels s R seed)
    (E:Finset (CommonIndex p.val.1 p.val.2)):ℝ:=
  CenteredMomentFirstInactiveRadicalMass.inactiveWeight p.val.1 p.val.2 E 0/
    ((commonRadical p.val.1 p.val.2).absNorm:ℝ)

omit [DecidableEq ι] in
lemma radicalWeight_nonneg (s:Input ι)(R seed:Ideal O)(p:Labels s R seed)
    (E:Finset (CommonIndex p.val.1 p.val.2)):0≤radicalWeight s R seed p E:=
  div_nonneg (inactiveWeight_nonneg _ _ _ _) (Nat.cast_nonneg _)

lemma physicalMass_eq_sum (s:Input ι)(R seed:Ideal O)(W:𝓢(ℝ,ℂ))(K Z ξ:ℝ):
    physicalMass s R seed (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 W K Z ξ=
      ∑p:Labels s R seed,∑E∈inactiveSubsets p.val.1 p.val.2,
        ∑n:SourceBlocks s R seed K Z ξ p E,‖originalBlock s R seed W K Z ξ p E n‖:=by
  rw [physicalMass_full_source]
  rfl

theorem original_block_sum (hi:ι→ℝ)(b₁ b₂ B ξ ε:ℝ)
    (hB:0≤B)(hξ:0≤ξ)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in atTop,∀s:Input ι,∀R seed:Ideal O,
      Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→
      (∀i,|s.hi i|≤hi i)→|s.b₁|≤b₁→|s.b₂|≤b₂→0<sourceRadius s→
    ∀W:𝓢(ℝ,ℂ),∀K A:ℝ,0<K→0≤A→PlainRows.CommonRows.volume s≤Z^B→K⁻¹≤Z^B→
    (∀p:Labels s R seed,∀E∈inactiveSubsets p.val.1 p.val.2,
      ∀n:SourceBlocks s R seed K Z ξ p E,
      ‖originalBlock s R seed W K Z ξ p E n‖/PlainRows.CommonRows.volume s≤A*radicalWeight s R seed p E)→
    physicalMass s R seed (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 W K Z ξ/
      PlainRows.CommonRows.volume s≤A*(C₀*Z^ε/(seed.absNorm:ℝ)) := by
  obtain ⟨Cd,hCd,hd⟩:=original_input_local_blocks_subpower hi b₁ b₂ B ξ (ε/2) hB hξ (by linarith)
  obtain ⟨Cm,hCm,hm⟩:=actual_inactive_radical_mass (B+1) (ε/2) (by linarith) (by linarith)
  refine ⟨Cd*Cm,mul_pos hCd hCm,?_⟩
  filter_upwards [hd,eventually_ge_atTop (2:ℝ),eventually_ge_atTop ((∏i,hi i)*b₁*b₂)] with Z hd hZ hfixed
  intro s R seed hs hs0 hz₁ hz₂ hhi hb₁ hb₂ hH W K A hK hA hV hKi hblock
  have hZ1:1≤Z:=by linarith
  have hcap:=input_radius_cap hi b₁ b₂ B Z s hhi hb₁ hb₂ hZ1 hfixed hV
  have hmass:=hm Z hZ seed hs hs0
    (finiteColumns (Fintype.piFinset s.pools)) (PlainRows.CommonRows.coefficient s R seed)
    (fun I _ hI=>original_column_mask s R seed I hI)
    (fun I _ hI=>(original_column_norm s R seed I hz₁ hz₂ hI).2.trans hcap) 0 (le_refl _)
  have hf:∀p E,0≤radicalWeight s R seed p E:=radicalWeight_nonneg s R seed
  have hsector (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
      (hE:E∈inactiveSubsets p.val.1 p.val.2):
      (∑n:SourceBlocks s R seed K Z ξ p E,‖originalBlock s R seed W K Z ξ p E n‖/PlainRows.CommonRows.volume s)≤
        (Cd*Z^(ε/2)*A)*radicalWeight s R seed p E := by
    have hp:=commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (PlainRows.CommonRows.coefficient s R seed)) _ _ p.property
    have hcard:=hd s hhi hb₁ hb₂ hH p.val.1 p.val.2 hp.1.1 hp.2.1 E K hK hV hKi
    change (Fintype.card (SourceBlocks s R seed K Z ξ p E):ℝ)≤Cd*Z^(ε/2) at hcard
    calc
      _≤∑_n:SourceBlocks s R seed K Z ξ p E,A*radicalWeight s R seed p E:=
        Finset.sum_le_sum (fun n _=>hblock p E hE n)
      _ = (Fintype.card (SourceBlocks s R seed K Z ξ p E):ℝ)*(A*radicalWeight s R seed p E) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _ ≤ (Cd*Z^(ε/2))*(A*radicalWeight s R seed p E) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg hA (hf p E))
      _ = _ := (mul_assoc _ _ _).symm
  rw [physicalMass_eq_sum]
  simp only [Finset.sum_div]
  calc
    _≤∑p:Labels s R seed,∑E∈inactiveSubsets p.val.1 p.val.2,
        (Cd*Z^(ε/2)*A)*radicalWeight s R seed p E:=by
      apply Finset.sum_le_sum;intro p _
      exact Finset.sum_le_sum (fun E hE=>hsector p E hE)
    _=(Cd*Z^(ε/2)*A)*(∑p:Labels s R seed,∑E∈inactiveSubsets p.val.1 p.val.2,
        radicalWeight s R seed p E):=by simp_rw [←Finset.mul_sum]
    _≤(Cd*Z^(ε/2)*A)*(Cm*Z^(ε/2)/(seed.absNorm:ℝ)):=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _=_ := by
      rw [show Z^ε=Z^(ε/2)*Z^(ε/2) by rw [←Real.rpow_add (by linarith : 0<Z)];congr 1;ring]
      ring


end OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.original_input_local_blocks_subpower
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.original_input_local_blocks_subpower

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.radicalWeight_nonneg
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.radicalWeight_nonneg

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.physicalMass_eq_sum
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.physicalMass_eq_sum

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.original_block_sum
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.original_block_sum
