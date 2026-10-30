import AngularPhysicalFirstReferenceEnergy
import OAI.NumberTheory.DirichletL.Energy.FirstColumnPairing
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
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
open CenteredMomentEnergyFirstColumnPairing (reference_sum)
lemma fixed_pair_moduli (η:AngularCharacter)(C D:Ideal O)(hC:Supported C)
    (E:Finset (CommonIndex C D))(χ:RayCharacter):
    (fixedPair η C D hC E χ χ).left.modulus=(fixedPair η C D hC E 1 1).left.modulus ∧
    (fixedPair η C D hC E χ χ).right.modulus=(fixedPair η C D hC E 1 1).right.modulus:=by
  constructor
  · rw [(fixedPair η C D hC E χ χ).left_modulus,
      (fixedPair η C D hC E 1 1).left_modulus]
  · rw [(fixedPair η C D hC E χ χ).right_modulus,
      (fixedPair η C D hC E 1 1).right_modulus]

omit [DecidableEq ι] in
theorem column_bounds_of_reference_sums
    (s:Input ι)(R seed:Ideal O)(Z:ℝ)(Jleft Jright:ℕ)
    (frontLeft frontRight:ℝ)(lossLeft lossRight:Fin 4→ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))(n:Fin 4→ℤ)
    (hleft:∀L:Ideal O,(L.absNorm:ℝ)≤sourceRadius s/(p.val.2.absNorm:ℝ)→
      Squarefree L→∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy (original s R seed) p.val.1 (supported s R seed p).1
        (fixedPair s.η p.val.1 p.val.2 (supported s R seed p).1 E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
        (((fixedPair s.η p.val.1 p.val.2 (supported s R seed p).1 E χ χ).left.modulus.absNorm:ℝ)*
            (PlainRows.CommonRows.volume s/(p.val.1.absNorm:ℝ))^2*Z^(allowance p.val.1 p.val.2 Z)/(L.absNorm:ℝ))*
          (frontLeft*∑j:Fin 4,Z^(lossLeft j))*(1+|v|)^(2*Jleft))
    (hright:∀L:Ideal O,(L.absNorm:ℝ)≤sourceRadius s/(p.val.2.absNorm:ℝ)→
      Squarefree L→∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy (original s R seed) p.val.2 (supported s R seed p).2
        (fixedPair s.η p.val.1 p.val.2 (supported s R seed p).1 E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
        (((fixedPair s.η p.val.1 p.val.2 (supported s R seed p).1 E χ χ).right.modulus.absNorm:ℝ)*
            (PlainRows.CommonRows.volume s/(p.val.2.absNorm:ℝ))^2*Z^(allowance p.val.2 p.val.1 Z)/(L.absNorm:ℝ))*
          (frontRight*∑j:Fin 4,Z^(lossRight j))*(1+|v|)^(2*Jright)):
    ColumnBounds s R seed Z Jleft Jright
      (fun j=>frontLeft*Z^(lossLeft j)) (fun j=>frontRight*Z^(lossRight j)) p E n:=by
  constructor
  · intro L _ hcap hL χ v
    have hh:=hleft L hcap hL χ v
    rw [(fixed_pair_moduli s.η p.val.1 p.val.2 (supported s R seed p).1 E χ).1] at hh
    exact hh.trans_eq (reference_sum _ _ _ _ _ _ _)
  · intro L _ hcap hL χ v
    have hh:=hright L hcap hL χ v
    rw [(fixed_pair_moduli s.η p.val.1 p.val.2 (supported s R seed p).1 E χ).2] at hh
    exact hh.trans_eq (reference_sum _ _ _ _ _ _ _)


end OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.fixed_pair_moduli
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.fixed_pair_moduli

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.column_bounds_of_reference_sums
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.column_bounds_of_reference_sums
