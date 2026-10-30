import AngularPhysicalOriginalPairData
import AngularPhysicalSecondDivisorSupport

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.CommonExceptionalSource
open PlainRows
open PlainRows.CommonRows (Input)
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSecondSectorColumns CenteredMomentSecondScaled CenteredMomentChildAssembly
open CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
local notation "O" => ActualEisensteinCubic.O
local instance {κ:Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _
theorem originalPair_filter_right {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(η:AngularCharacter)(χ ξ:RayCharacter)(A:O)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O)
    (t w X Y H:ℝ)(Ds:Finset (Ideal O))(rows:Finset O)
    (hβ:∀I:Ideal O,finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) I≠0→
      (I.absNorm:ℝ)≤H):
    originalPair s η χ ξ A C D hC hD R seed t w X Y Ds rows=
      originalPair s η χ ξ A C D hC hD R seed t w X Y
        (Ds.filter (fun L=>(L.absNorm:ℝ)≤H/(D.absNorm:ℝ))) rows:=by
  unfold originalPair
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro L hLD
  by_cases hL:(L.absNorm:ℝ)≤H/(D.absNorm:ℝ)
  · rw [ite_eq_left hL]
  · rw [ite_eq_right hL]
    have hz:=right_divisor_row_zero D hD (finiteColumns (Fintype.piFinset s.pools))
      (finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed))
      H hβ L (lt_of_not_ge hL) η t A ξ
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro z hzr
    apply mul_eq_zero_of_right
    exact norm_eq_zero.mpr (hz _ _)

end OAI.SevenEighths.Angular.CommonExceptionalSource

#print axioms OAI.SevenEighths.Angular.CommonExceptionalSource.originalPair_filter_right
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CommonExceptionalSource.originalPair_filter_right
