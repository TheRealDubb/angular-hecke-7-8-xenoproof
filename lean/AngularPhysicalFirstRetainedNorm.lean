import AngularPhysicalFirstRetainedAssembly
import AngularPhysicalFirstRetainedActive
import AngularPhysicalPlainSummability
import OAI.NumberTheory.DirichletL.Moments.FirstRetainedNorm

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace OAI.SevenEighths.Angular.PlainRows.FirstPhysical
open ActualEisensteinCubic ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstRetainedAssembly CenteredMomentFirstRetainedActive
open CenteredMomentFirstSectorTransform CenteredMomentFirstSectors PlainRows
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSourceRow CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentRowNorm
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentLogDyadic
open CenteredMomentActiveSource (activeSource)
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]


def sector (s:CommonRows.Input ι)(Rbad seed:Ideal O)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    let R:=frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ
    ∑n:Blocks (effectiveScale C D E K) R
        (CommonRows.sourceRadius s/(C.absNorm:ℝ))
        (CommonRows.sourceRadius s/(D.absNorm:ℝ)),
      block s.η m A t S (CommonRows.coefficient s Rbad seed)
        C D hC hD E (CenteredMomentSecondRetainedRows.retainedRows R 1) W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3))

def sectorMass (s:CommonRows.Input ι)(Rbad seed:Ideal O)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℝ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    let R:=frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ
    ∑n:Blocks (effectiveScale C D E K) R
        (CommonRows.sourceRadius s/(C.absNorm:ℝ))
        (CommonRows.sourceRadius s/(D.absNorm:ℝ)),
      ‖block s.η m A t S (CommonRows.coefficient s Rbad seed)
        C D hC hD E (CenteredMomentSecondRetainedRows.retainedRows R 1) W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3))‖

omit [DecidableEq ι] in
theorem sector_norm (s:CommonRows.Input ι)(Rbad seed:Ideal O)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    ‖sector s Rbad seed m A t S C D hC hD W K X Z ξ‖≤
      sectorMass s Rbad seed m A t S C D hC hD W K X Z ξ:=by
  unfold sector sectorMass
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro E hE
  exact norm_sum_le _ _

theorem original_active_sectors (s:CommonRows.Input ι)(Rbad seed:Ideal O)
    (hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)(m A:O)(t:ℝ)(S:Finset (Ideal O))
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ)(hK:0<K):
    let β:=CommonRows.coefficient s Rbad seed
    let T:=activeSource S β
    PlainRows.retainedEnergy s.η m A t S β W K X Z ξ=
      ∑p:commonLabels (supportedColumns T) (supportedColumns T),
        rowWeight s.η m A 1 t p.val.1*star (rowWeight s.η m A 1 t p.val.2)*
        sector s Rbad seed m A t T p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 W K X Z ξ:=by
  dsimp only
  rw [←retained_energy_active s.η m A t S _ W K X Z ξ]
  exact original_retained_physical s Rbad seed hz₁ hz₂ m A t _ W K X Z ξ hK

theorem original_retained_norm (s:CommonRows.Input ι)(Rbad seed:Ideal O)
    (hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)(m A:O)(t:ℝ)(S:Finset (Ideal O))
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ)(hK:0<K):
    let β:=CommonRows.coefficient s Rbad seed
    let T:=activeSource S β
    ‖PlainRows.retainedEnergy s.η m A t S β W K X Z ξ‖≤
      ∑p:commonLabels (supportedColumns T) (supportedColumns T),
        sectorMass s Rbad seed m A t T p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 W K X Z ξ:=by
  dsimp only
  rw [original_active_sectors s Rbad seed hz₁ hz₂ m A t S W K X Z ξ hK]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_mul]
  have hw:‖rowWeight s.η m A 1 t p.val.1*star (rowWeight s.η m A 1 t p.val.2)‖≤1:=by
    rw [norm_mul,norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (PlainRows.row_twisted_coefficient_norm _ _ _ _ _ _
        (commonLabels_supported _ p).1.1)).trans
      (PlainRows.row_twisted_coefficient_norm _ _ _ _ _ _
        (commonLabels_supported _ p).2.1)
  exact (mul_le_of_le_one_left (norm_nonneg _) hw).trans (sector_norm s Rbad seed m A t _ _ _ _ _ W K X Z ξ)

end OAI.SevenEighths.Angular.PlainRows.FirstPhysical

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.sector_norm
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.sector_norm

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.original_active_sectors
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.original_active_sectors

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.original_retained_norm
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.original_retained_norm
