import AngularPhysicalRetainedPhysicalBlocks
import AngularPhysicalPlainReflected
import OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows.SecondSource
open PhysicalBlock CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentCanonicalFirst
open CenteredMomentSecondSectorColumns CenteredMomentSectorLocalization CenteredMomentSupport
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondSectorRetained (physicalKernel)
open CenteredMomentSecondSourceRetained (retainedKernel)
open CenteredMomentSecondRetainedAggregate (commonLabels_supported)
open CenteredMomentSecondRetainedRows (retainedRows retained_mem_rows)
open CenteredMomentActiveSource (activeSource supportedColumns_active)
open CenteredMomentSecondActiveDyadic
  (sourceLower sourceUpper dyadicKernel active_sector_norm sourceLower_pos)
open CenteredMomentSecondDyadicPartition CenteredMomentSecondPhysicalWindow
open CenteredMomentSecondWholeKernel CenteredMomentLogDyadic CenteredMomentSmooth
open CenteredMomentSecondBlockAggregate (ActiveLabel SourceBlocks retainedRows_ne_zero)
local notation "O" => ActualEisensteinCubic.O

open ChildRows RayFourExpansion
open ExceptionalRows (nonexceptional)
open CenteredMomentSecondLiveBlock (liveRows liveRows_weight liveRows_geometry)
open CenteredMomentSecondEnergySplit (sourceRows sourceRows_nonzero)
def liveLabels (η:AngularCharacter) (S:Finset (Ideal O)) (β:Ideal O→ℂ):Finset (ActiveLabel S β):=
  Finset.univ.filter (fun p=>η.idealHom p.val.1≠0 ∧ η.idealHom p.val.2≠0)

lemma mem_liveLabels (η:AngularCharacter) (S:Finset (Ideal O)) (β:Ideal O→ℂ) (p:ActiveLabel S β):
    p∈liveLabels η S β ↔ η.idealHom p.val.1≠0 ∧ η.idealHom p.val.2≠0:=by
  simp only [liveLabels,Finset.mem_filter,Finset.mem_univ,true_and]

lemma common_height_zero_of_not_live (η:AngularCharacter) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (p:ActiveLabel S β)
    (hp:p∉liveLabels η S β):heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)=0:=by
  rw [mem_liveLabels] at hp
  push Not at hp
  by_cases hc:η.idealHom p.val.1=0
  · simp only [heightCoeff,hc,zero_mul]
  · simp only [heightCoeff,hp hc,zero_mul,star_zero,mul_zero]

end OAI.SevenEighths.Angular.PlainRows.SecondSource

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.mem_liveLabels
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.mem_liveLabels

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.common_height_zero_of_not_live
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.common_height_zero_of_not_live
