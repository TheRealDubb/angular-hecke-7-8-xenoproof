import AngularPhysicalNaturalInputReindex
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.NaturalZeroPhysical
open PlainRows PlainRows.CommonRows PlainRows.FirstPhysical
open EnergyState CenteredMomentFiniteProfileExceptional NaturalInputReindex
local notation "O"=>ActualEisensteinCubic.O
variable {α β:Type*}[Fintype α][Fintype β]
local instance successorZeroEmptyDecEq {κ:Type*}:DecidableEq κ:=Classical.decEq _
local instance successorZeroEmptySumLeft : DecidableEq (α⊕Fin 2):=Classical.decEq _
local instance successorZeroEmptySumRight : DecidableEq (β⊕Fin 2):=Classical.decEq _
variable {angularOrder:ℕ}
lemma physical_mass_map (e:α≃β)(s:Input α)(R seed:Ideal O)(m A:O)
    (Ψ:𝓢(ℝ,ℂ))(K Z ξ:ℝ):
    physicalMass (reindex e s) R seed m A Ψ K Z ξ=physicalMass s R seed m A Ψ K Z ξ:=by
  have hc:CommonRows.coefficient (reindex e s) R seed=CommonRows.coefficient s R seed:=
    coefficient_map e s R seed
  have hp:CenteredMomentSourceMass.finiteColumns (Fintype.piFinset (reindex e s).pools)=
      CenteredMomentSourceMass.finiteColumns (Fintype.piFinset s.pools):=by
    rw [←pools_map e s,CenteredMomentSourceMass.finiteColumns,Finset.image_image]
    congr 1
    funext v
    exact tupleMap_product e v
  have hv:CommonRows.volume (reindex e s)=
      CommonRows.volume s:=volume_map e s
  have hs (T:Finset (Ideal O))(C D:Ideal O)
      (hC:CanonicalQuadraticSieve.Supported C)(hD:CanonicalQuadraticSieve.Supported D)
      (t X:ℝ):
      sectorMass (reindex e s) R seed m A t T C D hC hD Ψ K X Z ξ=
      sectorMass s R seed m A t T C D hC hD Ψ K X Z ξ:=by
    unfold sectorMass
    rw [sourceRadius_map e s]
    simp only [hc, show (reindex e s).η=s.η from rfl]
  let sumAt (T:Finset (Ideal O))(t X:ℝ):ℝ:=
    ∑p:CenteredMomentFirstSectors.commonLabels
        (CenteredMomentSourceRow.supportedColumns T) (CenteredMomentSourceRow.supportedColumns T),
      sectorMass s R seed m A t T p.val.1 p.val.2
        (CenteredMomentFirstSectorTransform.commonLabels_supported T p).1
        (CenteredMomentFirstSectorTransform.commonLabels_supported T p).2 Ψ K X Z ξ
  have hl:physicalMass (reindex e s) R seed m A Ψ K Z ξ=
      sumAt (CenteredMomentActiveSource.activeSource
        (CenteredMomentSourceMass.finiteColumns (Fintype.piFinset (reindex e s).pools))
        (CommonRows.coefficient (reindex e s) R seed)) s.t
        (CommonRows.volume (reindex e s)):=by
    unfold physicalMass
    dsimp only
    exact Finset.sum_congr rfl (fun p _=>hs _ _ _ _ _ _ _)
  rw [hl]
  rw [hc,hp,hv]
  rfl

def emptyEquiv (α:Type*)[Fintype α]:Fin 0≃(∅:Finset α):=Equiv.equivOfIsEmpty _ _

variable {Z Bmask bΦ a b:ℝ}(s:NaturalState angularOrder Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

def emptyBalanced (α:Type*)[Fintype α]:Input (∅:Finset α):=
  reindex (emptyEquiv α)
    (NaturalZeroGrowth.balancedInput s p ha t X₁ X₂ hX₁ hX₂)

lemma empty_balanced_mass (R seed:Ideal O)(m A:O)(Ψ:𝓢(ℝ,ℂ))(K Z₀ ξ:ℝ):
    physicalMass (emptyBalanced s p ha t X₁ X₂ hX₁ hX₂ α) R seed m A Ψ K Z₀ ξ=
      physicalMass (NaturalZeroGrowth.balancedInput s p ha t X₁ X₂ hX₁ hX₂)
        R seed m A Ψ K Z₀ ξ:=
  physical_mass_map (emptyEquiv α) _ R seed m A Ψ K Z₀ ξ

lemma empty_balanced_volume : volume (emptyBalanced s p ha t X₁ X₂ hX₁ hX₂ α)=X₁*X₂:=by
  rw [emptyBalanced,volume_map,NaturalZeroGrowth.balanced_volume]


end OAI.SevenEighths.Angular.NaturalZeroPhysical

#print axioms OAI.SevenEighths.Angular.NaturalZeroPhysical.physical_mass_map
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalZeroPhysical.physical_mass_map

#print axioms OAI.SevenEighths.Angular.NaturalZeroPhysical.empty_balanced_mass
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalZeroPhysical.empty_balanced_mass

#print axioms OAI.SevenEighths.Angular.NaturalZeroPhysical.empty_balanced_volume
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalZeroPhysical.empty_balanced_volume
