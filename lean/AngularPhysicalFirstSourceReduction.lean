import AngularPhysicalFirstRetainedNorm
import AngularPhysicalActualFirstRemainder
import OAI.NumberTheory.DirichletL.Moments.FirstSourceReduction

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace OAI.SevenEighths.Angular.PlainRows.FirstPhysical
open HeckeFamily CanonicalQuadraticSieve CommonRows
open CommonRows CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentExceptionalAmplitudePair CommonRows
open CommonRows CenteredMomentFirstRetainedNorm
open CenteredMomentFirstSectorTransform CenteredMomentFirstSectors CenteredMomentFirstEnergy
open CenteredMomentActiveSource (activeSource)
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance actualFirstSourceReductionDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _


def physicalMass (s:CommonRows.Input ι)(R seed:Ideal O)(m A:O)(Φ:𝓢(ℝ,ℂ))(K Z ξ:ℝ):ℝ:=
  let β:=CommonRows.coefficient s R seed
  let T:=activeSource (finiteColumns (Fintype.piFinset s.pools)) β
  ∑p:commonLabels (supportedColumns T) (supportedColumns T),
    sectorMass s R seed m A s.t T p.val.1 p.val.2
      (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K
      (CommonRows.volume s) Z ξ

theorem original_first_physical_reduction (hi:ι→ℝ)(wlo whi B ε ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧ 0<Ctail ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(s:CommonRows.Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),
      s.W₁=W₁→s.W₂=W₂→Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤hi i)→
      ∀(m A:O),ConcretePrimeRowBridge.goodLambda∣m→(2:O)∣m→
      ∀(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0<K→
      CommonRows.volume s≤Z^B→K⁻¹≤Z^B→
      ‖finiteHeckeEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
          (CommonRows.coefficient s R seed) Φ K‖/CommonRows.volume s≤
      physicalMass s R seed m A Φ K Z ξ/CommonRows.volume s+
      Cdiag*(CommonRows.plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^ε+
      Ctail*(CommonRows.plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):=by
  obtain ⟨Sdiag,Stail,Cdiag,Ctail,hCdiag,hCtail,hrem⟩:=
    CommonRows.original_first_remainder hi wlo whi B ε ξ saving hhi hwlo hwhi hB hε hξ
  refine ⟨Sdiag,Stail,Cdiag,Ctail,hCdiag,hCtail,?_⟩
  filter_upwards [hrem] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A hml hm2 R seed Φ K hK hVcap hKi
  have hz (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc wlo whi):W 0=0:=by
    by_contra hn
    exact (not_le_of_gt hwlo) (hs hn).1
  have hr:=original_retained_norm s R seed (he₁.symm ▸ hz W₁ hs₁) (he₂.symm ▸ hz W₂ hs₂)
    m A s.t (finiteColumns (Fintype.piFinset s.pools)) Φ K (CommonRows.volume s) Z ξ hK
  change ‖PlainRows.retainedEnergy s.η m A s.t
    (finiteColumns (Fintype.piFinset s.pools)) (CommonRows.coefficient s R seed) Φ K
      (CommonRows.volume s) Z ξ‖≤physicalMass s R seed m A Φ K Z ξ at hr
  have he:=hZ.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A hml hm2 R seed Φ K hK hVcap hKi
  have htri:=norm_le_norm_sub_add
    (finiteHeckeEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools)) (CommonRows.coefficient s R seed) Φ K)
    (PlainRows.retainedEnergy s.η m A s.t
      (finiteColumns (Fintype.piFinset s.pools)) (CommonRows.coefficient s R seed) Φ K (CommonRows.volume s) Z ξ)
  have hdiv:=div_le_div_of_nonneg_right htri (CommonRows.volume_pos s).le
  rw [add_div] at hdiv
  have hrdiv:=div_le_div_of_nonneg_right hr (CommonRows.volume_pos s).le
  linarith

end OAI.SevenEighths.Angular.PlainRows.FirstPhysical

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.original_first_physical_reduction
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.original_first_physical_reduction
