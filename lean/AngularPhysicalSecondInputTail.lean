import AngularPhysicalSecondZeroInput
import AngularPhysicalSecondDiscardedEnergy

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open Filter
namespace OAI.SevenEighths.Angular.PlainRows.CommonRows
open SecondSource CanonicalQuadraticSieve
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentSourceProfileMass
open CenteredMomentExceptionalAmplitudePair CenteredMomentFiniteProfileExceptional
open CenteredMomentSectorLocalization
open CenteredMomentSourceInputTailUniform (choose_tail_order eventually_tail_threshold)
local notation "O" => ActualEisensteinCubic.O
local instance angularSecondInputTailDecEq {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
theorem second_input_tail_arbitrary_saving (hi:ι→ℝ)(wlo whi B ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hξ:0<ξ):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K Tsec:ℝ),
      0<K→volume s≤Z^B→Tsec≤Z^B→(volume s)^2/K≤Tsec→
      ‖secondDiscardedEnergy s.η s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K Tsec Z ξ‖/volume s≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):=by
  obtain ⟨Adec,hdecay⟩:=choose_tail_order B ξ saving hB hξ
  obtain ⟨SΦ,Ctail,hCtail,htail⟩:=second_discarded_energy_bound Adec
  let Cmass:=1+2*128^(Fintype.card ι+2)*(∏i,hi i)*whi^2
  have hprodhi:0≤∏i,hi i:=Finset.prod_nonneg (fun i _=>hhi i)
  have hCmass:0<Cmass:=by dsimp [Cmass];positivity
  let HN:=Real.log (max 1 ((∏i,hi i)*whi^2))
  have hexp:(∏i,hi i)*whi^2≤Real.exp HN:=by
    dsimp [HN]
    rw [Real.exp_log (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  let C:=Cmass^2*Ctail*(Real.exp HN)^2*(1+Real.exp (2*HN))^2
  refine ⟨SΦ,C,by dsimp [C];positivity,?_⟩
  filter_upwards [eventually_tail_threshold HN ξ hξ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi R seed Φ K Tsec hK hVcap hTcap hnom
  let V:=volume s
  have hV:0<V:=volume_pos s
  have hT:0<Tsec:=(div_pos (sq_pos_of_pos hV) hK).trans_le hnom
  have hmass:=input_mass hi whi hhi hwhi s W₁ W₂ wlo hwlo he₁ he₂ hs₁ hs₂ hshi R seed
  have hcontrol:=plainControl_nonneg s W₁ W₂
  have hm:(∑I∈finiteColumns (Fintype.piFinset s.pools),‖coefficient s R seed I‖)≤
      Cmass*plainControl s W₁ W₂*V:=by
    apply hmass.trans
    apply mul_le_mul_of_nonneg_right _ hV.le
    apply mul_le_mul_of_nonneg_right _ hcontrol
    dsimp [Cmass]
    linarith
  have hn (I:Ideal O)(_hI:I∈finiteColumns (Fintype.piFinset s.pools))
      (hI:coefficient s R seed I≠0):(Ideal.absNorm I:ℝ)≤Real.exp HN*V:=
    (input_column_bound hi whi s W₁ W₂ wlo hwlo he₁ he₂ hs₁ hs₂ hshi R seed I hI).trans
      (mul_le_mul_of_nonneg_right hexp hV.le)
  have ht:=htail s.η s.t (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)
    Φ K V HN Tsec Z 1 ξ hK hV hZ.1 le_rfl hn hnom (by simpa using hZ.2)
  have hsquare:=pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) hm 2
  have hp:0<min 1 (kernelReference Tsec HN):=lt_min zero_lt_one (kernelReference_pos _ _ hT)
  have hzpos:0<Z:=zero_lt_one.trans hZ.1
  have hzpower:0<Z^(ξ/4):=Real.rpow_pos_of_pos hzpos _
  have hden:0<(min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec:=by positivity
  have hb:=hdecay HN Z V Tsec hZ.1.le hV hVcap hT hTcap
  calc
    _≤((Cmass*plainControl s W₁ W₂*V)^2*K*(Real.exp HN*V)^2*
        (Ctail*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec))/V:=by
      apply div_le_div_of_nonneg_right _ hV.le
      apply ht.trans
      apply div_le_div_of_nonneg_right _ hden.le
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right hsquare hK.le
    _=(Cmass^2*Ctail*(Real.exp HN)^2*(plainControl s W₁ W₂)^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        (V^3*((min 1 (kernelReference Tsec HN))^2)⁻¹*((1+Z^(ξ/4))^Adec)⁻¹):=by
      field_simp [ne_of_gt hV,ne_of_gt hp]
    _≤(Cmass^2*Ctail*(Real.exp HN)^2*(plainControl s W₁ W₂)^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        ((1+Real.exp (2*HN))^2*Z^(-saving)):=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _=_:=by dsimp [C];ring

end OAI.SevenEighths.Angular.PlainRows.CommonRows

#print axioms OAI.SevenEighths.Angular.PlainRows.CommonRows.second_input_tail_arbitrary_saving
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.CommonRows.second_input_tail_arbitrary_saving
