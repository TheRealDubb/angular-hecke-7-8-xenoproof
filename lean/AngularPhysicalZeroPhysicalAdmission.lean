import AngularPhysicalZeroEmptyPhysical
import AngularPhysicalNaturalHighParameters
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.NaturalZeroPhysical
open PlainRows PlainRows.CommonRows PlainRows.FirstPhysical EnergyState EnergyBands
open QuadraticInitialBound CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyBands (length)
open CenteredMomentEnergyReferenceState (comparisonFirst comparisonSecond)
local notation "O"=>ActualEisensteinCubic.O
variable {angularOrder:ℕ} {Z Bmask bΦ a b:ℝ}
variable (s:NaturalState angularOrder Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)
local notation "zeroInput"=>NaturalZeroGrowth.balancedInput s p ha t X₁ X₂ hX₁ hX₂
local notation "inp"=>NaturalZeroGrowth.balancedInput s p ha t X₁ X₂ hX₁ hX₂
theorem declared_capacity (hZ:1<Z):
    let Mdecl:=max s.width (length Z X₁+length Z X₂);
    Real.logb Z (volume zeroInput)≤Mdecl ∧
    Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ)≤s.width ∧
    s.radial.scale*(s.character.modulus.absNorm:ℝ)≤Z^s.width ∧
    volume zeroInput≤Z^Mdecl:=by
  have hlog (X:ℝ)(hX:0<X):Real.logb Z X≤length Z X:=by
    rw [CenteredMomentEnergyReferenceLowBranchGeometry.length_eq_max_log Z X hZ hX]
    exact le_max_right _ _
  have hV:Real.logb Z (volume zeroInput)≤length Z X₁+length Z X₂:=by
    rw [NaturalZeroGrowth.balanced_volume,
      Real.logb_mul hX₁.ne' hX₂.ne']
    exact add_le_add (hlog X₁ hX₁) (hlog X₂ hX₂)
  have hdecl:=hV.trans (le_max_right s.width (length Z X₁+length Z X₂))
  refine ⟨hdecl,NaturalStage.actual_width_le s hZ,
    NaturalStage.actual_conductor_scale s hZ,?_⟩
  exact (Real.logb_le_iff_le_rpow hZ (volume_pos zeroInput)).mp hdecl

lemma declared_capacity_upper (Mcap Lgoal:ℝ)(hZ:1<Z)(hL:0≤Lgoal)
    (hs:s.width≤Mcap)(hc₁:X₁≤Z^Lgoal)(hc₂:X₂≤Z^Lgoal):
    max s.width (length Z X₁+length Z X₂)≤max Mcap (2*Lgoal):=by
  have hlen (X:ℝ)(hcap:X≤Z^Lgoal):length Z X≤Lgoal:=by
    unfold length
    exact (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le (le_max_left 1 X))).mpr
      (max_le (Real.one_le_rpow hZ.le hL) hcap)
  exact max_le_max hs (by linarith [hlen X₁ hc₁,hlen X₂ hc₂])

theorem four_upper_scales (Mcap Lgoal:ℝ)(hZ:1<Z)(hL:0≤Lgoal)
    (hs:s.width≤Mcap)(hc₁:X₁≤Z^Lgoal)(hc₂:X₂≤Z^Lgoal) :
    (inp).X₁≤Z^(max Mcap (2*Lgoal)) ∧
    (inp).X₂≤Z^(max Mcap (2*Lgoal)) ∧
    (inp).Y₁≤Z^(max Mcap (2*Lgoal)) ∧
    (inp).Y₂≤Z^(max Mcap (2*Lgoal)) := by
  have hLg:Lgoal≤max Mcap (2*Lgoal):=by linarith [le_max_right Mcap (2*Lgoal)]
  have hp:0<Z:=zero_lt_one.trans hZ
  have hquarter:0≤s.width/4:=div_nonneg s.width_nonneg (by norm_num)
  have hY₁:1≤comparisonFirst Z s.width:=Real.one_le_rpow hZ.le hquarter
  refine ⟨hc₁.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hLg),
    hc₂.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hLg),?_,?_⟩
  · change Z^(s.width/4)≤_
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith [s.width_nonneg,le_max_left Mcap (2*Lgoal)]
  · change X₁*X₂/comparisonFirst Z s.width≤_
    calc
      _≤X₁*X₂:=div_le_self (mul_pos hX₁ hX₂).le hY₁
      _≤Z^Lgoal*Z^Lgoal:=mul_le_mul hc₁ hc₂ hX₂.le (Real.rpow_pos_of_pos hp _).le
      _=Z^(2*Lgoal):=by rw [←Real.rpow_add hp];congr 1;ring
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZ.le (le_max_right _ _)


end OAI.SevenEighths.Angular.NaturalZeroPhysical

#print axioms OAI.SevenEighths.Angular.NaturalZeroPhysical.declared_capacity
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalZeroPhysical.declared_capacity

#print axioms OAI.SevenEighths.Angular.NaturalZeroPhysical.declared_capacity_upper
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalZeroPhysical.declared_capacity_upper

#print axioms OAI.SevenEighths.Angular.NaturalZeroPhysical.four_upper_scales
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalZeroPhysical.four_upper_scales
