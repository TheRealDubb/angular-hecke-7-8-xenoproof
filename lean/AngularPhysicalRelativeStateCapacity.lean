import AngularPhysicalRelativeStateSupport
import AngularPhysicalActualRelativeCapacity

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace OAI.SevenEighths.Angular.RelativePrime
open PlainRows NaturalRows EnergyState InductionEnergy ExceptionalRows ConcreteTraceCRT
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentSecondHeightFamily (fixedBadMask fixedBadMask_ne_zero)
open CenteredMomentNaturalRowSource (fixedConductorFactor)
open CenteredMomentEnergyCapacityRemoval (compact_radial_summable)
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι] {angularOrder:ℕ}

variable (M:Ideal O) [NeZero M]
local instance actualStateCapacityFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
include hH

theorem actual_state_capacity_removal
    (W : ι→ℝ→ℂ) (a b : ι→ℝ) (ha : ∀i,0<a i)
    (hWs : ∀i,Function.support (W i)⊆Set.Icc (a i) (b i))
    (hW : ∀i,ContDiff ℝ ∞ (W i))
    (Mrow bΦ Lmod Lslot ε lo hi : ℝ) (hbΦ : 0≤bΦ)
    (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hε : 0<ε) :
    ∃degree:ℕ,∃C:ℝ,0<C ∧ ∀ν:ι→AngularCharacter,∃Z₀:ℝ,1<Z₀ ∧
    ∀ceiling κ:ℝ,(51/100:ℝ)≤ceiling → ceiling≤1 →
    HeckeZeroSupremum.beta≤ceiling → 2*ceiling-1≤κ → ∀(J:Finset ι)(w:ι→ℝ)(n₁ n₂ width mesh:ℝ),0≤mesh →
      (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤width) ∧
      κ*(∑i∈R,w i)≤CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh ∧
    ∀Z:ℝ,Z₀≤Z → ∀Bmask:ℝ,∀s:NaturalState angularOrder Z Bmask bΦ,
      (∀i,s.character.k+(ν i).k=0) → s.puncture=1 → s.rowWidth≤Mrow → ∀q:ℝ,
      (s.character.modulus.absNorm:ℝ)≤Z^q → Mrow+q+1≤Lmod →
    ∀Q:Ideal O,s.fixedModulus=Q → Q≤M → (∀i,Q≤(ν i).modulus) →
    ∀(σ freq:ι→ℝ)(t V:ℝ),(∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤V → (∀i,|freq i|≤V) →
    ∀(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ),0<X₁ → 0<X₂ →
      let P:=fun i=>Z^(w i)
      let S:=fun i=>primePool M H (b i) (P i)
      let coeff:=fun i I=>(ν i).idealHom I*HeckePrimeAnnular.annularWeight (W i) (P i) (σ i) (freq i) I
      energy s.character s.mask 1 t W₁ W₂ (fun i:J=>S i) (fun i:J=>coeff i)
        (fun i:J=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        C*(1+|t|+V)^degree*Z^(ε+CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)*
          energy s.character s.mask 1 t W₁ W₂ (fun i:↥(J\R)=>S i) (fun i:↥(J\R)=>coeff i)
            (fun i:↥(J\R)=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale := by
  obtain ⟨degree,C,hC,hbound⟩:=actual_relative_capacity_removal M H hH W a b ha hWs hW
    Lmod Lslot ε lo hi hLm hLs hε
  obtain ⟨Zsupport,hsupport⟩:=eventually_atTop.mp (eventual_row_conductor bΦ Mrow hbΦ)
  refine ⟨degree,C,hC,?_⟩
  intro ν
  obtain ⟨Zbase,hZbase,hbound⟩:=hbound ν
  refine ⟨max Zbase Zsupport,lt_of_lt_of_le hZbase (le_max_left _ _),?_⟩
  intro ceiling κ hfloor hupper hceil hκ J w n₁ n₂ width mesh hmesh hw hwm hwcap
  obtain ⟨R,hR,hcapacity,hcost,hpoint⟩:=hbound ceiling κ hfloor hupper hceil hκ J w n₁ n₂ width mesh hmesh hw hwm hwcap
  refine ⟨R,hR,hcapacity,hcost,?_⟩
  intro Z hZ Bmask s htype hpuncture hrow q hmod hLmod Q hQ hQM hQν σ freq t V hσ hσhi hV hfreq W₁ W₂ X₁ X₂ hX₁ hX₂
  dsimp only
  have hZbase' : Zbase≤Z:=(le_max_left _ _).trans hZ
  have hs:=(hsupport Z ((le_max_right _ _).trans hZ))
  have hZpos:0<Z:=zero_lt_one.trans hs.1
  have hscale (i:ι) : 0≤Z^(w i):=Real.rpow_nonneg hZpos.le _
  let P:=fun i=>Z^(w i)
  let S:=fun i=>primePool M H (b i) (P i)
  let coeff:=fun i I=>(ν i).idealHom I*HeckePrimeAnnular.annularWeight (W i) (P i) (σ i) (freq i) I
  let cost:=C*(1+|t|+V)^degree*Z^(ε+CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)
  have hmask:s.mask=fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1:=by rw [NaturalState.mask,hpuncture]
  rw [hmask,unit_puncture_energy _ _ _ _ _ _ _ _ _ _ s.row_ne_zero,
    unit_puncture_energy _ _ _ _ _ _ _ _ _ _ s.row_ne_zero]
  change energy s.character fixedBadMask 1 t W₁ W₂ (fun i:J=>S i) (fun i:J=>coeff i)
    (fun i:J=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
    cost*energy s.character fixedBadMask 1 t W₁ W₂ (fun i:↥(J\R)=>S i) (fun i:↥(J\R)=>coeff i)
    (fun i:↥(J\R)=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale
  have hsum (T:Finset ι):=compact_radial_summable
    (fun z=>positiveSlotRow s.character fixedBadMask 1 z W₁ W₂ (fun i:T=>S i)
      (fun i:T=>coeff i) (fun i:T=>P i) t X₁ X₂)
    s.radial.keep s.radial.profile s.radial.scale bΦ s.radial.scale_pos s.radial_support
  unfold energy
  rw [←tsum_mul_left]
  apply (hsum J).tsum_le_tsum _ ((hsum (J\R)).mul_left cost)
  intro z
  by_cases hk:s.radial.keep z
  · simp only [ite_eq_left hk]
    by_cases hp:s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale)=0
    · simp [hp]
    · have hz:=s.row_ne_zero z hk
      have hc:((naturalRow s.character z hz).character.modulus.absNorm:ℝ)≤Z^Lmod:=
        (hs.2 Bmask s hrow q hmod z hz hp).trans
          (Real.rpow_le_rpow_of_exponent_le hs.1.le hLmod)
      have hh:=hpoint Z hZbase' s.character z (naturalRow s.character z hz) htype hc
        Q hQM hQν (state_unit_nonexceptional s hpuncture Q hQ z hk)
        σ freq t V hσ hσhi hV hfreq W₁ W₂ X₁ X₂
      dsimp only at hh
      rw [selected_eq_positive J s.character fixedBadMask 1 z W₁ W₂ S coeff P t X₁ X₂ (mul_pos hX₁ hX₂).le hscale,
        selected_eq_positive (J\R) s.character fixedBadMask 1 z W₁ W₂ S coeff P t X₁ X₂ (mul_pos hX₁ hX₂).le hscale] at hh
      exact (mul_le_mul_of_nonneg_right hh (s.radial.nonneg z)).trans_eq (by dsimp only [cost];ring)
  · simp only [ite_eq_right hk,mul_zero,le_refl]

end OAI.SevenEighths.Angular.RelativePrime

#print axioms OAI.SevenEighths.Angular.RelativePrime.actual_state_capacity_removal
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.actual_state_capacity_removal
