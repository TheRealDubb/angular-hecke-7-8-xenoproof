import AngularPhysicalRelativeStateCapacity
import AngularPhysicalFinitePrimeCeiling

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
local instance threeQuartersStateCapacityFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
include hH

/-- Actual angular-state capacity removal for kappa at least 3/4.
The only zero-supremum input is the proved original finite-order 7/8 theorem;
angular cancellation and all actual-state hypotheses remain explicit. -/
theorem actual_state_capacity_removal_of_three_quarters
    (W : ι→ℝ→ℂ) (a b : ι→ℝ) (ha : ∀i,0<a i)
    (hWs : ∀i,Function.support (W i)⊆Set.Icc (a i) (b i))
    (hW : ∀i,ContDiff ℝ ∞ (W i))
    (Mrow bΦ Lmod Lslot ε lo hi : ℝ) (hbΦ : 0≤bΦ)
    (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hε : 0<ε) :
    ∃degree:ℕ,∃C:ℝ,0<C ∧ ∀ν:ι→AngularCharacter,∃Z₀:ℝ,1<Z₀ ∧
    ∀κ:ℝ,(3/4:ℝ)≤κ → ∀(J:Finset ι)(w:ι→ℝ)(n₁ n₂ width mesh:ℝ),0≤mesh →
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
  obtain ⟨degree,C,hC,hbound⟩ := actual_state_capacity_removal M H hH W a b ha hWs hW
    Mrow bΦ Lmod Lslot ε lo hi hbΦ hLm hLs hε
  refine ⟨degree,C,hC,?_⟩
  intro ν
  obtain ⟨Z₀,hZ₀,hbound⟩ := hbound ν
  refine ⟨Z₀,hZ₀,?_⟩
  intro κ hκ
  exact hbound (7/8) κ (by norm_num) (by norm_num)
    finite_beta_le_seven_eighths (by linarith)

end OAI.SevenEighths.Angular.RelativePrime

#print axioms OAI.SevenEighths.Angular.RelativePrime.actual_state_capacity_removal_of_three_quarters
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.actual_state_capacity_removal_of_three_quarters
