import AngularPhysicalRelativeSlotsUniform
import OAI.NumberTheory.DirichletL.Moments.LiveCapacity

noncomputable section
open scoped Classical BigOperators ContDiff Topology
namespace OAI.SevenEighths.Angular.RelativePrime
open PlainRows NaturalRows ExceptionalRows HeckePrimeAnnular Filter
open CenteredMomentWholeSlotDeletion (whole_removal)
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentSecondHeightFamily (fixedBadMask)
local notation "O" => ActualEisensteinCubic.O
variable (M:Ideal O) [NeZero M]
local instance actualRelativeCapacityRemovalFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
include hH

theorem actual_relative_capacity_removal {ι:Type*}[Fintype ι][DecidableEq ι]
    (W:ι→ℝ→ℂ)(a b:ι→ℝ)(ha:∀i,0<a i)
    (hWs:∀i,Function.support (W i)⊆Set.Icc (a i) (b i))(hW:∀i,ContDiff ℝ ∞ (W i))
    (Lmod Lslot ε lo hi:ℝ)(hLm:0≤Lmod)(hLs:0≤Lslot)(hε:0<ε):
    ∃degree:ℕ,∃C:ℝ,0<C ∧ ∀ν:ι→AngularCharacter,∃Z₀:ℝ,1<Z₀ ∧
    ∀ceiling κ:ℝ,(51/100:ℝ)≤ceiling → ceiling≤1 →
    HeckeZeroSupremum.beta≤ceiling → 2*ceiling-1≤κ → ∀(J:Finset ι)(w:ι→ℝ)(n₁ n₂ width mesh:ℝ),0≤mesh →
      (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤width) ∧
      κ*(∑i∈R,w i)≤CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh ∧
    ∀Z:ℝ,Z₀≤Z → ∀η:AngularCharacter,∀z:O,∀F:NaturalRow η z,(∀i,η.k+(ν i).k=0) →
      (F.character.modulus.absNorm:ℝ)≤Z^Lmod →
    ∀Q:Ideal O,Q≤M → (∀i,Q≤(ν i).modulus) → ¬FixedInducingRow η Q fixedBadMask 1 z →
    ∀(σ freq:ι→ℝ)(t V:ℝ),(∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤V → (∀i,|freq i|≤V) →
    ∀(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ),
      let P:=fun i=>Z^(w i)
      let S:=fun i=>primePool M H (b i) (P i)
      let coeff:=fun i I=>(ν i).idealHom I*annularWeight (W i) (P i) (σ i) (freq i) I
      ‖selectedProduct J η fixedBadMask 1 z W₁ W₂ S coeff P t X₁ X₂‖^2≤
        C*(1+|t|+V)^degree*Z^(ε+CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)*
          ‖selectedProduct (J\R) η fixedBadMask 1 z W₁ W₂ S coeff P t X₁ X₂‖^2 := by
  let N:=Fintype.card ι
  let loss:=ε/((N:ℝ)+1)
  have hloss:0<loss:=div_pos hε (by positivity)
  obtain ⟨degree,C,hC,hbound⟩:=relative_slots_uniform M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi hLm hLs hloss
  refine ⟨degree*N,C^N,pow_pos (zero_lt_one.trans_le hC) _,?_⟩
  intro ν
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound ν
  refine ⟨Z₀,hZ₀,?_⟩
  intro ceiling κ hfloor hupper hceil hκ J w n₁ n₂ width mesh hmesh hw hwm hwcap
  have hκpos:0<κ:=by linarith
  let excess:=CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ
  obtain ⟨R,hR,hRsum,hpay,hcost⟩:=whole_removal J w excess κ mesh (le_max_right _ _) hκpos hmesh
    (fun i _=>hw i) (fun i _=>hwm i)
  refine ⟨R,hR,CenteredMomentLiveCapacity.remaining_capacity J R hR w n₁ n₂ width κ hpay,hcost,?_⟩
  intro Z hZ η z F htype hcond Q hQM hQν hex σ freq t V hσ hσhi hV hfreq W₁ W₂ X₁ X₂
  dsimp only
  have hZ1:1≤Z:=hZ₀.le.trans hZ
  have hZp:0<Z:=zero_lt_one.trans_le hZ1
  let B:=C*(1+|t|+V)^degree*Z^loss
  have hB:1≤B:=by
    have ht:1≤(1+|t|+V)^degree:=one_le_pow₀ (by linarith [abs_nonneg t])
    have hz:1≤Z^loss:=Real.one_le_rpow hZ1 hloss.le
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC ht) hz
  have hs:∀i∈R,‖normalizedSlot η fixedBadMask 1 z (primePool M H (b i) (Z^(w i)))
      (fun I=>(ν i).idealHom I*annularWeight (W i) (Z^(w i)) (σ i) (freq i) I) t (Z^(w i))‖^2≤
      B*Z^(κ*w i) := by
    intro i hi
    have hb:=hbound ceiling κ hfloor hupper hceil hκ i Z (Z^(w i)) hZ (Real.one_le_rpow hZ1 (hw i))
      (Real.rpow_le_rpow_of_exponent_le hZ1 (hwcap i)) η z F (htype i) hcond Q hQM (hQν i) hex
      (σ i) t (freq i) V (hσ i) (hσhi i) hV (hfreq i)
    rw [←Real.rpow_mul hZp.le] at hb
    simpa only [B,mul_comm (w i) κ] using hb
  have he:=selectedProduct_energy_remove J R hR η fixedBadMask 1 z W₁ W₂
    (fun i=>primePool M H (b i) (Z^(w i)))
    (fun i I=>(ν i).idealHom I*annularWeight (W i) (Z^(w i)) (σ i) (freq i) I)
    (fun i=>Z^(w i)) t X₁ X₂ Z κ hZp w (fun _=>B) (fun i hi=>zero_le_one.trans hB) hs
  apply he.trans
  gcongr 1
  have hcard:R.card≤N:=Finset.card_le_univ R
  have hpow:(∏i∈R,B)≤B^N:=by
    rw [Finset.prod_const]
    exact pow_le_pow_right₀ hB hcard
  have hcostZ:Z^(κ*∑i∈R,w i)≤Z^(excess/6+κ*mesh):=
    Real.rpow_le_rpow_of_exponent_le hZ1 hcost
  have hsplit:B^N=C^N*(1+|t|+V)^(degree*N)*Z^(loss*(N:ℝ)):=by
    dsimp [B]
    rw [mul_pow,mul_pow,←pow_mul,←Real.rpow_natCast (Z^loss) N,←Real.rpow_mul hZp.le]
  have hlossN:loss*(N:ℝ)≤ε:=by
    dsimp [loss]
    have hden:0<(N:ℝ)+1:=by positivity
    have hh:ε/((N:ℝ)+1)*((N:ℝ)+1)=ε:=div_mul_cancel₀ _ hden.ne'
    nlinarith [hloss.le]
  calc
    _≤B^N*Z^(excess/6+κ*mesh):=mul_le_mul hpow hcostZ (Real.rpow_nonneg hZp.le _) (by positivity)
    _=C^N*(1+|t|+V)^(degree*N)*Z^(loss*(N:ℝ)+(excess/6+κ*mesh)):=by
      rw [hsplit,mul_assoc,←Real.rpow_add hZp]
    _≤_:=mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)) (by positivity)
  apply le_of_eq
  congr 3
  ext i
  simp

end OAI.SevenEighths.Angular.RelativePrime

#print axioms OAI.SevenEighths.Angular.RelativePrime.actual_relative_capacity_removal
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.actual_relative_capacity_removal
