import AngularPhysicalActualRelativePrimeBound
import AngularPhysicalActualSlotDeletion

noncomputable section
open scoped Classical BigOperators ContDiff Topology
namespace OAI.SevenEighths.Angular.RelativePrime
open PlainRows NaturalRows ExceptionalRows HeckePrimeAnnular Filter
open CenteredMomentWholeSlotDeletion (whole_removal)
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentSecondHeightFamily (fixedBadMask)
local notation "O" => ActualEisensteinCubic.O
variable (M:Ideal O) [NeZero M]
local instance actualRelativeCapacityFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
include hH

theorem relative_slots_uniform {ι:Type*}[Fintype ι]
    (W:ι→ℝ→ℂ)(a b:ι→ℝ)(ha:∀i,0<a i)
    (hWs:∀i,Function.support (W i)⊆Set.Icc (a i) (b i))(hW:∀i,ContDiff ℝ ∞ (W i))
    (Lmod Lslot loss lo hi:ℝ)(hLm:0≤Lmod)(hLs:0≤Lslot)(hloss:0<loss):
    ∃degree:ℕ,∃C:ℝ,1≤C ∧ ∀ν:ι→AngularCharacter,∃Z₀:ℝ,1<Z₀ ∧
    ∀ceiling κ:ℝ,(51/100:ℝ)≤ceiling → ceiling≤1 →
    HeckeZeroSupremum.beta≤ceiling → 2*ceiling-1≤κ → ∀i:ι,∀Z P:ℝ,Z₀≤Z → 1≤P → P≤Z^Lslot →
    ∀η:AngularCharacter,∀z:O,∀F:NaturalRow η z,η.k+(ν i).k=0 →
      (F.character.modulus.absNorm:ℝ)≤Z^Lmod →
    ∀Q:Ideal O,Q≤M → Q≤(ν i).modulus → ¬FixedInducingRow η Q fixedBadMask 1 z →
    ∀σ t v V:ℝ,lo≤σ → σ≤hi → 0≤V → |v|≤V →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H (b i) P)
        (fun I=>(ν i).idealHom I*annularWeight (W i) P σ v I) t P‖^2≤
        C*(1+|t|+V)^degree*Z^loss*P^κ := by
  choose degree C hC hb using fun i=>natural_relative_slot_bound M H hH (W i) (a i) (b i)
    (ha i) (hWs i) (hW i) Lmod Lslot loss lo hi hLm hLs hloss
  let Ctotal:ℝ:=1+∑i,C i
  have hCtotal:1≤Ctotal:=by
    have hsum:=Finset.sum_nonneg (fun i (_:i∈Finset.univ)=>(hC i).le)
    dsimp [Ctotal];linarith
  have hCi (i:ι):C i≤Ctotal:=by
    have hsum:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hC j).le) (Finset.mem_univ i)
    dsimp [Ctotal];linarith
  refine ⟨∑i,degree i,Ctotal,hCtotal,?_⟩
  intro ν
  have hev:∀ᶠZ:ℝ in atTop,∀i:ι,_ := Filter.eventually_all.mpr (fun i=>hb i (ν i))
  obtain ⟨Zbase,hbase⟩:=eventually_atTop.mp hev
  refine ⟨max 2 Zbase,lt_max_of_lt_left (by norm_num),?_⟩
  intro ceiling κ hfloor hupper hceil hκ i Z P hZ hP hPcap η z F htype hcond Q hQM hQν hex σ t v V hσ hσhi hV hv
  have hZ0:Zbase≤Z:=(le_max_right _ _).trans hZ
  have hZp:0<Z:=lt_of_lt_of_le (by norm_num:0<(2:ℝ)) ((le_max_left _ _).trans hZ)
  refine (hbase Z hZ0 i ceiling κ hfloor hupper hceil hκ P hP hPcap η z F htype hcond Q hQM hQν hex σ t v hσ hσhi).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hP) _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZp.le _)
  apply mul_le_mul (hCi i) _ (by positivity) (zero_le_one.trans hCtotal)
  calc
    _≤(1+|t|+V)^(degree i):=pow_le_pow_left₀ (by positivity) (by linarith) _
    _≤_:=pow_le_pow_right₀ (by linarith [abs_nonneg t])
      (Finset.single_le_sum (fun j _=>Nat.zero_le _) (Finset.mem_univ i))

end OAI.SevenEighths.Angular.RelativePrime

#print axioms OAI.SevenEighths.Angular.RelativePrime.relative_slots_uniform
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.relative_slots_uniform
