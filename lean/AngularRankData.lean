import AngularRankNormalized
import AngularRankFamily
import OAI.NumberTheory.DirichletL.Descent.CanonicalRankExistenceData

namespace OAI.CubicEisenstein.AngularRankData
noncomputable section
open scoped Classical BigOperators SchwartzMap
open SevenEighths InverseMoment ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalRowCompletion InverseInitialClippedColumns InverseReflectedPhase
open AngularCanonicalCoefficient
local notation "O" => ActualEisensteinCubic.O

def AngularRankEnergyExists (order : ℕ) (n:ℕ)(L cstar cutoff eta:ℝ)(K:ℕ)(W:𝓢(ℝ,ℂ)):Prop :=
  ∃degree:ℕ,∃B:ℝ,1≤B ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀D:ℕ,B*Z^L≤D→
    ∀{σ:Type}[DecidableEq σ](slots:Finset σ),slots.card≤K→
    ∀(lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
      (H:σ→ℝ)(a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→
      (∀i∈slots,1≤H i)→(∀i∈slots,∀P∈lists i,(Ideal.absNorm P.val:ℝ)≤H i)→
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1)→
    ∀z:ℝ,0≤z→(∏i∈slots,H i)≤Z^z→
    ∀base:O→*ℂ,(∀u,‖base u‖≤1)→
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) base→
      CompletePoolRankMoments q D slots lists a (negativeAngularTwist base order) W Z (rankRowCap n cutoff)
        (rankTotalCap n L eta) z (rankMargin n cstar eta) (rankLoss n eta) C K degree

theorem angular_rank_energy_exists_zero (order : ℕ) (L cstar cutoff eta:ℝ)(hcut:0<cutoff)(K:ℕ)(W:𝓢(ℝ,ℂ)):
    AngularRankEnergyExists order 0 L cstar cutoff eta K W :=by
  refine ⟨0,1,le_rfl,?_⟩
  intro q hq
  refine ⟨1,2,by norm_num,by norm_num,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hdis hH hP ha z hz hprod base hb hp
  dsimp only [CompletePoolRankMoments]
  let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q)
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance
  apply canonical_rank_negative
  simp only [rankRowCap,Nat.cast_zero]
  linarith

#print axioms angular_rank_energy_exists_zero
end
end OAI.CubicEisenstein.AngularRankData
