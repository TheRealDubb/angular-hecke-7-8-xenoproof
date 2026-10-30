import AngularPhysicalOriginalErrorBall

noncomputable section
set_option maxHeartbeats 1000000
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace OAI.SevenEighths.Angular.PlainRows.Amplification
open AngularRowClosure ChildRows ChildInputs
open CenteredMomentSectorLocalization
open CanonicalQuadraticSieve CanonicalRowCompletion ConcreteTraceCRT ConcretePrimeRowBridge
open RayFourExpansion CenteredMomentPrimeElements CenteredMomentPrimePool
open CenteredMomentAmplificationEligibility CenteredMomentAmplificationEnergy
open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentGaussNormalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationGlobal
open CenteredMomentAmplificationSlotGap CenteredMomentAmplificationActiveFactor
open CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceProfileMass CenteredMomentSourceMass CenteredMomentAddedZeroUniform
open CenteredMomentOriginalChildEnergy CenteredMomentCommonAllocationSum
local notation "O" => ActualEisensteinCubic.O
local instance angularOriginalErrorPoolDecEq {κ:Type*} : DecidableEq (κ ⊕ Fin 2) := Classical.decEq _

theorem exists_pool_error_families {ι : Type*} [instι:Fintype ι]
    (P : Finset (Ideal O)) (hP : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (η : AngularCharacter) (m : O) (hm : m≠0) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) :
    ∃ τ : (elementPool P) → Fin 3 → RayCharacter → AngularCharacter,
        (∀ p i χ,(τ p i χ).k=η.k) ∧
      (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
        rowConductorBound (childCharacter η χ) m 1 (p.val^(2*errorMovingExponent (errorIndex i)))) ∧
      ∀ (D : OriginalData ι),
        (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
        (∀ p∈elementPool P,∀ i,∀ I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I) →
        ∀ (t T Z sigma D0 cLog : ℝ),0<T → 1<Z → 0≤sigma → ∀ (j : ℤ),
        (∑p∈elementPool P,∑h∈(dyadRows j).filter (fun h => eligible D.R D.s h p),
          errorEnergy Finset.univ (sourceGenerator D.columns) (sourceGenerator_supported D.columns)
            (originalCoefficient D η m t T) h p)≤
        ∑p : elementPool P,∑i : Fin 3,originalChildEnergy D (τ p i) p (errorIndex i) t T
          (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (errorIndex i+1))) := by
  have hf (p : elementPool P) (i : Fin 3) := by
    have hd := elementPool_data P hP hbad p p.property
    have hPid := hP _ hd.2.1
    letI : (Ideal.span {p.val}).IsMaximal :=
      (Ideal.isPrime_of_prime hPid).isMaximal hPid.ne_zero
    exact exists_original_error_ball_family (ι:=ι) η m p hm hd.1 hPid hd.2.2.2.1
      hd.2.2.2.2.1 hd.2.2.2.2.2 hd.2.2.1 hmLam hm2 (errorIndex i) (errorIndex_cases i)
  choose τ hτ using hf
  refine ⟨τ,fun p i => (hτ p i).1,fun p i => (hτ p i).2.1,?_⟩
  intro D hS hprime hslot t T Z sigma D0 cLog hT hZ hsigma j
  rw [←Finset.sum_coe_sort (elementPool P)]
  apply Finset.sum_le_sum
  intro p hp
  have h0 := (hτ p 0).2.2 D hS hprime (hslot p p.property) t T Z sigma D0 cLog hT hZ hsigma j
  have h5 := (hτ p 1).2.2 D hS hprime (hslot p p.property) t T Z sigma D0 cLog hT hZ hsigma j
  have h6 := (hτ p 2).2.2 D hS hprime (hslot p p.property) t T Z sigma D0 cLog hT hZ hsigma j
  simpa only [errorEnergy,Finset.sum_add_distrib,Fin.sum_univ_three,
    show errorIndex 0=0 from rfl,show errorIndex 1=5 from rfl,show errorIndex 2=6 from rfl,Nat.reduceAdd] using
    add_le_add (add_le_add h0 h5) h6


end OAI.SevenEighths.Angular.PlainRows.Amplification

#print axioms OAI.SevenEighths.Angular.PlainRows.Amplification.exists_pool_error_families
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.Amplification.exists_pool_error_families
