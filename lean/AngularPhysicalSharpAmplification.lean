import AngularPhysicalRadicalChildren
import AngularPhysicalActiveAmplification
import OAI.NumberTheory.DirichletL.Moments.AmplificationRadicalChoice
noncomputable section
set_option maxHeartbeats 1000000
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.AmplifiedRadical
open AngularRowClosure ChildRows CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentAmplificationShortening CenteredMomentFixedRay
open CenteredMomentAmplificationGlobal
open CenteredMomentSourceRow CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceSmoothedAllocation CenteredMomentGaussNormalization
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationErrorPool CenteredMomentAmplificationSourceDomain
open CenteredMomentAmplificationChildEnergy CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationLiveMask CenteredMomentAddedZeroUniform
open CenteredMomentSourceProfileMass CenteredMomentSourceMass CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationFamily
  (amplificationPhase amplificationPhase_expansion amplificationPhase_norm)
open CenteredMomentAmplificationActiveFamily (actual_error_energy_active)
local notation "O" => ActualEisensteinCubic.O
local instance angularSuccessorSharpAmplificationSumDecEq {ι:Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

open PlainRows PlainRows.Amplification PlainRows.ChildInputs
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationEligibility CenteredMomentPrimeElements
open Filter
open CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstScale
open CenteredMomentPrimePool
open CenteredMomentAmplificationEnergy (errorEnergy)
theorem childEnergy_radius_le {ι : Type*} [Fintype ι]
    (D : OriginalData ι) (τ : RayFourExpansion.RayCharacter→AngularCharacter) (p : O) (n : ℕ)
    (t T Y V : ℝ) (hT : 0≤T) (hY : 0<Y) (hV : 0<V) (hscale : 2*Y≤V) :
    originalChildEnergy D τ p n t T Y≤originalChildEnergy D τ p n t T V := by
  unfold originalChildEnergy
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (by positivity) (localErrorCost_nonneg p n))
  apply div_le_div_of_nonneg_right _ (div_nonneg hT (by positivity))
  apply Finset.sum_le_sum
  intro χ _
  apply Finset.sum_le_sum
  intro B _
  exact sourceGaussEnergy_radius_le _ _ _ Y V hY hV hscale

theorem child_energy_common {ι : Type*} [Fintype ι]
    (D : OriginalData ι) (τ : RayFourExpansion.RayCharacter→AngularCharacter) (p : O) (n : ℕ)
    (t T Z d K0 j c sigma δ reserve : ℝ) (hT : 0≤T) (hZ : 1<Z) (hδ : 0≤δ)
    (hj : j≤K0+δ) (hreserve : 2≤Z^reserve) :
    originalChildEnergy D τ p n t T (Z^(j+errorGain (d+K0-j) c sigma Z p (n+1)))≤
      originalChildEnergy D τ p n t T (errorCommonRadius Z d K0 c sigma δ reserve p (n+1)) := by
  apply childEnergy_radius_le D τ p n t T _ _ hT
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  exact doubled_radius_le Z _ _ reserve hZ
    (error_exponent_envelope d K0 j c sigma δ Z p (n+1) hδ hj) hreserve

theorem errorCommonRadius_six (Z d K0 c sigma δ reserve : ℝ) (p : O) :
    errorCommonRadius Z d K0 c sigma δ reserve p 6=
      Z^(K0+max (d-c-2*errorRemoval p Z 6) 0+sigma+δ+reserve) := by
  simp only [errorCommonRadius,errorMoving,ite_true,add_zero]

open CenteredMomentFirstScale

theorem retained_nominal_upper (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi : ℝ) (hK : 0<K) (hX : 0<X) (hZ : 1<Z)
    (hC : 0<Csec) (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n) :
    Real.logb Z (dyadicScale n)≤nominalLog I J E K X Z+frequencyLoss Z Csec xi := by
  apply retained_first_dyad_enclosure Tsec Z Csec (nominalLog I J E K X Z) xi hZ hC _ n hn
  rw [nominalLog,Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
    (firstNominalScale_pos I J E hE K X hK hX)]
  exact hsec

theorem exists_pool_error_families {ι : Type*} [Fintype ι]
    (P : Finset (Ideal O)) (hP : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (η : AngularCharacter) (m : O) (hm : m≠0) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) :
    ∃ τ : (elementPool P) → Fin 3 → RayCharacter → AngularCharacter,
      (∀ p i χ,(τ p i χ).k=η.k) ∧
      (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
        radicalBound (childCharacter η χ) m p.val (errorMovingExponent (errorIndex i))) ∧
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
    exact AmplifiedRadical.exists_original_error_ball_family (ι:=ι) η m p hm hd.1 hPid hd.2.2.2.1
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

theorem eventually_original_source_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : AngularCharacter) (m : O),m≠0 → goodLambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → AngularCharacter,
        (∀ p i χ,(τ p i χ).k=η.k) ∧
      (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) m p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,∀ I∈D.S (Sum.inl i),D.slot i ((Ideal.absNorm I:ℝ)/D.lengths i)≠0) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤Z^BR → (Ideal.absNorm D.s:ℝ)≤Z^Bs →
          ∀ (t T D0 cLog : ℝ),0<T → ∀ (j : ℤ),Real.logb Z (dyadicScale j)≤Mmax →
          (∑' h : O,dyadicWeight j (normValue h)*
            ‖gaussPolynomial Finset.univ (sourceGenerator D.columns)
              (sourceGenerator_supported D.columns) (originalCoefficient D η m t T) h‖^2)≤
            (8/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (originalCoefficient D η m t T) ballProfile
                  (Z^(Real.logb Z (dyadicScale j)+mainGain D0 cLog sigma))).re+
                ∑p : elementPool P,∑i : Fin 3,originalChildEnergy D (τ p i) p (errorIndex i) t T
                  (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (errorIndex i+1)))) := by
  filter_upwards [eventually_dyadic_amplification M H hH Sbad hbad sigma loss BR Bs Mmax b eta
    hsigma hloss hM hgap] with Z hz
  obtain ⟨hZ,hP,hcard,hsep,hdata,hamp⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hk,hN,herr⟩ := exists_pool_error_families (ι:=ι) _
    (fun Q hQ => (hdata Q hQ).1) (fun Q hQ => (hdata Q hQ).2.1) η m hm hmLam hm2
  refine ⟨τ,hk,hN,?_⟩
  intro D hS hprime hslot hsupp z hz hlen hR0 hs0 hR hs t T D0 cLog hT j hK
  have hcop (p : O) (hp : p∈elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3)))) :
      ∀i,∀I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I := by
    have hd := elementPool_data _ (fun Q hQ => (hdata Q hQ).1)
      (fun Q hQ => (hdata Q hQ).2.1) p hp
    exact original_slot_coprime D Z sigma b eta hZ.le hb hsep z hz hlen hsupp hslot hprime
      (Ideal.span {p}) (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
  have he := herr D hS hprime hcop t T Z sigma D0 cLog hT hZ hsigma.le j
  apply (hamp Finset.univ (sourceGenerator D.columns) (sourceGenerator_supported D.columns)
    (originalCoefficient D η m t T) D.R D.s hR0 hs0 hR hs j hK D0 cLog).trans
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl he) (by positivity)

theorem eventually_original_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : AngularCharacter) (m : O),m≠0 → goodLambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → AngularCharacter,
        (∀ p i χ,(τ p i χ).k=η.k) ∧
      (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) m p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤Z^BR → (Ideal.absNorm D.s:ℝ)≤Z^Bs →
          ∀ (t T D0 cLog : ℝ),0<T → ∀ (j : ℤ),Real.logb Z (dyadicScale j)≤Mmax →
          (∑' h : O,dyadicWeight j (normValue h)*
            ‖gaussPolynomial Finset.univ (sourceGenerator D.columns)
              (sourceGenerator_supported D.columns) (originalCoefficient D η m t T) h‖^2)≤
            (8/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (originalCoefficient D η m t T) ballProfile
                  (Z^(Real.logb Z (dyadicScale j)+mainGain D0 cLog sigma))).re+
                ∑p : elementPool P,∑i : Fin 3,originalChildEnergy D.active (τ p i) p (errorIndex i) t T
                  (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (errorIndex i+1)))) := by
  filter_upwards [eventually_original_source_amplification (ι:=ι) M H hH Sbad hbad
    sigma loss BR Bs Mmax b eta hsigma hloss hM hb hgap] with Z hz
  obtain ⟨hZ,hP,hcard,hfam⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hk,hN,henergy⟩ := hfam η m hm hmLam hm2
  refine ⟨τ,hk,hN,?_⟩
  intro D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T D0 cLog hT j hK
  have he := henergy D.active (fun i I hI => hS i I (D.active_subset i hI))
    (fun i I hI => hprime i I (D.active_subset _ hI)) D.active_slot hsupp z hz hlen
    hR0 hs0 hR hs t T D0 cLog hT j hK
  simpa only [PlainRows.Amplification.active_gaussPolynomial D,PlainRows.Amplification.active_gaussEnergy D] using he

theorem eventually_original_amplification_common {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6)
    (hC : 1≤Csec) (hxi : 0≤xi) (hreserve : 0<reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : AngularCharacter) (m : O),m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayFourExpansion.RayCharacter → AngularCharacter,
        (∀ p i χ,(τ p i χ).k=η.k) ∧
      (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) m p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤Z^BR → (Ideal.absNorm D.s:ℝ)≤Z^Bs →
          ∀ (t T d cLog : ℝ),0<T →
          ∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0<K → 0<X →
          Tsec≤Csec*firstNominalScale I J E K X →
          ∀ (j : ℤ),Retained (frequencyRadius Tsec Z xi) j →
          Real.logb Z (dyadicScale j)≤Mmax →
          (∑' h : O,dyadicWeight j (normValue h)*
            ‖gaussPolynomial Finset.univ (sourceGenerator D.columns)
              (sourceGenerator_supported D.columns) (originalCoefficient D η m t T) h‖^2)≤
            (8/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (originalCoefficient D η m t T) ballProfile
                  (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z Csec xi) reserve)).re+
                ∑p : elementPool P,∑i : Fin 3,originalChildEnergy D.active (τ p i) p (errorIndex i) t T
                  (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z Csec xi) reserve p (errorIndex i+1))) := by
  filter_upwards [eventually_original_amplification (ι:=ι) M H hH Sbad hbad
    sigma loss BR Bs Mmax b eta hsigma hloss hM hb hgap,
    eventually_support_reserve reserve hreserve] with Z hz hsupport
  obtain ⟨hZ,hP,hcard,hfam⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hk,hN,henergy⟩ := hfam η m hm hmLam hm2
  refine ⟨τ,hk,hN,?_⟩
  intro D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T d cLog hT
    I J E hE K X Tsec hK hX hsec j hj hMdyad
  let K0 := nominalLog I J E K X Z
  let kdyad := Real.logb Z (dyadicScale j)
  have henclose : kdyad≤K0+frequencyLoss Z Csec xi :=
    retained_nominal_upper I J E hE K X Z Csec Tsec xi hK hX hZ
      (zero_lt_one.trans_le hC) hsec j hj
  have hδ := frequencyLoss_nonneg Z Csec xi hZ hC hxi
  have he := henergy D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T
    (d+K0-kdyad) cLog hT j hMdyad
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact main_energy_common _ _ _ _ Z d K0 kdyad cLog sigma _ reserve hZ hδ henclose hsupport.2
  · apply Finset.sum_le_sum
    intro p _
    apply Finset.sum_le_sum
    intro i _
    exact child_energy_common D.active (τ p i) p (errorIndex i) t T Z d K0 kdyad cLog sigma
      _ reserve hT.le hZ hδ henclose hsupport.2


end OAI.SevenEighths.Angular.AmplifiedRadical

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.childEnergy_radius_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.childEnergy_radius_le

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.child_energy_common
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.child_energy_common

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.errorCommonRadius_six
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.errorCommonRadius_six

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.retained_nominal_upper
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.retained_nominal_upper

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.exists_pool_error_families
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.exists_pool_error_families

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.eventually_original_source_amplification
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.eventually_original_source_amplification

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.eventually_original_amplification
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.eventually_original_amplification

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.eventually_original_amplification_common
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.eventually_original_amplification_common
