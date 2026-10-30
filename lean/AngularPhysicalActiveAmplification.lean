import AngularPhysicalOriginalAmplification

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
local instance angularActiveAmplificationDecEq {κ:Type*} : DecidableEq (κ ⊕ Fin 2) := Classical.decEq _

variable {ι:Type*} [instι:Fintype ι]

theorem active_gaussPolynomial (D : OriginalData ι) (η : AngularCharacter) (m : O)
    (t T : ℝ) (h : O) :
    gaussPolynomial Finset.univ (sourceGenerator D.active.columns)
      (sourceGenerator_supported D.active.columns) (originalCoefficient D.active η m t T) h=
    gaussPolynomial Finset.univ (sourceGenerator D.columns)
      (sourceGenerator_supported D.columns) (originalCoefficient D η m t T) h := by
  unfold originalCoefficient
  rw [D.active_beta]
  rw [CenteredMomentLiveDomain.source_gaussPolynomial D.active.columns
    (fun I => (Real.sqrt T:ℂ)⁻¹*(D.beta I*rowWeight η m 1 1 t I)) h,
    CenteredMomentLiveDomain.source_gaussPolynomial D.columns
    (fun I => (Real.sqrt T:ℂ)⁻¹*(D.beta I*rowWeight η m 1 1 t I)) h]
  apply Finset.sum_subset (Finset.filter_subset_filter _ D.active_columns_subset)
  intro I hI hn
  have hz : D.beta I=0 := by
    by_contra hne
    have hm := CenteredMomentLiveDomain.finite_column_mem
      (Fintype.piFinset D.active.S) D.active.profile I
      (by change D.active.beta I≠0;rw [D.active_beta];exact hne)
    exact hn (Finset.mem_filter.mpr ⟨hm,(Finset.mem_filter.mp hI).2⟩)
  rw [hz,zero_mul,mul_zero,zero_mul]

theorem active_gaussEnergy (D : OriginalData ι) (η : AngularCharacter) (m : O)
    (t T : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    gaussEnergy Finset.univ (sourceGenerator D.active.columns)
      (sourceGenerator_supported D.active.columns) (originalCoefficient D.active η m t T) W K=
    gaussEnergy Finset.univ (sourceGenerator D.columns)
      (sourceGenerator_supported D.columns) (originalCoefficient D η m t T) W K := by
  unfold gaussEnergy
  simp_rw [active_gaussPolynomial D]

theorem eventually_original_amplification {ι : Type*} [instι:Fintype ι]
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
          rowConductorBound (childCharacter η χ) m 1 (p.val^(2*errorMovingExponent (errorIndex i)))) ∧
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
  simpa only [active_gaussPolynomial D,active_gaussEnergy D] using he

open CenteredMomentFirstScale CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstExtractedLedger
open CenteredMomentDescentLedger CenteredMomentCommonSupport
open CenteredMomentFirstColumns CenteredMomentRankinRadical ActualEisensteinCubic


end OAI.SevenEighths.Angular.PlainRows.Amplification

#print axioms OAI.SevenEighths.Angular.PlainRows.Amplification.eventually_original_amplification
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.Amplification.eventually_original_amplification
