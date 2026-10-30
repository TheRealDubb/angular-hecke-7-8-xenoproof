import AngularPhysicalSharpAmplification
import OAI.NumberTheory.DirichletL.Moments.FirstAnnularGeometry
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
local instance angularSuccessorSharpAnnularSumDecEq {ι:Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

open PlainRows PlainRows.Amplification PlainRows.ChildInputs
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationEligibility CenteredMomentPrimeElements
open Filter
open CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstScale
open CenteredMomentPrimePool
theorem eventually_annular_amplification_common {ι : Type*} [Fintype ι]
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
          ∀ (H0 : ℝ),0<H0 → H0≤4*frequencyRadius Tsec Z xi →
          8*H0≤Z^Mmax →
          (gaussEnergy Finset.univ (sourceGenerator D.columns)
            (sourceGenerator_supported D.columns) (originalCoefficient D η m t T)
            CenteredMomentFirstAnnularMajorant.profile H0).re≤
            (56/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (originalCoefficient D η m t T) ballProfile
                  (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z (32*Csec) xi) reserve)).re+
                ∑p : elementPool P,∑i : Fin 3,originalChildEnergy D.active (τ p i) p (errorIndex i) t T
                  (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))) := by
  filter_upwards [AmplifiedRadical.eventually_original_amplification_common
    (ι:=ι) M H hH Sbad hbad sigma loss BR Bs Mmax b eta (32*Csec) xi reserve
    hsigma hloss hM hb hgap (by linarith) hxi hreserve] with Z hz
  obtain ⟨hZ,hP,hcard,hfam⟩:=hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hk,hN,henergy⟩:=hfam η m hm hmLam hm2
  refine ⟨τ,hk,hN,?_⟩
  intro D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T d cLog hT
    I J E hE K X Tsec hK hX hsec H0 hH0 houter hcap
  have hsec' :32*Tsec≤(32*Csec)*firstNominalScale I J E K X:=by nlinarith
  have hfreq:8*H0≤frequencyRadius (32*Tsec) Z xi:=by
    unfold frequencyRadius at houter ⊢
    nlinarith
  have hbnd:=CenteredMomentFirstAnnularGeometry.common_bound_auto Finset.univ
    (sourceGenerator D.columns) (sourceGenerator_supported D.columns)
    (originalCoefficient D η m t T) H0 _ hH0 (fun j hj=>
      henergy D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T d cLog hT
        I J E hE K X (32*Tsec) hK hX hsec' j
        (CenteredMomentFirstAnnularGeometry.bands_retained H0 _ hH0 hfreq j hj)
        (CenteredMomentFirstAnnularGeometry.bands_log_cap H0 Z Mmax hH0 hZ hcap j hj))
  convert hbnd using 1 ; ring


end OAI.SevenEighths.Angular.AmplifiedRadical

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.eventually_annular_amplification_common
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.eventually_annular_amplification_common
