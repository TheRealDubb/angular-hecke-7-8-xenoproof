import AngularPhysicalAmplificationOriginalErrors
import AngularPhysicalPlainChildSource

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
local instance angularOriginalErrorBallDecEq {κ:Type*} : DecidableEq (κ ⊕ Fin 2) := Classical.decEq _

def originalCoefficient {ι:Type*} [instι:Fintype ι] (D:OriginalData ι)
    (η:AngularCharacter) (m:O) (t T:ℝ) : supportedColumns D.columns→ℂ :=
  fun I => (Real.sqrt T:ℂ)⁻¹*(D.beta I*rowWeight η m 1 1 t I)

theorem originalCoefficient_eq {ι:Type*} [instι:Fintype ι] (D:OriginalData ι)
    (η:AngularCharacter) (m:O) (t T:ℝ) : originalCoefficient D η m t T=
    fun I:supportedColumns D.columns => (Real.sqrt T:ℂ)⁻¹*(D.beta I*rowWeight η m 1 1 t I) := rfl

theorem exists_original_error_ball_family {ι : Type*} [instι:Fintype ι]
    (η : AngularCharacter) (m p : O) (hm : m≠0) (hp : Prime p)
    [(Ideal.span {p}).IsMaximal] (hPid : Prime (Ideal.span {p}))
    (hs : Supported (Ideal.span {p})) (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hpp : goodLambda^2∣p-1)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → AngularCharacter,
      (∀ χ,(τ χ).k=η.k) ∧
      (∀ χ,(τ χ).modulus.absNorm≤rowConductorBound (childCharacter η χ) m 1 (p^(2*errorMovingExponent n))) ∧
      ∀ (D : OriginalData ι),
        (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
        (∀ i,∀ I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I) →
        ∀ (t T Z sigma D0 cLog : ℝ),0<T → 1<Z → 0≤sigma → ∀ (j : ℤ),
        (∑ h∈(dyadRows j).filter (fun h => eligible D.R D.s h p),
          ‖amplificationError Finset.univ (sourceGenerator D.columns)
            (sourceGenerator_supported D.columns) (originalCoefficient D η m t T)
            (fun I => multiplicity p (sourceGenerator D.columns I)) p (n+1) h‖^2)≤
          originalChildEnergy D τ p n t T
            (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (n+1))) := by
  obtain ⟨τ,hk,hN,hτ⟩ := original_errors_to_children (ι:=ι) η m p hm hp hPid hs hg hc hpp hmLam hm2 n hn
  refine ⟨τ,hk,hN,?_⟩
  intro D hS hprime hslot t T Z sigma D0 cLog hT hZ hsigma j
  have hK : 0<Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (n+1)) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  by_cases he : ((dyadRows j).filter (fun h => eligible D.R D.s h p)).Nonempty
  · obtain ⟨h,hh⟩ := he
    have hsc := (eligible_coprime_divisor D.R D.s h p hPid (Finset.mem_filter.mp hh).2).pow_right (n:=n+1)
    have hfull := hτ D.S hS hprime (fun i I hI => ⟨hS _ _ hI,hslot i I hI⟩) D.R D.s hsc
      D.nu D.slot D.lengths D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂ t T hT
      ((dyadRows j).filter (fun h => eligible D.R D.s h p))
      (fun h hh => eligible_not_dvd_row D.R D.s h p (Finset.mem_filter.mp hh).2)
      ballProfile _ hK (fun _ => ballProfile_nonneg _)
      (fun h hh => dyad_ball_majorant Z hZ j _
        (hsigma.trans (errorGain_bounds D0 cLog sigma Z p (n+1) hsigma).1)
        h (Finset.mem_filter.mp hh).1)
    rw [originalCoefficient_eq]
    dsimp only at hfull
    dsimp only [originalChildEnergy,originalCoefficient,OriginalData.beta,
      OriginalData.columns,OriginalData.profile]
    exact hfull
  · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]
    exact originalChildEnergy_nonneg D τ p n t T _ hT.le hK


end OAI.SevenEighths.Angular.PlainRows.Amplification

#print axioms OAI.SevenEighths.Angular.PlainRows.Amplification.exists_original_error_ball_family
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.Amplification.exists_original_error_ball_family
