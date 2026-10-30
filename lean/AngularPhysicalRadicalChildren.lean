import AngularPhysicalAmplifiedRadicalFamily
import AngularPhysicalOriginalErrorBall
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
variable {ι:Type*} [instι:Fintype ι]
local instance successorRadicalErrorsDecEq : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

open PlainRows PlainRows.Amplification PlainRows.ChildInputs
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationEligibility CenteredMomentPrimeElements
theorem original_errors_to_children (η : AngularCharacter) (m p : O)
    (hm : m≠0) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hPid : Prime (Ideal.span {p})) (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (hpp : goodLambda^2 ∣ p-1) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → AngularCharacter,
      (∀ χ,(τ χ).k=η.k) ∧
      (∀ χ,(τ χ).modulus.absNorm≤radicalBound (childCharacter η χ) m p (errorMovingExponent n)) ∧
      ∀ (S : (ι ⊕ Fin 2) → Finset (Ideal O)),
      (∀ i,∀ I∈S i,I≠0) → (∀ i,∀ I∈S (Sum.inl i),Prime I) →
      (∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime (Ideal.span {p}) I) →
      ∀ (R s : Ideal O),IsCoprime s ((Ideal.span {p})^(n+1)) →
      ∀ (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
        (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (t T : ℝ),0<T →
      ∀ (rows : Finset O),(∀ h∈rows,¬p∣h) →
      ∀ (W : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (∀ z∈rows,1≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let β := finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
      let C := (Ideal.span {p})^(n+1)
      (∑ h∈rows,‖amplificationError Finset.univ
        (sourceGenerator (finiteColumns (Fintype.piFinset S)))
        (sourceGenerator_supported (finiteColumns (Fintype.piFinset S)))
        (fun I : supportedColumns (finiteColumns (Fintype.piFinset S)) =>
          (Real.sqrt T:ℂ)⁻¹*(β I*rowWeight η m 1 1 t I))
        (fun I => multiplicity p (sourceGenerator (finiteColumns (Fintype.piFinset S)) I)) p (n+1) h‖^2)≤
        (16*(n+2:ℝ)*localErrorCost p n) *
          ((∑ χ : RayCharacter,∑ B : actualAllocations S C,
            (sourceGaussEnergy
              (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
              (finiteColumnCoefficient
                (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
                (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
              (heightCoeff (τ χ) t) W K).re) /
            (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1))) := by
  obtain ⟨τ,hk,hN,hτ⟩ := AmplifiedRadical.exists_actual_error_family η m p hm hp hs hpp hmLam hm2 n hn
  refine ⟨τ,hk,hN,?_⟩
  intro S hS hprime hslot R s hsc ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ t T hT rows hrows W K hK hW hmajor
  dsimp only
  let β := finiteColumnCoefficient (Fintype.piFinset S)
    (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
  let S₀ := finiteColumns (Fintype.piFinset S)
  let C := (Ideal.span {p})^(n+1)
  let Q := residualColumns S₀ p hp (n+1)
  let T' := T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)
  have hC : C≠0 := pow_ne_zero _ hs.1
  have ht : 0<T' := by
    apply div_pos hT
    apply pow_pos
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs.1)
  have he := finite_original_error_energy S₀ (fun I => β I*rowWeight η m 1 1 t I)
    p hp hs hg hc hpp n hn T hT rows hrows W K hK hW hmajor
  have hf := hτ S₀ C hC β t W K hK hW
  have hb (χ : RayCharacter) :
      (sourceGaussEnergy Q (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re≤
        (n+2:ℝ)*∑ B : actualAllocations S C,
          (sourceGaussEnergy
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
            (heightCoeff (τ χ) t) W K).re := by
    have hpool := residual_energy_eq_punctured S₀ β (heightCoeff (τ χ) t) p hp hs hpp (n+1) (by omega) W K
    change _≤_
    rw [hpool]
    have hchild := actual_amplification_child_energy S hS hprime (Ideal.span {p}) R s hPid hs (n+1)
      hslot hsc ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ (heightCoeff (τ χ) t) W K hK hW
    have hcount : ((n+1:ℕ):ℝ)+1=(n+2:ℝ) := by push_cast; ring
    rw [hcount] at hchild
    exact hchild
  apply he.trans
  apply (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
    (hf.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _ => hb χ)) (by norm_num))) ht.le)
    (localErrorCost_nonneg p n)).trans_eq
  rw [←Finset.mul_sum]
  ring


theorem exists_original_error_ball_family {ι : Type*} [instι:Fintype ι]
    (η : AngularCharacter) (m p : O) (hm : m≠0) (hp : Prime p)
    [(Ideal.span {p}).IsMaximal] (hPid : Prime (Ideal.span {p}))
    (hs : Supported (Ideal.span {p})) (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hpp : goodLambda^2∣p-1)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → AngularCharacter,
      (∀ χ,(τ χ).k=η.k) ∧
      (∀ χ,(τ χ).modulus.absNorm≤radicalBound (childCharacter η χ) m p (errorMovingExponent n)) ∧
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
  obtain ⟨τ,hk,hN,hτ⟩ := AmplifiedRadical.original_errors_to_children (ι:=ι) η m p hm hp hPid hs hg hc hpp hmLam hm2 n hn
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



end OAI.SevenEighths.Angular.AmplifiedRadical

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.original_errors_to_children
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.original_errors_to_children

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.exists_original_error_ball_family
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.exists_original_error_ball_family
