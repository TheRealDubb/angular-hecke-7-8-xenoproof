import AngularPhysicalSecondSourceZero

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.PlainRows.SecondSource
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentLiveDomain
open CenteredMomentOriginalChildEnergy CenteredMomentFirstSectors CenteredMomentCommonSectors
open IdealMobiusDivisorSum ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentFourier CenteredMomentPoisson CenteredMomentSupportedCorrelation
open CenteredMomentRowNorm CenteredMomentSecondDiagonal
open CenteredMomentSecondSourceEnergy (secondSourceKernel)
open CenteredMomentSecondSourcePoisson (secondSourceKernel_poisson)
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceZeroEnergy CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceSecondZeroEnergy
  (secondZeroEnergy_filter sourceGenerator_span sourceGenerator_primary sourceGenerator_injective
   profileCoefficient_dvd)
local notation "O" => ActualEisensteinCubic.O
theorem tuple_second_zero_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (S : Finset (Tuple ι)) (β : Tuple ι→ℂ) (η : AngularCharacter) (t B Y : ℝ),
      0≤B → 1≤Y → (∀ v∈S,finiteTupleProduct v≠0→‖β v‖≤B) →
      ∀ (s : Ideal O),s≠0 →
      (∀ v∈S,β v≠0→s∣finiteTupleProduct v) →
      (∀ v∈S,β v≠0→(Ideal.absNorm (finiteTupleProduct v):ℝ)≤Y) →
      ‖sourceSecondZero (finiteColumns S) (finiteColumnCoefficient S β) η t‖≤
        C*B^2*Y^(1+ε)/(Ideal.absNorm s:ℝ) := by
  let δ := ε/(2*(N+2:ℕ))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδn : δ*(N+2:ℕ)=ε/2 := by dsimp [δ]; push_cast; field_simp
  obtain ⟨D,hD,hd⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨128*((1+D)^(N+2))^2,by positivity,?_⟩
  intro ι _ hi S β η t B Y hB hY hβ s hs hdiv hN
  let c := finiteColumnCoefficient S β
  have hY0 : 0<Y := zero_lt_one.trans_le hY
  have hbound (I : Ideal O) (hI : I∈supportedColumns (finiteColumns S)) (hn : c I≠0) :
      (Ideal.absNorm I:ℝ)≤Y := by
    obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
    rw [←he]
    exact hN v hv hv0
  have hbase : 1≤(1+D)*Y^δ := by
    have hp := Real.one_le_rpow hY hδ.le
    nlinarith
  have hcoeff (I : Ideal O) (hI : I∈supportedColumns (finiteColumns S)) (hn : c I≠0) :
      ‖c I‖≤B*((1+D)^(N+2)*Y^(ε/2)) := by
    have hI0 := (Finset.mem_filter.mp hI).2.1
    have hdI : ((IdealMobiusDivisorSum.idealDivisors I).card:ℝ)≤(1+D)*Y^δ :=
      (hd I hI0).trans (mul_le_mul (by linarith)
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hbound I hI hn) hδ.le) (by positivity) (by positivity))
    have hp : ((1+D)*Y^δ)^(N+2)=(1+D)^(N+2)*Y^(ε/2) := by
      rw [mul_pow,←Real.rpow_mul_natCast hY0.le,hδn]
    calc
      _ ≤ B*((IdealMobiusDivisorSum.idealDivisors I).card:ℝ)^(Fintype.card ι+2) :=
        finiteColumnCoefficient_norm_le S β B hB hβ I hI0
      _ ≤ B*((1+D)*Y^δ)^(Fintype.card ι+2) := by gcongr
      _ ≤ B*((1+D)*Y^δ)^(N+2) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (by omega)) hB
      _ = _ := by rw [hp]
  have hb := sourceSecondZero_divisor_bound (finiteColumns S) c η t
    (B*((1+D)^(N+2)*Y^(ε/2))) Y (by positivity) hY0.le s hs hcoeff
    (by
      intro I hI hn
      obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
      rw [←he]
      exact hdiv v hv hv0) hbound
  apply hb.trans_eq
  have hp : (Y^(ε/2))^2*Y=Y^(1+ε) := by
    rw [←Real.rpow_mul_natCast hY0.le]
    norm_num only [Nat.cast_ofNat]
    rw [show ε/2*(2:ℝ)=ε by ring,Real.rpow_add hY0,Real.rpow_one]
    ring
  calc
    _ = (128*((1+D)^(N+2))^2)*B^2*((Y^(ε/2))^2*Y)/(Ideal.absNorm s:ℝ) := by ring
    _ = _ := by rw [hp]

theorem normalized_tuple_second_zero_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (S : Finset (Tuple ι)) (β : Tuple ι→ℂ) (η : AngularCharacter) (t B L T : ℝ),
      0≤B → 0<L → 0<T → (∀ v∈S,finiteTupleProduct v≠0→‖β v‖≤B) →
      ∀ (s : Ideal O),s≠0 →
      (∀ v∈S,β v≠0→s∣finiteTupleProduct v) →
      (∀ v∈S,β v≠0→(Ideal.absNorm (finiteTupleProduct v):ℝ)≤L*T) →
      (L*T<1 → sourceSecondZero (finiteColumns S) (finiteColumnCoefficient S β) η t=0) ∧
      ∀ κ : ℂ,‖(κ/(T:ℂ))*sourceSecondZero (finiteColumns S) (finiteColumnCoefficient S β) η t‖≤
        C*‖κ‖*B^2*L^(1+ε)*T^ε/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := tuple_second_zero_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ hi S β η t B L T hB hL hT hβ s hs hdiv hN
  have hz (hsmall : L*T<1) : sourceSecondZero (finiteColumns S) (finiteColumnCoefficient S β) η t=0 := by
    apply sourceSecondZero_eq_zero_of_subunit _ _ η t (L*T) hsmall
    intro I hI hn
    obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
    rw [←he]
    exact hN v hv hv0
  refine ⟨hz,?_⟩
  intro κ
  by_cases hsmall : L*T<1
  · rw [hz hsmall,mul_zero,norm_zero]
    positivity
  have hb := hbound hi S β η t B (L*T) hB (le_of_not_gt hsmall) hβ s hs hdiv hN
  rw [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hT]
  apply (mul_le_mul_of_nonneg_left hb (div_nonneg (norm_nonneg _) hT.le)).trans_eq
  rw [Real.mul_rpow hL.le hT.le,Real.rpow_add hT,Real.rpow_one]
  field_simp

end OAI.SevenEighths.Angular.PlainRows.SecondSource

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.tuple_second_zero_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.tuple_second_zero_bound

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.normalized_tuple_second_zero_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.normalized_tuple_second_zero_bound
