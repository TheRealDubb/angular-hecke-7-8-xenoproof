import AngularPhysicalFirstZeroDictionary
import AngularPhysicalPlainSummability
import OAI.NumberTheory.DirichletL.Moments.SupportedZeroEnergy

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows
open CanonicalQuadraticSieve CanonicalRowCompletion IdealMobiusDivisorSum
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentZeroMode
open CenteredMomentSourceRow (supportedColumns)
open CenteredMomentSupportedZeroEnergy (activeColumns activeColumns_supported finiteColumnCoefficient_witness finiteColumnCoefficient_norm_le)
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

theorem active_tuple_zero_energy_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (η : AngularCharacter) (m A : O) (t : ℝ) (S : Finset (Tuple ι))
        (β : Tuple ι → ℂ) (W : 𝓢(ℝ,ℂ)) (X K B : ℝ),
      1≤X → 0≤K → 0≤B →
      (∀ v∈S,finiteTupleProduct v≠0 → ‖β v‖≤B) →
      (∀ I∈supportedColumns (finiteColumns S),finiteColumnCoefficient S β I≠0 →
        (Ideal.absNorm I:ℝ)≤X) →
      ‖zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) W K‖ ≤
        C*K*B^2*‖paperRadialFourier W 0‖*X^(1+ε) := by
  let δ := ε/(4*(N+2:ℕ))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hn : (N+2:ℝ)≠0 := by positivity
  have hδn : δ*(N+2:ℕ)=ε/4 := by dsimp [δ]; push_cast; field_simp
  obtain ⟨D,hD,hd⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  obtain ⟨C,hC,hc⟩ := ideal_zero_energy_bound (ε/2) (by positivity)
  refine ⟨C*((1+D)^(N+2))^2,by positivity,?_⟩
  intro ι _ hi η m A t S β W X K B hX hK hB hβ hN
  let c := finiteColumnCoefficient S β
  let Q := activeColumns (finiteColumns S) c
  have hQ : ∀ I∈Q,Supported I := activeColumns_supported _ _
  have hX0 : 0<X := zero_lt_one.trans_le hX
  have hNX (I : Ideal O) (hI : I∈Q) : (Ideal.absNorm I:ℝ)≤X :=
    hN I (Finset.mem_filter.mp hI).1 (Finset.mem_filter.mp hI).2
  have hbase : 1≤(1+D)*X^δ := by
    have hxδ : 1≤X^δ := Real.one_le_rpow hX hδ.le
    nlinarith
  have hcoeff (I : Ideal O) (hI : I∈Q) :
      ‖c I*rowWeight η m A 1 t I‖ ≤ B*((1+D)^(N+2)*X^(ε/4)) := by
    have hI0 := (hQ I hI).1
    have hdI : ((idealDivisors I).card:ℝ) ≤ (1+D)*X^δ := by
      apply (hd I hI0).trans
      apply mul_le_mul (by linarith : D≤1+D)
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hNX I hI) hδ.le) (by positivity) (by positivity)
    have hp : ((1+D)*X^δ)^(N+2) = (1+D)^(N+2)*X^(ε/4) := by
      rw [mul_pow,←Real.rpow_mul_natCast hX0.le,hδn]
    rw [norm_mul]
    calc
      _ ≤ ‖c I‖*1 := mul_le_mul_of_nonneg_left
        (row_twisted_coefficient_norm η m A 1 t I hI0) (norm_nonneg _)
      _ = ‖c I‖ := mul_one _
      _ ≤ B*((idealDivisors I).card:ℝ)^(Fintype.card ι+2) :=
        finiteColumnCoefficient_norm_le S β B hB hβ I hI0
      _ ≤ B*((1+D)*X^δ)^(Fintype.card ι+2) := by gcongr
      _ ≤ B*((1+D)*X^δ)^(N+2) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (by omega)) hB
      _ = _ := by rw [hp]
  have hb := hc Q hQ (fun I => c I*rowWeight η m A 1 t I)
    X K (B*((1+D)^(N+2)*X^(ε/4))) hX hK (by positivity) hNX hcoeff
  rw [zeroEnergy_eq_active_original,norm_mul]
  apply (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans_eq
  have hxpow : (X^(ε/4))^2*X^(1+ε/2)=X^(1+ε) := by
    rw [←Real.rpow_mul_natCast hX0.le,←Real.rpow_add hX0]
    congr 1
    ring
  calc
    _ = C*((1+D)^(N+2))^2*K*B^2*‖paperRadialFourier W 0‖*
      ((X^(ε/4))^2*X^(1+ε/2)) := by ring
    _ = _ := by rw [hxpow]

theorem normalized_active_tuple_zero_energy_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (η : AngularCharacter) (m A : O) (t : ℝ) (S : Finset (Tuple ι))
        (β : Tuple ι → ℂ) (W : 𝓢(ℝ,ℂ)) (X K B : ℝ),
      1≤X → 0≤K → 0≤B →
      (∀ v∈S,finiteTupleProduct v≠0 → ‖β v‖≤B) →
      (∀ I∈supportedColumns (finiteColumns S),finiteColumnCoefficient S β I≠0 →
        (Ideal.absNorm I:ℝ)≤X) →
      ‖((X⁻¹:ℝ):ℂ)*zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) W K‖ ≤
        C*K*B^2*‖paperRadialFourier W 0‖*X^ε := by
  obtain ⟨C,hC,hc⟩ := active_tuple_zero_energy_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ hi η m A t S β W X K B hX hK hB hβ hN
  have hX0 : 0<X := zero_lt_one.trans_le hX
  have hb := hc hi η m A t S β W X K B hX hK hB hβ hN
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hX0)]
  apply (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hX0.le)).trans_eq
  rw [Real.rpow_add hX0,Real.rpow_one]
  field_simp

theorem normalized_supported_tuple_zero_energy_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (η : AngularCharacter) (m A : O) (t : ℝ) (S : Finset (Tuple ι))
        (β : Tuple ι → ℂ) (W : 𝓢(ℝ,ℂ)) (X K B : ℝ),
      1≤X → 0≤K → 0≤B →
      (∀ v∈S,‖β v‖≤B) →
      (∀ v∈S,β v≠0 → (Ideal.absNorm (finiteTupleProduct v):ℝ)≤X) →
      ‖((X⁻¹:ℝ):ℂ)*zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) W K‖ ≤
        C*K*B^2*‖paperRadialFourier W 0‖*X^ε := by
  obtain ⟨C,hC,hc⟩ := normalized_active_tuple_zero_energy_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ hi η m A t S β W X K B hX hK hB hβ hN
  apply hc hi η m A t S β W X K B hX hK hB (fun v hv _ => hβ v hv)
  intro I _ hI
  obtain ⟨v,hv,hne,he⟩ := finiteColumnCoefficient_witness S β I hI
  rw [←he]
  exact hN v hv hne

end OAI.SevenEighths.Angular.PlainRows

#print axioms OAI.SevenEighths.Angular.PlainRows.active_tuple_zero_energy_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.active_tuple_zero_energy_bound

#print axioms OAI.SevenEighths.Angular.PlainRows.normalized_active_tuple_zero_energy_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.normalized_active_tuple_zero_energy_bound

#print axioms OAI.SevenEighths.Angular.PlainRows.normalized_supported_tuple_zero_energy_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.normalized_supported_tuple_zero_energy_bound
