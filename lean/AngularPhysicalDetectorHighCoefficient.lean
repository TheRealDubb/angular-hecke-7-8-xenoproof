import AngularCharacter
import OAI.NumberTheory.DirichletL.Detector.HighSeries
import OAI.NumberTheory.DirichletL.Detector.SourcePrimeFactor

/- Actual angular target in the calibrated physical HIGH coefficients.
Only multiplicativity and norm <= 1 are used for the target. Finite-order
claims about the target are neither assumed nor imported into these proofs. -/
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
noncomputable section
open scoped Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein ProbePhase ProbeEuler ProbePrimePower ProbeRow
open ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev targetMonoid (η : AngularCharacter) : O →*₀ ℂ := η.elementHom

theorem targetMonoid_norm_le_one (η : AngularCharacter) (a : O) :
    ‖targetMonoid η a‖ ≤ 1 := η.norm_elementCoeff_le_one a

def actualACube (η : AngularCharacter) (p : O) : ℂ :=
  star (FiniteGaussPhase.angularFactor p)^3 * (targetMonoid η p)^3

def actualAPhase (η : AngularCharacter) (p : O) : ℂ :=
  star (FiniteGaussPhase.angularFactor p)^6 * (targetMonoid η p)^6

theorem actualACube_sq (η : AngularCharacter) (p : O) :
    (actualACube η p)^2 = actualAPhase η p := by
  unfold actualACube actualAPhase
  ring

theorem actualAPhase_norm_le_one (η : AngularCharacter) (p : O) :
    ‖actualAPhase η p‖ ≤ 1 := by
  simp only [actualAPhase,norm_mul,norm_pow,norm_star]
  exact (mul_le_of_le_one_left (by positivity)
    (pow_le_one₀ (norm_nonneg _) (CompletedGauss.angularFactor_norm_le_one p))).trans
    (pow_le_one₀ (norm_nonneg _) (targetMonoid_norm_le_one η p))

def sourceHighCoefficient (C : CalibrationData) (η : AngularCharacter)
    (I : Ideal O) (hI : primaryGenerator I≠0) (A s : O) (hA : A≠0) (u a : O) : ℂ :=
  actualCongruenceCoefficient C A s hA (u*a^6) * idealRowHom C.generator (Ideal.span {s}) /
    ((Real.sqrt (elementNorm C.generator):ℂ)*C.tau*C.residueMonoid s*star (C.residueMonoid u)) *
    gaussTwo I hI * star (FiniteGaussPhase.angularFactor A * G A) *
    targetMonoid η A * (C.Xi A)⁻¹ * reciprocitySign A s

def bareSourceCoefficient (η : AngularCharacter) (I : Ideal O)
    (hI : primaryGenerator I≠0) (A s : O) (hA : A≠0) (H : O) : ℂ :=
  targetMonoid η A * star (FiniteGaussPhase.angularFactor A) *
    correctedFiniteCoefficient I hI A s hA H

theorem sourceHighCoefficient_eq_bare (S : Finset (Ideal O)) (hS : ∀ P∈S,P.IsMaximal)
    (η : AngularCharacter) (I : Ideal O) (hI : primaryGenerator I≠0)
    (A s : O) (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (u a : O)
    (hH : IsCoprime (calibrationForSet S hS).generator (u*a^6)) :
    sourceHighCoefficient (calibrationForSet S hS) η I hI A s (supportedElement_ne_zero A hA) u a =
      bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) (u*a^6) := by
  let C := calibrationForSet S hS
  have ha : IsCoprime C.generator a :=
    hH.of_isCoprime_of_dvd_right (by refine ⟨u*a^5,?_⟩; ring)
  have hval : C.residueMonoid (u*a^6)=C.residueMonoid u := by
    rw [map_mul,map_pow,calibrationForSet_residue_sixth S hS a ha,mul_one]
  have he := calibration_coefficient_cancel S hS A s hA hs hcop (u*a^6) hH
  dsimp only at he
  dsimp only [C] at hval
  rw [hval] at he
  unfold sourceHighCoefficient bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  simp only [star_mul]
  calc
    _ = (actualCongruenceCoefficient (calibrationForSet S hS) A s (supportedElement_ne_zero A hA) (u*a^6) *
      idealRowHom (calibrationForSet S hS).generator (Ideal.span {s}) /
      ((Real.sqrt (elementNorm (calibrationForSet S hS).generator):ℂ)*(calibrationForSet S hS).tau*
       (calibrationForSet S hS).residueMonoid s*star ((calibrationForSet S hS).residueMonoid u)) *
      ((calibrationForSet S hS).Xi A)⁻¹) *
      (gaussTwo I hI * star (G A) * star (FiniteGaussPhase.angularFactor A) *
        targetMonoid η A * reciprocitySign A s) := by ring
    _ = _ := by rw [he]; ring

theorem bareSourceCoefficient_product (η : AngularCharacter) (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hIJcop : IsCoprime I J)
    (n m s r : O)
    (hc : Supported (Ideal.span {primaryGenerator I})) (hd : Supported (Ideal.span {primaryGenerator J}))
    (hn : Supported (Ideal.span {n})) (hm : Supported (Ideal.span {m}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpc : goodLambda^2∣primaryGenerator I-1) (hpd : goodLambda^2∣primaryGenerator J-1)
    (hpn : goodLambda^2∣n-1) (hpm : goodLambda^2∣m-1)
    (hps : goodLambda^2∣s-1) (hpr : goodLambda^2∣r-1)
    (hcop : IsCoprime ((primaryGenerator I*n^3)*s) ((primaryGenerator J*m^3)*r)) (H : O) :
    let A := primaryGenerator I*n^3
    let B := primaryGenerator J*m^3
    let hA := supportedElement_ne_zero A (supported_completed _ _ hc hn)
    let hB := supportedElement_ne_zero B (supported_completed _ _ hd hm)
    bareSourceCoefficient η (I*J) hIJ.2 (A*B) (s*r) (mul_ne_zero hA hB) H =
      bareSourceCoefficient η I hI.2 A s hA H * bareSourceCoefficient η J hJ.2 B r hB H := by
  have he := correctedFiniteCoefficient_product I J hI hJ hIJ hIJcop n m s r
    hc hd hn hm hs hr hpc hpd hpn hpm hps hpr hcop H
  dsimp only at he ⊢
  unfold bareSourceCoefficient
  rw [he,map_mul,angularFactor_mul,star_mul]
  ring

theorem bareSourceCoefficient_norm_le (η : AngularCharacter)
    (I : Ideal O) (hI : CubicSieve.Admissible I) (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s})) (H : O) :
    ‖bareSourceCoefficient η I hI.2 A s (supportedElement_ne_zero A hA) H‖ ≤
      (Ideal.absNorm (Ideal.span {s}):ℝ)*(Ideal.absNorm (Ideal.span {A}):ℝ) := by
  have hR : ‖reciprocitySign A s‖≤1 := sexticReciprocityPhase_norm A s
  have ht := targetMonoid_norm_le_one η A
  have hfac : ‖targetMonoid η A‖*‖reciprocitySign A s‖≤1 :=
    (mul_le_of_le_one_left (norm_nonneg _) ht).trans hR
  calc
    _ = (‖targetMonoid η A‖*‖reciprocitySign A s‖)*
        ‖bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H‖ := by
      simp only [bareSourceCoefficient, correctedFiniteCoefficient, reciprocityCoefficient,
        norm_mul,norm_star,CubicSieve.gaussTwo_norm_one I hI,
        FiniteGaussPhase.norm_angularFactor A (supportedElement_ne_zero A hA),
        G_norm_one_of_odd A (supported_residue_odd A hA),one_mul,mul_one]
      ring
    _ ≤ ‖bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hfac
    _ ≤ _ := bareCongruenceCoefficient_norm_le A s (supportedElement_ne_zero A hA)
      (supportedElement_ne_zero s hs) H

def bareIdealHighCoefficient (η : AngularCharacter) (u : O) (I J K L : Id) : ℂ :=
  if h : Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported L then
    bareSourceCoefficient η I (supported_primaryGenerator_ne_zero I h.2.1)
      (primaryGenerator I * primaryGenerator J^3) (primaryGenerator K)
      (mul_ne_zero (supported_primaryGenerator_ne_zero I h.2.1)
        (pow_ne_zero _ (supported_primaryGenerator_ne_zero J h.2.2.1)))
      (u*primaryGenerator L^6)
  else 0

theorem bareIdealHighCoefficient_norm_le (η : AngularCharacter) (u : O) (I J K L : Id) :
    ‖bareIdealHighCoefficient η u I J K L‖ ≤ (K.absNorm:ℝ)*(I.absNorm:ℝ)*(J.absNorm:ℝ)^3 := by
  unfold bareIdealHighCoefficient
  split_ifs with h
  · have hi := (supported_span_primaryGenerator_iff I).mpr h.2.1
    have hj := (supported_span_primaryGenerator_iff J).mpr h.2.2.1
    have hk := (supported_span_primaryGenerator_iff K).mpr h.2.2.2.1
    have hb := bareSourceCoefficient_norm_le η I ⟨h.1,supported_primaryGenerator_ne_zero I h.2.1⟩
      (primaryGenerator I*primaryGenerator J^3) (primaryGenerator K)
      (supported_completed _ _ hi hj) hk (u*primaryGenerator L^6)
    rw [← Ideal.span_singleton_mul_span_singleton,← Ideal.span_singleton_pow,
      (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I h.2.1)).1,
      (primaryGenerator_spec J (supported_primaryGenerator_ne_zero J h.2.2.1)).1,
      (primaryGenerator_spec K (supported_primaryGenerator_ne_zero K h.2.2.2.1)).1,
      map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] at hb
    convert hb using 1 ; ring
  · simp only [norm_zero]
    positivity

def bareIdealHighSummand (η : AngularCharacter) (u : O) (x w z : ℂ) (I J K L : Id) : ℂ :=
  bareIdealHighCoefficient η u I J K L * fullIdealWeight (x+1/2) I *
    fullIdealWeight (1+3*x) J * fullIdealWeight w K * fullIdealWeight (6*z) L

lemma fullIdealWeight_nat_scale (s : ℂ) (I : Id) (hI : I≠0) (k : ℕ) :
    (I.absNorm:ℝ)^k * ‖fullIdealWeight s I‖ = ‖fullIdealWeight (s-k) I‖ := by
  have hN : 0<(I.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  simp only [fullIdealWeight,ite_eq_right hI]
  simp only [← Complex.ofReal_natCast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hN,Complex.norm_cpow_eq_rpow_re_of_pos hN]
  simp only [Complex.neg_re,Complex.sub_re,Complex.ofReal_re]
  rw [← Real.rpow_natCast,← Real.rpow_add hN]
  congr 1
  ring

theorem bareIdealHighSummand_norm_le (η : AngularCharacter) (u : O) (x w z : ℂ) (I J K L : Id) :
    ‖bareIdealHighSummand η u x w z I J K L‖ ≤
      ‖fullIdealWeight (x-1/2) I‖ * ‖fullIdealWeight (3*x-2) J‖ *
      ‖fullIdealWeight (w-1) K‖ * ‖fullIdealWeight (6*z) L‖ := by
  by_cases h : Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported L
  · have hb := bareIdealHighCoefficient_norm_le η u I J K L
    calc
      _ ≤ ((K.absNorm:ℝ)*(I.absNorm:ℝ)*(J.absNorm:ℝ)^3) *
          ‖fullIdealWeight (x+1/2) I‖ * ‖fullIdealWeight (1+3*x) J‖ *
          ‖fullIdealWeight w K‖ * ‖fullIdealWeight (6*z) L‖ := by
        simp only [bareIdealHighSummand,norm_mul]
        gcongr
      _ = ((I.absNorm:ℝ)^1*‖fullIdealWeight (x+1/2) I‖) *
          ((J.absNorm:ℝ)^3*‖fullIdealWeight (1+3*x) J‖) *
          ((K.absNorm:ℝ)^1*‖fullIdealWeight w K‖) * ‖fullIdealWeight (6*z) L‖ := by ring
      _ = _ := by
        rw [fullIdealWeight_nat_scale _ I h.2.1.1 1,
          fullIdealWeight_nat_scale _ J h.2.2.1.1 3,
          fullIdealWeight_nat_scale _ K h.2.2.2.1.1 1]
        norm_num only [Nat.cast_one, Nat.cast_ofNat]
        rw [show x+(1/2:ℂ)-1=x-1/2 by ring,show (1:ℂ)+3*x-3=3*x-2 by ring]
  · simp only [bareIdealHighSummand,bareIdealHighCoefficient,dite_eq_right h,zero_mul,norm_zero]
    positivity

theorem bareIdealHighSummand_summable (η : AngularCharacter) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    Summable (fun p : (Id×Id)×(Id×Id) =>
      bareIdealHighSummand η u x w z p.1.1 p.1.2 p.2.1 p.2.2) := by
  have h1 := fullIdealWeight_summable_norm (x-1/2) (by
    simp only [Complex.sub_re,Complex.div_re,Complex.one_re,Complex.one_im,
      show (2:ℂ).re=2 by rfl,show (2:ℂ).im=0 by rfl]
    norm_num
    linarith)
  have h2 := fullIdealWeight_summable_norm (3*x-2) (by
    norm_num [Complex.sub_re,Complex.mul_re]
    linarith)
  have h3 := fullIdealWeight_summable_norm (w-1) (by
    simp only [Complex.sub_re,Complex.one_re]
    linarith)
  have h4 := fullIdealWeight_summable_norm (6*z) (by
    norm_num [Complex.mul_re]
    linarith)
  have h12 := h1.mul_of_nonneg h2 (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)
  have h34 := h3.mul_of_nonneg h4 (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)
  have hall := h12.mul_of_nonneg h34
    (fun _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ hall
  intro p
  simpa only [mul_assoc] using bareIdealHighSummand_norm_le η u x w z p.1.1 p.1.2 p.2.1 p.2.2

def bareIdealHighSeries (η : AngularCharacter) (u : O) (x w z : ℂ) : ℂ :=
  ∑' p : (Id×Id)×(Id×Id), bareIdealHighSummand η u x w z p.1.1 p.1.2 p.2.1 p.2.2

theorem bareSourceCoefficient_prime_formula (η : AngularCharacter) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k j : ℕ) (he : e≤1)
    (hI : primaryGenerator (Ideal.span {p^e})≠0) :
    bareSourceCoefficient η (Ideal.span {p^e}) hI (p^(e+3*l)) (p^k)
      (pow_ne_zero _ hp.ne_zero) (p^j) =
    (-1:ℂ)^e * ((localGamma p hp.ne_zero hg 1)⁻¹)^e * (targetMonoid η p)^e *
      (star (FiniteGaussPhase.angularFactor p)^3 * (targetMonoid η p)^3 *
        star (localGamma p hp.ne_zero hg 3))^l *
      (actualSextic (Ideal.span {p}) hg (-1))^((e+3*l)*k+e*l+l.choose 2) *
      sourceScalar p hp hg (e+3*l) k j := by
  have ho := supported_residue_odd p hs
  have hself := reciprocitySign_self_eq_sextic_neg_one p hp.ne_zero hg hchar ho
  have hstar : star (actualSextic (Ideal.span {p}) hg (-1))=
      actualSextic (Ideal.span {p}) hg (-1) := by
    rw [←hself,reciprocitySign_star]
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [gaussTwo_prime_power_small p hp hg hprimary e he hI,
    bareCongruenceCoefficient_all_prime_powers p hp hg,
    angularFactor_pow,map_pow,
    G_completed_prime_power p ho e l he,
    G_cube_eq_normalizedTraceGauss p hp.ne_zero hg hchar ho,
    reciprocitySign_pow_left p _ (odd_residue_pow p ho k),reciprocitySign_pow_right p p ho,
    hself]
  change _ = _
  simp only [star_mul,star_pow,hstar]
  change (targetMonoid η p)^(e+3*l) * star (FiniteGaussPhase.angularFactor p)^(e+3*l) *
    (localGamma p hp.ne_zero hg 2^e *
      ((actualSextic (Ideal.span {p}) hg (-1))^(e*l+l.choose 2) *
        (star (localGamma p hp.ne_zero hg 3)^l * star (G p)^e)) *
      (((actualSextic (Ideal.span {p}) hg (-1))^k)^(e+3*l) *
        sourceScalar p hp hg (e+3*l) k j)) = _
  calc
    _ = (localGamma p hp.ne_zero hg 2 * star (FiniteGaussPhase.angularFactor p) * star (G p))^e *
      (targetMonoid η p)^e *
      (star (FiniteGaussPhase.angularFactor p)^3*(targetMonoid η p)^3*
        star (localGamma p hp.ne_zero hg 3))^l *
      (actualSextic (Ideal.span {p}) hg (-1))^((e+3*l)*k+e*l+l.choose 2) *
      sourceScalar p hp hg (e+3*l) k j := by
        simp only [pow_add,pow_mul,mul_pow]
        ring
    _ = _ := by
      rw [corrected_prime_cubic_signal p hp.ne_zero hg hchar hprimary hs]
      rw [neg_eq_neg_one_mul ((localGamma p hp.ne_zero hg 1)⁻¹),mul_pow]

theorem bareSourceCoefficient_weighted_prime (η : AngularCharacter) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k m : ℕ) (he : e≤1)
    (hI : primaryGenerator (Ideal.span {p^e})≠0) (x w z : ℂ) :
    bareSourceCoefficient η (Ideal.span {p^e}) hI (p^(e+3*l)) (p^k)
      (pow_ne_zero _ hp.ne_zero) (p^(6*m)) *
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) =
    sourcePrincipalTerm p hp hg (targetMonoid η p) (actualACube η p) x w z e l k m := by
  rw [bareSourceCoefficient_prime_formula η p hp hg hchar hprimary hs e l k (6*m) he hI]
  unfold sourcePrincipalTerm sourceWeightedScalar
  simp only [zpow_neg,zpow_natCast,←inv_pow,Complex.ofReal_natCast]
  have hpdiag := source_signed_phase
    (actualACube η p*star (localGamma p hp.ne_zero hg 3))
    (actualSextic (Ideal.span {p}) hg (-1)) (actualSextic_neg_one_sq _ hg) e l k
  simp only [localCubePhase] at hpdiag
  have ha : actualACube η p=
      star (FiniteGaussPhase.angularFactor p)^3*(targetMonoid η p)^3 := rfl
  rw [ha] at hpdiag ⊢
  calc
    _ = ((-1:ℂ)^e*((localGamma p hp.ne_zero hg 1)⁻¹)^e*(targetMonoid η p)^e) *
      ((star (FiniteGaussPhase.angularFactor p)^3*(targetMonoid η p)^3*
        star (localGamma p hp.ne_zero hg 3))^l *
        (actualSextic (Ideal.span {p}) hg (-1))^((e+3*l)*k+e*l+l.choose 2)) *
      sourceScalar p hp hg (e+3*l) k (6*m) *
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) := by ring
    _ = _ := by rw [←hpdiag]; ring

end
end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.sourceHighCoefficient_eq_bare

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.bareIdealHighSummand_summable

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.bareSourceCoefficient_weighted_prime
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.bareSourceCoefficient_weighted_prime
