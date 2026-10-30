import AngularPhysicalDetectorHighCoefficient
import OAI.NumberTheory.DirichletL.Detector.IdealLocalEuler
import OAI.NumberTheory.DirichletL.Detector.HighRowsUnramified
import OAI.NumberTheory.DirichletL.Detector.HighEulerRational

namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
noncomputable section
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein ProbePhase ProbeEuler ProbePrimePower ProbeRow
open ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem bareIdealHighCoefficient_at_prime (η : AngularCharacter) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k m : ℕ) (he : e≤1) :
    bareIdealHighCoefficient η 1 ((Ideal.span {p})^e) ((Ideal.span {p})^l)
      ((Ideal.span {p})^k) ((Ideal.span {p})^m) =
    bareSourceCoefficient η (Ideal.span {p^e})
      (by rw [← Ideal.span_singleton_pow,primaryGenerator_prime_power p hp.ne_zero hprimary e];
          exact pow_ne_zero _ hp.ne_zero)
      (p^(e+3*l)) (p^k) (pow_ne_zero _ hp.ne_zero) (p^(6*m)) := by
  have hguard : Squarefree ((Ideal.span {p})^e) ∧ Supported ((Ideal.span {p})^e) ∧
      Supported ((Ideal.span {p})^l) ∧ Supported ((Ideal.span {p})^k) ∧ Supported ((Ideal.span {p})^m) :=
    ⟨prime_power_small_squarefree p hp e he,supported_pow hs e,supported_pow hs l,supported_pow hs k,supported_pow hs m⟩
  unfold bareIdealHighCoefficient
  rw [dite_eq_left hguard]
  simp only [primaryGenerator_prime_power p hp.ne_zero hprimary,one_mul]
  have hA : p^e*(p^l)^3=p^(e+3*l) := by rw [←pow_mul,Nat.mul_comm l 3,←pow_add]
  have hH : (p^m)^6=p^(6*m) := by rw [←pow_mul,Nat.mul_comm m 6]
  simp only [hA,hH,Ideal.span_singleton_pow]

theorem bareIdealHighSummand_at_prime (η : AngularCharacter) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k m : ℕ) (he : e≤1) (x w z : ℂ) :
    bareIdealHighSummand η 1 x w z ((Ideal.span {p})^e) ((Ideal.span {p})^l)
      ((Ideal.span {p})^k) ((Ideal.span {p})^m) =
    sourcePrincipalTerm p hp hg (targetMonoid η p) (actualACube η p) x w z e l k m := by
  unfold bareIdealHighSummand
  rw [bareIdealHighCoefficient_at_prime η p hp hprimary hs e l k m he]
  have hw := prime_spectral_weights p hp.ne_zero e l k m x w z
  simp only [mul_assoc] at hw ⊢
  rw [hw]
  simpa only [mul_assoc] using
    bareSourceCoefficient_weighted_prime η p hp hg hchar hprimary hs e l k m he _ x w z

def idealHighLocalFactor (η : AngularCharacter) (P : Ideal O) (x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l, ∑' k, ∑' m,
    bareIdealHighSummand η 1 x w z (P^e.val) (P^l) (P^k) (P^m)

theorem idealHighLocalFactor_eq_source (η : AngularCharacter) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (x w z : ℂ) :
    idealHighLocalFactor η (Ideal.span {p}) x w z =
      sourcePrincipalSeries p hp hg (targetMonoid η p) (actualACube η p) x w z := by
  unfold idealHighLocalFactor sourcePrincipalSeries
  apply Finset.sum_congr rfl
  intro e he
  apply tsum_congr
  intro l
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  exact bareIdealHighSummand_at_prime η p hp hg hchar hprimary hs e.val l k m (by omega) x w z

theorem idealHighLocalFactor_euler_identity (η : AngularCharacter) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) ((actualACube η p)^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) (targetMonoid η p) 1 x≠0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    idealHighLocalFactor η (Ideal.span {p}) x w z =
      (1-coordD Q (targetMonoid η p) 1 x) / ((1-coordV Q z)*(1-coordW Q 1 w)) *
        unramifiedClosed Q ((actualACube η p)^2) (targetMonoid η p) 1 x w z := by
  rw [idealHighLocalFactor_eq_source η p hp hg hchar hprimary hs]
  exact sourcePrincipalSeries_euler_identity p hp hg hchar _ _ x w z hV hR hW hD

def idealRowHighLocalFactor (η : AngularCharacter) (u : O) (P : Ideal O) (x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l, ∑' k, ∑' m,
    bareIdealHighSummand η u x w z (P^e.val) (P^l) (P^k) (P^m)

theorem bareSourceCoefficient_unit_frequency (η : AngularCharacter)
    (I : Ideal O) (hI : primaryGenerator I≠0) (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (b H : O) (hcop : IsCoprime b (A*s)) :
    bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) (b*H)=
      ((idealRowHom b (Ideal.span {A}))⁻¹*idealRowHom b (Ideal.span {s}))*
        bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) H := by
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [bareCongruenceCoefficient_unit_frequency A s hA hs b H hcop]
  ring

theorem bareSourceCoefficient_row_prime_formula (η : AngularCharacter) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p)
    (e l k j : ℕ) (he : e≤1) (hI : primaryGenerator (Ideal.span {p^e})≠0) :
    bareSourceCoefficient η (Ideal.span {p^e}) hI (p^(e+3*l)) (p^k)
      (pow_ne_zero _ hp.ne_zero) (b*p^j)=
    ((actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^k /
      (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^(e+3*l)) *
    ((-1:ℂ)^e * ((localGamma p hp.ne_zero hg 1)⁻¹)^e * (targetMonoid η p)^e *
      (star (FiniteGaussPhase.angularFactor p)^3 * (targetMonoid η p)^3 *
        star (localGamma p hp.ne_zero hg 3))^l *
      (actualSextic (Ideal.span {p}) hg (-1))^((e+3*l)*k+e*l+l.choose 2) *
      sourceScalar p hp hg (e+3*l) k j) := by
  rw [bareSourceCoefficient_unit_frequency η _ hI _ _
    (supported_element_power p hs _) (supported_element_power p hs _) b _
    (hb.pow_right.mul_right hb.pow_right),
    bareSourceCoefficient_prime_formula η p hp hg hchar hprimary hs e l k j he hI,
    idealRowHom_prime_power_value p b hg,idealRowHom_prime_power_value p b hg]
  simp only [div_eq_mul_inv]
  ac_rfl

theorem bareSourceCoefficient_row_weighted_prime (η : AngularCharacter) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p) (j e l k m : ℕ) (he : e≤1)
    (hI : primaryGenerator (Ideal.span {p^e})≠0) (x w z : ℂ) :
    bareSourceCoefficient η (Ideal.span {p^e}) hI (p^(e+3*l)) (p^k)
      (pow_ne_zero _ hp.ne_zero) (b*p^(j+6*m)) *
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) =
    sourceRowTerm p hp hg (targetMonoid η p) (actualACube η p)
      (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)) x w z j e l k m := by
  rw [bareSourceCoefficient_row_prime_formula η p hp hg hchar hprimary hs b hb e l k (j+6*m) he hI]
  unfold sourceRowTerm sourceWeightedScalar
  simp only [zpow_neg,zpow_natCast,←inv_pow,Complex.ofReal_natCast]
  have hpdiag := source_signed_phase
    (actualACube η p*star (localGamma p hp.ne_zero hg 3))
    (actualSextic (Ideal.span {p}) hg (-1)) (actualSextic_neg_one_sq _ hg) e l k
  simp only [localCubePhase] at hpdiag
  have ha : actualACube η p=
      star (FiniteGaussPhase.angularFactor p)^3*(targetMonoid η p)^3 := rfl
  rw [ha] at hpdiag ⊢
  linear_combination -((actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^k /
      (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^(e+3*l)) *
    ((-1:ℂ)^e*((localGamma p hp.ne_zero hg 1)⁻¹)^e*(targetMonoid η p)^e) *
    sourceScalar p hp hg (e+3*l) k (j+6*m) *
    (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) * hpdiag

theorem bareIdealHighCoefficient_row_at_prime (η : AngularCharacter) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (u : O) (e l k m : ℕ) (he : e≤1) :
    bareIdealHighCoefficient η u ((Ideal.span {p})^e) ((Ideal.span {p})^l)
      ((Ideal.span {p})^k) ((Ideal.span {p})^m) =
    bareSourceCoefficient η (Ideal.span {p^e})
      (by rw [← Ideal.span_singleton_pow,primaryGenerator_prime_power p hp.ne_zero hprimary e];
          exact pow_ne_zero _ hp.ne_zero)
      (p^(e+3*l)) (p^k) (pow_ne_zero _ hp.ne_zero) (u*p^(6*m)) := by
  have hguard : Squarefree ((Ideal.span {p})^e) ∧ Supported ((Ideal.span {p})^e) ∧
      Supported ((Ideal.span {p})^l) ∧ Supported ((Ideal.span {p})^k) ∧ Supported ((Ideal.span {p})^m) :=
    ⟨prime_power_small_squarefree p hp e he,supported_pow hs e,supported_pow hs l,supported_pow hs k,supported_pow hs m⟩
  unfold bareIdealHighCoefficient
  rw [dite_eq_left hguard]
  simp only [primaryGenerator_prime_power p hp.ne_zero hprimary]
  have hA : p^e*(p^l)^3=p^(e+3*l) := by rw [←pow_mul,Nat.mul_comm l 3,←pow_add]
  have hH : (p^m)^6=p^(6*m) := by rw [←pow_mul,Nat.mul_comm m 6]
  simp only [hA,hH,Ideal.span_singleton_pow]

theorem bareIdealHighSummand_row_at_prime (η : AngularCharacter) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p)
    (j e l k m : ℕ) (he : e≤1) (x w z : ℂ) :
    bareIdealHighSummand η (b*p^j) x w z ((Ideal.span {p})^e) ((Ideal.span {p})^l)
      ((Ideal.span {p})^k) ((Ideal.span {p})^m)=
      sourceRowTerm p hp hg (targetMonoid η p) (actualACube η p)
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)) x w z j e l k m := by
  unfold bareIdealHighSummand
  rw [bareIdealHighCoefficient_row_at_prime η p hp hprimary hs (b*p^j) e l k m he]
  rw [show b*p^j*p^(6*m)=b*p^(j+6*m) by rw [pow_add]; ring]
  have hw := prime_spectral_weights p hp.ne_zero e l k m x w z
  simp only [mul_assoc] at hw ⊢
  rw [hw]
  simpa only [mul_assoc] using
    bareSourceCoefficient_row_weighted_prime η p hp hg hchar hprimary hs b hb j e l k m he _ x w z

theorem idealRowHighLocalFactor_eq_source (η : AngularCharacter) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p) (j : ℕ) (x w z : ℂ) :
    idealRowHighLocalFactor η (b*p^j) (Ideal.span {p}) x w z=
      ∑ e : Fin 2,∑' l,∑' k,∑' m,sourceRowTerm p hp hg (targetMonoid η p) (actualACube η p)
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)) x w z j e.val l k m := by
  unfold idealRowHighLocalFactor
  apply Finset.sum_congr rfl
  intro e he
  apply tsum_congr
  intro l
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  exact bareIdealHighSummand_row_at_prime η p hp hg hchar hprimary hs b hb j e.val l k m (by omega) x w z

theorem idealRowHighLocalFactor_eq_closed (η : AngularCharacter) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p)
    (j : ℕ) (hj : j<6) (x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) (actualACube η p)
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1)
    (hW : ‖actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)*
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))‖<1) :
    idealRowHighLocalFactor η (b*p^j) (Ideal.span {p}) x w z=
      1/(1-coordV (Ideal.absNorm (Ideal.span {p})) z)+
      (if j=0 then
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)*
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)))/
        (1-actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)*
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))) else 0)+
      rowClosedMarked p hp hg (targetMonoid η p) (actualACube η p)
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)) j := by
  rw [idealRowHighLocalFactor_eq_source η p hp hg hc hprimary hs b hb j x w z]
  exact sourceRowSeries_eq_closed p hp hg hc _ _ _ x w z
    (actualSextic_unit_six p b hg hc hb) hV hR hW j hj

/-- The target is arbitrary angular data; only the actual finite row satisfies rho^6=1. -/
theorem idealRowHighLocalFactor_unramified_euler (η : AngularCharacter) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p) (x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) ((actualACube η p)^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p}))
      (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)) w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) (targetMonoid η p)
      (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)) x≠0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let rho := actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)
    idealRowHighLocalFactor η b (Ideal.span {p}) x w z =
      (1-coordD Q (targetMonoid η p) rho x) / ((1-coordV Q z)*(1-coordW Q rho w)) *
        unramifiedClosed Q ((actualACube η p)^2) (targetMonoid η p) rho x w z := by
  have he := idealRowHighLocalFactor_eq_source η p hp hg hc hprimary hs b hb 0 x w z
  simp only [pow_zero,mul_one] at he
  rw [he]
  exact sourceRowSeries_unramified_euler p hp hg hc _ _ _ x w z
    (actualSextic_unit_six p b hg hc hb) hV hR hW hD

lemma targetMonoid_primaryGenerator (η : AngularCharacter) (I : Ideal O) (hs : Supported I) :
    targetMonoid η (primaryGenerator I)=η.idealHom I := by
  calc
    _ = η.idealHom (Ideal.span {primaryGenerator I}) := (η.idealHom_span _).symm
    _ = _ := by rw [span_primaryGenerator_of_supported I hs]

def idealClosedCorrection (η : AngularCharacter) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  unramifiedClosed (Ideal.absNorm P.val) (actualAPhase η (primaryGenerator P.val))
    (η.idealHom P.val) 1 x w z

theorem idealHighLocalFactor_rational (η : AngularCharacter) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let Q : ℝ := Ideal.absNorm P.val
    idealHighLocalFactor η P.val x w z =
      (1-η.idealHom P.val*(Q:ℂ)^(-x)) /
        ((1-(Q:ℂ)^(-6*z))*(1-(Q:ℂ)^(-w))) * idealClosedCorrection η P x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hprimary := (primaryGenerator_spec P.val (supported_primaryGenerator_ne_zero P.val hs)).2
  have hQ2 : (2:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by
    rw [hspan]
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P
  have hQ0 : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hQ1 : (1:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1 := by
    rw [coordV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) ((actualACube η p)^2) x z‖<1 := by
    rw [actualACube_sq]
    apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η p)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1 := by
    apply (coordW_norm_le _ hQ0 1 w (by simp)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hDnorm : ‖coordD (Ideal.absNorm (Ideal.span {p})) (targetMonoid η p) 1 x‖<1 := by
    apply (coordD_norm_le _ hQ0 _ 1 x (targetMonoid_norm_le_one η p) (by simp)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) (targetMonoid η p) 1 x≠0 := by
    intro he
    have hh : coordD (Ideal.absNorm (Ideal.span {p})) (targetMonoid η p) 1 x=1 := (sub_eq_zero.mp he).symm
    rw [hh,norm_one] at hDnorm
    exact lt_irrefl _ hDnorm
  have he := idealHighLocalFactor_euler_identity η p hp hg.1 hg.2 hprimary hsp x w z hV hR hW hD
  dsimp only at he ⊢
  rw [hspan,actualACube_sq,targetMonoid_primaryGenerator η P.val hs] at he
  simpa only [coordD,coordV,coordW,star_one,mul_one,one_mul,idealClosedCorrection,p] using he

end
end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.idealRowHighLocalFactor_eq_closed

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.idealRowHighLocalFactor_unramified_euler

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.idealHighLocalFactor_rational
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.idealHighLocalFactor_rational
