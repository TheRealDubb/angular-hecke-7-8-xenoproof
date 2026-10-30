import AngularPhysicalPlainExpansion
import OAI.NumberTheory.DirichletL.Moments.SourceRow

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.PlainRows
local notation "O" => ActualEisensteinCubic.O


open CenteredMomentRowNorm CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CompletedGauss
open CenteredMomentSourceRow (supportedColumns primary_span_supported sourceGenerator sourceGenerator_supported)

theorem rowWeight_split (η : AngularCharacter) (m A z : O) (t : ℝ) (I : Ideal O) :
    rowWeight η m A z t I = rowWeight η m A 1 t I*idealRowHom z I := by
  change (η.idealHom I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t) =
    ((η.idealHom I*idealRowHom (m^6*(A*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))*idealRowHom z I
  rw [mul_one,← mul_assoc,idealRowHom_argument_mul]
  ring

theorem rowWeight_zero_of_not_supported (η : AngularCharacter) (m A z : O) (t : ℝ)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) (I : Ideal O) (hI : ¬Supported I) :
    rowWeight η m A z t I=0 := by
  by_cases h0 : I=0
  · rw [h0,map_zero]
  let n := idealGenerator I
  have hn : n ≠ 0 := idealGenerator_ne_zero I h0
  have hs : Ideal.span {n}=I := span_idealGenerator I
  have hz := rowTwist_zero_of_not_supported η.elementHom.toMonoidHom m 1 (A*z) n
    hmLam hm2 (hs ▸ hI)
  have he : rowTwist η.elementHom.toMonoidHom m 1 (A*z) n =
      η.idealHom I*idealRowHom (m^6*(A*z)) I := by
    change η.elementCoeff n*idealRowHom (m^6*1^4*(A*z)) (Ideal.span {n})=_
    rw [one_pow,mul_one,hs,← η.idealHom_span,hs]
  rw [he] at hz
  change (η.idealHom I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)=0
  rw [hz,zero_mul]

theorem finite_hecke_sum_eq_rowPolynomial (η : AngularCharacter) (m A z : O) (t : ℝ)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) :
    (∑ I∈S,c I*rowWeight η m A z t I) =
      rowPolynomial Finset.univ (sourceGenerator S)
        (fun I : supportedColumns S => c I*rowWeight η m A 1 t I) z := by
  have he : (∑ I∈S,c I*rowWeight η m A z t I) =
      ∑ I∈supportedColumns S,c I*rowWeight η m A z t I := by
    symm
    apply Finset.sum_filter_of_ne
    intro I hI hn
    by_contra hs
    exact hn (by rw [rowWeight_zero_of_not_supported η m A z t hmLam hm2 I hs,mul_zero])
  rw [he,← Finset.sum_coe_sort (supportedColumns S) (fun I => c I*rowWeight η m A z t I)]
  unfold rowPolynomial
  apply Finset.sum_congr rfl
  intro I hI
  rw [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2,rowWeight_split]
  ring

def finiteHeckeEnergy (η : AngularCharacter) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑' z : O,((‖∑ I∈S,c I*rowWeight η m A z t I‖^2:ℝ):ℂ)*
    W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)

theorem finiteHeckeEnergy_eq (η : AngularCharacter) (m A : O) (t : ℝ)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    finiteHeckeEnergy η m A t S c W K =
      rowEnergy Finset.univ (sourceGenerator S)
        (fun I : supportedColumns S => c I*rowWeight η m A 1 t I) W K := by
  unfold finiteHeckeEnergy rowEnergy
  simp_rw [finite_hecke_sum_eq_rowPolynomial η m A _ t hmLam hm2 S c]

theorem finiteHeckeEnergy_poisson (η : AngularCharacter) (m A : O) (t : ℝ)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K) :
    finiteHeckeEnergy η m A t S c W K =
      ∑ I : supportedColumns S,∑ J : supportedColumns S,
        ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
          (((K/‖ConcreteTraceCRT.eisEmbedding (sourceGenerator S I*sourceGenerator S J)‖^2:ℝ):ℂ)*
            ∑' h : O,pairFourier (sourceGenerator S I) (sourceGenerator S J)
              (sourceGenerator_supported S I) (sourceGenerator_supported S J) h*
              EisensteinSchwartzPoisson.paperRadialFourier W
                (K*‖ConcreteTraceCRT.eisEmbedding h‖^2/
                  ‖ConcreteTraceCRT.eisEmbedding (sourceGenerator S I*sourceGenerator S J)‖^2)) := by
  rw [finiteHeckeEnergy_eq η m A t hmLam hm2 S c W K]
  exact rowEnergy_poisson Finset.univ (sourceGenerator S)
    (fun I : supportedColumns S => c I*rowWeight η m A 1 t I)
    (sourceGenerator_supported S) W K hK

end OAI.SevenEighths.Angular.PlainRows

#print axioms OAI.SevenEighths.Angular.PlainRows.finiteHeckeEnergy_poisson
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.finiteHeckeEnergy_poisson
