import AngularInverseRows
import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationColumn

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.Angular.InverseRows
open CanonicalRowCompletion
open CanonicalQuadraticSieve hiding O
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem row_coeff_zero_unsupported (η χ : AngularCharacter) (m f z : O)
    (heq : ∀ n : O, χ.elementCoeff n=rowTwist η.elementHom.toMonoidHom m f z n)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m) (J : Ideal O) (hJ : ¬Supported J) :
    χ.idealHom J=0 := by
  by_cases hz : J=0
  · subst J
    exact map_zero _
  let n := ConcretePrimeRowBridge.idealGenerator J
  have hn : n≠0 := ConcretePrimeRowBridge.idealGenerator_ne_zero J hz
  have hs : Ideal.span {n}=J := ConcretePrimeRowBridge.span_idealGenerator J
  rw [←hs,χ.idealHom_span n,heq]
  exact rowTwist_zero_of_not_supported η.elementHom.toMonoidHom m f z n hmLam hm2 (hs ▸ hJ)

theorem prime_coprime_iff (P : SmoothMobiusCorrection.PrimeIdeal) (J : Ideal O) :
    IsCoprime J P.val ↔ ¬P.val∣J := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  rw [isCoprime_comm,Ideal.isCoprime_iff_codisjoint,
    ←(Ideal.isMaximal_def.mp (inferInstance : P.val.IsMaximal)).not_le_iff_codisjoint,
    ←Ideal.dvd_iff_le]

theorem amplified_row_prime_mask (η χ ψ : AngularCharacter) (m f z a : O)
    (P : SmoothMobiusCorrection.PrimeIdeal) (hspan : Ideal.span {a}=P.val)
    (hχ : ∀ n : O, χ.elementCoeff n=rowTwist η.elementHom.toMonoidHom m f z n)
    (hψ : ∀ n : O, ψ.elementCoeff n=rowTwist η.elementHom.toMonoidHom m f (z*a^6) n)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m) :
    ψ.idealHom=IdealEuler.deletePrimes {P} (χ.idealHom) := by
  ext J
  rw [IdealEuler.deletePrimes_apply]
  simp only [Finset.mem_singleton,forall_eq]
  by_cases hs : Supported J
  · rw [idealCoeff_eq_row η ψ m f (z*a^6) hψ,
      show m^6*f^4*(z*a^6)=(m^6*f^4*z)*a^6 by ring,
      idealRowHom_argument_mul,idealRowHom_sixth_mask a J hs,hspan,prime_coprime_iff]
    by_cases hd : P.val∣J
    · simp [hd]
    · simp only [hd,not_false_eq_true,ite_true,mul_one]
      exact (idealCoeff_eq_row η χ m f z hχ J).symm
  · rw [row_coeff_zero_unsupported η ψ m f (z*a^6) hψ hmLam hm2 J hs,
      row_coeff_zero_unsupported η χ m f z hχ hmLam hm2 J hs]
    simp

theorem RowData.amplified_prime_mask (data : RowData) (u : NonzeroElement)
    (P : SmoothMobiusCorrection.PrimeIdeal) :
    (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)).idealHom =
      IdealEuler.deletePrimes {P} (data.character u).idealHom := by
  exact amplified_row_prime_mask data.η (data.character u)
    (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) data.m data.f u.val
    (ConcretePrimeRowBridge.idealGenerator P.val) P
    (ConcretePrimeRowBridge.span_idealGenerator P.val)
    (data.character_spec u) (data.character_spec (amplifiedElement u ⟨P.val,P.property.ne_zero⟩))
    data.lambda_dvd data.two_dvd

#print axioms RowData.amplified_prime_mask
end SevenEighths.Angular.InverseRows

end

end OAI
