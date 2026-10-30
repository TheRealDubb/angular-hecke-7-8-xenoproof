import AngularPhysicalFiniteProductPresentation
import OAI.NumberTheory.DirichletL.Moments.RadicalFamily

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.PlainRows
open AngularRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem exists_radical_row_presentation {ι : Type*} [Fintype ι]
    (η : AngularCharacter) (m : O) (hm : m≠0) (hmLam : λ₀∣m) (hm2 : (2:O)∣m)
    (p : ι→O) (hp : ∀i,Supported (Ideal.span {p i}))
    (e : ι→ℕ) (he : ∀i,0<e i) :
    ∃τ : AngularCharacter, τ.k=η.k ∧
      η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*(∏i,Ideal.span {p i})≤τ.modulus ∧
      τ.modulus.absNorm≤η.modulus.absNorm*(Ideal.span {m}).absNorm*
        (Ideal.span {(72:O)}).absNorm*∏i,(Ideal.span {p i}).absNorm ∧
      ∀n:O,τ.elementCoeff n=rowTwist η.elementHom.toMonoidHom m 1 (∏i,(p i)^(e i)) n := by
  obtain ⟨χ,hM,hN,hχ⟩:=CenteredMomentRadicalFamily.exists_radical_row_presentation
    finiteTrivial m hm hmLam hm2 p hp e he
  have hM' : Ideal.span {m}*Ideal.span {(72:O)}*(∏i,Ideal.span {p i})≤χ.modulus := by
    simpa only [show finiteTrivial.modulus=⊤ from rfl,Ideal.top_mul] using hM
  have hN' : χ.modulus.absNorm≤(Ideal.span {m}).absNorm*
      (Ideal.span {(72:O)}).absNorm*∏i,(Ideal.span {p i}).absNorm := by
    simpa only [show finiteTrivial.modulus=⊤ from rfl,Ideal.absNorm_top,one_mul] using hN
  refine ⟨finiteTwist η χ,rfl,?_,?_,?_⟩
  · change η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*(∏i,Ideal.span {p i})≤η.modulus⊓χ.modulus
    rw [mul_assoc,mul_assoc]
    exact le_inf Ideal.mul_le_left (Ideal.mul_le_right.trans (by simpa only [mul_assoc] using hM'))
  · exact (finiteTwist_conductor_bound η χ).trans (by
      simpa only [mul_assoc] using Nat.mul_le_mul_left η.modulus.absNorm hN')
  · intro n
    rw [elementCoeff_finiteTwist,hχ]
    change η.elementCoeff n*(HeckeFamily.elementCoeff finiteTrivial n*
      idealRowHom (m^6*1^4*(∏i,(p i)^(e i))) (Ideal.span {n}))=
      η.elementCoeff n*idealRowHom (m^6*1^4*(∏i,(p i)^(e i))) (Ideal.span {n})
    rw [finiteTrivial_elementCoeff,one_mul]

end OAI.SevenEighths.Angular.PlainRows

#print axioms OAI.SevenEighths.Angular.PlainRows.exists_radical_row_presentation
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.exists_radical_row_presentation
