import AngularPhysicalNaturalAnnularReflection

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.NaturalReflection
open CenteredMomentNaturalPrimitive NaturalPrimitive PlainDeletion AnnularReflection AnnularFourier
open CenteredMomentReflectionDeletion (SmoothIdeal norm)
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

lemma polynomial_coeff_congr (χ ψ:AngularCharacter)
    (h:∀I,χ.idealHom I=ψ.idealHom I) (W:ℝ→ℂ) (X:ℝ) :
    Dyadic.polynomial χ false W X 0 0=Dyadic.polynomial ψ false W X 0 0 := by
  unfold Dyadic.polynomial
  congr 1
  apply tsum_congr
  intro I
  unfold Dyadic.summand Dyadic.coefficient
  rw [h]

lemma conjugate_deletion_coeff (χ ψ:AngularCharacter) (S:Finset (Ideal O))
    (hS:∀P∈S,Prime P) (h:∀I,χ.idealHom I=(ψ.excludePrimes S hS).idealHom I)
    (I:Ideal O) : χ.conjugate.idealHom I=(ψ.conjugate.excludePrimes S hS).idealHom I := by
  rw [AngularCharacter.conjugate_idealHom,h,AngularCharacter.idealHom_excludePrimes,
    AngularCharacter.idealHom_excludePrimes,AngularCharacter.conjugate_idealHom]
  split_ifs <;> simp

theorem primitive_character_deleted (ψ:AngularCharacter)
    (hp:FiniteFourier.IsPrimitiveOnIdeals ψ.residue) (hn:ψ.k≠0 ∨ ψ.residue≠1) :
    ∃G:ℂ,‖G‖=1 ∧ ∀(S:Finset (Ideal O))(hS:∀P∈S,Prime P)
      (a b:ℝ)(ha:0<a)(W:𝓢(ℝ,ℂ)),Function.support (W:ℝ→ℂ)⊆Set.Icc a b →
      ∀X:ℝ,0<X →
      (∀D∈S.powerset,Summable (reflectedTerm ψ ψ.conjugate S hS (profile ψ.k a b ha W)
        X (ψ.modulus.absNorm:ℝ) D)) ∧
      Dyadic.polynomial (ψ.excludePrimes S hS) false W X 0 0=
        G*∑D∈S.powerset,∑'H:SmoothIdeal S,
          reflectedTerm ψ ψ.conjugate S hS (profile ψ.k a b ha W) X (ψ.modulus.absNorm:ℝ) D H := by
  let c:=Submodule.IsPrincipal.generator ψ.modulus
  have hm:ψ.modulus=Ideal.span {c}:=(Ideal.span_singleton_generator ψ.modulus).symm
  have hc:c≠0:=by
    intro h
    apply ψ.modulus_ne_bot
    rw [hm,h,Ideal.span_singleton_zero]
  letI primitiveCharacterDeletedNeZero:NeZero c:=⟨hc⟩
  have htransport (M N:Ideal O) (h:M=N) (ρ:MulChar (O⧸M) ℂ)
      (hr:FiniteFourier.IsPrimitiveOnIdeals ρ) : FiniteFourier.IsPrimitiveOnIdeals (h ▸ ρ):=by
    cases h
    exact hr
  have hp':FiniteFourier.IsPrimitiveOnIdeals (hm ▸ ψ.residue):=htransport _ _ hm ψ.residue hp
  refine ⟨annularReflectionScalar c ψ hm,norm_annularReflectionScalar c ψ hm hp',?_⟩
  intro S hS a b ha W hs X hX
  have hh:=primitive_deleted_reflection c ψ hm hp' hn S hS a b ha W hs X hX
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,←hm] at hh
  exact hh

end OAI.SevenEighths.Angular.NaturalReflection

#print axioms OAI.SevenEighths.Angular.NaturalReflection.primitive_character_deleted
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReflection.primitive_character_deleted
