import AngularPhysicalPlainDeletedReflection
import AngularPhysicalPrimitiveAnnularReflection

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.AnnularReflection
open EisensteinSchwartzPoisson ConcreteTraceCRT AnnularFourier
open PlainDeletion (reflectedTerm)
open CenteredMomentReflectionDeletion (SmoothIdeal schwartz_decayTwo)
local notation "O" => ActualEisensteinCubic.O

theorem primitive_deleted_reflection (c:O) [instc:NeZero c]
    (ψ:AngularCharacter) (hmod:ψ.modulus=Ideal.span {c})
    (hp:FiniteFourier.IsPrimitiveOnIdeals (hmod ▸ ψ.residue)) (hn:ψ.k≠0 ∨ ψ.residue≠1)
    (S:Finset (Ideal O)) (hS:∀P∈S,Prime P)
    (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ)) (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
    (X:ℝ) (hX:0<X) :
    (∀D∈S.powerset, Summable (reflectedTerm ψ ψ.conjugate S hS
      (profile ψ.k a b ha W) X (‖eisEmbedding c‖^2) D)) ∧
    Dyadic.polynomial (ψ.excludePrimes S hS) false W X 0 0=
      annularReflectionScalar c ψ hmod * ∑D∈S.powerset, ∑'H:SmoothIdeal S,
        reflectedTerm ψ ψ.conjugate S hS (profile ψ.k a b ha W) X (‖eisEmbedding c‖^2) D H := by
  apply PlainDeletion.deletion_reflection _ _ S hS W (profile ψ.k a b ha W)
    (schwartz_decayTwo W) (profile_decayTwo ψ.k a b ha W) _ _ _
    (fun Y hY => primitive_normalized_reflection c ψ hmod hp hn a b ha W hs Y hY) X hX
  exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c)))

theorem primitive_deleted_reflection_absolute (c:O) [instc:NeZero c]
    (ψ:AngularCharacter) (hmod:ψ.modulus=Ideal.span {c})
    (hp:FiniteFourier.IsPrimitiveOnIdeals (hmod ▸ ψ.residue)) (hn:ψ.k≠0 ∨ ψ.residue≠1)
    (S:Finset (Ideal O)) (hS:∀P∈S,Prime P)
    (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ)) (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
    (X:ℝ) (hX:0<X) :
    Summable (fun H:SmoothIdeal S => ∑D∈S.powerset,
      ‖reflectedTerm ψ ψ.conjugate S hS (profile ψ.k a b ha W) X (‖eisEmbedding c‖^2) D H‖) := by
  exact summable_sum (fun D hD =>
    ((primitive_deleted_reflection c ψ hmod hp hn S hS a b ha W hs X hX).1 D hD).norm)

end OAI.SevenEighths.Angular.AnnularReflection

#print axioms OAI.SevenEighths.Angular.AnnularReflection.primitive_deleted_reflection
#print axioms OAI.SevenEighths.Angular.AnnularReflection.primitive_deleted_reflection_absolute
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AnnularReflection.primitive_deleted_reflection_absolute
