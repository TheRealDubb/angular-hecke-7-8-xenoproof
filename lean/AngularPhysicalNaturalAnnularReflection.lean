import AngularPhysicalNaturalPrimitivePresentation
import AngularPhysicalDeletedAnnularReflection

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.NaturalPrimitive
open CenteredMomentNaturalPrimitive
local notation "O" => ActualEisensteinCubic.O

open EisensteinSchwartzPoisson ConcreteTraceCRT AnnularFourier AnnularReflection
open CenteredMomentReflectionDeletion (SmoothIdeal)
open PrimitiveReduction

theorem natural_annular_reflection (χ:AngularCharacter) (hn:χ.k≠0 ∨ χ.residue≠1)
    (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ)) (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
    (X:ℝ) (hX:0<X) :
    let ψ:=primitive χ
    let S:=redundantSet χ.modulus ψ.modulus
    let hS:=redundantSet_prime χ.modulus ψ.modulus
    let c:=generator χ
    letI:NeZero c:=⟨generator_ne_zero χ⟩
    (∀D∈S.powerset, Summable (PlainDeletion.reflectedTerm ψ ψ.conjugate S hS
      (profile ψ.k a b ha W) X (‖eisEmbedding c‖^2) D)) ∧
    Dyadic.polynomial χ false W X 0 0=
      annularReflectionScalar c ψ (primitive_modulus χ) * ∑D∈S.powerset, ∑'H:SmoothIdeal S,
        PlainDeletion.reflectedTerm ψ ψ.conjugate S hS (profile ψ.k a b ha W)
          X (‖eisEmbedding c‖^2) D H := by
  dsimp only
  letI naturalAnnularGeneratorNeZero:NeZero (generator χ):=⟨generator_ne_zero χ⟩
  have hh:=primitive_deleted_reflection (generator χ) (primitive χ) (primitive_modulus χ)
    (primitive_isPrimitive χ) (primitive_nonprincipal χ hn)
    (redundantSet χ.modulus (primitive χ).modulus)
    (redundantSet_prime χ.modulus (primitive χ).modulus) a b ha W hs X hX
  refine ⟨hh.1,?_⟩
  rw [polynomial_natural_deletion χ (primitive χ) (modulus_le χ) (idealHom_source_mask χ)]
  exact hh.2

end OAI.SevenEighths.Angular.NaturalPrimitive

#print axioms OAI.SevenEighths.Angular.NaturalPrimitive.natural_annular_reflection
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalPrimitive.natural_annular_reflection
