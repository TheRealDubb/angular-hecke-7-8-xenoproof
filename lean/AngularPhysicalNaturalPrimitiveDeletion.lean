import AngularPhysicalPlainFiniteDeletion
import AngularPrimitiveReduction
import OAI.NumberTheory.DirichletL.Moments.NaturalPrimitive

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.NaturalPrimitive
open CenteredMomentNaturalPrimitive
local notation "O" => ActualEisensteinCubic.O

theorem idealHom_natural_deletion (χ ψ:AngularCharacter) (hmod:χ.modulus≤ψ.modulus)
    (hmask:∀I:Ideal O,χ.idealHom I=if IsCoprime I χ.modulus then ψ.idealHom I else 0)
    (I:Ideal O) :
    χ.idealHom I=(ψ.excludePrimes (redundantSet χ.modulus ψ.modulus)
      (redundantSet_prime χ.modulus ψ.modulus)).idealHom I := by
  rw [hmask I,AngularCharacter.idealHom_excludePrimes]
  have hm:=coprime_original_iff I χ.modulus ψ.modulus χ.modulus_ne_bot ψ.modulus_ne_bot
    (Ideal.dvd_iff_le.mpr hmod)
  by_cases hC:IsCoprime I ψ.modulus
  · rw [hm]
    simp only [hC,true_and]
  · have hz:ψ.idealHom I=0:=(ψ.idealHom_zero_iff I).mpr (Or.inr hC)
    simp only [hz,ite_self]

theorem polynomial_natural_deletion (χ ψ:AngularCharacter) (hmod:χ.modulus≤ψ.modulus)
    (hmask:∀I:Ideal O,χ.idealHom I=if IsCoprime I χ.modulus then ψ.idealHom I else 0)
    (inverse:Bool) (W:ℝ→ℂ) (D σ t:ℝ) :
    Dyadic.polynomial χ inverse W D σ t=
      Dyadic.polynomial (ψ.excludePrimes (redundantSet χ.modulus ψ.modulus)
        (redundantSet_prime χ.modulus ψ.modulus)) inverse W D σ t := by
  unfold Dyadic.polynomial
  congr 1
  apply tsum_congr
  intro I
  unfold Dyadic.summand Dyadic.coefficient
  rw [idealHom_natural_deletion χ ψ hmod hmask I.val]

end OAI.SevenEighths.Angular.NaturalPrimitive

#print axioms OAI.SevenEighths.Angular.NaturalPrimitive.polynomial_natural_deletion
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalPrimitive.polynomial_natural_deletion
