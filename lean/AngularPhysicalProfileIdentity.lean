import AngularPhysicalConjugation
import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationProfiles

noncomputable section
open scoped Classical
namespace OAI.SevenEighths.Angular.InverseAmplification
open OAI.SevenEighths.Angular.Dyadic
open HeckeInverseAmplification (twistProfile)
theorem polynomial_twistProfile (χ : AngularCharacter) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) :
    polynomial χ inv (twistProfile W σ freq) D 0 0=polynomial χ inv W D σ freq := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  simp [summand,twistProfile,HeckeDyadic.shift,Dyadic.shift,mul_assoc]


#print axioms polynomial_twistProfile
end OAI.SevenEighths.Angular.InverseAmplification
