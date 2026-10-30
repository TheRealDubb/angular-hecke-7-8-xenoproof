import AngularRowClosure
import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationFamily

/-! Actual angular row characters, with exact ideal coefficients and a fixed
angular type. These are not aliases for the old finite-character RowData. -/
noncomputable section
open scoped Classical
namespace OAI.SevenEighths.Angular.InverseRows
open ActualEisensteinCubic CanonicalRowCompletion AngularRowClosure
local notation "O" => ActualEisensteinCubic.O
abbrev NonzeroElement := UnrestrictedIdealReindex.NonzeroElement

structure RowData where
  η : AngularCharacter
  m : O
  f : O
  m_ne_zero : m ≠ 0
  f_ne_zero : f ≠ 0
  lambda_dvd : ConcretePrimeRowBridge.goodLambda ∣ m
  two_dvd : (2 : O) ∣ m

def RowData.character (data : RowData) (u : NonzeroElement) : AngularCharacter :=
  Classical.choose (exists_angular_row_character data.η data.m data.f u.val
    data.m_ne_zero data.f_ne_zero u.property data.lambda_dvd data.two_dvd)

theorem RowData.character_k (data : RowData) (u : NonzeroElement) :
    (data.character u).k = data.η.k :=
  (Classical.choose_spec (exists_angular_row_character data.η data.m data.f u.val
    data.m_ne_zero data.f_ne_zero u.property data.lambda_dvd data.two_dvd)).1

theorem RowData.character_conductor (data : RowData) (u : NonzeroElement) :
    (data.character u).modulus.absNorm ≤ rowConductorBound data.η data.m data.f u.val :=
  (Classical.choose_spec (exists_angular_row_character data.η data.m data.f u.val
    data.m_ne_zero data.f_ne_zero u.property data.lambda_dvd data.two_dvd)).2.1

theorem RowData.character_spec (data : RowData) (u : NonzeroElement) (a : O) :
    (data.character u).elementCoeff a =
      rowTwist data.η.elementHom.toMonoidHom data.m data.f u.val a :=
  (Classical.choose_spec (exists_angular_row_character data.η data.m data.f u.val
    data.m_ne_zero data.f_ne_zero u.property data.lambda_dvd data.two_dvd)).2.2.1 a

theorem idealCoeff_eq_row (η χ : AngularCharacter) (m f z : O)
    (heq : ∀ a : O, χ.elementCoeff a = rowTwist η.elementHom.toMonoidHom m f z a)
    (I : Ideal O) : χ.idealHom I = η.idealHom I * idealRowHom (m^6*f^4*z) I := by
  rw [← Ideal.span_singleton_generator I, χ.idealHom_span, heq]
  change η.elementCoeff (Submodule.IsPrincipal.generator I) * _ =
    η.idealHom (Ideal.span {Submodule.IsPrincipal.generator I}) * _
  rw [η.idealHom_span]
  rfl

theorem RowData.character_ideal (data : RowData) (u : NonzeroElement) (I : Ideal O) :
    (data.character u).idealHom I = data.η.idealHom I * idealRowHom (data.m^6*data.f^4*u.val) I :=
  idealCoeff_eq_row data.η (data.character u) data.m data.f u.val (data.character_spec u) I

def baseCharacter (data : RowData) : AngularCharacter := data.character ⟨1, one_ne_zero⟩

theorem baseCharacter_k (data : RowData) : (baseCharacter data).k = data.η.k :=
  data.character_k ⟨1, one_ne_zero⟩

theorem baseCharacter_coeff (data : RowData) (I : Ideal O) :
    (baseCharacter data).idealHom I = data.η.idealHom I * idealRowHom (data.m^6*data.f^4) I := by
  simpa only [baseCharacter, mul_one] using data.character_ideal ⟨1, one_ne_zero⟩ I

theorem actual_row_fixed_base (data : RowData) (u : NonzeroElement) (I : Ideal O) :
    (data.character u).idealHom I = (baseCharacter data).idealHom I * idealRowHom u.val I := by
  rw [data.character_ideal, baseCharacter_coeff, idealRowHom_argument_mul]
  ring

abbrev amplifiedElement := HeckeInverseAmplification.amplifiedElement

end OAI.SevenEighths.Angular.InverseRows
