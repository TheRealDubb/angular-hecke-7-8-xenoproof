import AngularPhysicalNaturalCharacter
import OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySupport

noncomputable section
open scoped Classical
open Set
namespace OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource
open CenteredMomentDetectorDictionary (annular_prime_coprime)
local notation "O" => ActualEisensteinCubic.O
theorem angular_annular_prime_coprime (eta : AngularCharacter)
    (D : ℝ) (hD : 0<D) (hlarge : (eta.modulus.absNorm:ℝ)<D)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Icc (1:ℝ) 2)
    (P : Ideal O) (hP : Prime P) (hW : W ((P.absNorm:ℝ)/D)≠0) :
    IsCoprime P eta.modulus := by
  letI : NeZero eta.modulus := ⟨eta.modulus_ne_bot⟩
  exact annular_prime_coprime (HeckeRayFamily.character eta.modulus 1) 1 D
    (by norm_num) hD (by
      change (eta.modulus.absNorm:ℝ)/1<D
      simpa only [div_one] using hlarge) W (fun x hx=>(hWs hx).1) P hP hW


end OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.angular_annular_prime_coprime
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.angular_annular_prime_coprime
