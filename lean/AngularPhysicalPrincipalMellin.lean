import AngularPhysicalSignal
import OAI.NumberTheory.DirichletL.PrincipalMellinResidues

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
open Complex
namespace OAI.SevenEighths.Angular.PhysicalPrincipalMellin
open HeckeFamily PrincipalMellinResidues
local notation "O" => ActualEisensteinCubic.O

def sourceMultiplier (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (eta : AngularCharacter) (s : ℂ) (H B : ℂ → ℂ → ℂ) (w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z) * (Z:ℂ)^(s+z-1) * (Y:ℂ)^(w-1) *
    Complex.exp ((s+z-1)^2) *
    mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z * mellin W1 w /
      FamilyContinuation.LFunction eta s * H w z * B w z

theorem sourceMultiplier_integrand (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (eta : AngularCharacter) (principal : HeckeFamily.Character) (s : ℂ) (H B : ℂ → ℂ → ℂ) (w z : ℂ) :
    sourceMultiplier W0 W1 X Y Z eta s H B w z *
      HeckeFamily.LFunction principal (6*z) * HeckeFamily.LFunction principal w =
    (X:ℂ)^(1/2-z) * (Z:ℂ)^(s+z-1) * (Y:ℂ)^(w-1) *
      Complex.exp ((s+z-1)^2) *
      mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z * mellin W1 w *
      HeckeFamily.LFunction principal (6*z) * HeckeFamily.LFunction principal w /
      FamilyContinuation.LFunction eta s * H w z * B w z := by
  unfold sourceMultiplier
  ring

theorem source_double_residue (W0 W1 : SchwartzMap ℝ ℂ) (M : Ideal O) [NeZero M]
    (X Y Z : ℝ) (eta : AngularCharacter) (s : ℂ) (H B : ℂ → ℂ → ℂ) :
    fixedPrincipalResidue M ^ 2 / 6 *
      sourceMultiplier W0 W1 X Y Z eta s H B 1 (1/6) =
    sourceResidueConstant W0 W1 M *
      ((X:ℂ)^(1/3:ℂ) * (Z:ℂ)^(s-5/6) * Complex.exp ((s-5/6)^2) /
        FamilyContinuation.LFunction eta s * H 1 (1/6) * B 1 (1/6)) := by
  unfold sourceResidueConstant sourceMultiplier
  rw [show (1/2:ℂ)-1/6=1/3 by norm_num,
    show s+(1/6:ℂ)-1=s-5/6 by ring]
  simp only [sub_self, Complex.cpow_zero, mul_one]
  ring

end OAI.SevenEighths.Angular.PhysicalPrincipalMellin

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalMellin.sourceMultiplier_integrand

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalMellin.source_double_residue
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalPrincipalMellin.source_double_residue
