import AngularPhysicalPrincipalBoundary
import OAI.NumberTheory.DirichletL.PrincipalMellinGrowth

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory
namespace OAI.SevenEighths.Angular.PhysicalPrincipalGrowth
open HeckeFamily PrincipalMellinResidues PrincipalMellinGrowth ProbeMellinBoundary

theorem source_w_boundary (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ)
    (ha1 : 0<a1) (hW1 : Function.support W1⊆Icc a1 b1)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hY : 0<Y)
    (eta : AngularCharacter) (s z : ℂ) (hEta : FamilyContinuation.LFunction eta s≠0) (H B : ℂ → ℂ → ℂ) {cw AH : ℝ}
    (hcw : 1<cw) (hAH : 0≤AH) (JH : ℕ)
    (hHB : ContinuousOn (fun w => H w z*B w z) {w : ℂ | (19/20:ℝ)≤w.re ∧ w.re≤cw})
    (hHBbd : ∀x∈Icc (19/20:ℝ) cw, ∀t : ℝ, (x=19/20 ∨ x=cw ∨ 1≤|t|) →
      ‖H ((x:ℂ)+t*I) z * B ((x:ℂ)+t*I) z‖≤AH*height t^JH) :
    BoundaryControl (fun w => PhysicalPrincipalMellin.sourceMultiplier W0 W1 X Y Z eta s H B w z *
      LFunction (fixedPrincipal M) w) (19/20) cw := by
  apply PhysicalPrincipalBoundary.source_w_boundary W0 W1 a1 b1 ha1 hW1 M X Y Z hY eta s z hEta H B
    (AL:=wAmplitude M cw) hcw hAH (wAmplitude_pos M hcw).le JH 3 hHB hHBbd
  intro x hx t _
  exact fixed_principal_w_growth M hcw hx t

theorem source_z_boundary (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ)
    (ha0 : 0<a0) (hW0 : Function.support W0⊆Icc a0 b0)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (eta : AngularCharacter) (s : ℂ) (hEta : FamilyContinuation.LFunction eta s≠0) (H B : ℂ → ℂ → ℂ) {e AH : ℝ}
    (he : 0<e) (he' : e≤2/3) (hAH : 0≤AH) (JH : ℕ)
    (hHB : ContinuousOn (fun z => H 1 z*B 1 z)
      {z : ℂ | (33/200:ℝ)≤z.re ∧ z.re≤1/6+e})
    (hHBbd : ∀x∈Icc (33/200:ℝ) (1/6+e), ∀t : ℝ, (x=33/200 ∨ x=1/6+e ∨ 1≤|t|) →
      ‖H 1 ((x:ℂ)+t*I) * B 1 ((x:ℂ)+t*I)‖≤AH*height t^JH) :
    BoundaryControl (fun z => PhysicalPrincipalMellin.sourceMultiplier W0 W1 X Y Z eta s H B 1 z *
      LFunction (fixedPrincipal M) (6*z)) (33/200) (1/6+e) := by
  apply PhysicalPrincipalBoundary.source_z_boundary W0 W1 a0 b0 ha0 hW0 M X Y Z hX hZ eta s hEta H B
    (AL:=zAmplitude M) he hAH (zAmplitude_pos M).le JH 3 hHB hHBbd
  intro x hx t _
  exact fixed_principal_z_growth M he he' hx t


end OAI.SevenEighths.Angular.PhysicalPrincipalGrowth

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalGrowth.source_w_boundary

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalGrowth.source_z_boundary
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalPrincipalGrowth.source_z_boundary
