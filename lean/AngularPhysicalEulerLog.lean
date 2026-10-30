import AngularPhysicalRegularInput
import OAI.NumberTheory.DirichletL.Hecke.EulerLog

noncomputable section
open scoped Classical Topology
open Set Metric Complex
namespace OAI.SevenEighths.Angular.PhysicalLogarithmic
open PhysicalLogarithmicInput

def eulerLog (χ : AngularCharacter) : ℂ → ℂ :=
  if χ.k = 0 ∧ χ.residue = 1 then HeckeEulerLog.principalEulerLog χ.idealHom
  else HeckeEulerLog.eulerLog χ.idealHom

def innerBound : ℝ := 3+HeckeEulerLog.eulerLogBound

theorem innerBound_ge_one : 1 ≤ innerBound := by
  unfold innerBound
  linarith [HeckeEulerLog.eulerLogBound_ge_one]

theorem actual_inner_log (χ : AngularCharacter) (t : ℝ) :
    DifferentiableOn ℂ (eulerLog χ) (ball ((2:ℂ)+t*I) (1/2)) ∧
    EqOn (Complex.exp ∘ eulerLog χ) (regular χ) (ball ((2:ℂ)+t*I) (1/2)) ∧
    ∀ z ∈ closedBall ((2:ℂ)+t*I) (49/100), ‖eulerLog χ z‖ ≤ innerBound := by
  by_cases hp : χ.k = 0 ∧ χ.residue = 1
  · have hright (s : ℂ) (hs : 1 < s.re) : regular χ s =
        ((s-1)/(s+1))*IdealEuler.series χ.idealHom s := by
      have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
      rw [regular_eq_principal_factor χ hp.1 hp.2 (by linarith) h1,
        FamilyContinuation.LFunction_eq_series χ s hs,AngularCharacter.series]
      ring
    simpa only [eulerLog,ite_eq_left hp,innerBound] using
      HeckeEulerLog.principal_continued_inner_disk χ.idealHom χ.norm_idealHom_le_one
        (regular χ) hright t
  · have hnon : χ.k ≠ 0 ∨ χ.residue ≠ 1 := by tauto
    have hright (s : ℂ) (hs : 1 < s.re) : regular χ s =
        IdealEuler.series χ.idealHom s := by
      rw [regular_eq_nonprincipal χ hnon]
      exact FamilyContinuation.LFunction_eq_series χ s hs
    obtain ⟨hd,he,hb⟩ := HeckeEulerLog.continued_inner_disk χ.idealHom
      χ.norm_idealHom_le_one (regular χ) hright t
    simp only [eulerLog,ite_eq_right hp]
    refine ⟨hd,he,?_⟩
    intro z hz
    have h := hb z hz
    unfold innerBound
    linarith

end OAI.SevenEighths.Angular.PhysicalLogarithmic

#print axioms OAI.SevenEighths.Angular.PhysicalLogarithmic.innerBound_ge_one
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLogarithmic.innerBound_ge_one

#print axioms OAI.SevenEighths.Angular.PhysicalLogarithmic.actual_inner_log
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLogarithmic.actual_inner_log
