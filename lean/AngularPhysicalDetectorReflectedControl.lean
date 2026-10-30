import AngularPhysicalDetectorReflection
import OAI.NumberTheory.DirichletL.Hecke.DyadicReflectedControl

noncomputable section
open scoped Classical Topology ContDiff ComplexConjugate
open Set Metric Complex MeasureTheory Filter
namespace OAI.SevenEighths.Angular.PhysicalDetectorDyadic
open OAI.SevenEighths.Angular.Dyadic FamilyContinuation PhysicalLogarithmic
open PhysicalReciprocal (presentationComplexity)
open HeckeDeletionBounds
open HeckeDyadic (radical_norm_ge_one)
theorem buffered_reflected_line_control (angularOrder : ℕ) (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → AngularCharacter) (horder : ∀ j, (χ j).k.natAbs≤angularOrder)
      (hχ : ∀ j, ((χ j).k≠0 ∨ (χ j).residue≠1)) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      PhysicalDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (s : ℂ), s.re=1-a-6*e → |s.im|≤(3*i+2 : ℕ)*T →
      ‖LFunction (χ j) s‖≤C*((χ j).modulus.absNorm : ℝ)^(a-1/2+6*e)*
        ((radical (χ j).modulus).absNorm : ℝ)^(6*e+2*ε)*
        (3+(3*i+2 : ℕ)*T)^2*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε := by
  obtain ⟨Cg,hCg,hreflect⟩ := original_reflected_subpower angularOrder ε hε
  obtain ⟨Cb,hCb,hrect⟩ := buffered_rectangle_control angularOrder e ε he he' hε
  refine ⟨Cg*Cb,mul_pos hCg hCb,?_⟩
  intro ι _ χ horder hχ T a i hT ha ha' hmax j s hs him
  have hwre : (1-conj s).re=a+6*e := by simp; linarith
  have hwim : (1-conj s).im=s.im := by simp
  have hw := hrect χ horder hχ T a i hT ha ha' hmax j (1-conj s)
    (by rw [hwre]) (by rw [hwre]; linarith) (by rwa [hwim])
  have hL : ‖LFunction (χ j) (1-conj s)‖≤
      Cb*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans hw.2
  have href := hreflect (χ j) (horder j) (hχ j) s (by rw [hs]; linarith) (by rw [hs]; linarith)
  have hexp : 1/2-s.re=a-1/2+6*e := by rw [hs]; ring
  rw [hexp] at href
  have hR : ((radical (χ j).modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε)≤
      ((radical (χ j).modulus).absNorm : ℝ)^(6*e+2*ε) := by
    apply Real.rpow_le_rpow_of_exponent_le (radical_norm_ge_one _)
    have hm : max (-s.re) 0≤6*e := max_le (by rw [hs]; linarith) (by positivity)
    linarith
  calc
    _ ≤ Cg*((χ j).modulus.absNorm : ℝ)^(a-1/2+6*e)*
        ((radical (χ j).modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε)*
        (3+|s.im|)^2*‖LFunction (χ j) (1-conj s)‖ := href
    _ ≤ Cg*((χ j).modulus.absNorm : ℝ)^(a-1/2+6*e)*
        ((radical (χ j).modulus).absNorm : ℝ)^(6*e+2*ε)*
        (3+(3*i+2 : ℕ)*T)^2*(Cb*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε) := by
      gcongr
    _ = _ := by ring

end OAI.SevenEighths.Angular.PhysicalDetectorDyadic


#print axioms OAI.SevenEighths.Angular.PhysicalDetectorDyadic.buffered_reflected_line_control
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorDyadic.buffered_reflected_line_control
