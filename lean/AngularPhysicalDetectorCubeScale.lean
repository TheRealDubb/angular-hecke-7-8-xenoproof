import AngularPhysicalDetectorCentralHeightCost
import OAI.NumberTheory.DirichletL.Hecke.PrimeAmplitudeScale
import OAI.NumberTheory.DirichletL.Detector.MellinBoundary
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Topology
open Filter
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
open ProbeMellinBoundary
theorem cube_height_budget_eventually (n : ℕ) (τ dmin cost : ℝ)
    (hτ : 0<τ) (hc : 0≤cost) (hgap : 2*τ<dmin*cost) :
    ∀ᶠ Z : ℝ in atTop,∀i : ℕ,i≤n → ∀d : ℝ,dmin≤d →
      (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^cost := by
  have habs := HeckeDyadic.constant_absorbed_eventually
    ((3*(n:ℝ)+5)^2) (dmin*cost-2*τ) (by linarith)
  filter_upwards [habs,eventually_ge_atTop (1:ℝ)] with Z hC hZ
  intro i hi d hd
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hpow : 1≤Z^τ := Real.one_le_rpow hZ hτ.le
  have hi' : (i:ℝ)≤n := by exact_mod_cast hi
  have hx : 3+(3*i+2:ℕ)*Z^τ≤(3*(n:ℝ)+5)*Z^τ := by
    push_cast
    nlinarith
  calc
    _ ≤ ((3*(n:ℝ)+5)*Z^τ)^2 := by
      apply sq_le_sq₀ (by positivity) (by positivity) |>.mpr hx
    _ = (3*(n:ℝ)+5)^2*Z^(2*τ) := by
      rw [mul_pow]
      congr 1
      rw [←Real.rpow_two,←Real.rpow_mul hZp.le]
      congr 1
      ring
    _ ≤ Z^(dmin*cost-2*τ)*Z^(2*τ) :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le _)
    _ = Z^(dmin*cost) := by rw [←Real.rpow_add hZp];congr 1;ring
    _ ≤ (Z^d)^cost := by
      rw [←Real.rpow_mul hZp.le]
      exact Real.rpow_le_rpow_of_exponent_le hZ (mul_le_mul_of_nonneg_right hd hc)

theorem source_cube_height_eventually (τ : ℝ) (hτ : 0<τ) :
    ∀ᶠ Z : ℝ in atTop,1≤Z ∧ 2<Z^τ := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ))] with Z hZ hpow
  exact ⟨hZ,hpow⟩

lemma cube_buffered_heights (t : HeightSpace) (H B : ℝ) (i : ℕ)
    (ht : (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H) (hB : 0≤B)
    (hbuffer : H+B/2≤(3*i+2:ℕ)*B) :
    |t.1.1|≤(3*i+2:ℕ)*B ∧ |t.2|≤(3*i+2:ℕ)*B ∧
      |t.1.2|+B/2≤(3*i+2:ℕ)*B := by
  constructor
  · linarith [ht.1.1]
  constructor
  · linarith [ht.1.2]
  · linarith [ht.2]


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.cube_height_budget_eventually

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.source_cube_height_eventually

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.cube_buffered_heights
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.cube_buffered_heights
