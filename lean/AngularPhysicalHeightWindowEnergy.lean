import AngularPhysicalPlainHeight
import OAI.NumberTheory.DirichletL.Moments.HeckeWindowEnergy

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace OAI.SevenEighths.Angular.PlainRows.WindowEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy FourierBridge
open CenteredMomentHeckeColumnWindow (columnDensity columnDensity_moments)
open CenteredMomentHeckeWindowEnergy (finite_weighted_integral_energy heightCost heightCost_pos norm_height_shift)
local notation "O" => ActualEisensteinCubic.O

theorem gauss_column_integrable {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : AngularCharacter) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    Integrable (fun w : ℝ => columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      gaussPolynomial S a ha (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z) := by
  have hi (i : α) := ((height_column_integrable V hVc hVs τ _ (ha i).1 t θ X hX).const_mul (β i)).mul_const
    (gaussRow (a i) (ha i) z)
  convert integrable_finsetSum S (fun i _ => hi i) using 1
  funext w
  simp only [gaussPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem window_energy_from_shifted {α : Type*}
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : AngularCharacter) (t θ X : ℝ) (hX : 0<X) (rows : Finset O)
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀ w : ℝ,(∑ z∈rows,‖gaussPolynomial S a ha
      (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z‖^2)≤
      E*(1+‖w‖)^(2*J)) :
    (∑ z∈rows,‖gaussPolynomial S a ha (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) z‖^2)≤
      E*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  let φ := fun z : rows => fun w : ℝ => logPhase (θ-w) (Real.log X)*
    gaussPolynomial S a ha (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z
  have hi (z : rows) : Integrable (fun w => columnDensity V hVc hVs w*φ z w) := by
    simpa only [φ,mul_assoc] using gauss_column_integrable S a ha β τ t θ X hX V hVc hVs z
  have hb (w : ℝ) : (∑ z : rows,‖φ z w‖^2)≤E*((1+‖w‖)^J)^2 := by
    simp only [φ,norm_mul,logPhase_norm,one_mul,← pow_mul]
    rw [Finset.sum_coe_sort rows (fun z : O => ‖gaussPolynomial S a ha
      (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z‖^2)]
    simpa only [Nat.mul_comm] using henergy w
  have hh := finite_weighted_integral_energy (columnDensity V hVc hVs) φ
    (fun w => (1+‖w‖)^J) (by intro w;positivity) E hE
    (columnDensity_moments V hVc hVs J) hi hb
  calc
    _ = ∑ z : rows,‖∫ w : ℝ,columnDensity V hVc hVs w*φ z w‖^2 := by
      rw [← Finset.sum_coe_sort rows]
      apply Finset.sum_congr rfl
      intro z hz
      rw [gauss_column_integral S a ha β τ t θ X hX V hVc hVs z]
      simp only [φ,mul_assoc]
    _ ≤ _ := hh

theorem window_energy_from_height {α : Type*}
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : AngularCharacter) (t θ X : ℝ) (hX : 0<X) (rows : Finset O)
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀ v : ℝ,(∑ z∈rows,‖gaussPolynomial S a ha
      (fun i => β i*heightCoeff τ v (Ideal.span {a i})) z‖^2)≤E*(1+‖v‖)^(2*J)) :
    (∑ z∈rows,‖gaussPolynomial S a ha (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) z‖^2)≤
      (E*heightCost t θ^(2*J))*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  apply window_energy_from_shifted V hVc hVs J S a ha β τ t θ X hX rows
    (E*heightCost t θ^(2*J)) (mul_nonneg hE (pow_nonneg (heightCost_pos t θ).le _))
  intro w
  calc
    _ ≤ E*(1+‖t+2*Real.pi*(w-θ)‖)^(2*J) := henergy _
    _ ≤ E*(heightCost t θ*(1+‖w‖))^(2*J) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (norm_height_shift t θ w) _) hE
    _ = _ := by rw [mul_pow,mul_assoc]

end OAI.SevenEighths.Angular.PlainRows.WindowEnergy

#print axioms OAI.SevenEighths.Angular.PlainRows.WindowEnergy.gauss_column_integrable
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.WindowEnergy.gauss_column_integrable

#print axioms OAI.SevenEighths.Angular.PlainRows.WindowEnergy.window_energy_from_shifted
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.WindowEnergy.window_energy_from_shifted

#print axioms OAI.SevenEighths.Angular.PlainRows.WindowEnergy.window_energy_from_height
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.WindowEnergy.window_energy_from_height
