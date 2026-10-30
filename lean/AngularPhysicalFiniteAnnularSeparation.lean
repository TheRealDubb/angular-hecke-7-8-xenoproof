import AngularPhysicalFinite
import OAI.NumberTheory.DirichletL.Moments.ReflectedProfileMeasure

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace OAI.SevenEighths.Angular.AnnularEnergy
open FourierBridge
open CenteredMomentReflectedProfileMeasure (logWindow logWindow_support row_density_energy row_density_energy_two)
local notation "O" => ActualEisensteinCubic.O

theorem finite_annular_separation (V F : ℝ→ℂ) (s X : ℝ) (hX : 0<X)
    (density : 𝓢(ℝ,ℂ))
    (hsep : ∀y : ℝ,V y*F (s*Real.exp y)=
      ∫v : ℝ,(V y*logPhase v y)*density v)
    (η : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀I∈S,I≠0)
    (hc : ∀I : Ideal O,I≠0 → logWindow V ((I.absNorm:ℝ)/X)≠0 → I∈S) :
    Dyadic.polynomial η false (fun x=>logWindow V x*F (s*x)) X 0 0 =
      ∫v : ℝ,density v*Dyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v) := by
  have hnorm (I : Ideal O) (hI : I∈S) : 0<(I.absNorm:ℝ)/X := by
    apply div_pos _ hX
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hI))
  have hi (I : Ideal O) : Integrable (fun v : ℝ=>
      density v*(Dyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X)*
        logPhase v (Real.log ((I.absNorm:ℝ)/X)))) := by
    have ht := ((density.integrable (μ:=volume)).mul_bdd
      (logPhase_continuous_left (Real.log ((I.absNorm:ℝ)/X))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun v=>le_of_eq (logPhase_norm v _)))).mul_const
        (Dyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X))
    apply ht.congr
    filter_upwards [] with v
    ring
  have hp (v : ℝ) : Dyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)=
      (X:ℂ)^(-(1/2:ℂ))*∑I∈S,Dyadic.coefficient η false I*
        logWindow V ((I.absNorm:ℝ)/X)*logPhase v (Real.log ((I.absNorm:ℝ)/X)) := by
    rw [Dyadic.polynomial_eq_finite η false _ X 0 (2*Real.pi*v) S hc]
    congr 1
    apply Finset.sum_congr rfl
    intro I hI
    have hm := HeckeDetectorDyadicBridge.norm_phase (I.absNorm:ℝ) X
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hI))) hX 0 v
    simp only [neg_zero,Complex.cpow_zero,one_mul,Complex.zero_re,Complex.zero_im,sub_zero] at hm
    rw [hm]
    rfl
  rw [Dyadic.polynomial_eq_finite η false _ X 0 0 S
    (fun I hI h=>hc I hI (mul_ne_zero_iff.mp h).1)]
  simp only [Dyadic.shift,Complex.ofReal_zero,zero_mul,sub_self,neg_zero,
    Complex.cpow_zero,mul_one]
  simp_rw [hp]
  have he : (fun v : ℝ=>density v*((X:ℂ)^(-(1/2:ℂ))*
      ∑I∈S,Dyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X)*
        logPhase v (Real.log ((I.absNorm:ℝ)/X)))) =
      (fun v=>(X:ℂ)^(-(1/2:ℂ))*∑I∈S,density v*(Dyadic.coefficient η false I*
        logWindow V ((I.absNorm:ℝ)/X)*logPhase v (Real.log ((I.absNorm:ℝ)/X)))) := by
    funext v
    rw [←Finset.mul_sum]
    ring
  rw [he,integral_const_mul,integral_finsetSum S (fun I _=>hi I)]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  have hh := hsep (Real.log ((I.absNorm:ℝ)/X))
  rw [Real.exp_log (hnorm I hI)] at hh
  simp only [logWindow,ite_eq_left (hnorm I hI)]
  rw [hh,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  ring


end OAI.SevenEighths.Angular.AnnularEnergy

#print axioms OAI.SevenEighths.Angular.AnnularEnergy.finite_annular_separation
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AnnularEnergy.finite_annular_separation
