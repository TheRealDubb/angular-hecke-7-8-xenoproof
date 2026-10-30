import AngularPhysicalAnnularIdealReindex

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.AnnularReflection
open EisensteinSchwartzPoisson AnnularSchwartz AnnularFourier PlaneVolume ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def complexPhase (z:ℂ) : ℂ := z/(‖z‖:ℂ)

theorem complexPhase_mul_positive (s:ℝ) (hs:0<s) (z:ℂ) :
    complexPhase ((s:ℂ)*z)=complexPhase z := by
  unfold complexPhase
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs,Complex.ofReal_mul]
  exact mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr hs.ne')

theorem complexPhase_div (z w:ℂ) :
    complexPhase (z/w)=complexPhase z/complexPhase w := by
  unfold complexPhase
  rw [norm_div,Complex.ofReal_div]
  exact div_div_div_comm _ _ _ _

theorem scaled_fourier_nonzero (k:ℤ) (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b) (X:ℝ) (hX:0<X)
    (c z:O) (hc:c≠0) (hz:z≠0) :
    paperFourier (scaledPlane (annularCLM k a b ha W) X hX)
      (eisEmbedding z/eisEmbedding c)=
    ((X:ℂ)*alpha c^k)*alpha z^(-k)*
      profile k a b ha W (‖eisEmbedding z‖^2/(‖eisEmbedding c‖^2/X)) := by
  have hcE:=eisEmbedding_ne_zero hc
  have hzE:=eisEmbedding_ne_zero hz
  have hsqrt:(Real.sqrt X:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  rw [scaledPlane_fourier,actual_angular_fourier k a b ha W hs _
    (mul_ne_zero hsqrt (div_ne_zero hzE hcE))]
  have hp:complexPhase ((Real.sqrt X:ℂ)*(eisEmbedding z/eisEmbedding c))=alpha z/alpha c := by
    rw [complexPhase_mul_positive _ (Real.sqrt_pos.mpr hX),complexPhase_div]
    rfl
  have hn:‖(Real.sqrt X:ℂ)*(eisEmbedding z/eisEmbedding c)‖^2=
      ‖eisEmbedding z‖^2/(‖eisEmbedding c‖^2/X) := by
    rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg X),Real.sq_sqrt hX.le,norm_div,div_pow]
    rw [div_div_eq_mul_div]
    ring
  change (X:ℝ) • (complexPhase _^(-k)*profile k a b ha W _)=_
  rw [hp,hn,div_zpow,zpow_neg (alpha c)]
  simp only [Complex.real_smul,div_inv_eq_mul]
  ring

end OAI.SevenEighths.Angular.AnnularReflection

#print axioms OAI.SevenEighths.Angular.AnnularReflection.scaled_fourier_nonzero
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AnnularReflection.scaled_fourier_nonzero
