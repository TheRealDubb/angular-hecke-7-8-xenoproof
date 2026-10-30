import AngularPhysicalFirstSourceSupport
import OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalPrefactor

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows.FirstPhysical.Prefactor
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CommonRows Support
open CanonicalQuadraticSieve CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstActiveRadicalBudget CenteredMomentRankinRadical
open CenteredMomentExceptionalAmplitudePair CenteredMomentSupportedCorrelation
open CenteredMomentFirstPhysicalSource (scalar inactiveWeight)
open CenteredMomentFirstNonexceptionalPrefactor (scalar_conductor_algebra weighted_scalar_volume)
local notation "O" => ActualEisensteinCubic.O

theorem actual_scalar_conductors (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (E:Finset (CommonIndex C D))(η τ₁ τ₂:AngularCharacter)
    (K A₀ B₀ a T M F:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)(ha:0<a)(hT:0<T)(hF:0≤F)
    (hl:a*T≤(C.absNorm:ℝ)*Real.exp M*A₀)
    (hr:a*T≤(D.absNorm:ℝ)*Real.exp M*B₀)
    (hc₁:(τ₁.modulus.absNorm:ℝ)≤F*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2)
    (hc₂:(τ₂.modulus.absNorm:ℝ)≤F*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2):
    ‖scalar C D hC E K A₀ B₀‖*T/((C.absNorm:ℝ)*D.absNorm)*
      Real.sqrt ((τ₁.modulus.absNorm:ℝ)*τ₂.modulus.absNorm)≤
      ‖inactiveWeight C D E‖*(Real.exp M/a)*F*K*(η.modulus.absNorm:ℝ)/
        (commonRadical C D).absNorm := by
  have hN:0<(C.absNorm:ℝ)*D.absNorm:=mul_pos
    (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1))
    (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1))
  have he:0<‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖:=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero _ (subsetGenerator_supported C D hC E)))
  have hrpos:0<‖eisEmbedding (activeConductor C D)‖:=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero _ (activeConductor_supported C D hC)))
  have hh:=scalar_conductor_algebra _ _ K T _ _ _ (Real.exp M/a) F (η.modulus.absNorm:ℝ)
    (τ₁.modulus.absNorm:ℝ) (τ₂.modulus.absNorm:ℝ) (norm_nonneg _) (norm_nonneg _)
    hK.le hT hN (sq_pos_of_pos he) hrpos (by positivity) hF (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (weighted_scalar_volume C D hC E K A₀ B₀ a T M hK hA hB ha hT hl hr) hc₁ hc₂
  have hroot:=active_root_le_radical C D hC.1 hD.1
  rw [←eisEmbedding_norm_sq_eq_absNorm_span,Real.sqrt_sq (norm_nonneg _)] at hroot
  exact hh.trans ((mul_le_mul_of_nonneg_left hroot (by positivity)).trans_eq (by ring))

theorem original_scalar_conductors {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed:Ideal O)(a₁ a₂:ℝ)(ha₁:0<a₁)(ha₂:0<a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (E:Finset (CommonIndex C D))(rows:Finset O)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (K K₀ H₀ A₀ B₀ M F:ℝ)(τ₁ τ₂:AngularCharacter)
    (hK:0<K)(hA:0<A₀)(hB:0<B₀)(hF:0≤F)(hwin:∀i y,V i y≠0→|y|≤M)
    (hn:block s.η m A t S (CommonRows.coefficient s R seed)
      C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0)
    (hc₁:(τ₁.modulus.absNorm:ℝ)≤F*(s.η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2)
    (hc₂:(τ₂.modulus.absNorm:ℝ)≤F*(s.η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2):
    ‖scalar C D hC E K A₀ B₀‖*CommonRows.volume s/((C.absNorm:ℝ)*D.absNorm)*
      Real.sqrt ((τ₁.modulus.absNorm:ℝ)*τ₂.modulus.absNorm)≤
      ‖inactiveWeight C D E‖*(Real.exp M/((∏i,s.lo i)*a₁*a₂))*F*K*(s.η.modulus.absNorm:ℝ)/
        (commonRadical C D).absNorm := by
  have ha:0<(∏i,s.lo i)*a₁*a₂:=
    mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) ha₁) ha₂
  obtain ⟨hl,hr⟩:=block_reference_lower s.η m A t S
    (CommonRows.coefficient s R seed) C D hC hD E rows W V
    K K₀ H₀ A₀ B₀ ((∏i,s.lo i)*a₁*a₂) (CommonRows.volume s) M hA hB
    (fun I hi=>original_column_lower s R seed I a₁ a₂ ha₁.le ha₂.le hs₁ hs₂ hi) hwin hn
  exact actual_scalar_conductors C D hC hD E s.η τ₁ τ₂ K A₀ B₀ _ _ M F hK hA hB
    ha (CommonRows.volume_pos s) hF hl hr hc₁ hc₂

end OAI.SevenEighths.Angular.PlainRows.FirstPhysical.Prefactor

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.Prefactor.actual_scalar_conductors
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.Prefactor.actual_scalar_conductors

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.Prefactor.original_scalar_conductors
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.Prefactor.original_scalar_conductors
