import AngularPhysicalFirstPhysicalSource
import AngularPhysicalOriginalColumnSupport
import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicAssembly

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows.FirstPhysical
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst
open CenteredMomentFirstReduced CenteredMomentFirstColumns CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentRowNorm
open CenteredMomentFirstWholeKernel CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentDyadicCount CenteredMomentPrimitive
local notation "O" => ActualEisensteinCubic.O

open CenteredMomentFirstPhysicalDyadicAssembly (Blocks effectiveScale effectiveScale_pos
  windows_partition element_norm element_norm_ge_one element_norm_le retained_rows_nonzero)

def retainedBlock (η:AngularCharacter)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(K R:ℝ):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let k:=K/‖eisEmbedding e‖^2
  let r:=activeConductor C D
  inactiveWeight C D E * ∑h∈rows,
    ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      let na:=element C C hC.1 S a
      let nb:=element C D hD.1 S b
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (tripleRow na nb r (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) e *
        ((k/‖eisEmbedding (na*(nb*r))‖^2:ℝ):ℂ)*
        tripleFourier na nb r
          (supported_element_ne_zero _ (element_supported C C hC.1 S a))
          (supported_element_ne_zero _ (element_supported C D hD.1 S b))
          (finitePrimeModulus_ne_zero _) (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) h)*
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
        (retainedWeight R (‖eisEmbedding h‖^2):ℂ)*
        EisensteinSchwartzPoisson.paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (na*(nb*r))‖^2)
      else 0

theorem retainedBlock_eq_blocks
    (η:AngularCharacter)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(hrows:∀h∈rows,h≠0)(W:𝓢(ℝ,ℂ))(K R H:ℝ)(hK:0<K)
    (hcap:∀I,c I≠0→(I.absNorm:ℝ)≤H):
    retainedBlock η m A t S c C D hC hD E rows W K R=
      ∑n:Blocks (effectiveScale C D E K) R (H/(C.absNorm:ℝ)) (H/(D.absNorm:ℝ)),
        block η m A t S c C D hC hD E rows W (fun _=>logAnnulus) K
          (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)):=by
  unfold retainedBlock block
  dsimp only
  rw [←Finset.mul_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab:IsCoprime (a:Ideal O) (b:Ideal O)
  · simp only [hab,ite_true]
    by_cases hca:c (C*(a:Ideal O))=0
    · simp [coefficient,hca]
    by_cases hcb:c (D*(b:Ideal O))=0
    · simp [coefficient,hcb]
    have hnorm:1≤‖eisEmbedding h‖^2:=by
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr (hrows h hh)))
    have hpart:=windows_partition (effectiveScale C D E K) R
      (H/(C.absNorm:ℝ)) (H/(D.absNorm:ℝ)) (‖eisEmbedding h‖^2)
      (‖eisEmbedding (element C C hC.1 S a)‖^2) (‖eisEmbedding (element C D hD.1 S b)‖^2)
      (effectiveScale_pos C D E K hK) hnorm
      ⟨element_norm_ge_one C C hC.1 S a,element_norm_le C C hC.1 S a c H hcap hca⟩
      ⟨element_norm_ge_one C D hD.1 S b,element_norm_le C D hD.1 S b c H hcap hcb⟩
    rw [←Finset.sum_mul,←Finset.mul_sum]
    congr 1
    congr 1
    exact hpart.symm
  · simp [hab]

def retainedInfiniteBlock (η:AngularCharacter)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (W:𝓢(ℝ,ℂ))(K R:ℝ):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let k:=K/‖eisEmbedding e‖^2
  let r:=activeConductor C D
  inactiveWeight C D E * ∑'h:O,
    ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      let na:=element C C hC.1 S a
      let nb:=element C D hD.1 S b
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (tripleRow na nb r (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) e *
        ((k/‖eisEmbedding (na*(nb*r))‖^2:ℝ):ℂ)*
        tripleFourier na nb r
          (supported_element_ne_zero _ (element_supported C C hC.1 S a))
          (supported_element_ne_zero _ (element_supported C D hD.1 S b))
          (finitePrimeModulus_ne_zero _) (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) h)*
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
        (retainedWeight R (‖eisEmbedding h‖^2):ℂ)*
        EisensteinSchwartzPoisson.paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (na*(nb*r))‖^2)
      else 0

theorem retainedInfiniteBlock_eq_finite
    (η:AngularCharacter)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (W:𝓢(ℝ,ℂ))(K R:ℝ):
    retainedInfiniteBlock η m A t S c C D hC hD E W K R=
      retainedBlock η m A t S c C D hC hD E
        (CenteredMomentSecondRetainedRows.retainedRows R 1) W K R:=by
  unfold retainedInfiniteBlock retainedBlock
  dsimp only
  congr 1
  apply tsum_eq_sum
  intro h hh
  have hz:retainedWeight R (‖eisEmbedding h‖^2)=0:=by
    by_contra hn
    apply hh
    apply CenteredMomentSecondRetainedRows.retained_mem_rows R 1 h one_ne_zero
    simpa only [one_mul,normValue_eq_embedding] using hn
  simp only [hz,Complex.ofReal_zero,mul_zero,zero_mul,ite_self,Finset.sum_const_zero]

theorem original_retained_dyadic
    {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:CommonRows.Input ι)(Rbad seed:Ideal O)
    (hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (W:𝓢(ℝ,ℂ))(K R:ℝ)(hK:0<K):
    retainedInfiniteBlock s.η m A t S
      (CommonRows.coefficient s Rbad seed) C D hC hD E W K R=
      ∑n:Blocks (effectiveScale C D E K) R
          (CommonRows.sourceRadius s/(C.absNorm:ℝ))
          (CommonRows.sourceRadius s/(D.absNorm:ℝ)),
        block s.η m A t S (CommonRows.coefficient s Rbad seed)
          C D hC hD E (CenteredMomentSecondRetainedRows.retainedRows R 1) W
          (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
            (dyadicScale (n 2)) (dyadicScale (n 3)):=by
  rw [retainedInfiniteBlock_eq_finite]
  exact retainedBlock_eq_blocks s.η m A t S _ C D hC hD E _
    (retained_rows_nonzero R) W K R _ hK
    (fun I hI=>(CommonRows.original_column_norm s Rbad seed I hz₁ hz₂ hI).2)

end OAI.SevenEighths.Angular.PlainRows.FirstPhysical

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.retainedBlock_eq_blocks
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.retainedBlock_eq_blocks

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.retainedInfiniteBlock_eq_finite
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.retainedInfiniteBlock_eq_finite

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.original_retained_dyadic
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.original_retained_dyadic
