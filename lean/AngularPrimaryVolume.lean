import AngularAnnularSchwartz
import OAI.NumberTheory.DirichletL.Moments.HeckeVolume

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PrimaryVolume
open CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentPrimary CanonicalQuadraticSieve QuadraticInitialBound
open IdealMobiusDivisorSum UniqueFactorizationMonoid CenteredMomentMask
open PrimaryIdealUnitReindex (GoodIdeal)
open CubicEisenstein (PrimaryLower primaryLowerIdealEquiv)
open AnnularSchwartz PlaneVolume
local notation "O" => ActualEisensteinCubic.O

def primaryCoefficient (ψ : AngularCharacter) : Ideal O →* ℂ where
  toFun I := if primaryGenerator I=0 then 0 else ψ.idealHom I
  map_one' := by simp only [primaryGenerator_one,one_ne_zero,ite_false,map_one]
  map_mul' := by
    intro I J
    simp only [primaryGenerator_mul,map_mul]
    by_cases hI : primaryGenerator I=0 <;> by_cases hJ : primaryGenerator J=0 <;>
      simp only [hI,hJ,mul_eq_zero,or_false,ite_true,ite_false,zero_mul,mul_zero]

theorem primaryCoefficient_good (ψ : AngularCharacter) (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    primaryCoefficient ψ I = ψ.elementCoeff (primaryGenerator I) := by
  change (if primaryGenerator I=0 then 0 else ψ.idealHom I)=_
  rw [ite_eq_right hI]
  conv_lhs => rw [← (primaryGenerator_spec I hI).1,ψ.idealHom_span]

theorem primaryCoefficient_norm (ψ : AngularCharacter) (I : Ideal O) : ‖primaryCoefficient ψ I‖ ≤ 1 := by
  change ‖if primaryGenerator I=0 then 0 else ψ.idealHom I‖ ≤ 1
  split_ifs
  · simp only [norm_zero,zero_le_one]
  · exact ψ.norm_idealHom_le_one I

def periodicValue (c : O) (ψ : AngularCharacter) (r : O ⧸ Ideal.span {c}) : ℂ :=
  if (3:O) ∣ Quotient.out r-1 then ψ.residue (Ideal.Quotient.mk ψ.modulus (Quotient.out r)) else 0

theorem periodicValue_mk (c : O) (h3 : (3:O) ∣ c) (ψ : AngularCharacter)
    (hmod : (Ideal.span {c} : Ideal O) ≤ ψ.modulus) (x : O) :
    periodicValue c ψ (Ideal.Quotient.mk (Ideal.span {c}) x) =
      if (3:O) ∣ x-1 then ψ.residue (Ideal.Quotient.mk ψ.modulus x) else 0 := by
  have hc : c ∣ Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) x)-x :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk _ x)))
  have hd := h3.trans hc
  have hprimary : (3:O) ∣ Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) x)-1 ↔ (3:O) ∣ x-1 := by
    constructor
    · intro h; convert dvd_sub h hd using 1 ; ring
    · intro h; convert dvd_add hd h using 1 ; ring
  have hres : Ideal.Quotient.mk ψ.modulus (Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) x)) =
      Ideal.Quotient.mk ψ.modulus x :=
    Ideal.Quotient.eq.mpr (hmod (Ideal.mem_span_singleton.mpr hc))
  simp only [periodicValue,hprimary,hres]

theorem periodicValue_norm (c : O) (ψ : AngularCharacter) (r : O ⧸ Ideal.span {c}) :
    ‖periodicValue c ψ r‖ ≤ 1 := by
  let : Finite (O ⧸ ψ.modulus) := Ring.HasFiniteQuotients.finiteQuotient ψ.modulus_ne_bot
  let : Fintype (O ⧸ ψ.modulus) := Fintype.ofFinite _
  unfold periodicValue
  split_ifs
  · exact norm_finite_character_le_one ψ.residue _
  · simp only [norm_zero,zero_le_one]

theorem periodic_lattice_term (c : O) (h3 : (3:O)∣c) (ψ : AngularCharacter)
    (hmod : (Ideal.span {c} : Ideal O) ≤ ψ.modulus)
    (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support (W:ℝ→ℂ) ⊆ Set.Icc a b) (X : ℝ) (hX : 0<X) (z : O) :
    periodicValue c ψ (Ideal.Quotient.mk (Ideal.span {c}) z)*
      annularCLM ψ.k a b ha W (eisEmbedding z/(Real.sqrt X:ℂ)) =
      if (3:O)∣z-1 then ψ.elementCoeff z*W (‖eisEmbedding z‖^2/X) else 0 := by
  rw [periodicValue_mk c h3 ψ hmod,annularCLM_scaled ψ.k a b ha W hs X hX]
  by_cases hz : z=0
  · subst z
    have hW0 : W 0=0 := by
      by_contra hw
      have hh := (hs hw).1
      linarith
    simp [hW0]
  · rw [ψ.elementCoeff_eq hz]
    change (if (3:O)∣z-1 then ψ.residue (Ideal.Quotient.mk ψ.modulus z) else 0)*
      (alpha z^ψ.k*W (‖eisEmbedding z‖^2/X))=_
    split_ifs <;> ring

theorem lattice_eq_ideal_sum (c : O) (h3 : (3:O)∣c) (ψ : AngularCharacter)
    (hmod : (Ideal.span {c} : Ideal O) ≤ ψ.modulus)
    (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support (W:ℝ→ℂ) ⊆ Set.Icc a b) (X : ℝ) (hX : 0<X) :
    (∑' z : O,periodicValue c ψ (Ideal.Quotient.mk (Ideal.span {c}) z)*
      annularCLM ψ.k a b ha W (eisEmbedding z/(Real.sqrt X:ℂ))) =
      ∑' I : Ideal O,primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X) := by
  let f : O → ℂ := fun z=>ψ.elementCoeff z*W (‖eisEmbedding z‖^2/X)
  have hleft : (∑' z : O,periodicValue c ψ (Ideal.Quotient.mk (Ideal.span {c}) z)*
      annularCLM ψ.k a b ha W (eisEmbedding z/(Real.sqrt X:ℂ))) = ∑' z : PrimaryLower,f z.val := by
    calc
      _ = ∑' z : O,({z : O | (3:O)∣z-1} : Set O).indicator f z := by
        apply tsum_congr
        intro z
        rw [periodic_lattice_term c h3 ψ hmod W a b ha hs X hX]
        rfl
      _ = _ := (tsum_subtype {z : O | (3:O)∣z-1} f).symm
  have hideal : (∑' I : GoodIdeal, primaryCoefficient ψ I.val*W ((Ideal.absNorm I.val:ℝ)/X)) =
      ∑' I : Ideal O, primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X) := by
    apply tsum_subtype_eq_of_support_subset (s := {I : Ideal O | primaryGenerator I ≠ 0})
      (f := fun I : Ideal O => primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X))
    intro I hI
    change primaryGenerator I ≠ 0
    intro hz
    apply hI
    simp only [primaryCoefficient,MonoidHom.coe_mk,OneHom.coe_mk,hz,ite_true,zero_mul]
  rw [hleft,← hideal,← primaryLowerIdealEquiv.symm.tsum_eq]
  apply tsum_congr
  intro I
  change ψ.elementCoeff (primaryGenerator I.val)*W (‖eisEmbedding (primaryGenerator I.val)‖^2/X)=_
  rw [primaryGenerator_norm_sq I.val I.property,primaryCoefficient_good ψ I.val I.property]

theorem fixed_period_volume (c : O) (hc : c≠0) (h3 : (3:O)∣c)
    (ψ : AngularCharacter) (hmod : (Ideal.span {c} : Ideal O) ≤ ψ.modulus)
    (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support (W:ℝ→ℂ) ⊆ Set.Icc a b) (X : ℝ) (hX : 0<X) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    ‖(∑' I : Ideal O,primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X)) -
      (X/‖eisEmbedding c‖^2:ℝ) • ((∑ r : O ⧸ Ideal.span {c},periodicValue c ψ r)*
        paperFourier (annularCLM ψ.k a b ha W) 0)‖ ≤
      (Fintype.card (O ⧸ Ideal.span {c}):ℝ)*
        (nonzeroLatticeEnvelopeConstant*fourierControl (annularCLM ψ.k a b ha W)) := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [←lattice_eq_ideal_sum c h3 ψ hmod W a b ha hs X hX]
  have h := periodic_plane_volume_error (annularCLM ψ.k a b ha W) X hX c hc (periodicValue c ψ)
  exact h.trans (mul_le_mul_of_nonneg_right (by
    calc
      _ ≤ ∑ _r : O ⧸ Ideal.span {c},(1:ℝ) := Finset.sum_le_sum (fun r _=>periodicValue_norm c ψ r)
      _ = _ := by simp) (mul_nonneg nonzeroLatticeEnvelopeConstant_nonneg (fourierControl_nonneg _)))

end OAI.SevenEighths.Angular.PrimaryVolume
