import AngularPhysicalAnnularPoissonCharacter

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.AnnularReflection
open EisensteinSchwartzPoisson AnnularSchwartz AnnularFourier ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal
variable (c:O) [instc:NeZero c]

theorem primitive_plain_reflection (ψ:AngularCharacter) (hmod:ψ.modulus=Ideal.span {c})
    (hp:FiniteFourier.IsPrimitiveOnIdeals (hmod ▸ ψ.residue)) (hn:ψ.k≠0 ∨ ψ.residue≠1)
    (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ)) (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
    (X:ℝ) (hX:0<X) :
    (∑'I:NI,ψ.idealHom I.val*W ((I.val.absNorm:ℝ)/X))=
      ((X:ℂ)*annularReflectionScalar c ψ hmod/(‖eisEmbedding c‖:ℂ))*
      ∑'I:NI,ψ.conjugate.idealHom I.val*
        profile ψ.k a b ha W ((I.val.absNorm:ℝ)/(‖eisEmbedding c‖^2/X)) := by
  have hc:0<‖eisEmbedding c‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))
  have hY:0<‖eisEmbedding c‖^2/X:=div_pos (sq_pos_of_pos hc) hX
  have hh:=primitive_raw_annular_poisson c ψ.k (hmod ▸ ψ.residue) hp a b ha W hs
    (primitive_zero_mode c ψ hmod hn a b ha W hs) X hX
  simp_rw [rawCoefficient_actual c ψ hmod,rawCoefficient_conjugate c ψ hmod] at hh
  rw [radial_ideal_reindex ψ W X (original_radial_summable ψ W X hX),
    radial_ideal_reindex ψ.conjugate _ _
      (reflected_radial_summable ψ.conjugate ψ.k a b ha W hs _ hY)] at hh
  have hN:(Ideal.absNorm (Ideal.span {c}):ℂ)=(‖eisEmbedding c‖:ℂ)^2 := by
    exact_mod_cast (ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span c).symm
  have hfac:((X:ℂ)*alpha c^ψ.k*TraceCharacter.gaussScalar c (hmod ▸ ψ.residue)/
      (Ideal.absNorm (Ideal.span {c}):ℂ))=
      (X:ℂ)*annularReflectionScalar c ψ hmod/(‖eisEmbedding c‖:ℂ) := by
    rw [hN,annularReflectionScalar,TraceCharacter.normalizedGauss]
    ring
  rw [hfac] at hh
  linear_combination hh/6

theorem primitive_normalized_reflection (ψ:AngularCharacter) (hmod:ψ.modulus=Ideal.span {c})
    (hp:FiniteFourier.IsPrimitiveOnIdeals (hmod ▸ ψ.residue)) (hn:ψ.k≠0 ∨ ψ.residue≠1)
    (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ)) (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
    (X:ℝ) (hX:0<X) :
    Dyadic.polynomial ψ false W X 0 0=annularReflectionScalar c ψ hmod*
      Dyadic.polynomial ψ.conjugate false (profile ψ.k a b ha W) (‖eisEmbedding c‖^2/X) 0 0 := by
  have hc:0<‖eisEmbedding c‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))
  have hY:0<‖eisEmbedding c‖^2/X:=div_pos (sq_pos_of_pos hc) hX
  rw [PlainDeletion.polynomial_plain _ _ _ hX,
    primitive_plain_reflection c ψ hmod hp hn a b ha W hs X hX,
    PlainDeletion.polynomial_plain _ _ _ hY]
  have hsq:Real.sqrt (‖eisEmbedding c‖^2/X)=‖eisEmbedding c‖/Real.sqrt X := by
    rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq hc.le]
  have hx:(Real.sqrt X:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  have hcn:(‖eisEmbedding c‖:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hc.ne'
  have hx2:(Real.sqrt X:ℂ)^2=(X:ℂ):=by exact_mod_cast Real.sq_sqrt hX.le
  have hfac:(Real.sqrt X:ℂ)⁻¹*((X:ℂ)*annularReflectionScalar c ψ hmod/(‖eisEmbedding c‖:ℂ))=
      annularReflectionScalar c ψ hmod*(Real.sqrt (‖eisEmbedding c‖^2/X):ℂ)⁻¹ := by
    rw [hsq,Complex.ofReal_div]
    field_simp
    rw [hx2]
  rw [←mul_assoc,hfac,mul_assoc]

end OAI.SevenEighths.Angular.AnnularReflection

#print axioms OAI.SevenEighths.Angular.AnnularReflection.primitive_normalized_reflection
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AnnularReflection.primitive_normalized_reflection
