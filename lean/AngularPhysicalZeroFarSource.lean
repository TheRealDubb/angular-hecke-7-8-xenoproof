import AngularPhysicalUniformRetained
import AngularPhysicalUniformOriginalEnergy

/-! The far-reflection branch for the actual angular transform. The retained
source vanishes by its annular support, before any growth estimate is used. -/
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace OAI.SevenEighths.Angular.NaturalZeroGrowth
open Dyadic AnnularFourier UniformReflectionApproximation RetainedWeighted
open CenteredMomentNaturalPrimitive CenteredMomentSectorLocalization
open CenteredMomentReflectionDeletion (SmoothIdeal norm)
open CenteredMomentReflectedTruncation (retainedAnnuli)
open OriginalReflectionApproximation (finiteAnnularColumn)

theorem eventually_retained_source_zero (C xi:ℝ) (hC:0<C) (hxi:0<xi):
    ∀ᶠ Z:ℝ in atTop, 1<Z ∧ ∀(χ ψ:AngularCharacter)(M along:ℝ),
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      (χ.modulus.absNorm:ℝ)≤C*Z^M → M+xi<along →
      ∀(a b:ℝ)(ha:0<a)(G:𝓢(ℝ,ℂ)),
        retainedSource χ ψ a b ha G (Z^along) (Z^(xi/4))=0 := by
  filter_upwards [UniformRetained.eventually_natural_choice_geometry C xi hC hxi]
    with Z hZ
  refine ⟨hZ.1,?_⟩
  intro χ ψ M along hcap hmod hfar a b ha G
  unfold retainedSource
  apply Finset.sum_eq_zero
  intro D hD
  trans ∑' I : SmoothIdeal (sourcePrimes χ ψ), (0:ℂ)
  swap
  · simp
  apply tsum_congr
  intro I
  let Ds:(sourcePrimes χ ψ).powerset:=⟨D,hD⟩
  have hy:=dualScale_pos χ ψ (Z^along)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _) Ds I
  have hempty:retainedAnnuli (Z^(xi/4)) (dualScale χ ψ (Z^along) Ds I) hy=∅:=by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    have hh:=hZ.2 χ ψ M along hcap hmod ((Ds,I),n) hy hn
    have hp:=Real.log_pos hZ.1
    have hx:0≤(M-along+xi)*Real.log Z:=hh.2.1.trans hh.2.2
    have hnneg:(M-along+xi)*Real.log Z<0:=
      mul_neg_of_neg_of_pos (by linarith) hp
    linarith
  change _ * finiteAnnularColumn χ.conjugate (profile ψ.k a b ha G)
    (Z^(xi/4)) (dualScale χ ψ (Z^along) Ds I)=0
  rw [finiteAnnularColumn,dif_pos hy,hempty]
  simp

theorem finite_original_error (angularOrder:ℕ) (a b:ℝ) (ha:0<a)
    (xi saving Cscale epsilon:ℝ) (hxi:0<xi)(hscale:0<Cscale)(hepsilon:0<epsilon):
    ∃H:Finset (ℕ×ℕ),∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
      ∀{ι:Type}[Fintype ι],∀χ:ι→AngularCharacter,
      (∀i,(χ i).k.natAbs=angularOrder) →
      (∀i,(χ i).k≠0 ∨ (χ i).residue≠1) →
      ∀(G:ι→𝓢(ℝ,ℂ))(P:ι→ℂ)(Z M along Src Rcap:ℝ),
      (∀i,Function.support (G i:ℝ→ℂ)⊆Set.Icc a b) → Z₀≤Z →
      M+xi<along → 0<Src → 1≤Rcap →
      (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤Src) →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
      (∑i,‖polynomial (χ i) false (G i) (Z^along) 0 0*P i‖^2)≤
        C*Rcap^(2*epsilon)*Src^2*Z^(-2*saving)*(∑i,‖P i‖^2) := by
  obtain ⟨H,C,hC,happrox⟩:=actual_original_energy_to_retained angularOrder a b ha
    (xi/2) saving 0 Cscale epsilon (by positivity) hscale hepsilon
  obtain ⟨Z₁,hZ₁⟩:=eventually_atTop.mp
    (eventually_retained_source_zero Cscale xi hscale hxi)
  refine ⟨H,C,max 2 Z₁,hC,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro ι _ χ hkχ hχ G P Z M along Src Rcap hsG hZ₀ hfar hSrc hR hGS hmod hcap
  obtain ⟨ψ,hψ,henergy⟩:=happrox χ hkχ hχ
  have hZ:=hZ₁ Z ((le_max_right _ _).trans hZ₀)
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hzero(i:ι):retainedSource (χ i) (ψ i) a b ha (G i) (Z^along) (Z^(xi/4))=0:=
    hZ.2 (χ i) (ψ i) M along (hψ i).2.2.2 (hmod i) hfar a b ha (G i)
  have hsource(i:ι):((χ i).modulus.absNorm:ℝ)≤Cscale*Z^(0:ℝ)*Z^along:=by
    simp only [Real.rpow_zero,mul_one]
    exact (hmod i).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith)) hscale.le)
  have hh:=henergy G (fun _=>Z^along) P Src Z Rcap hsG hSrc hZ.1.le hR
    (fun _=>Real.rpow_pos_of_pos hz _) hGS hcap hsource
  rw [show (xi/2)/2=xi/4 by ring] at hh
  simpa only [hzero,zero_mul,norm_zero,zero_pow (by decide : 2≠0),
    Finset.sum_const_zero,mul_zero,zero_add] using hh

end OAI.SevenEighths.Angular.NaturalZeroGrowth

#print axioms OAI.SevenEighths.Angular.NaturalZeroGrowth.eventually_retained_source_zero
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalZeroGrowth.eventually_retained_source_zero

#print axioms OAI.SevenEighths.Angular.NaturalZeroGrowth.finite_original_error
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalZeroGrowth.finite_original_error
