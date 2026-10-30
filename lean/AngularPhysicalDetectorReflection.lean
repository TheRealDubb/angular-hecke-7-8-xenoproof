import AngularPhysicalDetectorBuffered
import AngularImprimitiveReflection
import OAI.NumberTheory.DirichletL.Hecke.DyadicReflectedFamily

noncomputable section
open scoped Classical Topology ComplexConjugate
open Set Complex
namespace OAI.SevenEighths.Angular.PhysicalDetectorDyadic
open FamilyContinuation PrimitiveReduction PhysicalLogarithmicInput PhysicalLogarithmic
open HeckeDeletionBounds

theorem original_reflected_subpower (angularOrder:ℕ) (ε:ℝ) (hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀χ:AngularCharacter,χ.k.natAbs≤angularOrder→
      (χ.k≠0 ∨ χ.residue≠1)→∀s:ℂ,-(1/10:ℝ)≤s.re→s.re≤1/2→
    ‖LFunction χ s‖≤C*(χ.modulus.absNorm:ℝ)^(1/2-s.re)*
      ((radical χ.modulus).absNorm:ℝ)^(max (-s.re) 0+2*ε)*
      (3+|s.im|)^2*‖LFunction χ (1-conj s)‖ := by
  induction angularOrder with
  | zero =>
    obtain ⟨C,hC,hb⟩:=HeckeDyadicReflection.original_reflected_subpower ε hε
    refine ⟨C,hC,?_⟩
    intro χ horder hn s hl hr
    have hk:χ.k=0:=Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero horder)
    have hχ:χ.residue≠1:=hn.resolve_left (not_not.mpr hk)
    have hh:=hb (FiniteIdentification.toFinite χ hk) hχ s hl hr
    rw [←TypeZeroEntire.LFunction_eq_finite χ hk hχ s,
      ←TypeZeroEntire.LFunction_eq_finite χ hk hχ (1-conj s)] at hh
    have hmod : (FiniteIdentification.toFinite χ hk).modulus = χ.modulus := rfl
    rwa [hmod] at hh
  | succ n ih =>
    obtain ⟨C,hC,hb⟩:=ih
    obtain ⟨D,hD,hd⟩:=PlainReflection.original_reflected_subpower (n+1) ε hε
    refine ⟨C+D,by positivity,?_⟩
    intro χ horder hn s hl hr
    by_cases hold:χ.k.natAbs≤n
    · apply (hb χ hold hn s hl hr).trans
      gcongr <;> linarith
    · have he:χ.k.natAbs=n+1:=by omega
      have hk:χ.k≠0:=by intro h;simp only [h,Int.natAbs_zero] at he;omega
      apply (hd χ hk he s hl hr).trans
      gcongr <;> linarith

theorem original_upper_strip (angularOrder:ℕ) (ε:ℝ) (hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀χ:AngularCharacter,χ.k.natAbs≤angularOrder→
      (χ.k≠0 ∨ χ.residue≠1)→∀s:ℂ,-(1/10:ℝ)≤s.re→
      ‖LFunction χ s‖≤C*(χ.modulus.absNorm:ℝ)^(3/5:ℝ)*
        ((radical χ.modulus).absNorm:ℝ)^(1/10+ε)*(3+|s.im|)^2 := by
  obtain ⟨Cg,hCg,hgrowth⟩:=regular_bounded_order_growth angularOrder
  obtain ⟨Cd,hCd,hdelete⟩:=DeletionBounds.factors_any_re_subpower_bound ε hε
  refine ⟨Cg*Cd,by positivity,?_⟩
  intro χ horder hn s hs
  have hp:=NaturalPrimitive.primitive_nonprincipal χ hn
  have hg:=hgrowth (primitive χ) horder (primitive_isPrimitive χ) s hs
  rw [regular_eq_nonprincipal (primitive χ) hp] at hg
  have hQ:((primitive χ).modulus.absNorm:ℝ)^(3/5:ℝ)≤
      (χ.modulus.absNorm:ℝ)^(3/5:ℝ):=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast PrimitiveReduction.norm_le χ) (by norm_num)
  have hrad:1≤((radical χ.modulus).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero _))
  have hd:‖factors χ s‖≤Cd*((radical χ.modulus).absNorm:ℝ)^(1/10+ε):=by
    apply (hdelete χ.modulus (primitive χ) s).trans
    apply mul_le_mul_of_nonneg_left _ hCd.le
    apply Real.rpow_le_rpow_of_exponent_le hrad
    have hm:max (-s.re) 0≤1/10:=max_le (by linarith) (by norm_num)
    linarith
  rw [PhysicalDetectorPrimitive.nonprincipal_primitive_identity χ hn s,norm_mul]
  calc
    _≤(Cg*((primitive χ).modulus.absNorm:ℝ)^(3/5:ℝ)*(3+|s.im|)^2)*
        (Cd*((radical χ.modulus).absNorm:ℝ)^(1/10+ε)):=
      mul_le_mul hg hd (norm_nonneg _) (by positivity)
    _≤(Cg*(χ.modulus.absNorm:ℝ)^(3/5:ℝ)*(3+|s.im|)^2)*
        (Cd*((radical χ.modulus).absNorm:ℝ)^(1/10+ε)):=by gcongr
    _= _:=by ring

end OAI.SevenEighths.Angular.PhysicalDetectorDyadic


#print axioms OAI.SevenEighths.Angular.PhysicalDetectorDyadic.original_reflected_subpower
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorDyadic.original_reflected_subpower

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorDyadic.original_upper_strip
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorDyadic.original_upper_strip
