import AngularPhysicalDetectorInitialState
import AngularPhysicalExceptionalForcing
import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFreeExceptional

noncomputable section
open scoped Classical BigOperators
open Filter
namespace OAI.SevenEighths.Angular.PhysicalDetectorInitial
open ExceptionalRows ProbeHighRowFamily UniqueFactorizationMonoid
open HeckeInverseAmplification (FreeRow)
open CenteredExceptionalCount CenteredExceptionalProfile
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
local notation "O" => ActualEisensteinCubic.O

/-- The angular phase cancels in the local valuation argument only because the
inducing character has the same angular type. That equality is retained here. -/
theorem fixed_inducing_free_support (η:AngularCharacter) (Q:Ideal O)
    (hQ0:Q≠0) (hQ:Q≠⊤) (hQ72:Q≤Ideal.span {(72:O)}) (hQη:Q≤η.modulus)
    (m:O) (hm:m≠0) (hml:goodLambda∣m) (hm2:(2:O)∣m)
    (u:FreeRow) (hu:FixedInducingRow η Q m 1 u.val):
    u.val∈HeckeExceptionalRows.rows (normalizedFactors Q).toFinset := by
  obtain ⟨χ,ψ,_,hk,_,hind,hψ,hχ⟩:=hu
  refine ⟨u.property.1,?_⟩
  intro P hP
  refine ⟨?_,u.property.2 P⟩
  by_contra hout
  have hp:Prime P:=prime_of_normalized_factor P hP
  let : P.IsMaximal:=(Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  obtain ⟨hl,h2,hQP⟩:=outside_fixed_support Q hQ0 hQ72 P hp hout
  have hηP:IsCoprime η.modulus P:=hQP.of_isCoprime_of_dvd_left (Ideal.dvd_iff_le.mpr hQη)
  have hz:=actual_row_numerator_valuation_zero η χ ψ hk hind Q hQ hQ72 hψ
    m 1 u.val hm one_ne_zero u.property.1 hml hm2
    (by simpa only [one_mul] using hχ) P hl h2 hQP hηP
  simp only [one_pow,one_mul,valuation] at hz
  have hpos:=Multiset.count_pos.mpr hP
  have hlt:=u.property.2 P
  omega

theorem fixed_exceptional_norm (η:AngularCharacter) (Q:Ideal O)
    (hQ0:Q≠0) (hQ:Q≠⊤) (hQ72:Q≤Ideal.span {(72:O)}) (hQη:Q≤η.modulus)
    (u:FreeRow) (hu:FixedInducingRow η Q (fixedBadMask*idealGenerator 1) 1 u.val):
    (Ideal.span {u.val}).absNorm≤HeckeExceptionalRows.bound (normalizedFactors Q).toFinset := by
  apply HeckeExceptionalRows.row_norm_bound _
    (fun P hP=>prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP))
  exact fixed_inducing_free_support η Q hQ0 hQ hQ72 hQη
    (fixedBadMask*idealGenerator 1)
    (mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero _ one_ne_zero))
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _)) u hu

/-- Uniform over a fixed finite dictionary, with the threshold chosen before
all growing row sets. No finite-order replacement of an angular character. -/
theorem eventually_dictionary_retained {Label:Type*}[Finite Label]
    (η:Label→AngularCharacter) (Q:Label→Ideal O)
    (hQ0:∀l,Q l≠0) (hQt:∀l,Q l≠⊤) (hQ72:∀l,Q l≤Ideal.span {(72:O)})
    (hQη:∀l,Q l≤(η l).modulus) (c:ℝ) (hc:0<c):
    ∀ᶠZ:ℝ in atTop,∀l:Label,∀u:FreeRow,
      Z^c≤((Ideal.span {u.val}).absNorm:ℝ)→initialKeep (η l) (Q l) u.val := by
  have hb:∀ᶠZ:ℝ in atTop,∀l:Label,
      (HeckeExceptionalRows.bound (normalizedFactors (Q l)).toFinset:ℝ)<Z^c := by
    apply Filter.eventually_all.mpr
    intro l
    exact (tendsto_rpow_atTop hc).eventually (eventually_gt_atTop _)
  filter_upwards [hb] with Z hz
  intro l u hu
  refine ⟨u.property.1,?_⟩
  intro hex
  have hn:((Ideal.span {u.val}).absNorm:ℝ)≤
      (HeckeExceptionalRows.bound (normalizedFactors (Q l)).toFinset:ℝ) := by
    exact_mod_cast fixed_exceptional_norm (η l) (Q l) (hQ0 l) (hQt l) (hQ72 l) (hQη l) u hex
  exact (not_lt_of_ge (hu.trans hn)) (hz l)

end OAI.SevenEighths.Angular.PhysicalDetectorInitial


#print axioms OAI.SevenEighths.Angular.PhysicalDetectorInitial.fixed_inducing_free_support
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorInitial.fixed_inducing_free_support

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorInitial.fixed_exceptional_norm
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorInitial.fixed_exceptional_norm

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorInitial.eventually_dictionary_retained
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorInitial.eventually_dictionary_retained
