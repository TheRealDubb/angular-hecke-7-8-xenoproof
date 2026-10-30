import AngularPhysicalCommonMaskSlots
import OAI.NumberTheory.DirichletL.Hecke.PrimeAnnular
import OAI.NumberTheory.DirichletL.Hecke.DetectorRowwise
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option autoImplicit false
set_option maxHeartbeats 1600000
-- Fixed finite profile interpolation controls the actual common prime height.
-- There is no factor depending on the number of primes or the row conductor.

namespace OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight
noncomputable section
open scoped Classical BigOperators
open _root_.Polynomial

/-- Fixed coefficients that extract the first coefficient of a polynomial
of degree at most `N` from its values at `0,...,N`. -/
def derivativeWeight (N : ℕ) (j : Fin (N+1)) : ℂ :=
  (Lagrange.basis Finset.univ (fun k : Fin (N+1)=>(k.val:ℂ)) j).coeff 1

theorem coefficient_one_interpolation (N : ℕ) (p : Polynomial ℂ)
    (hp : p.natDegree≤N) :
    p.coeff 1 = ∑j : Fin (N+1),derivativeWeight N j*p.eval (j.val:ℂ) := by
  have hi : Set.InjOn (fun k : Fin (N+1)=>(k.val:ℂ)) (Finset.univ : Finset (Fin (N+1))) := by
    intro a _ b _ h
    apply Fin.ext
    change (a.val:ℂ)=(b.val:ℂ) at h
    exact_mod_cast h
  have hd : p.degree<(Finset.univ : Finset (Fin (N+1))).card := by
    apply lt_of_le_of_lt degree_le_natDegree
    simp only [Finset.card_univ,Fintype.card_fin]
    exact_mod_cast Nat.lt_succ_of_le hp
  have he := congrArg (fun q : Polynomial ℂ=>q.coeff 1) (Lagrange.eq_interpolate hi hd)
  simpa only [Lagrange.interpolate_apply,finsetSum_coeff,coeff_C_mul,derivativeWeight,
    mul_comm] using he

/-- Differentiating a product of slots is a finite linear combination of
products with one common profile `A + j B`. The interpolation constants
are independent of the rows, scales, and coefficients. -/
theorem first_product_polarization {Slot : Type*} [DecidableEq Slot]
    (slots : Finset Slot) (N : ℕ) (hN : slots.card≤N) (A B : Slot→ℂ) :
    (∑s∈slots,(∏k∈slots.erase s,A k)*B s) =
      ∑j : Fin (N+1),derivativeWeight N j*(∏s∈slots,(A s+(j.val:ℂ)*B s)) := by
  let p : Polynomial ℂ := ∏s∈slots,(C (B s)*X+C (A s))
  have hd : p.natDegree≤N := by
    have hs : (∑s∈slots,(C (B s)*X+C (A s) : Polynomial ℂ).natDegree) ≤ slots.card := by
      calc
        (∑s∈slots,(C (B s)*X+C (A s) : Polynomial ℂ).natDegree) ≤
            ∑s∈slots,(1 : ℕ) := by
          apply Finset.sum_le_sum
          intro s hs
          exact natDegree_linear_le
        _ = slots.card := by simp
    exact (natDegree_prod_le slots (fun s=>(C (B s)*X+C (A s) : Polynomial ℂ))).trans
      (hs.trans hN)
  have hc : p.coeff 1=∑s∈slots,(∏k∈slots.erase s,A k)*B s := by
    have he := congrArg (fun q : Polynomial ℂ=>q.eval 0)
      (derivative_prod_finset (s:=slots) (f:=fun s=>C (B s)*X+C (A s)))
    rw [←Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_derivative] at he
    simpa [p,Polynomial.eval_finsetSum,Polynomial.eval_prod,Polynomial.eval_mul,Polynomial.eval_add] using he
  rw [←hc,coefficient_one_interpolation N p hd]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [p,Polynomial.eval_prod,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X]
  apply Finset.prod_congr rfl
  intro s _
  ring

/-- A single energy estimate for finitely many common profiles controls
all first height derivatives; no estimate for independently varying slot
profiles is required. -/
theorem polarized_product_energy {Row Slot : Type*} [DecidableEq Slot]
    (rows : Finset Row) (slots : Finset Slot) (N : ℕ) (hN : slots.card≤N)
    (A B : Row→Slot→ℂ) (C : Row→ℂ) (E : ℝ)
    (henergy : ∀j : Fin (N+1),
      ∑u∈rows,‖C u*(∏s∈slots,(A u s+(j.val:ℂ)*B u s))‖^2≤E) :
    (∑u∈rows,‖C u*(∑s∈slots,(∏k∈slots.erase s,A u k)*B u s)‖^2)≤
      ((∑j : Fin (N+1),‖derivativeWeight N j‖^2)*(N+1))*E := by
  have each (u : Row) :
      ‖C u*(∑s∈slots,(∏k∈slots.erase s,A u k)*B u s)‖^2≤
      (∑j : Fin (N+1),‖derivativeWeight N j‖^2)*
        ∑j : Fin (N+1),‖C u*(∏s∈slots,(A u s+(j.val:ℂ)*B u s))‖^2 := by
    rw [first_product_polarization slots N hN]
    have he : C u*(∑j : Fin (N+1),derivativeWeight N j*
        (∏s∈slots,(A u s+(j.val:ℂ)*B u s))) =
      ∑j : Fin (N+1),derivativeWeight N j*
        (C u*(∏s∈slots,(A u s+(j.val:ℂ)*B u s))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro _ _
      ring
    rw [he]
    apply le_trans ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _=>norm_nonneg _))).mpr
      (norm_sum_le _ _)) ?_
    simp_rw [norm_mul]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  apply (Finset.sum_le_sum (fun u _=>each u)).trans
  rw [←Finset.mul_sum,Finset.sum_comm]
  have hs := Finset.sum_le_sum (fun j (_:j∈(Finset.univ : Finset (Fin (N+1))))=>henergy j)
  have hw : 0≤∑j : Fin (N+1),‖derivativeWeight N j‖^2 := Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_add,Nat.cast_one,mul_assoc] using mul_le_mul_of_nonneg_left hs hw

end
end OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight


namespace OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight
noncomputable section
open scoped Classical BigOperators
open Set

/-- The fixed loss caused by recovering the derivative through common
profile interpolation. It depends only on the number of live slots. -/
def commonProfileCost (N : ℕ) : ℝ :=
  1+(∑j : Fin (N+1),‖derivativeWeight N j‖^2)*(N+1)

lemma commonProfileCost_ge_one (N : ℕ) : 1≤commonProfileCost N := by
  dsimp [commonProfileCost]
  have h : 0≤(∑j : Fin (N+1),‖derivativeWeight N j‖^2)*(N+1) := by positivity
  linarith

/-- Common-height maximization from finitely many common slot profiles.
Taking `B` to be the logarithmic derivative of the original prime slot
allows every row to choose a different height without losing a power of
its norm. The interpolation nodes are fixed independently of the scale. -/
theorem rowwise_common_profile_energy {Row Slot : Type*} [DecidableEq Slot]
    (rows : Finset Row) (slots : Finset Slot) (N : ℕ) (hN : slots.card≤N)
    (A B : Row→Slot→ℝ→ℂ) (C : Row→ℂ)
    (hA : ∀u∈rows,∀s∈slots,Continuous (A u s))
    (hB : ∀u∈rows,∀s∈slots,Continuous (B u s))
    (hd : ∀u∈rows,∀s∈slots,∀t,HasDerivAt (A u s) (B u s t) t)
    (a b E : ℝ) (hab : a≤b) (hE : 0≤E)
    (choice : Row→ℝ) (hchoice : ∀u∈rows,choice u∈Icc a b)
    (henergy : ∀j : Fin (N+1),∀t∈Icc a b,
      ∑u∈rows,‖C u*(∏s∈slots,(A u s t+(j.val:ℂ)*B u s t))‖^2≤E) :
    (∑u∈rows,‖C u*(∏s∈slots,A u s (choice u))‖^2)≤
      (1+2*(b-a))*commonProfileCost N*E := by
  let F (u : Row) (t : ℝ) := C u*(∏s∈slots,A u s t)
  let F' (u : Row) (t : ℝ) := C u*(∑s∈slots,(∏k∈slots.erase s,A u k t)*B u s t)
  have hc (u : Row) (hu : u∈rows) : Continuous (F u) := by
    exact (continuous_finsetProd slots (fun s hs=>hA u hu s hs)).const_mul _
  have hc' (u : Row) (hu : u∈rows) : Continuous (F' u) := by
    apply Continuous.const_mul
    apply continuous_finsetSum
    intro s hs
    exact (continuous_finsetProd (slots.erase s) (fun k hk=>hA u hu k
      (Finset.mem_of_mem_erase hk))).mul (hB u hu s hs)
  have hderiv (u : Row) (hu : u∈rows) (t : ℝ) : HasDerivAt (F u) (F' u t) t := by
    have hh := (HasDerivAt.finsetProd (fun s hs=>hd u hu s hs t)).const_mul (C u)
    simpa only [F,F',Finset.prod_apply,smul_eq_mul] using hh
  have hk : 0≤commonProfileCost N := zero_le_one.trans (commonProfileCost_ge_one N)
  have h0 (t : ℝ) (ht : t∈Icc a b) : ∑u∈rows,‖F u t‖^2≤commonProfileCost N*E := by
    have he := henergy (0 : Fin (N+1)) t ht
    simp only [Fin.val_zero,Nat.cast_zero,zero_mul,add_zero] at he
    exact he.trans (le_mul_of_one_le_left hE (commonProfileCost_ge_one N))
  have h1 (t : ℝ) (ht : t∈Icc a b) : ∑u∈rows,‖F' u t‖^2≤commonProfileCost N*E := by
    have he := polarized_product_energy rows slots N hN (fun u s=>A u s t)
      (fun u s=>B u s t) C E (fun j=>henergy j t ht)
    apply he.trans
    apply mul_le_mul_of_nonneg_right _ hE
    dsimp only [commonProfileCost]
    linarith
  have he := HeckeDetectorRowwise.rowwise_energy rows F F' hc hc' hderiv a b (commonProfileCost N*E)
    hab choice hchoice h0 h1
  simpa only [F,mul_assoc] using he

end
end OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight


namespace OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight
noncomputable section
open scoped Classical BigOperators ContDiff Topology
open Set Complex

/-- A finite annular prime sum with its normalized ratios exposed. The
coefficient contains the arithmetic character and scale normalization. -/
def annularSum {Index : Type*} (S : Finset Index) (c : Index→ℂ)
    (ratio : Index→ℝ) (W : ℝ→ℂ) (σ t : ℝ) : ℂ :=
  ∑p∈S,c p*W (ratio p)*(ratio p:ℂ)^(-(σ:ℂ)+(t:ℂ)*I)

def heightProfile (W : ℝ→ℂ) (y : ℝ) : ℂ := I*(Real.log y:ℂ)*W y

def commonProfile (W : ℝ→ℂ) (j : ℕ) (y : ℝ) : ℂ :=
  W y+(j:ℂ)*heightProfile W y

theorem commonProfile_support (W : ℝ→ℂ) (j : ℕ) :
    Function.support (commonProfile W j)⊆Function.support W := by
  intro y hy hzero
  exact hy (by simp [commonProfile,heightProfile,hzero])

theorem heightProfile_smooth (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (heightProfile W) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    have he : heightProfile W =ᶠ[nhds (0:ℝ)] (fun _=>0) := by
      filter_upwards [isOpen_Iio.mem_nhds ha] with y hy
      have hw : W y=0 := by
        by_contra hn
        exact (not_le_of_gt hy) (hs hn).1
      simp [heightProfile,hw]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hl : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log y : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_log.mpr hx)
    exact (contDiffAt_const.mul hl).mul hW.contDiffAt

theorem commonProfile_smooth (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (j : ℕ) :
    ContDiff ℝ ∞ (commonProfile W j) :=
  hW.add (contDiff_const.mul (heightProfile_smooth W a b ha hs hW))

theorem annularSum_profile {Index : Type*} (S : Finset Index) (c : Index→ℂ)
    (ratio : Index→ℝ) (W : ℝ→ℂ) (σ t : ℝ) (j : ℕ) :
    annularSum S c ratio (commonProfile W j) σ t=
      annularSum S c ratio W σ t+(j:ℂ)*annularSum S c ratio (heightProfile W) σ t := by
  simp only [annularSum,commonProfile,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

private lemma phase_deriv (x σ t : ℝ) (hx : 0<x) :
    HasDerivAt (fun u : ℝ=>(x:ℂ)^(-(σ:ℂ)+(u:ℂ)*I))
      (I*(Real.log x:ℂ)*(x:ℂ)^(-(σ:ℂ)+(t:ℂ)*I)) t := by
  have hd := (((hasDerivAt_id (t:ℂ)).mul_const I).const_add (-(σ:ℂ))).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hh := hd.comp_ofReal
  rw [←Complex.ofReal_log hx.le] at hh
  convert hh using 1 <;> simp only [id_eq] <;> ring

theorem annularSum_deriv {Index : Type*} (S : Finset Index) (c : Index→ℂ)
    (ratio : Index→ℝ) (hratio : ∀p∈S,0<ratio p)
    (W : ℝ→ℂ) (σ t : ℝ) :
    HasDerivAt (annularSum S c ratio W σ)
      (annularSum S c ratio (heightProfile W) σ t) t := by
  have hd (p : Index) (hp : p∈S) :=
    (phase_deriv (ratio p) σ t (hratio p hp)).const_mul (c p*W (ratio p))
  convert HasDerivAt.sum (u:=S) hd using 1
  · ext u
    simp only [annularSum,Finset.sum_apply]
  · apply Finset.sum_congr rfl
    intro p hp
    simp only [heightProfile]
    ring

theorem annularSum_continuous {Index : Type*} (S : Finset Index) (c : Index→ℂ)
    (ratio : Index→ℝ) (hratio : ∀p∈S,0<ratio p) (W : ℝ→ℂ) (σ : ℝ) :
    Continuous (annularSum S c ratio W σ) := by
  exact (show Differentiable ℝ (annularSum S c ratio W σ) from
    fun t=>(annularSum_deriv S c ratio hratio W σ t).differentiableAt).continuous

/-- Actual annular slot products can choose their common height row by row.
It is enough to know the usual fixed-height moment for the finite common
profiles `W*(1+j*i*log)`, at the same slot widths and arithmetic coefficients. -/
theorem annular_rowwise_energy {Row Slot Index : Type*} [DecidableEq Slot]
    (rows : Finset Row) (slots : Finset Slot) (N : ℕ) (hN : slots.card≤N)
    (pools : Slot→Finset Index) (c : Row→Slot→Index→ℂ)
    (ratio : Slot→Index→ℝ) (hratio : ∀s∈slots,∀p∈pools s,0<ratio s p)
    (W : ℝ→ℂ) (σ v : Slot→ℝ) (C : Row→ℂ)
    (a b E : ℝ) (hab : a≤b) (hE : 0≤E)
    (choice : Row→ℝ) (hchoice : ∀u∈rows,choice u∈Icc a b)
    (henergy : ∀j : Fin (N+1),∀t∈Icc a b,
      ∑u∈rows,‖C u*(∏s∈slots,
        annularSum (pools s) (c u s) (ratio s) (commonProfile W j.val) (σ s) (t+v s))‖^2≤E) :
    (∑u∈rows,‖C u*(∏s∈slots,
      annularSum (pools s) (c u s) (ratio s) W (σ s) (choice u+v s))‖^2)≤
      (1+2*(b-a))*commonProfileCost N*E := by
  apply rowwise_common_profile_energy rows slots N hN
    (fun u s t=>annularSum (pools s) (c u s) (ratio s) W (σ s) (t+v s))
    (fun u s t=>annularSum (pools s) (c u s) (ratio s) (heightProfile W) (σ s) (t+v s)) C
  · intro u hu s hs
    exact (annularSum_continuous (pools s) (c u s) (ratio s) (hratio s hs) W (σ s)).comp
      (continuous_id.add_const _)
  · intro u hu s hs
    exact (annularSum_continuous (pools s) (c u s) (ratio s) (hratio s hs)
      (heightProfile W) (σ s)).comp (continuous_id.add_const _)
  · intro u hu s hs t
    exact (annularSum_deriv (pools s) (c u s) (ratio s) (hratio s hs) W (σ s)
      (t+v s)).comp_add_const t (v s)
  · exact hab
  · exact hE
  · exact hchoice
  · intro j t ht
    simpa only [annularSum_profile] using henergy j t ht

end
end OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight


set_option autoImplicit false
namespace OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight
noncomputable section
open scoped Classical BigOperators
open Set CommonMask HeckePrimeAnnular
local notation "O" => HeckeFamily.O

/-- The annular sum model is exactly the normalized natural prime slot,
with arbitrary arithmetic coefficients and actual character. -/
theorem naturalSlot_eq_annular (χ : AngularCharacter) (pool : Finset (Ideal O))
    (ν : Ideal O→ℂ) (W : ℝ→ℂ) (P σ t : ℝ) :
    naturalSlot χ pool (fun I=>ν I*annularWeight W P σ t I) P=
      annularSum pool (fun I=>(Real.sqrt P:ℂ)⁻¹*χ.idealHom I*ν I)
        (fun I=>(I.absNorm:ℝ)/P) W σ t := by
  unfold naturalSlot annularSum annularWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  have he : -HeckeDyadic.shift σ t=-(σ:ℂ)+(t:ℂ)*Complex.I := by
    unfold HeckeDyadic.shift
    ring
  rw [he]
  ring

/-- An actual marked natural-slot product may choose its common frequency
separately at every row. The energy hypotheses are genuine fixed-frequency
moments for finitely many smooth common profiles. -/
theorem naturalSlot_rowwise_energy {Row Slot : Type*} [DecidableEq Slot]
    (rows : Finset Row) (slots : Finset Slot) (N : ℕ) (hN : slots.card≤N)
    (χ : Row→AngularCharacter) (pools : Slot→Finset (Ideal O))
    (hpools : ∀s∈slots,∀I∈pools s,I≠0)
    (ν : Slot→Ideal O→ℂ) (W : ℝ→ℂ) (P σ v : Slot→ℝ)
    (hP : ∀s∈slots,0<P s) (C : Row→ℂ)
    (a b E : ℝ) (hab : a≤b) (hE : 0≤E)
    (choice : Row→ℝ) (hchoice : ∀u∈rows,choice u∈Icc a b)
    (hmoment : ∀j : Fin (N+1),∀t∈Icc a b,
      ∑u∈rows,‖C u*(∏s∈slots,naturalSlot (χ u) (pools s)
        (fun I=>ν s I*annularWeight (commonProfile W j.val) (P s) (σ s) (t+v s) I)
        (P s))‖^2≤E) :
    (∑u∈rows,‖C u*(∏s∈slots,naturalSlot (χ u) (pools s)
      (fun I=>ν s I*annularWeight W (P s) (σ s) (choice u+v s) I) (P s))‖^2)≤
      (1+2*(b-a))*commonProfileCost N*E := by
  simp_rw [naturalSlot_eq_annular] at hmoment ⊢
  apply annular_rowwise_energy rows slots N hN pools
    (fun u s I=>(Real.sqrt (P s):ℂ)⁻¹*(χ u).idealHom I*ν s I)
    (fun s I=>(I.absNorm:ℝ)/(P s)) ?_ W σ v C a b E hab hE choice hchoice hmoment
  intro s hs I hI
  apply div_pos _ (hP s hs)
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hpools s hs I hI))

end
end OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.coefficient_one_interpolation
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.coefficient_one_interpolation

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.first_product_polarization
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.first_product_polarization

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.polarized_product_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.polarized_product_energy

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.commonProfileCost_ge_one
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.commonProfileCost_ge_one

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.rowwise_common_profile_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.rowwise_common_profile_energy

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.commonProfile_support
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.commonProfile_support

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.heightProfile_smooth
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.heightProfile_smooth

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.commonProfile_smooth
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.commonProfile_smooth

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.annularSum_profile
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.annularSum_profile

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.annularSum_deriv
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.annularSum_deriv

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.annularSum_continuous
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.annularSum_continuous

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.annular_rowwise_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.annular_rowwise_energy

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.naturalSlot_eq_annular
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.naturalSlot_eq_annular

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.naturalSlot_rowwise_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorMarkedHeight.naturalSlot_rowwise_energy
