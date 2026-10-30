import OAI.NumberTheory.DirichletL.Moments.CommonMaskEnergy
import AngularPhysicalDetectorDirectInverse
import AngularPhysicalCommonMaskSlots
import AngularPhysicalNaturalCharacter

open OAI.SevenEighths.Angular
open OAI.SevenEighths.Angular.Dyadic
open OAI.SevenEighths.Angular.InverseRows
open OAI.CubicEisenstein.AngularRawCoefficientGates
open OAI.SevenEighths.Angular.CommonMask
open OAI.SevenEighths.Angular.NaturalRows

-- The finite collision/coloring calculation is retained because the physical
-- intermediate prime pools may overlap. The final bound is for actual angular
-- inverse polynomials, with a cost depending only on the fixed slot count and
-- coefficient bound, never on the number of primes, rows or conductors.

/-!
Finite decoupling of repeated prime slots.  This file develops the finite
algebra needed to extend a uniform disjoint-pool moment estimate.  It does not
assert a nonvanishing theorem.
-/

noncomputable section
open scoped BigOperators Classical

namespace PhysicalRepeatedPrimeSlots

variable {A I : Type*} [Fintype A] [Fintype I]

/-- A coloring which gives every member of a tuple its prescribed slot color. -/
def Compatible (x : I → A) (c : A → I) : Prop := ∀ i, c (x i) = i

theorem compatible_injective {x : I → A} {c : A → I}
    (h : Compatible x c) : Function.Injective x := by
  intro i j hij
  calc i = c (x i) := (h i).symm
       _ = c (x j) := congrArg c hij
       _ = j := h j

/-- Once colors on an injective tuple are fixed, all other colors are free. -/
def compatibleEquiv (x : I → A) (hx : Function.Injective x) :
    {c : A → I // Compatible x c} ≃ ({a : A // a ∉ Set.range x} → I) := by
  classical
  let extend (f : {a : A // a ∉ Set.range x} → I) : A → I :=
    fun a => if h : a ∈ Set.range x then Classical.choose h else f ⟨a,h⟩
  have extend_on (f : {a : A // a ∉ Set.range x} → I) (i : I) :
      extend f (x i) = i := by
    dsimp [extend]
    rw [dif_pos (Set.mem_range_self i)]
    exact hx (Classical.choose_spec (Set.mem_range_self i))
  refine {
    toFun := fun c a => c.val a.val
    invFun := fun f => ⟨extend f, extend_on f⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro c
    apply Subtype.ext
    funext a
    change extend (fun a => c.val a.val) a = c.val a
    by_cases h : a ∈ Set.range x
    · obtain ⟨i,rfl⟩ := h
      exact (extend_on (fun a => c.val a.val) i).trans (c.property i).symm
    · dsimp only [extend]
      rw [dif_neg h]
  · intro f
    funext a
    change extend f a.val = f a
    dsimp only [extend]
    rw [dif_neg a.property]

theorem card_compatible (x : I → A) (hx : Function.Injective x) :
    Fintype.card {c : A → I // Compatible x c} =
      Fintype.card I ^ (Fintype.card A - Fintype.card I) := by
  classical
  rw [Fintype.card_congr (compatibleEquiv x hx), Fintype.card_fun]
  congr 1
  change Fintype.card (↥(Set.range x)ᶜ) = _
  rw [Fintype.card_compl_set]
  congr 1
  exact Fintype.card_congr (Equiv.ofInjective x hx).symm

theorem card_compatible_of_not_injective (x : I → A) (hx : ¬Function.Injective x) :
    Fintype.card {c : A → I // Compatible x c} = 0 := by
  classical
  letI : IsEmpty {c : A → I // Compatible x c} :=
    ⟨fun c => hx (compatible_injective c.property)⟩
  exact Fintype.card_eq_zero

/-- Unnormalized finite coloring identity.  The size of the prime universe
occurs only in the common number of extensions of an injective tuple. -/
theorem sum_colored_products {R : Type*} [CommSemiring R] (a : I → A → R) :
    (∑ c : A → I, ∏ i, ∑ p : A, if c p = i then a i p else 0) =
      (Fintype.card I ^ (Fintype.card A - Fintype.card I) : ℕ) *
        ∑ x : I → A, if Function.Injective x then ∏ i, a i (x i) else 0 := by
  classical
  simp_rw [Fintype.prod_sum]
  rw [Finset.sum_comm]
  simp_rw [Fintype.prod_ite_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : (Finset.univ.filter (fun c : A → I => ∀ i, c (x i) = i)).card =
      Fintype.card {c : A → I // Compatible x c} := by
    symm
    apply Fintype.card_of_subtype
    intro c
    simp [Compatible]
  rw [hc]
  by_cases hx : Function.Injective x
  · rw [if_pos hx, card_compatible x hx]
  · rw [if_neg hx, card_compatible_of_not_injective x hx]
    simp

end PhysicalRepeatedPrimeSlots


set_option maxHeartbeats 2000000
namespace PhysicalRepeatedPrimeSlots
noncomputable section
open scoped Classical BigOperators

theorem sum_comp_le_total {I J : Type*} [Fintype I] [Fintype J]
    (f : J → I) (hf : Function.Injective f) (w : I → ℝ) (hw : ∀i,0≤w i) :
    (∑j,w (f j)) ≤ ∑i,w i := by
  classical
  calc
    _ = ∑i∈Finset.univ.image f,w i := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => hf h
    _ ≤ ∑i,w i := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun i _ _ => hw i)

theorem sum_family_energy {Row Color : Type*} [Fintype Color]
    (rows : Finset Row) (F : Color → Row → ℂ) (E : ℝ)
    (h : ∀ c, ∑ u ∈ rows, ‖F c u‖^2 ≤ E) :
    (∑ u ∈ rows, ‖∑ c, F c u‖^2) ≤ (Fintype.card Color : ℝ)^2*E := by
  have hp (u : Row) : ‖∑ c, F c u‖^2 ≤
      (Fintype.card Color : ℝ) * ∑ c, ‖F c u‖^2 := by
    apply ((sq_le_sq₀ (norm_nonneg _)
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr (norm_sum_le _ _)).trans
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun (_ : Color) => (1 : ℝ)) (fun c => ‖F c u‖)
  calc
    _ ≤ ∑ u ∈ rows, (Fintype.card Color : ℝ)*∑ c, ‖F c u‖^2 :=
      Finset.sum_le_sum (fun u _ => hp u)
    _ = (Fintype.card Color : ℝ)*∑ c, ∑ u ∈ rows, ‖F c u‖^2 := by
      rw [←Finset.mul_sum,Finset.sum_comm]
    _ ≤ (Fintype.card Color : ℝ)*∑ c : Color, E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => h c)) (Nat.cast_nonneg _)
    _ = _ := by simp [pow_two,mul_assoc]

/-- Coloring separates the injective part with a cost depending only on the
number of slots. The number of available primes cancels exactly. -/
theorem injective_coloring_energy {Row A I : Type*} [Fintype A] [Fintype I]
    [Nonempty I] (rows : Finset Row) (a : Row → I → A → ℂ) (D : Row → ℂ)
    (E : ℝ) (hE : 0 ≤ E)
    (h : ∀ c : A → I,
      (∑ u ∈ rows, ‖D u*(∏ i, ∑ p : A, if c p=i then a u i p else 0)‖^2) ≤ E) :
    (∑ u ∈ rows, ‖D u*(∑ x : I → A,
      if Function.Injective x then ∏ i, a u i (x i) else 0)‖^2) ≤
      (Fintype.card I : ℝ)^(2*Fintype.card I)*E := by
  classical
  by_cases hx : ∃ x : I → A, Function.Injective x
  · obtain ⟨x,hx⟩ := hx
    have hcard : Fintype.card I ≤ Fintype.card A := Fintype.card_le_of_injective x hx
    let c : ℕ := Fintype.card I^(Fintype.card A-Fintype.card I)
    have hc : 0 < (c : ℝ) := by
      exact_mod_cast Nat.pow_pos (Fintype.card_pos : 0 < Fintype.card I)
    let F (col : A → I) (u : Row) : ℂ :=
      D u*(∏ i, ∑ p : A, if col p=i then a u i p else 0)
    have he := sum_family_energy rows F E h
    have hid (u : Row) : (∑ col, F col u) = (c : ℂ)*
        (D u*(∑ x : I → A, if Function.Injective x then ∏ i, a u i (x i) else 0)) := by
      dsimp only [F]
      rw [←Finset.mul_sum,sum_colored_products]
      ring
    simp_rw [hid,norm_mul,Complex.norm_natCast,mul_pow] at he
    rw [←Finset.mul_sum,Fintype.card_fun] at he
    have hp : ((Fintype.card I^Fintype.card A : ℕ) : ℝ)^2 =
        (c : ℝ)^2*(Fintype.card I : ℝ)^(2*Fintype.card I) := by
      have heq : Fintype.card I^Fintype.card A = c*Fintype.card I^Fintype.card I := by
        dsimp [c]
        rw [←pow_add,Nat.sub_add_cancel hcard]
      rw [heq]
      simp only [Nat.cast_mul,Nat.cast_pow,mul_pow,←pow_mul,Nat.mul_comm]
      ring
    rw [hp,mul_assoc] at he
    simpa only [norm_mul,mul_pow] using
      (mul_le_mul_iff_right₀ (sq_pos_of_pos hc)).mp he
  · have hzero (u : Row) : (∑ x : I → A,
        if Function.Injective x then ∏ i, a u i (x i) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [if_neg (fun hi => hx ⟨x,hi⟩)]
    simp only [hzero,mul_zero,norm_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero]
    positivity

end
end PhysicalRepeatedPrimeSlots


set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Angular.PhysicalDetectorDirectInverse
noncomputable section
open scoped Classical BigOperators
open Set ActualEisensteinCubic
open ConcreteTraceCRT
open CommonMask NaturalRows
open CenteredMomentCommonMaskEnergy CenteredMomentSecondHeightFamily
open CanonicalRowCompletion
open InverseRows CubicEisenstein.AngularRawCoefficientGates
local notation "O" => HeckeFamily.O

/-- Exact conversion of an actual natural prime slot, with arbitrary
relative coefficient, into the coefficient-uniform marked inverse input. -/
theorem naturalSlot_eq_direct {η : AngularCharacter} {u : O} (F : NaturalRow η u)
    (L : Finset (Ideal O)) (β : Ideal O → ℂ) (P : ℝ) :
    naturalSlot F.character L β P = directPrimeSlot u L
      (fun I=>idealCoeff η I*idealRowHom (fixedBadMask^6) I*β I) P := by
  unfold naturalSlot directPrimeSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [F.ideal,idealRowHom_argument_mul]
  ring

theorem natural_direct_coeff_bound (η : AngularCharacter) (β : Ideal O → ℂ)
    (I : Ideal O) (B : ℝ) (hβ : ‖β I‖≤B) :
    ‖idealCoeff η I*idealRowHom (fixedBadMask^6) I*β I‖≤B := by
  rw [norm_mul,norm_mul]
  have hbase : ‖idealCoeff η I‖*‖idealRowHom (fixedBadMask^6) I‖≤1 := by
    exact (mul_le_mul_of_nonneg_right (idealCoeff_norm_le_one η I) (norm_nonneg _)).trans
      (by simpa only [one_mul] using idealRowHom_norm (fixedBadMask^6) I)
  exact (mul_le_of_le_one_left (norm_nonneg _) hbase).trans hβ

theorem directPrimeSlot_const_mul (u : O) (L : Finset (Ideal O))
    (β : Ideal O → ℂ) (P : ℝ) (c : ℂ) :
    directPrimeSlot u L (fun I=>c*β I) P = c*directPrimeSlot u L β P := by
  unfold directPrimeSlot
  simp only [mul_assoc,←Finset.mul_sum]
  ring

theorem directPrimeSlot_div (u : O) (L : Finset (Ideal O))
    (β : Ideal O → ℂ) (P B : ℝ) (hB : B≠0) :
    directPrimeSlot u L β P = (B : ℂ)*directPrimeSlot u L (fun I=>β I/(B : ℂ)) P := by
  rw [←directPrimeSlot_const_mul]
  congr 2
  funext I
  rw [mul_comm (B : ℂ),div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hB)]

theorem direct_slot_energy_scale {ι Row : Type*} [Fintype ι]
    (rows : Finset Row) (u : Row → O) (D : Row → ℂ)
    (L : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (P : ι → ℝ) (B : ℝ) (hB : 0<B) :
    (∑v∈rows,‖D v*(∏i,directPrimeSlot (u v) (L i) (β i) (P i))‖^2) =
      B^(2*Fintype.card ι) *
        ∑v∈rows,‖D v*(∏i,directPrimeSlot (u v) (L i) (fun I=>β i I/(B : ℂ)) (P i))‖^2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have hs : (∏i,directPrimeSlot (u v) (L i) (β i) (P i)) =
      (B : ℂ)^Fintype.card ι *
        (∏i,directPrimeSlot (u v) (L i) (fun I=>β i I/(B : ℂ)) (P i)) := by
    calc
      _ = ∏i,(B : ℂ)*directPrimeSlot (u v) (L i) (fun I=>β i I/(B : ℂ)) (P i) :=
        Finset.prod_congr rfl (fun i _=>directPrimeSlot_div _ _ _ _ B hB.ne')
      _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  rw [hs]
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hB,mul_pow]
  rw [←pow_mul]
  ring

/-- Uniform coefficient-size version of the actual marked inverse moment.
The fixed cost is independent of the selected prime slots. -/
theorem bounded_inverse_marked_energy (angularOrder:ℕ) (εm B : ℝ) (hεm : 0<εm) (hB : 1≤B) (K : ℕ) :
    ∃ degree : ℕ, ∀ data : RowData, data.η.k=(angularOrder:ℤ) → ∃ C U₀ : ℝ, 0<C ∧ 1<U₀ ∧
      ∀ U : ℝ, U₀≤U → ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι≤K →
      ∀ (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ),
        (∀i,0≤ell i) → (∀i,∀P∈L i,Prime P) →
        (((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint L) →
        (∀i,∀P∈L i,((P.absNorm : ℝ)/U^(ell i))∈Icc (1 : ℝ) 2) →
        (∀i,∀P∈L i,‖β i P‖≤B) →
        (∀i,((deletedBase data).modulus.absNorm : ℝ)<U^(ell i)) →
      ∀r : ℝ, 0≤r → r+2*(∑i,ell i)<1 → 2*r+8*(∑i,ell i)<3 →
      ∀rows : Finset NonzeroElement, (∀u∈rows,‖eisEmbedding u.val‖^2≤U) →
      ∀tstar : ℝ, ∀reverse : Bool, ∀n : ℕ,n≤2 → ∀σ∈Icc (0 : ℝ) 1,
      ∀height t : ℝ, 0≤height → t∈Icc (-height) height →
      (∑u∈rows,‖polynomial (data.character u) true
        ((HeckeDetectorRowwisePolynomial.logProfile^[n])
          (HeckeDetectorCoefficientTransfer.orientedProfile reverse
            (HeckeDetectorInverseFiberCount.inverseTest U tstar r))) (U^r) σ t *
          (∏i,directPrimeSlot u.val (L i) (β i) (U^(ell i)))‖^2) ≤
        (C*(1+height)^degree)*U^(1+εm) := by
  obtain ⟨degree,henergy⟩ := actual_inverse_marked_energy angularOrder εm hεm K
  refine ⟨degree,?_⟩
  intro data hk
  obtain ⟨C,U₀,hC,hU₀,henergy⟩ := henergy data hk
  have hBp : 0<B := zero_lt_one.trans_le hB
  refine ⟨B^(2*K)*C,U₀,mul_pos (pow_pos hBp _) hC,hU₀,?_⟩
  intro U hU ι inst dec hK L ell β hell hp hdis hratio hβ hlarge r hr hfirst hsecond rows hrows
    tstar reverse n hn σ hσ height t hh ht
  have hb (i : ι) (P : Ideal O) (hP : P∈L i) : ‖β i P/(B : ℂ)‖≤1 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hBp]
    exact (div_le_one hBp).mpr (hβ i P hP)
  have he := henergy U hU hK L ell (fun i P=>β i P/(B : ℂ)) hell hp hdis hratio hb
    hlarge r hr hfirst hsecond rows hrows tstar reverse n hn σ hσ height t hh ht
  rw [direct_slot_energy_scale rows (fun u=>u.val) _ L β (fun i=>U^(ell i)) B hBp]
  apply (mul_le_mul_of_nonneg_left he (pow_nonneg hBp.le _)).trans
  calc
    _ ≤ B^(2*K)*((C*(1+height)^degree)*U^(1+εm)) := by
      apply mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hB (Nat.mul_le_mul_left 2 hK))
      have hUp : 0<U := (zero_lt_one.trans hU₀).trans_le hU
      positivity
    _ = _ := by ring


end
end OAI.SevenEighths.Angular.PhysicalDetectorDirectInverse


set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Angular.PhysicalDetectorDirectInverse
noncomputable section
open scoped Classical BigOperators

variable {I A R : Type*} [Fintype I] [Fintype A] [CommSemiring R]

instance finiteSetoid : Fintype (Setoid I) :=
  Fintype.ofInjective (fun r : Setoid I=>r.r) (fun _ _ h=>Setoid.eq_iff_rel_eq.mpr h)

/-- Tuples with a prescribed equality pattern are injective assignments
to the quotient blocks of that pattern. -/
def kernelTupleEquiv (r : Setoid I) :
    {p : Quotient r→A // Function.Injective p} ≃ {x : I→A // Setoid.ker x=r} where
  toFun p := ⟨fun i=>p.val (Quotient.mk r i),by
    apply Setoid.ext
    intro i j
    change (p.val (Quotient.mk r i)=p.val (Quotient.mk r j))↔r i j
    exact ⟨fun h=>Quotient.exact (p.property h),fun h=>congrArg p.val (Quotient.sound h)⟩⟩
  invFun x := ⟨Quotient.lift x.val (fun i j hij=>by
    have hh : Setoid.ker x.val i j := by rw [x.property];exact hij
    exact hh),by
    intro q q' h
    induction q using Quotient.inductionOn with | h i =>
      induction q' using Quotient.inductionOn with | h j =>
        apply Quotient.sound
        change x.val i=x.val j at h
        have hh : Setoid.ker x.val i j := h
        rwa [x.property] at hh⟩
  left_inv p := by
    apply Subtype.ext
    funext q
    induction q using Quotient.inductionOn
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

/-- Exact decomposition of the full slot product by equality pattern,
with the coefficient in each quotient block kept as a product. -/
theorem product_sum_kernel (a : I→A→R) :
    (∏i,∑p,a i p) = ∑r : Setoid I,
      ∑p : {p : Quotient r→A // Function.Injective p},
        ∏i,a i (p.val (Quotient.mk r i)) := by
  rw [Fintype.prod_sum]
  have hf := Finset.sum_fiberwise (Finset.univ : Finset (I→A))
    (fun x=>Setoid.ker x) (fun x=>∏i,a i (x i))
  rw [←hf]
  apply Finset.sum_congr (by ext;simp)
  intro r hr
  rw [Finset.sum_subtype (p:=fun x : I→A=>Setoid.ker x=r) _ (by simp) (fun x : I→A=>∏i,a i (x i))]
  exact ((kernelTupleEquiv r).sum_comp (fun x : {x : I→A // Setoid.ker x=r}=>∏i,a i (x.val i))).symm

def collisionBlock (r : Setoid I) (q : Quotient r) : Finset I :=
  Finset.univ.filter (fun i=>Quotient.mk r i=q)

theorem collisionBlock_nonempty (r : Setoid I) (q : Quotient r) :
    (collisionBlock r q).Nonempty := by
  obtain ⟨i,rfl⟩ := Quotient.exists_rep q
  exact ⟨i,by simp [collisionBlock]⟩

theorem product_over_collision_blocks (r : Setoid I) (a : I→A→R) (p : Quotient r→A) :
    (∏i,a i (p (Quotient.mk r i))) =
      ∏q : Quotient r,∏i∈collisionBlock r q,a i (p q) := by
  rw [←Fintype.prod_fiberwise (Quotient.mk r) (fun i=>a i (p (Quotient.mk r i)))]
  apply Finset.prod_congr (by ext;simp)
  intro q hq
  rw [Finset.prod_subtype (F:=inferInstance) (p:=fun i : I=>Quotient.mk r i=q)
    (collisionBlock r q) (by intro i;simp [collisionBlock])]
  apply Finset.prod_congr (by ext;simp)
  intro i hi
  rw [i.property]

def injectiveTuplePolynomial (a : I→A→R) : R :=
  ∑x : I→A,if Function.Injective x then ∏i,a i (x i) else 0

theorem product_sum_collision_blocks (a : I→A→R) :
    (∏i,∑p,a i p) = ∑r : Setoid I,
      injectiveTuplePolynomial (fun q : Quotient r=>fun p=>∏i∈collisionBlock r q,a i p) := by
  rw [product_sum_kernel]
  apply Finset.sum_congr (by ext;simp)
  intro r hr
  unfold injectiveTuplePolynomial
  rw [←Finset.sum_filter]
  rw [Finset.sum_subtype (F:=inferInstance) (p:=fun x : Quotient r→A=>Function.Injective x) _ (by simp)]
  apply Finset.sum_congr (by ext;simp)
  intro p hp
  exact product_over_collision_blocks r a p.val

variable (P : I→Prop)

def joinAssignments (s : {i // P i}→A) (t : {i // ¬P i}→A) (i : I) : A :=
  if h : P i then s ⟨i,h⟩ else t ⟨i,h⟩

theorem injective_joinAssignments (s : {i // P i}→A) (t : {i // ¬P i}→A) :
    Function.Injective (joinAssignments P s t) ↔
      Function.Injective s ∧ Function.Injective t ∧ ∀i j,s i≠t j := by
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro i j he
      apply Subtype.ext
      apply h
      simpa [joinAssignments,i.property,j.property] using he
    · intro i j he
      apply Subtype.ext
      apply h
      simpa [joinAssignments,i.property,j.property] using he
    · intro i j he
      have hh : i.val=j.val := h (by simpa [joinAssignments,i.property,j.property] using he)
      exact j.property (hh ▸ i.property)
  · rintro ⟨hs,ht,hcross⟩ i j he
    by_cases hi : P i <;> by_cases hj : P j
    · have hh := hs (show s ⟨i,hi⟩=s ⟨j,hj⟩ by simpa [joinAssignments,hi,hj] using he)
      exact congrArg Subtype.val hh
    · exact False.elim (hcross ⟨i,hi⟩ ⟨j,hj⟩ (by simpa [joinAssignments,hi,hj] using he))
    · exact False.elim (hcross ⟨j,hj⟩ ⟨i,hi⟩ (by simpa [joinAssignments,hi,hj] using he.symm))
    · have hh := ht (show t ⟨i,hi⟩=t ⟨j,hj⟩ by simpa [joinAssignments,hi,hj] using he)
      exact congrArg Subtype.val hh

def assignmentSplit : (I→A) ≃ ({i // P i}→A)×({i // ¬P i}→A) where
  toFun x := (fun i=>x i.val,fun i=>x i.val)
  invFun st := joinAssignments P st.1 st.2
  left_inv x := by funext i;simp [joinAssignments]
  right_inv st := by ext i <;> simp [joinAssignments,i.property]

theorem joinAssignments_product (a : I→A→R) (s : {i // P i}→A) (t : {i // ¬P i}→A) :
    (∏i,a i (joinAssignments P s t i)) = (∏i : {i // P i},a i.val (s i))*
      (∏j : {i // ¬P i},a j.val (t j)) := by
  rw [←Fintype.prod_subtype_mul_prod_subtype P]
  apply congrArg₂ (·*·)
  · apply Finset.prod_congr (by ext;simp)
    intro i hi
    simp [joinAssignments,i.property]
  · apply Finset.prod_congr (by ext;simp)
    intro i hi
    simp [joinAssignments,i.property]

theorem injectiveTuplePolynomial_split (a : I→A→R) :
    injectiveTuplePolynomial a =
      ∑t : {i // ¬P i}→A,if Function.Injective t then
        (∏j : {i // ¬P i},a j.val (t j))*
          injectiveTuplePolynomial (fun i : {i // P i}=>fun p=>
            if ∀j : {i // ¬P i},p≠t j then a i.val p else 0)
      else 0 := by
  unfold injectiveTuplePolynomial
  rw [←(assignmentSplit (A:=A) P).symm.sum_comp]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr (by ext;simp)
  intro t ht
  by_cases hti : Function.Injective t
  · rw [if_pos hti,Finset.mul_sum]
    apply Finset.sum_congr (by ext;simp)
    intro s hs
    change (if Function.Injective (joinAssignments P s t) then ∏i,a i (joinAssignments P s t i) else 0)=_
    simp only [joinAssignments_product,injective_joinAssignments]
    by_cases hsi : Function.Injective s
    · rw [if_pos hsi,Fintype.prod_ite_zero]
      by_cases hc : ∀i : {i // P i},∀j : {i // ¬P i},s i≠t j
      · simp [hsi,hti,hc,mul_comm]
      · simp only [hsi,hti,hc,and_true,true_and,ite_false,mul_zero]
    · simp only [hsi,false_and,ite_false,mul_zero]
  · rw [if_neg hti]
    apply Finset.sum_eq_zero
    intro s hs
    change (if Function.Injective (joinAssignments P s t) then _ else 0)=0
    simp [injective_joinAssignments,hti]

end
end OAI.SevenEighths.Angular.PhysicalDetectorDirectInverse


set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Angular.PhysicalDetectorDirectInverse
noncomputable section
open scoped Classical BigOperators
open CanonicalRowCompletion
local notation "O" => HeckeFamily.O

/-- Any collision block of at least two slots has bounded absolute mass.
Only two square-summable coefficient vectors are needed; all remaining
factors use their uniform pointwise bound. -/
theorem collision_block_mass {I A : Type*} [Fintype A]
    (J : Finset I) (v : I→A→ℝ) (B L : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hJ : 2≤J.card) (hv0 : ∀i∈J,∀p,0≤v i p)
    (hv : ∀i∈J,∀p,v i p≤B) (henergy : ∀i∈J,(∑p,(v i p)^2)≤L*B^2) :
    (∑p,∏i∈J,v i p)≤L*B^J.card := by
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp (by omega : 1<J.card)
  have hj' : j∈J.erase i := Finset.mem_erase.mpr ⟨hij.symm,hj⟩
  let T := (J.erase i).erase j
  have hTcard : T.card+2=J.card := by
    dsimp [T]
    rw [Finset.card_erase_of_mem hj',Finset.card_erase_of_mem hi]
    omega
  have hprod (p : A) : (∏k∈J,v k p)=v i p*v j p*(∏k∈T,v k p) := by
    rw [←Finset.mul_prod_erase J (fun k=>v k p) hi,
      ←Finset.mul_prod_erase (J.erase i) (fun k=>v k p) hj']
    dsimp [T]
    ring
  have hrem (p : A) : (∏k∈T,v k p)≤B^T.card := by
    calc
      _≤∏k∈T,B := Finset.prod_le_prod₀
        (fun k hk=>hv0 k (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk)) p)
        (fun k hk=>hv k (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk)) p)
      _=_ := Finset.prod_const _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset A) (v i) (v j)
  have henergyprod : (∑p,(v i p)^2)*(∑p,(v j p)^2)≤(L*B^2)^2 := by
    rw [pow_two]
    exact mul_le_mul (henergy i hi) (henergy j hj)
      (Finset.sum_nonneg (fun _ _=>sq_nonneg _)) (mul_nonneg hL (sq_nonneg _))
  have hpair : (∑p,v i p*v j p)≤L*B^2 := by
    have hh := hcs.trans henergyprod
    have hn : 0≤L*B^2 := mul_nonneg hL (sq_nonneg _)
    nlinarith
  calc
    _ = ∑p,v i p*v j p*(∏k∈T,v k p) := Finset.sum_congr rfl (fun p _=>hprod p)
    _ ≤ ∑p,v i p*v j p*B^T.card := Finset.sum_le_sum (fun p _=>
      mul_le_mul_of_nonneg_left (hrem p) (mul_nonneg (hv0 i hi p) (hv0 j hj p)))
    _ = (∑p,v i p*v j p)*B^T.card := by rw [Finset.sum_mul]
    _ ≤ (L*B^2)*B^T.card := mul_le_mul_of_nonneg_right hpair (pow_nonneg hB _)
    _ = L*B^J.card := by rw [mul_assoc,←pow_add,Nat.add_comm 2,hTcard]

def normalizedPrimeCoeff (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ)
    (I : Ideal O) : ℂ := if I∈pool then (Real.sqrt P:ℂ)⁻¹*β I else 0

theorem normalizedPrimeCoeff_bound (pool : Finset (Ideal O)) (β : Ideal O→ℂ)
    (P B : ℝ) (hP : 1≤P) (hB : 0≤B) (hβ : ∀I∈pool,‖β I‖≤B) (I : Ideal O) :
    ‖normalizedPrimeCoeff pool β P I‖≤B := by
  unfold normalizedPrimeCoeff
  split_ifs with hI
  · rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    have hs : 1≤Real.sqrt P := (Real.le_sqrt (by norm_num) (zero_le_one.trans hP)).mpr (by simpa using hP)
    exact (mul_le_mul_of_nonneg_left (hβ I hI) (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans
      (mul_le_of_le_one_left hB (inv_le_one_of_one_le₀ hs))
  · simpa using hB

/-- Actual normalized prime coefficients have uniformly bounded square
mass, without any separation condition between different slots. -/
theorem normalizedPrimeCoeff_energy (atoms pool : Finset (Ideal O)) (β : Ideal O→ℂ)
    (P B : ℝ) (hP : 1≤P) (hB : 0≤B) (hβ : ∀I∈pool,‖β I‖≤B)
    (hp : ∀I∈pool,I≠0) (hN : ∀I∈pool,(I.absNorm:ℝ)≤2*P) :
    (∑I∈atoms,‖normalizedPrimeCoeff pool β P I‖^2)≤256*B^2 := by
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hs : 0<Real.sqrt P := Real.sqrt_pos.mpr hPp
  have hc : (pool.card:ℝ)≤256*P := by
    have hh := CenteredMomentSecondDiagonal.divisible_ideal_card pool 1 one_ne_zero hp
      (fun I _=>one_dvd I) (2*P) (by positivity) hN
    simp only [map_one,Nat.cast_one,div_one] at hh
    nlinarith
  have hterm (I : Ideal O) (hI : I∈pool) :
      ‖normalizedPrimeCoeff pool β P I‖^2≤B^2/P := by
    rw [normalizedPrimeCoeff,if_pos hI,norm_mul,norm_inv,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hs.le,mul_pow,inv_pow,Real.sq_sqrt hPp.le]
    rw [div_eq_mul_inv,mul_comm (B^2)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hβ I hI) 2) (inv_nonneg.mpr hPp.le)
  have he : (∑I∈atoms,‖normalizedPrimeCoeff pool β P I‖^2)=
      ∑I∈atoms∩pool,‖normalizedPrimeCoeff pool β P I‖^2 := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro I hI hn
    have hnot : I∉pool := fun hp=>hn (Finset.mem_inter.mpr ⟨hI,hp⟩)
    simp [normalizedPrimeCoeff,hnot]
  rw [he]
  calc
    _≤∑I∈pool,‖normalizedPrimeCoeff pool β P I‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun _ _ _=>sq_nonneg _)
    _≤∑I∈pool,B^2/P := Finset.sum_le_sum hterm
    _=(pool.card:ℝ)*(B^2/P) := by simp
    _≤(256*P)*(B^2/P) := mul_le_mul_of_nonneg_right hc (by positivity)
    _=256*B^2 := by field_simp

end
end OAI.SevenEighths.Angular.PhysicalDetectorDirectInverse


set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Angular.PhysicalDetectorDirectInverse
noncomputable section
open scoped Classical BigOperators

/-- Weighted finite Cauchy-Schwarz. The number of assignments does not
enter the bound; only the sum of their scalar masses does. -/
theorem weighted_family_energy {Row T : Type*} [Fintype T]
    (rows : Finset Row) (F G : T→Row→ℂ) (w : T→ℝ) (E : ℝ)
    (hw : ∀t,0≤w t) (hFG : ∀t,∀u∈rows,‖F t u‖≤w t*‖G t u‖)
    (hG : ∀t,(∑u∈rows,‖G t u‖^2)≤E) :
    (∑u∈rows,‖∑t,F t u‖^2)≤(∑t,w t)^2*E := by
  have hp (u : Row) (hu : u∈rows) : ‖∑t,F t u‖^2≤
      (∑t,w t)*(∑t,w t*‖G t u‖^2) := by
    have hn : ‖∑t,F t u‖≤∑t,w t*‖G t u‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun t _=>hFG t u hu))
    apply ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg
      (fun t _=>mul_nonneg (hw t) (norm_nonneg _)))).mpr hn).trans
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun t _=>hw t) (fun t _=>mul_nonneg (hw t) (sq_nonneg _))
    intro t ht
    exact le_of_eq (by ring)
  calc
    _≤∑u∈rows,(∑t,w t)*(∑t,w t*‖G t u‖^2) := Finset.sum_le_sum hp
    _=(∑t,w t)*(∑t,w t*(∑u∈rows,‖G t u‖^2)) := by
      rw [←Finset.mul_sum,Finset.sum_comm]
      simp_rw [←Finset.mul_sum]
    _≤(∑t,w t)*(∑t,w t*E) := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun t _=>mul_le_mul_of_nonneg_left (hG t) (hw t)))
      (Finset.sum_nonneg (fun t _=>hw t))
    _=_ := by rw [←Finset.sum_mul];ring

variable {I A : Type*} [Fintype I] [Fintype A]

def singletonBlock (r : Setoid I) (q : Quotient r) : Prop :=
  (collisionBlock r q).card=1

def singletonRepresentative (r : Setoid I) (q : {q // singletonBlock r q}) : I :=
  (Finset.card_eq_one.mp q.property).choose

theorem singletonBlock_eq (r : Setoid I) (q : {q // singletonBlock r q}) :
    collisionBlock r q.val={singletonRepresentative r q} :=
  (Finset.card_eq_one.mp q.property).choose_spec

theorem singletonRepresentative_class (r : Setoid I) (q : {q // singletonBlock r q}) :
    Quotient.mk r (singletonRepresentative r q)=q.val := by
  have h : singletonRepresentative r q∈collisionBlock r q.val := by rw [singletonBlock_eq];simp
  simpa [collisionBlock] using h

theorem singletonRepresentative_injective (r : Setoid I) :
    Function.Injective (singletonRepresentative r) := by
  intro q q' h
  apply Subtype.ext
  rw [←singletonRepresentative_class r q,←singletonRepresentative_class r q',h]

theorem collisionBlock_card_two (r : Setoid I) (q : {q // ¬singletonBlock r q}) :
    2≤(collisionBlock r q.val).card := by
  have hp := (collisionBlock_nonempty r q.val).card_pos
  have hn := q.property
  unfold singletonBlock at hn
  omega

theorem quotient_card_le (r : Setoid I) : Fintype.card (Quotient r)≤Fintype.card I :=
  Fintype.card_le_of_surjective (Quotient.mk r) Quotient.mk_surjective

theorem singleton_card_le (r : Setoid I) :
    Fintype.card {q // singletonBlock r q}≤Fintype.card I :=
  Fintype.card_le_of_injective _ (singletonRepresentative_injective r)

theorem setoid_card_le (K : ℕ) (hK : Fintype.card I≤K) :
    Fintype.card (Setoid I)≤2^(K*K) := by
  have h := Fintype.card_le_of_injective (fun r : Setoid I=>r.r)
    (fun _ _ hh=>Setoid.eq_iff_rel_eq.mpr hh)
  have heq : Fintype.card (I→I→Prop)=2^(Fintype.card I*Fintype.card I) := by
    simp [Fintype.card_fun,pow_mul]
  rw [heq] at h
  exact h.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_self_le_mul_self hK))

/-- Uniform total mass of all collision assignments for a fixed equality
pattern. Singleton blocks retain the actual row phase. -/
theorem collision_assignments_mass (r : Setoid I) (v : I→A→ℝ)
    (B L : ℝ) (hB : 1≤B) (hL : 1≤L)
    (hv0 : ∀i p,0≤v i p) (hv : ∀i p,v i p≤B)
    (he : ∀i,(∑p,(v i p)^2)≤L*B^2) (K : ℕ) (hK : Fintype.card I≤K) :
    (∑t : {q // ¬singletonBlock r q}→A,
      ∏q : {q // ¬singletonBlock r q},∏i∈collisionBlock r q.val,v i (t q))≤
        (L*B^K)^K := by
  rw [←Fintype.prod_sum (fun q : {q // ¬singletonBlock r q}=>fun p : A=>
    ∏i∈collisionBlock r q.val,v i p)]
  have hbase : 1≤L*B^K := one_le_mul_of_one_le_of_one_le hL (one_le_pow₀ hB)
  calc
    _≤∏q : {q // ¬singletonBlock r q},L*B^K := by
      apply Finset.prod_le_prod₀
      · intro q hq
        exact Finset.sum_nonneg (fun p _=>Finset.prod_nonneg (fun i _=>hv0 i p))
      · intro q hq
        apply (collision_block_mass (collisionBlock r q.val) v B L
          (zero_le_one.trans hB) (zero_le_one.trans hL) (collisionBlock_card_two r q)
          (fun i _=>hv0 i) (fun i _=>hv i) (fun i _=>he i)).trans
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB
          ((Finset.card_le_univ _).trans hK)) (zero_le_one.trans hL)
    _=(L*B^K)^Fintype.card {q // ¬singletonBlock r q} := by simp
    _≤(L*B^K)^K := pow_le_pow_right₀ hbase
      ((Fintype.card_subtype_le _).trans ((quotient_card_le r).trans hK))

/-- Removing collisions reduces the complete product moment to the
injective singleton moments. Every cost depends only on the slot count. -/
theorem product_energy_of_singletons {Row : Type*}
    (rows : Finset Row) (a : Row→I→A→ℂ) (v : I→A→ℝ) (D : Row→ℂ)
    (B L E : ℝ) (hB : 1≤B) (hL : 1≤L) (hE : 0≤E)
    (hv0 : ∀i p,0≤v i p) (hv : ∀i p,v i p≤B)
    (he : ∀i,(∑p,(v i p)^2)≤L*B^2)
    (ha : ∀u∈rows,∀i p,‖a u i p‖≤v i p)
    (K : ℕ) (hK : Fintype.card I≤K)
    (hsingle : ∀r : Setoid I,∀t : {q // ¬singletonBlock r q}→A,
      (∑u∈rows,‖D u*injectiveTuplePolynomial
        (fun q : {q // singletonBlock r q}=>fun p=>
          if ∀j : {q // ¬singletonBlock r q},p≠t j then
            a u (singletonRepresentative r q) p else 0)‖^2)≤E) :
    (∑u∈rows,‖D u*(∏i,∑p,a u i p)‖^2)≤
      ((2:ℝ)^(K*K)*(L*B^K)^K)^2*E := by
  let M : ℝ := (L*B^K)^K
  have hM : 0≤ M := by dsimp [M];positivity
  have hr (r : Setoid I) :
      (∑u∈rows,‖D u*injectiveTuplePolynomial
        (fun q : Quotient r=>fun p=>∏i∈collisionBlock r q,a u i p)‖^2)≤ M^2*E := by
    let G (t : {q // ¬singletonBlock r q}→A) (u : Row) : ℂ :=
      D u*injectiveTuplePolynomial
        (fun q : {q // singletonBlock r q}=>fun p=>
          if ∀j : {q // ¬singletonBlock r q},p≠t j then
            a u (singletonRepresentative r q) p else 0)
    let F (t : {q // ¬singletonBlock r q}→A) (u : Row) : ℂ :=
      if Function.Injective t then
        (∏q : {q // ¬singletonBlock r q},∏i∈collisionBlock r q.val,a u i (t q))*G t u
      else 0
    let mass (t : {q // ¬singletonBlock r q}→A) : ℝ :=
      ∏q : {q // ¬singletonBlock r q},∏i∈collisionBlock r q.val,v i (t q)
    have hm0 (t) : 0≤ mass t := Finset.prod_nonneg
      (fun q _=>Finset.prod_nonneg (fun i _=>hv0 i (t q)))
    have hFG (t) (u) (hu : u∈rows) : ‖F t u‖≤ mass t*‖G t u‖ := by
      dsimp only [F]
      split_ifs
      · rw [norm_mul]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simp only [norm_prod]
        exact Finset.prod_le_prod₀ (fun q _=>Finset.prod_nonneg (fun i _=>norm_nonneg _))
          (fun q _=>Finset.prod_le_prod₀ (fun i _=>norm_nonneg _) (fun i _=>ha u hu i (t q)))
      · simpa using mul_nonneg (hm0 t) (norm_nonneg (G t u))
    have hh := weighted_family_energy rows F G mass E hm0 hFG (hsingle r)
    have hmass : (∑t,mass t)≤ M := collision_assignments_mass r v B L hB hL hv0 hv he K hK
    have hbound : (∑u∈rows,‖∑t,F t u‖^2)≤ M^2*E := hh.trans
      (mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (Finset.sum_nonneg (fun t _=>hm0 t)) hM).mpr hmass) hE)
    convert hbound using 1
    apply Finset.sum_congr rfl
    intro u hu
    congr 2
    rw [injectiveTuplePolynomial_split (singletonBlock r),Finset.mul_sum]
    apply Finset.sum_congr (by ext;simp)
    intro t ht
    dsimp only [F,G]
    have hs : (fun q : {q // singletonBlock r q}=>fun p : A=>
        if ∀j : {q // ¬singletonBlock r q},p≠t j then
          (∏i∈collisionBlock r q.val,a u i p) else 0) =
      (fun q : {q // singletonBlock r q}=>fun p : A=>
        if ∀j : {q // ¬singletonBlock r q},p≠t j then
          a u (singletonRepresentative r q) p else 0) := by
      funext q p
      rw [singletonBlock_eq]
      simp
    rw [hs]
    split_ifs <;> ring
  have hh := PhysicalRepeatedPrimeSlots.sum_family_energy rows
    (fun r : Setoid I=>fun u=>D u*injectiveTuplePolynomial
      (fun q : Quotient r=>fun p=>∏i∈collisionBlock r q,a u i p)) (M^2*E) hr
  have hcard : (Fintype.card (Setoid I):ℝ)≤(2:ℝ)^(K*K) := by
    exact_mod_cast setoid_card_le (I:=I) K hK
  have hbound := hh.trans (mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mpr hcard) (mul_nonneg (sq_nonneg M) hE))
  have heq (u : Row) : (∑r : Setoid I,D u*injectiveTuplePolynomial
      (fun q : Quotient r=>fun p=>∏i∈collisionBlock r q,a u i p)) =D u*(∏i,∑p,a u i p) := by
    rw [←Finset.mul_sum,←product_sum_collision_blocks]
  simp_rw [heq] at hbound
  convert hbound using 1
  dsimp [M]
  ring

end
end OAI.SevenEighths.Angular.PhysicalDetectorDirectInverse


set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Angular.PhysicalDetectorDirectInverse
noncomputable section
open scoped Classical BigOperators
open CanonicalRowCompletion
open InverseRows CubicEisenstein.AngularRawCoefficientGates
local notation "O" => HeckeFamily.O

theorem directPrimeSlot_sum_atoms (u : O) (pool atoms : Finset (Ideal O))
    (β : Ideal O→ℂ) (P : ℝ) (hpool : pool⊆atoms) :
    directPrimeSlot u pool β P =
      ∑p : atoms,idealRowHom u p.val*normalizedPrimeCoeff pool β P p.val := by
  rw [←Finset.sum_subtype (F:=inferInstance) (p:=fun p : Ideal O=>p∈atoms) atoms (by simp)
    (fun p=>idealRowHom u p*normalizedPrimeCoeff pool β P p)]
  unfold directPrimeSlot normalizedPrimeCoeff
  rw [Finset.mul_sum]
  calc
    _ = ∑p∈pool,idealRowHom u p*(if p∈pool then (Real.sqrt P:ℂ)⁻¹*β p else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      simp only [hp,ite_true]
      ring
    _ = ∑p∈atoms,idealRowHom u p*(if p∈pool then (Real.sqrt P:ℂ)⁻¹*β p else 0) := by
      apply Finset.sum_subset hpool
      intro p hp hn
      simp [hn]

theorem normalizedPrimeCoeff_filter (pool : Finset (Ideal O)) (β : Ideal O→ℂ)
    (P : ℝ) (keep : Ideal O→Prop) (p : Ideal O) :
    normalizedPrimeCoeff (pool.filter keep) β P p =
      if keep p then normalizedPrimeCoeff pool β P p else 0 := by
  simp only [normalizedPrimeCoeff,Finset.mem_filter]
  split_ifs <;> simp_all

end
end OAI.SevenEighths.Angular.PhysicalDetectorDirectInverse


set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace OAI.SevenEighths.Angular.PhysicalDetectorDirectInverse
noncomputable section
open scoped Classical BigOperators
open CanonicalRowCompletion
open InverseRows CubicEisenstein.AngularRawCoefficientGates
local notation "O" => HeckeFamily.O

def overlapCost (B : ℝ) (K : ℕ) : ℝ :=
  ((2:ℝ)^(K*K)*(256*B^K)^K)^2*(max 1 (K:ℝ))^(2*K)

theorem overlapCost_pos (B : ℝ) (hB : 1≤B) (K : ℕ) : 0<overlapCost B K := by
  unfold overlapCost
  have : 0<B := zero_lt_one.trans_le hB
  positivity

/-- A separated-pool estimate implies the same moment for arbitrary
pool overlaps. The coefficient square mass controls all repeated primes. -/
theorem overlapping_direct_energy {I Row : Type} [Fintype I] [DecidableEq I]
    (rows : Finset Row) (u : Row→O) (D : Row→ℂ)
    (L : I→Finset (Ideal O)) (β : I→Ideal O→ℂ) (P : I→ℝ)
    (B E : ℝ) (hB : 1≤B) (hE : 0≤E) (K : ℕ) (hK : Fintype.card I≤K)
    (hP : ∀i,1≤P i) (hβ : ∀i,∀p∈L i,‖β i p‖≤B)
    (hp : ∀i,∀p∈L i,p≠0) (hN : ∀i,∀p∈L i,(p.absNorm:ℝ)≤2*P i)
    (hsep : ∀{J : Type} [Fintype J] [DecidableEq J],
      ∀f : J→I,Function.Injective f →∀L' : J→Finset (Ideal O),
      (∀j,L' j⊆L (f j)) →
      (((Finset.univ : Finset J) : Set J).PairwiseDisjoint L') →
      (∑v∈rows,‖D v*(∏j,directPrimeSlot (u v) (L' j) (β (f j)) (P (f j)))‖^2)≤E) :
    (∑v∈rows,‖D v*(∏i,directPrimeSlot (u v) (L i) (β i) (P i))‖^2)≤overlapCost B K*E := by
  classical
  let atoms : Finset (Ideal O) := Finset.univ.biUnion L
  have hLa (i : I) : L i⊆atoms := by
    intro p hp
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hp⟩
  let a : Row→I→atoms→ℂ := fun v i p=>idealRowHom (u v) p.val*normalizedPrimeCoeff (L i) (β i) (P i) p.val
  let coeffNorm : I→atoms→ℝ := fun i p=>‖normalizedPrimeCoeff (L i) (β i) (P i) p.val‖
  let cK : ℝ := (max 1 (K:ℝ))^(2*K)
  have hcK : 1≤cK := one_le_pow₀ (le_max_left _ _)
  have ha (v : Row) (hv : v∈rows) (i : I) (p : atoms) : ‖a v i p‖≤coeffNorm i p := by
    dsimp [a,coeffNorm]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (idealRowHom_norm _ _)
  have hv (i : I) (p : atoms) : coeffNorm i p≤B := normalizedPrimeCoeff_bound _ _ _ _
    (hP i) (zero_le_one.trans hB) (hβ i) p.val
  have he (i : I) : (∑p : atoms,(coeffNorm i p)^2)≤256*B^2 := by
    rw [←Finset.sum_subtype (F:=inferInstance) (p:=fun p : Ideal O=>p∈atoms) atoms (by simp)
      (fun p=>‖normalizedPrimeCoeff (L i) (β i) (P i) p‖^2)]
    exact normalizedPrimeCoeff_energy atoms (L i) (β i) (P i) B (hP i)
      (zero_le_one.trans hB) (hβ i) (hp i) (hN i)
  have hsingle (r : Setoid I) (t : {q // ¬singletonBlock r q}→atoms) :
      (∑v∈rows,‖D v*injectiveTuplePolynomial
        (fun q : {q // singletonBlock r q}=>fun p : atoms=>
          if ∀j : {q // ¬singletonBlock r q},p≠t j then
            a v (singletonRepresentative r q) p else 0)‖^2)≤cK*E := by
    let J := {q // singletonBlock r q}
    letI : DecidableEq J := Classical.decEq J
    let f : J→I := singletonRepresentative r
    have hf : Function.Injective f := singletonRepresentative_injective r
    by_cases hJ : Nonempty J
    · letI : Nonempty J := hJ
      have hcolor (col : atoms→J) :
          (∑v∈rows,‖D v*(∏q : J,∑p : atoms,
            if col p=q then
              (if ∀j : {q // ¬singletonBlock r q},p≠t j then a v (f q) p else 0)
            else 0)‖^2)≤E := by
        let col' : Ideal O→J := fun p=>if h : p∈atoms then col ⟨p,h⟩ else Classical.choice hJ
        let keep : J→Ideal O→Prop := fun q p=>col' p=q ∧
          ∀j : {q // ¬singletonBlock r q},p≠(t j).val
        let L' : J→Finset (Ideal O) := fun q=>(L (f q)).filter (keep q)
        have hsub (q : J) : L' q⊆L (f q) := Finset.filter_subset _ _
        have hdis : (((Finset.univ : Finset J) : Set J).PairwiseDisjoint L') := by
          intro q hq q' hq' hne
          apply Finset.disjoint_left.mpr
          intro p hp hp'
          have hq := (Finset.mem_filter.mp hp).2.1
          have hq' := (Finset.mem_filter.mp hp').2.1
          exact hne (hq.symm.trans hq')
        have hid (v : Row) (q : J) :
            (∑p : atoms,if col p=q then
              (if ∀j : {q // ¬singletonBlock r q},p≠t j then a v (f q) p else 0)
              else 0) =directPrimeSlot (u v) (L' q) (β (f q)) (P (f q)) := by
          rw [directPrimeSlot_sum_atoms _ _ atoms _ _ ((hsub q).trans (hLa (f q)))]
          apply Finset.sum_congr rfl
          intro p hp
          dsimp only [L']
          simp only [normalizedPrimeCoeff,Finset.mem_filter]
          have hkeep : keep q p.val ↔col p=q ∧∀j : {q // ¬singletonBlock r q},p≠t j := by
            simp only [keep,col',p.property,dite_true]
            constructor
            · rintro ⟨hc,hn⟩
              exact ⟨hc,fun j hh=>hn j (congrArg Subtype.val hh)⟩
            · rintro ⟨hc,hn⟩
              exact ⟨hc,fun j hh=>hn j (Subtype.ext hh)⟩
          dsimp only [a]
          simp only [normalizedPrimeCoeff]
          simp only [hkeep]
          by_cases hc : col p=q <;> by_cases ht : ∀j : {q // ¬singletonBlock r q},p≠t j
          <;> by_cases hl : p.val∈L (f q)
          <;> simp only [hc,ht,hl,and_self,and_false,false_and,true_and,and_true,ite_true,ite_false,mul_zero]
          all_goals split_ifs <;> simp only [mul_zero]
        have hbound := hsep f hf L' hsub hdis
        simpa only [hid] using hbound
      have hh := PhysicalRepeatedPrimeSlots.injective_coloring_energy rows
        (fun v q p=>if ∀j : {q // ¬singletonBlock r q},p≠t j then a v (f q) p else 0)
        D E hE (by intro col; convert hcolor col using 1)
      apply hh.trans
      apply mul_le_mul_of_nonneg_right _ hE
      have hc : (Fintype.card J:ℝ)≤ max 1 (K:ℝ) :=
        (show (Fintype.card J:ℝ)≤(K:ℝ) by exact_mod_cast (singleton_card_le r).trans hK).trans (le_max_right _ _)
      exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hc _).trans
        (pow_le_pow_right₀ (le_max_left _ _) (Nat.mul_le_mul_left 2 ((singleton_card_le r).trans hK)))
    · letI : IsEmpty J := not_nonempty_iff.mp hJ
      have hdis : (((Finset.univ : Finset J) : Set J).PairwiseDisjoint (fun q=>L (f q))) := by
        intro q
        exact isEmptyElim q
      have hh := hsep f hf (fun q=>L (f q)) (fun _=>Finset.Subset.refl _) hdis
      have hbound : (∑v∈rows,‖D v‖^2)≤E := by simpa using hh
      have hid (v : Row) : injectiveTuplePolynomial
          (fun q : J=>fun p : atoms=>if ∀j : {q // ¬singletonBlock r q},p≠t j then
            a v (f q) p else 0)=1 := by simp [injectiveTuplePolynomial,Function.injective_of_subsingleton]
      have heq : (∑v∈rows,‖D v*injectiveTuplePolynomial
          (fun q : {q // singletonBlock r q}=>fun p : atoms=>
            if ∀j : {q // ¬singletonBlock r q},p≠t j then
              a v (singletonRepresentative r q) p else 0)‖^2)=(∑v∈rows,‖D v‖^2) := by
        apply Finset.sum_congr rfl
        intro v hv
        have hp := hid v
        change injectiveTuplePolynomial
          (fun q : {q // singletonBlock r q}=>fun p : atoms=>
            if ∀j : {q // ¬singletonBlock r q},p≠t j then
              a v (singletonRepresentative r q) p else 0)=1 at hp
        rw [hp,mul_one]
      rw [heq]
      exact hbound.trans (le_mul_of_one_le_left hE hcK)
  have hh := product_energy_of_singletons rows a coeffNorm D B 256 (cK*E) hB
    (by norm_num) (mul_nonneg (zero_le_one.trans hcK) hE)
    (fun i p=>norm_nonneg _) hv he ha K hK (by
      intro r t
      calc
        _ = (∑v∈rows,‖D v*injectiveTuplePolynomial
          (fun q : {q // singletonBlock r q}=>fun p : atoms=>
            if ∀j : {q // ¬singletonBlock r q},p≠t j then
              a v (singletonRepresentative r q) p else 0)‖^2) := by
          apply Finset.sum_congr rfl
          intro v hv
          apply congrArg (fun z : ℂ=>‖D v*z‖^2)
          apply congrArg injectiveTuplePolynomial
          funext q p
          split_ifs <;> rfl
        _ ≤ _ := hsingle r t)
  have hid (v : Row) (i : I) : (∑p : atoms,a v i p)=directPrimeSlot (u v) (L i) (β i) (P i) :=
    (directPrimeSlot_sum_atoms _ _ atoms _ _ (hLa i)).symm
  have heq : (∑v∈rows,‖D v*(∏i,∑p : atoms,a v i p)‖^2)=
      (∑v∈rows,‖D v*(∏i,directPrimeSlot (u v) (L i) (β i) (P i))‖^2) := by
    apply Finset.sum_congr rfl
    intro v hv
    congr 2
    apply congrArg (D v * ·)
    exact Finset.prod_congr rfl (fun i _=>hid v i)
  rw [heq] at hh
  convert hh using 1
  dsimp [overlapCost,cK]
  ring

end
end OAI.SevenEighths.Angular.PhysicalDetectorDirectInverse


set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Angular.PhysicalDetectorDirectInverse
noncomputable section
open scoped Classical BigOperators
open Set ActualEisensteinCubic
open ConcreteTraceCRT
open CommonMask NaturalRows
open CenteredMomentCommonMaskEnergy CenteredMomentSecondHeightFamily
open CanonicalRowCompletion
open InverseRows CubicEisenstein.AngularRawCoefficientGates
local notation "O" => HeckeFamily.O

theorem overlapping_inverse_marked_energy (angularOrder:ℕ) (εm B : ℝ) (hεm : 0<εm) (hB : 1≤B) (K : ℕ) :
    ∃ degree : ℕ, ∀ data : RowData, data.η.k=(angularOrder:ℤ) → ∃ C U₀ : ℝ, 0<C ∧ 1<U₀ ∧
      ∀ U : ℝ, U₀≤U → ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι≤K →
      ∀ (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ),
        (∀i,0≤ell i) → (∀i,∀P∈L i,Prime P) →
        (∀i,∀P∈L i,((P.absNorm : ℝ)/U^(ell i))∈Icc (1 : ℝ) 2) →
        (∀i,∀P∈L i,‖β i P‖≤B) →
        (∀i,((deletedBase data).modulus.absNorm : ℝ)<U^(ell i)) →
      ∀r : ℝ, 0≤r → r+2*(∑i,ell i)<1 → 2*r+8*(∑i,ell i)<3 →
      ∀rows : Finset NonzeroElement, (∀u∈rows,‖eisEmbedding u.val‖^2≤U) →
      ∀tstar : ℝ, ∀reverse : Bool, ∀n : ℕ,n≤2 → ∀σ∈Icc (0 : ℝ) 1,
      ∀height t : ℝ, 0≤height → t∈Icc (-height) height →
      (∑u∈rows,‖polynomial (data.character u) true
        ((HeckeDetectorRowwisePolynomial.logProfile^[n])
          (HeckeDetectorCoefficientTransfer.orientedProfile reverse
            (HeckeDetectorInverseFiberCount.inverseTest U tstar r))) (U^r) σ t *
          (∏i,directPrimeSlot u.val (L i) (β i) (U^(ell i)))‖^2) ≤
        (C*(1+height)^degree)*U^(1+εm) := by
  obtain ⟨degree,henergy⟩ := bounded_inverse_marked_energy angularOrder εm B hεm hB K
  refine ⟨degree,?_⟩
  intro data hk
  obtain ⟨C,U₀,hC,hU₀,henergy⟩ := henergy data hk
  refine ⟨overlapCost B K*C,U₀,mul_pos (overlapCost_pos B hB K) hC,hU₀,?_⟩
  intro U hU ι inst dec hK L ell β hell hp hratio hβ hlarge r hr hfirst hsecond rows hrows
    tstar reverse n hn σ hσ height t hh ht
  have hU1 : 1<U := hU₀.trans_le hU
  have hUp : 0<U := zero_lt_one.trans hU1
  let D : NonzeroElement→ℂ := fun u=>polynomial (data.character u) true
    ((HeckeDetectorRowwisePolynomial.logProfile^[n])
      (HeckeDetectorCoefficientTransfer.orientedProfile reverse
        (HeckeDetectorInverseFiberCount.inverseTest U tstar r))) (U^r) σ t
  have hP (i : ι) : 1≤U^(ell i) := Real.one_le_rpow hU1.le (hell i)
  have hN (i : ι) (p : Ideal O) (hp' : p∈L i) : (p.absNorm:ℝ)≤2*U^(ell i) :=
    (div_le_iff₀ (Real.rpow_pos_of_pos hUp _)).mp (hratio i p hp').2
  have hsep : ∀{J : Type} [Fintype J] [DecidableEq J],
      ∀f : J→ι,Function.Injective f →∀L' : J→Finset (Ideal O),
      (∀j,L' j⊆L (f j)) →
      (((Finset.univ : Finset J) : Set J).PairwiseDisjoint L') →
      (∑v∈rows,‖D v*(∏j,directPrimeSlot v.val (L' j) (β (f j)) (U^(ell (f j))))‖^2)≤
        (C*(1+height)^degree)*U^(1+εm) := by
    intro J instJ decJ f hf L' hsub hdis
    have hJK : Fintype.card J≤K := (Fintype.card_le_of_injective f hf).trans hK
    have hsum : (∑j,ell (f j))≤∑i,ell i :=
      PhysicalRepeatedPrimeSlots.sum_comp_le_total f hf ell hell
    exact henergy U hU hJK L' (fun j=>ell (f j)) (fun j=>β (f j))
      (fun j=>hell (f j)) (fun j p hp'=>hp (f j) p (hsub j hp')) hdis
      (fun j p hp'=>hratio (f j) p (hsub j hp'))
      (fun j p hp'=>hβ (f j) p (hsub j hp')) (fun j=>hlarge (f j))
      r hr (by linarith) (by linarith) rows hrows tstar reverse n hn σ hσ height t hh ht
  have he := overlapping_direct_energy rows (fun u=>u.val) D L β (fun i=>U^(ell i)) B
    ((C*(1+height)^degree)*U^(1+εm)) hB (by positivity) K hK hP hβ
    (fun i p hp'=> (hp i p hp').ne_zero) hN hsep
  convert he using 1
  ring


end
end OAI.SevenEighths.Angular.PhysicalDetectorDirectInverse

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorDirectInverse.normalizedPrimeCoeff_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorDirectInverse.normalizedPrimeCoeff_energy

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorDirectInverse.product_energy_of_singletons
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorDirectInverse.product_energy_of_singletons

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorDirectInverse.overlapping_direct_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorDirectInverse.overlapping_direct_energy

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorDirectInverse.overlapping_inverse_marked_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorDirectInverse.overlapping_inverse_marked_energy
