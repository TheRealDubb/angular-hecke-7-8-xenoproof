import AngularPhysicalDetectorHighLocal
import OAI.NumberTheory.DirichletL.Detector.HighRowsLocal

namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
noncomputable section
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein ProbePhase ProbeEuler ProbePrimePower ProbeRow
open ConcreteTraceCRT ProbeCompleted ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma bareIdealHighSummand_support (η : AngularCharacter) (u : O) (x w z : ℂ)
    (I J K L : Id) (h : bareIdealHighSummand η u x w z I J K L≠0) :
    highSupport I J K L := by
  by_contra hn
  apply h
  unfold highSupport at hn
  simp only [bareIdealHighSummand,bareIdealHighCoefficient,dite_eq_right hn,zero_mul]

theorem bareSourceCoefficient_sixth_frequency (η : AngularCharacter)
    (I : Ideal O) (hI : primaryGenerator I≠0) (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (v H : O) (hcop : IsCoprime v (A*s)) :
    bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) (v^6*H) =
      bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) H := by
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [bareCongruenceCoefficient_sixth_frequency A s hA hs v H hcop]

theorem bareSourceCoefficient_product_row_frequency (η : AngularCharacter) (u : O) (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hIJcop : IsCoprime I J)
    (n m s r : O)
    (hc : Supported (Ideal.span {primaryGenerator I})) (hd : Supported (Ideal.span {primaryGenerator J}))
    (hn : Supported (Ideal.span {n})) (hm : Supported (Ideal.span {m}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpc : goodLambda^2∣primaryGenerator I-1) (hpd : goodLambda^2∣primaryGenerator J-1)
    (hpn : goodLambda^2∣n-1) (hpm : goodLambda^2∣m-1)
    (hps : goodLambda^2∣s-1) (hpr : goodLambda^2∣r-1)
    (hcop : IsCoprime ((primaryGenerator I*n^3)*s) ((primaryGenerator J*m^3)*r)) (a b : O)
    (hba : IsCoprime b ((primaryGenerator I*n^3)*s))
    (hab : IsCoprime a ((primaryGenerator J*m^3)*r)) :
    let A := primaryGenerator I*n^3
    let B := primaryGenerator J*m^3
    let hA := supportedElement_ne_zero A (supported_completed _ _ hc hn)
    let hB := supportedElement_ne_zero B (supported_completed _ _ hd hm)
    bareSourceCoefficient η (I*J) hIJ.2 (A*B) (s*r) (mul_ne_zero hA hB) (u*(a*b)^6) =
      bareSourceCoefficient η I hI.2 A s hA (u*a^6) * bareSourceCoefficient η J hJ.2 B r hB (u*b^6) := by
  have he := bareSourceCoefficient_product η I J hI hJ hIJ hIJcop n m s r
    hc hd hn hm hs hr hpc hpd hpn hpm hps hpr hcop (u*(a*b)^6)
  dsimp only at he ⊢
  have hi := bareSourceCoefficient_sixth_frequency η I hI.2 (primaryGenerator I*n^3) s
    (supported_completed _ _ hc hn) hs b (u*a^6) hba
  have hj := bareSourceCoefficient_sixth_frequency η J hJ.2 (primaryGenerator J*m^3) r
    (supported_completed _ _ hd hm) hr a (u*b^6) hab
  rw [show b^6*(u*a^6)=u*(a*b)^6 by ring] at hi
  rw [show a^6*(u*b^6)=u*(a*b)^6 by ring] at hj
  rw [hi,hj] at he
  exact he

theorem bareIdealHighCoefficient_row_mul (η : AngularCharacter) (u : O)
    (I J K L I' J' K' L' : Id)
    (hcop : IsCoprime (I*J*K*L) (I'*J'*K'*L')) :
    bareIdealHighCoefficient η u (I*I') (J*J') (K*K') (L*L') =
      bareIdealHighCoefficient η u I J K L * bareIdealHighCoefficient η u I' J' K' L' := by
  have hII := hcop.mono (first_block_dvd I J K L) (first_block_dvd I' J' K' L')
  by_cases h : highSupport I J K L ∧ highSupport I' J' K' L'
  · have hprod := (highSupport_mul I J K L I' J' K' L' hII).mpr h
    rcases h with ⟨h,h'⟩
    have hsA := (supported_mul_iff (I*J^3) K).mpr
      ⟨(supported_mul_iff I (J^3)).mpr ⟨h.2.1,supported_pow h.2.2.1 3⟩,h.2.2.2.1⟩
    have hsB := (supported_mul_iff (I'*J'^3) K').mpr
      ⟨(supported_mul_iff I' (J'^3)).mpr ⟨h'.2.1,supported_pow h'.2.2.1 3⟩,h'.2.2.2.1⟩
    have hc3 : IsCoprime ((I*J*K*L)^3) ((I'*J'*K'*L')^3) := hcop.pow_left.pow_right
    have hab := primaryGenerator_coprime _ _ hsA hsB
      (hc3.mono (completed_block_dvd_cube I J K L) (completed_block_dvd_cube I' J' K' L'))
    have hba := primaryGenerator_coprime _ _ h'.2.2.2.2 hsA
      (hcop.symm.pow_right.mono (last_block_dvd I' J' K' L') (completed_block_dvd_cube I J K L))
    have hab' := primaryGenerator_coprime _ _ h.2.2.2.2 hsB
      (hcop.pow_right.mono (last_block_dvd I J K L) (completed_block_dvd_cube I' J' K' L'))
    simp only [primaryGenerator_mul,primaryGenerator_pow] at hab hba hab'
    have he := bareSourceCoefficient_product_row_frequency η u I I'
      ⟨h.1,supported_primaryGenerator_ne_zero I h.2.1⟩
      ⟨h'.1,supported_primaryGenerator_ne_zero I' h'.2.1⟩
      ⟨hprod.1,supported_primaryGenerator_ne_zero (I*I') hprod.2.1⟩ hII
      (primaryGenerator J) (primaryGenerator J') (primaryGenerator K) (primaryGenerator K')
      ((supported_span_primaryGenerator_iff I).mpr h.2.1)
      ((supported_span_primaryGenerator_iff I').mpr h'.2.1)
      ((supported_span_primaryGenerator_iff J).mpr h.2.2.1)
      ((supported_span_primaryGenerator_iff J').mpr h'.2.2.1)
      ((supported_span_primaryGenerator_iff K).mpr h.2.2.2.1)
      ((supported_span_primaryGenerator_iff K').mpr h'.2.2.2.1)
      (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I h.2.1)).2
      (primaryGenerator_spec I' (supported_primaryGenerator_ne_zero I' h'.2.1)).2
      (primaryGenerator_spec J (supported_primaryGenerator_ne_zero J h.2.2.1)).2
      (primaryGenerator_spec J' (supported_primaryGenerator_ne_zero J' h'.2.2.1)).2
      (primaryGenerator_spec K (supported_primaryGenerator_ne_zero K h.2.2.2.1)).2
      (primaryGenerator_spec K' (supported_primaryGenerator_ne_zero K' h'.2.2.2.1)).2
      hab (primaryGenerator L) (primaryGenerator L') hba hab'
    unfold highSupport at hprod h h'
    unfold bareIdealHighCoefficient
    rw [dite_eq_left hprod,dite_eq_left h,dite_eq_left h']
    simp only [primaryGenerator_mul]
    dsimp only at he
    convert he using 1 ; ring_nf
  · have hprod := mt (highSupport_mul I J K L I' J' K' L' hII).mp h
    unfold highSupport at hprod
    unfold bareIdealHighCoefficient
    rw [dite_eq_right hprod]
    by_cases hi : highSupport I J K L
    · have hj : ¬highSupport I' J' K' L' := fun hj=>h ⟨hi,hj⟩
      unfold highSupport at hj
      rw [dite_eq_right hj,mul_zero]
    · unfold highSupport at hi
      rw [dite_eq_right hi,zero_mul]

theorem bareIdealHighSummand_row_mul (η : AngularCharacter) (u : O) (x w z : ℂ)
    (I J K L I' J' K' L' : Id)
    (hcop : IsCoprime (I*J*K*L) (I'*J'*K'*L')) :
    bareIdealHighSummand η u x w z (I*I') (J*J') (K*K') (L*L') =
      bareIdealHighSummand η u x w z I J K L * bareIdealHighSummand η u x w z I' J' K' L' := by
  unfold bareIdealHighSummand
  rw [bareIdealHighCoefficient_row_mul η u I J K L I' J' K' L' hcop,
    fullIdealWeight_mul,fullIdealWeight_mul,fullIdealWeight_mul,fullIdealWeight_mul]
  ring

@[simp] theorem bareIdealHighCoefficient_row_one (η : AngularCharacter) (u : O) :
    bareIdealHighCoefficient η u 1 1 1 1=1 := by
  have hs := supported_one_ideal
  have hg : Squarefree (1:Ideal O) ∧ Supported 1 ∧ Supported 1 ∧ Supported 1 ∧ Supported 1 :=
    ⟨squarefree_one,hs,hs,hs,hs⟩
  unfold bareIdealHighCoefficient
  rw [dite_eq_left hg]
  simp only [primaryGenerator_one,one_pow,mul_one]
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [gaussTwo_one,ProbePhysical.G_one,angularFactor_one]
  have ho := supported_residue_odd (1:O) (by
    rw [Ideal.span_singleton_one,←Ideal.one_eq_top];exact hs)
  rw [reciprocitySign_one_left (1:O) ho,
    bareCongruenceCoefficient_inner_one 1 one_ne_zero,outerQuotient_mk]
  simp only [map_one,star_one,one_mul,Ideal.span_singleton_one,←Ideal.one_eq_top]

@[simp] theorem bareIdealHighSummand_row_one (η : AngularCharacter) (u : O) (x w z : ℂ) :
    bareIdealHighSummand η u x w z 1 1 1 1=1 := by
  have hw (t : ℂ) : fullIdealWeight t (1:Ideal O)=1 := (IdealEuler.normWeight t).map_one
  simp only [bareIdealHighSummand,bareIdealHighCoefficient_row_one,hw,one_mul]

theorem bareIdealHighSeries_row_hasProd (η : AngularCharacter) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,
      bareIdealHighSummand η u x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))
      (bareIdealHighSeries η u x w z) := by
  apply highArray_hasProd (fun a : HighIdeal=>bareIdealHighSummand η u x w z a.1.1 a.1.2 a.2.1 a.2.2)
  · exact bareIdealHighSummand_row_one η u x w z
  · intro a b hc
    exact bareIdealHighSummand_row_mul η u x w z _ _ _ _ _ _ _ _ hc
  · intro a ha
    have hs := bareIdealHighSummand_support η u x w z a.1.1 a.1.2 a.2.1 a.2.2 ha
    exact ⟨hs.2.1.1,hs.2.2.1.1,hs.2.2.2.1.1,hs.2.2.2.2.1⟩
  · exact (bareIdealHighSummand_summable η u x w z hx hw hz).norm

def markedIdealHighSummand (S : Finset Id) (D : Id) (η : AngularCharacter)
    (u : O) (x w z : ℂ) (I J K L : Id) : ℂ :=
  highIdealMask S D I J K L * bareIdealHighSummand η u x w z I J K L

lemma markedIdealHighSummand_norm_le (S : Finset Id) (D : Id) (η : AngularCharacter)
    (u : O) (x w z : ℂ) (I J K L : Id) :
    ‖markedIdealHighSummand S D η u x w z I J K L‖≤‖bareIdealHighSummand η u x w z I J K L‖ := by
  rw [markedIdealHighSummand,norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (highIdealMask_norm_le_one S D I J K L)

theorem markedIdealHighSummand_summable (S : Finset Id) (D : Id) (η : AngularCharacter)
    (u : O) (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    Summable (fun p : (Id×Id)×(Id×Id) =>
      markedIdealHighSummand S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _=>norm_nonneg _)
    (fun p=>markedIdealHighSummand_norm_le S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2)
    (bareIdealHighSummand_summable η u x w z hx hw hz).norm

def markedIdealHighSeries (S : Finset Id) (D : Id) (η : AngularCharacter)
    (u : O) (x w z : ℂ) : ℂ :=
  ∑' p : (Id×Id)×(Id×Id), markedIdealHighSummand S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2

theorem excludedIdealHighSeries_row_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : AngularCharacter) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,
      markedIdealHighSummand S 1 η u x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))
      (markedIdealHighSeries S 1 η u x w z) := by
  apply highArray_hasProd (fun a : HighIdeal=>markedIdealHighSummand S 1 η u x w z a.1.1 a.1.2 a.2.1 a.2.2)
  · simp only [Prod.fst_one,Prod.snd_one,markedIdealHighSummand,
      highIdealMask_unmarked_one S hS,bareIdealHighSummand_row_one,one_mul]
  · intro a b hc
    simp only [Prod.fst_mul,Prod.snd_mul,markedIdealHighSummand,
      highIdealMask_unmarked_mul S hS a b,
      bareIdealHighSummand_row_mul η u x w z _ _ _ _ _ _ _ _ hc]
    ring
  · intro a ha
    have hh : bareIdealHighSummand η u x w z a.1.1 a.1.2 a.2.1 a.2.2≠0 :=
      (mul_ne_zero_iff.mp ha).2
    have hs := bareIdealHighSummand_support η u x w z a.1.1 a.1.2 a.2.1 a.2.2 hh
    exact ⟨hs.2.1.1,hs.2.2.1.1,hs.2.2.2.1.1,hs.2.2.2.2.1⟩
  · exact (markedIdealHighSummand_summable S 1 η u x w z hx hw hz).norm

def rowHighPrimeTerm (η : AngularCharacter) (u : O) (x w z : ℂ)
    (P : PrimeIdeal) (b : HighValuation) : ℂ :=
  bareIdealHighSummand η u x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)

lemma rowHighPrimeTerm_summable_norm (η : AngularCharacter) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) (P : PrimeIdeal) :
    Summable (fun b : HighValuation=>‖rowHighPrimeTerm η u x w z P b‖) := by
  have hs := ((bareIdealHighSummand_summable η u x w z hx hw hz).norm.comp_injective
    highIdeals_injective).comp_injective (Finsupp.single_injective P)
  simpa only [Function.comp_def,highIdeals_single,rowHighPrimeTerm] using hs

lemma rowHighPrimeTerm_zero_of_two_le (η : AngularCharacter) (u : O) (x w z : ℂ)
    (P : PrimeIdeal) (e l k m : ℕ) (he : 2≤e) :
    rowHighPrimeTerm η u x w z P ((e,l),(k,m))=0 := by
  by_contra hn
  have hs := bareIdealHighSummand_support η u x w z (P.val^e) (P.val^l) (P.val^k) (P.val^m) hn
  have hc := hs.1.eq_zero_or_one_of_pow_of_not_isUnit P.property.not_isUnit
  omega

theorem rowHighPrimeTerm_tsum_eq_localFactor (η : AngularCharacter) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) (P : PrimeIdeal) :
    (∑' b : HighValuation,rowHighPrimeTerm η u x w z P b)=
      idealRowHighLocalFactor η u P.val x w z := by
  have hs := (rowHighPrimeTerm_summable_norm η u x w z hx hw hz P).of_norm
  rw [hs.tsum_prod,hs.prod.tsum_prod]
  have he (e l : ℕ) :
      (∑' b : ℕ×ℕ, rowHighPrimeTerm η u x w z P ((e,l),b))=
        ∑' k,∑' m,rowHighPrimeTerm η u x w z P ((e,l),(k,m)) :=
    (hs.prod_factor (e,l)).tsum_prod
  simp_rw [he]
  rw [tsum_eq_sum (s:=Finset.range 2) (fun e he=>by
    have hh : 2≤e := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using he)
    simp only [rowHighPrimeTerm_zero_of_two_le η u x w z P e _ _ _ hh,tsum_zero]),
    ←Fin.sum_univ_eq_sum_range]
  rfl

theorem bareIdealHighSeries_row_hasProd_localFactor (η : AngularCharacter) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>idealRowHighLocalFactor η u P.val x w z)
      (bareIdealHighSeries η u x w z) := by
  have h := bareIdealHighSeries_row_hasProd η u x w z hx hw hz
  change HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,rowHighPrimeTerm η u x w z P b) _ at h
  simpa only [rowHighPrimeTerm_tsum_eq_localFactor η u x w z hx hw hz] using h

theorem excludedRowHighLocalFactor (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : AngularCharacter) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) (P : PrimeIdeal) :
    (∑' b : HighValuation,markedIdealHighSummand S 1 η u x w z
      (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)) =
      if P.val∈S then 1 else idealRowHighLocalFactor η u P.val x w z := by
  by_cases hP : P.val∈S
  · rw [ite_eq_left hP]
    have he (b : HighValuation) : markedIdealHighSummand S 1 η u x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)=if b=0 then 1 else 0 := by
      rw [markedIdealHighSummand,highIdealMask_prime_inside S hS P hP b]
      by_cases hb : b=0
      · subst b
        simp only [Prod.fst_zero,Prod.snd_zero,pow_zero,bareIdealHighSummand_row_one,mul_one]
      · simp only [ite_eq_right hb,zero_mul]
    simp only [he,tsum_ite_eq]
  · rw [ite_eq_right hP]
    simp only [markedIdealHighSummand,highIdealMask_prime_outside S hS P hP,one_mul]
    exact rowHighPrimeTerm_tsum_eq_localFactor η u x w z hx hw hz P

theorem excludedIdealHighSeries_row_hasProd_outside (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : AngularCharacter) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>idealRowHighLocalFactor η u P.val.val x w z)
      (markedIdealHighSeries S 1 η u x w z) := by
  have h := excludedIdealHighSeries_row_hasProd S hS η u x w z hx hw hz
  simp only [excludedRowHighLocalFactor S hS η u x w z hx hw hz] at h
  apply (hasProd_subtype_iff_mulIndicator
    (s:={P : PrimeIdeal | P.val∉S})
    (f:=fun P : PrimeIdeal=>idealRowHighLocalFactor η u P.val x w z)).mpr
  convert h using 1
  funext P
  simp only [Set.mulIndicator,Set.mem_ofPred_eq]
  split_ifs <;> simp_all

end
end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.bareIdealHighSeries_row_hasProd_localFactor

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.excludedIdealHighSeries_row_hasProd_outside
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.excludedIdealHighSeries_row_hasProd_outside
