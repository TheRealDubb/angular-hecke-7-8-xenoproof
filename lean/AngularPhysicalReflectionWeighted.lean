import AngularPhysicalReflectionMass
import OAI.NumberTheory.DirichletL.Moments.ReflectionWeightedEnergy
noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.ReflectionWeighted
open CenteredMomentReflectionDeletion (SmoothIdeal)
open CenteredMomentReflectionMass (unitSmooth)
open CenteredMomentReflectedAnnuli
open CenteredMomentReflectionWeightedEnergy (Index baseIndex weighted_selection_energy)
open ReflectionMass
local notation "O" => ActualEisensteinCubic.O
def signedWeight (η ηi : AngularCharacter) (S : Finset (Ideal O)) (B : ℕ)
    (a : Index S) : ℂ :=
  coefficient η ηi S a.1.1.val a.1.2 * (annularMass B a.2 : ℂ)

lemma signedWeight_norm (η ηi : AngularCharacter) (S : Finset (Ideal O))
    (B : ℕ) (a : Index S) :
    ‖signedWeight η ηi S B a‖ =
      ‖coefficient η ηi S a.1.1.val a.1.2‖ * annularMass B a.2 := by
  rw [signedWeight,norm_mul,Complex.norm_real,Real.norm_of_nonneg (annularMass_nonneg _ _)]

lemma annularMass_le_two (B : ℕ) (hB : 2≤B) (n : ℤ) :
    annularMass B n ≤ annularMass 2 n := by
  have hp := CenteredMomentSectorLocalization.dyadicScale_pos n
  unfold annularMass
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity)
    (pow_le_pow_right₀ (by linarith [CenteredMomentSectorLocalization.dyadicScale_pos n]) hB)

lemma coefficient_joint_summable (η ηi : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) :
    Summable (fun a : S.powerset × SmoothIdeal S =>
      ‖coefficient η ηi S a.1.val a.2‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  exact ⟨fun D => coefficient_summable_norm η ηi S hS D.val
    (Finset.mem_powerset.mp D.property),(hasSum_fintype _).summable⟩

lemma coefficient_joint_mass (η ηi : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) :
    (∑' a : S.powerset × SmoothIdeal S,‖coefficient η ηi S a.1.val a.2‖) =
      ∑D∈S.powerset,∑'H : SmoothIdeal S,‖coefficient η ηi S D H‖ := by
  rw [(coefficient_joint_summable η ηi S hS).tsum_prod,tsum_fintype]
  exact Finset.sum_coe_sort S.powerset (fun D => ∑'H : SmoothIdeal S,‖coefficient η ηi S D H‖)

lemma signedWeight_summable_norm (η ηi : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (B : ℕ) (hB : 2≤B) :
    Summable (fun a : Index S => ‖signedWeight η ηi S B a‖) := by
  simp_rw [signedWeight_norm]
  exact (coefficient_joint_summable η ηi S hS).mul_of_nonneg
    (annularMass_summable B hB) (fun _ => norm_nonneg _) (annularMass_nonneg B)

lemma signedWeight_mass (η ηi : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (B : ℕ) (hB : 2≤B) :
    (∑'a : Index S,‖signedWeight η ηi S B a‖) =
      (∑D∈S.powerset,∑'H : SmoothIdeal S,‖coefficient η ηi S D H‖) *
        ∑'n : ℤ,annularMass B n := by
  rw [(signedWeight_summable_norm η ηi S hS B hB).tsum_prod]
  simp_rw [signedWeight_norm,tsum_mul_left]
  rw [tsum_mul_right,coefficient_joint_mass η ηi S hS]

lemma signed_series_reindex (η ηi : AngularCharacter) (S : Finset (Ideal O)) (B : ℕ)
    (f : Index S→ℂ) (hs : Summable (fun a=>‖signedWeight η ηi S B a*f a‖)) :
    (∑'a : Index S,signedWeight η ηi S B a*f a) =
      ∑D : S.powerset,∑'H : SmoothIdeal S,∑'n : ℤ,
        coefficient η ηi S D.val H*(annularMass B n:ℂ)*f ((D,H),n) := by
  rw [hs.of_norm.tsum_prod,hs.of_norm.prod.tsum_prod,tsum_fintype]
  rfl

lemma signedWeight_base (η ηi : AngularCharacter) (S : Finset (Ideal O)) (B : ℕ) :
    signedWeight η ηi S B (baseIndex S)=(annularMass B 0:ℂ) := by
  simp only [signedWeight,baseIndex,coefficient_empty_unit,one_mul]

theorem signed_mass_subpower (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)),(∀P∈S,Prime P) →
      ∀(η ηi : AngularCharacter)(B : ℕ),2≤B →
      Summable (fun a : Index S => ‖signedWeight η ηi S B a‖) ∧
      (∑'a : Index S,‖signedWeight η ηi S B a‖) ≤
        C*(Ideal.absNorm (∏P∈S,P):ℝ)^ε*(∑'n : ℤ,annularMass B n) := by
  obtain ⟨C,hC,hb⟩ := reflection_mass_subpower ε hε
  refine ⟨C,hC,?_⟩
  intro S hS η ηi B hB
  refine ⟨signedWeight_summable_norm η ηi S hS B hB,?_⟩
  rw [signedWeight_mass η ηi S hS B hB]
  exact mul_le_mul_of_nonneg_right (hb S hS η ηi).2 (tsum_nonneg (annularMass_nonneg B))

def annularConstant : ℝ := 1 + ∑'n : ℤ,annularMass 2 n

lemma annularConstant_pos : 0<annularConstant := by
  have h : 0≤∑'n : ℤ,annularMass 2 n := tsum_nonneg (annularMass_nonneg 2)
  dsimp [annularConstant]
  linarith

lemma annularMass_total_le (B : ℕ) (hB : 2≤B) :
    (∑'n : ℤ,annularMass B n) ≤ annularConstant := by
  apply ((annularMass_summable B hB).tsum_le_tsum (annularMass_le_two B hB)
    (annularMass_summable 2 le_rfl)).trans
  dsimp [annularConstant]
  linarith

theorem uniform_signed_mass (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)),(∀P∈S,Prime P) →
      ∀(η ηi : AngularCharacter)(B : ℕ),2≤B →
      Summable (fun a : Index S => ‖signedWeight η ηi S B a‖) ∧
      (∑'a : Index S,‖signedWeight η ηi S B a‖) ≤
        C*(Ideal.absNorm (∏P∈S,P):ℝ)^ε := by
  obtain ⟨C,hC,hb⟩ := signed_mass_subpower ε hε
  refine ⟨C*annularConstant,mul_pos hC annularConstant_pos,?_⟩
  intro S hS η ηi B hB
  refine ⟨(hb S hS η ηi B hB).1,(hb S hS η ηi B hB).2.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left (annularMass_total_le B hB) (by positivity)).trans_eq (by ring)


theorem actual_reflection_energy (ε:ℝ) (hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀{ι:Type*} [Fintype ι],
      ∀(S:ι→Finset (Ideal O)),(∀i P,P∈S i → Prime P) →
      ∀(η ηi:ι→AngularCharacter)(B:ι→ℕ),(∀i,2≤B i) →
      ∀(R E:ℝ),1≤R → (∀i,(Ideal.absNorm (∏P∈S i,P):ℝ)≤R) →
      ∀f:∀i,Index (S i)→ℂ,
      (∀a:∀i,Index (S i),(∑i,‖f i (a i)‖^2)≤E) →
      (∀i,Summable (fun a=>‖signedWeight (η i) (ηi i) (S i) (B i) a*f i a‖)) ∧
      (∑i,‖∑'a,signedWeight (η i) (ηi i) (S i) (B i) a*f i a‖^2)≤C*R^ε*E := by
  obtain ⟨C,hC,hb⟩:=uniform_signed_mass (ε/2) (by positivity)
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro ι _ S hS η ηi B hB R E hR hcap f hselection
  have hR0:0≤R:=by linarith
  have hs (i:ι):= (hb (S i) (hS i) (η i) (ηi i) (B i) (hB i)).1
  have hm (i:ι): (∑'a,‖signedWeight (η i) (ηi i) (S i) (B i) a‖)≤C*R^(ε/2):=by
    apply (hb (S i) (hS i) (η i) (ηi i) (B i) (hB i)).2.trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hcap i) (by positivity : 0≤ε/2)) hC.le
  have hh:=weighted_selection_energy (fun i=>baseIndex (S i))
    (fun i=>signedWeight (η i) (ηi i) (S i) (B i)) f (C*R^(ε/2)) E
    (by positivity) hs hm hselection
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  have hr:(R^(ε/2))^2=R^ε:=by
    rw [←Real.rpow_natCast,←Real.rpow_mul hR0]
    congr 1
    ring
  rw [mul_pow,hr]
end OAI.SevenEighths.Angular.ReflectionWeighted

#print axioms OAI.SevenEighths.Angular.ReflectionWeighted.signedWeight_norm
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ReflectionWeighted.signedWeight_norm

#print axioms OAI.SevenEighths.Angular.ReflectionWeighted.annularMass_le_two
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ReflectionWeighted.annularMass_le_two

#print axioms OAI.SevenEighths.Angular.ReflectionWeighted.coefficient_joint_summable
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ReflectionWeighted.coefficient_joint_summable

#print axioms OAI.SevenEighths.Angular.ReflectionWeighted.coefficient_joint_mass
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ReflectionWeighted.coefficient_joint_mass

#print axioms OAI.SevenEighths.Angular.ReflectionWeighted.signedWeight_summable_norm
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ReflectionWeighted.signedWeight_summable_norm

#print axioms OAI.SevenEighths.Angular.ReflectionWeighted.signedWeight_mass
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ReflectionWeighted.signedWeight_mass

#print axioms OAI.SevenEighths.Angular.ReflectionWeighted.signed_series_reindex
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ReflectionWeighted.signed_series_reindex

#print axioms OAI.SevenEighths.Angular.ReflectionWeighted.signedWeight_base
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ReflectionWeighted.signedWeight_base

#print axioms OAI.SevenEighths.Angular.ReflectionWeighted.signed_mass_subpower
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ReflectionWeighted.signed_mass_subpower

#print axioms OAI.SevenEighths.Angular.ReflectionWeighted.annularConstant_pos
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ReflectionWeighted.annularConstant_pos

#print axioms OAI.SevenEighths.Angular.ReflectionWeighted.annularMass_total_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ReflectionWeighted.annularMass_total_le

#print axioms OAI.SevenEighths.Angular.ReflectionWeighted.uniform_signed_mass
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ReflectionWeighted.uniform_signed_mass

#print axioms OAI.SevenEighths.Angular.ReflectionWeighted.actual_reflection_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ReflectionWeighted.actual_reflection_energy
