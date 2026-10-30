import AngularPhysicalDetectorHighSelectedCoordinates

/- Actual angular adaptation of pinned OAI-003 source proof bodies.
Original OpenAI and predecessor Apache-2.0 notices retained in source pin. -/
set_option Elab.async false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
noncomputable section
open scoped Classical BigOperators ComplexConjugate Topology
open Filter
open ActualEisensteinCubic HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
open ProbeHighRowFamily (rowCharacter unitPart unitPart_spec unitPart_coprime unitPart_ne_zero
  multiplicity_lt_six canonical_decomposition markExclusions markedSourceExclusions
  marked_firstTail FirstTail selected_V_ne_zero row_phase_ramified)
local notation "O" => ActualEisensteinCubic.O
attribute [local irreducible] FamilyContinuation.LFunction AngularCharacter.excludePrimes SourceRows.targetRow

def finiteLocalCorrection (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal) (hs : Supported P.val)
    (x w z : ℂ) : ℂ :=
  ProbeLocal.continuedCorrection (coordV P.val.absNorm z)
    (coordW P.val.absNorm (idealRowHom u.val P.val) w)
    (coordD P.val.absNorm (η.idealHom P.val) (idealRowHom u.val P.val) x)
    (continuedMarkedLocal η u P hs x w z)

theorem continuedCompensatedLocal_eq_difference (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z B q : ℂ) :
    continuedCompensatedLocal η u P hs x w z B q=
      B*continuedMarkedLocal η u P hs x w z*localNormalization η u P x w z-
        q*finiteLocalCorrection η u P hs x w z := by
  rw [localNormalization_coordinates]
  unfold continuedCompensatedLocal finiteLocalCorrection ProbeLocal.compensatedReplacement ProbeLocal.continuedCorrection
  ring

theorem ramifiedCorrection_eq_marked (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    ramifiedCorrection η u P hs x w z=
      1+(1-coordV P.val.absNorm z)*continuedMarkedLocal η u P hs x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := (supported_prime_data p hp hsp).1
  have hnorm : Ideal.absNorm (Ideal.span {p})=P.val.absNorm := congrArg Ideal.absNorm hspan
  change ramifiedClosed p hp hg (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp))) x w z (multiplicity p u.val)=
    1+(1-coordV P.val.absNorm z)*rowClosedMarked p hp hg (targetMonoid η p) (actualACube η p)
      ((P.val.absNorm:ℂ)^(-x)) ((P.val.absNorm:ℂ)^(-w)) (coordV P.val.absNorm z)
      (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp))) (multiplicity p u.val)
  unfold ramifiedClosed
  rw [hnorm]

theorem finiteLocalCorrection_ramified (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hP : P.val∣Ideal.span {u.val}) (x w z : ℂ) :
    finiteLocalCorrection η u P hs x w z=ramifiedCorrection η u P hs x w z := by
  rw [ramifiedCorrection_eq_marked]
  unfold finiteLocalCorrection
  rw [row_phase_ramified u P hP]
  simp only [coordW,coordD,star_zero,mul_zero,zero_mul,ProbeLocal.continuedCorrection,
    sub_zero,mul_one,div_one]

theorem finiteLocalCorrection_unramified (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) (x w z : ℂ)
    (hV : ‖coordV P.val.absNorm z‖<1)
    (hR : ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1) :
    finiteLocalCorrection η u P hs x w z=idealUnramifiedCorrection η u P x w z := by
  rw [finiteLocalCorrection,continuedMarkedLocal_unramified η u P hs hn x w z hV hR]
  rfl

theorem initial_marked_geometry (η : AngularCharacter) (P : PrimeIdeal) (x z : ℂ)
    (hx : 3/2<x.re) (hz : 1/6<z.re) :
    ‖coordV P.val.absNorm z‖<1 ∧
      ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1 := by
  have hQ : (1:ℝ)<P.val.absNorm := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (1:ℕ)<2) (SmoothMobiusCorrection.prime_norm_two_le P))
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  constructor
  · rw [coordV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  · apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η _)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)

theorem finiteLocalCorrection_eq_initial (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    finiteLocalCorrection η u P hs x w z=localCorrection η u P x w z := by
  by_cases hP : P.val∣Ideal.span {u.val}
  · rw [finiteLocalCorrection_ramified η u P hs hP]
    exact (localCorrection_eq_ramified η u P hs hP x w z hx hw hz).symm
  · have hg := initial_marked_geometry η P x z hx hz
    rw [finiteLocalCorrection_unramified η u P hs hP x w z hg.1 hg.2]
    exact (localCorrection_unramified_ideal η u P hs (supported_prime_coprime P hs u.val hP)
      x w z hx hw hz).symm

theorem continuedCompensatedLocal_eq_initial (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z B q : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    continuedCompensatedLocal η u P hs x w z B q=compensatedLocalCorrection η u P x w z B q := by
  rw [continuedCompensatedLocal_eq_difference,
    continuedMarkedLocal_eq_initial η u P hs x w z hx hw hz,
    finiteLocalCorrection_eq_initial η u P hs x w z hx hw hz]
  unfold compensatedLocalCorrection markedLocalCorrection
  ring

def continuedCompensatedRow (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : AngularCharacter) (u : FreeRow)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ) : ℂ :=
  (HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
    HeckeOrigin.continued (rowCharacter S hS.prime u) w*
    PhysicalReciprocal.reciprocal ((SourceRows.targetRow η u).excludePrimes S hS.prime) x)*
  (continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
    ∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z (B P.val) (q P.val))

theorem continuedCompensatedRow_eq_initial (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : AngularCharacter) (u : FreeRow)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    continuedCompensatedRow S hS T hT η u x w z B q=spectralCompensatedRow S T η u.val x w z B q := by
  have hx0 : x≠0 := by intro h; simp only [h,Complex.zero_re] at hx;linarith
  have hx1 : x≠1 := by intro h; simp only [h,Complex.one_re] at hx;linarith
  have hw0 : w≠0 := by intro h; simp only [h,Complex.zero_re] at hw;linarith
  have hw1 : w≠1 := by intro h; simp only [h,Complex.one_re] at hw;linarith
  unfold continuedCompensatedRow
  rw [HeckeOrigin.continued_eq _ hw0 hw1,PhysicalReciprocal.reciprocal_eq_inv _ x (by linarith) (fun _ _=>hx1),
    continuedCorrection_eq_initial (markExclusions S T) (markedSourceExclusions S hS T) η u x w z hx hw hz]
  simp_rw [continuedCompensatedLocal_eq_initial η u _ _ x w z _ _ hx hw hz]
  rw [Finset.prod_attach T (fun P=>compensatedLocalCorrection η u P x w z (B P) (q P)),spectralCompensatedRow_original_L_factorization S hS.prime hS.bad T hT η u x w z B q hx hw hz,
    div_eq_mul_inv]

theorem continuedCompensatedRow_eq_indexed {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let hT : ∀Q∈Finset.univ.image P,Q.val∉S := by
      intro Q hQ
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
      exact hPS i
    continuedCompensatedRow S hS (Finset.univ.image P) hT η u x w z
      (fun Q=>star (η.idealHom Q.val)*(Q.val.absNorm:ℂ)^x)
      (fun Q=>(Q.val.absNorm:ℂ)^(-w))=
      indexedCompensatedHigh η S (fun i=>CompletedGauss.primaryGenerator (P i).val) u.val x w z := by
  dsimp only
  rw [continuedCompensatedRow_eq_initial _ _ _ _ _ _ _ _ _ _ _ hx hw hz,
    indexedCompensatedHigh_eq_spectral η S P hP
      (fun i=>outside_prime_supported S hS.bad (P i) (hPS i)) u.val x w z]


end
end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.finiteLocalCorrection_eq_initial

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCompensatedRow_eq_initial

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCompensatedRow_eq_indexed
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCompensatedRow_eq_indexed
