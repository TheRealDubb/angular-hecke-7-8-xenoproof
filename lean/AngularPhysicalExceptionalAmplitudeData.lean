import AngularPhysicalAllocatedDetectorAmplitude
import AngularPhysicalExceptionalUniformShell
import OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.ExceptionalAmplitudePair
open PlainRows DetectorAmplitude ExceptionalShell CenteredMomentDivisorAllocation
open CenteredMomentDivisorRaw CenteredMomentDetectorDictionary ConcretePrimeRowBridge
open CenteredMomentExceptionalAmplitudePair (Tests norm_le_of_squared)
local notation "O" => ActualEisensteinCubic.O
universe u
def volume {ι:Type u} [Fintype ι] (s:Data ι):ℝ:=s.X₁*s.X₂*∏i,s.P i

lemma volume_pos {ι:Type u} [Fintype ι] (s:Data ι):0<volume s:=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=>s.P_pos i))

def Admissible {ι:Type u} [Fintype ι] (s:Data ι) (p:Tests)
    (Q:Ideal O) (Z B r:ℝ) (z:O):Prop:=
  (∀i,1≤s.P i) ∧ s.m≠0 ∧ s.A≠0 ∧ z≠0 ∧ goodLambda∣s.m ∧ (2:O)∣s.m ∧
  (AngularRowClosure.rowConductorBound s.η s.m 1 (s.A*z):ℝ)≤Z^B ∧
  ExceptionalRows.FixedInducingRow s.η Q s.m s.A z ∧
  s.W₁=p.profile 0 ∧ s.W₂=p.profile 1 ∧
  Z^r≤s.X₁ ∧ Z^r≤s.X₂ ∧ Z^r≤s.Y₁ ∧ Z^r≤s.Y₂

lemma reduction_cap_identity {ι κ:Type u} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (s:Data ι) (v:Data κ) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2))) (Z r:ℝ) (hZ:1<Z):
    1/(formalReductionFactor D a s.P*formalReductionFactor D b v.P*
      Z^(max (r-Real.logb Z (formalReductionFactor D a s.P)) 0))=
      exceptionalWeight s.toSource v.toSource D a b Z r:=by
  have hz:=zero_lt_one.trans hZ
  unfold exceptionalWeight
  rw [show -Real.logb Z (formalReductionFactor D a s.P)-Real.logb Z (formalReductionFactor D b v.P)-
      max (r-Real.logb Z (formalReductionFactor D a s.P)) 0=
      -(Real.logb Z (formalReductionFactor D a s.P)+Real.logb Z (formalReductionFactor D b v.P)+
        max (r-Real.logb Z (formalReductionFactor D a s.P)) 0) by ring,
    Real.rpow_neg hz.le,Real.rpow_add hz,Real.rpow_add hz,
    Real.rpow_logb hz hZ.ne' (s.reduction_pos D a),Real.rpow_logb hz hZ.ne' (v.reduction_pos D b)]
  exact one_div _

end OAI.SevenEighths.Angular.ExceptionalAmplitudePair

#print axioms OAI.SevenEighths.Angular.ExceptionalAmplitudePair.volume_pos
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ExceptionalAmplitudePair.volume_pos

#print axioms OAI.SevenEighths.Angular.ExceptionalAmplitudePair.reduction_cap_identity
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ExceptionalAmplitudePair.reduction_cap_identity
