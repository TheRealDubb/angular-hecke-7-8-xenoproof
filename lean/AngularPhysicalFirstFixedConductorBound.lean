import AngularPhysicalFirstFixedSource
import AngularPhysicalFirstConductorPrefactor

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows.FirstPhysical
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CanonicalQuadraticSieve Prefactor
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSource (scalar inactiveWeight fixedPresentationCost fixedPresentationCost_pos)
open RayFourExpansion IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
variable {η:AngularCharacter}{C D:Ideal O}{hC:Supported C}
  {E:Finset (CommonIndex C D)}{ξ₁ ξ₂:RayCharacter}

theorem FixedPair.scalar_conductors (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (K A₀ B₀ a T M:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)(ha:0<a)(hT:0<T)
    (hl:a*T≤(C.absNorm:ℝ)*Real.exp M*A₀)(hr:a*T≤(D.absNorm:ℝ)*Real.exp M*B₀):
    ‖scalar C D hC E K A₀ B₀‖*T/((C.absNorm:ℝ)*D.absNorm)*
      Real.sqrt ((F.left.modulus.absNorm:ℝ)*F.right.modulus.absNorm)≤
      ‖inactiveWeight C D E‖*(Real.exp M/a)*fixedPresentationCost*K*(η.modulus.absNorm:ℝ)/
        (CenteredMomentRankinRadical.commonRadical C D).absNorm:=by
  exact actual_scalar_conductors C D hC hD E η F.left F.right K A₀ B₀ a T M fixedPresentationCost
    hK hA hB ha hT fixedPresentationCost_pos.le hl hr F.conductor_caps.1 F.conductor_caps.2

end OAI.SevenEighths.Angular.PlainRows.FirstPhysical

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.FixedPair.scalar_conductors
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.FixedPair.scalar_conductors
