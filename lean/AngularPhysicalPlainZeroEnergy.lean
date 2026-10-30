import AngularPhysicalPlainRowDictionary
import AngularPhysicalPlainGlobal
import OAI.NumberTheory.DirichletL.Moments.PlainGlobalEnergy

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.Angular.PlainZeroEnergy
open OAI.SevenEighths.Angular.Dyadic PlainRows PlainGlobalActual
open CenteredMomentPlainGlobalEnergy (radial_bound_on_keep)
open CenteredMomentRadialEligibleEnergy (Radial)
open QuadraticInitialBound ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def zeroRow (η:AngularCharacter) (m A z:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ):ℂ :=
  (Real.sqrt (X₁*X₂):ℂ)⁻¹*(rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)

def zeroEnergy (η:AngularCharacter) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ) (r:Radial):ℝ :=
  ∑'z:O,if r.keep z then ‖zeroRow η m A z t W₁ W₂ X₁ X₂‖^2*
    (r.profile (‖eisEmbedding z‖^2/r.scale)).re else 0

theorem zero_row_norm (η χ:AngularCharacter)(mask A z:O)
    (hrow:∀n,χ.elementCoeff n=CanonicalRowCompletion.rowTwist η.elementHom.toMonoidHom mask 1 (A*z) n)
    (W₁ W₂:ℝ→ℂ)(a b:ℝ)(ha:0<a)(hs₁:Function.support W₁⊆Set.Icc a b)
    (hs₂:Function.support W₂⊆Set.Icc a b)(hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    ‖zeroRow η mask A z t W₁ W₂ X₁ X₂‖=
      ‖polynomial χ false W₁ X₁ 0 t‖*‖polynomial χ false W₂ X₂ 0 t‖:=by
  unfold zeroRow
  rw [rowTwistedSum_eq η χ mask A z hrow,rowTwistedSum_eq η χ mask A z hrow,
    Real.sqrt_mul hX₁.le,Complex.ofReal_mul,mul_inv_rev]
  have he:(Real.sqrt X₂:ℂ)⁻¹*(Real.sqrt X₁:ℂ)⁻¹*
      (twistedIdealSum χ W₁ t X₁*twistedIdealSum χ W₂ t X₂)=
      ((Real.sqrt X₁:ℂ)⁻¹*twistedIdealSum χ W₁ t X₁)*
      ((Real.sqrt X₂:ℂ)⁻¹*twistedIdealSum χ W₂ t X₂):=by ring
  rw [he,norm_mul,plain_height_norm χ W₁ a b ha hs₁ hW₁ t X₁ hX₁,
    plain_height_norm χ W₂ a b ha hs₂ hW₂ t X₂ hX₂]

theorem zero_all_lengths_floor (angularOrder:ℕ) (a b:ℝ)(ha:0<a):
    ∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
    ∀(W₁ W₂:SchwartzMap ℝ ℂ),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b→
    ∀(η:AngularCharacter)(mask A:O)(r:Radial)(χ:O→AngularCharacter),
      (∀z,r.keep z→(χ z).k.natAbs=angularOrder)→
      (∀z,r.keep z→(χ z).k≠0 ∨ (χ z).residue≠1)→
      (∀z,r.keep z→∀n,(χ z).elementCoeff n=
        CanonicalRowCompletion.rowTwist η.elementHom.toMonoidHom mask 1 (A*z) n)→
    ∀(Z m q ρ Cscale t X₁ X₂:ℝ),1≤Z→0≤m→0≤q→0≤Cscale→
      r.scale=Z^m→m+q≤ρ→1≤X₁→1≤X₂→
      (∀z,r.keep z→((χ z).modulus.absNorm:ℝ)≤Cscale*Z^(m+q))→
    zeroEnergy η mask A t W₁ W₂ X₁ X₂ r≤
      C*Cscale^4*diagonalControl r.profile*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*(3+|t|)^8*Z^(m+q+4*ρ):=by
  obtain ⟨S,C,hC,hpoly⟩:=global_polynomial_bound angularOrder a b ha
  refine ⟨S,C^4,pow_pos hC _,?_⟩
  intro W₁ W₂ hs₁ hs₂ η mask A r χ horder hχ hrow Z m q ρ Cscale t X₁ X₂ hZ hm hq hCs hscale hfloor hX₁ hX₂ hmod
  let B₁:=S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁
  let B₂:=S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂
  have hB₁:0≤B₁:=apply_nonneg _ _
  have hB₂:0≤B₂:=apply_nonneg _ _
  let V:=3+|t|
  let Q:=Cscale*Z^(m+q)
  have hQ:0≤Q:=mul_nonneg hCs (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  let B:=C^2*(B₁*B₂)*Q^2*V^4
  have hB:0≤B:=by dsimp [B]; positivity
  have hpoint (z:O)(hz:r.keep z):‖zeroRow η mask A z t W₁ W₂ X₁ X₂‖≤B:=by
    rw [zero_row_norm η (χ z) mask A z (hrow z hz) W₁ W₂ a b ha hs₁ hs₂
      (W₁.smooth ⊤) (W₂.smooth ⊤) t X₁ X₂ (zero_lt_one.trans_le hX₁) (zero_lt_one.trans_le hX₂)]
    have hb₁:=hpoly W₁ hs₁ (χ z) (horder z hz) (hχ z hz) X₁ t hX₁
    have hb₂:=hpoly W₂ hs₂ (χ z) (horder z hz) (hχ z hz) X₂ t hX₂
    have h₁:‖polynomial (χ z) false W₁ X₁ 0 t‖≤C*B₁*Q*V^2:=
      hb₁.trans (by dsimp [V]; gcongr; exact hmod z hz)
    have h₂:‖polynomial (χ z) false W₂ X₂ 0 t‖≤C*B₂*Q*V^2:=
      hb₂.trans (by dsimp [V]; gcongr; exact hmod z hz)
    exact (mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)).trans_eq (by dsimp [B];ring)
  have hb:=radial_bound_on_keep (fun z=>zeroRow η mask A z t W₁ W₂ X₁ X₂) r B hB hpoint
  change zeroEnergy η mask A t W₁ W₂ X₁ X₂ r≤_ at hb
  rw [hscale,max_eq_right (Real.one_le_rpow hZ hm)] at hb
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hp:Z^m*(Z^(m+q))^4≤Z^(m+q+4*ρ):=by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le,←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    norm_num
    linarith
  have hd:=diagonalControl_nonneg r.profile
  apply hb.trans
  calc
    _=(C^4*Cscale^4*diagonalControl r.profile*(B₁*B₂)^2*V^8)*(Z^m*(Z^(m+q))^4):=by
      dsimp [B,Q]; ring
    _≤_:=mul_le_mul_of_nonneg_left hp (by positivity)

#print axioms zero_all_lengths_floor
end SevenEighths.Angular.PlainZeroEnergy
end
end OAI
