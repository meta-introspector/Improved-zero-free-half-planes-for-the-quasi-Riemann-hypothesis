/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroReferenceBounded
Source SHA256: 884ba60e07c53f3483fa806d33c6b0fed16183dfe4fa7d7396d7379b42789c95
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2769




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferenceBounded
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferenceOriginal CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyStageReserveBounded
open CenteredMomentEnergyReferenceProfileBudget CenteredMomentNaturalRowSource
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

theorem balanced_reference_from_zero_low
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤e → 0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤s.width →s.width≤Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁ →0<X₂ →s.width/4≤Real.logb Z (X₁*X₂) →
      s.plainEnergy p t (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) ≤
        C*(K+1)*diagonalControl s.radial.profile*
          (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,saving,L,Cscalar,hd,hxi,hsaving,hCs,hxirho,hL,hLupper,hscalar⟩:=
    exists_bounded_separated_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro S
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,Cref,Dref,Cweight,hCr,hDr,hCw,href⟩:=
    original_from_low d hd a b bΦ d xi saving Mcap Bmask L ha hlo hhi hbΦ hd hxi
      hBmask hL 2 (by norm_num) S
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T Slong 0 n nlong
    Cref Dchild Dref hCr hDc hDr
  refine ⟨J,U,Cweight*Cprofile*Cscalar,by positivity,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hlarge
  have hxiM:xi≤s.width/6:=by linarith only [hxirho, hslo, hrho]
  have hh:=hZ.2 e Q degree K hK hlow s hQ hs hxiM p t X₁ X₂ hX₁ hX₂ hlarge
  have hledger:=hscalar e he Z hZ.1.le s hs (Fin 0) (fun _=>0) (by simpa using hM)
  simp only [Finset.univ_eq_empty,Finset.prod_empty,mul_one] at hledger
  have hp:=hprofile (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t 0 (le_refl 0)
  simp only [add_zero,zero_add,pow_zero,mul_one] at hp
  let A:=Cprofile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*(1+|t|)^J
  let E:=(K+1)*diagonalControl s.radial.profile*A
  have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hA:0≤A:=by dsimp only [A];positivity
  have hE:0≤E:=by dsimp only [E];positivity
  have hdir:K*diagonalControl s.radial.profile*
      ((CenteredMomentEnergyReferenceChild.independentProfiles ha (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t t).control S)^2≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=by
      dsimp only [E]
      nlinarith only [mul_nonneg hdiag hA]
    apply le_trans _ hk
    exact ht
  have hmain:Cref*(sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*
      (K*diagonalControl s.radial.profile*Dchild*(sourceControl T (p.profile 0))^2*
        (1+|t|)^(2*n))≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=by
      dsimp only [E]
      nlinarith only [mul_nonneg hdiag hA]
    apply le_trans _ hk
    convert ht using 1 ; ring
  have herr:Dref*(sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*diagonalControl s.radial.profile≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.2 hdiag
    have hk:diagonalControl s.radial.profile*A≤E:=by
      dsimp only [E]
      nlinarith only [mul_nonneg hK (mul_nonneg hdiag hA)]
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hLpos:0≤L:=by linarith only [hM, hBmask, hxi, hL]
  let P:=Z^(s.width+e)
  let Qmain:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))*Z^(s.width+e)
  let Qerror:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)
  have hP:0≤P:=by dsimp only [P];positivity
  have hQmain:0≤Qmain:=by dsimp only [Qmain];positivity
  have hQerror:0≤Qerror:=by dsimp only [Qerror];positivity
  have htotal:=add_le_add (add_le_add (mul_le_mul_of_nonneg_right hdir hP)
    (mul_le_mul_of_nonneg_right hmain hQmain)) (mul_le_mul_of_nonneg_right herr hQerror)
  apply hh.trans
  have hfirst:=mul_le_mul_of_nonneg_left htotal
    (show 0≤Cweight*(s.puncture.radical.absNorm:ℝ)^d by positivity)
  have hlast:=mul_le_mul_of_nonneg_left hledger (mul_nonneg hCw.le hE)
  refine le_trans ?_ (hlast.trans_eq ?_)
  · dsimp only [P,Qmain,Qerror] at hfirst
    convert hfirst using 1 <;> (try dsimp only [E,A]) <;> ring
  · dsimp only [E,A]
    ring

end SevenEighths.CenteredMomentEnergyZeroReferenceBounded

end

end OAI
end OAIOriginalModule2769

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroReferenceLiveBounded
Source SHA256: 28e602824bbe3fe98041ed86c1c686ee4d31b24904263a7e31a015af311053ef
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2770



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferenceLiveBounded
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferenceBounded CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

theorem balanced_reference_live (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧0<xi ∧xi≤rho/100 ∧Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤e → 0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤s.width →s.width≤Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁ →0<X₂ →
      5*s.width/6≤length Z X₁+length Z X₂ →
      s.plainEnergy p t X₁ X₂=0 ∨
      s.plainEnergy p t (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) ≤
        C*(K+1)*diagonalControl s.radial.profile*
          (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=balanced_reference_from_zero_low
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Z₀,hZ₀,hendpoint⟩:=CenteredMomentEnergyLiveClippingDefect.endpoint_threshold
    b (rho/100) (by positivity)
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop Z₀] with Z hZ hZZ
  refine ⟨hZ.1,?_⟩
  intro e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hlarge
  rcases CenteredMomentEnergyLiveClippingDefect.energy_zero_or_defect s.character s.mask 1 t p
    (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1) X₁ X₂ Z
    s.radial.keep s.radial.profile s.radial.scale hZ.1 hX₁ hX₂ with hz|hdft
  · exact Or.inl hz
  · refine Or.inr (hZ.2 e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ ?_)
    have hh:=hdft.2.trans (hendpoint Z hZZ)
    linarith

end SevenEighths.CenteredMomentEnergyZeroReferenceLiveBounded

end

end OAI
end OAIOriginalModule2770

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroReferencePower
Source SHA256: 715d3d9ead5258abe4cf6b23ab84f743c41583550fab7d603b6ab0686b1af23a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2771




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferencePower
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferenceOriginal CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyReferenceProfileBudget CenteredMomentNaturalRowSource
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

theorem balanced_reference_from_zero_low
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap d Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤s.width →s.width≤Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁ →0<X₂ →s.width/4≤Real.logb Z (X₁*X₂) →
      s.plainEnergy p t (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) ≤
        C*(K+1)*diagonalControl s.radial.profile*
          (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|)^J*Z^(s.width+ε):=by
  obtain ⟨d,xi,saving,L,Cscalar,hd,hxi,hsaving,hCs,hxirho,hL,hscalar⟩:=
    exists_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,?_⟩
  intro S
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,Cref,Dref,Cweight,hCr,hDr,hCw,href⟩:=
    original_from_low d hd a b bΦ d xi saving Mcap Bmask L ha hlo hhi hbΦ hd hxi
      hBmask hL 2 (by norm_num) S
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T Slong 0 n nlong
    Cref Dchild Dref hCr hDc hDr
  refine ⟨J,U,Cweight*Cprofile*Cscalar,by positivity,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Q degree K hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hlarge
  have hxiM:xi≤s.width/6:=by linarith only [hxirho, hslo, hrho]
  have hh:=hZ.2 d Q degree K hK hlow s hQ hs hxiM p t X₁ X₂ hX₁ hX₂ hlarge
  have hledger:=hscalar Z hZ.1.le s hs (Fin 0) (fun _=>0) (by simpa using hM)
  simp only [Finset.univ_eq_empty,Finset.prod_empty,mul_one] at hledger
  have hp:=hprofile (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t 0 (le_refl 0)
  simp only [add_zero,zero_add,pow_zero,mul_one] at hp
  let A:=Cprofile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*(1+|t|)^J
  let E:=(K+1)*diagonalControl s.radial.profile*A
  have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hA:0≤A:=by dsimp only [A];positivity
  have hE:0≤E:=by dsimp only [E];positivity
  have hdir:K*diagonalControl s.radial.profile*
      ((CenteredMomentEnergyReferenceChild.independentProfiles ha (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t t).control S)^2≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=by
      dsimp only [E]
      nlinarith only [mul_nonneg hdiag hA]
    apply le_trans _ hk
    exact ht
  have hmain:Cref*(sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*
      (K*diagonalControl s.radial.profile*Dchild*(sourceControl T (p.profile 0))^2*
        (1+|t|)^(2*n))≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=by
      dsimp only [E]
      nlinarith only [mul_nonneg hdiag hA]
    apply le_trans _ hk
    convert ht using 1 ; ring
  have herr:Dref*(sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*diagonalControl s.radial.profile≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.2 hdiag
    have hk:diagonalControl s.radial.profile*A≤E:=by
      dsimp only [E]
      nlinarith only [mul_nonneg hK (mul_nonneg hdiag hA)]
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hLpos:0≤L:=by linarith only [hM, hBmask, hxi, hL]
  let P:=Z^(s.width+d)
  let Qmain:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))*Z^(s.width+d)
  let Qerror:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)
  have hP:0≤P:=by dsimp only [P];positivity
  have hQmain:0≤Qmain:=by dsimp only [Qmain];positivity
  have hQerror:0≤Qerror:=by dsimp only [Qerror];positivity
  have htotal:=add_le_add (add_le_add (mul_le_mul_of_nonneg_right hdir hP)
    (mul_le_mul_of_nonneg_right hmain hQmain)) (mul_le_mul_of_nonneg_right herr hQerror)
  apply hh.trans
  have hfirst:=mul_le_mul_of_nonneg_left htotal
    (show 0≤Cweight*(s.puncture.radical.absNorm:ℝ)^d by positivity)
  have hlast:=mul_le_mul_of_nonneg_left hledger (mul_nonneg hCw.le hE)
  refine le_trans ?_ (hlast.trans_eq ?_)
  · dsimp only [P,Qmain,Qerror] at hfirst
    convert hfirst using 1 <;> (try dsimp only [E,A]) <;> ring
  · dsimp only [E,A]
    ring

end SevenEighths.CenteredMomentEnergyZeroReferencePower

end

end OAI
end OAIOriginalModule2771

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroReferenceLive
Source SHA256: 4ea4a2583996831a961fe8a2e03861dd220b4fc7dded2eb70d3ea9044249ffce
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2772



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferenceLive
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferencePower CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

theorem balanced_reference_live (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧0<xi ∧xi≤rho/100 ∧Mcap+Bmask+xi≤L ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap d Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤s.width →s.width≤Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁ →0<X₂ →
      5*s.width/6≤length Z X₁+length Z X₂ →
      s.plainEnergy p t X₁ X₂=0 ∨
      s.plainEnergy p t (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) ≤
        C*(K+1)*diagonalControl s.radial.profile*
          (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|)^J*Z^(s.width+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hstage⟩:=balanced_reference_from_zero_low
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Z₀,hZ₀,hendpoint⟩:=CenteredMomentEnergyLiveClippingDefect.endpoint_threshold
    b (rho/100) (by positivity)
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,?_⟩
  intro S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop Z₀] with Z hZ hZZ
  refine ⟨hZ.1,?_⟩
  intro Q degree K hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hlarge
  rcases CenteredMomentEnergyLiveClippingDefect.energy_zero_or_defect s.character s.mask 1 t p
    (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1) X₁ X₂ Z
    s.radial.keep s.radial.profile s.radial.scale hZ.1 hX₁ hX₂ with hz|hdft
  · exact Or.inl hz
  · refine Or.inr (hZ.2 Q degree K hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ ?_)
    have hh:=hdft.2.trans (hendpoint Z hZZ)
    linarith

end SevenEighths.CenteredMomentEnergyZeroReferenceLive

end

end OAI
end OAIOriginalModule2772

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroReferencePhysical
Source SHA256: ecbdeaf8733206f677d7190596d3effbff6c447114bb82102ed40116c3d8a6eb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2773




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferencePhysical
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferenceLive CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
local notation "O"=>HeckeFamily.O
local instance : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _

def balancedInput {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)
    (ha:0<a)(t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):Input (Fin 0):=
  naturalInput s p ha (fun _=>∅) (by simp) (fun _=>s.character) (fun _=>0)
    (fun _=>1) (fun _=>1) (by simp) (by simp) 1 1 (by norm_num)
    (by simp) (by simp) t X₁ X₂ (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
    hX₁ hX₂ (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).1
    (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).2
    (comparison_same_product Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one))

lemma balanced_volume {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)
    (ha:0<a)(t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    CenteredMomentAmplificationChildInput.volume (balancedInput s p ha t X₁ X₂ hX₁ hX₂)=X₁*X₂:=by
  simp only [CenteredMomentAmplificationChildInput.volume,
    balancedInput,naturalInput,completeInput,naturalData,Finset.univ_eq_empty,Finset.prod_empty,mul_one]

theorem actual_positive_source_entry (a b bΦ rho ε Mcap Bmask B εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hB:0≤B)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d xi L:ℝ,0<d ∧0<xi ∧xi≤rho/100 ∧Mcap+Bmask+xi≤L ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧0<Ctail ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap d Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤s.width →s.width≤Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂),X₁*X₂≤Z^B →
      5*s.width/6≤length Z X₁+length Z X₂ →
      let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂;
      s.plainEnergy p t X₁ X₂=0 ∨
      s.plainEnergy p t X₁ X₂≤
        2*diagonalControl s.radial.profile*(
          physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/(X₁*X₂)+
          Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
            Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
          Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
            Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving))+
        2*C*(K+1)*diagonalControl s.radial.profile*
          (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|)^J*Z^(s.width+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hstage⟩:=balanced_reference_live
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=actual_original_reduction
    (ι:=Fin 0) bΦ hbΦ (fun _=>1) a b B εdiag ξ saving (by simp) ha (by linarith) hB hεdiag hξ
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  intro S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,hred] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro Q degree K hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hV hlarge
  rcases hz.2 Q degree K hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hlarge with hzero|hreference
  · exact Or.inl hzero
  · right
    let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂
    have hphysical:=hr.2 inp (p.profile 0) (p.profile 1) rfl rfl
      (p.support 0) (p.support 1) (by simp) s.puncture s.radial s.radial_support
      (by rw [balanced_volume];exact hV) (natural_inverse_scale s B hB)
    change s.plainEnergy p t X₁ X₂≤_+2*s.plainEnergy p t
      (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) at hphysical
    rw [balanced_volume] at hphysical
    dsimp only [inp] at hphysical
    linarith only [hphysical,hreference]

end SevenEighths.CenteredMomentEnergyZeroReferencePhysical

end

end OAI
end OAIOriginalModule2773

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroReferencePhysicalBounded
Source SHA256: 2682777f51dbda4bbe6b810a870fca09af8215236e256c7abcb9f449eca98d19
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2774





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferencePhysicalBounded
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferenceLiveBounded CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
local notation "O"=>HeckeFamily.O
local instance : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _

open CenteredMomentEnergyZeroReferencePhysical

theorem actual_positive_source_entry (a b bΦ rho ε Mcap Bmask B εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hB:0≤B)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d xi L:ℝ,0<d ∧0<xi ∧xi≤rho/100 ∧Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧0<Ctail ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤e → 0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤s.width →s.width≤Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂),X₁*X₂≤Z^B →
      5*s.width/6≤length Z X₁+length Z X₂ →
      let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂;
      s.plainEnergy p t X₁ X₂=0 ∨
      s.plainEnergy p t X₁ X₂≤
        2*diagonalControl s.radial.profile*(
          physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/(X₁*X₂)+
          Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
            Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
          Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
            Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving))+
        2*C*(K+1)*diagonalControl s.radial.profile*
          (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=balanced_reference_live
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=actual_original_reduction
    (ι:=Fin 0) bΦ hbΦ (fun _=>1) a b B εdiag ξ saving (by simp) ha (by linarith) hB hεdiag hξ
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  intro S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,hred] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hV hlarge
  rcases hz.2 e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hlarge with hzero|hreference
  · exact Or.inl hzero
  · right
    let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂
    have hphysical:=hr.2 inp (p.profile 0) (p.profile 1) rfl rfl
      (p.support 0) (p.support 1) (by simp) s.puncture s.radial s.radial_support
      (by rw [balanced_volume];exact hV) (natural_inverse_scale s B hB)
    change s.plainEnergy p t X₁ X₂≤_+2*s.plainEnergy p t
      (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) at hphysical
    rw [balanced_volume] at hphysical
    dsimp only [inp] at hphysical
    linarith only [hphysical,hreference]

end SevenEighths.CenteredMomentEnergyZeroReferencePhysicalBounded

end

end OAI
end OAIOriginalModule2774

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroReflectionSupport
Source SHA256: 43a8597d29fdc12f89d446fc5762f02a6dfbb0b4afaa3b09294491d87b2c91e6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2775





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroReflectionSupport
open HeckeFamily Filter CenteredMomentNaturalPrimitive EisensteinSchwartzPoisson
open CenteredMomentReflectionMass CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentReflectionDeletion CenteredMomentReflectionWeightedEnergy
open CenteredMomentReflectedChoiceEnergy CenteredMomentReflectedTruncation
open CenteredMomentOriginalReflectionApproximation CenteredMomentUniformReflectionApproximation
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDivisors CenteredMomentEnergyReferenceLowWindow
open CenteredMomentEnergyReferenceLowBranchGeometry
local notation "O" => HeckeFamily.O

def naturalDualScale (χ ψ : Character) (X : ℝ)
    (D : Finset (Ideal O)) (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)) : ℝ :=
  (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)

lemma naturalDualScale_pos (χ ψ : Character) (X : ℝ) (hX : 0<X)
    (D : Finset (Ideal O)) (hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
    (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)) :
    0<naturalDualScale χ ψ X D H := by
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hN := subset_product_norm_pos D (fun P hP=>redundantSet_prime _ _ P
    (Finset.mem_powerset.mp hD hP))
  have hH := norm_pos H.val
  unfold naturalDualScale
  positivity

theorem eventually_natural_choice_range (C xi : ℝ) (hC : 0<C) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(χ ψ : Character)(M a : ℝ),
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      (χ.modulus.absNorm:ℝ)≤C*Z^M →
      ∀(D : Finset (Ideal O))(_hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
        (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))
        (hY : 0<naturalDualScale χ ψ (Z^a) D H)(n : ℤ),
      n∈retainedAnnuli (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H) hY → 0≤M-a+xi := by
  filter_upwards [eventually_natural_choice_geometry C xi hC hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro χ ψ M a hcap hmod D hD H hY n hn
  have h := hZ.2 χ ψ M a hcap hmod ((⟨D,hD⟩,H),n) hY hn
  have hz := Real.log_pos hZ.1
  have hm : 0≤(M-a+xi)*Real.log Z := h.2.1.trans h.2.2
  nlinarith

theorem eventually_natural_source_zero (C xi : ℝ) (hC : 0<C) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(χ ψ : Character)(M a : ℝ),
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      (χ.modulus.absNorm:ℝ)≤C*Z^M → M+xi<a →
      (∀(D : Finset (Ideal O))(_hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
        (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))
        (hY : 0<naturalDualScale χ ψ (Z^a) D H),
        retainedAnnuli (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H) hY=∅) ∧
      (∀(D : Finset (Ideal O)),D∈(redundantSet χ.modulus ψ.modulus).powerset →
        ∀(H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))(η : Character)(F : ℝ→ℂ),
        finiteAnnularColumn η F (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H)=0) ∧
      (∀(W : ℝ→ℂ)(t : ℝ),retainedOriginal χ ψ W (Z^a) (Z^(xi/4)) t=0) ∧
      (∀G : 𝓢(ℝ,ℂ),retainedSchwartz χ ψ G (Z^a) (Z^(xi/4))=0) := by
  filter_upwards [eventually_natural_choice_range C xi hC hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro χ ψ M a hcap hmod hfar
  have hempty (D : Finset (Ideal O)) (hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
      (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))
      (hY : 0<naturalDualScale χ ψ (Z^a) D H) :
      retainedAnnuli (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H) hY=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    have h := hZ.2 χ ψ M a hcap hmod D hD H hY n hn
    linarith
  have hcol (D : Finset (Ideal O)) (hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
      (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)) (η : Character)(F : ℝ→ℂ) :
      finiteAnnularColumn η F (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H)=0 := by
    have hy := naturalDualScale_pos χ ψ (Z^a) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _) D hD H
    rw [finiteAnnularColumn,dite_eq_left hy,hempty D hD H hy]
    simp
  refine ⟨hempty,hcol,?_,?_⟩
  · intro W t
    unfold retainedOriginal
    apply Finset.sum_eq_zero
    intro D hD
    have hz : (fun H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)=>
        coefficient ψ ψ.inverse (redundantSet χ.modulus ψ.modulus) D H*
        finiteAnnularColumn χ.inverse
          (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (Z^(xi/4))
          (naturalDualScale χ ψ (Z^a) D H))=fun _=>0 := by
      funext H
      rw [hcol D hD H]
      simp
    change (∑'H : SmoothIdeal (redundantSet χ.modulus ψ.modulus),
      coefficient ψ ψ.inverse (redundantSet χ.modulus ψ.modulus) D H*
      finiteAnnularColumn χ.inverse
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (Z^(xi/4))
        (naturalDualScale χ ψ (Z^a) D H))=0
    rw [hz,tsum_zero]
  · intro G
    unfold retainedSchwartz
    apply Finset.sum_eq_zero
    intro D hD
    have hz : (fun H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)=>
        coefficient ψ ψ.inverse (redundantSet χ.modulus ψ.modulus) D H*
        finiteAnnularColumn χ.inverse (paperRadialFourier G) (Z^(xi/4))
          (naturalDualScale χ ψ (Z^a) D H))=fun _=>0 := by
      funext H
      rw [hcol D hD H]
      simp
    change (∑'H : SmoothIdeal (redundantSet χ.modulus ψ.modulus),
      coefficient ψ ψ.inverse (redundantSet χ.modulus ψ.modulus) D H*
      finiteAnnularColumn χ.inverse (paperRadialFourier G) (Z^(xi/4))
        (naturalDualScale χ ψ (Z^a) D H))=0
    rw [hz,tsum_zero]

lemma deleted_short_length (Z b Xshort Xlong Nshort : ℝ)
    (hZ : 1<Z)(_hb : 0<b)(hshort : 0<Xshort)(hlong : Xshort≤Xlong)
    (hN : 1≤Nshort)(hsupport : 1≤b*Xlong) :
    length Z (Xshort/Nshort)≤Real.logb Z Xlong+Real.logb Z (max 1 b) := by
  have hx : 0<Xlong := hshort.trans_le hlong
  have hn : 0<Nshort := zero_lt_one.trans_le hN
  have hd : Xshort/Nshort≤Xlong := (div_le_self hshort.le hN).trans hlong
  have hlog := Real.logb_le_logb_of_le hZ (div_pos hshort hn) hd
  have hprod : 1≤max 1 b*Xlong := hsupport.trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hx.le)
  have hzero := Real.logb_nonneg hZ hprod
  rw [Real.logb_mul (ne_of_gt (zero_lt_one.trans_le (le_max_left 1 b))) hx.ne'] at hzero
  rw [length_eq_max_log Z _ hZ (div_pos hshort hn)]
  apply max_le
  · linarith
  · exact hlog.trans (le_add_of_nonneg_right (Real.logb_nonneg hZ (le_max_left _ _)))

theorem live_deleted_growth (Z b M xi Xshort Xlong Nshort Nlong : ℝ)
    (hZ : 1<Z)(hb : 0<b)(_hM : 0≤M)(hshort : 0<Xshort)(hlong : Xshort≤Xlong)
    (hNs : 1≤Nshort)(hNl : 1≤Nlong)(hsupport : 1≤b*Xlong)
    (hlive : 0≤M-Real.logb Z (Xlong/Nlong)+xi)
    (x : ℝ)(hx : x∈Set.Icc 0 (max 0 (M-Real.logb Z (Xlong/Nlong)+xi)*Real.log Z)) :
    length Z (Real.exp x)+length Z (Xshort/Nshort)≤
      M+Real.logb Z Nlong+Real.logb Z (max 1 b)+xi := by
  have hxlong : 0<Xlong := hshort.trans_le hlong
  have hnlong : 0<Nlong := zero_lt_one.trans_le hNl
  have hwindow := (reflection_window_length Z _ x hZ (le_max_left _ _) hx).1
  rw [max_eq_right hlive,Real.logb_div hxlong.ne' hnlong.ne'] at hwindow
  have hshortbound := deleted_short_length Z b Xshort Xlong Nshort hZ hb hshort hlong hNs hsupport
  linarith

theorem eventually_endpoint_defect (b epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ Real.logb Z (max 1 b)≤epsilon := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.log (max 1 b)/epsilon))] with Z hZ hz
  refine ⟨hZ,?_⟩
  rw [Real.logb]
  apply (div_le_iff₀ (Real.log_pos hZ)).mpr
  have hh := (div_le_iff₀ hepsilon).mp hz
  nlinarith

theorem actual_deleted_growth {Z Bmask bΦ : ℝ}(s : NaturalState Z Bmask bΦ)
    (b xi Xshort Xlong : ℝ)(hZ : 1<Z)(hb : 0<b)
    (hshort : 0<Xshort)(hlong : Xshort≤Xlong)(hsupport : 1≤b*Xlong)
    (Dshort Dlong : Finset (Ideal O))
    (hDs : Dshort∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hDl : Dlong∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hlive : 0≤s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)
    (x : ℝ)(hx : x∈Set.Icc 0
      (max 0 (s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)*Real.log Z)) :
    length Z (Real.exp x)+length Z (Xshort/((∏P∈Dshort,P).absNorm:ℝ))≤
      s.width+Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)+Real.logb Z (max 1 b)+xi := by
  exact live_deleted_growth Z b s.width xi Xshort Xlong _ _ hZ hb s.width_nonneg
    hshort hlong (divisor_norm s Dshort hDs).1 (divisor_norm s Dlong hDl).1 hsupport hlive x hx

theorem eventually_actual_source_zero (bΦ xi : ℝ)(hbΦ : 0<bΦ)(hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(Bmask : ℝ)(s : NaturalState Z Bmask bΦ)
      (z : O),(effectiveState s).radial.keep z →
      let χ := naturalCharacter s.character z
      ∀ψ : Character,
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      ∀a : ℝ,s.width+xi<a →
      (∀(W : ℝ→ℂ)(t : ℝ),retainedOriginal χ ψ W (Z^a) (Z^(xi/4)) t=0) ∧
      (∀G : 𝓢(ℝ,ℂ),retainedSchwartz χ ψ G (Z^a) (Z^(xi/4))=0) := by
  let C : ℝ := ((fixedConductorFactor:ℝ)+1)*bΦ
  have hC : 0<C := mul_pos (by positivity) hbΦ
  filter_upwards [eventually_natural_source_zero C xi hC hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask s z hz
  dsimp only
  intro ψ hcap a hfar
  have hm : ((naturalCharacter s.character z).modulus.absNorm:ℝ)≤C*Z^s.width := by
    apply (effective_character_cap s hbΦ.le z hz).trans
    dsimp only [C]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hbΦ.le)
      (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
  exact (hZ.2 (naturalCharacter s.character z) ψ s.width a hcap hm hfar).2.2

theorem eventually_actual_deleted_growth (b epsilon : ℝ)(hb : 0<b)(hepsilon : 0<epsilon) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(Bmask bΦ : ℝ)(s : NaturalState Z Bmask bΦ)
      (xi Xshort Xlong : ℝ),0<Xshort → Xshort≤Xlong → 1≤b*Xlong →
      ∀(Dshort Dlong : Finset (Ideal O)),
      Dshort∈(CompletedGauss.primeSupport s.puncture).powerset →
      Dlong∈(CompletedGauss.primeSupport s.puncture).powerset →
      0≤s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi →
      ∀x∈Set.Icc 0 (max 0 (s.width-Real.logb Z
        (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)*Real.log Z),
      length Z (Real.exp x)+length Z (Xshort/((∏P∈Dshort,P).absNorm:ℝ))≤
        s.width+Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)+epsilon+xi := by
  filter_upwards [eventually_endpoint_defect b epsilon hepsilon] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask bΦ s xi Xshort Xlong hshort hlong hsupport Dshort Dlong hDs hDl hlive x hx
  have h := actual_deleted_growth s b xi Xshort Xlong hZ.1 hb hshort hlong hsupport
    Dshort Dlong hDs hDl hlive x hx
  linarith [hZ.2]

theorem eventually_actual_retained_deleted_growth (b bΦ xi epsilon : ℝ)
    (hb : 0<b)(hbΦ : 0<bΦ)(hxi : 0<xi)(hepsilon : 0<epsilon) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(Bmask : ℝ)(s : NaturalState Z Bmask bΦ)
      (z : O),(effectiveState s).radial.keep z →
      let χ := naturalCharacter s.character z
      ∀ψ : Character,
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      ∀(Xshort Xlong : ℝ),0<Xshort → Xshort≤Xlong → 1≤b*Xlong →
      ∀(Dshort Dlong : Finset (Ideal O)),
      Dshort∈(CompletedGauss.primeSupport s.puncture).powerset →
      Dlong∈(CompletedGauss.primeSupport s.puncture).powerset →
      ∀(E : Finset (Ideal O)),E∈(redundantSet χ.modulus ψ.modulus).powerset →
      ∀(H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))
        (hY : 0<naturalDualScale χ ψ (Xlong/((∏P∈Dlong,P).absNorm:ℝ)) E H)(n : ℤ),
      n∈retainedAnnuli (Z^(xi/4))
        (naturalDualScale χ ψ (Xlong/((∏P∈Dlong,P).absNorm:ℝ)) E H) hY →
      ∀x∈Set.Icc 0 (max 0 (s.width-Real.logb Z
        (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)*Real.log Z),
      length Z (Real.exp x)+length Z (Xshort/((∏P∈Dshort,P).absNorm:ℝ))≤
        s.width+Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)+epsilon+xi := by
  let C : ℝ := ((fixedConductorFactor:ℝ)+1)*bΦ
  have hC : 0<C := mul_pos (by positivity) hbΦ
  filter_upwards [eventually_natural_choice_range C xi hC hxi,
    eventually_actual_deleted_growth b epsilon hb hepsilon] with Z hZ hgrowth
  refine ⟨hZ.1,?_⟩
  intro Bmask s z hz
  dsimp only
  intro ψ hcap Xshort Xlong hshort hlong hsupport Dshort Dlong hDs hDl E hE H hY n hn x hx
  have hm : ((naturalCharacter s.character z).modulus.absNorm:ℝ)≤C*Z^s.width := by
    apply (effective_character_cap s hbΦ.le z hz).trans
    dsimp only [C]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hbΦ.le)
      (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
  have hL : 0<Xlong/((∏P∈Dlong,P).absNorm:ℝ) :=
    div_pos (hshort.trans_le hlong) (zero_lt_one.trans_le (divisor_norm s Dlong hDl).1)
  have hexp : Z^(Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ)))=
      Xlong/((∏P∈Dlong,P).absNorm:ℝ) :=
    Real.rpow_logb (zero_lt_one.trans hZ.1) hZ.1.ne' hL
  have hrange := hZ.2 (naturalCharacter s.character z) ψ s.width
    (Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))) hcap hm E hE H
  rw [hexp] at hrange
  have hlive := hrange hY n hn
  exact hgrowth.2 Bmask bΦ s xi Xshort Xlong hshort hlong hsupport
    Dshort Dlong hDs hDl hlive x hx

end SevenEighths.CenteredMomentEnergyZeroReflectionSupport

end

end OAI
end OAIOriginalModule2775

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroGrowthMoments
Source SHA256: 4f5db79000f1b3568605d7cbd45024604c946f54280fa1c6c31835f22ee49515
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2776




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroGrowthMoments
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyZeroGrowth CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentEnergyZeroGrowthChild CenteredMomentEnergyReferenceLowControl
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentScaleSupremum
open CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

theorem reflected_uniform (a b:ℝ)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃D:ℝ,0<D ∧
    ∀(bΦ Bmask L Mcap ε Z:ℝ)(Q:Ideal O)(degree:ℕ)(C:ℝ),0≤C →
    ZeroGrowthAt Q a b bΦ Bmask L Mcap ε Z degree S C → 0≤Bmask →
    ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → s.width≤Mcap →
    ∀(Wshort:𝓢(ℝ,ℂ))(_hsW:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b)
      (j k:Fin 2)(v t X₁ X₂:ℝ),0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) X₂ 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      (C*diagonalControl s.radial.profile*D*(sourceControl T Wshort)^2*
        (1+|t|)^(2*n)*Z^(max s.width (length Z X₁+length Z X₂)+ε))*(1+‖v‖)^(2*n):=by
  obtain ⟨n,T,D,hD,hd⟩:=reflected_child_control a b ha hlo hhi S 0
  refine ⟨n,T,D,hD,?_⟩
  intro bΦ Bmask L Mcap ε Z Q degree C hC hlow hB s hQ hs
    Wshort hsW j k v t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hh:=reflected_from_growth a b bΦ Bmask L Mcap ε Z Q degree S C hlow hB ha hlo hhi
    s hQ hs Wshort hsW j k v t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hb:=hd Wshort hsW j k v t 0 (le_refl 0)
  simp only [add_zero,zero_add,pow_zero,mul_one] at hb
  have hp:0≤C*diagonalControl s.radial.profile:=mul_nonneg hC (by
    unfold diagonalControl
    positivity)
  have hz:0≤Z^(max s.width (length Z X₁+length Z X₂)+ε):=(Real.rpow_pos_of_pos (zero_lt_one.trans_le s.base_ge_one) _).le
  have hmul:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hp) hz
  apply hh.trans
  convert hmul using 1 ; ring

lemma actual_growth_power (Z b M xi epsilon loss Xshort Xlong Nshort Nlong x:ℝ)
    (hZ:1<Z)(hb:0<b)(hM:0≤M)(he:0≤epsilon)(hxi:0≤xi)
    (hshort:0<Xshort)(hlong:Xshort≤Xlong)(hNs:1≤Nshort)(hNl:1≤Nlong)
    (hsupport:1≤b*Xlong)(hdef:Real.logb Z (max 1 b)≤epsilon)
    (hlive:0≤M-Real.logb Z (Xlong/Nlong)+xi)
    (hx:x∈Set.Icc 0 (max 0 (M-Real.logb Z (Xlong/Nlong)+xi)*Real.log Z)):
    Z^(max M (length Z (Real.exp x)+length Z (Xshort/Nshort))+loss)≤
      Nlong*Z^(M+loss+epsilon+xi):=by
  have hg:=live_deleted_growth Z b M xi Xshort Xlong Nshort Nlong
    hZ hb hM hshort hlong hNs hNl hsupport hlive x hx
  have hN:=Real.logb_nonneg hZ hNl
  have hemax:max M (length Z (Real.exp x)+length Z (Xshort/Nshort))≤
      M+Real.logb Z Nlong+epsilon+xi:=max_le (by linarith) (by linarith)
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ.le (show max M (length Z (Real.exp x)+length Z (Xshort/Nshort))+loss≤M+Real.logb Z Nlong+epsilon+xi+loss by linarith)
  apply hp.trans_eq
  rw [show M+Real.logb Z Nlong+epsilon+xi+loss=
    Real.logb Z Nlong+(M+loss+epsilon+xi) by ring,
    Real.rpow_add (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (zero_lt_one.trans_le hNl)]

end SevenEighths.CenteredMomentEnergyZeroGrowthMoments

end

end OAI
end OAIOriginalModule2776

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroGrowthWindow
Source SHA256: 540ee099abfbf2550247d7fa1eafe8df4b05c9fba18e2ef412380910f3a21cc3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2777


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroGrowthWindow
open CenteredMomentFiniteProfileExceptional
open HeckeFamily HeckeDyadic QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyZeroGrowth
open CenteredMomentEnergyZeroGrowthMoments CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyReferenceLowWindow CenteredMomentEnergyReferenceLowBranchGeometry
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

theorem actual_reflected_window (a b:ℝ)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃D:ℝ,0<D ∧
    ∀(bΦ Bmask L Mcap loss Z:ℝ)(Q:Ideal O)(degree:ℕ)(C:ℝ),0≤C→
    ZeroGrowthAt Q a b bΦ Bmask L Mcap loss Z degree S C→0≤Bmask→
    ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤Mcap→
    ∀(Wshort:𝓢(ℝ,ℂ)),Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b→
    ∀xi epsilon Xshort Xlong:ℝ,0≤xi→0≤epsilon→1<Z→
    Real.logb Z (max 1 b)≤epsilon→Mcap+Bmask+epsilon+xi≤L→
    0<Xshort→Xshort≤Xlong→Xshort≤Z^L→1≤b*Xlong→
    ∀Dshort Dlong:Finset (Ideal O),
    Dshort∈(CompletedGauss.primeSupport s.puncture).powerset→
    Dlong∈(CompletedGauss.primeSupport s.puncture).powerset→
    let Nshort:ℝ:=(∏P∈Dshort,P).absNorm;
    let Nlong:ℝ:=(∏P∈Dlong,P).absNorm;
    0≤s.width-Real.logb Z (Xlong/Nlong)+xi→
    ∀(j k:Fin 2)(v t x:ℝ),
    x∈Set.Icc 0 (max 0 (s.width-Real.logb Z (Xlong/Nlong)+xi)*Real.log Z)→
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) (Xshort/Nshort) 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      (C*diagonalControl s.radial.profile*D*(sourceControl T Wshort)^2*
        (1+|t|)^(2*n)*Z^(s.width+loss+epsilon+xi)*Nlong)*(1+‖v‖)^(2*n):=by
  obtain ⟨n,T,D,hD,hu⟩:=reflected_uniform a b ha hlo hhi S
  refine ⟨n,T,D,hD,?_⟩
  intro bΦ Bmask L Mcap loss Z Q degree C hC hgrowth hB s hQ hs Wshort hsW
    xi epsilon Xshort Xlong hxi he hZ hdef hL hshort hlong hshortcap hsupport Dshort Dlong hDs hDl
  dsimp only
  intro hlive j k v t x hx
  obtain ⟨hNs,hNscap⟩:=divisor_norm s Dshort hDs
  obtain ⟨hNl,hNlcap⟩:=divisor_norm s Dlong hDl
  have hpS:0<((∏P∈Dshort,P).absNorm:ℝ):=zero_lt_one.trans_le hNs
  have hpL:0<((∏P∈Dlong,P).absNorm:ℝ):=zero_lt_one.trans_le hNl
  have hlogN:Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)≤Bmask:=
    (Real.logb_le_iff_le_rpow hZ hpL).mpr hNlcap
  have hlen:=live_deleted_growth Z b s.width xi Xshort Xlong _ _ hZ (by linarith)
    s.width_nonneg hshort hlong hNs hNl hsupport hlive x hx
  have hn:=length_nonneg Z (Xshort/((∏P∈Dshort,P).absNorm:ℝ)) hZ
  have hlenx:length Z (Real.exp x)≤L:=by linarith
  have hlogx:Real.logb Z (Real.exp x)≤length Z (Real.exp x):=by
    rw [length_eq_max_log Z _ hZ (Real.exp_pos _)]
    exact le_max_right _ _
  have hxc:Real.exp x≤Z^L:=(Real.logb_le_iff_le_rpow hZ (Real.exp_pos _)).mp (hlogx.trans hlenx)
  have hsc:Xshort/((∏P∈Dshort,P).absNorm:ℝ)≤Z^L:=
    (div_le_self hshort.le hNs).trans hshortcap
  have hh:=hu bΦ Bmask L Mcap loss Z Q degree C hC hgrowth hB s hQ hs Wshort hsW
    j k v t (Real.exp x) (Xshort/((∏P∈Dshort,P).absNorm:ℝ))
    (Real.exp_pos _) (div_pos hshort hpS) hxc hsc
  have hp:=actual_growth_power Z b s.width xi epsilon loss Xshort Xlong _ _ x
    hZ (by linarith) s.width_nonneg he hxi hshort hlong hNs hNl hsupport hdef hlive hx
  have hcoef:0≤C*diagonalControl s.radial.profile*D*(sourceControl T Wshort)^2*(1+|t|)^(2*n):=by
    have hd:=diagonalControl_nonneg s.radial.profile
    positivity
  apply hh.trans
  have hbnd:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hcoef)
    (show 0≤(1+‖v‖)^(2*n) by positivity)
  convert hbnd using 1 ; ring
end SevenEighths.CenteredMomentEnergyZeroGrowthWindow

end

end OAI
end OAIOriginalModule2777

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroGrowthReflection
Source SHA256: 3eee5420a6e48fcd6d2aa3771986d6985af0b75b37dc707983adf1cb683bc0d2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2778



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthReflection
open CenteredMomentNaturalRowSource
open HeckeFamily HeckeDyadic QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyZeroGrowth
open CenteredMomentEnergyZeroGrowthWindow CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyReferenceHomogeneous CenteredMomentFiniteProfileExceptional
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
local notation "O"=>HeckeFamily.O

theorem live_deleted_reflection (a b bΦ epsilon xi defect saving Lreflect:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (hepsilon:0<epsilon)(hxi:0<xi)(hdefect:0<defect)
    (B:ℕ)(hB:2≤B)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(Bmask L Mcap loss:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K→
    ZeroGrowthAt Q a b bΦ Bmask L Mcap loss Z degree S K→0≤Bmask→
    Mcap+Bmask+defect+xi≤L→Mcap+Bmask+defect≤Lreflect→
    ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤Mcap→
    ∀Wlong Wshort:𝓢(ℝ,ℂ),Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b→
    Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b→
    ∀t Xshort Xlong:ℝ,0<Xshort→Xshort≤Xlong→Xshort≤Z^L→1≤b*Xlong→
    ∀Dshort Dlong:Finset (Ideal O),
    Dshort∈(CompletedGauss.primeSupport s.puncture).powerset→
    Dlong∈(CompletedGauss.primeSupport s.puncture).powerset→
    let Ns:ℝ:=(∏P∈Dshort,P).absNorm;
    let Nl:ℝ:=(∏P∈Dlong,P).absNorm;
    let along:=Real.logb Z (Xlong/Nl);
    0≤s.width-along+xi→
    let E:=K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
      (1+|t|)^(2*n)*Z^(s.width+loss+defect+xi)*Nl;
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wlong (Xlong/Nl) 0 t*
      polynomial (naturalCharacter s.character z) false Wshort (Xshort/Ns) 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*
        (1+2*(max 0 (s.width-along+xi)*Real.log Z))*E+
      D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
        radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wshort (Xshort/Ns) 0 t)
          (effectiveState s).radial.keep s.radial.profile s.radial.scale:=by
  obtain ⟨n,T,Dchild,hDc,hchild⟩:=actual_reflected_window a b ha hlo hhi S
  obtain ⟨nlong,Slong,C,D,hC,hD,href⟩:=natural_reference_reflection_homogeneous
    a b bΦ epsilon xi saving Lreflect ha (by linarith) hbΦ hepsilon hxi B n hB
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,?_⟩
  filter_upwards [href,eventually_endpoint_defect b defect hdefect] with Z hZ hendpoint
  refine ⟨hZ.1,?_⟩
  intro Bmask L Mcap loss Q degree K hK hgrowth hBmask hL hLreflect
    s hQ hs Wlong Wshort hsLong hsShort t Xshort Xlong hshort hlong hshortcap hsupport Dshort Dlong hDs hDl
  dsimp only
  intro hlive
  have hz:=zero_lt_one.trans hZ.1
  obtain ⟨hNs,hNscap⟩:=divisor_norm s Dshort hDs
  obtain ⟨hNl,hNlcap⟩:=divisor_norm s Dlong hDl
  have hpS:=zero_lt_one.trans_le hNs
  have hpL:=zero_lt_one.trans_le hNl
  have hxl:=hshort.trans_le hlong
  have hlogs:=deleted_short_length Z b Xlong Xlong 1 hZ.1 (by linarith) hxl le_rfl le_rfl hsupport
  simp only [div_one] at hlogs
  have hn:=length_nonneg Z Xlong hZ.1
  have hlogN:Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)≤Bmask:=
    (Real.logb_le_iff_le_rpow hZ.1 hpL).mpr hNlcap
  have hlength:s.width≤Lreflect+Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ)):=by
    rw [Real.logb_div hxl.ne' hpL.ne']
    linarith [hendpoint.2]
  have hpowL:=Real.rpow_logb hz hZ.1.ne' (div_pos hxl hpL)
  have hpowS:=Real.rpow_logb hz hZ.1.ne' (div_pos hshort hpS)
  let E:=K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
      (1+|t|)^(2*n)*Z^(s.width+loss+defect+xi)*((∏P∈Dlong,P).absNorm:ℝ)
  have hh:=hZ.2 Bmask s Wlong Wshort hsLong hsShort (Fin 0) ∅
    (fun _=>∅) (fun _ _=>0) (fun _=>1) t
    (Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ)))
    (Real.logb Z (Xshort/((∏P∈Dshort,P).absNorm:ℝ))) E hlength
  simp only [Finset.prod_empty,mul_one,hpowL,hpowS] at hh
  apply hh
  · dsimp [E]
    have hd:=diagonalControl_nonneg s.radial.profile
    positivity
  · intro v j k x hx
    exact hchild bΦ Bmask L Mcap loss Z Q degree K hK hgrowth hBmask s hQ hs Wshort hsShort
      xi defect Xshort Xlong hxi.le hdefect.le hZ.1 hendpoint.2 hL
      hshort hlong hshortcap hsupport Dshort Dlong hDs hDl hlive j k v t x hx
end SevenEighths.CenteredMomentEnergyZeroGrowthReflection

end

end OAI
end OAIOriginalModule2778

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroGrowthBounds
Source SHA256: a6e0553b2bdf0b4bf2f95936151da48b18f2fd4f0fe6b7f61adf921dd74aa769
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2779



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthBounds
open HeckeFamily HeckeDyadic QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDivisors CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyZeroReferenceError CenteredMomentOriginalRadialComparison
open CenteredMomentNaturalRowSource
open CenteredMomentAllocatedNaturalRadial
local notation "O"=>HeckeFamily.O

lemma actual_window_cap (Z b Bmask bΦ Mcap defect xi L Xlong:ℝ)
    (hZ:1<Z)(hb:0<b)(hx:0<Xlong)(hsupport:1≤b*Xlong)
    (hdefect:Real.logb Z (max 1 b)≤defect)
    (hL:Mcap+Bmask+defect+xi≤L)(hL0:0≤L)
    (s:NaturalState Z Bmask bΦ)(hs:s.width≤Mcap)
    (Dlong:Finset (Ideal O))(hDl:Dlong∈(CompletedGauss.primeSupport s.puncture).powerset):
    max 0 (s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)≤L:=by
  obtain ⟨hn,hncap⟩:=divisor_norm s Dlong hDl
  have hnp:0<((∏P∈Dlong,P).absNorm:ℝ):=zero_lt_one.trans_le hn
  have hlogN:Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)≤Bmask:=
    (Real.logb_le_iff_le_rpow hZ hnp).mpr hncap
  have hlow:=deleted_short_length Z b Xlong Xlong 1 hZ hb hx le_rfl le_rfl hsupport
  simp only [div_one] at hlow
  have hnon:=CenteredMomentEnergyBands.length_nonneg Z Xlong hZ
  apply max_le hL0
  rw [Real.logb_div hx.ne' hnp.ne']
  linarith

theorem actual_deleted_short_mass (b:ℝ):
    ∃C:ℝ,0<C ∧ ∀(Z Bmask bΦ L:ℝ)(s:NaturalState Z Bmask bΦ)
      (W:𝓢(ℝ,ℂ)),Function.support (W:ℝ→ℂ)⊆Set.Iic b→
      ∀t X:ℝ,0<X→X≤Z^L→
      ∀D:Finset (Ideal O),D∈(CompletedGauss.primeSupport s.puncture).powerset→
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W
        (X/((∏P∈D,P).absNorm:ℝ)) 0 t)
        (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
        C*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)^2*
          diagonalControl s.radial.profile*max 1 s.radial.scale*Z^L:=by
  obtain ⟨C,hC,hbound⟩:=short_energy_bound b
  refine ⟨C,hC,?_⟩
  intro Z Bmask bΦ L s W hW t X hX hcap D hD
  obtain ⟨hn,_⟩:=divisor_norm s D hD
  have hnp:0<((∏P∈D,P).absNorm:ℝ):=zero_lt_one.trans_le hn
  have hh:=hbound W hW (naturalCharacter s.character) t
    (X/((∏P∈D,P).absNorm:ℝ)) s.radial.scale s.radial.profile
    (effectiveState s).radial.keep (div_pos hX hnp) s.radial.scale_pos s.radial.nonneg
  apply hh.trans
  apply mul_le_mul_of_nonneg_left ((div_le_self hX.le hn).trans hcap)
  exact mul_nonneg (mul_nonneg (mul_nonneg hC.le (sq_nonneg _))
    (diagonalControl_nonneg _)) (le_max_of_le_left zero_le_one)

end SevenEighths.CenteredMomentEnergyZeroGrowthBounds

end

end OAI
end OAIOriginalModule2779

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroGrowthBounded
Source SHA256: 05b36f928d8da81147df0a0b1f8f92f2c48982079db240dc6458148246fdefb4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2780


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthBounded
open CenteredMomentNaturalRowSource
open HeckeFamily HeckeDyadic QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyZeroGrowth
open CenteredMomentEnergyZeroGrowthWindow CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyReferenceHomogeneous CenteredMomentFiniteProfileExceptional
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
local notation "O"=>HeckeFamily.O

open CenteredMomentEnergyZeroGrowthReflection CenteredMomentEnergyZeroGrowthBounds

theorem live_deleted_bounded (a b bΦ epsilon xi defect saving Lreflect:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (hepsilon:0<epsilon)(hxi:0<xi)(hdefect:0<defect)
    (B:ℕ)(hB:2≤B)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(Bmask L Mcap loss:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K→
    ZeroGrowthAt Q a b bΦ Bmask L Mcap loss Z degree S K→0≤Bmask→
    Mcap+Bmask+defect+xi≤L→Mcap+Bmask+defect≤Lreflect→
    ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤Mcap→
    ∀Wlong Wshort:𝓢(ℝ,ℂ),Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b→
    Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b→
    ∀t Xshort Xlong:ℝ,0<Xshort→Xshort≤Xlong→Xshort≤Z^L→1≤b*Xlong→
    ∀Dshort Dlong:Finset (Ideal O),
    Dshort∈(CompletedGauss.primeSupport s.puncture).powerset→
    Dlong∈(CompletedGauss.primeSupport s.puncture).powerset→
    let Ns:ℝ:=(∏P∈Dshort,P).absNorm;
    let Nl:ℝ:=(∏P∈Dlong,P).absNorm;
    let along:=Real.logb Z (Xlong/Nl);
    0≤s.width-along+xi→
    let E:=K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
      (1+|t|)^(2*n)*Z^(s.width+loss+defect+xi)*Nl;
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wlong (Xlong/Nl) 0 t*
      polynomial (naturalCharacter s.character z) false Wshort (Xshort/Ns) 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*
        (1+2*(L*Real.log Z))*E+
      D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
        ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) Wshort)^2*
          diagonalControl s.radial.profile*max 1 s.radial.scale*Z^L :=by
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=live_deleted_reflection
    a b bΦ epsilon xi defect saving Lreflect ha hlo hhi hbΦ hepsilon hxi hdefect B hB S
  obtain ⟨Cshort,hCs,hshortmass⟩:=actual_deleted_short_mass b
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D*Cshort,hC,mul_pos hD hCs,?_⟩
  filter_upwards [href,eventually_endpoint_defect b defect hdefect] with Z hZ hendpoint
  refine ⟨hZ.1,?_⟩
  intro Bmask L Mcap loss Q degree K hK hgrowth hBmask hL hLreflect
    s hQ hs Wlong Wshort hsLong hsShort t Xshort Xlong hshort hlong hshortcap hsupport Dshort Dlong hDs hDl
  dsimp only
  intro hlive
  have hh:=hZ.2 Bmask L Mcap loss Q degree K hK hgrowth hBmask hL hLreflect
    s hQ hs Wlong Wshort hsLong hsShort t Xshort Xlong hshort hlong hshortcap hsupport Dshort Dlong hDs hDl hlive
  have hL0:0≤L:=by linarith [s.width_nonneg]
  have hw:=actual_window_cap Z b Bmask bΦ Mcap defect xi L Xlong hZ.1 (by linarith)
    (hshort.trans_le hlong) hsupport hendpoint.2 hL hL0 s hs Dlong hDl
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hwindow:1+2*(max 0 (s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)*Real.log Z)
      ≤1+2*(L*Real.log Z):=by nlinarith
  have hmass:=hshortmass Z Bmask bΦ L s Wshort (fun x hx=>(hsShort hx).2)
    t Xshort hshort hshortcap Dshort hDs
  have hd:=diagonalControl_nonneg s.radial.profile
  have hN:0≤((∏P∈Dlong,P).absNorm:ℝ):=Nat.cast_nonneg _
  have hZ0:0<Z:=zero_lt_one.trans hZ.1
  apply hh.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left hwindow (by positivity)
    · positivity
  · have he:=mul_le_mul_of_nonneg_left hmass
      (show 0≤D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving) by positivity)
    convert he using 1 ; ring

end SevenEighths.CenteredMomentEnergyZeroGrowthBounded

end

end OAI
end OAIOriginalModule2780

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroRetainedError
Source SHA256: e8072035aa11a39c3bd35424c14a6ec8efc0751a9f5e1b3b2bf1e688e3a1c3ae
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2781





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroRetainedError
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentNaturalPrimitive CenteredMomentUniformReflectionApproximation
open CenteredMomentEnergyZeroReflectionSupport CenteredMomentOriginalRadialComparison
open CenteredMomentRadialPolynomialEnergy CenteredMomentEnergyState
open CenteredMomentEnergyReferenceState CenteredMomentAllocatedNaturalRadial
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional CenteredMomentLattice
open CenteredMomentEnergyReferenceHomogeneous CenteredMomentEnergyReferenceReflection
local notation "O" => HeckeFamily.O

theorem finite_original_error (xi saving Cscale epsilon : ℝ)
    (hxi : 0<xi)(hscale : 0<Cscale)(hepsilon : 0<epsilon) :
    ∃H : Finset (ℕ×ℕ),∃C Z₀ : ℝ,0<C ∧ 1<Z₀ ∧
      ∀{ι : Type}[Fintype ι],∀χ : ι→Character,(∀i,(χ i).residue≠1) →
      ∃ψ : ι→Character,
        (∀i,FiniteFourier.IsPrimitiveOnIdeals (ψ i).residue ∧ (ψ i).residue≠1 ∧
          (ψ i).modulus.absNorm*(redundantIdeal (χ i).modulus (ψ i).modulus).absNorm≤(χ i).modulus.absNorm) ∧
      ∀(G : ι→𝓢(ℝ,ℂ))(P : ι→ℂ)(Z M along Src Rcap : ℝ),Z₀≤Z →
        M+xi<along → 0<Src → 1≤Rcap →
        (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤Src) →
        (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^M) →
        (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
        (∀i,retainedSchwartz (χ i) (ψ i) (G i) (Z^along) (Z^(xi/4))=0) ∧
        (∑i,‖polynomial (χ i) false (G i) (Z^along) 0 0*P i‖^2)≤
          C*Rcap^(2*epsilon)*Src^2*Z^(-2*saving)*(∑i,‖P i‖^2) := by
  obtain ⟨H,C,hC,happrox⟩:=CenteredMomentUniformOriginalEnergy.actual_original_energy_to_retained
    (xi/2) saving 0 Cscale epsilon (by positivity) hscale hepsilon
  obtain ⟨Z₁,hZ₁⟩:=eventually_atTop.mp (eventually_natural_source_zero Cscale xi hscale hxi)
  refine ⟨H,C,max 2 Z₁,hC,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro ι _ χ hχ
  obtain ⟨ψ,hψ,henergy⟩:=happrox χ hχ
  refine ⟨ψ,hψ,?_⟩
  intro G P Z M along Src Rcap hZ₀ hfar hSrc hR hGS hmod hcap
  have hZ:=hZ₁ Z ((le_max_right _ _).trans hZ₀)
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hzero(i:ι):retainedSchwartz (χ i) (ψ i) (G i) (Z^along) (Z^(xi/4))=0:=
    (hZ.2 (χ i) (ψ i) M along (hψ i).2.2 (hmod i) hfar).2.2.2 (G i)
  have hsource(i:ι):((χ i).modulus.absNorm:ℝ)≤Cscale*Z^(0:ℝ)*Z^along:=by
    simp only [Real.rpow_zero,mul_one]
    exact (hmod i).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith)) hscale.le)
  have hh:=henergy G (fun _=>Z^along) P Src Z Rcap hSrc hZ.1.le hR
    (fun _=>Real.rpow_pos_of_pos hz _) hGS hcap hsource
  rw [show (xi/2)/2=xi/4 by ring] at hh
  simp only [hzero,zero_mul,norm_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero,
    mul_zero,zero_add] at hh
  exact ⟨hzero,hh⟩

theorem radial_original_error (xi saving Cscale epsilon : ℝ)
    (hxi : 0<xi)(hscale : 0<Cscale)(hepsilon : 0<epsilon) :
    ∃H : Finset (ℕ×ℕ),∃C Z₀ : ℝ,0<C ∧ 1<Z₀ ∧
      ∀(G:O→𝓢(ℝ,ℂ))(χ:O→Character)(P:O→ℂ)(omega:O→ℝ)
        (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K Pbound:ℝ)(Wshort:ℝ→ℂ)
        (c d Z M along Xshort Src Rcap:ℝ),
      Z₀≤Z → 0<K → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      (∀z,‖P z‖≤Pbound) → (∀z,keep z → (χ z).residue≠1) →
      0≤d → Function.support Wshort⊆Set.Icc c d → 0<Xshort →
      M+xi<along → 0<Src → 1≤Rcap →
      (∀z,keep z → H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G z)≤Src) →
      (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤Rcap) →
      radialEnergy (fun z=>polynomial (χ z) false (G z) (Z^along) 0 0*
        polynomial (χ z) false Wshort Xshort 0 (omega z)*P z) keep Φ K≤
        C*Rcap^(2*epsilon)*Src^2*Z^(-2*saving)*
          radialEnergy (fun z=>polynomial (χ z) false Wshort Xshort 0 (omega z)*P z) keep Φ K := by
  obtain ⟨H,C,Z₀,hC,hZ₀,hfinite⟩:=finite_original_error xi saving Cscale epsilon hxi hscale hepsilon
  refine ⟨H,C,Z₀,hC,hZ₀,?_⟩
  intro G χ P omega keep Φ K Pbound Wshort c d Z M along Xshort Src Rcap
    hZ hK hΦ hP hχ hd hshort hXshort hfar hSrc hR hGS hmod hcap
  have hz:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hshortsum:=single_radial_summable χ P omega Wshort c d Xshort Pbound hd hXshort
    hshort hP keep Φ K hK
  unfold radialEnergy
  apply Real.tsum_le_of_sum_le (fun z=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
  intro rows
  let S:=rows.filter keep
  have hmem(z:↥S):keep (z:O):=(Finset.mem_filter.mp z.property).2
  obtain ⟨ψ,hψ,hf⟩:=hfinite (fun z:↥S=>χ z) (fun z=>hχ z (hmem z))
  let Q(z:↥S):ℂ:=
    (polynomial (χ z) false Wshort Xshort 0 (omega z)*P z)*
      (Real.sqrt ((Φ (‖eisEmbedding z‖^2/K)).re):ℂ)
  have hh:=(hf (fun z:↥S=>G z) Q Z M along Src Rcap hZ hfar hSrc hR
    (fun z=>hGS z (hmem z)) (fun z=>hmod z (hmem z)) (fun z=>hcap z (hmem z))).2
  simp only [Q,←mul_assoc] at hh
  rw [finite_weighted rows keep
      (fun z=>polynomial (χ z) false (G z) (Z^along) 0 0*
        polynomial (χ z) false Wshort Xshort 0 (omega z)*P z) Φ K hΦ,
    finite_weighted rows keep
      (fun z=>polynomial (χ z) false Wshort Xshort 0 (omega z)*P z) Φ K hΦ] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (hshortsum.sum_le_tsum rows (fun z _=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl))
    (by positivity))

theorem natural_polynomials_summable {Z Bmask bΦ:ℝ}(state:NaturalState Z Bmask bΦ)
    (Wlong Wshort:𝓢(ℝ,ℂ))(a b Xlong Xshort t omega:ℝ)
    (hb:0≤b)(hXlong:0<Xlong)(hXshort:0<Xshort)
    (hsLong:Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b)
    (hsShort:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b):
    Summable (fun z:O=>if (effectiveState state).radial.keep z then
      ‖polynomial (naturalCharacter state.character z) false Wlong Xlong 0 t*
        polynomial (naturalCharacter state.character z) false Wshort Xshort 0 omega‖^2*
        (state.radial.profile (‖eisEmbedding z‖^2/state.radial.scale)).re else 0) ∧
    Summable (fun z:O=>if (effectiveState state).radial.keep z then
      ‖polynomial (naturalCharacter state.character z) false Wshort Xshort 0 omega‖^2*
        (state.radial.profile (‖eisEmbedding z‖^2/state.radial.scale)).re else 0):=by
  constructor
  · simpa only [mul_one] using pair_radial_summable (naturalCharacter state.character)
      (fun _=>1) (fun _=>t) (fun _=>omega) Wlong Wshort a b a b Xlong Xshort 1
      hb hb hXlong hXshort hsLong hsShort (fun _=>by simp)
      (effectiveState state).radial.keep state.radial.profile state.radial.scale state.radial.scale_pos
  · simpa only [mul_one] using single_radial_summable (naturalCharacter state.character)
      (fun _=>1) (fun _=>omega) Wshort a b Xshort 1 hb hXshort hsShort (fun _=>by simp)
      (effectiveState state).radial.keep state.radial.profile state.radial.scale state.radial.scale_pos

theorem natural_original_error (a b bΦ epsilon xi saving:ℝ)
    (ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi):
    ∃n:ℕ,∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Bmask:ℝ)(state:NaturalState Z Bmask bΦ)(Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(t omega along Xshort:ℝ),0<Xshort → state.width+xi<along →
      radialEnergy (fun z=>polynomial (naturalCharacter state.character z) false Wlong
          (Z^along) 0 t*polynomial (naturalCharacter state.character z) false Wshort Xshort 0 omega)
        (effectiveState state).radial.keep state.radial.profile state.radial.scale≤
      C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^state.width))^(2*epsilon)*
        (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖t‖)^(2*n)*Z^(-2*saving)*
        radialEnergy (fun z=>polynomial (naturalCharacter state.character z) false Wshort Xshort 0 omega)
          (effectiveState state).radial.keep state.radial.profile state.radial.scale:=by
  obtain ⟨H,C,Z₀,hC,hZ₀,hr⟩:=radial_original_error xi saving
    ((fixedConductorFactor:ℝ)*bΦ) epsilon hxi (mul_pos conductorFactor_pos hbΦ) hepsilon
  obtain ⟨n,T,Ct,hCt,hprofile⟩:=normPowerProfile_source_control a b ha H
  let S:=T∪{(0,0)}
  have hS:(0,0)∈S:=by simp [S]
  refine ⟨n,S,C*Ct^2,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop Z₀] with Z hZ
  have hz:1<Z:=hZ₀.trans_le hZ
  refine ⟨hz,?_⟩
  intro Bmask state Wlong Wshort hsLong hsShort t omega along Xshort hXshort hfar
  by_cases hzero:sourceControl S Wlong=0
  · have hw:=sourceControl_zero S hS Wlong hzero
    subst Wlong
    simp [polynomial,summand,radialEnergy]
  have hpos:0<sourceControl S Wlong:=lt_of_le_of_ne (sourceControl_nonneg S Wlong) (Ne.symm hzero)
  let G:=normPowerProfile Wlong a b ha hsLong (Wlong.smooth ⊤) t
  let Src:=Ct*(S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)*(1+‖t‖)^n
  have hSrc:0<Src:=mul_pos (mul_pos hCt hpos) (by positivity)
  have hcontrol:sourceControl T Wlong≤sourceControl S Wlong:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left:T⊆T∪{(0,0)})) Wlong
  have hnorm:H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G≤Src:=
    (hprofile Wlong hsLong t).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcontrol hCt.le) (by positivity))
  have hh:=hr (fun _=>G) (naturalCharacter state.character) (fun _=>1) (fun _=>omega)
    (effectiveState state).radial.keep state.radial.profile state.radial.scale 1
    Wshort a b Z state.width along Xshort Src
    (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^state.width)) hZ state.radial.scale_pos
    state.radial.nonneg (fun _=>by simp) (effective_character_nonprincipal state)
    hb hsShort hXshort hfar hSrc (le_max_left _ _) (fun _ _=>hnorm)
    (effective_character_cap state hbΦ.le)
    (fun z hz=>(effective_character_cap state hbΦ.le z hz).trans (le_max_right _ _))
  have hG:(G:ℝ→ℂ)=normPowerProfile Wlong a b ha hsLong (Wlong.smooth ⊤) t:=rfl
  simp only [hG,CenteredMomentNaturalMaskedFloor.twist_polynomial _ Wlong a b ha hsLong t,mul_one] at hh
  apply hh.trans_eq
  dsimp only [Src]
  rw [show (1+‖t‖)^(2*n)=((1+‖t‖)^n)^2 by rw [Nat.mul_comm 2 n,pow_mul]]
  ring

theorem short_radial_mass (χ:O→Character)(W:𝓢(ℝ,ℂ))(a b X:ℝ)
    (hb:0≤b)(hX:0<X)(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
    (omega:O→ℝ)(keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K):
    radialEnergy (fun z=>polynomial (χ z) false W X 0 (omega z)) keep Φ K≤
      (128*max 1 b)^2*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)^2*
        QuadraticInitialBound.diagonalControl Φ*max 1 K*X:=by
  let A:=((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)
  let V:=(128*max 1 b*A)^2*X
  have hV:0≤V:=by dsimp [V];positivity
  have hp(z:O):‖polynomial (χ z) false W X 0 (omega z)‖^2≤V:=by
    have hh:=pow_le_pow_left₀ (norm_nonneg _)
      (CenteredMomentOriginalReflectionErrorMass.plain_polynomial_bound (χ z) W b A X (omega z)
        (apply_nonneg _ _) hX (SchwartzMap.norm_le_seminorm ℝ W) (fun y hy=>(hs hy).2)) 2
    simpa only [mul_pow,Real.sq_sqrt hX.le,V] using hh
  have hsum:=single_radial_summable χ (fun _=>1) omega W a b X 1 hb hX hs
    (fun _=>by simp) keep Φ K hK
  simp only [mul_one] at hsum
  have hweight:=CenteredMomentAbsoluteEnergy.radial_norm_summable Φ K hK
  have hh:radialEnergy (fun z=>polynomial (χ z) false W X 0 (omega z)) keep Φ K≤
      (∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖)*V:=by
    rw [←tsum_mul_right]
    apply hsum.tsum_le_tsum _ (hweight.mul_right V)
    intro z
    split_ifs
    · exact (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (sq_nonneg _)).trans
        ((mul_le_mul_of_nonneg_right (hp z) (norm_nonneg _)).trans_eq (mul_comm _ _))
    · exact mul_nonneg (norm_nonneg _) hV
  apply (hh.trans (mul_le_mul_of_nonneg_right
    (CenteredMomentAbsoluteEnergy.radial_weight_lattice_bound_all Φ K hK) hV)).trans_eq
  dsimp [V,A]
  ring

theorem natural_original_error_mass (a b bΦ epsilon xi saving:ℝ)
    (ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi):
    ∃n:ℕ,∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Bmask:ℝ)(state:NaturalState Z Bmask bΦ)(Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(t omega along Xshort:ℝ),0<Xshort → state.width+xi<along →
      radialEnergy (fun z=>polynomial (naturalCharacter state.character z) false Wlong
          (Z^along) 0 t*polynomial (naturalCharacter state.character z) false Wshort Xshort 0 omega)
        state.radial.keep state.radial.profile state.radial.scale≤
      C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^state.width))^(2*epsilon)*
        (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*
        ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) Wshort)^2*(1+‖t‖)^(2*n)*Z^(-2*saving)*
        QuadraticInitialBound.diagonalControl state.radial.profile*max 1 state.radial.scale*Xshort:=by
  obtain ⟨n,S,C,hC,h⟩:=natural_original_error a b bΦ epsilon xi saving ha hb hbΦ hepsilon hxi
  refine ⟨n,S,C*(128*max 1 b)^2,by positivity,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask state Wlong Wshort hsLong hsShort t omega along Xshort hXshort hfar
  have hh:=hZ.2 Bmask state Wlong Wshort hsLong hsShort t omega along Xshort hXshort hfar
  have he(f:O→ℂ):radialEnergy f (effectiveState state).radial.keep
      state.radial.profile state.radial.scale=
      radialEnergy f state.radial.keep state.radial.profile state.radial.scale:=
    radialEnergy_effective state.radial f
  rw [he,he] at hh
  have hm:=short_radial_mass (naturalCharacter state.character) Wshort a b Xshort
    hb hXshort hsShort (fun _=>omega) state.radial.keep state.radial.profile
    state.radial.scale state.radial.scale_pos
  have hz:0<Z:=zero_lt_one.trans hZ.1
  apply (hh.trans (mul_le_mul_of_nonneg_left hm (by positivity))).trans_eq
  ring

end SevenEighths.CenteredMomentEnergyZeroRetainedError

end

end OAI
end OAIOriginalModule2781

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroGrowthOriginal
Source SHA256: 1fea2597f9544591eb9c41eb088ed380efec3d32027cf911b97f3a2c55f4e11a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2782






namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthOriginal
open HeckeFamily HeckeDyadic QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyZeroGrowth
open CenteredMomentEnergyZeroGrowthBounded CenteredMomentEnergyZeroRetainedError
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyReferenceDeletionEnergy CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentInductionEnergy CenteredMomentEnergyLiveClippingDefect CenteredMomentRetainedEnergy
local notation "O"=>HeckeFamily.O

def swapProfiles {a b:ℝ}(p:Profiles a b):Profiles a b where
  profile := ![p.profile 1,p.profile 0]
  support := by
    intro i
    fin_cases i
    · simpa using p.support 1
    · simpa using p.support 0

lemma swapProfiles_control {a b:ℝ}(p:Profiles a b)(U:Finset (ℕ×ℕ)):
    (swapProfiles p).control U=p.control U:=by
  simp [swapProfiles,Profiles.control,mul_comm]

lemma plainEnergy_swap {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)
    (p:Profiles a b)(t X₁ X₂:ℝ):
    s.plainEnergy (swapProfiles p) t X₂ X₁=s.plainEnergy p t X₁ X₂:=by
  unfold NaturalState.plainEnergy energy
  apply tsum_congr
  intro z
  have hh:positiveSlotRow s.character s.mask 1 z ((swapProfiles p).profile 0)
      ((swapProfiles p).profile 1) (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1)
      t X₂ X₁=positiveSlotRow s.character s.mask 1 z (p.profile 0) (p.profile 1)
      (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1) t X₁ X₂:=by
    simp only [swapProfiles,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    unfold positiveSlotRow
    rw [mul_comm X₂ X₁]
    ring
  rw [hh]

theorem original_from_growth (a b bΦ epsilon xi defect saving Lreflect:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (hepsilon:0<epsilon)(hxi:0<xi)(hdefect:0<defect)(S:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(Bmask L Mcap loss:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K→
      ZeroGrowthAt Q a b bΦ Bmask L Mcap loss Z degree S K→0≤Bmask→
      Mcap+Bmask+defect+xi≤L→Mcap+Bmask+defect≤Lreflect→
      ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤Mcap→
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁→0<X₂→X₁≤Z^L→X₂≤Z^L→
      s.plainEnergy p t X₁ X₂≤
        C*(K+1)*diagonalControl s.radial.profile*(p.control U)^2*(1+|t|)^J*
          (s.puncture.radical.absNorm:ℝ)^epsilon*
          ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon*
            (1+2*(L*Real.log Z))*Z^(s.width+loss+defect+xi)+
           (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
            Z^(-2*saving)*max 1 s.radial.scale*Z^L):=by
  obtain ⟨n,T,Dchild,hDc,nlive,Slive,Clive,Dlive,hCl,hDl,hlive⟩:=
    live_deleted_bounded a b bΦ epsilon xi defect saving Lreflect
      ha hlo hhi hbΦ hepsilon hxi hdefect 2 (by norm_num) S
  obtain ⟨ndead,Sdead,Cdead,hCd,hdead⟩:=natural_original_error_mass
    a b bΦ epsilon xi saving ha (by linarith only [hlo, hhi]) hbΦ hepsilon hxi
  obtain ⟨Cweight,hCw,hweight⟩:=original_energy_weighted_deletion (α:=Fin 0)
    (fun _=>0) (fun _=>0) (fun _=>le_refl 0) epsilon hepsilon
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T (Slive∪Sdead)
    0 n (nlive+ndead) Clive Dchild (Dlive+Cdead) hCl hDc (by positivity)
  refine ⟨J,U,Cweight*Cprofile,by positivity,?_⟩
  filter_upwards [hlive,hdead] with Z hZ hZd
  refine ⟨hZ.1,?_⟩
  intro Bmask L Mcap loss Q degree K hK hgrowth hBmask hL hLreflect s hQ hs
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hL0:0≤L:=by linarith only [s.width_nonneg, hs, hBmask, hdefect, hxi, hL]
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hd:=diagonalControl_nonneg s.radial.profile
  let Rcap:=max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width)
  let Pmain:=Rcap^epsilon*(1+2*(L*Real.log Z))*Z^(s.width+loss+defect+xi)
  let Perror:=Rcap^(2*epsilon)*Z^(-2*saving)*max 1 s.radial.scale*Z^L
  have hPm:0≤Pmain:=by dsimp only [Pmain,Rcap];positivity
  have hPe:0≤Perror:=by dsimp only [Perror,Rcap];positivity
  have hordered (p:Profiles a b)(t Xshort Xlong:ℝ)(hXs:0<Xshort)(horder:Xshort≤Xlong)
      (hcap:Xshort≤Z^L)(hsupport:1≤b*Xlong):
      s.plainEnergy p t Xshort Xlong≤
        Cweight*Cprofile*(K+1)*diagonalControl s.radial.profile*(p.control U)^2*(1+|t|)^J*
          (s.puncture.radical.absNorm:ℝ)^epsilon*(Pmain+Perror):=by
    have hXl:0<Xlong:=hXs.trans_le horder
    have hp:=hprofile (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t 0 (le_refl 0)
    simp only [add_zero,zero_add,pow_zero,mul_one] at hp
    let A:=Cprofile*(p.control U)^2*(1+|t|)^J
    let E:=(K+1)*diagonalControl s.radial.profile*A
    have hA:0≤A:=by dsimp only [A];positivity
    have hE:0≤E:=by dsimp only [E];positivity
    have hSl:sourceControl Slive (p.profile 1)≤sourceControl (Slive∪Sdead) (p.profile 1):=
      control_mono Finset.subset_union_left _
    have hSd:sourceControl Sdead (p.profile 1)≤sourceControl (Slive∪Sdead) (p.profile 1):=
      control_mono Finset.subset_union_right _
    have hSl0:=sourceControl_nonneg Slive (p.profile 1)
    have hSd0:=sourceControl_nonneg Sdead (p.profile 1)
    have hheight:1≤1+‖t‖:=le_add_of_nonneg_right (norm_nonneg _)
    have hnL:(1+‖t‖)^(2*nlive)≤(1+‖t‖)^(2*(nlive+ndead)):=
      pow_le_pow_right₀ hheight (by omega)
    have hnD:(1+‖t‖)^(2*ndead)≤(1+‖t‖)^(2*(nlive+ndead)):=
      pow_le_pow_right₀ hheight (by omega)
    have hmain:Clive*(sourceControl Slive (p.profile 1))^2*(1+‖t‖)^(2*nlive)*
        (K*diagonalControl s.radial.profile*Dchild*(sourceControl T (p.profile 0))^2*(1+|t|)^(2*n))≤E:=by
      have hh:Clive*Dchild*(sourceControl Slive (p.profile 1))^2*(sourceControl T (p.profile 0))^2*
          (1+‖t‖)^(2*nlive)*(1+|t|)^(2*n)≤A:=by
        apply le_trans _ hp.2.1
        gcongr
      have hh':=mul_le_mul_of_nonneg_left hh (mul_nonneg hK hd)
      have he:K*diagonalControl s.radial.profile*A≤E:=by
        dsimp only [E]
        nlinarith only [mul_nonneg hd hA]
      apply le_trans _ he
      convert hh' using 1; ring
    have herrLive:Dlive*(sourceControl Slive (p.profile 1))^2*(1+‖t‖)^(2*nlive)*
        ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*diagonalControl s.radial.profile≤E:=by
      have hh:Dlive*(sourceControl Slive (p.profile 1))^2*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*(1+‖t‖)^(2*nlive)≤A:=by
        apply le_trans _ hp.2.2
        gcongr
        exact le_add_of_nonneg_right hCd.le
      have hh':=mul_le_mul_of_nonneg_left hh hd
      have he:diagonalControl s.radial.profile*A≤E:=by
        dsimp only [E]
        nlinarith only [mul_nonneg hK (mul_nonneg hd hA)]
      apply le_trans _ he
      convert hh' using 1; ring
    have herrDead:Cdead*(sourceControl Sdead (p.profile 1))^2*
        ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*(1+‖t‖)^(2*ndead)*
        diagonalControl s.radial.profile≤E:=by
      have hh:Cdead*(sourceControl Sdead (p.profile 1))^2*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*(1+‖t‖)^(2*ndead)≤A:=by
        apply le_trans _ hp.2.2
        gcongr
        exact le_add_of_nonneg_left hDl.le
      have hh':=mul_le_mul_of_nonneg_left hh hd
      have he:diagonalControl s.radial.profile*A≤E:=by
        dsimp only [E]
        nlinarith only [mul_nonneg hK (mul_nonneg hd hA)]
      apply le_trans _ he
      convert hh' using 1; ring
    have hw:=hweight Z Bmask bΦ a b s (p.profile 0) (p.profile 1) ha (by linarith only [hlo, hhi])
      (p.support 0) (p.support 1) (fun _=>∅) (fun _ _=>0) (fun _=>1)
      t Xshort Xlong (E*(Pmain+Perror)) 1
    have hresult:s.plainEnergy p t Xshort Xlong≤
        Cweight*(s.puncture.radical.absNorm:ℝ)^epsilon*(E*(Pmain+Perror)):=by
      apply hw
      · simp
      · simp
      · simp
      · simp
      · exact hXs
      · exact hXl
      · exact mul_nonneg hE (add_nonneg hPm hPe)
      · norm_num
      · intro Ds hDs Dl hDl' I hI
        obtain ⟨hNs,_⟩:=divisor_norm s Ds hDs
        obtain ⟨hNl,_⟩:=divisor_norm s Dl hDl'
        have hpS:0<((∏P∈Ds,P).absNorm:ℝ):=zero_lt_one.trans_le hNs
        have hpL:0<((∏P∈Dl,P).absNorm:ℝ):=zero_lt_one.trans_le hNl
        have heffective (f:O→ℂ):radialEnergy f (effectiveState s).radial.keep
            s.radial.profile s.radial.scale=radialEnergy f s.radial.keep s.radial.profile s.radial.scale:=
          radialEnergy_effective s.radial f
        simp only [Finset.univ_eq_empty,Finset.empty_sdiff,Finset.prod_empty,mul_one,Real.rpow_one]
        rw [show (fun z:O=>polynomial (naturalCharacter s.character z) false (p.profile 0)
              (Xshort/((∏P∈Ds,P).absNorm:ℝ)) 0 t*
            polynomial (naturalCharacter s.character z) false (p.profile 1)
              (Xlong/((∏P∈Dl,P).absNorm:ℝ)) 0 t)=
            (fun z:O=>polynomial (naturalCharacter s.character z) false (p.profile 1)
              (Xlong/((∏P∈Dl,P).absNorm:ℝ)) 0 t*
            polynomial (naturalCharacter s.character z) false (p.profile 0)
              (Xshort/((∏P∈Ds,P).absNorm:ℝ)) 0 t) by funext z;exact mul_comm _ _]
        by_cases hl:0≤s.width-Real.logb Z (Xlong/((∏P∈Dl,P).absNorm:ℝ))+xi
        · have hh:=hZ.2 Bmask L Mcap loss Q degree K hK hgrowth hBmask hL hLreflect
            s hQ hs (p.profile 1) (p.profile 0) (p.support 1) (p.support 0)
            t Xshort Xlong hXs horder hcap hsupport Ds Dl hDs hDl' hl
          have hb:=add_le_add
            (mul_le_mul_of_nonneg_right hmain (mul_nonneg hPm hpL.le))
            (mul_le_mul_of_nonneg_right herrLive hPe)
          have hc:E*Pmain*((∏P∈Dl,P).absNorm:ℝ)+E*Perror≤
              E*(Pmain+Perror)*((∏P∈Dl,P).absNorm:ℝ):=by
            calc
              _ ≤ E*Pmain*((∏P∈Dl,P).absNorm:ℝ)+(E*Perror)*((∏P∈Dl,P).absNorm:ℝ) :=
                add_le_add le_rfl (le_mul_of_one_le_right (mul_nonneg hE hPe) hNl)
              _ = _ := by ring
          apply hh.trans
          calc
            _ ≤ E*Pmain*((∏P∈Dl,P).absNorm:ℝ)+E*Perror := by
              convert hb using 1 <;> dsimp only [Pmain,Perror,Rcap] <;> ring
            _ ≤ _ := hc
        · have hfar:s.width+xi<Real.logb Z (Xlong/((∏P∈Dl,P).absNorm:ℝ)):=by linarith only [hl]
          have hh:=hZd.2 Bmask s (p.profile 1) (p.profile 0) (p.support 1) (p.support 0)
            t t (Real.logb Z (Xlong/((∏P∈Dl,P).absNorm:ℝ)))
            (Xshort/((∏P∈Ds,P).absNorm:ℝ)) (div_pos hXs hpS) hfar
          rw [Real.rpow_logb hz hZ.1.ne' (div_pos hXl hpL)] at hh
          rw [heffective]
          have hshortcap:Xshort/((∏P∈Ds,P).absNorm:ℝ)≤Z^L:=
            (div_le_self hXs.le hNs).trans hcap
          have hb:=mul_le_mul_of_nonneg_right herrDead
            (show 0≤Rcap^(2*epsilon)*Z^(-2*saving)*max 1 s.radial.scale*
              (Xshort/((∏P∈Ds,P).absNorm:ℝ)) by positivity)
          have hc:E*(Rcap^(2*epsilon)*Z^(-2*saving)*max 1 s.radial.scale*
              (Xshort/((∏P∈Ds,P).absNorm:ℝ)))≤E*Perror:=by
            dsimp only [Perror]
            gcongr
          have hf:E*Perror≤E*(Pmain+Perror)*((∏P∈Dl,P).absNorm:ℝ):=by
            exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hPm) hE).trans
              (le_mul_of_one_le_right (mul_nonneg hE (add_nonneg hPm hPe)) hNl)
          apply hh.trans
          calc
            _ ≤ E*(Rcap^(2*epsilon)*Z^(-2*saving)*max 1 s.radial.scale*
                (Xshort/((∏P∈Ds,P).absNorm:ℝ))) := by
              convert hb using 1; dsimp only [Rcap,sourceControl]; ring
            _ ≤ E*Perror := hc
            _ ≤ _ := hf
    apply hresult.trans_eq
    dsimp only [E,A]
    ring
  intro p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  by_cases hzero:s.plainEnergy p t X₁ X₂=0
  · rw [hzero]
    positivity
  · obtain ⟨z,hz,hrow⟩:=energy_support_witness s.character s.mask 1 t
      (p.profile 0) (p.profile 1) (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1)
      X₁ X₂ s.radial.keep s.radial.profile s.radial.scale hzero
    obtain ⟨hs₁,hs₂⟩:=positiveSlotRow_profiles_scales s.character s.mask 1 z p
      (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1) t X₁ X₂ hX₁ hX₂ hrow
    by_cases horder:X₁≤X₂
    · exact hordered p t X₁ X₂ hX₁ horder hc₁ hs₂
    · have hh:=hordered (swapProfiles p) t X₂ X₁ hX₂ (le_of_not_ge horder) hc₂ hs₁
      simpa only [plainEnergy_swap,swapProfiles_control] using hh

end SevenEighths.CenteredMomentEnergyZeroGrowthOriginal

end

end OAI
end OAIOriginalModule2782

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroGrowthConclusion
Source SHA256: 3064fea1e3b937590a97064b50d09341309052641cd96c460bae140ddc70d2b5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2783




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthConclusion
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyZeroGrowth CenteredMomentFiniteProfileExceptional
open CenteredMomentInductionEnergy QuadraticInitialBound
local notation "O" => HeckeFamily.O

lemma profile_control_mono {a b:ℝ}(p:Profiles a b)
    {S T:Finset (ℕ×ℕ)}(hST:S⊆T):p.control S≤p.control T:=by
  unfold Profiles.control
  exact mul_le_mul
    (Seminorm.le_def.mp (Finset.sup_mono hST) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono hST) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

lemma zeroGrowth_mono (Q:Ideal O)(a b bΦ Bmask L L' M M' ε ε' Z:ℝ)
    (degree degree':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hL:L'≤L)(hM:M'≤M)(hε:ε≤ε')(hdegree:degree≤degree')
    (hST:S⊆T)(hC:0≤C)(hCC:C≤C')
    (h:ZeroGrowthAt Q a b bΦ Bmask L M ε Z degree S C):
    ZeroGrowthAt Q a b bΦ Bmask L' M' ε' Z degree' T C':=by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hscale:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le s.base_ge_one hL
  have hh:=h s hQ (hs.trans hM) p t X₁ X₂ hX₁ hX₂
    (hc₁.trans hscale) (hc₂.trans hscale)
  have hC' : 0≤C' := hC.trans hCC
  have hp:=profile_control_mono p hST
  have hpn:=p.control_nonneg S
  have hpt:=p.control_nonneg T
  have hd:=diagonalControl_nonneg s.radial.profile
  have hheight:(1+‖t‖)^degree≤(1+‖t‖)^degree':=
    pow_le_pow_right₀ (by linarith [norm_nonneg t]) hdegree
  have hpower:Z^(max s.width (length Z X₁+length Z X₂)+ε)≤
      Z^(max s.width (length Z X₁+length Z X₂)+ε'):=
    Real.rpow_le_rpow_of_exponent_le s.base_ge_one (by linarith)
  have hZ : 0≤Z := zero_le_one.trans s.base_ge_one
  have hfront:C*diagonalControl s.radial.profile*(p.control S)^2*(1+‖t‖)^degree≤
      C'*diagonalControl s.radial.profile*(p.control T)^2*(1+‖t‖)^degree':=by
    apply mul_le_mul _ hheight (by positivity) (by positivity)
    apply mul_le_mul _ ((sq_le_sq₀ hpn hpt).mpr hp) (sq_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_right hCC hd
  exact hh.trans (mul_le_mul hfront hpower (Real.rpow_nonneg hZ _) (by positivity))

lemma zeroAt_mono (Q:Ideal O)(a b bΦ Bmask L L' M M' ε ε' Z:ℝ)
    (degree degree':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hL:L'≤L)(hM:M'≤M)(hε:ε≤ε')(hdegree:degree≤degree')
    (hST:S⊆T)(hC:0≤C)(hCC:C≤C')
    (h:ZeroAt Q a b bΦ Bmask L M ε Z degree S C):
    ZeroAt Q a b bΦ Bmask L' M' ε' Z degree' T C':=by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hscale:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le s.base_ge_one hL
  have hh:=h s hQ (hs.trans hM) p t X₁ X₂ hX₁ hX₂
    (hc₁.trans hscale) (hc₂.trans hscale)
  have hC' : 0≤C' := hC.trans hCC
  have hp:=profile_control_mono p hST
  have hpn:=p.control_nonneg S
  have hpt:=p.control_nonneg T
  have hd:=diagonalControl_nonneg s.radial.profile
  have hheight:(1+‖t‖)^degree≤(1+‖t‖)^degree':=
    pow_le_pow_right₀ (by linarith [norm_nonneg t]) hdegree
  have hpower:Z^(s.width+ε)≤Z^(s.width+ε'):=
    Real.rpow_le_rpow_of_exponent_le s.base_ge_one (by linarith)
  have hZ : 0≤Z := zero_le_one.trans s.base_ge_one
  have hfront:C*diagonalControl s.radial.profile*(p.control S)^2*(1+‖t‖)^degree≤
      C'*diagonalControl s.radial.profile*(p.control T)^2*(1+‖t‖)^degree':=by
    apply mul_le_mul _ hheight (by positivity) (by positivity)
    apply mul_le_mul _ ((sq_le_sq₀ hpn hpt).mpr hp) (sq_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_right hCC hd
  exact hh.trans (mul_le_mul hfront hpower (Real.rpow_nonneg hZ _) (by positivity))

theorem zero_from_same_width_growth (a b bΦ ε Mcap Bmask Loriginal:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d L:ℝ,0<d ∧ 0<L ∧ Loriginal≤L ∧
      ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K→
        ZeroGrowthAt Q a b bΦ Bmask L Mcap d Z degree S K→
        ZeroAt Q a b bΦ Bmask Loriginal Mcap ε Z J U (C*(K+1)):=by
  obtain ⟨d,L,saving,Cledger,hd,hL,hsaving,hCledger,hLoriginal,hroom,hledger⟩:=
    CenteredMomentEnergyZeroGrowthReserve.exists_growth_reserve
      ε Mcap Bmask bΦ Loriginal hε hM hB
  refine ⟨d,L,hd,hL,hLoriginal,?_⟩
  intro S
  obtain ⟨J,U,Csource,hCsource,hsource⟩:=
    CenteredMomentEnergyZeroGrowthOriginal.original_from_growth
      a b bΦ d d d saving L ha hlo hhi hbΦ hd hd hd S
  refine ⟨J,U,Csource*Cledger,mul_pos hCsource hCledger,?_⟩
  filter_upwards [hsource] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Q degree K hK hgrowth s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hscale:Z^Loriginal≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ.1.le hLoriginal
  have hh:=hZ.2 Bmask L Mcap d Q degree K hK hgrowth hB hroom
    (by linarith) s hQ hs p t X₁ X₂ hX₁ hX₂ (hc₁.trans hscale) (hc₂.trans hscale)
  have hl:=hledger Z hZ.1.le s hs
  have hfront:0≤Csource*(K+1)*diagonalControl s.radial.profile*
      (p.control U)^2*(1+|t|)^J:=by
    have hd:=diagonalControl_nonneg s.radial.profile
    positivity
  calc
    _≤Csource*(K+1)*diagonalControl s.radial.profile*(p.control U)^2*(1+|t|)^J*
        (Cledger*Z^(s.width+ε)):=by
      apply hh.trans
      convert mul_le_mul_of_nonneg_left hl hfront using 1 ; ring
    _=_:=by rw [Real.norm_eq_abs];ring

end SevenEighths.CenteredMomentEnergyZeroGrowthConclusion

end

end OAI
end OAIOriginalModule2783

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroGrowthContourBounded
Source SHA256: 0465cdc54fd85344a6217c263404faf3a2fe9eb1d55ebe7099b2d3905e073cbd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2784



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthContourBounded
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyZeroGrowth CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalRowSource QuadraticInitialBound
local notation "O"=>HeckeFamily.O

private lemma ledger_loss_mono (Z d ell A B P w:ℝ)(hZ:1≤Z)(hd:0≤d)(hell:0≤ell)
    (hA:0≤A)(hB:0≤B)(hP:0≤P):
    P*(A*Z^(w+ell+d+d)+B)≤Z^ell*(P*(A*Z^(w+d+d+d)+B)):=by
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hp:1≤Z^ell:=Real.one_le_rpow hZ hell
  have hm:Z^(w+ell+d+d)≤Z^ell*Z^(w+d+d+d):=by
    rw [←Real.rpow_add hz]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  calc
    _≤P*(A*(Z^ell*Z^(w+d+d+d))+Z^ell*B):=by
      apply mul_le_mul_of_nonneg_left _ hP
      exact add_le_add (mul_le_mul_of_nonneg_left hm hA)
        (le_mul_of_one_le_left hB hp)
    _=_:=by ring

theorem bounded_growth_reserve (ε Mcap Bmask bΦ Loriginal:ℝ)
    (hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d L saving C:ℝ,0<d ∧ d≤1 ∧ 0<L ∧ 0<saving ∧ 0<C ∧
      L=max Loriginal (Mcap+Bmask+2*d)+1 ∧ Loriginal≤L ∧
      Mcap+Bmask+d+d≤L ∧
      ∀Z:ℝ,1≤Z→∀s:NaturalState Z Bmask bΦ,s.width≤Mcap→
      (s.puncture.radical.absNorm:ℝ)^d*
        ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(L*Real.log Z))*Z^(s.width+d+d+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*
          Z^(-2*saving)*max 1 s.radial.scale*Z^L)≤C*Z^(s.width+ε):=by
  let d:=min 1 (ε/(8*(Bmask+Mcap+4)))
  let L:=max Loriginal (Mcap+Bmask+2*d)+1
  let saving:=L+Bmask*d+2*Mcap*d+1
  have hd:0<d:=lt_min (by norm_num) (by positivity)
  have hd1:d≤1:=min_le_left _ _
  have hdε:d*(Bmask+Mcap+4)≤ε/8:=by
    have hh: d≤ε/(8*(Bmask+Mcap+4)):=min_le_right _ _
    have he: d*(8*(Bmask+Mcap+4))≤ε:=
      (le_div_iff₀ (by positivity)).mp hh
    linarith
  have hL:0<L:=by dsimp only [L];linarith [le_max_right Loriginal (Mcap+Bmask+2*d)]
  have hs:0<saving:=by dsimp [saving];positivity
  have hmain:d*(Bmask+Mcap+1)+d+d+d≤ε:=by linarith
  have herr:Bmask*d+Mcap*(2*d)-2*saving+L≤ε:=by
    dsimp only [saving]
    nlinarith [mul_nonneg hB hd.le,mul_nonneg hM hd.le]
  obtain ⟨C,hC,hbound⟩:=CenteredMomentEnergyZeroGrowthReserve.ledger_bound
    Mcap Bmask bΦ L d d d d saving ε hM hB hL.le hd hmain herr
  refine ⟨d,L,saving,C,hd,hd1,hL,hs,hC,rfl,?_,?_,hbound⟩
  · dsimp only [L];linarith [le_max_left Loriginal (Mcap+Bmask+2*d)]
  · dsimp only [L];linarith [le_max_right Loriginal (Mcap+Bmask+2*d)]

theorem zero_from_growth_additional_loss_bounded (a b bΦ ε Mcap Bmask Loriginal:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d L:ℝ,0<d ∧ d≤1 ∧ 0<L ∧ Loriginal≤L ∧
      L=max Loriginal (Mcap+Bmask+2*d)+1 ∧
      L≤max Loriginal (Mcap+Bmask+2)+1 ∧
      ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(ell:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤ell→0≤K→
        ZeroGrowthAt Q a b bΦ Bmask L Mcap ell Z degree S K→
        ZeroAt Q a b bΦ Bmask Loriginal Mcap (ell+ε) Z J U (C*(K+1)):=by
  obtain ⟨d,L,saving,Cledger,hd,hd1,hL,hsaving,hCledger,hLexact,hLoriginal,hroom,hledger⟩:=
    bounded_growth_reserve
      ε Mcap Bmask bΦ Loriginal hε hM hB
  refine ⟨d,L,hd,hd1,hL,hLoriginal,hLexact,?_,?_⟩
  · rw [hLexact]
    gcongr
    linarith only [hd1]
  intro S
  obtain ⟨J,U,Csource,hCsource,hsource⟩:=
    CenteredMomentEnergyZeroGrowthOriginal.original_from_growth
      a b bΦ d d d saving L ha hlo hhi hbΦ hd hd hd S
  refine ⟨J,U,Csource*Cledger,mul_pos hCsource hCledger,?_⟩
  filter_upwards [hsource] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ell Q degree K hell hK hgrowth s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hscale:Z^Loriginal≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ.1.le hLoriginal
  have hh:=hZ.2 Bmask L Mcap ell Q degree K hK hgrowth hB hroom
    (by linarith) s hQ hs p t X₁ X₂ hX₁ hX₂ (hc₁.trans hscale) (hc₂.trans hscale)
  let Rcap:=max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width)
  let A:=Rcap^d*(1+2*(L*Real.log Z))
  let B:=Rcap^(2*d)*Z^(-2*saving)*max 1 s.radial.scale*Z^L
  let P:=(s.puncture.radical.absNorm:ℝ)^d
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hA:0≤A:=by dsimp [A,Rcap];positivity
  have hBb:0≤B:=by dsimp [B,Rcap];positivity
  have hP:0≤P:=by dsimp [P];positivity
  have hb:=ledger_loss_mono Z d ell A B P s.width hZ.1.le hd.le hell hA hBb hP
  have hl:=mul_le_mul_of_nonneg_left (hledger Z hZ.1.le s hs) (Real.rpow_nonneg hz.le ell)
  have htotal:P*(A*Z^(s.width+ell+d+d)+B)≤Cledger*Z^(s.width+(ell+ε)):=by
    apply hb.trans
    calc
      _≤Z^ell*(Cledger*Z^(s.width+ε)):=hl
      _=Cledger*(Z^ell*Z^(s.width+ε)):=by ring
      _=Cledger*Z^(s.width+(ell+ε)):=by rw [←Real.rpow_add hz];congr 2;ring
  have hfront:0≤Csource*(K+1)*diagonalControl s.radial.profile*
      (p.control U)^2*(1+|t|)^J:=by
    have hd:=diagonalControl_nonneg s.radial.profile
    positivity
  calc
    _≤Csource*(K+1)*diagonalControl s.radial.profile*(p.control U)^2*(1+|t|)^J*
        (Cledger*Z^(s.width+(ell+ε))):=by
      apply hh.trans
      convert mul_le_mul_of_nonneg_left htotal hfront using 1 ; dsimp only [P,A,B,Rcap] ; ring
    _=_:=by rw [Real.norm_eq_abs];ring

end SevenEighths.CenteredMomentEnergyZeroGrowthContourBounded

end

end OAI
end OAIOriginalModule2784

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroUnbalancedDeletedGeometry
Source SHA256: 0a445572d6a12896bd6585432ab0eb94650cae23704fc861362a62ace0065d96
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2785


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyZeroUnbalancedDeletedGeometry
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceDivisors CenteredMomentEnergyZeroReferenceGeometry
local notation "O" => HeckeFamily.O

theorem actual_deleted_gates {Z Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ)
    (hZ : 1 < Z) (hB : 0 ≤ Bmask) (Mcap L X₁ X₂ xi : ℝ)
    (hwidth : s.width ≤ Mcap) (hL : Mcap + Bmask + xi ≤ L)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hxi : 0 ≤ xi) (hxiM : xi ≤ s.width / 6)
    (hshort : Real.logb Z X₁ ≤ s.width / 4) (hlong : 1 ≤ X₂)
    (D₁ D₂ : Finset (Ideal O))
    (hD₁ : D₁ ∈ (CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂ : D₂ ∈ (CompletedGauss.primeSupport s.puncture).powerset) :
    let short := Real.logb Z X₁ - Real.logb Z ((∏ P ∈ D₁, P).absNorm : ℝ)
    let along := Real.logb Z X₂ - Real.logb Z ((∏ P ∈ D₂, P).absNorm : ℝ)
    Z ^ short = X₁ / ((∏ P ∈ D₁, P).absNorm : ℝ) ∧
    Z ^ along = X₂ / ((∏ P ∈ D₂, P).absNorm : ℝ) ∧
    short ≤ s.width / 4 ∧ short ≤ L ∧ -Bmask ≤ along ∧
    s.width ≤ Mcap + Bmask + along ∧ max 0 (s.width - along + xi) ≤ L ∧
    ((along ≤ L ∧ length Z (Z ^ short) + length Z (Z ^ along) ≤ 5 * s.width / 6) ∨
      (0 < along ∧ max 0 (s.width - along + xi) + length Z (Z ^ short) ≤ 5 * s.width / 6)) := by
  dsimp only
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  obtain ⟨hn₁, _⟩ := divisor_norm s D₁ hD₁
  obtain ⟨hn₂, hc₂⟩ := divisor_norm s D₂ hD₂
  have hl₁ := Real.logb_nonneg hZ hn₁
  have hlonglog := Real.logb_nonneg hZ hlong
  have hu₂ : Real.logb Z ((∏ P ∈ D₂, P).absNorm : ℝ) ≤ Bmask :=
    (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hn₂)).mpr hc₂
  have hM := s.width_nonneg
  have hL0 : 0 ≤ L := by linarith
  refine ⟨divided_scale_power Z X₁ _ hZ hX₁ (zero_lt_one.trans_le hn₁),
    divided_scale_power Z X₂ _ hZ hX₂ (zero_lt_one.trans_le hn₂),
    by linarith, by linarith, by linarith, by linarith,
    max_le hL0 (by linarith), ?_⟩
  have hlen (v : ℝ) : length Z (Z ^ v) = max 0 v := by
    rcases le_total 0 v with hv | hv
    · rw [length, max_eq_right (Real.one_le_rpow hZ.le hv),
        Real.logb_rpow hZ0 hZ.ne', max_eq_right hv]
    · rw [length, max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos hZ.le hv),
        Real.logb_one, max_eq_left hv]
  simp only [hlen]
  rcases low_or_reflected s.width
    (Real.logb Z X₁ - Real.logb Z ((∏ P ∈ D₁, P).absNorm : ℝ))
    (Real.logb Z X₂ - Real.logb Z ((∏ P ∈ D₂, P).absNorm : ℝ))
    xi hM (by linarith) hxi hxiM with hd | hr
  · refine Or.inl ⟨?_, hd⟩
    have hh₁ := le_max_right (0 : ℝ)
      (Real.logb Z X₂ - Real.logb Z ((∏ P ∈ D₂, P).absNorm : ℝ))
    have hh₂ := le_max_left (0 : ℝ)
      (Real.logb Z X₁ - Real.logb Z ((∏ P ∈ D₁, P).absNorm : ℝ))
    linarith
  · exact Or.inr hr

end SevenEighths.CenteredMomentEnergyZeroUnbalancedDeletedGeometry

end

end OAI
end OAIOriginalModule2785

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroUnbalancedOriginalDeleted
Source SHA256: 79151591392c0553ed704eac8ebe6035dcd8be52ba1f580a53fb07a85d26e688
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2786




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroUnbalancedOriginalDeleted
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyZeroReferenceChild
open CenteredMomentEnergyZeroUnbalancedDeletedGeometry CenteredMomentEnergyZeroReferenceReflection
open CenteredMomentEnergyZeroReferenceError CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentScaleSupremum
local notation "O"=>HeckeFamily.O

theorem deleted_from_low (a b bΦ epsilon xi saving Mcap Bmask L:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (hBmask:0≤Bmask)(hL:Mcap+Bmask+xi≤L)(B:ℕ)(hB:2≤B)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(ε:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap ε Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q →s.width≤Mcap →xi≤s.width/6 →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀t X₁ X₂:ℝ,0<X₁ →0<X₂ →Real.logb Z X₁≤s.width/4 →1≤X₂ →
      ∀D₁∈(CompletedGauss.primeSupport s.puncture).powerset,
      ∀D₂∈(CompletedGauss.primeSupport s.puncture).powerset,
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁
          (X₁/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
        polynomial (naturalCharacter s.character z) false W₂
          (X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t)
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
            (1+|t|)^(2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*Z^(s.width/4)):=by
  obtain ⟨Ce,hCe,he⟩:=short_energy_bound b
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=reference_from_low
    a b bΦ epsilon xi saving (Mcap+Bmask) ha hlo hhi hbΦ hepsilon hxi B hB S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D*Ce,hC,mul_pos hD hCe,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ε Q degree K hK hlow s hQ hs hxiM W₁ W₂ hs₁ hs₂ t X₁ X₂ hX₁ hX₂ hshort hlong D₁ hD₁ D₂ hD₂
  let short:=Real.logb Z X₁-Real.logb Z ((∏I∈D₁,I).absNorm:ℝ)
  let along:=Real.logb Z X₂-Real.logb Z ((∏I∈D₂,I).absNorm:ℝ)
  have hg:=actual_deleted_gates s hZ.1 hBmask Mcap L X₁ X₂ xi hs hL
    hX₁ hX₂ hxi.le hxiM hshort hlong D₁ D₂ hD₁ hD₂
  dsimp only at hg
  rw [←hg.1,←hg.2.1]
  have hZpos:0<Z:=zero_lt_one.trans hZ.1
  have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hLpos:0≤L:=by linarith [s.width_nonneg]
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  rcases hg.2.2.2.2.2.2.2 with hd|hr
  · have hdirect:=independent_from_low a b bΦ Bmask L Mcap ε Z Q degree S K hlow hBmask ha
      s hQ hs W₁ W₂ hs₁ hs₂ t t (Z^short) (Z^along)
      (Real.rpow_pos_of_pos hZpos _) (Real.rpow_pos_of_pos hZpos _)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.1)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hd.1) hd.2
    exact hdirect.trans (le_add_of_nonneg_right (by positivity))
  · have hh:=hZ.2 Bmask L Mcap ε Q degree K hK hlow hBmask s hQ hs
      W₂ W₁ hs₂ hs₁ t along short hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1 hg.2.2.2.1 hr.2
    dsimp only at hh
    have he₁:=he W₁ (fun x hx=>(hs₁ hx).2) (fun z=>naturalCharacter s.character z)
      t (Z^short) s.radial.scale s.radial.profile (effectiveState s).radial.keep
      (Real.rpow_pos_of_pos hZpos _) s.radial.scale_pos s.radial.nonneg
    have hswap:(fun z=>polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t *
        polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t)=
      (fun z=>polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t *
        polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t):=by funext z;ring
    rw [hswap]
    apply hh.trans
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    apply add_le_add
    · gcongr
      exact hg.2.2.2.2.2.2.1
    · calc
        _≤D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          (Ce*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*Z^(s.width/4)):=by
          gcongr
          exact he₁.trans (by
            gcongr
            · exact hZ.1.le
            · exact hg.2.2.1)
        _=_:=by ring

end SevenEighths.CenteredMomentEnergyZeroUnbalancedOriginalDeleted

end

end OAI
end OAIOriginalModule2786

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroUnbalancedOriginalGates
Source SHA256: f7ef3e30a0d1dfd0d76ebcca6bedb228a02113d2960d870841aafed9c495a033
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2787


namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyZeroUnbalancedOriginalGates
open CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBranchGeometry

lemma original_long_positive (Z M X₁ X₂:ℝ)(hZ:1<Z)(hM:0<M)
    (_hX₁:0<X₁)(hX₂:0<X₂)
    (hshort:length Z X₁≤M/4)
    (hlarge:5*M/6≤length Z X₁+length Z X₂):
    0<Real.logb Z X₂ ∧ length Z X₂=Real.logb Z X₂ ∧ 1≤X₂:=by
  have hpos:0<length Z X₂:=by linarith
  have he:=length_eq_max_log Z X₂ hZ hX₂
  have hl:0<Real.logb Z X₂:=by
    by_contra hn
    rw [he,max_eq_left (le_of_not_gt hn)] at hpos
    exact (lt_irrefl 0) hpos
  refine ⟨hl,he.trans (max_eq_right hl.le),?_⟩
  by_contra hn
  have hh:=Real.logb_le_logb_of_le hZ hX₂ (le_of_not_ge hn)
  rw [Real.logb_one] at hh
  linarith

lemma raw_short_bound (Z M X:ℝ)(hZ:1<Z)(hX:0<X)
    (hshort:length Z X≤M/4):Real.logb Z X≤M/4:=by
  rw [length_eq_max_log Z X hZ hX] at hshort
  exact (le_max_right _ _).trans hshort

end SevenEighths.CenteredMomentEnergyZeroUnbalancedOriginalGates

end

end OAI
end OAIOriginalModule2787

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroUnbalancedOriginalSource
Source SHA256: d562e56f910e9407b0fdb31e7af8347507f9e70c53946820a83a029a0a39e150
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2788



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroUnbalancedOriginalSource
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyZeroUnbalancedOriginalDeleted
open CenteredMomentEnergyReferenceDeletionEnergy CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
local notation "O"=>HeckeFamily.O

theorem original_from_low (epsilonDelete:ℝ)(hepsilonDelete:0<epsilonDelete)
    (a b bΦ epsilon xi saving Mcap Bmask L:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (hBmask:0≤Bmask)(hL:Mcap+Bmask+xi≤L)(B:ℕ)(hB:2≤B)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D Cweight:ℝ,0<C ∧ 0<D ∧ 0<Cweight ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(ε:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap ε Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q →s.width≤Mcap →xi≤s.width/6 →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁ →0<X₂ →Real.logb Z X₁≤s.width/4 →1≤X₂ →
      s.plainEnergy p t X₁ X₂ ≤
      Cweight*(s.puncture.radical.absNorm:ℝ)^epsilonDelete*(
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t t).control S)^2*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T (p.profile 0))^2*
            (1+|t|)^(2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*Z^(s.width/4))):=by
  obtain ⟨Cweight,hCweight,hweight⟩:=original_energy_weighted_deletion (α:=Fin 0)
    (fun _=>0) (fun _=>0) (fun _=>le_refl 0) epsilonDelete hepsilonDelete
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=deleted_from_low
    a b bΦ epsilon xi saving Mcap Bmask L ha hlo hhi hbΦ hepsilon hxi hBmask hL B hB S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,Cweight,hC,hD,hCweight,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ε Q degree K hK hlow s hQ hs hxiM p t X₁ X₂ hX₁ hX₂ hshort hlong
  have hZpos:0<Z:=zero_lt_one.trans hZ.1
  apply hweight Z Bmask bΦ a b s (p.profile 0) (p.profile 1) ha (by linarith)
    (p.support 0) (p.support 1) (fun _=>∅) (fun _ _=>0) (fun _=>1)
    t X₁ X₂ _ 0
  · simp
  · simp
  · simp
  · simp
  · exact hX₁
  · exact hX₂
  · have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
    have hLpos:0≤L:=by linarith [s.width_nonneg]
    have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
    positivity
  · norm_num
  · intro D₁ hD₁ D₂ hD₂ J hJ
    simpa only [Finset.univ_eq_empty,Finset.empty_sdiff,Finset.prod_empty,mul_one,Real.rpow_zero] using
      hZ.2 ε Q degree K hK hlow s hQ hs hxiM (p.profile 0) (p.profile 1)
        (p.support 0) (p.support 1) t X₁ X₂ hX₁ hX₂ hshort hlong D₁ hD₁ D₂ hD₂

end SevenEighths.CenteredMomentEnergyZeroUnbalancedOriginalSource

end

end OAI
end OAIOriginalModule2788

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroUnbalancedOriginalPower
Source SHA256: baf64c880cb48c79fc7410ae515de407a7d699e32d2dbbed0041221899cd6f06
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2789




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroUnbalancedOriginalPower
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroUnbalancedOriginalSource CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyStageReserveBounded
open CenteredMomentEnergyReferenceProfileBudget CenteredMomentNaturalRowSource
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

theorem original_from_zero_low
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤e → 0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤s.width →s.width≤Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁ →0<X₂ →Real.logb Z X₁≤s.width/4 →1≤X₂ →
      s.plainEnergy p t X₁ X₂ ≤
        C*(K+1)*diagonalControl s.radial.profile*
          (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,saving,L,Cscalar,hd,hxi,hsaving,hCs,hxirho,hL,hLupper,hscalar⟩:=
    exists_bounded_separated_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro S
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,Cref,Dref,Cweight,hCr,hDr,hCw,href⟩:=
    original_from_low d hd a b bΦ d xi saving Mcap Bmask L ha hlo hhi hbΦ hd hxi
      hBmask hL 2 (by norm_num) S
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T Slong 0 n nlong
    Cref Dchild Dref hCr hDc hDr
  refine ⟨J,U,Cweight*Cprofile*Cscalar,by positivity,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hshort hlong
  have hxiM:xi≤s.width/6:=by linarith only [hxirho, hslo, hrho]
  have hh:=hZ.2 e Q degree K hK hlow s hQ hs hxiM p t X₁ X₂ hX₁ hX₂ hshort hlong
  have hledger:=hscalar e he Z hZ.1.le s hs (Fin 0) (fun _=>0) (by simpa using hM)
  simp only [Finset.univ_eq_empty,Finset.prod_empty,mul_one] at hledger
  have hp:=hprofile (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t 0 (le_refl 0)
  simp only [add_zero,zero_add,pow_zero,mul_one] at hp
  let A:=Cprofile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*(1+|t|)^J
  let E:=(K+1)*diagonalControl s.radial.profile*A
  have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hA:0≤A:=by dsimp only [A];positivity
  have hE:0≤E:=by dsimp only [E];positivity
  have hdir:K*diagonalControl s.radial.profile*
      ((CenteredMomentEnergyReferenceChild.independentProfiles ha (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t t).control S)^2≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=by
      dsimp only [E]
      nlinarith only [mul_nonneg hdiag hA]
    apply le_trans _ hk
    exact ht
  have hmain:Cref*(sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*
      (K*diagonalControl s.radial.profile*Dchild*(sourceControl T (p.profile 0))^2*
        (1+|t|)^(2*n))≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=by
      dsimp only [E]
      nlinarith only [mul_nonneg hdiag hA]
    apply le_trans _ hk
    convert ht using 1 ; ring
  have herr:Dref*(sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*diagonalControl s.radial.profile≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.2 hdiag
    have hk:diagonalControl s.radial.profile*A≤E:=by
      dsimp only [E]
      nlinarith only [mul_nonneg hK (mul_nonneg hdiag hA)]
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hLpos:0≤L:=by linarith only [hM, hBmask, hxi, hL]
  let P:=Z^(s.width+e)
  let Qmain:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))*Z^(s.width+e)
  let Qerror:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)
  have hP:0≤P:=by dsimp only [P];positivity
  have hQmain:0≤Qmain:=by dsimp only [Qmain];positivity
  have hQerror:0≤Qerror:=by dsimp only [Qerror];positivity
  have htotal:=add_le_add (add_le_add (mul_le_mul_of_nonneg_right hdir hP)
    (mul_le_mul_of_nonneg_right hmain hQmain)) (mul_le_mul_of_nonneg_right herr hQerror)
  apply hh.trans
  have hfirst:=mul_le_mul_of_nonneg_left htotal
    (show 0≤Cweight*(s.puncture.radical.absNorm:ℝ)^d by positivity)
  have hlast:=mul_le_mul_of_nonneg_left hledger (mul_nonneg hCw.le hE)
  refine le_trans ?_ (hlast.trans_eq ?_)
  · dsimp only [P,Qmain,Qerror] at hfirst
    convert hfirst using 1 <;> (try dsimp only [E,A]) <;> ring
  · dsimp only [E,A]
    ring

end SevenEighths.CenteredMomentEnergyZeroUnbalancedOriginalPower

end

end OAI
end OAIOriginalModule2789

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroUnbalancedOriginal
Source SHA256: d212a815247b8fc3d2c5587f6c34cf12bbe1700c33e7dbee98c7f81f7330f5b7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2790



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroUnbalancedOriginal
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyZeroUnbalancedOriginalPower
open CenteredMomentEnergyZeroUnbalancedOriginalGates
local notation "O"=>HeckeFamily.O

theorem original_unbalanced_from_zero_low
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤e → 0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤s.width →s.width≤Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁ →0<X₂ →
      min (length Z X₁) (length Z X₂)≤s.width/4 →
      5*s.width/6≤length Z X₁+length Z X₂ →
      s.plainEnergy p t X₁ X₂ ≤
        C*(K+1)*diagonalControl s.radial.profile*(p.control U)^2*
          (1+|t|)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=original_from_zero_low
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hshort hlarge
  have hordered (p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)
      (hshort:length Z X₁≤s.width/4)
      (hlarge:5*s.width/6≤length Z X₁+length Z X₂):
      s.plainEnergy p t X₁ X₂≤
        C*(K+1)*diagonalControl s.radial.profile*(p.control U)^2*
          (1+|t|)^J*Z^(s.width+e+ε):=by
    have hlong:=original_long_positive Z s.width X₁ X₂ hZ.1
      (hrho.trans_le hslo) hX₁ hX₂ hshort hlarge
    exact hZ.2 e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂
      (raw_short_bound Z s.width X₁ hZ.1 hX₁ hshort) hlong.2.2
  rcases min_le_iff.mp hshort with hshort|hshort
  · exact hordered p X₁ X₂ hX₁ hX₂ hshort hlarge
  · let p':Profiles a b:={
      profile:=![p.profile 1,p.profile 0]
      support:=by
        intro i
        fin_cases i
        · simpa using p.support 1
        · simpa using p.support 0 }
    have hpcontrol:p'.control U=p.control U:=by
      simp [p',Profiles.control,mul_comm]
    have hswap:s.plainEnergy p' t X₂ X₁=s.plainEnergy p t X₁ X₂:=by
      unfold NaturalState.plainEnergy CenteredMomentInductionEnergy.energy
      apply tsum_congr
      intro z
      have hh:CenteredMomentRetainedEnergy.positiveSlotRow s.character s.mask 1 z
          (p'.profile 0) (p'.profile 1) (fun _:Fin 0=>∅) (fun _:Fin 0=>0)
          (fun _:Fin 0=>1) t X₂ X₁=
          CenteredMomentRetainedEnergy.positiveSlotRow s.character s.mask 1 z
          (p.profile 0) (p.profile 1) (fun _:Fin 0=>∅) (fun _:Fin 0=>0)
          (fun _:Fin 0=>1) t X₁ X₂:=by
        simp only [p',Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
        unfold CenteredMomentRetainedEnergy.positiveSlotRow
        rw [mul_comm X₂ X₁]
        ring
      rw [hh]
    have hh:=hordered p' X₂ X₁ hX₂ hX₁ hshort (by linarith)
    simpa only [hswap,hpcontrol] using hh

end SevenEighths.CenteredMomentEnergyZeroUnbalancedOriginal

end

end OAI
end OAIOriginalModule2790

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AllocatedRayDictionary
Source SHA256: 85c40e5529aa469a9cc99037fcbc89c630b88a1fd6181e56636795d391a45e48
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2791




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentAllocatedRayDictionary
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation
open CenteredMomentCommonMaskEnergy CenteredMomentInductionEnergy
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentHeckeTwist CenteredMomentHeckeCancellation
local notation "O" => HeckeFamily.O

variable {α : Type*} [Fintype α] [DecidableEq α]

def originalEmbedding (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C) :
    CenteredMomentCommonProfile.liveIndices B.val ↪ α :=
  ⟨Subtype.val, Subtype.val_injective⟩

def remaining (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) :
    Finset (CenteredMomentCommonProfile.liveIndices B.val) :=
  CenteredMomentDivisorRaw.liveIndices (ι := CenteredMomentCommonProfile.liveIndices B.val) L a \ J

def originalImage (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) : Finset α :=
  (remaining s C B L a J).map (originalEmbedding s C B)

lemma projection_injective (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) :
    Function.Injective (fun i : remaining s C B L a J => i.val.val) := by
  intro i j h
  exact Subtype.ext (Subtype.ext h)

lemma mem_originalImage (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) (i : α) :
    i ∈ originalImage s C B L a J ↔
      ∃ j ∈ remaining s C B L a J, j.val = i := by
  simp only [originalImage, Finset.mem_map, originalEmbedding, Function.Embedding.coeFn_mk]

lemma originalImage_card (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) :
    (originalImage s C B L a J).card = (remaining s C B L a J).card := Finset.card_map _

def commonFirst (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (left : Bool) : ℝ :=
  if left then (commonData s C R B).X₁ else (commonData s C R B).Y₁

def commonSecond (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (left : Bool) : ℝ :=
  if left then (commonData s C R B).X₂ else (commonData s C R B).Y₂

omit [DecidableEq α] in
lemma commonFirst_pos (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (left : Bool) : 0 < commonFirst s C R B left := by
  unfold commonFirst
  split
  · exact (commonData s C R B).X₁_pos
  · exact (commonData s C R B).Y₁_pos

omit [DecidableEq α] in
lemma commonSecond_pos (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (left : Bool) : 0 < commonSecond s C R B left := by
  unfold commonSecond
  split
  · exact (commonData s C R B).X₂_pos
  · exact (commonData s C R B).Y₂_pos

section RayData
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

structure Matches (s : Input α) (η₀ : Character)
    (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ)
    (W : ℝ → ℂ) (bslot Z : ℝ) : Prop where
  character : ∀ i I, s.ν i I = idealCoeff (relativeCharacter M H hH η₀ (θ i)) I
  profile : ∀ i y, s.W i y = W y * (y : ℂ)^(-HeckeDyadic.shift (σ i) (freq i))
  pool : ∀ i, s.slots i = primePool M H bslot (Z^(w i))
  scale : ∀ i, s.P i = Z^(w i)

variable {M H hH}
variable {s : Input α} {η₀ : Character} {θ : α → RayQuotient.Characters M H}
  {w σ freq : α → ℝ} {W : ℝ → ℂ} {bslot Z : ℝ}
  (h : Matches M H hH s η₀ θ w σ freq W bslot Z)

include h

omit [DecidableEq α] in
lemma common_coefficient (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (i : CenteredMomentCommonProfile.liveIndices B.val)
    (I : Ideal O) :
    (commonData (withHeight s τ v) C R B).coefficient i I =
      idealCoeff (relativeCharacter M H hH η₀ (θ i.val)) I *
        annularWeight W (Z^(w i.val)) (σ i.val) (freq i.val) I := by
  change s.ν i.val I * s.W i.val ((I.absNorm : ℝ) / s.P i.val) = _
  rw [h.character, h.profile, h.scale]
  rfl

omit [DecidableEq α] in
lemma common_height_coefficient (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (i : CenteredMomentCommonProfile.liveIndices B.val)
    (I : Ideal O) (hI : I ≠ 0) :
    heightCoefficient ((commonData (withHeight s τ v) C R B).coefficient i) v I =
      ((Z^(w i.val) : ℝ) : ℂ)^(Complex.I*v) *
        (idealCoeff (relativeCharacter M H hH η₀ (θ i.val)) I *
          annularWeight W (Z^(w i.val)) (σ i.val) (v+freq i.val) I) := by
  have he : (commonData (withHeight s τ v) C R B).coefficient i =
      fun I => idealCoeff (relativeCharacter M H hH η₀ (θ i.val)) I *
        annularWeight W (Z^(w i.val)) (σ i.val) (freq i.val) I :=
    funext (common_coefficient h τ v C R B i)
  rw [he]
  exact CenteredMomentEnergySlotHeight.height_coefficient _ W _ _ _ v
    (h.scale i.val ▸ s.P_pos i.val) I hI

omit [DecidableEq α] in
lemma scale_phase_norm (i : α) (v : ℝ) :
    ‖((Z^(w i) : ℝ) : ℂ)^(Complex.I*v)‖ = 1 := by
  simpa using Complex.norm_cpow_eq_rpow_re_of_pos (h.scale i ▸ s.P_pos i) (Complex.I*v)

theorem common_energy (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (m A : O) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let d := commonData (withHeight s τ v) C R B
    energy τ m A 0 W₁ W₂
      (fun i : remaining s C B L a J => d.slots i.val)
      (fun i : remaining s C B L a J => heightCoefficient (d.coefficient i.val) v)
      (fun i : remaining s C B L a J => d.P i.val) X₁ X₂ keep Φ K =
    energy τ m A 0 W₁ W₂
      (fun i : originalImage s C B L a J => primePool M H bslot (Z^(w i)))
      (fun i : originalImage s C B L a J => fun I =>
        idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
      (fun i : originalImage s C B L a J => Z^(w i)) X₁ X₂ keep Φ K := by
  dsimp only
  have hc : (fun i : remaining s C B L a J =>
      (commonData (withHeight s τ v) C R B).coefficient i.val) =
      fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i.val.val)) I *
        annularWeight W (Z^(w i.val.val)) (σ i.val.val) (freq i.val.val) I := by
    funext i I
    exact common_coefficient h τ v C R B i.val I
  have hp : (fun i : remaining s C B L a J =>
      (commonData (withHeight s τ v) C R B).P i.val) = fun i => Z^(w i.val.val) := by
    funext i
    exact h.scale i.val.val
  have hs : (fun i : remaining s C B L a J =>
      (commonData (withHeight s τ v) C R B).slots i.val) =
      fun i => primePool M H bslot (Z^(w i.val.val)) := by
    funext i
    exact h.pool i.val.val
  have hhc := congrArg (fun f => fun i : remaining s C B L a J => heightCoefficient (f i) v) hc
  rw [hhc, hp, hs]
  rw [CenteredMomentEnergySlotHeight.inherited_height_energy τ m A W₁ W₂ _ _ _ _ _ _
    (fun i => h.scale i.val.val ▸ s.P_pos i.val.val)
    (fun i I hI => (s.prime i.val.val I (by rw [h.pool]; exact hI)).ne_zero)
    v 0 X₁ X₂ keep Φ K]
  exact CenteredMomentEnergyReindex.energy_subset_map (originalEmbedding s C B)
    (remaining s C B L a J) τ m A W₁ W₂
    (fun i => primePool M H bslot (Z^(w i)))
    (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
      annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
    (fun i => Z^(w i)) 0 X₁ X₂ keep Φ K

theorem common_clipped_energy (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (V₁ V₂ : Plain) (X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (D₁ D₂ : Finset (Ideal O)) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let d := commonData (withHeight s τ v) C R B
    let W₁ := V₁.profile (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₁ 0) (rawScale_pos (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₁ hX₁ 0) v
    let W₂ := V₂.profile (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₂ 1) (rawScale_pos (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₂ hX₂ 1) v
    let Y₁ := clippedScale (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ)
    let Y₂ := clippedScale (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)
    energy τ (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0
      W₁ W₂ (fun i : remaining s C B L a J => d.slots i.val)
      (fun i : remaining s C B L a J => heightCoefficient (d.coefficient i.val) v)
      (fun i : remaining s C B L a J => d.P i.val) Y₁ Y₂ keep Φ K =
    energy τ (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0
      W₁ W₂ (fun i : originalImage s C B L a J => primePool M H bslot (Z^(w i)))
      (fun i : originalImage s C B L a J => fun I =>
        idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
      (fun i : originalImage s C B L a J => Z^(w i)) Y₁ Y₂ keep Φ K :=
  common_energy h τ v C R B L a J _ 1 _ _ _ _ keep Φ K

theorem both_common_rectangles (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (V₁ V₂ : Plain) (left : Bool)
    (D₁ D₂ : Finset (Ideal O)) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let X₁ := commonFirst s C R B left
    let X₂ := commonSecond s C R B left
    let hX₁ := commonFirst_pos s C R B left
    let hX₂ := commonSecond_pos s C R B left
    let d := commonData (withHeight s τ v) C R B
    let W₁ := V₁.profile (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₁ 0) (rawScale_pos (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₁ hX₁ 0) v
    let W₂ := V₂.profile (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₂ 1) (rawScale_pos (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₂ hX₂ 1) v
    let Y₁ := clippedScale (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ)
    let Y₂ := clippedScale (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)
    energy τ (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0
      W₁ W₂ (fun i : remaining s C B L a J => d.slots i.val)
      (fun i : remaining s C B L a J => heightCoefficient (d.coefficient i.val) v)
      (fun i : remaining s C B L a J => d.P i.val) Y₁ Y₂ keep Φ K =
    energy τ (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0
      W₁ W₂ (fun i : originalImage s C B L a J => primePool M H bslot (Z^(w i)))
      (fun i : originalImage s C B L a J => fun I =>
        idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
      (fun i : originalImage s C B L a J => Z^(w i)) Y₁ Y₂ keep Φ K :=
  common_clipped_energy h τ v C R B L a J V₁ V₂
    (commonFirst s C R B left) (commonSecond s C R B left)
    (commonFirst_pos s C R B left) (commonSecond_pos s C R B left) D₁ D₂ keep Φ K

omit h

lemma deleted_clipped_scale_pos (C : Ideal O) (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (X : ℝ) (j : Fin 2) (D : Finset (Ideal O)) (hD : ∀I∈D,I≠0) :
    0 < clippedScale (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X j)/(Ideal.absNorm (∏I∈D,I):ℝ) := by
  apply div_pos (zero_lt_one.trans_le (clippedScale_ge_one _))
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Finset.prod_ne_zero_iff.mpr hD))

lemma originalImage_fixedQ (Q : Ideal O) (hQM : Q ≤ M) (hQη : Q ≤ η₀.modulus)
    (C : Ideal O) (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (i : originalImage s C B L a J) :
    Q ≤ (relativeCharacter M H hH η₀ (θ i)).modulus :=
  relativeCharacter_fixedQ M H hH η₀ (θ i) Q hQM hQη

lemma originalImage_bounds (C : Ideal O) (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (Lslot lo hi height heightShift v : ℝ)
    (hw : ∀i,0 ≤ w i) (hwL : ∀i,w i ≤ Lslot)
    (hσlo : ∀i,lo ≤ σ i) (hσhi : ∀i,σ i ≤ hi)
    (hf : ∀i,|freq i| ≤ height) (hv : |v| ≤ heightShift) :
    ∀i : originalImage s C B L a J,
      0 ≤ w i ∧ w i ≤ Lslot ∧ lo ≤ σ i ∧ σ i ≤ hi ∧ |v+freq i| ≤ height+heightShift := by
  intro i
  refine ⟨hw i, hwL i, hσlo i, hσhi i, ?_⟩
  exact (abs_add_le v (freq i)).trans (by linarith [hf i])

lemma originalImage_scale_bounds (C : Ideal O) (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (hZ : 1<Z) (Lslot : ℝ) (hw : ∀i,0 ≤ w i) (hwL : ∀i,w i ≤ Lslot) :
    ∀i : originalImage s C B L a J, 1 ≤ Z^(w i) ∧ Z^(w i) ≤ Z^Lslot := by
  intro i
  exact ⟨Real.one_le_rpow hZ.le (hw i), Real.rpow_le_rpow_of_exponent_le hZ.le (hwL i)⟩

end RayData
end SevenEighths.CenteredMomentAllocatedRayDictionary

end

end OAI
end OAIOriginalModule2791

/-! Original module: OAI.NumberTheory.DirichletL.Energy.AmplifiedRayDictionary
Source SHA256: 81352bf6cd3904b6be633617d224fc8e5b6a1db395f499bcd6a342ad0ad753a2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2792




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary
open HeckeFamily CenteredMomentSecondHeightFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps CenteredMomentAllocatedRayDictionary
open CenteredMomentFirstAnnularInput CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentInductionEnergy CenteredMomentCommonMaskEnergy
open CenteredMomentEligibleEnergy CenteredMomentCommonHeightEnvelope
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α]
local instance {β : Type*} : DecidableEq β := Classical.decEq _

lemma active_pools_subset (s : Input α) (j : α⊕Fin 2) :
    (activeInput s).pools j⊆s.pools j := by
  cases j with
  | inl i => exact Finset.filter_subset _ _
  | inr j => exact Finset.Subset.refl _

lemma actualAllocations_mono {β : Type*} [Fintype β]
    (S T : β→Finset (Ideal O)) (h : ∀i,S i⊆T i) (C : Ideal O) :
    actualAllocations S C⊆actualAllocations T C := by
  intro B hB
  obtain ⟨hlabel,hprod⟩ := Finset.mem_filter.mp hB
  obtain ⟨v,hv,hvB⟩ := Finset.mem_image.mp hlabel
  refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨v,?_,hvB⟩,hprod⟩
  exact Fintype.mem_piFinset.mpr (fun i=>h i (Fintype.mem_piFinset.mp hv i))

abbrev restoreAllocation (s : Input α) (C : Ideal O)
    (B : actualAllocations (activeInput s).pools C) : actualAllocations s.pools C :=
  ⟨B.val,actualAllocations_mono _ _ (active_pools_subset s) C B.property⟩

@[simp] lemma restoreAllocation_val (s : Input α) (C : Ideal O)
    (B : actualAllocations (activeInput s).pools C) : (restoreAllocation s C B).val=B.val := rfl

lemma restoreAllocation_injective (s : Input α) (C : Ideal O) :
    Function.Injective (restoreAllocation s C) := by
  intro B D h
  exact Subtype.ext (congrArg (fun x : actualAllocations s.pools C=>x.val) h)

lemma child_active (s : Input α) (C R : Ideal O)
    (B : actualAllocations (activeInput s).pools C) (τ : Character) (t : ℝ) :
    child (activeInput s) C R B τ t=
      activeInput (child s C R (restoreAllocation s C B) τ t) := rfl

lemma active_coefficient (s : Input α) (i : α) :
    (activeInput s).toData.coefficient i=s.toData.coefficient i := rfl

lemma rowSlot_active (s : Input α) (i : α) (η : Character) (m A z : O) (t v : ℝ) :
    rowSlot η m A z ((activeInput s).slots i)
      (heightCoefficient ((activeInput s).toData.coefficient i) v) t=
    rowSlot η m A z (s.slots i) (heightCoefficient (s.toData.coefficient i) v) t := by
  unfold rowSlot
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro I hI hn
  have hz : s.W i ((I.absNorm:ℝ)/s.P i)=0 := by
    by_contra hh
    exact hn (Finset.mem_filter.mpr ⟨hI,hh⟩)
  simp only [heightCoefficient,Data.coefficient,activeInput,hz,mul_zero,zero_mul]

lemma positive_active (s : Input α) (η : Character) (m A z : O)
    (W₁ W₂ : ℝ→ℂ) (t v X₁ X₂ : ℝ) :
    positiveSlotRow η m A z W₁ W₂ (activeInput s).slots
      (fun i=>heightCoefficient ((activeInput s).toData.coefficient i) v)
      (activeInput s).P t X₁ X₂=
    positiveSlotRow η m A z W₁ W₂ s.slots
      (fun i=>heightCoefficient (s.toData.coefficient i) v) s.P t X₁ X₂ := by
  unfold positiveSlotRow
  congr 2
  exact Finset.prod_congr rfl (fun i _=>rowSlot_active s i η m A z t v)

theorem energy_active (s : Input α) (η : Character) (m A : O)
    (W₁ W₂ : ℝ→ℂ) (t v X₁ X₂ : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η m A t W₁ W₂ (activeInput s).slots
      (fun i=>heightCoefficient ((activeInput s).toData.coefficient i) v)
      (activeInput s).P X₁ X₂ keep Φ K=
    energy η m A t W₁ W₂ s.slots
      (fun i=>heightCoefficient (s.toData.coefficient i) v) s.P X₁ X₂ keep Φ K := by
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_active]

theorem positive_active_restrict {κ : Type*} [Fintype κ] (s : Input α) (f : κ→α)
    (η : Character) (m A z : O) (W₁ W₂ : ℝ→ℂ) (t v X₁ X₂ : ℝ) :
    positiveSlotRow η m A z W₁ W₂ (fun i=>(activeInput s).slots (f i))
      (fun i=>heightCoefficient ((activeInput s).toData.coefficient (f i)) v)
      (fun i=>(activeInput s).P (f i)) t X₁ X₂=
    positiveSlotRow η m A z W₁ W₂ (fun i=>s.slots (f i))
      (fun i=>heightCoefficient (s.toData.coefficient (f i)) v)
      (fun i=>s.P (f i)) t X₁ X₂ := by
  unfold positiveSlotRow
  congr 2
  exact Finset.prod_congr rfl (fun i _=>rowSlot_active s (f i) η m A z t v)

theorem energy_active_restrict {κ : Type*} [Fintype κ] (s : Input α) (f : κ→α)
    (η : Character) (m A : O) (W₁ W₂ : ℝ→ℂ) (t v X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η m A t W₁ W₂ (fun i=>(activeInput s).slots (f i))
      (fun i=>heightCoefficient ((activeInput s).toData.coefficient (f i)) v)
      (fun i=>(activeInput s).P (f i)) X₁ X₂ keep Φ K=
    energy η m A t W₁ W₂ (fun i=>s.slots (f i))
      (fun i=>heightCoefficient (s.toData.coefficient (f i)) v)
      (fun i=>s.P (f i)) X₁ X₂ keep Φ K := by
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_active_restrict]

theorem common_energy_active (s : Input α) (C R : Ideal O)
    (B : actualAllocations (activeInput s).pools C) (τ : Character) (v : ℝ)
    (L : Ideal O)
    (a : CenteredMomentDivisorAllocation.Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2)))
    (J : Finset (liveIndices B.val)) (m A : O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let d : CenteredMomentEligibleEnergy.Data (liveIndices B.val) :=
      commonData (withHeight (activeInput s) τ v) C R
        ⟨B.val, by simpa only [withHeight, Input.pools] using B.property⟩
    let e : CenteredMomentEligibleEnergy.Data (liveIndices B.val) :=
      commonData (withHeight s τ v) C R
        ⟨B.val, by simpa only [withHeight, Input.pools, restoreAllocation_val]
          using (restoreAllocation s C B).property⟩
    energy τ m A 0 W₁ W₂
      (fun i:remaining (activeInput s) C B L a J=>d.slots i.val)
      (fun i:remaining (activeInput s) C B L a J=>heightCoefficient (d.coefficient i.val) v)
      (fun i:remaining (activeInput s) C B L a J=>d.P i.val) X₁ X₂ keep Φ K=
    energy τ m A 0 W₁ W₂
      (fun i:remaining s C (restoreAllocation s C B) L a J=>e.slots i.val)
      (fun i:remaining s C (restoreAllocation s C B) L a J=>heightCoefficient (e.coefficient i.val) v)
      (fun i:remaining s C (restoreAllocation s C B) L a J=>e.P i.val) X₁ X₂ keep Φ K := by
  exact energy_active_restrict s
    (fun i:remaining (activeInput s) C B L a J=>i.val.val) τ m A W₁ W₂ 0 v X₁ X₂ keep Φ K

def restoredError (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) : Input (liveIndices Bp.val) :=
  twiceChild s C R B τ t Q k (restoreAllocation (child s C R B τ t) (Q^k) Bp) υ v

lemma error_source_active (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    child (activeInput (child s C R B τ t)) (Q^k) (R*C) Bp υ v=
      activeInput (restoredError s C R B τ t Q k Bp υ v) := rfl

theorem restoredError_data (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    let d:=restoredError s C R B τ t Q k Bp υ v
    d.η=υ ∧ d.t=v ∧ d.m=fixedBadMask*ConcretePrimeRowBridge.idealGenerator ((R*C)*(Q^k)) ∧
    d.X₁=s.X₁/(B.val (Sum.inr 0)).absNorm/(Bp.val (Sum.inr 0)).absNorm ∧
    d.X₂=s.X₂/(B.val (Sum.inr 1)).absNorm/(Bp.val (Sum.inr 1)).absNorm ∧
    d.Y₁=s.Y₁/(B.val (Sum.inr 0)).absNorm/(Bp.val (Sum.inr 0)).absNorm ∧
    d.Y₂=s.Y₂/(B.val (Sum.inr 1)).absNorm/(Bp.val (Sum.inr 1)).absNorm :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem error_live_slots (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k)) :
    liveIndices Bp.val=Finset.univ :=
  prime_slots_live (activeInput (child s C R B τ t)) Q hQ k hslot Bp

theorem restoredError_volume (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    volume (restoredError s C R B τ t Q k Bp υ v)=
      volume s/(CenteredMomentCommonRawScale.rawReduction B.val s.P*(Q.absNorm:ℝ)^k) := by
  have hh:=child_volume (activeInput (child s C R B τ t)) Q hQ k hslot (R*C) Bp υ v
  rw [error_source_active,active_volume,active_volume,common_volume,div_div] at hh
  exact hh

theorem error_normalized_source (s : Input α) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    childNormalizedGaussSource (activeInput (child s C R B τ t)) (Q^k) (R*C) seed Bp υ v Φ K=
      normalizedGaussSource (restoredError s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed Φ K := by
  unfold childNormalizedGaussSource
  rw [error_source_active,active_normalized]

theorem error_normalized_sum (s : Input α) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (υ : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k)→Character)
    (v : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k)→ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑Bp:actualAllocations (activeInput (child s C R B τ t)).pools (Q^k),
      childNormalizedGaussSource (activeInput (child s C R B τ t)) (Q^k) (R*C) seed Bp (υ Bp) (v Bp) Φ K)=
    ∑Bp:actualAllocations (activeInput (child s C R B τ t)).pools (Q^k),
      normalizedGaussSource (restoredError s C R B τ t Q k Bp (υ Bp) (v Bp)) ((R*C)*(Q^k)) seed Φ K :=
  Finset.sum_congr rfl (fun Bp _=>error_normalized_source s C R seed B τ t Q k Bp (υ Bp) (v Bp) Φ K)

theorem error_energy (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let e:=child (activeInput (child s C R B τ t)) (Q^k) (R*C) Bp υ v
    let d:=restoredError s C R B τ t Q k Bp υ v
    energy e.η e.m 1 0 W₁ W₂ e.slots
      (fun i=>heightCoefficient (e.toData.coefficient i) e.t) e.P X₁ X₂ keep Φ K=
    energy d.η d.m 1 0 W₁ W₂ d.slots
      (fun i=>heightCoefficient (d.toData.coefficient i) d.t) d.P X₁ X₂ keep Φ K := by
  dsimp only
  rw [error_source_active]
  exact energy_active (restoredError s C R B τ t Q k Bp υ v) υ
    (fixedBadMask*ConcretePrimeRowBridge.idealGenerator ((R*C)*(Q^k))) 1 W₁ W₂ 0 v X₁ X₂ keep Φ K

section Ray
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
variable {s : Input α} {η₀ : Character} {θ : α→RayQuotient.Characters M H}
  {w σ freq : α→ℝ} {W : ℝ→ℂ} {bslot Z : ℝ}

theorem matches_child (h : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    Matches M H hH (child s C R B τ t) η₀
      (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val)
      (fun i=>freq i.val) W bslot Z := by
  constructor
  · intro i I;exact h.character i.val I
  · intro i y;exact h.profile i.val y
  · intro i;exact h.pool i.val
  · intro i;exact h.scale i.val

theorem matches_twiceChild (h : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :
    Matches M H hH (twiceChild s C R B τ t Q k Bp υ v) η₀
      (fun i=>θ i.val.val) (fun i=>w i.val.val) (fun i=>σ i.val.val)
      (fun i=>freq i.val.val) W bslot Z :=
  matches_child M H hH (matches_child M H hH h C R B τ t) (Q^k) (R*C) Bp υ v

theorem active_common_ray_energy (h : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations (activeInput s).pools C) (L : Ideal O)
    (a : CenteredMomentDivisorAllocation.Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2)))
    (J : Finset (liveIndices B.val)) (m A : O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let d : CenteredMomentEligibleEnergy.Data (liveIndices B.val) :=
      commonData (withHeight (activeInput s) τ v) C R
        ⟨B.val, by simpa only [withHeight, Input.pools] using B.property⟩
    energy τ m A 0 W₁ W₂
      (fun i:remaining (activeInput s) C B L a J=>d.slots i.val)
      (fun i:remaining (activeInput s) C B L a J=>heightCoefficient (d.coefficient i.val) v)
      (fun i:remaining (activeInput s) C B L a J=>d.P i.val) X₁ X₂ keep Φ K=
    energy τ m A 0 W₁ W₂
      (fun i:originalImage s C (restoreAllocation s C B) L a J=>primePool M H bslot (Z^(w i)))
      (fun i:originalImage s C (restoreAllocation s C B) L a J=>fun I=>
        idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
      (fun i:originalImage s C (restoreAllocation s C B) L a J=>Z^(w i)) X₁ X₂ keep Φ K :=
  (common_energy_active s C R B τ v L a J m A W₁ W₂ X₁ X₂ keep Φ K).trans
    (common_energy h τ v C R (restoreAllocation s C B) L a J m A W₁ W₂ X₁ X₂ keep Φ K)

theorem restoredError_matches (h : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    Matches M H hH (restoredError s C R B τ t Q k Bp υ v) η₀
      (fun i=>θ i.val.val) (fun i=>w i.val.val) (fun i=>σ i.val.val)
      (fun i=>freq i.val.val) W bslot Z :=
  matches_twiceChild M H hH h C R B τ t Q k (restoreAllocation (child s C R B τ t) (Q^k) Bp) υ v

end Ray
end SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

end

end OAI
end OAIOriginalModule2792

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ActiveChildRestoration
Source SHA256: ce4a798fdd67dea471ebf8e6868f4dfac393507d0540c9de332fe5d9a35db066
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2793



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyActiveChildRestoration
open ConcretePrimeRowBridge
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonHeightEnvelope
open CenteredMomentFirstAnnularInput CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy CenteredMomentCommonMaskEnergy
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α]
local instance {β:Type*}:DecidableEq β:=Classical.decEq _

theorem allocated_row_active (s:Input α)(C R:Ideal O)
    (B:actualAllocations (activeInput s).pools C)(τ:Character)(v:ℝ)
    (D:Ideal O)(a:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (z:O)(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ):
    let d : CenteredMomentEligibleEnergy.Data (CenteredMomentCommonProfile.liveIndices B.val) :=
      commonData (withHeight (activeInput s) τ v) C R
        ⟨B.val, by simpa only [withHeight, Input.pools] using B.property⟩
    let e : CenteredMomentEligibleEnergy.Data (CenteredMomentCommonProfile.liveIndices B.val) :=
      commonData (withHeight s τ v) C R
        ⟨B.val, by simpa only [withHeight, Input.pools, restoreAllocation_val]
          using (restoreAllocation s C B).property⟩
    allocatedPositiveRow d.η d.m d.A z d.t d.slots d.coefficient d.P D a W₁ W₂ X₁ X₂=
      allocatedPositiveRow e.η e.m e.A z e.t e.slots e.coefficient e.P D a W₁ W₂ X₁ X₂ := by
  change positiveSlotRow τ
      (CenteredMomentSecondHeightFamily.fixedBadMask * idealGenerator (R * C)) 1 z
      (dilated W₁ (clipDilation (X₁ / Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain D a 0))))
      (dilated W₂ (clipDilation (X₂ / Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain D a 1))))
      (fun i : CenteredMomentDivisorRaw.liveIndices D a => (activeInput s).slots i.val.val)
      (fun i => (activeInput s).toData.coefficient i.val.val)
      (fun i => (activeInput s).P i.val.val) v _ _ =
    positiveSlotRow τ
      (CenteredMomentSecondHeightFamily.fixedBadMask * idealGenerator (R * C)) 1 z
      (dilated W₁ (clipDilation (X₁ / Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain D a 0))))
      (dilated W₂ (clipDilation (X₂ / Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain D a 1))))
      (fun i : CenteredMomentDivisorRaw.liveIndices D a => s.slots i.val.val)
      (fun i => s.toData.coefficient i.val.val)
      (fun i => s.P i.val.val) v _ _
  unfold positiveSlotRow
  congr 2
  apply Finset.prod_congr rfl
  intro i _
  have hz (f : Ideal O → ℂ) : heightCoefficient f 0 = f := by
    funext I
    simp [heightCoefficient]
  simpa only [hz] using rowSlot_active s i.val.val τ
    (CenteredMomentSecondHeightFamily.fixedBadMask * idealGenerator (R * C)) 1 z v 0

theorem child_energy_active (s:Input α)(C R:Ideal O)
    (B:actualAllocations (activeInput s).pools C)(τ:Character)(v:ℝ)
    (D:Ideal O)(a:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (rad:Radial):
    let d : CenteredMomentEligibleEnergy.Data (CenteredMomentCommonProfile.liveIndices B.val) :=
      commonData (withHeight (activeInput s) τ v) C R
        ⟨B.val, by simpa only [withHeight, Input.pools] using B.property⟩
    let e : CenteredMomentEligibleEnergy.Data (CenteredMomentCommonProfile.liveIndices B.val) :=
      commonData (withHeight s τ v) C R
        ⟨B.val, by simpa only [withHeight, Input.pools, restoreAllocation_val]
          using (restoreAllocation s C B).property⟩
    childEnergy d rad D a = childEnergy e rad D a := by
  dsimp only
  unfold childEnergy
  apply tsum_congr
  intro z
  exact congrArg₂ (fun x y : ℂ => rad.weight z * (‖x‖ ^ 2 + ‖y‖ ^ 2))
    (allocated_row_active s C R B τ v D a z s.W₁ s.W₂
      (s.X₁ / Ideal.absNorm (B.val (Sum.inr 0)))
      (s.X₂ / Ideal.absNorm (B.val (Sum.inr 1))))
    (allocated_row_active s C R B τ v D a z s.W₁ s.W₂
      (s.Y₁ / Ideal.absNorm (B.val (Sum.inr 0)))
      (s.Y₂ / Ideal.absNorm (B.val (Sum.inr 1))))

end SevenEighths.CenteredMomentEnergyActiveChildRestoration

end

end OAI
end OAIOriginalModule2793

/-! Original module: OAI.NumberTheory.DirichletL.Energy.FirstRawScaleAdmission
Source SHA256: ce750ee0a5d87968fca4bdc9ec52a4fd73de905ccc28c29cb686c5a7a20dc5e1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2794



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyFirstRawScaleAdmission
open HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentEnergyAmplifiedRayDictionary CenteredMomentFirstAnnularInput
open CenteredMomentFirstChildLower CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α]
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _

def parentLower (s:Input α)(Z:ℝ):ℝ:=
  min (min (Real.logb Z s.X₁) (Real.logb Z s.X₂))
    (min (Real.logb Z s.Y₁) (Real.logb Z s.Y₂))

theorem parent_lower_scales (s:Input α)(Z:ℝ)(hZ:1<Z):
    Z^(parentLower s Z)≤s.X₁ ∧ Z^(parentLower s Z)≤s.X₂ ∧
    Z^(parentLower s Z)≤s.Y₁ ∧ Z^(parentLower s Z)≤s.Y₂:=by
  have h (X:ℝ)(hX:0<X)(hx:parentLower s Z≤Real.logb Z X):Z^(parentLower s Z)≤X:=by
    calc
      _≤Z^(Real.logb Z X):=Real.rpow_le_rpow_of_exponent_le hZ.le hx
      _=X:=Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hX
  exact ⟨h _ s.X₁_pos ((min_le_left _ _).trans (min_le_left _ _)),
    h _ s.X₂_pos ((min_le_left _ _).trans (min_le_right _ _)),
    h _ s.Y₁_pos ((min_le_right _ _).trans (min_le_left _ _)),
    h _ s.Y₂_pos ((min_le_right _ _).trans (min_le_right _ _))⟩

theorem main_minimum_lower (s:Input α)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t Z:ℝ)(hZ:1<Z):
    let d:=child s C R B τ t
    let r:=parentLower s Z-Real.logb Z (C.absNorm:ℝ)
    Z^r≤d.X₁ ∧ Z^r≤d.X₂ ∧ Z^r≤d.Y₁ ∧ Z^r≤d.Y₂:=by
  have h:=parent_lower_scales s Z hZ
  exact child_lower s C R hC B τ t Z (parentLower s Z) hZ h.1 h.2.1 h.2.2.1 h.2.2.2

theorem active_error_lower (s:Input α)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t:ℝ)(p:O)(hp:p≠0)(k:ℕ)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools ((Ideal.span {p})^k))
    (υ:Character)(v Z r:ℝ)(hZ:1<Z)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    let d:=child (activeInput (child s C R B τ t)) ((Ideal.span {p})^k) (R*C) Bp υ v
    let r':=r-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k
    Z^r'≤d.X₁ ∧ Z^r'≤d.X₂ ∧ Z^r'≤d.Y₁ ∧ Z^r'≤d.Y₂:=by
  have hc:=child_lower s C R hC B τ t Z r hZ hX₁ hX₂ hY₁ hY₂
  have hpn:(Ideal.span {p}:Ideal O)≠0:=Ideal.span_singleton_eq_bot.not.mpr hp
  have hh:=child_lower (activeInput (child s C R B τ t)) ((Ideal.span {p})^k) (R*C)
    (pow_ne_zero k hpn) Bp υ v Z (r-Real.logb Z (C.absNorm:ℝ)) hZ
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  have he:Real.logb Z (((Ideal.span {p}:Ideal O)^k).absNorm:ℝ)=errorRemoval p Z k:=by
    rw [map_pow,Nat.cast_pow,Real.logb_pow]
    rfl
  simpa only [he] using hh

theorem restored_error_lower (s:Input α)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t:ℝ)(p:O)(hp:p≠0)(k:ℕ)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools ((Ideal.span {p})^k))
    (υ:Character)(v Z r:ℝ)(hZ:1<Z)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    let d:=restoredError s C R B τ t (Ideal.span {p}) k Bp υ v
    let r':=r-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k
    Z^r'≤d.X₁ ∧ Z^r'≤d.X₂ ∧ Z^r'≤d.Y₁ ∧ Z^r'≤d.Y₂:=by
  exact active_error_lower s C R hC B τ t p hp k Bp υ v Z r hZ hX₁ hX₂ hY₁ hY₂

theorem error_minimum_lower (s:Input α)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t:ℝ)(p:O)(hp:p≠0)(k:ℕ)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools ((Ideal.span {p})^k))
    (υ:Character)(v Z:ℝ)(hZ:1<Z):
    let d:=child (activeInput (child s C R B τ t)) ((Ideal.span {p})^k) (R*C) Bp υ v
    let r':=parentLower s Z-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k
    Z^r'≤d.X₁ ∧ Z^r'≤d.X₂ ∧ Z^r'≤d.Y₁ ∧ Z^r'≤d.Y₂:=by
  have h:=parent_lower_scales s Z hZ
  exact active_error_lower s C R hC B τ t p hp k Bp υ v Z (parentLower s Z) hZ
    h.1 h.2.1 h.2.2.1 h.2.2.2

end SevenEighths.CenteredMomentEnergyFirstRawScaleAdmission

end

end OAI
end OAIOriginalModule2794

/-! Original module: OAI.NumberTheory.DirichletL.Energy.NaturalInputMatches
Source SHA256: cfd5e4d5686458f461149cae45783c954f0f9e1b96206a7f9d3db1ce1d87726c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2795



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyNaturalInputMatches
open HeckeFamily HeckePrimeAnnular CenteredMomentPrimeSlot
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonRadialData CenteredMomentNaturalFixedRaySource
open CenteredMomentInductionEnergy CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
local notation "O" => HeckeFamily.O

def profile (W : ℝ → ℂ) (σ freq y : ℝ) : ℂ :=
  W y * (y : ℂ)^(-HeckeDyadic.shift σ freq)

lemma profile_support (W : ℝ → ℂ) (a b : ℝ)
    (hWs : Function.support W ⊆ Set.Icc a b) (σ freq : ℝ) :
    Function.support (profile W σ freq) ⊆ Set.Icc a b := by
  intro y hy
  apply hWs
  intro hz
  exact hy (by simp only [profile, hz, zero_mul])

lemma profile_zero (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) (σ freq : ℝ) :
    profile W σ freq 0 = 0 := by
  by_contra hn
  exact (not_le_of_gt ha) ((profile_support W a b hWs σ freq hn).1)

lemma profile_norm (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) (σ freq y : ℝ) :
    ‖profile W σ freq y‖ = ‖W y‖ * y^(-σ) := by
  by_cases hz : W y = 0
  · simp only [profile, hz, zero_mul, norm_zero]
  · have hy : 0 < y := ha.trans_le (hWs hz).1
    simp only [profile, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy,
      Complex.neg_re, HeckeDyadic.shift_re]

theorem exists_profile_bound (W : ℝ → ℂ) (hW : Continuous W)
    (a b lo hi : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ σ ∈ Set.Icc lo hi, ∀ freq y : ℝ,
      ‖profile W σ freq y‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := fixed_profile_norm_bound W hW a b lo hi ha
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro σ hσ freq y
  by_cases hz : W y = 0
  · simpa only [profile, hz, zero_mul, norm_zero] using
      (zero_le_one.trans (le_max_left 1 C))
  · rw [profile_norm W a b ha hWs]
    exact (hb σ hσ y (hWs hz)).trans (le_max_right _ _)

def profileBound (W : ℝ → ℂ) (hW : Continuous W)
    (a b lo hi : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) : ℝ :=
  (exists_profile_bound W hW a b lo hi ha hWs).choose

lemma profileBound_ge_one (W : ℝ → ℂ) (hW : Continuous W)
    (a b lo hi : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) :
    1 ≤ profileBound W hW a b lo hi ha hWs :=
  (exists_profile_bound W hW a b lo hi ha hWs).choose_spec.1

lemma norm_profile_le (W : ℝ → ℂ) (hW : Continuous W)
    (a b lo hi : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b)
    (σ : ℝ) (hσ : σ ∈ Set.Icc lo hi) (freq y : ℝ) :
    ‖profile W σ freq y‖ ≤ profileBound W hW a b lo hi ha hWs :=
  (exists_profile_bound W hW a b lo hi ha hWs).choose_spec.2 σ hσ freq y

section Input
variable {ι : Type*} [Fintype ι]
variable (Q : Ideal O) [NeZero Q]
local instance : Finite (O ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne Q)
variable (H : Subgroup (O ⧸ Q)ˣ) (hH : RayOrthogonality.globalUnits Q ≤ H)
variable (η₀ : Character) (θ : ι → RayQuotient.Characters Q H)
variable (W : ℝ → ℂ) (hW : Continuous W)
variable (aslot bslot lo hi : ℝ) (haslot : 0 < aslot)
variable (hWs : Function.support W ⊆ Set.Icc aslot bslot)
variable (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)
variable {Z Bmask bΦ a b : ℝ}
variable (state : NaturalState Z Bmask bΦ) (p : Profiles a b) (ha : 0 < a)
variable (t X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
variable (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hsame : Y₁ * Y₂ = X₁ * X₂)

def input : Input ι :=
  CenteredMomentEnergyOriginalSource.naturalInput state p ha
    (fun i => primePool Q H bslot (Z^(w i)))
    (fun _ _ hI => (Finset.mem_filter.mp hI).2.1)
    (fun i => relativeCharacter Q H hH η₀ (θ i))
    (fun i => profile W (σ i) (freq i)) (fun i => Z^(w i))
    (fun _ => profileBound W hW aslot bslot lo hi haslot hWs)
    (fun _ => Real.rpow_pos_of_pos (zero_lt_one.trans_le state.base_ge_one) _)
    (fun _ => profileBound_ge_one W hW aslot bslot lo hi haslot hWs)
    aslot bslot haslot (fun i => profile_support W aslot bslot hWs (σ i) (freq i))
    (fun i => norm_profile_le W hW aslot bslot lo hi haslot hWs (σ i) (hσ i) (freq i))
    t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame

local notation "inp" => input Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame

theorem input_matches :
    CenteredMomentAllocatedRayDictionary.Matches Q H hH inp η₀ θ w σ freq W bslot Z := by
  constructor <;> intros <;> rfl

lemma lower_eq : (inp).lower = aslot := rfl
lemma upper_eq : (inp).upper = bslot := rfl
lemma slot_control_eq (i : ι) :
    (inp).M i = profileBound W hW aslot bslot lo hi haslot hWs := rfl
lemma character_eq : (inp).η = state.character := rfl
lemma mask_eq : (inp).m = state.mask := rfl
lemma height_eq : (inp).t = t := rfl
lemma first_rectangle_eq : (inp).X₁ = X₁ ∧ (inp).X₂ = X₂ := ⟨rfl, rfl⟩
lemma second_rectangle_eq : (inp).Y₁ = Y₁ ∧ (inp).Y₂ = Y₂ := ⟨rfl, rfl⟩

theorem coefficient_eq (i : ι) (I : Ideal O) :
    (inp).toData.coefficient i I =
      idealCoeff (relativeCharacter Q H hH η₀ (θ i)) I *
        annularWeight W (Z^(w i)) (σ i) (freq i) I := rfl

theorem positive_row_eq (z : O) :
    positiveSlotRow (inp).η state.mask 1 z (inp).W₁ (inp).W₂ (inp).slots
      (inp).toData.coefficient (inp).P (inp).t (inp).X₁ (inp).X₂ =
    positiveSlotRow state.character state.mask 1 z (p.profile 0) (p.profile 1)
      (fun i => primePool Q H bslot (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter Q H hH η₀ (θ i)) I *
        annularWeight W (Z^(w i)) (σ i) (freq i) I)
      (fun i => Z^(w i)) t X₁ X₂ := rfl

theorem energy_eq :
    energy (inp).η state.mask 1 (inp).t (inp).W₁ (inp).W₂ (inp).slots
      (inp).toData.coefficient (inp).P (inp).X₁ (inp).X₂
      state.radial.keep state.radial.profile state.radial.scale =
    energy state.character state.mask 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool Q H bslot (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter Q H hH η₀ (θ i)) I *
        annularWeight W (Z^(w i)) (σ i) (freq i) I)
      (fun i => Z^(w i)) X₁ X₂
      state.radial.keep state.radial.profile state.radial.scale := rfl

theorem reference_energy_eq :
    energy (inp).η state.mask 1 (inp).t (inp).W₁ (inp).W₂ (inp).slots
      (inp).toData.coefficient (inp).P (inp).Y₁ (inp).Y₂
      state.radial.keep state.radial.profile state.radial.scale =
    energy state.character state.mask 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool Q H bslot (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter Q H hH η₀ (θ i)) I *
        annularWeight W (Z^(w i)) (σ i) (freq i) I)
      (fun i => Z^(w i)) Y₁ Y₂
      state.radial.keep state.radial.profile state.radial.scale := rfl

end Input
end SevenEighths.CenteredMomentEnergyNaturalInputMatches

end

end OAI
end OAIOriginalModule2795

/-! Original module: OAI.NumberTheory.DirichletL.Energy.OriginalProfileControl
Source SHA256: 9a1026f36c39af9f01ea069d12ddd5203a40a93018c66874644647db11e06fc4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2796





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyOriginalProfileControl
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentFiniteProfileExceptional
open CenteredMomentSourceInputTailUniform CenteredMomentFirstReferenceEnergy
open CenteredMomentEnergyZeroComparison CenteredMomentEnergyNaturalInputMatches
open CenteredMomentEnergyState CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalSource
variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [DecidableEq ι] in
lemma slot_product_le (s:Input ι)(N:ℕ)(C:ℝ)(hC:1≤C)
    (hN:Fintype.card ι≤N)(hM:∀i,s.M i≤C): (∏i,s.M i)≤C^N := by
  calc
    _≤∏_i:ι,C:=Finset.prod_le_prod₀ (fun i _=>(s.M_ge_one i).trans' zero_le_one) (fun i _=>hM i)
    _=C^(Fintype.card ι):=by simp
    _≤C^N:=pow_le_pow_right₀ hC hN

omit [DecidableEq ι] in
lemma plain_control_le {a b:ℝ}(s:Input ι)(p:Profiles a b)(S:Finset (ℕ×ℕ))
    (N:ℕ)(C:ℝ)(hC:1≤C)(hN:Fintype.card ι≤N)(hM:∀i,s.M i≤C):
    plainControl s (p.profile 0) (p.profile 1)≤C^N*p.control (insert (0,0) S) := by
  have h0 (i:Fin 2):SchwartzMap.seminorm ℝ 0 0 (p.profile i)≤
      sourceControl (insert (0,0) S) (p.profile i):=
    Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ)
      (s:=insert (0,0) S) (i:=(0,0)) (x:=p.profile i) (Finset.mem_insert_self _ _)
  have hpair:=mul_le_mul (h0 0) (h0 1) (apply_nonneg _ _) (sourceControl_nonneg _ _)
  have hh:=mul_le_mul (slot_product_le s N C hC hN hM) hpair
    (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) (pow_nonneg (by linarith) _)
  simpa only [plainControl,Profiles.control,mul_assoc] using hh

omit [DecidableEq ι] in
lemma plain_control_sq_le {a b:ℝ}(s:Input ι)(p:Profiles a b)(S:Finset (ℕ×ℕ))
    (N:ℕ)(C:ℝ)(hC:1≤C)(hN:Fintype.card ι≤N)(hM:∀i,s.M i≤C):
    (plainControl s (p.profile 0) (p.profile 1))^2≤C^(2*N)*(p.control (insert (0,0) S))^2 := by
  have hh:=pow_le_pow_left₀ (plainControl_nonneg _ _ _) (plain_control_le s p S N C hC hN hM) 2
  simpa only [mul_pow,←pow_mul,Nat.mul_comm N 2] using hh

omit [DecidableEq ι] in
lemma zero_plain_control (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)(W₁ W₂:𝓢(ℝ,ℂ)):
    plainControl (zeroInput s hz₁ hz₂) W₁ W₂=plainControl s W₁ W₂:=rfl

omit [DecidableEq ι] in
lemma lower_product (s:Input ι)(N:ℕ)(a:ℝ)(ha:0<a)
    (hN:Fintype.card ι≤N)(hlo:∀i,a≤s.lo i):
    (min 1 a)^N≤∏i,s.lo i := by
  have hm:0≤min 1 a:=le_min zero_le_one ha.le
  calc
    _≤(min 1 a)^(Fintype.card ι):=pow_le_pow_of_le_one hm (min_le_left _ _) hN
    _=∏_i:ι,min 1 a:=by simp
    _≤∏i,s.lo i:=Finset.prod_le_prod₀ (fun _ _=>hm) (fun i _=>(min_le_right _ _).trans (hlo i))

omit [DecidableEq ι] in
lemma source_factor_le (s:Input ι)(N:ℕ)(aslot a K:ℝ)(hs:0<aslot)(ha:0<a)(hK:0<K)
    (hN:Fintype.card ι≤N)(hlo:∀i,aslot≤s.lo i):
    sourceFactor s a a K≤
      (Real.exp (Real.log 4)*fixedPresentationCost/((min 1 aslot)^N*a*a))*K*(s.η.modulus.absNorm:ℝ) := by
  have hd:0<(min 1 aslot)^N*a*a:=by positivity
  have hprod:=lower_product s N aslot hs hN hlo
  have hden:(min 1 aslot)^N*a*a≤(∏i,s.lo i)*a*a:=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprod ha.le) ha.le
  have hdiv:=div_le_div_of_nonneg_left (Real.exp_pos (Real.log 4)).le hd hden
  have hc:=fixedPresentationCost_pos
  have hn:0≤(s.η.modulus.absNorm:ℝ):=Nat.cast_nonneg _
  have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hdiv hc.le) hK.le) hn
  unfold sourceFactor
  convert hh using 1 ; ring

local notation "O"=>HeckeFamily.O
section Input
variable {ι : Type*} [Fintype ι]
variable (Q : Ideal O) [NeZero Q]
local instance : Finite (O ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne Q)
variable (H : Subgroup (O ⧸ Q)ˣ) (hH : RayOrthogonality.globalUnits Q ≤ H)
variable (η₀ : Character) (θ : ι → RayQuotient.Characters Q H)
variable (W : ℝ → ℂ) (hW : Continuous W)
variable (aslot bslot lo hi : ℝ) (haslot : 0 < aslot)
variable (hWs : Function.support W ⊆ Set.Icc aslot bslot)
variable (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)
variable {Z Bmask bΦ a b : ℝ}
variable (state : NaturalState Z Bmask bΦ) (p : Profiles a b) (ha : 0 < a)
variable (t X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
variable (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hsame : Y₁ * Y₂ = X₁ * X₂)

local notation "inp" => CenteredMomentEnergyNaturalInputMatches.input Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame

theorem natural_plain_control (N:ℕ)(hN:Fintype.card ι≤N)(S:Finset (ℕ×ℕ)):
    (plainControl inp (p.profile 0) (p.profile 1))^2≤
      (profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2 :=
  plain_control_sq_le inp p S N _
    (profileBound_ge_one W hW aslot bslot lo hi haslot hWs) hN (fun _=>le_refl _)

theorem natural_zero_plain_control (N:ℕ)(hN:Fintype.card ι≤N)(S:Finset (ℕ×ℕ))
    (hz₁:(inp).W₁ 0=0)(hz₂:(inp).W₂ 0=0):
    (plainControl (zeroInput inp hz₁ hz₂) (p.profile 0) (p.profile 1))^2≤
      (profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2 :=
  plain_control_sq_le (zeroInput inp hz₁ hz₂) p S N _
    (profileBound_ge_one W hW aslot bslot lo hi haslot hWs) hN (fun _=>le_refl _)

theorem natural_source_factor (N:ℕ)(hN:Fintype.card ι≤N)(K:ℝ)(hK:0<K):
    sourceFactor inp a a K≤
      (Real.exp (Real.log 4)*fixedPresentationCost/((min 1 aslot)^N*a*a))*K*
        (state.character.modulus.absNorm:ℝ) :=
  source_factor_le inp N aslot a K haslot ha hK hN (fun _=>le_refl _)

theorem natural_zero_source_factor (N:ℕ)(hN:Fintype.card ι≤N)(K:ℝ)(hK:0<K)
    (hz₁:(inp).W₁ 0=0)(hz₂:(inp).W₂ 0=0):
    sourceFactor (zeroInput inp hz₁ hz₂) a a K≤
      (Real.exp (Real.log 4)*fixedPresentationCost/((min 1 aslot)^N*a*a))*K*
        (state.character.modulus.absNorm:ℝ) :=
  source_factor_le (zeroInput inp hz₁ hz₂) N aslot a K haslot ha hK hN (fun _=>le_refl _)

end Input
end SevenEighths.CenteredMomentEnergyOriginalProfileControl

end

end OAI
end OAIOriginalModule2796

/-! Original module: OAI.NumberTheory.DirichletL.Energy.NaturalLowSourceBound
Source SHA256: 38c22046b05e8f8d25d8169ba8afd2f5dcc784ebee61945f25d317cbc112c263
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2797




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalLowSourceBound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentEnergyNaturalInputMatches
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyZeroComparison CenteredMomentEnergyOriginalProfileControl
open CenteredMomentEnergyLowFixedRadialEntry CenteredMomentEnergyInputParentCapacity
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentAmplificationChildInput CenteredMomentInductionEnergy
open CenteredMomentEnergyBands CenteredMomentSecondHeightFamily
open CenteredMomentPrimeSlot CenteredMomentNaturalFixedRaySource HeckeDyadic HeckePrimeAnnular
local notation "O" => HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=
  CenteredMomentEnergyOriginalSource.energyOriginalSourceDecidableSum

section Source
variable (Q:Ideal O)[NeZero Q]
variable (H:Subgroup (O⧸Q)ˣ)(hH:RayOrthogonality.globalUnits Q≤H)
variable (η₀:Character)(θ:ι→RayQuotient.Characters Q H)
variable (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:ι→ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(state:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

def sourceInput : Input ι :=
  input Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
    state p ha t X₁ X₂ X₁ X₂ hX₁ hX₂ hX₁ hX₂ rfl

def zeroSourceInput : Input ι :=
  zeroInput (sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂)
    (CenteredMomentDetectorPlainSource.support_zero _ a b ha (p.support 0))
    (CenteredMomentDetectorPlainSource.support_zero _ a b ha (p.support 1))
end Source

private lemma control_mono {a b:ℝ}(p:Profiles a b)(S:Finset (ℕ×ℕ)):
    p.control S≤p.control (insert (0,0) S):=by
  unfold Profiles.control
  exact mul_le_mul
    (Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert _ _)) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert _ _)) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

theorem natural_low_source_bound
    (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi a b bΦ Mcap εdiag ξ saving:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤bslot)(ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hMcap:0≤Mcap)
    (hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∃Cfixed:ℝ,0<Cfixed ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(Q:Ideal O)[NeZero Q](H:Subgroup (O⧸Q)ˣ)(hH:RayOrthogonality.globalUnits Q≤H),
    ∀(η₀:Character)(θ:ι→RayQuotient.Characters Q H),
    ∀(w σ freq:ι→ℝ), (∀i,0≤w i) → ∀hσ:∀i,σ i∈Set.Icc lo hi,
    ∀(Bmask:ℝ)(state:NaturalState Z Bmask bΦ)(p:Profiles a b)(t X₁ X₂:ℝ),
    ∀hX₁:0<X₁,∀hX₂:0<X₂,∀κ:ℝ,1/6≤κ →
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤Mcap →
    ∀(S:Finset (ℕ×ℕ))(J:ℕ)(Cphysical height e:ℝ),0≤Cphysical →0≤height →
    εdiag≤e → -saving≤e →
    physicalMass (zeroSourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂) state.puncture 1 fixedBadMask 1
      Ψ state.radial.scale Z ξ /
      volume (sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
        w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂) ≤
      Cphysical*(p.control S)^2*(1+|t|+height)^J*Z^(state.width+e) →
    energy state.character state.mask 1 t (p.profile 0) (p.profile 1)
      (fun i=>primePool Q H bslot (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter Q H hH η₀ (θ i)) I*
        annularWeight W (Z^(w i)) (σ i) (freq i) I)
      (fun i=>Z^(w i)) X₁ X₂ state.radial.keep state.radial.profile state.radial.scale ≤
      Cfixed*(Cphysical+1)*diagonalControl state.radial.profile*
        (p.control (insert (0,0) S))^2*(1+|t|+height)^J*Z^(state.width+e):=by
  obtain ⟨Ψ,hΨs,hΨn,Sd,St,Cd,Ct,hCd,hCt,hred⟩:=
    original_low_reduction (ι:=ι) bΦ hbΦ (fun _=>bslot) a b Mcap εdiag ξ saving
      (fun _=>hbslot) ha hb hMcap hεdiag hξ
  let P:ℝ:=(profileBound W hW aslot bslot lo hi haslot hWs)^(2*Fintype.card ι)
  let D:ℝ:=Cd*P*Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  let T:ℝ:=Ct*P*St.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  have hP:0≤P:=pow_nonneg (zero_le_one.trans (profileBound_ge_one W hW aslot bslot lo hi haslot hWs)) _
  have hD:0≤D:=by dsimp [D];positivity
  have hT:0≤T:=by dsimp [T];positivity
  refine ⟨Ψ,hΨs,hΨn,2*(1+D+T),by positivity,?_⟩
  filter_upwards [hred] with Z hz
  refine ⟨hz.1,?_⟩
  intro Q _ H hH η₀ θ w σ freq hw hσ Bmask state p t X₁ X₂ hX₁ hX₂ κ hκ hcap
    S J Cphysical height e hCphysical hheight he hsave hphysical
  let s:=sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂
  have hZ:0<Z:=zero_lt_one.trans hz.1
  have hPi:∀i,1≤s.P i:=fun i=>Real.one_le_rpow hz.1.le (hw i)
  have hv:volume s≤Z^Mcap:=original_volume_cap s Z κ Mcap hz.1 hκ hPi (by
    change length Z X₁+length Z X₂+6*κ*(∑i,Real.logb Z (Z^(w i)))≤Mcap
    simpa only [Real.logb_rpow hZ hz.1.ne'] using hcap)
  have hscale:1≤state.radial.scale:=by rw [state.scale_eq];exact Real.one_le_rpow hz.1.le state.row_nonneg
  have hKi:state.radial.scale⁻¹≤Z^Mcap:=
    (inv_le_one_of_one_le₀ hscale).trans (Real.one_le_rpow hz.1.le hMcap)
  have hbound:=hz.2 s (p.profile 0) (p.profile 1) rfl rfl (p.support 0) (p.support 1)
    (fun _=>le_rfl) state.puncture state.radial state.radial_support hv hKi
  have hplain:(plainControl s (p.profile 0) (p.profile 1))^2≤P*(p.control (insert (0,0) S))^2:=
    plain_control_sq_le s p S (Fintype.card ι) _
      (profileBound_ge_one W hW aslot bslot lo hi haslot hWs) le_rfl (fun _=>le_rfl)
  have hsquare:(p.control S)^2≤(p.control (insert (0,0) S))^2:=
    pow_le_pow_left₀ (p.control_nonneg S) (control_mono p S) 2
  let F:ℝ:=(p.control (insert (0,0) S))^2*(1+|t|+height)^J*Z^(state.width+e)
  have hF:0≤F:=by dsimp [F];positivity
  have hheight1:1≤(1+|t|+height)^J:=one_le_pow₀ (by linarith [abs_nonneg t])
  have hscalePower (x:ℝ)(hx:x≤e):state.radial.scale*Z^x≤Z^(state.width+e):=by
    rw [state.scale_eq,←Real.rpow_add hZ]
    exact Real.rpow_le_rpow_of_exponent_le hz.1.le (by unfold NaturalState.width;linarith [state.character_nonneg])
  have hphysical':physicalMass (zeroSourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂) state.puncture 1 fixedBadMask 1
      Ψ state.radial.scale Z ξ/volume s≤Cphysical*F:=by
    apply hphysical.trans
    calc
      _≤Cphysical*(p.control (insert (0,0) S))^2*(1+|t|+height)^J*Z^(state.width+e):=by gcongr
      _=Cphysical*F:=by dsimp [F];ring
  have hterm (c A x:ℝ)(hc:0≤c)(hA:0≤A)(hx:x≤e):
      c*(plainControl s (p.profile 0) (p.profile 1))^2*A*state.radial.scale*Z^x≤c*P*A*F:=by
    calc
      _≤c*(P*(p.control (insert (0,0) S))^2)*A*(state.radial.scale*Z^x):=by
        rw [←mul_assoc];gcongr
      _≤c*(P*(p.control (insert (0,0) S))^2)*A*Z^(state.width+e):=by
        gcongr;exact hscalePower x hx
      _≤c*P*A*F:=by
        have hh:=le_mul_of_one_le_right
          (show 0≤c*P*A*(p.control (insert (0,0) S))^2*Z^(state.width+e) by positivity) hheight1
        dsimp [F]
        convert hh using 1 <;> ring
  have hd:=hterm Cd (Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) εdiag hCd.le (apply_nonneg _ _) he
  have ht:=hterm Ct (St.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) (-saving) hCt.le (apply_nonneg _ _) hsave
  change energy state.character state.mask 1 t (p.profile 0) (p.profile 1) _ _ _ _ _ _ _ _≤_ at hbound
  apply hbound.trans
  change 2*diagonalControl state.radial.profile*(_+_+_)≤_
  have hsum:=add_le_add (add_le_add hphysical' hd) ht
  have hmul:=mul_le_mul_of_nonneg_left hsum
    (mul_nonneg (by norm_num : (0:ℝ)≤2) (diagonalControl_nonneg state.radial.profile))
  apply hmul.trans
  dsimp only [D,T] at *
  have hcoeff:Cphysical+Cd*P*Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ+
      Ct*P*St.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ≤
      (1+Cd*P*Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ+
        Ct*P*St.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ)*(Cphysical+1):=by
    nlinarith [mul_nonneg hCphysical hD,mul_nonneg hCphysical hT]
  have hh:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoeff hF)
    (mul_nonneg (by norm_num : (0:ℝ)≤2) (diagonalControl_nonneg state.radial.profile))
  dsimp [F] at hh ⊢
  nlinarith only [hh]

end SevenEighths.CenteredMomentEnergyNaturalLowSourceBound

end

end OAI
end OAIOriginalModule2797

/-! Original module: OAI.NumberTheory.DirichletL.Energy.NaturalSourceAdmission
Source SHA256: b6007a32438984a06477d2716db23d9395778cb75d90caf117b048494e09b7c8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2798


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalSourceAdmission
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentEnergyNaturalInputMatches
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyZeroComparison
open CenteredMomentEnergyOriginalSource CenteredMomentEnergyOriginalProfileControl
open CenteredMomentEnergyInputParentCapacity CenteredMomentAmplificationChildInput
open CenteredMomentEnergyBands CenteredMomentSecondHeightFamily
open CenteredMomentPrimeSlot CenteredMomentNaturalFixedRaySource HeckeDyadic HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentSourceRow CenteredMomentRetainedEnergy
open CenteredMomentSourceInputTailUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentHeckeExpansion CenteredMomentHeckeHeight
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := energyOriginalSourceDecidableSum

def lowerProduct (N : ℕ) (aslot a : ℝ) : ℝ := (min 1 aslot)^N*a*a

lemma lowerProduct_pos (N : ℕ) {aslot a : ℝ} (hs : 0 < aslot) (ha : 0 < a) :
    0 < lowerProduct N aslot a := by unfold lowerProduct; positivity

section Source
variable (Q : Ideal O) [NeZero Q]
variable (H : Subgroup (O ⧸ Q)ˣ) (hH : RayOrthogonality.globalUnits Q ≤ H)
variable (η₀ : Character) (θ : ι → RayQuotient.Characters Q H)
variable (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi : ℝ)
variable (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
variable (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)
variable {Z Bmask bΦ a b : ℝ} (state : NaturalState Z Bmask bΦ)
variable (p : Profiles a b) (ha : 0 < a) (t X₁ X₂ : ℝ)
variable (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
local notation "s" => sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂
local notation "s₀" => zeroSourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂

theorem both_matches :
    CenteredMomentAllocatedRayDictionary.Matches Q H hH s η₀ θ w σ freq W bslot Z ∧
    CenteredMomentAllocatedRayDictionary.Matches Q H hH s₀ η₀ θ w σ freq W bslot Z := by
  constructor <;> constructor <;> intros <;> rfl

lemma source_fields :
    (s).η = state.character ∧ (s₀).η = state.character ∧
    (s).m = state.mask ∧ (s₀).m = state.mask ∧ (s).A = 1 ∧ (s₀).A = 1 ∧
    (s).t = t ∧ (s₀).t = t ∧
    (s).W₁ = p.profile 0 ∧ (s₀).W₁ = p.profile 0 ∧
    (s).W₂ = p.profile 1 ∧ (s₀).W₂ = p.profile 1 ∧
    (s).lower = aslot ∧ (s₀).lower = aslot ∧ (s).upper = bslot ∧ (s₀).upper = bslot := by
  repeat' constructor

lemma slot_fields (i : ι) :
    (s).P i = Z^(w i) ∧ (s₀).P i = Z^(w i) ∧
    (s).lo i = aslot ∧ (s₀).lo i = aslot ∧ (s).hi i = bslot ∧ (s₀).hi i = bslot ∧
    (s).M i = profileBound W hW aslot bslot lo hi haslot hWs ∧
    (s₀).M i = profileBound W hW aslot bslot lo hi haslot hWs ∧
    (s).slots i = primePool Q H bslot (Z^(w i)) ∧
    (s₀).slots i = primePool Q H bslot (Z^(w i)) := by repeat' constructor

lemma slot_coefficient (i : ι) (I : Ideal O) :
    (s).toData.coefficient i I = idealCoeff (relativeCharacter Q H hH η₀ (θ i)) I *
      annularWeight W (Z^(w i)) (σ i) (freq i) I ∧
    (s₀).toData.coefficient i I = (s).toData.coefficient i I := ⟨rfl, rfl⟩

lemma rectangles :
    (s).X₁ = X₁ ∧ (s).X₂ = X₂ ∧ (s).Y₁ = X₁ ∧ (s).Y₂ = X₂ ∧
    (s₀).X₁ = X₁ ∧ (s₀).X₂ = X₂ ∧
    (s₀).Y₁ = smallScale b ∧ (s₀).Y₂ = X₁*X₂/smallScale b ∧
    (s₀).Y₁*(s₀).Y₂ = X₁*X₂ := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  exact (s₀).same_product

lemma raw_volume : volume s = X₁*X₂*∏ i, Z^(w i) ∧ volume s₀ = volume s := ⟨rfl,rfl⟩

lemma volume_log (hZ : 1 < Z) :
    Real.logb Z (volume s) = Real.logb Z X₁ + Real.logb Z X₂ + ∑ i, w i ∧
    Real.logb Z (volume s₀) = Real.logb Z X₁ + Real.logb Z X₂ + ∑ i, w i := by
  have hh := input_volume_log s Z
  change Real.logb Z (volume s) = Real.logb Z X₁ + Real.logb Z X₂ +
    ∑ i, Real.logb Z (Z^(w i)) at hh
  simp only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  exact ⟨hh,hh⟩

theorem capacity_admission (hZ : 1 < Z) (hw : ∀ i, 0 ≤ w i) (κ : ℝ)
    (hκ : 1/6 ≤ κ)
    (hcap : length Z X₁ + length Z X₂ + 6*κ*(∑ i, w i) ≤ state.width) :
    (∀ i, 1 ≤ (s).P i ∧ 1 ≤ (s₀).P i) ∧
    volume s ≤ Z^state.width ∧ volume s₀ ≤ Z^state.width := by
  have hPi : ∀ i, 1 ≤ (s).P i := fun i => Real.one_le_rpow hZ.le (hw i)
  have hv := original_volume_cap s Z κ state.width hZ hκ hPi (by
    change length Z X₁ + length Z X₂ + 6*κ*(∑ i, Real.logb Z (Z^(w i))) ≤ _
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hcap)
  exact ⟨fun i => ⟨hPi i,hPi i⟩,hv,hv⟩

theorem low_admission (hZ : 1 < Z)
    (hlow : length Z X₁ + length Z X₂ + ∑ i, w i ≤ 5*state.width/6) :
    Real.logb Z (volume s) ≤ 5*state.width/6 ∧
    Real.logb Z (volume s₀) ≤ 5*state.width/6 := by
  have hv := volume_log Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂ hZ
  have h1 := raw_log_le_length Z X₁ hZ hX₁
  have h2 := raw_log_le_length Z X₂ hZ hX₂
  constructor <;> linarith [hv.1,hv.2]

theorem lower_product_admission (N : ℕ) (hN : Fintype.card ι ≤ N) :
    0 < lowerProduct N aslot a ∧
    lowerProduct N aslot a ≤ (∏ i, (s).lo i)*a*a ∧
    lowerProduct N aslot a ≤ (∏ i, (s₀).lo i)*a*a := by
  have hh := lower_product s N aslot haslot hN (fun _ => le_rfl)
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh ha.le) ha.le
  exact ⟨lowerProduct_pos N haslot ha,hb,hb⟩

theorem profile_control_admission (N : ℕ) (hN : Fintype.card ι ≤ N)
    (S : Finset (ℕ×ℕ)) :
    (plainControl s (p.profile 0) (p.profile 1))^2 ≤
      (profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2 ∧
    (plainControl s₀ (p.profile 0) (p.profile 1))^2 ≤
      (profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2 := by
  have hh := plain_control_sq_le s p S N _
    (profileBound_ge_one W hW aslot bslot lo hi haslot hWs) hN (fun _ => le_rfl)
  exact ⟨hh,hh⟩

theorem normalized_zero_source (R : Ideal O) (z : O) :
    positiveSlotRow state.character (fixedBadMask*idealGenerator R) 1 z
      (p.profile 0) (p.profile 1) (s).slots (s).toData.coefficient (s).P t X₁ X₂ =
    (Real.sqrt (volume s) : ℂ)⁻¹ *
      ∑ I ∈ finiteColumns (Fintype.piFinset (s₀).pools),
        CenteredMomentOriginalCommonHarmonic.coefficient s₀ R 1 I * rowWeight state.character fixedBadMask 1 z t I := by
  have hh := normalized_input_difference s₀ R z
  have hz := comparison_row_zero s
    (CenteredMomentDetectorPlainSource.support_zero _ a b ha (p.support 0))
    (CenteredMomentDetectorPlainSource.support_zero _ a b ha (p.support 1)) R z
  change positiveSlotRow state.character (fixedBadMask*idealGenerator R) 1 z
      (p.profile 0) (p.profile 1) (s).slots (s).toData.coefficient (s).P t X₁ X₂ -
    positiveSlotRow (s).η (fixedBadMask*idealGenerator R) 1 z (s).W₁ (s).W₂ (s).slots
      (s).toData.coefficient (s).P (s).t (s₀).Y₁ (s₀).Y₂ = _ at hh
  change positiveSlotRow (s).η (fixedBadMask*idealGenerator R) 1 z (s).W₁ (s).W₂ (s).slots
    (s).toData.coefficient (s).P (s).t (s₀).Y₁ (s₀).Y₂ = 0 at hz
  rw [hz,sub_zero] at hh
  exact hh

end Source

theorem radial_admission {Z Bmask bΦ : ℝ} (state : NaturalState Z Bmask bΦ) :
    1 ≤ state.radial.scale ∧ state.radial.scale⁻¹ ≤ 1 ∧
    state.radial.scale⁻¹ ≤ Z^state.width := by
  have hs : 1 ≤ state.radial.scale := by
    rw [state.scale_eq]
    exact Real.one_le_rpow state.base_ge_one state.row_nonneg
  have hi := inv_le_one_of_one_le₀ hs
  exact ⟨hs,hi,hi.trans (Real.one_le_rpow state.base_ge_one state.width_nonneg)⟩

theorem original_scale_caps {Z X₁ X₂ M L κ : ℝ} (w : ι → ℝ)
    (hZ : 1 < Z) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hw : ∀ i, 0 ≤ w i) (hκ : 1/6 ≤ κ)
    (hcap : length Z X₁ + length Z X₂ + 6*κ*(∑ i, w i) ≤ M)
    (hM : M ≤ L) : X₁ ≤ Z^L ∧ X₂ ≤ Z^L := by
  have hn : 0 ≤ 6*κ*(∑ i, w i) :=
    mul_nonneg (by linarith) (Finset.sum_nonneg (fun i _ => hw i))
  have h1 := raw_log_le_length Z X₁ hZ hX₁
  have h2 := raw_log_le_length Z X₂ hZ hX₂
  constructor
  · apply (Real.logb_le_iff_le_rpow hZ hX₁).mp
    linarith [length_nonneg Z X₂ hZ]
  · apply (Real.logb_le_iff_le_rpow hZ hX₂).mp
    linarith [length_nonneg Z X₁ hZ]

theorem eventually_scale_admission (b L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (ι : Type*) [Fintype ι] [DecidableEq ι],
    ∀ (Q : Ideal O) [NeZero Q] (H : Subgroup (O ⧸ Q)ˣ)
      (hH : RayOrthogonality.globalUnits Q ≤ H) (η₀ : Character)
      (θ : ι → RayQuotient.Characters Q H),
    ∀ (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi : ℝ)
      (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot),
    ∀ (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi),
    ∀ (Bmask bΦ a : ℝ) (state : NaturalState Z Bmask bΦ) (p : Profiles a b)
      (ha : 0 < a) (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (κ : ℝ),
    (∀ i, 0 ≤ w i) → 1/6 ≤ κ → state.width ≤ L →
    length Z X₁ + length Z X₂ + 6*κ*(∑ i, w i) ≤ state.width →
    let s := sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂
    let s₀ := zeroSourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂
    (s).X₁ ≤ Z^L ∧ (s).X₂ ≤ Z^L ∧ (s).Y₁ ≤ Z^L ∧ (s).Y₂ ≤ Z^L ∧
    (s₀).X₁ ≤ Z^L ∧ (s₀).X₂ ≤ Z^L ∧
    (s₀).Y₁ ≤ Z^(2*L+ε) ∧ (s₀).Y₂ ≤ Z^(2*L+ε) := by
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (2*max 1 b),
    eventually_gt_atTop (1 : ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro ι _ _ Q _ H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ Bmask bΦ a state p ha t X₁ X₂ hX₁ hX₂ κ hw hκ hM hcap
  dsimp only
  have hx := original_scale_caps w hZ hX₁ hX₂ hw hκ hcap hM
  refine ⟨hx.1,hx.2,hx.1,hx.2,hx.1,hx.2,?_,?_⟩
  · exact (smallScale_le_one b).trans (Real.one_le_rpow hZ.le (by positivity))
  · change X₁*X₂/smallScale b ≤ _
    have hp : X₁*X₂ ≤ Z^(2*L) := by
      have hh := mul_le_mul hx.1 hx.2 hX₂.le (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) L).le
      rw [←Real.rpow_add (zero_lt_one.trans hZ)] at hh
      simpa only [two_mul] using hh
    unfold smallScale
    rw [div_div_eq_mul_div,div_one]
    exact (mul_le_mul hp hc (by positivity)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).le).trans_eq
        (Real.rpow_add (zero_lt_one.trans hZ) _ _).symm

end SevenEighths.CenteredMomentEnergyNaturalSourceAdmission

end

end OAI
end OAIOriginalModule2798

/-! Original module: OAI.NumberTheory.DirichletL.Energy.PositiveHighSource
Source SHA256: 370cd3a1dc2e3c4647c4e9d5c8d7df570f19e2e7b30e416296fecf64cc67bb36
