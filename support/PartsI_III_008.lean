    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hν : 0<ν)
    (hlog : 0< logCost) (hMomentHeight : τ< heightCost)
    (ζ μ saving : ℝ) (hζ : 0<ζ) (hζ1 : ζ≤1/48) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (RHV2.h)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+(RHV2.ell)*mesh)+(logCost+heightCost+momentCost)+saving≤ HeckeZeroSupremum.beta-RHV2.boundary)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0< nu)
    (dyadCost : ℝ) (hdyadCost : 0< dyadCost)
    (hdmin1 : dmin<1/100) (hconductor : RHV2.h+ζ+2*margin≤ dmax)
    (hmuMargin : 2*margin≤μ)
    (hβ : (RHV2.boundary:ℝ)≤ HeckeZeroSupremum.beta)
    (sigma : ℝ) (hsigma : 0< sigma)
    (hgeometric : sigma+8*e+nu≤ RHV2.smallSaving) (hprincipal : sigma+nu≤1/3000)
    (hwindow : sigma+e≤(RHV2.boundary)*(dmax*rmin))
    (hfloorbudget : 2*ζ+26*e+(N+8)*eps+loss+(RHV2.ell)*mesh+nu+sigma≤1/200)
    (hcentral : sigma+nu+dyadCost≤ saving) (counts : ProbeFinalAssembly.CountParameters M H εm) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0< n ∧ ∃C : ℝ,
      0< C ∧
    ∀η : Character,∃Ct : ℝ,0< Ct ∧ ∀ᶠZ : ℝ in atTop,
      let Yp := fun j=> Z^(ell j)
      let T := fun j=> pool (RayQuotient.identityClass M H) S c b (Yp j)
      let _hT := v2_fixed_nonfloorPoolOutside M H S N c b Yp
      let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (RHV2.ell) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤ a ∧ a≤1 ∧
        a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ)< a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ)< a+2*e ∧
        (51/100< a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a≤ s.re ∧ s.re< a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((RHV2.h:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let rows := supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((RHV2.h:ℝ)+ζ))) grid
      ∀C0 : ℝ,0≤ C0 →
      (∀k∈smallDyadicIndices (Z^(RHV2.h+ζ)),∀i∈Finset.range (n+1),∀j∈Finset.range (⌊(49/100:ℝ)/e⌋₊+1),
        let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
        rows'.Nonempty → ∀t : HeightSpace,
        ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
        SourceMomentsAt M H hH S hS.prime η rows' ell WC Z
          (sourceDyadConductor Z margin k) (51/100+e*j) ε τ dmax b R mesh i
          ((17/50:ℂ)+t.1.2*Complex.I) (0:ℝ)
          (if 2*(51/100+e*j)-1≤5/6 then counts.cB else counts.cH)
          (if 2*(51/100+e*j)-1≤5/6 then counts.kB else counts.kH)
          (C0*Z^momentCost) (Z^heightCost) εm) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=> canonicalSlotSupport (T j)) WC Yp (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-(4+RHV2.b)/6) Z‖≤
        (Ct+C*C0*(η.modulus.absNorm:ℝ)^(2*eps))*Z^(RHV2.signalExponent HeckeZeroSupremum.beta-sigma) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hmin : 0< dmax*rmin := mul_pos (hdmin.trans_le hdRange) hrmin
  obtain ⟨n,hn,htransport⟩ := v2_actual_nonfloor_probe_transport M H hH N e (1/4) c b A ζ 1 τ (dmax*rmin) nu
    he he1 (by norm_num) (by norm_num) hζ hζ1 hτ hc hcb hA hmin hnu hβ S hS hmax hfirst
    ell hello hell hellsum W hW hcompact hWs hWB hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 sigma hsigma hgeometric hprincipal hwindow (by linarith only [hprincipal,RHV2.analytic_geometry.2.2.2.2.2.1])
    eps R dmin dmax rmin ε κ cost mesh margin loss heps hR hdmin hdmax hdRange hrmin hε hκ hcost hmesh hmargin
    hbudget hgap hheight hloss (by linarith) hello hellhi hfloorbudget
  obtain ⟨C,hC,hbound⟩ :=
    v2_fixed_actual_nonfloor_rows_saving M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm (0:ℝ) ν logCost heightCost momentCost hεm (by norm_num) (by norm_num) (by norm_num) hν hlog hMomentHeight
      ζ μ saving hζ.le (by linarith) hμ hcount hfinal W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      hr0 hr1 hp0 hp1 hn0 hn1 nu hnu ⌊(49/100:ℝ)/e⌋₊ dyadCost hdyadCost hdmin1 hconductor hmuMargin counts
  refine ⟨n,hn,C,hC,?_⟩
  intro η
  obtain ⟨Ct,hCt,htransport⟩ := htransport η
  refine ⟨Ct,hCt,?_⟩
  filter_upwards [htransport,hbound η,eventually_ge_atTop (1:ℝ)] with Z ht hb hZ
  dsimp only at ht ⊢
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,herror⟩ := ht
  refine ⟨hnorm,idx,grid,hlabels,hbins,hray,?_⟩
  intro C0 hC0 hmom
  let rows := supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((RHV2.h:ℝ)+ζ))) grid
  have hrows : ∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
      (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(RHV2.h+ζ) := by
    intro u hu
    rcases (mem_supportedNonfloorRows S hmax _ grid u).mp hu with ⟨hur,hcal,hg⟩
    have hh := mem_rowBand.mp hur
    exact ⟨hh.1,hh.2.1,hcal,hh.2.2.le⟩
  have hlabel : ∀u∈rows,idx u≤ n ∧ grid u≤⌊(49/100:ℝ)/e⌋₊ ∧ grid u≠0 ∧ 51/100+e*grid u≤11/12 := by
    intro u hu
    have hg : grid u≠0 := ((mem_supportedNonfloorRows S hmax _ grid u).mp hu).2.2
    have ha : 51/100<51/100+e*grid u := by
      have hgpos : (0:ℝ)< grid u := by exact_mod_cast Nat.pos_of_ne_zero hg
      nlinarith only [he,hgpos]
    obtain ⟨j,s,hz,hp,has,_⟩ := (hbins u).2.2.2.2.2 ha
    exact ⟨(hlabels u).2.1,(hlabels u).2.2.1,hg,
      v2_zero_bin_upper _ _ s (by linarith only [ha]) hz hp has⟩
  have hnext : ∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
      (3*(idx u+1:ℕ)*Z^τ)<51/100+e*grid u+2*e := fun u _=>(hbins u).2.2.2.2.1
  have hcurrent : ∀u∈rows,51/100+e*grid u≤ detectorMaximum
      (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*idx u:ℕ)*Z^τ) := by
    intro u hu
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using (hbins u).2.2.1
  have hglobal := (hb C0 hC0 rows hrows idx grid hlabel hnext hcurrent hmom).2
  have hexp : Z^(RHV2.signalExponent HeckeZeroSupremum.beta-saving+nu+dyadCost)≤
      Z^(RHV2.signalExponent HeckeZeroSupremum.beta-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hcentral' := hglobal.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  have hsum := (norm_add_le _ _).trans (add_le_add herror hcentral')
  simpa only [rows,sub_add_cancel,add_mul] using hsum


end

end RHZeroFreeExtension.AnalyticHigh

end LocalModule214
/- END RHZeroFreeExtension.analytic_high.V2FinalAssemblyHigh -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.V2FinalFixedHigh -/
section LocalModule215


noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace RHZeroFreeExtension.AnalyticHigh.V2
open OAI.SevenEighths.ProbeFinalAssembly
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison
open HeckeInverseAmplification HeckeDetectorPhysicalSelection HeckeDetectorFiberPartition
open ProbeMellinBoundary

theorem fixed_high_bound (hβ : (RHV2.boundary:ℝ) < HeckeZeroSupremum.beta)
    (D : HighData (HeckeZeroSupremum.beta-RHV2.boundary)) (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t) (τ : ℝ)
    (hτ : 0 < τ) (hτd : τ < (1/200:ℝ)/2) (hτcost : 4*τ < (1/200:ℝ)*D.cost)
    (hτt : τ < D.t) (hτ2 : 2*τ ≤ D.t) (hτeps : τ*(2+4*D.eps) < D.t) :
     ∃ C : ℝ,0 < C  ∧   ∀ η : Character, ∃ Ct : ℝ,0 < Ct  ∧   ∀ᶠ Z : ℝ in atTop,
       ∀ C0 : ℝ,0 ≤ C0  →  SourceMomentBound F counts η Z τ (C0*Z^D.t) (Z^(2*τ))  → 
      ‖F.probe η Z-HeckeSignal.signal (η.excludePrimes F.S F.exclusions.prime)
        (sourceCorrection η F.S) (-(4+RHV2.b)/6) Z‖ ≤ 
        (Ct+C*C0*(η.modulus.absNorm:ℝ)^(2*D.eps))*Z^(RHV2.signalExponent HeckeZeroSupremum.beta-D.sigma) := by
  let : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  have ht := D.t_pos
  have ht1 := D.t_small
  have hconductor : (RHV2.h:ℝ)+D.t+2*D.t ≤ 7/8 := by
    have hh : RHV2.h ≤ 5/6 := by v2_geometry
    linarith
  obtain ⟨n,hn,C,hC,hbound⟩ := v2_fixed_actual_high_probe_from_raw_moments F.modulus ⊤ le_top D.N
    D.e D.eps 1 2 1 D.t (1/200) (7/8) D.rmin τ D.ε D.κ D.cost D.t D.t D.t
    D.e_pos D.e_small D.eps_pos (by norm_num) (by norm_num) (by norm_num)
    ht.le (by norm_num) (by norm_num) (by norm_num) D.rmin_pos hτ D.epsilon_pos D.kappa_pos
    D.cost_pos.le ht D.phase_budget D.epsilon_gap ht (by linarith) hτeps
    F.S F.exclusions F.first F.maximal D.ell D.slots_injective
    (fun j=>(D.slots_bounds j).2.1) (fun j=>(D.slots_bounds j).2.2)
    (fun _=> F.w) (fun _=> F.support) (fun _=> F.smooth) (fun _=> F.bounded)
    (fun _=> F.compact) (fun _=> F.nonzero) D.slots_sum
    (by norm_num) D.epsilon_small D.kappa_small hτd hτcost (by linarith only [D.detector_budget])
    F.w F.smooth F.compact F.positive_support (fun y=>(F.bounded y).1) F.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num) F.support (fun y=>(F.bounded y).2)
    D.t D.t D.t (2*τ) D.t ht ht ht (by linarith)
    D.t (2*D.t) D.t ht (by linarith) (by positivity) D.count_budget (by linarith only [D.central_budget,hτ2,hβ])
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    (D.t/8) (by positivity) (D.t/8) (by positivity) (by norm_num) hconductor (by linarith) hβ.le
    D.sigma D.sigma_pos (D.geometric_budget.trans RHV2.smallSaving_lower) D.principal_budget D.window_budget D.floor_budget D.high_saving counts
  refine ⟨C,hC,?_⟩
  intro η
  obtain ⟨Ct,hCt,hb⟩ := hbound η
  refine ⟨Ct,hCt,?_⟩
  filter_upwards [hb,sourceDyad_geometry_eventually (1/200) (7/8) D.t (RHV2.h+D.t)
    (by norm_num) (by norm_num) ht hconductor,
    HeckeDyadic.constant_absorbed_eventually (3*(n:ℝ)+1) τ hτ,
    eventually_gt_atTop (1:ℝ)] with Z hb hgeo hnheight hZ
  intro C0 hC0 hmom
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,hestimate⟩ := hb
  apply hestimate C0 hC0
  intro k hk i hi j hj
  dsimp only
  intro hne t htheight
  let rows := supportedNonfloorRows F.S F.maximal (rowBand (Z^(1/100:ℝ)) (Z^((RHV2.h:ℝ)+D.t))) grid
  let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
  have hsub : rows'⊆rows∩dyadicRows 1 k := Finset.filter_subset _ _
  have hsubr : rows'⊆rows := hsub.trans Finset.inter_subset_left
  have hrows :  ∀ u∈rows,u.val≠1  ∧  Z^(1/100:ℝ) ≤ rowNorm u  ∧  rowNorm u ≤ Z^(RHV2.h+D.t) := by
    intro u hu
    have hh := mem_rowBand.mp ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu).1
    exact ⟨hh.1,hh.2.1,hh.2.2.le⟩
  have hg := hgeo rows hrows k (hne.mono hsub)
  obtain ⟨u,hu⟩ := hne
  have huj : grid u=j := ((mem_cubeBinRows _ idx grid i j u).mp hu).2.2
  have hjne : j≠0 := huj ▸ ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp (hsubr hu)).2.2
  have ha : (51/100:ℝ) < 51/100+D.e*j := by
    have hjp : (0:ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hjne
    nlinarith [D.e_pos]
  have ha' : (51/100:ℝ)+D.e*j ≤ 1 := by simpa only [huj] using (hbins u).2.1
  have hrow' :  ∀ v∈rows',v.val≠1  ∧  Z^(1/100:ℝ) ≤ rowNorm v  ∧ 
      (calibrationForSet F.S F.maximal).residueMonoid v.val≠0  ∧ 
      rowNorm v ≤ Z^(sourceDyadConductor Z D.t k-D.t) := by
    intro v hv
    exact ⟨(hrows v (hsubr hv)).1,(hrows v (hsubr hv)).2.1,
      ((mem_supportedNonfloorRows F.S F.maximal _ grid v).mp (hsubr hv)).2.1,hg.2.2.2.2.2 v (hsub hv)⟩
  have hi' : (i:ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hheight : (3*i+1:ℕ)*Z^τ ≤ Z^(2*τ) := by
    have hZp : 0 < Z := zero_lt_one.trans hZ
    calc
      _ ≤ (3*(n:ℝ)+1)*Z^τ := by push_cast;gcongr
      _ ≤ Z^τ*Z^τ := mul_le_mul_of_nonneg_right hnheight (by positivity)
      _=Z^(2*τ) := by rw [←Real.rpow_add hZp];congr 1;ring
  apply hmom rows' (sourceDyadConductor Z D.t k) (51/100+D.e*j) hg.2.2.1 hg.2.2.2.1 ha ha' hrow' i
    ((17/50:ℂ)+t.1.2*Complex.I)
  · simp
  · simpa using htheight.2.trans hheight

end RHZeroFreeExtension.AnalyticHigh.V2

end


#print axioms RHZeroFreeExtension.AnalyticHigh.V2.fixed_high_bound

end LocalModule215
/- END RHZeroFreeExtension.analytic_high.V2FinalFixedHigh -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.V2FinalChosenData -/
section LocalModule216


noncomputable section
open scoped Classical
open Filter

namespace RHZeroFreeExtension.AnalyticHigh.V2
open OAI.SevenEighths.ProbeFinalAssembly
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison

theorem chosen_data_height {Δ:ℝ}(D:HighData Δ)(F:SourceData D)
    (counts:CountParameters F.modulus ⊤ D.t)(J:ℝ)(hJ:0 ≤ J)
    (hbound: ∀ η:Character, ∃ C:ℝ,0 < C  ∧ 
       ∀ τ:ℝ,0 < τ → τ ≤ 1 →  ∀ᶠ Z:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))):
     ∃ τ:ℝ,0 < τ  ∧  τ < (1/200:ℝ)/2  ∧  4*τ < (1/200)*D.cost  ∧  τ < D.t  ∧ 
      2*τ ≤ D.t  ∧  τ*(2+4*D.eps) < D.t  ∧ 
       ∀ η:Character, ∃ C:ℝ,0 < C  ∧   ∀ᶠ Z:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*Z^D.t) (Z^(2*τ)):=by
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτJ,hτeps⟩:=D.height_choice J hJ
  have htau1:τ ≤ 1:=by linarith
  refine ⟨τ,hτ,hτd,hτcost,hτt,by nlinarith,hτeps,?_⟩
  intro η
  obtain ⟨C,hC,hbound⟩:=hbound η
  refine ⟨C*2^J,by positivity,?_⟩
  filter_upwards [hbound τ hτ htau1,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  exact hb.mono_constant (by linarith)
    (polynomial_height_absorption C Z τ J D.t hC.le hZ hτ.le hJ (by linarith))

theorem physical_probe_estimates_of_chosen_moments (hmom : ChosenMomentInput) :
    RHV2.PhysicalProbeEstimates := by
  intro hβ
  obtain ⟨D,F,counts,J,hJ,hmom⟩ := hmom hβ
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτ2,hτeps,hsource⟩ := chosen_data_height D F counts J hJ hmom
  obtain ⟨C,hC,hhigh⟩ := fixed_high_bound hβ D F counts τ hτ hτd hτcost hτt hτ2 hτeps
  let loss := (HeckeZeroSupremum.beta-RHV2.boundary)/2
  have hloss : 0 < loss := by dsimp [loss];linarith
  have hlossgap : loss < HeckeZeroSupremum.beta-RHV2.boundary := by dsimp [loss];linarith
  refine ⟨loss,D.sigma,hloss,hlossgap,D.sigma_pos,?_⟩
  intro η _hprimitive
  obtain ⟨hmask,_hOldAnalytic,_hOldBound⟩ :=
    ProbeFinalAssembly.actual_source_analytic F.S F.exclusions η
  refine ⟨η.excludePrimes F.S F.exclusions.prime,sourceCorrection η F.S,F.probe η,
    (-(4+RHV2.b)/6),hmask,?_,?_,?_,?_⟩
  · exact RHV2.source_analytic F.S F.exclusions η
  · exact RHV2.source_contraction F.S F.exclusions η
  · have hexp : (RHV2.boundary : ℝ)+(-(4+RHV2.b)/6)=RHV2.lowExponent := by rw [RHV2.lowExponent_signal];ring
    simpa only [hexp] using F.probe_low loss hloss η
  · obtain ⟨Ct,hCt,hhigh⟩ := hhigh η
    obtain ⟨Cm,hCm,hsource⟩ := hsource η
    apply isBigO_rpow_of_eventual_norm_bound
    refine ⟨Ct+C*Cm*(η.modulus.absNorm:ℝ)^(2*D.eps),by positivity,?_⟩
    filter_upwards [hhigh,hsource] with Z hh hs
    simpa only [RHV2.signalExponent, sub_eq_add_neg, neg_div] using hh Cm hCm.le hs

theorem beta_le_of_chosen_moments (hmom : ChosenMomentInput) :
    HeckeZeroSupremum.beta ≤ RHV2.boundary :=
  RHV2.beta_star_le_of_probes (physical_probe_estimates_of_chosen_moments hmom)

theorem beta_le_of_fine_moments (hmom : FineMomentInput) :
    HeckeZeroSupremum.beta ≤ (RHV2.boundary:ℝ) :=
  beta_le_of_chosen_moments (chosen_input_of_fine hmom)

end RHZeroFreeExtension.AnalyticHigh.V2
end
#print axioms RHZeroFreeExtension.AnalyticHigh.V2.physical_probe_estimates_of_chosen_moments
#print axioms RHZeroFreeExtension.AnalyticHigh.V2.beta_le_of_fine_moments

namespace RHZeroFreeExtension.AnalyticHigh.V2
/-- Assembly keeps the original headline only as an input needed to construct
the finite-kappa moment family; it is not the improved conclusion. -/
theorem beta_le_of_original_headline_and_fine_moment_construction
    (hOld : OAI.SevenEighths.HeckeZeroSupremum.beta ≤ (7/8 : ℝ))
    (hconstruct : OAI.SevenEighths.HeckeZeroSupremum.beta ≤ (7/8 : ℝ) → FineMomentInput) :
    OAI.SevenEighths.HeckeZeroSupremum.beta ≤ (RHV2.boundary : ℝ) :=
  beta_le_of_fine_moments (hconstruct hOld)
end RHZeroFreeExtension.AnalyticHigh.V2

end LocalModule216
/- END RHZeroFreeExtension.analytic_high.V2FinalChosenData -/

/- BEGIN original module RHZeroFreeExtension.V2FullVerification -/
section LocalModule217

/-! Full analytic assembly at the radical v2 geometry. The actual physical
probe estimates are constructed before deriving nonvanishing. No moment,
probe-estimate, or improved-boundary hypothesis is supplied to this entry. -/
namespace RHV2
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open RHZeroFreeExtension.AnalyticHigh.V2

 theorem physical_probe_estimates : PhysicalProbeEstimates :=
  physical_probe_estimates_of_chosen_moments
    (OAI.SevenEighths.V2ProbeFinalAssemblyCertifiedBands.chosen_moments_of_original_headline
      RHZeroFreeExtension.ActualOriginalBoundary.beta_le_seven_eighths)

 theorem beta_star_le : HeckeZeroSupremum.beta ≤ boundary :=
  beta_star_le_of_probes physical_probe_estimates

 theorem hecke_nonzero (chi : Character) (z : ℂ) (hz : boundary< z.re)
    (hpole : z≠1 ∨ chi.residue≠1) : LFunction chi z≠0 :=
  hecke_nonzero_of_probes physical_probe_estimates chi z hz hpole

 theorem dirichlet_nonzero (q : ℕ) (hq : q≠0) (chi : DirichletCharacter ℂ q) (z : ℂ)
    (hz : boundary< z.re) (hpole : ¬(chi=1 ∧ z=1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction chi z≠0 :=
  dirichlet_nonzero_of_probes physical_probe_estimates q hq chi z hz hpole

 theorem zeta_nonzero (z : ℂ) (hz : boundary< z.re) (hpole : z≠1) : riemannZeta z≠0 :=
  zeta_nonzero_of_probes physical_probe_estimates z hz hpole

#print axioms physical_probe_estimates
#print axioms beta_star_le
#print axioms hecke_nonzero
#print axioms dirichlet_nonzero
#print axioms zeta_nonzero
end
end RHV2

end LocalModule217
/- END RHZeroFreeExtension.V2FullVerification -/

/- BEGIN original module RHZeroFreeExtension.CombinedPaperVerification -/
section LocalModule218

/-! Correspondence entry for combine_v1.tex.  The definitions below use the
paper's r/new notation.  The zero-free statements are about the actual
upstream Hecke and Dirichlet L-functions, with principal poles excluded.
The analytic constructions are supplied by the full entries, not assumed.
This file does not claim that Lean parses or verifies the TeX prose. -/

namespace CombinedPaper
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily

def B_r : ℝ := 34999 / 40000
def b_r : ℝ := 1 / 8
def ell_r : ℝ := 1 / 6 + 1 / 10000
def B_new : ℝ := (1507 - 2 * Real.sqrt 921) / 1653
def b_new : ℝ := -4 / 29 + 230 * Real.sqrt 921 / 26709
def ell_new : ℝ := (33 + 8 * Real.sqrt 921) / 1653

theorem rational_parameters : b_r = RHLowGeometry.b ∧
    ell_r = RHLowGeometry.ell ∧ B_r = RHLowGeometry.beta0 := by
  norm_num [b_r, ell_r, B_r, RHLowGeometry.b, RHLowGeometry.ell,
    RHLowGeometry.beta0]

theorem algebraic_parameters : b_new = RHV2.b ∧
    ell_new = RHV2.ell ∧ B_new = RHV2.boundary := by
  exact ⟨rfl, rfl, rfl⟩

theorem balanced_signal_matching (b ell : ℝ) :
    (11 / 12 - ell / 4) - (4 + b) / 6 =
      ((1 - b - ell) / 2) / 2 + b / 12 := by
  ring

theorem rational_boundary : B_r = 11 / 12 - ell_r / 4 ∧
    (7 / 8 : ℝ) - B_r = 1 / 40000 := by
  norm_num [B_r, ell_r]

theorem algebraic_boundary : B_new = 11 / 12 - ell_new / 4 := by
  exact RHV2.boundary_identity

theorem boundary_order : B_new < B_r ∧ B_r < (7 / 8 : ℝ) := by
  constructor
  · exact RHV2.gate_v1_improvement
  · norm_num [B_r]

/-- Part I's original supremum conclusion. -/
theorem original_family_bound : HeckeZeroSupremum.beta ≤ (7 / 8 : ℝ) :=
  RHZeroFreeExtension.ActualOriginalBoundary.beta_le_seven_eighths

/-- The weaker 11/12 conclusion, asserted in Part I.  This is a deduction
from the original verified 7/8 conclusion, not a formalization of the
historical preliminary proof in Part I. -/
theorem preliminary_family_bound : HeckeZeroSupremum.beta ≤ (11 / 12 : ℝ) :=
  original_family_bound.trans (by norm_num)

/-- Part II, Theorem 15.1. -/
theorem rational_family_bound : HeckeZeroSupremum.beta ≤ B_r :=
  RHZeroFreeExtension.beta_star_le

theorem rational_hecke_nonzero (eta : Character) (s : ℂ)
    (hs : B_r < s.re) (hpole : s ≠ 1 ∨ eta.residue ≠ 1) :
    LFunction eta s ≠ 0 :=
  RHZeroFreeExtension.hecke_nonzero eta s hs hpole

theorem rational_dirichlet_nonzero (q : ℕ) (hq : q ≠ 0)
    (chi : DirichletCharacter ℂ q) (s : ℂ)
    (hs : B_r < s.re) (hpole : ¬ (chi = 1 ∧ s = 1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction chi s ≠ 0 :=
  RHZeroFreeExtension.dirichlet_nonzero q hq chi s hs hpole

theorem rational_zeta_nonzero (s : ℂ) (hs : B_r < s.re) (hpole : s ≠ 1) :
    riemannZeta s ≠ 0 :=
  RHZeroFreeExtension.zeta_nonzero s hs hpole

/-- Part III, Theorem 21.1, and the introductory main theorem. -/
theorem algebraic_family_bound : HeckeZeroSupremum.beta ≤ B_new :=
  RHV2.beta_star_le

theorem algebraic_hecke_nonzero (eta : Character) (s : ℂ)
    (hs : B_new < s.re) (hpole : s ≠ 1 ∨ eta.residue ≠ 1) :
    LFunction eta s ≠ 0 :=
  RHV2.hecke_nonzero eta s hs hpole

theorem algebraic_dirichlet_nonzero (q : ℕ) (hq : q ≠ 0)
    (chi : DirichletCharacter ℂ q) (s : ℂ)
    (hs : B_new < s.re) (hpole : ¬ (chi = 1 ∧ s = 1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction chi s ≠ 0 :=
  RHV2.dirichlet_nonzero q hq chi s hs hpole

theorem algebraic_zeta_nonzero (s : ℂ) (hs : B_new < s.re) (hpole : s ≠ 1) :
    riemannZeta s ≠ 0 :=
  RHV2.zeta_nonzero s hs hpole

/-- Part I's Hecke conclusion, with the pole condition made explicit. -/
theorem original_hecke_nonzero (eta : Character) (s : ℂ)
    (hs : (7 / 8 : ℝ) < s.re) (hpole : s ≠ 1 ∨ eta.residue ≠ 1) :
    LFunction eta s ≠ 0 := by
  apply rational_hecke_nonzero eta s (lt_trans boundary_order.2 hs) hpole

theorem original_dirichlet_nonzero (q : ℕ) (hq : q ≠ 0)
    (chi : DirichletCharacter ℂ q) (s : ℂ)
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (chi = 1 ∧ s = 1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction chi s ≠ 0 :=
  rational_dirichlet_nonzero q hq chi s (lt_trans boundary_order.2 hs) hpole

theorem original_zeta_nonzero (s : ℂ) (hs : (7 / 8 : ℝ) < s.re)
    (hpole : s ≠ 1) : riemannZeta s ≠ 0 :=
  rational_zeta_nonzero s (lt_trans boundary_order.2 hs) hpole

/-- Part II's uniform rational endpoint lemma. -/
theorem rational_endpoint (delta x : ℝ)
    (hd0 : 0 ≤ delta) (hd1 : delta ≤ 5 / 6)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    RHGeometry.E (5003 / 30000) delta x ≤ -(19 / 320000 : ℝ) := by
  simpa only [neg_div] using RHGeometry.perturbed_endpoint delta x hd0 hd1 hx0 hx1

/-- Part III's endpoint inequality. -/
theorem algebraic_endpoint (delta x : ℝ)
    (hd0 : 0 ≤ delta) (hd1 : delta ≤ 5 / 6)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) : RHV2.E delta x ≤ 0 :=
  RHV2.universal_endpoint delta x hd0 hd1 hx0 hx1

/-- The dual obstruction, retaining exactly its three numerical premises. -/
theorem scalar_obstruction (M ell B : ℝ)
    (h0 : 5 / 6 + M / 12 - ell / 6 ≤ B)
    (hK : 1 / 3 + 7 * M / 12 + ell / 3 ≤ B)
    (hH : 1 + RHV2.dc - (1 + RHV2.dc) * M / 2 + RHV2.dc * ell ≤ B) :
    B_new ≤ B := RHV2.closure_obstruction M ell B h0 hK hH

#print axioms rational_parameters
#print axioms algebraic_parameters
#print axioms balanced_signal_matching
#print axioms rational_boundary
#print axioms algebraic_boundary
#print axioms boundary_order
#print axioms original_family_bound
#print axioms preliminary_family_bound
#print axioms rational_family_bound
#print axioms rational_hecke_nonzero
#print axioms rational_dirichlet_nonzero
#print axioms rational_zeta_nonzero
#print axioms algebraic_family_bound
#print axioms algebraic_hecke_nonzero
#print axioms algebraic_dirichlet_nonzero
#print axioms algebraic_zeta_nonzero
#print axioms original_hecke_nonzero
#print axioms original_dirichlet_nonzero
#print axioms original_zeta_nonzero
#print axioms rational_endpoint
#print axioms algebraic_endpoint
#print axioms scalar_obstruction

end
end CombinedPaper

end LocalModule218
/- END RHZeroFreeExtension.CombinedPaperVerification -/
