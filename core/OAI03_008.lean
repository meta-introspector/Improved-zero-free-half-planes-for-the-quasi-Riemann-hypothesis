    (coeff.directionalSeries_continuousOn direction).comp
      (continuousOn_id.prodMk continuousOn_const) (fun v hv=>hv)
  apply (continuousOn_const.mul ((hd 1).sub (continuousOn_const.mul (hd Complex.I)))).congr
  intro v hv
  exact coeff.cuspZProfile_full_eq constant z v hv

end SubexponentialBesselCoefficients

lemma cuspBarProfile_source_continuousOn (z : ℂ) :
    ContinuousOn (cuspBarProfile cubicSourceResidualFunction z) (Set.Ioi 0) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.cuspBarProfile_continuousOn _ z

lemma cuspZProfile_source_continuousOn (z : ℂ) :
    ContinuousOn (cuspZProfile cubicSourceResidualFunction z) (Set.Ioi 0) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.cuspZProfile_continuousOn _ z

lemma cuspBarProfile_conjugate_eq (z : ℂ) :
    cuspBarProfile cubicSourceConjugateFunction z=fun v=>star (cuspZProfile cubicSourceResidualFunction z v) := by
  funext v
  exact horizontalWirtingerBar_star _ z

lemma cuspZProfile_conjugate_eq (z : ℂ) :
    cuspZProfile cubicSourceConjugateFunction z=fun v=>star (cuspBarProfile cubicSourceResidualFunction z v) := by
  funext v
  exact horizontalWirtingerZ_star _ z

lemma cuspBarProfile_conjugate_continuousOn (z : ℂ) :
    ContinuousOn (cuspBarProfile cubicSourceConjugateFunction z) (Set.Ioi 0) := by
  rw [cuspBarProfile_conjugate_eq]
  exact (cuspZProfile_source_continuousOn z).star

lemma cuspZProfile_conjugate_continuousOn (z : ℂ) :
    ContinuousOn (cuspZProfile cubicSourceConjugateFunction z) (Set.Ioi 0) := by
  rw [cuspZProfile_conjugate_eq]
  exact (cuspBarProfile_source_continuousOn z).star

lemma cuspBarProfile_source_isBigO (z : ℂ) :
    cuspBarProfile cubicSourceResidualFunction z =O[atTop]
      (fun v : ℝ=>Real.exp (-residualCuspDecayRate*v)) := by
  obtain ⟨C,hC,hbound⟩ := cubicSourceResidualFunction_wirtingerBar_cusp_decay 1 (by norm_num)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1:ℝ)] with v hv
  have hvp : 0<v := lt_of_lt_of_le (by norm_num) hv
  rw [cuspBarProfile_positive _ _ _ hvp,Real.norm_of_nonneg (Real.exp_pos _).le]
  exact hbound v hvp z hv

lemma cuspZProfile_source_isBigO (z : ℂ) :
    cuspZProfile cubicSourceResidualFunction z =O[atTop]
      (fun v : ℝ=>Real.exp (-residualCuspDecayRate*v)) := by
  obtain ⟨C,hC,hbound⟩ := cubicSourceResidualFunction_wirtingerZ_cusp_decay 1 (by norm_num)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1:ℝ)] with v hv
  have hvp : 0<v := lt_of_lt_of_le (by norm_num) hv
  rw [cuspZProfile_positive _ _ _ hvp,Real.norm_of_nonneg (Real.exp_pos _).le]
  exact hbound v hvp z hv

lemma cuspBarProfile_conjugate_isBigO (z : ℂ) :
    cuspBarProfile cubicSourceConjugateFunction z =O[atTop]
      (fun v : ℝ=>Real.exp (-residualCuspDecayRate*v)) := by
  obtain ⟨C,hC⟩ := Asymptotics.isBigO_iff.mp (cuspZProfile_source_isBigO z)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hC] with v hv
  simpa only [cuspBarProfile_conjugate_eq,norm_star] using hv

lemma cuspZProfile_conjugate_isBigO (z : ℂ) :
    cuspZProfile cubicSourceConjugateFunction z =O[atTop]
      (fun v : ℝ=>Real.exp (-residualCuspDecayRate*v)) := by
  obtain ⟨C,hC⟩ := Asymptotics.isBigO_iff.mp (cuspBarProfile_source_isBigO z)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hC] with v hv
  simpa only [cuspZProfile_conjugate_eq,norm_star] using hv

end CubicEisenstein

end

end OAI
end OAIOriginalModule0284

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.ConjugateCuspProfiles
Source SHA256: c935e1e023e9217bc4f2d5d0d4eea6537d5d9ad789f418566ce9e38a504fb3e3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0285



namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

theorem cuspBarProfile_conjugate_reflection (G : CubicKubota.levelThree)
    (g H : SL(2,ℂ)) (hfactor : g=complexMatrix G*H) (hc : g 1 0≠0)
    (v : ℝ) (hv : 0<v) :
    cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0) v=
      reflectedCuspProfile (-star (CubicKubota.complexCharacter G)/(g 1 0)^2)
        (‖g 1 0‖^2)
        (cuspZProfile (fun w=>cubicSourceConjugateFunction (H•w)) (-g 1 1/g 1 0)) v := by
  have hdual : 0<(‖g 1 0‖^2*v)⁻¹ := by positivity
  rw [cuspBarProfile_positive _ _ _ hv,reflectedCuspProfile,cuspZProfile_positive _ _ _ hdual]
  have he := cubicSourceConjugateFunction_cuspDerivative G g H hfactor hc v hv
  have hpow : (v:ℂ)^(-2:ℂ)=((v:ℂ)^2)⁻¹ := by
    rw [Complex.cpow_neg,Complex.cpow_ofNat]
  rw [hpow]
  simp only [one_div] at he
  rw [he]
  ring

theorem conjugateSource_principal_cusp_mellin_entire (G : CubicKubota.levelThree)
    (hc : complexMatrix G 1 0≠0) :
    (∀s : ℂ,MellinConvergent
      (cuspBarProfile cubicSourceConjugateFunction (complexMatrix G 0 0/complexMatrix G 1 0)) s) ∧
    Differentiable ℂ
      (mellin (cuspBarProfile cubicSourceConjugateFunction (complexMatrix G 0 0/complexMatrix G 1 0))) := by
  let g := complexMatrix G
  apply cusp_mellin_entire
    (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0))
    (cuspZProfile cubicSourceConjugateFunction (-g 1 1/g 1 0))
    (-star (CubicKubota.complexCharacter G)/(g 1 0)^2) (‖g 1 0‖^2)
    residualCuspDecayRate residualCuspDecayRate
  · change 0<‖complexMatrix G 1 0‖^2
    positivity
  · exact residualCuspDecayRate_pos
  · exact residualCuspDecayRate_pos
  · exact cuspBarProfile_conjugate_continuousOn _
  · exact cuspZProfile_conjugate_continuousOn _
  · exact cuspBarProfile_conjugate_isBigO _
  · exact cuspZProfile_conjugate_isBigO _
  · intro v hv
    simpa only [one_smul] using cuspBarProfile_conjugate_reflection G g 1 (by simp [g]) hc v hv

theorem conjugateSource_cusp_mellin_reflection (G : CubicKubota.levelThree)
    (g H : SL(2,ℂ)) (hfactor : g=complexMatrix G*H) (hc : g 1 0≠0) (s : ℂ) :
    mellin (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0)) (2*s)=
      (-star (CubicKubota.complexCharacter G)/(g 1 0)^2)*(‖g 1 0‖^2:ℝ)^(2-2*s:ℂ)*
        mellin (cuspZProfile (fun w=>cubicSourceConjugateFunction (H•w)) (-g 1 1/g 1 0)) (2-2*s) := by
  apply cusp_mellin_reflection_of_identity _ _ _ _ _ (by positivity)
  intro v hv
  exact cuspBarProfile_conjugate_reflection G g H hfactor hc v hv

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma cubicBesselIntegralDeriv_continuousAt (x : ℝ) (hx : 0<x) :
    ContinuousAt (fun y : ℝ=>∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv y t) x := by
  let delta := x/2
  have hdelta : 0<delta := half_pos hx
  apply continuousAt_of_dominated («μ» := volume.restrict (Set.Ioi (0:ℝ)))
    (bound:=fun t : ℝ=>(4/delta)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)))
  · exact Eventually.of_forall (fun y=>by unfold cubicBesselDensityDeriv cubicBesselDensity;fun_prop)
  · filter_upwards [Ioi_mem_nhds (show delta<x by dsimp [delta];linarith)] with y hy
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hyp : 0<y := hdelta.trans hy
    have htp : 0<t := ht
    calc
      _ ≤ (4/delta)*Real.exp (-y/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) :=
        cubicBesselDensityDeriv_bound delta y t hdelta hy.le ht
      _ ≤ _ := by
        have he : Real.exp (-y/2)≤1 := Real.exp_le_one_iff.mpr (by linarith)
        calc
          _ ≤ (4/delta)*1*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by gcongr
          _ = _ := by ring
  · exact cubicBesselDerivativeMajorant_integrable.const_mul (4/delta)
  · exact Eventually.of_forall (fun t=>by unfold cubicBesselDensityDeriv cubicBesselDensity;fun_prop)

lemma schlafliBesselK_cubic_derivative_continuousAt (x : ℝ) (hx : 0<x) :
    ContinuousAt schlafliBesselK_cubic_derivative x := by
  have hp4 : ContinuousAt (fun y : ℝ=>(y/2)^(-(4:ℝ)/3)) x :=
    (continuousAt_id.div_const 2).rpow_const (Or.inl (by positivity))
  have hp1 : ContinuousAt (fun y : ℝ=>(y/2)^(-(1:ℝ)/3)) x :=
    (continuousAt_id.div_const 2).rpow_const (Or.inl (by positivity))
  have hI := (cubicBesselIntegral_hasDerivAt x hx).continuousAt
  have hD := cubicBesselIntegralDeriv_continuousAt x hx
  apply Complex.continuous_ofReal.continuousAt.comp
  exact ((continuousAt_const.mul hp4).mul hI).add ((continuousAt_const.mul hp1).mul hD)

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma amplitudeDeriv_continuousAt (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) :
    ContinuousAt (fun y : ℝ=>coeff.amplitudeDeriv y h) v := by
  by_cases hh : h=0
  · simpa only [amplitudeDeriv,ite_eq_left hh] using (continuousAt_const (y:=(0:ℂ)) (x:=v))
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hK : ContinuousAt (fun y : ℝ=>schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*y)) v :=
    (schlafliBesselK_cubic_hasDerivAt _ (by positivity)).continuousAt.comp (by fun_prop)
  have hD : ContinuousAt (fun y : ℝ=>schlafliBesselK_cubic_derivative (4*Real.pi*‖cuspFrequency h‖*y)) v :=
    (schlafliBesselK_cubic_derivative_continuousAt _ (by positivity)).comp (by fun_prop)
  simp only [amplitudeDeriv,ite_eq_right hh]
  exact continuousAt_const.mul (hK.add ((Complex.continuous_ofReal.continuousAt.mul continuousAt_const).mul hD))

lemma termFDeriv_continuousAt (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) (hp : 0<p.1) :
    ContinuousAt (coeff.termFDeriv h) p := by
  by_cases hh : h=0
  · have he : coeff.termFDeriv h=fun _=>(0:(ℝ × ℂ)→L[ℝ]ℂ) := by
      funext q
      simp only [termFDeriv,ite_eq_left hh]
    rw [he]
    exact continuousAt_const
  have hA := (coeff.amplitudeDeriv_continuousAt p.1 hp h).comp continuousAt_fst
  have hphase : ContinuousAt (fun q : ℝ × ℂ=>ShortDraftTrace.breveE (cuspFrequency h*q.2)) p := by
    change ContinuousAt (fun q : ℝ × ℂ=>Complex.exp (2*Real.pi*Complex.I*
      ((cuspFrequency h*q.2)+starRingEnd ℂ (cuspFrequency h*q.2)))) p
    fun_prop
  have hfirst := (ContinuousLinearMap.smulRightL ℝ (ℝ × ℂ) ℂ
    (ContinuousLinearMap.fst ℝ ℝ ℂ)).continuous.continuousAt.comp (hA.mul hphase)
  have hterm := (coeff.term_continuousOn h).continuousAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds hp)
  have hsecond := hterm.smul (continuousAt_const
    (y:=(horizontalPhaseCLM (cuspFrequency h)).comp (ContinuousLinearMap.snd ℝ ℝ ℂ)))
  have he : coeff.termFDeriv h=(fun q : ℝ × ℂ=>
      (ContinuousLinearMap.fst ℝ ℝ ℂ).smulRight
        (coeff.amplitudeDeriv q.1 h*ShortDraftTrace.breveE (cuspFrequency h*q.2))+
      coeff.term h q • (horizontalPhaseCLM (cuspFrequency h)).comp (ContinuousLinearMap.snd ℝ ℝ ℂ)) := by
    funext q
    simp only [termFDeriv,ite_eq_right hh]
  rw [he]
  exact hfirst.add hsecond

lemma seriesFDeriv_continuousOn_slab (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ContinuousOn (fun p : ℝ × ℂ=>∑'h : ActualEisensteinCubic.O,coeff.termFDeriv h p)
      {p : ℝ × ℂ|p.1∈Set.Icc a b} := by
  obtain ⟨C,hC,hbound⟩ := coeff.termFDeriv_slab_bound a b ha hab
  apply continuousOn_tsum (u:=fun h : ActualEisensteinCubic.O=>C*((1+‖cuspFrequency h‖)*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)))
  · intro h p hp
    exact (coeff.termFDeriv_continuousAt h p (ha.trans_le hp.1)).continuousWithinAt
  · exact (summable_one_add_norm_exp_neg_cuspFrequency (Real.pi*a) (mul_pos Real.pi_pos ha)).mul_left C
  · exact hbound

lemma series_contDiffAt_one (p : ℝ × ℂ) (hp : 0<p.1) : ContDiffAt ℝ 1 coeff.series p := by
  apply contDiffAt_one_iff.mpr
  refine ⟨(fun q=>∑'h : ActualEisensteinCubic.O,coeff.termFDeriv h q),
    {q : ℝ × ℂ|q.1∈Set.Icc (p.1/2) (2*p.1)},?_,?_,?_⟩
  · exact continuousAt_fst.tendsto.eventually (Icc_mem_nhds (by linarith) (by linarith))
  · exact coeff.seriesFDeriv_continuousOn_slab _ _ (by linarith) (by linarith)
  · intro q hq
    exact coeff.series_hasFDerivAt q (by change p.1/2≤q.1 ∧ q.1≤2*p.1 at hq;linarith [hq.1])

end SubexponentialBesselCoefficients
end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

def cuspSpatialInput (q : ℝ × ℂ) : SpatialCoordinates := ![q.2.re,q.2.im,q.1]
def cuspSpatialOutput (p : SpatialCoordinates) : ℝ × ℂ := (p 2,spatialHorizontal p)

lemma cuspSpatialInput_contDiff : ContDiff ℝ 1 cuspSpatialInput := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · change ContDiff ℝ 1 (fun q : ℝ × ℂ=>q.2.re)
    exact Complex.reCLM.contDiff.comp contDiff_snd
  · change ContDiff ℝ 1 (fun q : ℝ × ℂ=>q.2.im)
    exact Complex.imCLM.contDiff.comp contDiff_snd
  · change ContDiff ℝ 1 (fun q : ℝ × ℂ=>q.1)
    fun_prop

lemma cuspSpatialOutput_contDiff : ContDiff ℝ 1 cuspSpatialOutput :=
  (contDiff_apply ℝ ℝ 2).prodMk (spatialHorizontal_contDiff.of_le (by simp))

lemma cuspSpatialInput_horizontal (q : ℝ × ℂ) : spatialHorizontal (cuspSpatialInput q)=q.2 :=
  Complex.re_add_im q.2

lemma cuspSpatialAction_lift (g : SL(2,ℂ)) (q : ℝ × ℂ) (hq : 0<q.1) :
    cuspCoordinateLift (cuspSpatialOutput (mobiusSpatial g (cuspSpatialInput q)))=
      g•cuspCoordinateLift q := by
  have hin : hyperbolicSpatialCoordinates (cuspCoordinateLift q)=cuspSpatialInput q := by
    rw [show q=(q.1,q.2) from rfl,cuspCoordinateLift_positive q.1 q.2 hq]
    simp only [hyperbolicSpatialCoordinates,hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint,cuspSpatialInput]
  have he := mobiusSpatial_coordinates_global g (cuspCoordinateLift q)
  rw [hin] at he
  have hr := hyperbolicSpatialCoordinates_reconstruct (g•cuspCoordinateLift q)
  have hp : 0<mobiusSpatial g (cuspSpatialInput q) 2 := mobiusSpatial_positive g _ hq
  rw [cuspSpatialOutput,cuspCoordinateLift_positive _ _ hp]
  refine Eq.trans ?_ hr
  apply upperPoint_congr
  · rw [he]
    rfl
  · rw [he]

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma fullFunction_cusp_contDiffAt_one (constant : ℂ) (p : ℝ × ℂ) (hp : 0<p.1) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>coeff.fullFunction constant (cuspCoordinateLift q)) p := by
  have hreal : ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>q.1^(2/3:ℝ)) p :=
    contDiff_fst.contDiffAt.rpow_const_of_ne hp.ne'
  have hcast := Complex.ofRealCLM.contDiff.contDiffAt.comp p hreal
  have hpow : ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>(q.1:ℂ)^(2/3:ℂ)) p := by
    apply hcast.congr_of_eventuallyEq
    filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
    have he := Complex.ofReal_cpow (le_of_lt hq) (2/3:ℝ)
    norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at he
    exact he.symm
  have hfull : ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>constant*(q.1:ℂ)^(2/3:ℂ)+coeff.series q) p :=
    (contDiffAt_const.mul hpow).add (coeff.series_contDiffAt_one p hp)
  apply hfull.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact coeff.fullFunction_cusp_eq constant q hq

lemma fullFunction_translate_cusp_contDiffAt_one (constant : ℂ) (g : SL(2,ℂ))
    (p : ℝ × ℂ) (hp : 0<p.1) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>coeff.fullFunction constant (g•cuspCoordinateLift q)) p := by
  have hmid : ContDiffAt ℝ 1 (fun q=>mobiusSpatial g (cuspSpatialInput q)) p :=
    ((mobiusSpatial_contDiffAt g (cuspSpatialInput p) hp).of_le (by simp)).comp p
      cuspSpatialInput_contDiff.contDiffAt
  have hact := cuspSpatialOutput_contDiff.contDiffAt.comp p hmid
  have hpos : 0<(cuspSpatialOutput (mobiusSpatial g (cuspSpatialInput p))).1 :=
    mobiusSpatial_positive g _ hp
  have hfull := (coeff.fullFunction_cusp_contDiffAt_one constant _ hpos).comp p hact
  apply hfull.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact congrArg (coeff.fullFunction constant) (cuspSpatialAction_lift g q hq).symm

lemma fullFunction_translate_split_contDiffAt_one (constant : ℂ) (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    ContDiffAt ℝ 1 (fun q : ℂ × ℝ=>coeff.fullFunction constant (g•cuspCoordinateLift (q.2,q.1))) p := by
  have hswap : ContDiffAt ℝ 1 (fun q : ℂ × ℝ=>(q.2,q.1)) p := by fun_prop
  exact (coeff.fullFunction_translate_cusp_contDiffAt_one constant g (p.2,p.1) hp).comp p hswap

end SubexponentialBesselCoefficients

lemma cubicSourceResidualFunction_translate_split_contDiffAt_one (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    ContDiffAt ℝ 1 (fun q : ℂ × ℝ=>cubicSourceResidualFunction (g•cuspCoordinateLift (q.2,q.1))) p := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_translate_split_contDiffAt_one _ g p hp

lemma cubicSourceConjugateFunction_translate_split_contDiffAt_one (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    ContDiffAt ℝ 1 (fun q : ℂ × ℝ=>cubicSourceConjugateFunction (g•cuspCoordinateLift (q.2,q.1))) p := by
  exact Complex.conjCLE.contDiff.contDiffAt.comp p
    (cubicSourceResidualFunction_translate_split_contDiffAt_one g p hp)

lemma horizontalWirtingerBar_eq_fderiv (F : ℂ × ℝ→ℂ) (A : (ℂ × ℝ)→L[ℝ]ℂ)
    (z : ℂ) (v : ℝ) (hF : HasFDerivAt F A (z,v)) :
    horizontalWirtingerBar (fun w=>F (w,v)) z=
      (1/2:ℂ)*(A (1,0)+Complex.I*A (Complex.I,0)) := by
  have hline (direction : ℂ) :
      HasDerivAt (fun t : ℝ=>F (z+(t:ℂ)*direction,v)) (A (direction,0)) 0 := by
    have hz : HasDerivAt (fun t : ℝ=>z+(t:ℂ)*direction) direction 0 := by
      simpa using (((hasDerivAt_id (0:ℝ)).ofReal_comp.mul_const direction).const_add z)
    have hp := hz.prodMk (hasDerivAt_const (0:ℝ) v)
    have hf : HasFDerivAt F A (z+(0:ℂ)*direction,v) := by simpa using hF
    exact hf.comp_hasDerivAt 0 hp
  have h1 := (hline 1).deriv
  have hI := (hline Complex.I).deriv
  simp only [mul_one] at h1
  rw [horizontalWirtingerBar,h1,hI]

lemma cuspBarProfile_continuousOn_of_contDiff (f : HyperbolicSpace→ℂ)
    (hreg : ∀p : ℂ × ℝ,0<p.2 → ContDiffAt ℝ 1
      (fun q : ℂ × ℝ=>f (cuspCoordinateLift (q.2,q.1))) p) (z : ℂ) :
    ContinuousOn (cuspBarProfile f z) (Set.Ioi 0) := by
  let F : ℂ × ℝ→ℂ := fun q=>f (cuspCoordinateLift (q.2,q.1))
  intro v hv
  have hd : ContinuousAt (fderiv ℝ F) (z,v) :=
    (hreg (z,v) hv).continuousAt_fderiv (by norm_num)
  have hc : ContinuousAt (fun y : ℝ=>(z,y)) v := continuousAt_const.prodMk continuousAt_id
  have h1 := (hd.comp hc).clm_apply (continuousAt_const (y:=((1,0):ℂ × ℝ)))
  have hI := (hd.comp hc).clm_apply (continuousAt_const (y:=((Complex.I,0):ℂ × ℝ)))
  have hformula : ContinuousAt (fun y : ℝ=>(1/2:ℂ)*
      ((fderiv ℝ F (z,y)) (1,0)+Complex.I*(fderiv ℝ F (z,y)) (Complex.I,0))) v :=
    continuousAt_const.mul (h1.add (continuousAt_const.mul hI))
  apply ContinuousAt.continuousWithinAt
  apply hformula.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show 0<v from hv)] with y hy
  exact horizontalWirtingerBar_eq_fderiv F (fderiv ℝ F (z,y)) z y
    ((hreg (z,y) hy).differentiableAt (by norm_num)).hasFDerivAt

lemma cuspZProfile_continuousOn_of_contDiff (f : HyperbolicSpace→ℂ)
    (hreg : ∀p : ℂ × ℝ,0<p.2 → ContDiffAt ℝ 1
      (fun q : ℂ × ℝ=>f (cuspCoordinateLift (q.2,q.1))) p) (z : ℂ) :
    ContinuousOn (cuspZProfile f z) (Set.Ioi 0) := by
  let F : ℂ × ℝ→ℂ := fun q=>f (cuspCoordinateLift (q.2,q.1))
  intro v hv
  have hd : ContinuousAt (fderiv ℝ F) (z,v) :=
    (hreg (z,v) hv).continuousAt_fderiv (by norm_num)
  have hc : ContinuousAt (fun y : ℝ=>(z,y)) v := continuousAt_const.prodMk continuousAt_id
  have h1 := (hd.comp hc).clm_apply (continuousAt_const (y:=((1,0):ℂ × ℝ)))
  have hI := (hd.comp hc).clm_apply (continuousAt_const (y:=((Complex.I,0):ℂ × ℝ)))
  have hformula : ContinuousAt (fun y : ℝ=>(1/2:ℂ)*
      ((fderiv ℝ F (z,y)) (1,0)-Complex.I*(fderiv ℝ F (z,y)) (Complex.I,0))) v :=
    continuousAt_const.mul (h1.sub (continuousAt_const.mul hI))
  apply ContinuousAt.continuousWithinAt
  apply hformula.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show 0<v from hv)] with y hy
  exact horizontalWirtingerZ_eq_fderiv F (fderiv ℝ F (z,y)) z y
    ((hreg (z,y) hy).differentiableAt (by norm_num)).hasFDerivAt

lemma cuspBarProfile_source_translate_continuousOn (H : SL(2,ℂ)) (z : ℂ) :
    ContinuousOn (cuspBarProfile (fun w=>cubicSourceResidualFunction (H•w)) z) (Set.Ioi 0) :=
  cuspBarProfile_continuousOn_of_contDiff _
    (cubicSourceResidualFunction_translate_split_contDiffAt_one H) z

lemma cuspZProfile_source_translate_continuousOn (H : SL(2,ℂ)) (z : ℂ) :
    ContinuousOn (cuspZProfile (fun w=>cubicSourceResidualFunction (H•w)) z) (Set.Ioi 0) :=
  cuspZProfile_continuousOn_of_contDiff _
    (cubicSourceResidualFunction_translate_split_contDiffAt_one H) z

lemma cuspBarProfile_conjugate_translate_continuousOn (H : SL(2,ℂ)) (z : ℂ) :
    ContinuousOn (cuspBarProfile (fun w=>cubicSourceConjugateFunction (H•w)) z) (Set.Ioi 0) :=
  cuspBarProfile_continuousOn_of_contDiff _
    (cubicSourceConjugateFunction_translate_split_contDiffAt_one H) z

lemma cuspZProfile_conjugate_translate_continuousOn (H : SL(2,ℂ)) (z : ℂ) :
    ContinuousOn (cuspZProfile (fun w=>cubicSourceConjugateFunction (H•w)) z) (Set.Ioi 0) :=
  cuspZProfile_continuousOn_of_contDiff _
    (cubicSourceConjugateFunction_translate_split_contDiffAt_one H) z

end

section
open Filter MeasureTheory
open scoped BigOperators Classical

open ActualEisensteinCubic ConcreteTraceCRT CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma ninth_trace_character_period (c x : Eis) :
    ShortDraftTrace.breveE ((eisEmbedding c/(9*eisLam))*(9*eisEmbedding x))=1 := by
  have he : (eisEmbedding c/(9*eisLam))*(9*eisEmbedding x)=eisEmbedding (c*x)/eisLam := by
    rw [map_mul]
    ring
  rw [he,breveE_embedding_div_traceLambda]

lemma ramifiedSource_scaled_periodic10 (v : ℝ) (hv : 0<v) (x : Eis) (z : ℂ) :
    ramifiedSourceFunction omega (upperPoint (3*(z+3*eisEmbedding x)) v hv)=
      ramifiedSourceFunction omega (upperPoint (3*z) v hv) := by
  have he : 3*(z+3*eisEmbedding x)=3*z+3*eisEmbedding (3*x) := by
    rw [map_mul,map_ofNat]
    ring
  rw [he,ramifiedSourceFunction_upper_shift10,show eisEmbedding (3*x)=3*eisEmbedding x by rw [map_mul,map_ofNat]]
  have hp : ShortDraftTrace.breveE (ramifiedShift10*(3*(3*eisEmbedding x)))=1 := by
    simpa only [ramifiedShift10,show (3:ℂ)*(3*eisEmbedding x)=9*eisEmbedding x by ring] using
      ninth_trace_character_period (omega-1) x
  rw [hp,one_mul]

lemma ramifiedSource_scaled_periodic19 (v : ℝ) (hv : 0<v) (x : Eis) (z : ℂ) :
    ramifiedSourceFunction (omega^2) (upperPoint (3*(z+3*eisEmbedding x)) v hv)=
      ramifiedSourceFunction (omega^2) (upperPoint (3*z) v hv) := by
  have he : 3*(z+3*eisEmbedding x)=3*z+3*eisEmbedding (3*x) := by
    rw [map_mul,map_ofNat]
    ring
  rw [he,ramifiedSourceFunction_upper_shift19,show eisEmbedding (3*x)=3*eisEmbedding x by rw [map_mul,map_ofNat]]
  have hp : ShortDraftTrace.breveE (ramifiedShift19*(3*(3*eisEmbedding x)))=1 := by
    simpa only [ramifiedShift19,show (3:ℂ)*(3*eisEmbedding x)=9*eisEmbedding x by ring] using
      ninth_trace_character_period (-2-omega) x
  rw [hp,one_mul]

lemma periodic_integral_zero_of_eigen_translation (f : ℂ→ℂ)
    (hf : ∀x:Eis,∀z,f (z+3*eisEmbedding x)=f z) (b c : ℂ)
    (hc : c≠1) (he : ∀z,f (b+z)=c*f z) :
    (∫z in periodDomain,f z)=0 := by
  have hi := period_integral_translation f hf b
  simp_rw [he] at hi
  rw [integral_const_mul] at hi
  have hzero : (c-1)*(∫z in periodDomain,f z)=0 := by linear_combination hi
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hc)

theorem ramifiedSource_zero_mode10 (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,ramifiedSourceFunction omega (upperPoint (3*z) v hv))=0 := by
  apply periodic_integral_zero_of_eigen_translation _
    (ramifiedSource_scaled_periodic10 v hv) 1 (eisEmbedding omega)
  · exact fun h => omega_primitive.ne_one (by decide) (eisEmbedding_injective (by simpa using h))
  · intro z
    have he : 3*(1+z)=3*z+3*eisEmbedding (ActualEisensteinCoordinates.eval 1 0) := by
      norm_num [ActualEisensteinCoordinates.eval]
      ring
    rw [he,ramifiedSourceFunction_upper_shift10,ramifiedShift10_period]
    norm_num [cubicExp]

theorem ramifiedSource_zero_mode19 (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,ramifiedSourceFunction (omega^2) (upperPoint (3*z) v hv))=0 := by
  apply periodic_integral_zero_of_eigen_translation _
    (ramifiedSource_scaled_periodic19 v hv) 1 (eisEmbedding (omega^2))
  · intro h
    have he : omega^2=(1:Eis) := eisEmbedding_injective (by simpa using h)
    have hpoly := ramified_omega_relation
    rw [he] at hpoly
    have hw : omega=(-2:Eis) := by linear_combination hpoly
    rw [hw] at he
    norm_num at he
  · intro z
    have he : 3*(1+z)=3*z+3*eisEmbedding (ActualEisensteinCoordinates.eval 1 0) := by
      norm_num [ActualEisensteinCoordinates.eval]
      ring
    rw [he,ramifiedSourceFunction_upper_shift19,ramifiedShift19_period]
    norm_num [cubicExp]

end

open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

abbrev UnitLowerData := Σa:PrimaryLower,{d:PrimaryLower//IsCoprime a.val d.val}

def unitLowerToPrimitive (u : Eisˣ) (p : UnitLowerData) : PrimitiveRow := by
  refine ⟨![(u:Eis)*(p.1.val-p.2.val.val),p.2.val.val],?_,?_,p.2.val.2⟩
  · change IsCoprime ((u:Eis)*(p.1.val-p.2.val.val)) p.2.val.val
    apply (isCoprime_mul_unit_left_left u.isUnit _ _).mpr
    apply IsCoprime.symm
    apply (isCoprime_right_congr_of_dvd p.2.val.val (p.1.val-p.2.val.val) p.1.val
      ⟨-1,by ring⟩).mpr
    exact p.2.2.symm
  · have hd : (3:Eis)∣p.1.val-p.2.val.val := by
      simpa only [sub_sub_sub_cancel_right] using dvd_sub p.1.2 p.2.val.2
    exact hd.mul_left (u:Eis)

lemma unitLowerToPrimitive_bijective (u : Eisˣ) :
    Function.Bijective (unitLowerToPrimitive u) := by
  constructor
  · rintro ⟨a,d,hd⟩ ⟨b,e,he⟩ h
    have hrow := congrArg Subtype.val h
    have hde : d=e := Subtype.ext (congrFun hrow 1)
    subst e
    have hab : a=b := by
      apply Subtype.ext
      have hh := congrFun hrow 0
      change (u:Eis)*(a.val-d.val)=(u:Eis)*(b.val-d.val) at hh
      have hcancel := u.isUnit.mul_left_cancel hh
      linear_combination hcancel
    subst b
    rfl
  · intro r
    let d : PrimaryLower := ⟨r.val 1,r.2.2.2⟩
    let a : PrimaryLower := ⟨(↑u⁻¹:Eis)*r.val 0+r.val 1,by
      have hc := r.2.2.1.mul_left (↑u⁻¹:Eis)
      have hh := dvd_add hc r.2.2.2
      convert hh using 1 ;ring⟩
    have hcop : IsCoprime a.val d.val := by
      apply IsCoprime.symm
      apply (isCoprime_right_congr_of_dvd d.val a.val ((↑u⁻¹:Eis)*r.val 0)
        ⟨1,by dsimp [a,d];ring⟩).mpr
      exact (isCoprime_mul_unit_left_right u⁻¹.isUnit _ _).mpr r.2.1.symm
    refine ⟨⟨a,d,hcop⟩,Subtype.ext ?_⟩
    funext i
    fin_cases i
    · change (u:Eis)*((↑u⁻¹:Eis)*r.val 0+r.val 1-r.val 1)=r.val 0
      rw [add_sub_cancel_right,←mul_assoc]
      simp
    · rfl

def unitLowerEquiv (u : Eisˣ) : UnitLowerData≃PrimitiveRow :=
  Equiv.ofBijective _ (unitLowerToPrimitive_bijective u)

lemma rowOperator_lowerCusp (t : Eis) (v : Fin 2→ℂ) :
    rowOperator (integralComplexMatrix (lowerCuspMatrix t)) v=
      ![v 0+eisEmbedding t*v 1,v 1] := by
  rw [rowOperator_apply]
  funext i
  simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_two,integralComplexMatrix_apply]
  fin_cases i <;>
    simp [lowerCuspMatrix,mul_comm]

lemma unitLower_row_phase (u : Eisˣ) (p : UnitLowerData) :
    (cosetCharacter (primitiveRowEquiv.symm (unitLowerEquiv u p)))⁻¹=
      eisEmbedding (symbol (u:Eis) p.2.val.val)*
        eisEmbedding (symbol p.2.val.val p.1.val) := by
  rw [inverse_cosetCharacter_eq_row_symbol,primitiveRowEquiv_symm_row]
  change eisEmbedding (symbol ((u:Eis)*(p.1.val-p.2.val.val)) p.2.val.val)=_
  have hh : symbol ((u:Eis)*(p.1.val-p.2.val.val)) p.2.val.val=
      symbol ((u:Eis)*p.1.val) p.2.val.val := by
    exact symbol_congr ⟨-(u:Eis),by ring⟩
  rw [hh,symbol_mul_numerator _ _ _ (primaryLower_primary p.2.val),
    symbol_reciprocity p.1.val p.2.val.val (primaryLower_ne_zero p.1)
      (primaryLower_ne_zero p.2.val) (primaryLower_primary p.1)
        (primaryLower_primary p.2.val),map_mul]

def unitLowerTerm (u : Eisˣ) (z : ℂ) (v : ℝ) (s : ℂ) (a d : Eis) : ℂ :=
  (eisEmbedding (symbol (u:Eis) d)*eisEmbedding (symbol d a))*
    ((v/(‖eisEmbedding ((u:Eis)*a)*z+eisEmbedding d‖^2+
      ‖eisEmbedding ((u:Eis)*a)‖^2*v^2):ℝ):ℂ)^s

lemma unitLower_summand (u : Eisˣ) (z : ℂ) (v : ℝ) (hv : 0<v)
    (s : ℂ) (p : UnitLowerData) :
    summand (integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv) s
      (primitiveRowEquiv.symm (unitLowerEquiv u p))=
      unitLowerTerm u z v s p.1.val p.2.val.val := by
  let r : Fin 2→ℂ := ![eisEmbedding ((u:Eis)*p.1.val),eisEmbedding p.2.val.val]
  have hr : rowOperator (integralComplexMatrix (lowerCuspMatrix (u:Eis)))
      (embeddedRow (primitiveRowEquiv.symm (unitLowerEquiv u p)))=r := by
    rw [embeddedRow, primitiveRowEquiv_symm_row, rowOperator_lowerCusp]
    funext i
    fin_cases i <;>
      simp [unitLowerEquiv, Equiv.ofBijective_apply, unitLowerToPrimitive, r, map_mul, map_sub, mul_sub]
  have hr0 : r≠0 := by
    intro hh
    have he := congrFun hh 1
    exact eisEmbedding_ne_zero (primaryLower_ne_zero p.2.val) he
  have hp := heightDenominator_pos z v hv r hr0
  rw [summand,←rowOperator_mul,hr,rowEnergy_upperSection,unitLower_row_phase]
  change _=(eisEmbedding (symbol (u:Eis) p.2.val.val)*eisEmbedding (symbol p.2.val.val p.1.val))*
    ((v/heightDenominator z v r:ℝ):ℂ)^s
  have hi : ((v/heightDenominator z v r:ℝ):ℂ)=
      (((heightDenominator z v r/v:ℝ):ℂ))⁻¹ := by
    simp only [Complex.ofReal_div,inv_div]
  rw [hi,Complex.inv_cpow_ofReal_nonneg (div_nonneg hp.le hv.le),Complex.cpow_neg]

theorem unitLowerEisenstein_eq_rows (u : Eisˣ) (z : ℂ) (v : ℝ) (hv : 0<v) (s : ℂ) :
    eisenstein (integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv) s=
      ∑'p:UnitLowerData,unitLowerTerm u z v s p.1.val p.2.val.val := by
  rw [eisenstein,←primitiveRowEquiv.symm.tsum_eq,←(unitLowerEquiv u).tsum_eq]
  exact tsum_congr (unitLower_summand u z v hv s)

end CubicEisenstein

end

end OAI
end OAIOriginalModule0285

/-! Original module: OAI.NumberTheory.DirichletL.Cusp.ResiduesModThree
Source SHA256: 5669337f308cd6c704bced622982a38b10d07829f6755418bcb2609fe4c2a4dc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0286



namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped Classical MatrixGroups

namespace EisensteinCuspModThree

section
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCoordinates (eval coords eval_coords unique_coordinates eval_mul)

abbrev Pair := ZMod 3 × ZMod 3
def add (x y : Pair) : Pair := (x.1+y.1,x.2+y.2)
def neg (x : Pair) : Pair := (-x.1,-x.2)
def sub (x y : Pair) : Pair := add x (neg y)
def mul (x y : Pair) : Pair := (x.1*y.1-x.2*y.2,x.1*y.2+x.2*y.1-x.2*y.2)
def scalar (a : ZMod 3) (x : Pair) : Pair := (a*x.1,a*x.2)
def residue (x : ActualEisensteinCubic.O) : Pair := ((coords x).1,(coords x).2)

lemma residue_eval (a b : ℤ) : residue (eval a b)=((a:ZMod 3),(b:ZMod 3)) := by
  have h := unique_coordinates (eval_coords (eval a b))
  exact Prod.ext (congrArg (fun n : ℤ => (n:ZMod 3)) h.1)
    (congrArg (fun n : ℤ => (n:ZMod 3)) h.2)

lemma residue_intCast (a : ℤ) : residue (a:ActualEisensteinCubic.O)=((a:ZMod 3),0) := by
  simpa [eval] using residue_eval a 0

lemma residue_zero : residue (0:ActualEisensteinCubic.O)=(0,0) := by simpa using residue_intCast 0
lemma residue_one : residue (1:ActualEisensteinCubic.O)=(1,0) := by simpa using residue_intCast 1

lemma residue_add (x y : ActualEisensteinCubic.O) : residue (x+y)=add (residue x) (residue y) := by
  have he : x+y=eval ((coords x).1+(coords y).1) ((coords x).2+(coords y).2) := by
    nth_rw 1 [←eval_coords x,←eval_coords y]
    simp only [eval,Int.cast_add]
    ring
  rw [he,residue_eval]
  simp [residue,add]

lemma residue_neg (x : ActualEisensteinCubic.O) : residue (-x)=neg (residue x) := by
  have he : -x=eval (-(coords x).1) (-(coords x).2) := by
    nth_rw 1 [←eval_coords x]
    simp only [eval,Int.cast_neg]
    ring
  rw [he,residue_eval]
  simp [residue,neg]

lemma residue_sub (x y : ActualEisensteinCubic.O) : residue (x-y)=sub (residue x) (residue y) := by
  rw [sub_eq_add_neg,residue_add,residue_neg]
  rfl

lemma residue_mul (x y : ActualEisensteinCubic.O) : residue (x*y)=mul (residue x) (residue y) := by
  calc
    residue (x*y)=residue (eval (coords x).1 (coords x).2*eval (coords y).1 (coords y).2) := by
      rw [eval_coords,eval_coords]
    _ = _ := by rw [eval_mul,residue_eval]; simp [residue,mul]

lemma residue_eq_implies_three_dvd {x y : ActualEisensteinCubic.O} (h : residue x=residue y) : (3:ActualEisensteinCubic.O)∣x-y := by
  have h1 : (3:ℤ)∣(coords x).1-(coords y).1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (coords y).1 (coords x).1 3).mp
      (congrArg Prod.fst h).symm
  have h2 : (3:ℤ)∣(coords x).2-(coords y).2 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (coords y).2 (coords x).2 3).mp
      (congrArg Prod.snd h).symm
  obtain ⟨a,ha⟩ := h1
  obtain ⟨b,hb⟩ := h2
  refine ⟨eval a b,?_⟩
  nth_rw 1 [←eval_coords x,←eval_coords y]
  have he1 : (coords x).1=(coords y).1+3*a := by omega
  have he2 : (coords x).2=(coords y).2+3*b := by omega
  simp only [eval,he1,he2]
  push_cast
  ring

lemma residue_mul_intCast (a : ℤ) (x : ActualEisensteinCubic.O) : residue ((a:ActualEisensteinCubic.O)*x)=scalar (a:ZMod 3) (residue x) := by
  rw [residue_mul,residue_intCast]
  simp [mul,scalar]

def primitive (a c : Pair) : Prop := ¬(a.1+a.2=0 ∧ c.1+c.2=0)
instance primitive_decidable (a c : Pair) : Decidable (primitive a c) := inferInstanceAs
  (Decidable (¬(a.1+a.2=0 ∧ c.1+c.2=0)))

lemma primitive_of_determinant : ∀a b c d : Pair,sub (mul a d) (mul b c)=(1,0) → primitive a c := by
  decide +kernel

lemma first_column_primitive (M : SL(2,ActualEisensteinCubic.O)) : primitive (residue (M 0 0)) (residue (M 1 0)) := by
  have hd : M 0 0*M 1 1-M 0 1*M 1 0=1 := by simpa only [Matrix.det_fin_two] using M.property
  have hh := congrArg residue hd
  rw [residue_sub,residue_mul,residue_mul,residue_one] at hh
  exact primitive_of_determinant _ _ _ _ hh

def omegaPower (k : Fin 3) : Pair := if k=0 then (1,0) else if k=1 then (0,1) else (-1,-1)
def unitPair (u : Fin 2 × Fin 3) : Pair := scalar ((-1:ZMod 3)^u.1.val) (omegaPower u.2)
def cuspPair (j : Fin 3) : Pair := if j=0 then (0,0) else if j=1 then (0,1) else (-1,-1)

def columnTop (g : SL(2,ZMod 3)) (j : Fin 3) (u : Fin 2 × Fin 3) : Pair :=
  mul (add (g 0 0,0) (scalar (g 0 1) (cuspPair j))) (unitPair u)
def columnBottom (g : SL(2,ZMod 3)) (j : Fin 3) (u : Fin 2 × Fin 3) : Pair :=
  mul (add (g 1 0,0) (scalar (g 1 1) (cuspPair j))) (unitPair u)

theorem primitive_column_three_cusps : ∀a c : Pair, primitive a c →
    ∃g : SL(2,ZMod 3), ∃j : Fin 3, ∃u : Fin 2 × Fin 3,
      columnTop g j u=a ∧ columnBottom g j u=c := by
  decide +kernel

end

open scoped Classical MatrixGroups Matrix

local notation "O" => ActualEisensteinCubic.O
local notation "ζ" => ActualEisensteinCubic.omega
open CubicKubota CubicEisenstein

def unitRepresentative (u : Fin 2 × Fin 3) : ActualEisensteinCubic.Oˣ :=
  (-1:ActualEisensteinCubic.Oˣ)^u.1.val*CubicRamified.omega_isUnit.unit^u.2.val

lemma unitRepresentative_value (u : Fin 2 × Fin 3) :
    (unitRepresentative u:ActualEisensteinCubic.O)=(-1:ActualEisensteinCubic.O)^u.1.val*ζ^u.2.val := by
  simp [unitRepresentative]

lemma residue_omega : residue ζ=(0,1) := by
  have he : ActualEisensteinCoordinates.eval 0 1=ζ := by
    simp only [ActualEisensteinCoordinates.eval,Int.cast_zero,Int.cast_one,zero_add,one_mul]
    rfl
  rw [←he]
  exact residue_eval 0 1

lemma residue_omega_sq : residue (ζ^2)=(-1,-1) := by
  rw [pow_two,residue_mul,residue_omega]
  norm_num [mul]

lemma unitRepresentative_residue (u : Fin 2 × Fin 3) :
    residue (unitRepresentative u:ActualEisensteinCubic.O)=unitPair u := by
  rw [unitRepresentative_value]
  rcases u with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [unitPair,omegaPower,scalar,residue_one,residue_neg,residue_omega,residue_omega_sq,neg]

def cuspParameter (j : Fin 3) : ActualEisensteinCubic.O := if j=0 then 0 else if j=1 then ζ else ζ^2
def cuspRepresentative (j : Fin 3) : SL(2,ActualEisensteinCubic.O) := lowerCuspMatrix (cuspParameter j)

lemma cuspParameter_residue (j : Fin 3) : residue (cuspParameter j)=cuspPair j := by
  fin_cases j <;> simp [cuspParameter,cuspPair,residue_zero,residue_omega,residue_omega_sq]

def unitDiagonal (u : ActualEisensteinCubic.Oˣ) : SL(2,ActualEisensteinCubic.O) :=
  ⟨!![(u:ActualEisensteinCubic.O),0;0,(↑u⁻¹:ActualEisensteinCubic.O)],by simp [Matrix.det_fin_two]⟩

def columnRepresentative (r : SL(2,ℤ)) (j : Fin 3) (u : Fin 2 × Fin 3) : SL(2,ActualEisensteinCubic.O) :=
  rationalEmbedding r*cuspRepresentative j*unitDiagonal (unitRepresentative u)

lemma columnRepresentative_entry (r : SL(2,ℤ)) (j : Fin 3) (u : Fin 2 × Fin 3) (i : Fin 2) :
    columnRepresentative r j u i 0=
      ((r i 0:ActualEisensteinCubic.O)+(r i 1:ActualEisensteinCubic.O)*cuspParameter j)*(unitRepresentative u:ActualEisensteinCubic.O) := by
  change (((r : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom O) *
    !![1, 0; cuspParameter j, 1]) *
    !![(unitRepresentative u : O), 0; 0, (↑(unitRepresentative u)⁻¹ : O)]) i 0 = _
  simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma columnRepresentative_top_residue (r : SL(2,ℤ)) (j : Fin 3) (u : Fin 2 × Fin 3) :
    residue (columnRepresentative r j u 0 0)=columnTop (rationalReductionThree r) j u := by
  rw [columnRepresentative_entry,residue_mul,residue_add,residue_intCast,
    residue_mul_intCast,cuspParameter_residue,unitRepresentative_residue]
  rfl

lemma columnRepresentative_bottom_residue (r : SL(2,ℤ)) (j : Fin 3) (u : Fin 2 × Fin 3) :
    residue (columnRepresentative r j u 1 0)=columnBottom (rationalReductionThree r) j u := by
  rw [columnRepresentative_entry,residue_mul,residue_add,residue_intCast,
    residue_mul_intCast,cuspParameter_residue,unitRepresentative_residue]
  rfl

lemma same_column_quotient_lower_zero (M N : SL(2,ActualEisensteinCubic.O))
    (h0 : N 0 0=M 0 0) (h1 : N 1 0=M 1 0) : (N⁻¹*M) 1 0=0 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,]
  rw [h0,h1]
  ring

theorem three_cusp_decomposition (M : SL(2,ActualEisensteinCubic.O)) :
    ∃G : levelTwo, ∃j : Fin 3, ∃T : SL(2,ActualEisensteinCubic.O),
      T 1 0=0 ∧ IsUnit (T 0 0) ∧ IsUnit (T 1 1) ∧
        M=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*T := by
  obtain ⟨g,j,u,ht,hb⟩ := primitive_column_three_cusps _ _ (first_column_primitive M)
  obtain ⟨r,hr⟩ := rationalReductionThree_surjective g
  let B := columnRepresentative r j u
  have hB0 : residue (B 0 0)=residue (M 0 0) := by
    dsimp only [B]
    rw [columnRepresentative_top_residue,hr]
    exact ht
  have hB1 : residue (B 1 0)=residue (M 1 0) := by
    dsimp only [B]
    rw [columnRepresentative_bottom_residue,hr]
    exact hb
  have hxy : IsCoprime (M 0 0) (M 1 0) := by
    refine ⟨M 1 1,-M 0 1,?_⟩
    have hd := M.property
    rw [Matrix.det_fin_two] at hd
    linear_combination hd
  obtain ⟨N,hN0,hN1,hNB⟩ := exists_congruent_cusp_completion B (M 0 0) (M 1 0) hxy
    (residue_eq_implies_three_dvd hB0.symm) (residue_eq_implies_three_dvd hB1.symm)
  let G : levelTwo := ⟨(N*B⁻¹)*rationalEmbedding r,⟨⟨N*B⁻¹,hNB⟩,r,rfl⟩⟩
  let T : SL(2,ActualEisensteinCubic.O) := unitDiagonal (unitRepresentative u)*(N⁻¹*M)
  have hT : T 1 0=0 := by
    have hz := same_column_quotient_lower_zero M N hN0 hN1
    change (∑k : Fin 2,(unitDiagonal (unitRepresentative u)) 1 k*(N⁻¹*M) k 0)=0
    rw [Fin.sum_univ_two]
    change 0*(N⁻¹*M) 0 0+(↑(unitRepresentative u)⁻¹:ActualEisensteinCubic.O)*(N⁻¹*M) 1 0=0
    rw [hz]
    ring
  have hdet : T 0 0*T 1 1=1 := by
    have hd := T.property
    simpa only [Matrix.det_fin_two,hT,mul_zero,sub_zero] using hd
  refine ⟨G,j,T,hT,?_,?_,?_⟩
  · exact IsUnit.of_mul_eq_one _ hdet
  · exact IsUnit.of_mul_eq_one _ (show T 1 1*T 0 0=1 by simpa only [mul_comm] using hdet)
  · dsimp [G,T,B,columnRepresentative]
    group

end EisensteinCuspModThree

namespace CubicEisenstein
open MeasureTheory Filter
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O
abbrev PrimaryCoprimeDenominator (a : PrimaryLower) := {d:PrimaryLower//IsCoprime a.val d.val}

def primaryDenominatorFromCoprime (a : PrimaryLower) (x : CoprimeElement a.val) :
    PrimaryCoprimeDenominator a := by
  refine ⟨⟨a.val+3*x.val,?_⟩,?_⟩
  · convert dvd_add a.2 (dvd_mul_right (3:Eis) x.val) using 1 ;ring
  · apply (isCoprime_right_congr_of_dvd a.val (a.val+3*x.val) (3*x.val) ⟨1,by ring⟩).mpr
    exact (primary_coprime_three a.val (primaryLower_primary a)).mul_right x.2

lemma primaryDenominatorFromCoprime_bijective (a : PrimaryLower) :
    Function.Bijective (primaryDenominatorFromCoprime a) := by
  constructor
  · intro x y h
    apply Subtype.ext
    have he := congrArg (fun d : PrimaryCoprimeDenominator a => d.val.val) h
    change a.val+3*x.val=a.val+3*y.val at he
    exact mul_left_cancel₀ (by norm_num : (3:Eis)≠0) (add_left_cancel he)
  · intro d
    have hdiv : (3:Eis)∣d.val.val-a.val := by
      simpa only [sub_sub_sub_cancel_right] using dvd_sub d.val.2 a.2
    obtain ⟨x,hx⟩ := hdiv
    have hd : d.val.val=a.val+3*x := by linear_combination hx
    have hcop : IsCoprime a.val x := by
      have hc : IsCoprime a.val (3*x) :=
        (isCoprime_right_congr_of_dvd a.val d.val.val (3*x) ⟨1,by rw [hd];ring⟩).mp d.2
      exact hc.of_isCoprime_of_dvd_right (dvd_mul_left x 3)
    refine ⟨⟨x,hcop⟩,Subtype.ext (Subtype.ext ?_)⟩
    exact hd.symm

def primaryDenominatorEquiv (a : PrimaryLower) : CoprimeElement a.val≃PrimaryCoprimeDenominator a :=
  Equiv.ofBijective _ (primaryDenominatorFromCoprime_bijective a)

def unitLowerIntegral (u : Eisˣ) (v : ℝ) (s freq : ℂ) (a d : Eis) : ℂ :=
  ∫z in periodDomain,unitLowerTerm u z v s a d*ShortDraftTrace.breveE (-freq*z)

lemma hasSum_unitLowerIntegrals (u : Eisˣ) (v : ℝ) (hv : 0<v) (s freq : ℂ) (hs : 2<s.re) :
    HasSum (fun p : UnitLowerData => unitLowerIntegral u v s freq p.1.val p.2.val.val)
      (∫z in periodDomain,eisenstein (integralComplexMatrix (lowerCuspMatrix (u:Eis))*
        upperSection z v hv) s*ShortDraftTrace.breveE (-freq*z)) := by
  have hh := ((unitLowerEquiv u).trans primitiveRowEquiv.symm).hasSum_iff.mpr
    (hasSum_integral_fixed_left_Eisenstein (integralComplexMatrix (lowerCuspMatrix (u:Eis))) v hv s freq hs)
  apply hh.congr_fun
  intro p
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only [Equiv.trans_apply,unitLowerIntegral]
    rw [unitLower_summand])

lemma unitLowerTerm_eq_shifted (u : Eisˣ) (z : ℂ) (v : ℝ) (hv : 0<v)
    (s : ℂ) (a d : Eis) (ha : a≠0) :
    unitLowerTerm u z v s a d=
      (eisEmbedding (symbol (u:Eis) d)*eisEmbedding (symbol d a)*
        ((‖eisEmbedding a‖^2:ℝ):ℂ)^(-s))*
          shiftedHeightKernel v s (eisEmbedding d/eisEmbedding ((u:Eis)*a)) z := by
  rw [unitLowerTerm,rowHeight_eq_shiftedHeightKernel z v hv s ((u:Eis)*a) d (mul_ne_zero u.ne_zero ha),
    GaussGeneratorTransport.norm_eisEmbedding_unit_mul]
  ring

lemma unitLowerTerm_integrable (u : Eisˣ) (v : ℝ) (hv : 0<v)
    (s : ℂ) (hs : 1<s.re) (a d : Eis) (ha : a≠0) :
    Integrable (fun z=>unitLowerTerm u z v s a d) := by
  simp_rw [unitLowerTerm_eq_shifted u _ v hv s a d ha]
  exact (shiftedHeightKernel_integrable v hv s _ hs).const_mul _

lemma unitLowerTerm_fourier_integral (u : Eisˣ) (v : ℝ) (hv : 0<v)
    (s freq : ℂ) (a d : Eis) (ha : a≠0) :
    (∫z:ℂ,unitLowerTerm u z v s a d*ShortDraftTrace.breveE (-freq*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (freq*v))*
        ((‖eisEmbedding a‖^2:ℝ):ℂ)^(-s)*
          ((eisEmbedding (symbol (u:Eis) d)*eisEmbedding (symbol d a))*
            ShortDraftTrace.breveE (freq*eisEmbedding d/eisEmbedding ((u:Eis)*a))) := by
  simp_rw [unitLowerTerm_eq_shifted u _ v hv s a d ha,mul_assoc]
  rw [integral_const_mul,integral_const_mul,integral_const_mul,
    traceIntegral_shiftedHeightKernel v hv s (eisEmbedding d/eisEmbedding ((u:Eis)*a)) freq]
  ring_nf

lemma unitLowerGaussTerm_factor (h a k r : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hu : (u:Eis)=omega^j)
    (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda) :
    (eisEmbedding (symbol (u:Eis) (a+3*r))*eisEmbedding (symbol (a+3*r) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*r)/eisEmbedding ((u:Eis)*a))=
    (ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
      (eisEmbedding (symbol (u:Eis) a)*eisEmbedding (symbol 3 a)))*
        (eisEmbedding (symbol r a)*residueAdditive (3*k) a r) := by
  have hchar : eisEmbedding (symbol (u:Eis) (a+3*r))=
      eisEmbedding (symbol (u:Eis) a)*ShortDraftTrace.breveE ((j:ℂ)*eisEmbedding r/3) := by
    rw [hu]
    exact symbol_omega_pow_primary_shift j a r hprimary
  have hs : symbol (a+3*r) a=symbol (3*r) a := symbol_congr ⟨1,by ring⟩
  rw [hchar,hs,symbol_mul_numerator _ _ _ hprimary,map_mul]
  have hp := unitLower_phase_identity h a r k u j ha hk
  calc
    _ = (eisEmbedding (symbol (u:Eis) a)*eisEmbedding (symbol 3 a)*eisEmbedding (symbol r a))*
      (ShortDraftTrace.breveE ((j:ℂ)*eisEmbedding r/3)*
        ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*r)/eisEmbedding ((u:Eis)*a))) := by ring
    _ = _ := by rw [hp];ring

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma unitLowerTwistedCoefficient_add (h a k r n : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hu : (u:Eis)=omega^j)
    (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda) :
    (eisEmbedding (symbol (u:Eis) (a+3*(r+a*n)))*eisEmbedding (symbol (a+3*(r+a*n)) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*(r+a*n))/eisEmbedding ((u:Eis)*a))=
    (eisEmbedding (symbol (u:Eis) (a+3*r))*eisEmbedding (symbol (a+3*r) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*r)/eisEmbedding ((u:Eis)*a)) := by
  rw [unitLowerGaussTerm_factor h a k (r+a*n) u j ha hprimary hu hk,
    unitLowerGaussTerm_factor h a k r u j ha hprimary hu hk]
  rw [symbol_congr (show a∣r+a*n-r from ⟨n,by ring⟩),
    residueAdditive_three_congr k a (r+a*n) r ha ⟨n,by ring⟩]

lemma unitLowerTerm_weighted_translate (h a k r n : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hu : (u:Eis)=omega^j)
    (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda)
    (z : ℂ) (v : ℝ) (s : ℂ) :
    unitLowerTerm u z v s a (a+3*(r+a*((u:Eis)*n)))*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z)=
    unitLowerTerm u (z+3*eisEmbedding n) v s a (a+3*r)*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding n)) := by
  let c1 := eisEmbedding (symbol (u:Eis) (a+3*(r+a*((u:Eis)*n))))*
    eisEmbedding (symbol (a+3*(r+a*((u:Eis)*n))) a)
  let c0 := eisEmbedding (symbol (u:Eis) (a+3*r))*eisEmbedding (symbol (a+3*r) a)
  let B := ninthCuspFrequency h*eisEmbedding (a+3*r)/eisEmbedding ((u:Eis)*a)
  let Q := ninthCuspFrequency h*(3*eisEmbedding n)
  have hc0 := eisEmbedding_ne_zero (mul_ne_zero u.ne_zero ha)
  have harg : ninthCuspFrequency h*eisEmbedding (a+3*(r+a*((u:Eis)*n)))/eisEmbedding ((u:Eis)*a)=B+Q := by
    dsimp [B,Q]
    simp only [map_add,map_mul,map_ofNat]
    field_simp [eisEmbedding_ne_zero u.ne_zero,eisEmbedding_ne_zero ha]
    ;ring
  have hcoef := unitLowerTwistedCoefficient_add h a k r ((u:Eis)*n) u j ha hprimary hu hk
  change c1*ShortDraftTrace.breveE (ninthCuspFrequency h*
    eisEmbedding (a+3*(r+a*((u:Eis)*n)))/eisEmbedding ((u:Eis)*a))=c0*ShortDraftTrace.breveE B at hcoef
  rw [harg,AddChar.map_add_eq_mul] at hcoef
  have heB : ShortDraftTrace.breveE B≠0 := Complex.exp_ne_zero _
  have heQ : ShortDraftTrace.breveE Q≠0 := Complex.exp_ne_zero _
  have hmult : c1*ShortDraftTrace.breveE Q=c0 := by
    apply mul_right_cancel₀ heB
    calc
      _ = c1*(ShortDraftTrace.breveE B*ShortDraftTrace.breveE Q) := by ring
      _ = _ := hcoef
  have hsolve : c1=c0*ShortDraftTrace.breveE (-Q) := by
    rw [AddChar.map_neg_eq_inv]
    calc
      c1=c1*(ShortDraftTrace.breveE Q*(ShortDraftTrace.breveE Q)⁻¹) := by rw [mul_inv_cancel₀ heQ,mul_one]
      _ = (c1*ShortDraftTrace.breveE Q)*(ShortDraftTrace.breveE Q)⁻¹ := by ring
      _ = _ := by rw [hmult]
  have hrow : eisEmbedding ((u:Eis)*a)*z+eisEmbedding (a+3*(r+a*((u:Eis)*n)))=
      eisEmbedding ((u:Eis)*a)*(z+3*eisEmbedding n)+eisEmbedding (a+3*r) := by
    simp only [map_add,map_mul,map_ofNat]
    ring
  change c1*((v/(‖eisEmbedding ((u:Eis)*a)*z+eisEmbedding (a+3*(r+a*((u:Eis)*n)))‖^2+
    ‖eisEmbedding ((u:Eis)*a)‖^2*v^2):ℝ):ℂ)^s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)=_
  rw [hsolve,hrow]
  unfold unitLowerTerm
  have hphase : -ninthCuspFrequency h*(z+3*eisEmbedding n)=(-Q)+(-ninthCuspFrequency h*z) := by
    dsimp [Q]
    ring
  rw [hphase,AddChar.map_add_eq_mul]
  dsimp only [c0]
  ring

lemma unitLowerIntegral_sum_translate (h a k r : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hu : (u:Eis)=omega^j)
    (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda)
    (v : ℝ) (hv : 0<v) (s : ℂ) (hs : 1<s.re) :
    (∑'n:Eis,unitLowerIntegral u v s (ninthCuspFrequency h) a (a+3*(r+a*((u:Eis)*n))))=
      ∫z:ℂ,unitLowerTerm u z v s a (a+3*r)*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  have hint := trace_mul_integrable (fun z=>unitLowerTerm u z v s a (a+3*r))
    (unitLowerTerm_integrable u v hv s hs a (a+3*r) ha) (ninthCuspFrequency h)
  rw [integral_eq_period_integrals _ hint]
  apply tsum_congr
  intro n
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => unitLowerTerm_weighted_translate h a k r n u j ha hprimary hu hk z v s)

def unitCuspIndexEquiv (u : Eisˣ) : Eis≃Eis where
  toFun n := (u:Eis)*n
  invFun n := (↑u⁻¹:Eis)*n
  left_inv n := by simp [←mul_assoc]
  right_inv n := by simp [←mul_assoc]

end

open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma unitDenominator_integral_formula (u : Eisˣ) (j : ℕ) (hu : (u:Eis)=omega^j)
    (h : Eis) (hh : UnitCuspFrequency h u j) (a : PrimaryLower)
    (v : ℝ) (hv : 0<v) (s : ℂ) (hs : 2<s.re) :
    (∑'d:PrimaryCoprimeDenominator a,unitLowerIntegral u v s (ninthCuspFrequency h) a.val d.val.val)=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s)*unitLowerGauss h u a.val := by
  obtain ⟨k,hk⟩ := unitCuspFrequency_lift h a.val u j (primaryLower_primary a) hh
  let e := (cubicResidueElementEquiv a.val (primaryLower_ne_zero a)).trans (primaryDenominatorEquiv a)
  have hf : Summable (fun d:PrimaryCoprimeDenominator a =>
      unitLowerIntegral u v s (ninthCuspFrequency h) a.val d.val.val) :=
    (hasSum_unitLowerIntegrals u v hv s (ninthCuspFrequency h) hs).summable.sigma_factor a
  have hsum := e.summable_iff.mpr hf
  change Summable (fun q:CubicUnitResidue a.val×Eis =>
    unitLowerIntegral u v s (ninthCuspFrequency h) a.val
      (a.val+3*(GaussianShiftedPartition.representative a.val q.1.val+a.val*q.2))) at hsum
  rw [←e.tsum_eq]
  change (∑'q:CubicUnitResidue a.val×Eis,
    unitLowerIntegral u v s (ninthCuspFrequency h) a.val
      (a.val+3*(GaussianShiftedPartition.representative a.val q.1.val+a.val*q.2)))=_
  rw [hsum.tsum_prod]
  have hinner (r:CubicUnitResidue a.val) :
      (∑'n:Eis,unitLowerIntegral u v s (ninthCuspFrequency h) a.val
        (a.val+3*(GaussianShiftedPartition.representative a.val r.val+a.val*n)))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s)*
          ((eisEmbedding (symbol (u:Eis) (a.val+3*GaussianShiftedPartition.representative a.val r.val))*
            eisEmbedding (symbol (a.val+3*GaussianShiftedPartition.representative a.val r.val) a.val))*
              ShortDraftTrace.breveE (ninthCuspFrequency h*
                eisEmbedding (a.val+3*GaussianShiftedPartition.representative a.val r.val)/eisEmbedding ((u:Eis)*a.val))) := by
    rw [←(unitCuspIndexEquiv u).tsum_eq]
    exact (unitLowerIntegral_sum_translate h a.val k
      (GaussianShiftedPartition.representative a.val r.val) u j (primaryLower_ne_zero a)
      (primaryLower_primary a) hu hk v hv s (by linarith)).trans
        (unitLowerTerm_fourier_integral u v hv s (ninthCuspFrequency h) a.val _ (primaryLower_ne_zero a))
  simp_rw [hinner]
  exact tsum_mul_left

theorem unitLowerEisenstein_fourier (u : Eisˣ) (j : ℕ) (hu : (u:Eis)=omega^j)
    (h : Eis) (hh : UnitCuspFrequency h u j)
    (v : ℝ) (hv : 0<v) (s : ℂ) (hs : 2<s.re) :
    (∫z in periodDomain,eisenstein (integralComplexMatrix (lowerCuspMatrix (u:Eis))*
      upperSection z v hv) s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
          unramifiedCubicGaussSeries s (3*h*(u:Eis)) := by
  have hhSum := hasSum_unitLowerIntegrals u v hv s (ninthCuspFrequency h) hs
  rw [←hhSum.tsum_eq,hhSum.summable.tsum_sigma]
  simp_rw [unitDenominator_integral_formula u j hu h hh _ v hv s hs]
  have he : (∑'a:PrimaryLower,
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s)*unitLowerGauss h u a.val)=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*unitCuspArithmeticSeries s h u := by
    rw [unitCuspArithmeticSeries,←tsum_mul_left]
    apply tsum_congr
    intro a
    ring
  rw [he,unitCuspArithmeticSeries_eq s h u j hu hh]
  ring

end CubicEisenstein

open scoped Classical MatrixGroups
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma levelTwo_entry_integer (g : levelTwo) (i j : Fin 2) :
    (3:Eis)∣((g:SL(2,Eis)) i j-((levelTwoRight g) i j:ℤ)) := by
  have he : Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) (g:SL(2,Eis)) =
      Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) (rationalEmbedding (levelTwoRight g)) := by
    rw [←levelTwo_product g,map_mul]
    have hn : Matrix.SpecialLinearGroup.map (n:=Fin 2)
        (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) (levelTwoLeft g:SL(2,Eis))=1 := (levelTwoLeft g).property
    rw [hn,one_mul]
  have h := congrArg (fun A : SL(2,Eis⧸Ideal.span {(3:Eis)})=>A i j) he
  exact Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h)

def integerUpper (b : ℤ) : SL(2,ℤ) := ⟨!![1,b;0,1],by simp [Matrix.det_fin_two_of]⟩
def integerLower (c : ℤ) : SL(2,ℤ) := ⟨!![1,0;c,1],by simp [Matrix.det_fin_two_of]⟩

lemma levelTwoComplexCharacter_primary (g : levelTwo)
    (ha : lambda^2∣((g:SL(2,Eis)) 0 0)-1) :
    levelTwoComplexCharacter g =
      eisEmbedding (symbol ((g:SL(2,Eis)) 1 0) ((g:SL(2,Eis)) 0 0)) := by
  let A : SL(2,Eis) := g
  let b : ℤ := levelTwoRight g 0 1
  let c : ℤ := levelTwoRight g 1 0
  have hA : (3:Eis)∣A 0 0-1 := three_dvd_primary_sub_one _ ha
  have hB : (3:Eis)∣A 0 1-(b:Eis) := levelTwo_entry_integer g 0 1
  have hC : (3:Eis)∣A 1 0-(c:Eis) := levelTwo_entry_integer g 1 0
  have hdet : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hD : (3:Eis)∣A 1 1-(1+(b:Eis)*(c:Eis)) := by
    have hh := dvd_add (dvd_add (dvd_neg.mpr (dvd_mul_of_dvd_left hA (A 1 1)))
      (dvd_mul_of_dvd_left hB (A 1 0))) (dvd_mul_of_dvd_right hC (b:Eis))
    convert hh using 1 ; linear_combination hdet
  let N : SL(2,Eis) := ⟨!![A 0 0,A 0 1-(b:Eis)*A 0 0;
    A 1 0-(c:Eis)*A 0 0,A 1 1-(c:Eis)*A 0 1-(b:Eis)*(A 1 0-(c:Eis)*A 0 0)],by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet⟩
  have hN : N∈levelThree := by
    apply (mem_levelThree_iff_entries N).mpr
    intro i j
    fin_cases i <;> fin_cases j
    · exact hA
    · have hh:=dvd_sub hB (dvd_mul_of_dvd_right hA (b:Eis))
      convert hh using 1 ; dsimp [N] ; ring
    · have hh:=dvd_sub hC (dvd_mul_of_dvd_right hA (c:Eis))
      convert hh using 1 ; dsimp [N] ; ring
    · have hh:=dvd_add (dvd_sub (dvd_sub hD (dvd_mul_of_dvd_right hB (c:Eis)))
        (dvd_mul_of_dvd_right hC (b:Eis))) (dvd_mul_of_dvd_right hA ((b:Eis)*(c:Eis)))
      convert hh using 1 ; dsimp [N] ; ring
  let lengthScale : levelTwo := ⟨rationalEmbedding (integerLower c),rational_mem_levelTwo _⟩
  let U : levelTwo := ⟨rationalEmbedding (integerUpper b),rational_mem_levelTwo _⟩
  let n : levelThree := ⟨N,hN⟩
  let n2 : levelTwo := ⟨N,levelThree_le_levelTwo hN⟩
  have he : g=lengthScale*n2*U := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change A i j = (((!![(1 : ℤ), 0; c, 1]).map (Int.castRingHom Eis) *
      (N : Matrix (Fin 2) (Fin 2) Eis)) *
      (!![(1 : ℤ), b; 0, 1]).map (Int.castRingHom Eis)) i j
    fin_cases i <;> fin_cases j <;>
      norm_num [N, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  conv_lhs => rw [he,map_mul,map_mul]
  have hL : levelTwoComplexCharacter lengthScale=1 := levelTwoComplexCharacter_rational _
  have hU : levelTwoComplexCharacter U=1 := levelTwoComplexCharacter_rational _
  rw [hL,hU,one_mul,mul_one]
  change levelTwoComplexCharacter ⟨(n:SL(2,Eis)),levelThree_le_levelTwo n.property⟩=_
  rw [levelTwoComplexCharacter_restrict]
  change eisEmbedding (symbol (A 1 0-(c:Eis)*A 0 0) (A 0 0))=_
  congr 1
  exact symbol_congr (x:=A 1 0-(c:Eis)*A 0 0) (y:=A 1 0) (d:=A 0 0) ⟨-(c:Eis),by ring⟩

end CubicKubota

end

end OAI
end OAIOriginalModule0286

/-! Original module: OAI.NumberTheory.DirichletL.Reciprocity.PrimaryCongruences
Source SHA256: 46f58ae465bcd89da31df5400e2cbdf0d06ecd9b9c7ecfc40d0eb6a7f3f67103
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0287


namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section

open scoped Classical MatrixGroups
namespace CubicJacobiGlobal
open ActualEisensteinCubic CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma integer_congruence_primary_cases (c : Eis) (r : ℤ) (h : (3:Eis)∣c-(r:Eis)) :
    (3:Eis)∣c ∨ lambda^2∣c-1 ∨ lambda^2∣(-c)-1 := by
  have hr : (3:ℤ)∣r ∨ (3:ℤ)∣r-1 ∨ (3:ℤ)∣r+1 := by omega
  rcases hr with hr|hr|hr
  · left
    obtain ⟨t,ht⟩:=hr
    have hn:(3:Eis)∣(r:Eis):=⟨(t:Eis),by exact_mod_cast ht⟩
    simpa using dvd_add h hn
  · right;left
    obtain ⟨t,ht⟩:=hr
    have hn:(3:Eis)∣(r:Eis)-1:=⟨(t:Eis),by exact_mod_cast ht⟩
    exact lambda_sq_dvd_three.trans (by simpa using dvd_add h hn)
  · right;right
    obtain ⟨t,ht⟩:=hr
    have hn:(3:Eis)∣(r:Eis)+1:=⟨(t:Eis),by exact_mod_cast ht⟩
    apply lambda_sq_dvd_three.trans
    convert dvd_neg.mpr (dvd_add h hn) using 1 ; ring

lemma symbol_three_shift_primary (c a t:Eis) (hc:lambda^2∣c-1) (ha:lambda^2∣a-1) :
    symbol c (a+3*t*c)=symbol c a := by
  have hs:=primary_add_multiple_three a c t ha
  calc
    _=symbol (a+3*t*c) c:=symbol_reciprocity _ _ (primary_ne_zero _ hc) (primary_ne_zero _ hs) hc hs
    _=symbol a c:=symbol_congr ⟨3*t,by ring⟩
    _=symbol c a:=(symbol_reciprocity _ _ (primary_ne_zero _ hc) (primary_ne_zero _ ha) hc ha).symm

lemma symbol_three_shift_integer (c a t:Eis) (r:ℤ)
    (ha:lambda^2∣a-1) (hc:(3:Eis)∣c-(r:Eis)) :
    symbol c (a+3*t*c)=symbol c a := by
  rcases integer_congruence_primary_cases c r hc with h|h|h
  · exact symbol_three_shift c a t ha h
  · exact symbol_three_shift_primary c a t h ha
  · have hh:=symbol_three_shift_primary (-c) a (-t) h ha
    have he:a+3*(-t)*(-c)=a+3*t*c:=by ring
    rw [he,symbol_neg_numerator _ _ (primary_add_multiple_three a c t ha),
      symbol_neg_numerator _ _ ha] at hh
    exact hh

end CubicJacobiGlobal
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma levelTwo_cube_phase_balance (A N:levelTwo) (p q:Eis) (j:ℕ)
    (hp:lambda^2∣p-1)
    (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1)
    (hN:lambda^2∣((N:SL(2,Eis)) 0 0)-1)
    (hx:(A:SL(2,Eis)) 0 0+3*q*(A:SL(2,Eis)) 1 0=p^j*(N:SL(2,Eis)) 0 0)
    (hc:(N:SL(2,Eis)) 1 0=p^(3-j)*(A:SL(2,Eis)) 1 0) :
    levelTwoComplexCharacter N *
        eisEmbedding (symbol ((A:SL(2,Eis)) 1 0) p)^j =
      levelTwoComplexCharacter A *
        eisEmbedding (symbol ((N:SL(2,Eis)) 0 0) p)^(3-j) := by
  have hs : symbol ((A:SL(2,Eis)) 1 0) ((A:SL(2,Eis)) 0 0) =
      symbol ((A:SL(2,Eis)) 1 0) p ^ j *
        symbol ((A:SL(2,Eis)) 1 0) ((N:SL(2,Eis)) 0 0) := by
    rw [←symbol_three_shift_integer _ _ q (levelTwoRight A 1 0) hA (levelTwo_entry_integer A 1 0),
      hx,symbol_mul_denominator,cubicSymbol_pow_denominator]
  rw [levelTwoComplexCharacter_primary N hN,levelTwoComplexCharacter_primary A hA,hc,
    symbol_mul_numerator _ _ _ hN,symbol_pow_numerator _ _ hN,
    symbol_reciprocity p ((N:SL(2,Eis)) 0 0) (primary_ne_zero _ hp) (primary_ne_zero _ hN) hp hN,
    hs,map_mul,map_pow,map_mul,map_pow]
  ring

lemma levelTwo_comparison_character (A N:levelTwo)
    (hNA:(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹∈levelThree) :
    complexCharacter ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,hNA⟩ *
        levelTwoComplexCharacter A = levelTwoComplexCharacter N := by
  rw [←levelTwoComplexCharacter_restrict ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,hNA⟩]
  change levelTwoComplexCharacter (N*A⁻¹)*levelTwoComplexCharacter A=levelTwoComplexCharacter N
  rw [map_mul,map_inv,mul_assoc]
  have hA:levelTwoComplexCharacter A≠0:=by
    intro he
    have hh:=levelTwoComplexCharacter_cube A
    rw [he] at hh
    norm_num at hh
  rw [inv_mul_cancel₀ hA,mul_one]

lemma levelTwo_cube_comparison_phase (A N:levelTwo) (p q:Eis) (j:ℕ) (hj:j≤3)
    (hp:lambda^2∣p-1)
    (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1)
    (hN:lambda^2∣((N:SL(2,Eis)) 0 0)-1)
    (hx:(A:SL(2,Eis)) 0 0+3*q*(A:SL(2,Eis)) 1 0=p^j*(N:SL(2,Eis)) 0 0)
    (hc:(N:SL(2,Eis)) 1 0=p^(3-j)*(A:SL(2,Eis)) 1 0)
    (hC:IsCoprime ((A:SL(2,Eis)) 1 0) p)
    (hNA:(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹∈levelThree) :
    complexCharacter ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,hNA⟩ =
      eisEmbedding (symbol (((N:SL(2,Eis)) 0 0)*((A:SL(2,Eis)) 1 0)) p)^(3-j) := by
  let a:=eisEmbedding (symbol ((A:SL(2,Eis)) 1 0) p)
  let b:=eisEmbedding (symbol ((N:SL(2,Eis)) 0 0) p)
  have ha3:a^3=1:=by
    dsimp [a]
    rw [←map_pow,symbol_cube_of_isCoprime _ _ hp hC,map_one]
  have hpow:a^j*a^(3-j)=1:=by rw [←pow_add,Nat.add_sub_of_le hj,ha3]
  have hbal:=levelTwo_cube_phase_balance A N p q j hp hA hN hx hc
  change levelTwoComplexCharacter N*a^j=levelTwoComplexCharacter A*b^(3-j) at hbal
  have he:levelTwoComplexCharacter N=levelTwoComplexCharacter A*(b*a)^(3-j):=by
    calc
      _=levelTwoComplexCharacter N*(a^j*a^(3-j)):=by rw [hpow,mul_one]
      _=(levelTwoComplexCharacter N*a^j)*a^(3-j):=(mul_assoc _ _ _).symm
      _=(levelTwoComplexCharacter A*b^(3-j))*a^(3-j):=by rw [hbal]
      _=_:=by rw [mul_pow];ring
  have hcomp:=levelTwo_comparison_character A N hNA
  have hbase:levelTwoComplexCharacter A≠0:=by
    intro he
    have hh:=levelTwoComplexCharacter_cube A
    rw [he] at hh
    norm_num at hh
  rw [symbol_mul_numerator _ _ _ hp,map_mul]
  change complexCharacter ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,hNA⟩=(b*a)^(3-j)
  apply mul_right_cancel₀ hbase
  rw [hcomp,he]
  ring

end CubicKubota
end

open scoped BigOperators Classical

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma ramified_cubicExp_nat_mul (n : ℕ) (t : ℤ) :
    cubicExp ((n:ℤ)*t)=cubicExp t^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,cubicExp_add,ih,pow_succ]

lemma ramified_trace_symbol (a : Eis) (ha : lambda^2∣a-1) :
    symbol ramifiedTraceLambda a=linearRay 0 (-1) a := by
  have h := symbol_traceLambda_eq_linearRay a ha
  change symbol ramifiedTraceLambda a=linearRay 0 (-1) a at h
  exact h

lemma ramifiedSymbol_primaryCoord (j n : ℕ) (A B : ℤ) :
    symbol (omega^j*ramifiedTraceLambda^n) (primaryCoord A B)=
      cubicExp ((j:ℤ)*(2*A-B)-(n:ℤ)*B) := by
  rw [symbol_mul_numerator _ _ _ (primaryCoord_primary _ _),
    symbol_pow_numerator _ _ (primaryCoord_primary _ _) j,
    symbol_pow_numerator _ _ (primaryCoord_primary _ _) n,
    symbol_omega_eq_linearRay _ (primaryCoord_primary _ _),
    ramified_trace_symbol _ (primaryCoord_primary _ _),linearRay_primaryCoord,linearRay_primaryCoord,
    ←ramified_cubicExp_nat_mul,←ramified_cubicExp_nat_mul,←cubicExp_add]
  congr 1
  ring

def ramifiedAffineParameter (j n : ℕ) : Eis := (j:Eis)*ramifiedTraceLambda-(n:Eis)

lemma ramifiedAffineParameter_coords (j n : ℕ) (C D : ℤ) :
    (ActualEisensteinCoordinates.coords
      (ramifiedAffineParameter j n*ActualEisensteinCoordinates.eval C D)).2=
      (j:ℤ)*(2*C-D)-(n:ℤ)*D := by
  have hk : ramifiedAffineParameter j n=ActualEisensteinCoordinates.eval ((j:ℤ)-(n:ℤ)) (2*(j:ℤ)) := by
    change (j:Eis)*(1+2*omega)-(n:Eis)=(((j:ℤ)-(n:ℤ):ℤ):Eis)+((2*(j:ℤ):ℤ):Eis)*omega
    push_cast
    ring
  rw [hk,ActualEisensteinCoordinates.eval_mul,ShortDraftLatticeCount.coords_eval]
  ring

theorem ramified_symbol_primary_shift (j n : ℕ) (a x : Eis) (ha : lambda^2∣a-1) :
    eisEmbedding (symbol (omega^j*ramifiedTraceLambda^n) (a+3*x))=
      eisEmbedding (symbol (omega^j*ramifiedTraceLambda^n) a)*
        ShortDraftTrace.breveE (eisEmbedding (ramifiedAffineParameter j n*x)/eisLam/3) := by
  obtain ⟨A,B,rfl⟩ := exists_primaryCoord a ha
  let C := (ActualEisensteinCoordinates.coords x).1
  let D := (ActualEisensteinCoordinates.coords x).2
  have hx : x=ActualEisensteinCoordinates.eval C D := (ActualEisensteinCoordinates.eval_coords x).symm
  have hsum : primaryCoord A B+3*x=primaryCoord (A+C) (B+D) := by
    rw [hx,primaryCoord_eq,primaryCoord_eq]
    change 1+3*(A:Eis)+3*(B:Eis)*omega+3*((C:Eis)+(D:Eis)*omega)=_
    push_cast
    ring
  rw [hsum,ramifiedSymbol_primaryCoord,ramifiedSymbol_primaryCoord]
  have ht := breveE_real_trace_of_O (3:ℝ) (ramifiedAffineParameter j n*x)
  norm_num only [Complex.ofReal_ofNat] at ht
  rw [ht,hx,ramifiedAffineParameter_coords,←embedding_cubicExp,←map_mul,←cubicExp_add]
  apply congrArg eisEmbedding
  apply congrArg cubicExp
  ring

lemma ramified_symbol_primary_shift_signed (j n : ℕ) (r a x : Eis)
    (hr : r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (ha : lambda^2∣a-1) :
    eisEmbedding (symbol r (a+3*x))=eisEmbedding (symbol r a)*
      ShortDraftTrace.breveE (eisEmbedding (ramifiedAffineParameter j n*x)/eisLam/3) := by
  rcases hr with rfl|rfl
  · exact ramified_symbol_primary_shift j n a x ha
  · rw [symbol_neg_numerator _ _ (primary_add_three a x ha),symbol_neg_numerator _ _ ha]
    exact ramified_symbol_primary_shift j n a x ha

end
section

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedTraceLambda_square : ramifiedTraceLambda^2=(-3:Eis) := by
  unfold ramifiedTraceLambda
  linear_combination 4*ramified_omega_relation

lemma ramified_character_coprime (j n : ℕ) (r a : Eis)
    (hr : r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (ha : lambda^2∣a-1) : IsCoprime r a := by
  have hc3 := (primary_coprime_three a ha).symm
  have ht : ramifiedTraceLambda∣(3:Eis) := by
    refine ⟨-ramifiedTraceLambda,?_⟩
    linear_combination ramifiedTraceLambda_square
  have hcT := hc3.of_isCoprime_of_dvd_left ht
  have hcW : IsCoprime omega a := by
    refine ⟨omega^2,0,?_⟩
    rw [zero_mul,add_zero,←pow_succ,omega_primitive.pow_eq_one]
  have hc : IsCoprime (omega^j*ramifiedTraceLambda^n) a := hcW.pow_left.mul_left hcT.pow_left
  rcases hr with rfl|rfl
  · exact hc
  · exact hc.neg_left

lemma affineCusp_phase_identity (h h1 q a k c x : Eis)
    (ha : a≠0) (hq : q≠0) (hh : h=q*h1) (hk : 3*k=h1+c*a) :
    ShortDraftTrace.breveE (eisEmbedding (c*x)/eisLam/3)*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding (q*a))=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*residueAdditive (3*k) a x := by
  have hk' : eisEmbedding k=(eisEmbedding h1+eisEmbedding c*eisEmbedding a)/3 := by
    apply (eq_div_iff (by norm_num : (3:ℂ)≠0)).mpr
    have he := congrArg eisEmbedding hk
    simp only [map_mul,map_add,map_ofNat] at he
    linear_combination he
  rw [←AddChar.map_add_eq_mul]
  unfold residueAdditive
  rw [←AddChar.map_add_eq_mul]
  apply congrArg ShortDraftTrace.breveE
  rw [hh]
  simp only [ninthCuspFrequency,cuspFrequency,map_add,map_mul,map_ofNat]
  rw [hk']
  field_simp [eisEmbedding_ne_zero ha,eisEmbedding_ne_zero hq,eisLam_ne_zero]
  ;ring

def ramifiedAffineGauss (h q r a : Eis) : ℂ :=
  ∑'x:CubicUnitResidue a,
    (eisEmbedding (symbol r (a+3*GaussianShiftedPartition.representative a x.val))*
      eisEmbedding (symbol (a+3*GaussianShiftedPartition.representative a x.val) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*
        eisEmbedding (a+3*GaussianShiftedPartition.representative a x.val)/eisEmbedding (q*a))

lemma ramifiedAffineGauss_factor (h h1 q r a k : Eis) (j n : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hq : q≠0)
    (hr : r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh : h=q*h1) (hk : 3*k=h1+ramifiedAffineParameter j n*a) :
    ramifiedAffineGauss h q r a=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
        (eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a))*cubicUnitGaussSum k a := by
  rw [ramifiedAffineGauss,cubicUnitGaussSum,←tsum_mul_left]
  apply tsum_congr
  intro x
  let t := GaussianShiftedPartition.representative a x.val
  have hs : symbol (a+3*t) a=symbol (3*t) a := symbol_congr ⟨1,by ring⟩
  change (eisEmbedding (symbol r (a+3*t))*eisEmbedding (symbol (a+3*t) a))*
    ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*t)/eisEmbedding (q*a))=_
  rw [ramified_symbol_primary_shift_signed j n r a t hr hprimary,hs,
    symbol_mul_numerator _ _ _ hprimary]
  rw [map_mul eisEmbedding (symbol 3 a) (symbol t a)]
  have hp := affineCusp_phase_identity h h1 q a k (ramifiedAffineParameter j n) t ha hq hh hk
  calc
    _ = (eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a)*eisEmbedding (symbol t a))*
      (ShortDraftTrace.breveE (eisEmbedding (ramifiedAffineParameter j n*t)/eisLam/3)*
        ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*t)/eisEmbedding (q*a))) := by ring
    _ = _ := by rw [hp];ring

theorem ramifiedAffineGauss_eq_unramified (h h1 q r a k : Eis) (j n : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hq : q≠0)
    (hr : r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh : h=q*h1) (hk : 3*k=h1+ramifiedAffineParameter j n*a) :
    ramifiedAffineGauss h q r a=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
        cubicUnitGaussSum (3*r^2*h1) a := by
  rw [ramifiedAffineGauss_factor h h1 q r a k j n ha hprimary hq hr hh hk]
  have hcop := ramified_character_coprime j n r a hr hprimary
  have hcop3 : IsCoprime (3*r^2) a := (primary_coprime_three a hprimary).symm.mul_left hcop.pow_left
  have hp := cubicUnitGaussSum_phase_shift k (r^2) a ha hprimary hcop3
  have hc := symbol_cube_of_isCoprime r a hprimary hcop
  have hchars : eisEmbedding (symbol (r^2) a)*eisEmbedding (symbol (3*r^2) a)=
      eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a) := by
    rw [←map_mul,←symbol_mul_numerator _ _ a hprimary,
      show r^2*(3*r^2)=3*r^4 by ring,symbol_mul_numerator _ _ a hprimary,
      symbol_pow_numerator _ _ hprimary 4,pow_succ,hc,one_mul,map_mul]
    ring
  rw [hchars] at hp
  have hcong : a∣k*(9*r^2)-3*r^2*h1 := by
    refine ⟨3*r^2*ramifiedAffineParameter j n,?_⟩
    linear_combination 3*r^2*hk
  have hg := cubicUnitGaussSum_frequency_congr (k*(9*r^2)) (3*r^2*h1) a ha hcong
  calc
    _ = ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
      (eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a)*cubicUnitGaussSum k a) := by ring
    _ = _ := by rw [hp,hg]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology Pointwise

open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def eisensteinUnitRotation (u : ActualEisensteinCubic.Oˣ) : ℂ≃ₗᵢ[ℝ]ℂ where
  toFun z := eisEmbedding (u:ActualEisensteinCubic.O)*z
  invFun z := eisEmbedding (↑u⁻¹:ActualEisensteinCubic.O)*z
  left_inv z := by
    dsimp only
    rw [←mul_assoc,←map_mul]
    simp
  right_inv z := by
    dsimp only
    rw [←mul_assoc,←map_mul]
    simp
  map_add' z w := mul_add _ _ _
  map_smul' t z := by
    simp only [RingHom.id_apply,Complex.real_smul]
    ring
  norm_map' z := by
    change ‖eisEmbedding (u:ActualEisensteinCubic.O)*z‖=‖z‖
    rw [norm_mul,GaussGeneratorTransport.norm_eisEmbedding_unit,one_mul]

def eisensteinUnitEquiv (u : ActualEisensteinCubic.Oˣ) : ActualEisensteinCubic.O≃ActualEisensteinCubic.O where
  toFun x := (u:ActualEisensteinCubic.O)*x
  invFun x := (↑u⁻¹:ActualEisensteinCubic.O)*x
  left_inv x := by dsimp only; rw [←mul_assoc];simp
  right_inv x := by dsimp only; rw [←mul_assoc];simp

def periodUnitEquiv (u : ActualEisensteinCubic.Oˣ) : periodLattice≃periodLattice :=
  (periodEquiv.symm.trans (eisensteinUnitEquiv u)).trans periodEquiv

lemma periodUnitEquiv_val (u : ActualEisensteinCubic.Oˣ) (x : periodLattice) :
    (periodUnitEquiv u x:ℂ)=eisEmbedding (u:ActualEisensteinCubic.O)*(x:ℂ) := by
  obtain ⟨n,rfl⟩ := periodEquiv.surjective x
  dsimp only [periodUnitEquiv,Equiv.trans_apply]
  rw [Equiv.symm_apply_apply]
  change (periodEquiv ((u:ActualEisensteinCubic.O)*n):ℂ)=eisEmbedding (u:ActualEisensteinCubic.O)*(periodEquiv n:ℂ)
  change 3*eisEmbedding ((u:ActualEisensteinCubic.O)*n)=eisEmbedding (u:ActualEisensteinCubic.O)*(3*eisEmbedding n)
  rw [map_mul]
  ring

lemma periodDomain_unit_rotation (u : ActualEisensteinCubic.Oˣ) :
    IsAddFundamentalDomain periodLattice (eisensteinUnitRotation u '' periodDomain) volume := by
  apply periodDomain_fundamental.image_of_equiv (eisensteinUnitRotation u).toEquiv
    (eisensteinUnitRotation u).symm.measurePreserving.quasiMeasurePreserving (periodUnitEquiv u⁻¹)
  intro n z
  change eisEmbedding (u:ActualEisensteinCubic.O)*((periodUnitEquiv u⁻¹ n:ℂ)+z)=
    (n:ℂ)+eisEmbedding (u:ActualEisensteinCubic.O)*z
  rw [periodUnitEquiv_val,mul_add,←mul_assoc,←map_mul]
  simp

theorem period_integral_unit_rotation (f : ℂ→ℂ)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n)=f z) (u : ActualEisensteinCubic.Oˣ) :
    (∫z in periodDomain,f (eisEmbedding (u:ActualEisensteinCubic.O)*z))=∫z in periodDomain,f z := by
  have hperiod (n : periodLattice) (z : ℂ) : f (n+ᵥz)=f z := by
    obtain ⟨m,rfl⟩ := periodEquiv.surjective n
    change f (3*eisEmbedding m+z)=f z
    simpa only [add_comm] using hp m z
  have heq := periodDomain_fundamental.setIntegral_eq (periodDomain_unit_rotation u) hperiod
  have hchange := (eisensteinUnitRotation u).measurePreserving.setIntegral_image_emb
    (eisensteinUnitRotation u).toHomeomorph.measurableEmbedding f periodDomain
  exact hchange.symm.trans heq.symm

theorem period_integral_unit_affine (f : ℂ→ℂ)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n)=f z) (u : ActualEisensteinCubic.Oˣ) (b : ℂ) :
    (∫z in periodDomain,f (eisEmbedding (u:ActualEisensteinCubic.O)*z+b))=∫z in periodDomain,f z := by
  have hg : ∀n : ActualEisensteinCubic.O,∀z : ℂ,(fun w=>f (w+b)) (z+3*eisEmbedding n)=(fun w=>f (w+b)) z := by
    intro n z
    dsimp
    rw [show z+3*eisEmbedding n+b=(z+b)+3*eisEmbedding n by ring,hp]
  rw [period_integral_unit_rotation (fun w=>f (w+b)) hg u]
  simpa only [add_comm] using period_integral_translation f hp b

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma integral_upper_triangular_action (T : SL(2,ActualEisensteinCubic.O)) (hc : T 1 0=0)
    (z : ℂ) (v : ℝ) (hv : 0<v) :
    integralComplexMatrix T • upperPoint z v hv=
      upperPoint (eisEmbedding (T 0 0)^2*z+eisEmbedding (T 0 0*T 0 1)) v hv := by
  have hdet : T 0 0*T 1 1=1 := by
    simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using T.property
  let u : ActualEisensteinCubic.Oˣ := ⟨T 1 1,T 0 0,by rw [mul_comm,hdet],hdet⟩
  have hn : ‖eisEmbedding (T 1 1)‖=1 := GaussGeneratorTransport.norm_eisEmbedding_unit u
  have hprod : eisEmbedding (T 1 1)*star (eisEmbedding (T 1 1))=1 := by
    simpa only [Complex.star_def,Complex.normSq_eq_norm_sq,hn,one_pow,Complex.ofReal_one] using
      Complex.mul_conj (eisEmbedding (T 1 1))
  have hstar : star (eisEmbedding (T 1 1))=eisEmbedding (T 0 0) := by
    have hnon : eisEmbedding (T 1 1)≠0 := by
      intro hz
      rw [hz,norm_zero] at hn
      exact zero_ne_one hn
    apply mul_left_cancel₀ hnon
    rw [hprod,←map_mul,mul_comm,hdet,map_one]
  rw [mobius_upperPoint]
  apply upperPoint_congr
  · simp only [integralComplexMatrix_apply,hc,map_zero,zero_mul,zero_add,star_zero,
      mul_zero,add_zero,norm_zero,hn,one_pow,hstar,map_mul]
    norm_num
    ; ring
  · simp only [integralComplexMatrix_apply,hc,map_zero,zero_mul,zero_add,norm_zero,
      hn,one_pow,]
    norm_num

theorem period_integral_upper_triangular
    (F : HyperbolicSpace→ℂ) (v : ℝ) (hv : 0<v)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,
      F (upperPoint (3*(z+3*eisEmbedding n)) v hv)=F (upperPoint (3*z) v hv))
    (T : SL(2,ActualEisensteinCubic.O)) (hc : T 1 0=0) :
    (∫z in periodDomain,F (integralComplexMatrix T • upperPoint (3*z) v hv))=
      ∫z in periodDomain,F (upperPoint (3*z) v hv) := by
  have hdet : T 0 0*T 1 1=1 := by
    simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using T.property
  let u : ActualEisensteinCubic.Oˣ := ⟨T 0 0,T 1 1,hdet,by rw [mul_comm,hdet]⟩
  let f : ℂ→ℂ := fun z=>F (upperPoint (3*z) v hv)
  have he (z : ℂ) : F (integralComplexMatrix T • upperPoint (3*z) v hv)=
      f (eisEmbedding (↑(u^2):ActualEisensteinCubic.O)*z+eisEmbedding (T 0 0*T 0 1)/3) := by
    rw [integral_upper_triangular_action T hc]
    dsimp only [f]
    congr 2
    simp only [Units.val_pow_eq_pow_val,map_pow]
    ring
  simp_rw [he]
  exact period_integral_unit_affine f hp (u^2) _

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal

local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients

lemma series_scaled_three_average_zero (coeff : SubexponentialBesselCoefficients)
    (v : ℝ) (hv : 0<v) : (∫z in periodDomain,coeff.series (v,3*z))=0 := by
  let : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let : IsFiniteMeasure (volume.restrict periodDomain) := isFiniteMeasure_restrict.mpr (by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top)
  let f : ActualEisensteinCubic.O→ℂ→ℂ := fun h z => coeff.term h (v,3*z)
  have hc (h : ActualEisensteinCubic.O) : Continuous (f h) := by
    change Continuous (fun z : ℂ => coeff.term h (v,3*z))
    simp_rw [coeff.term_eq_amplitude v hv h]
    change Continuous (fun z : ℂ => coeff.amplitude v h*
      Complex.exp (2*Real.pi*Complex.I*((cuspFrequency h*(3*z))+
        starRingEnd ℂ (cuspFrequency h*(3*z)))))
    fun_prop
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound v v hv le_rfl
  have hfbound (h : ActualEisensteinCubic.O) (z : ℂ) : ‖f h z‖≤C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖) :=
    hbound h (v,3*z) ⟨le_rfl,le_rfl⟩
  have hi (h : ActualEisensteinCubic.O) : IntegrableOn (f h) periodDomain volume :=
    (integrable_const (C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖))).mono'
      (hc h).aestronglyMeasurable (Eventually.of_forall (hfbound h))
  have hnorm (h : ActualEisensteinCubic.O) : (∫z in periodDomain,‖f h z‖)≤
      volume.real periodDomain*(C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)) := by
    have hh := integral_mono_ae (hi h).norm (integrable_const (C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)))
      (Eventually.of_forall (hfbound h))
    simpa only [setIntegral_const,smul_eq_mul] using hh
  have hs : Summable (fun h : ActualEisensteinCubic.O => ∫z in periodDomain,‖f h z‖) := by
    apply Summable.of_nonneg_of_le (fun h => integral_nonneg (fun z => norm_nonneg _)) hnorm
    exact ((summable_exp_neg_cuspFrequency_norm (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C).mul_left
      (volume.real periodDomain)
  have hterm (h : ActualEisensteinCubic.O) : (∫z in periodDomain,f h z)=0 := by
    have he (z : ℂ) : cuspFrequency h*(3*z)= -cuspFrequency (-(3*h))*z := by
      simp only [cuspFrequency,map_neg,map_mul,map_ofNat]
      ring
    change (∫z in periodDomain,coeff.term h (v,3*z))=0
    simp_rw [coeff.term_eq_amplitude v hv h,he]
    rw [integral_const_mul,integral_cusp_character]
    by_cases hh : h=0
    · simp [hh,amplitude]
    · have hk : -(3*h)≠(0:ActualEisensteinCubic.O) := neg_ne_zero.mpr (mul_ne_zero (by norm_num) hh)
      simp [hk]
  change (∫z in periodDomain,∑'h : ActualEisensteinCubic.O,f h z)=0
  rw [←integral_tsum_of_summable_integral_norm hi hs]
  simp_rw [hterm]
  exact tsum_zero

lemma fullFunction_scaled_three_average (coeff : SubexponentialBesselCoefficients)
    (c : ℂ) (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,coeff.fullFunction c (upperPoint (3*z) v hv))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*c*(v:ℂ)^(2/3:ℂ) := by
  let : IsFiniteMeasure (volume.restrict periodDomain) := isFiniteMeasure_restrict.mpr (by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top)
  have hc : Continuous (fun z : ℂ=>coeff.series (v,3*z)) :=
    (coeff.series_height_continuous v hv).comp (continuous_const.mul continuous_id)
  simp only [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
  rw [integral_add (integrable_const _) (periodDomain_integrable_of_continuous _ hc),
    series_scaled_three_average_zero coeff v hv,add_zero,setIntegral_const]
  rw [Measure.real,periodDomain_volume,ENNReal.toReal_ofReal (by positivity)]
  simp only [Complex.real_smul]
  ring

end SubexponentialBesselCoefficients

theorem cubicSource_scaled_three_average (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction (upperPoint (3*z) v hv))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*((3*(Real.pi:ℂ))*constantArithmeticResidue)*(v:ℂ)^(2/3:ℂ) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_scaled_three_average _ v hv

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open ConcreteTraceCRT CubicKubota EisensteinCuspModThree
local notation "O" => ActualEisensteinCubic.O

lemma lowerCuspMatrix_zero : lowerCuspMatrix (0:ActualEisensteinCubic.O)=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerCuspMatrix]

lemma cubicSource_scaled_periodic (v : ℝ) (hv : 0<v) (n : ActualEisensteinCubic.O) (z : ℂ) :
    cubicSourceResidualFunction (upperPoint (3*(z+3*eisEmbedding n)) v hv)=
      cubicSourceResidualFunction (upperPoint (3*z) v hv) := by
  have he : 3*(z+3*eisEmbedding n)=3*z+3*eisEmbedding (3*n) := by
    rw [map_mul,map_ofNat]
    ring
  rw [cubicSourceResidualFunction_eq_bessel,he]
  exact sourceBesselFunction_period v hv (3*z) (3*n)

lemma sourceCuspRepresentative_periodic (j : Fin 3) (v : ℝ) (hv : 0<v) (n : ActualEisensteinCubic.O) (z : ℂ) :
    cubicSourceResidualFunction (integralComplexMatrix (cuspRepresentative j) •
      upperPoint (3*(z+3*eisEmbedding n)) v hv)=
    cubicSourceResidualFunction (integralComplexMatrix (cuspRepresentative j) •
      upperPoint (3*z) v hv) := by
  fin_cases j
  · simpa [cuspRepresentative,cuspParameter,lowerCuspMatrix_zero] using cubicSource_scaled_periodic v hv n z
  · simpa [cuspRepresentative,cuspParameter,ramifiedSourceFunction] using ramifiedSource_scaled_periodic10 v hv n z
  · simpa [cuspRepresentative,cuspParameter,ramifiedSourceFunction] using ramifiedSource_scaled_periodic19 v hv n z

def sourcePrincipalCuspConstant : ℂ :=
  ((9*Real.sqrt 3/2:ℝ):ℂ)*((3*(Real.pi:ℂ))*constantArithmeticResidue)

lemma sourceCuspRepresentative_average (j : Fin 3) (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction
      (integralComplexMatrix (cuspRepresentative j) • upperPoint (3*z) v hv))=
      (if j=0 then sourcePrincipalCuspConstant else 0)*(v:ℂ)^(2/3:ℂ) := by
  fin_cases j
  · simpa [cuspRepresentative,cuspParameter,lowerCuspMatrix_zero,sourcePrincipalCuspConstant] using
      cubicSource_scaled_three_average v hv
  · simpa [cuspRepresentative,cuspParameter,ramifiedSourceFunction] using ramifiedSource_zero_mode10 v hv
  · simpa [cuspRepresentative,cuspParameter,ramifiedSourceFunction] using ramifiedSource_zero_mode19 v hv

lemma sourceCusp_average_of_decomposition (M : SL(2,ActualEisensteinCubic.O)) (G : levelTwo) (j : Fin 3)
    (T : SL(2,ActualEisensteinCubic.O)) (hT : T 1 0=0) (hM : M=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*T)
    (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) v hv))=
      (levelTwoComplexCharacter G*(if j=0 then sourcePrincipalCuspConstant else 0))*(v:ℂ)^(2/3:ℂ) := by
  have he (z : ℂ) : cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) v hv)=
      levelTwoComplexCharacter G*cubicSourceResidualFunction
        (integralComplexMatrix (cuspRepresentative j) • (integralComplexMatrix T • upperPoint (3*z) v hv)) := by
    rw [hM,map_mul,map_mul,mul_smul,mul_smul,cubicSourceResidualFunction_automorphy]
  simp_rw [he]
  rw [integral_const_mul]
  have hi := period_integral_upper_triangular
    (fun w=>cubicSourceResidualFunction (integralComplexMatrix (cuspRepresentative j) • w))
    v hv (sourceCuspRepresentative_periodic j v hv) T hT
  rw [hi,sourceCuspRepresentative_average]
  ring

def sourceCuspConstant (M : SL(2,ActualEisensteinCubic.O)) : ℂ :=
  ∫z in periodDomain,cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) 1 (by norm_num))

theorem sourceCusp_average_all (M : SL(2,ActualEisensteinCubic.O)) (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) v hv))=
      sourceCuspConstant M*(v:ℂ)^(2/3:ℂ) := by
  obtain ⟨G,j,T,hT,_,_,hM⟩ := three_cusp_decomposition M
  have h1 := sourceCusp_average_of_decomposition M G j T hT hM 1 (by norm_num)
  have hc : sourceCuspConstant M=levelTwoComplexCharacter G*(if j=0 then sourcePrincipalCuspConstant else 0) := by
    simpa only [sourceCuspConstant,Complex.ofReal_one,Complex.one_cpow,mul_one] using h1
  rw [hc]
  exact sourceCusp_average_of_decomposition M G j T hT hM v hv

theorem sourceCuspConstant_decomposition (M : SL(2,ActualEisensteinCubic.O)) (G : levelTwo) (j : Fin 3)
    (T : SL(2,ActualEisensteinCubic.O)) (hT : T 1 0=0) (hM : M=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*T) :
    sourceCuspConstant M=levelTwoComplexCharacter G*(if j=0 then sourcePrincipalCuspConstant else 0) := by
  simpa only [sourceCuspConstant,Complex.ofReal_one,Complex.one_cpow,mul_one] using
    sourceCusp_average_of_decomposition M G j T hT hM 1 (by norm_num)

lemma sourcePrincipalCuspConstant_ne_zero : sourcePrincipalCuspConstant≠0 := by
  unfold sourcePrincipalCuspConstant
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      constantArithmeticResidue_ne_zero

lemma sourceCuspConstant_zero_iff (M : SL(2,ActualEisensteinCubic.O)) (G : levelTwo) (j : Fin 3)
    (T : SL(2,ActualEisensteinCubic.O)) (hT : T 1 0=0) (hM : M=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*T) :
    sourceCuspConstant M=0 ↔ j≠0 := by
  have hG : levelTwoComplexCharacter G≠0 := by
    intro hz
    have hn := norm_levelTwoComplexCharacter G
    rw [hz,norm_zero] at hn
    exact zero_ne_one hn
  rw [sourceCuspConstant_decomposition M G j T hT hM]
  by_cases hj : j=0 <;> simp [hj,hG,sourcePrincipalCuspConstant_ne_zero]

lemma sourceCuspConstant_left (G : levelTwo) (M : SL(2,ActualEisensteinCubic.O)) :
    sourceCuspConstant ((G:SL(2,ActualEisensteinCubic.O))*M)=levelTwoComplexCharacter G*sourceCuspConstant M := by
  unfold sourceCuspConstant
  simp_rw [map_mul,mul_smul,cubicSourceResidualFunction_automorphy]
  exact integral_const_mul _ _

lemma sourceCuspConstant_upper_right (M T : SL(2,ActualEisensteinCubic.O)) (hT : T 1 0=0) :
    sourceCuspConstant (M*T)=sourceCuspConstant M := by
  obtain ⟨G,j,S,hS,_,_,hM⟩ := three_cusp_decomposition M
  have hST : (S*T) 1 0=0 := by
    change (∑k : Fin 2,S 1 k*T k 0)=0
    rw [Fin.sum_univ_two,hS,hT]
    ring
  have he : M*T=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*(S*T) := by rw [hM]; group
  rw [sourceCuspConstant_decomposition (M*T) G j (S*T) hST he,
    sourceCuspConstant_decomposition M G j S hS hM]

end CubicEisenstein

end

end OAI
end OAIOriginalModule0287

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.CubeResidueStrata
Source SHA256: 395f646488de11481dab9fcb1270db591cd5bcce06eff3d828ead02638ecaeed
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0288


namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients

theorem series_cusp_decay (coeff : SubexponentialBesselCoefficients) (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀v z,a≤v → ‖coeff.series (v,z)‖≤C*Real.exp (-residualCuspDecayRate*v) := by
  obtain ⟨D,hD,hterm⟩ := coeff.term_cusp_bound a ha
  let S : ℝ := ∑'h : ActualEisensteinCubic.O,Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖)
  have hS : 0≤S := tsum_nonneg (fun h => (Real.exp_pos _).le)
  have hs := summable_exp_neg_cuspFrequency_norm (Real.pi*a/2) (by positivity)
  refine ⟨D*S*(2/(2*residualCuspDecayRate)),by have := residualCuspDecayRate_pos;positivity,?_⟩
  intro v z hav
  have hv : 0<v := ha.trans_le hav
  have hb (h : ActualEisensteinCubic.O) : ‖coeff.term h (v,z)‖≤
      (D*v*Real.exp (-(2*residualCuspDecayRate)*v))*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖) := by
    by_cases hh : h=0
    · simp only [term,ite_eq_left hh,norm_zero]
      positivity
    have he : Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)≤
        Real.exp (-(2*residualCuspDecayRate)*v)*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 := mul_le_mul_of_nonneg_left (cuspFrequency_norm_lower h hh)
        (show 0≤Real.pi*v/2 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hav (show 0≤Real.pi*‖cuspFrequency h‖/2 by positivity)
      unfold residualCuspDecayRate
      nlinarith
    exact (hterm h v z hav).trans ((mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (by ring))
  have hsum := tsum_of_norm_bounded (hs.hasSum.mul_left (D*v*Real.exp (-(2*residualCuspDecayRate)*v))) hb
  calc
    _ ≤ (D*v*Real.exp (-(2*residualCuspDecayRate)*v))*S := hsum
    _ = (D*S)*(v*Real.exp (-(2*residualCuspDecayRate)*v)) := by ring
    _ ≤ (D*S)*((2/(2*residualCuspDecayRate))*Real.exp (-((2*residualCuspDecayRate)/2)*v)) :=
      mul_le_mul_of_nonneg_left (norm_mul_exp_neg_bound (2*residualCuspDecayRate) v
        (mul_pos (by norm_num) residualCuspDecayRate_pos)) (mul_nonneg hD hS)
    _ = _ := by
      rw [show -((2*residualCuspDecayRate)/2)*v=-residualCuspDecayRate*v by ring]
      ring

theorem series_cubic_decay (coeff : SubexponentialBesselCoefficients) (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀v z,a≤v → ‖coeff.series (v,z)‖≤C/v^3 := by
  obtain ⟨C,hC,hbound⟩ := coeff.series_cusp_decay a ha
  let k := residualCuspDecayRate
  have hk : 0<k := residualCuspDecayRate_pos
  refine ⟨C*(6/k^3),by positivity,?_⟩
  intro v z hav
  have hv : 0<v := ha.trans_le hav
  have he : Real.exp (-k*v)*v^3≤6/k^3 := by
    have hb := Real.pow_div_factorial_le_exp (k*v) (mul_nonneg hk.le hv.le) 3
    norm_num only [Nat.factorial] at hb
    have hm := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-k*v)).le
    rw [←Real.exp_add,show k*v+ -k*v=0 by ring,Real.exp_zero] at hm
    apply (le_div_iff₀ (pow_pos hk 3)).mpr
    nlinarith [hm]
  apply (le_div_iff₀ (pow_pos hv 3)).mpr
  calc
    _ ≤ (C*Real.exp (-k*v))*v^3 := mul_le_mul_of_nonneg_right (hbound v z hav) (pow_nonneg hv.le 3)
    _ = C*(Real.exp (-k*v)*v^3) := by ring
    _ ≤ C*(6/k^3) := mul_le_mul_of_nonneg_left he hC

theorem fullFunction_zero_cubic_decay (coeff : SubexponentialBesselCoefficients) (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀v (hv : 0<v) z,a≤v →
      ‖coeff.fullFunction 0 (upperPoint z v hv)‖≤C/v^3 := by
  obtain ⟨C,hC,hbound⟩ := coeff.series_cubic_decay a ha
  refine ⟨C,hC,fun v hv z hav => ?_⟩
  simpa only [fullFunction,zero_mul,zero_add,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
    using hbound v z hav

end SubexponentialBesselCoefficients
end

open scoped BigOperators Classical MatrixGroups Matrix

section
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal GoodElement)
local notation "Eis" => ActualEisensteinCubic.O
local notation "ramLambda" => (omega-1:Eis)

lemma halfPrimary_lambda_dvd_three : ramLambda ∣ (3:Eis) := by
  exact (dvd_pow_self ramLambda (by decide : (2:ℕ)≠0)).trans lambda_sq_dvd_three

lemma halfPrimary_lambda_not_dvd_one : ¬ramLambda ∣ (1:Eis) := by
  intro h
  exact PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit (isUnit_of_dvd_one h)

lemma halfPrimary_omega_pow (j:ℕ) : ramLambda ∣ omega^j-1 := by
  simpa only [one_pow] using sub_dvd_pow_sub_pow omega (1:Eis) j

lemma halfPrimary_not_negative (j:ℕ) : ¬ramLambda ∣ -(omega^j)-1 := by
  intro h
  have h2 : ramLambda ∣ (2:Eis) := by
    have hh:=dvd_add h (halfPrimary_omega_pow j)
    convert dvd_neg.mpr hh using 1 ;ring
  apply halfPrimary_lambda_not_dvd_one
  convert dvd_sub halfPrimary_lambda_dvd_three h2 using 1 ;ring

abbrev HalfPrimary := {b:Eis // ramLambda ∣ b-1}

lemma halfPrimary_ne_zero (b:HalfPrimary) : b.val≠0 := by
  intro h
  apply halfPrimary_lambda_not_dvd_one
  simpa only [h,zero_sub,dvd_neg] using b.2

lemma halfPrimary_not_dvd (b:HalfPrimary) : ¬ramLambda∣b.val := by
  intro h
  apply halfPrimary_lambda_not_dvd_one
  convert dvd_sub h b.2 using 1 ;ring

def halfPrimaryFromAssociate (p:Fin 3×PrimaryLower) : HalfPrimary :=
  ⟨omega^p.1.val*p.2.val,by
    have ha:ramLambda∣p.2.val-1:=halfPrimary_lambda_dvd_three.trans p.2.2
    convert dvd_add ((halfPrimary_omega_pow p.1.val).mul_right p.2.val) ha using 1 ;ring⟩

lemma halfPrimaryFromAssociate_injective : Function.Injective halfPrimaryFromAssociate := by
  intro p q hpq
  have he:omega^p.1.val*p.2.val=omega^q.1.val*q.2.val:=congrArg Subtype.val hpq
  have hunit (j:Fin 3):IsUnit (omega^j.val):=(omega_primitive.isUnit (by decide)).pow _
  have hs:(Ideal.span {p.2.val}:Ideal Eis)=Ideal.span {q.2.val}:=by
    simpa only [Ideal.span_singleton_mul_left_unit (hunit p.1),
      Ideal.span_singleton_mul_left_unit (hunit q.1)] using
      congrArg (fun z:Eis=>(Ideal.span {z}:Ideal Eis)) he
  have hab:p.2=q.2:=by
    apply Subtype.ext
    have hg:=congrArg primaryGenerator hs
    simpa only [primaryGenerator_span p.2.val (primaryLower_ne_zero p.2) (primaryLower_primary p.2),
      primaryGenerator_span q.2.val (primaryLower_ne_zero q.2) (primaryLower_primary q.2)] using hg
  have hj:p.1=q.1:=by
    apply Fin.ext
    apply omega_primitive.pow_inj p.1.isLt q.1.isLt
    rw [hab] at he
    exact mul_right_cancel₀ (primaryLower_ne_zero q.2) he
  exact Prod.ext hj hab

lemma halfPrimaryFromAssociate_surjective : Function.Surjective halfPrimaryFromAssociate := by
  intro b
  let z:GoodElement:=⟨b.val,PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff b.val |>.mpr
    (halfPrimary_not_dvd b)⟩
  let p:=PrimaryIdealUnitReindex.unitIdealEquiv.symm z
  have he:(p.1:Eis)*primaryGenerator p.2.val=b.val:=
    congrArg Subtype.val (PrimaryIdealUnitReindex.unitIdealEquiv.apply_symm_apply z)
  let a:PrimaryLower:=primaryLowerIdealEquiv.symm p.2
  have ha:a.val=primaryGenerator p.2.val:=rfl
  have hea:(p.1:Eis)*a.val=b.val:=by simpa only [ha] using he
  have hu:ramLambda∣(p.1:Eis)-1:=by
    have hpa:ramLambda∣a.val-1:=halfPrimary_lambda_dvd_three.trans a.2
    have hh:=dvd_sub b.2 (hpa.mul_left (p.1:Eis))
    rw [←hea] at hh
    convert hh using 1 ;ring
  obtain ⟨j,hj|hj⟩:=unit_eq_sign_omega p.1
  · exact ⟨(j,a),Subtype.ext (by simpa only [halfPrimaryFromAssociate,hj] using hea)⟩
  · exact (halfPrimary_not_negative j.val (by simpa only [hj] using hu)).elim

def halfPrimaryAssociateEquiv : Fin 3×PrimaryLower ≃ HalfPrimary :=
  Equiv.ofBijective halfPrimaryFromAssociate
    ⟨halfPrimaryFromAssociate_injective,halfPrimaryFromAssociate_surjective⟩

lemma halfPrimaryAssociateEquiv_apply (j:Fin 3) (a:PrimaryLower) :
    (halfPrimaryAssociateEquiv (j,a)).val=omega^j.val*a.val:=rfl

lemma halfPrimary_tsum (f:Eis→ℂ) :
    (∑'b:HalfPrimary,f b.val)=∑'p:Fin 3×PrimaryLower,f (omega^p.1.val*p.2.val) :=
  halfPrimaryAssociateEquiv.tsum_eq (fun b:HalfPrimary=>f b.val) |>.symm

end

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def unitCuspUpper (b : Eis) : SL(2,Eis) := ⟨!![1,b;0,1],by simp [Matrix.det_fin_two]⟩
def unitCuspDiagonal (u : Eisˣ) : SL(2,Eis) := ⟨!![(u:Eis),0;0,(↑u⁻¹:Eis)],by
  simp [Matrix.det_fin_two]⟩

theorem rational_cusp_lower_factor (u : Eisˣ) (n : ℤ) :
    rationalEmbedding ModularGroup.S*unitCuspUpper (n:Eis)*lowerCuspMatrix (u:Eis)=
      unitCuspDiagonal (-u)*lowerCuspMatrix (-(u:Eis)*(1+(n:Eis)*(u:Eis)))*
        unitCuspUpper (↑u⁻¹:Eis) := by
  apply Subtype.ext
  change ((!![(0 : ℤ), -1; 1, 0]).map (Int.castRingHom Eis) *
    !![1, (n : Eis); 0, 1] * !![1, 0; (u : Eis), 1]) =
    (!![(↑(-u) : Eis), 0; 0, (↑(-u)⁻¹ : Eis)] *
      !![1, 0; -(u : Eis) * (1 + (n : Eis) * (u : Eis)), 1] *
      !![1, (↑u⁻¹ : Eis); 0, 1])
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, neg_mul, Units.val_neg,
      mul_add, add_mul, mul_assoc, add_comm]

lemma unitCuspUpper_section (b : Eis) (z : ℂ) (v : ℝ) (hv : 0<v) :
    integralComplexMatrix (unitCuspUpper b)*upperSection z v hv=
      upperSection (z+eisEmbedding b) v hv := by
  apply Subtype.ext
  change ((!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) Eis).map eisEmbedding *
    !![(Real.sqrt v : ℂ), z / Real.sqrt v; 0, (Real.sqrt v : ℂ)⁻¹]) =
    !![(Real.sqrt v : ℂ), (z + eisEmbedding b) / Real.sqrt v;
      0, (Real.sqrt v : ℂ)⁻¹]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

lemma unitCuspDiagonal_norm (u : Eisˣ) :
    ‖eisEmbedding (u:Eis)‖=1 ∧ ‖eisEmbedding (↑u⁻¹:Eis)‖=1 :=
  ⟨GaussGeneratorTransport.norm_eisEmbedding_unit u,
    GaussGeneratorTransport.norm_eisEmbedding_unit u⁻¹⟩

end CubicEisenstein

open scoped Classical MatrixGroups
namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

abbrev CubeResidueStrata (p:Eis) := Σj:Fin 4,CubicUnitResidue (p^(3-j.val))

def cubeResidueStratumMap (p:Eis) (x:CubeResidueStrata p) : Eis⧸Ideal.span {p^3} :=
  Ideal.Quotient.mk _ (p^x.1.val * GaussianShiftedPartition.representative (p^(3-x.1.val)) x.2.1)

private lemma unit_rep_coprime (c:Eis) (x:CubicUnitResidue c) :
    IsCoprime c (GaussianShiftedPartition.representative c x.1) := by
  apply (isUnit_quotient_span_iff c _).mp
  simpa only [GaussianShiftedPartition.representative_spec] using x.2

private lemma cube_strata_exponents (p:Eis) (hp:Prime p) (j k:Fin 4)
    (b d:Eis) (hb:IsCoprime (p^(3-j.val)) b)
    (he:p^3∣p^j.val*b-p^k.val*d) : ¬j.val<k.val := by
  intro hjk
  have hj3:j.val+1≤3:=by omega
  have hjk':j.val+1≤k.val:=by omega
  have h1:p^(j.val+1)∣p^j.val*b-p^k.val*d:=
    (pow_dvd_pow p hj3).trans he
  have h2:p^(j.val+1)∣p^k.val*d:=
    dvd_mul_of_dvd_left (pow_dvd_pow p hjk') d
  have h3:p^(j.val+1)∣p^j.val*b:=by
    simpa only [sub_add_cancel] using dvd_add h1 h2
  rw [pow_succ] at h3
  have hpb:p∣b:=(mul_dvd_mul_iff_left (pow_ne_zero j.val hp.ne_zero)).mp h3
  have hpc:IsCoprime p b:=hb.of_isCoprime_of_dvd_left
    (dvd_pow_self p (by omega:3-j.val≠0))
  exact (hp.coprime_iff_not_dvd.mp hpc) hpb

lemma cubeResidueStratumMap_injective (p:Eis) (hp:Prime p) :
    Function.Injective (cubeResidueStratumMap p) := by
  rintro ⟨j,b⟩ ⟨k,d⟩ he
  have hd:p^3∣p^j.val*GaussianShiftedPartition.representative (p^(3-j.val)) b.1-
      p^k.val*GaussianShiftedPartition.representative (p^(3-k.val)) d.1 :=
    Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp he)
  have hle:=cube_strata_exponents p hp j k _ _ (unit_rep_coprime _ b) hd
  have hge:=cube_strata_exponents p hp k j _ _ (unit_rep_coprime _ d)
    (by simpa only [neg_sub] using dvd_neg.mpr hd)
  have hjk:j=k:=Fin.ext (by omega)
  subst k
  have hpow:p^3=p^j.val*p^(3-j.val):=by rw [←pow_add,Nat.add_sub_of_le (by omega:j.val≤3)]
  rw [hpow,←mul_sub] at hd
  have hrep:p^(3-j.val)∣GaussianShiftedPartition.representative (p^(3-j.val)) b.1-
      GaussianShiftedPartition.representative (p^(3-j.val)) d.1:=
    (mul_dvd_mul_iff_left (pow_ne_zero j.val hp.ne_zero)).mp hd
  have hbd:b=d:=by
    apply Subtype.ext
    rw [←GaussianShiftedPartition.representative_spec (p^(3-j.val)) b.1,
      ←GaussianShiftedPartition.representative_spec (p^(3-j.val)) d.1]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (Ideal.mem_span_singleton.mpr hrep)
  subst d
  rfl

lemma cubeResidueStratumMap_surjective (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) :
    Function.Surjective (cubeResidueStratumMap p) := by
  intro r
  let a:=GaussianShiftedPartition.representative (p^3) r
  let A:SL(2,Eis):=⟨!![a,-1;1,0],by simp [Matrix.det_fin_two_of]⟩
  obtain ⟨j,hj,N,hx,hc,hNA,hjN,hupper⟩:=cube_average_cusp_reduction A p 0 hp hprimary
  have ha:a=p^j*N 0 0:=by simpa [A] using hx
  have hc':p^3=p^j*N 1 0:=by simpa [A] using hc
  have hpow:p^3=p^j*p^(3-j):=by rw [←pow_add,Nat.add_sub_of_le hj]
  have hN10:N 1 0=p^(3-j):=by
    apply mul_left_cancel₀ (pow_ne_zero j hp.ne_zero)
    exact hc'.symm.trans hpow
  have hcop:IsCoprime (p^(3-j)) (N 0 0):=by
    refine ⟨-N 0 1,N 1 1,?_⟩
    have hd:N 0 0*N 1 1-N 0 1*N 1 0=1:=by
      simpa only [Matrix.det_fin_two] using N.property
    rw [hN10] at hd
    linear_combination hd
  let b:CubicUnitResidue (p^(3-j)):=⟨Ideal.Quotient.mk _ (N 0 0),
    (isUnit_quotient_span_iff _ _).mpr hcop⟩
  refine ⟨⟨⟨j,by omega⟩,b⟩,?_⟩
  change Ideal.Quotient.mk (Ideal.span {p^3})
      (p^j*GaussianShiftedPartition.representative (p^(3-j)) b.1)=r
  rw [←GaussianShiftedPartition.representative_spec (p^3) r]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  apply Ideal.mem_span_singleton.mpr
  change p^3∣p^j*GaussianShiftedPartition.representative (p^(3-j)) b.1-a
  rw [ha,←mul_sub,hpow]
  exact mul_dvd_mul_left (p^j) (gaussRep_mk_congr (p^(3-j)) (N 0 0))

def cubeResidueStrataEquiv (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) :
    CubeResidueStrata p≃(Eis⧸Ideal.span {p^3}) :=
  Equiv.ofBijective (cubeResidueStratumMap p)
    ⟨cubeResidueStratumMap_injective p hp,cubeResidueStratumMap_surjective p hp hprimary⟩

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

def cubeStratumSymbol (p C:Eis) (j:Fin 4) (b:CubicUnitResidue (p^(3-j.val))) : ℂ :=
  eisEmbedding (symbol (GaussianShiftedPartition.representative (p^(3-j.val)) b.1*C) (p^(3-j.val)))

lemma unit_stratum_symbol_gauss (p C:Eis) (hp:lambda^2∣p-1) (n:ℕ) :
    (∑' b:CubicUnitResidue (p^n),
      eisEmbedding (symbol (GaussianShiftedPartition.representative (p^n) b.1*C) (p^n))) =
      cubicUnitGaussSum 0 (p^n)*eisEmbedding (symbol C (p^n)) := by
  rw [cubicUnitGaussSum]
  simp only [mul_zero,residueAdditive,map_zero,cuspFrequency,zero_div,zero_mul,
    AddChar.map_zero_eq_one,mul_one]
  rw [←tsum_mul_right]
  apply tsum_congr
  intro b
  rw [symbol_mul_numerator _ _ _ (primary_pow_congruence p hp n),map_mul]

lemma cubeStratumSymbol_sum (p C:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (hC:IsCoprime C p) (j:Fin 4) :
    (∑' b:CubicUnitResidue (p^(3-j.val)), cubeStratumSymbol p C j b) =
      if j=0 then (Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)
      else if j=3 then 1 else 0 := by
  have h3:eisEmbedding (symbol C (p^3))=1:=by
    rw [cubicSymbol_pow_denominator,symbol_cube_of_isCoprime C p hprimary hC,map_one]
  unfold cubeStratumSymbol
  rw [unit_stratum_symbol_gauss p C hprimary (3-j.val)]
  fin_cases j
  · have hh:=cubicUnitGaussSum_prime_power_zero p hp hprimary 2
    norm_num at hh ⊢
    rw [hh,h3,mul_one]
  · have hh:=cubicUnitGaussSum_prime_power_zero p hp hprimary 1
    norm_num at hh ⊢
    simp [hh]
  · have hh:=cubicUnitGaussSum_prime_power_zero p hp hprimary 0
    norm_num at hh ⊢
    simp [hh]
  · simp

lemma cubeStrata_weighted_sum (p C:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (hC:IsCoprime C p) (w:Fin 4→ℂ) :
    (∑ j:Fin 4, w j * ∑' b:CubicUnitResidue (p^(3-j.val)), cubeStratumSymbol p C j b) =
      w 0*(Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)+w 3 := by
  simp_rw [cubeStratumSymbol_sum p C hp hprimary hC]
  simp [Fin.sum_univ_succ]
  ring

end CubicEisenstein

open scoped Classical MatrixGroups
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma comparison_mod_three (A N:SL(2,Eis)) (hNA:N*A⁻¹∈levelThree) (i j:Fin 2) :
    (3:Eis)∣N i j-A i j := by
  have hh:Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) (N*A⁻¹)=1:=hNA
  rw [map_mul,map_inv] at hh
  have he:=mul_inv_eq_one.mp hh
  have he' :=congrArg (fun B:SL(2,Eis⧸Ideal.span {(3:Eis)})=>B i j) he
  exact Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp he')

lemma comparison_primary (A N:SL(2,Eis)) (hNA:N*A⁻¹∈levelThree)
    (hA:lambda^2∣A 0 0-1) : lambda^2∣N 0 0-1 := by
  have hh:=lambda_sq_dvd_three.trans (comparison_mod_three A N hNA 0 0)
  simpa only [sub_add_sub_cancel] using dvd_add hh hA

lemma comparison_levelTwo (A:levelTwo) (N:SL(2,Eis))
    (hNA:N*(A:SL(2,Eis))⁻¹∈levelThree) : N∈levelTwo := by
  have hh:=Subgroup.mul_mem levelTwo (levelThree_le_levelTwo hNA) A.property
  simpa only [inv_mul_cancel_right] using hh

lemma levelTwo_cube_zero_phase (A N:levelTwo) (p q:Eis)
    (hp:lambda^2∣p-1)
    (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1)
    (hN:lambda^2∣((N:SL(2,Eis)) 0 0)-1)
    (hx:(A:SL(2,Eis)) 0 0+3*q*(A:SL(2,Eis)) 1 0=(N:SL(2,Eis)) 0 0)
    (hc:(N:SL(2,Eis)) 1 0=p^3*(A:SL(2,Eis)) 1 0)
    (hNA:(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹∈levelThree) :
    complexCharacter ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,hNA⟩=1 := by
  have hcop:IsCoprime ((N:SL(2,Eis)) 0 0) p:=by
    refine ⟨(N:SL(2,Eis)) 1 1,-(N:SL(2,Eis)) 0 1*p^2*(A:SL(2,Eis)) 1 0,?_⟩
    have hd:(N:SL(2,Eis)) 0 0*(N:SL(2,Eis)) 1 1-
        (N:SL(2,Eis)) 0 1*(N:SL(2,Eis)) 1 0=1:=by
      simpa only [Matrix.det_fin_two] using (N:SL(2,Eis)).property
    rw [hc] at hd
    linear_combination hd
  have hcube:eisEmbedding (symbol ((N:SL(2,Eis)) 0 0) p)^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime _ _ hp hcop,map_one]
  have hb:=levelTwo_cube_phase_balance A N p q 0 hp hA hN (by simpa using hx) (by simpa using hc)
  simp only [pow_zero,mul_one,Nat.sub_zero,hcube] at hb
  have hcomp:=levelTwo_comparison_character A N hNA
  have hbase:levelTwoComplexCharacter A≠0:=by
    intro he
    have hh:=levelTwoComplexCharacter_cube A
    rw [he] at hh
    norm_num at hh
  apply mul_right_cancel₀ hbase
  rw [one_mul,hcomp,hb]

lemma cube_exponent_zero_of_lower_divisible (A N:SL(2,Eis)) (p q:Eis) (j:ℕ)
    (hp:Prime p) (hC:p∣A 1 0)
    (hx:A 0 0+3*q*A 1 0=p^j*N 0 0) : j=0 := by
  by_contra hj
  have hpx:p∣A 0 0+3*q*A 1 0:=by
    rw [hx]
    exact dvd_mul_of_dvd_left (dvd_pow_self p hj) (N 0 0)
  have hpa:p∣A 0 0:=by
    simpa only [add_sub_cancel_right] using dvd_sub hpx (dvd_mul_of_dvd_right hC (3*q))
  have hone:p∣(1:Eis):=by
    have hh:=dvd_sub (dvd_mul_of_dvd_left hpa (A 1 1)) (dvd_mul_of_dvd_right hC (A 0 1))
    have hd:A 0 0*A 1 1-A 0 1*A 1 0=1:=by
      simpa only [Matrix.det_fin_two] using A.property
    rwa [hd] at hh
  exact hp.not_isUnit (isUnit_of_dvd_one hone)

end CubicKubota

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma cube_affine_coefficient_unit (p C:Eis) (hprimary:lambda^2∣p-1) (hC:IsCoprime C p) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {p^3}) (3*C)) := by
  obtain ⟨t,ht⟩:=(three_dvd_primary_sub_one p hprimary)
  have hp3:IsCoprime p (3:Eis):=by
    refine ⟨1,-t,?_⟩
    linear_combination ht
  apply (isUnit_quotient_span_iff _ _).mpr
  exact hp3.pow_left.mul_right hC.symm.pow_left

def cubeCuspAffineEquiv (p A C:Eis) (hprimary:lambda^2∣p-1) (hC:IsCoprime C p) :
    (Eis⧸Ideal.span {p^3})≃(Eis⧸Ideal.span {p^3}) := by
  let a:=Ideal.Quotient.mk (Ideal.span {p^3}) A
  let u:Units (Eis⧸Ideal.span {p^3}):=(cube_affine_coefficient_unit p C hprimary hC).unit
  exact {
    toFun:=fun r=>a+(u:_) * r
    invFun:=fun r=>(↑u⁻¹:_)*(r-a)
    left_inv:=by
      intro r
      simp only [add_sub_cancel_left,←mul_assoc,Units.inv_mul,one_mul]
    right_inv:=by
      intro r
      simp only [←mul_assoc,Units.mul_inv,one_mul,add_sub_cancel] }

lemma cubeCuspAffineEquiv_apply (p A C:Eis) (hprimary:lambda^2∣p-1) (hC:IsCoprime C p)
    (r:Eis⧸Ideal.span {p^3}) :
    cubeCuspAffineEquiv p A C hprimary hC r=
      Ideal.Quotient.mk (Ideal.span {p^3}) A+
        Ideal.Quotient.mk (Ideal.span {p^3}) (3*C)*r := by
  simp only [cubeCuspAffineEquiv,IsUnit.unit_spec]
  rfl

lemma cubeCuspAffineEquiv_mk (p A C q:Eis) (hprimary:lambda^2∣p-1) (hC:IsCoprime C p) :
    cubeCuspAffineEquiv p A C hprimary hC (Ideal.Quotient.mk _ q)=
      Ideal.Quotient.mk (Ideal.span {p^3}) (A+3*q*C) := by
  rw [cubeCuspAffineEquiv_apply]
  simp only [map_add,map_mul]
  ring

end CubicEisenstein

open scoped Classical MatrixGroups BigOperators
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

structure CubeCuspData (A:SL(2,Eis)) (p q:Eis) where
  exponent : Fin 4
  matrix : SL(2,Eis)
  first : A 0 0+3*q*A 1 0=p^exponent.val*matrix 0 0
  second : p^3*A 1 0=p^exponent.val*matrix 1 0
  congruent : matrix*A⁻¹∈levelThree

def actualCubeCuspData (A:SL(2,Eis)) (p q:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) :
    CubeCuspData A p q := by
  let h:=cube_average_cusp_reduction A p q hp hprimary
  let j:=Classical.choose h
  have hj:j≤3:=(Classical.choose_spec h).1
  let N:=Classical.choose (Classical.choose_spec h).2
  have hN:=(Classical.choose_spec (Classical.choose_spec h).2)
  exact ⟨⟨j,by omega⟩,N,hN.1,hN.2.1,hN.2.2.1⟩

namespace CubeCuspData
variable {A:SL(2,Eis)} {p q:Eis}

lemma lower_eq (d:CubeCuspData A p q) (hp:p≠0) :
    d.matrix 1 0=p^(3-d.exponent.val)*A 1 0 := by
  apply mul_left_cancel₀ (pow_ne_zero d.exponent.val hp)
  rw [←d.second,←mul_assoc,←pow_add,Nat.add_sub_of_le (by omega:d.exponent.val≤3)]

lemma unit_top (d:CubeCuspData A p q) (hp:p≠0) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {p^(3-d.exponent.val)}) (d.matrix 0 0)) := by
  apply (isUnit_quotient_span_iff _ _).mpr
  refine ⟨-d.matrix 0 1*A 1 0,d.matrix 1 1,?_⟩
  have hd:d.matrix 0 0*d.matrix 1 1-d.matrix 0 1*d.matrix 1 0=1:=by
    simpa only [Matrix.det_fin_two] using d.matrix.property
  rw [d.lower_eq hp] at hd
  linear_combination hd

def stratum (d:CubeCuspData A p q) (hp:p≠0) : CubeResidueStrata p :=
  ⟨d.exponent,⟨Ideal.Quotient.mk _ (d.matrix 0 0),d.unit_top hp⟩⟩

lemma stratum_map (d:CubeCuspData A p q) (hp:p≠0) :
    cubeResidueStratumMap p (d.stratum hp)=
      Ideal.Quotient.mk (Ideal.span {p^3}) (A 0 0+3*q*A 1 0) := by
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  apply Ideal.mem_span_singleton.mpr
  change p^3∣p^d.exponent.val*GaussianShiftedPartition.representative
    (p^(3-d.exponent.val)) (Ideal.Quotient.mk _ (d.matrix 0 0))-(A 0 0+3*q*A 1 0)
  rw [d.first,←mul_sub]
  have hpow:p^3=p^d.exponent.val*p^(3-d.exponent.val):=by
    rw [←pow_add,Nat.add_sub_of_le (by omega:d.exponent.val≤3)]
  rw [hpow]
  exact mul_dvd_mul_left _ (gaussRep_mk_congr _ _)

lemma comparison_phase (A2:levelTwo) (d:CubeCuspData (A2:SL(2,Eis)) p q)
    (hp:Prime p) (hprimary:lambda^2∣p-1)
    (hA:lambda^2∣((A2:SL(2,Eis)) 0 0)-1)
    (hC:IsCoprime ((A2:SL(2,Eis)) 1 0) p) :
    complexCharacter ⟨d.matrix*(A2:SL(2,Eis))⁻¹,d.congruent⟩ =
      cubeStratumSymbol p ((A2:SL(2,Eis)) 1 0) d.exponent (d.stratum hp.ne_zero).2 := by
  let N2:levelTwo:=⟨d.matrix,comparison_levelTwo A2 d.matrix d.congruent⟩
  have hN:lambda^2∣d.matrix 0 0-1:=comparison_primary _ _ d.congruent hA
  have he:=levelTwo_cube_comparison_phase A2 N2 p q d.exponent.val
    (by omega:d.exponent.val≤3) hprimary hA hN d.first (d.lower_eq hp.ne_zero) hC d.congruent
  rw [he]
  unfold cubeStratumSymbol
  rw [←map_pow,←cubicSymbol_pow_denominator]
  apply congrArg eisEmbedding
  apply symbol_congr
  have hd:=gaussRep_mk_congr (p^(3-d.exponent.val)) (d.matrix 0 0)
  change p^(3-d.exponent.val)∣d.matrix 0 0*((A2:SL(2,Eis)) 1 0)-
    GaussianShiftedPartition.representative (p^(3-d.exponent.val))
      (Ideal.Quotient.mk _ (d.matrix 0 0))*((A2:SL(2,Eis)) 1 0)
  convert dvd_mul_of_dvd_left (dvd_neg.mpr hd) ((A2:SL(2,Eis)) 1 0) using 1 ; ring

end CubeCuspData
end CubicKubota

end

end OAI
end OAIOriginalModule0288

/-! Original module: OAI.NumberTheory.DirichletL.Reciprocity.RamifiedCuspPhases
Source SHA256: a6f544e2b6c0e7ad808a52b7f40be5fec38caf01a8f5b6e94f91912db65c4776
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0289


namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CubicKubota

open scoped Classical MatrixGroups BigOperators
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def actualCubeCuspPhaseSum (A:levelTwo) (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (w:Fin 4→ℂ) : ℂ :=
  ∑' r:Eis⧸Ideal.span {p^3},
    let d:=actualCubeCuspData (A:SL(2,Eis)) p (GaussianShiftedPartition.representative (p^3) r) hp hprimary
    w d.exponent * complexCharacter ⟨d.matrix*(A:SL(2,Eis))⁻¹,d.congruent⟩

theorem actualCubeCuspPhaseSum_coprime (A:levelTwo) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1)
    (hC:IsCoprime ((A:SL(2,Eis)) 1 0) p) (w:Fin 4→ℂ) :
    actualCubeCuspPhaseSum A p hp hprimary w =
      w 0*(Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)+w 3 := by
  let e:=cubeResidueStrataEquiv p hp hprimary
  let a:=cubeCuspAffineEquiv p ((A:SL(2,Eis)) 0 0) ((A:SL(2,Eis)) 1 0) hprimary hC
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData (A:SL(2,Eis)) p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  let phi (s:CubeResidueStrata p):=w s.1*cubeStratumSymbol p ((A:SL(2,Eis)) 1 0) s.1 s.2
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      w (d r).exponent*complexCharacter ⟨(d r).matrix*(A:SL(2,Eis))⁻¹,(d r).congruent⟩=
        phi (e.symm (a r)) := by
    rw [(d r).comparison_phase A hp hprimary hA hC]
    change phi ((d r).stratum hp.ne_zero)=phi (e.symm (a r))
    apply congrArg phi
    apply e.injective
    rw [e.apply_symm_apply]
    change cubeResidueStratumMap p ((d r).stratum hp.ne_zero)=a r
    rw [(d r).stratum_map hp.ne_zero]
    rw [←cubeCuspAffineEquiv_mk p ((A:SL(2,Eis)) 0 0) ((A:SL(2,Eis)) 1 0)
      (GaussianShiftedPartition.representative (p^3) r) hprimary hC,
      GaussianShiftedPartition.representative_spec]
  let (j:Fin 4):Finite (Eis⧸Ideal.span {p^(3-j.val)}) :=
    finite_quotient_span (pow_ne_zero _ hp.ne_zero)
  let (j:Fin 4):Finite (CubicUnitResidue (p^(3-j.val))) := inferInstance
  have hphi:Summable phi:=Summable.of_finite
  calc
    actualCubeCuspPhaseSum A p hp hprimary w = ∑' r,phi (e.symm (a r)) := by
      unfold actualCubeCuspPhaseSum
      exact tsum_congr hpoint
    _ = ∑' r,phi (e.symm r) := a.tsum_eq (fun r => phi (e.symm r))
    _ = ∑' s,phi s := e.symm.tsum_eq phi
    _ = ∑j:Fin 4,w j*∑' b:CubicUnitResidue (p^(3-j.val)),cubeStratumSymbol p ((A:SL(2,Eis)) 1 0) j b := by
      rw [hphi.tsum_sigma,tsum_fintype]
      apply Finset.sum_congr rfl
      intro j hj
      exact tsum_mul_left (f := fun b:CubicUnitResidue (p^(3-j.val)) =>
        cubeStratumSymbol p ((A:SL(2,Eis)) 1 0) j b) (a := w j)
    _ = _ := cubeStrata_weighted_sum p ((A:SL(2,Eis)) 1 0) hp hprimary hC w

theorem actualCubeCuspPhaseSum_dvd (A:levelTwo) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1)
    (hC:p∣((A:SL(2,Eis)) 1 0)) (w:Fin 4→ℂ) :
    actualCubeCuspPhaseSum A p hp hprimary w =
      w 0*(Ideal.absNorm (Ideal.span {p}):ℂ)^3 := by
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData (A:SL(2,Eis)) p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      w (d r).exponent*complexCharacter ⟨(d r).matrix*(A:SL(2,Eis))⁻¹,(d r).congruent⟩=w 0 := by
    have hj:((d r).exponent:ℕ)=0:=cube_exponent_zero_of_lower_divisible
      (A:SL(2,Eis)) (d r).matrix p _ _ hp hC (d r).first
    have hj':(d r).exponent=0:=Fin.ext hj
    let N:levelTwo:=⟨(d r).matrix,comparison_levelTwo A (d r).matrix (d r).congruent⟩
    have hphase:=levelTwo_cube_zero_phase A N p
      (GaussianShiftedPartition.representative (p^3) r) hprimary hA
      (comparison_primary _ _ (d r).congruent hA)
      (by simpa only [hj,pow_zero,one_mul] using (d r).first)
      (by simpa only [hj,Nat.sub_zero] using (d r).lower_eq hp.ne_zero)
      (d r).congruent
    change w (d r).exponent*complexCharacter ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,(d r).congruent⟩=w 0
    rw [hphase,hj',mul_one]
  calc
    actualCubeCuspPhaseSum A p hp hprimary w = ∑' r:Eis⧸Ideal.span {p^3},w 0 := by
      unfold actualCubeCuspPhaseSum
      exact tsum_congr hpoint
    _ = (Nat.card (Eis⧸Ideal.span {p^3}):ℂ)*w 0 := by
      rw [tsum_const,nsmul_eq_mul]
    _ = _ := by
      change (Ideal.absNorm (Ideal.span {p^3}):ℂ)*w 0 = _
      rw [←Ideal.span_singleton_pow,map_pow,Nat.cast_pow]
      ring

end CubicKubota

namespace CubicEisenstein

section
open scoped BigOperators Classical MatrixGroups Matrix

section
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local notation "ramLambda" => (omega-1:Eis)

lemma onceCusp_trace_lambda : ramifiedTraceLambda*ramLambda=3*omega^2 := by
  unfold ramifiedTraceLambda
  linear_combination -ramified_omega_relation

lemma onceCusp_lambda_dvd_trace : ramLambda∣ramifiedTraceLambda := by
  refine ⟨-omega,?_⟩
  unfold ramifiedTraceLambda
  linear_combination ramified_omega_relation

def onceCuspScale (u:Eisˣ) : Eis := (u:Eis)*ramifiedTraceLambda

def onceCuspComplement (u:Eisˣ) : Eis := -(↑u⁻¹:Eis)*ramifiedTraceLambda

lemma onceCusp_scale_complement (u:Eisˣ) : onceCuspScale u*onceCuspComplement u=3 := by
  calc
    _ = -((u:Eis)*(↑u⁻¹:Eis))*ramifiedTraceLambda^2 := by
      unfold onceCuspScale onceCuspComplement; ring
    _ = 3 := by simp [ramifiedTraceLambda_square]

lemma onceCusp_scale_ne_zero (u:Eisˣ) : onceCuspScale u≠0 := by
  intro h
  have hh:=onceCusp_scale_complement u
  rw [h,zero_mul] at hh
  exact (by norm_num : (0:Eis)≠3) hh

lemma onceCusp_scale_lambda (u:Eisˣ) : (3:Eis)∣onceCuspScale u*ramLambda := by
  refine ⟨(u:Eis)*omega^2,?_⟩
  simp only [onceCuspScale,mul_assoc,onceCusp_trace_lambda]
  ring

lemma onceCusp_complement_lambda (u:Eisˣ) : ramLambda∣onceCuspComplement u :=
  onceCusp_lambda_dvd_trace.mul_left _

lemma onceCusp_scale_coprime (u:Eisˣ) (d:PrimaryLower) : IsCoprime (onceCuspScale u) d.val := by
  apply (isCoprime_mul_unit_left_left u.isUnit _ _).mpr
  apply (primary_coprime_three d.val (primaryLower_primary d)).symm.of_isCoprime_of_dvd_left
  exact ⟨-ramifiedTraceLambda,by linear_combination ramifiedTraceLambda_square⟩

abbrev OnceRamifiedData := Fin 3×UnitLowerData

def onceRamifiedToPrimitive (u:Eisˣ) (p:OnceRamifiedData) : PrimitiveRow := by
  let b:=omega^p.1.val*p.2.1.val
  let d:=p.2.2.val.val
  refine ⟨![onceCuspScale u*(b-d),d],?_,?_,p.2.2.val.2⟩
  · change IsCoprime (onceCuspScale u*(b-d)) d
    apply (onceCusp_scale_coprime u p.2.2.val).mul_left
    apply IsCoprime.symm
    apply (isCoprime_right_congr_of_dvd d (b-d) b ⟨-1,by ring⟩).mpr
    exact ((isCoprime_mul_unit_left_left ((omega_primitive.isUnit (by decide)).pow _) _ _).mpr
      p.2.2.2).symm
  · change (3:Eis)∣onceCuspScale u*(b-d)
    have hb:ramLambda∣b-1:=(halfPrimaryFromAssociate (p.1,p.2.1)).2
    have hd:ramLambda∣d-1:=halfPrimary_lambda_dvd_three.trans p.2.2.val.2
    have hbd:ramLambda∣b-d:=by
      simpa only [sub_sub_sub_cancel_right] using dvd_sub hb hd
    obtain ⟨k,hk⟩:=hbd
    rw [hk,←mul_assoc]
    exact (onceCusp_scale_lambda u).mul_right k

lemma onceRamifiedToPrimitive_bijective (u:Eisˣ) :
    Function.Bijective (onceRamifiedToPrimitive u) := by
  constructor
  · rintro ⟨j,a,d,had⟩ ⟨k,b,e,hbe⟩ h
    have hrow:=congrArg Subtype.val h
    have hde:d=e:=Subtype.ext (congrFun hrow 1)
    subst e
    have he:=congrFun hrow 0
    change onceCuspScale u*(omega^j.val*a.val-d.val)=
      onceCuspScale u*(omega^k.val*b.val-d.val) at he
    have hsub:=mul_left_cancel₀ (onceCusp_scale_ne_zero u) he
    have hassoc:halfPrimaryFromAssociate (j,a)=halfPrimaryFromAssociate (k,b):=by
      apply Subtype.ext
      change omega^j.val*a.val=omega^k.val*b.val
      linear_combination hsub
    have hp:=halfPrimaryFromAssociate_injective hassoc
    have hj:j=k:=congrArg Prod.fst hp
    have hab:a=b:=congrArg Prod.snd hp
    subst k
    subst b
    rfl
  · intro r
    obtain ⟨k,hk⟩:=r.2.2.1
    let d:PrimaryLower:=⟨r.val 1,r.2.2.2⟩
    let b:HalfPrimary:=⟨onceCuspComplement u*k+d.val,by
      have hh:=dvd_add ((onceCusp_complement_lambda u).mul_right k)
        (halfPrimary_lambda_dvd_three.trans d.2)
      convert hh using 1 ;ring⟩
    let p:=halfPrimaryAssociateEquiv.symm b
    have hp:omega^p.1.val*p.2.val=b.val:=
      congrArg Subtype.val (halfPrimaryAssociateEquiv.apply_symm_apply b)
    have hr:onceCuspScale u*(b.val-d.val)=r.val 0:=by
      change onceCuspScale u*(onceCuspComplement u*k+d.val-d.val)=_
      rw [add_sub_cancel_right,←mul_assoc,onceCusp_scale_complement,hk]
    have hcop:IsCoprime p.2.val d.val:=by
      have h0:IsCoprime (b.val-d.val) d.val:=
        (hr ▸ r.2.1).of_isCoprime_of_dvd_left (dvd_mul_left _ _)
      have hb:IsCoprime b.val d.val:=by
        apply IsCoprime.symm
        exact (isCoprime_right_congr_of_dvd d.val (b.val-d.val) b.val ⟨-1,by ring⟩).mp h0.symm
      rw [←hp] at hb
      exact hb.of_isCoprime_of_dvd_left (dvd_mul_left _ _)
    refine ⟨(p.1,⟨p.2,d,hcop⟩),Subtype.ext ?_⟩
    funext i
    fin_cases i
    · change onceCuspScale u*(omega^p.1.val*p.2.val-d.val)=r.val 0
      rw [hp,hr]
    · rfl

def onceRamifiedEquiv (u:Eisˣ) : OnceRamifiedData≃PrimitiveRow :=
  Equiv.ofBijective _ (onceRamifiedToPrimitive_bijective u)

lemma onceRamified_row_phase (u:Eisˣ) (p:OnceRamifiedData) :
    (cosetCharacter (primitiveRowEquiv.symm (onceRamifiedEquiv u p)))⁻¹=
      eisEmbedding (symbol (onceCuspScale u*omega^p.1.val) p.2.2.val.val)*
        eisEmbedding (symbol p.2.2.val.val p.2.1.val) := by
  rw [inverse_cosetCharacter_eq_row_symbol,primitiveRowEquiv_symm_row]
  change eisEmbedding (symbol (onceCuspScale u*(omega^p.1.val*p.2.1.val-p.2.2.val.val))
    p.2.2.val.val)=_
  have hh : symbol (onceCuspScale u*(omega^p.1.val*p.2.1.val-p.2.2.val.val)) p.2.2.val.val=
      symbol ((onceCuspScale u*omega^p.1.val)*p.2.1.val) p.2.2.val.val :=
    symbol_congr ⟨-onceCuspScale u,by ring⟩
  rw [hh,symbol_mul_numerator _ _ _ (primaryLower_primary p.2.2.val),
    symbol_reciprocity p.2.1.val p.2.2.val.val (primaryLower_ne_zero p.2.1)
      (primaryLower_ne_zero p.2.2.val) (primaryLower_primary p.2.1)
        (primaryLower_primary p.2.2.val),map_mul]

end

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def diagonalPrimitiveMap (u:Eisˣ) (v:PrimitiveRow) : PrimitiveRow :=
  ⟨![(u:Eis)^2*v.val 0,v.val 1],by
    refine ⟨?_,?_,v.2.2.2⟩
    · exact (isCoprime_mul_unit_left_left (u.isUnit.pow 2) _ _).mpr v.2.1
    · exact v.2.2.1.mul_left _⟩

def diagonalPrimitiveEquiv (u:Eisˣ) : PrimitiveRow≃PrimitiveRow where
  toFun:=diagonalPrimitiveMap u
  invFun:=diagonalPrimitiveMap u⁻¹
  left_inv v:=by
    apply Subtype.ext
    funext i
    fin_cases i
    · change (↑u⁻¹:Eis)^2*((u:Eis)^2*v.val 0)=v.val 0
      rw [←mul_assoc,←mul_pow]
      simp
    · rfl
  right_inv v:=by
    apply Subtype.ext
    funext i
    fin_cases i
    · change (u:Eis)^2*((↑u⁻¹:Eis)^2*v.val 0)=v.val 0
      rw [←mul_assoc,←mul_pow]
      simp
    · rfl

lemma rowOperator_unitCuspDiagonal (u:Eisˣ) (v:PrimitiveRow) :
    rowOperator (integralComplexMatrix (unitCuspDiagonal u))
      (embeddedRow (primitiveRowEquiv.symm v))=
      eisEmbedding (↑u⁻¹:Eis) •
        embeddedRow (primitiveRowEquiv.symm (diagonalPrimitiveEquiv u v)) := by
  simp only [embeddedRow, Function.comp_def, primitiveRowEquiv_symm_row]
  rw [rowOperator_apply]
  funext i
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two,
    integralComplexMatrix_apply, Pi.smul_apply, smul_eq_mul]
  fin_cases i
  · change eisEmbedding (v.val 0) * eisEmbedding (u : Eis) +
      eisEmbedding (v.val 1) * eisEmbedding (0 : Eis) =
      eisEmbedding (↑u⁻¹ : Eis) * eisEmbedding ((u : Eis) ^ 2 * v.val 0)
    simp only [map_zero, mul_zero, add_zero, map_mul, pow_two]
    have hu : eisEmbedding (↑u⁻¹ : Eis) * eisEmbedding (u : Eis) = 1 := by
      rw [← map_mul]
      simp
    calc
      _ = (eisEmbedding (↑u⁻¹ : Eis) * eisEmbedding (u : Eis)) *
          (eisEmbedding (v.val 0) * eisEmbedding (u : Eis)) := by rw [hu, one_mul]
      _ = _ := by ring
  · change eisEmbedding (v.val 0) * eisEmbedding (0 : Eis) +
      eisEmbedding (v.val 1) * eisEmbedding (↑u⁻¹ : Eis) =
      eisEmbedding (↑u⁻¹ : Eis) * eisEmbedding (v.val 1)
    simp [mul_comm]

lemma rowEnergy_unit_smul (u:Eisˣ) (v:Fin 2→ℂ) :
    rowEnergy (eisEmbedding (u:Eis) • v)=rowEnergy v := by
  simp only [rowEnergy,Pi.smul_apply,smul_eq_mul,norm_mul,
    GaussGeneratorTransport.norm_eisEmbedding_unit,one_mul]

lemma diagonal_ray_summand (u:Eisˣ) (g:SL(2,ℂ)) (s:ℂ) (v:PrimitiveRow) :
    summand (integralComplexMatrix (unitCuspDiagonal u)*g) s (primitiveRowEquiv.symm v)=
      eisEmbedding (symbol ((↑u⁻¹:Eis)^2) (v.val 1))*
        summand g s (primitiveRowEquiv.symm (diagonalPrimitiveEquiv u v)) := by
  have hphase : (cosetCharacter (primitiveRowEquiv.symm v))⁻¹=
      eisEmbedding (symbol ((↑u⁻¹:Eis)^2) (v.val 1))*
        (cosetCharacter (primitiveRowEquiv.symm (diagonalPrimitiveEquiv u v)))⁻¹ := by
    simp only [inverse_cosetCharacter_eq_row_symbol,primitiveRowEquiv_symm_row]
    change eisEmbedding (symbol (v.val 0) (v.val 1))=
      eisEmbedding (symbol ((↑u⁻¹:Eis)^2) (v.val 1))*
        eisEmbedding (symbol ((u:Eis)^2*v.val 0) (v.val 1))
    rw [←map_mul,←symbol_mul_numerator _ _ _ (lambda_sq_dvd_three.trans v.2.2.2)]
    congr 2
    rw [←mul_assoc,←mul_pow]
    simp
  rw [summand,←rowOperator_mul,rowOperator_unitCuspDiagonal,map_smul,rowEnergy_unit_smul,hphase,
    summand]
  ring

def rayEisenstein (r:Eis) (g:SL(2,ℂ)) (s:ℂ) : ℂ :=
  ∑'v:PrimitiveRow,eisEmbedding (symbol r (v.val 1))*summand g s (primitiveRowEquiv.symm v)

theorem eisenstein_unit_diagonal (u:Eisˣ) (g:SL(2,ℂ)) (s:ℂ) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*g) s=
      rayEisenstein ((↑u⁻¹:Eis)^2) g s := by
  rw [eisenstein,←primitiveRowEquiv.symm.tsum_eq]
  simp_rw [diagonal_ray_summand]
  exact (diagonalPrimitiveEquiv u).tsum_eq
    (fun v:PrimitiveRow=>eisEmbedding (symbol ((↑u⁻¹:Eis)^2) (v.val 1))*
      summand g s (primitiveRowEquiv.symm v))

end

section
open MeasureTheory
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def affineLowerTerm (q r:Eis) (z:ℂ) (v:ℝ) (s:ℂ) (a d:Eis) : ℂ :=
  (eisEmbedding (symbol r d)*eisEmbedding (symbol d a))*
    ((v/(‖eisEmbedding (q*a)*z+eisEmbedding d‖^2+
      ‖eisEmbedding (q*a)‖^2*v^2):ℝ):ℂ)^s

lemma affineLowerTerm_mul_ray (q r t:Eis) (z:ℂ) (v:ℝ) (s:ℂ) (a d:PrimaryLower) :
    eisEmbedding (symbol t d.val)*affineLowerTerm q r z v s a.val d.val=
      affineLowerTerm q (t*r) z v s a.val d.val := by
  rw [affineLowerTerm,affineLowerTerm,symbol_mul_numerator _ _ _ (primaryLower_primary d),
    map_mul eisEmbedding (symbol t d.val) (symbol r d.val)]
  ring

lemma onceRamified_summand (u:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) (p:OnceRamifiedData) :
    summand (integralComplexMatrix (lowerCuspMatrix (onceCuspScale u))*upperSection z v hv) s
      (primitiveRowEquiv.symm (onceRamifiedEquiv u p))=
      affineLowerTerm (onceCuspScale u*omega^p.1.val) (onceCuspScale u*omega^p.1.val)
        z v s p.2.1.val p.2.2.val.val := by
  let r:Fin 2→ℂ:=![eisEmbedding ((onceCuspScale u*omega^p.1.val)*p.2.1.val),
    eisEmbedding p.2.2.val.val]
  have hr:rowOperator (integralComplexMatrix (lowerCuspMatrix (onceCuspScale u)))
      (embeddedRow (primitiveRowEquiv.symm (onceRamifiedEquiv u p)))=r:=by
    rw [embeddedRow, primitiveRowEquiv_symm_row, rowOperator_lowerCusp]
    funext i
    fin_cases i <;>
      simp [onceRamifiedEquiv, Equiv.ofBijective_apply, onceRamifiedToPrimitive,
        r, map_mul, map_sub, mul_sub, mul_assoc]
  have hr0:r≠0:=by
    intro hh
    have he:=congrFun hh 1
    exact eisEmbedding_ne_zero (primaryLower_ne_zero p.2.2.val) he
  have hp:=heightDenominator_pos z v hv r hr0
  rw [summand,←rowOperator_mul,hr,rowEnergy_upperSection,onceRamified_row_phase]
  change _= (eisEmbedding (symbol (onceCuspScale u*omega^p.1.val) p.2.2.val.val)*
    eisEmbedding (symbol p.2.2.val.val p.2.1.val))*((v/heightDenominator z v r:ℝ):ℂ)^s
  have hi:((v/heightDenominator z v r:ℝ):ℂ)=(((heightDenominator z v r/v:ℝ):ℂ))⁻¹:=by
    simp only [Complex.ofReal_div,inv_div]
  rw [hi,Complex.inv_cpow_ofReal_nonneg (div_nonneg hp.le hv.le),Complex.cpow_neg]

def diagonalOnceCuspIndex (u t:Eisˣ) : OnceRamifiedData≃CuspCosets :=
  (onceRamifiedEquiv t).trans ((diagonalPrimitiveEquiv u).symm.trans primitiveRowEquiv.symm)

def diagonalUnitCuspIndex (u t:Eisˣ) : UnitLowerData≃CuspCosets :=
  (unitLowerEquiv t).trans ((diagonalPrimitiveEquiv u).symm.trans primitiveRowEquiv.symm)

lemma diagonal_once_summand (u t:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) (p:OnceRamifiedData) :
    summand (integralComplexMatrix (unitCuspDiagonal u)*
      (integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv)) s
      (diagonalOnceCuspIndex u t p)=
      affineLowerTerm (onceCuspScale t*omega^p.1.val)
        ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^p.1.val)) z v s p.2.1.val p.2.2.val.val := by
  change summand _ _ (primitiveRowEquiv.symm
    ((diagonalPrimitiveEquiv u).symm (onceRamifiedEquiv t p)))=_
  rw [diagonal_ray_summand,Equiv.apply_symm_apply,onceRamified_summand]
  change eisEmbedding (symbol ((↑u⁻¹:Eis)^2) p.2.2.val.val)*affineLowerTerm _ _ _ _ _ _ _=_
  exact affineLowerTerm_mul_ray _ _ _ _ _ _ p.2.1 p.2.2.val

lemma diagonal_unit_summand (u t:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) (p:UnitLowerData) :
    summand (integralComplexMatrix (unitCuspDiagonal u)*
      (integralComplexMatrix (lowerCuspMatrix (t:Eis)))*upperSection z v hv) s
      (diagonalUnitCuspIndex u t p)=
      affineLowerTerm (t:Eis) ((↑u⁻¹:Eis)^2*(t:Eis)) z v s p.1.val p.2.val.val := by
  rw [mul_assoc]
  change summand _ _ (primitiveRowEquiv.symm
    ((diagonalPrimitiveEquiv u).symm (unitLowerEquiv t p)))=_
  rw [diagonal_ray_summand,Equiv.apply_symm_apply,unitLower_summand]
  change eisEmbedding (symbol ((↑u⁻¹:Eis)^2) p.2.val.val)*affineLowerTerm _ _ _ _ _ _ _=_
  exact affineLowerTerm_mul_ray _ _ _ _ _ _ p.1 p.2.val

theorem diagonal_once_eisenstein_rows (u t:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      (integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv)) s=
      ∑'p:OnceRamifiedData,affineLowerTerm (onceCuspScale t*omega^p.1.val)
        ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^p.1.val)) z v s p.2.1.val p.2.2.val.val := by
  rw [eisenstein,←(diagonalOnceCuspIndex u t).tsum_eq]
  exact tsum_congr (diagonal_once_summand u t z v hv s)

theorem diagonal_unit_eisenstein_rows (u t:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      (integralComplexMatrix (lowerCuspMatrix (t:Eis)))*upperSection z v hv) s=
      ∑'p:UnitLowerData,affineLowerTerm (t:Eis) ((↑u⁻¹:Eis)^2*(t:Eis))
        z v s p.1.val p.2.val.val := by
  rw [eisenstein,←(diagonalUnitCuspIndex u t).tsum_eq]
  exact tsum_congr (diagonal_unit_summand u t z v hv s)

theorem hasSum_diagonal_once_integrals (u t:Eisˣ) (v:ℝ) (hv:0<v) (s freq:ℂ) (hs:2<s.re) :
    HasSum (fun p:OnceRamifiedData=>∫z in periodDomain,
      affineLowerTerm (onceCuspScale t*omega^p.1.val)
        ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^p.1.val)) z v s p.2.1.val p.2.2.val.val*
          ShortDraftTrace.breveE (-freq*z))
      (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
        integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv) s*
          ShortDraftTrace.breveE (-freq*z)) := by
  have hh:=(diagonalOnceCuspIndex u t).hasSum_iff.mpr
    (hasSum_integral_fixed_left_Eisenstein
      (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (onceCuspScale t)))
      v hv s freq hs)
  apply hh.congr_fun
  intro p
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z=>by dsimp only; rw [mul_assoc,diagonal_once_summand])

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

open ConcreteTraceCRT EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def eisensteinCoordinateMul (b : ActualEisensteinCubic.O) (x : Fin 2→ℝ) : Fin 2→ℝ :=
  ![(ActualEisensteinCoordinates.coords b).1 • x 0-(ActualEisensteinCoordinates.coords b).2 • x 1,
    (ActualEisensteinCoordinates.coords b).2 • x 0+
      ((ActualEisensteinCoordinates.coords b).1-(ActualEisensteinCoordinates.coords b).2) • x 1]

def eisensteinTorusMul (b : ActualEisensteinCubic.O) : UnitAddTorus (Fin 2)→+UnitAddTorus (Fin 2) where
  toFun t :=
    ![(ActualEisensteinCoordinates.coords b).1 • t 0-(ActualEisensteinCoordinates.coords b).2 • t 1,
      (ActualEisensteinCoordinates.coords b).2 • t 0+
        ((ActualEisensteinCoordinates.coords b).1-(ActualEisensteinCoordinates.coords b).2) • t 1]
  map_zero' := by ext i;fin_cases i <;> simp
  map_add' t s := by ext i;fin_cases i <;> simp [smul_add] <;> abel

lemma eisensteinTorusMul_continuous (b : ActualEisensteinCubic.O) : Continuous (eisensteinTorusMul b) := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun t : UnitAddTorus (Fin 2) => (ActualEisensteinCoordinates.coords b).1 • t 0-(ActualEisensteinCoordinates.coords b).2 • t 1)
    fun_prop
  · change Continuous (fun t : UnitAddTorus (Fin 2) => (ActualEisensteinCoordinates.coords b).2 • t 0+((ActualEisensteinCoordinates.coords b).1-(ActualEisensteinCoordinates.coords b).2) • t 1)
    fun_prop

lemma periodVector_coordinateMul (b : ActualEisensteinCubic.O) (x : Fin 2→ℝ) :
    periodVector (eisensteinCoordinateMul b x)=eisEmbedding b*periodVector x := by
  have hb : eisEmbedding b=((ActualEisensteinCoordinates.coords b).1:ℂ)+
      ((ActualEisensteinCoordinates.coords b).2:ℂ)*omega3 := by
    simpa only [ActualEisensteinCubic.eisEmbedding_eval] using (congrArg eisEmbedding (ActualEisensteinCoordinates.eval_coords b)).symm
  rw [periodVector_apply,periodVector_apply,hb]
  simp only [eisensteinCoordinateMul,Matrix.cons_val_zero,Matrix.cons_val_one,
    zsmul_eq_mul]
  push_cast
  linear_combination -(3*((ActualEisensteinCoordinates.coords b).2:ℂ)*(x 1:ℂ))*EisensteinEmbedding.omega3_sq

lemma eisensteinTorusMul_periodTorus (b : ActualEisensteinCubic.O) (z : ℂ) :
    eisensteinTorusMul b (periodTorus z)=periodTorus (eisEmbedding b*z) := by
  obtain ⟨x,rfl⟩ := periodVector.surjective z
  rw [←periodVector_coordinateMul,periodTorus_periodVector,periodTorus_periodVector]
  ext i
  fin_cases i <;> rfl

lemma eisensteinTorusMul_surjective (b : ActualEisensteinCubic.O) (hb : b≠0) : Function.Surjective (eisensteinTorusMul b) := by
  intro t
  refine ⟨periodTorus ((eisEmbedding b)⁻¹*periodSection t),?_⟩
  rw [eisensteinTorusMul_periodTorus,←mul_assoc,mul_inv_cancel₀ (eisEmbedding_ne_zero hb),one_mul,
    periodTorus_section]

theorem eisensteinTorusMul_measurePreserving (b : ActualEisensteinCubic.O) (hb : b≠0) :
    MeasurePreserving (eisensteinTorusMul b) volume volume :=
  AddMonoidHom.measurePreserving (eisensteinTorusMul_continuous b) (eisensteinTorusMul_surjective b hb) rfl

lemma periodTorus_eq_implies_lattice_difference (z w : ℂ) (h : periodTorus z=periodTorus w) :
    ∃n : ActualEisensteinCubic.O,z=w+3*eisEmbedding n := by
  obtain ⟨x,rfl⟩ := periodVector.surjective z
  obtain ⟨y,rfl⟩ := periodVector.surjective w
  rw [periodTorus_periodVector,periodTorus_periodVector] at h
  have hz (i : Fin 2) : ((x i-y i:ℝ):UnitAddCircle)=0 := by
    rw [AddCircle.coe_sub,congrFun h i,sub_self]
  obtain ⟨n0,hn0⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp (hz 0)
  obtain ⟨n1,hn1⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp (hz 1)
  simp only [zsmul_eq_mul,mul_one] at hn0 hn1
  have hx0 : x 0=y 0+n0 := by linarith
  have hx1 : x 1=y 1+n1 := by linarith
  refine ⟨ActualEisensteinCoordinates.eval n0 n1,?_⟩
  rw [periodVector_apply,periodVector_apply,ActualEisensteinCubic.eisEmbedding_eval,hx0,hx1]
  push_cast
  ring

lemma periodic_function_periodSection (f : ℂ→ℂ)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n)=f z) (z : ℂ) :
    f (periodSection (periodTorus z))=f z := by
  obtain ⟨n,hn⟩ := periodTorus_eq_implies_lattice_difference (periodSection (periodTorus z)) z
    (periodTorus_section (periodTorus z))
  rw [hn,hp]

theorem period_integral_eisenstein_mul (f : ℂ→ℂ) (hf : Measurable f)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n)=f z) (b : ActualEisensteinCubic.O) (hb : b≠0) :
    (∫z in periodDomain,f (eisEmbedding b*z))=∫z in periodDomain,f z := by
  let F : UnitAddTorus (Fin 2)→ℂ := fun t=>f (periodSection t)
  have hF : Measurable F := hf.comp periodSection_measurableEmbedding.measurable
  have hm := eisensteinTorusMul_measurePreserving b hb
  have hi : (∫t,F (eisensteinTorusMul b t))=∫t,F t := by
    have hh := integral_map («μ» := (volume : Measure (UnitAddTorus (Fin 2)))) hm.measurable.aemeasurable hF.stronglyMeasurable.aestronglyMeasurable
    rw [hm.map_eq] at hh
    exact hh.symm
  rw [periodTorus_integral,periodTorus_integral] at hi
  simp only [eisensteinTorusMul_periodTorus,F,periodic_function_periodSection f hp] at hi
  simp only [Complex.real_smul] at hi
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (show (2/(9*Real.sqrt 3):ℝ)≠0 by positivity)) hi

end CubicEisenstein

open MeasureTheory Filter
open scoped BigOperators Classical ENNReal

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem finite_index_period_unfold_of_summable (q:Eis) (hq:q≠0) (f:ℂ→ℂ) (hf:Integrable f)
    (hsum:Summable (fun n:Eis=>∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q))) :
    (∑'n:Eis,∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*(∫z:ℂ,f z) := by
  let : Finite (Eis⧸Ideal.span {q}):=finite_quotient_span hq
  let : Fintype (Eis⧸Ideal.span {q}):=Fintype.ofFinite _
  let I:Eis→ℂ:=fun n=>∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q)
  have hinner (r:Eis⧸Ideal.span {q}) :
      (∑'n:((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}),I n.val)=∫z:ℂ,f z := by
    rw [GaussianFiberEquiv.fiber_tsum q hq r (GaussianShiftedPartition.representative q r)
      (GaussianShiftedPartition.representative_spec q r)]
    let b:=3*eisEmbedding (GaussianShiftedPartition.representative q r)/eisEmbedding q
    have he (n:Eis) (z:ℂ) :
        z+3*eisEmbedding (GaussianShiftedPartition.representative q r+q*n)/eisEmbedding q=
          (z+3*eisEmbedding n)+b := by
      dsimp [b]
      simp only [map_add,map_mul]
      field_simp [eisEmbedding_ne_zero hq]
      ;ring
    change (∑'n:Eis,∫z in periodDomain,f (z+3*eisEmbedding
      (GaussianShiftedPartition.representative q r+q*n)/eisEmbedding q))=_
    simp_rw [he]
    rw [←integral_eq_period_integrals (fun z=>f (z+b)) (hf.comp_add_right b)]
    exact integral_add_right_eq_self f b
  have hsplit:=(hsum.hasSum.tsum_fiberwise (Ideal.Quotient.mk (Ideal.span {q}))).tsum_eq.symm
  change (∑'n:Eis,I n)=_ at hsplit ⊢
  rw [hsplit]
  change (∑'r:Eis⧸Ideal.span {q},∑'n:((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}),I n.val)=_
  simp only [hinner,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  congr 1
  change (Fintype.card (Eis⧸Ideal.span {q}):ℂ)=(Nat.card (Eis⧸Ideal.span {q}):ℂ)
  rw [Nat.card_eq_fintype_card]

lemma finite_index_period_lintegral (q:Eis) (hq:q≠0) (f:ℂ→ℝ≥0∞) :
    (∑'n:Eis,∫⁻z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q))=
      (Ideal.absNorm (Ideal.span {q}):ℝ≥0∞)*(∫⁻z:ℂ,f z) := by
  let : Finite (Eis⧸Ideal.span {q}):=finite_quotient_span hq
  let : Fintype (Eis⧸Ideal.span {q}):=Fintype.ofFinite _
  let I:Eis→ℝ≥0∞:=fun n=>∫⁻z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q)
  have hinner (r:Eis⧸Ideal.span {q}) :
      (∑'n:((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}),I n.val)=∫⁻z:ℂ,f z := by
    rw [←(GaussianFiberEquiv.fiberEquiv q hq r (GaussianShiftedPartition.representative q r)
      (GaussianShiftedPartition.representative_spec q r)).tsum_eq]
    change (∑'n:Eis,∫⁻z in periodDomain,f (z+3*eisEmbedding
      (GaussianShiftedPartition.representative q r+q*n)/eisEmbedding q))=_
    let b:=3*eisEmbedding (GaussianShiftedPartition.representative q r)/eisEmbedding q
    have he (n:Eis) (z:ℂ) :
        z+3*eisEmbedding (GaussianShiftedPartition.representative q r+q*n)/eisEmbedding q=
          (z+3*eisEmbedding n)+b := by
      dsimp [b]
      simp only [map_add,map_mul]
      field_simp [eisEmbedding_ne_zero hq]
      ;ring
    simp_rw [he]
    rw [←lintegral_eq_period_lintegrals (fun z=>f (z+b))]
    exact lintegral_add_right_eq_self f b
  change (∑'n:Eis,I n)=_
  rw [←ENNReal.tsum_fiberwise I (Ideal.Quotient.mk (Ideal.span {q}))]
  simp only [hinner,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  congr 1
  change (Fintype.card (Eis⧸Ideal.span {q}):ℝ≥0∞)=(Nat.card (Eis⧸Ideal.span {q}):ℝ≥0∞)
  rw [Nat.card_eq_fintype_card]

lemma finite_index_period_integrals_summable (q:Eis) (hq:q≠0) (f:ℂ→ℂ) (hf:Integrable f) :
    Summable (fun n:Eis=>∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q)) := by
  apply Summable.of_enorm
  apply ne_of_lt
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n=>enorm_integral_le_lintegral_enorm _))
  rw [finite_index_period_lintegral q hq (fun z=>‖f z‖ₑ)]
  exact ENNReal.mul_lt_top (by simp) hf.hasFiniteIntegral

theorem finite_index_period_unfold (q:Eis) (hq:q≠0) (f:ℂ→ℂ) (hf:Integrable f) :
    (∑'n:Eis,∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*(∫z:ℂ,f z) :=
  finite_index_period_unfold_of_summable q hq f hf
    (finite_index_period_integrals_summable q hq f hf)

end CubicEisenstein

end

end OAI
end OAIOriginalModule0289

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.AffineCuspFourier
Source SHA256: bbe6759e7f6e760210cb5ee7fb868cc41c0aebb4ec7156cfd6dd0a94ca08cb79
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0290


namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma affineLowerTerm_eq_shifted (q r:Eis) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ)
    (a d:Eis) (ha:a≠0) (hq:q≠0) :
    affineLowerTerm q r z v s a d=
      (eisEmbedding (symbol r d)*eisEmbedding (symbol d a)*
        ((‖eisEmbedding (q*a)‖^2:ℝ):ℂ)^(-s))*
          shiftedHeightKernel v s (eisEmbedding d/eisEmbedding (q*a)) z := by
  rw [affineLowerTerm,rowHeight_eq_shiftedHeightKernel z v hv s (q*a) d (mul_ne_zero hq ha)]
  ring

lemma affineLowerTerm_integrable (q r:Eis) (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (a d:Eis) (ha:a≠0) (hq:q≠0) :
    Integrable (fun z=>affineLowerTerm q r z v s a d) := by
  simp_rw [affineLowerTerm_eq_shifted q r _ v hv s a d ha hq]
  exact (shiftedHeightKernel_integrable v hv s _ hs).const_mul _

lemma affineLowerTerm_fourier_integral (q r:Eis) (v:ℝ) (hv:0<v) (s freq:ℂ)
    (a d:Eis) (ha:a≠0) (hq:q≠0) :
    (∫z:ℂ,affineLowerTerm q r z v s a d*ShortDraftTrace.breveE (-freq*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (freq*v))*
        ((‖eisEmbedding (q*a)‖^2:ℝ):ℂ)^(-s)*
          ((eisEmbedding (symbol r d)*eisEmbedding (symbol d a))*
            ShortDraftTrace.breveE (freq*eisEmbedding d/eisEmbedding (q*a))) := by
  simp_rw [affineLowerTerm_eq_shifted q r _ v hv s a d ha hq,mul_assoc]
  rw [integral_const_mul,integral_const_mul,integral_const_mul,
    traceIntegral_shiftedHeightKernel v hv s (eisEmbedding d/eisEmbedding (q*a)) freq]
  ring_nf

lemma affineCuspGaussTerm_factor (h h1 q r a k x:Eis) (j n:ℕ)
    (ha:a≠0) (hprimary:lambda^2∣a-1) (hq:q≠0)
    (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hk:3*k=h1+ramifiedAffineParameter j n*a) :
    (eisEmbedding (symbol r (a+3*x))*eisEmbedding (symbol (a+3*x) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding (q*a))=
    (ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
      (eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a)))*
        (eisEmbedding (symbol x a)*residueAdditive (3*k) a x) := by
  have hs:symbol (a+3*x) a=symbol (3*x) a:=symbol_congr ⟨1,by ring⟩
  rw [ramified_symbol_primary_shift_signed j n r a x hr hprimary,hs,
    symbol_mul_numerator _ _ _ hprimary,map_mul eisEmbedding (symbol 3 a) (symbol x a)]
  have hp:=affineCusp_phase_identity h h1 q a k (ramifiedAffineParameter j n) x ha hq hh hk
  calc
    _ = (eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a)*eisEmbedding (symbol x a))*
      (ShortDraftTrace.breveE (eisEmbedding (ramifiedAffineParameter j n*x)/eisLam/3)*
        ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding (q*a))) := by ring
    _ = _ := by rw [hp];ring

lemma affineCuspTwistedCoefficient_add (h h1 q r a k x m:Eis) (j n:ℕ)
    (ha:a≠0) (hprimary:lambda^2∣a-1) (hq:q≠0)
    (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hk:3*k=h1+ramifiedAffineParameter j n*a) :
    (eisEmbedding (symbol r (a+3*(x+a*m)))*eisEmbedding (symbol (a+3*(x+a*m)) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*(x+a*m))/eisEmbedding (q*a))=
    (eisEmbedding (symbol r (a+3*x))*eisEmbedding (symbol (a+3*x) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding (q*a)) := by
  rw [affineCuspGaussTerm_factor h h1 q r a k (x+a*m) j n ha hprimary hq hr hh hk,
    affineCuspGaussTerm_factor h h1 q r a k x j n ha hprimary hq hr hh hk]
  rw [symbol_congr (show a∣x+a*m-x from ⟨m,by ring⟩),
    residueAdditive_three_congr k a (x+a*m) x ha ⟨m,by ring⟩]

lemma affineLowerTerm_weighted_translate (h h1 q r a k x m:Eis) (j n:ℕ)
    (ha:a≠0) (hprimary:lambda^2∣a-1) (hq:q≠0)
    (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hk:3*k=h1+ramifiedAffineParameter j n*a)
    (z:ℂ) (v:ℝ) (s:ℂ) :
    affineLowerTerm q r z v s a (a+3*(x+a*m))*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)=
      affineLowerTerm q r (z+3*eisEmbedding m/eisEmbedding q) v s a (a+3*x)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding m/eisEmbedding q)) := by
  let c1:=eisEmbedding (symbol r (a+3*(x+a*m)))*eisEmbedding (symbol (a+3*(x+a*m)) a)
  let c0:=eisEmbedding (symbol r (a+3*x))*eisEmbedding (symbol (a+3*x) a)
  let B:=ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding (q*a)
  let Q:=ninthCuspFrequency h*(3*eisEmbedding m/eisEmbedding q)
  have harg:ninthCuspFrequency h*eisEmbedding (a+3*(x+a*m))/eisEmbedding (q*a)=B+Q:=by
    dsimp [B,Q]
    simp only [map_add,map_mul,map_ofNat]
    field_simp [eisEmbedding_ne_zero hq,eisEmbedding_ne_zero ha]
    ;ring
  have hcoef:=affineCuspTwistedCoefficient_add h h1 q r a k x m j n ha hprimary hq hr hh hk
  change c1*ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*(x+a*m))/eisEmbedding (q*a))=
    c0*ShortDraftTrace.breveE B at hcoef
  rw [harg,AddChar.map_add_eq_mul] at hcoef
  have heB:ShortDraftTrace.breveE B≠0:=Complex.exp_ne_zero _
  have heQ:ShortDraftTrace.breveE Q≠0:=Complex.exp_ne_zero _
  have hmult:c1*ShortDraftTrace.breveE Q=c0:=by
    apply mul_right_cancel₀ heB
    calc
      _ = c1*(ShortDraftTrace.breveE B*ShortDraftTrace.breveE Q) := by ring
      _ = _ := hcoef
  have hsolve:c1=c0*ShortDraftTrace.breveE (-Q):=by
    rw [AddChar.map_neg_eq_inv]
    calc
      c1=c1*(ShortDraftTrace.breveE Q*(ShortDraftTrace.breveE Q)⁻¹) := by rw [mul_inv_cancel₀ heQ,mul_one]
      _ = (c1*ShortDraftTrace.breveE Q)*(ShortDraftTrace.breveE Q)⁻¹ := by ring
      _ = _ := by rw [hmult]
  have hrow:eisEmbedding (q*a)*z+eisEmbedding (a+3*(x+a*m))=
      eisEmbedding (q*a)*(z+3*eisEmbedding m/eisEmbedding q)+eisEmbedding (a+3*x):=by
    simp only [map_add,map_mul,map_ofNat]
    field_simp [eisEmbedding_ne_zero hq]
    ;ring
  change c1*((v/(‖eisEmbedding (q*a)*z+eisEmbedding (a+3*(x+a*m))‖^2+
    ‖eisEmbedding (q*a)‖^2*v^2):ℝ):ℂ)^s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)=_
  rw [hsolve,hrow]
  unfold affineLowerTerm
  have hphase:-ninthCuspFrequency h*(z+3*eisEmbedding m/eisEmbedding q)=(-Q)+(-ninthCuspFrequency h*z):=by
    dsimp [Q];ring
  rw [hphase,AddChar.map_add_eq_mul]
  dsimp only [c0]
  ring

lemma affineLowerIntegral_sum_translate (h h1 q r a k x:Eis) (j n:ℕ)
    (ha:a≠0) (hprimary:lambda^2∣a-1) (hq:q≠0)
    (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hk:3*k=h1+ramifiedAffineParameter j n*a)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re) :
    (∑'m:Eis,∫z in periodDomain,affineLowerTerm q r z v s a (a+3*(x+a*m))*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*
        ∫z:ℂ,affineLowerTerm q r z v s a (a+3*x)*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  have hint:=trace_mul_integrable (fun z=>affineLowerTerm q r z v s a (a+3*x))
    (affineLowerTerm_integrable q r v hv s hs a (a+3*x) ha hq) (ninthCuspFrequency h)
  rw [←finite_index_period_unfold q hq _ hint]
  apply tsum_congr
  intro m
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z=>affineLowerTerm_weighted_translate
    h h1 q r a k x m j n ha hprimary hq hr hh hk z v s)

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma affineDenominator_integral_formula (h h1 q r k:Eis) (j n:ℕ) (a:PrimaryLower)
    (hq:q≠0) (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hk:3*k=h1+ramifiedAffineParameter j n*a.val)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (hsum:Summable (fun d:PrimaryCoprimeDenominator a=>∫z in periodDomain,
      affineLowerTerm q r z v s a.val d.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))) :
    (∑'d:PrimaryCoprimeDenominator a,∫z in periodDomain,
      affineLowerTerm q r z v s a.val d.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*
        ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
          ((‖eisEmbedding (q*a.val)‖^2:ℝ):ℂ)^(-s)*ramifiedAffineGauss h q r a.val := by
  let e:=(cubicResidueElementEquiv a.val (primaryLower_ne_zero a)).trans (primaryDenominatorEquiv a)
  have hpair:=e.summable_iff.mpr hsum
  change Summable (fun p:CubicUnitResidue a.val×Eis=>∫z in periodDomain,
    affineLowerTerm q r z v s a.val (a.val+3*(GaussianShiftedPartition.representative a.val p.1.val+a.val*p.2))*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z)) at hpair
  rw [←e.tsum_eq]
  change (∑'p:CubicUnitResidue a.val×Eis,∫z in periodDomain,
    affineLowerTerm q r z v s a.val (a.val+3*(GaussianShiftedPartition.representative a.val p.1.val+a.val*p.2))*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=_
  rw [hpair.tsum_prod]
  have hinner (x:CubicUnitResidue a.val) :
      (∑'m:Eis,∫z in periodDomain,
        affineLowerTerm q r z v s a.val (a.val+3*(GaussianShiftedPartition.representative a.val x.val+a.val*m))*
          ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*
        (((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
          ((‖eisEmbedding (q*a.val)‖^2:ℝ):ℂ)^(-s)*
            ((eisEmbedding (symbol r (a.val+3*GaussianShiftedPartition.representative a.val x.val))*
              eisEmbedding (symbol (a.val+3*GaussianShiftedPartition.representative a.val x.val) a.val))*
                ShortDraftTrace.breveE (ninthCuspFrequency h*
                  eisEmbedding (a.val+3*GaussianShiftedPartition.representative a.val x.val)/eisEmbedding (q*a.val)))) := by
    rw [affineLowerIntegral_sum_translate h h1 q r a.val k _ j n (primaryLower_ne_zero a)
      (primaryLower_primary a) hq hr hh hk v hv s hs,
      affineLowerTerm_fourier_integral q r v hv s _ a.val _ (primaryLower_ne_zero a) hq]
  simp_rw [hinner]
  unfold ramifiedAffineGauss
  simp_rw [mul_assoc]
  rw [tsum_mul_left,tsum_mul_left,tsum_mul_left,tsum_mul_left]

lemma affineCuspFrequency_lift (h1:Eis) (j n:ℕ) (a:PrimaryLower)
    (hfreq:(3:Eis)∣h1+ramifiedAffineParameter j n) :
    ∃k:Eis,3*k=h1+ramifiedAffineParameter j n*a.val := by
  have hh:=dvd_add hfreq (a.2.mul_left (ramifiedAffineParameter j n))
  have hd:(3:Eis)∣h1+ramifiedAffineParameter j n*a.val:=by
    convert hh using 1 ;ring
  obtain ⟨k,hk⟩:=hd
  exact ⟨k,hk.symm⟩

lemma affineCusp_norm_factor (q:Eis) (s:ℂ) (a:PrimaryLower) :
    ((‖eisEmbedding (q*a.val)‖^2:ℝ):ℂ)^(-s)=
      ((‖eisEmbedding q‖^2:ℝ):ℂ)^(-s)*((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s) := by
  rw [map_mul,norm_mul,mul_pow,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (sq_nonneg _) (sq_nonneg _)]

theorem affineCusp_branch_fourier (h h1 q r:Eis) (j n:ℕ)
    (hq:q≠0) (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hfreq:(3:Eis)∣h1+ramifiedAffineParameter j n)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (hsum:Summable (fun p:UnitLowerData=>∫z in periodDomain,
      affineLowerTerm q r z v s p.1.val p.2.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))) :
    (∑'p:UnitLowerData,∫z in periodDomain,
      affineLowerTerm q r z v s p.1.val p.2.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*((‖eisEmbedding q‖^2:ℝ):ℂ)^(-s)*
        ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
          ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
            unramifiedCubicGaussSeries s (3*r^2*h1) := by
  rw [hsum.tsum_sigma]
  have ha (a:PrimaryLower):
      (∑'d:PrimaryCoprimeDenominator a,∫z in periodDomain,
        affineLowerTerm q r z v s a.val d.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ((Ideal.absNorm (Ideal.span {q}):ℂ)*((‖eisEmbedding q‖^2:ℝ):ℂ)^(-s)*
        ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
          ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q))*
        (((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s)*cubicUnitGaussSum (3*r^2*h1) a.val) := by
    obtain ⟨k,hk⟩:=affineCuspFrequency_lift h1 j n a hfreq
    rw [affineDenominator_integral_formula h h1 q r k j n a hq hr hh hk v hv s hs
      (hsum.sigma_factor a),ramifiedAffineGauss_eq_unramified h h1 q r a.val k j n
        (primaryLower_ne_zero a) (primaryLower_primary a) hq hr hh hk,
      affineCusp_norm_factor]
    ring
  simp_rw [ha]
  rw [tsum_mul_left]
  congr 1
  rw [←primaryLowerIdealEquiv.symm.tsum_eq,unramifiedCubicGaussSeries]
  apply tsum_congr
  intro I
  change ((‖eisEmbedding (CompletedGauss.primaryGenerator I.val)‖^2:ℝ):ℂ)^(-s)*
    cubicUnitGaussSum (3*r^2*h1) (CompletedGauss.primaryGenerator I.val)=_
  rw [eisEmbedding_norm_sq_eq_absNorm_span,(CompletedGauss.primaryGenerator_spec I.val I.2).1,
    Complex.ofReal_natCast]

end

section
open MeasureTheory Filter
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma hasSum_diagonal_unit_integrals (u t:Eisˣ) (v:ℝ) (hv:0<v) (s freq:ℂ) (hs:2<s.re) :
    HasSum (fun p:UnitLowerData=>∫z in periodDomain,
      affineLowerTerm (t:Eis) ((↑u⁻¹:Eis)^2*(t:Eis)) z v s p.1.val p.2.val.val*
        ShortDraftTrace.breveE (-freq*z))
      (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
        integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s*
          ShortDraftTrace.breveE (-freq*z)) := by
  have hh:=(diagonalUnitCuspIndex u t).hasSum_iff.mpr
    (hasSum_integral_fixed_left_Eisenstein
      (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (t:Eis)))
      v hv s freq hs)
  apply hh.congr_fun
  intro p
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z=>by dsimp only; rw [diagonal_unit_summand])

theorem diagonal_unit_eisenstein_fourier (u t:Eisˣ) (j:ℕ) (h h1:Eis)
    (hr:(↑u⁻¹:Eis)^2*(t:Eis)=omega^j ∨ (↑u⁻¹:Eis)^2*(t:Eis)=-(omega^j))
    (hh:h=(t:Eis)*h1) (hfreq:(3:Eis)∣h1+ramifiedAffineParameter j 0)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) :
    (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (t:Eis))*
          unramifiedCubicGaussSeries s (3*((↑u⁻¹:Eis)^2*(t:Eis))^2*h1) := by
  have hsum:=hasSum_diagonal_unit_integrals u t v hv s (ninthCuspFrequency h) hs
  rw [←hsum.tsum_eq]
  have h:=affineCusp_branch_fourier h h1 (t:Eis) ((↑u⁻¹:Eis)^2*(t:Eis)) j 0 t.ne_zero
    (by simpa using hr) hh hfreq v hv s (by linarith) hsum.summable
  simpa only [GaussGeneratorTransport.norm_eisEmbedding_unit,one_pow,Complex.ofReal_one,
    Complex.one_cpow,Ideal.span_singleton_eq_top.mpr t.isUnit,Ideal.absNorm_top,map_one,Nat.cast_one,one_mul] using h

lemma onceCusp_q_norm (t:Eisˣ) (j:Fin 3) :
    ‖eisEmbedding (onceCuspScale t*omega^j.val)‖^2=3 := by
  have hw:‖eisEmbedding omega‖=1:=by
    let w:Eisˣ:=(omega_primitive.isUnit (by decide)).unit
    have hw:(w:Eis)=omega:=(omega_primitive.isUnit (by decide)).unit_spec
    rw [←hw]
    exact GaussGeneratorTransport.norm_eisEmbedding_unit w
  simp only [onceCuspScale,map_mul,norm_mul,GaussGeneratorTransport.norm_eisEmbedding_unit,
    one_mul,map_pow,norm_pow,hw,one_pow,mul_one,ramifiedEmbedding_traceLambda]
  rw [←ramifiedEmbedding_traceLambda,←norm_pow,←map_pow,ramifiedTraceLambda_square]
  norm_num [map_ofNat]

lemma onceCusp_q_absNorm (t:Eisˣ) (j:Fin 3) :
    Ideal.absNorm (Ideal.span {onceCuspScale t*omega^j.val})=3 := by
  have h:=onceCusp_q_norm t j
  rw [eisEmbedding_norm_sq_eq_absNorm_span] at h
  exact_mod_cast h

theorem diagonal_once_branch_fourier (u t:Eisˣ) (l:Fin 3) (j:ℕ) (h h1:Eis)
    (hr:(↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)=omega^j*ramifiedTraceLambda ∨
      (↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)=-(omega^j*ramifiedTraceLambda))
    (hh:h=(onceCuspScale t*omega^l.val)*h1) (hfreq:(3:Eis)∣h1+ramifiedAffineParameter j 1)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) :
    (∑'p:UnitLowerData,∫z in periodDomain,
      affineLowerTerm (onceCuspScale t*omega^l.val)
        ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)) z v s p.1.val p.2.val.val*
          ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      (3:ℂ)*(3:ℂ)^(-s)*((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (onceCuspScale t*omega^l.val))*
          unramifiedCubicGaussSeries s
            (3*((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val))^2*h1) := by
  have hsum:=(hasSum_diagonal_once_integrals u t v hv s (ninthCuspFrequency h) hs).summable.prod_factor l
  have hq:onceCuspScale t*omega^l.val≠0:=mul_ne_zero (onceCusp_scale_ne_zero t)
    (pow_ne_zero _ (omega_primitive.isUnit (by decide)).ne_zero)
  have h:=affineCusp_branch_fourier h h1 (onceCuspScale t*omega^l.val)
    ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)) j 1 hq (by simpa only [pow_one] using hr)
      hh hfreq v hv s (by linarith) hsum
  simpa only [onceCusp_q_norm,onceCusp_q_absNorm,Nat.cast_ofNat,Complex.ofReal_ofNat] using h

end

section
open MeasureTheory Filter
open scoped BigOperators Classical ENNReal

open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem quotient_weighted_period_unfold (q:Eis) (hq:q≠0)
    (ψ:(Eis⧸Ideal.span {q})→ℂ) (f:ℂ→ℂ) (hf:Integrable f) :
    (∑'n:Eis,ψ (Ideal.Quotient.mk (Ideal.span {q}) n)*
      ∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q))=
      (∑'r:Eis⧸Ideal.span {q},ψ r)*(∫z:ℂ,f z) := by
  let : Finite (Eis⧸Ideal.span {q}):=finite_quotient_span hq
  let : Fintype (Eis⧸Ideal.span {q}):=Fintype.ofFinite _
  let I:Eis→ℂ:=fun n=>∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q)
  have hs:Summable (fun n:Eis=>ψ (Ideal.Quotient.mk (Ideal.span {q}) n)*I n):=by
    apply (((finite_index_period_integrals_summable q hq f hf).norm).mul_left ‖ψ‖).of_norm_bounded
    intro n
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_le_pi_norm ψ _) (norm_nonneg _)
  have hinner (r:Eis⧸Ideal.span {q}):
      (∑'n:((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}),
        ψ (Ideal.Quotient.mk (Ideal.span {q}) n.val)*I n.val)=ψ r*(∫z:ℂ,f z) := by
    have heval (n:((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r})):
        Ideal.Quotient.mk (Ideal.span {q}) n.val=r:=n.2
    simp_rw [heval]
    rw [tsum_mul_left,GaussianFiberEquiv.fiber_tsum q hq r (GaussianShiftedPartition.representative q r)
      (GaussianShiftedPartition.representative_spec q r)]
    congr 1
    let b:=3*eisEmbedding (GaussianShiftedPartition.representative q r)/eisEmbedding q
    have he (n:Eis) (z:ℂ):
        z+3*eisEmbedding (GaussianShiftedPartition.representative q r+q*n)/eisEmbedding q=
          (z+3*eisEmbedding n)+b:=by
      dsimp [b]
      simp only [map_add,map_mul]
      field_simp [eisEmbedding_ne_zero hq]
      ;ring
    change (∑'n:Eis,∫z in periodDomain,f (z+3*eisEmbedding
      (GaussianShiftedPartition.representative q r+q*n)/eisEmbedding q))=_
    simp_rw [he]
    rw [←integral_eq_period_integrals (fun z=>f (z+b)) (hf.comp_add_right b)]
    exact integral_add_right_eq_self f b
  rw [←(hs.hasSum.tsum_fiberwise (Ideal.Quotient.mk (Ideal.span {q})) ).tsum_eq]
  change (∑'r:Eis⧸Ideal.span {q},∑'n:((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}),
    ψ (Ideal.Quotient.mk (Ideal.span {q}) n.val)*I n.val)=_
  simp_rw [hinner]
  exact tsum_mul_right

theorem character_weighted_period_unfold (q:Eis) (hq:q≠0)
    (ψ:AddChar (Eis⧸Ideal.span {q}) ℂ) (f:ℂ→ℂ) (hf:Integrable f) :
    (∑'n:Eis,ψ (Ideal.Quotient.mk (Ideal.span {q}) n)*
      ∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q))=
      if ψ=1 then (Ideal.absNorm (Ideal.span {q}):ℂ)*(∫z:ℂ,f z) else 0 := by
  let : Finite (Eis⧸Ideal.span {q}):=finite_quotient_span hq
  let : Fintype (Eis⧸Ideal.span {q}):=Fintype.ofFinite _
  rw [quotient_weighted_period_unfold q hq ψ f hf,tsum_fintype]
  split_ifs with hψ
  · rw [AddChar.sum_eq_card_of_eq_one hψ]
    congr 1
    change (Fintype.card (Eis⧸Ideal.span {q}):ℂ)=(Nat.card (Eis⧸Ideal.span {q}):ℂ)
    rw [Nat.card_eq_fintype_card]
  · rw [AddChar.sum_eq_zero_of_ne_one hψ,zero_mul]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

def affinePeriodChar (q:Eis) (hq:q≠0) (ell:Eis) : AddChar (Eis⧸Ideal.span {q}) ℂ :=
  (eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates q hq).mulShift
    (Ideal.Quotient.mk (Ideal.span {q}) ell)

lemma affinePeriodChar_mk (q:Eis) (hq:q≠0) (ell x:Eis) :
    affinePeriodChar q hq ell (Ideal.Quotient.mk (Ideal.span {q}) x)=
      ShortDraftTrace.breveE (eisEmbedding (ell*x)/(eisEmbedding q*eisLam)) := by
  simp only [affinePeriodChar,AddChar.mulShift_apply,←map_mul,eisTraceModChar,
    IdealGaussCRT.traceModChar_mk]

lemma affinePeriodChar_eq_one (q:Eis) (hq:q≠0) (ell:Eis) :
    affinePeriodChar q hq ell=1 ↔ q∣ell := by
  constructor
  · intro h
    by_contra hd
    have hz:Ideal.Quotient.mk (Ideal.span {q}) ell≠0:=by
      intro he
      exact hd (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp he))
    exact GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive q hq hz h
  · intro hd
    have hz:Ideal.Quotient.mk (Ideal.span {q}) ell=0:=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hd)
    simp [affinePeriodChar,hz]

lemma affineCusp_general_weighted_translate (h q r a ell x m:Eis) (j n:ℕ)
    (hprimary:lambda^2∣a-1) (hq:q≠0)
    (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hell:3*ell=h+ramifiedAffineParameter j n*q*a)
    (z:ℂ) (v:ℝ) (s:ℂ) :
    affineLowerTerm q r z v s a (a+3*(x+a*m))*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)=
      affinePeriodChar q hq ell (Ideal.Quotient.mk (Ideal.span {q}) m)*
        (affineLowerTerm q r (z+3*eisEmbedding m/eisEmbedding q) v s a (a+3*x)*
          ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding m/eisEmbedding q))) := by
  let A:=eisEmbedding (ramifiedAffineParameter j n*(a*m))/eisLam/3
  let delta:=3*eisEmbedding m/eisEmbedding q
  have hchar:eisEmbedding (symbol r (a+3*(x+a*m)))=
      eisEmbedding (symbol r (a+3*x))*ShortDraftTrace.breveE A:=by
    have hd:lambda^2∣a+3*x-1:=primary_add_three a x hprimary
    have h:=ramified_symbol_primary_shift_signed j n r (a+3*x) (a*m) hr hd
    convert h using 1 ; congr 2 ;ring
  have hden:symbol (a+3*(x+a*m)) a=symbol (a+3*x) a:=
    symbol_congr ⟨3*m,by ring⟩
  have hrow:eisEmbedding (q*a)*z+eisEmbedding (a+3*(x+a*m))=
      eisEmbedding (q*a)*(z+delta)+eisEmbedding (a+3*x):=by
    dsimp [delta]
    simp only [map_add,map_mul,map_ofNat]
    field_simp [eisEmbedding_ne_zero hq]
    ;ring
  have hell':eisEmbedding ell=(eisEmbedding h+eisEmbedding (ramifiedAffineParameter j n)*eisEmbedding q*eisEmbedding a)/3:=by
    apply (eq_div_iff (by norm_num : (3:ℂ)≠0)).mpr
    have he:=congrArg eisEmbedding hell
    simp only [map_mul,map_add,map_ofNat] at he
    linear_combination he
  have harg:A+ninthCuspFrequency h*delta=eisEmbedding (ell*m)/(eisEmbedding q*eisLam):=by
    dsimp [A,delta,ninthCuspFrequency,cuspFrequency]
    simp only [map_mul]
    rw [hell']
    field_simp [eisEmbedding_ne_zero hq,eisLam_ne_zero]
    ;ring
  have hphase:ShortDraftTrace.breveE A*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)=
      affinePeriodChar q hq ell (Ideal.Quotient.mk (Ideal.span {q}) m)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+delta)):=by
    rw [affinePeriodChar_mk,←harg,←AddChar.map_add_eq_mul,←AddChar.map_add_eq_mul]
    congr 1
    ring
  unfold affineLowerTerm
  rw [hchar,hden,hrow]
  change _=affinePeriodChar q hq ell (Ideal.Quotient.mk (Ideal.span {q}) m)*
    ((eisEmbedding (symbol r (a+3*x))*eisEmbedding (symbol (a+3*x) a))*
      ((v/(‖eisEmbedding (q*a)*(z+delta)+eisEmbedding (a+3*x)‖^2+
        ‖eisEmbedding (q*a)‖^2*v^2):ℝ):ℂ)^s*
          ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+delta)))
  calc
    _ = ((eisEmbedding (symbol r (a+3*x))*eisEmbedding (symbol (a+3*x) a))*
      ((v/(‖eisEmbedding (q*a)*(z+delta)+eisEmbedding (a+3*x)‖^2+
        ‖eisEmbedding (q*a)‖^2*v^2):ℝ):ℂ)^s)*
        (ShortDraftTrace.breveE A*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)) := by ring
    _ = _ := by rw [hphase];ring

lemma affineCusp_masked_inner (h q r a ell x:Eis) (j n:ℕ)
    (ha:a≠0) (hprimary:lambda^2∣a-1) (hq:q≠0)
    (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hell:3*ell=h+ramifiedAffineParameter j n*q*a)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re) :
    (∑'m:Eis,∫z in periodDomain,affineLowerTerm q r z v s a (a+3*(x+a*m))*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      if q∣ell then (Ideal.absNorm (Ideal.span {q}):ℂ)*
        (∫z:ℂ,affineLowerTerm q r z v s a (a+3*x)*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)) else 0 := by
  have hint:=trace_mul_integrable (fun z=>affineLowerTerm q r z v s a (a+3*x))
    (affineLowerTerm_integrable q r v hv s hs a (a+3*x) ha hq) (ninthCuspFrequency h)
  simp_rw [affineCusp_general_weighted_translate h q r a ell x _ j n hprimary hq hr hell,
    integral_const_mul]
  rw [character_weighted_period_unfold q hq (affinePeriodChar q hq ell) _ hint]
  simp only [affinePeriodChar_eq_one]

end

open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma affineDenominator_zero (h h1 q r:Eis) (j n:ℕ) (a:PrimaryLower)
    (hq:q≠0) (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hbase:(3:Eis)∣h+ramifiedAffineParameter j n*q)
    (hfreq:¬(3:Eis)∣h1+ramifiedAffineParameter j n)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (hsum:Summable (fun d:PrimaryCoprimeDenominator a=>∫z in periodDomain,
      affineLowerTerm q r z v s a.val d.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))) :
    (∑'d:PrimaryCoprimeDenominator a,∫z in periodDomain,
      affineLowerTerm q r z v s a.val d.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=0 := by
  have hdiv:(3:Eis)∣h+ramifiedAffineParameter j n*q*a.val:=by
    have ht:=dvd_add hbase (a.2.mul_left (ramifiedAffineParameter j n*q))
    convert ht using 1 ;ring
  obtain ⟨ell,hell⟩:=hdiv
  have hell':3*ell=h+ramifiedAffineParameter j n*q*a.val:=hell.symm
  have hne:¬q∣ell:=by
    rintro ⟨b,hb⟩
    have he:q*(3*b)=q*(h1+ramifiedAffineParameter j n*a.val):=by
      rw [hb,hh] at hell'
      linear_combination hell'
    have hc:=mul_left_cancel₀ hq he
    have ht:(3:Eis)∣h1+ramifiedAffineParameter j n*a.val:=⟨b,hc.symm⟩
    apply hfreq
    have hh:=dvd_sub ht (a.2.mul_left (ramifiedAffineParameter j n))
    convert hh using 1 ;ring
  let e:=(cubicResidueElementEquiv a.val (primaryLower_ne_zero a)).trans (primaryDenominatorEquiv a)
  have hpair:=e.summable_iff.mpr hsum
  change Summable (fun p:CubicUnitResidue a.val×Eis=>∫z in periodDomain,
    affineLowerTerm q r z v s a.val (a.val+3*(GaussianShiftedPartition.representative a.val p.1.val+a.val*p.2))*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z)) at hpair
