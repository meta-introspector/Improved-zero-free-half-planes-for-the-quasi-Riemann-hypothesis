    exact P.mul_mem_left _ hm
  have hx:m^6*f^4*z∈P:=P.mul_mem_right _ (P.mul_mem_right _ hm6)
  change Ψ n*idealRowHom _ (Ideal.span {n})=0
  rw [idealRowHom_zero_of_dvd _ hp hPI hx,mul_zero]

theorem rowTwist_unitSupplement (Ψ : ActualEisensteinCubic.O→*ℂ) (m f z : ActualEisensteinCubic.O) (u : ActualEisensteinCubic.Oˣ)
    (hmLam : lambda∣m) (hm2 : (2:ActualEisensteinCubic.O)∣m) :
    rowTwist Ψ m f (u.val*z)=unitSupplement u*rowTwist Ψ m f z := by
  ext n
  by_cases hn:Supported (Ideal.span {n})
  · change Ψ n*idealRowHom (m^6*f^4*(u.val*z)) (Ideal.span {n})=
      (if Supported (Ideal.span {n}) then _ else 0)*(Ψ n*idealRowHom _ (Ideal.span {n}))
    rw [ite_eq_left hn,show m^6*f^4*(u.val*z)=u.val*(m^6*f^4*z) by ring,idealRowHom_argument_mul]
    ring
  · have hz:rowTwist Ψ m f (u.val*z) n=0 := by
      have hbad : lambda∣n ∨ (2:ActualEisensteinCubic.O)∣n := by
        simpa only [supported_span_iff,not_and_or,not_not] using hn
      rcases hbad with hLam|h2
      · exact rowTwist_zero_of_common_prime Ψ m f _ n (Ideal.span {lambda})
          (Ideal.prime_of_isPrime (by
            rw [ne_eq,Ideal.span_singleton_eq_bot]
            exact PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero) lambdaIdeal_maximal.isPrime)
          (Ideal.mem_span_singleton.mpr hmLam) (Ideal.mem_span_singleton.mpr hLam)
      · exact rowTwist_zero_of_common_prime Ψ m f _ n (Ideal.span {(2:ActualEisensteinCubic.O)})
          (Ideal.prime_of_isPrime (by
            rw [ne_eq,Ideal.span_singleton_eq_bot]
            norm_num) twoIdeal_maximal.isPrime)
          (Ideal.mem_span_singleton.mpr hm2) (Ideal.mem_span_singleton.mpr h2)
    change rowTwist Ψ m f (u.val*z) n=(if Supported (Ideal.span {n}) then _ else 0)*_
    rw [hz,ite_eq_right hn,zero_mul]

theorem rowTwist_unitSupplement_base (Ψ : ActualEisensteinCubic.O→*ℂ) (m f z : ActualEisensteinCubic.O) (u : ActualEisensteinCubic.Oˣ)
    (hmLam : lambda∣m) (hm2 : (2:ActualEisensteinCubic.O)∣m) :
    rowTwist Ψ m f (u.val*z)=rowTwist (unitSupplement u*Ψ) m f z := by
  rw [rowTwist_unitSupplement Ψ m f z u hmLam hm2]
  ext n
  change unitSupplement u n*(Ψ n*idealRowHom _ _)=(unitSupplement u n*Ψ n)*idealRowHom _ _
  ring

theorem unitRowFamily_transport (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (u : ActualEisensteinCubic.Oˣ) {F : ℝ}
    (f : idealRange F) (I : Ideal ActualEisensteinCubic.O) (hmLam : lambda∣m) (hm2 : (2:ActualEisensteinCubic.O)∣m) :
    CompletedUnitRows.unitRowFamily Ψ m u f I=
      CompletedUnitRows.unitRowFamily (unitSupplement u*Ψ) m 1 f I := by
  simp only [CompletedUnitRows.unitRowFamily,Units.val_one,one_mul]
  exact rowTwist_unitSupplement_base Ψ m (ConcretePrimeRowBridge.idealGenerator f.val)
    (ConcretePrimeRowBridge.idealGenerator I) u hmLam hm2

theorem unitSupplement_mul_periodic (u : ActualEisensteinCubic.Oˣ) (Ψ : ActualEisensteinCubic.O→*ℂ) (Q : Ideal ActualEisensteinCubic.O)
    (hΨ : ∀x y : ActualEisensteinCubic.O,x-y∈Q→Ψ x=Ψ y) (x y : ActualEisensteinCubic.O)
    (hxy : x-y∈Q*Ideal.span {(36:ActualEisensteinCubic.O)}) :
    (unitSupplement u*Ψ) x=(unitSupplement u*Ψ) y := by
  simp only [MonoidHom.mul_apply]
  rw [unitSupplement_periodic u x y (Ideal.mul_le_right hxy),hΨ x y (Ideal.mul_le_left hxy)]

end CanonicalUnitEuler

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold MatrixGroups

lemma kernelBarrier_sublevel_isCompact (T : ℝ) :
    IsCompact {q : KernelQuotient | kernelQuotientBarrier 2 3 q≤T} := by
  obtain ⟨S,hS⟩ := globalKubotaKernel_compact_core_cusp_cover
  obtain ⟨hcompact,hcover⟩ := hS (max 3 T)
  apply hcompact.of_isClosed_subset
    (isClosed_le (kernelQuotientBarrier_continuous 2 3 (by norm_num) (by norm_num)) continuous_const)
  intro q hq
  have hmem : q∈compactFordCore globalKubotaKernel S (max 3 T) ∪
      ⋃r∈S,fordCuspTail globalKubotaKernel r (max 3 T) := by rw [←hcover]; trivial
  rcases hmem with hcore | htail
  · exact hcore
  · exfalso
    obtain ⟨r,hr⟩ := Set.mem_iUnion.mp htail
    obtain ⟨hrS,htail⟩ := Set.mem_iUnion.mp hr
    obtain ⟨p,hp,rfl⟩ := htail
    have hh : 3<p.1.2 := (le_max_left 3 T).trans_lt hp.2.2
    change kernelQuotientBarrier 2 3 (fordOrbitChart globalKubotaKernel r p)≤T at hq
    rw [kernelQuotientBarrier_fordCusp 2 3 (by norm_num) (by norm_num) r p hh] at hq
    exact (not_lt_of_ge hq) ((le_max_right 3 T).trans_lt hp.2.2)

def kernelExhaustionProfile (n : ℕ) (v : ℝ) : ℝ :=
  1-cuspTransition 1 2 (v/((n:ℝ)+1))

def kernelExhaustionCutoff (n : ℕ) (q : KernelQuotient) : ℝ :=
  kernelExhaustionProfile n (kernelQuotientBarrier 2 3 q)

lemma kernelExhaustionProfile_smooth (n : ℕ) :
    ContDiff ℝ ∞ (kernelExhaustionProfile n) := by
  unfold kernelExhaustionProfile cuspTransition
  fun_prop

lemma kernelExhaustionCutoff_smooth (n : ℕ) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ (kernelExhaustionCutoff n) :=
  (kernelExhaustionProfile_smooth n).contMDiff.comp
    (kernelQuotientBarrier_contMDiff 2 3 (by norm_num) (by norm_num))

lemma kernelExhaustionProfile_bounds (n : ℕ) (v : ℝ) :
    0≤kernelExhaustionProfile n v ∧ kernelExhaustionProfile n v≤1 := by
  have h0 := Real.smoothTransition.nonneg ((v/((n:ℝ)+1)-1)/(2-1))
  have h1 := Real.smoothTransition.le_one ((v/((n:ℝ)+1)-1)/(2-1))
  change 0≤1-Real.smoothTransition _ ∧ 1-Real.smoothTransition _≤1
  constructor <;> linarith

lemma kernelExhaustionProfile_one (n : ℕ) (v : ℝ) (hv : v≤(n:ℝ)+1) :
    kernelExhaustionProfile n v=1 := by
  rw [kernelExhaustionProfile,cuspTransition_zero 1 2 _ (by norm_num)
    ((div_le_one (by positivity)).mpr hv),sub_zero]

lemma kernelExhaustionProfile_zero (n : ℕ) (v : ℝ) (hv : 2*((n:ℝ)+1)≤v) :
    kernelExhaustionProfile n v=0 := by
  rw [kernelExhaustionProfile,cuspTransition_one 1 2 _ (by norm_num)
    ((le_div_iff₀ (by positivity)).mpr hv),sub_self]

lemma kernelExhaustionCutoff_hasCompactSupport (n : ℕ) :
    HasCompactSupport (kernelExhaustionCutoff n) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (kernelBarrier_sublevel_isCompact (2*((n:ℝ)+1)))
  intro q hq
  change kernelQuotientBarrier 2 3 q≤2*((n:ℝ)+1)
  by_contra h
  exact hq (kernelExhaustionProfile_zero n _ (le_of_not_ge h))

lemma kernelExhaustionCutoff_bounds (n : ℕ) (q : KernelQuotient) :
    0≤kernelExhaustionCutoff n q ∧ kernelExhaustionCutoff n q≤1 :=
  kernelExhaustionProfile_bounds n _

lemma kernelExhaustionCutoff_eventually_one (q : KernelQuotient) :
    ∀ᶠn : ℕ in atTop,kernelExhaustionCutoff n q=1 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (kernelQuotientBarrier 2 3 q)
  filter_upwards [eventually_ge_atTop N] with n hn
  apply kernelExhaustionProfile_one
  have hh : (N:ℝ)≤n := by exact_mod_cast hn
  linarith

lemma kernelExhaustionCutoff_eventually_one_near (q : KernelQuotient) :
    ∀ᶠn : ℕ in atTop,kernelExhaustionCutoff n =ᶠ[𝓝 q] (fun _ => 1) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (kernelQuotientBarrier 2 3 q)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hh : kernelQuotientBarrier 2 3 q<(n:ℝ)+1 := by
    have hcast : (N:ℝ)≤n := by exact_mod_cast hn
    linarith
  filter_upwards [(kernelQuotientBarrier_continuous 2 3 (by norm_num) (by norm_num)).continuousAt.eventually_lt_const hh]
    with p hp
  exact kernelExhaustionProfile_one n _ hp.le

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

lemma cuspTransition_euler_bounded (a b : ℝ) (hab : a<b) :
    ∃C : ℝ,0≤C ∧ ∀v,|v*deriv (cuspTransition a b) v|≤C := by
  have hc : HasCompactSupport (fun v => v*deriv (cuspTransition a b) v) := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    intro v hv
    by_contra hnot
    have hout : v<a ∨ b<v := by simpa only [Set.mem_Icc,not_and_or,not_le] using hnot
    exact hv (by change v*deriv (cuspTransition a b) v=0; rw [(cuspTransition_derivatives a b v hab hout).1,mul_zero])
  have hcont : Continuous (fun v => v*deriv (cuspTransition a b) v) :=
    continuous_id.mul ((contDiff_infty_iff_deriv.mp (cuspTransition_contDiff a b)).2.continuous)
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hcont
  exact ⟨max C 0,le_max_right _ _,fun v => (hC v).trans (le_max_left _ _)⟩

lemma cuspRemainderProfile_contDiffAt (a b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) :
    ContDiffAt ℝ ∞ (cuspRemainderProfile a b s) v :=
  (positiveHeightPower_contDiffAt s v hv.ne').sub (cuspSeedProfile_contDiffAt a b s v hv)

lemma cuspRemainderProfile_euler (a b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) :
    (v:ℂ)*deriv (cuspRemainderProfile a b s) v=
      positiveHeightPower s v *
        (((1-cuspTransition a b v:ℝ):ℂ)*s-((v*deriv (cuspTransition a b) v:ℝ):ℂ)) := by
  have h := (positiveHeightPower_hasDerivAt s v hv.ne').sub
    (cuspSeedProfile_hasDerivAt a b s v hv.ne')
  change HasDerivAt (cuspRemainderProfile a b s) _ v at h
  rw [h.deriv]
  simp only [Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_mul]
  field_simp [Complex.ofReal_ne_zero.mpr hv.ne']
  ; ring

lemma cuspRemainderProfile_euler_bound (a b : ℝ) (s : ℂ) (C : ℝ)
    (hC : ∀v,|v*deriv (cuspTransition a b) v|≤C) (v : ℝ) (hv : 0<v) :
    ‖(v:ℂ)*deriv (cuspRemainderProfile a b s) v‖≤(‖s‖+C)*v^s.re := by
  rw [cuspRemainderProfile_euler a b s v hv,norm_mul,
    positiveHeightPower_eq_cpow s v hv,Complex.norm_cpow_eq_rpow_re_of_pos hv]
  have hχ0 : 0≤1-cuspTransition a b v := sub_nonneg.mpr (Real.smoothTransition.le_one _)
  have hχ1 : 1-cuspTransition a b v≤1 := by
    have h := Real.smoothTransition.nonneg ((v-a)/(b-a))
    change 0≤cuspTransition a b v at h
    linarith
  have hfactor : ‖((1-cuspTransition a b v:ℝ):ℂ)*s-
      ((v*deriv (cuspTransition a b) v:ℝ):ℂ)‖≤‖s‖+C := by
    apply (norm_sub_le _ _).trans
    rw [norm_mul,Complex.norm_of_nonneg hχ0,Complex.norm_real,Real.norm_eq_abs]
    have hm := mul_le_mul_of_nonneg_right hχ1 (norm_nonneg s)
    linarith [hC v]
  have hh := mul_le_mul_of_nonneg_left hfactor (Real.rpow_nonneg hv.le s.re)
  simpa only [mul_comm (v^s.re)] using hh

lemma cuspRemainderProfile_deriv_zero (a b : ℝ) (s : ℂ) (v : ℝ)
    (hab : a<b) (hv : 0<v) (hbv : b<v) : deriv (cuspRemainderProfile a b s) v=0 := by
  have he : cuspRemainderProfile a b s =ᶠ[𝓝 v] (fun _ => 0) := by
    filter_upwards [Ioi_mem_nhds hv,Ioi_mem_nhds hbv] with y hy hyb
    exact cuspRemainderProfile_zero a b s y hab hy hyb.le
  exact he.deriv_eq.trans (deriv_const v 0)

lemma rowLogD_hyperbolic_bound (u : Fin 2→ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) : |p 2*rowLogD u p j|≤1 := by
  have he := rowLog_eikonal u hu p hp
  have hsq : (p 2*rowLogD u p j)^2≤1 := by
    fin_cases j
    · change (p 2*rowLogD u p 0)^2≤1
      nlinarith [sq_nonneg (p 2*rowLogD u p 1),sq_nonneg (p 2*rowLogD u p 2)]
    · change (p 2*rowLogD u p 1)^2≤1
      nlinarith [sq_nonneg (p 2*rowLogD u p 0),sq_nonneg (p 2*rowLogD u p 2)]
    · change (p 2*rowLogD u p 2)^2≤1
      nlinarith [sq_nonneg (p 2*rowLogD u p 0),sq_nonneg (p 2*rowLogD u p 1)]
  exact (abs_le).mpr ⟨by nlinarith,by nlinarith⟩

lemma cuspRemainder_row_scaled_deriv_bound (a b : ℝ) (s : ℂ) (C : ℝ)
    (hC : ∀v,|v*deriv (cuspTransition a b) v|≤C)
    (u : Fin 2→ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    ‖(p 2:ℂ)*deriv (axisSlice (fun q => cuspRemainderProfile a b s (rowHeight u q)) p j) (p j)‖≤
      (‖s‖+C)*(rowHeight u p)^s.re := by
  have hd := (rowProfile_axis_derivatives (cuspRemainderProfile a b s)
    (cuspRemainderProfile_contDiffAt a b s) u hu p hp j).1
  rw [hd.deriv]
  have he : (p 2:ℂ)*(deriv (cuspRemainderProfile a b s) (rowHeight u p)*
      (rowHeight u p:ℂ)*(rowLogD u p j:ℂ))=
      (((p 2*rowLogD u p j):ℝ):ℂ)*
        ((rowHeight u p:ℂ)*deriv (cuspRemainderProfile a b s) (rowHeight u p)) := by
    push_cast
    ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  apply (mul_le_of_le_one_left (norm_nonneg _) (rowLogD_hyperbolic_bound u hu p hp j)).trans
  exact cuspRemainderProfile_euler_bound a b s C hC _ (rowHeight_pos u hu p hp)

end CubicEisenstein

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation JointLogSeparation

theorem progressingCanonicalFamily_closed_step
    (g V : 𝓢(ℝ,ℂ)) (A M Nv : ℝ) (hM : 0≤M) (hNv : 0≤Nv)
    (hgM : ∀t,g t≠0→|t|≤M) (hV : ∀t,V t≠0→|t|≤Nv)
    (hWin : ∀t,g t≠0→V t=1)
    (hgOne : ∀u,|u|≤columnWindowRadius (Real.exp (-A)) (Real.exp A)→g u=1)
    (ε deltaLoss η : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (hη : 0<η)
    (hηsmall : η≤(1:ℝ)/1000) (hbudget : 3000*η≤(1:ℝ)/40) (J : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ),
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t|≤M+7) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t|≤M+7) ∧
      ∀(W : ℝ→ℂ) (hs : Function.support W⊆Set.Icc (Real.exp (-A)) (Real.exp A))
      (hW : ContDiff ℝ ∞ W), HasCompactSupport W →
      ∃C : ℝ,0≤C ∧
      ∀(S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
      (base : ActualEisensteinCubic.O→*ℂ) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O))
      (X F K E oldHeight : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      (∀u,‖base u‖≤1) → 1<Z → Real.exp 9000≤Z → 1≤X → X≤Z^3 → F≤Z^3 → 1≤E →
      Real.exp A*X≤D →
      let P:=InitialMeanSquare.outsideSquarefreeIdeals S D
      let hP:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
      letI : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal :=
        fun i=>by rw [poolPrimary_span P hP i];infer_instance
      (∀side : Bool, let windows:=if side then windows₁ else windows₂
        ∀(Ψ' : ActualEisensteinCubic.O→*ℂ) (m' : ActualEisensteinCubic.O) (labels' : Finset (Ideal ActualEisensteinCubic.O)) (X' F' K' : ℝ),
        CanonicalStateCondition base (∏Q∈S,Q) Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z K → ∀s : ℝ,
        (canonicalLogEnergy (poolPrimary P) (poolPrimary_ne_zero P hP) (poolPrimary_coprime P hP)
          (poolPrimary_good P hP) Finset.univ (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy (poolPrimary P) (poolPrimary_ne_zero P hP) (poolPrimary_coprime P hP)
          (poolPrimary_good P hP) Finset.univ (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      rowFamilyEnergy labels (fun I z=>outsideCanonicalRow S D hbad (normHeightTwist Ψ oldHeight)
        m (idealGenerator I) z W X) K≤
      2*X*rowFamilyEnergy labels (fun I z=>
        shortCompletedSum (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (idealGenerator I) z)
          W X (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0)) K+
      C*(X*F)^2*Z^(η+17*deltaLoss+39*ε)*E*(1+|oldHeight|)^(2*J) := by
  obtain ⟨w₁,w₂,C₀,hC₀,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,hstep⟩:=
    progressingCanonicalBin_closed_step g V A M Nv hM hNv hgM hV hWin
      ε deltaLoss η hε hδ hη hηsmall hbudget J
  obtain ⟨Cb,hCb,hcard⟩:=cubeLogRange_sq_small_power (Real.exp A) ε (Real.exp_pos _).le hε
  refine ⟨w₁,w₂,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro W hs hW hWc
  let moment:=∫ξ : ℝ,‖reopeningCoefficient W (Real.exp (-A)) (Real.exp A) (Real.exp_pos _) hs hW ξ‖*(1+|ξ|)^J
  refine ⟨2*Cb*C₀*moment^2,by positivity,?_⟩
  intro S D hbad hSp base Z Ψ m labels X F K E oldHeight hstate hbase hZ hZbig hX hXZ hFZ hE hD
  dsimp only
  let P:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hP:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span P hP i];infer_instance
  intro ih
  have hsource:=hstep S D hbad hSp base Z Ψ m labels X F K E oldHeight
    hstate hbase hZ hZbig hX hXZ hFZ hE ih
  have hwhole:=progressingCanonicalFamily_energy S D hbad hSp labels Ψ m W
    (Real.exp (-A)) (Real.exp A) (Real.exp_pos _) (Real.exp_pos _).le hs hW hWc
    g hgOne X (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0) K
    (C₀*(X*F)^2*Z^(η+17*deltaLoss+38*ε)*E) oldHeight J hstate.column_pos
    (zero_lt_one.trans_le hstate.row_ge_one) (by positivity) hD hsource
  have hcount:=hcard X Z hstate.column_pos.le hZ.le hXZ
  have hpower : Z^ε*Z^(η+17*deltaLoss+38*ε)=Z^(η+17*deltaLoss+39*ε) := by
    rw [←Real.rpow_add (by linarith : 0<Z)]
    congr 1
    ring
  apply hwhole.trans
  apply add_le_add le_rfl
  calc
    _ ≤ 2*(Cb*Z^ε)*(C₀*(X*F)^2*Z^(η+17*deltaLoss+38*ε)*E)*(1+|oldHeight|)^(2*J)*moment^2 := by
      change 2*((cubeLogRange (Real.exp A) X).card:ℝ)^2*
        (C₀*(X*F)^2*Z^(η+17*deltaLoss+38*ε)*E)*(1+|oldHeight|)^(2*J)*moment^2≤_
      gcongr
    _ = (2*Cb*C₀*moment^2)*(X*F)^2*(Z^ε*Z^(η+17*deltaLoss+38*ε))*E*(1+|oldHeight|)^(2*J) := by ring
    _ = _ := by rw [hpower]

end CanonicalRowCompletion

end

end OAI
end OAIOriginalModule0248

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.SeedHeight
Source SHA256: 66be2c4e5522cfcce39313e6881eba43efb5c006c60074be04c8dbe211c0fe79
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0249



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
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups

lemma fullCuspHeight_le_barrier (x : FullCuspClasses) (w : HyperbolicSpace) :
    fullCuspHeight x w≤max 3 (cuspBarrier 2 3 w) := by
  by_cases hx : fullCuspHeight x w≤3
  · exact hx.trans (le_max_left _ _)
  · have he : cuspBarrier 2 3 w=fullCuspHeight x w := by
      rw [cuspBarrier,fullCuspProfileSum_eq_single _
        (fun v hv => cuspBarrierProfile_zero 2 3 (by norm_num) v (by linarith)) w x (by linarith),
        cuspBarrierProfile,cuspTransition_one 2 3 _ (by norm_num) (by linarith),one_mul]
      ring
    exact he ▸ le_max_right _ _

lemma cosetHeight_le_barrier (r : CuspCosets) (w : HyperbolicSpace) :
    cosetHeight r w≤max 3 (cuspBarrier 2 3 w) := by
  induction r using Quotient.inductionOn with
  | _ M =>
    change cosetHeight (cosetOf M) w≤max 3 (cuspBarrier 2 3 w)
    rw [cosetHeight_cosetOf]
    exact fullCuspHeight_le_barrier (fullCuspOf M.1) w

lemma kernel_compact_seed_height_bound (a : ℝ) (S : Set KernelQuotient) (hS : IsCompact S) :
    ∃B : ℝ,a≤B ∧ 3≤B ∧ ∀q∈S,kernelQuotientBarrier 2 3 q≤B := by
  obtain ⟨B,hB⟩ := (hS.image (kernelQuotientBarrier_contMDiff 2 3 (by norm_num) (by norm_num)).continuous).bddAbove
  refine ⟨max a (max 3 B),le_max_left _ _,(le_max_left 3 B).trans (le_max_right _ _),?_⟩
  intro q hq
  exact (hB (Set.mem_image_of_mem _ hq)).trans ((le_max_right 3 B).trans (le_max_right _ _))

def kernelSeedHeightBound (a : ℝ) (S : Set KernelQuotient) (hS : IsCompact S) : ℝ :=
  Classical.choose (kernel_compact_seed_height_bound a S hS)

lemma kernelSeedHeightBound_spec (a : ℝ) (S : Set KernelQuotient) (hS : IsCompact S) :
    a≤kernelSeedHeightBound a S hS ∧ 3≤kernelSeedHeightBound a S hS ∧
      ∀q∈S,kernelQuotientBarrier 2 3 q≤kernelSeedHeightBound a S hS :=
  Classical.choose_spec (kernel_compact_seed_height_bound a S hS)

def compactSeedTransition (a b B : ℝ) : C(Set.Icc a B,ℂ) :=
  ⟨fun v => (cuspTransition a b (v:ℝ):ℂ),Complex.continuous_ofReal.comp
    ((cuspTransition_contDiff a b).continuous.comp continuous_subtype_val)⟩

def compactSeedProfile (a b B : ℝ) (ha : 0<a) (s : ℂ) : C(Set.Icc a B,ℂ) :=
  compactSeedTransition a b B * NormedSpace.exp (s • compactLogProfile a B ha)

lemma compactSeedProfile_entire (a b B : ℝ) (ha : 0<a) :
    Differentiable ℂ (compactSeedProfile a b B ha) :=
  (differentiable_const _).mul (differentiable_exp_smul_const ℂ (compactLogProfile a B ha))

lemma compactSeedProfile_apply (a b B : ℝ) (ha : 0<a) (s : ℂ) (v : Set.Icc a B) :
    compactSeedProfile a b B ha s v=cuspSeedProfile a b s v := by
  have he := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ v)
    (continuous_eval_const v) (s • compactLogProfile a B ha)
  change (NormedSpace.exp (s • compactLogProfile a B ha)) v=
    NormedSpace.exp ((s • compactLogProfile a B ha) v) at he
  change (cuspTransition a b (v:ℝ):ℂ)*(NormedSpace.exp (s • compactLogProfile a B ha)) v=_
  rw [he,←Complex.exp_eq_exp_ℂ]
  simp only [compactLogProfile,ContinuousMap.smul_apply,smul_eq_mul,cuspSeedProfile,
    positiveHeightPower,logRatioPower,Real.log_one,sub_zero,ContinuousMap.coe_mk]

lemma compactHeightProfile_seed (a b B : ℝ) (ha : 0<a) (hab : a<b) (hB : a≤B)
    (s : ℂ) (v : ℝ) (hv : v≤B) :
    compactHeightProfile a B hB (compactSeedProfile a b B ha s) v=cuspSeedProfile a b s v := by
  by_cases hva : a≤v
  · rw [compactHeightProfile,Set.indicator_of_mem (show v∈Set.Icc a B from ⟨hva,hv⟩),
      Set.projIcc_of_mem hB ⟨hva,hv⟩,compactSeedProfile_apply]
  · rw [compactHeightProfile,Set.indicator_of_notMem (by simp [Set.mem_Icc,hva]),
      cuspSeedProfile,cuspTransition_zero a b v hab (le_of_not_ge hva)]
    simp

lemma kernelCompactProfile_seed (a b B : ℝ) (ha : 0<a) (hab : a<b) (hB : a≤B)
    (hthree : 3≤B) (s : ℂ) (q : KernelQuotient) (hq : kernelQuotientBarrier 2 3 q≤B) :
    kernelCompactProfile a B hB (compactSeedProfile a b B ha s) q=kernelQuotientSeed a b s q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change cuspCutoffCorrection 1 (compactHeightProfile a B hB (compactSeedProfile a b B ha s)) w=
      cuspCutoffCorrection 1 (cuspSeedProfile a b s) w
    unfold cuspCutoffCorrection
    apply tsum_congr
    intro r
    unfold cuspCutoffTerm
    rw [compactHeightProfile_seed a b B ha hab hB s _
      ((cosetHeight_le_barrier r w).trans (max_le hthree hq))]

def kernelLocalSeedL2 (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (s : ℂ) : KernelQuotientL2 :=
  kernelMassRestrictionCLM S hS.measurableSet
    (compactProfileL2 a (kernelSeedHeightBound a S hS) (kernelSeedHeightBound_spec a S hS).1
      (compactSeedProfile a b (kernelSeedHeightBound a S hS) ha s))

lemma kernelLocalSeedL2_entire (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) : Differentiable ℂ (kernelLocalSeedL2 S hS a b ha) := by
  exact (kernelMassRestrictionCLM S hS.measurableSet).differentiable.comp
    ((compactProfileL2 a (kernelSeedHeightBound a S hS) (kernelSeedHeightBound_spec a S hS).1).differentiable.comp
      (compactSeedProfile_entire a b (kernelSeedHeightBound a S hS) ha))

lemma kernelLocalSeedL2_ae_eq (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    (kernelLocalSeedL2 S hS a b ha s : KernelQuotient→ℂ)=ᵐ[integralQuotientVolume globalKubotaKernel]
      S.indicator (kernelQuotientSeed a b s) := by
  let B := kernelSeedHeightBound a S hS
  have hB := kernelSeedHeightBound_spec a S hS
  filter_upwards [kernelMassRestriction_coe S hS.measurableSet
    (compactProfileL2 a B hB.1 (compactSeedProfile a b B ha s)),
    compactProfileL2_ae_eq a B hB.1 (compactSeedProfile a b B ha s)] with q hr hp
  change kernelMassRestriction S hS.measurableSet
    (compactProfileL2 a B hB.1 (compactSeedProfile a b B ha s)) q=S.indicator (kernelQuotientSeed a b s) q
  rw [hr]
  by_cases hq : q∈S
  · rw [Set.indicator_of_mem hq,Set.indicator_of_mem hq,hp]
    exact kernelCompactProfile_seed a b B ha hab hB.1 hB.2.1 s q (hB.2.2 q hq)
  · rw [Set.indicator_of_notMem hq,Set.indicator_of_notMem hq]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

def kernelCorrectedSeed (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : KernelQuotient→ℂ :=
  fun q => kernelQuotientSeed a b s q+kernelEisensteinL2Correction a b ha hab s q

def kernelLocalCorrectedSeed (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : KernelQuotientL2 :=
  kernelLocalSeedL2 S hS a b ha s +
    kernelMassRestrictionCLM S hS.measurableSet (kernelEisensteinL2Correction a b ha hab s)

lemma kernelLocalCorrectedSeed_meromorphicAt (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) :
    MeromorphicAt (kernelLocalCorrectedSeed S hS a b ha hab) (4/3:ℂ) := by
  exact ((kernelLocalSeedL2_entire S hS a b ha).analyticAt (4/3)).meromorphicAt.add
    (meromorphicAt_clm (kernelMassRestrictionCLM S hS.measurableSet)
      (kernelEisensteinL2Correction_meromorphicAt a b ha hab))

lemma kernelLocalCorrectedSeed_analyticAt_nonreal (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelLocalCorrectedSeed S hS a b ha hab) s := by
  exact ((kernelLocalSeedL2_entire S hS a b ha).analyticAt s).add
    ((ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := KernelQuotientL2)
      (kernelMassRestrictionCLM S hS.measurableSet) (kernelEisensteinL2Correction a b ha hab s)).comp_of_eq
        (kernelEisensteinL2Correction_analyticAt_nonreal a b ha hab s hs hi) rfl)

lemma kernelLocalCorrectedSeed_ae_eq (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    (kernelLocalCorrectedSeed S hS a b ha hab s : KernelQuotient→ℂ)=ᵐ[integralQuotientVolume globalKubotaKernel]
      S.indicator (kernelCorrectedSeed a b ha hab s) := by
  filter_upwards [Lp.coeFn_add (kernelLocalSeedL2 S hS a b ha s)
      (kernelMassRestrictionCLM S hS.measurableSet (kernelEisensteinL2Correction a b ha hab s)),
    kernelLocalSeedL2_ae_eq S hS a b ha hab s,
    kernelMassRestriction_coe S hS.measurableSet (kernelEisensteinL2Correction a b ha hab s)]
    with q hsum hseed hcor
  change (kernelLocalSeedL2 S hS a b ha s+
    kernelMassRestrictionCLM S hS.measurableSet (kernelEisensteinL2Correction a b ha hab s)) q=_
  rw [hsum]
  change kernelLocalSeedL2 S hS a b ha s q+
    kernelMassRestriction S hS.measurableSet (kernelEisensteinL2Correction a b ha hab s) q=_
  rw [hseed,hcor]
  by_cases hq : q∈S
  · simp only [Set.indicator_of_mem hq,kernelCorrectedSeed]
  · simp only [Set.indicator_of_notMem hq,add_zero]

lemma kernelLocalCorrectedSeed_residue_limit (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) :
    Tendsto (fun s : ℂ => (s-4/3)•kernelLocalCorrectedSeed S hS a b ha hab s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (kernelMassRestrictionCLM S hS.measurableSet (kernelEisensteinResidueVector a b ha hab))) := by
  have hseed : Tendsto (fun s : ℂ => (s-4/3)•kernelLocalSeedL2 S hS a b ha s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 0) := by
    have hh : ContinuousAt (fun s : ℂ => (s-4/3)•kernelLocalSeedL2 S hS a b ha s) (4/3:ℂ) :=
      (continuousAt_id.sub continuousAt_const).smul
        ((kernelLocalSeedL2_entire S hS a b ha).continuous.continuousAt)
    simpa only [sub_self,zero_smul] using hh.tendsto.mono_left
      (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  have hcor := (kernelMassRestrictionCLM S hS.measurableSet).continuous.continuousAt.tendsto.comp
    (kernelEisensteinResidueVector_limit a b ha hab)
  have hh := hseed.add hcor
  simpa only [kernelLocalCorrectedSeed,smul_add,map_smul,Function.comp_def,zero_add] using hh

end

section
open Filter
open scoped BigOperators Classical Topology ContDiff

section PartialDerivatives
variable {A E G : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma partial_iteratedFDeriv_contDiffAt (F : A→E→G) (a : A) (x : E)
    (hF : ContDiffAt ℝ ∞ (Function.uncurry F) (a,x)) (k : ℕ) :
    ContDiffAt ℝ ∞ (fun p : A×E => iteratedFDeriv ℝ k (F p.1) p.2) (a,x) := by
  induction k with
  | zero =>
    exact hF.continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 ℝ E G).symm : G→L[ℝ] E [×0]→L[ℝ]G)
  | succ k ih =>
    have hpair : ContDiffAt ℝ ∞
        (fun p : (A×E)×E => (p.1.1,p.2)) ((a,x),x) :=
      (contDiffAt_fst.fst).prodMk contDiffAt_snd
    have hp := ih.comp ((a,x),x) hpair
    have hd : ContDiffAt ℝ ∞
        (fun p : A×E => fderiv ℝ (fun y => iteratedFDeriv ℝ k (F p.1) y) p.2) (a,x) :=
      hp.fderiv contDiffAt_snd (by simp)
    exact hd.continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => E) G).symm :
        (E→L[ℝ] E [×k]→L[ℝ]G)→L[ℝ] E [×(k+1)]→L[ℝ]G)

lemma compact_family_derivative_bound (F : A→E→G)
    (K : Set A) (P : Set E) (hK : IsCompact K) (hP : IsCompact P)
    (hF : ∀a∈K,∀x,ContDiffAt ℝ ∞ (Function.uncurry F) (a,x))
    (hsupp : ∀a∈K,tsupport (F a)⊆P) (k : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀a∈K,∀x,‖iteratedFDeriv ℝ k (F a) x‖≤C := by
  have hc : ContinuousOn (fun p : A×E => iteratedFDeriv ℝ k (F p.1) p.2) (K×ˢP) := by
    intro p hp
    exact (partial_iteratedFDeriv_contDiffAt F p.1 p.2 (hF p.1 hp.1 p.2) k).continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := (hK.prod hP).bddAbove_image hc.norm
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro a ha x
  by_cases hx : x∈P
  · exact (hC ⟨(a,x),⟨ha,hx⟩,rfl⟩).trans (le_max_left _ _)
  · have hz : iteratedFDeriv ℝ k (F a) x=0 := by
      by_contra hn
      exact hx (hsupp a ha (support_iteratedFDeriv_subset k hn))
    rw [hz,norm_zero]
    exact le_max_right _ _

end PartialDerivatives
section

variable {A E ι : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compact_smooth_family_tsum (F : A→E→ℂ)
    (K : Set A) (P : Set E) (hK : IsCompact K) (hP : IsCompact P)
    (hF : ∀a∈K,∀x,ContDiffAt ℝ ∞ (Function.uncurry F) (a,x))
    (hsupp : ∀a∈K,tsupport (F a)⊆P)
    (a : ι→A) (ha : ∀i,a i∈K) (b : ι→ℂ) (hb : Summable (fun i => ‖b i‖)) :
    ContDiff ℝ ∞ (fun x => ∑'i,b i*F (a i) x) := by
  choose C hC hbound using compact_family_derivative_bound F K P hK hP hF hsupp
  have hf (i : ι) : ContDiff ℝ ∞ (F (a i)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (hF (a i) (ha i) x).comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hprod (i : ι) : ContDiff ℝ ∞ (fun x => b i*F (a i) x) :=
    contDiff_const.mul (hf i)
  apply contDiff_tsum (v := fun k i => ‖b i‖*C k) hprod
  · intro k hk
    exact hb.mul_right (C k)
  · intro k i x hk
    have he : iteratedFDeriv ℝ k (fun x => b i*F (a i) x) x=
        b i • iteratedFDeriv ℝ k (F (a i)) x :=
      by simpa only [smul_eq_mul] using
        (iteratedFDeriv_const_smul_apply' (a := b i) (i := k) (x := x)
          ((hf i).contDiffAt.of_le (by simp)))
    rw [he,norm_smul]
    exact mul_le_mul_of_nonneg_left (hbound k (a i) (ha i) x) (norm_nonneg _)

end

lemma rowEnergy_real_smul (r : ℝ) (u : Fin 2→ℂ) :
    rowEnergy (r • u)=r^2*rowEnergy u := by
  simp only [rowEnergy,Pi.smul_apply,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

def normalizedComplexRow (u : Fin 2→ℂ) : Fin 2→ℂ := (Real.sqrt (rowEnergy u))⁻¹ • u

lemma normalizedComplexRow_energy (u : Fin 2→ℂ) (hu : u≠0) :
    rowEnergy (normalizedComplexRow u)=1 := by
  rw [normalizedComplexRow,rowEnergy_real_smul,inv_pow,
    Real.sq_sqrt (rowEnergy_nonneg u),inv_mul_cancel₀ (rowEnergy_pos u hu).ne']

lemma rowEnergy_continuous : Continuous rowEnergy := by
  unfold rowEnergy
  fun_prop

lemma rowEnergy_unit_isCompact : IsCompact {u : Fin 2→ℂ | rowEnergy u=1} := by
  apply (isCompact_closedBall (0 : Fin 2→ℂ) 1).of_isClosed_subset
    (isClosed_eq rowEnergy_continuous continuous_const)
  intro u hu
  change rowEnergy u=1 at hu
  rw [Metric.mem_closedBall,dist_zero_right]
  simpa only [hu,Real.sqrt_one] using norm_le_sqrt_rowEnergy u

lemma rowEnergy_unit_ne_zero (u : Fin 2→ℂ) (hu : rowEnergy u=1) : u≠0 := by
  intro h
  simp [h,rowEnergy] at hu

def regularSpatialHeight (deltaLoss : ℝ) (p : SpatialCoordinates) : ℝ :=
  deltaLoss*ConcreteCompactWeight.positiveExtension (p 2/deltaLoss)

lemma regularSpatialHeight_pos (deltaLoss : ℝ) (hδ : 0<deltaLoss) (p : SpatialCoordinates) :
    0<regularSpatialHeight deltaLoss p :=
  mul_pos hδ (ConcreteCompactWeight.positiveExtension_pos _)

lemma regularSpatialHeight_contDiff (deltaLoss : ℝ) : ContDiff ℝ ∞ (regularSpatialHeight deltaLoss) := by
  unfold regularSpatialHeight
  exact contDiff_const.mul (ConcreteCompactWeight.positiveExtension_smooth.comp
    ((contDiff_apply ℝ ℝ 2).div_const deltaLoss))

lemma regularSpatialHeight_eq (deltaLoss : ℝ) (hδ : 0<deltaLoss) (p : SpatialCoordinates) (hp : deltaLoss≤p 2) :
    regularSpatialHeight deltaLoss p=p 2 := by
  rw [regularSpatialHeight,ConcreteCompactWeight.positiveExtension_eq _ ((le_div_iff₀ hδ).mpr (by simpa using hp))]
  field_simp

def regularRowKernel (s : ℂ) (deltaLoss : ℝ) (u : Fin 2→ℂ) (p : SpatialCoordinates) : ℂ :=
  logRatioPower s (regularSpatialHeight deltaLoss p)
    (heightDenominator (spatialHorizontal p) (regularSpatialHeight deltaLoss p) u)

lemma regularRowDenominator_contDiff (deltaLoss : ℝ) :
    ContDiff ℝ ∞ (fun p : (Fin 2→ℂ)×SpatialCoordinates =>
      heightDenominator (spatialHorizontal p.2) (regularSpatialHeight deltaLoss p.2) p.1) := by
  have hc (j : Fin 2) : ContDiff ℝ ∞ (fun p : (Fin 2→ℂ)×SpatialCoordinates => p.1 j) :=
    (contDiff_apply ℝ ℂ j).comp contDiff_fst
  have hz := spatialHorizontal_contDiff.comp (contDiff_snd (E := Fin 2→ℂ))
  have hv := (regularSpatialHeight_contDiff deltaLoss).comp (contDiff_snd (E := Fin 2→ℂ))
  have hw := ((hc 0).mul hz).add (hc 1)
  simp only [heightDenominator,←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  exact (((Complex.reCLM.contDiff.comp hw).mul (Complex.reCLM.contDiff.comp hw)).add
    ((Complex.imCLM.contDiff.comp hw).mul (Complex.imCLM.contDiff.comp hw))).add
    ((((Complex.reCLM.contDiff.comp (hc 0)).mul (Complex.reCLM.contDiff.comp (hc 0))).add
      ((Complex.imCLM.contDiff.comp (hc 0)).mul (Complex.imCLM.contDiff.comp (hc 0)))).mul (hv.pow 2))

lemma regularRowKernel_contDiffAt (s : ℂ) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (u : Fin 2→ℂ) (hu : u≠0) (p : SpatialCoordinates) :
    ContDiffAt ℝ ∞ (Function.uncurry (regularRowKernel s deltaLoss)) (u,p) := by
  have hv : ContDiff ℝ ∞ (fun q : (Fin 2→ℂ)×SpatialCoordinates => regularSpatialHeight deltaLoss q.2) :=
    (regularSpatialHeight_contDiff deltaLoss).comp contDiff_snd
  have hD := (regularRowDenominator_contDiff deltaLoss).contDiffAt (x := (u,p))
  have hv0 := regularSpatialHeight_pos deltaLoss hδ p
  have hD0 := heightDenominator_pos (spatialHorizontal p) (regularSpatialHeight deltaLoss p) hv0 u hu
  have hl := (hv.contDiffAt.log hv0.ne').sub (hD.log hD0.ne')
  exact (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp (u,p) hl)).cexp

lemma heightDenominator_real_smul (z : ℂ) (v r : ℝ) (u : Fin 2→ℂ) :
    heightDenominator z v (r•u)=r^2*heightDenominator z v u := by
  unfold heightDenominator
  have he : (r•u) 0*z+(r•u) 1=r•(u 0*z+u 1) := by
    simp only [Pi.smul_apply,smul_add,smul_mul_assoc]
  rw [he]
  simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

lemma heightDenominator_normalized (z : ℂ) (v : ℝ) (u : Fin 2→ℂ) :
    heightDenominator z v (normalizedComplexRow u)=heightDenominator z v u/rowEnergy u := by
  rw [normalizedComplexRow,heightDenominator_real_smul,inv_pow,Real.sq_sqrt (rowEnergy_nonneg u)]
  ring

lemma regularRowKernel_eq (s : ℂ) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (u : Fin 2→ℂ)
    (p : SpatialCoordinates) (hp : deltaLoss≤p 2) :
    regularRowKernel s deltaLoss u p=rowSmoothPower s u p := by
  rw [regularRowKernel,regularSpatialHeight_eq deltaLoss hδ p hp]
  unfold rowSmoothPower spatialHeightPower
  rw [←heightDenominator_eq_quadratic]
  rfl

lemma normalized_row_summand (s : ℂ) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (r : CuspCosets) (p : SpatialCoordinates) (hp : deltaLoss≤p 2) :
    summand 1 s r*regularRowKernel s deltaLoss (normalizedComplexRow (embeddedRow r)) p=
      smoothSummand s r p := by
  have hu := embeddedRow_ne_zero r
  have hE := rowEnergy_pos _ hu
  have hv : 0<p 2 := hδ.trans_le hp
  have hD := heightDenominator_pos (spatialHorizontal p) (p 2) hv (embeddedRow r) hu
  rw [regularRowKernel,regularSpatialHeight_eq deltaLoss hδ p hp,heightDenominator_normalized]
  rw [summand,rowOperator_one,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hE.ne'),
    ←Complex.ofReal_log hE.le]
  unfold smoothSummand rowSmoothPower spatialHeightPower
  rw [←heightDenominator_eq_quadratic]
  unfold logRatioPower
  rw [Real.log_div hD.ne' hE.ne',mul_assoc,←Complex.exp_add]
  congr 2
  unfold spatialHorizontal
  push_cast
  ring

theorem regular_eisenstein_compact_smooth (s : ℂ) (hs : 2<s.re)
    (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ψ : SpatialCoordinates→ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    ContDiff ℝ ∞ (fun p => ∑'r : CuspCosets,
      summand 1 s r*(ψ p*regularRowKernel s deltaLoss (normalizedComplexRow (embeddedRow r)) p)) := by
  apply compact_smooth_family_tsum (fun u p => ψ p*regularRowKernel s deltaLoss u p)
    {u : Fin 2→ℂ | rowEnergy u=1} (tsupport ψ) rowEnergy_unit_isCompact hcψ
  · intro u hu p
    have hψp : ContDiffAt ℝ ∞ (fun q : (Fin 2→ℂ)×SpatialCoordinates => ψ q.2) (u,p) :=
      hψ.contDiffAt.comp (u,p) contDiffAt_snd
    exact hψp.mul (regularRowKernel_contDiffAt s deltaLoss hδ u (rowEnergy_unit_ne_zero u hu) p)
  · intro u hu
    exact tsupport_mul_subset_left
  · intro r
    exact normalizedComplexRow_energy _ (embeddedRow_ne_zero r)
  · exact summable_norm_summand 1 s hs

theorem smoothEisenstein_contDiffAt (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (smoothEisenstein s) p := by
  let deltaLoss : ℝ:=p 2/2
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  let χ : ContDiffBump p := ⟨1,2,by norm_num,by norm_num⟩
  let ψ : SpatialCoordinates→ℂ:=fun q => (χ q:ℂ)
  have hψ : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp χ.contDiff
  have hcψ : HasCompactSupport ψ := by
    have he : Function.support ψ=Function.support (fun q => χ q) := by
      ext q
      simp [Function.mem_support,ψ]
    change IsCompact (closure (Function.support ψ))
    rw [he]
    exact χ.hasCompactSupport
  have hsum := regular_eisenstein_compact_smooth s hs deltaLoss hδ ψ hψ hcψ
  apply hsum.contDiffAt.congr_of_eventuallyEq
  have hn : ∀ᶠq in 𝓝 p, deltaLoss<q 2 :=
    (isOpen_lt continuous_const (continuous_apply 2)).mem_nhds (by dsimp [deltaLoss]; linarith)
  filter_upwards [χ.eventuallyEq_one,hn] with q hχ hq
  unfold smoothEisenstein
  apply tsum_congr
  intro r
  have hψq : ψ q=1 := by simp [ψ,hχ]
  rw [hψq,one_mul]
  exact (normalized_row_summand s deltaLoss hδ r q hq.le).symm

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

lemma kernel_contMDiff_of_spatial (f : KernelQuotient→ℂ) (F : SpatialCoordinates→ℂ)
    (hF : ∀p,0<p 2→ContDiffAt ℝ ∞ F p)
    (hcoord : ∀q : KernelQuotient,∀p∈hyperbolicSpatialChart.target,
      f ((kernelQuotientChart q).symm p)=F p) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f := by
  intro q
  have hq : q∈(kernelQuotientChart q).source := mem_chart_source SpatialCoordinates q
  have hp : kernelQuotientChart q q∈hyperbolicSpatialChart.target :=
    ((kernelQuotientChart q).map_source hq).1
  have hc : ContinuousAt (kernelQuotientChart q) q :=
    (kernelQuotientChart q).continuousOn.continuousAt ((kernelQuotientChart q).open_source.mem_nhds hq)
  have heq : f=ᶠ[𝓝 q] (fun t => F (kernelQuotientChart q t)) := by
    filter_upwards [(kernelQuotientChart q).open_source.mem_nhds hq] with t ht
    rw [←hcoord q _ ((kernelQuotientChart q).map_source ht).1,
      (kernelQuotientChart q).left_inv ht]
  rw [contMDiffAt_iff]
  refine ⟨((hF _ (hyperbolicSpatialChart_target_positive hp)).continuousAt.comp hc).congr heq.symm,?_⟩
  have he : (fun p => f ((kernelQuotientChart q).symm p))=ᶠ[𝓝 (kernelQuotientChart q q)] F := by
    filter_upwards [hyperbolicSpatialChart.open_target.mem_nhds hp] with p hp
    exact hcoord q p hp
  have hh := (hF _ (hyperbolicSpatialChart_target_positive hp)).congr_of_eventuallyEq he
  have hh' := hh.contDiffWithinAt (s := Set.univ)
  simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Function.id_comp,Function.comp_id,Set.range_id,
    chartAt_self_eq,kernelSpatial_chartAt,OpenPartialHomeomorph.refl_apply,Function.comp_def,id_eq] using hh'

lemma kernelQuotientEisenstein_coordinate (s : ℂ) (hs : 2<s.re) (q : KernelQuotient)
    (p : SpatialCoordinates) (hp : p∈hyperbolicSpatialChart.target) :
    kernelQuotientEisenstein s hs ((kernelQuotientChart q).symm p)=smoothEisenstein s p := by
  rw [kernelQuotientChart_symm,hyperbolicSpatialChart_symm_eq hp,
    kernelQuotientEisenstein_mk,hyperbolicEisenstein_upperPoint,
    smoothEisenstein_eq_actual s p (hyperbolicSpatialChart_target_positive hp)]
  rfl

lemma kernelQuotientEisenstein_contMDiff (s : ℂ) (hs : 2<s.re) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (kernelQuotientEisenstein s hs) :=
  kernel_contMDiff_of_spatial _ _ (smoothEisenstein_contDiffAt s hs)
    (kernelQuotientEisenstein_coordinate s hs)

lemma kernelQuotientSeed_coordinate (a b : ℝ) (s : ℂ) (q : KernelQuotient)
    (p : SpatialCoordinates) (hp : p∈hyperbolicSpatialChart.target) :
    kernelQuotientSeed a b s ((kernelQuotientChart q).symm p)=smoothCuspSeedField a b s p := by
  rw [kernelQuotientChart_symm,hyperbolicSpatialChart_symm_eq hp]
  change smoothCuspSeed a b s _=smoothCuspSeedField a b s p
  rw [smoothCuspSeedField,dite_eq_left (hyperbolicSpatialChart_target_positive hp)]
  rfl

lemma kernelQuotientSeed_contMDiff (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (kernelQuotientSeed a b s) :=
  kernel_contMDiff_of_spatial _ _ (actual_smoothCuspSeed_contDiffAt a b s ha hab)
    (kernelQuotientSeed_coordinate a b s)

def kernelCutoffRemainderTest (n : ℕ) (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) : kernelSmoothTests := by
  let f : KernelQuotient→ℂ:=fun q => (kernelExhaustionCutoff n q:ℂ)*
    (kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q)
  refine ⟨f,?_,?_⟩
  · have hm : ContDiff ℝ ∞ (fun z : ℂ × ℂ => z.1*z.2) := contDiff_fst.mul contDiff_snd
    exact hm.contMDiff.comp
      ((Complex.ofRealCLM.contDiff.contMDiff.comp (kernelExhaustionCutoff_smooth n)).prodMk_space
        ((kernelQuotientEisenstein_contMDiff s hs).sub (kernelQuotientSeed_contMDiff a b s ha hab)))
  · apply HasCompactSupport.of_support_subset_isCompact (kernelExhaustionCutoff_hasCompactSupport n)
    intro q hq
    by_contra hn
    have hz : kernelExhaustionCutoff n q=0 := by
      by_contra hne
      exact hn (subset_closure hne)
    exact hq (by simp [f,hz])

lemma kernelCutoffRemainderTest_apply (n : ℕ) (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (q : KernelQuotient) :
    (kernelCutoffRemainderTest n a b ha hab s hs).1 q=(kernelExhaustionCutoff n q:ℂ)*
      (kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q) := rfl

end CubicEisenstein

open scoped BigOperators Classical ContDiff
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm)

def HasInitialCanonicalDensityAtRadius {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) : Prop :=
  ∀ deltaLoss : ℝ,0 < deltaLoss → ∀ P : ℕ,∀ A : ℝ,0≤A → ∃ J : ℕ,
    ∀ V₁ V₂ : ℝ → ℂ,HasCompactSupport V₁ → HasCompactSupport V₂ →
    ContDiff ℝ ∞ V₁ → ContDiff ℝ ∞ V₂ →
    (∀s,V₁ s≠0→|s|≤A) → (∀s,V₂ s≠0→|s|≤A) →
    ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ P ≤ E ∧ ∀ (D : ℕ) (Z X lengthScale K : ℝ)
      (R : Finset (OutsidePrimeIndex S D)) (ray : SecondRayIndex) (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)),
      1 ≤ Z → Cpool*Z^E ≤ D → 1 ≤ X → 1 ≤ lengthScale → 1 ≤ K →
      X ≤ Z^P → lengthScale ≤ Z^P → K ≤ Z^P →
      initialExcludedNorm S*primeProductNorm (outsidePrime S D) R ≤ Z^P →
      X*lengthScale ≤ Z^2 →
      K*(initialExcludedNorm S*primeProductNorm (outsidePrime S D) R) ≤ X*lengthScale*Z^(-(1 : ℝ)/20) →
      (∀ z ∈ T,Admissible z.1 ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
        z.2 ≠ 0 ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) →
      (∀z∈T,IsCoprime z.1 (∏P∈S,P)) →
      outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X J ≤ C*Z^deltaLoss*(X*lengthScale)^2

end InitialMeanSquare

end

end OAI
end OAIOriginalModule0249

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.CuspResidues
Source SHA256: d2fda4f589bb97b11e7215e3f8d159ca24739684eb448f60711b630fbe1d3590
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0250


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
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups Matrix

lemma levelThree_integral_eq_translation (M : CubicKubota.levelThree)
    (hc : (M : SL(2,ActualEisensteinCubic.O)) 1 0=0) :
    integralComplexMatrix M.1=complexTranslation (ConcreteTraceCRT.eisEmbedding ((M : SL(2,ActualEisensteinCubic.O)) 0 1)) := by
  have hr := row_eq_one_of_lower_left_zero M hc
  have hd : (M : SL(2,ActualEisensteinCubic.O)) 1 1=1 := by
    simpa [row,Matrix.one_apply] using congrFun hr 1
  have ha : (M : SL(2,ActualEisensteinCubic.O)) 0 0=1 := by
    have hh : (M : SL(2,ActualEisensteinCubic.O)) 0 0 * (M : SL(2,ActualEisensteinCubic.O)) 1 1-
      (M : SL(2,ActualEisensteinCubic.O)) 0 1 * (M : SL(2,ActualEisensteinCubic.O)) 1 0=1 := by
      simpa only [Matrix.det_fin_two] using (M : SL(2,ActualEisensteinCubic.O)).property
    simpa only [hc,hd,mul_zero,mul_one,sub_zero] using hh
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexTranslation,ha,hc,hd]

lemma periodDomain_unique_translate (z w t : ℂ) (hz : z∈periodDomain) (hw : w∈periodDomain)
    (ht : t∈periodLattice) (he : z=w+t) : z=w := by
  have hf := ZSpan.fract_add_ZSpan periodBasis w ht
  rw [←he,(ZSpan.fract_eq_self (b := periodBasis)).mpr hz,
    (ZSpan.fract_eq_self (b := periodBasis)).mpr hw] at hf
  exact hf

def cuspPeriodRegion : Set HyperbolicSpace :=
  {w | hyperbolicHorizontal w∈periodDomain ∧ 1<hyperbolicHeight w}

lemma cuspPeriodRegion_measurable : MeasurableSet cuspPeriodRegion :=
  (periodDomain_measurable.preimage hyperbolicHorizontal_continuous.measurable).inter
    (measurableSet_Ioi.preimage hyperbolicHeight_continuous.measurable)

lemma kernelProjection_cuspPeriodRegion_injective :
    Set.InjOn (integralOrbitProjection globalKubotaKernel) cuspPeriodRegion := by
  intro u hu v hv he
  obtain ⟨M,hM⟩ := (integralOrbitProjection_eq_iff globalKubotaKernel u v).mp he
  have hMu : integralComplexMatrix (M:SL(2,ActualEisensteinCubic.O)) • v=u := hM
  have hc : (M:SL(2,ActualEisensteinCubic.O)) 1 0=0 := by
    by_contra hn
    have hb := integral_hyperbolicHeight_mul_le_one (M:SL(2,ActualEisensteinCubic.O)) hn v
    rw [hMu] at hb
    have huh : 1<hyperbolicHeight u := hu.2
    have hvh : 1<hyperbolicHeight v := hv.2
    nlinarith [mul_pos (sub_pos.mpr huh) (sub_pos.mpr hvh)]
  let N : CubicKubota.levelThree := ⟨M,globalKubotaKernel_le_levelThree M.2⟩
  have ht := levelThree_integral_eq_translation N hc
  obtain ⟨z,t,htpos,hvrep⟩ := upperPoint_surjective v
  have hua : u=upperPoint (z+ConcreteTraceCRT.eisEmbedding ((M:SL(2,ActualEisensteinCubic.O)) 0 1)) t htpos := by
    rw [←hMu,←hvrep,ht,complexTranslation_action]
  have hvl : hyperbolicHorizontal v=z := by rw [←hvrep,hyperbolicHorizontal_upperPoint]
  have hul : hyperbolicHorizontal u=z+ConcreteTraceCRT.eisEmbedding ((M:SL(2,ActualEisensteinCubic.O)) 0 1) := by
    rw [hua,hyperbolicHorizontal_upperPoint]
  obtain ⟨k,hk⟩ := CubicKubota.levelThree_upper N
  have hper : ConcreteTraceCRT.eisEmbedding ((M:SL(2,ActualEisensteinCubic.O)) 0 1)∈periodLattice := by
    change ConcreteTraceCRT.eisEmbedding ((N:CubicKubota.levelThree).1 0 1)∈periodLattice
    rw [hk,map_mul,map_ofNat]
    exact three_embedding_mem k
  have hehor : hyperbolicHorizontal u=hyperbolicHorizontal v :=
    periodDomain_unique_translate _ _ _ hu.1 hv.1 hper (by rw [hul,hvl])
  have hez : z+ConcreteTraceCRT.eisEmbedding ((M:SL(2,ActualEisensteinCubic.O)) 0 1)=z := by
    simpa only [hul,hvl] using hehor
  rw [hua,hez,←hvrep]

def cuspPeriodStrip (a b : ℝ) : Set HyperbolicSpace :=
  {w | hyperbolicHorizontal w∈periodDomain ∧ hyperbolicHeight w∈Set.Icc a b}

lemma cuspPeriodStrip_measurable (a b : ℝ) : MeasurableSet (cuspPeriodStrip a b) :=
  (periodDomain_measurable.preimage hyperbolicHorizontal_continuous.measurable).inter
    (measurableSet_Icc.preimage hyperbolicHeight_continuous.measurable)

lemma kernelProjection_cuspPeriodStrip_injective (a b : ℝ) (ha : 1<a) :
    Set.InjOn (integralOrbitProjection globalKubotaKernel) (cuspPeriodStrip a b) := by
  apply kernelProjection_cuspPeriodRegion_injective.mono
  intro w hw
  exact ⟨hw.1,ha.trans_le hw.2.1⟩

lemma kernelProjection_cuspPeriodStrip_measurePreserving (a b : ℝ) (ha : 1<a) :
    MeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (cuspPeriodStrip a b))
      ((integralQuotientVolume globalKubotaKernel).restrict
        (integralOrbitProjection globalKubotaKernel '' cuspPeriodStrip a b)) :=
  kernelProjection_measurePreserving_on _ (cuspPeriodStrip_measurable a b)
    (kernelProjection_cuspPeriodStrip_injective a b ha)

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups

def kernelCuspStripSet : Set KernelQuotient :=
  integralOrbitProjection globalKubotaKernel '' cuspPeriodStrip 5 6

lemma kernelCuspStripSet_measurable : MeasurableSet kernelCuspStripSet :=
  (cuspPeriodStrip_measurable 5 6).image_of_continuousOn_injOn
    (continuous_integralOrbitProjection globalKubotaKernel).continuousOn
    (kernelProjection_cuspPeriodStrip_injective 5 6 (by norm_num))

def kernelCuspStripAverage : KernelQuotientL2→L[ℂ]ℂ :=
  innerSL ℂ (indicatorConstLp 2 kernelCuspStripSet_measurable
    (measure_ne_top (integralQuotientVolume globalKubotaKernel) _) (1:ℂ))

lemma kernelCuspStripAverage_apply (F : KernelQuotientL2) :
    kernelCuspStripAverage F=∫q in kernelCuspStripSet,F q∂integralQuotientVolume globalKubotaKernel :=
  L2.inner_indicatorConstLp_one kernelCuspStripSet_measurable
    (measure_ne_top (integralQuotientVolume globalKubotaKernel) _) F

lemma kernelCuspStripAverage_hyperbolic (F : KernelQuotientL2) :
    kernelCuspStripAverage F=∫w in cuspPeriodStrip 5 6,
      F (integralOrbitProjection globalKubotaKernel w)∂hyperbolicVolume := by
  rw [kernelCuspStripAverage_apply]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hh := (Lp.aestronglyMeasurable F).mono_measure (Measure.restrict_le_self (s := kernelCuspStripSet))
  change AEStronglyMeasurable F ((integralQuotientVolume globalKubotaKernel).restrict
    (integralOrbitProjection globalKubotaKernel '' cuspPeriodStrip 5 6)) at hh
  change (∫q in integralOrbitProjection globalKubotaKernel '' cuspPeriodStrip 5 6,
    F q∂integralQuotientVolume globalKubotaKernel)=_
  rw [←hm.map_eq] at hh ⊢
  exact integral_map hm.measurable.aemeasurable hh

def kernelCuspAverageCompact : Set KernelQuotient :=
  {q | kernelQuotientBarrier 2 3 q≤6}

lemma kernelCuspAverageCompact_isCompact : IsCompact kernelCuspAverageCompact :=
  kernelBarrier_sublevel_isCompact 6

lemma kernelCuspStripSet_subset_compact : kernelCuspStripSet⊆kernelCuspAverageCompact := by
  rintro q ⟨w,hw,rfl⟩
  obtain ⟨z,v,hv,rfl⟩ := upperPoint_surjective w
  have hfive : 5≤v := by simpa only [hyperbolicHeight_upperPoint] using hw.2.1
  have hsix : v≤6 := by simpa only [hyperbolicHeight_upperPoint] using hw.2.2
  change cuspBarrier 2 3 (upperPoint z v hv)≤6
  have hh := cuspBarrier_high 2 3 (by norm_num) (by norm_num) 1 z v hv (by linarith)
  simpa only [map_one,one_smul] using hh.le.trans hsix

lemma kernelCuspStripAverage_restrict (F : KernelQuotientL2) :
    kernelCuspStripAverage (kernelMassRestrictionCLM kernelCuspAverageCompact
      kernelCuspAverageCompact_isCompact.measurableSet F)=kernelCuspStripAverage F := by
  rw [kernelCuspStripAverage_apply,kernelCuspStripAverage_apply]
  apply setIntegral_congr_ae kernelCuspStripSet_measurable
  filter_upwards [kernelMassRestriction_coe kernelCuspAverageCompact
    kernelCuspAverageCompact_isCompact.measurableSet F] with q hq
  intro hmem
  exact hq.trans (Set.indicator_of_mem (kernelCuspStripSet_subset_compact hmem) F)

def kernelCuspAverageFamily (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : ℂ :=
  kernelCuspStripAverage
    (kernelLocalCorrectedSeed kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab s)

lemma kernelCuspAverageFamily_meromorphicAt (a b : ℝ) (ha : 0<a) (hab : a<b) :
    MeromorphicAt (kernelCuspAverageFamily a b ha hab) (4/3:ℂ) :=
  meromorphicAt_clm kernelCuspStripAverage
    (kernelLocalCorrectedSeed_meromorphicAt kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab)

lemma kernelCuspAverageFamily_residue_limit (a b : ℝ) (ha : 0<a) (hab : a<b) :
    Tendsto (fun s : ℂ => (s-4/3)*kernelCuspAverageFamily a b ha hab s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (kernelCuspStripAverage (kernelEisensteinResidueVector a b ha hab))) := by
  have hh := kernelCuspStripAverage.continuous.continuousAt.tendsto.comp
    (kernelLocalCorrectedSeed_residue_limit kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab)
  simpa only [Function.comp_def,map_smul,smul_eq_mul,kernelCuspStripAverage_restrict,kernelCuspAverageFamily] using hh

lemma kernelCuspAverageFamily_actual_integral (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    kernelCuspAverageFamily a b ha hab s=∫w in cuspPeriodStrip 5 6,
      kernelCorrectedSeed a b ha hab s (integralOrbitProjection globalKubotaKernel w)∂hyperbolicVolume := by
  rw [kernelCuspAverageFamily,kernelCuspStripAverage_hyperbolic]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hlocal := kernelLocalCorrectedSeed_ae_eq kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab s
  have hrestr := ae_restrict_of_ae hlocal (s := kernelCuspStripSet)
  have hp := hm.quasiMeasurePreserving.ae_eq_comp hrestr
  apply integral_congr_ae
  filter_upwards [hp,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  exact hw.trans (Set.indicator_of_mem (kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩) _)

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups Matrix

def spatialComplexSplit : EuclideanSpatial ≃ᵐ ℝ × ℂ :=
  spatialHeightSplit.trans ((MeasurableEquiv.refl ℝ).prodCongr Complex.measurableEquivPi.symm)

lemma spatialComplexSplit_fst (p : EuclideanSpatial) : (spatialComplexSplit p).1=p 2 := rfl
lemma spatialComplexSplit_snd (p : EuclideanSpatial) :
    (spatialComplexSplit p).2=(p 0:ℂ)+(p 1:ℂ)*Complex.I := rfl

lemma spatialComplexSplit_preserves_volume : MeasurePreserving spatialComplexSplit volume volume :=
  ((MeasurePreserving.id volume).prod Complex.volume_preserving_equiv_pi.symm).comp
    spatialHeightSplit_preserves_volume

lemma spatialComplexSplit_coordinates (w : HyperbolicSpace) :
    spatialComplexSplit (hyperbolicEuclideanCoordinates w)=
      (hyperbolicHeight w,hyperbolicHorizontal w) := by
  apply Prod.ext
  · rfl
  · change (hyperbolicHorizontal w).re+(hyperbolicHorizontal w).im*Complex.I=hyperbolicHorizontal w
    exact Complex.re_add_im _

def cuspCoordinateLift (q : ℝ × ℂ) : HyperbolicSpace :=
  euclideanToHyperbolic (spatialComplexSplit.symm q)

lemma cuspCoordinateLift_positive (v : ℝ) (z : ℂ) (hv : 0<v) :
    cuspCoordinateLift (v,z)=upperPoint z v hv := by
  have he : spatialComplexSplit (hyperbolicEuclideanCoordinates (upperPoint z v hv))=(v,z) := by
    simp only [spatialComplexSplit_coordinates,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
  have he' := congrArg spatialComplexSplit.symm he
  rw [spatialComplexSplit.symm_apply_apply] at he'
  rw [cuspCoordinateLift,←he',euclideanToHyperbolic_coordinates]

def cuspEuclideanStrip : Set EuclideanSpatial :=
  spatialComplexSplit ⁻¹' (Set.Icc (5:ℝ) 6 ×ˢ periodDomain)

lemma cuspEuclideanStrip_measurable : MeasurableSet cuspEuclideanStrip :=
  spatialComplexSplit.measurable (measurableSet_Icc.prod periodDomain_measurable)

lemma cuspEuclideanStrip_positive : cuspEuclideanStrip⊆euclideanUpperHalf := by
  intro p hp
  have hh : 5≤p 2 := hp.1.1
  change 0<p 2
  linarith

lemma cuspEuclideanStrip_preimage :
    hyperbolicEuclideanCoordinates ⁻¹' cuspEuclideanStrip=cuspPeriodStrip 5 6 := by
  ext w
  change spatialComplexSplit (hyperbolicEuclideanCoordinates w)∈(Set.Icc (5:ℝ) 6 ×ˢ periodDomain) ↔ _
  rw [spatialComplexSplit_coordinates]
  exact and_comm

lemma cuspPeriodStrip_integral_coordinates (g : HyperbolicSpace→ℂ)
    (hg : AEStronglyMeasurable g hyperbolicVolume)
    (hint : IntegrableOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
      (Set.Icc (5:ℝ) 6 ×ˢ periodDomain) volume) :
    (∫w in cuspPeriodStrip 5 6,g w∂hyperbolicVolume)=
      ∫v in Set.Icc (5:ℝ) 6,(∫z in periodDomain,g (cuspCoordinateLift (v,z)))/(v:ℂ)^3 := by
  have hm := euclideanToHyperbolic_measurePreserving_on cuspEuclideanStrip
    cuspEuclideanStrip_measurable cuspEuclideanStrip_positive
  rw [cuspEuclideanStrip_preimage] at hm
  have hh := hg.mono_measure (Measure.restrict_le_self (s := cuspPeriodStrip 5 6))
  have he : (∫w in cuspPeriodStrip 5 6,g w∂hyperbolicVolume)=
      ∫p in cuspEuclideanStrip,g (euclideanToHyperbolic p)∂hyperbolicEuclideanVolume := by
    rw [←hm.map_eq] at hh ⊢
    exact integral_map hm.measurable.aemeasurable hh
  rw [he,hyperbolicEuclidean_setIntegral_complex cuspEuclideanStrip
    cuspEuclideanStrip_measurable cuspEuclideanStrip_positive]
  have hsplit := spatialComplexSplit.measurableEmbedding.setIntegral_map
    (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
    (Set.Icc (5:ℝ) 6 ×ˢ periodDomain) («μ» := (volume : Measure EuclideanSpatial))
  rw [spatialComplexSplit_preserves_volume.map_eq] at hsplit
  have heq : (∫p in cuspEuclideanStrip,g (euclideanToHyperbolic p)/(p 2:ℂ)^3)=
      ∫q in Set.Icc (5:ℝ) 6 ×ˢ periodDomain,g (cuspCoordinateLift q)/(q.1:ℂ)^3 := by
    rw [hsplit]
    simp only [cuspEuclideanStrip,cuspCoordinateLift,spatialComplexSplit.symm_apply_apply,
      spatialComplexSplit_fst]
  rw [heq]
  change (∫q in Set.Icc (5:ℝ) 6 ×ˢ periodDomain,
    g (cuspCoordinateLift q)/(q.1:ℂ)^3 ∂((volume : Measure ℝ).prod volume))=_
  rw [setIntegral_prod _ hint]
  congr 1
  ext v
  exact integral_div ((v:ℂ)^3) (fun z => g (cuspCoordinateLift (v,z)))

lemma hyperbolicEisenstein_continuous (s : ℂ) (hs : 2<s.re) :
    Continuous (hyperbolicEisenstein s) := by
  have hcoord : Continuous (fun p : UpperCoordinates =>
      upperEisenstein p.1.1 p.1.2 p.2 s) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hin : ContinuousAt (fun q : UpperCoordinates => (q,s)) p :=
      continuousAt_id.prodMk continuousAt_const
    exact ContinuousAt.comp (f := fun q : UpperCoordinates => (q,s))
      (upperEisenstein_joint_continuousAt (p,s) hs) hin
  convert hcoord.comp hyperbolicCoordinates_continuous using 1
  ext w
  obtain ⟨z,v,hv,rfl⟩ := upperPoint_surjective w
  simp only [Function.comp_def,hyperbolicEisenstein_upperPoint,hyperbolicCoordinates,
    hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint]

lemma spatialComplexSplit_symm_eq (q : ℝ × ℂ) :
    spatialComplexSplit.symm q=WithLp.toLp 2 ![q.2.re,q.2.im,q.1] := by
  apply spatialComplexSplit.injective
  rw [spatialComplexSplit.apply_symm_apply]
  apply Prod.ext
  · rfl
  · exact (Complex.re_add_im q.2).symm

lemma spatialComplexSplit_symm_continuous : Continuous spatialComplexSplit.symm := by
  change Continuous (fun q : ℝ × ℂ => spatialComplexSplit.symm q)
  simp_rw [spatialComplexSplit_symm_eq]
  fun_prop

lemma cuspCoordinateLift_continuousAt (q : ℝ × ℂ) (hq : 0<q.1) :
    ContinuousAt cuspCoordinateLift q := by
  have hp : 0<(spatialComplexSplit.symm q) 2 := by
    rw [spatialComplexSplit_symm_eq]
    exact hq
  exact (euclideanToHyperbolic_contMDiffAt _ hp).continuousAt.comp
    spatialComplexSplit_symm_continuous.continuousAt

lemma cuspCoordinateLift_weighted_integrable (g : HyperbolicSpace→ℂ) (hg : Continuous g) :
    IntegrableOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
      (Set.Icc (5:ℝ) 6 ×ˢ periodDomain) volume := by
  let radiusBound : ℝ := ∑i,‖periodBasis i‖
  have hc : ContinuousOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
      (Set.Icc (5:ℝ) 6 ×ˢ Metric.closedBall (0:ℂ) radiusBound) := by
    intro q hq
    have hpos : 0<q.1 := lt_of_lt_of_le (by norm_num) hq.1.1
    exact ((hg.continuousAt.comp (cuspCoordinateLift_continuousAt q hpos)).div
      ((Complex.continuous_ofReal.comp continuous_fst).continuousAt.pow 3)
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hpos.ne'))).continuousWithinAt
  apply (hc.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall _ _))).mono_set
  intro q hq
  refine ⟨hq.1,?_⟩
  simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain q.2 hq.2

lemma hyperbolicEisenstein_cusp_average (s : ℂ) (hs : 2<s.re) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume)=
      ∫v in Set.Icc (5:ℝ) 6,
        (((v:ℂ)^s+(v:ℂ)^(2-s)*((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0)*
          ((9*Real.sqrt 3/2:ℝ):ℂ))/(v:ℂ)^3 := by
  rw [cuspPeriodStrip_integral_coordinates _
    (hyperbolicEisenstein_continuous s hs).aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable _ (hyperbolicEisenstein_continuous s hs))]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
  have hh : (∫z in periodDomain,hyperbolicEisenstein s (cuspCoordinateLift (v,z)))=
      eisensteinFourierCoefficient v hpos s 0*((9*Real.sqrt 3/2:ℝ):ℂ) := by
    simp_rw [cuspCoordinateLift_positive v _ hpos,hyperbolicEisenstein_upperPoint]
    rw [eisensteinFourierCoefficient]
    simp only [cuspFrequency,map_zero,zero_div,neg_zero,zero_mul,
      AddChar.map_zero_eq_one,mul_one]
    exact (div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (by positivity))).symm
  dsimp only
  rw [hh,eisensteinConstantCoefficient_formula v hpos s hs]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

def cuspMainHeightFactor (s : ℂ) : ℂ :=
  ((6:ℂ)^(s-2)-(5:ℂ)^(s-2))/(s-2)

def cuspScatterHeightFactor (s : ℂ) : ℂ :=
  ((5:ℂ)^(-s)-(6:ℂ)^(-s))/s

lemma cuspHeightPower_integrable (s : ℂ) :
    IntegrableOn (fun v : ℝ => (v:ℂ)^s) (Set.Icc (5:ℝ) 6) volume := by
  apply ContinuousOn.integrableOn_Icc
  intro v hv
  exact (Complex.continuousAt_ofReal_cpow_const v s (Or.inr (by linarith [hv.1]))).continuousWithinAt

lemma cuspMainHeightFactor_integral (s : ℂ) (hs : s≠2) :
    (∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(s-3))=cuspMainHeightFactor s := by
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (5:ℝ)≤6)]
  have hr : s-3≠(-1:ℂ) := by intro h; apply hs; linear_combination h
  rw [integral_cpow (Or.inr ⟨hr,by norm_num⟩)]
  change ((6:ℂ)^(s-3+1)-(5:ℂ)^(s-3+1))/(s-3+1)=_
  have he : s-3+1=s-2 := by ring
  rw [he]
  rfl

lemma cuspScatterHeightFactor_integral (s : ℂ) (hs : s≠0) :
    (∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-s-1))=cuspScatterHeightFactor s := by
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (5:ℝ)≤6)]
  have hr : -s-1≠(-1:ℂ) := by intro h; apply hs; linear_combination -h
  rw [integral_cpow (Or.inr ⟨hr,by norm_num⟩)]
  change ((6:ℂ)^(-s-1+1)-(5:ℂ)^(-s-1+1))/(-s-1+1)=_
  have he : -s-1+1=-s := by ring
  rw [he,cuspScatterHeightFactor]
  ring

lemma cuspMainHeightFactor_differentiableAt (s : ℂ) (hs : s≠2) :
    DifferentiableAt ℂ cuspMainHeightFactor s := by
  have hd : DifferentiableAt ℂ (fun z : ℂ => z-2) s := differentiableAt_id.sub_const 2
  exact ((hd.const_cpow (Or.inl (by norm_num))).sub
    (hd.const_cpow (Or.inl (by norm_num)))).div hd (sub_ne_zero.mpr hs)

lemma cuspScatterHeightFactor_differentiableAt (s : ℂ) (hs : s≠0) :
    DifferentiableAt ℂ cuspScatterHeightFactor s := by
  have hd : DifferentiableAt ℂ (fun z : ℂ => -z) s := differentiableAt_id.neg
  exact ((hd.const_cpow (Or.inl (by norm_num))).sub
    (hd.const_cpow (Or.inl (by norm_num)))).div differentiableAt_id hs

def cuspConstantAverage (s : ℂ) : ℂ :=
  ((9*Real.sqrt 3/2:ℝ):ℂ)*(cuspMainHeightFactor s+
    ((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0*cuspScatterHeightFactor s)

lemma hyperbolicEisenstein_cusp_average_eq (s : ℂ) (hs : 2<s.re) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume)=
      cuspConstantAverage s := by
  have hs2 : s≠2 := by intro he; subst s; norm_num at hs
  have hs0 : s≠0 := by intro he; subst s; norm_num at hs
  rw [hyperbolicEisenstein_cusp_average s hs]
  have heq : (∫v in Set.Icc (5:ℝ) 6,
      (((v:ℂ)^s+(v:ℂ)^(2-s)*((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0)*
        ((9*Real.sqrt 3/2:ℝ):ℂ))/(v:ℂ)^3)=
      ∫v in Set.Icc (5:ℝ) 6,((9*Real.sqrt 3/2:ℝ):ℂ)*
        ((v:ℂ)^(s-3)+(((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0)*(v:ℂ)^(-s-1)) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith [hv.1])
    have h1 : (v:ℂ)^(s-3)=(v:ℂ)^s/(v:ℂ)^3 := by
      rw [Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    have h2 : (v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3 := by
      rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    dsimp only
    rw [h1,h2]
    ring
  rw [heq,integral_const_mul,integral_add (cuspHeightPower_integrable _)
    ((cuspHeightPower_integrable _).const_mul _),integral_const_mul,
    cuspMainHeightFactor_integral s hs2,cuspScatterHeightFactor_integral s hs0]
  rfl

lemma cuspConstantAverage_differentiableAt (s : ℂ) (hs : 4/3<s.re) (hs2 : s≠2) :
    DifferentiableAt ℂ cuspConstantAverage s := by
  have hs0 : s≠0 := by intro he; subst s; norm_num at hs
  have hs1 : s≠1 := by intro he; subst s; norm_num at hs
  have hsc : DifferentiableAt ℂ (fun z : ℂ => scatteringCoefficient z 0) s :=
    (arithmeticDirichletSeries_zero_differentiableAt s hs).div_const _
  exact ((cuspMainHeightFactor_differentiableAt s hs2).add
    ((((differentiableAt_const (Real.pi:ℂ)).div (differentiableAt_id.sub_const 1)
      (sub_ne_zero.mpr hs1)).mul hsc).mul
      (cuspScatterHeightFactor_differentiableAt s hs0))).const_mul _

lemma cuspScatterHeightFactor_center_re_pos :
    0<(cuspScatterHeightFactor (4/3:ℂ)).re := by
  have h5 := Complex.ofReal_cpow (by norm_num : (0:ℝ)≤5) (-(4/3:ℝ))
  have h6 := Complex.ofReal_cpow (by norm_num : (0:ℝ)≤6) (-(4/3:ℝ))
  norm_num only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat] at h5 h6
  have he : cuspScatterHeightFactor (4/3:ℂ)=
      (((5:ℝ)^(-(4/3:ℝ))-(6:ℝ)^(-(4/3:ℝ)))/(4/3:ℝ):ℝ) := by
    rw [cuspScatterHeightFactor,←h5,←h6]
    push_cast
    rfl
  rw [he,Complex.ofReal_re]
  apply div_pos
  · exact sub_pos.mpr (Real.rpow_lt_rpow_of_neg (by norm_num) (by norm_num) (by norm_num))
  · norm_num

def cuspConstantAverageResidue : ℂ :=
  ((9*Real.sqrt 3/2:ℝ):ℂ)*(3*(Real.pi:ℂ))*constantArithmeticResidue*
    cuspScatterHeightFactor (4/3:ℂ)

lemma cuspConstantAverageResidue_ne_zero : cuspConstantAverageResidue≠0 := by
  apply mul_ne_zero
  · exact mul_ne_zero (mul_ne_zero cusp_volume_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
      constantArithmeticResidue_ne_zero
  · intro he
    have hh := cuspScatterHeightFactor_center_re_pos
    rw [he,Complex.zero_re] at hh
    exact lt_irrefl 0 hh

lemma cuspConstantAverage_oneSidedResidue :
    Tendsto (fun x : ℝ => ((x:ℂ)-(4/3:ℂ))*cuspConstantAverage (x:ℂ))
      (𝓝[>] (4/3:ℝ)) (𝓝 cuspConstantAverageResidue) := by
  have harg : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] (4/3:ℝ)) (𝓝 (4/3:ℂ)) := by
    convert Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 ; norm_num
  have hlinear := harg.sub_const (4/3:ℂ)
  norm_num only [sub_self] at hlinear
  have hm := (cuspMainHeightFactor_differentiableAt (4/3:ℂ) (by norm_num)).continuousAt.tendsto.comp harg
  have hh := (cuspScatterHeightFactor_differentiableAt (4/3:ℂ) (by norm_num)).continuousAt.tendsto.comp harg
  have hpi : Tendsto (fun x : ℝ => (Real.pi:ℂ)/((x:ℂ)-1))
      (𝓝[>] (4/3:ℝ)) (𝓝 (3*(Real.pi:ℂ))) := by
    convert tendsto_const_nhds.div (harg.sub_const 1) (by norm_num : (4/3:ℂ)-1≠0) using 1 ; ring_nf
  have hall := ((hlinear.mul hm).add
    ((hpi.mul scatteringCoefficient_zero_oneSidedResidue).mul hh)).const_mul
      ((9*Real.sqrt 3/2:ℝ):ℂ)
  convert hall using 1
  · ext x
    dsimp only [cuspConstantAverage,Function.comp_def]
    ring
  · simp only [zero_mul,zero_add,cuspConstantAverageResidue]
    ring_nf

open Filter MeasureTheory
open scoped BigOperators Classical Topology

lemma kernelSpectralResolvent_analyticAt_of_isUnit (z : ℂ)
    (hz : IsUnit (kernelSpectralFormOperator z)) :
    AnalyticAt ℂ kernelSpectralResolvent z := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := KernelEnergyGraph→L[ℂ]KernelEnergyGraph)
    (F := KernelQuotientL2→L[ℂ]KernelQuotientL2) kernelL2SandwichCLM
      (Ring.inverse (kernelSpectralFormOperator z))).comp_of_eq
    (kernelSpectralFormInverse_analyticAt_of_isUnit z hz) rfl

lemma kernelEisensteinResolvent_analyticAt_of_isUnit (s : ℂ)
    (hs : IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter s))) :
    AnalyticAt ℂ kernelEisensteinResolvent s := by
  exact (kernelSpectralResolvent_analyticAt_of_isUnit _ hs).comp_of_eq
    (by unfold kernelEisensteinSpectralParameter; fun_prop) rfl

lemma kernelCuspAverageFamily_analyticAt_of_isUnit (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter s))) :
    AnalyticAt ℂ (kernelCuspAverageFamily a b ha hab) s := by
  have hcor : AnalyticAt ℂ (kernelEisensteinL2Correction a b ha hab) s :=
    ((ContinuousLinearMap.apply ℂ KernelQuotientL2).analyticAt_bilinear
      (kernelL2Defect a b ha hab s,kernelEisensteinResolvent s)).comp₂
      ((kernelL2Defect_entire a b ha hab).analyticAt s)
      (kernelEisensteinResolvent_analyticAt_of_isUnit s hs)
  have hlocal : AnalyticAt ℂ
      (kernelLocalCorrectedSeed kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab) s :=
    ((kernelLocalSeedL2_entire kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha).analyticAt s).add
      ((ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := KernelQuotientL2)
        (kernelMassRestrictionCLM kernelCuspAverageCompact kernelCuspAverageCompact_isCompact.measurableSet)
        (kernelEisensteinL2Correction a b ha hab s)).comp_of_eq hcor rfl)
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := ℂ)
    kernelCuspStripAverage _).comp_of_eq hlocal rfl

lemma kernelCuspAverageFamily_analyticAt_nonreal (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelCuspAverageFamily a b ha hab) s :=
  kernelCuspAverageFamily_analyticAt_of_isUnit a b ha hab s
    (kernelSpectralFormOperator_isUnit_nonreal _ (kernelEisensteinSpectralParameter_nonreal s hs hi))

def cuspUpperParameterRegion : Set ℂ := {s | (4/3:ℝ)<s.re ∧ 0<s.im}

lemma cuspUpperParameterRegion_isOpen : IsOpen cuspUpperParameterRegion :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)

lemma cuspUpperParameterRegion_convex : Convex ℝ cuspUpperParameterRegion :=
  ((convex_Ioi (4/3:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
    ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)

lemma cuspConstantAverage_analyticOn_upper : AnalyticOnNhd ℂ cuspConstantAverage cuspUpperParameterRegion := by
  apply (Complex.analyticOnNhd_iff_differentiableOn cuspUpperParameterRegion_isOpen).mpr
  intro s hs
  apply (cuspConstantAverage_differentiableAt s hs.1 ?_).differentiableWithinAt
  intro he
  subst s
  norm_num [cuspUpperParameterRegion] at hs

lemma kernelCuspAverageFamily_eq_upper_of_overlap (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ,4<s.re → 0<s.im →
      kernelCuspAverageFamily a b ha hab s=
        ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume) :
    Set.EqOn (kernelCuspAverageFamily a b ha hab) cuspConstantAverage cuspUpperParameterRegion := by
  have hleft : AnalyticOnNhd ℂ (kernelCuspAverageFamily a b ha hab) cuspUpperParameterRegion := by
    intro s hs
    exact kernelCuspAverageFamily_analyticAt_nonreal a b ha hab s (by linarith [hs.1]) hs.2.ne'
  have hstart : (5+Complex.I:ℂ)∈cuspUpperParameterRegion := by
    norm_num [cuspUpperParameterRegion]
  have hV : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : kernelCuspAverageFamily a b ha hab =ᶠ[𝓝 (5+Complex.I:ℂ)] cuspConstantAverage := by
    filter_upwards [hV.mem_nhds (by norm_num)] with s hs
    exact (hoverlap s hs.1 hs.2).trans (hyperbolicEisenstein_cusp_average_eq s (by linarith [hs.1]))
  exact hleft.eqOn_of_preconnected_of_eventuallyEq cuspConstantAverage_analyticOn_upper
    cuspUpperParameterRegion_convex.isPreconnected hstart hevent

lemma kernelCuspAverageFamily_eq_real_of_upper (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hupper : Set.EqOn (kernelCuspAverageFamily a b ha hab) cuspConstantAverage cuspUpperParameterRegion)
    (x : ℝ) (hx : (4/3:ℝ)<x) (hx2 : x≠2)
    (hunit : IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter (x:ℂ)))) :
    kernelCuspAverageFamily a b ha hab (x:ℂ)=cuspConstantAverage (x:ℂ) := by
  have hpath : Tendsto (fun t : ℝ => (x:ℂ)+(t:ℂ)*Complex.I) (𝓝[>] (0:ℝ)) (𝓝 (x:ℂ)) := by
    have hcont : Continuous (fun t : ℝ => (x:ℂ)+(t:ℂ)*Complex.I) :=
      (Complex.continuous_ofReal.mul_const Complex.I).const_add (x:ℂ)
    have hh := (hcont.tendsto 0).mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
    simpa only [Complex.ofReal_zero,zero_mul,add_zero] using hh
  have hleft := (kernelCuspAverageFamily_analyticAt_of_isUnit a b ha hab (x:ℂ) hunit).continuousAt.tendsto.comp hpath
  have hx2' : (x:ℂ)≠2 := by exact_mod_cast hx2
  have hright := (cuspConstantAverage_differentiableAt (x:ℂ) hx hx2').continuousAt.tendsto.comp hpath
  have hevent : (fun t : ℝ => kernelCuspAverageFamily a b ha hab ((x:ℂ)+(t:ℂ)*Complex.I))
      =ᶠ[𝓝[>] (0:ℝ)] (fun t : ℝ => cuspConstantAverage ((x:ℂ)+(t:ℂ)*Complex.I)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    apply hupper
    simpa only [cuspUpperParameterRegion,Set.mem_ofPred_eq,Complex.add_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.add_im,
      Complex.mul_im,mul_zero,zero_mul,sub_zero,add_zero,zero_add,mul_one] using And.intro hx ht
  exact tendsto_nhds_unique_of_eventuallyEq hleft hright hevent

lemma realAbove_tendsto_complex_punctured :
    Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] (4/3:ℝ)) (𝓝[≠] (4/3:ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · convert Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 ; norm_num
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change (4/3:ℝ)<x at hx
    change (x:ℂ)≠(4/3:ℂ)
    intro he
    have hh := congrArg Complex.re he
    norm_num at hh
    linarith [hx]

lemma kernelEisensteinResidueVector_average_of_overlap (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ,4<s.re → 0<s.im →
      kernelCuspAverageFamily a b ha hab s=
        ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume) :
    kernelCuspStripAverage (kernelEisensteinResidueVector a b ha hab)=cuspConstantAverageResidue := by
  have hupper := kernelCuspAverageFamily_eq_upper_of_overlap a b ha hab hoverlap
  have hleft := (kernelCuspAverageFamily_residue_limit a b ha hab).comp realAbove_tendsto_complex_punctured
  have hunit := realAbove_tendsto_complex_punctured.eventually kernelEisensteinPencil_eventually_isUnit
  have hlt : ∀ᶠx : ℝ in 𝓝[>] (4/3:ℝ),x<2 := by
    have hh : ∀ᶠx : ℝ in 𝓝 (4/3:ℝ),x<2 := Iio_mem_nhds (by norm_num)
    exact hh.filter_mono nhdsWithin_le_nhds
  have hevent : (fun x : ℝ => ((x:ℂ)-4/3)*kernelCuspAverageFamily a b ha hab (x:ℂ))
      =ᶠ[𝓝[>] (4/3:ℝ)] (fun x : ℝ => ((x:ℂ)-4/3)*cuspConstantAverage (x:ℂ)) := by
    filter_upwards [self_mem_nhdsWithin,hunit,hlt] with x hx hux hxx
    rw [kernelCuspAverageFamily_eq_real_of_upper a b ha hab hupper x hx hxx.ne hux]
  exact tendsto_nhds_unique_of_eventuallyEq hleft cuspConstantAverage_oneSidedResidue hevent

lemma kernelEisensteinResidueVector_ne_zero_of_overlap (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ,4<s.re → 0<s.im →
      kernelCuspAverageFamily a b ha hab s=
        ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume) :
    kernelEisensteinResidueVector a b ha hab≠0 := by
  intro he
  have hh := kernelEisensteinResidueVector_average_of_overlap a b ha hab hoverlap
  rw [he,map_zero] at hh
  exact cuspConstantAverageResidue_ne_zero hh.symm

end CubicEisenstein

end

end OAI
end OAIOriginalModule0250

/-! Original module: OAI.NumberTheory.DirichletL.RowCompletion.DensityTransfer
Source SHA256: 07d87a7d25124dde00e884e345083eca072c7bb5cd653db7fa87266ec8b45b4c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0251



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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open ConcreteTraceCRT (eisEmbedding)

theorem canonicalShortState_from_certificate
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : ActualEisensteinCubic.O→*ℂ) (hbase : ∀u,‖base u‖≤1)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S base ρ q levelBound)
    (A : ℝ) (hA : 0≤A) (ε κ : ℝ) (hε : 0<ε) (hκ : 0<κ) :
    ∃d : ℕ,∀(W : ℝ→ℂ),
      Function.support W⊆Set.Icc (Real.exp (-A)) (Real.exp A) → ContDiff ℝ ∞ W →
      ∃C : ℝ,0≤C ∧ ∀(θ Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      1≤Z → Real.exp 9000≤Z → 0≤η → 3000*η≤(1:ℝ)/80 →
      2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) →
      2*X*rowFamilyEnergy labels (fun I z=>shortCompletedSum
        (rowTwist (normHeightTwist Ψ θ) (m*excludedGenerator S) (idealGenerator I) z)
        W X (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0)) K≤
      C*(X*F)^2*Z^(κ+7*ε-(1:ℝ)/40)*(1+|θ|)^d := by
  obtain ⟨d,hshort⟩:=canonicalShortState_uniform_twist
    (Real.exp (-A)) (Real.exp A) (Real.exp_pos _) ε ρ q levelBound hε hρ hq hlevel
  refine ⟨d,?_⟩
  intro W hs hW
  obtain ⟨Cs,hCs,hsbound⟩:=hshort W hs hW
  obtain ⟨Cm,hCm,hm⟩:=hmodels A hA W hs hW κ hκ
  refine ⟨Cs*Cm,mul_nonneg hCs hCm,?_⟩
  intro θ Z η Ψ m labels X F K hstate hZ hZbig hη hbudget hfixed
  by_cases hF : F<Z^((1:ℝ)/1000)
  · have hgeometry:=canonicalShortState_geometry S hSp hbad base Z η Ψ m labels X F K
      hstate hZ hZbig hη hbudget hfixed
    obtain ⟨rays,lengthScale,hsize,hformula⟩:=hm Z K X F θ hZ hstate.row_ge_one hstate.column_pos
      hstate.label_ge_one hF.le Ψ hstate.coefficient m hstate.mask_ne_zero hgeometry.2.2.2.2
    have hb:=hsbound θ rays S hSp hbad base Z η Ψ m labels X F K hstate hbase hZ hZbig
      hη hbudget hfixed lengthScale (fun _=>hformula)
    calc
      _ ≤ (Cs*(1+‖θ‖)^d)*(rays:ℝ)^2*‖lengthScale‖^2*(X*F)^2*Z^(7*ε-(1:ℝ)/40):=hb
      _ = Cs*(1+|θ|)^d*((rays:ℝ)^2*‖lengthScale‖^2)*(X*F)^2*Z^(7*ε-(1:ℝ)/40):=by
        rw [Real.norm_eq_abs]
        ring
      _ ≤ Cs*(1+|θ|)^d*(Cm*Z^κ)*(X*F)^2*Z^(7*ε-(1:ℝ)/40):=by gcongr
      _ = _ := by
        rw [show κ+7*ε-(1:ℝ)/40=κ+(7*ε-(1:ℝ)/40) by ring,
          Real.rpow_add (zero_lt_one.trans_le hZ)]
        ring
  · have hb:=hsbound θ 0 S hSp hbad base Z η Ψ m labels X F K hstate hbase hZ hZbig
      hη hbudget hfixed 0 (fun hf=>False.elim (hF hf))
    have hz : 2*X*rowFamilyEnergy labels (fun I z=>shortCompletedSum
        (rowTwist (normHeightTwist Ψ θ) (m*excludedGenerator S) (idealGenerator I) z)
        W X (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0)) K≤0 := by
      simpa only [Nat.cast_zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero,zero_mul] using hb
    exact hz.trans (by positivity)

end

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation JointLogSeparation
open ConcreteTraceCRT (eisEmbedding)

theorem canonicalLog_actual_step
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : ActualEisensteinCubic.O→*ℂ) (hbase : ∀u,‖base u‖≤1)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S base ρ q levelBound)
    (A : ℝ) (hA : 0≤A) (η : ℝ) (hη : 0<η) (hηsmall : η≤(1:ℝ)/1000)
    (hbudget : 3000*η≤(1:ℝ)/80) :
    ∃d : ℕ,∀J : ℕ,d≤2*J →
    ∃child : Bool→Bool→ℝ→ℂ,
      (∀side neg,ContDiff ℝ ∞ (child side neg)) ∧
      (∀side neg s,child side neg s≠0→|s|≤2*A+11) ∧
      ∀(V : ℝ→ℂ),ContDiff ℝ ∞ V → (∀s,V s≠0→|s|≤A) →
      ∃C : ℝ,0≤C ∧ ∀(D : ℕ) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K E t : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      1<Z → Real.exp 9000≤Z →
      2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) →
      1≤X → Real.exp A*X≤D → 1≤E →
      (∀side neg (Ψ' : ActualEisensteinCubic.O→*ℂ) (m' : ActualEisensteinCubic.O) (labels' : Finset (Ideal ActualEisensteinCubic.O)) (X' F' K' : ℝ),
        CanonicalStateCondition base (∏P∈S,P) Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z K → ∀s : ℝ,
        outsideLogEnergy S D hbad (normHeightTwist Ψ' s) m' labels' (child side neg) X' K'≤
          E*(X'*F')^2*(1+‖s‖)^(2*J)) →
      outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K≤
        C*E*(X*F)^2*Z^(57*η)*(1+|t|)^(2*J) := by
  obtain ⟨d,hshort⟩:=canonicalShortState_from_certificate S hSp hbad base hbase
    ρ q levelBound hρ hq hlevel hmodels A hA η η hη hη
  refine ⟨d,?_⟩
  intro J hJ
  obtain ⟨g,v,hgc,hvc,hgone,hgb,hwin,hvb⟩:=fixed_reopening_profiles A hA
  have hbudget' : 3000*η≤(1:ℝ)/40:=by linarith
  obtain ⟨w₁,w₂,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,hlarge⟩:=
    progressingCanonicalFamily_closed_step g v A (2*A+4) (2*A+5) (by linarith) (by linarith)
      hgb hvb hwin hgone η η η hη hη hη hηsmall hbudget' J
  let child : Bool→Bool→ℝ→ℂ:=fun side neg=>
    orientedLogProfile neg ((if side then w₁ else w₂) (if neg then 5 else 6))
  have hcs : ∀side neg,ContDiff ℝ ∞ (child side neg) := by
    intro side neg
    cases side <;> cases neg
    · exact hws₂ 6
    · exact Complex.conjCLE.contDiff.comp (hws₂ 5)
    · exact hws₁ 6
    · exact Complex.conjCLE.contDiff.comp (hws₁ 5)
  have hcb : ∀side neg s,child side neg s≠0→|s|≤2*A+11 := by
    intro side neg s hn
    have hnorm (w : Fin 7→ℝ→ℂ) (hw : ∀i t,w i t≠0→|t|≤(2*A+4)+7)
        (i : Fin 7) (hi : w i s≠0) : |s|≤2*A+11 := by
      have hh:=hw i s hi
      linarith
    cases side <;> cases neg
    · exact hnorm w₂ hwb₂ 6 hn
    · apply hnorm w₂ hwb₂ 5
      intro hz
      exact hn (by simp [child,orientedLogProfile,hz])
    · exact hnorm w₁ hwb₁ 6 hn
    · apply hnorm w₁ hwb₁ 5
      intro hz
      exact hn (by simp [child,orientedLogProfile,hz])
  refine ⟨child,hcs,hcb,?_⟩
  intro V hVs hV
  let W : ℝ→ℂ:=radialFromLog V hVs A hV
  have hW : ContDiff ℝ ∞ W:=(radialFromLog V hVs A hV).smooth ⊤
  have hs : Function.support W⊆Set.Icc (Real.exp (-A)) (Real.exp A):=
    fun s hs=>radialFromLog_support V hVs A hV s hs
  obtain ⟨Cs,hCs,hsmall⟩:=hshort W hs hW
  obtain ⟨Cl,hCl,hlong⟩:=hlarge W hs hW (radialFromLog_hasCompactSupport V hVs A hV)
  refine ⟨Cs+Cl,add_nonneg hCs hCl,?_⟩
  intro D Z Ψ m labels X F K E t hstate hZ hZbig hfixed hX hD hE ih
  obtain ⟨hXZ,hFZ⟩:=canonical_live_scale_bounds Z X F (fixedDepthRank Z K)
    hZbig hX hstate.label_ge_one hstate.mass_le
  have hsbound:=hsmall t Z η Ψ m labels X F K hstate hZ.le hZbig hη.le hbudget hfixed
  have hb:=hlong S D hbad hSp base Z Ψ m labels X F K E t hstate hbase hZ hZbig
    hX hXZ hFZ hE hD
  dsimp only at hb
  have hlbound:=hb (by
    intro side Ψ' m' labels' X' F' K' hs' hr s
    exact ⟨ih side true Ψ' m' labels' X' F' K' hs' hr s,
      ih side false Ψ' m' labels' X' F' K' hs' hr s⟩)
  have he : η+17*η+39*η=57*η:=by ring
  rw [he] at hlbound
  have hp : Z^(η+7*η-(1:ℝ)/40)≤Z^(57*η):=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have ht : (1+|t|)^d≤(1+|t|)^(2*J):=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hJ
  have hs' : 2*X*rowFamilyEnergy labels (fun I z=>shortCompletedSum
      (rowTwist (normHeightTwist Ψ t) (m*excludedGenerator S) (idealGenerator I) z)
      W X (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0)) K≤
      Cs*E*(X*F)^2*Z^(57*η)*(1+|t|)^(2*J) := by
    calc
      _ ≤ Cs*(X*F)^2*Z^(η+7*η-(1:ℝ)/40)*(1+|t|)^d:=hsbound
      _ ≤ Cs*(X*F)^2*Z^(57*η)*(1+|t|)^(2*J):=by gcongr
      _ ≤ (Cs*(X*F)^2*Z^(57*η)*(1+|t|)^(2*J))*E:=
        le_mul_of_one_le_right (by positivity) hE
      _ = _:=by ring
  rw [outsideLogEnergy_eq_completed S D hbad (normHeightTwist Ψ t) m labels V hVs A hV X K hstate.column_pos]
  exact hlbound.trans ((add_le_add hs' le_rfl).trans_eq (by ring))

end

open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation
open ConcreteTraceCRT (eisEmbedding)

theorem outsideLogEnergy_finite_rank
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : ActualEisensteinCubic.O→*ℂ) (hbase : ∀u,‖base u‖≤1)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S base ρ q levelBound)
    (η : ℝ) (hη : 0<η) (hηsmall : η≤(1:ℝ)/1000)
    (hbudget : 3000*η≤(1:ℝ)/80) (r : ℕ) :
    ∀(A : ℝ),0≤A → ∃d : ℕ,∀(V : ℝ→ℂ),ContDiff ℝ ∞ V →
    (∀s,V s≠0→|s|≤A) → ∃C : ℝ,1≤C ∧
    ∀(D : ℕ) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O))
      (X F K t : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      1<Z → Real.exp 9000≤Z →
      2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) →
      fixedDepthRank Z K≤r → Real.exp (radiusIter A r)*Z^3≤D →
      outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K≤
        C*Z^(57*η*(r:ℝ))*(X*F)^2*(1+|t|)^d := by
  have hbudget' : 3000*η≤(1:ℝ)/40:=by linarith
  induction r with
  | zero =>
    intro A hA
    refine ⟨0,?_⟩
    intro V hVs hV
    obtain ⟨C,hC,hterm⟩:=outsideLogEnergy_terminal_constant V hVs A hV
    refine ⟨max 1 C,le_max_left _ _,?_⟩
    intro D Z Ψ m labels X F K t hstate hZ hZbig hfixed hr hD
    have hb:=hterm S D hbad base Z η Ψ m labels X F K t hstate hbase hZ hη.le hbudget'
      (Or.inl (Nat.eq_zero_of_le_zero hr))
    simpa only [Nat.cast_zero,mul_zero,Real.rpow_zero,mul_one,pow_zero] using
      hb.trans (mul_le_mul_of_nonneg_right (le_max_right 1 C) (sq_nonneg (X*F)))
  | succ r ih =>
    intro A hA
    obtain ⟨dc,hchild⟩:=ih (2*A+11) (by linarith)
    obtain ⟨ds,hstep⟩:=canonicalLog_actual_step S hSp hbad base hbase ρ q levelBound
      hρ hq hlevel hmodels A hA η hη hηsmall hbudget
    let J : ℕ:=dc+ds
    have hdchild : dc≤2*J:=by dsimp [J];omega
    have hdstep : ds≤2*J:=by dsimp [J];omega
    obtain ⟨child,hcs,hcb,hparent⟩:=hstep J hdstep
    choose childC hchildC using (fun side neg=>hchild (child side neg) (hcs side neg) (hcb side neg))
    have hcnonneg (side neg : Bool) : 0≤childC side neg:=zero_le_one.trans (hchildC side neg).1
    let E0 : ℝ:=1+∑side : Bool,∑neg : Bool,childC side neg
    have hE0 : 1≤E0:=by
      have hs : 0≤∑side : Bool,∑neg : Bool,childC side neg:=
        Finset.sum_nonneg (fun side _=>Finset.sum_nonneg (fun neg _=>hcnonneg side neg))
      exact le_add_of_nonneg_right hs
    have hcE (side neg : Bool) : childC side neg≤E0:=by
      have h1 : childC side neg≤∑j : Bool,childC side j:=
        Finset.single_le_sum (fun j _=>hcnonneg side j) (Finset.mem_univ neg)
      have h2 : (∑j : Bool,childC side j)≤∑i : Bool,∑j : Bool,childC i j:=
        Finset.single_le_sum (fun i _=>Finset.sum_nonneg (fun j _=>hcnonneg i j)) (Finset.mem_univ side)
      exact h1.trans (h2.trans (le_add_of_nonneg_left zero_le_one))
    refine ⟨2*J,?_⟩
    intro V hVs hV
    obtain ⟨Ct,hCt,hterm⟩:=outsideLogEnergy_terminal_constant V hVs A hV
    obtain ⟨Cp,hCp,hp⟩:=hparent V hVs hV
    let C : ℝ:=1+Ct+Cp*E0
    have hC : 1≤C:=by dsimp [C];nlinarith [mul_nonneg hCp (zero_le_one.trans hE0)]
    have htC : Ct≤C:=by dsimp [C];nlinarith [mul_nonneg hCp (zero_le_one.trans hE0)]
    have hpC : Cp*E0≤C:=by dsimp [C];linarith
    refine ⟨C,hC,?_⟩
    intro D Z Ψ m labels X F K t hstate hZ hZbig hfixed hr hD
    have hZ0 : 0<Z:=zero_lt_one.trans hZ
    have hpow : 1≤Z^(57*η*((r+1:ℕ):ℝ)):=
      Real.one_le_rpow hZ.le (by positivity)
    have hheight : 1≤(1+|t|)^(2*J):=one_le_pow₀ (by linarith [abs_nonneg t])
    by_cases hstop : fixedDepthRank Z K=0 ∨ X≤1
    · have hb:=hterm S D hbad base Z η Ψ m labels X F K t hstate hbase hZ hη.le hbudget' hstop
      apply hb.trans
      calc
        Ct*(X*F)^2≤C*(X*F)^2:=mul_le_mul_of_nonneg_right htC (sq_nonneg _)
        _ ≤ C*Z^(57*η*((r+1:ℕ):ℝ))*(X*F)^2*(1+|t|)^(2*J):=by
          calc
            _ ≤ (C*(X*F)^2)*Z^(57*η*((r+1:ℕ):ℝ)):=
              le_mul_of_one_le_right (by positivity) hpow
            _ ≤ ((C*(X*F)^2)*Z^(57*η*((r+1:ℕ):ℝ)))*(1+|t|)^(2*J):=
              le_mul_of_one_le_right (by positivity) hheight
            _ = _:=by ring
    · have hX : 1≤X:=(lt_of_not_ge (fun hh=>hstop (Or.inr hh))).le
      have hXZ : X≤Z^3:=(canonical_live_scale_bounds Z X F (fixedDepthRank Z K)
        hZbig hX hstate.label_ge_one hstate.mass_le).1
      have hDparent : Real.exp A*X≤D:=
        common_pool_parent A Z X D (r+1) hA hZ0.le hstate.column_pos.le hXZ hD
      let E : ℝ:=E0*Z^(57*η*(r:ℝ))
      have hEr : 1≤Z^(57*η*(r:ℝ)):=Real.one_le_rpow hZ.le (by positivity)
      have hE : 1≤E:=by
        change 1≤E0*Z^(57*η*(r:ℝ))
        simpa only [one_mul] using mul_le_mul hE0 hEr zero_le_one (zero_le_one.trans hE0)
      have hb:=hp D Z Ψ m labels X F K E t hstate hZ hZbig hfixed hX hDparent hE
      have hbound : outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K≤
          Cp*E*(X*F)^2*Z^(57*η)*(1+|t|)^(2*J):=hb (by
        intro side neg Ψ' m' labels' X' F' K' hs hr' s
        have hrchild : fixedDepthRank Z K'≤r:=by omega
        have hDchild : Real.exp (radiusIter (2*A+11) r)*Z^3≤D:=by
          simpa only [radiusIter_succ] using hD
        have hh:=(hchildC side neg).2 D Z Ψ' m' labels' X' F' K' s hs hZ hZbig hfixed hrchild hDchild
        apply hh.trans
        rw [Real.norm_eq_abs]
        change childC side neg*Z^(57*η*(r:ℝ))*(X'*F')^2*(1+|s|)^dc≤_
        have hcscale : childC side neg*Z^(57*η*(r:ℝ))*(X'*F')^2≤
            (E0*Z^(57*η*(r:ℝ)))*(X'*F')^2:=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hcE side neg) (Real.rpow_nonneg hZ0.le _)) (sq_nonneg _)
        have hheight' : (1+|s|)^dc≤(1+|s|)^(2*J):=
          pow_le_pow_right₀ (by linarith [abs_nonneg s]) hdchild
        exact mul_le_mul hcscale hheight' (by positivity) (by positivity))
      apply hbound.trans
      have hexp : Z^(57*η*(r:ℝ))*Z^(57*η)=Z^(57*η*((r+1:ℕ):ℝ)):=by
        rw [←Real.rpow_add hZ0]
        congr 1
        push_cast
        ring
      calc
        Cp*E*(X*F)^2*Z^(57*η)*(1+|t|)^(2*J)=
            (Cp*E0)*(Z^(57*η*(r:ℝ))*Z^(57*η))*(X*F)^2*(1+|t|)^(2*J):=by dsimp [E];ring
        _ = (Cp*E0)*Z^(57*η*((r+1:ℕ):ℝ))*(X*F)^2*(1+|t|)^(2*J):=by rw [hexp]
        _ ≤ _:=by gcongr

def canonicalDescentPadding (ε : ℝ) : ℝ:=canonicalPadding ε 57/2

theorem canonicalDescentPadding_budget (ε : ℝ) (hε : 0<ε) :
    0<canonicalDescentPadding ε ∧ canonicalDescentPadding ε≤(1:ℝ)/1000 ∧
    3000*canonicalDescentPadding ε≤(1:ℝ)/80 ∧
    171000*canonicalDescentPadding ε≤ε := by
  have h:=canonicalPadding_budget ε 57 hε (by norm_num)
  dsimp [canonicalDescentPadding]
  refine ⟨by linarith [h.1],by linarith [h.2.1],by linarith [h.2.2.1],?_⟩
  have ht:=h.2.2.2.2.1
  nlinarith [h.1]

theorem outsideLogEnergy_state_small_power
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : ActualEisensteinCubic.O→*ℂ) (hbase : ∀u,‖base u‖≤1)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S base ρ q levelBound)
    (ε η : ℝ) (hη : 0<η) (hηsmall : η≤(1:ℝ)/1000)
    (hbudget : 3000*η≤(1:ℝ)/80) (hloss : 171000*η≤ε)
    (A : ℝ) (hA : 0≤A) :
    ∃d : ℕ,∀(V : ℝ→ℂ),ContDiff ℝ ∞ V → (∀s,V s≠0→|s|≤A) →
    ∃C : ℝ,1≤C ∧ ∀(D : ℕ) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K t : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      1<Z → Real.exp 9000≤Z →
      2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) →
      Real.exp (radiusIter A 3000)*Z^3≤D →
      outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K≤
        C*Z^ε*(X*F)^2*(1+|t|)^d := by
  obtain ⟨d,hd⟩:=outsideLogEnergy_finite_rank S hSp hbad base hbase ρ q levelBound
    hρ hq hlevel hmodels η hη hηsmall hbudget 3000 A hA
  refine ⟨d,?_⟩
  intro V hVs hV
  obtain ⟨C,hC,hbound⟩:=hd V hVs hV
  refine ⟨C,hC,?_⟩
  intro D Z Ψ m labels X F K t hstate hZ hZbig hfixed hD
  have hr:=fixedDepthRank_initial Z K hZ (zero_lt_one.trans_le hstate.row_ge_one) hstate.row_le_global
  have hb:=hbound D Z Ψ m labels X F K t hstate hZ hZbig hfixed hr hD
  have he : 57*η*(3000:ℝ)≤ε:=by linarith
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le he) (zero_le_one.trans hC)

theorem outsideLogEnergy_small_power
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : ActualEisensteinCubic.O→*ℂ) (hbase : ∀u,‖base u‖≤1)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S base ρ q levelBound)
    (ε : ℝ) (hε : 0<ε) (A : ℝ) (hA : 0≤A) :
    ∃d : ℕ,∀(V : ℝ→ℂ),ContDiff ℝ ∞ V → (∀s,V s≠0→|s|≤A) →
    ∃C : ℝ,1≤C ∧ ∀(D : ℕ) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K t : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z (canonicalDescentPadding ε) Ψ m labels X F K →
      1<Z → Real.exp 9000≤Z →
      2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) →
      Real.exp (radiusIter A 3000)*Z^3≤D →
      outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K≤
        C*Z^ε*(X*F)^2*(1+|t|)^d := by
  have h:=canonicalDescentPadding_budget ε hε
  exact outsideLogEnergy_state_small_power S hSp hbad base hbase ρ q levelBound hρ hq hlevel hmodels
    ε (canonicalDescentPadding ε) h.1 h.2.1 h.2.2.1 h.2.2.2 A hA

end CanonicalRowCompletion

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels (primeProductNorm)
open InitialMeanSquare hiding O
open CanonicalCoefficientClass (IsBaseRayTwist)
open ConcreteTraceCRT (eisEmbedding)

theorem initialCanonicalState
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (base Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : IsBaseRayTwist base Ψ) (Z η X lengthScale K : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hX : 1≤X) (hL : 1≤lengthScale) (hK : 1≤K)
    (R : Finset (OutsidePrimeIndex S D)) (T : Finset (Ideal ActualEisensteinCubic.O×ActualEisensteinCubic.O))
    (hmass : X*lengthScale≤Z^2)
    (hinv : K*(initialExcludedNorm S*primeProductNorm (outsidePrime S D) R)≤
      X*lengthScale*Z^(-(1:ℝ)/20))
    (hlabels : ∀z∈T,Admissible z.1 ∧ (Ideal.absNorm z.1:ℝ)≤lengthScale)
    (houtside : ∀z∈T,IsCoprime z.1 (∏P∈S,P)) :
    CanonicalStateCondition base (∏P∈S,P) Z η Ψ
      (primeSubsetGenerator (fun i=>Ideal.span {outsidePrime S D i}) R)
      (T.image Prod.fst) X lengthScale K := by
  let p:=outsidePrime S D
  have hp:=outsidePrime_ne_zero S hbad D
  let:=outsidePrime_maximal S hbad D
  have hN : 1≤primeProductNorm p R:=primeProductNorm_ge_one p hp R
  have hN0 : 0≤primeProductNorm p R:=zero_le_one.trans hN
  have hmod : 1 ≤ initialExcludedNorm S*primeProductNorm p R:=
    one_le_mul_of_one_le_of_one_le (initialExcludedNorm_ge_one S) hN
  have hdecay : Z^(-(1:ℝ)/20)≤1:=by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hZ (by norm_num : -(1:ℝ)/20≤0)
  have hKmass : K≤X*lengthScale := by
    calc
      K ≤ K*(initialExcludedNorm S*primeProductNorm p R):=
        le_mul_of_one_le_right (zero_le_one.trans hK) hmod
      _ ≤ X*lengthScale*Z^(-(1:ℝ)/20):=hinv
      _ ≤ X*lengthScale:=mul_le_of_le_one_right (by positivity) hdecay
  have hKg : K≤Z^3 :=
    (hKmass.trans hmass).trans (pow_le_pow_right₀ hZ (by decide : (2:ℕ)≤3))
  refine ⟨hΨ,primeSubsetGenerator_ne_zero _ _,by linarith,hL,hK,hKg,
    hmass.trans (canonicalRankMass_initial Z _),?_,?_⟩
  · rw [primeSubsetGenerator_norm_eq_productNorm]
    calc
      K*primeProductNorm p R ≤ K*(initialExcludedNorm S*primeProductNorm p R) := by
        apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hK)
        exact le_mul_of_one_le_left hN0 (initialExcludedNorm_ge_one S)
      _ ≤ X*lengthScale*Z^(-(1:ℝ)/20):=hinv
      _ ≤ X*lengthScale*Z^(-canonicalRankMargin ((1:ℝ)/20) η (fixedDepthRank Z K)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le hZ
        unfold canonicalRankMargin
        have hn : 0≤η*((3000-fixedDepthRank Z K:ℕ):ℝ):=mul_nonneg hη (Nat.cast_nonneg _)
        linarith
  · intro I hI
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hI
    exact ⟨(hlabels z hz).1.1,(hlabels z hz).1.2.1,houtside z hz,(hlabels z hz).2⟩

theorem canonicalInitialThreshold (S : Finset (Ideal ActualEisensteinCubic.O)) :
    ∃Z₀ : ℝ,1≤Z₀ ∧ ∀Z : ℝ,Z₀≤Z →
      1<Z ∧ Real.exp 9000≤Z ∧
      2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) := by
  let c:=2*‖eisEmbedding (excludedGenerator S)‖^2
  let Z₀:=2+Real.exp 9000+c^80
  have hc : 0≤c:=by dsimp only [c];positivity
  have hp : 0≤c^80:=pow_nonneg hc _
  have he:=Real.exp_pos (9000:ℝ)
  refine ⟨Z₀,by dsimp only [Z₀];linarith,?_⟩
  intro Z hZ
  have hZ1 : 1<Z:=by dsimp only [Z₀] at hZ;linarith
  refine ⟨hZ1,by dsimp only [Z₀] at hZ;linarith,?_⟩
  have hpow : c^80≤Z:=by dsimp only [Z₀] at hZ;linarith
  have hh := (Real.le_rpow_inv_iff_of_pos hc (by linarith : 0≤Z) (by norm_num : (0:ℝ)<80)).mpr
    (show c^(80:ℝ)≤Z by simpa only [Real.rpow_ofNat] using hpow)
  simpa only [one_div] using hh

end CanonicalRowCompletion

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic ConcreteTraceCRT

theorem densityChildEnergy_from_canonical_heights {ι : Type*} [DecidableEq ι]
    (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i})
    (pool : Finset ι) (Ψ₁ Ψ₂ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
    (T : Finset (Ideal ActualEisensteinCubic.O×ActualEisensteinCubic.O)) (labels : Finset (Ideal ActualEisensteinCubic.O)) (V₁ V₂ : ℝ→ℂ)
    (X F K E : ℝ) (J : ℕ) (hX : 0<X) (hK : 0<K) (hE : 0≤E)
    (hlabels : ∀z∈T,z.1∈labels) (hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K)
    (hzero : ∀z∈T,z.2≠0)
    (h₁ : ∀t,canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ₁ t) m labels
      (orientedLogProfile true V₁) X K≤E*(X*F)^2*(1+‖t‖)^(2*J))
    (h₂ : ∀t,canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ₂ t) m labels
      (orientedLogProfile false V₂) X K≤E*(X*F)^2*(1+‖t‖)^(2*J)) :
    densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J)≤
      6*E*(X*F)^2*(∫t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t)^3 := by
  have hl (a : ℝ) : childEnergy p hp hcop hg pool Ψ₁ m T V₁ X true false a 0≤
      (6*E*(X*F)^2)*(1+‖a‖)^(2*J) := by
    have hh:=childEnergy_le_canonicalLogEnergy p hp hcop hg pool Ψ₁ m
      T labels V₁ X K a 0 hX hK true false hlabels hrows hzero
    simp only [secondSignedHeight,ite_true,zero_sub] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (h₁ (-a)) (by norm_num : (0:ℝ)≤6)).trans_eq
      (by rw [norm_neg];ring))
  have hr (a : ℝ) : childEnergy p hp hcop hg pool Ψ₂ m T V₂ X false true a 0≤
      (6*E*(X*F)^2)*(1+‖a‖)^(2*J) := by
    have hh:=childEnergy_le_canonicalLogEnergy p hp hcop hg pool Ψ₂ m
      T labels V₂ X K a 0 hX hK false true hlabels hrows hzero
    simp only [secondSignedHeight,Bool.false_eq_true,ite_false,sub_zero] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (h₂ a) (by norm_num : (0:ℝ)≤6)).trans_eq (by ring))
  have hb : 0≤6*E*(X*F)^2:=by positivity
  have hd:=densityChildEnergy_polynomial_bound p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X J
    (6*E*(X*F)^2) (6*E*(X*F)^2) hb hb hl hr
  rwa [Real.mul_self_sqrt hb] at hd

end SecondPassIntegration
end

open scoped BigOperators Classical
namespace QuadraticAllOddCRT
open ActualEisensteinCubic
open QuadraticGaussRay hiding O
open ActualEisensteinCoordinates hiding O
open FiniteGaussPhase hiding O

theorem quadratic_ray_cross (a b : ActualEisensteinCubic.O) (ha : a≠0) (hb : b≠0)
    [(Ideal.span {a}).IsMaximal] [(Ideal.span {b}).IsMaximal]
    (hab : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    (hca : ringChar (ActualEisensteinCubic.O⧸Ideal.span {a})≠2)
    (hcb : ringChar (ActualEisensteinCubic.O⧸Ideal.span {b})≠2) :
    quadraticRayValue (residue (a*b))=
      character (Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) b)*
      character (Ideal.span {b}) (Ideal.Quotient.mk (Ideal.span {b}) a)*
      quadraticRayValue (residue a)*quadraticRayValue (residue b) := by
  let p : Bool→ActualEisensteinCubic.O:=fun i=>if i then a else b
  have hp : ∀i,p i≠0:=by
    intro i
    cases i
    · exact hb
    · exact ha
  let (i : Bool) : (Ideal.span {p i}).IsMaximal := by
    cases i <;> dsimp [p] <;> infer_instance
  have hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})) := by
    intro i j hij
    cases i <;> cases j <;> simp_all [p,Function.onFun,isCoprime_comm]
  have hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2 := by
    intro i
    cases i
    · exact hcb
    · exact hca
  have h:=quadraticGamma_product p hp hcop hc
  simp only [quadraticGammaO_eq_rayValue] at h
  have ht : cofactor p true=b:=by
    apply mul_left_cancel₀ ha
    simpa [p] using prime_mul_cofactor p true
  have hf : cofactor p false=a:=by
    apply mul_left_cancel₀ hb
    simpa [p,mul_comm] using prime_mul_cofactor p false
  simp only [Fintype.prod_bool,ht,hf] at h
  simpa [p,mul_comm,mul_left_comm,mul_assoc] using h

theorem quadraticRayValue_ne_zero_of_odd (r : EisensteinEPrimaryPhase.Coord)
    (hr : EisensteinEPrimaryPhase.odd r) : quadraticRayValue r≠0 := by
  rcases r with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [EisensteinEPrimaryPhase.odd,quadraticRayValue,breveGaussianFourTerms_formula,
      zpow_neg,Complex.I_sq,Complex.I_pow_three,Complex.inv_I,ZMod.val] at * <;>
      intro h <;> solve | (have hh:=congrArg Complex.re h; norm_num at hh) | (have hh:=congrArg Complex.im h; norm_num at hh)

end QuadraticAllOddCRT

end

end OAI
end OAIOriginalModule0251

/-! Original module: OAI.NumberTheory.DirichletL.RowCompletion.InitialDensity
Source SHA256: 78d0b56e675d445e1c62a0d2647b6f69d5aa659d004318669ad1ef3e299ab82f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0252



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

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open SecondPassIntegration hiding O
open InitialMeanSquare hiding O
open CanonicalCubeSeparation
open CanonicalCoefficientClass (IsBaseRayTwist)
open FirstPassCubeLabels (primeProductNorm firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)

theorem hasInitialCanonicalDensityAtRadius_of_theta {q₀ : ℕ}
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound) :
    HasInitialCanonicalDensityAtRadius χ S hbad := by
  intro deltaLoss hδ P A hA
  let base:=conjugateMonoid (normCharacter χ)
  have hbase : ∀u,‖base u‖≤1:=conjugateMonoid_norm_le_one (normCharacter χ) (normCharacter_norm_le_one χ)
  obtain ⟨d,henergy⟩:=outsideLogEnergy_small_power S hSp hbad base hbase
    ρ q levelBound hρ hq hlevel hmodels deltaLoss hδ A hA
  refine ⟨d,?_⟩
  intro V₁ V₂ hVc₁ hVc₂ hVs₁ hVs₂ hV₁ hV₂
  have hs₁ : ContDiff ℝ ∞ (orientedLogProfile true V₁):=Complex.conjCLE.contDiff.comp hVs₁
  have hb₁ : ∀s,orientedLogProfile true V₁ s≠0→|s|≤A := by
    intro s hs
    apply hV₁ s
    intro hz
    exact hs (by simp [orientedLogProfile,hz])
  obtain ⟨C₁,hC₁,he₁⟩:=henergy (orientedLogProfile true V₁) hs₁ hb₁
  obtain ⟨C₂,hC₂,he₂⟩:=henergy (orientedLogProfile false V₂) hVs₂ hV₂
  obtain ⟨A',Vmax,hA',hVmax,hbV₁,hbV₂,hsV₁,hsV₂⟩:=
    initial_two_windows_bounded V₁ V₂ hVc₁ hVc₂ hVs₁.continuous hVs₂.continuous
  obtain ⟨Z₀,hZ₀,hthreshold⟩:=canonicalInitialThreshold S
  let I₀:=∫t : ℝ,firstLogDensity 0 t
  have hI₀ : 0≤I₀:=integral_nonneg (fun t=>FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  let Ccan:=6*(C₁+C₂)*I₀^3
  let Cele:=initialElementaryConstant A' Vmax*I₀^3
  let C:=Ccan+Cele*Z₀^3+1
  have hCcan : 0≤Ccan:=by dsimp only [Ccan];positivity
  have hCele : 0≤Cele:=mul_nonneg (initialElementaryConstant_nonneg A' Vmax) (pow_nonneg hI₀ _)
  have hC : 0<C:=by dsimp only [C];positivity
  have hcanC : Ccan≤C:=by
    have hp : 0≤Cele*Z₀^3:=by positivity
    dsimp only [C]
    linarith
  have heleC : Cele*Z₀^3≤C:=by
    dsimp only [C]
    linarith
  let Cpool:=Real.exp (radiusIter A 3000)
  refine ⟨C,Cpool,max P 3,hC,Real.one_le_exp (radiusIter_nonneg A hA 3000),le_max_left _ _,?_⟩
  intro D Z X lengthScale K R ray T hZ hpool hX hL hK hXP hLP hKP hRP hmass hinv hT hout
  let p:=outsidePrime S D
  let hp:=outsidePrime_ne_zero S hbad D
  let hcop:=outsidePrime_coprime S hbad D
  let hg:=outsidePrime_good S hbad D
  let:=outsidePrime_maximal S hbad D
  let Ψ₁:=secondRayMinus base ray
  let Ψ₂:=secondRayPlus base ray
  let m:=primeSubsetGenerator (fun i=>Ideal.span {p i}) R
  let labels:=T.image Prod.fst
  have hmember : IsBaseRayTwist base base:=Or.inl rfl
  have hη : 0≤canonicalDescentPadding deltaLoss:=(canonicalDescentPadding_budget deltaLoss hδ).1.le
  have hstate₁ := initialCanonicalState S D hbad base Ψ₁ (hmember.secondMinus ray)
    Z (canonicalDescentPadding deltaLoss) X lengthScale K hZ hη hX hL hK R T hmass hinv
    (fun z hz=>⟨(hT z hz).1,(hT z hz).2.1⟩) hout
  have hstate₂ := initialCanonicalState S D hbad base Ψ₂ (hmember.secondPlus ray)
    Z (canonicalDescentPadding deltaLoss) X lengthScale K hZ hη hX hL hK R T hmass hinv
    (fun z hz=>⟨(hT z hz).1,(hT z hz).2.1⟩) hout
  have hZδ : 1≤Z^deltaLoss:=Real.one_le_rpow hZ hδ.le
  have hD : Real.exp (radiusIter A 3000)*Z^3≤D :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hZ (le_max_right P 3)) (Real.exp_pos _).le).trans hpool
  have hlabels : ∀z∈T,z.1∈labels:=fun z hz=>Finset.mem_image.mpr ⟨z,hz,rfl⟩
  have hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K:=fun z hz=>(hT z hz).2.2.2
  have hzero : ∀z∈T,z.2≠0:=fun z hz=>(hT z hz).2.2.1
  by_cases hlarge : Z₀≤Z
  · obtain ⟨hZgt,hZbig,hfixed⟩:=hthreshold Z hlarge
    have hleft (t : ℝ) : canonicalLogEnergy p hp hcop hg Finset.univ
        (normHeightTwist Ψ₁ t) m labels (orientedLogProfile true V₁) X K≤
        ((C₁+C₂)*Z^deltaLoss)*(X*lengthScale)^2*(1+‖t‖)^(2*d) := by
      have hh:=he₁ D Z Ψ₁ m labels X lengthScale K t hstate₁ hZgt hZbig hfixed hD
      change canonicalLogEnergy p hp hcop hg Finset.univ (normHeightTwist Ψ₁ t) m labels
        (orientedLogProfile true V₁) X K≤_ at hh
      apply hh.trans
      rw [Real.norm_eq_abs]
      gcongr
      · linarith
      · linarith [abs_nonneg t]
      · omega
    have hright (t : ℝ) : canonicalLogEnergy p hp hcop hg Finset.univ
        (normHeightTwist Ψ₂ t) m labels (orientedLogProfile false V₂) X K≤
        ((C₁+C₂)*Z^deltaLoss)*(X*lengthScale)^2*(1+‖t‖)^(2*d) := by
      have hh:=he₂ D Z Ψ₂ m labels X lengthScale K t hstate₂ hZgt hZbig hfixed hD
      change canonicalLogEnergy p hp hcop hg Finset.univ (normHeightTwist Ψ₂ t) m labels
        (orientedLogProfile false V₂) X K≤_ at hh
      apply hh.trans
      rw [Real.norm_eq_abs]
      gcongr
      · linarith
      · linarith [abs_nonneg t]
      · omega
    have hd:=densityChildEnergy_from_canonical_heights p hp hcop hg Finset.univ Ψ₁ Ψ₂ m T labels
      V₁ V₂ X lengthScale K ((C₁+C₂)*Z^deltaLoss) d (by linarith) (by linarith) (by positivity)
      hlabels hrows hzero hleft hright
    change outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X d≤_ at hd
    have hcan : outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X d≤Ccan*Z^deltaLoss*(X*lengthScale)^2 := by
      convert hd using 1 ; dsimp only [Ccan,I₀] ; ring
    exact hcan.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcanC (Real.rpow_nonneg (by linarith) _)) (sq_nonneg _))
  · have hKcap : K≤Z₀^3:=hstate₁.row_le_global.trans
      (pow_le_pow_left₀ (by linarith) (le_of_not_ge hlarge) 3)
    have hΨ₁ : ∀u,‖Ψ₁ u‖≤1:=fun u=>(secondRayMinus_norm_le base ray u).trans (hbase u)
    have hΨ₂ : ∀u,‖Ψ₂ u‖≤1:=fun u=>(secondRayPlus_norm_le base ray u).trans (hbase u)
    have hd:=initial_density_elementary_squared_mass p hp hcop hg (outsidePrime_odd S hbad D)
      (outsidePrime_injective S hbad D) Finset.univ Ψ₁ Ψ₂ hΨ₁ hΨ₂ m T V₁ V₂
      X lengthScale K A' Vmax d (by linarith) hL hK hA' hVmax hbV₁ hbV₂ hsV₁ hsV₂
      (fun z hz=>⟨(hT z hz).1.1,(hT z hz).2.1,(hT z hz).2.2.2⟩)
    change outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X d≤Cele*K*(X*lengthScale)^2 at hd
    apply hd.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact (mul_le_mul_of_nonneg_left hKcap hCele).trans
      (heleC.trans (le_mul_of_one_le_right hC.le hZδ))

end CanonicalRowCompletion

namespace InitialMeanSquare

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (normalizedColumn columnLog firstLogDensity)

theorem initial_sector_transfer_radius
    (U : ℝ→ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0≤A)
    (hU : ∀t,g t≠0→U t=1) (hgA : ∀t,g t≠0→|t|≤A)
    (ε : ℝ) (hε : 0<ε) (N J : ℕ) :
    ∃ (windows : Fin 7→ℝ→ℂ) (C Cₛ : ℝ),0≤C ∧ 0≤Cₛ ∧
      (∀i,HasCompactSupport (windows i)) ∧ (∀i,ContDiff ℝ ∞ (windows i)) ∧
      (∀i t,windows i t≠0→|t|≤A+2+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
        [∀i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀i,lambda∉Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
        (_hpr : ∀i,lambda^2∣p i-1)
        (F : Finset ι) (Ψ : ActualEisensteinCubic.O→*ℂ) (m r : ActualEisensteinCubic.O) (ray : SecondRayIndex)
        (s : Finset (SecondExpansionData ι)) (Z H E V X K : ℝ),
        0<Z → 0<H → 0<E → 0<V → 0<X → 0<K →
        (∀a,‖Ψ a‖≤1) → (∀x∈s,InSecondQuotientSector p r x) → (∀x∈s,x.frequency≠0) →
        (∀x∈s,|sourceLogZ p Z X x|≤2) → (∀x∈s,|sourceLogE p E x|≤2) →
        (∀x∈s,|sourceLogV p V x|≤2) → (∀x∈s,|sourceLogK p K x|≤2) →
        ∃ B : Frequency→ℝ,
          (∀q,0≤B q) ∧
          (∀q,(1+H*K/(E^2*V^2*X^2))^N*B q≤
            Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) ∧
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray s
            (fun S => normalizedColumn p (fun T => g (columnLog p Z T)) S)
            (fun S => normalizedColumn p (fun T => g (columnLog p Z T)) S) W H‖≤
          (C*H*elementNorm r/Z^2*‖secondRayCoefficient ray‖*(K*Real.exp 2)^ε)*
            (∫t₁:ℝ,∫t₂:ℝ,∫t₃:ℝ,B (t₁,t₂,t₃)*
              sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
                (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X (t₁,t₂,t₃)) := by
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := initial_sector_fixed_profiles
    U hUc hUs g g W A hA hU hU hgA hgA
  obtain ⟨Cw,hCw,hwbound⟩ := outerWindow_global_bound windows hwc (fun i => (hws i).continuous)
  have hM : 0≤A+2+1 := by linarith
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htrans⟩ := initial_source_uniform_transfer ε hε A₁ A₂ W windows
    (fun _ => A+2+1) (fun _ => hM) hwb N J
  refine ⟨windows,Cw*Cₐ,Cₛ,mul_nonneg hCw hCₐ.le,hCₛ,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F Ψ m r ray s Z H E V X K hZ hH hE hV hX hK hΨ hs hk hz he hv hkap
  let R := H*K/(E^2*V^2*X^2)
  have hR : 0<R := by dsimp [R]; positivity
  obtain ⟨b,hpoint,hbound⟩ := htrans R hR
  let B : Frequency→ℝ := fun q => ‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b q‖
  refine ⟨B,fun q => norm_nonneg _,?_,?_⟩
  · intro q
    simpa only [B,R,tripleCoefficient,mul_assoc] using hpoint q.1 q.2.1 q.2.2
  · let T := s.image (sourceObservation p)
    have hT0 : ∀y∈T,y.1≠0 := by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact sourceRow_nonzero p x (hk x hx)
    have hTK : ∀y∈T,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K*Real.exp 2 := by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      have hpos := elementNorm_pos _ (sourceRow_nonzero p x (hk x hx))
      have hl : Real.log (elementNorm (sourceObservation p x).1/K)≤2 :=
        (le_abs_self _).trans (hkap x hx)
      have hh := Real.exp_le_exp.mpr hl
      rw [Real.exp_log (div_pos hpos hK)] at hh
      have hh' := (div_le_iff₀ hK).mp hh
      simpa only [elementNorm,eisEmbedding_norm_sq_eq_absNorm_span,mul_comm] using hh'
    let D := H*elementNorm r/Z^2*‖secondRayCoefficient ray‖
    have hD : 0≤D := by dsimp [D,elementNorm]; positivity
    have hweights : ∀x∈s,‖sourceWeight p hp hcop hg Ψ m ray Z H x‖*
        ‖outerWindow windows (sourceLogZ p Z X x) 0 (sourceLogE p E x) (sourceLogV p V x) (sourceLogK p K x)‖≤D*Cw := by
      intro x hx
      exact mul_le_mul (sourceWeight_norm_fixed p hp hcop hg hinj hc Ψ m r ray Z H x
        (hs x hx) hZ hH.le (hΨ _) (hΨ _)) (hwbound _ _ _ _ _) (norm_nonneg _) hD
    have hh := hbound p hp hcop hg hinj r s T (sourceWeight p hp hcop hg Ψ m ray Z H) (D*Cw)
      (K*Real.exp 2) F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) (m*r)
      (sourceLogZ p Z X) (fun _ => 0) (sourceLogE p E) (sourceLogV p V) (sourceLogK p K) X X
      (mul_nonneg hD hCw) (by positivity) hs (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩) hT0 hTK hweights
    rw [hid p hp hcop hg hinj hpr F Ψ m r ray s Z H E V X K hZ hE hV hX hK hs hk hz he hv hkap]
    convert hh using 1 ; dsimp [D,B,R,T] ; ring

end
section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)

theorem initial_subbin_transfer_radius
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A)
    (hU : ∀ t, g t ≠ 0 → U t=1) (hgA : ∀ t, g t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (N J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Cₛ : ℝ), 0 ≤ C ∧ 0 ≤ Cₛ ∧
      (∀ i, HasCompactSupport (windows i)) ∧ (∀ i, ContDiff ℝ ∞ (windows i)) ∧
      (∀i t,windows i t≠0→|t|≤A+2+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀ i, lambda ∉ Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hc : ∀ i, ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
        (_hpr : ∀ i, lambda^2 ∣ p i-1)
        (F R : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (ray : SecondRayIndex)
        (K : Finset ι → Finset ι → Finset ActualEisensteinCubic.O) (Z H M : ℝ) (j : SecondLogIndex)
        (s : Finset (SecondExpansionData ι)),
        0 < Z → 0 < H → (∀ a, ‖Ψ a‖ ≤ 1) →
        s ⊆ secondLogSector p ∅ F K R Z M j →
        let X := initialLogColumn Z (primeProductNorm p R) j
        let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
        ∃ B : Frequency → ℝ,
          (∀ q, 0 ≤ B q) ∧
          (∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
            Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) ∧
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray s
            (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V)
            (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V) W H‖ ≤
          (C*H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
            (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, B (t₁,t₂,t₃)*
              sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
                (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X (t₁,t₂,t₃)) := by
  obtain ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,hwb,ht⟩ :=
    initial_sector_transfer_radius U hUc hUs g W A hA hU hgA ε hε N J
  refine ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F R Ψ m ray K Z H M j s hZ hH hΨ hsub
  dsimp only
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let X := initialLogColumn Z (primeProductNorm p R) j
  have hR : 0 < primeProductNorm p R := FirstPassCubeLabels.primeProductNorm_pos p hp R
  have hX : 0 < X := div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hR)
  have hs : ∀ x ∈ s, InSecondQuotientSector p r x := by
    intro x hx
    exact secondExpansionSector_valid p F (fun G E => (K G E).erase 0) R x
      (secondLogSector_subset p ∅ F K R Z M j (hsub hx))
  have hk : ∀ x ∈ s, x.frequency ≠ 0 := by
    intro x hx
    exact (secondSupportedSector_mem p F K R Z M x (Finset.mem_filter.mp (hsub hx)).1).2.2.2.1
  have hcoords := initial_sector_coordinates p hp F R K Z M hZ j
  obtain ⟨B,hB,hdec,hbound⟩ := ht p hp hcop hg hinj hc hpr F Ψ m r ray s Z H
    (secondLogE j) (secondLogV j) X (secondLogK j) hZ hH
    (normLogScale_pos _) (normLogScale_pos _) hX (normLogScale_pos _) hΨ hs hk
    (fun x hx => (hcoords x (hsub hx)).1) (fun x hx => (hcoords x (hsub hx)).2.1)
    (fun x hx => (hcoords x (hsub hx)).2.2.1) (fun x hx => (hcoords x (hsub hx)).2.2.2)
  refine ⟨B,hB,?_,?_⟩
  · simpa only [X, initial_log_radial Z H (primeProductNorm p R) hZ.ne' hR.ne'] using hdec
  · simpa only [r, elementNorm, primeSubsetGenerator_norm_eq_productNorm] using hbound

end

section
open ActualEisensteinCubic
open SecondPassArithmetic

theorem initial_source_target_coprime
    {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) [∀i,(Ideal.span {p i}).IsMaximal]
    (bad : Ideal ActualEisensteinCubic.O) (hbad : ∀i,IsCoprime (Ideal.span {p i}) bad)
    (s : Finset (SecondExpansionData ι)) :
    ∀z∈sourceIdealTarget (s.image (sourceObservation p)),IsCoprime z.1 bad := by
  intro z hz
  obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hz
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hy
  change IsCoprime (Ideal.span {(sourceObservation p x).2}) bad
  rw [sourceLabel_span]
  exact (IsCoprime.prod_left (fun i _=>hbad i)).mul_left
    (IsCoprime.prod_left (fun i _=>hbad i))

end

open MeasureTheory
open scoped BigOperators Classical ContDiff
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

theorem HasInitialCanonicalDensityAtRadius.retained_density {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S)
    (hcan : HasInitialCanonicalDensityAtRadius χ S hbad)
    (a b σ θ ν η : ℝ) (hσ : 0 ≤ σ) (hν : 0 < ν) (hη : 0 < η)
    (hmargin : ν+θ ≤ σ-(1 : ℝ)/20) (A : ℝ) (hA : 0≤A) :
    ∃ J : ℕ,∀ V₁ V₂ : ℝ → ℂ,HasCompactSupport V₁ → HasCompactSupport V₂ →
      ContDiff ℝ ∞ V₁ → ContDiff ℝ ∞ V₂ →
      (∀s,V₁ s≠0→|s|≤A) → (∀s,V₂ s≠0→|s|≤A) →
      ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ 20 ≤ E ∧ ∀ (D : ℕ) (Z : ℝ)
        (R : Finset (OutsidePrimeIndex S D)) (ray : SecondRayIndex) (j : SecondLogIndex)
        (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)),
        1 ≤ Z → Cpool*Z^E ≤ D →
        R ∈ boundedPrimeSupports (outsidePrime S D) Finset.univ (Z*Real.exp (initialErrorWindow a b)) →
        j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z (Z^(1+σ))) →
        initialRadial Z (Z^(1+σ)) (primeProductNorm (outsidePrime S D) R) j ≤ Z^θ →
        (∀ z ∈ T,Admissible z.1 ∧ (Ideal.absNorm z.1 : ℝ) ≤ initialLogLabel j ∧
          z.2 ≠ 0 ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ secondLogK j*Real.exp 2) →
        (∀z∈T,IsCoprime z.1 (∏P∈S,P)) →
        outsideCanonicalDensity χ S hbad D ray R T V₁ V₂
          (initialLogColumn Z (primeProductNorm (outsidePrime S D) R) j) J ≤
        C*Z^η*(initialLogColumn Z (primeProductNorm (outsidePrime S D) R) j*initialLogLabel j)^2 := by
  obtain ⟨J,hJ⟩ := hcan η hη 20 A hA
  refine ⟨J,?_⟩
  intro V₁ V₂ hVc₁ hVc₂ hVs₁ hVs₂ hVrad₁ hVrad₂
  obtain ⟨Cc,Cpool,E,hCc,hCpool,hPE,hcanonical⟩ := hJ V₁ V₂ hVc₁ hVc₂ hVs₁ hVs₂ hVrad₁ hVrad₂
  obtain ⟨A,Vmax,hA,hVmax,hV₁,hV₂,hs₁,hs₂⟩ :=
    initial_two_windows_bounded V₁ V₂ hVc₁ hVc₂ hVs₁.continuous hVs₂.continuous
  obtain ⟨Z0,hZ0,hthreshold⟩ := initial_large_threshold a b (initialExcludedNorm S) ν
    (initialExcludedNorm_ge_one S) hν
  let Ce := initialElementaryConstant A Vmax*(∫ t : ℝ,firstLogDensity 0 t)^3
  let K0 := initialPolynomialCap a b*Z0^17*Real.exp 2
  let C := Cc+Ce*(K0+1)+1
  have hI : 0 ≤ ∫ t : ℝ,firstLogDensity 0 t :=
    integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hCe : 0 ≤ Ce := mul_nonneg (initialElementaryConstant_nonneg A Vmax) (pow_nonneg hI _)
  have hcap := initialPolynomialCap_ge_one a b
  have hK0 : 0 ≤ K0 := by dsimp [K0]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hCcC : Cc ≤ C := by dsimp [C]; nlinarith
  have hCeC : Ce ≤ C := by dsimp [C]; nlinarith
  have hCeKC : Ce*K0 ≤ C := by dsimp [C]; nlinarith
  refine ⟨C,Cpool,E,hC,hCpool,hPE,?_⟩
  intro D Z R ray j T hZ hpool hR hj hrad hT hTc
  let p := outsidePrime S D
  let hp := outsidePrime_ne_zero S hbad D
  let hcop := outsidePrime_coprime S hbad D
  let hg := outsidePrime_good S hbad D
  let := outsidePrime_maximal S hbad D
  let Ψ := conjugateMonoid (normCharacter χ)
  let X := initialLogColumn Z (primeProductNorm p R) j
  let lengthScale := initialLogLabel j
  let Kr := secondLogK j*Real.exp 2
  have hZp := zero_lt_one.trans_le hZ
  have hH : 1 ≤ Z^(1+σ) := Real.one_le_rpow hZ (by linarith)
  have hB := primeProductNorm_ge_one p hp R
  have hBpos := zero_lt_one.trans_le hB
  have hX : 0 < X := initialLogColumn_pos Z _ j hZp hBpos
  have hL : 1 ≤ lengthScale := initialLogLabel_ge_one j
  have hKr : 1 ≤ Kr := one_le_mul_of_one_le_of_one_le
    (normLogScale_ge_one _) (Real.one_le_exp (by norm_num))
  have hZη : 1 ≤ Z^η := Real.one_le_rpow hZ hη.le
  have hΨ : ∀ z,‖Ψ z‖ ≤ 1 := conjugateMonoid_norm_le_one (normCharacter χ) (normCharacter_norm_le_one χ)
  have hΨ₁ : ∀ z,‖secondRayMinus Ψ ray z‖ ≤ 1 :=
    fun z => (secondRayMinus_norm_le Ψ ray z).trans (hΨ z)
  have hΨ₂ : ∀ z,‖secondRayPlus Ψ ray z‖ ≤ 1 :=
    fun z => (secondRayPlus_norm_le Ψ ray z).trans (hΨ z)
  have hTb : ∀ z ∈ T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ Kr := by
    intro z hz
    exact ⟨(hT z hz).1.1,(hT z hz).2.1,(hT z hz).2.2.2⟩
  have promote (d : ℝ) (hd : d ≤ C)
      (he : outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X J ≤ d*(X*lengthScale)^2) :
      outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X J ≤ C*Z^η*(X*lengthScale)^2 :=
    he.trans (mul_le_mul_of_nonneg_right (hd.trans (le_mul_of_one_le_right hC.le hZη)) (sq_nonneg _))
  by_cases hzlarge : Z0 ≤ Z
  · have hgeom := initial_large_bin_geometry p hp Finset.univ R a b Z σ θ ν (initialExcludedNorm S)
      j hZ (initialExcludedNorm_ge_one S) hR hj hσ hmargin (hthreshold Z hzlarge) hrad
    dsimp only at hgeom
    by_cases hxlarge : 1 ≤ X
    · exact (hcanonical D Z X lengthScale Kr R ray T hZ hpool hxlarge hL hKr
        hgeom.1 hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1 hgeom.2.2.2.2.1 hgeom.2.2.2.2.2 hT hTc).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCcC (Real.rpow_nonneg hZp.le _)) (sq_nonneg _))
    · have hKL : Kr ≤ lengthScale := initial_subunit_row_le_label Z X lengthScale Kr
        (initialExcludedNorm S*primeProductNorm p R) ((1 : ℝ)/20) hZ (le_of_not_ge hxlarge)
        (zero_le_one.trans hL) (zero_le_one.trans hKr)
        (one_le_mul_of_one_le_of_one_le (initialExcludedNorm_ge_one S) hB)
        (by norm_num) (by simpa only [Kr,X,lengthScale,neg_div] using hgeom.2.2.2.2.2)
      apply promote Ce hCeC
      exact initial_subunit_density_bound p hp hcop hg (outsidePrime_odd S hbad D)
        (outsidePrime_injective S hbad D) Finset.univ (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        hΨ₁ hΨ₂ _ T V₁ V₂ X lengthScale Kr A Vmax J hX hL hKr hKL hA hVmax hV₁ hV₂ hs₁ hs₂ hTb
  · have hKmax := initialErrorRowBound_ge_one a b Z (Z^(1+σ)) hZ hH
    have hkr : Kr ≤ K0 := by
      have hbin := initial_bin_row_scale_le (Z*Real.exp (initialErrorWindow a b))
        (initialErrorRowBound a b Z (Z^(1+σ))) hKmax j hj
      have hcapZ := (initial_actual_bin_polynomial_caps a b Z (Z^(1+σ)) hZ hH).2
      have hpow : Z^17 ≤ Z0^17 := pow_le_pow_left₀ hZp.le (le_of_not_ge hzlarge) 17
      calc
        Kr ≤ (initialPolynomialCap a b*Z^17)*Real.exp 2 :=
          mul_le_mul_of_nonneg_right (hbin.trans hcapZ) (Real.exp_pos _).le
        _ ≤ K0 := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hcap)) (Real.exp_pos _).le
    apply promote (Ce*Kr) ((mul_le_mul_of_nonneg_left hkr hCe).trans hCeKC)
    exact initial_density_elementary_squared_mass p hp hcop hg (outsidePrime_odd S hbad D)
      (outsidePrime_injective S hbad D) Finset.univ (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      hΨ₁ hΨ₂ _ T V₁ V₂ X lengthScale Kr A Vmax J hX hL hKr hA hVmax hV₁ hV₂ hs₁ hs₂ hTb

end InitialMeanSquare

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity normalizedColumn columnLog)

theorem HasInitialCanonicalDensityAtRadius.retained_source {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (hcan : HasInitialCanonicalDensityAtRadius χ S hbad)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (a b σ θ ν η : ℝ)
    (hU : ∀ t,g t ≠ 0 → U t=1)
    (hgs : ∀ t,g t ≠ 0 → |t| ≤ initialErrorWindow a b)
    (hσ : 0 ≤ σ) (hν : 0 < ν) (hη : 0 < η)
    (hmargin : ν+θ ≤ σ-(1 : ℝ)/20) :
    ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ 20 ≤ E ∧
      ∀ (D : ℕ) (Z : ℝ),1 ≤ Z → Cpool*Z^E ≤ D →
      let p := outsidePrime S D
      let hp := outsidePrime_ne_zero S hbad D
      let hcop := outsidePrime_coprime S hbad D
      let hg := outsidePrime_good S hbad D
      letI := outsidePrime_maximal S hbad D
      let Ψ := conjugateMonoid (normCharacter χ)
      let H := Z^(1+σ)
      let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
      let K := fun (_ _ : Finset (OutsidePrimeIndex S D)) => initialErrorCutoff a b Z H
      (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp (initialErrorWindow a b)),
        ∑ j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H),
        if initialRadial Z H (primeProductNorm p R) j ≤ Z^θ then
          ‖secondExpansionSource p hp hcop hg Finset.univ Ψ 1 1 1 ray
            (initialSquarefreeSector p (secondLogSector p ∅ Finset.univ K R Z (initialErrorWindow a b) j))
            G G W H‖ else 0) ≤ C*H*Z^(35*η) := by
  obtain ⟨J,hJ⟩ := HasInitialCanonicalDensityAtRadius.retained_density χ S hbad hcan a b σ θ ν η hσ hν hη hmargin
    (initialErrorWindow a b+2+1) (by unfold initialErrorWindow; positivity)
  have hM : 0 ≤ initialErrorWindow a b := by unfold initialErrorWindow; positivity
  obtain ⟨windows,Ct,Cs,hCt,hCs,hwc,hws,hwb,ht⟩ :=
    initial_subbin_transfer_radius U hUc hUs g W (initialErrorWindow a b) hM hU hgs η hη 0 (2*J)
  obtain ⟨Ce,Cpool,E,hCe,hCpool,hPE,henergy⟩ := hJ (windows 5) (windows 6) (hwc 5) (hwc 6) (hws 5) (hws 6) (hwb 5) (hwb 6)
  obtain ⟨Cl,hCl,hlog⟩ := initial_row_log_budget η (initialPolynomialCap a b) hη (initialPolynomialCap_ge_one a b)
  let C0 := Ct*Real.exp 4*Ce*Cs*initialRayMass*Cl
  have hray := initialRayMass_nonneg
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  refine ⟨C0+1,Cpool,E,by linarith,hCpool,hPE,?_⟩
  intro D Z hZ hpool
  dsimp only
  let p := outsidePrime S D
  let hp := outsidePrime_ne_zero S hbad D
  let hcop := outsidePrime_coprime S hbad D
  let hg := outsidePrime_good S hbad D
  let := outsidePrime_maximal S hbad D
  let Ψ := conjugateMonoid (normCharacter χ)
  let H := Z^(1+σ)
  let M := initialErrorWindow a b
  let K := fun (_ _ : Finset (OutsidePrimeIndex S D)) => initialErrorCutoff a b Z H
  let Kmax := initialErrorRowBound a b Z H
  let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
  let s := fun (R : Finset (OutsidePrimeIndex S D)) (j : SecondLogIndex) =>
    initialSquarefreeSector p (secondLogSector p ∅ Finset.univ K R Z M j)
  have hZp := zero_lt_one.trans_le hZ
  have hH : 1 ≤ H := Real.one_le_rpow hZ (by linarith)
  have hHp := zero_lt_one.trans_le hH
  have hΨ : ∀ z,‖Ψ z‖ ≤ 1 := conjugateMonoid_norm_le_one (normCharacter χ) (normCharacter_norm_le_one χ)
  have hKmax : 1 ≤ Kmax := initialErrorRowBound_ge_one a b Z H hZ hH
  let B : SecondRayIndex → Finset (OutsidePrimeIndex S D) → SecondLogIndex → Frequency → ℝ :=
    fun ray R j => Classical.choose
      (ht p hp hcop hg (outsidePrime_injective S hbad D) (outsidePrime_odd S hbad D)
        (outsidePrime_primary S hbad D) Finset.univ R Ψ 1 ray K Z H M j (s R j)
        hZp hHp hΨ (Finset.filter_subset _ _))
  have hB (ray : SecondRayIndex) (R : Finset (OutsidePrimeIndex S D)) (j : SecondLogIndex) :=
    Classical.choose_spec
      (ht p hp hcop hg (outsidePrime_injective S hbad D) (outsidePrime_odd S hbad D)
        (outsidePrime_primary S hbad D) Finset.univ R Ψ 1 ray K Z H M j (s R j)
        hZp hHp hΨ (Finset.filter_subset _ _))
  let d := H*Real.exp 4*(Ce*Z^η)*Cs*(Kmax*Real.exp 2)^η
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hterm (ray : SecondRayIndex) (R : Finset (OutsidePrimeIndex S D))
      (hR : R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M))
      (j : SecondLogIndex) (hj : j ∈ secondLogBinBox (Z*Real.exp M) Kmax)
      (hlow : initialRadial Z H (primeProductNorm p R) j ≤ Z^θ) :
      initialSquarefreeBinCost p hp hcop hg Finset.univ R Ψ 1 ray K Z H M η j windows (B ray R j) ≤
        d/primeProductNorm p R*‖secondRayCoefficient ray‖ := by
    have hT := initial_squarefree_target_geometry p hp hg (outsidePrime_odd S hbad D)
      Finset.univ R K Z M j
    have hTe : ∀ z ∈ sourceIdealTarget ((s R j).image (sourceObservation p)),
        Admissible z.1 ∧ (Ideal.absNorm z.1 : ℝ) ≤ initialLogLabel j ∧ z.2 ≠ 0 ∧
        ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ secondLogK j*Real.exp 2 := by
      intro z hz
      exact ⟨(hT z hz).1,(hT z hz).2.1,(hT z hz).2.2.1,(hT z hz).2.2.2.trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num)) (normLogScale_pos _).le)⟩
    have hTc := initial_source_target_coprime p (∏P∈S,P)
      (CanonicalRowCompletion.outside_pool_coprime_excluded S D hbad hSp) (s R j)
    have he := henergy D Z R ray j _ hZ hpool hR hj hlow hTe hTc
    have he' :
        densityChildEnergy p hp hcop hg Finset.univ (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
          (1*primeSubsetGenerator (fun i => Ideal.span {p i}) R)
          (sourceIdealTarget ((s R j).image (sourceObservation p)))
          (windows 5) (windows 6) (initialLogColumn Z (primeProductNorm p R) j)
          (initialLogColumn Z (primeProductNorm p R) j) (2*J) ≤
          (Ce*Z^η)*(initialLogColumn Z (primeProductNorm p R) j*initialLogLabel j)^2 := by
      simpa only [outsideCanonicalDensity,one_mul] using he
    exact initial_bin_cost_uniform p hp hcop hg Finset.univ R Ψ 1 ray K Z H M Kmax η Cs
      (Ce*Z^η) hZp hHp hKmax hη.le hCs (by positivity) j hj windows (B ray R j) (2*J) 0
      (hB ray R j).1 (hB ray R j).2.1 he'
  have hsum :
      (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
        ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
        if initialRadial Z H (primeProductNorm p R) j ≤ Z^θ then
          ‖secondExpansionSource p hp hcop hg Finset.univ Ψ 1 1 1 ray (s R j) G G W H‖ else 0) ≤
      Ct*(d*initialRayMass*((secondLogBinBox (Z*Real.exp M) Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin (Z*Real.exp M)+1 : ℝ))) := by
    apply le_trans _ (mul_le_mul_of_nonneg_left
      (initial_harmonic_aggregation p (outsidePrime_injective S hbad D) Finset.univ
        (Z*Real.exp M) Kmax d hd
        (fun ray R j => if initialRadial Z H (primeProductNorm p R) j ≤ Z^θ then
          initialSquarefreeBinCost p hp hcop hg Finset.univ R Ψ 1 ray K Z H M η j windows (B ray R j)
          else 0) (by
          intro ray R hR j hj
          split_ifs with hlow
          · exact hterm ray R hR j hj hlow
          · have hRp := FirstPassCubeLabels.primeProductNorm_pos p hp R
            positivity)) hCt)
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ray hray
    apply Finset.sum_le_sum
    intro R hR
    apply Finset.sum_le_sum
    intro j hj
    split_ifs with hlow
    · convert (hB ray R j).2.2 using 1 ;
        dsimp only [initialSquarefreeBinCost,s,G,B] ; ring
    · simp
  have hlogBound := hlog Z (Z*Real.exp M) Kmax hZ (by positivity) (zero_lt_one.trans_le hKmax)
    (initial_actual_bin_polynomial_caps a b Z H hZ hH).1
    (initial_actual_bin_polynomial_caps a b Z H hZ hH).2
  calc
    _ ≤ Ct*(d*initialRayMass*((secondLogBinBox (Z*Real.exp M) Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin (Z*Real.exp M)+1 : ℝ))) := hsum
    _ = (Ct*Real.exp 4*Ce*Cs*initialRayMass)*H*Z^η*
        ((Kmax*Real.exp 2)^η*((secondLogBinBox (Z*Real.exp M) Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin (Z*Real.exp M)+1 : ℝ))) := by dsimp [d]; ring
    _ ≤ (Ct*Real.exp 4*Ce*Cs*initialRayMass)*H*Z^η*(Cl*Z^(34*η)) :=
      mul_le_mul_of_nonneg_left hlogBound (by positivity)
    _ = C0*H*Z^(35*η) := by
      rw [show 35*η=η+34*η by ring,Real.rpow_add hZp]
      dsimp [C0]
      ring
    _ ≤ (C0+1)*H*Z^(35*η) := by
      gcongr
      linarith

end InitialMeanSquare

end

end OAI
end OAIOriginalModule0252

/-! Original module: OAI.NumberTheory.DirichletL.MeanSquare.ThetaDensity
Source SHA256: 317247ddc7135b06a35186f290ece58d0abf8a4e9025bcd7c96697e32e5206b4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0253


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

namespace InitialMeanSquare

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)

theorem HasInitialCanonicalDensityAtRadius.nonzero_source_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (hcan : HasInitialCanonicalDensityAtRadius χ S hbad)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (a b σ ε : ℝ)
    (hU : ∀ t,g t ≠ 0 → U t=1)
    (hgs : ∀ t,g t ≠ 0 → |t| ≤ initialErrorWindow a b)
    (hσ : (1 : ℝ)/20 < σ) (hε : 0 < ε) :
    ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ 20 ≤ E ∧
      ∀ (D : ℕ) (Z : ℝ),1 ≤ Z → Cpool*Z^E ≤ D →
      let p := outsidePrime S D
      let hp := outsidePrime_ne_zero S hbad D
      let hg := outsidePrime_good S hbad D
      let hinj := outsidePrime_injective S hbad D
      letI := outsidePrime_maximal S hbad D
      let Ψ := conjugateMonoid (normCharacter χ)
      let H := Z^(1+σ)
      ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1
        (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V)
        W H (fun _ _ => (initialErrorCutoff a b Z H).erase 0)‖ ≤ C*H*Z^ε := by
  let η := min 1 (ε/100)
  let ν := (σ-(1 : ℝ)/20)/3
  have hη : 0 < η := lt_min zero_lt_one (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : 35*η ≤ ε := by
    have hh : η ≤ ε/100 := min_le_right _ _
    linarith
  have hν : 0 < ν := by dsimp [ν]; linarith
  have hσ0 : 0 ≤ σ := by linarith
  have hmargin : ν+ν ≤ σ-(1 : ℝ)/20 := by dsimp [ν]; linarith
  obtain ⟨Cl,Cpool,E,hCl,hCpool,hPE,hlow⟩ := HasInitialCanonicalDensityAtRadius.retained_source χ S hbad hSp hcan U hUc hUs g W
    a b σ ν ν η hU hgs hσ0 hν hη hmargin
  obtain ⟨Ch,hCh,hhigh⟩ := initial_high_radial_source U hUc hUs g W a b ν 1 η hU hgs hν hη hη1
  refine ⟨Cl+Ch,Cpool,E,by positivity,hCpool,hPE,?_⟩
  intro D Z hZ hpool
  dsimp only
  let p := outsidePrime S D
  let hp := outsidePrime_ne_zero S hbad D
  let hcop := outsidePrime_coprime S hbad D
  let hg := outsidePrime_good S hbad D
  let hinj := outsidePrime_injective S hbad D
  let := outsidePrime_maximal S hbad D
  let Ψ := conjugateMonoid (normCharacter χ)
  let H := Z^(1+σ)
  let M := initialErrorWindow a b
  let K := fun (_ _ : Finset (OutsidePrimeIndex S D)) => initialErrorCutoff a b Z H
  let Kmax := initialErrorRowBound a b Z H
  let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
  let s := fun (R : Finset (OutsidePrimeIndex S D)) (j : SecondLogIndex) =>
    initialSquarefreeSector p (secondLogSector p ∅ Finset.univ K R Z M j)
  let f := fun (ray : SecondRayIndex) (R : Finset (OutsidePrimeIndex S D)) (j : SecondLogIndex) =>
    ‖secondExpansionSource p hp hcop hg Finset.univ Ψ 1 1 1 ray (s R j) G G W H‖
  let Lsum := ∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
    ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
      if initialRadial Z H (primeProductNorm p R) j ≤ Z^ν then f ray R j else 0
  let Hsum := ∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
    ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
      if Z^ν < initialRadial Z H (primeProductNorm p R) j then f ray R j else 0
  have hZp := zero_lt_one.trans_le hZ
  have hH : 1 ≤ H := Real.one_le_rpow hZ (by linarith)
  have hHp := zero_lt_one.trans_le hH
  have hΨ : ∀ z,‖Ψ z‖ ≤ 1 := conjugateMonoid_norm_le_one (normCharacter χ) (normCharacter_norm_le_one χ)
  have hL : Lsum ≤ Cl*H*Z^(35*η) := hlow D Z hZ hpool
  have hHi : Hsum ≤ Ch*Z^(-(1 : ℝ)) :=
    hhigh p hp hcop hg hinj (outsidePrime_odd S hbad D) (outsidePrime_primary S hbad D)
      Finset.univ Ψ 1 Z H hZ hH hΨ (fun _ R j => s R j) (fun _ _ _ => Finset.filter_subset _ _)
  have hrow : ∀ R ∈ (Finset.univ : Finset (OutsidePrimeIndex S D)).powerset,
      ∀ x ∈ secondSupportedSector p Finset.univ K R Z M,elementNorm (sourceObservation p x).1 ≤ Kmax := by
    intro R hR x hx
    exact initialErrorRowBound_valid p hp Finset.univ R a b Z H hZp hHp x hx
  have htotal := initial_nonzero_source_norm_le_squarefree_bins p hp hcop hg hinj
    (outsidePrime_odd S hbad D) (outsidePrime_primary S hbad D) Finset.univ Ψ 1 g W
    Z H M Kmax hZp hgs K hrow
  have hpart : (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
      ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,f ray R j)=Lsum+Hsum := by
    dsimp only [Lsum,Hsum]
    simp only [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ray hray
    apply Finset.sum_congr rfl
    intro R hR
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hh : initialRadial Z H (primeProductNorm p R) j ≤ Z^ν
    · rw [ite_eq_left hh,ite_eq_right (not_lt.mpr hh),add_zero]
    · rw [ite_eq_right hh,ite_eq_left (lt_of_not_ge hh),zero_add]
  have hpower : Z^(35*η) ≤ Z^ε := Real.rpow_le_rpow_of_exponent_le hZ hηε
  have hsmall : Z^(-(1 : ℝ)) ≤ H*Z^ε := by
    have h1 : Z^(-(1 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hZ (by norm_num)
    exact h1.trans (one_le_mul_of_one_le_of_one_le hH (Real.one_le_rpow hZ hε.le))
  calc
    _ ≤ ∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
      ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,f ray R j := htotal
    _ = Lsum+Hsum := hpart
    _ ≤ Cl*H*Z^(35*η)+Ch*Z^(-(1 : ℝ)) := add_le_add hL hHi
    _ ≤ Cl*H*Z^ε+Ch*(H*Z^ε) := add_le_add
      (mul_le_mul_of_nonneg_left hpower (mul_nonneg hCl.le hHp.le))
      (mul_le_mul_of_nonneg_left hsmall hCh.le)
    _ = (Cl+Ch)*H*Z^ε := by ring

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (normalizedColumn columnLog)

theorem outside_mean_square_of_canonical_density_at_radius {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀ P ∈ S,Prime P)
    (hcan : HasInitialCanonicalDensityAtRadius χ S hbad)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (σ ε : ℝ) (hσ : (1 : ℝ)/20 < σ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (D : ℕ) (Z : ℝ),1 ≤ Z → b*Z ≤ D →
      ∀ T : Finset ActualEisensteinCubic.O,
      (∀ z ∈ T,(Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Z^(1+σ)) →
      (∀ z ∈ T,z ≠ 0) →
      (∑ z ∈ T,‖idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
        (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2) ≤ C*Z*(Z^(1+σ))*Z^ε := by
  let g0 := initialLogProfile W a b ha hs hW
  let g := conjugateProfile g0
  let M := initialErrorWindow a b
  have hM : 0 ≤ M := by dsimp [M,initialErrorWindow]; positivity
  have hg0 : ∀ t,g0 t ≠ 0 → |t| ≤ M := initialLogProfile_support W a b ha hs hW
  have hg : ∀ t,g t ≠ 0 → |t| ≤ M := conjugateProfile_support_bound g0 M hg0
  obtain ⟨U,hUc,hUs,hUeq,hUsupp,hUzero⟩ := FourierBridge.exists_complex_smooth_cutoff M hM
  have hU : ∀ t,g t ≠ 0 → U t=1 := fun t ht => hUeq t (hg t ht)
  obtain ⟨Cs,Cpool,E,hCs,hCpool,hE,hsource⟩ := HasInitialCanonicalDensityAtRadius.nonzero_source_bound χ S hbad hSp hcan
    U hUc hUs g rowMajorant a b σ ε hU hg hσ hε
  obtain ⟨Ce,hCe,herrors⟩ := outside_mean_square_source_with_errors W a b ha hs hW
  refine ⟨Cs+Ce,by positivity,?_⟩
  intro D Z hZ hD T hT hT0
  let Db : ℕ := max D ⌈Cpool*Z^E⌉₊
  have hDDb : D ≤ Db := le_max_left _ _
  have hpool : Cpool*Z^E ≤ (Db : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right D ⌈Cpool*Z^E⌉₊)
  have hDb : b*Z ≤ (Db : ℝ) := hD.trans (by exact_mod_cast hDDb)
  let p := outsidePrime S Db
  let hp := outsidePrime_ne_zero S hbad Db
  let hg := outsidePrime_good S hbad Db
  let hinj := outsidePrime_injective S hbad Db
  let := outsidePrime_maximal S hbad Db
  let Ψ := conjugateMonoid (normCharacter χ)
  let H := Z^(1+σ)
  let G := fun V => normalizedColumn p (fun T => g0 (columnLog p Z T)) V
  let MS := ∑ z ∈ T,‖idealRowSum (outsideIdealsUpTo S Db) (outsideIdealsUpTo_ne_bot S Db)
    (outside_good S Db hbad) χ (fun n => W (n/Z)) z‖^2
  have hZp := zero_lt_one.trans_le hZ
  have hH : 1 ≤ H := Real.one_le_rpow hZ (by linarith)
  have hHp := zero_lt_one.trans_le hH
  have hεZ : 1 ≤ Z^ε := Real.one_le_rpow hZ hε.le
  have he := herrors χ S Db hbad hSp Z H hZp hHp hDb T hT hT0
  have hsrc := hsource Db Z hZ hpool
  have hstar : (fun V => star (G V)) =
      (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V) := by
    funext V
    exact star_normalizedColumn p g0 Z V
  have hsrc' :
      ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1 (fun V => star (G V))
        rowMajorant H (fun _ _ => (initialErrorCutoff a b Z H).erase 0)‖ ≤ Cs*H*Z^ε := by
    rw [hstar]
    exact hsrc
  change MS/Z ≤
    ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1 (fun V => star (G V))
      rowMajorant H (fun _ _ => (initialErrorCutoff a b Z H).erase 0)‖+Ce*H-‖G ∅‖^2 at he
  have herr : Ce*H ≤ Ce*H*Z^ε := le_mul_of_one_le_right (mul_nonneg hCe.le hHp.le) hεZ
  have hnorm : MS/Z ≤ (Cs+Ce)*H*Z^ε := by
    nlinarith [sq_nonneg ‖G ∅‖]
  have hfinal := (div_le_iff₀ hZp).mp hnorm
  have hMS : (∑ z ∈ T,‖idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
      (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2)=MS := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [outside_row_cutoff_stable S hbad hDDb χ W b Z hZp (fun t ht => (hs ht).2) hD z]
  rw [hMS]
  convert hfinal using 1 ; dsimp only [H] ; ring

end

open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalRowCompletion

theorem outside_mean_square_of_theta_models {q₀ : ℕ}
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (σ ε : ℝ) (hσ : (1:ℝ)/20<σ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(D : ℕ) (Z : ℝ),1≤Z → b*Z≤D →
      ∀T : Finset ActualEisensteinCubic.O,
      (∀z∈T,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Z^(1+σ)) →
      (∀z∈T,z≠0) →
      (∑z∈T,‖idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
        (outside_good S D hbad) χ (fun n=>W (n/Z)) z‖^2)≤C*Z*(Z^(1+σ))*Z^ε :=
  outside_mean_square_of_canonical_density_at_radius χ S hbad hSp
    (hasInitialCanonicalDensityAtRadius_of_theta χ S hSp hbad ρ q levelBound hρ hq hlevel hmodels)
    W a b ha hs hW σ ε hσ hε

end InitialMeanSquare

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

lemma cuspBarrierField_local_model (p : SpatialCoordinates) (hp : 0<p 2) :
    (cuspBarrierField 2 3 =ᶠ[𝓝 p] (fun _ => 1)) ∨
    ∃x : FullCuspClasses,1<rowHeight (fullCuspRow x) p ∧
      cuspBarrierField 2 3 =ᶠ[𝓝 p] (fun q => 1+cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) q)) := by
  by_cases hx : ∃x : FullCuspClasses,1<rowHeight (fullCuspRow x) p
  · obtain ⟨x,hx⟩ := hx
    refine Or.inr ⟨x,hx,?_⟩
    have hc := (rowHeight_contDiffAt _ (fullCuspRow_ne_zero x) p hp).continuousAt
    filter_upwards [hc.eventually_const_lt hx,(continuous_apply 2).continuousAt.eventually_const_lt hp] with q hq hpos
    change 1+fullCuspProfileField (cuspBarrierProfile 2 3) q=_
    rw [fullCuspProfileField_eq _ q hpos,fullCuspProfileSum_eq_single _
      (fun v hv => cuspBarrierProfile_zero 2 3 (by norm_num) v (by linarith)) _ x
        (by rwa [←fullCuspRow_height x q hpos]),←fullCuspRow_height x q hpos]
  · left
    obtain ⟨T,hT⟩ := fullCuspRows_locally_finite p hp
    have hsmall : ∀ᶠq in 𝓝 p,∀x∈T,rowHeight (fullCuspRow x) q<2 := by
      rw [eventually_all_finset]
      intro x hxT
      apply (rowHeight_contDiffAt _ (fullCuspRow_ne_zero x) p hp).continuousAt.eventually_lt_const
      have hn : rowHeight (fullCuspRow x) p≤1 := not_lt.mp (fun h => hx ⟨x,h⟩)
      linarith
    filter_upwards [hT,hsmall] with q hq hqT
    change 1+fullCuspProfileField (cuspBarrierProfile 2 3) q=1
    have hz : ∀x : FullCuspClasses,cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) q)=0 := by
      intro x
      apply cuspBarrierProfile_zero 2 3 (by norm_num)
      by_cases hmem : x∈T
      · exact (hqT x hmem).le
      · exact (hq x hmem).le.trans (by norm_num)
    simp only [fullCuspProfileField,hz,tsum_zero,add_zero]

lemma cuspBarrierProfile_log_derivative_bound :
    ∃D : ℝ,0≤D ∧ ∀v : ℝ,1<v→
      |v*deriv (cuspBarrierProfile 2 3) v|≤D*(1+cuspBarrierProfile 2 3 v) := by
  have hd := (contDiff_infty_iff_deriv.mp (cuspBarrierProfile_smooth 2 3)).2.continuous
  obtain ⟨C,hC⟩ := ((isCompact_Icc : IsCompact (Set.Icc (1:ℝ) 3)).image hd.abs).bddAbove
  let D := max 1 (3*max C 0)
  have hD : 0≤D := le_trans (by norm_num) (le_max_left _ _)
  refine ⟨D,hD,fun v hv => ?_⟩
  by_cases hhigh : 3<v
  · have he : cuspBarrierProfile 2 3 =ᶠ[𝓝 v] (fun x => x-1) := by
      filter_upwards [Ioi_mem_nhds hhigh] with x hx
      rw [cuspBarrierProfile,cuspTransition_one 2 3 x (by norm_num) hx.le,one_mul]
    have hder : deriv (cuspBarrierProfile 2 3) v=1 := by rw [he.deriv_eq]; simp
    rw [hder,mul_one,abs_of_pos (by linarith),he.self_of_nhds]
    have h := mul_le_mul_of_nonneg_right (le_max_left 1 (3*max C 0)) (show 0≤v by linarith)
    dsimp only [D]
    nlinarith
  · have hCv : |deriv (cuspBarrierProfile 2 3) v|≤max C 0 :=
      (hC (Set.mem_image_of_mem _ (show v∈Set.Icc (1:ℝ) 3 from ⟨hv.le,not_lt.mp hhigh⟩))).trans (le_max_left _ _)
    have h1 : |v*deriv (cuspBarrierProfile 2 3) v|≤3*max C 0 := by
      rw [abs_mul,abs_of_pos (by linarith)]
      exact mul_le_mul (not_lt.mp hhigh) hCv (abs_nonneg _) (by positivity)
    have hphi := cuspBarrierProfile_nonneg 2 3 (by norm_num) (by norm_num) v
    exact (h1.trans (le_max_right _ _)).trans (by nlinarith)

lemma cuspBarrierField_scaled_deriv_bound :
    ∃D : ℝ,0≤D ∧ ∀p : SpatialCoordinates,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*deriv (axisSlice (fun q => (cuspBarrierField 2 3 q:ℂ)) p j) (p j)‖≤
        D*cuspBarrierField 2 3 p := by
  obtain ⟨D,hD,hbound⟩ := cuspBarrierProfile_log_derivative_bound
  refine ⟨D,hD,fun p hp j => ?_⟩
  have ht : Tendsto (fun t => Function.update p j t) (𝓝 (p j)) (𝓝 p) := by
    simpa only [Function.update_eq_self] using ((continuous_axis_update p j).continuousAt (x := p j)).tendsto
  rcases cuspBarrierField_local_model p hp with hz | ⟨x,hx,he⟩
  · have hzCast : (fun q => (cuspBarrierField 2 3 q:ℂ)) =ᶠ[𝓝 p] (fun _ => (1:ℂ)) :=
      hz.mono (fun q hq => congrArg (fun v : ℝ => (v:ℂ)) hq)
    have hzC := hzCast.comp_tendsto ht
    change axisSlice (fun q => (cuspBarrierField 2 3 q:ℂ)) p j =ᶠ[𝓝 (p j)] (fun _ => (1:ℂ)) at hzC
    rw [hzC.deriv_eq,deriv_const,mul_zero,norm_zero,hz.self_of_nhds,mul_one]
    exact hD
  · have heCast : (fun q => (cuspBarrierField 2 3 q:ℂ)) =ᶠ[𝓝 p]
        (fun q => ((1+cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) q):ℝ):ℂ)) :=
      he.mono (fun q hq => congrArg (fun v : ℝ => (v:ℂ)) hq)
    have heC := heCast.comp_tendsto ht
    change axisSlice (fun q => (cuspBarrierField 2 3 q:ℂ)) p j =ᶠ[𝓝 (p j)]
      (fun t => ((1+cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) (Function.update p j t)):ℝ):ℂ)) at heC
    rw [heC.deriv_eq]
    simp only [Complex.ofReal_add,Complex.ofReal_one]
    rw [deriv_const_add]
    have hpF := (rowProfile_axis_derivatives (fun v => (cuspBarrierProfile 2 3 v:ℂ))
      (fun v hv => Complex.ofRealCLM.contDiff.contDiffAt.comp v (cuspBarrierProfile_smooth 2 3).contDiffAt)
      (fullCuspRow x) (fullCuspRow_ne_zero x) p hp j).1
    change ‖(p 2:ℂ)*deriv (axisSlice (fun q => (cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) q):ℂ)) p j) (p j)‖≤_
    rw [hpF.deriv,cast_profile_deriv _ ((cuspBarrierProfile_smooth 2 3).differentiable (by simp))]
    have hid : (p 2:ℂ)*(((deriv (cuspBarrierProfile 2 3) (rowHeight (fullCuspRow x) p):ℝ):ℂ)*
        (rowHeight (fullCuspRow x) p:ℂ)*(rowLogD (fullCuspRow x) p j:ℂ))=
        ((p 2*rowLogD (fullCuspRow x) p j:ℝ):ℂ)*
        ((rowHeight (fullCuspRow x) p*deriv (cuspBarrierProfile 2 3) (rowHeight (fullCuspRow x) p):ℝ):ℂ) := by
      push_cast
      ring
    rw [hid,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
    apply (mul_le_of_le_one_left (abs_nonneg _) (rowLogD_hyperbolic_bound _ (fullCuspRow_ne_zero x) p hp j)).trans
    rw [he.self_of_nhds]
    exact hbound _ hx

lemma kernelBarrier_scaled_fderiv_bound :
    ∃D : ℝ,0≤D ∧ ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (fun q => (kernelQuotientBarrier 2 3 (kernelEuclideanProjection q):ℂ)) p
        (euclideanCoordinateVector j)‖≤D*kernelQuotientBarrier 2 3 (kernelEuclideanProjection p) := by
  obtain ⟨D,hD,hbound⟩ := cuspBarrierField_scaled_deriv_bound
  refine ⟨D,hD,fun p hp j => ?_⟩
  let f : EuclideanSpatial→ℂ := fun q => (kernelQuotientBarrier 2 3 (kernelEuclideanProjection q):ℂ)
  have hf : ∀q,0<q 2→ContDiffAt ℝ ∞ f q := fun q hq =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp q
      (cuspBarrier_euclidean_contDiffAt 2 3 (by norm_num) (by norm_num) q hq)
  have he : ∀q : SpatialCoordinates,0<q 2→ f (WithLp.toLp 2 q)=(cuspBarrierField 2 3 q:ℂ) := by
    intro q hq
    exact congrArg Complex.ofReal (cuspBarrier_euclidean_eq 2 3 (WithLp.toLp 2 q) hq)
  have ha := axisSlice_eventuallyEq_of_positive _ _ he p.ofLp hp j
  change ‖(p 2:ℂ)*fderiv ℝ f p (euclideanCoordinateVector j)‖≤_
  rw [←(euclideanAxisSlice_derivatives f hf p hp j).1,ha.deriv_eq]
  change _≤D*cuspBarrier 2 3 (euclideanToHyperbolic p)
  rw [cuspBarrier_euclidean_eq 2 3 p hp]
  exact hbound p.ofLp hp j

lemma kernelBarrier_scaled_real_fderiv_bound :
    ∃D : ℝ,0≤D ∧ ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      |p 2*fderiv ℝ (fun q => kernelQuotientBarrier 2 3 (kernelEuclideanProjection q)) p
        (euclideanCoordinateVector j)|≤D*kernelQuotientBarrier 2 3 (kernelEuclideanProjection p) := by
  obtain ⟨D,hD,hbound⟩ := kernelBarrier_scaled_fderiv_bound
  refine ⟨D,hD,fun p hp j => ?_⟩
  have hphi := (cuspBarrier_euclidean_contDiffAt 2 3 (by norm_num) (by norm_num) p hp).differentiableAt (by simp)
  have he := (Complex.ofRealCLM.hasFDerivAt.comp p hphi.hasFDerivAt).fderiv
  have hh := hbound p hp j
  change ‖(p 2:ℂ)*fderiv ℝ (Complex.ofRealCLM ∘ (fun q => cuspBarrier 2 3 (euclideanToHyperbolic q))) p
      (euclideanCoordinateVector j)‖≤_ at hh
  rw [he] at hh
  simpa only [ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,←Complex.ofReal_mul,
    Complex.norm_real,Real.norm_eq_abs] using! hh

lemma kernelExhaustionProfile_euler_bounded :
    ∃C : ℝ,0≤C ∧ ∀n : ℕ,∀v : ℝ,|v*deriv (kernelExhaustionProfile n) v|≤C := by
  obtain ⟨C,hC,hbound⟩ := cuspTransition_euler_bounded 1 2 (by norm_num)
  refine ⟨C,hC,fun n v => ?_⟩
  let c : ℝ := (n:ℝ)+1
  have hc : c≠0 := by dsimp [c]; positivity
  have hd := (hasDerivAt_const v (1:ℝ)).sub
    (((cuspTransition_contDiff 1 2).differentiable (by simp) (v/c)).hasDerivAt.comp v
      ((hasDerivAt_id v).div_const c))
  change HasDerivAt (kernelExhaustionProfile n) (0-deriv (cuspTransition 1 2) (v/c)*(1/c)) v at hd
  rw [hd.deriv]
  have he : v*(0-deriv (cuspTransition 1 2) (v/c)*(1/c))= -(v/c*deriv (cuspTransition 1 2) (v/c)) := by ring
  rw [he,abs_neg]
  exact hbound (v/c)

lemma kernelExhaustionCutoff_scaled_fderiv_bound :
    ∃C : ℝ,0≤C ∧ ∀n : ℕ,∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (fun q => (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)) p
        (euclideanCoordinateVector j)‖≤C := by
  obtain ⟨D,hD,hgrad⟩ := kernelBarrier_scaled_real_fderiv_bound
  obtain ⟨B,hB,hprofile⟩ := kernelExhaustionProfile_euler_bounded
  refine ⟨D*B,mul_nonneg hD hB,fun n p hp j => ?_⟩
  let phi : EuclideanSpatial→ℝ := fun q => kernelQuotientBarrier 2 3 (kernelEuclideanProjection q)
  have hphi : DifferentiableAt ℝ phi p :=
    (cuspBarrier_euclidean_contDiffAt 2 3 (by norm_num) (by norm_num) p hp).differentiableAt (by simp)
  have hP := ((kernelExhaustionProfile_smooth n).differentiable (by simp) (phi p)).hasDerivAt
  have hd := (hP.ofReal_comp.hasFDerivAt.comp p hphi.hasFDerivAt).fderiv
  change ‖(p 2:ℂ)*fderiv ℝ ((fun v => (kernelExhaustionProfile n v:ℂ)) ∘ phi) p
    (euclideanCoordinateVector j)‖≤D*B
  rw [hd]
  change ‖(p 2:ℂ)*((fderiv ℝ phi p (euclideanCoordinateVector j):ℝ) •
    ((deriv (kernelExhaustionProfile n) (phi p):ℝ):ℂ))‖≤D*B
  rw [Complex.real_smul,←Complex.ofReal_mul,←Complex.ofReal_mul,Complex.norm_real,Real.norm_eq_abs]
  calc
    |p 2*(fderiv ℝ phi p (euclideanCoordinateVector j)*deriv (kernelExhaustionProfile n) (phi p))|
      = |p 2*fderiv ℝ phi p (euclideanCoordinateVector j)| *|deriv (kernelExhaustionProfile n) (phi p)| := by rw [←abs_mul]; congr 1; ring
    _ ≤ (D*phi p)*|deriv (kernelExhaustionProfile n) (phi p)| :=
      mul_le_mul_of_nonneg_right (hgrad p hp j) (abs_nonneg _)
    _ = D*|phi p*deriv (kernelExhaustionProfile n) (phi p)| := by
      rw [abs_mul,abs_of_nonneg (le_trans zero_le_one (kernelQuotientBarrier_one_le 2 3 (by norm_num) (by norm_num) _))]
      ring
    _ ≤ D*B := mul_le_mul_of_nonneg_left (hprofile n (phi p)) hD

lemma kernelExhaustionCutoff_fderiv_eventually_zero (p : EuclideanSpatial) (hp : 0<p 2) :
    ∀ᶠn : ℕ in atTop,
      fderiv ℝ (fun q => (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)) p=0 := by
  have hc : ContinuousAt kernelEuclideanProjection p :=
    (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp
      (euclideanToHyperbolic_contMDiffAt p hp).continuousAt
  filter_upwards [kernelExhaustionCutoff_eventually_one_near (kernelEuclideanProjection p)] with n hn
  have he := hn.comp_tendsto hc
  have heC : (fun q => (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)) =ᶠ[𝓝 p]
      (fun _ => (1:ℂ)) := he.mono (fun q hq => congrArg (fun v : ℝ => (v:ℂ)) hq)
  rw [heC.fderiv_eq]
  simp

lemma kernelExhaustionCutoff_energy_density_bound :
    ∃C : ℝ,0≤C ∧ ∀n : ℕ,∀p : EuclideanSpatial,0<p 2→
      (∑j : Fin 3,‖(p 2:ℂ)*fderiv ℝ (fun q => (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)) p
        (euclideanCoordinateVector j)‖^2)≤C := by
  obtain ⟨D,hD,hbound⟩ := kernelExhaustionCutoff_scaled_fderiv_bound
  refine ⟨3*D^2,by positivity,fun n p hp => ?_⟩
  calc
    _ ≤ ∑j : Fin 3,D^2 := Finset.sum_le_sum (fun j hj =>
      (sq_le_sq₀ (norm_nonneg _) hD).mpr (hbound n p hp j))
    _ = 3*D^2 := by simp

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace SixthPowerAverage
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open EisensteinSchwartzPoisson hiding O
open IdealMobiusDivisorSum hiding O
open ConcreteTraceCRT ShortDraftHeckeBridge
open QuadraticInitialBound hiding O

def totientDensity (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  ∏ P ∈ primeSupport I, (1-(1:ℂ)/(Ideal.absNorm P:ℂ))

theorem idealSupport_card (F : Finset (Ideal ActualEisensteinCubic.O)) {I : Ideal ActualEisensteinCubic.O} (hI : I∈F) :
    (idealSupport F I).card=(primeSupport I).card := by
  rw [primeSupport,←idealSupport_image_eq_factors F hI]
  exact (Finset.card_image_iff.mpr (fun _ _ _ _ h => Subtype.val_injective h)).symm

theorem idealSupport_density (F : Finset (Ideal ActualEisensteinCubic.O)) {I : Ideal ActualEisensteinCubic.O} (hI : I∈F) :
    (∏ i ∈ idealSupport F I, (1-(1:ℂ)/(Ideal.absNorm i.val:ℂ)))=totientDensity I := by
  rw [totientDensity, primeSupport, ←idealSupport_image_eq_factors F hI,
    Finset.prod_image]
  exact fun _ _ _ _ h => Subtype.val_injective h

theorem idealSexticRow_sixth_mask
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    (I : Ideal ActualEisensteinCubic.O) (b : ActualEisensteinCubic.O) :
    idealSexticRow F hF hg I (b^6)=
      rowCoprimeMask (fun i : primePool F => i.val) (idealSupport F I) b := by
  let : ∀i : primePool F,(i.val).IsMaximal := primePool_maximal F hF
  exact finiteSquarefreeRow_sixth_power _ _ _ _

theorem idealSexticRow_sixth_radial_summable
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    (I : Ideal ActualEisensteinCubic.O) (V : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y) :
    Summable (fun b : ActualEisensteinCubic.O => idealSexticRow F hF hg I (b^6)*V (‖eisEmbedding b‖^2/Y)) := by
  have hs : Summable (fun b : ActualEisensteinCubic.O => V (‖eisEmbedding b‖^2/Y)) := by
    simpa only [scaledRadialTest_apply] using
      (actual_eisenstein_summable_norm (scaledRadialTest V Y hY)).of_norm
  simp_rw [idealSexticRow_sixth_mask]
  convert hs.indicator {b : ActualEisensteinCubic.O | ¬∃i∈idealSupport F I,b∈i.val} using 1
  funext b
  by_cases hb : ∃i∈idealSupport F I,b∈i.val
  · rw [Set.indicator_of_notMem (show b∉{b : ActualEisensteinCubic.O | ¬∃i∈idealSupport F I,b∈i.val} from fun hn=>hn hb)]
    simp only [rowCoprimeMask,ite_eq_left hb,zero_mul]
  · rw [Set.indicator_of_mem hb]
    simp only [rowCoprimeMask,ite_eq_right hb,one_mul]

theorem idealSexticRow_sixth_average
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    {I : Ideal ActualEisensteinCubic.O} (hI : I∈F) (V : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y) :
    (∑'b : ActualEisensteinCubic.O,idealSexticRow F hF hg I (b^6)*V (‖eisEmbedding b‖^2/Y))=
      (Y:ℂ)*paperRadialFourier V 0*totientDensity I+
      maskedPrincipalRemainder (fun i : primePool F => i.val) (idealSupport F I) V Y := by
  let : ∀i : primePool F,(i.val).IsMaximal := primePool_maximal F hF
  simp_rw [idealSexticRow_sixth_mask]
  rw [masked_principal_radial_poisson_zero_split _ Subtype.val_injective _ V Y hY,
    idealSupport_density F hI]

theorem idealRowSum_sixth_average {q : ℕ}
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    (χ : DirichletCharacter ℂ q) (W : ℕ→ℂ)
    (V : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y) :
    (∑'b : ActualEisensteinCubic.O, V (‖eisEmbedding b‖^2/Y)*idealRowSum F hF hg χ W (b^6))=
      (Y:ℂ)*paperRadialFourier V 0*
        (∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*totientDensity I)+
      ∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
        maskedPrincipalRemainder (fun i : primePool F => i.val) (idealSupport F I) V Y := by
  have he (b : ActualEisensteinCubic.O) : V (‖eisEmbedding b‖^2/Y)*idealRowSum F hF hg χ W (b^6)=
      ∑I∈F,(baseChangeWeight χ I*W (Ideal.absNorm I))*
        (idealSexticRow F hF hg I (b^6)*V (‖eisEmbedding b‖^2/Y)) := by
    rw [idealRowSum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I hI
    ring
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun I _ =>
    (idealSexticRow_sixth_radial_summable F hF hg I V Y hY).mul_left _)]
  simp_rw [tsum_mul_left]
  rw [show (∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
      ∑'b : ActualEisensteinCubic.O,idealSexticRow F hF hg I (b^6)*V (‖eisEmbedding b‖^2/Y))=
      ∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
        ((Y:ℂ)*paperRadialFourier V 0*totientDensity I+
          maskedPrincipalRemainder (fun i : primePool F => i.val) (idealSupport F I) V Y) by
    apply Finset.sum_congr rfl
    intro I hI
    rw [idealSexticRow_sixth_average F hF hg hI V Y hY]]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  ring

theorem sixth_average_remainder_bound {q : ℕ}
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (χ : DirichletCharacter ℂ q) (W : ℕ→ℂ)
    (V : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y) :
    ‖∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
        maskedPrincipalRemainder (fun i : primePool F => i.val) (idealSupport F I) V Y‖≤
      ∑I∈F,‖W (Ideal.absNorm I)‖*(2:ℝ)^(primeSupport I).card*pvControl V := by
  let : ∀i : primePool F,(i.val).IsMaximal := primePool_maximal F hF
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  have hr := maskedPrincipalRemainder_uniform (fun i : primePool F=>i.val)
    (idealSupport F I) V Y hY
  rw [idealSupport_card F hI] at hr
  rw [norm_mul,norm_mul]
  calc
    _≤(1*‖W (Ideal.absNorm I)‖)*((2:ℝ)^(primeSupport I).card*pvControl V) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (baseChangeWeight_norm_le_one χ I) (norm_nonneg _))
        hr (norm_nonneg _) (by positivity)
    _=_ := by ring

theorem sixth_power_fiber_card (s : Finset ActualEisensteinCubic.O) (z : ActualEisensteinCubic.O) :
    (s.filter (fun b=>b^6=z)).card≤6 := by
  calc
    _≤(Polynomial.nthRoots 6 z).toFinset.card := by
      apply Finset.card_le_card
      intro b hb
      exact Multiset.mem_toFinset.mpr
        ((Polynomial.mem_nthRoots (by norm_num : 0<6)).mpr (Finset.mem_filter.mp hb).2)
    _≤(Polynomial.nthRoots 6 z).card := Multiset.toFinset_card_le _
    _≤6 := Polynomial.card_nthRoots 6 z

theorem sixth_power_average_cauchy (s : Finset ActualEisensteinCubic.O) (V A : ActualEisensteinCubic.O→ℂ)
    (hV : ∀b∈s,‖V b‖≤1) :
    ‖∑b∈s,V b*A (b^6)‖^2≤
      6*s.card*∑z∈s.image (fun b=>b^6),‖A z‖^2 := by
  have hc := DescentWeightedCauchy.weighted_cauchy_sq s V (fun b=>A (b^6)) (fun _=>1)
  simp only [star_one,mul_one,norm_one,one_pow,mul_one] at hc
  have hp := DescentWeightedCauchy.weighted_energy_pushforward s (s.image (fun b=>b^6))
    (fun b=>b^6) V A (fun _=>6) (fun b hb=>Finset.mem_image.mpr ⟨b,hb,rfl⟩) (by
      intro z hz
      calc
        _≤∑b∈s with b^6=z,(1:ℝ) := Finset.sum_le_sum (fun b hb=>hV b (Finset.mem_filter.mp hb).1)
        _=(s.filter (fun b=>b^6=z)).card := by simp
        _≤6 := by exact_mod_cast sixth_power_fiber_card s z)
  have hv : (∑b∈s,‖V b‖)≤s.card := by
    simpa using Finset.sum_le_sum (fun b hb=>hV b hb)
  apply hc.trans
  calc
    _≤(∑z∈s.image (fun b=>b^6),6*‖A z‖^2)*(s.card:ℝ) :=
      mul_le_mul hp hv (Finset.sum_nonneg (fun _ _=>norm_nonneg _))
        (Finset.sum_nonneg (fun _ _=>by positivity))
    _=_ := by rw [←Finset.mul_sum]; ring

end SixthPowerAverage

end

end OAI
end OAIOriginalModule0253

/-! Original module: OAI.NumberTheory.DirichletL.Mellin.SixthPowerAverage
Source SHA256: 5e83e8741e30c8163745b493223c3018cf7146f565f49e8520fd75427818aa56
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0254


namespace OAI

noncomputable section

namespace SixthPowerAverage

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

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Metric
open EisensteinSchwartzPoisson

theorem exists_averaging_test :
    ∃V : 𝓢(ℝ,ℂ),
      (∀x,‖V x‖≤1) ∧
      (Function.support (V:ℝ→ℂ)⊆Set.Icc ((1:ℝ)/2) 1) ∧
      V 0=0 ∧ paperRadialFourier V 0≠0 := by
  let f : ContDiffBump ((3:ℝ)/4) := ⟨1/8,1/4,by norm_num,by norm_num⟩
  let g : ℝ→ℂ := fun x=>(f x:ℂ)
  have hgs : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp f.contDiff
  have hsupport : Function.support g⊆Set.Icc ((1:ℝ)/2) 1 := by
    intro x hx
    have hf : f x≠0 := by simpa only [g,Function.mem_support,ne_eq,Complex.ofReal_eq_zero] using hx
    have hh : |x-(3:ℝ)/4|<1/4 := by
      have hi : x∈Function.support (f:ℝ→ℝ) := hf
      rw [f.support_eq] at hi
      simpa only [Metric.mem_ball,Real.dist_eq,f] using hi
    exact ⟨by linarith [(abs_lt.mp hh).1],by linarith [(abs_lt.mp hh).2]⟩
  have hgc : HasCompactSupport g :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupport
  let V : 𝓢(ℝ,ℂ) := hgc.toSchwartzMap hgs
  have hz : V 0=0 := by
    by_contra h
    have hh := (hsupport h).1
    norm_num at hh
  refine ⟨V,?_,hsupport,hz,?_⟩
  · intro x
    change ‖(f x:ℂ)‖≤1
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg f.nonneg]
    exact f.le_one
  · rw [paperRadialFourier_zero_eq_halfline]
    have he : (∫x : ℝ in Set.Ioi 0,(V x))=∫x : ℝ,(f x:ℂ) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      by_contra hn
      have hp := (hsupport hn).1
      simp only [Set.mem_Ioi,not_lt] at hx
      linarith
    rw [he,integral_complex_ofReal]
    apply mul_ne_zero
    · apply div_ne_zero
      · exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
      · exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<3))
    · have hfint : Integrable (f:ℝ→ℝ) := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
      have hfpos : 0 < ∫x : ℝ,f x := by
        apply (integral_pos_iff_support_of_nonneg f.nonneg' hfint).mpr
        rw [f.support_eq]
        exact measure_ball_pos volume _ f.rOut_pos
      exact_mod_cast hfpos.ne'

end

section

open scoped BigOperators Classical
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open ShortDraftHeckeBridge

lemma prime_coprime_span_iff (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (b : ActualEisensteinCubic.O) : IsCoprime P (Ideal.span {b}) ↔ b∉P := by
  rw [Ideal.isCoprime_iff_codisjoint,
    ←(Ideal.isMaximal_def.mp (inferInstance : P.IsMaximal)).not_le_iff_codisjoint,
    Ideal.span_singleton_le_iff_mem]

lemma squarefree_sixth_row_coprime
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    {I : Ideal ActualEisensteinCubic.O} (hI : I∈F) (hsq : Squarefree I)
    (b : ActualEisensteinCubic.O) :
    idealSexticRow F hF hg I (b^6)=if IsCoprime I (Ideal.span {b}) then 1 else 0 := by
  let : ∀i : primePool F,(i.val).IsMaximal:=primePool_maximal F hF
  have hc : IsCoprime I (Ideal.span {b}) ↔ ¬∃i∈idealSupport F I,b∈i.val := by
    conv_lhs => rw [←idealSupport_product_eq F hI hsq]
    rw [IsCoprime.prod_left_iff]
    simp only [prime_coprime_span_iff,not_exists,not_and]
  rw [idealSexticRow_sixth_mask,hc]
  by_cases hn : ∃i∈idealSupport F I,b∈i.val <;> simp [rowCoprimeMask,hn]

theorem idealRowSum_sixth_eq_coprime_sum {q : ℕ}
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    (χ : DirichletCharacter ℂ q) (W : ℕ→ℂ) (b : ActualEisensteinCubic.O) :
    idealRowSum F hF hg χ W (b^6)=
      ∑I∈F with IsCoprime I (Ideal.span {b}),baseChangeWeight χ I*W (Ideal.absNorm I) := by
  rw [idealRowSum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hsq : Squarefree I
  · rw [squarefree_sixth_row_coprime F hF hg hI hsq b]
    split_ifs <;> simp
  · rw [ConcretePrimeRowBridge.baseChangeWeight_zero_of_not_squarefree χ I hsq]
    simp

end

section

open scoped BigOperators Classical SchwartzMap ContDiff

section
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open EisensteinSchwartzPoisson hiding O
open IdealMobiusDivisorSum hiding O
open ConcreteTraceCRT ShortDraftHeckeBridge
open QuadraticInitialBound hiding O

def averagingRows (Y : ℝ) : Finset ActualEisensteinCubic.O := rowNormDisk ⌊Y⌋₊

theorem mem_averagingRows {Y : ℝ} {b : ActualEisensteinCubic.O} (hY : 0≤Y) :
    b∈averagingRows Y ↔ b≠0 ∧ ‖eisEmbedding b‖^2≤Y := by
  rw [averagingRows,mem_rowNormDisk]
  have hz : 0<Ideal.absNorm (Ideal.span {b}:Ideal ActualEisensteinCubic.O) ↔ b≠0 := by
    rw [Nat.pos_iff_ne_zero,ne_eq,Ideal.absNorm_eq_zero_iff,Ideal.span_singleton_eq_bot]
  rw [hz,Nat.le_floor_iff hY,←eisEmbedding_norm_sq_eq_absNorm_span]

theorem averagingRows_card (Y : ℝ) (hY : 1≤Y) :
    ((averagingRows Y).card:ℝ)≤128*Y :=
  DescentFiberCost.finite_element_count_real _ Y hY
    (fun b hb=>(mem_averagingRows (by linarith)).mp hb |>.2)

theorem averagingRows_power_norm (Y : ℝ) (hY : 1≤Y)
    {z : ActualEisensteinCubic.O} (hz : z∈(averagingRows Y).image (fun b=>b^6)) :
    z≠0 ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤Y^6 := by
  obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp hz
  have hh:=(mem_averagingRows (by linarith : (0:ℝ)≤Y)).mp hb
  refine ⟨pow_ne_zero _ hh.1,?_⟩
  rw [←eisEmbedding_norm_sq_eq_absNorm_span,map_pow,norm_pow,
    ←pow_mul,show (6:ℕ)*2=2*6 by omega,pow_mul]
  exact pow_le_pow_left₀ (sq_nonneg _) hh.2 _

theorem average_tsum_eq_finite (V : 𝓢(ℝ,ℂ))
    (hV : Function.support (V:ℝ→ℂ)⊆Set.Icc ((1:ℝ)/2) 1)
    (hV0 : V 0=0) (Y : ℝ) (hY : 0<Y) (A : ActualEisensteinCubic.O→ℂ) :
    (∑'b : ActualEisensteinCubic.O,V (‖eisEmbedding b‖^2/Y)*A (b^6))=
      ∑b∈averagingRows Y,V (‖eisEmbedding b‖^2/Y)*A (b^6) := by
  apply tsum_eq_sum
  intro b hb
  have hz : V (‖eisEmbedding b‖^2/Y)=0 := by
    by_contra hv
    apply hb
    apply (mem_averagingRows hY.le).mpr
    refine ⟨?_,?_⟩
    · intro he
      simp only [he,map_zero,norm_zero,zero_pow (by decide : (2:ℕ)≠0),zero_div,hV0] at hv
      exact hv trivial
    · exact (div_le_one hY).mp (hV hv).2
  rw [hz,zero_mul]

theorem average_tsum_cauchy (V : 𝓢(ℝ,ℂ))
    (hV : ∀x,‖V x‖≤1)
    (hs : Function.support (V:ℝ→ℂ)⊆Set.Icc ((1:ℝ)/2) 1)
    (hV0 : V 0=0) (Y : ℝ) (hY : 1≤Y) (A : ActualEisensteinCubic.O→ℂ) :
    ‖∑'b : ActualEisensteinCubic.O,V (‖eisEmbedding b‖^2/Y)*A (b^6)‖^2≤
      768*Y*∑z∈(averagingRows Y).image (fun b=>b^6),‖A z‖^2 := by
  rw [average_tsum_eq_finite V hs hV0 Y (by linarith) A]
  apply (sixth_power_average_cauchy _ _ _ (fun b hb=>hV _)).trans
  have hc:=averagingRows_card Y hY
  nlinarith [Finset.sum_nonneg (s:=(averagingRows Y).image (fun b=>b^6))
    (fun z _=>sq_nonneg ‖A z‖)]

theorem average_remainder_small_power (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ {q : ℕ}
      (F : Finset (Ideal ActualEisensteinCubic.O)) (_hF : ∀I∈F,I≠⊥)
      (χ : DirichletCharacter ℂ q) (W : ℕ→ℂ)
      (V : 𝓢(ℝ,ℂ)) (Y lengthScale G : ℝ),0<Y → 1≤lengthScale → 0≤G →
      (∀n,‖W n‖≤G) → (∀I∈F,W (Ideal.absNorm I)≠0→(Ideal.absNorm I:ℝ)≤lengthScale) →
      ‖∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
        maskedPrincipalRemainder (fun i : primePool F=>i.val) (idealSupport F I) V Y‖≤
      C*G*pvControl V*lengthScale^(1+ε) := by
  obtain ⟨C,hC,hp⟩:=SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨128*C,by positivity,?_⟩
  intro q F hF χ W V Y lengthScale G hY hL hG hW hnorm
  apply (sixth_average_remainder_bound F hF χ W V Y hY).trans
  let T:=F.filter (fun I=>W (Ideal.absNorm I)≠0)
  have he : (∑I∈F,‖W (Ideal.absNorm I)‖*(2:ℝ)^(primeSupport I).card*pvControl V)=
      ∑I∈T,‖W (Ideal.absNorm I)‖*(2:ℝ)^(primeSupport I).card*pvControl V := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro I hI hn
    have hz : W (Ideal.absNorm I)=0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hI,hh⟩)
    simp only [hz,norm_zero,zero_mul]
  have hc : (T.card:ℝ)≤128*lengthScale :=
    DescentFiberCost.finite_ideal_count_real T lengthScale hL
      (fun I hI=>hF I (Finset.mem_filter.mp hI).1)
      (fun I hI=>hnorm I (Finset.mem_filter.mp hI).1 (Finset.mem_filter.mp hI).2)
  rw [he]
  calc
    _≤∑I∈T,G*(C*lengthScale^ε)*pvControl V := by
      apply Finset.sum_le_sum
      intro I hI
      have hh:=Finset.mem_filter.mp hI
      have hb:=(hp I (hF I hh.1)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm I hh.1 hh.2) hε.le) hC.le)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (hW _) hb (by positivity) hG) (pvControl_nonneg V)
    _=(T.card:ℝ)*(G*(C*lengthScale^ε)*pvControl V) := by simp
    _≤128*lengthScale*(G*(C*lengthScale^ε)*pvControl V) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg (by positivity) (pvControl_nonneg V))
    _=(128*C)*G*pvControl V*lengthScale^(1+ε) := by
      rw [Real.rpow_add (by linarith : (0:ℝ)<lengthScale),Real.rpow_one]
      ring

theorem totient_sum_normalized_bound {q : ℕ}
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    (χ : DirichletCharacter ℂ q) (W : ℕ→ℂ)
    (V : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y) :
    Y*‖paperRadialFourier V 0‖*
      ‖∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*totientDensity I‖≤
      ‖∑'b : ActualEisensteinCubic.O,V (‖eisEmbedding b‖^2/Y)*idealRowSum F hF hg χ W (b^6)‖+
      ‖∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
        maskedPrincipalRemainder (fun i : primePool F=>i.val) (idealSupport F I) V Y‖ := by
  have he:=idealRowSum_sixth_average F hF hg χ W V Y hY
  have hh:=norm_sub_le (∑'b : ActualEisensteinCubic.O,V (‖eisEmbedding b‖^2/Y)*idealRowSum F hF hg χ W (b^6))
    (∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
      maskedPrincipalRemainder (fun i : primePool F=>i.val) (idealSupport F I) V Y)
  rw [he,add_sub_cancel_right,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY] at hh
  rwa [←he] at hh

end

open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open EisensteinSchwartzPoisson hiding O
open ConcreteTraceCRT ShortDraftHeckeBridge
open QuadraticInitialBound hiding O
open InitialMeanSquare
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalRowCompletion

theorem outside_totient_moebius_bound {q₀ : ℕ}
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(D : ℕ) (Z : ℝ),1≤Z → b*Z≤D →
      ‖∑I∈outsideIdealsUpTo S D,baseChangeWeight χ I*W ((Ideal.absNorm I:ℝ)/Z)*totientDensity I‖≤
        C*Z^((23:ℝ)/24+ε) := by
  obtain ⟨V,hV,hVs,hV0,hVhat⟩:=exists_averaging_test
  obtain ⟨Cm,hCm,hm⟩:=outside_mean_square_of_theta_models χ S hbad hSp ρ q levelBound hρ hq hlevel hmodels
    W a b ha hs hW ((1:ℝ)/10) (2*ε) (by norm_num) (by positivity)
  simp only [show (1:ℝ)+1/10=11/10 by norm_num] at hm
  obtain ⟨Ce,hCe,he⟩:=average_remainder_small_power ε hε
  have hWc : HasCompactSupport W := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs
  let Ws : 𝓢(ℝ,ℂ):=hWc.toSchwartzMap hW
  let G : ℝ:=SchwartzMap.seminorm ℝ 0 0 Ws
  let B : ℝ:=max 1 b
  let Err : ℝ:=Ce*G*pvControl V*B^(1+ε)
  let Avg : ℝ:=Real.sqrt (768*Cm)
  let C : ℝ:=(Avg+Err)/‖paperRadialFourier V 0‖
  have hG : 0≤G:=apply_nonneg _ _
  have hB : 1≤B:=le_max_left _ _
  have hErr : 0≤Err:=mul_nonneg (mul_nonneg (mul_nonneg hCe.le hG) (pvControl_nonneg V)) (by positivity)
  have hAvg : 0<Avg:=Real.sqrt_pos.mpr (by positivity)
  have hhat : 0<‖paperRadialFourier V 0‖:=norm_pos_iff.mpr hVhat
  refine ⟨C,div_pos (by linarith) hhat,?_⟩
  intro D Z hZ hD
  have hZp : 0<Z:=by linarith
  let Y : ℝ:=Z^((11:ℝ)/60)
  have hY : 1≤Y:=Real.one_le_rpow hZ (by norm_num)
  have hYp : 0<Y:=by linarith
  let F:=outsideIdealsUpTo S D
  let A : ActualEisensteinCubic.O→ℂ:=idealRowSum F (outsideIdealsUpTo_ne_bot S D)
    (outside_good S D hbad) χ (fun n=>W (n/Z))
  have hYpow : Y^6=Z^((11:ℝ)/10) := by
    dsimp only [Y]
    rw [←Real.rpow_mul_natCast hZp.le]
    norm_num
  have hms : (∑z∈(averagingRows Y).image (fun b=>b^6),‖A z‖^2)≤
      Cm*Z*Z^((11:ℝ)/10)*Z^(2*ε) := by
    apply hm D Z hZ hD
    · intro z hz
      have hn:=(averagingRows_power_norm Y hY hz).2
      simpa only [hYpow,show (1:ℝ)+1/10=11/10 by norm_num] using hn
    · intro z hz
      exact (averagingRows_power_norm Y hY hz).1
  have havg2:= (average_tsum_cauchy V hV hVs hV0 Y hY A).trans
    (mul_le_mul_of_nonneg_left hms (by positivity : 0≤768*Y))
  have heq : 768*Y*(Cm*Z*Z^((11:ℝ)/10)*Z^(2*ε))=
      (Avg*Z^((137:ℝ)/120+ε))^2 := by
    dsimp only [Y,Avg]
    rw [mul_pow,Real.sq_sqrt (by positivity : (0:ℝ)≤768*Cm),←Real.rpow_mul_natCast hZp.le]
    calc
      _ = (768*Cm)*(Z^((11:ℝ)/60)*Z^(1:ℝ)*Z^((11:ℝ)/10)*Z^(2*ε)) := by rw [Real.rpow_one];ring
      _ = (768*Cm)*Z^((11:ℝ)/60+1+11/10+2*ε) := by
        rw [←Real.rpow_add hZp,←Real.rpow_add hZp,←Real.rpow_add hZp]
      _ = _ := by congr 2 ; ring
  rw [heq] at havg2
  have havg : ‖∑'z : ActualEisensteinCubic.O,V (‖eisEmbedding z‖^2/Y)*A (z^6)‖≤
      Avg*Z^((137:ℝ)/120+ε) := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp havg2
  have herr : ‖∑I∈F,baseChangeWeight χ I*W ((Ideal.absNorm I:ℝ)/Z)*
      maskedPrincipalRemainder (fun i : primePool F=>i.val) (idealSupport F I) V Y‖≤Err*Z^(1+ε) := by
    have hbZ : 1≤B*Z:=by nlinarith [mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr hZ)]
    have hh:=he F (outsideIdealsUpTo_ne_bot S D) χ (fun n=>W (n/Z)) V Y (B*Z) G hYp hbZ hG
      (fun n=>Ws.norm_le_seminorm ℝ (n/Z)) (by
        intro I hI hn
        have hh:=(hs hn).2
        exact ((div_le_iff₀ hZp).mp hh).trans (mul_le_mul_of_nonneg_right (le_max_right 1 b) hZp.le))
    calc
      _≤Ce*G*pvControl V*(B*Z)^(1+ε):=hh
      _=Err*Z^(1+ε):=by rw [Real.mul_rpow (by linarith : 0≤B) hZp.le];dsimp only [Err];ring
  have hexponent : Z^(1+ε)≤Z^((137:ℝ)/120+ε) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hmain:=totient_sum_normalized_bound F (outsideIdealsUpTo_ne_bot S D)
    (outside_good S D hbad) χ (fun n=>W (n/Z)) V Y hYp
  have hbound : Y*‖paperRadialFourier V 0‖*
      ‖∑I∈F,baseChangeWeight χ I*W ((Ideal.absNorm I:ℝ)/Z)*totientDensity I‖≤
      (Avg+Err)*Z^((137:ℝ)/120+ε) := by
    apply hmain.trans
    have := add_le_add havg (herr.trans (mul_le_mul_of_nonneg_left hexponent hErr))
    simpa only [add_mul] using this
  have hzexp : Z^((137:ℝ)/120+ε)=Y*Z^((23:ℝ)/24+ε) := by
    dsimp only [Y]
    rw [←Real.rpow_add hZp]
    congr 1
    ring
  apply (mul_le_mul_iff_right₀ (mul_pos hYp hhat)).mp
