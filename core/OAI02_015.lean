  dsimp only
  exact sum_activeCubeLogBins S D b X _

theorem outsideCanonicalRow_reopened_binned
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ : ℝ)
    (hb : 0 ≤ b) (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t ≤ b) (hD : b*X ≤ D) :
    (Real.sqrt X : ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀ +
        ∑ j ∈ cubeLogRange b X,
          outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) Ψ m f z W X H₀ := by
  rw [outsideCanonicalRow_reopened_active S D hbad hSp Ψ m f z W hWc b X H₀ hb hX hW hD,
    outsideCanonicalBin_log_bins]

end CanonicalRowCompletion

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels

theorem nonzeroRowMajorantSum_exact_disk (P : ActualEisensteinCubic.O → ℂ) (K : ℝ) (hK : 0<K) :
    nonzeroRowMajorantSum P K=
      ∑z∈(firstFrequencyDisk (2*K)).erase 0,
        rowMajorant (‖eisEmbedding z‖^2/K)*(‖P z‖^2:ℝ) := by
  unfold nonzeroRowMajorantSum
  have hz (z : ActualEisensteinCubic.O) (hz : z∉(firstFrequencyDisk (2*K)).erase 0) :
      (if z=0 then 0 else rowMajorant (‖eisEmbedding z‖^2/K)*(‖P z‖^2:ℝ))=0 := by
    by_cases hzero : z=0
    · simp [hzero]
    have hn : z∉firstFrequencyDisk (2*K) := by
      intro hm
      exact hz (Finset.mem_erase.mpr ⟨hzero,hm⟩)
    have hlarge : 2<‖eisEmbedding z‖^2/K :=
      (lt_div_iff₀ hK).mpr (outside_firstFrequencyDisk (2*K) z hn)
    rw [ite_eq_right hzero,rowMajorant_zero _ hlarge,zero_mul]
  rw [tsum_eq_sum hz]
  apply Finset.sum_congr rfl
  intro z hz
  rw [ite_eq_right (Finset.mem_erase.mp hz).1]

def canonicalTerminalConstant (A M : ℝ) : ℝ :=
  2*128^4*SchwartzMap.seminorm ℝ 0 0 rowMajorant*(Real.exp A*M)^2

theorem canonicalTerminalConstant_nonneg (A M : ℝ) : 0≤canonicalTerminalConstant A M := by
  unfold canonicalTerminalConstant
  positivity

theorem fixedDepthRank_zero_iff (Z K : ℝ) (hZ : 1<Z) (hK : 0<K) :
    fixedDepthRank Z K=0 ↔ K≤1 := by
  rw [fixedDepthRank,Nat.ceil_eq_zero]
  constructor
  · intro h
    have hm := (div_le_iff₀ (Real.log_pos hZ)).mp h
    apply (Real.log_nonpos_iff hK.le).mp
    nlinarith
  · intro h
    apply (div_le_iff₀ (Real.log_pos hZ)).mpr
    have hm := (Real.log_nonpos_iff hK.le).mpr h
    nlinarith

theorem smallColumn_row_le_label (m : ActualEisensteinCubic.O) (hm : m≠0) (X F K : ℝ)
    (hX : X≤1) (hF : 0≤F) (hK : 0≤K)
    (hinv : K*‖eisEmbedding m‖^2≤X*F) : K≤F := by
  have hn := element_norm_ge_one m hm
  have h1 := mul_le_mul_of_nonneg_left hn hK
  have h2 := mul_le_mul_of_nonneg_right hX hF
  nlinarith

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem canonicalSmoothedEnergy_uniform_row_bound (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (H : Finset ι → ℂ) (F K D : ℝ)
    (hF : 1≤F) (hK : 1≤K) (_hD : 0≤D)
    (hI0 : ∀I∈labels,I≠⊥) (hIF : ∀I∈labels,(Ideal.absNorm I:ℝ)≤F)
    (hrow : ∀I∈labels,∀z,‖fixedChildRow p hp hcop hg pool Ψ m H
      (ConcretePrimeRowBridge.idealGenerator I) z‖≤D) :
    canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels H K≤
      2*128^2*SchwartzMap.seminorm ℝ 0 0 rowMajorant*F*K*D^2 := by
  have hK0 : 0<K := zero_lt_one.trans_le hK
  let R := (firstFrequencyDisk (2*K)).erase 0
  have hR : (R.card:ℝ)≤128*(2*K) := by
    apply DescentFiberCost.finite_element_count_real R (2*K) (by linarith)
    exact fun z hz=>(mem_firstFrequencyDisk (2*K) z).mp (Finset.mem_erase.mp hz).2
  have hI : (labels.card:ℝ)≤128*F := DescentFiberCost.finite_ideal_count_real labels F hF hI0 hIF
  have hm : 0≤SchwartzMap.seminorm ℝ 0 0 rowMajorant := by positivity
  unfold canonicalSmoothedEnergy
  simp_rw [nonzeroRowMajorantSum_exact_disk _ K hK0]
  rw [Complex.re_sum]
  calc
    _ ≤ ∑I∈labels,∑z∈R,SchwartzMap.seminorm ℝ 0 0 rowMajorant*D^2 := by
      apply Finset.sum_le_sum
      intro I hIL
      rw [Complex.re_sum]
      apply Finset.sum_le_sum
      intro z hz
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      exact mul_le_mul
        ((Complex.re_le_norm _).trans (rowMajorant.norm_le_seminorm ℝ _))
        (pow_le_pow_left₀ (norm_nonneg _) (hrow I hIL z) 2) (sq_nonneg _) hm
    _ = (labels.card:ℝ)*R.card*(SchwartzMap.seminorm ℝ 0 0 rowMajorant*D^2) := by simp; ring
    _ ≤ (128*F)*(128*(2*K))*(SchwartzMap.seminorm ℝ 0 0 rowMajorant*D^2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hI hR (Nat.cast_nonneg _) (by linarith)) (by positivity)
    _ = _ := by ring

theorem canonicalLogEnergy_subunit (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (V : ℝ → ℂ) (X K A : ℝ) (hX : 0<X)
    (hV : ∀s,V s≠0→|s|≤A) (hsmall : X*Real.exp A<1) :
    canonicalLogEnergy p hp hcop hg pool Ψ m labels V X K=0 := by
  have hcol (S : Finset ι) : V (columnLog p X S)=0 := by
    by_contra hn
    have hupper := columnLog_norm_upper p hp X A hX S ((le_abs_self _).trans (hV _ hn))
    have hlower := primeProductNorm_ge_one p hp S
    linarith
  have hrow (f y : ActualEisensteinCubic.O) : fixedChildRow p hp hcop hg pool Ψ m
      (fun S=>V (columnLog p X S)) f y=0 := by
    unfold fixedChildRow
    apply Finset.sum_eq_zero
    intro S hS
    simp only [secondChildColumn,hcol,mul_zero]
  simp only [canonicalLogEnergy,canonicalSmoothedEnergy,nonzeroRowMajorantSum,hrow,norm_zero,
    zero_pow (by decide : (2:ℕ)≠0),Complex.ofReal_zero,mul_zero,ite_self,tsum_zero,
    Finset.sum_const_zero,Complex.zero_re]

theorem canonicalLogEnergy_terminal
    (hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (V : ℝ → ℂ) (X F K A M : ℝ)
    (hX : 0<X) (hF : 1≤F) (hK : 1≤K) (hKF : K≤F) (hM : 0≤M)
    (hV : ∀s,‖V s‖≤M) (hVs : ∀s,V s≠0→|s|≤A)
    (hI0 : ∀I∈labels,I≠⊥) (hIF : ∀I∈labels,(Ideal.absNorm I:ℝ)≤F) :
    canonicalLogEnergy p hp hcop hg pool Ψ m labels V X K≤canonicalTerminalConstant A M*(X*F)^2 := by
  by_cases hscale : 1≤X*Real.exp A
  · have hcol : ∀S,V (columnLog p X S)≠0→primeProductNorm p S≤X*Real.exp A :=
      fun S hn=>columnLog_norm_upper p hp X A hX S ((le_abs_self _).trans (hVs _ hn))
    have hrow (I : Ideal ActualEisensteinCubic.O) (hI : I∈labels) (z : ActualEisensteinCubic.O) :
        ‖fixedChildRow p hp hcop hg pool Ψ m (fun S=>V (columnLog p X S))
          (ConcretePrimeRowBridge.idealGenerator I) z‖≤128*(X*Real.exp A)*M :=
      fixedChildRow_elementary p hp hcop hg hc hinj pool Ψ hΨ m _ z _ (X*Real.exp A) M hscale hM
        (fun S=>hV _) hcol
    have hb := canonicalSmoothedEnergy_uniform_row_bound p hp hcop hg pool Ψ m labels
      (fun S=>V (columnLog p X S)) F K (128*(X*Real.exp A)*M) hF hK (by positivity) hI0 hIF hrow
    change canonicalLogEnergy p hp hcop hg pool Ψ m labels V X K≤_ at hb
    calc
      _ ≤ 2*128^2*SchwartzMap.seminorm ℝ 0 0 rowMajorant*F*K*(128*(X*Real.exp A)*M)^2 := hb
      _ = canonicalTerminalConstant A M*X^2*F*K := by unfold canonicalTerminalConstant; ring
      _ ≤ canonicalTerminalConstant A M*X^2*F*F :=
        mul_le_mul_of_nonneg_left hKF (by have := canonicalTerminalConstant_nonneg A M; positivity)
      _ = _ := by ring
  · rw [canonicalLogEnergy_subunit p hp hcop hg pool Ψ m labels V X K A hX hVs (lt_of_not_ge hscale)]
    exact mul_nonneg (canonicalTerminalConstant_nonneg A M) (sq_nonneg _)

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0232

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.CoordinateLaplacian
Source SHA256: c2890bdef185a468f506b85e2c8abb4e0c276af30e01e66d49387e3c876c7787
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0233



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
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv

def kernelCoordinateLaplacian (f : kernelSmoothTests) (p : EuclideanSpatial) : ℂ :=
  -(p 2:ℂ)^2*(∑j : Fin 3,
    fderiv ℝ (fun q => fderiv ℝ (kernelTestField f) q (euclideanCoordinateVector j)) p
      (euclideanCoordinateVector j))+
    (p 2:ℂ)*fderiv ℝ (kernelTestField f) p (euclideanCoordinateVector 2)

lemma kernelCoreLift_laplacian (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : p∈kernelChartCore χ) :
    upperPositiveLaplacian (kernelCoreLift χ f) p=kernelCoordinateLaplacian f p := by
  have he := kernelCoreLift_eventually_eq χ f p hp
  have hd (j : Fin 3) : (fun q => fderiv ℝ (kernelCoreLift χ f) q (euclideanCoordinateVector j))=ᶠ[𝓝 p]
      (fun q => fderiv ℝ (kernelTestField f) q (euclideanCoordinateVector j)) :=
    (he.fderiv (𝕜 := ℝ)).mono (fun q hq => congrArg (fun d => d (euclideanCoordinateVector j)) hq)
  have hdd (j : Fin 3) :
      (∂_{euclideanCoordinateVector j} (∂_{euclideanCoordinateVector j} (kernelCoreLift χ f))) p=
        fderiv ℝ (fun q => fderiv ℝ (kernelTestField f) q (euclideanCoordinateVector j)) p
          (euclideanCoordinateVector j) := by
    change fderiv ℝ (fun q => fderiv ℝ (kernelCoreLift χ f) q (euclideanCoordinateVector j)) p
      (euclideanCoordinateVector j)=_
    rw [(hd j).fderiv_eq]
  simp only [upperPositiveLaplacian,kernelCoordinateLaplacian,hdd,
    SchwartzMap.lineDerivOp_apply_eq_fderiv,he.fderiv_eq]

lemma kernelDirichletForm_coordinate_equation_chart (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f g : kernelSmoothTests) (hg : tsupport g.1⊆kernelChartCoreImage χ)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p)) :
    kernelDirichletForm f g=∫q,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel := by
  let S := tsupport χ.func
  have hS : MeasurableSet S := χ.compact.measurableSet
  have hi : Integrable (fun q => star (A q)*g.1 q) (integralQuotientVolume globalKubotaKernel) :=
    hA.star.integrable_mul (kernelSmoothTests_memLp g)
  have himg : kernelChartCoreImage χ⊆kernelEuclideanProjection '' S :=
    Set.image_mono (kernelChartCore_subset χ)
  rw [kernelDirichletForm_eq_chart_laplacian χ hinj f g hg]
  calc
    _ = ∫p in S,star (upperPositiveLaplacian (kernelCoreLift χ f) p)*kernelCoreLift χ g p/(p 2:ℂ)^3 := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      have hz : kernelCoreLift χ g p=0 := image_eq_zero_of_notMem_tsupport
        (fun h => hp (kernelCoreLift_tsupport_outer χ g h))
      rw [hz,mul_zero,zero_div]
    _ = ∫p in S,star (A (kernelEuclideanProjection p))*g.1 (kernelEuclideanProjection p)/(p 2:ℂ)^3 := by
      apply setIntegral_congr_fun hS
      intro p hp
      dsimp only
      rw [kernelCoreLift_eq_on_outer χ hinj g hg hp]
      by_cases hc : p∈kernelChartCore χ
      · rw [kernelCoreLift_laplacian χ f p hc,heq p (χ.positive hp)]
        rfl
      · have hz : kernelCoreLift χ g p=0 := image_eq_zero_of_notMem_tsupport
          (fun h => hc (kernelCoreLift_tsupport χ hinj g hg h))
        rw [kernelCoreLift_eq_on_outer χ hinj g hg hp] at hz
        change g.1 (kernelEuclideanProjection p)=0 at hz
        change star _*g.1 (kernelEuclideanProjection p)/_=star _*g.1 (kernelEuclideanProjection p)/_
        rw [hz,mul_zero,zero_div,mul_zero,zero_div]
    _ = ∫p in S,star (A (kernelEuclideanProjection p))*g.1 (kernelEuclideanProjection p)
        ∂hyperbolicEuclideanVolume :=
      (hyperbolicEuclidean_setIntegral_complex S hS χ.positive _).symm
    _ = ∫q in kernelEuclideanProjection '' S,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel :=
      kernelEuclideanProjection_integral_complex S hS χ.positive hinj _ hi.aestronglyMeasurable
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro q hq
      have hz : g.1 q=0 := image_eq_zero_of_notMem_tsupport (fun h => hq (himg (hg h)))
      rw [hz,mul_zero]

lemma kernelDirichletForm_sum_right {ι : Type*} (f : kernelSmoothTests)
    (t : Finset ι) (g : ι→kernelSmoothTests) :
    kernelDirichletForm f (∑i∈t,g i)=∑i∈t,kernelDirichletForm f (g i) := by
  induction t using Finset.induction_on with
  | empty =>
    have hz := kernelDirichletForm_smul_right 0 f (0 : kernelSmoothTests)
    simpa only [Finset.sum_empty,zero_smul,zero_mul] using hz
  | @insert i t hi ih =>
    simp only [Finset.sum_insert hi,kernelDirichletForm_add_right,ih]

theorem kernelDirichletForm_coordinate_equation (f : kernelSmoothTests)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p))
    (g : kernelSmoothTests) :
    kernelDirichletForm f g=∫q,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel := by
  obtain ⟨t,G,hG,hGsupp⟩ := kernelSmoothTest_finite_chart_partition g
  calc
    _ = ∑i : t,kernelDirichletForm f (G i) := by
      rw [←hG,kernelDirichletForm_sum_right]
    _ = ∑i : t,∫q,star (A q)*(G i).1 q∂integralQuotientVolume globalKubotaKernel := by
      apply Finset.sum_congr rfl
      intro i hi
      exact kernelDirichletForm_coordinate_equation_chart i.1.1 i.1.2 f (G i) (hGsupp i) A hA heq
    _ = ∫q,∑i : t,star (A q)*(G i).1 q∂integralQuotientVolume globalKubotaKernel := by
      symm
      exact integral_finsetSum _ (fun i hi => hA.star.integrable_mul (kernelSmoothTests_memLp (G i)))
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun q => by
        have hq := congrArg (fun k : kernelSmoothTests => k.1 q) hG
        simp only [Submodule.coe_sum,Finset.sum_apply] at hq
        dsimp only
        rw [←Finset.mul_sum,hq])

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff

lemma kernelL2_inner_toLp_smooth (A : KernelQuotient→ℂ)
    (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel)) (g : kernelSmoothTests) :
    inner ℂ (hA.toLp A) (kernelSmoothTestsToL2 g)=
      ∫q,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel := by
  calc
    _ = ∫q,inner ℂ ((hA.toLp A) q) (kernelSmoothTestsToL2 g q)
        ∂integralQuotientVolume globalKubotaKernel := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hA.coeFn_toLp,(kernelSmoothTests_memLp g).coeFn_toLp] with q hq hg
      change inner ℂ ((hA.toLp A) q) (((kernelSmoothTests_memLp g).toLp g.1) q)=_
      rw [hq,hg,RCLike.inner_apply]
      simp only [RCLike.star_def,mul_comm]

lemma kernelCoordinateLaplacian_form (f : kernelSmoothTests)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p))
    (v : KernelEnergyGraph) :
    inner ℂ (kernelEnergyGradient (kernelEnergyGraphCore f)) (kernelEnergyGradient v)=
      inner ℂ (hA.toLp A) (kernelEnergyMass v) := by
  exact kernelEnergyGraphCore_dense.induction_on v
    (isClosed_eq (by fun_prop : Continuous (fun u : KernelEnergyGraph =>
      inner ℂ (kernelEnergyGradient (kernelEnergyGraphCore f)) (kernelEnergyGradient u)))
      (by fun_prop : Continuous (fun u : KernelEnergyGraph => inner ℂ (hA.toLp A) (kernelEnergyMass u))))
    (fun g => by
      rw [kernelEnergyGradient_core,kernelEnergyGradient_core,kernelEnergyMass_core,
        kernelGradientToL2_inner,kernelL2_inner_toLp_smooth]
      exact kernelDirichletForm_coordinate_equation f A hA heq g)

theorem kernelEnergyLaplacian_graph_of_coordinate (f : kernelSmoothTests)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p)) :
    (kernelSmoothTestsToL2 f,hA.toLp A)∈kernelEnergyLaplacian.graph := by
  have hu : kernelEnergyGraphCore f=
      kernelVariationalSolution (kernelSmoothTestsToL2 f+hA.toLp A) := by
    apply kernelVariationalSolution_unique
    intro v
    rw [kernelEnergyMass_core,kernelCoordinateLaplacian_form f A hA heq,inner_add_left]
  have hm := congrArg kernelEnergyMass hu
  rw [kernelEnergyMass_core] at hm
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph]
  exact hm.symm

lemma kernelEnergyLaplacian_domain_of_coordinate (f : kernelSmoothTests)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p)) :
    kernelSmoothTestsToL2 f∈kernelEnergyLaplacian.domain :=
  LinearPMap.mem_domain_of_mem_graph (kernelEnergyLaplacian_graph_of_coordinate f A hA heq)

lemma kernelEnergyLaplacian_apply_of_coordinate (f : kernelSmoothTests)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p)) :
    kernelEnergyLaplacian ⟨kernelSmoothTestsToL2 f,kernelEnergyLaplacian_domain_of_coordinate f A hA heq⟩=
      hA.toLp A :=
  kernelEnergyLaplacian.mem_graph_snd_inj
    (kernelEnergyLaplacian.mem_graph ⟨kernelSmoothTestsToL2 f,kernelEnergyLaplacian_domain_of_coordinate f A hA heq⟩)
    (kernelEnergyLaplacian_graph_of_coordinate f A hA heq) rfl

end CubicEisenstein

section

open scoped BigOperators Classical
open MeasureTheory
namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic ConcreteTraceCRT

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem densityChildEnergy_from_canonical_state
    (pool : Finset ι) (Ψ₁ Ψ₂ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (labels : Finset (Ideal ActualEisensteinCubic.O)) (V₁ V₂ : ℝ → ℂ)
    (X F K E t₁ t₂ : ℝ) (J : ℕ) (hX : 0<X) (hK : 0<K) (hE : 0≤E)
    (hlabels : ∀z∈T,z.1∈labels)
    (hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K) (hzero : ∀z∈T,z.2≠0)
    (h₁ : ∀t,canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ₁ t) m labels
      (orientedLogProfile true V₁) X K≤E*(X*F)^2*(1+‖t‖)^(2*J))
    (h₂ : ∀t,canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ₂ t) m labels
      (orientedLogProfile false V₂) X K≤E*(X*F)^2*(1+‖t‖)^(2*J)) :
    densityChildEnergy p hp hcop hg pool (normHeightTwist Ψ₁ t₁) (normHeightTwist Ψ₂ t₂)
      m T V₁ V₂ X X (2*J)≤
      6*E*(X*F)^2*(1+‖t₁‖)^J*(1+‖t₂‖)^J*
        (∫t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t)^3 := by
  have hleft (t : ℝ) : childEnergy p hp hcop hg pool (normHeightTwist Ψ₁ t) m T V₁ X true false 0 0≤
      (6*E*(X*F)^2)*(1+‖t‖)^(2*J) := by
    have hh := childEnergy_le_canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ₁ t) m
      T labels V₁ X K 0 0 hX hK true false hlabels hrows hzero
    simp only [normHeightTwist_twice,secondSignedHeight,ite_true,sub_self,add_zero] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (h₁ t) (by norm_num : (0:ℝ)≤6)).trans_eq (by ring))
  have hright (t : ℝ) : childEnergy p hp hcop hg pool (normHeightTwist Ψ₂ t) m T V₂ X false true 0 0≤
      (6*E*(X*F)^2)*(1+‖t‖)^(2*J) := by
    have hh := childEnergy_le_canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ₂ t) m
      T labels V₂ X K 0 0 hX hK false true hlabels hrows hzero
    simp only [normHeightTwist_twice,secondSignedHeight,Bool.false_eq_true,ite_false,sub_self,add_zero] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (h₂ t) (by norm_num : (0:ℝ)≤6)).trans_eq (by ring))
  have hb : 0≤6*E*(X*F)^2 := by positivity
  have hd := densityChildEnergy_normHeight_polynomial p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂
    X X t₁ t₂ (6*E*(X*F)^2) (6*E*(X*F)^2) J hX hX hb hb hleft hright
  rw [Real.mul_self_sqrt hb] at hd
  exact hd

end SecondPassIntegration

namespace SecondPassArithmetic
open ActualEisensteinCubic FirstPassCubeLabels ConcreteTraceCRT

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

def globalCanonicalLabels (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex) : Finset (Ideal ActualEisensteinCubic.O) :=
  (globalArithmeticTargets p source side q j).image Prod.fst

include hp in
theorem globalCanonicalLabels_bounds (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex)
    (hk : ∀x∈source,x.source.frequency≠0) :
    ∀I∈globalCanonicalLabels p source side q j,
      I≠⊥ ∧ Squarefree I ∧ (Ideal.absNorm I:ℝ)≤globalPooledLabelScale j := by
  intro I hI
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hI
  have hb := globalArithmeticTargets_bounds p hp source side q j hk z hz
  exact ⟨hb.1,globalArithmeticTargets_squarefree p source side q j z hz,hb.2.1⟩

end SecondPassArithmetic
end

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct jLabel)

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O)

omit [DecidableEq ι] in
theorem actualSecondLabel_coprime (bad : Ideal ActualEisensteinCubic.O)
    (hbad : ∀i,IsCoprime (Ideal.span {p i}) bad)
    (B C E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    IsCoprime (actualSecondLabel p B C E V v₁ v₂ ε₁ ε₂) bad := by
  have hprod (S : Finset ι) : IsCoprime (∏i∈S,Ideal.span {p i}) bad :=
    IsCoprime.prod_left (fun i _=>hbad i)
  have hJ : IsCoprime (Ideal.span {jLabel p B (fun i=>v₁ i+v₂ i) ε₁ ε₂}) bad := by
    simp only [jLabel,primeProduct,FiniteGaussPhase.span_finset_prod,←Ideal.span_singleton_pow]
    exact IsCoprime.prod_left (fun i _=>(hbad i).pow_left)
  exact ((hJ.mul_left (hprod C)).mul_left (hprod E)).mul_left (hprod V)

theorem globalNewLabel_coprime (bad : Ideal ActualEisensteinCubic.O)
    (hbad : ∀i,IsCoprime (Ideal.span {p i}) bad) (x : GlobalSecondData ι) :
    IsCoprime (SecondPassFiber.newLabel (globalSecondTuple p x)) bad := by
  exact actualSecondLabel_coprime p bad hbad x.cube.support x.common x.source.divisor x.source.overlap
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit

theorem globalCanonicalLabels_coprime (bad : Ideal ActualEisensteinCubic.O)
    (hbad : ∀i,IsCoprime (Ideal.span {p i}) bad)
    (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex) :
    ∀I∈globalCanonicalLabels p source side q j,IsCoprime I bad := by
  intro I hI
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  exact globalNewLabel_coprime p bad hbad x

end SecondPassArithmetic

namespace CanonicalRowCompletion

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O

theorem finite_integral_energy_polynomial {κ : Type*} [Fintype κ]
    (b : ℝ → ℂ) (φ : κ → ℝ → ℂ) (d : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hb : Integrable (fun t => ‖b t‖*(1+|t|)^d))
    (hφ : ∀ k, Integrable (fun t => b t*φ k t))
    (hbound : ∀ t, (∑ k, ‖φ k t‖^2) ≤ E*(1+|t|)^(2*d)) :
    (∑ k, ‖∫ t : ℝ, b t*φ k t‖^2) ≤
      E*(∫ t : ℝ, ‖b t‖*(1+|t|)^d)^2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : ℝ → EuclideanSpace ℂ κ := fun t => e.symm (fun k => b t*φ k t)
  have hF (t : ℝ) : ‖F t‖ ≤ (‖b t‖*(1+|t|)^d)*Real.sqrt E := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ k, ‖b t*φ k t‖^2) ≤ _
    simp only [norm_mul,mul_pow,← Finset.mul_sum,Real.sq_sqrt hE]
    have hp : (1+|t|)^(2*d) = ((1+|t|)^d)^2 := by
      rw [← pow_mul,Nat.mul_comm d 2]
    calc
      _ ≤ ‖b t‖^2 * (E*(1+|t|)^(2*d)) :=
        mul_le_mul_of_nonneg_left (hbound t) (sq_nonneg _)
      _ = _ := by rw [hp]; ring
  have he : (∫ t : ℝ, F t) = e.symm (fun k => ∫ t : ℝ, b t*φ k t) := by
    rw [show F = (fun t => e.symm (fun k => b t*φ k t)) from rfl,
      e.symm.integral_comp_comm]
    congr 1
    funext k
    exact eval_integral hφ k
  have hn : ‖e.symm (fun k => ∫ t : ℝ, b t*φ k t)‖ ≤
      (∫ t : ℝ, ‖b t‖*(1+|t|)^d)*Real.sqrt E := by
    rw [← he,← integral_mul_const]
    exact norm_integral_le_of_norm_le (hb.mul_const _)
      (Filter.Eventually.of_forall hF)
  have hh := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt hE] at hh
  change (∑ k, ‖∫ t : ℝ, b t*φ k t‖^2) ≤
    (∫ t : ℝ, ‖b t‖*(1+|t|)^d)^2 * E at hh
  simpa only [mul_comm] using hh

theorem norm_add_sum_sq_le {κ : Type*} (s : Finset κ) (a : ℂ) (b : κ → ℂ) :
    ‖a + ∑ k ∈ s, b k‖^2 ≤ 2*(‖a‖^2 + s.card*∑ k ∈ s, ‖b k‖^2) := by
  have hs : ‖∑ k ∈ s, b k‖^2 ≤ (s.card : ℝ)*∑ k ∈ s, ‖b k‖^2 := by
    calc
      _ ≤ (∑ k ∈ s, ‖b k‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by
        simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one]
          using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1:ℝ)) (fun k => ‖b k‖)
  have ha := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a (∑ k ∈ s, b k)) 2
  nlinarith [sq_nonneg (‖a‖ - ‖∑ k ∈ s, b k‖)]

theorem outsideCanonicalRow_binned_energy
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ : ℝ)
    (hb : 0 ≤ b) (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t ≤ b) (hD : b*X ≤ D) :
    ‖outsideCanonicalRow S D hbad Ψ m f z W X‖^2 ≤
      2*X*(‖shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀‖^2 +
        (cubeLogRange b X).card * ∑ j ∈ cubeLogRange b X,
          ‖outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) Ψ m f z W X H₀‖^2) := by
  have hs := norm_add_sum_sq_le (cubeLogRange b X)
    (shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀)
    (fun j => outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) Ψ m f z W X H₀)
  rw [← outsideCanonicalRow_reopened_binned S D hbad hSp Ψ m f z W hWc b X H₀ hb hX hW hD] at hs
  have hn : ‖outsideCanonicalRow S D hbad Ψ m f z W X‖^2 =
      X*‖(Real.sqrt X : ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X‖^2 := by
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg X),
      mul_pow,inv_pow,Real.sq_sqrt hX.le]
    field_simp
  rw [hn]
  convert mul_le_mul_of_nonneg_left hs hX.le using 1 ; ring

end CanonicalRowCompletion

open scoped BigOperators Classical
namespace CanonicalCoefficientClass

section
open ActualEisensteinCubic
open SecondPassArithmetic (rayMonoid conjugateRayMonoid rayMonoid_apply conjugateRayMonoid_apply
  FirstCoreIndex firstCoreTwist sideRayMonoid SecondRayIndex secondRayMinus secondRayPlus)
open RayFourExpansion (RayCharacter)

def IsBaseRayTwist (base Ψ : ActualEisensteinCubic.O→*ℂ) : Prop :=
  Ψ=base ∨ ∃χ : RayCharacter, Ψ=rayMonoid χ*base

def baseRayOrbit (base : ActualEisensteinCubic.O→*ℂ) : Finset (ActualEisensteinCubic.O→*ℂ) :=
  insert base (Finset.univ.image (fun χ : RayCharacter => rayMonoid χ*base))

lemma mem_baseRayOrbit (base Ψ : ActualEisensteinCubic.O→*ℂ) : Ψ∈baseRayOrbit base ↔ IsBaseRayTwist base Ψ := by
  simp only [baseRayOrbit,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and,IsBaseRayTwist]
  constructor
  · rintro (h|⟨χ,h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨χ,h.symm⟩
  · rintro (h|⟨χ,h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨χ,h.symm⟩

lemma baseRayOrbit_card (base : ActualEisensteinCubic.O→*ℂ) : (baseRayOrbit base).card≤17 := by
  have h1 := Finset.card_insert_le base (Finset.univ.image (fun χ : RayCharacter => rayMonoid χ*base))
  have h2 := Finset.card_image_le (s := (Finset.univ : Finset RayCharacter))
    (f := fun χ : RayCharacter => rayMonoid χ*base)
  have h3 := RayFourExpansion.rayCharacter_card_le
  simp only [Finset.card_univ] at h2
  unfold baseRayOrbit
  omega

lemma rayMonoid_mul (χ η : RayCharacter) : rayMonoid (χ*η)=rayMonoid χ*rayMonoid η := by
  ext x
  simp only [rayMonoid_apply,RayFourExpansion.rayCharacter,MulChar.mul_apply,MonoidHom.mul_apply]

lemma conjugateRayMonoid_eq (χ : RayCharacter) : conjugateRayMonoid χ=rayMonoid (star χ) := by
  ext x
  simp only [conjugateRayMonoid_apply,rayMonoid_apply,RayFourExpansion.rayCharacter,MulChar.star_apply]

lemma IsBaseRayTwist.mul_ray {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ) (χ : RayCharacter) :
    IsBaseRayTwist base (rayMonoid χ*Ψ) := by
  rcases hΨ with h|⟨η,h⟩
  · exact Or.inr ⟨χ,by rw [h]⟩
  · exact Or.inr ⟨χ*η,by rw [h,rayMonoid_mul,mul_assoc]⟩

lemma firstCoreTwist_single_ray (side : Bool) (χ : RayCharacter) (Ψ : ActualEisensteinCubic.O→*ℂ)
    (r : FirstCoreIndex) :
    firstCoreTwist side χ Ψ r =
      rayMonoid ((if side then star χ else χ)*FirstPassCubeLabels.coreRayCharacter side r.1 r.2.2)*Ψ := by
  rw [rayMonoid_mul]
  have hcore : FirstPassCubeLabels.coreRayTwist side r.1 r.2.2 =
      rayMonoid (FirstPassCubeLabels.coreRayCharacter side r.1 r.2.2) := rfl
  unfold firstCoreTwist sideRayMonoid
  rw [hcore]
  cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true,conjugateRayMonoid_eq] <;> ac_rfl

lemma IsBaseRayTwist.firstCore {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ)
    (side : Bool) (χ : RayCharacter) (r : FirstCoreIndex) :
    IsBaseRayTwist base (firstCoreTwist side χ Ψ r) := by
  rw [firstCoreTwist_single_ray]
  exact hΨ.mul_ray _

lemma secondRayMinus_single_ray (Ψ : ActualEisensteinCubic.O→*ℂ) (r : SecondRayIndex) :
    secondRayMinus Ψ r=rayMonoid (star r.2.2*star r.1.2)*Ψ := by
  rw [rayMonoid_mul]
  simp only [secondRayMinus,conjugateRayMonoid_eq,mul_assoc]

lemma secondRayPlus_single_ray (Ψ : ActualEisensteinCubic.O→*ℂ) (r : SecondRayIndex) :
    secondRayPlus Ψ r=rayMonoid (r.2.1*star r.1.1)*Ψ := by
  rw [rayMonoid_mul]
  simp only [secondRayPlus,conjugateRayMonoid_eq,mul_assoc]

lemma IsBaseRayTwist.secondMinus {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ)
    (r : SecondRayIndex) : IsBaseRayTwist base (secondRayMinus Ψ r) := by
  rw [secondRayMinus_single_ray]
  exact hΨ.mul_ray _

lemma IsBaseRayTwist.secondPlus {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ)
    (r : SecondRayIndex) : IsBaseRayTwist base (secondRayPlus Ψ r) := by
  rw [secondRayPlus_single_ray]
  exact hΨ.mul_ray _

lemma IsBaseRayTwist.norm_le {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ)
    (hbase : ∀x,‖base x‖≤1) (x : ActualEisensteinCubic.O) : ‖Ψ x‖≤1 := by
  rcases hΨ with rfl|⟨χ,rfl⟩
  · exact hbase x
  · rw [MonoidHom.mul_apply,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (FiniteRayExpansion.norm_char_le_one χ _)).trans (hbase x)

def FactorsModulo (Q : Ideal ActualEisensteinCubic.O) (Ψ : ActualEisensteinCubic.O→*ℂ) : Prop :=
  ∀x y : ActualEisensteinCubic.O,x-y∈Q → Ψ x=Ψ y

lemma IsBaseRayTwist.factorsModulo {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ)
    (Q : Ideal ActualEisensteinCubic.O) (hbase : FactorsModulo Q base) :
    FactorsModulo (Q*Ideal.span {(4:ActualEisensteinCubic.O)}) Ψ := by
  intro x y hxy
  have hb := hbase x y (Ideal.mul_le_left hxy)
  rcases hΨ with rfl|⟨χ,rfl⟩
  · exact hb
  · simp only [MonoidHom.mul_apply]
    rw [hb]
    congr 1
    exact RayFourExpansion.rayCharacter_eq_of_mod_four χ x y
      (Ideal.mem_span_singleton.mp (Ideal.mul_le_right hxy))

def initialBase {q : ℕ} (χ : DirichletCharacter ℂ q) : ActualEisensteinCubic.O→*ℂ :=
  InitialMeanSquare.conjugateMonoid (InitialMeanSquare.normCharacter χ)

lemma initialBase_norm {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ActualEisensteinCubic.O) :
    ‖initialBase χ x‖≤1 := by
  change ‖star (InitialMeanSquare.normCharacter χ x)‖≤1
  rw [norm_star]
  exact InitialMeanSquare.normCharacter_norm_le_one χ x

lemma initial_minus_member {q : ℕ} (χ : DirichletCharacter ℂ q) (r : SecondRayIndex) :
    IsBaseRayTwist (initialBase χ) (secondRayMinus (initialBase χ) r) :=
  IsBaseRayTwist.secondMinus (Or.inl rfl : IsBaseRayTwist (initialBase χ) (initialBase χ)) r

lemma initial_plus_member {q : ℕ} (χ : DirichletCharacter ℂ q) (r : SecondRayIndex) :
    IsBaseRayTwist (initialBase χ) (secondRayPlus (initialBase χ) r) :=
  IsBaseRayTwist.secondPlus (Or.inl rfl : IsBaseRayTwist (initialBase χ) (initialBase χ)) r

end

open ActualEisensteinCubic
open ActualEisensteinCoordinates (eval coords eval_coords)
open ShortDraftLatticeCount (qNat qO_nonneg coords_eval)

lemma norm_eval_mod (m : ℕ) (a b : ℤ) :
    (Ideal.absNorm (Ideal.span {eval a b}) : ZMod m)=
      (a : ZMod m)^2-(a : ZMod m)*(b : ZMod m)+(b : ZMod m)^2 := by
  have hi : (Ideal.absNorm (Ideal.span {eval a b}) : ℤ)=a^2-a*b+b^2 := by
    rw [←qNat_eq_absNorm_span]
    change ((ShortDraftLatticeCount.q (coords (eval a b))).toNat : ℤ)=_
    rw [Int.toNat_of_nonneg (qO_nonneg _),coords_eval]
    rfl
  have hz := congrArg (fun k : ℤ => (k : ZMod m)) hi
  push_cast at hz
  exact hz

theorem normCharacter_factorsModulo {m : ℕ} (χ : DirichletCharacter ℂ m) :
    FactorsModulo (Ideal.span {(m : ActualEisensteinCubic.O)}) (InitialMeanSquare.normCharacter χ) := by
  intro x y hxy
  obtain ⟨z,hz⟩ := Ideal.mem_span_singleton.mp hxy
  let c := (coords y).1
  let d := (coords y).2
  let e := (coords z).1
  let f := (coords z).2
  have hy : y=eval c d := (eval_coords y).symm
  have hx : x=eval (c+(m : ℤ)*e) (d+(m : ℤ)*f) := by
    calc
      x=y+(m : ActualEisensteinCubic.O)*z := by linear_combination hz
      _=eval (c+(m : ℤ)*e) (d+(m : ℤ)*f) := by
        rw [hy,←eval_coords z]
        dsimp [eval,c,d,e,f]
        push_cast
        ring
  change χ (Ideal.absNorm (Ideal.span {x}))=χ (Ideal.absNorm (Ideal.span {y}))
  congr 1
  rw [hx,hy,norm_eval_mod,norm_eval_mod]
  simp

theorem initialBase_factorsModulo {m : ℕ} (χ : DirichletCharacter ℂ m) :
    FactorsModulo (Ideal.span {(m : ActualEisensteinCubic.O)}) (initialBase χ) := by
  intro x y hxy
  change star (InitialMeanSquare.normCharacter χ x)=star (InitialMeanSquare.normCharacter χ y)
  rw [normCharacter_factorsModulo χ x y hxy]

def fixedBaseConductor (m : ℕ) : Ideal ActualEisensteinCubic.O := Ideal.span {(m : ActualEisensteinCubic.O)}*Ideal.span {(4 : ActualEisensteinCubic.O)}

theorem initialOrbit_factorsModulo {m : ℕ} (χ : DirichletCharacter ℂ m) (Ψ : ActualEisensteinCubic.O→*ℂ)
    (hΨ : IsBaseRayTwist (initialBase χ) Ψ) : FactorsModulo (fixedBaseConductor m) Ψ :=
  hΨ.factorsModulo _ (initialBase_factorsModulo χ)

lemma fixedBaseConductor_principal (m : ℕ) :
    fixedBaseConductor m=Ideal.span {((4*m : ℕ) : ActualEisensteinCubic.O)} := by
  rw [fixedBaseConductor,Ideal.span_singleton_mul_span_singleton]
  congr 1
  push_cast
  ring_nf

lemma fixedBaseConductor_ne_zero (m : ℕ) (hm : m≠0) : fixedBaseConductor m≠0 := by
  rw [fixedBaseConductor_principal]
  change Ideal.span {((4*m : ℕ) : ActualEisensteinCubic.O)}≠⊥
  rw [ne_eq,Ideal.span_singleton_eq_bot]
  exact_mod_cast Nat.mul_ne_zero (by decide : (4:ℕ)≠0) hm

lemma fixedBaseConductor_norm (m : ℕ) (hm : m≠0) :
    Ideal.absNorm (fixedBaseConductor m)=16*m^2 := by
  rw [fixedBaseConductor_principal]
  have h := rational_modulus_card (4*m) (Nat.mul_ne_zero (by decide) hm)
  rw [Ideal.absNorm_apply,Submodule.cardQuot_apply]
  rw [h]
  ring

end CanonicalCoefficientClass

end

end OAI
end OAIOriginalModule0233

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.DensityBudgets
Source SHA256: 48a755cd21192079251f34a3c0680c14562e982da53d0bd4cddc6262c592c765
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0234


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

namespace SecondPassArithmetic

section

open scoped BigOperators Classical
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)
open SecondPassIntegration (densityChildEnergy_from_canonical_state)

def canonicalDensityConstant (E : ℝ) (J : ℕ) (t : ℝ) : ℝ :=
  6*E*(1+‖t‖)^(2*J)*(∫s : ℝ,firstLogDensity 0 s)^3

theorem canonicalDensityConstant_nonneg (E : ℝ) (hE : 0≤E) (J : ℕ) (t : ℝ) :
    0≤canonicalDensityConstant E J t := by
  have hi : 0≤∫s : ℝ,firstLogDensity 0 s :=
    integral_nonneg (fun s=>FirstPassCubeLabels.firstLogDensity_nonneg 0 s)
  unfold canonicalDensityConstant
  positivity

theorem globalFirstQuantitativeBudget_state_bound (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) :
    ∃ Clo Chi : ℝ,0<Clo ∧ 0<Chi ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (side : Bool)
      (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (windows : Fin 7 → ℝ → ℂ)
      (C Cd Ct Γ E oldHeight K ell B F M H U Z θ A₀ Vmax : ℝ) (N J Ntail : ℕ),
      0≤C → 0≤Γ → 0≤E → 1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U → 0<Z → 0≤A₀ → 0≤Vmax →
      (∀t,‖windows 5 t‖≤Vmax) → (∀t,‖windows 6 t‖≤Vmax) →
      (∀t,windows 5 t≠0 → |t|≤A₀) → (∀t,windows 6 t≠0 → |t|≤A₀) →
      (∀u,‖Ψ u‖≤1) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (let source := globalQuantitativeSource p pool blocks K ell B F M H U side
       ∀a : RayCharacter×RayCharacter,∀r : FirstCoreIndex,
       ∀j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter
          (fun j => globalBinRadial ell (globalPooledRowScale K ell B F j) j<Z^θ),
       ∀ray : SecondRayIndex,∀q∈globalBinTriples p source side j,
       let Ψmode := firstCoreTwist side (if side then a.1 else a.2) Ψ r
       ∀s : ℝ,
       (canonicalLogEnergy p hp hcop hg pool (normHeightTwist (secondRayMinus Ψmode ray) s)
         (fixedTripleMask m q) (globalCanonicalLabels p source side q j)
         (orientedLogProfile true (windows 5)) (globalPooledColumnScale ell j)
         (globalLogRep j 8*Real.exp 1)≤
         E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2*(1+‖s‖)^(2*J)) ∧
       (canonicalLogEnergy p hp hcop hg pool (normHeightTwist (secondRayPlus Ψmode ray) s)
         (fixedTripleMask m q) (globalCanonicalLabels p source side q j)
         (orientedLogProfile false (windows 6)) (globalPooledColumnScale ell j)
         (globalLogRep j 8*Real.exp 1)≤
         E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2*(1+‖s‖)^(2*J))) →
      globalFirstQuantitativeBudget p hp hcop hg pool blocks (normHeightTwist Ψ oldHeight) m windows
        C Cd Ct Γ ε K ell B F M H U (N+1) (2*J) Ntail side ≤
        (∫t : ℝ,firstLogDensity 0 t)*(512*(512*32))*Γ*((ell*B^3)*F)*
          ((B*U)^ε*(Cd+Ct*globalFirstTailFactor K ell B F U H Ntail)+
           C*globalRayTripleConstant*U^(deltaLoss+8*ε)*
             (canonicalDensityConstant E J oldHeight*Clo+globalTerminalConstant A₀ Vmax*K*Chi/Z^(θ*N))) := by
  obtain ⟨Clo,Chi,hClo,hChi,hbound⟩ := globalFirstQuantitativeBudget_canonical_bound deltaLoss hδ ε hε
  refine ⟨Clo,Chi,hClo,hChi,?_⟩
  intro ι _ p hp _ hcop hg hc hinj pool blocks side Ψ m windows C Cd Ct Γ E oldHeight K ell B F M H U Z θ A₀ Vmax N J Ntail
    hC hΓ hE hU hK hell hB hF hH hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂ hΨ hb₁ hb₂ he
  apply hbound p hp hcop hg hc hinj pool blocks side (normHeightTwist Ψ oldHeight) m windows
    C Cd Ct Γ (canonicalDensityConstant E J oldHeight) K ell B F M H U Z θ A₀ Vmax N J Ntail
    hC hΓ (canonicalDensityConstant_nonneg E hE J oldHeight) hU hK hell hB hF hH
    hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂
    (fun u=>(normHeightTwist_norm_le Ψ oldHeight u).trans (hΨ u)) hb₁ hb₂
  dsimp only
  intro a r j hj ray q hq
  rw [firstCoreTwist_normHeight,secondRayMinus_normHeight,secondRayPlus_normHeight]
  let source := globalQuantitativeSource p pool blocks K ell B F M H U side
  have hk : ∀x∈source,x.source.frequency≠0 :=
    fun x hx=>globalQuantitativeSource_frequency_ne_zero p pool blocks K ell B F M H U side x hx
  have hkc : 0<globalLogRep j 8*Real.exp 1 := mul_pos (globalLogRep_pos j 8) (Real.exp_pos 1)
  have hs := he a r j hj ray q hq
  have hd := densityChildEnergy_from_canonical_state p hp hcop hg pool
    (secondRayMinus (firstCoreTwist side (if side then a.1 else a.2) Ψ r) ray)
    (secondRayPlus (firstCoreTwist side (if side then a.1 else a.2) Ψ r) ray)
    (fixedTripleMask m q) (globalArithmeticTargets p source side q j)
    (globalCanonicalLabels p source side q j) (windows 5) (windows 6)
    (globalPooledColumnScale ell j) (globalPooledLabelScale j) (globalLogRep j 8*Real.exp 1)
    E oldHeight oldHeight J (globalPooledColumnScale_pos ell hell j) hkc hE
    (fun z hz=>Finset.mem_image.mpr ⟨z,hz,rfl⟩)
    (fun z hz=>(globalArithmeticTargets_bounds p hp source side q j hk z hz).2.2)
    (globalArithmeticTargets_nonzero p source side q j hk)
    (fun t=>(hs t).1) (fun t=>(hs t).2)
  exact hd.trans_eq (by unfold canonicalDensityConstant; rw [two_mul,pow_add]; ring)

end

open ActualEisensteinCubic ConcreteTraceCRT

def canonicalRankMass (Z : ℝ) (r : ℕ) : ℝ :=
  Real.exp (3*((3000-r:ℕ):ℝ))*Z^2

theorem canonicalRankMass_initial (Z : ℝ) (r : ℕ) : Z^2≤canonicalRankMass Z r := by
  have he : 1≤Real.exp (3*((3000-r:ℕ):ℝ)) := Real.one_le_exp (by positivity)
  simpa only [one_mul,canonicalRankMass] using mul_le_mul_of_nonneg_right he (sq_nonneg Z)

theorem canonicalRankMass_step (Z : ℝ) (r s : ℕ) (hr : r≤3000) (hs : s+1≤r) :
    Real.exp 3*canonicalRankMass Z r≤canonicalRankMass Z s := by
  have hn : 3000-r+1≤3000-s := by omega
  have hn' : ((3000-r:ℕ):ℝ)+1≤((3000-s:ℕ):ℝ) := by exact_mod_cast hn
  unfold canonicalRankMass
  rw [←mul_assoc,←Real.exp_add]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (sq_nonneg Z)

theorem canonicalRankMass_child (Z X F X' F' : ℝ) (r s : ℕ)
    (hr : r≤3000) (hs : s+1≤r) (hparent : X*F≤canonicalRankMass Z r)
    (hchild : X'*F'≤Real.exp 3*(X*F)) : X'*F'≤canonicalRankMass Z s :=
  hchild.trans ((mul_le_mul_of_nonneg_left hparent (Real.exp_pos _).le).trans
    (canonicalRankMass_step Z r s hr hs))

theorem canonicalRankMass_global (Z : ℝ) (hZ : Real.exp 9000≤Z) (r : ℕ) :
    canonicalRankMass Z r≤Z^3 := by
  have hn : ((3000-r:ℕ):ℝ)≤3000 := by exact_mod_cast (Nat.sub_le 3000 r)
  have he : Real.exp (3*((3000-r:ℕ):ℝ))≤Z :=
    (Real.exp_le_exp.mpr (by linarith)).trans hZ
  calc
    canonicalRankMass Z r ≤ Z*Z^2 := mul_le_mul_of_nonneg_right he (sq_nonneg Z)
    _ = Z^3 := by ring

theorem lowerCubeBin_transfer_mass (X B F : ℝ) (hB : B≠0) :
    (X/B^3)*(Real.exp 1*B)^3*F=Real.exp 3*(X*F) := by
  have he : (Real.exp 1)^3=Real.exp 3 := by
    rw [show (3:ℝ)=1+1+1 by norm_num,Real.exp_add,Real.exp_add]
    ring
  rw [mul_pow,←he]
  field_simp

theorem lowerCubeBin_energy_normalization (ell B F : ℝ) (hell : 0<ell) (hB : 0<B) :
    (ell*B^3)*((B*Real.sqrt ell)^2)⁻¹*
      (ell*(Real.exp 1*B)^2*F)*(ell*(Real.exp 1*B)^3*F)=
      Real.exp 5*((ell*B^3)*F)^2 := by
  have he : (Real.exp 1)^5=Real.exp 5 := by
    rw [show (5:ℝ)=1+1+1+1+1 by norm_num]
    simp only [Real.exp_add]
    ring
  rw [mul_pow,Real.sq_sqrt hell.le]
  simp only [mul_pow]
  rw [←he]
  field_simp

theorem canonical_live_scale_bounds (Z X F : ℝ) (r : ℕ)
    (hZ : Real.exp 9000≤Z) (hX : 1≤X) (hF : 1≤F)
    (hmass : X*F≤canonicalRankMass Z r) : X≤Z^3 ∧ F≤Z^3 := by
  have hm := hmass.trans (canonicalRankMass_global Z hZ r)
  constructor <;> nlinarith

theorem canonical_small_or_live (Z X F K : ℝ) (r : ℕ) (m : ActualEisensteinCubic.O)
    (hZ : Real.exp 9000≤Z) (_hX : 0<X) (hF : 1≤F) (hK : 0≤K) (hm : m≠0)
    (hmass : X*F≤canonicalRankMass Z r) (hinv : K*‖eisEmbedding m‖^2≤X*F) :
    K≤F ∨ (1<X ∧ X≤Z^3 ∧ F≤Z^3) := by
  by_cases hx : X≤1
  · exact Or.inl (smallColumn_row_le_label m hm X F K hx (by linarith) hK hinv)
  · have hl := lt_of_not_ge hx
    exact Or.inr ⟨hl,canonical_live_scale_bounds Z X F r hZ hl.le hF hmass⟩

def canonicalPoolCutoff (Bsupport Z : ℝ) : ℕ := ⌈Bsupport*Z^3⌉₊

theorem canonicalPoolCutoff_covers (Bsupport b Z X : ℝ)
    (hB : 0≤Bsupport) (hb : b≤Bsupport) (hX : 0≤X) (hXZ : X≤Z^3) :
    b*X≤(canonicalPoolCutoff Bsupport Z:ℝ) := by
  calc
    b*X ≤ Bsupport*X := mul_le_mul_of_nonneg_right hb hX
    _ ≤ Bsupport*Z^3 := mul_le_mul_of_nonneg_left hXZ hB
    _ ≤ _ := Nat.le_ceil _

end SecondPassArithmetic

open MeasureTheory
open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open ConcreteTraceCRT (eisEmbedding)

def rowFamilyEnergy (labels : Finset (Ideal ActualEisensteinCubic.O)) (P : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ) (K : ℝ) : ℝ :=
  (∑ I ∈ labels, nonzeroRowMajorantSum (P I) K).re

theorem rowFamilyEnergy_eq_sum (labels : Finset (Ideal ActualEisensteinCubic.O)) (P : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ)
    (K : ℝ) (hK : 0 < K) :
    rowFamilyEnergy labels P K =
      ∑ I ∈ labels, ∑ z ∈ (firstFrequencyDisk (2*K)).erase 0,
        (rowMajorant (‖eisEmbedding z‖^2/K)).re * ‖P I z‖^2 := by
  unfold rowFamilyEnergy
  simp only [nonzeroRowMajorantSum_exact_disk _ K hK, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem rowFamilyEnergy_nonneg (labels : Finset (Ideal ActualEisensteinCubic.O)) (P : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ)
    (K : ℝ) (hK : 0 < K) : 0 ≤ rowFamilyEnergy labels P K := by
  rw [rowFamilyEnergy_eq_sum labels P K hK]
  exact Finset.sum_nonneg (fun I hI => Finset.sum_nonneg
    (fun z hz => mul_nonneg (rowMajorant_nonneg _) (sq_nonneg _)))

theorem rowFamilyEnergy_integral_polynomial
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (K : ℝ) (hK : 0 < K)
    (b : ℝ → ℂ) (φ : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℝ → ℂ) (d : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hb : Integrable (fun t => ‖b t‖*(1+|t|)^d))
    (hφ : ∀ I z, Integrable (fun t => b t*φ I z t))
    (hbound : ∀ t, rowFamilyEnergy labels (fun I z => φ I z t) K ≤ E*(1+|t|)^(2*d)) :
    rowFamilyEnergy labels (fun I z => ∫ t : ℝ, b t*φ I z t) K ≤
      E*(∫ t : ℝ, ‖b t‖*(1+|t|)^d)^2 := by
  let R := (firstFrequencyDisk (2*K)).erase 0
  let w : ActualEisensteinCubic.O → ℝ := fun z => Real.sqrt ((rowMajorant (‖eisEmbedding z‖^2/K)).re)
  have hw (z : ActualEisensteinCubic.O) : 0 ≤ w z := Real.sqrt_nonneg _
  have hw2 (z : ActualEisensteinCubic.O) : (w z)^2 = (rowMajorant (‖eisEmbedding z‖^2/K)).re :=
    Real.sq_sqrt (rowMajorant_nonneg _)
  have hsum (P : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ) :
      (∑ x : labels × R, ‖(w x.2.val : ℂ)*P x.1.val x.2.val‖^2) = rowFamilyEnergy labels P K := by
    rw [rowFamilyEnergy_eq_sum labels P K hK]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_coe_sort (s := labels)
      (f := fun I : Ideal ActualEisensteinCubic.O => ∑ z : R, ‖(w z.val : ℂ)*P I z.val‖^2)]
    apply Finset.sum_congr rfl
    intro I hI
    rw [Finset.sum_coe_sort (s := R) (f := fun z : ActualEisensteinCubic.O => ‖(w z : ℂ)*P I z‖^2)]
    apply Finset.sum_congr rfl
    intro z hz
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw z),mul_pow,hw2]
  let ψ : labels × R → ℝ → ℂ := fun x t => (w x.2.val : ℂ)*φ x.1.val x.2.val t
  have hψ (x : labels × R) : Integrable (fun t => b t*ψ x t) := by
    convert (hφ x.1.val x.2.val).const_mul (w x.2.val : ℂ) using 1
    funext t
    dsimp only [ψ]
    ring
  have hψbound (t : ℝ) : (∑ x : labels × R, ‖ψ x t‖^2) ≤ E*(1+|t|)^(2*d) := by
    change (∑ x : labels × R, ‖(w x.2.val : ℂ)*φ x.1.val x.2.val t‖^2) ≤ _
    rw [hsum (fun I z => φ I z t)]
    exact hbound t
  have hi (x : labels × R) :
      (∫ t : ℝ, b t*ψ x t) = (w x.2.val : ℂ)*(∫ t : ℝ, b t*φ x.1.val x.2.val t) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [ψ]
    ring
  have hm := finite_integral_energy_polynomial b ψ d E hE hb hψ hψbound
  simp_rw [hi] at hm
  rwa [hsum (fun I z => ∫ t : ℝ, b t*φ I z t)] at hm

theorem rowFamilyEnergy_const_mul (labels : Finset (Ideal ActualEisensteinCubic.O)) (P : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ)
    (K : ℝ) (hK : 0 < K) (c : ℂ) :
    rowFamilyEnergy labels (fun I z => c*P I z) K = ‖c‖^2*rowFamilyEnergy labels P K := by
  simp only [rowFamilyEnergy_eq_sum _ _ K hK, norm_mul, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem canonicalSmoothedEnergy_eq_rowFamilyEnergy {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O))
    (H : Finset ι → ℂ) (K : ℝ) :
    canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels H K =
      rowFamilyEnergy labels (fun I z => fixedChildRow p hp hcop hg pool Ψ m H (idealGenerator I) z) K := rfl

end
section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O
open CanonicalCubeSeparation JointLogSeparation

variable {ι : Type*} [DecidableEq ι]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem separated_canonical_integrable
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (n : (ι →₀ ℕ) → ℝ) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O)
    (b V : 𝓢(ℝ,ℂ)) (B ell : ℝ) :
    Integrable (fun ξ : ℝ => b ξ *
      reopenedCanonicalRow p hp hcop hg pool Q (separatedCubeCoefficient β n B ξ)
        Ψ m f (fun T => frequencyTwist V ξ (columnLog p ell T)) z) := by
  let A : (ι →₀ ℕ) → Finset ι → ℂ := fun v T =>
    multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
      canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) T *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z
  have hi := reopening_finite_sum_integrable Q pool.powerset β A n (primeProductNorm p) B ell b V
  convert hi using 1
  funext ξ
  rw [reopenedCanonicalRow_integrand p hp hcop hg]
  rfl

theorem separated_canonical_family_energy
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (labels : Finset (Ideal ActualEisensteinCubic.O))
    (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ) (n : (ι →₀ ℕ) → ℝ)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (b V : 𝓢(ℝ,ℂ))
    (B ell K E : ℝ) (d : ℕ) (hB : 0 < B) (hell : 0 < ell) (hK : 0 < K) (hE : 0 ≤ E)
    (hbound : ∀ ξ : ℝ,
      rowFamilyEnergy labels (fun I z =>
        reopenedCanonicalRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
          Ψ m (idealGenerator I) (fun T => frequencyTwist V ξ (columnLog p ell T)) z) K ≤
        E*(1+|ξ|)^(2*d)) :
    rowFamilyEnergy labels (fun I z => ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
      ∫ ξ : ℝ, b ξ *
        reopenedCanonicalRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
          Ψ m (idealGenerator I) (fun T => frequencyTwist V ξ (columnLog p ell T)) z) K ≤
      (B^2*ell)⁻¹ * E*(∫ ξ : ℝ, ‖b ξ‖*(1+|ξ|)^d)^2 := by
  have hb : Integrable (fun ξ : ℝ => ‖b ξ‖*(1+|ξ|)^d) := by
    simpa only [Real.norm_eq_abs,mul_comm] using weighted_schwartz_integrable b d
  have hφ (I : Ideal ActualEisensteinCubic.O) (z : ActualEisensteinCubic.O) : Integrable (fun ξ : ℝ => b ξ *
      reopenedCanonicalRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
        Ψ m (idealGenerator I) (fun T => frequencyTwist V ξ (columnLog p ell T)) z) :=
    separated_canonical_integrable p hp hcop hg pool Q (β I) n Ψ m (idealGenerator I) z b V B ell
  have hm := rowFamilyEnergy_integral_polynomial labels K hK b
    (fun I z ξ => reopenedCanonicalRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
      Ψ m (idealGenerator I) (fun T => frequencyTwist V ξ (columnLog p ell T)) z)
    d E hE hb hφ hbound
  have hn : ‖((B*Real.sqrt ell : ℝ) : ℂ)⁻¹‖^2 = (B^2*ell)⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (mul_pos hB (Real.sqrt_pos.mpr hell)),inv_pow,mul_pow,Real.sq_sqrt hell.le]
  rw [rowFamilyEnergy_const_mul labels _ K hK, hn]
  convert mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ (B^2*ell)⁻¹) using 1 ; ring

end

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open ConcreteTraceCRT (eisEmbedding)

theorem rowFamilyEnergy_bound_sum {κ : Type*}
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (bins : Finset κ) (K : ℝ) (hK : 0 < K)
    (P A : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ) (B : κ → Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ) (c N : ℝ)
    (hbound : ∀ I ∈ labels, ∀ z ∈ (firstFrequencyDisk (2*K)).erase 0,
      ‖P I z‖^2 ≤ c*(‖A I z‖^2 + N*∑ j ∈ bins, ‖B j I z‖^2)) :
    rowFamilyEnergy labels P K ≤
      c*(rowFamilyEnergy labels A K + N*∑ j ∈ bins, rowFamilyEnergy labels (B j) K) := by
  let R := (firstFrequencyDisk (2*K)).erase 0
  let w : ActualEisensteinCubic.O → ℝ := fun z => (rowMajorant (‖eisEmbedding z‖^2/K)).re
  have hswap : (∑ I ∈ labels, ∑ z ∈ R, w z*∑ j ∈ bins, ‖B j I z‖^2) =
      ∑ j ∈ bins, rowFamilyEnergy labels (B j) K := by
    simp_rw [Finset.mul_sum]
    calc
      _ = ∑ I ∈ labels, ∑ j ∈ bins, ∑ z ∈ R, w z*‖B j I z‖^2 :=
        Finset.sum_congr rfl (fun I hI => Finset.sum_comm)
      _ = ∑ j ∈ bins, ∑ I ∈ labels, ∑ z ∈ R, w z*‖B j I z‖^2 := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl (fun j hj => (rowFamilyEnergy_eq_sum labels (B j) K hK).symm)
  rw [rowFamilyEnergy_eq_sum labels P K hK]
  calc
    _ ≤ ∑ I ∈ labels, ∑ z ∈ R,
        (c*(w z*‖A I z‖^2) + c*N*(∑ j ∈ bins, w z*‖B j I z‖^2)) := by
      apply Finset.sum_le_sum
      intro I hI
      apply Finset.sum_le_sum
      intro z hz
      calc
        _ ≤ w z*(c*(‖A I z‖^2 + N*∑ j ∈ bins, ‖B j I z‖^2)) :=
          mul_le_mul_of_nonneg_left (hbound I hI z hz) (rowMajorant_nonneg _)
        _ = _ := by rw [← Finset.mul_sum]; ring
    _ = c*(rowFamilyEnergy labels A K + N*∑ j ∈ bins, rowFamilyEnergy labels (B j) K) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hswap, ← rowFamilyEnergy_eq_sum labels A K hK]
      ring

theorem outsideCanonicalRow_family_binned_energy
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O))
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ K : ℝ)
    (hb : 0 ≤ b) (hX : 0 < X) (hK : 0 < K)
    (hW : ∀ t, W t ≠ 0 → t ≤ b) (hD : b*X ≤ D) :
    rowFamilyEnergy labels (fun I z => outsideCanonicalRow S D hbad Ψ m (idealGenerator I) z W X) K ≤
      2*X*(rowFamilyEnergy labels (fun I z =>
        shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z) W X H₀) K +
        (cubeLogRange b X).card * ∑ j ∈ cubeLogRange b X,
          rowFamilyEnergy labels (fun I z =>
            outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) Ψ m (idealGenerator I) z W X H₀) K) := by
  apply rowFamilyEnergy_bound_sum labels (cubeLogRange b X) K hK
  intro I hI z hz
  exact outsideCanonicalRow_binned_energy S D hbad hSp Ψ m (idealGenerator I) z W hWc
    b X H₀ hb hX hW hD

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O
open CanonicalCubeSeparation JointLogSeparation

theorem outsideCanonicalBin_energy
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ))
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (V : 𝓢(ℝ,ℂ))
    (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (B ell X H₀ K E : ℝ) (d : ℕ)
    (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell) (hK : 0 < K) (hE : 0 ≤ E)
    (hn : ∀ v ∈ Q, B ≤ (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ))
    (hn' : ∀ v ∈ Q, (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*B) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let β := fun I v => reopenedCubeCoefficient H₀
      (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
    let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
    (∀ ξ : ℝ, rowFamilyEnergy labels (fun I z =>
      reopenedCanonicalRow (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q
        (separatedCubeCoefficient (β I) n B ξ) Ψ m (idealGenerator I)
        (fun T => frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z) K ≤
      E*(1+|ξ|)^(2*d)) →
    rowFamilyEnergy labels (fun I z =>
      outsideCanonicalBin S D hbad Q Ψ m (idealGenerator I) z W X H₀) K ≤
      (B^2*ell)⁻¹ * E *
        (∫ ξ : ℝ, ‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^d)^2 := by
  dsimp only
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  let β := fun I v => reopenedCubeCoefficient H₀
    (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
  let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
  intro hbound
  have hrows : (fun I z => outsideCanonicalBin S D hbad Q Ψ m (idealGenerator I) z W X H₀) =
      (fun I z => ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∫ ξ : ℝ,
        reopeningCoefficient W a b ha hs hW ξ *
          reopenedCanonicalRow (poolPrimary F) (poolPrimary_ne_zero F hF)
            (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q
            (separatedCubeCoefficient (β I) n B ξ) Ψ m (idealGenerator I)
            (fun T => frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z) := by
    funext I z
    exact outsideCanonicalBin_separated S D hbad Q Ψ m (idealGenerator I) z W a b ha hs hW V hV
      B ell X H₀ hB hell hX hn hn'
  rw [hrows]
  exact separated_canonical_family_energy (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q labels β n Ψ m
    (reopeningCoefficient W a b ha hs hW) V B ell K E d hB hell hK hE hbound

end CanonicalRowCompletion

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (primeProduct)

theorem canonicalProgress_large (Z : ℝ) (hZ : Real.exp 9000≤Z) :
    Real.exp 4≤Z^((1:ℝ)/1000) := by
  have hh := Real.rpow_le_rpow (Real.exp_pos 9000).le hZ (by norm_num : (0:ℝ)≤1/1000)
  rw [Real.rpow_def_of_pos (Real.exp_pos 9000), Real.log_exp] at hh
  norm_num at hh
  exact (Real.exp_le_exp.mpr (by norm_num : (4:ℝ)≤9)).trans hh

theorem paddedCanonicalRatio (K M R Z η : ℝ) (hM : 0<M) (hZ : 0<Z) :
    Z^η*((K/Z^η)*R/(Real.exp 3*M))=(K*R/M)/Real.exp 3 := by
  field_simp

def canonicalRankMargin (σ η : ℝ) (r : ℕ) : ℝ :=
  σ-η*((3000-r:ℕ):ℝ)

theorem canonicalRankMargin_lower (σ η : ℝ) (hη : 0≤η) (r : ℕ) :
    σ-3000*η≤canonicalRankMargin σ η r := by
  have hn : ((3000-r:ℕ):ℝ)≤3000 := by exact_mod_cast (Nat.sub_le 3000 r)
  unfold canonicalRankMargin
  nlinarith

theorem canonicalRankMargin_step (σ η : ℝ) (hη : 0≤η) (r s : ℕ)
    (hr : r≤3000) (hs : s+1≤r) :
    canonicalRankMargin σ η s+η≤canonicalRankMargin σ η r := by
  have hn : 3000-r+1≤3000-s := by omega
  have hn' : ((3000-r:ℕ):ℝ)+1≤((3000-s:ℕ):ℝ) := by exact_mod_cast hn
  unfold canonicalRankMargin
  nlinarith

theorem canonicalRatio_exp_loss (K M R : ℝ) (hM : 0<M) :
    K*R/(Real.exp 3*M)=(K*R/M)/Real.exp 3 := by
  field_simp

theorem canonicalRankMargin_padding (Z σ η a : ℝ) (r s : ℕ)
    (hZ : 1<Z) (hη : 0≤η) (hr : r≤3000) (hs : s+1≤r)
    (ha : 0≤a) (hbound : a≤Z^(-canonicalRankMargin σ η r)) :
    Z^η*(a/Real.exp 3)≤Z^(-canonicalRankMargin σ η s) := by
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hmargin := canonicalRankMargin_step σ η hη r s hr hs
  calc
    Z^η*(a/Real.exp 3) ≤ Z^η*a :=
      mul_le_mul_of_nonneg_left (div_le_self ha (Real.one_le_exp (by norm_num)))
        (Real.rpow_nonneg hZ0.le _)
    _ ≤ Z^η*Z^(-canonicalRankMargin σ η r) :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hZ0.le _)
    _ = Z^(η-canonicalRankMargin σ η r) := by
      rw [sub_eq_add_neg,Real.rpow_add hZ0]
    _ ≤ Z^(-canonicalRankMargin σ η s) :=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem fixedTripleMask_ne_zero_of_bin (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex)
    (hq : q∈globalBinTriples p source side j) (m : ActualEisensteinCubic.O) (hm : m≠0) :
    fixedTripleMask m q≠0 := by
  obtain ⟨x,hx,hqx⟩ := Finset.mem_image.mp hq
  have ht := globalSecondFixedTriple_nonzero p hp x
  rw [←hqx]
  unfold fixedTripleMask
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hm
    (ConcretePrimeRowBridge.idealGenerator_ne_zero _ ht.1))
    (ConcretePrimeRowBridge.idealGenerator_ne_zero _ ht.2.1))
    (ConcretePrimeRowBridge.idealGenerator_ne_zero _ ht.2.2)

include hp in

theorem canonical_retained_scale_closure
    (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex)
    (hq : q∈globalBinTriples p source side j)
    (Z σ η X B F K : ℝ) (m : ActualEisensteinCubic.O)
    (hZ : 1<Z) (hZbig : Real.exp 9000≤Z) (hη : 0≤η) (hηsmall : η≤(1:ℝ)/1000)
    (hX : 0<X) (hB : 0<B) (hF : 1≤F) (hK : 1≤K) (hm : m≠0)
    (hprogress : Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F)
    (hstart : K≤Z^3) (hmass : X*F≤canonicalRankMass Z (fixedDepthRank Z K))
    (hinv : K*‖eisEmbedding m‖^2≤(X*F)*Z^(-σ))
    (hk : ∀x∈source,x.source.frequency≠0)
    (hb₁ : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Real.exp 1*B)
    (hb₂ : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Real.exp 1*B)
    (hretained : globalBinRadial (X/B^3)
      (globalPooledRowScale (K/Z^η) (X/B^3) (Real.exp 1*B) F j) j≤Z^η) :
    let X':=globalPooledColumnScale (X/B^3) j
    let F':=globalPooledLabelScale j
    let K':=globalLogRep j 8*Real.exp 1
    0<X' ∧ 1≤F' ∧ 1≤K' ∧
      fixedDepthRank Z K'+1≤fixedDepthRank Z K ∧ K'≤Z^3 ∧
      X'*F'≤canonicalRankMass Z (fixedDepthRank Z K') ∧
      K'*‖eisEmbedding (fixedTripleMask m q)‖^2≤(X'*F')*Z^(-σ) ∧
      fixedTripleMask m q≠0 ∧
      (∀I∈globalCanonicalLabels p source side q j,
        I≠⊥ ∧ Squarefree I ∧ (Ideal.absNorm I:ℝ)≤F') := by
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hK0 : 0<K := zero_lt_one.trans_le hK
  have hF0 : 0<F := zero_lt_one.trans_le hF
  have hBup : 0<Real.exp 1*B := mul_pos (Real.exp_pos _) hB
  have hell : 0<X/B^3 := div_pos hX (pow_pos hB 3)
  have hKpad : 0<K/Z^η := div_pos hK0 (Real.rpow_pos_of_pos hZ0 _)
  have hKle : K/Z^η≤K := div_le_self hK0.le (Real.one_le_rpow hZ.le hη)
  have hlarge : Real.exp 4≤(Real.exp 1*B)*F := (canonicalProgress_large Z hZbig).trans hprogress
  obtain ⟨hXc,hFc,hKc,hMc,hsmall,hrank,hrank0,hratio,hlabels⟩ :=
    globalRetained_canonical_geometry p hp source side q j hq Z η K (K/Z^η)
      (X/B^3) (Real.exp 1*B) F m hZ hηsmall hK0 hKpad hKle hell hBup hF
      hprogress hlarge hstart hk hb₁ hb₂ hretained
  have hMc' : globalPooledColumnScale (X/B^3) j*globalPooledLabelScale j≤Real.exp 3*(X*F) := by
    simpa only [lowerCubeBin_transfer_mass X B F hB.ne'] using hMc
  have hratio' : globalLogRep j 8*Real.exp 1*‖eisEmbedding (fixedTripleMask m q)‖^2/
      (globalPooledColumnScale (X/B^3) j*globalPooledLabelScale j)≤Z^(-σ) := by
    rw [lowerCubeBin_transfer_mass X B F hB.ne',paddedCanonicalRatio K (X*F)
      (‖eisEmbedding m‖^2) Z η (mul_pos hX hF0) hZ0] at hratio
    apply hratio.trans
    apply (div_le_self (div_nonneg (mul_nonneg hK0.le (sq_nonneg _)) (mul_pos hX hF0).le)
      (Real.one_le_exp (by norm_num))).trans
    exact (div_le_iff₀ (mul_pos hX hF0)).mpr (by simpa only [mul_comm] using hinv)
  refine ⟨hXc,hFc,hKc,hrank,?_,?_,?_,fixedTripleMask_ne_zero_of_bin p hp source side q j hq m hm,
    globalCanonicalLabels_bounds p hp source side q j hk⟩
  · exact hsmall.trans ((div_le_self hK0.le
      (Real.one_le_rpow hZ.le (by norm_num : (0:ℝ)≤1/1000))).trans hstart)
  · exact canonicalRankMass_child Z X F _ _ _ _ hrank0 hrank hmass hMc'
  · exact (div_le_iff₀ (mul_pos hXc (zero_lt_one.trans_le hFc))).mp hratio' |>.trans_eq (by ring)

include hp in

theorem canonical_retained_unpadded_closure
    (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex)
    (hq : q∈globalBinTriples p source side j)
    (Z σ η X B F K : ℝ) (m : ActualEisensteinCubic.O)
    (hZ : 1<Z) (hZbig : Real.exp 9000≤Z) (hη : 0≤η) (hηsmall : η≤(1:ℝ)/1000)
    (hX : 0<X) (hB : 0<B) (hF : 1≤F) (hK : 1≤K) (hm : m≠0)
    (hprogress : Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F)
    (hstart : K≤Z^3) (hmass : X*F≤canonicalRankMass Z (fixedDepthRank Z K))
    (hinv : K*‖eisEmbedding m‖^2≤
      (X*F)*Z^(-canonicalRankMargin σ η (fixedDepthRank Z K)))
    (hk : ∀x∈source,x.source.frequency≠0)
    (hb₁ : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Real.exp 1*B)
    (hb₂ : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Real.exp 1*B)
    (hretained : globalBinRadial (X/B^3)
      (globalPooledRowScale K (X/B^3) (Real.exp 1*B) F j) j≤Z^η) :
    let X':=globalPooledColumnScale (X/B^3) j
    let F':=globalPooledLabelScale j
    let K':=globalLogRep j 8*Real.exp 1
    0<X' ∧ 1≤F' ∧ 1≤K' ∧
      fixedDepthRank Z K'+1≤fixedDepthRank Z K ∧ K'≤Z^3 ∧
      X'*F'≤canonicalRankMass Z (fixedDepthRank Z K') ∧
      K'*‖eisEmbedding (fixedTripleMask m q)‖^2≤
        (X'*F')*Z^(-canonicalRankMargin σ η (fixedDepthRank Z K')) ∧
      fixedTripleMask m q≠0 ∧
      (∀I∈globalCanonicalLabels p source side q j,
        I≠⊥ ∧ Squarefree I ∧ (Ideal.absNorm I:ℝ)≤F') := by
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hK0 : 0<K := zero_lt_one.trans_le hK
  have hF0 : 0<F := zero_lt_one.trans_le hF
  have hBup : 0<Real.exp 1*B := mul_pos (Real.exp_pos _) hB
  have hell : 0<X/B^3 := div_pos hX (pow_pos hB 3)
  have hlarge : Real.exp 4≤(Real.exp 1*B)*F := (canonicalProgress_large Z hZbig).trans hprogress
  obtain ⟨hXc,hFc,hKc,hMc,hsmall,hrank,hrank0,hratio,hlabels⟩ :=
    globalRetained_canonical_geometry p hp source side q j hq Z η K K
      (X/B^3) (Real.exp 1*B) F m hZ hηsmall hK0 hK0 le_rfl hell hBup hF
      hprogress hlarge hstart hk hb₁ hb₂ hretained
  have hMc' : globalPooledColumnScale (X/B^3) j*globalPooledLabelScale j≤Real.exp 3*(X*F) := by
    simpa only [lowerCubeBin_transfer_mass X B F hB.ne'] using hMc
  have hparent : K*‖eisEmbedding m‖^2/(X*F)≤
      Z^(-canonicalRankMargin σ η (fixedDepthRank Z K)) :=
    (div_le_iff₀ (mul_pos hX hF0)).mpr (by simpa only [mul_comm] using hinv)
  have hratio' : globalLogRep j 8*Real.exp 1*‖eisEmbedding (fixedTripleMask m q)‖^2/
      (globalPooledColumnScale (X/B^3) j*globalPooledLabelScale j)≤
      Z^(-canonicalRankMargin σ η (fixedDepthRank Z (globalLogRep j 8*Real.exp 1))) := by
    rw [lowerCubeBin_transfer_mass X B F hB.ne',canonicalRatio_exp_loss K (X*F)
      (‖eisEmbedding m‖^2) (mul_pos hX hF0)] at hratio
    exact hratio.trans (canonicalRankMargin_padding Z σ η _ _ _ hZ hη hrank0 hrank
      (div_nonneg (mul_nonneg hK0.le (sq_nonneg _)) (mul_pos hX hF0).le) hparent)
  refine ⟨hXc,hFc,hKc,hrank,?_,?_,?_,fixedTripleMask_ne_zero_of_bin p hp source side q j hq m hm,
    globalCanonicalLabels_bounds p hp source side q j hk⟩
  · exact hsmall.trans ((div_le_self hK0.le
      (Real.one_le_rpow hZ.le (by norm_num : (0:ℝ)≤1/1000))).trans hstart)
  · exact canonicalRankMass_child Z X F _ _ _ _ hrank0 hrank hmass hMc'
  · exact (div_le_iff₀ (mul_pos hXc (zero_lt_one.trans_le hFc))).mp hratio' |>.trans_eq (by ring)

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0234

/-! Original module: OAI.NumberTheory.DirichletL.RowCompletion.PolynomialHeight
Source SHA256: e225c890d9f8601b6358ca1158be947ff459a010480fd4f3fc13749c978bebdb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0235


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

open scoped BigOperators Classical
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalCubeSeparation

theorem outside_separated_cube_coefficient_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (Ψ : ActualEisensteinCubic.O →* ℂ), (∀ z, ‖Ψ z‖ ≤ 1) →
      ∀ (m f : ActualEisensteinCubic.O) (H₀ B ξ : ℝ)
      (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ),
      0 < B →
      B ≤ (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) →
      (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*B →
      ‖separatedCubeCoefficient
        (fun u => reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1)
          (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) u))
        (fun u => (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) u) : ℝ))
        B ξ v‖ ≤ C*(Real.exp 1*B)^ε := by
  obtain ⟨C,hC,hbound⟩ := reopenedCubeCoefficient_small_power ε hε
  refine ⟨C*Real.exp (1/2),mul_pos hC (Real.exp_pos _),?_⟩
  intro S D Ψ hΨ m f H₀ B ξ v hB hn hn'
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have ht : ∀ z, ‖rowTwist Ψ (m*excludedGenerator S) f 1 z‖ ≤ 1 :=
    rowTwist_norm Ψ hΨ (m*excludedGenerator S) f 1
  have hβ : ‖reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)‖ ≤
      C*(Real.exp 1*B)^ε := by
    apply (hbound H₀ _ ht _ (cubeIdeal_ne_zero F v)).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hn' hε.le) hC.le
  have hh := separatedCubeCoefficient_bound
    (fun u => reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F u))
    (fun u => (Ideal.absNorm (cubeIdeal F u) : ℝ)) B ξ (C*(Real.exp 1*B)^ε)
    hB (by positivity) v hn hn' hβ
  convert hh using 1 ; ring

end CanonicalRowCompletion

namespace CompletedHeight

open MeasureTheory Filter Set
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff Topology
open FourierBridge JointLogSeparation

def positiveCutoff (a b : ℝ) (ha : 0 < a) : ContDiffBump ((a+max a b)/2) where
  rIn := (max a b-a)/2+a/4
  rOut := (max a b-a)/2+a/2
  rIn_pos := by linarith [le_max_left a b]
  rIn_lt_rOut := by linarith

lemma positiveCutoff_one (a b : ℝ) (ha : 0 < a) (x : ℝ) (hx : x∈Icc a b) :
    positiveCutoff a b ha x=1 := by
  apply (positiveCutoff a b ha).one_of_mem_closedBall
  change dist x ((a+max a b)/2) ≤ (max a b-a)/2+a/4
  rw [Real.dist_eq,abs_le]
  constructor <;> linarith [hx.1,hx.2,le_max_right a b]

lemma positiveCutoff_zero (a b : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < a/2) :
    positiveCutoff a b ha x=0 := by
  by_contra hn
  have hm : x∈Function.support (positiveCutoff a b ha) := hn
  rw [(positiveCutoff a b ha).support_eq] at hm
  change dist x ((a+max a b)/2) < (max a b-a)/2+a/2 at hm
  rw [Real.dist_eq,abs_lt] at hm
  linarith [hm.1]

def logCorrection (a b : ℝ) (ha : 0 < a) (x : ℝ) : ℝ :=
  positiveCutoff a b ha x*(Real.log x-x)

def patchedLog (a b : ℝ) (ha : 0 < a) (x : ℝ) : ℝ := x+logCorrection a b ha x

lemma logCorrection_compact (a b : ℝ) (ha : 0 < a) :
    HasCompactSupport (logCorrection a b ha) := (positiveCutoff a b ha).hasCompactSupport.mul_right

lemma logCorrection_smooth (a b : ℝ) (ha : 0 < a) :
    ContDiff ℝ ∞ (logCorrection a b ha) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x=0
  · subst x
    have he : logCorrection a b ha =ᶠ[𝓝 (0:ℝ)] (fun _=>0) := by
      filter_upwards [isOpen_Iio.mem_nhds (by linarith : (0:ℝ)<a/2)] with y hy
      simp only [logCorrection,positiveCutoff_zero a b ha y hy,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (positiveCutoff a b ha).contDiff.contDiffAt.mul
      ((Real.contDiffAt_log.mpr hx).sub contDiffAt_id)

lemma patchedLog_temperate (a b : ℝ) (ha : 0 < a) :
    Function.HasTemperateGrowth (patchedLog a b ha) :=
  Function.HasTemperateGrowth.id'.add
    ((logCorrection_compact a b ha).hasTemperateGrowth (logCorrection_smooth a b ha))

lemma patchedLog_proper (a b : ℝ) (ha : 0 < a) :
    ∃k : ℕ, ∃C : ℝ, ∀x : ℝ, ‖x‖ ≤ C*(1+‖patchedLog a b ha x‖)^k := by
  obtain ⟨x₀,hx₀⟩ := (logCorrection_smooth a b ha).continuous.norm.exists_forall_ge_of_hasCompactSupport
    (logCorrection_compact a b ha).norm
  refine ⟨1,‖logCorrection a b ha x₀‖+1,?_⟩
  intro x
  have ht : ‖x‖ ≤ ‖patchedLog a b ha x‖+‖logCorrection a b ha x‖ := by
    simpa only [patchedLog,add_sub_cancel_right] using
      norm_sub_le (patchedLog a b ha x) (logCorrection a b ha x)
  have hb := hx₀ x
  simp only [pow_one]
  nlinarith [norm_nonneg (patchedLog a b ha x),norm_nonneg (logCorrection a b ha x₀)]

lemma patchedLog_eq_log (a b : ℝ) (ha : 0 < a) (x : ℝ) (hx : x∈Icc a b) :
    patchedLog a b ha x=Real.log x := by
  simp only [patchedLog,logCorrection,positiveCutoff_one a b ha x hx,one_mul]
  ring

def sourceTwistCLM (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0 < a) :
    𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
  ((SchwartzMap.smulLeftCLM ℂ (W : ℝ→ℂ)).restrictScalars ℝ).comp
    (SchwartzMap.compCLM ℝ (patchedLog_temperate a b ha) (patchedLog_proper a b ha))

lemma sourceTwistCLM_apply (W g : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0 < a) (x : ℝ) :
    sourceTwistCLM W a b ha g x = W x*g (patchedLog a b ha x) := by
  change (SchwartzMap.smulLeftCLM ℂ (W : ℝ→ℂ)
    ((SchwartzMap.compCLM ℝ (patchedLog_temperate a b ha) (patchedLog_proper a b ha)) g)) x = _
  rw [SchwartzMap.smulLeftCLM_apply_apply W.hasTemperateGrowth]
  rfl

def normTwistedSource (W : ℝ→ℂ) (t x : ℝ) : ℂ := logPhase t (Real.log x)*W x

lemma normTwistedSource_support (W : ℝ→ℂ) (t : ℝ) :
    Function.support (normTwistedSource W t) ⊆ Function.support W := by
  intro x hx hz
  exact hx (by simp only [normTwistedSource,hz,mul_zero])

theorem frequencyTwist_finite_bound (g : 𝓢(ℝ,ℂ)) (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ, ∃C : ℝ, 0 < C ∧ ∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (frequencyTwist g t) ≤ C*(1+‖t‖)^n := by
  let n := S.sup Prod.snd
  let c : ℕ×ℕ → ℝ := fun z => (2:ℝ)^z.2*(1+2*Real.pi)^z.2*derivativeSeminormSum g z.1 z.2
  let C := 1+∑z∈S,c z
  have hc : ∀z,0≤c z := fun z => by dsimp [c]; exact mul_nonneg (by positivity) (derivativeSeminormSum_nonneg _ _ _)
  have hC : 0<C := by dsimp [C]; have := Finset.sum_nonneg (fun z (_ : z∈S) => hc z); linarith
  refine ⟨n,C,hC,?_⟩
  intro t
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  have hzC : c z≤C := by
    have hh := Finset.single_le_sum (fun z (_ : z∈S) => hc z) hz
    dsimp [C]
    linarith
  have hzn : z.2≤n := Finset.le_sup hz
  have hh := frequencyTwist_seminorm_polynomial g t z.1 z.2
  exact hh.trans (mul_le_mul hzC (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hzn)
    (by positivity) hC.le)

theorem normTwistedSource_schwartz (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support (W : ℝ→ℂ) ⊆ Icc a b) :
    ∃ G : ℝ→𝓢(ℝ,ℂ), (∀t x,G t x=normTwistedSource W t x) ∧
      (∀S : Finset (ℕ×ℕ), ∃n : ℕ, ∃C : ℝ, 0<C ∧ ∀t : ℝ,
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G t)≤C*(1+‖t‖)^n) := by
  let M := |Real.log a|+|Real.log b|+1
  have hM : 0≤M := by dsimp [M]; positivity
  obtain ⟨v,hvc,hvs,hvone,hvsupp,_⟩ := exists_complex_smooth_cutoff M hM
  let V : 𝓢(ℝ,ℂ) := hvc.toSchwartzMap hvs
  let G : ℝ→𝓢(ℝ,ℂ) := fun t => sourceTwistCLM W a b ha (frequencyTwist V t)
  refine ⟨G,?_,?_⟩
  · intro t x
    rw [show G t x=sourceTwistCLM W a b ha (frequencyTwist V t) x from rfl,
      sourceTwistCLM_apply,frequencyTwist_apply]
    by_cases hx : W x=0
    · simp only [normTwistedSource,hx,zero_mul,mul_zero]
    · have hxi := hs hx
      rw [patchedLog_eq_log a b ha x hxi]
      have hlog : |Real.log x|≤M := by
        have hlo := Real.log_le_log ha hxi.1
        have hhi := Real.log_le_log (lt_of_lt_of_le ha hxi.1) hxi.2
        rw [abs_le]
        constructor <;> dsimp [M] <;> linarith [neg_abs_le (Real.log a),le_abs_self (Real.log b),
          abs_nonneg (Real.log a),abs_nonneg (Real.log b)]
      have hv : V (Real.log x)=1 := hvone _ hlog
      simp only [hv,mul_one,normTwistedSource]
      ring
  · intro S
    obtain ⟨s,C,hC,hcontrol⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control
      (sourceTwistCLM W a b ha) S
    obtain ⟨n,D,hD,hbound⟩ := frequencyTwist_finite_bound V s
    refine ⟨n,C*D,mul_pos hC hD,?_⟩
    intro t
    exact (hcontrol _).trans ((mul_le_mul_of_nonneg_left (hbound t) hC.le).trans_eq (by ring))

end CompletedHeight

namespace LocalLogFourier

open MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
theorem coupled_positive_log_separation_linear_constant
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : ℝ → ℂ),
      ContDiffOn ℝ ∞ F (Set.Ioi 0) → ∀ CF : ℝ, 0 ≤ CF →
      (∀ i ≤ J + (volume : Measure ℝ).integrablePower, ∀ x : ℝ, 0 < x →
        (1 + x)^A * ‖eulerDeriv F i x‖ ≤ CF) →
      ∀ R : ℝ, 0 < R →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ y : ι → ℝ,
          (∏ j : ι, W j (y j)) *
            F (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, W j (y j) *
              FourierBridge.logPhase t (a j * y j)) * b t) ∧
        Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C * CF ∧
        (∀ t : ℝ, (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ C * CF) := by
  classical
  let T : ℝ := ∑ j : ι, |a j| * M j
  have hT : 0 ≤ T := by
    dsimp [T]
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (abs_nonneg _) (hM j)
  let K : ℕ := J + (volume : Measure ℝ).integrablePower
  let Lwin : ℝ := T + 1
  let m : ℝ := Real.exp (-Lwin)
  have hL : 0 ≤ Lwin := by dsimp [Lwin]; linarith
  have hm : 0 < m := Real.exp_pos _
  have hm1 : m ≤ 1 := by
    dsimp [m]
    simpa using (Real.exp_le_exp.mpr (show -Lwin ≤ 0 by linarith))
  obtain ⟨V, CW, hVc, hVs, hVone, hCW, hVderiv, hwindow⟩ :=
    FourierBridge.exists_complex_smooth_cutoff_with_derivative_bounds T K hT
  let P₀ : ℝ := momentConstant K Lwin CW 1
  let B₀ : ℝ := (2 : ℝ)^J * (FourierBridge.coefficientMomentBound 0 P₀ +
    FourierBridge.coefficientMomentBound J P₀)
  let D₀ : ℝ := FourierBridge.fourierPointBound J P₀
  let C₀ : ℝ := (B₀+D₀)/m^A
  have hP₀ : 0 ≤ P₀ := momentConstant_nonneg K Lwin CW 1 hL hCW zero_le_one
  have hB₀ : 0 ≤ B₀ := by
    dsimp [B₀]
    exact mul_nonneg (by positivity) (add_nonneg
      (FourierBridge.coefficientMomentBound_nonneg 0 P₀ hP₀)
      (FourierBridge.coefficientMomentBound_nonneg J P₀ hP₀))
  have hD₀ : 0 ≤ D₀ := FourierBridge.fourierPointBound_nonneg J P₀ hP₀
  refine ⟨C₀,by dsimp [C₀]; positivity,?_⟩
  intro F hFpos CF hCF hEuler
  let P : ℝ := momentConstant K Lwin CW CF
  let B : ℝ := (2 : ℝ)^J * (FourierBridge.coefficientMomentBound 0 P +
    FourierBridge.coefficientMomentBound J P)
  let Bpoint : ℝ := FourierBridge.fourierPointBound J P
  have hP : 0 ≤ P := momentConstant_nonneg K Lwin CW CF hL hCW hCF
  have hPeq : P=P₀*CF := by
    dsimp [P,P₀]
    unfold momentConstant derivativeConstant
    simp only [Finset.sum_mul,Finset.mul_sum,mul_one]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hBeq : B=B₀*CF := by
    dsimp [B,B₀]
    rw [hPeq]
    unfold FourierBridge.coefficientMomentBound
    ring
  have hBpeq : Bpoint=D₀*CF := by
    dsimp [Bpoint,D₀]
    rw [hPeq]
    unfold FourierBridge.fourierPointBound FourierBridge.fourierSeminormBound
    ring
  intro R hR
  let b : 𝓢(ℝ, ℂ) := 𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · intro y
    have hactive : (∏ j : ι, W j (y j)) ≠ 0 →
        V (∑ j : ι, a j * y j) = 1 :=
      FourierBridge.coupled_cutoff_active W V a y M hWwindow
        (by simpa [T] using hVone)
    simpa [b] using coupled_positive_log_separation W F V R a y
      hVc hVs hFpos hR hactive
  · exact AnalyticBridge.schwartz_fourier_one_plus_integrable
      (positiveLogProfile V F R hVc hVs hFpos hR) J
  · have hwindow' : ∀ s,
        (∃ i ≤ K, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
          m ≤ Real.exp s ∧ |s| ≤ Lwin := by
      intro s hs
      exact ⟨(hwindow s hs).1, (hwindow s hs).2.2⟩
    have hbound := positive_log_fourier_bound V F R m Lwin CW CF A J
      hVc hVs hFpos hR hm hm1 hL hCW hCF
      (by simpa [K] using hVderiv)
      (by simpa only [K] using hwindow')
      (by simpa [K] using hEuler)
    have hb : (1 + R) ^ A * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ B / m ^ A := by
      simpa [B, P, b, K, Lwin, m] using hbound
    apply hb.trans
    rw [hBeq]
    dsimp [C₀]
    have hh := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD₀ : B₀≤B₀+D₀) hCF
    exact (div_le_div_of_nonneg_right hh (by positivity)).trans_eq (by ring)
  · intro t
    let g := positiveLogProfile V F R hVc hVs hFpos hR
    have hwindow' : ∀ s,
        (∃ i ≤ K, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
          m ≤ Real.exp s ∧ |s| ≤ Lwin := by
      intro s hs
      exact ⟨(hwindow s hs).1, (hwindow s hs).2.2⟩
    have hsource (n : ℕ) (hn : n ≤ J) :
        (m ^ A * (1 + R) ^ A) *
          ((SchwartzMap.seminorm ℝ 0 n) g +
            (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower n) g) ≤ P := by
      apply positive_log_source_pair V F R m Lwin CW CF P A K n
        hVc hVs hFpos hR hm hm1 hL hCW hCF
      · dsimp [K]; omega
      · exact hVderiv
      · exact hwindow'
      · exact hEuler
      · intro i hi
        exact momentConstant_dominates K i Lwin CW CF hL hCW hCF hi
    have hpoint := FourierBridge.uniform_fourier_pointwise g J
      (m ^ A * (1 + R) ^ A) P (by positivity) hP hsource t
    have hb : (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ Bpoint / m ^ A := by
      apply (le_div_iff₀ (pow_pos hm A)).mpr
      simpa only [g, b, Bpoint, mul_assoc, mul_left_comm, mul_comm] using hpoint
    apply hb.trans
    rw [hBpeq]
    dsimp [C₀]
    have hh := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB₀ : D₀≤B₀+D₀) hCF
    exact (div_le_div_of_nonneg_right hh (by positivity)).trans_eq (by ring)

end LocalLogFourier

namespace CompletedHeight

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open CompletedGauss

def HasPolynomialKernel (P : ℝ→ℝ→ℂ) : Prop :=
  (∀t,ContDiffOn ℝ ∞ (CubicReflectionKernel.paperKernel (Vstar (P t))) (Set.Ioi 0)) ∧
  ∀ A K : ℕ,∃n : ℕ,∃C : ℝ,0<C ∧ ∀t : ℝ,∀i≤K,∀x : ℝ,0<x →
    (1+x)^A*‖LocalLogFourier.eulerDeriv (CubicReflectionKernel.paperKernel (Vstar (P t))) i x‖≤
      C*(1+‖t‖)^n

theorem normTwistedSource_polynomial_kernel (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    HasPolynomialKernel (normTwistedSource W) := by
  let S := vstarSchwartz W a b ha hsupp hW
  have hS : Function.support (S : ℝ→ℂ) ⊆ Set.Icc a b := Vstar_support W a b hsupp
  obtain ⟨G,hG,hbound⟩ := normTwistedSource_schwartz S a b ha hS
  have hlink (t : ℝ) : (G t : ℝ→ℂ)=Vstar (normTwistedSource W t) := by
    funext x
    rw [hG t x]
    change FourierBridge.logPhase t (Real.log x)*((Real.sqrt x:ℂ)*W x)=
      (Real.sqrt x:ℂ)*(FourierBridge.logPhase t (Real.log x)*W x)
    ring
  have hGs (t : ℝ) : Function.support (G t : ℝ→ℂ)⊆Set.Icc a b := by
    intro x hx
    change G t x≠0 at hx
    rw [hG t x] at hx
    exact hS (normTwistedSource_support S t hx)
  constructor
  · intro t
    rw [←hlink t]
    exact CubicReflectionKernel.paperKernel_compact_source_smooth (G t) a b ha (hGs t) ((G t).smooth ⊤)
  · intro A K
    obtain ⟨s,D,hD,hkernel⟩ := CubicReflectionKernel.paperKernel_euler_source_uniform_weighted_bound a b ha A K
    obtain ⟨n,C,hC,hsource⟩ := hbound s
    refine ⟨n,D*C,mul_pos hD hC,?_⟩
    intro t i hi x hx
    rw [←hlink t]
    exact (hkernel (G t) (hGs t) i hi x hx).trans
      ((mul_le_mul_of_nonneg_left (hsource t) hD.le).trans_eq (by ring))

theorem polynomial_kernel_log_separation {ι : Type*} [Fintype ι]
    (P : ℝ→ℝ→ℂ) (hP : HasPolynomialKernel P)
    (V : ι→ℝ→ℂ) (slope M : ι→ℝ) (hM : ∀i,0≤M i)
    (hV : ∀i y,V i y≠0 → |y|≤M i) (A J : ℕ) :
    ∃n : ℕ,∃C : ℝ,0≤C ∧ ∀θ R : ℝ,0<R → ∃B : 𝓢(ℝ,ℂ),
      (∀y : ι→ℝ,(∏i,V i (y i))*CubicReflectionKernel.paperKernel (Vstar (P θ))
          (R*Real.exp (∑i,slope i*y i))=
        ∫t : ℝ,(∏i,V i (y i)*FourierBridge.logPhase t (slope i*y i))*B t) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖B t‖) ∧
      (1+R)^A*(∫t : ℝ,(1+‖t‖)^J*‖B t‖)≤C*(1+‖θ‖)^n ∧
      (∀t : ℝ,(1+R)^A*(1+‖t‖)^J*‖B t‖≤C*(1+‖θ‖)^n) := by
  obtain ⟨n,D,hD,hkernel⟩ := hP.2 A (J+(volume : Measure ℝ).integrablePower)
  obtain ⟨C,hC,hsep⟩ := LocalLogFourier.coupled_positive_log_separation_linear_constant
    V slope M hM hV A J
  refine ⟨n,C*D,mul_nonneg hC hD.le,?_⟩
  intro θ R hR
  obtain ⟨B,hB,hi,hb,hp⟩ := hsep (CubicReflectionKernel.paperKernel (Vstar (P θ))) (hP.1 θ)
    (D*(1+‖θ‖)^n) (by positivity) (hkernel θ) R hR
  refine ⟨B,hB,hi,?_,?_⟩
  · exact hb.trans_eq (by ring)
  · intro t
    exact (hp t).trans_eq (by ring)

theorem polynomial_kernel_three_window
    (P : ℝ→ℝ→ℂ) (hP : HasPolynomialKernel P)
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂) (A : ℕ) :
    ∃n : ℕ,∃C : ℝ,0≤C ∧ ∀θ R : ℝ,0<R → ∃B : 𝓢(ℝ,ℂ),
      (∀r u v : ℝ,V₀ r*V₁ u*V₂ v*CubicReflectionKernel.paperKernel (Vstar (P θ))
        (R*Real.exp (-2*r+u+3*v))=
        ∫t : ℝ,(V₀ r*FourierBridge.logPhase t (-2*r))*
          (V₁ u*FourierBridge.logPhase t u)*(V₂ v*FourierBridge.logPhase t (3*v))*B t) ∧
      (1+R)^A*(∫t : ℝ,‖B t‖)≤C*(1+‖θ‖)^n := by
  let V : Fin 3→ℝ→ℂ := ![V₀,V₁,V₂]
  let slope : Fin 3→ℝ := ![-2,1,3]
  let M : Fin 3→ℝ := ![M₀,M₁,M₂]
  have hm : ∀i,0≤M i := by intro i; fin_cases i <;> assumption
  have hv : ∀i y,V i y≠0 → |y|≤M i := by intro i; fin_cases i <;> assumption
  obtain ⟨n,C,hC,h⟩ := polynomial_kernel_log_separation P hP V slope M hm hv A 0
  refine ⟨n,C,hC,?_⟩
  intro θ R hR
  obtain ⟨B,hB,hi,hbound,hpoint⟩ := h θ R hR
  refine ⟨B,?_,by simpa only [pow_zero,one_mul] using hbound⟩
  intro r u v
  simpa [V,slope,Fin.prod_univ_succ,Fin.sum_univ_succ,mul_assoc,add_assoc] using hB ![r,u,v]

end CompletedHeight

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedHeight
open CompletedGauss hiding O
open ActualEisensteinCubic
open CanonicalQuadraticSieve hiding O
theorem polynomial_smooth_quadratic
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (hV₀n : ∀y,‖V₀ y‖≤1) (hV₁n : ∀y,‖V₁ y‖≤1) (hV₂n : ∀y,‖V₂ y‖≤1)
    (P : ℝ→ℝ→ℂ) (hP : HasPolynomialKernel P)
    (A : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀θ K U B lengthScale R : ℝ,1≤K → 1≤U → 1≤B → 0≤lengthScale → 0<R →
    ∀S T : Finset (Ideal ActualEisensteinCubic.O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
    ∀β : Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ,(∀n∈S,∀v∈T,‖β n v‖≤lengthScale) →
    ∀yr : idealRange K→ℝ,∀yn yb : Ideal ActualEisensteinCubic.O→ℝ,
    (∑k : idealRange K,‖∑n∈S,∑v∈T,
      quadraticRow k.val (primaryGenerator (n*v))*β n v*
      (V₀ (yr k)*V₁ (yn n)*V₂ (yb v)*CubicReflectionKernel.paperKernel (Vstar (P θ))
        (R*Real.exp (-2*yr k+yn n+3*yb v)))‖^2)≤
      (C*(1+‖θ‖)^heightDegree)*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2/(1+R)^(2*A) := by
  obtain ⟨Cq,hCq,hq⟩ := integrated_product_quadratic ε hε
  obtain ⟨heightDegree,Ck₀,hCk₀,hkernel⟩ := polynomial_kernel_three_window P hP V₀ V₁ V₂ M₀ M₁ M₂
    hM₀ hM₁ hM₂ hV₀ hV₁ hV₂ A
  refine ⟨2*heightDegree,Cq*(Ck₀^2+1),by positivity,?_⟩
  intro θ K U B lengthScale R hK hU hB hL hR S T hS hT β hβ yr yn yb
  let Ck := Ck₀*(1+‖θ‖)^heightDegree
  have hCk : 0≤Ck := by dsimp [Ck]; positivity
  have hCoeff : Cq*(Ck^2+1)≤(Cq*(Ck₀^2+1))*(1+‖θ‖)^(2*heightDegree) := by
    have hh : 1≤(1+‖θ‖)^(2*heightDegree) := one_le_pow₀ (by linarith [norm_nonneg θ])
    have he : Ck^2=Ck₀^2*(1+‖θ‖)^(2*heightDegree) := by
      dsimp [Ck]
      rw [mul_pow,←pow_mul]
      congr 2
      omega
    rw [he]
    nlinarith [sq_nonneg Ck₀]
  obtain ⟨g,hsep,hg⟩ := hkernel θ R hR
  change (1+R)^A*(∫t : ℝ,‖g t‖)≤Ck at hg
  let rowPhase : idealRange K→ℝ→ℂ := fun k t => V₀ (yr k)*FourierBridge.logPhase t (-2*yr k)
  let βt : ℝ→Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ := fun t n v =>
    β n v*(V₁ (yn n)*FourierBridge.logPhase t (yn n))*(V₂ (yb v)*FourierBridge.logPhase t (3*yb v))
  have hphase (t x : ℝ) : ‖FourierBridge.logPhase t x‖=1 := FourierBridge.logPhase_norm t x
  have hrowPhase (k : idealRange K) (t : ℝ) : ‖rowPhase k t‖≤1 := by
    simp only [rowPhase,norm_mul,hphase,mul_one]
    exact hV₀n _
  have hβt (t : ℝ) (n : Ideal ActualEisensteinCubic.O) (hn : n∈S) (v : Ideal ActualEisensteinCubic.O) (hv : v∈T) : ‖βt t n v‖≤lengthScale := by
    simp only [βt,norm_mul,hphase,mul_one]
    exact (mul_le_of_le_one_right (by positivity)
      (hV₂n _)).trans ((mul_le_of_le_one_right (norm_nonneg _) (hV₁n _)).trans (hβ n hn v hv))
  have hrowPhasec (k : idealRange K) : Continuous (rowPhase k) :=
    continuous_const.mul (FourierBridge.logPhase_continuous_left _)
  have hβtc (n v : Ideal ActualEisensteinCubic.O) : Continuous (fun t => βt t n v) :=
    (continuous_const.mul (continuous_const.mul (FourierBridge.logPhase_continuous_left _))).mul
      (continuous_const.mul (FourierBridge.logPhase_continuous_left _))
  have hi := hq K U B lengthScale hK hU hB hL S T hS hT βt hβtc hβt rowPhase hrowPhasec hrowPhase g
  have he (k : idealRange K) :
      (∑n∈S,∑v∈T,quadraticRow k.val (primaryGenerator (n*v))*β n v*
        (V₀ (yr k)*V₁ (yn n)*V₂ (yb v)*CubicReflectionKernel.paperKernel (Vstar (P θ))
          (R*Real.exp (-2*yr k+yn n+3*yb v)))) =
      ∫t : ℝ,g t*(rowPhase k t*∑n∈S,∑v∈T,quadraticRow k.val (primaryGenerator (n*v))*βt t n v) := by
    have hint (n v : Ideal ActualEisensteinCubic.O) : Integrable (fun t : ℝ =>
        g t*(rowPhase k t*(quadraticRow k.val (primaryGenerator (n*v))*βt t n v))) := by
      apply g.integrable.mul_bdd (c := ‖quadraticRow k.val (primaryGenerator (n*v))*β n v‖)
      · exact ((hrowPhasec k).mul (continuous_const.mul (hβtc n v))).aestronglyMeasurable
      · filter_upwards [] with t
        simp only [rowPhase,βt,norm_mul,hphase,mul_one]
        have hv01 : ‖V₀ (yr k)‖*‖V₁ (yn n)‖≤1 := by
          simpa only [one_mul] using mul_le_mul (hV₀n (yr k)) (hV₁n (yn n)) (norm_nonneg _) zero_le_one
        have hv012 : (‖V₀ (yr k)‖*‖V₁ (yn n)‖)*‖V₂ (yb v)‖≤1 := by
          simpa only [one_mul] using mul_le_mul hv01 (hV₂n (yb v)) (norm_nonneg _) zero_le_one
        calc
          _ = (‖quadraticRow k.val (primaryGenerator (n*v))‖*‖β n v‖)*
            ((‖V₀ (yr k)‖*‖V₁ (yn n)‖)*‖V₂ (yb v)‖) := by ring
          _ ≤ (‖quadraticRow k.val (primaryGenerator (n*v))‖*‖β n v‖)*1 :=
            mul_le_mul_of_nonneg_left hv012 (by positivity)
          _ = _ := by ring
    simp only [Finset.mul_sum]
    rw [integral_finsetSum _ (fun n hn => integrable_finsetSum _ (fun v hv => hint n v))]
    apply Finset.sum_congr rfl
    intro n hn
    rw [integral_finsetSum _ (fun v hv => hint n v)]
    apply Finset.sum_congr rfl
    intro v hv
    rw [hsep (yr k) (yn n) (yb v),←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp [rowPhase,βt]
    ring
  simp_rw [he]
  apply hi.trans
  have hpow : 0<(1+R)^A := by positivity
  have hmass : (∫t : ℝ,‖g t‖)≤Ck/(1+R)^A := (le_div_iff₀ hpow).mpr (by simpa only [mul_comm] using hg)
  have hmass2 := pow_le_pow_left₀ (integral_nonneg (fun t => norm_nonneg _)) hmass 2
  have hbase : 0≤Cq*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2 := by positivity
  calc
    _ ≤ (Cq*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2)*(Ck/(1+R)^A)^2 :=
      mul_le_mul_of_nonneg_left hmass2 hbase
    _ ≤ (Cq*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2)*((Ck^2+1)/(1+R)^(2*A)) := by
      apply mul_le_mul_of_nonneg_left _ hbase
      rw [div_pow,←pow_mul]
      have hp : A*2=2*A := Nat.mul_comm _ _
      rw [hp]
      exact div_le_div_of_nonneg_right (by nlinarith : Ck^2≤Ck^2+1) (by positivity)
    _ = (Cq*(Ck^2+1))*((K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2)/(1+R)^(2*A) := by ring
    _ ≤ _ := by
      have hb := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCoeff (by positivity : 0≤(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2))
        (by positivity : 0≤(1+R)^(2*A))
      convert hb using 1 ; ring

end CompletedHeight

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedHeight
open CompletedGauss hiding O
open ActualEisensteinCubic CompletedDyadic
open CanonicalQuadraticSieve hiding O
theorem polynomial_smooth_series_rowPhase
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (hV₀n : ∀y,‖V₀ y‖≤1) (hV₁n : ∀y,‖V₁ y‖≤1) (hV₂n : ∀y,‖V₂ y‖≤1)
    (P : ℝ→ℝ→ℂ) (hP : HasPolynomialKernel P)
    (deltaLoss ρ q : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀θ K Y H : ℝ,1≤K → 0<Y → 0<H →
    ∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal ActualEisensteinCubic.O),
      (∀i,∀I∈S i,I≠0 ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀I∈T i,I≠0 ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.1) →
    ∀β : (ℕ×ℕ×ℕ)→Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖β i n v‖≤
        1/(Real.sqrt ((2:ℝ)^i.2.2)*(2:ℝ)^i.2.1*ramifiedScale ρ q i.1*Real.sqrt H)) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange K→ℂ,(∀i k,‖σ i k‖≤1) →
      (∀k,Summable (fun i => ‖σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ (P θ) K Y ρ q S T β i k‖)) ∧
      (∑k : idealRange K,‖∑'i : ℕ×ℕ×ℕ,
        σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ (P θ) K Y ρ q S T β i k‖^2)
        ≤(C*(1+‖θ‖)^heightDegree)*(K*Y)^(2*deltaLoss)*(K+Y)/H := by
  obtain ⟨A,hA⟩ := exists_nat_gt (deltaLoss+1/2)
  obtain ⟨heightDegree,Cbase,hCbase,hquadbase⟩ := polynomial_smooth_quadratic V₀ V₁ V₂ M₀ M₁ M₂
    hM₀ hM₁ hM₂ hV₀ hV₁ hV₂ hV₀n hV₁n hV₂n P hP A (2*deltaLoss) (by positivity)
  obtain ⟨Cs,hCs,hsum⟩ := normMajorant_sum_bound deltaLoss A ρ q hδ hA hρ hq
  refine ⟨heightDegree,2*Cbase*Cs^2,by positivity,?_⟩
  intro θ K Y H hK hY hH S T hS hT β hβ σ hσ
  let Cq := Cbase*(1+‖θ‖)^heightDegree
  have hCq : 0<Cq := by dsimp [Cq]; positivity
  have hquad := hquadbase θ
  have hKp : 0<K := by linarith
  have hqp : 0<q := by linarith
  let g : (ℕ×ℕ×ℕ)→ℝ := fun i => Real.sqrt Cq *
    normMajorant deltaLoss A K Y⁻¹ (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)
  have hg0 (i : ℕ×ℕ×ℕ) : 0≤g i := by
    dsimp [g]
    exact mul_nonneg (Real.sqrt_nonneg _) (normMajorant_nonneg _ _ _ _ _ _ _ _
      hKp (by positivity) (ramifiedScale_pos ρ q hρ hqp _) hH (by positivity) (by positivity))
  have henergy (i : ℕ×ℕ×ℕ) :
      (∑k : idealRange K,‖σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ (P θ) K Y ρ q S T β i k‖^2)
        ≤(g i)^2 := by
    let U : ℝ := (2:ℝ)^i.2.2
    let B : ℝ := (2:ℝ)^i.2.1
    let r : ℝ := ramifiedScale ρ q i.1
    let R : ℝ := Y⁻¹*r^3*B^3*U
    have hU : 1≤U := one_le_pow₀ (by norm_num)
    have hB : 1≤B := one_le_pow₀ (by norm_num)
    have hUp : 0<U := by positivity
    have hBp : 0<B := by positivity
    have hr : 0<r := ramifiedScale_pos ρ q hρ hqp _
    have hR : 0<R := by dsimp [R]; positivity
    have h := hquad K U B (1/(Real.sqrt U*B*r*Real.sqrt H)) R
      hK hU hB (by positivity) hR (S i) (T i) (hS i) (hT i) (β i) (hβ i)
      (fun k => Real.log ((Ideal.absNorm k.val:ℝ)/K))
      (fun n => Real.log ((Ideal.absNorm n:ℝ)/U))
      (fun v => Real.log ((Ideal.absNorm v:ℝ)/B))
    change (∑k,‖completedSmoothDyadicBlock V₀ V₁ V₂ (P θ) K Y ρ q S T β i k‖^2)≤_ at h
    have hphase : (∑k : idealRange K,‖σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ (P θ) K Y ρ q S T β i k‖^2)≤
        ∑k : idealRange K,‖completedSmoothDyadicBlock V₀ V₁ V₂ (P θ) K Y ρ q S T β i k‖^2 := by
      apply Finset.sum_le_sum
      intro k _
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hσ i k)
    apply (hphase.trans h).trans
    have he : Cq*(K*(U*B))^(2*deltaLoss)*(K+U*B)*(U*B)*
        (1/(Real.sqrt U*B*r*Real.sqrt H))^2/(1+R)^(2*A)=
        Cq*((K*(U*B))^(2*deltaLoss)*(K+U*B)/(B*r^2*H)/(1+R)^(2*(A:ℝ))) := by
      rw [show 2*(A:ℝ)=((2*A:ℕ):ℝ) by norm_num,Real.rpow_natCast]
      simp only [one_div,inv_pow,mul_pow,Real.sq_sqrt hUp.le,Real.sq_sqrt hH.le]
      field_simp

    rw [he]
    have hm := smooth_energy_le_normMajorant_sq deltaLoss A K Y⁻¹ r H U B
      hKp (by positivity) hr hH hUp hBp
    calc
      _ ≤ Cq*(normMajorant deltaLoss A K Y⁻¹ r H U B)^2 := mul_le_mul_of_nonneg_left hm hCq.le
      _ = (g i)^2 := by dsimp [g,U,B,r]; rw [mul_pow,Real.sq_sqrt hCq.le]
  obtain ⟨hs,hb⟩ := hsum K Y H hKp hY hH
  have hm := finite_tsum_energy_bound
    (fun i k => σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ (P θ) K Y ρ q S T β i k) g hg0
    (hs.mul_left (Real.sqrt Cq)) henergy
  refine ⟨hm.1,hm.2.trans ?_⟩
  have hb' : (∑'i,g i)≤Real.sqrt Cq*(Cs*(K*Y)^deltaLoss*(Real.sqrt K+Real.sqrt Y)/Real.sqrt H) := by
    rw [show g=(fun i => Real.sqrt Cq*normMajorant deltaLoss A K Y⁻¹
      (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)) from rfl,tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
  have hsq := pow_le_pow_left₀ (tsum_nonneg hg0) hb' 2
  apply hsq.trans
  have hroot : (Real.sqrt K+Real.sqrt Y)^2≤2*(K+Y) := by
    nlinarith [Real.sq_sqrt hKp.le,Real.sq_sqrt hY.le,
      sq_nonneg (Real.sqrt K-Real.sqrt Y)]
  simp only [mul_pow,div_pow,Real.sq_sqrt hCq.le,Real.sq_sqrt hH.le]
  have hp : ((K*Y)^deltaLoss)^2=(K*Y)^(2*deltaLoss) := by
    rw [←Real.rpow_mul_natCast (mul_pos hKp hY).le]
    congr 1
    ring
  rw [hp]
  calc
    _ ≤ Cq*(Cs^2*(K*Y)^(2*deltaLoss)*(2*(K+Y))/H) := by
      apply mul_le_mul_of_nonneg_left _ hCq.le
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (by positivity)) hH.le
    _ = _ := by dsimp [Cq]; ring

end CompletedHeight

end

end OAI
end OAIOriginalModule0235
