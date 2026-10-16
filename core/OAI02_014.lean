    (hpr : ∀i,lambda^2∣p i-1) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (hQ : ∀v∈Q,v.support⊆pool) (labels : Finset (Ideal ActualEisensteinCubic.O))
    (β : Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (g W : 𝓢(ℝ,ℂ))
    (K X t : ℝ) (hK : 0<K) (hX : 0<X) :
    canonicalSourceTotal p hp hcop hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
      Ψ Ψ m m (frequencyTwist g t) (frequencyTwist g t) W K X=
    canonicalSourceTotal p hp hcop hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
      (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g W K X := by
  rw [←reopenedCanonicalRow_smoothed_eq_source p hp hcop hg hinj hpr pool Q hQ labels β Ψ m
    (frequencyTwist g t) W K X hK,
    ←reopenedCanonicalRow_smoothed_eq_source p hp hcop hg hinj hpr pool Q hQ labels β
      (normHeightTwist Ψ t) m g W K X hK]
  apply Finset.sum_congr rfl
  intro I hI
  apply tsum_congr
  intro z
  rw [reopenedCanonicalRow_frequencyTwist_norm p hp hcop hg pool Q (β I) Ψ m _ z g X t hX]

end

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open JointLogSeparation (frequencyTwist)

theorem reopenedCanonicalRow_twoPassage_uniform_height
    (W g V : 𝓢(ℝ,ℂ)) (M Nv : ℝ) (hM : 0≤M) (hNv : 0≤Nv)
    (hgM : ∀t,g t≠0→|t|≤M) (hV : ∀t,V t≠0→|t|≤Nv)
    (hWin : ∀t,g t≠0→V t=1)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t|≤M+6+1) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t|≤M+6+1) ∧
      ∀{ι:Type*} [DecidableEq ι]
      (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι) (Q:Finset (ι→₀ℕ)) (labels:Finset (Ideal ActualEisensteinCubic.O))
      (β:Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ) (Ψ:ActualEisensteinCubic.O→*ℂ) (m:ActualEisensteinCubic.O) (Γ t Ksrc K ell B F H U:ℝ),
      0≤Γ → 0<Ksrc → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U →
      ell*Real.exp M≤U → (∀u,‖Ψ u‖≤1) →
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) → (∀v∈Q,v.support⊆pool) →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤B) →
      (∀I∈labels,Squarefree I) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      let Ψt:=normHeightTwist Ψ t
      let bs:=reopenedCubeFamily Q
      let a:=reopenedPairCoefficient β
      ‖(ell*B^2*F:ℂ)⁻¹*
        ((∑I∈labels,∑'z:ActualEisensteinCubic.O,W (‖eisEmbedding z‖^2/Ksrc)*
           (‖reopenedCanonicalRow p hp hcop hg pool Q (β I) Ψ m
             (ConcretePrimeRowBridge.idealGenerator I)
             (fun S=>frequencyTwist g t (columnLog p ell S)) z‖^2:ℝ))-
         canonicalSourceZero p hp hcop hg pool bs labels a Ψt Ψt m m g g W Ksrc ell-
         canonicalSourceTail p hp hcop hg pool bs labels a Ψt Ψt m m g g W Ksrc K ell)‖≤
      (Ksrc/K)*Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool (canonicalSourceBlocks pool bs)
          Ψt m windows₁ C₁ Cd₁ Ct₁ (Γ^2) ε K ell B F M H U A J N true)*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool (canonicalSourceBlocks pool bs)
          Ψt m windows₂ C₂ Cd₂ Ct₂ (Γ^2) ε K ell B F M H U A J N false) := by
  obtain ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hw₁,hs₁,hb₁,hw₂,hs₂,hb₂,htransfer⟩:=
    canonicalSource_twoPassage_quantitative W g g V V M M Nv Nv hM hM hNv hNv
      hgM hgM hV hV hWin hWin ε deltaLoss hε hδ A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hw₁,hs₁,hb₁,hw₂,hs₂,hb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool Q labels β Ψ m Γ t Ksrc K ell B F H U
    hΓ hKsrc hK hell hB hF hH hU hMU hΨ hβ hQ hQB hsf hf
  dsimp only
  rw [reopenedCanonicalRow_smoothed_eq_source p hp hcop hg hinj hpr pool Q hQ labels β Ψ m
    (frequencyTwist g t) W Ksrc ell hKsrc,
    reopenedSource_frequencyTwist p hp hcop hg hinj hpr pool Q hQ labels β Ψ m g W Ksrc ell t hKsrc hell]
  have hΨt : ∀u,‖normHeightTwist Ψ t u‖≤1 :=
    fun u=>(normHeightTwist_norm_le Ψ t u).trans (hΨ u)
  exact htransfer p hp hinj hcop hg hc hpr pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
    (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m (Γ^2) Ksrc K ell B F H U
    (sq_nonneg Γ) hKsrc hK hell hB hF hH hU hMU hMU hΨt hΨt
    (fun b hb C hC I hI=>reopenedPairCoefficient_bound Q labels β Γ hΓ hβ b hb C I hI)
    (reopenedCubeFamily_admissible Q)
    (fun b hb=>(reopenedCubeFamily_cube_norms p Q B hQB b hb).1)
    (fun b hb=>(reopenedCubeFamily_cube_norms p Q B hQB b hb).2) hsf hf

end SecondPassArithmetic

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff

namespace CanonicalCubeSeparation
open FourierBridge JointLogSeparation FirstPassCubeLabels

def columnWindowRadius (a b : ℝ) : ℝ := |Real.log a| + |Real.log b| + 3

lemma columnWindowRadius_nonneg (a b : ℝ) : 0 ≤ columnWindowRadius a b := by
  unfold columnWindowRadius
  positivity

def sourceLogProfile (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(ℝ,ℂ) := by
  have hc : HasCompactSupport (fun u : ℝ => W (Real.exp u)) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (Real.log a) (Real.log b)) isCompact_Icc
    intro u hu
    have hm := hs hu
    constructor
    · simpa only [Real.log_exp] using Real.log_le_log ha hm.1
    · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos u) hm.2
  exact hc.toSchwartzMap (hW.comp Real.contDiff_exp)

@[simp] lemma sourceLogProfile_apply (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (u : ℝ) :
    sourceLogProfile W a b ha hs hW u = W (Real.exp u) := rfl

def reopeningCoefficient (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(ℝ,ℂ) :=
  𝓕 (sourceLogProfile W a b ha hs hW)

def cubeFrequencyFactor (t ξ : ℝ) : ℂ :=
  (Real.exp (t/2) : ℂ) * logPhase ξ (3*t)

@[simp] lemma cubeFrequencyFactor_norm (t ξ : ℝ) :
    ‖cubeFrequencyFactor t ξ‖ = Real.exp (t/2) := by
  simp only [cubeFrequencyFactor, norm_mul, logPhase_norm, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma cubeFrequencyFactor_bound (t ξ : ℝ) (ht : t ≤ 1) :
    ‖cubeFrequencyFactor t ξ‖ ≤ Real.exp (1/2) := by
  rw [cubeFrequencyFactor_norm]
  exact Real.exp_le_exp.mpr (by linarith)

lemma active_column_window (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (t u : ℝ)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hWu : W (Real.exp (u+3*t)) ≠ 0) :
    |u| ≤ columnWindowRadius a b := by
  have hab := hs hWu
  have hlo : Real.log a ≤ u+3*t := by
    simpa only [Real.log_exp] using Real.log_le_log ha hab.1
  have hhi : u+3*t ≤ Real.log b := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hab.2
  unfold columnWindowRadius
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (Real.log a), le_abs_self (Real.log b),
    abs_nonneg (Real.log a), abs_nonneg (Real.log b), ht.1, ht.2]

lemma reopening_integrable (b V : 𝓢(ℝ,ℂ)) (t u : ℝ) :
    Integrable (fun ξ : ℝ => b ξ * cubeFrequencyFactor t ξ * frequencyTwist V ξ u) := by
  have hi : Integrable (fun ξ : ℝ =>
      b ξ * ((Real.exp (t/2) : ℂ) * logPhase ξ (3*t) * (logPhase ξ u * V u))) := by
    apply b.integrable.mul_bdd (c := Real.exp (t/2) * ‖V u‖)
    · exact (((logPhase_continuous_left (3*t)).const_mul _).mul
        ((logPhase_continuous_left u).mul_const _)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ξ => by
        simp only [norm_mul, logPhase_norm, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _), one_mul, mul_one, le_refl])
  convert hi using 1
  funext ξ
  rw [frequencyTwist_apply]
  unfold cubeFrequencyFactor
  ring

theorem reopening_separation_with_window (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (t u : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (Real.exp (t/2) : ℂ) * W (Real.exp (u+3*t)) =
      ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
        cubeFrequencyFactor t ξ * frequencyTwist V ξ u := by
  have hwindow : V u * W (Real.exp (u+3*t)) = W (Real.exp (u+3*t)) := by
    by_cases hz : W (Real.exp (u+3*t)) = 0
    · simp [hz]
    · rw [hV u (active_column_window W a b ha hs t u ht hz), one_mul]
  have hinv := schwartz_phase_inversion
    (sourceLogProfile W a b ha hs hW) (u+3*t)
  change W (Real.exp (u+3*t)) =
    ∫ ξ : ℝ, logPhase ξ (u+3*t) * reopeningCoefficient W a b ha hs hW ξ at hinv
  calc
    _ = ((Real.exp (t/2) : ℂ) * V u) * W (Real.exp (u+3*t)) := by
      rw [mul_assoc, hwindow]
    _ = ∫ ξ : ℝ, ((Real.exp (t/2) : ℂ) * V u) *
        (logPhase ξ (u+3*t) * reopeningCoefficient W a b ha hs hW ξ) := by
      rw [hinv, integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [logPhase_add, frequencyTwist_apply]
      unfold cubeFrequencyFactor
      ring

theorem exists_reopening_separation (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃ V : 𝓢(ℝ,ℂ), HasCompactSupport V ∧
      (∀ u, |u| ≤ columnWindowRadius a b → V u = 1) ∧
      (∀ u, V u ≠ 0 → |u| ≤ columnWindowRadius a b + 1) ∧
      (∀ t u : ℝ, t ∈ Set.Icc (0:ℝ) 1 →
        (Real.exp (t/2) : ℂ) * W (Real.exp (u+3*t)) =
          ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
            cubeFrequencyFactor t ξ * frequencyTwist V ξ u) ∧
      (∀ t u : ℝ, Integrable (fun ξ : ℝ => reopeningCoefficient W a b ha hs hW ξ *
          cubeFrequencyFactor t ξ * frequencyTwist V ξ u)) ∧
      (∀ J : ℕ, ∃ C : ℝ, 0 < C ∧
        Integrable (fun ξ : ℝ => (1+‖ξ‖)^J * ‖reopeningCoefficient W a b ha hs hW ξ‖) ∧
        (∫ ξ : ℝ, (1+‖ξ‖)^J * ‖reopeningCoefficient W a b ha hs hW ξ‖) ≤ C ∧
        ∀ ξ : ℝ, ‖reopeningCoefficient W a b ha hs hW ξ‖ ≤ C * firstLogDensity J ξ) := by
  obtain ⟨v,hvc,hvs,hvone,hvsupp,_⟩ := exists_complex_smooth_cutoff
    (columnWindowRadius a b) (columnWindowRadius_nonneg a b)
  let V : 𝓢(ℝ,ℂ) := hvc.toSchwartzMap hvs
  have hVone : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1 := hvone
  refine ⟨V,hvc,hVone,?_,?_,reopening_integrable _ V,?_⟩
  · intro u hu
    have hmem := hvsupp (subset_tsupport v hu)
    exact abs_le.mpr hmem
  · exact fun t u ht => reopening_separation_with_window W a b ha hs hW V hVone t u ht
  · intro J
    let g := sourceLogProfile W a b ha hs hW
    let c := fourierPointBound (J+2) (profileSourceBound g (J+2))
    let m := ∫ ξ : ℝ, (1+‖ξ‖)^J * ‖reopeningCoefficient W a b ha hs hW ξ‖
    have hc : 0 ≤ c := fourierPointBound_nonneg _ _ (profileSourceBound_nonneg _ _)
    have hm : 0 ≤ m := integral_nonneg (fun ξ => by positivity)
    refine ⟨1+c+m,by positivity,weighted_schwartz_integrable _ J,by dsimp [m]; linarith,?_⟩
    intro ξ
    exact (profile_fourier_envelope g J ξ).trans
      (mul_le_mul_of_nonneg_right (by linarith : c ≤ 1+c+m) (firstLogDensity_nonneg J ξ))

end CanonicalCubeSeparation

end

end OAI
end OAIOriginalModule0223

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.CompactEnergyFamilies
Source SHA256: 895150367a2a113d4e16b072eddc9ef1ce7f3cf861fb891641101fdd9c6c6893
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0224



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

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

section

lemma compact_of_norm_le_compact {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (f : E→L[ℂ]F) (g : E→L[ℂ]G) (hg : IsCompactOperator g)
    (hbound : ∃C : ℝ,∀x,‖f x‖≤C*‖g x‖) : IsCompactOperator f := by
  let S := (LinearMap.range g.toLinearMap).topologicalClosure
  have hS : IsClosed (S : Set G) := (LinearMap.range g.toLinearMap).isClosed_topologicalClosure
  have hmem : ∀x,g x∈S := fun x => (LinearMap.range g.toLinearMap).le_topologicalClosure ⟨x,rfl⟩
  let e : E→L[ℂ]S := g.codRestrict S hmem
  have he : DenseRange e := by
    rw [DenseRange,Subtype.dense_iff,←Set.range_comp]
    change closure (Set.range g)⊆closure (Set.range g)
    exact Set.Subset.rfl
  have hec : IsCompactOperator e := hg.codRestrict hmem hS
  let q : S→L[ℂ]F := f.toLinearMap.extendOfNorm e.toLinearMap
  have hfq : f=q.comp e := by
    ext x
    exact (LinearMap.extendOfNorm_eq he hbound x).symm
  rw [hfq]
  exact hec.clm_comp q

lemma compact_finite_pi {E G ι : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (T : ι→E→L[ℂ]G) (hT : ∀i,IsCompactOperator (T i)) :
    IsCompactOperator (ContinuousLinearMap.pi T) := by
  let K : ι→Set G := fun i => closure ((T i) '' Metric.ball (0 : E) 1)
  have hK : ∀i,IsCompact (K i) := fun i => (hT i).isCompact_closure_image_ball 1
  refine ⟨Set.pi Set.univ K,isCompact_univ_pi hK,?_⟩
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ)<1))
  intro x hx
  exact fun i hi => subset_closure ⟨x,hx,rfl⟩

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap

def kernelChartCore (χ : PositiveChartCutoff) : Set EuclideanSpatial :=
  {p | (1/2 : ℝ)<χ.func p}

def kernelChartCoreImage (χ : PositiveChartCutoff) : Set KernelQuotient :=
  kernelEuclideanProjection '' kernelChartCore χ

lemma kernelChartCore_open (χ : PositiveChartCutoff) : IsOpen (kernelChartCore χ) :=
  isOpen_lt continuous_const χ.smooth.continuous

lemma kernelChartCore_subset (χ : PositiveChartCutoff) : kernelChartCore χ⊆tsupport χ.func := by
  intro p hp
  apply subset_tsupport
  change χ.func p≠0
  have hh : (1/2 : ℝ)<χ.func p := hp
  linarith

lemma kernelChartCoreImage_open (χ : PositiveChartCutoff) : IsOpen (kernelChartCoreImage χ) := by
  have hp : kernelChartCore χ⊆euclideanUpperHalf := (kernelChartCore_subset χ).trans χ.positive
  have he : kernelChartCoreImage χ=integralOrbitProjection globalKubotaKernel ''
      (hyperbolicEuclideanCoordinates ⁻¹' kernelChartCore χ) := by
    rw [←euclideanToHyperbolic_image_positive _ hp,Set.image_image]
    rfl
  rw [he]
  exact (integralOrbitProjection_openQuotient globalKubotaKernel
    globalKubotaKernel_le_levelThree).isOpenMap _
      ((kernelChartCore_open χ).preimage hyperbolicEuclideanCoordinates_continuous)

abbrev KernelGoodCutoff := {χ : PositiveChartCutoff //
  Set.InjOn kernelEuclideanProjection (tsupport χ.func)}

lemma kernelChartCoreImage_cover : (Set.univ : Set KernelQuotient)⊆
    ⋃χ : KernelGoodCutoff,kernelChartCoreImage χ.1 := by
  intro q hq
  obtain ⟨w,rfl⟩ := Quotient.mk_surjective q
  obtain ⟨χ,hχ,hrange,hinj⟩ := kernelChartCutoff_exists
    (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)
  refine Set.mem_iUnion.mpr ⟨⟨χ,hinj⟩,hyperbolicEuclideanCoordinates w,?_,?_⟩
  · change (1/2 : ℝ)<χ.func (hyperbolicEuclideanCoordinates w)
    rw [hχ]
    norm_num
  · simp only [kernelEuclideanProjection,Function.comp_apply,euclideanToHyperbolic_coordinates]
    rfl

lemma kernelCompact_finite_chart_cover (K : Set KernelQuotient) (hK : IsCompact K) :
    ∃t : Finset KernelGoodCutoff,K⊆⋃χ∈t,kernelChartCoreImage χ.1 := by
  exact hK.elim_finite_subcover (fun χ : KernelGoodCutoff => kernelChartCoreImage χ.1)
    (fun χ => kernelChartCoreImage_open χ.1)
    (Set.subset_univ K |>.trans kernelChartCoreImage_cover)

lemma kernelChartCore_mass_estimate (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (H : ℝ) (hH : 0≤H) (hdensity : ∀p∈tsupport χ.func,((p 2)^3)⁻¹≤H)
    (f : kernelSmoothTests) :
    (∫q in kernelChartCoreImage χ,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel)≤
      4*H*‖kernelL2Localize χ (kernelSmoothTestsToL2 f)‖^2 := by
  let S := kernelChartCore χ
  have hS : MeasurableSet S := (kernelChartCore_open χ).measurableSet
  have hpos : S⊆euclideanUpperHalf := (kernelChartCore_subset χ).trans χ.positive
  have hi : Set.InjOn kernelEuclideanProjection S := hinj.mono (kernelChartCore_subset χ)
  have hm := hyperbolicVolume_le_densityBound S hS hpos H
    (fun p hp => hdensity p (kernelChartCore_subset χ hp))
  have hloc : Integrable (fun p => ‖kernelLocalizedField χ f p‖^2) volume := by
    exact ((kernelLocalizedSchwartz χ f).memLp 2 volume).norm.integrable_sq
  have hlocHyp : IntegrableOn (fun p => ‖kernelLocalizedField χ f p‖^2) S hyperbolicEuclideanVolume :=
    (hloc.integrableOn.smul_measure (c := ENNReal.ofReal H) ENNReal.ofReal_ne_top).mono_measure hm
  have hmass : IntegrableOn (fun p => ‖kernelTestField f p‖^2) S hyperbolicEuclideanVolume :=
    (kernelEuclideanProjection_measurePreserving_on S hS hpos hi).integrable_comp_of_integrable
      (kernelSmoothTests_memLp f).norm.integrable_sq.integrableOn
  rw [kernelL2Localize_core χ hinj,schwartz_toL2_norm_sq]
  have hEq := kernelEuclideanProjection_integral S hS hpos hi
    (fun q => ‖f.1 q‖^2) (kernelSmoothTests_memLp f).norm.integrable_sq.aestronglyMeasurable
  change (∫p in S,‖kernelTestField f p‖^2∂hyperbolicEuclideanVolume)=_ at hEq
  change (∫q in kernelEuclideanProjection '' S,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel)≤
    4*H*(∫p,‖kernelLocalizedField χ f p‖^2)
  rw [←hEq]
  calc
    _ ≤ ∫p in S,4*‖kernelLocalizedField χ f p‖^2∂hyperbolicEuclideanVolume := by
      apply setIntegral_mono_on hmass (hlocHyp.const_mul 4) hS
      intro p hp
      have hc : (1/2 : ℝ)<χ.func p := hp
      rw [kernelLocalizedField,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
      have hn := sq_nonneg ‖kernelTestField f p‖
      have hx : 1≤4*(χ.func p)^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hx hn]
    _ = 4*(∫p in S,‖kernelLocalizedField χ f p‖^2∂hyperbolicEuclideanVolume) := integral_const_mul _ _
    _ ≤ 4*(H*(∫p in S,‖kernelLocalizedField χ f p‖^2)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      have hh := integral_mono_measure hm
        (Eventually.of_forall (fun p => sq_nonneg ‖kernelLocalizedField χ f p‖))
        (hloc.integrableOn.smul_measure (c := ENNReal.ofReal H) ENNReal.ofReal_ne_top)
      simpa only [integral_smul_measure,ENNReal.toReal_ofReal hH,smul_eq_mul] using hh
    _ ≤ _ := by
      rw [←mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact setIntegral_le_integral hloc (Eventually.of_forall (fun p => sq_nonneg ‖kernelLocalizedField χ f p‖))

lemma kernelChartCore_mass_bound (χ : KernelGoodCutoff) : ∃C : ℝ,0≤C ∧
    ∀f : kernelSmoothTests,
      (∫q in kernelChartCoreImage χ.1,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel)≤
        C*‖kernelL2Localize χ.1 (kernelSmoothTestsToL2 f)‖^2 := by
  have hrho : ContinuousOn (fun p : EuclideanSpatial => ((p 2)^3)⁻¹) (tsupport χ.1.func) :=
    (by fun_prop : Continuous (fun p : EuclideanSpatial => (p 2)^3)).continuousOn.inv₀
      (fun p hp => pow_ne_zero _ (ne_of_gt (χ.1.positive hp)))
  obtain ⟨r,hr⟩ := χ.1.compact.bddAbove_image hrho
  refine ⟨4*max 0 r,by positivity,fun f => ?_⟩
  exact kernelChartCore_mass_estimate χ.1 χ.2 (max 0 r) (le_max_left _ _)
    (fun p hp => (hr ⟨p,hp,rfl⟩).trans (le_max_right _ _)) f

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

def kernelMassRestriction (K : Set KernelQuotient) (hK : MeasurableSet K)
    (f : KernelQuotientL2) : KernelQuotientL2 :=
  ((Lp.memLp f).indicator hK).toLp (K.indicator f)

lemma kernelMassRestriction_coe (K : Set KernelQuotient) (hK : MeasurableSet K)
    (f : KernelQuotientL2) :
    (kernelMassRestriction K hK f : KernelQuotient→ℂ)=ᵐ[integralQuotientVolume globalKubotaKernel]
      K.indicator f := ((Lp.memLp f).indicator hK).coeFn_toLp

def kernelMassRestrictionLinear (K : Set KernelQuotient) (hK : MeasurableSet K) :
    KernelQuotientL2→ₗ[ℂ]KernelQuotientL2 where
  toFun := kernelMassRestriction K hK
  map_add' f g := by
    apply Lp.ext
    filter_upwards [kernelMassRestriction_coe K hK (f+g),kernelMassRestriction_coe K hK f,
      kernelMassRestriction_coe K hK g,Lp.coeFn_add f g,
      Lp.coeFn_add (kernelMassRestriction K hK f) (kernelMassRestriction K hK g)] with q hfg hf hg ha hb
    rw [hfg,hb,Pi.add_apply,hf,hg]
    by_cases hq : q∈K
    · simp only [Set.indicator_of_mem hq,ha,Pi.add_apply]
    · simp only [Set.indicator_of_notMem hq,add_zero]
  map_smul' c f := by
    change kernelMassRestriction K hK (c•f)=c•kernelMassRestriction K hK f
    apply Lp.ext
    filter_upwards [kernelMassRestriction_coe K hK (c•f),kernelMassRestriction_coe K hK f,
      Lp.coeFn_smul c f,Lp.coeFn_smul c (kernelMassRestriction K hK f)] with q hcf hf ha hb
    rw [hcf,hb,Pi.smul_apply,hf]
    by_cases hq : q∈K
    · simp only [Set.indicator_of_mem hq,ha,Pi.smul_apply]
    · simp only [Set.indicator_of_notMem hq,smul_zero]

lemma kernelMassRestriction_norm_le (K : Set KernelQuotient) (hK : MeasurableSet K)
    (f : KernelQuotientL2) : ‖kernelMassRestriction K hK f‖≤‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [kernelMassRestriction_coe K hK f] with q hq
  rw [hq]
  by_cases hm : q∈K
  · simp only [Set.indicator_of_mem hm,le_refl]
  · simp only [Set.indicator_of_notMem hm,norm_zero,norm_nonneg]

def kernelMassRestrictionCLM (K : Set KernelQuotient) (hK : MeasurableSet K) :
    KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  (kernelMassRestrictionLinear K hK).mkContinuous 1 (by
    intro f
    change ‖kernelMassRestriction K hK f‖≤1*‖f‖
    simpa only [one_mul] using kernelMassRestriction_norm_le K hK f)

lemma kernelMassRestriction_norm_sq (K : Set KernelQuotient) (hK : MeasurableSet K)
    (f : KernelQuotientL2) :
    ‖kernelMassRestrictionCLM K hK f‖^2=
      ∫q in K,‖f q‖^2∂integralQuotientVolume globalKubotaKernel := by
  rw [←integral_indicator hK]
  calc
    _ = inner ℝ (kernelMassRestriction K hK f) (kernelMassRestriction K hK f) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫q,inner ℝ (kernelMassRestriction K hK f q) (kernelMassRestriction K hK f q)
        ∂integralQuotientVolume globalKubotaKernel := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [kernelMassRestriction_coe K hK f] with q hq
      rw [hq,real_inner_self_eq_norm_sq]
      by_cases hqK : q∈K
      · simp only [Set.indicator_of_mem hqK]
      · simp only [Set.indicator_of_notMem hqK,norm_zero,zero_pow (by decide : 2≠0)]

lemma kernelMassRestriction_smooth_norm_sq (K : Set KernelQuotient) (hK : MeasurableSet K)
    (f : kernelSmoothTests) :
    ‖kernelMassRestrictionCLM K hK (kernelSmoothTestsToL2 f)‖^2=
      ∫q in K,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel := by
  rw [kernelMassRestriction_norm_sq]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (kernelSmoothTests_memLp f).coeFn_toLp] with q hq
  change ‖((kernelSmoothTests_memLp f).toLp f.1) q‖^2=‖f.1 q‖^2
  rw [hq]

def kernelEnergyMassRestriction (K : Set KernelQuotient) (hK : MeasurableSet K) :
    KernelEnergyGraph→L[ℂ]KernelQuotientL2 :=
  (kernelMassRestrictionCLM K hK).comp kernelEnergyMass

lemma integral_le_finite_cover {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (ν : Measure X) (K : Set X) (hK : MeasurableSet K) (U : ι→Set X)
    (hU : ∀i,MeasurableSet (U i)) (hcover : K⊆⋃i,U i)
    (g : X→ℝ) (hg : Integrable g ν) (hn : ∀x,0≤g x) :
    (∫x in K,g x∂ν)≤∑i,∫x in U i,g x∂ν := by
  have hi : ∀i,Integrable ((U i).indicator g) ν := fun i => hg.indicator (hU i)
  calc
    _ = ∫x,K.indicator g x∂ν := (integral_indicator hK).symm
    _ ≤ ∫x,∑i,(U i).indicator g x∂ν := by
      apply integral_mono (hg.indicator hK) (integrable_finsetSum _ (fun i himem => hi i))
      intro x
      have hnon : ∀i,0≤(U i).indicator g x := fun i => Set.indicator_nonneg (fun y hy => hn y) x
      by_cases hx : x∈K
      · rw [Set.indicator_of_mem hx]
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hcover hx)
        calc
          g x=(U i).indicator g x := (Set.indicator_of_mem hi g).symm
          _ ≤ ∑j,(U j).indicator g x := Finset.single_le_sum (fun j hj => hnon j) (Finset.mem_univ i)
      · rw [Set.indicator_of_notMem hx]
        exact Finset.sum_nonneg (fun i hi => hnon i)
    _ = _ := by
      rw [integral_finsetSum _ (fun i himem => hi i)]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_indicator (hU i)

def kernelEnergyChartFamily (t : Finset KernelGoodCutoff) :
    KernelEnergyGraph→L[ℂ](t→EuclideanL2) :=
  ContinuousLinearMap.pi (fun χ : t => kernelEnergyLocalizeL2 χ.1.1)

lemma kernelEnergyChartFamily_isCompact (t : Finset KernelGoodCutoff) :
    IsCompactOperator (kernelEnergyChartFamily t) :=
  compact_finite_pi _ (fun χ => kernelEnergyLocalizeL2_isCompact χ.1.1 χ.1.2)

lemma finite_sum_weighted_norm_sq_le {G ι : Type*} [Fintype ι]
    [NormedAddCommGroup G] (C : ι→ℝ) (hC : ∀i,0≤C i) (x : ι→G) :
    (∑i,C i*‖x i‖^2)≤(∑i,C i)*‖x‖^2 := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x i) 2) (hC i)

lemma kernelEnergyChartFamily_core_apply (t : Finset KernelGoodCutoff)
    (f : kernelSmoothTests) (χ : t) :
    kernelEnergyChartFamily t (kernelEnergyGraphCore f) χ=
      kernelL2Localize χ.1.1 (kernelSmoothTestsToL2 f) := by
  change kernelL2Localize χ.1.1 (kernelEnergyMass (kernelEnergyGraphCore f))=_
  rw [kernelEnergyMass_core]

lemma kernelCompact_mass_bound (K : Set KernelQuotient) (hK : IsCompact K) :
    ∃t : Finset KernelGoodCutoff,∃C : ℝ,0≤C ∧ ∀f : kernelSmoothTests,
      (∫q in K,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel)≤
        C*‖kernelEnergyChartFamily t (kernelEnergyGraphCore f)‖^2 := by
  obtain ⟨t,ht⟩ := kernelCompact_finite_chart_cover K hK
  have hcov : K⊆⋃χ : t,kernelChartCoreImage χ.1.1 := by
    intro q hq
    obtain ⟨χ,hχ,hqχ⟩ := Set.mem_iUnion₂.mp (ht hq)
    exact Set.mem_iUnion.mpr ⟨⟨χ,hχ⟩,hqχ⟩
  choose C hC hbound using fun χ : t => kernelChartCore_mass_bound χ.1
  refine ⟨t,∑χ,C χ,Finset.sum_nonneg (fun χ hχ => hC χ),fun f => ?_⟩
  calc
    _ ≤ ∑χ : t,∫q in kernelChartCoreImage χ.1.1,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel :=
      integral_le_finite_cover _ K hK.measurableSet _
        (fun χ : t => (kernelChartCoreImage_open χ.1.1).measurableSet) hcov _
        (kernelSmoothTests_memLp f).norm.integrable_sq (fun _ => sq_nonneg _)
    _ ≤ ∑χ : t,C χ*‖kernelL2Localize χ.1.1 (kernelSmoothTestsToL2 f)‖^2 :=
      Finset.sum_le_sum (fun χ hχ => hbound χ f)
    _ = ∑χ : t,C χ*‖kernelEnergyChartFamily t (kernelEnergyGraphCore f) χ‖^2 := by
      simp only [kernelEnergyChartFamily_core_apply]
    _ ≤ _ := finite_sum_weighted_norm_sq_le C hC _

theorem kernelEnergyMassRestriction_isCompact (K : Set KernelQuotient) (hK : IsCompact K) :
    IsCompactOperator (kernelEnergyMassRestriction K hK.measurableSet) := by
  obtain ⟨t,C,hC,hbound⟩ := kernelCompact_mass_bound K hK
  have hsq : ∀u : KernelEnergyGraph,
      ‖kernelEnergyMassRestriction K hK.measurableSet u‖^2≤
        C*‖kernelEnergyChartFamily t u‖^2 := by
    intro u
    exact kernelEnergyGraphCore_dense.induction_on u
      (isClosed_le (by fun_prop : Continuous (fun v => ‖kernelEnergyMassRestriction K hK.measurableSet v‖^2))
        (by fun_prop : Continuous (fun v => C*‖kernelEnergyChartFamily t v‖^2)))
      (fun f => by
        change ‖kernelMassRestrictionCLM K hK.measurableSet
          (kernelEnergyMass (kernelEnergyGraphCore f))‖^2≤_
        rw [kernelEnergyMass_core,kernelMassRestriction_smooth_norm_sq]
        exact hbound f)
  apply compact_of_norm_le_compact _ (kernelEnergyChartFamily t)
    (kernelEnergyChartFamily_isCompact t)
  refine ⟨Real.sqrt C,fun u => ?_⟩
  have hs := hsq u
  have hc := Real.sq_sqrt hC
  have hn := mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg (kernelEnergyChartFamily t u))
  have he : (Real.sqrt C*‖kernelEnergyChartFamily t u‖)^2=C*‖kernelEnergyChartFamily t u‖^2 := by
    rw [mul_pow,Real.sq_sqrt hC]
  nlinarith [norm_nonneg (kernelEnergyMassRestriction K hK.measurableSet u)]

lemma kernelVariationalResolvent_compact_restriction (K : Set KernelQuotient)
    (hK : IsCompact K) :
    IsCompactOperator ((kernelMassRestrictionCLM K hK.measurableSet).comp kernelVariationalResolvent) := by
  exact (kernelEnergyMassRestriction_isCompact K hK).comp_clm kernelVariationalSolution

end CubicEisenstein

open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss (actualSextic)

def primeValueHom (w : Ideal ActualEisensteinCubic.O → ℂ) : Ideal ActualEisensteinCubic.O →*₀ ℂ where
  toFun I := if I=0 then 0 else ((UniqueFactorizationMonoid.normalizedFactors I).map w).prod
  map_zero' := by simp
  map_one' := by
    rw [ite_eq_right one_ne_zero,UniqueFactorizationMonoid.normalizedFactors_one]
    rfl
  map_mul' I J := by
    by_cases hI : I=0
    · simp [hI]
    by_cases hJ : J=0
    · simp [hJ]
    simp only [ite_eq_right hI,ite_eq_right hJ,ite_eq_right (mul_ne_zero hI hJ),
      UniqueFactorizationMonoid.normalizedFactors_mul hI hJ,Multiset.map_add,Multiset.prod_add]

theorem primeValueHom_prime (w : Ideal ActualEisensteinCubic.O → ℂ) (P : Ideal ActualEisensteinCubic.O) (hP : Prime P) :
    primeValueHom w P = w P := by
  change (if P=0 then 0 else _) = w P
  rw [ite_eq_right hP.ne_zero,
    UniqueFactorizationMonoid.normalizedFactors_irreducible hP.irreducible]
  simp only [normalize_eq,Multiset.map_singleton,Multiset.prod_singleton]

theorem primeValueHom_norm_le_one (w : Ideal ActualEisensteinCubic.O → ℂ) (hw : ∀ P,‖w P‖≤1)
    (I : Ideal ActualEisensteinCubic.O) : ‖primeValueHom w I‖≤1 := by
  by_cases hI : I=0
  · rw [hI,map_zero,norm_zero]
    exact zero_le_one
  change ‖if I=0 then 0 else _‖≤1
  rw [ite_eq_right hI]
  have hprod (s : Multiset (Ideal ActualEisensteinCubic.O)) : ‖(s.map w).prod‖≤1 := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons P s ih =>
      simp only [Multiset.map_cons,Multiset.prod_cons,norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hw P)).trans ih
  exact hprod _

def principalIdealHom : ActualEisensteinCubic.O →*₀ Ideal ActualEisensteinCubic.O where
  toFun n := Ideal.span {n}
  map_zero' := by simp
  map_one' := by simp
  map_mul' a b := (Ideal.span_singleton_mul_span_singleton a b).symm

def localRowValue (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) : ℂ :=
  if h : P.IsMaximal ∧ lambda∉P then
    letI : P.IsMaximal := h.1
    actualSextic P h.2 (Ideal.Quotient.mk P x)
  else 0

theorem localRowValue_good (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : lambda∉P) :
    localRowValue x P = actualSextic P hg (Ideal.Quotient.mk P x) := by
  simp only [localRowValue,dite_eq_left (show P.IsMaximal ∧ lambda∉P from ⟨inferInstance,hg⟩)]

theorem localRowValue_norm (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) : ‖localRowValue x P‖≤1 := by
  unfold localRowValue
  split_ifs with h
  · let : P.IsMaximal := h.1
    let : Fintype (ActualEisensteinCubic.O⧸P) := Fintype.ofFinite _
    exact FiniteRayExpansion.norm_char_le_one _ _
  · simp

def idealRowHom (x : ActualEisensteinCubic.O) : Ideal ActualEisensteinCubic.O →*₀ ℂ := primeValueHom (localRowValue x)

def rowTwist (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) : ActualEisensteinCubic.O →* ℂ :=
  Ψ * (idealRowHom (m^6*f^4*z)).toMonoidHom.comp principalIdealHom.toMonoidHom

theorem idealRowHom_prime (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : lambda∉P) :
    idealRowHom x P = actualSextic P hg (Ideal.Quotient.mk P x) := by
  rw [idealRowHom,primeValueHom_prime _ P
    (Ideal.prime_of_isPrime (NeZero.ne P) inferInstance),localRowValue_good]

theorem idealRowHom_norm (x : ActualEisensteinCubic.O) (I : Ideal ActualEisensteinCubic.O) : ‖idealRowHom x I‖≤1 :=
  primeValueHom_norm_le_one _ (localRowValue_norm x) I

theorem rowTwist_norm (Ψ : ActualEisensteinCubic.O →* ℂ) (hΨ : ∀n,‖Ψ n‖≤1) (m f z n : ActualEisensteinCubic.O) :
    ‖rowTwist Ψ m f z n‖≤1 := by
  change ‖Ψ n * idealRowHom (m^6*f^4*z) (Ideal.span {n})‖≤1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hΨ n)).trans (idealRowHom_norm _ _)

theorem idealRowHom_product {ι : Type*} (p : ι → ActualEisensteinCubic.O)
    [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
    (S : Finset ι) (x : ActualEisensteinCubic.O) :
    idealRowHom x (Ideal.span {∏i∈S,p i}) =
      finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S x := by
  rw [FiniteGaussPhase.span_finset_prod,map_prod]
  simp only [finiteSquarefreeRow]
  apply Finset.prod_congr rfl
  intro i hi
  exact idealRowHom_prime x _ (hg i)

theorem rowTwist_product {ι : Type*} (p : ι → ActualEisensteinCubic.O)
    [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
    (S : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) :
    rowTwist Ψ m f z (∏i∈S,p i) =
      Ψ (∏i∈S,p i)*rowCoprimeMask (fun i=>Ideal.span {p i}) S m*
        finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S f^4*
        finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z := by
  change Ψ _ * idealRowHom _ (Ideal.span {∏i∈S,p i}) = _
  rw [idealRowHom_product p hg S,finiteSquarefreeRow_mul,finiteSquarefreeRow_mul,
    FirstPassCubeLabels.row_pow,FirstPassCubeLabels.row_pow,FirstPassCubeLabels.row_sixth]
  ring

end

open ActualEisensteinCubic
open CompletedGauss hiding O
open SecondPassArithmetic hiding O

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem squarefreeGaussCoefficient_finset (hpr : ∀i,lambda^2∣p i-1) (S : Finset ι) :
    squarefreeGaussCoefficient (Ideal.span {∏i∈S,p i}) =
      MixedCrossSeparation.columnCoefficient p hp hcop hg S := by
  have h := squarefreeGaussCoefficient_eq_canonicalProductCoefficient
    (fun i:S=>p i.val) (fun i=>hp i.val)
    (MixedCrossSeparation.columnPrimeCoprime p hcop S) (fun i=>hg i.val)
    (fun i=>hpr i.val)
  simpa only [Finset.prod_coe_sort,MixedCrossSeparation.columnCoefficient] using h

theorem columnWeight_finset (hpr : ∀i,lambda^2∣p i-1)
    (S : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (H : Finset ι → ℂ) :
    columnWeight (rowTwist Ψ m f z) (Ideal.span {∏i∈S,p i}) * H S =
      canonicalSourceCoefficient p hp hcop hg Ψ m f H S *
        finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z := by
  have hn : (∏i∈S,p i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hprimary : lambda^2∣(∏i∈S,p i)-1 := by
    have h := product_primary (fun i:S=>p i.val) (fun i=>hpr i.val)
    simpa only [Finset.prod_coe_sort] using h
  rw [columnWeight,squarefreeGaussCoefficient_finset p hp hcop hg hpr S,
    primaryGenerator_span _ hn hprimary,rowTwist_product p hg S]
  simp only [canonicalSourceCoefficient]
  ring

end

theorem selected_column_sum (F : Finset (Ideal ActualEisensteinCubic.O))
    (hF : ∀I∈F,CanonicalQuadraticSieve.Admissible I)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℕ → ℂ) :
    let p := CanonicalQuadraticSieve.poolPrimary F
    let hp := CanonicalQuadraticSieve.poolPrimary_ne_zero F hF
    letI : ∀i:ConcretePrimeRowBridge.primePool F,(Ideal.span {p i}).IsMaximal :=
      fun i=>by rw [CanonicalQuadraticSieve.poolPrimary_span F hF i]; infer_instance
    let hcop := CanonicalQuadraticSieve.poolPrimary_coprime F hF
    let hg := CanonicalQuadraticSieve.poolPrimary_good F hF
    (∑I∈F,columnWeight (rowTwist Ψ m f z) I * W (Ideal.absNorm I)) =
      ∑S∈(Finset.univ:Finset (ConcretePrimeRowBridge.primePool F)).powerset,
        canonicalSourceCoefficient p hp hcop hg Ψ m f (InitialMeanSquare.selectedIdealTest F W) S *
          finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z := by
  dsimp only
  let : ∀i:ConcretePrimeRowBridge.primePool F,
      (Ideal.span {CanonicalQuadraticSieve.poolPrimary F i}).IsMaximal :=
    fun i=>by rw [CanonicalQuadraticSieve.poolPrimary_span F hF i]; infer_instance
  rw [InitialMeanSquare.sum_selected_ideals F (fun I hI=>(hF I hI).2.1)]
  apply Finset.sum_congr rfl
  intro S hS
  have hspan : (Ideal.span {∏i∈S,CanonicalQuadraticSieve.poolPrimary F i}) = ∏i∈S,i.val := by
    rw [FiniteGaussPhase.span_finset_prod]
    exact Finset.prod_congr rfl (fun i _=>CanonicalQuadraticSieve.poolPrimary_span F hF i)
  have hpr (i:ConcretePrimeRowBridge.primePool F) :
      lambda^2∣CanonicalQuadraticSieve.poolPrimary F i-1 :=
    (primaryPrime_spec i.val (CanonicalQuadraticSieve.poolPrimary_ne_zero F hF i)).2.2.2
  have h := columnWeight_finset (CanonicalQuadraticSieve.poolPrimary F)
    (CanonicalQuadraticSieve.poolPrimary_ne_zero F hF)
    (CanonicalQuadraticSieve.poolPrimary_coprime F hF)
    (CanonicalQuadraticSieve.poolPrimary_good F hF) hpr S Ψ m f z
    (InitialMeanSquare.selectedIdealTest F W)
  rw [hspan] at h
  rw [←h]
  unfold InitialMeanSquare.selectedIdealTest
  split_ifs <;> simp

end CanonicalRowCompletion

end

end OAI
end OAIOriginalModule0224

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.RadialProfiles
Source SHA256: a5924a8c9d2c3c82262a8d694e5501231bb076cf3ec7096849b1b157e31622f1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0225


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

open scoped BigOperators Classical SchwartzMap ContDiff Topology
open Filter

def positiveRadialProfile (V : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0<x then V (Real.log x) else 0

theorem positiveRadialProfile_support (V : ℝ → ℂ) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) (x : ℝ) (hx : positiveRadialProfile V x≠0) :
    x∈Set.Icc (Real.exp (-A)) (Real.exp A) := by
  have hpos : 0<x := by
    by_contra hn
    exact hx (by simp [positiveRadialProfile,hn])
  have hlog : |Real.log x|≤A := hV _ (by simpa [positiveRadialProfile,hpos] using hx)
  constructor
  · calc
      Real.exp (-A) ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr (abs_le.mp hlog).1
      _ = x := Real.exp_log hpos
  · calc
      x = Real.exp (Real.log x) := (Real.exp_log hpos).symm
      _ ≤ Real.exp A := Real.exp_le_exp.mpr (abs_le.mp hlog).2

theorem positiveRadialProfile_compact (V : ℝ → ℂ) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) : HasCompactSupport (positiveRadialProfile V) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (fun x hx=>positiveRadialProfile_support V A hV x hx)

theorem positiveRadialProfile_smooth (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V)
    (A : ℝ) (hV : ∀s,V s≠0→|s|≤A) : ContDiff ℝ ∞ (positiveRadialProfile V) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hpos : 0<x
  · have he : positiveRadialProfile V =ᶠ[𝓝 x] (fun y=>V (Real.log y)) := by
      filter_upwards [Ioi_mem_nhds hpos] with y hy
      change 0<y at hy
      simp only [positiveRadialProfile,ite_eq_left hy]
    exact (hVs.contDiffAt.comp x (Real.contDiffAt_log.mpr hpos.ne')).congr_of_eventuallyEq he
  · have hx : x<Real.exp (-A) := (le_of_not_gt hpos).trans_lt (Real.exp_pos _)
    have he : positiveRadialProfile V =ᶠ[𝓝 x] (fun _=>0) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      by_contra hn
      have hb := (positiveRadialProfile_support V A hV y hn).1
      exact (not_le_of_gt hy) hb
    exact (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq he

def radialFromLog (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) : 𝓢(ℝ,ℂ) :=
  (positiveRadialProfile_compact V A hV).toSchwartzMap (positiveRadialProfile_smooth V hVs A hV)

@[simp] theorem radialFromLog_apply_pos (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) (x : ℝ) (hx : 0<x) :
    radialFromLog V hVs A hV x=V (Real.log x) := by
  change positiveRadialProfile V x=_
  simp only [positiveRadialProfile,ite_eq_left hx]

theorem radialFromLog_hasCompactSupport (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) : HasCompactSupport (radialFromLog V hVs A hV) :=
  positiveRadialProfile_compact V A hV

theorem radialFromLog_support (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) (x : ℝ) (hx : radialFromLog V hVs A hV x≠0) :
    Real.exp (-A)≤x ∧ x≤Real.exp A := positiveRadialProfile_support V A hV x hx

theorem radialFromLog_column {ι : Type*} (p : ι → ActualEisensteinCubic.O)
    (hp : ∀i,p i≠0) (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) (X : ℝ) (hX : 0<X) (S : Finset ι) :
    radialFromLog V hVs A hV (FirstPassCubeLabels.primeProductNorm p S/X)=
      V (FirstPassCubeLabels.columnLog p X S) :=
  radialFromLog_apply_pos V hVs A hV _ (div_pos (FirstPassCubeLabels.primeProductNorm_pos p hp S) hX)

end SecondPassArithmetic

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

def kernelTestPartitionTerm {ι : Type*} {S : Set KernelQuotient}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ,SpatialCoordinates) KernelQuotient S)
    (f : kernelSmoothTests) (i : ι) : kernelSmoothTests :=
  ⟨fun q => ρ i q • f.1 q,(ρ i).contMDiff.smul f.2.1,
    HasCompactSupport.smul_left (f := fun q => ρ i q) (f' := f.1) f.2.2⟩

lemma kernelTestPartitionTerm_tsupport {ι : Type*} {S : Set KernelQuotient}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ,SpatialCoordinates) KernelQuotient S)
    (f : kernelSmoothTests) (i : ι) :
    tsupport (kernelTestPartitionTerm ρ f i).1⊆tsupport (ρ i) :=
  tsupport_smul_subset_left _ _

lemma kernelTestPartition_sum {ι : Type*} [Fintype ι]
    (f : kernelSmoothTests)
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ,SpatialCoordinates) KernelQuotient (tsupport f.1)) :
    ∑i,kernelTestPartitionTerm ρ f i=f := by
  apply Subtype.ext
  funext q
  simp only [Submodule.coe_sum,Finset.sum_apply,kernelTestPartitionTerm]
  rw [←Finset.sum_smul]
  by_cases hq : q∈tsupport f.1
  · have hs := ρ.sum_eq_one hq
    rw [finsum_eq_sum_of_fintype] at hs
    rw [hs,one_smul]
  · have hz : f.1 q=0 := image_eq_zero_of_notMem_tsupport hq
    rw [hz,smul_zero]

theorem kernelSmoothTest_finite_chart_partition (f : kernelSmoothTests) :
    ∃t : Finset KernelGoodCutoff,∃g : t→kernelSmoothTests,
      (∑i,g i)=f ∧ ∀i,tsupport (g i).1⊆kernelChartCoreImage i.1.1 := by
  obtain ⟨t,ht⟩ := kernelCompact_finite_chart_cover (tsupport f.1) f.2.2
  have hc : tsupport f.1⊆⋃χ : t,kernelChartCoreImage χ.1.1 := by
    intro q hq
    obtain ⟨χ,hχ,hqχ⟩ := Set.mem_iUnion₂.mp (ht hq)
    exact Set.mem_iUnion.mpr ⟨⟨χ,hχ⟩,hqχ⟩
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,SpatialCoordinates)
    (isClosed_tsupport f.1) (fun χ : t => kernelChartCoreImage χ.1.1)
    (fun χ => kernelChartCoreImage_open χ.1.1) hc
  refine ⟨t,kernelTestPartitionTerm ρ f,kernelTestPartition_sum f ρ,fun i => ?_⟩
  exact (kernelTestPartitionTerm_tsupport ρ f i).trans (hρ i)

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv

namespace CubicEisenstein

def kernelFullCutoffFun (χ : PositiveChartCutoff) (p : EuclideanSpatial) : ℝ :=
  Real.smoothTransition (4*χ.func p-1)

lemma kernelFullCutoffFun_smooth (χ : PositiveChartCutoff) :
    ContDiff ℝ ∞ (kernelFullCutoffFun χ) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul χ.smooth).sub contDiff_const)

lemma kernelFullCutoffFun_tsupport (χ : PositiveChartCutoff) :
    tsupport (kernelFullCutoffFun χ)⊆tsupport χ.func := by
  apply closure_mono
  intro p hp
  change kernelFullCutoffFun χ p≠0 at hp
  change χ.func p≠0
  intro hz
  apply hp
  simp only [kernelFullCutoffFun,hz,mul_zero,zero_sub]
  exact Real.smoothTransition.zero_of_nonpos (by norm_num)

lemma kernelFullCutoffFun_compact (χ : PositiveChartCutoff) :
    HasCompactSupport (kernelFullCutoffFun χ) :=
  χ.compact.of_isClosed_subset (isClosed_tsupport _) (kernelFullCutoffFun_tsupport χ)

def kernelFullCutoff (χ : PositiveChartCutoff) : PositiveChartCutoff where
  func := kernelFullCutoffFun χ
  smooth := kernelFullCutoffFun_smooth χ
  compact := kernelFullCutoffFun_compact χ
  positive := (kernelFullCutoffFun_tsupport χ).trans χ.positive

lemma kernelFullCutoff_one (χ : PositiveChartCutoff) (p : EuclideanSpatial)
    (hp : p∈kernelChartCore χ) : (kernelFullCutoff χ).func p=1 := by
  apply Real.smoothTransition.one_of_one_le
  change (1/2 : ℝ)<χ.func p at hp
  linarith

lemma kernelFullCutoff_eventually_one (χ : PositiveChartCutoff) (p : EuclideanSpatial)
    (hp : p∈kernelChartCore χ) : (kernelFullCutoff χ).func =ᶠ[𝓝 p] fun _ => 1 := by
  filter_upwards [(kernelChartCore_open χ).mem_nhds hp] with q hq
  exact kernelFullCutoff_one χ q hq

def kernelCoreLift (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    𝓢(EuclideanSpatial,ℂ) := kernelLocalizedSchwartz (kernelFullCutoff χ) f

lemma kernelCoreLift_eventually_eq (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : p∈kernelChartCore χ) :
    (kernelCoreLift χ f : EuclideanSpatial→ℂ)=ᶠ[𝓝 p] kernelTestField f := by
  filter_upwards [kernelFullCutoff_eventually_one χ p hp] with q hq
  change (kernelFullCutoff χ).func q • kernelTestField f q=kernelTestField f q
  rw [hq,one_smul]

lemma kernelCoreLift_tsupport_outer (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    tsupport (kernelCoreLift χ f)⊆tsupport χ.func :=
  (kernelLocalizedField_tsupport (kernelFullCutoff χ) f).trans (kernelFullCutoffFun_tsupport χ)

lemma kernelCoreLift_tsupport (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f : kernelSmoothTests) (hf : tsupport f.1⊆kernelChartCoreImage χ) :
    tsupport (kernelCoreLift χ f)⊆kernelChartCore χ := by
  intro p hp
  have houter := kernelCoreLift_tsupport_outer χ f hp
  by_contra hn
  have hfp : kernelEuclideanProjection p∉tsupport f.1 := by
    intro hfp
    obtain ⟨q,hq,heq⟩ := hf hfp
    have hqp := hinj (kernelChartCore_subset χ hq) houter heq
    exact hn (hqp ▸ hq)
  have hc : ContinuousAt kernelEuclideanProjection p :=
    (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp
      (euclideanToHyperbolic_contMDiffAt p (χ.positive houter)).continuousAt
  have hz := (notMem_tsupport_iff_eventuallyEq.mp hfp).comp_tendsto hc
  have hzero : (kernelCoreLift χ f : EuclideanSpatial→ℂ)=ᶠ[𝓝 p] 0 := by
    filter_upwards [hz] with q hq
    change (kernelFullCutoff χ).func q • f.1 (kernelEuclideanProjection q)=0
    change f.1 (kernelEuclideanProjection q)=0 at hq
    rw [hq,smul_zero]
  exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hp

lemma kernelCoreLift_eq_on_outer (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f : kernelSmoothTests) (hf : tsupport f.1⊆kernelChartCoreImage χ) :
    Set.EqOn (kernelCoreLift χ f) (kernelTestField f) (tsupport χ.func) := by
  intro p hp
  by_cases hc : p∈kernelChartCore χ
  · exact (kernelCoreLift_eventually_eq χ f p hc).self_of_nhds
  · have hz : kernelTestField f p=0 := by
      change f.1 (kernelEuclideanProjection p)=0
      apply image_eq_zero_of_notMem_tsupport
      intro hfp
      obtain ⟨q,hq,heq⟩ := hf hfp
      have hqp := hinj (kernelChartCore_subset χ hq) hp heq
      exact hc (hqp ▸ hq)
    change (kernelFullCutoff χ).func p • kernelTestField f p=kernelTestField f p
    rw [hz,smul_zero]

def euclideanHeightCLM : EuclideanSpatial→L[ℝ]ℂ :=
  Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2)

lemma euclideanHeightCLM_apply (p : EuclideanSpatial) : euclideanHeightCLM p=(p 2:ℂ) := rfl

lemma upperHeightDivide_smooth (f : 𝓢(EuclideanSpatial,ℂ))
    (hpos : tsupport f⊆euclideanUpperHalf) :
    ContDiff ℝ ∞ (fun p : EuclideanSpatial => f p/(p 2:ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p 2=0
  · have hn : p∉tsupport f := by
      intro hf
      have hh := hpos hf
      change 0<p 2 at hh
      linarith
    have hz := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : EuclideanSpatial => (0 : ℂ)) p).congr_of_eventuallyEq
    filter_upwards [hz] with q hq
    simp only [hq,Pi.zero_apply,zero_div]
  · simpa only [div_eq_mul_inv,Pi.inv_apply,euclideanHeightCLM_apply] using
      (f.smooth ⊤).contDiffAt.mul (euclideanHeightCLM.contDiff.contDiffAt.fun_inv
        (Complex.ofReal_ne_zero.mpr hp))

lemma upperHeightDivide_compact (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) :
    HasCompactSupport (fun p : EuclideanSpatial => f p/(p 2:ℂ)) := by
  rw [hasCompactSupport_iff_eventuallyEq] at hcompact ⊢
  exact hcompact.mono (fun p hp => by simp only [hp,Pi.zero_apply,zero_div])

def upperHeightDivide (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) :
    𝓢(EuclideanSpatial,ℂ) :=
  (upperHeightDivide_compact f hcompact).toSchwartzMap (upperHeightDivide_smooth f hpos)

lemma upperHeightDivide_apply (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf)
    (p : EuclideanSpatial) : upperHeightDivide f hcompact hpos p=f p/(p 2:ℂ) := rfl

lemma upperHeightDivide_tsupport (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) :
    tsupport (upperHeightDivide f hcompact hpos)⊆tsupport f := by
  apply closure_mono
  intro p hp
  change f p/(p 2:ℂ)≠0 at hp
  change f p≠0
  exact fun hz => hp (by rw [hz,zero_div])

lemma upperHeightDivide_lineDeriv (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf)
    (p u : EuclideanSpatial) (hp : p 2≠0) :
    (∂_{u} (upperHeightDivide f hcompact hpos)) p=
      ((∂_{u} f) p*(p 2:ℂ)-f p*(u 2:ℂ))/(p 2:ℂ)^2 := by
  have hf := (f.hasFDerivAt p).hasLineDerivAt u
  have hv := (euclideanHeightCLM.hasFDerivAt (x := p)).hasLineDerivAt u
  change HasDerivAt (fun t : ℝ => f (p+t•u)) ((∂_{u} f) p) 0 at hf
  change HasDerivAt (fun t : ℝ => ((p+t•u) 2:ℂ)) (u 2:ℂ) 0 at hv
  have hd := hf.div hv (by simpa using Complex.ofReal_ne_zero.mpr hp)
  have hline : HasLineDerivAt ℝ (upperHeightDivide f hcompact hpos)
      (((∂_{u} f) p*(p 2:ℂ)-f p*(u 2:ℂ))/(p 2:ℂ)^2) p u := by
    simpa only [HasLineDerivAt,upperHeightDivide_apply,Pi.div_apply,zero_smul,add_zero] using! hd
  exact ((upperHeightDivide f hcompact hpos).hasFDerivAt p).hasLineDerivAt u |>.unique hline

lemma upperSchwartz_derivative_compact (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (u : EuclideanSpatial) :
    HasCompactSupport (∂_{u} f : 𝓢(EuclideanSpatial,ℂ)) :=
  hcompact.fderiv_apply ℝ u

def upperWeightedPartial (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) (j : Fin 3) :
    𝓢(EuclideanSpatial,ℂ) :=
  upperHeightDivide (∂_{euclideanCoordinateVector j} f)
    (upperSchwartz_derivative_compact f hcompact _)
    ((SchwartzMap.tsupport_lineDerivOp_subset _ f).trans hpos)

def upperWeightedDivergence (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) :
    𝓢(EuclideanSpatial,ℂ) :=
  -∑j : Fin 3,∂_{euclideanCoordinateVector j} (upperWeightedPartial f hcompact hpos j)

def complexHermitianBilin : ℂ→L[ℝ]ℂ→L[ℝ]ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ).comp Complex.conjCLE.toContinuousLinearMap

lemma schwartz_hermitian_integrable (f g : 𝓢(EuclideanSpatial,ℂ)) :
    Integrable (fun p => star (f p)*g p) volume :=
  (SchwartzMap.bilinLeftCLM complexHermitianBilin g.hasTemperateGrowth f).integrable

lemma schwartz_hermitian_lineGreen (f g : 𝓢(EuclideanSpatial,ℂ)) (u : EuclideanSpatial) :
    (∫p,star (f p)*(∂_{u} g) p)=-∫p,star ((∂_{u} f) p)*g p :=
  SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left f g complexHermitianBilin u

lemma upperWeighted_green (f g : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) :
    (∫p,∑j : Fin 3,star (upperWeightedPartial f hcompact hpos j p)*
      (∂_{euclideanCoordinateVector j} g) p)=
      ∫p,star (upperWeightedDivergence f hcompact hpos p)*g p := by
  calc
    _ = ∑j : Fin 3,∫p,star (upperWeightedPartial f hcompact hpos j p)*
        (∂_{euclideanCoordinateVector j} g) p :=
      integral_finsetSum _ (fun j hj => schwartz_hermitian_integrable _ _)
    _ = -∑j : Fin 3,∫p,star ((∂_{euclideanCoordinateVector j}
        (upperWeightedPartial f hcompact hpos j)) p)*g p := by
      simp only [schwartz_hermitian_lineGreen,Finset.sum_neg_distrib]
    _ = _ := by
      rw [←integral_finsetSum _ (fun j hj => schwartz_hermitian_integrable _ _),←integral_neg]
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by
        simp only [upperWeightedDivergence,_root_.neg_apply,_root_.sum_apply,star_neg,star_sum,
          Finset.sum_mul,neg_mul])

def upperPositiveLaplacian (f : 𝓢(EuclideanSpatial,ℂ)) (p : EuclideanSpatial) : ℂ :=
  -(p 2:ℂ)^2*(∑j : Fin 3,(∂_{euclideanCoordinateVector j} (∂_{euclideanCoordinateVector j} f)) p)+
    (p 2:ℂ)*(∂_{euclideanCoordinateVector 2} f) p

lemma upperWeightedDivergence_apply_ne_zero (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf)
    (p : EuclideanSpatial) (hp : p 2≠0) :
    upperWeightedDivergence f hcompact hpos p=upperPositiveLaplacian f p/(p 2:ℂ)^3 := by
  have hd (j : Fin 3) : (∂_{euclideanCoordinateVector j} (upperWeightedPartial f hcompact hpos j)) p=
      ((∂_{euclideanCoordinateVector j} (∂_{euclideanCoordinateVector j} f)) p*(p 2:ℂ)-
        (∂_{euclideanCoordinateVector j} f) p*(euclideanCoordinateVector j 2:ℂ))/(p 2:ℂ)^2 :=
    upperHeightDivide_lineDeriv _ _ _ p _ hp
  simp only [upperWeightedDivergence,Fin.sum_univ_three,_root_.neg_apply,_root_.add_apply]
  rw [hd 0,hd 1,hd 2]
  simp only [upperPositiveLaplacian,Fin.sum_univ_three]
  norm_num [euclideanCoordinateVector]
  field_simp [Complex.ofReal_ne_zero.mpr hp]
  ring

lemma upperWeightedDivergence_apply (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf)
    (p : EuclideanSpatial) :
    upperWeightedDivergence f hcompact hpos p=upperPositiveLaplacian f p/(p 2:ℂ)^3 := by
  by_cases hp : p 2=0
  · have hz : ∀j : Fin 3,(∂_{euclideanCoordinateVector j}
        (upperWeightedPartial f hcompact hpos j)) p=0 := by
      intro j
      have hn : p∉tsupport (upperWeightedPartial f hcompact hpos j) := by
        intro hm
        have ht := hpos ((SchwartzMap.tsupport_lineDerivOp_subset _ f)
          (upperHeightDivide_tsupport _ _ _ hm))
        change 0<p 2 at ht
        linarith
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,fderiv_of_notMem_tsupport ℝ hn]
      rfl
    simp only [upperWeightedDivergence,_root_.neg_apply,_root_.sum_apply,hz,Finset.sum_const_zero,neg_zero,
      upperPositiveLaplacian,hp,Complex.ofReal_zero,zero_pow (by decide : 2≠0),
      zero_pow (by decide : 3≠0),zero_mul,zero_add,zero_div]
  · exact upperWeightedDivergence_apply_ne_zero f hcompact hpos p hp

theorem upperHyperbolic_green (f g : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) :
    (∫p,∑j : Fin 3,star ((∂_{euclideanCoordinateVector j} f) p)*
      (∂_{euclideanCoordinateVector j} g) p/(p 2:ℂ))=
      ∫p,star (upperPositiveLaplacian f p)*g p/(p 2:ℂ)^3 := by
  have hh := upperWeighted_green f g hcompact hpos
  simpa only [upperWeightedPartial,upperHeightDivide_apply,upperWeightedDivergence_apply,
    star_div₀,star_pow,Complex.star_def,Complex.conj_ofReal,div_mul_eq_mul_div] using hh

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv

namespace CubicEisenstein

lemma kernelEuclideanProjection_integral_complex (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (g : KernelQuotient→ℂ)
    (hg : AEStronglyMeasurable g (integralQuotientVolume globalKubotaKernel)) :
    (∫p in S,g (kernelEuclideanProjection p)∂hyperbolicEuclideanVolume)=
      ∫q in kernelEuclideanProjection '' S,g q∂integralQuotientVolume globalKubotaKernel := by
  have hm := kernelEuclideanProjection_measurePreserving_on S hS hpos hinj
  have hh := hg.mono_measure (Measure.restrict_le_self (s := kernelEuclideanProjection '' S))
  rw [←hm.map_eq] at hh ⊢
  exact (integral_map hm.measurable.aemeasurable hh).symm

lemma hyperbolicEuclidean_setIntegral_complex (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf) (g : EuclideanSpatial→ℂ) :
    (∫p in S,g p∂hyperbolicEuclideanVolume)=∫p in S,g p/(p 2:ℂ)^3 := by
  rw [hyperbolicEuclideanVolume,MeasureTheory.restrict_withDensity hS,
    Measure.restrict_restrict hS,Set.inter_eq_left.mpr hpos,
    integral_withDensity_eq_integral_toReal_smul hyperbolicDensity_measurable
      (Eventually.of_forall (fun p => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hS] with p hp
  have hpositive : 0<p 2 := hpos hp
  rw [hyperbolicDensity,ENNReal.toReal_ofReal (by positivity)]
  rw [Complex.real_smul]
  change (↑(((p 2)^3)⁻¹) : ℂ)*g p=g p/(p 2:ℂ)^3
  simp only [Complex.ofReal_inv,Complex.ofReal_pow,div_eq_mul_inv,mul_comm]

lemma kernelDirichletPairDensity_zero_of_notMem (f g : kernelSmoothTests) (q : KernelQuotient)
    (hq : q∉tsupport g.1) : kernelDirichletPairDensity f g q=0 := by
  have hz : kernelQuotientEnergyDensity g q=0 := by
    by_contra hn
    exact hq (kernelQuotientEnergyDensity_support g hn)
  induction q using Quotient.inductionOn with
  | _ w =>
    change kernelDirichletPairDensity f g (integralOrbitProjection globalKubotaKernel w)=0
    rw [kernelDirichletPairDensity_coordinate]
    have hg : kernelGradientAt w g=0 := by
      apply norm_eq_zero.mp
      have h := kernelGradientAt_norm_sq w g
      change kernelTestEnergyDensity g w=0 at hz
      rw [hz] at h
      nlinarith [norm_nonneg (kernelGradientAt w g)]
    rw [hg,inner_zero_right]

lemma kernelDirichletPairDensity_euclidean (f g : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    kernelDirichletPairDensity f g (kernelEuclideanProjection p)=
      (p 2:ℂ)^2*∑j : Fin 3,star (fderiv ℝ (kernelTestField f) p (euclideanCoordinateVector j))*
        fderiv ℝ (kernelTestField g) p (euclideanCoordinateVector j) := by
  have hc := hyperbolicEuclideanCoordinates_toHyperbolic p hp
  have hv : hyperbolicHeight (euclideanToHyperbolic p)=p 2 := congrArg (fun q : EuclideanSpatial => q 2) hc
  change kernelDirichletPairDensity f g (integralOrbitProjection globalKubotaKernel (euclideanToHyperbolic p))=_
  rw [kernelDirichletPairDensity_coordinate,PiLp.inner_apply]
  change (∑j : Fin 3,inner ℂ ((hyperbolicHeight (euclideanToHyperbolic p):ℂ)*kernelTestPartial f (euclideanToHyperbolic p) j)
    ((hyperbolicHeight (euclideanToHyperbolic p):ℂ)*kernelTestPartial g (euclideanToHyperbolic p) j))=_
  rw [hv,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [kernelTestPartial,hc,←euclideanCoordinateVector_eq_basis,RCLike.inner_apply,
    map_mul,Complex.conj_ofReal,Complex.star_def]
  ring

lemma kernelCoreLift_fderiv_eq_on_outer (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f : kernelSmoothTests) (hf : tsupport f.1⊆kernelChartCoreImage χ)
    (p : EuclideanSpatial) (hp : p∈tsupport χ.func) :
    fderiv ℝ (kernelCoreLift χ f) p=fderiv ℝ (kernelTestField f) p := by
  by_cases hc : p∈kernelChartCore χ
  · exact (kernelCoreLift_eventually_eq χ f p hc).fderiv_eq
  · have hl : p∉tsupport (kernelCoreLift χ f) := fun h => hc (kernelCoreLift_tsupport χ hinj f hf h)
    have hfp : kernelEuclideanProjection p∉tsupport f.1 := by
      intro hfp
      obtain ⟨q,hq,heq⟩ := hf hfp
      exact hc ((hinj (kernelChartCore_subset χ hq) hp heq) ▸ hq)
    have hcont : ContinuousAt kernelEuclideanProjection p :=
      (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp
        (euclideanToHyperbolic_contMDiffAt p (χ.positive hp)).continuousAt
    have hz : kernelTestField f=ᶠ[𝓝 p]0 := (notMem_tsupport_iff_eventuallyEq.mp hfp).comp_tendsto hcont
    rw [fderiv_of_notMem_tsupport ℝ hl,hz.fderiv_eq,fderiv_zero]
    rfl

lemma kernelCoreLift_pair_on_outer (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f g : kernelSmoothTests) (hg : tsupport g.1⊆kernelChartCoreImage χ)
    (p : EuclideanSpatial) (hp : p∈tsupport χ.func) :
    kernelDirichletPairDensity f g (kernelEuclideanProjection p)=
      (p 2:ℂ)^2*∑j : Fin 3,star ((∂_{euclideanCoordinateVector j} (kernelCoreLift χ f)) p)*
        (∂_{euclideanCoordinateVector j} (kernelCoreLift χ g)) p := by
  rw [kernelDirichletPairDensity_euclidean f g p (χ.positive hp)]
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [←kernelCoreLift_fderiv_eq_on_outer χ hinj g hg p hp]
  by_cases hc : p∈kernelChartCore χ
  · rw [(kernelCoreLift_eventually_eq χ f p hc).fderiv_eq]
  · have hn : p∉tsupport (kernelCoreLift χ g) := fun h => hc (kernelCoreLift_tsupport χ hinj g hg h)
    rw [fderiv_of_notMem_tsupport ℝ hn]
    simp only [_root_.zero_apply,mul_zero,Finset.sum_const_zero]

theorem kernelDirichletForm_eq_chart_pairing (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f g : kernelSmoothTests) (hg : tsupport g.1⊆kernelChartCoreImage χ) :
    kernelDirichletForm f g=
      ∫p,∑j : Fin 3,star ((∂_{euclideanCoordinateVector j} (kernelCoreLift χ f)) p)*
        (∂_{euclideanCoordinateVector j} (kernelCoreLift χ g)) p/(p 2:ℂ) := by
  let S := tsupport χ.func
  have hS : MeasurableSet S := χ.compact.measurableSet
  have himg : kernelChartCoreImage χ⊆kernelEuclideanProjection '' S :=
    Set.image_mono (kernelChartCore_subset χ)
  calc
    _ = ∫q in kernelEuclideanProjection '' S,kernelDirichletPairDensity f g q
        ∂integralQuotientVolume globalKubotaKernel := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro q hq
      exact kernelDirichletPairDensity_zero_of_notMem f g q (fun h => hq (himg (hg h)))
    _ = ∫p in S,kernelDirichletPairDensity f g (kernelEuclideanProjection p)
        ∂hyperbolicEuclideanVolume :=
      (kernelEuclideanProjection_integral_complex S hS χ.positive hinj _
        (kernelDirichletPairDensity_integrable f g).aestronglyMeasurable).symm
    _ = ∫p in S,kernelDirichletPairDensity f g (kernelEuclideanProjection p)/(p 2:ℂ)^3 :=
      hyperbolicEuclidean_setIntegral_complex S hS χ.positive _
    _ = ∫p in S,∑j : Fin 3,star ((∂_{euclideanCoordinateVector j} (kernelCoreLift χ f)) p)*
        (∂_{euclideanCoordinateVector j} (kernelCoreLift χ g)) p/(p 2:ℂ) := by
      apply setIntegral_congr_fun hS
      intro p hp
      dsimp only
      rw [kernelCoreLift_pair_on_outer χ hinj f g hg p hp,←Finset.sum_div]
      have hv : (p 2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (χ.positive hp).ne'
      field_simp [hv]
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      have hn : p∉tsupport (kernelCoreLift χ g) := fun h => hp (kernelCoreLift_tsupport_outer χ g h)
      simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv,fderiv_of_notMem_tsupport ℝ hn,
        _root_.zero_apply,mul_zero,zero_div,Finset.sum_const_zero]

theorem kernelDirichletForm_eq_chart_laplacian (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f g : kernelSmoothTests) (hg : tsupport g.1⊆kernelChartCoreImage χ) :
    kernelDirichletForm f g=
      ∫p,star (upperPositiveLaplacian (kernelCoreLift χ f) p)*kernelCoreLift χ g p/(p 2:ℂ)^3 := by
  rw [kernelDirichletForm_eq_chart_pairing χ hinj f g hg]
  exact upperHyperbolic_green _ _ (kernelLocalizedField_compact (kernelFullCutoff χ) f)
    ((kernelCoreLift_tsupport_outer χ f).trans χ.positive)

end CubicEisenstein

end

end OAI
end OAIOriginalModule0225

/-! Original module: OAI.NumberTheory.DirichletL.ResidueCharacter
Source SHA256: f535a3a570315f6d3658542e8f4881bab5bc5f44f5e261332982ee702120d2de
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0226


namespace OAI

namespace SevenEighths.ResidueCharacter

open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open SevenEighths.ConductorPresentation
open scoped Classical

noncomputable section

variable {A : Type*} [CommRing A]

def inflate {M L : Ideal A} (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ) :
    MulChar (A ⧸ M) ℂ :=
  MulChar.ofUnitHom (χ.toUnitHom.comp
    (Units.map (Ideal.Quotient.factor hML).toMonoidHom))

theorem inflate_toUnitHom {M L : Ideal A} (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ) :
    (inflate hML χ).toUnitHom =
      χ.toUnitHom.comp (Units.map (Ideal.Quotient.factor hML).toMonoidHom) := by
  simp only [inflate, MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq, Equiv.apply_symm_apply]

theorem inflate_apply_unit {M L : Ideal A} (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ)
    (u : (A ⧸ M)ˣ) :
    inflate hML χ u = χ (Ideal.Quotient.factor hML (u : A ⧸ M)) :=
  MulChar.ofUnitHom_coe _ u

theorem inflate_apply {M L : Ideal A} (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ)
    (x : A ⧸ M) :
    inflate hML χ x = if IsUnit x then χ (Ideal.Quotient.factor hML x) else 0 := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    simpa only [u.isUnit, ite_true] using inflate_apply_unit hML χ u
  · simp only [hx, ite_false, MulChar.map_nonunit _ hx]

theorem inflate_mk {M L : Ideal A} (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ) (a : A) :
    inflate hML χ (Ideal.Quotient.mk M a) =
      if IsUnit (Ideal.Quotient.mk M a) then χ (Ideal.Quotient.mk L a) else 0 := by
  simpa only [Ideal.Quotient.factor_mk] using inflate_apply hML χ (Ideal.Quotient.mk M a)

theorem inflate_factorsThrough {M L : Ideal A} [Finite (A ⧸ M)]
    (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ) :
    FactorsThroughIdeal (inflate hML χ) (L.map (Ideal.Quotient.mk M)) := by
  rw [factorsThroughIdeal_iff]
  intro u hu
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : A ⧸ M)
  have haL : a - 1 ∈ L := by
    apply (Ideal.mem_quotient_iff_mem hML).mp
    simpa only [map_sub, map_one, ha] using hu
  have ha1 : Ideal.Quotient.mk L a = 1 :=
    (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr haL
  rw [inflate_apply_unit, ← ha, Ideal.Quotient.factor_mk, ha1, map_one]

theorem inflate_trans {M L K : Ideal A} (hML : M ≤ L) (hLK : L ≤ K)
    (χ : MulChar (A ⧸ K) ℂ) :
    inflate hML (inflate hLK χ) = inflate (hML.trans hLK) χ := by
  apply MulChar.ext
  intro u
  rw [inflate_apply_unit]
  let v : (A ⧸ L)ˣ := Units.map (Ideal.Quotient.factor hML).toMonoidHom u
  change inflate hLK χ (v : A ⧸ L) = _
  rw [inflate_apply_unit, inflate_apply_unit]
  exact congrArg χ (Ideal.Quotient.factor_comp_apply hML hLK (u : A ⧸ M))

theorem inflate_global_units {M L : Ideal A} (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ)
    (hχ : ∀ u : Aˣ, χ (Ideal.Quotient.mk L u) = 1) :
    ∀ u : Aˣ, inflate hML χ (Ideal.Quotient.mk M u) = 1 := by
  intro u
  rw [inflate_mk]
  simp only [u.isUnit.map (Ideal.Quotient.mk M), ite_true, hχ]

theorem isUnit_mk_inf_iff (I J : Ideal A) (a : A) :
    IsUnit (Ideal.Quotient.mk (I ⊓ J) a) ↔
      IsUnit (Ideal.Quotient.mk I a) ∧ IsUnit (Ideal.Quotient.mk J a) := by
  constructor
  · intro h
    constructor
    · simpa only [Ideal.Quotient.factor_mk] using
        (h.map (Ideal.Quotient.factor (show I ⊓ J ≤ I from inf_le_left)))
    · simpa only [Ideal.Quotient.factor_mk] using
        (h.map (Ideal.Quotient.factor (show I ⊓ J ≤ J from inf_le_right)))
  · rintro ⟨hI, hJ⟩
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hI
    obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp hJ
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hbI : a * b - 1 ∈ I :=
      (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp (by simpa only [map_mul] using hb)
    have hcJ : a * c - 1 ∈ J :=
      (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp (by simpa only [map_mul] using hc)
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Ideal.Quotient.mk (I ⊓ J) (b + c - a * b * c), ?_⟩
    rw [← map_mul]
    apply (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr
    have hid : a * (b + c - a * b * c) - 1 = -((a * b - 1) * (a * c - 1)) := by ring
    rw [hid]
    exact ⟨I.neg_mem (I.mul_mem_right _ hbI), J.neg_mem (J.mul_mem_left _ hcJ)⟩

theorem finite_quotient_inf (I J : Ideal A) [Finite (A ⧸ I)] [Finite (A ⧸ J)] :
    Finite (A ⧸ I ⊓ J) := by
  let f : A ⧸ I ⊓ J →+* (A ⧸ I) × (A ⧸ J) :=
    (Ideal.Quotient.factor inf_le_left).prod (Ideal.Quotient.factor inf_le_right)
  apply Finite.of_injective f
  apply (injective_iff_map_eq_zero f).mpr
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact ⟨Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.fst hx),
    Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.snd hx)⟩

def product (I J : Ideal A) (χ : MulChar (A ⧸ I) ℂ) (ψ : MulChar (A ⧸ J) ℂ) :
    MulChar (A ⧸ I ⊓ J) ℂ :=
  inflate inf_le_left χ * inflate inf_le_right ψ

theorem product_mk (I J : Ideal A) (χ : MulChar (A ⧸ I) ℂ) (ψ : MulChar (A ⧸ J) ℂ)
    (a : A) :
    product I J χ ψ (Ideal.Quotient.mk (I ⊓ J) a) =
      χ (Ideal.Quotient.mk I a) * ψ (Ideal.Quotient.mk J a) := by
  rw [product, MulChar.mul_apply, inflate_mk, inflate_mk]
  by_cases ha : IsUnit (Ideal.Quotient.mk (I ⊓ J) a)
  · simp only [ha, ite_true]
  · simp only [ha, ite_false, zero_mul]
    by_cases hI : IsUnit (Ideal.Quotient.mk I a)
    · have hJ : ¬ IsUnit (Ideal.Quotient.mk J a) := fun hJ =>
        ha ((isUnit_mk_inf_iff I J a).mpr ⟨hI, hJ⟩)
      rw [MulChar.map_nonunit _ hJ, mul_zero]
    · rw [MulChar.map_nonunit _ hI, zero_mul]

theorem product_global_units (I J : Ideal A) (χ : MulChar (A ⧸ I) ℂ)
    (ψ : MulChar (A ⧸ J) ℂ)
    (hχ : ∀ u : Aˣ, χ (Ideal.Quotient.mk I u) = 1)
    (hψ : ∀ u : Aˣ, ψ (Ideal.Quotient.mk J u) = 1) :
    ∀ u : Aˣ, product I J χ ψ (Ideal.Quotient.mk (I ⊓ J) u) = 1 := by
  intro u
  rw [product_mk, hχ, hψ, one_mul]

section PrimitiveProduct

variable [IsDedekindDomain A] [Infinite A]

theorem exists_primitive_product (I J : Ideal A) [Finite (A ⧸ I)] [Finite (A ⧸ J)]
    (χ : MulChar (A ⧸ I) ℂ) (ψ : MulChar (A ⧸ J) ℂ) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      I ⊓ J ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧
      K.absNorm ≤ I.absNorm * J.absNorm ∧
      ∀ a : A, χ (Ideal.Quotient.mk I a) * ψ (Ideal.Quotient.mk J a) =
        if IsUnit (Ideal.Quotient.mk I a) ∧ IsUnit (Ideal.Quotient.mk J a)
          then φ (Ideal.Quotient.mk K a) else 0 := by
  let : Finite (A ⧸ I ⊓ J) := finite_quotient_inf I J
  obtain ⟨K, φ, hIK, hK, hprimitive, hnorm, hmask⟩ :=
    exists_primitive_presentation (I ⊓ J) (product I J χ ψ)
  refine ⟨K, φ, hIK, hK, hprimitive, hnorm.trans (absNorm_inf_le_mul I J), ?_⟩
  intro a
  simpa only [product_mk, isUnit_mk_inf_iff] using hmask a

theorem exists_primitive_product_global_units
    (I J : Ideal A) [Finite (A ⧸ I)] [Finite (A ⧸ J)]
    (χ : MulChar (A ⧸ I) ℂ) (ψ : MulChar (A ⧸ J) ℂ)
    (hχ : ∀ u : Aˣ, χ (Ideal.Quotient.mk I u) = 1)
    (hψ : ∀ u : Aˣ, ψ (Ideal.Quotient.mk J u) = 1) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      I ⊓ J ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧
      K.absNorm ≤ I.absNorm * J.absNorm ∧
      (∀ u : Aˣ, φ (Ideal.Quotient.mk K u) = 1) ∧
      ∀ a : A, χ (Ideal.Quotient.mk I a) * ψ (Ideal.Quotient.mk J a) =
        if IsUnit (Ideal.Quotient.mk I a) ∧ IsUnit (Ideal.Quotient.mk J a)
          then φ (Ideal.Quotient.mk K a) else 0 := by
  obtain ⟨K, φ, hIK, hK, hprimitive, hnorm, hmask⟩ := exists_primitive_product I J χ ψ
  refine ⟨K, φ, hIK, hK, hprimitive, hnorm, ?_, hmask⟩
  intro u
  have h := hmask (u : A)
  simpa only [hχ, hψ, one_mul, u.isUnit.map (Ideal.Quotient.mk I),
    u.isUnit.map (Ideal.Quotient.mk J), and_self, ite_true] using h.symm

end PrimitiveProduct

end

end SevenEighths.ResidueCharacter

end OAI
end OAIOriginalModule0226

/-! Original module: OAI.NumberTheory.DirichletL.IdealCharacter
Source SHA256: ae9e08095d0eaa044a305e11db19c7d363302159897fcd54d07f65f952cc1f6e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0227



namespace OAI

namespace SevenEighths.IdealCharacter

open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open SevenEighths.ConductorPresentation
open Submodule.IsPrincipal
open scoped Classical

noncomputable section

variable {A : Type*} [CommRing A]

abbrev UnitInvariant (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) : Prop :=
  ∀ u : Aˣ, χ (Ideal.Quotient.mk M u) = 1

theorem residue_eq_of_associated (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) {a b : A} (hab : Associated a b) :
    χ (Ideal.Quotient.mk M a) = χ (Ideal.Quotient.mk M b) := by
  obtain ⟨u, rfl⟩ := hab
  rw [map_mul, map_mul, hχ u, mul_one]

theorem isUnit_mk_iff_isCoprime (M : Ideal A) (a : A) :
    IsUnit (Ideal.Quotient.mk M a) ↔ IsCoprime (Ideal.span ({a} : Set A)) M := by
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, Ideal.mem_span_singleton_sup]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv'.mp h
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hba : b * a - 1 ∈ M :=
      (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp (by simpa only [map_mul] using hb)
    refine ⟨b, -(b * a - 1), M.neg_mem hba, ?_⟩
    ring
  · rintro ⟨b, c, hc, hbc⟩
    apply isUnit_iff_exists_inv'.mpr
    refine ⟨Ideal.Quotient.mk M b, ?_⟩
    have h := congrArg (Ideal.Quotient.mk M) hbc
    simpa only [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hc,
      add_zero, map_one] using h

section Principal

variable [IsDomain A] [IsPrincipalIdealRing A]

def value (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) (I : Ideal A) : ℂ :=
  if I = ⊥ then 0 else χ (Ideal.Quotient.mk M (generator I))

omit [IsDomain A] in
theorem value_bot (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) : value M χ ⊥ = 0 := by
  simp only [value, ite_true]

theorem value_span (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ)
    {a : A} (ha : a ≠ 0) :
    value M χ (Ideal.span ({a} : Set A)) = χ (Ideal.Quotient.mk M a) := by
  have hI : Ideal.span ({a} : Set A) ≠ ⊥ := by
    exact fun h => ha (Ideal.span_singleton_eq_bot.mp h)
  simp only [value, hI, ite_false]
  exact residue_eq_of_associated M χ hχ (associated_generator_span_self a)

def ofResidue (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ) :
    Ideal A →*₀ ℂ where
  toFun := value M χ
  map_zero' := value_bot M χ
  map_one' := by
    simpa only [Ideal.span_singleton_one, Ideal.one_eq_top, map_one] using
      value_span M χ hχ (one_ne_zero : (1 : A) ≠ 0)
  map_mul' I J := by
    by_cases hI : I = ⊥
    · subst I
      simp only [Ideal.bot_mul, value_bot, zero_mul]
    by_cases hJ : J = ⊥
    · subst J
      simp only [Ideal.mul_bot, value_bot, mul_zero]
    let a := generator I
    let b := generator J
    have ha : a ≠ 0 := fun h => hI ((eq_bot_iff_generator_eq_zero I).mpr h)
    have hb : b ≠ 0 := fun h => hJ ((eq_bot_iff_generator_eq_zero J).mpr h)
    have hIa : Ideal.span ({a} : Set A) = I := Ideal.span_singleton_generator I
    have hJb : Ideal.span ({b} : Set A) = J := Ideal.span_singleton_generator J
    calc
      value M χ (I * J) = value M χ (Ideal.span ({a * b} : Set A)) := by
        rw [← Ideal.span_singleton_mul_span_singleton, hIa, hJb]
      _ = χ (Ideal.Quotient.mk M (a * b)) := value_span M χ hχ (mul_ne_zero ha hb)
      _ = χ (Ideal.Quotient.mk M a) * χ (Ideal.Quotient.mk M b) := by
        rw [map_mul, map_mul]
      _ = value M χ I * value M χ J := by
        rw [← hIa, ← hJb, value_span M χ hχ ha, value_span M χ hχ hb]

@[simp] theorem ofResidue_bot (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) : ofResidue M χ hχ ⊥ = 0 := value_bot M χ

theorem ofResidue_span (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ)
    {a : A} (ha : a ≠ 0) :
    ofResidue M χ hχ (Ideal.span ({a} : Set A)) = χ (Ideal.Quotient.mk M a) :=
  value_span M χ hχ ha

theorem ofResidue_of_generator (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) {I : Ideal A} (hI : I ≠ ⊥) {a : A}
    (ha : Ideal.span ({a} : Set A) = I) :
    ofResidue M χ hχ I = χ (Ideal.Quotient.mk M a) := by
  have ha0 : a ≠ 0 := by
    intro h
    apply hI
    simpa only [h, Ideal.span_singleton_zero] using ha.symm
  rw [← ha, ofResidue_span M χ hχ ha0]

omit [IsDomain A] [IsPrincipalIdealRing A] in
theorem norm_residue_le_one (M : Ideal A) [Finite (A ⧸ M)]
    (χ : MulChar (A ⧸ M) ℂ) (a : A ⧸ M) : ‖χ a‖ ≤ 1 := by
  let : Fintype (A ⧸ M)ˣ := Fintype.ofFinite _
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    have h := Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
    have hn : ‖χ (u : A ⧸ M)‖ = 1 := by
      simpa only [MulChar.coe_equivToUnitHom] using h
    exact hn.le
  · rw [MulChar.map_nonunit χ ha, norm_zero]
    exact zero_le_one

theorem norm_ofResidue_le_one (M : Ideal A) [Finite (A ⧸ M)]
    (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ) (I : Ideal A) :
    ‖ofResidue M χ hχ I‖ ≤ 1 := by
  by_cases hI : I = ⊥
  · rw [hI, ofResidue_bot, norm_zero]
    exact zero_le_one
  · change ‖value M χ I‖ ≤ 1
    simp only [value, hI, ite_false]
    exact norm_residue_le_one M χ _

omit [IsDomain A] [IsPrincipalIdealRing A] in

theorem one_unitInvariant (M : Ideal A) : UnitInvariant M (1 : MulChar (A ⧸ M) ℂ) := by
  intro u
  exact MulChar.one_apply (u.isUnit.map (Ideal.Quotient.mk M))

theorem ofResidue_one (M : Ideal A) (I : Ideal A) :
    ofResidue M 1 (one_unitInvariant M) I =
      if I = ⊥ then 0 else if IsCoprime I M then 1 else 0 := by
  by_cases hI : I = ⊥
  · simp only [hI, ofResidue_bot, ite_true]
  · have hg : generator I ≠ 0 := fun h => hI ((eq_bot_iff_generator_eq_zero I).mpr h)
    have heq := ofResidue_span M 1 (one_unitInvariant M) hg
    rw [Ideal.span_singleton_generator] at heq
    rw [heq]
    simp only [hI, ite_false]
    have hu : IsUnit (Ideal.Quotient.mk M (generator I)) ↔ IsCoprime I M := by
      simpa only [Ideal.span_singleton_generator] using isUnit_mk_iff_isCoprime M (generator I)
    by_cases hc : IsCoprime I M
    · simp only [hc, ite_true]
      exact MulChar.one_apply (hu.mpr hc)
    · simp only [hc, ite_false]
      exact MulChar.map_nonunit _ (fun h => hc (hu.mp h))

theorem ofResidue_one_top (I : Ideal A) :
    ofResidue (⊤ : Ideal A) 1 (one_unitInvariant ⊤) I = if I = ⊥ then 0 else 1 := by
  rw [ofResidue_one]
  have h : IsCoprime I (⊤ : Ideal A) := Ideal.isCoprime_iff_sup_eq.mpr (sup_top_eq I)
  simp only [h, ite_true]

theorem ofResidue_source_mask (M K : Ideal A)
    (χ : MulChar (A ⧸ M) ℂ) (φ : MulChar (A ⧸ K) ℂ)
    (hχ : UnitInvariant M χ) (hφ : UnitInvariant K φ)
    (hmask : ∀ a : A, χ (Ideal.Quotient.mk M a) =
      if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0)
    (I : Ideal A) :
    ofResidue M χ hχ I = if IsCoprime I M then ofResidue K φ hφ I else 0 := by
  by_cases hI : I = ⊥
  · simp only [hI, ofResidue_bot, ite_self]
  · have hg : generator I ≠ 0 := fun h => hI ((eq_bot_iff_generator_eq_zero I).mpr h)
    have h := hmask (generator I)
    have hcop : IsUnit (Ideal.Quotient.mk M (generator I)) ↔ IsCoprime I M := by
      simpa only [Ideal.span_singleton_generator] using isUnit_mk_iff_isCoprime M (generator I)
    rw [← ofResidue_span M χ hχ hg, ← ofResidue_span K φ hφ hg,
      Ideal.span_singleton_generator] at h
    simpa only [hcop] using h

theorem ofResidue_finite_deletion (M K : Ideal A)
    (χ : MulChar (A ⧸ M) ℂ) (φ : MulChar (A ⧸ K) ℂ)
    (hχ : UnitInvariant M χ) (hφ : UnitInvariant K φ)
    (hmask : ∀ a : A, χ (Ideal.Quotient.mk M a) =
      if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0)
    (I : Ideal A) :
    ofResidue M χ hχ I =
      ofResidue M 1 (one_unitInvariant M) I * ofResidue K φ hφ I := by
  rw [ofResidue_source_mask M K χ φ hχ hφ hmask, ofResidue_one]
  by_cases hI : I = ⊥
  · simp only [hI, ofResidue_bot, ite_true, ite_self, mul_zero]
  · simp only [hI, ite_false]
    split_ifs <;> simp only [one_mul, zero_mul]

theorem ofResidue_product (M N : Ideal A)
    (χ : MulChar (A ⧸ M) ℂ) (ψ : MulChar (A ⧸ N) ℂ)
    (hχ : UnitInvariant M χ) (hψ : UnitInvariant N ψ) (I : Ideal A) :
    ofResidue (M ⊓ N) (ResidueCharacter.product M N χ ψ)
        (ResidueCharacter.product_global_units M N χ ψ hχ hψ) I =
      ofResidue M χ hχ I * ofResidue N ψ hψ I := by
  by_cases hI : I = ⊥
  · simp only [hI, ofResidue_bot, mul_zero]
  · have hg : generator I ≠ 0 := fun h => hI ((eq_bot_iff_generator_eq_zero I).mpr h)
    conv_lhs => rw [← Ideal.span_singleton_generator I]
    rw [ofResidue_span _ _ _ hg, ResidueCharacter.product_mk]
    rw [← ofResidue_span M χ hχ hg, ← ofResidue_span N ψ hψ hg,
      Ideal.span_singleton_generator]

section Primitive

variable [Infinite A]

theorem exists_primitive_associate (M : Ideal A) [Finite (A ⧸ M)]
    (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ) (hφ : UnitInvariant K φ),
      M ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ M.absNorm ∧
      (∀ I : Ideal A, ofResidue M χ hχ I =
        if IsCoprime I M then ofResidue K φ hφ I else 0) ∧
      ∀ I : Ideal A, ofResidue M χ hχ I =
        ofResidue M 1 (one_unitInvariant M) I * ofResidue K φ hφ I := by
  obtain ⟨K, φ, hMK, hK, hprimitive, hnorm, hmask⟩ := exists_primitive_presentation M χ
  have hφ : UnitInvariant K φ := by
    intro u
    have h := hmask (u : A)
    simpa only [hχ u, u.isUnit.map (Ideal.Quotient.mk M), ite_true] using h.symm
  exact ⟨K, φ, hφ, hMK, hK, hprimitive, hnorm,
    ofResidue_source_mask M K χ φ hχ hφ hmask,
    ofResidue_finite_deletion M K χ φ hχ hφ hmask⟩

theorem exists_primitive_product_associate (M N : Ideal A)
    [Finite (A ⧸ M)] [Finite (A ⧸ N)]
    (χ : MulChar (A ⧸ M) ℂ) (ψ : MulChar (A ⧸ N) ℂ)
    (hχ : UnitInvariant M χ) (hψ : UnitInvariant N ψ) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ) (hφ : UnitInvariant K φ),
      M ⊓ N ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧
      K.absNorm ≤ M.absNorm * N.absNorm ∧
      (∀ I : Ideal A, ofResidue M χ hχ I * ofResidue N ψ hψ I =
        if IsCoprime I (M ⊓ N) then ofResidue K φ hφ I else 0) ∧
      ∀ I : Ideal A, ofResidue M χ hχ I * ofResidue N ψ hψ I =
        ofResidue (M ⊓ N) 1 (one_unitInvariant (M ⊓ N)) I * ofResidue K φ hφ I := by
  let : Finite (A ⧸ M ⊓ N) := ResidueCharacter.finite_quotient_inf M N
  obtain ⟨K, φ, hφ, hMNK, hK, hprimitive, hnorm, hmask, hdelete⟩ :=
    exists_primitive_associate (M ⊓ N) (ResidueCharacter.product M N χ ψ)
      (ResidueCharacter.product_global_units M N χ ψ hχ hψ)
  refine ⟨K, φ, hφ, hMNK, hK, hprimitive, hnorm.trans (absNorm_inf_le_mul M N), ?_, ?_⟩
  · intro I
    exact (ofResidue_product M N χ ψ hχ hψ I).symm.trans (hmask I)
  · intro I
    exact (ofResidue_product M N χ ψ hχ hψ I).symm.trans (hdelete I)

end Primitive

end Principal

end

end SevenEighths.IdealCharacter

end OAI
end OAIOriginalModule0227

/-! Original module: OAI.NumberTheory.DirichletL.RayOrthogonality
Source SHA256: 85ff7487c61c123c298ed50f372be88338689a5d9d83ed4827bae30664243eed
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0228



namespace OAI

namespace SevenEighths.RayOrthogonality

open scoped Classical
noncomputable section

section FiniteMonoid
variable {R : Type*} [CommMonoid R] [Finite R]

def characters (H : Subgroup Rˣ) : Subgroup (MulChar R ℂ) :=
  (MulChar.subgroupOrderIsoSubgroupMulChar R ℂ H).ofDual

instance (H : Subgroup Rˣ) : Fintype (characters H) := Fintype.ofFinite _

theorem mem_characters_iff (H : Subgroup Rˣ) (χ : MulChar R ℂ) :
    χ ∈ characters H ↔ ∀ u ∈ H, χ u = 1 :=
  MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff

theorem card_characters (H : Subgroup Rˣ) :
    Fintype.card (characters H) = Nat.card (Rˣ ⧸ H) := by
  rw [← Nat.card_eq_fintype_card]
  exact MulChar.card_subgroupOrderIsoSubgroupMulChar

theorem exists_character_ne_one (H : Subgroup Rˣ) {u : Rˣ} (hu : u ∉ H) :
    ∃ χ : characters H, (χ : MulChar R ℂ) u ≠ 1 := by
  by_contra hn
  apply hu
  have hall : ∀ χ ∈ characters H, χ u = 1 := by
    intro χ hχ
    by_contra h
    exact hn ⟨⟨χ, hχ⟩, h⟩
  have hh := (MulChar.mem_subgroupOrderIsoSubgroupMulChar_symm_iff).mpr hall
  simpa only [characters, OrderDual.toDual_ofDual, OrderIso.symm_apply_apply] using hh

theorem sum_characters_unit (H : Subgroup Rˣ) (u : Rˣ) :
    ∑ χ : characters H, (χ : MulChar R ℂ) u =
      if u ∈ H then (Nat.card (Rˣ ⧸ H) : ℂ) else 0 := by
  by_cases hu : u ∈ H
  · simp only [hu, ite_true]
    calc
      _ = ∑ _χ : characters H, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro χ _
        exact (mem_characters_iff H χ).mp χ.property u hu
      _ = _ := by simp [card_characters]
  · simp only [hu, ite_false]
    obtain ⟨χ, hχ⟩ := exists_character_ne_one H hu
    refine eq_zero_of_mul_eq_self_left hχ ?_
    simp only [Finset.mul_sum, ← MulChar.mul_apply]
    exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' ↦ rfl

def inUnitSubgroup (H : Subgroup Rˣ) (r : R) : Prop :=
  ∃ u : Rˣ, (u : R) = r ∧ u ∈ H

theorem sum_characters (H : Subgroup Rˣ) (r : R) :
    ∑ χ : characters H, (χ : MulChar R ℂ) r =
      if inUnitSubgroup H r then (Nat.card (Rˣ ⧸ H) : ℂ) else 0 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    have hi : inUnitSubgroup H (u : R) ↔ u ∈ H := by
      constructor
      · rintro ⟨v, hv, h⟩
        exact (Units.ext hv) ▸ h
      · exact fun h ↦ ⟨u, rfl, h⟩
    rw [sum_characters_unit, hi]
  · have hn : ¬ inUnitSubgroup H r := by
      rintro ⟨u, rfl, _⟩
      exact hr u.isUnit
    simp only [hn, ite_false]
    exact Finset.sum_eq_zero fun χ _ ↦ MulChar.map_nonunit χ.val hr

theorem ray_card_pos (H : Subgroup Rˣ) : 0 < Nat.card (Rˣ ⧸ H) :=
  Nat.card_pos

theorem average_characters (H : Subgroup Rˣ) (r : R) :
    (∑ χ : characters H, (χ : MulChar R ℂ) r) / (Nat.card (Rˣ ⧸ H) : ℂ) =
      if inUnitSubgroup H r then 1 else 0 := by
  rw [sum_characters]
  have hn : (Nat.card (Rˣ ⧸ H) : ℂ) ≠ 0 := by
    exact_mod_cast (ray_card_pos H).ne'
  split_ifs <;> simp [hn]

end FiniteMonoid

section Residues
variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]

def globalUnits : Subgroup (A ⧸ M)ˣ :=
  (Units.map (Ideal.Quotient.mk M).toMonoidHom).range

abbrev rayCharacters := characters (globalUnits M)

theorem mem_rayCharacters_iff (χ : MulChar (A ⧸ M) ℂ) :
    χ ∈ rayCharacters M ↔ IdealCharacter.UnitInvariant M χ := by
  rw [mem_characters_iff]
  constructor
  · intro h u
    exact h _ ⟨u, rfl⟩
  · intro h u hu
    obtain ⟨v, rfl⟩ := hu
    exact h v

def principalResidue (r : A ⧸ M) : Prop :=
  ∃ u : Aˣ, Ideal.Quotient.mk M u = r

omit [Finite (A ⧸ M)] in
theorem inUnitSubgroup_globalUnits_iff (r : A ⧸ M) :
    inUnitSubgroup (globalUnits M) r ↔ principalResidue M r := by
  constructor
  · rintro ⟨u, hur, v, hv⟩
    exact ⟨v, (congrArg Units.val hv).trans hur⟩
  · rintro ⟨u, hu⟩
    exact ⟨Units.map (Ideal.Quotient.mk M).toMonoidHom u, hu, ⟨u, rfl⟩⟩

abbrev rayCard : ℕ := Nat.card ((A ⧸ M)ˣ ⧸ globalUnits M)

theorem rayCard_pos : 0 < rayCard M := ray_card_pos _

theorem sum_rayCharacters (r : A ⧸ M) :
    ∑ χ : rayCharacters M, (χ : MulChar (A ⧸ M) ℂ) r =
      if principalResidue M r then (rayCard M : ℂ) else 0 := by
  rw [sum_characters, inUnitSubgroup_globalUnits_iff]

theorem average_rayCharacters (r : A ⧸ M) :
    (∑ χ : rayCharacters M, (χ : MulChar (A ⧸ M) ℂ) r) / (rayCard M : ℂ) =
      if principalResidue M r then 1 else 0 := by
  rw [average_characters, inUnitSubgroup_globalUnits_iff]

section PrincipalIdeals
variable [IsDomain A] [IsPrincipalIdealRing A]

def idealCharacter (χ : rayCharacters M) : Ideal A →*₀ ℂ :=
  IdealCharacter.ofResidue M χ ((mem_rayCharacters_iff M χ).mp χ.property)

def principalIdeals : Set (Ideal A) :=
  {I | I ≠ ⊥ ∧ ∃ a : A, Ideal.span ({a} : Set A) = I ∧
    principalResidue M (Ideal.Quotient.mk M a)}

omit [Finite (A ⧸ M)] in
theorem principalIdeals_iff_generator {I : Ideal A} (hI : I ≠ ⊥) :
    I ∈ principalIdeals M ↔
      principalResidue M (Ideal.Quotient.mk M (Submodule.IsPrincipal.generator I)) := by
  constructor
  · rintro ⟨_, a, ha, u, hu⟩
    have hga : Associated (Submodule.IsPrincipal.generator I) a := by
      rw [← ha]
      exact Submodule.IsPrincipal.associated_generator_span_self a
    obtain ⟨v, hv⟩ := hga
    refine ⟨u * v⁻¹, ?_⟩
    have hq := congrArg (Ideal.Quotient.mk M) hv
    simp only [map_mul] at hq
    simp only [Units.val_mul, map_mul]
    rw [hu, ← hq]
    rw [mul_assoc, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, mul_one]
  · intro h
    exact ⟨hI, _, Ideal.span_singleton_generator I, h⟩

omit [Finite (A ⧸ M)] [IsPrincipalIdealRing A] in

theorem principalIdeals_iff_congruent_one (I : Ideal A) :
    I ∈ principalIdeals M ↔ ∃ a : A, a ≠ 0 ∧
      Ideal.span ({a} : Set A) = I ∧ Ideal.Quotient.mk M a = 1 := by
  constructor
  · rintro ⟨hI, a, ha, u, hu⟩
    refine ⟨a * (u⁻¹ : Aˣ), ?_, ?_, ?_⟩
    · apply mul_ne_zero
      · exact fun h ↦ hI (ha ▸ (Ideal.span_singleton_eq_bot.mpr h))
      · exact Units.ne_zero _
    · rw [Ideal.span_singleton_mul_right_unit (u⁻¹).isUnit, ha]
    · rw [map_mul, ← hu, ← map_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, map_one]
  · rintro ⟨a, ha, hI, hq⟩
    refine ⟨?_, a, hI, 1, ?_⟩
    · exact fun h ↦ ha (Ideal.span_singleton_eq_bot.mp (hI.trans h))
    · simpa only [Units.val_one, map_one] using hq.symm

theorem norm_idealCharacter_le_one (χ : rayCharacters M) (I : Ideal A) :
    ‖idealCharacter M χ I‖ ≤ 1 := IdealCharacter.norm_ofResidue_le_one M χ _ I

theorem idealCharacter_one (I : Ideal A) :
    idealCharacter M 1 I =
      if I = ⊥ then 0 else if IsCoprime I M then 1 else 0 :=
  IdealCharacter.ofResidue_one M I

theorem sum_idealCharacters (I : Ideal A) :
    ∑ χ : rayCharacters M, idealCharacter M χ I =
      if I ∈ principalIdeals M then (rayCard M : ℂ) else 0 := by
  by_cases hI : I = ⊥
  · subst I
    simp [idealCharacter, principalIdeals]
  · have heq (χ : rayCharacters M) : idealCharacter M χ I =
        (χ : MulChar (A ⧸ M) ℂ) (Ideal.Quotient.mk M (Submodule.IsPrincipal.generator I)) := by
      exact IdealCharacter.ofResidue_of_generator M χ _ hI (Ideal.span_singleton_generator I)
    simp only [heq, sum_rayCharacters, principalIdeals_iff_generator M hI]

theorem average_idealCharacters (I : Ideal A) :
    (∑ χ : rayCharacters M, idealCharacter M χ I) / (rayCard M : ℂ) =
      if I ∈ principalIdeals M then 1 else 0 := by
  rw [sum_idealCharacters]
  have hn : (rayCard M : ℂ) ≠ 0 := by exact_mod_cast (rayCard_pos M).ne'
  split_ifs <;> simp [hn]

end PrincipalIdeals
end Residues

end
end SevenEighths.RayOrthogonality

end OAI
end OAIOriginalModule0228

/-! Original module: OAI.NumberTheory.DirichletL.RayQuotient
Source SHA256: 250f6013c7423bbfaf24bc4e6b7d5a3b99a10b48115c0d5f05eb5e4a3cd6af14
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0229


namespace OAI

namespace SevenEighths.RayQuotient
open SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section

variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]
    (H : Subgroup (A ⧸ M)ˣ) (hH : globalUnits M ≤ H)

abbrev Characters := characters H
abbrev classNumber := Nat.card ((A ⧸ M)ˣ ⧸ H)

theorem classNumber_pos : 0 < classNumber M H := ray_card_pos H

include hH

theorem character_unitInvariant (χ : Characters M H) :
    IdealCharacter.UnitInvariant M χ := by
  intro u
  exact (mem_characters_iff H χ).mp χ.property _ (hH ⟨u, rfl⟩)

def toFullRay : Characters M H →* rayCharacters M where
  toFun χ := ⟨χ, (mem_rayCharacters_iff M χ).mpr (character_unitInvariant M H hH χ)⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem toFullRay_injective : Function.Injective (toFullRay M H hH) := by
  intro χ ψ heq
  exact Subtype.ext (congrArg (fun ρ : rayCharacters M => (ρ : MulChar (A ⧸ M) ℂ)) heq)

@[simp] theorem toFullRay_eq_one (χ : Characters M H) :
    toFullRay M H hH χ = 1 ↔ χ = 1 := by
  rw [← map_one (toFullRay M H hH)]
  exact (toFullRay_injective M H hH).eq_iff

variable [IsDomain A] [IsPrincipalIdealRing A]

def idealCharacter (χ : Characters M H) : Ideal A →*₀ ℂ :=
  IdealCharacter.ofResidue M χ (character_unitInvariant M H hH χ)

theorem idealCharacter_eq_fullRay (χ : Characters M H) :
    idealCharacter M H hH χ = RayOrthogonality.idealCharacter M (toFullRay M H hH χ) := rfl

def identityClass : Set (Ideal A) :=
  {I | I ≠ ⊥ ∧ ∃ a : A, Ideal.span ({a} : Set A) = I ∧
    inUnitSubgroup H (Ideal.Quotient.mk M a)}

omit [Finite (A ⧸ M)] in
theorem identityClass_iff_generator {I : Ideal A} (hI : I ≠ ⊥) :
    I ∈ identityClass M H ↔
      inUnitSubgroup H (Ideal.Quotient.mk M (Submodule.IsPrincipal.generator I)) := by
  constructor
  · rintro ⟨_, a, ha, u, hua, huH⟩
    have hga : Associated (Submodule.IsPrincipal.generator I) a := by
      rw [← ha]
      exact Submodule.IsPrincipal.associated_generator_span_self a
    obtain ⟨v, hv⟩ := hga
    let w := Units.map (Ideal.Quotient.mk M).toMonoidHom v
    refine ⟨u * w⁻¹, ?_, H.mul_mem huH (H.inv_mem (hH ⟨v, rfl⟩))⟩
    have hq := congrArg (Ideal.Quotient.mk M) hv
    simp only [map_mul] at hq
    change (u : A ⧸ M) * ((Units.map (Ideal.Quotient.mk M).toMonoidHom v)⁻¹ :
      (A ⧸ M)ˣ) = _
    rw [hua, ← hq]
    change (Ideal.Quotient.mk M (Submodule.IsPrincipal.generator I)) *
      (w : A ⧸ M) * (w⁻¹ : (A ⧸ M)ˣ) = _
    rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  · intro h
    exact ⟨hI, _, Ideal.span_singleton_generator I, h⟩

theorem norm_idealCharacter_le_one (χ : Characters M H) (I : Ideal A) :
    ‖idealCharacter M H hH χ I‖ ≤ 1 :=
  IdealCharacter.norm_ofResidue_le_one M χ _ I

theorem idealCharacter_one (I : Ideal A) :
    idealCharacter M H hH 1 I =
      if I = ⊥ then 0 else if IsCoprime I M then 1 else 0 :=
  IdealCharacter.ofResidue_one M I

theorem sum_idealCharacters (I : Ideal A) :
    ∑ χ : Characters M H, idealCharacter M H hH χ I =
      if I ∈ identityClass M H then (classNumber M H : ℂ) else 0 := by
  by_cases hI : I = ⊥
  · subst I
    simp [idealCharacter, identityClass]
  · have heq (χ : Characters M H) : idealCharacter M H hH χ I =
        (χ : MulChar (A ⧸ M) ℂ) (Ideal.Quotient.mk M (Submodule.IsPrincipal.generator I)) := by
      exact IdealCharacter.ofResidue_of_generator M χ _ hI (Ideal.span_singleton_generator I)
    simp only [heq, sum_characters, identityClass_iff_generator M H hH hI, classNumber]

theorem average_idealCharacters (I : Ideal A) :
    (∑ χ : Characters M H, idealCharacter M H hH χ I) / (classNumber M H : ℂ) =
      if I ∈ identityClass M H then 1 else 0 := by
  rw [sum_idealCharacters]
  have hn : (classNumber M H : ℂ) ≠ 0 := by exact_mod_cast (classNumber_pos M H).ne'
  split_ifs <;> simp [hn]

omit [Finite (A ⧸ M)] [IsPrincipalIdealRing A] [IsDomain A] hH in
theorem identityClass_globalUnits : identityClass M (globalUnits M) = principalIdeals M := by
  ext I
  simp only [identityClass, principalIdeals, Set.mem_ofPred_eq,
    inUnitSubgroup_globalUnits_iff]

end
end SevenEighths.RayQuotient

end OAI
end OAIOriginalModule0229

/-! Original module: OAI.NumberTheory.DirichletL.RowCompletion.SupportBounds
Source SHA256: e6ddea5d982cef3e63fc651ebc5508878b1c3bb9485dbf89c64894efa2ba5663
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0230


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

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight

theorem localRowValue_zero_of_mem (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) (hx : x∈P) :
    localRowValue x P = 0 := by
  unfold localRowValue
  split_ifs with h
  · let : P.IsMaximal := h.1
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact MulChar.map_nonunit _ (not_isUnit_zero)
  · rfl

theorem idealRowHom_zero_of_dvd (x : ActualEisensteinCubic.O) {P I : Ideal ActualEisensteinCubic.O}
    (hP : Prime P) (hPI : P∣I) (hx : x∈P) : idealRowHom x I = 0 := by
  obtain ⟨J,rfl⟩ := hPI
  rw [map_mul]
  have hz : idealRowHom x P = 0 := by
    rw [idealRowHom,primeValueHom_prime _ P hP,localRowValue_zero_of_mem x P hx]
  rw [hz,zero_mul]

theorem columnWeight_zero_of_mask (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) {P I : Ideal ActualEisensteinCubic.O}
    (hP : Prime P) (hPI : P∣I) (hm : m∈P) :
    columnWeight (rowTwist Ψ m f z) I = 0 := by
  unfold columnWeight
  have hx : m^6*f^4*z∈P := by
    have hm6 : m^6∈P := by
      rw [show m^6=m^5*m by ring]
      exact P.mul_mem_left (m^5) hm
    exact P.mul_mem_right z (P.mul_mem_right (f^4) hm6)
  by_cases hg : primaryGenerator I=0
  · rw [hg]
    change squarefreeGaussCoefficient I * (Ψ 0 * idealRowHom _ (Ideal.span {0})) = 0
    rw [Ideal.span_singleton_zero]
    change squarefreeGaussCoefficient I * (Ψ 0 * idealRowHom _ (0:Ideal ActualEisensteinCubic.O)) = 0
    rw [map_zero (idealRowHom _),mul_zero,mul_zero]
  · change squarefreeGaussCoefficient I *
      (Ψ (primaryGenerator I) * idealRowHom _ (Ideal.span {primaryGenerator I})) = 0
    rw [(primaryGenerator_spec I hg).1,idealRowHom_zero_of_dvd _ hP hPI hx,mul_zero,mul_zero]

theorem columnWeight_zero_of_not_squarefree (Ψ : ActualEisensteinCubic.O →* ℂ) {I : Ideal ActualEisensteinCubic.O}
    (hI : ¬Squarefree I) : columnWeight Ψ I = 0 := by
  simp [columnWeight,squarefreeGaussCoefficient,hI]

theorem weighted_column_support (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (hm : ∀P∈S,m∈P)
    (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X≤D)
    {I : Ideal ActualEisensteinCubic.O}
    (hn : columnWeight (rowTwist Ψ m f z) I * W ((Ideal.absNorm I:ℝ)/X) ≠ 0) :
    I∈InitialMeanSquare.outsideSquarefreeIdeals S D := by
  have hc : columnWeight (rowTwist Ψ m f z) I ≠ 0 :=
    fun h=>hn (by rw [h,zero_mul])
  have hwindow : W ((Ideal.absNorm I:ℝ)/X) ≠ 0 :=
    fun h=>hn (by rw [h,mul_zero])
  have hI : I≠0 := fun h=>hc (by rw [h,columnWeight_zero])
  have hsf : Squarefree I := by
    by_contra h
    exact hc (columnWeight_zero_of_not_squarefree _ h)
  apply Finset.mem_filter.mpr
  refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,?_,?_⟩,hsf⟩
  · exact Nat.one_le_iff_ne_zero.mpr (fun h=>hI (Ideal.absNorm_eq_zero_iff.mp h))
  · exact_mod_cast ((div_le_iff₀ hX).mp (hW _ hwindow)).trans hD
  · intro P hP hPI
    exact hc (columnWeight_zero_of_mask Ψ m f z (hSp P hP) hPI (hm P hP))

theorem weighted_column_tsum_eq (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (hm : ∀P∈S,m∈P)
    (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X≤D) :
    (∑'I:Ideal ActualEisensteinCubic.O,columnWeight (rowTwist Ψ m f z) I * W ((Ideal.absNorm I:ℝ)/X)) =
      ∑I∈InitialMeanSquare.outsideSquarefreeIdeals S D,
        columnWeight (rowTwist Ψ m f z) I * W ((Ideal.absNorm I:ℝ)/X) := by
  apply tsum_eq_sum
  intro I hI
  by_contra hn
  exact hI (weighted_column_support S D hSp Ψ m f z hm W b X hX hW hD hn)

end

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open FirstPassCubeLabels hiding O

theorem localRowValue_mul (a b : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) :
    localRowValue (a*b) P = localRowValue a P * localRowValue b P := by
  unfold localRowValue
  split_ifs with h
  · let : P.IsMaximal := h.1
    simp only [map_mul]
  · simp

theorem idealRowHom_argument_mul (a b : ActualEisensteinCubic.O) (I : Ideal ActualEisensteinCubic.O) :
    idealRowHom (a*b) I = idealRowHom a I * idealRowHom b I := by
  by_cases hI : I=0
  · rw [hI,map_zero,map_zero,map_zero,zero_mul]
  change (if I=0 then 0 else _) = (if I=0 then 0 else _) * (if I=0 then 0 else _)
  simp only [ite_eq_right hI]
  have hprod (s : Multiset (Ideal ActualEisensteinCubic.O)) :
      (s.map (localRowValue (a*b))).prod =
        (s.map (localRowValue a)).prod * (s.map (localRowValue b)).prod := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons P s ih =>
      simp only [Multiset.map_cons,Multiset.prod_cons]
      rw [localRowValue_mul,ih]
      ring
  exact hprod _

theorem rowTwist_row_factor (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z n : ActualEisensteinCubic.O) :
    rowTwist Ψ m f z n =
      rowTwist Ψ m f 1 n * idealRowHom z (Ideal.span {n}) := by
  change Ψ n * idealRowHom (m^6*f^4*z) (Ideal.span {n}) =
    (Ψ n * idealRowHom (m^6*f^4*1) (Ideal.span {n})) * idealRowHom z (Ideal.span {n})
  rw [mul_one,idealRowHom_argument_mul]
  ring

theorem cubeWeight_row_factor (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (B : Ideal ActualEisensteinCubic.O) :
    cubeWeight (rowTwist Ψ m f z) B =
      cubeWeight (rowTwist Ψ m f 1) B * idealRowHom z B^3 := by
  by_cases hB : primaryGenerator B=0
  · have hzero (x:ActualEisensteinCubic.O) : rowTwist Ψ m f x (primaryGenerator B) = 0 := by
      rw [hB]
      change Ψ 0 * idealRowHom _ (Ideal.span {(0:ActualEisensteinCubic.O)}) = 0
      rw [Ideal.span_singleton_zero]
      change Ψ 0 * idealRowHom _ (0:Ideal ActualEisensteinCubic.O) = 0
      rw [map_zero (idealRowHom _),mul_zero]
    change _ * rowTwist Ψ m f z (primaryGenerator B)^3 / _ =
      (_ * rowTwist Ψ m f 1 (primaryGenerator B)^3 / _) * _
    rw [hzero z,hzero 1]
    simp
  · change _ * rowTwist Ψ m f z (primaryGenerator B)^3 / _ =
      (_ * rowTwist Ψ m f 1 (primaryGenerator B)^3 / _) * _
    rw [rowTwist_row_factor,(primaryGenerator_spec B hB).1,mul_pow]
    ring

theorem idealRowHom_prime_powers {ι : Type*} (P : ι → Ideal ActualEisensteinCubic.O)
    [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (pool : Finset ι)
    (v : ι → ℕ) (z : ActualEisensteinCubic.O) :
    idealRowHom z (∏i∈pool,(P i)^v i) = multiplicityRow P hg pool v z := by
  rw [map_prod]
  simp only [map_pow,multiplicityRow]
  apply Finset.prod_congr rfl
  intro i hi
  rw [idealRowHom_prime z (P i) (hg i)]

theorem cubeWeight_prime_powers {ι : Type*} (P : ι → Ideal ActualEisensteinCubic.O)
    [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (pool : Finset ι)
    (v : ι → ℕ) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) :
    cubeWeight (rowTwist Ψ m f z) (∏i∈pool,(P i)^v i) =
      cubeWeight (rowTwist Ψ m f 1) (∏i∈pool,(P i)^v i) *
        multiplicityRow P hg pool v z^3 := by
  rw [cubeWeight_row_factor,idealRowHom_prime_powers P hg pool v z]

end

section
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O

def excludedGenerator (S : Finset (Ideal ActualEisensteinCubic.O)) : ActualEisensteinCubic.O := idealGenerator (∏P∈S,P)

theorem excludedGenerator_mem (S : Finset (Ideal ActualEisensteinCubic.O)) {P : Ideal ActualEisensteinCubic.O} (hP : P∈S) :
    excludedGenerator S∈P := by
  have hdiv : P∣∏Q∈S,Q := Finset.dvd_prod_of_mem (fun Q:Ideal ActualEisensteinCubic.O=>Q) hP
  have hm : idealGenerator (∏Q∈S,Q)∈Ideal.span {idealGenerator (∏Q∈S,Q)} :=
    Ideal.subset_span (by simp)
  rw [span_idealGenerator] at hm
  exact (Ideal.dvd_iff_le.mp hdiv) hm

theorem excludedGenerator_not_mem_pool (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P)
    (i : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)) :
    excludedGenerator S∉i.val := by
  intro hm
  have hprime : Prime i.val := Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
  have hspan : Ideal.span {excludedGenerator S} ≤ i.val :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
  change Ideal.span {idealGenerator (∏Q∈S,Q)} ≤ i.val at hspan
  rw [span_idealGenerator] at hspan
  have hdiv : i.val∣∏Q∈S,Q := Ideal.dvd_iff_le.mpr hspan
  obtain ⟨P,hPS,hPi⟩ := (hprime.dvd_finsetProd_iff (fun Q:Ideal ActualEisensteinCubic.O=>Q)).mp hdiv
  have heq : i.val=P := (prime_dvd_prime_iff_eq hprime (hSp P hPS)).mp hPi
  obtain ⟨I,hI,hfactor⟩ := mem_primePool_iff.mp i.property
  have ho : I∈outsideIdealsUpTo S D := (Finset.mem_filter.mp hI).1
  have hd : i.val∣I := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hfactor
  exact (mem_outsideIdealsUpTo.mp ho).2.2 P hPS (heq ▸ hd)

theorem outside_pool_fixed_mask (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (T : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D))) :
    rowCoprimeMask (fun i=>Ideal.span {poolPrimary (InitialMeanSquare.outsideSquarefreeIdeals S D) i})
      T (excludedGenerator S) = 1 := by
  unfold rowCoprimeMask
  rw [ite_eq_right]
  rintro ⟨i,hi,hmem⟩
  change excludedGenerator S ∈ Ideal.span {poolPrimary (InitialMeanSquare.outsideSquarefreeIdeals S D) i} at hmem
  rw [poolPrimary_span _ (InitialMeanSquare.outsideSquarefree_admissible S D hbad)] at hmem
  exact excludedGenerator_not_mem_pool S D hSp i hmem

theorem canonicalSourceCoefficient_fixed_mask {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i}) (Ψ : ActualEisensteinCubic.O →* ℂ) (m c f : ActualEisensteinCubic.O)
    (H : Finset ι → ℂ) (T : Finset ι)
    (hc : rowCoprimeMask (fun i=>Ideal.span {p i}) T c=1) :
    canonicalSourceCoefficient p hp hcop hg Ψ (m*c) f H T =
      canonicalSourceCoefficient p hp hcop hg Ψ m f H T := by
  simp only [canonicalSourceCoefficient,FirstPassCubeLabels.mask_mul _ hg,hc,mul_one]

end

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O

def outsideCanonicalRow (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i]; infer_instance
  fixedChildRow (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
    (poolPrimary_good F hF) Finset.univ Ψ m
    (fun T=>W (primeProductNorm (poolPrimary F) T/X)) f z

theorem outsideCanonicalRow_eq_global (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D) :
    outsideCanonicalRow S D hbad Ψ m f z W X =
      ∑'I:Ideal ActualEisensteinCubic.O,columnWeight (rowTwist Ψ (m*excludedGenerator S) f z) I *
        W ((Ideal.absNorm I:ℝ)/X) := by
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i]; infer_instance
  symm
  rw [weighted_column_tsum_eq S D hSp Ψ (m*excludedGenerator S) f z
    (fun P hP=>P.mul_mem_left m (excludedGenerator_mem S hP)) W b X hX hW hD]
  have he := selected_column_sum F hF Ψ (m*excludedGenerator S) f z (fun n=>W (n/X))
  dsimp only at he
  rw [he]
  unfold outsideCanonicalRow fixedChildRow
  dsimp only
  apply Finset.sum_congr rfl
  intro T hT
  rw [canonicalSourceCoefficient_fixed_mask _ _ _ _ Ψ m (excludedGenerator S) f _ T
    (outside_pool_fixed_mask S D hbad hSp T)]
  have ht := InitialMeanSquare.selectedIdealTest_outside S D hbad hSp W b X hX hW hD T
  simp only [canonicalSourceCoefficient,secondChildColumn]
  rw [ht]
  ring

theorem outsideCanonicalRow_cube_inverse (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (b X : ℝ) (hX : 0<X) (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D) :
    (Real.sqrt X:ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      ∑'H:Ideal ActualEisensteinCubic.O,(UniqueFactorizationMonoid.moebius H:ℂ)*
        cubeWeight (rowTwist Ψ (m*excludedGenerator S) f z) H *
        completedT (rowTwist Ψ (m*excludedGenerator S) f z) W
          (X/(Ideal.absNorm H:ℝ)^3) := by
  rw [outsideCanonicalRow_eq_global S D hbad hSp Ψ m f z W b X hX hW hD]
  exact completed_cube_inverse _ W hWc X hX

theorem outsideCanonicalRow_cube_split (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D) :
    (Real.sqrt X:ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀ +
      ∑'I:Ideal ActualEisensteinCubic.O,∑'B:Ideal ActualEisensteinCubic.O,largeCubeCoefficient H₀ B *
        summand (rowTwist Ψ (m*excludedGenerator S) f z) W X I B := by
  rw [outsideCanonicalRow_eq_global S D hbad hSp Ψ m f z W b X hX hW hD]
  exact completed_cube_inverse_split _ W hWc X H₀ hX

end

open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open CompletedGauss hiding O

def cubeIndex (F : Finset (Ideal ActualEisensteinCubic.O)) (B : Ideal ActualEisensteinCubic.O) : primePool F →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i=>(UniqueFactorizationMonoid.normalizedFactors B).count i.val)

@[simp] theorem cubeIndex_apply (F : Finset (Ideal ActualEisensteinCubic.O)) (B : Ideal ActualEisensteinCubic.O) (i : primePool F) :
    cubeIndex F B i = (UniqueFactorizationMonoid.normalizedFactors B).count i.val := by
  simp [cubeIndex]

def cubeIdeal (F : Finset (Ideal ActualEisensteinCubic.O)) (v : primePool F →₀ ℕ) : Ideal ActualEisensteinCubic.O :=
  ∏i:primePool F,i.val^v i

theorem cubeIdeal_cubeIndex (F : Finset (Ideal ActualEisensteinCubic.O)) (B : Ideal ActualEisensteinCubic.O) (hB : B≠0)
    (hcover : ∀P∈UniqueFactorizationMonoid.normalizedFactors B,P∈primePool F) :
    cubeIdeal F (cubeIndex F B) = B := by
  have hsub : (UniqueFactorizationMonoid.normalizedFactors B).toFinset ⊆ primePool F := by
    intro P hP
    exact hcover P (Multiset.mem_toFinset.mp hP)
  calc
    _ = ∏P∈primePool F,P^(UniqueFactorizationMonoid.normalizedFactors B).count P := by
      simp only [cubeIdeal,cubeIndex_apply]
      exact Finset.prod_coe_sort (s := primePool F)
        (f := fun P:Ideal ActualEisensteinCubic.O=>P^(UniqueFactorizationMonoid.normalizedFactors B).count P)
    _ = (UniqueFactorizationMonoid.normalizedFactors B).prod :=
      (Finset.prod_multiset_count_of_subset _ _ hsub).symm
    _ = B := Ideal.prod_normalizedFactors_eq_self hB

theorem cubeIndex_inj (F : Finset (Ideal ActualEisensteinCubic.O)) (B C : Ideal ActualEisensteinCubic.O) (hB : B≠0) (hC : C≠0)
    (hb : ∀P∈UniqueFactorizationMonoid.normalizedFactors B,P∈primePool F)
    (hc : ∀P∈UniqueFactorizationMonoid.normalizedFactors C,P∈primePool F)
    (heq : cubeIndex F B = cubeIndex F C) : B=C := by
  have he := congrArg (cubeIdeal F) heq
  rwa [cubeIdeal_cubeIndex F B hB hb,cubeIdeal_cubeIndex F C hC hc] at he

theorem outside_cubeIdeal_cubeIndex (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    {B : Ideal ActualEisensteinCubic.O} (hB : B∈outsideIdealsUpTo S D) :
    cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D)
      (cubeIndex (InitialMeanSquare.outsideSquarefreeIdeals S D) B) = B := by
  exact cubeIdeal_cubeIndex _ B (outsideIdealsUpTo_ne_bot S D B hB)
    (InitialMeanSquare.outside_factors_mem_pool S D hB)

theorem sum_outside_cubeIndex (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (a : Ideal ActualEisensteinCubic.O → ℂ) :
    (∑B∈outsideIdealsUpTo S D,a B) =
      ∑v∈(outsideIdealsUpTo S D).image (cubeIndex (InitialMeanSquare.outsideSquarefreeIdeals S D)),
        a (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) := by
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro B hB
    rw [outside_cubeIdeal_cubeIndex S D hB]
  · intro B hB C hC he
    exact cubeIndex_inj _ B C (outsideIdealsUpTo_ne_bot S D B hB)
      (outsideIdealsUpTo_ne_bot S D C hC)
      (InitialMeanSquare.outside_factors_mem_pool S D hB)
      (InitialMeanSquare.outside_factors_mem_pool S D hC) he

theorem cubeIdeal_ne_zero (F : Finset (Ideal ActualEisensteinCubic.O)) (v : primePool F →₀ ℕ) :
    cubeIdeal F v ≠ 0 := by
  unfold cubeIdeal
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>pow_ne_zero _ (NeZero.ne i.val))

theorem cubeIdeal_primaryGenerator (F : Finset (Ideal ActualEisensteinCubic.O))
    (v : primePool F →₀ ℕ) :
    primaryGenerator (cubeIdeal F v) =
      FirstPassCubeLabels.primeProduct (poolPrimary F) Finset.univ v := by
  change primaryGeneratorHom (∏i:primePool F,i.val^v i) = _
  rw [map_prod]
  simp only [map_pow]
  unfold FirstPassCubeLabels.primeProduct
  apply Finset.prod_congr rfl
  intro i hi
  change primaryGenerator i.val^v i = poolPrimary F i^v i
  rw [←primaryPrime_eq_primaryGenerator i.val]
  rfl

end CanonicalRowCompletion

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic

theorem densityChildEnergy_canonical_terminal
    {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hc : ∀ i,ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ₁ Ψ₂ : ActualEisensteinCubic.O →* ℂ)
    (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : ActualEisensteinCubic.O) (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (V₁ V₂ : ℝ → ℂ)
    (X F K A M : ℝ) (J : ℕ) (hX : 0 < X) (hF : 1 ≤ F) (hK : 1 ≤ K)
    (hKF : K ≤ F) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hV₁ : ∀ s,‖V₁ s‖ ≤ M) (hV₂ : ∀ s,‖V₂ s‖ ≤ M)
    (hVs₁ : ∀ s,V₁ s ≠ 0 → |s| ≤ A) (hVs₂ : ∀ s,V₂ s ≠ 0 → |s| ≤ A)
    (hT : ∀ z∈T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ F ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) :
    densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J) ≤
      globalTerminalConstant A M*(X*F)^2 := by
  have hXF : 0 < X*F := mul_pos hX (zero_lt_one.trans_le hF)
  have he := childDensity_elementary_all_scales p hp hcop hg hc hinj pool Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m T V₁ V₂ X F K A M J hX hF hK hA hM hV₁ hV₂ hVs₁ hVs₂ hT
  change _ ≤ globalTerminalConstant A M*K*X at he
  have hc0 := globalTerminalConstant_nonneg A M
  have he' : densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J)/(X*F) ≤
      globalTerminalConstant A M*(X*F) := by
    calc
      _ ≤ globalTerminalConstant A M*K*X := he
      _ ≤ globalTerminalConstant A M*F*X :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKF hc0) hX.le
      _ = globalTerminalConstant A M*(X*F) := by ring
  convert (div_le_iff₀ hXF).mp he' using 1 ; ring

end SecondPassIntegration

open scoped BigOperators Classical
open MeasureTheory
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct primeProductNorm firstLogDensity)
open SecondPassIntegration (densityChildEnergy)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter crossCoeff)

section
variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O)
  [∀i,(Ideal.span {p i}).IsMaximal]

def globalQuantitativeSource (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
    (K ell B F M H U : ℝ) (side : Bool) : Finset (GlobalSecondData ι) :=
  globalFirstSupportedPool p pool
    ((globalFirstFamilySet pool blocks).filter
      (fun b => primeProductNorm p b.common ≤ U ∧ primeProductNorm p b.firstCommon ≤ U))
    (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side

theorem globalQuantitativeSource_block_mem (pool : Finset ι)
    (blocks : Finset (GlobalCubeBlock ι)) (K ell B F M H U : ℝ) (side : Bool)
    (x : GlobalSecondData ι) (hx : x∈globalQuantitativeSource p pool blocks K ell B F M H U side) :
    x.first.block∈blocks := by
  have hx' := (mem_globalFirstExpansionPool pool _ _ x).mp (Finset.mem_filter.mp hx).1
  exact ((mem_globalFirstFamilySet pool blocks x.first).mp (Finset.mem_filter.mp hx'.1).1).1

theorem globalQuantitativeSource_frequency_ne_zero (pool : Finset ι)
    (blocks : Finset (GlobalCubeBlock ι)) (K ell B F M H U : ℝ) (side : Bool)
    (x : GlobalSecondData ι) (hx : x∈globalQuantitativeSource p pool blocks K ell B F M H U side) :
    x.source.frequency ≠ 0 :=
  globalFirstSupportedPool_frequency_ne_zero p pool _ _ ell M side x hx

end

theorem globalFirstRayChildBudget_canonical_bound (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) :
    ∃ Clo Chi : ℝ,0<Clo ∧ 0<Chi ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (side : Bool)
      (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (windows : Fin 7 → ℝ → ℂ)
      (C Γ E K ell B F M H U Z θ A₀ Vmax : ℝ) (N J : ℕ),
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
       densityChildEnergy p hp hcop hg pool (secondRayMinus Ψmode ray) (secondRayPlus Ψmode ray)
         (fixedTripleMask m q) (globalArithmeticTargets p source side q j) (windows 5) (windows 6)
         (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (2*J) ≤
         E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2) →
      globalFirstRayChildBudget p hp hcop hg pool blocks Ψ m windows C Γ ε K ell B F M H U (N+1) (2*J) side ≤
        (∫t : ℝ,firstLogDensity 0 t)*(512*(512*32))*Γ*C*globalRayTripleConstant*
          ((ell*B^3)*F)*U^(deltaLoss+8*ε)*
          (E*Clo+globalTerminalConstant A₀ Vmax*K*Chi/Z^(θ*N)) := by
  obtain ⟨Clo,Chi,hClo,hChi,hbound⟩ := globalChildBudget_canonical_bound deltaLoss hδ ε hε
  refine ⟨Clo,Chi,hClo,hChi,?_⟩
  intro ι _ p hp _ hcop hg hc hinj pool blocks side Ψ m windows C Γ E K ell B F M H U Z θ A₀ Vmax N J
    hC hΓ hE hU hK hell hB hF hH hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂ hΨ hb₁ hb₂ he
  let source := globalQuantitativeSource p pool blocks K ell B F M H U side
  let Q := (∫t : ℝ,firstLogDensity 0 t)*Γ*C*globalRayTripleConstant*((ell*B^3)*F)*
    U^(deltaLoss+8*ε)*(E*Clo+globalTerminalConstant A₀ Vmax*K*Chi/Z^(θ*N))
  have hI : 0≤∫t : ℝ,firstLogDensity 0 t :=
    integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hQ : 0≤Q := by
    have ht := globalTerminalConstant_nonneg A₀ Vmax
    have hB0 := zero_lt_one.trans_le hB
    have hF0 := zero_lt_one.trans_le hF
    dsimp [Q]
    unfold globalRayTripleConstant
    positivity
  have hrow (a : RayCharacter×RayCharacter) (r : FirstCoreIndex) :
      (∫t : ℝ,firstLogDensity 0 t)*globalChildBudget p hp hcop hg pool source
        (firstCoreTwist side (if side then a.1 else a.2) Ψ r) m windows (Γ*firstCoreUniformWeight r*C)
        ε 0 0 K ell B F M H (N+1) (2*J) side ≤ firstCoreUniformWeight r*Q := by
    have hcoeff : 0≤Γ*firstCoreUniformWeight r*C := by
      unfold firstCoreUniformWeight
      positivity
    have hk : ∀x∈source,x.source.frequency≠0 :=
      fun x hx => globalQuantitativeSource_frequency_ne_zero p pool blocks K ell B F M H U side x hx
    have hb₁' : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B :=
      fun x hx => hb₁ x.first.block (globalQuantitativeSource_block_mem p pool blocks K ell B F M H U side x hx)
    have hb₂' : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B :=
      fun x hx => hb₂ x.first.block (globalQuantitativeSource_block_mem p pool blocks K ell B F M H U side x hx)
    have hr := hbound p hp hcop hg hc hinj pool source side
      (firstCoreTwist side (if side then a.1 else a.2) Ψ r) m windows (Γ*firstCoreUniformWeight r*C)
      E K ell B F M H U Z θ A₀ Vmax N J hcoeff hE hU hK hell hB hF hH
      hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂
      (fun u => (firstCoreTwist_norm_le side (if side then a.1 else a.2) Ψ r u).trans (hΨ u))
      hk hb₁' hb₂' (he a r)
    exact (mul_le_mul_of_nonneg_left hr hI).trans_eq (by dsimp [Q]; ring)
  have hmass : (∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖)≤512 := by
    simpa only [Fintype.sum_prod_type] using RayFourExpansion.crossCoeff_sum_norm_le
  calc
    _ ≤ ∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖*
        ∑r : FirstCoreIndex,firstCoreUniformWeight r*Q :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun r _ => hrow a r)) (norm_nonneg _))
    _ = (∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖)*
        (∑r : FirstCoreIndex,firstCoreUniformWeight r)*Q := by
      simp only [←Finset.sum_mul,mul_assoc]
    _ ≤ (512*(512*32))*Q :=
      mul_le_mul_of_nonneg_right (mul_le_mul hmass firstCoreUniformWeight_mass
        (Finset.sum_nonneg (fun r _ => by unfold firstCoreUniformWeight; positivity)) (by norm_num)) hQ
    _ = _ := by dsimp [Q]; ring

theorem globalFirstQuantitativeBudget_canonical_bound (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) :
    ∃ Clo Chi : ℝ,0<Clo ∧ 0<Chi ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (side : Bool)
      (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (windows : Fin 7 → ℝ → ℂ)
      (C Cd Ct Γ E K ell B F M H U Z θ A₀ Vmax : ℝ) (N J Ntail : ℕ),
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
       densityChildEnergy p hp hcop hg pool (secondRayMinus Ψmode ray) (secondRayPlus Ψmode ray)
         (fixedTripleMask m q) (globalArithmeticTargets p source side q j) (windows 5) (windows 6)
         (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (2*J) ≤
         E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2) →
      globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ m windows
        C Cd Ct Γ ε K ell B F M H U (N+1) (2*J) Ntail side ≤
        (∫t : ℝ,firstLogDensity 0 t)*(512*(512*32))*Γ*((ell*B^3)*F)*
          ((B*U)^ε*(Cd+Ct*globalFirstTailFactor K ell B F U H Ntail)+
           C*globalRayTripleConstant*U^(deltaLoss+8*ε)*
             (E*Clo+globalTerminalConstant A₀ Vmax*K*Chi/Z^(θ*N))) := by
  obtain ⟨Clo,Chi,hClo,hChi,hbound⟩ := globalFirstRayChildBudget_canonical_bound deltaLoss hδ ε hε
  refine ⟨Clo,Chi,hClo,hChi,?_⟩
  intro ι _ p hp _ hcop hg hc hinj pool blocks side Ψ m windows C Cd Ct Γ E K ell B F M H U Z θ A₀ Vmax N J Ntail
    hC hΓ hE hU hK hell hB hF hH hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂ hΨ hb₁ hb₂ he
  have hr := hbound p hp hcop hg hc hinj pool blocks side Ψ m windows C Γ E K ell B F M H U Z θ A₀ Vmax N J
    hC hΓ hE hU hK hell hB hF hH hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂ hΨ hb₁ hb₂ he
  unfold globalFirstQuantitativeBudget
  calc
    _ ≤ (∫t : ℝ,firstLogDensity 0 t)*(512*(512*32))*Γ*(ell*B^3*F)*(B*U)^ε*
          (Cd+Ct*globalFirstTailFactor K ell B F U H Ntail)+
        (∫t : ℝ,firstLogDensity 0 t)*(512*(512*32))*Γ*C*globalRayTripleConstant*
          ((ell*B^3)*F)*U^(deltaLoss+8*ε)*
          (E*Clo+globalTerminalConstant A₀ Vmax*K*Chi/Z^(θ*N)) := add_le_add le_rfl hr
    _ = _ := by ring

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0230

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.LogSeparation
Source SHA256: 7ba99b6b53ffcc4a40c9a6315875df7e06441ea350781152fd94c30749551bf8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0231



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

namespace CanonicalCubeSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open FourierBridge JointLogSeparation

lemma cube_log_bin (B n : ℝ) (hB : 0 < B) (hn : B ≤ n)
    (hn' : n ≤ Real.exp 1 * B) : Real.log (n/B) ∈ Set.Icc (0:ℝ) 1 := by
  have hn0 : 0 < n := lt_of_lt_of_le hB hn
  constructor
  · exact Real.log_nonneg ((le_div_iff₀ hB).mpr (by simpa using hn))
  · have hh : n/B ≤ Real.exp 1 := (div_le_iff₀ hB).mpr hn'
    have := Real.log_le_log (div_pos hn0 hB) hh
    simpa only [Real.log_exp] using this

lemma cube_log_argument (B ell n q : ℝ) (hB : 0 < B) (hell : 0 < ell)
    (hn : 0 < n) (hq : 0 < q) :
    Real.exp (Real.log (q/ell) + 3*Real.log (n/B)) = q*n^3/(B^3*ell) := by
  rw [Real.exp_add, Real.exp_log (div_pos hq hell)]
  have he : Real.exp (3*Real.log (n/B)) = (n/B)^3 := by
    rw [show (3:ℝ)*Real.log (n/B) =
      Real.log (n/B)+Real.log (n/B)+Real.log (n/B) by ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_log (div_pos hn hB)]
    ring
  rw [he]
  field_simp

lemma cube_half_normalization (B ell n : ℝ) (hB : 0 < B) (hell : 0 < ell)
    (hn : 0 < n) :
    (Real.sqrt (B^3*ell))⁻¹ * Real.sqrt n =
      (B*Real.sqrt ell)⁻¹ * Real.exp (Real.log (n/B)/2) := by
  have hb0 := (Real.sqrt_pos.mpr hB).ne'
  have he0 := (Real.sqrt_pos.mpr hell).ne'
  have hs : Real.sqrt (B^3*ell) = B*Real.sqrt B*Real.sqrt ell := by
    rw [show B^3*ell=B^2*(B*ell) by ring,
      Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB.le, Real.sqrt_mul hB.le]
    ring
  have hnexp : Real.exp (Real.log (n/B)/2) = Real.sqrt n/Real.sqrt B := by
    rw [← sqrt_exp_half, Real.exp_log (div_pos hn hB), Real.sqrt_div hn.le]
  rw [hs, hnexp]
  field_simp

lemma cube_half_normalization_complex (B ell n : ℝ) (hB : 0 < B) (hell : 0 < ell)
    (hn : 0 < n) :
    (Real.sqrt (B^3*ell) : ℂ)⁻¹ * (Real.sqrt n : ℂ) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * (Real.exp (Real.log (n/B)/2) : ℂ) := by
  exact_mod_cast cube_half_normalization B ell n hB hell hn

theorem reopening_norm_separation (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (B ell X n q : ℝ) (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : B ≤ n) (hn' : n ≤ Real.exp 1*B) (hq : 0 < q) :
    (Real.sqrt X : ℂ)⁻¹ * (Real.sqrt n : ℂ) * W (q*n^3/X) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
        ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
          cubeFrequencyFactor (Real.log (n/B)) ξ * frequencyTwist V ξ (Real.log (q/ell)) := by
  have hn0 : 0 < n := lt_of_lt_of_le hB hn
  have hsep := reopening_separation_with_window W a b ha hs hW V hV
    (Real.log (n/B)) (Real.log (q/ell)) (cube_log_bin B n hB hn hn')
  rw [cube_log_argument B ell n q hB hell hn0 hq] at hsep
  rw [hX, cube_half_normalization_complex B ell n hB hell hn0, mul_assoc, hsep]

lemma completed_cube_half_weight (X n : ℝ) (hX : 0 < X) (hn : 0 < n) :
    n⁻¹ * (Real.sqrt (X/n^3))⁻¹ = (Real.sqrt X)⁻¹ * Real.sqrt n := by
  have hs : Real.sqrt (n^3) = n*Real.sqrt n := by
    rw [show n^3=n^2*n by ring, Real.sqrt_mul (sq_nonneg n), Real.sqrt_sq hn.le]
  rw [Real.sqrt_div hX.le, hs, inv_div]
  field_simp

lemma completed_cube_half_weight_complex (X n : ℝ) (hX : 0 < X) (hn : 0 < n) :
    (n : ℂ)⁻¹ * (Real.sqrt (X/n^3) : ℂ)⁻¹ =
      (Real.sqrt X : ℂ)⁻¹ * (Real.sqrt n : ℂ) := by
  exact_mod_cast completed_cube_half_weight X n hX hn

theorem completed_cube_norm_separation (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (B ell X n q : ℝ) (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : B ≤ n) (hn' : n ≤ Real.exp 1*B) (hq : 0 < q) :
    (n : ℂ)⁻¹ * (Real.sqrt (X/n^3) : ℂ)⁻¹ * W (q/(X/n^3)) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
        ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
          cubeFrequencyFactor (Real.log (n/B)) ξ * frequencyTwist V ξ (Real.log (q/ell)) := by
  have hXp : 0 < X := hX ▸ mul_pos (pow_pos hB _) hell
  rw [completed_cube_half_weight_complex X n hXp (lt_of_lt_of_le hB hn), div_div_eq_mul_div]
  exact reopening_norm_separation W a b ha hs hW V hV B ell X n q hB hell hX hn hn' hq

def separatedCubeCoefficient {κ : Type*} (β : κ → ℂ) (n : κ → ℝ)
    (B ξ : ℝ) (v : κ) : ℂ := β v * cubeFrequencyFactor (Real.log (n v/B)) ξ

lemma separatedCubeCoefficient_bound {κ : Type*} (β : κ → ℂ) (n : κ → ℝ)
    (B ξ Γ : ℝ) (hB : 0 < B) (hΓ : 0 ≤ Γ) (v : κ)
    (hn : B ≤ n v) (hn' : n v ≤ Real.exp 1*B) (hβ : ‖β v‖ ≤ Γ) :
    ‖separatedCubeCoefficient β n B ξ v‖ ≤ Γ*Real.exp (1/2) := by
  unfold separatedCubeCoefficient
  rw [norm_mul]
  exact mul_le_mul hβ (cubeFrequencyFactor_bound _ ξ (cube_log_bin B _ hB hn hn').2)
    (norm_nonneg _) hΓ

theorem reopening_finite_sum_integrable {κ τ : Type*}
    (Q : Finset κ) (S : Finset τ) (β : κ → ℂ) (A : κ → τ → ℂ)
    (n : κ → ℝ) (q : τ → ℝ) (B ell : ℝ) (b V : 𝓢(ℝ,ℂ)) :
    Integrable (fun ξ : ℝ => b ξ * ∑v∈Q,∑j∈S,
      separatedCubeCoefficient β n B ξ v * A v j * frequencyTwist V ξ (Real.log (q j/ell))) := by
  have hi : Integrable (fun ξ : ℝ => ∑v∈Q,∑j∈S,
      (β v*A v j)*(b ξ*cubeFrequencyFactor (Real.log (n v/B)) ξ*
        frequencyTwist V ξ (Real.log (q j/ell)))) := by
    apply integrable_finsetSum
    intro v hv
    apply integrable_finsetSum
    intro j hj
    exact (reopening_integrable b V _ _).const_mul _
  convert hi using 1
  funext ξ
  simp only [Finset.mul_sum, separatedCubeCoefficient]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem reopening_finite_sum {κ τ : Type*}
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (Q : Finset κ) (S : Finset τ) (β : κ → ℂ) (A : κ → τ → ℂ)
    (n : κ → ℝ) (q : τ → ℝ) (B ell X : ℝ)
    (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : ∀v∈Q,B ≤ n v) (hn' : ∀v∈Q,n v ≤ Real.exp 1*B)
    (hq : ∀j∈S,0 < q j) :
    (∑v∈Q,∑j∈S, (β v*A v j)*
      ((n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹ * W (q j/(X/(n v)^3)))) =
    ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
      ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ * ∑v∈Q,∑j∈S,
        separatedCubeCoefficient β n B ξ v * A v j *
          frequencyTwist V ξ (Real.log (q j/ell)) := by
  let G : ℝ → κ → τ → ℂ := fun ξ v j => (β v*A v j)*
    (reopeningCoefficient W a b ha hs hW ξ * cubeFrequencyFactor (Real.log (n v/B)) ξ *
      frequencyTwist V ξ (Real.log (q j/ell)))
  have hi (v : κ) (j : τ) : Integrable (fun ξ => G ξ v j) :=
    (reopening_integrable _ V _ _).const_mul _
  have hterm (v : κ) (hv : v∈Q) (j : τ) (hj : j∈S) :
      (β v*A v j)*((n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹ * W (q j/(X/(n v)^3))) =
        ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∫ ξ : ℝ,G ξ v j := by
    rw [completed_cube_norm_separation W a b ha hs hW V hV B ell X (n v) (q j)
      hB hell hX (hn v hv) (hn' v hv) (hq j hj)]
    rw [show (∫ ξ : ℝ,G ξ v j) = (β v*A v j)*∫ ξ : ℝ,
        reopeningCoefficient W a b ha hs hW ξ * cubeFrequencyFactor (Real.log (n v/B)) ξ *
          frequencyTwist V ξ (Real.log (q j/ell)) from integral_const_mul _ _]
    ring
  calc
    _ = ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∑v∈Q,∑j∈S,∫ ξ : ℝ,G ξ v j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j hj => hterm v hv j hj)
    _ = ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∫ ξ : ℝ,∑v∈Q,∑j∈S,G ξ v j := by
      congr 1
      rw [integral_finsetSum _ (fun v hv => integrable_finsetSum _ (fun j hj => hi v j))]
      apply Finset.sum_congr rfl
      intro v hv
      exact (integral_finsetSum _ (fun j hj => hi v j)).symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp only [Finset.mul_sum, separatedCubeCoefficient]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [G]
      ring

end CanonicalCubeSeparation

open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight

theorem rowTwist_primary_zero_of_mask (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) {P B : Ideal ActualEisensteinCubic.O}
    (hP : Prime P) (hPB : P∣B) (hm : m∈P) :
    rowTwist Ψ m f z (primaryGenerator B) = 0 := by
  have hx : m^6*f^4*z∈P := by
    have hm6 : m^6∈P := by
      rw [show m^6=m^5*m by ring]
      exact P.mul_mem_left (m^5) hm
    exact P.mul_mem_right z (P.mul_mem_right (f^4) hm6)
  by_cases hg : primaryGenerator B=0
  · rw [hg]
    change Ψ 0 * idealRowHom _ (Ideal.span {(0:ActualEisensteinCubic.O)}) = 0
    rw [Ideal.span_singleton_zero]
    change Ψ 0 * idealRowHom _ (0:Ideal ActualEisensteinCubic.O) = 0
    rw [map_zero (idealRowHom _),mul_zero]
  · change Ψ (primaryGenerator B) * idealRowHom _ (Ideal.span {primaryGenerator B}) = 0
    rw [(primaryGenerator_spec B hg).1,idealRowHom_zero_of_dvd _ hP hPB hx,mul_zero]

theorem cubeWeight_zero_of_prime_mask (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) {P B : Ideal ActualEisensteinCubic.O}
    (hP : Prime P) (hPB : P∣B) (hm : m∈P) :
    cubeWeight (rowTwist Ψ m f z) B = 0 :=
  cubeWeight_zero_of_mask _ B (rowTwist_primary_zero_of_mask Ψ m f z hP hPB hm)

theorem summand_cube_support (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (hm : ∀P∈S,m∈P)
    (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D)
    (I B : Ideal ActualEisensteinCubic.O) (hn : summand (rowTwist Ψ m f z) W X I B≠0) :
    B∈outsideIdealsUpTo S D := by
  have hI : I≠0 := fun h=>hn (by rw [h,summand_zero_left])
  have hB : B≠0 := fun h=>hn (by rw [h,summand_zero_right])
  have hw : W ((Ideal.absNorm I:ℝ)*(Ideal.absNorm B:ℝ)^3/X)≠0 :=
    fun h=>hn (summand_zero_window _ W X I B h)
  have hsize := (div_le_iff₀ hX).mp (hW _ hw)
  have hb := (triple_scale_bounds (Ideal.absNorm I:ℝ) (Ideal.absNorm B:ℝ) 1
    (norm_at_least_one I hI) (norm_at_least_one B hB) (by norm_num)).2.1
  simp only [one_pow,mul_one] at hb
  apply mem_outsideIdealsUpTo.mpr
  refine ⟨?_,?_,?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (fun h=>hB (Ideal.absNorm_eq_zero_iff.mp h))
  · exact_mod_cast (hb.trans hsize).trans hD
  · intro P hP hPB
    have hz := cubeWeight_zero_of_prime_mask Ψ m f z (hSp P hP) hPB (hm P hP)
    exact hn (by simp only [summand,hz,mul_zero,zero_mul])

theorem large_cube_sum_comm (Ψ : ActualEisensteinCubic.O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0<X) :
    (∑'I:Ideal ActualEisensteinCubic.O,∑'B:Ideal ActualEisensteinCubic.O,largeCubeCoefficient H₀ B*summand Ψ W X I B) =
      ∑'B:Ideal ActualEisensteinCubic.O,∑'I:Ideal ActualEisensteinCubic.O,largeCubeCoefficient H₀ B*summand Ψ W X I B := by
  let a : Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O → ℂ := fun p=>largeCubeCoefficient H₀ p.2*summand Ψ W X p.1 p.2
  have hf : (Function.support a).Finite :=
    (completedT_finite_support Ψ W hW X hX).subset (by
      intro p hp
      exact fun h=>hp (by simp only [a,h,mul_zero]))
  have hs : Summable a := summable_of_hasFiniteSupport hf
  let e := Equiv.prodComm (Ideal ActualEisensteinCubic.O) (Ideal ActualEisensteinCubic.O)
  have ht : Summable (fun p=>a (e p)) := e.summable_iff.mpr hs
  calc
    _ = ∑'p:Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O,a p := hs.tsum_prod.symm
    _ = ∑'p:Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O,a (e p) := (e.tsum_eq a).symm
    _ = _ := ht.tsum_prod

theorem large_cube_sum_finite (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (hm : ∀P∈S,m∈P)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D) :
    (∑'I:Ideal ActualEisensteinCubic.O,∑'B:Ideal ActualEisensteinCubic.O,largeCubeCoefficient H₀ B*summand (rowTwist Ψ m f z) W X I B) =
      ∑B∈outsideIdealsUpTo S D,largeCubeCoefficient H₀ B*
        ∑'I:Ideal ActualEisensteinCubic.O,summand (rowTwist Ψ m f z) W X I B := by
  rw [large_cube_sum_comm _ W hWc X H₀ hX]
  simp only [tsum_mul_left]
  apply tsum_eq_sum
  intro B hB
  have hz : ∀I:Ideal ActualEisensteinCubic.O,summand (rowTwist Ψ m f z) W X I B=0 := by
    intro I
    by_contra hn
    exact hB (summand_cube_support S D hSp Ψ m f z hm W b X hX hW hD I B hn)
  simp only [hz,tsum_zero,mul_zero]

open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O

theorem inner_completed_sum (Ψ : ActualEisensteinCubic.O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (hX : 0<X)
    (B : Ideal ActualEisensteinCubic.O) (hB : B≠0) :
    (∑'I:Ideal ActualEisensteinCubic.O,summand Ψ W X I B) =
      (cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) *
        ∑'I:Ideal ActualEisensteinCubic.O,columnWeight Ψ I * W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3)) := by
  have hN : 0 < (Ideal.absNorm B:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one B hB)
  have hY : 0 < X/(Ideal.absNorm B:ℝ)^3 := div_pos hX (pow_pos hN _)
  have ht (I:Ideal ActualEisensteinCubic.O) : summand Ψ W X I B =
      (cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) *
        (columnWeight Ψ I * W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))) := by
    have harg : (Ideal.absNorm I:ℝ)*(Ideal.absNorm B:ℝ)^3/X =
        (Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3) := by
      rw [div_div_eq_mul_div]
    have hn := vstar_source_normalization Ψ W (X/(Ideal.absNorm B:ℝ)^3) hY I
    calc
      _ = cubeWeight Ψ B * (columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I:ℝ):ℂ) *
          Vstar W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))) := by
        rw [summand,harg]
        ring
      _ = _ := by rw [hn]; ring
  simp_rw [ht]
  exact tsum_mul_left

theorem outsideCanonicalRow_reopened (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hb : 0 ≤ b) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D) :
    (Real.sqrt X:ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀ +
      ∑B∈outsideIdealsUpTo S D,
        (largeCubeCoefficient H₀ B * cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) B *
          (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) * idealRowHom z B^3 *
          outsideCanonicalRow S D hbad Ψ m f z W (X/(Ideal.absNorm B:ℝ)^3) := by
  rw [outsideCanonicalRow_cube_split S D hbad hSp Ψ m f z W hWc b X H₀ hX hW hD]
  rw [large_cube_sum_finite S D hSp Ψ (m*excludedGenerator S) f z
    (fun P hP=>P.mul_mem_left m (excludedGenerator_mem S hP)) W hWc b X H₀ hX hW hD]
  congr 1
  apply Finset.sum_congr rfl
  intro B hB
  have hB0 : B≠0 := outsideIdealsUpTo_ne_bot S D B hB
  have hN := norm_at_least_one B hB0
  have hY : 0 < X/(Ideal.absNorm B:ℝ)^3 := by positivity
  have hYX : X/(Ideal.absNorm B:ℝ)^3 ≤ X :=
    div_le_self hX.le (one_le_pow₀ hN)
  have hDY : b*(X/(Ideal.absNorm B:ℝ)^3) ≤ D :=
    (mul_le_mul_of_nonneg_left hYX hb).trans hD
  rw [inner_completed_sum _ W X hX B hB0]
  rw [←outsideCanonicalRow_eq_global S D hbad hSp Ψ m f z W b
    (X/(Ideal.absNorm B:ℝ)^3) hY hW hDY]
  rw [cubeWeight_row_factor]
  ring

theorem outsideCanonicalRow_reopened_exponents (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hb : 0 ≤ b) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    (Real.sqrt X:ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀ +
      ∑v∈(outsideIdealsUpTo S D).image (cubeIndex F),
        (largeCubeCoefficient H₀ (cubeIdeal F v) *
          cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v) *
          (Real.sqrt (X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3):ℂ)⁻¹) *
          idealRowHom z (cubeIdeal F v)^3 *
          outsideCanonicalRow S D hbad Ψ m f z W (X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3) := by
  dsimp only
  rw [outsideCanonicalRow_reopened S D hbad hSp Ψ m f z W hWc b X H₀ hb hX hW hD]
  rw [sum_outside_cubeIndex S D]

end

open ActualEisensteinCubic
open CompletedGauss hiding O

theorem cubeWeight_norm_le (Ψ : ActualEisensteinCubic.O →* ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (B : Ideal ActualEisensteinCubic.O) :
    ‖cubeWeight Ψ B‖ ≤ 1/(Ideal.absNorm B:ℝ) := by
  have hang : ‖FiniteGaussPhase.angularFactor (primaryGenerator B)‖ ≤ 1 := by
    by_cases hz : primaryGenerator B=0
    · simp [hz,FiniteGaussPhase.angularFactor]
    · exact (FiniteGaussPhase.norm_angularFactor _ hz).le
  change ‖star (FiniteGaussPhase.angularFactor (primaryGenerator B))^3*
    Ψ (primaryGenerator B)^3/(Ideal.absNorm B:ℂ)‖ ≤ _
  rw [norm_div,norm_mul,norm_pow,norm_pow,norm_star,Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact (mul_le_of_le_one_left (by positivity)
    (pow_le_one₀ (norm_nonneg _) hang)).trans (pow_le_one₀ (norm_nonneg _) (hΨ _))

def cubePhase (Ψ : ActualEisensteinCubic.O →* ℂ) (B : Ideal ActualEisensteinCubic.O) : ℂ :=
  (Ideal.absNorm B:ℂ)*cubeWeight Ψ B

theorem cubePhase_norm_le (Ψ : ActualEisensteinCubic.O →* ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (B : Ideal ActualEisensteinCubic.O) :
    ‖cubePhase Ψ B‖ ≤ 1 := by
  by_cases hB : B=0
  · simp [hB,cubePhase]
  have hN : 0 < (Ideal.absNorm B:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one B hB)
  rw [cubePhase,norm_mul,Complex.norm_natCast]
  calc
    _ ≤ (Ideal.absNorm B:ℝ)*(1/(Ideal.absNorm B:ℝ)) :=
      mul_le_mul_of_nonneg_left (cubeWeight_norm_le Ψ hΨ B) hN.le
    _ = 1 := by field_simp

theorem cube_weight_scale (Ψ : ActualEisensteinCubic.O →* ℂ) (B : Ideal ActualEisensteinCubic.O) (hB : B≠0)
    (X : ℝ) (hX : 0<X) :
    cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹ =
      cubePhase Ψ B * (Real.sqrt (Ideal.absNorm B:ℝ):ℂ)/(Real.sqrt X:ℂ) := by
  have hN : 0 < (Ideal.absNorm B:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one B hB)
  have hs3 : Real.sqrt ((Ideal.absNorm B:ℝ)^3) =
      (Ideal.absNorm B:ℝ)*Real.sqrt (Ideal.absNorm B:ℝ) := by
    rw [show (Ideal.absNorm B:ℝ)^3=(Ideal.absNorm B:ℝ)^2*(Ideal.absNorm B:ℝ) by ring,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos hN]
  have hs : Real.sqrt (X/(Ideal.absNorm B:ℝ)^3) =
      Real.sqrt X/((Ideal.absNorm B:ℝ)*Real.sqrt (Ideal.absNorm B:ℝ)) := by
    rw [Real.sqrt_div hX.le,hs3]
  rw [hs,Complex.ofReal_div,Complex.ofReal_mul,cubePhase]
  push_cast
  have hNc : (Ideal.absNorm B:ℂ)≠0 := by exact_mod_cast hN.ne'
  have hsN : (Real.sqrt (Ideal.absNorm B:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hN).ne'
  have hsX : (Real.sqrt X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  field_simp

def reopenedCubeCoefficient (H₀ : ℝ) (Ψ : ActualEisensteinCubic.O →* ℂ) (B : Ideal ActualEisensteinCubic.O) : ℂ :=
  largeCubeCoefficient H₀ B * cubePhase Ψ B

theorem reopenedCubeCoefficient_small_power (ε : ℝ) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀(H₀:ℝ) (Ψ:ActualEisensteinCubic.O →* ℂ), (∀z,‖Ψ z‖≤1) →
      ∀B:Ideal ActualEisensteinCubic.O,B≠0 → ‖reopenedCubeCoefficient H₀ Ψ B‖ ≤ C*(Ideal.absNorm B:ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := largeCubeCoefficient_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro H₀ Ψ hΨ B hB
  rw [reopenedCubeCoefficient,norm_mul]
  calc
    _ ≤ ‖largeCubeCoefficient H₀ B‖*1 :=
      mul_le_mul_of_nonneg_left (cubePhase_norm_le Ψ hΨ B) (norm_nonneg _)
    _ ≤ _ := by simpa only [mul_one] using hbound H₀ B hB

theorem reopenedCubeCoefficient_support (H₀:ℝ) (Ψ:ActualEisensteinCubic.O →* ℂ) (B:Ideal ActualEisensteinCubic.O)
    (h:reopenedCubeCoefficient H₀ Ψ B≠0) : B≠0 ∧ H₀ ≤ (Ideal.absNorm B:ℝ) := by
  exact largeCubeCoefficient_support H₀ B (fun hz=>h (by simp only [reopenedCubeCoefficient,hz,zero_mul]))

end CanonicalRowCompletion

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels

def childLabelRotation (u : ActualEisensteinCubic.Oˣ) (negative : Bool) (z : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O) : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O :=
  (z.1,(u : ActualEisensteinCubic.O)^4*(if negative then -z.2 else z.2))

theorem childLabelRotation_injective (u : ActualEisensteinCubic.Oˣ) (negative : Bool) :
    Function.Injective (childLabelRotation u negative) := by
  intro z w he
  have hf := congrArg Prod.fst he
  change z.1=w.1 at hf
  have hs := congrArg Prod.snd he
  change (u : ActualEisensteinCubic.O)^4*(if negative then -z.2 else z.2)=
    (u : ActualEisensteinCubic.O)^4*(if negative then -w.2 else w.2) at hs
  have hz := mul_left_cancel₀ (pow_ne_zero 4 u.ne_zero) hs
  apply Prod.ext hf
  cases negative <;> simpa only [Bool.false_eq_true,ite_false,ite_true,neg_inj] using hz

theorem childLabelRotation_norm (u : ActualEisensteinCubic.Oˣ) (negative : Bool) (z : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O) :
    ‖eisEmbedding (childLabelRotation u negative z).2‖^2=‖eisEmbedding z.2‖^2 := by
  cases negative <;> simp only [childLabelRotation,Bool.false_eq_true,ite_false,ite_true,
    map_mul,norm_mul,map_pow,norm_pow,GaussGeneratorTransport.norm_eisEmbedding_unit,
    one_pow,one_mul,map_neg,norm_neg]

theorem childLabelRotation_ne_zero (u : ActualEisensteinCubic.Oˣ) (negative : Bool) (z : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)
    (hz : z.2≠0) : (childLabelRotation u negative z).2≠0 := by
  apply mul_ne_zero (pow_ne_zero 4 u.ne_zero)
  cases negative <;> simpa using hz

section
variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem fixedChildRow_label_mul (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (H : Finset ι → ℂ) (u f z : ActualEisensteinCubic.O) :
    fixedChildRow p hp hcop hg pool Ψ m H (u*f) z=
      fixedChildRow p hp hcop hg pool Ψ m H f (u^4*z) := by
  unfold fixedChildRow
  apply Finset.sum_congr rfl
  intro S hS
  simp only [secondChildColumn,finiteSquarefreeRow_mul,row_pow,mul_pow]
  ring

theorem idealChildRow_eq_rotated (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (H : Finset ι → ℂ) (negative : Bool) (u : ActualEisensteinCubic.Oˣ) (z : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O) :
    idealChildRow p hp hcop hg pool Ψ m H negative u z=
      fixedChildRow p hp hcop hg pool Ψ m H
        (ConcretePrimeRowBridge.idealGenerator (childLabelRotation u negative z).1)
        (childLabelRotation u negative z).2 := by
  exact fixedChildRow_label_mul p hp hcop hg pool Ψ m H (u : ActualEisensteinCubic.O) _ _

def canonicalSmoothedEnergy (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (H : Finset ι → ℂ) (K : ℝ) : ℝ :=
  (∑I∈labels,nonzeroRowMajorantSum
    (fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I)) K).re

theorem canonicalSmoothedEnergy_nonneg (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (H : Finset ι → ℂ) (K : ℝ) (hK : 0<K) :
    0≤canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels H K := by
  unfold canonicalSmoothedEnergy
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro I hI
  have he := finite_nonzero_row_energy_le_majorant
    (fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I)) ∅ K hK
    (by simp) (by simp)
  simpa using he

theorem canonicalSmoothedEnergy_zero_correction (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (H : Finset ι → ℂ) (K : ℝ) (hK : 0<K) :
    canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels H K=
      (∑I∈labels,∑'z:ActualEisensteinCubic.O,rowMajorant (‖eisEmbedding z‖^2/K)*
        (‖fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I) z‖^2:ℝ)).re-
      ∑I∈labels,‖fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I) 0‖^2 := by
  unfold canonicalSmoothedEnergy
  simp only [nonzeroRowMajorantSum_eq_sub _ K hK,Finset.sum_sub_distrib,Complex.sub_re,
    Complex.re_sum,Complex.ofReal_re]

theorem idealChildRow_energy_le_canonical (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (H : Finset ι → ℂ) (negative : Bool) (u : ActualEisensteinCubic.Oˣ)
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (labels : Finset (Ideal ActualEisensteinCubic.O)) (K : ℝ) (hK : 0<K)
    (hlabels : ∀z∈T,z.1∈labels)
    (hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K) (hzero : ∀z∈T,z.2≠0) :
    (∑z∈T,‖idealChildRow p hp hcop hg pool Ψ m H negative u z‖^2)≤
      canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels H K := by
  let f : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O → ℝ := fun z=>
    ‖fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator z.1) z.2‖^2
  let R := (firstFrequencyDisk K).erase 0
  have hsub : T.image (childLabelRotation u negative)⊆labels.product R := by
    intro w hw
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hw
    apply Finset.mem_product.mpr
    refine ⟨hlabels z hz,Finset.mem_erase.mpr ⟨childLabelRotation_ne_zero u negative z (hzero z hz),?_⟩⟩
    apply (mem_firstFrequencyDisk K _).mpr
    rw [childLabelRotation_norm]
    exact hrows z hz
  calc
    _ = ∑w∈T.image (childLabelRotation u negative),f w := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro z hz
        rw [idealChildRow_eq_rotated]
      · exact fun _ _ _ _ he=>childLabelRotation_injective u negative he
    _ ≤ ∑w∈labels.product R,f w :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>sq_nonneg _)
    _ = ∑I∈labels,∑z∈R,f (I,z) := by rw [Finset.product_eq_sprod,Finset.sum_product]
    _ ≤ ∑I∈labels,(nonzeroRowMajorantSum
        (fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I)) K).re := by
      apply Finset.sum_le_sum
      intro I hI
      apply finite_nonzero_row_energy_le_majorant _ R K hK
      · intro z hz
        rw [←eisEmbedding_norm_sq_eq_absNorm_span]
        exact (mem_firstFrequencyDisk K z).mp (Finset.mem_erase.mp hz).2
      · exact fun z hz=>(Finset.mem_erase.mp hz).1
    _ = _ := by unfold canonicalSmoothedEnergy; rw [Complex.re_sum]

def canonicalLogEnergy (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (V : ℝ → ℂ) (X K : ℝ) : ℝ :=
  canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels (fun S=>V (columnLog p X S)) K

end

def orientedLogProfile (negative : Bool) (V : ℝ → ℂ) : ℝ → ℂ :=
  if negative then fun s=>star (V s) else V

theorem fixedSecondTest_zero_profile {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O)
    (V : ℝ → ℂ) (X : ℝ) (negative : Bool) :
    fixedSecondTest p V X 0 0 negative=(fun S=>orientedLogProfile negative V (columnLog p X S)) := by
  funext S
  cases negative <;> simp [fixedSecondTest,orientedLogProfile,JointLogSeparation.fixedColumnTest,FourierBridge.logPhase]

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0231

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.CanonicalLogEnergy
Source SHA256: cc7ce1c9b23ad546f7071389ec4db70479cb5a7c22eaa81e041d9a7dbf7a94d3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0232


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

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic ConcreteTraceCRT

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem childEnergy_le_canonicalSmoothed (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (labels : Finset (Ideal ActualEisensteinCubic.O)) (V : ℝ → ℂ)
    (X K a b : ℝ) (hK : 0<K) (testNegative rowNegative : Bool)
    (hlabels : ∀z∈T,z.1∈labels)
    (hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K) (hzero : ∀z∈T,z.2≠0) :
    childEnergy p hp hcop hg pool Ψ m T V X testNegative rowNegative a b≤
      6*canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels
        (fixedSecondTest p V X a b testNegative) K := by
  apply idealChildRow_unit_energy_le
  intro u
  exact idealChildRow_energy_le_canonical p hp hcop hg pool Ψ m _ rowNegative u
    T labels K hK hlabels hrows hzero

theorem childEnergy_le_canonicalLogEnergy (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (labels : Finset (Ideal ActualEisensteinCubic.O)) (V : ℝ → ℂ)
    (X K a b : ℝ) (hX : 0<X) (hK : 0<K) (testNegative rowNegative : Bool)
    (hlabels : ∀z∈T,z.1∈labels)
    (hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K) (hzero : ∀z∈T,z.2≠0) :
    childEnergy p hp hcop hg pool Ψ m T V X testNegative rowNegative a b≤
      6*canonicalLogEnergy p hp hcop hg pool
        (normHeightTwist Ψ (secondSignedHeight testNegative a b)) m labels
        (orientedLogProfile testNegative V) X K := by
  rw [childEnergy_normHeight p hp hcop hg pool Ψ m T V X a b hX testNegative rowNegative]
  simpa only [canonicalLogEnergy,fixedSecondTest_zero_profile] using
    childEnergy_le_canonicalSmoothed p hp hcop hg pool
      (normHeightTwist Ψ (secondSignedHeight testNegative a b)) m T labels V X K 0 0 hK
      testNegative rowNegative hlabels hrows hzero

theorem childEnergy_le_canonicalLogEnergy_actual_labels (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (V : ℝ → ℂ)
    (X K a b : ℝ) (hX : 0<X) (hK : 0<K) (testNegative rowNegative : Bool)
    (hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K) (hzero : ∀z∈T,z.2≠0) :
    childEnergy p hp hcop hg pool Ψ m T V X testNegative rowNegative a b≤
      6*canonicalLogEnergy p hp hcop hg pool
        (normHeightTwist Ψ (secondSignedHeight testNegative a b)) m (T.image Prod.fst)
        (orientedLogProfile testNegative V) X K :=
  childEnergy_le_canonicalLogEnergy p hp hcop hg pool Ψ m T (T.image Prod.fst) V X K a b hX hK
    testNegative rowNegative (fun z hz=>Finset.mem_image.mpr ⟨z,hz,rfl⟩) hrows hzero

end SecondPassIntegration

namespace CanonicalRowCompletion

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

section
open ActualEisensteinCubic
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O
open CanonicalCubeSeparation JointLogSeparation

variable {ι : Type*} [DecidableEq ι]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem fixedChildRow_coefficient_expansion
    (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (H : Finset ι → ℂ) :
    fixedChildRow p hp hcop hg pool Ψ m H f z =
      ∑ T ∈ pool.powerset,
        canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) T *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z * H T := by
  unfold fixedChildRow
  apply Finset.sum_congr rfl
  intro T hT
  simp only [secondChildColumn, canonicalSourceCoefficient]
  ring

theorem reopenedCanonicalRow_integrand
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (H : Finset ι → ℂ) :
    reopenedCanonicalRow p hp hcop hg pool Q β Ψ m f H z =
      ∑ v ∈ Q, ∑ T ∈ pool.powerset,
        β v * (multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
          canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) T *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z) * H T := by
  unfold reopenedCanonicalRow
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro T hT
  simp only [canonicalSourceCoefficient]
  ring

theorem canonical_bin_separation
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (n : (ι →₀ ℕ) → ℝ) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (B ell X : ℝ)
    (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : ∀ v ∈ Q, B ≤ n v) (hn' : ∀ v ∈ Q, n v ≤ Real.exp 1*B) :
    (∑ v ∈ Q, (β v * (n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹) *
      multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
      fixedChildRow p hp hcop hg pool Ψ m
        (fun T => W (primeProductNorm p T/(X/(n v)^3))) f z) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
        ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
          reopenedCanonicalRow p hp hcop hg pool Q
            (separatedCubeCoefficient β n B ξ) Ψ m f
            (fun T => frequencyTwist V ξ (columnLog p ell T)) z := by
  let A : (ι →₀ ℕ) → Finset ι → ℂ := fun v T =>
    multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
      canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) T *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z
  have hsep := reopening_finite_sum W a b ha hs hW V hV Q pool.powerset β A n
    (primeProductNorm p) B ell X hB hell hX hn hn'
    (fun T _ => primeProductNorm_pos p hp T)
  calc
    _ = ∑ v ∈ Q, ∑ T ∈ pool.powerset, (β v * A v T) *
        ((n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹ *
          W (primeProductNorm p T/(X/(n v)^3))) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [fixedChildRow_coefficient_expansion p hp hcop hg, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      dsimp only [A]
      ring
    _ = _ := by
      rw [hsep]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [reopenedCanonicalRow_integrand p hp hcop hg]
      rfl

end

open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O
open CanonicalCubeSeparation JointLogSeparation

theorem cube_coefficient_restore (H₀ : ℝ) (Ψ : ActualEisensteinCubic.O →* ℂ) (I : Ideal ActualEisensteinCubic.O)
    (hI : I ≠ 0) :
    reopenedCubeCoefficient H₀ Ψ I * (Ideal.absNorm I : ℂ)⁻¹ =
      largeCubeCoefficient H₀ I * cubeWeight Ψ I := by
  have hN : (Ideal.absNorm I : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (norm_at_least_one I hI)))
  unfold reopenedCubeCoefficient cubePhase
  field_simp

theorem cubeIdeal_row (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀ I ∈ F, Admissible I)
    (v : primePool F →₀ ℕ) (z : ActualEisensteinCubic.O) :
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    idealRowHom z (cubeIdeal F v) =
      multiplicityRow (fun i => Ideal.span {poolPrimary F i}) (poolPrimary_good F hF)
        Finset.univ v z := by
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have hprod : cubeIdeal F v = ∏ i : primePool F, (Ideal.span {poolPrimary F i}) ^ v i := by
    unfold cubeIdeal
    exact Finset.prod_congr rfl (fun i _ => by rw [poolPrimary_span F hF i])
  rw [hprod, idealRowHom_prime_powers]

def outsideCanonicalBin (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ))
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (X H₀ : ℝ) : ℂ :=
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  ∑ v ∈ Q,
    (largeCubeCoefficient H₀ (cubeIdeal F v) *
      cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v) *
      (Real.sqrt (X/(Ideal.absNorm (cubeIdeal F v) : ℝ)^3) : ℂ)⁻¹) *
      idealRowHom z (cubeIdeal F v)^3 *
      outsideCanonicalRow S D hbad Ψ m f z W (X/(Ideal.absNorm (cubeIdeal F v) : ℝ)^3)

theorem outsideCanonicalBin_separated
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ))
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (V : 𝓢(ℝ,ℂ))
    (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (B ell X H₀ : ℝ) (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : ∀ v ∈ Q, B ≤ (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ))
    (hn' : ∀ v ∈ Q, (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*B) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let β := fun v => reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)
    let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
    outsideCanonicalBin S D hbad Q Ψ m f z W X H₀ =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
        ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
          reopenedCanonicalRow (poolPrimary F) (poolPrimary_ne_zero F hF)
            (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q
            (separatedCubeCoefficient β n B ξ) Ψ m f
            (fun T => frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z := by
  dsimp only
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  let β := fun v => reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)
  let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
  rw [← canonical_bin_separation (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) W a b ha hs hW V hV
    Finset.univ Q β n Ψ m f z B ell X hB hell hX hn hn']
  unfold outsideCanonicalBin
  dsimp only
  apply Finset.sum_congr rfl
  intro v hv
  rw [cubeIdeal_row F hF v z]
  have hc := cube_coefficient_restore H₀ (rowTwist Ψ (m*excludedGenerator S) f 1)
    (cubeIdeal F v) (cubeIdeal_ne_zero F v)
  change _ = (β v * (n v : ℂ)⁻¹ * _) * _ * _
  have hc' : β v * (n v : ℂ)⁻¹ =
      largeCubeCoefficient H₀ (cubeIdeal F v) *
        cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v) := by
    simpa only [β,n,Complex.ofReal_natCast] using hc
  rw [hc']
  rfl

end

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O

theorem fixedChildRow_zero_of_subunit {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ)
    (b X : ℝ) (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t ≤ b) (hsub : b*X < 1) :
    fixedChildRow p hp hcop hg pool Ψ m
      (fun T => W (primeProductNorm p T/X)) f z = 0 := by
  unfold fixedChildRow
  apply Finset.sum_eq_zero
  intro T hT
  have hw : W (primeProductNorm p T/X) = 0 := by
    by_contra hne
    have hh := (div_le_iff₀ hX).mp (hW _ hne)
    have hone := primeProductNorm_ge_one p hp T
    linarith
  simp only [secondChildColumn,hw,mul_zero]

theorem outsideCanonicalRow_zero_of_subunit
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ)
    (b X : ℝ) (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t ≤ b) (hsub : b*X < 1) :
    outsideCanonicalRow S D hbad Ψ m f z W X = 0 := by
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  unfold outsideCanonicalRow
  dsimp only
  exact fixedChildRow_zero_of_subunit _ _ _ _ _ Ψ m f z W b X hX hW hsub

def activeCubeExponents (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ) :
    Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ) :=
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  ((outsideIdealsUpTo S D).image (cubeIndex F)).filter
    (fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)^3 ≤ b*X)

theorem outsideCanonicalBin_eq_active
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (b X H₀ : ℝ)
    (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t ≤ b) :
    outsideCanonicalBin S D hbad
      ((outsideIdealsUpTo S D).image (cubeIndex (InitialMeanSquare.outsideSquarefreeIdeals S D)))
      Ψ m f z W X H₀ =
    outsideCanonicalBin S D hbad (activeCubeExponents S D b X) Ψ m f z W X H₀ := by
  unfold outsideCanonicalBin activeCubeExponents
  dsimp only
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro v hv hn
  have hlarge : b*X < (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ)^3 := by
    exact lt_of_not_ge (fun hh => hn (Finset.mem_filter.mpr ⟨hv,hh⟩))
  have hN : 0 < (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) :=
    lt_of_lt_of_le zero_lt_one (norm_at_least_one _ (cubeIdeal_ne_zero _ v))
  have hsub : b*(X/(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ)^3) < 1 := by
    rw [← mul_div_assoc]
    exact (div_lt_one (pow_pos hN _)).mpr hlarge
  rw [outsideCanonicalRow_zero_of_subunit S D hbad Ψ m f z W b _
    (div_pos hX (pow_pos hN _)) hW hsub,mul_zero]

theorem outsideCanonicalRow_reopened_active
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ : ℝ)
    (hb : 0 ≤ b) (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t ≤ b) (hD : b*X ≤ D) :
    (Real.sqrt X : ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀ +
        outsideCanonicalBin S D hbad (activeCubeExponents S D b X) Ψ m f z W X H₀ := by
  have hh := outsideCanonicalRow_reopened_exponents S D hbad hSp Ψ m f z W hWc b X H₀ hb hX hW hD
  change _ = _ + outsideCanonicalBin S D hbad
    ((outsideIdealsUpTo S D).image (cubeIndex (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    Ψ m f z W X H₀ at hh
  rwa [outsideCanonicalBin_eq_active S D hbad Ψ m f z W b X H₀ hX hW] at hh

theorem activeCubeExponents_norm_bound
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ)
    (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ)
    (hv : v ∈ activeCubeExponents S D b X) :
    (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ max 1 (b*X) := by
  have hcube := (Finset.mem_filter.mp hv).2
  have hN := norm_at_least_one _ (cubeIdeal_ne_zero (InitialMeanSquare.outsideSquarefreeIdeals S D) v)
  let n := (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ)
  have hone : 1 ≤ n := hN
  have hnn : n ≤ n^3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hone) (show 0 ≤ n^2+n by positivity)]
  exact (hnn.trans hcube).trans (le_max_right _ _)

end

open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O

def cubeLogIndex (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ) : ℕ :=
  normLogBin (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ)

def cubeLogRange (b X : ℝ) : Finset ℕ :=
  Finset.range (normLogBin (max 1 (b*X)) + 1)

def activeCubeLogBin (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ) (j : ℕ) :
    Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ) :=
  (activeCubeExponents S D b X).filter (fun v => cubeLogIndex S D v = j)

theorem activeCubeLogIndex_mem (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ)
    (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ)
    (hv : v ∈ activeCubeExponents S D b X) : cubeLogIndex S D v ∈ cubeLogRange b X := by
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  exact normLogBin_mono
    (lt_of_lt_of_le zero_lt_one (norm_at_least_one _ (cubeIdeal_ne_zero _ v)))
    (activeCubeExponents_norm_bound S D b X v hv)

theorem activeCubeLogBin_norms (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ) (j : ℕ)
    (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ)
    (hv : v ∈ activeCubeLogBin S D b X j) :
    normLogScale j ≤ (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ∧
    (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*normLogScale j := by
  have hj := (Finset.mem_filter.mp hv).2
  rw [← hj]
  have hh := normLogBin_scale_bounds
    (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ)
    (norm_at_least_one _ (cubeIdeal_ne_zero _ v))
  exact ⟨hh.1,by simpa only [mul_comm,cubeLogIndex] using hh.2⟩

theorem cubeLogRange_card (b X : ℝ) :
    (cubeLogRange b X).card = normLogBin (max 1 (b*X)) + 1 := by
  exact Finset.card_range _

theorem sum_activeCubeLogBins {M : Type*} [AddCommMonoid M]
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ)
    (a : (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ) → M) :
    (∑ v ∈ activeCubeExponents S D b X, a v) =
      ∑ j ∈ cubeLogRange b X, ∑ v ∈ activeCubeLogBin S D b X j, a v := by
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun v hv => activeCubeLogIndex_mem S D b X v hv) a

theorem outsideCanonicalBin_log_bins
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (b X H₀ : ℝ) :
    outsideCanonicalBin S D hbad (activeCubeExponents S D b X) Ψ m f z W X H₀ =
      ∑ j ∈ cubeLogRange b X,
        outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) Ψ m f z W X H₀ := by
  unfold outsideCanonicalBin
