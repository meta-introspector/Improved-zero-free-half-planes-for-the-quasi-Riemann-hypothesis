  intro d hd
  by_cases hc : Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z
  · simp only [hc, and_self, ite_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    have harg : (X / (Ideal.absNorm d : ℝ)) * ‖eisEmbedding h‖ ^ 2 =
        X * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ) := by ring
    rw [harg]
    push_cast
    ring
  · simp only [hc, ite_false, mul_zero, Finset.sum_const_zero]

theorem principalTruncation_eq_ideal_divisors (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (X Z : ℝ) :
    principalTruncation (fun P : primePool {G} => P.val) Finset.univ W X Z =
      (X : ℂ) * paperRadialFourier W 0 *
        (∏ P : primePool {G}, (1 - (1 : ℂ) / Ideal.absNorm P.val)) -
      (X : ℂ) * paperRadialFourier W 0 *
        (∑ d ∈ idealDivisors G, if Z < (Ideal.absNorm d : ℝ) then
          (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) else 0) -
      W 0 * (∑ d ∈ idealDivisors G, if (Ideal.absNorm d : ℝ) ≤ Z then
        (UniqueFactorizationMonoid.moebius d : ℂ) else 0) := by
  classical
  rw [← primePool_subset_sum_eq_divisors G hG
    (fun d => if Z < (Ideal.absNorm d : ℝ) then
      (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) else 0),
    ← primePool_subset_sum_eq_divisors G hG
    (fun d => if (Ideal.absNorm d : ℝ) ≤ Z then (UniqueFactorizationMonoid.moebius d : ℂ) else 0)]
  unfold principalTruncation largeDivisors smallDivisors
  simp only [Finset.sum_filter, subsetNorm, subsetMobius, Complex.ofReal_natCast]

end

open ActualEisensteinCubic

theorem finite_middle_triangle
    {m n p H D : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype H] [Fintype D]
    (muCoefficient : D → ℂ) (hμ : ∀ d, ‖muCoefficient d‖ ≤ 1) (A : m → n → p → H → D → ℂ) :
    ‖∑ i, ∑ j, ∑ k, ∑ h, ∑ d, muCoefficient d * A i j k h d‖ ≤
      ∑ h, ∑ i, ∑ d, ‖∑ j, ∑ k, A i j k h d‖ := by
  classical
  have he : (∑ i, ∑ j, ∑ k, ∑ h, ∑ d, muCoefficient d * A i j k h d) =
      ∑ h, ∑ i, ∑ d, muCoefficient d * (∑ j, ∑ k, A i j k h d) := by
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset p)) (t := (Finset.univ : Finset H)),
      Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset H)),
      Finset.sum_comm (s := (Finset.univ : Finset m)) (t := (Finset.univ : Finset H)),
      Finset.sum_comm (s := (Finset.univ : Finset p)) (t := (Finset.univ : Finset D)),
      Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset D))]
    simp only [Finset.mul_sum]
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro h hh
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hμ d)

theorem finite_nonzero_frequency_sum_le (H : Finset O) (hH : ∀ h ∈ H, h ≠ 0)
    (f : O → ℝ) (hf : ∀ h, 0 ≤ f h)
    (hs : Summable (fun h : {h : O // h ≠ 0} => f h.val)) :
    (∑ h ∈ H, f h) ≤ ∑' h : {h : O // h ≠ 0}, f h.val := by
  classical
  let e : H → {h : O // h ≠ 0} := fun h => ⟨h.val, hH h.val h.property⟩
  have he : Function.Injective e := by
    intro h k hh
    apply Subtype.ext
    exact congrArg (fun x : {h : O // h ≠ 0} => x.val) hh
  have hsH : Summable (fun h : H => f h.val) :=
    summable_of_hasFiniteSupport (Set.toFinite _)
  have hb := hsH.tsum_le_tsum_of_inj e he (fun h _ => hf h.val) (fun _ => le_rfl) hs
  rw [tsum_fintype, Finset.sum_coe_sort H f] at hb
  exact hb

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem sum_two_finite_subtypes {α β A : Type*} [AddCommMonoid A]
    (S : Finset α) (T : Finset β) (f : α → β → A) :
    (∑ a : S, ∑ b : T, f a.val b.val) = ∑ a ∈ S, ∑ b ∈ T, f a b := by
  rw [Finset.sum_coe_sort S (fun a => ∑ b : T, f a b.val)]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_coe_sort T (f a))

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalTruncatedMiddle (W : 𝓢(ℝ, ℂ))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) (Y i) (Z i) lengthScale

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem original_truncated_pair_expansion
    (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hK : ∀ j k d, d ∣ left j * right k → d ∈ K) (i : m) (j : n) (k : p) :
    originalTerm rows left right a b 1 1 i j k *
      middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
        (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) (Y i) (Z i) lengthScale =
      ∑ h : rowNormDisk ⌊lengthScale⌋₊, ∑ d : K, (UniqueFactorizationMonoid.moebius d.val : ℂ) *
        (if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
          if d.val ∣ left j * right k then
            originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h.val d.val i
          else 0 else 0) := by
  classical
  rw [sum_two_finite_subtypes (rowNormDisk ⌊lengthScale⌋₊) K (fun h d =>
    (UniqueFactorizationMonoid.moebius d : ℂ) *
      (if Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i then
        if d ∣ left j * right k then
          originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h d i
        else 0 else 0))]
  by_cases hc : IsCoprime (left j) (right k)
  · have hsq : Squarefree (left j * right k) :=
      squarefree_mul_iff.mpr ⟨hc.isRelPrime, (hleft j).2.1, (hright k).2.1⟩
    rw [middleTruncation_eq_ideal_frequencies _ hsq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    rw [← divisorPool_filter K (left j * right k) hsq.ne_zero (hK j k), Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdv : d ∣ left j * right k
    · by_cases hp : Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i
      · simp only [hdv, hp, and_self, ite_true, originalPrincipalKernel]
        ring
      · simp only [hdv, hp, ite_true, ite_false, mul_zero]
    · simp only [hdv, ite_false, ite_self, mul_zero]
  · have hz : originalTerm rows left right a b 1 1 i j k = 0 := by simp only [originalTerm, hc, ite_false]
    simp only [hz, zero_mul, ite_self, mul_zero, Finset.sum_const_zero]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalTruncatedMiddle_le_product_divisors
    (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hK : ∀ j k d, d ∣ left j * right k → d ∈ K) :
    ‖originalTruncatedMiddle W rows left right a b M Y Z lengthScale‖ ≤
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, originalProductDivisorMiddleAt W K rows left right a b M
        (fun d i => Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i) h := by
  classical
  let A : m → n → p → rowNormDisk ⌊lengthScale⌋₊ → K → ℂ := fun i j k h d =>
    if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
      if d.val ∣ left j * right k then
        originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h.val d.val i
      else 0 else 0
  have he : originalTruncatedMiddle W rows left right a b M Y Z lengthScale =
      ∑ i, ∑ j, ∑ k, ∑ h : rowNormDisk ⌊lengthScale⌋₊, ∑ d : K,
        (UniqueFactorizationMonoid.moebius d.val : ℂ) * A i j k h d := by
    unfold originalTruncatedMiddle
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    exact original_truncated_pair_expansion W K rows left right a b M Y Z lengthScale hleft hright hK i j k
  rw [he]
  apply (finite_middle_triangle (fun d : K => (UniqueFactorizationMonoid.moebius d.val : ℂ))
    (fun d => QuadraticInitialBound.norm_ideal_moebius_le_one d.val) A).trans_eq
  rw [Finset.sum_coe_sort (rowNormDisk ⌊lengthScale⌋₊) (fun h => ∑ i, ∑ d : K,
    ‖∑ j, ∑ k, if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
      if d.val ∣ left j * right k then
        originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h d.val i
      else 0 else 0‖)]
  apply Finset.sum_congr rfl
  intro h hh
  unfold originalProductDivisorMiddleAt
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_coe_sort K (fun d =>
    ‖∑ j, ∑ k, if Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i then
      if d ∣ left j * right k then
        originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h d i
      else 0 else 0‖)]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hp : Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i <;>
    simp only [hp, and_self, ite_true, ite_false, Finset.sum_const_zero, norm_zero]

theorem HasSieveExponent.original_truncated_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hZ : ∀ i, Z i ≤ U * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) :
    ‖originalTruncatedMiddle W rows left right a b M Y Z lengthScale‖ ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2))) := by
  let pairCols : n × p → Ideal O := fun x => left x.1 * right x.2
  let K := columnDivisorPool pairCols
  have hPair : ∀ x, pairCols x ≠ 0 := fun x => mul_ne_zero (hleft x.1).1.1 (hright x.2).1.1
  have hK (j : n) (k : p) (d : Ideal O) (hd : d ∣ left j * right k) : d ∈ K :=
    mem_columnDivisorPool_of_dvd pairCols hPair (j, k) d hd
  let P : Ideal O → m → Prop := fun d i =>
    Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i
  have hb := hexp.original_product_divisor_middle deltaLoss hδ ε hε K B N M U hB hN hM hU
    rows left right hr hl hri hrows a b (fun _ => a) (fun _ => b)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) W P hleft hright
    (fun d hd i hp => hp.2.trans (hZ i))
  have hH (h : O) (hh : h ∈ rowNormDisk ⌊lengthScale⌋₊) : h ≠ 0 := by
    intro hz
    have hn := (mem_rowNormDisk.mp hh).1
    simp [hz] at hn
  calc
    _ ≤ ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, originalProductDivisorMiddleAt W K rows left right a b M P h :=
      originalTruncatedMiddle_le_product_divisors W K rows left right a b M Y Z lengthScale
        (fun j => (hleft j).1) (fun k => (hright k).1) hK
    _ ≤ ∑' h : {h : O // h ≠ 0}, originalProductDivisorMiddleAt W K rows left right a b M P h.val :=
      finite_nonzero_frequency_sum_le (rowNormDisk ⌊lengthScale⌋₊) hH _
        (fun h => originalProductDivisorMiddleAt_nonneg W K rows left right a b M P h) hb.1
    _ ≤ _ := hb.2

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0157

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.SmoothCuspCutoffs
Source SHA256: 0e3447dc237d29e57d96f993939fd96411cf488e298726088256b460e379e186
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0158


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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff

def cuspTransition (a b v : ℝ) : ℝ := Real.smoothTransition ((v-a)/(b-a))

lemma cuspTransition_contDiff (a b : ℝ) : ContDiff ℝ ∞ (cuspTransition a b) := by
  unfold cuspTransition
  fun_prop

lemma cuspTransition_zero (a b v : ℝ) (hab : a<b) (hv : v≤a) : cuspTransition a b v=0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv) (sub_pos.mpr hab).le)
lemma cuspTransition_one (a b v : ℝ) (hab : a<b) (hv : b≤v) : cuspTransition a b v=1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (sub_pos.mpr hab)).mpr (by linarith))

lemma cuspTransition_derivatives (a b v : ℝ) (hab : a<b) (hv : v<a ∨ b<v) :
    deriv (cuspTransition a b) v=0 ∧ deriv (deriv (cuspTransition a b)) v=0 := by
  rcases hv with hv | hv
  · have heq : cuspTransition a b =ᶠ[𝓝 v] (fun _ => (0:ℝ)) := by
      filter_upwards [Iio_mem_nhds hv] with x hx
      exact cuspTransition_zero a b x hab hx.le
    exact ⟨heq.deriv_eq.trans (deriv_const _ _),heq.deriv.deriv_eq.trans (by simp)⟩
  · have heq : cuspTransition a b =ᶠ[𝓝 v] (fun _ => (1:ℝ)) := by
      filter_upwards [Ioi_mem_nhds hv] with x hx
      exact cuspTransition_one a b x hab hx.le
    exact ⟨heq.deriv_eq.trans (deriv_const _ _),heq.deriv.deriv_eq.trans (by simp)⟩

def positiveHeightPower (s : ℂ) (v : ℝ) : ℂ := logRatioPower s v 1
lemma positiveHeightPower_eq_cpow (s : ℂ) (v : ℝ) (hv : 0<v) :
    positiveHeightPower s v=(v:ℂ)^s := by
  simpa only [positiveHeightPower,div_one] using logRatioPower_eq_cpow s hv (by norm_num : (0:ℝ)<1)

lemma positiveHeightPower_hasDerivAt (s : ℂ) (v : ℝ) (hv : v≠0) :
    HasDerivAt (positiveHeightPower s) (positiveHeightPower s v*s/(v:ℂ)) v := by
  convert hasDerivAt_logRatioPower s (hasDerivAt_id v) (hasDerivAt_const v (1:ℝ)) hv one_ne_zero using 1
  · rfl
  · simp [positiveHeightPower,div_eq_mul_inv]

lemma positiveHeightPower_hasDerivAt_deriv (s : ℂ) (v : ℝ) (hv : v≠0) :
    HasDerivAt (deriv (positiveHeightPower s))
      (positiveHeightPower s v*s*(s-1)/(v:ℂ)^2) v := by
  convert hasDerivAt_deriv_logRatioPower s id (fun _ => 1) (fun _ => 1) (fun _ => 0) v 0 0
    (fun x => hasDerivAt_id x) (fun x => hasDerivAt_const x (1:ℝ))
    (hasDerivAt_const v (1:ℝ)) (hasDerivAt_const v (0:ℝ)) hv one_ne_zero using 1
  · rfl
  · simp only [id_eq,zero_mul,mul_one,sub_self,sub_zero,one_pow,div_one,
      Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_pow,
      Complex.ofReal_zero,positiveHeightPower]
    field_simp [Complex.ofReal_ne_zero.mpr hv]
    ; ring

def cuspSeedProfile (a b : ℝ) (s : ℂ) (v : ℝ) : ℂ :=
  (cuspTransition a b v:ℂ)*positiveHeightPower s v

lemma cuspSeedProfile_zero (a b : ℝ) (s : ℂ) (v : ℝ) (hab : a<b) (hv : v≤a) :
    cuspSeedProfile a b s v=0 := by simp [cuspSeedProfile,cuspTransition_zero a b v hab hv]
lemma cuspSeedProfile_incoming (a b : ℝ) (s : ℂ) (v : ℝ)
    (hab : a<b) (hv : b≤v) (hpos : 0<v) : cuspSeedProfile a b s v=(v:ℂ)^s := by
  simp [cuspSeedProfile,cuspTransition_one a b v hab hv,positiveHeightPower_eq_cpow s v hpos]

lemma cuspSeedProfile_hasDerivAt (a b : ℝ) (s : ℂ) (v : ℝ) (hv : v≠0) :
    HasDerivAt (cuspSeedProfile a b s)
      (((deriv (cuspTransition a b) v:ℝ):ℂ)*positiveHeightPower s v+
        (cuspTransition a b v:ℂ)*(positiveHeightPower s v*s/(v:ℂ))) v := by
  exact (((cuspTransition_contDiff a b).differentiable (by simp) v).hasDerivAt.ofReal_comp).mul
    (positiveHeightPower_hasDerivAt s v hv)

lemma cuspSeedProfile_hasDerivAt_deriv (a b : ℝ) (s : ℂ) (v : ℝ) (hv : v≠0) :
    HasDerivAt (deriv (cuspSeedProfile a b s))
      (((deriv (deriv (cuspTransition a b)) v:ℝ):ℂ)*positiveHeightPower s v+
        2*((deriv (cuspTransition a b) v:ℝ):ℂ)*(positiveHeightPower s v*s/(v:ℂ))+
        (cuspTransition a b v:ℂ)*(positiveHeightPower s v*s*(s-1)/(v:ℂ)^2)) v := by
  have hχ := ((cuspTransition_contDiff a b).differentiable (by simp) v).hasDerivAt.ofReal_comp
  have hdχ := (((contDiff_infty_iff_deriv.mp (cuspTransition_contDiff a b)).2).differentiable
    (by simp) v).hasDerivAt.ofReal_comp
  have hH := positiveHeightPower_hasDerivAt s v hv
  have hdH := positiveHeightPower_hasDerivAt_deriv s v hv
  have heq : deriv (cuspSeedProfile a b s) =ᶠ[𝓝 v]
      (fun x => ((deriv (cuspTransition a b) x:ℝ):ℂ)*positiveHeightPower s x+
        (cuspTransition a b x:ℂ)*deriv (positiveHeightPower s) x) := by
    filter_upwards [eventually_ne_nhds hv] with x hx
    rw [(cuspSeedProfile_hasDerivAt a b s x hx).deriv,(positiveHeightPower_hasDerivAt s x hx).deriv]
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  convert (hdχ.mul hH).add (hχ.mul hdH) using 1
  · rw [hH.deriv]
    ring

def cuspSeedDefectProfile (a b : ℝ) (s : ℂ) (v : ℝ) : ℂ :=
  positiveHeightPower s v*((v:ℂ)^2*((deriv (deriv (cuspTransition a b)) v:ℝ):ℂ)+
    (2*s-1)*(v:ℂ)*((deriv (cuspTransition a b) v:ℝ):ℂ))

lemma cuspSeedProfile_laplace_defect (a b : ℝ) (s : ℂ) (v : ℝ) (hv : v≠0) :
    (v:ℂ)^2*deriv (deriv (cuspSeedProfile a b s)) v-
      (v:ℂ)*deriv (cuspSeedProfile a b s) v-s*(s-2)*cuspSeedProfile a b s v=
        cuspSeedDefectProfile a b s v := by
  rw [(cuspSeedProfile_hasDerivAt a b s v hv).deriv,(cuspSeedProfile_hasDerivAt_deriv a b s v hv).deriv]
  unfold cuspSeedDefectProfile cuspSeedProfile
  field_simp [Complex.ofReal_ne_zero.mpr hv]
  ; ring

lemma cuspSeedDefectProfile_zero (a b : ℝ) (s : ℂ) (v : ℝ) (hab : a<b) (hv : v<a ∨ b<v) :
    cuspSeedDefectProfile a b s v=0 := by
  obtain ⟨h₁,h₂⟩ := cuspTransition_derivatives a b v hab hv
  simp [cuspSeedDefectProfile,h₁,h₂]

lemma cuspSeedDefectProfile_hasCompactSupport (a b : ℝ) (s : ℂ) (hab : a<b) :
    HasCompactSupport (cuspSeedDefectProfile a b s) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro v hv
  by_contra hn
  have hout : v<a ∨ b<v := by simpa only [Set.mem_Icc,not_and_or,not_le] using hn
  exact hv (cuspSeedDefectProfile_zero a b s v hab hout)

def rowHeight (u : Fin 2 → ℂ) (p : SpatialCoordinates) : ℝ :=
  p 2 / quadraticHeightDenominator (Complex.normSq (u 0)) (u 0*star (u 1)).re
    (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) (p 0) (p 1) (p 2)

lemma rowHeight_pos (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    0<rowHeight u p := div_pos hp (row_denominator_pos u hu p hp)
lemma rowHeight_eq_transformedHeight (u : Fin 2 → ℂ) (p : SpatialCoordinates) :
    rowHeight u p=transformedHeight ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) u := by
  rw [transformedHeight,heightDenominator_eq_quadratic]
  rfl
lemma cosetHeight_upperPoint_rowHeight (r : CuspCosets) (p : SpatialCoordinates) (hp : 0<p 2) :
    cosetHeight r (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp)=rowHeight (embeddedRow r) p := by
  change (rowEnergy (rowOperator (upperSection ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp) (embeddedRow r)))⁻¹=_
  rw [rowEnergy_upperSection,inv_div,heightDenominator_eq_quadratic]
  rfl

lemma rowHeight_contDiffAt (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (rowHeight u) p := by
  have hq : ContDiffAt ℝ ∞
      (fun q : SpatialCoordinates => quadraticHeightDenominator (Complex.normSq (u 0))
        (u 0*star (u 1)).re (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) (q 0) (q 1) (q 2)) p := by
    unfold quadraticHeightDenominator
    fun_prop
  exact (show ContDiffAt ℝ ∞ (fun q : SpatialCoordinates => q 2) p by fun_prop).div hq
    (row_denominator_pos u hu p hp).ne'

lemma rowSmoothPower_eq_height (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) : rowSmoothPower s u p=(rowHeight u p:ℂ)^s :=
  logRatioPower_eq_cpow s hp (row_denominator_pos u hu p hp)

lemma norm_smoothSummand_three (r : CuspCosets) (p : SpatialCoordinates) (hp : 0<p 2) :
    ‖smoothSummand 3 r p‖=(rowHeight (embeddedRow r) p)^3 := by
  rw [smoothSummand,rowSmoothPower_eq_height 3 _ (embeddedRow_ne_zero r) p hp,norm_mul,norm_inv,
    norm_cosetCharacter,inv_one,one_mul]
  rw [show (3:ℂ)=(3:ℕ) by norm_num,Complex.cpow_natCast,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (rowHeight_pos _ (embeddedRow_ne_zero r) p hp)]

lemma locally_finite_high_rows (p : SpatialCoordinates) (hp : 0<p 2) :
    ∃U : Set SpatialCoordinates, IsOpen U ∧ p∈U ∧ ∃S : Finset CuspCosets,
      ∀q∈U, 0<q 2 ∧ ∀r∉S,rowHeight (embeddedRow r) q<1 := by
  obtain ⟨U,hU,hpU,M₀,M₁,M₂,hM₀,hM₁,hM₂,hbound⟩ :=
    spatial_summable_derivative_bounds 3 (by norm_num) p hp
  have hevent : ∀ᶠr in Filter.cofinite,M₀ r<1 :=
    hM₀.tendsto_cofinite_zero.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  have hfinite : Set.Finite {r | ¬M₀ r<1} := Filter.eventually_cofinite.mp hevent
  refine ⟨U,hU,hpU,hfinite.toFinset,?_⟩
  intro q hq
  refine ⟨(hbound q hq).1,?_⟩
  intro r hr
  have hrM : M₀ r<1 := by simpa only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq,not_not] using hr
  have hnorm := ((hbound q hq).2 r).1
  rw [norm_smoothSummand_three r q (hbound q hq).1] at hnorm
  have hpos := (rowHeight_pos _ (embeddedRow_ne_zero r) q (hbound q hq).1).le
  nlinarith [sq_nonneg (rowHeight (embeddedRow r) q-1)]

def heightPoincareField (F : ℝ → ℂ) (p : SpatialCoordinates) : ℂ :=
  ∑'r : CuspCosets,(cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) p)

lemma heightPoincareField_locally_finite (F : ℝ → ℂ) (hF : ∀v≤1,F v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ∃S : Finset CuspCosets, heightPoincareField F =ᶠ[𝓝 p]
      (fun q => ∑r∈S,(cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) q)) := by
  obtain ⟨U,hU,hpU,S,hrows⟩ := locally_finite_high_rows p hp
  refine ⟨S,?_⟩
  filter_upwards [hU.mem_nhds hpU] with q hq
  apply tsum_eq_sum
  intro r hr
  rw [hF _ ((hrows q hq).2 r hr).le,mul_zero]

lemma heightPoincareField_contDiffAt (F : ℝ → ℂ) (hzero : ∀v≤1,F v=0)
    (hF : ∀v,0<v→ContDiffAt ℝ ∞ F v) (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (heightPoincareField F) p := by
  obtain ⟨S,hS⟩ := heightPoincareField_locally_finite F hzero p hp
  apply ContDiffAt.congr_of_eventuallyEq _ hS
  apply ContDiffAt.sum
  intro r hr
  exact contDiffAt_const.mul ((hF _ (rowHeight_pos _ (embeddedRow_ne_zero r) p hp)).comp p
    (rowHeight_contDiffAt _ (embeddedRow_ne_zero r) p hp))

lemma heightPoincareField_eq_cuspCorrection (F : ℝ → ℂ) (hzero : ∀v≤1,F v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    heightPoincareField F p=cuspCutoffCorrection 1 F
      (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp) := by
  unfold heightPoincareField cuspCutoffCorrection
  apply tsum_congr
  intro r
  rw [cuspCutoffTerm,cosetHeight_upperPoint_rowHeight]
  split_ifs with h
  · rfl
  · rw [hzero _ (le_of_not_gt h),mul_zero]

open CubicKubota

lemma positiveHeightPower_contDiffAt (s : ℂ) (v : ℝ) (hv : v≠0) :
    ContDiffAt ℝ ∞ (positiveHeightPower s) v := by
  have hlog : ContDiffAt ℝ ∞ (fun x : ℝ => (Real.log x:ℂ)) v :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp v (Real.contDiffAt_log.mpr hv)
  have hs : ContDiffAt ℝ ∞ (fun x : ℝ => s*(Real.log x:ℂ)) v := contDiffAt_const.mul hlog
  unfold positiveHeightPower logRatioPower
  simpa only [Real.log_one,sub_zero] using hs.cexp

lemma cuspSeedProfile_contDiffAt (a b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) :
    ContDiffAt ℝ ∞ (cuspSeedProfile a b s) v :=
  (Complex.ofRealCLM.contDiff.contDiffAt.comp v (cuspTransition_contDiff a b).contDiffAt).mul
    (positiveHeightPower_contDiffAt s v hv.ne')

lemma cuspSeedDefectProfile_contDiffAt (a b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) :
    ContDiffAt ℝ ∞ (cuspSeedDefectProfile a b s) v := by
  have hχ₁ : ContDiff ℝ ∞ (deriv (cuspTransition a b)) :=
    (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff a b)).2
  have hχ₂ : ContDiff ℝ ∞ (deriv (deriv (cuspTransition a b))) :=
    (contDiff_infty_iff_deriv.mp hχ₁).2
  have hd₁ := Complex.ofRealCLM.contDiff.contDiffAt.comp v hχ₁.contDiffAt
  have hd₂ := Complex.ofRealCLM.contDiff.contDiffAt.comp v hχ₂.contDiffAt
  have hid : ContDiffAt ℝ ∞ (fun x : ℝ => (x:ℂ)) v := Complex.ofRealCLM.contDiff.contDiffAt
  exact (positiveHeightPower_contDiffAt s v hv.ne').mul
    (((hid.pow 2).mul hd₂).add ((contDiffAt_const.mul hid).mul hd₁))

lemma cuspSeedDefectProfile_continuous (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    Continuous (cuspSeedDefectProfile a b s) := by
  rw [continuous_iff_continuousAt]
  intro v
  by_cases hv : v<a
  · have heq : cuspSeedDefectProfile a b s =ᶠ[𝓝 v] (fun _ => (0:ℂ)) := by
      filter_upwards [Iio_mem_nhds hv] with x hx
      exact cuspSeedDefectProfile_zero a b s x hab (Or.inl hx)
    exact continuousAt_const.congr heq.symm
  · exact (cuspSeedDefectProfile_contDiffAt a b s v (lt_of_lt_of_le ha (le_of_not_gt hv))).continuousAt

lemma cuspSeedDefectProfile_integrable (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    Integrable (cuspSeedDefectProfile a b s) volume :=
  (cuspSeedDefectProfile_continuous a b s ha hab).integrable_of_hasCompactSupport
    (cuspSeedDefectProfile_hasCompactSupport a b s hab)

def smoothCuspSeed (a b : ℝ) (s : ℂ) : HyperbolicSpace → ℂ :=
  cuspCutoffCorrection 1 (cuspSeedProfile a b s)

def smoothCuspSeedDefect (a b : ℝ) (s : ℂ) : HyperbolicSpace → ℂ :=
  cuspCutoffCorrection 1 (cuspSeedDefectProfile a b s)

lemma smoothCuspSeed_automorphy (a b : ℝ) (s : ℂ) (M : levelThree) (w : HyperbolicSpace) :
    smoothCuspSeed a b s (complexMatrix M • w)=complexCharacter M*smoothCuspSeed a b s w :=
  cuspCutoffCorrection_automorphy 1 le_rfl _ M w
lemma smoothCuspSeedDefect_automorphy (a b : ℝ) (s : ℂ) (M : levelThree) (w : HyperbolicSpace) :
    smoothCuspSeedDefect a b s (complexMatrix M • w)=complexCharacter M*smoothCuspSeedDefect a b s w :=
  cuspCutoffCorrection_automorphy 1 le_rfl _ M w

lemma smoothCuspSeed_coordinate (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    smoothCuspSeed a b s (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp)=
      heightPoincareField (cuspSeedProfile a b s) p :=
  (heightPoincareField_eq_cuspCorrection _
    (fun v hv => cuspSeedProfile_zero a b s v hab (hv.trans ha.le)) p hp).symm
lemma smoothCuspSeedDefect_coordinate (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    smoothCuspSeedDefect a b s (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp)=
      heightPoincareField (cuspSeedDefectProfile a b s) p :=
  (heightPoincareField_eq_cuspCorrection _
    (fun v hv => cuspSeedDefectProfile_zero a b s v hab (Or.inl (lt_of_le_of_lt hv ha))) p hp).symm

lemma smoothCuspSeed_contDiffAt (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (heightPoincareField (cuspSeedProfile a b s)) p :=
  heightPoincareField_contDiffAt _ (fun v hv => cuspSeedProfile_zero a b s v hab (hv.trans ha.le))
    (cuspSeedProfile_contDiffAt a b s) p hp
lemma smoothCuspSeedDefect_contDiffAt (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (heightPoincareField (cuspSeedDefectProfile a b s)) p :=
  heightPoincareField_contDiffAt _
    (fun v hv => cuspSeedDefectProfile_zero a b s v hab (Or.inl (lt_of_le_of_lt hv ha)))
    (cuspSeedDefectProfile_contDiffAt a b s) p hp

lemma cuspCutoffCorrection_upperPoint (F : ℝ → ℂ) (z : ℂ) (v : ℝ) (hv : 0<v) (h1v : 1<v) :
    cuspCutoffCorrection 1 F (upperPoint z v hv)=F v := by
  have hh : cosetHeight (cosetOf 1) (upperPoint z v hv)=v := by
    rw [cosetHeight_cosetOf,map_one,one_smul,hyperbolicHeight_upperPoint]
  rw [cuspCutoffCorrection_eq 1 le_rfl _ _ (cosetOf 1) (hh.symm ▸ h1v),hh,
    cosetCharacter_cosetOf,map_one,inv_one,one_mul]

lemma smoothCuspSeed_incoming (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (z : ℂ) (v : ℝ) (hv : 0<v) (hbv : b≤v) :
    smoothCuspSeed a b s (upperPoint z v hv)=(v:ℂ)^s := by
  rw [smoothCuspSeed,cuspCutoffCorrection_upperPoint _ z v hv (lt_of_lt_of_le (ha.trans hab) hbv)]
  exact cuspSeedProfile_incoming a b s v hab hbv hv

lemma smoothCuspSeedDefect_support (a b : ℝ) (s : ℂ) (hab : a<b) (w : HyperbolicSpace)
    (hw : smoothCuspSeedDefect a b s w≠0) :
    ∃r : CuspCosets, a≤cosetHeight r w ∧ cosetHeight r w≤b := by
  by_contra hn
  apply hw
  unfold smoothCuspSeedDefect cuspCutoffCorrection
  calc
    _ = ∑'r : CuspCosets, (0:ℂ) := by
      apply tsum_congr
      intro r
      have hout : cosetHeight r w<a ∨ b<cosetHeight r w := by
        have h := not_exists.mp hn r
        simpa only [not_and_or,not_le] using h
      simp [cuspCutoffTerm,cuspSeedDefectProfile_zero a b s _ hab hout]
    _ = 0 := tsum_zero

end

open Filter
open scoped BigOperators Classical Topology ContDiff

def rowLogHeight (u : Fin 2 → ℂ) (p : SpatialCoordinates) : ℝ :=
  Real.log (p 2)-Real.log (quadraticHeightDenominator (Complex.normSq (u 0))
    (u 0*star (u 1)).re (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) (p 0) (p 1) (p 2))

lemma exp_rowLogHeight (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    Real.exp (rowLogHeight u p)=rowHeight u p := by
  rw [rowLogHeight,Real.exp_sub,Real.exp_log hp,Real.exp_log (row_denominator_pos u hu p hp)]
  rfl

lemma hasDerivAt_deriv_log_ratio (f g df dg : ℝ → ℝ) (x ddf ddg : ℝ)
    (hf : ∀t,HasDerivAt f (df t) t) (hg : ∀t,HasDerivAt g (dg t) t)
    (hdf : HasDerivAt df ddf x) (hdg : HasDerivAt dg ddg x)
    (hf0 : f x≠0) (hg0 : g x≠0) :
    HasDerivAt (deriv (fun t => Real.log (f t)-Real.log (g t)))
      ((ddf*f x-df x*df x)/(f x)^2-(ddg*g x-dg x*dg x)/(g x)^2) x := by
  have heq : deriv (fun t => Real.log (f t)-Real.log (g t)) =ᶠ[𝓝 x]
      (fun t => df t/f t-dg t/g t) := by
    filter_upwards [((hf x).continuousAt.eventually_ne hf0).and ((hg x).continuousAt.eventually_ne hg0)] with t ht
    exact (((hf t).log ht.1).sub ((hg t).log ht.2)).deriv
  exact ((hdf.div (hf x) hf0).sub (hdg.div (hg x) hg0)).congr_of_eventuallyEq heq

lemma rowLogHeight_hasDerivAt (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    HasDerivAt (fun t => rowLogHeight u (Function.update p j t)) (rowLogD u p j) (p j) := by
  let A := Complex.normSq (u 0)
  let B := (u 0*star (u 1)).re
  let C := -(u 0*star (u 1)).im
  let D := Complex.normSq (u 1)
  have hq := (row_denominator_pos u hu p hp).ne'
  fin_cases j
  · have h := ((hasDerivAt_const (p 0) (p 2)).log hp.ne').sub
      ((quadraticHeightDenominator_hasDerivAt_x A B C D (p 0) (p 1) (p 2)).log hq)
    simpa [rowLogHeight,rowLogD,spatialLogD,heightLogDx,Function.update,A,B,C,D,Pi.sub_def] using! h
  · have h := ((hasDerivAt_const (p 1) (p 2)).log hp.ne').sub
      ((quadraticHeightDenominator_hasDerivAt_y A B C D (p 0) (p 1) (p 2)).log hq)
    simpa [rowLogHeight,rowLogD,spatialLogD,heightLogDy,Function.update,A,B,C,D,Pi.sub_def] using! h
  · have h := ((hasDerivAt_id (p 2)).log hp.ne').sub
      ((quadraticHeightDenominator_hasDerivAt_v A B C D (p 0) (p 1) (p 2)).log hq)
    simpa [rowLogHeight,rowLogD,spatialLogD,heightLogDv,Function.update,A,B,C,D,Pi.sub_def] using! h

lemma rowLogHeight_hasDerivAt_deriv (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    HasDerivAt (deriv (fun t => rowLogHeight u (Function.update p j t))) (rowLogDD u p j) (p j) := by
  let A := Complex.normSq (u 0)
  let B := (u 0*star (u 1)).re
  let C := -(u 0*star (u 1)).im
  let D := Complex.normSq (u 1)
  have hq := (row_denominator_pos u hu p hp).ne'
  fin_cases j
  · have h := hasDerivAt_deriv_log_ratio (fun _ => p 2)
      (fun t => quadraticHeightDenominator A B C D t (p 1) (p 2)) (fun _ => 0)
      (fun t => 2*(A*t+B)) (p 0) 0 (2*A)
      (fun t => hasDerivAt_const t (p 2))
      (fun t => quadraticHeightDenominator_hasDerivAt_x A B C D t (p 1) (p 2))
      (hasDerivAt_const (p 0) 0)
      (by simpa only [id_eq,mul_one] using ((hasDerivAt_id (p 0)).const_mul A |>.add_const B).const_mul 2)
      hp.ne' hq
    simpa [rowLogHeight,rowLogDD,spatialLogDD,heightLogDxx,Function.update,A,B,C,D,Pi.sub_def] using! h
  · have h := hasDerivAt_deriv_log_ratio (fun _ => p 2)
      (fun t => quadraticHeightDenominator A B C D (p 0) t (p 2)) (fun _ => 0)
      (fun t => 2*(A*t+C)) (p 1) 0 (2*A)
      (fun t => hasDerivAt_const t (p 2))
      (fun t => quadraticHeightDenominator_hasDerivAt_y A B C D (p 0) t (p 2))
      (hasDerivAt_const (p 1) 0)
      (by simpa only [id_eq,mul_one] using ((hasDerivAt_id (p 1)).const_mul A |>.add_const C).const_mul 2)
      hp.ne' hq
    simpa [rowLogHeight,rowLogDD,spatialLogDD,heightLogDyy,Function.update,A,B,C,D,Pi.sub_def] using! h
  · have h := hasDerivAt_deriv_log_ratio id
      (fun t => quadraticHeightDenominator A B C D (p 0) (p 1) t) (fun _ => 1)
      (fun t => 2*A*t) (p 2) 0 (2*A)
      (fun t => hasDerivAt_id t)
      (fun t => quadraticHeightDenominator_hasDerivAt_v A B C D (p 0) (p 1) t)
      (hasDerivAt_const (p 2) 1)
      (by simpa only [id_eq,mul_one] using (hasDerivAt_id (p 2)).const_mul (2*A))
      hp.ne' hq
    simpa [rowLogHeight,rowLogDD,spatialLogDD,heightLogDvv,Function.update,A,B,C,D,div_eq_mul_inv] using h

lemma complex_profile_second_chain (F : ℝ → ℂ) (g : ℝ → ℝ) (x dg ddg : ℝ) (dF ddF : ℂ)
    (hg : HasDerivAt g dg x) (hdg : HasDerivAt (deriv g) ddg x)
    (hF : HasDerivAt F dF (g x)) (hdF : HasDerivAt (deriv F) ddF (g x))
    (hlocal : ∀ᶠy in 𝓝 x,DifferentiableAt ℝ g y ∧ DifferentiableAt ℝ F (g y)) :
    HasDerivAt (deriv (fun y => F (g y))) (ddF*(dg:ℂ)^2+dF*(ddg:ℂ)) x := by
  have heq : deriv (fun y => F (g y)) =ᶠ[𝓝 x]
      (fun y => (deriv g y:ℝ) • deriv F (g y)) := by
    filter_upwards [hlocal] with y hy
    exact (hy.2.hasDerivAt.scomp y hy.1.hasDerivAt).deriv
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  convert hdg.smul (hdF.scomp x hg) using 1
  · rfl
  · simp only [Function.comp_apply,hg.deriv,hF.deriv,Complex.real_smul]
    ring

lemma positiveProfile_differentiable (F : ℝ → ℂ)
    (hF : ∀v,0<v→ContDiffAt ℝ ∞ F v) (v : ℝ) (hv : 0<v) :
    DifferentiableAt ℝ F v ∧ DifferentiableAt ℝ (deriv F) v :=
  ⟨(hF v hv).differentiableAt (by simp),
    ((hF v hv).derivWithin (m := ∞) (by simp)).differentiableAt (by simp)⟩

lemma positiveProfile_exp_derivatives (F : ℝ → ℂ)
    (hF : ∀v,0<v→ContDiffAt ℝ ∞ F v) (t : ℝ) :
    HasDerivAt (fun y => F (Real.exp y))
      (deriv F (Real.exp t)*(Real.exp t:ℂ)) t ∧
    HasDerivAt (deriv (fun y => F (Real.exp y)))
      (deriv (deriv F) (Real.exp t)*(Real.exp t:ℂ)^2+
        deriv F (Real.exp t)*(Real.exp t:ℂ)) t := by
  have hdf := positiveProfile_differentiable F hF (Real.exp t) (Real.exp_pos t)
  constructor
  · simpa only [Complex.real_smul,mul_comm,Function.comp_def] using! hdf.1.hasDerivAt.scomp t (Real.hasDerivAt_exp t)
  · apply complex_profile_second_chain F Real.exp t (Real.exp t) (Real.exp t)
      (deriv F (Real.exp t)) (deriv (deriv F) (Real.exp t)) (Real.hasDerivAt_exp t)
      (by simpa only [Real.deriv_exp] using Real.hasDerivAt_exp t) hdf.1.hasDerivAt hdf.2.hasDerivAt
    exact Filter.Eventually.of_forall (fun y =>
      ⟨Real.differentiable_exp y,(positiveProfile_differentiable F hF _ (Real.exp_pos y)).1⟩)

lemma rowProfile_axis_derivatives (F : ℝ → ℂ)
    (hF : ∀v,0<v→ContDiffAt ℝ ∞ F v) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    HasDerivAt (axisSlice (fun q => F (rowHeight u q)) p j)
      (deriv F (rowHeight u p)*(rowHeight u p:ℂ)*(rowLogD u p j:ℂ)) (p j) ∧
    HasDerivAt (deriv (axisSlice (fun q => F (rowHeight u q)) p j))
      (deriv (deriv F) (rowHeight u p)*(rowHeight u p:ℂ)^2*(rowLogD u p j:ℂ)^2+
       deriv F (rowHeight u p)*(rowHeight u p:ℂ)*
        ((rowLogD u p j:ℂ)^2+(rowLogDD u p j:ℂ))) (p j) := by
  let g : ℝ → ℝ := fun t => rowLogHeight u (Function.update p j t)
  let G : ℝ → ℂ := fun t => F (Real.exp t)
  have hg : HasDerivAt g (rowLogD u p j) (p j) := rowLogHeight_hasDerivAt u hu p hp j
  have hdg : HasDerivAt (deriv g) (rowLogDD u p j) (p j) := rowLogHeight_hasDerivAt_deriv u hu p hp j
  have hgval : g (p j)=rowLogHeight u p := by simp [g,Function.update_eq_self]
  have hexp : Real.exp (g (p j))=rowHeight u p := by rw [hgval,exp_rowLogHeight u hu p hp]
  have hG := positiveProfile_exp_derivatives F hF (g (p j))
  have hnear : ∀ᶠt in 𝓝 (p j),0<(Function.update p j t) 2 :=
    ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
      (by simpa only [Function.comp_apply,Function.update_eq_self] using hp)
  have heq : axisSlice (fun q => F (rowHeight u q)) p j =ᶠ[𝓝 (p j)] (fun t => G (g t)) := by
    filter_upwards [hnear] with t ht
    change F (rowHeight u (Function.update p j t))=F (Real.exp (rowLogHeight u (Function.update p j t)))
    rw [exp_rowLogHeight u hu _ ht]
  constructor
  · have hh := hG.1.scomp (p j) hg
    apply HasDerivAt.congr_of_eventuallyEq _ heq
    convert hh using 1
    · rfl
    · simp only [Complex.real_smul,hexp]
      ring
  · have hlocal : ∀ᶠy in 𝓝 (p j),DifferentiableAt ℝ g y ∧ DifferentiableAt ℝ G (g y) := by
      filter_upwards [hnear] with y hy
      constructor
      · have h := rowLogHeight_hasDerivAt u hu (Function.update p j y) hy j
        simpa only [Function.update_idem,Function.update_self] using h.differentiableAt
      · exact (positiveProfile_exp_derivatives F hF (g y)).1.differentiableAt
    have hh := complex_profile_second_chain G g (p j) (rowLogD u p j) (rowLogDD u p j)
      _ _ hg hdg hG.1 hG.2 hlocal
    apply HasDerivAt.congr_of_eventuallyEq _ heq.deriv
    convert hh using 1
    · rw [hexp]
      ring

lemma rowLog_eikonal (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    (p 2)^2*((rowLogD u p 0)^2+(rowLogD u p 1)^2+(rowLogD u p 2)^2)=1 := by
  exact heightLog_eikonal _ _ _ _ _ _ _ (complex_row_quadratic_relation (u 0) (u 1)) hp.ne'
    (row_denominator_pos u hu p hp).ne'
lemma rowLog_laplacian (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    (p 2)^2*(rowLogDD u p 0+rowLogDD u p 1+rowLogDD u p 2)-(p 2)*rowLogD u p 2= -2 := by
  exact heightLog_laplacian _ _ _ _ _ _ _ (complex_row_quadratic_relation (u 0) (u 1)) hp.ne'
    (row_denominator_pos u hu p hp).ne'

theorem rowProfile_laplacian (F : ℝ → ℂ) (hF : ∀v,0<v→ContDiffAt ℝ ∞ F v)
    (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (fun q => F (rowHeight u q)) p=
      (rowHeight u p:ℂ)^2*deriv (deriv F) (rowHeight u p)-(rowHeight u p:ℂ)*deriv F (rowHeight u p) := by
  have hp0 := rowProfile_axis_derivatives F hF u hu p hp 0
  have hp1 := rowProfile_axis_derivatives F hF u hu p hp 1
  have hp2 := rowProfile_axis_derivatives F hF u hu p hp 2
  unfold axisLaplacian
  rw [Fin.sum_univ_three,hp0.2.deriv,hp1.2.deriv,hp2.2.deriv,hp2.1.deriv]
  have hE := congrArg (fun r : ℝ => (r:ℂ)) (rowLog_eikonal u hu p hp)
  have hD := congrArg (fun r : ℝ => (r:ℂ)) (rowLog_laplacian u hu p hp)
  push_cast at hE hD
  linear_combination
    (deriv (deriv F) (rowHeight u p)*(rowHeight u p:ℂ)^2+
      deriv F (rowHeight u p)*(rowHeight u p:ℂ))*hE+
    (deriv F (rowHeight u p)*(rowHeight u p:ℂ))*hD

open Filter
open scoped BigOperators Classical Topology ContDiff

lemma axisLaplacian_congr_eventuallyEq (f g : SpatialCoordinates → ℂ) (p : SpatialCoordinates)
    (heq : f =ᶠ[𝓝 p] g) : axisLaplacian f p=axisLaplacian g p := by
  have haxis (j : Fin 3) : axisSlice f p j =ᶠ[𝓝 (p j)] axisSlice g p j := by
    have ht : Tendsto (fun x => Function.update p j x) (𝓝 (p j)) (𝓝 p) := by
      have h : Tendsto (fun x => Function.update p j x) (𝓝 (p j)) (𝓝 (Function.update p j (p j))) :=
        (continuous_axis_update p j).continuousAt
      simpa only [Function.update_eq_self] using h
    exact heq.comp_tendsto ht
  unfold axisLaplacian
  congr 1
  · congr 1
    exact Finset.sum_congr rfl (fun j _ => (haxis j).deriv.deriv_eq)
  · rw [(haxis 2).deriv_eq]

lemma axisLaplacian_const_mul (c : ℂ) (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) :
    axisLaplacian (fun q => c*f q) p=c*axisLaplacian f p := by
  unfold axisLaplacian
  simp only [Fin.sum_univ_three]
  unfold axisSlice
  simp only [deriv_const_mul_field',deriv_const_mul_field]
  ring

lemma axisLaplacian_finset_sum {ι : Type*} (S : Finset ι) (f : ι → SpatialCoordinates → ℂ)
    (hreg : ∀i∈S,∀q,0<q 2→∀j : Fin 3,
      DifferentiableAt ℝ (axisSlice (f i) q j) (q j) ∧
      DifferentiableAt ℝ (deriv (axisSlice (f i) q j)) (q j))
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (fun q => ∑i∈S,f i q) p=∑i∈S,axisLaplacian (f i) p := by
  have hpair (j : Fin 3) :
      deriv (axisSlice (fun q => ∑i∈S,f i q) p j) (p j)=∑i∈S,deriv (axisSlice (f i) p j) (p j) ∧
      deriv (deriv (axisSlice (fun q => ∑i∈S,f i q) p j)) (p j)=
        ∑i∈S,deriv (deriv (axisSlice (f i) p j)) (p j) := by
    have hfirst (x : ℝ) (hx : 0<(Function.update p j x) 2) :
        HasDerivAt (axisSlice (fun q => ∑i∈S,f i q) p j)
          (∑i∈S,deriv (axisSlice (f i) p j) x) x := by
      have hi (i : ι) (hiS : i∈S) : DifferentiableAt ℝ (axisSlice (f i) p j) x := by
        simpa only [axisSlice_update,Function.update_self] using (hreg i hiS (Function.update p j x) hx j).1
      convert HasDerivAt.sum (fun i hiS => (hi i hiS).hasDerivAt) using 1
      ext y
      simp only [axisSlice,Finset.sum_apply]
    have hnear : ∀ᶠx in 𝓝 (p j),0<(Function.update p j x) 2 :=
      ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
        (by simpa only [Function.comp_apply,Function.update_eq_self] using hp)
    have heq : deriv (axisSlice (fun q => ∑i∈S,f i q) p j) =ᶠ[𝓝 (p j)]
        (fun x => ∑i∈S,deriv (axisSlice (f i) p j) x) := by
      filter_upwards [hnear] with x hx
      exact (hfirst x hx).deriv
    have hsecond : HasDerivAt (deriv (axisSlice (fun q => ∑i∈S,f i q) p j))
        (∑i∈S,deriv (deriv (axisSlice (f i) p j)) (p j)) (p j) := by
      apply (HasDerivAt.sum (fun i hiS => (hreg i hiS p hp j).2.hasDerivAt)).congr_of_eventuallyEq
      filter_upwards [heq] with x hx
      simpa only [Finset.sum_apply] using hx
    exact ⟨(hfirst (p j) (by simpa only [Function.comp_apply,Function.update_eq_self] using hp)).deriv,hsecond.deriv⟩
  unfold axisLaplacian
  simp_rw [(hpair _).1,(hpair _).2]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum,Finset.sum_sub_distrib]

end CubicEisenstein

end

end OAI
end OAIOriginalModule0158

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.DualMiddleExpansion
Source SHA256: 67afec6b5aaa9228984f79b0c1f2f332779ff9100483bb276e4f6b8e776a5403
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0159


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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem scaled_middleTruncation_eq_ideal_frequencies (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (c X Y Z lengthScale : ℝ) :
    (c : ℂ) * middleTruncation (fun P : primePool {G} => P.val) Finset.univ W X Y Z lengthScale =
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, ∑ d ∈ idealDivisors G,
        if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
          (UniqueFactorizationMonoid.moebius d : ℂ) *
            ((((c * X) / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
              paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ)))
        else 0 := by
  classical
  rw [middleTruncation_eq_ideal_frequencies G hG]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hp : Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z
  · simp only [hp, and_self, ite_true]
    push_cast
    ring
  · simp only [hp, ite_false, mul_zero]

theorem dual_normalized_middle_expansion (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (M F b i j Y Z lengthScale : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hb : 0 < b) (hi : 0 < i) (hj : 0 < j) :
    ((M / (Real.sqrt (i * j) * F) : ℝ) : ℂ) *
      middleTruncation (fun P : primePool {G} => P.val) Finset.univ W
        (Real.sqrt (F * i * j / (M * b))) Y Z lengthScale =
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, ∑ d ∈ idealDivisors G,
        if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
          (UniqueFactorizationMonoid.moebius d : ℂ) *
            (((Real.sqrt ((M / F) / b) / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
              paperRadialFourier W
                (Real.sqrt (F * i * j / (M * b)) * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ)))
        else 0 := by
  rw [scaled_middleTruncation_eq_ideal_frequencies G hG,
    dual_principal_prefactor_identity M F b i j hM hF hb hi hj]

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def dualTruncatedMiddle (W : 𝓢(ℝ, ℂ))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    (((M / (Real.sqrt ((Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ)) * F) : ℝ) : ℂ) *
      middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ)))) (Y i) (Z i) lengthScale)

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dual_truncated_pair_expansion
    (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hrows : ∀ i, Admissible (rows i))
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hK : ∀ j k d, d ∣ left j * right k → d ∈ K) (i : m) (j : n) (k : p) :
    originalTerm rows left right a b 1 1 i j k *
      (((M / (Real.sqrt ((Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ)) * F) : ℝ) : ℂ) *
        middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
          (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
            (M * (Ideal.absNorm (rows i) : ℝ)))) (Y i) (Z i) lengthScale) =
      ∑ h : rowNormDisk ⌊lengthScale⌋₊, ∑ d : K, (UniqueFactorizationMonoid.moebius d.val : ℂ) *
        (if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
          if d.val ∣ left j * right k then
            originalTerm rows left right a b 1 1 i j k *
              dualPrincipalKernel W rows left right M F h.val d.val i j k
          else 0 else 0) := by
  classical
  rw [sum_two_finite_subtypes (rowNormDisk ⌊lengthScale⌋₊) K (fun h d =>
    (UniqueFactorizationMonoid.moebius d : ℂ) *
      (if Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i then
        if d ∣ left j * right k then
          originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h d i j k
        else 0 else 0))]
  by_cases hc : IsCoprime (left j) (right k)
  · have hsq : Squarefree (left j * right k) :=
      squarefree_mul_iff.mpr ⟨hc.isRelPrime, (hleft j).2.1, (hright k).2.1⟩
    have hpos (I : Ideal O) (hI : Admissible I) : 0 < (Ideal.absNorm I : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h => hI.1 (Ideal.absNorm_eq_zero_iff.mp h))
    rw [dual_normalized_middle_expansion _ hsq _ _ _ _ _ _ _ _ _ hM hF
      (hpos _ (hrows i)) (hpos _ (hleft j)) (hpos _ (hright k)), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    rw [← divisorPool_filter K (left j * right k) hsq.ne_zero (hK j k), Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdv : d ∣ left j * right k
    · by_cases hp : Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i
      · simp only [hdv, hp, and_self, ite_true, dualPrincipalKernel]
        ring
      · simp only [hdv, hp, ite_true, ite_false, mul_zero]
    · simp only [hdv, ite_false, ite_self, mul_zero]
  · have hz : originalTerm rows left right a b 1 1 i j k = 0 := by simp only [originalTerm, hc, ite_false]
    simp only [hz, zero_mul, ite_self, mul_zero, Finset.sum_const_zero]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualTruncatedMiddle_le_product_divisors
    (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hrows : ∀ i, Admissible (rows i))
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hK : ∀ j k d, d ∣ left j * right k → d ∈ K) :
    ‖dualTruncatedMiddle W rows left right a b M F Y Z lengthScale‖ ≤
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, dualProductDivisorMiddleAt W K rows left right a b M F
        (fun d i => Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i) h := by
  classical
  let A : m → n → p → rowNormDisk ⌊lengthScale⌋₊ → K → ℂ := fun i j k h d =>
    if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
      if d.val ∣ left j * right k then
        originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h.val d.val i j k
      else 0 else 0
  have he : dualTruncatedMiddle W rows left right a b M F Y Z lengthScale =
      ∑ i, ∑ j, ∑ k, ∑ h : rowNormDisk ⌊lengthScale⌋₊, ∑ d : K,
        (UniqueFactorizationMonoid.moebius d.val : ℂ) * A i j k h d := by
    unfold dualTruncatedMiddle
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    exact dual_truncated_pair_expansion W K rows left right a b M F Y Z lengthScale hM hF hrows hleft hright hK i j k
  rw [he]
  apply (finite_middle_triangle (fun d : K => (UniqueFactorizationMonoid.moebius d.val : ℂ))
    (fun d => QuadraticInitialBound.norm_ideal_moebius_le_one d.val) A).trans_eq
  rw [Finset.sum_coe_sort (rowNormDisk ⌊lengthScale⌋₊) (fun h => ∑ i, ∑ d : K,
    ‖∑ j, ∑ k, if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
      if d.val ∣ left j * right k then
        originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h d.val i j k
      else 0 else 0‖)]
  apply Finset.sum_congr rfl
  intro h hh
  unfold dualProductDivisorMiddleAt
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_coe_sort K (fun d =>
    ‖∑ j, ∑ k, if Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i then
      if d ∣ left j * right k then
        originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h d i j k
      else 0 else 0‖)]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hp : Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i <;>
    simp only [hp, and_self, ite_true, ite_false, Finset.sum_const_zero, norm_zero]

theorem HasSieveExponent.dual_truncated_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hZ : ∀ i, Z i ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) :
    ‖dualTruncatedMiddle W rows left right a b M F Y Z lengthScale‖ ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2))) := by
  let pairCols : n × p → Ideal O := fun x => left x.1 * right x.2
  let K := columnDivisorPool pairCols
  have hPair : ∀ x, pairCols x ≠ 0 := fun x => mul_ne_zero (hleft x.1).1.1 (hright x.2).1.1
  have hK (j : n) (k : p) (d : Ideal O) (hd : d ∣ left j * right k) : d ∈ K :=
    mem_columnDivisorPool_of_dvd pairCols hPair (j, k) d hd
  let P : Ideal O → m → Prop := fun d i =>
    Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i
  have hb := hexp.dual_product_divisor_middle deltaLoss hδ ε hε K B N M F U hB hN hM hF hU
    rows left right hr hl hri hrows a b (fun _ => a) (fun _ => b)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) W P hleft hright
    (fun d hd i hp => hp.2.trans (hZ i))
  have hH (h : O) (hh : h ∈ rowNormDisk ⌊lengthScale⌋₊) : h ≠ 0 := by
    intro hz
    have hn := (mem_rowNormDisk.mp hh).1
    simp [hz] at hn
  calc
    _ ≤ ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, dualProductDivisorMiddleAt W K rows left right a b M F P h :=
      dualTruncatedMiddle_le_product_divisors W K rows left right a b M F Y Z lengthScale hM hF (fun i => (hrows i).1)
        (fun j => (hleft j).1) (fun k => (hright k).1) hK
    _ ≤ ∑' h : {h : O // h ≠ 0}, dualProductDivisorMiddleAt W K rows left right a b M F P h.val :=
      finite_nonzero_frequency_sum_le (rowNormDisk ⌊lengthScale⌋₊) hH _
        (fun h => dualProductDivisorMiddleAt_nonneg W K rows left right a b M F P h) hb.1
    _ ≤ _ := hb.2

end CanonicalQuadraticSieve

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (jLabel primeProduct bit)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hcop in
omit [DecidableEq ι] in
theorem primeSpanProduct_squarefree (S : Finset ι) :
    Squarefree (∏ i ∈ S, Ideal.span {p i}) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    exact (hcop hij).isRelPrime
  · intro i hi
    exact (Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance).squarefree

omit [DecidableEq ι] in
theorem row_nonzero_notMem (S : Finset ι) (c : O)
    (h : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S c ≠ 0) :
    ∀ i ∈ S, c ∉ Ideal.span {p i} := by
  intro i hi hc
  have hzero : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S c ^ 6 = 0 := by
    rw [← FirstPassCubeLabels.row_pow, finiteSquarefreeRow_sixth_power, ite_eq_left ⟨i,hi,hc⟩]
  exact pow_ne_zero 6 h hzero

omit [DecidableEq ι] in
theorem primeSpanProduct_isCoprime_of_row_nonzero (S : Finset ι) (c : O)
    (h : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S c ≠ 0) :
    IsCoprime (∏ i ∈ S, Ideal.span {p i}) (Ideal.span {c}) := by
  apply IsCoprime.prod_left
  intro i hi
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra htop
  have he := Ideal.IsMaximal.eq_of_le (inferInstance : (Ideal.span {p i}).IsMaximal)
    htop (show Ideal.span {p i} ≤ Ideal.span {p i} ⊔ Ideal.span {c} from le_sup_left)
  have hc : c ∈ Ideal.span {p i} := by
    rw [he]
    exact (show Ideal.span {c} ≤ Ideal.span {p i} ⊔ Ideal.span {c} from le_sup_right)
      (Ideal.subset_span (Set.mem_singleton c))
  exact row_nonzero_notMem p hg S c h i hi hc

def firstRetainedSupport (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Finset ι :=
  B.filter (fun i => FirstPassCubeLabels.retained (FirstPassCubeLabels.parity (v i)) (ε₁ i) (ε₂ i))

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem jLabel_eq_retainedProduct (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    jLabel p B v ε₁ ε₂ = ∏ i ∈ firstRetainedSupport B v ε₁ ε₂, p i := by
  unfold jLabel primeProduct firstRetainedSupport
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i hi
  cases hb : FirstPassCubeLabels.retained (FirstPassCubeLabels.parity (v i)) (ε₁ i) (ε₂ i) <;> simp [bit,hb]

include hcop in
theorem firstBaseLabel_squarefree (B C : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hCB : Disjoint C B) :
    Squarefree (Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) C * jLabel p B v ε₁ ε₂}) := by
  have hCJ : Disjoint C (firstRetainedSupport B v ε₁ ε₂) :=
    Finset.disjoint_of_subset_right (Finset.filter_subset _ _) hCB
  rw [← Ideal.span_singleton_mul_span_singleton, jLabel_eq_retainedProduct,
    FiniteGaussPhase.span_finset_prod, primeSubsetGenerator, ConcretePrimeRowBridge.span_idealGenerator,
    ← Finset.prod_union hCJ]
  exact primeSpanProduct_squarefree p hcop _

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (jLabel)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondArithmeticWeight (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex)
    (x : SecondExpansionData ι) : ℂ :=
  secondSourceCommonCoefficient p hg Ψ m c d x.sourceCommon x.divisor *
    secondTotalWeight p hp hcop hg Ψ Ψ m (secondExpansionQuotient p x) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency (z,x.overlap)

theorem secondArithmeticWeight_coprime (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex)
    (x : SecondExpansionData ι) (hE : x.divisor ⊆ x.sourceCommon)
    (h : secondArithmeticWeight p hp hcop hg Ψ m c d z x ≠ 0) :
    IsCoprime (Ideal.span {c}) (∏ i ∈ x.divisor, Ideal.span {p i}) ∧
    IsCoprime (Ideal.span {c}) (∏ i ∈ x.overlap, Ideal.span {p i}) ∧
    IsCoprime (∏ i ∈ x.divisor, Ideal.span {p i}) (∏ i ∈ x.overlap, Ideal.span {p i}) := by
  have hG : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg x.sourceCommon c ≠ 0 := by
    intro hz
    apply h
    simp only [secondArithmeticWeight, secondSourceCommonCoefficient, secondInputCoefficient,
      hz, zero_pow (by decide : 4 ≠ 0), mul_zero, zero_mul, norm_zero, zero_pow (by decide : 2 ≠ 0),
      Complex.ofReal_zero]
  have hV : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg x.overlap c ≠ 0 := by
    intro hz
    apply h
    simp only [secondArithmeticWeight, secondTotalWeight, secondCommonWeight, secondPreColumn,
      hz, zero_pow (by decide : 4 ≠ 0), mul_zero, zero_mul, star_zero]
  have hVe : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg x.overlap
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) ≠ 0 := by
    intro hz
    apply h
    simp only [secondArithmeticWeight, secondTotalWeight, secondCommonWeight, secondPreColumn,
      hz, mul_zero, zero_mul, star_zero]
  have hGc := primeSpanProduct_isCoprime_of_row_nonzero p hg x.sourceCommon c hG
  have hEc : IsCoprime (∏ i ∈ x.divisor, Ideal.span {p i}) (Ideal.span {c}) := by
    apply IsCoprime.prod_left
    intro i hi
    exact (IsCoprime.prod_left_iff.mp hGc) i (hE hi)
  have hVc := primeSpanProduct_isCoprime_of_row_nonzero p hg x.overlap c hV
  have hVE := primeSpanProduct_isCoprime_of_row_nonzero p hg x.overlap _ hVe
  rw [primeSubsetGenerator, ConcretePrimeRowBridge.span_idealGenerator] at hVE
  exact ⟨hEc.symm,hVc.symm,hVE.symm⟩

theorem secondArithmeticWeight_squarefree (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex)
    (x : SecondExpansionData ι) (hE : x.divisor ⊆ x.sourceCommon)
    (hc : Squarefree (Ideal.span {c}))
    (h : secondArithmeticWeight p hp hcop hg Ψ m c d z x ≠ 0) :
    Squarefree (Ideal.span {c} * (∏ i ∈ x.divisor, Ideal.span {p i}) *
      (∏ i ∈ x.overlap, Ideal.span {p i})) := by
  obtain ⟨hcE,hcV,hEV⟩ := secondArithmeticWeight_coprime p hp hcop hg Ψ m c d z x hE h
  apply squarefree_mul_iff.mpr
  refine ⟨(hcV.mul_left hEV).isRelPrime,?_,primeSpanProduct_squarefree p hcop _⟩
  exact squarefree_mul_iff.mpr ⟨hcE.isRelPrime,hc,primeSpanProduct_squarefree p hcop _⟩

theorem actualSecondLabel_squarefree_of_weight
    (B C : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hCB : Disjoint C B)
    (Ψ : O →* ℂ) (m d : O) (z : SecondRayIndex)
    (x : SecondExpansionData ι) (hE : x.divisor ⊆ x.sourceCommon)
    (h : secondArithmeticWeight p hp hcop hg Ψ m
      (primeSubsetGenerator (fun i => Ideal.span {p i}) C *
        jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂) d z x ≠ 0) :
    Squarefree (actualSecondLabel p B C x.divisor x.overlap v₁ v₂ ε₁ ε₂) := by
  have hs := secondArithmeticWeight_squarefree p hp hcop hg Ψ m _ d z x hE
    (firstBaseLabel_squarefree p hcop B C (fun i => v₁ i+v₂ i) ε₁ ε₂ hCB) h
  rw [← Ideal.span_singleton_mul_span_singleton, primeSubsetGenerator,
    ConcretePrimeRowBridge.span_idealGenerator, mul_comm (∏ i ∈ C, Ideal.span {p i})] at hs
  exact hs

theorem secondExpansionSource_eq_squarefree
    (B C : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hCB : Disjoint C B)
    (F : Finset ι) (Ψ : O →* ℂ) (m d : O) (z : SecondRayIndex)
    (s : Finset (SecondExpansionData ι)) (hE : ∀ x ∈ s, x.divisor ⊆ x.sourceCommon)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C *
      jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂
    secondExpansionSource p hp hcop hg F Ψ m c d z s H₁ H₂ W Y =
    secondExpansionSource p hp hcop hg F Ψ m c d z
      (s.filter (fun x => Squarefree (actualSecondLabel p B C x.divisor x.overlap v₁ v₂ ε₁ ε₂)))
      H₁ H₂ W Y := by
  dsimp only
  unfold secondExpansionSource
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hs : Squarefree (actualSecondLabel p B C x.divisor x.overlap v₁ v₂ ε₁ ε₂)
  · rw [ite_eq_left hs]
  · rw [ite_eq_right hs]
    have hw : secondArithmeticWeight p hp hcop hg Ψ m
        (primeSubsetGenerator (fun i => Ideal.span {p i}) C *
          jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂) d z x = 0 := by
      by_contra hn
      exact hs (actualSecondLabel_squarefree_of_weight p hp hcop hg B C v₁ v₂ ε₁ ε₂ hCB
        Ψ m d z x (hE x hx) hn)
    unfold secondArithmeticWeight at hw
    rcases mul_eq_zero.mp hw with hA | hB
    · rw [hA]
      ring
    · rw [hB]
      ring

end

open scoped BigOperators Classical
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
open SecondPassIntegration (densityChildEnergy childGeometricMean childEnergy)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondLogNormalizedEnergy (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex)
    (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (J : ℕ) : ℝ :=
  densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ m
    (secondLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j) V₁ V₂
    (secondLogX p R X j) (secondLogX p R X j) J /
  (secondLogX p R X j * secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j)

lemma secondLogNormalizedEnergy_nonneg
    (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (hX : 0 < X)
    (j : SecondLogIndex) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (J : ℕ) :
    0 ≤ secondLogNormalizedEnergy p hp hcop hg B C D F v₁ v₂ ε₁ ε₂ K R X M j Ψ₁ Ψ₂ m V₁ V₂ J := by
  apply div_nonneg
  · apply integral_nonneg
    intro t₁
    apply integral_nonneg
    intro t₂
    apply integral_nonneg
    intro t₃
    exact mul_nonneg (JointLogSeparation.tripleLogDensity_nonneg _ _)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  · exact mul_nonneg (secondLogX_pos p hp R X hX j).le
      (zero_le_one.trans (secondLogLabelBound_ge_one p hp B C v₁ v₂ ε₁ ε₂ j))

lemma secondLogNormalizedEnergy_empty
    (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ)
    (j : SecondLogIndex) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (J : ℕ)
    (hT : secondLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j = ∅) :
    secondLogNormalizedEnergy p hp hcop hg B C D F v₁ v₂ ε₁ ε₂ K R X M j Ψ₁ Ψ₂ m V₁ V₂ J = 0 := by
  simp only [secondLogNormalizedEnergy, hT, densityChildEnergy, childGeometricMean, childEnergy,
    Finset.sum_empty, Finset.sum_const_zero, Real.sqrt_zero, mul_zero, integral_zero, zero_div]

theorem secondLog_normalized_cost
    (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X Y M : ℝ) (hX : 0 < X)
    (j : SecondLogIndex) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (J : ℕ) :
    (Y*primeProductNorm p R/X^2) *
      densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ m
        (secondLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j) V₁ V₂
        (secondLogX p R X j) (secondLogX p R X j) J =
    (Y*‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖^2*Real.exp 2/X) *
      secondLogNormalizedEnergy p hp hcop hg B C D F v₁ v₂ ε₁ ε₂ K R X M j Ψ₁ Ψ₂ m V₁ V₂ J := by
  unfold secondLogNormalizedEnergy
  rw [secondLogX_label_cost]
  have hR := (FirstPassCubeLabels.primeProductNorm_pos p hp R).ne'
  have hc := (zero_lt_one.trans_le (element_norm_ge_one _ (secondBaseLabel_ne_zero p hp B C v₁ v₂ ε₁ ε₂))).ne'
  have hcn : ‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖ ≠ 0 := by
    intro h; apply hc; rw [h]; norm_num
  field_simp

include hp in

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem first_second_normalized_child_cost
    (A B C R : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (X Y : ℝ) (hX : 0 < X) (j : SecondLogIndex) :
    (primeProductNorm p A)⁻¹ *
      (Y*primeProductNorm p R/(X/primeProductNorm p A)^2) *
      (secondLogX p R (X/primeProductNorm p A) j * secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j) =
    Y*‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖^2*Real.exp 2/X := by
  rw [secondLogX_label_cost]
  have hA := (FirstPassCubeLabels.primeProductNorm_pos p hp A).ne'
  have hR := (FirstPassCubeLabels.primeProductNorm_pos p hp R).ne'
  field_simp

end

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in

theorem secondBinnedIndex_mass (F : Finset ι) (U Kmax : ℝ) :
    (∑ z : SecondRayIndex, ∑ _R ∈ boundedPrimeSupports p F U,
      ∑ _j ∈ secondLogBinBox U Kmax, ‖secondRayCoefficient z‖) ≤
    (512*32^2) * (128*max 1 U) *
      (((normLogBin U+1)^2*(normLogBin Kmax+1) : ℕ) : ℝ) := by
  have hsub : boundedPrimeSupports p F U ⊆ boundedPrimeSupports p F (max 1 U) := by
    intro R hR
    obtain ⟨hR,hN⟩ := Finset.mem_filter.mp hR
    exact Finset.mem_filter.mpr ⟨hR,hN.trans (le_max_right _ _)⟩
  have hc : ((boundedPrimeSupports p F U).card : ℝ) ≤ 128*max 1 U := by
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (boundedPrimeSupports_card p hinj F (max 1 U) (le_max_left _ _))
  have he : (∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F U,
      ∑ j ∈ secondLogBinBox U Kmax, ‖secondRayCoefficient z‖) =
      (∑ z : SecondRayIndex, ‖secondRayCoefficient z‖) *
        (boundedPrimeSupports p F U).card * (secondLogBinBox U Kmax).card := by
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_mul]
    ring_nf
  rw [he, secondLogBinBox_card]
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul secondRayCoefficient_mass hc (by positivity) (by positivity)
  · positivity

end SecondPassArithmetic

namespace FirstPassCubeLabels
open scoped BigOperators
open MeasureTheory

lemma firstLogDensity_pair_moment (J : ℕ) (t : ℝ) :
    firstLogDensity (2*(J+2)) t * ((1+‖t‖)^(J+2) * (1+‖t‖)^(J+2)) = firstLogDensity 0 t := by
  rw [← pow_add, show J+2+(J+2)=2*(J+2) by omega, mul_comm]
  exact JointLogSeparation.density_weight_identity _ _

lemma firstLogDensity_le_zero (J : ℕ) (t : ℝ) : firstLogDensity J t ≤ firstLogDensity 0 t := by
  have h := pow_le_pow_right₀ (show 1 ≤ 1+‖t‖ by linarith [norm_nonneg t]) (show 2 ≤ J+2 by omega)
  apply inv_anti₀ (by positivity : 0 < (1+‖t‖)^2) h

lemma integral_pair_moment_bound (J : ℕ) (f : ℝ → ℝ)
    (hf : Integrable (fun t => firstLogDensity (2*(J+2)) t * f t))
    (a d c q : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d) (hq : 0 ≤ q)
    (h : ∀ t, f t ≤ a*(d + ((1+‖t‖)^(J+2)*(1+‖t‖)^(J+2))*c + q)) :
    (∫ t, firstLogDensity (2*(J+2)) t * f t) ≤
      (∫ t, firstLogDensity 0 t) * a * (d+c+q) := by
  have hi := (firstLogDensity_integrable 0).mul_const (a*(d+c+q))
  have hm : ∀ t, firstLogDensity (2*(J+2)) t * f t ≤ firstLogDensity 0 t*(a*(d+c+q)) := by
    intro t
    apply (mul_le_mul_of_nonneg_left (h t) (firstLogDensity_nonneg _ _)).trans
    have h1 := mul_le_mul_of_nonneg_right (firstLogDensity_le_zero (2*(J+2)) t) (mul_nonneg ha hd)
    have h2 := mul_le_mul_of_nonneg_right (firstLogDensity_le_zero (2*(J+2)) t) (mul_nonneg ha hq)
    have he := firstLogDensity_pair_moment J t
    calc
      _ = firstLogDensity (2*(J+2)) t*(a*d) +
          (firstLogDensity (2*(J+2)) t*((1+‖t‖)^(J+2)*(1+‖t‖)^(J+2)))*(a*c) +
          firstLogDensity (2*(J+2)) t*(a*q) := by ring
      _ ≤ firstLogDensity 0 t*(a*d) + firstLogDensity 0 t*(a*c) + firstLogDensity 0 t*(a*q) := by
        rw [he]
        exact add_le_add (add_le_add h1 le_rfl) h2
      _ = _ := by ring
  have hh := integral_mono hf hi hm
  rw [integral_mul_const] at hh
  simpa only [mul_assoc] using hh

end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter)
open SecondPassIntegration (densityChildEnergy)

theorem firstCoreInputRow_binned_integrated_transfer
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (hU : ∀ t, g t ≠ 0 → U t = 1)
    (M : ℝ) (hM : 0 ≤ M) (hgM : ∀ t, g t ≠ 0 → |t| ≤ M)
    (ε : ℝ) (hε : 0 < ε) (tailOrder decayOrder J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw Ctail : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧ 0 < Ctail ∧
      ∀ (Y : ℝ), 0 < Y →
      ∀ (A₀ B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (χ : RayCharacter) (Ψ : O →* ℂ) (m : O) (r₁ : FirstCoreIndex)
        (X Z : ℝ) (Srows : Finset O),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X → 0 ≤ Z →
        (∀ z ∈ Srows, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
        (∀ z ∈ Srows, z ≠ 0) →
        let v := fun i => v₁ i + v₂ i
        let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
        let Ψ' := firstCoreTwist negative χ Ψ r₁
        let m' := m * b0Label p B v ε₁ ε₂
        let c' := c * jLabel p B v ε₁ ε₂
        let X' := X / primeProductNorm p A₀
        let Usupp := X' * Real.exp M
        let K := firstCoreSecondCutoff p A₀ X Y M Z
        let Kmax := firstCoreSecondRowBound p D A₀ X Y M Z
        let Hbase := normalizedColumn p (fun S => firstCoreBaseProfile g V negative (columnLog p X' S))
        (∫ t : ℝ, FirstPassCubeLabels.firstLogDensity (2*(J+2)) t * (∑ z ∈ Srows, ‖firstCoreInputRow p hg F A₀ B v ε₁ ε₂ negative χ Ψ m
          (normalizedColumn p (fun S => g (columnLog p X S))) V (columnLog p X) c d r₁ t z‖^2)) ≤
        (∫ t : ℝ, FirstPassCubeLabels.firstLogDensity 0 t) * (primeProductNorm p A₀)⁻¹ *
          (|Y| * ‖paperRadialFourier rowMajorant 0‖ *
              (∑ G ∈ (F\A₀).powerset, ‖secondInputCoefficient p hg Ψ' m' c' d Hbase G‖^2) +
            (∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p (F\A₀) Usupp,
              ∑ j ∈ secondLogBinBox Usupp Kmax,
              (Y * primeProductNorm p R / X'^2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
                (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j *
                  Ideal.absNorm (Ideal.span {b0Label p B v ε₁ ε₂}))^ε) *
              (Cₛ /
                (1+Y*secondLogK j*(primeProductNorm p R)^2/(primeProductNorm p D*X'^2))^decayOrder) *
              densityChildEnergy p hp hcop hg (F\A₀) (secondRayMinus Ψ' z) (secondRayPlus Ψ' z)
                (m' * primeSubsetGenerator (fun i => Ideal.span {p i}) R)
                (secondLogTargets p B C D (F\A₀) v₁ v₂ ε₁ ε₂ K R X' M j)
                (windows 5) (windows 6) (secondLogX p R X' j) (secondLogX p R X' j) J) +
            Ctail*(1+Usupp)^4*Y*(1+(1+Usupp)^3/Y)^2/(1+Z)^tailOrder) := by
  obtain ⟨windows,Cₐ,Cₛ,Cw,Ctail,hCₐ,hCₛ,hCw,hCtail,hpoint⟩ :=
    firstCoreInputRow_binned_finite_transfer p hp hcop hg hinj hc hpr U hUc hUs
      g V negative hU M hM hgM ε hε tailOrder decayOrder J
  refine ⟨windows,Cₐ,Cₛ,Cw,Ctail,hCₐ,hCₛ,hCw,hCtail,?_⟩
  intro Y hY A₀ B C D F v₁ v₂ ε₁ ε₂ χ Ψ m r₁ X Z Srows hv hCB hD hΨ hX hZ hSrows hSrows0
  dsimp only
  let v := fun i => v₁ i+v₂ i
  let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
  let Ψ' := firstCoreTwist negative χ Ψ r₁
  let m' := m*b0Label p B v ε₁ ε₂
  let c' := c*jLabel p B v ε₁ ε₂
  let X' := X/primeProductNorm p A₀
  let Usupp := X'*Real.exp M
  let K := firstCoreSecondCutoff p A₀ X Y M Z
  let Kmax := firstCoreSecondRowBound p D A₀ X Y M Z
  let Hbase := normalizedColumn p (fun S => firstCoreBaseProfile g V negative (columnLog p X' S))
  let f := fun t => ∑ z ∈ Srows, ‖firstCoreInputRow p hg F A₀ B v ε₁ ε₂ negative χ Ψ m
    (normalizedColumn p (fun S => g (columnLog p X S))) V (columnLog p X) c d r₁ t z‖^2
  let diag := |Y| * ‖paperRadialFourier rowMajorant 0‖*
    (∑ G ∈ (F\A₀).powerset, ‖secondInputCoefficient p hg Ψ' m' c' d Hbase G‖^2)
  let tail := Ctail*(1+Usupp)^4*Y*(1+(1+Usupp)^3/Y)^2/(1+Z)^tailOrder
  let childAt := fun t : ℝ => ∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p (F\A₀) Usupp,
    ∑ j ∈ secondLogBinBox Usupp Kmax,
    (Y*primeProductNorm p R/X'^2*‖secondRayCoefficient z‖*Cw*Cₐ*
      (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j*Ideal.absNorm (Ideal.span {b0Label p B v ε₁ ε₂}))^ε) *
    (Cₛ*(1+‖t‖)^(J+2)*(1+‖t‖)^(J+2) /
      (1+Y*secondLogK j*(primeProductNorm p R)^2/(primeProductNorm p D*X'^2))^decayOrder) *
    densityChildEnergy p hp hcop hg (F\A₀) (secondRayMinus Ψ' z) (secondRayPlus Ψ' z)
      (m'*primeSubsetGenerator (fun i => Ideal.span {p i}) R)
      (secondLogTargets p B C D (F\A₀) v₁ v₂ ε₁ ε₂ K R X' M j)
      (windows 5) (windows 6) (secondLogX p R X' j) (secondLogX p R X' j) J
  let child := ∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p (F\A₀) Usupp,
    ∑ j ∈ secondLogBinBox Usupp Kmax,
    (Y*primeProductNorm p R/X'^2*‖secondRayCoefficient z‖*Cw*Cₐ*
      (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j*Ideal.absNorm (Ideal.span {b0Label p B v ε₁ ε₂}))^ε) *
    (Cₛ /
      (1+Y*secondLogK j*(primeProductNorm p R)^2/(primeProductNorm p D*X'^2))^decayOrder) *
    densityChildEnergy p hp hcop hg (F\A₀) (secondRayMinus Ψ' z) (secondRayPlus Ψ' z)
      (m'*primeSubsetGenerator (fun i => Ideal.span {p i}) R)
      (secondLogTargets p B C D (F\A₀) v₁ v₂ ε₁ ε₂ K R X' M j)
      (windows 5) (windows 6) (secondLogX p R X' j) (secondLogX p R X' j) J
  have hchild (t : ℝ) : childAt t = ((1+‖t‖)^(J+2)*(1+‖t‖)^(J+2))*child := by
    dsimp only [child, childAt]
    simp only [    Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    apply Finset.sum_congr rfl
    intro R hR
    apply Finset.sum_congr rfl
    intro j hj
    ring
  change (∫ t, firstLogDensity (2*(J+2)) t*f t) ≤
    (∫ t, firstLogDensity 0 t)*(primeProductNorm p A₀)⁻¹*(diag+child+tail)
  apply FirstPassCubeLabels.integral_pair_moment_bound J f
  · dsimp only [f]
    simp only [Finset.mul_sum]
    apply integrable_finsetSum
    intro z hz
    exact firstCoreInputRow_integrable p hg F A₀ B v ε₁ ε₂ negative χ Ψ m
      (normalizedColumn p (fun S => g (columnLog p X S))) V (columnLog p X) c d r₁ z
      (FirstPassCubeLabels.firstLogDensity_integrable (2*(J+2)))
  · exact inv_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp A₀).le
  · dsimp [diag]
    positivity
  · dsimp [tail]
    positivity
  · intro t
    have hb := hpoint Y hY A₀ B C D F v₁ v₂ ε₁ ε₂ χ Ψ m r₁ X Z t Srows
      hv hCB hD hΨ hX hZ hSrows hSrows0
    change f t + _ ≤ (primeProductNorm p A₀)⁻¹*(diag+childAt t+tail) at hb
    rw [hchild] at hb
    exact (le_add_of_nonneg_right (sq_nonneg _)).trans hb

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0159

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.SeedDefects
Source SHA256: 84d756d4f63556c745485648efb25fb39dbe65b530f3750332f44d360a933a8b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0160



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

namespace CubicEisenstein
open Filter
open scoped BigOperators Classical Topology ContDiff

lemma cuspSeed_row_defect (a b : ℝ) (s c : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (fun q => c*cuspSeedProfile a b s (rowHeight u q)) p-
      s*(s-2)*(c*cuspSeedProfile a b s (rowHeight u p))=
        c*cuspSeedDefectProfile a b s (rowHeight u p) := by
  rw [axisLaplacian_const_mul,rowProfile_laplacian _ (cuspSeedProfile_contDiffAt a b s) u hu p hp]
  have h := cuspSeedProfile_laplace_defect a b s (rowHeight u p) (rowHeight_pos u hu p hp).ne'
  linear_combination c*h

theorem heightPoincare_cuspSeed_laplace_defect (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (heightPoincareField (cuspSeedProfile a b s)) p-
      s*(s-2)*heightPoincareField (cuspSeedProfile a b s) p=
        heightPoincareField (cuspSeedDefectProfile a b s) p := by
  obtain ⟨U,hU,hpU,S,hrows⟩ := locally_finite_high_rows p hp
  let f : CuspCosets → SpatialCoordinates → ℂ :=
    fun r q => (cosetCharacter r)⁻¹*cuspSeedProfile a b s (rowHeight (embeddedRow r) q)
  have heq : heightPoincareField (cuspSeedProfile a b s) =ᶠ[𝓝 p] (fun q => ∑r∈S,f r q) := by
    filter_upwards [hU.mem_nhds hpU] with q hq
    apply tsum_eq_sum
    intro r hr
    rw [cuspSeedProfile_zero a b s _ hab (le_trans ((hrows q hq).2 r hr).le ha.le),mul_zero]
  have hD : heightPoincareField (cuspSeedDefectProfile a b s) p=
      ∑r∈S,(cosetCharacter r)⁻¹*cuspSeedDefectProfile a b s (rowHeight (embeddedRow r) p) := by
    apply tsum_eq_sum
    intro r hr
    rw [cuspSeedDefectProfile_zero a b s _ hab (Or.inl (((hrows p hpU).2 r hr).trans ha)),mul_zero]
  have hreg : ∀r∈S,∀q,0<q 2→∀j : Fin 3,
      DifferentiableAt ℝ (axisSlice (f r) q j) (q j) ∧
      DifferentiableAt ℝ (deriv (axisSlice (f r) q j)) (q j) := by
    intro r hr q hq j
    have hc : ∀v,0<v→ContDiffAt ℝ ∞ (fun v => (cosetCharacter r)⁻¹*cuspSeedProfile a b s v) v :=
      fun v hv => contDiffAt_const.mul (cuspSeedProfile_contDiffAt a b s v hv)
    have h := rowProfile_axis_derivatives _ hc (embeddedRow r) (embeddedRow_ne_zero r) q hq j
    exact ⟨h.1.differentiableAt,h.2.differentiableAt⟩
  rw [axisLaplacian_congr_eventuallyEq _ _ p heq,axisLaplacian_finset_sum S f hreg p hp,
    heq.eq_of_nhds,hD,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  exact cuspSeed_row_defect a b s (cosetCharacter r)⁻¹ (embeddedRow r) (embeddedRow_ne_zero r) p hp

def smoothCuspSeedField (a b : ℝ) (s : ℂ) (p : SpatialCoordinates) : ℂ :=
  if hp : 0<p 2 then smoothCuspSeed a b s
    (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp) else 0

def smoothCuspSeedDefectField (a b : ℝ) (s : ℂ) (p : SpatialCoordinates) : ℂ :=
  if hp : 0<p 2 then smoothCuspSeedDefect a b s
    (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp) else 0

lemma smoothCuspSeedField_eq (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    smoothCuspSeedField a b s p=heightPoincareField (cuspSeedProfile a b s) p := by
  rw [smoothCuspSeedField,dite_eq_left hp,smoothCuspSeed_coordinate a b s ha hab p hp]
lemma smoothCuspSeedDefectField_eq (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    smoothCuspSeedDefectField a b s p=heightPoincareField (cuspSeedDefectProfile a b s) p := by
  rw [smoothCuspSeedDefectField,dite_eq_left hp,smoothCuspSeedDefect_coordinate a b s ha hab p hp]

lemma actual_smoothCuspSeed_contDiffAt (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) : ContDiffAt ℝ ∞ (smoothCuspSeedField a b s) p := by
  have heq : smoothCuspSeedField a b s =ᶠ[𝓝 p] heightPoincareField (cuspSeedProfile a b s) := by
    filter_upwards [(continuous_apply 2).continuousAt.eventually_const_lt hp] with q hq
    exact smoothCuspSeedField_eq a b s ha hab q hq
  exact (smoothCuspSeed_contDiffAt a b s ha hab p hp).congr_of_eventuallyEq heq

theorem actual_smoothCuspSeed_laplace_defect (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (smoothCuspSeedField a b s) p-s*(s-2)*smoothCuspSeedField a b s p=
      smoothCuspSeedDefectField a b s p := by
  rw [axisLaplacian_congr_positive _ _ (fun q hq => smoothCuspSeedField_eq a b s ha hab q hq) p hp,
    smoothCuspSeedField_eq a b s ha hab p hp,smoothCuspSeedDefectField_eq a b s ha hab p hp]
  exact heightPoincare_cuspSeed_laplace_defect a b s ha hab p hp

lemma cuspSeedProfile_entire (a b v : ℝ) : Differentiable ℂ (fun s => cuspSeedProfile a b s v) := by
  unfold cuspSeedProfile positiveHeightPower logRatioPower
  fun_prop
lemma cuspSeedDefectProfile_entire (a b v : ℝ) : Differentiable ℂ (fun s => cuspSeedDefectProfile a b s v) := by
  unfold cuspSeedDefectProfile positiveHeightPower logRatioPower
  fun_prop

lemma cuspCutoffCorrection_parameter_entire (F : ℂ → ℝ → ℂ)
    (hF : ∀v,Differentiable ℂ (fun s => F s v)) (w : HyperbolicSpace) :
    Differentiable ℂ (fun s => cuspCutoffCorrection 1 (F s) w) := by
  let S := (high_cosets_finite 1 le_rfl w).toFinset
  have heq : (fun s => cuspCutoffCorrection 1 (F s) w)=
      (fun s => ∑r∈S,cuspCutoffTerm 1 (F s) r w) := by
    funext s
    apply tsum_eq_sum
    intro r hr
    have hh : ¬1<cosetHeight r w := by simpa only [S,Set.Finite.mem_toFinset,Set.mem_ofPred_eq] using hr
    simp [cuspCutoffTerm,hh]
  rw [heq]
  apply Differentiable.fun_sum
  intro r hr
  unfold cuspCutoffTerm
  split_ifs
  · exact (differentiable_const _).mul (hF _)
  · exact differentiable_const _

theorem smoothCuspSeed_entire (a b : ℝ) (w : HyperbolicSpace) :
    Differentiable ℂ (fun s => smoothCuspSeed a b s w) :=
  cuspCutoffCorrection_parameter_entire _ (cuspSeedProfile_entire a b) w

theorem smoothCuspSeedDefect_entire (a b : ℝ) (w : HyperbolicSpace) :
    Differentiable ℂ (fun s => smoothCuspSeedDefect a b s w) :=
  cuspCutoffCorrection_parameter_entire _ (cuspSeedDefectProfile_entire a b) w

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

def sectorBadIdeal (E : fixedBadPrimes.powerset) : Ideal O := ∏ P ∈ E.val, P

theorem sector_bad_good_product (I : Ideal O) (hI : Squarefree I)
    (E : fixedBadPrimes.powerset) (hE : badPrimeSector I = E) :
    sectorBadIdeal E * goodSquarefreePart I = I := by
  have hs : badPrimeSupport I = E.val := congrArg Subtype.val hE
  simpa only [hs, sectorBadIdeal] using squarefree_bad_good_product I hI

theorem sectorBadIdeal_ne_zero_of_row (I : Ideal O) (hI : Squarefree I)
    (E : fixedBadPrimes.powerset) (hE : badPrimeSector I = E) : sectorBadIdeal E ≠ 0 := by
  intro hz
  have hp := sector_bad_good_product I hI E hE
  rw [hz, zero_mul] at hp
  exact hI.ne_zero hp.symm

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def unrestrictedPairTerm (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (i : m) (j : n) (k : p) : ℂ :=
  if IsCoprime (left j) (right k) then
    star (a j) * b k * unrestrictedPairCharacter (left j) (right k) (rows i) else 0

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem unrestrictedPairTerm_sector (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ)
    (hrows : ∀ i, Squarefree (rows i)) (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E) (i : m) (j : n) (k : p) :
    unrestrictedPairTerm rows left right a b i j k =
      originalTerm (fun i => goodSquarefreePart (rows i)) left right
        (fun j => a j * quadraticRow (left j) (idealGenerator (sectorBadIdeal E)))
        (fun k => b k * quadraticRow (right k) (idealGenerator (sectorBadIdeal E))) 1 1 i j k := by
  classical
  by_cases hc : IsCoprime (left j) (right k)
  · simp only [unrestrictedPairTerm, originalTerm, hc, ite_true, one_dvd]
    have hp := unrestrictedPairCharacter_squarefree_bad_split (left j) (right k) (rows i)
      (hleft j) (hright k) (hray j k) (hrows i)
    have hs : badPrimeSupport (rows i) = E.val := congrArg Subtype.val (hE i)
    rw [hp, hs]
    simp only [sectorBadIdeal, unrestrictedPairCharacter, star_mul,
      canonical_quadraticRow_star _ (hleft j)]
    ring
  · simp only [unrestrictedPairTerm, originalTerm, hc, ite_false]

def unrestrictedDualTruncatedMiddle (W : 𝓢(ℝ, ℂ))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows left right a b i j k *
    (((M / (Real.sqrt ((Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ)) * F) : ℝ) : ℂ) *
      middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ)))) (Y i) (Z i) lengthScale)

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem unrestrictedDualTruncatedMiddle_sector
    (W : 𝓢(ℝ, ℂ)) (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hrows : ∀ i, Squarefree (rows i)) (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E)
    (hQ : sectorBadIdeal E ≠ 0) :
    unrestrictedDualTruncatedMiddle W rows left right a b M F Y Z lengthScale =
      ((1 / (Ideal.absNorm (sectorBadIdeal E) : ℝ) : ℝ) : ℂ) *
        dualTruncatedMiddle W (fun i => goodSquarefreePart (rows i)) left right
          (fun j => a j * quadraticRow (left j) (idealGenerator (sectorBadIdeal E)))
          (fun k => b k * quadraticRow (right k) (idealGenerator (sectorBadIdeal E)))
          (M * (Ideal.absNorm (sectorBadIdeal E) : ℝ)) F Y Z lengthScale := by
  classical
  have hQn : (Ideal.absNorm (sectorBadIdeal E) : ℝ) ≠ 0 := by
    exact_mod_cast (show Ideal.absNorm (sectorBadIdeal E) ≠ 0 from fun h => hQ (Ideal.absNorm_eq_zero_iff.mp h))
  unfold unrestrictedDualTruncatedMiddle dualTruncatedMiddle
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [unrestrictedPairTerm_sector rows left right a b hrows hleft hright hray E hE i j k]
  have hn : (Ideal.absNorm (rows i) : ℝ) =
      (Ideal.absNorm (sectorBadIdeal E) : ℝ) * (Ideal.absNorm (goodSquarefreePart (rows i)) : ℝ) := by
    calc
      (Ideal.absNorm (rows i) : ℝ) =
          (Ideal.absNorm (sectorBadIdeal E * goodSquarefreePart (rows i)) : ℝ) :=
        congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ))
          (sector_bad_good_product (rows i) (hrows i) E (hE i)).symm
      _ = _ := by rw [map_mul, Nat.cast_mul]
  rw [hn]
  have harg : F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
      (M * ((Ideal.absNorm (sectorBadIdeal E) : ℝ) * (Ideal.absNorm (goodSquarefreePart (rows i)) : ℝ))) =
    F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
      ((M * (Ideal.absNorm (sectorBadIdeal E) : ℝ)) * (Ideal.absNorm (goodSquarefreePart (rows i)) : ℝ)) := by ring
  rw [harg]
  have hs : (M / (Real.sqrt ((Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ)) * F) : ℝ) =
      (1 / (Ideal.absNorm (sectorBadIdeal E) : ℝ)) *
        ((M * (Ideal.absNorm (sectorBadIdeal E) : ℝ)) /
          (Real.sqrt ((Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ)) * F)) := by
    field_simp [hQn]
  rw [hs, Complex.ofReal_mul]
  ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss

lemma divisorEnergyFactor_mono_coefficients {n p : Type*} [Fintype n] [Fintype p]
    (ε : ℝ) (hε : 0 < ε) (N : ℝ) (a a' : n → ℂ) (b b' : p → ℂ)
    (ha : ∀ j, ‖a' j‖ ≤ ‖a j‖) (hb : ∀ k, ‖b' k‖ ≤ ‖b k‖) :
    divisorEnergyFactor ε hε N a' b' ≤ divisorEnergyFactor ε hε N a b := by
  have hA : (∑ j, ‖a' j‖ ^ 2) ≤ ∑ j, ‖a j‖ ^ 2 :=
    Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (ha j) _)
  have hB : (∑ k, ‖b' k‖ ^ 2) ≤ ∑ k, ‖b k‖ ^ 2 :=
    Finset.sum_le_sum (fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hb k) _)
  have hs := (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le
  have hd := (DivisorBlockCauchy.divisorConstant_pos ε hε).le
  unfold divisorEnergyFactor
  gcongr

lemma dual_bad_sector_scale (M F B Q U α : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 ≤ B) (hQ : 1 ≤ Q)
    (hU : 0 ≤ U) (hα : 1 / 2 ≤ α) :
    (1 / Q) * (M * Q / F + (2 * U) * Real.sqrt (M * Q / F) * (B / Q) ^ (α - 1 / 2)) ≤
      M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2) := by
  have hQp : 0 < Q := by linarith
  have hpow : (B / Q) ^ (α - 1 / 2) ≤ B ^ (α - 1 / 2) :=
    Real.rpow_le_rpow (by positivity) (div_le_self hB hQ) (by linarith)
  have hsQ : Real.sqrt Q ≤ Q := Real.sqrt_le_self_iff.mpr (Or.inr hQ)
  have hs : (1 / Q) * Real.sqrt (M * Q / F) ≤ Real.sqrt (M / F) := by
    have he : M * Q / F = (M / F) * Q := by ring
    rw [he, Real.sqrt_mul (by positivity)]
    have ht : Real.sqrt Q / Q ≤ 1 := (div_le_one hQp).mpr hsQ
    calc
      _ = Real.sqrt (M / F) * (Real.sqrt Q / Q) := by ring
      _ ≤ Real.sqrt (M / F) * 1 := mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg _)
      _ = _ := mul_one _
  calc
    _ = M / F + (2 * U) * ((1 / Q) * Real.sqrt (M * Q / F)) * (B / Q) ^ (α - 1 / 2) := by
      field_simp

    _ ≤ _ := by gcongr

def dualMiddleMajorant {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U : ℝ) (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) : ℝ :=
  ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
    ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
      divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
        (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2)))

lemma dualMiddleMajorant_nonneg {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U : ℝ) (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ))
    (hB : 0 ≤ B) (hN : 0 ≤ N) (hM : 0 ≤ M) (hF : 0 ≤ F) (hU : 0 ≤ U) :
    0 ≤ dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W := by
  have hc := nonzeroLatticeEnvelopeConstant_nonneg
  have hW := dualMiddleDecayConstant_nonneg W
  have he := divisorEnergyFactor_nonneg ε hε N a b
  have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  unfold dualMiddleMajorant
  positivity

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem HasSieveExponent.dual_truncated_middle_sector {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1 / 2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Squarefree (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (hZ : ∀ i, Z i ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E) :
    ‖unrestrictedDualTruncatedMiddle W rows left right a b M F Y Z lengthScale‖ ≤
      dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W := by
  classical
  cases isEmpty_or_nonempty m with
  | inl hempty =>
    let := hempty
    simp only [unrestrictedDualTruncatedMiddle, Finset.univ_eq_empty, Finset.sum_empty, norm_zero]
    exact dualMiddleMajorant_nonneg hexp deltaLoss hδ ε hε B N M F U a b W (by linarith) (by linarith) hM.le hF.le hU
  | inr hnonempty =>
    let := hnonempty
    let i₀ : m := Classical.choice hnonempty
    let Q : ℝ := Ideal.absNorm (sectorBadIdeal E)
    let good := fun i => goodSquarefreePart (rows i)
    let a' := fun j => a j * quadraticRow (left j) (idealGenerator (sectorBadIdeal E))
    let b' := fun k => b k * quadraticRow (right k) (idealGenerator (sectorBadIdeal E))
    have hQnz := sectorBadIdeal_ne_zero_of_row (rows i₀) (hrows i₀).1 E (hE i₀)
    have hQ : 1 ≤ Q := by
      dsimp only [Q]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun h => hQnz (Ideal.absNorm_eq_zero_iff.mp h)))
    have hQp : 0 < Q := by linarith
    have hn (i : m) : (Ideal.absNorm (rows i) : ℝ) = Q * (Ideal.absNorm (good i) : ℝ) := by
      have hi := congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ))
        (sector_bad_good_product (rows i) (hrows i).1 E (hE i))
      simpa only [map_mul, Nat.cast_mul] using hi.symm
    have hgr : Function.Injective good := by
      intro i k h
      exact hr (goodSquarefreePart_injective_on_sector _ _ (hrows i).1 (hrows k).1
        ((hE i).trans (hE k).symm) h)
    have hg (i : m) : Admissible (good i) ∧ (B / Q) / 2 ≤ (Ideal.absNorm (good i) : ℝ) ∧
        (Ideal.absNorm (good i) : ℝ) ≤ B / Q := by
      refine ⟨goodSquarefreePart_admissible _, ?_, ?_⟩
      · rw [show B / Q / 2 = (B / 2) / Q by ring]
        apply (div_le_iff₀ hQp).2
        have hx := (hrows i).2.1
        rw [hn i] at hx
        nlinarith
      · exact (le_div_iff₀ hQp).2 (by simpa only [mul_comm] using (hn i).symm.trans_le (hrows i).2.2)
    have hBQ : 1 ≤ B / Q := by
      have hh : 1 ≤ (Ideal.absNorm (good i₀) : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun h => (hg i₀).1.1 (Ideal.absNorm_eq_zero_iff.mp h)))
      exact hh.trans (hg i₀).2.2
    have hZa (i : m) : Z i ≤ U * (N * Real.sqrt (F / ((M * Q) * (Ideal.absNorm (good i) : ℝ)))) := by
      simpa only [hn i, mul_assoc] using hZ i
    have hbnd := hexp.dual_truncated_middle deltaLoss hδ ε hε (B / Q) N (M * Q) F U hBQ hN
      (by positivity) hF hU good left right hgr hl hri hg a' b' W Y Z lengthScale hleft hright hZa
    change ‖dualTruncatedMiddle W good left right a' b' (M * Q) F Y Z lengthScale‖ ≤
      dualMiddleMajorant hexp deltaLoss hδ ε hε (B / Q) N (M * Q) F U a' b' W at hbnd
    have htr := unrestrictedDualTruncatedMiddle_sector W rows left right a b M F Y Z lengthScale
      (fun i => (hrows i).1) (fun j => (hleft j).1) (fun k => (hright k).1) hray E hE hQnz
    change unrestrictedDualTruncatedMiddle W rows left right a b M F Y Z lengthScale =
      ((1 / Q : ℝ) : ℂ) * dualTruncatedMiddle W good left right a' b' (M * Q) F Y Z lengthScale at htr
    rw [htr, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / Q)]
    apply (mul_le_mul_of_nonneg_left hbnd (by positivity)).trans
    have hae (j : n) : ‖a' j‖ ≤ ‖a j‖ := by
      dsimp only [a']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)
    have hbe (k : p) : ‖b' k‖ ≤ ‖b k‖ := by
      dsimp only [b']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)
    have he := divisorEnergyFactor_mono_coefficients ε hε N a a' b b' hae hbe
    have hp : ((B / Q) * N) ^ deltaLoss ≤ (B * N) ^ deltaLoss := by
      apply Real.rpow_le_rpow (by positivity) _ hδ.le
      exact mul_le_mul_of_nonneg_right (div_le_self (by linarith) hQ) (by linarith)
    have hs := dual_bad_sector_scale M F B Q U α hM hF (by linarith) hQ hU hα
    have hc := nonzeroLatticeEnvelopeConstant_nonneg
    have hW := dualMiddleDecayConstant_nonneg W
    have hea := divisorEnergyFactor_nonneg ε hε N a' b'
    have heb := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    unfold dualMiddleMajorant
    calc
      _ = ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a' b' * (divisorExponentConstant hexp deltaLoss hδ * ((B / Q) * N) ^ deltaLoss) *
            ((1 / Q) * (M * Q / F + (2 * U) * Real.sqrt (M * Q / F) * (B / Q) ^ (α - 1 / 2)))) := by ring
      _ ≤ _ := by gcongr

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem HasSieveExponent.unrestricted_dual_truncated_middle {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1 / 2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Squarefree (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (hZ : ∀ i, Z i ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) :
    ‖unrestrictedDualTruncatedMiddle W rows left right a b M F Y Z lengthScale‖ ≤
      4 * dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W := by
  classical
  let σ := fun i => badPrimeSector (rows i)
  have hs : unrestrictedDualTruncatedMiddle W rows left right a b M F Y Z lengthScale =
      ∑ E : fixedBadPrimes.powerset,
        unrestrictedDualTruncatedMiddle W (fun i : {i // σ i = E} => rows i.val)
          left right a b M F (fun i => Y i.val) (fun i => Z i.val) lengthScale := by
    unfold unrestrictedDualTruncatedMiddle
    exact (Fintype.sum_fiberwise σ _).symm
  have hb (E : fixedBadPrimes.powerset) :
      ‖unrestrictedDualTruncatedMiddle W (fun i : {i // σ i = E} => rows i.val)
          left right a b M F (fun i => Y i.val) (fun i => Z i.val) lengthScale‖ ≤
        dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W := by
    apply hexp.dual_truncated_middle_sector hα deltaLoss hδ ε hε B N M F U hB hN hM hF hU
      (fun i : {i // σ i = E} => rows i.val) left right
      (fun i k h => Subtype.ext (hr h)) hl hri (fun i => hrows i.val) a b W
      (fun i => Y i.val) (fun i => Z i.val) lengthScale hleft hright hray (fun i => hZ i.val) E
    exact fun i => i.property
  rw [hs]
  calc
    _ ≤ ∑ E : fixedBadPrimes.powerset,
        ‖unrestrictedDualTruncatedMiddle W (fun i : {i // σ i = E} => rows i.val)
          left right a b M F (fun i => Y i.val) (fun i => Z i.val) lengthScale‖ := norm_sum_le _ _
    _ ≤ ∑ _E : fixedBadPrimes.powerset, dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W :=
      Finset.sum_le_sum (fun E _ => hb E)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe,
        fixedBadPrimes_powerset_card]
      norm_num

end CanonicalQuadraticSieve

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondChildColumn_fixed_mask (Ψ : O →* ℂ) (m g f y : O)
    (H : Finset ι → ℂ) (U : Finset ι) :
    secondChildColumn p hp hcop hg Ψ (m*g) f y H U =
      rowCoprimeMask (fun i => Ideal.span {p i}) U g * secondChildColumn p hp hcop hg Ψ m f y H U := by
  simp only [secondChildColumn,FirstPassCubeLabels.mask_mul _ hg U m g]
  ring

theorem fixedChildRow_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F A : Finset ι) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (f y : O) :
    fixedChildRow p hp hcop hg (F\A) Ψ m H f y =
      fixedChildRow p hp hcop hg F Ψ (m*∏ i ∈ A,p i) H f y := by
  unfold fixedChildRow
  rw [sum_remove_common_pool p hg hinj F A]
  apply Finset.sum_congr rfl
  intro U hU
  exact (secondChildColumn_fixed_mask p hp hcop hg Ψ m _ f y H U).symm

end SecondPassArithmetic

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

theorem childEnergy_fixed_pool (F A : Finset ι) (Ψ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (V : ℝ → ℂ) (X : ℝ) (negative rowNegative : Bool) (a b : ℝ) :
    childEnergy p hp hcop hg (F\A) Ψ m T V X negative rowNegative a b =
      childEnergy p hp hcop hg F Ψ (m*∏ i ∈ A,p i) T V X negative rowNegative a b := by
  simp only [childEnergy,idealChildRow,fixedChildRow_fixed_pool p hp hcop hg hinj]

theorem childGeometricMean_fixed_pool (F A : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (q : JointLogSeparation.Frequency) :
    childGeometricMean p hp hcop hg (F\A) Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ q =
      childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ (m*∏ i ∈ A,p i) T V₁ V₂ X₁ X₂ q := by
  simp only [childGeometricMean,childEnergy_fixed_pool p hp hcop hg hinj]

theorem densityChildEnergy_fixed_pool (F A : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (J : ℕ) :
    densityChildEnergy p hp hcop hg (F\A) Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ J =
      densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ (m*∏ i ∈ A,p i) T V₁ V₂ X₁ X₂ J := by
  simp only [densityChildEnergy,childGeometricMean_fixed_pool p hp hcop hg hinj]

end

open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (primeProductNorm)

theorem restored_child_mask_norm {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (m b0 : O) (R A : Finset ι) :
    ‖eisEmbedding ((m*b0*primeSubsetGenerator (fun i => Ideal.span {p i}) R)*∏ i ∈ A,p i)‖^2 =
      ‖eisEmbedding m‖^2*‖eisEmbedding b0‖^2*primeProductNorm p R*primeProductNorm p A := by
  simp only [map_mul,norm_mul,mul_pow,SecondPassArithmetic.primeSubsetGenerator_norm_eq_productNorm,
    primeProductNorm]

end SecondPassIntegration

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct primeProductNorm squarefreeLabel jLabel j2Label b0Label
  bit parity conductorExponent cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

lemma element_norm_le_of_dvd {a b : O} (hb : b ≠ 0) (h : a ∣ b) :
    ‖eisEmbedding a‖^2 ≤ ‖eisEmbedding b‖^2 := by
  obtain ⟨c,rfl⟩ := h
  have hc : c ≠ 0 := (mul_ne_zero_iff.mp hb).2
  rw [map_mul, norm_mul, mul_pow]
  exact le_mul_of_one_le_right (sq_nonneg _) (element_norm_ge_one c hc)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma primeProduct_ne_zero (B : Finset ι) (v : ι → ℕ) : primeProduct p B v ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _hi => pow_ne_zero _ (hp i))

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma squarefreeLabel_active_bound (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    ‖eisEmbedding (squarefreeLabel p B v)‖^2 ≤ primeProductNorm p (cubeActiveSupport B v ε₁ ε₂) := by
  let S := B.filter (fun i => parity (v i))
  have he : squarefreeLabel p B v = ∏ i ∈ S, p i := by
    unfold squarefreeLabel primeProduct S
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i hi
    cases hb : parity (v i) <;> simp [bit,hb]
  have hsub : S ⊆ cubeActiveSupport B v ε₁ ε₂ := by
    intro i hi
    obtain ⟨hi,hpi⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨hi,?_⟩
    change parity (v i) = true at hpi
    rw [hpi]
    cases h1 : ε₁ i <;> cases h2 : ε₂ i <;> decide
  rw [he]
  exact primeProductNorm_mono p hp hsub

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma jLabel_dvd_cube_product (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂ ∣ primeProduct p B v₁ * primeProduct p B v₂ := by
  rw [← primeProduct_add]
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  apply pow_dvd_pow
  dsimp only
  unfold bit
  split <;> have h := hv i hi <;> omega

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma b0_square_dvd_cube_product (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂ ^ 2 ∣ primeProduct p B v₁ * primeProduct p B v₂ := by
  rw [FirstPassCubeLabels.cube_pair_product_decomposition p B v₁ v₂ ε₁ ε₂ hv]
  exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma b0_jLabel_square (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    (b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂ * jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂)^2 =
      primeProduct p B v₁ * primeProduct p B v₂ * squarefreeLabel p B (fun i => v₁ i+v₂ i) := by
  rw [FirstPassCubeLabels.jLabel_eq_squarefree_mul_j2,
    FirstPassCubeLabels.cube_pair_product_decomposition p B v₁ v₂ ε₁ ε₂ hv]
  ring

include hp in

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cube_label_norm_bounds (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) (B₀ : ℝ) (hB : 0 ≤ B₀)
    (hb₁ : ‖eisEmbedding (primeProduct p B v₁)‖^2 ≤ B₀)
    (hb₂ : ‖eisEmbedding (primeProduct p B v₂)‖^2 ≤ B₀) :
    let v := fun i => v₁ i+v₂ i
    ‖eisEmbedding (jLabel p B v ε₁ ε₂)‖^2 ≤ B₀^2 ∧
    ‖eisEmbedding (b0Label p B v ε₁ ε₂)‖^2 ≤ B₀ ∧
    ‖eisEmbedding (b0Label p B v ε₁ ε₂)‖^2 ≤
      B₀*‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂,p i)‖ /
        ‖eisEmbedding (jLabel p B v ε₁ ε₂)‖^2 := by
  dsimp only
  have hbb : ‖eisEmbedding (primeProduct p B v₁ * primeProduct p B v₂)‖^2 ≤ B₀^2 := by
    rw [map_mul,norm_mul,mul_pow]
    simpa only [pow_two] using mul_le_mul hb₁ hb₂ (sq_nonneg _) hB
  have hbb0 := mul_ne_zero (primeProduct_ne_zero p hp B v₁) (primeProduct_ne_zero p hp B v₂)
  have hJ := (element_norm_le_of_dvd hbb0 (jLabel_dvd_cube_product p B v₁ v₂ ε₁ ε₂ hv)).trans hbb
  have hb0sq := (element_norm_le_of_dvd hbb0 (b0_square_dvd_cube_product p B v₁ v₂ ε₁ ε₂ hv)).trans hbb
  simp only [map_pow,norm_pow] at hb0sq
  have hb0 : ‖eisEmbedding (b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂)‖^2 ≤ B₀ := by
    nlinarith [sq_nonneg ‖eisEmbedding (b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂)‖]
  refine ⟨hJ,hb0,?_⟩
  have heq := congrArg (fun a : O => ‖eisEmbedding a‖^2) (b0_jLabel_square p B v₁ v₂ ε₁ ε₂ hv)
  simp only [map_pow,map_mul,norm_pow,norm_mul,mul_pow] at heq
  have hs := squarefreeLabel_active_bound p hp B (fun i => v₁ i+v₂ i) ε₁ ε₂
  have hNprod : ‖eisEmbedding (primeProduct p B v₁)‖^2 * ‖eisEmbedding (primeProduct p B v₂)‖^2 ≤ B₀^2 := by
    simpa only [map_mul,norm_mul,mul_pow] using hbb
  have hmul := mul_le_mul hNprod hs (sq_nonneg _) (sq_nonneg B₀)
  change _ ≤ B₀^2*‖eisEmbedding (∏ i ∈ cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)‖^2 at hmul
  have hjpos : 0 < ‖eisEmbedding (jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂)‖^2 := by
    exact zero_lt_one.trans_le (element_norm_ge_one _ (primeProduct_ne_zero p hp B _))
  apply (le_div_iff₀ hjpos).mpr
  apply (sq_le_sq₀ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (mul_nonneg hB (norm_nonneg _))).mp
  simp only [mul_pow]
  exact heq.trans_le hmul

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0160

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.GlobalEncoding
Source SHA256: cf5cf6c8e52b2ff49b42572b50705b7580ed3be6ae647acdfed0dbd7bf6ea5a3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0161


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

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic

section
variable {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
  [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
include hinj

theorem primeIdealProduct_emultiplicity (S : Finset ι) (v : ι → ℕ) (i : ι) :
    emultiplicity (P i) (∏ j ∈ S, P j ^ v j) = if i ∈ S then (v i : ℕ∞) else 0 := by
  have hp (j : ι) : Prime (P j) := Ideal.prime_of_isPrime (NeZero.ne (P j)) inferInstance
  rw [Finset.emultiplicity_prod (hp i)]
  have hz (j : ι) (hji : j ≠ i) : emultiplicity (P i) (P j ^ v j) = 0 := by
    rw [emultiplicity_pow (hp i), emultiplicity_eq_zero_of_irreducible_ne
      (hp i).irreducible (hp j).irreducible (fun he => hji (hinj he).symm), mul_zero]
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi,Finset.sum_eq_single i]
    · exact emultiplicity_pow_self_of_prime (hp i) (v i)
    · intro j hj hji
      exact hz j hji
    · exact fun hn => (hn hi).elim
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j hj
    exact hz j (fun he => hi (he ▸ hj))

theorem primeIdealProduct_exponents_eq
    (B C : Finset ι) (v w : ι → ℕ)
    (hv : ∀ i, i ∉ B → v i = 0) (hw : ∀ i, i ∉ C → w i = 0)
    (heq : (∏ i ∈ B, P i ^ v i) = ∏ i ∈ C, P i ^ w i) : v = w := by
  funext i
  have he := congrArg (fun I => emultiplicity (P i) I) heq
  rw [primeIdealProduct_emultiplicity P hinj,primeIdealProduct_emultiplicity P hinj] at he
  have hB : (if i ∈ B then (v i : ℕ∞) else 0) = (v i : ℕ∞) := by
    by_cases h : i ∈ B <;> simp [h,hv i]
  have hC : (if i ∈ C then (w i : ℕ∞) else 0) = (w i : ℕ∞) := by
    by_cases h : i ∈ C <;> simp [h,hw i]
  rw [hB,hC] at he
  exact_mod_cast he

end

theorem primeProduct_span_exponents_eq {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (B C : Finset ι) (v w : ι → ℕ)
    (hv : ∀ i, i ∉ B → v i = 0) (hw : ∀ i, i ∉ C → w i = 0)
    (heq : Ideal.span {FirstPassCubeLabels.primeProduct p B v} =
      Ideal.span {FirstPassCubeLabels.primeProduct p C w}) : v = w := by
  apply primeIdealProduct_exponents_eq (fun i => Ideal.span {p i}) hinj B C v w hv hw
  simpa only [FirstPassCubeLabels.primeProduct,FiniteGaussPhase.span_finset_prod,
    ←Ideal.span_singleton_pow] using heq

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem divisor_dyadic_sum_le (S T : Finset (Ideal O)) (N : ℝ)
    (f : Ideal O → Ideal O → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ j k : Fin (columnDyadicLength N + 1),
      (divisorDyadicBin S N j).Nonempty → (divisorDyadicBin T N k).Nonempty →
      (∑ D ∈ divisorDyadicBin S N j, ∑ E ∈ divisorDyadicBin T N k, f D E) ≤ C) :
    (∑ D ∈ S, ∑ E ∈ T, f D E) ≤ ((columnDyadicLength N + 1 : ℕ) : ℝ)^2 * C := by
  rw [sum_divisorDyadicRectangles S T N f]
  calc
    _ ≤ ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1), C := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      by_cases hS : (divisorDyadicBin S N j).Nonempty
      · by_cases hT : (divisorDyadicBin T N k).Nonempty
        · exact hb j k hS hT
        · simpa only [Finset.not_nonempty_iff_eq_empty.mp hT, Finset.sum_empty, Finset.sum_const_zero] using hC
      · simpa only [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.sum_empty] using hC
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_two]; ring

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def largePrincipalWindow (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) : ℝ := by
  classical
  exact ∑ D ∈ S, ∑ E ∈ T, ∑ i, if P (D*E) i then
    (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D : ℝ)*(Ideal.absNorm E : ℝ))) *
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma largePrincipalWindow_le (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) :
    largePrincipalWindow S T rows left right a b M P ≤
      principalCorrectionAt S T rows left right a b M := by
  classical
  unfold principalCorrectionAt
  rw [sum_two_subtype_pools S T (fun D E => ∑ i,
    (Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/((Ideal.absNorm D:ℝ)*(Ideal.absNorm E:ℝ)))*
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k‖)]
  unfold largePrincipalWindow
  apply Finset.sum_le_sum
  intro D _
  apply Finset.sum_le_sum
  intro E _
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> first | exact le_rfl | positivity

theorem HasSieveExponent.large_principal_window {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M V : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hM : 0 < M) (hV : 0 ≤ V) (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2*D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2*D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ D ∈ S, ∀ E ∈ T, ∀ i, P (D*E) i →
      Real.sqrt (M/B)*N ≤ (V/4)*(Ideal.absNorm (D*E):ℝ)) :
    largePrincipalWindow S T rows left right a b M P ≤
      2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (V+Real.sqrt M*B^(α-1/2)) := by
  classical
  by_cases hc : Real.sqrt (M/B)*N ≤ V*(D₁*D₂)
  · exact (largePrincipalWindow_le S T rows left right a b M P).trans
      (HasSieveExponent.large_principal_correction ε hε S T D₁ D₂ B N M hD₁ hD₂ hB hN hM hS hT
        rows left right hr hl hri hrows hleft hright a b hexp deltaLoss hδ hD₁N hD₂N V hc)
  · have hz : largePrincipalWindow S T rows left right a b M P = 0 := by
      unfold largePrincipalWindow
      apply Finset.sum_eq_zero
      intro D hD
      apply Finset.sum_eq_zero
      intro E hE
      apply Finset.sum_eq_zero
      intro i _
      have hn : ¬P (D*E) i := by
        intro hp
        apply hc
        have hlo := hP D hD E hE i hp
        have hhi : (Ideal.absNorm (D*E):ℝ) ≤ 4*(D₁*D₂) := by
          rw [map_mul, Nat.cast_mul]
          calc
            _ ≤ (2*D₁)*(2*D₂) := mul_le_mul (hS D hD).2 (hT E hE).2 (by positivity) (by linarith)
            _ = _ := by ring
        nlinarith
      simp only [hn, ite_false]
    rw [hz]
    have he := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity

theorem HasSieveExponent.large_principal_pool {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (B N M V : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hV : 0 ≤ V)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D:ℝ) ∧ (Ideal.absNorm D:ℝ) ≤ N)
    (hT : ∀ E ∈ T, 1 ≤ (Ideal.absNorm E:ℝ) ∧ (Ideal.absNorm E:ℝ) ≤ N)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ D ∈ S, ∀ E ∈ T, ∀ i, P (D*E) i →
      Real.sqrt (M/B)*N ≤ (V/4)*(Ideal.absNorm (D*E):ℝ)) :
    largePrincipalWindow S T rows left right a b M P ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (V+Real.sqrt M*B^(α-1/2))) := by
  classical
  apply divisor_dyadic_sum_le S T N _ _
  · have he := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity
  · intro j k hj hk
    exact hexp.large_principal_window deltaLoss hδ ε hε (divisorDyadicBin S N j) (divisorDyadicBin T N k)
      (divisorDyadicScale j.val) (divisorDyadicScale k.val) B N M V
      (divisorDyadicScale_ge_one _) (divisorDyadicScale_ge_one _) hB hN hM hV
      (divisorDyadicBin_scale_le S N hS j hj) (divisorDyadicBin_scale_le T N hT k hk)
      (divisorDyadicBin_bounds S N hS j) (divisorDyadicBin_bounds T N hT k)
      rows left right hr hl hri hrows hleft hright a b P
      (fun D hD E hE i hp => hP D (Finset.mem_filter.mp hD).1 E (Finset.mem_filter.mp hE).1 i hp)

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem finite_principal_triangle
    {m n p D : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype D]
    (muCoefficient : D → ℂ) (hμ : ∀ d, ‖muCoefficient d‖ ≤ 1) (A : m → n → p → D → ℂ) :
    ‖∑ i, ∑ j, ∑ k, ∑ d, muCoefficient d * A i j k d‖ ≤
      ∑ i, ∑ d, ‖∑ j, ∑ k, A i j k d‖ := by
  classical
  have he : (∑ i, ∑ j, ∑ k, ∑ d, muCoefficient d * A i j k d) =
      ∑ i, ∑ d, muCoefficient d * (∑ j, ∑ k, A i j k d) := by
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset p)) (t := (Finset.univ : Finset D)),
      Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset D))]
    simp only [Finset.mul_sum]
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hμ d)

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def principalDivisorCorrection (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) : ℂ := by
  classical
  exact ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    ∑ d ∈ idealDivisors (left j*right k), if P d i then
      (UniqueFactorizationMonoid.moebius d : ℂ) *
        ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0

def largePrincipalProductAt (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) : ℝ := by
  classical
  exact ∑ i, ∑ d ∈ K, if P d i then
    ‖∑ j, ∑ k, if d ∣ left j*right k then originalTerm rows left right a b 1 1 i j k *
      ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma largePrincipalProductAt_le_window (K S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T) :
    largePrincipalProductAt K rows left right a b M P ≤
      largePrincipalWindow S T rows left right a b M (fun d i => d ∈ K ∧ P d i) := by
  classical
  have hp (i : m) := originalColumnSum_divisor_rectangles K S T rows left right a b i
    hleft hright hS hT P
    (fun d i _ _ => ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ))
  apply (Finset.sum_le_sum (fun i _ => hp i)).trans_eq
  unfold largePrincipalWindow
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E _
  apply Finset.sum_congr rfl
  intro i _
  by_cases hd : D*E ∈ K
  · by_cases hi : P (D*E) i
    · simp only [hd, hi, and_self, ite_true, map_mul, Nat.cast_mul]
      simp only [←Finset.sum_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/
          ((Ideal.absNorm D:ℝ)*(Ideal.absNorm E:ℝ)) by positivity)]
      ring
    · simp only [hd, hi, and_false, ite_true, ite_false]
  · simp only [hd, false_and, ite_false]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma principalDivisorCorrection_le_product (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hK : ∀ j k d, d ∣ left j*right k → d ∈ K) :
    ‖principalDivisorCorrection rows left right a b M P‖ ≤
      largePrincipalProductAt K rows left right a b M P := by
  classical
  let A : m → n → p → K → ℂ := fun i j k d => if P d.val i then
    if d.val ∣ left j*right k then originalTerm rows left right a b 1 1 i j k *
      ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d.val:ℝ):ℝ):ℂ) else 0 else 0
  have he : principalDivisorCorrection rows left right a b M P =
      ∑ i, ∑ j, ∑ k, ∑ d : K, (UniqueFactorizationMonoid.moebius d.val : ℂ)*A i j k d := by
    unfold principalDivisorCorrection
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [← divisorPool_filter K (left j*right k) (mul_ne_zero (hleft j) (hright k)) (hK j k),
      Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_coe_sort K (fun d => (UniqueFactorizationMonoid.moebius d:ℂ)*
      (if P d i then if d ∣ left j*right k then originalTerm rows left right a b 1 1 i j k *
        ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0 else 0))]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : d ∣ left j*right k <;> by_cases hi : P d i <;>
      simp only [hd, hi, ite_true, ite_false, mul_zero] ; ring
  rw [he]
  apply (finite_principal_triangle (fun d : K => (UniqueFactorizationMonoid.moebius d.val:ℂ))
    (fun d => QuadraticInitialBound.norm_ideal_moebius_le_one d.val) A).trans_eq
  unfold largePrincipalProductAt
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_coe_sort K (fun d => ‖∑ j, ∑ k, if P d i then
    if d ∣ left j*right k then originalTerm rows left right a b 1 1 i j k *
      ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0 else 0‖)]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : P d i <;> simp only [hd, ite_true, ite_false, Finset.sum_const_zero, norm_zero]

theorem HasSieveExponent.principal_divisor_correction {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M V : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hV : 0 ≤ V)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ d i, P d i → Real.sqrt (M/B)*N ≤ (V/4)*(Ideal.absNorm d:ℝ)) :
    ‖principalDivisorCorrection rows left right a b M P‖ ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (V+Real.sqrt M*B^(α-1/2))) := by
  let S := columnDivisorPool left
  let T := columnDivisorPool right
  let pairCols : n × p → Ideal O := fun x => left x.1*right x.2
  let K := columnDivisorPool pairCols
  have hl0 : ∀ j, left j ≠ 0 := fun j => (hleft j).1.1
  have hr0 : ∀ k, right k ≠ 0 := fun k => (hright k).1.1
  have hp0 : ∀ x, pairCols x ≠ 0 := fun x => mul_ne_zero (hl0 x.1) (hr0 x.2)
  have hk : ∀ j k d, d ∣ left j*right k → d ∈ K :=
    fun j k d hd => mem_columnDivisorPool_of_dvd pairCols hp0 (j,k) d hd
  calc
    _ ≤ largePrincipalProductAt K rows left right a b M P :=
      principalDivisorCorrection_le_product K rows left right a b M P hl0 hr0 hk
    _ ≤ largePrincipalWindow S T rows left right a b M (fun d i => d ∈ K ∧ P d i) :=
      largePrincipalProductAt_le_window K S T rows left right a b M P hl0 hr0
        (mem_columnDivisorPool_of_dvd left hl0) (mem_columnDivisorPool_of_dvd right hr0)
    _ ≤ _ := hexp.large_principal_pool deltaLoss hδ ε hε S T B N M V hB hN hM hV
      (columnDivisorPool_norm_bounds left hl0 N (fun j => (hleft j).2))
      (columnDivisorPool_norm_bounds right hr0 N (fun k => (hright k).2))
      rows left right hr hl hri hrows hleft hright a b _
      (fun D _ E _ i hp => hP (D*E) i hp.2)

end CanonicalQuadraticSieve

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct aLabel b0Label jLabel cubeActiveSupport primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

@[ext] structure CubeCoordinates (ι : Type*) where
  leftExponent : ι →₀ ℕ
  rightExponent : ι →₀ ℕ
  leftDivisor : Finset ι
  rightDivisor : Finset ι

namespace CubeCoordinates
variable {ι : Type*} [DecidableEq ι]

def support (x : CubeCoordinates ι) : Finset ι :=
  x.leftExponent.support ∪ x.rightExponent.support

def leftBit (x : CubeCoordinates ι) (i : ι) : Bool := decide (i ∈ x.leftDivisor)
def rightBit (x : CubeCoordinates ι) (i : ι) : Bool := decide (i ∈ x.rightDivisor)

def Admissible (x : CubeCoordinates ι) : Prop :=
  x.leftDivisor ⊆ x.support ∧ x.rightDivisor ⊆ x.support

theorem support_pos (x : CubeCoordinates ι) (i : ι) (hi : i ∈ x.support) :
    0 < x.leftExponent i+x.rightExponent i := by
  simp only [support,Finset.mem_union,Finsupp.mem_support_iff] at hi
  omega

theorem left_off (x : CubeCoordinates ι) (i : ι) (hi : i ∉ x.support) :
    x.leftExponent i=0 := by
  by_contra hv
  exact hi (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hv))

theorem right_off (x : CubeCoordinates ι) (i : ι) (hi : i ∉ x.support) :
    x.rightExponent i=0 := by
  by_contra hv
  exact hi (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hv))

theorem aLabel_left (p : ι → O) (x : CubeCoordinates ι) (hx : x.Admissible) :
    aLabel p x.support x.leftBit = ∏ i ∈ x.leftDivisor,p i := by
  simp only [aLabel,primeProduct,leftBit,FirstPassCubeLabels.bit,decide_eq_true_eq]
  simp_rw [apply_ite, pow_one, pow_zero]
  rw [← Finset.prod_filter]
  have he : x.support.filter (fun i => i ∈ x.leftDivisor)=x.leftDivisor := by
    ext i
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hi => hx.1 hi)
  rw [he]

theorem aLabel_right (p : ι → O) (x : CubeCoordinates ι) (hx : x.Admissible) :
    aLabel p x.support x.rightBit = ∏ i ∈ x.rightDivisor,p i := by
  simp only [aLabel,primeProduct,rightBit,FirstPassCubeLabels.bit,decide_eq_true_eq]
  simp_rw [apply_ite, pow_one, pow_zero]
  rw [← Finset.prod_filter]
  have he : x.support.filter (fun i => i ∈ x.rightDivisor)=x.rightDivisor := by
    ext i
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hi => hx.2 hi)
  rw [he]

end CubeCoordinates

@[ext] structure GlobalSecondData (ι : Type*) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  common : Finset ι
  firstDivisor : Finset ι
  source : SecondExpansionData ι

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

def globalSecondTuple (x : GlobalSecondData ι) : SecondPassFiber.OldTuple :=
  actualSecondTuple p x.cube.support x.common x.firstDivisor x.source.divisor x.source.overlap
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit x.source.frequency

def globalSecondFixedTriple (x : GlobalSecondData ι) : Ideal O × Ideal O × Ideal O :=
  (Ideal.span {b0Label p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit},
   ∏ i ∈ x.firstCommon,Ideal.span {p i},
   ∏ i ∈ x.source.sourceCommon\x.source.divisor,Ideal.span {p i})

def GlobalSecondAdmissible (x : GlobalSecondData ι) : Prop :=
  x.cube.Admissible ∧ x.source.divisor ⊆ x.source.sourceCommon ∧
  Disjoint x.common x.cube.support ∧ x.firstDivisor ⊆ x.common∪x.cube.support

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondTuple_valid (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x) :
    SecondPassFiber.Valid (globalSecondTuple p x)
      (SecondPassFiber.newLabel (globalSecondTuple p x))
      (globalSecondFixedTriple p x).1
      (SecondPassFiber.newRow (globalSecondTuple p x)) :=
  actualSecondTuple_valid p x.cube.support x.common x.firstDivisor x.source.divisor x.source.overlap
    hx.2.2.1 hx.2.2.2 x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
    x.cube.support_pos x.source.frequency

theorem globalSecondFixedTriple_nonzero (hp : ∀ i,p i ≠ 0) (x : GlobalSecondData ι) :
    (globalSecondFixedTriple p x).1 ≠ ⊥ ∧
    (globalSecondFixedTriple p x).2.1 ≠ ⊥ ∧
    (globalSecondFixedTriple p x).2.2 ≠ ⊥ := by
  refine ⟨sector_b0_ne_bot p hp _ _ _ _ _,?_,?_⟩ <;>
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => NeZero.ne (Ideal.span {p i}))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondFixedTriple_norm_bounds (hp : ∀ i,p i ≠ 0)
    (x : GlobalSecondData ι) (B H J T R : ℝ) (hB : 0 ≤ B) (hJ : 0 < J)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hactive : ‖eisEmbedding (∏ i ∈ cubeActiveSupport x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖ ≤ H)
    (hlabel : J ≤ ‖eisEmbedding (jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2)
    (ht : primeProductNorm p x.firstCommon ≤ T)
    (hr : primeProductNorm p (x.source.sourceCommon\x.source.divisor) ≤ R) :
    (Ideal.absNorm (globalSecondFixedTriple p x).1 : ℝ) ≤ B*H/J ∧
    (Ideal.absNorm (globalSecondFixedTriple p x).2.1 : ℝ) ≤ T ∧
    (Ideal.absNorm (globalSecondFixedTriple p x).2.2 : ℝ) ≤ R := by
  obtain ⟨_,_,hb0⟩ := cube_label_norm_bounds p hp x.cube.support
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
    x.cube.support_pos B hB hb₁ hb₂
  refine ⟨?_,?_,?_⟩
  · change (Ideal.absNorm (Ideal.span {_}) : ℝ) ≤ _
    rw [← eisEmbedding_norm_sq_eq_absNorm_span]
    apply hb0.trans
    exact div_le_div₀ (mul_nonneg hB ((norm_nonneg _).trans hactive))
      (mul_le_mul_of_nonneg_left hactive hB) hJ hlabel
  · exact (primeProductNorm_eq_ideal_norm p _).symm ▸ ht
  · exact (primeProductNorm_eq_ideal_norm p _).symm ▸ hr

theorem globalSecondFixedTriple_count (hp : ∀ i,p i ≠ 0)
    (s : Finset (GlobalSecondData ι)) (B H J T R : ℝ)
    (hB : 0 ≤ B) (hJ : 0 < J) (hscale : 1 ≤ B*H/J) (hT : 1 ≤ T) (hR : 1 ≤ R)
    (hb₁ : ∀ x∈s, ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x∈s, ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hactive : ∀ x∈s, ‖eisEmbedding (∏ i ∈ cubeActiveSupport x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖ ≤ H)
    (hlabel : ∀ x∈s, J ≤ ‖eisEmbedding (jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2)
    (ht : ∀ x∈s, primeProductNorm p x.firstCommon ≤ T)
    (hr : ∀ x∈s, primeProductNorm p (x.source.sourceCommon\x.source.divisor) ≤ R) :
    ((s.image (globalSecondFixedTriple p)).card : ℝ) ≤ 128^3*(B*H/J)*T*R := by
  apply DescentFiberCost.fixed_triple_count _ _ _ _ hscale hT hR
  · intro q hq
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact globalSecondFixedTriple_nonzero p hp x
  · intro q hq
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact globalSecondFixedTriple_norm_bounds p hp x B H J T R hB hJ
      (hb₁ x hx) (hb₂ x hx) (hactive x hx) (hlabel x hx) (ht x hx) (hr x hx)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem sum_globalSecondFixedTriple {M : Type*} [AddCommMonoid M]
    (s : Finset (GlobalSecondData ι)) (f : GlobalSecondData ι → M) :
    ∑ x∈s,f x = ∑ q∈s.image (globalSecondFixedTriple p),
      ∑ x∈s with globalSecondFixedTriple p x=q,f x := by
  symm
  exact Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩) f

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct aLabel)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

theorem globalSecondTuple_cube_eq {x y : GlobalSecondData ι}
    (hx : x.cube.Admissible) (hy : y.cube.Admissible)
    (h : globalSecondTuple p x=globalSecondTuple p y) : x.cube=y.cube := by
  have h₁ := congrArg (fun z : SecondPassFiber.OldTuple => z.core 4) h
  have h₂ := congrArg SecondPassFiber.OldTuple.b2 h
  have hA₁ := congrArg (fun z : SecondPassFiber.OldTuple => z.core 5) h
  have hA₂ := congrArg (fun z : SecondPassFiber.OldTuple => z.core 6) h
  change Ideal.span {primeProduct p x.cube.support x.cube.leftExponent} =
    Ideal.span {primeProduct p y.cube.support y.cube.leftExponent} at h₁
  change Ideal.span {primeProduct p x.cube.support x.cube.rightExponent} =
    Ideal.span {primeProduct p y.cube.support y.cube.rightExponent} at h₂
  have hv₁ := primeProduct_span_exponents_eq p hinj x.cube.support y.cube.support
    x.cube.leftExponent y.cube.leftExponent x.cube.left_off y.cube.left_off h₁
  have hv₂ := primeProduct_span_exponents_eq p hinj x.cube.support y.cube.support
    x.cube.rightExponent y.cube.rightExponent x.cube.right_off y.cube.right_off h₂
  change Ideal.span {aLabel p x.cube.support x.cube.leftBit} =
    Ideal.span {aLabel p y.cube.support y.cube.leftBit} at hA₁
  change Ideal.span {aLabel p x.cube.support x.cube.rightBit} =
    Ideal.span {aLabel p y.cube.support y.cube.rightBit} at hA₂
  rw [CubeCoordinates.aLabel_left p x.cube hx,CubeCoordinates.aLabel_left p y.cube hy,
    FiniteGaussPhase.span_finset_prod,FiniteGaussPhase.span_finset_prod] at hA₁
  rw [CubeCoordinates.aLabel_right p x.cube hx,CubeCoordinates.aLabel_right p y.cube hy,
    FiniteGaussPhase.span_finset_prod,FiniteGaussPhase.span_finset_prod] at hA₂
  apply CubeCoordinates.ext
  · exact Finsupp.ext (congrFun hv₁)
  · exact Finsupp.ext (congrFun hv₂)
  · exact FirstCauchyArithmetic.family_product_injective _ hinj hA₁
  · exact FirstCauchyArithmetic.family_product_injective _ hinj hA₂

theorem globalSecondEncoding_injective {x y : GlobalSecondData ι}
    (hx : GlobalSecondAdmissible x) (hy : GlobalSecondAdmissible y)
    (ht : globalSecondFixedTriple p x=globalSecondFixedTriple p y)
    (h : globalSecondTuple p x=globalSecondTuple p y) : x=y := by
  have hc := globalSecondTuple_cube_eq p hinj hx.1 hy.1 h
  have hA := congrArg (fun q : Ideal O × Ideal O × Ideal O => q.2.1) ht
  have hR := congrArg (fun q : Ideal O × Ideal O × Ideal O => q.2.2) ht
  have hC := congrArg (fun z : SecondPassFiber.OldTuple => z.core 1) h
  have hD := congrArg (fun z : SecondPassFiber.OldTuple => z.core 7) h
  have hE := congrArg (fun z : SecondPassFiber.OldTuple => z.core 2) h
  have hV := congrArg SecondPassFiber.OldTuple.v h
  have hk := congrArg SecondPassFiber.OldTuple.row h
  have hA' : x.firstCommon=y.firstCommon := FirstCauchyArithmetic.family_product_injective _ hinj hA
  have hC' : x.common=y.common := FirstCauchyArithmetic.family_product_injective _ hinj hC
  have hD' : x.firstDivisor=y.firstDivisor := FirstCauchyArithmetic.family_product_injective _ hinj hD
  have hE' : x.source.divisor=y.source.divisor := FirstCauchyArithmetic.family_product_injective _ hinj hE
  have hV' : x.source.overlap=y.source.overlap := FirstCauchyArithmetic.family_product_injective _ hinj hV
  have hR' : x.source.sourceCommon\x.source.divisor=y.source.sourceCommon\y.source.divisor :=
    FirstCauchyArithmetic.family_product_injective _ hinj hR
  have hG : x.source.sourceCommon=y.source.sourceCommon := by
    calc
      _ = x.source.divisor ∪ (x.source.sourceCommon\x.source.divisor) :=
        (Finset.union_sdiff_of_subset hx.2.1).symm
      _ = y.source.divisor ∪ (y.source.sourceCommon\y.source.divisor) := by rw [hR',hE']
      _ = _ := Finset.union_sdiff_of_subset hy.2.1
  exact GlobalSecondData.ext hc hA' hC' hD' (SecondExpansionData.ext hG hE' hV' hk)

theorem globalSecond_fiber_card (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (GlobalSecondData ι))
      (q : Ideal O × Ideal O × Ideal O) (f : Ideal O) (y : O),
      (∀ x∈s,GlobalSecondAdmissible x) → f ≠ ⊥ → q.1 ≠ ⊥ →
      (∀ x∈s,globalSecondFixedTriple p x=q) →
      (∀ x∈s,SecondPassFiber.newLabel (globalSecondTuple p x)=f) →
      (∀ x∈s,SecondPassFiber.newRow (globalSecondTuple p x)=y) →
      (s.card : ℝ) ≤ C*((Ideal.absNorm f : ℝ)*Ideal.absNorm q.1)^ε := by
  obtain ⟨C,hC,hbound⟩ := SecondPassFiber.valid_tuple_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro s q f y hs hf hq htr hlabel hrow
  have hi : Set.InjOn (globalSecondTuple p) s := by
    intro x hx z hz he
    exact globalSecondEncoding_injective p hinj (hs x hx) (hs z hz)
      ((htr x hx).trans (htr z hz).symm) he
  rw [← Finset.card_image_of_injOn hi]
  apply hbound _ f q.1 y hf hq
  intro t ht
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  have hv := globalSecondTuple_valid p x (hs x hx)
  simpa only [htr x hx,hlabel x hx,hrow x hx] using hv

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0161

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.MaskedPrincipalBounds
Source SHA256: f880872b4e1b664e008a9b143da89fe723c69d5e7e05b0025e50b153888ce14f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0162


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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem middleTruncation_coprime_common_mask
    (G C : Ideal O) (hG : Squarefree G) (hC : Squarefree C) (hGC : IsCoprime G C)
    (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) :
    middleTruncation (fun P : primePool {G * C} => P.val) Finset.univ W X Y Z lengthScale =
      ∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q : ℂ) *
        middleTruncation (fun P : primePool {C} => P.val) Finset.univ W
          (X / (Ideal.absNorm q : ℝ)) (Y / (Ideal.absNorm q : ℝ)) (Z / (Ideal.absNorm q : ℝ)) lengthScale := by
  classical
  have hprod : Squarefree (G * C) := squarefree_mul_iff.mpr ⟨hGC.isRelPrime, hG, hC⟩
  rw [middleTruncation_eq_ideal_frequencies _ hprod]
  simp_rw [middleTruncation_eq_ideal_frequencies C hC]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := idealDivisors G) (t := rowNormDisk ⌊lengthScale⌋₊)]
  apply Finset.sum_congr rfl
  intro h hh
  rw [QuadraticDivisorSplit.sum_divisors_coprime_product G C hG.ne_zero hC.ne_zero hGC]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro d hd
  have hqG := (mem_idealDivisors hG.ne_zero).mp hq
  have hdC := (mem_idealDivisors hC.ne_zero).mp hd
  have hq0 : q ≠ 0 := by intro he; rw [he, zero_dvd_iff] at hqG; exact hG.ne_zero hqG
  have hNq : 0 < (Ideal.absNorm q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun he => hq0 (Ideal.absNorm_eq_zero_iff.mp he))
  have hqd := (hGC.mono hqG hdC).isRelPrime
  have hlow : Y < (Ideal.absNorm q : ℝ) * (Ideal.absNorm d : ℝ) ↔
      Y / (Ideal.absNorm q : ℝ) < (Ideal.absNorm d : ℝ) := by
    constructor
    · intro hy
      apply (div_lt_iff₀ hNq).mpr
      simpa only [mul_comm] using hy
    · intro hy
      simpa only [mul_comm] using (div_lt_iff₀ hNq).mp hy
  have hhigh : (Ideal.absNorm q : ℝ) * (Ideal.absNorm d : ℝ) ≤ Z ↔
      (Ideal.absNorm d : ℝ) ≤ Z / (Ideal.absNorm q : ℝ) := by
    constructor
    · intro hz
      apply (le_div_iff₀ hNq).mpr
      simpa only [mul_comm] using hz
    · intro hz
      simpa only [mul_comm] using (le_div_iff₀ hNq).mp hz
  simp only [map_mul, Nat.cast_mul, hlow, hhigh, hqd.moebius_mul, Int.cast_mul]
  by_cases hp : Y / (Ideal.absNorm q : ℝ) < (Ideal.absNorm d : ℝ) ∧
      (Ideal.absNorm d : ℝ) ≤ Z / (Ideal.absNorm q : ℝ)
  · simp only [hp, and_self, ite_true]
    have harg : X * ‖eisEmbedding h‖ ^ 2 / ((Ideal.absNorm q : ℝ) * (Ideal.absNorm d : ℝ)) =
        (X / (Ideal.absNorm q : ℝ)) * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ) := by ring
    rw [harg]
    push_cast
    ring
  · simp only [hp, ite_false, mul_zero]

theorem sqrt_norm_divisor_scale (M B q : ℝ) (hM : 0 ≤ M) (_hB : 0 ≤ B) (hq : 0 < q) :
    Real.sqrt (M / B) / q = Real.sqrt ((M / q ^ 2) / B) := by
  rw [Real.sqrt_div hM, Real.sqrt_div (by positivity : 0 ≤ M / q ^ 2), Real.sqrt_div hM, Real.sqrt_sq hq.le]
  ring

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalMaskedTruncatedMiddle (G : Ideal O) (W : 𝓢(ℝ, ℂ))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    middleTruncation (fun P : primePool {G * (left j * right k)} => P.val) Finset.univ W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) (Y i) (Z i) lengthScale

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMaskedTruncatedMiddle_eq_divisors
    (G : Ideal O) (hG : Squarefree G) (W : 𝓢(ℝ, ℂ))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (hM : 0 ≤ M) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hGl : ∀ j, IsCoprime G (left j)) (hGr : ∀ k, IsCoprime G (right k)) :
    originalMaskedTruncatedMiddle G W rows left right a b M Y Z lengthScale =
      ∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q : ℂ) *
        originalTruncatedMiddle W rows left right a b (M / (Ideal.absNorm q : ℝ) ^ 2)
          (fun i => Y i / (Ideal.absNorm q : ℝ)) (fun i => Z i / (Ideal.absNorm q : ℝ)) lengthScale := by
  classical
  have hp (i : m) (j : n) (k : p) :
      originalTerm rows left right a b 1 1 i j k *
        middleTruncation (fun P : primePool {G * (left j * right k)} => P.val) Finset.univ W
          (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) (Y i) (Z i) lengthScale =
      ∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q : ℂ) *
        (originalTerm rows left right a b 1 1 i j k *
          middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
            (Real.sqrt ((M / (Ideal.absNorm q : ℝ) ^ 2) / (Ideal.absNorm (rows i) : ℝ)))
            (Y i / (Ideal.absNorm q : ℝ)) (Z i / (Ideal.absNorm q : ℝ)) lengthScale) := by
    by_cases hc : IsCoprime (left j) (right k)
    · have hsq : Squarefree (left j * right k) :=
        squarefree_mul_iff.mpr ⟨hc.isRelPrime, (hleft j).2.1, (hright k).2.1⟩
      rw [middleTruncation_coprime_common_mask G _ hG hsq ((hGl j).mul_right (hGr k)), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      have hqG := (mem_idealDivisors hG.ne_zero).mp hq
      have hq0 : q ≠ 0 := by intro he; rw [he, zero_dvd_iff] at hqG; exact hG.ne_zero hqG
      have hNq : 0 < (Ideal.absNorm q : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (fun he => hq0 (Ideal.absNorm_eq_zero_iff.mp he))
      rw [sqrt_norm_divisor_scale M _ _ hM (Nat.cast_nonneg _) hNq]
      ring
    · have hz : originalTerm rows left right a b 1 1 i j k = 0 := by simp only [originalTerm, hc, ite_false]
      simp only [hz, zero_mul, mul_zero, Finset.sum_const_zero]
  unfold originalMaskedTruncatedMiddle
  simp_rw [hp]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset p)) (t := idealDivisors G),
    Finset.sum_comm (s := (Finset.univ : Finset n)) (t := idealDivisors G),
    Finset.sum_comm (s := (Finset.univ : Finset m)) (t := idealDivisors G)]
  simp only [originalTruncatedMiddle, Finset.mul_sum]

theorem HasSieveExponent.original_masked_truncated_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (G : Ideal O) (hG : Squarefree G)
    (B N M U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hGl : ∀ j, IsCoprime G (left j)) (hGr : ∀ k, IsCoprime G (right k))
    (hZ : ∀ i, Z i ≤ U * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) :
    ‖originalMaskedTruncatedMiddle G W rows left right a b M Y Z lengthScale‖ ≤
      (idealDivisors G).card * (((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2)))) := by
  let V := ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2)))
  have hqbound (q : Ideal O) (hq : q ∈ idealDivisors G) :
      ‖originalTruncatedMiddle W rows left right a b (M / (Ideal.absNorm q : ℝ) ^ 2)
        (fun i => Y i / (Ideal.absNorm q : ℝ)) (fun i => Z i / (Ideal.absNorm q : ℝ)) lengthScale‖ ≤ V := by
    have hqG := (mem_idealDivisors hG.ne_zero).mp hq
    have hq0 : q ≠ 0 := by intro he; rw [he, zero_dvd_iff] at hqG; exact hG.ne_zero hqG
    have hq1 : (1 : ℝ) ≤ Ideal.absNorm q := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun he => hq0 (Ideal.absNorm_eq_zero_iff.mp he))
    have hqpos : (0 : ℝ) < Ideal.absNorm q := by linarith
    have hZq (i : m) : Z i / (Ideal.absNorm q : ℝ) ≤
        U * Real.sqrt ((M / (Ideal.absNorm q : ℝ) ^ 2) / (Ideal.absNorm (rows i) : ℝ)) := by
      calc
        _ ≤ (U * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) / (Ideal.absNorm q : ℝ) :=
          div_le_div_of_nonneg_right (hZ i) hqpos.le
        _ = U * (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) / (Ideal.absNorm q : ℝ)) := by ring
        _ = _ := by rw [sqrt_norm_divisor_scale M _ _ hM.le (Nat.cast_nonneg _) hqpos]
    have hb := hexp.original_truncated_middle deltaLoss hδ ε hε B N (M / (Ideal.absNorm q : ℝ) ^ 2) U
      hB hN (by positivity) hU rows left right hr hl hri hrows a b W
      (fun i => Y i / (Ideal.absNorm q : ℝ)) (fun i => Z i / (Ideal.absNorm q : ℝ)) lengthScale hleft hright hZq
    apply hb.trans
    dsimp only [V]
    have h1 := nonzeroLatticeEnvelopeConstant_nonneg
    have h2 := originalMiddleDecayConstant_nonneg W
    have h3 := divisorEnergyFactor_nonneg ε hε N a b
    have h4 := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    gcongr
    exact div_le_self hM.le (one_le_pow₀ hq1)
  rw [originalMaskedTruncatedMiddle_eq_divisors G hG W rows left right a b M hM.le Y Z lengthScale
    (fun j => (hleft j).1) (fun k => (hright k).1) hGl hGr]
  calc
    _ ≤ ∑ q ∈ idealDivisors G,
        ‖(UniqueFactorizationMonoid.moebius q : ℂ) *
          originalTruncatedMiddle W rows left right a b (M / (Ideal.absNorm q : ℝ) ^ 2)
            (fun i => Y i / (Ideal.absNorm q : ℝ)) (fun i => Z i / (Ideal.absNorm q : ℝ)) lengthScale‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ idealDivisors G, V := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (QuadraticInitialBound.norm_ideal_moebius_le_one q)).trans (hqbound q hq)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, V]

end

open ActualEisensteinCubic IdealMobiusDivisorSum IdealCoprimeSieveOperator

theorem HasSieveExponent.actual_principal_difference {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : Type} [Fintype n] [DecidableEq n]
      (cols : n → Ideal O) (_hinj : Function.Injective cols)
      (M N K : ℝ), 1 ≤ M → 1 ≤ N → 1 ≤ K →
      (∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) →
      (∀ j k, columnRay (cols j) = columnRay (cols k)) →
      ∀ (a : n → ℂ) (G : Ideal O), Squarefree G →
      (∀ P ∈ fixedBadPrimes, P ∣ G) → ∀ (ε : ℝ) (hε : 0 < ε),
      ‖(Real.sqrt M : ℂ) * actualPrincipalDifference cols a G K‖ ≤
        ((idealDivisors G).card : ℝ)^2 * (supportConstant ε hε * N^ε) *
          C * (K*N)^deltaLoss * (Real.sqrt (M/K)*N + Real.sqrt M*K^(α-1/2)) *
          ∑ j, ‖a j‖^2 := by
  obtain ⟨C,hC,hbound⟩ := hexp.reverse deltaLoss hδ
  refine ⟨C,hC,?_⟩
  intro n _ _ cols hinj M N K hM hN hK hcols hray a G hG hbad ε hε
  have hM0 : 0 ≤ M := by linarith
  have hK0 : 0 < K := by linarith
  have hs := actualPrincipalDifference_bound cols hinj N (by linarith) hcols hray a G hG hbad K hK0 ε hε
  have hsupp := (supportConstant_pos ε hε).le
  have hb := hbound K N hK hN
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg M)]
  calc
    _ ≤ Real.sqrt M * (((idealDivisors G).card : ℝ)^2 *
        ((1/Real.sqrt K)*sieveNorm K N*(supportConstant ε hε*N^ε)*∑ j, ‖a j‖^2)) :=
      mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt M * (((idealDivisors G).card : ℝ)^2 *
        ((1/Real.sqrt K)*(C*(K*N)^deltaLoss*(N+K^α))*(supportConstant ε hε*N^ε)*∑ j, ‖a j‖^2)) := by
      gcongr
    _ = ((idealDivisors G).card : ℝ)^2*(supportConstant ε hε*N^ε)*C*(K*N)^deltaLoss*
        (Real.sqrt (M/K)*(N+K^α))*∑ j, ‖a j‖^2 := by
      rw [Real.sqrt_div hM0]
      ring
    _ = _ := by
      rw [mul_add, sqrt_div_mul_rpow M K α hM0 hK0]

end CanonicalQuadraticSieve

namespace ShortDraftDescent
open MeasureTheory Filter

theorem integral_geometric_descent
    {Node Parameter : Type*} [MeasurableSpace Parameter]
    (rank : Node → ℕ) (energy mass terminal : Node → ℝ)
    (left right : Node → Parameter → Node)
    (measure : Node → Measure Parameter) (weight : Node → Parameter → ℝ)
    (hweight : ∀ x, ∀ᵐ t ∂measure x, 0 ≤ weight x t)
    (hintegrable : ∀ x, Integrable (fun t => weight x t *
      Real.sqrt (mass (left x t)) * Real.sqrt (mass (right x t))) (measure x))
    (hterminal : ∀ x, rank x = 0 → energy x ≤ mass x)
    (hchildren : ∀ x, rank x ≠ 0 → ∀ᵐ t ∂measure x,
      rank (left x t) < rank x ∧ rank (right x t) < rank x)
    (hstep : ∀ x, rank x ≠ 0 → energy x ≤ terminal x +
      ∫ t, weight x t * Real.sqrt (energy (left x t)) * Real.sqrt (energy (right x t)) ∂measure x)
    (hbudget : ∀ x, rank x ≠ 0 → terminal x +
      (∫ t, weight x t * Real.sqrt (mass (left x t)) * Real.sqrt (mass (right x t)) ∂measure x) ≤ mass x) :
    ∀ x, energy x ≤ mass x := by
  have h : ∀ n : ℕ, ∀ x, rank x = n → energy x ≤ mass x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      by_cases hn : n = 0
      · exact hterminal x (hx.trans hn)
      have hx0 : rank x ≠ 0 := by omega
      have hmono : (∫ t, weight x t * Real.sqrt (energy (left x t)) *
          Real.sqrt (energy (right x t)) ∂measure x) ≤
          ∫ t, weight x t * Real.sqrt (mass (left x t)) *
          Real.sqrt (mass (right x t)) ∂measure x := by
        refine integral_mono_of_nonneg ?_ (hintegrable x) ?_
        · filter_upwards [hweight x] with t ht
          exact mul_nonneg (mul_nonneg ht (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
        · filter_upwards [hweight x, hchildren x hx0] with t ht hr
          have hl := ih (rank (left x t)) (by omega) (left x t) rfl
          have hh := ih (rank (right x t)) (by omega) (right x t) rfl
          exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hl) ht)
            (Real.sqrt_le_sqrt hh) (Real.sqrt_nonneg _)
            (mul_nonneg ht (Real.sqrt_nonneg _))
      exact (hstep x hx0).trans ((add_le_add le_rfl hmono).trans (hbudget x hx0))
  intro x
  exact h (rank x) x rfl

end ShortDraftDescent

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic FourierBridge

def halfShellFactor (N q : ℝ) : ℝ := Real.sqrt (N/2) / Real.sqrt q

lemma halfShellFactor_nonneg (N q : ℝ) : 0 ≤ halfShellFactor N q := by
  unfold halfShellFactor
  positivity

lemma halfShellFactor_le_one (N q : ℝ) (hq : 0 < q) (h : N/2 ≤ q) :
    halfShellFactor N q ≤ 1 := by
  unfold halfShellFactor
  exact (div_le_one (Real.sqrt_pos.mpr hq)).mpr (Real.sqrt_le_sqrt h)

lemma halfShellFactor_pair (M F N i j : ℝ) (hN : 0 < N) (hi : 0 < i) (hj : 0 < j)
    (hF : 0 < F) :
    (2*M/(F*N))*halfShellFactor N i*halfShellFactor N j =
      M/(Real.sqrt (i*j)*F) := by
  unfold halfShellFactor
  rw [Real.sqrt_mul hi.le]
  have hs := Real.sq_sqrt (show 0 ≤ N/2 by positivity)
  have hsi := (Real.sqrt_pos.mpr hi).ne'
  have hsj := (Real.sqrt_pos.mpr hj).ne'
  field_simp
  rw [hs]
  ring

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def smallPrincipalCorrection (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) : ℝ :=
  ∑ D ∈ S, ∑ E ∈ T, ∑ i,
    ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k *
      ((M/(Real.sqrt ((Ideal.absNorm (left j) : ℝ)*(Ideal.absNorm (right k) : ℝ))*F) : ℝ) : ℂ)‖

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma originalTerm_real_scaling
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (u : n → ℝ) (v : p → ℝ)
    (D E : Ideal O) (i : m) (j : n) (k : p) :
    originalTerm rows left right (fun j => a j*(u j:ℂ)) (fun k => b k*(v k:ℂ)) D E i j k =
      originalTerm rows left right a b D E i j k * (u j:ℂ) * (v k:ℂ) := by
  unfold originalTerm
  by_cases hc : IsCoprime (left j) (right k) <;>
    by_cases hd : D ∣ left j <;> by_cases he : E ∣ right k <;>
    simp only [hc,hd,he,ite_true,ite_false,mul_zero,zero_mul,star_zero,star_mul,Complex.star_def,
      Complex.conj_ofReal] ; ring

theorem smallPrincipalCorrection_bound
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M F : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hN : 1 ≤ N)
    (hM : 0 < M) (hF : 0 < F)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2*D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2*D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ N/2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N/2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) :
    smallPrincipalCorrection S T rows left right a b M F ≤
      (2*M/(F*N))*Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) := by
  have hN0 : 0 < N := by linarith
  let u := fun j => halfShellFactor N (Ideal.absNorm (left j) : ℝ)
  let v := fun k => halfShellFactor N (Ideal.absNorm (right k) : ℝ)
  let a' := fun j => a j*(u j:ℂ)
  let b' := fun k => b k*(v k:ℂ)
  have hu (j) : 0 ≤ u j ∧ u j ≤ 1 :=
    ⟨halfShellFactor_nonneg _ _,halfShellFactor_le_one _ _ (by linarith [(hleft j).2.1]) (hleft j).2.1⟩
  have hv (k) : 0 ≤ v k ∧ v k ≤ 1 :=
    ⟨halfShellFactor_nonneg _ _,halfShellFactor_le_one _ _ (by linarith [(hright k).2.1]) (hright k).2.1⟩
  have ha (j) : ‖a' j‖ ≤ ‖a j‖ := by
    simp only [a',norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hu j).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (hu j).2
  have hb (k) : ‖b' k‖ ≤ ‖b k‖ := by
    simp only [b',norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hv k).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (hv k).2
  have ht (D E : Ideal O) (i j k) :
      originalTerm rows left right a b D E i j k *
        ((M/(Real.sqrt ((Ideal.absNorm (left j) : ℝ)*(Ideal.absNorm (right k) : ℝ))*F) : ℝ) : ℂ) =
      ((2*M/(F*N):ℝ):ℂ)*originalTerm rows left right a' b' D E i j k := by
    have hid := halfShellFactor_pair M F N (Ideal.absNorm (left j) : ℝ) (Ideal.absNorm (right k) : ℝ)
      hN0 (by linarith [(hleft j).2.1]) (by linarith [(hright k).2.1]) hF
    rw [←hid, show originalTerm rows left right a' b' D E i j k =
      originalTerm rows left right a b D E i j k*(u j:ℂ)*(v k:ℂ) from
      originalTerm_real_scaling rows left right a b u v D E i j k]
    push_cast
    dsimp only [u,v]
    ring
  have hblock := canonical_original_divisor_block_phase_bound ε hε S T D₁ D₂ B N hD₁ hD₂ hN hS hT
    rows left right hr hl hri hrows (fun j => ⟨(hleft j).1,(hleft j).2.2⟩)
      (fun k => ⟨(hright k).1,(hright k).2.2⟩) a' b' (fun _ => 0) (fun _ => 0) 0
  simp only [zero_add,logPhase_zero,mul_one] at hblock
  have hcost := divisorBlockCost_mono_coefficients ε hε D₁ D₂ B N (by linarith) (by linarith) a' a b' b ha hb
  have heq : smallPrincipalCorrection S T rows left right a b M F =
      (2*M/(F*N))*(∑ D ∈ S, ∑ E ∈ T, ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a' b' D E i j k‖) := by
    unfold smallPrincipalCorrection
    simp_rw [ht,←Finset.mul_sum]
    simp only [norm_mul,Complex.norm_of_nonneg (show 0 ≤ 2*M/(F*N) by positivity)]
    simp_rw [←Finset.mul_sum]
  rw [heq]
  exact mul_le_mul_of_nonneg_left (hblock.trans (Real.sqrt_le_sqrt hcost)) (by positivity)

end

open ActualEisensteinCubic

theorem HasSieveExponent.small_principal_correction {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M F U : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hM : 0 < M) (hF : 0 < F) (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2*D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2*D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ N/2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N/2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (hcut : D₁*D₂ ≤ U*(N*Real.sqrt (F/(M*B)))) :
    smallPrincipalCorrection S T rows left right a b M F ≤
      2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (M/F+U*Real.sqrt (M/F)*B^(α-1/2)) := by
  have hb := smallPrincipalCorrection_bound ε hε S T D₁ D₂ B N M F hD₁ hD₂ hN hM hF hS hT
    rows left right hr hl hri hrows hleft hright a b
  have hc := divisor_cost_with_constant hexp deltaLoss hδ ε hε B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N a b
  have he := divisorEnergyFactor_nonneg ε hε N a b
  have hC := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  calc
    _ ≤ (2*M/(F*N))*(divisorEnergyFactor ε hε N a b*
        (divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss*(N+B^α*(D₁*D₂)))) :=
      hb.trans (mul_le_mul_of_nonneg_left hc (by positivity))
    _ = (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss))*
        ((M/(F*N))*(N+B^α*(D₁*D₂))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (dual_middle_scale_shape M F B N (D₁*D₂) U α hM hF (by linarith) (by linarith) hcut)
      (by positivity)

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

theorem truncationError_symmetric_bound (m : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (_hinj : Function.Injective P) (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X₀ X T : ℝ),
        0 < X₀ → X₀ / 2 ≤ X → X ≤ 2 * X₀ → 4 ≤ T →
        ‖truncationError P S W X (X₀ / T) (T * X₀) (T ^ 4)‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ m := by
  obtain ⟨s, C, hC, hb⟩ := truncationError_bound (m + 3)
  refine ⟨s, C * 2 ^ (m + 10), by positivity, ?_⟩
  intro ι _ P _ hinj S W X₀ X T hX₀ hlo hhi hT
  obtain ⟨hX, hY, hYX, hXZ, hL⟩ := symmetric_truncation_scales X₀ X T hX₀ hlo hhi hT
  have hp := hb P hinj S W X (X₀ / T) (T * X₀) (T ^ 4) hX hY hYX hXZ hL
  have hs := symmetric_truncation_scalar_bound m X₀ X T hX₀ hlo hhi hT
  calc
    _ ≤ (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
        (((X₀ / T) / X) ^ (m + 3) + 1 / (1 + (T * X₀) / X) ^ (m + 3) +
          (X / (X₀ / T)) / ((min 1 (X / (T * X₀))) ^ 2 * (1 + X * T ^ 4 / (T * X₀)) ^ (m + 3))) := hp
    _ ≤ (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * (2 ^ (m + 10) / T ^ m) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

theorem primePool_symmetric_error_bound (m : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (G : Ideal O) (_hG : G ≠ 0)
        (W : 𝓢(ℝ, ℂ)) (X₀ X T : ℝ),
        0 < X₀ → X₀ / 2 ≤ X → X ≤ 2 * X₀ → 4 ≤ T →
        ‖truncationError (fun P : primePool {G} => P.val) Finset.univ W
          X (X₀ / T) (T * X₀) (T ^ 4)‖ ≤
          (supportConstant ε hε * (Ideal.absNorm G : ℝ) ^ ε) *
            (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ m := by
  obtain ⟨s, C, hC, hb⟩ := truncationError_symmetric_bound m
  refine ⟨s, C, hC, ?_⟩
  intro ε hε G hG W X₀ X T hX₀ hlo hhi hT
  have hh := hb (fun P : primePool {G} => P.val) Subtype.val_injective Finset.univ W
    X₀ X T hX₀ hlo hhi hT
  simp only [Finset.card_univ, Fintype.card_coe, primePool_singleton_eq_primeSupport] at hh
  apply hh.trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (support_card_bound ε hε G hG) (by positivity)) (by positivity)

theorem lowPrincipal_symmetric_error_bound (m : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (I J : Ideal O) (_hI : Admissible I) (_hJ : Admissible J)
        (W : 𝓢(ℝ, ℂ)) (X₀ X T : ℝ),
        0 < X₀ → X₀ / 2 ≤ X → X ≤ 2 * X₀ → 4 ≤ T →
        ‖lowPrincipalError I J W X (X₀ / T) (T * X₀) (T ^ 4)‖ ≤
          (4 * supportConstant ε hε * ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ)) ^ ε) *
            (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) / T ^ m := by
  obtain ⟨s, C, hC, hb⟩ := lowPrincipalError_bound (m + 3)
  refine ⟨s, C * 2 ^ (m + 10), by positivity, ?_⟩
  intro ε hε I J hI hJ W X₀ X T hX₀ hlo hhi hT
  obtain ⟨hX, hY, hYX, hXZ, hL⟩ := symmetric_truncation_scales X₀ X T hX₀ hlo hhi hT
  have hh := hb ε hε I J hI hJ W X (X₀ / T) (T * X₀) (T ^ 4) hX hY hYX hXZ hL
  have hs := symmetric_truncation_scalar_bound m X₀ X T hX₀ hlo hhi hT
  have hc := (supportConstant_pos ε hε).le
  calc
    _ ≤ (4 * supportConstant ε hε * ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ)) ^ ε) *
        (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) *
        (((X₀ / T) / X) ^ (m + 3) + 1 / (1 + (T * X₀) / X) ^ (m + 3) +
          (X / (X₀ / T)) / ((min 1 (X / (T * X₀))) ^ 2 * (1 + X * T ^ 4 / (T * X₀)) ^ (m + 3))) := hh
    _ ≤ (4 * supportConstant ε hε * ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ)) ^ ε) *
        (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) * (2 ^ (m + 10) / T ^ m) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

theorem originalTerm_one_norm_le {m n p : Type*}
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (i : m) (j : n) (k : p) :
    ‖originalTerm rows left right a b 1 1 i j k‖ ≤ ‖a j‖ * ‖b k‖ := by
  classical
  unfold originalTerm
  simp only [one_dvd, ite_true]
  split_ifs with hc
  · simp only [norm_mul, norm_star]
    calc
      _ ≤ (1 * ‖a j‖) * (1 * ‖b k‖) := mul_le_mul
        (mul_le_mul_of_nonneg_right (quadraticRow_norm_le_one _ _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (quadraticRow_norm_le_one _ _) (norm_nonneg _))
        (by positivity) (by positivity)
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

theorem actual_pair_error_energy {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ)
    (E : ℝ) (hE : 0 ≤ E) (error : m → n → n → ℂ)
    (herr : ∀ i j k, ‖error i j k‖ ≤ E) :
    ‖∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k * error i j k‖ ≤
      Fintype.card m * Fintype.card n * E * ∑ j, ‖a j‖ ^ 2 := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j : n => ‖a j‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hcs
  have hs : (∑ j, ∑ k, ‖a j‖ * ‖a k‖ * E) = (∑ j, ‖a j‖) ^ 2 * E := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  calc
    _ ≤ ∑ i, ∑ j, ∑ k, ‖originalTerm rows cols cols a a 1 1 i j k * error i j k‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun j hj => norm_sum_le _ _)
    _ ≤ ∑ _i : m, ∑ j, ∑ k, ‖a j‖ * ‖a k‖ * E := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul]
      exact mul_le_mul (originalTerm_one_norm_le rows cols cols a a i j k) (herr i j k)
        (norm_nonneg _) (by positivity)
    _ = (Fintype.card m : ℝ) * ((∑ j, ‖a j‖) ^ 2 * E) := by
      simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Fintype.card m : ℝ) * (((∑ j, ‖a j‖ ^ 2) * Fintype.card n) * E) := by gcongr
    _ = _ := by ring

theorem finite_ideal_family_card_bound {m : Type*} [Fintype m]
    (I : m → Ideal O) (hI : Function.Injective I) (B : ℝ) (hB : 1 ≤ B)
    (hzero : ∀ i, I i ≠ 0) (hNorm : ∀ i, (Ideal.absNorm (I i) : ℝ) ≤ B) :
    (Fintype.card m : ℝ) ≤ 128 * B := by
  classical
  have hb := DescentFiberCost.finite_ideal_count_real (Finset.univ.image I) B hB
    (by intro J hJ; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hJ; exact hzero i)
    (by intro J hJ; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hJ; exact hNorm i)
  simpa only [Finset.card_image_of_injective _ hI, Finset.card_univ] using hb

theorem actual_pair_error_ideal_bound {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (hr : Function.Injective rows) (hc : Function.Injective cols)
    (B N : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hrows : ∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (hcols : ∀ j, cols j ≠ 0 ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (a : n → ℂ) (E : ℝ) (hE : 0 ≤ E) (error : m → n → n → ℂ)
    (herr : ∀ i j k, ‖error i j k‖ ≤ E) :
    ‖∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k * error i j k‖ ≤
      16384 * B * N * E * ∑ j, ‖a j‖ ^ 2 := by
  have hrc := finite_ideal_family_card_bound rows hr B hB (fun i => (hrows i).1) (fun i => (hrows i).2)
  have hcc := finite_ideal_family_card_bound cols hc N hN (fun j => (hcols j).1) (fun j => (hcols j).2)
  apply (actual_pair_error_energy rows cols a E hE error herr).trans
  calc
    _ ≤ (128 * B) * (128 * N) * E * ∑ j, ‖a j‖ ^ 2 := by gcongr
    _ = _ := by ring

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0162

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.PrincipalNormalization
Source SHA256: 5eae16e8332295ad0a32992dcb6b6d469158240cda532493520d509efd49be1a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0163



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

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open SecondPassFiber (newLabel newRow)
open ConcretePrimeRowBridge (idealGenerator)
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalSecondLabel (x : GlobalSecondData ι) : O :=
  secondSupportLabel p x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit (expansionSupportData x.common x.firstDivisor x.source)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondLabel_span (x : GlobalSecondData ι) :
    Ideal.span {globalSecondLabel p x}=newLabel (globalSecondTuple p x) :=
  actualSecondLabel_span p x.cube.support x.common x.source.divisor x.source.overlap
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit

def globalSecondLabelUnit (x : GlobalSecondData ι) : Oˣ :=
  Classical.choose (exists_label_unit (globalSecondLabel p x)
    (newLabel (globalSecondTuple p x)) (globalSecondLabel_span p x))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondLabelUnit_spec (x : GlobalSecondData ι) :
    globalSecondLabel p x=(globalSecondLabelUnit p x : O)*idealGenerator (newLabel (globalSecondTuple p x)) :=
  Classical.choose_spec (exists_label_unit (globalSecondLabel p x)
    (newLabel (globalSecondTuple p x)) (globalSecondLabel_span p x))

theorem global_second_energy_pushforward
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (s : Finset (GlobalSecondData ι)) (t : Finset (Ideal O × O))
      (q : Ideal O × Ideal O × Ideal O) (w : GlobalSecondData ι → ℂ) (B lengthScale : ℝ)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (negative : Bool),
      q.1 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,globalSecondFixedTriple p x=q) →
      (∀ x∈s,(newLabel (globalSecondTuple p x),newRow (globalSecondTuple p x))∈t) →
      (∀ z∈t,z.1 ≠ ⊥) → (∀ z∈t,(Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x∈s,‖w x‖ ≤ B) →
      (∑ x∈s,‖w x‖ * ‖fixedChildRow p hp hcop hg F Ψ m H (globalSecondLabel p x)
        (if negative then -newRow (globalSecondTuple p x) else newRow (globalSecondTuple p x))‖^2) ≤
      B*C*(lengthScale*Ideal.absNorm q.1)^ε *
        ∑ u : Oˣ,∑ z∈t,‖idealChildRow p hp hcop hg F Ψ m H negative u z‖^2 := by
  obtain ⟨C,hC,hcard⟩ := globalSecond_fiber_card p hinj ε hε
  refine ⟨C,hC,?_⟩
  intro s t q w B lengthScale F Ψ m H negative hq hB hL hs hfixed hmap ht hnorm hw
  let f : GlobalSecondData ι → Oˣ × (Ideal O × O) := fun x =>
    (globalSecondLabelUnit p x,newLabel (globalSecondTuple p x),newRow (globalSecondTuple p x))
  let P : Oˣ × (Ideal O × O) → ℂ := fun z => idealChildRow p hp hcop hg F Ψ m H negative z.1 z.2
  have hm : ∀ x∈s,f x∈Finset.univ ×ˢ t := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,hmap x hx⟩
  have hpush := DescentWeightedCauchy.bounded_energy_pushforward s (Finset.univ ×ˢ t) f w P B hm hw
  have he : (∑ x∈s,‖w x‖ * ‖fixedChildRow p hp hcop hg F Ψ m H (globalSecondLabel p x)
      (if negative then -newRow (globalSecondTuple p x) else newRow (globalSecondTuple p x))‖^2) =
      ∑ x∈s,‖w x‖ * ‖P (f x)‖^2 := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [globalSecondLabelUnit_spec p x]
    rfl
  rw [he]
  apply hpush.trans
  calc
    _ ≤ ∑ z∈Finset.univ ×ˢ t,B*C*(lengthScale*Ideal.absNorm q.1)^ε * ‖P z‖^2 := by
      apply Finset.sum_le_sum
      intro z hz
      have hzt := (Finset.mem_product.mp hz).2
      have hc := hcard (s.filter (fun x => f x=z)) q z.2.1 z.2.2
        (fun x hx => hs x (Finset.mem_filter.mp hx).1) (ht z.2 hzt) hq
        (fun x hx => hfixed x (Finset.mem_filter.mp hx).1)
        (fun x hx => congrArg (fun z : Oˣ × (Ideal O × O) => z.2.1) (Finset.mem_filter.mp hx).2)
        (fun x hx => congrArg (fun z : Oˣ × (Ideal O × O) => z.2.2) (Finset.mem_filter.mp hx).2)
      have hn : (Ideal.absNorm z.2.1 : ℝ)*Ideal.absNorm q.1 ≤ lengthScale*Ideal.absNorm q.1 :=
        mul_le_mul_of_nonneg_right (hnorm z.2 hzt) (by positivity)
      have hc' := hc.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hn hε.le) hC.le)
      have hfinal := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc' hB) (sq_nonneg ‖P z‖)
      simpa only [mul_assoc] using hfinal
    _ = _ := by
      rw [← Finset.mul_sum,Finset.sum_product]

def globalSecondMode (s : Finset (GlobalSecondData ι)) (w : GlobalSecondData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (H₁ H₂ : Finset ι → ℂ) : ℂ :=
  ∑ x∈s,w x * star (fixedChildRow p hp hcop hg F Ψ₁ m H₁
    (globalSecondLabel p x) (newRow (globalSecondTuple p x))) *
    fixedChildRow p hp hcop hg F Ψ₂ m H₂ (globalSecondLabel p x) (-newRow (globalSecondTuple p x))

theorem global_second_mode_transfer
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (s : Finset (GlobalSecondData ι)) (t : Finset (Ideal O × O))
      (q : Ideal O × Ideal O × Ideal O) (w : GlobalSecondData ι → ℂ) (B lengthScale : ℝ)
      (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (H₁ H₂ : Finset ι → ℂ),
      q.1 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,globalSecondFixedTriple p x=q) →
      (∀ x∈s,(newLabel (globalSecondTuple p x),newRow (globalSecondTuple p x))∈t) →
      (∀ z∈t,z.1 ≠ ⊥) → (∀ z∈t,(Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x∈s,‖w x‖ ≤ B) →
      ‖globalSecondMode p hp hcop hg s w F Ψ₁ Ψ₂ m H₁ H₂‖ ≤
      B*C*(lengthScale*Ideal.absNorm q.1)^ε *
        Real.sqrt (∑ u : Oˣ,∑ z∈t,‖idealChildRow p hp hcop hg F Ψ₁ m H₁ false u z‖^2) *
        Real.sqrt (∑ u : Oˣ,∑ z∈t,‖idealChildRow p hp hcop hg F Ψ₂ m H₂ true u z‖^2) := by
  obtain ⟨C,hC,hpush⟩ := global_second_energy_pushforward p hp hcop hg hinj ε hε
  refine ⟨C,hC,?_⟩
  intro s t q w B lengthScale F Ψ₁ Ψ₂ m H₁ H₂ hq hB hL hs hfixed hmap ht hnorm hw
  let P₁ := fun x => fixedChildRow p hp hcop hg F Ψ₁ m H₁ (globalSecondLabel p x) (newRow (globalSecondTuple p x))
  let P₂ := fun x => fixedChildRow p hp hcop hg F Ψ₂ m H₂ (globalSecondLabel p x) (-newRow (globalSecondTuple p x))
  have h₁ := hpush s t q w B lengthScale F Ψ₁ m H₁ false hq hB hL hs hfixed hmap ht hnorm hw
  have h₂ := hpush s t q w B lengthScale F Ψ₂ m H₂ true hq hB hL hs hfixed hmap ht hnorm hw
  simp only [Bool.false_eq_true,ite_false,ite_true] at h₁ h₂
  let D := B*C*(lengthScale*Ideal.absNorm q.1)^ε
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hCau := DescentWeightedCauchy.weighted_cauchy s w P₂ P₁
  have he : globalSecondMode p hp hcop hg s w F Ψ₁ Ψ₂ m H₁ H₂ =
      ∑ x∈s,w x*P₂ x*star (P₁ x) := by
    unfold globalSecondMode
    apply Finset.sum_congr rfl
    intro x hx
    dsimp [P₁,P₂]
    ring
  rw [he]
  apply hCau.trans
  calc
    _ ≤ Real.sqrt (D*∑ u : Oˣ,∑ z∈t,‖idealChildRow p hp hcop hg F Ψ₂ m H₂ true u z‖^2) *
      Real.sqrt (D*∑ u : Oˣ,∑ z∈t,‖idealChildRow p hp hcop hg F Ψ₁ m H₁ false u z‖^2) := by
        gcongr
    _ = _ := by
      rw [Real.sqrt_mul hD,Real.sqrt_mul hD]
      calc
        _ = (Real.sqrt D)^2 *
          Real.sqrt (∑ u : Oˣ,∑ z∈t,‖idealChildRow p hp hcop hg F Ψ₁ m H₁ false u z‖^2) *
          Real.sqrt (∑ u : Oˣ,∑ z∈t,‖idealChildRow p hp hcop hg F Ψ₂ m H₂ true u z‖^2) := by ring
        _ = _ := by rw [Real.sq_sqrt hD]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm b0Label jLabel cubeRadical)
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)
open SecondPassFiber (newLabel newRow)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem rowCoprimeMask_congr_span (S : Finset ι) {a b : O}
    (h : Ideal.span {a}=Ideal.span {b}) :
    rowCoprimeMask (fun i => Ideal.span {p i}) S a = rowCoprimeMask (fun i => Ideal.span {p i}) S b := by
  have hm (i : ι) : a ∈ Ideal.span {p i} ↔ b ∈ Ideal.span {p i} := by
    rw [← Ideal.span_singleton_le_iff_mem, h, Ideal.span_singleton_le_iff_mem]
  simp only [rowCoprimeMask,hm]

theorem fixedChildRow_congr_mask_span (F : Finset ι) (Ψ : O →* ℂ) {a b : O}
    (h : Ideal.span {a}=Ideal.span {b}) (H : Finset ι → ℂ) (f y : O) :
    fixedChildRow p hp hcop hg F Ψ a H f y = fixedChildRow p hp hcop hg F Ψ b H f y := by
  simp only [fixedChildRow,secondChildColumn,rowCoprimeMask_congr_span p _ h]

theorem secondChildColumn_zero_of_mask_label_mem (Ψ : O →* ℂ) (m f y : O)
    (H : Finset ι → ℂ) (S : Finset ι) (i : ι) (hi : i ∈ S)
    (hmf : m*f ∈ Ideal.span {p i}) :
    secondChildColumn p hp hcop hg Ψ m f y H S = 0 := by
  rcases (inferInstance : (Ideal.span {p i}).IsPrime).mem_or_mem hmf with hm|hf
  · have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S m=0 := by
      simp only [rowCoprimeMask,ite_eq_left (show ∃ i∈S,m ∈ Ideal.span {p i} from ⟨i,hi,hm⟩)]
    simp only [secondChildColumn,hz,mul_zero,zero_mul]
  · have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S f=0 := by
      simp only [rowCoprimeMask,ite_eq_left (show ∃ i∈S,f ∈ Ideal.span {p i} from ⟨i,hi,hf⟩)]
    have hr := FirstPassCubeLabels.row_zero_of_mask_zero (fun i => Ideal.span {p i}) hg S f hz
    simp only [secondChildColumn,hr,zero_pow (by decide : (4 : ℕ) ≠ 0),mul_zero,zero_mul]

theorem fixedChildRow_restore_killed_pool (F B : Finset ι) (Ψ : O →* ℂ)
    (m f y : O) (H : Finset ι → ℂ) (hB : ∀ i∈B,m*f ∈ Ideal.span {p i}) :
    fixedChildRow p hp hcop hg (F\B) Ψ m H f y = fixedChildRow p hp hcop hg F Ψ m H f y := by
  unfold fixedChildRow
  apply Finset.sum_subset (Finset.powerset_mono.mpr Finset.sdiff_subset)
  intro S hS hn
  have hd : ¬ Disjoint B S := by
    intro hd
    apply hn
    apply Finset.mem_powerset.mpr
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hS) hi,
      fun hiB => Finset.disjoint_left.mp hd hiB hi⟩
  obtain ⟨i,hiB,hiS⟩ := Finset.not_disjoint_iff.mp hd
  exact secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ m f y H S i hiS (hB i hiB)

def globalSecondMask (m : O) (x : GlobalSecondData ι) : O :=
  (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
    x.cube.leftBit x.cube.rightBit *
    primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor)) *
    ∏ i∈x.firstCommon,p i

def fixedTripleMask (m : O) (q : Ideal O × Ideal O × Ideal O) : O :=
  m*idealGenerator q.1*idealGenerator q.2.1*idealGenerator q.2.2

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondMask_span (m : O) (x : GlobalSecondData ι) :
    Ideal.span {globalSecondMask p m x}=Ideal.span {fixedTripleMask m (globalSecondFixedTriple p x)} := by
  simp only [globalSecondMask,fixedTripleMask,globalSecondFixedTriple,
    ← Ideal.span_singleton_mul_span_singleton,span_idealGenerator,
    primeSubsetGenerator,FiniteGaussPhase.span_finset_prod]
  ring

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondMask_kills_cube_common (m : O) (x : GlobalSecondData ι) :
    ∀ i∈x.cube.support∪x.common,globalSecondMask p m x*globalSecondLabel p x ∈ Ideal.span {p i} := by
  intro i hi
  let J := jLabel p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
    x.cube.leftBit x.cube.rightBit
  let b0 := b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
    x.cube.leftBit x.cube.rightBit
  rcases Finset.mem_union.mp hi with hi|hi
  · have hd : p i ∣ J*b0 := (Finset.dvd_prod_of_mem p hi).trans
      (cubeRadical_dvd_jLabel_b0 p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit x.cube.support_pos)
    have he : globalSecondMask p m x*globalSecondLabel p x =
        (J*b0)*(m*primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor)*
          (∏ i∈x.firstCommon,p i)*primeSubsetGenerator (fun i => Ideal.span {p i}) x.common*
          primeSubsetGenerator (fun i => Ideal.span {p i}) x.source.divisor*(∏ i∈x.source.overlap,p i)) := by
      simp only [globalSecondMask,globalSecondLabel,secondSupportLabel,expansionSupportData,J,b0]
      ring
    rw [he]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_left hd _)
  · have hC : primeSubsetGenerator (fun i => Ideal.span {p i}) x.common ∈ Ideal.span {p i} := by
      have hs : Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) x.common} ≤ Ideal.span {p i} := by
        rw [primeSubsetGenerator,span_idealGenerator]
        exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun i => Ideal.span {p i}) hi)
      exact hs (Ideal.subset_span (Set.mem_singleton _))
    have hlabel : globalSecondLabel p x ∈ Ideal.span {p i} := by
      apply Ideal.mul_mem_right
      apply Ideal.mul_mem_right
      apply Ideal.mul_mem_right
      exact hC
    exact Ideal.mul_mem_left _ _ hlabel

theorem globalSecondRawRow_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ)
    (x : GlobalSecondData ι) (y : O) :
    fixedChildRow p hp hcop hg ((F\(x.cube.support∪x.common))\x.firstCommon) Ψ
      (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit *
        primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor))
      H (globalSecondLabel p x) y =
    fixedChildRow p hp hcop hg F Ψ (fixedTripleMask m (globalSecondFixedTriple p x))
      H (globalSecondLabel p x) y := by
  rw [fixedChildRow_fixed_pool p hp hcop hg hinj]
  change fixedChildRow p hp hcop hg (F\(x.cube.support∪x.common)) Ψ (globalSecondMask p m x)
    H (globalSecondLabel p x) y = _
  rw [fixedChildRow_restore_killed_pool p hp hcop hg F (x.cube.support∪x.common) Ψ
    (globalSecondMask p m x) (globalSecondLabel p x) y H (globalSecondMask_kills_cube_common p m x)]
  exact fixedChildRow_congr_mask_span p hp hcop hg F Ψ (globalSecondMask_span p m x) H _ _

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def signedProductDivisorSum (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (H : Ideal O → m → n → p → ℂ) : ℂ := by
  classical
  exact ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    ∑ d ∈ idealDivisors (left j*right k), if P d i then
