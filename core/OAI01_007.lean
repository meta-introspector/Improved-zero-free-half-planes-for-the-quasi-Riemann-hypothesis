          (outsideCoeff (insert Q {P}) w (n / Ideal.absNorm P) +
            (if Ideal.absNorm Q ∣ n / Ideal.absNorm P then
              w Q * outsideCoeff (insert Q {P}) w
                ((n / Ideal.absNorm P) / Ideal.absNorm Q) else 0))
        else 0) := by
  classical
  have hPnot : P ∉ (∅ : Finset (Ideal O)) := by simp
  have hSprime : ∀ R ∈ ({P} : Finset (Ideal O)), Prime R := by
    intro R hR
    have heq : R = P := Finset.mem_singleton.mp hR
    exact heq ▸ hP
  have hQnot : Q ∉ ({P} : Finset (Ideal O)) := by simpa using hne.symm
  have hfirst := restore_insert_prime ∅ (by simp) P hP hPnot w hzero hmul n
  have hsecond := restore_insert_prime {P} hSprime Q hQ hQnot w hzero hmul n
  have hthird := restore_insert_prime {P} hSprime Q hQ hQnot w hzero hmul
    (n / Ideal.absNorm P)
  simp only [Finset.insert_empty] at hfirst
  rw [hsecond, hthird] at hfirst
  exact hfirst

end FiniteSFactor

end

end OAI
end OAIOriginalModule0076

/-! Original module: OAI.NumberTheory.DirichletL.Mellin.FiniteEulerRestoration
Source SHA256: 1fcbfb1b01e40575a1fd017fd625f123fe8d5eeececc6549c15ca6532cb9a87f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0077


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

namespace FiniteEulerRestoration

theorem isBigO_power_atTop_div_const {A : ℝ → ℂ} {σ N : ℝ}
    (hN : 0 < N) (hA : A =O[atTop] fun D : ℝ => D ^ σ) :
    (fun D : ℝ => A (D / N)) =O[atTop] (fun D : ℝ => D ^ σ) := by
  have hshift : (fun D : ℝ => A (D / N)) =O[atTop]
      (fun D : ℝ => (D / N) ^ σ) :=
    hA.comp_tendsto ((tendsto_div_const_atTop_of_pos hN).2 tendsto_id)
  have hconst : (fun D : ℝ => (N ^ σ)⁻¹ * D ^ σ) =O[atTop]
      (fun D : ℝ => D ^ σ) :=
    isBigO_const_mul_self (N ^ σ)⁻¹ (fun D : ℝ => D ^ σ) atTop
  have hpower : (fun D : ℝ => (D / N) ^ σ) =O[atTop]
      (fun D : ℝ => D ^ σ) := by
    apply hconst.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with D hD
    rw [Real.div_rpow hD hN.le]
    ring
  exact hshift.trans hpower

theorem isBigO_finite_Euler_shifts {ι : Type*} (s : Finset ι)
    (A : ℝ → ℂ) (c : ι → ℂ) (N : ι → ℝ) {σ : ℝ}
    (hN : ∀ i ∈ s, 0 < N i)
    (hA : A =O[atTop] fun D : ℝ => D ^ σ) :
    (fun D : ℝ => ∑ i ∈ s, c i * A (D / N i)) =O[atTop]
      (fun D : ℝ => D ^ σ) := by
  have hsum : (∑ i ∈ s, fun D : ℝ => c i * A (D / N i)) =O[atTop]
      (fun D : ℝ => D ^ σ) := by
    apply IsBigO.sum
    intro i hi
    exact (isBigO_power_atTop_div_const (hN i hi) hA).const_mul_left (c i)
  exact hsum.congr_left (by
    intro D
    simp only [Finset.sum_apply])

theorem tsum_dvd_shift {N : ℕ} (hN : 0 < N)
    (b : ℕ → ℂ) (φ : ℕ → ℂ) :
    (∑' n : ℕ, if N ∣ n then b (n / N) * φ n else 0) =
      ∑' m : ℕ, b m * φ (N * m) := by
  classical
  let f : ℕ → ℂ := fun n => if N ∣ n then b (n / N) * φ n else 0
  let g : ℕ → ℂ := fun m => b m * φ (N * m)
  have hindex (m : ℕ) : f (N * m) = g m := by
    simp [f, g, hN]
  change (∑' n : ℕ, f n) = ∑' m : ℕ, g m
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun x : Function.support g => N * x.1) ?_ ?_ ?_
  · intro x y hxy
    apply Subtype.ext
    exact Nat.mul_left_cancel hN hxy
  · intro n hn
    have hdiv : N ∣ n := by
      by_contra hnot
      have : f n = 0 := by simp [f, hnot]
      exact hn this
    let m := n / N
    have hnm : N * m = n := Nat.mul_div_cancel' hdiv
    have hgm : g m ≠ 0 := by
      intro hg
      apply hn
      rw [← hnm, hindex, hg]
    exact ⟨⟨m, hgm⟩, hnm⟩
  · intro x
    exact hindex x.1

theorem tsum_restore_one_prime {N : ℕ} (hN : 0 < N)
    (c : ℂ) (a b φ : ℕ → ℂ)
    (hcoeff : ∀ n, a n = b n + if N ∣ n then c * b (n / N) else 0)
    (hb : Summable (fun n => b n * φ n))
    (hshift : Summable (fun m => b m * φ (N * m))) :
    (∑' n : ℕ, a n * φ n) =
      (∑' n : ℕ, b n * φ n) +
        c * (∑' m : ℕ, b m * φ (N * m)) := by
  classical
  let f : ℕ → ℂ := fun n => if N ∣ n then b (n / N) * φ n else 0
  have hcomp : (fun m => f (N * m)) = (fun m => b m * φ (N * m)) := by
    funext m
    simp [f, hN]
  have hinj : Function.Injective (fun m : ℕ => N * m) :=
    fun _ _ h => Nat.mul_left_cancel hN h
  have hsupport : ∀ n, n ∉ Set.range (fun m : ℕ => N * m) → f n = 0 := by
    intro n hn
    have hnot : ¬N ∣ n := by
      intro hd
      exact hn ⟨n / N, Nat.mul_div_cancel' hd⟩
    simp [f, hnot]
  have hf : Summable f := by
    rw [← (hinj.summable_iff hsupport)]
    change Summable (fun m => f (N * m))
    rw [hcomp]
    exact hshift
  have hfc : Summable (fun n => c * f n) := hf.mul_left c
  have hpoint (n : ℕ) : a n * φ n = b n * φ n + c * f n := by
    rw [hcoeff n]
    by_cases hd : N ∣ n
    · simp [f, hd]
      ring
    · simp [f, hd]
  calc
    (∑' n : ℕ, a n * φ n) = ∑' n : ℕ, (b n * φ n + c * f n) := by
      congr 1
      funext n
      exact hpoint n
    _ = (∑' n : ℕ, b n * φ n) + ∑' n : ℕ, c * f n :=
      hb.tsum_add hfc
    _ = (∑' n : ℕ, b n * φ n) + c * (∑' m : ℕ, b m * φ (N * m)) := by
      rw [tsum_mul_left, tsum_dvd_shift hN b φ]

theorem tsum_restore_one_prime_exp {N : ℕ} (hN : 0 < N)
    (c : ℂ) (a b : ℕ → ℂ) (t : ℝ)
    (hcoeff : ∀ n, a n = b n + if N ∣ n then c * b (n / N) else 0)
    (hb : Summable (fun n => b n * Real.exp (-(n : ℝ) * t)))
    (hscaled : Summable (fun m => b m * Real.exp (-(m : ℝ) * ((N : ℝ) * t)))) :
    (∑' n : ℕ, a n * Real.exp (-(n : ℝ) * t)) =
      (∑' n : ℕ, b n * Real.exp (-(n : ℝ) * t)) +
        c * (∑' m : ℕ, b m * Real.exp (-(m : ℝ) * ((N : ℝ) * t))) := by
  have hscale (m : ℕ) :
      Real.exp (-((N * m : ℕ) : ℝ) * t) =
        Real.exp (-(m : ℝ) * ((N : ℝ) * t)) := by
    congr 1
    simp only [Nat.cast_mul]
    ring
  have hshift : Summable (fun m : ℕ =>
      b m * Real.exp (-((N * m : ℕ) : ℝ) * t)) := by
    convert hscaled using 1
    funext m
    rw [hscale]
  simpa only [hscale] using
    tsum_restore_one_prime hN c a b
      (fun n : ℕ => (Real.exp (-(n : ℝ) * t) : ℂ)) hcoeff hb hshift

end FiniteEulerRestoration

namespace FiniteSFactor

noncomputable def outsideExpSum (S : Finset (Ideal O))
    (w : Ideal O → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, outsideCoeff S w n * Real.exp (-(n : ℝ) * t)

theorem outsideExpSum_restore_insert_prime
    (S : Finset (Ideal O)) (hprime : ∀ Q ∈ S, Prime Q)
    (P : Ideal O) (hP : Prime P) (hPnot : P ∉ S)
    (w : Ideal O → ℂ)
    (hzero : ∀ I, ¬Squarefree I → w I = 0)
    (hmul : ∀ I J, IsRelPrime I J → w (I * J) = w I * w J)
    (t : ℝ)
    (hbase : Summable (fun n : ℕ =>
      outsideCoeff (insert P S) w n * Real.exp (-(n : ℝ) * t)))
    (hscaled : Summable (fun n : ℕ =>
      outsideCoeff (insert P S) w n *
        Real.exp (-(n : ℝ) * ((Ideal.absNorm P : ℝ) * t)))) :
    outsideExpSum S w t = outsideExpSum (insert P S) w t +
      w P * outsideExpSum (insert P S) w ((Ideal.absNorm P : ℝ) * t) := by
  let N : ℕ := Ideal.absNorm P
  have hN : 0 < N :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.1)
  have hcoeff (n : ℕ) :
      outsideCoeff S w n = outsideCoeff (insert P S) w n +
        (if N ∣ n then w P * outsideCoeff (insert P S) w (n / N) else 0) :=
    restore_insert_prime S hprime P hP hPnot w hzero hmul n
  unfold outsideExpSum
  exact FiniteEulerRestoration.tsum_restore_one_prime_exp hN
    (w P) (outsideCoeff S w) (outsideCoeff (insert P S) w)
    t hcoeff hbase hscaled

end FiniteSFactor
open Filter Asymptotics MeasureTheory
open scoped Topology

namespace CompactMellinBridge

theorem mellin_weighted_sum
    (a : ℕ → ℂ) (W F : ℝ → ℂ) (s : ℂ)
    (ha0 : a 0 = 0)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) (F t))
    (hint : ∀ n : ℕ,
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t)))
        (Set.Ioi 0))
    (hsumint : Summable (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi 0,
        ‖(t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))‖))
    (hlsum : LSeriesSummable a s) :
    mellin (fun D : ℝ => F D⁻¹) (-s) =
      mellin W s * LSeries a s := by
  have hterm (n : ℕ) :
      (∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))) =
        mellin W s * LSeries.term a s n := by
    by_cases hn : n = 0
    · subst n
      simp [ha0, LSeries.term_zero]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hscale := mellin_comp_mul_left W s hnpos
      have hmul : mellin (fun t : ℝ => a n * W ((n : ℝ) * t)) s =
          a n * mellin (fun t : ℝ => W ((n : ℝ) * t)) s := by
        simpa only [smul_eq_mul] using
          (mellin_const_smul (fun t : ℝ => W ((n : ℝ) * t)) s (a n))
      change mellin (fun t : ℝ => a n * W ((n : ℝ) * t)) s = _
      rw [hmul, hscale, LSeries.term_of_ne_zero hn]
      simp only [smul_eq_mul, Complex.ofReal_natCast, Complex.cpow_neg]
      ring
  have hsum :
      (∑' n : ℕ, ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))) =
        ∫ t : ℝ in Set.Ioi 0,
          ∑' n : ℕ, (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t)) :=
    integral_tsum_of_summable_integral_norm hint hsumint
  have hseries :
      (∑' n : ℕ, mellin W s * LSeries.term a s n) =
        mellin W s * LSeries a s := by
    simpa only [LSeries] using hlsum.hasSum.mul_left (mellin W s) |>.tsum_eq
  calc
    mellin (fun D : ℝ => F D⁻¹) (-s) = mellin F s := by
      simpa using mellin_comp_inv F (-s)
    _ = ∫ t : ℝ in Set.Ioi 0,
          ∑' n : ℕ, (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t)) := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change (t : ℂ) ^ (s - 1) * F t =
        ∑' n : ℕ, (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))
      rw [← (hF t ht).tsum_eq]
      rw [← tsum_mul_left]
    _ = ∑' n : ℕ, ∫ t : ℝ in Set.Ioi 0,
          (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t)) := hsum.symm
    _ = ∑' n : ℕ, mellin W s * LSeries.term a s n := by simp_rw [hterm]
    _ = mellin W s * LSeries a s := hseries

theorem normFiber_compact_euler_identity
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal ShortDraftHeckeBridge.O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      ShortDraftHeckeBridge.normFiberCoeff weight n =
        ShortDraftHeckeBridge.pairInverseCoeff χ ψ n)
    (hcoeff0 : ShortDraftHeckeBridge.normFiberCoeff weight 0 = 0)
    (W F : ℝ → ℂ)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ =>
        ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t)) (F t))
    (s : ℂ) (hs : 1 < s.re)
    (hint : ∀ n : ℕ,
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s - 1) *
          (ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t)))
        (Set.Ioi 0))
    (hsumint : Summable (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi 0,
        ‖(t : ℂ) ^ (s - 1) *
          (ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t))‖)) :
    (χ.LFunction s * ψ.LFunction s) *
      mellin (fun D : ℝ => F D⁻¹) (-s) = mellin W s := by
  have hM := mellin_weighted_sum
    (ShortDraftHeckeBridge.normFiberCoeff weight) W F s hcoeff0 hF
    hint hsumint
    ((LSeriesSummable_congr s (fun {n} hn => hcoeff n hn)).mpr
      (ShortDraftHeckeBridge.pairInverseCoeff_LSeriesSummable χ ψ s hs))
  rw [hM,
    ShortDraftHeckeBridge.normFiber_LSeries_eq_pair_inverse χ ψ weight hcoeff s]
  have hEuler := ShortDraftHeckeBridge.pair_inverse_euler_identity χ ψ s hs
  calc
    (χ.LFunction s * ψ.LFunction s) *
        (mellin W s * LSeries (ShortDraftHeckeBridge.pairInverseCoeff χ ψ) s) =
        (χ.LFunction s * ψ.LFunction s *
          LSeries (ShortDraftHeckeBridge.pairInverseCoeff χ ψ) s) * mellin W s := by ring
    _ = mellin W s := by rw [hEuler]; ring

theorem weighted_sum_zero_of_large_t
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (W F : ℝ → ℂ)
    (hW : ∀ y : ℝ, 2 ≤ y → W y = 0)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) (F t))
    (t : ℝ) (ht : 2 ≤ t) : F t = 0 := by
  have hterm (n : ℕ) : a n * W ((n : ℝ) * t) = 0 := by
    by_cases hn : n = 0
    · simp [hn, ha0]
    · have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hnt : 2 ≤ (n : ℝ) * t := by
        calc
          2 ≤ t := ht
          _ = (1 : ℝ) * t := by ring
          _ ≤ (n : ℝ) * t :=
            mul_le_mul_of_nonneg_right hn1 (by linarith)
      simp [hW _ hnt]
  have hzero : HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) 0 := by
    simpa only [hterm] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  exact (hF t (lt_of_lt_of_le (by norm_num) ht)).unique hzero

theorem weighted_sum_zero_near_small_D
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (W F : ℝ → ℂ)
    (hW : ∀ y : ℝ, 2 ≤ y → W y = 0)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) (F t)) :
    (fun D : ℝ => F D⁻¹) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with D hD
  have hDpos : 0 < D := hD.1
  have hDsmall : D < 1 / 2 := hD.2
  have hDinvpos : 0 < D⁻¹ := inv_pos.mpr hDpos
  have hmul := mul_le_mul_of_nonneg_right (le_of_lt hDsmall) hDinvpos.le
  have hinv : 2 ≤ D⁻¹ := by
    rw [mul_inv_cancel₀ (ne_of_gt hDpos)] at hmul
    nlinarith
  exact weighted_sum_zero_of_large_t a ha0 W F hW hF D⁻¹ hinv

theorem compact_weight_mellin_analytic
    (W : ℝ → ℂ) (hW : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hsupp : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0)
    (σ : ℝ) :
    AnalyticOnNhd ℂ (mellin W) {s : ℂ | σ < s.re} := by
  let A : ℝ → ℂ := fun D => W D⁻¹
  have hcont : ContinuousOn A (Set.Ioi (0 : ℝ)) := by
    have hcontW : ContinuousOn W Set.univ := hW.continuous.continuousOn
    apply hcontW.comp
      (continuousOn_inv₀.mono (by
        intro D hD
        exact ne_of_gt hD))
    intro D hD
    simp
  have hlocal : LocallyIntegrableOn A (Set.Ioi (0 : ℝ)) :=
    hcont.locallyIntegrableOn measurableSet_Ioi
  have hzero : A =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with D hD
    have hDpos : 0 < D := hD.1
    have hDsmall : D < 1 / 2 := hD.2
    have hDinvpos : 0 < D⁻¹ := inv_pos.mpr hDpos
    have hmul := mul_le_mul_of_nonneg_right (le_of_lt hDsmall) hDinvpos.le
    have hinv : 2 ≤ D⁻¹ := by
      rw [mul_inv_cancel₀ (ne_of_gt hDpos)] at hmul
      nlinarith
    exact hsupp D⁻¹ (Or.inr hinv)
  have hzeroTop : A =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with D hD
    have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
    have hDinvpos : 0 < D⁻¹ := inv_pos.mpr hDpos
    have hmul := mul_le_mul_of_nonneg_right hD hDinvpos.le
    have hinv : D⁻¹ ≤ 1 := by
      rw [mul_inv_cancel₀ (ne_of_gt hDpos)] at hmul
      nlinarith
    exact hsupp D⁻¹ (Or.inl hinv)
  have htop : A =O[atTop] (fun D : ℝ => D ^ σ) :=
    hzeroTop.isBigO.trans (isBigO_zero _ _)
  have hM := ShortDraftMellin.inverse_mellin_analytic A σ hlocal htop hzero
  simpa only [A, mellin_comp_inv, neg_neg] using hM

theorem pair_zero_free_of_compact_weight_bound
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (weight : Ideal ShortDraftHeckeBridge.O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      ShortDraftHeckeBridge.normFiberCoeff weight n =
        ShortDraftHeckeBridge.pairInverseCoeff χ ψ n)
    (hcoeff0 : ShortDraftHeckeBridge.normFiberCoeff weight 0 = 0)
    (W F : ℝ → ℂ)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ =>
        ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t)) (F t))
    (hint : ∀ (s : ℂ), 1 < s.re → ∀ n : ℕ,
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s - 1) *
          (ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t)))
        (Set.Ioi 0))
    (hsumint : ∀ (s : ℂ), 1 < s.re → Summable (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi 0,
        ‖(t : ℂ) ^ (s - 1) *
          (ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t))‖))
    (σ : ℝ) (hσ : σ < 1)
    (hlocal : LocallyIntegrableOn (fun D : ℝ => F D⁻¹) (Set.Ioi 0))
    (hzero : (fun D : ℝ => F D⁻¹) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0))
    (htop : (fun D : ℝ => F D⁻¹) =O[atTop] (fun D : ℝ => D ^ σ))
    (hWanalytic : AnalyticOnNhd ℂ (mellin W) {s : ℂ | σ < s.re})
    (ρ : ℂ) (hρ : σ < ρ.re) (hWρ : mellin W ρ ≠ 0) :
    χ.LFunction ρ ≠ 0 ∧ ψ.LFunction ρ ≠ 0 := by
  let a : ℕ → ℂ := ShortDraftHeckeBridge.normFiberCoeff weight
  have ha0 : a 0 = 0 := hcoeff0
  have hMseries (s : ℂ) (hs : 1 < s.re) :
      mellin (fun D : ℝ => F D⁻¹) (-s) =
        mellin W s * LSeries a s := by
    apply mellin_weighted_sum a W F s ha0 (fun t ht => hF t ht)
      (hint s hs) (hsumint s hs)
    exact (LSeriesSummable_congr s (fun {n} hn => hcoeff n hn)).mpr
      (ShortDraftHeckeBridge.pairInverseCoeff_LSeriesSummable χ ψ s hs)
  let U : Set ℂ := {s : ℂ | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hLχ : AnalyticOnNhd ℂ χ.LFunction U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (χ.differentiable_LFunction hχ).differentiableOn
  have hLψ : AnalyticOnNhd ℂ ψ.LFunction U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (ψ.differentiable_LFunction hψ).differentiableOn
  have hL : AnalyticOnNhd ℂ (fun s => χ.LFunction s * ψ.LFunction s) U :=
    hLχ.mul hLψ
  have hM : AnalyticOnNhd ℂ
      (fun s : ℂ => mellin (fun D : ℝ => F D⁻¹) (-s)) U :=
    ShortDraftMellin.inverse_mellin_analytic _ σ hlocal htop hzero
  have heq (s : ℂ) (hs : 1 < s.re) :
      (χ.LFunction s * ψ.LFunction s) *
        mellin (fun D : ℝ => F D⁻¹) (-s) = mellin W s := by
    rw [hMseries s hs,
      ShortDraftHeckeBridge.normFiber_LSeries_eq_pair_inverse χ ψ weight hcoeff s]
    have hEuler := ShortDraftHeckeBridge.pair_inverse_euler_identity χ ψ s hs
    calc
      (χ.LFunction s * ψ.LFunction s) *
          (mellin W s * LSeries (ShortDraftHeckeBridge.pairInverseCoeff χ ψ) s) =
          (χ.LFunction s * ψ.LFunction s *
            LSeries (ShortDraftHeckeBridge.pairInverseCoeff χ ψ) s) * mellin W s := by ring
      _ = mellin W s := by rw [hEuler]; ring
  have hprod : χ.LFunction ρ * ψ.LFunction ρ ≠ 0 :=
    ShortDraft.zero_free_of_analytic_identity σ hσ
      (fun s => χ.LFunction s * ψ.LFunction s)
      (fun s => mellin (fun D : ℝ => F D⁻¹) (-s)) (mellin W)
      hL hM hWanalytic heq ρ hρ hWρ
  exact mul_ne_zero_iff.mp hprod

theorem pair_zero_free_of_weighted_identity_principal_left
    {q r : ℕ} [NeZero q] [NeZero r]
    (ψ : DirichletCharacter ℂ r) (hψ : ψ ≠ 1)
    (σ : ℝ) (hσ : σ < 1) (M W : ℂ → ℂ)
    (hM : AnalyticOnNhd ℂ M {s : ℂ | σ < s.re})
    (hW : AnalyticOnNhd ℂ W {s : ℂ | σ < s.re})
    (heq : ∀ s : ℂ, 1 < s.re →
      ((1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s) * M s = W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1) (hWρ : W ρ ≠ 0) :
    (1 : DirichletCharacter ℂ q).LFunction ρ ≠ 0 ∧
      ψ.LFunction ρ ≠ 0 := by
  let U : Set ℂ := {s : ℂ | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hLregular₁ : AnalyticOnNhd ℂ
      (DirichletCharacter.LFunctionTrivChar₁ q) U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).differentiableOn
  have hLψ : AnalyticOnNhd ℂ ψ.LFunction U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (ψ.differentiable_LFunction hψ).differentiableOn
  have hLregular : AnalyticOnNhd ℂ
      (fun s => DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s) U :=
    hLregular₁.mul hLψ
  have hregular : ∀ s : ℂ, σ < s.re → s ≠ 1 →
      DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s =
        (s - 1) * ((1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s) := by
    intro s _ hs
    simp [DirichletCharacter.LFunctionTrivChar₁,
      DirichletCharacter.LFunctionTrivChar, Function.update_of_ne hs]
    ring
  have heqregular : ∀ s : ℂ, 1 < s.re →
      (DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s) * M s =
        (s - 1) * W s := by
    intro s hs
    rw [hregular s (lt_trans hσ hs) (by
      intro h; subst s; norm_num at hs)]
    calc
      (s - 1) * ((1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s) * M s =
          (s - 1) * (((1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s) * M s) := by ring
      _ = (s - 1) * W s := by rw [heq s hs]
  have hprod :
      (1 : DirichletCharacter ℂ q).LFunction ρ * ψ.LFunction ρ ≠ 0 :=
    ShortDraft.zero_free_of_regularized_analytic_identity σ hσ
      (fun s => (1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s)
      (fun s => DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s)
      M W hLregular hM hW hregular heqregular ρ hρ hρone hWρ
  exact mul_ne_zero_iff.mp hprod

theorem pair_zero_free_of_compact_weight_bound_principal_left
    {q r : ℕ} [NeZero q] [NeZero r]
    (ψ : DirichletCharacter ℂ r) (hψ : ψ ≠ 1)
    (weight : Ideal ShortDraftHeckeBridge.O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      ShortDraftHeckeBridge.normFiberCoeff weight n =
        ShortDraftHeckeBridge.pairInverseCoeff
          (1 : DirichletCharacter ℂ q) ψ n)
    (hcoeff0 : ShortDraftHeckeBridge.normFiberCoeff weight 0 = 0)
    (W F : ℝ → ℂ)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ =>
        ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t)) (F t))
    (hint : ∀ (s : ℂ), 1 < s.re → ∀ n : ℕ,
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s - 1) *
          (ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t)))
        (Set.Ioi 0))
    (hsumint : ∀ (s : ℂ), 1 < s.re → Summable (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi 0,
        ‖(t : ℂ) ^ (s - 1) *
          (ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t))‖))
    (σ : ℝ) (hσ : σ < 1)
    (hlocal : LocallyIntegrableOn (fun D : ℝ => F D⁻¹) (Set.Ioi 0))
    (hzero : (fun D : ℝ => F D⁻¹) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0))
    (htop : (fun D : ℝ => F D⁻¹) =O[atTop] (fun D : ℝ => D ^ σ))
    (hWanalytic : AnalyticOnNhd ℂ (mellin W) {s : ℂ | σ < s.re})
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1)
    (hWρ : mellin W ρ ≠ 0) :
    (1 : DirichletCharacter ℂ q).LFunction ρ ≠ 0 ∧
      ψ.LFunction ρ ≠ 0 := by
  have hM : AnalyticOnNhd ℂ
      (fun s : ℂ => mellin (fun D : ℝ => F D⁻¹) (-s))
      {s : ℂ | σ < s.re} :=
    ShortDraftMellin.inverse_mellin_analytic _ σ hlocal htop hzero
  have heq (s : ℂ) (hs : 1 < s.re) :
      ((1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s) *
        mellin (fun D : ℝ => F D⁻¹) (-s) = mellin W s :=
    normFiber_compact_euler_identity 1 ψ weight hcoeff hcoeff0 W F
      hF s hs (hint s hs) (hsumint s hs)
  exact pair_zero_free_of_weighted_identity_principal_left ψ hψ σ hσ
    (fun s => mellin (fun D : ℝ => F D⁻¹) (-s)) (mellin W)
    hM hWanalytic heq ρ hρ hρone hWρ

theorem pair_zero_free_of_compact_weight_bound_principal_right
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (weight : Ideal ShortDraftHeckeBridge.O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      ShortDraftHeckeBridge.normFiberCoeff weight n =
        ShortDraftHeckeBridge.pairInverseCoeff χ
          (1 : DirichletCharacter ℂ r) n)
    (hcoeff0 : ShortDraftHeckeBridge.normFiberCoeff weight 0 = 0)
    (W F : ℝ → ℂ)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ =>
        ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t)) (F t))
    (hint : ∀ (s : ℂ), 1 < s.re → ∀ n : ℕ,
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s - 1) *
          (ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t)))
        (Set.Ioi 0))
    (hsumint : ∀ (s : ℂ), 1 < s.re → Summable (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi 0,
        ‖(t : ℂ) ^ (s - 1) *
          (ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t))‖))
    (σ : ℝ) (hσ : σ < 1)
    (hlocal : LocallyIntegrableOn (fun D : ℝ => F D⁻¹) (Set.Ioi 0))
    (hzero : (fun D : ℝ => F D⁻¹) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0))
    (htop : (fun D : ℝ => F D⁻¹) =O[atTop] (fun D : ℝ => D ^ σ))
    (hWanalytic : AnalyticOnNhd ℂ (mellin W) {s : ℂ | σ < s.re})
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1)
    (hWρ : mellin W ρ ≠ 0) :
    χ.LFunction ρ ≠ 0 ∧
      (1 : DirichletCharacter ℂ r).LFunction ρ ≠ 0 := by
  have hcoeff' : ∀ n : ℕ, n ≠ 0 →
      ShortDraftHeckeBridge.normFiberCoeff weight n =
        ShortDraftHeckeBridge.pairInverseCoeff
          (1 : DirichletCharacter ℂ r) χ n := by
    intro n hn
    rw [hcoeff n hn, ShortDraftHeckeBridge.pairInverseCoeff_comm]
  have h := pair_zero_free_of_compact_weight_bound_principal_left
    χ hχ weight hcoeff' hcoeff0 W F hF hint hsumint
    σ hσ hlocal hzero htop hWanalytic ρ hρ hρone hWρ
  exact ⟨h.2, h.1⟩

structure BaseChangeCompactTest
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) where
  W : ℝ → ℂ
  F : ℝ → ℂ
  sigma : ℝ
  sigma_pos : 0 < sigma
  sigma_lt : sigma < ρ.re
  smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) W
  support : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0
  sum_eq : ∀ t : ℝ, 0 < t →
    HasSum (fun n : ℕ =>
      ShortDraftHeckeBridge.normFiberCoeff
        (ShortDraftHeckeBridge.baseChangeWeight χ) n * W ((n : ℝ) * t)) (F t)
  term_integrable : ∀ (s : ℂ), 1 < s.re → ∀ n : ℕ,
    IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) *
        (ShortDraftHeckeBridge.normFiberCoeff
          (ShortDraftHeckeBridge.baseChangeWeight χ) n * W ((n : ℝ) * t)))
      (Set.Ioi 0)
  fubini : ∀ (s : ℂ), 1 < s.re → Summable (fun n : ℕ =>
    ∫ t : ℝ in Set.Ioi 0,
      ‖(t : ℂ) ^ (s - 1) *
        (ShortDraftHeckeBridge.normFiberCoeff
          (ShortDraftHeckeBridge.baseChangeWeight χ) n * W ((n : ℝ) * t))‖)
  locally_integrable : LocallyIntegrableOn
    (fun D : ℝ => F D⁻¹) (Set.Ioi 0)
  power_bound : (fun D : ℝ => F D⁻¹) =O[atTop]
    (fun D : ℝ => D ^ sigma)
  mellin_nonzero : mellin W ρ ≠ 0

theorem dirichletTarget_of_compact_normFiber_tests
    (hTest : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (ρ : ℂ), (23 / 24 : ℝ) < ρ.re → ρ.re < 1 →
        BaseChangeCompactTest χ ρ) :
    ShortDraft.DirichletTarget := by
  intro q _ χ ρ h23 hprincipal
  by_cases hρ : ρ.re < 1
  · let T := hTest q χ ρ h23 hρ
    have hσone : T.sigma < 1 := lt_trans T.sigma_lt hρ
    have hρone : ρ ≠ 1 := by
      intro hh
      subst ρ
      norm_num at hρ
    have hc := ShortDraftHeckeBridge.normFiberCoeff_baseChange_eq_pairInverseCoeff χ
    have hz := ShortDraftHeckeBridge.normFiberCoeff_baseChangeWeight_zero χ
    have hzeroTest :
        (fun D : ℝ => T.F D⁻¹) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) :=
      weighted_sum_zero_near_small_D
        (ShortDraftHeckeBridge.normFiberCoeff
          (ShortDraftHeckeBridge.baseChangeWeight χ)) hz T.W T.F
        (fun y hy => T.support y (Or.inr hy)) T.sum_eq
    have hWanalytic : AnalyticOnNhd ℂ (mellin T.W)
        {s : ℂ | T.sigma < s.re} :=
      compact_weight_mellin_analytic T.W T.smooth T.support T.sigma
    by_cases hχ : χ = 1
    · have hψ : ShortDraftHeckeBridge.baseChangeChar χ ≠ 1 :=
        ShortDraftHeckeBridge.baseChangeChar_ne_one_of_one χ hχ
      have hc' : ∀ n : ℕ, n ≠ 0 →
          ShortDraftHeckeBridge.normFiberCoeff
            (ShortDraftHeckeBridge.baseChangeWeight χ) n =
            ShortDraftHeckeBridge.pairInverseCoeff
              (1 : DirichletCharacter ℂ q)
              (ShortDraftHeckeBridge.baseChangeChar χ) n := by
        intro n hn
        simpa only [hχ] using hc n hn
      have hpair := pair_zero_free_of_compact_weight_bound_principal_left
        (q := q) (ShortDraftHeckeBridge.baseChangeChar χ) hψ
        (ShortDraftHeckeBridge.baseChangeWeight χ) hc' hz
        T.W T.F T.sum_eq T.term_integrable T.fubini
        T.sigma hσone T.locally_integrable hzeroTest T.power_bound
        hWanalytic ρ T.sigma_lt hρone T.mellin_nonzero
      simpa only [hχ] using hpair.1
    · by_cases hψ : ShortDraftHeckeBridge.baseChangeChar χ = 1
      · have hc' : ∀ n : ℕ, n ≠ 0 →
            ShortDraftHeckeBridge.normFiberCoeff
              (ShortDraftHeckeBridge.baseChangeWeight χ) n =
              ShortDraftHeckeBridge.pairInverseCoeff χ
                (1 : DirichletCharacter ℂ (q * 3)) n := by
          intro n hn
          simpa only [hψ] using hc n hn
        exact (pair_zero_free_of_compact_weight_bound_principal_right
          χ hχ (ShortDraftHeckeBridge.baseChangeWeight χ) hc' hz
          T.W T.F T.sum_eq T.term_integrable T.fubini
          T.sigma hσone T.locally_integrable hzeroTest T.power_bound
          hWanalytic ρ T.sigma_lt hρone T.mellin_nonzero).1
      · exact (pair_zero_free_of_compact_weight_bound
          χ (ShortDraftHeckeBridge.baseChangeChar χ) hχ hψ
          (ShortDraftHeckeBridge.baseChangeWeight χ) (fun n hn => hc n hn) hz
          T.W T.F T.sum_eq T.term_integrable T.fubini
          T.sigma hσone T.locally_integrable hzeroTest T.power_bound
          hWanalytic ρ T.sigma_lt T.mellin_nonzero).1
  · exact ShortDraft.dirichlet_target_of_one_le_re q χ ρ
      (le_of_not_gt hρ) hprincipal

end CompactMellinBridge

end

end OAI
end OAIOriginalModule0077

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.NormFiberExtraction
Source SHA256: e7d2b7ad532e2a7fd3b3910e970b904a92d9e56a8fc6bdfabcd60ac2e6eedf22
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0078


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

namespace ConcretePrimeRowBridge

section

open ActualEisensteinCubic ShortDraftHeckeBridge

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

instance : IsPrincipalIdealRing O :=
  IsCyclotomicExtension.Rat.three_pid K

noncomputable def idealGenerator (I : Ideal O) : O :=
  Submodule.IsPrincipal.generator I

theorem span_idealGenerator (I : Ideal O) :
    Ideal.span {idealGenerator I} = I := by
  exact Submodule.IsPrincipal.span_singleton_generator I

theorem idealGenerator_injective : Function.Injective idealGenerator := by
  intro I J h
  calc
    I = Ideal.span {idealGenerator I} := (span_idealGenerator I).symm
    _ = Ideal.span {idealGenerator J} := by rw [h]
    _ = J := span_idealGenerator J

noncomputable def idealsUpTo (D : ℕ) : Finset (Ideal O) :=
  (Finset.Icc 1 D).biUnion
    (fun n => (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset)

theorem mem_idealsUpTo {D : ℕ} {I : Ideal O} :
    I ∈ idealsUpTo D ↔ 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D := by
  classical
  simp [idealsUpTo, Finset.mem_biUnion, Finset.mem_Icc]

noncomputable def columnsUpTo (D : ℕ) : Finset O :=
  by
    classical
    exact (idealsUpTo D).image idealGenerator

noncomputable def columnWeight {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (x : O) : ℂ :=
  baseChangeWeight χ (Ideal.span {x}) * W (Ideal.absNorm (Ideal.span {x}))

theorem columnWeight_idealGenerator {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (I : Ideal O) :
    columnWeight χ W (idealGenerator I) =
      baseChangeWeight χ I * W (Ideal.absNorm I) := by
  simp [columnWeight, span_idealGenerator]

theorem columnsUpTo_sum_eq_ideal_sum {q D : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) :
    (∑ x ∈ columnsUpTo D, columnWeight χ W x) =
      ∑ I ∈ idealsUpTo D,
        baseChangeWeight χ I * W (Ideal.absNorm I) := by
  classical
  rw [columnsUpTo, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro I hI
    exact columnWeight_idealGenerator χ W I
  · intro I hI J hJ h
    exact idealGenerator_injective h

noncomputable def goodLambda : O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1

noncomputable def primePool (F : Finset (Ideal O)) : Finset (Ideal O) :=
  F.biUnion (fun I => (UniqueFactorizationMonoid.normalizedFactors I).toFinset)

theorem mem_primePool_iff {F : Finset (Ideal O)} {P : Ideal O} :
    P ∈ primePool F ↔
      ∃ I ∈ F, P ∈ UniqueFactorizationMonoid.normalizedFactors I := by
  classical
  simp only [primePool, Finset.mem_biUnion, Multiset.mem_toFinset]

theorem primePool_maximal (F : Finset (Ideal O))
    (_hFpos : ∀ I ∈ F, I ≠ ⊥) (i : primePool F) :
    (i.1).IsMaximal := by
  obtain ⟨I, hIF, hfac⟩ := mem_primePool_iff.mp i.property
  have hp : Prime i.1 := UniqueFactorizationMonoid.prime_of_normalized_factor i.1 hfac
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

theorem primePool_good (F : Finset (Ideal O))
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    (i : primePool F) : goodLambda ∉ i.1 := by
  obtain ⟨I, hIF, hfac⟩ := mem_primePool_iff.mp i.property
  exact hFgood I hIF i.1 hfac

noncomputable def idealSupport (F : Finset (Ideal O)) (I : Ideal O) :
    Finset (primePool F) :=
  Finset.univ.filter (fun i => i.1 ∈ UniqueFactorizationMonoid.normalizedFactors I)

theorem mem_idealSupport_iff (F : Finset (Ideal O)) (I : Ideal O)
    (i : primePool F) :
    i ∈ idealSupport F I ↔ i.1 ∈ UniqueFactorizationMonoid.normalizedFactors I := by
  classical
  simp [idealSupport]

theorem idealGenerator_mem_prime_of_support
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (I : Ideal O) (hIF : I ∈ F) (i : primePool F)
    (hi : i ∈ idealSupport F I) : idealGenerator I ∈ i.1 := by
  have hfac := (mem_idealSupport_iff F I i).mp hi
  have hle := ((Ideal.mem_normalizedFactors_iff (hFpos I hIF)).mp hfac).2
  have hmem : idealGenerator I ∈ Ideal.span {idealGenerator I} :=
    Ideal.subset_span (Set.mem_singleton _)
  rw [span_idealGenerator I] at hmem
  exact hle hmem

noncomputable def idealSexticRow
    (F : Finset (Ideal O))
    (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    (I : Ideal O) (u : O) : ℂ := by
  letI : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact ActualEisensteinCubic.finiteSquarefreeRow
    (fun i : primePool F => i.1) (primePool_good F hFgood)
    (idealSupport F I) u

theorem idealSexticRow_one
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    (I : Ideal O) : idealSexticRow F hFpos hFgood I 1 = 1 := by
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact ActualEisensteinCubic.finiteSquarefreeRow_one
    (fun i : primePool F => i.1) (primePool_good F hFgood)
    (idealSupport F I)

theorem baseChangeWeight_zero_of_not_squarefree {q : ℕ}
    (χ : DirichletCharacter ℂ q) (I : Ideal O)
    (hI : ¬ Squarefree I) : baseChangeWeight χ I = 0 := by
  rw [baseChangeWeight, UniqueFactorizationMonoid.moebius_of_not_squarefree hI]
  simp

private theorem idealMoebius_norm_le_one (I : Ideal O) :
    ‖((UniqueFactorizationMonoid.moebius I : ℤ) : ℂ)‖ ≤ 1 := by
  classical
  by_cases h : Squarefree I
  · rw [h.moebius_eq]
    simp
  · rw [UniqueFactorizationMonoid.moebius_of_not_squarefree h]
    simp

theorem baseChangeWeight_norm_le_one {q : ℕ}
    (χ : DirichletCharacter ℂ q) (I : Ideal O) :
    ‖baseChangeWeight χ I‖ ≤ 1 := by
  rw [baseChangeWeight, norm_mul]
  have hμ := idealMoebius_norm_le_one I
  have hχ := χ.norm_le_one (Ideal.absNorm I)
  exact (mul_le_mul hμ hχ (norm_nonneg _) (by positivity)).trans (by norm_num)

theorem columnWeight_norm_le_one {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ)
    (hW : ∀ n, ‖W n‖ ≤ 1) (x : O) :
    ‖columnWeight χ W x‖ ≤ 1 := by
  rw [columnWeight, norm_mul]
  have hμ := baseChangeWeight_norm_le_one χ (Ideal.span {x})
  have hW' := hW (Ideal.absNorm (Ideal.span {x}))
  exact (mul_le_mul hμ hW' (norm_nonneg _) (by positivity)).trans (by norm_num)

noncomputable def elementRow
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (u : O) : ℂ := by
  classical
  letI : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact ∑ x ∈ F.image idealGenerator,
    columnWeight χ W x *
      finiteSquarefreeRow (fun i : primePool F => i.1)
        (primePool_good F hFgood)
        (idealSupport F (Ideal.span {x})) u

noncomputable def idealRowSum
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (u : O) : ℂ :=
  ∑ I ∈ F,
    baseChangeWeight χ I * W (Ideal.absNorm I) *
      idealSexticRow F hFpos hFgood I u

theorem elementRow_eq_idealRowSum
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (u : O) :
    elementRow F hFpos hFgood χ W u =
      idealRowSum F hFpos hFgood χ W u := by
  classical
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  unfold elementRow idealRowSum
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro I hI
    rw [columnWeight_idealGenerator, span_idealGenerator]
    rfl
  · intro I hI J hJ h
    exact idealGenerator_injective h

theorem idealRowSum_one
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) :
    idealRowSum F hFpos hFgood χ W 1 =
      ∑ I ∈ F, baseChangeWeight χ I * W (Ideal.absNorm I) := by
  unfold idealRowSum
  apply Finset.sum_congr rfl
  intro I hI
  rw [idealSexticRow_one]
  ring

open ActualEisensteinCubic ShortDraftHeckeBridge
open scoped Classical

noncomputable def rowNormDisk (H : ℕ) : Finset O := by
  classical
  exact (ShortDraftLatticeCount.rowNormBall H).filter
    (fun u => 0 < Ideal.absNorm (Ideal.span {u}) ∧
      Ideal.absNorm (Ideal.span {u}) ≤ H)

theorem mem_rowNormDisk {H : ℕ} {u : O} :
    u ∈ rowNormDisk H ↔
      0 < Ideal.absNorm (Ideal.span {u}) ∧
      Ideal.absNorm (Ideal.span {u}) ≤ H := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr
      ⟨ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le H u h.2, h⟩

theorem sixth_power_rows_in_rowNormDisk
    {β : Type*} (selected : Finset β) (p : β → O)
    (D H : ℕ) (hD : 1 ≤ D)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hnormupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hH : Nat.floor ((D : ℝ) ^ (11 / 10 : ℝ)) ≤ H) :
    selected.image (fun i => p i ^ 6) ⊆ rowNormDisk H := by
  classical
  intro u hu
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
  rw [mem_rowNormDisk]
  have hpNorm : Ideal.absNorm (Ideal.span {p i}) ≠ 0 :=
    (Ideal.absNorm_eq_zero_iff).not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (hp i hi))
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  have hupper : (Ideal.absNorm (Ideal.span {p i ^ 6}) : ℝ) ≤
      (D : ℝ) ^ (11 / 10 : ℝ) := by
    calc
      (Ideal.absNorm (Ideal.span {p i ^ 6}) : ℝ) =
          (Ideal.absNorm (Ideal.span {p i}) : ℝ) ^ 6 := by
            exact_mod_cast ActualEisensteinCubic.principal_absNorm_pow (p i) 6
      _ ≤ ((D : ℝ) ^ (11 / 60 : ℝ)) ^ 6 := by
        gcongr
        exact hnormupper i hi
      _ = (D : ℝ) ^ (11 / 10 : ℝ) := by
        rw [← Real.rpow_mul_natCast hDpos.le (11 / 60 : ℝ) 6]
        congr 1
        norm_num
  constructor
  · rw [ActualEisensteinCubic.principal_absNorm_pow]
    exact pow_pos (Nat.pos_of_ne_zero hpNorm) 6
  · exact (Nat.le_floor hupper).trans hH

theorem baseChange_prime_extraction_from_MS
    {β : Type*} {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ)
    (F : Finset (Ideal O))
    (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    (hW : ∀ n, ‖W n‖ ≤ 1)
    (selected : Finset β) (p : β → O)
    (D H : ℕ) (ε : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hFnorm : ∀ I ∈ F, Ideal.absNorm I ≤ D)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hprime : ∀ i ∈ selected, (Ideal.span {p i} : Ideal O).IsMaximal)
    (hinj : Set.InjOn (fun i => (Ideal.span {p i} : Ideal O)) (selected : Set β))
    (hnormlower : ∀ i ∈ selected,
      (D : ℝ) ^ (11 / 60 : ℝ) / 2 ≤
        (Ideal.absNorm (Ideal.span {p i}) : ℝ))
    (hnormupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hH : Nat.floor ((D : ℝ) ^ (11 / 10 : ℝ)) ≤ H)
    (hcount : (D : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤ (selected.card : ℝ))
    (hmean :
      (∑ u ∈ rowNormDisk H,
        ‖idealRowSum F hFpos hFgood χ W u‖ ^ 2) ≤
        (D : ℝ) ^ ((21 / 10 : ℝ) + ε)) :
    ‖∑ I ∈ F, baseChangeWeight χ I * W (Ideal.absNorm I)‖ ≤
      384 * (D : ℝ) ^ ((23 / 24 : ℝ) + ε) := by
  classical
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  let P : primePool F → Ideal O := fun i => i.1
  let support : O → Finset (primePool F) :=
    fun x => idealSupport F (Ideal.span {x})
  let columns : Finset O := F.image idealGenerator
  let weight : O → ℂ := columnWeight χ W
  have hsupport : ∀ x ∈ columns, ∀ i ∈ support x, x ∈ P i := by
    intro x hx i hi
    obtain ⟨I, hIF, rfl⟩ := Finset.mem_image.mp hx
    dsimp [support, P] at hi ⊢
    rw [span_idealGenerator I] at hi
    exact idealGenerator_mem_prime_of_support F hFpos I hIF i hi
  have hcolnorm : ∀ x ∈ columns,
      Ideal.absNorm (Ideal.span {x}) ≤ D := by
    intro x hx
    obtain ⟨I, hIF, rfl⟩ := Finset.mem_image.mp hx
    rw [span_idealGenerator I]
    exact hFnorm I hIF
  have hweight : ∀ x ∈ columns, ‖weight x‖ ≤ 1 := by
    intro x hx
    exact columnWeight_norm_le_one χ W hW x
  have hmean' :
      (∑ u ∈ rowNormDisk H,
        ‖∑ x ∈ columns,
          weight x * finiteSquarefreeRow P (primePool_good F hFgood)
            (support x) u‖ ^ 2) ≤
        (D : ℝ) ^ ((21 / 10 : ℝ) + ε) := by
    calc
      _ = ∑ u ∈ rowNormDisk H,
          ‖idealRowSum F hFpos hFgood χ W u‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro u hu
            change ‖elementRow F hFpos hFgood χ W u‖ ^ 2 =
              ‖idealRowSum F hFpos hFgood χ W u‖ ^ 2
            rw [elementRow_eq_idealRowSum]
      _ ≤ _ := hmean
  have hrows : selected.image (fun i => p i ^ 6) ⊆ rowNormDisk H :=
    sixth_power_rows_in_rowNormDisk selected p D H hD hp hnormupper hH
  have hbound := finite_actual_prime_extraction_dyadic
    P (primePool_good F hFgood) columns support weight selected p
    (rowNormDisk H) D ε hD hε hp hprime hinj hrows
    hsupport hcolnorm hweight hnormlower hcount hmean'
  have hsum :
      (∑ x ∈ columns, weight x) =
        ∑ I ∈ F, baseChangeWeight χ I * W (Ideal.absNorm I) := by
    change (∑ x ∈ F.image idealGenerator, columnWeight χ W x) = _
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro I hIF
      exact columnWeight_idealGenerator χ W I
    · intro I hIF J hJF h
      exact idealGenerator_injective h
  rwa [hsum] at hbound

end

open ShortDraftHeckeBridge FiniteSFactor

noncomputable def outsideIdealsUpTo (S : Finset (Ideal O)) (D : ℕ) :
    Finset (Ideal O) := by
  classical
  exact (idealsUpTo D).filter (fun I => ∀ P ∈ S, ¬ P ∣ I)

theorem mem_outsideIdealsUpTo {S : Finset (Ideal O)} {D : ℕ}
    {I : Ideal O} :
    I ∈ outsideIdealsUpTo S D ↔
      1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D ∧
        (∀ P ∈ S, ¬ P ∣ I) := by
  classical
  simp [outsideIdealsUpTo, mem_idealsUpTo, and_assoc]

theorem outsideIdealsUpTo_ne_bot (S : Finset (Ideal O)) (D : ℕ)
    (I : Ideal O) (hI : I ∈ outsideIdealsUpTo S D) : I ≠ ⊥ := by
  have hn := (mem_outsideIdealsUpTo.mp hI).1
  intro h
  subst I
  simp at hn

theorem outsideIdealsUpTo_norm_le (S : Finset (Ideal O)) (D : ℕ)
    (I : Ideal O) (hI : I ∈ outsideIdealsUpTo S D) :
    Ideal.absNorm I ≤ D :=
  (mem_outsideIdealsUpTo.mp hI).2.1

theorem goodLambda_prime : Prime goodLambda := by
  let : IsCyclotomicExtension {3} ℚ K :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'

theorem goodLambdaIdeal_maximal :
    (Ideal.span {goodLambda} : Ideal O).IsMaximal := by
  have hp : (Ideal.span {goodLambda} : Ideal O).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime goodLambda_prime
  have hne : (Ideal.span {goodLambda} : Ideal O) ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr goodLambda_prime.ne_zero
  exact hp.isMaximal hne

theorem badPrime_cover_of_lambdaIdeal_mem
    (S : Finset (Ideal O))
    (hS : (Ideal.span {goodLambda} : Ideal O) ∈ S) :
    ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S := by
  intro P hP hmem
  have hle : (Ideal.span {goodLambda} : Ideal O) ≤ P :=
    (Ideal.span_singleton_le_iff_mem P).mpr hmem
  have heq : (Ideal.span {goodLambda} : Ideal O) = P :=
    goodLambdaIdeal_maximal.eq_of_le hP.ne_top hle
  rwa [heq] at hS

theorem outsideIdealsUpTo_good
    (S : Finset (Ideal O)) (D : ℕ)
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (I : Ideal O) (hI : I ∈ outsideIdealsUpTo S D)
    (Q : Ideal O) (hQ : Q ∈ UniqueFactorizationMonoid.normalizedFactors I) :
    goodLambda ∉ Q := by
  intro hmemLam
  have hne : I ≠ ⊥ := outsideIdealsUpTo_ne_bot S D I hI
  have hp : Prime Q := UniqueFactorizationMonoid.prime_of_normalized_factor Q hQ
  have hmax : Q.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hQS : Q ∈ S := hSbad Q hmax hmemLam
  have hdiv : Q ∣ I := (Ideal.dvd_iff_le).mpr
    ((Ideal.mem_normalizedFactors_iff hne).mp hQ).2
  exact (mem_outsideIdealsUpTo.mp hI).2.2 Q hQS hdiv

theorem idealsUpTo_eq_biUnion_fibers (D : ℕ) :
    idealsUpTo D =
      (Finset.Icc 1 D).biUnion FiniteSFactor.fiber := by
  rfl

private theorem normFibers_pairwiseDisjoint (D : ℕ) :
    ((Finset.Icc 1 D : Finset ℕ) : Set ℕ).PairwiseDisjoint
      FiniteSFactor.fiber := by
  intro n hn m hm hnm
  apply Finset.disjoint_left.mpr
  intro I hIn hIm
  exact hnm ((FiniteSFactor.mem_fiber.mp hIn).symm.trans
    (FiniteSFactor.mem_fiber.mp hIm))

theorem outsideIdealSum_eq_outsideCoeff_sum
    (S : Finset (Ideal O)) (D : ℕ)
    (w : Ideal O → ℂ) (W : ℕ → ℂ) :
    (∑ I ∈ outsideIdealsUpTo S D,
      w I * W (Ideal.absNorm I)) =
      ∑ n ∈ Finset.Icc 1 D,
        FiniteSFactor.outsideCoeff S w n * W n := by
  classical
  have hsets : outsideIdealsUpTo S D =
      (Finset.Icc 1 D).biUnion (fun n =>
        (FiniteSFactor.fiber n).filter (fun I => ∀ P ∈ S, ¬P ∣ I)) := by
    ext I
    simp [outsideIdealsUpTo, idealsUpTo_eq_biUnion_fibers,
      FiniteSFactor.mem_fiber, Finset.mem_biUnion]
  rw [hsets, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [FiniteSFactor.outsideCoeff, Finset.sum_mul, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro I hI
    rw [FiniteSFactor.mem_fiber.mp hI]
    by_cases hgood : ∀ P ∈ S, ¬P ∣ I <;>
      simp [FiniteSFactor.outsideWeight, hgood]
  · intro n hn m hm hnm
    exact Finset.disjoint_filter_filter
      (normFibers_pairwiseDisjoint D hn hm hnm)

theorem outsideCoeff_prime_extraction_from_MS
    {β : Type*} {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ)
    (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (hW : ∀ n, ‖W n‖ ≤ 1)
    (selected : Finset β) (p : β → O)
    (D H : ℕ) (ε : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hprime : ∀ i ∈ selected, (Ideal.span {p i} : Ideal O).IsMaximal)
    (hinj : Set.InjOn (fun i => (Ideal.span {p i} : Ideal O)) (selected : Set β))
    (hnormlower : ∀ i ∈ selected,
      (D : ℝ) ^ (11 / 60 : ℝ) / 2 ≤
        (Ideal.absNorm (Ideal.span {p i}) : ℝ))
    (hnormupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hH : Nat.floor ((D : ℝ) ^ (11 / 10 : ℝ)) ≤ H)
    (hcount : (D : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤ (selected.card : ℝ))
    (hmean :
      (∑ u ∈ rowNormDisk H,
        ‖idealRowSum (outsideIdealsUpTo S D)
            (outsideIdealsUpTo_ne_bot S D)
            (outsideIdealsUpTo_good S D hSbad)
            χ W u‖ ^ 2) ≤
        (D : ℝ) ^ ((21 / 10 : ℝ) + ε)) :
    ‖∑ n ∈ Finset.Icc 1 D,
        FiniteSFactor.outsideCoeff S (baseChangeWeight χ) n * W n‖ ≤
      384 * (D : ℝ) ^ ((23 / 24 : ℝ) + ε) := by
  let F := outsideIdealsUpTo S D
  have hbound := baseChange_prime_extraction_from_MS χ W F
    (outsideIdealsUpTo_ne_bot S D)
    (outsideIdealsUpTo_good S D hSbad)
    hW selected p D H ε hD hε
    (outsideIdealsUpTo_norm_le S D)
    hp hprime hinj hnormlower hnormupper hH hcount hmean
  simpa only [F, outsideIdealSum_eq_outsideCoeff_sum] using hbound

open ShortDraftHeckeBridge FiniteSFactor Filter

theorem eventually_absorb_MS_and_count_constants
    (Cmean Ccount eta : ℝ) (hcount : 0 < Ccount) (heta : 0 < eta) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      Cmean ≤ (D : ℝ) ^ eta ∧ 1 ≤ Ccount * (D : ℝ) ^ eta := by
  have hpow : Tendsto (fun D : ℕ => (D : ℝ) ^ eta) atTop atTop :=
    (tendsto_rpow_atTop heta).comp tendsto_natCast_atTop_atTop
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp
    (hpow.eventually_ge_atTop (max Cmean Ccount⁻¹))
  refine ⟨D₀, fun D hD => ?_⟩
  have hlarge := hD₀ D hD
  constructor
  · exact (le_max_left _ _).trans hlarge
  · have hinv : Ccount⁻¹ ≤ (D : ℝ) ^ eta :=
      (le_max_right _ _).trans hlarge
    have hmul := mul_le_mul_of_nonneg_left hinv hcount.le
    simpa [hcount.ne'] using hmul

theorem outsideCoeff_prime_extraction_with_constants
    {β : Type*} {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ)
    (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (hW : ∀ n, ‖W n‖ ≤ 1)
    (selected : Finset β) (p : β → O)
    (D H : ℕ) (ε : ℝ) (eta : ℝ) (Cmean Ccount : ℝ)
    (hD : 1 ≤ D) (hε : 0 ≤ ε) (heta : 0 ≤ eta)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hprime : ∀ i ∈ selected, (Ideal.span {p i} : Ideal O).IsMaximal)
    (hinj : Set.InjOn (fun i => (Ideal.span {p i} : Ideal O)) (selected : Set β))
    (hnormlower : ∀ i ∈ selected,
      (D : ℝ) ^ (11 / 60 : ℝ) / 2 ≤
        (Ideal.absNorm (Ideal.span {p i}) : ℝ))
    (hnormupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hH : Nat.floor ((D : ℝ) ^ (11 / 10 : ℝ)) ≤ H)
    (hcount : Ccount * (D : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤
      (selected.card : ℝ))
    (hmean :
      (∑ u ∈ rowNormDisk H,
        ‖idealRowSum (outsideIdealsUpTo S D)
            (outsideIdealsUpTo_ne_bot S D)
            (outsideIdealsUpTo_good S D hSbad)
            χ W u‖ ^ 2) ≤
        Cmean * (D : ℝ) ^ ((21 / 10 : ℝ) + ε))
    (hmeanAbsorb : Cmean ≤ (D : ℝ) ^ eta)
    (hcountAbsorb : 1 ≤ Ccount * (D : ℝ) ^ eta) :
    ‖∑ n ∈ Finset.Icc 1 D,
        FiniteSFactor.outsideCoeff S (baseChangeWeight χ) n * W n‖ ≤
      384 * (D : ℝ) ^ ((23 / 24 : ℝ) + (ε + eta)) := by
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  have hcount' :
      (D : ℝ) ^ ((11 / 60 : ℝ) - (ε + eta)) ≤
        (selected.card : ℝ) := by
    calc
      (D : ℝ) ^ ((11 / 60 : ℝ) - (ε + eta)) =
          1 * (D : ℝ) ^ ((11 / 60 : ℝ) - (ε + eta)) := by ring
      _ ≤ (Ccount * (D : ℝ) ^ eta) *
          (D : ℝ) ^ ((11 / 60 : ℝ) - (ε + eta)) :=
            mul_le_mul_of_nonneg_right hcountAbsorb
              (Real.rpow_nonneg hDpos.le _)
      _ = Ccount * (D : ℝ) ^ ((11 / 60 : ℝ) - ε) := by
            rw [mul_assoc, ← Real.rpow_add hDpos]
            congr 1
            ring_nf
      _ ≤ (selected.card : ℝ) := hcount
  have hmean' :
      (∑ u ∈ rowNormDisk H,
        ‖idealRowSum (outsideIdealsUpTo S D)
            (outsideIdealsUpTo_ne_bot S D)
            (outsideIdealsUpTo_good S D hSbad)
            χ W u‖ ^ 2) ≤
        (D : ℝ) ^ ((21 / 10 : ℝ) + (ε + eta)) := by
    calc
      _ ≤ Cmean * (D : ℝ) ^ ((21 / 10 : ℝ) + ε) := hmean
      _ ≤ (D : ℝ) ^ eta * (D : ℝ) ^ ((21 / 10 : ℝ) + ε) :=
          mul_le_mul_of_nonneg_right hmeanAbsorb
            (Real.rpow_nonneg hDpos.le _)
      _ = (D : ℝ) ^ ((21 / 10 : ℝ) + (ε + eta)) := by
          rw [← Real.rpow_add hDpos]
          congr 1
          ring
  exact outsideCoeff_prime_extraction_from_MS χ W S hSbad hW selected p
    D H (ε + eta) hD (add_nonneg hε heta) hp hprime hinj
    hnormlower hnormupper hH hcount' hmean'

end ConcretePrimeRowBridge

end

end OAI
end OAIOriginalModule0078

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.SecondPoissonScale
Source SHA256: 5453ff3e38024577604c103d57018cad7f4caecc57297192d2de6c56fa9a99d5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0079


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

theorem second_prefactor_identity
    (Y qe qg qx₁ qx₂ Li : ℝ)
    (hqe : 0 < qe) (hqg : 0 < qg) (hqx₁ : 0 < qx₁)
    (hqx₂ : 0 < qx₂) (hLi : 0 < Li) :
    Y / (qe * Real.sqrt ((qx₁ / qg) * (qx₂ / qg))) =
      (Y * qg / (qe * Li)) * Real.sqrt (Li / qx₁) * Real.sqrt (Li / qx₂) := by
  have hs1 : Real.sqrt (qx₁ / qg) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (div_pos hqx₁ hqg))
  have hs2 : Real.sqrt (qx₂ / qg) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (div_pos hqx₂ hqg))
  have ht1 : Real.sqrt (Li / qx₁) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (div_pos hLi hqx₁))
  have ht2 : Real.sqrt (Li / qx₂) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (div_pos hLi hqx₂))
  have hqg0 : qg ≠ 0 := ne_of_gt hqg
  have hqe0 : qe ≠ 0 := ne_of_gt hqe
  have hLi0 : Li ≠ 0 := ne_of_gt hLi
  have hqx10 : qx₁ ≠ 0 := ne_of_gt hqx₁
  have hqx20 : qx₂ ≠ 0 := ne_of_gt hqx₂
  rw [Real.sqrt_mul (le_of_lt (div_pos hqx₁ hqg))]
  have ha : Real.sqrt (qx₁ / qg) * Real.sqrt (Li / qx₁) = Real.sqrt (Li / qg) := by
    rw [← Real.sqrt_mul (le_of_lt (div_pos hqx₁ hqg))]
    congr 1
    field_simp
  have hb : Real.sqrt (qx₂ / qg) * Real.sqrt (Li / qx₂) = Real.sqrt (Li / qg) := by
    rw [← Real.sqrt_mul (le_of_lt (div_pos hqx₂ hqg))]
    congr 1
    field_simp
  have hc : Real.sqrt (Li / qg) * Real.sqrt (Li / qg) = Li / qg := by
    simpa [pow_two] using Real.sq_sqrt (le_of_lt (div_pos hLi hqg))
  have hmain :
      Real.sqrt (Li / qx₁) * Real.sqrt (Li / qx₂) *
        (Real.sqrt (qx₁ / qg) * Real.sqrt (qx₂ / qg)) = Li / qg := by
    calc
      _ = (Real.sqrt (qx₁ / qg) * Real.sqrt (Li / qx₁)) *
          (Real.sqrt (qx₂ / qg) * Real.sqrt (Li / qx₂)) := by ring
      _ = Li / qg := by rw [ha, hb, hc]
  apply (div_eq_iff (mul_ne_zero hqe0 (mul_ne_zero hs1 hs2))).2
  calc
    Y = (Y * qg / (qe * Li)) * ((Li / qg) * qe) := by field_simp
    _ = ((Y * qg / (qe * Li)) * Real.sqrt (Li / qx₁) * Real.sqrt (Li / qx₂)) *
          (qe * (Real.sqrt (qx₁ / qg) * Real.sqrt (qx₂ / qg))) := by
       rw [← hmain]
       ring

namespace ActualEisensteinCubic

section

open scoped ComplexConjugate

theorem canonicalSextic_conj_as_row_label
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) (e : O) :
    star (canonicalSextic P hgood (Ideal.Quotient.mk P e)) =
      canonicalSextic P hgood (Ideal.Quotient.mk P e) *
        (canonicalSextic P hgood (Ideal.Quotient.mk P e)) ^ 4 := by
  let χ := canonicalSextic P hgood
  let x : O ⧸ P := Ideal.Quotient.mk P e
  have hconj : star (χ x) = (χ x)⁻¹ := by
    by_cases hx : IsUnit x
    · let u : (O ⧸ P)ˣ := hx.unit
      have hu : (u : O ⧸ P) = x := hx.unit_spec
      rw [← hu]
      exact (canonicalSextic_inverse_eq_conj_on_units P hgood u).symm
    · have hzero : χ x = 0 := MulChar.map_nonunit χ hx
      simp [hzero]
  rw [hconj]
  by_cases hx : IsUnit x
  · have h6 : (χ x) ^ 6 = 1 := by
      rw [← MulChar.pow_apply' χ (by decide : 6 ≠ 0),
        canonicalSextic_pow_six P hgood]
      exact MulChar.one_apply hx
    apply inv_eq_of_mul_eq_one_right
    calc
      χ x * (χ x * (χ x) ^ 4) = (χ x) ^ 6 := by ring
      _ = 1 := h6
  · have hzero : χ x = 0 := MulChar.map_nonunit χ hx
    change (χ x)⁻¹ = χ x * (χ x) ^ 4
    simp [hzero]

theorem canonicalSextic_second_child
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (d e k J C v : O) :
    star (canonicalSextic P hgood (Ideal.Quotient.mk P e)) *
      canonicalSextic P hgood (Ideal.Quotient.mk P d) *
      canonicalSextic P hgood (Ideal.Quotient.mk P k) *
      (canonicalSextic P hgood (Ideal.Quotient.mk P (J * C))) ^ 4 *
      (canonicalSextic P hgood (Ideal.Quotient.mk P v)) ^ 4 =
    canonicalSextic P hgood (Ideal.Quotient.mk P (d * e * k)) *
      (canonicalSextic P hgood (Ideal.Quotient.mk P (J * C * e * v))) ^ 4 := by
  rw [canonicalSextic_conj_as_row_label P hgood e]
  simp only [map_mul]
  ring

theorem finiteSquarefreeRow_mul
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (a b : O) :
    finiteSquarefreeRow P hgood S (a * b) =
      finiteSquarefreeRow P hgood S a * finiteSquarefreeRow P hgood S b := by
  classical
  simp only [finiteSquarefreeRow, map_mul, Finset.prod_mul_distrib]

theorem finiteSquarefreeRow_conj_as_row_label
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (e : O) :
    star (finiteSquarefreeRow P hgood S e) =
      finiteSquarefreeRow P hgood S e *
        (finiteSquarefreeRow P hgood S e) ^ 4 := by
  classical
  simp only [finiteSquarefreeRow, star_prod]
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact canonicalSextic_conj_as_row_label (P i) (hgood i) e

theorem finiteSquarefreeRow_second_child
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι)
    (d e k J C v : O) :
    star (finiteSquarefreeRow P hgood S e) *
      finiteSquarefreeRow P hgood S d *
      finiteSquarefreeRow P hgood S k *
      (finiteSquarefreeRow P hgood S (J * C)) ^ 4 *
      (finiteSquarefreeRow P hgood S v) ^ 4 =
    finiteSquarefreeRow P hgood S (d * e * k) *
      (finiteSquarefreeRow P hgood S (J * C * e * v)) ^ 4 := by
  rw [finiteSquarefreeRow_conj_as_row_label P hgood S e]
  simp only [finiteSquarefreeRow_mul]
  ring

end

noncomputable def rowCoprimeMask
    {ι : Type*} (P : ι → Ideal O) (S : Finset ι) (u : O) : ℂ := by
  classical
  exact if ∃ i ∈ S, u ∈ P i then 0 else 1

theorem finiteSquarefreeRow_self_pair
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1 ∉ P i)
    (S : Finset ι) (u : O) :
    star (finiteSquarefreeRow P hgood S u) * finiteSquarefreeRow P hgood S u =
      rowCoprimeMask P S u := by
  classical
  unfold finiteSquarefreeRow rowCoprimeMask
  rw [star_prod, ← Finset.prod_mul_distrib]
  by_cases h : ∃ i ∈ S, u ∈ P i
  · rw [ite_eq_left h]
    obtain ⟨i, hi, hui⟩ := h
    apply Finset.prod_eq_zero hi
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hui, MulChar.map_zero]
    simp
  · rw [ite_eq_right h]
    apply Finset.prod_eq_one
    intro i hi
    rw [MulChar.star_apply', ← MulChar.mul_apply, inv_mul_cancel]
    apply MulChar.one_apply
    let : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
    exact isUnit_iff_ne_zero.mpr fun hui => h ⟨i, hi, Ideal.Quotient.eq_zero_iff_mem.mp hui⟩

theorem finiteSquarefreeRow_pair_kernel
    {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1 ∉ P i)
    (S T : Finset ι) (u : O) :
    star (finiteSquarefreeRow P hgood S u) * finiteSquarefreeRow P hgood T u =
      rowCoprimeMask P (S ∩ T) u *
        star (finiteSquarefreeRow P hgood (S \ T) u) *
        finiteSquarefreeRow P hgood (T \ S) u := by
  have hsplit (A B : Finset ι) :
      finiteSquarefreeRow P hgood A u =
        finiteSquarefreeRow P hgood (A ∩ B) u *
        finiteSquarefreeRow P hgood (A \ B) u := by
    exact (Finset.prod_inter_mul_prod_sdiff A B _).symm
  rw [hsplit S T, hsplit T S, Finset.inter_comm T S, star_mul]
  calc
    _ = (star (finiteSquarefreeRow P hgood (S ∩ T) u) *
          finiteSquarefreeRow P hgood (S ∩ T) u) *
        star (finiteSquarefreeRow P hgood (S \ T) u) *
        finiteSquarefreeRow P hgood (T \ S) u := by ring
    _ = _ := by rw [finiteSquarefreeRow_self_pair]

private theorem mask_powerset {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (p : ι → Prop) [DecidablePred p] :
    (if ∃ i ∈ S, p i then (0 : ℂ) else 1) =
      ∑ E ∈ S.powerset, (-1 : ℂ) ^ E.card *
        if ∀ i ∈ E, p i then 1 else 0 := by
  have hprod : (if ∃ i ∈ S, p i then (0 : ℂ) else 1) =
      ∏ i ∈ S, (1 - if p i then (1 : ℂ) else 0) := by
    by_cases h : ∃ i ∈ S, p i
    · rw [ite_eq_left h]
      obtain ⟨i, hi, hp⟩ := h
      symm
      apply Finset.prod_eq_zero hi
      simp [hp]
    · rw [ite_eq_right h]
      symm
      apply Finset.prod_eq_one
      intro i hi
      simp [show ¬p i from fun hp => h ⟨i, hi, hp⟩]
  rw [hprod, Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro E hE
  simp only [Finset.prod_const_one, mul_one]
  congr 1
  by_cases h : ∀ i ∈ E, p i
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro i hi
    simp [h i hi]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨i, hi, hp⟩ := h
    apply Finset.prod_eq_zero hi
    simp [hp]

theorem rowCoprimeMask_subsets
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι) (u : O) :
    rowCoprimeMask P S u =
      ∑ E ∈ S.powerset, (-1 : ℂ) ^ E.card *
        if ∀ i ∈ E, u ∈ P i then 1 else 0 := by
  classical
  exact mask_powerset S (fun i => u ∈ P i)

theorem finiteSquarefreeRow_pair_sum_mobius
    {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1 ∉ P i)
    (S T : Finset ι) (R : Finset O) (V : O → ℂ) :
    (∑ u ∈ R, V u * star (finiteSquarefreeRow P hgood S u) *
      finiteSquarefreeRow P hgood T u) =
      ∑ E ∈ (S ∩ T).powerset, (-1 : ℂ) ^ E.card *
        ∑ u ∈ R.filter (fun u => ∀ i ∈ E, u ∈ P i),
          V u * star (finiteSquarefreeRow P hgood (S \ T) u) *
            finiteSquarefreeRow P hgood (T \ S) u := by
  classical
  have hterm (u : O) :
      V u * star (finiteSquarefreeRow P hgood S u) *
          finiteSquarefreeRow P hgood T u =
        ∑ E ∈ (S ∩ T).powerset, (-1 : ℂ) ^ E.card *
          if ∀ i ∈ E, u ∈ P i then
            V u * star (finiteSquarefreeRow P hgood (S \ T) u) *
              finiteSquarefreeRow P hgood (T \ S) u else 0 := by
    rw [mul_assoc, finiteSquarefreeRow_pair_kernel, rowCoprimeMask_subsets]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro E hE
    by_cases h : ∀ i ∈ E, u ∈ P i
    · simp only [ite_eq_left h, mul_one]
      ring
    · simp only [ite_eq_right h, mul_zero, zero_mul]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E hE
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases h : ∀ i ∈ E, u ∈ P i <;> simp [h]

private theorem finite_energy_expand {α β : Type*}
    (R : Finset α) (C : Finset β) (V : α → ℂ) (a : β → ℂ)
    (r : β → α → ℂ) :
    (∑ u ∈ R, V u * (↑(‖∑ n ∈ C, a n * r n u‖ ^ 2) : ℂ)) =
      ∑ n ∈ C, ∑ m ∈ C, star (a n) * a m *
        ∑ u ∈ R, V u * star (r n u) * r m u := by
  have hnorm (u : α) :
      (↑(‖∑ n ∈ C, a n * r n u‖ ^ 2) : ℂ) =
        (∑ n ∈ C, star (a n) * star (r n u)) *
          (∑ m ∈ C, a m * r m u) := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    simp only [map_sum, map_mul, starRingEnd_apply]
  simp_rw [hnorm]
  calc
    _ = ∑ u ∈ R, ∑ n ∈ C, ∑ m ∈ C,
        (star (a n) * a m) * (V u * star (r n u) * r m u) := by
      apply Finset.sum_congr rfl
      intro u hu
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]

theorem finiteSquarefreeRow_mean_square_mobius
    {ι β : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1 ∉ P i)
    (C : Finset β) (support : β → Finset ι) (a : β → ℂ)
    (R : Finset O) (V : O → ℂ) :
    (∑ u ∈ R, V u * (↑(‖∑ n ∈ C,
      a n * finiteSquarefreeRow P hgood (support n) u‖ ^ 2) : ℂ)) =
      ∑ n ∈ C, ∑ m ∈ C, star (a n) * a m *
        ∑ E ∈ (support n ∩ support m).powerset, (-1 : ℂ) ^ E.card *
          ∑ u ∈ R.filter (fun u => ∀ i ∈ E, u ∈ P i),
            V u * star (finiteSquarefreeRow P hgood (support n \ support m) u) *
              finiteSquarefreeRow P hgood (support m \ support n) u := by
  rw [finite_energy_expand]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  exact finiteSquarefreeRow_pair_sum_mobius P hgood (support n) (support m) R V

theorem prime_product_moebius
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hprime : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (S : Finset ι) :
    (UniqueFactorizationMonoid.moebius (∏ i ∈ S, P i) : ℂ) =
      (-1 : ℂ) ^ S.card := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, UniqueFactorizationMonoid.moebius_one, Int.cast_one, Finset.card_empty, pow_zero]
  | @insert i S hi ih =>
    have hcop : IsCoprime (P i) (∏ j ∈ S, P j) := by
      apply IsCoprime.prod_right
      intro j hj
      apply Ideal.isCoprime_of_isMaximal
      exact hinj.ne (by intro h; subst j; exact hi hj)
    rw [Finset.prod_insert hi, hcop.isRelPrime.moebius_mul,
      (hprime i).irreducible.moebius_eq, Int.cast_mul, Int.cast_neg,
      Int.cast_one, ih, Finset.card_insert_of_notMem hi, pow_succ]
    ring

theorem mem_prime_product_iff
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (u : O) :
    u ∈ (∏ i ∈ S, P i) ↔ ∀ i ∈ S, u ∈ P i := by
  rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime]
  · simp
  · intro i hi j hj hij
    exact Ideal.isCoprime_of_isMaximal (hinj.ne hij)

end ActualEisensteinCubic

namespace ConcretePrimeRowBridge

section

open ActualEisensteinCubic ShortDraftHeckeBridge
open scoped BigOperators Classical

noncomputable def primeSubsetProduct (F : Finset (Ideal O))
    (E : Finset (primePool F)) : Ideal O := ∏ i ∈ E, i.1

noncomputable def residualSexticRow
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    (I J : Ideal O) (u : O) : ℂ := by
  letI : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact finiteSquarefreeRow (fun i : primePool F => i.1)
    (primePool_good F hFgood) (idealSupport F I \ idealSupport F J) u

theorem idealRowSum_mean_square_mobius
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ)
    (R : Finset O) (V : O → ℂ) :
    (∑ u ∈ R, V u * (↑(‖idealRowSum F hFpos hFgood χ W u‖ ^ 2) : ℂ)) =
      ∑ I ∈ F, ∑ J ∈ F,
        star (baseChangeWeight χ I * W (Ideal.absNorm I)) *
          (baseChangeWeight χ J * W (Ideal.absNorm J)) *
        ∑ E ∈ (idealSupport F I ∩ idealSupport F J).powerset,
          (UniqueFactorizationMonoid.moebius (primeSubsetProduct F E) : ℂ) *
          ∑ u ∈ R.filter (fun u => u ∈ primeSubsetProduct F E),
            V u * star (residualSexticRow F hFpos hFgood I J u) *
              residualSexticRow F hFpos hFgood J I u := by
  classical
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  have hprime (i : primePool F) : Prime i.1 := by
    obtain ⟨I, hIF, hi⟩ := mem_primePool_iff.mp i.property
    exact UniqueFactorizationMonoid.prime_of_normalized_factor i.1 hi
  change (∑ u ∈ R, V u * (↑(‖∑ I ∈ F,
    (baseChangeWeight χ I * W (Ideal.absNorm I)) *
      finiteSquarefreeRow (fun i : primePool F => i.1)
        (primePool_good F hFgood) (idealSupport F I) u‖ ^ 2) : ℂ)) = _
  erw [finiteSquarefreeRow_mean_square_mobius]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  congr 1
  apply Finset.sum_congr rfl
  intro E hE
  rw [show (UniqueFactorizationMonoid.moebius (primeSubsetProduct F E) : ℂ) =
    (-1 : ℂ) ^ E.card from
      prime_product_moebius (fun i : primePool F => i.1)
        hprime Subtype.val_injective E]
  congr 1
  apply Finset.sum_congr
  · ext u
    simp only [Finset.mem_filter]
    exact and_congr_right fun hu =>
      (mem_prime_product_iff (fun i : primePool F => i.1)
        Subtype.val_injective E u).symm
  · intro u hu
    rfl

end

open ActualEisensteinCubic

theorem idealSupport_product_dvd
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (I : Ideal O) (E : Finset (primePool F))
    (hE : E ⊆ idealSupport F I) :
    (∏ i ∈ E, i.1) ∣ I := by
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    apply Ideal.isCoprime_of_isMaximal
    exact Subtype.val_injective.ne hij
  · intro i hi
    exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors
      ((mem_idealSupport_iff F I i).mp (hE hi))

theorem commonSupport_product_dvd
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (I J : Ideal O) (E : Finset (primePool F))
    (hE : E ∈ (idealSupport F I ∩ idealSupport F J).powerset) :
    (∏ i ∈ E, i.1) ∣ I ∧ (∏ i ∈ E, i.1) ∣ J := by
  have hsub := Finset.mem_powerset.mp hE
  exact ⟨idealSupport_product_dvd F hFpos I E
    (fun i hi => (Finset.mem_inter.mp (hsub hi)).1),
    idealSupport_product_dvd F hFpos J E
    (fun i hi => (Finset.mem_inter.mp (hsub hi)).2)⟩

end ConcretePrimeRowBridge

namespace EisensteinSchwartzPoisson
open MeasureTheory Filter LineDeriv
open scoped FourierTransform SchwartzMap Real RealInnerProductSpace
abbrev LogPlane := WithLp 2 (ℝ × ℝ)

theorem fourier_prod_eq_iterated (f : LogPlane → ℂ) (hf : Integrable f) (ξ η : ℝ) :
    𝓕 f (WithLp.toLp 2 (ξ, η)) =
      𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => f (WithLp.toLp 2 (x, y))) η) ξ := by
  let w : LogPlane := WithLp.toLp 2 (ξ, η)
  let G : LogPlane → ℂ := fun z => Real.fourierChar (-⟪z, w⟫) • f z
  have hG : Integrable G := (Real.fourierIntegral_convergent_iff w).mpr hf
  have hGp : Integrable (fun z : ℝ × ℝ => G (WithLp.toLp 2 z)) :=
    (WithLp.volume_preserving_toLp ℝ ℝ).integrable_comp_of_integrable hG
  calc
    𝓕 f (WithLp.toLp 2 (ξ, η)) = ∫ z : LogPlane, G z := rfl
    _ = ∫ z : ℝ × ℝ, G (WithLp.toLp 2 z) :=
      ((WithLp.volume_preserving_toLp ℝ ℝ).integral_comp
        (MeasurableEquiv.toLp 2 (ℝ × ℝ)).measurableEmbedding G).symm
    _ = ∫ x : ℝ, ∫ y : ℝ, G (WithLp.toLp 2 (x, y)) := integral_prod _ hGp
    _ = 𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => f (WithLp.toLp 2 (x, y))) η) ξ := by
      simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          simp only [G, w, WithLp.prod_inner_apply,
            neg_add, Real.fourierChar.map_add_eq_mul, Circle.smul_def, smul_eq_mul,
            Circle.coe_mul, mul_assoc]

def complexPoint (x y : ℝ) : ℂ := ⟨x, y⟩

theorem complexPoint_eq (x y : ℝ) : complexPoint x y = (x : ℂ) + Complex.I * (y : ℂ) := by
  apply Complex.ext <;> simp [complexPoint]

def planeComplexIso : LogPlane ≃ₗᵢ[ℝ] ℂ where
  toLinearEquiv := (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).trans
    Complex.equivRealProdCLM.toLinearEquiv.symm
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖complexPoint (WithLp.ofLp z).1 (WithLp.ofLp z).2‖ ^ 2 =
      ‖(WithLp.ofLp z).1‖ ^ 2 + ‖(WithLp.ofLp z).2‖ ^ 2
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, complexPoint, Real.norm_eq_abs,  sq]

@[simp] theorem planeComplexIso_apply (x y : ℝ) :
    planeComplexIso (WithLp.toLp 2 (x, y)) = complexPoint x y := rfl

theorem horizontal_isometry (η : ℝ) : Isometry (fun x : ℝ => complexPoint x η) := by
  apply Isometry.of_dist_eq
  intro x y
  have h : complexPoint x η - complexPoint y η = ((x - y : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [complexPoint]
  simp only [dist_eq_norm, h, Complex.norm_real]

theorem horizontal_temperate (η : ℝ) :
    (fun x : ℝ => complexPoint x η).HasTemperateGrowth := by
  have heq : (fun x : ℝ => complexPoint x η) =
      (fun x : ℝ => Complex.ofRealCLM x + Complex.I * (η : ℂ)) := by
    funext x
    exact complexPoint_eq x η
  rw [heq]
  fun_prop

def horizontalSlice (f : SchwartzMap ℂ ℂ) (η : ℝ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (horizontal_temperate η)
    (horizontal_isometry η).antilipschitzWith f

@[simp] theorem horizontalSlice_apply (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    horizontalSlice f η x = f (complexPoint x η) := rfl

def partialFourier (f : SchwartzMap ℂ ℂ) (η x : ℝ) : ℂ :=
  𝓕 (fun y : ℝ => f (complexPoint x y)) η

theorem partialFourier_eq_integral (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    partialFourier f η x =
      ∫ y : ℝ, Real.fourierChar (-inner ℝ y η) • f (complexPoint x y) := rfl

theorem partialFourier_eq_exp_integral (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    partialFourier f η x = ∫ y : ℝ,
      Complex.exp (((-2 * Real.pi * (y * η) : ℝ) : ℂ) * Complex.I) *
        f ((x : ℂ) + Complex.I * (y : ℂ)) := by
  have hin (y : ℝ) : inner ℝ y η = y * η := by simp [RCLike.inner_apply, mul_comm]
  simp only [partialFourier, Real.fourier_eq', hin, complexPoint_eq, smul_eq_mul]

def verticalMajorant (f : SchwartzMap ℂ ℂ) (y : ℝ) : ℝ :=
  ((SchwartzMap.seminorm ℝ 0 0) f + (SchwartzMap.seminorm ℝ 2 0) f) * (1 + y ^ 2)⁻¹

theorem verticalMajorant_integrable (f : SchwartzMap ℂ ℂ) : Integrable (verticalMajorant f) :=
  integrable_inv_one_add_sq.const_mul _

theorem norm_le_verticalMajorant (f : SchwartzMap ℂ ℂ) (x y : ℝ) :
    ‖f (complexPoint x y)‖ ≤ verticalMajorant f y := by
  have h0 := SchwartzMap.norm_le_seminorm ℝ f (complexPoint x y)
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ f 2 (complexPoint x y)
  have hy : y ^ 2 ≤ ‖complexPoint x y‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, complexPoint]
    nlinarith [sq_nonneg x]
  have hym := mul_le_mul_of_nonneg_right hy (norm_nonneg (f (complexPoint x y)))
  have hden : 0 < 1 + y ^ 2 := by positivity
  rw [verticalMajorant, ← div_eq_mul_inv]
  apply (le_div_iff₀ hden).mpr
  nlinarith

theorem partialFourier_continuous (f : SchwartzMap ℂ ℂ) (η : ℝ) :
    Continuous (partialFourier f η) := by
  change Continuous (fun x : ℝ => ∫ y : ℝ,
    Real.fourierChar (-inner ℝ y η) • f (complexPoint x y))
  apply continuous_of_dominated
    (bound := verticalMajorant f)
  · intro x
    have hline : Continuous (fun y : ℝ => complexPoint x y) :=
      Complex.equivRealProdCLM.symm.continuous.comp (continuous_const.prodMk continuous_id)
    exact ((by fun_prop : Continuous (fun y : ℝ => Real.fourierChar (-inner ℝ y η))).smul
      (f.continuous.comp hline)).aestronglyMeasurable
  · intro x
    exact Eventually.of_forall fun y => by
      simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul] using
        norm_le_verticalMajorant f x y
  · exact verticalMajorant_integrable f
  · exact Eventually.of_forall fun y => by
      have hf : Continuous (fun x : ℝ => f (complexPoint x y)) :=
        f.continuous.comp (horizontal_isometry y).continuous
      exact continuous_const.smul hf

theorem partialFourier_integrable (f : SchwartzMap ℂ ℂ) (η : ℝ) :
    Integrable (partialFourier f η) := by
  let G : ℂ → ℂ := fun z => Real.fourierChar (-inner ℝ z.im η) • f z
  have hG : Integrable G := f.integrable.norm.mono'
    (by fun_prop : Continuous G).aestronglyMeasurable
    (Eventually.of_forall fun z => by
      simp only [G, Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
      exact le_rfl)
  have hGp : Integrable (fun z : ℝ × ℝ => G (Complex.measurableEquivRealProd.symm z)) :=
    Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_of_integrable hG
  change Integrable (fun x : ℝ => ∫ y : ℝ,
    Real.fourierChar (-inner ℝ y η) • f (complexPoint x y))
  simpa only [G, Complex.measurableEquivRealProd_symm_apply, complexPoint]
    using hGp.integral_prod_left

theorem fourier_partialFourier (f : SchwartzMap ℂ ℂ) (ξ η : ℝ) :
    𝓕 (partialFourier f η) ξ = 𝓕 (f : ℂ → ℂ) (complexPoint ξ η) := by
  let fp : SchwartzMap LogPlane ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ planeComplexIso.toContinuousLinearEquiv f
  have hprod := fourier_prod_eq_iterated (fp : LogPlane → ℂ) fp.integrable ξ η
  have hcoe : (fp : LogPlane → ℂ) = (f : ℂ → ℂ) ∘ planeComplexIso := rfl
  rw [hcoe, Real.fourier_comp_linearIsometry] at hprod
  change 𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => f (complexPoint x y)) η) ξ = _
  simpa only [Function.comp_apply, planeComplexIso_apply] using hprod.symm

def partialFourierSchwartz (f : SchwartzMap ℂ ℂ) (η : ℝ) : SchwartzMap ℝ ℂ :=
  𝓕⁻ (horizontalSlice (𝓕 f) η)

theorem partialFourierSchwartz_apply (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    partialFourierSchwartz f η x = partialFourier f η x := by
  have heq : 𝓕 (partialFourier f η) =
      (horizontalSlice (𝓕 f) η : ℝ → ℂ) := by
    funext ξ
    rw [fourier_partialFourier, horizontalSlice_apply]
    exact (congrFun (SchwartzMap.fourier_coe f) (complexPoint ξ η)).symm
  have hi : Integrable (𝓕 (partialFourier f η)) := by
    rw [heq]
    exact (horizontalSlice (𝓕 f) η).integrable
  change (𝓕⁻ (horizontalSlice (𝓕 f) η)) x = _
  rw [congrFun (SchwartzMap.fourierInv_coe (horizontalSlice (𝓕 f) η)) x, ← heq]
  exact (partialFourier_integrable f η).fourierInv_fourier_eq hi
    (partialFourier_continuous f η).continuousAt

theorem partialFourierSchwartz_coe (f : SchwartzMap ℂ ℂ) (η : ℝ) :
    (partialFourierSchwartz f η : ℝ → ℂ) = partialFourier f η :=
  funext (partialFourierSchwartz_apply f η)

theorem fourier_partialFourierSchwartz (f : SchwartzMap ℂ ℂ) (ξ η : ℝ) :
    𝓕 (partialFourierSchwartz f η : ℝ → ℂ) ξ =
      𝓕 (f : ℂ → ℂ) ((ξ : ℂ) + Complex.I * (η : ℂ)) := by
  rw [partialFourierSchwartz_coe, fourier_partialFourier, complexPoint_eq]

theorem horizontal_hasFDerivAt (η x : ℝ) :
    HasFDerivAt (fun y : ℝ => complexPoint y η) Complex.ofRealCLM x := by
  have heq : (fun y : ℝ => complexPoint y η) =
      (fun y : ℝ => Complex.ofRealCLM y + Complex.I * (η : ℂ)) := by
    funext y
    exact complexPoint_eq y η
  rw [heq]
  exact Complex.ofRealCLM.hasFDerivAt.add_const _

theorem horizontalSlice_lineDerivOp (F : SchwartzMap ℂ ℂ) (η : ℝ) :
    ∂_{(1 : ℝ)} (horizontalSlice F η) = horizontalSlice (∂_{(1 : ℂ)} F) η := by
  apply SchwartzMap.ext
  intro x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, horizontalSlice_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hcomp := (F.hasFDerivAt (complexPoint x η)).comp x (horizontal_hasFDerivAt η x)
  change fderiv ℝ (fun y : ℝ => F (complexPoint y η)) x (1 : ℝ) = _
  change fderiv ℝ ((F : ℂ → ℂ) ∘ (fun y => complexPoint y η)) x (1 : ℝ) = _
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.ofReal_one]

theorem horizontalSlice_lineDerivOp_twice (F : SchwartzMap ℂ ℂ) (η : ℝ) :
    ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (horizontalSlice F η)) =
      horizontalSlice (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F)) η := by
  rw [horizontalSlice_lineDerivOp, horizontalSlice_lineDerivOp]

theorem summable_int_cauchy_weight :
    Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2)⁻¹) := by
  classical
  have hp : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  rw [← Finset.summable_compl_iff (s := ({0} : Finset ℤ))]
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _
    (hp.subtype (fun n : ℤ => n ∉ ({0} : Finset ℤ)))
  intro n
  have hn : n.val ≠ 0 := by simpa only [Finset.mem_singleton] using n.property
  have hnr : (n.val : ℝ) ≠ 0 := by exact_mod_cast hn
  have hsq : 0 < (n.val : ℝ) ^ 2 := sq_pos_of_ne_zero hnr
  change (1 + (n.val : ℝ) ^ 2)⁻¹ ≤ 1 / (n.val : ℝ) ^ 2
  simpa only [one_div] using
    one_div_le_one_div_of_le hsq (show (n.val : ℝ) ^ 2 ≤ 1 + (n.val : ℝ) ^ 2 by linarith)

theorem summable_int_cauchy_product :
    Summable (fun p : ℤ × ℤ =>
      (1 + (p.1 : ℝ) ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2)⁻¹) :=
  summable_int_cauchy_weight.mul_of_nonneg summable_int_cauchy_weight
    (fun _ => by positivity) (fun _ => by positivity)

theorem summable_norm_of_cauchy_product (F : ℤ × ℤ → ℂ) (C : ℝ)
    (hF : ∀ p, ‖F p‖ ≤ C *
      ((1 + (p.1 : ℝ) ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2)⁻¹)) :
    Summable (fun p => ‖F p‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF
    (summable_int_cauchy_product.mul_left C)

theorem summable_of_cauchy_product (F : ℤ × ℤ → ℂ) (C : ℝ)
    (hF : ∀ p, ‖F p‖ ≤ C *
      ((1 + (p.1 : ℝ) ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2)⁻¹)) : Summable F :=
  (summable_norm_of_cauchy_product F C hF).of_norm

def planeDecayConstant (F : SchwartzMap ℂ ℂ) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 F + SchwartzMap.seminorm ℝ 2 0 F +
    SchwartzMap.seminorm ℝ 4 0 F

theorem planeDecayConstant_nonneg (F : SchwartzMap ℂ ℂ) : 0 ≤ planeDecayConstant F := by
  unfold planeDecayConstant
  positivity

theorem plane_schwartz_product_decay (F : SchwartzMap ℂ ℂ) (ξ η : ℝ) :
    ((1 + ξ ^ 2) * (1 + η ^ 2)) * ‖F (complexPoint ξ η)‖ ≤
      planeDecayConstant F := by
  let z := complexPoint ξ η
  have hz : ‖z‖ ^ 2 = ξ ^ 2 + η ^ 2 := by
    rw [Complex.sq_norm]
    simp [z, Complex.normSq_apply, complexPoint, sq]
  have h0 := SchwartzMap.norm_le_seminorm ℝ F z
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 2 z
  have h4 := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 4 z
  have hz4 : ‖z‖ ^ 4 = (ξ ^ 2 + η ^ 2) ^ 2 := by
    calc
      ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 := by ring
      _ = (ξ ^ 2 + η ^ 2) ^ 2 := congrArg (fun t : ℝ => t ^ 2) hz
  have hxy : ξ ^ 2 * η ^ 2 ≤ ‖z‖ ^ 4 := by
    rw [hz4]
    nlinarith [sq_nonneg (ξ ^ 2), sq_nonneg (η ^ 2),
      mul_nonneg (sq_nonneg ξ) (sq_nonneg η)]
  have hm := mul_le_mul_of_nonneg_right hxy (norm_nonneg (F z))
  rw [hz] at h2
  change ((1 + ξ ^ 2) * (1 + η ^ 2)) * ‖F z‖ ≤ _
  unfold planeDecayConstant
  nlinarith

theorem norm_horizontalSlice_le (F : SchwartzMap ℂ ℂ) (η ξ : ℝ) :
    ‖horizontalSlice F η ξ‖ ≤
      (planeDecayConstant F / (1 + η ^ 2)) * (1 + ξ ^ 2)⁻¹ := by
  rw [horizontalSlice_apply, ← div_eq_mul_inv, div_div]
  apply (le_div_iff₀ (by positivity : 0 < (1 + η ^ 2) * (1 + ξ ^ 2))).mpr
  nlinarith [plane_schwartz_product_decay F ξ η]

theorem norm_inverse_horizontalSlice_le (F : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ‖(𝓕⁻ (horizontalSlice F η)) x‖ ≤
      (planeDecayConstant F / (1 + η ^ 2)) * Real.pi := by
  rw [congrFun (SchwartzMap.fourierInv_coe (horizontalSlice F η)) x,
    Real.fourierInv_eq]
  have hb : Integrable (fun ξ : ℝ =>
      (planeDecayConstant F / (1 + η ^ 2)) * (1 + ξ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have h := norm_integral_le_of_norm_le
    (f := fun ξ : ℝ => Real.fourierChar (inner ℝ ξ x) • horizontalSlice F η ξ) hb (Eventually.of_forall fun ξ => by
    simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul] using
      norm_horizontalSlice_le F η ξ)
  simpa only [integral_const_mul, integral_univ_inv_one_add_sq] using h

theorem norm_inverse_lineDeriv (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖(𝓕⁻ (∂_{(1 : ℝ)} g)) x‖ =
      (2 * Real.pi) * |x| * ‖(𝓕⁻ g) x‖ := by
  have ht : (fun u : ℝ => inner ℝ u (1 : ℝ)).HasTemperateGrowth := by fun_prop
  have hc : ‖(-(2 * Real.pi * Complex.I) : ℂ)‖ = 2 * Real.pi := by
    simp [ Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [SchwartzMap.fourierInv_lineDerivOp_eq]
  simp only [_root_.smul_apply, SchwartzMap.smulLeftCLM_apply_apply ht,
    norm_smul, hc]
  simp [RCLike.inner_apply, Real.norm_eq_abs, mul_assoc]

theorem sq_mul_norm_inverse_le_second (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    x ^ 2 * ‖(𝓕⁻ g) x‖ ≤ ‖(𝓕⁻ (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} g))) x‖ := by
  rw [norm_inverse_lineDeriv, norm_inverse_lineDeriv]
  have hp : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  calc
    x ^ 2 * ‖(𝓕⁻ g) x‖ ≤ ((2 * Real.pi) ^ 2 * x ^ 2) * ‖(𝓕⁻ g) x‖ :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (sq_nonneg x) hp) (norm_nonneg _)
    _ = ((2 * Real.pi) ^ 2 * |x| ^ 2) * ‖(𝓕⁻ g) x‖ := by rw [sq_abs]
    _ = _ := by ring

theorem inverse_horizontalSlice_product_decay (F : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ((1 + x ^ 2) * (1 + η ^ 2)) * ‖(𝓕⁻ (horizontalSlice F η)) x‖ ≤
      Real.pi * (planeDecayConstant F +
        planeDecayConstant (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F))) := by
  have h0 := norm_inverse_horizontalSlice_le F η x
  have h2a := sq_mul_norm_inverse_le_second (horizontalSlice F η) x
  rw [horizontalSlice_lineDerivOp_twice] at h2a
  have h2 := h2a.trans
    (norm_inverse_horizontalSlice_le (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F)) η x)
  have hden : 0 < 1 + η ^ 2 := by positivity
  have h0' : ‖(𝓕⁻ (horizontalSlice F η)) x‖ * (1 + η ^ 2) ≤
      planeDecayConstant F * Real.pi := by
    apply (le_div_iff₀ hden).mp
    simpa only [div_mul_eq_mul_div] using h0
  have h2' : (x ^ 2 * ‖(𝓕⁻ (horizontalSlice F η)) x‖) * (1 + η ^ 2) ≤
      planeDecayConstant (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F)) * Real.pi := by
    apply (le_div_iff₀ hden).mp
    simpa only [div_mul_eq_mul_div] using h2
  nlinarith

def partialFourierDecayConstant (f : SchwartzMap ℂ ℂ) : ℝ :=
  Real.pi * (planeDecayConstant (𝓕 f) +
    planeDecayConstant (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} (𝓕 f))))

theorem partialFourierDecayConstant_nonneg (f : SchwartzMap ℂ ℂ) :
    0 ≤ partialFourierDecayConstant f :=
  mul_nonneg Real.pi_pos.le
    (add_nonneg (planeDecayConstant_nonneg _) (planeDecayConstant_nonneg _))

theorem partialFourier_product_decay (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ((1 + x ^ 2) * (1 + η ^ 2)) * ‖partialFourier f η x‖ ≤
      partialFourierDecayConstant f := by
  rw [← partialFourierSchwartz_apply]
  exact inverse_horizontalSlice_product_decay (𝓕 f) η x

theorem norm_partialFourier_le (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ‖partialFourier f η x‖ ≤
      partialFourierDecayConstant f * ((1 + x ^ 2)⁻¹ * (1 + η ^ 2)⁻¹) := by
  rw [← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < (1 + x ^ 2) * (1 + η ^ 2))).mpr
  nlinarith [partialFourier_product_decay f η x]

theorem partialFourier_gaussian_summable_norm (f : SchwartzMap ℂ ℂ) :
    Summable (fun p : ℤ × ℤ =>
      ‖partialFourier f (p.2 : ℝ) (p.1 : ℝ)‖) := by
  apply summable_norm_of_cauchy_product
    (fun p : ℤ × ℤ => partialFourier f (p.2 : ℝ) (p.1 : ℝ))
    (partialFourierDecayConstant f)
  intro p
  exact norm_partialFourier_le f (p.2 : ℝ) (p.1 : ℝ)

theorem partialFourier_gaussian_summable (f : SchwartzMap ℂ ℂ) :
    Summable (fun p : ℤ × ℤ => partialFourier f (p.2 : ℝ) (p.1 : ℝ)) :=
  (partialFourier_gaussian_summable_norm f).of_norm

theorem plane_lattice_summable_norm (f : 𝓢(ℂ, ℂ)) :
    Summable (fun p : ℤ × ℤ => ‖f (complexPoint (p.1 : ℝ) (p.2 : ℝ))‖) := by
  apply summable_norm_of_cauchy_product _ (planeDecayConstant f)
  intro p
  rw [← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity :
    0 < (1 + (p.1 : ℝ) ^ 2) * (1 + (p.2 : ℝ) ^ 2))).mpr
  nlinarith [plane_schwartz_product_decay f (p.1 : ℝ) (p.2 : ℝ)]

theorem plane_lattice_summable (f : 𝓢(ℂ, ℂ)) :
    Summable (fun p : ℤ × ℤ => f (complexPoint (p.1 : ℝ) (p.2 : ℝ))) :=
  (plane_lattice_summable_norm f).of_norm

theorem vertical_isometry (x : ℝ) : Isometry (fun y : ℝ => complexPoint x y) := by
  apply Isometry.of_dist_eq
  intro y z
  have h : complexPoint x y - complexPoint x z =
      Complex.I * ((y - z : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [complexPoint]
  simp only [dist_eq_norm, h, norm_mul, Complex.norm_I, one_mul, Complex.norm_real]

theorem vertical_temperate (x : ℝ) :
    (fun y : ℝ => complexPoint x y).HasTemperateGrowth := by
  have heq : (fun y : ℝ => complexPoint x y) =
      (fun y : ℝ => (x : ℂ) + Complex.I * Complex.ofRealCLM y) := by
    funext y
    exact complexPoint_eq x y
  rw [heq]
  fun_prop

def verticalSlice (f : 𝓢(ℂ, ℂ)) (x : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (vertical_temperate x)
    (vertical_isometry x).antilipschitzWith f

@[simp] theorem verticalSlice_apply (f : 𝓢(ℂ, ℂ)) (x y : ℝ) :
    verticalSlice f x y = f (complexPoint x y) := rfl

theorem schwartz_poisson_zero (g : 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, g (n : ℝ)) = ∑' n : ℤ, 𝓕 (g : ℝ → ℂ) (n : ℝ) := by
  simpa [fourier_eval_zero, SchwartzMap.fourier_coe] using g.tsum_eq_tsum_fourier 0

theorem vertical_poisson (f : 𝓢(ℂ, ℂ)) (x : ℝ) :
    (∑' n : ℤ, f (complexPoint x (n : ℝ))) =
      ∑' n : ℤ, partialFourier f (n : ℝ) x := by
  exact schwartz_poisson_zero (verticalSlice f x)

private theorem horizontal_poisson (f : 𝓢(ℂ, ℂ)) (n : ℤ) :
    (∑' m : ℤ, partialFourier f (n : ℝ) (m : ℝ)) =
      ∑' k : ℤ, (𝓕 f) (complexPoint (k : ℝ) (n : ℝ)) := by
  have h := schwartz_poisson_zero (partialFourierSchwartz f n)
  simpa only [partialFourierSchwartz_apply, partialFourierSchwartz_coe,
    fourier_partialFourier, SchwartzMap.fourier_coe] using h

private theorem iterated_poisson_pair_sum
    (f g h : ℤ → ℤ → ℂ)
    (hf : Summable (Function.uncurry f))
    (hg : Summable (Function.uncurry g))
    (hh : Summable (Function.uncurry h))
    (hvertical : ∀ m, (∑' n, f m n) = ∑' n, h m n)
    (hhorizontal : ∀ n, (∑' m, h m n) = ∑' m, g m n) :
    (∑' p : ℤ × ℤ, f p.1 p.2) = ∑' p : ℤ × ℤ, g p.1 p.2 := by
  calc
    (∑' p : ℤ × ℤ, f p.1 p.2) = ∑' m, ∑' n, f m n := hf.tsum_prod
    _ = ∑' m, ∑' n, h m n := tsum_congr hvertical
    _ = ∑' n, ∑' m, h m n := hh.tsum_comm.symm
    _ = ∑' n, ∑' m, g m n := tsum_congr hhorizontal
    _ = ∑' m, ∑' n, g m n := hg.tsum_comm
    _ = ∑' p : ℤ × ℤ, g p.1 p.2 := hg.tsum_prod.symm

theorem integer_pair_poisson (f : 𝓢(ℂ, ℂ)) :
    (∑' p : ℤ × ℤ, f (complexPoint (p.1 : ℝ) (p.2 : ℝ))) =
      ∑' p : ℤ × ℤ, (𝓕 f) (complexPoint (p.1 : ℝ) (p.2 : ℝ)) := by
  exact iterated_poisson_pair_sum
    (fun m n => f (complexPoint (m : ℝ) (n : ℝ)))
    (fun m n : ℤ => (𝓕 f : 𝓢(ℂ, ℂ)) (complexPoint (m : ℝ) (n : ℝ)))
    (fun m n => partialFourier f (n : ℝ) (m : ℝ))
    (plane_lattice_summable f) (plane_lattice_summable (𝓕 f))
    (partialFourier_gaussian_summable f)
    (fun m => vertical_poisson f m) (horizontal_poisson f)

end EisensteinSchwartzPoisson

end

end OAI
end OAIOriginalModule0079

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.FiniteEulerFactors
Source SHA256: 54d432aa1884ffb6f3652d9c32a4e7d893d742e941842b3192f8801e4f7d9d14
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0080



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
namespace FiniteSFactor

private theorem fiber_card_natCard (n : ℕ) :
    (fiber n).card = Nat.card {I : Ideal O // Ideal.absNorm I = n} := by
  change (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset.card =
    Set.ncard {I : Ideal O | Ideal.absNorm I = n}
  exact (Set.ncard_eq_toFinset_card _ _).symm

private theorem fiber_card_le_count (n : ℕ) :
    (fiber n).card ≤ Nat.card {I : Ideal O // Ideal.absNorm I ≤ n} := by
  let f : {I : Ideal O // Ideal.absNorm I = n} →
      {I : Ideal O // Ideal.absNorm I ≤ n} :=
    fun I => ⟨I.1, I.2.le⟩
  have hinj : Function.Injective f := by
    intro I J h
    have hval : I.1 = J.1 :=
      congrArg (fun x : {I : Ideal O // Ideal.absNorm I ≤ n} => x.1) h
    exact Subtype.ext hval
  have hfin : Finite {I : Ideal O // Ideal.absNorm I ≤ n} :=
    Ideal.finite_setOfPred_absNorm_le n
  simpa only [fiber_card_natCard] using Nat.card_le_card_of_injective f hinj

private theorem count_isBigO :
    (fun n : ℕ =>
      (Nat.card {I : Ideal O // Ideal.absNorm I ≤ n} : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)) := by
  have hlim :=
    (NumberField.Ideal.tendsto_norm_le_div_atTop (CyclotomicField 3 ℚ)).comp
      tendsto_natCast_atTop_atTop
  have hlim' : Filter.Tendsto
      (fun n : ℕ =>
        (Nat.card {I : Ideal O // Ideal.absNorm I ≤ n} : ℝ) / (n : ℝ))
      atTop (nhds ((2 ^ NumberField.InfinitePlace.nrRealPlaces (CyclotomicField 3 ℚ) *
        (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces (CyclotomicField 3 ℚ) *
        NumberField.Units.regulator (CyclotomicField 3 ℚ) *
        (NumberField.classNumber (CyclotomicField 3 ℚ) : ℝ)) /
        ((NumberField.Units.torsionOrder (CyclotomicField 3 ℚ) : ℝ) *
          Real.sqrt |(NumberField.discr (CyclotomicField 3 ℚ) : ℝ)|))) := by
    simpa [Function.comp_def] using hlim
  have hzero : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) = 0 →
        (Nat.card {I : Ideal O // Ideal.absNorm I ≤ n} : ℝ) = 0 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn hz
    have hn0 : n = 0 := by exact_mod_cast hz
    exact (Nat.ne_of_gt hn hn0).elim
  exact Asymptotics.isBigO_of_div_tendsto_nhds hzero _ hlim'

private theorem fiber_card_eventually_le_linear :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ((fiber n).card : ℝ) ≤ C * n := by
  obtain ⟨C, hC⟩ := count_isBigO.bound
  refine ⟨C, ?_⟩
  filter_upwards [hC] with n hn
  calc
    ((fiber n).card : ℝ) ≤
        (Nat.card {I : Ideal O // Ideal.absNorm I ≤ n} : ℝ) := by
          exact_mod_cast fiber_card_le_count n
    _ = ‖(Nat.card {I : Ideal O // Ideal.absNorm I ≤ n} : ℝ)‖ := by simp
    _ ≤ C * ‖(n : ℝ)‖ := hn
    _ = C * n := by simp

private theorem outsideCoeff_norm_le_card (S : Finset (Ideal O))
    (w : Ideal O → ℂ) (hw : ∀ I, ‖w I‖ ≤ 1) (n : ℕ) :
    ‖outsideCoeff S w n‖ ≤ ((fiber n).card : ℝ) := by
  classical
  have hweight (I : Ideal O) : ‖outsideWeight S w I‖ ≤ 1 := by
    by_cases hgood : ∀ P ∈ S, ¬P ∣ I
    · change ‖if ∀ P ∈ S, ¬P ∣ I then w I else 0‖ ≤ 1
      rw [ite_eq_left hgood]
      exact hw I
    · change ‖if ∀ P ∈ S, ¬P ∣ I then w I else 0‖ ≤ 1
      rw [ite_eq_right hgood]
      simp
  unfold outsideCoeff
  calc
    ‖∑ I ∈ fiber n, outsideWeight S w I‖ ≤
        ∑ I ∈ fiber n, ‖outsideWeight S w I‖ := norm_sum_le _ _
    _ ≤ ∑ _I ∈ fiber n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro I hI
      exact hweight I
    _ = ((fiber n).card : ℝ) := by simp

private theorem baseChangeWeight_norm_le_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (I : Ideal O) :
    ‖ShortDraftHeckeBridge.baseChangeWeight χ I‖ ≤ 1 := by
  have hμ : ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖ ≤ 1 := by
    by_cases hsq : Squarefree I
    · simp [hsq.moebius_eq]
    · simp [UniqueFactorizationMonoid.moebius_of_not_squarefree hsq]
  have hχ : ‖χ (Ideal.absNorm I)‖ ≤ 1 := χ.norm_le_one _
  rw [ShortDraftHeckeBridge.baseChangeWeight, norm_mul]
  calc
    ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖ * ‖χ (Ideal.absNorm I)‖ ≤
        1 * ‖χ (Ideal.absNorm I)‖ :=
      mul_le_mul_of_nonneg_right hμ (norm_nonneg _)
    _ ≤ 1 := by simpa using hχ

private theorem outsideCoeff_baseChange_isBigO_linear {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (S : Finset (Ideal O)) :
    (fun n : ℕ => outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ) n)
      =O[atTop] (fun n : ℕ => (n : ℝ)) := by
  obtain ⟨C, hC⟩ := fiber_card_eventually_le_linear
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hC] with n hn
  calc
    ‖outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ) n‖ ≤
        ((fiber n).card : ℝ) := outsideCoeff_norm_le_card S
          (ShortDraftHeckeBridge.baseChangeWeight χ)
          (baseChangeWeight_norm_le_one χ) n
    _ ≤ C * (n : ℝ) := hn
    _ = C * ‖(n : ℝ)‖ := by simp

theorem outsideCoeff_LSeriesSummable_baseChange {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (S : Finset (Ideal O))
    (s : ℂ) (hs : 2 < s.re) :
    LSeriesSummable (outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ)) s := by
  have hO :
      (fun n : ℕ => outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ) n)
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ ((2 : ℝ) - 1)) := by
    simpa only [show ((2 : ℝ) - 1) = 1 by norm_num, Real.rpow_one] using
      outsideCoeff_baseChange_isBigO_linear χ S
  exact LSeriesSummable_of_isBigO_rpow hs hO

theorem outsideCoeff_exp_summable_baseChange {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (S : Finset (Ideal O))
    (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℕ => outsideCoeff S
      (ShortDraftHeckeBridge.baseChangeWeight χ) n * Real.exp (-(n : ℝ) * t)) := by
  obtain ⟨C, hC⟩ := fiber_card_eventually_le_linear
  have hexp : Summable (fun n : ℕ => (n : ℝ) * Real.exp (-(n : ℝ) * t)) := by
    convert Real.summable_pow_mul_exp_neg_nat_mul 1 ht using 1
    ext n
    simp only [pow_one]
    congr 1
    ring_nf
  apply (hexp.mul_left C).of_norm_bounded_eventually_nat
  filter_upwards [hC] with n hn
  have hcoeff := outsideCoeff_norm_le_card S
    (ShortDraftHeckeBridge.baseChangeWeight χ)
    (baseChangeWeight_norm_le_one χ) n
  have hlin : ‖outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ) n‖ ≤
      C * (n : ℝ) := hcoeff.trans hn
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-(n : ℝ) * t)).le)

theorem outsideExpSum_restore_baseChange {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (hS : ∀ Q ∈ S, Prime Q)
    (P : Ideal O) (hP : Prime P) (hPnot : P ∉ S)
    (t : ℝ) (ht : 0 < t) :
    outsideExpSum S (ShortDraftHeckeBridge.baseChangeWeight χ) t =
      outsideExpSum (insert P S) (ShortDraftHeckeBridge.baseChangeWeight χ) t +
        ShortDraftHeckeBridge.baseChangeWeight χ P *
          outsideExpSum (insert P S) (ShortDraftHeckeBridge.baseChangeWeight χ)
            ((Ideal.absNorm P : ℝ) * t) := by
  have hN : (0 : ℝ) < (Ideal.absNorm P : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.1)
  exact outsideExpSum_restore_insert_prime S hS P hP hPnot
    (ShortDraftHeckeBridge.baseChangeWeight χ)
    (ShortDraftHeckeBridge.baseChangeWeight_zero_of_not_squarefree χ)
    (ShortDraftHeckeBridge.baseChangeWeight_mul_of_isRelPrime χ)
    t
    (outsideCoeff_exp_summable_baseChange χ (insert P S) t ht)
    (outsideCoeff_exp_summable_baseChange χ (insert P S)
      ((Ideal.absNorm P : ℝ) * t) (mul_pos hN ht))

theorem outsideExpSum_empty_eq_normFiberExpSum {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    outsideExpSum ∅ (ShortDraftHeckeBridge.baseChangeWeight χ) t =
      ShortDraftHeckeBridge.normFiberExpSum
        (ShortDraftHeckeBridge.baseChangeWeight χ) t := by
  unfold outsideExpSum ShortDraftHeckeBridge.normFiberExpSum
  congr 1

theorem normFiberExpSum_restore_two_primes {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (P Q : Ideal O) (hP : Prime P) (hQ : Prime Q) (hPQ : P ≠ Q)
    (t : ℝ) (ht : 0 < t) :
    ShortDraftHeckeBridge.normFiberExpSum
      (ShortDraftHeckeBridge.baseChangeWeight χ) t =
        outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ) t +
        ShortDraftHeckeBridge.baseChangeWeight χ Q *
          outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ)
            ((Ideal.absNorm Q : ℝ) * t) +
        ShortDraftHeckeBridge.baseChangeWeight χ P *
          outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ)
            ((Ideal.absNorm P : ℝ) * t) +
        ShortDraftHeckeBridge.baseChangeWeight χ P *
          ShortDraftHeckeBridge.baseChangeWeight χ Q *
          outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ)
            ((Ideal.absNorm Q : ℝ) * ((Ideal.absNorm P : ℝ) * t)) := by
  have hPnot : P ∉ (∅ : Finset (Ideal O)) := by simp
  have hQnot : Q ∉ ({P} : Finset (Ideal O)) := by simpa using hPQ.symm
  have hSP : ∀ R ∈ ({P} : Finset (Ideal O)), Prime R := by
    intro R hR
    simp only [Finset.mem_singleton] at hR
    subst R
    exact hP
  have hNP : (0 : ℝ) < (Ideal.absNorm P : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.1)
  have h0 := outsideExpSum_restore_baseChange χ ∅ (by simp) P hP hPnot t ht
  have h1 := outsideExpSum_restore_baseChange χ {P} hSP Q hQ hQnot t ht
  have h2 := outsideExpSum_restore_baseChange χ {P} hSP Q hQ hQnot
    ((Ideal.absNorm P : ℝ) * t) (mul_pos hNP ht)
  rw [outsideExpSum_empty_eq_normFiberExpSum] at h0
  simp only [Finset.insert_empty] at h0
  rw [h1, h2] at h0
  calc
    ShortDraftHeckeBridge.normFiberExpSum
        (ShortDraftHeckeBridge.baseChangeWeight χ) t =
      outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ) t +
      ShortDraftHeckeBridge.baseChangeWeight χ Q *
        outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ)
          ((Ideal.absNorm Q : ℝ) * t) +
      ShortDraftHeckeBridge.baseChangeWeight χ P *
        (outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ)
          ((Ideal.absNorm P : ℝ) * t) +
        ShortDraftHeckeBridge.baseChangeWeight χ Q *
          outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ)
            ((Ideal.absNorm Q : ℝ) * ((Ideal.absNorm P : ℝ) * t))) := h0
    _ = _ := by ring

private noncomputable def dirichletKernel (s : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else (n : ℂ) ^ (-s)

private theorem term_eq_mul_kernel (a : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    LSeries.term a s n = a n * dirichletKernel s n := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term, dirichletKernel]
  · simp [LSeries.term, dirichletKernel, hn, div_eq_mul_inv, Complex.cpow_neg]

private theorem kernel_shift {N : ℕ} (hN : 0 < N) (s : ℂ) (m : ℕ) :
    dirichletKernel s (N * m) =
      (N : ℂ) ^ (-s) * dirichletKernel s m := by
  by_cases hm : m = 0
  · subst m
    simp [dirichletKernel]
  · have hNm : N * m ≠ 0 := mul_ne_zero hN.ne' hm
    simp only [dirichletKernel, ite_eq_right hNm, ite_eq_right hm]
    simpa only [Nat.cast_mul] using Complex.natCast_mul_natCast_cpow N m (-s)

private theorem tsum_mul_kernel_eq_LSeries (a : ℕ → ℂ) (s : ℂ) :
    (∑' n : ℕ, a n * dirichletKernel s n) = LSeries a s := by
  unfold LSeries
  apply tsum_congr
  intro n
  exact (term_eq_mul_kernel a s n).symm

theorem outsideLSeries_restore_baseChange {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (hS : ∀ Q ∈ S, Prime Q)
    (P : Ideal O) (hP : Prime P) (hPnot : P ∉ S)
    (s : ℂ) (hs : 2 < s.re) :
    LSeries (outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ)) s =
      (1 + ShortDraftHeckeBridge.baseChangeWeight χ P *
        (Ideal.absNorm P : ℂ) ^ (-s)) *
        LSeries (outsideCoeff (insert P S)
          (ShortDraftHeckeBridge.baseChangeWeight χ)) s := by
  let N : ℕ := Ideal.absNorm P
  let a : ℕ → ℂ := outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ)
  let b : ℕ → ℂ := outsideCoeff (insert P S) (ShortDraftHeckeBridge.baseChangeWeight χ)
  let c : ℂ := ShortDraftHeckeBridge.baseChangeWeight χ P
  have hN : 0 < N :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.1)
  have hcoeff (n : ℕ) :
      a n = b n + if N ∣ n then c * b (n / N) else 0 :=
    restore_insert_prime S hS P hP hPnot
      (ShortDraftHeckeBridge.baseChangeWeight χ)
      (ShortDraftHeckeBridge.baseChangeWeight_zero_of_not_squarefree χ)
      (ShortDraftHeckeBridge.baseChangeWeight_mul_of_isRelPrime χ) n
  have hbsum : LSeriesSummable b s :=
    outsideCoeff_LSeriesSummable_baseChange χ (insert P S) s hs
  change Summable (LSeries.term b s) at hbsum
  have hb : Summable (fun n : ℕ => b n * dirichletKernel s n) := by
    simpa only [← term_eq_mul_kernel b s] using hbsum
  have hshiftPoint (m : ℕ) :
      b m * dirichletKernel s (N * m) =
        (N : ℂ) ^ (-s) * LSeries.term b s m := by
    rw [kernel_shift hN s m, term_eq_mul_kernel]
    ring
  have hshift : Summable (fun m : ℕ => b m * dirichletKernel s (N * m)) := by
    simpa only [hshiftPoint] using hbsum.mul_left ((N : ℂ) ^ (-s))
  have hgeneric := FiniteEulerRestoration.tsum_restore_one_prime hN c a b
    (dirichletKernel s) hcoeff hb hshift
  rw [tsum_mul_kernel_eq_LSeries a s, tsum_mul_kernel_eq_LSeries b s] at hgeneric
  have hshiftSum :
      (∑' m : ℕ, b m * dirichletKernel s (N * m)) =
        (N : ℂ) ^ (-s) * LSeries b s := by
    calc
      (∑' m : ℕ, b m * dirichletKernel s (N * m)) =
          ∑' m : ℕ, (N : ℂ) ^ (-s) * LSeries.term b s m := by
            apply tsum_congr
            exact hshiftPoint
      _ = (N : ℂ) ^ (-s) * LSeries b s := by
            rw [tsum_mul_left]
            rfl
  rw [hshiftSum] at hgeneric
  change LSeries a s = (1 + c * (N : ℂ) ^ (-s)) * LSeries b s
  calc
    LSeries a s = LSeries b s + c * ((N : ℂ) ^ (-s) * LSeries b s) := hgeneric
    _ = (1 + c * (N : ℂ) ^ (-s)) * LSeries b s := by ring

theorem outsideLSeries_finiteEuler_baseChange {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P)
    (s : ℂ) (hs : 2 < s.re) :
    LSeries (outsideCoeff ∅ (ShortDraftHeckeBridge.baseChangeWeight χ)) s =
      (∏ P ∈ S, (1 + ShortDraftHeckeBridge.baseChangeWeight χ P *
        (Ideal.absNorm P : ℂ) ^ (-s))) *
      LSeries (outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ)) s := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert P S hPnot ih =>
      have hSP : ∀ Q ∈ S, Prime Q := by
        intro Q hQ
        exact hS Q (Finset.mem_insert_of_mem hQ)
      have hPP : Prime P := hS P (Finset.mem_insert_self P S)
      have hrest := outsideLSeries_restore_baseChange χ S hSP P hPP hPnot s hs
      calc
        LSeries (outsideCoeff ∅ (ShortDraftHeckeBridge.baseChangeWeight χ)) s =
            (∏ Q ∈ S, (1 + ShortDraftHeckeBridge.baseChangeWeight χ Q *
              (Ideal.absNorm Q : ℂ) ^ (-s))) *
            LSeries (outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ)) s :=
          ih hSP
        _ = (∏ Q ∈ S, (1 + ShortDraftHeckeBridge.baseChangeWeight χ Q *
              (Ideal.absNorm Q : ℂ) ^ (-s))) *
            ((1 + ShortDraftHeckeBridge.baseChangeWeight χ P *
              (Ideal.absNorm P : ℂ) ^ (-s)) *
              LSeries (outsideCoeff (insert P S)
                (ShortDraftHeckeBridge.baseChangeWeight χ)) s) := by rw [hrest]
        _ = (∏ Q ∈ insert P S, (1 + ShortDraftHeckeBridge.baseChangeWeight χ Q *
              (Ideal.absNorm Q : ℂ) ^ (-s))) *
            LSeries (outsideCoeff (insert P S)
              (ShortDraftHeckeBridge.baseChangeWeight χ)) s := by
          rw [Finset.prod_insert hPnot]
          ring

theorem outsideCoeff_empty_eq_normFiberCoeff (w : Ideal O → ℂ) (n : ℕ) :
    outsideCoeff ∅ w n = ShortDraftHeckeBridge.normFiberCoeff w n := by
  simp [outsideCoeff, outsideWeight, fiber, ShortDraftHeckeBridge.normFiberCoeff]

theorem normFiberLSeries_finiteEuler_baseChange {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (s : ℂ) (hs : 2 < s.re) :
    LSeries (ShortDraftHeckeBridge.normFiberCoeff
      (ShortDraftHeckeBridge.baseChangeWeight χ)) s =
      (∏ P ∈ S, (1 - χ (Ideal.absNorm P) *
        (Ideal.absNorm P : ℂ) ^ (-s))) *
      LSeries (outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ)) s := by
  have h := outsideLSeries_finiteEuler_baseChange χ S hS s hs
  have hfun : outsideCoeff ∅ (ShortDraftHeckeBridge.baseChangeWeight χ) =
      ShortDraftHeckeBridge.normFiberCoeff
        (ShortDraftHeckeBridge.baseChangeWeight χ) := by
    funext n
    exact outsideCoeff_empty_eq_normFiberCoeff _ n
  rw [hfun] at h
  have hprod :
      (∏ P ∈ S, (1 + ShortDraftHeckeBridge.baseChangeWeight χ P *
        (Ideal.absNorm P : ℂ) ^ (-s))) =
      (∏ P ∈ S, (1 - χ (Ideal.absNorm P) *
        (Ideal.absNorm P : ℂ) ^ (-s))) := by
    apply Finset.prod_congr rfl
    intro P hPS
    rw [ShortDraftHeckeBridge.baseChangeWeight_prime χ P (hS P hPS)]
    ring
  rw [hprod] at h
  exact h

end FiniteSFactor

open Filter

namespace CompactScaleBridge

open ConcretePrimeRowBridge ShortDraftHeckeBridge

abbrev O := ConcretePrimeRowBridge.O

theorem idealsUpTo_card_le (N : ℕ) :
    (idealsUpTo N).card ≤ 64 * (N + 1) := by
  classical
  have himage : (columnsUpTo N).card = (idealsUpTo N).card := by
    unfold columnsUpTo
    exact Finset.card_image_of_injective _ idealGenerator_injective
  rw [← himage]
  apply ShortDraftLatticeCount.actual_eisenstein_count
  intro x hx
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hx
  have hnorm : Ideal.absNorm I ≤ N := (mem_idealsUpTo.mp hI).2
  have hqNat : ShortDraftLatticeCount.qNat (idealGenerator I) ≤ N := by
    rw [ActualEisensteinCubic.qNat_eq_absNorm_span, span_idealGenerator]
    exact hnorm
  have hnonneg := ShortDraftLatticeCount.qO_nonneg (idealGenerator I)
  have hcast : ((ShortDraftLatticeCount.q
      (ActualEisensteinCoordinates.coords (idealGenerator I))).toNat : ℤ) =
      ShortDraftLatticeCount.q
        (ActualEisensteinCoordinates.coords (idealGenerator I)) :=
    Int.toNat_of_nonneg hnonneg
  change (ShortDraftLatticeCount.q
    (ActualEisensteinCoordinates.coords (idealGenerator I))).toNat ≤ N at hqNat
  have hqInt :
      ((ShortDraftLatticeCount.q
        (ActualEisensteinCoordinates.coords (idealGenerator I))).toNat : ℤ) ≤ N := by
    exact_mod_cast hqNat
  simpa only [hcast] using hqInt

theorem outsideIdealsUpTo_card_le (S : Finset (Ideal O)) (N : ℕ) :
    (outsideIdealsUpTo S N).card ≤ 64 * (N + 1) := by
  classical
  calc
    (outsideIdealsUpTo S N).card ≤ (idealsUpTo N).card := by
      apply Finset.card_le_card
      intro I hI
      exact (Finset.mem_filter.mp hI).1
    _ ≤ _ := idealsUpTo_card_le N

theorem integer_fixed_test_identity
    (S : Finset (Ideal O)) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℝ → ℂ) (m : ℕ) (hm : 0 < m) :
    (∑ I ∈ outsideIdealsUpTo S (2 * m),
      baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ))) =
    ∑ n ∈ Finset.Icc 1 (2 * m),
      FiniteSFactor.outsideCoeff S (baseChangeWeight χ) n *
        (fun y : ℝ => W (2 * y)) ((n : ℝ) / (2 * m : ℕ)) := by
  convert outsideIdealSum_eq_outsideCoeff_sum S (2 * m)
    (baseChangeWeight χ) (fun n => W ((n : ℝ) / (m : ℝ))) using 1
  simp only
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  push_cast
  field_simp

theorem real_to_integer_compact_bound
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (W : ℝ → ℂ)
    (LipC D : ℝ) (m : ℕ)
    (hL : 0 ≤ LipC) (hLip : ∀ x y : ℝ, ‖W x - W y‖ ≤ LipC * |x - y|)
    (hD : 1 ≤ D) (hmLower : D ≤ (m : ℝ))
    (hmUpper : (m : ℝ) ≤ D + 1) :
    ‖(∑ I ∈ outsideIdealsUpTo S (2 * m),
        baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D)) -
      (∑ I ∈ outsideIdealsUpTo S (2 * m),
        baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ)))‖ ≤
      640 * LipC := by
  classical
  let F := outsideIdealsUpTo S (2 * m)
  have hDpos : 0 < D := by linarith
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le hDpos hmLower
  have hcardNat : F.card ≤ 64 * (2 * m + 1) :=
    outsideIdealsUpTo_card_le S (2 * m)
  have hcard : (F.card : ℝ) ≤ 320 * D := by
    have hcardReal : (F.card : ℝ) ≤ 64 * (2 * (m : ℝ) + 1) := by
      exact_mod_cast hcardNat
    nlinarith
  have hpoint (I : Ideal O) (hIF : I ∈ F) :
      ‖baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D) -
        baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ))‖ ≤
      2 * LipC / D := by
    let n : ℝ := Ideal.absNorm I
    have hn0 : 0 ≤ n := by positivity
    have hn : n ≤ 2 * (m : ℝ) := by
      have hh : Ideal.absNorm I ≤ 2 * m :=
        (mem_outsideIdealsUpTo.mp hIF).2.1
      have hh' : (Ideal.absNorm I : ℝ) ≤ (2 * m : ℕ) := by
        exact_mod_cast hh
      simpa only [n, Nat.cast_mul, Nat.cast_ofNat] using hh'
    have hgap : 0 ≤ (m : ℝ) - D := sub_nonneg.mpr hmLower
    have hgap1 : (m : ℝ) - D ≤ 1 := by linarith
    have hnum : n * ((m : ℝ) - D) ≤ 2 * (m : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn) hgap,
        mul_nonneg hn0 (sub_nonneg.mpr hgap1)]
    have hxy : n / (m : ℝ) ≤ n / D := by
      apply (div_le_div_iff₀ hmpos hDpos).2
      nlinarith [mul_nonneg hn0 hgap]
    have hdiff : n / D - n / (m : ℝ) ≤ 2 / D := by
      have haux : n * ((m : ℝ) - D) / (D * (m : ℝ)) ≤ 2 / D := by
        apply (div_le_div_iff₀ (mul_pos hDpos hmpos) hDpos).2
        nlinarith [mul_le_mul_of_nonneg_right hnum hDpos.le]
      have hfactor : n / D - n / (m : ℝ) =
          n * ((m : ℝ) - D) / (D * (m : ℝ)) := by
        field_simp
      rw [hfactor]
      exact haux
    have habs : |n / D - n / (m : ℝ)| ≤ 2 / D := by
      rwa [abs_of_nonneg (sub_nonneg.mpr hxy)]
    have hW := hLip (n / D) (n / (m : ℝ))
    have hwNorm := baseChangeWeight_norm_le_one χ I
    calc
      ‖baseChangeWeight χ I * W (n / D) -
          baseChangeWeight χ I * W (n / (m : ℝ))‖ =
          ‖baseChangeWeight χ I‖ *
            ‖W (n / D) - W (n / (m : ℝ))‖ := by
              rw [← mul_sub, norm_mul]
      _ ≤ 1 * (LipC * |n / D - n / (m : ℝ)|) :=
        mul_le_mul hwNorm hW (norm_nonneg _) (by positivity)
      _ ≤ 1 * (LipC * (2 / D)) := by
        gcongr
      _ = 2 * LipC / D := by ring
  calc
    ‖(∑ I ∈ F, baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D)) -
      (∑ I ∈ F, baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ)))‖ =
        ‖∑ I ∈ F,
          (baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D) -
            baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ)))‖ := by
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ I ∈ F,
          ‖baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D) -
            baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ))‖ :=
          norm_sum_le _ _
    _ ≤ ∑ _I ∈ F, (2 * LipC / D) := by
      apply Finset.sum_le_sum
      exact hpoint
    _ = (F.card : ℝ) * (2 * LipC / D) := by simp [mul_comm]
    _ ≤ 640 * LipC := by
      have hcoef : 0 ≤ 2 * LipC / D := by positivity
      calc
        (F.card : ℝ) * (2 * LipC / D) ≤
            (320 * D) * (2 * LipC / D) :=
          mul_le_mul_of_nonneg_right hcard hcoef
        _ = 640 * LipC := by
          field_simp
          ring

theorem smooth_supported_hasLipschitzConstant
    (W : ℝ → ℂ) (hSmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hSupp : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0) :
    ∃ LipC : ℝ, 0 ≤ LipC ∧
      ∀ x y : ℝ, ‖W x - W y‖ ≤ LipC * |x - y| := by
  have hCompact : HasCompactSupport W := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    intro x hx
    constructor
    · by_contra h
      have hxle : x ≤ 1 := le_of_not_ge h
      exact hx (hSupp x (Or.inl hxle))
    · by_contra h
      have hxge : 2 ≤ x := le_of_not_ge h
      exact hx (hSupp x (Or.inr hxge))
  obtain ⟨C, hC⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hCompact hSmooth (by simp)
  refine ⟨(C : ℝ), C.2, ?_⟩
  intro x y
  simpa only [dist_eq_norm, Real.norm_eq_abs] using hC.dist_le_mul x y

noncomputable def fixedTestWeight (W : ℝ → ℂ) (m n : ℕ) : ℂ :=
  W (2 * ((n : ℝ) / (2 * m : ℕ)))

theorem fixedTestWeight_eq (W : ℝ → ℂ) {m : ℕ} (hm : 0 < m) (n : ℕ) :
    fixedTestWeight W m n = W ((n : ℝ) / (m : ℝ)) := by
  unfold fixedTestWeight
  congr 1
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  push_cast
  field_simp

structure FixedTestPrimeMS
    {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (W : ℝ → ℂ) (m : ℕ) (ε : ℝ) where
  H : ℕ
  selected : Finset O
  hp : ∀ p ∈ selected, p ≠ 0
  hprime : ∀ p ∈ selected, (Ideal.span {p} : Ideal O).IsMaximal
  hinj : Set.InjOn (fun p : O => (Ideal.span {p} : Ideal O)) (selected : Set O)
  hnormlower : ∀ p ∈ selected,
    ((2 * m : ℕ) : ℝ) ^ (11 / 60 : ℝ) / 2 ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ)
  hnormupper : ∀ p ∈ selected,
    (Ideal.absNorm (Ideal.span {p}) : ℝ) ≤
      ((2 * m : ℕ) : ℝ) ^ (11 / 60 : ℝ)
  hH : Nat.floor (((2 * m : ℕ) : ℝ) ^ (11 / 10 : ℝ)) ≤ H
  hcount : ((2 * m : ℕ) : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤
    (selected.card : ℝ)
  hmean :
    (∑ u ∈ rowNormDisk H,
      ‖idealRowSum (outsideIdealsUpTo S (2 * m))
          (outsideIdealsUpTo_ne_bot S (2 * m))
          (outsideIdealsUpTo_good S (2 * m) hSbad)
          χ (fixedTestWeight W m) u‖ ^ 2) ≤
      ((2 * m : ℕ) : ℝ) ^ ((21 / 10 : ℝ) + ε)

theorem FixedTestPrimeMS.bound
    {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (W : ℝ → ℂ) (m : ℕ) (ε : ℝ)
    (h : FixedTestPrimeMS χ S hSbad W m ε)
    (hm : 0 < m) (hε : 0 ≤ ε) (hW : ∀ y : ℝ, ‖W y‖ ≤ 1) :
    ‖∑ I ∈ outsideIdealsUpTo S (2 * m),
      baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ))‖ ≤
      384 * ((2 * m : ℕ) : ℝ) ^ ((23 / 24 : ℝ) + ε) := by
  have hWeight : ∀ n : ℕ, ‖fixedTestWeight W m n‖ ≤ 1 := by
    intro n
    exact hW _
  have hD : 1 ≤ 2 * m := by omega
  have hbound := outsideCoeff_prime_extraction_from_MS χ
    (fixedTestWeight W m) S hSbad hWeight h.selected (fun p : O => p)
    (2 * m) h.H ε hD hε h.hp h.hprime h.hinj h.hnormlower
    h.hnormupper h.hH h.hcount h.hmean
  rw [← outsideIdealSum_eq_outsideCoeff_sum] at hbound
  simpa only [fixedTestWeight_eq W hm] using hbound

end CompactScaleBridge

end

end OAI
end OAIOriginalModule0080

/-! Original module: OAI.NumberTheory.DirichletL.Mellin.CompactScale
Source SHA256: 7262fb3b7362a6e3cb153b685ab4fd7c27a1214f0fe6b8e9d42a1708bdc0431d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0081


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

namespace CompactScaleBridge

open ConcretePrimeRowBridge ShortDraftHeckeBridge Filter Asymptotics

noncomputable def realCompactOutsideSum
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (W : ℝ → ℂ) (D : ℝ) : ℂ :=
  ∑ I ∈ outsideIdealsUpTo S (2 * Nat.ceil D),
    baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D)

theorem realCompactOutsideSum_bound_of_fixedTestPrimeMS
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (W : ℝ → ℂ) (LipC ε : ℝ) (m₀ : ℕ)
    (hL : 0 ≤ LipC)
    (hLip : ∀ x y : ℝ, ‖W x - W y‖ ≤ LipC * |x - y|)
    (hε : 0 ≤ ε) (hW : ∀ y : ℝ, ‖W y‖ ≤ 1)
    (hMS : ∀ m : ℕ, m₀ ≤ m → FixedTestPrimeMS χ S hSbad W m ε)
    (D : ℝ) (hD : max 1 (m₀ : ℝ) ≤ D) :
    ‖realCompactOutsideSum χ S W D‖ ≤
      (640 * LipC + 384 * (4 : ℝ) ^ ((23 / 24 : ℝ) + ε)) *
        D ^ ((23 / 24 : ℝ) + ε) := by
  let m := Nat.ceil D
  have hD1 : 1 ≤ D := (le_max_left _ _).trans hD
  have hDpos : 0 < D := by linarith
  have hmLower : D ≤ (m : ℝ) := Nat.le_ceil D
  have hmUpper : (m : ℝ) ≤ D + 1 :=
    (Nat.ceil_lt_add_one (by linarith : 0 ≤ D)).le
  have hmPos : 0 < m := by
    have h : (0 : ℝ) < m := lt_of_lt_of_le hDpos hmLower
    exact_mod_cast h
  have hm₀ : m₀ ≤ m := by
    have h : (m₀ : ℝ) ≤ m :=
      ((le_max_right _ _).trans hD).trans hmLower
    exact_mod_cast h
  have hInt := FixedTestPrimeMS.bound χ S hSbad W m ε
    (hMS m hm₀) hmPos hε hW
  have hReal := real_to_integer_compact_bound χ S W LipC D m
    hL hLip hD1 hmLower hmUpper
  let α : ℝ := (23 / 24 : ℝ) + ε
  have hα : 0 ≤ α := by dsimp [α]; linarith
  have hsize : ((2 * m : ℕ) : ℝ) ≤ 4 * D := by
    push_cast
    nlinarith
  have hpower : ((2 * m : ℕ) : ℝ) ^ α ≤ (4 * D) ^ α :=
    Real.rpow_le_rpow (by positivity) hsize hα
  have hDpower : 1 ≤ D ^ α := Real.one_le_rpow hD1 hα
  have hLnonneg : 0 ≤ 640 * LipC := by positivity
  change ‖∑ I ∈ outsideIdealsUpTo S (2 * m),
      baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D)‖ ≤ _
  calc
    ‖∑ I ∈ outsideIdealsUpTo S (2 * m),
        baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D)‖ =
      ‖((∑ I ∈ outsideIdealsUpTo S (2 * m),
          baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D)) -
        (∑ I ∈ outsideIdealsUpTo S (2 * m),
          baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ)))) +
        (∑ I ∈ outsideIdealsUpTo S (2 * m),
          baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ)))‖ := by
            rw [sub_add_cancel]
    _ ≤ 640 * LipC + 384 * ((2 * m : ℕ) : ℝ) ^ α := by
      calc
        _ ≤ ‖(∑ I ∈ outsideIdealsUpTo S (2 * m),
              baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D)) -
              (∑ I ∈ outsideIdealsUpTo S (2 * m),
                baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ)))‖ +
            ‖∑ I ∈ outsideIdealsUpTo S (2 * m),
                baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ))‖ :=
              norm_add_le _ _
        _ ≤ 640 * LipC + 384 * ((2 * m : ℕ) : ℝ) ^ α :=
          add_le_add hReal hInt
    _ ≤ 640 * LipC + 384 * (4 * D) ^ α := by gcongr
    _ = 640 * LipC + 384 * ((4 : ℝ) ^ α * D ^ α) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hDpos.le]
    _ ≤ (640 * LipC + 384 * (4 : ℝ) ^ α) * D ^ α := by
      have hconst : 640 * LipC ≤ 640 * LipC * D ^ α :=
        by simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hDpower hLnonneg)
      nlinarith

theorem realCompactOutsideSum_isBigO_of_fixedTestPrimeMS
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (W : ℝ → ℂ) (LipC ε : ℝ) (m₀ : ℕ)
    (hL : 0 ≤ LipC)
    (hLip : ∀ x y : ℝ, ‖W x - W y‖ ≤ LipC * |x - y|)
    (hε : 0 ≤ ε) (hW : ∀ y : ℝ, ‖W y‖ ≤ 1)
    (hMS : ∀ m : ℕ, m₀ ≤ m → FixedTestPrimeMS χ S hSbad W m ε) :
    (realCompactOutsideSum χ S W) =O[atTop]
      (fun D : ℝ => D ^ ((23 / 24 : ℝ) + ε)) := by
  let C : ℝ := 640 * LipC + 384 * (4 : ℝ) ^ ((23 / 24 : ℝ) + ε)
  apply isBigO_iff_isBigOWith.mpr
  refine ⟨C, IsBigOWith.of_bound ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (m₀ : ℝ))] with D hD
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hD)
  have hpow : 0 ≤ D ^ ((23 / 24 : ℝ) + ε) := Real.rpow_nonneg hDpos.le _
  have h := realCompactOutsideSum_bound_of_fixedTestPrimeMS
    χ S hSbad W LipC ε m₀ hL hLip hε hW hMS D hD
  simpa only [C, Real.norm_eq_abs, abs_of_nonneg hpow] using h

structure FixedTestPrimeMSConstants
    {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (W : ℝ → ℂ) (m : ℕ) (ε Cmean Ccount : ℝ) where
  H : ℕ
  selected : Finset O
  hp : ∀ p ∈ selected, p ≠ 0
  hprime : ∀ p ∈ selected, (Ideal.span {p} : Ideal O).IsMaximal
  hinj : Set.InjOn (fun p : O => (Ideal.span {p} : Ideal O)) (selected : Set O)
  hnormlower : ∀ p ∈ selected,
    ((2 * m : ℕ) : ℝ) ^ (11 / 60 : ℝ) / 2 ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ)
  hnormupper : ∀ p ∈ selected,
    (Ideal.absNorm (Ideal.span {p}) : ℝ) ≤
      ((2 * m : ℕ) : ℝ) ^ (11 / 60 : ℝ)
  hH : Nat.floor (((2 * m : ℕ) : ℝ) ^ (11 / 10 : ℝ)) ≤ H
  hcount : Ccount * ((2 * m : ℕ) : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤
    (selected.card : ℝ)
  hmean :
    (∑ u ∈ rowNormDisk H,
      ‖idealRowSum (outsideIdealsUpTo S (2 * m))
          (outsideIdealsUpTo_ne_bot S (2 * m))
          (outsideIdealsUpTo_good S (2 * m) hSbad)
          χ (fixedTestWeight W m) u‖ ^ 2) ≤
      Cmean * ((2 * m : ℕ) : ℝ) ^ ((21 / 10 : ℝ) + ε)

noncomputable def FixedTestPrimeMSConstants.absorb
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (W : ℝ → ℂ) (m : ℕ) (ε η Cmean Ccount : ℝ)
    (h : FixedTestPrimeMSConstants χ S hSbad W m ε Cmean Ccount)
    (hm : 0 < m) (hCmean : Cmean ≤ ((2 * m : ℕ) : ℝ) ^ η)
    (hCcount : 1 ≤ Ccount * ((2 * m : ℕ) : ℝ) ^ η) :
    FixedTestPrimeMS χ S hSbad W m (ε + η) := by
  let N : ℝ := (2 * m : ℕ)
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast (by omega : 0 < 2 * m)
  have hcount' : N ^ ((11 / 60 : ℝ) - (ε + η)) ≤
      (h.selected.card : ℝ) := by
    calc
      N ^ ((11 / 60 : ℝ) - (ε + η)) =
          1 * N ^ ((11 / 60 : ℝ) - (ε + η)) := by ring
      _ ≤ (Ccount * N ^ η) * N ^ ((11 / 60 : ℝ) - (ε + η)) :=
        mul_le_mul_of_nonneg_right hCcount (Real.rpow_nonneg hNpos.le _)
      _ = Ccount * N ^ ((11 / 60 : ℝ) - ε) := by
        rw [mul_assoc, ← Real.rpow_add hNpos]
        congr 1
        ring_nf
      _ ≤ _ := h.hcount
  have hmean' :
      (∑ u ∈ rowNormDisk h.H,
        ‖idealRowSum (outsideIdealsUpTo S (2 * m))
            (outsideIdealsUpTo_ne_bot S (2 * m))
            (outsideIdealsUpTo_good S (2 * m) hSbad)
            χ (fixedTestWeight W m) u‖ ^ 2) ≤
        N ^ ((21 / 10 : ℝ) + (ε + η)) := by
    calc
      _ ≤ Cmean * N ^ ((21 / 10 : ℝ) + ε) := h.hmean
      _ ≤ N ^ η * N ^ ((21 / 10 : ℝ) + ε) :=
        mul_le_mul_of_nonneg_right hCmean (Real.rpow_nonneg hNpos.le _)
      _ = N ^ ((21 / 10 : ℝ) + (ε + η)) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
  exact {
    H := h.H
    selected := h.selected
    hp := h.hp
    hprime := h.hprime
    hinj := h.hinj
    hnormlower := h.hnormlower
    hnormupper := h.hnormupper
    hH := h.hH
    hcount := hcount'
    hmean := hmean'
  }

theorem realCompactOutsideSum_isBigO_of_fixedTestPrimeMSConstants
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (W : ℝ → ℂ) (LipC ε η Cmean Ccount : ℝ) (m₀ : ℕ)
    (hLipC : 0 ≤ LipC)
    (hLip : ∀ x y : ℝ, ‖W x - W y‖ ≤ LipC * |x - y|)
    (hε : 0 ≤ ε) (hη : 0 < η) (hCcount : 0 < Ccount)
    (hW : ∀ y : ℝ, ‖W y‖ ≤ 1)
    (hMS : ∀ m : ℕ, m₀ ≤ m →
      FixedTestPrimeMSConstants χ S hSbad W m ε Cmean Ccount) :
    (realCompactOutsideSum χ S W) =O[atTop]
      (fun D : ℝ => D ^ ((23 / 24 : ℝ) + (ε + η))) := by
  obtain ⟨N₀, hAbsorb⟩ :=
    eventually_absorb_MS_and_count_constants Cmean Ccount η hCcount hη
  let m₁ := max 1 (max m₀ N₀)
  have hMS' : ∀ m : ℕ, m₁ ≤ m →
      FixedTestPrimeMS χ S hSbad W m (ε + η) := by
    intro m hm
    have hm₀ : m₀ ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
    have hN₀ : N₀ ≤ 2 * m := by omega
    have hmPos : 0 < m := by omega
    have habs := hAbsorb (2 * m) hN₀
    exact (hMS m hm₀).absorb χ S hSbad W m ε η Cmean Ccount
      hmPos habs.1 habs.2
  exact realCompactOutsideSum_isBigO_of_fixedTestPrimeMS χ S hSbad
    W LipC (ε + η) m₁ hLipC hLip (add_nonneg hε hη.le) hW hMS'

end CompactScaleBridge

open Filter Asymptotics MeasureTheory
open scoped Topology

namespace CompactMellinBridge

theorem compact_weight_mellin_convergent
    (W : ℝ → ℂ) (hW : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hsupp : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0)
    (s : ℂ) : MellinConvergent W s := by
  have hlocal : LocallyIntegrableOn W (Set.Ioi (0 : ℝ)) :=
    hW.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htopzero : W =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with y hy
    exact hsupp y (Or.inr hy)
  have hbotzero : W =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with y hy
    exact hsupp y (Or.inl hy.2.le)
  have htop : W =O[atTop] (fun y : ℝ => y ^ (-(s.re + 1))) :=
    htopzero.isBigO.trans (isBigO_zero _ _)
  have hbot : W =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-(s.re - 1))) :=
    hbotzero.isBigO.trans (isBigO_zero _ _)
  exact mellinConvergent_of_isBigO_rpow hlocal htop (by linarith)
    hbot (by linarith)

theorem weighted_term_integrable
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (W : ℝ → ℂ)
    (s : ℂ) (hW : MellinConvergent W s) (n : ℕ) :
    IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) *
        (a n * W ((n : ℝ) * t)))
      (Set.Ioi 0) := by
  by_cases hn : n = 0
  · subst n
    simp [ha0]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hscale : MellinConvergent
        (fun t : ℝ => W ((n : ℝ) * t)) s :=
      (MellinConvergent.comp_mul_left hnpos).mpr hW
    have hscaled := hscale.const_smul (a n)
    simpa only [MellinConvergent, smul_eq_mul, mul_assoc] using hscaled

theorem weighted_sum_continuousOn_pos
    (a : ℕ → ℂ) (W F : ℝ → ℂ)
    (hW : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hsupp : ∀ y : ℝ, 2 ≤ y → W y = 0)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) (F t)) :
    ContinuousOn F (Set.Ioi (0 : ℝ)) := by
  intro t0 ht0
  have ht0pos : 0 < t0 := ht0
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / t0)
  have hNmul := mul_lt_mul_of_pos_right hN (by positivity : 0 < t0 / 2)
  have hNtwo : 2 < (N : ℝ) * (t0 / 2) := by
    have hdiv : (4 / t0) * (t0 / 2) = 2 := by
      field_simp
      ring
    rw [hdiv] at hNmul
    exact hNmul
  have hsumEq (u : ℝ) (hu : t0 / 2 ≤ u) :
      F u = ∑ n ∈ Finset.range N, a n * W ((n : ℝ) * u) := by
    have hupos : 0 < u := lt_of_lt_of_le (by positivity : 0 < t0 / 2) hu
    have htail (n : ℕ) (hn : n ∉ Finset.range N) :
        a n * W ((n : ℝ) * u) = 0 := by
      have hnNat : N ≤ n := Nat.le_of_not_gt (by simpa using hn)
      have hnReal : (N : ℝ) ≤ n := by exact_mod_cast hnNat
      have hnu : 2 ≤ (n : ℝ) * u := by
        calc
          2 ≤ (N : ℝ) * (t0 / 2) := hNtwo.le
          _ ≤ (N : ℝ) * u :=
            mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg (α := ℝ) N)
          _ ≤ (n : ℝ) * u :=
            mul_le_mul_of_nonneg_right hnReal hupos.le
      simp [hsupp _ hnu]
    calc
      F u = ∑' n : ℕ, a n * W ((n : ℝ) * u) := (hF u hupos).tsum_eq.symm
      _ = ∑ n ∈ Finset.range N, a n * W ((n : ℝ) * u) :=
        tsum_eq_sum htail
  have hcontW : Continuous W := hW.continuous
  have hcontSum : Continuous
      (fun u : ℝ => ∑ n ∈ Finset.range N, a n * W ((n : ℝ) * u)) := by
    fun_prop
  have hevent : F =ᶠ[𝓝 t0]
      (fun u : ℝ => ∑ n ∈ Finset.range N, a n * W ((n : ℝ) * u)) := by
    filter_upwards [Ioi_mem_nhds (by linarith : t0 / 2 < t0)] with u hu
    exact hsumEq u hu.le
  exact (hcontSum.continuousAt.congr_of_eventuallyEq hevent).continuousWithinAt

theorem weighted_sum_inv_locallyIntegrableOn_pos
    (a : ℕ → ℂ) (W F : ℝ → ℂ)
    (hW : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hsupp : ∀ y : ℝ, 2 ≤ y → W y = 0)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) (F t)) :
    LocallyIntegrableOn (fun D : ℝ => F D⁻¹) (Set.Ioi 0) := by
  have hcont : ContinuousOn (fun D : ℝ => F D⁻¹) (Set.Ioi 0) := by
    apply (weighted_sum_continuousOn_pos a W F hW hsupp hF).comp
      (continuousOn_inv₀.mono (by
        intro D hD
        exact ne_of_gt hD))
    intro D hD
    exact inv_pos.mpr (show 0 < D from hD)
  exact hcont.locallyIntegrableOn measurableSet_Ioi

private theorem weighted_norm_scale
    (a : ℂ) (W : ℝ → ℂ) (s : ℂ)
    (N t : ℝ) (hN : 0 < N) (ht : 0 < t) :
    ‖(t : ℂ) ^ (s - 1) * (a * W (N * t))‖ =
      (‖a‖ / N ^ (s.re - 1)) *
        ‖(N * t : ℂ) ^ (s - 1) * W (N * t)‖ := by
  have hNt : 0 < N * t := mul_pos hN ht
  have hNpow : 0 < N ^ (s.re - 1) := Real.rpow_pos_of_pos hN _
  rw [norm_mul, norm_mul, norm_mul]
  rw [← Complex.ofReal_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.norm_cpow_eq_rpow_re_of_pos hNt]
  simp only [Complex.sub_re, Complex.one_re]
  rw [Real.mul_rpow hN.le ht.le]
  field_simp

private theorem weighted_norm_integral
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (W : ℝ → ℂ)
    (s : ℂ) (n : ℕ) :
    (∫ t : ℝ in Set.Ioi 0,
      ‖(t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))‖) =
    ‖LSeries.term a s n‖ *
      (∫ u : ℝ in Set.Ioi 0,
        ‖(u : ℂ) ^ (s - 1) * W u‖) := by
  by_cases hn : n = 0
  · subst n
    simp [ha0, LSeries.term_zero]
  · have hN : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    let G : ℝ → ℝ := fun u => ‖(u : ℂ) ^ (s - 1) * W u‖
    have hscale :
        (∫ t : ℝ in Set.Ioi 0,
          ‖(t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))‖) =
          (‖a n‖ / (n : ℝ) ^ (s.re - 1)) *
            (∫ t : ℝ in Set.Ioi 0, G ((n : ℝ) * t)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simpa only [G, Complex.ofReal_mul] using
        weighted_norm_scale (a n) W s n t hN ht
    rw [hscale, integral_comp_mul_left_Ioi G 0 hN]
    simp only [mul_zero, smul_eq_mul]
    have hpow : (n : ℝ) ^ (s.re - 1) * (n : ℝ) =
        (n : ℝ) ^ s.re := by
      calc
        (n : ℝ) ^ (s.re - 1) * (n : ℝ) =
            (n : ℝ) ^ (s.re - 1) * (n : ℝ) ^ (1 : ℝ) := by
              rw [Real.rpow_one]
        _ = (n : ℝ) ^ ((s.re - 1) + 1) :=
          (Real.rpow_add hN (s.re - 1) 1).symm
        _ = (n : ℝ) ^ s.re := by congr 1; ring
    rw [LSeries.norm_term_eq]
    simp only [ite_eq_right hn, G]
    have hinv : ((n : ℝ) ^ (s.re - 1))⁻¹ * (n : ℝ)⁻¹ =
        ((n : ℝ) ^ s.re)⁻¹ := by
      rw [← mul_inv_rev, mul_comm, hpow]
    simp only [div_eq_mul_inv]
    calc
      ‖a n‖ * ((n : ℝ) ^ (s.re - 1))⁻¹ *
          ((n : ℝ)⁻¹ *
            (∫ u : ℝ in Set.Ioi 0, ‖(u : ℂ) ^ (s - 1) * W u‖)) =
          (‖a n‖ * (((n : ℝ) ^ (s.re - 1))⁻¹ * (n : ℝ)⁻¹)) *
            (∫ u : ℝ in Set.Ioi 0, ‖(u : ℂ) ^ (s - 1) * W u‖) := by ring
      _ = (‖a n‖ * ((n : ℝ) ^ s.re)⁻¹) *
            (∫ u : ℝ in Set.Ioi 0, ‖(u : ℂ) ^ (s - 1) * W u‖) := by rw [hinv]

theorem weighted_terms_fubini
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (W : ℝ → ℂ)
    (s : ℂ) (hlsum : LSeriesSummable a s) :
    Summable (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi 0,
        ‖(t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))‖) := by
  let C : ℝ := ∫ u : ℝ in Set.Ioi 0,
    ‖(u : ℂ) ^ (s - 1) * W u‖
  have hnorm : Summable (fun n : ℕ => ‖LSeries.term a s n‖) := hlsum.norm
  have hsum : Summable (fun n : ℕ => ‖LSeries.term a s n‖ * C) :=
    hnorm.mul_right C
  exact hsum.congr (fun n => (weighted_norm_integral a ha0 W s n).symm)

noncomputable def finiteEulerFactor
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ShortDraftHeckeBridge.O)) (s : ℂ) : ℂ :=
  ∏ P ∈ S,
    (1 - χ (Ideal.absNorm P) *
      ((Ideal.absNorm P : ℂ) ^ (-s)))

theorem finiteEulerFactor_analytic
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ShortDraftHeckeBridge.O))
    (hprime : ∀ P ∈ S, Prime P) (σ : ℝ) :
    AnalyticOnNhd ℂ (finiteEulerFactor χ S)
      {s : ℂ | σ < s.re} := by
  have hE : Differentiable ℂ (finiteEulerFactor χ S) := by
    unfold finiteEulerFactor
    apply Differentiable.fun_finsetProd
    intro P hPS
    have hN : Ideal.absNorm P ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr (hprime P hPS).1
    have hNc : (Ideal.absNorm P : ℂ) ≠ 0 := by exact_mod_cast hN
    have hcpow : Differentiable ℂ
        (fun s : ℂ => ((Ideal.absNorm P : ℂ) ^ (-s))) :=
      (differentiable_id.neg).const_cpow (Or.inl hNc)
    exact (differentiable_const (1 : ℂ)).sub
      ((differentiable_const (χ (Ideal.absNorm P))).mul hcpow)
  exact (Complex.analyticOnNhd_iff_differentiableOn
    (Complex.isOpen_re_gt σ)).2 hE.differentiableOn

theorem zero_free_of_analytic_identity_gt_two
    (σ : ℝ) (hσ : σ < 2) (G M W : ℂ → ℂ)
    (hG : AnalyticOnNhd ℂ G {s | σ < s.re})
    (hM : AnalyticOnNhd ℂ M {s | σ < s.re})
    (hW : AnalyticOnNhd ℂ W {s | σ < s.re})
    (heq : ∀ s : ℂ, 2 < s.re → G s * M s = W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hWρ : W ρ ≠ 0) : G ρ ≠ 0 := by
  have hthree : (3 : ℂ) ∈ {s : ℂ | σ < s.re} := by
    change σ < (3 : ℂ).re
    norm_num at *
    linarith
  have heventual : (fun s : ℂ => G s * M s) =ᶠ[𝓝 (3 : ℂ)] W := by
    filter_upwards [((Complex.isOpen_re_gt 2).mem_nhds
      (by norm_num : (3 : ℂ) ∈ {s : ℂ | 2 < s.re}))] with s hs
    exact heq s hs
  have hident : Set.EqOn (fun s : ℂ => G s * M s) W
      {s | σ < s.re} :=
    (hG.mul hM).eqOn_of_preconnected_of_eventuallyEq hW
      ((convex_halfSpace_re_gt σ).isPreconnected) hthree heventual
  intro hGρ
  have heqρ := hident hρ
  change G ρ * M ρ = W ρ at heqρ
  rw [hGρ, zero_mul] at heqρ
  exact hWρ heqρ.symm

theorem zero_free_of_regularized_identity_gt_two
    (σ : ℝ) (hσ : σ < 2) (G Lregular M W : ℂ → ℂ)
    (hLregular : AnalyticOnNhd ℂ Lregular {s | σ < s.re})
    (hM : AnalyticOnNhd ℂ M {s | σ < s.re})
    (hW : AnalyticOnNhd ℂ W {s | σ < s.re})
    (hregular : ∀ s : ℂ, σ < s.re → s ≠ 1 →
      Lregular s = (s - 1) * G s)
    (heq : ∀ s : ℂ, 2 < s.re →
      Lregular s * M s = (s - 1) * W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1)
    (hWρ : W ρ ≠ 0) : G ρ ≠ 0 := by
  have hWregular : AnalyticOnNhd ℂ
      (fun s : ℂ => (s - 1) * W s) {s | σ < s.re} :=
    (analyticOnNhd_id.sub analyticOnNhd_const).mul hW
  have hWregularρ : (ρ - 1) * W ρ ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hρone) hWρ
  have hLregularρ := zero_free_of_analytic_identity_gt_two σ hσ
    Lregular M (fun s : ℂ => (s - 1) * W s)
    hLregular hM hWregular heq ρ hρ hWregularρ
  rw [hregular ρ hρ hρone] at hLregularρ
  exact (mul_ne_zero_iff.mp hLregularρ).2

theorem outsideCoeff_baseChange_zero {q : ℕ}
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal FiniteSFactor.O)) :
    FiniteSFactor.outsideCoeff S
      (ShortDraftHeckeBridge.baseChangeWeight χ) 0 = 0 := by
  classical
  unfold FiniteSFactor.outsideCoeff
  apply Finset.sum_eq_zero
  intro I hI
  have hnorm : Ideal.absNorm I = 0 := by
    simpa [FiniteSFactor.fiber] using hI
  have hbot : I = ⊥ := Ideal.absNorm_eq_zero_iff.mp hnorm
  subst I
  unfold FiniteSFactor.outsideWeight
  split_ifs
  · have hz : UniqueFactorizationMonoid.moebius (⊥ : Ideal FiniteSFactor.O) = 0 := by
      simpa only [Ideal.zero_eq_bot] using
        (UniqueFactorizationMonoid.moebius_zero (α := Ideal FiniteSFactor.O))
    simp [ShortDraftHeckeBridge.baseChangeWeight, hz]
  · rfl

noncomputable def outsideCompactSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal FiniteSFactor.O)) (W : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℕ,
    FiniteSFactor.outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ) n *
      W ((n : ℝ) * t)

theorem outsideCompactSum_hasSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal FiniteSFactor.O)) (W : ℝ → ℂ)
    (hsupp : ∀ y : ℝ, 2 ≤ y → W y = 0)
    (t : ℝ) (ht : 0 < t) :
    HasSum (fun n : ℕ =>
      FiniteSFactor.outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ) n *
        W ((n : ℝ) * t)) (outsideCompactSum χ S W t) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / t)
  have htail (n : ℕ) (hn : n ∉ Finset.range N) :
      FiniteSFactor.outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ) n *
        W ((n : ℝ) * t) = 0 := by
    have hnNat : N ≤ n := Nat.le_of_not_gt (by simpa using hn)
    have hnReal : (N : ℝ) ≤ n := by exact_mod_cast hnNat
    have hNt : 2 ≤ (N : ℝ) * t := by
      have h := mul_lt_mul_of_pos_right hN ht
      have hcancel : (2 / t) * t = 2 := by
        field_simp
      rw [hcancel] at h
      exact h.le
    have hnt : 2 ≤ (n : ℝ) * t :=
      hNt.trans (mul_le_mul_of_nonneg_right hnReal ht.le)
    simp [hsupp _ hnt]
  exact (summable_of_ne_finset_zero htail).hasSum

theorem outside_compact_euler_identity {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal FiniteSFactor.O)) (hS : ∀ P ∈ S, Prime P)
    (W : ℝ → ℂ) (hW : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hsupp : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0)
    (s : ℂ) (hs : 2 < s.re) :
    (χ.LFunction s * (ShortDraftHeckeBridge.baseChangeChar χ).LFunction s) *
      (finiteEulerFactor χ S s *
        mellin (fun D : ℝ => (outsideCompactSum χ S W) D⁻¹) (-s)) =
      mellin W s := by
  let a : ℕ → ℂ := FiniteSFactor.outsideCoeff S
    (ShortDraftHeckeBridge.baseChangeWeight χ)
  have ha0 : a 0 = 0 := outsideCoeff_baseChange_zero χ S
  have hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t))
        (outsideCompactSum χ S W t) := by
    intro t ht
    exact outsideCompactSum_hasSum χ S W (fun y hy => hsupp y (Or.inr hy)) t ht
  have hlsum : LSeriesSummable a s :=
    FiniteSFactor.outsideCoeff_LSeriesSummable_baseChange χ S s hs
  have hM := mellin_weighted_sum a W (outsideCompactSum χ S W) s
    ha0 hF
    (weighted_term_integrable a ha0 W s
      (compact_weight_mellin_convergent W hW hsupp s))
    (weighted_terms_fubini a ha0 W s hlsum) hlsum
  have hnorm := FiniteSFactor.normFiberLSeries_finiteEuler_baseChange
    χ S hS s hs
  change LSeries (ShortDraftHeckeBridge.normFiberCoeff
    (ShortDraftHeckeBridge.baseChangeWeight χ)) s =
    finiteEulerFactor χ S s * LSeries a s at hnorm
  have hcoeff := ShortDraftHeckeBridge.normFiberCoeff_baseChange_eq_pairInverseCoeff χ
  have hpair := ShortDraftHeckeBridge.normFiber_LSeries_eq_pair_inverse
    χ (ShortDraftHeckeBridge.baseChangeChar χ)
    (ShortDraftHeckeBridge.baseChangeWeight χ) hcoeff s
  have hEuler := ShortDraftHeckeBridge.pair_inverse_euler_identity
    χ (ShortDraftHeckeBridge.baseChangeChar χ) s (by linarith : 1 < s.re)
  have hfinite :
      (χ.LFunction s * (ShortDraftHeckeBridge.baseChangeChar χ).LFunction s) *
        (finiteEulerFactor χ S s * LSeries a s) = 1 := by
    rw [← hnorm, hpair]
    exact hEuler
  rw [hM]
  calc
    (χ.LFunction s * (ShortDraftHeckeBridge.baseChangeChar χ).LFunction s) *
        (finiteEulerFactor χ S s * (mellin W s * LSeries a s)) =
      ((χ.LFunction s * (ShortDraftHeckeBridge.baseChangeChar χ).LFunction s) *
        (finiteEulerFactor χ S s * LSeries a s)) * mellin W s := by ring
    _ = mellin W s := by rw [hfinite]; ring

theorem pair_zero_free_of_identity_gt_two
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hnotboth : χ ≠ 1 ∨ ψ ≠ 1)
    (σ : ℝ) (hσ : σ < 1) (M W : ℂ → ℂ)
    (hM : AnalyticOnNhd ℂ M {s : ℂ | σ < s.re})
    (hW : AnalyticOnNhd ℂ W {s : ℂ | σ < s.re})
    (heq : ∀ s : ℂ, 2 < s.re →
      (χ.LFunction s * ψ.LFunction s) * M s = W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1)
    (hWρ : W ρ ≠ 0) :
    χ.LFunction ρ ≠ 0 ∧ ψ.LFunction ρ ≠ 0 := by
  let U : Set ℂ := {s : ℂ | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hσtwo : σ < 2 := by linarith
  by_cases hχ : χ = 1
  · have hψ : ψ ≠ 1 := by
      intro hψ
      rcases hnotboth with h | h
      · exact h hχ
      · exact h hψ
    subst χ
    have hLregular₁ : AnalyticOnNhd ℂ
        (DirichletCharacter.LFunctionTrivChar₁ q) U :=
      (Complex.analyticOnNhd_iff_differentiableOn hopen).2
        (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).differentiableOn
    have hLψ : AnalyticOnNhd ℂ ψ.LFunction U :=
      (Complex.analyticOnNhd_iff_differentiableOn hopen).2
        (ψ.differentiable_LFunction hψ).differentiableOn
    have hLregular : AnalyticOnNhd ℂ
        (fun s => DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s) U :=
      hLregular₁.mul hLψ
    have hregular : ∀ s : ℂ, σ < s.re → s ≠ 1 →
        DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s =
          (s - 1) * ((1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s) := by
      intro s _ hs
      simp [DirichletCharacter.LFunctionTrivChar₁,
        DirichletCharacter.LFunctionTrivChar, Function.update_of_ne hs]
      ring
    have heqregular : ∀ s : ℂ, 2 < s.re →
        (DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s) * M s =
          (s - 1) * W s := by
      intro s hs
      rw [hregular s (lt_trans hσ (by linarith : 1 < s.re)) (by
        intro h; subst s; norm_num at hs)]
      calc
        (s - 1) * ((1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s) * M s =
            (s - 1) * (((1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s) * M s) := by ring
        _ = (s - 1) * W s := by rw [heq s hs]
    have hprod := zero_free_of_regularized_identity_gt_two σ hσtwo
      (fun s => (1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s)
      (fun s => DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s)
      M W hLregular hM hW hregular heqregular ρ hρ hρone hWρ
    exact mul_ne_zero_iff.mp hprod
  · by_cases hψ : ψ = 1
    · subst ψ
      have hLregular₁ : AnalyticOnNhd ℂ
          (DirichletCharacter.LFunctionTrivChar₁ r) U :=
        (Complex.analyticOnNhd_iff_differentiableOn hopen).2
          (DirichletCharacter.differentiable_LFunctionTrivChar₁ r).differentiableOn
      have hLχ : AnalyticOnNhd ℂ χ.LFunction U :=
        (Complex.analyticOnNhd_iff_differentiableOn hopen).2
          (χ.differentiable_LFunction hχ).differentiableOn
      have hLregular : AnalyticOnNhd ℂ
          (fun s => χ.LFunction s * DirichletCharacter.LFunctionTrivChar₁ r s) U :=
        hLχ.mul hLregular₁
      have hregular : ∀ s : ℂ, σ < s.re → s ≠ 1 →
          χ.LFunction s * DirichletCharacter.LFunctionTrivChar₁ r s =
            (s - 1) * (χ.LFunction s *
              (1 : DirichletCharacter ℂ r).LFunction s) := by
        intro s _ hs
        simp [DirichletCharacter.LFunctionTrivChar₁,
          DirichletCharacter.LFunctionTrivChar, Function.update_of_ne hs]
        ring
      have heqregular : ∀ s : ℂ, 2 < s.re →
          (χ.LFunction s * DirichletCharacter.LFunctionTrivChar₁ r s) * M s =
            (s - 1) * W s := by
        intro s hs
        rw [hregular s (lt_trans hσ (by linarith : 1 < s.re)) (by
          intro h; subst s; norm_num at hs)]
        calc
          (s - 1) * (χ.LFunction s *
              (1 : DirichletCharacter ℂ r).LFunction s) * M s =
              (s - 1) * ((χ.LFunction s *
                (1 : DirichletCharacter ℂ r).LFunction s) * M s) := by ring
          _ = (s - 1) * W s := by rw [heq s hs]
      have hprod := zero_free_of_regularized_identity_gt_two σ hσtwo
        (fun s => χ.LFunction s *
          (1 : DirichletCharacter ℂ r).LFunction s)
        (fun s => χ.LFunction s * DirichletCharacter.LFunctionTrivChar₁ r s)
        M W hLregular hM hW hregular heqregular ρ hρ hρone hWρ
      exact mul_ne_zero_iff.mp hprod
    · have hLχ : AnalyticOnNhd ℂ χ.LFunction U :=
        (Complex.analyticOnNhd_iff_differentiableOn hopen).2
          (χ.differentiable_LFunction hχ).differentiableOn
      have hLψ : AnalyticOnNhd ℂ ψ.LFunction U :=
        (Complex.analyticOnNhd_iff_differentiableOn hopen).2
          (ψ.differentiable_LFunction hψ).differentiableOn
      have hprod := zero_free_of_analytic_identity_gt_two σ hσtwo
        (fun s => χ.LFunction s * ψ.LFunction s) M W
        (hLχ.mul hLψ) hM hW heq ρ hρ hWρ
      exact mul_ne_zero_iff.mp hprod

theorem baseChange_outsideCompact_zero_free {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal FiniteSFactor.O)) (hS : ∀ P ∈ S, Prime P)
    (W : ℝ → ℂ) (hW : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hsupp : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0)
    (σ : ℝ)
    (htop : (fun D : ℝ => outsideCompactSum χ S W D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (ρ : ℂ) (hσρ : σ < ρ.re) (hρone : ρ.re < 1)
    (hWρ : mellin W ρ ≠ 0) :
    χ.LFunction ρ ≠ 0 := by
  let a : ℕ → ℂ := FiniteSFactor.outsideCoeff S
    (ShortDraftHeckeBridge.baseChangeWeight χ)
  have ha0 : a 0 = 0 := outsideCoeff_baseChange_zero χ S
  have hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t))
        (outsideCompactSum χ S W t) := by
    intro t ht
    exact outsideCompactSum_hasSum χ S W (fun y hy => hsupp y (Or.inr hy)) t ht
  have hlocal : LocallyIntegrableOn
      (fun D : ℝ => outsideCompactSum χ S W D⁻¹) (Set.Ioi 0) :=
    weighted_sum_inv_locallyIntegrableOn_pos a W
      (outsideCompactSum χ S W) hW
      (fun y hy => hsupp y (Or.inr hy)) hF
  have hzero : (fun D : ℝ => outsideCompactSum χ S W D⁻¹) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun _ => 0) :=
    weighted_sum_zero_near_small_D a ha0 W
      (outsideCompactSum χ S W)
      (fun y hy => hsupp y (Or.inr hy)) hF
  have hM : AnalyticOnNhd ℂ
      (fun s : ℂ => mellin
        (fun D : ℝ => outsideCompactSum χ S W D⁻¹) (-s))
      {s : ℂ | σ < s.re} :=
    ShortDraftMellin.inverse_mellin_analytic _ σ hlocal htop hzero
  have hE : AnalyticOnNhd ℂ (finiteEulerFactor χ S)
      {s : ℂ | σ < s.re} :=
    finiteEulerFactor_analytic χ S hS σ
  have hWanalytic : AnalyticOnNhd ℂ (mellin W)
      {s : ℂ | σ < s.re} :=
    compact_weight_mellin_analytic W hW hsupp σ
  have hnotboth : χ ≠ 1 ∨ ShortDraftHeckeBridge.baseChangeChar χ ≠ 1 := by
    by_cases hχ : χ = 1
    · exact Or.inr (ShortDraftHeckeBridge.baseChangeChar_ne_one_of_one χ hχ)
    · exact Or.inl hχ
  have heq (s : ℂ) (hs : 2 < s.re) :
      (χ.LFunction s *
        (ShortDraftHeckeBridge.baseChangeChar χ).LFunction s) *
        (finiteEulerFactor χ S s *
          mellin (fun D : ℝ => outsideCompactSum χ S W D⁻¹) (-s)) =
        mellin W s :=
    outside_compact_euler_identity χ S hS W hW hsupp s hs
  have hρneq : ρ ≠ 1 := by
    intro h
    subst ρ
    norm_num at hρone
  exact (pair_zero_free_of_identity_gt_two
    χ (ShortDraftHeckeBridge.baseChangeChar χ) hnotboth
    σ (lt_trans hσρ hρone)
    (fun s => finiteEulerFactor χ S s *
      mellin (fun D : ℝ => outsideCompactSum χ S W D⁻¹) (-s))
    (mellin W) (hE.mul hM) hWanalytic heq
    ρ hσρ hρneq hWρ).1

structure BaseChangeOutsideCompactTest
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) where
  S : Finset (Ideal FiniteSFactor.O)
  S_prime : ∀ P ∈ S, Prime P
  W : ℝ → ℂ
  sigma : ℝ
  sigma_lt : sigma < ρ.re
  smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) W
  support : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0
  power_bound :
    (fun D : ℝ => outsideCompactSum χ S W D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ sigma)
  mellin_nonzero : mellin W ρ ≠ 0

theorem dirichletTarget_of_compact_outside_tests
    (hTest : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (ρ : ℂ), (23 / 24 : ℝ) < ρ.re → ρ.re < 1 →
        BaseChangeOutsideCompactTest χ ρ) :
    ShortDraft.DirichletTarget := by
  intro q _ χ ρ h23 hprincipal
  by_cases hρ : ρ.re < 1
  · let T := hTest q χ ρ h23 hρ
    exact baseChange_outsideCompact_zero_free χ T.S T.S_prime
      T.W T.smooth T.support T.sigma T.power_bound
      ρ T.sigma_lt hρ T.mellin_nonzero
  · exact ShortDraft.dirichlet_target_of_one_le_re q χ ρ
      (le_of_not_gt hρ) hprincipal

end CompactMellinBridge

end

end OAI
end OAIOriginalModule0081

/-! Original module: OAI.NumberTheory.DirichletL.Mellin.CompactWeights
Source SHA256: 819234aaf334c97ea09351c4f6e0171f187718cda5e4d8dcecae7f7db45d79dd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0082


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

namespace CompactScaleBridge

section

open ConcretePrimeRowBridge ShortDraftHeckeBridge FiniteSFactor

theorem outsideCoeff_baseChange_zero
    {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal O)) :
    outsideCoeff S (baseChangeWeight χ) 0 = 0 := by
  classical
  unfold outsideCoeff
  apply Finset.sum_eq_zero
  intro I hI
  have hnorm : Ideal.absNorm I = 0 := mem_fiber.mp hI
  have hbot : I = ⊥ := Ideal.absNorm_eq_zero_iff.mp hnorm
  subst I
  have hz : baseChangeWeight χ (⊥ : Ideal O) = 0 := by
    rw [baseChangeWeight]
    have hμ : UniqueFactorizationMonoid.moebius (⊥ : Ideal O) = 0 := by
      simpa only [Ideal.zero_eq_bot] using
        (UniqueFactorizationMonoid.moebius_zero (α := Ideal O))
    rw [hμ]
    simp
  by_cases hgood : ∀ P ∈ S, ¬P ∣ (⊥ : Ideal O) <;>
    simp [outsideWeight,  hz]

theorem outsideCoeff_compact_hasSum
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (W : ℝ → ℂ) (D : ℝ)
    (hD : 0 < D) (hSupp : ∀ y : ℝ, 2 ≤ y → W y = 0) :
    HasSum (fun n : ℕ =>
      outsideCoeff S (baseChangeWeight χ) n * W ((n : ℝ) / D))
      (realCompactOutsideSum χ S W D) := by
  classical
  let N : ℕ := 2 * Nat.ceil D
  have hNreal : 2 * D ≤ (N : ℝ) := by
    dsimp [N]
    push_cast
    nlinarith [Nat.le_ceil D]
  have hterm (n : ℕ) (hn : n ∉ Finset.Icc 1 N) :
      outsideCoeff S (baseChangeWeight χ) n * W ((n : ℝ) / D) = 0 := by
    by_cases hn0 : n = 0
    · subst n
      rw [outsideCoeff_baseChange_zero]
      simp
    · have hn_gt : N < n := by
        simp only [Finset.mem_Icc] at hn
        omega
      have hnreal : (N : ℝ) < n := by exact_mod_cast hn_gt
      have hratio : 2 ≤ (n : ℝ) / D := by
        apply (le_div_iff₀ hD).2
        nlinarith
      simp [hSupp _ hratio]
  have hs : HasSum (fun n : ℕ =>
      outsideCoeff S (baseChangeWeight χ) n * W ((n : ℝ) / D))
      (∑ n ∈ Finset.Icc 1 N,
        outsideCoeff S (baseChangeWeight χ) n * W ((n : ℝ) / D)) :=
    hasSum_sum_of_ne_finset_zero hterm
  change HasSum _ (∑ I ∈ outsideIdealsUpTo S N,
      baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D))
  rw [outsideIdealSum_eq_outsideCoeff_sum S N (baseChangeWeight χ)
    (fun n : ℕ => W ((n : ℝ) / D))]
  exact hs

end

open ConcretePrimeRowBridge ShortDraftHeckeBridge Filter Asymptotics

theorem realCompactOutsideSum_eq_outsideCompactSum
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (W : ℝ → ℂ) (D : ℝ)
    (hD : 0 < D) (hSupp : ∀ y : ℝ, 2 ≤ y → W y = 0) :
    realCompactOutsideSum χ S W D =
      CompactMellinBridge.outsideCompactSum χ S W D⁻¹ := by
  have hs := outsideCoeff_compact_hasSum χ S W D hD hSupp
  have h := hs.tsum_eq
  simpa only [CompactMellinBridge.outsideCompactSum, div_eq_mul_inv] using h.symm

theorem zero_free_of_fixedTestPrimeMSConstants
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O))
    (hSprime : ∀ P ∈ S, Prime P)
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (W : ℝ → ℂ) (hSmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hSupp : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0)
    (hBoundW : ∀ y : ℝ, ‖W y‖ ≤ 1)
    (ε η Cmean Ccount : ℝ) (m₀ : ℕ)
    (hε : 0 ≤ ε) (hη : 0 < η) (hCcount : 0 < Ccount)
    (hMS : ∀ m : ℕ, m₀ ≤ m →
      FixedTestPrimeMSConstants χ S hSbad W m ε Cmean Ccount)
    (ρ : ℂ) (hσρ : (23 / 24 : ℝ) + (ε + η) < ρ.re)
    (hρone : ρ.re < 1) (hWρ : mellin W ρ ≠ 0) :
    χ.LFunction ρ ≠ 0 := by
  obtain ⟨LipC, hLipC, hLip⟩ :=
    smooth_supported_hasLipschitzConstant W hSmooth hSupp
  have hFinite := realCompactOutsideSum_isBigO_of_fixedTestPrimeMSConstants
    χ S hSbad W LipC ε η Cmean Ccount m₀
    hLipC hLip hε hη hCcount hBoundW hMS
  have hEq :
      (fun D : ℝ => CompactMellinBridge.outsideCompactSum χ S W D⁻¹) =ᶠ[atTop]
      (realCompactOutsideSum χ S W) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with D hD
    exact (realCompactOutsideSum_eq_outsideCompactSum χ S W D hD
      (fun y hy => hSupp y (Or.inr hy))).symm
  have hTop :
      (fun D : ℝ => CompactMellinBridge.outsideCompactSum χ S W D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ ((23 / 24 : ℝ) + (ε + η))) :=
    hFinite.congr' hEq.symm Filter.EventuallyEq.rfl
  exact CompactMellinBridge.baseChange_outsideCompact_zero_free
    χ S hSprime W hSmooth hSupp ((23 / 24 : ℝ) + (ε + η)) hTop
    ρ hσρ hρone hWρ

end CompactScaleBridge

open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ConcreteCompactWeight

noncomputable def bumpData : ContDiffBump (3 / 2 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

noncomputable def bump (y : ℝ) : ℝ := bumpData y

theorem bump_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) bump := by
  change ContDiff ℝ (↑(⊤ : ℕ∞)) (bumpData : ℝ → ℝ)
  exact bumpData.contDiff (n := ⊤)
