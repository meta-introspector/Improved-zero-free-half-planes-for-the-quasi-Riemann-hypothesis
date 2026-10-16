  apply hbound.trans_eq
  rw [hzexp]
  dsimp only [C]
  field_simp [hhat.ne']

end

section

open scoped BigOperators Classical SchwartzMap ContDiff Topology
open Filter Asymptotics MeasureTheory
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open ShortDraftHeckeBridge
open IdealMobiusDivisorSum hiding O
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalRowCompletion
open InitialMeanSquare

def weightedMoebius {q : ℕ} (χ : DirichletCharacter ℂ q) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  baseChangeWeight χ I*totientDensity I

def outsideWeight {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) : Ideal ActualEisensteinCubic.O→ℂ :=
  FiniteSFactor.outsideWeight S (weightedMoebius χ)

def weightedCoeff {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) : ℕ→ℂ :=
  FiniteSFactor.outsideCoeff S (weightedMoebius χ)

theorem totientDensity_norm_le_one (I : Ideal ActualEisensteinCubic.O) : ‖totientDensity I‖≤1 := by
  rw [totientDensity,norm_prod]
  apply Finset.prod_le_one₀
  · intro P hP
    exact norm_nonneg _
  · intro P hP
    have hN : (2:ℝ)≤Ideal.absNorm P:=by exact_mod_cast IdealDivisorBound.support_norm_two_le hP
    have hNp : (0:ℝ)<Ideal.absNorm P:=by linarith
    have he : (1-(1:ℂ)/(Ideal.absNorm P:ℂ))=((1-1/(Ideal.absNorm P:ℝ):ℝ):ℂ) := by push_cast;rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
    · exact sub_le_self _ (by positivity)
    · have hi : (1:ℝ)/(Ideal.absNorm P:ℝ)≤1 := (div_le_one hNp).mpr (by linarith)
      linarith

theorem weightedMoebius_norm_le_one {q : ℕ} (χ : DirichletCharacter ℂ q)
    (I : Ideal ActualEisensteinCubic.O) : ‖weightedMoebius χ I‖≤1 := by
  rw [weightedMoebius,norm_mul]
  exact (mul_le_mul (ConcretePrimeRowBridge.baseChangeWeight_norm_le_one χ I)
    (totientDensity_norm_le_one I) (norm_nonneg _) zero_le_one).trans_eq (mul_one _)

@[simp] theorem weightedMoebius_zero {q : ℕ} (χ : DirichletCharacter ℂ q) :
    weightedMoebius χ (0:Ideal ActualEisensteinCubic.O)=0 := by
  change ((UniqueFactorizationMonoid.moebius (0:Ideal ActualEisensteinCubic.O):ℂ)*
    χ (Ideal.absNorm (0:Ideal ActualEisensteinCubic.O)))*totientDensity 0=0
  rw [UniqueFactorizationMonoid.moebius_zero,Int.cast_zero,zero_mul,zero_mul]

theorem outsideWeight_norm_le_one {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (I : Ideal ActualEisensteinCubic.O) :
    ‖outsideWeight χ S I‖≤1 := by
  unfold outsideWeight FiniteSFactor.outsideWeight
  split_ifs
  · exact weightedMoebius_norm_le_one χ I
  · simp

@[simp] theorem outsideWeight_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) :
    outsideWeight χ S (0:Ideal ActualEisensteinCubic.O)=0 := by
  unfold outsideWeight FiniteSFactor.outsideWeight
  split_ifs
  · exact weightedMoebius_zero χ
  · rfl

@[simp] theorem weightedCoeff_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) : weightedCoeff χ S 0=0 := by
  unfold weightedCoeff FiniteSFactor.outsideCoeff
  apply Finset.sum_eq_zero
  intro I hI
  have hz:=Ideal.absNorm_eq_zero_iff.mp (FiniteSFactor.mem_fiber.mp hI)
  change outsideWeight χ S I=0
  rw [hz]
  exact outsideWeight_zero χ S

theorem weightedCoeff_norm_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (n : ℕ) : ‖weightedCoeff χ S n‖≤128*n := by
  by_cases hn : n=0
  · subst n
    simp
  have hn1 : (1:ℝ)≤n:=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hc:=DescentFiberCost.finite_ideal_count_real (FiniteSFactor.fiber n) n hn1 (by
      intro I hI hz
      have hh:=FiniteSFactor.mem_fiber.mp hI
      rw [hz] at hh
      simp only [Ideal.absNorm_bot] at hh
      exact hn hh.symm) (by
      intro I hI
      exact_mod_cast (FiniteSFactor.mem_fiber.mp hI).le)
  calc
    _≤∑I∈FiniteSFactor.fiber n,‖outsideWeight χ S I‖:=norm_sum_le _ _
    _≤∑I∈FiniteSFactor.fiber n,(1:ℝ):=Finset.sum_le_sum (fun I hI=>outsideWeight_norm_le_one χ S I)
    _=(FiniteSFactor.fiber n).card:=by simp
    _≤128*n:=hc

theorem weightedCoeff_LSeriesSummable {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (s : ℂ) (hs : 2<s.re) :
    LSeriesSummable (weightedCoeff χ S) s := by
  apply LSeriesSummable_of_isBigO_rpow hs
  apply Asymptotics.IsBigO.of_bound 128
  filter_upwards [] with n
  simpa only [show (2:ℝ)-1=1 by norm_num,Real.rpow_one,Real.norm_natCast]
    using weightedCoeff_norm_bound χ S n

theorem weightedCoeff_hasSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (W : ℝ→ℂ) (b Z : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0→x≤b) (D : ℕ) (hD : b*Z≤D) :
    HasSum (fun n : ℕ=>weightedCoeff χ S n*W ((n:ℝ)/Z))
      (∑I∈outsideIdealsUpTo S D,baseChangeWeight χ I*W ((Ideal.absNorm I:ℝ)/Z)*totientDensity I) := by
  have ht (n : ℕ) (hn : n∉Finset.Icc 1 D) : weightedCoeff χ S n*W ((n:ℝ)/Z)=0 := by
    by_cases hn0 : n=0
    · subst n
      simp
    · have hnD : D<n := by simp only [Finset.mem_Icc] at hn;omega
      have hz : W ((n:ℝ)/Z)=0 := by
        by_contra hw
        have hh:=(div_le_iff₀ hZ).mp (hW _ hw)
        have hl : (D:ℝ)<n:=by exact_mod_cast hnD
        linarith
      rw [hz,mul_zero]
  have hh : HasSum (fun n : ℕ=>weightedCoeff χ S n*W ((n:ℝ)/Z))
      (∑n∈Finset.Icc 1 D,weightedCoeff χ S n*W ((n:ℝ)/Z)) :=
    hasSum_sum_of_ne_finset_zero ht
  have he:=outsideIdealSum_eq_outsideCoeff_sum S D (weightedMoebius χ)
    (fun n=>W ((n:ℝ)/Z))
  change _=(∑n∈Finset.Icc 1 D,weightedCoeff χ S n*W ((n:ℝ)/Z)) at he
  rw [←he] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro I hI
  dsimp only [weightedMoebius]
  ring

theorem ideal_weighted_hasSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (W : ℝ→ℂ) (b Z : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0→x≤b) (D : ℕ) (hD : b*Z≤D) :
    HasSum (fun I : Ideal ActualEisensteinCubic.O=>outsideWeight χ S I*W ((Ideal.absNorm I:ℝ)/Z))
      (∑I∈outsideIdealsUpTo S D,baseChangeWeight χ I*W ((Ideal.absNorm I:ℝ)/Z)*totientDensity I) := by
  have ht (I : Ideal ActualEisensteinCubic.O) (hI : I∉outsideIdealsUpTo S D) :
      outsideWeight χ S I*W ((Ideal.absNorm I:ℝ)/Z)=0 := by
    by_cases hI0 : I=0
    · rw [hI0,outsideWeight_zero,zero_mul]
    by_cases hg : ∀P∈S,¬P∣I
    · have hz : W ((Ideal.absNorm I:ℝ)/Z)=0 := by
        by_contra hn
        apply hI
        refine mem_outsideIdealsUpTo.mpr ⟨?_,?_,hg⟩
        · exact Nat.one_le_iff_ne_zero.mpr (fun hh=>hI0 (Ideal.absNorm_eq_zero_iff.mp hh))
        · exact_mod_cast ((div_le_iff₀ hZ).mp (hW _ hn)).trans hD
      rw [hz,mul_zero]
    · simp [outsideWeight,FiniteSFactor.outsideWeight,hg]
  have hh : HasSum (fun I : Ideal ActualEisensteinCubic.O=>outsideWeight χ S I*W ((Ideal.absNorm I:ℝ)/Z))
      (∑I∈outsideIdealsUpTo S D,outsideWeight χ S I*W ((Ideal.absNorm I:ℝ)/Z)) :=
    hasSum_sum_of_ne_finset_zero ht
  convert hh using 1
  apply Finset.sum_congr rfl
  intro I hI
  simp only [outsideWeight,FiniteSFactor.outsideWeight,ite_eq_left (mem_outsideIdealsUpTo.mp hI).2.2,weightedMoebius]
  ring

end

open scoped BigOperators Classical SchwartzMap ContDiff Topology
open Filter Asymptotics MeasureTheory
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open ShortDraftHeckeBridge
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalRowCompletion
open InitialMeanSquare CompactMellinBridge

def weightedCompactSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (W : ℝ→ℂ) (t : ℝ) : ℂ :=
  ∑'n : ℕ,weightedCoeff χ S n*W ((n:ℝ)*t)

theorem weightedCompactSum_hasSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (W : ℝ→ℂ)
    (hW : ∀x,2≤x→W x=0) (t : ℝ) (ht : 0<t) :
    HasSum (fun n : ℕ=>weightedCoeff χ S n*W ((n:ℝ)*t)) (weightedCompactSum χ S W t) := by
  obtain ⟨N,hN⟩:=exists_nat_gt (2/t)
  have hz (n : ℕ) (hn : n∉Finset.range N) : weightedCoeff χ S n*W ((n:ℝ)*t)=0 := by
    have hNn : N≤n:=by simpa only [Finset.mem_range,not_lt] using hn
    have htwo : 2≤(n:ℝ)*t := by
      have hh:=(div_lt_iff₀ ht).mp hN
      exact hh.le.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hNn) ht.le)
    rw [hW _ htwo,mul_zero]
  exact (summable_of_ne_finset_zero hz).hasSum

theorem weightedCompactSum_inv_eq {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (W : ℝ→ℂ) (Z b : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0→x≤b) (D : ℕ) (hD : b*Z≤D) :
    weightedCompactSum χ S W Z⁻¹=
      ∑I∈outsideIdealsUpTo S D,baseChangeWeight χ I*W ((Ideal.absNorm I:ℝ)/Z)*totientDensity I := by
  simpa only [weightedCompactSum,div_eq_mul_inv] using
    (weightedCoeff_hasSum χ S W b Z hZ hW D hD).tsum_eq

theorem weightedCompactSum_eq_ideal_tsum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (W : ℝ→ℂ) (Z b : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0→x≤b) :
    weightedCompactSum χ S W Z⁻¹=
      ∑'I : Ideal ActualEisensteinCubic.O,outsideWeight χ S I*W ((Ideal.absNorm I:ℝ)/Z) := by
  have hD : b*Z≤(⌈b*Z⌉₊:ℝ):=Nat.le_ceil _
  rw [weightedCompactSum_inv_eq χ S W Z b hZ hW _ hD,
    (ideal_weighted_hasSum χ S W b Z hZ hW _ hD).tsum_eq]

theorem weightedCompactSum_isBigO_of_theta {q₀ : ℕ}
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε : ℝ) (hε : 0<ε) :
    (fun Z : ℝ=>weightedCompactSum χ S W Z⁻¹)=O[atTop]
      (fun Z : ℝ=>Z^((23:ℝ)/24+ε)) := by
  obtain ⟨C,hC,hbound⟩:=outside_totient_moebius_bound χ S hbad hSp ρ q levelBound hρ hq hlevel hmodels
    W a b ha hs hW ε hε
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1:ℝ)] with Z hZ
  have hZp : 0<Z:=by linarith
  have hD : b*Z≤(⌈b*Z⌉₊:ℝ):=Nat.le_ceil _
  rw [weightedCompactSum_inv_eq χ S W Z b hZp (fun x hx=>(hs hx).2) _ hD,
    Real.norm_of_nonneg (Real.rpow_nonneg hZp.le _)]
  exact hbound _ Z hZ hD

theorem weightedCompactMellin_analytic_of_theta {q₀ : ℕ}
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : ∀x,x≤1 ∨ 2≤x→W x=0)
    (ε : ℝ) (hε : 0<ε) :
    AnalyticOnNhd ℂ
      (fun s : ℂ=>mellin (fun Z : ℝ=>weightedCompactSum χ S W Z⁻¹) (-s))
      {s : ℂ | (23:ℝ)/24+ε<s.re} := by
  have hf:=weightedCompactSum_hasSum χ S W (fun x hx=>hs x (Or.inr hx))
  have hlocal:=weighted_sum_inv_locallyIntegrableOn_pos (weightedCoeff χ S) W
    (weightedCompactSum χ S W) hW (fun x hx=>hs x (Or.inr hx)) hf
  have hzero:=weighted_sum_zero_near_small_D (weightedCoeff χ S) (weightedCoeff_zero χ S) W
    (weightedCompactSum χ S W) (fun x hx=>hs x (Or.inr hx)) hf
  have hsup : Function.support W⊆Set.Icc (1:ℝ) 2 := by
    intro x hx
    have h1 : 1<x:=by by_contra hh;exact hx (hs x (Or.inl (le_of_not_gt hh)))
    have h2 : x<2:=by by_contra hh;exact hx (hs x (Or.inr (le_of_not_gt hh)))
    exact ⟨h1.le,h2.le⟩
  exact ShortDraftMellin.inverse_mellin_analytic _ _ hlocal
    (weightedCompactSum_isBigO_of_theta χ S hbad hSp ρ q levelBound hρ hq hlevel hmodels
      W 1 2 (by norm_num) hsup hW ε hε) hzero

theorem weightedCompactMellin_eq_series {q₀ : ℕ}
    (χ : DirichletCharacter ℂ q₀) (S : Finset (Ideal ActualEisensteinCubic.O))
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : ∀x,x≤1 ∨ 2≤x→W x=0)
    (s : ℂ) (hRe : 2<s.re) :
    mellin (fun Z : ℝ=>weightedCompactSum χ S W Z⁻¹) (-s)=
      mellin W s*LSeries (weightedCoeff χ S) s := by
  have hls:=weightedCoeff_LSeriesSummable χ S s hRe
  exact mellin_weighted_sum (weightedCoeff χ S) W (weightedCompactSum χ S W) s
    (weightedCoeff_zero χ S) (weightedCompactSum_hasSum χ S W (fun x hx=>hs x (Or.inr hx)))
    (weighted_term_integrable _ (weightedCoeff_zero χ S) W s (compact_weight_mellin_convergent W hW hs s))
    (weighted_terms_fubini _ (weightedCoeff_zero χ S) W s hls) hls

theorem weightedCompactMellin_analytic {q₀ : ℕ}
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : ∀x,x≤1 ∨ 2≤x→W x=0) :
    AnalyticOnNhd ℂ
      (fun s : ℂ=>mellin (fun Z : ℝ=>weightedCompactSum χ S W Z⁻¹) (-s))
      {s : ℂ | (23:ℝ)/24<s.re} := by
  intro s hsRe
  have he : 0<(s.re-(23:ℝ)/24)/2:=by change (23:ℝ)/24<s.re at hsRe;linarith
  apply weightedCompactMellin_analytic_of_theta χ S hbad hSp ρ q levelBound hρ hq hlevel hmodels
    W hW hs _ he s
  change (23:ℝ)/24+(s.re-23/24)/2<s.re
  change (23:ℝ)/24<s.re at hsRe
  linarith

theorem ideal_totient_moebius_bound {q₀ : ℕ}
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
      ‖∑'I : Ideal ActualEisensteinCubic.O,outsideWeight χ S I*W ((Ideal.absNorm I:ℝ)/Z)‖≤
        C*Z^((23:ℝ)/24+ε) := by
  obtain ⟨C,hC,hbound⟩:=outside_totient_moebius_bound χ S hbad hSp ρ q levelBound hρ hq hlevel hmodels
    W a b ha hs hW ε hε
  refine ⟨C,hC,?_⟩
  intro Z hZ
  have hZp : 0<Z:=by linarith
  have hD : b*Z≤(⌈b*Z⌉₊:ℝ):=Nat.le_ceil _
  rw [(ideal_weighted_hasSum χ S W b Z hZp (fun x hx=>(hs hx).2) _ hD).tsum_eq]
  exact hbound _ Z hZ hD

end SixthPowerAverage

end

end OAI
end OAIOriginalModule0254

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.MobiusEulerCorrection
Source SHA256: 75d572e9739e36d437d021ea13f7d32e8bda8702c6dce6d02b40fa11b03d4f32
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0255


namespace OAI

noncomputable section

namespace SmoothMobiusCorrection

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

section
open ActualEisensteinCubic
open IdealMobiusDivisorSum hiding O
open UniqueFactorizationMonoid
open CanonicalRowCompletion (primeValueHom primeValueHom_prime)

abbrev PrimeIdeal := {P : Ideal ActualEisensteinCubic.O // Prime P}

def primeProduct (s : Finset PrimeIdeal) : Ideal ActualEisensteinCubic.O := ∏ P ∈ s, P.val

def primeSet (I : Ideal ActualEisensteinCubic.O) : Finset PrimeIdeal :=
  (primeSupport I).attach.image (fun P => ⟨P.val, support_prime P.property⟩)

@[simp] theorem mem_primeSet (I : Ideal ActualEisensteinCubic.O) (P : PrimeIdeal) :
    P ∈ primeSet I ↔ P.val ∈ primeSupport I := by
  simp only [primeSet, Finset.mem_image, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨Q,hQ⟩
    have hv := congrArg Subtype.val hQ
    simpa only [←hv] using Q.property
  · intro h
    exact ⟨⟨P.val,h⟩,rfl⟩

theorem primeProduct_ne_zero (s : Finset PrimeIdeal) : primeProduct s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _ => P.property.ne_zero)

theorem factors_primeProduct (s : Finset PrimeIdeal) :
    normalizedFactors (primeProduct s) = s.val.map Subtype.val := by
  have h := normalizedFactors_prod_of_prime
    (m := s.val.map (fun P : PrimeIdeal => P.val)) (by
      intro P hP
      obtain ⟨Q,hQ,rfl⟩ := Multiset.mem_map.mp hP
      exact Q.property)
  simpa only [primeProduct, Finset.prod_eq_multiset_prod] using h

theorem primeSet_primeProduct (s : Finset PrimeIdeal) : primeSet (primeProduct s) = s := by
  ext P
  rw [mem_primeSet]
  simp only [primeSupport, factors_primeProduct, Multiset.mem_toFinset,
    Multiset.mem_map, Finset.mem_val]
  constructor
  · rintro ⟨Q,hQ,he⟩
    have : Q=P := Subtype.ext he
    simpa [this] using hQ
  · intro h
    exact ⟨P,h,rfl⟩

theorem primeProduct_injective : Function.Injective primeProduct := by
  intro s t h
  simpa only [primeSet_primeProduct] using congrArg primeSet h

theorem primeProduct_squarefree (s : Finset PrimeIdeal) : Squarefree (primeProduct s) := by
  rw [squarefree_iff_nodup_normalizedFactors (primeProduct_ne_zero s),factors_primeProduct]
  exact s.nodup.map Subtype.val_injective

theorem primeProduct_primeSet (I : Ideal ActualEisensteinCubic.O) (hI : Squarefree I) :
    primeProduct (primeSet I) = I := by
  unfold primeProduct primeSet
  rw [Finset.prod_image]
  · change (∏ P ∈ (primeSupport I).attach, (fun Q : Ideal ActualEisensteinCubic.O => Q) P.val) = I
    exact (Finset.prod_attach (primeSupport I) (fun Q : Ideal ActualEisensteinCubic.O => Q)).trans
      (squarefree_support_product_self hI)
  · intro P hP Q hQ he
    exact Subtype.ext (congrArg (fun R : PrimeIdeal => R.val) he)

def mobiusPrimeCoeff (w : Ideal ActualEisensteinCubic.O → ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  (moebius I : ℂ) * primeValueHom w I

theorem mobiusPrimeCoeff_nonsquarefree (w : Ideal ActualEisensteinCubic.O → ℂ) (I : Ideal ActualEisensteinCubic.O)
    (hI : ¬Squarefree I) : mobiusPrimeCoeff w I=0 := by
  simp [mobiusPrimeCoeff,moebius_of_not_squarefree hI]

theorem mobiusPrimeCoeff_primeProduct (w : Ideal ActualEisensteinCubic.O → ℂ) (s : Finset PrimeIdeal) :
    mobiusPrimeCoeff w (primeProduct s) = ∏ P ∈ s, -w P.val := by
  have hm : (moebius (primeProduct s) : ℂ)=(-1:ℂ)^s.card := by
    rw [(primeProduct_squarefree s).moebius_eq,factors_eq_normalizedFactors,
      factors_primeProduct]
    simp
  rw [mobiusPrimeCoeff,hm]
  simp only [primeProduct,map_prod,primeValueHom_prime _ _ (Subtype.property _)]
  rw [Finset.prod_neg]

theorem mobiusPrimeCoeff_tsum (w : Ideal ActualEisensteinCubic.O → ℂ) :
    (∑' I : Ideal ActualEisensteinCubic.O, mobiusPrimeCoeff w I) =
      ∑' s : Finset PrimeIdeal, ∏ P ∈ s, -w P.val := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun s => primeProduct s.val)
  · exact primeProduct_injective.comp Subtype.val_injective
  · intro I hI
    have hs : Squarefree I := by
      by_contra hs
      exact hI (mobiusPrimeCoeff_nonsquarefree w I hs)
    have hp : (∏ P ∈ primeSet I, -w P.val) ≠ 0 := by
      rw [←mobiusPrimeCoeff_primeProduct,primeProduct_primeSet I hs]
      exact hI
    exact ⟨⟨primeSet I,hp⟩,primeProduct_primeSet I hs⟩
  · intro s
    exact mobiusPrimeCoeff_primeProduct w s.val

theorem mobiusPrimeCoeff_euler (w : Ideal ActualEisensteinCubic.O → ℂ)
    (hw : Summable (fun P : PrimeIdeal => ‖w P.val‖)) :
    (∑' I : Ideal ActualEisensteinCubic.O, mobiusPrimeCoeff w I) =
      ∏' P : PrimeIdeal, (1-w P.val) := by
  rw [mobiusPrimeCoeff_tsum]
  have hs : Summable (fun P : PrimeIdeal => ‖-w P.val‖) := by simpa using hw
  simpa only [sub_eq_add_neg] using
    (tprod_one_add (summable_finsetProd_of_summable_norm hs)).symm

end

section
open ActualEisensteinCubic
open Filter

lemma prime_norm_two_le (P : PrimeIdeal) : 2 ≤ Ideal.absNorm P.val := by
  have h0 : Ideal.absNorm P.val ≠ 0 := fun h => P.property.ne_zero (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm P.val ≠ 1 := by
    intro h
    apply P.property.not_isUnit
    rw [Ideal.absNorm_eq_one_iff.mp h]
    simpa only [Ideal.one_eq_top] using (show IsUnit (1 : Ideal ActualEisensteinCubic.O) from isUnit_one)
  omega

lemma prime_norm_pos (P : PrimeIdeal) : (0 : ℝ) < Ideal.absNorm P.val := by
  have h := prime_norm_two_le P
  exact_mod_cast (by omega : 0 < Ideal.absNorm P.val)

def primeNormPower (P : PrimeIdeal) (s : ℂ) : ℂ := (Ideal.absNorm P.val : ℂ)^(-s)

def primeCharacterTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (P : PrimeIdeal) (s : ℂ) : ℂ :=
  χ (Ideal.absNorm P.val) * primeNormPower P s

def primeDensity (P : PrimeIdeal) : ℂ := 1-(1:ℂ)/(Ideal.absNorm P.val:ℂ)

lemma norm_primeNormPower (P : PrimeIdeal) (s : ℂ) :
    ‖primeNormPower P s‖=(Ideal.absNorm P.val : ℝ)^(-s.re) := by
  exact Complex.norm_cpow_eq_rpow_re_of_pos (prime_norm_pos P) (-s)

lemma primeDensity_norm_le_one (P : PrimeIdeal) : ‖primeDensity P‖≤1 := by
  have hn := prime_norm_pos P
  have hn1 : (1:ℝ)≤Ideal.absNorm P.val := by exact_mod_cast (by have:=prime_norm_two_le P;omega)
  have he : primeDensity P = ((1-(1:ℝ)/(Ideal.absNorm P.val:ℝ):ℝ):ℂ) := by
    simp [primeDensity]
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
  · have : (0:ℝ)≤1/(Ideal.absNorm P.val:ℝ) := by positivity
    linarith
  · exact sub_nonneg.mpr ((div_le_one hn).mpr hn1)

lemma primeCharacterTerm_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) (P : PrimeIdeal)
    (s : ℂ) (σ : ℝ) (hs : σ≤s.re) :
    ‖primeCharacterTerm χ P s‖≤(Ideal.absNorm P.val:ℝ)^(-σ) := by
  rw [primeCharacterTerm,norm_mul,norm_primeNormPower]
  have hn1 : (1:ℝ)≤Ideal.absNorm P.val := by exact_mod_cast (by have:=prime_norm_two_le P;omega)
  calc
    _ ≤ 1*(Ideal.absNorm P.val:ℝ)^(-s.re) :=
      mul_le_mul_of_nonneg_right (χ.norm_le_one _) (by positivity)
    _ ≤ _ := by rw [one_mul]; exact Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hs)

lemma primeCharacterTerm_norm_lt_one {q : ℕ} (χ : DirichletCharacter ℂ q) (P : PrimeIdeal)
    (s : ℂ) (hs : 0<s.re) : ‖primeCharacterTerm χ P s‖<1 := by
  apply (primeCharacterTerm_norm_le χ P s s.re le_rfl).trans_lt
  exact Real.rpow_lt_one_of_one_lt_of_neg (by have:=prime_norm_two_le P;exact_mod_cast (by omega:1<Ideal.absNorm P.val)) (by linarith)

lemma one_sub_ne_zero {x : ℂ} (hx : ‖x‖<1) : 1-x≠0 := by
  intro h
  have he : x=1 := (sub_eq_zero.mp h).symm
  simp [he] at hx

lemma correctionDenominator_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q) (P : PrimeIdeal)
    (s : ℂ) (hs : 0<s.re) : 1-primeDensity P*primeCharacterTerm χ P s≠0 := by
  apply one_sub_ne_zero
  rw [norm_mul]
  calc
    _ ≤ 1*‖primeCharacterTerm χ P s‖ :=
      mul_le_mul_of_nonneg_right (primeDensity_norm_le_one P) (norm_nonneg _)
    _ < 1 := by rw [one_mul];exact primeCharacterTerm_norm_lt_one χ P s hs

def correctionTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) : ℂ :=
  if P.val∈S then 0 else
    -((1:ℂ)/(Ideal.absNorm P.val:ℂ))*primeCharacterTerm χ P s /
      (1-primeDensity P*primeCharacterTerm χ P s)

def eulerCorrection {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O)) (s : ℂ) : ℂ :=
  ∏' P : PrimeIdeal, (1+correctionTerm χ S P s)

lemma correctionTerm_factor {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) (hs : 0<s.re) :
    1+correctionTerm χ S P s =
      if P.val∈S then 1 else (1-primeCharacterTerm χ P s)/(1-primeDensity P*primeCharacterTerm χ P s) := by
  by_cases hP : P.val∈S
  · simp [correctionTerm,hP]
  · simp only [correctionTerm,ite_eq_right hP]
    have hd := correctionDenominator_ne_zero χ P s hs
    apply (eq_div_iff hd).mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ hd]
    dsimp [primeDensity]
    ring

lemma correctionFactor_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) (hs : 0<s.re) : 1+correctionTerm χ S P s≠0 := by
  rw [correctionTerm_factor χ S P s hs]
  split_ifs
  · exact one_ne_zero
  · exact div_ne_zero (one_sub_ne_zero (primeCharacterTerm_norm_lt_one χ P s hs))
      (correctionDenominator_ne_zero χ P s hs)

lemma correctionTerm_uniform_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (σ : ℝ) (hσ : 0<σ) (P : PrimeIdeal) (s : ℂ) (hs : σ≤s.re) :
    ‖correctionTerm χ S P s‖ ≤
      (1-(2:ℝ)^(-σ))⁻¹*(Ideal.absNorm P.val:ℝ)^(-(1+σ)) := by
  have hn := prime_norm_pos P
  have hn2 : (2:ℝ)≤Ideal.absNorm P.val := by exact_mod_cast prime_norm_two_le P
  have hr : (2:ℝ)^(-σ)<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hr0 : 0<1-(2:ℝ)^(-σ) := sub_pos.mpr hr
  have hx := primeCharacterTerm_norm_le χ P s σ hs
  have hx2 : ‖primeCharacterTerm χ P s‖≤(2:ℝ)^(-σ) := hx.trans
    (Real.rpow_le_rpow_of_nonpos (by norm_num) hn2 (by linarith))
  have hd : 1-(2:ℝ)^(-σ)≤‖1-primeDensity P*primeCharacterTerm χ P s‖ := by
    have hb : ‖primeDensity P*primeCharacterTerm χ P s‖≤(2:ℝ)^(-σ) := by
      rw [norm_mul]
      calc
        _ ≤ 1*‖primeCharacterTerm χ P s‖ :=
          mul_le_mul_of_nonneg_right (primeDensity_norm_le_one P) (norm_nonneg _)
        _ ≤ _ := by simpa using hx2
    have hh := norm_sub_norm_le (1:ℂ) (primeDensity P*primeCharacterTerm χ P s)
    simpa only [norm_one] using (show 1-(2:ℝ)^(-σ) ≤ ‖(1:ℂ)‖-‖primeDensity P*primeCharacterTerm χ P s‖ from by simpa using sub_le_sub_left hb 1) |>.trans hh
  by_cases hP : P.val∈S
  · simp only [correctionTerm,ite_eq_left hP,norm_zero]
    positivity
  · rw [correctionTerm,ite_eq_right hP,norm_div,norm_mul,norm_neg,norm_div,norm_one,Complex.norm_natCast]
    calc
      _ ≤ ((1:ℝ)/(Ideal.absNorm P.val:ℝ)*(Ideal.absNorm P.val:ℝ)^(-σ))/(1-(2:ℝ)^(-σ)) :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hx (by positivity)) hr0 hd
      _ = _ := by
        rw [show -(1+σ)=(-1)+(-σ) by ring,Real.rpow_add hn,Real.rpow_neg_one]
        ring

lemma prime_norm_series_summable (σ : ℝ) (hσ : 0<σ) :
    Summable (fun P : PrimeIdeal => (Ideal.absNorm P.val:ℝ)^(-(1+σ))) := by
  have ht := (CubicEisenstein.fullIdealWeight_summable_norm (1+(σ:ℂ)) (by simp;linarith)).comp_injective
    (i := fun P : PrimeIdeal => P.val) Subtype.val_injective
  apply ht.congr
  intro P
  simp only [Function.comp_def,CubicEisenstein.fullIdealWeight,ite_eq_right P.property.ne_zero]
  simpa only [Complex.neg_re, Complex.add_re, Complex.one_re, Complex.ofReal_re,
    Complex.ofReal_natCast] using
    (Complex.norm_cpow_eq_rpow_re_of_pos (prime_norm_pos P) (-(1+(σ:ℂ))))

lemma correctionTerm_summable {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (hs : 0<s.re) : Summable (fun P : PrimeIdeal => ‖correctionTerm χ S P s‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun P => correctionTerm_uniform_bound χ S s.re hs P s le_rfl)
  exact (prime_norm_series_summable s.re hs).mul_left _

theorem eulerCorrection_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (hs : 0<s.re) : eulerCorrection χ S s≠0 :=
  tprod_one_add_ne_zero_of_summable (fun P => correctionFactor_ne_zero χ S P s hs)
    (correctionTerm_summable χ S s hs)

lemma primeCharacterTerm_differentiable {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : PrimeIdeal) : Differentiable ℂ (primeCharacterTerm χ P) := by
  have hn : (Ideal.absNorm P.val:ℂ)≠0 := by
    exact_mod_cast (ne_of_gt (prime_norm_pos P))
  exact ((differentiable_id.neg).const_cpow (Or.inl hn)).const_mul _

lemma correctionTerm_differentiableOn {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (P : PrimeIdeal) (σ : ℝ) (hσ : 0≤σ) :
    DifferentiableOn ℂ (correctionTerm χ S P) {s:ℂ | σ<s.re} := by
  unfold correctionTerm
  by_cases hP : P.val∈S
  · simpa only [ite_eq_left hP] using (differentiableOn_const (𝕜 := ℂ) (s := {s:ℂ | σ<s.re}) (c := (0:ℂ)))
  · simp only [ite_eq_right hP]
    intro s hs
    have hx := primeCharacterTerm_differentiable χ P s
    convert ((hx.const_mul (-((1:ℂ)/(Ideal.absNorm P.val:ℂ)))).div
      ((differentiableAt_const (1:ℂ)).sub (hx.const_mul (primeDensity P)))
      (correctionDenominator_ne_zero χ P s (lt_of_le_of_lt hσ hs))).differentiableWithinAt using 1

lemma eulerCorrection_locally_uniform {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (σ : ℝ) (hσ : 0<σ) :
    HasProdLocallyUniformlyOn (fun P s => 1+correctionTerm χ S P s)
      (eulerCorrection χ S) {s:ℂ | σ<s.re} := by
  have hu := (prime_norm_series_summable σ hσ).mul_left ((1-(2:ℝ)^(-σ))⁻¹)
  exact hu.hasProdLocallyUniformlyOn_one_add
    (isOpen_lt continuous_const Complex.continuous_re)
    (Filter.Eventually.of_forall (fun P s hs => correctionTerm_uniform_bound χ S σ hσ P s hs.le))
    (fun P => (correctionTerm_differentiableOn χ S P σ hσ.le).continuousOn)

theorem eulerCorrection_differentiableOn_halfplane {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (σ : ℝ) (hσ : 0<σ) :
    DifferentiableOn ℂ (eulerCorrection χ S) {s:ℂ | σ<s.re} := by
  apply (eulerCorrection_locally_uniform χ S σ hσ).differentiableOn
  · apply Filter.Eventually.of_forall
    intro t
    change DifferentiableOn ℂ (fun z => ∏ P ∈ t, (1+correctionTerm χ S P z)) _
    apply DifferentiableOn.fun_finsetProd
    intro P hP
    exact (differentiableOn_const (𝕜 := ℂ) (c := (1:ℂ))).add
      (correctionTerm_differentiableOn χ S P σ hσ.le)
  · exact isOpen_lt continuous_const Complex.continuous_re

theorem eulerCorrection_differentiableOn {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) : DifferentiableOn ℂ (eulerCorrection χ S) {s:ℂ | 0<s.re} := by
  intro s hs
  have hh := eulerCorrection_differentiableOn_halfplane χ S (s.re/2) (by dsimp at hs;linarith)
  exact (hh.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show s∈{z:ℂ | s.re/2<z.re} by dsimp at *;linarith))).differentiableWithinAt

end

section
open ActualEisensteinCubic
open ShortDraftHeckeBridge hiding O
open IdealMobiusDivisorSum hiding O
open UniqueFactorizationMonoid
open CanonicalRowCompletion (primeValueHom primeValueHom_prime)

lemma prod_primeSet {M : Type*} [CommMonoid M] (I : Ideal ActualEisensteinCubic.O) (f : Ideal ActualEisensteinCubic.O→M) :
    (∏P∈primeSet I,f P.val)=∏P∈primeSupport I,f P := by
  unfold primeSet
  rw [Finset.prod_image]
  · exact Finset.prod_attach (primeSupport I) f
  · intro P hP Q hQ he
    exact Subtype.ext (congrArg (fun R : PrimeIdeal => R.val) he)

lemma primeValueHom_squarefree (w : Ideal ActualEisensteinCubic.O→ℂ) (I : Ideal ActualEisensteinCubic.O) (hI : Squarefree I) :
    primeValueHom w I=∏P∈primeSet I,w P.val := by
  calc
    _ = primeValueHom w (primeProduct (primeSet I)) :=
      congrArg (primeValueHom w) (primeProduct_primeSet I hI).symm
    _ = _ := by simp only [primeProduct,map_prod,primeValueHom_prime _ _ (Subtype.property _)]

lemma outside_primeProduct_iff (S : Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀P∈S,Prime P)
    (t : Finset PrimeIdeal) :
    (∀P∈S,¬P∣primeProduct t) ↔ ∀Q∈t,Q.val∉S := by
  constructor
  · intro h Q hQ hQS
    apply h Q.val hQS
    exact Finset.dvd_prod_of_mem (fun P : PrimeIdeal => P.val) hQ
  · intro h P hP hd
    obtain ⟨Q,hQ,hPQ⟩ := ((hS P hP).dvd_finsetProd_iff (fun Q : PrimeIdeal => Q.val)).mp hd
    have he : P=Q.val := associated_iff_eq.mp (((hS P hP).dvd_prime_iff_associated Q.property).mp hPQ)
    exact h Q hQ (he ▸ hP)

def outsideMask (S : Finset (Ideal ActualEisensteinCubic.O)) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  if ∀P∈S,¬P∣I then 1 else 0

lemma prod_cut_primes (S : Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀P∈S,Prime P)
    (t : Finset PrimeIdeal) (f : Ideal ActualEisensteinCubic.O→ℂ) :
    (∏Q∈t,if Q.val∈S then 0 else f Q.val)=outsideMask S (primeProduct t)*(∏Q∈t,f Q.val) := by
  by_cases ho : ∀P∈S,¬P∣primeProduct t
  · rw [outsideMask,ite_eq_left ho,one_mul]
    apply Finset.prod_congr rfl
    intro Q hQ
    exact ite_eq_right ((outside_primeProduct_iff S hS t).mp ho Q hQ)
  · rw [outsideMask,ite_eq_right ho,zero_mul]
    have hh : ¬∀Q∈t,Q.val∉S := fun h => ho ((outside_primeProduct_iff S hS t).mpr h)
    push Not at hh
    obtain ⟨Q,hQ,hQS⟩ := hh
    exact Finset.prod_eq_zero hQ (ite_eq_left hQS)

lemma nat_cpow_prod {ι : Type*} (t : Finset ι) (N : ι→ℕ) (s : ℂ) :
    ((∏i∈t,N i : ℕ):ℂ)^s=∏i∈t,(N i:ℂ)^s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    rw [Finset.prod_insert hi,Finset.prod_insert hi,Nat.cast_mul,Complex.natCast_mul_natCast_cpow,ih]

lemma primeNormTerm_prod {q : ℕ} (χ : DirichletCharacter ℂ q) (t : Finset PrimeIdeal) (s : ℂ) :
    (∏P∈t,χ (Ideal.absNorm P.val)*(Ideal.absNorm P.val:ℂ)^(-s))=
      χ (Ideal.absNorm (primeProduct t))*(Ideal.absNorm (primeProduct t):ℂ)^(-s) := by
  rw [Finset.prod_mul_distrib]
  simp only [primeProduct,map_prod,Nat.cast_prod]
  congr 1
  simpa only [Nat.cast_prod] using (nat_cpow_prod t (fun P=>Ideal.absNorm P.val) (-s)).symm

def ordinaryPrimeValue {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  if I∈S then 0 else χ (Ideal.absNorm I)*(Ideal.absNorm I:ℂ)^(-s)

def dampedPrimeValue {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  if I∈S then 0 else (1-(1:ℂ)/(Ideal.absNorm I:ℂ))*(χ (Ideal.absNorm I)*(Ideal.absNorm I:ℂ)^(-s))

def ordinarySeriesTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  outsideMask S I * baseChangeWeight χ I * CubicEisenstein.fullIdealWeight s I

def dampedSeriesTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  ordinarySeriesTerm χ S s I * SixthPowerAverage.totientDensity I

lemma ordinarySeriesTerm_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (hS : ∀P∈S,Prime P) (s : ℂ) (I : Ideal ActualEisensteinCubic.O) :
    ordinarySeriesTerm χ S s I = mobiusPrimeCoeff (ordinaryPrimeValue χ S s) I := by
  by_cases hI : Squarefree I
  · rw [mobiusPrimeCoeff,primeValueHom_squarefree _ I hI]
    simp only [ordinaryPrimeValue]
    rw [prod_cut_primes S hS (primeSet I) (fun P => χ (Ideal.absNorm P)*(Ideal.absNorm P:ℂ)^(-s)),
      primeNormTerm_prod,primeProduct_primeSet I hI]
    simp only [ordinarySeriesTerm,baseChangeWeight,CubicEisenstein.fullIdealWeight,ite_eq_right hI.ne_zero]
    ring
  · simp [ordinarySeriesTerm,baseChangeWeight,mobiusPrimeCoeff_nonsquarefree _ I hI,
      moebius_of_not_squarefree hI]

lemma dampedSeriesTerm_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (hS : ∀P∈S,Prime P) (s : ℂ) (I : Ideal ActualEisensteinCubic.O) :
    dampedSeriesTerm χ S s I = mobiusPrimeCoeff (dampedPrimeValue χ S s) I := by
  by_cases hI : Squarefree I
  · rw [mobiusPrimeCoeff,primeValueHom_squarefree _ I hI]
    simp only [dampedPrimeValue]
    rw [prod_cut_primes S hS (primeSet I) (fun P => (1-(1:ℂ)/(Ideal.absNorm P:ℂ))*(χ (Ideal.absNorm P)*(Ideal.absNorm P:ℂ)^(-s))),
      Finset.prod_mul_distrib,primeNormTerm_prod,
      prod_primeSet I (fun P => (1-(1:ℂ)/(Ideal.absNorm P:ℂ))),
      primeProduct_primeSet I hI]
    simp only [dampedSeriesTerm,ordinarySeriesTerm,baseChangeWeight,SixthPowerAverage.totientDensity,
      CubicEisenstein.fullIdealWeight,ite_eq_right hI.ne_zero]
    ring
  · simp [dampedSeriesTerm,ordinarySeriesTerm,baseChangeWeight,mobiusPrimeCoeff_nonsquarefree _ I hI,
      moebius_of_not_squarefree hI]

end

open ActualEisensteinCubic

lemma ordinaryPrimeValue_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) :
    ‖ordinaryPrimeValue χ S s P.val‖≤(Ideal.absNorm P.val:ℝ)^(-s.re) := by
  by_cases hP : P.val∈S
  · simp only [ordinaryPrimeValue,ite_eq_left hP,norm_zero]
    positivity
  · simpa only [ordinaryPrimeValue,ite_eq_right hP,primeCharacterTerm,primeNormPower] using
      primeCharacterTerm_norm_le χ P s s.re le_rfl

lemma dampedPrimeValue_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) :
    ‖dampedPrimeValue χ S s P.val‖≤(Ideal.absNorm P.val:ℝ)^(-s.re) := by
  by_cases hP : P.val∈S
  · simp only [dampedPrimeValue,ite_eq_left hP,norm_zero]
    positivity
  · change ‖if P.val∈S then 0 else primeDensity P*primeCharacterTerm χ P s‖≤_
    rw [ite_eq_right hP,norm_mul]
    exact (mul_le_mul_of_nonneg_right (primeDensity_norm_le_one P) (norm_nonneg _)).trans
      (by simpa using primeCharacterTerm_norm_le χ P s s.re le_rfl)

lemma prime_reciprocal_series_summable (s : ℂ) (hs : 1<s.re) :
    Summable (fun P : PrimeIdeal => (Ideal.absNorm P.val:ℝ)^(-s.re)) := by
  have hh := prime_norm_series_summable (s.re-1) (by linarith)
  simpa only [show 1+(s.re-1)=s.re by ring] using hh

lemma ordinaryPrimeValue_summable {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (hs : 1<s.re) : Summable (fun P : PrimeIdeal => ‖ordinaryPrimeValue χ S s P.val‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun P => ordinaryPrimeValue_norm_le χ S P s) (prime_reciprocal_series_summable s hs)

lemma dampedPrimeValue_summable {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (hs : 1<s.re) : Summable (fun P : PrimeIdeal => ‖dampedPrimeValue χ S s P.val‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun P => dampedPrimeValue_norm_le χ S P s) (prime_reciprocal_series_summable s hs)

lemma ordinarySeries_euler {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (hS : ∀P∈S,Prime P) (s : ℂ) (hs : 1<s.re) :
    (∑'I : Ideal ActualEisensteinCubic.O,ordinarySeriesTerm χ S s I)=
      ∏'P : PrimeIdeal,(1-ordinaryPrimeValue χ S s P.val) := by
  simp_rw [ordinarySeriesTerm_eq χ S hS]
  exact mobiusPrimeCoeff_euler _ (ordinaryPrimeValue_summable χ S s hs)

lemma dampedSeries_euler {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (hS : ∀P∈S,Prime P) (s : ℂ) (hs : 1<s.re) :
    (∑'I : Ideal ActualEisensteinCubic.O,dampedSeriesTerm χ S s I)=
      ∏'P : PrimeIdeal,(1-dampedPrimeValue χ S s P.val) := by
  simp_rw [dampedSeriesTerm_eq χ S hS]
  exact mobiusPrimeCoeff_euler _ (dampedPrimeValue_summable χ S s hs)

lemma local_correction_identity {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) (hs : 0<s.re) :
    (1-dampedPrimeValue χ S s P.val)*(1+correctionTerm χ S P s)=
      1-ordinaryPrimeValue χ S s P.val := by
  rw [correctionTerm_factor χ S P s hs]
  by_cases hP : P.val∈S
  · simp [dampedPrimeValue,ordinaryPrimeValue,hP]
  · simp only [dampedPrimeValue,ordinaryPrimeValue,ite_eq_right hP]
    change (1-primeDensity P*primeCharacterTerm χ P s)*
      ((1-primeCharacterTerm χ P s)/(1-primeDensity P*primeCharacterTerm χ P s))=
      1-primeCharacterTerm χ P s
    exact mul_div_cancel₀ _ (correctionDenominator_ne_zero χ P s hs)

theorem actual_dirichlet_correction {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀P∈S,Prime P) (s : ℂ) (hs : 1<s.re) :
    (∑'I : Ideal ActualEisensteinCubic.O,ordinarySeriesTerm χ S s I)=
      eulerCorrection χ S s*(∑'I : Ideal ActualEisensteinCubic.O,dampedSeriesTerm χ S s I) := by
  rw [ordinarySeries_euler χ S hS s hs,dampedSeries_euler χ S hS s hs,mul_comm]
  have hd : Multipliable (fun P : PrimeIdeal => 1-dampedPrimeValue χ S s P.val) := by
    simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable
      (show Summable (fun P : PrimeIdeal => ‖-dampedPrimeValue χ S s P.val‖) by
        simpa only [norm_neg] using dampedPrimeValue_summable χ S s hs)
  have hc := multipliable_one_add_of_summable (correctionTerm_summable χ S s (by linarith))
  change _ = (∏' P : PrimeIdeal, (1-dampedPrimeValue χ S s P.val))*(∏' P : PrimeIdeal, (1+correctionTerm χ S P s))
  rw [←hd.tprod_mul hc]
  apply tprod_congr
  intro P
  exact (local_correction_identity χ S P s (by linarith)).symm

open scoped BigOperators Classical
open ActualEisensteinCubic
open ShortDraftHeckeBridge hiding O

lemma normFiber_tsum (a : Ideal ActualEisensteinCubic.O→ℂ) (n : ℕ) :
    (∑'I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n},a I.val)=normFiberCoeff a n := by
  let : Fintype {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n} :=
    (Ideal.finite_setOfPred_absNorm_eq (S := ActualEisensteinCubic.O) n).fintype
  rw [tsum_fintype]
  symm
  change (∑I∈FiniteSFactor.fiber n,a I)=_
  apply Finset.sum_bij (fun I hI => (⟨I,FiniteSFactor.mem_fiber.mp hI⟩ : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n}))
  · intro I hI
    exact Finset.mem_univ _
  · intro I hI J hJ he
    exact congrArg Subtype.val he
  · intro I hI
    exact ⟨I.val,FiniteSFactor.mem_fiber.mpr I.property,rfl⟩
  · intro I hI
    rfl

lemma idealDirichlet_fiber (a : Ideal ActualEisensteinCubic.O→ℂ) (s : ℂ) (n : ℕ) :
    (∑'I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n},a I.val*CubicEisenstein.fullIdealWeight s I.val)=
      LSeries.term (normFiberCoeff a) s n := by
  by_cases hn : n=0
  · subst n
    have hz (I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=0}) : CubicEisenstein.fullIdealWeight s I.val=0 := by
      have hI : I.val=0 := Ideal.absNorm_eq_zero_iff.mp I.property
      simp [CubicEisenstein.fullIdealWeight,hI]
    simp only [hz,mul_zero,tsum_zero,LSeries.term_zero]
  · have ht (I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n}) :
        CubicEisenstein.fullIdealWeight s I.val=(n:ℂ)^(-s) := by
      have hI : I.val≠0 := fun h => hn (by rw [←I.property,h,map_zero])
      rw [CubicEisenstein.fullIdealWeight,ite_eq_right hI,I.property]
    simp_rw [ht]
    rw [tsum_mul_right,normFiber_tsum,LSeries.term_of_ne_zero hn,Complex.cpow_neg,div_eq_mul_inv]

lemma idealDirichlet_summable (a : Ideal ActualEisensteinCubic.O→ℂ) (ha : ∀I,‖a I‖≤1) (s : ℂ) (hs : 1<s.re) :
    Summable (fun I : Ideal ActualEisensteinCubic.O => a I*CubicEisenstein.fullIdealWeight s I) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun I => ?_) (CubicEisenstein.fullIdealWeight_summable_norm s hs)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha I)

theorem idealDirichlet_eq_LSeries (a : Ideal ActualEisensteinCubic.O→ℂ) (ha : ∀I,‖a I‖≤1)
    (s : ℂ) (hs : 1<s.re) :
    (∑'I : Ideal ActualEisensteinCubic.O,a I*CubicEisenstein.fullIdealWeight s I)=LSeries (normFiberCoeff a) s := by
  have hh := (idealDirichlet_summable a ha s hs).hasSum.tsum_fiberwise Ideal.absNorm
  change HasSum (fun n : ℕ => ∑'I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n},
    a I.val*CubicEisenstein.fullIdealWeight s I.val) _ at hh
  simp_rw [idealDirichlet_fiber] at hh
  exact hh.tsum_eq.symm

lemma ordinarySeriesTerm_outside {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : ordinarySeriesTerm χ S s I=
      FiniteSFactor.outsideWeight S (baseChangeWeight χ) I*CubicEisenstein.fullIdealWeight s I := by
  unfold ordinarySeriesTerm outsideMask FiniteSFactor.outsideWeight
  split_ifs <;> simp

lemma dampedSeriesTerm_outside {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : dampedSeriesTerm χ S s I=
      SixthPowerAverage.outsideWeight χ S I*CubicEisenstein.fullIdealWeight s I := by
  unfold dampedSeriesTerm ordinarySeriesTerm outsideMask SixthPowerAverage.outsideWeight
    FiniteSFactor.outsideWeight SixthPowerAverage.weightedMoebius
  split_ifs <;> ring

lemma ordinarySeries_eq_LSeries {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (hs : 1<s.re) : (∑'I : Ideal ActualEisensteinCubic.O,ordinarySeriesTerm χ S s I)=
      LSeries (FiniteSFactor.outsideCoeff S (baseChangeWeight χ)) s := by
  simp_rw [ordinarySeriesTerm_outside]
  apply idealDirichlet_eq_LSeries
  intro I
  unfold FiniteSFactor.outsideWeight
  split_ifs
  · exact ConcretePrimeRowBridge.baseChangeWeight_norm_le_one χ I
  · simp
  exact hs

lemma dampedSeries_eq_LSeries {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (hs : 1<s.re) : (∑'I : Ideal ActualEisensteinCubic.O,dampedSeriesTerm χ S s I)=
      LSeries (SixthPowerAverage.weightedCoeff χ S) s := by
  simp_rw [dampedSeriesTerm_outside]
  exact idealDirichlet_eq_LSeries _ (SixthPowerAverage.outsideWeight_norm_le_one χ S) s hs

theorem actual_LSeries_correction {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀P∈S,Prime P) (s : ℂ) (hs : 1<s.re) :
    LSeries (FiniteSFactor.outsideCoeff S (baseChangeWeight χ)) s=
      eulerCorrection χ S s*LSeries (SixthPowerAverage.weightedCoeff χ S) s := by
  rw [←ordinarySeries_eq_LSeries χ S s hs,←dampedSeries_eq_LSeries χ S s hs]
  exact actual_dirichlet_correction χ S hS s hs

theorem full_LSeries_correction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀P∈S,Prime P) (s : ℂ) (hs : 2<s.re) :
    LSeries (normFiberCoeff (baseChangeWeight χ)) s=
      (CompactMellinBridge.finiteEulerFactor χ S s*eulerCorrection χ S s)*
        LSeries (SixthPowerAverage.weightedCoeff χ S) s := by
  rw [FiniteSFactor.normFiberLSeries_finiteEuler_baseChange χ S hS s hs,
    actual_LSeries_correction χ S hS s (by linarith)]
  exact (mul_assoc _ _ _).symm

theorem eulerCorrection_analytic {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O)) :
    AnalyticOnNhd ℂ (eulerCorrection χ S) {s : ℂ | 0<s.re} :=
  (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).mpr
    (eulerCorrection_differentiableOn χ S)

end SmoothMobiusCorrection

end

end OAI
end OAIOriginalModule0255

/-! Original module: OAI.NumberTheory.DirichletL.RowCompletion.ThetaNonvanishing
Source SHA256: 8027e02d12f871c42b640534070cd18383f5fbfb433a07a7a269eea692ccbe43
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0256


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

open scoped BigOperators Classical ContDiff Topology
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open ShortDraftHeckeBridge
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open SixthPowerAverage CompactMellinBridge InitialMeanSquare

theorem corrected_weighted_mellin_identity {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (hS : ∀P∈S,Prime P) (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : ∀x,x≤1 ∨ 2≤x→W x=0) (s : ℂ) (hRe : 2<s.re) :
    (χ.LFunction s*(baseChangeChar χ).LFunction s)*
      ((finiteEulerFactor χ S s*SmoothMobiusCorrection.eulerCorrection χ S s)*
        mellin (fun Z : ℝ=>weightedCompactSum χ S W Z⁻¹) (-s))=
      mellin W s := by
  rw [weightedCompactMellin_eq_series χ S W hW hs s hRe]
  have hc:=SmoothMobiusCorrection.full_LSeries_correction χ S hS s hRe
  have hp:=normFiber_LSeries_eq_pair_inverse χ (baseChangeChar χ) (baseChangeWeight χ)
    (normFiberCoeff_baseChange_eq_pairInverseCoeff χ) s
  have he:=pair_inverse_euler_identity χ (baseChangeChar χ) s (by linarith : 1<s.re)
  rw [←hp,hc] at he
  calc
    _=((χ.LFunction s*(baseChangeChar χ).LFunction s)*
      ((finiteEulerFactor χ S s*SmoothMobiusCorrection.eulerCorrection χ S s)*
        LSeries (weightedCoeff χ S) s))*mellin W s := by ring
    _=mellin W s := by rw [he,one_mul]

theorem dirichlet_open_strip_of_theta_models {q₀ : ℕ} [NeZero q₀]
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound)
    (z : ℂ) (hz : (23:ℝ)/24<z.re) (hz1 : z.re<1) : χ.LFunction z≠0 := by
  let W : ℝ→ℂ:=ConcreteCompactWeight.weight z
  have hW : ContDiff ℝ ∞ W:=ConcreteCompactWeight.weight_smooth z
  have hWs : ∀x,x≤1 ∨ 2≤x→W x=0:=ConcreteCompactWeight.weight_support z
  have hM:=weightedCompactMellin_analytic χ S hbad hSp ρ q levelBound hρ hq hlevel hmodels W hW hWs
  have hE:=finiteEulerFactor_analytic χ S hSp ((23:ℝ)/24)
  have hH : AnalyticOnNhd ℂ (SmoothMobiusCorrection.eulerCorrection χ S)
      {s : ℂ | (23:ℝ)/24<s.re} :=
    (SmoothMobiusCorrection.eulerCorrection_analytic χ S).mono (by intro s hs;change 0<s.re;change (23:ℝ)/24<s.re at hs;linarith)
  have hWanalytic:=compact_weight_mellin_analytic W hW hWs ((23:ℝ)/24)
  have hnotboth : χ≠1 ∨ baseChangeChar χ≠1 := by
    by_cases hc : χ=1
    · exact Or.inr (baseChangeChar_ne_one_of_one χ hc)
    · exact Or.inl hc
  have hzneq : z≠1 := by intro he;subst z;norm_num at hz1
  exact (pair_zero_free_of_identity_gt_two χ (baseChangeChar χ) hnotboth
    ((23:ℝ)/24) (by norm_num)
    (fun s=>(finiteEulerFactor χ S s*SmoothMobiusCorrection.eulerCorrection χ S s)*
      mellin (fun Z : ℝ=>weightedCompactSum χ S W Z⁻¹) (-s))
    (mellin W) ((hE.mul hH).mul hM) hWanalytic
    (corrected_weighted_mellin_identity χ S hSp W hW hWs)
    z hz hzneq (ConcreteCompactWeight.weight_mellin_ne_zero z)).1

theorem dirichlet_nonvanishing_of_theta_models {q₀ : ℕ} [NeZero q₀]
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound)
    (z : ℂ) (hz : (23:ℝ)/24<z.re) (hpole : ¬(χ=1 ∧ z=1)) : χ.LFunction z≠0 := by
  by_cases hz1 : z.re<1
  · exact dirichlet_open_strip_of_theta_models χ S hbad hSp ρ q levelBound hρ hq hlevel hmodels z hz hz1
  · exact ShortDraft.dirichlet_target_of_one_le_re q₀ χ z (le_of_not_gt hz1) hpole

theorem dirichletTarget_of_theta_models
    (hmodels : ∀(q₀ : ℕ) [NeZero q₀] (χ : DirichletCharacter ℂ q₀),
      ∃S : Finset (Ideal ActualEisensteinCubic.O),fixedBadPrimes⊆S ∧ (∀P∈S,Prime P) ∧
      ∃ρ q levelBound : ℝ,0<ρ ∧ 1<q ∧ 1≤levelBound ∧
        HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound) :
    ShortDraft.DirichletTarget := by
  intro q₀ _ χ z hz hpole
  obtain ⟨S,hbad,hSp,ρ,q,level,hρ,hq,hl,hm⟩:=hmodels q₀ χ
  exact dirichlet_nonvanishing_of_theta_models χ S hbad hSp ρ q level hρ hq hl hm z hz hpole

end CanonicalRowCompletion

open scoped BigOperators Classical
namespace QuadraticAllOddCRT

section
open ActualEisensteinCubic
open QuadraticGaussRay hiding O
open ActualEisensteinCoordinates hiding O omega
open CanonicalQuadraticSieve hiding O

local instance : (Ideal.span {lambda} : Ideal ActualEisensteinCubic.O).IsMaximal:=lambdaIdeal_maximal

lemma lambda_odd : ringChar (ActualEisensteinCubic.O⧸Ideal.span {lambda})≠2:=
  ActualEisensteinSieve.lambda_residue_odd

lemma lambda_residue : residue lambda=((3:ZMod 4),(1:ZMod 4)) := by
  have h : lambda=eval (-1) 1 := by
    change (ActualEisensteinCubic.omega-1:ActualEisensteinCubic.O)=((-1:ℤ):ActualEisensteinCubic.O)+((1:ℤ):ActualEisensteinCubic.O)*ActualEisensteinCubic.omega
    push_cast
    ring
  rw [h,residue_eval]
  decide

lemma lambda_quadratic_ray_ne_zero : quadraticRayValue (residue lambda)≠0 := by
  apply quadraticRayValue_ne_zero_of_odd
  rw [lambda_residue]
  decide

lemma character_lambda_primary (p : ActualEisensteinCubic.O) (hp : lambda^2∣p-1) :
    character (Ideal.span {lambda}) (Ideal.Quotient.mk (Ideal.span {lambda}) p)=1 := by
  have hm : Ideal.Quotient.mk (Ideal.span {lambda}) p=Ideal.Quotient.mk (Ideal.span {lambda}) (1:ActualEisensteinCubic.O) :=
    Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr
      ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans hp))
  rw [hm,map_one,map_one]

def lambdaQuadraticRay (r : EisensteinEPrimaryPhase.Coord) : ℂ:=
  quadraticRayValue (EisensteinEPrimaryPhase.mul (residue lambda) r)/
    (quadraticRayValue (residue lambda)*quadraticRayValue r)

theorem character_lambda_eq_ray (p : ActualEisensteinCubic.O) (hp : p≠0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda∉Ideal.span {p}) (hc : ringChar (ActualEisensteinCubic.O⧸Ideal.span {p})≠2)
    (hprimary : lambda^2∣p-1) :
    character (Ideal.span {p}) (Ideal.Quotient.mk (Ideal.span {p}) lambda)=
      lambdaQuadraticRay (residue p) := by
  have hcop : IsCoprime (Ideal.span {lambda} : Ideal ActualEisensteinCubic.O) (Ideal.span {p}) := by
    apply Ideal.isCoprime_of_isMaximal
    intro he
    apply hg
    rw [←he]
    exact Ideal.subset_span (by simp)
  have h:=quadratic_ray_cross lambda p PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero hp hcop lambda_odd hc
  rw [character_lambda_primary p hprimary,one_mul] at h
  have hodd : EisensteinEPrimaryPhase.odd (residue p) := by
    have hn : ‖quadraticRayValue (residue p)‖=1 := by
      let pp : Unit→ActualEisensteinCubic.O:=fun _=>p
      have hpp : ∀i,pp i≠0:=fun _=>hp
      have hcp : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {pp i})):=by
        intro i j hij
        exact False.elim (hij (Subsingleton.elim _ _))
      have hh:=FiniteGaussPhase.norm_canonicalProductGauss pp hpp hcp (fun _=>hg) (fun _=>hc)
        (fun _=>3) (by intro i;decide) (by intro i;decide)
      rw [QuadraticGaussRay.canonicalProductGauss_three_eq_rayValue pp hpp hcp (fun _=>hg) (fun _=>hc)] at hh
      simpa [pp] using hh
    exact QuadraticUnitInvariance.odd_of_quadraticRayValue_norm_eq_one _ hn
  unfold lambdaQuadraticRay
  rw [←residue_mul]
  apply (eq_div_iff (mul_ne_zero lambda_quadratic_ray_ne_zero (quadraticRayValue_ne_zero_of_odd _ hodd))).mpr
  simpa only [mul_assoc] using h.symm

end

open ActualEisensteinCubic
open QuadraticGaussRay hiding O
open ActualEisensteinCoordinates hiding O omega

def lambdaQuadraticTable (r : EisensteinEPrimaryPhase.Coord) : ℤ :=
  if ¬EisensteinEPrimaryPhase.odd r then 0
  else if r∈({(0,1),(1,0),(1,2),(1,3),(2,3),(3,3)} : Finset EisensteinEPrimaryPhase.Coord)
    then 1 else -1

lemma lambdaQuadraticTable_mul (r s : EisensteinEPrimaryPhase.Coord) :
    lambdaQuadraticTable (EisensteinEPrimaryPhase.mul r s)=
      lambdaQuadraticTable r*lambdaQuadraticTable s := by
  have h : ∀r s : EisensteinEPrimaryPhase.Coord,
      lambdaQuadraticTable (EisensteinEPrimaryPhase.mul r s)=
        lambdaQuadraticTable r*lambdaQuadraticTable s := by decide
  exact h r s

lemma lambdaQuadraticTable_eq_ray (r : EisensteinEPrimaryPhase.Coord)
    (hr : EisensteinEPrimaryPhase.odd r) :
    (lambdaQuadraticTable r:ℂ)=lambdaQuadraticRay r := by
  have hcmp (a b : ZMod 4) : (a=b) ↔ (a.val=b.val) :=
    (ZMod.val_injective 4).eq_iff.symm
  have hn3 : (-3 : ZMod 4) = 1 := by decide
  rcases r with ⟨a,b⟩
  have hcases : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
  rcases hcases a with rfl | rfl | rfl | rfl <;>
    rcases hcases b with rfl | rfl | rfl | rfl <;>
    norm_num [EisensteinEPrimaryPhase.odd,ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] at hr <;>
    norm_num [lambdaQuadraticTable,lambdaQuadraticRay,lambda_residue,EisensteinEPrimaryPhase.mul,
      EisensteinEPrimaryPhase.odd,quadraticRayValue,breveGaussianFourTerms_formula,
      Prod.mk.injEq,hcmp,hn3,ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.val_ofNat,
      ZMod.val_neg_one,ZMod.val_mul,ZMod.val_add,ZMod.val_sub,
      Complex.I_sq,Complex.I_pow_three,Complex.inv_I,zpow_neg] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.I_pow_three]
  all_goals
    field_simp [Complex.I_ne_zero]
    change (-2 : ℂ) = Complex.I * (Complex.I ^ (1 : ℤ) + Complex.I ^ (2 - 1 : ℤ))
    norm_num [Complex.I_sq]
    ring_nf
    norm_num [Complex.I_sq]

def lambdaQuadraticCharacter : ActualEisensteinCubic.O→*ℂ where
  toFun n:=(lambdaQuadraticTable (residue n):ℂ)
  map_one' := by
    have h : residue (1:ActualEisensteinCubic.O)=((1:ZMod 4),0):=by
      have h1 : (1:ActualEisensteinCubic.O)=eval 1 0:=by simp [eval]
      rw [h1,residue_eval]
      norm_num
    rw [h]
    exact_mod_cast (show lambdaQuadraticTable ((1:ZMod 4),0)=1 from by decide)
  map_mul' x y := by
    rw [residue_mul,lambdaQuadraticTable_mul]
    push_cast
    rfl

lemma lambdaQuadraticCharacter_periodic (x y : ActualEisensteinCubic.O) (h : (4:ActualEisensteinCubic.O)∣x-y) :
    lambdaQuadraticCharacter x=lambdaQuadraticCharacter y := by
  change (lambdaQuadraticTable (residue x):ℂ)=(lambdaQuadraticTable (residue y):ℂ)
  rw [QuadraticGaussRay.residue_eq_of_four_dvd_sub x y h]

end QuadraticAllOddCRT

open scoped BigOperators Classical
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open CubicJacobiGlobal hiding O
open QuadraticAllOddCRT
open CanonicalQuadraticSieve hiding O
open ConcreteTraceCRT (eisEmbedding)
open UniqueFactorizationMonoid

lemma localRowValue_square (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) :
    localRowValue x P^2=eisEmbedding (primeValue P x) := by
  unfold localRowValue primeValue
  split_ifs with h
  · let : P.IsMaximal:=h.1
    change (actualSextic P h.2 (Ideal.Quotient.mk P x))^2=_
    rw [←MulChar.pow_apply' _ (by decide : (2:ℕ)≠0),canonicalSextic_pow_two]
    rfl
  · simp

theorem idealRowHom_square (x : ActualEisensteinCubic.O) (I : Ideal ActualEisensteinCubic.O) :
    idealRowHom x I^2=eisEmbedding (idealSymbol I x) := by
  have hm (s : Multiset (Ideal ActualEisensteinCubic.O)) :
      (s.map (localRowValue x)).prod^2=eisEmbedding ((s.map (fun P=>primeValue P x)).prod) := by
    induction s using Multiset.induction_on with
    | empty=>simp
    | @cons P s ih=>
      simp only [Multiset.map_cons,Multiset.prod_cons,mul_pow,map_mul,localRowValue_square,ih]
  by_cases hI : I=0
  · subst I
    simp only [map_zero,idealSymbol_zero,zero_pow (by decide : (2:ℕ)≠0)]
  · change (if I=0 then 0 else _)^2=eisEmbedding (if I=0 then 0 else _)
    simp only [ite_eq_right hI]
    exact hm _

lemma actualSextic_cube_quadratic (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : lambda∉P) :
    actualSextic P hg^3=character P := by
  let : Field (ActualEisensteinCubic.O⧸P):=Ideal.Quotient.field P
  let : Fintype (ActualEisensteinCubic.O⧸P):=Fintype.ofFinite _
  obtain ⟨χ,hχ,hχ3⟩ : ∃χ : MulChar (ActualEisensteinCubic.O⧸P) ActualEisensteinCubic.O,
      actualSextic P hg=χ.ringHomComp eisEmbedding ∧
      χ^3=(quadraticChar (ActualEisensteinCubic.O⧸P)).ringHomComp (Int.castRingHom ActualEisensteinCubic.O) :=
    ⟨_,rfl,(sexticChar_powers P hg).2.1⟩
  rw [hχ,MulChar.ringHomComp_pow,hχ3]
  ext x
  change eisEmbedding ((quadraticChar (ActualEisensteinCubic.O⧸P) x:ℤ):ActualEisensteinCubic.O)=((quadraticChar (ActualEisensteinCubic.O⧸P) x:ℤ):ℂ)
  simp

lemma idealRowHom_lambda_prime_cube (p : ActualEisensteinCubic.O) (hp : Prime p)
    (hprimary : lambda^2∣p-1) (hs : Supported (Ideal.span {p})) :
    idealRowHom lambda (Ideal.span {p})^3=lambdaQuadraticCharacter p := by
  let : (Ideal.span {p}).IsMaximal:=PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hmem : Ideal.span {p}∈normalizedFactors (Ideal.span {p}) :=
    (Ideal.mem_normalizedFactors_iff hs.1).mpr ⟨inferInstance,le_rfl⟩
  obtain ⟨hg,hc⟩:=hs.2 _ hmem
  rw [idealRowHom_prime lambda _ hg]
  change (actualSextic _ hg (Ideal.Quotient.mk _ lambda))^3=_
  rw [←MulChar.pow_apply' _ (by decide : (3:ℕ)≠0),actualSextic_cube_quadratic]
  have he:=character_lambda_eq_ray p hp.ne_zero hg hc hprimary
  have ho:=ActualEisensteinCoordinates.odd_residue_iff_not_two_dvd p
  have hs' := (supported_span_iff p).mp hs
  change character _ (Ideal.Quotient.mk _ lambda)=_
  rw [he]
  exact (lambdaQuadraticTable_eq_ray _ (ho.mpr hs'.2)).symm

theorem idealRowHom_lambda_cube (y : ActualEisensteinCubic.O) (hy : lambda^2∣y-1)
    (hs : Supported (Ideal.span {y})) :
    idealRowHom lambda (Ideal.span {y})^3=lambdaQuadraticCharacter y := by
  have hy0 : y≠0:=by
    intro he
    apply hs.1
    simp [he]
  obtain ⟨s,hprod,hfactors⟩:=exists_primary_prime_factorization y hy0 hy
  rw [←hprod] at hs ⊢
  clear hprod hy hy0 y
  induction s using Multiset.induction_on with
  | empty=>
    simp only [Multiset.prod_zero,Ideal.span_singleton_one,←Ideal.one_eq_top,map_one,one_pow]
  | @cons p s ih=>
    have hp:=hfactors p (Multiset.mem_cons_self _ _)
    have htail : ∀q∈s,Prime q ∧ lambda^2∣q-1:=
      fun q hq=>hfactors q (Multiset.mem_cons_of_mem hq)
    have hsplit : Supported (Ideal.span {p}) ∧ Supported (Ideal.span {s.prod}) := by
      simpa only [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,supported_mul_iff] using hs
    rw [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,map_mul,mul_pow,
      idealRowHom_lambda_prime_cube p hp.1 hp.2 hsplit.1,ih hsplit.2 htail,map_mul]

theorem idealRowHom_lambda_formula (y : ActualEisensteinCubic.O) (hy : lambda^2∣y-1)
    (hs : Supported (Ideal.span {y})) :
    idealRowHom lambda (Ideal.span {y})=
      eisEmbedding (CubicRamified.linearRay 1 0 y)^2*lambdaQuadraticCharacter y := by
  have htwo:=idealRowHom_square lambda (Ideal.span {y})
  change idealRowHom lambda (Ideal.span {y})^2=eisEmbedding (symbol lambda y) at htwo
  rw [CubicRamified.symbol_lambda_eq_linearRay y hy] at htwo
  have hthree:=idealRowHom_lambda_cube y hy hs
  have hq : lambdaQuadraticCharacter y^2=1 := by
    change (lambdaQuadraticTable (ActualEisensteinCoordinates.residue y):ℂ)^2=1
    have ho := ActualEisensteinCoordinates.odd_residue_iff_not_two_dvd y |>.mpr ((supported_span_iff y).mp hs).2
    unfold lambdaQuadraticTable
    rw [ite_eq_right (not_not.mpr ho)]
    split_ifs <;> norm_num
  have hsix : idealRowHom lambda (Ideal.span {y})^6=1 := by
    calc
      _ = (idealRowHom lambda (Ideal.span {y})^3)^2:=by ring
      _ = 1:=by rw [hthree,hq]
  calc
    _ = (idealRowHom lambda (Ideal.span {y})^2)^2*(idealRowHom lambda (Ideal.span {y})^3):=by
      calc
        _ = idealRowHom lambda (Ideal.span {y})*idealRowHom lambda (Ideal.span {y})^6:=by rw [hsix,mul_one]
        _ = _:=by ring
    _ = _:=by rw [htwo,hthree]

theorem idealRowHom_lambda_mod_thirty_six (x y : ActualEisensteinCubic.O)
    (hx : lambda^2∣x-1) (hy : lambda^2∣y-1)
    (hsx : Supported (Ideal.span {x})) (hsy : Supported (Ideal.span {y}))
    (hxy : (36:ActualEisensteinCubic.O)∣x-y) :
    idealRowHom lambda (Ideal.span {x})=idealRowHom lambda (Ideal.span {y}) := by
  rw [idealRowHom_lambda_formula x hx hsx,idealRowHom_lambda_formula y hy hsy,
    CubicRamified.linearRay_congr_mod_nine 1 0 x y hx hy ((show (9:ActualEisensteinCubic.O)∣36 from ⟨4,by norm_num⟩).trans hxy),
    lambdaQuadraticCharacter_periodic x y ((show (4:ActualEisensteinCubic.O)∣36 from ⟨9,by norm_num⟩).trans hxy)]

end CanonicalRowCompletion

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma cuspRemainder_absolute_chart (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (M : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (hz : ‖z‖≤1)
    (v : ℝ) (hv : 1/2≤v) (hv0 : 0<v) :
    Summable (fun r : CuspCosets => ‖cuspRemainderProfile a b s
      (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))‖) ∧
    (∑'r : CuspCosets,‖cuspRemainderProfile a b s
      (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))‖)≤eisensteinRemainderBound b s := by
  let G : ((Fin 2×Fin 2)→ℤ)→ℝ := fun n => (max 5 (2*b))^s.re*‖n‖^(-s.re)
  let f : CuspCosets→(Fin 2×Fin 2)→ℤ := fun r => rowCoordinates (translatedCuspRow M r)
  let R : CuspCosets→ℝ := fun r => ‖cuspRemainderProfile a b s
    (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))‖
  have hg : Summable G := (summable_integer_four_rpow s.re hs).mul_left _
  have hi : Function.Injective f := rowCoordinates_injective.comp (translatedCuspRow_injective M)
  have hb : ∀r,R r≤G (f r) := by
    intro r
    simpa only [norm_mul,norm_inv,norm_cosetCharacter,inv_one,one_mul] using
      translated_remainder_majorant a b s hab (by linarith) (by linarith) M z hz v hv hv0 r
  have hr : Summable R := (hg.comp_injective hi).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  refine ⟨hr,?_⟩
  have hsum : (∑'r,R r)≤∑'n,G n :=
    Summable.tsum_le_tsum_of_inj f hi (fun _ _ => by dsimp [G]; positivity) hb hr hg
  simpa only [G,tsum_mul_left,eisensteinRemainderBound] using hsum

theorem cuspRemainder_absolute_bound (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (w : HyperbolicSpace) :
    Summable (fun r : CuspCosets => ‖cuspRemainderProfile a b s (cosetHeight r w)‖) ∧
    (∑'r : CuspCosets,‖cuspRemainderProfile a b s (cosetHeight r w)‖)≤eisensteinRemainderBound b s := by
  obtain ⟨M,z,v,hv,hMw,hz,hfloor⟩ := bianchi_reduction_height_floor w
  have hz1 : ‖z‖≤1 := by
    rw [Complex.normSq_eq_norm_sq] at hz
    nlinarith [norm_nonneg z]
  have hv1 : 1/2≤v := by
    have hh := Real.sq_sqrt (by norm_num : (0:ℝ)≤2/3)
    have hh0 := Real.sqrt_nonneg (2/3 : ℝ)
    nlinarith
  have hw : w=integralComplexMatrix M⁻¹ • upperPoint z v hv := by
    rw [←hMw,map_inv,inv_smul_smul]
  rw [hw]
  exact cuspRemainder_absolute_chart a b ha hab s hs M⁻¹ z hz1 v hv1 hv

lemma cuspRemainder_aux_norm (b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) (hvb : v≤b) :
    ‖cuspRemainderProfile (b+1) (b+2) s v‖=v^s.re := by
  rw [cuspRemainderProfile,cuspSeedProfile_zero (b+1) (b+2) s v (by linarith) (by linarith),
    sub_zero,positiveHeightPower_eq_cpow s v hv,Complex.norm_cpow_eq_rpow_re_of_pos hv]

lemma cuspRemainder_row_scaled_deriv_aux_bound (a b : ℝ) (hab : a<b) (s : ℂ)
    (C : ℝ) (hC0 : 0≤C) (hC : ∀v,|v*deriv (cuspTransition a b) v|≤C)
    (u : Fin 2→ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    ‖(p 2:ℂ)*deriv (axisSlice (fun q => cuspRemainderProfile a b s (rowHeight u q)) p j) (p j)‖≤
      (‖s‖+C)*‖cuspRemainderProfile (b+1) (b+2) s (rowHeight u p)‖ := by
  have hh := rowHeight_pos u hu p hp
  by_cases hb : rowHeight u p≤b
  · rw [cuspRemainder_aux_norm b s _ hh hb]
    exact cuspRemainder_row_scaled_deriv_bound a b s C hC u hu p hp j
  · have hd := (rowProfile_axis_derivatives (cuspRemainderProfile a b s)
      (cuspRemainderProfile_contDiffAt a b s) u hu p hp j).1
    rw [hd.deriv,cuspRemainderProfile_deriv_zero a b s _ hab hh (lt_of_not_ge hb)]
    simp only [zero_mul,mul_zero,norm_zero]
    exact mul_nonneg (add_nonneg (norm_nonneg s) hC0) (norm_nonneg _)

end

open Filter
open scoped BigOperators Classical Topology ContDiff

def weightedHeightProfile (F : ℝ→ℂ) (r : CuspCosets) (p : SpatialCoordinates) : ℂ :=
  (cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) p)

lemma weightedHeightProfile_axis_differentiable (F : ℝ→ℂ)
    (hF : ∀v,0<v→ContDiffAt ℝ ∞ F v) (r : CuspCosets)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    DifferentiableAt ℝ (axisSlice (weightedHeightProfile F r) p j) (p j) :=
  ((rowProfile_axis_derivatives F hF (embeddedRow r) (embeddedRow_ne_zero r) p hp j).1.const_mul _).differentiableAt

lemma heightPoincare_axis_termwise (F : ℝ→ℂ) (hzero : ∀v≤1,F v=0)
    (hF : ∀v,0<v→ContDiffAt ℝ ∞ F v)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    Summable (fun r => deriv (axisSlice (weightedHeightProfile F r) p j) (p j)) ∧
    HasDerivAt (axisSlice (heightPoincareField F) p j)
      (∑'r,deriv (axisSlice (weightedHeightProfile F r) p j) (p j)) (p j) := by
  obtain ⟨U,hU,hpU,S,hrows⟩ := locally_finite_high_rows p hp
  have ht : Tendsto (fun t => Function.update p j t) (𝓝 (p j)) (𝓝 p) := by
    simpa only [ContinuousAt,Function.update_eq_self] using
      ((continuous_axis_update p j).continuousAt (x := p j))
  have hn : ∀ᶠt in 𝓝 (p j),Function.update p j t∈U := ht (hU.mem_nhds hpU)
  have hz (r : CuspCosets) (hr : r∉S) :
      deriv (axisSlice (weightedHeightProfile F r) p j) (p j)=0 := by
    have he : axisSlice (weightedHeightProfile F r) p j=ᶠ[𝓝 (p j)] (fun _ => 0) := by
      filter_upwards [hn] with t ht
      change (cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) (Function.update p j t))=0
      rw [hzero _ ((hrows _ ht).2 r hr).le,mul_zero]
    exact he.deriv_eq.trans (deriv_const _ _)
  refine ⟨summable_of_ne_finset_zero hz,?_⟩
  rw [tsum_eq_sum hz]
  have hd := HasDerivAt.sum (u := S) (fun r hr =>
    (weightedHeightProfile_axis_differentiable F hF r p hp j).hasDerivAt)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hn] with t ht
  simp only [Finset.sum_apply]
  change (∑'r,weightedHeightProfile F r (Function.update p j t))=
    ∑r∈S,weightedHeightProfile F r (Function.update p j t)
  apply tsum_eq_sum
  intro r hr
  change (cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) (Function.update p j t))=0
  rw [hzero _ ((hrows _ ht).2 r hr).le,mul_zero]

lemma weightedRemainder_axis_deriv (a b : ℝ) (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)=
      deriv (axisSlice (smoothSummand s r) p j) (p j)-
        deriv (axisSlice (weightedHeightProfile (cuspSeedProfile a b s) r) p j) (p j) := by
  have hn : ∀ᶠt in 𝓝 (p j),0<(Function.update p j t) 2 := by
    apply ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
    simpa only [Function.comp_apply,Function.update_eq_self] using hp
  have he : axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j=ᶠ[𝓝 (p j)]
      (fun t => axisSlice (smoothSummand s r) p j t-
        axisSlice (weightedHeightProfile (cuspSeedProfile a b s) r) p j t) := by
    filter_upwards [hn] with t ht
    simp only [axisSlice,weightedHeightProfile,cuspRemainderProfile,smoothSummand]
    rw [rowSmoothPower_eq_height s _ (embeddedRow_ne_zero r) _ ht,
      positiveHeightPower_eq_cpow s _ (rowHeight_pos _ (embeddedRow_ne_zero r) _ ht)]
    ring
  rw [he.deriv_eq]
  exact deriv_sub (smooth_axis_differentiable s r p hp j)
    (weightedHeightProfile_axis_differentiable _ (cuspSeedProfile_contDiffAt a b s) r p hp j)

def eisensteinRemainderField (a b : ℝ) (s : ℂ) (p : SpatialCoordinates) : ℂ :=
  smoothEisenstein s p-smoothCuspSeedField a b s p

theorem eisensteinRemainder_axis_termwise (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    Summable (fun r => deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)) ∧
    HasDerivAt (axisSlice (eisensteinRemainderField a b s) p j)
      (∑'r,deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)) (p j) := by
  have hE := eisenstein_axis_termwise s hs p hp j
  have hS := heightPoincare_axis_termwise (cuspSeedProfile a b s)
    (fun v hv => cuspSeedProfile_zero a b s v hab (hv.trans ha.le))
    (cuspSeedProfile_contDiffAt a b s) p hp j
  have hcoeff : (∑'r,deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j))=
      (∑'r,deriv (axisSlice (smoothSummand s r) p j) (p j))-
        ∑'r,deriv (axisSlice (weightedHeightProfile (cuspSeedProfile a b s) r) p j) (p j) := by
    simp_rw [weightedRemainder_axis_deriv a b s _ p hp j]
    exact hE.1.tsum_sub hS.1
  refine ⟨(hE.1.sub hS.1).congr (fun r => (weightedRemainder_axis_deriv a b s r p hp j).symm),?_⟩
  rw [hcoeff]
  apply (hE.2.2.1.sub hS.2).congr_of_eventuallyEq
  have hn : ∀ᶠt in 𝓝 (p j),0<(Function.update p j t) 2 := by
    apply ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
    simpa only [Function.comp_apply,Function.update_eq_self] using hp
  filter_upwards [hn] with t ht
  change smoothEisenstein s _-smoothCuspSeedField a b s _=
    smoothEisenstein s _-heightPoincareField (cuspSeedProfile a b s) _
  rw [smoothCuspSeedField_eq a b s ha hab _ ht]

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

namespace CubicEisenstein

lemma weightedRemainder_scaled_deriv_bound (a b : ℝ) (hab : a<b) (s : ℂ)
    (C : ℝ) (hC0 : 0≤C) (hC : ∀v,|v*deriv (cuspTransition a b) v|≤C)
    (r : CuspCosets) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    ‖(p 2:ℂ)*deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)‖≤
      (‖s‖+C)*‖cuspRemainderProfile (b+1) (b+2) s (rowHeight (embeddedRow r) p)‖ := by
  let g : SpatialCoordinates→ℂ:=fun q => cuspRemainderProfile a b s (rowHeight (embeddedRow r) q)
  have hd := (rowProfile_axis_derivatives (cuspRemainderProfile a b s)
    (cuspRemainderProfile_contDiffAt a b s) (embeddedRow r) (embeddedRow_ne_zero r) p hp j).1
  have hw := hd.const_mul (cosetCharacter r)⁻¹
  have he : deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)=
      (cosetCharacter r)⁻¹*deriv (axisSlice g p j) (p j) := by
    change deriv (fun t => (cosetCharacter r)⁻¹*axisSlice g p j t) (p j)=_
    rw [hw.deriv,hd.deriv]
  rw [he]
  calc
    ‖(p 2:ℂ)*((cosetCharacter r)⁻¹*deriv (axisSlice g p j) (p j))‖
      = ‖(cosetCharacter r)⁻¹*((p 2:ℂ)*deriv (axisSlice g p j) (p j))‖ := by congr 1; ring
    _ = ‖(p 2:ℂ)*deriv (axisSlice g p j) (p j)‖ := by
      rw [norm_mul,norm_inv,norm_cosetCharacter,inv_one,one_mul]
    _ ≤ _ := cuspRemainder_row_scaled_deriv_aux_bound a b hab s C hC0 hC _ (embeddedRow_ne_zero r) p hp j

theorem eisensteinRemainder_scaled_axis_bound (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    ∃B : ℝ,0≤B ∧ ∀p : SpatialCoordinates,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*deriv (axisSlice (eisensteinRemainderField a b s) p j) (p j)‖≤B := by
  obtain ⟨C,hC0,hC⟩ := cuspTransition_euler_bounded a b hab
  refine ⟨(‖s‖+C)*eisensteinRemainderBound (b+2) s,
    mul_nonneg (add_nonneg (norm_nonneg s) hC0) (eisensteinRemainderBound_nonneg _ _),?_⟩
  intro p hp j
  have hA : Summable (fun r : CuspCosets =>
      ‖cuspRemainderProfile (b+1) (b+2) s (rowHeight (embeddedRow r) p)‖) ∧
      (∑'r : CuspCosets,‖cuspRemainderProfile (b+1) (b+2) s (rowHeight (embeddedRow r) p)‖)≤
        eisensteinRemainderBound (b+2) s := by
    simpa only [cosetHeight_upperPoint_rowHeight] using
      cuspRemainder_absolute_bound (b+1) (b+2) (by linarith) (by linarith) s hs
        (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp)
  have hB := hA.1.mul_left (‖s‖+C)
  have hb (r : CuspCosets) := weightedRemainder_scaled_deriv_bound a b hab s C hC0 hC r p hp j
  have hnorm := hB.of_nonneg_of_le (fun r => norm_nonneg
    ((p 2:ℂ)*deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j))) hb
  have ht := eisensteinRemainder_axis_termwise a b ha hab s (by linarith) p hp j
  rw [ht.2.deriv,←tsum_mul_left]
  apply (norm_tsum_le_tsum_norm hnorm).trans
  apply (Summable.tsum_le_tsum hb hnorm hB).trans
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hA.2 (add_nonneg (norm_nonneg s) hC0)

def kernelEisensteinRemainder (a b : ℝ) (s : ℂ) (hs : 2<s.re) : KernelQuotient→ℂ :=
  fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q

lemma kernelEisensteinRemainder_smooth (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (kernelEisensteinRemainder a b s hs) :=
  (kernelQuotientEisenstein_contMDiff s hs).sub (kernelQuotientSeed_contMDiff a b s ha hab)

lemma kernelEisensteinRemainder_euclidean_smooth (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (fun q => kernelEisensteinRemainder a b s hs (kernelEuclideanProjection q)) p :=
  ((((kernelEisensteinRemainder_smooth a b ha hab s hs).comp kernelProjection_contMDiff)
    (euclideanToHyperbolic p)).comp p (euclideanToHyperbolic_contMDiffAt p hp)).contDiffAt

lemma kernelEisensteinRemainder_euclidean_eq (a b : ℝ) (s : ℂ) (hs : 2<s.re)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    kernelEisensteinRemainder a b s hs (kernelEuclideanProjection p)=eisensteinRemainderField a b s p.ofLp := by
  unfold kernelEisensteinRemainder kernelEuclideanProjection
  simp only [Function.comp_apply]
  rw [euclideanToHyperbolic_positive p hp,kernelQuotientEisenstein_mk,hyperbolicEisenstein_upperPoint]
  unfold eisensteinRemainderField
  rw [smoothEisenstein_eq_actual s p.ofLp hp,smoothCuspSeedField,dite_eq_left hp]
  simp only [mul_comm Complex.I]
  rfl

theorem kernelEisensteinRemainder_scaled_fderiv_bound (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    ∃B : ℝ,0≤B ∧ ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (fun q => kernelEisensteinRemainder a b s (by linarith)
        (kernelEuclideanProjection q)) p (euclideanCoordinateVector j)‖≤B := by
  obtain ⟨B,hB,hbound⟩ := eisensteinRemainder_scaled_axis_bound a b ha hab s hs
  refine ⟨B,hB,?_⟩
  intro p hp j
  let f : EuclideanSpatial→ℂ:=fun q => kernelEisensteinRemainder a b s (by linarith) (kernelEuclideanProjection q)
  have hf : ∀q,0<q 2→ContDiffAt ℝ ∞ f q := kernelEisensteinRemainder_euclidean_smooth a b ha hab s (by linarith)
  have he : ∀q : SpatialCoordinates,0<q 2→f (WithLp.toLp 2 q)=eisensteinRemainderField a b s q := by
    intro q hq
    exact kernelEisensteinRemainder_euclidean_eq a b s (by linarith) (WithLp.toLp 2 q) hq
  have heq := axisSlice_eventuallyEq_of_positive _ _ he p.ofLp hp j
  change ‖(p 2:ℂ)*fderiv ℝ f p (euclideanCoordinateVector j)‖≤B
  rw [←(euclideanAxisSlice_derivatives f hf p hp j).1,heq.deriv_eq]
  exact hbound p.ofLp hp j

end CubicEisenstein

end

end OAI
end OAIOriginalModule0256

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.ConjugateLevelAction
Source SHA256: 7f7ca628f1099385d079e845e669c4692bc4f84ef4291513ada64cc820d82366
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0257



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
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise

open CubicKubota
local notation "O" => ActualEisensteinCubic.O

lemma globalKubotaKernel_conjugate_mem (M : levelThree) (N : globalKubotaKernel) :
    (M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹∈globalKubotaKernel := by
  obtain ⟨n,hn,hnval⟩ := N.property
  change (n:SL(2,ActualEisensteinCubic.O))=(N:SL(2,ActualEisensteinCubic.O)) at hnval
  refine ⟨M*n*M⁻¹,?_,?_⟩
  · change finiteCubicMultiplier (M*n*M⁻¹)=1
    change finiteCubicMultiplier n=1 at hn
    simp only [map_mul,map_inv,hn,mul_one,mul_inv_cancel]
  · change (M:SL(2,ActualEisensteinCubic.O))*(n:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹=_
    rw [hnval]

def kernelConjugate (M : levelThree) : globalKubotaKernel ≃* globalKubotaKernel where
  toFun N := ⟨(M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹,globalKubotaKernel_conjugate_mem M N⟩
  invFun N := ⟨(M⁻¹:levelThree)*(N:SL(2,ActualEisensteinCubic.O))*(M⁻¹:levelThree)⁻¹,globalKubotaKernel_conjugate_mem M⁻¹ N⟩
  left_inv N := by apply Subtype.ext; simp [mul_assoc]
  right_inv N := by apply Subtype.ext; simp [mul_assoc]
  map_mul' N P := by apply Subtype.ext; simp [mul_assoc]

lemma kernelConjugate_coe (M : levelThree) (N : globalKubotaKernel) :
    (kernelConjugate M N : SL(2,ActualEisensteinCubic.O))=(M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹ := rfl

lemma level_action_respects_kernel (M : levelThree) (u v : HyperbolicSpace)
    (h : (integralOrbitRel globalKubotaKernel).r u v) :
    (integralOrbitRel globalKubotaKernel).r (complexMatrix M • u) (complexMatrix M • v) := by
  obtain ⟨N,hN⟩ := h
  refine ⟨kernelConjugate M N,?_⟩
  change integralComplexMatrix ((M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹) •
    (complexMatrix M • u)=complexMatrix M • v
  rw [map_mul,map_mul,map_inv,mul_smul,mul_smul]
  change complexMatrix M • (integralComplexMatrix (N:SL(2,ActualEisensteinCubic.O)) •
    ((complexMatrix M)⁻¹ • (complexMatrix M • u)))=_
  rw [inv_smul_smul,hN]

def kernelLevelAction (M : levelThree) : KernelQuotient→KernelQuotient :=
  Quotient.map' (fun w => complexMatrix M • w) (level_action_respects_kernel M)

lemma kernelLevelAction_mk (M : levelThree) (w : HyperbolicSpace) :
    kernelLevelAction M (integralOrbitProjection globalKubotaKernel w)=
      integralOrbitProjection globalKubotaKernel (complexMatrix M • w) := rfl

lemma kernelLevelAction_one (q : KernelQuotient) : kernelLevelAction 1 q=q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection globalKubotaKernel (complexMatrix 1 • w)=integralOrbitProjection globalKubotaKernel w
    rw [map_one,one_smul]

lemma kernelLevelAction_mul (M N : levelThree) (q : KernelQuotient) :
    kernelLevelAction (M*N) q=kernelLevelAction M (kernelLevelAction N q) := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection globalKubotaKernel (complexMatrix (M*N) • w)=
      integralOrbitProjection globalKubotaKernel (complexMatrix M • (complexMatrix N • w))
    rw [map_mul,mul_smul]

lemma kernelLevelAction_continuous (M : levelThree) : Continuous (kernelLevelAction M) :=
  (continuous_hyperbolic_action (complexMatrix M)).quotient_map' (level_action_respects_kernel M)

def kernelLevelHomeomorph (M : levelThree) : KernelQuotient ≃ₜ KernelQuotient where
  toFun := kernelLevelAction M
  invFun := kernelLevelAction M⁻¹
  left_inv q := by rw [←kernelLevelAction_mul,inv_mul_cancel,kernelLevelAction_one]
  right_inv q := by rw [←kernelLevelAction_mul,mul_inv_cancel,kernelLevelAction_one]
  continuous_toFun := kernelLevelAction_continuous M
  continuous_invFun := kernelLevelAction_continuous M⁻¹

lemma kernelLevelAction_eisenstein (M : levelThree) (s : ℂ) (hs : 2<s.re)
    (q : KernelQuotient) :
    kernelQuotientEisenstein s hs (kernelLevelAction M q)=
      complexCharacter M*kernelQuotientEisenstein s hs q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    exact hyperbolicEisenstein_automorphy M s hs w

lemma kernelLevelAction_seed (M : levelThree) (a b : ℝ) (s : ℂ) (q : KernelQuotient) :
    kernelQuotientSeed a b s (kernelLevelAction M q)=complexCharacter M*kernelQuotientSeed a b s q := by
  induction q using Quotient.inductionOn with
  | _ w => exact smoothCuspSeed_automorphy a b s M w

lemma kernelLevelAction_defect (M : levelThree) (a b : ℝ) (s : ℂ) (q : KernelQuotient) :
    kernelQuotientDefect a b s (kernelLevelAction M q)=complexCharacter M*kernelQuotientDefect a b s q := by
  induction q using Quotient.inductionOn with
  | _ w => exact smoothCuspSeedDefect_automorphy a b s M w

lemma kernelLevelAction_fundamentalDomain (M : levelThree) :
    IsFundamentalDomain globalKubotaKernel
      ((fun w : HyperbolicSpace => complexMatrix M • w) '' hyperbolicFundamentalSet globalKubotaKernel)
      hyperbolicVolume := by
  apply (hyperbolicFundamentalSet_isFundamentalDomain globalKubotaKernel
    globalKubotaKernel_le_levelThree).image_of_equiv (MulAction.toPerm (complexMatrix M))
    (show Measure.QuasiMeasurePreserving (MulAction.toPerm (complexMatrix M)).symm hyperbolicVolume hyperbolicVolume from by
      exact (measurePreserving_smul (complexMatrix M)⁻¹ hyperbolicVolume).quasiMeasurePreserving)
    (kernelConjugate M⁻¹).toEquiv
  intro N w
  change complexMatrix M • (integralComplexMatrix
    ((M⁻¹:levelThree)*(N:SL(2,ActualEisensteinCubic.O))*(M⁻¹:levelThree)⁻¹) • w)=
      integralComplexMatrix (N:SL(2,ActualEisensteinCubic.O)) • (complexMatrix M • w)
  simp only [Subgroup.coe_inv,map_mul,map_inv]
  change complexMatrix M • (((complexMatrix M)⁻¹*integralComplexMatrix (N:SL(2,ActualEisensteinCubic.O))*
    ((complexMatrix M)⁻¹)⁻¹) • w)=_
  simp only [inv_inv,mul_smul,smul_inv_smul]

lemma kernelLevelAction_measurePreserving (M : levelThree) :
    MeasurePreserving (kernelLevelAction M) (integralQuotientVolume globalKubotaKernel)
      (integralQuotientVolume globalKubotaKernel) := by
  refine ⟨(kernelLevelAction_continuous M).measurable,?_⟩
  let act : HyperbolicSpace→HyperbolicSpace := fun w => complexMatrix M • w
  have hmap := (measurePreserving_smul (complexMatrix M) hyperbolicVolume).restrict_image_emb
    (measurableEmbedding_const_smul (complexMatrix M)) (hyperbolicFundamentalSet globalKubotaKernel)
  have heq : kernelLevelAction M ∘ integralOrbitProjection globalKubotaKernel=
      integralOrbitProjection globalKubotaKernel ∘ act := by ext w; rfl
  change Measure.map (kernelLevelAction M)
    (Measure.map (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)))=_
  rw [Measure.map_map (kernelLevelAction_continuous M).measurable
    (measurable_integralOrbitProjection _),heq,
    ←Measure.map_map (measurable_integralOrbitProjection _) (continuous_hyperbolic_action _).measurable]
  change Measure.map (integralOrbitProjection globalKubotaKernel)
    (Measure.map act (hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)))=_
  rw [hmap.map_eq]
  exact integralQuotientVolume_independent globalKubotaKernel globalKubotaKernel_le_levelThree _
    (kernelLevelAction_fundamentalDomain M)

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open CubicKubota

def kernelLevelPullback (M : levelThree) : KernelQuotientL2 →ₗᵢ[ℂ] KernelQuotientL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (kernelLevelAction M) (kernelLevelAction_measurePreserving M)

lemma kernelLevelPullback_ae_eq (M : levelThree) (F : KernelQuotientL2) :
    kernelLevelPullback M F=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => F (kernelLevelAction M q) :=
  Lp.coeFn_compMeasurePreserving F (kernelLevelAction_measurePreserving M)

lemma kernelLevelPullback_one (F : KernelQuotientL2) : kernelLevelPullback 1 F=F := by
  apply Lp.ext
  filter_upwards [kernelLevelPullback_ae_eq 1 F] with q hq
  simpa only [kernelLevelAction_one] using hq

lemma kernelLevelPullback_comp (M N : levelThree) (F : KernelQuotientL2) :
    kernelLevelPullback M (kernelLevelPullback N F)=kernelLevelPullback (N*M) F := by
  have hcomp := (kernelLevelAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp
    (kernelLevelPullback_ae_eq N F)
  apply Lp.ext
  filter_upwards [kernelLevelPullback_ae_eq M (kernelLevelPullback N F),hcomp,
    kernelLevelPullback_ae_eq (N*M) F] with q hp hn hnm
  rw [hp,hnm]
  exact hn.trans (congrArg F (kernelLevelAction_mul N M q).symm)

lemma kernelLevelPullback_surjective (M : levelThree) : Function.Surjective (kernelLevelPullback M) := by
  intro F
  refine ⟨kernelLevelPullback M⁻¹ F,?_⟩
  rw [kernelLevelPullback_comp,inv_mul_cancel,kernelLevelPullback_one]

def kernelLevelUnitary (M : levelThree) : KernelQuotientL2 ≃ₗᵢ[ℂ] KernelQuotientL2 :=
  LinearIsometryEquiv.ofSurjective (kernelLevelPullback M) (kernelLevelPullback_surjective M)

lemma kernelLevelUnitary_apply (M : levelThree) (F : KernelQuotientL2) :
    kernelLevelUnitary M F=kernelLevelPullback M F := rfl

lemma kernelLevelPullback_defect (M : levelThree) (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    kernelLevelPullback M (kernelL2Defect a b ha hab s)=
      complexCharacter M • kernelL2Defect a b ha hab s := by
  have hdef := kernelL2Defect_ae_eq a b ha hab s
  have hcomp := (kernelLevelAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp hdef
  apply Lp.ext
  filter_upwards [kernelLevelPullback_ae_eq M (kernelL2Defect a b ha hab s),hcomp,hdef,
    Lp.coeFn_smul (complexCharacter M) (kernelL2Defect a b ha hab s)] with q hp hc hd hs
  change _=complexCharacter M * kernelL2Defect a b ha hab s q at hs
  rw [hp,hs,hd]
  exact hc.trans (kernelLevelAction_defect M a b s q)

lemma kernelLevelPullback_of_remainder_ae (M : levelThree) (a b : ℝ) (s : ℂ)
    (hs : 2<s.re) (F : KernelQuotientL2)
    (hF : F=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q) :
    kernelLevelPullback M F=complexCharacter M • F := by
  have hcomp := (kernelLevelAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp hF
  apply Lp.ext
  filter_upwards [kernelLevelPullback_ae_eq M F,hcomp,hF,Lp.coeFn_smul (complexCharacter M) F]
    with q hp hc hf hsmul
  change _=complexCharacter M*F q at hsmul
  rw [hp,hsmul,hf]
  dsimp only [Function.comp_def] at hc
  rw [hc,kernelLevelAction_eisenstein,kernelLevelAction_seed,mul_sub]

lemma kernelCorrection_character_of_initial_overlap (M : levelThree) (a b : ℝ)
    (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ, ∀hs : 4<s.re, 0<s.im →
      kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
        fun q => kernelQuotientEisenstein s (by linarith) q-kernelQuotientSeed a b s q) :
    ∀s∈cuspUpperParameterRegion,
      kernelLevelPullback M (kernelEisensteinL2Correction a b ha hab s)=
        complexCharacter M • kernelEisensteinL2Correction a b ha hab s := by
  have hc : AnalyticOnNhd ℂ (kernelEisensteinL2Correction a b ha hab) cuspUpperParameterRegion := by
    intro s hs
    exact kernelEisensteinL2Correction_analyticAt_nonreal a b ha hab s (by linarith [hs.1]) hs.2.ne'
  have hl : AnalyticOnNhd ℂ (fun s => kernelLevelPullback M (kernelEisensteinL2Correction a b ha hab s))
      cuspUpperParameterRegion := by
    intro s hs
    exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := KernelQuotientL2)
      (kernelLevelPullback M).toContinuousLinearMap _).comp_of_eq (hc s hs) rfl
  have hr : AnalyticOnNhd ℂ (fun s => complexCharacter M • kernelEisensteinL2Correction a b ha hab s)
      cuspUpperParameterRegion := by
    intro s hs
    exact (hc s hs).const_smul (c := complexCharacter M)
  have hV : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : (fun s => kernelLevelPullback M (kernelEisensteinL2Correction a b ha hab s))
      =ᶠ[𝓝 (5+Complex.I:ℂ)] (fun s => complexCharacter M • kernelEisensteinL2Correction a b ha hab s) := by
    filter_upwards [hV.mem_nhds (by norm_num)] with s hs
    exact kernelLevelPullback_of_remainder_ae M a b s (by linarith [hs.1]) _ (hoverlap s hs.1 hs.2)
  exact hl.eqOn_of_preconnected_of_eventuallyEq hr cuspUpperParameterRegion_convex.isPreconnected
    (by norm_num [cuspUpperParameterRegion]) hevent

lemma thetaApproach_tendsto_complex_punctured :
    Tendsto (fun t : ℝ => (4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I)
      (𝓝[>] (0:ℝ)) (𝓝[≠] (4/3:ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hh : Continuous (fun t : ℝ => (4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I) := by fun_prop
    have ht := (hh.tendsto 0).mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
    simpa only [Complex.ofReal_zero,zero_mul,add_zero] using ht
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    change (4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I≠(4/3:ℂ)
    intro he
    have him := congrArg Complex.im he
    simp at him
    linarith

lemma kernelEisensteinResidueVector_character_of_initial_overlap (M : levelThree) (a b : ℝ)
    (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ, ∀hs : 4<s.re, 0<s.im →
      kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
        fun q => kernelQuotientEisenstein s (by linarith) q-kernelQuotientSeed a b s q) :
    kernelLevelPullback M (kernelEisensteinResidueVector a b ha hab)=
      complexCharacter M • kernelEisensteinResidueVector a b ha hab := by
  have hlim := (kernelEisensteinResidueVector_limit a b ha hab).comp thetaApproach_tendsto_complex_punctured
  have hl := (kernelLevelPullback M).continuous.continuousAt.tendsto.comp hlim
  have hr := hlim.const_smul (complexCharacter M)
  have hevent :
      (fun t : ℝ => kernelLevelPullback M
        (((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I-4/3) •
          kernelEisensteinL2Correction a b ha hab ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I)))
      =ᶠ[𝓝[>] (0:ℝ)]
      (fun t : ℝ => complexCharacter M •
        (((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I-4/3) •
          kernelEisensteinL2Correction a b ha hab ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have hs : (4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I∈cuspUpperParameterRegion := by
      simp only [cuspUpperParameterRegion,Set.mem_ofPred_eq,Complex.add_re,Complex.add_im,
        Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
        Complex.I_im,mul_zero,mul_one,sub_zero,add_zero]
      norm_num
      exact ht
    rw [map_smul,kernelCorrection_character_of_initial_overlap M a b ha hab hoverlap _ hs]
    exact smul_comm _ _ _
  exact tendsto_nhds_unique_of_eventuallyEq hl hr hevent

lemma kernelCuspAverageFamily_eq_of_initial_overlap (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re)
    (hoverlap : kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q) :
    kernelCuspAverageFamily a b ha hab s=
      ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume := by
  have hcorrected : kernelCorrectedSeed a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelQuotientEisenstein s hs := by
    filter_upwards [hoverlap] with q hq
    change kernelQuotientSeed a b s q+kernelEisensteinL2Correction a b ha hab s q=_
    rw [hq]
    ring
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hrestr := ae_restrict_of_ae hcorrected (s := kernelCuspStripSet)
  have hp := hm.quasiMeasurePreserving.ae_eq_comp hrestr
  rw [kernelCuspAverageFamily_actual_integral]
  apply integral_congr_ae
  filter_upwards [hp] with w hw
  exact hw.trans (kernelQuotientEisenstein_mk s hs w)

lemma kernelEisensteinResidueVector_nonzero_character_of_initial_overlap (a b : ℝ)
    (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ, ∀hs : 4<s.re, 0<s.im →
      kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
        fun q => kernelQuotientEisenstein s (by linarith) q-kernelQuotientSeed a b s q) :
    kernelEisensteinResidueVector a b ha hab≠0 ∧
      ∀M : levelThree,kernelLevelPullback M (kernelEisensteinResidueVector a b ha hab)=
        complexCharacter M • kernelEisensteinResidueVector a b ha hab := by
  constructor
  · apply kernelEisensteinResidueVector_ne_zero_of_overlap a b ha hab
    intro s hs hi
    exact kernelCuspAverageFamily_eq_of_initial_overlap a b ha hab s (by linarith) (hoverlap s hs hi)
  · intro M
    exact kernelEisensteinResidueVector_character_of_initial_overlap M a b ha hab hoverlap

end CubicEisenstein

open scoped BigOperators
namespace QuadraticAllOddCRT
open ActualEisensteinCubic
open QuadraticGaussRay hiding O
open ActualEisensteinCoordinates hiding O omega
open EisensteinEPrimaryPhase (Coord odd)

def quadraticRayExponent (r : Coord) : ZMod 4 :=
  if r∈({(0,1),(0,3),(1,0),(1,1),(3,0),(3,3)} : Finset Coord) then 0
  else if r∈({(1,2),(1,3),(2,3)} : Finset Coord) then 1 else 3

def fourthRoot (a : ZMod 4) : ℂ := Complex.I^(a.val:ℤ)

lemma fourthRoot_add (a b : ZMod 4) : fourthRoot (a+b)=fourthRoot a*fourthRoot b := by
  unfold fourthRoot
  rw [←zpow_add₀ Complex.I_ne_zero]
  apply I_zpow_eq_of_mod_four
  push_cast
  simp

lemma quadraticRayValue_eq_fourthRoot (r : Coord) (hr : odd r) :
    quadraticRayValue r=fourthRoot (quadraticRayExponent r) := by
  have hcmp (a b : ZMod 4) : (a=b) ↔ (a.val=b.val) :=
    (ZMod.val_injective 4).eq_iff.symm
  have hcases : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
  rcases r with ⟨a,b⟩
  rcases hcases a with rfl | rfl | rfl | rfl <;>
    rcases hcases b with rfl | rfl | rfl | rfl <;>
    norm_num [EisensteinEPrimaryPhase.odd,ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] at hr <;>
    norm_num [quadraticRayExponent,fourthRoot,EisensteinEPrimaryPhase.odd,
      quadraticRayValue,breveGaussianFourTerms_formula,Prod.mk.injEq,hcmp,
      ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.val_ofNat,
      Complex.I_sq,Complex.I_pow_three,Complex.inv_I,zpow_neg] <;>
    ring_nf

def quadraticRaySign (r s : Coord) : ℤ :=
  if odd r ∧ odd s then
    if quadraticRayExponent (EisensteinEPrimaryPhase.mul r s)=
      quadraticRayExponent r+quadraticRayExponent s then 1 else -1
  else 0

lemma quadraticRaySign_mul_left (r s t : Coord) :
    quadraticRaySign (EisensteinEPrimaryPhase.mul r s) t=
      quadraticRaySign r t*quadraticRaySign s t := by
  have h : ∀r s t : Coord,
      quadraticRaySign (EisensteinEPrimaryPhase.mul r s) t=
        quadraticRaySign r t*quadraticRaySign s t := by decide
  exact h r s t

lemma quadraticRaySign_mul_right (r s t : Coord) :
    quadraticRaySign r (EisensteinEPrimaryPhase.mul s t)=
      quadraticRaySign r s*quadraticRaySign r t := by
  have h : ∀r s t : Coord,
      quadraticRaySign r (EisensteinEPrimaryPhase.mul s t)=
        quadraticRaySign r s*quadraticRaySign r t := by decide
  exact h r s t

lemma quadraticRaySign_symm (r s : Coord) : quadraticRaySign r s=quadraticRaySign s r := by
  have h : ∀r s : Coord,quadraticRaySign r s=quadraticRaySign s r := by decide
  exact h r s

lemma quadraticRaySign_sq (r s : Coord) (hr : odd r) (hs : odd s) :
    quadraticRaySign r s^2=1 := by
  unfold quadraticRaySign
  rw [ite_eq_left ⟨hr,hs⟩]
  split_ifs <;> norm_num

lemma quadraticRaySign_exponent (r s : Coord) (hr : odd r) (hs : odd s) :
    quadraticRayExponent (EisensteinEPrimaryPhase.mul r s)=
      (if quadraticRaySign r s=1 then 0 else 2)+quadraticRayExponent r+quadraticRayExponent s := by
  have h : ∀r s : Coord,odd r → odd s →
      quadraticRayExponent (EisensteinEPrimaryPhase.mul r s)=
        (if quadraticRaySign r s=1 then 0 else 2)+quadraticRayExponent r+quadraticRayExponent s := by decide
  exact h r s hr hs

lemma quadraticRaySign_root (r s : Coord) (hr : odd r) (hs : odd s) :
    fourthRoot (if quadraticRaySign r s=1 then 0 else 2)=(quadraticRaySign r s:ℂ) := by
  by_cases he : quadraticRayExponent (EisensteinEPrimaryPhase.mul r s)=
      quadraticRayExponent r+quadraticRayExponent s
  · norm_num [quadraticRaySign,hr,hs,he,fourthRoot,ZMod.val_zero,ZMod.val_ofNat,Complex.I_sq]
  · norm_num [quadraticRaySign,hr,hs,he,fourthRoot,ZMod.val_zero,ZMod.val_ofNat,Complex.I_sq]

lemma odd_mul (r s : Coord) (hr : odd r) (hs : odd s) : odd (EisensteinEPrimaryPhase.mul r s) := by
  have h : ∀r s : Coord,odd r → odd s → odd (EisensteinEPrimaryPhase.mul r s) := by decide
  exact h r s hr hs

theorem quadraticRayValue_mul (r s : Coord) (hr : odd r) (hs : odd s) :
    quadraticRayValue (EisensteinEPrimaryPhase.mul r s)=
      (quadraticRaySign r s:ℂ)*quadraticRayValue r*quadraticRayValue s := by
  rw [quadraticRayValue_eq_fourthRoot _ (odd_mul r s hr hs),quadraticRaySign_exponent r s hr hs,
    fourthRoot_add,fourthRoot_add,quadraticRaySign_root r s hr hs,
    quadraticRayValue_eq_fourthRoot r hr,quadraticRayValue_eq_fourthRoot s hs]

lemma quadraticRayPair_eq_sign (r s : Coord) (hr : odd r) (hs : odd s) :
    MixedCrossSeparation.quadraticRayPair r s=(quadraticRaySign r s:ℂ) := by
  unfold MixedCrossSeparation.quadraticRayPair
  rw [quadraticRayValue_mul r s hr hs]
  apply (div_eq_iff (mul_ne_zero (quadraticRayValue_ne_zero_of_odd r hr)
    (quadraticRayValue_ne_zero_of_odd s hs))).mpr
  ring

end QuadraticAllOddCRT

open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open CanonicalQuadraticSieve hiding O
open CubicJacobiGlobal hiding O
open QuadraticGaussRay hiding O
open QuadraticAllOddCRT
open ActualEisensteinCoordinates hiding O omega
open UniqueFactorizationMonoid

lemma supported_factors_good (I : Ideal ActualEisensteinCubic.O) (hI : Supported I) :
    ∀P∈normalizedFactors I,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2 := by
  intro P hP
  have hp := prime_of_normalized_factor P hP
  exact ⟨(Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero,hI.2 P hP⟩

lemma idealRowHom_one_supported (I : Ideal ActualEisensteinCubic.O) (hI : Supported I) : idealRowHom 1 I=1 := by
  have h := CanonicalUnitEuler.idealRowHom_unit_norm (1:ActualEisensteinCubic.Oˣ) I hI.1 (supported_factors_good I hI)
  simpa using h

lemma supported_prime_data (p : ActualEisensteinCubic.O) (hp : Prime p) (hs : Supported (Ideal.span {p})) :
    lambda∉(Ideal.span {p}:Ideal ActualEisensteinCubic.O) ∧ ringChar (ActualEisensteinCubic.O⧸Ideal.span {p})≠2 := by
  let : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  exact hs.2 _ ((Ideal.mem_normalizedFactors_iff hs.1).mpr ⟨inferInstance,le_rfl⟩)

lemma supported_residue_odd (p : ActualEisensteinCubic.O) (hs : Supported (Ideal.span {p})) : EisensteinEPrimaryPhase.odd (residue p) :=
  (ActualEisensteinCoordinates.odd_residue_iff_not_two_dvd p).mpr ((supported_span_iff p).mp hs).2

theorem idealRowHom_prime_reciprocity (p q : ActualEisensteinCubic.O) (hp : Prime p) (hq : Prime q)
    (hprimaryP : lambda^2∣p-1) (hprimaryQ : lambda^2∣q-1)
    (hsP : Supported (Ideal.span {p})) (hsQ : Supported (Ideal.span {q})) :
    idealRowHom q (Ideal.span {p})=
      (quadraticRaySign (residue p) (residue q):ℂ)*idealRowHom p (Ideal.span {q}) := by
  let : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let : (Ideal.span {q}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hq.irreducible
  obtain ⟨hgP,hcP⟩ := supported_prime_data p hp hsP
  obtain ⟨hgQ,hcQ⟩ := supported_prime_data q hq hsQ
  by_cases he : (Ideal.span {p}:Ideal ActualEisensteinCubic.O)=Ideal.span {q}
  · have hqp : q∈(Ideal.span {p}:Ideal ActualEisensteinCubic.O) := by rw [he];exact Ideal.subset_span (by simp)
    have hpq : p∈(Ideal.span {q}:Ideal ActualEisensteinCubic.O) := by rw [←he];exact Ideal.subset_span (by simp)
    rw [idealRowHom_prime q _ hgP,idealRowHom_prime p _ hgQ,
      Ideal.Quotient.eq_zero_iff_mem.mpr hqp,Ideal.Quotient.eq_zero_iff_mem.mpr hpq]
    simp only [MulChar.map_zero,mul_zero]
  · have hcop : IsCoprime (Ideal.span {p}:Ideal ActualEisensteinCubic.O) (Ideal.span {q}) := Ideal.isCoprime_of_isMaximal he
    have hqp : q∉(Ideal.span {p}:Ideal ActualEisensteinCubic.O) := by
      intro h
      apply he
      exact ((inferInstance : (Ideal.span {q}:Ideal ActualEisensteinCubic.O).IsMaximal).eq_of_le
        (Ideal.IsMaximal.ne_top inferInstance)
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h))).symm
    have h2 : idealRowHom q (Ideal.span {p})^2=idealRowHom p (Ideal.span {q})^2 := by
      rw [idealRowHom_square,idealRowHom_square]
      exact congrArg ConcreteTraceCRT.eisEmbedding (symbol_reciprocity q p hq.ne_zero hp.ne_zero hprimaryQ hprimaryP)
    have h6 : idealRowHom q (Ideal.span {p})^6=1 := by
      rw [idealRowHom_prime q _ hgP]
      have h := canonicalSextic_sixth_power_mask (Ideal.span {p}) hgP q
      change actualSextic _ hgP (Ideal.Quotient.mk _ (q^6))=_ at h
      simpa only [map_pow,ite_eq_right hqp] using h
    have hcross := quadratic_ray_cross p q hp.ne_zero hq.ne_zero hcop hcP hcQ
    rw [residue_mul,quadraticRayValue_mul _ _ (supported_residue_odd p hsP) (supported_residue_odd q hsQ)] at hcross
    have h3 (x y : ActualEisensteinCubic.O) (hg : lambda∉(Ideal.span {x}:Ideal ActualEisensteinCubic.O)) [(Ideal.span {x}).IsMaximal] :
        idealRowHom y (Ideal.span {x})^3=
          character (Ideal.span {x}) (Ideal.Quotient.mk (Ideal.span {x}) y) := by
      rw [idealRowHom_prime y _ hg,←MulChar.pow_apply' _ (by decide : (3:ℕ)≠0),actualSextic_cube_quadratic]
    have hc : idealRowHom q (Ideal.span {p})^3*idealRowHom p (Ideal.span {q})^3=
        (quadraticRaySign (residue p) (residue q):ℂ) := by
      rw [h3 p q hgP,h3 q p hgQ]
      apply mul_right_cancel₀ (quadraticRayValue_ne_zero_of_odd _ (supported_residue_odd p hsP))
      apply mul_right_cancel₀ (quadraticRayValue_ne_zero_of_odd _ (supported_residue_odd q hsQ))
      simpa only [mul_assoc,mul_left_comm,mul_comm] using hcross.symm
    calc
      _ = idealRowHom q (Ideal.span {p})*idealRowHom q (Ideal.span {p})^6 := by rw [h6,mul_one]
      _ = idealRowHom q (Ideal.span {p})^3*(idealRowHom q (Ideal.span {p})^2)^2 := by ring
      _ = idealRowHom q (Ideal.span {p})^3*(idealRowHom p (Ideal.span {q})^2)^2 := by rw [h2]
      _ = (idealRowHom q (Ideal.span {p})^3*idealRowHom p (Ideal.span {q})^3)*idealRowHom p (Ideal.span {q}) := by ring
      _ = _ := by rw [hc]

end

open ActualEisensteinCubic
open CompletedGauss hiding O
open CanonicalQuadraticSieve hiding O
open CubicJacobiGlobal hiding O
open QuadraticAllOddCRT
open ActualEisensteinCoordinates hiding O omega

def sexticReciprocityPhase (a b : ActualEisensteinCubic.O) : ℂ :=
  (quadraticRaySign (residue a) (residue b):ℂ)

lemma sexticReciprocityPhase_mul_left (a b c : ActualEisensteinCubic.O) :
    sexticReciprocityPhase (a*b) c=sexticReciprocityPhase a c*sexticReciprocityPhase b c := by
  simp only [sexticReciprocityPhase,residue_mul,quadraticRaySign_mul_left,Int.cast_mul]

lemma sexticReciprocityPhase_mul_right (a b c : ActualEisensteinCubic.O) :
    sexticReciprocityPhase a (b*c)=sexticReciprocityPhase a b*sexticReciprocityPhase a c := by
  simp only [sexticReciprocityPhase,residue_mul,quadraticRaySign_mul_right,Int.cast_mul]

lemma sexticReciprocityPhase_one_right (a : ActualEisensteinCubic.O) (ha : Supported (Ideal.span {a})) :
    sexticReciprocityPhase a 1=1 := by
  have h1 : residue (1:ActualEisensteinCubic.O)=((1:ZMod 4),0) := by
    have h : (1:ActualEisensteinCubic.O)=eval 1 0 := by simp [eval]
    rw [h,residue_eval]
    norm_num
  have ht : ∀r : EisensteinEPrimaryPhase.Coord,EisensteinEPrimaryPhase.odd r →
      quadraticRaySign r ((1:ZMod 4),0)=1 := by decide
  simp only [sexticReciprocityPhase,h1,ht _ (supported_residue_odd a ha),Int.cast_one]

lemma sexticReciprocityPhase_one_left (a : ActualEisensteinCubic.O) (ha : Supported (Ideal.span {a})) :
    sexticReciprocityPhase 1 a=1 := by
  have he : sexticReciprocityPhase 1 a=sexticReciprocityPhase a 1 := by
    simp only [sexticReciprocityPhase,quadraticRaySign_symm]
  rw [he,sexticReciprocityPhase_one_right a ha]

lemma idealRowHom_prime_primary_reciprocity (p b : ActualEisensteinCubic.O) (hp : Prime p)
    (hprimaryP : lambda^2∣p-1) (hprimaryB : lambda^2∣b-1)
    (hsP : Supported (Ideal.span {p})) (hsB : Supported (Ideal.span {b})) :
    idealRowHom b (Ideal.span {p})=sexticReciprocityPhase p b*idealRowHom p (Ideal.span {b}) := by
  have hb0 : b≠0 := by
    intro h
    apply hsB.1
    simp [h]
  obtain ⟨s,hprod,hfactors⟩ := exists_primary_prime_factorization b hb0 hprimaryB
  rw [←hprod] at hsB ⊢
  clear hprod hb0 hprimaryB b
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.prod_zero,Ideal.span_singleton_one,←Ideal.one_eq_top,map_one,
      idealRowHom_one_supported _ hsP,sexticReciprocityPhase_one_right p hsP,mul_one]
  | @cons q s ih =>
    have hq := hfactors q (Multiset.mem_cons_self _ _)
    have htail : ∀r∈s,Prime r ∧ lambda^2∣r-1 := fun r hr => hfactors r (Multiset.mem_cons_of_mem hr)
    have hsplit : Supported (Ideal.span {q}) ∧ Supported (Ideal.span {s.prod}) := by
      simpa only [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,supported_mul_iff] using hsB
    rw [Multiset.prod_cons,idealRowHom_argument_mul,←Ideal.span_singleton_mul_span_singleton,
      map_mul,sexticReciprocityPhase_mul_right,
      idealRowHom_prime_reciprocity p q hp hq.1 hprimaryP hq.2 hsP hsplit.1,
      ih hsplit.2 htail]
    simp only [sexticReciprocityPhase]
    ring

theorem idealRowHom_primary_reciprocity (a b : ActualEisensteinCubic.O)
    (hprimaryA : lambda^2∣a-1) (hprimaryB : lambda^2∣b-1)
    (hsA : Supported (Ideal.span {a})) (hsB : Supported (Ideal.span {b})) :
    idealRowHom b (Ideal.span {a})=sexticReciprocityPhase a b*idealRowHom a (Ideal.span {b}) := by
  have ha0 : a≠0 := by
    intro h
    apply hsA.1
    simp [h]
  obtain ⟨s,hprod,hfactors⟩ := exists_primary_prime_factorization a ha0 hprimaryA
  rw [←hprod] at hsA ⊢
  clear hprod ha0 hprimaryA a
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.prod_zero,Ideal.span_singleton_one,←Ideal.one_eq_top,map_one,
      idealRowHom_one_supported _ hsB,sexticReciprocityPhase_one_left b hsB,one_mul]
  | @cons p s ih =>
    have hp := hfactors p (Multiset.mem_cons_self _ _)
    have htail : ∀r∈s,Prime r ∧ lambda^2∣r-1 := fun r hr => hfactors r (Multiset.mem_cons_of_mem hr)
    have hsplit : Supported (Ideal.span {p}) ∧ Supported (Ideal.span {s.prod}) := by
      simpa only [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,supported_mul_iff] using hsA
    rw [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,map_mul,
      idealRowHom_argument_mul,sexticReciprocityPhase_mul_left,
      idealRowHom_prime_primary_reciprocity p b hp.1 hp.2 hprimaryB hsplit.1 hsB,
      ih hsplit.2 htail]
    ring

theorem idealRowHom_primary_reciprocity_ray (a b : ActualEisensteinCubic.O)
    (hprimaryA : lambda^2∣a-1) (hprimaryB : lambda^2∣b-1)
    (hsA : Supported (Ideal.span {a})) (hsB : Supported (Ideal.span {b})) :
    idealRowHom b (Ideal.span {a})=
      MixedCrossSeparation.quadraticRayPair (residue a) (residue b)*idealRowHom a (Ideal.span {b}) := by
  rw [quadraticRayPair_eq_sign _ _ (supported_residue_odd a hsA) (supported_residue_odd b hsB)]
  exact idealRowHom_primary_reciprocity a b hprimaryA hprimaryB hsA hsB

theorem idealRowHom_ideal_reciprocity (I J : Ideal ActualEisensteinCubic.O) (hI : Supported I) (hJ : Supported J) :
    idealRowHom (primaryGenerator J) I=
      sexticReciprocityPhase (primaryGenerator I) (primaryGenerator J)*idealRowHom (primaryGenerator I) J := by
  have hpI := primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)
  have hpJ := primaryGenerator_spec J (supported_primaryGenerator_ne_zero J hJ)
  have h := idealRowHom_primary_reciprocity (primaryGenerator I) (primaryGenerator J)
    hpI.2 hpJ.2 (by rwa [hpI.1]) (by rwa [hpJ.1])
  simpa only [hpI.1,hpJ.1] using h

end CanonicalRowCompletion

end

end OAI
end OAIOriginalModule0257

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.CutoffApproximation
Source SHA256: 26d2893e506db572e630ae50c9ce32ec42f561f3ed90c9892155a925ccff0a6f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0258


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

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

section BoundedConvergence
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] («μ» : Measure α)

omit [CompleteSpace E] in
lemma l2_norm_sq_integral (f : Lp E 2 «μ») : ‖f‖^2=∫a,‖f a‖^2∂«μ» := by
  calc
    ‖f‖^2=inner ℝ f f := (real_inner_self_eq_norm_sq f).symm
    _ = ∫a,inner ℝ (f a) (f a)∂«μ» := L2.inner_def _ _
    _ = _ := by simp only [real_inner_self_eq_norm_sq]

omit [CompleteSpace E] in
lemma l2_toLp_sub_norm_sq (f g : α→E) (hf : MemLp f 2 «μ») (hg : MemLp g 2 «μ») :
    ‖hf.toLp f-hg.toLp g‖^2=∫a,‖f a-g a‖^2∂«μ» := by
  rw [l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g),hf.coeFn_toLp,hg.coeFn_toLp] with a ha hf hg
  rw [ha]
  simp only [Pi.sub_apply,hf,hg]

omit [CompleteSpace E] in
theorem l2_tendsto_of_bounded_eventuallyEq [IsFiniteMeasure «μ»]
    (f : ℕ→α→E) (g : α→E) (hf : ∀n,MemLp (f n) 2 «μ») (hg : MemLp g 2 «μ»)
    (B C : ℝ) (hB : 0≤B) (hC : 0≤C)
    (hfB : ∀n a,‖f n a‖≤B) (hgC : ∀a,‖g a‖≤C)
    (hlim : ∀a,∀ᶠn : ℕ in atTop,f n a=g a) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  have hsq : Tendsto (fun n => ∫a,‖f n a-g a‖^2∂«μ») atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence («μ» := «μ»)
      (F := fun n a => ‖f n a-g a‖^2) (f := fun _ => (0:ℝ)) (fun _ => (B+C)^2)
      (fun n => ((hf n).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm.pow 2)
      (integrable_const _) ?_ ?_
    · simpa only [integral_zero] using h
    · intro n
      exact Eventually.of_forall (fun a => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg hB hC)).mpr
        exact (norm_sub_le _ _).trans (add_le_add (hfB n a) (hgC a)))
    · exact Eventually.of_forall (fun a => by
        apply tendsto_const_nhds.congr'
        filter_upwards [hlim a] with n hn
        simp only [hn,sub_self,norm_zero,zero_pow (by decide : 2≠0)])
  have hn : Tendsto (fun n => ‖(hf n).toLp (f n)-hg.toLp g‖^2) atTop (𝓝 0) := by
    simpa only [l2_toLp_sub_norm_sq] using hsq
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hsqrt

end BoundedConvergence

instance kernelFundamentalVolume_finite : IsFiniteMeasure KernelFundamentalVolume := by
  refine ⟨?_⟩
  change (hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)) Set.univ<⊤
  rw [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter]
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  exact hyperbolicFundamentalSet_volume_lt_top globalKubotaKernel globalKubotaKernel_le_levelThree

def kernelFunctionField (f : KernelQuotient→ℂ) (p : EuclideanSpatial) : ℂ :=
  f (kernelEuclideanProjection p)

lemma kernelFunctionField_smooth (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (kernelFunctionField f) p :=
  (((hf.comp kernelProjection_contMDiff) (euclideanToHyperbolic p)).comp p
    (euclideanToHyperbolic_contMDiffAt p hp)).contDiffAt

def kernelFunctionGradient (f : KernelQuotient→ℂ) (w : HyperbolicSpace) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 (fun j => (hyperbolicHeight w:ℂ)*
    fderiv ℝ (kernelFunctionField f) (hyperbolicEuclideanCoordinates w) (euclideanCoordinateVector j))

lemma kernelFunctionGradient_continuous (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f) :
    Continuous (kernelFunctionGradient f) := by
  apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm.continuous.comp
  apply continuous_pi
  intro j
  apply (Complex.continuous_ofReal.comp hyperbolicHeight_continuous).mul
  rw [continuous_iff_continuousAt]
  intro w
  exact (((kernelFunctionField_smooth f hf _ (hyperbolicHeight_pos w)).continuousAt_fderiv
    (by simp)).clm_apply continuousAt_const).comp hyperbolicEuclideanCoordinates_continuous.continuousAt

lemma norm_three_vector_bound (v : EuclideanSpace ℂ (Fin 3)) (B : ℝ) (hB : 0≤B)
    (hv : ∀j,‖v j‖≤B) : ‖v‖≤3*B := by
  have hsq : ‖v‖^2≤3*B^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑j : Fin 3,B^2 := Finset.sum_le_sum (fun j hj =>
        (sq_le_sq₀ (norm_nonneg _) hB).mpr (hv j))
      _ = _ := by simp
  nlinarith [norm_nonneg v,sq_nonneg B]

lemma kernelFunctionGradient_bound (f : KernelQuotient→ℂ) (B : ℝ) (hB : 0≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤B)
    (w : HyperbolicSpace) : ‖kernelFunctionGradient f w‖≤3*B := by
  apply norm_three_vector_bound _ B hB
  intro j
  exact hgrad (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w) j

lemma kernelFunctionGradient_memLp (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (B : ℝ) (hB : 0≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤B) :
    MemLp (kernelFunctionGradient f) 2 KernelFundamentalVolume :=
  MemLp.of_bound (kernelFunctionGradient_continuous f hf).aestronglyMeasurable (3*B)
    (Eventually.of_forall (kernelFunctionGradient_bound f B hB hgrad))

def kernelFunctionCutoff (n : ℕ) (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f) : kernelSmoothTests := by
  refine ⟨fun q => (kernelExhaustionCutoff n q:ℂ)*f q,?_,?_⟩
  · have hm : ContDiff ℝ ∞ (fun z : ℂ × ℂ => z.1*z.2) := contDiff_fst.mul contDiff_snd
    exact hm.contMDiff.comp
      ((Complex.ofRealCLM.contDiff.contMDiff.comp (kernelExhaustionCutoff_smooth n)).prodMk_space hf)
  · apply HasCompactSupport.of_support_subset_isCompact (kernelExhaustionCutoff_hasCompactSupport n)
    intro q hq
    by_contra hn
    have hz : kernelExhaustionCutoff n q=0 := image_eq_zero_of_notMem_tsupport hn
    exact hq (by simp [hz])

lemma kernelFunctionCutoff_apply (n : ℕ) (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f) (q : KernelQuotient) :
    (kernelFunctionCutoff n f hf).1 q=(kernelExhaustionCutoff n q:ℂ)*f q := rfl

lemma kernelFunctionCutoff_field (n : ℕ) (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f) :
    kernelTestField (kernelFunctionCutoff n f hf)=
      fun p => (kernelExhaustionCutoff n (kernelEuclideanProjection p):ℂ)*kernelFunctionField f p := rfl

lemma kernelFunctionGradient_of_test (f : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelFunctionGradient f.1 w=kernelGradientAt w f := by
  unfold kernelFunctionGradient
  simp only [euclideanCoordinateVector_eq_basis]
  rfl

lemma kernelFunctionCutoff_field_eventually (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    ∀ᶠn : ℕ in atTop,kernelTestField (kernelFunctionCutoff n f hf)=ᶠ[𝓝 p]kernelFunctionField f := by
  have hc : ContinuousAt kernelEuclideanProjection p :=
    (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp
      (euclideanToHyperbolic_contMDiffAt p hp).continuousAt
  filter_upwards [kernelExhaustionCutoff_eventually_one_near (kernelEuclideanProjection p)] with n hn
  filter_upwards [hn.comp_tendsto hc] with q hq
  change kernelExhaustionCutoff n (kernelEuclideanProjection q)=1 at hq
  change (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)*kernelFunctionField f q=kernelFunctionField f q
  rw [hq]
  simp

lemma kernelFunctionCutoff_gradient_eventually (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f) (w : HyperbolicSpace) :
    ∀ᶠn : ℕ in atTop,kernelGradientAt w (kernelFunctionCutoff n f hf)=kernelFunctionGradient f w := by
  filter_upwards [kernelFunctionCutoff_field_eventually f hf
    (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)] with n hn
  apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
  funext j
  change (hyperbolicHeight w:ℂ)*fderiv ℝ (kernelTestField (kernelFunctionCutoff n f hf)) _ _=
    (hyperbolicHeight w:ℂ)*fderiv ℝ (kernelFunctionField f) _ _
  rw [hn.fderiv_eq,euclideanCoordinateVector_eq_basis]

lemma kernelFunctionCutoff_mass_bound (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (B : ℝ) (_hB : 0≤B) (hbound : ∀q,‖f q‖≤B) (n : ℕ) (q : KernelQuotient) :
    ‖(kernelFunctionCutoff n f hf).1 q‖≤B := by
  rw [kernelFunctionCutoff_apply,norm_mul,Complex.norm_of_nonneg (kernelExhaustionCutoff_bounds n q).1]
  exact (mul_le_mul (kernelExhaustionCutoff_bounds n q).2 (hbound q) (norm_nonneg _) zero_le_one).trans_eq (one_mul B)

lemma kernelFunctionCutoff_scaled_deriv_bound (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (B G D : ℝ) (hB : 0≤B) (hfB : ∀q,‖f q‖≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G)
    (hcut : ∀n : ℕ,∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (fun q => (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)) p
        (euclideanCoordinateVector j)‖≤D)
    (n : ℕ) (p : EuclideanSpatial) (hp : 0<p 2) (j : Fin 3) :
    ‖(p 2:ℂ)*fderiv ℝ (kernelTestField (kernelFunctionCutoff n f hf)) p (euclideanCoordinateVector j)‖≤G+B*D := by
  let c : EuclideanSpatial→ℂ:=fun q => (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)
  have hc : DifferentiableAt ℝ c p :=
    (kernelFunctionField_smooth (fun q => (kernelExhaustionCutoff n q:ℂ))
      (Complex.ofRealCLM.contDiff.contMDiff.comp (kernelExhaustionCutoff_smooth n)) p hp).differentiableAt (by simp)
  have hd := (kernelFunctionField_smooth f hf p hp).differentiableAt (by simp)
  rw [kernelFunctionCutoff_field,fderiv_fun_mul hc hd]
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  have he : (p 2:ℂ)*(c p*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)+
      kernelFunctionField f p*fderiv ℝ c p (euclideanCoordinateVector j))=
      c p*((p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j))+
        kernelFunctionField f p*((p 2:ℂ)*fderiv ℝ c p (euclideanCoordinateVector j)) := by ring
  change ‖(p 2:ℂ)*(c p*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)+
      kernelFunctionField f p*fderiv ℝ c p (euclideanCoordinateVector j))‖≤_
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul]
  have hc1 : ‖c p‖≤1 := by
    rw [Complex.norm_of_nonneg (kernelExhaustionCutoff_bounds n _).1]
    exact (kernelExhaustionCutoff_bounds n _).2
  have hleft : ‖c p‖*‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G :=
    (mul_le_mul hc1 (hgrad p hp j) (norm_nonneg _) zero_le_one).trans_eq (one_mul G)
  have hright : ‖kernelFunctionField f p‖*‖(p 2:ℂ)*fderiv ℝ c p (euclideanCoordinateVector j)‖≤B*D :=
    mul_le_mul (hfB (kernelEuclideanProjection p)) (hcut n p hp j) (norm_nonneg _) hB
  simpa only [norm_mul] using add_le_add hleft hright

lemma kernelFunctionCutoff_gradient_bound (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (B G : ℝ) (hB : 0≤B) (hG : 0≤G) (hfB : ∀q,‖f q‖≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G) :
    ∃D : ℝ,0≤D ∧ ∀n : ℕ,∀w : HyperbolicSpace,‖kernelGradientAt w (kernelFunctionCutoff n f hf)‖≤D := by
  obtain ⟨D,hD,hcut⟩ := kernelExhaustionCutoff_scaled_fderiv_bound
  refine ⟨3*(G+B*D),by positivity,?_⟩
  intro n w
  apply norm_three_vector_bound _ (G+B*D) (by positivity)
  intro j
  change ‖(hyperbolicHeight w:ℂ)*fderiv ℝ (kernelTestField (kernelFunctionCutoff n f hf))
    (hyperbolicEuclideanCoordinates w) (EuclideanSpace.basisFun (Fin 3) ℝ j)‖≤_
  rw [←euclideanCoordinateVector_eq_basis]
  exact kernelFunctionCutoff_scaled_deriv_bound f hf B G D hB hfB hgrad hcut n
    (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w) j

theorem kernelFunctionCutoff_mass_tendsto (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (hfL : MemLp f 2 (integralQuotientVolume globalKubotaKernel))
    (B : ℝ) (hB : 0≤B) (hbound : ∀q,‖f q‖≤B) :
    Tendsto (fun n => kernelSmoothTestsToL2 (kernelFunctionCutoff n f hf)) atTop (𝓝 (hfL.toLp f)) := by
  apply l2_tendsto_of_bounded_eventuallyEq (integralQuotientVolume globalKubotaKernel)
    (fun n => (kernelFunctionCutoff n f hf).1) f
    (fun n => kernelSmoothTests_memLp (kernelFunctionCutoff n f hf)) hfL B B hB hB
    (kernelFunctionCutoff_mass_bound f hf B hB hbound) hbound
  intro q
  filter_upwards [kernelExhaustionCutoff_eventually_one q] with n hn
  rw [kernelFunctionCutoff_apply,hn]
  simp

theorem kernelFunctionCutoff_gradient_tendsto (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (hgL : MemLp (kernelFunctionGradient f) 2 KernelFundamentalVolume)
    (B G : ℝ) (hB : 0≤B) (hG : 0≤G) (hfB : ∀q,‖f q‖≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G) :
    Tendsto (fun n => kernelGradientToL2 (kernelFunctionCutoff n f hf)) atTop
      (𝓝 (hgL.toLp (kernelFunctionGradient f))) := by
  obtain ⟨D,hD,hbound⟩ := kernelFunctionCutoff_gradient_bound f hf B G hB hG hfB hgrad
  apply l2_tendsto_of_bounded_eventuallyEq KernelFundamentalVolume
    (fun n w => kernelGradientAt w (kernelFunctionCutoff n f hf)) (kernelFunctionGradient f)
    (fun n => kernelGradientAt_memLp (kernelFunctionCutoff n f hf)) hgL D (3*G) hD (by positivity)
    hbound (kernelFunctionGradient_bound f G hG hgrad)
  exact kernelFunctionCutoff_gradient_eventually f hf

theorem kernel_bounded_smooth_energy_exists (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (hfL : MemLp f 2 (integralQuotientVolume globalKubotaKernel))
    (hgL : MemLp (kernelFunctionGradient f) 2 KernelFundamentalVolume)
    (B G : ℝ) (hB : 0≤B) (hG : 0≤G) (hfB : ∀q,‖f q‖≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G) :
    ∃u : KernelEnergyGraph,kernelEnergyMass u=hfL.toLp f ∧
      kernelEnergyGradient u=hgL.toLp (kernelFunctionGradient f) := by
  let x : KernelEnergyAmbient:=WithLp.toLp 2 (hfL.toLp f,hgL.toLp (kernelFunctionGradient f))
  have hm := kernelFunctionCutoff_mass_tendsto f hf hfL B hB hfB
  have hg := kernelFunctionCutoff_gradient_tendsto f hf hgL B G hB hG hfB hgrad
  have hp := hm.prodMk_nhds hg
  have ht : Tendsto (fun n => kernelEnergyCore (kernelFunctionCutoff n f hf)) atTop (𝓝 x) := by
    have h := (WithLp.prodContinuousLinearEquiv 2 ℂ KernelQuotientL2 KernelGradientL2).symm.continuous.continuousAt.tendsto.comp hp
    exact h
  have hx : x∈kernelEnergyGraphSubmodule := by
    change x∈closure (Set.range kernelEnergyCore)
    exact mem_closure_of_tendsto ht (Eventually.of_forall (fun n => ⟨kernelFunctionCutoff n f hf,rfl⟩))
  exact ⟨⟨x,hx⟩,rfl,rfl⟩

def kernelEisensteinRemainderL2 (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) : KernelQuotientL2 :=
  (kernel_eisenstein_sub_seed_memLp a b ha.le hab s hs).toLp
    (kernelEisensteinRemainder a b s (by linarith))

lemma kernelEisensteinRemainderL2_ae (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    kernelEisensteinRemainderL2 a b ha hab s hs=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelEisensteinRemainder a b s (by linarith) :=
  (kernel_eisenstein_sub_seed_memLp a b ha.le hab s hs).coeFn_toLp

theorem kernelEisensteinRemainder_energy (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    ∃u : KernelEnergyGraph,kernelEnergyMass u=kernelEisensteinRemainderL2 a b ha hab s hs := by
  let f := kernelEisensteinRemainder a b s (by linarith)
  have hf := kernelEisensteinRemainder_smooth a b ha hab s (by linarith)
  have hfL : MemLp f 2 (integralQuotientVolume globalKubotaKernel) :=
    kernel_eisenstein_sub_seed_memLp a b ha.le hab s hs
  have hfB : ∀q,‖f q‖≤eisensteinRemainderBound b s := by
    intro q
    induction q using Quotient.inductionOn with
    | _ w => exact eisenstein_sub_seed_bounded a b ha.le hab s hs w
  obtain ⟨G,hG,hgrad⟩ := kernelEisensteinRemainder_scaled_fderiv_bound a b ha hab s hs
  have hgrad' : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G := hgrad
  have hgL := kernelFunctionGradient_memLp f hf G hG hgrad'
  obtain ⟨u,hu,hgu⟩ := kernel_bounded_smooth_energy_exists f hf hfL hgL
    (eisensteinRemainderBound b s) G (eisensteinRemainderBound_nonneg b s) hG hfB hgrad'
  exact ⟨u,hu⟩

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold Matrix

lemma axis_update_contDiff (p : SpatialCoordinates) (j : Fin 3) :
    ContDiff ℝ ∞ (fun t => Function.update p j t) := by
  apply contDiff_pi.mpr
  intro k
  by_cases h : k=j
  · subst k
    simpa only [Function.update_self,id_eq] using! (contDiff_id : ContDiff ℝ ∞ (fun t : ℝ => t))
  · simpa only [Function.update_of_ne h] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => p k))

lemma smooth_positive_axis_regular (f : SpatialCoordinates→ℂ)
    (hf : ∀p,0<p 2→ContDiffAt ℝ ∞ f p) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    DifferentiableAt ℝ (axisSlice f p j) (p j) ∧
      DifferentiableAt ℝ (deriv (axisSlice f p j)) (p j) := by
  have hh : ContDiffAt ℝ ∞ (axisSlice f p j) (p j) := by
    have hfp : ContDiffAt ℝ ∞ f (Function.update p j (p j)) := by
      simpa only [Function.update_eq_self] using hf p hp
    have h := hfp.comp (p j) (axis_update_contDiff p j).contDiffAt
    simpa only [axisSlice,Function.comp_def,Function.update_eq_self] using! h
  exact ⟨hh.differentiableAt (by simp),(hh.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)⟩

lemma axisLaplacian_sub_smooth (f g : SpatialCoordinates→ℂ)
    (hf : ∀p,0<p 2→ContDiffAt ℝ ∞ f p) (hg : ∀p,0<p 2→ContDiffAt ℝ ∞ g p)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (fun q => f q-g q) p=axisLaplacian f p-axisLaplacian g p := by
  let F : Fin 2→SpatialCoordinates→ℂ:=![f,fun q => (-1:ℂ)*g q]
  have hF : ∀i : Fin 2,∀q,0<q 2→ContDiffAt ℝ ∞ (F i) q := by
    intro i q hq
    fin_cases i
    · exact hf q hq
    · exact contDiffAt_const.mul (hg q hq)
  have hh := axisLaplacian_finset_sum Finset.univ F
    (fun i hi q hq j => smooth_positive_axis_regular (F i) (hF i) q hq j) p hp
  have he : (fun q => ∑i : Fin 2,F i q)=(fun q => f q-g q) := by
    funext q
    simp [F,Fin.sum_univ_two,sub_eq_add_neg]
  rw [he] at hh
  simp only [Fin.sum_univ_two,F,Matrix.cons_val_zero,Matrix.cons_val_one] at hh
  rw [axisLaplacian_const_mul] at hh
  simpa only [neg_one_mul,sub_eq_add_neg] using hh

lemma eisensteinRemainder_coordinate_equation (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (p : SpatialCoordinates) (hp : 0<p 2) :
    -axisLaplacian (eisensteinRemainderField a b s) p=
      smoothCuspSeedDefectField a b s p+s*(2-s)*eisensteinRemainderField a b s p := by
  have hD := actual_smoothCuspSeed_laplace_defect a b s ha hab p hp
  unfold eisensteinRemainderField
  rw [axisLaplacian_sub_smooth _ _ (smoothEisenstein_contDiffAt s hs)
    (actual_smoothCuspSeed_contDiffAt a b s ha hab) p hp,smoothEisenstein_eigenfunction s hs p hp]
  linear_combination hD

lemma kernelQuotientDefect_euclidean_eq (a b : ℝ) (s : ℂ)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    kernelQuotientDefect a b s (kernelEuclideanProjection p)=smoothCuspSeedDefectField a b s p.ofLp := by
  unfold kernelEuclideanProjection
  simp only [Function.comp_apply]
  rw [euclideanToHyperbolic_positive p hp]
  change smoothCuspSeedDefect a b s _=smoothCuspSeedDefectField a b s p.ofLp
  rw [smoothCuspSeedDefectField,dite_eq_left hp]
  simp only [mul_comm Complex.I]

theorem kernelEisensteinRemainder_operator_equation (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (p : EuclideanSpatial) (hp : 0<p 2) :
    positiveEuclideanLaplacian (kernelFunctionField (kernelEisensteinRemainder a b s hs)) p=
      kernelQuotientDefect a b s (kernelEuclideanProjection p)+
        kernelEisensteinSpectralParameter s*kernelEisensteinRemainder a b s hs (kernelEuclideanProjection p) := by
  let f := kernelFunctionField (kernelEisensteinRemainder a b s hs)
  have hf : ∀q,0<q 2→ContDiffAt ℝ ∞ f q := kernelEisensteinRemainder_euclidean_smooth a b ha hab s hs
  have he : ∀q : SpatialCoordinates,0<q 2→f (WithLp.toLp 2 q)=eisensteinRemainderField a b s q := by
    intro q hq
    exact kernelEisensteinRemainder_euclidean_eq a b s hs (WithLp.toLp 2 q) hq
  rw [positiveEuclideanLaplacian_eq_axis f hf p hp,
    axisLaplacian_congr_positive _ _ he p.ofLp hp,
    eisensteinRemainder_coordinate_equation a b ha hab s hs p.ofLp hp,
    kernelQuotientDefect_euclidean_eq a b s p hp,kernelEisensteinRemainder_euclidean_eq a b s hs p hp]
  rfl

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

lemma kernelFunctionCutoff_uniform_near (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (K : Set KernelQuotient) (hK : IsCompact K) :
    ∃N : ℕ,∀n≥N,∀p : EuclideanSpatial,0<p 2→kernelEuclideanProjection p∈K→
      kernelTestField (kernelFunctionCutoff n f hf)=ᶠ[𝓝 p]kernelFunctionField f := by
  obtain ⟨C,hC⟩ := hK.bddAbove_image
    (kernelQuotientBarrier_continuous 2 3 (by norm_num) (by norm_num)).continuousOn
  obtain ⟨N,hN⟩ := exists_nat_gt C
  refine ⟨N,?_⟩
  intro n hn p hp hpK
  have hheight : kernelQuotientBarrier 2 3 (kernelEuclideanProjection p)<(n:ℝ)+1 := by
    have hh := hC ⟨kernelEuclideanProjection p,hpK,rfl⟩
    have hcast : (N:ℝ)≤n := by exact_mod_cast hn
    linarith
  have hnear := (kernelQuotientBarrier_continuous 2 3 (by norm_num) (by norm_num)).continuousAt.eventually_lt_const hheight
  have hc : ContinuousAt kernelEuclideanProjection p :=
    (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp
      (euclideanToHyperbolic_contMDiffAt p hp).continuousAt
  filter_upwards [hc hnear] with q hq
  change (kernelExhaustionProfile n (kernelQuotientBarrier 2 3 (kernelEuclideanProjection q)):ℂ)*
    kernelFunctionField f q=kernelFunctionField f q
  rw [kernelExhaustionProfile_one n _ hq.le]
  simp

lemma kernelBoundedFunction_form_equation (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (hgL : MemLp (kernelFunctionGradient f) 2 KernelFundamentalVolume)
    (B G : ℝ) (hB : 0≤B) (hG : 0≤G) (hfB : ∀q,‖f q‖≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (hEq : ∀p : EuclideanSpatial,0<p 2→
      positiveEuclideanLaplacian (kernelFunctionField f) p=A (kernelEuclideanProjection p))
    (g : kernelSmoothTests) :
    inner ℂ (hgL.toLp (kernelFunctionGradient f)) (kernelGradientToL2 g)=
      inner ℂ (hA.toLp A) (kernelSmoothTestsToL2 g) := by
  obtain ⟨N,hN⟩ := kernelFunctionCutoff_uniform_near f hf (tsupport g.1) g.2.2
  have hconstant : ∀ᶠn : ℕ in atTop,
      inner ℂ (kernelGradientToL2 (kernelFunctionCutoff n f hf)) (kernelGradientToL2 g)=
        inner ℂ (hA.toLp A) (kernelSmoothTestsToL2 g) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [kernelGradientToL2_inner,kernelL2_inner_toLp_smooth]
    apply kernelDirichletForm_supported_equation (kernelFunctionCutoff n f hf) g A hA
    intro p hp hpg
    change positiveEuclideanLaplacian (kernelTestField (kernelFunctionCutoff n f hf)) p=A (kernelEuclideanProjection p)
    rw [positiveEuclideanLaplacian_congr _ _ p (hN n hn p hp hpg)]
    exact hEq p hp
  have hlim : Tendsto (fun n => inner ℂ (kernelGradientToL2 (kernelFunctionCutoff n f hf))
      (kernelGradientToL2 g)) atTop (𝓝 (inner ℂ (hgL.toLp (kernelFunctionGradient f)) (kernelGradientToL2 g))) :=
    (kernelFunctionCutoff_gradient_tendsto f hf hgL B G hB hG hfB hgrad).inner
      (tendsto_const_nhds (x := kernelGradientToL2 g))
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hconstant.mono (fun n hn => hn.symm)))

theorem kernel_bounded_smooth_operator_graph (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (hfL : MemLp f 2 (integralQuotientVolume globalKubotaKernel))
    (B G : ℝ) (hB : 0≤B) (hG : 0≤G) (hfB : ∀q,‖f q‖≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (hEq : ∀p : EuclideanSpatial,0<p 2→
      positiveEuclideanLaplacian (kernelFunctionField f) p=A (kernelEuclideanProjection p)) :
    (hfL.toLp f,hA.toLp A)∈kernelEnergyLaplacian.graph := by
  have hgL := kernelFunctionGradient_memLp f hf G hG hgrad
  obtain ⟨u,hum,hug⟩ := kernel_bounded_smooth_energy_exists f hf hfL hgL B G hB hG hfB hgrad
  have hform (v : KernelEnergyGraph) :
      inner ℂ (kernelEnergyGradient u) (kernelEnergyGradient v)=inner ℂ (hA.toLp A) (kernelEnergyMass v) := by
    exact kernelEnergyGraphCore_dense.induction_on v
      (isClosed_eq (by fun_prop : Continuous (fun v : KernelEnergyGraph =>
        inner ℂ (kernelEnergyGradient u) (kernelEnergyGradient v)))
        (by fun_prop : Continuous (fun v : KernelEnergyGraph => inner ℂ (hA.toLp A) (kernelEnergyMass v))))
      (fun g => by
        rw [hug,kernelEnergyGradient_core,kernelEnergyMass_core]
        exact kernelBoundedFunction_form_equation f hf hgL B G hB hG hfB hgrad A hA hEq g)
  have hu : u=kernelVariationalSolution (hfL.toLp f+hA.toLp A) := by
    apply kernelVariationalSolution_unique
    intro v
    rw [hum,hform v,inner_add_left]
  have hm := congrArg kernelEnergyMass hu
  rw [hum] at hm
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph]
  exact hm.symm

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

theorem kernelEisensteinRemainderL2_graph (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    (kernelEisensteinRemainderL2 a b ha hab s hs,
      kernelL2Defect a b (by linarith) hab s+kernelEisensteinSpectralParameter s •
        kernelEisensteinRemainderL2 a b ha hab s hs)∈kernelEnergyLaplacian.graph := by
  let f := kernelEisensteinRemainder a b s (by linarith)
  have hf := kernelEisensteinRemainder_smooth a b ha hab s (by linarith)
  have hfL : MemLp f 2 (integralQuotientVolume globalKubotaKernel) :=
    kernel_eisenstein_sub_seed_memLp a b ha.le hab s hs
  have hfB : ∀q,‖f q‖≤eisensteinRemainderBound b s := by
    intro q
    induction q using Quotient.inductionOn with
    | _ w => exact eisenstein_sub_seed_bounded a b ha.le hab s hs w
  obtain ⟨G,hG,hgrad⟩ := kernelEisensteinRemainder_scaled_fderiv_bound a b ha hab s hs
  let A : KernelQuotient→ℂ := fun q => kernelQuotientDefect a b s q+
    kernelEisensteinSpectralParameter s*f q
  have hD := kernelQuotientDefect_memLp a b s (by linarith) hab
  have hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel) :=
    hD.add (hfL.const_smul (kernelEisensteinSpectralParameter s))
  have hEq : ∀p : EuclideanSpatial,0<p 2→
      positiveEuclideanLaplacian (kernelFunctionField f) p=A (kernelEuclideanProjection p) := by
    intro p hp
    exact kernelEisensteinRemainder_operator_equation a b ha hab s (by linarith) p hp
  have hgraph := kernel_bounded_smooth_operator_graph f hf hfL
    (eisensteinRemainderBound b s) G (eisensteinRemainderBound_nonneg b s) hG hfB hgrad A hA hEq
  have hAL : hA.toLp A=kernelL2Defect a b (by linarith) hab s+
      kernelEisensteinSpectralParameter s • kernelEisensteinRemainderL2 a b ha hab s hs := by
    exact (hD.toLp_add (hfL.const_smul (kernelEisensteinSpectralParameter s))).trans
      (congrArg (fun x => hD.toLp (kernelQuotientDefect a b s)+x)
        (hfL.toLp_const_smul (kernelEisensteinSpectralParameter s)))
  rw [hAL] at hgraph
  exact hgraph

theorem kernelEisensteinL2Correction_eq_remainder (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelEisensteinL2Correction a b (by linarith) hab s=
      kernelEisensteinRemainderL2 a b ha hab s hs := by
  exact kernelEisensteinL2Correction_unique a b (by linarith) hab s
    (kernelSpectralFormOperator_isUnit_nonreal _
      (kernelEisensteinSpectralParameter_nonreal s (by linarith) (by linarith)))
    _ (kernelEisensteinRemainderL2_graph a b ha hab s hs)

theorem kernelEisensteinL2Correction_initial_overlap (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelEisensteinL2Correction a b (by linarith) hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s (by linarith) q-kernelQuotientSeed a b s q := by
  rw [kernelEisensteinL2Correction_eq_remainder a b ha hab s hs hi]
  exact kernelEisensteinRemainderL2_ae a b ha hab s hs

end CubicEisenstein

end

end OAI
end OAIOriginalModule0258

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.ScatteringCoefficients
Source SHA256: f0520ea6bf2a1efea393c0ed3e3b14ac64f80f7a0d4849c12bf9ddd7ccc5a02d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0259



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
open scoped BigOperators Classical Topology MatrixGroups

def cubicEisensteinResidue : KernelQuotientL2 :=
  kernelEisensteinResidueVector 2 3 (by norm_num) (by norm_num)

lemma cubicEisensteinResidue_nonzero_character :
    cubicEisensteinResidue≠0 ∧
      ∀M : CubicKubota.levelThree,kernelLevelPullback M cubicEisensteinResidue=
        CubicKubota.complexCharacter M • cubicEisensteinResidue := by
  apply kernelEisensteinResidueVector_nonzero_character_of_initial_overlap 2 3 (by norm_num) (by norm_num)
  intro s hs hi
  exact kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi

lemma cubicEisensteinResidue_ne_zero : cubicEisensteinResidue≠0 :=
  cubicEisensteinResidue_nonzero_character.1

lemma cubicEisensteinResidue_character (M : CubicKubota.levelThree) :
    kernelLevelPullback M cubicEisensteinResidue=
      CubicKubota.complexCharacter M • cubicEisensteinResidue :=
  cubicEisensteinResidue_nonzero_character.2 M

lemma cubicEisensteinResidue_eigenvector :
    (cubicEisensteinResidue,(8/9:ℂ) • cubicEisensteinResidue)∈kernelEnergyLaplacian.graph :=
  kernelEisensteinResidueVector_graph 2 3 (by norm_num) (by norm_num)

lemma cubicEisensteinResidue_limit :
    Tendsto (fun s : ℂ => (s-4/3) • kernelEisensteinL2Correction 2 3 (by norm_num) (by norm_num) s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 cubicEisensteinResidue) :=
  kernelEisensteinResidueVector_limit 2 3 (by norm_num) (by norm_num)

lemma cubicEisensteinResidue_cusp_average :
    kernelCuspStripAverage cubicEisensteinResidue=cuspConstantAverageResidue := by
  apply kernelEisensteinResidueVector_average_of_overlap 2 3 (by norm_num) (by norm_num)
  intro s hs hi
  apply kernelCuspAverageFamily_eq_of_initial_overlap 2 3 (by norm_num) (by norm_num) s (by linarith)
  exact kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi

lemma cubicEisensteinCorrection_not_continuousAt :
    ¬ContinuousAt (kernelEisensteinL2Correction 2 3 (by norm_num) (by norm_num)) (4/3:ℂ) := by
  intro hc
  have hh := ((tendsto_id.sub_const (4/3:ℂ)).smul hc.tendsto).mono_left
    (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  simp only [sub_self,zero_smul] at hh
  exact cubicEisensteinResidue_ne_zero (tendsto_nhds_unique cubicEisensteinResidue_limit hh)

lemma cubicEisensteinResidue_local_limit (S : Set KernelQuotient) (hS : IsCompact S) :
    Tendsto (fun s : ℂ => (s-4/3) •
      kernelLocalCorrectedSeed S hS 2 3 (by norm_num) (by norm_num) s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (kernelMassRestrictionCLM S hS.measurableSet cubicEisensteinResidue)) :=
  kernelLocalCorrectedSeed_residue_limit S hS 2 3 (by norm_num) (by norm_num)

lemma cubicEisensteinLocalFamily_initial_ae (S : Set KernelQuotient) (hS : IsCompact S)
    (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    (kernelLocalCorrectedSeed S hS 2 3 (by norm_num) (by norm_num) s : KernelQuotient→ℂ)
      =ᵐ[integralQuotientVolume globalKubotaKernel]
        S.indicator (kernelQuotientEisenstein s (by linarith)) := by
  have hlocal := kernelLocalCorrectedSeed_ae_eq S hS 2 3 (by norm_num) (by norm_num) s
  have hoverlap := kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi
  filter_upwards [hlocal,hoverlap] with q hq hc
  rw [hq]
  by_cases hmem : q∈S
  · rw [Set.indicator_of_mem hmem,Set.indicator_of_mem hmem]
    change kernelQuotientSeed 2 3 s q+kernelEisensteinL2Correction 2 3 (by norm_num) (by norm_num) s q=_
    rw [hc]
    ring
  · rw [Set.indicator_of_notMem hmem,Set.indicator_of_notMem hmem]

lemma cubicEisensteinLocalFamily_meromorphicAt (S : Set KernelQuotient) (hS : IsCompact S) :
    MeromorphicAt (kernelLocalCorrectedSeed S hS 2 3 (by norm_num) (by norm_num)) (4/3:ℂ) :=
  kernelLocalCorrectedSeed_meromorphicAt S hS 2 3 (by norm_num) (by norm_num)

lemma cubicEisensteinLocalFamily_not_continuousAt :
    ¬ContinuousAt (kernelLocalCorrectedSeed kernelCuspAverageCompact kernelCuspAverageCompact_isCompact
      2 3 (by norm_num) (by norm_num)) (4/3:ℂ) := by
  have hnonzero : kernelMassRestrictionCLM kernelCuspAverageCompact
      kernelCuspAverageCompact_isCompact.measurableSet cubicEisensteinResidue≠0 := by
    intro hz
    have hh := congrArg kernelCuspStripAverage hz
    rw [kernelCuspStripAverage_restrict,map_zero,cubicEisensteinResidue_cusp_average] at hh
    exact cuspConstantAverageResidue_ne_zero hh
  intro hc
  have hh := ((tendsto_id.sub_const (4/3:ℂ)).smul hc.tendsto).mono_left
    (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  simp only [sub_self,zero_smul] at hh
  exact hnonzero (tendsto_nhds_unique
    (cubicEisensteinResidue_local_limit kernelCuspAverageCompact kernelCuspAverageCompact_isCompact) hh)

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

def whittakerHeight (v : ℝ) : ℝ := max 5 v
def whittakerBase (p : ℝ × ℂ) : ℝ := whittakerHeight p.1*(1+‖p.2‖^2)
def whittakerIntegrand (freq s : ℂ) (p : ℝ × ℂ) : ℂ :=
  (whittakerHeight p.1:ℂ)⁻¹*(whittakerBase p:ℂ)^(-s)*
    ShortDraftTrace.breveE (-(freq*whittakerHeight p.1)*p.2)
def whittakerIntegrandDeriv (freq s : ℂ) (p : ℝ × ℂ) : ℂ :=
  -(Real.log (whittakerBase p):ℂ)*whittakerIntegrand freq s p
def whittakerProductVolume : Measure (ℝ × ℂ) :=
  (volume.restrict (Set.Icc (5:ℝ) 6)).prod volume

lemma whittakerHeight_ge_one (v : ℝ) : 1≤whittakerHeight v := by
  exact (by norm_num : (1:ℝ)≤5).trans (le_max_left _ _)

lemma whittakerBase_ge (p : ℝ × ℂ) : 1+‖p.2‖^2≤whittakerBase p := by
  exact le_mul_of_one_le_left (by positivity) (whittakerHeight_ge_one p.1)

lemma whittakerBase_ge_one (p : ℝ × ℂ) : 1≤whittakerBase p :=
  (by nlinarith [sq_nonneg ‖p.2‖] : 1≤1+‖p.2‖^2).trans (whittakerBase_ge p)

lemma whittakerBase_pos (p : ℝ × ℂ) : 0<whittakerBase p :=
  zero_lt_one.trans_le (whittakerBase_ge_one p)

lemma whittakerIntegrand_continuous (freq s : ℂ) : Continuous (whittakerIntegrand freq s) := by
  have hv : Continuous (fun p : ℝ × ℂ => whittakerHeight p.1) := by
    unfold whittakerHeight
    fun_prop
  have hb : Continuous whittakerBase := by unfold whittakerBase; fun_prop
  have hp : Continuous (fun p : ℝ × ℂ => (whittakerBase p:ℂ)^(-s)) :=
    (Complex.continuous_ofReal.comp hb).cpow continuous_const
      (fun p => Complex.ofReal_mem_slitPlane.mpr (whittakerBase_pos p))
  have hi : Continuous (fun p : ℝ × ℂ => (whittakerHeight p.1:ℂ)⁻¹) :=
    (Complex.continuous_ofReal.comp hv).inv₀ (fun p => by
      change (whittakerHeight p.1:ℂ)≠0
      exact_mod_cast (zero_lt_one.trans_le (whittakerHeight_ge_one p.1)).ne')
  have hc : Continuous (fun p : ℝ × ℂ =>
      ShortDraftTrace.breveE (-(freq*whittakerHeight p.1)*p.2)) := by
    change Continuous (fun p : ℝ × ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-(freq*whittakerHeight p.1)*p.2)+starRingEnd ℂ (-(freq*whittakerHeight p.1)*p.2))))
    fun_prop
  exact (hi.mul hp).mul hc

lemma whittakerIntegrandDeriv_continuous (freq s : ℂ) : Continuous (whittakerIntegrandDeriv freq s) := by
  have hb : Continuous whittakerBase := by unfold whittakerBase whittakerHeight; fun_prop
  have hl : Continuous (fun p => Real.log (whittakerBase p)) :=
    hb.log (fun p => (whittakerBase_pos p).ne')
  exact (Complex.continuous_ofReal.comp hl).neg.mul (whittakerIntegrand_continuous freq s)

lemma whittakerIntegrand_hasDerivAt (freq s : ℂ) (p : ℝ × ℂ) :
    HasDerivAt (fun w => whittakerIntegrand freq w p) (whittakerIntegrandDeriv freq s p) s := by
  have hn : (whittakerBase p:ℂ)≠0 := by exact_mod_cast (whittakerBase_pos p).ne'
  have hh := (((hasDerivAt_id s).neg.const_cpow (Or.inl hn)).const_mul
    ((whittakerHeight p.1:ℂ)⁻¹)).mul_const
      (ShortDraftTrace.breveE (-(freq*whittakerHeight p.1)*p.2))
  convert hh using 1
  · rfl
  · rw [←Complex.ofReal_log (whittakerBase_pos p).le]
    unfold whittakerIntegrandDeriv whittakerIntegrand
    simp only [Pi.neg_apply,id_eq]
    ring

lemma whittakerIntegrand_norm (freq s : ℂ) (p : ℝ × ℂ) :
    ‖whittakerIntegrand freq s p‖=(whittakerHeight p.1)⁻¹*(whittakerBase p)^(-s.re) := by
  unfold whittakerIntegrand
  rw [norm_mul,norm_mul,breveE_norm,mul_one,norm_inv,
    Complex.norm_of_nonneg (zero_lt_one.trans_le (whittakerHeight_ge_one p.1)).le,
    Complex.norm_cpow_eq_rpow_re_of_pos (whittakerBase_pos p)]
  rfl

lemma whittakerIntegrand_norm_bound (freq s : ℂ) (p : ℝ × ℂ)
    (b : ℝ) (hb : 0≤b) (hs : b≤s.re) :
    ‖whittakerIntegrand freq s p‖≤(1+‖p.2‖^2)^(-b) := by
  rw [whittakerIntegrand_norm]
  calc
    _ ≤ (whittakerBase p)^(-s.re) := by
      exact mul_le_of_le_one_left (Real.rpow_nonneg (whittakerBase_pos p).le _)
        (inv_le_one_of_one_le₀ (whittakerHeight_ge_one p.1))
    _ ≤ (whittakerBase p)^(-b) :=
      Real.rpow_le_rpow_of_exponent_le (whittakerBase_ge_one p) (by linarith)
    _ ≤ (1+‖p.2‖^2)^(-b) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (whittakerBase_ge p) (by linarith)

lemma whittakerIntegrandDeriv_norm_bound (freq s : ℂ) (p : ℝ × ℂ)
    (b ε : ℝ) (hb : 0≤b) (hε : 0<ε) (hs : b+ε≤s.re) :
    ‖whittakerIntegrandDeriv freq s p‖≤ε⁻¹*(1+‖p.2‖^2)^(-b) := by
  have hlog := Real.log_nonneg (whittakerBase_ge_one p)
  unfold whittakerIntegrandDeriv
  rw [norm_mul,norm_neg,Complex.norm_of_nonneg hlog,whittakerIntegrand_norm]
  calc
    _ ≤ Real.log (whittakerBase p)*(whittakerBase p)^(-s.re) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (Real.rpow_nonneg (whittakerBase_pos p).le _)
          (inv_le_one_of_one_le₀ (whittakerHeight_ge_one p.1))) hlog
    _ ≤ ((whittakerBase p)^ε/ε)*(whittakerBase p)^(-s.re) := by
      exact mul_le_mul_of_nonneg_right (Real.log_le_rpow_div (whittakerBase_pos p).le hε)
        (Real.rpow_nonneg (whittakerBase_pos p).le _)
    _ = ε⁻¹*(whittakerBase p)^(ε-s.re) := by
      rw [Real.rpow_sub (whittakerBase_pos p),Real.rpow_neg (whittakerBase_pos p).le]
      ring
    _ ≤ ε⁻¹*(whittakerBase p)^(-b) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (whittakerBase_ge_one p) (by linarith)) (by positivity)
    _ ≤ ε⁻¹*(1+‖p.2‖^2)^(-b) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by positivity) (whittakerBase_ge p) (by linarith)) (by positivity)

lemma whittaker_bound_integrable (b : ℝ) (hb : 1<b) :
    Integrable (fun p : ℝ × ℂ => (1+‖p.2‖^2)^(-b)) whittakerProductVolume := by
  have hk : Integrable (fun z : ℂ => (1+‖z‖^2)^(-b)) := by
    convert (hyperbolicKernel_integrable (b:ℂ) hb).norm using 1
    funext z
    simp only [hyperbolicKernel,Complex.norm_cpow_eq_rpow_re_of_pos
      (by positivity : 0<1+‖z‖^2),Complex.neg_re,Complex.ofReal_re]
  have hv : Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict (Set.Icc (5:ℝ) 6)) := integrable_const _
  unfold whittakerProductVolume
  simpa only [one_mul] using hv.mul_prod hk

lemma whittakerIntegrand_integrable (freq s : ℂ) (hs : 1<s.re) :
    Integrable (whittakerIntegrand freq s) whittakerProductVolume := by
  exact (whittaker_bound_integrable s.re hs).mono'
    (whittakerIntegrand_continuous freq s).aestronglyMeasurable
    (Eventually.of_forall (fun p => whittakerIntegrand_norm_bound freq s p s.re (by linarith) le_rfl))

lemma whittakerProduct_differentiableAt (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ (fun w => ∫p,whittakerIntegrand freq w p∂whittakerProductVolume) s := by
  let b : ℝ := (s.re+1)/2
  let ε : ℝ := (s.re-1)/4
  have hb : 1<b := by dsimp [b]; linarith
  have hε : 0<ε := by dsimp [ε]; linarith
  have hsb : b+ε<s.re := by dsimp [b,ε]; linarith
  have hU : {w : ℂ | b+ε<w.re}∈𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsb
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ» := whittakerProductVolume) (F := whittakerIntegrand freq)
    (F' := whittakerIntegrandDeriv freq)
    (bound := fun p => ε⁻¹*(1+‖p.2‖^2)^(-b)) hU
    (Eventually.of_forall (fun w => (whittakerIntegrand_continuous freq w).aestronglyMeasurable))
    (whittakerIntegrand_integrable freq s hs)
    (whittakerIntegrandDeriv_continuous freq s).aestronglyMeasurable
    (Eventually.of_forall (fun p w hw => whittakerIntegrandDeriv_norm_bound freq w p b ε (by linarith) hε hw.le))
    ((whittaker_bound_integrable b hb).const_mul ε⁻¹)
    (Eventually.of_forall (fun p w _ => whittakerIntegrand_hasDerivAt freq w p))
  exact h.2.differentiableAt

lemma whittakerIntegrand_eq (freq s : ℂ) (v : ℝ) (hv : 5≤v) (z : ℂ) :
    whittakerIntegrand freq s (v,z)=
      (v:ℂ)^(-s-1)*(hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z)) := by
  have hvp : 0<v := by linarith
  have hvn : (v:ℂ)≠0 := by exact_mod_cast hvp.ne'
  have hp : (v:ℂ)^(-s-1)=(v:ℂ)^(-s)*(v:ℂ)⁻¹ := by
    rw [Complex.cpow_sub _ _ hvn,Complex.cpow_one,div_eq_mul_inv]
  unfold whittakerIntegrand whittakerBase whittakerHeight hyperbolicKernel
  simp only [max_eq_right hv,Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg hvp.le (by positivity),hp]
  ring

lemma whittakerProduct_eq_average (freq s : ℂ) (hs : 1<s.re) :
    (∫p,whittakerIntegrand freq s p∂whittakerProductVolume)=
      ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-s-1)*sourceFourierKernel s (freq*v) := by
  have hi := whittakerIntegrand_integrable freq s hs
  unfold whittakerProductVolume at hi ⊢
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  calc
    _ = ∫z : ℂ,(v:ℂ)^(-s-1)*(hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => whittakerIntegrand_eq freq s v hv.1 z)
    _ = _ := integral_const_mul _ _

theorem cuspWhittakerAverage_differentiableAt (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ
      (fun w => ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-w-1)*sourceFourierKernel w (freq*v)) s := by
  have he : (fun w => ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-w-1)*sourceFourierKernel w (freq*v))
      =ᶠ[𝓝 s](fun w => ∫p,whittakerIntegrand freq w p∂whittakerProductVolume) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
    exact (whittakerProduct_eq_average freq w hw).symm
  exact (whittakerProduct_differentiableAt freq s hs).congr_of_eventuallyEq he

end

section
open scoped BigOperators Classical

open ActualEisensteinCubic ConcreteTraceCRT

lemma arithmeticDirichletTerm_differentiable (h : ActualEisensteinCubic.O) (c : LevelLower) :
    Differentiable ℂ (fun s : ℂ => arithmeticDirichletTerm s h c) := by
  by_cases hc : c.1=0
  · simp only [arithmeticDirichletTerm,ite_eq_left hc]
    exact differentiable_const _
  · have hq : ((‖eisEmbedding c.1‖^2:ℝ):ℂ)≠0 :=
      Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc)))
    simp only [arithmeticDirichletTerm,ite_eq_right hc]
    exact (differentiable_id.neg.const_cpow (Or.inl hq)).mul_const _

lemma arithmeticDirichletTerm_norm_mono (h : ActualEisensteinCubic.O)
    (a : ℝ) (s : ℂ) (ha : a≤s.re) (c : LevelLower) :
    ‖arithmeticDirichletTerm s h c‖≤‖arithmeticDirichletTerm (a:ℂ) h c‖ := by
  by_cases hc : c.1=0
  · simp only [arithmeticDirichletTerm,ite_eq_left hc,norm_zero,le_refl]
  · have hpos : 0<‖eisEmbedding c.1‖^2 := sq_pos_of_pos
      (norm_pos_iff.mpr (eisEmbedding_ne_zero hc))
    have hq : 1≤‖eisEmbedding c.1‖^2 := by
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hc))
    simp only [arithmeticDirichletTerm,ite_eq_right hc,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hpos,Complex.neg_re,Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hq (neg_le_neg ha))
      (norm_nonneg _)

theorem arithmeticDirichletSeries_differentiableAt (h : ActualEisensteinCubic.O)
    (s : ℂ) (hs : 2<s.re) :
    DifferentiableAt ℂ (fun z => arithmeticDirichletSeries z h) s := by
  let a : ℝ := (2+s.re)/2
  have ha : 2<a := by dsimp [a]; linarith
  have has : a<s.re := by dsimp [a]; linarith
  have hsum := arithmeticDirichletTerm_summable_norm (a:ℂ) (by simpa using ha) h
  have hopen : IsOpen {z : ℂ | a<z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (fun z => arithmeticDirichletSeries z h) {z : ℂ | a<z.re} := by
    apply Complex.differentiableOn_tsum_of_summable_norm hsum
      (fun c => (arithmeticDirichletTerm_differentiable h c).differentiableOn) hopen
    intro c z hz
    exact arithmeticDirichletTerm_norm_mono h a z hz.le c
  exact (hd s has).differentiableAt (hopen.mem_nhds has)

theorem scatteringCoefficient_differentiableAt (h : ActualEisensteinCubic.O)
    (s : ℂ) (hs : 2<s.re) :
    DifferentiableAt ℂ (fun z => scatteringCoefficient z h) s :=
  (arithmeticDirichletSeries_differentiableAt h s hs).div_const _

theorem scatteringCoefficient_analyticOnNhd (h : ActualEisensteinCubic.O) :
    AnalyticOnNhd ℂ (fun z => scatteringCoefficient z h) {z : ℂ | 2<z.re} := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    exact (scatteringCoefficient_differentiableAt h z hz).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal

local notation "O" => ActualEisensteinCubic.O

lemma cuspPeriodStrip_measure_ne_top : hyperbolicVolume (cuspPeriodStrip 5 6)≠(⊤:ℝ≥0∞) := by
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hh := hm.measure_preimage (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
  simp only [Set.preimage_univ,Measure.restrict_apply_univ] at hh
  rw [hh]
  exact measure_ne_top _ _

instance cuspStripFiniteVolume : IsFiniteMeasure (hyperbolicVolume.restrict (cuspPeriodStrip 5 6)) :=
  isFiniteMeasure_restrict.mpr cuspPeriodStrip_measure_ne_top

abbrev CuspStripL2 := Lp ℂ 2 (hyperbolicVolume.restrict (cuspPeriodStrip 5 6))

def kernelCuspPullback : KernelQuotientL2→L[ℂ]CuspStripL2 :=
  (Lp.compMeasurePreservingₗᵢ ℂ (integralOrbitProjection globalKubotaKernel)
    (kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num))).toContinuousLinearMap.comp
    (LpToLpRestrictCLM KernelQuotient ℂ ℂ (integralQuotientVolume globalKubotaKernel) 2 kernelCuspStripSet)

lemma kernelCuspPullback_ae_eq (F : KernelQuotientL2) :
    kernelCuspPullback F=ᵐ[hyperbolicVolume.restrict (cuspPeriodStrip 5 6)]
      fun w => F (integralOrbitProjection globalKubotaKernel w) := by
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hr := LpToLpRestrictCLM_coeFn ℂ kernelCuspStripSet F
  have hc := hm.quasiMeasurePreserving.ae_eq_comp hr
  have hp := Lp.coeFn_compMeasurePreserving
    (LpToLpRestrictCLM KernelQuotient ℂ ℂ (integralQuotientVolume globalKubotaKernel) 2 kernelCuspStripSet F) hm
  filter_upwards [hp,hc] with w hw hc
  exact hw.trans hc

def cuspFourierPhase (h : ActualEisensteinCubic.O) (w : HyperbolicSpace) : ℂ :=
  ShortDraftTrace.breveE (-cuspFrequency h*hyperbolicHorizontal w)

lemma cuspFourierPhase_continuous (h : ActualEisensteinCubic.O) : Continuous (cuspFourierPhase h) := by
  have hc : Continuous (fun z : ℂ => ShortDraftTrace.breveE (-cuspFrequency h*z)) := by
    change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-cuspFrequency h*z)+starRingEnd ℂ (-cuspFrequency h*z))))
    fun_prop
  exact hc.comp hyperbolicHorizontal_continuous

lemma cuspFourierPhase_norm (h : ActualEisensteinCubic.O) (w : HyperbolicSpace) : ‖cuspFourierPhase h w‖=1 :=
  breveE_norm _

lemma cuspFourierTest_memLp (h : ActualEisensteinCubic.O) :
    MemLp (fun w => star (cuspFourierPhase h w)) 2
      (hyperbolicVolume.restrict (cuspPeriodStrip 5 6)) := by
  apply MemLp.of_bound (cuspFourierPhase_continuous h).star.aestronglyMeasurable 1
  exact Eventually.of_forall (fun w => by rw [norm_star,cuspFourierPhase_norm])

def cuspFourierTestL2 (h : ActualEisensteinCubic.O) : CuspStripL2 :=
  (cuspFourierTest_memLp h).toLp (fun w => star (cuspFourierPhase h w))

def kernelCuspFourier (h : ActualEisensteinCubic.O) : KernelQuotientL2→L[ℂ]ℂ :=
  (innerSL ℂ (cuspFourierTestL2 h)).comp kernelCuspPullback

lemma kernelCuspFourier_integral (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    kernelCuspFourier h F=∫w in cuspPeriodStrip 5 6,
      F (integralOrbitProjection globalKubotaKernel w)*cuspFourierPhase h w∂hyperbolicVolume := by
  change inner ℂ (cuspFourierTestL2 h) (kernelCuspPullback F)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (cuspFourierTest_memLp h),kernelCuspPullback_ae_eq F] with w hw hp
  rw [RCLike.inner_apply,cuspFourierTestL2,hw,hp]
  simp only [starRingEnd_apply,star_star]

lemma kernelCuspFourier_restrict (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    kernelCuspFourier h (kernelMassRestrictionCLM kernelCuspAverageCompact
      kernelCuspAverageCompact_isCompact.measurableSet F)=kernelCuspFourier h F := by
  rw [kernelCuspFourier_integral,kernelCuspFourier_integral]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae
    (kernelMassRestriction_coe kernelCuspAverageCompact kernelCuspAverageCompact_isCompact.measurableSet F)
    (s := kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  exact congrArg (fun z : ℂ => z*cuspFourierPhase h w)
    (hw.trans (Set.indicator_of_mem (kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩) _))

def kernelCuspFourierFamily (h : ActualEisensteinCubic.O) (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : ℂ :=
  kernelCuspFourier h
    (kernelLocalCorrectedSeed kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab s)

lemma kernelCuspFourierFamily_meromorphicAt (h : ActualEisensteinCubic.O) (a b : ℝ) (ha : 0<a) (hab : a<b) :
    MeromorphicAt (kernelCuspFourierFamily h a b ha hab) (4/3:ℂ) :=
  meromorphicAt_clm (kernelCuspFourier h)
    (kernelLocalCorrectedSeed_meromorphicAt kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab)

lemma kernelCuspFourierFamily_residue_limit (h : ActualEisensteinCubic.O) (a b : ℝ) (ha : 0<a) (hab : a<b) :
    Tendsto (fun s : ℂ => (s-4/3)*kernelCuspFourierFamily h a b ha hab s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (kernelCuspFourier h (kernelEisensteinResidueVector a b ha hab))) := by
  have hh := (kernelCuspFourier h).continuous.continuousAt.tendsto.comp
    (kernelLocalCorrectedSeed_residue_limit kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab)
  simpa only [Function.comp_def,map_smul,smul_eq_mul,kernelCuspFourier_restrict,kernelCuspFourierFamily] using hh

lemma kernelCuspFourierFamily_actual_integral (h : ActualEisensteinCubic.O) (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    kernelCuspFourierFamily h a b ha hab s=∫w in cuspPeriodStrip 5 6,
      kernelCorrectedSeed a b ha hab s (integralOrbitProjection globalKubotaKernel w)*
        cuspFourierPhase h w∂hyperbolicVolume := by
  rw [kernelCuspFourierFamily,kernelCuspFourier_integral]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae
    (kernelLocalCorrectedSeed_ae_eq kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab s)
    (s := kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  exact congrArg (fun z : ℂ => z*cuspFourierPhase h w)
    (hw.trans (Set.indicator_of_mem (kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩) _))

lemma kernelCuspFourierFamily_of_initial_overlap (h : ActualEisensteinCubic.O) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re)
    (hoverlap : kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q) :
    kernelCuspFourierFamily h a b ha hab s=∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s w*cuspFourierPhase h w∂hyperbolicVolume := by
  have hcorrected : kernelCorrectedSeed a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelQuotientEisenstein s hs := by
    filter_upwards [hoverlap] with q hq
    change kernelQuotientSeed a b s q+kernelEisensteinL2Correction a b ha hab s q=_
    rw [hq]
    ring
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hp := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hcorrected (s := kernelCuspStripSet))
  rw [kernelCuspFourierFamily_actual_integral]
  apply integral_congr_ae
  filter_upwards [hp] with w hw
  exact congrArg (fun z : ℂ => z*cuspFourierPhase h w)
    (hw.trans (kernelQuotientEisenstein_mk s hs w))

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

local notation "O" => ActualEisensteinCubic.O

lemma hyperbolicEisenstein_cusp_fourier_average (s : ℂ) (hs : 2<s.re) (h : ActualEisensteinCubic.O) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w*cuspFourierPhase h w∂hyperbolicVolume)=
      ∫v in Set.Icc (5:ℝ) 6,
        (((if h=0 then (v:ℂ)^s else 0)+
          (v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v)*scatteringCoefficient s h)*
          ((9*Real.sqrt 3/2:ℝ):ℂ))/(v:ℂ)^3 := by
  let g : HyperbolicSpace→ℂ := fun w => hyperbolicEisenstein s w*cuspFourierPhase h w
  have hg : Continuous g := (hyperbolicEisenstein_continuous s hs).mul (cuspFourierPhase_continuous h)
  rw [cuspPeriodStrip_integral_coordinates g hg.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable g hg)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
  have hh : (∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
      eisensteinFourierCoefficient v hpos s h*((9*Real.sqrt 3/2:ℝ):ℂ) := by
    simp_rw [g,cuspCoordinateLift_positive v _ hpos,hyperbolicEisenstein_upperPoint,
      cuspFourierPhase,hyperbolicHorizontal_upperPoint]
    rw [eisensteinFourierCoefficient]
    exact (div_mul_cancel₀ _ cusp_volume_ne_zero).symm
  dsimp only
  rw [hh,eisensteinFourierCoefficient_formula v hpos s hs h]

def cuspWhittakerHeightFactor (s : ℂ) (h : ActualEisensteinCubic.O) : ℂ :=
  ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v)

lemma hyperbolicEisenstein_cusp_fourier_nonzero (s : ℂ) (hs : 2<s.re) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w*cuspFourierPhase h w∂hyperbolicVolume)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h := by
  rw [hyperbolicEisenstein_cusp_fourier_average s hs h]
  simp only [ite_eq_right hh,zero_add]
  have heq : (∫v in Set.Icc (5:ℝ) 6,
      ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v)*scatteringCoefficient s h)*
        ((9*Real.sqrt 3/2:ℝ):ℂ)/(v:ℂ)^3)=
      ∫v in Set.Icc (5:ℝ) 6,
        (((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h)*
          ((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v)) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith [hv.1])
    have hp : (v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3 := by
      rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    dsimp only
    rw [hp]
    ring
  rw [heq,integral_const_mul]
  rfl

lemma cuspWhittakerHeightFactor_bessel (s : ℂ) (hs : 1<s.re) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    cuspWhittakerHeightFactor s h=
      ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-s-1)*
        ((2*Real.pi:ℂ)/Complex.Gamma s*
          (2*Real.pi*‖cuspFrequency h*v‖:ℂ)^(s-1)*
          schlafliBesselK (s-1) (4*Real.pi*‖cuspFrequency h*v‖)) := by
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
  dsimp only
  rw [sourceFourierKernel_bessel s _ hs
    (mul_ne_zero (cuspFrequency_ne_zero h hh) (Complex.ofReal_ne_zero.mpr hpos.ne'))]

def kernelResidualFourierDatum (h : ActualEisensteinCubic.O) (a b : ℝ) (ha : 0<a) (hab : a<b) : ℂ :=
  kernelCuspFourier h (kernelEisensteinResidueVector a b ha hab)

lemma kernelCuspFourierFamily_nonzero_of_initial_overlap (h : ActualEisensteinCubic.O) (hh : h≠0)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) (hs : 2<s.re)
    (hoverlap : kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q) :
    kernelCuspFourierFamily h a b ha hab s=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h := by
  rw [kernelCuspFourierFamily_of_initial_overlap h a b ha hab s hs hoverlap,
    hyperbolicEisenstein_cusp_fourier_nonzero s hs h hh]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

local notation "O" => ActualEisensteinCubic.O

lemma sourceFourierKernel_continuous_freq (s : ℂ) (hs : 1<s.re) :
    Continuous (sourceFourierKernel s) := by
  change Continuous (fun freq : ℂ => ∫z : ℂ,hyperbolicKernel s z*ShortDraftTrace.breveE (-freq*z))
  apply continuous_of_dominated (bound := fun z => ‖hyperbolicKernel s z‖)
  · exact fun freq => (sourceFourierKernel_integrable s freq hs).aestronglyMeasurable
  · exact fun freq => Eventually.of_forall (fun z => by rw [norm_mul,breveE_norm,mul_one])
  · exact (hyperbolicKernel_integrable s hs).norm
  · filter_upwards with z
    change Continuous (fun freq : ℂ => hyperbolicKernel s z*
      Complex.exp (2*Real.pi*Complex.I*((-freq*z)+starRingEnd ℂ (-freq*z))))
    fun_prop

lemma schlafliIntegrand_real (nu x t : ℝ) (ht : 0<t) :
    (t:ℂ)^((nu:ℂ)-1)*Complex.exp (-(t:ℂ)-(x:ℂ)^2/(4*t))=
      ((t^(nu-1)*Real.exp (-t-x^2/(4*t)):ℝ):ℂ) := by
  have hp := Complex.ofReal_cpow ht.le (nu-1)
  simp only [Complex.ofReal_sub,Complex.ofReal_one] at hp
  rw [Complex.ofReal_mul,hp,Complex.ofReal_exp]
  congr 2
  push_cast
  rfl

lemma schlafliIntegral_real_re_pos (nu x : ℝ) (hnu : 0<nu) :
    0<(schlafliIntegral (nu:ℂ) x).re := by
  let f : ℝ→ℂ := fun t => (t:ℂ)^((nu:ℂ)-1)*Complex.exp (-(t:ℂ)-(x:ℂ)^2/(4*t))
  have hi : IntegrableOn f (Set.Ioi (0:ℝ)) volume := schlafliIntegral_integrable (nu:ℂ) x hnu
  have hp (t : ℝ) (ht : 0<t) : 0<(f t).re := by
    rw [show f t=((t^(nu-1)*Real.exp (-t-x^2/(4*t)):ℝ):ℂ) from schlafliIntegrand_real nu x t ht,
      Complex.ofReal_re]
    exact mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)
  change 0<RCLike.re (∫t in Set.Ioi (0:ℝ),f t)
  rw [←integral_re hi]
  apply (integral_pos_iff_support_of_nonneg_ae ?_ hi.re).mpr
  · have heq : Function.support (fun t => RCLike.re (f t))=ᵐ[volume.restrict (Set.Ioi (0:ℝ))] Set.univ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      apply propext
      simp only [Function.mem_support,Set.mem_univ,iff_true]
      exact (hp t ht).ne'
    rw [measure_congr heq,Measure.restrict_apply_univ]
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hp t ht).le

lemma sourceFourierKernel_real_re_pos (sigma : ℝ) (hsigma : 1<sigma) (freq : ℂ) :
    0<(sourceFourierKernel (sigma:ℂ) freq).re := by
  have hh := sourceFourierKernel_gamma_schlafli (sigma:ℂ) freq hsigma
  have hre := congrArg Complex.re hh
  have hsch : 0<(schlafliIntegral ((sigma:ℂ)-1) (4*Real.pi*‖freq‖)).re := by
    convert schlafliIntegral_real_re_pos (sigma-1) (4*Real.pi*‖freq‖) (by linarith) using 1 ; push_cast ; rfl
  rw [Complex.Gamma_ofReal] at hre
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero] at hre
  have hg := Real.Gamma_pos_of_pos (show 0<sigma by linarith)
  have hp := mul_pos Real.pi_pos hsch
  nlinarith

lemma cuspWhittakerHeightFactor_integrable (s : ℂ) (hs : 1<s.re) (h : ActualEisensteinCubic.O) :
    IntegrableOn (fun v : ℝ => (v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))
      (Set.Icc (5:ℝ) 6) volume := by
  apply ContinuousOn.integrableOn_Icc
  intro v hv
  have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
  exact ((Complex.continuousAt_ofReal_cpow_const v (-s-1) (Or.inr hpos.ne')).mul
    ((sourceFourierKernel_continuous_freq s hs).continuousAt.comp
      ((Complex.continuous_ofReal.const_mul (cuspFrequency h)).continuousAt))).continuousWithinAt

lemma cuspWhittakerHeightFactor_real_re_pos (sigma : ℝ) (hsigma : 1<sigma) (h : ActualEisensteinCubic.O) :
    0<(cuspWhittakerHeightFactor (sigma:ℂ) h).re := by
  let f : ℝ→ℂ := fun v => (v:ℂ)^(-(sigma:ℂ)-1)*sourceFourierKernel (sigma:ℂ) (cuspFrequency h*v)
  have hi : IntegrableOn f (Set.Icc (5:ℝ) 6) volume :=
    cuspWhittakerHeightFactor_integrable (sigma:ℂ) hsigma h
  have hp (v : ℝ) (hv : v∈Set.Icc (5:ℝ) 6) : 0<(f v).re := by
    have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
    have he := Complex.ofReal_cpow hpos.le (-sigma-1)
    simp only [Complex.ofReal_sub,Complex.ofReal_neg,Complex.ofReal_one] at he
    change 0<((v:ℂ)^(-(sigma:ℂ)-1)*sourceFourierKernel (sigma:ℂ) (cuspFrequency h*v)).re
    rw [←he,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact mul_pos (Real.rpow_pos_of_pos hpos _) (sourceFourierKernel_real_re_pos sigma hsigma _)
  change 0<RCLike.re (∫v in Set.Icc (5:ℝ) 6,f v)
  rw [←integral_re hi]
  apply (integral_pos_iff_support_of_nonneg_ae ?_ hi.re).mpr
  · have heq : Function.support (fun v => RCLike.re (f v))=ᵐ[volume.restrict (Set.Icc (5:ℝ) 6)] Set.univ := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      apply propext
      simp only [Function.mem_support,Set.mem_univ,iff_true]
      exact (hp v hv).ne'
    rw [measure_congr heq,Measure.restrict_apply_univ]
    norm_num
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (hp v hv).le

lemma cuspWhittakerHeightFactor_center_ne_zero (h : ActualEisensteinCubic.O) :
    cuspWhittakerHeightFactor (4/3:ℂ) h≠0 := by
  intro he
  have hh := cuspWhittakerHeightFactor_real_re_pos (4/3:ℝ) (by norm_num) h
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hh
  rw [he,Complex.zero_re] at hh
  exact lt_irrefl 0 hh

end CubicEisenstein

end

end OAI
end OAIOriginalModule0259

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.WhittakerContinuation
Source SHA256: f58c9c870c116dda730f07d5b43b6ebd8dc83062d1b7cb24f51b77ee1db45cac
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0260


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
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma cuspWhittakerHeightFactor_analyticAt (h : ActualEisensteinCubic.O) (s : ℂ) (hs : 1<s.re) :
    AnalyticAt ℂ (fun w => cuspWhittakerHeightFactor w h) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have hopen : IsOpen {w : ℂ | 1<w.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with w hw
  exact cuspWhittakerAverage_differentiableAt (cuspFrequency h) w hw

lemma kernelCuspFourierFamily_analyticAt_nonreal (h : ActualEisensteinCubic.O) (a b : ℝ)
    (ha : 0<a) (hab : a<b) (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelCuspFourierFamily h a b ha hab) s := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := ℂ)
    (kernelCuspFourier h) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal kernelCuspAverageCompact
        kernelCuspAverageCompact_isCompact a b ha hab s hs hi) rfl

def continuedNonzeroScattering (h : ActualEisensteinCubic.O) (s : ℂ) : ℂ :=
  kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s /
    (((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor s h)

def nonzeroScatteringResidue (h : ActualEisensteinCubic.O) : ℂ :=
  kernelCuspFourier h cubicEisensteinResidue /
    (((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor (4/3:ℂ) h)

lemma continuedNonzeroScattering_meromorphicAt_center (h : ActualEisensteinCubic.O) :
    MeromorphicAt (continuedNonzeroScattering h) (4/3:ℂ) := by
  exact (kernelCuspFourierFamily_meromorphicAt h 2 3 (by norm_num) (by norm_num)).div
    ((analyticAt_const.mul (cuspWhittakerHeightFactor_analyticAt h (4/3) (by norm_num))).meromorphicAt)

lemma continuedNonzeroScattering_meromorphicOn_upper (h : ActualEisensteinCubic.O) :
    MeromorphicOn (continuedNonzeroScattering h) {s : ℂ | 1<s.re ∧ 0<s.im} := by
  intro s hs
  exact (kernelCuspFourierFamily_analyticAt_nonreal h 2 3 (by norm_num) (by norm_num)
    s (ne_of_gt hs.1) (ne_of_gt hs.2)).meromorphicAt.div
    ((analyticAt_const.mul (cuspWhittakerHeightFactor_analyticAt h s hs.1)).meromorphicAt)

lemma continuedNonzeroScattering_residue_limit (h : ActualEisensteinCubic.O) :
    Tendsto (fun s : ℂ => (s-4/3)*continuedNonzeroScattering h s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (nonzeroScatteringResidue h)) := by
  have hden : Tendsto (fun s : ℂ => ((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor s h)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor (4/3:ℂ) h)) := (continuousAt_const.mul
    (cuspWhittakerHeightFactor_analyticAt h (4/3) (by norm_num)).continuousAt).tendsto.mono_left
      (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  have hlimit := (kernelCuspFourierFamily_residue_limit h 2 3 (by norm_num) (by norm_num)).div hden
    (mul_ne_zero cusp_volume_ne_zero (cuspWhittakerHeightFactor_center_ne_zero h))
  change Tendsto (fun s : ℂ =>
      ((s-4/3)*kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s)/
        (((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor s h))
      (𝓝[≠] (4/3:ℂ)) (𝓝 (nonzeroScatteringResidue h)) at hlimit
  convert hlimit using 1
  funext s
  exact (mul_div_assoc _ _ _).symm

lemma continuedNonzeroScattering_initial (h : ActualEisensteinCubic.O) (hh : h≠0) (s : ℂ)
    (hs : 4<s.re) (hi : 0<s.im) (hH : cuspWhittakerHeightFactor s h≠0) :
    continuedNonzeroScattering h s=scatteringCoefficient s h := by
  unfold continuedNonzeroScattering
  rw [kernelCuspFourierFamily_nonzero_of_initial_overlap h hh 2 3
    (by norm_num) (by norm_num) s (by linarith)
    (kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi)]
  field_simp [cusp_volume_ne_zero,hH]

lemma cuspWhittakerHeightFactor_ne_zero_near_five (h : ActualEisensteinCubic.O) :
    ∀ᶠ s : ℂ in 𝓝 (5:ℂ),4<s.re ∧ cuspWhittakerHeightFactor s h≠0 := by
  have hpos := cuspWhittakerHeightFactor_real_re_pos 5 (by norm_num) h
  have hH : cuspWhittakerHeightFactor (5:ℂ) h≠0 := by
    intro he
    norm_num only [Complex.ofReal_ofNat] at hpos
    rw [he,Complex.zero_re] at hpos
    exact lt_irrefl 0 hpos
  have hre : ∀ᶠ s : ℂ in 𝓝 (5:ℂ),4<s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  exact hre.and ((cuspWhittakerHeightFactor_analyticAt h 5 (by norm_num)).continuousAt.eventually_ne hH)

lemma kernelCuspFourierFamily_eq_upper (h : ActualEisensteinCubic.O) (hh : h≠0) :
    Set.EqOn (kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num))
      (fun s => ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h)
      {s : ℂ | 2<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 2<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (2:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hleft : AnalyticOnNhd ℂ (kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num)) domain := by
    intro s hs
    exact kernelCuspFourierFamily_analyticAt_nonreal h 2 3 (by norm_num) (by norm_num)
      s (by linarith [hs.1]) hs.2.ne'
  have hright : AnalyticOnNhd ℂ
      (fun s => ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h) domain := by
    intro s hs
    exact (analyticAt_const.mul (scatteringCoefficient_analyticOnNhd h s hs.1)).mul
      (cuspWhittakerHeightFactor_analyticAt h s (by linarith [hs.1]))
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : (kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num))
      =ᶠ[𝓝 (5+Complex.I:ℂ)]
        (fun s => ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    exact kernelCuspFourierFamily_nonzero_of_initial_overlap h hh 2 3
      (by norm_num) (by norm_num) s (by linarith [hs.1])
      (kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs.1 hs.2)
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hconvex.isPreconnected hstart hevent

lemma continuedNonzeroScattering_eq_upper (h : ActualEisensteinCubic.O) (hh : h≠0) (s : ℂ)
    (hs : 2<s.re) (hi : 0<s.im) (hH : cuspWhittakerHeightFactor s h≠0) :
    continuedNonzeroScattering h s=scatteringCoefficient s h := by
  unfold continuedNonzeroScattering
  rw [kernelCuspFourierFamily_eq_upper h hh ⟨hs,hi⟩]
  field_simp [cusp_volume_ne_zero,hH]

lemma continuedNonzeroScattering_initial_open (h : ActualEisensteinCubic.O) (hh : h≠0) :
    ∃U : Set ℂ,IsOpen U ∧ U.Nonempty ∧ U⊆{s : ℂ | 4<s.re ∧ 0<s.im} ∧
      Set.EqOn (continuedNonzeroScattering h) (fun s => scatteringCoefficient s h) U := by
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp (cuspWhittakerHeightFactor_ne_zero_near_five h)
  let z : ℂ := 5+(ε/2:ℝ)*Complex.I
  have hz : dist z (5:ℂ)<ε := by
    have hdist : dist z (5:ℂ)=ε/2 := by
      simp [z,dist_eq_norm,hε.le]
    rw [hdist]
    linarith
  have hzim : 0<z.im := by simpa [z] using half_pos hε
  refine ⟨Metric.ball (5:ℂ) ε ∩ {s : ℂ | 0<s.im},
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im),⟨z,hz,hzim⟩,?_,?_⟩
  · intro s hs
    exact ⟨(hball hs.1).1,hs.2⟩
  · intro s hs
    exact continuedNonzeroScattering_initial h hh s (hball hs.1).1 hs.2 (hball hs.1).2

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

lemma weightedWhittakerIntegrand_integrable (ρ : BoundedContinuousFunction ℝ ℂ) (freq s : ℂ) (hs : 1<s.re) :
    Integrable (fun p : ℝ × ℂ => ρ p.1*whittakerIntegrand freq s p) whittakerProductVolume := by
  apply ((whittaker_bound_integrable s.re hs).const_mul ‖ρ‖).mono'
  · exact ((ρ.continuous.comp continuous_fst).mul (whittakerIntegrand_continuous freq s)).aestronglyMeasurable
  · exact Eventually.of_forall (fun p => by
      rw [norm_mul]
      exact mul_le_mul (ρ.norm_coe_le_norm p.1)
        (whittakerIntegrand_norm_bound freq s p s.re (by linarith) le_rfl) (norm_nonneg _) (norm_nonneg _))

lemma weightedWhittakerProduct_differentiableAt (ρ : BoundedContinuousFunction ℝ ℂ) (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ
      (fun w => ∫p : ℝ × ℂ,ρ p.1*whittakerIntegrand freq w p∂whittakerProductVolume) s := by
  let b : ℝ := (s.re+1)/2
  let ε : ℝ := (s.re-1)/4
  have hb : 1<b := by dsimp [b]; linarith
  have hε : 0<ε := by dsimp [ε]; linarith
  have hsb : b+ε<s.re := by dsimp [b,ε]; linarith
  have hU : {w : ℂ | b+ε<w.re}∈𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsb
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ» := whittakerProductVolume)
    (F := fun w (p : ℝ × ℂ) => ρ p.1*whittakerIntegrand freq w p)
    (F' := fun w (p : ℝ × ℂ) => ρ p.1*whittakerIntegrandDeriv freq w p)
    (bound := fun p => ‖ρ‖*(ε⁻¹*(1+‖p.2‖^2)^(-b))) hU
    (Eventually.of_forall (fun w =>
      ((ρ.continuous.comp continuous_fst).mul (whittakerIntegrand_continuous freq w)).aestronglyMeasurable))
    (weightedWhittakerIntegrand_integrable ρ freq s hs)
    ((ρ.continuous.comp continuous_fst).mul (whittakerIntegrandDeriv_continuous freq s)).aestronglyMeasurable
    (Eventually.of_forall (fun p w hw => by
      rw [norm_mul]
      exact mul_le_mul (ρ.norm_coe_le_norm p.1)
        (whittakerIntegrandDeriv_norm_bound freq w p b ε (by linarith) hε hw.le)
        (norm_nonneg _) (norm_nonneg _)))
