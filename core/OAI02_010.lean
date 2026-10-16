  unfold reflectionLocalCost
  split_ifs <;> positivity

theorem reflectionLocalCost_le_square (q : ℝ) (hq : 1≤q) (j : ℕ) (e : Fin 3) :
    reflectionLocalCost q j e≤q^2 := by
  have hq0 : 0<q := by linarith
  have hq2 : 1≤q^2 := one_le_pow₀ hq
  unfold reflectionLocalCost
  split_ifs
  · exact (div_le_one (by positivity)).mpr hq2 |>.trans hq2
  · nlinarith
  · nlinarith
  · rfl

theorem reflectionLocalCost_le_single (q : ℝ) (hq : 1≤q) (j : ℕ) (e : Fin 3)
    (hj : j=0 ∨ j=4) : reflectionLocalCost q j e≤q := by
  have hq0 : 0<q := by linarith
  rcases hj with rfl|rfl
  · simp [reflectionLocalCost]
  · simp only [reflectionLocalCost,ite_true]
    split_ifs
    · exact ((div_le_one (by positivity)).mpr (one_le_pow₀ hq)).trans hq
    · rfl

theorem completedLocalExponent_of_not_dvd (I F P : Ideal O) (hI : I≠0) (_hP : Prime P)
    (hn : ¬P∣I) : completedLocalExponent I F P=0 ∨ completedLocalExponent I F P=4 := by
  have hm : P∉normalizedFactors I := by
    intro h
    exact hn ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mp h).2
  simp only [completedLocalExponent,Multiset.count_eq_zero.mpr hm,zero_add]
  split_ifs <;> norm_num

theorem reflectionLocalCost_le_gain (I F P : Ideal O) (hI : I≠0) (hP : Prime P) (e : Fin 3) :
    reflectionLocalCost (Ideal.absNorm P:ℝ) (completedLocalExponent I F P) e≤
      (Ideal.absNorm (nonresidualGain I P):ℝ) := by
  have hq : 1≤(Ideal.absNorm P:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hP.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
  by_cases hd : P∣I
  · rw [nonresidualGain,ite_eq_left hd,map_pow,Nat.cast_pow]
    exact reflectionLocalCost_le_square _ hq _ _
  · rw [nonresidualGain,ite_eq_right hd]
    exact reflectionLocalCost_le_single _ hq _ _ (completedLocalExponent_of_not_dvd I F P hI hP hd)

theorem reflectionConductorCost_bound {ι : Type*} [Fintype ι]
    (I F Q : Ideal O) (hI : I≠0) (hQ : Q≠0)
    (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀i,P i∣I*Q) (hres : ∀i,¬P i∣rowResidualPart I Q) (e : ι→Fin 3) :
    reflectionConductorCost P (fun i => completedLocalExponent I F (P i)) e≤
      (Ideal.absNorm (rowPowerfulPart I):ℝ)*(Ideal.absNorm (rowMaskPart I Q):ℝ)^2*(Ideal.absNorm Q:ℝ) := by
  rw [reflectionConductorCost_eq_prod P (fun i => NeZero.ne (P i))]
  have hfirst : (∏i,reflectionLocalCost (Ideal.absNorm (P i):ℝ) (completedLocalExponent I F (P i)) (e i))≤
      (Ideal.absNorm (∏i,nonresidualGain I (P i)):ℝ) := by
    rw [map_prod,Nat.cast_prod]
    exact Finset.prod_le_prod₀ (fun i _ => reflectionLocalCost_nonneg _ (Nat.cast_nonneg _) _ _)
      (fun i _ => reflectionLocalCost_le_gain I F (P i) hI (Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance) (e i))
  apply hfirst.trans
  have hd := nonresidual_gain_product_dvd I Q hI P hcop hpool hres
  have hN : 0<Ideal.absNorm (rowPowerfulPart I*(rowMaskPart I Q)^2*Q) := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hne := mul_ne_zero (mul_ne_zero (rowPowerfulPart_ne_zero I)
      (pow_ne_zero 2 (squarefreeMaskPart_ne_zero (rowSimplePart I) Q))) hQ
    exact hne (Ideal.absNorm_eq_zero_iff.mp hz)
  have hb := Nat.le_of_dvd hN (map_dvd Ideal.absNorm hd)
  have hr : (Ideal.absNorm (∏i,nonresidualGain I (P i)):ℝ)≤
      (Ideal.absNorm (rowPowerfulPart I*(rowMaskPart I Q)^2*Q):ℝ) := by exact_mod_cast hb
  simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using hr

end CompletedGauss

end

end OAI
end OAIOriginalModule0198

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.ReflectedBranches
Source SHA256: ec2f89738ea74354e0b152f496b0e248a203130fd78cb778b8aee0ec332755d4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0199


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
namespace CompletedGauss

section
open ActualEisensteinCubic LocalReflectionBrackets

def reflectedLocalPiece (P : Ideal O) [P.IsMaximal] (hg : lambda∉P)
    (j : ℕ) (e : Fin 3) (n b : O) : ℂ :=
  if j=4 then exceptionalPiece P e n b
  else if e=0 then bracket (actualSextic P hg) j (Ideal.Quotient.mk P (n*b^3)) else 0

def reflectedLocalSize (P : Ideal O) [P.IsMaximal] (j : ℕ) (e : Fin 3) : ℝ :=
  if j=4 then (if e=0 then (rootCard (O ⧸ P))⁻¹ else rootCard (O ⧸ P))
  else if j=0 then (rootCard (O ⧸ P))⁻¹ else 1

def reflectedBranch {ι : Type*} [Fintype ι] (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hg : ∀i,lambda∉P i) (j : ι→ℕ) (e : ι→Fin 3) (n b : O) : ℂ :=
  ∏i,reflectedLocalPiece (P i) (hg i) (j i) (e i) n b

theorem bracket_eq_sum_reflectedLocalPiece (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (j : ℕ) (n b : O) :
    bracket (actualSextic P hg) j (Ideal.Quotient.mk P (n*b^3))=
      ∑e : Fin 3, reflectedLocalPiece P hg j e n b := by
  by_cases hj : j=4
  · subst j
    simpa only [reflectedLocalPiece,ite_true] using bracket_four_eq_sum_exceptionalPiece P hg n b
  · simp [reflectedLocalPiece,hj]

theorem prod_bracket_eq_full_branches {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (n b : O) :
    (∏i,bracket (actualSextic (P i) (hg i)) (j i) (Ideal.Quotient.mk (P i) (n*b^3)))=
      ∑e : ι→Fin 3,reflectedBranch P hg j e n b := by
  simp_rw [bracket_eq_sum_reflectedLocalPiece]
  simpa only [Fintype.piFinset_univ,reflectedBranch] using
    Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset (Fin 3)))
      (fun i e => reflectedLocalPiece (P i) (hg i) (j i) e n b)

theorem reflectedLocalPiece_norm_le (P : Ideal O) [P.IsMaximal] (hg : lambda∉P)
    (j : ℕ) (e : Fin 3) (n b : O) :
    ‖reflectedLocalPiece P hg j e n b‖≤reflectedLocalSize P j e := by
  have hr : 0<rootCard (O ⧸ P) := rootCard_pos
  by_cases hj4 : j=4
  · subst j
    simpa only [reflectedLocalPiece,reflectedLocalSize,ite_true] using exceptionalPiece_norm_le P e n b
  · by_cases he : e=0
    · rw [reflectedLocalPiece,ite_eq_right hj4,ite_eq_left he,reflectedLocalSize,ite_eq_right hj4]
      by_cases hj0 : j=0
      · subst j
        simpa only [ite_true] using norm_bracket_zero_le (actualSextic P hg) (Ideal.Quotient.mk P (n*b^3))
      · rw [ite_eq_right hj0]
        exact norm_bracket_nonexceptional_le_one _ j hj4 hj0 _
    · simp only [reflectedLocalPiece,ite_eq_right hj4,ite_eq_right he,norm_zero,reflectedLocalSize]
      split_ifs <;> positivity

theorem sqrt_norm_reflectionExtractedDivisor {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (j : ι→ℕ) (e : ι→Fin 3) (v : Fin 3) :
    Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e v):ℝ)=
      ∏i,if (j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0) then rootCard (O ⧸ P i) else 1 := by
  rw [reflectionExtractedDivisor,map_prod,Nat.cast_prod,Real.sqrt_prod]
  · apply Finset.prod_congr rfl
    intro i _
    unfold reflectionExtractedPrime
    split_ifs
    · rw [rootCard_eq_sqrt_absNorm]
    · simp
  · intro i _
    exact Nat.cast_nonneg _

theorem reflectedBranch_norm_bound {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (n b : O) :
    ‖reflectedBranch P hg j e n b‖≤
      Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*
      Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)/
      Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ) := by
  have hb : ‖reflectedBranch P hg j e n b‖≤∏i,reflectedLocalSize (P i) (j i) (e i) := by
    rw [reflectedBranch,norm_prod]
    exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
      (fun i _ => reflectedLocalPiece_norm_le (P i) (hg i) (j i) (e i) n b)
  apply hb.trans_eq
  rw [sqrt_norm_reflectionExtractedDivisor,sqrt_norm_reflectionExtractedDivisor,
    sqrt_norm_reflectionExtractedDivisor,←Finset.prod_mul_distrib,←Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hj4 : j i=4
  · rw [hj4]
    generalize e i=x
    fin_cases x <;> simp [reflectedLocalSize]
  · by_cases hj0 : j i=0
    · simp [reflectedLocalSize,hj0]
    · simp [reflectedLocalSize,hj4,hj0]

theorem reflectionExtractedDivisor_ne_zero {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) (hP : ∀i,P i≠0) (j : ι→ℕ) (e : ι→Fin 3) (v : Fin 3) :
    reflectionExtractedDivisor P j e v≠0 := by
  unfold reflectionExtractedDivisor
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  unfold reflectionExtractedPrime
  split_ifs
  · exact hP i
  · exact one_ne_zero

theorem reflectedBranch_normalized_bound {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (n b : O) (U B : ℝ) (hU : 0<U) (hB : 0<B) :
    ‖reflectedBranch P hg j e n b‖ /
      (Real.sqrt ((Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*U)*
        ((Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)*B)) ≤
      1/(Real.sqrt U*B*Real.sqrt ((Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
        (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ))) := by
  have hn (v : Fin 3) : 0<(Ideal.absNorm (reflectionExtractedDivisor P j e v):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) j e v
      (Ideal.absNorm_eq_zero_iff.mp hz))
  have hs (v : Fin 3) : 0<Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e v):ℝ) := Real.sqrt_pos.mpr (hn v)
  have hsu : 0<Real.sqrt U := Real.sqrt_pos.mpr hU
  apply (div_le_div_of_nonneg_right (reflectedBranch_norm_bound P hg j e n b) (by positivity)).trans
  rw [Real.sqrt_mul (hn 1).le,Real.sqrt_mul (hn 0).le]
  have he := Real.sq_sqrt (hn 2).le
  apply le_of_eq
  field_simp [(hs 0).ne', (hs 1).ne', (hs 2).ne', (hn 2).ne', hsu.ne', hB.ne']
  nlinarith

theorem reflectedBranch_divisibility {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (hcop : Pairwise (fun i k => IsCoprime (P i) (P k)))
    (j : ι→ℕ) (e : ι→Fin 3) (n b : O) (hne : reflectedBranch P hg j e n b≠0) :
    reflectionExtractedDivisor P j e 1∣Ideal.span {n} ∧
    reflectionExtractedDivisor P j e 2∣Ideal.span {b} ∧
    (∀i,j i=4 → e i=2 → n∉P i) := by
  have hn i : reflectedLocalPiece (P i) (hg i) (j i) (e i) n b≠0 :=
    (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)
  have hmemn i (hj : j i=4) (he : e i=1) : n∈P i := by
    by_contra hz
    exact hn i (by simp [reflectedLocalPiece,exceptionalPiece,hj,he,hz])
  have hmemb i (hj : j i=4) (he : e i=2) : n∉P i ∧ b∈P i := by
    by_contra hz
    exact hn i (by simp [reflectedLocalPiece,exceptionalPiece,hj,he,hz])
  have hprod (v : Fin 3) (z : O)
      (hz : ∀i,(j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0) → z∈P i) :
      reflectionExtractedDivisor P j e v∣Ideal.span {z} := by
    unfold reflectionExtractedDivisor reflectionExtractedPrime
    apply Fintype.prod_dvd_of_coprime
    · intro i k hik
      change IsCoprime (if (j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0) then P i else 1)
        (if (j k=4 ∧ e k=v) ∨ (j k=0 ∧ v=0) then P k else 1)
      by_cases hi : (j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0)
      · rw [ite_eq_left hi]
        by_cases hk : (j k=4 ∧ e k=v) ∨ (j k=0 ∧ v=0)
        · rw [ite_eq_left hk]
          exact hcop hik
        · rw [ite_eq_right hk]
          exact isCoprime_one_right
      · rw [ite_eq_right hi]
        exact isCoprime_one_left
    · intro i
      split_ifs with hi
      · rw [Ideal.dvd_iff_le,Ideal.span_le,Set.singleton_subset_iff,SetLike.mem_coe]
        exact hz i hi
      · exact one_dvd _
  refine ⟨hprod 1 n ?_,hprod 2 b ?_,fun i hj he => (hmemb i hj he).1⟩
  · intro i hi
    rcases hi with ⟨hj,he⟩|⟨hj,he⟩
    · exact hmemn i hj he
    · norm_num at he
  · intro i hi
    rcases hi with ⟨hj,he⟩|⟨hj,he⟩
    · exact (hmemb i hj he).2
    · norm_num at he

end

open scoped BigOperators Classical SchwartzMap ContDiff Topology
open MeasureTheory Filter

theorem Vstar_contDiff (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (Vstar W) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x=0
  · subst x
    have hz : (Vstar W)=ᶠ[𝓝 (0:ℝ)] (fun _ => (0:ℂ)) := by
      filter_upwards [isOpen_Iio.mem_nhds ha] with y hy
      change y<a at hy
      have hw : W y=0 := by
        by_contra hn
        have hh := (hsupp hn).1
        linarith
      simp only [Vstar,hw,mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq hz
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_sqrt hx)).mul hW.contDiffAt

theorem Vstar_support (W : ℝ→ℂ) (a b : ℝ)
    (hsupp : Function.support W⊆Set.Icc a b) : Function.support (Vstar W)⊆Set.Icc a b := by
  intro x hx
  apply hsupp
  intro hz
  exact hx (by simp [Vstar,hz])

def vstarSchwartz (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(ℝ,ℂ) :=
  (HasCompactSupport.of_support_subset_isCompact isCompact_Icc (Vstar_support W a b hsupp)).toSchwartzMap
    (Vstar_contDiff W a b ha hsupp hW)

@[simp] theorem vstarSchwartz_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) (x : ℝ) :
    vstarSchwartz W a b ha hsupp hW x=Vstar W x := rfl

theorem completed_kernel_log_separation
    {ι : Type*} [Fintype ι] (V : ι→ℝ→ℂ) (slope M : ι→ℝ)
    (hM : ∀i,0≤M i) (hV : ∀i y,V i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (A J : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀R : ℝ,0<R → ∃B : 𝓢(ℝ,ℂ),
      (∀y : ι→ℝ,(∏i,V i (y i))*CubicReflectionKernel.paperKernel (Vstar W)
          (R*Real.exp (∑i,slope i*y i))=
        ∫t : ℝ,(∏i,V i (y i)*FourierBridge.logPhase t (slope i*y i))*B t) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖B t‖) volume ∧
      (1+R)^A*(∫t : ℝ,(1+‖t‖)^J*‖B t‖)≤C ∧
      (∀t : ℝ,(1+R)^A*(1+‖t‖)^J*‖B t‖≤C) := by
  let S := vstarSchwartz W a b ha hsupp hW
  obtain ⟨s,D,hD,hbound⟩ := CubicReflectionKernel.paperKernel_euler_source_uniform_weighted_bound
    a b ha A (J+(volume : Measure ℝ).integrablePower)
  have hF := CubicReflectionKernel.paperKernel_compact_source_smooth (Vstar W) a b ha
    (Vstar_support W a b hsupp) (Vstar_contDiff W a b ha hsupp hW)
  apply LocalLogFourier.coupled_positive_log_separation_envelope V (CubicReflectionKernel.paperKernel (Vstar W))
    slope M hM hV hF A J (D*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) S) (by positivity)
  intro i hi x hx
  have he : (S : ℝ→ℂ)=Vstar W := rfl
  have hb := hbound S (Vstar_support W a b hsupp) i hi x hx
  rw [he] at hb
  exact hb

end CompletedGauss

namespace InitialMeanSquare
open SecondPassArithmetic

theorem initial_bin_invariant (Z H B R : ℝ) (j : SecondLogIndex)
    (hZ : Z≠0) (hH : H≠0) (hB : B≠0) :
    (secondLogK j*Real.exp 2)*R/(initialLogColumn Z B j*initialLogLabel j)=
      (R/B)*(Z/H)*(H*secondLogK j*B^2/Z^2) := by
  rw [initial_log_mass Z B hB j]
  have hexp : Real.exp 2≠0 := (Real.exp_pos _).ne'
  field_simp

theorem initial_bin_invariant_le (Z H B R c : ℝ) (j : SecondLogIndex)
    (hZ : 0<Z) (hH : 0<H) (hB : 0<B) (hR : R≤c*B) :
    (secondLogK j*Real.exp 2)*R/(initialLogColumn Z B j*initialLogLabel j)≤
      c*(Z/H)*(H*secondLogK j*B^2/Z^2) := by
  rw [initial_bin_invariant Z H B R j hZ.ne' hH.ne' hB.ne']
  have hr : R/B≤c := (div_le_iff₀ hB).mpr hR
  have hk : 0<secondLogK j := normLogScale_pos _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hr (div_nonneg hZ.le hH.le)) (by positivity)

theorem initial_small_radial_admissible (Z B R c σ θ deltaLoss : ℝ) (j : SecondLogIndex)
    (hZ : 1≤Z) (hB : 0<B) (hR : R≤c*B) (hc : 0≤c) (hcZ : c≤Z^deltaLoss)
    (hmargin : deltaLoss+θ≤σ-(1:ℝ)/40)
    (hrad : Z^(1+σ)*secondLogK j*B^2/Z^2≤Z^θ) :
    (secondLogK j*Real.exp 2)*R≤
      initialLogColumn Z B j*initialLogLabel j*Z^(-(1:ℝ)/40) := by
  have hZ0 : 0<Z := by linarith
  have hH : 0<Z^(1+σ) := Real.rpow_pos_of_pos hZ0 _
  have hm : 0 < initialLogColumn Z B j*initialLogLabel j := by
    rw [initial_log_mass Z B hB.ne' j]
    positivity
  have he : Z/Z^(1+σ)=Z^(-σ) := by
    calc
      _ = Z^((1:ℝ)-(1+σ)) := by rw [Real.rpow_sub hZ0,Real.rpow_one]
      _ = _ := by congr 1; ring
  have hb := initial_bin_invariant_le Z (Z^(1+σ)) B R c j hZ0 hH hB hR
  rw [he] at hb
  rw [mul_comm (initialLogColumn Z B j*initialLogLabel j)]
  apply (div_le_iff₀ hm).mp
  apply hb.trans
  calc
    c*Z^(-σ)*(Z^(1+σ)*secondLogK j*B^2/Z^2) ≤ c*Z^(-σ)*Z^θ :=
      mul_le_mul_of_nonneg_left hrad (mul_nonneg hc (Real.rpow_nonneg hZ0.le _))
    _ ≤ Z^deltaLoss*Z^(-σ)*Z^θ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcZ (Real.rpow_nonneg hZ0.le _)) (Real.rpow_nonneg hZ0.le _)
    _ = Z^(deltaLoss-σ+θ) := by rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]; simp only [sub_eq_add_neg]
    _ ≤ Z^(-(1:ℝ)/40) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

end InitialMeanSquare

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups Matrix InnerProductSpace

def hyperbolicEuclideanCoordinates (w : HyperbolicSpace) : EuclideanSpatial :=
  WithLp.toLp 2 (hyperbolicSpatialCoordinates w)

lemma hyperbolicEuclideanCoordinates_upperPoint (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicEuclideanCoordinates (upperPoint z v hv)=WithLp.toLp 2 ![z.re,z.im,v] := by
  simp only [hyperbolicEuclideanCoordinates,hyperbolicSpatialCoordinates,
    hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint]

lemma euclideanToHyperbolic_coordinates (w : HyperbolicSpace) :
    euclideanToHyperbolic (hyperbolicEuclideanCoordinates w)=w := by
  have hp : 0<hyperbolicEuclideanCoordinates w 2 := hyperbolicHeight_pos w
  rw [euclideanToHyperbolic_positive _ hp]
  change upperPoint ((hyperbolicSpatialCoordinates w 0:ℂ)+Complex.I*(hyperbolicSpatialCoordinates w 1:ℂ))
    (hyperbolicSpatialCoordinates w 2) hp=w
  simpa only [mul_comm] using hyperbolicSpatialCoordinates_reconstruct w

lemma hyperbolicEuclideanCoordinates_toHyperbolic (p : EuclideanSpatial) (hp : 0<p 2) :
    hyperbolicEuclideanCoordinates (euclideanToHyperbolic p)=p := by
  rw [euclideanToHyperbolic_positive _ hp,hyperbolicEuclideanCoordinates_upperPoint]
  apply (WithLp.equiv 2 (Fin 3→ℝ)).injective
  funext j
  fin_cases j <;> simp

def euclideanAction (g : SL(2,ℂ)) (p : EuclideanSpatial) : EuclideanSpatial :=
  hyperbolicEuclideanCoordinates (g•euclideanToHyperbolic p)

lemma euclideanAction_positive (g : SL(2,ℂ)) (p : EuclideanSpatial) :
    0<euclideanAction g p 2 := by
  change 0<hyperbolicHeight (g•euclideanToHyperbolic p)
  exact hyperbolicHeight_pos _

lemma euclideanAction_mul (g h : SL(2,ℂ)) :
    euclideanAction (g*h)=euclideanAction g ∘ euclideanAction h := by
  funext p
  simp only [euclideanAction,Function.comp_apply,euclideanToHyperbolic_coordinates,mul_smul]

lemma euclideanAction_translation (b : ℂ) (p : EuclideanSpatial) (hp : 0<p 2) :
    euclideanAction (complexTranslation b) p=p+euclideanHorizontalTranslation b := by
  rw [euclideanAction,euclideanToHyperbolic_positive _ hp,complexTranslation_action,
    hyperbolicEuclideanCoordinates_upperPoint]
  apply (WithLp.equiv 2 (Fin 3→ℝ)).injective
  funext j
  fin_cases j <;> simp [euclideanHorizontalTranslation]

lemma euclideanAction_diagonal (b : ℂ) (hb : b≠0) (p : EuclideanSpatial) (hp : 0<p 2) :
    euclideanAction (complexDiagonal b hb) p=euclideanComplexDilation b p := by
  rw [euclideanAction,euclideanToHyperbolic_positive _ hp,complexDiagonal_action,
    hyperbolicEuclideanCoordinates_upperPoint]
  obtain ⟨h0,h1,h2⟩ := euclideanComplexDilation_apply b p
  apply (WithLp.equiv 2 (Fin 3→ℝ)).injective
  funext j
  fin_cases j
  · simpa [Complex.mul_re] using h0.symm
  · simpa [Complex.mul_im,add_comm] using h1.symm
  · exact h2.symm

lemma euclideanAction_weyl (p : EuclideanSpatial) (hp : 0<p 2) :
    euclideanAction complexWeyl p=euclideanWeylAction p := by
  have hn : ‖p‖≠0 := norm_ne_zero_iff.mpr (euclideanUpperHalf_ne_zero p hp)
  have hnc : (‖p‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hn
  have hq : 0<euclideanWeylAction p 2 := by
    rw [(euclideanWeylAction_apply p).2.2]
    exact mul_pos (sq_pos_of_ne_zero (one_div_ne_zero hn)) hp
  have h := congrArg hyperbolicEuclideanCoordinates
    (show euclideanToHyperbolic (euclideanWeylAction p)=
      complexWeyl•euclideanToHyperbolic p from by
      rw [euclideanToHyperbolic_positive _ hq,euclideanToHyperbolic_positive _ hp,complexWeyl_action]
      obtain ⟨h0,h1,h2⟩ := euclideanWeylAction_apply p
      apply upperPoint_congr
      · rw [h0,h1,euclidean_complex_norm_sq]
        simp only [Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_div,
          Complex.ofReal_one,Complex.star_def,map_add,map_mul,Complex.conj_ofReal,Complex.conj_I]
        field_simp
        ; ring
      · rw [h2,euclidean_complex_norm_sq]
        field_simp)
  simpa only [hyperbolicEuclideanCoordinates_toHyperbolic _ hq,euclideanAction] using h.symm

lemma euclideanWeylReflection_norm (u : EuclideanSpatial) : ‖euclideanWeylReflection u‖=‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  obtain ⟨h0,h1,h2⟩ := euclideanWeylReflection_apply u
  simp only [Fin.sum_univ_three,h0,h1,h2,neg_sq]

lemma euclideanComplexDilation_norm (b : ℂ) (u : EuclideanSpatial) :
    ‖euclideanComplexDilation b u‖=Complex.normSq b*‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Complex.normSq_nonneg _) (norm_nonneg _))).mp
  have h : (b^2).re^2+(b^2).im^2=(Complex.normSq b)^2 := by
    simpa [Complex.normSq_apply,sq] using map_pow Complex.normSq b 2
  rw [mul_pow,EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  obtain ⟨h0,h1,h2⟩ := euclideanComplexDilation_apply b u
  simp only [Fin.sum_univ_three,h0,h1,h2]
  calc
    _ = ((b^2).re^2+(b^2).im^2)*((u 0)^2+(u 1)^2)+(Complex.normSq b)^2*(u 2)^2 := by ring
    _ = _ := by rw [h]; ring

lemma euclideanInversionDeriv_norm (p u : EuclideanSpatial) :
    ‖euclideanInversionDeriv p u‖=(1/‖p‖)^2*‖u‖ := by
  unfold euclideanInversionDeriv
  rw [_root_.smul_apply,norm_smul,Real.norm_of_nonneg (sq_nonneg _)]
  simp only [LinearIsometryEquiv.coe_coe'',LinearIsometryEquiv.norm_map]

def HyperbolicDifferentialIsometry (g : SL(2,ℂ)) : Prop :=
  ∀p : EuclideanSpatial,0<p 2 → ∃A : EuclideanSpatial→L[ℝ]EuclideanSpatial,
    HasFDerivAt (euclideanAction g) A p ∧
    ∀u,‖A u‖*p 2=‖u‖*euclideanAction g p 2

lemma hyperbolicDifferentialIsometry_mul (g h : SL(2,ℂ))
    (hg : HyperbolicDifferentialIsometry g) (hh : HyperbolicDifferentialIsometry h) :
    HyperbolicDifferentialIsometry (g*h) := by
  intro p hp
  obtain ⟨B,hB,hBn⟩ := hh p hp
  obtain ⟨A,hA,hAn⟩ := hg (euclideanAction h p) (euclideanAction_positive h p)
  refine ⟨A.comp B,?_,?_⟩
  · rw [euclideanAction_mul]
    exact hA.comp p hB
  · intro u
    rw [euclideanAction_mul]
    change ‖A (B u)‖*p 2=‖u‖*euclideanAction g (euclideanAction h p) 2
    apply (mul_right_inj' (euclideanAction_positive h p).ne').mp
    calc
      _ = (‖A (B u)‖*euclideanAction h p 2)*p 2 := by ring
      _ = (‖B u‖*euclideanAction g (euclideanAction h p) 2)*p 2 := by rw [hAn]
      _ = (‖B u‖*p 2)*euclideanAction g (euclideanAction h p) 2 := by ring
      _ = _ := by rw [hBn]; ring

lemma hyperbolicDifferentialIsometry_translation (b : ℂ) :
    HyperbolicDifferentialIsometry (complexTranslation b) := by
  intro p hp
  refine ⟨ContinuousLinearMap.id ℝ _,?_,?_⟩
  · apply ((hasFDerivAt_id p).add_const (euclideanHorizontalTranslation b)).congr_of_eventuallyEq
    filter_upwards [(by fun_prop : Continuous (fun p : EuclideanSpatial => p 2)).continuousAt.eventually_const_lt hp]
      with q hq
    exact euclideanAction_translation b q hq
  · intro u
    rw [euclideanAction_translation b p hp]
    simp [euclideanHorizontalTranslation]

lemma hyperbolicDifferentialIsometry_diagonal (b : ℂ) (hb : b≠0) :
    HyperbolicDifferentialIsometry (complexDiagonal b hb) := by
  intro p hp
  refine ⟨euclideanComplexDilation b,?_,?_⟩
  · apply (euclideanComplexDilation b).hasFDerivAt.congr_of_eventuallyEq
    filter_upwards [(by fun_prop : Continuous (fun p : EuclideanSpatial => p 2)).continuousAt.eventually_const_lt hp]
      with q hq
    exact euclideanAction_diagonal b hb q hq
  · intro u
    rw [euclideanComplexDilation_norm,euclideanAction_diagonal b hb p hp,
      (euclideanComplexDilation_apply b p).2.2]
    ring

lemma hyperbolicDifferentialIsometry_weyl : HyperbolicDifferentialIsometry complexWeyl := by
  intro p hp
  refine ⟨euclideanWeylReflection.comp (euclideanInversionDeriv p),?_,?_⟩
  · have h := euclideanWeylReflection.hasFDerivAt.comp p
      (euclideanInversion_hasFDerivAt p (euclideanUpperHalf_ne_zero p hp))
    apply h.congr_of_eventuallyEq
    filter_upwards [(by fun_prop : Continuous (fun p : EuclideanSpatial => p 2)).continuousAt.eventually_const_lt hp]
      with q hq
    exact euclideanAction_weyl q hq
  · intro u
    change ‖euclideanWeylReflection (euclideanInversionDeriv p u)‖*p 2=_
    rw [euclideanWeylReflection_norm,euclideanInversionDeriv_norm,euclideanAction_weyl p hp,
      (euclideanWeylAction_apply p).2.2]
    ring

theorem hyperbolicDifferentialIsometry (g : SL(2,ℂ)) : HyperbolicDifferentialIsometry g := by
  by_cases hc : g 1 0=0
  · obtain ⟨ha,hg⟩ := complex_bruhat_zero g hc
    rw [hg]
    exact hyperbolicDifferentialIsometry_mul _ _ (hyperbolicDifferentialIsometry_diagonal _ ha)
      (hyperbolicDifferentialIsometry_translation _)
  · rw [complex_bruhat_nonzero g hc]
    exact hyperbolicDifferentialIsometry_mul _ _
      (hyperbolicDifferentialIsometry_mul _ _
        (hyperbolicDifferentialIsometry_mul _ _ (hyperbolicDifferentialIsometry_translation _)
          (hyperbolicDifferentialIsometry_diagonal _ (inv_ne_zero hc)))
        hyperbolicDifferentialIsometry_weyl)
      (hyperbolicDifferentialIsometry_translation _)

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups

namespace CubicEisenstein

lemma norm_comp_scaled_isometry (A : EuclideanSpatial→L[ℝ]EuclideanSpatial) (r : ℝ)
    (hr : 0<r) (hA : ∀u,‖A u‖=r*‖u‖) (φ : EuclideanSpatial→L[ℝ]ℝ) :
    ‖φ.comp A‖=r*‖φ‖ := by
  let iso : EuclideanSpatial→ₗᵢ[ℝ]EuclideanSpatial :=
    { toLinearMap := (r⁻¹ • A).toLinearMap
      norm_map' := fun u => by
        change ‖r⁻¹ • A u‖=‖u‖
        rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le),hA]
        field_simp }
  let equiv : EuclideanSpatial≃ₗᵢ[ℝ]EuclideanSpatial :=
    LinearIsometryEquiv.ofSurjective iso ((LinearMap.injective_iff_surjective).mp iso.injective)
  have he : A=r • (equiv : EuclideanSpatial→L[ℝ]EuclideanSpatial) := by
    apply ContinuousLinearMap.ext
    intro u
    change A u=r • (r⁻¹ • A u)
    rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  rw [he,ContinuousLinearMap.comp_smul,norm_smul,Real.norm_of_nonneg hr.le,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

lemma hyperbolic_cotangent_energy_comp (g : SL(2,ℂ)) (F : EuclideanSpatial→ℝ)
    (p : EuclideanSpatial) (hp : 0<p 2) (hF : DifferentiableAt ℝ F (euclideanAction g p)) :
    (p 2)^2*‖fderiv ℝ (F ∘ euclideanAction g) p‖^2=
      (euclideanAction g p 2)^2*‖fderiv ℝ F (euclideanAction g p)‖^2 := by
  obtain ⟨A,hA,hAn⟩ := hyperbolicDifferentialIsometry g p hp
  rw [(hF.hasFDerivAt.comp p hA).fderiv]
  have hn : ∀u,‖A u‖=(euclideanAction g p 2/p 2)*‖u‖ := by
    intro u
    calc
      ‖A u‖=(‖u‖*euclideanAction g p 2)/p 2 := (eq_div_iff hp.ne').2 (hAn u)
      _ = _ := by ring
  rw [norm_comp_scaled_isometry A _ (div_pos (euclideanAction_positive g p) hp) hn]
  field_simp

def euclideanScalarDirichletDensity (F : EuclideanSpatial→ℝ) (p : EuclideanSpatial) : ℝ :=
  (p 2)^2*‖fderiv ℝ F p‖^2

lemma euclideanScalarDirichletDensity_invariant (g : SL(2,ℂ)) (F : EuclideanSpatial→ℝ)
    (p : EuclideanSpatial) (hp : 0<p 2) (hF : DifferentiableAt ℝ F (euclideanAction g p))
    (hinv : F ∘ euclideanAction g=F) :
    euclideanScalarDirichletDensity F (euclideanAction g p)=euclideanScalarDirichletDensity F p := by
  have h := hyperbolic_cotangent_energy_comp g F p hp hF
  rw [hinv] at h
  exact h.symm

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups

namespace CubicEisenstein

lemma hyperbolicEuclideanCoordinates_continuous : Continuous hyperbolicEuclideanCoordinates :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.continuous.comp
    hyperbolicSpatialCoordinates_continuous

lemma hyperbolicSpatialChart_toHyperbolic (p : EuclideanSpatial) (hp : 0<p 2) :
    hyperbolicSpatialChart (euclideanToHyperbolic p)=p.ofLp :=
  congrArg WithLp.ofLp (hyperbolicEuclideanCoordinates_toHyperbolic p hp)

lemma euclideanToHyperbolic_contMDiffAt (p : EuclideanSpatial) (hp : 0<p 2) :
    ContMDiffAt 𝓘(ℝ,EuclideanSpatial) 𝓘(ℝ,SpatialCoordinates) ∞ euclideanToHyperbolic p := by
  have ht : p.ofLp∈hyperbolicSpatialChart.target := by
    rw [←hyperbolicSpatialChart_toHyperbolic p hp]
    exact hyperbolicSpatialChart.map_source (Set.mem_univ _)
  have hs : ContMDiffOn 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,SpatialCoordinates) ∞
      hyperbolicSpatialChart.symm hyperbolicSpatialChart.target := by
    simpa only [hyperbolicSpatial_chartAt] using
      (contMDiffOn_chart_symm (I := 𝓘(ℝ,SpatialCoordinates)) (n := ∞) (x := euclideanToHyperbolic p))
  have hd := (hs.contMDiffAt (hyperbolicSpatialChart.open_target.mem_nhds ht)).comp p
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).contDiff.contDiffAt.contMDiffAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [(by fun_prop : Continuous (fun p : EuclideanSpatial => p 2)).continuousAt.eventually_const_lt hp]
    with q hq
  change euclideanToHyperbolic q=hyperbolicSpatialChart.symm q.ofLp
  rw [←hyperbolicSpatialChart_toHyperbolic q hq,hyperbolicSpatialChart.left_inv (Set.mem_univ _)]

def kernelTestField (f : kernelSmoothTests) (p : EuclideanSpatial) : ℂ :=
  f.1 (integralOrbitProjection globalKubotaKernel (euclideanToHyperbolic p))

lemma kernelTestField_contDiffAt (f : kernelSmoothTests) (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (kernelTestField f) p :=
  (((f.2.1.comp kernelProjection_contMDiff) (euclideanToHyperbolic p)).comp p
    (euclideanToHyperbolic_contMDiffAt p hp)).contDiffAt

lemma kernelTestField_re_contDiffAt (f : kernelSmoothTests) (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (fun p => (kernelTestField f p).re) p :=
  Complex.reCLM.contDiff.contDiffAt.comp p (kernelTestField_contDiffAt f p hp)

lemma kernelTestField_im_contDiffAt (f : kernelSmoothTests) (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (fun p => (kernelTestField f p).im) p :=
  Complex.imCLM.contDiff.contDiffAt.comp p (kernelTestField_contDiffAt f p hp)

lemma kernelTestField_invariant (f : kernelSmoothTests) (M : globalKubotaKernel) (p : EuclideanSpatial) :
    kernelTestField f (euclideanAction (integralComplexMatrix M) p)=kernelTestField f p := by
  simp only [kernelTestField,euclideanAction,euclideanToHyperbolic_coordinates,integralOrbitProjection_eq]

def kernelTestEnergyDensity (f : kernelSmoothTests) (w : HyperbolicSpace) : ℝ :=
  euclideanScalarDirichletDensity (fun p => (kernelTestField f p).re) (hyperbolicEuclideanCoordinates w)+
  euclideanScalarDirichletDensity (fun p => (kernelTestField f p).im) (hyperbolicEuclideanCoordinates w)

lemma kernelTestEnergyDensity_nonneg (f : kernelSmoothTests) (w : HyperbolicSpace) :
    0≤kernelTestEnergyDensity f w := by
  unfold kernelTestEnergyDensity euclideanScalarDirichletDensity
  positivity

lemma kernelTestEnergyDensity_invariant (f : kernelSmoothTests) (M : globalKubotaKernel) (w : HyperbolicSpace) :
    kernelTestEnergyDensity f (integralComplexMatrix M•w)=kernelTestEnergyDensity f w := by
  have he : hyperbolicEuclideanCoordinates (integralComplexMatrix M•w)=
      euclideanAction (integralComplexMatrix M) (hyperbolicEuclideanCoordinates w) := by
    simp only [euclideanAction,euclideanToHyperbolic_coordinates]
  have hp : 0<hyperbolicEuclideanCoordinates w 2 := hyperbolicHeight_pos w
  unfold kernelTestEnergyDensity
  rw [he]
  congr 1
  · apply euclideanScalarDirichletDensity_invariant _ _ _ hp
    · exact (kernelTestField_re_contDiffAt f _ (euclideanAction_positive _ _)).differentiableAt (by simp)
    · funext p
      exact congrArg Complex.re (kernelTestField_invariant f M p)
  · apply euclideanScalarDirichletDensity_invariant _ _ _ hp
    · exact (kernelTestField_im_contDiffAt f _ (euclideanAction_positive _ _)).differentiableAt (by simp)
    · funext p
      exact congrArg Complex.im (kernelTestField_invariant f M p)

def kernelQuotientEnergyDensity (f : kernelSmoothTests) : KernelQuotient→ℝ :=
  Quotient.lift (kernelTestEnergyDensity f) (by
    intro u v huv
    obtain ⟨M,hM⟩ := huv
    rw [←hM]
    exact (kernelTestEnergyDensity_invariant f M u).symm)

lemma kernelTestEnergyDensity_continuous (f : kernelSmoothTests) : Continuous (kernelTestEnergyDensity f) := by
  rw [continuous_iff_continuousAt]
  intro w
  have hp : 0<hyperbolicEuclideanCoordinates w 2 := hyperbolicHeight_pos w
  have hr := (kernelTestField_re_contDiffAt f _ hp).continuousAt_fderiv (by simp)
  have hi := (kernelTestField_im_contDiffAt f _ hp).continuousAt_fderiv (by simp)
  have ht : ContinuousAt (fun p : EuclideanSpatial => p 2) (hyperbolicEuclideanCoordinates w) := by fun_prop
  exact (((ht.pow 2).mul (hr.norm.pow 2)).add ((ht.pow 2).mul (hi.norm.pow 2))).comp
    hyperbolicEuclideanCoordinates_continuous.continuousAt

lemma kernelQuotientEnergyDensity_continuous (f : kernelSmoothTests) : Continuous (kernelQuotientEnergyDensity f) :=
  (kernelTestEnergyDensity_continuous f).quotient_lift _

lemma kernelQuotientEnergyDensity_nonneg (f : kernelSmoothTests) (q : KernelQuotient) :
    0≤kernelQuotientEnergyDensity f q := by
  induction q using Quotient.inductionOn with
  | _ w => exact kernelTestEnergyDensity_nonneg f w

lemma kernelQuotientEnergyDensity_support (f : kernelSmoothTests) :
    Function.support (kernelQuotientEnergyDensity f)⊆tsupport f.1 := by
  intro q hq
  by_contra hn
  have hz : f.1=ᶠ[𝓝 q]0 := notMem_tsupport_iff_eventuallyEq.mp hn
  induction q using Quotient.inductionOn with
  | _ w =>
    have hp : 0<hyperbolicEuclideanCoordinates w 2 := hyperbolicHeight_pos w
    have hc := (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp
      (euclideanToHyperbolic_contMDiffAt _ hp).continuousAt
    change Tendsto (integralOrbitProjection globalKubotaKernel ∘ euclideanToHyperbolic)
      (𝓝 (hyperbolicEuclideanCoordinates w))
      (𝓝 (integralOrbitProjection globalKubotaKernel (euclideanToHyperbolic (hyperbolicEuclideanCoordinates w)))) at hc
    rw [euclideanToHyperbolic_coordinates] at hc
    have hzF : kernelTestField f=ᶠ[𝓝 (hyperbolicEuclideanCoordinates w)]0 := hz.comp_tendsto hc
    have hzr : (fun p => (kernelTestField f p).re)=ᶠ[𝓝 (hyperbolicEuclideanCoordinates w)]0 := by
      filter_upwards [hzF] with p hp
      simp [hp]
    have hzi : (fun p => (kernelTestField f p).im)=ᶠ[𝓝 (hyperbolicEuclideanCoordinates w)]0 := by
      filter_upwards [hzF] with p hp
      simp [hp]
    apply hq
    change kernelTestEnergyDensity f w=0
    simp only [kernelTestEnergyDensity,euclideanScalarDirichletDensity,hzr.fderiv_eq,hzi.fderiv_eq,
      fderiv_zero,Pi.zero_apply,norm_zero,zero_pow (by decide : 2≠0),mul_zero,add_zero]

lemma kernelQuotientEnergyDensity_hasCompactSupport (f : kernelSmoothTests) :
    HasCompactSupport (kernelQuotientEnergyDensity f) :=
  HasCompactSupport.of_support_subset_isCompact f.2.2 (kernelQuotientEnergyDensity_support f)

lemma kernelQuotientEnergyDensity_integrable (f : kernelSmoothTests) :
    Integrable (kernelQuotientEnergyDensity f) (integralQuotientVolume globalKubotaKernel) :=
  (kernelQuotientEnergyDensity_continuous f).integrable_of_hasCompactSupport
    (kernelQuotientEnergyDensity_hasCompactSupport f)

def kernelDirichletEnergy (f : kernelSmoothTests) : ℝ :=
  ∫q,kernelQuotientEnergyDensity f q ∂integralQuotientVolume globalKubotaKernel

lemma kernelDirichletEnergy_nonneg (f : kernelSmoothTests) : 0≤kernelDirichletEnergy f :=
  integral_nonneg (kernelQuotientEnergyDensity_nonneg f)

end CubicEisenstein

end

end OAI
end OAIOriginalModule0199

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.CuspHeight
Source SHA256: f42e1fd406a61f5ec479d3e7889d42c1880093ac27b21bdd83297e5b3eafbb66
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0200


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
open scoped BigOperators Classical Topology ContDiff Manifold

lemma kernelCompact_smooth_cutoff (K : Set KernelQuotient) (hK : IsCompact K) :
    ∃χ : KernelQuotient→ℝ,ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ χ ∧
      HasCompactSupport χ ∧ (∀q∈K,χ=ᶠ[𝓝 q](fun _ => 1)) ∧ ∀q,χ q∈Set.Icc 0 1 := by
  obtain ⟨J,hJ,hKJ⟩ := exists_compact_superset hK
  obtain ⟨χ,hχone,hχzero,hχrange⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    𝓘(ℝ,SpatialCoordinates) hK.isClosed hKJ (n := (⊤ : ℕ∞))
  refine ⟨χ,χ.contMDiff,?_,?_,hχrange⟩
  · apply HasCompactSupport.of_support_subset_isCompact hJ
    intro q hq
    by_contra hn
    exact hq (hχzero q hn)
  · intro q hq
    exact hχone.filter_mono (nhds_le_nhdsSet hq)

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

lemma integral_upper_triangular_height_all (M : SL(2,ActualEisensteinCubic.O))
    (hc : M 1 0=0) (w : HyperbolicSpace) :
    hyperbolicHeight (integralComplexMatrix M • w)=hyperbolicHeight w := by
  obtain ⟨z,v,hv,rfl⟩ := upperPoint_surjective w
  rw [integral_upper_triangular_height M hc,hyperbolicHeight_upperPoint]

def fullMatrixHeight (M : SL(2,ActualEisensteinCubic.O)) (w : HyperbolicSpace) : ℝ :=
  hyperbolicHeight (integralComplexMatrix M • w)

def fullCuspHeightRelation : Setoid (SL(2,ActualEisensteinCubic.O)) := Setoid.ker fullMatrixHeight
abbrev FullCuspClasses := Quotient fullCuspHeightRelation

def fullCuspOf (M : SL(2,ActualEisensteinCubic.O)) : FullCuspClasses := Quotient.mk _ M

def fullCuspHeight : FullCuspClasses→HyperbolicSpace→ℝ :=
  Quotient.lift fullMatrixHeight (fun _ _ h => h)

lemma fullCuspHeight_of (M : SL(2,ActualEisensteinCubic.O)) (w : HyperbolicSpace) :
    fullCuspHeight (fullCuspOf M) w=fullMatrixHeight M w := rfl

lemma fullCuspHeight_continuous (x : FullCuspClasses) : Continuous (fullCuspHeight x) := by
  induction x using Quotient.inductionOn with
  | _ M => exact hyperbolicHeight_continuous.comp (continuous_hyperbolic_action (integralComplexMatrix M))

lemma fullMatrixHeight_eq_of_lower_zero (M N : SL(2,ActualEisensteinCubic.O))
    (h : (M*N⁻¹) 1 0=0) : fullMatrixHeight M=fullMatrixHeight N := by
  funext w
  have hh := integral_upper_triangular_height_all (M*N⁻¹) h (integralComplexMatrix N • w)
  simpa only [fullMatrixHeight,map_mul,map_inv,mul_smul,inv_smul_smul] using hh

lemma fullCuspOf_eq_iff (M N : SL(2,ActualEisensteinCubic.O)) :
    fullCuspOf M=fullCuspOf N ↔ (M*N⁻¹) 1 0=0 := by
  constructor
  · intro h
    by_contra hc
    have he : fullMatrixHeight M=fullMatrixHeight N := Quotient.exact h
    let w := upperPoint 0 2 (by norm_num : (0:ℝ)<2)
    have hh := congrFun he (integralComplexMatrix N⁻¹ • w)
    have hp := integral_hyperbolicHeight_mul_le_one (M*N⁻¹) hc w
    have hN : hyperbolicHeight w=2 := hyperbolicHeight_upperPoint _ _ _
    change hyperbolicHeight (integralComplexMatrix M • (integralComplexMatrix N⁻¹ • w))=
      hyperbolicHeight (integralComplexMatrix N • (integralComplexMatrix N⁻¹ • w)) at hh
    simp only [map_inv,smul_inv_smul] at hh
    simp only [map_mul,map_inv,mul_smul] at hp
    rw [hh,hN] at hp
    norm_num at hp
  · intro h
    exact Quotient.sound (fullMatrixHeight_eq_of_lower_zero M N h)

def fullCuspTranslate (M : SL(2,ActualEisensteinCubic.O)) : FullCuspClasses→FullCuspClasses :=
  Quotient.map (fun N => N*M) (by
    intro N P h
    change fullMatrixHeight (N*M)=fullMatrixHeight (P*M)
    funext w
    have hh := congrFun h (integralComplexMatrix M • w)
    simpa only [fullMatrixHeight,map_mul,mul_smul] using hh)

lemma fullCuspTranslate_mul (M N : SL(2,ActualEisensteinCubic.O)) (x : FullCuspClasses) :
    fullCuspTranslate N (fullCuspTranslate M x)=fullCuspTranslate (M*N) x := by
  induction x using Quotient.inductionOn with
  | _ P => change fullCuspOf ((P*M)*N)=fullCuspOf (P*(M*N)); rw [mul_assoc]

lemma fullCuspTranslate_one (x : FullCuspClasses) : fullCuspTranslate 1 x=x := by
  induction x using Quotient.inductionOn with
  | _ P => change fullCuspOf (P*1)=fullCuspOf P; rw [mul_one]

def fullCuspRightEquiv (M : SL(2,ActualEisensteinCubic.O)) : FullCuspClasses≃FullCuspClasses where
  toFun := fullCuspTranslate M
  invFun := fullCuspTranslate M⁻¹
  left_inv x := by rw [fullCuspTranslate_mul,mul_inv_cancel,fullCuspTranslate_one]
  right_inv x := by rw [fullCuspTranslate_mul,inv_mul_cancel,fullCuspTranslate_one]

lemma fullCuspHeight_translate (M : SL(2,ActualEisensteinCubic.O)) (x : FullCuspClasses)
    (w : HyperbolicSpace) :
    fullCuspHeight (fullCuspRightEquiv M x) w=fullCuspHeight x (integralComplexMatrix M • w) := by
  induction x using Quotient.inductionOn with
  | _ N => change fullMatrixHeight (N*M) w=fullMatrixHeight N (integralComplexMatrix M • w)
           simp only [fullMatrixHeight,map_mul,mul_smul]

lemma fullCuspHeight_high_unique (w : HyperbolicSpace) (x y : FullCuspClasses)
    (hx : 1<fullCuspHeight x w) (hy : 1<fullCuspHeight y w) : x=y := by
  induction x using Quotient.inductionOn with
  | _ M =>
    induction y using Quotient.inductionOn with
    | _ N =>
      apply (fullCuspOf_eq_iff M N).mpr
      by_contra hc
      have hp := integral_hyperbolicHeight_mul_le_one (M*N⁻¹) hc (integralComplexMatrix N • w)
      simp only [map_mul,map_inv,mul_smul,inv_smul_smul] at hp
      change 1<fullMatrixHeight M w at hx
      change 1<fullMatrixHeight N w at hy
      change fullMatrixHeight M w*fullMatrixHeight N w≤1 at hp
      nlinarith [mul_pos (sub_pos.mpr hx) (sub_pos.mpr hy)]

lemma fullCusp_profile_finite (F : ℝ→ℝ) (hF : ∀v≤1,F v=0) (w : HyperbolicSpace) :
    Function.HasFiniteSupport (fun x : FullCuspClasses => F (fullCuspHeight x w)) := by
  have hs : Set.Subsingleton {x : FullCuspClasses | 1<fullCuspHeight x w} :=
    fun x hx y hy => fullCuspHeight_high_unique w x y hx hy
  apply hs.finite.subset
  intro x hx
  by_contra hn
  exact hx (hF _ (le_of_not_gt hn))

def fullCuspProfileSum (F : ℝ→ℝ) (w : HyperbolicSpace) : ℝ :=
  ∑'x : FullCuspClasses,F (fullCuspHeight x w)

lemma fullCuspProfileSum_summable (F : ℝ→ℝ) (hF : ∀v≤1,F v=0) (w : HyperbolicSpace) :
    Summable (fun x : FullCuspClasses => F (fullCuspHeight x w)) :=
  summable_of_hasFiniteSupport (fullCusp_profile_finite F hF w)

lemma fullCuspProfileSum_invariant (F : ℝ→ℝ) (M : SL(2,ActualEisensteinCubic.O)) (w : HyperbolicSpace) :
    fullCuspProfileSum F (integralComplexMatrix M • w)=fullCuspProfileSum F w := by
  unfold fullCuspProfileSum
  simp only [←fullCuspHeight_translate M]
  exact (fullCuspRightEquiv M).tsum_eq (fun x : FullCuspClasses => F (fullCuspHeight x w))

lemma fullCuspProfileSum_eq_single (F : ℝ→ℝ) (hF : ∀v≤1,F v=0)
    (w : HyperbolicSpace) (x : FullCuspClasses) (hx : 1<fullCuspHeight x w) :
    fullCuspProfileSum F w=F (fullCuspHeight x w) := by
  apply tsum_eq_single x
  intro y hy
  apply hF
  by_contra hn
  exact hy (fullCuspHeight_high_unique w y x (lt_of_not_ge hn) hx)

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

def cuspBarrierProfile (a b v : ℝ) : ℝ := cuspTransition a b v*(v-1)

lemma cuspBarrierProfile_smooth (a b : ℝ) : ContDiff ℝ ∞ (cuspBarrierProfile a b) :=
  (cuspTransition_contDiff a b).mul (contDiff_id.sub contDiff_const)

lemma cuspBarrierProfile_zero (a b : ℝ) (hab : a<b) (v : ℝ) (hv : v≤a) :
    cuspBarrierProfile a b v=0 := by
  rw [cuspBarrierProfile,cuspTransition_zero a b v hab hv,zero_mul]

lemma cuspBarrierProfile_nonneg (a b : ℝ) (ha : 1≤a) (hab : a<b) (v : ℝ) :
    0≤cuspBarrierProfile a b v := by
  by_cases hv : v≤a
  · rw [cuspBarrierProfile_zero a b hab v hv]
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (sub_nonneg.mpr (ha.trans (le_of_not_ge hv)))

def cuspBarrier (a b : ℝ) (w : HyperbolicSpace) : ℝ :=
  1+fullCuspProfileSum (cuspBarrierProfile a b) w

lemma cuspBarrier_summable (a b : ℝ) (ha : 1≤a) (hab : a<b) (w : HyperbolicSpace) :
    Summable (fun x : FullCuspClasses => cuspBarrierProfile a b (fullCuspHeight x w)) :=
  fullCuspProfileSum_summable _ (fun v hv => cuspBarrierProfile_zero a b hab v (hv.trans ha)) w

lemma cuspBarrier_one_le (a b : ℝ) (ha : 1≤a) (hab : a<b) (w : HyperbolicSpace) :
    1≤cuspBarrier a b w := by
  exact le_add_of_nonneg_right (tsum_nonneg (fun x => cuspBarrierProfile_nonneg a b ha hab _))

lemma cuspBarrier_invariant (a b : ℝ) (M : SL(2,ActualEisensteinCubic.O)) (w : HyperbolicSpace) :
    cuspBarrier a b (integralComplexMatrix M • w)=cuspBarrier a b w := by
  rw [cuspBarrier,cuspBarrier,fullCuspProfileSum_invariant]

theorem cuspBarrier_high (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (M : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (v : ℝ) (hv : 0<v) (hbv : b<v) :
    cuspBarrier a b (integralComplexMatrix M • upperPoint z v hv)=v := by
  rw [cuspBarrier_invariant]
  have hx : fullCuspHeight (fullCuspOf 1) (upperPoint z v hv)=v := by
    simp only [fullCuspHeight_of,fullMatrixHeight,map_one,one_smul,hyperbolicHeight_upperPoint]
  rw [cuspBarrier,fullCuspProfileSum_eq_single _
    (fun y hy => cuspBarrierProfile_zero a b hab y (hy.trans ha)) _ (fullCuspOf 1)
      (by rw [hx]; linarith),hx,cuspBarrierProfile,cuspTransition_one a b v hab hbv.le,one_mul]
  ring

def kernelQuotientBarrier (a b : ℝ) : KernelQuotient→ℝ :=
  Quotient.lift (cuspBarrier a b) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    exact (cuspBarrier_invariant a b (M:SL(2,ActualEisensteinCubic.O)) w).symm)

lemma kernelQuotientBarrier_one_le (a b : ℝ) (ha : 1≤a) (hab : a<b) (q : KernelQuotient) :
    1≤kernelQuotientBarrier a b q := by
  induction q using Quotient.inductionOn with
  | _ w => exact cuspBarrier_one_le a b ha hab w

lemma kernelQuotientBarrier_fordCusp (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (M : SL(2,ActualEisensteinCubic.O)) (p : UpperCoordinates) (hp : b<p.1.2) :
    kernelQuotientBarrier a b (fordOrbitChart globalKubotaKernel M p)=p.1.2 :=
  cuspBarrier_high a b ha hab M⁻¹ p.1.1 p.1.2 p.2 hp

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups ContDiff

lemma principal_high_locally_finite (w : HyperbolicSpace) :
    ∃U : Set HyperbolicSpace,IsOpen U ∧ w∈U ∧ ∃T : Finset CuspCosets,
      ∀z∈U,∀x∉T,cosetHeight x z<1 := by
  obtain ⟨U,hU,hw,T,hT⟩ := locally_finite_high_rows (hyperbolicSpatialCoordinates w)
    (hyperbolicSpatialCoordinates_positive w)
  refine ⟨hyperbolicSpatialCoordinates ⁻¹' U,hU.preimage hyperbolicSpatialCoordinates_continuous,
    hw,T,?_⟩
  intro z hz x hx
  have hh := (hT _ hz).2 x hx
  rw [←cosetHeight_upperPoint_rowHeight x _ (hyperbolicSpatialCoordinates_positive z),
    hyperbolicSpatialCoordinates_reconstruct] at hh
  exact hh

def fullCuspFromPrincipal (r : SL(2,ActualEisensteinCubic.O)) : CuspCosets→FullCuspClasses :=
  Quotient.lift (fun N : CubicKubota.levelThree => fullCuspOf ((N:SL(2,ActualEisensteinCubic.O))*r⁻¹)) (by
    intro N P h
    apply Quotient.sound
    funext w
    have he : cosetOf N=cosetOf P := Quotient.sound h
    have hh := congrArg (fun x => cosetHeight x (integralComplexMatrix r⁻¹ • w)) he
    simpa only [cosetHeight_cosetOf,fullMatrixHeight,map_mul,mul_smul,integralComplexMatrix_levelThree] using hh)

lemma fullCuspFromPrincipal_height (r : SL(2,ActualEisensteinCubic.O)) (x : CuspCosets)
    (w : HyperbolicSpace) :
    fullCuspHeight (fullCuspFromPrincipal r x) w=cosetHeight x (integralComplexMatrix r⁻¹ • w) := by
  induction x using Quotient.inductionOn with
  | _ N =>
    change fullMatrixHeight ((N:SL(2,ActualEisensteinCubic.O))*r⁻¹) w=cosetHeight (cosetOf N) _
    simp only [fullMatrixHeight,cosetHeight_cosetOf,map_mul,mul_smul,integralComplexMatrix_levelThree]

lemma fullCusp_finite_principal_cover :
    ∃S : Finset (SL(2,ActualEisensteinCubic.O)),∀x : FullCuspClasses,
      ∃r∈S,∃y : CuspCosets,fullCuspFromPrincipal r y=x := by
  let : CubicKubota.levelThree.FiniteIndex := levelThree_finiteIndex
  obtain ⟨S,hS⟩ := finite_right_representatives CubicKubota.levelThree
  refine ⟨S,fun x => ?_⟩
  induction x using Quotient.inductionOn with
  | _ M =>
    obtain ⟨r,hr,hM⟩ := hS M⁻¹
    have hm : M*r∈CubicKubota.levelThree := by
      simpa only [mul_inv_rev,inv_inv] using CubicKubota.levelThree.inv_mem hM
    refine ⟨r,hr,cosetOf ⟨M*r,hm⟩,?_⟩
    change fullCuspOf ((M*r)*r⁻¹)=fullCuspOf M
    rw [mul_inv_cancel_right]

lemma full_high_locally_finite (w : HyperbolicSpace) :
    ∃U : Set HyperbolicSpace,IsOpen U ∧ w∈U ∧ ∃T : Finset FullCuspClasses,
      ∀z∈U,∀x∉T,fullCuspHeight x z<1 := by
  obtain ⟨S,hS⟩ := fullCusp_finite_principal_cover
  choose U hU hw T hT using fun r : S => principal_high_locally_finite (integralComplexMatrix r.1⁻¹ • w)
  let V : Set HyperbolicSpace := ⋂r : S,(fun z => integralComplexMatrix r.1⁻¹ • z) ⁻¹' U r
  let B : Finset FullCuspClasses := Finset.univ.biUnion (fun r : S => (T r).image (fullCuspFromPrincipal r.1))
  refine ⟨V,isOpen_iInter_of_finite (fun r => (hU r).preimage (continuous_hyperbolic_action _)),?_,B,?_⟩
  · exact Set.mem_iInter.mpr hw
  · intro z hz x hx
    obtain ⟨r,hr,y,hxy⟩ := hS x
    let i : S := ⟨r,hr⟩
    have hy : y∉T i := by
      intro hy
      apply hx
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨y,hy,hxy⟩⟩
    rw [←hxy,fullCuspFromPrincipal_height]
    exact hT i _ (Set.mem_iInter.mp hz i) y hy

lemma fullCuspProfileSum_locally_finite (F : ℝ→ℝ) (hF : ∀v≤1,F v=0) (w : HyperbolicSpace) :
    ∃T : Finset FullCuspClasses,fullCuspProfileSum F =ᶠ[𝓝 w]
      (fun z => ∑x∈T,F (fullCuspHeight x z)) := by
  obtain ⟨U,hU,hw,T,hT⟩ := full_high_locally_finite w
  refine ⟨T,?_⟩
  filter_upwards [hU.mem_nhds hw] with z hz
  apply tsum_eq_sum
  intro x hx
  exact hF _ (hT z hz x hx).le

lemma fullCuspProfileSum_continuous (F : ℝ→ℝ) (hF : ∀v≤1,F v=0) (hFc : Continuous F) :
    Continuous (fullCuspProfileSum F) := by
  rw [continuous_iff_continuousAt]
  intro w
  obtain ⟨T,hT⟩ := fullCuspProfileSum_locally_finite F hF w
  apply ContinuousAt.congr _ hT.symm
  exact (continuous_finsetSum T (fun x hx => hFc.comp (fullCuspHeight_continuous x))).continuousAt

lemma cuspBarrier_continuous (a b : ℝ) (ha : 1≤a) (hab : a<b) :
    Continuous (cuspBarrier a b) :=
  continuous_const.add (fullCuspProfileSum_continuous _
    (fun v hv => cuspBarrierProfile_zero a b hab v (hv.trans ha)) (cuspBarrierProfile_smooth a b).continuous)

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold MatrixGroups

lemma fullCuspHeight_chart_contDiffAt (x : FullCuspClasses) (p : SpatialCoordinates)
    (hp : p∈hyperbolicSpatialChart.target) :
    ContDiffAt ℝ ∞ (fun q => fullCuspHeight x (hyperbolicSpatialChart.symm q)) p := by
  induction x using Quotient.inductionOn with
  | _ M =>
    have hh : ContDiffAt ℝ ∞ (fun q => mobiusSpatial (integralComplexMatrix M) q 2) p :=
      (contDiff_apply ℝ ℝ 2).contDiffAt.comp p
        (mobiusSpatial_contDiffAt _ p (hyperbolicSpatialChart_target_positive hp))
    apply hh.congr_of_eventuallyEq
    filter_upwards [hyperbolicSpatialChart.open_target.mem_nhds hp] with q hq
    rw [hyperbolicSpatialChart_symm_eq hq]
    exact congrArg (fun r : SpatialCoordinates => r 2)
      (mobiusSpatial_coordinates (integralComplexMatrix M) q
        (hyperbolicSpatialChart_target_positive hq))

lemma fullCuspProfileSum_chart_contDiffAt (F : ℝ→ℝ) (hF : ∀v≤1,F v=0)
    (hFc : ContDiff ℝ ∞ F) (p : SpatialCoordinates) (hp : p∈hyperbolicSpatialChart.target) :
    ContDiffAt ℝ ∞ (fun q => fullCuspProfileSum F (hyperbolicSpatialChart.symm q)) p := by
  obtain ⟨T,hT⟩ := fullCuspProfileSum_locally_finite F hF (hyperbolicSpatialChart.symm p)
  have hc := hyperbolicSpatialChart.continuousAt_symm hp
  have he := hT.comp_tendsto hc
  apply ContDiffAt.congr_of_eventuallyEq _ he
  exact ContDiffAt.sum (fun x hx => hFc.contDiffAt.comp p
    (fullCuspHeight_chart_contDiffAt x p hp))

lemma cuspBarrier_chart_contDiffAt (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (p : SpatialCoordinates) (hp : p∈hyperbolicSpatialChart.target) :
    ContDiffAt ℝ ∞ (fun q => cuspBarrier a b (hyperbolicSpatialChart.symm q)) p :=
  contDiffAt_const.add (fullCuspProfileSum_chart_contDiffAt _
    (fun v hv => cuspBarrierProfile_zero a b hab v (hv.trans ha))
    (cuspBarrierProfile_smooth a b) p hp)

lemma kernelQuotientBarrier_continuous (a b : ℝ) (ha : 1≤a) (hab : a<b) :
    Continuous (kernelQuotientBarrier a b) :=
  (cuspBarrier_continuous a b ha hab).quotient_lift _

lemma kernelQuotientBarrier_contMDiff (a b : ℝ) (ha : 1≤a) (hab : a<b) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ (kernelQuotientBarrier a b) := by
  intro q
  rw [contMDiffAt_iff]
  refine ⟨(kernelQuotientBarrier_continuous a b ha hab).continuousAt,?_⟩
  have hq : q∈(kernelQuotientChart q).source := mem_chart_source SpatialCoordinates q
  have hp : kernelQuotientChart q q∈hyperbolicSpatialChart.target :=
    ((kernelQuotientChart q).map_source hq).1
  have hh := cuspBarrier_chart_contDiffAt a b ha hab _ hp
  have he : (fun p => kernelQuotientBarrier a b ((kernelQuotientChart q).symm p))=
      (fun p => cuspBarrier a b (hyperbolicSpatialChart.symm p)) := by
    funext p
    rw [kernelQuotientChart_symm]
    rfl
  have hh' := (he.symm ▸ hh).contDiffWithinAt (s := Set.univ)
  simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Function.id_comp,Function.comp_id,Set.range_id,
    chartAt_self_eq,kernelSpatial_chartAt,OpenPartialHomeomorph.refl_apply,Function.comp_def,id_eq] using hh'

lemma cuspBarrier_euclidean_contDiffAt (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (fun q => cuspBarrier a b (euclideanToHyperbolic q)) p :=
  (((kernelQuotientBarrier_contMDiff a b ha hab).comp kernelProjection_contMDiff)
    (euclideanToHyperbolic p) |>.comp p (euclideanToHyperbolic_contMDiffAt p hp)).contDiffAt

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

def positiveHeightLaplacian (F : ℝ→ℝ) (v : ℝ) : ℝ :=
  v*deriv F v-v^2*deriv (deriv F) v

def cuspBarrierDefectProfile (a b v : ℝ) : ℝ :=
  positiveHeightLaplacian (cuspBarrierProfile a b) v-cuspBarrierProfile a b v

lemma positiveHeightLaplacian_smooth (F : ℝ→ℝ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (positiveHeightLaplacian F) := by
  have hD : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.mp hF).2
  exact (contDiff_id.mul hD).sub ((contDiff_id.pow 2).mul ((contDiff_infty_iff_deriv.mp hD).2))

lemma cuspBarrierDefectProfile_smooth (a b : ℝ) :
    ContDiff ℝ ∞ (cuspBarrierDefectProfile a b) :=
  (positiveHeightLaplacian_smooth _ (cuspBarrierProfile_smooth a b)).sub
    (cuspBarrierProfile_smooth a b)

lemma cuspBarrierDefectProfile_zero (a b v : ℝ) (hab : a<b) (hv : v<a) :
    cuspBarrierDefectProfile a b v=0 := by
  have he : cuspBarrierProfile a b =ᶠ[𝓝 v] (fun _ => (0:ℝ)) := by
    filter_upwards [Iio_mem_nhds hv] with x hx
    exact cuspBarrierProfile_zero a b hab x hx.le
  have hd := he.deriv_eq
  have hdd : deriv (deriv (cuspBarrierProfile a b)) v=0 := by
    simpa only [show deriv (fun _ : ℝ => (0:ℝ))=(fun _ => 0) from funext (fun x => deriv_const x 0),deriv_const] using he.deriv.deriv_eq
  simp only [deriv_const] at hd
  simp only [cuspBarrierDefectProfile,positiveHeightLaplacian,he.eq_of_nhds,hd,hdd,mul_zero,sub_zero]

lemma cuspBarrierDefectProfile_one (a b v : ℝ) (hab : a<b) (hv : b<v) :
    cuspBarrierDefectProfile a b v=1 := by
  have he : cuspBarrierProfile a b =ᶠ[𝓝 v] (fun x => x-1) := by
    filter_upwards [Ioi_mem_nhds hv] with x hx
    rw [cuspBarrierProfile,cuspTransition_one a b x hab hx.le,one_mul]
  have hd := he.deriv_eq
  have hlin : deriv (fun x : ℝ => x-1)=(fun _ => 1) := by ext x; simp
  have hdd : deriv (deriv (cuspBarrierProfile a b)) v=0 := by
    simpa only [hlin,deriv_const] using he.deriv.deriv_eq
  simp only [deriv_sub_const,deriv_id''] at hd
  simp only [cuspBarrierDefectProfile,positiveHeightLaplacian,he.eq_of_nhds,hd,hdd]
  ring

def cuspBarrierDefect (a b : ℝ) (w : HyperbolicSpace) : ℝ :=
  -1+fullCuspProfileSum (cuspBarrierDefectProfile a b) w

lemma cuspBarrierDefect_invariant (a b : ℝ) (M : SL(2,ActualEisensteinCubic.O))
    (w : HyperbolicSpace) :
    cuspBarrierDefect a b (integralComplexMatrix M • w)=cuspBarrierDefect a b w := by
  rw [cuspBarrierDefect,cuspBarrierDefect,fullCuspProfileSum_invariant]

lemma cuspBarrierDefect_high (a b : ℝ) (ha : 1<a) (hab : a<b)
    (M : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (v : ℝ) (hv : 0<v) (hbv : b<v) :
    cuspBarrierDefect a b (integralComplexMatrix M • upperPoint z v hv)=0 := by
  rw [cuspBarrierDefect_invariant]
  have hx : fullCuspHeight (fullCuspOf 1) (upperPoint z v hv)=v := by
    simp only [fullCuspHeight_of,fullMatrixHeight,map_one,one_smul,hyperbolicHeight_upperPoint]
  rw [cuspBarrierDefect,fullCuspProfileSum_eq_single _
    (fun y hy => cuspBarrierDefectProfile_zero a b y hab (hy.trans_lt ha)) _ (fullCuspOf 1)
      (by rw [hx]; linarith),hx,cuspBarrierDefectProfile_one a b v hab hbv]
  ring

def kernelQuotientBarrierDefect (a b : ℝ) : KernelQuotient→ℝ :=
  Quotient.lift (cuspBarrierDefect a b) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    exact (cuspBarrierDefect_invariant a b (M:SL(2,ActualEisensteinCubic.O)) w).symm)

lemma kernelQuotientBarrierDefect_hasCompactSupport (a b : ℝ) (ha : 1<a) (hab : a<b) :
    HasCompactSupport (kernelQuotientBarrierDefect a b) := by
  obtain ⟨S,hS⟩ := globalKubotaKernel_compact_core_cusp_cover
  obtain ⟨hcompact,hcover⟩ := hS b
  apply HasCompactSupport.of_support_subset_isCompact hcompact
  intro q hq
  have hmem : q∈compactFordCore globalKubotaKernel S b ∪
      ⋃r∈S,fordCuspTail globalKubotaKernel r b := by rw [←hcover]; trivial
  rcases hmem with hcore | htail
  · exact hcore
  · exfalso
    obtain ⟨r,hr⟩ := Set.mem_iUnion.mp htail
    obtain ⟨hrS,htail⟩ := Set.mem_iUnion.mp hr
    obtain ⟨p,hp,rfl⟩ := htail
    exact hq (cuspBarrierDefect_high a b ha hab r⁻¹ p.1.1 p.1.2 p.2 hp.2.2)

lemma kernelQuotientBarrierDefect_continuous (a b : ℝ) (ha : 1<a) (hab : a<b) :
    Continuous (kernelQuotientBarrierDefect a b) := by
  apply Continuous.quotient_lift
  exact continuous_const.add (fullCuspProfileSum_continuous _
    (fun v hv => cuspBarrierDefectProfile_zero a b v hab (hv.trans_lt ha))
    (cuspBarrierDefectProfile_smooth a b).continuous)

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

def fullCuspRow (x : FullCuspClasses) : Fin 2→ℂ :=
  complexBottomRow (integralComplexMatrix x.out)

lemma fullCuspRow_ne_zero (x : FullCuspClasses) : fullCuspRow x≠0 :=
  complexBottomRow_ne_zero _

lemma fullCuspRow_height (x : FullCuspClasses) (p : SpatialCoordinates) (hp : 0<p 2) :
    rowHeight (fullCuspRow x) p=fullCuspHeight x (upperPoint (spatialHorizontal p) (p 2) hp) := by
  have hx : fullCuspOf x.out=x := Quotient.out_eq x
  conv_rhs => rw [←hx]
  rw [fullCuspHeight_of,fullMatrixHeight,hyperbolicHeight_action_upperPoint]
  rw [rowHeight_eq_transformedHeight]
  simp only [transformedHeight,heightDenominator,fullCuspRow,complexBottomRow,spatialHorizontal]

def fullCuspProfileField (F : ℝ→ℝ) (p : SpatialCoordinates) : ℝ :=
  ∑'x : FullCuspClasses,F (rowHeight (fullCuspRow x) p)

lemma fullCuspProfileField_eq (F : ℝ→ℝ) (p : SpatialCoordinates) (hp : 0<p 2) :
    fullCuspProfileField F p=fullCuspProfileSum F (upperPoint (spatialHorizontal p) (p 2) hp) := by
  simp only [fullCuspProfileField,fullCuspProfileSum,fullCuspRow_height _ p hp]

lemma fullCuspRows_locally_finite (p : SpatialCoordinates) (hp : 0<p 2) :
    ∃T : Finset FullCuspClasses,∀ᶠq in 𝓝 p,∀x∉T,rowHeight (fullCuspRow x) q<1 := by
  let w := upperPoint (spatialHorizontal p) (p 2) hp
  obtain ⟨U,hU,hw,T,hT⟩ := full_high_locally_finite w
  have ht : p∈hyperbolicSpatialChart.target := by
    have he : hyperbolicSpatialChart w=p := by
      simp only [w,hyperbolicSpatialChart_apply,hyperbolicSpatialCoordinates,spatialHorizontal,
        hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint]
      ext j
      fin_cases j <;> simp
    rw [←he]
    exact hyperbolicSpatialChart.map_source (Set.mem_univ _)
  have he : hyperbolicSpatialChart.symm p=w := by
    rw [hyperbolicSpatialChart_symm_eq ht]
  have hnear := (hyperbolicSpatialChart.continuousAt_symm ht) (by simpa only [he] using hU.mem_nhds hw)
  refine ⟨T,?_⟩
  filter_upwards [hnear,hyperbolicSpatialChart.open_target.mem_nhds ht] with q hq hqt
  have hpos := hyperbolicSpatialChart_target_positive hqt
  intro x hx
  rw [fullCuspRow_height x q hpos,←hyperbolicSpatialChart_symm_eq hqt]
  exact hT _ hq x hx

lemma fullCuspProfileField_locally_finite (F : ℝ→ℝ) (hF : ∀v≤1,F v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ∃T : Finset FullCuspClasses,fullCuspProfileField F =ᶠ[𝓝 p]
      (fun q => ∑x∈T,F (rowHeight (fullCuspRow x) q)) := by
  obtain ⟨T,hT⟩ := fullCuspRows_locally_finite p hp
  refine ⟨T,?_⟩
  filter_upwards [hT] with q hq
  apply tsum_eq_sum
  intro x hx
  exact hF _ (hq x hx).le

lemma cast_profile_deriv (F : ℝ→ℝ) (hF : Differentiable ℝ F) (v : ℝ) :
    deriv (fun y => (F y:ℂ)) v=((deriv F v:ℝ):ℂ) :=
  (hF v).hasDerivAt.ofReal_comp.deriv

lemma cast_profile_deriv2 (F : ℝ→ℝ) (hF : ContDiff ℝ ∞ F) (v : ℝ) :
    deriv (deriv (fun y => (F y:ℂ))) v=((deriv (deriv F) v:ℝ):ℂ) := by
  have he : deriv (fun y => (F y:ℂ))=(fun y => ((deriv F y:ℝ):ℂ)) :=
    funext (cast_profile_deriv F (hF.differentiable (by simp)))
  rw [he]
  exact cast_profile_deriv (deriv F) (((contDiff_infty_iff_deriv.mp hF).2).differentiable (by simp)) v

lemma fullCuspProfile_row_laplacian (F : ℝ→ℝ) (hF : ContDiff ℝ ∞ F)
    (x : FullCuspClasses) (p : SpatialCoordinates) (hp : 0<p 2) :
    -axisLaplacian (fun q => (F (rowHeight (fullCuspRow x) q):ℂ)) p=
      (positiveHeightLaplacian F (rowHeight (fullCuspRow x) p):ℂ) := by
  rw [rowProfile_laplacian (fun y => (F y:ℂ)) (fun v hv => Complex.ofRealCLM.contDiff.contDiffAt.comp v hF.contDiffAt)
    _ (fullCuspRow_ne_zero x) p hp,cast_profile_deriv F (hF.differentiable (by simp)),cast_profile_deriv2 F hF]
  simp only [positiveHeightLaplacian,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_pow]
  ring

lemma fullCuspProfileField_laplacian (F : ℝ→ℝ) (hF : ContDiff ℝ ∞ F)
    (hzero : ∀v≤1,F v=0) (hLzero : ∀v≤1,positiveHeightLaplacian F v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    -axisLaplacian (fun q => (fullCuspProfileField F q:ℂ)) p=
      (fullCuspProfileField (positiveHeightLaplacian F) p:ℂ) := by
  obtain ⟨T,hT⟩ := fullCuspRows_locally_finite p hp
  have he : (fun q => (fullCuspProfileField F q:ℂ)) =ᶠ[𝓝 p]
      (fun q => ∑x∈T,(F (rowHeight (fullCuspRow x) q):ℂ)) := by
    filter_upwards [hT] with q hq
    have hh : fullCuspProfileField F q=∑x∈T,F (rowHeight (fullCuspRow x) q) :=
      tsum_eq_sum (fun x hx => hzero _ (hq x hx).le)
    rw [hh]
    push_cast
    rfl
  have hval : fullCuspProfileField (positiveHeightLaplacian F) p=
      ∑x∈T,positiveHeightLaplacian F (rowHeight (fullCuspRow x) p) :=
    tsum_eq_sum (fun x hx => hLzero _ (hT.self_of_nhds x hx).le)
  have hreg : ∀x∈T,∀q,0<q 2→∀j : Fin 3,
      DifferentiableAt ℝ (axisSlice (fun z => (F (rowHeight (fullCuspRow x) z):ℂ)) q j) (q j) ∧
      DifferentiableAt ℝ (deriv (axisSlice (fun z => (F (rowHeight (fullCuspRow x) z):ℂ)) q j)) (q j) := by
    intro x hx q hq j
    have hd := rowProfile_axis_derivatives (fun v => (F v:ℂ))
      (fun v hv => Complex.ofRealCLM.contDiff.contDiffAt.comp v hF.contDiffAt)
      (fullCuspRow x) (fullCuspRow_ne_zero x) q hq j
    exact ⟨hd.1.differentiableAt,hd.2.differentiableAt⟩
  rw [axisLaplacian_congr_eventuallyEq _ _ p he,axisLaplacian_finset_sum T _ hreg p hp,hval]
  rw [←Finset.sum_neg_distrib]
  push_cast
  exact Finset.sum_congr rfl (fun x hx => fullCuspProfile_row_laplacian F hF x p hp)

end CubicEisenstein

end

end OAI
end OAIOriginalModule0200

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.DirichletForm
Source SHA256: 7e2badae293ad8ba491822b8b14b5188868428f210606e2752553e40fe6761c0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0201


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

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups

namespace CubicEisenstein

def kernelTestPartial (f : kernelSmoothTests) (w : HyperbolicSpace) (j : Fin 3) : ℂ :=
  fderiv ℝ (kernelTestField f) (hyperbolicEuclideanCoordinates w) (EuclideanSpace.basisFun (Fin 3) ℝ j)

lemma kernelTestPartial_add (f g : kernelSmoothTests) (w : HyperbolicSpace) (j : Fin 3) :
    kernelTestPartial (f+g) w j=kernelTestPartial f w j+kernelTestPartial g w j := by
  unfold kernelTestPartial
  have he : kernelTestField (f+g)=kernelTestField f+kernelTestField g := rfl
  rw [he,fderiv_add ((kernelTestField_contDiffAt f _ (hyperbolicHeight_pos w)).differentiableAt (by simp))
    ((kernelTestField_contDiffAt g _ (hyperbolicHeight_pos w)).differentiableAt (by simp))]
  rfl

lemma kernelTestPartial_sub (f g : kernelSmoothTests) (w : HyperbolicSpace) (j : Fin 3) :
    kernelTestPartial (f-g) w j=kernelTestPartial f w j-kernelTestPartial g w j := by
  unfold kernelTestPartial
  have he : kernelTestField (f-g)=kernelTestField f-kernelTestField g := rfl
  rw [he,fderiv_sub ((kernelTestField_contDiffAt f _ (hyperbolicHeight_pos w)).differentiableAt (by simp))
    ((kernelTestField_contDiffAt g _ (hyperbolicHeight_pos w)).differentiableAt (by simp))]
  rfl

lemma kernelTestPartial_smul (c : ℂ) (f : kernelSmoothTests) (w : HyperbolicSpace) (j : Fin 3) :
    kernelTestPartial (c•f) w j=c*kernelTestPartial f w j := by
  unfold kernelTestPartial
  have he : kernelTestField (c•f)=c•kernelTestField f := rfl
  rw [he,fderiv_const_smul ((kernelTestField_contDiffAt f _ (hyperbolicHeight_pos w)).differentiableAt (by simp))]
  rfl

lemma kernelTestEnergyDensity_eq_partials (f : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelTestEnergyDensity f w=(hyperbolicHeight w)^2*∑j:Fin 3,‖kernelTestPartial f w j‖^2 := by
  have hd := ((kernelTestField_contDiffAt f (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)).differentiableAt (by simp)).hasFDerivAt
  have hr := (Complex.reCLM.hasFDerivAt.comp (hyperbolicEuclideanCoordinates w) hd).fderiv
  have hi := (Complex.imCLM.hasFDerivAt.comp (hyperbolicEuclideanCoordinates w) hd).fderiv
  change fderiv ℝ (fun p => (kernelTestField f p).re) (hyperbolicEuclideanCoordinates w)=_ at hr
  change fderiv ℝ (fun p => (kernelTestField f p).im) (hyperbolicEuclideanCoordinates w)=_ at hi
  unfold kernelTestEnergyDensity euclideanScalarDirichletDensity
  rw [hr,hi,(EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual,
    (EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual,←mul_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  change (kernelTestPartial f w j).re^2+(kernelTestPartial f w j).im^2=‖kernelTestPartial f w j‖^2
  simpa only [Complex.normSq_apply,pow_two] using Complex.normSq_eq_norm_sq (kernelTestPartial f w j)

lemma kernelTestEnergyDensity_smul (c : ℂ) (f : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelTestEnergyDensity (c•f) w=‖c‖^2*kernelTestEnergyDensity f w := by
  simp only [kernelTestEnergyDensity_eq_partials,kernelTestPartial_smul,norm_mul,mul_pow,←Finset.mul_sum]
  ring

lemma kernelTestEnergyDensity_parallelogram (f g : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelTestEnergyDensity (f+g) w+kernelTestEnergyDensity (f-g) w=
      2*(kernelTestEnergyDensity f w+kernelTestEnergyDensity g w) := by
  simp only [kernelTestEnergyDensity_eq_partials,kernelTestPartial_add,kernelTestPartial_sub]
  rw [←mul_add,←Finset.sum_add_distrib]
  simp only [parallelogram_law_with_norm ℂ,←Finset.mul_sum,Finset.sum_add_distrib]
  ring

lemma kernelQuotientEnergyDensity_smul (c : ℂ) (f : kernelSmoothTests) (q : KernelQuotient) :
    kernelQuotientEnergyDensity (c•f) q=‖c‖^2*kernelQuotientEnergyDensity f q := by
  induction q using Quotient.inductionOn with
  | _ w => exact kernelTestEnergyDensity_smul c f w

lemma kernelQuotientEnergyDensity_parallelogram (f g : kernelSmoothTests) (q : KernelQuotient) :
    kernelQuotientEnergyDensity (f+g) q+kernelQuotientEnergyDensity (f-g) q=
      2*(kernelQuotientEnergyDensity f q+kernelQuotientEnergyDensity g q) := by
  induction q using Quotient.inductionOn with
  | _ w => exact kernelTestEnergyDensity_parallelogram f g w

lemma kernelDirichletEnergy_smul (c : ℂ) (f : kernelSmoothTests) :
    kernelDirichletEnergy (c•f)=‖c‖^2*kernelDirichletEnergy f := by
  unfold kernelDirichletEnergy
  simp_rw [kernelQuotientEnergyDensity_smul]
  exact integral_const_mul _ _

lemma kernelDirichletEnergy_parallelogram (f g : kernelSmoothTests) :
    kernelDirichletEnergy (f+g)+kernelDirichletEnergy (f-g)=
      2*(kernelDirichletEnergy f+kernelDirichletEnergy g) := by
  unfold kernelDirichletEnergy
  rw [←integral_add (kernelQuotientEnergyDensity_integrable _) (kernelQuotientEnergyDensity_integrable _)]
  simp_rw [kernelQuotientEnergyDensity_parallelogram]
  rw [integral_const_mul,integral_add (kernelQuotientEnergyDensity_integrable _) (kernelQuotientEnergyDensity_integrable _)]

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups InnerProductSpace

def kernelGradientAt (w : HyperbolicSpace) : kernelSmoothTests→ₗ[ℂ]EuclideanSpace ℂ (Fin 3) where
  toFun f := WithLp.toLp 2 (fun j => (hyperbolicHeight w:ℂ)*kernelTestPartial f w j)
  map_add' f g := by
    apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
    funext j
    simp [kernelTestPartial_add,mul_add]
  map_smul' c f := by
    apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
    funext j
    simp [kernelTestPartial_smul,smul_eq_mul,mul_left_comm]

lemma kernelGradientAt_norm_sq (w : HyperbolicSpace) (f : kernelSmoothTests) :
    ‖kernelGradientAt w f‖^2=kernelTestEnergyDensity f w := by
  rw [PiLp.norm_sq_eq_of_L2,kernelTestEnergyDensity_eq_partials]
  change (∑j:Fin 3,‖(hyperbolicHeight w:ℂ)*kernelTestPartial f w j‖^2)=_
  simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_of_nonneg (hyperbolicHeight_pos w).le,
    Finset.mul_sum]

def kernelDirichletPairDensity (f g : kernelSmoothTests) (q : KernelQuotient) : ℂ :=
  ((kernelQuotientEnergyDensity (f+g) q:ℂ)-(kernelQuotientEnergyDensity (f-g) q:ℂ)+
    ((kernelQuotientEnergyDensity (f-Complex.I•g) q:ℂ)-
      (kernelQuotientEnergyDensity (f+Complex.I•g) q:ℂ))*Complex.I)/4

lemma kernelDirichletPairDensity_coordinate (f g : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelDirichletPairDensity f g (integralOrbitProjection globalKubotaKernel w)=
      inner ℂ (kernelGradientAt w f) (kernelGradientAt w g) := by
  rw [inner_eq_sum_norm_sq_div_four]
  simp only [←map_add,←map_sub,←map_smul,RCLike.ofReal_eq_complex_ofReal,←Complex.ofReal_pow,kernelGradientAt_norm_sq]
  rfl

lemma kernelDirichletPairDensity_integrable (f g : kernelSmoothTests) :
    Integrable (kernelDirichletPairDensity f g) (integralQuotientVolume globalKubotaKernel) := by
  have hf : ∀h : kernelSmoothTests,Integrable (fun q => (kernelQuotientEnergyDensity h q:ℂ))
      (integralQuotientVolume globalKubotaKernel) := fun h =>
    (kernelQuotientEnergyDensity_integrable h).ofReal
  exact ((hf (f+g)).sub (hf (f-g)) |>.add (((hf (f-Complex.I•g)).sub (hf (f+Complex.I•g))).mul_const _)).div_const _

lemma kernelDirichletPairDensity_add_right (f g h : kernelSmoothTests) (q : KernelQuotient) :
    kernelDirichletPairDensity f (g+h) q=kernelDirichletPairDensity f g q+kernelDirichletPairDensity f h q := by
  induction q using Quotient.inductionOn with
  | _ w => simp only [←show integralOrbitProjection globalKubotaKernel w=Quotient.mk _ w from rfl,
      kernelDirichletPairDensity_coordinate,map_add,inner_add_right]

lemma kernelDirichletPairDensity_smul_right (c : ℂ) (f g : kernelSmoothTests) (q : KernelQuotient) :
    kernelDirichletPairDensity f (c•g) q=c*kernelDirichletPairDensity f g q := by
  induction q using Quotient.inductionOn with
  | _ w => simp only [←show integralOrbitProjection globalKubotaKernel w=Quotient.mk _ w from rfl,
      kernelDirichletPairDensity_coordinate,map_smul,inner_smul_right]

lemma kernelDirichletPairDensity_conj (f g : kernelSmoothTests) (q : KernelQuotient) :
    star (kernelDirichletPairDensity g f q)=kernelDirichletPairDensity f g q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change star (kernelDirichletPairDensity g f (integralOrbitProjection globalKubotaKernel w))=
      kernelDirichletPairDensity f g (integralOrbitProjection globalKubotaKernel w)
    rw [kernelDirichletPairDensity_coordinate,kernelDirichletPairDensity_coordinate]
    exact inner_conj_symm _ _

lemma kernelDirichletPairDensity_self (f : kernelSmoothTests) (q : KernelQuotient) :
    kernelDirichletPairDensity f f q=(kernelQuotientEnergyDensity f q:ℂ) := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change kernelDirichletPairDensity f f (integralOrbitProjection globalKubotaKernel w)=_
    rw [kernelDirichletPairDensity_coordinate,inner_self_eq_norm_sq_to_K,RCLike.ofReal_eq_complex_ofReal,←Complex.ofReal_pow,kernelGradientAt_norm_sq]
    rfl

def kernelDirichletForm (f g : kernelSmoothTests) : ℂ :=
  ∫q,kernelDirichletPairDensity f g q ∂integralQuotientVolume globalKubotaKernel

lemma kernelDirichletForm_add_right (f g h : kernelSmoothTests) :
    kernelDirichletForm f (g+h)=kernelDirichletForm f g+kernelDirichletForm f h := by
  unfold kernelDirichletForm
  simp_rw [kernelDirichletPairDensity_add_right]
  exact integral_add (kernelDirichletPairDensity_integrable f g) (kernelDirichletPairDensity_integrable f h)

lemma kernelDirichletForm_smul_right (c : ℂ) (f g : kernelSmoothTests) :
    kernelDirichletForm f (c•g)=c*kernelDirichletForm f g := by
  unfold kernelDirichletForm
  simp_rw [kernelDirichletPairDensity_smul_right]
  exact integral_const_mul _ _

lemma kernelDirichletForm_conj (f g : kernelSmoothTests) :
    star (kernelDirichletForm g f)=kernelDirichletForm f g := by
  unfold kernelDirichletForm
  simp only [Complex.star_def]
  rw [←integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (kernelDirichletPairDensity_conj f g)

lemma kernelDirichletForm_self (f : kernelSmoothTests) :
    kernelDirichletForm f f=(kernelDirichletEnergy f:ℂ) := by
  unfold kernelDirichletForm kernelDirichletEnergy
  simp_rw [kernelDirichletPairDensity_self]
  exact integral_complex_ofReal

lemma kernelDirichletForm_self_nonneg (f : kernelSmoothTests) : 0≤(kernelDirichletForm f f).re := by
  rw [kernelDirichletForm_self,Complex.ofReal_re]
  exact kernelDirichletEnergy_nonneg f

end CubicEisenstein

namespace CompletedGauss

section

open scoped BigOperators Classical SchwartzMap
open MeasureTheory

theorem finite_integral_energy_bound {κ : Type*} [Fintype κ]
    (b : ℝ→ℂ) (φ : κ→ℝ→ℂ) (E : ℝ) (hE : 0≤E)
    (hb : Integrable (fun t => ‖b t‖))
    (hφ : ∀k,Integrable (fun t => b t*φ k t))
    (hbound : ∀t,(∑k,‖φ k t‖^2)≤E) :
    (∑k,‖∫t : ℝ,b t*φ k t‖^2)≤E*(∫t : ℝ,‖b t‖)^2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : ℝ→EuclideanSpace ℂ κ := fun t => e.symm (fun k => b t*φ k t)
  have hF (t : ℝ) : ‖F t‖≤‖b t‖*Real.sqrt E := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt hE]
    change (∑k,‖b t*φ k t‖^2)≤‖b t‖^2*E
    simp only [norm_mul,mul_pow,←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hbound t) (sq_nonneg _)
  have he : (∫t : ℝ,F t)=e.symm (fun k => ∫t : ℝ,b t*φ k t) := by
    rw [show F=(fun t => e.symm (fun k => b t*φ k t)) from rfl,e.symm.integral_comp_comm]
    congr 1
    funext k
    exact eval_integral hφ k
  have hn : ‖e.symm (fun k => ∫t : ℝ,b t*φ k t)‖≤(∫t : ℝ,‖b t‖)*Real.sqrt E := by
    rw [←he,←integral_mul_const]
    exact norm_integral_le_of_norm_le (hb.mul_const _) (Filter.Eventually.of_forall hF)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt hE] at hs
  simpa [e,mul_comm] using hs

open CanonicalQuadraticSieve ActualEisensteinCubic

theorem integrated_product_quadratic (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀K U B lengthScale : ℝ,1≤K → 1≤U → 1≤B → 0≤lengthScale →
    ∀S T : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
    ∀β : ℝ→Ideal O→Ideal O→ℂ,
      (∀n b,Continuous (fun t => β t n b)) →
      (∀t,∀n∈S,∀b∈T,‖β t n b‖≤lengthScale) →
    ∀rowPhase : idealRange K→ℝ→ℂ,(∀k,Continuous (rowPhase k)) → (∀k t,‖rowPhase k t‖≤1) →
    ∀b : 𝓢(ℝ,ℂ),
      (∑k : idealRange K,‖∫t : ℝ,b t*(rowPhase k t*
        ∑n∈S,∑v∈T,quadraticRow k.val (primaryGenerator (n*v))*β t n v)‖^2)≤
      C*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2*(∫t : ℝ,‖b t‖)^2 := by
  obtain ⟨C,hC,hbound⟩ := product_quadratic_norm_scaled ε hε
  refine ⟨C,hC,?_⟩
  intro K U B lengthScale hK hU hB hL S T hS hT β hβc hβ rowPhase hωc hω b
  let E := C*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2
  have hE : 0≤E := by dsimp [E]; positivity
  let φ : idealRange K→ℝ→ℂ := fun k t => rowPhase k t*
    ∑n∈S,∑v∈T,quadraticRow k.val (primaryGenerator (n*v))*β t n v
  have hφc (k : idealRange K) : Continuous (φ k) := by
    apply (hωc k).mul
    apply continuous_finsetSum
    intro n hn
    apply continuous_finsetSum
    intro v hv
    exact continuous_const.mul (hβc n v)
  have hφbound (t : ℝ) : (∑k,‖φ k t‖^2)≤E := by
    apply le_trans _ (hbound K U B lengthScale hK hU hB hL S T hS hT (β t) (hβ t))
    apply Finset.sum_le_sum
    intro k hk
    exact pow_le_pow_left₀ (norm_nonneg _) (by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hω k t)) 2
  have hpoint (k : idealRange K) (t : ℝ) : ‖φ k t‖≤Real.sqrt E := by
    apply (Real.le_sqrt (norm_nonneg _) hE).mpr
    exact (Finset.single_le_sum (fun j _ => sq_nonneg ‖φ j t‖) (Finset.mem_univ k)).trans (hφbound t)
  have hφint (k : idealRange K) : Integrable (fun t : ℝ => b t*φ k t) :=
    b.integrable.mul_bdd (hφc k).aestronglyMeasurable (Filter.Eventually.of_forall (hpoint k))
  exact finite_integral_energy_bound b φ E hE b.integrable.norm hφint hφbound

end

section
open ActualEisensteinCubic CanonicalQuadraticSieve

def completedRowFiber (S : Finset (Ideal O)) (Q A T : Ideal O) : Finset (Ideal O) :=
  S.filter (fun I => rowPowerfulPart I=A ∧ rowMaskPart I Q=T)

theorem rowResidualPart_injective_on_fiber (S : Finset (Ideal O)) (Q A T : Ideal O)
    (hS : ∀I∈S,I≠0) : Set.InjOn (fun I => rowResidualPart I Q) (completedRowFiber S Q A T) := by
  intro I hI J hJ he
  change rowResidualPart I Q=rowResidualPart J Q at he
  obtain ⟨hIS,hIA,hIT⟩ := Finset.mem_filter.mp hI
  obtain ⟨hJS,hJA,hJT⟩ := Finset.mem_filter.mp hJ
  calc
    I = rowPowerfulPart I*rowMaskPart I Q*rowResidualPart I Q := (row_powerful_mask_residual_product I Q (hS I hIS)).symm
    _ = rowPowerfulPart J*rowMaskPart J Q*rowResidualPart J Q := by rw [hIA,hJA,hIT,hJT,he]
    _ = J := row_powerful_mask_residual_product J Q (hS J hJS)

theorem completedRowFiber_residual_range (S : Finset (Ideal O)) (Q A T : Ideal O)
    (hbad : ∀P∈fixedBadPrimes,P∣Q) (K : ℝ)
    (hS : ∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) (I : Ideal O)
    (hI : I∈completedRowFiber S Q A T) :
    rowResidualPart I Q∈idealRange (K/((Ideal.absNorm A:ℝ)*(Ideal.absNorm T:ℝ))) := by
  obtain ⟨hIS,hIA,hIT⟩ := Finset.mem_filter.mp hI
  apply mem_idealRange.mpr
  refine ⟨rowResidualPart_admissible I Q hbad,?_⟩
  rw [rowResidualPart_norm I Q (hS I hIS).1,hIA,hIT]
  exact div_le_div_of_nonneg_right (hS I hIS).2 (by positivity)

theorem completedRowFiber_energy_le (S : Finset (Ideal O)) (Q A T : Ideal O)
    (hbad : ∀P∈fixedBadPrimes,P∣Q) (K : ℝ)
    (hS : ∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) (f : Ideal O→ℂ) :
    (∑I∈completedRowFiber S Q A T,‖f (rowResidualPart I Q)‖^2)≤
      ∑J : idealRange (K/((Ideal.absNorm A:ℝ)*(Ideal.absNorm T:ℝ))),‖f J.val‖^2 := by
  let U := (completedRowFiber S Q A T).image (fun I => rowResidualPart I Q)
  have he : (∑I∈completedRowFiber S Q A T,‖f (rowResidualPart I Q)‖^2)=∑J∈U,‖f J‖^2 := by
    rw [Finset.sum_image (rowResidualPart_injective_on_fiber S Q A T (fun I hI => (hS I hI).1))]
  rw [he,Finset.sum_coe_sort (s := idealRange (K/((Ideal.absNorm A:ℝ)*(Ideal.absNorm T:ℝ)))) (f := fun J : Ideal O => ‖f J‖^2)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro J hJ
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ
    exact completedRowFiber_residual_range S Q A T hbad K hS I hI
  · intro _ _ _
    exact sq_nonneg _

end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic CanonicalQuadraticSieve

theorem completed_kernel_three_window
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) (A : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀R : ℝ,0<R → ∃B : 𝓢(ℝ,ℂ),
      (∀r u v : ℝ,V₀ r*V₁ u*V₂ v*CubicReflectionKernel.paperKernel (Vstar W)
        (R*Real.exp (-2*r+u+3*v))=
        ∫t : ℝ,(V₀ r*FourierBridge.logPhase t (-2*r))*
          (V₁ u*FourierBridge.logPhase t u)*(V₂ v*FourierBridge.logPhase t (3*v))*B t) ∧
      (1+R)^A*(∫t : ℝ,‖B t‖)≤C := by
  let V : Fin 3→ℝ→ℂ := ![V₀,V₁,V₂]
  let slope : Fin 3→ℝ := ![-2,1,3]
  let M : Fin 3→ℝ := ![M₀,M₁,M₂]
  have hm : ∀i,0≤M i := by intro i; fin_cases i <;> assumption
  have hv : ∀i y,V i y≠0 → |y|≤M i := by intro i; fin_cases i <;> assumption
  obtain ⟨C,hC,h⟩ := completed_kernel_log_separation V slope M hm hv W a b ha hsupp hW A 0
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨B,hB,hi,hbound,hpoint⟩ := h R hR
  refine ⟨B,?_,by simpa only [pow_zero,one_mul] using hbound⟩
  intro r u v
  simpa [V,slope,Fin.prod_univ_succ,Fin.sum_univ_succ,mul_assoc,add_assoc] using hB ![r,u,v]

theorem completed_smooth_quadratic
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (hV₀n : ∀y,‖V₀ y‖≤1) (hV₁n : ∀y,‖V₁ y‖≤1) (hV₂n : ∀y,‖V₂ y‖≤1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (A : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀K U B lengthScale R : ℝ,1≤K → 1≤U → 1≤B → 0≤lengthScale → 0<R →
    ∀S T : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
    ∀β : Ideal O→Ideal O→ℂ,(∀n∈S,∀v∈T,‖β n v‖≤lengthScale) →
    ∀yr : idealRange K→ℝ,∀yn yb : Ideal O→ℝ,
    (∑k : idealRange K,‖∑n∈S,∑v∈T,
      quadraticRow k.val (primaryGenerator (n*v))*β n v*
      (V₀ (yr k)*V₁ (yn n)*V₂ (yb v)*CubicReflectionKernel.paperKernel (Vstar W)
        (R*Real.exp (-2*yr k+yn n+3*yb v)))‖^2)≤
      C*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2/(1+R)^(2*A) := by
  obtain ⟨Cq,hCq,hq⟩ := integrated_product_quadratic ε hε
  obtain ⟨Ck,hCk,hkernel⟩ := completed_kernel_three_window V₀ V₁ V₂ M₀ M₁ M₂
    hM₀ hM₁ hM₂ hV₀ hV₁ hV₂ W a b ha hsupp hW A
  refine ⟨Cq*(Ck^2+1),by positivity,?_⟩
  intro K U B lengthScale R hK hU hB hL hR S T hS hT β hβ yr yn yb
  obtain ⟨g,hsep,hg⟩ := hkernel R hR
  let rowPhase : idealRange K→ℝ→ℂ := fun k t => V₀ (yr k)*FourierBridge.logPhase t (-2*yr k)
  let βt : ℝ→Ideal O→Ideal O→ℂ := fun t n v =>
    β n v*(V₁ (yn n)*FourierBridge.logPhase t (yn n))*(V₂ (yb v)*FourierBridge.logPhase t (3*yb v))
  have hphase (t x : ℝ) : ‖FourierBridge.logPhase t x‖=1 := FourierBridge.logPhase_norm t x
  have hrowPhase (k : idealRange K) (t : ℝ) : ‖rowPhase k t‖≤1 := by
    simp only [rowPhase,norm_mul,hphase,mul_one]
    exact hV₀n _
  have hβt (t : ℝ) (n : Ideal O) (hn : n∈S) (v : Ideal O) (hv : v∈T) : ‖βt t n v‖≤lengthScale := by
    simp only [βt,norm_mul,hphase,mul_one]
    exact (mul_le_of_le_one_right (by positivity)
      (hV₂n _)).trans ((mul_le_of_le_one_right (norm_nonneg _) (hV₁n _)).trans (hβ n hn v hv))
  have hrowPhasec (k : idealRange K) : Continuous (rowPhase k) :=
    continuous_const.mul (FourierBridge.logPhase_continuous_left _)
  have hβtc (n v : Ideal O) : Continuous (fun t => βt t n v) :=
    (continuous_const.mul (continuous_const.mul (FourierBridge.logPhase_continuous_left _))).mul
      (continuous_const.mul (FourierBridge.logPhase_continuous_left _))
  have hi := hq K U B lengthScale hK hU hB hL S T hS hT βt hβtc hβt rowPhase hrowPhasec hrowPhase g
  have he (k : idealRange K) :
      (∑n∈S,∑v∈T,quadraticRow k.val (primaryGenerator (n*v))*β n v*
        (V₀ (yr k)*V₁ (yn n)*V₂ (yb v)*CubicReflectionKernel.paperKernel (Vstar W)
          (R*Real.exp (-2*yr k+yn n+3*yb v)))) =
      ∫t : ℝ,g t*(rowPhase k t*∑n∈S,∑v∈T,quadraticRow k.val (primaryGenerator (n*v))*βt t n v) := by
    have hint (n v : Ideal O) : Integrable (fun t : ℝ =>
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
    _ = _ := by ring

end CompletedGauss

open scoped BigOperators Classical SchwartzMap ContDiff

namespace InitialMeanSquare
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)

def initialLogProfile (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(ℝ,ℂ) :=
  ((CubicReflectionKernel.logProfile_compact W a b ha hs).mul_left
    (f := fun t : ℝ => (Real.exp (t/2) : ℂ))).toSchwartzMap (by
      change ContDiff ℝ ∞ (fun t : ℝ => (Real.exp (t/2) : ℂ)*W (Real.exp t))
      have he : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (t/2)) :=
        Real.contDiff_exp.comp (contDiff_id.div_const 2)
      exact (Complex.ofRealCLM.contDiff.comp he).mul
        (hW.comp Real.contDiff_exp))

@[simp] lemma initialLogProfile_apply (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (t : ℝ) :
    initialLogProfile W a b ha hs hW t =
      (Real.exp (t/2) : ℂ)*W (Real.exp t) := rfl

theorem initialLogProfile_support (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∀ t, initialLogProfile W a b ha hs hW t ≠ 0 →
      |t| ≤ |Real.log a|+|Real.log b|+1 := by
  intro t ht
  have hw : W (Real.exp t) ≠ 0 := by
    intro hz
    simp only [initialLogProfile_apply, hz, mul_zero] at ht
    exact ht rfl
  have hm := hs hw
  have hlo : Real.log a ≤ t := by
    simpa only [Real.log_exp] using Real.log_le_log ha hm.1
  have hhi : t ≤ Real.log b := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos t) hm.2
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log a), neg_abs_le (Real.log a),
    le_abs_self (Real.log b), abs_nonneg (Real.log a), abs_nonneg (Real.log b)]

theorem initialLogProfile_normalized {ι : Type*} (p : ι → O)
    (hp : ∀ i, p i ≠ 0) (S : Finset ι) (Z : ℝ) (hZ : 0 < Z)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    normalizedColumn p (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T)) S =
      (Real.sqrt Z : ℂ)⁻¹*W (primeProductNorm p S/Z) := by
  let n := ‖eisEmbedding (∏ i ∈ S,p i)‖
  have hn : 0 < n := norm_pos_iff.mpr
    (eisEmbedding_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)))
  have hpos : 0 < n^2/Z := div_pos (sq_pos_of_pos hn) hZ
  have hexp : Real.exp (Real.log (n^2/Z)/2)=n/Real.sqrt Z := by
    rw [←JointLogSeparation.sqrt_exp_half, Real.exp_log hpos,
      Real.sqrt_div (sq_nonneg n), Real.sqrt_sq hn.le]
  change ((Real.exp (Real.log (n^2/Z)/2) : ℂ)*W (Real.exp (Real.log (n^2/Z)))) /
    (n : ℂ) = (Real.sqrt Z : ℂ)⁻¹*W (n^2/Z)
  rw [hexp, Real.exp_log hpos, Complex.ofReal_div]
  have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn.ne'
  have hsz : (Real.sqrt Z : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hZ).ne'
  field_simp

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] in
lemma mobiusRow_mul (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (c : ℂ) (z : O) :
    mobiusRow p hg F Ψ m (fun S => c*H S) z = c*mobiusRow p hg F Ψ m H z := by
  simp only [mobiusRow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [inputColumn]
  ring

omit [DecidableEq ι] in
theorem mobiusRow_initial_normalization (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (z : O) (Z : ℝ) (hZ : 0 < Z)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    mobiusRow p hg F Ψ m
      (normalizedColumn p (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T))) z =
      (Real.sqrt Z : ℂ)⁻¹*mobiusRow p hg F Ψ m (fun T => W (primeProductNorm p T/Z)) z := by
  have hc : normalizedColumn p (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T)) =
      fun T => (Real.sqrt Z : ℂ)⁻¹*W (primeProductNorm p T/Z) := by
    funext T
    exact initialLogProfile_normalized p hp T Z hZ W a b ha hs hW
  rw [hc, mobiusRow_mul]

omit [DecidableEq ι] in
theorem mobiusRow_initial_energy (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (z : O) (Z : ℝ) (hZ : 0 < Z)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ‖mobiusRow p hg F Ψ m
      (normalizedColumn p (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T))) z‖^2 =
      ‖mobiusRow p hg F Ψ m (fun T => W (primeProductNorm p T/Z)) z‖^2/Z := by
  rw [mobiusRow_initial_normalization p hg hp F Ψ m z Z hZ W a b ha hs hW,
    norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.mpr hZ), mul_pow, inv_pow, Real.sq_sqrt hZ.le]
  ring

end InitialMeanSquare

end

end OAI
end OAIOriginalModule0201

/-! Original module: OAI.NumberTheory.DirichletL.MeanSquare.InputEnergy
Source SHA256: 0ec1f738fe80aef452f38abcff849e1049d4e5c088aa8d60379c629749e5b356
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0202


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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)

theorem poolProduct_admissible (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (S : Finset (primePool F)) : Admissible (∏ i ∈ S,i.val) := by
  have hp (i : primePool F) : Prime i.val :=
    Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
  have hn : (∏ i ∈ S,i.val) ≠ (0 : Ideal O) :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)
  refine ⟨hn, ?_, ?_⟩
  · apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i hi j hj hij
      exact (Ideal.isCoprime_of_isMaximal (fun he => hij (Subtype.ext he))).isRelPrime
    · intro i hi
      exact (hp i).squarefree
  · intro P hP
    obtain ⟨hprime, hdiv⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mp hP
    obtain ⟨i, hi, hPi⟩ := (hprime.dvd_finsetProd_iff (fun i : primePool F => i.val)).mp hdiv
    have he : P=i.val := (prime_dvd_prime_iff_eq hprime (hp i)).mp hPi
    rw [he]
    exact ⟨poolGood F hF i, poolOdd F hF i⟩

theorem poolPrimary_norm (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (S : Finset (primePool F)) :
    primeProductNorm (poolPrimary F) S = (Ideal.absNorm (∏ i ∈ S,i.val) : ℝ) := by
  rw [primeProductNorm, eisEmbedding_norm_sq_eq_absNorm_span, FiniteGaussPhase.span_finset_prod]
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  exact poolPrimary_span F hF i

theorem selectedIdealTest_full_range (W : ℝ → ℂ) (b Z X : ℝ) (hZ : 0 < Z)
    (hs : ∀ t, W t ≠ 0 → t ≤ b) (hX : b*Z ≤ X)
    (S : Finset (primePool (idealRange X))) :
    selectedIdealTest (idealRange X) (fun n => W (n/Z)) S =
      W (primeProductNorm (poolPrimary (idealRange X)) S/Z) := by
  have hF : ∀ I ∈ idealRange X, Admissible I := fun I hI => (mem_idealRange.mp hI).1
  rw [poolPrimary_norm (idealRange X) hF S]
  unfold selectedIdealTest
  by_cases hw : W ((Ideal.absNorm (∏ i ∈ S,i.val) : ℝ)/Z)=0
  · simp only [hw, ite_self]
  · rw [ite_eq_left]
    apply mem_idealRange.mpr
    refine ⟨poolProduct_admissible (idealRange X) hF S, ?_⟩
    exact ((div_le_iff₀ hZ).mp (hs _ hw)).trans hX

theorem idealRowSum_initial_energy {q : ℕ} (χ : DirichletCharacter ℂ q)
    (W : ℝ → ℂ) (a b Z X : ℝ) (ha : 0 < a) (hZ : 0 < Z)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hX : b*Z ≤ X) (z : O) :
    let F := idealRange X
    let hF := fun I (hI : I ∈ F) => (mem_idealRange.mp hI).1
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    ‖idealRowSum F (fun I hI => (hF I hI).1)
      (fun I hI P hP => ((hF I hI).2.2 P hP).1) χ (fun n => W (n/Z)) z‖^2/Z =
    ‖mobiusRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ (normCharacter χ) 1
      (normalizedColumn (poolPrimary F)
        (fun T => initialLogProfile W a b ha hs hW (columnLog (poolPrimary F) Z T))) z‖^2 := by
  dsimp only
  let F := idealRange X
  have hF : ∀ I ∈ F, Admissible I := fun I hI => (mem_idealRange.mp hI).1
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  rw [idealRowSum_eq_mobiusRow F hF]
  have ht : selectedIdealTest F (fun n => W (n/Z)) =
      fun T => W (primeProductNorm (poolPrimary F) T/Z) := by
    funext T
    exact selectedIdealTest_full_range W b Z X hZ (fun t ht => (hs ht).2) hX T
  rw [ht]
  exact (mobiusRow_initial_energy (poolPrimary F) (poolPrimary_good F hF)
    (poolPrimary_ne_zero F hF) Finset.univ (normCharacter χ) 1 z Z hZ W a b ha hs hW).symm

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
open RayFourExpansion (RayCharacter)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem inputConjugateRow_zero_of_mass_zero (F : Finset ι) (Ψ : O →* ℂ)
    (m c d : O) (H : Finset ι → ℂ)
    (hm : (∑S∈F.powerset,‖secondInputCoefficient p hg Ψ m c d H S‖^2)=0) (z : O) :
    inputConjugateRow p hg F Ψ m c d H z=0 := by
  unfold inputConjugateRow FirstCauchyArithmetic.supportConjugateSum
  apply Finset.sum_eq_zero
  intro S hS
  have hle : ‖secondInputCoefficient p hg Ψ m c d H S‖^2≤0 := by
    rw [←hm]
    exact Finset.single_le_sum (f := fun A => ‖secondInputCoefficient p hg Ψ m c d H A‖^2) (fun A _ => sq_nonneg _) hS
  have hz : secondInputCoefficient p hg Ψ m c d H S=0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (secondInputCoefficient p hg Ψ m c d H S)]
  simp only [hz,mul_zero,zero_mul]

include hp in
theorem globalFirstCoreRow_zero_off_support (pool : Finset ι) (b : GlobalFirstData ι)
    (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ,ℂ)) (ell M U : ℝ) (hell : 0<ell)
    (hM : ∀t,g t≠0 → |t|≤M) (hU : ell*Real.exp M≤U)
    (side : Bool) (χ : RayCharacter) (r : FirstCoreIndex) (t : ℝ) (z : O)
    (hoff : ¬(primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U)) :
    globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z=0 := by
  have hX : 0<globalFirstBlockColumnScale p ell side b :=
    div_pos hell (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp _) (FirstPassCubeLabels.primeProductNorm_pos p hp _))
  have hm := globalFirstColumnMass_zero_off_support p hp hg pool b (firstCoreTwist side χ Ψ r) m
    (firstCoreModeProfile g V side t) ell M U hell
    (fun u hu => hM u (firstCoreModeProfile_support g V side t u hu).1) hU side hoff
  have hz := inputConjugateRow_zero_of_mass_zero p hg (globalFirstRawPool pool b)
    (firstCoreTwist side χ Ψ r) (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
    (globalFirstBlockTest p (firstCoreModeProfile g V side t) ell side b) hm (if side then -z else z)
  unfold globalFirstCoreRow
  rw [firstCoreInputRow_eq_mode_row p hp hg _ _ _ _ _ _ side χ Ψ m g V _ hX]
  change _*inputConjugateRow p hg (globalFirstRawPool pool b) (firstCoreTwist side χ Ψ r)
    (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
    (globalFirstBlockTest p (firstCoreModeProfile g V side t) ell side b) (if side then -z else z)=0
  rw [hz,mul_zero]

include hp in

theorem globalFirstFiniteEnergy_eq_supported (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℝ) (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ,ℂ))
    (ell M U : ℝ) (hell : 0<ell) (hM : ∀t,g t≠0 → |t|≤M) (hU : ell*Real.exp M≤U)
    (side : Bool) (χ : RayCharacter) (r : FirstCoreIndex)
    (T : GlobalFirstData ι → Finset O) (t : ℝ) :
    globalFirstFiniteEnergy p hg pool s w Ψ m g V ell side χ r T t=
      globalFirstFiniteEnergy p hg pool
        (s.filter (fun b => primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U))
        w Ψ m g V ell side χ r T t := by
  unfold globalFirstFiniteEnergy
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro b hb hn
  have hoff : ¬(primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U) := by
    intro hh; exact hn (Finset.mem_filter.mpr ⟨hb,hh⟩)
  have hz (z : O) := globalFirstCoreRow_zero_off_support p hp hg pool b Ψ m g V ell M U hell hM hU side χ r t z hoff
  simp only [hz,norm_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero,mul_zero]

end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)

def globalFirstTailFactor (K ell B F U H : ℝ) (N : ℕ) : ℝ :=
  (1+U)^4*(1+(1+U)^3*(K*U^2/(ell^2*B^2*F^2)))^2/(1+H)^N

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem globalFirstPooledRow_lower_from_common (b : GlobalFirstData ι)
    (K ell B F U : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) (hU : 0<U)
    (hc : primeProductNorm p b.common≤U)
    (hb1 : ‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb2 : ‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) (side : Bool) :
    ell^2*B^2*F^2/(K*U^2)≤globalFirstPooledRow p K ell B F side b := by
  let x := b.append (⟨∅,∅,∅,1⟩ : SecondExpansionData ι)
  let j := globalScaleIndex p side x
  have hC : globalLogRep j 1≤U := (globalScaleIndex_bounds p hp side x one_ne_zero 1).1.trans hc
  have hJ := globalPooled_J_bound p hp B hB side x one_ne_zero hb1 hb2
  have hcp := globalLogRep_pos j 1
  have hjp := globalLogRep_pos j 4
  have hd := globalLogRep_ge_one j 5
  have he : 1≤Real.exp 1 := Real.one_le_exp (by norm_num)
  change _≤Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4)
  calc
    _ = ell^2*B^4*F^2/(K*U^2*B^2) := by field_simp
    _ ≤ _ := by
      apply div_le_div₀ (by positivity)
      · calc
          ell^2*B^4*F^2 = 1*ell^2*B^4*F^2*1 := by ring
          _ ≤ _ := by gcongr
      · positivity
      · gcongr

include hp in
theorem globalFirstTailFactor_bound (b : GlobalFirstData ι)
    (K ell B F M U H : ℝ) (N : ℕ)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) (hU : 1≤U) (hH : 0≤H)
    (hellU : ell*Real.exp M≤U) (hc : primeProductNorm p b.common≤U)
    (hb1 : ‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb2 : ‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) (side : Bool) :
    let lengthScale := 1+globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon*Real.exp M
    let Y := globalFirstPooledRow p K ell B F side b
    lengthScale^4*(1+lengthScale^3/Y)^2/(1+H)^N≤globalFirstTailFactor K ell B F U H N := by
  dsimp only
  let X := globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon
  let Y := globalFirstPooledRow p K ell B F side b
  have ha := primeProductNorm_ge_one p hp (b.cube.sideDivisor side)
  have hc1 := primeProductNorm_ge_one p hp b.common
  have ht := primeProductNorm_ge_one p hp b.firstCommon
  have hX : 0<X := by
    dsimp [X,globalFirstBlockColumnScale]
    positivity
  have hXle : X≤ell := by
    dsimp [X,globalFirstBlockColumnScale]
    apply (div_le_self (by positivity) ht).trans
    exact div_le_self hell.le (one_le_mul_of_one_le_of_one_le ha hc1)
  have hL : 1+X*Real.exp M≤1+U := add_le_add le_rfl ((mul_le_mul_of_nonneg_right hXle (Real.exp_pos _).le).trans hellU)
  have hY : 0<Y := globalPooledRowScale_pos K ell B F hK hell hB hF _
  have hlower := globalFirstPooledRow_lower_from_common p hp b K ell B F U hK hell hB hF (by linarith) hc hb1 hb2 side
  have hinv : 1/Y≤K*U^2/(ell^2*B^2*F^2) := by
    have h := one_div_le_one_div_of_le (by positivity : 0<ell^2*B^2*F^2/(K*U^2)) hlower
    simpa only [one_div_div] using h
  have hratio : (1+X*Real.exp M)^3/Y≤(1+U)^3*(K*U^2/(ell^2*B^2*F^2)) := by
    calc
      _ = (1+X*Real.exp M)^3*(1/Y) := by ring
      _ ≤ _ := by gcongr
  change (1+X*Real.exp M)^4*(1+(1+X*Real.exp M)^3/Y)^2/(1+H)^N≤_
  unfold globalFirstTailFactor
  gcongr

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

theorem globalFirstWeightedVolume_bound (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι → O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℝ)
      (Γ K ell B F U : ℝ) (side : Bool),
      0≤Γ → 0<K → 0<ell → 1≤B → 0<F → 1≤U →
      (∀b∈s,0≤w b ∧ w b≤Γ) → (∀b∈s,GlobalFirstAdmissible b) →
      (∀b∈s,primeProductNorm p b.common≤U) → (∀b∈s,primeProductNorm p b.firstCommon≤U) →
      (∀b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∑b∈s,w b*globalFirstCoefficient p K ell B F side b*
        globalFirstPooledRow p K ell B F side b*(primeProductNorm p b.firstCommon)⁻¹)≤
          C*Γ*(ell*B^3*F)*(B*U)^ε := by
  obtain ⟨Cd,hCd,hcount⟩ := globalFirstData_harmonic_sum (ε/3) (by positivity)
  obtain ⟨Cp,hCp,hpowers⟩ := globalDiagonalPowers ε hε
  refine ⟨Cd*(Real.exp 1)^3*Cp,by positivity,?_⟩
  intro ι _ p hp _ hinj s w Γ K ell B F U side hΓ hK hell hB hF hU hw hs hC ht hb1 hb2
  have hB0 : 0<B := by linarith
  let θ := fun b : GlobalFirstData ι =>
    (1/primeProductNorm p b.common)*(1/primeProductNorm p b.firstCommon)*
      (1/‖eisEmbedding (∏i∈cubeActiveSupport b.cube.support
        (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖)
  have hsum := hcount p hp hinj s B U hB hU hs hC ht hb1 hb2
  change (∑b∈s,θ b)≤_ at hsum
  have hterm (b : GlobalFirstData ι) (hb : b∈s) :
      w b*globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*
        (primeProductNorm p b.firstCommon)⁻¹≤(Γ*(Real.exp 1)^3*ell*B^2*F)*θ b := by
    have htpos := FirstPassCubeLabels.primeProductNorm_pos p hp b.firstCommon
    have hc : 0≤globalFirstCoefficient p K ell B F side b :=
      globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB0 hF _
    have hY : 0<globalFirstPooledRow p K ell B F side b := globalPooledRowScale_pos K ell B F hK hell hB0 hF _
    have hsc := globalFirst_diagonal_scalar p hp K ell B F hK hell hB0 hF side b
    have hsc' : globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*
        (primeProductNorm p b.firstCommon)⁻¹≤((Real.exp 1)^3*ell*B^2*F)*θ b := by
      convert hsc using 1 ; dsimp [θ] ; ring
    calc
      _ = w b*(globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*
        (primeProductNorm p b.firstCommon)⁻¹) := by ring
      _ ≤ Γ*(globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*
        (primeProductNorm p b.firstCommon)⁻¹) := mul_le_mul_of_nonneg_right (hw b hb).2 (by positivity)
      _ ≤ Γ*(((Real.exp 1)^3*ell*B^2*F)*θ b) := mul_le_mul_of_nonneg_left hsc' hΓ
      _ = _ := by ring
  calc
    _ ≤ (Γ*(Real.exp 1)^3*ell*B^2*F)*(∑b∈s,θ b) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    _ ≤ (Γ*(Real.exp 1)^3*ell*B^2*F)*
        (Cd*B^(1+ε/3)*(U*B^2)^(ε/3)*(128*Real.exp 1*(normLogBin U+1 : ℝ))^2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (Cd*(Real.exp 1)^3)*Γ*(ell*B^3*F)*
        (B^(ε/3)*(U*B^2)^(ε/3)*(128*Real.exp 1*(normLogBin U+1 : ℝ))^2) := by
      rw [Real.rpow_add hB0,Real.rpow_one]
      ring
    _ ≤ (Cd*(Real.exp 1)^3)*Γ*(ell*B^3*F)*(Cp*(B*U)^ε) :=
      mul_le_mul_of_nonneg_left (hpowers B U hB hU) (by positivity)
    _ = _ := by ring

theorem globalFirstTailCost_parent_bound (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι → O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℝ)
      (Γ K ell B F M U H : ℝ) (N : ℕ) (side : Bool),
      0≤Γ → 0<K → 0<ell → 1≤B → 0<F → 1≤U → 0≤H → ell*Real.exp M≤U →
      (∀b∈s,0≤w b ∧ w b≤Γ) → (∀b∈s,GlobalFirstAdmissible b) →
      (∀b∈s,primeProductNorm p b.common≤U) → (∀b∈s,primeProductNorm p b.firstCommon≤U) →
      (∀b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      globalFirstTailCost p s (fun b => ((w b*globalFirstCoefficient p K ell B F side b : ℝ) : ℂ))
        K ell B F M H N side≤C*Γ*(ell*B^3*F)*(B*U)^ε*globalFirstTailFactor K ell B F U H N := by
  obtain ⟨C,hC,hvolume⟩ := globalFirstWeightedVolume_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj s w Γ K ell B F M U H N side hΓ hK hell hB hF hU hH hellU hw hs hCnorm ht hb1 hb2
  have hB0 : 0<B := by linarith
  have hfactor : 0≤globalFirstTailFactor K ell B F U H N := by unfold globalFirstTailFactor; positivity
  have hv := hvolume p hp hinj s w Γ K ell B F U side hΓ hK hell hB hF hU hw hs hCnorm ht hb1 hb2
  apply le_trans _ (mul_le_mul_of_nonneg_right hv hfactor)
  unfold globalFirstTailCost
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro b hb
  dsimp only
  have hc : 0≤globalFirstCoefficient p K ell B F side b :=
    globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB0 hF _
  have hY : 0<globalFirstPooledRow p K ell B F side b := globalPooledRowScale_pos K ell B F hK hell hB0 hF _
  have hT := FirstPassCubeLabels.primeProductNorm_pos p hp b.firstCommon
  have hw0 := (hw b hb).1
  rw [Complex.norm_real,Real.norm_of_nonneg (mul_nonneg hw0 hc)]
  have h := globalFirstTailFactor_bound p hp b K ell B F M U H N hK hell hB0 hF hU hH hellU (hCnorm b hb) (hb1 b hb) (hb2 b hb) side
  dsimp only at h
  have h' := mul_le_mul_of_nonneg_left h
    (show 0≤w b*globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*
      (primeProductNorm p b.firstCommon)⁻¹ by positivity)
  convert h' using 1 ; ring

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

theorem globalFirstCoreRows_quantitative_transfer
    (ε : ℝ) (hε : 0<ε) (g V : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0≤M)
    (hgM : ∀ t,g t ≠ 0 → |t|≤M) (side : Bool) (A J N : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Cd Ct : ℝ),0≤C ∧ 0<Cd ∧ 0<Ct ∧
      (∀ i,HasCompactSupport (windows i)) ∧ (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t|≤M+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (s : Finset (GlobalFirstData ι))
      (w : GlobalFirstData ι → ℝ) (Γ K ell B F H U : ℝ)
      (Ψ : O →* ℂ) (m : O) (χ : RayCharacter) (r : FirstCoreIndex)
      (T : GlobalFirstData ι → Finset O),
      0≤Γ → (∀ b∈s,0≤w b ∧ w b≤Γ) → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U → ell*Real.exp M≤U →
      (∀ b∈s,GlobalFirstAdmissible b) → (∀ a,‖Ψ a‖≤1) →
      (∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈s,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F side b) →
      (∀ b∈s,∀ z∈T b,z≠0) →
      let activeFamily := s.filter (fun b => FirstPassCubeLabels.primeProductNorm p b.common≤U ∧
        FirstPassCubeLabels.primeProductNorm p b.firstCommon≤U)
      let source := globalFirstSupportedPool p pool activeFamily
        (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side
      let weight := fun b => w b*globalFirstCoefficient p K ell B F side b
      let Ψmode := firstCoreTwist side χ Ψ r
      (∫ t : ℝ,firstLogDensity (2*(J+2)) t*
        globalFirstFiniteEnergy p hg pool s weight Ψ m g V ell side χ r T t) ≤
      (∫ t : ℝ,firstLogDensity 0 t)*
        (Cd*Γ*(ell*B^3*F)*(B*U)^ε +
          globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*C) ε 0 0 K ell B F M H A J side +
          Ct*Γ*(ell*B^3*F)*(B*U)^ε*globalFirstTailFactor K ell B F U H N) := by
  have hbase : ∀t,firstCoreBaseProfile g V side t≠0 → |t|≤M := by
    intro t ht
    apply hgM t
    intro hz
    apply ht
    simp only [firstCoreBaseProfile_apply,hz,zero_mul]
  obtain ⟨windows,C,Ct0,hC,hCt0,hwc,hws,hwb,hrows⟩ :=
    globalFirstCoreRows_integrated_transfer ε hε g V M hM hgM side A J N
  obtain ⟨Cd,hCd,hdiag⟩ := globalFirstDiagonalCost_parent_bound ε hε
    (firstCoreBaseProfile g V side) rowMajorant M hbase
  obtain ⟨Ct1,hCt1,htail⟩ := globalFirstTailCost_parent_bound ε hε
  refine ⟨windows,C,Cd,Ct0*Ct1,hC,hCd,mul_pos hCt0 hCt1,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr pool s w Γ K ell B F H U Ψ m χ r T
    hΓ hw hK hell hB hF hH hU hellU hs hΨ hb1 hb2 hT hT0
  dsimp only
  have hB0 : 0<B := by linarith
  let activeFamily := s.filter (fun b => FirstPassCubeLabels.primeProductNorm p b.common≤U ∧
    FirstPassCubeLabels.primeProductNorm p b.firstCommon≤U)
  let weight := fun b => w b*globalFirstCoefficient p K ell B F side b
  let Ψmode := firstCoreTwist side χ Ψ r
  have hsub (b : GlobalFirstData ι) (hb : b∈activeFamily) : b∈s := (Finset.mem_filter.mp hb).1
  have hΓw := fun b hb => hw b (hsub b hb)
  have hsa := fun b hb => hs b (hsub b hb)
  have hba1 := fun b hb => hb1 b (hsub b hb)
  have hba2 := fun b hb => hb2 b (hsub b hb)
  have hΨmode : ∀a,‖Ψmode a‖≤1 := fun a => (firstCoreTwist_norm_le side χ Ψ r a).trans (hΨ a)
  have hr := hrows p hp hcop hg hinj hc hpr pool activeFamily w Γ K ell B F H Ψ m χ r T
    hΓ hΓw hK hell hB0 hF hH hsa hΨ hba1 hba2
    (fun b hb => hT b (hsub b hb)) (fun b hb => hT0 b (hsub b hb))
  dsimp only at hr
  have hd := hdiag p hp hg hinj pool activeFamily w Ψmode m Γ K ell B F U side
    hΓ hK hell hB hF hU hellU hΨmode hΓw hsa hba1 hba2
  have ht := htail p hp hinj activeFamily w Γ K ell B F M U H N side
    hΓ hK hell hB hF hU hH hellU hΓw hsa
    (fun b hb => (Finset.mem_filter.mp hb).2.1) (fun b hb => (Finset.mem_filter.mp hb).2.2) hba1 hba2
  have heq :
      (∫t : ℝ,firstLogDensity (2*(J+2)) t*globalFirstFiniteEnergy p hg pool s weight Ψ m g V ell side χ r T t)=
      (∫t : ℝ,firstLogDensity (2*(J+2)) t*globalFirstFiniteEnergy p hg pool activeFamily weight Ψ m g V ell side χ r T t) := by
    apply integral_congr_ae
    filter_upwards with t
    rw [globalFirstFiniteEnergy_eq_supported p hp hg pool s weight Ψ m g V ell M U hell hgM hellU side χ r T t]
  rw [heq]
  apply hr.trans
  apply mul_le_mul_of_nonneg_left _ (integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t))
  have ht' := mul_le_mul_of_nonneg_left ht hCt0.le
  have h := add_le_add (add_le_add hd (le_refl
    (globalChildBudget p hp hcop hg pool
      (globalFirstSupportedPool p pool activeFamily
        (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side)
      Ψmode m windows (Γ*C) ε 0 0 K ell B F M H A J side))) ht'
  convert h using 1 ; dsimp [weight,Ψmode] ; ring

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct primeProductNorm firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter crossCoeff)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def globalFirstRayChildBudget (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C Γ ε K ell B F M H U : ℝ) (A J : ℕ) (side : Bool) : ℝ :=
  let family := (globalFirstFamilySet pool blocks).filter
    (fun b => primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U)
  let source := globalFirstSupportedPool p pool family
    (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side
  ∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖*∑r : FirstCoreIndex,
    (∫t : ℝ,firstLogDensity 0 t)*globalChildBudget p hp hcop hg pool source
      (firstCoreTwist side (if side then a.1 else a.2) Ψ r) m windows (Γ*firstCoreUniformWeight r*C)
      ε 0 0 K ell B F M H A J side

def globalFirstQuantitativeBudget (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C Cd Ct Γ ε K ell B F M H U : ℝ) (A J N : ℕ) (side : Bool) : ℝ :=
  (∫t : ℝ,firstLogDensity 0 t)*(512*(512*32))*Γ*(ell*B^3*F)*(B*U)^ε*
      (Cd+Ct*globalFirstTailFactor K ell B F U H N) +
    globalFirstRayChildBudget p hp hcop hg pool blocks Ψ m windows C Γ ε K ell B F M H U A J side

end

private lemma two_finite_error_sum {α β : Type*} [Fintype α] [Fintype β]
    (a : α → ℝ) (b : β → ℝ) (E : ℝ) (c : α → β → ℝ) :
    (∑x,a x*∑y,(b y*E+c x y))=(∑x,a x)*(∑y,b y)*E+∑x,a x*∑y,c x y := by
  simp only [Finset.sum_add_distrib,Finset.sum_mul,mul_add]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [←Finset.sum_mul]
  ring

theorem globalCubeInputFamilyEnergy_quantitative
    (ε : ℝ) (hε : 0<ε) (g V : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0≤M)
    (hgM : ∀t,g t≠0 → |t|≤M) (side : Bool) (A J N : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Cd Ct : ℝ),0≤C ∧ 0<Cd ∧ 0<Ct ∧
      (∀i,HasCompactSupport (windows i)) ∧ (∀i,ContDiff ℝ ∞ (windows i)) ∧
      (∀i t,windows i t≠0 → |t|≤M+6+1) ∧
      ∀{ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀i,ringChar (O ⧸ Ideal.span {p i})≠2) (_hpr : ∀i,lambda^2∣p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (w : GlobalCubeBlock ι → ℝ) (Γ K ell B F H U : ℝ)
      (Ψ : O →* ℂ) (m : O) (T : GlobalCubeBlock ι → Finset O),
      0≤Γ → (∀b∈blocks,0≤w b ∧ w b≤Γ) → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U → ell*Real.exp M≤U →
      (∀b∈blocks,GlobalCubeAdmissible b) → (∀a,‖Ψ a‖≤1) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀b∈blocks,∀z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F side (b.withCommon ∅)) →
      (∀b∈blocks,∀z∈T b,z≠0) →
      (∑b∈blocks,w b*globalCubeCoefficient p K ell B F side b*
        globalCubeInputFamilyEnergy p hg pool b Ψ m g V ell side (2*(J+2)) (T b))≤
      globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ m windows C Cd Ct Γ ε K ell B F M H U A J N side := by
  obtain ⟨windows,C,Cd,Ct,hC,hCd,hCt,hwc,hws,hwb,hrow⟩ :=
    globalFirstCoreRows_quantitative_transfer ε hε g V M hM hgM side A J N
  refine ⟨windows,C,Cd,Ct,hC,hCd,hCt,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr pool blocks w Γ K ell B F H U Ψ m T
    hΓ hw hK hell hB hF hH hU hellU hs hΨ hb1 hb2 hT hT0
  have hB0 : 0<B := by linarith
  let family := globalFirstFamilySet pool blocks
  let activeFamily := family.filter (fun b => primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U)
  let source := globalFirstSupportedPool p pool activeFamily
    (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side
  let child := fun (a : RayCharacter×RayCharacter) (r : FirstCoreIndex) =>
    (∫t : ℝ,firstLogDensity 0 t)*globalChildBudget p hp hcop hg pool source
      (firstCoreTwist side (if side then a.1 else a.2) Ψ r) m windows (Γ*firstCoreUniformWeight r*C)
      ε 0 0 K ell B F M H A J side
  let E0 := (∫t : ℝ,firstLogDensity 0 t)*Γ*(ell*B^3*F)*(B*U)^ε*(Cd+Ct*globalFirstTailFactor K ell B F U H N)
  have hI : 0≤∫t : ℝ,firstLogDensity 0 t := integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hf0 : 0≤globalFirstTailFactor K ell B F U H N := by unfold globalFirstTailFactor; positivity
  have hE0 : 0≤E0 := by dsimp [E0]; positivity
  have hrow' (a : RayCharacter×RayCharacter) (r : FirstCoreIndex) :
      (∫t : ℝ,firstLogDensity (2*(J+2)) t*
        globalFirstFiniteEnergy p hg pool family
          (fun d => globalFirstFamilyWeight p hg w Ψ m side r d*globalFirstCoefficient p K ell B F side d)
          Ψ m g V ell side (if side then a.1 else a.2) r (fun d => T d.block) t)≤
      firstCoreUniformWeight r*E0+child a r := by
    have hΓr : 0≤Γ*firstCoreUniformWeight r := by unfold firstCoreUniformWeight; positivity
    have h := hrow p hp hcop hg hinj hc hpr pool family
      (globalFirstFamilyWeight p hg w Ψ m side r) (Γ*firstCoreUniformWeight r) K ell B F H U Ψ m
      (if side then a.1 else a.2) r (fun d => T d.block) hΓr
      (fun d hd => globalFirstFamilyWeight_bounds p hg blocks w Γ hw Ψ hΨ m side r pool d hd)
      hK hell hB hF hH hU hellU
      (fun d hd => hs d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1) hΨ
      (fun d hd => hb1 d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1)
      (fun d hd => hb2 d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1)
      (by intro d hd z hz; rw [globalFirstPooledRow_block]; exact hT d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1 z hz)
      (fun d hd => hT0 d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1)
    dsimp only at h
    convert h using 1 ; dsimp [E0,child,source,activeFamily] ; ring
  rw [globalCubeInputFamilyEnergy_eq_integrated_rows]
  have hm : (∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖)*(∑r : FirstCoreIndex,firstCoreUniformWeight r)≤512*(512*32) := by
    have ha : (∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖)≤512 := by
      simpa only [Fintype.sum_prod_type] using RayFourExpansion.crossCoeff_sum_norm_le
    exact mul_le_mul ha firstCoreUniformWeight_mass
      (Finset.sum_nonneg (fun r _ => by unfold firstCoreUniformWeight; positivity)) (by norm_num)
  calc
    _ ≤ ∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖*∑r : FirstCoreIndex,(firstCoreUniformWeight r*E0+child a r) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun r _ => hrow' a r)) (norm_nonneg _))
    _ = ((∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖)*(∑r : FirstCoreIndex,firstCoreUniformWeight r))*E0+
        ∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖*∑r : FirstCoreIndex,child a r :=
      two_finite_error_sum _ _ _ _
    _ ≤ (512*(512*32))*E0+∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖*∑r : FirstCoreIndex,child a r :=
      add_le_add (mul_le_mul_of_nonneg_right hm hE0) le_rfl
    _ = _ := by
      unfold globalFirstQuantitativeBudget globalFirstRayChildBudget
      dsimp [E0,child,source,activeFamily,family]
      ring

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0202

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.QuantitativePassage
Source SHA256: 9abb0b7909494b09587017f6bdc731c69d379770aecece0d458e8f0d5f637600
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0203


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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

theorem globalTwoPassage_quantitative
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀ t,g₁ t≠0 → |t|≤M₁) (hg₂ : ∀ t,g₂ t≠0 → |t|≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤N₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤N₂)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃ (windows₁ windows₂ : Fin 7 → ℝ → ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
      (∀ i,HasCompactSupport (windows₁ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀ i t,windows₁ i t≠0 → |t|≤M₁+6+1) ∧
      (∀ i,HasCompactSupport (windows₂ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀ i t,windows₂ i t≠0 → |t|≤M₂+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (Γ K ell B F H U : ℝ),
      0≤Γ → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U → ell*Real.exp M₁≤U → ell*Real.exp M₂≤U →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b ∧ w b≤Γ) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,GlobalCubeAdmissible b) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,(Ideal.absNorm x.1 : ℝ)≤F) →
      (∀ b∈blocks,∀ x∈s b,‖eisEmbedding x.2‖^2≤globalFirstFrequencyScale p K ell b) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,globalCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₁ m₁ windows₁ C₁ Cd₁ Ct₁ Γ ε K ell B F M₁ H U A J N true) *
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₂ m₂ windows₂ C₂ Cd₂ Ct₂ Γ ε K ell B F M₂ H U A J N false) := by
  obtain ⟨Cfirst,hCfirst,hfirst⟩ := globalCubeFirstBlock_input_transfer W V₁ V₂ N₁ N₂ hN₁ hN₂ hV₁ hV₂ (2*(J+2)) deltaLoss hδ
  obtain ⟨windows₁,C₁,Cd₁,Ct₁,hC₁,hCd₁,hCt₁,hwc₁,hws₁,hwb₁,hleft⟩ :=
    globalCubeInputFamilyEnergy_quantitative ε hε g₁ V₁ M₁ hM₁ hg₁ true A J N
  obtain ⟨windows₂,C₂,Cd₂,Ct₂,hC₂,hCd₂,hCt₂,hwc₂,hws₂,hwb₂,hright⟩ :=
    globalCubeInputFamilyEnergy_quantitative ε hε g₂ V₂ M₂ hM₂ hg₂ false A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCfirst,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w Ψ₁ Ψ₂ m₁ m₂ Γ K ell B F H U
    hΓ hK hell hB hF hH hU hellU1 hellU2 hΨ₁ hΨ₂ hw ha hadm hb₁ hb₂ hsf hs0 hf hh
  have hB0 : 0<B := by linarith
  let T := fun b => globalCubeFirstTargets p b (s b)
  have hT0 (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) : z≠0 :=
    globalCubeFirstTargets_ne_zero p hp b (s b) (hsf b hb) (hs0 b hb) z hz
  have hT (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) :
      (Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F true (b.withCommon ∅) :=
    globalCubeFirstTargets_norm_bound p hp b (s b) K ell B F hK hell hB0 hF
      (hb₁ b hb) (hb₂ b hb) (hf b hb) (hh b hb) z hz
  have hTc (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) :
      (Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F false (b.withCommon ∅) := by
    rw [globalFirstPooledRow_side]
    exact hT b hb z hz
  have hblock := hfirst p hp hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ K ell B F
    (globalFirstRowCap K ell B F) hK hell hB0 hF hΨ₁ hΨ₂ (fun b hb => (hw b hb).1) ha
    (fun b hb => globalFirstPooledRow_le_cap p hp K ell B F hK hell hB0 hF b (hadm b hb) (hb₁ b hb) (hb₂ b hb))
    hsf hs0 (fun b _ x hx => globalCubeFirstTargets_mem p b (s b) x hx) hT0 hT
  have hl := hleft p hp hcop hg hinj hc hpr pool blocks w Γ K ell B F H U Ψ₁ m₁ T
    hΓ hw hK hell hB hF hH hU hellU1 hadm hΨ₁ hb₁ hb₂ hT hT0
  have hr := hright p hp hcop hg hinj hc hpr pool blocks w Γ K ell B F H U Ψ₂ m₂ T
    hΓ hw hK hell hB hF hH hU hellU2 hadm hΨ₂ hb₁ hb₂ hTc hT0
  have hprefix : 0≤Cfirst*(globalFirstRowCap K ell B F)^deltaLoss :=
    mul_nonneg hCfirst (Real.rpow_nonneg (globalFirstRowCap_pos K ell B F hK hell hB0 hF).le _)
  exact hblock.trans (mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hl) hprefix)
    (Real.sqrt_le_sqrt hr) (Real.sqrt_nonneg _) (mul_nonneg hprefix (Real.sqrt_nonneg _)))

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel columnLog)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def canonicalCubeFirstBlock (pool : Finset ι) (b : GlobalCubeBlock ι)
    (s : Finset (Ideal O × O)) (a : Ideal O × O → ℂ)
    (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ W V₁ V₂ : 𝓢(ℝ,ℂ)) (K ell : ℝ) : ℂ :=
  let c := primeSubsetGenerator (fun i => Ideal.span {p i}) b.common
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor
  let X₁ := globalCubeColumnScale p ell true b
  let X₂ := globalCubeColumnScale p ell false b
  (primeProductNorm p b.firstDivisor : ℂ)⁻¹ * ∑ x∈s,a x*actualFirstKernel p hp hcop hg (globalCubePool pool b) b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
    (originalLabelColumn p hg b.cube.support b.cube.leftBit b.cube.rightBit true
      (multiplicativeCoreColumn p Ψ₁ m₁ (fun S => g₁ (columnLog p X₁ S))) c (ConcretePrimeRowBridge.idealGenerator x.1))
    (originalLabelColumn p hg b.cube.support b.cube.leftBit b.cube.rightBit false
      (multiplicativeCoreColumn p Ψ₂ m₂ (fun S => g₂ (columnLog p X₂ S))) c (ConcretePrimeRowBridge.idealGenerator x.1))
    W V₁ V₂ X₁ X₂ K d x.2

end

theorem canonicalCubeFirstBlock_input_transfer
    (W V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ : ℝ) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤M₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤M₂)
    (J : ℕ) (deltaLoss : ℝ) (hδ : 0<deltaLoss) :
    ∃ C : ℝ,0≤C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ) (T : GlobalCubeBlock ι → Finset O)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ : 𝓢(ℝ,ℂ)) (K ell B F Ymax : ℝ),
      0<K → 0<ell → 0<B → 0<F →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,globalFirstPooledRow p K ell B F true (b.withCommon ∅)≤Ymax) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,DescentWeightedCauchy.firstElementRowMap
        (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
          b.cube.leftBit b.cube.rightBit) x∈T b) →
      (∀ b∈blocks,∀ z∈T b,z≠0) →
      (∀ b∈blocks,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤
        globalFirstPooledRow p K ell B F true (b.withCommon ∅)) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,canonicalCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      C*Ymax^deltaLoss*
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F true b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)) *
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F false b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)) := by
  obtain ⟨C,hC,hfirst⟩ := first_passage_full_uniform_input_family W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ J deltaLoss hδ
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ K ell B F Ymax hK hell hB hF hΨ₁ hΨ₂ hw ha hYmax hsf hs0 hmap hT0 hT
  by_cases hempty : blocks=∅
  · subst blocks
    simp only [Finset.sum_empty,mul_zero,norm_zero,Real.sqrt_zero,le_refl]
  have hne : blocks.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  let E₁ := fun b => globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)
  let E₂ := fun b => globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)
  let v := fun b => w b*globalCubeCoefficient p K ell B F true b
  have hv (b) (hb : b∈blocks) : 0≤v b := mul_nonneg (hw b hb)
    (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _)
  have hE₁ (b) : 0≤E₁ b := firstInputFamilyEnergy_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hE₂ (b) : 0≤E₂ b := firstInputFamilyEnergy_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hden : 0<ell*B^2*F := by positivity
  have hYmax0 : 0≤Ymax := by
    obtain ⟨b,hb⟩ := hne
    exact (globalPooledRowScale_pos K ell B F hK hell hB hF _).le.trans (hYmax b hb)
  have hpref : 0≤C*Ymax^deltaLoss := mul_nonneg hC (Real.rpow_nonneg hYmax0 deltaLoss)
  have hpoint (b) (hb : b∈blocks) : (ell*B^2*F)⁻¹*
      ‖canonicalCubeFirstBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      (C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
    have hFB : Disjoint (globalCubePool pool b) b.cube.support := by
      apply Finset.disjoint_left.mpr
      intro i hi hiB
      exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hiB)
    have hX₁ := globalCubeColumnScale_pos p hp ell hell true b
    have hX₂ := globalCubeColumnScale_pos p hp ell hell false b
    have hD := FirstPassCubeLabels.primeProductNorm_pos p hp b.firstDivisor
    have hY := globalPooledRowScale_pos K ell B F hK hell hB hF (globalFirstIndex p true (b.withCommon ∅))
    have hh := hfirst p hp hinj hcop hg hc hpr (globalCubePool pool b) b.cube.support hFB
      (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit b.cube.support_pos
      Ψ₁ Ψ₂ m₁ m₂ (fun A => g₁ (columnLog p (globalCubeColumnScale p ell true b) A))
      (fun A => g₂ (columnLog p (globalCubeColumnScale p ell false b) A))
      (fun A hA => hΨ₁ _) (fun A hA => hΨ₂ _)
      _ _ hX₁ hX₂ K hK (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) (primeSubsetGenerator_ne_zero _ _)
      (s b) (T b) (a b) (w b) (globalFirstPooledRow p K ell B F true (b.withCommon ∅))
      (hw b hb) hY.le (hsf b hb) (hs0 b hb) (hmap b hb) (hT0 b hb) (hT b hb) (ha b hb)
    have hscl := globalCube_first_scalar_bound p hp K ell B F hK hell hB hF b
    have hpow := Real.rpow_le_rpow hY.le (hYmax b hb) hδ.le
    have hmul := mul_le_mul_of_nonneg_left hh
      (show 0≤(ell*B^2*F)⁻¹*(primeProductNorm p b.firstDivisor)⁻¹ by positivity)
    simp only [canonicalCubeFirstBlock,norm_mul,norm_inv,Complex.norm_real,
      Real.norm_of_nonneg hD.le,←mul_assoc]
    apply hmul.trans
    calc
      _ = ((ell*B^2*F)⁻¹*((K/primeProductNorm p b.firstDivisor)/
          ‖eisEmbedding (∏ i∈cubeActiveSupport b.cube.support
            (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖))*
          (w b*C*(globalFirstPooledRow p K ell B F true (b.withCommon ∅))^deltaLoss)*
          (Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by dsimp [E₁,E₂,globalCubeInputFamilyEnergy];ring
      _ ≤ globalCubeCoefficient p K ell B F true b*(w b*C*Ymax^deltaLoss)*
          (Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        apply mul_le_mul hscl
          (mul_le_mul_of_nonneg_left hpow (mul_nonneg (hw b hb) hC))
          (mul_nonneg (mul_nonneg (hw b hb) hC) (Real.rpow_nonneg hY.le _))
          (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _)
      _ = _ := by dsimp [v];ring
  rw [norm_mul, norm_inv]
  have hn : ‖(ell*B^2*F : ℂ)‖=ell*B^2*F := by
    norm_cast
    exact abs_of_pos hden
  rw [hn]
  calc
    _ ≤ (ell*B^2*F)⁻¹*∑ b∈blocks,‖canonicalCubeFirstBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hden.le)
    _ ≤ ∑ b∈blocks,(C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hpoint
    _ = (C*Ymax^deltaLoss)*∑ b∈blocks,Real.sqrt (v b*E₁ b)*Real.sqrt (v b*E₂ b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Real.sqrt_mul (hv b hb),Real.sqrt_mul (hv b hb)]
      have hs := Real.sq_sqrt (hv b hb)
      calc
        _ = (C*Ymax^deltaLoss)*(Real.sqrt (v b))^2*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by rw [hs]
        _ = _ := by ring
    _ ≤ (C*Ymax^deltaLoss)*(Real.sqrt (∑ b∈blocks,v b*E₁ b)*Real.sqrt (∑ b∈blocks,v b*E₂ b)) :=
      mul_le_mul_of_nonneg_left (by
        have hcauchy := Real.sum_sqrt_mul_sqrt_le blocks.attach
          (fun b => mul_nonneg (hv b.val b.property) (hE₁ b.val))
          (fun b => mul_nonneg (hv b.val b.property) (hE₂ b.val))
        simpa only [Finset.sum_attach (f := fun b => Real.sqrt (v b*E₁ b)*Real.sqrt (v b*E₂ b)),
          Finset.sum_attach (f := fun b => v b*E₁ b),Finset.sum_attach (f := fun b => v b*E₂ b)] using hcauchy) hpref
    _ = _ := by simp only [v,E₁,E₂,globalCubeCoefficient_side,mul_assoc]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

theorem canonicalTwoPassage_quantitative
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀ t,g₁ t≠0 → |t|≤M₁) (hg₂ : ∀ t,g₂ t≠0 → |t|≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤N₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤N₂)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃ (windows₁ windows₂ : Fin 7 → ℝ → ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
      (∀ i,HasCompactSupport (windows₁ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀ i t,windows₁ i t≠0 → |t|≤M₁+6+1) ∧
      (∀ i,HasCompactSupport (windows₂ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀ i t,windows₂ i t≠0 → |t|≤M₂+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (Γ K ell B F H U : ℝ),
      0≤Γ → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U → ell*Real.exp M₁≤U → ell*Real.exp M₂≤U →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b ∧ w b≤Γ) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,GlobalCubeAdmissible b) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,(Ideal.absNorm x.1 : ℝ)≤F) →
      (∀ b∈blocks,∀ x∈s b,‖eisEmbedding x.2‖^2≤globalFirstFrequencyScale p K ell b) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,canonicalCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₁ m₁ windows₁ C₁ Cd₁ Ct₁ Γ ε K ell B F M₁ H U A J N true) *
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₂ m₂ windows₂ C₂ Cd₂ Ct₂ Γ ε K ell B F M₂ H U A J N false) := by
  obtain ⟨Cfirst,hCfirst,hfirst⟩ := canonicalCubeFirstBlock_input_transfer W V₁ V₂ N₁ N₂ hN₁ hN₂ hV₁ hV₂ (2*(J+2)) deltaLoss hδ
  obtain ⟨windows₁,C₁,Cd₁,Ct₁,hC₁,hCd₁,hCt₁,hwc₁,hws₁,hwb₁,hleft⟩ :=
    globalCubeInputFamilyEnergy_quantitative ε hε g₁ V₁ M₁ hM₁ hg₁ true A J N
  obtain ⟨windows₂,C₂,Cd₂,Ct₂,hC₂,hCd₂,hCt₂,hwc₂,hws₂,hwb₂,hright⟩ :=
    globalCubeInputFamilyEnergy_quantitative ε hε g₂ V₂ M₂ hM₂ hg₂ false A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCfirst,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w Ψ₁ Ψ₂ m₁ m₂ Γ K ell B F H U
    hΓ hK hell hB hF hH hU hellU1 hellU2 hΨ₁ hΨ₂ hw ha hadm hb₁ hb₂ hsf hs0 hf hh
  have hB0 : 0<B := by linarith
  let T := fun b => globalCubeFirstTargets p b (s b)
  have hT0 (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) : z≠0 :=
    globalCubeFirstTargets_ne_zero p hp b (s b) (hsf b hb) (hs0 b hb) z hz
  have hT (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) :
      (Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F true (b.withCommon ∅) :=
    globalCubeFirstTargets_norm_bound p hp b (s b) K ell B F hK hell hB0 hF
      (hb₁ b hb) (hb₂ b hb) (hf b hb) (hh b hb) z hz
  have hTc (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) :
      (Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F false (b.withCommon ∅) := by
    rw [globalFirstPooledRow_side]
    exact hT b hb z hz
  have hblock := hfirst p hp hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ K ell B F
    (globalFirstRowCap K ell B F) hK hell hB0 hF hΨ₁ hΨ₂ (fun b hb => (hw b hb).1) ha
    (fun b hb => globalFirstPooledRow_le_cap p hp K ell B F hK hell hB0 hF b (hadm b hb) (hb₁ b hb) (hb₂ b hb))
    hsf hs0 (fun b _ x hx => globalCubeFirstTargets_mem p b (s b) x hx) hT0 hT
  have hl := hleft p hp hcop hg hinj hc hpr pool blocks w Γ K ell B F H U Ψ₁ m₁ T
    hΓ hw hK hell hB hF hH hU hellU1 hadm hΨ₁ hb₁ hb₂ hT hT0
  have hr := hright p hp hcop hg hinj hc hpr pool blocks w Γ K ell B F H U Ψ₂ m₂ T
    hΓ hw hK hell hB hF hH hU hellU2 hadm hΨ₂ hb₁ hb₂ hTc hT0
  have hprefix : 0≤Cfirst*(globalFirstRowCap K ell B F)^deltaLoss :=
    mul_nonneg hCfirst (Real.rpow_nonneg (globalFirstRowCap_pos K ell B F hK hell hB0 hF).le _)
  exact hblock.trans (mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hl) hprefix)
    (Real.sqrt_le_sqrt hr) (Real.sqrt_nonneg _) (mul_nonneg hprefix (Real.sqrt_nonneg _)))

end SecondPassArithmetic

open scoped BigOperators Classical
namespace CompletedGauss

section
open ActualEisensteinCubic IdealMobiusDivisorSum UniqueFactorizationMonoid

theorem completed_branch_count_small_power (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(I : Ideal O),I≠0 → ∀{ι : Type*} [Fintype ι]
      (P : ι→Ideal O) [∀i,(P i).IsMaximal],Function.Injective P →
      (∀i,P i∣I) → (6:ℝ)^(2*Fintype.card ι)≤C*(Ideal.absNorm I:ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := SquarefreeDivisorBound.prime_support_subsets_bound (ε/6) (by positivity)
  refine ⟨C^6,by positivity,?_⟩
  intro I hI ι _ P _ hinj hd
  let f : ι→primeSupport I := fun i => ⟨P i,by
    change P i∈(normalizedFactors I).toFinset
    exact Multiset.mem_toFinset.mpr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr
      ⟨Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance,hd i⟩)⟩
  have hfi : Function.Injective f := by
    intro i j hij
    exact hinj (congrArg Subtype.val hij)
  have hcard : Fintype.card ι≤(primeSupport I).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hfi
  have htwo : (2:ℝ)^Fintype.card ι≤C*(Ideal.absNorm I:ℝ)^(ε/6) :=
    (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hcard).trans (hbound I hI)
  have hn : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  calc
    _ = (36:ℝ)^Fintype.card ι := by rw [pow_mul]; norm_num
    _ ≤ (64:ℝ)^Fintype.card ι := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = ((2:ℝ)^Fintype.card ι)^6 := by rw [←pow_mul, Nat.mul_comm, pow_mul]; norm_num
    _ ≤ (C*(Ideal.absNorm I:ℝ)^(ε/6))^6 := pow_le_pow_left₀ (by positivity) htwo 6
    _ = C^6*(Ideal.absNorm I:ℝ)^ε := by
      rw [mul_pow,←Real.rpow_mul_natCast hn.le]
      congr 2
      ring

end

open ActualEisensteinCubic CanonicalQuadraticSieve IdealMobiusDivisorSum

theorem sum_completedRowFibers (S : Finset (Ideal O)) (Q : Ideal O) (f : Ideal O→ℝ) :
    (∑A∈S.image rowPowerfulPart,∑T∈S.image (fun I => rowMaskPart I Q),
      ∑I∈completedRowFiber S Q A T,f I)=∑I∈S,f I := by
  let mapPair : Ideal O→Ideal O×Ideal O := fun I => (rowPowerfulPart I,rowMaskPart I Q)
  have hm : ∀I∈S,mapPair I∈(S.image rowPowerfulPart)×ˢ(S.image (fun J => rowMaskPart J Q)) := by
    intro I hI
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hI,Finset.mem_image_of_mem _ hI⟩
  have hh := Finset.sum_fiberwise_of_maps_to hm f
  rw [Finset.sum_product] at hh
  simpa only [mapPair,Prod.mk.injEq,completedRowFiber] using hh

theorem rowMaskPart_image_card (S : Finset (Ideal O)) (Q : Ideal O) (hQ : Q≠0) :
    (S.image (fun I => rowMaskPart I Q)).card≤(idealDivisors Q).card := by
  apply Finset.card_le_card
  intro T hT
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hT
  exact (mem_idealDivisors hQ).mpr (rowMaskPart_dvd I Q)

theorem completed_outer_row_sum_bound (S : Finset (Ideal O)) (Q : Ideal O) (hQ : Q≠0)
    (f : Ideal O→ℝ) (C : ℝ) (hC : 0≤C)
    (hblocks : ∀A∈S.image rowPowerfulPart,∀T∈S.image (fun I => rowMaskPart I Q),
      (∑I∈completedRowFiber S Q A T,f I)≤C/(Ideal.absNorm A:ℝ)) :
    (∑I∈S,f I)≤1048576*((idealDivisors Q).card:ℝ)*C := by
  rw [←sum_completedRowFibers S Q f]
  calc
    _ ≤ ∑A∈S.image rowPowerfulPart,∑T∈S.image (fun I => rowMaskPart I Q),C/(Ideal.absNorm A:ℝ) := by
      apply Finset.sum_le_sum
      intro A hA
      exact Finset.sum_le_sum (fun T hT => hblocks A hA T hT)
    _ = ((S.image (fun I => rowMaskPart I Q)).card:ℝ)*C*
        ∑A∈S.image rowPowerfulPart,1/(Ideal.absNorm A:ℝ) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A hA
      ring
    _ ≤ ((S.image (fun I => rowMaskPart I Q)).card:ℝ)*C*1048576 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply powerful_inverse_norm_sum
      intro A hA
      obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hA
      exact rowPowerfulPart_powerful I
    _ ≤ ((idealDivisors Q).card:ℝ)*C*1048576 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (rowMaskPart_image_card S Q hQ)) hC) (by norm_num)
    _ = _ := by ring

theorem completed_outer_row_small_power (ε : ℝ) (hε : 0<ε) :
    ∃D : ℝ,0<D ∧ ∀(S : Finset (Ideal O)) (Q : Ideal O),Q≠0 →
      ∀(f : Ideal O→ℝ) (C : ℝ),0≤C →
      (∀A∈S.image rowPowerfulPart,∀T∈S.image (fun I => rowMaskPart I Q),
        (∑I∈completedRowFiber S Q A T,f I)≤C/(Ideal.absNorm A:ℝ)) →
      (∑I∈S,f I)≤D*(Ideal.absNorm Q:ℝ)^ε*C := by
  obtain ⟨D,hD,hbound⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨1048576*D,by positivity,?_⟩
  intro S Q hQ f C hC hblocks
  apply (completed_outer_row_sum_bound S Q hQ f C hC hblocks).trans
  have hh := mul_le_mul_of_nonneg_right (hbound Q hQ) hC
  nlinarith

end CompletedGauss

open scoped BigOperators
namespace CompletedDyadic

def kernelTerm (t s A : ℝ) (n : ℕ) : ℝ := ((2:ℝ)^n)^s/(1+t*(2:ℝ)^n)^A

theorem pow_rpow_comm (s : ℝ) (n : ℕ) : ((2:ℝ)^n)^s=((2:ℝ)^s)^n := by
  rw [←Real.rpow_natCast_mul (by norm_num),←Real.rpow_mul_natCast (by norm_num)]
  congr 1
  ring

theorem kernelTerm_nonneg (t s A : ℝ) (ht : 0<t) (n : ℕ) : 0≤kernelTerm t s A n := by
  unfold kernelTerm
  positivity

theorem kernelTerm_le_head (t s A : ℝ) (ht : 0<t) (hA : 0≤A) (n : ℕ) :
    kernelTerm t s A n≤((2:ℝ)^s)^n := by
  rw [kernelTerm,←pow_rpow_comm]
  exact div_le_self (Real.rpow_nonneg (by positivity) _)
    (Real.one_le_rpow (by nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n]) hA)

theorem kernelTerm_le_tail (t s A : ℝ) (ht : 0<t) (hA : 0≤A) (n : ℕ) :
    kernelTerm t s A n≤t^(-A)*((2:ℝ)^(s-A))^n := by
  have hn : 0<(2:ℝ)^n := by positivity
  have htA : 0<t^A := Real.rpow_pos_of_pos ht _
  calc
    _ ≤ ((2:ℝ)^n)^s/(t*(2:ℝ)^n)^A := by
      unfold kernelTerm
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (Real.rpow_le_rpow (by positivity) (by linarith) hA)
    _ = t^(-A)*(((2:ℝ)^n)^s/((2:ℝ)^n)^A) := by
      rw [Real.mul_rpow ht.le hn.le,Real.rpow_neg ht.le]
      ring
    _ = _ := by rw [←Real.rpow_sub hn,pow_rpow_comm]

theorem ratio_lt_one (s A : ℝ) (hsA : s<A) : (2:ℝ)^(s-A)<1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hsA)

theorem kernel_summable (t s A : ℝ) (ht : 0<t) (hA : 0≤A) (hsA : s<A) :
    Summable (kernelTerm t s A) := by
  have hq := summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (s-A)) (ratio_lt_one s A hsA)
  exact (hq.mul_left (t^(-A))).of_nonneg_of_le (kernelTerm_nonneg t s A ht) (kernelTerm_le_tail t s A ht hA)

theorem kernel_sum_cutoff (t s A : ℝ) (ht : 0<t) (hs : 0<s) (hsA : s<A) (N : ℕ) :
    (∑'n : ℕ,kernelTerm t s A n)≤
      ((2:ℝ)^s)^N/((2:ℝ)^s-1)+t^(-A)*((2:ℝ)^(s-A))^N/(1-(2:ℝ)^(s-A)) := by
  have hA : 0≤A := by linarith
  have hp : 1<(2:ℝ)^s := Real.one_lt_rpow (by norm_num) hs
  have hq : (2:ℝ)^(s-A)<1 := ratio_lt_one s A hsA
  have hq0 : 0≤(2:ℝ)^(s-A) := by positivity
  have hsum := kernel_summable t s A ht hA hsA
  have hhead : (∑n∈Finset.range N,kernelTerm t s A n)≤((2:ℝ)^s)^N/((2:ℝ)^s-1) := by
    apply (Finset.sum_le_sum (fun n _ => kernelTerm_le_head t s A ht hA n)).trans
    rw [geom_sum_eq hp.ne']
    exact div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr hp.le)
  have htail : (∑'n : ℕ,kernelTerm t s A (n+N))≤
      t^(-A)*((2:ℝ)^(s-A))^N/(1-(2:ℝ)^(s-A)) := by
    have hgeo := (summable_geometric_of_lt_one hq0 hq).mul_left (t^(-A)*((2:ℝ)^(s-A))^N)
    have hb := Summable.tsum_le_tsum (fun n => show kernelTerm t s A (n+N)≤
      (t^(-A)*((2:ℝ)^(s-A))^N)*((2:ℝ)^(s-A))^n by
        simpa only [pow_add,mul_assoc,mul_left_comm,mul_comm] using kernelTerm_le_tail t s A ht hA (n+N))
      ((summable_nat_add_iff N).mpr hsum) hgeo
    rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq] at hb
    simpa only [div_eq_mul_inv] using hb
  rw [←hsum.sum_add_tsum_nat_add N]
  exact add_le_add hhead htail

theorem kernel_sum_bound (s A : ℝ) (hs : 0<s) (hsA : s<A) :
    ∃C : ℝ,0<C ∧ ∀t : ℝ,0<t →
      Summable (kernelTerm t s A) ∧ (∑'n : ℕ,kernelTerm t s A n)≤C*t^(-s) := by
  let r : ℝ := (2:ℝ)^s
  let q : ℝ := (2:ℝ)^(s-A)
  have hr : 1<r := Real.one_lt_rpow (by norm_num) hs
  have hq : q<1 := ratio_lt_one s A hsA
  have hq0 : 0≤q := by dsimp [q]; positivity
  let C := r/(r-1)+1/(1-q)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro t ht
  have hA : 0≤A := by linarith
  have hsum := kernel_summable t s A ht hA hsA
  refine ⟨hsum,?_⟩
  by_cases ht1 : 1≤t
  · have hg := (summable_geometric_of_lt_one hq0 hq).mul_left (t^(-A))
    have hb := hsum.tsum_le_tsum (fun n => kernelTerm_le_tail t s A ht hA n) hg
    change (∑'n : ℕ,kernelTerm t s A n)≤∑'n : ℕ,t^(-A)*q^n at hb
    rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq] at hb
    calc
      _ ≤ t^(-A)/(1-q) := by simpa only [div_eq_mul_inv] using hb
      _ ≤ t^(-s)/(1-q) := div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)) (by linarith)
      _ ≤ C*t^(-s) := by
        have hp : 0≤r/(r-1)*t^(-s) := by positivity
        calc
          _ ≤ r/(r-1)*t^(-s)+t^(-s)/(1-q) := le_add_of_nonneg_left hp
          _ = C*t^(-s) := by dsimp [C]; ring
  · have ht_le : t≤1 := le_of_not_ge ht1
    have hit : 1≤1/t := (one_le_div ht).mpr ht_le
    obtain ⟨N,hN,hN'⟩ := exists_nat_pow_near hit (by norm_num : (1:ℝ)<2)
    have hheadpow : r^(N+1)≤r*t^(-s) := by
      change ((2:ℝ)^s)^(N+1)≤(2:ℝ)^s*t^(-s)
      rw [←pow_rpow_comm]
      calc
        _ ≤ ((2:ℝ)/t)^s := by
          apply Real.rpow_le_rpow (by positivity) _ hs.le
          rw [pow_succ]
          calc
            _ ≤ (1/t)*2 := mul_le_mul_of_nonneg_right hN (by norm_num)
            _ = 2/t := by ring
        _ = _ := by rw [Real.div_rpow (by norm_num) ht.le,Real.rpow_neg ht.le]; ring
    have htailpow : t^(-A)*q^(N+1)≤t^(-s) := by
      change t^(-A)*((2:ℝ)^(s-A))^(N+1)≤t^(-s)
      rw [←pow_rpow_comm]
      calc
        _ ≤ t^(-A)*(1/t)^(s-A) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by positivity) hN'.le (by linarith)) (by positivity)
        _ = t^(-A)*t^(-(s-A)) := by rw [one_div,Real.inv_rpow ht.le,←Real.rpow_neg ht.le]
        _ = t^(-s) := by rw [←Real.rpow_add ht]; congr 1; ring
    have hb := kernel_sum_cutoff t s A ht hs hsA (N+1)
    change (∑'n : ℕ,kernelTerm t s A n)≤r^(N+1)/(r-1)+t^(-A)*q^(N+1)/(1-q) at hb
    calc
      _ ≤ r^(N+1)/(r-1)+t^(-A)*q^(N+1)/(1-q) := hb
      _ ≤ (r*t^(-s))/(r-1)+t^(-s)/(1-q) := add_le_add
        (div_le_div_of_nonneg_right hheadpow (by linarith))
        (div_le_div_of_nonneg_right htailpow (by linarith))
      _ = C*t^(-s) := by dsimp [C]; ring

end CompletedDyadic

end

end OAI
end OAIOriginalModule0203

/-! Original module: OAI.NumberTheory.DirichletL.MeanSquare.OutsideIdeals
Source SHA256: 8a82948b64d0b417b5b1c2287bcf7d848a5a00c2187dc767767b5db5c63a340c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0204


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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)

theorem idealRowSum_filter_squarefree (F : Finset (Ideal O))
    (hFp : ∀ I ∈ F, I ≠ ⊥)
    (hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
      goodLambda ∉ P) {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (z : O) :
    idealRowSum F hFp hFg χ W z =
    idealRowSum (F.filter Squarefree)
      (fun I hI => hFp I (Finset.mem_filter.mp hI).1)
      (fun I hI => hFg I (Finset.mem_filter.mp hI).1) χ W z := by
  unfold idealRowSum
  calc
    _ = ∑ I ∈ F.filter Squarefree,
        ShortDraftHeckeBridge.baseChangeWeight χ I * W (Ideal.absNorm I) *
          idealSexticRow F hFp hFg I z := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro I hIF hIn
      have hs : ¬ Squarefree I := fun h => hIn (Finset.mem_filter.mpr ⟨hIF,h⟩)
      rw [baseChangeWeight_zero_of_not_squarefree χ I hs, zero_mul, zero_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [idealSexticRow_ambient F (F.filter Squarefree) hFp
        (fun J hJ => hFp J (Finset.mem_filter.mp hJ).1) hFg
        (fun J hJ => hFg J (Finset.mem_filter.mp hJ).1) I
        (Finset.mem_filter.mp hI).1 hI z]

def outsideSquarefreeIdeals (S : Finset (Ideal O)) (D : ℕ) : Finset (Ideal O) :=
  (outsideIdealsUpTo S D).filter Squarefree

theorem outsideSquarefree_admissible (S : Finset (Ideal O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) : ∀ I ∈ outsideSquarefreeIdeals S D, Admissible I := by
  intro I hI
  obtain ⟨ho,hs⟩ := Finset.mem_filter.mp hI
  have hn := outsideIdealsUpTo_ne_bot S D I ho
  refine ⟨hn,hs,?_⟩
  intro P hP
  obtain ⟨hp,hd⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mp hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  apply (prime_good_iff_not_bad P).mpr
  intro hPb
  exact (mem_outsideIdealsUpTo.mp ho).2.2 P (hbad hPb) hd

theorem outside_good (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S) :
    ∀ I ∈ outsideIdealsUpTo S D,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P := by
  apply outsideIdealsUpTo_good S D
  apply badPrime_cover_of_lambdaIdeal_mem
  exact hbad (Finset.mem_insert_self _ _)

theorem outside_pool_product_not_dvd (S : Finset (Ideal O)) (D : ℕ)
    (hSp : ∀ P ∈ S, Prime P) (T : Finset (primePool (outsideSquarefreeIdeals S D))) :
    ∀ P ∈ S, ¬ P ∣ ∏ i ∈ T,i.val := by
  intro P hPS hdiv
  obtain ⟨i,hi,hPi⟩ := ((hSp P hPS).dvd_finsetProd_iff
    (fun i : primePool (outsideSquarefreeIdeals S D) => i.val)).mp hdiv
  obtain ⟨I,hIF,hiI⟩ := mem_primePool_iff.mp i.property
  have ho : I ∈ outsideIdealsUpTo S D := (Finset.mem_filter.mp hIF).1
  have hn := outsideIdealsUpTo_ne_bot S D I ho
  have hd : i.val ∣ I := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mp hiI |>.2
  exact (mem_outsideIdealsUpTo.mp ho).2.2 P hPS (hPi.trans hd)

theorem selectedIdealTest_outside (S : Finset (Ideal O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀ P ∈ S, Prime P)
    (W : ℝ → ℂ) (b Z : ℝ) (hZ : 0 < Z)
    (hs : ∀ t, W t ≠ 0 → t ≤ b) (hD : b*Z ≤ D)
    (T : Finset (primePool (outsideSquarefreeIdeals S D))) :
    selectedIdealTest (outsideSquarefreeIdeals S D) (fun n => W (n/Z)) T =
    W (primeProductNorm (poolPrimary (outsideSquarefreeIdeals S D)) T/Z) := by
  let F := outsideSquarefreeIdeals S D
  have hF := outsideSquarefree_admissible S D hbad
  rw [poolPrimary_norm F hF T]
  unfold selectedIdealTest
  by_cases hw : W ((Ideal.absNorm (∏ i ∈ T,i.val) : ℝ)/Z)=0
  · split_ifs
    · rfl
    · exact hw.symm
  · rw [ite_eq_left]
    have ha := poolProduct_admissible F hF T
    apply Finset.mem_filter.mpr
    refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,?_,outside_pool_product_not_dvd S D hSp T⟩,ha.2.1⟩
    · exact Nat.one_le_iff_ne_zero.mpr (fun hz => ha.1 (Ideal.absNorm_eq_zero_iff.mp hz))
    · exact_mod_cast ((div_le_iff₀ hZ).mp (hs _ hw)).trans hD

theorem outside_idealRowSum_initial_energy {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (W : ℝ → ℂ) (a b Z : ℝ) (ha : 0 < a) (hZ : 0 < Z)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hD : b*Z ≤ D) (z : O) :
    let F := outsideSquarefreeIdeals S D
    let hF := outsideSquarefree_admissible S D hbad
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    ‖idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
      (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2/Z =
    ‖mobiusRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ (normCharacter χ) 1
      (normalizedColumn (poolPrimary F)
        (fun T => initialLogProfile W a b ha hs hW (columnLog (poolPrimary F) Z T))) z‖^2 := by
  dsimp only
  let F := outsideSquarefreeIdeals S D
  have hF := outsideSquarefree_admissible S D hbad
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  rw [idealRowSum_filter_squarefree]
  change ‖idealRowSum F (fun I hI => (hF I hI).1)
    (fun I hI P hP => ((hF I hI).2.2 P hP).1) χ (fun n => W (n/Z)) z‖^2/Z = _
  rw [idealRowSum_eq_mobiusRow F hF]
  have ht : selectedIdealTest F (fun n => W (n/Z)) =
      fun T => W (primeProductNorm (poolPrimary F) T/Z) := by
    funext T
    exact selectedIdealTest_outside S D hbad hSp W b Z hZ (fun t ht => (hs ht).2) hD T
  rw [ht]
  exact (mobiusRow_initial_energy (poolPrimary F) (poolPrimary_good F hF)
    (poolPrimary_ne_zero F hF) Finset.univ (normCharacter χ) 1 z Z hZ W a b ha hs hW).symm

end InitialMeanSquare

end

end OAI
end OAIOriginalModule0204

/-! Original module: OAI.NumberTheory.DirichletL.MeanSquare.PoissonSource
Source SHA256: bc07cdfc3e24fef666e5ee885ba84c53cdf60b4d1d7294fee4fc0eb40dfa39ca
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0205


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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace InitialMeanSquare

section
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic
open FirstPassCubeLabels (normalizedColumn columnLog)

theorem outside_mean_square_source {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (W : ℝ → ℂ) (a b Z Y : ℝ)
    (ha : 0 < a) (hZ : 0 < Z) (hY : 0 < Y)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hD : b*Z ≤ D) (T : Finset O)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y)
    (hT0 : ∀ z ∈ T, z ≠ 0)
    (K : Finset (primePool (outsideSquarefreeIdeals S D)) →
      Finset (primePool (outsideSquarefreeIdeals S D)) → Finset O) :
    let F := outsideSquarefreeIdeals S D
    let hF := outsideSquarefree_admissible S D hbad
    let p := poolPrimary F
    let hp := poolPrimary_ne_zero F hF
    let hg := poolPrimary_good F hF
    letI : ∀ i : primePool F, (Ideal.span {p i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let hinj : Function.Injective (fun i : primePool F => Ideal.span {p i}) := by
      intro i j hij
      apply Subtype.ext
      simpa only [p, poolPrimary_span F hF] using hij
    let G := normalizedColumn p (fun V => initialLogProfile W a b ha hs hW (columnLog p Z V))
    let Ψ := conjugateMonoid (normCharacter χ)
    (∑ z ∈ T, ‖idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
      (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2)/Z ≤
      ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1
        (fun V => star (G V)) rowMajorant Y (fun C E => (K C E).erase 0)‖+
      (truncatedSecondZero p hg Finset.univ Ψ 1 1 1
        (fun V => star (G V)) rowMajorant Y K).re+
      ‖secondSourceTail p hp hg hinj Finset.univ Ψ 1 1 1
        (fun V => star (G V)) rowMajorant Y K‖-‖G ∅‖^2 := by
  dsimp only
  let F := outsideSquarefreeIdeals S D
  have hF := outsideSquarefree_admissible S D hbad
  let p := poolPrimary F
  let hp := poolPrimary_ne_zero F hF
  let hg := poolPrimary_good F hF
  let : ∀ i : primePool F, (Ideal.span {p i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have hinj : Function.Injective (fun i : primePool F => Ideal.span {p i}) := by
    intro i j hij
    apply Subtype.ext
    simpa only [p, poolPrimary_span F hF] using hij
  let G := normalizedColumn p (fun V => initialLogProfile W a b ha hs hW (columnLog p Z V))
  have he := mobiusRow_finite_source p hg hp hinj (poolPrimary_odd F hF) Finset.univ
    (normCharacter χ) 1 G Y hY T hT hT0 K
  calc
    _ = ∑ z ∈ T, ‖mobiusRow p hg Finset.univ (normCharacter χ) 1 G z‖^2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro z hz
      exact outside_idealRowSum_initial_energy χ S D hbad hSp W a b Z ha hZ hs hW hD z
    _ ≤ _ := he

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma initial_actual_row_norm (x : SecondExpansionData ι) :
    ‖eisEmbedding (actualSecondRow p ∅ x.divisor x.frequency)‖^2 =
      elementNorm (sourceObservation p x).1 := by
  simp only [actualSecondRow, sourceObservation, elementNorm,
    map_mul, norm_mul, mul_pow, primeSubsetGenerator_norm_eq_productNorm,
    primeProductNorm, Finset.prod_empty, map_one, norm_one, one_pow, one_mul]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma initialLogIndex_eq_second (x : SecondExpansionData ι) :
    initialLogIndex p x = secondLogIndex p ∅ x := by
  simp only [initialLogIndex, secondLogIndex, initial_actual_row_norm]

theorem initial_sector_coordinates (hp : ∀ i, p i ≠ 0)
    (F R : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (Z M : ℝ) (hZ : 0 < Z) (j : SecondLogIndex)
    (x : SecondExpansionData ι) (hx : x ∈ secondLogSector p ∅ F K R Z M j) :
    let X := initialLogColumn Z (primeProductNorm p R) j
    |sourceLogZ p Z X x| ≤ 2 ∧ |sourceLogE p (secondLogE j) x| ≤ 2 ∧
    |sourceLogV p (secondLogV j) x| ≤ 2 ∧ |sourceLogK p (secondLogK j) x| ≤ 2 := by
  obtain ⟨hx',hj⟩ := Finset.mem_filter.mp hx
  obtain ⟨hG,hE,hV,hk,hkf,hR,hs⟩ := secondSupportedSector_mem p F K R Z M x hx'
  have hsec := secondExpansionSector_valid p F (fun G E => (K G E).erase 0) R x
    (Finset.mem_filter.mp hx').1
  have heq : initialLogIndex p x=j := (initialLogIndex_eq_second p x).trans hj
  have hc := initial_log_coordinates p hp Z hZ x hE hk
  dsimp only at hc ⊢
  rw [heq,quotient_norm_fixed p _ x hsec] at hc
  simpa only [sourceLogZ, sourceLogE, sourceLogV, sourceLogK, elementNorm,
    primeSubsetGenerator_norm_eq_productNorm] using hc

end

theorem initial_bin_transfer
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A)
    (hU : ∀ t, g t ≠ 0 → U t=1) (hgA : ∀ t, g t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (N J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Cₛ : ℝ), 0 ≤ C ∧ 0 ≤ Cₛ ∧
      (∀ i, HasCompactSupport (windows i)) ∧ (∀ i, ContDiff ℝ ∞ (windows i)) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀ i, lambda ∉ Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
        (_hpr : ∀ i, lambda^2 ∣ p i-1)
        (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
        (K : Finset ι → Finset ι → Finset O) (Z H M : ℝ) (j : SecondLogIndex),
        0 < Z → 0 < H → (∀ a, ‖Ψ a‖ ≤ 1) →
        let s := secondLogSector p ∅ F K R Z M j
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
  obtain ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,ht⟩ :=
    initial_sector_transfer U hUc hUs g W A hA hU hgA ε hε N J
  refine ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F R Ψ m ray K Z H M j hZ hH hΨ
  dsimp only
  let s := secondLogSector p ∅ F K R Z M j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let X := initialLogColumn Z (primeProductNorm p R) j
  have hR : 0 < primeProductNorm p R := FirstPassCubeLabels.primeProductNorm_pos p hp R
  have hX : 0 < X := div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hR)
  have hs : ∀ x ∈ s, InSecondQuotientSector p r x := by
    intro x hx
    exact secondExpansionSector_valid p F (fun G E => (K G E).erase 0) R x
      (secondLogSector_subset p ∅ F K R Z M j hx)
  have hk : ∀ x ∈ s, x.frequency ≠ 0 := by
    intro x hx
    exact (secondSupportedSector_mem p F K R Z M x (Finset.mem_filter.mp hx).1).2.2.2.1
  have hcoords := initial_sector_coordinates p hp F R K Z M hZ j
  obtain ⟨B,hB,hdec,hbound⟩ := ht p hp hcop hg hinj hc hpr F Ψ m r ray s Z H
    (secondLogE j) (secondLogV j) X (secondLogK j) hZ hH
    (normLogScale_pos _) (normLogScale_pos _) hX (normLogScale_pos _) hΨ hs hk
    (fun x hx => (hcoords x hx).1) (fun x hx => (hcoords x hx).2.1)
    (fun x hx => (hcoords x hx).2.2.1) (fun x hx => (hcoords x hx).2.2.2)
  refine ⟨B,hB,?_,?_⟩
  · simpa only [X, initial_log_radial Z H (primeProductNorm p R) hZ.ne' hR.ne'] using hdec
  · simpa only [r, elementNorm, primeSubsetGenerator_norm_eq_productNorm] using hbound

end InitialMeanSquare

open scoped BigOperators
namespace FiniteOverlapDecomposition
variable {ι : Type*} [DecidableEq ι]

theorem sum_powerset_split {β : Type*} [AddCommMonoid β]
    (F B : Finset ι) (hB : B⊆F) (f : Finset ι→β) :
    (∑S∈F.powerset,f S)=∑A∈B.powerset,∑U∈(F\B).powerset,f (A∪U) := by
  have hsplit (S : Finset ι) : S∩B∪S\B=S := by
    ext i
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  have he : (∑S∈F.powerset,f S)=
      ∑AU∈B.powerset ×ˢ (F\B).powerset,f (AU.1∪AU.2) := by
    apply Finset.sum_bij (fun S _ => (S∩B,S\B))
    · intro S hS
      rw [Finset.mem_product,Finset.mem_powerset,Finset.mem_powerset]
      refine ⟨Finset.inter_subset_right,?_⟩
      intro i hi
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hS) (Finset.mem_sdiff.mp hi).1,(Finset.mem_sdiff.mp hi).2⟩
    · intro S hS T hT he
      have hi := congrArg (fun AU : Finset ι×Finset ι => AU.1∪AU.2) he
      simpa only [hsplit] using hi
    · intro AU hAU
      rcases Finset.mem_product.mp hAU with ⟨hA,hU⟩
      have hAB := Finset.mem_powerset.mp hA
      have hUFB := Finset.mem_powerset.mp hU
      refine ⟨AU.1∪AU.2,Finset.mem_powerset.mpr (Finset.union_subset (hAB.trans hB) (hUFB.trans Finset.sdiff_subset)),?_⟩
      apply Prod.ext <;> ext i
      · have h1 : i∈AU.1 → i∈B := fun hi => hAB hi
        have h2 : i∈AU.2 → i∉B := fun hi => (Finset.mem_sdiff.mp (hUFB hi)).2
        simp only [Finset.mem_inter,Finset.mem_union]
        tauto
      · have h1 : i∈AU.1 → i∈B := fun hi => hAB hi
        have h2 : i∈AU.2 → i∉B := fun hi => (Finset.mem_sdiff.mp (hUFB hi)).2
        simp only [Finset.mem_sdiff,Finset.mem_union]
        tauto
    · intro S hS
      rw [hsplit]
  simpa only [Finset.sum_product] using he

theorem sum_pair_split_cube {β : Type*} [AddCommMonoid β]
    (F B : Finset ι) (hB : B⊆F) (f : Finset ι→Finset ι→β) :
    (∑S∈F.powerset,∑T∈F.powerset,f S T)=
      ∑A₂∈B.powerset,∑A₁∈B.powerset,∑C∈(F\B).powerset,
        ∑N∈((F\B)\C).powerset,∑P∈((F\B)\C).powerset,
          if Disjoint N P then f ((A₂∪C)∪N) ((A₁∪C)∪P) else 0 := by
  rw [sum_powerset_split F B hB]
  apply Finset.sum_congr rfl
  intro A₂ hA₂
  simp_rw [sum_powerset_split F B hB]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A₁ hA₁
  rw [sum_pair_eq_overlap]
  simp only [Finset.union_assoc]

end FiniteOverlapDecomposition

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open MixedCrossSeparation (columnCoefficient)
open FirstPassCubeLabels

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda∉Ideal.span {p i})

def canonicalSourceCoefficient (Ψ : O→*ℂ) (m f : O)
    (H : Finset ι→ℂ) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S * Ψ (∏i∈S,p i) *
    rowCoprimeMask (fun i => Ideal.span {p i}) S m *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S f^4 * H S

theorem canonicalSourceCoefficient_union
    (hpr : ∀ i,lambda^2∣p i-1) (Ψ : O→*ℂ) (m f : O)
    (H : Finset ι→ℂ) (D S : Finset ι) (hd : Disjoint D S) :
    canonicalSourceCoefficient p hp hcop hg Ψ m f H (D∪S) =
      canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) D *
      (columnCoefficient p hp hcop hg S *
        multiplicativeCoreColumn p Ψ m (fun U => H (D∪U)) S *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (∏i∈D,p i)^4 *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S f^4) := by
  have hA := columnCoefficient_union_row_four p hp hcop hg hpr S D hd.symm
  rw [Finset.union_comm S D] at hA
  simp only [canonicalSourceCoefficient,hA,Finset.prod_union hd,map_mul,
    row_union _ hg D S hd,mask_union _ hg D S hd,mul_pow,multiplicativeCoreColumn]
  ring

theorem canonicalCube_pair_row
    (B C N P : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (hcover : ∀ i∈B,0<v₁ i+v₂ i)
    (hCB : Disjoint C B) (hNC : Disjoint N C) (hPC : Disjoint P C)
    (hNB : Disjoint N B) (hPB : Disjoint P B) (hNP : Disjoint N P)
    (z : O) :
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg
      (((B.filter fun i => ε₂ i)∪C)∪N) z) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg
        (((B.filter fun i => ε₁ i)∪C)∪P) z *
      star (multiplicityRow (fun i => Ideal.span {p i}) hg B v₂ z^3) *
      multiplicityRow (fun i => Ideal.span {p i}) hg B v₁ z^3 =
    rowCoprimeMask (fun i => Ideal.span {p i})
      (C∪cubePrincipalSupport B v₁ v₂ ε₁ ε₂) z *
    blockRow p hg ((N∪P)∪cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂)
      (threeBlockExponent N P (fun i => v₁ i+v₂ i) ε₁ ε₂) z := by
  have hA₁C : Disjoint (B.filter fun i => ε₁ i) C := hCB.symm.mono_left (Finset.filter_subset _ _)
  have hA₂C : Disjoint (B.filter fun i => ε₂ i) C := hCB.symm.mono_left (Finset.filter_subset _ _)
  have hA₁P : Disjoint (B.filter fun i => ε₁ i) P := hPB.symm.mono_left (Finset.filter_subset _ _)
  have hA₂N : Disjoint (B.filter fun i => ε₂ i) N := hNB.symm.mono_left (Finset.filter_subset _ _)
  have hCp : Disjoint C (cubePrincipalSupport B v₁ v₂ ε₁ ε₂) :=
    hCB.mono_right (Finset.filter_subset _ _)
  have hsel : cubePairRow (fun i => Ideal.span {p i}) hg B v₁ v₂ ε₁ ε₂ z =
      rowCoprimeMask (fun i => Ideal.span {p i}) (cubePrincipalSupport B v₁ v₂ ε₁ ε₂) z *
      blockRow p hg (cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂)
        (fun i => (conductorExponent (parity (v₁ i+v₂ i)) (ε₁ i) (ε₂ i)).val) z := by
    exact cubePairRow_conductor_selection (fun i => Ideal.span {p i}) hg B v₁ v₂ ε₁ ε₂
      (fun i hi => by have := hcover i hi;omega) z
  rw [row_union _ hg _ N (Finset.disjoint_union_left.mpr ⟨hA₂N,hNC.symm⟩),
    row_union _ hg _ P (Finset.disjoint_union_left.mpr ⟨hA₁P,hPC.symm⟩),
    row_union _ hg _ C hA₂C,row_union _ hg _ C hA₁C]
  simp only [star_mul]
  calc
    _ = (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg C z)*
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg C z)*
      (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N z)*
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P z)*
      cubePairRow (fun i => Ideal.span {p i}) hg B v₁ v₂ ε₁ ε₂ z := by
        simp only [cubePairRow];ring
    _ = _ := by
      rw [ActualEisensteinCubic.finiteSquarefreeRow_self_pair (fun i => Ideal.span {p i}) hg C z,
        hsel,
        threeBlockRow_factor p hg N P B hNP hNB hPB,
        mask_union _ hg C _ hCp]
      ring

theorem canonicalSourceCoefficient_cube_split
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i,lambda^2∣p i-1) (Ψ : O→*ℂ) (m f : O)
    (H : Finset ι→ℂ) (B C S : Finset ι) (ε₁ ε₂ : ι→Bool) (negative : Bool)
    (hCB : Disjoint C B) (hSC : Disjoint S C) (hSB : Disjoint S B) :
    let A := B.filter (fun i => if negative then ε₂ i else ε₁ i)
    canonicalSourceCoefficient p hp hcop hg Ψ m f H ((A∪C)∪S) =
      canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) (A∪C) *
      (columnCoefficient p hp hcop hg S *
        originalLabelColumn p hg B ε₁ ε₂ negative
          (multiplicativeCoreColumn p Ψ m (fun U => H ((A∪C)∪U)))
          (∏i∈C,p i) f S) := by
  dsimp only
  have hAC : Disjoint (B.filter fun i => if negative then ε₂ i else ε₁ i) C :=
    hCB.symm.mono_left (Finset.filter_subset _ _)
  have hAS : Disjoint (B.filter fun i => if negative then ε₂ i else ε₁ i) S :=
    hSB.symm.mono_left (Finset.filter_subset _ _)
  rw [canonicalSourceCoefficient_union p hp hcop hg hpr Ψ m f H _ S
    (Finset.disjoint_union_left.mpr ⟨hAS,hSC.symm⟩)]
  have hA : (∏i∈B.filter (fun i => if negative then ε₂ i else ε₁ i),p i) =
      aLabel p B (if negative then ε₂ else ε₁) := by
    cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,aLabel,primeProduct,
      Finset.prod_filter,bit]
    all_goals
      apply Finset.prod_congr rfl
      intro i hi
      split_ifs <;> simp_all
  rw [Finset.prod_union hAC,hA]
  simp only [originalLabelColumn,cubeRadical,commonProduct_mask p hg hinj S B,ite_eq_left hSB,mul_one]
  ring

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open MixedCrossSeparation (columnCoefficient columnPrimeCoprime)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def canonicalPairMode (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (d h : O) : ℂ :=
  (V₁ (columnLog p X₁ N)*V₂ (columnLog p X₂ P))*
    ((K:ℂ)/(‖eisEmbedding (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖:ℂ))*
    paperRadialFourier W (K*‖eisEmbedding h‖^2/
      (‖eisEmbedding d‖^2*primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h

lemma canonicalPairMode_summable (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) (d : O) (hd : d≠0) :
    Summable (canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d) := by
  let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
