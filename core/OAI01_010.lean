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

open scoped BigOperators Classical

namespace CompletedGauss

open ActualEisensteinCubic

def expandedTerm (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I H J : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ (H * J) *
    (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm H : ℝ) ^ 3 *
        (Ideal.absNorm J : ℝ) ^ 3 / X))

theorem finite_support_expandedTerm (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    (Function.support (fun p : Ideal O × Ideal O × Ideal O =>
      expandedTerm Ψ W X p.1 p.2.1 p.2.2)).Finite := by
  apply finite_support_norm_triple W hW X hX
  · intro I H J hz
    rcases hz with rfl | rfl | rfl <;> simp [expandedTerm]
  · intro I H J hw
    simp [expandedTerm, Vstar, hw]

theorem expandedTerm_scale (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I H J : Ideal O) :
    (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      summand Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) I J = expandedTerm Ψ W X I H J := by
  have harg : (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 /
      (X / (Ideal.absNorm H : ℝ) ^ 3) =
      (Ideal.absNorm I : ℝ) * (Ideal.absNorm H : ℝ) ^ 3 *
        (Ideal.absNorm J : ℝ) ^ 3 / X := by
    rw [div_div_eq_mul_div]
    ring
  simp only [summand, expandedTerm, harg, map_mul]
  ring

theorem expandedTerm_one (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) :
    expandedTerm Ψ W X I 1 J = summand Ψ W X I J := by
  simp only [expandedTerm, summand, UniqueFactorizationMonoid.moebius_one, Int.cast_one,
    one_mul, map_one, Nat.cast_one, one_pow, mul_one]
  ring

theorem completedT_finite_support (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    (Function.support (fun p : Ideal O × Ideal O => summand Ψ W X p.1 p.2)).Finite := by
  have hf := finite_support_expandedTerm Ψ W hW X hX
  have hinj : Function.Injective (fun p : Ideal O × Ideal O => (p.1, (1 : Ideal O), p.2)) := by
    intro a b hab
    exact Prod.ext (Prod.mk.inj hab).1 (Prod.mk.inj (Prod.mk.inj hab).2).2
  have hp := Set.Finite.preimage hinj.injOn hf
  change (Function.support (fun p : Ideal O × Ideal O => expandedTerm Ψ W X p.1 1 p.2)).Finite at hp
  simpa only [expandedTerm_one] using hp

theorem completedT_summable (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : Ideal O × Ideal O => summand Ψ W X p.1 p.2) :=
  summable_of_hasFiniteSupport (completedT_finite_support Ψ W hW X hX)

theorem weighted_completedT_reopen (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (H : Ideal O) :
    (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      completedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) =
      ∑' I : Ideal O, ∑' J : Ideal O, expandedTerm Ψ W X I H J := by
  simp only [completedT, ← tsum_mul_left, expandedTerm_scale]

theorem cube_inverse_finite_support (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    (Function.support (fun H : Ideal O =>
      (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
        completedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3))).Finite := by
  have hf := finite_support_expandedTerm Ψ W hW X hX
  apply (hf.image (fun p => p.2.1)).subset
  intro H hH
  by_contra hn
  have hzero : ∀ I J, expandedTerm Ψ W X I H J = 0 := by
    intro I J
    by_contra hz
    exact hn ⟨(I, H, J), hz, rfl⟩
  apply hH
  dsimp only
  rw [weighted_completedT_reopen]
  simp only [hzero, tsum_zero]

theorem cube_inner_inverse (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (I : Ideal O) :
    (∑' H : Ideal O, ∑' J : Ideal O, expandedTerm Ψ W X I H J) =
      columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
        Vstar W ((Ideal.absNorm I : ℝ) / X) := by
  let f : Ideal O → ℂ := fun B =>
    columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm B : ℝ) ^ 3 / X)
  have heq (H J : Ideal O) :
      (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ (H * J) * f (H * J) =
        expandedTerm Ψ W X I H J := by
    simp only [f, expandedTerm, map_mul, Nat.cast_mul, mul_pow, mul_assoc]
  have hf := finite_support_expandedTerm Ψ W hW X hX
  have hp : (Function.support (fun p : Ideal O × Ideal O => expandedTerm Ψ W X I p.1 p.2)).Finite := by
    change ((fun p : Ideal O × Ideal O => (I, p)) ⁻¹'
      Function.support (fun p : Ideal O × Ideal O × Ideal O =>
        expandedTerm Ψ W X p.1 p.2.1 p.2.2)).Finite
    exact Set.Finite.preimage (fun a _ b _ hab => (Prod.mk.inj hab).2) hf
  have hgeneric := ideal_cube_convolution (cubeWeight Ψ) (cubeWeight_zero Ψ) f
    (by simpa only [heq] using hp)
  simpa only [heq, f, map_one, Nat.cast_one, one_pow, mul_one] using hgeneric

theorem completed_cube_inverse_vstar (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    (∑' H : Ideal O, (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      completedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3)) =
    ∑' I : Ideal O, columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) / X) := by
  let F : Ideal O × Ideal O × Ideal O → ℂ := fun p => expandedTerm Ψ W X p.1 p.2.1 p.2.2
  have hF : Summable F := summable_of_hasFiniteSupport (finite_support_expandedTerm Ψ W hW X hX)
  let e : (Ideal O × Ideal O × Ideal O) ≃ (Ideal O × Ideal O × Ideal O) := {
    toFun := fun p => (p.2.1, p.1, p.2.2)
    invFun := fun p => (p.2.1, p.1, p.2.2)
    left_inv := by rintro ⟨I, H, J⟩; rfl
    right_inv := by rintro ⟨I, H, J⟩; rfl }
  have hswap : Summable (fun p => F (e p)) := e.summable_iff.mpr hF
  calc
    _ = ∑' H : Ideal O, ∑' I : Ideal O, ∑' J : Ideal O, expandedTerm Ψ W X I H J := by
      simp only [completedT, ← tsum_mul_left, expandedTerm_scale]
    _ = ∑' p : Ideal O × Ideal O × Ideal O, F (e p) := by
      rw [hswap.tsum_prod]
      apply tsum_congr
      intro H
      exact (hswap.prod_factor H).tsum_prod.symm
    _ = ∑' p : Ideal O × Ideal O × Ideal O, F p := e.tsum_eq F
    _ = ∑' I : Ideal O, ∑' H : Ideal O, ∑' J : Ideal O, expandedTerm Ψ W X I H J := by
      rw [hF.tsum_prod]
      apply tsum_congr
      intro I
      exact (hF.prod_factor I).tsum_prod
    _ = _ := tsum_congr (cube_inner_inverse Ψ W hW X hX)

theorem vstar_source_normalization (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (X : ℝ) (hX : 0 < X) (I : Ideal O) :
    columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) / X) =
      (Real.sqrt X : ℂ)⁻¹ * columnWeight Ψ I * W ((Ideal.absNorm I : ℝ) / X) := by
  by_cases hI : I = 0
  · subst I; simp
  have hN : (0 : ℝ) < Ideal.absNorm I := lt_of_lt_of_le zero_lt_one (norm_at_least_one I hI)
  have hsN : (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hN).ne'
  have hsX : (Real.sqrt X : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hX).ne'
  rw [Vstar, Real.sqrt_div hN.le, Complex.ofReal_div]
  field_simp

theorem completed_cube_inverse (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    (Real.sqrt X : ℂ)⁻¹ *
      (∑' I : Ideal O, columnWeight Ψ I * W ((Ideal.absNorm I : ℝ) / X)) =
    ∑' H : Ideal O, (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      completedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) := by
  rw [completed_cube_inverse_vstar Ψ W hW X hX, ← tsum_mul_left]
  apply tsum_congr
  intro I
  simpa only [mul_assoc] using (vstar_source_normalization Ψ W X hX I).symm

open ActualEisensteinCubic ConcreteTraceCRT

theorem normalizedFactors_product {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal] :
    UniqueFactorizationMonoid.normalizedFactors (Ideal.span {∏ i, p i}) =
      Finset.univ.val.map (fun i => Ideal.span {p i}) := by
  have hp (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne _) inferInstance
  have h := UniqueFactorizationMonoid.normalizedFactors_prod_of_prime
    (m := Finset.univ.val.map (fun i => Ideal.span {p i})) (by
      intro P hP
      obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hP
      exact hp i)
  rw [FiniteGaussPhase.span_finset_prod]
  exact h

theorem product_primary {ι : Type*} [Fintype ι] (p : ι → O)
    (hp : ∀ i, lambda ^ 2 ∣ p i - 1) : lambda ^ 2 ∣ (∏ i, p i) - 1 := by
  apply primary_multiset_prod (Finset.univ.val.map p)
  intro r hr
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hr
  exact hp i

def productPrimeIndexEquiv {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) :
    ι ≃ PrimeIndex (Ideal.span {∏ i, p i}) := by
  have hinj : Function.Injective (fun i => (Ideal.span {p i} : Ideal O)) := by
    intro i j hij
    by_contra hne
    have ht := (hcop hne).sup_eq
    rw [hij, sup_idem] at ht
    exact (inferInstance : (Ideal.span {p j}).IsMaximal).ne_top ht
  have hmem (i : ι) : (Ideal.span {p i} : Ideal O) ∈ primeSupport (Ideal.span {∏ i, p i}) := by
    rw [primeSupport, normalizedFactors_product]
    exact Multiset.mem_toFinset.mpr (Multiset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  let f : ι → PrimeIndex (Ideal.span {∏ i, p i}) := fun i => ⟨Ideal.span {p i}, hmem i⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    exact hinj (congrArg Subtype.val hij)
  · intro P
    have hm := Multiset.mem_toFinset.mp P.property
    rw [normalizedFactors_product] at hm
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hm
    exact ⟨i, Subtype.ext hi⟩

theorem cubicRow_product_mk {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hI : primaryGenerator (Ideal.span {∏ i, p i}) ≠ 0) (a : O) :
    cubicRow (Ideal.span {∏ i, p i}) hI (Ideal.Quotient.mk (Ideal.span {∏ i, p i}) a) =
      ∏ i, (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 2)
        (Ideal.Quotient.mk (Ideal.span {p i}) a) := by
  rw [cubicRow_mk]
  symm
  exact (productPrimeIndexEquiv p hcop).prod_comp (fun P =>
    (canonicalSextic P.val (primeIndex_good _ hI P) ^ 2) (Ideal.Quotient.mk P.val a))

theorem gaussTwo_eq_canonicalProductGauss {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (hI : primaryGenerator (Ideal.span {∏ i, p i}) ≠ 0) :
    gaussTwo (Ideal.span {∏ i, p i}) hI =
      FiniteGaussPhase.canonicalProductGauss p hp hcop hgood (fun _ => 2) := by
  have hpall : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hgen := primaryGenerator_span (∏ i, p i) hpall (product_primary p hprimary)
  let : Finite (O ⧸ Ideal.span {∏ i, p i}) := finite_quotient_span hpall
  let : Fintype (O ⧸ Ideal.span {∏ i, p i}) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {primaryGenerator (Ideal.span {∏ i, p i})}) := finite_quotient_span hI
  let : Fintype (O ⧸ Ideal.span {primaryGenerator (Ideal.span {∏ i, p i})}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (primaryGenerator_spec (Ideal.span {∏ i, p i}) hI).1
  have hsum :
      (∑ x : O ⧸ Ideal.span {primaryGenerator (Ideal.span {∏ i, p i})},
        cubicRow (Ideal.span {∏ i, p i}) hI (e x) *
          eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
            (primaryGenerator (Ideal.span {∏ i, p i})) hI x) =
      (∑ x : O ⧸ Ideal.span {∏ i, p i},
        (∏ i, (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 2)
          (FiniteGaussPhase.productElementCRT p hcop x i)) *
          eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
            (∏ i, p i) hpall x) := by
    apply Fintype.sum_equiv e.toEquiv
    intro x
    change cubicRow (Ideal.span {∏ i, p i}) hI (e x) *
        eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
          (primaryGenerator (Ideal.span {∏ i, p i})) hI x =
      (∏ i, (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 2)
        (FiniteGaussPhase.productElementCRT p hcop (e x) i)) *
        eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
          (∏ i, p i) hpall (e x)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [e, Ideal.quotEquivOfEq_mk, cubicRow_product_mk p hcop hgood hI,
      FiniteGaussPhase.productElementCRT_mk, eisTraceModChar, IdealGaussCRT.traceModChar_mk, hgen]
  change _ / _ = _ / _
  rw [hsum, hgen]

theorem squarefreeGaussCoefficient_eq_canonicalProductCoefficient {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    squarefreeGaussCoefficient (Ideal.span {∏ i, p i}) =
      FiniteGaussPhase.canonicalProductCoefficient p hp hcop hgood := by
  have hpall : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hgen := primaryGenerator_span (∏ i, p i) hpall (product_primary p hprimary)
  have hI : primaryGenerator (Ideal.span {∏ i, p i}) ≠ 0 := by rwa [hgen]
  have hsq : Squarefree (Ideal.span {∏ i, p i}) := by
    apply (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
      (Ideal.span_singleton_eq_bot.not.mpr hpall)).mpr
    rw [normalizedFactors_product]
    apply Multiset.Nodup.map
    · intro i j hij
      by_contra hne
      have ht := (hcop hne).sup_eq
      rw [hij, sup_idem] at ht
      exact (inferInstance : (Ideal.span {p j}).IsMaximal).ne_top ht
    · exact Finset.univ.nodup
  rw [squarefreeGaussCoefficient_eq _ hsq hI,
    gaussTwo_eq_canonicalProductGauss p hp hcop hgood hprimary hI, hgen]
  rfl

end CompletedGauss

namespace FiniteRayExpansion

variable {R : Type*} [CommRing R] [Fintype R]
noncomputable local instance : Fintype (MulChar R ℂ) := Fintype.ofFinite _

def unitFourierCoeff (f : Rˣ → ℂ) (χ : MulChar R ℂ) : ℂ :=
  (∑ u : Rˣ, f u * star (χ (u : R))) / (Fintype.card Rˣ : ℂ)

theorem unit_fourier_inversion (f : Rˣ → ℂ) (v : Rˣ) :
    (∑ χ : MulChar R ℂ, unitFourierCoeff f χ * χ (v : R)) = f v := by
  have hN : (Fintype.card Rˣ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp_rw [unitFourierCoeff, div_mul_eq_mul_div, Finset.sum_mul, mul_assoc]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, FiniteRingSieve.unit_char_orthogonal]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact mul_div_cancel_right₀ (f v) hN

theorem norm_char_unit (χ : MulChar R ℂ) (u : Rˣ) : ‖χ (u : R)‖ = 1 := by
  simpa only [MulChar.coe_equivToUnitHom] using
    Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)

theorem norm_char_le_one (χ : MulChar R ℂ) (r : R) : ‖χ r‖ ≤ 1 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    exact (norm_char_unit χ u).le
  · rw [MulChar.map_nonunit χ hr, norm_zero]
    norm_num

theorem unitFourierCoeff_norm_le_average (f : Rˣ → ℂ) (χ : MulChar R ℂ) :
    ‖unitFourierCoeff f χ‖ ≤ (∑ u : Rˣ, ‖f u‖) / (Fintype.card Rˣ : ℝ) := by
  rw [unitFourierCoeff, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ∑ u : Rˣ, ‖f u * star (χ (u : R))‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, norm_star, norm_char_unit, mul_one]

theorem unitFourierCoeff_norm_le (f : Rˣ → ℂ) (B : ℝ)
    (hf : ∀ u, ‖f u‖ ≤ B) (χ : MulChar R ℂ) : ‖unitFourierCoeff f χ‖ ≤ B := by
  have hN : (Fintype.card Rˣ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ (∑ u : Rˣ, ‖f u‖) / (Fintype.card Rˣ : ℝ) := unitFourierCoeff_norm_le_average f χ
    _ ≤ (∑ _u : Rˣ, B) / (Fintype.card Rˣ : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun u _ => hf u)) (by positivity)
    _ = B := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

theorem character_card_eq_units : Fintype.card (MulChar R ℂ) = Fintype.card Rˣ := by
  simpa only [Nat.card_eq_fintype_card] using
    MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity R ℂ

theorem unitFourierCoeff_sum_norm_le (f : Rˣ → ℂ) (B : ℝ)
    (hf : ∀ u, ‖f u‖ ≤ B) :
    (∑ χ : MulChar R ℂ, ‖unitFourierCoeff f χ‖) ≤ (Fintype.card Rˣ : ℝ) * B := by
  calc
    _ ≤ ∑ _χ : MulChar R ℂ, B :=
      Finset.sum_le_sum (fun χ _ => unitFourierCoeff_norm_le f B hf χ)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, character_card_eq_units]

theorem unitFourierCoeff_sum_norm_le_sum (f : Rˣ → ℂ) :
    (∑ χ : MulChar R ℂ, ‖unitFourierCoeff f χ‖) ≤ ∑ u : Rˣ, ‖f u‖ := by
  have hN : (Fintype.card Rˣ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ ∑ _χ : MulChar R ℂ, (∑ u : Rˣ, ‖f u‖) / (Fintype.card Rˣ : ℝ) :=
      Finset.sum_le_sum (fun χ _ => unitFourierCoeff_norm_le_average f χ)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, character_card_eq_units]
      field_simp

def zeroExtendUnits (f : Rˣ → ℂ) (r : R) : ℂ :=
  if hr : IsUnit r then f hr.unit else 0

@[simp] theorem zeroExtendUnits_unit (f : Rˣ → ℂ) (u : Rˣ) :
    zeroExtendUnits f (u : R) = f u := by
  rw [zeroExtendUnits, dite_eq_left u.isUnit]
  congr 1
  exact Units.ext u.isUnit.unit_spec

@[simp] theorem zeroExtendUnits_nonunit (f : Rˣ → ℂ) (r : R) (hr : ¬ IsUnit r) :
    zeroExtendUnits f r = 0 := dite_eq_right hr

theorem zeroExtendUnits_fourier (f : Rˣ → ℂ) (r : R) :
    zeroExtendUnits f r = ∑ χ : MulChar R ℂ, unitFourierCoeff f χ * χ r := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    rw [zeroExtendUnits_unit]
    exact (unit_fourier_inversion f u).symm
  · rw [zeroExtendUnits_nonunit f r hr]
    simp only [MulChar.map_nonunit _ hr, mul_zero, Finset.sum_const_zero]

theorem zeroExtendUnits_restrict (f : R → ℂ) (r : R) :
    zeroExtendUnits (fun u : Rˣ => f (u : R)) r = (if IsUnit r then 1 else 0) * f r := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    simp only [zeroExtendUnits_unit, u.isUnit, ite_true, one_mul]
  · simp only [zeroExtendUnits_nonunit _ _ hr, hr, ite_false, zero_mul]

def unitTensorCoeff (f : Rˣ → Rˣ → ℂ) (χ η : MulChar R ℂ) : ℂ :=
  unitFourierCoeff (fun u => unitFourierCoeff (f u) η) χ

theorem unit_tensor_fourier_inversion (f : Rˣ → Rˣ → ℂ) (u v : Rˣ) :
    (∑ χ : MulChar R ℂ, ∑ η : MulChar R ℂ,
      unitTensorCoeff f χ η * χ (u : R) * η (v : R)) = f u v := by
  calc
    _ = ∑ η : MulChar R ℂ,
        (∑ χ : MulChar R ℂ, unitTensorCoeff f χ η * χ (u : R)) * η (v : R) := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = ∑ η : MulChar R ℂ, unitFourierCoeff (f u) η * η (v : R) := by
      apply Finset.sum_congr rfl
      intro η _
      change (∑ χ : MulChar R ℂ,
        unitFourierCoeff (fun a => unitFourierCoeff (f a) η) χ * χ (u : R)) * η (v : R) = _
      rw [unit_fourier_inversion]
    _ = _ := unit_fourier_inversion (f u) v

theorem unitTensorCoeff_norm_le (f : Rˣ → Rˣ → ℂ) (B : ℝ)
    (hf : ∀ u v, ‖f u v‖ ≤ B) (χ η : MulChar R ℂ) :
    ‖unitTensorCoeff f χ η‖ ≤ B :=
  unitFourierCoeff_norm_le _ B (fun u => unitFourierCoeff_norm_le (f u) B (hf u) η) χ

theorem unitTensorCoeff_sum_norm_le (f : Rˣ → Rˣ → ℂ) (B : ℝ)
    (hf : ∀ u v, ‖f u v‖ ≤ B) :
    (∑ χ : MulChar R ℂ, ∑ η : MulChar R ℂ, ‖unitTensorCoeff f χ η‖) ≤
      (Fintype.card Rˣ : ℝ) ^ 2 * B := by
  calc
    _ ≤ ∑ _χ : MulChar R ℂ, ∑ _η : MulChar R ℂ, B :=
      Finset.sum_le_sum (fun χ _ => Finset.sum_le_sum (fun η _ => unitTensorCoeff_norm_le f B hf χ η))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, character_card_eq_units]
      ring

theorem unitTensorCoeff_sum_norm_le_sum (f : Rˣ → Rˣ → ℂ) :
    (∑ χ : MulChar R ℂ, ∑ η : MulChar R ℂ, ‖unitTensorCoeff f χ η‖) ≤
      ∑ u : Rˣ, ∑ v : Rˣ, ‖f u v‖ := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ η : MulChar R ℂ, ∑ u : Rˣ, ‖unitFourierCoeff (f u) η‖ :=
      Finset.sum_le_sum (fun η _ => unitFourierCoeff_sum_norm_le_sum (fun u => unitFourierCoeff (f u) η))
    _ = ∑ u : Rˣ, ∑ η : MulChar R ℂ, ‖unitFourierCoeff (f u) η‖ := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun u _ => unitFourierCoeff_sum_norm_le_sum (f u))

def zeroExtendUnitPair (f : Rˣ → Rˣ → ℂ) (r s : R) : ℂ :=
  zeroExtendUnits (fun u => zeroExtendUnits (f u) s) r

theorem zeroExtendUnitPair_fourier (f : Rˣ → Rˣ → ℂ) (r s : R) :
    zeroExtendUnitPair f r s = ∑ χ : MulChar R ℂ, ∑ η : MulChar R ℂ,
      unitTensorCoeff f χ η * χ r * η s := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    by_cases hs : IsUnit s
    · obtain ⟨v, rfl⟩ := hs
      simp only [zeroExtendUnitPair, zeroExtendUnits_unit]
      exact (unit_tensor_fourier_inversion f u v).symm
    · simp only [zeroExtendUnitPair, zeroExtendUnits_unit, zeroExtendUnits_nonunit _ _ hs,
        MulChar.map_nonunit _ hs, mul_zero, Finset.sum_const_zero]
  · simp only [zeroExtendUnitPair, zeroExtendUnits_nonunit _ _ hr,
      MulChar.map_nonunit _ hr, mul_zero, zero_mul, Finset.sum_const_zero]

theorem zeroExtendUnitPair_restrict (f : R → R → ℂ) (r s : R) :
    zeroExtendUnitPair (fun u v : Rˣ => f (u : R) (v : R)) r s =
      (if IsUnit r then 1 else 0) * (if IsUnit s then 1 else 0) * f r s := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    simp only [zeroExtendUnitPair, zeroExtendUnits_unit, zeroExtendUnits_restrict,
      u.isUnit, ite_true, one_mul]
  · simp only [zeroExtendUnitPair, zeroExtendUnits_nonunit _ _ hr, hr, ite_false, zero_mul]

end FiniteRayExpansion

open scoped BigOperators Classical

namespace RayFourExpansion
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ActualEisensteinCoordinates QuadraticGaussRay
open FiniteRayExpansion

abbrev RayRing := O ⧸ Ideal.span {(4 : O)}

noncomputable instance rayRingFintype : Fintype RayRing := by
  letI : Finite RayRing := finite_quotient_span (by norm_num : (4 : O) ≠ 0)
  exact Fintype.ofFinite _

abbrev RayCharacter := MulChar RayRing ℂ
noncomputable instance rayCharacterFintype : Fintype RayCharacter := Fintype.ofFinite _

def rayCharacter (χ : RayCharacter) (a : O) : ℂ :=
  χ (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a)

theorem rayCharacter_mul (χ : RayCharacter) (a b : O) :
    rayCharacter χ (a * b) = rayCharacter χ a * rayCharacter χ b := by
  simp only [rayCharacter, map_mul]

theorem rayCharacter_eq_of_mod_four (χ : RayCharacter) (a b : O) (h : (4 : O) ∣ a - b) :
    rayCharacter χ a = rayCharacter χ b := by
  unfold rayCharacter
  congr 1
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr h)

def rayMask (a : O) : ℂ :=
  if IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a) then 1 else 0

theorem rayRing_card : Fintype.card RayRing = 16 := by
  have h := rational_modulus_card 4 (by decide)
  simpa only [Nat.card_eq_fintype_card, Nat.cast_ofNat, show (4 : ℕ) ^ 2 = 16 by decide] using h

theorem rayUnit_card_le : Fintype.card RayRingˣ ≤ 16 := by
  calc
    _ ≤ Fintype.card RayRing := Fintype.card_le_of_injective _ Units.val_injective
    _ = 16 := rayRing_card

theorem rayCharacter_card_le : Fintype.card RayCharacter ≤ 16 := by
  rw [character_card_eq_units]
  exact rayUnit_card_le

def phaseCoeff (f : RayRing → ℂ) (χ : RayCharacter) : ℂ :=
  unitFourierCoeff (fun u : RayRingˣ => f (u : RayRing)) χ

theorem phase_expansion (f : RayRing → ℂ) (a : O) :
    rayMask a * f (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a) =
      ∑ χ : RayCharacter, phaseCoeff f χ * rayCharacter χ a := by
  rw [rayMask, ← zeroExtendUnits_restrict]
  exact zeroExtendUnits_fourier _ _

theorem phaseCoeff_norm_le (f : RayRing → ℂ) (B : ℝ)
    (hf : ∀ u : RayRingˣ, ‖f (u : RayRing)‖ ≤ B) (χ : RayCharacter) :
    ‖phaseCoeff f χ‖ ≤ B := unitFourierCoeff_norm_le _ B hf χ

theorem phaseCoeff_sum_norm_le (f : RayRing → ℂ) (B : ℝ)
    (hf : ∀ u : RayRingˣ, ‖f (u : RayRing)‖ ≤ B) :
    (∑ χ : RayCharacter, ‖phaseCoeff f χ‖) ≤ 16 * B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hf 1)
  exact (unitFourierCoeff_sum_norm_le _ B hf).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast rayUnit_card_le) hB)

def pairCoeff (f : RayRing → RayRing → ℂ) (χ η : RayCharacter) : ℂ :=
  unitTensorCoeff (fun u v : RayRingˣ => f (u : RayRing) (v : RayRing)) χ η

theorem pair_phase_expansion (f : RayRing → RayRing → ℂ) (a b : O) :
    rayMask a * rayMask b *
      f (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a)
        (Ideal.Quotient.mk (Ideal.span {(4 : O)}) b) =
      ∑ χ : RayCharacter, ∑ η : RayCharacter,
        pairCoeff f χ η * rayCharacter χ a * rayCharacter η b := by
  rw [rayMask, rayMask, ← zeroExtendUnitPair_restrict]
  exact zeroExtendUnitPair_fourier _ _ _

theorem pairCoeff_norm_le (f : RayRing → RayRing → ℂ) (B : ℝ)
    (hf : ∀ u v : RayRingˣ, ‖f (u : RayRing) (v : RayRing)‖ ≤ B) (χ η : RayCharacter) :
    ‖pairCoeff f χ η‖ ≤ B := unitTensorCoeff_norm_le _ B hf χ η

theorem pairCoeff_sum_norm_le (f : RayRing → RayRing → ℂ) (B : ℝ)
    (hf : ∀ u v : RayRingˣ, ‖f (u : RayRing) (v : RayRing)‖ ≤ B) :
    (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖pairCoeff f χ η‖) ≤ 256 * B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hf 1 1)
  have hcard : (Fintype.card RayRingˣ : ℝ) ^ 2 ≤ 256 := by
    have h : (Fintype.card RayRingˣ : ℝ) ≤ 16 := by exact_mod_cast rayUnit_card_le
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card RayRingˣ)]
  exact (unitTensorCoeff_sum_norm_le _ B hf).trans (mul_le_mul_of_nonneg_right hcard hB)

theorem quadraticRayValue_bounds (r : EisensteinEPrimaryPhase.Coord) :
    ‖quadraticRayValue r‖ ≤ 2 ∧ ‖(quadraticRayValue r)⁻¹‖ ≤ 1 := by
  rcases r with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [quadraticRayValue, breveGaussianFourTerms_formula, zpow_neg,
      Complex.I_sq, Complex.I_pow_three, Complex.inv_I,
      ZMod.val] <;>
    ring_nf <;> norm_num [Complex.I_sq, Complex.inv_I]

theorem fixedGQuotientValue_norm_le_two (r : RayRing) : ‖fixedGQuotientValue r‖ ≤ 2 := by
  let : Fintype (O ⧸ cubicTwoIdeal) := Fintype.ofFinite _
  let χ : MulChar (O ⧸ cubicTwoIdeal) ℂ :=
    (cubicChar cubicTwoIdeal cubicTwoIdeal_good).ringHomComp eisEmbedding
  let x := Ideal.Quotient.mk cubicTwoIdeal (lift (residueQuotientFour r))
  have hc : ‖(χ x)⁻¹‖ ≤ 1 := by
    simpa only [MulChar.inv_apply_eq_inv'] using norm_char_le_one (χ⁻¹) x
  change ‖(χ x)⁻¹ * quadraticRayValue (residueQuotientFour r)‖ ≤ 2
  rw [norm_mul]
  calc
    _ ≤ 1 * 2 := mul_le_mul hc (quadraticRayValue_bounds _).1 (norm_nonneg _) (by norm_num)
    _ = 2 := by norm_num

def gCoeff : RayCharacter → ℂ := phaseCoeff fixedGQuotientValue

theorem gCoeff_norm_le_two (χ : RayCharacter) : ‖gCoeff χ‖ ≤ 2 :=
  phaseCoeff_norm_le _ 2 (fun u => fixedGQuotientValue_norm_le_two u) χ

theorem gCoeff_sum_norm_le : (∑ χ : RayCharacter, ‖gCoeff χ‖) ≤ 32 := by
  exact (phaseCoeff_sum_norm_le _ 2 (fun u => fixedGQuotientValue_norm_le_two u)).trans_eq (by norm_num)

theorem fixedG_character_expansion (a : O) :
    rayMask a * fixedGQuotientValue (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a) =
      ∑ χ : RayCharacter, gCoeff χ * rayCharacter χ a := phase_expansion _ a

def crossQuotientPhase (r s : RayRing) : ℂ :=
  MixedCrossSeparation.quadraticRayPair (residueQuotientFour r) (residueQuotientFour s)

theorem crossQuotientPhase_norm_le_two (r s : RayRing) : ‖crossQuotientPhase r s‖ ≤ 2 := by
  unfold crossQuotientPhase MixedCrossSeparation.quadraticRayPair
  rw [div_eq_mul_inv, mul_inv_rev, norm_mul, norm_mul]
  calc
    _ ≤ 2 * (1 * 1) :=
      mul_le_mul (quadraticRayValue_bounds _).1
        (mul_le_mul (quadraticRayValue_bounds _).2 (quadraticRayValue_bounds _).2
          (norm_nonneg _) (by norm_num))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = 2 := by norm_num

def crossCoeff : RayCharacter → RayCharacter → ℂ := pairCoeff crossQuotientPhase

theorem crossCoeff_norm_le_two (χ η : RayCharacter) : ‖crossCoeff χ η‖ ≤ 2 :=
  pairCoeff_norm_le _ 2 (fun u v => crossQuotientPhase_norm_le_two u v) χ η

theorem crossCoeff_sum_norm_le :
    (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖) ≤ 512 := by
  exact (pairCoeff_sum_norm_le _ 2 (fun u v => crossQuotientPhase_norm_le_two u v)).trans_eq (by norm_num)

theorem quadraticRayPair_character_expansion (a b : O) :
    rayMask a * rayMask b * MixedCrossSeparation.quadraticRayPair (residue a) (residue b) =
      ∑ χ : RayCharacter, ∑ η : RayCharacter,
        crossCoeff χ η * rayCharacter χ a * rayCharacter η b := by
  simpa only [crossCoeff, crossQuotientPhase, residueQuotientFour_mk] using
    pair_phase_expansion crossQuotientPhase a b

end RayFourExpansion

end

end OAI
end OAIOriginalModule0094

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.RayCharacters
Source SHA256: 1dd2abcb3b701760af193e7ec339fb238a82dbce044276a6dc39fcb85cdf17b4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0095


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

open scoped BigOperators Classical

namespace RayFourExpansion
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase QuadraticGaussRay
open ActualEisensteinCoordinates MixedCrossSeparation

theorem prime_unit_mod_four (p : O) [(Ideal.span {p}).IsMaximal]
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) p) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have h2 : (2 : O) ∉ Ideal.span {p} := by
    intro hm
    have hz : (2 : O ⧸ Ideal.span {p}) = 0 := by
      simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr hm
    apply hchar
    exact (Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime (O ⧸ Ideal.span {p}) _)
      Nat.prime_two).mp ((ringChar.spec (O ⧸ Ideal.span {p}) 2).mp hz)
  let : (Ideal.span {(2 : O)}).IsMaximal := by
    simpa only [cubicTwoIdeal, Ideal.span_singleton_neg] using cubicTwoIdeal_isMaximal
  have hcop : IsCoprime (Ideal.span {p}) (Ideal.span {(2 : O)}) := by
    apply Ideal.isCoprime_of_isMaximal
    intro heq
    apply h2
    rw [heq]
    exact Ideal.subset_span (by simp)
  obtain ⟨a, b, hab⟩ := IdealGaussCRT.bezout_of_principal_coprime hcop
  have hcp : IsCoprime p (2 : O) := ⟨a, b, hab⟩
  have hcp4 : IsCoprime p (4 : O) := by
    simpa only [show (2 : O) ^ 2 = 4 by norm_num] using
      (hcp.pow_right : IsCoprime p ((2 : O) ^ 2))
  obtain ⟨a, b, hab⟩ := hcp4
  have hz : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (4 : O) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hm := congrArg (Ideal.Quotient.mk (Ideal.span {(4 : O)})) hab
  simp only [map_add, map_mul, map_one, hz, mul_zero, add_zero] at hm
  exact IsUnit.of_mul_eq_one_right _ hm

theorem prime_product_unit_mod_four {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (S : Finset ι) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ S, p i)) := by
  rw [map_prod]
  exact IsUnit.prod_iff.mpr (fun i _ => prime_unit_mod_four (p i) (hchar i))

theorem rayMask_prime_product {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (S : Finset ι) :
    rayMask (∏ i ∈ S, p i) = 1 := by
  rw [rayMask, ite_eq_left (prime_product_unit_mod_four p hchar S)]

theorem canonicalProductG_character_expansion
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductG p hp hcop hgood =
      ∑ χ : RayCharacter, gCoeff χ * rayCharacter χ (∏ i, p i) := by
  rw [canonicalProductG_eq_fixed_quotient p hp hcop hgood hchar hprimary]
  have h := fixedG_character_expansion (∏ i, p i)
  rw [rayMask_prime_product p hchar Finset.univ, one_mul] at h
  exact h

theorem quadraticCrossPhase_character_expansion
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (A B : Finset ι) (hd : Disjoint A B) :
    quadraticCrossPhase p hg A B =
      ∑ χ : RayCharacter, ∑ η : RayCharacter,
        crossCoeff χ η * rayCharacter χ (∏ i ∈ A, p i) *
          rayCharacter η (∏ i ∈ B, p i) := by
  rw [quadraticCrossPhase_eq_rayPair p hp hcop hg hchar A B hd]
  have h := quadraticRayPair_character_expansion (∏ i ∈ A, p i) (∏ i ∈ B, p i)
  rw [rayMask_prime_product p hchar A, rayMask_prime_product p hchar B, one_mul, one_mul] at h
  exact h

end RayFourExpansion

namespace MixedCrossSeparation
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
open QuadraticGaussRay ActualEisensteinCoordinates GaussGeneratorTransport

theorem converted_active_row_observations
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) (d h : O) :
    let q : activeSupport S T → O := fun i => p i.val
    let hq : ∀ i, q i ≠ 0 := fun i => hp i.val
    let hgood : ∀ i, lambda ∉ Ideal.span {q i} := fun i => hg i.val
    let A : Finset (activeSupport S T) := Finset.univ.filter fun i => i.val ∈ S \ T
    let B : Finset (activeSupport S T) := Finset.univ.filter fun i => i.val ∉ S \ T
    let P : ι → Ideal O := fun i => Ideal.span {p i}
    let row := finiteSexticRow (activePrimes P S T) (fun i => hg i.val) (activeExponent S T)
    let cA := star (convertedColumnBlock q hq hgood A true) *
      finiteSquarefreeRow P hg (S \ T) d
    let cB := convertedColumnBlock q hq hgood B false *
      finiteSquarefreeRow P hg (T \ S) d
    activeConvertedGauss p hp hg S T * (row d * star (row h)) =
      quadraticRayPair (residue (∏ i ∈ A, q i)) (residue (∏ i ∈ B, q i)) *
        star (cA * star (finiteSquarefreeRow P hg (S \ T) h)) *
        (cB * star (finiteSquarefreeRow P hg (T \ S) h)) := by
  dsimp only
  have hqcop : Pairwise (Function.onFun IsCoprime
      (fun i : activeSupport S T => Ideal.span {p i.val})) := by
    intro i k hik
    exact hcop (fun he => hik (Subtype.ext he))
  have hd : Disjoint
      (Finset.univ.filter (fun i : activeSupport S T => i.val ∈ S \ T))
      (Finset.univ.filter (fun i : activeSupport S T => i.val ∉ S \ T)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hi).2
  rw [activeConvertedGauss_separated p hp hg hprimary S T]
  rw [quadraticCrossPhase_eq_rayPair (fun i : activeSupport S T => p i.val)
    (fun i => hp i.val) hqcop (fun i => hg i.val) (fun i => hchar i.val) _ _ hd]
  rw [active_dual_row_factorization (fun i => Ideal.span {p i}) hg S T d h]
  simp only [star_mul, star_star]
  ring

theorem convertedColumnBlock_image
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (e : κ → ι) (he : Function.Injective e)
    (A : Finset κ) (inverse : Bool) :
    convertedColumnBlock (fun i => p (e i)) (fun i => hp (e i)) (fun i => hg (e i)) A inverse =
      convertedColumnBlock p hp hg (A.image e) inverse := by
  unfold convertedColumnBlock
  rw [Finset.prod_image (fun a ha b hb hab => he hab)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.image_erase he A i, Finset.prod_image (fun a ha b hb hab => he hab)]
  rfl

theorem quadraticCrossPhase_image
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (e : κ → ι) (he : Function.Injective e)
    (A B : Finset κ) :
    quadraticCrossPhase (fun i => p (e i)) (fun i => hg (e i)) A B =
      quadraticCrossPhase p hg (A.image e) (B.image e) := by
  unfold quadraticCrossPhase
  rw [Finset.prod_image (fun a ha b hb hab => he hab)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.prod_image (fun a ha b hb hab => he hab)]
  rfl

private theorem negative_active_image {ι : Type*} [DecidableEq ι] (S T : Finset ι) :
    (Finset.univ.filter (fun i : activeSupport S T => i.val ∈ S \ T)).image Subtype.val = S \ T := by
  ext i
  constructor
  · intro hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp ha).2
  · intro hi
    exact Finset.mem_image.mpr ⟨⟨i, Finset.mem_union_left _ hi⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩

private theorem positive_active_image {ι : Type*} [DecidableEq ι] (S T : Finset ι) :
    (Finset.univ.filter (fun i : activeSupport S T => i.val ∉ S \ T)).image Subtype.val = T \ S := by
  ext i
  constructor
  · intro hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    have hm := a.property
    rcases Finset.mem_union.mp hm with hleft | hright
    · exact ((Finset.mem_filter.mp ha).2 hleft).elim
    · exact hright
  · intro hi
    have hn : i ∉ S \ T := fun h => (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp h).1
    exact Finset.mem_image.mpr ⟨⟨i, Finset.mem_union_right _ hi⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩, rfl⟩

theorem activeConvertedGauss_eq_columnBlocks
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) :
    activeConvertedGauss p hp hg S T =
      convertedColumnBlock p hp hg (S \ T) true *
        convertedColumnBlock p hp hg (T \ S) false *
          quadraticCrossPhase p hg (S \ T) (T \ S) := by
  rw [activeConvertedGauss_separated p hp hg hprimary S T]
  rw [convertedColumnBlock_image p hp hg Subtype.val Subtype.val_injective,
    convertedColumnBlock_image p hp hg Subtype.val Subtype.val_injective,
    quadraticCrossPhase_image p hg Subtype.val Subtype.val_injective,
    negative_active_image, positive_active_image]

theorem activeConvertedGauss_disjoint_mod_four
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) (hd : Disjoint S T) :
    activeConvertedGauss p hp hg S T =
      convertedColumnBlock p hp hg S true * convertedColumnBlock p hp hg T false *
        quadraticRayPair (residue (∏ i ∈ S, p i)) (residue (∏ i ∈ T, p i)) := by
  rw [activeConvertedGauss_eq_columnBlocks p hp hg hprimary S T,
    Finset.sdiff_eq_self_of_disjoint hd, Finset.sdiff_eq_self_of_disjoint hd.symm,
    quadraticCrossPhase_eq_rayPair p hp hcop hg hchar S T hd]

end MixedCrossSeparation

namespace FirstCauchyArithmetic

section
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic CoprimeMobiusExtension

def supportMobius {ι : Type*} (P : ι → Ideal O) (S : Finset ι) : ℂ :=
  (UniqueFactorizationMonoid.moebius (∏ i ∈ S, P i) : ℂ)

def supportConjugateSum {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (B : Finset ι) (C : Finset ι → ℂ) (h : O) : ℂ :=
  ∑ S ∈ B.powerset, supportMobius P S * C S * star (finiteSquarefreeRow P hg S h)

private theorem supportMobius_union {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (S T : Finset ι) (hd : Disjoint S T) :
    supportMobius P (S ∪ T) = supportMobius P S * supportMobius P T := by
  simp only [supportMobius, prime_product_moebius P hprime hinj,
    Finset.card_union_of_disjoint hd, pow_add]

theorem supportMobius_sq {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P) (S : Finset ι) :
    supportMobius P S * supportMobius P S = 1 := by
  rw [supportMobius, prime_product_moebius P hprime hinj, ← mul_pow]
  norm_num

theorem star_supportMobius {ι : Type*} (P : ι → Ideal O) (S : Finset ι) :
    star (supportMobius P S) = supportMobius P S := by
  simp [supportMobius]

private theorem finiteSquarefreeRow_union {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S T : Finset ι) (hd : Disjoint S T) (h : O) :
    finiteSquarefreeRow P hg (S ∪ T) h =
      finiteSquarefreeRow P hg S h * finiteSquarefreeRow P hg T h := by
  exact Finset.prod_union hd

theorem coprime_pair_sum_reindexed
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (hg : ∀ i, lambda ∉ P i) (B : Finset ι) (C₁ C₂ : Finset ι → ℂ) (h : O) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
      if Disjoint S T then
        star (supportMobius P S * C₁ S * star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P T * C₂ T * star (finiteSquarefreeRow P hg T h)) else 0) =
    ∑ D ∈ B.powerset, supportMobius P D * rowCoprimeMask P D h *
      star (supportConjugateSum P hg (B \ D) (fun U => C₁ (D ∪ U)) h) *
        supportConjugateSum P hg (B \ D) (fun V => C₂ (D ∪ V)) h := by
  rw [double_sum_disjoint_reindexed]
  apply Finset.sum_congr rfl
  intro D hD
  rw [← prime_product_moebius P hprime hinj D]
  change supportMobius P D * _ = _
  have ht (U V : Finset ι) (hU : U ∈ (B \ D).powerset) (hV : V ∈ (B \ D).powerset) :
      star (supportMobius P (D ∪ U) * C₁ (D ∪ U) *
        star (finiteSquarefreeRow P hg (D ∪ U) h)) *
      (supportMobius P (D ∪ V) * C₂ (D ∪ V) *
        star (finiteSquarefreeRow P hg (D ∪ V) h)) =
      rowCoprimeMask P D h *
        star (supportMobius P U * C₁ (D ∪ U) * star (finiteSquarefreeRow P hg U h)) *
          (supportMobius P V * C₂ (D ∪ V) * star (finiteSquarefreeRow P hg V h)) := by
    have hdU : Disjoint D U := Finset.disjoint_of_subset_right
      (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
    have hdV : Disjoint D V := Finset.disjoint_of_subset_right
      (Finset.mem_powerset.mp hV) disjoint_sdiff_self_right
    rw [supportMobius_union P hprime hinj D U hdU,
      supportMobius_union P hprime hinj D V hdV,
      finiteSquarefreeRow_union P hg D U hdU,
      finiteSquarefreeRow_union P hg D V hdV]
    simp only [star_mul, star_star, star_supportMobius]
    have hmu := supportMobius_sq P hprime hinj D
    have hrow := finiteSquarefreeRow_self_pair P hg D h
    calc
      _ = (supportMobius P D * supportMobius P D) *
          (star (finiteSquarefreeRow P hg D h) * finiteSquarefreeRow P hg D h) *
          (finiteSquarefreeRow P hg U h * star (C₁ (D ∪ U)) * supportMobius P U) *
          (supportMobius P V * C₂ (D ∪ V) * star (finiteSquarefreeRow P hg V h)) := by ring
      _ = _ := by rw [hmu, hrow]; ring
  have heq : (∑ U ∈ (B \ D).powerset, ∑ V ∈ (B \ D).powerset,
      star (supportMobius P (D ∪ U) * C₁ (D ∪ U) * star (finiteSquarefreeRow P hg (D ∪ U) h)) *
      (supportMobius P (D ∪ V) * C₂ (D ∪ V) * star (finiteSquarefreeRow P hg (D ∪ V) h))) =
    rowCoprimeMask P D h *
      star (supportConjugateSum P hg (B \ D) (fun U => C₁ (D ∪ U)) h) *
        supportConjugateSum P hg (B \ D) (fun V => C₂ (D ∪ V)) h := by
    simp only [supportConjugateSum, star_sum]
    rw [mul_assoc, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro V hV
    simpa only [mul_assoc] using ht U V hU hV
  rw [heq]
  ring

theorem finite_phase_coprime_reindex
    {ι R : Type*} [DecidableEq ι] [Fintype R] [DecidableEq R]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (hg : ∀ i, lambda ∉ P i) (B : Finset ι)
    (σ : Finset ι → R) (phase : R → R → ℂ) (C₁ C₂ : Finset ι → ℂ) (h : O) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
      if Disjoint S T then phase (σ S) (σ T) *
        star (supportMobius P S * C₁ S * star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P T * C₂ T * star (finiteSquarefreeRow P hg T h)) else 0) =
    ∑ r : R × R, phase r.1 r.2 *
      ∑ D ∈ B.powerset, supportMobius P D * rowCoprimeMask P D h *
        star (supportConjugateSum P hg (B \ D)
          (fun U => if σ (D ∪ U) = r.1 then C₁ (D ∪ U) else 0) h) *
        supportConjugateSum P hg (B \ D)
          (fun V => if σ (D ∪ V) = r.2 then C₂ (D ∪ V) else 0) h := by
  let Z (r : R × R) (S T : Finset ι) : ℂ :=
    if Disjoint S T then
      star (supportMobius P S * (if σ S = r.1 then C₁ S else 0) *
        star (finiteSquarefreeRow P hg S h)) *
      (supportMobius P T * (if σ T = r.2 then C₂ T else 0) *
        star (finiteSquarefreeRow P hg T h)) else 0
  have ht (S T : Finset ι) :
      (if Disjoint S T then phase (σ S) (σ T) *
        star (supportMobius P S * C₁ S * star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P T * C₂ T * star (finiteSquarefreeRow P hg T h)) else 0) =
      ∑ r : R × R, phase r.1 r.2 * Z r S T := by
    by_cases hd : Disjoint S T
    · simp only [Z, ite_eq_left hd, Fintype.sum_prod_type]
      simp only [ mul_zero, ite_mul, zero_mul, apply_ite, star_zero]
      simp
      ring
    · simp [Z, hd]
  calc
    _ = ∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
        ∑ r : R × R, phase r.1 r.2 * Z r S T := by
      apply Finset.sum_congr rfl
      intro S hS
      exact Finset.sum_congr rfl (fun T hT => ht S T)
    _ = ∑ r : R × R, phase r.1 r.2 *
        ∑ S ∈ B.powerset, ∑ T ∈ B.powerset, Z r S T := by
      simp only [Finset.mul_sum]
      calc
        _ = ∑ S ∈ B.powerset, ∑ r : R × R,
            ∑ T ∈ B.powerset, phase r.1 r.2 * Z r S T := by
          apply Finset.sum_congr rfl
          intro S hS
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      exact coprime_pair_sum_reindexed P hprime hinj hg B
        (fun S => if σ S = r.1 then C₁ S else 0)
        (fun T => if σ T = r.2 then C₂ T else 0) h

end
section

open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedCrossSeparation RayFourExpansion

def supportRay {ι : Type*} (p : ι → O) (χ : RayCharacter) (S : Finset ι) : ℂ :=
  rayCharacter χ (∏ i ∈ S, p i)

private theorem supportRay_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) (χ : RayCharacter) (S T : Finset ι) (hd : Disjoint S T) :
    supportRay p χ (S ∪ T) = supportRay p χ S * supportRay p χ T := by
  rw [supportRay, Finset.prod_union hd, rayCharacter_mul]
  rfl

theorem supportConjugateSum_ray_common
    {ι : Type*} [DecidableEq ι] (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B D : Finset ι)
    (C : Finset ι → ℂ) (χ : RayCharacter) (h : O) :
    supportConjugateSum (fun i => Ideal.span {p i}) hg (B \ D)
      (fun U => supportRay p χ (D ∪ U) * C (D ∪ U)) h =
    supportRay p χ D * supportConjugateSum (fun i => Ideal.span {p i}) hg (B \ D)
      (fun U => supportRay p χ U * C (D ∪ U)) h := by
  rw [supportConjugateSum, supportConjugateSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hdU : Disjoint D U := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
  rw [supportRay_union p χ D U hdU]
  ring

theorem supportConjugateSum_star_ray_common
    {ι : Type*} [DecidableEq ι] (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B D : Finset ι)
    (C : Finset ι → ℂ) (χ : RayCharacter) (h : O) :
    supportConjugateSum (fun i => Ideal.span {p i}) hg (B \ D)
      (fun U => star (supportRay p χ (D ∪ U)) * C (D ∪ U)) h =
    star (supportRay p χ D) * supportConjugateSum (fun i => Ideal.span {p i}) hg (B \ D)
      (fun U => star (supportRay p χ U) * C (D ∪ U)) h := by
  rw [supportConjugateSum, supportConjugateSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hdU : Disjoint D U := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
  rw [supportRay_union p χ D U hdU, star_mul]
  ring

theorem quadratic_phase_coprime_ray_reindex
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (B : Finset ι) (C₁ C₂ : Finset ι → ℂ) (h : O) :
    let P : ι → Ideal O := fun i => Ideal.span {p i}
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
      if Disjoint S T then quadraticCrossPhase p hg S T *
        star (supportMobius P S * C₁ S * star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P T * C₂ T * star (finiteSquarefreeRow P hg T h)) else 0) =
    ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
      ∑ D ∈ B.powerset,
        (supportMobius P D * rowCoprimeMask P D h * supportRay p r.1 D * supportRay p r.2 D) *
        star (supportConjugateSum P hg (B \ D)
          (fun U => star (supportRay p r.1 U) * C₁ (D ∪ U)) h) *
        supportConjugateSum P hg (B \ D)
          (fun V => supportRay p r.2 V * C₂ (D ∪ V)) h := by
  dsimp only
  let P : ι → Ideal O := fun i => Ideal.span {p i}
  have hcop : Pairwise (Function.onFun IsCoprime P) := by
    intro i k hik
    exact Ideal.isCoprime_of_isMaximal (hinj.ne hik)
  have hprime (i : ι) : Prime (P i) :=
    Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
  let Z (r : RayCharacter × RayCharacter) (S T : Finset ι) : ℂ :=
    if Disjoint S T then
      star (supportMobius P S * (star (supportRay p r.1 S) * C₁ S) *
        star (finiteSquarefreeRow P hg S h)) *
      (supportMobius P T * (supportRay p r.2 T * C₂ T) *
        star (finiteSquarefreeRow P hg T h)) else 0
  have ht (S T : Finset ι) :
      (if Disjoint S T then quadraticCrossPhase p hg S T *
        star (supportMobius P S * C₁ S * star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P T * C₂ T * star (finiteSquarefreeRow P hg T h)) else 0) =
      ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 * Z r S T := by
    by_cases hd : Disjoint S T
    · rw [ite_eq_left hd, quadraticCrossPhase_character_expansion p hp hcop hg hchar S T hd]
      simp only [Fintype.sum_prod_type, Z, ite_eq_left hd, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ hχ
      apply Finset.sum_congr rfl
      intro η hη
      simp only [supportRay, star_mul, star_star]
      ring
    · simp [Z, hd]
  calc
    _ = ∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
        ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 * Z r S T := by
      apply Finset.sum_congr rfl
      intro S hS
      exact Finset.sum_congr rfl (fun T hT => ht S T)
    _ = ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
        ∑ S ∈ B.powerset, ∑ T ∈ B.powerset, Z r S T := by
      simp only [Finset.mul_sum]
      calc
        _ = ∑ S ∈ B.powerset, ∑ r : RayCharacter × RayCharacter,
            ∑ T ∈ B.powerset, crossCoeff r.1 r.2 * Z r S T := by
          apply Finset.sum_congr rfl
          intro S hS
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      change (∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
        if Disjoint S T then star (supportMobius P S *
          (star (supportRay p r.1 S) * C₁ S) * star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P T * (supportRay p r.2 T * C₂ T) *
            star (finiteSquarefreeRow P hg T h)) else 0) = _
      rw [coprime_pair_sum_reindexed P hprime hinj hg B]
      apply Finset.sum_congr rfl
      intro D hD
      rw [supportConjugateSum_star_ray_common p hg B D C₁ r.1 h,
        supportConjugateSum_ray_common p hg B D C₂ r.2 h]
      simp only [star_mul, star_star]
      ring

end

open ActualEisensteinCubic ConcretePrimeRowBridge

private theorem family_prime {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (i : ι) :
    Prime (P i) := Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance

private theorem family_prod_ne_zero {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (S : Finset ι) :
    (∏ i ∈ S, P i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (family_prime P i).ne_zero)

theorem family_prime_dvd_product_iff {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (S : Finset ι) (i : ι) :
    P i ∣ ∏ j ∈ S, P j ↔ i ∈ S := by
  constructor
  · intro h
    obtain ⟨j, hj, hd⟩ := ((family_prime P i).dvd_finsetProd_iff P).mp h
    have he : P i = P j := associated_iff_eq.mp
      ((family_prime P i).associated_of_dvd (family_prime P j) hd)
    exact hinj he ▸ hj
  · exact fun hi => Finset.dvd_prod_of_mem P hi

theorem family_product_injective {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) : Function.Injective (fun S : Finset ι => ∏ i ∈ S, P i) := by
  intro S T h
  change (∏ i ∈ S, P i) = (∏ i ∈ T, P i) at h
  ext i
  rw [← family_prime_dvd_product_iff P hinj S i, h, family_prime_dvd_product_iff P hinj T i]

def supportIdealFamily {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (B : Finset ι) : Finset (Ideal O) :=
  B.powerset.image (fun S => ∏ i ∈ S, P i)

theorem supportIdealFamily_pos {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (B : Finset ι) :
    ∀ I ∈ supportIdealFamily P B, I ≠ ⊥ := by
  intro I hI
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hI
  exact family_prod_ne_zero P S

private theorem factor_family_product_iff {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (S : Finset ι) (Q : Ideal O) :
    Q ∈ UniqueFactorizationMonoid.normalizedFactors (∏ i ∈ S, P i) ↔
      ∃ i ∈ S, Q = P i := by
  rw [UniqueFactorizationMonoid.mem_normalizedFactors_iff (family_prod_ne_zero P S)]
  constructor
  · rintro ⟨hQ, hd⟩
    obtain ⟨i, hi, hdiv⟩ := (hQ.dvd_finsetProd_iff P).mp hd
    exact ⟨i, hi, associated_iff_eq.mp (hQ.associated_of_dvd (family_prime P i) hdiv)⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨family_prime P i, Finset.dvd_prod_of_mem P hi⟩

theorem supportIdealFamily_good {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (B : Finset ι) :
    ∀ I ∈ supportIdealFamily P B,
      ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ Q := by
  intro I hI Q hQ
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨i, hi, rfl⟩ := (factor_family_product_iff P S Q).mp hQ
  exact hg i

def recoveredSupport {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (B : Finset ι) (I : Ideal O) : Finset ι :=
  B.filter (fun i => P i ∣ I)

theorem recoveredSupport_product {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (B S : Finset ι) (hS : S ⊆ B) :
    recoveredSupport P B (∏ i ∈ S, P i) = S := by
  ext i
  simp only [recoveredSupport, Finset.mem_filter, family_prime_dvd_product_iff P hinj S i]
  exact and_iff_right_of_imp (fun hi => hS hi)

theorem idealSexticRow_support_product {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, lambda ∉ P i)
    (B S : Finset ι) (hS : S ⊆ B) (h : O) :
    idealSexticRow (supportIdealFamily P B) (supportIdealFamily_pos P B)
      (supportIdealFamily_good P hg B) (∏ i ∈ S, P i) h =
      finiteSquarefreeRow P hg S h := by
  let F := supportIdealFamily P B
  have hIF : (∏ i ∈ S, P i) ∈ F :=
    Finset.mem_image.mpr ⟨S, Finset.mem_powerset.mpr hS, rfl⟩
  let idx (i : ι) (hi : i ∈ S) : primePool F :=
    ⟨P i, mem_primePool_iff.mpr ⟨∏ j ∈ S, P j, hIF,
      (factor_family_product_iff P S (P i)).mpr ⟨i, hi, rfl⟩⟩⟩
  symm
  unfold idealSexticRow finiteSquarefreeRow
  apply Finset.prod_bij idx
  · intro i hi
    exact (mem_idealSupport_iff F _ (idx i hi)).mpr
      ((factor_family_product_iff P S (P i)).mpr ⟨i, hi, rfl⟩)
  · intro i hi j hj hij
    exact hinj (congrArg Subtype.val hij)
  · intro Q hQ
    have hm := (mem_idealSupport_iff F _ Q).mp hQ
    obtain ⟨i, hi, he⟩ := (factor_family_product_iff P S Q.val).mp hm
    exact ⟨i, hi, Subtype.ext he.symm⟩
  · intro i hi
    rfl

theorem supportConjugateSum_eq_conjugateIdealRowSum
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, lambda ∉ P i)
    (B : Finset ι) (C : Finset ι → ℂ) (h : O) :
    supportConjugateSum P hg B C h =
      conjugateIdealRowSum (supportIdealFamily P B) (supportIdealFamily_pos P B)
        (supportIdealFamily_good P hg B) (fun I => C (recoveredSupport P B I)) h := by
  let f : Ideal O → ℂ := fun I =>
    mobiusIdealColumn (fun I => C (recoveredSupport P B I)) I *
      star (idealSexticRow (supportIdealFamily P B) (supportIdealFamily_pos P B)
        (supportIdealFamily_good P hg B) I h)
  change supportConjugateSum P hg B C h =
    ∑ I ∈ B.powerset.image (fun S => ∏ i ∈ S, P i), f I
  rw [Finset.sum_image (fun S hS T hT h => family_product_injective P hinj h)]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro S hS
  have hSB := Finset.mem_powerset.mp hS
  dsimp only [f]
  rw [idealSexticRow_support_product P hinj hg B S hSB h]
  simp only [mobiusIdealColumn, supportMobius, recoveredSupport_product P hinj B S hSB]

theorem quadratic_phase_reindex_to_ideal_rows
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (B : Finset ι) (C₁ C₂ : Finset ι → ℂ) (h : O) :
    let P : ι → Ideal O := fun i => Ideal.span {p i}
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
      if Disjoint S T then MixedCrossSeparation.quadraticCrossPhase p hg S T *
        star (supportMobius P S * C₁ S * star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P T * C₂ T * star (finiteSquarefreeRow P hg T h)) else 0) =
    ∑ r : RayFourExpansion.RayCharacter × RayFourExpansion.RayCharacter,
      RayFourExpansion.crossCoeff r.1 r.2 *
      ∑ D ∈ B.powerset,
        (supportMobius P D * rowCoprimeMask P D h * supportRay p r.1 D * supportRay p r.2 D) *
        star (conjugateIdealRowSum (supportIdealFamily P (B \ D))
          (supportIdealFamily_pos P (B \ D)) (supportIdealFamily_good P hg (B \ D))
          (fun I => star (supportRay p r.1 (recoveredSupport P (B \ D) I)) *
            C₁ (D ∪ recoveredSupport P (B \ D) I)) h) *
        conjugateIdealRowSum (supportIdealFamily P (B \ D))
          (supportIdealFamily_pos P (B \ D)) (supportIdealFamily_good P hg (B \ D))
          (fun I => supportRay p r.2 (recoveredSupport P (B \ D) I) *
            C₂ (D ∪ recoveredSupport P (B \ D) I)) h := by
  dsimp only
  rw [quadratic_phase_coprime_ray_reindex p hp hinj hg hchar B C₁ C₂ h]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  apply Finset.sum_congr rfl
  intro D hD
  rw [supportConjugateSum_eq_conjugateIdealRowSum (fun i => Ideal.span {p i}) hinj hg,
    supportConjugateSum_eq_conjugateIdealRowSum (fun i => Ideal.span {p i}) hinj hg]

end FirstCauchyArithmetic

end

end OAI
end OAIOriginalModule0095

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.CoefficientCancellation
Source SHA256: 4e5d5286ced57ac8ec45136d112cbc215d5ac7ee46fff4a2c8e3a77eb77e2069
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0096


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

open scoped BigOperators Classical

namespace MixedCrossSeparation
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion

theorem norm_localCoefficient (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    ‖localCoefficient p hp hg‖ = 1 := by
  rw [localCoefficient, norm_mul, norm_star, norm_angularFactor p hp,
    norm_localGauss p hp hg hc 2 (by decide) (by decide), one_mul]

theorem local_coefficient_cancel (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hpr : lambda ^ 2 ∣ p - 1) :
    localCoefficient p hp hg * convertedLocal p hp hg false = localG p hp hg ∧
      star (localCoefficient p hp hg) * convertedLocal p hp hg true =
        canonicalSextic (Ideal.span {p}) hg (Ideal.Quotient.mk (Ideal.span {p}) (-1 : O)) *
          star (localG p hp hg) := by
  have hA : localCoefficient p hp hg * star (localCoefficient p hp hg) = 1 := by
    rw [← starRingEnd_apply, Complex.mul_conj', norm_localCoefficient p hp hg hc]
    norm_num
  have hG : localG p hp hg * star (localG p hp hg) = 1 := by
    rw [← starRingEnd_apply, Complex.mul_conj', norm_localG p hp hg hc hpr]
    norm_num
  have hGn : localG p hp hg ≠ 0 := by
    intro h
    simp [h] at hG
  have hGsn := star_ne_zero.mpr hGn
  constructor
  · simp only [convertedLocal, Bool.false_eq_true, ↓reduceIte]
    rw [← mul_div_assoc]
    apply (div_eq_iff hGsn).mpr
    rw [hA, hG]
  · simp only [convertedLocal, ↓reduceIte]
    rw [← mul_div_assoc]
    apply (div_eq_iff hGn).mpr
    calc
      _ = canonicalSextic (Ideal.span {p}) hg (Ideal.Quotient.mk (Ideal.span {p}) (-1 : O)) *
          (localCoefficient p hp hg * star (localCoefficient p hp hg)) := by ring
      _ = _ := by
        rw [hA]
        calc
          _ = canonicalSextic (Ideal.span {p}) hg (Ideal.Quotient.mk (Ideal.span {p}) (-1 : O)) *
              (localG p hp hg * star (localG p hp hg)) := by rw [hG]
          _ = _ := by ring

theorem canonicalProductG_crt {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) :
    canonicalProductG p hp hcop hg = canonicalCrossFactor p hg ^ 3 *
      ∏ i, localG (p i) (hp i) (hg i) := by
  rw [canonicalProductG, canonicalProductGauss_constant_power p hp hcop hg 3 (by decide)]
  change (∏ i, canonicalSextic (Ideal.span {p i}) (hg i)
      (Ideal.Quotient.mk (Ideal.span {p i}) (4 : O)))⁻¹ *
      (canonicalCrossFactor p hg ^ 3 * ∏ i, localGauss (p i) (hp i) (hg i) 3) = _
  simp only [localG, breveLocalG, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  change (∏ i, canonicalSextic (Ideal.span {p i}) (hg i)
      (Ideal.Quotient.mk (Ideal.span {p i}) (4 : O)))⁻¹ *
      (canonicalCrossFactor p hg ^ 3 * ∏ i, localGauss (p i) (hp i) (hg i) 3) =
    canonicalCrossFactor p hg ^ 3 *
      ((∏ i, canonicalSextic (Ideal.span {p i}) (hg i)
        (Ideal.Quotient.mk (Ideal.span {p i}) (4 : O)))⁻¹ *
        ∏ i, localGauss (p i) (hp i) (hg i) 3)
  ring

theorem convertedColumnBlock_univ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (b : Bool) :
    convertedColumnBlock p hp hg Finset.univ b =
      canonicalCrossFactor p hg ^ (if b then 5 else 1) *
        ∏ i, convertedLocal (p i) (hp i) (hg i) b := by
  simp only [convertedColumnBlock, Finset.prod_mul_distrib, ← Finset.prod_pow,
    canonicalCrossFactor, crossSymbol]
  congr 2
  funext i
  congr 1
  ext k
  simp

theorem coefficient_cancel_univ_false {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductCoefficient p hp hcop hg * convertedColumnBlock p hp hg Finset.univ false =
      canonicalProductG p hp hcop hg := by
  rw [canonicalProductCoefficient_crt, convertedColumnBlock_univ, canonicalProductG_crt]
  change (canonicalCrossFactor p hg ^ 2 * ∏ i, localCoefficient (p i) (hp i) (hg i)) *
      (canonicalCrossFactor p hg ^ 1 * ∏ i, convertedLocal (p i) (hp i) (hg i) false) = _
  calc
    _ = canonicalCrossFactor p hg ^ 3 * ∏ i,
        localCoefficient (p i) (hp i) (hg i) * convertedLocal (p i) (hp i) (hg i) false := by
      rw [Finset.prod_mul_distrib]
      ring
    _ = _ := by
      congr 1
      exact Finset.prod_congr rfl (fun i _ => (local_coefficient_cancel (p i) (hp i) (hg i) (hc i) (hpr i)).1)

theorem coefficient_cancel_univ_true {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) :
    star (canonicalProductCoefficient p hp hcop hg) * convertedColumnBlock p hp hg Finset.univ true =
      (∏ i, canonicalSextic (Ideal.span {p i}) (hg i)
        (Ideal.Quotient.mk (Ideal.span {p i}) (-1 : O))) * star (canonicalProductG p hp hcop hg) := by
  let C := canonicalCrossFactor p hg
  have hC6 : C ^ 6 = 1 := canonicalCrossFactor_pow_six p hcop hg
  have hCn : ‖C‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hC6 (by decide)
  have hCC : C * star C = 1 := by
    rw [← starRingEnd_apply, Complex.mul_conj', hCn]
    norm_num
  have hC3 : star C ^ 3 = C ^ 3 := by
    have hh : (C ^ 3) ^ 2 = 1 := by simpa only [← pow_mul] using hC6
    rw [← star_pow]
    rcases (sq_eq_one_iff).mp hh with h | h <;> simp [h]
  rw [canonicalProductCoefficient_crt, convertedColumnBlock_univ, canonicalProductG_crt]
  change star (C ^ 2 * ∏ i, localCoefficient (p i) (hp i) (hg i)) *
      (C ^ 5 * ∏ i, convertedLocal (p i) (hp i) (hg i) true) =
        _ * star (C ^ 3 * ∏ i, localG (p i) (hp i) (hg i))
  simp only [star_mul, star_pow, star_prod, hC3]
  calc
    _ = (C * star C) ^ 2 * C ^ 3 * ∏ i,
        star (localCoefficient (p i) (hp i) (hg i)) * convertedLocal (p i) (hp i) (hg i) true := by
      rw [Finset.prod_mul_distrib]
      ring
    _ = C ^ 3 * ∏ i,
        canonicalSextic (Ideal.span {p i}) (hg i)
          (Ideal.Quotient.mk (Ideal.span {p i}) (-1 : O)) * star (localG (p i) (hp i) (hg i)) := by
      rw [hCC, one_pow, one_mul]
      congr 1
      exact Finset.prod_congr rfl (fun i _ => (local_coefficient_cancel (p i) (hp i) (hg i) (hc i) (hpr i)).2)
    _ = _ := by rw [Finset.prod_mul_distrib]; ring

theorem columnPrimeCoprime {ι : Type*} (p : ι → O)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (S : Finset ι) :
    Pairwise (Function.onFun IsCoprime (fun i : S => Ideal.span {p i.val})) := by
  intro i j hij
  exact hcop (fun h => hij (Subtype.ext h))

def columnCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) : ℂ :=
  canonicalProductCoefficient (fun i : S => p i.val) (fun i => hp i.val)
    (columnPrimeCoprime p hcop S) (fun i => hg i.val)

def columnG {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) : ℂ :=
  canonicalProductG (fun i : S => p i.val) (fun i => hp i.val)
    (columnPrimeCoprime p hcop S) (fun i => hg i.val)

theorem convertedColumnBlock_subtype {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (b : Bool) :
    convertedColumnBlock (fun i : S => p i.val) (fun i => hp i.val)
      (fun i => hg i.val) Finset.univ b = convertedColumnBlock p hp hg S b := by
  have h := convertedColumnBlock_image p hp hg (Subtype.val : S → ι)
    Subtype.val_injective Finset.univ b
  have he : (Finset.univ : Finset S).image Subtype.val = S := by ext; simp
  simpa only [he] using h

theorem columnCoefficient_cancel_false {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) :
    columnCoefficient p hp hcop hg S * convertedColumnBlock p hp hg S false =
      columnG p hp hcop hg S := by
  have h := coefficient_cancel_univ_false (fun i : S => p i.val) (fun i => hp i.val)
    (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => hc i.val) (fun i => hpr i.val)
  rw [convertedColumnBlock_subtype] at h
  exact h

theorem columnCoefficient_cancel_true {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) :
    star (columnCoefficient p hp hcop hg S) * convertedColumnBlock p hp hg S true =
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1) *
        star (columnG p hp hcop hg S) := by
  have h := coefficient_cancel_univ_true (fun i : S => p i.val) (fun i => hp i.val)
    (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => hc i.val) (fun i => hpr i.val)
  have hprod : (∏ i : S, canonicalSextic (Ideal.span {p i.val}) (hg i.val)
      (Ideal.Quotient.mk (Ideal.span {p i.val}) (-1 : O))) =
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1) := by
    simpa only [finiteSquarefreeRow] using
      (Finset.prod_coe_sort S (fun i => canonicalSextic (Ideal.span {p i}) (hg i)
        (Ideal.Quotient.mk (Ideal.span {p i}) (-1 : O))))
  rw [convertedColumnBlock_subtype, hprod] at h
  exact h

end MixedCrossSeparation

open scoped BigOperators Classical SchwartzMap ContDiff
namespace FirstCauchyArithmetic
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
open MixedCrossSeparation GaussGeneratorTransport ConcretePrimeRowBridge EisensteinSchwartzPoisson

def firstPassColumnMinus {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (C : Finset ι → ℂ) (d : O) (S : Finset ι) : ℂ :=
  star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1)) *
    columnG p hp hcop hg S * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d * C S

def firstPassColumnPlus {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (C : Finset ι → ℂ) (d : O) (S : Finset ι) : ℂ :=
  columnG p hp hcop hg S * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d * C S

theorem norm_columnG
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) :
    ‖columnG p hp hcop hg S‖ = 1 :=
  norm_canonicalProductG (fun i : S => p i.val) (fun i => hp i.val)
    (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => hc i.val) (fun i => hpr i.val)

theorem norm_firstPassColumnMinus_le
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (C : Finset ι → ℂ) (d : O) (S : Finset ι) :
    ‖firstPassColumnMinus p hp hcop hg C d S‖ ≤ ‖C S‖ := by
  simp only [firstPassColumnMinus, norm_mul, norm_star, norm_columnG p hp hcop hg hc hpr]
  calc
    _ ≤ 1 * 1 * 1 * ‖C S‖ := by
      gcongr
      · exact finiteSquarefreeRow_norm_le_one (fun i => Ideal.span {p i}) hg S (-1)
      · exact finiteSquarefreeRow_norm_le_one (fun i => Ideal.span {p i}) hg S d
    _ = _ := by ring

theorem norm_firstPassColumnPlus_le
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (C : Finset ι → ℂ) (d : O) (S : Finset ι) :
    ‖firstPassColumnPlus p hp hcop hg C d S‖ ≤ ‖C S‖ := by
  simp only [firstPassColumnPlus, norm_mul, norm_columnG p hp hcop hg hc hpr, one_mul]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (finiteSquarefreeRow_norm_le_one (fun i => Ideal.span {p i}) hg S d)

theorem a_weighted_converted_pair
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (S T : Finset ι) (hd : Disjoint S T) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    let P : ι → Ideal O := fun i => Ideal.span {p i}
    let row := finiteSexticRow (activePrimes P S T) (fun i => hg i.val) (activeExponent S T)
    star (columnCoefficient p hp hcop hg S * C₁ S) *
      (columnCoefficient p hp hcop hg T * C₂ T) *
      (supportMobius P S * supportMobius P T * activeConvertedGauss p hp hg S T) *
        (row d * star (row h)) =
    quadraticCrossPhase p hg S T *
      star (supportMobius P S * firstPassColumnMinus p hp hcop hg C₁ d S *
        star (finiteSquarefreeRow P hg S h)) *
      (supportMobius P T * firstPassColumnPlus p hp hcop hg C₂ d T *
        star (finiteSquarefreeRow P hg T h)) := by
  dsimp only
  rw [activeConvertedGauss_eq_columnBlocks p hp hg hpr S T,
    active_dual_row_factorization (fun i => Ideal.span {p i}) hg S T d h,
    Finset.sdiff_eq_self_of_disjoint hd, Finset.sdiff_eq_self_of_disjoint hd.symm]
  have hminus := columnCoefficient_cancel_true p hp hcop hg hc hpr S
  have hplus := columnCoefficient_cancel_false p hp hcop hg hc hpr T
  simp only [firstPassColumnMinus, firstPassColumnPlus, star_mul, star_star,
    star_supportMobius]
  calc
    _ = (star (columnCoefficient p hp hcop hg S) * convertedColumnBlock p hp hg S true) *
      (columnCoefficient p hp hcop hg T * convertedColumnBlock p hp hg T false) *
      (star (C₁ S) * C₂ T * supportMobius (fun i => Ideal.span {p i}) S *
        supportMobius (fun i => Ideal.span {p i}) T * quadraticCrossPhase p hg S T *
        (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S h *
          star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d)) *
        (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T d *
          star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T h))) := by ring
    _ = _ := by rw [hminus, hplus]; ring

theorem active_productGauss_eq_mobius_converted
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) :
    let q : activeSupport S T → O := fun i => p i.val
    canonicalProductGauss q (fun i => hp i.val)
      (activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T)
      (fun i => hg i.val) (activeExponent S T) =
    supportMobius (fun i => Ideal.span {p i}) S *
      supportMobius (fun i => Ideal.span {p i}) T * activeConvertedGauss p hp hg S T := by
  dsimp only
  let : DecidableEq (activeSupport S T) := fun a b => Classical.propDecidable (a = b)
  let q : activeSupport S T → O := fun i => p i.val
  let hq := activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T
  have he : activeExponent S T =
      (fun i : activeSupport S T => if decide (i.val ∈ S \ T) then 5 else 1) := by
    funext i
    simp only [activeExponent, decide_eq_true_eq]
  have h' : (supportMobius (fun i => Ideal.span {p i}) S *
      supportMobius (fun i => Ideal.span {p i}) T) *
      canonicalProductGauss q (fun i => hp i.val) hq (fun i => hg i.val)
        (activeExponent S T) = activeConvertedGauss p hp hg S T := by
    rw [supportMobius, supportMobius, pair_moebius_eq_active p hinj S T]
    unfold activeConvertedGauss
    rw [he]
    exact moebius_mixed_gauss_conversion q (fun i => hp i.val) hq (fun i => hg i.val)
      (fun i => hc i.val) (fun i => hpr i.val) (fun i => decide (i.val ∈ S \ T))
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hs := supportMobius_sq (fun i => Ideal.span {p i}) hprime hinj S
  have ht := supportMobius_sq (fun i => Ideal.span {p i}) hprime hinj T
  calc
    _ = (supportMobius (fun i => Ideal.span {p i}) S * supportMobius (fun i => Ideal.span {p i}) S) *
      (supportMobius (fun i => Ideal.span {p i}) T * supportMobius (fun i => Ideal.span {p i}) T) *
      canonicalProductGauss q (fun i => hp i.val) hq (fun i => hg i.val) (activeExponent S T) := by
        rw [hs, ht]; ring
    _ = _ := by rw [← h']; ring

def activeGaussRowFactor
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (S T : Finset ι) (d h : O) : ℂ :=
  let P : ι → Ideal O := fun i => Ideal.span {p i}
  let row := finiteSexticRow (activePrimes P S T) (fun i => hg i.val) (activeExponent S T)
  canonicalProductGauss (fun i : activeSupport S T => p i.val) (fun i => hp i.val)
    (activePrimes_pairwise_isCoprime P hinj S T) (fun i => hg i.val) (activeExponent S T) *
      (row d * star (row h))

theorem disjoint_pair_poisson_arithmetic
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (S T : Finset ι) (hd : Disjoint S T)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let P : ι → Ideal O := fun i => Ideal.span {p i}
    let n := ∏ i : activeSupport S T, p i.val
    (∑' z : O, (star (finiteSquarefreeRow P hg S z) * finiteSquarefreeRow P hg T z) *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
    ((scale : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
      ∑' h : O, paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding n‖ ^ 2) *
        activeGaussRowFactor p hp hinj hg S T 1 h := by
  dsimp only
  let P : ι → Ideal O := fun i => Ideal.span {p i}
  let q : activeSupport S T → O := fun i => p i.val
  let hq := activePrimes_pairwise_isCoprime P hinj S T
  let row := finiteSexticRow (activePrimes P S T) (fun i => hg i.val) (activeExponent S T)
  let G := canonicalProductGauss q (fun i => hp i.val) hq (fun i => hg i.val) (activeExponent S T)
  have hpz (z : O) : star (finiteSquarefreeRow P hg S z) * finiteSquarefreeRow P hg T z = row z := by
    rw [finiteSquarefreeRow_pair_activeSupport]
    simp [Finset.disjoint_iff_inter_eq_empty.mp hd, rowCoprimeMask, row]
  have hrow1 : row 1 = 1 := by simp [row, finiteSexticRow]
  have ht := canonical_radial_poisson_product q (fun i => hp i.val) hq (fun i => hg i.val)
    (fun i => hc i.val) (activeExponent S T) (activeExponent_ne_zero S T)
    (activeExponent_lt_six S T) W scale hscale
  have hseries : (∑' h : O,
      paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (∏ i, q i)‖ ^ 2) *
        activeGaussRowFactor p hp hinj hg S T 1 h) =
      G * ∑' h : O, star (row h) *
        paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (∏ i, q i)‖ ^ 2) := by
    calc
      _ = ∑' h : O, G * (star (row h) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (∏ i, q i)‖ ^ 2)) := by
        apply tsum_congr
        intro h
        change _ * (G * (row 1 * star (row h))) = _
        rw [hrow1]
        ring
      _ = _ := tsum_mul_left
  rw [hseries]
  calc
    _ = ∑' z : O, row z * W (‖eisEmbedding z‖ ^ 2 / scale) := by
      apply tsum_congr
      intro z
      rw [hpz]
    _ = ((scale : ℂ) * G / (‖eisEmbedding (∏ i, q i)‖ : ℂ)) *
        ∑' h : O, star (row h) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (∏ i, q i)‖ ^ 2) := ht
    _ = _ := by ring

theorem a_weighted_activeGaussRowFactor
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (S T : Finset ι) (hd : Disjoint S T) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    let P : ι → Ideal O := fun i => Ideal.span {p i}
    star (columnCoefficient p hp hcop hg S * C₁ S) *
      (columnCoefficient p hp hcop hg T * C₂ T) * activeGaussRowFactor p hp hinj hg S T d h =
    quadraticCrossPhase p hg S T *
      star (supportMobius P S * firstPassColumnMinus p hp hcop hg C₁ d S *
        star (finiteSquarefreeRow P hg S h)) *
      (supportMobius P T * firstPassColumnPlus p hp hcop hg C₂ d T *
        star (finiteSquarefreeRow P hg T h)) := by
  dsimp only
  unfold activeGaussRowFactor
  dsimp only
  rw [active_productGauss_eq_mobius_converted p hp hinj hg hc hpr S T]
  simpa only [mul_assoc] using a_weighted_converted_pair p hp hcop hg hc hpr S T hd C₁ C₂ d h

theorem a_weighted_pair_sum_to_second_poisson_rows
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (B : Finset ι) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    let P : ι → Ideal O := fun i => Ideal.span {p i}
    let D₁ := firstPassColumnMinus p hp hcop hg C₁ d
    let D₂ := firstPassColumnPlus p hp hcop hg C₂ d
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
      if Disjoint S T then
        star (columnCoefficient p hp hcop hg S * C₁ S) *
          (columnCoefficient p hp hcop hg T * C₂ T) *
            activeGaussRowFactor p hp hinj hg S T d h else 0) =
    ∑ r : RayFourExpansion.RayCharacter × RayFourExpansion.RayCharacter,
      RayFourExpansion.crossCoeff r.1 r.2 *
      ∑ D ∈ B.powerset,
        (supportMobius P D * rowCoprimeMask P D h * supportRay p r.1 D * supportRay p r.2 D) *
        star (conjugateIdealRowSum (supportIdealFamily P (B \ D))
          (supportIdealFamily_pos P (B \ D)) (supportIdealFamily_good P hg (B \ D))
          (fun I => star (supportRay p r.1 (recoveredSupport P (B \ D) I)) *
            D₁ (D ∪ recoveredSupport P (B \ D) I)) h) *
        conjugateIdealRowSum (supportIdealFamily P (B \ D))
          (supportIdealFamily_pos P (B \ D)) (supportIdealFamily_good P hg (B \ D))
          (fun I => supportRay p r.2 (recoveredSupport P (B \ D) I) *
            D₂ (D ∪ recoveredSupport P (B \ D) I)) h := by
  dsimp only
  rw [← quadratic_phase_reindex_to_ideal_rows p hp hinj hg hc B
    (firstPassColumnMinus p hp hcop hg C₁ d) (firstPassColumnPlus p hp hcop hg C₂ d) h]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd : Disjoint S T
  · rw [ite_eq_left hd, ite_eq_left hd]
    exact a_weighted_activeGaussRowFactor p hp hinj hcop hg hc hpr S T hd C₁ C₂ d h
  · rw [ite_eq_right hd, ite_eq_right hd]

end FirstCauchyArithmetic

open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def pvSeminorms : Finset (ℕ × ℕ) :=
  Classical.choose paperRadialFourier_nonzero_lattice_uniform

def pvConstant : ℝ :=
  Classical.choose (Classical.choose_spec paperRadialFourier_nonzero_lattice_uniform)

theorem pvConstant_pos : 0 < pvConstant :=
  (Classical.choose_spec
    (Classical.choose_spec paperRadialFourier_nonzero_lattice_uniform)).1

def pvControl (W : 𝓢(ℝ, ℂ)) : ℝ :=
  pvConstant * pvSeminorms.sup (schwartzSeminormFamily ℝ ℝ ℂ) W

theorem pvControl_nonneg (W : 𝓢(ℝ, ℂ)) : 0 ≤ pvControl W :=
  mul_nonneg pvConstant_pos.le (apply_nonneg _ _)

theorem pv_lattice_bound (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t) :
    t * (∑' h : {h : O // h ≠ 0},
      ‖paperRadialFourier W (t * ‖eisEmbedding h.val‖ ^ 2)‖) ≤ pvControl W :=
  (Classical.choose_spec
    (Classical.choose_spec paperRadialFourier_nonzero_lattice_uniform)).2 W t ht

theorem norm_finite_character_le_one {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (r : R) : ‖χ r‖ ≤ 1 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    simpa only [MulChar.coe_equivToUnitHom] using
      (Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)).le
  · rw [MulChar.map_nonunit χ hr, norm_zero]
    exact zero_le_one

theorem finiteSexticRow_norm_le_one {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (j : ι → ℕ) (a : O) :
    ‖finiteSexticRow P hg j a‖ ≤ 1 := by
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  rw [finiteSexticRow, norm_prod]
  calc
    _ ≤ ∏ i : ι, (1 : ℝ) := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun i _ => norm_finite_character_le_one
        (canonicalSextic (P i) (hg i) ^ j i) _)
    _ = 1 := by simp

theorem canonical_polya_vinogradov {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, lambda ∉ P i) (hc : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, finiteSexticRow P hg j z * W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      pvControl W * ‖eisEmbedding (finitePrimeModulus P)‖ := by
  let c := finitePrimeModulus P
  let q := ‖eisEmbedding c‖
  have hq : 0 < q := norm_pos_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P))
  let t := M / q ^ 2
  have ht : 0 < t := div_pos hM (sq_pos_of_pos hq)
  let F : O → ℂ := fun h => star (finiteSexticRow P hg j h) *
    paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)
  have hF (h : O) : ‖F h‖ ≤ ‖paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)‖ := by
    dsimp only [F]
    rw [norm_mul, norm_star]
    exact mul_le_of_le_one_left (norm_nonneg _) (finiteSexticRow_norm_le_one P hg j h)
  have hs := paperRadialFourier_lattice_summable_norm W t ht
  have hFs : Summable (fun h : O => ‖F h‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF hs
  have hzero : F 0 = 0 := by simp only [F, finiteSexticRow_zero, star_zero, zero_mul]
  have heq : (∑' h : O, F h) = ∑' h : {h : O // h ≠ 0}, F h := by
    symm
    apply tsum_subtype_eq_of_support_subset
    intro h hh
      hz
    subst h
    exact hh hzero
  have hn : ‖∑' h : O, F h‖ ≤
      ∑' h : {h : O // h ≠ 0}, ‖paperRadialFourier W (t * ‖eisEmbedding h.val‖ ^ 2)‖ := by
    rw [heq]
    exact (norm_tsum_le_tsum_norm (hFs.subtype _)).trans
      ((hFs.subtype _).tsum_le_tsum (fun h => hF h) (hs.subtype _))
  have hbound : t * ‖∑' h : O, F h‖ ≤ pvControl W :=
    (mul_le_mul_of_nonneg_left hn ht.le).trans (pv_lattice_bound W t ht)
  rw [canonical_radial_poisson_normalized P hcop hg hc j hj0 hj6 W M hM]
  have hargs (h : O) : M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2 =
      t * ‖eisEmbedding h‖ ^ 2 := by dsimp [t, q]; ring
  change ‖((M : ℂ) * canonicalNormalizedGauss P hcop hg j / (q : ℂ)) *
    ∑' h : O, star (finiteSexticRow P hg j h) *
      paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)‖ ≤ _
  simp_rw [hargs]
  change ‖((M : ℂ) * canonicalNormalizedGauss P hcop hg j / (q : ℂ)) * ∑' h : O, F h‖ ≤ _
  rw [norm_mul, norm_div, norm_mul, norm_canonicalNormalizedGauss P hcop hg hc j hj0 hj6,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
  change M / q * ‖∑' h : O, F h‖ ≤ pvControl W * q
  calc
    _ = q * (t * ‖∑' h : O, F h‖) := by dsimp [t]; field_simp
    _ ≤ q * pvControl W := mul_le_mul_of_nonneg_left hbound hq.le
    _ = _ := mul_comm _ _

theorem norm_ideal_moebius_le_one (I : Ideal O) :
    ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖ ≤ 1 := by
  unfold UniqueFactorizationMonoid.moebius
  split_ifs <;> simp

theorem canonical_masked_polya_vinogradov
    {α ι : Type*} [DecidableEq α] [Fintype ι] [Nonempty ι]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset α) (Q : ι → Ideal O) [∀ i, (Q i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime Q))
    (hg : ∀ i, lambda ∉ Q i) (hc : ∀ i, ringChar (O ⧸ Q i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, rowCoprimeMask P S z * finiteSexticRow Q hg j z *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      (2 : ℝ) ^ S.card * (pvControl W * ‖eisEmbedding (finitePrimeModulus Q)‖) := by
  rw [canonical_masked_radial_dilations P hinj S Q hcop hg j W M hM]
  calc
    _ ≤ ∑ E ∈ S.powerset, ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
        finiteSexticRow Q hg j (primeSubsetGenerator P E) *
        ∑' z : O, finiteSexticRow Q hg j z *
          W (‖eisEmbedding z‖ ^ 2 / (M / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _E ∈ S.powerset, pvControl W * ‖eisEmbedding (finitePrimeModulus Q)‖ := by
      apply Finset.sum_le_sum
      intro E hE
      rw [norm_mul, norm_mul]
      have hp := canonical_polya_vinogradov Q hcop hg hc j hj0 hj6 W _
        (primeSubset_reducedScale_pos P E hM)
      have hmul : ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ)‖ *
          ‖finiteSexticRow Q hg j (primeSubsetGenerator P E)‖ ≤ 1 := by
        calc
          _ ≤ 1 * 1 := mul_le_mul (norm_ideal_moebius_le_one _)
            (finiteSexticRow_norm_le_one Q hg j _) (norm_nonneg _) zero_le_one
          _ = 1 := one_mul _
      exact (mul_le_of_le_one_left (norm_nonneg _) hmul).trans hp
    _ = _ := by simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

end QuadraticInitialBound

end

end OAI
end OAIOriginalModule0096

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.InitialBound
Source SHA256: 3c9c167b74671ed905cdd6a6a46a9d61d801e29b9f28d552a664785bc795d8f6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0097



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

open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def quadraticRow {α : Type*} (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset α) (z : O) : ℂ :=
  (finiteSquarefreeRow P hg S z) ^ 3

theorem quadraticRow_eq_canonical {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset α) (z : O) :
    quadraticRow P hg S z =
      finiteSexticRow (fun i : S => P i.val) (fun i => hg i.val) (fun _ => 3) z := by
  simp only [quadraticRow, finiteSexticRow, finiteSquarefreeRow,
    MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), Finset.prod_pow]
  rw [Finset.prod_coe_sort (s := S) (f := fun i => canonicalSextic (P i) (hg i) (Ideal.Quotient.mk (P i) z))]

theorem quadraticRow_star {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset α) (z : O) :
    star (quadraticRow P hg S z) = quadraticRow P hg S z := by
  rw [quadraticRow_eq_canonical]
  simp only [finiteSexticRow, star_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [canonicalSextic_pow_three_quadratic]
  simp only [MulChar.ringHomComp_apply, Int.coe_castRingHom, star_intCast]

theorem quadraticRow_disjoint_union {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S T : Finset α) (hd : Disjoint S T) (z : O) :
    quadraticRow P hg (S ∪ T) z = quadraticRow P hg S z * quadraticRow P hg T z := by
  simp only [quadraticRow, finiteSquarefreeRow, Finset.prod_union hd, mul_pow]

theorem quadraticRow_pair_kernel {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S T : Finset α) (z : O) :
    star (quadraticRow P hg S z) * quadraticRow P hg T z =
      rowCoprimeMask P (S ∩ T) z *
        finiteSexticRow (activePrimes P S T) (fun i => hg i.val) (fun _ => 3) z := by
  have h := congrArg (fun v : ℂ => v ^ 3) (finiteSquarefreeRow_pair_kernel P hg S T z)
  have hm : rowCoprimeMask P (S ∩ T) z ^ 3 = rowCoprimeMask P (S ∩ T) z := by
    unfold rowCoprimeMask
    split_ifs <;> simp
  have hd : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  simp only [mul_pow, ← star_pow, hm] at h
  change star (quadraticRow P hg S z) * quadraticRow P hg T z =
    rowCoprimeMask P (S ∩ T) z * star (quadraticRow P hg (S \ T) z) *
      quadraticRow P hg (T \ S) z at h
  simp only [quadraticRow_star] at h ⊢
  rw [← quadraticRow_eq_canonical]
  change _ = rowCoprimeMask P (S ∩ T) z * quadraticRow P hg ((S \ T) ∪ (T \ S)) z
  rw [quadraticRow_disjoint_union P hg _ _ hd]
  simpa only [mul_assoc] using h

theorem quadratic_gram_offdiagonal {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, lambda ∉ P i) (hc : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (S T : Finset α) (hne : S ≠ T) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, (star (quadraticRow P hg S z) * quadraticRow P hg T z) *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      (2 : ℝ) ^ (S ∩ T).card *
        (pvControl W * ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖) := by
  let : Nonempty (activeSupport S T) := (activeSupport_nonempty_of_ne hne).to_subtype
  simp_rw [quadraticRow_pair_kernel P hg S T]
  exact canonical_masked_polya_vinogradov P hinj (S ∩ T) (activePrimes P S T)
    (activePrimes_pairwise_isCoprime P hinj S T) (fun i => hg i.val)
    (fun i => hc i.val) (fun _ => 3) (fun _ => by decide) (fun _ => by decide) W M hM

def supportNorm {α : Type*} (P : α → Ideal O) (S : Finset α) : ℝ :=
  Ideal.absNorm (∏ i ∈ S, P i)

theorem supportNorm_nonneg {α : Type*} (P : α → Ideal O) (S : Finset α) :
    0 ≤ supportNorm P S := Nat.cast_nonneg _

theorem two_pow_card_le_supportNorm {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (S : Finset α) :
    (2 : ℝ) ^ S.card ≤ supportNorm P S := by
  have hnorm (i : α) : (2 : ℝ) ≤ Ideal.absNorm (P i) := by
    have h0 : Ideal.absNorm (P i) ≠ 0 := by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]
      exact NeZero.ne (P i)
    have h1 : Ideal.absNorm (P i) ≠ 1 := by
      rw [ne_eq, Ideal.absNorm_eq_one_iff]
      exact (inferInstance : (P i).IsMaximal).ne_top
    exact_mod_cast (show 2 ≤ Ideal.absNorm (P i) by omega)
  change (2 : ℝ) ^ S.card ≤ (Ideal.absNorm (∏ i ∈ S, P i) : ℝ)
  rw [map_prod, Nat.cast_prod]
  calc
    _ = ∏ _i ∈ S, (2 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => by norm_num) (fun i _ => hnorm i)

theorem divisor_conductor_bound {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (S T : Finset α)
    (N : ℝ) (hN : 0 ≤ N) (hS : supportNorm P S ≤ N) (hT : supportNorm P T ≤ N) :
    (2 : ℝ) ^ (S ∩ T).card *
      ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖ ≤ N := by
  have hid := congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ))
    (activeSupport_product_mul_common_sq P S T)
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow] at hid
  rw [← activePrimeModulus_norm_sq] at hid
  change ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖ ^ 2 *
    (supportNorm P (S ∩ T)) ^ 2 = supportNorm P S * supportNorm P T at hid
  have hpow := two_pow_card_le_supportNorm P (S ∩ T)
  have hmul := mul_le_mul_of_nonneg_right hpow
    (norm_nonneg (eisEmbedding (finitePrimeModulus (activePrimes P S T))))
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (2 : ℝ) ^ (S ∩ T).card *
    ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖) hmul 2
  have hprod := mul_le_mul hS hT (supportNorm_nonneg P T) hN
  nlinarith

theorem quadratic_gram_offdiagonal_of_norm_le {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, lambda ∉ P i) (hc : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (S T : Finset α) (hne : S ≠ T) (N : ℝ) (hN : 0 ≤ N)
    (hS : supportNorm P S ≤ N) (hT : supportNorm P T ≤ N)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, (star (quadraticRow P hg S z) * quadraticRow P hg T z) *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤ pvControl W * N := by
  apply (quadratic_gram_offdiagonal P hinj hg hc S T hne W M hM).trans
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (divisor_conductor_bound P S T N hN hS hT)
    (pvControl_nonneg W)

def diagonalControl (W : 𝓢(ℝ, ℂ)) : ℝ :=
  16 * (1 + Real.pi) ^ 2 *
    (Finset.Iic (2, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W

theorem diagonalControl_nonneg (W : 𝓢(ℝ, ℂ)) : 0 ≤ diagonalControl W := by
  unfold diagonalControl
  positivity

theorem radial_weight_lattice_bound (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    (∑' z : O, ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) ≤ diagonalControl W * M := by
  have hMp : 0 < M := by linarith
  let t := M⁻¹
  have ht : 0 < t := inv_pos.mpr hMp
  have ht1 : t ≤ 1 := (inv_le_one₀ hMp).mpr hM
  let B := 4 * (Finset.Iic (2, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hp (z : O) : ‖W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      B * ((1 + t * ‖eisEmbedding z‖ ^ 2) ^ 2)⁻¹ := by
    have hq : 0 ≤ ‖eisEmbedding z‖ ^ 2 / M := div_nonneg (sq_nonneg _) hMp.le
    have hh := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (2, 0)) (k := 2) (n := 0) le_rfl le_rfl W (‖eisEmbedding z‖ ^ 2 / M)
    simp only [norm_iteratedFDeriv_zero, Real.norm_of_nonneg hq] at hh
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hh
    change (1 + ‖eisEmbedding z‖ ^ 2 / M) ^ 2 * ‖W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤ B at hh
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [t, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh
  have hs : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hMp)
  have hb := hs.tsum_le_tsum hp ((scaled_eisenstein_cauchy_summable t ht).mul_left B)
  rw [tsum_mul_left] at hb
  have hsmall := scaled_eisenstein_cauchy_small t ht ht1
  have hmul := mul_le_mul_of_nonneg_left hb ht.le
  have hcontrol := mul_le_mul_of_nonneg_left hsmall hB
  have hfinal : t * (∑' z : O, ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) ≤ diagonalControl W := by
    unfold diagonalControl
    dsimp [B] at hcontrol hmul
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hfinal hMp.le
  simpa only [t, ← mul_assoc, mul_inv_cancel₀ hMp.ne', one_mul, mul_comm] using hh

theorem quadraticRow_norm_le_one {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset α) (z : O) :
    ‖quadraticRow P hg S z‖ ≤ 1 := by
  rw [quadraticRow_eq_canonical]
  exact finiteSexticRow_norm_le_one _ _ _ _

theorem quadratic_pair_summable {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S T : Finset α)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => (star (quadraticRow P hg S z) * quadraticRow P hg T z) *
      W (‖eisEmbedding z‖ ^ 2 / M)) := by
  have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hM)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hW
  intro z
  rw [norm_mul, norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_mul (quadraticRow_norm_le_one P hg S z) (quadraticRow_norm_le_one P hg T z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

theorem quadratic_gram_diagonal {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset α)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    ‖∑' z : O, (star (quadraticRow P hg S z) * quadraticRow P hg S z) *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤ diagonalControl W * M := by
  have hMp : 0 < M := by linarith
  have hs := (quadratic_pair_summable P hg S S W M hMp).norm
  have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hMp)
  refine (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum ?_ hW).trans
    (radial_weight_lattice_bound W M hM))
  intro z
  rw [norm_mul, norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_mul (quadraticRow_norm_le_one P hg S z) (quadraticRow_norm_le_one P hg S z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

private theorem norm_sq_finite_sum {β : Type*} (C : Finset β) (a r : β → ℂ) :
    (↑(‖∑ n ∈ C, a n * r n‖ ^ 2) : ℂ) =
      ∑ n ∈ C, ∑ m ∈ C, (star (a n) * a m) * (star (r n) * r m) := by
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, map_mul, starRingEnd_apply]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem quadratic_mean_summable {α β : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (C : Finset β) (support : β → Finset α) (a : β → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * quadraticRow P hg (support n) z‖ ^ 2) : ℂ)) := by
  have hs := summable_sum (s := C) (fun n hn => summable_sum (s := C) (fun m hm =>
    (quadratic_pair_summable P hg (support n) (support m) W M hM).mul_left (star (a n) * a m)))
  apply hs.congr
  intro z
  rw [norm_sq_finite_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem quadratic_mean_expand {α β : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (C : Finset β) (support : β → Finset α) (a : β → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * quadraticRow P hg (support n) z‖ ^ 2) : ℂ)) =
      ∑ n ∈ C, ∑ m ∈ C, (star (a n) * a m) *
        ∑' z : O, (star (quadraticRow P hg (support n) z) * quadraticRow P hg (support m) z) *
          W (‖eisEmbedding z‖ ^ 2 / M) := by
  let f : β → β → O → ℂ := fun n m z => (star (a n) * a m) *
    ((star (quadraticRow P hg (support n) z) * quadraticRow P hg (support m) z) *
      W (‖eisEmbedding z‖ ^ 2 / M))
  have hf (n m : β) : Summable (f n m) :=
    (quadratic_pair_summable P hg (support n) (support m) W M hM).mul_left _
  have heq (z : O) : W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * quadraticRow P hg (support n) z‖ ^ 2) : ℂ) =
        ∑ n ∈ C, ∑ m ∈ C, f n m z := by
    rw [norm_sq_finite_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    dsimp [f]
    ring
  rw [tsum_congr heq, Summable.tsum_finsetSum (fun n hn => summable_sum (fun m hm => hf n m))]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Summable.tsum_finsetSum (fun m hm => hf n m)]
  apply Finset.sum_congr rfl
  intro m hm
  exact tsum_mul_left

theorem quadratic_initial_mean_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, lambda ∉ P i) (hc : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (C : Finset β) (support : β → Finset α)
    (hsupp : Set.InjOn support (↑C : Set β))
    (N : ℝ) (hN : 0 ≤ N) (hNorm : ∀ n ∈ C, supportNorm P (support n) ≤ N)
    (a : β → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    ‖∑' z : O, W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * quadraticRow P hg (support n) z‖ ^ 2) : ℂ)‖ ≤
        (diagonalControl W * M + pvControl W * N * C.card) * ∑ n ∈ C, ‖a n‖ ^ 2 := by
  have hMp : 0 < M := by linarith
  let D := diagonalControl W * M
  let B := pvControl W * N
  have hB : 0 ≤ B := mul_nonneg (pvControl_nonneg W) hN
  let K : β → β → ℂ := fun n m => ∑' z : O,
    (star (quadraticRow P hg (support n) z) * quadraticRow P hg (support m) z) *
      W (‖eisEmbedding z‖ ^ 2 / M)
  have hK (n : β) (hn : n ∈ C) (m : β) (hm : m ∈ C) :
      ‖K n m‖ ≤ (if n = m then D else 0) + B := by
    by_cases hnm : n = m
    · subst m
      simp only [ite_true]
      exact (quadratic_gram_diagonal P hg (support n) W M hM).trans (le_add_of_nonneg_right hB)
    · simp only [hnm, ite_false, zero_add]
      exact quadratic_gram_offdiagonal_of_norm_le P hinj hg hc _ _
        (fun h => hnm (hsupp hn hm h)) N hN (hNorm n hn) (hNorm m hm) W M hMp
  have heq (n : β) (hn : n ∈ C) :
      (∑ m ∈ C, ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B)) =
        D * ‖a n‖ ^ 2 + B * ‖a n‖ * ∑ m ∈ C, ‖a m‖ := by
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq,  hn, ite_true]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hcalc : (∑ n ∈ C, ∑ m ∈ C,
      ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B)) =
      D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * (∑ n ∈ C, ‖a n‖) ^ 2 := by
    rw [Finset.sum_congr rfl heq]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [quadratic_mean_expand P hg C support a W M hMp]
  calc
    _ ≤ ∑ n ∈ C, ∑ m ∈ C, ‖(star (a n) * a m) * K n m‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ n ∈ C, ∑ m ∈ C, ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B) := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      simp only [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (hK n hn m hm) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * (∑ n ∈ C, ‖a n‖) ^ 2 := hcalc
    _ ≤ D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * ((C.card : ℝ) * ∑ n ∈ C, ‖a n‖ ^ 2) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ hB
      simpa only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, mul_comm] using
        Finset.sum_mul_sq_le_sq_mul_sq C (fun n => ‖a n‖) (fun _ => (1 : ℝ))
    _ = _ := by dsimp [D, B]; ring

def sieveBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def sieveCutoff : 𝓢(ℝ, ℂ) := by
  have hc : HasCompactSupport (fun t : ℝ => (sieveBump t : ℂ)) :=
    sieveBump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hs : ContDiff ℝ ∞ (fun t : ℝ => (sieveBump t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp sieveBump.contDiff
  exact hc.toSchwartzMap hs

@[simp] theorem sieveCutoff_apply (t : ℝ) : sieveCutoff t = (sieveBump t : ℂ) := rfl

theorem sieveBump_eq_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : sieveBump t = 1 := by
  apply sieveBump.one_of_mem_closedBall
  change dist t 0 ≤ 1
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht0] using ht1

theorem quadratic_initial_finite_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, lambda ∉ P i) (hc : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (C : Finset β) (support : β → Finset α) (hsupp : Set.InjOn support (↑C : Set β))
    (N : ℝ) (hN : 0 ≤ N) (hNorm : ∀ n ∈ C, supportNorm P (support n) ≤ N)
    (a : β → ℂ) (M : ℝ) (hM : 1 ≤ M) (R : Finset O)
    (hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M) :
    (∑ z ∈ R, ‖∑ n ∈ C, a n * quadraticRow P hg (support n) z‖ ^ 2) ≤
      (diagonalControl sieveCutoff * M + pvControl sieveCutoff * N * C.card) *
        ∑ n ∈ C, ‖a n‖ ^ 2 := by
  have hMp : 0 < M := by linarith
  let E : O → ℝ := fun z => ‖∑ n ∈ C, a n * quadraticRow P hg (support n) z‖ ^ 2
  let F : O → ℝ := fun z => sieveBump (‖eisEmbedding z‖ ^ 2 / M) * E z
  let H : O → ℂ := fun z => sieveCutoff (‖eisEmbedding z‖ ^ 2 / M) * (E z : ℂ)
  have hF (z : O) : 0 ≤ F z := mul_nonneg sieveBump.nonneg (sq_nonneg _)
  have hH (z : O) : H z = (F z : ℂ) := by
    simp only [H, F, sieveCutoff_apply, Complex.ofReal_mul]
  have hHs : Summable H := quadratic_mean_summable P hg C support a sieveCutoff M hMp
  have hFs : Summable F := hHs.norm.congr (fun z => by
    rw [hH, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hF z)])
  have hsum : ‖∑' z : O, H z‖ = ∑' z : O, F z := by
    rw [tsum_congr hH, ← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (tsum_nonneg hF)]
  calc
    _ = ∑ z ∈ R, F z := by
      apply Finset.sum_congr rfl
      intro z hz
      have ht0 : 0 ≤ ‖eisEmbedding z‖ ^ 2 / M := div_nonneg (sq_nonneg _) hMp.le
      have ht1 : ‖eisEmbedding z‖ ^ 2 / M ≤ 1 := (div_le_one hMp).mpr (hR z hz)
      simp only [F, sieveBump_eq_one ht0 ht1, one_mul, E]
    _ ≤ ∑' z : O, F z := hFs.sum_le_tsum R (fun z _ => hF z)
    _ = ‖∑' z : O, H z‖ := hsum.symm
    _ ≤ _ := quadratic_initial_mean_bound P hinj hg hc C support hsupp N hN hNorm
      a sieveCutoff M hM

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open ConcretePrimeRowBridge ShortDraftHeckeBridge

def initialSieveConstant : ℝ :=
  diagonalControl sieveCutoff + 128 * pvControl sieveCutoff + 1

theorem initialSieveConstant_pos : 0 < initialSieveConstant := by
  have := diagonalControl_nonneg sieveCutoff
  have := pvControl_nonneg sieveCutoff
  unfold initialSieveConstant
  positivity

theorem ideal_initial_quadratic_sieve
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hsq : ∀ I ∈ F, Squarefree I)
    (hchar : ∀ i : primePool F, ringChar (O ⧸ i.val) ≠ 2)
    (N : ℕ) (hN : 1 ≤ N) (hnorm : ∀ I ∈ F, Ideal.absNorm I ≤ N)
    (a : Ideal O → ℂ) (M : ℝ) (hM : 1 ≤ M) (R : Finset O)
    (hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M) :
    (∑ z ∈ R, ‖∑ I ∈ F, a I * (idealSexticRow F hFpos hFgood I z) ^ 3‖ ^ 2) ≤
      initialSieveConstant * (M + (N : ℝ) ^ 2) * ∑ I ∈ F, ‖a I‖ ^ 2 := by
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsupp : Set.InjOn (idealSupport F) (↑F : Set (Ideal O)) := by
    intro I hI J hJ h
    exact idealSupport_injective_on_squarefree F hI hJ (hsq I hI) (hsq J hJ) h
  have hNorm (I : Ideal O) (hI : I ∈ F) :
      supportNorm (fun i : primePool F => i.val) (idealSupport F I) ≤ (N : ℝ) := by
    unfold supportNorm
    rw [idealSupport_product_eq F hI (hsq I hI)]
    exact_mod_cast hnorm I hI
  have hb := quadratic_initial_finite_bound (fun i : primePool F => i.val)
    Subtype.val_injective (primePool_good F hFgood) hchar F (idealSupport F) hsupp
    (N : ℝ) (by positivity) hNorm a M hM R hR
  change (∑ z ∈ R, ‖∑ I ∈ F, a I * (idealSexticRow F hFpos hFgood I z) ^ 3‖ ^ 2) ≤
    (diagonalControl sieveCutoff * M + pvControl sieveCutoff * (N : ℝ) * F.card) *
      ∑ I ∈ F, ‖a I‖ ^ 2 at hb
  have hsub : F ⊆ idealsUpTo N := by
    intro I hI
    apply mem_idealsUpTo.mpr
    constructor
    · apply Nat.one_le_iff_ne_zero.mpr
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]
      exact hFpos I hI
    · exact hnorm I hI
  have hcardNat : F.card ≤ 64 * (N + 1) :=
    (Finset.card_le_card hsub).trans (CompactScaleBridge.idealsUpTo_card_le N)
  have hcard : (F.card : ℝ) ≤ 128 * (N : ℝ) := by
    have hh : (F.card : ℝ) ≤ 64 * ((N : ℝ) + 1) := by exact_mod_cast hcardNat
    linarith
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hdiag := diagonalControl_nonneg sieveCutoff
  have hpv := pvControl_nonneg sieveCutoff
  have hmul := mul_le_mul_of_nonneg_left hcard (mul_nonneg hpv (by positivity : (0 : ℝ) ≤ N))
  unfold initialSieveConstant
  nlinarith [mul_nonneg hdiag (sq_nonneg (N : ℝ)),
    mul_nonneg hpv (show 0 ≤ M by linarith)]

end QuadraticInitialBound

open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory

namespace CubicReflectionKernel

def gammaMultiplier (s : ℂ) : ℂ :=
  Complex.Gamma ((7 / 6 : ℂ) + s) * Complex.Gamma ((5 / 6 : ℂ) + s) /
    (Complex.Gamma ((7 / 6 : ℂ) - s) * Complex.Gamma ((5 / 6 : ℂ) - s))

theorem gammaMultiplier_neg (s : ℂ) : gammaMultiplier (-s) = (gammaMultiplier s)⁻¹ := by
  simp only [gammaMultiplier, sub_neg_eq_add, ← sub_eq_add_neg, inv_div]

theorem Gamma_vertical_ne_zero (a u : ℝ) (ha : 0 < a) :
    Complex.Gamma ((a : ℂ) + u * Complex.I) ≠ 0 := by
  apply Complex.Gamma_ne_zero_of_re_pos
  simpa using ha

theorem Gamma_vertical_conj (a u : ℝ) :
    Complex.Gamma ((a : ℂ) - u * Complex.I) =
      star (Complex.Gamma ((a : ℂ) + u * Complex.I)) := by
  change _ = (starRingEnd ℂ) (Complex.Gamma ((a : ℂ) + u * Complex.I))
  rw [← Complex.Gamma_conj]
  congr 1
  simp [sub_eq_add_neg]

theorem gammaMultiplier_norm_imaginary (u : ℝ) :
    ‖gammaMultiplier (u * Complex.I)‖ = 1 := by
  have ha := Gamma_vertical_ne_zero (7 / 6) u (by norm_num)
  have hb := Gamma_vertical_ne_zero (5 / 6) u (by norm_num)
  have hca := Gamma_vertical_conj (7 / 6) u
  have hcb := Gamma_vertical_conj (5 / 6) u
  push_cast at ha hb hca hcb
  rw [gammaMultiplier, hca, hcb, norm_div, norm_mul, norm_mul, norm_star, norm_star]
  exact div_self (mul_ne_zero (norm_ne_zero_iff.mpr ha) (norm_ne_zero_iff.mpr hb))

theorem Gamma_vertical_continuous (a : ℝ) (ha : 0 < a) :
    Continuous (fun u : ℝ => Complex.Gamma ((a : ℂ) + u * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  apply (Complex.continuousAt_Gamma _ ?_).comp
  · fun_prop
  · intro n hn
    have heq := congrArg Complex.re hn
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.neg_re, Complex.natCast_re] at heq
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

def axisMultiplier (u : ℝ) : ℂ := gammaMultiplier ((2 * Real.pi * u : ℝ) * Complex.I)

theorem axisMultiplier_norm (u : ℝ) : ‖axisMultiplier u‖ = 1 :=
  gammaMultiplier_norm_imaginary _

theorem axisMultiplier_continuous : Continuous axisMultiplier := by
  have h1 := (Gamma_vertical_continuous (7 / 6) (by norm_num)).comp
    (show Continuous (fun u : ℝ => 2 * Real.pi * u) by fun_prop)
  have h2 := (Gamma_vertical_continuous (5 / 6) (by norm_num)).comp
    (show Continuous (fun u : ℝ => 2 * Real.pi * u) by fun_prop)
  have h3 := (Gamma_vertical_continuous (7 / 6) (by norm_num)).comp
    (show Continuous (fun u : ℝ => -(2 * Real.pi * u)) by fun_prop)
  have h4 := (Gamma_vertical_continuous (5 / 6) (by norm_num)).comp
    (show Continuous (fun u : ℝ => -(2 * Real.pi * u)) by fun_prop)
  have hd := h3.mul h4
  have hne (u : ℝ) :
      Complex.Gamma ((7 / 6 : ℝ) + (-(2 * Real.pi * u) : ℝ) * Complex.I) *
      Complex.Gamma ((5 / 6 : ℝ) + (-(2 * Real.pi * u) : ℝ) * Complex.I) ≠ 0 :=
    mul_ne_zero (Gamma_vertical_ne_zero _ _ (by norm_num)) (Gamma_vertical_ne_zero _ _ (by norm_num))
  convert (h1.mul h2).div hd hne using 1
  ext u
  simp only [axisMultiplier, gammaMultiplier, Function.comp_def, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg,
    Pi.div_apply, Pi.mul_apply]

def spectralProfile (logSource : SchwartzMap ℝ ℂ) (u : ℝ) : ℂ := axisMultiplier u * (𝓕 logSource) u

theorem spectralProfile_norm (logSource : SchwartzMap ℝ ℂ) (u : ℝ) :
    ‖spectralProfile logSource u‖ = ‖(𝓕 logSource) u‖ := by
  rw [spectralProfile, norm_mul, axisMultiplier_norm, one_mul]

theorem spectralProfile_continuous (logSource : SchwartzMap ℝ ℂ) : Continuous (spectralProfile logSource) :=
  axisMultiplier_continuous.mul (𝓕 logSource).continuous

theorem spectralProfile_moment_integrable (logSource : SchwartzMap ℝ ℂ) (j : ℕ) :
    Integrable (fun u : ℝ => ‖u‖ ^ j * ‖spectralProfile logSource u‖) := by
  simpa only [spectralProfile_norm] using (𝓕 logSource).integrable_pow_mul volume j

theorem spectralProfile_pow_integrable (logSource : SchwartzMap ℝ ℂ) (j : ℕ) :
    Integrable (fun u : ℝ => u ^ j • spectralProfile logSource u) := by
  apply (spectralProfile_moment_integrable logSource j).mono'
    ((show Continuous (fun u : ℝ => u ^ j • spectralProfile logSource u) by
      exact (continuous_id.pow j).smul (spectralProfile_continuous logSource)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun u => by simp only [norm_smul, norm_pow, le_rfl])

def reflectedLogProfile (logSource : SchwartzMap ℝ ℂ) : ℝ → ℂ := 𝓕 (spectralProfile logSource)

theorem reflectedLogProfile_smooth (logSource : SchwartzMap ℝ ℂ) :
    ContDiff ℝ ∞ (reflectedLogProfile logSource) :=
  Real.contDiff_fourier (fun j _ => spectralProfile_moment_integrable logSource j)

theorem reflectedLogProfile_deriv (logSource : SchwartzMap ℝ ℂ) (j : ℕ) :
    iteratedDeriv j (reflectedLogProfile logSource) =
      𝓕 (fun u : ℝ => (-2 * Real.pi * Complex.I * u) ^ j * spectralProfile logSource u) := by
  simpa only [reflectedLogProfile, smul_eq_mul] using
    (Real.iteratedDeriv_fourier (N := (⊤ : ℕ∞))
      (fun n _ => spectralProfile_pow_integrable logSource n) (by simp : (j : ℕ∞) ≤ ⊤))

end CubicReflectionKernel

end

end OAI
end OAIOriginalModule0097

/-! Original module: OAI.NumberTheory.DirichletL.Mellin.ReflectedKernel
Source SHA256: 1b8cdac8957ad098d2834e9ddc30a6653abd526dd91632e5477dfc8525e2a1e6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0098


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

namespace CubicReflectionKernel

section
open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory

theorem reflectedLogProfile_deriv_bound (logSource : SchwartzMap ℝ ℂ) (j : ℕ) (y : ℝ) :
    ‖iteratedDeriv j (reflectedLogProfile logSource) y‖ ≤
      (2 * Real.pi) ^ j * ∫ u : ℝ, ‖u‖ ^ j * ‖(𝓕 logSource) u‖ := by
  rw [reflectedLogProfile_deriv]
  have hb := VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (innerₗ ℝ)
    (fun u : ℝ => (-2 * Real.pi * Complex.I * u) ^ j * spectralProfile logSource u) y
  change ‖𝓕 (fun u : ℝ => (-2 * Real.pi * Complex.I * u) ^ j * spectralProfile logSource u) y‖ ≤ _ at hb
  refine hb.trans_eq ?_
  have hnorm (u : ℝ) :
      ‖(-2 * Real.pi * Complex.I * u) ^ j * spectralProfile logSource u‖ =
        (2 * Real.pi) ^ j * (‖u‖ ^ j * ‖(𝓕 logSource) u‖) := by
    simp only [norm_mul, norm_pow, spectralProfile_norm, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  simp_rw [hnorm]
  exact integral_const_mul _ _

def momentScale : ℝ :=
  2 ^ (volume : Measure ℝ).integrablePower *
    ∫ u : ℝ, (1 + ‖u‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)

theorem momentScale_nonneg : 0 ≤ momentScale := by
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro u
  positivity

theorem reflectedLogProfile_source_bound (j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (logSource : SchwartzMap ℝ ℂ) (y : ℝ),
        ‖iteratedDeriv j (reflectedLogProfile logSource) y‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource := by
  let m := j + (volume : Measure ℝ).integrablePower
  let S : Finset (ℕ × ℕ) := {(0, 0), (m, 0)}
  obtain ⟨s, C, hC, hbound⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control (E := ℝ)
    (FourierTransform.fourierCLM ℝ (SchwartzMap ℝ ℂ)) S
  refine ⟨s, (2 * Real.pi) ^ j * (momentScale + 1) * (2 * C), by
    have := momentScale_nonneg
    positivity, ?_⟩
  intro logSource y
  have h0' : schwartzSeminormFamily ℝ ℝ ℂ (0, 0) ≤
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
    Finset.le_sup (f := schwartzSeminormFamily ℝ ℝ ℂ) (by simp [S])
  have hm' : schwartzSeminormFamily ℝ ℝ ℂ (m, 0) ≤
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
    Finset.le_sup (f := schwartzSeminormFamily ℝ ℝ ℂ) (by simp [S])
  have h0 := Seminorm.le_def.mp h0' (𝓕 logSource)
  have hm := Seminorm.le_def.mp hm' (𝓕 logSource)
  change SchwartzMap.seminorm ℝ 0 0 (𝓕 logSource) ≤ _ at h0
  change SchwartzMap.seminorm ℝ m 0 (𝓕 logSource) ≤ _ at hm
  have hs := hbound logSource
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (𝓕 logSource) ≤ _ at hs
  have hsum : SchwartzMap.seminorm ℝ 0 0 (𝓕 logSource) + SchwartzMap.seminorm ℝ m 0 (𝓕 logSource) ≤
      2 * C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource := by linarith
  have hmoment := FourierBridge.fourier_coefficient_moment logSource j
  change (∫ u : ℝ, ‖u‖ ^ j * ‖(𝓕 logSource) u‖) ≤ momentScale *
    (SchwartzMap.seminorm ℝ 0 0 (𝓕 logSource) + SchwartzMap.seminorm ℝ m 0 (𝓕 logSource)) at hmoment
  calc
    _ ≤ (2 * Real.pi) ^ j * ∫ u : ℝ, ‖u‖ ^ j * ‖(𝓕 logSource) u‖ :=
      reflectedLogProfile_deriv_bound logSource j y
    _ ≤ (2 * Real.pi) ^ j * (momentScale *
        (2 * C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource)) := by
      exact mul_le_mul_of_nonneg_left
        (hmoment.trans (mul_le_mul_of_nonneg_left hsum momentScale_nonneg)) (by positivity)
    _ ≤ _ := by
      have hpos : 0 ≤ 2 * C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource := by positivity
      calc
        _ ≤ (2 * Real.pi) ^ j * ((momentScale + 1) *
            (2 * C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right zero_le_one) hpos) (by positivity)
        _ = _ := by ring

end

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Asymptotics

def paperScale : ℝ := (2 * Real.pi) ^ 4 / 27

theorem paperScale_pos : 0 < paperScale := by
  unfold paperScale
  positivity

def paperKernel (V : ℝ → ℂ) (x : ℝ) : ℂ :=
  mellinInv 0 (fun t => mellin V (-t) * gammaMultiplier t) (paperScale * x)

theorem logProfile_compact (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) :
    HasCompactSupport (fun u : ℝ => V (Real.exp u)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (Real.log a) (Real.log b)) isCompact_Icc
  intro u hu
  have huv : V (Real.exp u) ≠ 0 := hu
  have hm := hsupp huv
  constructor
  · simpa only [Real.log_exp] using Real.log_le_log ha hm.1
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos u) hm.2

def logSchwartz (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) :
    SchwartzMap ℝ ℂ :=
  (logProfile_compact V a b ha hsupp).toSchwartzMap (hV.comp Real.contDiff_exp)

@[simp] theorem logSchwartz_apply (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) (u : ℝ) :
    logSchwartz V a b ha hsupp hV u = V (Real.exp u) := rfl

theorem compact_source_mellin_convergent
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) : MellinConvergent V s := by
  have hlocal : LocallyIntegrableOn V (Set.Ioi (0 : ℝ)) :=
    hV.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htopzero : V =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_gt_atTop b] with y hy
    by_contra hn
    exact (not_le_of_gt hy) (hsupp hn).2
  have hbotzero : V =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT ha] with y hy
    by_contra hn
    exact (not_le_of_gt hy.2) (hsupp hn).1
  have htop : V =O[atTop] (fun y : ℝ => y ^ (-(s.re + 1))) :=
    htopzero.isBigO.trans (isBigO_zero _ _)
  have hbot : V =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-(s.re - 1))) :=
    hbotzero.isBigO.trans (isBigO_zero _ _)
  exact mellinConvergent_of_isBigO_rpow hlocal htop (by linarith)
    hbot (by linarith)

theorem mellin_axis_eq_fourier (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (u : ℝ) :
    mellin V (-((2 * Real.pi * u : ℝ) * Complex.I)) = (𝓕 logSource) u := by
  rw [mellin_eq_fourier]
  have hfreq : (-((2 * Real.pi * u : ℝ) * Complex.I) : ℂ).im / (2 * Real.pi) = -u := by
    simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]
    field_simp
  rw [hfreq]
  have hfun : (fun v : ℝ => Real.exp
      (-(-((2 * Real.pi * u : ℝ) * Complex.I) : ℂ).re * v) • V (Real.exp (-v))) =
      (logSource : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ := by
    funext v
    simp [hL]
  rw [hfun, Real.fourier_comp_linearIsometry]
  simp
  rfl

theorem paperKernel_eq_logFourier (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (x : ℝ) (hx : 0 < x) :
    paperKernel V x = reflectedLogProfile logSource (Real.log (paperScale * x)) := by
  unfold paperKernel
  rw [mellinInv_eq_fourierInv 0 _ (mul_pos paperScale_pos hx)]
  simp only [Complex.ofReal_zero, neg_zero, Complex.cpow_zero, one_smul]
  rw [Real.fourierInv_eq_fourier_neg, neg_neg]
  have hfun : (fun y : ℝ => mellin V (-(0 + 2 * Real.pi * y * Complex.I)) *
      gammaMultiplier (0 + 2 * Real.pi * y * Complex.I)) = spectralProfile logSource := by
    funext y
    have hy : (0 + 2 * Real.pi * y * Complex.I : ℂ) =
        ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hy, mellin_axis_eq_fourier V logSource hL]
    exact mul_comm _ _
  rw [hfun]
  rfl

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter
namespace CubicReflectionKernel

theorem kernel_vertical_eq_spectralProfile (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (y : ℝ) :
    mellin V (-(y * Complex.I)) * gammaMultiplier (y * Complex.I) =
      spectralProfile logSource (y / (2 * Real.pi)) := by
  have hy : 2 * Real.pi * (y / (2 * Real.pi)) = y := by field_simp
  rw [spectralProfile, axisMultiplier, ← mellin_axis_eq_fourier V logSource hL, hy]
  exact mul_comm _ _

theorem kernel_vertical_integrable (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) :
    Complex.VerticalIntegrable (fun t => mellin V (-t) * gammaMultiplier t) 0 := by
  have hi : Integrable (spectralProfile logSource) := by
    simpa using spectralProfile_pow_integrable logSource 0
  have hscaled := hi.comp_div (R := 2 * Real.pi) (by positivity)
  simpa only [Complex.VerticalIntegrable, Complex.ofReal_zero, zero_add,
    kernel_vertical_eq_spectralProfile V logSource hL] using hscaled

theorem paperKernel_integrable (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (x : ℝ) (hx : 0 < x) :
    Integrable (fun y : ℝ => ((paperScale * x : ℝ) : ℂ) ^ (-(y * Complex.I)) *
      (mellin V (-(y * Complex.I)) * gammaMultiplier (y * Complex.I))) := by
  have hcx := mul_pos paperScale_pos hx
  have hi := kernel_vertical_integrable V logSource hL
  simp only [Complex.VerticalIntegrable, Complex.ofReal_zero, zero_add] at hi
  apply hi.bdd_mul (c := 1)
  · exact ((show Continuous (fun y : ℝ => -(y * Complex.I)) by fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt hcx)))).aestronglyMeasurable
  · filter_upwards [] with y
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hcx]
    simp

theorem paperKernel_contDiffOn (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) :
    ContDiffOn ℝ ∞ (paperKernel V) (Set.Ioi 0) := by
  have hg : ContDiffOn ℝ ∞
      (fun x => reflectedLogProfile logSource (Real.log (paperScale * x))) (Set.Ioi 0) := by
    intro x hx
    apply (reflectedLogProfile_smooth logSource).contDiffAt.comp_contDiffWithinAt x
    exact ((contDiffAt_const.mul contDiffAt_id).log
      (ne_of_gt (mul_pos paperScale_pos hx))).contDiffWithinAt
  apply hg.congr
  intro x hx
  exact paperKernel_eq_logFourier V logSource hL x hx

theorem paperKernel_euler_eq (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (j : ℕ) (x : ℝ) (hx : 0 < x) :
    LocalLogFourier.eulerDeriv (paperKernel V) j x =
      iteratedDeriv j (reflectedLogProfile logSource) (Real.log (paperScale * x)) := by
  have hfun : (fun t : ℝ => paperKernel V (x * Real.exp t)) =
      (fun t : ℝ => reflectedLogProfile logSource (Real.log (paperScale * x) + t)) := by
    funext t
    rw [paperKernel_eq_logFourier V logSource hL _ (mul_pos hx (Real.exp_pos t))]
    rw [← mul_assoc, Real.log_mul (ne_of_gt (mul_pos paperScale_pos hx))
      (ne_of_gt (Real.exp_pos t)), Real.log_exp]
  rw [LocalLogFourier.eulerDeriv, hfun, iteratedDeriv_comp_const_add]
  simp

theorem paperKernel_source_euler_bound (j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
        (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
        (x : ℝ), 0 < x →
        ‖LocalLogFourier.eulerDeriv (paperKernel V) j x‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (logSchwartz V a b ha hsupp hV) := by
  obtain ⟨s, C, hC, hb⟩ := reflectedLogProfile_source_bound j
  refine ⟨s, C, hC, ?_⟩
  intro V a b ha hsupp hV x hx
  rw [paperKernel_euler_eq V (logSchwartz V a b ha hsupp hV) (by intro u; rfl) j x hx]
  exact hb _ _

theorem paperKernel_compact_source_integrable
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (x : ℝ) (hx : 0 < x) :
    Integrable (fun y : ℝ => ((paperScale * x : ℝ) : ℂ) ^ (-(y * Complex.I)) *
      (mellin V (-(y * Complex.I)) * gammaMultiplier (y * Complex.I))) :=
  paperKernel_integrable V (logSchwartz V a b ha hsupp hV) (by intro u; rfl) x hx

theorem paperKernel_compact_source_smooth
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) :
    ContDiffOn ℝ ∞ (paperKernel V) (Set.Ioi 0) :=
  paperKernel_contDiffOn V (logSchwartz V a b ha hsupp hV) (by intro u; rfl)

theorem reflectedLogProfile_deriv_vanish (logSource : SchwartzMap ℝ ℂ) (j : ℕ) :
    Tendsto (iteratedDeriv j (reflectedLogProfile logSource)) (cocompact ℝ) (𝓝 0) := by
  rw [reflectedLogProfile_deriv]
  exact Real.zero_at_infty_fourier _

theorem paperKernel_euler_vanish_infty (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (j : ℕ) :
    Tendsto (LocalLogFourier.eulerDeriv (paperKernel V) j) atTop (𝓝 0) := by
  have hd := (reflectedLogProfile_deriv_vanish logSource j).mono_left atTop_le_cocompact
  have hlog : Tendsto (fun x : ℝ => Real.log (paperScale * x)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Tendsto.const_mul_atTop paperScale_pos tendsto_id)
  apply (hd.comp hlog).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (paperKernel_euler_eq V logSource hL j x hx).symm

theorem paperKernel_euler_vanish_zero (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (j : ℕ) :
    Tendsto (LocalLogFourier.eulerDeriv (paperKernel V) j) (𝓝[>] 0) (𝓝 0) := by
  have hd := (reflectedLogProfile_deriv_vanish logSource j).mono_left atBot_le_cocompact
  have hmul : Tendsto (fun x : ℝ => paperScale * x) (𝓝[>] 0) (𝓝[>] 0) := by
    have hm : Tendsto (fun x : ℝ => paperScale * x)
        (comap (fun x : ℝ => paperScale * x) (𝓝[>] 0)) (𝓝[>] 0) := tendsto_comap
    rwa [comap_mulLeft_nhdsGT_zero paperScale_pos] at hm
  have hlog := Real.tendsto_log_nhdsGT_zero.comp hmul
  apply (hd.comp hlog).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (paperKernel_euler_eq V logSource hL j x hx).symm

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Asymptotics

theorem compact_source_mellin_hasDerivAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) :
    HasDerivAt (mellin V) (mellin (fun t => Real.log t • V t) s) s := by
  have hlocal : LocallyIntegrableOn V (Set.Ioi (0 : ℝ)) :=
    hV.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htopzero : V =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_gt_atTop b] with y hy
    by_contra hn
    exact (not_le_of_gt hy) (hsupp hn).2
  have hbotzero : V =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT ha] with y hy
    by_contra hn
    exact (not_le_of_gt hy.2) (hsupp hn).1
  have htop : V =O[atTop] (fun y : ℝ => y ^ (-(s.re + 1))) :=
    htopzero.isBigO.trans (isBigO_zero _ _)
  have hbot : V =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-(s.re - 1))) :=
    hbotzero.isBigO.trans (isBigO_zero _ _)
  exact (mellin_hasDerivAt_of_isBigO_rpow hlocal htop (by linarith)
    hbot (by linarith)).2

theorem compact_source_mellin_differentiable
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) :
    Differentiable ℂ (mellin V) :=
  fun s => (compact_source_mellin_hasDerivAt V a b ha hsupp hV s).differentiableAt

theorem Gamma_differentiableAt_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.Gamma z := by
  apply Complex.differentiableAt_Gamma
  intro m hm
  have hr := congrArg Complex.re hm
  simp only [Complex.neg_re, Complex.natCast_re] at hr
  have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem gammaMultiplier_differentiableAt (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ gammaMultiplier s := by
  have h1 := (Gamma_differentiableAt_of_re_pos ((7 / 6 : ℂ) + s) (by
    norm_num [Complex.add_re, Complex.div_re]
    linarith)).comp s (differentiableAt_const _ |>.add differentiableAt_id)
  have h2 := (Gamma_differentiableAt_of_re_pos ((5 / 6 : ℂ) + s) (by
    norm_num [Complex.add_re, Complex.div_re]
    linarith)).comp s (differentiableAt_const _ |>.add differentiableAt_id)
  have h3 := (Complex.differentiable_one_div_Gamma ((7 / 6 : ℂ) - s)).comp s
    (differentiableAt_const _ |>.sub differentiableAt_id)
  have h4 := (Complex.differentiable_one_div_Gamma ((5 / 6 : ℂ) - s)).comp s
    (differentiableAt_const _ |>.sub differentiableAt_id)
  convert ((h1.mul h2).mul (h3.mul h4)) using 1
  ext z
  simp only [gammaMultiplier, Function.comp_def, div_eq_mul_inv, mul_inv_rev, Pi.mul_apply]
  ring

theorem kernelMellinIntegrand_differentiableAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (fun t => mellin V (-t) * gammaMultiplier t) s := by
  exact ((compact_source_mellin_differentiable V a b ha hsupp hV (-s)).comp s
    differentiableAt_id.neg).mul (gammaMultiplier_differentiableAt s hs)

end CubicReflectionKernel

open scoped BigOperators Classical

namespace DescentWeightedCauchy

theorem weighted_cauchy_sq {ι : Type*} (s : Finset ι)
    (w U V : ι → ℂ) :
    ‖∑ i ∈ s, w i * U i * star (V i)‖ ^ 2 ≤
      (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2) := by
  have hnorm : ‖∑ i ∈ s, w i * U i * star (V i)‖ ≤
      ∑ i ∈ s, ‖w i‖ * ‖U i‖ * ‖V i‖ := by
    simpa only [norm_mul, norm_star] using
      norm_sum_le s (fun i => w i * U i * star (V i))
  calc
    _ ≤ (∑ i ∈ s, ‖w i‖ * ‖U i‖ * ‖V i‖) ^ 2 :=
      sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ => by positivity)) |>.mpr hnorm
    _ ≤ _ := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (fun i _ => by positivity) (fun i _ => by positivity)
      (fun i _ => by ring_nf; exact le_rfl)

theorem weighted_cauchy {ι : Type*} (s : Finset ι)
    (w U V : ι → ℂ) :
    ‖∑ i ∈ s, w i * U i * star (V i)‖ ≤
      Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2) := by
  have h1 : 0 ≤ ∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => by positivity)
  have h2 : 0 ≤ ∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => by positivity)
  have hs := weighted_cauchy_sq s w U V
  have he1 := Real.sq_sqrt h1
  have he2 := Real.sq_sqrt h2
  have hp : (Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2)) ^ 2 =
      (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2) := by rw [mul_pow, he1, he2]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (hp ▸ hs)

theorem weighted_energy_pushforward {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (f : ι → κ) (w : ι → ℂ)
    (P : κ → ℂ) (B : κ → ℝ)
    (hmap : ∀ i ∈ s, f i ∈ t)
    (hfib : ∀ y ∈ t, (∑ i ∈ s with f i = y, ‖w i‖) ≤ B y) :
    (∑ i ∈ s, ‖w i‖ * ‖P (f i)‖ ^ 2) ≤
      ∑ y ∈ t, B y * ‖P y‖ ^ 2 := by
  calc
    _ = ∑ y ∈ t, ∑ i ∈ s with f i = y, ‖w i‖ * ‖P (f i)‖ ^ 2 := by
      symm
      exact Finset.sum_fiberwise_of_maps_to hmap _
    _ = ∑ y ∈ t, (∑ i ∈ s with f i = y, ‖w i‖) * ‖P y‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ ≤ _ := Finset.sum_le_sum (fun y hy =>
      mul_le_mul_of_nonneg_right (hfib y hy) (sq_nonneg _))

theorem bounded_energy_pushforward {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (f : ι → κ) (w : ι → ℂ)
    (P : κ → ℂ) (C : ℝ)
    (hmap : ∀ i ∈ s, f i ∈ t) (hw : ∀ i ∈ s, ‖w i‖ ≤ C) :
    (∑ i ∈ s, ‖w i‖ * ‖P (f i)‖ ^ 2) ≤
      ∑ y ∈ t, C * (s.filter (fun i => f i = y)).card * ‖P y‖ ^ 2 := by
  apply weighted_energy_pushforward s t f w P _ hmap
  intro y hy
  calc
    _ ≤ ∑ i ∈ s with f i = y, C := Finset.sum_le_sum
      (fun i hi => hw i (Finset.mem_filter.mp hi).1)
    _ = _ := by simp [mul_comm]

abbrev O := ActualEisensteinCubic.O

def firstRowMap (E : Ideal O) (x : Ideal O × Ideal O) : Ideal O :=
  x.2 * x.1 ^ 2 * E

theorem firstRowMap_fst_dvd (E : Ideal O) (x : Ideal O × Ideal O) :
    x.1 ∣ firstRowMap E x := by
  refine ⟨x.2 * x.1 * E, ?_⟩
  simp only [firstRowMap]
  ring

theorem firstRowMap_fst_injective_on_fiber
    (s : Finset (Ideal O × Ideal O)) (E Y : Ideal O) (hY : Y ≠ ⊥) :
    Set.InjOn (Prod.fst : Ideal O × Ideal O → Ideal O)
      {x | x ∈ s ∧ firstRowMap E x = Y} := by
  intro x hx z hz hfst
  have hx' := hx.2
  have hz' := hz.2
  have hfac : x.1 ^ 2 * E ≠ 0 := by
    intro he
    apply hY
    rw [← hx']
    simp [firstRowMap, mul_assoc, he]
  apply Prod.ext hfst
  apply mul_right_cancel₀ hfac
  calc
    x.2 * (x.1 ^ 2 * E) = Y := by simpa [firstRowMap, mul_assoc] using hx'
    _ = z.2 * (x.1 ^ 2 * E) := by simpa [firstRowMap, mul_assoc, hfst] using hz'.symm

theorem firstRowMap_fiber_card_le
    (s : Finset (Ideal O × Ideal O)) (E Y : Ideal O) (hY : Y ≠ ⊥) :
    (s.filter (fun x => firstRowMap E x = Y)).card ≤
      (IdealMobiusDivisorSum.idealDivisors Y).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro x hx
    change x.1 ∈ IdealMobiusDivisorSum.idealDivisors Y
    rw [IdealMobiusDivisorSum.mem_idealDivisors hY]
    rw [← (Finset.mem_filter.mp hx).2]
    exact firstRowMap_fst_dvd E x
  · intro x hx z hz he
    exact firstRowMap_fst_injective_on_fiber s E Y hY
      (Finset.mem_filter.mp hx) (Finset.mem_filter.mp hz) he

theorem first_energy_pushforward
    (s : Finset (Ideal O × Ideal O)) (t : Finset (Ideal O))
    (E : Ideal O) (w : Ideal O × Ideal O → ℂ) (P : Ideal O → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hmap : ∀ x ∈ s, firstRowMap E x ∈ t)
    (ht : ∀ Y ∈ t, Y ≠ ⊥) (hw : ∀ x ∈ s, ‖w x‖ ≤ C) :
    (∑ x ∈ s, ‖w x‖ * ‖P (firstRowMap E x)‖ ^ 2) ≤
      ∑ Y ∈ t, C * (IdealMobiusDivisorSum.idealDivisors Y).card * ‖P Y‖ ^ 2 := by
  apply (bounded_energy_pushforward s t (firstRowMap E) w P C hmap hw).trans
  apply Finset.sum_le_sum
  intro Y hY
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast firstRowMap_fiber_card_le s E Y (ht Y hY)) hC)
    (sq_nonneg _)

def firstElementRowMap (e : O) (x : Ideal O × O) : O :=
  x.2 * ConcretePrimeRowBridge.idealGenerator x.1 ^ 2 * e

theorem firstElementRowMap_label_dvd (e : O) (x : Ideal O × O) :
    x.1 ∣ Ideal.span {firstElementRowMap e x} := by
  rw [← ConcretePrimeRowBridge.span_idealGenerator x.1]
  apply Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr
  refine ⟨x.2 * ConcretePrimeRowBridge.idealGenerator x.1 * e, ?_⟩
  simp only [firstElementRowMap]
  ring

theorem firstElementRowMap_fiber_card_le
    (s : Finset (Ideal O × O)) (e y : O) (hy : y ≠ 0) :
    (s.filter (fun x => firstElementRowMap e x = y)).card ≤
      (IdealMobiusDivisorSum.idealDivisors (Ideal.span {y})).card := by
  have hyI : (Ideal.span {y} : Ideal O) ≠ ⊥ := by
    intro h
    have hm : y ∈ (Ideal.span {y} : Ideal O) := Ideal.subset_span (by simp)
    rw [h] at hm
    exact hy hm
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro x hx
    change x.1 ∈ IdealMobiusDivisorSum.idealDivisors (Ideal.span {y})
    rw [IdealMobiusDivisorSum.mem_idealDivisors hyI,
      ← (Finset.mem_filter.mp hx).2]
    exact firstElementRowMap_label_dvd e x
  · intro x hx z hz hfst
    have hx' := (Finset.mem_filter.mp hx).2
    have hz' := (Finset.mem_filter.mp hz).2
    have hfac : ConcretePrimeRowBridge.idealGenerator x.1 ^ 2 * e ≠ 0 := by
      intro he
      apply hy
      rw [← hx']
      simp [firstElementRowMap, mul_assoc, he]
    apply Prod.ext hfst
    apply mul_right_cancel₀ hfac
    calc
      x.2 * (ConcretePrimeRowBridge.idealGenerator x.1 ^ 2 * e) = y := by
        simpa [firstElementRowMap, mul_assoc] using hx'
      _ = z.2 * (ConcretePrimeRowBridge.idealGenerator x.1 ^ 2 * e) := by
        simpa [firstElementRowMap, mul_assoc, hfst] using hz'.symm

theorem first_element_energy_pushforward
    (s : Finset (Ideal O × O)) (t : Finset O)
    (e : O) (w : Ideal O × O → ℂ) (P : O → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hmap : ∀ x ∈ s, firstElementRowMap e x ∈ t)
    (ht : ∀ y ∈ t, y ≠ 0) (hw : ∀ x ∈ s, ‖w x‖ ≤ C) :
    (∑ x ∈ s, ‖w x‖ * ‖P (firstElementRowMap e x)‖ ^ 2) ≤
      ∑ y ∈ t, C * (IdealMobiusDivisorSum.idealDivisors (Ideal.span {y})).card *
        ‖P y‖ ^ 2 := by
  apply (bounded_energy_pushforward s t (firstElementRowMap e) w P C hmap hw).trans
  apply Finset.sum_le_sum
  intro y hyt
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (by exact_mod_cast firstElementRowMap_fiber_card_le s e y (ht y hyt)) hC)
    (sq_nonneg _)

end DescentWeightedCauchy

end

end OAI
end OAIOriginalModule0098

/-! Original module: OAI.NumberTheory.DirichletL.Arithmetic.SquarefreeDivisors
Source SHA256: da5054c7c9b6f565e96738fae5b7f2f24992100d7a0ec0da490c6a3cafd9dc63
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0099


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

namespace SquarefreeDivisorBound
open scoped BigOperators Classical
open Filter IdealMobiusDivisorSum

abbrev O := ActualEisensteinCubic.O

theorem squarefree_divisor_card_le (I : Ideal O) (hI : I ≠ ⊥) :
    ((idealDivisors I).filter Squarefree).card ≤ 2 ^ (primeSupport I).card := by
  rw [squarefree_divisors_eq_image I hI]
  exact Finset.card_image_le.trans_eq (Finset.card_powerset _)

theorem prime_support_subsets_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal O, I ≠ ⊥ →
      (2 : ℝ) ^ (primeSupport I).card ≤ C * (Ideal.absNorm I : ℝ) ^ ε := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2 : ℝ)))
  let small : Finset (Ideal O) :=
    (Ideal.finite_setOfPred_absNorm_le (S := O) N).toFinset
  refine ⟨(2 : ℝ) ^ small.card, by positivity, ?_⟩
  intro I hI
  let S := primeSupport I
  let A := S ∩ small
  let B := S \ small
  have hBS : B ⊆ primeSupport I := Finset.sdiff_subset
  have hlarge (P : Ideal O) (hP : P ∈ B) : (2 : ℝ) ≤ (Ideal.absNorm P : ℝ) ^ ε := by
    apply hN
    have hn : P ∉ small := (Finset.mem_sdiff.mp hP).2
    have hgt : N < Ideal.absNorm P := by
      apply Nat.lt_of_not_ge
      intro hp
      exact hn (by simpa [small] using hp)
    exact hgt.le
  have hpowB : (2 : ℝ) ^ B.card ≤ (Ideal.absNorm (∏ P ∈ B, P) : ℝ) ^ ε := by
    calc
      _ = ∏ P ∈ B, (2 : ℝ) := by simp
      _ ≤ ∏ P ∈ B, (Ideal.absNorm P : ℝ) ^ ε :=
        Finset.prod_le_prod₀ (fun _ _ => by positivity) hlarge
      _ = (∏ P ∈ B, (Ideal.absNorm P : ℝ)) ^ ε :=
        (Real.finsetProd_rpow B (fun P => (Ideal.absNorm P : ℝ))
          (fun _ _ => by positivity) ε)
      _ = _ := by simp only [map_prod, Nat.cast_prod]
  have hNI : 0 < Ideal.absNorm I := Nat.pos_iff_ne_zero.mpr
    (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))
  have hnorm : Ideal.absNorm (∏ P ∈ B, P) ≤ Ideal.absNorm I :=
    Nat.le_of_dvd hNI (map_dvd Ideal.absNorm (support_product_dvd hI hBS))
  have hpowBI : (2 : ℝ) ^ B.card ≤ (Ideal.absNorm I : ℝ) ^ ε :=
    hpowB.trans (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnorm) hε.le)
  have hAc : A.card ≤ small.card := Finset.card_le_card Finset.inter_subset_right
  have hcard : S.card = A.card + B.card := by
    simp [A, B]
  change (2 : ℝ) ^ S.card ≤ _
  rw [hcard, pow_add]
  exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hAc) hpowBI
    (by positivity) (by positivity)

theorem squarefree_divisor_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal O, I ≠ ⊥ →
      (((idealDivisors I).filter Squarefree).card : ℝ) ≤ C * (Ideal.absNorm I : ℝ) ^ ε := by
  obtain ⟨C, hC, h⟩ := prime_support_subsets_bound ε hε
  refine ⟨C, hC, fun I hI => ?_⟩
  have hc : (((idealDivisors I).filter Squarefree).card : ℝ) ≤
      (2 : ℝ) ^ (primeSupport I).card := by
    exact_mod_cast squarefree_divisor_card_le I hI
  exact hc.trans (h I hI)

open DescentWeightedCauchy

theorem first_element_squarefree_fiber
    (s : Finset (Ideal O × O)) (hs : ∀ x ∈ s, Squarefree x.1)
    (e y : O) (hy : y ≠ 0) :
    (s.filter (fun x => firstElementRowMap e x = y)).card ≤
      ((idealDivisors (Ideal.span {y})).filter Squarefree).card := by
  have hyI : (Ideal.span {y} : Ideal O) ≠ ⊥ := by
    intro h
    have hm : y ∈ (Ideal.span {y} : Ideal O) := Ideal.subset_span (by simp)
    rw [h] at hm
    exact hy hm
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro x hx
    change x.1 ∈ (idealDivisors (Ideal.span {y})).filter Squarefree
    have hx' := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨?_, hs x hx'.1⟩
    rw [mem_idealDivisors hyI, ← hx'.2]
    exact firstElementRowMap_label_dvd e x
  · intro x hx z hz hfst
    have hx' := (Finset.mem_filter.mp hx).2
    have hz' := (Finset.mem_filter.mp hz).2
    have hfac : ConcretePrimeRowBridge.idealGenerator x.1 ^ 2 * e ≠ 0 := by
      intro he
      apply hy
      rw [← hx']
      simp [firstElementRowMap, mul_assoc, he]
    apply Prod.ext hfst
    apply mul_right_cancel₀ hfac
    calc
      x.2 * (ConcretePrimeRowBridge.idealGenerator x.1 ^ 2 * e) = y := by
        simpa [firstElementRowMap, mul_assoc] using hx'
      _ = z.2 * (ConcretePrimeRowBridge.idealGenerator x.1 ^ 2 * e) := by
        simpa [firstElementRowMap, mul_assoc, hfst] using hz'.symm

theorem first_element_fiber_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (Ideal O × O)),
      (∀ x ∈ s, Squarefree x.1) → ∀ e y : O, y ≠ 0 →
      ((s.filter (fun x => firstElementRowMap e x = y)).card : ℝ) ≤
        C * (Ideal.absNorm (Ideal.span {y}) : ℝ) ^ ε := by
  obtain ⟨C, hC, h⟩ := squarefree_divisor_small_power ε hε
  refine ⟨C, hC, ?_⟩
  intro s hs e y hy
  have hyI : (Ideal.span {y} : Ideal O) ≠ ⊥ := by
    intro he
    have hm : y ∈ (Ideal.span {y} : Ideal O) := Ideal.subset_span (by simp)
    rw [he] at hm
    exact hy hm
  have hc : ((s.filter (fun x => firstElementRowMap e x = y)).card : ℝ) ≤
      (((idealDivisors (Ideal.span {y})).filter Squarefree).card : ℝ) := by
    exact_mod_cast first_element_squarefree_fiber s hs e y hy
  exact hc.trans (h _ hyI)

theorem first_element_energy_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (Ideal O × O)) (t : Finset O)
      (e : O) (w : Ideal O × O → ℂ) (P : O → ℂ) (B Y : ℝ),
      0 ≤ B → 0 ≤ Y → (∀ x ∈ s, Squarefree x.1) →
      (∀ x ∈ s, firstElementRowMap e x ∈ t) → (∀ y ∈ t, y ≠ 0) →
      (∀ y ∈ t, (Ideal.absNorm (Ideal.span {y}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∑ x ∈ s, ‖w x‖ * ‖P (firstElementRowMap e x)‖ ^ 2) ≤
        B * C * Y ^ ε * ∑ y ∈ t, ‖P y‖ ^ 2 := by
  obtain ⟨C, hC, hc⟩ := first_element_fiber_small_power ε hε
  refine ⟨C, hC, ?_⟩
  intro s t e w P B Y hB hY hs hmap ht hnorm hw
  have hpush := bounded_energy_pushforward s t (firstElementRowMap e) w P B hmap hw
  apply hpush.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  have hcard := (hc s hs e y (ht y hy)).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hnorm y hy) hε.le) hC.le)
  have hterm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcard hB) (sq_nonneg ‖P y‖)
  simpa only [mul_assoc] using hterm

end SquarefreeDivisorBound

namespace VerticalContourShift
open MeasureTheory Filter Set
open scoped Topology

theorem horizontal_integral_tendsto_zero
    (f : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖f ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2)) :
    Tendsto (fun t : ℝ => ∫ σ : ℝ in a..b, f ((σ : ℂ) + t * Complex.I))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => 1 + t ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  have hz : Tendsto (fun t : ℝ => C / (1 + t ^ 2) * |b - a|) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop ht).mul_const |b - a|
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hz
  intro t
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro σ hσ
  exact hbound σ (Ioc_subset_Icc_self (by simpa [uIoc_of_le hab] using hσ)) t

theorem integral_eq_of_strip_decay
    (f : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hdiff : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ f z)
    (ha : Integrable (fun t : ℝ => f ((a : ℂ) + t * Complex.I)))
    (hb : Integrable (fun t : ℝ => f ((b : ℂ) + t * Complex.I)))
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖f ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2)) :
    (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)) =
      ∫ t : ℝ, f ((b : ℂ) + t * Complex.I) := by
  let H (t : ℝ) : ℂ := ∫ σ : ℝ in a..b, f ((σ : ℂ) + t * Complex.I)
  let V (σ t : ℝ) : ℂ := ∫ u : ℝ in -t..t, f ((σ : ℂ) + u * Complex.I)
  have htop : Tendsto H atTop (𝓝 0) := horizontal_integral_tendsto_zero f a b C hab hbound
  have hbottom : Tendsto (fun t : ℝ => H (-t)) atTop (𝓝 0) := by
    let g (z : ℂ) := f (star z)
    have hg : ∀ σ ∈ Icc a b, ∀ t : ℝ,
        ‖g ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
      intro σ hσ t
      simpa [g] using hbound σ hσ (-t)
    convert horizontal_integral_tendsto_zero g a b C hab hg using 1 ;
      simp [g, H]
  have hVa : Tendsto (V a) atTop
      (𝓝 (∫ t : ℝ, f ((a : ℂ) + t * Complex.I))) :=
    intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hVb : Tendsto (V b) atTop
      (𝓝 (∫ t : ℝ, f ((b : ℂ) + t * Complex.I))) :=
    intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have hrect (t : ℝ) : H (-t) - H t + Complex.I * V b t - Complex.I * V a t = 0 := by
    have hd : DifferentiableOn ℂ f
        (uIcc (((a : ℂ) - t * Complex.I).re) (((b : ℂ) + t * Complex.I).re) ×ℂ
         uIcc (((a : ℂ) - t * Complex.I).im) (((b : ℂ) + t * Complex.I).im)) := by
      intro z hz
      apply (hdiff z ?_ ?_).differentiableWithinAt
      · have hz' : z.re ∈ Icc a b := by
          simpa [uIcc_of_le hab] using hz.1
        exact hz'.1
      · have hz' : z.re ∈ Icc a b := by
          simpa [uIcc_of_le hab] using hz.1
        exact hz'.2
    have hr := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a : ℂ) - t * Complex.I) ((b : ℂ) + t * Complex.I) hd
    simpa [H, V, smul_eq_mul] using hr
  have hlim : Tendsto
      (fun t : ℝ => H (-t) - H t + Complex.I * V b t - Complex.I * V a t)
      atTop (𝓝 (0 - 0 + Complex.I * (∫ t : ℝ, f ((b : ℂ) + t * Complex.I)) -
        Complex.I * (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)))) :=
    ((hbottom.sub htop).add (tendsto_const_nhds.mul hVb)).sub
      (tendsto_const_nhds.mul hVa)
  have heq : Complex.I * (∫ t : ℝ, f ((b : ℂ) + t * Complex.I)) -
      Complex.I * (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)) = 0 := by
    have hzero : Tendsto (fun t : ℝ => H (-t) - H t + Complex.I * V b t - Complex.I * V a t)
        atTop (𝓝 0) := by
      simpa only [hrect] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0))
    simpa using tendsto_nhds_unique hlim hzero
  exact (mul_left_cancel₀ Complex.I_ne_zero (sub_eq_zero.mp heq)).symm

end VerticalContourShift

open scoped BigOperators Classical
namespace FirstPassCubeLabels
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic

def bit (b : Bool) : ℕ := if b then 1 else 0

def conductorExponent (parityBit ε₁ ε₂ : Bool) : ZMod 6 :=
  (bit ε₁ : ZMod 6) - (bit ε₂ : ZMod 6) + 3 * (bit parityBit : ZMod 6)

def crtExponent (side parityBit ε₁ ε₂ : Bool) : ℕ :=
  if conductorExponent parityBit ε₁ ε₂ = 0 then 0 else
    ((1 : ZMod 6) + if side then -conductorExponent parityBit ε₁ ε₂
      else conductorExponent parityBit ε₁ ε₂).val

def dilationExponent (parityBit ε₁ ε₂ : Bool) : ℕ :=
  if parityBit then bit ε₁ + bit ε₂ else 0

def retained (parityBit ε₁ ε₂ : Bool) : Bool := parityBit || (ε₁ && ε₂)

theorem exponent_table (side parityBit ε₁ ε₂ : Bool) :
    (4 * bit (if side then ε₂ else ε₁) + crtExponent side parityBit ε₁ ε₂ +
      dilationExponent parityBit ε₁ ε₂) % 6 = if retained parityBit ε₁ ε₂ then 4 else 0 := by
  cases side <;> cases parityBit <;> cases ε₁ <;> cases ε₂ <;> decide

section Rows
variable {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)

theorem row_pow (a : O) (m : ℕ) :
    finiteSquarefreeRow P hg S (a ^ m) = finiteSquarefreeRow P hg S a ^ m := by
  simp only [finiteSquarefreeRow, map_pow, Finset.prod_pow]

theorem row_prod {κ : Type*} (B : Finset κ) (a : κ → O) :
    finiteSquarefreeRow P hg S (∏ j ∈ B, a j) =
      ∏ j ∈ B, finiteSquarefreeRow P hg S (a j) := by
  classical
  induction B using Finset.induction_on with
  | empty => simp [finiteSquarefreeRow]
  | @insert j B hj ih =>
    simp only [Finset.prod_insert hj, finiteSquarefreeRow_mul, ih]

theorem row_sixth (a : O) :
    finiteSquarefreeRow P hg S a ^ 6 = rowCoprimeMask P S a := by
  rw [← row_pow, finiteSquarefreeRow_sixth_power]
  rfl

include hg

theorem mask_mul (a b : O) :
    rowCoprimeMask P S (a * b) = rowCoprimeMask P S a * rowCoprimeMask P S b := by
  simp only [← row_sixth P hg S, finiteSquarefreeRow_mul, mul_pow]

theorem mask_pow (a : O) (m : ℕ) :
    rowCoprimeMask P S (a ^ m) = rowCoprimeMask P S a ^ m := by
  rw [← row_sixth P hg S, row_pow, ← row_sixth P hg S]
  simp only [← pow_mul, Nat.mul_comm]

theorem mask_prod {κ : Type*} (B : Finset κ) (a : κ → O) :
    rowCoprimeMask P S (∏ j ∈ B, a j) = ∏ j ∈ B, rowCoprimeMask P S (a j) := by
  rw [← row_sixth P hg S, row_prod, ← Finset.prod_pow]
  simp only [row_sixth]

theorem row_zero_of_mask_zero (a : O) (h : rowCoprimeMask P S a = 0) :
    finiteSquarefreeRow P hg S a = 0 := by
  have hq := row_sixth P hg S a
  rw [h] at hq
  exact (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hq

theorem row_power_mul_mask_power (a : O) (k m : ℕ) (hk : 0 < k) :
    finiteSquarefreeRow P hg S a ^ k * rowCoprimeMask P S a ^ m =
      finiteSquarefreeRow P hg S a ^ k := by
  by_cases h : ∃ i ∈ S, a ∈ P i
  · have hm : rowCoprimeMask P S a = 0 := by simp [rowCoprimeMask, h]
    rw [row_zero_of_mask_zero P hg S a hm]
    simp [Nat.ne_of_gt hk]
  · simp [rowCoprimeMask, h]

def localFactor (side parityBit ε₁ ε₂ : Bool) (a : O) : ℂ :=
  rowCoprimeMask P S a *
    finiteSquarefreeRow P hg S a ^ (4 * bit (if side then ε₂ else ε₁)) *
    finiteSquarefreeRow P hg S a ^ crtExponent side parityBit ε₁ ε₂ *
    finiteSquarefreeRow P hg S a ^ dilationExponent parityBit ε₁ ε₂

theorem localFactor_eq (side parityBit ε₁ ε₂ : Bool) (a : O) :
    localFactor P hg S side parityBit ε₁ ε₂ a =
      if retained parityBit ε₁ ε₂ then finiteSquarefreeRow P hg S a ^ 4
      else rowCoprimeMask P S a := by
  by_cases h : ∃ i ∈ S, a ∈ P i
  · have hm : rowCoprimeMask P S a = 0 := by simp [rowCoprimeMask, h]
    have hz := row_zero_of_mask_zero P hg S a hm
    simp [localFactor, hm, hz]
  · have hm : rowCoprimeMask P S a = 1 := by simp [rowCoprimeMask, h]
    have h6 : finiteSquarefreeRow P hg S a ^ 6 = 1 := (row_sixth P hg S a).trans hm
    simp only [localFactor, hm, one_mul, ← pow_add]
    rw [pow_eq_pow_mod _ h6, exponent_table]
    split <;> simp

end Rows

def parity (m : ℕ) : Bool := decide (m % 2 = 1)

def evenDouble (m : ℕ) (ε₁ ε₂ : Bool) : Bool := !parity m && ε₁ && ε₂

def b0Exponent (m : ℕ) (ε₁ ε₂ : Bool) : ℕ := m / 2 - bit (evenDouble m ε₁ ε₂)

theorem multiplicity_decomposition (m : ℕ) (ε₁ ε₂ : Bool) (hm : 0 < m) :
    2 * b0Exponent m ε₁ ε₂ + 2 * bit (evenDouble m ε₁ ε₂) + bit (parity m) = m := by
  have hmod := Nat.mod_lt m (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div m 2
  cases ε₁ <;> cases ε₂ <;> by_cases h : m % 2 = 1 <;>
    simp [b0Exponent, evenDouble, parity, bit, h] <;> omega

theorem b0Exponent_pos_of_not_retained (m : ℕ) (ε₁ ε₂ : Bool) (hm : 0 < m)
    (hret : retained (parity m) ε₁ ε₂ = false) : 0 < b0Exponent m ε₁ ε₂ := by
  have hmod := Nat.mod_lt m (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div m 2
  cases ε₁ <;> cases ε₂ <;> by_cases h : m % 2 = 1 <;>
    simp_all [b0Exponent, evenDouble, parity, retained, bit] <;> omega

section Reassembly
variable {ι κ : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)

theorem localFactor_eq_b0 (side ε₁ ε₂ : Bool) (a : O) (m : ℕ) (hm : 0 < m) :
    localFactor P hg S side (parity m) ε₁ ε₂ a =
      (finiteSquarefreeRow P hg S (a ^ bit (retained (parity m) ε₁ ε₂))) ^ 4 *
        rowCoprimeMask P S (a ^ b0Exponent m ε₁ ε₂) := by
  rw [localFactor_eq, row_pow, mask_pow P hg S]
  cases hr : retained (parity m) ε₁ ε₂
  · have hpos := b0Exponent_pos_of_not_retained m ε₁ ε₂ hm hr
    simp only [Bool.false_eq_true, ↓reduceIte, bit, Bool.false_eq_true, pow_zero, one_pow,
      one_mul]
    unfold rowCoprimeMask
    split <;> simp [Nat.ne_of_gt hpos]
  · simp only [↓reduceIte, bit, pow_one]
    exact (row_power_mul_mask_power P hg S a 4 _ (by decide)).symm

def primeProduct (p : κ → O) (B : Finset κ) (v : κ → ℕ) : O := ∏ j ∈ B, p j ^ v j

def cubeRadical (p : κ → O) (B : Finset κ) : O := ∏ j ∈ B, p j

def aLabel (p : κ → O) (B : Finset κ) (ε : κ → Bool) : O :=
  primeProduct p B (fun j => bit (ε j))

def crtLabel (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) (side : Bool) : O :=
  primeProduct p B (fun j => crtExponent side (parity (v j)) (ε₁ j) (ε₂ j))

def dilationLabel (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : O :=
  primeProduct p B (fun j => dilationExponent (parity (v j)) (ε₁ j) (ε₂ j))

def jLabel (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : O :=
  primeProduct p B (fun j => bit (retained (parity (v j)) (ε₁ j) (ε₂ j)))

def j2Label (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : O :=
  primeProduct p B (fun j => bit (evenDouble (v j) (ε₁ j) (ε₂ j)))

def squarefreeLabel (p : κ → O) (B : Finset κ) (v : κ → ℕ) : O :=
  primeProduct p B (fun j => bit (parity (v j)))

def b0Label (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : O :=
  primeProduct p B (fun j => b0Exponent (v j) (ε₁ j) (ε₂ j))

theorem first_pass_label_identity (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) (hv : ∀ j ∈ B, 0 < v j) (side : Bool) :
    rowCoprimeMask P S (cubeRadical p B) *
      finiteSquarefreeRow P hg S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
      finiteSquarefreeRow P hg S (crtLabel p B v ε₁ ε₂ side) *
      finiteSquarefreeRow P hg S (dilationLabel p B v ε₁ ε₂) =
    finiteSquarefreeRow P hg S (jLabel p B v ε₁ ε₂) ^ 4 *
      rowCoprimeMask P S (b0Label p B v ε₁ ε₂) := by
  classical
  simp only [cubeRadical, aLabel, crtLabel, dilationLabel, jLabel, b0Label,
    primeProduct, mask_prod P hg S, row_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  rw [row_pow, row_pow, row_pow]
  convert localFactor_eq_b0 P hg S side (ε₁ j) (ε₂ j) (p j) (v j) (hv j hj) using 1
  cases side <;> simp only [localFactor, Bool.false_eq_true, ↓reduceIte,
    ← _root_.pow_mul, _root_.Nat.mul_comm]

theorem cube_product_decomposition (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) (hv : ∀ j ∈ B, 0 < v j) :
    primeProduct p B v = b0Label p B v ε₁ ε₂ ^ 2 * j2Label p B v ε₁ ε₂ ^ 2 *
      squarefreeLabel p B v := by
  simp only [b0Label, j2Label, squarefreeLabel, primeProduct, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib, ← pow_mul, ← pow_add]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  have h := multiplicity_decomposition (v j) (ε₁ j) (ε₂ j) (hv j hj)
  omega

theorem jLabel_eq_squarefree_mul_j2 (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) :
    jLabel p B v ε₁ ε₂ = squarefreeLabel p B v * j2Label p B v ε₁ ε₂ := by
  simp only [jLabel, squarefreeLabel, j2Label, primeProduct, ← Finset.prod_mul_distrib,
    ← pow_add]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  cases hp : parity (v j) <;> cases ε₁ j <;> cases ε₂ j <;>
    simp [bit, retained, evenDouble, hp]

include hg in

theorem radical_mask_absorbs (p : κ → O) (B : Finset κ) (v : κ → ℕ) :
    rowCoprimeMask P S (cubeRadical p B) * rowCoprimeMask P S (primeProduct p B v) =
      rowCoprimeMask P S (cubeRadical p B) := by
  simp only [cubeRadical, primeProduct, mask_prod P hg S, mask_pow P hg S,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  unfold rowCoprimeMask
  split <;> simp

theorem masked_dual_dilation (p : κ → O) (B : Finset κ) (v : κ → ℕ) (z : O) (c : ℂ) :
    rowCoprimeMask P S (cubeRadical p B) * c * star (finiteSquarefreeRow P hg S z) =
      (rowCoprimeMask P S (cubeRadical p B) * c *
        finiteSquarefreeRow P hg S (primeProduct p B v)) *
      star (finiteSquarefreeRow P hg S (z * primeProduct p B v)) := by
  rw [finiteSquarefreeRow_mul, star_mul]
  calc
    _ = (rowCoprimeMask P S (cubeRadical p B) *
        rowCoprimeMask P S (primeProduct p B v)) * c *
        star (finiteSquarefreeRow P hg S z) := by rw [radical_mask_absorbs P hg S]
    _ = _ := by rw [← finiteSquarefreeRow_self_pair P hg S (primeProduct p B v)]; ring

theorem first_pass_after_dual_dilation
    (p : κ → O) (B : Finset κ) (v : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hv : ∀ j ∈ B, 0 < v j) (side : Bool) (z : O) :
    (rowCoprimeMask P S (cubeRadical p B) *
      finiteSquarefreeRow P hg S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
      finiteSquarefreeRow P hg S (crtLabel p B v ε₁ ε₂ side)) *
      star (finiteSquarefreeRow P hg S z) =
    (finiteSquarefreeRow P hg S (jLabel p B v ε₁ ε₂) ^ 4 *
      rowCoprimeMask P S (b0Label p B v ε₁ ε₂)) *
      star (finiteSquarefreeRow P hg S (z * dilationLabel p B v ε₁ ε₂)) := by
  have hd := masked_dual_dilation P hg S p B
    (fun j => dilationExponent (parity (v j)) (ε₁ j) (ε₂ j)) z
    (finiteSquarefreeRow P hg S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
      finiteSquarefreeRow P hg S (crtLabel p B v ε₁ ε₂ side))
  change _ = (_ * finiteSquarefreeRow P hg S (dilationLabel p B v ε₁ ε₂)) * _ at hd
  simp only [← mul_assoc] at hd
  rw [first_pass_label_identity P hg S p B v ε₁ ε₂ hv side] at hd
  exact hd

theorem cube_pair_product_decomposition
    (p : κ → O) (B : Finset κ) (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hv : ∀ j ∈ B, 0 < v₁ j + v₂ j) :
    primeProduct p B v₁ * primeProduct p B v₂ =
      b0Label p B (fun j => v₁ j + v₂ j) ε₁ ε₂ ^ 2 *
      j2Label p B (fun j => v₁ j + v₂ j) ε₁ ε₂ ^ 2 *
      squarefreeLabel p B (fun j => v₁ j + v₂ j) := by
  rw [← cube_product_decomposition p B (fun j => v₁ j + v₂ j) ε₁ ε₂ hv]
  simp only [primeProduct, pow_add, Finset.prod_mul_distrib]

end Reassembly

theorem mobius_column_after_dual_dilation
    {ι κ : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (columns : Finset ι) (C : Finset ι → ℂ)
    (p : κ → O) (B : Finset κ) (v : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hv : ∀ j ∈ B, 0 < v j) (side : Bool) (z : O) :
    (∑ S ∈ columns.powerset, FirstCauchyArithmetic.supportMobius P S * C S *
      ((rowCoprimeMask P S (cubeRadical p B) *
        finiteSquarefreeRow P hg S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
        finiteSquarefreeRow P hg S (crtLabel p B v ε₁ ε₂ side)) *
        star (finiteSquarefreeRow P hg S z))) =
    FirstCauchyArithmetic.supportConjugateSum P hg columns
      (fun S => C S * finiteSquarefreeRow P hg S (jLabel p B v ε₁ ε₂) ^ 4 *
        rowCoprimeMask P S (b0Label p B v ε₁ ε₂))
      (z * dilationLabel p B v ε₁ ε₂) := by
  unfold FirstCauchyArithmetic.supportConjugateSum
  apply Finset.sum_congr rfl
  intro S hS
  rw [first_pass_after_dual_dilation P hg S p B v ε₁ ε₂ hv side z]
  ring

end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open FiniteGaussPhase MixedCrossSeparation ActualEisensteinCoordinates QuadraticGaussRay
open RayFourExpansion

def quadraticSymbol {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) : ℂ :=
  quadraticRow (fun i => Ideal.span {p i}) hg A (∏ i ∈ B, p i)

theorem quadraticSymbol_eq_cross_product {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) :
    quadraticSymbol p hg A B = ∏ i ∈ A, ∏ k ∈ B, crossSymbol p hg i k ^ 3 := by
  simp only [quadraticSymbol, quadraticRow, finiteSquarefreeRow, map_prod,
    ← Finset.prod_pow, crossSymbol]

theorem quadraticSymbol_mul_reverse {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) :
    quadraticSymbol p hg A B * quadraticSymbol p hg B A = quadraticCrossPhase p hg A B := by
  rw [quadraticSymbol_eq_cross_product, quadraticSymbol_eq_cross_product]
  rw [Finset.prod_comm (s := B) (t := A)]
  simp only [quadraticCrossPhase, Finset.prod_mul_distrib]

theorem quadraticSymbol_eq_zero_of_not_disjoint {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) (h : ¬ Disjoint A B) :
    quadraticSymbol p hg A B = 0 := by
  obtain ⟨i, hiA, hiB⟩ := Finset.not_disjoint_iff.mp h
  rw [quadraticSymbol_eq_cross_product]
  apply Finset.prod_eq_zero hiA
  apply Finset.prod_eq_zero hiB
  have hz : Ideal.Quotient.mk (Ideal.span {p i}) (p i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  simp only [crossSymbol, hz, MulChar.map_zero, zero_pow (by decide : 3 ≠ 0)]

theorem quadraticSymbol_sq_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) (hd : Disjoint A B) :
    quadraticSymbol p hg A B ^ 2 = 1 := by
  rw [quadraticSymbol_eq_cross_product, ← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i hi
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro k hk
  have hik : i ≠ k := by
    intro h
    subst k
    exact Finset.disjoint_left.mp hd hi hk
  rw [← pow_mul]
  simpa only [crossSymbol, show 3 * 2 = 6 by decide, map_pow,
    ite_eq_right (prime_generator_not_mem_other p hcop i k hik)] using
      canonicalSextic_sixth_power_mask (Ideal.span {p i}) (hg i) (p k)

theorem quadraticSymbol_reciprocity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A B : Finset ι) :
