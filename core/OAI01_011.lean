    quadraticSymbol p hg A B =
      quadraticRayPair (residue (∏ i ∈ A, p i)) (residue (∏ i ∈ B, p i)) *
        quadraticSymbol p hg B A := by
  by_cases hd : Disjoint A B
  · have hprod := quadraticSymbol_mul_reverse p hg A B
    rw [quadraticCrossPhase_eq_rayPair p hp hcop hg hc A B hd] at hprod
    have hsq := quadraticSymbol_sq_eq_one p hcop hg B A hd.symm
    calc
      _ = quadraticSymbol p hg A B * (quadraticSymbol p hg B A) ^ 2 := by rw [hsq, mul_one]
      _ = _ := by rw [pow_two, ← mul_assoc, hprod]
  · rw [quadraticSymbol_eq_zero_of_not_disjoint p hg A B hd,
      quadraticSymbol_eq_zero_of_not_disjoint p hg B A (fun h => hd h.symm), mul_zero]

theorem quadraticSymbol_reciprocity_characters {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A B : Finset ι) :
    quadraticSymbol p hg A B =
      ∑ χ : RayCharacter, ∑ η : RayCharacter,
        crossCoeff χ η * rayCharacter χ (∏ i ∈ A, p i) *
          rayCharacter η (∏ i ∈ B, p i) * quadraticSymbol p hg B A := by
  rw [quadraticSymbol_reciprocity p hp hcop hg hc]
  have hr := quadraticRayPair_character_expansion (∏ i ∈ A, p i) (∏ i ∈ B, p i)
  rw [rayMask_prime_product p hc A, rayMask_prime_product p hc B, one_mul, one_mul] at hr
  rw [hr]
  simp only [Finset.sum_mul]

end QuadraticInitialBound

end

end OAI
end OAIOriginalModule0099

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.CubeLabels
Source SHA256: b740b4bc77b7e1a1baa99f980e8b9d56a99a789497b93ec5e053bcd0c58eebae
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0100


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

section
open scoped BigOperators Classical
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (crossSymbol quadraticCrossPhase)

private theorem cross_sixth {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (i k : ι) (hik : i ≠ k) :
    crossSymbol p hg i k ^ 6 = 1 := by
  have hnot : p k ∉ Ideal.span {p i} := by
    intro hm
    have hle : Ideal.span {p k} ≤ Ideal.span {p i} :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    have ht := (hcop hik).sup_eq
    rw [sup_eq_left.mpr hle] at ht
    exact (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top ht
  simpa only [crossSymbol, map_pow, ite_eq_right hnot] using
    canonicalSextic_sixth_power_mask (Ideal.span {p i}) (hg i) (p k)

theorem reverse_cross_eq_quadratic {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (i k : ι) (hik : i ≠ k) :
    crossSymbol p hg k i = crossSymbol p hg i k *
      (crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3) := by
  have hr : crossSymbol p hg i k ^ 2 = crossSymbol p hg k i ^ 2 :=
    canonicalSextic_sq_reciprocity_primary (Ideal.span {p i}) (Ideal.span {p k})
      (hg i) (hg k) (p i) (p k) rfl rfl (hpr i) (hpr k)
  symm
  calc
    _ = crossSymbol p hg i k ^ 4 *
        (crossSymbol p hg k i ^ 2 * crossSymbol p hg k i) := by ring
    _ = crossSymbol p hg i k ^ 6 * crossSymbol p hg k i := by rw [← hr]; ring
    _ = _ := by rw [cross_sixth p hcop hg i k hik, one_mul]

private theorem local_quadratic_sq {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (i k : ι) (hik : i ≠ k) :
    (crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3) ^ 2 = 1 := by
  rw [mul_pow, ← pow_mul, ← pow_mul]
  norm_num only [show 3 * 2 = 6 by decide, cross_sixth p hcop hg i k hik,
    cross_sixth p hcop hg k i hik.symm, one_mul]

private theorem crt_exponent_table (side parityBit ε₁ ε₂ : Bool)
    (he : conductorExponent parityBit ε₁ ε₂ ≠ 0) :
    ((if side then 5 else 1) + (conductorExponent parityBit ε₁ ε₂).val) % 6 =
      ((if side then 5 else 1) * crtExponent side parityBit ε₁ ε₂) % 6 := by
  cases side <;> cases parityBit <;> cases ε₁ <;> cases ε₂ <;>
    first | exact False.elim (he (by decide)) | decide

theorem active_cube_cross_local {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (i k : ι) (hik : i ≠ k)
    (side parityBit ε₁ ε₂ : Bool) (he : conductorExponent parityBit ε₁ ε₂ ≠ 0) :
    crossSymbol p hg i k ^ (if side then 5 else 1) *
      crossSymbol p hg k i ^ (conductorExponent parityBit ε₁ ε₂).val =
    (if side then star (crossSymbol p hg i k ^ crtExponent side parityBit ε₁ ε₂)
      else crossSymbol p hg i k ^ crtExponent side parityBit ε₁ ε₂) *
      (crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3) ^
        (conductorExponent parityBit ε₁ ε₂).val := by
  let x := crossSymbol p hg i k
  let q := crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3
  have hrev : crossSymbol p hg k i = x * q := reverse_cross_eq_quadratic p hcop hg hpr i k hik
  have h6 : x ^ 6 = 1 := cross_sixth p hcop hg i k hik
  have hs : star x = x ^ 5 := by
    have h := canonicalSextic_conj_as_row_label (Ideal.span {p i}) (hg i) (p k)
    change star x = x * x ^ 4 at h
    rw [h]
    ring
  calc
    _ = x ^ ((if side then 5 else 1) + (conductorExponent parityBit ε₁ ε₂).val) *
        q ^ (conductorExponent parityBit ε₁ ε₂).val := by rw [hrev, mul_pow, pow_add]; ring
    _ = _ := by
      congr 1
      cases side
      · change x ^ (1 + (conductorExponent parityBit ε₁ ε₂).val) = x ^ crtExponent false parityBit ε₁ ε₂
        conv_lhs => rw [pow_eq_pow_mod _ h6]
        conv_rhs => rw [pow_eq_pow_mod _ h6]
        congr 1
        simpa only [Bool.false_eq_true, ↓reduceIte, one_mul] using crt_exponent_table false parityBit ε₁ ε₂ he
      · change x ^ (5 + (conductorExponent parityBit ε₁ ε₂).val) = star (x ^ crtExponent true parityBit ε₁ ε₂)
        rw [star_pow, hs, ← pow_mul]
        conv_lhs => rw [pow_eq_pow_mod _ h6]
        conv_rhs => rw [pow_eq_pow_mod _ h6]
        congr 1
        exact crt_exponent_table true parityBit ε₁ ε₂ he

def cubeOddSupport {ι : Type*} (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Finset ι :=
  B.filter fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val % 2 = 1

def mixedCubeCross {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (U B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) : ℂ :=
  ∏ i ∈ U, ∏ k ∈ B.filter (fun k => conductorExponent (parity (v k)) (ε₁ k) (ε₂ k) ≠ 0),
    crossSymbol p hg i k ^ (if side then 5 else 1) *
      crossSymbol p hg k i ^ (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val

theorem mixedCubeCross_eq_ordered {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (U B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) :
    mixedCubeCross p hg U B v ε₁ ε₂ side =
      (∏ i ∈ U, ∏ k ∈ B.filter (fun k => conductorExponent (parity (v k)) (ε₁ k) (ε₂ k) ≠ 0),
        crossSymbol p hg i k ^ (if side then 5 else 1)) *
      (∏ k ∈ B.filter (fun k => conductorExponent (parity (v k)) (ε₁ k) (ε₂ k) ≠ 0),
        ∏ i ∈ U, crossSymbol p hg k i ^ (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) := by
  rw [Finset.prod_comm (s := B.filter _) (t := U)]
  simp only [mixedCubeCross, Finset.prod_mul_distrib]

private theorem cube_cross_local_if {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (i k : ι) (hik : i ≠ k)
    (side parityBit ε₁ ε₂ : Bool) :
    (if conductorExponent parityBit ε₁ ε₂ ≠ 0 then
      crossSymbol p hg i k ^ (if side then 5 else 1) *
        crossSymbol p hg k i ^ (conductorExponent parityBit ε₁ ε₂).val else 1) =
    (if side then star (crossSymbol p hg i k ^ crtExponent side parityBit ε₁ ε₂)
      else crossSymbol p hg i k ^ crtExponent side parityBit ε₁ ε₂) *
      (if (conductorExponent parityBit ε₁ ε₂).val % 2 = 1 then
        crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3 else 1) := by
  by_cases he : conductorExponent parityBit ε₁ ε₂ = 0
  · simp [he, crtExponent]
  · rw [ite_eq_left he, active_cube_cross_local p hcop hg hpr i k hik side parityBit ε₁ ε₂ he]
    congr 1
    rw [pow_eq_pow_mod _ (local_quadratic_sq p hcop hg i k hik)]
    by_cases ho : (conductorExponent parityBit ε₁ ε₂).val % 2 = 1
    · simp [ho]
    · have hz : (conductorExponent parityBit ε₁ ε₂).val % 2 = 0 := by omega
      simp [ hz]

theorem mixedCubeCross_eq_row_quadratic {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (U B : Finset ι) (hd : Disjoint U B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) :
    mixedCubeCross p hg U B v ε₁ ε₂ side =
      (if side then star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U
          (crtLabel p B v ε₁ ε₂ side))
        else finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U
          (crtLabel p B v ε₁ ε₂ side)) *
      quadraticCrossPhase p hg U (cubeOddSupport B v ε₁ ε₂) := by
  have hr : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U
      (crtLabel p B v ε₁ ε₂ side) =
      ∏ i ∈ U, ∏ k ∈ B, crossSymbol p hg i k ^
        crtExponent side (parity (v k)) (ε₁ k) (ε₂ k) := by
    simp only [finiteSquarefreeRow, crtLabel, primeProduct, map_prod, map_pow, crossSymbol]
  calc
    _ = (∏ i ∈ U, ∏ k ∈ B,
        if side then star (crossSymbol p hg i k ^ crtExponent side (parity (v k)) (ε₁ k) (ε₂ k))
        else crossSymbol p hg i k ^ crtExponent side (parity (v k)) (ε₁ k) (ε₂ k)) *
      (∏ i ∈ U, ∏ k ∈ B,
        if (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val % 2 = 1 then
          crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3 else 1) := by
      simp only [mixedCubeCross, Finset.prod_filter, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      apply Finset.prod_congr rfl
      intro k hk
      apply cube_cross_local_if p hcop hg hpr i k
      exact fun he => Finset.disjoint_left.mp hd hi (he ▸ hk)
    _ = _ := by
      congr 1
      · rw [hr]
        cases side <;> simp only [Bool.false_eq_true, ↓reduceIte, star_prod]
      · simp only [quadraticCrossPhase, cubeOddSupport, Finset.prod_filter]

theorem mixedCubeCross_eq_ray_expansion {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (U B : Finset ι) (hd : Disjoint U B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) :
    mixedCubeCross p hg U B v ε₁ ε₂ side =
      (if side then star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U
          (crtLabel p B v ε₁ ε₂ side))
        else finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U
          (crtLabel p B v ε₁ ε₂ side)) *
      (∑ χ : RayFourExpansion.RayCharacter, ∑ η : RayFourExpansion.RayCharacter,
        RayFourExpansion.crossCoeff χ η * RayFourExpansion.rayCharacter χ (∏ i ∈ U, p i) *
          RayFourExpansion.rayCharacter η (∏ k ∈ cubeOddSupport B v ε₁ ε₂, p k)) := by
  rw [mixedCubeCross_eq_row_quadratic p hcop hg hpr U B hd v ε₁ ε₂ side,
    RayFourExpansion.quadraticCrossPhase_character_expansion p hp hcop hg hc]
  exact hd.mono_right (Finset.filter_subset _ _)

end FirstPassCubeLabels

open scoped BigOperators Classical
open UniqueFactorizationMonoid
namespace QuadraticSquarefreeKernel
abbrev O := ActualEisensteinCubic.O

def squarePart (I : Ideal O) : Ideal O := (exists_sq_mul_squarefree I).choose

def squarefreePart (I : Ideal O) : Ideal O :=
  (exists_sq_mul_squarefree I).choose_spec.choose

theorem squarePart_sq_mul_squarefreePart (I : Ideal O) :
    squarePart I ^ 2 * squarefreePart I = I :=
  (exists_sq_mul_squarefree I).choose_spec.choose_spec.1

theorem squarefree_squarefreePart (I : Ideal O) : Squarefree (squarefreePart I) :=
  (exists_sq_mul_squarefree I).choose_spec.choose_spec.2

theorem squarePart_ne_zero {I : Ideal O} (hI : I ≠ 0) : squarePart I ≠ 0 := by
  intro hz
  have h := squarePart_sq_mul_squarefreePart I
  rw [hz, zero_pow (by decide : 2 ≠ 0), zero_mul] at h
  exact hI h.symm

theorem squarefree_decomposition_unique {A B D E : Ideal O}
    (hA : A ≠ 0) (hB : B ≠ 0) (hD : Squarefree D) (hE : Squarefree E)
    (h : A ^ 2 * D = B ^ 2 * E) : A = B ∧ D = E := by
  have hf := congrArg normalizedFactors h
  rw [normalizedFactors_mul (pow_ne_zero _ hA) hD.ne_zero,
    normalizedFactors_mul (pow_ne_zero _ hB) hE.ne_zero,
    normalizedFactors_pow, normalizedFactors_pow] at hf
  have hd := (squarefree_iff_nodup_normalizedFactors hD.ne_zero).mp hD
  have he := (squarefree_iff_nodup_normalizedFactors hE.ne_zero).mp hE
  have hcount (P : Ideal O) :
      (normalizedFactors A).count P = (normalizedFactors B).count P ∧
      (normalizedFactors D).count P = (normalizedFactors E).count P := by
    have hc := congrArg (Multiset.count P) hf
    simp only [Multiset.count_add, Multiset.count_nsmul] at hc
    have hd1 := Multiset.nodup_iff_count_le_one.mp hd P
    have he1 := Multiset.nodup_iff_count_le_one.mp he P
    omega
  constructor
  · apply associated_iff_eq.mp
    apply (associated_iff_normalizedFactors_eq_normalizedFactors hA hB).mpr
    exact Multiset.ext.mpr (fun P => (hcount P).1)
  · apply associated_iff_eq.mp
    apply (associated_iff_normalizedFactors_eq_normalizedFactors hD.ne_zero hE.ne_zero).mpr
    exact Multiset.ext.mpr (fun P => (hcount P).2)

theorem squarePart_mul_squarefree {A D : Ideal O} (hA : A ≠ 0) (hD : Squarefree D) :
    squarePart (A ^ 2 * D) = A ∧ squarefreePart (A ^ 2 * D) = D :=
  squarefree_decomposition_unique
    (squarePart_ne_zero (mul_ne_zero (pow_ne_zero _ hA) hD.ne_zero)) hA
    (squarefree_squarefreePart _) hD (squarePart_sq_mul_squarefreePart _)

def decompositionEquiv : {I : Ideal O // I ≠ 0} ≃
    {A : Ideal O // A ≠ 0} × {D : Ideal O // Squarefree D} where
  toFun I := (⟨squarePart I.val, squarePart_ne_zero I.property⟩,
    ⟨squarefreePart I.val, squarefree_squarefreePart I.val⟩)
  invFun p := ⟨p.1.val ^ 2 * p.2.val, mul_ne_zero (pow_ne_zero _ p.1.property) p.2.property.ne_zero⟩
  left_inv I := Subtype.ext (squarePart_sq_mul_squarefreePart I.val)
  right_inv p := by
    apply Prod.ext
    · exact Subtype.ext (squarePart_mul_squarefree p.1.property p.2.property).1
    · exact Subtype.ext (squarePart_mul_squarefree p.1.property p.2.property).2

theorem squarefree_decomposition_tsum {V : Type*} [AddCommMonoid V] [TopologicalSpace V]
    (f : Ideal O → V) :
    (∑' I : {I : Ideal O // I ≠ 0}, f I.val) =
      ∑' p : {A : Ideal O // A ≠ 0} × {D : Ideal O // Squarefree D},
        f (p.1.val ^ 2 * p.2.val) := by
  exact (decompositionEquiv.symm.tsum_eq (fun I => f I.val)).symm

theorem norm_decomposition (I : Ideal O) :
    Ideal.absNorm (squarePart I) ^ 2 * Ideal.absNorm (squarefreePart I) = Ideal.absNorm I := by
  simpa only [map_mul, map_pow] using congrArg Ideal.absNorm (squarePart_sq_mul_squarefreePart I)

open ActualEisensteinCubic QuadraticInitialBound CompletedGauss

theorem quadraticRow_mul {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (a b : O) :
    quadraticRow P hg S (a * b) = quadraticRow P hg S a * quadraticRow P hg S b := by
  rw [quadraticRow, finiteSquarefreeRow_mul, mul_pow]
  rfl

theorem quadraticRow_square {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (a : O) :
    quadraticRow P hg S (a ^ 2) = rowCoprimeMask P S a := by
  have heq : quadraticRow P hg S (a ^ 2) = finiteSquarefreeRow P hg S (a ^ 6) := by
    simp only [quadraticRow, finiteSquarefreeRow, map_pow, ← Finset.prod_pow, ← pow_mul]
  rw [heq, finiteSquarefreeRow_sixth_power]
  rfl

theorem quadraticRow_primary_decomposition {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (I : Ideal O) :
    quadraticRow P hg S (primaryGenerator I) =
      rowCoprimeMask P S (primaryGenerator (squarePart I)) *
        quadraticRow P hg S (primaryGenerator (squarefreePart I)) := by
  conv_lhs => rw [← squarePart_sq_mul_squarefreePart I]
  rw [primaryGenerator_mul]
  have hpow : primaryGenerator (squarePart I ^ 2) = primaryGenerator (squarePart I) ^ 2 :=
    map_pow primaryGeneratorHom _ _
  rw [hpow, quadraticRow_mul, quadraticRow_square]

theorem quadraticRow_primary_tsum_decomposition {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (W : ℝ → ℂ) (X : ℝ) :
    (∑' I : {I : Ideal O // I ≠ 0},
      quadraticRow P hg S (primaryGenerator I.val) * W ((Ideal.absNorm I.val : ℝ) / X)) =
    ∑' p : {A : Ideal O // A ≠ 0} × {D : Ideal O // Squarefree D},
      rowCoprimeMask P S (primaryGenerator p.1.val) *
      quadraticRow P hg S (primaryGenerator p.2.val) *
      W (((Ideal.absNorm p.1.val : ℝ) ^ 2 * Ideal.absNorm p.2.val) / X) := by
  rw [squarefree_decomposition_tsum (fun I =>
    quadraticRow P hg S (primaryGenerator I) * W ((Ideal.absNorm I : ℝ) / X))]
  apply tsum_congr
  intro p
  have hpow : primaryGenerator (p.1.val ^ 2) = primaryGenerator p.1.val ^ 2 :=
    map_pow primaryGeneratorHom _ _
  simp only [primaryGenerator_mul, hpow, quadraticRow_mul, quadraticRow_square,
    map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]

end QuadraticSquarefreeKernel
end

namespace QuadraticMainBoundary
open scoped BigOperators Classical
open UniqueFactorizationMonoid
abbrev O := ActualEisensteinCubic.O
open QuadraticSquarefreeKernel

def cutoffDifference (K : ℝ) (H D : Ideal O) : ℝ :=
  (if (Ideal.absNorm (H * D) : ℝ) ≤ K then 1 else 0) -
    (if (Ideal.absNorm H : ℝ) ≤ K then 1 else 0)

theorem norm_pos {I : Ideal O} (hI : I ≠ 0) : 0 < (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.pos_iff_ne_zero.mpr
    (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

theorem norm_one_le {I : Ideal O} (hI : I ≠ 0) : 1 ≤ (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

theorem norm_le_of_dvd {I J : Ideal O} (hJ : J ≠ 0) (hIJ : I ∣ J) :
    (Ideal.absNorm I : ℝ) ≤ Ideal.absNorm J := by
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_iff_ne_zero.mpr (fun h => hJ (Ideal.absNorm_eq_zero_iff.mp h)))
    (map_dvd Ideal.absNorm hIJ)

theorem cutoffDifference_nonzero_iff (K : ℝ) (H D : Ideal O) (hD : D ≠ 0) :
    cutoffDifference K H D ≠ 0 ↔
      (Ideal.absNorm H : ℝ) ≤ K ∧ K < (Ideal.absNorm (H * D) : ℝ) := by
  have hmono : (Ideal.absNorm H : ℝ) ≤ Ideal.absNorm (H * D) := by
    rw [map_mul, Nat.cast_mul]
    nlinarith [norm_one_le hD, Nat.cast_nonneg (α := ℝ) (Ideal.absNorm H)]
  unfold cutoffDifference
  split_ifs <;> simp_all ; linarith

theorem cutoffDifference_eq_neg_one_of_nonzero (K : ℝ) (H D : Ideal O) (hD : D ≠ 0)
    (h : cutoffDifference K H D ≠ 0) : cutoffDifference K H D = -1 := by
  obtain ⟨hH, hHD⟩ := (cutoffDifference_nonzero_iff K H D hD).mp h
  simp only [cutoffDifference, ite_eq_right (not_le.mpr hHD), ite_eq_left hH]
  norm_num

theorem squarePart_dvd {G H D E : Ideal O} (hG : G ≠ 0) (hH : Squarefree H)
    (hDG : D ∣ G) (hEG : E ∣ G) : squarePart (H * D * E) ∣ G := by
  have hD := ne_zero_of_dvd_ne_zero hG hDG
  have hE := ne_zero_of_dvd_ne_zero hG hEG
  have hB : H * D * E ≠ 0 := mul_ne_zero (mul_ne_zero hH.ne_zero hD) hE
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (squarePart_ne_zero hB) hG).mpr
  apply Multiset.le_iff_count.mpr
  intro P
  have hfac := congrArg normalizedFactors (squarePart_sq_mul_squarefreePart (H * D * E))
  rw [normalizedFactors_mul (pow_ne_zero _ (squarePart_ne_zero hB))
    (squarefree_squarefreePart _).ne_zero, normalizedFactors_pow,
    normalizedFactors_mul (mul_ne_zero hH.ne_zero hD) hE,
    normalizedFactors_mul hH.ne_zero hD] at hfac
  have hcnt := congrArg (Multiset.count P) hfac
  simp only [Multiset.count_add, Multiset.count_nsmul] at hcnt
  have hd := (dvd_iff_normalizedFactors_le_normalizedFactors hD hG).mp hDG
  have he := (dvd_iff_normalizedFactors_le_normalizedFactors hE hG).mp hEG
  have hdc := Multiset.count_le_of_le P hd
  have hec := Multiset.count_le_of_le P he
  have hhc := Multiset.nodup_iff_count_le_one.mp
    ((squarefree_iff_nodup_normalizedFactors hH.ne_zero).mp hH) P
  omega

theorem cutoffDifference_eq_zero_of_product_le (K : ℝ) {H D E : Ideal O}
    (hD : D ≠ 0) (hE : E ≠ 0)
    (hB : (Ideal.absNorm (H * D * E) : ℝ) ≤ K) : cutoffDifference K H D = 0 := by
  by_contra h
  have hh := (cutoffDifference_nonzero_iff K H D hD).mp h
  have he := norm_one_le hE
  rw [map_mul, Nat.cast_mul] at hB
  have hp := Nat.cast_nonneg (Ideal.absNorm (H * D)) (α := ℝ)
  nlinarith

theorem main_boundary_localization (K : ℝ) {G H D E : Ideal O}
    (hG : G ≠ 0) (hH : Squarefree H) (hDG : D ∣ G) (hEG : E ∣ G)
    (h : cutoffDifference K H D ≠ 0) :
    K < (Ideal.absNorm (H * D * E) : ℝ) ∧
    (Ideal.absNorm (H * D * E) : ℝ) ≤ K * (Ideal.absNorm G : ℝ) ^ 2 ∧
    squarePart (H * D * E) ∣ G ∧
    K / (Ideal.absNorm G : ℝ) ^ 2 < (Ideal.absNorm (squarefreePart (H * D * E)) : ℝ) ∧
    (Ideal.absNorm (squarefreePart (H * D * E)) : ℝ) ≤ K * (Ideal.absNorm G : ℝ) ^ 2 := by
  have hD := ne_zero_of_dvd_ne_zero hG hDG
  have hE := ne_zero_of_dvd_ne_zero hG hEG
  have hB0 : H * D * E ≠ 0 := mul_ne_zero (mul_ne_zero hH.ne_zero hD) hE
  obtain ⟨hHK, hKHD⟩ := (cutoffDifference_nonzero_iff K H D hD).mp h
  have hHpos := norm_pos hH.ne_zero
  have hDpos := norm_pos hD
  have hEpos := norm_pos hE
  have hGone := norm_one_le hG
  have hEone := norm_one_le hE
  have hDle := norm_le_of_dvd hG hDG
  have hEle := norm_le_of_dvd hG hEG
  have hK : 0 ≤ K := le_trans hHpos.le hHK
  have hBlo : K < (Ideal.absNorm (H * D * E) : ℝ) := by
    rw [map_mul, Nat.cast_mul]
    have hp := Nat.cast_nonneg (Ideal.absNorm (H * D)) (α := ℝ)
    nlinarith
  have hBhi : (Ideal.absNorm (H * D * E) : ℝ) ≤ K * (Ideal.absNorm G : ℝ) ^ 2 := by
    simp only [map_mul, Nat.cast_mul]
    calc
      (Ideal.absNorm H : ℝ) * Ideal.absNorm D * Ideal.absNorm E ≤
        K * Ideal.absNorm G * Ideal.absNorm G :=
        mul_le_mul (mul_le_mul hHK hDle hDpos.le hK) hEle hEpos.le (by positivity)
      _ = _ := by ring
  have hroot := squarePart_dvd hG hH hDG hEG
  have hrootle := norm_le_of_dvd hG hroot
  have hrootone := norm_one_le (squarePart_ne_zero hB0)
  have hkerpos := norm_pos (squarefree_squarefreePart (H * D * E)).ne_zero
  have hdecomp : (Ideal.absNorm (squarePart (H * D * E)) : ℝ) ^ 2 *
      Ideal.absNorm (squarefreePart (H * D * E)) = Ideal.absNorm (H * D * E) := by
    exact_mod_cast norm_decomposition (H * D * E)
  have hrootpow : (Ideal.absNorm (squarePart (H * D * E)) : ℝ) ^ 2 ≤
      (Ideal.absNorm G : ℝ) ^ 2 := pow_le_pow_left₀ (le_trans zero_le_one hrootone) hrootle 2
  refine ⟨hBlo, hBhi, hroot, ?_, ?_⟩
  · apply (div_lt_iff₀ (by positivity : 0 < (Ideal.absNorm G : ℝ) ^ 2)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hrootpow hkerpos.le]
  · have hrpow : 1 ≤ (Ideal.absNorm (squarePart (H * D * E)) : ℝ) ^ 2 := by nlinarith
    nlinarith

theorem cutoffDifference_of_common_one (K : ℝ) {H D : Ideal O} (hD : D ∣ 1) :
    cutoffDifference K H D = 0 := by
  have hD1 : D = 1 := associated_iff_eq.mp (associated_one_iff_isUnit.mpr (isUnit_of_dvd_one hD))
  simp [cutoffDifference, hD1]

end QuadraticMainBoundary

open scoped BigOperators Classical
namespace QuadraticDivisorCancellation
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT QuadraticInitialBound QuadraticSquarefreeKernel

def normalizedRow {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (z : O) : ℂ :=
  quadraticRow P hg S z / (‖eisEmbedding z‖ : ℂ)

theorem normalizedRow_mul {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (a b : O) :
    normalizedRow P hg S (a * b) = normalizedRow P hg S a * normalizedRow P hg S b := by
  simp only [normalizedRow, quadraticRow_mul, map_mul, norm_mul, Complex.ofReal_mul,
    div_mul_div_comm]

theorem normalizedRow_one {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) : normalizedRow P hg S 1 = 1 := by
  simp [normalizedRow, quadraticRow, finiteSquarefreeRow]

def normalizedRowHom {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) : O →* ℂ where
  toFun := normalizedRow P hg S
  map_one' := normalizedRow_one P hg S
  map_mul' := normalizedRow_mul P hg S

theorem normalizedRow_prod {ι κ : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (q : κ → O) (T : Finset κ) :
    normalizedRow P hg S (∏ i ∈ T, q i) = ∏ i ∈ T, normalizedRow P hg S (q i) :=
  map_prod (normalizedRowHom P hg S) q T

theorem normalizedRow_sq {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (z : O) :
    normalizedRow P hg S z ^ 2 = rowCoprimeMask P S z /
      (Ideal.absNorm (Ideal.span {z}) : ℂ) := by
  have hrow : quadraticRow P hg S z ^ 2 = rowCoprimeMask P S z := by
    simpa only [pow_two, quadraticRow_mul] using quadraticRow_square P hg S z
  have hn : (‖eisEmbedding z‖ : ℂ) ^ 2 = (Ideal.absNorm (Ideal.span {z}) : ℂ) := by
    exact_mod_cast eisEmbedding_norm_sq_eq_absNorm_span z
  rw [normalizedRow, div_pow, hrow, hn]

theorem double_divisor_factorization {κ : Type*} [DecidableEq κ]
    (z : κ → ℂ) (T U : Finset κ) (hTU : Disjoint T U) :
    (∑ D ∈ T.powerset, ∑ E ∈ (T ∪ U).powerset,
      (-1 : ℂ) ^ E.card * (∏ i ∈ D, z i) * ∏ i ∈ E, z i) =
    (∏ i ∈ T, (1 - z i ^ 2)) *
      ∑ E ∈ U.powerset, (-1 : ℂ) ^ E.card * ∏ i ∈ E, z i := by
  have hm (V : Finset κ) :
      (∑ E ∈ V.powerset, (-1 : ℂ) ^ E.card * ∏ i ∈ E, z i) =
      ∏ i ∈ V, (1 - z i) := by
    rw [Finset.prod_sub]
    simp only [Finset.prod_const_one, mul_one]
  calc
    _ = (∑ D ∈ T.powerset, ∏ i ∈ D, z i) *
        (∑ E ∈ (T ∪ U).powerset, (-1 : ℂ) ^ E.card * ∏ i ∈ E, z i) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro D _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E _
      ring
    _ = (∏ i ∈ T, (1 + z i)) * ((∏ i ∈ T, (1 - z i)) * ∏ i ∈ U, (1 - z i)) := by
      rw [← Finset.prod_one_add, hm, Finset.prod_union hTU]
    _ = (∏ i ∈ T, (1 - z i ^ 2)) * ∏ i ∈ U, (1 - z i) := by
      rw [← mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      ring
    _ = _ := by rw [hm]

theorem actual_double_divisor_cancellation {ι κ : Type*} [DecidableEq κ]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι)
    (q : κ → O) [∀ i, (Ideal.span {q i}).IsMaximal]
    (hprime : ∀ i, Prime (Ideal.span {q i}))
    (hinj : Function.Injective (fun i => (Ideal.span {q i} : Ideal O)))
    (T U : Finset κ) (hTU : Disjoint T U) :
    (∑ D ∈ T.powerset, ∑ E ∈ (T ∪ U).powerset,
      (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {q i}) : ℂ) *
        normalizedRow P hg S ((∏ i ∈ D, q i) * ∏ i ∈ E, q i)) =
    (∏ i ∈ T, (1 - rowCoprimeMask P S (q i) /
        (Ideal.absNorm (Ideal.span {q i}) : ℂ))) *
      ∑ E ∈ U.powerset,
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {q i}) : ℂ) *
          normalizedRow P hg S (∏ i ∈ E, q i) := by
  simp only [prime_product_moebius (fun i => Ideal.span {q i}) hprime hinj,
    normalizedRow_mul, normalizedRow_prod, ← mul_assoc]
  have h := double_divisor_factorization (normalizedRow P hg S ∘ q) T U hTU
  simpa only [Function.comp_apply, normalizedRow_sq] using h

theorem actual_double_divisor_cancellation_coprime {ι κ : Type*} [DecidableEq κ]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι)
    (q : κ → O) [∀ i, (Ideal.span {q i}).IsMaximal]
    (hprime : ∀ i, Prime (Ideal.span {q i}))
    (hinj : Function.Injective (fun i => (Ideal.span {q i} : Ideal O)))
    (T U : Finset κ) (hTU : Disjoint T U)
    (havoid : ∀ i ∈ T, ∀ j ∈ S, q i ∉ P j) :
    (∑ D ∈ T.powerset, ∑ E ∈ (T ∪ U).powerset,
      (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {q i}) : ℂ) *
        normalizedRow P hg S ((∏ i ∈ D, q i) * ∏ i ∈ E, q i)) =
    (∏ i ∈ T, (1 - (1 : ℂ) / (Ideal.absNorm (Ideal.span {q i}) : ℂ))) *
      ∑ E ∈ U.powerset,
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {q i}) : ℂ) *
          normalizedRow P hg S (∏ i ∈ E, q i) := by
  rw [actual_double_divisor_cancellation P hg S q hprime hinj T U hTU]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hm : rowCoprimeMask P S (q i) = 1 := by
    simp only [rowCoprimeMask]
    rw [ite_eq_right]
    push Not
    exact havoid i hi
  rw [hm]

end QuadraticDivisorCancellation

end

end OAI
end OAIOriginalModule0100

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.FiniteOperator
Source SHA256: 0561af36787abe84636a4274f92539b53b78166a5de530dccd96cc4feb9acc1e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0101


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
namespace FiniteSieveOperator

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def operator (A : Matrix m n ℂ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m :=
  A.toEuclideanLin.toContinuousLinearMap

omit [DecidableEq m] in
@[simp] theorem operator_apply (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) (i : m) :
    operator A x i = ∑ j, A i j * x j := rfl

theorem operator_conjTranspose (A : Matrix m n ℂ) :
    operator A.conjTranspose = (operator A).adjoint := by
  unfold operator
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap]

theorem operator_conjTranspose_norm (A : Matrix m n ℂ) :
    ‖operator A.conjTranspose‖ = ‖operator A‖ := by
  rw [operator_conjTranspose]
  exact ContinuousLinearMap.adjoint.norm_map _

omit [DecidableEq m] in
theorem operator_zero : operator (0 : Matrix m n ℂ) = 0 := by
  ext x i
  simp

omit [DecidableEq m] in
theorem operator_add (A B : Matrix m n ℂ) : operator (A + B) = operator A + operator B := by
  ext x i
  simp [add_mul, Finset.sum_add_distrib]

omit [DecidableEq m] in
theorem operator_smul (c : ℂ) (A : Matrix m n ℂ) : operator (c • A) = c • operator A := by
  ext x i
  simp [Finset.mul_sum, mul_assoc]

omit [DecidableEq m] in
theorem operator_sum {κ : Type*} (S : Finset κ) (A : κ → Matrix m n ℂ) :
    operator (∑ k ∈ S, A k) = ∑ k ∈ S, operator (A k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [operator_zero]
  | @insert a S ha ih => simp only [Finset.sum_insert ha, operator_add, ih]

omit [DecidableEq m] in
theorem diagonal_twist_norm_le (A : Matrix m n ℂ) (l : m → ℂ) (r : n → ℂ)
    (hl : ∀ i, ‖l i‖ ≤ 1) (hr : ∀ j, ‖r j‖ ≤ 1) :
    ‖operator (fun i j => l i * A i j * r j)‖ ≤ ‖operator A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  let y : EuclideanSpace ℂ n := WithLp.toLp 2 (fun j => r j * x j)
  have hy : ‖y‖ ≤ ‖x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro j _
    change ‖r j * x j‖ ^ 2 ≤ ‖x j‖ ^ 2
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hr j)
  have heq (i : m) : operator (fun i j => l i * A i j * r j) x i = l i * operator A y i := by
    simp only [operator_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change l i * A i j * r j * x j = l i * (A i j * (r j * x j))
    ring
  have hz : ‖operator (fun i j => l i * A i j * r j) x‖ ≤ ‖operator A y‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    rw [heq, norm_mul]
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_of_le_one_left (norm_nonneg _) (hl i)
  exact hz.trans ((operator A).le_opNorm y |>.trans
    (mul_le_mul_of_nonneg_left hy (norm_nonneg _)))

omit [DecidableEq m] in
theorem separated_phase_norm_le {κ : Type*} [Fintype κ]
    (A B : Matrix m n ℂ) (c : κ → ℂ) (l : κ → m → ℂ) (r : κ → n → ℂ)
    (hl : ∀ k i, ‖l k i‖ ≤ 1) (hr : ∀ k j, ‖r k j‖ ≤ 1)
    (heq : ∀ i j, A i j = ∑ k, c k * (l k i * B i j * r k j)) :
    ‖operator A‖ ≤ (∑ k, ‖c k‖) * ‖operator B‖ := by
  let T : κ → Matrix m n ℂ := fun k i j => l k i * B i j * r k j
  have hA : A = ∑ k, c k • T k := by
    ext i j
    rw [Matrix.sum_apply]
    exact heq i j
  have hOp : operator A = ∑ k, c k • operator (T k) := by
    calc
      _ = operator (∑ k, c k • T k) := congrArg operator hA
      _ = ∑ k, operator (c k • T k) := operator_sum _ _
      _ = _ := Finset.sum_congr rfl (fun k _ => operator_smul (c k) (T k))
  rw [hOp]
  calc
    _ ≤ ∑ k, ‖c k • operator (T k)‖ := norm_sum_le _ _
    _ ≤ ∑ k, ‖c k‖ * ‖operator B‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (diagonal_twist_norm_le B (l k) (r k) (hl k) (hr k))
        (norm_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm

omit [DecidableEq m] in
theorem energy_bound (A : Matrix m n ℂ) (u : n → ℂ) :
    (∑ i, ‖∑ j, A i j * u j‖ ^ 2) ≤ ‖operator A‖ ^ 2 * ∑ j, ‖u j‖ ^ 2 := by
  let x : EuclideanSpace ℂ n := WithLp.toLp 2 u
  have h := (operator A).le_opNorm x
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [mul_pow, EuclideanSpace.norm_sq_eq, operator_apply, x, PiLp.toLp_apply] using hs

end FiniteSieveOperator

section
open scoped BigOperators Classical
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT RayFourExpansion

def quadraticMatrix {ι m n : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (rows : m → Finset ι) (cols : n → Finset ι) : Matrix m n ℂ :=
  fun i j => quadraticSymbol p hg (cols j) (rows i)

def quadraticSieveNorm {ι m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (rows : m → Finset ι) (cols : n → Finset ι) : ℝ :=
  ‖FiniteSieveOperator.operator (quadraticMatrix p hg rows cols)‖ ^ 2

theorem quadraticSieveNorm_energy {ι m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (rows : m → Finset ι) (cols : n → Finset ι) (a : n → ℂ) :
    (∑ i, ‖∑ j, quadraticSymbol p hg (cols j) (rows i) * a j‖ ^ 2) ≤
      quadraticSieveNorm p hg rows cols * ∑ j, ‖a j‖ ^ 2 :=
  FiniteSieveOperator.energy_bound (quadraticMatrix p hg rows cols) a

theorem quadratic_matrix_norm_reverse_le
    {ι m n : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (rows : m → Finset ι) (cols : n → Finset ι) :
    ‖FiniteSieveOperator.operator (quadraticMatrix p hg rows cols)‖ ≤
      512 * ‖FiniteSieveOperator.operator (quadraticMatrix p hg cols rows)‖ := by
  let A := quadraticMatrix p hg rows cols
  let B := (quadraticMatrix p hg cols rows).conjTranspose
  let c : RayCharacter × RayCharacter → ℂ := fun k => crossCoeff k.1 k.2
  let l : RayCharacter × RayCharacter → m → ℂ := fun k i =>
    rayCharacter k.2 (∏ s ∈ rows i, p s)
  let r : RayCharacter × RayCharacter → n → ℂ := fun k j =>
    rayCharacter k.1 (∏ s ∈ cols j, p s)
  have hB (i : m) (j : n) : B i j = quadraticSymbol p hg (rows i) (cols j) := by
    change star (quadraticSymbol p hg (rows i) (cols j)) = _
    exact quadraticRow_star _ _ _ _
  have hl (k : RayCharacter × RayCharacter) (i : m) : ‖l k i‖ ≤ 1 :=
    FiniteRayExpansion.norm_char_le_one k.2 _
  have hr (k : RayCharacter × RayCharacter) (j : n) : ‖r k j‖ ≤ 1 :=
    FiniteRayExpansion.norm_char_le_one k.1 _
  have hA (i : m) (j : n) : A i j = ∑ k, c k * (l k i * B i j * r k j) := by
    rw [hB, Fintype.sum_prod_type]
    change quadraticSymbol p hg (cols j) (rows i) = _
    rw [quadraticSymbol_reciprocity_characters p hp hcop hg hc]
    apply Finset.sum_congr rfl
    intro χ _
    apply Finset.sum_congr rfl
    intro η _
    dsimp [c, l, r]
    ring
  have hmass : (∑ k, ‖c k‖) ≤ 512 := by
    simpa only [c, Fintype.sum_prod_type] using crossCoeff_sum_norm_le
  calc
    _ ≤ (∑ k, ‖c k‖) * ‖FiniteSieveOperator.operator B‖ :=
      FiniteSieveOperator.separated_phase_norm_le A B c l r hl hr hA
    _ ≤ 512 * ‖FiniteSieveOperator.operator B‖ :=
      mul_le_mul_of_nonneg_right hmass (norm_nonneg _)
    _ = _ := by
      change 512 * ‖FiniteSieveOperator.operator
        (quadraticMatrix p hg cols rows).conjTranspose‖ = _
      rw [FiniteSieveOperator.operator_conjTranspose_norm]

theorem quadraticSieveNorm_reverse_le
    {ι m n : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (rows : m → Finset ι) (cols : n → Finset ι) :
    quadraticSieveNorm p hg rows cols ≤ 262144 * quadraticSieveNorm p hg cols rows := by
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (quadratic_matrix_norm_reverse_le p hp hcop hg hc rows cols) 2
  simpa only [quadraticSieveNorm, mul_pow, show (512 : ℝ) ^ 2 = 262144 by norm_num] using h

end QuadraticInitialBound

open scoped BigOperators Classical
open Filter IdealMobiusDivisorSum UniqueFactorizationMonoid

namespace IdealDivisorBound
abbrev O := ActualEisensteinCubic.O

theorem divisor_ne_zero {I J : Ideal O} (hI : I ≠ ⊥) (hJ : J ∈ idealDivisors I) : J ≠ 0 := by
  intro hz
  have hd := (mem_idealDivisors hI).mp hJ
  rw [hz, zero_dvd_iff] at hd
  exact hI hd

theorem divisor_card_le_product (I : Ideal O) (hI : I ≠ ⊥) :
    (idealDivisors I).card ≤
      ∏ P ∈ primeSupport I, ((normalizedFactors I).count P + 1) := by
  change (idealDivisors I).card ≤
    ∏ P ∈ (normalizedFactors I).toFinset, ((normalizedFactors I).count P + 1)
  rw [← Multiset.card_Iic]
  apply Finset.card_le_card_of_injOn normalizedFactors
  · intro J hJ
    change normalizedFactors J ∈ Finset.Iic (normalizedFactors I)
    rw [Finset.mem_Iic]
    exact (dvd_iff_normalizedFactors_le_normalizedFactors
      (divisor_ne_zero hI hJ) hI).mp ((mem_idealDivisors hI).mp hJ)
  · intro J hJ K hK he
    calc
      J = (normalizedFactors J).prod := (Ideal.prod_normalizedFactors_eq_self (divisor_ne_zero hI hJ)).symm
      _ = (normalizedFactors K).prod := congrArg Multiset.prod he
      _ = K := Ideal.prod_normalizedFactors_eq_self (divisor_ne_zero hI hK)

theorem linear_le_geometric (b : ℝ) (hb : 1 < b) (n : ℕ) :
    (n : ℝ) + 1 ≤ (1 + (b - 1)⁻¹) * b ^ n := by
  have hδ : 0 < b - 1 := sub_pos.mpr hb
  have hn := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ b by linarith) n
  have hn' : (n : ℝ) ≤ b ^ n / (b - 1) := by
    apply (le_div_iff₀ hδ).mpr
    linarith
  have h1 : (1 : ℝ) ≤ b ^ n := one_le_pow₀ hb.le
  calc
    (n : ℝ) + 1 ≤ b ^ n / (b - 1) + b ^ n := add_le_add hn' h1
    _ = _ := by ring

theorem support_norm_two_le {I P : Ideal O} (hP : P ∈ primeSupport I) :
    2 ≤ Ideal.absNorm P := by
  have hp := support_prime hP
  have h0 : Ideal.absNorm P ≠ 0 := by
    intro h
    exact hp.ne_zero (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm P ≠ 1 := by
    intro h
    have ht := Ideal.absNorm_eq_one_iff.mp h
    apply hp.not_isUnit
    rw [ht]
    simpa only [Ideal.one_eq_top] using (show IsUnit (1 : Ideal O) from isUnit_one)
  omega

theorem norm_factor_product (I : Ideal O) (hI : I ≠ ⊥) :
    (∏ P ∈ primeSupport I, (Ideal.absNorm P : ℝ) ^ (normalizedFactors I).count P) =
      Ideal.absNorm I := by
  have he := congrArg (fun J : Ideal O => (Ideal.absNorm J : ℝ))
    (Ideal.prod_normalizedFactors_eq_self hI)
  rw [Finset.prod_multiset_count] at he
  simpa only [primeSupport, map_prod, map_pow, Nat.cast_prod, Nat.cast_pow] using he

theorem ideal_divisor_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal O, I ≠ ⊥ →
      ((idealDivisors I).card : ℝ) ≤ C * (Ideal.absNorm I : ℝ) ^ ε := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2 : ℝ)))
  let small : Finset (Ideal O) :=
    (Ideal.finite_setOfPred_absNorm_le (S := O) N).toFinset
  let b : ℝ := (2 : ℝ) ^ ε
  have hb : 1 < b := by
    dsimp [b]
    exact Real.one_lt_rpow (by norm_num) hε
  let c : ℝ := 1 + (b - 1)⁻¹
  have hc : 1 ≤ c := by
    dsimp [c]
    have hi : 0 ≤ (b - 1)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hb.le)
    linarith
  refine ⟨c ^ small.card, by positivity, ?_⟩
  intro I hI
  let S := primeSupport I
  let e := fun P : Ideal O => (normalizedFactors I).count P
  have hfac (P : Ideal O) (hP : P ∈ S) :
      ((e P + 1 : ℕ) : ℝ) ≤
        (if P ∈ small then c else 1) * ((Ideal.absNorm P : ℝ) ^ ε) ^ e P := by
    have hnorm : (2 : ℝ) ≤ Ideal.absNorm P := by exact_mod_cast support_norm_two_le hP
    have hbase : b ≤ (Ideal.absNorm P : ℝ) ^ ε :=
      Real.rpow_le_rpow (by norm_num) hnorm hε.le
    by_cases hp : P ∈ small
    · rw [ite_eq_left hp]
      have hlin := linear_le_geometric b hb (e P)
      have hl : ((e P + 1 : ℕ) : ℝ) ≤ c * b ^ e P := by
        simpa only [Nat.cast_add, Nat.cast_one, c] using hlin
      apply hl.trans
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hbase _) (by positivity)
    · rw [ite_eq_right hp, one_mul]
      have hn : N ≤ Ideal.absNorm P := by
        have : ¬ Ideal.absNorm P ≤ N := fun h => hp (by simpa [small] using h)
        omega
      have hp2 := hN _ hn
      calc
        _ ≤ (2 : ℝ) ^ e P := by
          have hh := one_add_mul_sub_le_pow (by norm_num : (-1 : ℝ) ≤ 2) (e P)
          norm_num at hh ⊢
          linarith
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) hp2 _
  have hprod := Finset.prod_le_prod₀
    (fun P (_ : P ∈ S) => (by positivity : (0 : ℝ) ≤ ((e P + 1 : ℕ) : ℝ))) hfac
  have hconst : (∏ P ∈ S, if P ∈ small then c else 1) ≤ c ^ small.card := by
    have he : (∏ P ∈ S, if P ∈ small then c else 1) = c ^ (S ∩ small).card := by
      simp []
    rw [he]
    exact pow_le_pow_right₀ hc (Finset.card_le_card Finset.inter_subset_right)
  have hpow : (∏ P ∈ S, ((Ideal.absNorm P : ℝ) ^ ε) ^ e P) =
      (Ideal.absNorm I : ℝ) ^ ε := by
    calc
      _ = ∏ P ∈ S, ((Ideal.absNorm P : ℝ) ^ e P) ^ ε := by
        apply Finset.prod_congr rfl
        intro P hP
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
          ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        rw [mul_comm]
      _ = (∏ P ∈ S, (Ideal.absNorm P : ℝ) ^ e P) ^ ε :=
        Real.finsetProd_rpow S _ (fun _ _ => by positivity) ε
      _ = _ := by rw [norm_factor_product I hI]
  have hcard : ((idealDivisors I).card : ℝ) ≤ ∏ P ∈ S, ((e P + 1 : ℕ) : ℝ) := by
    exact_mod_cast divisor_card_le_product I hI
  apply hcard.trans
  rw [Finset.prod_mul_distrib, hpow] at hprod
  exact hprod.trans (mul_le_mul_of_nonneg_right hconst (by positivity))

end IdealDivisorBound
end

namespace SecondPassFiber
open scoped BigOperators Classical
open IdealMobiusDivisorSum ConcretePrimeRowBridge

abbrev O := ActualEisensteinCubic.O

@[ext] structure OldTuple where
  core : Fin 8 → Ideal O
  v : Ideal O
  j2 : Ideal O
  b2 : Ideal O
  row : O

structure Valid (x : OldTuple) (F b0 : Ideal O) (y : O) : Prop where
  label : x.core 0 * x.core 1 * x.core 2 * x.v = F
  j_split : x.core 3 * x.j2 = x.core 0
  b_split : x.core 4 * x.b2 = b0 ^ 2 * x.j2 ^ 2 * x.core 3
  a1 : x.core 5 ∣ x.core 4 * x.b2
  a2 : x.core 6 ∣ x.core 4 * x.b2
  d : x.core 7 ∣ F * b0
  row_eq : idealGenerator (x.core 7) * idealGenerator (x.core 2) * x.row = y

def divisorTarget (F b0 : Ideal O) : Ideal O := (F * b0) ^ 2

theorem core_dvd_target (x : OldTuple) (F b0 : Ideal O) (y : O)
    (h : Valid x F b0 y) (i : Fin 8) : x.core i ∣ divisorTarget F b0 := by
  have hJ : x.core 0 ∣ F := by
    rw [← h.label]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  have hC : x.core 1 ∣ F := by
    rw [← h.label]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
  have he : x.core 2 ∣ F := by
    rw [← h.label]
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hs : x.core 3 ∣ F := by
    apply dvd_trans _ hJ
    rw [← h.j_split]
    exact dvd_mul_right _ _
  have hFT : F ∣ divisorTarget F b0 := by
    dsimp [divisorTarget]
    exact (dvd_mul_right F b0).trans (dvd_pow_self _ (by decide))
  have hbprod : x.core 4 * x.b2 ∣ divisorTarget F b0 := by
    apply dvd_trans (b := b0 ^ 2 * x.core 0 ^ 2)
    · refine ⟨x.core 3, ?_⟩
      rw [h.b_split, ← h.j_split]
      ring
    · dsimp [divisorTarget]
      rw [mul_pow, mul_comm (F ^ 2)]
      exact mul_dvd_mul_left _ (pow_dvd_pow_of_dvd hJ 2)
  fin_cases i
  · exact hJ.trans hFT
  · exact hC.trans hFT
  · exact he.trans hFT
  · exact hs.trans hFT
  · exact (dvd_mul_right _ _).trans hbprod
  · exact h.a1.trans hbprod
  · exact h.a2.trans hbprod
  · exact h.d.trans (dvd_pow_self _ (by decide))

theorem target_ne_zero (F b0 : Ideal O) (hF : F ≠ ⊥) (hb0 : b0 ≠ ⊥) :
    divisorTarget F b0 ≠ 0 := pow_ne_zero _ (mul_ne_zero hF hb0)

theorem core_ne_zero (x : OldTuple) (F b0 : Ideal O) (y : O)
    (hF : F ≠ ⊥) (hb0 : b0 ≠ ⊥) (h : Valid x F b0 y) (i : Fin 8) :
    x.core i ≠ 0 := by
  intro he
  have hd := core_dvd_target x F b0 y h i
  rw [he, zero_dvd_iff] at hd
  exact target_ne_zero F b0 hF hb0 hd

theorem valid_core_injective (F b0 : Ideal O) (y : O)
    (hF : F ≠ ⊥) (hb0 : b0 ≠ ⊥) {x z : OldTuple}
    (hx : Valid x F b0 y) (hz : Valid z F b0 y) (hcore : x.core = z.core) : x = z := by
  have hc (i : Fin 8) : x.core i = z.core i := congrFun hcore i
  have hv : x.v = z.v := by
    apply mul_left_cancel₀
      (mul_ne_zero (mul_ne_zero (core_ne_zero x F b0 y hF hb0 hx 0)
        (core_ne_zero x F b0 y hF hb0 hx 1)) (core_ne_zero x F b0 y hF hb0 hx 2))
    calc
      _ = F := hx.label
      _ = _ := by simpa only [hc] using hz.label.symm
  have hj : x.j2 = z.j2 := by
    apply mul_left_cancel₀ (core_ne_zero x F b0 y hF hb0 hx 3)
    calc
      _ = x.core 0 := hx.j_split
      _ = _ := by simpa only [hc] using hz.j_split.symm
  have hb : x.b2 = z.b2 := by
    apply mul_left_cancel₀ (core_ne_zero x F b0 y hF hb0 hx 4)
    calc
      _ = b0 ^ 2 * x.j2 ^ 2 * x.core 3 := hx.b_split
      _ = _ := by simpa only [hc, hj] using hz.b_split.symm
  have hgen (i : Fin 8) : idealGenerator (x.core i) ≠ 0 := by
    intro he
    apply core_ne_zero x F b0 y hF hb0 hx i
    rw [← span_idealGenerator (x.core i), he]
    simp
  have hr : x.row = z.row := by
    apply mul_left_cancel₀ (mul_ne_zero (hgen 7) (hgen 2))
    calc
      _ = y := hx.row_eq
      _ = _ := by simpa only [hc] using hz.row_eq.symm
  exact OldTuple.ext hcore hv hj hb hr

theorem valid_tuple_card_le (s : Finset OldTuple) (F b0 : Ideal O) (y : O)
    (hF : F ≠ ⊥) (hb0 : b0 ≠ ⊥) (hs : ∀ x ∈ s, Valid x F b0 y) :
    s.card ≤ (idealDivisors (divisorTarget F b0)).card ^ 8 := by
  let D := idealDivisors (divisorTarget F b0)
  let encode (x : s) : Fin 8 → D := fun i => ⟨x.val.core i, by
    apply (mem_idealDivisors (target_ne_zero F b0 hF hb0)).mpr
    exact core_dvd_target x.val F b0 y (hs x.val x.property) i⟩
  have hinj : Function.Injective encode := by
    intro x z he
    apply Subtype.ext
    apply valid_core_injective F b0 y hF hb0 (hs x.val x.property) (hs z.val z.property)
    funext i
    exact congrArg Subtype.val (congrFun he i)
  have hc := Fintype.card_le_of_injective encode hinj
  simpa [D] using hc

theorem valid_tuple_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset OldTuple) (F b0 : Ideal O) (y : O),
      F ≠ ⊥ → b0 ≠ ⊥ → (∀ x ∈ s, Valid x F b0 y) →
      (s.card : ℝ) ≤ C * ((Ideal.absNorm F : ℝ) * Ideal.absNorm b0) ^ ε := by
  obtain ⟨C, hC, h⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 16) (by positivity)
  refine ⟨C ^ 8, by positivity, ?_⟩
  intro s F b0 y hF hb0 hs
  have hc : (s.card : ℝ) ≤ ((idealDivisors (divisorTarget F b0)).card : ℝ) ^ 8 := by
    exact_mod_cast valid_tuple_card_le s F b0 y hF hb0 hs
  have hd := pow_le_pow_left₀ (by positivity)
    (h (divisorTarget F b0) (target_ne_zero F b0 hF hb0)) 8
  apply hc.trans (hd.trans_eq ?_)
  rw [mul_pow]
  congr 1
  simp only [divisorTarget, map_pow, map_mul, Nat.cast_pow, Nat.cast_mul]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

def newLabel (x : OldTuple) : Ideal O := x.core 0 * x.core 1 * x.core 2 * x.v
def newRow (x : OldTuple) : O :=
  idealGenerator (x.core 7) * idealGenerator (x.core 2) * x.row

theorem second_energy_pushforward (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset OldTuple) (t : Finset (Ideal O × O))
      (b0 : Ideal O) (w : OldTuple → ℂ) (P : Ideal O × O → ℂ) (B H : ℝ),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ H →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ t) →
      (∀ z ∈ t, z.1 ≠ ⊥) →
      (∀ z ∈ t, (Ideal.absNorm z.1 : ℝ) ≤ H) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∑ x ∈ s, ‖w x‖ * ‖P (newLabel x, newRow x)‖ ^ 2) ≤
        B * C * (H * Ideal.absNorm b0) ^ ε * ∑ z ∈ t, ‖P z‖ ^ 2 := by
  obtain ⟨C, hC, hc⟩ := valid_tuple_small_power ε hε
  refine ⟨C, hC, ?_⟩
  intro s t b0 w P B H hb0 hB hH hvalid hmap ht hnorm hw
  have hpush := DescentWeightedCauchy.bounded_energy_pushforward
    s t (fun x => (newLabel x, newRow x)) w P B hmap hw
  apply hpush.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have hval : ∀ x ∈ s.filter (fun x => (newLabel x, newRow x) = z), Valid x z.1 b0 z.2 := by
    intro x hx
    have he := (Finset.mem_filter.mp hx).2
    have hv := hvalid x (Finset.mem_filter.mp hx).1
    have h1 : newLabel x = z.1 := congrArg Prod.fst he
    have h2 : newRow x = z.2 := congrArg Prod.snd he
    simpa only [h1, h2] using hv
  have hfiber := hc (s.filter (fun x => (newLabel x, newRow x) = z)) z.1 b0 z.2
    (ht z hz) hb0 hval
  have hgrowth : (Ideal.absNorm z.1 : ℝ) * Ideal.absNorm b0 ≤ H * Ideal.absNorm b0 :=
    mul_le_mul_of_nonneg_right (hnorm z hz) (by positivity)
  have hcard := hfiber.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) hgrowth hε.le) hC.le)
  have hterm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcard hB) (sq_nonneg ‖P z‖)
  simpa only [mul_assoc] using hterm

end SecondPassFiber

open scoped BigOperators Classical
namespace FirstPassCubeLabels
open ActualEisensteinCubic

theorem conductorExponent_val (parityBit ε₁ ε₂ : Bool) :
    (conductorExponent parityBit ε₁ ε₂).val = (bit ε₁ + 5 * bit ε₂ + 3 * bit parityBit) % 6 := by
  cases parityBit <;> cases ε₁ <;> cases ε₂ <;> decide

theorem cube_pair_exponent_mod (m₁ m₂ : ℕ) (ε₁ ε₂ : Bool) :
    (bit ε₁ + 5 * bit ε₂ + 3 * m₁ + 15 * m₂) % 6 =
      (conductorExponent (parity (m₁ + m₂)) ε₁ ε₂).val := by
  have hmod := Nat.mod_lt (m₁ + m₂) (by decide : 0 < 2)
  rw [conductorExponent_val]
  cases ε₁ <;> cases ε₂ <;> by_cases h : (m₁ + m₂) % 2 = 1 <;>
    norm_num [parity, bit, h] <;> omega

def cubePairLocal (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)
    (m₁ m₂ : ℕ) (ε₁ ε₂ : Bool) (z : O) : ℂ :=
  let q := canonicalSextic P hg (Ideal.Quotient.mk P z)
  q ^ bit ε₁ * star (q ^ bit ε₂) * q ^ (3 * m₁) * star (q ^ (3 * m₂))

theorem cubePairLocal_eq_character
    (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)
    (m₁ m₂ : ℕ) (ε₁ ε₂ : Bool) (hm : 0 < m₁ + m₂ + bit ε₁ + bit ε₂) (z : O) :
    cubePairLocal P hg m₁ m₂ ε₁ ε₂ z =
      (canonicalSextic P hg ^ (conductorExponent (parity (m₁ + m₂)) ε₁ ε₂).val)
        (Ideal.Quotient.mk P z) := by
  let q := canonicalSextic P hg (Ideal.Quotient.mk P z)
  have hstar : star q = q ^ 5 := by
    have hs := canonicalSextic_conj_as_row_label P hg z
    change star q = q * q ^ 4 at hs
    rw [hs]
    ring
  have hleft : cubePairLocal P hg m₁ m₂ ε₁ ε₂ z =
      q ^ (bit ε₁ + 5 * bit ε₂ + 3 * m₁ + 15 * m₂) := by
    change q ^ bit ε₁ * star (q ^ bit ε₂) * q ^ (3 * m₁) * star (q ^ (3 * m₂)) = _
    simp only [star_pow, hstar, ← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hleft]
  by_cases hz : z ∈ P
  · have hq : q = 0 := by
      change canonicalSextic P hg (Ideal.Quotient.mk P z) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, MulChar.map_zero]
    rw [hq, Ideal.Quotient.eq_zero_iff_mem.mpr hz, MulChar.map_zero]
    exact zero_pow (by omega)
  · have hu : IsUnit (Ideal.Quotient.mk P z) := by
      let : Field (O ⧸ P) := Ideal.Quotient.field P
      exact isUnit_iff_ne_zero.mpr (fun h => hz (Ideal.Quotient.eq_zero_iff_mem.mp h))
    have h6 : q ^ 6 = 1 := by
      have h := canonicalSextic_sixth_power_mask P hg z
      simp only [map_pow, ite_eq_right hz] at h
      exact h
    rw [pow_eq_pow_mod _ h6, cube_pair_exponent_mod]
    exact (MulChar.pow_apply_coe _ _ hu.unit).symm

def cubeConductorSupport {κ : Type*} (B : Finset κ) (v₁ v₂ : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : Finset κ :=
  B.filter (fun j => conductorExponent (parity (v₁ j + v₂ j)) (ε₁ j) (ε₂ j) ≠ 0)

def cubePrincipalSupport {κ : Type*} (B : Finset κ) (v₁ v₂ : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : Finset κ :=
  B.filter (fun j => conductorExponent (parity (v₁ j + v₂ j)) (ε₁ j) (ε₂ j) = 0)

theorem cubeConductorExponent_ne_zero {κ : Type*} (B : Finset κ)
    (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool) (j : cubeConductorSupport B v₁ v₂ ε₁ ε₂) :
    (conductorExponent (parity (v₁ j.val + v₂ j.val)) (ε₁ j.val) (ε₂ j.val)).val ≠ 0 := by
  exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp j.property).2

theorem cubeConductorExponent_lt_six {κ : Type*} (B : Finset κ)
    (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool) (j : cubeConductorSupport B v₁ v₂ ε₁ ε₂) :
    (conductorExponent (parity (v₁ j.val + v₂ j.val)) (ε₁ j.val) (ε₂ j.val)).val < 6 :=
  ZMod.val_lt _

def multiplicityRow {κ : Type*} (P : κ → Ideal O) [∀ j, (P j).IsMaximal]
    (hg : ∀ j, lambda ∉ P j) (B : Finset κ) (v : κ → ℕ) (z : O) : ℂ :=
  ∏ j ∈ B, canonicalSextic (P j) (hg j) (Ideal.Quotient.mk (P j) z) ^ v j

def cubePairRow {κ : Type*} (P : κ → Ideal O) [∀ j, (P j).IsMaximal]
    (hg : ∀ j, lambda ∉ P j) (B : Finset κ) (v₁ v₂ : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) (z : O) : ℂ :=
  finiteSquarefreeRow P hg (B.filter fun j => ε₁ j) z *
    star (finiteSquarefreeRow P hg (B.filter fun j => ε₂ j) z) *
    multiplicityRow P hg B v₁ z ^ 3 * star (multiplicityRow P hg B v₂ z ^ 3)

private theorem row_filter_eq_power_product {κ : Type*}
    (P : κ → Ideal O) [∀ j, (P j).IsMaximal] (hg : ∀ j, lambda ∉ P j)
    (B : Finset κ) (ε : κ → Bool) (z : O) :
    finiteSquarefreeRow P hg (B.filter fun j => ε j) z =
      ∏ j ∈ B, canonicalSextic (P j) (hg j) (Ideal.Quotient.mk (P j) z) ^ bit (ε j) := by
  simp only [finiteSquarefreeRow, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro j hj
  cases ε j <;> simp [bit]

theorem cubePairRow_eq_product {κ : Type*}
    (P : κ → Ideal O) [∀ j, (P j).IsMaximal] (hg : ∀ j, lambda ∉ P j)
    (B : Finset κ) (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool) (z : O) :
    cubePairRow P hg B v₁ v₂ ε₁ ε₂ z =
      ∏ j ∈ B, cubePairLocal (P j) (hg j) (v₁ j) (v₂ j) (ε₁ j) (ε₂ j) z := by
  simp only [cubePairRow, row_filter_eq_power_product, multiplicityRow,
    ← Finset.prod_pow, star_prod, ← Finset.prod_mul_distrib, ← pow_mul]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [cubePairLocal, Nat.mul_comm]

private theorem principal_product_eq_mask {κ : Type*}
    (P : κ → Ideal O) [∀ j, (P j).IsMaximal] (B : Finset κ) (z : O) :
    (∏ j ∈ B, (1 : MulChar (O ⧸ P j) ℂ) (Ideal.Quotient.mk (P j) z)) =
      rowCoprimeMask P B z := by
  by_cases h : ∃ j ∈ B, z ∈ P j
  · rw [rowCoprimeMask, ite_eq_left h]
    obtain ⟨j, hj, hz⟩ := h
    apply Finset.prod_eq_zero hj
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, MulChar.map_zero]
  · rw [rowCoprimeMask, ite_eq_right h]
    apply Finset.prod_eq_one
    intro j hj
    apply MulChar.one_apply
    let : Field (O ⧸ P j) := Ideal.Quotient.field (P j)
    apply isUnit_iff_ne_zero.mpr
    exact fun hz => h ⟨j, hj, Ideal.Quotient.eq_zero_iff_mem.mp hz⟩

theorem cubePairRow_conductor_selection {κ : Type*}
    (P : κ → Ideal O) [∀ j, (P j).IsMaximal] (hg : ∀ j, lambda ∉ P j)
    (B : Finset κ) (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hcover : ∀ j ∈ B, 0 < v₁ j + v₂ j + bit (ε₁ j) + bit (ε₂ j)) (z : O) :
    cubePairRow P hg B v₁ v₂ ε₁ ε₂ z =
      rowCoprimeMask P (cubePrincipalSupport B v₁ v₂ ε₁ ε₂) z *
        finiteSexticRow (fun j : cubeConductorSupport B v₁ v₂ ε₁ ε₂ => P j.val)
          (fun j => hg j.val)
          (fun j => (conductorExponent (parity (v₁ j.val + v₂ j.val))
            (ε₁ j.val) (ε₂ j.val)).val) z := by
  let e := fun j => conductorExponent (parity (v₁ j + v₂ j)) (ε₁ j) (ε₂ j)
  let f := fun j => (canonicalSextic (P j) (hg j) ^ (e j).val) (Ideal.Quotient.mk (P j) z)
  have hlocal : cubePairRow P hg B v₁ v₂ ε₁ ε₂ z = ∏ j ∈ B, f j := by
    rw [cubePairRow_eq_product]
    apply Finset.prod_congr rfl
    intro j hj
    exact cubePairLocal_eq_character (P j) (hg j) (v₁ j) (v₂ j)
      (ε₁ j) (ε₂ j) (hcover j hj) z
  have hzero : (∏ j ∈ B.filter (fun j => e j = 0), f j) =
      rowCoprimeMask P (cubePrincipalSupport B v₁ v₂ ε₁ ε₂) z := by
    rw [← principal_product_eq_mask]
    apply Finset.prod_congr rfl
    intro j hj
    have he : e j = 0 := (Finset.mem_filter.mp hj).2
    simp only [f, he, ZMod.val_zero, pow_zero]
  rw [hlocal, ← Finset.prod_filter_mul_prod_filter_not B (fun j => e j = 0) f, hzero]
  congr 1
  exact (Finset.prod_coe_sort (s := cubeConductorSupport B v₁ v₂ ε₁ ε₂) (f := f)).symm

theorem cubeConductorPrimes_pairwise_coprime {κ : Type*}
    (P : κ → Ideal O) [∀ j, (P j).IsMaximal] (hinj : Function.Injective P)
    (B : Finset κ) (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool) :
    Pairwise (Function.onFun IsCoprime
      (fun j : cubeConductorSupport B v₁ v₂ ε₁ ε₂ => P j.val)) := by
  intro i j hij
  apply Ideal.isCoprime_of_isMaximal
  exact fun he => hij (Subtype.ext (hinj he))

open scoped SchwartzMap ContDiff
open ConcreteTraceCRT
open EisensteinSchwartzPoisson (paperRadialFourier)

def cubePairPoissonKernel {κ : Type*} [DecidableEq κ]
    (P : κ → Ideal O) [∀ j, (P j).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ j, lambda ∉ P j) (B : Finset κ) (v₁ v₂ : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  let Q := fun j : cubeConductorSupport B v₁ v₂ ε₁ ε₂ => P j.val
  let hQ := cubeConductorPrimes_pairwise_coprime P hinj B v₁ v₂ ε₁ ε₂
  let eg := fun j : cubeConductorSupport B v₁ v₂ ε₁ ε₂ =>
    (conductorExponent (parity (v₁ j.val + v₂ j.val)) (ε₁ j.val) (ε₂ j.val)).val
  let row := finiteSexticRow Q (fun j => hg j.val) eg
  let c := finitePrimeModulus Q
  ((scale : ℂ) * canonicalNormalizedGauss Q hQ (fun j => hg j.val) eg /
    (‖eisEmbedding c‖ : ℂ)) *
    ∑ E ∈ (cubePrincipalSupport B v₁ v₂ ε₁ ε₂).powerset,
      let d := primeSubsetGenerator P E
      ((UniqueFactorizationMonoid.moebius (∏ j ∈ E, P j) : ℂ) * row d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
        ∑' h : O, star (row h) * paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding c‖ ^ 2))

theorem cubePairRow_radial_poisson {κ : Type*} [DecidableEq κ]
    (P : κ → Ideal O) [∀ j, (P j).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ j, lambda ∉ P j) (hc : ∀ j, ringChar (O ⧸ P j) ≠ 2)
    (B : Finset κ) (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hcover : ∀ j ∈ B, 0 < v₁ j + v₂ j + bit (ε₁ j) + bit (ε₂ j))
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' z : O, cubePairRow P hg B v₁ v₂ ε₁ ε₂ z *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      cubePairPoissonKernel P hinj hg B v₁ v₂ ε₁ ε₂ W scale := by
  simp_rw [cubePairRow_conductor_selection P hg B v₁ v₂ ε₁ ε₂ hcover]
  exact canonical_masked_radial_poisson_collected P hinj
    (cubePrincipalSupport B v₁ v₂ ε₁ ε₂)
    (fun j : cubeConductorSupport B v₁ v₂ ε₁ ε₂ => P j.val)
    (cubeConductorPrimes_pairwise_coprime P hinj B v₁ v₂ ε₁ ε₂)
    (fun j => hg j.val) (fun j => hc j.val)
    (fun j => (conductorExponent (parity (v₁ j.val + v₂ j.val)) (ε₁ j.val) (ε₂ j.val)).val)
    (cubeConductorExponent_ne_zero B v₁ v₂ ε₁ ε₂)
    (cubeConductorExponent_lt_six B v₁ v₂ ε₁ ε₂) W scale hscale

end FirstPassCubeLabels

end

end OAI
end OAIOriginalModule0101

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.MainTermDifference
Source SHA256: abeb2af5e9ed8037c1a3a72a7c00d45ff9a486586e091ed92d38205ed9fde54d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0102


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
namespace QuadraticMainTermDifference
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic QuadraticDivisorCancellation QuadraticMainBoundary

theorem sum_powerset_disjoint_union {κ V : Type*} [DecidableEq κ] [AddCommMonoid V]
    (T G : Finset κ) (hTG : Disjoint T G) (f : Finset κ → V) :
    (∑ A ∈ (T ∪ G).powerset, f A) =
      ∑ H ∈ T.powerset, ∑ D ∈ G.powerset, f (H ∪ D) := by
  induction T using Finset.induction_on generalizing f with
  | empty => simp
  | @insert i T hi ih =>
    have hiG : i ∉ G := fun h => Finset.disjoint_left.mp hTG (by simp) h
    have hTG' : Disjoint T G := Finset.disjoint_of_subset_left (Finset.subset_insert _ _) hTG
    have hiU : i ∉ T ∪ G := by simp [hi, hiG]
    rw [Finset.insert_union, Finset.sum_powerset_insert hiU]
    rw [ih hTG' f, ih hTG' (fun A => f (insert i A))]
    rw [Finset.sum_powerset_insert hi]
    simp only [Finset.insert_union]

def normCutoff {κ : Type*} (q : κ → O) (K : ℝ) (A : Finset κ) : ℂ :=
  if (Ideal.absNorm (∏ i ∈ A, Ideal.span {q i}) : ℝ) ≤ K then 1 else 0

def partialSquarefreeSum {ι κ : Type*} [DecidableEq κ]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι)
    (q : κ → O) (K : ℝ) (V : Finset κ) : ℂ :=
  ∑ A ∈ V.powerset, normalizedRow P hg S (∏ i ∈ A, q i) * normCutoff q K A

def divisorSum {ι κ : Type*} [DecidableEq κ]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι)
    (q : κ → O) (G : Finset κ) : ℂ :=
  ∑ E ∈ G.powerset, (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {q i}) : ℂ) *
    normalizedRow P hg S (∏ i ∈ E, q i)

theorem actual_main_terms_difference {ι κ : Type*} [DecidableEq κ]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι)
    (q : κ → O) [∀ i, (Ideal.span {q i}).IsMaximal]
    (hprime : ∀ i, Prime (Ideal.span {q i}))
    (hinj : Function.Injective (fun i => (Ideal.span {q i} : Ideal O)))
    (T G : Finset κ) (hTG : Disjoint T G) (K : ℝ)
    (havoid : ∀ i ∈ G, ∀ j ∈ S, q i ∉ P j) :
    partialSquarefreeSum P hg S q K (T ∪ G) * divisorSum P hg S q G -
      partialSquarefreeSum P hg S q K T *
        (∏ i ∈ G, (1 - (1 : ℂ) / (Ideal.absNorm (Ideal.span {q i}) : ℂ))) =
      ∑ H ∈ T.powerset, ∑ D ∈ G.powerset, ∑ E ∈ G.powerset,
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {q i}) : ℂ) *
        normalizedRow P hg S ((∏ i ∈ H, q i) * (∏ i ∈ D, q i) * ∏ i ∈ E, q i) *
        (cutoffDifference K (∏ i ∈ H, Ideal.span {q i})
          (∏ i ∈ D, Ideal.span {q i}) : ℝ) := by
  have hdensity := actual_double_divisor_cancellation_coprime P hg S q hprime hinj
    G ∅ (by simp) havoid
  simp only [Finset.union_empty, Finset.powerset_empty, Finset.sum_singleton,
    Finset.prod_empty, UniqueFactorizationMonoid.moebius_one, Int.cast_one,
    normalizedRow_one, mul_one] at hdensity
  rw [← hdensity]
  unfold partialSquarefreeSum divisorSum
  rw [sum_powerset_disjoint_union T G hTG]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro H hH
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro D hD
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  have hHD : Disjoint H D := hTG.mono (Finset.mem_powerset.mp hH) (Finset.mem_powerset.mp hD)
  have hc : normCutoff q K (H ∪ D) - normCutoff q K H =
      (cutoffDifference K (∏ i ∈ H, Ideal.span {q i})
        (∏ i ∈ D, Ideal.span {q i}) : ℝ) := by
    simp only [normCutoff, Finset.prod_union hHD, cutoffDifference, Complex.ofReal_sub]
    split_ifs <;> norm_num
  simp only [Finset.prod_union hHD, normalizedRow_mul]
  rw [← hc]
  ring

end QuadraticMainTermDifference

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter
namespace CubicReflectionKernel

def realBeta (a b : ℝ) : ℝ :=
  ∫ x : ℝ in 0..1, x ^ (a - 1) * (1 - x) ^ (b - 1)

theorem realBeta_nonneg (a b : ℝ) : 0 ≤ realBeta a b := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x hx
  exact mul_nonneg (Real.rpow_nonneg hx.1 _) (Real.rpow_nonneg (sub_nonneg.mpr hx.2) _)

theorem betaIntegral_ofReal (a b : ℝ) :
    Complex.betaIntegral (a : ℂ) (b : ℂ) = (realBeta a b : ℂ) := by
  rw [Complex.betaIntegral, realBeta, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  dsimp only
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le,
    Complex.ofReal_cpow (sub_pos.mpr hx.2).le]
  push_cast
  rfl

theorem norm_betaIntegral_le (u v : ℂ) :
    ‖Complex.betaIntegral u v‖ ≤ realBeta u.re v.re := by
  apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)).trans_eq
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
  have hcast : (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr hx.2)]
  simp

theorem realBeta_eq_Gamma (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    realBeta a b = Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  apply Complex.ofReal_injective
  rw [← betaIntegral_ofReal]
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using ha) (by simpa using hb)]
  rw [← Complex.ofReal_add]
  simp only [Complex.Gamma_ofReal, Complex.ofReal_div, Complex.ofReal_mul]

theorem Gamma_ratio_eq_beta (z : ℂ) (d : ℝ) (hz : 0 < z.re) (hd : 0 < d) :
    Complex.Gamma z / Complex.Gamma (z + d) =
      Complex.betaIntegral z d / Complex.Gamma d := by
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hz (by simpa using hd)]
  have hdn : Complex.Gamma (d : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hd)
  field_simp

theorem Gamma_vertical_ratio_bound (a d t : ℝ) (ha : 0 < a) (hd : 0 < d) :
    ‖Complex.Gamma ((a : ℂ) + t * Complex.I) /
      Complex.Gamma ((a : ℂ) + t * Complex.I + d)‖ ≤
      Real.Gamma a / Real.Gamma (a + d) := by
  rw [Gamma_ratio_eq_beta _ d (by simpa using ha) hd, norm_div]
  have hg := Real.Gamma_pos_of_pos hd
  have hb := norm_betaIntegral_le ((a : ℂ) + t * Complex.I) (d : ℂ)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero] at hb
  rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg]
  calc
    _ ≤ realBeta a d / Real.Gamma d := div_le_div_of_nonneg_right hb hg.le
    _ = _ := by rw [realBeta_eq_Gamma a d ha hd]; field_simp

theorem inverse_Gamma_shift (z : ℂ) (n : ℕ) :
    (Complex.Gamma z)⁻¹ =
      (∏ k ∈ Finset.range n, (z + k)) * (Complex.Gamma (z + n))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (z + n),
      Finset.prod_range_succ]
    push_cast
    ring_nf

theorem Gamma_shifted_pair_bound (a σ t : ℝ) (n : ℕ)
    (ha : 0 < a + σ) (hd : 0 < (n : ℝ) - 2 * σ) :
    ‖Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
      Complex.Gamma ((a : ℂ) - (σ + t * Complex.I) + n)‖ ≤
      Real.Gamma (a + σ) / Real.Gamma (a - σ + n) := by
  have hb := Gamma_vertical_ratio_bound (a + σ) ((n : ℝ) - 2 * σ) t ha hd
  have hn : ((a + σ : ℝ) : ℂ) + t * Complex.I =
      (a : ℂ) + (σ + t * Complex.I) := by push_cast; ring
  have hdp : ((a + σ : ℝ) : ℂ) + t * Complex.I + ((n : ℝ) - 2 * σ : ℝ) =
      ((a - σ + n : ℝ) : ℂ) + t * Complex.I := by push_cast; ring
  have hdm : (a : ℂ) - (σ + t * Complex.I) + n =
      ((a - σ + n : ℝ) : ℂ) - t * Complex.I := by push_cast; ring
  have hr : a + σ + ((n : ℝ) - 2 * σ) = a - σ + n := by ring
  rw [hdp, hn, hr] at hb
  rw [hdm, Gamma_vertical_conj, norm_div, norm_star]
  simpa only [norm_div] using hb

theorem gammaMultiplier_left_bound (t : ℝ) :
    ‖gammaMultiplier ((-(1 / 4) : ℝ) + t * Complex.I)‖ ≤
      (Real.Gamma (11 / 12) / Real.Gamma (17 / 12)) *
      (Real.Gamma (7 / 12) / Real.Gamma (13 / 12)) := by
  have h1 := Gamma_shifted_pair_bound (7 / 6) (-(1 / 4)) t 0 (by norm_num) (by norm_num)
  have h2 := Gamma_shifted_pair_bound (5 / 6) (-(1 / 4)) t 0 (by norm_num) (by norm_num)
  norm_num only [Nat.cast_zero, add_zero, show (7 / 6 : ℝ) + -(1 / 4) = 11 / 12 by norm_num,
    show (7 / 6 : ℝ) - -(1 / 4) = 17 / 12 by norm_num,
    show (5 / 6 : ℝ) + -(1 / 4) = 7 / 12 by norm_num,
    show (5 / 6 : ℝ) - -(1 / 4) = 13 / 12 by norm_num] at h1 h2
  have heq : gammaMultiplier ((-(1 / 4) : ℝ) + t * Complex.I) =
      (Complex.Gamma (((7 / 6 : ℝ) : ℂ) + ((-(1 / 4) : ℝ) + t * Complex.I)) /
       Complex.Gamma (((7 / 6 : ℝ) : ℂ) - ((-(1 / 4) : ℝ) + t * Complex.I))) *
      (Complex.Gamma (((5 / 6 : ℝ) : ℂ) + ((-(1 / 4) : ℝ) + t * Complex.I)) /
       Complex.Gamma (((5 / 6 : ℝ) : ℂ) - ((-(1 / 4) : ℝ) + t * Complex.I))) := by
    simp only [gammaMultiplier, Complex.ofReal_div, Complex.ofReal_ofNat]
    exact div_mul_div_comm _ _ _ _ |>.symm
  rw [heq, norm_mul]
  exact mul_le_mul h1 h2 (norm_nonneg _) (div_nonneg
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 11 / 12)).le
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 17 / 12)).le)

theorem norm_Gamma_shift_factor (z : ℂ) (n : ℕ) :
    ‖∏ k ∈ Finset.range n, (z + k)‖ ≤ (‖z‖ + n) ^ n := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _k ∈ Finset.range n, (‖z‖ + n) := by
      apply Finset.prod_le_prod₀
      · intro k hk
        exact norm_nonneg _
      · intro k hk
        have hk' : (k : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hk).le
        exact (norm_add_le _ _).trans (by simpa using add_le_add_left hk' ‖z‖)
    _ = _ := by simp

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

theorem Gamma_pair_strip_bound (a : ℝ) (ha : 1 / 4 < a) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
        Complex.Gamma ((a : ℂ) - (σ + t * Complex.I))‖ ≤
        C * (1 + |t|) ^ (2 * A + 2) := by
  let n : ℕ := 2 * A + 2
  let I : Set ℝ := Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)
  have hapos (σ : ℝ) (hσ : σ ∈ I) : 0 < a + σ := by
    have := hσ.1
    linarith
  have hdpos (σ : ℝ) (hσ : σ ∈ I) : 0 < (n : ℝ) - 2 * σ := by
    have := hσ.2
    dsimp [n]
    push_cast
    linarith
  have hdenpos (σ : ℝ) (hσ : σ ∈ I) : 0 < a - σ + n := by
    have h1 := hapos σ hσ
    have h2 := hdpos σ hσ
    linarith
  have hc1 : ContinuousOn (fun σ : ℝ => Real.Gamma (a + σ)) I :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp
      (continuous_const.add continuous_id).continuousOn hapos
  have hc2 : ContinuousOn (fun σ : ℝ => Real.Gamma (a - σ + n)) I :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp
      ((continuous_const.sub continuous_id).add continuous_const).continuousOn hdenpos
  have hc : ContinuousOn (fun σ : ℝ => Real.Gamma (a + σ) / Real.Gamma (a - σ + n)) I :=
    hc1.div hc2 (fun σ hσ => (Real.Gamma_pos_of_pos (hdenpos σ hσ)).ne')
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc : IsCompact I).bddAbove_image hc
  let C₁ : ℝ := |C₀| + 1
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  have hreal (σ : ℝ) (hσ : σ ∈ I) :
      Real.Gamma (a + σ) / Real.Gamma (a - σ + n) ≤ C₁ := by
    exact (hC₀ (Set.mem_image_of_mem _ hσ)).trans (by dsimp [C₁]; linarith [le_abs_self C₀])
  let B : ℝ := |a| + A + 1 + n + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B ^ n * C₁, mul_pos (pow_pos hB n) hC₁, ?_⟩
  intro σ hσ t
  have hσ' : σ ∈ I := hσ
  have hσabs : |σ| ≤ (A : ℝ) + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hσ.1, hσ.2, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  have hz : ‖(a : ℂ) - (σ + t * Complex.I)‖ ≤ |a| + A + 1 + |t| := by
    calc
      _ ≤ ‖(a : ℂ)‖ + ‖(σ : ℂ) + t * Complex.I‖ := norm_sub_le _ _
      _ ≤ ‖(a : ℂ)‖ + (‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖) :=
        add_le_add le_rfl (norm_add_le _ _)
      _ = |a| + (|σ| + |t|) := by simp
      _ ≤ _ := by linarith
  have hzB : ‖(a : ℂ) - (σ + t * Complex.I)‖ + n ≤ B * (1 + |t|) := by
    dsimp [B]
    nlinarith [abs_nonneg a, abs_nonneg t, (Nat.cast_nonneg A : (0 : ℝ) ≤ A), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hprod : ‖∏ k ∈ Finset.range n, ((a : ℂ) - (σ + t * Complex.I) + k)‖ ≤
      B ^ n * (1 + |t|) ^ n := by
    apply (norm_Gamma_shift_factor _ n).trans
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hzB n
  have hratio := (Gamma_shifted_pair_bound a σ t n (hapos σ hσ') (hdpos σ hσ')).trans
    (hreal σ hσ')
  have heq : Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
      Complex.Gamma ((a : ℂ) - (σ + t * Complex.I)) =
      (∏ k ∈ Finset.range n, ((a : ℂ) - (σ + t * Complex.I) + k)) *
      (Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
       Complex.Gamma ((a : ℂ) - (σ + t * Complex.I) + n)) := by
    rw [div_eq_mul_inv, inverse_Gamma_shift _ n, div_eq_mul_inv]
    ring
  rw [heq, norm_mul]
  calc
    _ ≤ (B ^ n * (1 + |t|) ^ n) * C₁ :=
      mul_le_mul hprod hratio (norm_nonneg _) (by positivity)
    _ = _ := by dsimp [n]; ring

theorem gammaMultiplier_strip_bound (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖gammaMultiplier ((σ : ℂ) + t * Complex.I)‖ ≤
        C * (1 + |t|) ^ (4 * A + 4) := by
  obtain ⟨C₁, hC₁, h1⟩ := Gamma_pair_strip_bound (7 / 6) (by norm_num) A
  obtain ⟨C₂, hC₂, h2⟩ := Gamma_pair_strip_bound (5 / 6) (by norm_num) A
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  intro σ hσ t
  have heq : gammaMultiplier ((σ : ℂ) + t * Complex.I) =
      (Complex.Gamma (((7 / 6 : ℝ) : ℂ) + (σ + t * Complex.I)) /
       Complex.Gamma (((7 / 6 : ℝ) : ℂ) - (σ + t * Complex.I))) *
      (Complex.Gamma (((5 / 6 : ℝ) : ℂ) + (σ + t * Complex.I)) /
       Complex.Gamma (((5 / 6 : ℝ) : ℂ) - (σ + t * Complex.I))) := by
    simp only [gammaMultiplier, Complex.ofReal_div, Complex.ofReal_ofNat]
    exact div_mul_div_comm _ _ _ _ |>.symm
  rw [heq, norm_mul]
  calc
    _ ≤ (C₁ * (1 + |t|) ^ (2 * A + 2)) * (C₂ * (1 + |t|) ^ (2 * A + 2)) :=
      mul_le_mul (h1 σ hσ t) (h2 σ hσ t) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [mul_mul_mul_comm, ← pow_add]
      congr 2
      omega

theorem section_deriv_smooth (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (F p.1) p.2) := by
  have hFp : ContDiff ℝ ∞
      (Function.uncurry (fun p : ℝ × ℝ => F p.1)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hFp.fderiv contDiff_snd (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  simpa only [deriv] using hd.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem section_iteratedDeriv_smooth (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv j (F p.1) p.2) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hF
  | succ j ih =>
    simpa only [iteratedDeriv_succ] using
      section_deriv_smooth (fun σ => iteratedDeriv j (F σ)) ih

theorem tsupport_iteratedDeriv_subset (f : ℝ → ℂ) (j : ℕ) :
    tsupport (iteratedDeriv j f) ⊆ tsupport f := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem compact_family_deriv_integrable (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (σ : ℝ) (j : ℕ) :
    Integrable (iteratedDeriv j (F σ)) := by
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (iteratedDeriv j (F σ)) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    exact (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  exact (hs.continuous_iteratedDeriv j (by simp)).integrable_of_hasCompactSupport hc

theorem compact_family_deriv_L1_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, (∫ u : ℝ, ‖iteratedDeriv j (F σ) u‖) ≤ C := by
  have hc := (section_iteratedDeriv_smooth F hF j).continuous.norm
  obtain ⟨M, hM⟩ := (hJ.prod hK).bddAbove_image hc.continuousOn
  let C : ℝ := (|M| + 1) * (volume.real K + 1)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro σ hσ
  have hbound : ∀ u ∈ K, ‖iteratedDeriv j (F σ) u‖ ≤ |M| + 1 := by
    intro u hu
    exact (hM (Set.mem_image_of_mem _ (show (σ, u) ∈ J ×ˢ K from ⟨hσ, hu⟩))).trans (by linarith [le_abs_self M])
  have hs : Function.support (iteratedDeriv j (F σ)) ⊆ K :=
    (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  have hzero : ∀ u, u ∉ K → ‖iteratedDeriv j (F σ) u‖ = 0 := by
    intro u hu
    have hz : iteratedDeriv j (F σ) u = 0 := by
      by_contra hn
      exact hu (hs hn)
    simp [hz]
  have hi := norm_setIntegral_le_of_norm_le_const («μ» := volume) (f := fun u => ‖iteratedDeriv j (F σ) u‖)
    hK.measure_lt_top (C := |M| + 1) (fun u hu => by simpa using hbound u hu)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero] at hi
  rw [Real.norm_of_nonneg (integral_nonneg (fun u => norm_nonneg _))] at hi
  exact hi.trans (by dsimp [C]; nlinarith [abs_nonneg M])

theorem compact_family_fourier_power_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      |w| ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_family_deriv_L1_bound F hF K hK hsupp J hJ j
  refine ⟨C / (2 * Real.pi) ^ j, by positivity, ?_⟩
  intro σ hσ w
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hfour := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hs
    (fun k _ => compact_family_deriv_integrable F hF K hK hsupp σ k)
    (by simp : (j : ℕ∞) ≤ ⊤)
  have hid : (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) =
      ‖𝓕 (iteratedDeriv j (F σ)) w‖ := by
    rw [hfour]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  have hn : ‖𝓕 (iteratedDeriv j (F σ)) w‖ ≤ C := by
    apply (VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (iteratedDeriv j (F σ)) w).trans
    exact hb σ hσ
  apply (le_div_iff₀ (by positivity : 0 < (2 * Real.pi) ^ j)).mpr
  rw [← hid] at hn
  calc
    _ = (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := mul_comm _ _
    _ ≤ C := hn

theorem compact_family_fourier_weighted_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      (1 + |w|) ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C₀, hC₀, h0⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ 0
  obtain ⟨Cj, hCj, hj⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ j
  refine ⟨2 ^ j * (C₀ + Cj), by positivity, ?_⟩
  intro σ hσ w
  have hbase : ‖𝓕 (F σ) w‖ ≤ C₀ := by simpa using h0 σ hσ w
  by_cases hw : |w| ≤ 1
  · calc
      _ ≤ 2 ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ ≤ 2 ^ j * C₀ := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hw' : 1 ≤ |w| := le_of_lt (lt_of_not_ge hw)
    calc
      _ ≤ (2 * |w|) ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ = 2 ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := by rw [mul_pow, mul_assoc]
      _ ≤ 2 ^ j * Cj := mul_le_mul_of_nonneg_left (hj σ hσ w) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

def mellinLogFamily (V : ℝ → ℂ) (σ u : ℝ) : ℂ :=
  Real.exp (-σ * u) • V (Real.exp (-u))

theorem mellinLogFamily_smooth (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (Function.uncurry (mellinLogFamily V)) := by
  change ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.exp (-p.1 * p.2) • V (Real.exp (-p.2)))
  exact (Real.contDiff_exp.comp (contDiff_fst.neg.mul contDiff_snd)).smul
    (hV.comp (Real.contDiff_exp.comp contDiff_snd.neg))

theorem mellinLogFamily_support (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (σ : ℝ) :
    Function.support (mellinLogFamily V σ) ⊆ Set.Icc (-Real.log b) (-Real.log a) := by
  intro u hu
  have hv : V (Real.exp (-u)) ≠ 0 := by
    intro hv
    exact hu (by simp [mellinLogFamily, hv])
  have hm := hsupp hv
  have hlow := Real.log_le_log ha hm.1
  have hhigh := Real.log_le_log (Real.exp_pos (-u)) hm.2
  simp only [Real.log_exp] at hlow hhigh
  constructor <;> linarith

theorem mellin_eq_logFamily_fourier (V : ℝ → ℂ) (σ t : ℝ) :
    mellin V ((σ : ℂ) + t * Complex.I) = 𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, mul_zero,  sub_zero, add_zero, Complex.add_im,
    Complex.mul_im, Complex.I_im, mul_one, zero_add]
  rfl

theorem compact_source_mellin_strip_decay (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (lo hi : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc lo hi, ∀ t : ℝ,
      (1 + |t|) ^ j * ‖mellin V ((σ : ℂ) + t * Complex.I)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_family_fourier_weighted_bound
    (mellinLogFamily V) (mellinLogFamily_smooth V hV)
    (Set.Icc (-Real.log b) (-Real.log a)) isCompact_Icc
    (mellinLogFamily_support V a b ha hsupp) (Set.Icc lo hi) isCompact_Icc j
  refine ⟨(1 + 2 * Real.pi) ^ j * C, by positivity, ?_⟩
  intro σ hσ t
  rw [mellin_eq_logFamily_fourier]
  have ht : |t| = (2 * Real.pi) * |t / (2 * Real.pi)| := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    field_simp
  have hbase : 1 + |t| ≤ (1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos, abs_nonneg (t / (2 * Real.pi))]
  calc
    _ ≤ ((1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|)) ^ j *
        ‖𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase j) (norm_nonneg _)
    _ = (1 + 2 * Real.pi) ^ j * ((1 + |t / (2 * Real.pi)|) ^ j *
        ‖𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi))‖) := by rw [mul_pow, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb σ hσ _) (by positivity)

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

def mellinData (V : ℝ → ℂ) (s : ℂ) : ℂ := mellin V (-s) * gammaMultiplier s

def mellinEulerData (V : ℝ → ℂ) (j : ℕ) (s : ℂ) : ℂ := (-s) ^ j * mellinData V s

theorem mellinData_strip_decay (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      (1 + |t|) ^ j * ‖mellinData V ((σ : ℂ) + t * Complex.I)‖ ≤ C := by
  let g : ℕ := 4 * A + 4
  obtain ⟨Cγ, hCγ, hγ⟩ := gammaMultiplier_strip_bound A
  obtain ⟨CV, hCV, hVb⟩ := compact_source_mellin_strip_decay V a b ha hsupp hV
    (-(A : ℝ)) (1 / 4) (g + j)
  refine ⟨Cγ * CV, mul_pos hCγ hCV, ?_⟩
  intro σ hσ t
  have hσ' : -σ ∈ Set.Icc (-(A : ℝ)) (1 / 4) := by constructor <;> linarith [hσ.1, hσ.2]
  have hmb := hVb (-σ) hσ' (-t)
  have heq : (-σ : ℝ) + (-t : ℝ) * Complex.I = -((σ : ℂ) + t * Complex.I) := by
    push_cast
    ring
  rw [heq, abs_neg] at hmb
  have hgb : ‖gammaMultiplier ((σ : ℂ) + t * Complex.I)‖ ≤ Cγ * (1 + |t|) ^ g := hγ σ hσ t
  rw [mellinData, norm_mul]
  calc
    _ = ((1 + |t|) ^ j * ‖mellin V (-((σ : ℂ) + t * Complex.I))‖) *
        ‖gammaMultiplier ((σ : ℂ) + t * Complex.I)‖ := by ring
    _ ≤ ((1 + |t|) ^ j * ‖mellin V (-((σ : ℂ) + t * Complex.I))‖) *
        (Cγ * (1 + |t|) ^ g) := mul_le_mul_of_nonneg_left hgb (by positivity)
    _ = Cγ * ((1 + |t|) ^ (g + j) * ‖mellin V (-((σ : ℂ) + t * Complex.I))‖) := by
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmb hCγ.le

theorem weighted_two_to_cauchy {C B : ℝ} (hB : 0 ≤ B) (t : ℝ)
    (h : (1 + |t|) ^ 2 * B ≤ C) : B ≤ C / (1 + t ^ 2) := by
  apply (le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).mpr
  have hpow : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
  exact (mul_le_mul_of_nonneg_left hpow hB).trans (by simpa only [mul_comm] using h)

theorem mellinEulerData_strip_bound (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖mellinEulerData V j ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨C, hC, hb⟩ := mellinData_strip_decay V a b ha hsupp hV A (j + 2)
  refine ⟨((A : ℝ) + 2) ^ j * C, by positivity, ?_⟩
  intro σ hσ t
  apply weighted_two_to_cauchy (norm_nonneg _) t
  have hσabs : |σ| ≤ (A : ℝ) + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hσ.1, hσ.2, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  have hz : ‖(σ : ℂ) + t * Complex.I‖ ≤ ((A : ℝ) + 2) * (1 + |t|) := by
    have hnorm := norm_add_le (σ : ℂ) ((t : ℂ) * Complex.I)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] at hnorm
    nlinarith [abs_nonneg t, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  rw [mellinEulerData, norm_mul, norm_pow, norm_neg]
  calc
    _ ≤ (1 + |t|) ^ 2 * ((((A : ℝ) + 2) * (1 + |t|)) ^ j *
        ‖mellinData V ((σ : ℂ) + t * Complex.I)‖) := by
      gcongr
    _ = ((A : ℝ) + 2) ^ j * ((1 + |t|) ^ (j + 2) *
        ‖mellinData V ((σ : ℂ) + t * Complex.I)‖) := by rw [mul_pow, pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb σ hσ t) (by positivity)

theorem mellinEulerData_differentiableAt (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (j : ℕ) (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (mellinEulerData V j) s :=
  (differentiableAt_id.neg.pow j).mul
    (kernelMellinIntegrand_differentiableAt V a b ha hsupp hV s hs)

theorem mellinEulerData_vertical_integrable (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)) :
    Integrable (fun t : ℝ => mellinEulerData V j ((σ : ℂ) + t * Complex.I)) := by
  obtain ⟨C, hC, hb⟩ := mellinEulerData_strip_bound V a b ha hsupp hV A j
  have hc : Continuous (fun t : ℝ => mellinEulerData V j ((σ : ℂ) + t * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (mellinEulerData_differentiableAt V a b ha hsupp hV j _ ?_).continuousAt.comp
    · fun_prop
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
      linarith [hσ.1]
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by simpa only [div_eq_mul_inv] using hb σ hσ t)

end CubicReflectionKernel

end

end OAI
end OAIOriginalModule0102

/-! Original module: OAI.NumberTheory.DirichletL.Mellin.InverseContour
Source SHA256: 77a34ef6a916727383393a046051fe1f1424a5583344a883f6a6bbf9da283d44
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0103


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
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set

def inverseMellinIntegrand (V : ℝ → ℂ) (j : ℕ) (y : ℝ) (s : ℂ) : ℂ :=
  (y : ℂ) ^ (-s) * mellinEulerData V j s

theorem inverseMellinIntegrand_differentiableAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (j : ℕ) (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (inverseMellinIntegrand V j y) s := by
  exact (differentiableAt_id.neg.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).mul
    (mellinEulerData_differentiableAt V a b ha hsupp hV j s hs)

theorem inverseMellinIntegrand_vertical_integrable
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ))
    (y : ℝ) (hy : 0 < y) :
    Integrable (fun t : ℝ => inverseMellinIntegrand V j y ((σ : ℂ) + t * Complex.I)) := by
  apply (mellinEulerData_vertical_integrable V a b ha hsupp hV A j σ hσ).bdd_mul
    (c := y ^ (-σ))
  · exact ((show Continuous (fun t : ℝ => -((σ : ℂ) + t * Complex.I)) by fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp

theorem inverseMellinIntegrand_strip_bound
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (y : ℝ) (hy : 0 < y) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖inverseMellinIntegrand V j y ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨C, hC, hb⟩ := mellinEulerData_strip_bound V a b ha hsupp hV A j
  have hc : Continuous (fun σ : ℝ => y ^ (-σ)) :=
    (Real.continuous_const_rpow hy.ne').comp continuous_neg
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Set.Icc (-(1 / 4 : ℝ)) (A : ℝ))).bddAbove_image hc.continuousOn
  refine ⟨(|B| + 1) * C, by positivity, ?_⟩
  intro σ hσ t
  have hby : y ^ (-σ) ≤ |B| + 1 :=
    (hB (Set.mem_image_of_mem _ hσ)).trans (by linarith [le_abs_self B])
  rw [inverseMellinIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
  calc
    _ ≤ (|B| + 1) * (C / (1 + t ^ 2)) :=
      mul_le_mul hby (hb σ hσ t) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem mellinInv_euler_shift
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ))
    (y : ℝ) (hy : 0 < y) :
    mellinInv 0 (mellinEulerData V j) y = mellinInv σ (mellinEulerData V j) y := by
  obtain ⟨C, hC, hb⟩ := inverseMellinIntegrand_strip_bound V a b ha hsupp hV A j y hy
  have h0 : (0 : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ) := by
    constructor
    · norm_num
    · exact Nat.cast_nonneg A
  have hshift (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)) :
      (∫ t : ℝ, inverseMellinIntegrand V j y ((-(1 / 4) : ℝ) + t * Complex.I)) =
      ∫ t : ℝ, inverseMellinIntegrand V j y ((ρ : ℂ) + t * Complex.I) := by
    apply VerticalContourShift.integral_eq_of_strip_decay
      (inverseMellinIntegrand V j y) (-(1 / 4)) ρ C hρ.1
    · intro z hzlo hzhi
      apply inverseMellinIntegrand_differentiableAt V a b ha hsupp hV j y hy z
      linarith
    · apply inverseMellinIntegrand_vertical_integrable V a b ha hsupp hV A j
        (-(1 / 4)) ⟨le_rfl, hρ.1.trans hρ.2⟩ y hy
    · exact inverseMellinIntegrand_vertical_integrable V a b ha hsupp hV A j ρ hρ y hy
    · intro r hr t
      exact hb r ⟨hr.1, hr.2.trans hρ.2⟩ t
  have heq := (hshift 0 h0).symm.trans (hshift σ hσ)
  simpa only [mellinInv, smul_eq_mul, inverseMellinIntegrand] using
    congrArg (fun z : ℂ => (1 / (2 * Real.pi) : ℝ) • z) heq

theorem mellinInv_euler_line_bound
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ),
      ∀ y : ℝ, 0 < y → ‖mellinInv σ (mellinEulerData V j) y‖ ≤ C * y ^ (-σ) := by
  obtain ⟨C, hC, hb⟩ := mellinEulerData_strip_bound V a b ha hsupp hV A j
  refine ⟨C / 2, by positivity, ?_⟩
  intro σ hσ y hy
  have hint : ‖∫ t : ℝ, (y : ℂ) ^ (-((σ : ℂ) + t * Complex.I)) *
        mellinEulerData V j ((σ : ℂ) + t * Complex.I)‖ ≤
      (y ^ (-σ) * C) * Real.pi := by
    calc
      _ ≤ ∫ t : ℝ, (y ^ (-σ) * C) * (1 + t ^ 2)⁻¹ := by
        apply norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _)
        filter_upwards [] with t
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
        simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
        simpa only [div_eq_mul_inv, mul_assoc] using
          mul_le_mul_of_nonneg_left (hb σ hσ t) (Real.rpow_nonneg hy.le (-σ))
      _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  rw [mellinInv, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  simp only [smul_eq_mul]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ((y ^ (-σ) * C) * Real.pi) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by field_simp

def paperEulerKernel (V : ℝ → ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  mellinInv 0 (mellinEulerData V j) (paperScale * x)

theorem mellinEulerData_axis (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hlog : ∀ u, logSource u = V (Real.exp u)) (j : ℕ) (u : ℝ) :
    mellinEulerData V j (2 * Real.pi * u * Complex.I) =
      (-2 * Real.pi * Complex.I * u) ^ j * spectralProfile logSource u := by
  have hu : (2 * Real.pi * u * Complex.I : ℂ) =
      ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [mellinEulerData, mellinData, hu, mellin_axis_eq_fourier V logSource hlog]
  have hb : -(((2 * Real.pi * u : ℝ) : ℂ) * Complex.I) =
      -2 * Real.pi * Complex.I * u := by push_cast; ring
  rw [hb, spectralProfile, axisMultiplier]
  ring

theorem paperEulerKernel_eq_euler (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hlog : ∀ u, logSource u = V (Real.exp u)) (j : ℕ) (x : ℝ) (hx : 0 < x) :
    paperEulerKernel V j x = LocalLogFourier.eulerDeriv (paperKernel V) j x := by
  rw [paperKernel_euler_eq V logSource hlog j x hx, reflectedLogProfile_deriv]
  unfold paperEulerKernel
  rw [mellinInv_eq_fourierInv 0 _ (mul_pos paperScale_pos hx)]
  simp only [Complex.ofReal_zero, neg_zero, Complex.cpow_zero, one_smul,
    Real.fourierInv_eq_fourier_neg, neg_neg, zero_add]
  have hfun : (fun u : ℝ => mellinEulerData V j (2 * Real.pi * u * Complex.I)) =
      (fun u : ℝ => (-2 * Real.pi * Complex.I * u) ^ j * spectralProfile logSource u) := by
    funext u
    exact mellinEulerData_axis V logSource hlog j u
  rw [hfun]

theorem paperKernel_euler_decay_at_line
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x →
      ‖LocalLogFourier.eulerDeriv (paperKernel V) j x‖ ≤ C * x ^ (-σ) := by
  obtain ⟨C, hC, hb⟩ := mellinInv_euler_line_bound V a b ha hsupp hV A j
  refine ⟨C * paperScale ^ (-σ), mul_pos hC (Real.rpow_pos_of_pos paperScale_pos _), ?_⟩
  intro x hx
  rw [← paperEulerKernel_eq_euler V (logSchwartz V a b ha hsupp hV) (by intro u; rfl) j x hx]
  unfold paperEulerKernel
  rw [mellinInv_euler_shift V a b ha hsupp hV A j σ hσ _ (mul_pos paperScale_pos hx)]
  have hbound := hb σ hσ (paperScale * x) (mul_pos paperScale_pos hx)
  rw [Real.mul_rpow paperScale_pos.le hx.le] at hbound
  simpa only [mul_assoc] using hbound

theorem paperKernel_euler_power_decay
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x →
      (‖LocalLogFourier.eulerDeriv (paperKernel V) j x‖ ≤ C * x ^ (1 / 4 : ℝ)) ∧
      (‖LocalLogFourier.eulerDeriv (paperKernel V) j x‖ ≤ C * x ^ (-(A : ℝ))) := by
  have hleft : -(1 / 4 : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ) := by
    constructor
    · rfl
    · linarith [show (0 : ℝ) ≤ A from Nat.cast_nonneg A]
  have hright : (A : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ) := by
    constructor
    · linarith [show (0 : ℝ) ≤ A from Nat.cast_nonneg A]
    · rfl
  obtain ⟨CL, hCL, hL⟩ := paperKernel_euler_decay_at_line V a b ha hsupp hV A j _ hleft
  obtain ⟨CR, hCR, hR⟩ := paperKernel_euler_decay_at_line V a b ha hsupp hV A j _ hright
  refine ⟨max CL CR, lt_of_lt_of_le hCL (le_max_left _ _), ?_⟩
  intro x hx
  constructor
  · have hh : ‖LocalLogFourier.eulerDeriv (paperKernel V) j x‖ ≤ CL * x ^ (1 / 4 : ℝ) := by
      simpa only [neg_neg] using hL x hx
    exact hh.trans
      (mul_le_mul_of_nonneg_right (le_max_left CL CR) (Real.rpow_nonneg hx.le _))
  · exact (hR x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_right CL CR) (Real.rpow_nonneg hx.le _))

theorem paperKernel_euler_uniform_weighted_bound
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i ≤ K, ∀ x : ℝ, 0 < x →
      (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperKernel V) i x‖ ≤ C := by
  choose c hc hb using fun i : Fin (K + 1) =>
    paperKernel_euler_power_decay V a b ha hsupp hV A i.val
  let D : ℝ := (∑ i : Fin (K + 1), c i) + 1
  have hD : 0 < D := by
    have hs : (0 : ℝ) ≤ ∑ i : Fin (K + 1), c i := Finset.sum_nonneg (fun i _ => (hc i).le)
    dsimp [D]
    linarith
  have hci (i : Fin (K + 1)) : c i ≤ D := by
    have hs : c i ≤ ∑ k : Fin (K + 1), c k :=
      Finset.single_le_sum (fun k _ => (hc k).le) (Finset.mem_univ i)
    dsimp [D]
    linarith
  have hsmall : ∀ i ≤ K, ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖LocalLogFourier.eulerDeriv (paperKernel V) i x‖ ≤ D := by
    intro i hi x hx hx1
    let k : Fin (K + 1) := ⟨i, by omega⟩
    have hp : x ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hx.le hx1 (by norm_num)
    calc
      _ ≤ c k * x ^ (1 / 4 : ℝ) := (hb k x hx).1
      _ ≤ c k := by simpa using mul_le_mul_of_nonneg_left hp (hc k).le
      _ ≤ D := hci k
  have hlarge : ∀ i ≤ K, ∀ x : ℝ, 1 ≤ x →
      x ^ A * ‖LocalLogFourier.eulerDeriv (paperKernel V) i x‖ ≤ D := by
    intro i hi x hx1
    have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    let k : Fin (K + 1) := ⟨i, by omega⟩
    have hxpow : x ^ A ≠ 0 := pow_ne_zero A hx.ne'
    calc
      _ ≤ x ^ A * (c k * x ^ (-(A : ℝ))) :=
        mul_le_mul_of_nonneg_left (hb k x hx).2 (pow_nonneg hx.le A)
      _ = c k := by
        rw [Real.rpow_neg hx.le, Real.rpow_natCast]
        field_simp
      _ ≤ D := hci k
  refine ⟨2 ^ A * (D + D), by positivity, ?_⟩
  intro i hi x hx
  exact LocalLogFourier.euler_two_regime_bound (paperKernel V) A K D D hD.le hD.le
    hsmall hlarge i hi x hx

end CubicReflectionKernel

namespace DescentFiberCost
open scoped BigOperators Classical
open ConcretePrimeRowBridge

abbrev O := ActualEisensteinCubic.O

theorem finite_ideal_count_real (s : Finset (Ideal O)) (H : ℝ) (hH : 1 ≤ H)
    (hpos : ∀ I ∈ s, I ≠ ⊥) (hN : ∀ I ∈ s, (Ideal.absNorm I : ℝ) ≤ H) :
    (s.card : ℝ) ≤ 128 * H := by
  have hs : s ⊆ idealsUpTo ⌊H⌋₊ := by
    intro I hI
    apply mem_idealsUpTo.mpr
    refine ⟨?_, Nat.le_floor (hN I hI)⟩
    exact Nat.one_le_iff_ne_zero.mpr (fun h => hpos I hI (Ideal.absNorm_eq_zero_iff.mp h))
  have hc := (Finset.card_le_card hs).trans (CompactScaleBridge.idealsUpTo_card_le ⌊H⌋₊)
  have hfloor : (⌊H⌋₊ : ℝ) ≤ H := Nat.floor_le (by linarith)
  have hr : (s.card : ℝ) ≤ 64 * ((⌊H⌋₊ : ℝ) + 1) := by exact_mod_cast hc
  linarith

theorem fixed_triple_count
    (s : Finset (Ideal O × Ideal O × Ideal O)) (B T W : ℝ)
    (hB : 1 ≤ B) (hT : 1 ≤ T) (hW : 1 ≤ W)
    (hpos : ∀ x ∈ s, x.1 ≠ ⊥ ∧ x.2.1 ≠ ⊥ ∧ x.2.2 ≠ ⊥)
    (hN : ∀ x ∈ s, (Ideal.absNorm x.1 : ℝ) ≤ B ∧
      (Ideal.absNorm x.2.1 : ℝ) ≤ T ∧ (Ideal.absNorm x.2.2 : ℝ) ≤ W) :
    (s.card : ℝ) ≤ 128 ^ 3 * B * T * W := by
  let a := s.image Prod.fst
  let b := s.image (fun x => x.2.1)
  let c := s.image (fun x => x.2.2)
  have hsub : s ⊆ a ×ˢ (b ×ˢ c) := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩,
        Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩⟩
  have ha : (a.card : ℝ) ≤ 128 * B := by
    apply finite_ideal_count_real a B hB
    · intro I hI
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hI
      exact (hpos x hx).1
    · intro I hI
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hI
      exact (hN x hx).1
  have hb : (b.card : ℝ) ≤ 128 * T := by
    apply finite_ideal_count_real b T hT
    · intro I hI
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hI
      exact (hpos x hx).2.1
    · intro I hI
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hI
      exact (hN x hx).2.1
  have hc : (c.card : ℝ) ≤ 128 * W := by
    apply finite_ideal_count_real c W hW
    · intro I hI
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hI
      exact (hpos x hx).2.2
    · intro I hI
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hI
      exact (hN x hx).2.2
  have hs : (s.card : ℝ) ≤ (a.card : ℝ) * ((b.card : ℝ) * c.card) := by
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_product] at hcard
    exact_mod_cast hcard
  apply hs.trans
  calc
    _ ≤ (128 * B) * ((128 * T) * (128 * W)) := by gcongr
    _ = _ := by ring

theorem complete_second_prefactor
    (K ell B F A C d J g e v t w c : ℝ)
    (hK : K ≠ 0) (hell : ell ≠ 0) (hB : B ≠ 0) (hF : F ≠ 0)
    (hC : C ≠ 0) (hd : d ≠ 0) (hJ : J ≠ 0)
    (hg : g ≠ 0) (he : e ≠ 0) (hv : v ≠ 0) (hc : c ≠ 0)
    (Li : ℝ) (hLi : Li ≠ 0) :
    (K * A * C / (d * ell ^ 2 * B ^ 2 * F * c)) *
      ((ell ^ 2 * B ^ 4 * F ^ 2 * d / (K * C ^ 2 * J)) * g / (e * Li)) *
      ((B * c / J) * t * w) *
      ((Li / (g * v)) * (J * C * e * v)) =
      (B * F * A * t * w) * B ^ 2 / J := by
  field_simp

theorem complete_second_zero_prefactor
    (K ell B F A C d J t c : ℝ)
    (hK : K ≠ 0) (hell : ell ≠ 0) (hB : B ≠ 0) (hF : F ≠ 0)
    (hA : A ≠ 0) (hC : C ≠ 0) (hd : d ≠ 0) (hJ : J ≠ 0)
    (ht : t ≠ 0) (hc : c ≠ 0) :
    (K * A * C / (d * ell ^ 2 * B ^ 2 * F * c)) *
      ((ell ^ 2 * B ^ 4 * F ^ 2 * d / (K * C ^ 2 * J)) * (ell / (A * C * t))) *
      (C * t) * (B * c) = (ell * B ^ 3) * F / (C * J) := by
  field_simp

end DescentFiberCost

namespace EisensteinSchwartzPoisson
open MeasureTheory Set
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem fourier_real_line_integrable (f : 𝓢(ℂ, ℂ)) :
    Integrable (fun x : ℝ => 𝓕 (f : ℂ → ℂ) (x : ℂ)) := by
  have h : Integrable (fun x : ℝ => horizontalSlice (𝓕 f) 0 x) :=
    (horizontalSlice (𝓕 f) 0).integrable
  simpa only [horizontalSlice_apply, complexPoint_eq, mul_zero, add_zero,
    Complex.ofReal_zero, SchwartzMap.fourier_coe] using h

theorem fourier_real_line_integral (f : 𝓢(ℂ, ℂ)) :
    (∫ x : ℝ, 𝓕 (f : ℂ → ℂ) (x : ℂ)) =
      ∫ y : ℝ, f (Complex.I * (y : ℂ)) := by
  let g : ℝ → ℂ := partialFourier f 0
  have hF : 𝓕 g = fun x : ℝ => 𝓕 (f : ℂ → ℂ) (x : ℂ) := by
    funext x
    simpa only [g, complexPoint_eq, Complex.ofReal_zero, mul_zero, add_zero] using fourier_partialFourier f x 0
  have hgi : Integrable (𝓕 g) := by rw [hF]; exact fourier_real_line_integrable f
  have hinv : 𝓕⁻ (𝓕 g) (0 : ℝ) = g 0 :=
    (partialFourier_integrable f 0).fourierInv_fourier_eq hgi
      (partialFourier_continuous f 0).continuousAt
  calc
    _ = ∫ x : ℝ, 𝓕 g x := by rw [hF]
    _ = 𝓕⁻ (𝓕 g) 0 := by simp [Real.fourierInv_eq]
    _ = g 0 := hinv
    _ = _ := by simp [g, partialFourier_eq_integral, complexPoint_eq]

theorem paperFrequency_imaginary (x : ℝ) :
    paperFrequency ((x : ℂ) * Complex.I) = (((2 / Real.sqrt 3) * x : ℝ) : ℂ) := by
  simp [paperFrequency]
  ring_nf
  simp

theorem paperRadialFourier_square (W : ℝ → ℂ) (x : ℝ) :
    paperRadialFourier W (x ^ 2) =
      (2 / Real.sqrt 3 : ℝ) • 𝓕 (fun z : ℂ => W (‖z‖ ^ 2))
        ((((2 / Real.sqrt 3) * x : ℝ) : ℂ)) := by
  have h := paperFourier_radial W ((x : ℂ) * Complex.I)
  have hn : ‖(x : ℂ) * Complex.I‖ ^ 2 = x ^ 2 := by
    simp [ Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hn, paperFourier_eq_standard, paperFrequency_imaginary] at h
  exact h.symm

theorem radial_square_integrable (W : 𝓢(ℝ, ℂ)) :
    Integrable (fun x : ℝ => W (x ^ 2)) := by
  have h : Integrable (fun x : ℝ => horizontalSlice (radialTest W) 0 x) :=
    (horizontalSlice (radialTest W) 0).integrable
  simpa [horizontalSlice_apply, complexPoint_eq, radialTest_apply,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

theorem paperRadialFourier_square_integrable (W : 𝓢(ℝ, ℂ)) :
    Integrable (fun x : ℝ => paperRadialFourier W (x ^ 2)) := by
  have he : (radialTest W : ℂ → ℂ) = fun z : ℂ => W (‖z‖ ^ 2) := rfl
  have hc : (2 / Real.sqrt 3 : ℝ) ≠ 0 := by positivity
  have h := ((fourier_real_line_integrable (radialTest W)).comp_mul_left' hc).smul
    (2 / Real.sqrt 3 : ℝ)
  change Integrable (fun x : ℝ => (2 / Real.sqrt 3 : ℝ) •
    𝓕 (radialTest W : ℂ → ℂ) ((((2 / Real.sqrt 3) * x : ℝ) : ℂ))) at h
  simpa only [paperRadialFourier_square, he] using h

theorem paperRadialFourier_square_integral (W : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ, paperRadialFourier W (x ^ 2)) = ∫ x : ℝ, W (x ^ 2) := by
  have hc : (0 : ℝ) < 2 / Real.sqrt 3 := by positivity
  have he : (radialTest W : ℂ → ℂ) = fun z : ℂ => W (‖z‖ ^ 2) := rfl
  calc
    _ = (2 / Real.sqrt 3 : ℝ) •
        ∫ x : ℝ, 𝓕 (radialTest W : ℂ → ℂ) ((((2 / Real.sqrt 3) * x : ℝ) : ℂ)) := by
      simp only [paperRadialFourier_square, he, integral_smul]
    _ = ∫ x : ℝ, 𝓕 (radialTest W : ℂ → ℂ) (x : ℂ) := by
      rw [Measure.integral_comp_mul_left
        (fun x : ℝ => 𝓕 (radialTest W : ℂ → ℂ) (x : ℂ)) (2 / Real.sqrt 3)]
      rw [abs_of_pos (inv_pos.mpr hc), smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    _ = ∫ y : ℝ, radialTest W (Complex.I * (y : ℂ)) := fourier_real_line_integral _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp [radialTest_apply,  Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem integral_even_eq_twice_Ioi (F : ℝ → ℂ) (hF : Integrable F)
    (heven : ∀ x : ℝ, F (-x) = F x) :
    (∫ x : ℝ, F x) = 2 * ∫ x : ℝ in Ioi 0, F x := by
  have hneg : (∫ x : ℝ in Iic 0, F x) = ∫ x : ℝ in Ioi 0, F x := by
    calc
      _ = ∫ x : ℝ in Ioi 0, F (-x) := by simp
      _ = _ := setIntegral_congr_fun measurableSet_Ioi (fun x _ => heven x)
  rw [← integral_add_compl (s := Ioi 0) measurableSet_Ioi hF, compl_Ioi, hneg]
  ring

theorem paperRadialFourier_halfline_integral (W : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ in Ioi 0, paperRadialFourier W (x ^ 2)) =
      ∫ x : ℝ in Ioi 0, W (x ^ 2) := by
  have h := paperRadialFourier_square_integral W
  rw [integral_even_eq_twice_Ioi _ (paperRadialFourier_square_integrable W)
    (by intro x; simp), integral_even_eq_twice_Ioi _ (radial_square_integrable W)
    (by intro x; simp)] at h
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h

end EisensteinSchwartzPoisson

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

def logRadius (a b : ℝ) : ℝ := |Real.log a| + |Real.log b| + 1

theorem logRadius_pos (a b : ℝ) : 0 < logRadius a b := by unfold logRadius; positivity

def logCutoff (a b : ℝ) : ContDiffBump (0 : ℝ) where
  rIn := logRadius a b
  rOut := logRadius a b + 1
  rIn_pos := logRadius_pos a b
  rIn_lt_rOut := by linarith

def logOuterCutoff (a b : ℝ) : ContDiffBump (0 : ℝ) where
  rIn := logRadius a b + 1
  rOut := logRadius a b + 2
  rIn_pos := by have := logRadius_pos a b; linarith
  rIn_lt_rOut := by linarith

def expCorrection (a b u : ℝ) : ℝ := logOuterCutoff a b u * (Real.exp u - u)
def patchedExp (a b u : ℝ) : ℝ := u + expCorrection a b u

theorem expCorrection_compact (a b : ℝ) : HasCompactSupport (expCorrection a b) :=
  (logOuterCutoff a b).hasCompactSupport.mul_right

theorem expCorrection_smooth (a b : ℝ) : ContDiff ℝ ∞ (expCorrection a b) :=
  (logOuterCutoff a b).contDiff.mul (Real.contDiff_exp.sub contDiff_id)

theorem patchedExp_temperate (a b : ℝ) : Function.HasTemperateGrowth (patchedExp a b) :=
  Function.HasTemperateGrowth.id'.add ((expCorrection_compact a b).hasTemperateGrowth
    (expCorrection_smooth a b))

theorem patchedExp_proper (a b : ℝ) :
    ∃ (k : ℕ) (C : ℝ), ∀ u : ℝ, ‖u‖ ≤ C * (1 + ‖patchedExp a b u‖) ^ k := by
  obtain ⟨u₀, hu₀⟩ := (expCorrection_smooth a b).continuous.norm.exists_forall_ge_of_hasCompactSupport
    (expCorrection_compact a b).norm
  refine ⟨1, ‖expCorrection a b u₀‖ + 1, ?_⟩
  intro u
  have htriangle : ‖u‖ ≤ ‖patchedExp a b u‖ + ‖expCorrection a b u‖ := by
    simpa only [patchedExp, add_sub_cancel_right] using
      norm_sub_le (patchedExp a b u) (expCorrection a b u)
  have hbound := hu₀ u
  simp only [pow_one]
  nlinarith [norm_nonneg (patchedExp a b u), norm_nonneg (expCorrection a b u₀)]

def logPullbackCLM (a b : ℝ) : SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.smulLeftCLM ℂ (logCutoff a b)).comp
    (SchwartzMap.compCLM ℝ (patchedExp_temperate a b) (patchedExp_proper a b))

theorem logPullbackCLM_apply (a b : ℝ) (W : SchwartzMap ℝ ℂ) (u : ℝ) :
    logPullbackCLM a b W u = logCutoff a b u • W (patchedExp a b u) := by
  rw [logPullbackCLM, ContinuousLinearMap.comp_apply, SchwartzMap.smulLeftCLM_apply_apply
    ((logCutoff a b).hasCompactSupport.hasTemperateGrowth (logCutoff a b).contDiff)]
  rfl

theorem logCutoff_eq_one_of_source (a b : ℝ) (ha : 0 < a) (u : ℝ)
    (hu : Real.exp u ∈ Set.Icc a b) : logCutoff a b u = 1 := by
  apply (logCutoff a b).one_of_mem_closedBall
  have hl := Real.log_le_log ha hu.1
  have hr := Real.log_le_log (Real.exp_pos u) hu.2
  simp only [Real.log_exp] at hl hr
  change dist u 0 ≤ logRadius a b
  rw [Real.dist_eq, sub_zero]
  apply abs_le.mpr
  constructor <;> dsimp [logRadius] <;>
    linarith [neg_abs_le (Real.log a), le_abs_self (Real.log b), abs_nonneg (Real.log a), abs_nonneg (Real.log b)]

theorem patchedExp_eq_exp_of_cutoff_ne_zero (a b u : ℝ) (hu : logCutoff a b u ≠ 0) :
    patchedExp a b u = Real.exp u := by
  have hmem : u ∈ Function.support (logCutoff a b) := hu
  rw [(logCutoff a b).support_eq] at hmem
  have heta : logOuterCutoff a b u = 1 := by
    apply (logOuterCutoff a b).one_of_mem_closedBall
    change dist u 0 ≤ logRadius a b + 1
    change dist u 0 < logRadius a b + 1 at hmem
    exact le_of_lt hmem
  simp [patchedExp, expCorrection, heta]

theorem logPullbackCLM_eq_actual (a b : ℝ) (ha : 0 < a) (W : SchwartzMap ℝ ℂ)
    (hsupp : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) (u : ℝ) :
    logPullbackCLM a b W u = W (Real.exp u) := by
  rw [logPullbackCLM_apply]
  by_cases hW : W (Real.exp u) = 0
  · by_cases hcut : logCutoff a b u = 0
    · simp [hcut, hW]
    · rw [patchedExp_eq_exp_of_cutoff_ne_zero a b u hcut, hW, smul_zero]
  · have hcut := logCutoff_eq_one_of_source a b ha u (hsupp hW)
    rw [patchedExp_eq_exp_of_cutoff_ne_zero a b u (by rw [hcut]; norm_num), hcut, one_smul]

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

theorem compact_family_deriv_sup_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ u : ℝ, ‖iteratedFDeriv ℝ j (F σ) u‖ ≤ C := by
  have hc := (section_iteratedDeriv_smooth F hF j).continuous.norm
  obtain ⟨M, hM⟩ := (hJ.prod hK).bddAbove_image hc.continuousOn
  refine ⟨|M| + 1, by positivity, ?_⟩
  intro σ hσ u
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hu : u ∈ K
  · exact (hM (Set.mem_image_of_mem _ (show (σ, u) ∈ J ×ˢ K from ⟨hσ, hu⟩))).trans
      (by linarith [le_abs_self M])
  · have hs : Function.support (iteratedDeriv j (F σ)) ⊆ K :=
      (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
        (closure_minimal (hsupp σ) hK.isClosed))
    have hz : iteratedDeriv j (F σ) u = 0 := by by_contra hn; exact hu (hs hn)
    simp only [hz, norm_zero]
    positivity

theorem compact_family_mul_deriv_L1_source_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : SchwartzMap ℝ ℂ, ∀ σ ∈ J,
      (∫ u : ℝ, ‖iteratedDeriv j (fun u => F σ u * W u) u‖) ≤
        C * (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  choose c hc hcb using fun i : Fin (j + 1) => compact_family_deriv_sup_bound F hF K hK hsupp J hJ i.val
  let D := (∑ i : Fin (j + 1), c i) + 1
  have hD : 0 < D := by
    have : 0 ≤ ∑ i : Fin (j + 1), c i := Finset.sum_nonneg (fun i _ => (hc i).le)
    dsimp [D]
    linarith
  have hder (i : ℕ) (hi : i ≤ j) (σ : ℝ) (hσ : σ ∈ J) (u : ℝ) :
      ‖iteratedFDeriv ℝ i (F σ) u‖ ≤ D := by
    let k : Fin (j + 1) := ⟨i, by omega⟩
    have hsum : c k ≤ ∑ l : Fin (j + 1), c l :=
      Finset.single_le_sum (fun l _ => (hc l).le) (Finset.mem_univ k)
    exact (hcb k σ hσ u).trans (by dsimp [D]; linarith)
  let B : ℝ := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * D
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨(B + 1) * (volume.real K + 1), by positivity, ?_⟩
  intro W σ hσ
  let S : ℝ := (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hWder (k : ℕ) (hk : k ≤ j) (u : ℝ) : ‖iteratedFDeriv ℝ k W u‖ ≤ S := by
    have hle : schwartzSeminormFamily ℝ ℝ ℂ (0, k) ≤
        (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
      Finset.le_sup (f := schwartzSeminormFamily ℝ ℝ ℂ) (by simp [hk])
    exact (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ W k u).trans (Seminorm.le_def.mp hle W)
  have hb (u : ℝ) : ‖iteratedDeriv j (fun u => F σ u * W u) u‖ ≤ (B + 1) * S := by
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hfσ : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
    apply (norm_iteratedFDeriv_mul_le hfσ (W.smooth ⊤) u (n := j) (by simp)).trans
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * D * S := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hder i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) σ hσ u) (by positivity))
          (hWder (j - i) (Nat.sub_le _ _) u) (norm_nonneg _) (by positivity)
      _ = B * S := by rw [← Finset.sum_mul]
      _ ≤ (B + 1) * S := mul_le_mul_of_nonneg_right (by linarith) hS
  have hmul : Function.support (fun u => F σ u * W u) ⊆ K := by
    intro u hu
    exact hsupp σ (mul_ne_zero_iff.mp hu).1
  have hs : Function.support (iteratedDeriv j (fun u => F σ u * W u)) ⊆ K :=
    (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset _ j).trans
      (closure_minimal hmul hK.isClosed))
  have hzero : ∀ u, u ∉ K → ‖iteratedDeriv j (fun u => F σ u * W u) u‖ = 0 := by
    intro u hu
    have hz : iteratedDeriv j (fun u => F σ u * W u) u = 0 := by by_contra hn; exact hu (hs hn)
    simp [hz]
  have hi := norm_setIntegral_le_of_norm_le_const («μ» := volume)
    (f := fun u => ‖iteratedDeriv j (fun u => F σ u * W u) u‖) hK.measure_lt_top
    (C := (B + 1) * S) (fun u _ => by simpa using hb u)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    Real.norm_of_nonneg (integral_nonneg (fun u => norm_nonneg _))] at hi
  calc
    _ ≤ ((B + 1) * S) * volume.real K := hi
    _ ≤ ((B + 1) * S) * (volume.real K + 1) := by gcongr; linarith
    _ = _ := by dsimp [S]; ring

end CubicReflectionKernel

end

end OAI
end OAIOriginalModule0103

/-! Original module: OAI.NumberTheory.DirichletL.Mellin.UniformKernelBounds
Source SHA256: bc8071918ac9e5a87485400e8d6fd22bff752d993e70f8c8f61067329bd24c11
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0104


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
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set

theorem compact_family_mul_fourier_power_source_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : SchwartzMap ℝ ℂ, ∀ σ ∈ J, ∀ w : ℝ,
      |w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ ≤
        C * (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨C, hC, hb⟩ := compact_family_mul_deriv_L1_source_bound F hF K hK hsupp J hJ j
  refine ⟨C / (2 * Real.pi) ^ j, by positivity, ?_⟩
  intro W σ hσ w
  have hFW : ContDiff ℝ ∞ (Function.uncurry (fun σ u => F σ u * W u)) :=
    hF.mul ((W.smooth ⊤).comp contDiff_snd)
  have hsupport : ∀ σ, Function.support (fun u => F σ u * W u) ⊆ K := by
    intro σ u hu
    exact hsupp σ (mul_ne_zero_iff.mp hu).1
  have hs : ContDiff ℝ ∞ (fun u => F σ u * W u) :=
    hFW.comp (contDiff_const.prodMk contDiff_id)
  have hfour := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hs
    (fun k _ => compact_family_deriv_integrable (fun σ u => F σ u * W u) hFW K hK hsupport σ k)
    (by simp : (j : ℕ∞) ≤ ⊤)
  have hid : (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖) =
      ‖𝓕 (iteratedDeriv j (fun u => F σ u * W u)) w‖ := by
    rw [hfour]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  have hn : ‖𝓕 (iteratedDeriv j (fun u => F σ u * W u)) w‖ ≤
      C * (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
    apply (VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (iteratedDeriv j (fun u => F σ u * W u)) w).trans
    exact hb W σ hσ
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < (2 * Real.pi) ^ j)).mpr
  rw [← hid] at hn
  calc
    _ = (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖) := mul_comm _ _
    _ ≤ _ := hn

theorem compact_family_mul_fourier_weighted_source_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : SchwartzMap ℝ ℂ, ∀ σ ∈ J, ∀ w : ℝ,
      (1 + |w|) ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ ≤
        C * (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨C₀, hC₀, h0⟩ := compact_family_mul_fourier_power_source_bound F hF K hK hsupp J hJ 0
  obtain ⟨Cj, hCj, hj⟩ := compact_family_mul_fourier_power_source_bound F hF K hK hsupp J hJ j
  refine ⟨2 ^ j * (C₀ + Cj), by positivity, ?_⟩
  intro W σ hσ w
  let S := (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hsubset : Finset.Iic (0, 0) ⊆ Finset.Iic (0, j) := by
    intro p hp
    exact Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hp).trans (by simp))
  have hseminorm : (Finset.Iic (0, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ S :=
    Seminorm.le_def.mp (Finset.sup_mono hsubset) W
  have hbase : ‖𝓕 (fun u => F σ u * W u) w‖ ≤ C₀ * S := by
    have hh : ‖𝓕 (fun u => F σ u * W u) w‖ ≤ C₀ * (Finset.Iic (0, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
      simpa using h0 W σ hσ w
    exact hh.trans (mul_le_mul_of_nonneg_left hseminorm hC₀.le)
  have hpower : |w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ ≤ Cj * S := hj W σ hσ w
  by_cases hw : |w| ≤ 1
  · calc
      _ ≤ 2 ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ ≤ 2 ^ j * (C₀ * S) := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤ 2 ^ j * ((C₀ + Cj) * S) := by gcongr; linarith
      _ = _ := by dsimp [S]; ring
  · have hw' : 1 ≤ |w| := le_of_lt (lt_of_not_ge hw)
    calc
      _ ≤ (2 * |w|) ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ = 2 ^ j * (|w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖) := by rw [mul_pow, mul_assoc]
      _ ≤ 2 ^ j * (Cj * S) := mul_le_mul_of_nonneg_left hpower (by positivity)
      _ ≤ 2 ^ j * ((C₀ + Cj) * S) := by gcongr; linarith
      _ = _ := by dsimp [S]; ring

def negativeLogPullbackCLM (a b : ℝ) : SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv).comp (logPullbackCLM a b)

theorem negativeLogPullbackCLM_eq_actual (a b : ℝ) (ha : 0 < a) (W : SchwartzMap ℝ ℂ)
    (hsupp : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) (u : ℝ) :
    negativeLogPullbackCLM a b W u = W (Real.exp (-u)) := by
  change logPullbackCLM a b W (-u) = _
  exact logPullbackCLM_eq_actual a b ha W hsupp (-u)

def logWeight (a b σ u : ℝ) : ℂ := (Real.exp (-σ * u) * logCutoff a b (-u) : ℝ)

theorem logWeight_smooth (a b : ℝ) : ContDiff ℝ ∞ (Function.uncurry (logWeight a b)) := by
  change ContDiff ℝ ∞ (fun p : ℝ × ℝ => ((Real.exp (-p.1 * p.2) * logCutoff a b (-p.2) : ℝ) : ℂ))
  exact Complex.ofRealCLM.contDiff.comp
    ((Real.contDiff_exp.comp (contDiff_fst.neg.mul contDiff_snd)).mul
      ((logCutoff a b).contDiff.comp contDiff_snd.neg))

theorem logWeight_support (a b σ : ℝ) :
    Function.support (logWeight a b σ) ⊆ Metric.closedBall 0 (logRadius a b + 1) := by
  intro u hu
  have hc : logCutoff a b (-u) ≠ 0 := by
    intro hc
    exact hu (by simp [logWeight, hc])
  have hm : -u ∈ Function.support (logCutoff a b) := hc
  rw [(logCutoff a b).support_eq] at hm
  change dist (-u) 0 < logRadius a b + 1 at hm
  change dist u 0 ≤ logRadius a b + 1
  simpa only [dist_zero_right, norm_neg] using hm.le

theorem logWeight_mul_pullback (a b : ℝ) (ha : 0 < a) (W : SchwartzMap ℝ ℂ)
    (hsupp : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) (σ u : ℝ) :
    logWeight a b σ u * negativeLogPullbackCLM a b W u = mellinLogFamily W σ u := by
  rw [negativeLogPullbackCLM_eq_actual a b ha W hsupp]
  by_cases hW : W (Real.exp (-u)) = 0
  · simp [logWeight, mellinLogFamily, hW]
  · have hc := logCutoff_eq_one_of_source a b ha (-u) (hsupp hW)
    simp [logWeight, mellinLogFamily, hc]

theorem mellin_strip_source_bound (a b : ℝ) (ha : 0 < a) (lo hi : ℝ) (j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ σ ∈ Set.Icc lo hi, ∀ t : ℝ,
        (1 + |t|) ^ j * ‖mellin W ((σ : ℂ) + t * Complex.I)‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨C, hC, hb⟩ := compact_family_mul_fourier_weighted_source_bound
    (logWeight a b) (logWeight_smooth a b) (Metric.closedBall 0 (logRadius a b + 1))
    (isCompact_closedBall _ _) (logWeight_support a b) (Set.Icc lo hi) isCompact_Icc j
  obtain ⟨s, D, hD, hDbd⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control
    (negativeLogPullbackCLM a b) (Finset.Iic (0, j))
  refine ⟨s, (1 + 2 * Real.pi) ^ j * C * D, by positivity, ?_⟩
  intro W hsupp σ hσ t
  have hfun : (fun u => logWeight a b σ u * negativeLogPullbackCLM a b W u) = mellinLogFamily W σ :=
    funext (logWeight_mul_pullback a b ha W hsupp σ)
  have hfour := hb (negativeLogPullbackCLM a b W) σ hσ (t / (2 * Real.pi))
  rw [hfun] at hfour
  have ht : |t| = (2 * Real.pi) * |t / (2 * Real.pi)| := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    field_simp
  have hbase : 1 + |t| ≤ (1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos, abs_nonneg (t / (2 * Real.pi))]
  rw [mellin_eq_logFamily_fourier]
  calc
    _ ≤ ((1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|)) ^ j *
        ‖𝓕 (mellinLogFamily W σ) (t / (2 * Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase j) (norm_nonneg _)
    _ = (1 + 2 * Real.pi) ^ j * ((1 + |t / (2 * Real.pi)|) ^ j *
        ‖𝓕 (mellinLogFamily W σ) (t / (2 * Real.pi))‖) := by rw [mul_pow, mul_assoc]
    _ ≤ (1 + 2 * Real.pi) ^ j * (C *
        (D * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)) :=
      mul_le_mul_of_nonneg_left (hfour.trans (mul_le_mul_of_nonneg_left (hDbd W) hC.le)) (by positivity)
    _ = _ := by ring

theorem mellinData_strip_source_bound (a b : ℝ) (ha : 0 < a) (A j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
        (1 + |t|) ^ j * ‖mellinData W ((σ : ℂ) + t * Complex.I)‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  let g : ℕ := 4 * A + 4
  obtain ⟨Cγ, hCγ, hγ⟩ := gammaMultiplier_strip_bound A
  obtain ⟨s, CV, hCV, hVb⟩ := mellin_strip_source_bound a b ha (-(A : ℝ)) (1 / 4) (g + j)
  refine ⟨s, Cγ * CV, mul_pos hCγ hCV, ?_⟩
  intro W hsupp σ hσ t
  have hσ' : -σ ∈ Set.Icc (-(A : ℝ)) (1 / 4) := by constructor <;> linarith [hσ.1, hσ.2]
  have hmb := hVb W hsupp (-σ) hσ' (-t)
  have heq : (-σ : ℝ) + (-t : ℝ) * Complex.I = -((σ : ℂ) + t * Complex.I) := by
    push_cast
    ring
  rw [heq, abs_neg] at hmb
  have hgb : ‖gammaMultiplier ((σ : ℂ) + t * Complex.I)‖ ≤ Cγ * (1 + |t|) ^ g := hγ σ hσ t
  rw [mellinData, norm_mul]
  calc
    _ = ((1 + |t|) ^ j * ‖mellin W (-((σ : ℂ) + t * Complex.I))‖) *
        ‖gammaMultiplier ((σ : ℂ) + t * Complex.I)‖ := by ring
    _ ≤ ((1 + |t|) ^ j * ‖mellin W (-((σ : ℂ) + t * Complex.I))‖) *
        (Cγ * (1 + |t|) ^ g) := mul_le_mul_of_nonneg_left hgb (by positivity)
    _ = Cγ * ((1 + |t|) ^ (g + j) * ‖mellin W (-((σ : ℂ) + t * Complex.I))‖) := by
      rw [pow_add]
      ring
    _ ≤ Cγ * (CV * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := mul_le_mul_of_nonneg_left hmb hCγ.le
    _ = _ := by ring

theorem mellinEulerData_strip_source_bound (a b : ℝ) (ha : 0 < a) (A j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
        ‖mellinEulerData W j ((σ : ℂ) + t * Complex.I)‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W / (1 + t ^ 2) := by
  obtain ⟨s, C, hC, hb⟩ := mellinData_strip_source_bound a b ha A (j + 2)
  refine ⟨s, ((A : ℝ) + 2) ^ j * C, by positivity, ?_⟩
  intro W hsupp σ hσ t
  apply weighted_two_to_cauchy (norm_nonneg _) t
  have hσabs : |σ| ≤ (A : ℝ) + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hσ.1, hσ.2, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  have hz : ‖(σ : ℂ) + t * Complex.I‖ ≤ ((A : ℝ) + 2) * (1 + |t|) := by
    have hnorm := norm_add_le (σ : ℂ) ((t : ℂ) * Complex.I)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] at hnorm
    nlinarith [abs_nonneg t, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  rw [mellinEulerData, norm_mul, norm_pow, norm_neg]
  calc
    _ ≤ (1 + |t|) ^ 2 * ((((A : ℝ) + 2) * (1 + |t|)) ^ j *
        ‖mellinData W ((σ : ℂ) + t * Complex.I)‖) := by gcongr
    _ = ((A : ℝ) + 2) ^ j * ((1 + |t|) ^ (j + 2) *
        ‖mellinData W ((σ : ℂ) + t * Complex.I)‖) := by rw [mul_pow, pow_add]; ring
    _ ≤ ((A : ℝ) + 2) ^ j * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) :=
      mul_le_mul_of_nonneg_left (hb W hsupp σ hσ t) (by positivity)
    _ = _ := by ring

theorem mellinInv_euler_line_source_bound (a b : ℝ) (ha : 0 < a) (A j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ y : ℝ, 0 < y →
        ‖mellinInv σ (mellinEulerData W j) y‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * y ^ (-σ) := by
  obtain ⟨s, C, hC, hb⟩ := mellinEulerData_strip_source_bound a b ha A j
  refine ⟨s, C / 2, by positivity, ?_⟩
  intro W hsupp σ hσ y hy
  let Q := s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hint : ‖∫ t : ℝ, (y : ℂ) ^ (-((σ : ℂ) + t * Complex.I)) *
        mellinEulerData W j ((σ : ℂ) + t * Complex.I)‖ ≤
      (y ^ (-σ) * (C * Q)) * Real.pi := by
    calc
      _ ≤ ∫ t : ℝ, (y ^ (-σ) * (C * Q)) * (1 + t ^ 2)⁻¹ := by
        apply norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _)
        filter_upwards [] with t
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
        simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
        simpa only [div_eq_mul_inv, mul_assoc] using
          mul_le_mul_of_nonneg_left (hb W hsupp σ hσ t) (Real.rpow_nonneg hy.le (-σ))
      _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  rw [mellinInv, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  simp only [smul_eq_mul]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ((y ^ (-σ) * (C * Q)) * Real.pi) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by dsimp [Q]; field_simp

theorem paperKernel_euler_source_power_decay (a b : ℝ) (ha : 0 < a) (A j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ x : ℝ, 0 < x →
        (‖LocalLogFourier.eulerDeriv (paperKernel W) j x‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * x ^ (1 / 4 : ℝ)) ∧
        (‖LocalLogFourier.eulerDeriv (paperKernel W) j x‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * x ^ (-(A : ℝ))) := by
  obtain ⟨s, C, hC, hb⟩ := mellinInv_euler_line_source_bound a b ha A j
  let B := max (paperScale ^ (1 / 4 : ℝ)) (paperScale ^ (-(A : ℝ)))
  have hB : 0 < B := lt_of_lt_of_le (Real.rpow_pos_of_pos paperScale_pos _) (le_max_left _ _)
  refine ⟨s, C * B, mul_pos hC hB, ?_⟩
  intro W hsupp x hx
  let Q := s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hline (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)) :
      ‖LocalLogFourier.eulerDeriv (paperKernel W) j x‖ ≤
        C * Q * (paperScale * x) ^ (-σ) := by
    rw [← paperEulerKernel_eq_euler W (logPullbackCLM a b W)
      (logPullbackCLM_eq_actual a b ha W hsupp) j x hx]
    unfold paperEulerKernel
    rw [mellinInv_euler_shift W a b ha hsupp (W.smooth ⊤) A j σ hσ _ (mul_pos paperScale_pos hx)]
    exact hb W hsupp σ hσ (paperScale * x) (mul_pos paperScale_pos hx)
  have hleft : -(1 / 4 : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ) := by
    constructor
    · rfl
    · linarith [show (0 : ℝ) ≤ A from Nat.cast_nonneg A]
  have hright : (A : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ) := by
    constructor
    · linarith [show (0 : ℝ) ≤ A from Nat.cast_nonneg A]
    · rfl
  constructor
  · have hh := hline _ hleft
    rw [neg_neg, Real.mul_rpow paperScale_pos.le hx.le] at hh
    calc
      _ ≤ C * Q * (paperScale ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) := hh
      _ = (C * paperScale ^ (1 / 4 : ℝ)) * Q * x ^ (1 / 4 : ℝ) := by ring
      _ ≤ (C * B) * Q * x ^ (1 / 4 : ℝ) := by
        gcongr
        exact le_max_left _ _
  · have hh := hline _ hright
    rw [Real.mul_rpow paperScale_pos.le hx.le] at hh
    calc
      _ ≤ C * Q * (paperScale ^ (-(A : ℝ)) * x ^ (-(A : ℝ))) := hh
      _ = (C * paperScale ^ (-(A : ℝ))) * Q * x ^ (-(A : ℝ)) := by ring
      _ ≤ (C * B) * Q * x ^ (-(A : ℝ)) := by
        gcongr
        exact le_max_right _ _

theorem paperKernel_euler_source_uniform_weighted_bound
    (a b : ℝ) (ha : 0 < a) (A K : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ i ≤ K, ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperKernel W) i x‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  choose s c hc hb using fun i : Fin (K + 1) => paperKernel_euler_source_power_decay a b ha A i.val
  let S : Finset (ℕ × ℕ) := Finset.univ.biUnion s
  let D : ℝ := (∑ i : Fin (K + 1), c i) + 1
  have hD : 0 < D := by
    have hs : (0 : ℝ) ≤ ∑ i : Fin (K + 1), c i := Finset.sum_nonneg (fun i _ => (hc i).le)
    dsimp [D]
    linarith
  have hci (i : Fin (K + 1)) : c i ≤ D := by
    have hs : c i ≤ ∑ k : Fin (K + 1), c k :=
      Finset.single_le_sum (fun k _ => (hc k).le) (Finset.mem_univ i)
    dsimp [D]
    linarith
  refine ⟨S, 2 ^ A * (D + D), by positivity, ?_⟩
  intro W hsupp
  let Q := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hsource (i : Fin (K + 1)) : c i * (s i).sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ D * Q := by
    have hsub : s i ⊆ S := Finset.subset_biUnion_of_mem s (Finset.mem_univ i)
    have hq : (s i).sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
      Seminorm.le_def.mp (Finset.sup_mono hsub) W
    exact mul_le_mul (hci i) hq (by positivity) hD.le
  have hsmall : ∀ i ≤ K, ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖LocalLogFourier.eulerDeriv (paperKernel W) i x‖ ≤ D * Q := by
    intro i hi x hx hx1
    let k : Fin (K + 1) := ⟨i, by omega⟩
    have hp : x ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hx.le hx1 (by norm_num)
    calc
      _ ≤ (c k * (s k).sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * x ^ (1 / 4 : ℝ) := (hb k W hsupp x hx).1
      _ ≤ c k * (s k).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
        simpa using mul_le_mul_of_nonneg_left hp (mul_nonneg (hc k).le (by positivity))
      _ ≤ D * Q := hsource k
  have hlarge : ∀ i ≤ K, ∀ x : ℝ, 1 ≤ x →
      x ^ A * ‖LocalLogFourier.eulerDeriv (paperKernel W) i x‖ ≤ D * Q := by
    intro i hi x hx1
    have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    let k : Fin (K + 1) := ⟨i, by omega⟩
    have hxpow : x ^ A ≠ 0 := pow_ne_zero A hx.ne'
    calc
      _ ≤ x ^ A * ((c k * (s k).sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * x ^ (-(A : ℝ))) :=
        mul_le_mul_of_nonneg_left (hb k W hsupp x hx).2 (pow_nonneg hx.le A)
      _ = c k * (s k).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
        rw [Real.rpow_neg hx.le, Real.rpow_natCast]
        field_simp
      _ ≤ D * Q := hsource k
  intro i hi x hx
  have hh := LocalLogFourier.euler_two_regime_bound (paperKernel W) A K (D * Q) (D * Q)
    (mul_nonneg hD.le hQ) (mul_nonneg hD.le hQ) hsmall hlarge i hi x hx
  convert hh using 1 ; dsimp [Q] ; ring

end CubicReflectionKernel

open scoped BigOperators Classical
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (crossSymbol quadraticCrossPhase columnPrimeCoprime)
open FiniteGaussPhase (canonicalProductGauss canonicalProductGauss_cross_factors)
open MixedGaussConversion (localGauss)

def gaussBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ) : ℂ :=
  ∏ i ∈ S, (∏ k ∈ S.erase i, crossSymbol p hg i k ^ e i) *
    localGauss (p i) (hp i) (hg i) (e i)

theorem canonicalProductGauss_eq_gaussBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ)
    (he : ∀ i ∈ S, e i ≠ 0) :
    canonicalProductGauss (fun i : S => p i.val) (fun i => hp i.val)
      (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => e i.val) =
      gaussBlock p hp hg S e := by
  let : DecidableEq S := fun a b => Classical.propDecidable (a = b)
  rw [canonicalProductGauss_cross_factors, ← Finset.prod_mul_distrib]
  have hin (i : S) :
      (∏ k ∈ (Finset.univ : Finset S).erase i,
        (canonicalSextic (Ideal.span {p i.val}) (hg i.val) ^ e i.val)
          (Ideal.Quotient.mk (Ideal.span {p i.val}) (p k.val))) =
      ∏ k ∈ S.erase i.val, crossSymbol p hg i.val k ^ e i.val := by
    apply Finset.prod_bij (fun k _ => k.val)
    · intro k hk
      exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hk).1 (Subtype.ext h), k.property⟩
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro k hk
      refine ⟨⟨k, (Finset.mem_erase.mp hk).2⟩, ?_, rfl⟩
      exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hk).1 (congrArg Subtype.val h),
        Finset.mem_univ _⟩
    · intro k hk
      exact MulChar.pow_apply' _ (he i.val i.property) _
  calc
    _ = ∏ i : S, (∏ k ∈ S.erase i.val, crossSymbol p hg i.val k ^ e i.val) *
        localGauss (p i.val) (hp i.val) (hg i.val) (e i.val) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hin i]
      rfl
    _ = _ := Finset.prod_coe_sort S (fun i =>
      (∏ k ∈ S.erase i, crossSymbol p hg i k ^ e i) * localGauss (p i) (hp i) (hg i) (e i))

def blockCross {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) (e : ι → ℕ) : ℂ :=
  ∏ i ∈ S, ∏ k ∈ T,
    crossSymbol p hg i k ^ e i * crossSymbol p hg k i ^ e k

theorem gaussBlock_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) (hd : Disjoint S T)
    (e : ι → ℕ) :
    gaussBlock p hp hg (S ∪ T) e =
      gaussBlock p hp hg S e * gaussBlock p hp hg T e * blockCross p hg S T e := by
  have hS (i : ι) (hi : i ∈ S) :
      (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) =
      (∏ k ∈ S.erase i, crossSymbol p hg i k ^ e i) *
        ∏ k ∈ T, crossSymbol p hg i k ^ e i := by
    have hn : i ∉ T := fun h => Finset.disjoint_left.mp hd hi h
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hn,
      Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hT (i : ι) (hi : i ∈ T) :
      (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) =
      (∏ k ∈ T.erase i, crossSymbol p hg i k ^ e i) *
        ∏ k ∈ S, crossSymbol p hg i k ^ e i := by
    have hn : i ∉ S := fun h => Finset.disjoint_left.mp hd h hi
    rw [Finset.union_comm S T, Finset.erase_union_distrib, Finset.erase_eq_of_notMem hn,
      Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
  have hpS : (∏ i ∈ S, (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) *
      localGauss (p i) (hp i) (hg i) (e i)) =
      gaussBlock p hp hg S e * (∏ i ∈ S, ∏ k ∈ T, crossSymbol p hg i k ^ e i) := by
    rw [gaussBlock, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hS i hi]
    ring
  have hpT : (∏ i ∈ T, (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) *
      localGauss (p i) (hp i) (hg i) (e i)) =
      gaussBlock p hp hg T e * (∏ i ∈ T, ∏ k ∈ S, crossSymbol p hg i k ^ e i) := by
    rw [gaussBlock, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hT i hi]
    ring
  rw [gaussBlock, Finset.prod_union hd, hpS, hpT,
    Finset.prod_comm (s := T) (t := S)]
  simp only [blockCross, Finset.prod_mul_distrib]
  ring

theorem gaussBlock_congr {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e f : ι → ℕ)
    (he : ∀ i ∈ S, e i = f i) : gaussBlock p hp hg S e = gaussBlock p hp hg S f := by
  apply Finset.prod_congr rfl
  intro i hi
  rw [he i hi]

def cubeActiveSupport {ι : Type*} (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Finset ι :=
  B.filter (fun k => conductorExponent (parity (v k)) (ε₁ k) (ε₂ k) ≠ 0)

def blockCubeExponent {ι : Type*} [DecidableEq ι] (U : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) (i : ι) : ℕ :=
  if i ∈ U then (if side then 5 else 1)
  else (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val

theorem gaussBlock_cube_partition {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (U B : Finset ι) (hd : Disjoint U B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) :
    gaussBlock p hp hg (U ∪ cubeActiveSupport B v ε₁ ε₂)
      (blockCubeExponent U v ε₁ ε₂ side) =
    gaussBlock p hp hg U (fun _ => if side then 5 else 1) *
      gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
        (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
      mixedCubeCross p hg U B v ε₁ ε₂ side := by
  have hdc : Disjoint U (cubeActiveSupport B v ε₁ ε₂) := hd.mono_right (Finset.filter_subset _ _)
  have hU : ∀ i ∈ U, blockCubeExponent U v ε₁ ε₂ side i = (if side then 5 else 1) := by
    intro i hi
    simp only [blockCubeExponent, ite_eq_left hi]
  have hB : ∀ i ∈ cubeActiveSupport B v ε₁ ε₂, blockCubeExponent U v ε₁ ε₂ side i =
      (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val := by
    intro i hi
    exact ite_eq_right (fun hu => Finset.disjoint_left.mp hdc hu hi)
  rw [gaussBlock_union p hp hg U _ hdc,
    gaussBlock_congr p hp hg U _ _ hU, gaussBlock_congr p hp hg _ _ _ hB]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro k hk
  rw [hU i hi, hB k hk]

theorem canonicalProductGauss_cube_partition {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (U B : Finset ι) (hd : Disjoint U B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) :
    canonicalProductGauss (fun i : ↥(U ∪ cubeActiveSupport B v ε₁ ε₂) => p i.val)
      (fun i => hp i.val) (columnPrimeCoprime p hcop _) (fun i => hg i.val)
      (fun i => blockCubeExponent U v ε₁ ε₂ side i.val) =
    gaussBlock p hp hg U (fun _ => if side then 5 else 1) *
      gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
        (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
      ((if side then star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U
          (crtLabel p B v ε₁ ε₂ side))
        else finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U
          (crtLabel p B v ε₁ ε₂ side)) *
        quadraticCrossPhase p hg U (cubeOddSupport B v ε₁ ε₂)) := by
  have he : ∀ i ∈ U ∪ cubeActiveSupport B v ε₁ ε₂, blockCubeExponent U v ε₁ ε₂ side i ≠ 0 := by
    intro i hi
    by_cases hiU : i ∈ U
    · cases side <;> simp [blockCubeExponent, hiU]
    · have hiB := (Finset.mem_union.mp hi).resolve_left hiU
      simp only [blockCubeExponent, ite_eq_right hiU]
      exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hiB).2
  rw [canonicalProductGauss_eq_gaussBlock p hp hcop hg _ _ he,
    gaussBlock_cube_partition p hp hg U B hd,
    mixedCubeCross_eq_row_quadratic p hcop hg hpr U B hd]

theorem columnCoefficient_eq_gaussBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) :
    MixedCrossSeparation.columnCoefficient p hp hcop hg S =
      star (FiniteGaussPhase.angularFactor (∏ i ∈ S, p i)) *
        gaussBlock p hp hg S (fun _ => 2) := by
  unfold MixedCrossSeparation.columnCoefficient FiniteGaussPhase.canonicalProductCoefficient
  rw [Finset.prod_coe_sort]
  rw [canonicalProductGauss_eq_gaussBlock p hp hcop hg S (fun _ => 2) (fun _ _ => by decide)]

theorem blockCross_two_eq_row_four {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) :
    blockCross p hg S T (fun _ => 2) =
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (∏ k ∈ T, p k) ^ 4 := by
  simp only [blockCross, finiteSquarefreeRow, map_prod, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro k hk
  have hr : crossSymbol p hg i k ^ 2 = crossSymbol p hg k i ^ 2 :=
    canonicalSextic_sq_reciprocity_primary (Ideal.span {p i}) (Ideal.span {p k})
      (hg i) (hg k) (p i) (p k) rfl rfl (hpr i) (hpr k)
  change crossSymbol p hg i k ^ 2 * crossSymbol p hg k i ^ 2 = crossSymbol p hg i k ^ 4
  rw [← hr]
  ring

theorem columnCoefficient_union_row_four {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) (hd : Disjoint S T) :
    MixedCrossSeparation.columnCoefficient p hp hcop hg (S ∪ T) =
      MixedCrossSeparation.columnCoefficient p hp hcop hg S *
        MixedCrossSeparation.columnCoefficient p hp hcop hg T *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (∏ k ∈ T, p k) ^ 4 := by
  have ha : FiniteGaussPhase.angularFactor (∏ i ∈ S ∪ T, p i) =
      FiniteGaussPhase.angularFactor (∏ i ∈ S, p i) *
        FiniteGaussPhase.angularFactor (∏ i ∈ T, p i) := by
    rw [Finset.prod_union hd]
    simp only [FiniteGaussPhase.angularFactor, map_mul, norm_mul, Complex.ofReal_mul,
      div_eq_mul_inv, mul_inv_rev]
    ring
  rw [columnCoefficient_eq_gaussBlock, columnCoefficient_eq_gaussBlock,
    columnCoefficient_eq_gaussBlock, ha, star_mul, gaussBlock_union p hp hg S T hd,
    blockCross_two_eq_row_four p hg hpr S T]
  ring

theorem gaussBlock_norm_one {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (S : Finset ι) (e : ι → ℕ) (he : ∀ i ∈ S, e i ≠ 0) (he6 : ∀ i ∈ S, e i < 6) :
    ‖gaussBlock p hp hg S e‖ = 1 := by
  rw [← canonicalProductGauss_eq_gaussBlock p hp hcop hg S e he]
  exact FiniteGaussPhase.norm_canonicalProductGauss
    (fun i : S => p i.val) (fun i => hp i.val) (columnPrimeCoprime p hcop S)
    (fun i => hg i.val) (fun i => hc i.val) (fun i => e i.val)
    (fun i => he i.val i.property) (fun i => he6 i.val i.property)

end FirstPassCubeLabels

end

end OAI
end OAIOriginalModule0104

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.CrossFactorization
Source SHA256: 73001c49ec707cb5d80ec10f16a2f982eb4cf2ee0b22ef189e0a4a911123877d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0105



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
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (crossSymbol quadraticCrossPhase columnPrimeCoprime)
open FiniteGaussPhase (canonicalProductGauss)

theorem blockCross_union_left {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S T C : Finset ι)
    (hd : Disjoint S T) (e : ι → ℕ) :
    blockCross p hg (S ∪ T) C e = blockCross p hg S C e * blockCross p hg T C e :=
  Finset.prod_union hd

def threeBlockExponent {ι : Type*} [DecidableEq ι] (N P : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (i : ι) : ℕ :=
  if i ∈ N then 5 else if i ∈ P then 1
  else (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val

theorem gaussBlock_three_cube_partition {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    gaussBlock p hp hg ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂)
      (threeBlockExponent N P v ε₁ ε₂) =
    gaussBlock p hp hg N (fun _ => 5) * gaussBlock p hp hg P (fun _ => 1) *
      gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
        (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
      quadraticCrossPhase p hg N P * mixedCubeCross p hg N B v ε₁ ε₂ true *
        mixedCubeCross p hg P B v ε₁ ε₂ false := by
  let C := cubeActiveSupport B v ε₁ ε₂
  let e := threeBlockExponent N P v ε₁ ε₂
  have hNC : Disjoint N C := hNB.mono_right (Finset.filter_subset _ _)
  have hPC : Disjoint P C := hPB.mono_right (Finset.filter_subset _ _)
  have hNPC : Disjoint (N ∪ P) C := Finset.disjoint_union_left.mpr ⟨hNC, hPC⟩
  have hN (i : ι) (hi : i ∈ N) : e i = 5 := by simp [e, threeBlockExponent, hi]
  have hP (i : ι) (hi : i ∈ P) : e i = 1 := by
    have hn : i ∉ N := fun h => Finset.disjoint_left.mp hNP h hi
    simp [e, threeBlockExponent, hn, hi]
  have hC (i : ι) (hi : i ∈ C) : e i =
      (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val := by
    have hn : i ∉ N := fun h => Finset.disjoint_left.mp hNC h hi
    have hp' : i ∉ P := fun h => Finset.disjoint_left.mp hPC h hi
    simp [e, threeBlockExponent, hn, hp']
  have hcrossNP : blockCross p hg N P e = quadraticCrossPhase p hg N P := by
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro k hk
    rw [hN i hi, hP k hk, pow_one]
    exact MixedCrossSeparation.mixed_cross_eq_quadratic p hg i k (hpr i) (hpr k)
  have hcrossNC : blockCross p hg N C e = mixedCubeCross p hg N B v ε₁ ε₂ true := by
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro k hk
    rw [hN i hi, hC k hk]
    rfl
  have hcrossPC : blockCross p hg P C e = mixedCubeCross p hg P B v ε₁ ε₂ false := by
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro k hk
    rw [hP i hi, hC k hk]
    rfl
  change gaussBlock p hp hg ((N ∪ P) ∪ C) e = _
  rw [gaussBlock_union p hp hg (N ∪ P) C hNPC, gaussBlock_union p hp hg N P hNP,
    blockCross_union_left p hg N P C hNP,
    gaussBlock_congr p hp hg N e (fun _ => 5) hN,
    gaussBlock_congr p hp hg P e (fun _ => 1) hP,
    gaussBlock_congr p hp hg C e _ hC, hcrossNP, hcrossNC, hcrossPC]
  ring

theorem canonicalProductGauss_three_cube_partition {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    canonicalProductGauss
      (fun i : ↥((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂) => p i.val)
      (fun i => hp i.val) (columnPrimeCoprime p hcop _) (fun i => hg i.val)
      (fun i => threeBlockExponent N P v ε₁ ε₂ i.val) =
    gaussBlock p hp hg N (fun _ => 5) * gaussBlock p hp hg P (fun _ => 1) *
      gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
        (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
      quadraticCrossPhase p hg N P *
      (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N (crtLabel p B v ε₁ ε₂ true)) *
        quadraticCrossPhase p hg N (cubeOddSupport B v ε₁ ε₂)) *
      (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P (crtLabel p B v ε₁ ε₂ false) *
        quadraticCrossPhase p hg P (cubeOddSupport B v ε₁ ε₂)) := by
  have he : ∀ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂,
      threeBlockExponent N P v ε₁ ε₂ i ≠ 0 := by
    intro i hi
    by_cases hn : i ∈ N
    · simp [threeBlockExponent, hn]
    by_cases hp' : i ∈ P
    · simp [threeBlockExponent, hn, hp']
    · have hiC : i ∈ cubeActiveSupport B v ε₁ ε₂ := by simpa [hn, hp'] using hi
      simp only [threeBlockExponent, ite_eq_right hn, ite_eq_right hp']
      exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hiC).2
  rw [canonicalProductGauss_eq_gaussBlock p hp hcop hg _ _ he,
    gaussBlock_three_cube_partition p hp hg hpr N P B hNP hNB hPB,
    mixedCubeCross_eq_row_quadratic p hcop hg hpr N B hNB,
    mixedCubeCross_eq_row_quadratic p hcop hg hpr P B hPB]
  rfl

theorem gaussBlock_eq_mobius_converted {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) (side : Bool) :
    gaussBlock p hp hg S (fun _ => if side then 5 else 1) =
      FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) S *
        MixedCrossSeparation.convertedColumnBlock p hp hg S side := by
  have hinj : Function.Injective (fun i => Ideal.span {p i}) := by
    intro i k hik
    by_contra hne
    have ht := (hcop hne).sup_eq
    rw [hik, sup_idem] at ht
    exact (inferInstance : (Ideal.span {p k}).IsMaximal).ne_top ht
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  rw [FirstCauchyArithmetic.supportMobius,
    prime_product_moebius (fun i => Ideal.span {p i}) hprime hinj S]
  unfold gaussBlock MixedCrossSeparation.convertedColumnBlock
  rw [← Finset.prod_neg]
  apply Finset.prod_congr rfl
  intro i hi
  have hl := MixedGaussConversion.neg_localGauss_eq_converted (p i) (hp i) (hg i) (hc i) (hpr i) side
  change (∏ k ∈ S.erase i, crossSymbol p hg i k ^ (if side then 5 else 1)) *
      MixedGaussConversion.localGauss (p i) (hp i) (hg i) (if side then 5 else 1) =
    -((∏ k ∈ S.erase i, crossSymbol p hg i k ^ (if side then 5 else 1)) *
      MixedGaussConversion.convertedLocal (p i) (hp i) (hg i) side)
  rw [← hl]
  ring

theorem a_weighted_three_cube_gauss {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) :
    star (MixedCrossSeparation.columnCoefficient p hp hcop hg N * C₁ N) *
      (MixedCrossSeparation.columnCoefficient p hp hcop hg P * C₂ P) *
      canonicalProductGauss
        (fun i : ↥((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂) => p i.val)
        (fun i => hp i.val) (columnPrimeCoprime p hcop _) (fun i => hg i.val)
        (fun i => threeBlockExponent N P v ε₁ ε₂ i.val) =
    (gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
        (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
      quadraticCrossPhase p hg N P *
      quadraticCrossPhase p hg N (cubeOddSupport B v ε₁ ε₂) *
      quadraticCrossPhase p hg P (cubeOddSupport B v ε₁ ε₂)) *
      star (FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) N *
        FirstCauchyArithmetic.firstPassColumnMinus p hp hcop hg C₁ (crtLabel p B v ε₁ ε₂ true) N) *
      (FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) P *
        FirstCauchyArithmetic.firstPassColumnPlus p hp hcop hg C₂ (crtLabel p B v ε₁ ε₂ false) P) := by
  rw [canonicalProductGauss_three_cube_partition p hp hcop hg hpr N P B hNP hNB hPB]
  have hconvN := gaussBlock_eq_mobius_converted p hp hcop hg hc hpr N true
  have hconvP := gaussBlock_eq_mobius_converted p hp hcop hg hc hpr P false
  simp only [Bool.false_eq_true, ↓reduceIte] at hconvN hconvP
  rw [hconvN, hconvP]
  have hn := MixedCrossSeparation.columnCoefficient_cancel_true p hp hcop hg hc hpr N
  have hp' := MixedCrossSeparation.columnCoefficient_cancel_false p hp hcop hg hc hpr P
  simp only [FirstCauchyArithmetic.firstPassColumnMinus, FirstCauchyArithmetic.firstPassColumnPlus,
    star_mul, star_star, FirstCauchyArithmetic.star_supportMobius]
  calc
    _ = (star (MixedCrossSeparation.columnCoefficient p hp hcop hg N) *
        MixedCrossSeparation.convertedColumnBlock p hp hg N true) *
      (MixedCrossSeparation.columnCoefficient p hp hcop hg P *
        MixedCrossSeparation.convertedColumnBlock p hp hg P false) *
      (star (C₁ N) * C₂ P *
        FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) N *
        FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) P *
        gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
          (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
        quadraticCrossPhase p hg N P *
        quadraticCrossPhase p hg N (cubeOddSupport B v ε₁ ε₂) *
        quadraticCrossPhase p hg P (cubeOddSupport B v ε₁ ε₂) *
        star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N (crtLabel p B v ε₁ ε₂ true)) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P (crtLabel p B v ε₁ ε₂ false)) := by ring
    _ = _ := by rw [hn, hp']; ring

end FirstPassCubeLabels

namespace QuadraticGaussRay
open EisensteinEPrimaryPhase ActualEisensteinCoordinates ActualEisensteinCubic

theorem quadraticRayValue_square (r : Coord) (hr : odd r) :
    quadraticRayValue (mul r r) = 1 := by
  have hi : (Complex.I : ℂ)⁻¹ = -Complex.I := by
    apply inv_eq_of_mul_eq_one_right
    norm_num
  have h : mul r r = (1, 0) ∨ mul r r = (3, 3) ∨ mul r r = (0, 1) := by
    decide +revert
  rcases h with h | h | h
  · rw [h]
    change breveGaussianFourTerms 1 0 = 1
    rw [breveGaussianFourTerms_formula]
    norm_num [hi]
  · rw [h]
    change breveGaussianFourTerms 3 3 = 1
    rw [breveGaussianFourTerms_formula]
    norm_num [hi]
  · rw [h]
    change breveGaussianFourTerms 0 1 = 1
    rw [breveGaussianFourTerms_formula]
    norm_num [hi]
    ring

theorem quadraticRayValue_same_residue_product (a b : ActualEisensteinCubic.O)
    (ha : odd (residue a)) (hab : residue a = residue b) :
    quadraticRayValue (residue (a * b)) = 1 := by
  rw [residue_mul, ← hab]
  exact quadraticRayValue_square _ ha

end QuadraticGaussRay

namespace QuadraticMainBoundaryFibers
abbrev O := ActualEisensteinCubic.O
open IdealMobiusDivisorSum QuadraticMainBoundary

def productIdeal (x : Ideal O × Ideal O × Ideal O) : Ideal O := x.1 * x.2.1 * x.2.2

theorem product_fiber_card_le (s : Finset (Ideal O × Ideal O × Ideal O))
    (G : Ideal O) (hG : G ≠ 0)
    (hdiv : ∀ x ∈ s, x.2.1 ∣ G ∧ x.2.2 ∣ G) (B : Ideal O) :
    (s.filter (fun x => productIdeal x = B)).card ≤ (idealDivisors G).card ^ 2 := by
  have hle : (s.filter (fun x => productIdeal x = B)).card ≤
      ((idealDivisors G) ×ˢ (idealDivisors G)).card := by
    apply Finset.card_le_card_of_injOn (fun x => (x.2.1, x.2.2))
    · intro x hx
      have hd := hdiv x (Finset.mem_filter.mp hx).1
      exact Finset.mem_product.mpr ⟨(mem_idealDivisors hG).mpr hd.1,
        (mem_idealDivisors hG).mpr hd.2⟩
    · intro x hx y hy hde
      obtain ⟨hD, hE⟩ := Prod.mk.inj hde
      have hd := hdiv x (Finset.mem_filter.mp hx).1
      have hD0 := ne_zero_of_dvd_ne_zero hG hd.1
      have hE0 := ne_zero_of_dvd_ne_zero hG hd.2
      have hprod := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
      change x.1 * x.2.1 * x.2.2 = y.1 * y.2.1 * y.2.2 at hprod
      rw [← hD, ← hE] at hprod
      have hH : x.1 = y.1 := mul_right_cancel₀ hD0 (mul_right_cancel₀ hE0 hprod)
      exact Prod.ext hH (Prod.ext hD hE)
  simpa only [Finset.card_product, pow_two] using hle

theorem product_fiber_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (Ideal O × Ideal O × Ideal O)) (G : Ideal O),
      G ≠ 0 → (∀ x ∈ s, x.2.1 ∣ G ∧ x.2.2 ∣ G) → ∀ B : Ideal O,
      ((s.filter (fun x => productIdeal x = B)).card : ℝ) ≤
        C * (Ideal.absNorm G : ℝ) ^ ε := by
  obtain ⟨C, hC, hbound⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) (by linarith)
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro s G hG hdiv B
  have hc : ((s.filter (fun x => productIdeal x = B)).card : ℝ) ≤
      ((idealDivisors G).card : ℝ) ^ 2 := by
    exact_mod_cast product_fiber_card_le s G hG hdiv B
  have hb := pow_le_pow_left₀ (by positivity : 0 ≤ ((idealDivisors G).card : ℝ))
    (hbound G hG) 2
  have heq : ((Ideal.absNorm G : ℝ) ^ (ε / 2)) ^ 2 = (Ideal.absNorm G : ℝ) ^ ε := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    norm_num
  apply hc.trans
  simpa only [mul_pow, heq] using hb

def boundaryCoefficient (K : ℝ) (s : Finset (Ideal O × Ideal O × Ideal O))
    (B : Ideal O) : ℂ :=
  ∑ x ∈ s.filter (fun x => productIdeal x = B),
    (UniqueFactorizationMonoid.moebius x.2.2 : ℂ) * (cutoffDifference K x.1 x.2.1 : ℝ)

theorem norm_cutoffDifference_le (K : ℝ) (H D : Ideal O) :
    ‖(cutoffDifference K H D : ℂ)‖ ≤ 1 := by
  unfold cutoffDifference
  split_ifs <;> norm_num

theorem boundaryCoefficient_norm_le_card (K : ℝ)
    (s : Finset (Ideal O × Ideal O × Ideal O)) (B : Ideal O) :
    ‖boundaryCoefficient K s B‖ ≤ (s.filter (fun x => productIdeal x = B)).card := by
  unfold boundaryCoefficient
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _x ∈ s.filter (fun x => productIdeal x = B), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      rw [norm_mul]
      have hm : ‖(UniqueFactorizationMonoid.moebius x.2.2 : ℂ)‖ ≤ 1 := by
        unfold UniqueFactorizationMonoid.moebius
        split_ifs <;> simp
      exact (mul_le_of_le_one_left (norm_nonneg _) hm).trans (norm_cutoffDifference_le _ _ _)
    _ = _ := by simp

theorem boundaryCoefficient_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ) (s : Finset (Ideal O × Ideal O × Ideal O)) (G : Ideal O),
      G ≠ 0 → (∀ x ∈ s, x.2.1 ∣ G ∧ x.2.2 ∣ G) → ∀ B : Ideal O,
      ‖boundaryCoefficient K s B‖ ≤ C * (Ideal.absNorm G : ℝ) ^ ε := by
  obtain ⟨C, hC, hbound⟩ := product_fiber_small_power ε hε
  exact ⟨C, hC, fun K s G hG hdiv B =>
    (boundaryCoefficient_norm_le_card K s B).trans (hbound s G hG hdiv B)⟩

theorem boundaryCoefficient_eq_zero_below (K : ℝ)
    (s : Finset (Ideal O × Ideal O × Ideal O)) (G : Ideal O) (hG : G ≠ 0)
    (hdiv : ∀ x ∈ s, x.2.1 ∣ G ∧ x.2.2 ∣ G)
    (B : Ideal O) (hB : (Ideal.absNorm B : ℝ) ≤ K) : boundaryCoefficient K s B = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  have hx' := Finset.mem_filter.mp hx
  have hd := hdiv x hx'.1
  have hz := cutoffDifference_eq_zero_of_product_le K
    (ne_zero_of_dvd_ne_zero hG hd.1) (ne_zero_of_dvd_ne_zero hG hd.2)
    (by simpa only [← hx'.2, productIdeal] using hB)
  rw [hz, Complex.ofReal_zero, mul_zero]

end QuadraticMainBoundaryFibers

namespace CoprimeSieveOperator
open FiniteSieveOperator CoprimeMobiusExtension

theorem square_norm_sum {n : Type*} [Fintype n] (z : n → ℂ) :
    (↑(‖∑ j, z j‖ ^ 2) : ℂ) = ∑ j, ∑ k, star (z j) * z k := by
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, starRingEnd_apply]
  rw [Finset.sum_mul_sum]

theorem disjoint_gram_expansion {ι n : Type*} [DecidableEq ι] [Fintype n]
    (B : Finset ι) (support : n → Finset ι) (hs : ∀ j, support j ⊆ B) (z : n → ℂ) :
    (∑ j, ∑ k, if Disjoint (support j) (support k) then star (z j) * z k else 0) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        (↑(‖∑ j, if D ⊆ support j then z j else 0‖ ^ 2) : ℂ) := by
  have hp (j k : n) :
      (if Disjoint (support j) (support k) then star (z j) * z k else 0) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        (if D ⊆ support j ∧ D ⊆ support k then star (z j) * z k else 0) := by
    calc
      _ = (if Disjoint (support j) (support k) then (1 : ℂ) else 0) * (star (z j) * z k) := by
        split_ifs <;> simp
      _ = _ := by
        rw [disjoint_indicator_expansion B _ _ (hs j) (hs k), Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro D _
        split_ifs <;> simp
  simp_rw [hp]
  calc
    _ = ∑ j, ∑ D ∈ B.powerset, ∑ k,
        (-1 : ℂ) ^ D.card *
          (if D ⊆ support j ∧ D ⊆ support k then star (z j) * z k else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ D ∈ B.powerset, ∑ j, ∑ k,
        (-1 : ℂ) ^ D.card *
          (if D ⊆ support j ∧ D ⊆ support k then star (z j) * z k else 0) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D _
      simp_rw [← Finset.mul_sum]
      congr 1
      rw [square_norm_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      by_cases hj : D ⊆ support j <;> by_cases hk : D ⊆ support k <;> simp [hj, hk]

theorem masked_coefficient_energy {ι n : Type*} [DecidableEq ι] [Fintype n]
    (B : Finset ι) (support : n → Finset ι) (hs : ∀ j, support j ⊆ B) (a : n → ℂ) :
    (∑ D ∈ B.powerset, ∑ j, ‖if D ⊆ support j then a j else 0‖ ^ 2) =
      ∑ j, (2 : ℝ) ^ (support j).card * ‖a j‖ ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have heq : B.powerset.filter (fun D => D ⊆ support j) = (support j).powerset := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨And.right, fun h => ⟨h.trans (hs j), h⟩⟩
  have hite (D : Finset ι) : ‖if D ⊆ support j then a j else 0‖ ^ 2 =
      if D ⊆ support j then ‖a j‖ ^ 2 else 0 := by split_ifs <;> simp
  simp_rw [hite]
  rw [← Finset.sum_filter, heq]
  simp

theorem weighted_energy_bound {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) (a : n → ℂ) (w : m → ℂ) (W : ℝ)
    (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) :
    ‖∑ i, w i * (↑(‖∑ j, A i j * a j‖ ^ 2) : ℂ)‖ ≤
      W * ‖operator A‖ ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
  calc
    _ ≤ ∑ i, ‖w i * (↑(‖∑ j, A i j * a j‖ ^ 2) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i, W * ‖∑ j, A i j * a j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right (hw i) (sq_nonneg _)
    _ = W * ∑ i, ‖∑ j, A i j * a j‖ ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (energy_bound A a) hW

theorem coprime_gram_operator_bound {ι m n : Type*} [DecidableEq ι]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (B : Finset ι) (support : n → Finset ι) (hs : ∀ j, support j ⊆ B)
    (A : Matrix m n ℂ) (a : n → ℂ) (w : m → ℂ) (W : ℝ)
    (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) :
    ‖∑ i, w i * (∑ j, ∑ k,
      if Disjoint (support j) (support k) then
        star (A i j * a j) * (A i k * a k) else 0)‖ ≤
      W * ‖operator A‖ ^ 2 * ∑ j, (2 : ℝ) ^ (support j).card * ‖a j‖ ^ 2 := by
  have heq : (∑ i, w i * (∑ j, ∑ k,
      if Disjoint (support j) (support k) then
        star (A i j * a j) * (A i k * a k) else 0)) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        ∑ i, w i * (↑(‖∑ j, A i j * (if D ⊆ support j then a j else 0)‖ ^ 2) : ℂ) := by
    simp_rw [disjoint_gram_expansion B support hs, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro D _
    apply Finset.sum_congr rfl
    intro i _
    have hz : (∑ j, if D ⊆ support j then A i j * a j else 0) =
        ∑ j, A i j * (if D ⊆ support j then a j else 0) := by
      apply Finset.sum_congr rfl
      intro j _
