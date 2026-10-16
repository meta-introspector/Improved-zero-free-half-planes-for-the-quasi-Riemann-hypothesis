
theorem finite_divisible_count
    (p : O) (hp : p ≠ 0) (S : Finset O) (D : ℕ)
    (hdiv : ∀ n ∈ S, p ∣ n)
    (hnorm : ∀ n ∈ S, qNat n ≤ D) :
    S.card ≤ 64 * (D / qNat p + 1) := by
  classical
  let quotient : (x : {n : O // n ∈ S}) → O :=
    fun x => Classical.choose (hdiv x.1 x.2)
  have hrep : ∀ x : {n : O // n ∈ S}, x.1 = p * quotient x := by
    intro x
    exact Classical.choose_spec (hdiv x.1 x.2)
  have hinj : Function.Injective quotient := by
    intro x y hxy
    apply Subtype.ext
    calc
      x.1 = p * quotient x := hrep x
      _ = p * quotient y := by rw [hxy]
      _ = y.1 := (hrep y).symm
  let T : Finset O := S.attach.image quotient
  have hcard : T.card = S.card := by
    simpa [T] using Finset.card_image_of_injective S.attach hinj
  have hT : ∀ m ∈ T, qNat (p * m) ≤ D := by
    intro m hm
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hm
    rw [← hrep x]
    exact hnorm x.1 x.2
  calc
    S.card = T.card := hcard.symm
    _ ≤ 64 * (D / qNat p + 1) := finite_multiples_count p hp T D hT

end ShortDraftLatticeCount

namespace IdealGaussCRT
open AddChar MulChar

private theorem leftAddChar_mulShift {T R S : Type*}
    [CommRing T] [CommRing R] [CommRing S]
    (e : T ≃+* R × S) (ψ : AddChar T ℂ) (h : T) :
    leftAddChar e (ψ.mulShift h) =
      (leftAddChar e ψ).mulShift (e h).1 := by
  ext z
  change ψ (h * e.symm (z, 0)) = ψ (e.symm ((e h).1 * z, 0))
  congr 1
  apply e.injective
  ext <;> simp

private theorem rightAddChar_mulShift {T R S : Type*}
    [CommRing T] [CommRing R] [CommRing S]
    (e : T ≃+* R × S) (ψ : AddChar T ℂ) (h : T) :
    rightAddChar e (ψ.mulShift h) =
      (rightAddChar e ψ).mulShift (e h).2 := by
  ext z
  change ψ (h * e.symm (0, z)) = ψ (e.symm (0, (e h).2 * z))
  congr 1
  apply e.injective
  ext <;> simp

theorem gauss_transform_crt {T R S : Type*}
    [CommRing T] [Field R] [Field S]
    [Fintype T] [Fintype R] [Fintype S]
    (e : T ≃+* R × S)
    (χR : MulChar R ℂ) (χS : MulChar S ℂ)
    (ψ : AddChar T ℂ) (hχR : χR ≠ 1) (hχS : χS ≠ 1)
    (h : T) :
    (∑ x : T, χR (e x).1 * χS (e x).2 * ψ (h * x)) =
      (if (e h).1 = 0 then 0 else
        (χR (e h).1)⁻¹ * gaussSum χR (leftAddChar e ψ)) *
      (if (e h).2 = 0 then 0 else
        (χS (e h).2)⁻¹ * gaussSum χS (rightAddChar e ψ)) := by
  have hbase := gauss_sum_crt e χR χS (ψ.mulShift h)
  simp only [AddChar.mulShift_apply] at hbase
  rw [leftAddChar_mulShift, rightAddChar_mulShift] at hbase
  have hR := ShortDraftFiniteGaussFourier.gauss_transform χR
    (leftAddChar e ψ) hχR (e h).1
  have hS := ShortDraftFiniteGaussFourier.gauss_transform χS
    (rightAddChar e ψ) hχS (e h).2
  have hR' : gaussSum χR ((leftAddChar e ψ).mulShift (e h).1) =
      (if (e h).1 = 0 then 0 else
        (χR (e h).1)⁻¹ * gaussSum χR (leftAddChar e ψ)) := by
    simpa only [gaussSum, AddChar.mulShift_apply] using hR
  have hS' : gaussSum χS ((rightAddChar e ψ).mulShift (e h).2) =
      (if (e h).2 = 0 then 0 else
        (χS (e h).2)⁻¹ * gaussSum χS (rightAddChar e ψ)) := by
    simpa only [gaussSum, AddChar.mulShift_apply] using hS
  rw [hR', hS'] at hbase
  exact hbase

theorem gauss_transform_ideal_crt {A : Type*} [CommRing A]
    (I J : Ideal A) (hc : IsCoprime I J)
    [I.IsMaximal] [J.IsMaximal]
    [Fintype (A ⧸ I * J)] [Fintype (A ⧸ I)] [Fintype (A ⧸ J)]
    (χI : MulChar (A ⧸ I) ℂ) (χJ : MulChar (A ⧸ J) ℂ)
    (ψ : AddChar (A ⧸ I * J) ℂ)
    (hχI : χI ≠ 1) (hχJ : χJ ≠ 1)
    (h : A ⧸ I * J) :
    (∑ x : A ⧸ I * J,
      χI (Ideal.Quotient.factor (Ideal.mul_le_left : I * J ≤ I) x) *
      χJ (Ideal.Quotient.factor (Ideal.mul_le_right : I * J ≤ J) x) *
      ψ (h * x)) =
      (if Ideal.Quotient.factor (Ideal.mul_le_left : I * J ≤ I) h = 0
        then 0 else
        (χI (Ideal.Quotient.factor (Ideal.mul_le_left : I * J ≤ I) h))⁻¹ *
          gaussSum χI
            (leftAddChar (Ideal.quotientMulEquivQuotientProd I J hc) ψ)) *
      (if Ideal.Quotient.factor (Ideal.mul_le_right : I * J ≤ J) h = 0
        then 0 else
        (χJ (Ideal.Quotient.factor (Ideal.mul_le_right : I * J ≤ J) h))⁻¹ *
          gaussSum χJ
            (rightAddChar (Ideal.quotientMulEquivQuotientProd I J hc) ψ)) := by
  let : Field (A ⧸ I) := Ideal.Quotient.field I
  let : Field (A ⧸ J) := Ideal.Quotient.field J
  let e := Ideal.quotientMulEquivQuotientProd I J hc
  convert gauss_transform_crt e χI χJ ψ hχI hχJ h using 1 <;>
    simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
      Ideal.quotientMulEquivQuotientProd_snd]

end IdealGaussCRT

namespace ActualEisensteinCubic

section

open ShortDraftLatticeCount

theorem prime_sixth_row_approx
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι)
    (weight : O → ℂ) (p : O) (hp : p ≠ 0) (D : ℕ)
    (hfactor : ∀ n ∈ columns,
      (∃ i ∈ support n, p ∈ P i) → p ∣ n)
    (hcolnorm : ∀ n ∈ columns, qNat n ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1) :
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (p ^ 6))‖ ≤
      (64 * (D / qNat p + 1) : ℕ) := by
  classical
  let S := columns.filter (fun n => ∃ i ∈ support n, p ∈ P i)
  have hdiv : ∀ n ∈ S, p ∣ n := by
    intro n hn
    obtain ⟨hcol, hsupp⟩ := Finset.mem_filter.mp hn
    exact hfactor n hcol hsupp
  have hnorm : ∀ n ∈ S, qNat n ≤ D := by
    intro n hn
    exact hcolnorm n (Finset.mem_filter.mp hn).1
  have hcount := finite_divisible_count p hp S D hdiv hnorm
  calc
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (p ^ 6))‖ ≤
        ∑ n ∈ S, ‖weight n‖ :=
      finiteSquarefreeRow_difference_norm P hgood columns support weight p
    _ ≤ ∑ n ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hweight n (Finset.mem_filter.mp hn).1
    _ = (S.card : ℝ) := by simp
    _ ≤ (64 * (D / qNat p + 1) : ℕ) := by exact_mod_cast hcount

end

theorem prime_sixth_row_approx_maximal
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι)
    (weight : O → ℂ) (p : O) (hp : p ≠ 0)
    (hprime : (Ideal.span {p} : Ideal O).IsMaximal)
    (D : ℕ)
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hcolnorm : ∀ n ∈ columns, ShortDraftLatticeCount.qNat n ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1) :
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (p ^ 6))‖ ≤
      (64 * (D / ShortDraftLatticeCount.qNat p + 1) : ℕ) := by
  apply prime_sixth_row_approx P hgood columns support weight p hp D
    ?_ hcolnorm hweight
  intro n hn ⟨i, hi, hpi⟩
  have hle : (Ideal.span {p} : Ideal O) ≤ P i :=
    (Ideal.span_singleton_le_iff_mem (P i)).mpr hpi
  have hne : P i ≠ ⊤ := (inferInstance : (P i).IsMaximal).ne_top
  have heq : (Ideal.span {p} : Ideal O) = P i := hprime.eq_of_le hne hle
  have hnP : n ∈ Ideal.span {p} := by
    rw [heq]
    exact hsupport n hn i hi
  exact Ideal.mem_span_singleton.mp hnP

open AddChar MulChar

theorem canonical_two_prime_gauss_transform
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hc : IsCoprime P Q)
    [Fintype (O ⧸ P * Q)] [Fintype (O ⧸ P)] [Fintype (O ⧸ Q)]
    (hgoodP : lambda ∉ P) (hgoodQ : lambda ∉ Q)
    (hcharP : ringChar (O ⧸ P) ≠ 2)
    (hcharQ : ringChar (O ⧸ Q) ≠ 2)
    (j k : ℕ) (hj0 : j ≠ 0) (hj6 : j < 6)
    (hk0 : k ≠ 0) (hk6 : k < 6)
    (ψ : AddChar (O ⧸ P * Q) ℂ) (h : O ⧸ P * Q) :
    (∑ x : O ⧸ P * Q,
      (canonicalSextic P hgoodP ^ j)
          (Ideal.Quotient.factor (Ideal.mul_le_left : P * Q ≤ P) x) *
      (canonicalSextic Q hgoodQ ^ k)
          (Ideal.Quotient.factor (Ideal.mul_le_right : P * Q ≤ Q) x) *
      ψ (h * x)) =
      (if Ideal.Quotient.factor (Ideal.mul_le_left : P * Q ≤ P) h = 0
        then 0 else
        ((canonicalSextic P hgoodP ^ j)
          (Ideal.Quotient.factor (Ideal.mul_le_left : P * Q ≤ P) h))⁻¹ *
          gaussSum (canonicalSextic P hgoodP ^ j)
            (IdealGaussCRT.leftAddChar
              (Ideal.quotientMulEquivQuotientProd P Q hc) ψ)) *
      (if Ideal.Quotient.factor (Ideal.mul_le_right : P * Q ≤ Q) h = 0
        then 0 else
        ((canonicalSextic Q hgoodQ ^ k)
          (Ideal.Quotient.factor (Ideal.mul_le_right : P * Q ≤ Q) h))⁻¹ *
          gaussSum (canonicalSextic Q hgoodQ ^ k)
            (IdealGaussCRT.rightAddChar
              (Ideal.quotientMulEquivQuotientProd P Q hc) ψ)) := by
  exact IdealGaussCRT.gauss_transform_ideal_crt P Q hc
    (canonicalSextic P hgoodP ^ j)
    (canonicalSextic Q hgoodQ ^ k) ψ
    (canonicalSextic_pow_ne_one P hgoodP hcharP hj0 hj6)
    (canonicalSextic_pow_ne_one Q hgoodQ hcharQ hk0 hk6) h

end ActualEisensteinCubic

end

end OAI
end OAIOriginalModule0045

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.QuadraticTrace
Source SHA256: cd11e2de58ab4326bcd2d7c376ef25987f8a06031d5cf3ac67e1b9f704d10048
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0046


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

namespace ActualEisensteinCubic

section

open ActualEisensteinCoordinates ShortDraftLatticeCount

theorem omega_sq_for_norm : omega ^ 2 = -omega - 1 := by
  simpa [omega] using
    IsCyclotomicExtension.Rat.Three.eta_sq
      (IsCyclotomicExtension.zeta_spec 3 ℚ K)

theorem conjO_eval_coordinates (a b : ℤ) :
    conjO (eval a b) = eval (a - b) (-b) := by
  have hω : ActualEisensteinCoordinates.omega = omega := rfl
  simp only [eval, map_add, map_mul, map_intCast, hω, conjO_omega]
  rw [omega_sq_for_norm]
  push_cast
  ring

theorem coordinate_norm_eq_mul_conjO (p : O) :
    ((q (coords p) : ℤ) : O) = p * conjO p := by
  let a := (coords p).1
  let b := (coords p).2
  have hp : p = eval a b := (eval_coords p).symm
  symm
  calc
    p * conjO p = eval a b * eval (a - b) (-b) := by
      rw [hp, conjO_eval_coordinates]
    _ = ((q (coords p) : ℤ) : O) := by
      rw [eval_mul]
      simp only [eval, q]
      dsimp [a, b]
      push_cast
      ring

theorem algebraNorm_eq_coordinate_norm (p : O) :
    Algebra.norm ℤ p = q (coords p) := by
  have h := (norm_int_eq_mul_conjO p).trans
    (coordinate_norm_eq_mul_conjO p).symm
  exact_mod_cast h

theorem qNat_eq_absNorm_span (p : O) :
    qNat p = Ideal.absNorm (Ideal.span {p}) := by
  rw [Ideal.absNorm_span_singleton, algebraNorm_eq_coordinate_norm]
  unfold qNat
  apply Nat.cast_injective (R := ℤ)
  rw [Int.toNat_of_nonneg (qO_nonneg p),
    Int.natAbs_of_nonneg (qO_nonneg p)]

end

section

theorem prime_sixth_row_approx_ideal_norm
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι)
    (weight : O → ℂ) (p : O) (hp : p ≠ 0)
    (hprime : (Ideal.span {p} : Ideal O).IsMaximal)
    (D : ℕ)
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hcolnorm : ∀ n ∈ columns,
      Ideal.absNorm (Ideal.span {n}) ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1) :
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (p ^ 6))‖ ≤
      (64 * (D / Ideal.absNorm (Ideal.span {p}) + 1) : ℕ) := by
  have hcol : ∀ n ∈ columns, ShortDraftLatticeCount.qNat n ≤ D := by
    intro n hn
    rw [qNat_eq_absNorm_span]
    exact hcolnorm n hn
  simpa only [qNat_eq_absNorm_span] using
    (prime_sixth_row_approx_maximal P hgood columns support weight p hp
      hprime D hsupport hcol hweight)

theorem sixth_power_eq_implies_same_prime_ideal
    (p q : O)
    (hp : (Ideal.span {p} : Ideal O).IsMaximal)
    (hq : (Ideal.span {q} : Ideal O).IsMaximal)
    (h : p ^ 6 = q ^ 6) :
    (Ideal.span {p} : Ideal O) = Ideal.span {q} := by
  have hq6 : q ^ 6 ∈ Ideal.span {q} :=
    Ideal.mem_span_singleton.mpr (dvd_pow_self q (by decide))
  have hp6 : p ^ 6 ∈ Ideal.span {q} := by rw [h]; exact hq6
  have hpmem : p ∈ Ideal.span {q} :=
    hq.isPrime.mem_of_pow_mem 6 hp6
  have hle : (Ideal.span {p} : Ideal O) ≤ Ideal.span {q} :=
    (Ideal.span_singleton_le_iff_mem _).mpr hpmem
  exact hp.eq_of_le hq.ne_top hle

theorem sixth_power_rows_injective
    {ι : Type*} (S : Finset ι) (P : ι → Ideal O) (p : ι → O)
    (hprime : ∀ i ∈ S, (P i).IsMaximal)
    (hgen : ∀ i ∈ S, P i = Ideal.span {p i})
    (hinj : Set.InjOn P (S : Set ι)) :
    Set.InjOn (fun i => p i ^ 6) (S : Set ι) := by
  intro i hi j hj heq
  have hsame : Ideal.span {p i} = (Ideal.span {p j} : Ideal O) :=
    sixth_power_eq_implies_same_prime_ideal (p i) (p j)
      (hgen i hi ▸ hprime i hi)
      (hgen j hj ▸ hprime j hj) heq
  apply hinj hi hj
  rw [hgen i hi, hgen j hj]
  exact hsame

open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE

theorem rational_modulus_card (m : ℕ) (_hm : m ≠ 0) :
    Nat.card (O ⧸ Ideal.span {(m : O)}) = m ^ 2 := by
  have hnorm : Algebra.norm ℤ (m : O) = (m : ℤ) ^ 2 := by
    have h := Algebra.norm_algebraMap_of_basis
      EisensteinEmbedding.pb.basis (m : ℤ)
    simpa [EisensteinEmbedding.pb_dim] using h
  calc
    Nat.card (O ⧸ Ideal.span {(m : O)}) =
        Ideal.absNorm (Ideal.span {(m : O)}) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    _ = (Algebra.norm ℤ (m : O)).natAbs :=
      Ideal.absNorm_span_singleton (m : O)
    _ = m ^ 2 := by rw [hnorm]; simp

private theorem mk_eval_congr_mod (m : ℕ) (a b c d : ℤ)
    (ha : (a : ZMod m) = c) (hb : (b : ZMod m) = d) :
    Ideal.Quotient.mk (Ideal.span {(m : O)})
        (ActualEisensteinCoordinates.eval a b) =
      Ideal.Quotient.mk (Ideal.span {(m : O)})
        (ActualEisensteinCoordinates.eval c d) := by
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  have hda : (m : ℤ) ∣ a - c :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub c a m).mp ha.symm
  have hdb : (m : ℤ) ∣ b - d :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub d b m).mp hb.symm
  obtain ⟨r, hr⟩ := hda
  obtain ⟨s, hs⟩ := hdb
  apply (Ideal.mem_span_singleton).mpr
  refine ⟨ActualEisensteinCoordinates.eval r s, ?_⟩
  dsimp [ActualEisensteinCoordinates.eval]
  rw [show a = c + m*r by omega, show b = d + m*s by omega]
  push_cast
  ring

noncomputable def rationalCoordMap (m : ℕ) :
    ZMod m × ZMod m → (O ⧸ Ideal.span {(m : O)}) :=
  fun ab => Ideal.Quotient.mk (Ideal.span {(m : O)})
    (ActualEisensteinCoordinates.eval (ZMod.cast ab.1) (ZMod.cast ab.2))

theorem rationalCoordMap_surjective (m : ℕ) :
    Function.Surjective (rationalCoordMap m) := by
  intro x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a, b, hab⟩ := ActualEisensteinCoordinates.exists_coordinates z
  refine ⟨((a : ZMod m), (b : ZMod m)), ?_⟩
  change Ideal.Quotient.mk (Ideal.span {(m : O)})
      (ActualEisensteinCoordinates.eval (ZMod.cast (a : ZMod m))
        (ZMod.cast (b : ZMod m))) = _
  rw [hab]
  apply mk_eval_congr_mod
  · exact ZMod.intCast_zmod_cast _
  · exact ZMod.intCast_zmod_cast _

noncomputable def rationalCoordEquiv (m : ℕ) (hm : m ≠ 0) :
    ZMod m × ZMod m ≃ (O ⧸ Ideal.span {(m : O)}) := by
  letI : NeZero m := ⟨hm⟩
  letI : Finite (O ⧸ Ideal.span {(m : O)}) :=
    finite_quotient_span (by exact_mod_cast hm)
  letI : Fintype (O ⧸ Ideal.span {(m : O)}) := Fintype.ofFinite _
  refine Equiv.ofBijective (rationalCoordMap m) ?_
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  constructor
  · exact rationalCoordMap_surjective m
  · have hq : Fintype.card (O ⧸ Ideal.span {(m : O)}) = m ^ 2 := by
      simpa only [Nat.card_eq_fintype_card] using rational_modulus_card m hm
    simp [hq, Fintype.card_prod, sq]

theorem breveE_rational_trace (m : ℕ) [NeZero m] (a b : ℤ) :
    ShortDraftTrace.breveE
      ((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / m) =
      (ZMod.stdAddChar (N := m)) (b : ZMod m) := by
  have htrace := ShortDraftTrace.trace_div_lam omega3 omega3_sq
    ShortDraftTrace.omega_conj a b
  have hconj : ∀ z : ℂ, star (z / m) = star z / m := by
    intro z
    simp
  change Complex.exp (2 * Real.pi * Complex.I *
    (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / m) +
      star (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / m)))) = _
  rw [hconj]
  have hL : ((a : ℂ) + (b : ℂ) * omega3) / eisLam +
      star (((a : ℂ) + (b : ℂ) * omega3) / eisLam) = (b : ℂ) := by
    simpa only [eisLam, Complex.star_def] using htrace
  have harg : 2 * Real.pi * Complex.I *
      (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / m) +
        (star (((a : ℂ) + (b : ℂ) * omega3) / eisLam)) / m) =
      2 * Real.pi * Complex.I * (b : ℂ) / m := by
    rw [← add_div, hL]
    ring
  rw [harg, ZMod.stdAddChar_coe]

theorem eisEmbedding_eval (a b : ℤ) :
    eisEmbedding (ActualEisensteinCoordinates.eval a b) =
      (a : ℂ) + (b : ℂ) * omega3 := by
  have hgen : ActualEisensteinCoordinates.omega =
      EisensteinEmbedding.pb.gen := by
    rw [← ActualEisensteinCoordinates.pb_gen]
    rfl
  rw [ActualEisensteinCoordinates.eval, hgen]
  change EisensteinEmbedding.embedding omega3 omega3_sq
    (a + b * EisensteinEmbedding.pb.gen : O) = _
  exact EisensteinEmbedding.embedding_apply_ab omega3 omega3_sq a b

theorem rationalCoordEquiv_apply (m : ℕ) (hm : m ≠ 0)
    (a b : ZMod m) :
    rationalCoordEquiv m hm (a,b) =
      Ideal.Quotient.mk (Ideal.span {(m : O)})
        (ActualEisensteinCoordinates.eval (ZMod.cast a) (ZMod.cast b)) := rfl

theorem rational_quadratic_phase (m : ℕ) (hm : m ≠ 0)
    (a b : ZMod m) :
    letI : NeZero m := ⟨hm⟩
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      breveE_period_coordinates (m : O) (by exact_mod_cast hm)
    ψ ((rationalCoordEquiv m hm (a,b)) ^ 2) =
      ZMod.stdAddChar (2*a*b - b^2) := by
  let : NeZero m := ⟨hm⟩
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    breveE_period_coordinates (m : O) (by exact_mod_cast hm)
  let A : ℤ := ZMod.cast a
  let B : ℤ := ZMod.cast b
  change ShortDraftTrace.breveE
    (eisEmbedding (ActualEisensteinCoordinates.eval (ZMod.cast a) (ZMod.cast b) ^ 2) /
      (eisEmbedding (m : O) * eisLam)) = _
  rw [pow_two, ActualEisensteinCoordinates.eval_mul]
  rw [eisEmbedding_eval, map_natCast]
  change ShortDraftTrace.breveE
    ((((A*A-B*B : ℤ) : ℂ) + ((A*B+B*A-B*B : ℤ) : ℂ) * omega3) /
      ((m : ℂ) * eisLam)) = _
  have hdiv (X : ℂ) : X / ((m : ℂ) * eisLam) = (X / eisLam) / m := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hdiv, breveE_rational_trace]
  congr 1
  dsimp [A, B]
  push_cast
  ring

theorem rational_quadratic_character_sum (m : ℕ) [NeZero m]
    (hodd : Odd m) :
    (∑ a : ZMod m, ∑ b : ZMod m,
      ZMod.stdAddChar (2*a*b-b^2)) = (m : ℂ) := by
  let ψ : AddChar (ZMod m) ℂ := ZMod.stdAddChar
  have htwo : IsUnit (2 : ZMod m) :=
    (ZMod.isUnit_iff_coprime 2 m).mpr (Nat.coprime_two_left.mpr hodd)
  have hmulzero (b : ZMod m) : (2 : ZMod m) * b = 0 ↔ b = 0 := by
    simpa only [mul_zero] using
      (htwo.mul_right_inj (b := b) (c := (0 : ZMod m)))
  calc
    (∑ a : ZMod m, ∑ b : ZMod m,
      ZMod.stdAddChar (2*a*b-b^2)) =
        ∑ b : ZMod m, ∑ a : ZMod m, ψ (2*a*b-b^2) := by
      rw [Finset.sum_comm]
    _ = ∑ b : ZMod m, (if b = 0 then (m : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro b hb
      calc
        (∑ a : ZMod m, ψ (2*a*b-b^2)) =
            (∑ a : ZMod m, ψ (a*(2*b))) * ψ (-b^2) := by
          simp_rw [show ∀ a : ZMod m, 2*a*b-b^2 = a*(2*b)+(-b^2) from
            fun a => by ring, map_add_eq_mul]
          rw [Finset.sum_mul]
        _ = (if (2 : ZMod m)*b = 0 then (m : ℂ) else 0) * ψ (-b^2) := by
          rw [AddChar.sum_mulShift (2*b) (ZMod.isPrimitive_stdAddChar m)]
          simp
        _ = if b = 0 then (m : ℂ) else 0 := by
          simp only [hmulzero]
          split_ifs with h
          · subst b
            simp [ψ]
          · simp
    _ = (m : ℂ) := by simp

noncomputable def quadraticGammaRational (m : ℕ) (hm : m ≠ 0) : ℂ := by
  letI : Finite (O ⧸ Ideal.span {(m : O)}) :=
    finite_quotient_span (by exact_mod_cast hm)
  letI : Fintype (O ⧸ Ideal.span {(m : O)}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates
    (m : O) (by exact_mod_cast hm)
  exact (∑ x : O ⧸ Ideal.span {(m : O)}, ψ (x ^ 2)) /
    (‖eisEmbedding (m : O)‖ : ℂ)

theorem quadraticGammaRational_eq_one (m : ℕ) (hm : m ≠ 0)
    (hodd : Odd m) : quadraticGammaRational m hm = 1 := by
  let : NeZero m := ⟨hm⟩
  let : Finite (O ⧸ Ideal.span {(m : O)}) :=
    finite_quotient_span (by exact_mod_cast hm)
  let : Fintype (O ⧸ Ideal.span {(m : O)}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates
    (m : O) (by exact_mod_cast hm)
  have hsum : (∑ x : O ⧸ Ideal.span {(m : O)}, ψ (x ^ 2)) = (m : ℂ) := by
    have hreindex := ((rationalCoordEquiv m hm).sum_comp
      (fun x : O ⧸ Ideal.span {(m : O)} => ψ (x ^ 2))).symm
    rw [hreindex, Fintype.sum_prod_type]
    calc
      (∑ x : ZMod m, ∑ y : ZMod m,
        ψ ((rationalCoordEquiv m hm) (x, y) ^ 2)) =
        ∑ x : ZMod m, ∑ y : ZMod m,
          ZMod.stdAddChar (2*x*y-y^2) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        exact rational_quadratic_phase m hm x y
      _ = (m : ℂ) := rational_quadratic_character_sum m hodd
  have hnorm : ‖eisEmbedding (m : O)‖ = m := by simp
  unfold quadraticGammaRational
  change (∑ x : O ⧸ Ideal.span {(m : O)}, ψ (x ^ 2)) /
    (‖eisEmbedding (m : O)‖ : ℂ) = 1
  rw [hsum, hnorm]
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  exact div_self hmC

theorem breveGaussianFourTerms_rational_odd (m : ℕ) (hodd : Odd m) :
    breveGaussianFourTerms (m : ℤ) 0 = 1 := by
  have hsq : (Complex.I ^ m) ^ 2 = -1 := by
    calc
      (Complex.I ^ m) ^ 2 = Complex.I ^ (m * 2) := by rw [pow_mul]
      _ = Complex.I ^ (2 * m) := by rw [mul_comm]
      _ = (Complex.I ^ 2) ^ m := by rw [pow_mul]
      _ = (-1 : ℂ) ^ m := by rw [Complex.I_sq]
      _ = -1 := hodd.neg_one_pow
  have hinv : (Complex.I ^ m)⁻¹ = -(Complex.I ^ m) := by
    apply inv_eq_of_mul_eq_one_right
    calc
      (Complex.I ^ m) * -(Complex.I ^ m) = -((Complex.I ^ m) ^ 2) := by ring
      _ = 1 := by rw [hsq]; ring
  rw [breveGaussianFourTerms_formula]
  simp only [zero_sub,  zpow_neg, zpow_zero, inv_one, zpow_natCast]
  rw [hinv]
  ring

theorem quadraticGammaRational_eq_fourTerms (m : ℕ) (hm : m ≠ 0)
    (hodd : Odd m) :
    quadraticGammaRational m hm = breveGaussianFourTerms (m : ℤ) 0 := by
  rw [quadraticGammaRational_eq_one m hm hodd,
    breveGaussianFourTerms_rational_odd m hodd]

end

section

theorem cubic_roots_reduce_injective (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) {x y : O}
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hxy : Ideal.Quotient.mk P x = Ideal.Quotient.mk P y) : x = y := by
  obtain ⟨i, hi, rfl⟩ := omega_primitive.eq_pow_of_pow_eq_one hx
  obtain ⟨j, hj, rfl⟩ := omega_primitive.eq_pow_of_pow_eq_one hy
  have hij : i = j := by
    apply (omega_reduced_primitive P hgood).pow_inj hi hj
    simpa only [map_pow] using hxy
  rw [hij]

theorem cubicChar_omega (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    cubicChar P hgood (Ideal.Quotient.mk P omega) =
      omega ^ ((Nat.card (O ⧸ P) - 1) / 3) := by
  let χ := cubicChar P hgood
  have hx : (χ (Ideal.Quotient.mk P omega)) ^ 3 = 1 := by
    rw [← χ.pow_apply' (by decide), cubicChar_pow_three P hgood]
    exact MulChar.one_apply ((omega_reduced_primitive P hgood).isUnit (by decide))
  have hy : (omega ^ ((Nat.card (O ⧸ P) - 1) / 3)) ^ 3 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, omega_primitive.pow_eq_one, one_pow]
  apply cubic_roots_reduce_injective P hgood hx hy
  rw [map_pow]
  exact cubicChar_reduce P hgood (Ideal.Quotient.mk P omega)

theorem cubicChar_omega_eq_one_of_card_mod_nine
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (hcard : Nat.card (O ⧸ P) % 9 = 1) :
    cubicChar P hgood (Ideal.Quotient.mk P omega) = 1 := by
  rw [cubicChar_omega P hgood]
  apply (omega_primitive.pow_eq_one_iff_dvd _).mpr
  omega

theorem cubicChar_omega_eq_omega_of_card_mod_nine
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (hcard : Nat.card (O ⧸ P) % 9 = 4) :
    cubicChar P hgood (Ideal.Quotient.mk P omega) = omega := by
  rw [cubicChar_omega P hgood]
  calc
    omega ^ ((Nat.card (O ⧸ P) - 1) / 3) = omega ^ 1 := by
      apply ((omega_primitive.isOfFinOrder (by decide)).pow_inj_mod).mpr
      rw [← omega_primitive.eq_orderOf]
      omega
    _ = omega := pow_one omega

theorem cubicChar_omega_eq_omega_sq_of_card_mod_nine
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (hcard : Nat.card (O ⧸ P) % 9 = 7) :
    cubicChar P hgood (Ideal.Quotient.mk P omega) = omega ^ 2 := by
  rw [cubicChar_omega P hgood]
  apply ((omega_primitive.isOfFinOrder (by decide)).pow_inj_mod).mpr
  rw [← omega_primitive.eq_orderOf]
  omega

theorem cubicChar_omega_sq (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    cubicChar P hgood (Ideal.Quotient.mk P (omega ^ 2)) =
      omega ^ (2 * ((Nat.card (O ⧸ P) - 1) / 3)) := by
  rw [map_pow, map_pow, cubicChar_omega P hgood]
  ring

theorem finiteSquarefreeRow_one
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) :
    finiteSquarefreeRow P hgood S 1 = 1 := by
  classical
  unfold finiteSquarefreeRow
  apply Finset.prod_eq_one
  intro i hi
  simp

theorem finite_actual_prime_extraction
    {ι β : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι) (weight : O → ℂ)
    (selected : Finset β) (p : β → O) (rows : Finset O)
    (D : ℕ) (ε : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hprime : ∀ i ∈ selected, (Ideal.span {p i} : Ideal O).IsMaximal)
    (hinj : Set.InjOn (fun i => (Ideal.span {p i} : Ideal O)) (selected : Set β))
    (hrows : selected.image (fun i => p i ^ 6) ⊆ rows)
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hcolnorm : ∀ n ∈ columns, Ideal.absNorm (Ideal.span {n}) ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1)
    (hrowbound : ∀ i ∈ selected,
      ((64 * (D / Ideal.absNorm (Ideal.span {p i}) + 1) : ℕ) : ℝ) ≤
        (D : ℝ) ^ (49 / 60 : ℝ))
    (hcount : (D : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤ (selected.card : ℝ))
    (hmean :
      (∑ u ∈ rows,
        ‖∑ n ∈ columns,
          weight n * finiteSquarefreeRow P hgood (support n) u‖ ^ 2) ≤
        (D : ℝ) ^ ((21 / 10 : ℝ) + ε)) :
    ‖∑ n ∈ columns, weight n‖ ≤
      2 * (D : ℝ) ^ ((23 / 24 : ℝ) + ε) := by
  classical
  let A : O → ℂ := fun u =>
    ∑ n ∈ columns, weight n * finiteSquarefreeRow P hgood (support n) u
  have hone : A 1 = ∑ n ∈ columns, weight n := by
    dsimp [A]
    apply Finset.sum_congr rfl
    intro n hn
    rw [finiteSquarefreeRow_one]
    ring
  have hinjRows : Set.InjOn (fun i => p i ^ 6) (selected : Set β) := by
    apply sixth_power_rows_injective selected
      (fun i => (Ideal.span {p i} : Ideal O)) p
    · exact hprime
    · intro i hi; rfl
    · exact hinj
  have happrox : ∀ i ∈ selected,
      ‖A 1 - A (p i ^ 6)‖ ≤ (D : ℝ) ^ (49 / 60 : ℝ) := by
    intro i hi
    rw [hone]
    change ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (p i ^ 6))‖ ≤ _
    exact (prime_sixth_row_approx_ideal_norm P hgood columns support
      weight (p i) (hp i hi) (hprime i hi) D hsupport hcolnorm hweight).trans
      (hrowbound i hi)
  have hmean' : (∑ u ∈ rows, ‖A u‖ ^ 2) ≤
      (D : ℝ) ^ ((21 / 10 : ℝ) + ε) := hmean
  have hbound := PowerExtraction.from_finite_sixth_power_rows
    rows selected (fun i => p i ^ 6) A 1 (D : ℝ) ε
    (by exact_mod_cast hD) hε hrows hinjRows happrox hcount hmean'
  simpa only [hone] using hbound

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem breveE_int_trace_div (q u v : ℤ) (_hq : q ≠ 0) :
    ShortDraftTrace.breveE
      ((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / q) =
      Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) / q) := by
  have htrace := ShortDraftTrace.trace_div_lam omega3 omega3_sq
    ShortDraftTrace.omega_conj u v
  have hL : ((u : ℂ) + (v : ℂ) * omega3) / eisLam +
      star (((u : ℂ) + (v : ℂ) * omega3) / eisLam) = (v : ℂ) := by
    simpa only [eisLam, Complex.star_def] using htrace
  change Complex.exp (2 * Real.pi * Complex.I *
    (((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / q) +
      star (((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / q)))) = _
  rw [show star (((u : ℂ) + (v : ℂ) * omega3) / eisLam / q) =
      star (((u : ℂ) + (v : ℂ) * omega3) / eisLam) / q by simp]
  rw [← add_div, hL]
  congr 1
  ring

theorem breveE_quadratic_coordinate (a b x y : ℤ)
    (hq : a*a - a*b + b*b ≠ 0) :
    let c : ℂ := (a : ℂ) + (b : ℂ) * omega3
    let z : ℂ := (x : ℂ) + (y : ℂ) * omega3
    ShortDraftTrace.breveE (z ^ 2 / (c * eisLam)) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((-b*x*x + 2*a*x*y + (b-a)*y*y : ℤ) : ℂ) /
        ((a*a-a*b+b*b : ℤ) : ℂ)) := by
  let c : ℂ := (a : ℂ) + (b : ℂ) * omega3
  let z : ℂ := (x : ℂ) + (y : ℂ) * omega3
  let cb : ℂ := ((a-b : ℤ) : ℂ) - (b : ℂ) * omega3
  let q : ℤ := a*a-a*b+b*b
  let U : ℤ := (x*x-y*y)*(a-b)+b*(2*x*y-y*y)
  let V : ℤ := -b*x*x+2*a*x*y+(b-a)*y*y
  have hnorm : c * cb = (q : ℂ) := by
    dsimp [c, cb, q]
    push_cast
    linear_combination -(b : ℂ)^2 * omega3_sq
  have hnum : z ^ 2 * cb = (U : ℂ) + (V : ℂ) * omega3 := by
    dsimp [z, cb, U, V]
    push_cast
    linear_combination
      ((y : ℂ)^2 * ((a : ℂ)-(b : ℂ)-(b : ℂ)*omega3) -
        (b : ℂ) * (2*(x : ℂ)*(y : ℂ)-(y : ℂ)^2)) * omega3_sq
  have hqC : (q : ℂ) ≠ 0 := by
    dsimp [q]
    exact_mod_cast hq
  have hc : c ≠ 0 := by
    intro hc
    apply hqC
    rw [← hnorm, hc, zero_mul]
  have hcb : cb ≠ 0 := by
    intro hcb
    apply hqC
    rw [← hnorm, hcb, mul_zero]
  have hdiv : z ^ 2 / (c * eisLam) =
      ((z ^ 2 * cb) / eisLam) / q := by
    rw [← hnorm]
    field_simp [hc, hcb, eisLam_ne_zero]
  change ShortDraftTrace.breveE (z ^ 2 / (c * eisLam)) = _
  rw [hdiv, hnum, breveE_int_trace_div q U V (by simpa [q] using hq)]

end

theorem cubicChar_traceLambda_relation (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    cubicChar P hgood (Ideal.Quotient.mk P traceLambda) =
      omega ^ ((Nat.card (O ⧸ P) - 1) / 3) *
        cubicChar P hgood (Ideal.Quotient.mk P (1 - omega)) := by
  have ht : traceLambda = omega * (1 - omega) := by
    rw [traceLambda_eq_unit_mul_lambda]
    dsimp [lambda]
    ring
  calc
    cubicChar P hgood (Ideal.Quotient.mk P traceLambda) =
        cubicChar P hgood (Ideal.Quotient.mk P (omega * (1 - omega))) := by rw [ht]
    _ = cubicChar P hgood (Ideal.Quotient.mk P omega) *
        cubicChar P hgood (Ideal.Quotient.mk P (1 - omega)) := by rw [map_mul, map_mul]
    _ = _ := by rw [cubicChar_omega P hgood]

theorem cubicChar_lambda_eq_one_sub_omega (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    cubicChar P hgood (Ideal.Quotient.mk P lambda) =
      cubicChar P hgood (Ideal.Quotient.mk P (1 - omega)) := by
  have hl : lambda = (-1 : O) * (1 - omega) := by
    dsimp [lambda]
    ring
  calc
    cubicChar P hgood (Ideal.Quotient.mk P lambda) =
        cubicChar P hgood (Ideal.Quotient.mk P ((-1 : O) * (1 - omega))) := by rw [hl]
    _ = cubicChar P hgood (-1) *
        cubicChar P hgood (Ideal.Quotient.mk P (1 - omega)) := by rw [map_mul, map_mul, map_neg, map_one]
    _ = _ := by rw [A3_cubicChar_neg_one P hgood, one_mul]

theorem cubicChar_traceLambda_eq_lambda_of_card_mod_nine
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (hcard : Nat.card (O ⧸ P) % 9 = 1) :
    cubicChar P hgood (Ideal.Quotient.mk P traceLambda) =
      cubicChar P hgood (Ideal.Quotient.mk P lambda) := by
  have hpow : omega ^ ((Nat.card (O ⧸ P) - 1) / 3) = 1 := by
    rw [← cubicChar_omega P hgood]
    exact cubicChar_omega_eq_one_of_card_mod_nine P hgood hcard
  rw [cubicChar_traceLambda_relation P hgood, hpow, one_mul,
    cubicChar_lambda_eq_one_sub_omega P hgood]

end ActualEisensteinCubic

end

end OAI
end OAIOriginalModule0046

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.QuadraticNormalization
Source SHA256: 9c53a3ed0355834facdea096e2e402ad83893a7688e603f4f3f572a1f3f39c62
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0047


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

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE

noncomputable def quadraticGammaO (c : O) (hc : c ≠ 0) : ℂ := by
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc
  exact (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) /
    (‖eisEmbedding c‖ : ℂ)

theorem quadraticGammaO_traceLambda :
    quadraticGammaO traceLambda traceLambda_ne_zero =
      quadraticGammaTraceLambda := by rfl

theorem quadraticGammaO_negTraceLambda :
    quadraticGammaO (-traceLambda) (neg_ne_zero.mpr traceLambda_ne_zero) =
      quadraticGammaNegTraceLambda := by rfl

theorem quadraticGammaO_rational (m : ℕ) (hm : m ≠ 0)
    (hc : (m : O) ≠ 0) :
    quadraticGammaO (m : O) hc = quadraticGammaRational m hm := by rfl

theorem quadraticGammaO_rational_odd (m : ℕ) (hm : m ≠ 0)
    (hodd : Odd m) (hc : (m : O) ≠ 0) :
    quadraticGammaO (m : O) hc = breveGaussianFourTerms (m : ℤ) 0 := by
  rw [quadraticGammaO_rational m hm hc,
    quadraticGammaRational_eq_fourTerms m hm hodd]

end ActualEisensteinCubic

namespace PowerExtraction

theorem from_mean_square_and_prime_rows_with_constant
    (D ε J A C : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hJ : D ^ ((11 / 60 : ℝ) - ε) ≤ J)
    (hmean : J * A ^ 2 ≤
      2 * D ^ ((21 / 10 : ℝ) + ε) +
      2 * J * C ^ 2 * D ^ (49 / 30 : ℝ)) :
    A ≤ 2 * C * D ^ ((23 / 24 : ℝ) + ε) := by
  let E : ℝ := (23 / 24 : ℝ) + ε
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hJpos : 0 < J := lt_of_lt_of_le (Real.rpow_pos_of_pos hDpos _) hJ
  have hpow :
      D ^ ((21 / 10 : ℝ) + ε) ≤
        J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      D ^ ((21 / 10 : ℝ) + ε) =
          D ^ ((11 / 60 : ℝ) - ε) *
            D ^ ((23 / 12 : ℝ) + 2 * ε) := by
            rw [← Real.rpow_add hDpos]
            congr 1
            ring
      _ ≤ J * D ^ ((23 / 12 : ℝ) + 2 * ε) :=
          mul_le_mul_of_nonneg_right hJ (by positivity)
  have herr : D ^ (49 / 30 : ℝ) ≤
      D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    apply Real.rpow_le_rpow_of_exponent_le hD
    linarith
  have hC2 : 1 ≤ C ^ 2 := by nlinarith
  have hP : 0 ≤ J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by positivity
  have hsq : A ^ 2 ≤
      4 * C ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    have hmain : J * A ^ 2 ≤
        4 * J * C ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
      calc
        J * A ^ 2 ≤
            2 * D ^ ((21 / 10 : ℝ) + ε) +
            2 * J * C ^ 2 * D ^ (49 / 30 : ℝ) := hmean
        _ ≤ 2 * (J * D ^ ((23 / 12 : ℝ) + 2 * ε)) +
            2 * J * C ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
              gcongr
        _ ≤ 4 * J * C ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hC2) hP]
    nlinarith
  have hexp : (23 / 12 : ℝ) + 2 * ε = E * 2 := by
    dsimp [E]
    ring
  have hpow2 : (D ^ E) ^ 2 = D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      (D ^ E) ^ 2 = D ^ (E * 2) :=
        (Real.rpow_mul_natCast hDpos.le E 2).symm
      _ = D ^ ((23 / 12 : ℝ) + 2 * ε) := by rw [hexp]
  have htwo : 0 ≤ 2 * C * D ^ E := by positivity
  apply (sq_le_sq₀ hA htwo).mp
  rw [mul_pow, mul_pow, hpow2]
  nlinarith

theorem from_finite_sixth_power_rows_with_constant
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (rows : Finset α) (primes : Finset β) (row : β → α)
    (A : α → ℂ) (untwisted : α) (D ε C : ℝ)
    (hD : 1 ≤ D) (hε : 0 ≤ ε) (hC : 1 ≤ C)
    (hrows : primes.image row ⊆ rows)
    (hinj : Set.InjOn row (primes : Set β))
    (happrox : ∀ p ∈ primes,
      ‖A untwisted - A (row p)‖ ≤ C * D ^ (49 / 60 : ℝ))
    (hcount : D ^ ((11 / 60 : ℝ) - ε) ≤ (primes.card : ℝ))
    (hmean : (∑ u ∈ rows, ‖A u‖ ^ 2) ≤
      D ^ ((21 / 10 : ℝ) + ε)) :
    ‖A untwisted‖ ≤ 2 * C * D ^ ((23 / 24 : ℝ) + ε) := by
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hextract := ShortDraft.complex_row_extraction rows primes row A untwisted
    (C * D ^ (49 / 60 : ℝ)) (D ^ ((21 / 10 : ℝ) + ε))
    (by positivity) hrows hinj happrox hmean
  have herror : (C * D ^ (49 / 60 : ℝ)) ^ 2 =
      C ^ 2 * D ^ (49 / 30 : ℝ) := by
    rw [mul_pow]
    congr 1
    calc
      (D ^ (49 / 60 : ℝ)) ^ 2 = D ^ ((49 / 60 : ℝ) * 2) :=
        (Real.rpow_mul_natCast hDpos.le _ 2).symm
      _ = D ^ (49 / 30 : ℝ) := by congr 1; norm_num
  rw [herror] at hextract
  exact from_mean_square_and_prime_rows_with_constant D ε
    (primes.card : ℝ) ‖A untwisted‖ C hD hε (norm_nonneg _) hC
    hcount (by simpa only [mul_assoc] using hextract)

end PowerExtraction

namespace ActualEisensteinCubic

theorem finite_actual_prime_extraction_with_constant
    {ι β : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι) (weight : O → ℂ)
    (selected : Finset β) (p : β → O) (rows : Finset O)
    (D : ℕ) (ε C : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hC : 1 ≤ C)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hprime : ∀ i ∈ selected, (Ideal.span {p i} : Ideal O).IsMaximal)
    (hinj : Set.InjOn (fun i => (Ideal.span {p i} : Ideal O)) (selected : Set β))
    (hrows : selected.image (fun i => p i ^ 6) ⊆ rows)
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hcolnorm : ∀ n ∈ columns, Ideal.absNorm (Ideal.span {n}) ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1)
    (hrowbound : ∀ i ∈ selected,
      ((64 * (D / Ideal.absNorm (Ideal.span {p i}) + 1) : ℕ) : ℝ) ≤
        C * (D : ℝ) ^ (49 / 60 : ℝ))
    (hcount : (D : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤ (selected.card : ℝ))
    (hmean :
      (∑ u ∈ rows,
        ‖∑ n ∈ columns,
          weight n * finiteSquarefreeRow P hgood (support n) u‖ ^ 2) ≤
        (D : ℝ) ^ ((21 / 10 : ℝ) + ε)) :
    ‖∑ n ∈ columns, weight n‖ ≤
      2 * C * (D : ℝ) ^ ((23 / 24 : ℝ) + ε) := by
  classical
  let A : O → ℂ := fun u =>
    ∑ n ∈ columns, weight n * finiteSquarefreeRow P hgood (support n) u
  have hone : A 1 = ∑ n ∈ columns, weight n := by
    dsimp [A]
    apply Finset.sum_congr rfl
    intro n hn
    rw [finiteSquarefreeRow_one]
    ring
  have hinjRows : Set.InjOn (fun i => p i ^ 6) (selected : Set β) := by
    apply sixth_power_rows_injective selected
      (fun i => (Ideal.span {p i} : Ideal O)) p
    · exact hprime
    · intro i hi; rfl
    · exact hinj
  have happrox : ∀ i ∈ selected,
      ‖A 1 - A (p i ^ 6)‖ ≤ C * (D : ℝ) ^ (49 / 60 : ℝ) := by
    intro i hi
    rw [hone]
    change ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (p i ^ 6))‖ ≤ _
    exact (prime_sixth_row_approx_ideal_norm P hgood columns support
      weight (p i) (hp i hi) (hprime i hi) D hsupport hcolnorm hweight).trans
      (hrowbound i hi)
  have hmean' : (∑ u ∈ rows, ‖A u‖ ^ 2) ≤
      (D : ℝ) ^ ((21 / 10 : ℝ) + ε) := hmean
  have hbound := PowerExtraction.from_finite_sixth_power_rows_with_constant
    rows selected (fun i => p i ^ 6) A 1 (D : ℝ) ε C
    (by exact_mod_cast hD) hε hC hrows hinjRows happrox hcount hmean'
  simpa only [hone] using hbound

end ActualEisensteinCubic

namespace PowerExtraction

theorem dyadic_prime_error_bound (D N : ℕ) (hD : 1 ≤ D)
    (hN : (D : ℝ) ^ (11 / 60 : ℝ) / 2 ≤ (N : ℝ)) :
    ((64 * (D / N + 1) : ℕ) : ℝ) ≤
      192 * (D : ℝ) ^ (49 / 60 : ℝ) := by
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  have hYpos : 0 < (D : ℝ) ^ (11 / 60 : ℝ) :=
    Real.rpow_pos_of_pos hDpos _
  have hNpos : (0 : ℝ) < N := by linarith
  have hpow :
      (D : ℝ) ^ (49 / 60 : ℝ) *
        (D : ℝ) ^ (11 / 60 : ℝ) = D := by
    rw [← Real.rpow_add hDpos]
    norm_num
  have hfrac : (D : ℝ) / N ≤
      2 * (D : ℝ) ^ (49 / 60 : ℝ) := by
    apply (div_le_iff₀ hNpos).mpr
    calc
      (D : ℝ) =
          (D : ℝ) ^ (49 / 60 : ℝ) *
            (D : ℝ) ^ (11 / 60 : ℝ) := hpow.symm
      _ =
          (2 * (D : ℝ) ^ (49 / 60 : ℝ)) *
            ((D : ℝ) ^ (11 / 60 : ℝ) / 2) := by
              ring
      _ ≤ (2 * (D : ℝ) ^ (49 / 60 : ℝ)) * N :=
          mul_le_mul_of_nonneg_left hN (by positivity)
  have hcast : ((D / N : ℕ) : ℝ) ≤ (D : ℝ) / N :=
    Nat.cast_div_le
  have hone : (1 : ℝ) ≤ (D : ℝ) ^ (49 / 60 : ℝ) :=
    Real.one_le_rpow hDreal (by norm_num)
  have hnatcast : ((64 * (D / N + 1) : ℕ) : ℝ) =
      64 * (((D / N : ℕ) : ℝ) + 1) := by push_cast; ring
  rw [hnatcast]
  nlinarith

end PowerExtraction

namespace ActualEisensteinCubic

theorem cubicChar_unit_eq_one_of_card_mod_nine
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (hcard : Nat.card (O ⧸ P) % 9 = 1) (u : Oˣ) :
    cubicChar P hgood (Ideal.Quotient.mk P (u : O)) = 1 := by
  let ζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η : Oˣ := (ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η : O) = omega := rfl
  have hu : u ∈ ([1, -1, η, -η, η ^ 2, -η ^ 2] : List Oˣ) :=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  have hone : cubicChar P hgood (Ideal.Quotient.mk P omega) = 1 :=
    cubicChar_omega_eq_one_of_card_mod_nine P hgood hcard
  have hminus : cubicChar P hgood (-1 : O ⧸ P) = 1 :=
    A3_cubicChar_neg_one P hgood
  have hneg (x : O) :
      cubicChar P hgood (Ideal.Quotient.mk P (-x)) =
        cubicChar P hgood (Ideal.Quotient.mk P x) := by
    have hx : -x = (-1 : O) * x := by ring
    rw [hx, map_mul, map_mul, map_neg, map_one, hminus, one_mul]
  simp only [List.mem_cons] at hu
  rcases hu with h | h | h | h | h | h
  · rw [h]
    simp
  · rw [h]
    simpa only [Units.val_neg, Units.val_one, map_neg, map_one] using hminus
  · rw [h, hη]
    exact hone
  · rw [h, Units.val_neg, hneg, hη]
    exact hone
  · rw [h, Units.val_pow_eq_pow_val, hη, map_pow, map_pow, hone]
    norm_num
  · rcases h with h | h
    · rw [h, Units.val_neg, hneg, Units.val_pow_eq_pow_val, hη, map_pow, map_pow, hone]
      norm_num
    · simp at h

theorem cubicChar_omega_agree_of_card_mod_nine
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hP : lambda ∉ P) (hQ : lambda ∉ Q)
    (hcard : Nat.card (O ⧸ P) % 9 = Nat.card (O ⧸ Q) % 9) :
    cubicChar P hP (Ideal.Quotient.mk P omega) =
      cubicChar Q hQ (Ideal.Quotient.mk Q omega) := by
  rw [cubicChar_omega P hP, cubicChar_omega Q hQ]
  apply ((omega_primitive.isOfFinOrder (by decide)).pow_inj_mod).mpr
  rw [← omega_primitive.eq_orderOf]
  have hPpos : 0 < Nat.card (O ⧸ P) := Nat.card_pos
  have hQpos : 0 < Nat.card (O ⧸ Q) := Nat.card_pos
  omega

theorem cubicChar_units_agree_of_card_mod_nine
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hP : lambda ∉ P) (hQ : lambda ∉ Q)
    (hcard : Nat.card (O ⧸ P) % 9 = Nat.card (O ⧸ Q) % 9)
    (u : Oˣ) :
    cubicChar P hP (Ideal.Quotient.mk P (u : O)) =
      cubicChar Q hQ (Ideal.Quotient.mk Q (u : O)) := by
  let ζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η : Oˣ := (ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η : O) = omega := rfl
  have hu : u ∈ ([1, -1, η, -η, η ^ 2, -η ^ 2] : List Oˣ) :=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  have hω := cubicChar_omega_agree_of_card_mod_nine P Q hP hQ hcard
  have hnegP := A3_cubicChar_neg_one P hP
  have hnegQ := A3_cubicChar_neg_one Q hQ
  have hminus (R : Ideal O) [R.IsMaximal] (hR : lambda ∉ R) (x : O) :
      cubicChar R hR (Ideal.Quotient.mk R (-x)) =
        cubicChar R hR (Ideal.Quotient.mk R x) := by
    have hx : -x = (-1 : O) * x := by ring
    rw [hx, map_mul, map_mul, map_neg, map_one,
      A3_cubicChar_neg_one R hR, one_mul]
  simp only [List.mem_cons] at hu
  rcases hu with h | h | h | h | h | h
  · rw [h]
    simp
  · rw [h]
    simpa only [Units.val_neg, Units.val_one, map_neg, map_one] using
      hnegP.trans hnegQ.symm
  · rw [h, hη]
    exact hω
  · rw [h, Units.val_neg, hminus P hP, hminus Q hQ, hη]
    exact hω
  · rw [h, Units.val_pow_eq_pow_val, hη, map_pow, map_pow,
      map_pow, map_pow, hω]
  · rcases h with h | h
    · rw [h, Units.val_neg, hminus P hP, hminus Q hQ,
        Units.val_pow_eq_pow_val, hη, map_pow, map_pow, map_pow, map_pow, hω]
    · simp at h

open EisensteinEmbedding ConcreteTraceCRT Complex
theorem eisenstein_coord_norm_zero (a b : ℤ)
    (h : a*a-a*b+b*b = 0) : a = 0 ∧ b = 0 := by
  have hs : (a-b)^2 + a^2 + b^2 = 0 := by nlinarith [h]
  have ha : a^2 = 0 := by
    nlinarith [sq_nonneg (a-b), sq_nonneg b]
  have hb : b^2 = 0 := by
    nlinarith [sq_nonneg (a-b), sq_nonneg a]
  constructor <;> nlinarith

theorem quadraticTraceModChar_coordinate (a b x y : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let z : O := ActualEisensteinCoordinates.eval x y
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc)
      (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((-b*x*x + 2*a*x*y + (b-a)*y*y : ℤ) : ℂ) /
        ((a*a-a*b+b*b : ℤ) : ℂ)) := by
  have hq : a*a-a*b+b*b ≠ 0 := by
    intro h
    obtain ⟨ha,hb⟩ := eisenstein_coord_norm_zero a b h
    subst a
    subst b
    exact hc (by simp [ActualEisensteinCoordinates.eval])
  change ShortDraftTrace.breveE
    (eisEmbedding (ActualEisensteinCoordinates.eval x y ^ 2) /
      (eisEmbedding (ActualEisensteinCoordinates.eval a b) * eisLam)) = _
  rw [map_pow, eisEmbedding_eval, eisEmbedding_eval]
  exact breveE_quadratic_coordinate a b x y hq

end ActualEisensteinCubic

namespace GaussianAbelPartition

theorem tsum_by_finite_fibers {A B : Type*} [Fintype B]
    (q : A → B) (f : A → ℂ) (hf : Summable f) :
    (∑' a : A, f a) =
      ∑ b : B, ∑' a : (q ⁻¹' {b}), f a.1 := by
  have h := (hf.hasSum.tsum_fiberwise q).tsum_eq
  simpa only [tsum_fintype] using h.symm

theorem tsum_periodic_weighted_partition {A B : Type*} [Fintype B]
    (q : A → B) (P : B → ℂ) (W : A → ℂ)
    (hf : Summable (fun a => P (q a) * W a)) :
    (∑' a : A, P (q a) * W a) =
      ∑ b : B, P b * ∑' a : (q ⁻¹' {b}), W a.1 := by
  rw [tsum_by_finite_fibers q _ hf]
  apply Finset.sum_congr rfl
  intro b hb
  calc
    (∑' a : (q ⁻¹' {b}), P (q a.1) * W a.1) =
        ∑' a : (q ⁻¹' {b}), P b * W a.1 := by
      apply tsum_congr
      intro a
      have ha : q a.1 = b := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using a.property
      rw [ha]
    _ = P b * ∑' a : (q ⁻¹' {b}), W a.1 := tsum_mul_left

open ConcreteTraceCRT ConcreteBreveE ActualEisensteinCubic

theorem actual_quadratic_gaussian_partition (c : O) (hc : c ≠ 0)
    (W : O → ℂ)
    (hsum : Summable (fun z : O =>
      (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
        ((Ideal.Quotient.mk (Ideal.span {c}) z) ^ 2) * W z)) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O,
      (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
        ((Ideal.Quotient.mk (Ideal.span {c}) z) ^ 2) * W z) =
      ∑ r : O ⧸ Ideal.span {c},
        (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
          (r ^ 2) *
          ∑' z : ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}), W z.1 := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  exact tsum_periodic_weighted_partition
    (Ideal.Quotient.mk (Ideal.span {c}))
    (fun r => (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
      (r ^ 2)) W hsum

end GaussianAbelPartition

namespace ActualEisensteinCubic

theorem finite_actual_prime_extraction_dyadic
    {ι β : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι) (weight : O → ℂ)
    (selected : Finset β) (p : β → O) (rows : Finset O)
    (D : ℕ) (ε : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hprime : ∀ i ∈ selected, (Ideal.span {p i} : Ideal O).IsMaximal)
    (hinj : Set.InjOn (fun i => (Ideal.span {p i} : Ideal O)) (selected : Set β))
    (hrows : selected.image (fun i => p i ^ 6) ⊆ rows)
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hcolnorm : ∀ n ∈ columns, Ideal.absNorm (Ideal.span {n}) ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1)
    (hnormlower : ∀ i ∈ selected,
      (D : ℝ) ^ (11 / 60 : ℝ) / 2 ≤
        (Ideal.absNorm (Ideal.span {p i}) : ℝ))
    (hcount : (D : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤ (selected.card : ℝ))
    (hmean :
      (∑ u ∈ rows,
        ‖∑ n ∈ columns,
          weight n * finiteSquarefreeRow P hgood (support n) u‖ ^ 2) ≤
        (D : ℝ) ^ ((21 / 10 : ℝ) + ε)) :
    ‖∑ n ∈ columns, weight n‖ ≤
      384 * (D : ℝ) ^ ((23 / 24 : ℝ) + ε) := by
  have hbound := finite_actual_prime_extraction_with_constant P hgood
    columns support weight selected p rows D ε 192 hD hε (by norm_num)
    hp hprime hinj hrows hsupport hcolnorm hweight
    (by
      intro i hi
      exact PowerExtraction.dyadic_prime_error_bound D
        (Ideal.absNorm (Ideal.span {p i})) hD (hnormlower i hi))
    hcount hmean
  simpa only [show (2 : ℝ) * 192 = 384 by norm_num] using hbound

end ActualEisensteinCubic

namespace GaussianFiberEquiv

open ActualEisensteinCubic

def fiberMap (c : O) (r : O ⧸ Ideal.span {c})
    (r0 : O) (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r)
    (w : O) : ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}) := by
  refine ⟨r0 + c*w, ?_⟩
  change Ideal.Quotient.mk (Ideal.span {c}) (r0 + c*w) = r
  rw [map_add, map_mul]
  have hc0 : Ideal.Quotient.mk (Ideal.span {c}) c = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (Set.mem_singleton c))
  rw [hc0, zero_mul, add_zero, hr]

private theorem fiberMap_injective (c : O) (hc : c ≠ 0)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r) :
    Function.Injective (fiberMap c r r0 hr) := by
  intro u v h
  have hval := congrArg Subtype.val h
  change r0 + c*u = r0 + c*v at hval
  exact mul_left_cancel₀ hc (add_left_cancel hval)

private theorem fiberMap_surjective (c : O)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r) :
    Function.Surjective (fiberMap c r r0 hr) := by
  rintro ⟨z, hz⟩
  have hz' : Ideal.Quotient.mk (Ideal.span {c}) z = r := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hz
  have hdiff : z-r0 ∈ Ideal.span {c} :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem z r0).mp (hz'.trans hr.symm)
  obtain ⟨w, hw⟩ := (Ideal.mem_span_singleton).mp hdiff
  refine ⟨w, ?_⟩
  apply Subtype.ext
  change r0 + c*w = z
  rw [← hw]
  ring

noncomputable def fiberEquiv (c : O) (hc : c ≠ 0)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r) :
    O ≃ ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}) :=
  Equiv.ofBijective (fiberMap c r r0 hr)
    ⟨fiberMap_injective c hc r r0 hr, fiberMap_surjective c r r0 hr⟩

theorem fiber_tsum (c : O) (hc : c ≠ 0)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r)
    (W : O → ℂ) :
    (∑' z : ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}), W z.1) =
      ∑' w : O, W (r0 + c*w) := by
  have h := (fiberEquiv c hc r r0 hr).tsum_eq (fun z => W z.1)
  have happ (w : O) : ((fiberEquiv c hc r r0 hr) w).1 = r0 + c*w := rfl
  simpa only [happ] using h.symm

end GaussianFiberEquiv

namespace RankTwoPoisson

open Real

theorem schwartz_int_summable (f : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => f (n : ℝ)) := by
  exact summable_of_isBigO (Real.summable_abs_int_rpow (show (1 : ℝ) < 2 by norm_num))
    ((f.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)

theorem schwartz_int_norm_summable (f : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => ‖f (n : ℝ)‖) :=
  (schwartz_int_summable f).norm

theorem schwartz_int_poisson (f : 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, f (n : ℝ)) = ∑' n : ℤ, (𝓕 f) (n : ℝ) := by
  simpa [fourier_eval_zero] using
    SchwartzMap.tsum_eq_tsum_fourier f 0

theorem tensor_poisson (f g : 𝓢(ℝ, ℂ)) :
    (∑' z : ℤ × ℤ, f (z.1 : ℝ) * g (z.2 : ℝ)) =
      ∑' z : ℤ × ℤ, (𝓕 f) (z.1 : ℝ) * (𝓕 g) (z.2 : ℝ) := by
  calc
    (∑' z : ℤ × ℤ, f (z.1 : ℝ) * g (z.2 : ℝ)) =
        (∑' m : ℤ, f (m : ℝ)) * (∑' n : ℤ, g (n : ℝ)) :=
      (tsum_mul_tsum_of_summable_norm
        (schwartz_int_norm_summable f) (schwartz_int_norm_summable g)).symm
    _ = (∑' m : ℤ, (𝓕 f) (m : ℝ)) * (∑' n : ℤ, (𝓕 g) (n : ℝ)) :=
      congrArg₂ (· * ·) (schwartz_int_poisson f) (schwartz_int_poisson g)
    _ = ∑' z : ℤ × ℤ, (𝓕 f) (z.1 : ℝ) * (𝓕 g) (z.2 : ℝ) :=
      tsum_mul_tsum_of_summable_norm
        (schwartz_int_norm_summable (𝓕 f))
        (schwartz_int_norm_summable (𝓕 g))
  rfl

private theorem gauss_int_summable {a : ℂ} (ha : 0 < a.re) :
    Summable (fun n : ℤ => Complex.exp (-((Real.pi : ℂ) * a) * (n : ℂ) ^ 2)) := by
  have hpa : 0 < ((Real.pi : ℂ) * a).re := by
    simpa using mul_pos Real.pi_pos ha
  exact summable_of_isBigO (Real.summable_abs_int_rpow (show (1 : ℝ) < 2 by norm_num))
    ((isLittleO_exp_neg_mul_sq_cocompact hpa (-2)).isBigO.comp_tendsto
      Int.tendsto_coe_cofinite)

noncomputable def cg (a : ℂ) (n : ℤ) : ℂ :=
  Complex.exp (-((Real.pi : ℂ) * a) * (n : ℂ) ^ 2)

private theorem cg_summable {a : ℂ} (ha : 0 < a.re) : Summable (cg a) :=
  gauss_int_summable ha

private theorem cg_poisson {a : ℂ} (ha : 0 < a.re) :
    (∑' n : ℤ, cg a n) =
      (1 / a ^ (1 / 2 : ℂ)) * ∑' n : ℤ, cg a⁻¹ n := by
  simpa only [cg, div_eq_mul_inv, neg_mul, mul_assoc] using
    Complex.tsum_exp_neg_mul_int_sq ha

theorem diagonal_gaussian_poisson {a b : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re)
    (hai : 0 < (a⁻¹).re) (hbi : 0 < (b⁻¹).re) :
    (∑' z : ℤ × ℤ, cg a z.1 * cg b z.2) =
      (1 / a ^ (1 / 2 : ℂ)) * (1 / b ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, cg a⁻¹ z.1 * cg b⁻¹ z.2 := by
  calc
    (∑' z : ℤ × ℤ, cg a z.1 * cg b z.2) =
        (∑' m : ℤ, cg a m) * (∑' n : ℤ, cg b n) :=
      (tsum_mul_tsum_of_summable_norm (cg_summable ha).norm (cg_summable hb).norm).symm
    _ = ((1 / a ^ (1 / 2 : ℂ)) * ∑' m : ℤ, cg a⁻¹ m) *
        ((1 / b ^ (1 / 2 : ℂ)) * ∑' n : ℤ, cg b⁻¹ n) := by
      rw [cg_poisson ha, cg_poisson hb]
    _ = (1 / a ^ (1 / 2 : ℂ)) * (1 / b ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, cg a⁻¹ z.1 * cg b⁻¹ z.2 := by
      rw [← tsum_mul_tsum_of_summable_norm (cg_summable hai).norm (cg_summable hbi).norm]
      ring

theorem real_gauss_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℤ => Real.exp (-Real.pi * t * (n : ℝ) ^ 2)) := by
  have htc : 0 < (t : ℂ).re := by simpa using ht
  have h := (cg_summable htc).norm
  simpa [cg, Complex.norm_exp, ← Complex.ofReal_intCast, ← Complex.ofReal_pow, mul_assoc] using h

noncomputable def eisQ (z : ℤ × ℤ) : ℝ :=
  (z.1 : ℝ) ^ 2 - (z.1 : ℝ) * (z.2 : ℝ) + (z.2 : ℝ) ^ 2

noncomputable def eisGauss (t : ℝ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp ((-Real.pi * t * eisQ z : ℝ) : ℂ)

theorem eisQ_lower (z : ℤ × ℤ) :
    ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) / 2 ≤ eisQ z := by
  dsimp [eisQ]
  nlinarith [sq_nonneg ((z.1 : ℝ) - (z.2 : ℝ))]

theorem eis_gauss_summable {t : ℝ} (ht : 0 < t) :
    Summable (eisGauss t) := by
  have ht2 : 0 < t / 2 := by positivity
  have h1 := real_gauss_summable ht2
  have hmaj : Summable (fun z : ℤ × ℤ =>
      Real.exp (-Real.pi * (t / 2) * (z.1 : ℝ) ^ 2) *
      Real.exp (-Real.pi * (t / 2) * (z.2 : ℝ) ^ 2)) :=
    h1.mul_of_nonneg h1 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  refine hmaj.of_norm_bounded ?_
  intro z
  have hq := eisQ_lower z
  have hpi : 0 ≤ Real.pi * t := (mul_pos Real.pi_pos ht).le
  have hmul := mul_le_mul_of_nonneg_left hq hpi
  have hexp : -Real.pi * t * eisQ z ≤
      -Real.pi * (t / 2) * (z.1 : ℝ) ^ 2 +
      -Real.pi * (t / 2) * (z.2 : ℝ) ^ 2 := by
    nlinarith [hmul]
  simpa [eisGauss, Complex.norm_exp, Real.exp_add] using
    (Real.exp_le_exp.mpr hexp)

private noncomputable def phase (k n : ℤ) : ℂ :=
  Complex.exp (((-Real.pi * (k : ℝ) * (n : ℝ) : ℝ) : ℂ) * Complex.I)

private noncomputable def g1 (t : ℝ) (z : ℤ × ℤ) : ℂ :=
  cg ((t⁻¹ : ℝ) : ℂ) z.1 * cg (((3 * t) / 4 : ℝ) : ℂ) z.2 * phase z.1 z.2

private theorem phase_norm (k n : ℤ) : ‖phase k n‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re]

private theorem g1_summable {t : ℝ} (ht : 0 < t) : Summable (g1 t) := by
  have htinv : 0 < t⁻¹ := inv_pos.mpr ht
  have ht3 : 0 < 3 * t / 4 := by positivity
  have h1 := (cg_summable (a := ((t⁻¹ : ℝ) : ℂ)) (by simpa using htinv)).norm
  have h2 := (cg_summable (a := (((3 * t) / 4 : ℝ) : ℂ)) (by simpa using ht3)).norm
  have hmaj : Summable (fun z : ℤ × ℤ =>
      ‖cg ((t⁻¹ : ℝ) : ℂ) z.1‖ * ‖cg (((3 * t) / 4 : ℝ) : ℂ) z.2‖) :=
    h1.mul_of_nonneg h2 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  refine hmaj.of_norm_bounded ?_
  intro z
  simp [g1,  phase_norm]

private theorem eisGauss_split (t : ℝ) (m n : ℤ) :
    eisGauss t (m, n) =
      Complex.exp ((-Real.pi * t * (n : ℝ) ^ 2 : ℝ) : ℂ) *
        Complex.exp (-(Real.pi : ℂ) * (t : ℂ) * (m : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * (((t : ℂ) * (n : ℂ)) / 2) * (m : ℂ)) := by
  dsimp [eisGauss, eisQ]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem eis_exponent_identity {t : ℝ} (ht : 0 < t) (k n : ℤ) :
    (-(Real.pi : ℂ) * (t : ℂ) * (n : ℂ) ^ 2) +
      (-(Real.pi : ℂ) / (t : ℂ) *
        ((k : ℂ) + Complex.I * ((t : ℂ) * (n : ℂ) / 2)) ^ 2) =
      (-(Real.pi : ℂ) * (((t⁻¹ : ℝ) : ℂ)) * (k : ℂ) ^ 2) +
        (-(Real.pi : ℂ) * ((((3 * t) / 4 : ℝ) : ℂ)) * (n : ℂ) ^ 2) +
        (((-Real.pi * (k : ℝ) * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  push_cast
  field_simp [ht0]
  ring_nf
  simp [Complex.I_sq]
  ring

private theorem first_transform_term {t : ℝ} (ht : 0 < t) (k n : ℤ) :
    Complex.exp ((-Real.pi * t * (n : ℝ) ^ 2 : ℝ) : ℂ) *
      Complex.exp (-(Real.pi : ℂ) / (t : ℂ) *
        ((k : ℂ) + Complex.I * (((t : ℂ) * (n : ℂ)) / 2)) ^ 2) =
      g1 t (k, n) := by
  have hn : ((-Real.pi * t * (n : ℝ) ^ 2 : ℝ) : ℂ) =
      -(Real.pi : ℂ) * (t : ℂ) * (n : ℂ) ^ 2 := by
    push_cast
    ring
  rw [hn, ← Complex.exp_add, eis_exponent_identity ht k n]
  simp only [Complex.exp_add]
  dsimp [g1, cg, phase]
  push_cast
  ring_nf

private theorem first_poisson_slice {t : ℝ} (ht : 0 < t) (n : ℤ) :
    (∑' m : ℤ, eisGauss t (m, n)) =
      (1 / (t : ℂ) ^ (1 / 2 : ℂ)) * ∑' k : ℤ, g1 t (k, n) := by
  have htc : 0 < (t : ℂ).re := by simpa using ht
  let C : ℂ := Complex.exp ((-Real.pi * t * (n : ℝ) ^ 2 : ℝ) : ℂ)
  let B : ℂ := ((t : ℂ) * (n : ℂ)) / 2
  let F : ℤ → ℂ := fun m => Complex.exp
    (-(Real.pi : ℂ) * (t : ℂ) * (m : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * B * (m : ℂ))
  let H : ℤ → ℂ := fun k => Complex.exp
    (-(Real.pi : ℂ) / (t : ℂ) * ((k : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' m : ℤ, eisGauss t (m, n)) = C * ∑' m : ℤ, F m := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    exact eisGauss_split t m n
  have hpoisson : (∑' m : ℤ, F m) =
      (1 / (t : ℂ) ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k := by
    exact Complex.tsum_exp_neg_quadratic htc B
  calc
    (∑' m : ℤ, eisGauss t (m, n)) = C * ∑' m : ℤ, F m := hsplit
    _ = C * ((1 / (t : ℂ) ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k) := by rw [hpoisson]
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) * (C * ∑' k : ℤ, H k) := by ring
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) * ∑' k : ℤ, g1 t (k, n) := by
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      exact first_transform_term ht k n

private noncomputable def dualTerm (t : ℝ) (z : ℤ × ℤ) : ℂ :=
  cg ((t⁻¹ : ℝ) : ℂ) z.1 *
    Complex.exp (-(Real.pi : ℂ) / (((3 * t) / 4 : ℝ) : ℂ) *
      ((z.2 : ℂ) + (z.1 : ℂ) / 2) ^ 2)

private theorem second_transform_term (t : ℝ) (k n : ℤ) :
    cg ((((3 * t) / 4 : ℝ) : ℂ)) n * phase k n =
      Complex.exp (-(Real.pi : ℂ) * ((((3 * t) / 4 : ℝ) : ℂ)) * (n : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) * (-(Complex.I * (k : ℂ)) / 2) * (n : ℂ)) := by
  dsimp [cg, phase]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem second_poisson_slice {t : ℝ} (ht : 0 < t) (k : ℤ) :
    (∑' n : ℤ, g1 t (k, n)) =
      (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
        ∑' l : ℤ, dualTerm t (k, l) := by
  have ht3 : 0 < 3 * t / 4 := by positivity
  have ht3c : 0 < (((3 * t) / 4 : ℝ) : ℂ).re := by simpa using ht3
  let A : ℂ := (((3 * t) / 4 : ℝ) : ℂ)
  let B : ℂ := -(Complex.I * (k : ℂ)) / 2
  let C : ℂ := cg ((t⁻¹ : ℝ) : ℂ) k
  let F : ℤ → ℂ := fun n => Complex.exp
    (-(Real.pi : ℂ) * A * (n : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * B * (n : ℂ))
  let H : ℤ → ℂ := fun l => Complex.exp
    (-(Real.pi : ℂ) / A * ((l : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' n : ℤ, g1 t (k,n)) = C * ∑' n : ℤ, F n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    calc
      g1 t (k, n) = C * (cg A n * phase k n) := by
        dsimp [g1, C, A]
        ring
      _ = C * F n := by rw [second_transform_term t k n]
  have hpoisson : (∑' n : ℤ, F n) =
      (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l :=
    Complex.tsum_exp_neg_quadratic ht3c B
  have hterm (l : ℤ) : C * H l = dualTerm t (k,l) := by
    have hb : Complex.I * B = (k : ℂ) / 2 := by
      dsimp [B]
      field_simp
      ring_nf
      simp [Complex.I_sq]
    dsimp [H, dualTerm, C, A]
    rw [hb]
  calc
    (∑' n : ℤ, g1 t (k,n)) = C * ∑' n : ℤ, F n := hsplit
    _ = C * ((1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l) := by rw [hpoisson]
    _ = (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) := by ring
    _ = (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
          ∑' l : ℤ, dualTerm t (k,l) := by
      change (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) =
        (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, dualTerm t (k,l)
      congr 1
      rw [← tsum_mul_left]
      exact tsum_congr hterm

theorem eisenstein_gaussian_poisson_iterated {t : ℝ} (ht : 0 < t) :
    (∑' z : ℤ × ℤ, eisGauss t z) =
      (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
        (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
        ∑' k : ℤ, ∑' l : ℤ, dualTerm t (k,l) := by
  have hE := eis_gauss_summable ht
  have hG := g1_summable ht
  have hEcomm :
      (∑' n : ℤ, ∑' m : ℤ, eisGauss t (m,n)) =
        ∑' m : ℤ, ∑' n : ℤ, eisGauss t (m,n) :=
    (show Summable (Function.uncurry (fun m n : ℤ => eisGauss t (m,n))) from hE).tsum_comm
  have hGcomm :
      (∑' n : ℤ, ∑' k : ℤ, g1 t (k,n)) =
        ∑' k : ℤ, ∑' n : ℤ, g1 t (k,n) :=
    (show Summable (Function.uncurry (fun k n : ℤ => g1 t (k,n))) from hG).tsum_comm
  calc
    (∑' z : ℤ × ℤ, eisGauss t z) =
        ∑' m : ℤ, ∑' n : ℤ, eisGauss t (m,n) := hE.tsum_prod
    _ = ∑' n : ℤ, ∑' m : ℤ, eisGauss t (m,n) := hEcomm.symm
    _ = ∑' n : ℤ, (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          ∑' k : ℤ, g1 t (k,n) := by
      apply tsum_congr
      intro n
      exact first_poisson_slice ht n
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (∑' n : ℤ, ∑' k : ℤ, g1 t (k,n)) := tsum_mul_left
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' n : ℤ, g1 t (k,n)) := by
      rw [hGcomm]
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
            ∑' l : ℤ, dualTerm t (k,l)) := by
      congr 1
      apply tsum_congr
      intro k
      exact second_poisson_slice ht k
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
          ∑' k : ℤ, ∑' l : ℤ, dualTerm t (k,l) := by
      rw [tsum_mul_left]
      ring

private theorem dualTerm_eq_eisGauss {t : ℝ} (ht : 0 < t) (k l : ℤ) :
    dualTerm t (k,l) = eisGauss (4 / (3 * t)) (k,-l) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  dsimp [dualTerm, cg, eisGauss, eisQ]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  field_simp [ht0]
  ring

private theorem dualTerm_summable {t : ℝ} (ht : 0 < t) :
    Summable (dualTerm t) := by
  have htd : 0 < 4 / (3 * t) := by positivity
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have h := (e.summable_iff).2 (eis_gauss_summable htd)
  apply h.congr
  intro z
  change eisGauss (4 / (3 * t)) (z.1, -z.2) = dualTerm t z
  exact (dualTerm_eq_eisGauss ht z.1 z.2).symm

theorem eisenstein_gaussian_poisson {t : ℝ} (ht : 0 < t) :
    (∑' z : ℤ × ℤ, eisGauss t z) =
      (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
        (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, eisGauss (4 / (3 * t)) z := by
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have hdual : (∑' z : ℤ × ℤ, dualTerm t z) =
      ∑' z : ℤ × ℤ, eisGauss (4 / (3 * t)) z := by
    calc
      (∑' z : ℤ × ℤ, dualTerm t z) =
          ∑' z : ℤ × ℤ, eisGauss (4 / (3 * t)) (e z) := by
        apply tsum_congr
        intro z
        exact dualTerm_eq_eisGauss ht z.1 z.2
      _ = ∑' z : ℤ × ℤ, eisGauss (4 / (3 * t)) z :=
        Equiv.tsum_eq e _
  calc
    (∑' z : ℤ × ℤ, eisGauss t z) =
        (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' l : ℤ, dualTerm t (k,l)) :=
      eisenstein_gaussian_poisson_iterated ht
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
          (∑' z : ℤ × ℤ, dualTerm t z) := by
      rw [(dualTerm_summable ht).tsum_prod]
    _ = _ := by rw [hdual]

end RankTwoPoisson

end

end OAI
end OAIOriginalModule0047

/-! Original module: OAI.NumberTheory.DirichletL.Moments.Basic
Source SHA256: 437f147882d26f668db45b3ed9721f3c9c334ecc4e76fe22e8848e005f26ba71
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0048










namespace OAI

open scoped BigOperators NNReal
namespace SevenEighths.CenteredMoment
noncomputable section

variable {M R : Type*} [CommMonoid M] [CommRing R]

structure MaskedCharacter (M R : Type*) [CommMonoid M] [CommRing R] where
  residue : M →* R
  character : MulChar R ℂ
  keep : M → Prop
  keep_mul : ∀ a b, keep (a * b) ↔ keep a ∧ keep b

def ofResidueMask {S : Type*} [CommRing S] (ρ : M →* R)
    (χ : MulChar R ℂ) (puncture : M →* S) : MaskedCharacter M R where
  residue := ρ
  character := χ
  keep a := IsUnit (puncture a)
  keep_mul a b := by
    rw [map_mul]
    exact (Commute.all _ _).isUnit_mul_iff

@[simp] theorem ofResidueMask_keep_one {S : Type*} [CommRing S]
    (ρ : M →* R) (χ : MulChar R ℂ) (puncture : M →* S) :
    (ofResidueMask ρ χ puncture).keep 1 := by
  change IsUnit (puncture 1)
  simp only [map_one, isUnit_one]

def MaskedCharacter.value (d : MaskedCharacter M R) (a : M) : ℂ :=
  @ite ℂ (d.keep a) (Classical.propDecidable _) (d.character (d.residue a)) 0

@[simp] theorem MaskedCharacter.value_mul (d : MaskedCharacter M R) (a b : M) :
    d.value (a * b) = d.value a * d.value b := by
  classical
  simp only [MaskedCharacter.value, d.keep_mul, map_mul]
  split_ifs <;> simp_all

def normTwist (N : M →* ℝ≥0) (t : ℝ) (a : M) : ℂ :=
  ((N a : ℝ) : ℂ) ^ (Complex.I * t)

@[simp] theorem normTwist_mul (N : M →* ℝ≥0) (t : ℝ) (a b : M) :
    normTwist N t (a * b) = normTwist N t a * normTwist N t b := by
  simp only [normTwist, map_mul, NNReal.coe_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (N a).coe_nonneg (N b).coe_nonneg _

def coefficient (d : MaskedCharacter M R) (N : M →* ℝ≥0) (t : ℝ) (a : M) : ℂ :=
  d.value a * normTwist N t a

@[simp] theorem coefficient_mul (d : MaskedCharacter M R) (N : M →* ℝ≥0)
    (t : ℝ) (a b : M) :
    coefficient d N t (a * b) = coefficient d N t a * coefficient d N t b := by
  simp only [coefficient, MaskedCharacter.value_mul, normTwist_mul]
  ring

def plainSum (d : MaskedCharacter M R) (N : M →* ℝ≥0) (t : ℝ)
    (s : Finset M) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑ a ∈ s, coefficient d N t a * W ((N a : ℝ) / X)

def rectangle (N : M →* ℝ≥0) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (a b : M) : ℂ :=
  W₁ ((N a : ℝ) / X₁) * W₂ ((N b : ℝ) / X₂) -
    W₁ ((N a : ℝ) / Y₁) * W₂ ((N b : ℝ) / Y₂)

theorem rectangle_sum_eq (d : MaskedCharacter M R) (N : M →* ℝ≥0) (t : ℝ)
    (s₁ s₂ : Finset M) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) :
    (∑ a ∈ s₁, ∑ b ∈ s₂,
      coefficient d N t (a * b) * rectangle N W₁ W₂ X₁ X₂ Y₁ Y₂ a b) =
      plainSum d N t s₁ W₁ X₁ * plainSum d N t s₂ W₂ X₂ -
        plainSum d N t s₁ W₁ Y₁ * plainSum d N t s₂ W₂ Y₂ := by
  simp only [plainSum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [coefficient_mul, rectangle]
  ring

theorem slot_rectangle_sum_eq (d : MaskedCharacter M R) (N : M →* ℝ≥0) (t : ℝ)
    (p : M) (s₁ s₂ : Finset M) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) :
    (∑ a ∈ s₁, ∑ b ∈ s₂,
      coefficient d N t (p * (a * b)) * rectangle N W₁ W₂ X₁ X₂ Y₁ Y₂ a b) =
      coefficient d N t p *
        (plainSum d N t s₁ W₁ X₁ * plainSum d N t s₂ W₂ X₂ -
          plainSum d N t s₁ W₁ Y₁ * plainSum d N t s₂ W₂ Y₂) := by
  rw [← rectangle_sum_eq]
  simp only [coefficient_mul, Finset.mul_sum, mul_assoc]

def volumeTerm (c I : ℂ) (t X : ℝ) : ℂ :=
  c * (X : ℂ) ^ (1 + Complex.I * t) * I

theorem volume_products_eq (c I₁ I₂ : ℂ) (t X₁ X₂ Y₁ Y₂ : ℝ)
    (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂) (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂)
    (hscale : X₁ * X₂ = Y₁ * Y₂) :
    volumeTerm c I₁ t X₁ * volumeTerm c I₂ t X₂ =
      volumeTerm c I₁ t Y₁ * volumeTerm c I₂ t Y₂ := by
  have hpow : (X₁ : ℂ) ^ (1 + Complex.I * t) *
      (X₂ : ℂ) ^ (1 + Complex.I * t) =
      (Y₁ : ℂ) ^ (1 + Complex.I * t) * (Y₂ : ℂ) ^ (1 + Complex.I * t) := by
    rw [← Complex.mul_cpow_ofReal_nonneg hX₁ hX₂,
      ← Complex.mul_cpow_ofReal_nonneg hY₁ hY₂, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, hscale]
  unfold volumeTerm
  calc
    _ = c ^ 2 * I₁ * I₂ *
      ((X₁ : ℂ) ^ (1 + Complex.I * t) * (X₂ : ℂ) ^ (1 + Complex.I * t)) := by ring
    _ = _ := by rw [hpow]; ring

theorem centered_error_identity (A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ : ℂ)
    (hmain : a₁ * a₂ = b₁ * b₂) :
    A₁ * A₂ - B₁ * B₂ =
      (A₁ - a₁) * A₂ + a₁ * (A₂ - a₂) -
        (B₁ - b₁) * B₂ - b₁ * (B₂ - b₂) := by
  linear_combination hmain

theorem norm_centered_le (A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ : ℂ)
    (hmain : a₁ * a₂ = b₁ * b₂) :
    ‖A₁ * A₂ - B₁ * B₂‖ ≤
      ‖A₁ - a₁‖ * ‖A₂‖ + ‖a₁‖ * ‖A₂ - a₂‖ +
        ‖B₁ - b₁‖ * ‖B₂‖ + ‖b₁‖ * ‖B₂ - b₂‖ := by
  rw [centered_error_identity A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ hmain]
  calc
    _ ≤ ‖(A₁ - a₁) * A₂ + a₁ * (A₂ - a₂) - (B₁ - b₁) * B₂‖ +
        ‖b₁ * (B₂ - b₂)‖ := norm_sub_le _ _
    _ ≤ (‖(A₁ - a₁) * A₂ + a₁ * (A₂ - a₂)‖ +
        ‖(B₁ - b₁) * B₂‖) + ‖b₁ * (B₂ - b₂)‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ ((‖(A₁ - a₁) * A₂‖ + ‖a₁ * (A₂ - a₂)‖) +
        ‖(B₁ - b₁) * B₂‖) + ‖b₁ * (B₂ - b₂)‖ :=
      add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ = _ := by simp only [norm_mul]

theorem norm_centered_le_of_approx
    (A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ : ℂ)
    (X₁ X₂ Y₁ Y₂ C E : ℝ)
    (hmain : a₁ * a₂ = b₁ * b₂)
    (hE : 0 ≤ E)
    (hA₁ : ‖A₁ - a₁‖ ≤ E) (hA₂ : ‖A₂ - a₂‖ ≤ E)
    (hB₁ : ‖B₁ - b₁‖ ≤ E) (hB₂ : ‖B₂ - b₂‖ ≤ E)
    (hvA₂ : ‖A₂‖ ≤ C * X₂) (hva₁ : ‖a₁‖ ≤ C * X₁)
    (hvB₂ : ‖B₂‖ ≤ C * Y₂) (hvb₁ : ‖b₁‖ ≤ C * Y₁) :
    ‖A₁ * A₂ - B₁ * B₂‖ ≤ E * C * (X₁ + X₂ + Y₁ + Y₂) := by
  have h₁ := mul_le_mul hA₁ hvA₂ (norm_nonneg A₂) hE
  have h₂ := mul_le_mul hA₂ hva₁ (norm_nonneg a₁) hE
  have h₃ := mul_le_mul hB₁ hvB₂ (norm_nonneg B₂) hE
  have h₄ := mul_le_mul hB₂ hvb₁ (norm_nonneg b₁) hE
  have h := norm_centered_le A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ hmain
  nlinarith

theorem scale_le_product_div {X Y T L : ℝ}
    (hX : 0 ≤ X) (hL : 0 < L) (hY : L ≤ Y) (hprod : X * Y = T) :
    X ≤ T / L := by
  apply (le_div_iff₀ hL).mpr
  rw [← hprod]
  exact mul_le_mul_of_nonneg_left hY hX

theorem sum_scales_le {X₁ X₂ Y₁ Y₂ T L : ℝ}
    (hL : 0 < L) (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂)
    (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    X₁ + X₂ + Y₁ + Y₂ ≤ 4 * (T / L) := by
  have a := scale_le_product_div (le_trans hL.le hX₁) hL hX₂ hprodX
  have b := scale_le_product_div (le_trans hL.le hX₂) hL hX₁
    (by simpa only [mul_comm] using hprodX)
  have c := scale_le_product_div (le_trans hL.le hY₁) hL hY₂ hprodY
  have d := scale_le_product_div (le_trans hL.le hY₂) hL hY₁
    (by simpa only [mul_comm] using hprodY)
  linarith

theorem centered_saving_of_approx
    (A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ : ℂ)
    (X₁ X₂ Y₁ Y₂ T L C E : ℝ)
    (hmain : a₁ * a₂ = b₁ * b₂)
    (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hA₁ : ‖A₁ - a₁‖ ≤ E) (hA₂ : ‖A₂ - a₂‖ ≤ E)
    (hB₁ : ‖B₁ - b₁‖ ≤ E) (hB₂ : ‖B₂ - b₂‖ ≤ E)
    (hvA₂ : ‖A₂‖ ≤ C * X₂) (hva₁ : ‖a₁‖ ≤ C * X₁)
    (hvB₂ : ‖B₂‖ ≤ C * Y₂) (hvb₁ : ‖b₁‖ ≤ C * Y₁)
    (hL : 0 < L) (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂)
    (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    ‖A₁ * A₂ - B₁ * B₂‖ ≤ 4 * E * C * (T / L) := by
  have h := norm_centered_le_of_approx A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂
    X₁ X₂ Y₁ Y₂ C E hmain hE hA₁ hA₂ hB₁ hB₂ hvA₂ hva₁ hvB₂ hvb₁
  have hs := sum_scales_le hL hX₁ hX₂ hY₁ hY₂ hprodX hprodY
  calc
    _ ≤ E * C * (X₁ + X₂ + Y₁ + Y₂) := h
    _ ≤ E * C * (4 * (T / L)) := mul_le_mul_of_nonneg_left hs (mul_nonneg hE hC)
    _ = _ := by ring

theorem extracted_volume_phase (X D t : ℝ) (hX : 0 ≤ X) (hD : 0 < D) :
    (D : ℂ) ^ (Complex.I * t) * ((X / D : ℝ) : ℂ) ^ (1 + Complex.I * t) =
      (X : ℂ) ^ (1 + Complex.I * t) / (D : ℂ) := by
  have hDc : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hD)
  have hp : (D : ℂ) ^ (Complex.I * t) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hDc)
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hX hD.le,
    Complex.cpow_add _ _ hDc, Complex.cpow_one]
  field_simp

theorem extracted_volume_sum {D : Type*} (s : Finset D) (a : D → ℂ)
    (norm : D → ℝ) (hnorm : ∀ d ∈ s, 0 < norm d)
    (c I : ℂ) (t X : ℝ) (hX : 0 ≤ X) :
    (∑ d ∈ s, a d * (norm d : ℂ) ^ (Complex.I * t) *
      volumeTerm c I t (X / norm d)) =
      volumeTerm (c * ∑ d ∈ s, a d / (norm d : ℂ)) I t X := by
  unfold volumeTerm
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  have h := extracted_volume_phase X (norm d) t hX (hnorm d hd)
  calc
    _ = a d * c * I * ((norm d : ℂ) ^ (Complex.I * t) *
        ((X / norm d : ℝ) : ℂ) ^ (1 + Complex.I * t)) := by ring
    _ = _ := by rw [h]; ring

theorem centered_volume_fallback (A₁ A₂ B₁ B₂ : ℂ)
    (X₁ X₂ Y₁ Y₂ T C : ℝ)
    (hA₁ : ‖A₁‖ ≤ C * X₁) (hA₂ : ‖A₂‖ ≤ C * X₂)
    (hB₁ : ‖B₁‖ ≤ C * Y₁) (hB₂ : ‖B₂‖ ≤ C * Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    ‖A₁ * A₂ - B₁ * B₂‖ ≤ 2 * C ^ 2 * T := by
  have hA := mul_le_mul hA₁ hA₂ (norm_nonneg A₂) ((norm_nonneg A₁).trans hA₁)
  have hB := mul_le_mul hB₁ hB₂ (norm_nonneg B₂) ((norm_nonneg B₁).trans hB₁)
  have h := norm_sub_le (A₁ * A₂) (B₁ * B₂)
  rw [norm_mul, norm_mul] at h
  have heX : C * X₁ * (C * X₂) = C ^ 2 * T := by rw [← hprodX]; ring
  have heY : C * Y₁ * (C * Y₂) = C ^ 2 * T := by rw [← hprodY]; ring
  rw [heX] at hA
  rw [heY] at hB
  linarith

theorem normalized_centered_saving (D : ℂ) (T L C E : ℝ)
    (hT : 0 < T) (hbound : ‖D‖ ≤ 4 * E * C * (T / L)) :
    ‖(Real.sqrt T : ℂ)⁻¹ * D‖ ≤ 4 * E * C * (Real.sqrt T / L) := by
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs.le]
  calc
    _ ≤ (Real.sqrt T)⁻¹ * (4 * E * C * (T / L)) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hs.le)
    _ = 4 * E * C * ((T / Real.sqrt T) / L) := by ring
    _ = _ := by
      have hdiv : T / Real.sqrt T = Real.sqrt T :=
        (div_eq_iff hs.ne').mpr (Real.mul_self_sqrt hT.le).symm
      rw [hdiv]

end
end SevenEighths.CenteredMoment

end OAI
end OAIOriginalModule0048

/-! Original module: OAI.NumberTheory.DirichletL.Moments.Correlation
Source SHA256: 90d0837fc41a775de40975dae29ff985ceaf4a4b01e7c1f0c078de251addedbe
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0049







namespace OAI

open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {R X Y : Type*} [CommRing R] [Fintype R] [Fintype X] [Fintype Y]

def fourierSum (ψ : AddChar R ℂ) (place : X → R) (f : X → ℂ) (h : R) : ℂ :=
  ∑ x, f x * ψ (h * place x)

def fullCorrelation (left : X → R) (right : Y → R)
    (f : X → ℂ) (g : Y → ℂ) (j : R) : ℂ :=
  ∑ x, ∑ y, if left x - right y = j then f x * star (g y) else 0

omit [Fintype R] in
theorem fullCorrelation_swap (left : X → R) (right : Y → R)
    (f : X → ℂ) (g : Y → ℂ) (j : R) :
    fullCorrelation left right f g j = star (fullCorrelation right left g f (-j)) := by
  classical
  simp only [fullCorrelation, star_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  have heq : left x - right y = j ↔ right y - left x = -j := by
    constructor <;> intro h <;> linear_combination -h
  by_cases h : left x - right y = j
  · simp [h, heq.mp h, star_mul]
  · simp [h, not_congr heq |>.mp h]

theorem fullCorrelation_fourier (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (left : X → R) (right : Y → R) (f : X → ℂ) (g : Y → ℂ) (j : R) :
    (∑ h : R, fourierSum ψ left f h * star (fourierSum ψ right g h) * ψ (-(h * j))) =
      (Fintype.card R : ℂ) * fullCorrelation left right f g j := by
  classical
  simp only [fourierSum, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext x
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  have hphase (h : R) (x : X) (y : Y) :
      (f x * ψ (h * left x) * (star (ψ (h * right y)) * star (g y))) * ψ (-(h * j)) =
        (f x * star (g y)) * ψ (h * (left x - right y - j)) := by
    have hs : star (ψ (h * right y)) = ψ (-(h * right y)) := by
      simpa only [← starRingEnd_apply] using (AddChar.map_neg_eq_conj ψ (h * right y)).symm
    rw [hs]
    calc
      _ = (f x * star (g y)) *
          (ψ (h * left x) * ψ (-(h * right y)) * ψ (-(h * j))) := by ring
      _ = _ := by
        rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
        congr 2
        ring
  simp_rw [hphase, ← Finset.mul_sum, AddChar.sum_mulShift _ hψ]
  simp only [fullCorrelation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : left x - right y = j
  · simp [hxy, mul_comm]
  · simp [sub_ne_zero.mpr hxy, hxy]

section FiniteField
variable {F : Type*} [Field F] [Fintype F]

def shiftCorrelation (χ : MulChar F ℂ) (k : F) : ℂ :=
  ∑ x : F, χ x * star (χ (x - k))

lemma character_mul_star (χ : MulChar F ℂ) {a : F} (ha : a ≠ 0) :
    χ a * star (χ a) = 1 := by
  rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']
  exact mul_inv_cancel₀ (χ.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr ha))

theorem shiftCorrelation_scale (χ : MulChar F ℂ) {k : F} (hk : k ≠ 0) :
    shiftCorrelation χ k = shiftCorrelation χ 1 := by
  unfold shiftCorrelation
  rw [← (Equiv.mulLeft₀ k hk).sum_comp]
  swap
  · simp
  apply Finset.sum_congr rfl
  intro x _
  simp only [Equiv.mulLeft₀_apply]
  rw [show k * x - k = k * (x - 1) by ring, map_mul, map_mul, star_mul]
  calc
    _ = (χ k * star (χ k)) * (χ x * star (χ (x - 1))) := by ring
    _ = _ := by rw [character_mul_star χ hk, one_mul]

theorem shiftCorrelation_one (χ : MulChar F ℂ) :
    shiftCorrelation χ 1 = χ⁻¹ (-1) * jacobiSum χ χ⁻¹ := by
  simp only [shiftCorrelation, jacobiSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [MulChar.star_apply', show x - 1 = (-1) * (1 - x) by ring, map_mul]
  ring

theorem shiftCorrelation_zero (χ : MulChar F ℂ) :
    shiftCorrelation χ 0 = (Fintype.card F : ℂ) - 1 := by
  classical
  simp only [shiftCorrelation, sub_zero, MulChar.star_apply', ← MulChar.mul_apply,
    mul_inv_cancel]
  rw [MulChar.sum_one_eq_card_units, Fintype.card_eq_card_units_add_one (α := F)]
  simp

theorem shiftCorrelation_nonprincipal (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    {k : F} (hk : k ≠ 0) : shiftCorrelation χ k = -1 := by
  rw [shiftCorrelation_scale χ hk, shiftCorrelation_one, jacobiSum_nontrivial_inv hχ,
    mul_neg, ← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero))]

theorem shiftCorrelation_principal {k : F} (hk : k ≠ 0) :
    shiftCorrelation (1 : MulChar F ℂ) k = (Fintype.card F : ℂ) - 2 := by
  rw [shiftCorrelation_scale _ hk, shiftCorrelation_one, inv_one,
    MulChar.one_apply (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero)), one_mul, jacobiSum_one_one]

def localCorrelation (χ : MulChar F ℂ) (n₁ n₂ k : F) : ℂ :=
  fullCorrelation (fun x : F => n₂ * x) (fun y : F => n₁ * y) χ χ k

theorem localCorrelation_eq_shift (χ : MulChar F ℂ) {n₁ n₂ : F}
    (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) (k : F) :
    localCorrelation χ n₁ n₂ k = χ (n₁ / n₂) * shiftCorrelation χ (k / n₁) := by
  classical
  have hsolve (x y : F) : n₂ * x - n₁ * y = k ↔ y = (n₂ * x - k) / n₁ := by
    rw [eq_div_iff h₁]
    constructor <;> intro h <;> linear_combination -h
  unfold localCorrelation fullCorrelation
  simp only [hsolve, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← (Equiv.mulLeft₀ (n₁ / n₂) (div_ne_zero h₁ h₂)).sum_comp]
  swap
  · simp
  simp only [Equiv.mulLeft₀_apply, shiftCorrelation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_mul]
  have heq : (n₂ * (n₁ / n₂ * x) - k) / n₁ = x - k / n₁ := by
    field_simp
  rw [heq, mul_assoc]

theorem localCorrelation_units (χ : MulChar F ℂ) {n₁ n₂ : F}
    (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) (k : F) :
    localCorrelation χ n₁ n₂ k = χ (n₁ / n₂) *
      (if k = 0 then (Fintype.card F : ℂ) - 1
       else if χ = 1 then (Fintype.card F : ℂ) - 2 else -1) := by
  rw [localCorrelation_eq_shift χ h₁ h₂]
  by_cases hk : k = 0
  · simp [hk, shiftCorrelation_zero]
  · by_cases hχ : χ = 1
    · simp [hk, hχ, shiftCorrelation_principal (div_ne_zero hk h₁)]
    · simp [hk, hχ, shiftCorrelation_nonprincipal χ hχ (div_ne_zero hk h₁)]

lemma character_sum (χ : MulChar F ℂ) :
    (∑ x : F, χ x) = if χ = 1 then (Fintype.card F : ℂ) - 1 else 0 := by
  classical
  by_cases hχ : χ = 1
  · subst χ
    rw [MulChar.sum_one_eq_card_units, Fintype.card_eq_card_units_add_one (α := F)]
    simp
  · simp [hχ, MulChar.sum_eq_zero_of_ne_one hχ]

theorem localCorrelation_first_zero (χ : MulChar F ℂ) {n₂ : F} (h₂ : n₂ ≠ 0) (k : F) :
    localCorrelation χ 0 n₂ k =
      if χ = 1 ∧ k ≠ 0 then (Fintype.card F : ℂ) - 1 else 0 := by
  classical
  have hsolve (x : F) : n₂ * x = k ↔ x = k / n₂ := by
    rw [eq_div_iff h₂, mul_comm]
  have hsum : localCorrelation χ 0 n₂ k = χ (k / n₂) * star (∑ y : F, χ y) := by
    unfold localCorrelation fullCorrelation
    simp only [zero_mul, sub_zero, hsolve]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.mul_sum, ← star_sum]
  rw [hsum, character_sum]
  by_cases hχ : χ = 1
  · subst χ
    by_cases hk : k = 0
    · simp [hk, MulChar.map_zero]
    · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr (div_ne_zero hk h₂))]
      simp [hk]
  · simp [hχ]

theorem localCorrelation_second_zero (χ : MulChar F ℂ) {n₁ : F} (h₁ : n₁ ≠ 0) (k : F) :
    localCorrelation χ n₁ 0 k =
      if χ = 1 ∧ k ≠ 0 then (Fintype.card F : ℂ) - 1 else 0 := by
  classical
  have hsolve (y : F) : -(n₁ * y) = k ↔ y = -k / n₁ := by
    rw [eq_div_iff h₁]
    constructor <;> intro h <;> linear_combination -h
  have hsum : localCorrelation χ n₁ 0 k = (∑ x : F, χ x) * star (χ (-k / n₁)) := by
    unfold localCorrelation fullCorrelation
    simp only [zero_mul, zero_sub, hsolve, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      ← Finset.sum_mul]
  rw [hsum, character_sum]
  by_cases hχ : χ = 1
  · subst χ
    by_cases hk : k = 0
    · simp [hk, MulChar.map_zero]
    · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr (div_ne_zero (neg_ne_zero.mpr hk) h₁))]
      simp [hk]
  · simp [hχ]

end FiniteField

variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]

def reductionMultiplicity (π : A →+* B) : ℕ :=
  (Finset.univ.filter fun x : A => π x = 0).card

theorem sum_reduction (π : A →+* B) (hπ : Function.Surjective π) (f : B → ℂ) :
    (∑ x : A, f (π x)) = (reductionMultiplicity π : ℂ) * ∑ y : B, f y := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ π (fun x => f (π x)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = ∑ x : A with π x = y, f y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = _ := by
      have hc := AddMonoidHom.card_fiber_eq_of_mem_range π (hπ y) (hπ 0)
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hc]
      rfl

theorem reductionMultiplicity_mul_card (π : A →+* B) (hπ : Function.Surjective π) :
    reductionMultiplicity π * Fintype.card B = Fintype.card A := by
  have h := sum_reduction π hπ (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h.symm

theorem reductionMultiplicity_eq_pow (π : A →+* B) (hπ : Function.Surjective π)
    {P c : ℕ} (hP : 0 < P) (hc : 1 ≤ c)
    (hA : Fintype.card A = P ^ c) (hB : Fintype.card B = P) :
    reductionMultiplicity π = P ^ (c - 1) := by
  apply Nat.eq_of_mul_eq_mul_right hP
  rw [← hB, reductionMultiplicity_mul_card π hπ, hA, hB, ← pow_succ,
    Nat.sub_add_cancel hc]

theorem fullCorrelation_unit_right (u : Aˣ) (v k : A) (f g : A → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => (u : A) * y) f g k =
      ∑ x : A, f x * star (g ((↑u⁻¹ : A) * (v * x - k))) := by
  classical
  have hsolve (x y : A) : v * x - (u : A) * y = k ↔
      y = (↑u⁻¹ : A) * (v * x - k) := by
    constructor
    · intro h
      have heq : v * x - k = (u : A) * y := by linear_combination h
      rw [heq, ← mul_assoc, Units.inv_mul, one_mul]
    · intro h
      rw [h, ← mul_assoc, Units.mul_inv, one_mul]
      ring
  simp only [fullCorrelation, hsolve, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem fullCorrelation_reduction_unit_right (π : A →+* B)
    (hπ : Function.Surjective π) (u : Aˣ) (v k : A) (f g : B → ℂ) :
    fullCorrelation (fun x : A => v * x) (fun y : A => (u : A) * y)
        (fun x => f (π x)) (fun y => g (π y)) k =
      (reductionMultiplicity π : ℂ) *
        fullCorrelation (fun x : B => π v * x) (fun y : B => π u * y) f g (π k) := by
  rw [fullCorrelation_unit_right]
  have hright := fullCorrelation_unit_right (Units.map π.toMonoidHom u) (π v) (π k) f g
  change fullCorrelation _ (fun y : B => π u * y) _ _ _ = _ at hright
  rw [hright]
  change (∑ x : A, f (π x) * star (g (π ((↑u⁻¹ : A) * (v * x - k))))) =
    (reductionMultiplicity π : ℂ) *
      ∑ x : B, f x * star (g (π (↑u⁻¹ : A) * (π v * x - π k)))
  simpa only [map_mul, map_sub] using
    sum_reduction π hπ (fun x => f x * star (g (π (↑u⁻¹ : A) * (π v * x - π k))))

theorem fullCorrelation_reduction_unit_left (π : A →+* B)
    (hπ : Function.Surjective π) (u : A) (v : Aˣ) (k : A) (f g : B → ℂ) :
    fullCorrelation (fun x : A => (v : A) * x) (fun y : A => u * y)
        (fun x => f (π x)) (fun y => g (π y)) k =
      (reductionMultiplicity π : ℂ) *
        fullCorrelation (fun x : B => π v * x) (fun y : B => π u * y) f g (π k) := by
  rw [fullCorrelation_swap, fullCorrelation_reduction_unit_right π hπ v u (-k) g f]
  rw [fullCorrelation_swap (fun x : B => π v * x) (fun y : B => π u * y) f g (π k)]
  simp only [map_neg, star_mul, star_natCast]
  ring

end
end SevenEighths.CenteredMomentCorrelation

end OAI
end OAIOriginalModule0049

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CRT
Source SHA256: 870db8546c08aea6d11ffad289fcd0e6c8d2454d29d3cb04a9c1ce269935aa36
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0050




namespace OAI

open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]

theorem fullCorrelation_ringEquiv (e : A ≃+* B) (u v k : A) (f g : B → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => f (e x)) (fun y => g (e y)) k =
      fullCorrelation (fun x => e v * x) (fun y => e u * y) f g (e k) := by
  unfold fullCorrelation
  apply Fintype.sum_equiv e.toEquiv
  intro x
  apply Fintype.sum_equiv e.toEquiv
  intro y
  have heq : v * x - u * y = k ↔ e v * e x - e u * e y = e k := by
    rw [← map_mul, ← map_mul, ← map_sub, e.injective.eq_iff]
  simp only [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, heq]

theorem fullCorrelation_product (u v k : A × B) (f₁ g₁ : A → ℂ) (f₂ g₂ : B → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => f₁ x.1 * f₂ x.2) (fun y => g₁ y.1 * g₂ y.2) k =
      fullCorrelation (fun x => v.1 * x) (fun y => u.1 * y) f₁ g₁ k.1 *
        fullCorrelation (fun x => v.2 * x) (fun y => u.2 * y) f₂ g₂ k.2 := by
  classical
  simp only [fullCorrelation, Fintype.sum_prod_type]
  have hterm (x₁ y₁ : A) (x₂ y₂ : B) :
      (if v * (x₁, x₂) - u * (y₁, y₂) = k
       then (f₁ x₁ * f₂ x₂) * star (g₁ y₁ * g₂ y₂) else 0) =
      (if v.1 * x₁ - u.1 * y₁ = k.1 then f₁ x₁ * star (g₁ y₁) else 0) *
      (if v.2 * x₂ - u.2 * y₂ = k.2 then f₂ x₂ * star (g₂ y₂) else 0) := by
    have heq : v * (x₁, x₂) - u * (y₁, y₂) = k ↔
        v.1 * x₁ - u.1 * y₁ = k.1 ∧ v.2 * x₂ - u.2 * y₂ = k.2 := by
      exact Prod.ext_iff
    by_cases h₁ : v.1 * x₁ - u.1 * y₁ = k.1 <;>
      by_cases h₂ : v.2 * x₂ - u.2 * y₂ = k.2 <;>
      simp [heq, h₁, h₂, star_mul] ; ring
  simp_rw [hterm]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x₁ _
  rw [Finset.sum_comm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y₁ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x₂ _
  rw [Finset.mul_sum]

theorem fullCorrelation_pi {ι : Type*} [Fintype ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] [∀ i, Fintype (R i)]
    (u v k : ∀ i, R i) (f g : ∀ i, R i → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => ∏ i, f i (x i)) (fun y => ∏ i, g i (y i)) k =
      ∏ i, fullCorrelation (fun x => v i * x) (fun y => u i * y) (f i) (g i) (k i) := by
  classical
  have hterm (x y : ∀ i, R i) :
      (if v * x - u * y = k then (∏ i, f i (x i)) * star (∏ i, g i (y i)) else 0) =
      ∏ i, if v i * x i - u i * y i = k i then f i (x i) * star (g i (y i)) else 0 := by
    by_cases h : ∀ i, v i * x i - u i * y i = k i
    · have heq : v * x - u * y = k := funext h
      simp only [heq, ite_true, h, star_prod, Finset.prod_mul_distrib]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      have hne : v * x - u * y ≠ k := fun heq => hi (congrFun heq i)
      rw [ite_eq_right hne]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [hi, ite_false]
  simp only [fullCorrelation]
  simp_rw [hterm]
  calc
    _ = ∑ x : ∀ i, R i, ∏ i, ∑ y : R i,
        if v i * x i - u i * y = k i then f i (x i) * star (g i y) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Fintype.prod_sum (fun i (y : R i) =>
        if v i * x i - u i * y = k i then f i (x i) * star (g i y) else (0 : ℂ))).symm
    _ = _ := (Fintype.prod_sum (fun i (x : R i) => ∑ y : R i,
      if v i * x - u i * y = k i then f i x * star (g i y) else (0 : ℂ))).symm

theorem fullCorrelation_idealCRT {S ι : Type*} [CommRing S] [Fintype ι]
    (I : ι → Ideal S) (hI : Pairwise (Function.onFun IsCoprime I))
    [Fintype (S ⧸ ⨅ i, I i)] [∀ i, Fintype (S ⧸ I i)]
    (u v k : S ⧸ ⨅ i, I i) (f g : ∀ i, S ⧸ I i → ℂ) :
    let e := Ideal.quotientInfRingEquivPiQuotient I hI
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => ∏ i, f i (e x i)) (fun y => ∏ i, g i (e y i)) k =
      ∏ i, fullCorrelation (fun x => e v i * x) (fun y => e u i * y)
        (f i) (g i) (e k i) := by
  classical
  dsimp only
  rw [fullCorrelation_ringEquiv (Ideal.quotientInfRingEquivPiQuotient I hI) u v k
    (fun x => ∏ i, f i (x i)) (fun y => ∏ i, g i (y i)), fullCorrelation_pi]

def crtCharacter {S ι : Type*} [CommRing S] [Fintype ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] (e : S ≃+* (∀ i, R i)) (χ : ∀ i, MulChar (R i) ℂ) :
    MulChar S ℂ where
  toFun x := ∏ i, χ i (e x i)
  map_one' := by simp
  map_mul' := by intro x y; simp [map_mul, Finset.prod_mul_distrib]
  map_nonunit' := by
    intro x hx
    have hn : ¬IsUnit (e x) := fun h => hx ((isUnit_map_iff e x).mp h)
    have hsome : ∃ i, ¬IsUnit (e x i) := by
      by_contra h
      apply hn
      exact Pi.isUnit_iff.mpr (by simpa only [not_exists, not_not] using h)
    obtain ⟨i, hi⟩ := hsome
    exact Finset.prod_eq_zero (Finset.mem_univ i) ((χ i).map_nonunit hi)

@[simp] theorem crtCharacter_apply {S ι : Type*} [CommRing S] [Fintype ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] (e : S ≃+* (∀ i, R i)) (χ : ∀ i, MulChar (R i) ℂ) (x : S) :
    crtCharacter e χ x = ∏ i, χ i (e x i) := rfl

end
end SevenEighths.CenteredMomentCorrelation

end OAI
end OAIOriginalModule0050

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FullCorrelation
Source SHA256: 1ca3f1b22920fbc75dd7f41351aebd6293db8a421196210048175e235d51ef65
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0051



namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCorrelation
variable {A : Type*} [CommRing A]

def scaledResidue (d a m : A) (hm : m = d * a) :
    (A ⧸ Ideal.span {d}) → (A ⧸ Ideal.span {m}) := fun x =>
  Quotient.liftOn' x (fun z => Ideal.Quotient.mk (Ideal.span {m}) (a * z)) (by
    intro x y hxy
    apply Ideal.Quotient.eq.mpr
    have hd : d ∣ x - y := Ideal.mem_span_singleton.mp
      ((Ideal.span {d}).quotientRel_def.mp hxy)
    apply Ideal.mem_span_singleton.mpr
    obtain ⟨z, hz⟩ := hd
    refine ⟨z, ?_⟩
    rw [hm, ← mul_sub, hz]
    ring)

@[simp] theorem scaledResidue_mk (d a m : A) (hm : m = d * a) (x : A) :
    scaledResidue d a m hm (Ideal.Quotient.mk (Ideal.span {d}) x) =
      Ideal.Quotient.mk (Ideal.span {m}) (a * x) := rfl

def fullModulusCorrelation (u v : A)
    [Fintype (A ⧸ Ideal.span {u})] [Fintype (A ⧸ Ideal.span {v})]
    (χu : MulChar (A ⧸ Ideal.span {u}) ℂ)
    (χv : MulChar (A ⧸ Ideal.span {v}) ℂ) (j : A) : ℂ :=
  fullCorrelation (scaledResidue u v (u * v) rfl)
    (scaledResidue v u (u * v) (mul_comm u v)) χu χv
    (Ideal.Quotient.mk (Ideal.span {u * v}) j)

theorem scaledResidue_congruence (u v x y j : A) :
    scaledResidue u v (u * v) rfl (Ideal.Quotient.mk (Ideal.span {u}) x) -
      scaledResidue v u (u * v) (mul_comm u v)
        (Ideal.Quotient.mk (Ideal.span {v}) y) =
      Ideal.Quotient.mk (Ideal.span {u * v}) j ↔
      u * v ∣ v * x - u * y - j := by
  rw [scaledResidue_mk, scaledResidue_mk, ← map_sub, Ideal.Quotient.eq]
  exact Ideal.mem_span_singleton

theorem fullModulusCorrelation_fourier (u v : A)
    [Fintype (A ⧸ Ideal.span {u})] [Fintype (A ⧸ Ideal.span {v})]
    [Fintype (A ⧸ Ideal.span {u * v})]
    (χu : MulChar (A ⧸ Ideal.span {u}) ℂ)
    (χv : MulChar (A ⧸ Ideal.span {v}) ℂ) (j : A)
    (ψ : AddChar (A ⧸ Ideal.span {u * v}) ℂ) (hψ : ψ.IsPrimitive) :
    (∑ h : A ⧸ Ideal.span {u * v},
      fourierSum ψ (scaledResidue u v (u * v) rfl) χu h *
        star (fourierSum ψ (scaledResidue v u (u * v) (mul_comm u v)) χv h) *
          ψ (-(h * Ideal.Quotient.mk (Ideal.span {u * v}) j))) =
      (Fintype.card (A ⧸ Ideal.span {u * v}) : ℂ) * fullModulusCorrelation u v χu χv j :=
  fullCorrelation_fourier ψ hψ _ _ χu χv _

theorem common_divisor_frequency {u v d x y j : A}
    (hdu : d ∣ u) (hdv : d ∣ v) (hcong : u * v ∣ v * x - u * y - j) : d ∣ j := by
  have hleft : d ∣ v * x - u * y := dvd_sub (hdv.trans (dvd_mul_right v x))
    (hdu.trans (dvd_mul_right u y))
  have hprod : d ∣ u * v := hdu.trans (dvd_mul_right u v)
  have hdiff := dvd_sub hleft (hprod.trans hcong)
  convert hdiff using 1 ; ring

theorem fullModulusCorrelation_eq_zero_of_common_not_dvd (u v d j : A)
    [Fintype (A ⧸ Ideal.span {u})] [Fintype (A ⧸ Ideal.span {v})]
    (χu : MulChar (A ⧸ Ideal.span {u}) ℂ)
    (χv : MulChar (A ⧸ Ideal.span {v}) ℂ)
    (hdu : d ∣ u) (hdv : d ∣ v) (hdj : ¬d ∣ j) :
    fullModulusCorrelation u v χu χv j = 0 := by
  unfold fullModulusCorrelation fullCorrelation
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  refine Quotient.inductionOn₂' x y ?_
  intro a b
  have hn : ¬ scaledResidue u v (u * v) rfl (Ideal.Quotient.mk (Ideal.span {u}) a) -
      scaledResidue v u (u * v) (mul_comm u v) (Ideal.Quotient.mk (Ideal.span {v}) b) =
      Ideal.Quotient.mk (Ideal.span {u * v}) j := by
    intro h
    exact hdj (common_divisor_frequency hdu hdv ((scaledResidue_congruence u v a b j).mp h))
  exact ite_eq_right hn

theorem dvd_of_unit_residue_mul {u x v : A}
    (hx : IsUnit (Ideal.Quotient.mk (Ideal.span {u}) x)) (hdiv : u ∣ v * x) : u ∣ v := by
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hm : Ideal.Quotient.mk (Ideal.span {u}) v *
      Ideal.Quotient.mk (Ideal.span {u}) x = 0 := by
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv)
  exact hx.mul_right_injective (by simpa only [mul_comm, mul_zero, zero_mul] using hm)

theorem zero_frequency_units_force_divides {u v x y : A}
    (hx : IsUnit (Ideal.Quotient.mk (Ideal.span {u}) x))
    (hy : IsUnit (Ideal.Quotient.mk (Ideal.span {v}) y))
    (hcong : u * v ∣ v * x - u * y) : u ∣ v ∧ v ∣ u := by
  have hu : u ∣ v * x := by
    have h := dvd_add ((dvd_mul_right u v).trans hcong) (dvd_mul_right u y)
    simpa only [sub_add_cancel] using h
  have hv : v ∣ u * y := by
    have h := dvd_sub (dvd_mul_right v x) ((dvd_mul_left v u).trans hcong)
    convert h using 1 ; ring
  exact ⟨dvd_of_unit_residue_mul hx hu, dvd_of_unit_residue_mul hy hv⟩

theorem fullModulusCorrelation_zero_frequency_off_diagonal (u v : A)
    [Fintype (A ⧸ Ideal.span {u})] [Fintype (A ⧸ Ideal.span {v})]
    (χu : MulChar (A ⧸ Ideal.span {u}) ℂ)
    (χv : MulChar (A ⧸ Ideal.span {v}) ℂ)
    (hne : Ideal.span ({u} : Set A) ≠ Ideal.span ({v} : Set A)) :
    fullModulusCorrelation u v χu χv 0 = 0 := by
  classical
  unfold fullModulusCorrelation fullCorrelation
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  refine Quotient.inductionOn₂' x y ?_
  intro a b
  change (if scaledResidue u v (u * v) rfl (Ideal.Quotient.mk (Ideal.span {u}) a) -
      scaledResidue v u (u * v) (mul_comm u v) (Ideal.Quotient.mk (Ideal.span {v}) b) =
      Ideal.Quotient.mk (Ideal.span {u * v}) 0
    then χu (Ideal.Quotient.mk (Ideal.span {u}) a) *
      star (χv (Ideal.Quotient.mk (Ideal.span {v}) b)) else 0) = 0
  by_cases hx : χu (Ideal.Quotient.mk (Ideal.span {u}) a) = 0
  · simp only [hx, zero_mul, ite_self]
  by_cases hy : χv (Ideal.Quotient.mk (Ideal.span {v}) b) = 0
  · simp only [hy, star_zero, mul_zero, ite_self]
  split_ifs with h
  · exfalso
    have hd := (scaledResidue_congruence u v a b 0).mp h
    rw [sub_zero] at hd
    obtain ⟨huv, hvu⟩ := zero_frequency_units_force_divides
      (χu.apply_ne_zero_iff.mp hx) (χv.apply_ne_zero_iff.mp hy) hd
    apply hne
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact Ideal.mem_span_singleton.mpr hvu
    · apply Ideal.span_le.mpr
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact Ideal.mem_span_singleton.mpr huv
  · rfl

variable [IsDomain A]

theorem scaledResidue_injective (d a m : A) (hm : m = d * a) (ha : a ≠ 0) :
    Function.Injective (scaledResidue d a m hm) := by
  intro x y
  refine Quotient.inductionOn₂' x y ?_
  intro r s hrs
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_singleton.mpr
  have hd := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hrs)
  change m ∣ a * r - a * s at hd
  rw [hm, ← mul_sub, mul_comm d a] at hd
  exact (mul_dvd_mul_iff_left ha).mp hd

theorem fullModulusCorrelation_zero_frequency_diagonal (u : A) (hu : u ≠ 0)
    [Fintype (A ⧸ Ideal.span {u})] (χ : MulChar (A ⧸ Ideal.span {u}) ℂ) :
    fullModulusCorrelation u u χ χ 0 =
      (Fintype.card (A ⧸ Ideal.span {u})ˣ : ℂ) := by
  classical
  have hinj := scaledResidue_injective u u (u * u) rfl hu
  unfold fullModulusCorrelation fullCorrelation
  have hcond (x y : A ⧸ Ideal.span {u}) :
      scaledResidue u u (u * u) rfl x -
        scaledResidue u u (u * u) (mul_comm u u) y =
        Ideal.Quotient.mk (Ideal.span {u * u}) 0 ↔ y = x := by
    rw [map_zero, sub_eq_zero]
    exact hinj.eq_iff.trans eq_comm
  simp only [hcond, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    MulChar.star_apply', ← MulChar.mul_apply, mul_inv_cancel]
  exact MulChar.sum_one_eq_card_units

end SevenEighths.CenteredMomentCorrelation
end

end OAI
end OAIOriginalModule0051

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramCommonParam
Source SHA256: 8e7b58b840b0c14f5118402a93cf7c10a57692530c3f083c3f760629f8acc334
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0052


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A] [IsDomain A]
abbrev ResidueQ (a : A) := A⧸Ideal.span {a}

def condition (C n₁ n₂ k : A) (p : ResidueQ (C*n₁) × ResidueQ (C*n₂)) : Prop :=
  scaledResidue (C*n₁) (C*n₂) ((C*n₁)*(C*n₂)) rfl p.1-
    scaledResidue (C*n₂) (C*n₁) ((C*n₁)*(C*n₂)) (mul_comm _ _) p.2=
    Ideal.Quotient.mk (Ideal.span {(C*n₁)*(C*n₂)}) (C*k)

abbrev Solutions (C n₁ n₂ k : A) := {p : ResidueQ (C*n₁) × ResidueQ (C*n₂) // condition C n₁ n₂ k p}

def leftParam (C n₁ b k : A) (t : ResidueQ C) : ResidueQ (C*n₁) :=
  Ideal.Quotient.mk _ (b*k)+scaledResidue C n₁ (C*n₁) rfl t

def rightParam (C n₂ a k : A) (t : ResidueQ C) : ResidueQ (C*n₂) :=
  Ideal.Quotient.mk _ (-a*k)+scaledResidue C n₂ (C*n₂) rfl t

omit [IsDomain A] in
@[simp] lemma leftParam_mk (C n₁ b k t : A) :
    leftParam C n₁ b k (Ideal.Quotient.mk _ t)=Ideal.Quotient.mk _ (b*k+n₁*t) := by
  simp only [leftParam,scaledResidue_mk,map_add]

omit [IsDomain A] in
@[simp] lemma rightParam_mk (C n₂ a k t : A) :
    rightParam C n₂ a k (Ideal.Quotient.mk _ t)=Ideal.Quotient.mk _ (-a*k+n₂*t) := by
  simp only [rightParam,scaledResidue_mk,map_add]

omit [IsDomain A] in
lemma param_condition (C n₁ n₂ a b k : A) (hab : a*n₁+b*n₂=1) (t : ResidueQ C) :
    condition C n₁ n₂ k (leftParam C n₁ b k t,rightParam C n₂ a k t) := by
  obtain ⟨t,rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [leftParam_mk,rightParam_mk]
  unfold condition
  rw [scaledResidue_congruence]
  have he : C*n₂*(b*k+n₁*t)-C*n₁*(-a*k+n₂*t)-C*k=C*k*(a*n₁+b*n₂-1) := by ring
  rw [he,hab,sub_self,mul_zero]
  exact dvd_zero _

def param (C n₁ n₂ a b k : A) (hab : a*n₁+b*n₂=1) (t : ResidueQ C) : Solutions C n₁ n₂ k :=
  ⟨(leftParam C n₁ b k t,rightParam C n₂ a k t),param_condition C n₁ n₂ a b k hab t⟩

lemma param_injective (C n₁ n₂ a b k : A) (hab : a*n₁+b*n₂=1) (hn₁ : n₁≠0) :
    Function.Injective (param C n₁ n₂ a b k hab) := by
  intro t u he
  have hl : leftParam C n₁ b k t=leftParam C n₁ b k u := congrArg (fun p=>p.val.1) he
  apply scaledResidue_injective C n₁ (C*n₁) rfl hn₁
  exact add_left_cancel hl

lemma condition_divided (C n₁ n₂ k x y : A) (hC : C≠0)
    (hc : condition C n₁ n₂ k (Ideal.Quotient.mk _ x,Ideal.Quotient.mk _ y)) :
    C*n₁*n₂∣n₂*x-n₁*y-k := by
  unfold condition at hc
  rw [scaledResidue_congruence] at hc
  have hh : C*(C*n₁*n₂)∣C*(n₂*x-n₁*y-k) := by convert hc using 1 <;> ring
  exact (mul_dvd_mul_iff_left hC).mp hh

lemma param_surjective (C n₁ n₂ a b k : A) (hC : C≠0) (hab : a*n₁+b*n₂=1) :
    Function.Surjective (param C n₁ n₂ a b k hab) := by
  intro p
  obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective p.val.1
  obtain ⟨y,hy⟩ := Ideal.Quotient.mk_surjective p.val.2
  have hc : condition C n₁ n₂ k (Ideal.Quotient.mk _ x,Ideal.Quotient.mk _ y) := by
    rw [hx,hy]
    exact p.property
  have hd := condition_divided C n₁ n₂ k x y hC hc
  refine ⟨Ideal.Quotient.mk _ (a*x+b*y),?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change leftParam C n₁ b k (Ideal.Quotient.mk _ (a*x+b*y))=p.val.1
    rw [leftParam_mk,←hx,Ideal.Quotient.eq]
    apply Ideal.mem_span_singleton.mpr
    have hh : C*n₁∣n₂*x-n₁*y-k := (dvd_mul_right (C*n₁) n₂).trans hd
    have he : b*k+n₁*(a*x+b*y)-x= -b*(n₂*x-n₁*y-k) := by
      linear_combination x*hab
    rw [he]
    exact dvd_mul_of_dvd_right hh _
  · change rightParam C n₂ a k (Ideal.Quotient.mk _ (a*x+b*y))=p.val.2
    rw [rightParam_mk,←hy,Ideal.Quotient.eq]
    apply Ideal.mem_span_singleton.mpr
    have hh : C*n₂∣n₂*x-n₁*y-k := by
      apply dvd_trans _ hd
      exact ⟨n₁,by ring⟩
    have he : -a*k+n₂*(a*x+b*y)-y=a*(n₂*x-n₁*y-k) := by
      linear_combination y*hab
    rw [he]
    exact dvd_mul_of_dvd_right hh _

def solutionEquiv (C n₁ n₂ a b k : A) (hC : C≠0) (hn₁ : n₁≠0)
    (hab : a*n₁+b*n₂=1) : ResidueQ C≃Solutions C n₁ n₂ k :=
  Equiv.ofBijective (param C n₁ n₂ a b k hab)
    ⟨param_injective C n₁ n₂ a b k hab hn₁,param_surjective C n₁ n₂ a b k hC hab⟩

@[simp] lemma solutionEquiv_val (C n₁ n₂ a b k : A) (hC : C≠0) (hn₁ : n₁≠0)
    (hab : a*n₁+b*n₂=1) (t : ResidueQ C) :
    (solutionEquiv C n₁ n₂ a b k hC hn₁ hab t).val=(leftParam C n₁ b k t,rightParam C n₂ a k t) := rfl

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule0052

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramCommonLinear
Source SHA256: 8e3a9c94eefe0a667e4bac935d71b54f325d05f2d22c57acaad6df1e2a2e3405
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0053


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {R : Type*} [CommRing R]

def bezoutPairEquiv (n₁ n₂ a b : R) (hab : a*n₁+b*n₂=1) : R×R≃R×R where
  toFun p := (b*p.2+n₁*p.1,-a*p.2+n₂*p.1)
  invFun p := (a*p.1+b*p.2,n₂*p.1-n₁*p.2)
  left_inv p := by
    apply Prod.ext
    · dsimp only
      linear_combination p.1*hab
    · dsimp only
      linear_combination p.2*hab
  right_inv p := by
    apply Prod.ext
    · dsimp only
      linear_combination p.1*hab
    · dsimp only
      linear_combination p.2*hab

theorem fullCorrelation_bezout [Fintype R] (n₁ n₂ a b k : R) (hab : a*n₁+b*n₂=1)
    (f g : R→ℂ) :
    fullCorrelation (fun x=>n₂*x) (fun y=>n₁*y) f g k=
      ∑t : R,f (b*k+n₁*t)*star (g (-a*k+n₂*t)) := by
  unfold fullCorrelation
  rw [←Fintype.sum_prod_type (fun p : R×R=>if n₂*p.1-n₁*p.2=k then f p.1*star (g p.2) else 0)]
  have he := (Fintype.sum_equiv (bezoutPairEquiv n₁ n₂ a b hab)
    (fun p : R×R=>if p.2=k then f (b*p.2+n₁*p.1)*star (g (-a*p.2+n₂*p.1)) else 0)
    (fun p : R×R=>if n₂*p.1-n₁*p.2=k then f p.1*star (g p.2) else 0) (by
      intro p
      have hh : n₂*(b*p.2+n₁*p.1)-n₁*(-a*p.2+n₂*p.1)=p.2 := by
        linear_combination p.2*hab
      change (if p.2=k then _ else 0)=(if n₂*(b*p.2+n₁*p.1)-n₁*(-a*p.2+n₂*p.1)=k then _ else 0)
      rw [hh]
      rfl)).symm
  rw [he,Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem fullCorrelation_bezout_norm [Fintype R] (n₁ n₂ a b k : R) (hab : a*n₁+b*n₂=1)
    (f g : R→ℂ) (hf : ∀x,‖f x‖≤1) (hg : ∀x,‖g x‖≤1) :
    ‖fullCorrelation (fun x=>n₂*x) (fun y=>n₁*y) f g k‖≤(Fintype.card R:ℝ) := by
  rw [fullCorrelation_bezout n₁ n₂ a b k hab]
  calc
    _ ≤ ∑t : R,‖f (b*k+n₁*t)*star (g (-a*k+n₂*t))‖ := norm_sum_le _ _
    _ ≤ ∑_t : R,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [norm_mul,norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf _)).trans (hg _)
    _ = _ := by simp

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule0053

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramCommonSum
Source SHA256: 9a535de804ab686b34673b4729493d2c875381ffdd8b03cb8e16d4e527ae1568
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0054


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A] [IsDomain A]

omit [IsDomain A] in
lemma fullModulusCorrelation_solutions (C n₁ n₂ k : A)
    [Fintype (ResidueQ (C*n₁))] [Fintype (ResidueQ (C*n₂))]
    (χ : MulChar (ResidueQ (C*n₁)) ℂ) (ψ : MulChar (ResidueQ (C*n₂)) ℂ) :
    fullModulusCorrelation (C*n₁) (C*n₂) χ ψ (C*k)=
      ∑p : Solutions C n₁ n₂ k,χ p.val.1*star (ψ p.val.2) := by
  unfold fullModulusCorrelation fullCorrelation
  change (∑x : ResidueQ (C*n₁),∑y : ResidueQ (C*n₂),
    if condition C n₁ n₂ k (x,y) then χ x*star (ψ y) else 0)=_
  rw [←Fintype.sum_prod_type (fun p : ResidueQ (C*n₁)×ResidueQ (C*n₂)=>
    if condition C n₁ n₂ k p then χ p.1*star (ψ p.2) else 0)]
  change (∑p : ResidueQ (C*n₁)×ResidueQ (C*n₂),
    if condition C n₁ n₂ k p then χ p.1*star (ψ p.2) else 0)=_
  rw [←Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

theorem fullModulusCorrelation_parameter (C n₁ n₂ a b k : A) (hC : C≠0) (hn₁ : n₁≠0)
    (hab : a*n₁+b*n₂=1)
    [Fintype (ResidueQ C)] [Fintype (ResidueQ (C*n₁))] [Fintype (ResidueQ (C*n₂))]
    (χ : MulChar (ResidueQ (C*n₁)) ℂ) (ψ : MulChar (ResidueQ (C*n₂)) ℂ) :
    fullModulusCorrelation (C*n₁) (C*n₂) χ ψ (C*k)=
      ∑t : ResidueQ C,χ (leftParam C n₁ b k t)*star (ψ (rightParam C n₂ a k t)) := by
  rw [fullModulusCorrelation_solutions]
  symm
  exact Fintype.sum_equiv (solutionEquiv C n₁ n₂ a b k hC hn₁ hab) _ _ (fun _=>rfl)

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule0054

/-! Original module: OAI.NumberTheory.DirichletL.Moments.PrimePower
Source SHA256: bc1c13575d102be643e58ccf58777559f8dacb3529caae27c08fab91218bcc55
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0055






namespace OAI

open scoped BigOperators Classical
open NumberField
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
local instance : Infinite (𝓞 K) := Module.Free.infinite ℤ (𝓞 K)

def primePowerReduction (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c) :
    (𝓞 K ⧸ P ^ c) →+* (𝓞 K ⧸ P) :=
  Ideal.Quotient.factor (by simpa using Ideal.pow_le_pow_right (I := P) hc)

omit [NumberField K] in
theorem primePowerReduction_surjective (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c) :
    Function.Surjective (primePowerReduction P hc) :=
  Ideal.Quotient.factor_surjective _

theorem primePowerReduction_multiplicity (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c)
    [Fintype (𝓞 K ⧸ P ^ c)] [Fintype (𝓞 K ⧸ P)] :
    reductionMultiplicity (primePowerReduction P hc) = Ideal.absNorm P ^ (c - 1) := by
  have hcard (I : Ideal (𝓞 K)) [Fintype (𝓞 K ⧸ I)] :
      Fintype.card (𝓞 K ⧸ I) = Ideal.absNorm I := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  refine reductionMultiplicity_eq_pow _ (primePowerReduction_surjective P hc)
      (P := Ideal.absNorm P) ?_ hc ?_ ?_
  · rw [← hcard P]
    exact Fintype.card_pos
  · rw [hcard, map_pow]
  · exact hcard P

def primePowerCharacter (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c)
    (χ : MulChar (𝓞 K ⧸ P) ℂ) : MulChar (𝓞 K ⧸ P ^ c) ℂ where
  __ := χ.toMonoidHom.comp (primePowerReduction P hc).toMonoidHom
  map_nonunit' := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change χ (Ideal.Quotient.mk P a) = 0
    apply χ.map_nonunit
    intro ha
    exact hx ((Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P (by omega)).mpr ha)

omit [NumberField K] in
@[simp] theorem primePowerCharacter_apply (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c)
    (χ : MulChar (𝓞 K ⧸ P) ℂ) (x : 𝓞 K ⧸ P ^ c) :
    primePowerCharacter P hc χ x = χ (primePowerReduction P hc x) := rfl

section Local
variable (P : Ideal (𝓞 K)) [P.IsMaximal] {c : ℕ} (hc : 1 ≤ c)
variable [Fintype (𝓞 K ⧸ P ^ c)] [Fintype (𝓞 K ⧸ P)]
local instance : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P

theorem primePower_localCorrelation (χ : MulChar (𝓞 K ⧸ P) ℂ)
    (u : (𝓞 K ⧸ P ^ c)ˣ) (v k : 𝓞 K ⧸ P ^ c) :
    fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ P ^ c) * y)
      (fun x => (χ ^ c) (primePowerReduction P hc x))
      (fun y => (χ ^ c) (primePowerReduction P hc y)) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      localCorrelation (χ ^ c) (primePowerReduction P hc u)
        (primePowerReduction P hc v) (primePowerReduction P hc k) := by
  rw [fullCorrelation_reduction_unit_right _ (primePowerReduction_surjective P hc),
    primePowerReduction_multiplicity, Nat.cast_pow]
  rfl

theorem primePower_localCorrelation_units (χ : MulChar (𝓞 K ⧸ P) ℂ)
    (hχ : orderOf χ = 6) (u : (𝓞 K ⧸ P ^ c)ˣ) (v k : 𝓞 K ⧸ P ^ c)
    (hv : primePowerReduction P hc v ≠ 0) :
    fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ P ^ c) * y)
      (fun x => (χ ^ c) (primePowerReduction P hc x))
      (fun y => (χ ^ c) (primePowerReduction P hc y)) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      χ (primePowerReduction P hc u / primePowerReduction P hc v) ^ c *
      (if primePowerReduction P hc k = 0 then (Ideal.absNorm P : ℂ) - 1
       else if 6 ∣ c then (Ideal.absNorm P : ℂ) - 2 else -1) := by
  have hu : primePowerReduction P hc u ≠ 0 :=
    (isUnit_iff_ne_zero.mp (u.isUnit.map (primePowerReduction P hc)))
  have hpow : χ ^ c = 1 ↔ 6 ∣ c := by rw [← orderOf_dvd_iff_pow_eq_one, hχ]
  have hcard : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [primePower_localCorrelation, localCorrelation_units _ hu hv,
    MulChar.pow_apply' _ (by omega), hcard, hpow, mul_assoc]
  split_ifs <;> rfl

theorem primePower_localCorrelation_second_zero (χ : MulChar (𝓞 K ⧸ P) ℂ)
    (hχ : orderOf χ = 6) (u : (𝓞 K ⧸ P ^ c)ˣ) (v k : 𝓞 K ⧸ P ^ c)
    (hv : primePowerReduction P hc v = 0) :
    fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ P ^ c) * y)
      (fun x => (χ ^ c) (primePowerReduction P hc x))
      (fun y => (χ ^ c) (primePowerReduction P hc y)) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      (if 6 ∣ c ∧ primePowerReduction P hc k ≠ 0
       then (Ideal.absNorm P : ℂ) - 1 else 0) := by
  have hu : primePowerReduction P hc u ≠ 0 :=
    (isUnit_iff_ne_zero.mp (u.isUnit.map (primePowerReduction P hc)))
  have hpow : χ ^ c = 1 ↔ 6 ∣ c := by rw [← orderOf_dvd_iff_pow_eq_one, hχ]
  have hcard : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [primePower_localCorrelation, hv, localCorrelation_second_zero _ hu, hcard, hpow]
  split_ifs <;> rfl

theorem primePower_localCorrelation_first_zero (χ : MulChar (𝓞 K ⧸ P) ℂ)
    (hχ : orderOf χ = 6) (u : 𝓞 K ⧸ P ^ c) (v : (𝓞 K ⧸ P ^ c)ˣ)
    (k : 𝓞 K ⧸ P ^ c) (hu : primePowerReduction P hc u = 0) :
    fullCorrelation (fun x => (v : 𝓞 K ⧸ P ^ c) * x) (fun y => u * y)
      (fun x => (χ ^ c) (primePowerReduction P hc x))
      (fun y => (χ ^ c) (primePowerReduction P hc y)) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      (if 6 ∣ c ∧ primePowerReduction P hc k ≠ 0
       then (Ideal.absNorm P : ℂ) - 1 else 0) := by
  have hv : primePowerReduction P hc v ≠ 0 :=
    (isUnit_iff_ne_zero.mp (v.isUnit.map (primePowerReduction P hc)))
  have hpow : χ ^ c = 1 ↔ 6 ∣ c := by rw [← orderOf_dvd_iff_pow_eq_one, hχ]
  have hcard : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [fullCorrelation_reduction_unit_left _ (primePowerReduction_surjective P hc),
    primePowerReduction_multiplicity, Nat.cast_pow]
  change (Ideal.absNorm P : ℂ) ^ (c - 1) *
      localCorrelation (χ ^ c) (primePowerReduction P hc u)
        (primePowerReduction P hc v) (primePowerReduction P hc k) = _
  rw [hu, localCorrelation_first_zero _ hv, hcard, hpow]
  split_ifs <;> rfl

end Local
end
end SevenEighths.CenteredMomentCorrelation

end OAI
end OAIOriginalModule0055

/-! Original module: OAI.NumberTheory.DirichletL.Parameters
Source SHA256: 32b77db1ea32e62c931063764ae60738e84737edb39a5f7d2cb40b15ee8ed424
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0056







namespace OAI

namespace SevenEighths.Parameters

theorem compensated_geometry {d : ℝ} (_hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 6) :
    (1 / 2 : ℝ) ≤ 5 / 6 - 2 * d ∧
    3 / 16 ≤ 17 / 48 - d ∧
    5 / 16 ≤ 23 / 48 - d ∧
    1 / 12 ≤ 23 / 48 - d - 11 * (1 / 8) / 6 ∧
    (17 / 48 : ℝ) / 2 + (1 / 8) / 12 = 3 / 16 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · norm_num

theorem exists_height_cutoff {dmin allowance A : ℝ}
    (hd : 0 < dmin) (ha : 0 < allowance) (hA : 0 ≤ A) :
    ∃ τ : ℝ, 0 < τ ∧ τ < dmin / 100 ∧
      A * τ < dmin * allowance / 100 := by
  have hden : 0 < 200 * (1 + A) := by positivity
  let τ := min (dmin / 200) (dmin * allowance / (200 * (1 + A)))
  have ht : 0 < τ := lt_min (by positivity) (by positivity)
  have h1 : τ ≤ dmin / 200 := min_le_left _ _
  have h2 : τ ≤ dmin * allowance / (200 * (1 + A)) := min_le_right _ _
  have h2' : τ * (200 * (1 + A)) ≤ dmin * allowance :=
    (le_div_iff₀ hden).mp h2
  refine ⟨τ, ht, by linarith, ?_⟩
  have hp : 0 < dmin * allowance := mul_pos hd ha
  nlinarith

theorem exists_tail_order {τ B saving : ℝ} (hτ : 0 < τ) :
    ∃ N : ℕ, B - τ * N < -saving := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((B + saving) / τ)
  have h := (div_lt_iff₀ hτ).mp hN
  exact ⟨N, by nlinarith⟩

theorem cumulative_frequency_bound {ι : Type*} (s : Finset ι)
    (frequency : ι → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hfreq : ∀ i ∈ s, |frequency i| ≤ T / (4 * s.card)) :
    |∑ i ∈ s, frequency i| ≤ T / 4 := by
  by_cases hs : s.card = 0
  · have he : s = ∅ := Finset.card_eq_zero.mp hs
    simp only [he, Finset.sum_empty, abs_zero]
    positivity
  · have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs
    calc
      |∑ i ∈ s, frequency i| ≤ ∑ i ∈ s, |frequency i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ s, T / (4 * s.card) := Finset.sum_le_sum hfreq
      _ = T / 4 := by simp only [Finset.sum_const, nsmul_eq_mul]; field_simp

end SevenEighths.Parameters

end OAI
end OAIOriginalModule0056

/-! Original module: OAI.NumberTheory.DirichletL.ParametersSlotLengths
Source SHA256: f52f5f4282489ffce669a9ebdf91766990fa6c2d7e15178c60d4ec69cb3c0ef6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0057




namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.Parameters

theorem exists_distinct_slot_lengths (L : ℝ) (hL : 0<L) :
    ∃N : ℕ,0<N ∧ ∃ell : Fin N→ℝ,Function.Injective ell ∧
      (∀j,0<ell j ∧ ell j<L) ∧ (∑j,ell j)=1/6 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (1/(3*L)))
  have hN1 : (1:ℝ)<N := (le_max_left _ _).trans_lt hN
  have hNp : 0<(N:ℝ) := by linarith
  have hNnat : 0<N := by exact_mod_cast hNp
  have hNL : 1/(3*L)<(N:ℝ) := (le_max_right _ _).trans_lt hN
  have hsmall : 1/(3*(N:ℝ))<L := by
    have hh := (div_lt_iff₀ (show 0<3*L by positivity)).mp hNL
    apply (div_lt_iff₀ (show 0<3*(N:ℝ) by positivity)).mpr
    nlinarith
  let w : Fin N→ℝ := fun j=>1+(j.val:ℝ)/(N:ℝ)
  let A : ℝ := ∑j,w j
  have hw (j : Fin N) : 1≤w j ∧ w j<2 := by
    have hj : (j.val:ℝ)<N := by exact_mod_cast j.isLt
    have hdiv : (j.val:ℝ)/(N:ℝ)<1 := (div_lt_one hNp).mpr hj
    dsimp only [w]
    constructor
    · linarith [div_nonneg (Nat.cast_nonneg j.val) hNp.le]
    · linarith
  have hA : (N:ℝ)≤A := by
    calc
      _ = ∑_j : Fin N,(1:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _=>(hw j).1
  have hAp : 0<A := hNp.trans_le hA
  let ell : Fin N→ℝ := fun j=>w j/(6*A)
  refine ⟨N,hNnat,ell,?_,?_,?_⟩
  · intro j k he
    have hden : 6*A≠0 := by positivity
    have hwjk : w j=w k := (div_left_inj' hden).mp he
    have hjk : (j.val:ℝ)/(N:ℝ)=(k.val:ℝ)/(N:ℝ) := by dsimp [w] at hwjk;linarith
    have he' : (j.val:ℝ)=(k.val:ℝ) := (div_left_inj' hNp.ne').mp hjk
    apply Fin.ext
    exact_mod_cast he'
  · intro j
    constructor
    · exact div_pos (by linarith [(hw j).1]) (by positivity)
    · calc
        ell j < 2/(6*A) := (div_lt_div_iff_of_pos_right (by positivity)).mpr (hw j).2
        _ ≤ 2/(6*(N:ℝ)) := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
        _ = 1/(3*(N:ℝ)) := by ring
        _ < L := hsmall
  · dsimp only [ell]
    rw [←Finset.sum_div]
    change A/(6*A)=1/6
    field_simp

theorem exists_physical_slot_lengths (dmin dmax mesh R : ℝ)
    (hdmin : 0<dmin) (hd : dmin≤dmax) (hm : 0<mesh) (hR : 0<R) :
    ∃N : ℕ,0<N ∧ ∃ell : Fin N→ℝ,∃rmin : ℝ,0<rmin ∧
      Function.Injective ell ∧ (∑j,ell j)=1/6 ∧
      (∀j,0<ell j ∧ dmax*rmin≤ell j ∧ ell j≤dmin*mesh ∧ ell j≤dmin*R) ∧
      (∀d : ℝ,dmin≤d → d≤dmax → ∀j,rmin≤ell j/d ∧ ell j/d≤mesh ∧ ell j/d≤R) := by
  obtain ⟨N,hN,ell,hi,he,hS⟩ := exists_distinct_slot_lengths (dmin*min mesh R)
    (mul_pos hdmin (lt_min hm hR))
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  obtain ⟨j,hj,hjmin⟩ := Finset.exists_min_image Finset.univ ell hne
  have hmax : 0<dmax := hdmin.trans_le hd
  let rmin := ell j/(2*dmax)
  have hr : 0<rmin := div_pos (he j).1 (by positivity)
  have hlo (k : Fin N) : dmax*rmin≤ell k := by
    have hk := hjmin k (Finset.mem_univ k)
    have hiden : dmax*rmin=ell j/2 := by dsimp [rmin]; field_simp
    rw [hiden]
    linarith [(he j).1]
  have hup (k : Fin N) : ell k≤dmin*mesh ∧ ell k≤dmin*R := by
    constructor
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hdmin.le)
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hdmin.le)
  refine ⟨N,hN,ell,rmin,hr,hi,hS,fun k=>⟨(he k).1,hlo k,(hup k).1,(hup k).2⟩,?_⟩
  intro d hd' hd'' k
  have hd0 : 0<d := hdmin.trans_le hd'
  refine ⟨(le_div_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_⟩
  · exact (by nlinarith : rmin*d≤dmax*rmin).trans (hlo k)
  · exact (hup k).1.trans (by nlinarith)
  · exact (hup k).2.trans (by nlinarith)

end SevenEighths.Parameters

end

end OAI
end OAIOriginalModule0057

/-! Original module: OAI.NumberTheory.DirichletL.ParametersDetectorScales
Source SHA256: 374bbbb6e7c0cd5d08ddacdb16a2233c730a6d488eb875739369fac982de437a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0058


namespace OAI

noncomputable section
namespace SevenEighths.Parameters

theorem exists_detector_scales (R rmin mesh dmin loss ellMin allowance J : ℝ)
    (hR : 0≤R) (hr : 0<rmin) (hm : 0<mesh) (hd : 0<dmin)
    (hl : 0<loss) (hell : 0<ellMin) (ha : 0<allowance) (hJ : 0≤J) :
    ∃ε e κ cost τ : ℝ,
      0<ε ∧ ε≤1/1000 ∧ ε<rmin*mesh ∧ ε≤allowance ∧
      0<e ∧ e<1/1000 ∧ e≤ellMin/4 ∧ e≤allowance ∧
      0<κ ∧ κ≤1 ∧ 0<cost ∧
      12*e*(22+2)+8*κ+2*cost≤ε/2 ∧
      8*e*R+κ≤ε ∧
      0<τ ∧ τ<dmin/2 ∧ 4*τ<dmin*cost ∧
      2*τ*(1+J)≤loss ∧ ∀eps : ℝ,0≤eps → eps≤1 → τ*(2+4*eps)<loss := by
  let ε := min (allowance/2) (min (rmin*mesh/2) (1/2000))
  have hε : 0<ε := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hεa : ε≤allowance/2 := min_le_left _ _
  have hεr : ε≤rmin*mesh/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε1 : ε≤1/2000 := (min_le_right _ _).trans (min_le_right _ _)
  let e := min (ε/(10000*(1+R))) (min (ellMin/4) (allowance/2))
  have he : 0<e := lt_min (div_pos hε (by positivity)) (lt_min (by positivity) (by positivity))
  have heb : e≤ε/(10000*(1+R)) := min_le_left _ _
  have hep : e*(10000*(1+R))≤ε := (le_div_iff₀ (by positivity)).mp heb
  have heR : 0≤e*R := mul_nonneg he.le hR
  have hel : e≤ellMin/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hea : e≤allowance/2 := (min_le_right _ _).trans (min_le_right _ _)
  let κ := ε/1000
  let cost := ε/1000
  have hk : 0<κ := by dsimp [κ]; positivity
  have hc : 0<cost := by dsimp [cost]; positivity
  let τ := min (dmin*cost/16) (min (dmin/4) (loss/(4*(1+J+6))))
  have ht : 0<τ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have htc : τ≤dmin*cost/16 := min_le_left _ _
  have htd : τ≤dmin/4 := (min_le_right _ _).trans (min_le_left _ _)
  have htl : τ≤loss/(4*(1+J+6)) := (min_le_right _ _).trans (min_le_right _ _)
  have htJ : τ*(4*(1+J+6))≤loss := (le_div_iff₀ (by positivity)).mp htl
  have hprod : 0≤τ*J := mul_nonneg ht.le hJ
  refine ⟨ε,e,κ,cost,τ,hε,by linarith,by nlinarith [mul_pos hr hm],by linarith,
    he,by nlinarith,hel,by linarith,hk,?_,hc,?_,?_,ht,by linarith,?_,?_,?_⟩
  · dsimp [κ];linarith
  · dsimp [κ,cost];nlinarith
  · dsimp [κ];nlinarith
  · have hp := mul_pos hd hc;linarith
  · nlinarith
  · intro eps heps heps1
    have hp := mul_le_mul_of_nonneg_left heps1 ht.le
    nlinarith
end SevenEighths.Parameters

end

end OAI
end OAIOriginalModule0058

/-! Original module: OAI.NumberTheory.DirichletL.ParametersCentralBudget
Source SHA256: 9ea5e11ef3b449210791351dbdeb9766bdf5f0c8701576b9ab890101b4feaa49
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0059


namespace OAI

noncomputable section
namespace SevenEighths.Parameters

theorem exists_central_budget (Δ : ℝ) (hΔ : 0<Δ) :
    ∃ t : ℝ,0<t ∧ t<Δ/4 ∧ t≤1/100000000 ∧
      (0:ℝ)<1/200 ∧ (1/200:ℝ)<1/100 ∧
      (13/16:ℝ)+t+2*t≤7/8 ∧ (7/8:ℝ)≤37/42 ∧ t≤3/16 ∧
      0<Δ-t/4 ∧ Δ-t/4<Δ ∧
      (3/16+Δ-t+t/8+t/8 : ℝ)≤3/16+(Δ-t/4) ∧
      ∀N : ℕ,∃allowance : ℝ,0<allowance ∧
      ∀ε e eps : ℝ,0≤ε → ε≤allowance → 0≤e → e≤allowance →
        0≤eps → eps≤allowance →
        159*ε+t+t+7*t≤1/32 ∧
        (13/16)*(159*ε+t+t+7*t)+2*t+(3/2)*(2*t)+
          (26*e+(N+8)*eps+t+t/6)+(t+t+t)+t≤49/440640 := by
  let t := min (Δ/8) (1/100000000)
  have ht : 0<t := lt_min (by positivity) (by norm_num)
  have htΔ : t≤Δ/8 := min_le_left _ _
  have ht1 : t≤1/100000000 := min_le_right _ _
  refine ⟨t,ht,by linarith,ht1,by norm_num,by norm_num,by linarith,
    by norm_num,by linarith,by linarith,by linarith,by linarith,?_⟩
  intro N
  let allowance := t/((N:ℝ)+2000)
  have hden : 0<(N:ℝ)+2000 := by positivity
  have ha : 0<allowance := div_pos ht hden
  have ha0 : allowance≤t/2000 := div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N])
  have hap : allowance*((N:ℝ)+2000)=t := by dsimp [allowance];field_simp
  refine ⟨allowance,ha,?_⟩
  intro ε e eps hε hεa he hea heps hepsa
  have hεt : 2000*ε≤t := by linarith
  have het : 2000*e≤t := by linarith
  have hepsN : ((N:ℝ)+2000)*eps≤t := by
    have h := mul_le_mul_of_nonneg_left hepsa hden.le
    nlinarith
  have heps8 : ((N:ℝ)+8)*eps≤t := by nlinarith
  constructor <;> nlinarith
end SevenEighths.Parameters

end

end OAI
end OAIOriginalModule0059

/-! Original module: OAI.NumberTheory.DirichletL.ParametersHighData
Source SHA256: e1e6e123d840366a92bc252e25510da2c103540880c7ba87e1077cac68451f0d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0060


namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.Parameters

structure HighData (Δ : ℝ) where
  t : ℝ
  N : ℕ
  ell : Fin N→ℝ
  rmin : ℝ
  ε : ℝ
  e : ℝ
  κ : ℝ
  cost : ℝ
  eps : ℝ
  sigma : ℝ
  t_pos : 0<t
  t_delta : t<Δ/4
  t_small : t≤1/100000000
  slots_pos : 0<N
  slots_injective : Function.Injective ell
  slots_sum : (∑j,ell j)=1/6
  slots_bounds : ∀j,0<ell j ∧ (7/8)*rmin≤ell j ∧ ell j≤(1/200)*t
  rmin_pos : 0<rmin
  epsilon_pos : 0<ε
  epsilon_small : ε≤1/1000
  epsilon_gap : ε<rmin*t
  e_pos : 0<e
  e_small : e<1/1000
  kappa_pos : 0<κ
  kappa_small : κ≤1
  cost_pos : 0<cost
  eps_pos : 0<eps
  eps_small : eps≤1
  sigma_pos : 0<sigma
  detector_budget : 288*e+8*κ+2*cost≤ε/2
  phase_budget : 8*e*t+κ≤ε
  count_budget : 159*ε+t+t+7*t≤1/32
  central_budget : (13/16)*(159*ε+t+t+7*t)+2*t+(3/2)*(2*t)+
    (26*e+(N+8)*eps+t+t/6)+(t+t+t)+t≤49/440640
  geometric_budget : sigma+8*e+t/8≤63/800
  principal_budget : sigma+t/8≤17/48000
  window_budget : sigma+e≤(7/8)*((7/8)*rmin)
  floor_budget : 2*t+26*e+(N+8)*eps+t+t/6+t/8+sigma≤7/1200
  high_saving : sigma+t/8+t/8≤t
  height_choice : ∀J : ℝ,0≤J → ∃τ : ℝ,0<τ ∧ τ<(1/200)/2 ∧
    4*τ<(1/200)*cost ∧ τ<t ∧ 2*τ*(1+J)≤t ∧ τ*(2+4*eps)<t

theorem exists_high_data (Δ : ℝ) (hΔ : 0<Δ) : Nonempty (HighData Δ) := by
  obtain ⟨t,ht,htΔ,ht1,_,_,hgeo,hdtop,ht3,hω,hωΔ,hhigh,hallow⟩ := exists_central_budget Δ hΔ
  obtain ⟨N,hN,ell,rmin,hr,hell,hsum,hbounds,_⟩ :=
    exists_physical_slot_lengths (1/200) (7/8) t t (by norm_num) (by norm_num) ht ht
  obtain ⟨allowance,ha,hbud⟩ := hallow N
  let small := min allowance (t/((N:ℝ)+2000))
  have hsmall : 0<small := lt_min ha (div_pos ht (by positivity))
  have hsa : small≤allowance := min_le_left _ _
  have hst : small≤t/((N:ℝ)+2000) := min_le_right _ _
  have hst0 : small≤t/2000 := hst.trans
    (div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N]))
  let ellMin := (7/8:ℝ)*rmin
  have hmin : 0<ellMin := mul_pos (by norm_num) hr
  obtain ⟨ε,e,κ,cost,τ₀,hε,hε1,hεgap,hεa,he,he1,heell,hea,hκ,hκ1,hcost,
    hdet,hphase,_,_,_,_,_⟩ :=
    exists_detector_scales t rmin t (1/200) t ellMin small 0
      ht.le hr ht (by norm_num) ht hmin hsmall (by norm_num)
  let eps := small/2
  have heps : 0<eps := by dsimp [eps];positivity
  have hepss : eps≤small := by dsimp [eps];linarith only [hsmall]
  have heps1 : eps≤1 := by linarith only [hepss, hst0, ht1]
  have hbud' := hbud ε e eps hε.le (hεa.trans hsa) he.le (hea.trans hsa)
    heps.le (hepss.trans hsa)
  have heN : ((N:ℝ)+2000)*eps≤t := by
    have h := (le_div_iff₀ (show 0<(N:ℝ)+2000 by positivity)).mp (hepss.trans hst)
    simpa only [mul_comm] using h
  have he8 : ((N:ℝ)+8)*eps≤t := by nlinarith only [heN, heps.le]
  have het : 2000*e≤t := by linarith only [hea, hst0]
  let sigma := min (t/2) (ellMin/4)
  have hs : 0<sigma := lt_min (by positivity) (by positivity)
  have hst2 : sigma≤t/2 := min_le_left _ _
  have hsell : sigma≤ellMin/4 := min_le_right _ _
  refine ⟨{
    t:=t,N:=N,ell:=ell,rmin:=rmin,ε:=ε,e:=e,κ:=κ,cost:=cost,eps:=eps,sigma:=sigma
    t_pos:=ht,t_delta:=htΔ,t_small:=ht1,slots_pos:=hN,slots_injective:=hell,slots_sum:=hsum
    slots_bounds:=fun j=>⟨(hbounds j).1,(hbounds j).2.1,(hbounds j).2.2.1⟩
    rmin_pos:=hr,epsilon_pos:=hε,epsilon_small:=hε1,epsilon_gap:=hεgap
    e_pos:=he,e_small:=he1,kappa_pos:=hκ,kappa_small:=hκ1,cost_pos:=hcost
    eps_pos:=heps,eps_small:=heps1,sigma_pos:=hs,detector_budget:=by linarith only [hdet]
    phase_budget:=hphase,count_budget:=hbud'.1,central_budget:=hbud'.2
    geometric_budget:=by linarith only [hst2, het, ht1]
    principal_budget:=by linarith only [hst2, ht1]
    window_budget:=by change sigma+e≤(7/8)*ellMin;linarith only [hsell, heell, hmin]
    floor_budget:=by linarith only [hst2, het, he8, ht1]
    high_saving:=by linarith only [hst2, ht]
    height_choice:=?_ }⟩
  intro J hJ
  let τ := min ((1/200:ℝ)*cost/16) (min (1/800) (t/(4*(J+7))))
  have htau : 0<τ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have hτc : τ≤(1/200:ℝ)*cost/16 := min_le_left _ _
  have hτd : τ≤1/800 := (min_le_right _ _).trans (min_le_left _ _)
  have hτt : τ≤t/(4*(J+7)) := (min_le_right _ _).trans (min_le_right _ _)
  have hτJ : τ*(4*(J+7))≤t := (le_div_iff₀ (by positivity)).mp hτt
  have hprod : 0≤τ*J := mul_nonneg htau.le hJ
  have hprodeps := mul_le_mul_of_nonneg_left heps1 htau.le
  refine ⟨τ,htau,by linarith only [hτd],by linarith only [hτc, hcost],
      by nlinarith only [hτJ, hprod, htau],by nlinarith only [hτJ, hprod, htau],
      by nlinarith only [hτJ, hprod, hprodeps, htau]⟩
end SevenEighths.Parameters

end

end OAI
end OAIOriginalModule0060

/-! Original module: OAI.NumberTheory.DirichletL.ParametersHighDataFine
Source SHA256: 791fdccc40304508076fa534126f6bd52321411141e94faeff194081339adbd9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0061


namespace OAI

noncomputable section
open scoped BigOperators

namespace SevenEighths.Parameters

theorem exists_high_data_fine (Δ:ℝ)(hΔ:0<Δ)(mesh:ℝ→ℝ)
    (hmesh:∀t:ℝ,0<t→0<mesh t):
    ∃D:HighData Δ,∀j,D.ell j≤mesh D.t/200:=by
  obtain ⟨t,ht,htΔ,ht1,_,_,hgeo,hdtop,ht3,hω,hωΔ,hhigh,hallow⟩ := exists_central_budget Δ hΔ
  obtain ⟨N,hN,ell,rmin,hr,hell,hsum,hbounds,_⟩ :=
    exists_physical_slot_lengths (1/200) (7/8) (min t (mesh t)) t (by norm_num) (by norm_num)
      (lt_min ht (hmesh t ht)) ht
  obtain ⟨allowance,ha,hbud⟩ := hallow N
  let small := min allowance (t/((N:ℝ)+2000))
  have hsmall : 0<small := lt_min ha (div_pos ht (by positivity))
  have hsa : small≤allowance := min_le_left _ _
  have hst : small≤t/((N:ℝ)+2000) := min_le_right _ _
  have hst0 : small≤t/2000 := hst.trans
    (div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N]))
  let ellMin := (7/8:ℝ)*rmin
  have hmin : 0<ellMin := mul_pos (by norm_num) hr
  obtain ⟨ε,e,κ,cost,τ₀,hε,hε1,hεgap,hεa,he,he1,heell,hea,hκ,hκ1,hcost,
    hdet,hphase,_,_,_,_,_⟩ :=
    exists_detector_scales t rmin t (1/200) t ellMin small 0
      ht.le hr ht (by norm_num) ht hmin hsmall (by norm_num)
  let eps := small/2
  have heps : 0<eps := by dsimp [eps];positivity
  have hepss : eps≤small := by dsimp [eps];linarith only [hsmall]
  have heps1 : eps≤1 := by linarith only [hepss, hst0, ht1]
  have hbud' := hbud ε e eps hε.le (hεa.trans hsa) he.le (hea.trans hsa)
    heps.le (hepss.trans hsa)
  have heN : ((N:ℝ)+2000)*eps≤t := by
    have h := (le_div_iff₀ (show 0<(N:ℝ)+2000 by positivity)).mp (hepss.trans hst)
    simpa only [mul_comm] using h
  have he8 : ((N:ℝ)+8)*eps≤t := by nlinarith only [heN, heps.le]
  have het : 2000*e≤t := by linarith only [hea, hst0]
  let sigma := min (t/2) (ellMin/4)
  have hs : 0<sigma := lt_min (by positivity) (by positivity)
  have hst2 : sigma≤t/2 := min_le_left _ _
  have hsell : sigma≤ellMin/4 := min_le_right _ _
  refine ⟨{
    t:=t,N:=N,ell:=ell,rmin:=rmin,ε:=ε,e:=e,κ:=κ,cost:=cost,eps:=eps,sigma:=sigma
    t_pos:=ht,t_delta:=htΔ,t_small:=ht1,slots_pos:=hN,slots_injective:=hell,slots_sum:=hsum
    slots_bounds:=fun j=>⟨(hbounds j).1,(hbounds j).2.1,(hbounds j).2.2.2⟩
    rmin_pos:=hr,epsilon_pos:=hε,epsilon_small:=hε1,epsilon_gap:=hεgap
    e_pos:=he,e_small:=he1,kappa_pos:=hκ,kappa_small:=hκ1,cost_pos:=hcost
    eps_pos:=heps,eps_small:=heps1,sigma_pos:=hs,detector_budget:=by linarith only [hdet]
    phase_budget:=hphase,count_budget:=hbud'.1,central_budget:=hbud'.2
    geometric_budget:=by linarith only [hst2, het, ht1]
    principal_budget:=by linarith only [hst2, ht1]
    window_budget:=by change sigma+e≤(7/8)*ellMin;linarith only [hsell, heell, hmin]
    floor_budget:=by linarith only [hst2, het, he8, ht1]
    high_saving:=by linarith only [hst2, ht]
    height_choice:=?_ },?_⟩
  · intro J hJ
    let τ := min ((1/200:ℝ)*cost/16) (min (1/800) (t/(4*(J+7))))
    have htau : 0<τ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
    have hτc : τ≤(1/200:ℝ)*cost/16 := min_le_left _ _
    have hτd : τ≤1/800 := (min_le_right _ _).trans (min_le_left _ _)
    have hτt : τ≤t/(4*(J+7)) := (min_le_right _ _).trans (min_le_right _ _)
    have hτJ : τ*(4*(J+7))≤t := (le_div_iff₀ (by positivity)).mp hτt
    have hprod : 0≤τ*J := mul_nonneg htau.le hJ
    have hprodeps := mul_le_mul_of_nonneg_left heps1 htau.le
    refine ⟨τ,htau,by linarith only [hτd],by linarith only [hτc, hcost],
      by nlinarith only [hτJ, hprod, htau],by nlinarith only [hτJ, hprod, htau],
      by nlinarith only [hτJ, hprod, hprodeps, htau]⟩
  · intro j
    change ell j≤mesh t/200
    calc
      ell j≤(1/200:ℝ)*min t (mesh t):=(hbounds j).2.2.1
      _≤(1/200:ℝ)*mesh t:=mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _=mesh t/200:=by ring

theorem fine_slot_widths {Δ:ℝ}(D:HighData Δ)(mesh:ℝ→ℝ)
    (hmesh:0<mesh D.t)(hfine:∀j,D.ell j≤mesh D.t/200)
    (d:ℝ)(hd:(1/200:ℝ)≤d)(j:Fin D.N):
    0<D.ell j/d ∧ D.ell j/d≤mesh D.t:=by
  have hd0:0<d:=by linarith
  refine ⟨div_pos (D.slots_bounds j).1 hd0,(div_le_iff₀ hd0).mpr ?_⟩
  have hh:=hfine j
  nlinarith

end SevenEighths.Parameters

end

end OAI
end OAIOriginalModule0061

/-! Original module: OAI.NumberTheory.DirichletL.Poisson.BinaryGaussian
Source SHA256: a00b58ab5dc7d2b0e0bcfedbf29372b276dcffc056e0f4e8911d9a6630c61eaa
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0062


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

namespace RankTwoComplex

open Real

theorem lattice_gaussian_summable_of_re_bound (F : ℤ × ℤ → ℂ)
    {eps : ℝ} (heps : 0 < eps)
    (hbound : ∀ z : ℤ × ℤ,
      eps * ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) ≤ (F z).re) :
    Summable (fun z : ℤ × ℤ => Complex.exp (-(Real.pi : ℂ) * F z)) := by
  have h1 := RankTwoPoisson.real_gauss_summable heps
  have hmaj : Summable (fun z : ℤ × ℤ =>
      Real.exp (-Real.pi * eps * (z.1 : ℝ) ^ 2) *
      Real.exp (-Real.pi * eps * (z.2 : ℝ) ^ 2)) :=
    h1.mul_of_nonneg h1 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  refine hmaj.of_norm_bounded ?_
  intro z
  have hb := hbound z
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hm := mul_le_mul_of_nonneg_left hb hpi
  have hexp : (-(Real.pi : ℂ) * F z).re ≤
      -Real.pi * eps * (z.1 : ℝ) ^ 2 +
      -Real.pi * eps * (z.2 : ℝ) ^ 2 := by
    simp [Complex.mul_re] at *
    nlinarith [hm]
  simpa only [Complex.norm_exp, Real.exp_add] using
    (Real.exp_le_exp.mpr hexp)

noncomputable def schur (a b d : ℂ) : ℂ := d - b ^ 2 / a

noncomputable def binaryGaussian (a b d : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    (a * (z.1 : ℂ) ^ 2 + 2 * b * (z.1 : ℂ) * (z.2 : ℂ) + d * (z.2 : ℂ) ^ 2))

noncomputable def firstGaussian (a b d : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) / a * (z.1 : ℂ) ^ 2) *
    Complex.exp (-(Real.pi : ℂ) * schur a b d * (z.2 : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * (Complex.I * b / a * (z.1 : ℂ)) * (z.2 : ℂ))

noncomputable def dualGaussian (a b d : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) / a * (z.1 : ℂ) ^ 2) *
    Complex.exp (-(Real.pi : ℂ) / (schur a b d) *
      ((z.2 : ℂ) - b / a * (z.1 : ℂ)) ^ 2)

private theorem binary_split (a b d : ℂ) (m n : ℤ) :
    binaryGaussian a b d (m,n) =
      Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2) *
        Complex.exp (-(Real.pi : ℂ) * a * (m : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * (-(b * (n : ℂ))) * (m : ℂ)) := by
  dsimp [binaryGaussian]
  rw [← Complex.exp_add]
  congr 1
  ring

private theorem first_exponent_identity {a b d : ℂ} (ha : a ≠ 0) (k n : ℤ) :
    (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2) +
      (-(Real.pi : ℂ) / a * ((k : ℂ) + Complex.I * (-(b * (n : ℂ)))) ^ 2) =
      (-(Real.pi : ℂ) / a * (k : ℂ) ^ 2) +
        (-(Real.pi : ℂ) * schur a b d * (n : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * (Complex.I * b / a * (k : ℂ)) * (n : ℂ)) := by
  dsimp [schur]
  field_simp [ha]
  ring_nf
  simp [Complex.I_sq]

private theorem first_transform_term {a b d : ℂ} (ha : a ≠ 0) (k n : ℤ) :
    Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2) *
      Complex.exp (-(Real.pi : ℂ) / a *
        ((k : ℂ) + Complex.I * (-(b * (n : ℂ)))) ^ 2) =
      firstGaussian a b d (k,n) := by
  rw [← Complex.exp_add, first_exponent_identity ha k n, Complex.exp_add]
  rfl

private theorem first_poisson_slice {a b d : ℂ} (ha : 0 < a.re) (n : ℤ) :
    (∑' m : ℤ, binaryGaussian a b d (m,n)) =
      (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, firstGaussian a b d (k,n) := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  let C : ℂ := Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2)
  let B : ℂ := -(b * (n : ℂ))
  let F : ℤ → ℂ := fun m => Complex.exp
    (-(Real.pi : ℂ) * a * (m : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * B * (m : ℂ))
  let H : ℤ → ℂ := fun k => Complex.exp
    (-(Real.pi : ℂ) / a * ((k : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' m : ℤ, binaryGaussian a b d (m,n)) = C * ∑' m : ℤ, F m := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    exact binary_split a b d m n
  have hpoisson : (∑' m : ℤ, F m) =
      (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k :=
    Complex.tsum_exp_neg_quadratic ha B
  calc
    (∑' m : ℤ, binaryGaussian a b d (m,n)) = C * ∑' m : ℤ, F m := hsplit
    _ = C * ((1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k) := by rw [hpoisson]
    _ = (1 / a ^ (1 / 2 : ℂ)) * (C * ∑' k : ℤ, H k) := by ring
    _ = (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, firstGaussian a b d (k,n) := by
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      exact first_transform_term ha0 k n

private theorem second_poisson_slice {a b d : ℂ}
    (hδ : 0 < (schur a b d).re) (k : ℤ) :
    (∑' n : ℤ, firstGaussian a b d (k,n)) =
      (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
        ∑' l : ℤ, dualGaussian a b d (k,l) := by
  have hδ0 : schur a b d ≠ 0 := by
    intro h
    simp [h] at hδ
  let A : ℂ := schur a b d
  let B : ℂ := Complex.I * b / a * (k : ℂ)
  let C : ℂ := Complex.exp (-(Real.pi : ℂ) / a * (k : ℂ) ^ 2)
  let F : ℤ → ℂ := fun n => Complex.exp
    (-(Real.pi : ℂ) * A * (n : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * B * (n : ℂ))
  let H : ℤ → ℂ := fun l => Complex.exp
    (-(Real.pi : ℂ) / A * ((l : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' n : ℤ, firstGaussian a b d (k,n)) = C * ∑' n : ℤ, F n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rfl
  have hpoisson : (∑' n : ℤ, F n) =
      (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l :=
    Complex.tsum_exp_neg_quadratic hδ B
  have hterm (l : ℤ) : C * H l = dualGaussian a b d (k,l) := by
    have hb : Complex.I * B = -(b / a * (k : ℂ)) := by
      dsimp [B]
      field_simp
      ring_nf
      simp [Complex.I_sq]
    dsimp [H, dualGaussian, C, A]
    rw [hb]
    ring_nf
  calc
    (∑' n : ℤ, firstGaussian a b d (k,n)) = C * ∑' n : ℤ, F n := hsplit
    _ = C * ((1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l) := by rw [hpoisson]
    _ = (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) := by ring
    _ = (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          ∑' l : ℤ, dualGaussian a b d (k,l) := by
      change (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) =
        (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, dualGaussian a b d (k,l)
      congr 1
      rw [← tsum_mul_left]
      exact tsum_congr hterm

theorem binary_gaussian_poisson {a b d : ℂ}
    (ha : 0 < a.re) (hδ : 0 < (schur a b d).re)
    (hO : Summable (binaryGaussian a b d))
    (hM : Summable (firstGaussian a b d))
    (hD : Summable (dualGaussian a b d)) :
    (∑' z : ℤ × ℤ, binaryGaussian a b d z) =
      (1 / a ^ (1 / 2 : ℂ)) *
        (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, dualGaussian a b d z := by
  have hOcomm :
      (∑' n : ℤ, ∑' m : ℤ, binaryGaussian a b d (m,n)) =
        ∑' m : ℤ, ∑' n : ℤ, binaryGaussian a b d (m,n) :=
    (show Summable (Function.uncurry (fun m n : ℤ => binaryGaussian a b d (m,n)))
      from hO).tsum_comm
  have hMcomm :
      (∑' n : ℤ, ∑' k : ℤ, firstGaussian a b d (k,n)) =
        ∑' k : ℤ, ∑' n : ℤ, firstGaussian a b d (k,n) :=
    (show Summable (Function.uncurry (fun k n : ℤ => firstGaussian a b d (k,n)))
      from hM).tsum_comm
  calc
    (∑' z : ℤ × ℤ, binaryGaussian a b d z) =
        ∑' m : ℤ, ∑' n : ℤ, binaryGaussian a b d (m,n) := hO.tsum_prod
    _ = ∑' n : ℤ, ∑' m : ℤ, binaryGaussian a b d (m,n) := hOcomm.symm
    _ = ∑' n : ℤ, (1 / a ^ (1 / 2 : ℂ)) *
          ∑' k : ℤ, firstGaussian a b d (k,n) := by
      apply tsum_congr
      intro n
      exact first_poisson_slice ha n
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' n : ℤ, ∑' k : ℤ, firstGaussian a b d (k,n)) := tsum_mul_left
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' n : ℤ, firstGaussian a b d (k,n)) := by
      rw [hMcomm]
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
            ∑' l : ℤ, dualGaussian a b d (k,l)) := by
      congr 1
      apply tsum_congr
      intro k
      exact second_poisson_slice hδ k
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' l : ℤ, dualGaussian a b d (k,l)) := by
      rw [tsum_mul_left]
      ring
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          ∑' z : ℤ × ℤ, dualGaussian a b d z := by
      rw [hD.tsum_prod]

end RankTwoComplex

namespace GaussianShiftedPartition

open ActualEisensteinCubic ConcreteTraceCRT ConcreteBreveE

noncomputable def representative (c : O) (r : O ⧸ Ideal.span {c}) : O :=
  Classical.choose (Ideal.Quotient.mk_surjective r)

theorem representative_spec (c : O) (r : O ⧸ Ideal.span {c}) :
    Ideal.Quotient.mk (Ideal.span {c}) (representative c r) = r :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective r)

theorem actual_quadratic_shifted_partition (c : O) (hc : c ≠ 0)
    (W : O → ℂ)
    (hsum : Summable (fun z : O =>
      (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
        ((Ideal.Quotient.mk (Ideal.span {c}) z) ^ 2) * W z)) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O,
      (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
        ((Ideal.Quotient.mk (Ideal.span {c}) z) ^ 2) * W z) =
      ∑ r : O ⧸ Ideal.span {c},
        (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
          (r ^ 2) *
          ∑' w : O, W (representative c r + c*w) := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [GaussianAbelPartition.actual_quadratic_gaussian_partition c hc W hsum]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  exact GaussianFiberEquiv.fiber_tsum c hc r
    (representative c r) (representative_spec c r) W

end GaussianShiftedPartition

namespace RankTwoAffine

open RankTwoComplex

noncomputable def binaryGaussian (a b d u v : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    (a * (z.1 : ℂ) ^ 2 + 2 * b * (z.1 : ℂ) * (z.2 : ℂ) + d * (z.2 : ℂ) ^ 2) +
    2 * (Real.pi : ℂ) * (u * (z.1 : ℂ) + v * (z.2 : ℂ)))

noncomputable def firstGaussian (a b d u v : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) / a * ((z.1 : ℂ) + Complex.I * u) ^ 2) *
    Complex.exp (-(Real.pi : ℂ) * schur a b d * (z.2 : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) *
        (v + Complex.I * b / a * ((z.1 : ℂ) + Complex.I * u)) * (z.2 : ℂ))

noncomputable def dualGaussian (a b d u v : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) / a * ((z.1 : ℂ) + Complex.I * u) ^ 2) *
    Complex.exp (-(Real.pi : ℂ) / (schur a b d) *
      ((z.2 : ℂ) + Complex.I *
        (v + Complex.I * b / a * ((z.1 : ℂ) + Complex.I * u))) ^ 2)

private theorem binary_split (a b d u v : ℂ) (m n : ℤ) :
    binaryGaussian a b d u v (m,n) =
      Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) * v * (n : ℂ)) *
        Complex.exp (-(Real.pi : ℂ) * a * (m : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * (u - b * (n : ℂ)) * (m : ℂ)) := by
  dsimp [binaryGaussian]
  rw [← Complex.exp_add]
  congr 1
  ring

private theorem first_exponent_identity {a b d u v : ℂ} (ha : a ≠ 0) (k n : ℤ) :
    (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) * v * (n : ℂ)) +
      (-(Real.pi : ℂ) / a *
        ((k : ℂ) + Complex.I * (u - b * (n : ℂ))) ^ 2) =
      (-(Real.pi : ℂ) / a * ((k : ℂ) + Complex.I * u) ^ 2) +
        (-(Real.pi : ℂ) * schur a b d * (n : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) *
            (v + Complex.I * b / a * ((k : ℂ) + Complex.I * u)) * (n : ℂ)) := by
  dsimp [schur]
  field_simp [ha]
  ring_nf
  simp [Complex.I_sq]

private theorem first_transform_term {a b d u v : ℂ} (ha : a ≠ 0) (k n : ℤ) :
    Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * v * (n : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) / a *
        ((k : ℂ) + Complex.I * (u - b * (n : ℂ))) ^ 2) =
      firstGaussian a b d u v (k,n) := by
  rw [← Complex.exp_add, first_exponent_identity ha k n, Complex.exp_add]
  rfl

private theorem first_poisson_slice {a b d u v : ℂ} (ha : 0 < a.re) (n : ℤ) :
    (∑' m : ℤ, binaryGaussian a b d u v (m,n)) =
      (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, firstGaussian a b d u v (k,n) := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  let C : ℂ := Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2 +
    2 * (Real.pi : ℂ) * v * (n : ℂ))
  let B : ℂ := u - b * (n : ℂ)
  let F : ℤ → ℂ := fun m => Complex.exp
    (-(Real.pi : ℂ) * a * (m : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * B * (m : ℂ))
  let H : ℤ → ℂ := fun k => Complex.exp
    (-(Real.pi : ℂ) / a * ((k : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' m : ℤ, binaryGaussian a b d u v (m,n)) = C * ∑' m : ℤ, F m := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    exact binary_split a b d u v m n
  have hpoisson : (∑' m : ℤ, F m) =
      (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k :=
    Complex.tsum_exp_neg_quadratic ha B
  calc
    (∑' m : ℤ, binaryGaussian a b d u v (m,n)) = C * ∑' m : ℤ, F m := hsplit
    _ = C * ((1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k) := by rw [hpoisson]
    _ = (1 / a ^ (1 / 2 : ℂ)) * (C * ∑' k : ℤ, H k) := by ring
    _ = (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, firstGaussian a b d u v (k,n) := by
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      exact first_transform_term ha0 k n

private theorem second_poisson_slice {a b d u v : ℂ}
    (hδ : 0 < (schur a b d).re) (k : ℤ) :
    (∑' n : ℤ, firstGaussian a b d u v (k,n)) =
      (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
        ∑' l : ℤ, dualGaussian a b d u v (k,l) := by
  let A : ℂ := schur a b d
  let B : ℂ := v + Complex.I * b / a * ((k : ℂ) + Complex.I * u)
  let C : ℂ := Complex.exp (-(Real.pi : ℂ) / a * ((k : ℂ) + Complex.I * u) ^ 2)
  let F : ℤ → ℂ := fun n => Complex.exp
    (-(Real.pi : ℂ) * A * (n : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * B * (n : ℂ))
  let H : ℤ → ℂ := fun l => Complex.exp
    (-(Real.pi : ℂ) / A * ((l : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' n : ℤ, firstGaussian a b d u v (k,n)) = C * ∑' n : ℤ, F n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rfl
  have hpoisson : (∑' n : ℤ, F n) =
      (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l :=
    Complex.tsum_exp_neg_quadratic hδ B
  calc
    (∑' n : ℤ, firstGaussian a b d u v (k,n)) = C * ∑' n : ℤ, F n := hsplit
    _ = C * ((1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l) := by rw [hpoisson]
    _ = (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) := by ring
    _ = (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          ∑' l : ℤ, dualGaussian a b d u v (k,l) := by
      change (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) =
        (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, dualGaussian a b d u v (k,l)
      congr 1
      rw [← tsum_mul_left]
      rfl

theorem affine_gaussian_poisson {a b d u v : ℂ}
    (ha : 0 < a.re) (hδ : 0 < (schur a b d).re)
    (hO : Summable (binaryGaussian a b d u v))
    (hM : Summable (firstGaussian a b d u v))
    (hD : Summable (dualGaussian a b d u v)) :
    (∑' z : ℤ × ℤ, binaryGaussian a b d u v z) =
      (1 / a ^ (1 / 2 : ℂ)) *
        (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, dualGaussian a b d u v z := by
  have hOcomm :
      (∑' n : ℤ, ∑' m : ℤ, binaryGaussian a b d u v (m,n)) =
        ∑' m : ℤ, ∑' n : ℤ, binaryGaussian a b d u v (m,n) :=
    (show Summable (Function.uncurry (fun m n : ℤ => binaryGaussian a b d u v (m,n)))
      from hO).tsum_comm
  have hMcomm :
      (∑' n : ℤ, ∑' k : ℤ, firstGaussian a b d u v (k,n)) =
        ∑' k : ℤ, ∑' n : ℤ, firstGaussian a b d u v (k,n) :=
    (show Summable (Function.uncurry (fun k n : ℤ => firstGaussian a b d u v (k,n)))
      from hM).tsum_comm
  calc
    (∑' z : ℤ × ℤ, binaryGaussian a b d u v z) =
        ∑' m : ℤ, ∑' n : ℤ, binaryGaussian a b d u v (m,n) := hO.tsum_prod
    _ = ∑' n : ℤ, ∑' m : ℤ, binaryGaussian a b d u v (m,n) := hOcomm.symm
    _ = ∑' n : ℤ, (1 / a ^ (1 / 2 : ℂ)) *
          ∑' k : ℤ, firstGaussian a b d u v (k,n) := by
      apply tsum_congr
      intro n
      exact first_poisson_slice ha n
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' n : ℤ, ∑' k : ℤ, firstGaussian a b d u v (k,n)) := tsum_mul_left
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' n : ℤ, firstGaussian a b d u v (k,n)) := by
      rw [hMcomm]
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
            ∑' l : ℤ, dualGaussian a b d u v (k,l)) := by
      congr 1
      apply tsum_congr
      intro k
      exact second_poisson_slice hδ k
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' l : ℤ, dualGaussian a b d u v (k,l)) := by
      rw [tsum_mul_left]
      ring
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          ∑' z : ℤ × ℤ, dualGaussian a b d u v z := by
      rw [hD.tsum_prod]

end RankTwoAffine

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem eisEmbedding_eval_norm_sq (x y : ℤ) :
    ‖eisEmbedding (ActualEisensteinCoordinates.eval x y)‖ ^ 2 =
      (x*x-x*y+y*y : ℤ) := by
  rw [eisEmbedding_eval, ← Complex.normSq_eq_norm_sq]
  have hre : ((x : ℂ) + (y : ℂ) * omega3).re =
      (x : ℝ) - (y : ℝ) / 2 := by
    simp [omega3, Complex.add_re, Complex.mul_re]
    ring
  have him : ((x : ℂ) + (y : ℂ) * omega3).im =
      (y : ℝ) * Real.sqrt 3 / 2 := by
    simp [omega3, Complex.add_im, Complex.mul_im]
    ring
  rw [Complex.normSq_apply, hre, him]
  have hs : (Real.sqrt 3)^2 = (3:ℝ) := Real.sq_sqrt (by norm_num)
  push_cast
  nlinarith

theorem fiber_coordinates (a b x y m n : ℤ) :
    ActualEisensteinCoordinates.eval x y +
      ActualEisensteinCoordinates.eval a b *
        ActualEisensteinCoordinates.eval m n =
    ActualEisensteinCoordinates.eval (x + a*m-b*n)
      (y+b*m+(a-b)*n) := by
  rw [ActualEisensteinCoordinates.eval_mul]
  simp only [ActualEisensteinCoordinates.eval]
  push_cast
  ring

theorem fiber_quadratic_expansion (a b x y m n : ℤ) :
    let q := a*a-a*b+b*b
    let X := x+a*m-b*n
    let Y := y+b*m+(a-b)*n
    X*X-X*Y+Y*Y =
      q*(m*m-m*n+n*n) +
      ((2*a-b)*x+(2*b-a)*y)*m +
      (-(a+b)*x+(2*a-b)*y)*n +
      (x*x-x*y+y*y) := by
  dsimp
  ring

theorem eisEmbedding_fiber_norm_sq (a b x y m n : ℤ) :
    ‖eisEmbedding
      (ActualEisensteinCoordinates.eval x y +
        ActualEisensteinCoordinates.eval a b *
          ActualEisensteinCoordinates.eval m n)‖ ^ 2 =
      ((a*a-a*b+b*b)*(m*m-m*n+n*n) +
      ((2*a-b)*x+(2*b-a)*y)*m +
      (-(a+b)*x+(2*a-b)*y)*n +
      (x*x-x*y+y*y) : ℤ) := by
  rw [fiber_coordinates, eisEmbedding_eval_norm_sq]
  exact_mod_cast fiber_quadratic_expansion a b x y m n

theorem coordinate_norm_pos_of_nonzero (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    0 < a*a-a*b+b*b := by
  have he : eisEmbedding (ActualEisensteinCoordinates.eval a b) ≠ 0 :=
    ConcreteTraceCRT.eisEmbedding_ne_zero hc
  have hn : 0 < ‖eisEmbedding (ActualEisensteinCoordinates.eval a b)‖ :=
    norm_pos_iff.mpr he
  have heq := eisEmbedding_eval_norm_sq a b
  exact_mod_cast (show (0:ℝ) < (a*a-a*b+b*b : ℤ) by
    rw [← heq]
    positivity)

end ActualEisensteinCubic

namespace RankTwoEisShift

noncomputable def Q (x y : ℝ) : ℝ := x ^ 2 - x * y + y ^ 2

noncomputable def shifted (t x y : ℝ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (((-Real.pi * t * Q ((z.1 : ℝ) + x) ((z.2 : ℝ) + y) : ℝ) : ℂ))

noncomputable def A (t : ℝ) : ℂ := (t : ℂ)
noncomputable def B (t : ℝ) : ℂ := ((-t / 2 : ℝ) : ℂ)
noncomputable def D (t : ℝ) : ℂ := (t : ℂ)
noncomputable def U (t x y : ℝ) : ℂ := ((-t * (x - y / 2) : ℝ) : ℂ)
noncomputable def V (t x y : ℝ) : ℂ := ((-t * (y - x / 2) : ℝ) : ℂ)
noncomputable def C (t x y : ℝ) : ℂ :=
  Complex.exp (((-Real.pi * t * Q x y : ℝ) : ℂ))

private theorem shifted_eq_affine (t x y : ℝ) (m n : ℤ) :
    shifted t x y (m,n) =
      C t x y * RankTwoAffine.binaryGaussian (A t) (B t) (D t) (U t x y) (V t x y) (m,n) := by
  dsimp [shifted, C, Q, RankTwoAffine.binaryGaussian, A, B, D, U, V]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem schur_eis {t : ℝ} (ht : 0 < t) :
    RankTwoComplex.schur (A t) (B t) (D t) = (((3 * t) / 4 : ℝ) : ℂ) := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  dsimp [RankTwoComplex.schur, A, B, D]
  push_cast
  field_simp [ht0]
  ring

private theorem schur_eis_pos {t : ℝ} (ht : 0 < t) :
    0 < (RankTwoComplex.schur (A t) (B t) (D t)).re := by
  rw [schur_eis ht]
  have h : 0 < 3 * t / 4 := by positivity
  simpa using h

