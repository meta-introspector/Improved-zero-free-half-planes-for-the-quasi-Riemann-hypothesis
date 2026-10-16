Source SHA256: 34717d522f27b29a5d939ba45ee190ed48836e79cc2775ba4533edbafa3f12aa
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1293




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeRowNonprincipal
open HeckeFamily CanonicalRowCompletion CenteredMomentCanonical
open ConcretePrimeRowBridge hiding O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem nonprincipal_of_local_factor (χ : Character)
    (Q J P : Ideal O) [P.IsMaximal]
    (hQ : Q ≤ Ideal.span {λ₀ ^ 2})
    (φ : O →* ℂ) (hφ : CanonicalCoefficientClass.FactorsModulo Q φ)
    (hJ : CanonicalQuadraticSieve.Supported J)
    (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {c : ℕ} (hc : 1 ≤ c) (hc6 : ¬ 6 ∣ c)
    (hcop : IsCoprime (Q * J) (P ^ c))
    (hrow : ∀ n : O, λ₀ ^ 2 ∣ n - 1 →
      elementCoeff χ n = φ n * idealRowHom n (P ^ c * J)) :
    χ.residue ≠ 1 := by
  let ψ := canonicalPrimePowerCharacter P hg hc
  have hψ : ψ ≠ 1 := fun h => hc6 ((HeckeLocalRamification.canonicalPrimePowerCharacter_eq_one_iff P hg hchar hc).mp h)
  obtain ⟨u, hu⟩ : ∃ u : (O ⧸ P ^ c)ˣ, ψ (u : O ⧸ P ^ c) ≠ 1 := by
    by_contra! h
    apply hψ
    apply MulChar.ext
    intro u
    rw [MulChar.one_apply u.isUnit]
    exact h u
  let e := Ideal.quotientInfEquivQuotientProd (Q * J) (P ^ c) hcop
  obtain ⟨x, hx⟩ := e.surjective ((1 : O ⧸ Q * J), (u : O ⧸ P ^ c))
  obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (Ideal.Quotient.mk (Q * J) n, Ideal.Quotient.mk (P ^ c) n) = (1, (u : O ⧸ P ^ c)) at hx
  have hnQJ := congrArg Prod.fst hx
  have hnP := congrArg Prod.snd hx
  dsimp only at hnQJ hnP
  have hn : n - 1 ∈ Q * J := Ideal.Quotient.eq.mp (by simpa using hnQJ)
  have hnQ : n - 1 ∈ Q := Ideal.mul_le_left hn
  have hnJ : n - 1 ∈ J := Ideal.mul_le_right hn
  have hnprimary : λ₀ ^ 2 ∣ n - 1 := Ideal.mem_span_singleton.mp (hQ hnQ)
  have hv : elementCoeff χ n = ψ (u : O ⧸ P ^ c) := by
    rw [hrow n hnprimary, map_mul, hφ n 1 hnQ, map_one, one_mul,
      idealRowHom_congr_mod J n 1 hnJ, idealRowHom_one_supported J hJ, mul_one]
    rw [← canonicalPrimePowerCharacter_mk P hg hc n, hnP]
  have hv0 : elementCoeff χ n ≠ 0 := hv ▸ (MulChar.apply_ne_zero_iff.mpr u.isUnit)
  intro hχ
  have hunit : IsUnit (Ideal.Quotient.mk χ.modulus n) := MulChar.apply_ne_zero_iff.mp hv0
  have hv1 : elementCoeff χ n = 1 := by
    change χ.residue _ = 1
    rw [hχ, MulChar.one_apply hunit]
  exact hu (hv.symm.trans hv1)

theorem actual_row_nonprincipal (η χ : Character) (m f z : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀ ^ 2 ∣ r - 1) (hx : f ^ 4 * z = (u : O) * λ₀ ^ a * (2 : O) ^ b * r)
    (P J : Ideal O) [P.IsMaximal]
    (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (hJ : CanonicalQuadraticSieve.Supported J)
    {c : ℕ} (hc : 1 ≤ c) (hc6 : ¬ 6 ∣ c)
    (hsplit : Ideal.span {r} = P ^ c * J)
    (hcop : IsCoprime ((η.modulus * Ideal.span {m} * Ideal.span {(72 : O)}) * J) (P ^ c))
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m f z n) :
    χ.residue ≠ 1 := by
  let φ := HeckeRowClosure.elementHom η * coprimalityMask m * numeratorBadTwist u a b r hr
  refine nonprincipal_of_local_factor χ (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)}) J P
      ?_ φ ?_ hJ hg hchar hc hc6 hcop ?_
  · have hd3 : λ₀ ^ 2 ∣ (3 : O) := ActualEisensteinCubic.lambda_sq_dvd_three
    have hd72 : λ₀ ^ 2 ∣ (72 : O) := hd3.trans ⟨24, by norm_num⟩
    exact Ideal.mul_le_right.trans ((Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.mem_span_singleton.mpr hd72))
  · intro x y hxy
    change ((HeckeRowClosure.elementHom η x * coprimalityMask m x) * numeratorBadTwist u a b r hr x) =
      ((HeckeRowClosure.elementHom η y * coprimalityMask m y) * numeratorBadTwist u a b r hr y)
    rw [HeckeRowClosure.elementHom_periodic η x y (Ideal.mul_le_left (Ideal.mul_le_left hxy)),
      coprimalityMask_periodic m x y (Ideal.mul_le_right (Ideal.mul_le_left hxy)),
      numeratorBadTwist_periodic u a b r hr x y (Ideal.mul_le_right hxy)]
  · intro n hn
    rw [hχ n, rowTwist_eq_actualPeriodicRow_primary _ _ _ _ hmLam hm2 u a b r hr hpr hx n hn]
    change φ n * idealRowHom n (Ideal.span {r}) = φ n * idealRowHom n (P ^ c * J)
    rw [hsplit]

open UniqueFactorizationMonoid in

theorem extract_prime_power (I : Ideal O) (hI : CanonicalQuadraticSieve.Supported I)
    (P : Ideal O) (hP : P ∈ normalizedFactors I) :
    ∃ J : Ideal O, I = P ^ (normalizedFactors I).count P * J ∧
      CanonicalQuadraticSieve.Supported J ∧ IsCoprime J P := by
  let S := (normalizedFactors I).toFinset
  let J := ∏ Q ∈ S.erase P, Q ^ (normalizedFactors I).count Q
  have hPS : P ∈ S := Multiset.mem_toFinset.mpr hP
  have hsplit : I = P ^ (normalizedFactors I).count P * J := by
    calc
      I = (normalizedFactors I).prod := (Ideal.prod_normalizedFactors_eq_self hI.1).symm
      _ = ∏ Q ∈ S, Q ^ (normalizedFactors I).count Q := Finset.prod_multiset_count _
      _ = P ^ (normalizedFactors I).count P * J :=
        (Finset.mul_prod_erase S (fun Q => Q ^ (normalizedFactors I).count Q) hPS).symm
  have hgood := supported_factors_good I hI P hP
  let : P.IsMaximal := hgood.1
  refine ⟨J, hsplit, ?_, ?_⟩
  · exact (CanonicalQuadraticSieve.supported_mul_iff _ _).mp (hsplit ▸ hI) |>.2
  · apply IsCoprime.prod_left
    intro Q hQ
    obtain ⟨hQP, hQS⟩ := Finset.mem_erase.mp hQ
    have hgoodQ := supported_factors_good I hI Q (Multiset.mem_toFinset.mp hQS)
    let : Q.IsMaximal := hgoodQ.1
    exact (Ideal.isCoprime_of_isMaximal hQP).pow_left

open UniqueFactorizationMonoid in

theorem principal_row_multiplicity (η χ : Character) (m f z : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀ ^ 2 ∣ r - 1) (hx : f ^ 4 * z = (u : O) * λ₀ ^ a * (2 : O) ^ b * r)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m f z n)
    (hprincipal : χ.residue = 1)
    (P : Ideal O) (hP : P ∈ normalizedFactors (Ideal.span {r}))
    (hcop : IsCoprime (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)}) P) :
    6 ∣ (normalizedFactors (Ideal.span {r})).count P := by
  by_contra hc6
  have hgood := supported_factors_good (Ideal.span {r}) hr P hP
  let : P.IsMaximal := hgood.1
  obtain ⟨J, hsplit, hJ, hJP⟩ := extract_prime_power _ hr P hP
  have hc : 1 ≤ (normalizedFactors (Ideal.span {r})).count P := Multiset.count_pos.mpr hP
  exact actual_row_nonprincipal η χ m f z hmLam hm2 u a b r hr hpr hx P J
    hgood.2.1 hgood.2.2 hJ hc hc6 hsplit ((hcop.mul_left hJP).pow_right) hχ hprincipal

open UniqueFactorizationMonoid in

theorem principal_row_fixed_support (η χ : Character) (m f z : O)
    (hm : m ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀ ^ 2 ∣ r - 1) (hx : f ^ 4 * z = (u : O) * λ₀ ^ a * (2 : O) ^ b * r)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m f z n)
    (hprincipal : χ.residue = 1)
    (hfree : ∀ P ∈ normalizedFactors (Ideal.span {r}),
      (normalizedFactors (Ideal.span {r})).count P < 6) :
    r ∈ HeckeExceptionalRows.rows
      (normalizedFactors (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)})).toFinset := by
  let Q := η.modulus * Ideal.span {m} * Ideal.span {(72 : O)}
  have hQ : Q ≠ ⊥ := mul_ne_zero
    (mul_ne_zero η.modulus_ne_bot (Ideal.span_singleton_eq_bot.not.mpr hm))
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))
  refine ⟨Ideal.span_singleton_eq_bot.not.mp hr.1, ?_⟩
  intro P hP
  refine ⟨?_, hfree P hP⟩
  apply Multiset.mem_toFinset.mpr
  have hgood := supported_factors_good (Ideal.span {r}) hr P hP
  let : P.IsMaximal := hgood.1
  apply (Ideal.mem_normalizedFactors_iff hQ).mpr
  refine ⟨Ideal.isPrime_of_prime (prime_of_normalized_factor P hP), ?_⟩
  by_contra hQP
  have hcop : IsCoprime Q P := by
    apply Ideal.coprime_of_no_prime_ge
    intro J hQJ hPJ hJ
    have hPJ' : P = J := hgood.1.eq_of_le hJ.ne_top hPJ
    exact hQP (hPJ' ▸ hQJ)
  have hd := principal_row_multiplicity η χ m f z hmLam hm2 u a b r hr hpr hx hχ hprincipal P hP hcop
  exact Nat.not_dvd_of_pos_of_lt (Multiset.count_pos.mpr hP) (hfree P hP) hd

end SevenEighths.HeckeRowNonprincipal

end

end OAI
end OAIOriginalModule1293

/-! Original module: OAI.NumberTheory.DirichletL.CenteredExceptionalProfile
Source SHA256: 807a5a72662c10f2ca59a24bd9d4d88ee62c8f4214f344fc492f329de990d7d5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1294



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredExceptionalProfile
open UniqueFactorizationMonoid HeckeFamily CanonicalRowCompletion
open ConcretePrimeRowBridge hiding O
open CompletedGauss hiding O
open ConcreteTraceCRT
local notation "O" => HeckeFamily.O
open CenteredExceptionalCount CenteredMomentCanonical
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem split_at_prime (I P : Ideal O) (hI : I ≠ 0) [P.IsMaximal] :
    ∃ J : Ideal O, I = P ^ valuation I P * J ∧ J ≠ 0 ∧ IsCoprime J P := by
  let S := (normalizedFactors I).toFinset
  let J := ∏ Q ∈ S.erase P, Q ^ valuation I Q
  have hsplit : I = P ^ valuation I P * J := by
    calc
      I = (normalizedFactors I).prod := (Ideal.prod_normalizedFactors_eq_self hI).symm
      _ = ∏ Q ∈ S, Q ^ valuation I Q := Finset.prod_multiset_count _
      _ = P ^ valuation I P * J := by
        by_cases hP : P ∈ S
        · exact (Finset.mul_prod_erase S (fun Q => Q ^ valuation I Q) hP).symm
        · have hz : valuation I P = 0 := Multiset.count_eq_zero.mpr
            (fun h => hP (Multiset.mem_toFinset.mpr h))
          simp only [J, Finset.erase_eq_of_notMem hP, hz, pow_zero, one_mul]
  refine ⟨J, hsplit, ?_, ?_⟩
  · intro hz
    apply hI
    rw [hsplit, hz, mul_zero]
  · apply IsCoprime.prod_left
    intro Q hQ
    obtain ⟨hQP, hQS⟩ := Finset.mem_erase.mp hQ
    have hp := prime_of_normalized_factor Q (Multiset.mem_toFinset.mp hQS)
    let : Q.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    exact (Ideal.isCoprime_of_isMaximal hQP).pow_left

theorem exists_unit_probe (Q K P : Ideal O) (hK : K ≠ 0) [P.IsMaximal]
    (hQP : IsCoprime Q P) (u : (O ⧸ P)ˣ) :
    ∃ n : O, n - 1 ∈ Q ∧ IsCoprime (Ideal.span {n}) K ∧
      Ideal.Quotient.mk P n = (u : O ⧸ P) := by
  obtain ⟨J, hsplit, hJ, hJP⟩ := split_at_prime K P hK
  let e := Ideal.quotientInfEquivQuotientProd (Q * J) P (hQP.mul_left hJP)
  obtain ⟨x, hx⟩ := e.surjective ((1 : O ⧸ Q * J), (u : O ⧸ P))
  obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (Ideal.Quotient.mk (Q * J) n, Ideal.Quotient.mk P n) = (1, (u : O ⧸ P)) at hx
  have hnQJ := congrArg Prod.fst hx
  have hnP := congrArg Prod.snd hx
  dsimp only at hnQJ hnP
  have hn : n - 1 ∈ Q * J := Ideal.Quotient.eq.mp (by simpa using hnQJ)
  have hnJ : Ideal.Quotient.mk J n = 1 :=
    (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (Ideal.mul_le_right hn)
  have hcJ : IsCoprime (Ideal.span {n}) J :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hnJ ▸ isUnit_one)
  have hcP : IsCoprime (Ideal.span {n}) P :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hnP ▸ u.isUnit)
  refine ⟨n, Ideal.mul_le_left hn, ?_, hnP⟩
  rw [hsplit]
  exact hcP.pow_right.mul_right hcJ

theorem valuation_mod_six_of_unit_agreement (Q K I J P : Ideal O)
    (hK : K ≠ 0) (hI : CanonicalQuadraticSieve.Supported I)
    (hJ : CanonicalQuadraticSieve.Supported J) [P.IsMaximal]
    (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (hQP : IsCoprime Q P)
    (heq : ∀ n : O, n - 1 ∈ Q → IsCoprime (Ideal.span {n}) K →
      idealRowHom n I = idealRowHom n J) :
    valuation I P % 6 = valuation J P % 6 := by
  obtain ⟨I₀, hsplitI, hI₀, hcI⟩ := split_at_prime I P hI.1
  obtain ⟨J₀, hsplitJ, hJ₀, hcJ⟩ := split_at_prime J P hJ.1
  have hsI : CanonicalQuadraticSieve.Supported I₀ :=
    ((CanonicalQuadraticSieve.supported_mul_iff _ _).mp (hsplitI ▸ hI)).2
  have hsJ : CanonicalQuadraticSieve.Supported J₀ :=
    ((CanonicalQuadraticSieve.supported_mul_iff _ _).mp (hsplitJ ▸ hJ)).2
  have hpows : actualSextic P hg ^ valuation I P = actualSextic P hg ^ valuation J P := by
    apply MulChar.ext
    intro u
    obtain ⟨n, hn, hcK, hnP⟩ := exists_unit_probe (Q * I₀ * J₀) K P hK
      ((hQP.mul_left hcI).mul_left hcJ) u
    have hval := heq n (Ideal.mul_le_left (Ideal.mul_le_left hn)) hcK
    have hIn : n - 1 ∈ I₀ := Ideal.mul_le_right (Ideal.mul_le_left hn)
    have hJn : n - 1 ∈ J₀ := Ideal.mul_le_right hn
    rw [hsplitI, hsplitJ, map_mul, map_mul, map_pow, map_pow,
      idealRowHom_congr_mod I₀ n 1 hIn, idealRowHom_congr_mod J₀ n 1 hJn,
      idealRowHom_one_supported I₀ hsI, idealRowHom_one_supported J₀ hsJ,
      mul_one, mul_one, idealRowHom_prime n P hg, hnP] at hval
    simpa only [MulChar.pow_apply_coe] using hval
  have hm := (pow_eq_pow_iff_modEq.mp hpows)
  rw [actualSextic_order_six P hg hchar] at hm
  exact hm

def InducedBy (χ ψ : Character) : Prop :=
  ∀ I : Ideal O, idealCoeff χ I =
    if IsCoprime I χ.modulus then idealCoeff ψ I else 0

theorem exists_primitive_inducedBy (χ : Character) :
    ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      χ.modulus ≤ ψ.modulus ∧ InducedBy χ ψ := by
  obtain ⟨ψ, hmod, hprim, _, hmask⟩ := exists_primitive_character χ
  exact ⟨ψ, hprim, hmod, hmask⟩

theorem elementCoeff_eq_of_inducedBy (χ ψ : Character) (h : InducedBy χ ψ)
    (n : O) (hn : n ≠ 0) (hc : IsCoprime (Ideal.span {n}) χ.modulus) :
    elementCoeff χ n = elementCoeff ψ n := by
  have he := h (Ideal.span {n})
  simp only [hc, ite_true, idealCoeff_span χ hn, idealCoeff_span ψ hn] at he
  exact he

theorem elementCoeff_eq_one_of_inducedBy (χ ψ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hψ : Q ≤ ψ.modulus)
    (n : O) (hn : n - 1 ∈ Q) (hc : IsCoprime (Ideal.span {n}) χ.modulus) :
    elementCoeff χ n = 1 := by
  have hn0 : n ≠ 0 := by
    intro hz
    have h1 : (1 : O) ∈ Q := by simpa [hz] using Q.neg_mem hn
    exact hQ ((Ideal.eq_top_iff_one Q).mpr h1)
  rw [elementCoeff_eq_of_inducedBy χ ψ h n hn0 hc]
  change ψ.residue (Ideal.Quotient.mk ψ.modulus n) = 1
  rw [(Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (hψ hn), map_one]

theorem local_rows_profile (η χ₁ χ₂ ψ₁ ψ₂ : Character)
    (h₁ : InducedBy χ₁ ψ₁) (h₂ : InducedBy χ₂ ψ₂)
    (Q K I J P : Ideal O) (hQ : Q ≠ ⊤) (hK : K ≠ 0)
    (hψ₁ : Q ≤ ψ₁.modulus) (hψ₂ : Q ≤ ψ₂.modulus)
    (hI : CanonicalQuadraticSieve.Supported I)
    (hJ : CanonicalQuadraticSieve.Supported J) [P.IsMaximal]
    (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (hQP : IsCoprime Q P)
    (hrow₁ : ∀ n : O, n - 1 ∈ Q → IsCoprime (Ideal.span {n}) K →
      elementCoeff χ₁ n = elementCoeff η n * idealRowHom n I)
    (hrow₂ : ∀ n : O, n - 1 ∈ Q → IsCoprime (Ideal.span {n}) K →
      elementCoeff χ₂ n = elementCoeff η n * idealRowHom n J) :
    valuation I P % 6 = valuation J P % 6 := by
  let L := ((K * η.modulus) * χ₁.modulus) * χ₂.modulus
  have hL : L ≠ 0 := mul_ne_zero
    (mul_ne_zero (mul_ne_zero hK η.modulus_ne_bot) χ₁.modulus_ne_bot) χ₂.modulus_ne_bot
  apply valuation_mod_six_of_unit_agreement Q L I J P hL hI hJ hg hchar hQP
  intro n hn hc
  obtain ⟨⟨⟨hcK, hcη⟩, hc₁⟩, hc₂⟩ :=
    (show ((IsCoprime (Ideal.span {n}) K ∧ IsCoprime (Ideal.span {n}) η.modulus) ∧
      IsCoprime (Ideal.span {n}) χ₁.modulus) ∧ IsCoprime (Ideal.span {n}) χ₂.modulus from by
        simpa only [L, IsCoprime.mul_right_iff] using hc)
  have he₁ := elementCoeff_eq_one_of_inducedBy χ₁ ψ₁ h₁ Q hQ hψ₁ n hn hc₁
  have he₂ := elementCoeff_eq_one_of_inducedBy χ₂ ψ₂ h₂ Q hQ hψ₂ n hn hc₂
  rw [hrow₁ n hn hcK] at he₁
  rw [hrow₂ n hn hcK] at he₂
  have hη : elementCoeff η n ≠ 0 := MulChar.apply_ne_zero_iff.mpr
    ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hcη)
  exact mul_left_cancel₀ hη (he₁.trans he₂.symm)

theorem actual_row_on_fixed_units (η χ : Character) (m f z : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀ ^ 2 ∣ r - 1)
    (hx : f ^ 4 * z = (u : O) * λ₀ ^ a * (2 : O) ^ b * r)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m f z n)
    (n : O) (hn : n - 1 ∈ Ideal.span {(72 : O)})
    (hc : IsCoprime (Ideal.span {n}) (Ideal.span {m})) :
    elementCoeff χ n = elementCoeff η n * idealRowHom n (Ideal.span {r}) := by
  have hd72 : λ₀ ^ 2 ∣ (72 : O) := ActualEisensteinCubic.lambda_sq_dvd_three.trans
    (show (3 : O) ∣ 72 from ⟨24, by norm_num⟩)
  have hp : λ₀ ^ 2 ∣ n - 1 := hd72.trans (Ideal.mem_span_singleton.mp hn)
  rw [hχ n, rowTwist_eq_actualPeriodicRow_primary _ _ _ _ hmLam hm2 u a b r hr hpr hx n hp]
  change ((elementCoeff η n * coprimalityMask m n) * numeratorBadTwist u a b r hr n) *
    idealRowHom n (Ideal.span {r}) = _
  have hm : coprimalityMask m n = 1 := by
    change (if IsCoprime m n then (1 : ℂ) else 0) = 1
    simp only [((Ideal.isCoprime_span_singleton_iff _ _).mp hc).symm, ite_true]
  rw [hm, numeratorBadTwist_periodic u a b r hr n 1 hn, map_one, mul_one, mul_one]

theorem actual_rows_good_profile (η χ₁ χ₂ ψ₁ ψ₂ : Character)
    (h₁ : InducedBy χ₁ ψ₁) (h₂ : InducedBy χ₂ ψ₂)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hψ₁ : Q ≤ ψ₁.modulus) (hψ₂ : Q ≤ ψ₂.modulus)
    (m f z₁ z₂ : O) (hm : m ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u₁ u₂ : Oˣ) (a₁ b₁ a₂ b₂ : ℕ) (r₁ r₂ : O)
    (hr₁ : CanonicalQuadraticSieve.Supported (Ideal.span {r₁}))
    (hr₂ : CanonicalQuadraticSieve.Supported (Ideal.span {r₂}))
    (hpr₁ : λ₀ ^ 2 ∣ r₁ - 1) (hpr₂ : λ₀ ^ 2 ∣ r₂ - 1)
    (hx₁ : f ^ 4 * z₁ = (u₁ : O) * λ₀ ^ a₁ * (2 : O) ^ b₁ * r₁)
    (hx₂ : f ^ 4 * z₂ = (u₂ : O) * λ₀ ^ a₂ * (2 : O) ^ b₂ * r₂)
    (hχ₁ : ∀ n, elementCoeff χ₁ n = rowTwist (HeckeRowClosure.elementHom η) m f z₁ n)
    (hχ₂ : ∀ n, elementCoeff χ₂ n = rowTwist (HeckeRowClosure.elementHom η) m f z₂ n)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P)
    (hchar : ringChar (O ⧸ P) ≠ 2) (hQP : IsCoprime Q P) :
    valuation (Ideal.span {r₁}) P % 6 = valuation (Ideal.span {r₂}) P % 6 := by
  apply local_rows_profile η χ₁ χ₂ ψ₁ ψ₂ h₁ h₂ Q (Ideal.span {m})
    (Ideal.span {r₁}) (Ideal.span {r₂}) P hQ (Ideal.span_singleton_eq_bot.not.mpr hm)
    hψ₁ hψ₂ hr₁ hr₂ hg hchar hQP
  · intro n hn hc
    exact actual_row_on_fixed_units η χ₁ m f z₁ hmLam hm2 u₁ a₁ b₁ r₁ hr₁ hpr₁ hx₁ hχ₁ n (hQ72 hn) hc
  · intro n hn hc
    exact actual_row_on_fixed_units η χ₂ m f z₂ hmLam hm2 u₂ a₂ b₂ r₂ hr₂ hpr₂ hx₂ hχ₂ n (hQ72 hn) hc

theorem valuation_span_eq_zero_of_not_mem (x : O) (P : Ideal O) (hx : x ∉ P) :
    valuation (Ideal.span {x}) P = 0 := by
  have hx0 : x ≠ 0 := fun hz => hx (hz ▸ P.zero_mem)
  apply Multiset.count_eq_zero.mpr
  intro hP
  have hle := ((Ideal.mem_normalizedFactors_iff (Ideal.span_singleton_eq_bot.not.mpr hx0)).mp hP).2
  exact hx (hle (Ideal.subset_span (by simp)))

theorem valuation_supported_numerator (x : O) (u : Oˣ) (a b : ℕ) (r : O)
    (hr : r ≠ 0) (hx : x = (u : O) * λ₀ ^ a * (2 : O) ^ b * r)
    (P : Ideal O) (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P) :
    valuation (Ideal.span {x}) P = valuation (Ideal.span {r}) P := by
  have hu : Ideal.span {(u : O)} = (1 : Ideal O) := by
    simpa only [Ideal.one_eq_top] using (Ideal.span_singleton_eq_top.mpr u.isUnit)
  have hl0 : Ideal.span {λ₀} ≠ (0 : Ideal O) :=
    Ideal.span_singleton_eq_bot.not.mpr PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero
  have h20 : Ideal.span {(2 : O)} ≠ (0 : Ideal O) :=
    Ideal.span_singleton_eq_bot.not.mpr (by norm_num)
  have hr0 : Ideal.span {r} ≠ (0 : Ideal O) := Ideal.span_singleton_eq_bot.not.mpr hr
  rw [hx]
  simp only [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, hu, one_mul]
  rw [valuation_mul _ _ _ (mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ h20)) hr0,
    valuation_mul _ _ _ (pow_ne_zero _ hl0) (pow_ne_zero _ h20), valuation_pow, valuation_pow,
    valuation_span_eq_zero_of_not_mem λ₀ P hg, valuation_span_eq_zero_of_not_mem (2 : O) P h2]
  omega

theorem valuation_mod_six_cancel_frozen (A I J P : Ideal O)
    (hA : A ≠ 0) (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : valuation (A * I) P % 6 = valuation (A * J) P % 6) :
    valuation I P % 6 = valuation J P % 6 := by
  rw [valuation_mul A I P hA hI, valuation_mul A J P hA hJ] at h
  exact Nat.ModEq.add_left_cancel' (valuation A P) h

theorem actual_rows_profile (η χ₁ χ₂ ψ₁ ψ₂ : Character)
    (h₁ : InducedBy χ₁ ψ₁) (h₂ : InducedBy χ₂ ψ₂)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hψ₁ : Q ≤ ψ₁.modulus) (hψ₂ : Q ≤ ψ₂.modulus)
    (m f z₁ z₂ : O) (hm : m ≠ 0) (hf : f ≠ 0) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hχ₁ : ∀ n, elementCoeff χ₁ n = rowTwist (HeckeRowClosure.elementHom η) m f z₁ n)
    (hχ₂ : ∀ n, elementCoeff χ₂ n = rowTwist (HeckeRowClosure.elementHom η) m f z₂ n)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P)
    (hQP : IsCoprime Q P) :
    valuation (Ideal.span {z₁}) P % 6 = valuation (Ideal.span {z₂}) P % 6 := by
  obtain ⟨u₁, a₁, b₁, r₁, hr₁, hpr₁, hx₁⟩ :=
    exists_supported_numerator_factorization (f ^ 4 * z₁) (mul_ne_zero (pow_ne_zero _ hf) hz₁)
  obtain ⟨u₂, a₂, b₂, r₂, hr₂, hpr₂, hx₂⟩ :=
    exists_supported_numerator_factorization (f ^ 4 * z₂) (mul_ne_zero (pow_ne_zero _ hf) hz₂)
  have hr₁0 := Ideal.span_singleton_eq_bot.not.mp hr₁.1
  have hr₂0 := Ideal.span_singleton_eq_bot.not.mp hr₂.1
  have h := actual_rows_good_profile η χ₁ χ₂ ψ₁ ψ₂ h₁ h₂ Q hQ hQ72 hψ₁ hψ₂
    m f z₁ z₂ hm hmLam hm2 u₁ u₂ a₁ b₁ a₂ b₂ r₁ r₂ hr₁ hr₂ hpr₁ hpr₂ hx₁ hx₂
    hχ₁ hχ₂ P hg (ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem P h2) hQP
  rw [← valuation_supported_numerator _ u₁ a₁ b₁ r₁ hr₁0 hx₁ P hg h2,
    ← valuation_supported_numerator _ u₂ a₂ b₂ r₂ hr₂0 hx₂ P hg h2,
    ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton] at h
  exact valuation_mod_six_cancel_frozen _ _ _ P
    (Ideal.span_singleton_eq_bot.not.mpr (pow_ne_zero _ hf))
    (Ideal.span_singleton_eq_bot.not.mpr hz₁) (Ideal.span_singleton_eq_bot.not.mpr hz₂) h

theorem local_row_valuation_zero (η χ ψ : Character) (h : InducedBy χ ψ)
    (Q K I P : Ideal O) (hQ : Q ≠ ⊤) (hK : K ≠ 0)
    (hψ : Q ≤ ψ.modulus) (hI : CanonicalQuadraticSieve.Supported I)
    [P.IsMaximal] (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (hQP : IsCoprime Q P) (hηP : IsCoprime η.modulus P)
    (hrow : ∀ n : O, n - 1 ∈ Q → IsCoprime (Ideal.span {n}) K →
      elementCoeff χ n = elementCoeff η n * idealRowHom n I) :
    valuation I P % 6 = 0 := by
  have hzero : valuation (1 : Ideal O) P % 6 = 0 := by
    simp only [valuation, normalizedFactors_one, Multiset.count_zero, Nat.zero_mod]
  rw [← hzero]
  apply valuation_mod_six_of_unit_agreement (Q * η.modulus) (K * χ.modulus) I 1 P
    (mul_ne_zero hK χ.modulus_ne_bot) hI
    (by constructor; exact one_ne_zero; simp only [normalizedFactors_one, Multiset.notMem_zero, false_implies, implies_true]) hg hchar
    (hQP.mul_left hηP)
  intro n hn hc
  obtain ⟨hcK, hcχ⟩ := IsCoprime.mul_right_iff.mp hc
  have hnQ := Ideal.mul_le_left hn
  have hη : elementCoeff η n = 1 := by
    change η.residue (Ideal.Quotient.mk η.modulus n) = 1
    rw [(Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (Ideal.mul_le_right hn), map_one]
  have he := elementCoeff_eq_one_of_inducedBy χ ψ h Q hQ hψ n hnQ hcχ
  rw [hrow n hnQ hcK, hη, one_mul] at he
  simpa only [map_one] using he

theorem actual_row_numerator_valuation_zero (η χ ψ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hψ : Q ≤ ψ.modulus)
    (m f z : O) (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m f z n)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P)
    (hQP : IsCoprime Q P) (hηP : IsCoprime η.modulus P) :
    valuation (Ideal.span {f ^ 4 * z}) P % 6 = 0 := by
  obtain ⟨u, a, b, r, hr, hpr, hx⟩ :=
    exists_supported_numerator_factorization (f ^ 4 * z) (mul_ne_zero (pow_ne_zero _ hf) hz)
  rw [valuation_supported_numerator _ u a b r (Ideal.span_singleton_eq_bot.not.mp hr.1) hx P hg h2]
  apply local_row_valuation_zero η χ ψ h Q (Ideal.span {m}) (Ideal.span {r}) P hQ
    (Ideal.span_singleton_eq_bot.not.mpr hm) hψ hr hg
    (ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem P h2) hQP hηP
  intro n hn hc
  exact actual_row_on_fixed_units η χ m f z hmLam hm2 u a b r hr hpr hx hχ n (hQ72 hn) hc

theorem actual_row_forced_residue_four (η χ ψ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hψ : Q ≤ ψ.modulus)
    (m A z : O) (hm : m ≠ 0) (hA : A ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m 1 (A * z) n)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P)
    (hQP : IsCoprime Q P) (hηP : IsCoprime η.modulus P)
    (hA2 : valuation (Ideal.span {A}) P % 6 = 2) :
    valuation (Ideal.span {z}) P % 6 = 4 := by
  have he := actual_row_numerator_valuation_zero η χ ψ h Q hQ hQ72 hψ m 1 (A * z)
    hm one_ne_zero (mul_ne_zero hA hz) hmLam hm2 hχ P hg h2 hQP hηP
  simp only [one_pow, one_mul] at he
  rw [← Ideal.span_singleton_mul_span_singleton, valuation_mul _ _ _
    (Ideal.span_singleton_eq_bot.not.mpr hA) (Ideal.span_singleton_eq_bot.not.mpr hz),
    Nat.add_mod, hA2] at he
  omega

theorem actual_forced_fourth_power (η χ ψ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hψ : Q ≤ ψ.modulus)
    (m A z : O) (hm : m ≠ 0) (hA : A ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m 1 (A * z) n)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ normalizedFactors D, λ₀ ∉ P ∧ (2 : O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P % 6 = 2) :
    D ^ 4 ∣ sixthRemainder (Ideal.span {z}) ∧
      (Ideal.absNorm D : ℝ) ^ 4 ≤ Ideal.absNorm (sixthRemainder (Ideal.span {z})) := by
  have hf : ∀ P ∈ normalizedFactors D, valuation (Ideal.span {z}) P % 6 = 4 := by
    intro P hP
    have hp := prime_of_normalized_factor P hP
    let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    obtain ⟨hg, h2, hQP, hηP, hA2⟩ := hgood P hP
    exact actual_row_forced_residue_four η χ ψ h Q hQ hQ72 hψ m A z hm hA hz hmLam hm2 hχ
      P hg h2 hQP hηP hA2
  exact ⟨forced_fourth_power_dvd _ D hD hf, forced_fourth_power_norm_le _ D hD hf⟩

def FixedInducingRow (η : Character) (Q : Ideal O) (m A z : O) : Prop :=
  ∃ χ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
    InducedBy χ ψ ∧ Q ≤ ψ.modulus ∧
    ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m 1 (A * z) n

theorem fixed_inducing_rows_profile (η : Character) (Q : Ideal O)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A z₁ z₂ : O) (hm : m ≠ 0) (hA : A ≠ 0) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (h₁ : FixedInducingRow η Q m A z₁) (h₂ : FixedInducingRow η Q m A z₂)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P)
    (hQP : IsCoprime Q P) :
    valuation (Ideal.span {z₁}) P % 6 = valuation (Ideal.span {z₂}) P % 6 := by
  obtain ⟨χ₁, ψ₁, _, hi₁, hψ₁, hχ₁⟩ := h₁
  obtain ⟨χ₂, ψ₂, _, hi₂, hψ₂, hχ₂⟩ := h₂
  have he := actual_rows_profile η χ₁ χ₂ ψ₁ ψ₂ hi₁ hi₂ Q hQ hQ72 hψ₁ hψ₂
    m 1 (A * z₁) (A * z₂) hm one_ne_zero (mul_ne_zero hA hz₁) (mul_ne_zero hA hz₂)
    hmLam hm2 hχ₁ hχ₂ P hg h2 hQP
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton] at he
  exact valuation_mod_six_cancel_frozen _ _ _ P (Ideal.span_singleton_eq_bot.not.mpr hA)
    (Ideal.span_singleton_eq_bot.not.mpr hz₁) (Ideal.span_singleton_eq_bot.not.mpr hz₂) he

theorem fixed_inducing_rows_same_remainder (η : Character) (Q : Ideal O)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A z₁ z₂ : O) (hm : m ≠ 0) (hA : A ≠ 0) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (h₁ : FixedInducingRow η Q m A z₁) (h₂ : FixedInducingRow η Q m A z₂)
    (S : Finset (Ideal O))
    (houtside : ∀ P : Ideal O, Prime P → P ∉ S →
      λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P)
    (hsector : ∀ P ∈ S, valuation (Ideal.span {z₁}) P % 6 = valuation (Ideal.span {z₂}) P % 6) :
    sixthRemainder (Ideal.span {z₁}) = sixthRemainder (Ideal.span {z₂}) := by
  apply sixthRemainder_eq_of_prime_profile (sixthRemainder_ne_zero _)
  intro P hP
  rw [sixthRemainder_valuation]
  by_cases hPS : P ∈ S
  · exact hsector P hPS
  · let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
    obtain ⟨hg, h2, hQP⟩ := houtside P hP hPS
    exact fixed_inducing_rows_profile η Q hQ hQ72 m A z₁ z₂ hm hA hz₁ hz₂ hmLam hm2
      h₁ h₂ P hg h2 hQP

theorem fixed_inducing_remainder_card (η : Character) (Q : Ideal O)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (S : Finset (Ideal O))
    (houtside : ∀ P : Ideal O, Prime P → P ∉ S →
      λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P)
    (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, FixedInducingRow η Q m A z) :
    (T.image (fun z => sixthRemainder (Ideal.span {z}))).card ≤ 6 ^ S.card := by
  let Rs := T.image (fun z => sixthRemainder (Ideal.span {z}))
  let code : Ideal O → (S → Fin 6) :=
    fun R P => ⟨valuation R P.val % 6, Nat.mod_lt _ (by decide)⟩
  have hinj : (Rs : Set (Ideal O)).InjOn code := by
    intro R hR R' hR' he
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hR'
    apply fixed_inducing_rows_same_remainder η Q hQ hQ72 m A z z' hm hA (hT z hz) (hT z' hz')
      hmLam hm2 (hex z hz) (hex z' hz') S houtside
    intro P hP
    have hh := congrArg (fun f : S → Fin 6 => (f ⟨P, hP⟩).val) he
    simpa only [code, sixthRemainder_valuation, Nat.mod_mod] using hh
  have hc := Finset.card_le_card_of_injOn code (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _) hinj
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Rs] using hc

theorem fixed_inducing_row_count (η : Character) (Q : Ideal O)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (S : Finset (Ideal O))
    (houtside : ∀ P : Ideal O, Prime P → P ∉ S →
      λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P)
    (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, FixedInducingRow η Q m A z)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ normalizedFactors D, λ₀ ∉ P ∧ (2 : O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P % 6 = 2)
    (Z C M F : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hDnorm : Z ^ (F / 2) ≤ (Ideal.absNorm D : ℝ))
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ M) :
    (T.card : ℝ) ≤ 768 * (6 : ℝ) ^ S.card * C ^ (1 / 6 : ℝ) * Z ^ ((M - 2 * F) / 6) := by
  let Rs := T.image (fun z => sixthRemainder (Ideal.span {z}))
  have hRs : ∀ R ∈ Rs, R ≠ 0 := by
    intro R hR
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hR
    exact sixthRemainder_ne_zero _
  have hRnorm : ∀ R ∈ Rs, Z ^ (2 * F) ≤ (Ideal.absNorm R : ℝ) := by
    intro R hR
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨χ, ψ, _, hi, hψ, hχ⟩ := hex z hz
    have hf := (actual_forced_fourth_power η χ ψ hi Q hQ hQ72 hψ m A z hm hA
      (hT z hz) hmLam hm2 hχ D hD hgood).2
    calc
      Z ^ (2 * F) = (Z ^ (F / 2)) ^ (4 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hZ.le]
        congr 1
        norm_num
        ring
      _ ≤ (Ideal.absNorm D : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ (Real.rpow_nonneg hZ.le _) hDnorm _
      _ ≤ _ := hf
  have hcount := element_count_power_scale_family T Rs hRs Z C M (2 * F) hZ hC hRnorm hT
    (fun z hz => Finset.mem_image.mpr ⟨z, hz, rfl⟩) hN
  have hcard : (Rs.card : ℝ) ≤ (6 : ℝ) ^ S.card := by
    exact_mod_cast fixed_inducing_remainder_card η Q hQ hQ72 m A hm hA hmLam hm2 S houtside T hT hex
  apply hcount.trans
  gcongr

theorem outside_fixed_support (Q : Ideal O) (hQ : Q ≠ 0)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (P : Ideal O) (hP : Prime P)
    (hPS : P ∉ (normalizedFactors Q).toFinset) :
    λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P := by
  let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  have hcop : IsCoprime Q P := by
    apply Ideal.coprime_of_no_prime_ge
    intro J hQJ hPJ hJ
    have hPJ' : P = J := (inferInstance : P.IsMaximal).eq_of_le hJ.ne_top hPJ
    apply hPS
    apply Multiset.mem_toFinset.mpr
    apply (Ideal.mem_normalizedFactors_iff hQ).mpr
    exact ⟨Ideal.isPrime_of_prime hP, hPJ' ▸ hQJ⟩
  have h72 : (72 : O) ∉ P := by
    intro hh
    have hle : Q ≤ P := hQ72.trans ((Ideal.span_singleton_le_iff_mem _).mpr hh)
    have he := Ideal.isCoprime_iff_sup_eq.mp hcop
    rw [sup_eq_right.mpr hle] at he
    exact hP.ne_one (by simpa only [Ideal.one_eq_top] using he)
  have hl : λ₀ ∣ (72 : O) :=
    (dvd_pow_self λ₀ (by decide : (2 : ℕ) ≠ 0)).trans
      (ActualEisensteinCubic.lambda_sq_dvd_three.trans (show (3 : O) ∣ 72 from ⟨24, by norm_num⟩))
  have h2 : (2 : O) ∣ 72 := ⟨36, by norm_num⟩
  refine ⟨?_, ?_, hcop⟩
  · intro hh
    obtain ⟨v, hv⟩ := hl
    exact h72 (hv ▸ P.mul_mem_right v hh)
  · intro hh
    obtain ⟨v, hv⟩ := h2
    exact h72 (hv ▸ P.mul_mem_right v hh)

theorem fixed_support_exceptional_count (η : Character) (Q : Ideal O)
    (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, FixedInducingRow η Q m A z)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ normalizedFactors D, λ₀ ∉ P ∧ (2 : O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P % 6 = 2)
    (Z C M F : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hDnorm : Z ^ (F / 2) ≤ (Ideal.absNorm D : ℝ))
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ M) :
    (T.card : ℝ) ≤ 768 * (6 : ℝ) ^ (normalizedFactors Q).toFinset.card *
      C ^ (1 / 6 : ℝ) * Z ^ ((M - 2 * F) / 6) :=
  fixed_inducing_row_count η Q hQ hQ72 m A hm hA hmLam hm2
    (normalizedFactors Q).toFinset (outside_fixed_support Q hQ0 hQ72) T hT hex
    D hD hgood Z C M F hZ hC hDnorm hN

theorem fixed_support_exceptional_count_weaker (η : Character) (Q : Ideal O)
    (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, FixedInducingRow η Q m A z)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ normalizedFactors D, λ₀ ∉ P ∧ (2 : O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P % 6 = 2)
    (Z C M F : ℝ) (hZ : 1 ≤ Z) (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hDnorm : Z ^ (F / 2) ≤ (Ideal.absNorm D : ℝ))
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ M) :
    (T.card : ℝ) ≤ 768 * (6 : ℝ) ^ (normalizedFactors Q).toFinset.card *
      C ^ (1 / 6 : ℝ) * Z ^ ((M - F) / 6) := by
  apply (fixed_support_exceptional_count η Q hQ0 hQ hQ72 m A hm hA hmLam hm2 T hT hex
    D hD hgood Z C M F (zero_lt_one.trans_le hZ) hC hDnorm hN).trans
  gcongr
  linarith

theorem fixed_inducing_rows_empty (η : Character) (Q : Ideal O)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, FixedInducingRow η Q m A z)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ normalizedFactors D, λ₀ ∉ P ∧ (2 : O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P % 6 = 2)
    (H : ℝ) (hH : H < (Ideal.absNorm D : ℝ) ^ 4)
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ H) : T = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨χ, ψ, _, hi, hψ, hχ⟩ := hex z hz
  have hf := (actual_forced_fourth_power η χ ψ hi Q hQ hQ72 hψ m A z hm hA
    (hT z hz) hmLam hm2 hχ D hD hgood).2
  have hr := sixthRemainder_norm_le (Ideal.span {z}) (Ideal.span_singleton_eq_bot.not.mpr (hT z hz))
  exact (not_le_of_gt hH) (hf.trans (hr.trans (hN z hz)))

end SevenEighths.CenteredExceptionalProfile

end

end OAI
end OAIOriginalModule1294

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.ZeroSupremum
Source SHA256: 3b3ca749fb669e5a278a5d956a61eec73bab919e0369f7d46d2abae2e0f0011e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1295



namespace OAI

noncomputable section
namespace SevenEighths.HeckeZeroSupremum
open HeckeFamily

def zeroRealParts : Set ℝ :=
  {x | ∃ (χ : Character) (s : ℂ), 0 < s.re ∧
    (s ≠ 1 ∨ χ.residue ≠ 1) ∧ LFunction χ s = 0 ∧ s.re = x}

def zeroSetWithSentinel : Set ℝ := insert (1 / 2) zeroRealParts

def beta : ℝ := sSup zeroSetWithSentinel

theorem zeroRealParts_le_one {x : ℝ} (hx : x ∈ zeroRealParts) : x ≤ 1 := by
  obtain ⟨χ, s, _, _, hz, rfl⟩ := hx
  by_contra h
  exact LFunction_ne_zero_of_one_lt_re χ (lt_of_not_ge h) hz

theorem zeroSet_bddAbove : BddAbove zeroSetWithSentinel := by
  refine ⟨1, ?_⟩
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · exact zeroRealParts_le_one hx

theorem zeroSet_nonempty : zeroSetWithSentinel.Nonempty :=
  Set.insert_nonempty _ _

theorem half_le_beta : (1 / 2 : ℝ) ≤ beta :=
  le_csSup zeroSet_bddAbove (Set.mem_insert _ _)

theorem beta_le_one : beta ≤ 1 := by
  apply csSup_le zeroSet_nonempty
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · exact zeroRealParts_le_one hx

theorem zero_re_le_beta (χ : Character) {s : ℂ} (hs : 0 < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) (hz : LFunction χ s = 0) :
    s.re ≤ beta :=
  le_csSup zeroSet_bddAbove (Set.mem_insert_of_mem _ ⟨χ, s, hs, hpole, hz, rfl⟩)

theorem LFunction_ne_zero_of_beta_lt (χ : Character) {s : ℂ}
    (hs : beta < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    LFunction χ s ≠ 0 := by
  intro hz
  have hpos : 0 < s.re := lt_trans (by linarith [half_le_beta]) hs
  exact (not_lt_of_ge (zero_re_le_beta χ hpos hpole hz)) hs

theorem exists_zero_near_beta {ε : ℝ} (hε : 0 < ε)
    (hεsmall : (1 / 2 : ℝ) ≤ beta - ε) :
    ∃ (χ : Character) (s : ℂ), 0 < s.re ∧
      (s ≠ 1 ∨ χ.residue ≠ 1) ∧ LFunction χ s = 0 ∧ beta - ε < s.re := by
  obtain ⟨x, hx, hlt⟩ := Supremum.exists_gt_supremum_sub_of_insert
    zeroSet_bddAbove hε hεsmall
  obtain ⟨χ, s, hpos, hpole, hz, rfl⟩ := hx
  exact ⟨χ, s, hpos, hpole, hz, hlt⟩

theorem beta_le_seven_eighths_of_uniform_margin
    (hbound : 7 / 8 < beta →
      ∃ ω σ : ℝ, 0 < ω ∧ ω < beta - 7 / 8 ∧ 0 < σ ∧
        ∀ (χ : Character) (s : ℂ), 0 < s.re →
          (s ≠ 1 ∨ χ.residue ≠ 1) → LFunction χ s = 0 →
            s.re ≤ beta - Supremum.continuationMargin beta ω σ) :
    beta ≤ 7 / 8 := by
  apply Supremum.seven_eighths_of_uniform_margin_with_sentinel zeroSet_bddAbove
  intro hbeta
  obtain ⟨ω, σ, hω, hωb, hσ, hzeros⟩ := hbound hbeta
  refine ⟨ω, σ, hω, hωb, hσ, ?_⟩
  rintro x ⟨χ, s, hpos, hpole, hz, rfl⟩
  exact hzeros χ s hpos hpole hz

end SevenEighths.HeckeZeroSupremum

end

end OAI
end OAIOriginalModule1295

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.Reciprocal
Source SHA256: d243f1e44bb2fcec20d209300980172dcaf2f5a09e31c45dcb761343b9c9e89b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1296


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeReciprocal
open HeckeFamily HeckeCharacterAnalytic HeckeCoordinates

theorem coefficients_sum_ne_zero_of_principal (χ : Character) (hχ : χ.residue = 1) :
    (∑ a, coefficients χ a) ≠ 0 := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Fintype (O ⧸ χ.modulus) := Fintype.ofFinite _
  let e := Equiv.prodCongr (finCastEquiv χ.period) (finCastEquiv χ.period)
  have heq : (∑ a, coefficients χ a) =
      (Nat.card (coordinateQuotientHom χ).ker : ℂ) *
        (Fintype.card (O ⧸ χ.modulus)ˣ : ℂ) := by
    calc
      _ = ∑ a, χ.residue (coordinateQuotientHom χ (e a)) := by
        apply Finset.sum_congr rfl
        intro a _
        exact coefficients_eq_quotient_character χ a
      _ = ∑ a : ZMod χ.period × ZMod χ.period,
          χ.residue (coordinateQuotientHom χ a) :=
        e.bijective.sum_comp (fun a => χ.residue (coordinateQuotientHom χ a))
      _ = _ := by
        rw [sum_comp_additiveHom _ (coordinateQuotientHom_surjective χ), hχ,
          MulChar.sum_one_eq_card_units]
  rw [heq]
  apply mul_ne_zero
  · exact_mod_cast (Nat.card_pos (α := (coordinateQuotientHom χ).ker)).ne'
  · exact_mod_cast (Fintype.card_pos (α := (O ⧸ χ.modulus)ˣ)).ne'

theorem dualScalar_ne_zero (N : ℕ) [NeZero N] : HeckeTheta.dualScalar N ≠ 0 := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  unfold HeckeTheta.dualScalar
  apply mul_ne_zero <;> apply Complex.ofReal_ne_zero.mpr
  · exact (Real.rpow_pos_of_pos (sq_pos_of_pos hN) _).ne'
  · exact (Real.rpow_pos_of_pos (mul_pos (by norm_num) (sq_pos_of_pos hN)) _).ne'

theorem principal_dual_constant_ne_zero (χ : Character) (hχ : χ.residue = 1) :
    (HeckeTheta.pair (coefficients χ)).g₀ ≠ 0 := by
  rw [HeckeTheta.pair_g₀]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (dualScalar_ne_zero χ.period))
    (coefficients_sum_ne_zero_of_principal χ hχ)

def regularizedL (χ : Character) (s : ℂ) : ℂ :=
  HeckeTheta.regularizedLatticeL (coefficients χ) s / 6

theorem regularizedL_eq (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    regularizedL χ s = (s - 1) * LFunction χ s := by
  unfold regularizedL LFunction continuedLattice
  rw [HeckeTheta.regularizedLatticeL_eq _ h0 h1]
  ring

theorem regularizedL_at_one (χ : Character) :
    regularizedL χ 1 = (Real.pi : ℂ) * (HeckeTheta.pair (coefficients χ)).g₀ / 6 := by
  simp [regularizedL, HeckeTheta.regularizedLatticeL, HeckeTheta.regularizedCompleted]

theorem regularizedL_ne_zero_at_one (χ : Character) (hχ : χ.residue = 1) :
    regularizedL χ 1 ≠ 0 := by
  rw [regularizedL_at_one]
  exact div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    (principal_dual_constant_ne_zero χ hχ)) (by norm_num)

theorem regularizedL_differentiableAt (χ : Character) {s : ℂ} (h0 : s ≠ 0) :
    DifferentiableAt ℂ (regularizedL χ) s :=
  (HeckeTheta.regularizedLatticeL_differentiableAt _ h0).div_const 6

theorem regularizedL_ne_zero (χ : Character) (hχ : χ.residue = 1) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) : regularizedL χ s ≠ 0 := by
  by_cases h1 : s = 1
  · subst s
    exact regularizedL_ne_zero_at_one χ hχ
  have h0 : s ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hs
    linarith [HeckeZeroSupremum.half_le_beta]
  rw [regularizedL_eq χ h0 h1]
  exact mul_ne_zero (sub_ne_zero.mpr h1)
    (HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ hs (Or.inl h1))

def reciprocal (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue = 1 then (s - 1) / regularizedL χ s else (LFunction χ s)⁻¹

theorem reciprocal_eq_inv (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    reciprocal χ s = (LFunction χ s)⁻¹ := by
  unfold reciprocal
  split_ifs
  · rw [regularizedL_eq χ h0 h1, div_mul_eq_div_div,
      div_self (sub_ne_zero.mpr h1), one_div]
  · rfl

theorem reciprocal_principal_one (χ : Character) (hχ : χ.residue = 1) :
    reciprocal χ 1 = 0 := by simp [reciprocal, hχ]

theorem reciprocal_differentiableAt (χ : Character) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) : DifferentiableAt ℂ (reciprocal χ) s := by
  have h0 : s ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hs
    linarith [HeckeZeroSupremum.half_le_beta]
  by_cases hχ : χ.residue = 1
  · have heq : reciprocal χ = fun z => (z - 1) / regularizedL χ z := by
      funext z
      simp [reciprocal, hχ]
    rw [heq]
    exact (differentiableAt_id.sub_const 1).div
      (regularizedL_differentiableAt χ h0) (regularizedL_ne_zero χ hχ hs)
  · have heq : reciprocal χ = fun z => (LFunction χ z)⁻¹ := by
      funext z
      simp [reciprocal, hχ]
    rw [heq]
    exact (LFunction_differentiableAt χ h0 (Or.inr hχ)).inv
      (HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ hs (Or.inr hχ))

end SevenEighths.HeckeReciprocal

end

end OAI
end OAIOriginalModule1296

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion
Source SHA256: dfb26a8cb221175f3c7cef4e854e21c467b040ca903bde1ff75bca00ff7eeee1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1297




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeFiniteDeletion
open HeckeFamily HeckeReciprocal

def factors (M : Ideal O) (ψ : Character) : ℂ → ℂ :=
  EulerFactors.deletedProduct (SmoothMobiusCorrection.primeSet M)
    (fun P => Ideal.absNorm P.val) (fun P => idealCoeff ψ P.val)

theorem factors_eq (M : Ideal O) (ψ : Character) (s : ℂ) :
    factors M ψ s = ∏ P ∈ SmoothMobiusCorrection.primeSet M,
      (1 - IdealEuler.weighted (idealCoeff ψ) s P.val) := by
  apply Finset.prod_congr rfl
  intro P _
  simp only [EulerFactors.factor, IdealEuler.weighted, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, IdealEuler.normWeight, CubicEisenstein.fullIdealWeight,
    P.property.ne_zero, ite_false, Complex.ofReal_natCast]

theorem factors_differentiable (M : Ideal O) (ψ : Character) :
    Differentiable ℂ (factors M ψ) := by
  apply EulerFactors.differentiable_deletedProduct
  intro P _
  have h := SmoothMobiusCorrection.prime_norm_two_le P
  exact_mod_cast (by omega : 0 < Ideal.absNorm P.val)

theorem factors_ne_zero (M : Ideal O) (ψ : Character) {s : ℂ} (hs : 0 < s.re) :
    factors M ψ s ≠ 0 := by
  apply EulerFactors.deletedProduct_ne_zero _ _ _ _ _ hs
  · intro P _
    have h := SmoothMobiusCorrection.prime_norm_two_le P
    exact_mod_cast (by omega : 1 < Ideal.absNorm P.val)
  · intro P _
    exact idealCoeff_norm_le_one ψ P.val

theorem LFunction_eq_of_mask_right (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = LFunction ψ s * factors χ.modulus ψ s := by
  rw [LFunction_eq_series χ hs, LFunction_eq_series ψ hs, factors_eq]
  exact IdealEuler.series_of_coprime_mask χ.modulus χ.modulus_ne_bot
    _ _ (idealCoeff_norm_le_one ψ) hmask s hs

theorem regularizedL_analytic (χ : Character) :
    AnalyticOnNhd ℂ (regularizedL χ) {s : ℂ | 0 < s.re} := by
  apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
  intro s hs
  exact (regularizedL_differentiableAt χ (by intro h; simp [h] at hs)).differentiableWithinAt

theorem regularizedL_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) :
    regularizedL χ s = regularizedL ψ s * factors χ.modulus ψ s := by
  have hf : AnalyticOnNhd ℂ (factors χ.modulus ψ) {z : ℂ | 0 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
    exact (factors_differentiable _ _).differentiableOn
  apply Eq.symm
  apply Continuation.product_identity_on_halfPlane 0 1
    (regularizedL ψ) (factors χ.modulus ψ) (regularizedL χ)
    (regularizedL_analytic ψ) hf (regularizedL_analytic χ) _ hs
  intro z hz
  have hz' : 1 < z.re := by simpa using hz
  have h0 : z ≠ 0 := by intro h; norm_num [h] at hz'
  have h1 : z ≠ 1 := by intro h; norm_num [h] at hz'
  rw [regularizedL_eq χ h0 h1, regularizedL_eq ψ h0 h1,
    LFunction_eq_of_mask_right χ ψ hmask hz']
  ring

theorem LFunction_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    LFunction χ s = LFunction ψ s * factors χ.modulus ψ s := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hs
  have h := regularizedL_eq_of_mask χ ψ hmask hs
  rw [regularizedL_eq χ h0 h1, regularizedL_eq ψ h0 h1, mul_assoc] at h
  exact mul_left_cancel₀ (sub_ne_zero.mpr h1) h

theorem regularizedL_one_ne_zero_iff (χ : Character) :
    regularizedL χ 1 ≠ 0 ↔ χ.residue = 1 := by
  constructor
  · intro h
    by_contra hχ
    rw [regularizedL_at_one,
      HeckeTheta.pair_g₀_eq_zero _ (HeckeCharacterAnalytic.coefficients_sum_eq_zero χ hχ),
      mul_zero, zero_div] at h
    exact h rfl
  · exact regularizedL_ne_zero_at_one χ

theorem principal_iff_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0) :
    χ.residue = 1 ↔ ψ.residue = 1 := by
  rw [← regularizedL_one_ne_zero_iff χ, ← regularizedL_one_ne_zero_iff ψ,
    regularizedL_eq_of_mask χ ψ hmask (by norm_num : 0 < (1 : ℂ).re),
    mul_ne_zero_iff, and_iff_left (factors_ne_zero χ.modulus ψ (by norm_num))]

theorem LFunction_eq_of_mask_nonprincipal (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    (hχ : χ.residue ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s = LFunction ψ s * factors χ.modulus ψ s := by
  have hψ : ψ.residue ≠ 1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
  have ha (η : Character) (hη : η.residue ≠ 1) :
      AnalyticOnNhd ℂ (LFunction η) {z : ℂ | 0 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
    intro z hz
    exact (LFunction_differentiableAt η (by intro h; simp [h] at hz)
      (Or.inr hη)).differentiableWithinAt
  have hf : AnalyticOnNhd ℂ (factors χ.modulus ψ) {z : ℂ | 0 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
    exact (factors_differentiable _ _).differentiableOn
  apply Eq.symm
  apply Continuation.product_identity_on_halfPlane 0 1
    (LFunction ψ) (factors χ.modulus ψ) (LFunction χ) (ha ψ hψ) hf (ha χ hχ) _ hs
  intro z hz
  exact (LFunction_eq_of_mask_right χ ψ hmask (by simpa using hz)).symm

theorem LFunction_eq_of_mask_nonpole (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    LFunction χ s = LFunction ψ s * factors χ.modulus ψ s := by
  rcases hpole with h1 | hχ
  · exact LFunction_eq_of_mask χ ψ hmask hs h1
  · exact LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hs

theorem exists_primitive_same_zeros (χ : Character) :
    ∃ ψ : Character, χ.modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ χ.modulus.absNorm ∧
      ∀ s : ℂ, 0 < s.re → s ≠ 1 →
        (LFunction χ s = 0 ↔ LFunction ψ s = 0) := by
  obtain ⟨ψ, hmod, hp, hnorm, hmask⟩ := exists_primitive_character χ
  refine ⟨ψ, hmod, hp, hnorm, ?_⟩
  intro s hs h1
  rw [LFunction_eq_of_mask χ ψ hmask hs h1, mul_eq_zero]
  exact or_iff_left (factors_ne_zero χ.modulus ψ hs)

theorem exists_primitive_zero (χ : Character) {s : ℂ}
    (hs : 0 < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) (hz : LFunction χ s = 0) :
    ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (s ≠ 1 ∨ ψ.residue ≠ 1) ∧ LFunction ψ s = 0 := by
  obtain ⟨ψ, _, hp, _, hmask⟩ := exists_primitive_character χ
  refine ⟨ψ, hp, ?_, ?_⟩
  · rcases hpole with h1 | hχ
    · exact Or.inl h1
    · exact Or.inr (fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h))
  · rw [LFunction_eq_of_mask_nonpole χ ψ hmask hs hpole, mul_eq_zero] at hz
    exact hz.resolve_right (factors_ne_zero χ.modulus ψ hs)

end SevenEighths.HeckeFiniteDeletion

end

end OAI
end OAIOriginalModule1297

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DeletionBounds
Source SHA256: 129624cafbac617ee0288024f623cc81fec9f7b16e8b5f4adc0c4890f83fde6b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1298


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDeletionBounds
open HeckeFamily

theorem constant_pow_primeSupport_bound (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Ideal O, M ≠ ⊥ →
      K^(IdealMobiusDivisorSum.primeSupport M).card ≤ C*(M.absNorm : ℝ)^ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max K 1)
  have hn0 : 0 < (n : ℝ) := by linarith [le_max_right K 1]
  have hKpow : K ≤ (2 : ℝ)^n := by
    have hn2 : (n : ℝ) ≤ (2 : ℝ)^n := by exact_mod_cast (show n < 2^n from Nat.lt_two_pow_self).le
    linarith [le_max_left K 1]
  obtain ⟨C, hC, hbound⟩ := SquarefreeDivisorBound.prime_support_subsets_bound
    (ε/(n : ℝ)) (div_pos hε hn0)
  refine ⟨C^n, by positivity, ?_⟩
  intro M hM
  calc
    _ ≤ ((2 : ℝ)^n)^(IdealMobiusDivisorSum.primeSupport M).card :=
      pow_le_pow_left₀ hK hKpow _
    _ = ((2 : ℝ)^(IdealMobiusDivisorSum.primeSupport M).card)^n := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ (C*(M.absNorm : ℝ)^(ε/(n : ℝ)))^n :=
      pow_le_pow_left₀ (by positivity) (hbound M hM) n
    _ = C^n*(M.absNorm : ℝ)^ε := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity), div_mul_cancel₀ _ hn0.ne']

def localBound (σ : ℝ) : ℝ := (1-(2 : ℝ)^(-σ))⁻¹

theorem localBound_pos {σ : ℝ} (hσ : 0 < σ) : 0 < localBound σ := by
  unfold localBound
  exact inv_pos.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)))

theorem term_bound {σ N : ℝ} (hσ : 0 < σ) (hN : 2 ≤ N)
    {a s : ℂ} (ha : ‖a‖ ≤ 1) (hs : σ ≤ s.re) :
    ‖a*(N : ℂ)^(-s)‖ ≤ (2 : ℝ)^(-σ) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < N), Complex.neg_re]
  apply (mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) _) ha).trans
  apply (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ N) (by linarith : -s.re ≤ -σ)).trans
  exact Real.rpow_le_rpow_of_nonpos (by norm_num) hN (by linarith)

theorem factor_bounds {σ N : ℝ} (hσ : 0 < σ) (hN : 2 ≤ N)
    {a s : ℂ} (ha : ‖a‖ ≤ 1) (hs : σ ≤ s.re) :
    ‖EulerFactors.factor N a s‖ ≤ localBound σ ∧
      ‖(EulerFactors.factor N a s)⁻¹‖ ≤ localBound σ := by
  have hδ : (2 : ℝ)^(-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hδ0 : 0 ≤ (2 : ℝ)^(-σ) := Real.rpow_nonneg (by norm_num) _
  have ht := term_bound hσ hN ha hs
  have hl : 1-(2 : ℝ)^(-σ) ≤ ‖EulerFactors.factor N a s‖ := by
    have hh := norm_sub_le (1-a*(N : ℂ)^(-s)) (-a*(N : ℂ)^(-s))
    have he : (1-a*(N : ℂ)^(-s))-(-a*(N : ℂ)^(-s)) = 1 := by ring
    rw [he, norm_one, neg_mul, norm_neg] at hh
    change 1-(2 : ℝ)^(-σ) ≤ ‖1-a*(N : ℂ)^(-s)‖
    linarith
  constructor
  · apply (norm_sub_le _ _).trans
    rw [norm_one]
    apply (add_le_add (le_refl 1) ht).trans
    unfold localBound
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by linarith : 0 < 1-(2 : ℝ)^(-σ))).mpr
    nlinarith [sq_nonneg ((2 : ℝ)^(-σ))]
  · rw [norm_inv]
    exact (inv_le_inv₀ (by linarith : 0 < ‖EulerFactors.factor N a s‖)
      (by linarith : 0 < 1-(2 : ℝ)^(-σ))).mpr hl

theorem factors_bound_pow (σ : ℝ) (hσ : 0 < σ) (M : Ideal O)
    (ψ : Character) {s : ℂ} (hs : σ ≤ s.re) :
    ‖HeckeFiniteDeletion.factors M ψ s‖ ≤
      (localBound σ)^(IdealMobiusDivisorSum.primeSupport M).card ∧
    ‖(HeckeFiniteDeletion.factors M ψ s)⁻¹‖ ≤
      (localBound σ)^(IdealMobiusDivisorSum.primeSupport M).card := by
  have hfactor (P : SmoothMobiusCorrection.PrimeIdeal) :
      ‖EulerFactors.factor (P.val.absNorm : ℝ) (idealCoeff ψ P.val) s‖ ≤ localBound σ ∧
      ‖(EulerFactors.factor (P.val.absNorm : ℝ) (idealCoeff ψ P.val) s)⁻¹‖ ≤ localBound σ :=
    factor_bounds hσ (by exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P)
      (idealCoeff_norm_le_one ψ P.val) hs
  have he : (∏ P ∈ SmoothMobiusCorrection.primeSet M, localBound σ) =
      (localBound σ)^(IdealMobiusDivisorSum.primeSupport M).card := by
    rw [SmoothMobiusCorrection.prod_primeSet M (fun _ => localBound σ)]
    simp
  constructor
  · unfold HeckeFiniteDeletion.factors EulerFactors.deletedProduct
    rw [norm_prod, ← he]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun P _ => (hfactor P).1)
  · unfold HeckeFiniteDeletion.factors EulerFactors.deletedProduct
    rw [← Finset.prod_inv_distrib, norm_prod, ← he]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun P _ => (hfactor P).2)

theorem factors_subpower_bound (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal O), M ≠ ⊥ → ∀ (ψ : Character) (s : ℂ),
      σ ≤ s.re → ‖HeckeFiniteDeletion.factors M ψ s‖ +
        ‖(HeckeFiniteDeletion.factors M ψ s)⁻¹‖ ≤ C*(M.absNorm : ℝ)^ε := by
  obtain ⟨C, hC, hb⟩ := constant_pow_primeSupport_bound (localBound σ) ε
    (localBound_pos hσ).le hε
  refine ⟨2*C, by positivity, ?_⟩
  intro M hM ψ s hs
  obtain ⟨h1, h2⟩ := factors_bound_pow σ hσ M ψ hs
  have h := hb M hM
  nlinarith

def radical (M : Ideal O) : Ideal O :=
  SmoothMobiusCorrection.primeProduct (SmoothMobiusCorrection.primeSet M)

theorem radical_ne_zero (M : Ideal O) : radical M ≠ 0 :=
  SmoothMobiusCorrection.primeProduct_ne_zero _

theorem factors_radical (M : Ideal O) (ψ : Character) (s : ℂ) :
    HeckeFiniteDeletion.factors (radical M) ψ s = HeckeFiniteDeletion.factors M ψ s := by
  unfold HeckeFiniteDeletion.factors radical
  rw [SmoothMobiusCorrection.primeSet_primeProduct]

theorem factors_radical_subpower_bound (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal O) (ψ : Character) (s : ℂ),
      σ ≤ s.re → ‖HeckeFiniteDeletion.factors M ψ s‖ +
        ‖(HeckeFiniteDeletion.factors M ψ s)⁻¹‖ ≤ C*((radical M).absNorm : ℝ)^ε := by
  obtain ⟨C, hC, hb⟩ := factors_subpower_bound σ ε hσ hε
  refine ⟨C, hC, ?_⟩
  intro M ψ s hs
  simpa only [factors_radical] using hb (radical M) (radical_ne_zero M) ψ s hs

theorem factor_bound_any_re {N : ℝ} (hN : 2 ≤ N) {a s : ℂ} (ha : ‖a‖ ≤ 1) :
    ‖EulerFactors.factor N a s‖ ≤ 2*N^(max (-s.re) 0) := by
  have hn : 1 ≤ N := by linarith
  have ht : ‖a*(N : ℂ)^(-s)‖ ≤ N^(-s.re) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < N), Complex.neg_re]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) _) ha
  have hpow : N^(-s.re) ≤ N^(max (-s.re) 0) :=
    Real.rpow_le_rpow_of_exponent_le hn (le_max_left _ _)
  have h1 : 1 ≤ N^(max (-s.re) 0) := Real.one_le_rpow hn (le_max_right _ _)
  have hb := norm_sub_le (1 : ℂ) (a*(N : ℂ)^(-s))
  rw [norm_one] at hb
  change ‖1-a*(N : ℂ)^(-s)‖ ≤ _
  linarith

theorem factors_bound_any_re (M : Ideal O) (ψ : Character) (s : ℂ) :
    ‖HeckeFiniteDeletion.factors M ψ s‖ ≤
      (2 : ℝ)^(SmoothMobiusCorrection.primeSet M).card *
        ((radical M).absNorm : ℝ)^(max (-s.re) 0) := by
  unfold HeckeFiniteDeletion.factors EulerFactors.deletedProduct
  rw [norm_prod]
  calc
    _ ≤ ∏ P ∈ SmoothMobiusCorrection.primeSet M,
        2*(P.val.absNorm : ℝ)^(max (-s.re) 0) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro P _
      exact factor_bound_any_re (show (2 : ℝ) ≤ (P.val.absNorm : ℝ) by exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P)
        (idealCoeff_norm_le_one ψ P.val)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const,
        Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
      simp only [radical, SmoothMobiusCorrection.primeProduct, map_prod, Nat.cast_prod]

theorem primeSet_card (M : Ideal O) :
    (SmoothMobiusCorrection.primeSet M).card =
      (IdealMobiusDivisorSum.primeSupport M).card := by
  unfold SmoothMobiusCorrection.primeSet
  rw [Finset.card_image_iff.mpr ?_, Finset.card_attach]
  intro P hP Q hQ h
  exact Subtype.ext (congrArg (fun R : SmoothMobiusCorrection.PrimeIdeal => R.val) h)

theorem factors_any_re_subpower_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal O) (ψ : Character) (s : ℂ),
      ‖HeckeFiniteDeletion.factors M ψ s‖ ≤
        C*((radical M).absNorm : ℝ)^(max (-s.re) 0 + ε) := by
  obtain ⟨C, hC, hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro M ψ s
  have hR : 0 < ((radical M).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero M))
  have hc : (2 : ℝ)^(SmoothMobiusCorrection.primeSet M).card ≤ C*((radical M).absNorm : ℝ)^ε := by
    have h := hb (radical M) (radical_ne_zero M)
    rw [← primeSet_card, radical, SmoothMobiusCorrection.primeSet_primeProduct] at h
    exact h
  apply (factors_bound_any_re M ψ s).trans
  calc
    _ ≤ (C*((radical M).absNorm : ℝ)^ε)*((radical M).absNorm : ℝ)^(max (-s.re) 0) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hR.le _)
    _ = _ := by rw [Real.rpow_add hR]; ring

end SevenEighths.HeckeDeletionBounds

end

end OAI
end OAIOriginalModule1298

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DeletionDerivative
Source SHA256: fe8264f1e6793b10da38218403f23fa0c55aefacaf1bab35e84d3abcb250770e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1299


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDeletionDerivative
open HeckeFamily HeckeDeletionBounds

theorem factor_deriv {N : ℝ} (hN : 0 < N) (a s : ℂ) :
    deriv (EulerFactors.factor N a) s = a*(N : ℂ)^(-s)*Complex.log (N : ℂ) := by
  have h := (hasDerivAt_const s (1 : ℂ)).sub
    (((hasDerivAt_id s).neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hN.ne'))).const_mul a)
  have h' : HasDerivAt (EulerFactors.factor N a)
      (a*(N : ℂ)^(-s)*Complex.log (N : ℂ)) s := by
    convert h using 1
    · funext z
      rfl
    · dsimp
      ring
  exact h'.deriv

theorem factor_logDeriv_norm {σ N : ℝ} (hσ : 0 < σ) (hN : 2 ≤ N)
    {a s : ℂ} (ha : ‖a‖ ≤ 1) (hs : σ ≤ s.re) :
    ‖logDeriv (EulerFactors.factor N a) s‖ ≤ localBound σ * Real.log N := by
  have hn0 : 0 < N := by linarith
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have ht := term_bound hσ hN ha hs
  have hδ : (2 : ℝ)^(-σ) ≤ 1 :=
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)).le
  have hf := (factor_bounds hσ hN ha hs).2
  rw [logDeriv_apply, factor_deriv hn0, div_eq_mul_inv, norm_mul, norm_mul,
    ← Complex.ofReal_log hn0.le, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]
  have hterm : ‖a*(N : ℂ)^(-s)‖ ≤ 1 := ht.trans hδ
  calc
    _ ≤ (1*Real.log N)*localBound σ := by gcongr
    _ = _ := by ring

theorem factors_logDeriv_norm (σ : ℝ) (hσ : 0 < σ) (M : Ideal O)
    (ψ : Character) {s : ℂ} (hs : σ ≤ s.re) :
    ‖logDeriv (HeckeFiniteDeletion.factors M ψ) s‖ ≤
      localBound σ * Real.log ((radical M).absNorm : ℝ) := by
  have hp0 (P : SmoothMobiusCorrection.PrimeIdeal) : 0 < (P.val.absNorm : ℝ) := by
    have h := SmoothMobiusCorrection.prime_norm_two_le P
    exact_mod_cast (by omega : 0 < P.val.absNorm)
  have hp2 (P : SmoothMobiusCorrection.PrimeIdeal) : 2 ≤ (P.val.absNorm : ℝ) := by
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P
  have he : logDeriv (HeckeFiniteDeletion.factors M ψ) s =
      ∑ P ∈ SmoothMobiusCorrection.primeSet M,
        logDeriv (EulerFactors.factor (P.val.absNorm : ℝ) (idealCoeff ψ P.val)) s := by
    apply logDeriv_fun_prod
    · intro P _
      exact EulerFactors.factor_ne_zero (by linarith [hp2 P]) (idealCoeff_norm_le_one ψ P.val)
        (hσ.trans_le hs)
    · intro P _
      exact EulerFactors.differentiable_factor (hp0 P) _ s
  rw [he]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ P ∈ SmoothMobiusCorrection.primeSet M, localBound σ*Real.log (P.val.absNorm : ℝ) := by
      apply Finset.sum_le_sum
      intro P _
      exact factor_logDeriv_norm hσ (hp2 P) (idealCoeff_norm_le_one ψ P.val) hs
    _ = localBound σ * Real.log ((radical M).absNorm : ℝ) := by
      rw [← Finset.mul_sum, ← Real.log_prod (fun P _ => (hp0 P).ne')]
      simp only [radical, SmoothMobiusCorrection.primeProduct, map_prod, Nat.cast_prod]

end SevenEighths.HeckeDeletionDerivative

end

end OAI
end OAIOriginalModule1299

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DeletionReciprocal
Source SHA256: 337a0e05e48896e92f7d19223c96c1225dfcb72111cc1b9394cba10f775e87ea
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1300


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDeletionReciprocal
open HeckeFamily HeckeFiniteDeletion HeckeReciprocal HeckeDeletionBounds

theorem reciprocal_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) :
    reciprocal χ s = reciprocal ψ s * (factors χ.modulus ψ s)⁻¹ := by
  by_cases hχ : χ.residue = 1
  · have hψ := (principal_iff_of_mask χ ψ hmask).mp hχ
    simp only [reciprocal, ite_eq_left hχ, ite_eq_left hψ]
    rw [regularizedL_eq_of_mask χ ψ hmask hs]
    ring
  · have hψ : ψ.residue ≠ 1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
    simp only [reciprocal, ite_eq_right hχ, ite_eq_right hψ]
    rw [LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hs, mul_inv]

theorem exists_primitive_reciprocal_reduction (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ χ : Character,
      ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
        ψ.modulus.absNorm ≤ χ.modulus.absNorm ∧
        (∀ I : Ideal O, idealCoeff χ I =
          if IsCoprime I χ.modulus then idealCoeff ψ I else 0) ∧
        ∀ s : ℂ, σ ≤ s.re →
          ‖reciprocal χ s‖ ≤ C*((radical χ.modulus).absNorm : ℝ)^ε * ‖reciprocal ψ s‖ := by
  obtain ⟨C, hC, hb⟩ := factors_radical_subpower_bound σ ε hσ hε
  refine ⟨C, hC, ?_⟩
  intro χ
  obtain ⟨ψ, _, hp, hn, hm⟩ := exists_primitive_character χ
  refine ⟨ψ, hp, hn, hm, ?_⟩
  intro s hs
  rw [reciprocal_eq_of_mask χ ψ hm (hσ.trans_le hs), norm_mul]
  have hf := hb χ.modulus ψ s hs
  have hfb : ‖(factors χ.modulus ψ s)⁻¹‖ ≤ C*((radical χ.modulus).absNorm : ℝ)^ε := by
    linarith [norm_nonneg (factors χ.modulus ψ s)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hfb (norm_nonneg (reciprocal ψ s))

end SevenEighths.HeckeDeletionReciprocal

end

end OAI
end OAIOriginalModule1300

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.ModulusRefinement
Source SHA256: 10760a970f8dc85bb90e2d797f12f13a34f280e5899b55fa34bc1111d73736c0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1301



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeFamily
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

def Character.refineModulus (η : Character) (M : Ideal O) (hM : M ≠ ⊥)
    (hle : M ≤ η.modulus) : Character :=
  Character.ofResidue M hM (ResidueCharacter.inflate hle η.residue)
    (ResidueCharacter.inflate_global_units hle η.residue η.unit_trivial)

theorem elementCoeff_refineModulus (η : Character) (M : Ideal O) (hM : M ≠ ⊥)
    (hle : M ≤ η.modulus) (n : O) :
    elementCoeff (η.refineModulus M hM hle) n =
      if IsUnit (Ideal.Quotient.mk M n) then elementCoeff η n else 0 :=
  ResidueCharacter.inflate_mk hle η.residue n

theorem idealCoeff_refineModulus (η : Character) (M : Ideal O) (hM : M ≠ ⊥)
    (hle : M ≤ η.modulus) (I : Ideal O) :
    idealCoeff (η.refineModulus M hM hle) I =
      if IsCoprime I M then idealCoeff η I else 0 :=
  IdealCharacter.ofResidue_source_mask M η.modulus _ _ _ _
    (ResidueCharacter.inflate_mk hle η.residue) I

theorem idealCoeff_source_mask (η : Character) (I : Ideal O) :
    idealCoeff η I = if IsCoprime I η.modulus then idealCoeff η I else 0 := by
  apply IdealCharacter.ofResidue_source_mask η.modulus η.modulus η.residue η.residue
    η.unit_trivial η.unit_trivial _ I
  intro n
  split_ifs with hn
  · rfl
  · exact MulChar.map_nonunit _ hn

def Character.excludePrimes (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) : Character :=
  η.refineModulus (η.modulus * ∏ P ∈ S, P)
    (mul_ne_zero η.modulus_ne_bot (Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero)))
    Ideal.mul_le_left

theorem idealCoeff_excludePrimes (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (I : Ideal O) :
    idealCoeff (η.excludePrimes S hS) I =
      if ∀ P ∈ S, IsCoprime I P then idealCoeff η I else 0 := by
  rw [Character.excludePrimes, idealCoeff_refineModulus, IsCoprime.mul_right_iff,
    IsCoprime.prod_right_iff]
  by_cases hη : IsCoprime I η.modulus
  · simp only [hη, true_and]
  · have hz : idealCoeff η I = 0 := by simpa only [hη, ite_false] using idealCoeff_source_mask η I
    simp [hη, hz]

theorem excludePrimes_mask (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (I : Ideal O) :
    idealCoeff (η.excludePrimes S hS) I =
      if IsCoprime I (η.excludePrimes S hS).modulus then idealCoeff η I else 0 :=
  idealCoeff_refineModulus η _ _ _ I

end SevenEighths.HeckeFamily

end

end OAI
end OAIOriginalModule1301

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.Origin
Source SHA256: 6ff6b0c08619fc86f0ebb63c3ba9d6bdb2e14cff8a4328a85fb9e00e73af9f2f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1302



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeOrigin
open HeckeFamily HeckeTheta

def poleRemoved (χ : Character) (s : ℂ) : ℂ :=
  (Real.pi : ℂ)^s * (Complex.Gamma (s+1))⁻¹ *
    HeckeMellinIdentity.regularized (pair (coefficients χ)) s / 6

theorem poleRemoved_entire (χ : Character) : Differentiable ℂ (poleRemoved χ) := by
  have hGamma : Differentiable ℂ (fun s : ℂ => (Complex.Gamma (s+1))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const 1)
  exact (((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul hGamma).mul
      (HeckeMellinIdentity.regularized_entire _)).div_const 6

theorem poleRemoved_eq (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    poleRemoved χ s = (s-1) * LFunction χ s := by
  unfold poleRemoved LFunction continuedLattice latticeL completed
  rw [HeckeMellinIdentity.regularized_eq _ (pair_k _) h0 h1,
    Complex.Gamma_add_one s h0, mul_inv_rev]
  field_simp

theorem poleRemoved_zero (χ : Character) :
    poleRemoved χ 0 = coefficients χ (0,0) / 6 := by
  simp [poleRemoved, HeckeMellinIdentity.regularized, pair_f₀]

theorem poleRemoved_one (χ : Character) :
    poleRemoved χ 1 = HeckeReciprocal.regularizedL χ 1 := by
  rw [HeckeReciprocal.regularizedL_at_one]
  simp [poleRemoved, HeckeMellinIdentity.regularized,
    Complex.Gamma_add_one 1 one_ne_zero,
    show (pair (coefficients χ)).ε = 1 from rfl]

theorem poleRemoved_one_ne_zero (χ : Character) (hχ : χ.residue = 1) :
    poleRemoved χ 1 ≠ 0 := by
  rw [poleRemoved_one]
  exact HeckeReciprocal.regularizedL_ne_zero_at_one χ hχ

def continued (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue = 1 then poleRemoved χ s / (s-1) else LFunction χ s

theorem continued_eq (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    continued χ s = LFunction χ s := by
  unfold continued
  split_ifs
  · rw [poleRemoved_eq χ h0 h1, mul_div_cancel_left₀ _ (sub_ne_zero.mpr h1)]
  · rfl

theorem continued_differentiableAt (χ : Character) {s : ℂ}
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : DifferentiableAt ℂ (continued χ) s := by
  by_cases hχ : χ.residue = 1
  · have heq : continued χ = fun z => poleRemoved χ z / (z-1) := by
      funext z
      simp [continued, hχ]
    rw [heq]
    exact (poleRemoved_entire χ s).div (differentiableAt_id.sub_const 1)
      (sub_ne_zero.mpr (hpole.resolve_right (not_not.mpr hχ)))
  · have heq : continued χ = LFunction χ := by
      funext z
      simp [continued, hχ]
    rw [heq]
    exact ((HeckeCharacterAnalytic.continuedLattice_entire_nonprincipal χ hχ).div_const 6) s

theorem continued_zero (χ : Character) : continued χ 0 = -coefficients χ (0,0) / 6 := by
  by_cases hχ : χ.residue = 1
  · simp [continued, hχ, poleRemoved_zero]
    ring
  · rw [HeckeCharacterAnalytic.coefficients_zero_of_nonprincipal χ hχ]
    simp [continued, hχ, LFunction, continuedLattice, latticeL, Complex.Gamma_zero]

end SevenEighths.HeckeOrigin

end

end OAI
end OAIOriginalModule1302

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.LogDerivative
Source SHA256: fe1c9db01e5dd1db995f6bcc1af25598df6a3e1a33cc44a4683e349a709f663f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1303




namespace OAI

noncomputable section
open scoped Classical Topology
namespace SevenEighths.HeckeLogDerivative
open HeckeFamily

def coeff (χ : Character) : ℕ → ℂ := IdealLogDerivative.coeff (idealCoeff χ)

theorem coeff_LSeries_eq (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LSeries (coeff χ) s = -deriv (LFunction χ) s / LFunction χ s :=
  IdealLogDerivative.coeff_LSeries_eq_neg_logDeriv_of_eq _ (idealCoeff_norm_le_one χ)
    (LFunction χ) (fun _ hz => LFunction_eq_series χ hz) s hs

def poleSubtracted (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue = 1 then
    -deriv (HeckeOrigin.poleRemoved χ) s / HeckeOrigin.poleRemoved χ s
  else -deriv (LFunction χ) s / LFunction χ s

theorem poleRemoved_ne_zero_boundary (χ : Character) (hχ : χ.residue = 1)
    {s : ℂ} (hs : 1 ≤ s.re) : HeckeOrigin.poleRemoved χ s ≠ 0 := by
  by_cases h1 : s = 1
  · subst s
    exact HeckeOrigin.poleRemoved_one_ne_zero χ hχ
  · rw [HeckeOrigin.poleRemoved_eq χ (by intro h; norm_num [h] at hs) h1]
    exact mul_ne_zero (sub_ne_zero.mpr h1) (LFunction_ne_zero_of_one_le_re χ hs (Or.inl h1))

theorem poleSubtracted_analyticAt (χ : Character) {s : ℂ} (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (poleSubtracted χ) s := by
  by_cases hχ : χ.residue = 1
  · have heq : poleSubtracted χ = fun z =>
        -deriv (HeckeOrigin.poleRemoved χ) z / HeckeOrigin.poleRemoved χ z := by
      funext z
      simp [poleSubtracted, hχ]
    rw [heq]
    have ha := (HeckeOrigin.poleRemoved_entire χ).analyticAt s
    exact ha.deriv.neg.div ha (poleRemoved_ne_zero_boundary χ hχ hs)
  · have heq : poleSubtracted χ = fun z => -deriv (LFunction χ) z / LFunction χ z := by
      funext z
      simp [poleSubtracted, hχ]
    rw [heq]
    have ha := (LFunction_entire_nonprincipal χ hχ).analyticAt s
    exact ha.deriv.neg.div ha (LFunction_ne_zero_of_one_le_re χ hs (Or.inr hχ))

theorem poleSubtracted_continuousOn (χ : Character) :
    ContinuousOn (poleSubtracted χ) {s : ℂ | 1 ≤ s.re} :=
  fun _ hs => (poleSubtracted_analyticAt χ hs).continuousAt.continuousWithinAt

theorem poleRemoved_deriv (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    deriv (HeckeOrigin.poleRemoved χ) s = LFunction χ s + (s-1)*deriv (LFunction χ) s := by
  have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
  have heq : HeckeOrigin.poleRemoved χ =ᶠ[nhds s] (fun z => (z-1)*LFunction χ z) := by
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds hs] with z hz
    exact HeckeOrigin.poleRemoved_eq χ
      (by intro h; norm_num [h] at hz) (by intro h; norm_num [h] at hz)
  rw [heq.deriv_eq]
  have hd := (LFunction_differentiableAt χ h0 (Or.inl h1)).hasDerivAt
  have hh := ((hasDerivAt_id s).sub_const 1 |>.mul hd).deriv
  have hfun : ((fun x : ℂ => id x - 1) * LFunction χ) =
      (fun z => (z-1)*LFunction χ z) := rfl
  rw [hfun] at hh
  simpa only [one_mul, id_eq] using hh

theorem coeff_LSeries_eq_poleSubtracted (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LSeries (coeff χ) s = (if χ.residue = 1 then (1 : ℂ)/(s-1) else 0) +
      poleSubtracted χ s := by
  rw [coeff_LSeries_eq χ hs]
  by_cases hχ : χ.residue = 1
  · simp only [hχ, ite_true, poleSubtracted]
    have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
    have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
    rw [poleRemoved_deriv χ hs, HeckeOrigin.poleRemoved_eq χ h0 h1]
    have hn := LFunction_ne_zero_of_one_lt_re χ hs
    field_simp
    ; ring
  · simp [poleSubtracted, hχ]

end SevenEighths.HeckeLogDerivative

end

end OAI
end OAIOriginalModule1303

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.PrimitiveSupremum
Source SHA256: d049c74d13211d7bb59aabaaa8f84275c861b68b08305dab8306dbc2c97e2b26
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1304


namespace OAI

noncomputable section
namespace SevenEighths.HeckePrimitiveSupremum
open HeckeFamily HeckeZeroSupremum

def primitiveZeroRealParts : Set ℝ :=
  {x | ∃ (χ : Character) (s : ℂ), FiniteFourier.IsPrimitiveOnIdeals χ.residue ∧
    (1 / 2 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ (s ≠ 1 ∨ χ.residue ≠ 1) ∧
    LFunction χ s = 0 ∧ s.re = x}

def primitiveSetWithSentinel : Set ℝ := insert (1 / 2) primitiveZeroRealParts

theorem primitiveSet_subset : primitiveSetWithSentinel ⊆ zeroSetWithSentinel := by
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact Set.mem_insert _ _
  · obtain ⟨χ, s, _, hhalf, _, hpole, hz, rfl⟩ := hx
    exact Set.mem_insert_of_mem _ ⟨χ, s, by linarith, hpole, hz, rfl⟩

theorem primitiveSet_bddAbove : BddAbove primitiveSetWithSentinel :=
  zeroSet_bddAbove.mono primitiveSet_subset

theorem primitiveSet_nonempty : primitiveSetWithSentinel.Nonempty :=
  Set.insert_nonempty _ _

theorem beta_eq_primitive_supremum : beta = sSup primitiveSetWithSentinel := by
  apply le_antisymm
  · apply csSup_le zeroSet_nonempty
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact le_csSup primitiveSet_bddAbove (Set.mem_insert _ _)
    · by_cases hhalf : (1 / 2 : ℝ) ≤ x
      · obtain ⟨χ, s, hpos, hpole, hz, rfl⟩ := hx
        obtain ⟨ψ, hp, hpoleψ, hzψ⟩ :=
          HeckeFiniteDeletion.exists_primitive_zero χ hpos hpole hz
        apply le_csSup primitiveSet_bddAbove
        exact Set.mem_insert_of_mem _ ⟨ψ, s, hp, hhalf,
          zeroRealParts_le_one ⟨χ, s, hpos, hpole, hz, rfl⟩, hpoleψ, hzψ, rfl⟩
      · exact (le_of_not_ge hhalf).trans
          (le_csSup primitiveSet_bddAbove (Set.mem_insert _ _))
  · exact csSup_le_csSup zeroSet_bddAbove primitiveSet_nonempty primitiveSet_subset

theorem exists_primitive_zero_near_beta {ε : ℝ} (hε : 0 < ε)
    (hsmall : (1 / 2 : ℝ) ≤ beta - ε) :
    ∃ (χ : Character) (s : ℂ), FiniteFourier.IsPrimitiveOnIdeals χ.residue ∧
      (1 / 2 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ (s ≠ 1 ∨ χ.residue ≠ 1) ∧
      LFunction χ s = 0 ∧ beta - ε < s.re := by
  rw [beta_eq_primitive_supremum] at hsmall ⊢
  obtain ⟨x, hx, hlt⟩ := Supremum.exists_gt_supremum_sub_of_insert
    primitiveSet_bddAbove hε hsmall
  obtain ⟨χ, s, hp, hhalf, hone, hpole, hz, rfl⟩ := hx
  exact ⟨χ, s, hp, hhalf, hone, hpole, hz, hlt⟩

end SevenEighths.HeckePrimitiveSupremum

end

end OAI
end OAIOriginalModule1304

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.RayFamily
Source SHA256: 86c80381f402618d744802694f1f09a9ab6a197d8730bcdd50d99a646c871c7e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1305



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeRayFamily
open HeckeFamily

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

def character (χ : RayOrthogonality.rayCharacters M) : Character :=
  Character.ofResidue M (NeZero.ne M) χ.val ((RayOrthogonality.mem_rayCharacters_iff M χ.val).mp χ.property)

theorem idealCoeff_character (χ : RayOrthogonality.rayCharacters M) (I : Ideal O) :
    idealCoeff (character M χ) I = RayOrthogonality.idealCharacter M χ I := rfl

theorem principal_iff (χ : RayOrthogonality.rayCharacters M) :
    (character M χ).residue = 1 ↔ χ = 1 := by
  change χ.val = 1 ↔ χ = 1
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem character_entire (χ : RayOrthogonality.rayCharacters M) (hχ : χ ≠ 1) :
    Differentiable ℂ (LFunction (character M χ)) :=
  LFunction_entire_nonprincipal _ (fun h => hχ ((principal_iff M χ).mp h))

theorem character_boundary_ne_zero (χ : RayOrthogonality.rayCharacters M)
    {s : ℂ} (hs : 1 ≤ s.re) (hpole : s ≠ 1 ∨ χ ≠ 1) :
    LFunction (character M χ) s ≠ 0 := by
  apply LFunction_ne_zero_of_one_le_re _ hs
  exact hpole.imp id (fun h hn => h ((principal_iff M χ).mp hn))

theorem principal_pole_ne_zero : HeckeOrigin.poleRemoved (character M 1) 1 ≠ 0 :=
  HeckeOrigin.poleRemoved_one_ne_zero _ rfl

theorem average_idealCoeff (I : Ideal O) :
    (RayOrthogonality.rayCard M : ℂ)⁻¹ *
      ∑ χ : RayOrthogonality.rayCharacters M, idealCoeff (character M χ) I =
      if I ∈ RayOrthogonality.principalIdeals M then 1 else 0 := by
  simp only [idealCoeff_character]
  simpa only [div_eq_mul_inv, mul_comm] using RayOrthogonality.average_idealCharacters M I

theorem mangoldt_LSeries (χ : RayOrthogonality.rayCharacters M)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (IdealLogDerivative.coeff (RayOrthogonality.idealCharacter M χ)) s =
      (if χ = 1 then (1 : ℂ)/(s-1) else 0) +
        HeckeLogDerivative.poleSubtracted (character M χ) s := by
  have h := HeckeLogDerivative.coeff_LSeries_eq_poleSubtracted (character M χ) hs
  change LSeries (IdealLogDerivative.coeff (idealCoeff (character M χ))) s = _ at h
  have heq : idealCoeff (character M χ) = RayOrthogonality.idealCharacter M χ := rfl
  rw [heq, principal_iff] at h
  by_cases hc : χ = 1 <;> simpa [hc] using h

theorem poleSubtracted_analyticAt (χ : RayOrthogonality.rayCharacters M)
    {s : ℂ} (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (HeckeLogDerivative.poleSubtracted (character M χ)) s :=
  HeckeLogDerivative.poleSubtracted_analyticAt _ hs

end SevenEighths.HeckeRayFamily

end

end OAI
end OAIOriginalModule1305

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.PrincipalResidue
Source SHA256: 35e58be12c947041e0b0116d08023f892d8dca637bca32b69dd891a48ded4d80
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1306


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckePrincipalResidue
open HeckeFamily HeckeCharacterAnalytic HeckeCoordinates

theorem coefficients_sum_positive (χ : Character) (hχ : χ.residue=1) :
    ∃ c : ℝ, 0<c ∧ (∑ a, coefficients χ a)=(c : ℂ) := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Fintype (O ⧸ χ.modulus) := Fintype.ofFinite _
  let e := Equiv.prodCongr (finCastEquiv χ.period) (finCastEquiv χ.period)
  have heq : (∑ a, coefficients χ a) =
      (Nat.card (coordinateQuotientHom χ).ker : ℂ) *
        (Fintype.card (O ⧸ χ.modulus)ˣ : ℂ) := by
    calc
      _ = ∑ a, χ.residue (coordinateQuotientHom χ (e a)) := by
        apply Finset.sum_congr rfl
        intro a _
        exact coefficients_eq_quotient_character χ a
      _ = ∑ a : ZMod χ.period × ZMod χ.period,
          χ.residue (coordinateQuotientHom χ a) :=
        e.bijective.sum_comp (fun a => χ.residue (coordinateQuotientHom χ a))
      _ = _ := by
        rw [sum_comp_additiveHom _ (coordinateQuotientHom_surjective χ), hχ,
          MulChar.sum_one_eq_card_units]
  refine ⟨(Nat.card (coordinateQuotientHom χ).ker : ℝ) * Fintype.card (O ⧸ χ.modulus)ˣ, ?_, ?_⟩
  · exact mul_pos (Nat.cast_pos.mpr (Nat.card_pos (α := (coordinateQuotientHom χ).ker)))
      (Nat.cast_pos.mpr (Fintype.card_pos (α := (O ⧸ χ.modulus)ˣ)))
  · simpa only [Complex.ofReal_mul, Complex.ofReal_natCast] using heq

theorem principal_residue_positive (χ : Character) (hχ : χ.residue=1) :
    ∃ R : ℝ, 0<R ∧ HeckeOrigin.poleRemoved χ 1=(R : ℂ) := by
  obtain ⟨c,hc,he⟩ := coefficients_sum_positive χ hχ
  have hN : (0 : ℝ)<χ.period := Nat.cast_pos.mpr (NeZero.pos χ.period)
  let d : ℝ := (((χ.period : ℝ)^2)^(-(1/2 : ℝ))) *
    ((3*(χ.period : ℝ)^2)^(-(1/2 : ℝ)))
  have hd : 0<d := mul_pos (Real.rpow_pos_of_pos (sq_pos_of_pos hN) _)
    (Real.rpow_pos_of_pos (mul_pos (by norm_num) (sq_pos_of_pos hN)) _)
  refine ⟨Real.pi*(2*d*c)/6, by positivity, ?_⟩
  rw [HeckeOrigin.poleRemoved_one, HeckeReciprocal.regularizedL_at_one,
    HeckeTheta.pair_g₀, he]
  simp only [HeckeTheta.dualScalar, d, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_ofNat]

theorem fixed_principal_residue_positive (M : Ideal O) [NeZero M] :
    ∃ R : ℝ, 0<R ∧ HeckeOrigin.poleRemoved (HeckeRayFamily.character M 1) 1=(R : ℂ) :=
  principal_residue_positive _ rfl

end SevenEighths.HeckePrincipalResidue

end

end OAI
end OAIOriginalModule1306

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.RayPrimes
Source SHA256: 9b402e301e534f86854a4c403fd4f9a51c1ae55bb074222a78364987900e93d6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1307




namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.HeckeRayPrimes
open HeckeFamily
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

theorem analytic_family : PNT.RayAsymptotic.AnalyticFamily M
    (fun χ => LFunction (HeckeRayFamily.character M χ))
    (HeckeOrigin.poleRemoved (HeckeRayFamily.character M 1) 1) := by
  refine ⟨?_, ?_, ?_, ?_, HeckeRayFamily.principal_pole_ne_zero M⟩
  · intro χ s hs
    exact LFunction_eq_series _ hs
  · intro χ s hs hpole
    rcases hpole with hχ | hs1
    · exact (HeckeRayFamily.character_entire M χ hχ).analyticAt s
    · apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
      have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
      filter_upwards [isOpen_ne.mem_nhds hs0, isOpen_ne.mem_nhds hs1] with z hz0 hz1
      exact LFunction_differentiableAt _ hz0 (Or.inl hz1)
  · intro χ s hs hpole
    exact HeckeRayFamily.character_boundary_ne_zero M χ hs hpole.symm
  · apply PNT.RayAsymptotic.principalRegularization_analyticAt_of_local
      _ (HeckeOrigin.poleRemoved (HeckeRayFamily.character M 1))
      ((HeckeOrigin.poleRemoved_entire _).analyticAt 1)
    filter_upwards [isOpen_ne.mem_nhds (by norm_num : (1 : ℂ) ≠ 0)] with s hs0
    intro hs1
    exact (HeckeOrigin.poleRemoved_eq _ hs0 hs1).symm

theorem classCoeff_ratio_tendsto :
    Tendsto (fun N : ℕ => cumsum (PNT.RayAsymptotic.classCoeff M) N / N)
      atTop (𝓝 ((RayOrthogonality.rayCard M : ℝ)⁻¹)) :=
  PNT.RayAsymptotic.classCoeff_ratio_tendsto M (analytic_family M)

theorem quotientClassCoeff_ratio_tendsto
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H) :
    Tendsto (fun N : ℕ => cumsum (PNT.RayAsymptotic.quotientClassCoeff M H) N / N)
      atTop (𝓝 ((RayQuotient.classNumber M H : ℝ)⁻¹)) :=
  PNT.RayAsymptotic.quotientClassCoeff_ratio_tendsto M H hH (analytic_family M)

theorem primeLogMass_ratio_tendsto :
    Tendsto (fun N : ℕ => PNT.IdealPrimeMass.primeLogMass (RayOrthogonality.principalIdeals M) N / N)
      atTop (𝓝 ((RayOrthogonality.rayCard M : ℝ)⁻¹)) :=
  PNT.IdealPrimeMass.primeLogMass_ratio_tendsto _ (classCoeff_ratio_tendsto M)

theorem quotientPrimeLogMass_ratio_tendsto
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H) :
    Tendsto (fun N : ℕ => PNT.IdealPrimeMass.primeLogMass (RayQuotient.identityClass M H) N / N)
      atTop (𝓝 ((RayQuotient.classNumber M H : ℝ)⁻¹)) :=
  PNT.IdealPrimeMass.primeLogMass_ratio_tendsto _ (quotientClassCoeff_ratio_tendsto M H hH)

end SevenEighths.HeckeRayPrimes

end

end OAI
end OAIOriginalModule1307

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.RayQuotient
Source SHA256: 7eed3879d118ca87d25dfeb78babe3b7fc2b4204cb1cc32404aaf0203b23a3a6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1308



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeRayQuotient
open HeckeFamily
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

def character (χ : RayQuotient.Characters M H) : Character :=
  HeckeRayFamily.character M (RayQuotient.toFullRay M H hH χ)

theorem idealCoeff_character (χ : RayQuotient.Characters M H) (I : Ideal O) :
    idealCoeff (character M H hH χ) I = RayQuotient.idealCharacter M H hH χ I := rfl

theorem principal_iff (χ : RayQuotient.Characters M H) :
    (character M H hH χ).residue = 1 ↔ χ = 1 := by
  rw [character, HeckeRayFamily.principal_iff, RayQuotient.toFullRay_eq_one]

theorem character_entire (χ : RayQuotient.Characters M H) (hχ : χ ≠ 1) :
    Differentiable ℂ (LFunction (character M H hH χ)) :=
  LFunction_entire_nonprincipal _ (fun h => hχ ((principal_iff M H hH χ).mp h))

theorem character_boundary_ne_zero (χ : RayQuotient.Characters M H)
    {s : ℂ} (hs : 1 ≤ s.re) (hpole : s ≠ 1 ∨ χ ≠ 1) :
    LFunction (character M H hH χ) s ≠ 0 := by
  apply LFunction_ne_zero_of_one_le_re _ hs
  exact hpole.imp id (fun h hn => h ((principal_iff M H hH χ).mp hn))

theorem principal_pole_ne_zero : HeckeOrigin.poleRemoved (character M H hH 1) 1 ≠ 0 :=
  HeckeOrigin.poleRemoved_one_ne_zero _ ((principal_iff M H hH 1).mpr rfl)

theorem average_idealCoeff (I : Ideal O) :
    (RayQuotient.classNumber M H : ℂ)⁻¹ *
      ∑ χ : RayQuotient.Characters M H, idealCoeff (character M H hH χ) I =
      if I ∈ RayQuotient.identityClass M H then 1 else 0 := by
  simp only [idealCoeff_character]
  simpa only [div_eq_mul_inv, mul_comm] using RayQuotient.average_idealCharacters M H hH I

theorem mangoldt_LSeries (χ : RayQuotient.Characters M H)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (IdealLogDerivative.coeff (RayQuotient.idealCharacter M H hH χ)) s =
      (if χ = 1 then (1 : ℂ)/(s-1) else 0) +
        HeckeLogDerivative.poleSubtracted (character M H hH χ) s := by
  have h := HeckeLogDerivative.coeff_LSeries_eq_poleSubtracted (character M H hH χ) hs
  change LSeries (IdealLogDerivative.coeff (idealCoeff (character M H hH χ))) s = _ at h
  have heq : idealCoeff (character M H hH χ) = RayQuotient.idealCharacter M H hH χ := rfl
  rw [heq, principal_iff] at h
  by_cases hc : χ = 1 <;> simpa [hc] using h

theorem poleSubtracted_analyticAt (χ : RayQuotient.Characters M H)
    {s : ℂ} (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (HeckeLogDerivative.poleSubtracted (character M H hH χ)) s :=
  HeckeLogDerivative.poleSubtracted_analyticAt _ hs

end SevenEighths.HeckeRayQuotient

end

end OAI
end OAIOriginalModule1308

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.ReciprocalBound
Source SHA256: b68d5ef937121a5834d1656a79cf6ca586ba643ca8d997127c3c820a19166fa4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1309


namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeReciprocalBound
open HeckeFamily

def bound (σ : ℝ) : ℝ :=
  ∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight (σ : ℂ) I‖

theorem normWeight_le_of_re_ge {σ : ℝ} {s : ℂ} (hs : σ ≤ s.re) (I : Ideal O) :
    ‖CubicEisenstein.fullIdealWeight s I‖ ≤
      ‖CubicEisenstein.fullIdealWeight (σ : ℂ) I‖ := by
  by_cases hI : I = 0
  · simp [hI, CubicEisenstein.fullIdealWeight]
  · have hN : (1 : ℝ) ≤ Ideal.absNorm I := by
      have hpos : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff I).mpr (Ring.HasFiniteQuotients.finiteQuotient hI))
      exact_mod_cast hpos
    simp only [CubicEisenstein.fullIdealWeight, hI, ite_false]
    have hn : (0 : ℝ) < Ideal.absNorm I := lt_of_lt_of_le zero_lt_one hN
    rw [show (Ideal.absNorm I : ℂ) = ((Ideal.absNorm I : ℝ) : ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hn,
      Complex.norm_cpow_eq_rpow_re_of_pos hn]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hs)

theorem reciprocal_norm_le (χ : Character) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) : ‖HeckeReciprocal.reciprocal χ s‖ ≤ bound σ := by
  have hs1 : 1 < s.re := hσ.trans_le hs
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs1
  have hsp : s ≠ 1 := by intro h; norm_num [h] at hs1
  rw [HeckeReciprocal.reciprocal_eq_inv χ hs0 hsp, LFunction_eq_series χ hs1,
    ← IdealEuler.inverseSeries_eq_inv _ (idealCoeff_norm_le_one χ) s hs1]
  have hsum := IdealEuler.inverse_summable_norm (idealCoeff χ)
    (idealCoeff_norm_le_one χ) s hs1
  apply (norm_tsum_le_tsum_norm hsum).trans
  apply Summable.tsum_le_tsum _ hsum
    (CubicEisenstein.fullIdealWeight_summable_norm (σ : ℂ) (by simpa using hσ))
  intro I
  change ‖(UniqueFactorizationMonoid.moebius I : ℂ) *
    (idealCoeff χ I * CubicEisenstein.fullIdealWeight s I)‖ ≤ _
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ‖CubicEisenstein.fullIdealWeight s I‖ := by
      apply (mul_le_of_le_one_left (by positivity)
        (CubicEisenstein.norm_ideal_moebius_le_one I)).trans
      exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one χ I)
    _ ≤ _ := normWeight_le_of_re_ge hs I

end SevenEighths.HeckeReciprocalBound

end

end OAI
end OAIOriginalModule1309

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.Dyadic
Source SHA256: 532a488b08c81b0f60a9f765693a9cf26d800cd08caba9c261a79fb65921dcd3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1310


namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set
namespace SevenEighths.HeckeDyadic
open HeckeFamily

abbrev NonzeroIdeal := UnrestrictedIdealReindex.NonzeroIdeal

private instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
private instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

def norm (I : NonzeroIdeal) : ℝ := I.val.absNorm

theorem norm_pos (I : NonzeroIdeal) : 0 < norm I := by
  unfold norm
  exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)

def coefficient (χ : Character) (inverse : Bool) (I : Ideal O) : ℂ :=
  if inverse then (UniqueFactorizationMonoid.moebius I : ℂ)*idealCoeff χ I else idealCoeff χ I

theorem coefficient_norm_le (χ : Character) (inverse : Bool) (I : Ideal O) :
    ‖coefficient χ inverse I‖ ≤ 1 := by
  cases inverse
  · exact idealCoeff_norm_le_one χ I
  · change ‖(UniqueFactorizationMonoid.moebius I : ℂ)*idealCoeff χ I‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (CubicEisenstein.norm_ideal_moebius_le_one I)).trans
      (idealCoeff_norm_le_one χ I)

@[simp] theorem coefficient_zero (χ : Character) (inverse : Bool) : coefficient χ inverse 0 = 0 := by
  cases inverse
  · exact idealCoeff_zero χ
  · change (UniqueFactorizationMonoid.moebius (0 : Ideal O) : ℂ)*idealCoeff χ 0 = 0
    rw [idealCoeff_zero, mul_zero]

def shift (σ ω : ℝ) : ℂ := (σ : ℂ)-(ω : ℂ)*Complex.I

@[simp] theorem shift_re (σ ω : ℝ) : (shift σ ω).re = σ := by simp [shift]

def summand (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ ω : ℝ) (I : NonzeroIdeal) : ℂ :=
  coefficient χ inverse I.val * W (norm I/D) * ((norm I/D : ℝ) : ℂ)^(-shift σ ω)

def polynomial (χ : Character) (inverse : Bool) (W : ℝ → ℂ) (D σ ω : ℝ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ)) * ∑' I : NonzeroIdeal, summand χ inverse W D σ ω I

theorem summand_finite_support (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (a b D σ ω : ℝ) (hD : 0 < D) (hW : Function.support W ⊆ Icc a b) :
    (Function.support (summand χ inverse W D σ ω)).Finite := by
  have hfin := Ideal.finite_setOfPred_absNorm_le (S := O) ⌈D*b⌉₊
  apply (Set.Finite.preimage (f := fun I : NonzeroIdeal => I.val) Subtype.val_injective.injOn hfin).subset
  intro I hI
  have hw : W (norm I/D) ≠ 0 := by
    intro h
    exact hI (by simp [summand, h])
  have hupper := (hW hw).2
  have hq : norm I ≤ D*b := by
    have h := (div_le_iff₀ hD).mp hupper
    linarith
  have hr : norm I ≤ (⌈D*b⌉₊ : ℝ) := hq.trans (Nat.le_ceil _)
  change I.val.absNorm ≤ ⌈D*b⌉₊
  dsimp [norm] at hr
  exact_mod_cast hr

def series (χ : Character) (inverse : Bool) (s : ℂ) : ℂ :=
  if inverse then HeckeReciprocal.reciprocal χ s else LFunction χ s

theorem series_eq_tsum (χ : Character) (inverse : Bool) {s : ℂ} (hs : 1 < s.re) :
    series χ inverse s =
      ∑' I : NonzeroIdeal, coefficient χ inverse I.val * (norm I : ℂ)^(-s) := by
  have he : (∑' I : NonzeroIdeal, coefficient χ inverse I.val *
      CubicEisenstein.fullIdealWeight s I.val) =
      ∑' I : Ideal O, coefficient χ inverse I * CubicEisenstein.fullIdealWeight s I := by
    apply tsum_subtype_eq_of_support_subset
      (s := {I : Ideal O | I ≠ 0})
      (f := fun I : Ideal O => coefficient χ inverse I * CubicEisenstein.fullIdealWeight s I)
    intro I hI hi
    subst I
    exact hI (by
      change coefficient χ inverse 0 * CubicEisenstein.fullIdealWeight s 0 = 0
      rw [coefficient_zero, zero_mul])
  have hc : (∑' I : NonzeroIdeal, coefficient χ inverse I.val * (norm I : ℂ)^(-s)) =
      ∑' I : Ideal O, coefficient χ inverse I * CubicEisenstein.fullIdealWeight s I := by
    rw [← he]
    apply tsum_congr
    intro I
    have hI : I.val ≠ 0 := I.property
    rw [CubicEisenstein.fullIdealWeight, ite_eq_right hI]
    simp only [norm, Complex.ofReal_natCast]
  rw [hc]
  cases inverse
  · exact LFunction_eq_series χ hs
  · have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
    have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
    change HeckeReciprocal.reciprocal χ s = _
    rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1, LFunction_eq_series χ hs,
      ← IdealEuler.inverseSeries_eq_inv _ (idealCoeff_norm_le_one χ) s hs]
    apply tsum_congr
    intro I
    simp only [coefficient,  ite_true, IdealEuler.weighted,
      IdealEuler.normWeight, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
    ring

end SevenEighths.HeckeDyadic

end

end OAI
end OAIOriginalModule1310

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorRowSpecialization
Source SHA256: cc461149e20ee542203ce8324c9255ee2b82d1cf06996d8176e94a324e096b3a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1311



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRowSpecialization
open HeckeFamily HeckeDyadic HeckeRowClosure

theorem inverse_polynomial_original_row (η χ : Character) (m f z : O)
    (heq : ∀ n : O, elementCoeff χ n =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n)
    (W : ℝ→ℂ) (D σ freq : ℝ) :
    polynomial χ true W D σ freq =
      (D : ℂ)^(-(1/2 : ℂ))*∑' J : NonzeroIdeal,
        (UniqueFactorizationMonoid.moebius J.val : ℂ)*idealCoeff η J.val*
          CanonicalRowCompletion.idealRowHom (m^6*f^4*z) J.val*
          W (norm J/D)*((norm J/D : ℝ) : ℂ)^(-shift σ freq) := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  unfold summand coefficient
  simp only [ite_true,idealCoeff_eq_row η χ m f z heq]
  ring

theorem plain_polynomial_original_row (η χ : Character) (m f z : O)
    (heq : ∀ n : O, elementCoeff χ n =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n)
    (W : ℝ→ℂ) (D σ freq : ℝ) :
    polynomial χ false W D σ freq =
      (D : ℂ)^(-(1/2 : ℂ))*∑' J : NonzeroIdeal,
        idealCoeff η J.val*CanonicalRowCompletion.idealRowHom (m^6*f^4*z) J.val*
          W (norm J/D)*((norm J/D : ℝ) : ℂ)^(-shift σ freq) := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  unfold summand coefficient
  simp only [Bool.false_eq_true,ite_false,idealCoeff_eq_row η χ m f z heq]

end SevenEighths.HeckeDetectorRowSpecialization

end

end OAI
end OAIOriginalModule1311

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationRows
Source SHA256: 5aba9352dc9c92b7fb7052957d9215cb2272087e3b791de6b3cb70c52fded135
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1312


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily UniqueFactorizationMonoid

def SixthFree (I : Ideal O) : Prop := ∀ P, (normalizedFactors I).count P<6

theorem ideal_decomposition_unique {I J A B : Ideal O}
    (hI : I≠0) (hJ : J≠0) (hA : A≠0) (hB : B≠0)
    (hIf : SixthFree I) (hJf : SixthFree J) (he : I*A^6=J*B^6) :
    I=J ∧ A=B := by
  have hf := congrArg normalizedFactors he
  rw [normalizedFactors_mul hI (pow_ne_zero _ hA),
    normalizedFactors_mul hJ (pow_ne_zero _ hB),normalizedFactors_pow,normalizedFactors_pow] at hf
  have hc (P : Ideal O) := congrArg (Multiset.count P) hf
  have hcounts (P : Ideal O) :
      (normalizedFactors I).count P=(normalizedFactors J).count P ∧
      (normalizedFactors A).count P=(normalizedFactors B).count P := by
    have hh := hc P
    simp only [Multiset.count_add,Multiset.count_nsmul] at hh
    have hi := hIf P
    have hj := hJf P
    omega
  have hIJ : normalizedFactors I=normalizedFactors J :=
    Multiset.ext.mpr (fun P => (hcounts P).1)
  have hAB : normalizedFactors A=normalizedFactors B :=
    Multiset.ext.mpr (fun P => (hcounts P).2)
  constructor
  · simpa only [Ideal.prod_normalizedFactors_eq_self hI,Ideal.prod_normalizedFactors_eq_self hJ]
      using congrArg Multiset.prod hIJ
  · simpa only [Ideal.prod_normalizedFactors_eq_self hA,Ideal.prod_normalizedFactors_eq_self hB]
      using congrArg Multiset.prod hAB

abbrev FreeRow := {u : O // u≠0 ∧ SixthFree (Ideal.span {u})}
abbrev NonzeroIdeal := UnrestrictedIdealReindex.NonzeroIdeal

def rowMap (p : FreeRow×NonzeroIdeal) : O :=
  p.1.val*(ConcretePrimeRowBridge.idealGenerator p.2.val)^6

theorem rowMap_ne_zero (p : FreeRow×NonzeroIdeal) : rowMap p≠0 :=
  mul_ne_zero p.1.property.1 (pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero
    p.2.val p.2.property))

theorem rowMap_span (p : FreeRow×NonzeroIdeal) :
    Ideal.span {rowMap p}=Ideal.span {p.1.val}*p.2.val^6 := by
  unfold rowMap
  rw [←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_pow,
    ConcretePrimeRowBridge.span_idealGenerator]

theorem rowMap_injective : Function.Injective rowMap := by
  intro p q hpq
  have he := congrArg (fun u : O => Ideal.span {u}) hpq
  rw [rowMap_span,rowMap_span] at he
  have hd := ideal_decomposition_unique
    (Ideal.span_singleton_eq_bot.not.mpr p.1.property.1)
    (Ideal.span_singleton_eq_bot.not.mpr q.1.property.1)
    p.2.property q.2.property p.1.property.2 q.1.property.2 he
  have ha : p.2=q.2 := Subtype.ext hd.2
  apply Prod.ext
  · apply Subtype.ext
    change p.1.val*(ConcretePrimeRowBridge.idealGenerator p.2.val)^6=
      q.1.val*(ConcretePrimeRowBridge.idealGenerator q.2.val)^6 at hpq
    rw [ha] at hpq
    exact mul_right_cancel₀ (pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero
      q.2.val q.2.property)) hpq
  · exact ha

theorem rowMap_norm (p : FreeRow×NonzeroIdeal) :
    (Ideal.span {rowMap p}).absNorm=(Ideal.span {p.1.val}).absNorm*p.2.val.absNorm^6 := by
  rw [rowMap_span,map_mul,map_pow]

end SevenEighths.HeckeInverseAmplification

end

end OAI
end OAIOriginalModule1312

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.Signal
Source SHA256: 91f3e1509427c767f43c6a57916aafd5915411bbae982449c73b9f2608ae6b76
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1313



namespace OAI

noncomputable section

open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology FourierTransform
namespace SevenEighths.HeckeSignal
open HeckeFamily Continuation

def quotient (χ : Character) (H : ℂ → ℂ) (s : ℂ) : ℂ :=
  H s * HeckeReciprocal.reciprocal χ s

def amplitude (χ : Character) (H : ℂ → ℂ) (s : ℂ) : ℂ :=
  Complex.exp ((s - 5/6)^2) * quotient χ H s

def signal (χ : Character) (H : ℂ → ℂ) (c : ℝ) (x : ℝ) : ℂ :=
  (x : ℂ)^(c : ℂ) * mellinInv (-2) (fun s => amplitude χ H (-s)) x

theorem quotient_differentiableAt (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re}) {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (quotient χ H) s :=
  (hH.differentiableAt ((Complex.isOpen_re_gt (7/8)).mem_nhds (by linarith : (7/8 : ℝ) < s.re))).mul
    (HeckeReciprocal.reciprocal_differentiableAt χ
      (lt_of_le_of_lt HeckeZeroSupremum.beta_le_one hs))

theorem quotient_bound (χ : Character) (H : ℂ → ℂ)
    (hH : ∀ s : ℂ, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2)
    {s : ℂ} (hs : 2 ≤ s.re) :
    ‖quotient χ H s‖ ≤ (3/2) * HeckeReciprocalBound.bound 2 := by
  have hn : ‖H s‖ ≤ 3/2 := by
    have h := norm_add_le (H s - 1) (1 : ℂ)
    have h' := hH s (by linarith)
    simp only [sub_add_cancel, norm_one] at h
    linarith
  unfold quotient
  rw [norm_mul]
  exact mul_le_mul hn (HeckeReciprocalBound.reciprocal_norm_le χ (by norm_num) hs)
    (norm_nonneg _) (by norm_num)

theorem normalizedSignal_eq (χ : Character) (H : ℂ → ℂ) (c : ℝ)
    {x : ℝ} (hx : 0 < x) :
    normalizedSignal (signal χ H c) c x =
      mellinInv (-2) (fun s => amplitude χ H (-s)) x := by
  unfold normalizedSignal signal
  simp only [smul_eq_mul, ← mul_assoc]
  rw [Complex.cpow_neg, inv_mul_cancel₀]
  · simp
  · exact (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [hx.ne'])

theorem signal_eq_contour (χ : Character) (H : ℂ → ℂ) (c : ℝ)
    {x : ℝ} (hx : 0 < x) :
    signal χ H c x = (1 / (2 * Real.pi) : ℂ) *
      ∫ y : ℝ, gaussianContourIntegrand (quotient χ H) c x ((2 : ℂ) + y * I) := by
  unfold signal mellinInv
  simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_one]
  rw [mul_left_comm, ← integral_const_mul]
  congr 1
  rw [← integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards [] with y
  unfold gaussianContourIntegrand amplitude
  have he : -(((-2 : ℝ) : ℂ) + (-y : ℝ) * I) = (2 : ℂ) + y * I := by push_cast; ring
  rw [he, ← mul_assoc, ← Complex.cpow_add]
  · ring_nf
  · exact Complex.ofReal_ne_zero.mpr hx.ne'

def quotientBound : ℝ := (3/2) * HeckeReciprocalBound.bound 2

theorem quotientBound_nonneg : 0 ≤ quotientBound := by
  unfold quotientBound HeckeReciprocalBound.bound
  positivity

theorem amplitude_continuous_line (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re}) (a : ℝ) (ha : 1 < a) :
    Continuous (fun y : ℝ => amplitude χ H ((a : ℂ) + y * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have hd : DifferentiableAt ℂ (amplitude χ H) ((a : ℂ) + y * I) := by
    unfold amplitude
    exact (((differentiable_id.sub_const (5/6 : ℂ)).pow 2).cexp.differentiableAt).mul
      (quotient_differentiableAt χ H hH (by simpa using ha))
  have hm : Continuous (fun v : ℝ => (a : ℂ) + v * I) := by fun_prop
  exact hd.continuousAt.comp (f := fun v : ℝ => (a : ℂ) + v * I) hm.continuousAt

theorem amplitude_norm_bound (χ : Character) (H : ℂ → ℂ)
    (hH : ∀ s : ℂ, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2)
    (a y : ℝ) (ha : 2 ≤ a) :
    ‖amplitude χ H ((a : ℂ) + y * I)‖ ≤
      (Real.exp ((a-5/6)^2) * quotientBound) * Real.exp (-(y^2)) := by
  have hn := norm_gaussianContourIntegrand (quotient χ H) 0 a y (Z := 1) zero_lt_one
  simp only [gaussianContourIntegrand, Complex.ofReal_one, Complex.ofReal_zero,
    add_zero, Complex.one_cpow, one_mul, Real.one_rpow] at hn
  change ‖amplitude χ H ((a : ℂ) + y * I)‖ = _ at hn
  rw [hn]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (quotient_bound χ H hH (by simpa using ha))
      (Real.exp_pos _).le) (Real.exp_pos _).le

theorem amplitude_integrable_line (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2)
    (a : ℝ) (ha : 2 ≤ a) : Integrable (fun y : ℝ => amplitude χ H ((a : ℂ) + y * I)) :=
  integrable_of_gaussian_bound _ _
    (amplitude_continuous_line χ H hH a (by linarith)).aestronglyMeasurable
    (fun y => amplitude_norm_bound χ H hb a y ha)

theorem contour_shift (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2)
    (c B : ℝ) (hB : 2 ≤ B) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    signal χ H c x = (1 / (2 * Real.pi) : ℂ) *
      ∫ y : ℝ, gaussianContourIntegrand (quotient χ H) c x ((B : ℂ) + y * I) := by
  rw [signal_eq_contour χ H c hx]
  congr 1
  apply vertical_integral_eq_of_gaussian_bound (C :=
    x^(2+c) * Real.exp ((B-5/6)^2) * quotientBound) _ hB
  · apply gaussianContourIntegrand_differentiableOn _ c hx
    intro z hz
    exact (quotient_differentiableAt χ H hH (by linarith [hz.1])).differentiableWithinAt
  · intro a ha y
    rw [norm_gaussianContourIntegrand _ _ _ _ hx]
    have hxpow : x^(a+c) ≤ x^(2+c) :=
      Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith [ha.1])
    have hexp : Real.exp ((a-5/6)^2) ≤ Real.exp ((B-5/6)^2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [ha.1, ha.2]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply mul_le_mul _ (quotient_bound χ H hb (by simpa using ha.1)) (norm_nonneg _)
      (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le)
    exact mul_le_mul hxpow hexp (Real.exp_pos _).le (Real.rpow_nonneg hx.le _)

def endpointConstant (B : ℝ) : ℝ :=
  ‖(1 / (2 * Real.pi) : ℂ)‖ * Real.exp ((B-5/6)^2) * quotientBound *
    ∫ y : ℝ, Real.exp (-(y^2))

theorem endpointConstant_nonneg (B : ℝ) : 0 ≤ endpointConstant B := by
  unfold endpointConstant
  have hq := quotientBound_nonneg
  have hg : 0 ≤ ∫ y : ℝ, Real.exp (-(y^2)) := integral_nonneg (fun _ => (Real.exp_pos _).le)
  positivity

theorem signal_bound_at_zero (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2)
    (c B : ℝ) (hB : 2 ≤ B) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖signal χ H c x‖ ≤ endpointConstant B * x^(B+c) := by
  rw [contour_shift χ H hH hb c B hB hx hx1, norm_mul]
  have hg : Integrable (fun y : ℝ => Real.exp (-(y^2))) := by
    simpa using integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  have hint := norm_integral_le_of_norm_le
    (hg.const_mul (x^(B+c) * Real.exp ((B-5/6)^2) * quotientBound))
    (f := fun y : ℝ => gaussianContourIntegrand (quotient χ H) c x ((B : ℂ) + y * I))
    (ae_of_all _ (fun y => by
      rw [norm_gaussianContourIntegrand _ _ _ _ hx]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left (quotient_bound χ H hb (by simpa using hB))
        (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le)))
  have h := mul_le_mul_of_nonneg_left hint (norm_nonneg (1/(2*Real.pi) : ℂ))
  rw [integral_const_mul] at h
  convert h using 1 ; unfold endpointConstant ; ring

theorem signal_rapidDecayAtZero (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2)
    (c : ℝ) : RapidDecayAtZero (signal χ H c) := by
  intro R
  let B : ℝ := max 2 (R-c)
  apply IsBigO.of_bound (endpointConstant B)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with x hx hx1
  have hpow : x^(B+c) ≤ x^R :=
    Real.rpow_le_rpow_of_exponent_ge hx hx1 (by dsimp [B]; linarith [le_max_right (2 : ℝ) (R-c)])
  have h := (signal_bound_at_zero χ H hH hb c B (le_max_left _ _) hx hx1).trans
    (mul_le_mul_of_nonneg_left hpow (endpointConstant_nonneg B))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx.le R)] using h

theorem amplitude_integrable_reflected (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2) :
    Integrable (fun y : ℝ => amplitude χ H ((2 : ℂ) - 2 * Real.pi * y * I)) := by
  have h := (amplitude_integrable_line χ H hH hb 2 le_rfl).comp_mul_left'
    (neg_ne_zero.mpr (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero))
  convert h using 1
  ext y
  congr 1
  push_cast
  ring

theorem amplitude_continuous_reflected (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re}) :
    Continuous (fun y : ℝ => amplitude χ H ((2 : ℂ) - 2 * Real.pi * y * I)) := by
  have h := (amplitude_continuous_line χ H hH 2 (by norm_num)).comp
    (show Continuous (fun y : ℝ => -(2*Real.pi)*y) by fun_prop)
  convert h using 1
  ext y
  congr 1
  push_cast
  ring

theorem signal_continuousOn (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2) (c : ℝ) :
    ContinuousOn (signal χ H c) (Ioi 0) := by
  let F : ℝ → ℂ := fun y => amplitude χ H (-(((-2 : ℝ) : ℂ) + 2 * Real.pi * y * I))
  have harg (y : ℝ) : -(((-2 : ℝ) : ℂ) + 2 * Real.pi * y * I) =
      (2 : ℂ) - 2 * Real.pi * y * I := by push_cast; ring
  have hF : Integrable F := by
    simpa only [F, harg] using amplitude_integrable_reflected χ H hH hb
  have hfour : Continuous (𝓕 F) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hF
  have hinv : Continuous (𝓕⁻ F) := by
    have heq : 𝓕⁻ F = fun w : ℝ => 𝓕 F (-w) := funext (Real.fourierInv_eq_fourier_neg F)
    rw [heq]
    exact hfour.comp continuous_neg
  have hpow (z : ℂ) : ContinuousOn (fun x : ℝ => (x : ℂ)^z) (Ioi 0) :=
    Complex.continuous_ofReal.continuousOn.cpow_const (fun _ hx => Complex.ofReal_mem_slitPlane.mpr hx)
  have hlog : ContinuousOn (fun x : ℝ => -Real.log x) (Ioi 0) := by
    intro x hx
    exact (Real.continuousAt_log hx.ne').neg.continuousWithinAt
  apply ((hpow (c : ℂ)).mul ((hpow (2 : ℂ)).mul (hinv.comp_continuousOn hlog))).congr
  intro x hx
  unfold signal
  rw [mellinInv_eq_fourierInv _ _ hx]
  simp only [smul_eq_mul, Complex.ofReal_neg, neg_neg, Complex.ofReal_ofNat,
    F, Pi.mul_apply, Function.comp_apply]

theorem signal_locallyIntegrable (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2) (c : ℝ) :
    LocallyIntegrableOn (signal χ H c) (Ioi 0) :=
  (signal_continuousOn χ H hH hb c).locallyIntegrableOn measurableSet_Ioi

theorem signalMellin_eq_amplitude_on_line (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2) (c a : ℝ) (ha : a < 2)
    (htop : signal χ H c =O[atTop] (fun x : ℝ => x^(a+c))) (y : ℝ) :
    signalMellin (signal χ H c) c ((2 : ℂ) - 2 * Real.pi * y * I) =
      amplitude χ H ((2 : ℂ) - 2 * Real.pi * y * I) := by
  apply signalMellin_eq_on_line _ _ c 2
    (signalMellin_convergent _ a c (signal_locallyIntegrable χ H hH hb c) htop
      (signal_rapidDecayAtZero χ H hH hb c) (by simpa using ha))
    (amplitude_integrable_reflected χ H hH hb) (amplitude_continuous_reflected χ H hH)
  intro x hx
  exact normalizedSignal_eq χ H c hx

end SevenEighths.HeckeSignal

end

end OAI
end OAIOriginalModule1313

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.SignalIdentity
Source SHA256: b62af8a2ae114e91f46d872392ccbd130c48b5bde2c8aeef073bcf9b831c8e1b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1314




namespace OAI

noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology Classical
namespace SevenEighths.HeckeSignal
open HeckeFamily Continuation

private theorem line_tendsto_punctured :
    Tendsto (fun y : ℝ => (2 : ℂ) - 2 * Real.pi * y * I) (𝓝[≠] 0) (𝓝[≠] (2 : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Continuous (fun y : ℝ => (2 : ℂ) - 2 * Real.pi * y * I) := by fun_prop
    simpa using (h.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy ⊢
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact hy (by nlinarith [Real.pi_pos])

theorem signalMellin_eq_amplitude (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2)
    (c a : ℝ) (ha : a < 2)
    (htop : signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)))
    {s : ℂ} (hs : max a 1 < s.re) :
    signalMellin (signal χ H c) c s = amplitude χ H s := by
  have hF := signalMellin_analytic (signal χ H c) a c
    (signal_locallyIntegrable χ H hH hb c) htop (signal_rapidDecayAtZero χ H hH hb c)
  have hFa : AnalyticOnNhd ℂ (signalMellin (signal χ H c) c) {z : ℂ | max a 1 < z.re} :=
    hF.mono (fun _ hz => (le_max_left a 1).trans_lt hz)
  have hA : AnalyticOnNhd ℂ (amplitude χ H) {z : ℂ | max a 1 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt _)).2
    intro z hz
    have hq := quotient_differentiableAt χ H hH ((le_max_right a 1).trans_lt hz)
    exact ((((differentiable_id.sub_const (5/6 : ℂ)).pow 2).cexp.differentiableAt).mul hq).differentiableWithinAt
  apply hFa.eqOn_of_preconnected_of_frequently_eq hA (convex_halfSpace_re_gt _).isPreconnected
    (z₀ := (2 : ℂ)) (by simpa using max_lt ha (by norm_num : (1 : ℝ) < 2)) _ hs
  apply line_tendsto_punctured.frequently
  exact Filter.Frequently.of_forall (fun y => signalMellin_eq_amplitude_on_line χ H hH hb c a ha htop y)

theorem poleRemoved_mul_signalMellin (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2)
    (c a : ℝ) (ha : a < 2)
    (htop : signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)))
    {s : ℂ} (hs : max a 1 < s.re) :
    HeckeOrigin.poleRemoved χ s * signalMellin (signal χ H c) c s =
      (s-1) * gaussianMultiplier H s := by
  have hs1 : 1 < s.re := (le_max_right a 1).trans_lt hs
  have h0 : s ≠ 0 := by intro h; norm_num [h] at hs1
  have h1 : s ≠ 1 := by intro h; norm_num [h] at hs1
  rw [HeckeOrigin.poleRemoved_eq χ h0 h1, signalMellin_eq_amplitude χ H hH hb c a ha htop hs]
  unfold amplitude quotient gaussianMultiplier
  rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1]
  have hn := LFunction_ne_zero_of_one_lt_re χ hs1
  field_simp

def targetRegularizer (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue = 1 then s-1 else 1

def regularL (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue = 1 then HeckeOrigin.poleRemoved χ s else LFunction χ s

theorem targetRegularizer_entire (χ : Character) : Differentiable ℂ (targetRegularizer χ) := by
  by_cases h : χ.residue = 1
  · have he : targetRegularizer χ = fun z : ℂ => z-1 := by funext z; simp [targetRegularizer, h]
    rw [he]
    exact differentiable_id.sub_const 1
  · have he : targetRegularizer χ = fun _ : ℂ => (1 : ℂ) := by funext z; simp [targetRegularizer, h]
    rw [he]
    exact differentiable_const 1

theorem regularL_entire (χ : Character) : Differentiable ℂ (regularL χ) := by
  by_cases h : χ.residue = 1
  · have he : regularL χ = HeckeOrigin.poleRemoved χ := by funext z; simp [regularL, h]
    rw [he]
    exact HeckeOrigin.poleRemoved_entire χ
  · have he : regularL χ = LFunction χ := by funext z; simp [regularL, h]
    rw [he]
    exact LFunction_entire_nonprincipal χ h

theorem regularL_eq (χ : Character) {s : ℂ} (h0 : s ≠ 0)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    regularL χ s = targetRegularizer χ s * LFunction χ s := by
  by_cases h : χ.residue = 1
  · simp only [regularL, targetRegularizer, h, ite_true]
    exact HeckeOrigin.poleRemoved_eq χ h0 (hpole.resolve_right (not_not.mpr h))
  · simp [regularL, targetRegularizer, h]

theorem targetRegularizer_ne_zero (χ : Character) {s : ℂ}
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : targetRegularizer χ s ≠ 0 := by
  by_cases h : χ.residue = 1
  · simpa only [targetRegularizer, h, ite_true, sub_ne_zero] using
      hpole.resolve_right (not_not.mpr h)
  · simp [targetRegularizer, h]

theorem nonzero_of_probe_bounds (χ : Character) (H : ℂ → ℂ) (J : ℝ → ℂ)
    (β ω σ c : ℝ) (hβ : β ≤ 1) (hω0 : 0 < ω) (hω : ω < β-7/8) (hσ : 0 < σ)
    (hH : AnalyticOnNhd ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2)
    (hJ : J =O[atTop] (fun x : ℝ => x^(7/8+c+ω)))
    (herror : (fun x => J x - signal χ H c x) =O[atTop]
      (fun x : ℝ => x^(β+c-σ)))
    {ρ : ℂ} (hρ : β - Supremum.continuationMargin β ω σ < ρ.re)
    (hpole : ρ ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ ρ ≠ 0 := by
  let a := β - Supremum.continuationMargin β ω σ
  have ha2 : a < 2 := by
    have hp := Supremum.continuationMargin_pos hω hσ
    dsimp [a]
    linarith
  have htop : signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)) := by
    have h := common_signal_bound_with_margin J (signal χ H c) β ω σ c hJ herror
    convert h using 1; dsimp [a]; ring_nf
  have hHd := hH.differentiableOn
  apply nonzero_of_common_signal β ω σ c hω0 (LFunction χ) (regularL χ)
    (targetRegularizer χ) H J (signal χ H c)
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr (regularL_entire χ)).mono (Set.subset_univ _))
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr (targetRegularizer_entire χ)).mono (Set.subset_univ _))
    hH hb (signal_locallyIntegrable χ H hHd hb c) (signal_rapidDecayAtZero χ H hHd hb c)
    hJ herror _ hρ _ (targetRegularizer_ne_zero χ hpole)
  · intro s hs
    have hs1 : 1 < s.re := (le_max_right a 1).trans_lt hs
    have h0 : s ≠ 0 := by intro h; norm_num [h] at hs1
    have h1 : s ≠ 1 := by intro h; norm_num [h] at hs1
    rw [regularL_eq χ h0 (Or.inl h1), signalMellin_eq_amplitude χ H hHd hb c a ha2 htop hs]
    unfold amplitude quotient gaussianMultiplier
    rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1]
    have hn := LFunction_ne_zero_of_one_lt_re χ hs1
    field_simp
  · apply regularL_eq χ _ hpole
    intro h
    have hbound := Supremum.continuation_boundary_gt (β := β) (σ := σ) hω0
    rw [h] at hρ
    norm_num at hρ
    linarith

end SevenEighths.HeckeSignal

end

end OAI
end OAIOriginalModule1314

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.CommonProbe
Source SHA256: db523b6b84d2464b34837d864e6d2811903e6085c2862eda85e1c8e2c7b839d4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1315




namespace OAI

noncomputable section
open Filter Asymptotics
open scoped Classical
namespace SevenEighths.HeckeCommonProbe
open HeckeFamily HeckeZeroSupremum

def PrimitiveContract (ω σ : ℝ) : Prop :=
  ∀ η : Character, FiniteFourier.IsPrimitiveOnIdeals η.residue →
    ∃ (χ : Character) (H : ℂ → ℂ) (J : ℝ → ℂ),
      (∀ I, idealCoeff χ I = if IsCoprime I χ.modulus then idealCoeff η I else 0) ∧
      AnalyticOnNhd ℂ H {s : ℂ | 7/8 < s.re} ∧
      (∀ s : ℂ, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2) ∧
      J =O[atTop] (fun x : ℝ => x^(3/16+ω)) ∧
      (fun x => J x - HeckeSignal.signal χ H (-11/16) x) =O[atTop]
        (fun x : ℝ => x^(beta-11/16-σ))

def UniformCommonProbe : Prop :=
  7/8 < beta → ∃ ω σ : ℝ,
    0 < ω ∧ ω < beta-7/8 ∧ 0 < σ ∧ PrimitiveContract ω σ

theorem beta_le_seven_eighths (h : UniformCommonProbe) : beta ≤ 7/8 := by
  by_contra hn
  obtain ⟨ω, σ, hω0, hω, hσ, hcontract⟩ := h (lt_of_not_ge hn)
  have hmargin := Supremum.continuationMargin_pos hω hσ
  have hboundary := Supremum.continuation_boundary_gt (β := beta) (σ := σ) hω0
  obtain ⟨η, ρ, hp, hhalf, _, hpole, hz, hnear⟩ :=
    HeckePrimitiveSupremum.exists_primitive_zero_near_beta hmargin (by linarith)
  obtain ⟨χ, H, J, hmask, hH, hb, hJ, herr⟩ := hcontract η hp
  have hχpole : ρ ≠ 1 ∨ χ.residue ≠ 1 := by
    rcases hpole with h1 | hη
    · exact Or.inl h1
    · exact Or.inr (fun hc => hη ((HeckeFiniteDeletion.principal_iff_of_mask χ η hmask).mp hc))
  have hzχ : LFunction χ ρ = 0 := by
    rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonpole χ η hmask (by linarith) hχpole,
      hz, zero_mul]
  apply (HeckeSignal.nonzero_of_probe_bounds χ H J beta ω σ (-11/16)
    beta_le_one hω0 hω hσ hH hb ?_ ?_ hnear hχpole) hzχ
  · convert hJ using 1; ring_nf
  · convert herr using 1; ring_nf

theorem hecke_ne_zero_of_common_probe (h : UniformCommonProbe)
    (χ : Character) (s : ℂ) (hs : (7/8 : ℝ) < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ s ≠ 0 := by
  exact LFunction_ne_zero_of_beta_lt χ ((beta_le_seven_eighths h).trans_lt hs) hpole

theorem dirichlet_of_common_probe (h : UniformCommonProbe) (q : ℕ) (hq : q ≠ 0)
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : (7/8 : ℝ) < s.re)
    (hexc : ¬ (χ = 1 ∧ s = 1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction χ s ≠ 0 := by
  let : NeZero q := ⟨hq⟩
  exact HeckeDirichlet.dirichlet_seven_eighths_of_hecke
    (hecke_ne_zero_of_common_probe h) χ s hs hexc

theorem zeta_of_common_probe (h : UniformCommonProbe) (s : ℂ)
    (hs : (7/8 : ℝ) < s.re) : riemannZeta s ≠ 0 :=
  HeckeDirichlet.zeta_seven_eighths_of_hecke (hecke_ne_zero_of_common_probe h) s hs

end SevenEighths.HeckeCommonProbe

end

end OAI
end OAIOriginalModule1315

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.SignalShift
Source SHA256: 1c13a3ca3d8a7223ca446adfd5a0ca8f698c85b44c8cbfeeb4372260dcdf666b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1316



namespace OAI

noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology
namespace SevenEighths.HeckeSignalShift
open HeckeFamily HeckeSignal Continuation

theorem quotient_holomorphic (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re}) {a : ℝ}
    (ha : (7/8 : ℝ)<a) (hβ : HeckeZeroSupremum.beta < a) :
    DifferentiableOn ℂ (quotient χ H) {s : ℂ | a ≤ s.re ∧ s.re ≤ 2} := by
  intro s hs
  exact ((hH.differentiableAt ((Complex.isOpen_re_gt (7/8)).mem_nhds
    (ha.trans_le hs.1))).mul
    (HeckeReciprocal.reciprocal_differentiableAt χ (hβ.trans_le hs.1))).differentiableWithinAt

theorem quotient_polynomial_bound (χ : Character) (H : ℂ → ℂ)
    (hb : ∀ s : ℂ, 7/8<s.re → ‖H s-1‖ ≤ 1/2)
    {a C : ℝ} (n : ℕ) (ha : (7/8 : ℝ)<a) (_hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^n))
    {s : ℂ} (hs : a ≤ s.re ∧ s.re ≤ 2) :
    ‖quotient χ H s‖ ≤ ((3/2)*C)*(1+|s.im|^n) := by
  have hnorm : ‖H s‖ ≤ 3/2 := by
    have ht := norm_add_le (H s-1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at ht
    linarith [hb s (ha.trans_le hs.1)]
  unfold quotient
  rw [norm_mul]
  calc
    _ ≤ (3/2)*(C*(1+|s.im|^n)) :=
      mul_le_mul hnorm (hR s hs.1 hs.2) (norm_nonneg _) (by norm_num)
    _ = _ := by ring

theorem contour_shift_left (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8<s.re})
    (hb : ∀ s : ℂ, 7/8<s.re → ‖H s-1‖ ≤ 1/2)
    (c a C : ℝ) (n : ℕ) (ha : (7/8 : ℝ)<a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^n))
    {x : ℝ} (hx : 1 ≤ x) :
    signal χ H c x = (1/(2*Real.pi) : ℂ)*
      ∫ y : ℝ, gaussianContourIntegrand (quotient χ H) c x ((a : ℂ)+y*I) := by
  have hx0 : 0 < x := by linarith
  rw [signal_eq_contour χ H c hx0]
  congr 1
  apply Eq.symm
  apply vertical_integral_eq_of_polynomial_gaussian_bound _ n ha2
    (gaussianContourIntegrand_differentiableOn (quotient_holomorphic χ H hH ha hβ) c hx0)
    (C := x^(2+c)*Real.exp ((2-5/6 : ℝ)^2)*((3/2)*C))
  intro b hb' y
  rw [norm_gaussianContourIntegrand _ _ _ _ hx0]
  have hxpow : x^(b+c) ≤ x^(2+c) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith [hb'.2])
  have he : Real.exp ((b-5/6)^2) ≤ Real.exp ((2-5/6 : ℝ)^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hb'.1,hb'.2]
  have hq := quotient_polynomial_bound χ H hb n ha hC hR
    (s := (b : ℂ)+y*I) (by simpa using hb')
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
  calc
    _ ≤ (x^(2+c)*Real.exp ((2-5/6 : ℝ)^2)) *
        (((3/2)*C)*(1+|y|^n))*Real.exp (-(y^2)) := by gcongr
    _ = _ := by unfold polynomialGaussian; ring

def infinityConstant (a C : ℝ) (n : ℕ) : ℝ :=
  ‖(1/(2*Real.pi) : ℂ)‖*Real.exp ((a-5/6)^2)*((3/2)*C)*
    ∫ y : ℝ, polynomialGaussian n y

theorem signal_bound_at_infinity (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8<s.re})
    (hb : ∀ s : ℂ, 7/8<s.re → ‖H s-1‖ ≤ 1/2)
    (c a C : ℝ) (n : ℕ) (ha : (7/8 : ℝ)<a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^n))
    {x : ℝ} (hx : 1 ≤ x) :
    ‖signal χ H c x‖ ≤ infinityConstant a C n*x^(a+c) := by
  have hx0 : 0 < x := by linarith
  rw [contour_shift_left χ H hH hb c a C n ha ha2 hβ hC hR hx, norm_mul]
  have hint := norm_integral_le_of_norm_le
    ((polynomialGaussian_integrable n).const_mul
      (x^(a+c)*Real.exp ((a-5/6)^2)*((3/2)*C)))
    (f := fun y : ℝ => gaussianContourIntegrand (quotient χ H) c x ((a : ℂ)+y*I))
    (ae_of_all _ (fun y => by
      rw [norm_gaussianContourIntegrand _ _ _ _ hx0]
      have hq := quotient_polynomial_bound χ H hb n ha hC hR
        (s := (a : ℂ)+y*I) (by simpa using And.intro (le_refl a) ha2)
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
        Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
      calc
        _ ≤ x^(a+c)*Real.exp ((a-5/6)^2)*(((3/2)*C)*(1+|y|^n))*Real.exp (-(y^2)) := by gcongr
        _ = _ := by unfold polynomialGaussian; ring))
  have h := mul_le_mul_of_nonneg_left hint (norm_nonneg (1/(2*Real.pi) : ℂ))
  rw [integral_const_mul] at h
  convert h using 1 ; unfold infinityConstant ; ring

theorem signal_isBigO_atTop (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8<s.re})
    (hb : ∀ s : ℂ, 7/8<s.re → ‖H s-1‖ ≤ 1/2)
    (c a C : ℝ) (n : ℕ) (ha : (7/8 : ℝ)<a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^n)) :
    signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)) := by
  apply IsBigO.of_bound (infinityConstant a C n)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have h := signal_bound_at_infinity χ H hH hb c a C n ha ha2 hβ hC hR hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (show 0 ≤ x by linarith) (a+c))] using h

end SevenEighths.HeckeSignalShift

end

end OAI
end OAIOriginalModule1316

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.UnitRows
Source SHA256: c60223ea086c923299f92e63cd46d668823b23db61dab989baf7871743d322bf
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1317



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeUnitRows
open HeckeFamily CanonicalUnitEuler CanonicalRowCompletion
open ActualEisensteinCubic CubicRamified ConcreteTraceCRT
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O
local notation "ω" => HeckeFamily.omega
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem seven_coprime_thirty_six : IsCoprime sevenPrime (36 : O) := by
  have hω : ω ^ 2 = -ω - 1 := by
    simpa [HeckeFamily.omega] using IsCyclotomicExtension.Rat.Three.eta_sq
      (IsCyclotomicExtension.zeta_spec 3 ℚ HeckeFamily.K)
  change IsCoprime (1 + 3 * ω) (36 : O)
  refine ⟨31 * (-2 - 3 * ω), -6, ?_⟩
  linear_combination -279 * hω

theorem supported_unit_thirty_six (n : O) (hn : Supported (Ideal.span {n})) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(36 : O)}) n) := by
  have hs := (supported_span_iff n).mp hn
  have hneg2 : IsCoprime (-2 : O) n := negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using hs.2)
  have h2 : IsCoprime n (2 : O) := (hneg2.of_isCoprime_of_dvd_left ⟨-1, by ring⟩).symm
  have h9 := (ShortDraftCRT.nine_coprime_of_not_lambda_dvd n hs.1).symm
  rw [IdealCharacter.isUnit_mk_iff_isCoprime, Ideal.isCoprime_span_singleton_iff]
  convert (h2.pow_right : IsCoprime n ((2 : O)^2)).mul_right h9 using 1 ; norm_num

theorem unitSupplement_unit (u v : Oˣ) : unitSupplement u (v : O) = 1 := by
  have hspan : (Ideal.span {(v : O)} : Ideal O) = 1 := by
    simpa only [Ideal.one_eq_top] using Ideal.span_singleton_eq_top.mpr v.isUnit
  have hs : Supported (1 : Ideal O) := ⟨one_ne_zero, by
    intro P hP
    rw [UniqueFactorizationMonoid.normalizedFactors_one] at hP
    exact False.elim (Multiset.notMem_zero P hP)⟩
  change (if Supported (Ideal.span {(v : O)}) then idealRowHom (u : O) (Ideal.span {(v : O)}) else 0) = 1
  rw [hspan, ite_eq_left hs, map_one]

private theorem unitSupplement_factorsModulo (u : Oˣ) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(36 : O)}) (unitSupplement u) :=
  unitSupplement_periodic u

def character (u : Oˣ) : Character :=
  HeckeRowClosure.rowCharacter (Ideal.span {(36 : O)})
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)) (unitSupplement u)
    (unitSupplement_factorsModulo u) (unitSupplement_unit u)

theorem elementCoeff_character (u : Oˣ) (n : O) :
    elementCoeff (character u) n = unitSupplement u n := by
  rw [character, HeckeRowClosure.elementCoeff_rowCharacter]
  split_ifs with hn
  · rfl
  · change 0 = if Supported (Ideal.span {n}) then _ else 0
    rw [ite_eq_right (fun hs => hn (supported_unit_thirty_six n hs))]

theorem seven_supported : Supported (Ideal.span {sevenPrime}) := by
  rw [supported_span_iff]
  constructor
  · intro h
    have hd : λ₀ ∣ (36 : O) :=
      ((dvd_pow_self λ₀ (by decide : (2 : ℕ) ≠ 0)).trans lambda_sq_dvd_three).trans ⟨12, by norm_num⟩
    exact PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit
      (seven_coprime_thirty_six.isUnit_of_dvd' h hd)
  · intro h
    have hu := seven_coprime_thirty_six.isUnit_of_dvd' h (show (2 : O) ∣ 36 from ⟨18, by norm_num⟩)
    exact negative_two_prime.not_isUnit hu.neg

theorem unitSupplement_seven (u : Oˣ) :
    unitSupplement u sevenPrime = eisEmbedding (u : O) := by
  change (if Supported (Ideal.span {sevenPrime}) then idealRowHom (u : O) (Ideal.span {sevenPrime}) else 0) = _
  rw [ite_eq_left seven_supported,
    idealRowHom_unit_norm u _ seven_supported.1
      (supported_factors_good _ seven_supported)]
  change eisEmbedding ((u : O) ^ ((Ideal.absNorm sevenIdeal - 1) / 6)) = _
  rw [sevenIdeal_norm]
  norm_num

theorem character_nonprincipal (u : Oˣ) (hu : u ≠ 1) :
    (character u).residue ≠ 1 := by
  have hv : elementCoeff (character u) sevenPrime = eisEmbedding (u : O) := by
    rw [elementCoeff_character, unitSupplement_seven]
  have hv0 : elementCoeff (character u) sevenPrime ≠ 0 :=
    hv ▸ (u.isUnit.map eisEmbedding).ne_zero
  intro h
  have hunit := MulChar.apply_ne_zero_iff.mp hv0
  have hv1 : elementCoeff (character u) sevenPrime = 1 := by
    change (character u).residue _ = 1
    rw [h, MulChar.one_apply hunit]
  apply hu
  apply Units.ext
  apply eisEmbedding_injective
  simpa only [Units.val_one, map_one] using hv.symm.trans hv1

theorem masked_character_nonprincipal (u : Oˣ) (hu : u ≠ 1) (χ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff (character u) I else 0) :
    χ.residue ≠ 1 := by
  intro h
  exact character_nonprincipal u hu ((HeckeFiniteDeletion.principal_iff_of_mask χ (character u) hmask).mp h)

end SevenEighths.HeckeUnitRows

end

end OAI
end OAIOriginalModule1317

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FixedRay
Source SHA256: 93bf6619e9b13079c5181df0aaa48e2781dff3f191a301e033bb73857b766cd9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1318




namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFixedRay
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open RayFourExpansion CenteredMomentPrimary HeckeFamily HeckeRowClosure
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem supported_coprime_four (a : O) (ha : Supported (Ideal.span {a})) :
    IsCoprime (4 : O) a := by
  have hn := (supported_span_iff a).mp ha |>.2
  have hneg : IsCoprime (-2 : O) a :=
    CanonicalRowCompletion.negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
      (by simpa only [neg_dvd] using hn)
  have h2 : IsCoprime (2 : O) a := hneg.of_isCoprime_of_dvd_left ⟨-1, by ring⟩
  have h4 : IsCoprime ((2 : O)^2) a := h2.pow_left
  simpa only [show (2 : O)^2 = 4 by norm_num] using h4

theorem supported_coprime_twelve (a : O) (ha : Supported (Ideal.span {a})) :
    IsCoprime (12 : O) a := by
  have h9 := ShortDraftCRT.nine_coprime_of_not_lambda_dvd a ((supported_span_iff a).mp ha).1
  have h36 : IsCoprime (36 : O) a := by
    convert (supported_coprime_four a ha).mul_left h9 using 1 ; norm_num
  exact h36.of_isCoprime_of_dvd_left ⟨3, by norm_num⟩

theorem supported_rayMask (a : O) (ha : Supported (Ideal.span {a})) : rayMask a = 1 := by
  rw [rayMask, ite_eq_left (CenteredMomentCommonSupport.isUnit_residue_of_coprime
    4 a (supported_coprime_four a ha))]

def phaseTable (D E : O) (r s : RayRing) : ℂ :=
  (QuadraticAllOddCRT.quadraticRaySign
    (QuadraticGaussRay.residueQuotientFour r) (ActualEisensteinCoordinates.residue E) : ℂ) *
  (QuadraticAllOddCRT.quadraticRaySign
    (QuadraticGaussRay.residueQuotientFour s) (ActualEisensteinCoordinates.residue D) : ℂ) *
  (QuadraticAllOddCRT.quadraticRaySign
    (QuadraticGaussRay.residueQuotientFour r) (QuadraticGaussRay.residueQuotientFour s) : ℂ)

theorem phaseTable_mk (D E a b : O) :
    phaseTable D E (Ideal.Quotient.mk _ a) (Ideal.Quotient.mk _ b) =
      sexticReciprocityPhase a E * star (sexticReciprocityPhase b D) *
        sexticReciprocityPhase a b := by
  simp only [phaseTable, QuadraticGaussRay.residueQuotientFour_mk,
    sexticReciprocityPhase, star_intCast]

theorem phaseTable_norm (D E : O) (r s : RayRing) : ‖phaseTable D E r s‖ ≤ 1 := by
  unfold phaseTable QuadraticAllOddCRT.quadraticRaySign
  split_ifs <;> norm_num

theorem phaseTable_expansion (D E a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) :
    sexticReciprocityPhase a E * star (sexticReciprocityPhase b D) *
        sexticReciprocityPhase a b =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff (phaseTable D E) χ ξ * rayCharacter χ a * rayCharacter ξ b := by
  have h := pair_phase_expansion (phaseTable D E) a b
  simpa only [supported_rayMask a ha, supported_rayMask b hb, one_mul,
    phaseTable_mk] using h

theorem phaseTable_mass (D E : O) :
    (∑ χ : RayCharacter, ∑ ξ : RayCharacter, ‖pairCoeff (phaseTable D E) χ ξ‖) ≤ 256 := by
  simpa only [mul_one] using pairCoeff_sum_norm_le (phaseTable D E) 1
    (fun u v => phaseTable_norm D E u v)

def primaryRayHom (χ : RayCharacter) : O →* ℂ where
  toFun n := primaryIdealCharacter 4 χ (Ideal.span {n})
  map_one' := by simp [← Ideal.one_eq_top]
  map_mul' x y := by rw [← Ideal.span_singleton_mul_span_singleton, map_mul]

theorem primaryRayHom_primary (χ : RayCharacter) (a : O) (hp : λ₀^2 ∣ a - 1) :
    primaryRayHom χ a = rayCharacter χ a := by
  change χ (Ideal.Quotient.mk _ (CompletedGauss.primaryGenerator (Ideal.span {a}))) = _
  rw [CompletedGauss.primaryGenerator_span a (CubicJacobiGlobal.primary_ne_zero a hp) hp]
  rfl

theorem primaryRayHom_unit_mul (χ : RayCharacter) (u : Oˣ) (a : O) :
    primaryRayHom χ ((u : O) * a) = primaryRayHom χ a := by
  change primaryIdealCharacter 4 χ (Ideal.span {(u : O) * a}) = _
  rw [Ideal.span_singleton_mul_left_unit u.isUnit]
  rfl

theorem primaryRayHom_periodic (χ : RayCharacter) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(12 : O)}) (primaryRayHom χ) := by
  let F : O →* ℂ := χ.toMonoidHom.comp (Ideal.Quotient.mk (Ideal.span {(4 : O)})).toMonoidHom
  refine periodic_of_primary _ ?_ _ F ?_ (primaryRayHom_unit_mul χ) ?_ ?_
  · apply Ideal.span_singleton_le_span_singleton.mpr
    exact ActualEisensteinCubic.lambda_sq_dvd_three.trans ⟨4, by norm_num⟩
  · intro x y hxy
    apply congrArg χ
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    exact (show (4 : O) ∣ 12 from ⟨3, by norm_num⟩).trans (Ideal.mem_span_singleton.mp hxy)
  · intro x hx
    have hz : CompletedGauss.primaryGenerator (Ideal.span {x}) = 0 := by
      by_contra hn
      exact (PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff x).mp hn hx
    change χ (Ideal.Quotient.mk _ (CompletedGauss.primaryGenerator (Ideal.span {x}))) = 0
    let : Nontrivial RayRing := Fintype.one_lt_card_iff_nontrivial.mp (by rw [rayRing_card]; norm_num)
    rw [hz, map_zero, MulChar.map_zero]
  · exact primaryRayHom_primary χ

def primaryRayCharacter (χ : RayCharacter) : Character :=
  rowCharacter (Ideal.span {(12 : O)}) (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))
    (primaryRayHom χ) (primaryRayHom_periodic χ) (by
      intro u
      simpa using primaryRayHom_unit_mul χ u 1)

@[simp] theorem primaryRayCharacter_modulus (χ : RayCharacter) :
    (primaryRayCharacter χ).modulus = Ideal.span {(12 : O)} := rfl

theorem primaryRayCharacter_primary (χ : RayCharacter) (a : O)
    (ha : Supported (Ideal.span {a})) (hp : λ₀^2 ∣ a - 1) :
    elementCoeff (primaryRayCharacter χ) a = rayCharacter χ a := by
  rw [primaryRayCharacter, elementCoeff_rowCharacter,
    ite_eq_left (CenteredMomentCommonSupport.isUnit_residue_of_coprime
      12 a (supported_coprime_twelve a ha)), primaryRayHom_primary χ a hp]

theorem completeSupportExtension_separated (D E h a b : O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) :
    completeSupportExtension D E hD hE h a b =
      actualCorrelation D E hD hE h *
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          pairCoeff (phaseTable D E) χ ξ *
            (rayCharacter χ a * idealRowHom h (Ideal.span {a})) *
            (rayCharacter ξ b * star (idealRowHom (-h) (Ideal.span {b}))) := by
  rw [completeSupportExtension]
  have he := phaseTable_expansion D E a b ha hb
  calc
    _ = actualCorrelation D E hD hE h *
        (sexticReciprocityPhase a E * star (sexticReciprocityPhase b D) *
          sexticReciprocityPhase a b) *
        idealRowHom h (Ideal.span {a}) * star (idealRowHom (-h) (Ideal.span {b})) := by ring
    _ = _ := by
      rw [he]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ _
      apply Finset.sum_congr rfl
      intro ξ _
      ring

end SevenEighths.CenteredMomentFixedRay

end

end OAI
end OAIOriginalModule1318

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ChildRows
Source SHA256: 9c2b490007aba432c41f292ff5e4c0c1227667f6a711b8ba15348226840c08f6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1319



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentChildRows
open CanonicalRowCompletion CanonicalQuadraticSieve HeckeFamily HeckeRowClosure
open CenteredMomentFixedRay RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def childCharacter (η : Character) (χ : RayCharacter) : Character :=
  η.product (primaryRayCharacter χ)

@[simp] theorem childCharacter_modulus (η : Character) (χ : RayCharacter) :
    (childCharacter η χ).modulus = η.modulus ⊓ Ideal.span {(12 : O)} := rfl

theorem childCharacter_primary (η : Character) (χ : RayCharacter) (n : O)
    (hn : Supported (Ideal.span {n})) (hp : λ₀^2 ∣ n - 1) :
    elementCoeff (childCharacter η χ) n = elementCoeff η n * rayCharacter χ n := by
  rw [childCharacter, elementCoeff_product, primaryRayCharacter_primary χ n hn hp]

theorem child_row_primary (η : Character) (χ : RayCharacter) (m A h n : O)
    (hn : Supported (Ideal.span {n})) (hp : λ₀^2 ∣ n - 1) :
    rowTwist (elementHom (childCharacter η χ)) m 1 (A*h) n =
      (elementCoeff η n * rayCharacter χ n) * coprimalityMask m n *
        idealRowHom (A*h) (Ideal.span {n}) := by
  rw [rowTwist_extract_sixth_mask _ m 1 (A*h) n hn]
  change elementCoeff (childCharacter η χ) n * _ * _ = _
  rw [childCharacter_primary η χ n hn hp]
  simp only [one_pow, one_mul]

theorem child_row_extract (η : Character) (χ : RayCharacter) (m A h e n : O) :
    rowTwist (elementHom (childCharacter η χ)) m 1 (A*h) (e*n) =
      rowTwist (elementHom (childCharacter η χ)) m 1 (A*h) e *
        rowTwist (elementHom (childCharacter η χ)) m 1 (A*h) n := map_mul _ _ _

theorem exists_child_row_character (η : Character) (χ : RayCharacter) (m A h : O)
    (hm : m ≠ 0) (hA : A ≠ 0) (hh : h ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    ∃ ρ : Character, ∀ n, elementCoeff ρ n =
      rowTwist (elementHom (childCharacter η χ)) m 1 (A*h) n :=
  exists_row_character (childCharacter η χ) m 1 (A*h) hm one_ne_zero (mul_ne_zero hA hh) hmLam hm2

theorem old_coefficient_nonzero_coprime (η : Character) (e : O)
    (he : elementCoeff η e ≠ 0) : IsCoprime (Ideal.span {e}) η.modulus :=
  (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp he)

theorem old_coefficient_prime_coprime (η : Character) (e : O)
    (he : elementCoeff η e ≠ 0) (P : Ideal O) (hP : P ∣ Ideal.span {e}) :
    IsCoprime η.modulus P :=
  (old_coefficient_nonzero_coprime η e he).symm.of_isCoprime_of_dvd_right hP

theorem childCharacter_coprime (η : Character) (χ : RayCharacter) (Q P : Ideal O)
    (hQ : Q ≤ Ideal.span {(72 : O)}) (hQP : IsCoprime Q P)
    (hηP : IsCoprime η.modulus P) : IsCoprime (childCharacter η χ).modulus P := by
  have h12 : IsCoprime (Ideal.span {(12 : O)}) P :=
    hQP.of_isCoprime_of_dvd_left (Ideal.dvd_iff_le.mpr (hQ.trans
      (Ideal.span_singleton_le_span_singleton.mpr ⟨6, by norm_num⟩)))
  rw [childCharacter_modulus]
  exact (hηP.mul_left h12).of_isCoprime_of_dvd_left
    (Ideal.dvd_iff_le.mpr Ideal.mul_le_inf)

theorem separated_exceptional_count (η : Character) (χ : RayCharacter)
    (Q : Ideal O) (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A e : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (he : elementCoeff η e ≠ 0) (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m A z)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors D,
      λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P ∧ P ∣ Ideal.span {e} ∧
        CenteredExceptionalCount.valuation (Ideal.span {A}) P % 6 = 2)
    (Z C M F : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hDnorm : Z ^ (F / 2) ≤ (Ideal.absNorm D : ℝ))
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ M) :
    (T.card : ℝ) ≤ 768 * (6 : ℝ) ^ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card *
      C ^ (1 / 6 : ℝ) * Z ^ ((M - 2 * F) / 6) := by
  apply CenteredExceptionalProfile.fixed_support_exceptional_count
    (childCharacter η χ) Q hQ0 hQ hQ72 m A hm hA hmLam hm2 T hT hex D hD
      ?_ Z C M F hZ hC hDnorm hN
  intro P hP
  obtain ⟨hg,h2,hQP,hPe,hval⟩ := hgood P hP
  exact ⟨hg,h2,hQP,childCharacter_coprime η χ Q P hQ72 hQP
    (old_coefficient_prime_coprime η e he P hPe),hval⟩

end SevenEighths.CenteredMomentChildRows

end

end OAI
end OAIOriginalModule1319

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ExceptionalPair
Source SHA256: fd3d1272f43eabb4c8e3f5d33d8dc2ec52798948da3eee8d27f75fdb665c93a7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1320



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentExceptionalPair
open HeckeFamily CenteredExceptionalProfile CenteredMomentChildRows CenteredMomentFixedRay
open CanonicalRowCompletion CanonicalQuadraticSieve RayFourExpansion
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem idealCoeff_ne_zero_iff (χ : Character) (I : Ideal O) :
    idealCoeff χ I ≠ 0 ↔ I ≠ ⊥ ∧ IsCoprime I χ.modulus := by
  change (if I = ⊥ then 0 else χ.residue
    (Ideal.Quotient.mk χ.modulus (Submodule.IsPrincipal.generator I))) ≠ 0 ↔ _
  by_cases hI : I = ⊥
  · simp only [hI,ite_true,ne_eq,not_true_eq_false,false_and]
  · rw [ite_eq_right hI]
    have he : χ.residue (Ideal.Quotient.mk χ.modulus (Submodule.IsPrincipal.generator I)) ≠ 0 ↔
        IsUnit (Ideal.Quotient.mk χ.modulus (Submodule.IsPrincipal.generator I)) := MulChar.apply_ne_zero_iff
    rw [IdealCharacter.isUnit_mk_iff_isCoprime,Ideal.span_singleton_generator] at he
    exact he.trans (and_iff_right hI).symm

theorem fixed_primitive_product (χ ψ τ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hψ : Q ≤ ψ.modulus) (hτ : Q ≤ τ.modulus) :
    ∃ ρ : Character, FiniteFourier.IsPrimitiveOnIdeals ρ.residue ∧
      Q ≤ ρ.modulus ∧ InducedBy (χ.product τ) ρ := by
  obtain ⟨ρ,hmod,hprim,hnorm,hmask⟩ := exists_primitive_product_character ψ τ
  refine ⟨ρ,hprim,(le_inf hψ hτ).trans hmod,?_⟩
  intro I
  by_cases hI : I = 0
  · simp only [hI,idealCoeff_zero,ite_self]
  by_cases hc : IsCoprime I (χ.product τ).modulus
  · have hn := (idealCoeff_ne_zero_iff (χ.product τ) I).mpr ⟨hI,hc⟩
    rw [idealCoeff_product] at hn
    have hχ := (idealCoeff_ne_zero_iff χ I).mp (left_ne_zero_of_mul hn) |>.2
    have he : idealCoeff χ I = idealCoeff ψ I := by rw [h I,ite_eq_left hχ]
    have hnψ : idealCoeff (ψ.product τ) I ≠ 0 := by
      rw [idealCoeff_product,← he]
      exact hn
    have hcψ := (idealCoeff_ne_zero_iff (ψ.product τ) I).mp hnψ |>.2
    change IsCoprime I (ψ.modulus ⊓ τ.modulus) at hcψ
    rw [ite_eq_left hc,idealCoeff_product,he,hmask I,ite_eq_left hcψ]
  · have hz : idealCoeff (χ.product τ) I = 0 := by
      by_contra hn
      exact hc ((idealCoeff_ne_zero_iff (χ.product τ) I).mp hn).2
    rw [hz,ite_eq_right hc]

theorem fixedInducingRow_of_product (η₁ η₂ τ : Character) (Q : Ideal O)
    (m A z₁ z₂ : O) (hτ : Q ≤ τ.modulus)
    (he : ∀ n, rowTwist (HeckeRowClosure.elementHom η₂) m 1 (A*z₂) n =
      rowTwist (HeckeRowClosure.elementHom η₁) m 1 (A*z₁) n * elementCoeff τ n)
    (hx : FixedInducingRow η₁ Q m A z₁) : FixedInducingRow η₂ Q m A z₂ := by
  obtain ⟨χ,ψ,hprim,hind,hQ,hrow⟩ := hx
  obtain ⟨ρ,hρ,hQρ,hindρ⟩ := fixed_primitive_product χ ψ τ hind Q hQ hτ
  refine ⟨χ.product τ,ρ,hρ,hindρ,hQρ,?_⟩
  intro n
  rw [elementCoeff_product,hrow n,he n]

def rayRatio (χ ξ : RayCharacter) : Character :=
  (primaryRayCharacter χ).inverse.product (primaryRayCharacter ξ)

theorem childCharacter_ratio (η : Character) (χ ξ : RayCharacter) (n : O) :
    elementCoeff (childCharacter η ξ) n =
      elementCoeff (childCharacter η χ) n * elementCoeff (rayRatio χ ξ) n := by
  simp only [childCharacter,rayRatio,elementCoeff_product,elementCoeff_inverse]
  by_cases hn : IsUnit (Ideal.Quotient.mk (Ideal.span {(12 : O)}) n)
  · have hχ : elementCoeff (primaryRayCharacter χ) n ≠ 0 :=
      MulChar.apply_ne_zero_iff.mpr hn
    field_simp
  · have hz (ψ : RayCharacter) : elementCoeff (primaryRayCharacter ψ) n = 0 :=
      MulChar.map_nonunit _ hn
    rw [hz χ,hz ξ]
    ring

def reflectionRatio (χ ξ : RayCharacter) : Character :=
  (rayRatio χ ξ).product (HeckeUnitRows.character (-1 : Oˣ))

theorem reflectionRatio_modulus (χ ξ : RayCharacter) (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72 : O)}) : Q ≤ (reflectionRatio χ ξ).modulus := by
  change Q ≤ ((Ideal.span {(12 : O)}) ⊓ (Ideal.span {(12 : O)})) ⊓ Ideal.span {(36 : O)}
  refine le_inf (le_inf ?_ ?_) ?_
  · exact hQ.trans (Ideal.span_singleton_le_span_singleton.mpr ⟨6,by norm_num⟩)
  · exact hQ.trans (Ideal.span_singleton_le_span_singleton.mpr ⟨6,by norm_num⟩)
  · exact hQ.trans (Ideal.span_singleton_le_span_singleton.mpr ⟨2,by norm_num⟩)

end SevenEighths.CenteredMomentExceptionalPair

end

end OAI
end OAIOriginalModule1320

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ExceptionalReflection
Source SHA256: 95e9a3ec5af47f18386762c8368eb5cec63baa17ac21db5d7b43598c2aeccd87
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1321


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentExceptionalReflection
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile CenteredMomentChildRows
open CenteredMomentFixedRay CenteredMomentExceptionalPair RayFourExpansion
open CanonicalRowCompletion CanonicalQuadraticSieve CanonicalUnitEuler
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem child_rows_zero_off_support (η : Character) (χ ξ : RayCharacter)
    (m A z n : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hn : ¬Supported (Ideal.span {n})) :
    rowTwist (elementHom (childCharacter η χ)) m 1 (A*z) n = 0 ∧
      rowTwist (elementHom (childCharacter η ξ)) m 1 (A*(-z)) n = 0 := by
  exact ⟨rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn,
    rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn⟩

theorem child_row_reflection (η : Character) (χ ξ : RayCharacter)
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) (n : O) :
    rowTwist (elementHom (childCharacter η ξ)) m 1 (A*(-z)) n =
      rowTwist (elementHom (childCharacter η χ)) m 1 (A*z) n *
        elementCoeff (reflectionRatio χ ξ) n := by
  by_cases hn : Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask _ m 1 (A*(-z)) n hn,
      rowTwist_extract_sixth_mask _ m 1 (A*z) n hn]
    simp only [one_pow, one_mul]
    change elementCoeff (childCharacter η ξ) n * coprimalityMask m n *
        idealRowHom (A*(-z)) (Ideal.span {n}) =
      (elementCoeff (childCharacter η χ) n * coprimalityMask m n *
        idealRowHom (A*z) (Ideal.span {n})) * elementCoeff (reflectionRatio χ ξ) n
    rw [childCharacter_ratio, reflectionRatio, elementCoeff_product,
      HeckeUnitRows.elementCoeff_character]
    have hu : unitSupplement (-1 : Oˣ) n = idealRowHom (-1) (Ideal.span {n}) := by
      change (if Supported (Ideal.span {n}) then
        idealRowHom ((-1 : Oˣ) : O) (Ideal.span {n}) else 0) = _
      rw [ite_eq_left hn]
      rfl
    rw [hu, show A*(-z) = (-1)*(A*z) by ring, idealRowHom_argument_mul]
    ring
  · obtain ⟨hleft, hright⟩ := child_rows_zero_off_support η χ ξ m A z n hmLam hm2 hn
    rw [hleft, hright, zero_mul]

theorem child_row_reflection_hom (η : Character) (χ ξ : RayCharacter)
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    rowTwist (elementHom (childCharacter η ξ)) m 1 (A*(-z)) =
      rowTwist (elementHom (childCharacter η χ)) m 1 (A*z) *
        elementHom (reflectionRatio χ ξ) := by
  ext n
  exact child_row_reflection η χ ξ m A z hmLam hm2 n

theorem fixedInducingRow_reflected (η : Character) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q ≤ Ideal.span {(72 : O)})
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hex : FixedInducingRow (childCharacter η χ) Q m A z) :
    FixedInducingRow (childCharacter η ξ) Q m A (-z) := by
  exact fixedInducingRow_of_product (childCharacter η χ) (childCharacter η ξ)
    (reflectionRatio χ ξ) Q m A z (-z) (reflectionRatio_modulus χ ξ Q hQ)
    (child_row_reflection η χ ξ m A z hmLam hm2) hex

theorem fixedInducingRow_reflection_iff (η : Character) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q ≤ Ideal.span {(72 : O)})
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    FixedInducingRow (childCharacter η χ) Q m A z ↔
      FixedInducingRow (childCharacter η ξ) Q m A (-z) := by
  constructor
  · exact fixedInducingRow_reflected η χ ξ Q hQ m A z hmLam hm2
  · intro hex
    simpa only [neg_neg] using
      fixedInducingRow_reflected η ξ χ Q hQ m A (-z) hmLam hm2 hex

theorem not_fixedInducingRow_reflection_iff (η : Character) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q ≤ Ideal.span {(72 : O)})
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    (¬FixedInducingRow (childCharacter η χ) Q m A z) ↔
      ¬FixedInducingRow (childCharacter η ξ) Q m A (-z) :=
  not_congr (fixedInducingRow_reflection_iff η χ ξ Q hQ m A z hmLam hm2)

end SevenEighths.CenteredMomentExceptionalReflection

end

end OAI
end OAIOriginalModule1321

/-! Original module: OAI.NumberTheory.DirichletL.Moments.Fourier
Source SHA256: a4b303af73929120c44218208fa6260a25f2e2162a2d4712c8715f4f04dc9f75
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1322



namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentFourier
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentSupportedCorrelation

def frequencyReduction (d m : O) (h : d ∣ m) : Residue m →+* Residue d :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr h)

@[simp] theorem frequencyReduction_mk (d m : O) (h : d ∣ m) (x : O) :
    frequencyReduction d m h (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl

theorem quotientTrace_scaled (d a m : O) (hm : m = d * a)
    (hd : d ≠ 0) (ha : a ≠ 0) (hm0 : m ≠ 0)
    (h : Residue m) (x : Residue d) :
    quotientTrace m hm0 (h * scaledResidue d a m hm x) =
      quotientTrace d hd (frequencyReduction d m (hm ▸ dvd_mul_right d a) h * x) := by
  subst m
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective h
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have ht := quotientTrace_conductor_scale d a h hd ha (Ideal.Quotient.mk _ x)
  simp only [scaledResidue_mk, frequencyReduction_mk, ← map_mul]
  simpa only [← map_mul, conductorReduction, Ideal.Quotient.factor_mk, mul_assoc,
    mul_left_comm, mul_comm] using ht

def residueGauss (d : O) (hd : d ≠ 0) (χ : MulChar (Residue d) ℂ)
    (h : Residue d) : ℂ :=
  ∑' x : Residue d, χ x * quotientTrace d hd (h * x)

theorem residueGauss_supported_mk (d : O)
    (hd : CanonicalQuadraticSieve.Supported (Ideal.span {d})) (h : O) :
    residueGauss d (supported_element_ne_zero d hd) (supportedModulusCharacter d hd)
      (Ideal.Quotient.mk _ h) = ProbePhysical.sexticGauss d (supported_element_ne_zero d hd) h := by
  apply tsum_congr
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [supportedModulusCharacter_mk, ProbePhysical.sexticGauss_coefficient_mk]

theorem fourierSum_scaled (d a m : O) (hm : m = d * a)
    (hd : d ≠ 0) (ha : a ≠ 0) (hm0 : m ≠ 0)
    [Fintype (Residue d)] (χ : MulChar (Residue d) ℂ) (h : Residue m) :
    fourierSum (quotientTrace m hm0) (scaledResidue d a m hm) χ h =
      residueGauss d hd χ (frequencyReduction d m (hm ▸ dvd_mul_right d a) h) := by
  simp only [fourierSum, residueGauss, tsum_fintype, quotientTrace_scaled d a m hm hd ha hm0]

theorem actual_gauss_correlation (u v : O) (hu : u ≠ 0) (hv : v ≠ 0)
    [Fintype (Residue u)] [Fintype (Residue v)] [Fintype (Residue (u * v))]
    (χu : MulChar (Residue u) ℂ) (χv : MulChar (Residue v) ℂ) (j : O) :
    (∑ h : Residue (u * v),
      residueGauss u hu χu (frequencyReduction u (u * v) (dvd_mul_right u v) h) *
        star (residueGauss v hv χv (frequencyReduction v (u * v) (dvd_mul_left v u) h)) *
          quotientTrace (u * v) (mul_ne_zero hu hv) (-(h * Ideal.Quotient.mk _ j))) =
      (Fintype.card (Residue (u * v)) : ℂ) * fullModulusCorrelation u v χu χv j := by
  have h := fullModulusCorrelation_fourier u v χu χv j
    (quotientTrace (u * v) (mul_ne_zero hu hv))
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive _ _)
  simp_rw [fourierSum_scaled u v (u * v) rfl hu hv (mul_ne_zero hu hv),
    fourierSum_scaled v u (u * v) (mul_comm u v) hv hu (mul_ne_zero hu hv)] at h
  exact h

def normalizedResidueGauss (d : O) (hd : d ≠ 0) (χ : MulChar (Residue d) ℂ)
    (h : Residue d) : ℂ :=
  residueGauss d hd χ h / (Real.sqrt (Ideal.absNorm (Ideal.span {d}) : ℝ) : ℂ)

theorem normalized_gauss_correlation (u v : O) (hu : u ≠ 0) (hv : v ≠ 0)
    [Fintype (Residue u)] [Fintype (Residue v)] [Fintype (Residue (u * v))]
    (χu : MulChar (Residue u) ℂ) (χv : MulChar (Residue v) ℂ) (j : O) :
    fullModulusCorrelation u v χu χv j =
      ((Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {v}) : ℝ) : ℂ))⁻¹ *
      ∑ h : Residue (u * v),
        normalizedResidueGauss u hu χu (frequencyReduction u (u * v) (dvd_mul_right u v) h) *
          star (normalizedResidueGauss v hv χv
            (frequencyReduction v (u * v) (dvd_mul_left v u) h)) *
          quotientTrace (u * v) (mul_ne_zero hu hv) (-(h * Ideal.Quotient.mk _ j)) := by
  let ru : ℂ := Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ)
  let rv : ℂ := Real.sqrt (Ideal.absNorm (Ideal.span {v}) : ℝ)
  have hqu : (0 : ℝ) < Ideal.absNorm (Ideal.span {u}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hu))
  have hqv : (0 : ℝ) < Ideal.absNorm (Ideal.span {v}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hv))
  have hru : ru ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hqu).ne'
  have hrv : rv ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hqv).ne'
  have hsqu : ru ^ 2 = (Ideal.absNorm (Ideal.span {u}) : ℂ) := by
    dsimp only [ru]
    exact_mod_cast Real.sq_sqrt hqu.le
  have hsqv : rv ^ 2 = (Ideal.absNorm (Ideal.span {v}) : ℂ) := by
    dsimp only [rv]
    exact_mod_cast Real.sq_sqrt hqv.le
  have hcard : (Fintype.card (Residue (u * v)) : ℂ) = (ru * rv) ^ 2 := by
    have hc : Fintype.card (Residue (u * v)) = Ideal.absNorm (Ideal.span {u * v}) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    rw [hc, ← Ideal.span_singleton_mul_span_singleton, map_mul, Nat.cast_mul,
      ← hsqu, ← hsqv, mul_pow]
  have hterm (h : Residue (u * v)) :
      normalizedResidueGauss u hu χu (frequencyReduction u (u * v) (dvd_mul_right u v) h) *
        star (normalizedResidueGauss v hv χv
          (frequencyReduction v (u * v) (dvd_mul_left v u) h)) *
        quotientTrace (u * v) (mul_ne_zero hu hv) (-(h * Ideal.Quotient.mk _ j)) =
      (residueGauss u hu χu (frequencyReduction u (u * v) (dvd_mul_right u v) h) *
        star (residueGauss v hv χv (frequencyReduction v (u * v) (dvd_mul_left v u) h)) *
        quotientTrace (u * v) (mul_ne_zero hu hv) (-(h * Ideal.Quotient.mk _ j))) / (ru * rv) := by
    simp only [normalizedResidueGauss, star_div₀, Complex.star_def, Complex.conj_ofReal]
    dsimp only [ru, rv]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_div, actual_gauss_correlation u v hu hv χu χv j, hcard]
  change _ = (ru * rv)⁻¹ * ((ru * rv) ^ 2 * _ / (ru * rv))
  field_simp

end SevenEighths.CenteredMomentFourier
end

end OAI
end OAIOriginalModule1322

/-! Original module: OAI.NumberTheory.DirichletL.Moments.HeckeVolume
Source SHA256: df9586c81da96e8b8f7c3eed562b2c437ac77e270ef6acb533bc862f494617a8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1323





namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentHeckeVolume
open HeckeFamily CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentPrimary CanonicalQuadraticSieve QuadraticInitialBound
open IdealMobiusDivisorSum UniqueFactorizationMonoid CenteredMomentMask
open PrimaryIdealUnitReindex (GoodIdeal)
open CubicEisenstein (PrimaryLower primaryLowerIdealEquiv)
local notation "O" => ActualEisensteinCubic.O

def primaryCoefficient (ψ : Character) : Ideal O →* ℂ where
  toFun I := if primaryGenerator I=0 then 0 else idealCoeff ψ I
  map_one' := by simp only [primaryGenerator_one,one_ne_zero,ite_false,map_one]
  map_mul' := by
    intro I J
    simp only [primaryGenerator_mul,map_mul]
    by_cases hI : primaryGenerator I=0 <;> by_cases hJ : primaryGenerator J=0 <;>
      simp only [hI,hJ,mul_eq_zero,or_false,ite_true,ite_false,zero_mul,mul_zero]

theorem primaryCoefficient_good (ψ : Character) (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    primaryCoefficient ψ I = elementCoeff ψ (primaryGenerator I) := by
  change (if primaryGenerator I=0 then 0 else idealCoeff ψ I)=_
  rw [ite_eq_right hI]
  conv_lhs => rw [← (primaryGenerator_spec I hI).1,idealCoeff_span ψ hI]

theorem primaryCoefficient_norm (ψ : Character) (I : Ideal O) : ‖primaryCoefficient ψ I‖ ≤ 1 := by
  change ‖if primaryGenerator I=0 then 0 else idealCoeff ψ I‖ ≤ 1
  split_ifs
  · simp only [norm_zero,zero_le_one]
  · exact idealCoeff_norm_le_one ψ I

def periodicValue (c : O) (ψ : Character) (r : O ⧸ Ideal.span {c}) : ℂ :=
  if (3:O) ∣ Quotient.out r-1 then elementCoeff ψ (Quotient.out r) else 0

theorem periodicValue_mk (c : O) (h3 : (3:O) ∣ c) (ψ : Character)
    (hmod : (Ideal.span {c} : Ideal O) ≤ ψ.modulus) (x : O) :
    periodicValue c ψ (Ideal.Quotient.mk (Ideal.span {c}) x) =
      if (3:O) ∣ x-1 then elementCoeff ψ x else 0 := by
  have hc : c ∣ Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) x)-x :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk _ x)))
  have hd := h3.trans hc
  have hprimary : (3:O) ∣ Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) x)-1 ↔ (3:O) ∣ x-1 := by
    constructor
    · intro h; convert dvd_sub h hd using 1 ; ring
    · intro h; convert dvd_add hd h using 1 ; ring
  have hres : Ideal.Quotient.mk ψ.modulus (Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) x)) =
      Ideal.Quotient.mk ψ.modulus x :=
    Ideal.Quotient.eq.mpr (hmod (Ideal.mem_span_singleton.mpr hc))
  simp only [periodicValue,hprimary,elementCoeff,hres]

theorem periodicValue_norm (c : O) (ψ : Character) (r : O ⧸ Ideal.span {c}) :
    ‖periodicValue c ψ r‖ ≤ 1 := by
  let : Finite (O ⧸ ψ.modulus) := Ring.HasFiniteQuotients.finiteQuotient ψ.modulus_ne_bot
  let : Fintype (O ⧸ ψ.modulus) := Fintype.ofFinite _
  unfold periodicValue
  split_ifs
  · exact norm_finite_character_le_one ψ.residue _
  · simp only [norm_zero,zero_le_one]

theorem lattice_eq_ideal_sum (c : O) (h3 : (3:O) ∣ c) (ψ : Character)
    (hmod : (Ideal.span {c} : Ideal O) ≤ ψ.modulus) (W : ℝ → ℂ) (X : ℝ) :
    (∑' z : O, periodicValue c ψ (Ideal.Quotient.mk (Ideal.span {c}) z)*W (‖eisEmbedding z‖^2/X)) =
      ∑' I : Ideal O, primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X) := by
  let f : O → ℂ := fun z => elementCoeff ψ z*W (‖eisEmbedding z‖^2/X)
  have hleft : (∑' z : O, periodicValue c ψ (Ideal.Quotient.mk (Ideal.span {c}) z)*W (‖eisEmbedding z‖^2/X)) =
      ∑' z : PrimaryLower, f z.val := by
    calc
      _ = ∑' z : O, ({z : O | (3:O) ∣ z-1} : Set O).indicator f z := by
        apply tsum_congr
        intro z
        rw [periodicValue_mk c h3 ψ hmod z]
        simp only [Set.indicator_apply,Set.mem_ofPred_eq,f]
        split_ifs <;> simp only [zero_mul]
      _ = _ := (tsum_subtype {z : O | (3:O) ∣ z-1} f).symm
  have hideal : (∑' I : GoodIdeal, primaryCoefficient ψ I.val*W ((Ideal.absNorm I.val:ℝ)/X)) =
      ∑' I : Ideal O, primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X) := by
    apply tsum_subtype_eq_of_support_subset (s := {I : Ideal O | primaryGenerator I ≠ 0})
      (f := fun I : Ideal O => primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X))
    intro I hI
    change primaryGenerator I ≠ 0
    intro hz
    apply hI
    simp only [primaryCoefficient,MonoidHom.coe_mk,OneHom.coe_mk,hz,ite_true,zero_mul]
  rw [hleft,← hideal,← primaryLowerIdealEquiv.symm.tsum_eq]
  apply tsum_congr
  intro I
  change elementCoeff ψ (primaryGenerator I.val)*W (‖eisEmbedding (primaryGenerator I.val)‖^2/X)=_
  rw [primaryGenerator_norm_sq I.val I.property,primaryCoefficient_good ψ I.val I.property]

theorem fixed_period_volume (c : O) (hc : c ≠ 0) (h3 : (3:O) ∣ c)
    (ψ : Character) (hmod : (Ideal.span {c} : Ideal O) ≤ ψ.modulus)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0 < X) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    ‖(∑' I : Ideal O, primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X)) -
      (X/‖eisEmbedding c‖^2:ℝ) • ((∑ r : O ⧸ Ideal.span {c}, periodicValue c ψ r)*paperRadialFourier W 0)‖ ≤
      (Fintype.card (O ⧸ Ideal.span {c}):ℝ)*pvControl W := by
  let := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [← lattice_eq_ideal_sum c h3 ψ hmod W X]
  have h := CenteredMomentLattice.periodic_lattice_volume_error W X hX c hc (periodicValue c ψ)
  exact h.trans (mul_le_mul_of_nonneg_right (by
    calc
      _ ≤ ∑ _r : O ⧸ Ideal.span {c}, (1:ℝ) := Finset.sum_le_sum (fun r hr => periodicValue_norm c ψ r)
      _ = _ := by simp) (pvControl_nonneg W))

theorem masked_hecke_volume
    (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    (ψ : Character) (hmod : (Ideal.span {c} : Ideal O) ≤ ψ.modulus)
    (R : Ideal O) (hR : R ≠ 0) (W : 𝓢(ℝ, ℂ)) (b X : ℝ) (hX : 0 < X)
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Iic b) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let Ψ := primaryCoefficient ψ
    let v := (1 / (‖eisEmbedding c‖ ^ 2 : ℂ)) *
      ((∑ r : O ⧸ Ideal.span {c}, periodicValue c ψ r) * paperRadialFourier W 0)
    ‖(∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) *
        (Ψ I * W ((Ideal.absNorm I : ℝ) / X))) -
      (X : ℂ) * (∑ D ∈ idealDivisors R, (moebius D : ℂ) * Ψ D / (Ideal.absNorm D : ℂ)) * v‖ ≤
      ((idealDivisors R).card : ℝ) *
        ((Fintype.card (O ⧸ Ideal.span {c}) : ℝ) * pvControl W) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let Ψ := primaryCoefficient ψ
  let v := (1 / (‖eisEmbedding c‖ ^ 2 : ℂ)) *
    ((∑ r : O ⧸ Ideal.span {c}, periodicValue c ψ r) * paperRadialFourier W 0)
  let B := (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) * pvControl W
  let L : ℝ → ℂ := fun Y => ∑' I : Ideal O, Ψ I * W ((Ideal.absNorm I : ℝ) / Y)
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) (pvControl_nonneg W)
  have hnD (D : Ideal O) (hD : D ∈ idealDivisors R) : 0 < (Ideal.absNorm D : ℝ) := by
    have hD0 : D ≠ 0 := ne_zero_of_dvd_ne_zero hR ((mem_idealDivisors hR).mp hD)
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hD0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hsingle (D : Ideal O) (hD : D ∈ idealDivisors R) :
      ‖L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * v‖ ≤ B := by
    have h := fixed_period_volume c hc h3 ψ hmod W
      (X / Ideal.absNorm D) (div_pos hX (hnD D hD))
    convert h using 1
    congr 1
    dsimp only [v]
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
    ring
  have hcoef (D : Ideal O) : ‖(moebius D : ℂ) * Ψ D‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (norm_ideal_moebius_le_one D)
      (primaryCoefficient_norm ψ D) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have heq :
      (∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) *
        (Ψ I * W ((Ideal.absNorm I : ℝ) / X))) -
        (X : ℂ) * (∑ D ∈ idealDivisors R, (moebius D : ℂ) * Ψ D / (Ideal.absNorm D : ℂ)) * v =
      ∑ D ∈ idealDivisors R, ((moebius D : ℂ) * Ψ D) *
        (L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * v) := by
    rw [masked_plain_ideal_sum R hR Ψ W b X hX hs]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro D _
    simp only [L, Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  change ‖_ - (X : ℂ) * _ * v‖ ≤ ((idealDivisors R).card : ℝ) * B
  rw [heq]
  calc
    _ ≤ ∑ D ∈ idealDivisors R, ‖((moebius D : ℂ) * Ψ D) *
        (L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * v)‖ := norm_sum_le _ _
    _ ≤ ∑ _D ∈ idealDivisors R, B := by
      apply Finset.sum_le_sum
      intro D hD
      rw [norm_mul]
      exact (mul_le_mul (hcoef D) (hsingle D hD) (norm_nonneg _) zero_le_one).trans_eq (one_mul B)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

def fixedPeriod (Q : Ideal O) : O := 3*ConcretePrimeRowBridge.idealGenerator Q

theorem fixedPeriod_ne_zero (Q : Ideal O) (hQ : Q ≠ 0) : fixedPeriod Q ≠ 0 :=
  mul_ne_zero (by norm_num) (ConcretePrimeRowBridge.idealGenerator_ne_zero Q hQ)

theorem fixedPeriod_three (Q : Ideal O) : (3:O) ∣ fixedPeriod Q := dvd_mul_right _ _

theorem span_fixedPeriod_le (Q : Ideal O) : (Ideal.span {fixedPeriod Q} : Ideal O) ≤ Q := by
  conv_rhs => rw [← ConcretePrimeRowBridge.span_idealGenerator Q]
  exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _)

theorem inducedBy_of_elementCoeff_eq (χ χ' ψ : Character)
    (heq : ∀ n, elementCoeff χ' n=elementCoeff χ n)
    (hind : CenteredExceptionalProfile.InducedBy χ ψ) :
    CenteredExceptionalProfile.InducedBy χ' ψ := by
  have hideal (I : Ideal O) : idealCoeff χ' I=idealCoeff χ I := by
    by_cases hI : I=0
    · simp only [hI,map_zero]
    · conv_lhs => rw [← ConcretePrimeRowBridge.span_idealGenerator I,
        idealCoeff_span χ' (ConcretePrimeRowBridge.idealGenerator_ne_zero I hI),heq]
      rw [← idealCoeff_span χ (ConcretePrimeRowBridge.idealGenerator_ne_zero I hI),
        ConcretePrimeRowBridge.span_idealGenerator]
  intro I
  by_cases hI : I=0
  · simp only [hI,map_zero,ite_self]
  by_cases hc : IsCoprime I χ'.modulus
  · have hn := CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ' I |>.mpr ⟨hI,hc⟩
    rw [hideal I] at hn
    have hc' := (CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ I).mp hn |>.2
    rw [ite_eq_left hc,hideal I,hind I,ite_eq_left hc']
  · have hz : idealCoeff χ' I=0 := by
      by_contra hn
      exact hc ((CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ' I).mp hn).2
    rw [ite_eq_right hc,hz]

theorem fixedInducingRow_controlled (η : Character) (Q : Ideal O) (m A₀ z : O)
    (hm : m ≠ 0) (hA : A₀ ≠ 0) (hz : z ≠ 0)
    (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hex : CenteredExceptionalProfile.FixedInducingRow η Q m A₀ z) :
    ∃ χ ψ : Character,
      χ.modulus.absNorm ≤ HeckeRowClosure.rowConductorBound η m 1 (A₀*z) ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      CenteredExceptionalProfile.InducedBy χ ψ ∧ Q ≤ ψ.modulus ∧
      ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
        (HeckeRowClosure.elementHom η) m 1 (A₀*z) n := by
  obtain ⟨χ₀,ψ,hprim,hind,hQ,hrow₀⟩ := hex
  obtain ⟨χ,hbound,hrow⟩ := HeckeRowClosure.exists_row_character_with_conductor
    η m 1 (A₀*z) hm one_ne_zero (mul_ne_zero hA hz) hmLam hm2
  refine ⟨χ,ψ,hbound,hprim,?_,hQ,hrow⟩
  exact inducedBy_of_elementCoeff_eq χ₀ χ ψ (fun n => (hrow n).trans (hrow₀ n).symm) hind

theorem induced_primaryCoefficient (χ ψ : Character)
    (hind : CenteredExceptionalProfile.InducedBy χ ψ) (I : Ideal O) :
    primaryCoefficient χ I =
      (if IsCoprime I χ.modulus then (1:ℂ) else 0)*primaryCoefficient ψ I := by
  change (if primaryGenerator I=0 then 0 else idealCoeff χ I)=
    (if IsCoprime I χ.modulus then (1:ℂ) else 0)*(if primaryGenerator I=0 then 0 else idealCoeff ψ I)
  rw [hind I]
  split_ifs <;> simp only [one_mul,zero_mul]

theorem primaryCoefficient_actual_row (η χ : Character) (m A₀ z : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n) (I : Ideal O) :
    primaryCoefficient χ I=idealCoeff χ I := by
  change (if primaryGenerator I=0 then 0 else idealCoeff χ I)=_
  by_cases hI : I=0
  · simp only [hI,primaryGenerator_zero,map_zero,ite_self]
  by_cases hg : primaryGenerator I=0
  · rw [ite_eq_left hg]
    let n := ConcretePrimeRowBridge.idealGenerator I
    have hn : n ≠ 0 := ConcretePrimeRowBridge.idealGenerator_ne_zero I hI
    have hs : Ideal.span {n}=I := ConcretePrimeRowBridge.span_idealGenerator I
    have hbad : ¬Supported (Ideal.span {n}) := by
      intro h
      have hp : primaryGenerator (Ideal.span {n}) ≠ 0 :=
        PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff n |>.mpr ((CanonicalQuadraticSieve.supported_span_iff n).mp h).1
      exact hp (hs ▸ hg)
    rw [← hs,idealCoeff_span χ hn,hrow,
      CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hbad]
  · rw [ite_eq_right hg]

def density (c : O) (hc : c ≠ 0) (ψ : Character) (R : Ideal O) : ℂ :=
  letI := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  (∑ D ∈ idealDivisors R, (moebius D:ℂ)*primaryCoefficient ψ D/(Ideal.absNorm D:ℂ)) *
    (1/(‖eisEmbedding c‖^2:ℂ))*(∑ r : O ⧸ Ideal.span {c}, periodicValue c ψ r)

theorem density_norm_le (c : O) (hc : c ≠ 0) (ψ : Character) (R : Ideal O) (hR : R ≠ 0) :
    ‖density c hc ψ R‖ ≤
      ((idealDivisors R).card:ℝ)*(Nat.card (O ⧸ Ideal.span {c}):ℝ)/‖eisEmbedding c‖^2 := by
  let := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  have hdiv : ‖∑ D ∈ idealDivisors R, (moebius D:ℂ)*primaryCoefficient ψ D/(Ideal.absNorm D:ℂ)‖ ≤
      ((idealDivisors R).card:ℝ) := by
    calc
      _ ≤ ∑ D ∈ idealDivisors R, ‖(moebius D:ℂ)*primaryCoefficient ψ D/(Ideal.absNorm D:ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _D ∈ idealDivisors R, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro D hD
        have hD0 : D ≠ 0 := ne_zero_of_dvd_ne_zero hR ((mem_idealDivisors hR).mp hD)
        have hN : (1:ℝ) ≤ Ideal.absNorm D := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD0)
        rw [norm_div,norm_mul,Complex.norm_natCast]
        apply (div_le_one (by linarith : 0 < (Ideal.absNorm D:ℝ))).mpr
        exact ((mul_le_of_le_one_left (norm_nonneg _) (norm_ideal_moebius_le_one D)).trans
          (primaryCoefficient_norm ψ D)).trans hN
      _ = _ := by simp
  have hres : ‖∑ r : O ⧸ Ideal.span {c}, periodicValue c ψ r‖ ≤
      (Nat.card (O ⧸ Ideal.span {c}):ℝ) := by
    calc
      _ ≤ ∑ r : O ⧸ Ideal.span {c}, ‖periodicValue c ψ r‖ := norm_sum_le _ _
      _ ≤ ∑ _r : O ⧸ Ideal.span {c}, (1:ℝ) := Finset.sum_le_sum (fun r hr => periodicValue_norm c ψ r)
      _ = _ := by simp [Nat.card_eq_fintype_card]
  unfold density
  rw [norm_mul,norm_mul,norm_div,norm_one,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  calc
    _ ≤ (((idealDivisors R).card:ℝ)*(1/‖eisEmbedding c‖^2))*(Nat.card (O ⧸ Ideal.span {c}):ℝ) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hdiv (by positivity)) hres (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem actual_induced_volume (η χ ψ : Character) (Q : Ideal O) (hQ : Q ≠ 0)
    (hQψ : Q ≤ ψ.modulus) (hind : CenteredExceptionalProfile.InducedBy χ ψ)
    (m A₀ z : O) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n)
    (W : 𝓢(ℝ,ℂ)) (b X : ℝ) (hX : 0 < X)
    (hs : Function.support (W:ℝ→ℂ) ⊆ Set.Iic b) :
    ‖(∑' I : Ideal O, idealCoeff χ I*W ((Ideal.absNorm I:ℝ)/X)) -
      (X:ℂ)*(density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus*paperRadialFourier W 0)‖ ≤
      ((idealDivisors χ.modulus).card:ℝ)*(Nat.card (O ⧸ Ideal.span {fixedPeriod Q}):ℝ)*pvControl W := by
  let := finite_quotient_span (fixedPeriod_ne_zero Q hQ)
  let : Fintype (O ⧸ Ideal.span {fixedPeriod Q}) := Fintype.ofFinite _
  have h := masked_hecke_volume (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ)
    (fixedPeriod_three Q) ψ ((span_fixedPeriod_le Q).trans hQψ)
    χ.modulus χ.modulus_ne_bot W b X hX hs
  have he (I : Ideal O) :
      (if IsCoprime I χ.modulus then (1:ℂ) else 0)*primaryCoefficient ψ I=idealCoeff χ I := by
    rw [← induced_primaryCoefficient χ ψ hind I,primaryCoefficient_actual_row η χ m A₀ z hmLam hm2 hrow I]
  simp_rw [show ∀ I : Ideal O, (if IsCoprime I χ.modulus then (1:ℂ) else 0)*
      (primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X)) =
        idealCoeff χ I*W ((Ideal.absNorm I:ℝ)/X) by intro I; rw [← mul_assoc,he]] at h
  convert h using 1
  · congr 1
    unfold density
    ring
  · rw [Nat.card_eq_fintype_card]
    ring

end SevenEighths.CenteredMomentHeckeVolume

end

end OAI
end OAIOriginalModule1323

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.MaskDescent
Source SHA256: 6aea5168746b85d4d9248a4debaea71be43fcdf969ba8df0c68d028c5797f69b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1324



namespace OAI

noncomputable section
open scoped Classical BigOperators

