lemma unramifiedCubicGaussSeries_prime_two_power (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h) :
    unramifiedCubicGaussSeries s (h*p^2)=
      (1-(Ideal.absNorm (Ideal.span {p}):ℂ)^2*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*
        unramifiedPrimeDeletedSeries p s (h*p^2) := by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 2
  have hg1:cubicUnitGaussSum (h*p^2) p=0:=by
    rw [cubicUnitGaussSum_frequency_dvd _ p hp.ne_zero
      ((dvd_pow_self p (by decide : (2:ℕ)≠0)).trans (dvd_mul_left (p^2) h))]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
  have hg2:cubicUnitGaussSum (h*p^2) (p^2)=0:=by
    rw [cubicUnitGaussSum_frequency_dvd _ (p^2) (pow_ne_zero _ hp.ne_zero) (dvd_mul_left (p^2) h)]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 1
  have hg3:cubicUnitGaussSum (h*p^2) (p^3)= -(Ideal.absNorm (Ideal.span {p}):ℂ)^2:=by
    have hh:=cubicUnitGaussSum_prime_power_lift p hp hprimary 2 h
    rw [primeCubicGauss_trivial_nonzero p hp hprimary 3 (dvd_refl 3) h hph] at hh
    simpa only [mul_comm (p^2) h,mul_neg_one] using hh
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    cubicUnitGaussSum_one,mul_one,one_mul,hg1,hg2,hg3,mul_zero,zero_mul,add_zero] at he
  rw [unramifiedPrimeDeletedSeries_cube_shift p hp] at he
  exact he.trans (by ring)

lemma unramifiedCubicGaussSeries_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h) :
    unramifiedCubicGaussSeries s (h*p^5)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)^3*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*
        unramifiedCubicGaussSeries s (h*p^2) := by
  have he:=unramifiedCubicGaussSeries_cube_step p hp hprimary s hs h hph 2
  rw [←unramifiedCubicGaussSeries_prime_two_power p hp hprimary s hs h hph] at he
  simpa only [show 2+3=5 from rfl,add_mul,one_mul] using he

theorem unramifiedGaussResidue_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    unramifiedGaussResidue (h*p^5)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*unramifiedGaussResidue (h*p^2) := by
  let A:ℂ→ℂ:=fun s=>1+(Ideal.absNorm (Ideal.span {p}):ℂ)^3*
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3
  have hA (s:ℂ):AnalyticAt ℂ A s:=analyticAt_const.add
    (analyticAt_const.mul ((gaussPrimeWeight_analytic p hp s).pow 3))
  have he:=unramifiedGaussResidue_of_initial_relation (h*p^5) (h*p^2) 0 A (fun _=>0)
    (fun s _=>hA s) (fun _ _=>analyticAt_const) (hA _).continuousAt continuousAt_const
    (fun s hs _=>by simpa only [A,zero_mul,add_zero] using
      unramifiedCubicGaussSeries_square_cube p hp hprimary s (by linarith) h hph)
  dsimp only [A] at he
  rw [gaussPrimeWeight_center p hp] at he
  simpa only [zero_mul,add_zero] using he

lemma principalResidueTerm_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (u:Eisˣ) (n:ℕ) :
    principalResidueTerm (h*p^5) u n=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*principalResidueTerm (h*p^2) u n := by
  let c:=u.val*lambda^(n+2)
  have hA:=arithmeticResidueSum_frequency_cube (h*p^2) c p
    (ramifiedElement_ne_zero u (n+2)) (ramifiedElement_level u (n+2) (by omega)) hprimary
    (ramified_primary_coprime u (n+2) p hprimary).of_mul_left_right
  have hfreq:¬p∣h*(9*c):=ramified_prime_frequency_not_dvd h p hp hprimary hph u (n+2)
  rw [show (h*p^2)*p^3=h*p^5 by ring] at hA
  change _*arithmeticResidueSum (h*p^5) c*unramifiedGaussResidue ((h*p^5)*(9*c))=_
  rw [hA,show (h*p^5)*(9*c)=(h*(9*c))*p^5 by ring,
    unramifiedGaussResidue_square_cube p hp hprimary (h*(9*c)) hfreq]
  change _=(1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*
    (((3^(n+2):ℕ):ℂ)^(-(4/3:ℂ))*arithmeticResidueSum (h*p^2) c*
      unramifiedGaussResidue ((h*p^2)*(9*c)))
  rw [show (h*p^2)*(9*c)=(h*(9*c))*p^2 by ring]
  ring

lemma principalArithmeticResidue_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    principalArithmeticResidue (h*p^5)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*principalArithmeticResidue (h*p^2) := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  let N:=max (ramifiedFrequencyBound (h*p^5)+1) (ramifiedFrequencyBound (h*p^2)+1)
  rw [principalArithmeticResidue_eq_sum (h*p^5) (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) N (le_max_left _ _),
    principalArithmeticResidue_eq_sum (h*p^2) (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) N (le_max_right _ _)]
  simp_rw [principalResidueTerm_square_cube p hp hprimary h hph,←Finset.mul_sum]
  ring

theorem sourceArithmeticResidue_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceArithmeticResidue (h*p^5)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*sourceArithmeticResidue (h*p^2) := by
  have hm:ShortDraftTrace.breveE (cuspFrequency (h*p^5))=
      ShortDraftTrace.breveE (cuspFrequency (h*p^2)):=by
    rw [show h*p^5=(((h*p^2)*p)*p)*p by ring]
    rw [sourceRayPhase_mul_primary _ p hprimary,sourceRayPhase_mul_primary _ p hprimary,
      sourceRayPhase_mul_primary _ p hprimary]
  have hp9:¬p∣9*h:=by
    have hh:=ramified_prime_frequency_not_dvd h p hp hprimary hph (1:Eisˣ) 0
    simpa only [Units.val_one,pow_zero,one_mul,mul_one,mul_comm 9 h] using hh
  simp only [sourceArithmeticResidue,hm]
  split_ifs
  · rw [principalArithmeticResidue_square_cube p hp hprimary h hph,
      show 9*(h*p^5)=(9*h)*p^5 by ring,
      unramifiedGaussResidue_square_cube p hp hprimary (9*h) hp9,
      show 9*(h*p^2)=(9*h)*p^2 by ring]
    ring
  · ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceArithmeticResidue_prime_pow_mod (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hh:h≠0) (n:ℕ) :
    sourceArithmeticResidue (h*p^n)=sourceArithmeticResidue (h*p^(n%3)) := by
  induction n using Nat.strong_induction_on with
  | h n ih=>
    by_cases hn:n<3
    · rw [Nat.mod_eq_of_lt hn]
    · have hn3:3≤n:=by omega
      have he:h*p^n=(h*p^(n-3))*p^3:=by rw [mul_assoc,←pow_add,Nat.sub_add_cancel hn3]
      rw [he,sourceArithmeticResidue_prime_cube p hp hprimary _ (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)),
        ih (n-3) (by omega)]
      have hm:(n-3)%3=n%3:=by omega
      rw [hm]

theorem sourceArithmeticResidue_prime_square (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceArithmeticResidue (h*p^2)=0 := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  have he:=sourceArithmeticResidue_square_cube p hp hprimary h hph
  rw [show h*p^5=(h*p^2)*p^3 by ring,
    sourceArithmeticResidue_prime_cube p hp hprimary _ (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero))] at he
  have hq:(Ideal.absNorm (Ideal.span {p}):ℂ)≠0:=Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hz:(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceArithmeticResidue (h*p^2)=0:=by
    linear_combination -he
  exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hq)

theorem sourceArithmeticResidue_prime_factor (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceArithmeticResidue (h*p)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ))*
        primeCubicGauss p hp hprimary 2 (9*h)*sourceArithmeticResidue h := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  have hrec:=sourceArithmeticResidue_prime_recurrence p hp hprimary h hph
  rw [sourceArithmeticResidue_prime_cube p hp hprimary h hh] at hrec
  have hrel:(Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*
      primeCubicGauss p hp hprimary 1 (9*h)*sourceArithmeticResidue (h*p)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceArithmeticResidue h:=by
    linear_combination hrec
  have hp9:¬p∣9*h:=by
    have ht:=ramified_prime_frequency_not_dvd h p hp hprimary hph (1:Eisˣ) 0
    simpa only [Units.val_one,pow_zero,one_mul,mul_one,mul_comm 9 h] using ht
  have hG:=primeCubicGauss_one_mul_two p hp hprimary (9*h) hp9
  let q:ℂ:=(Ideal.absNorm (Ideal.span {p}):ℂ)
  have hq:q≠0:=Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hpower:q^(-(2/3:ℂ))*q^(-(4/3:ℂ))*q^2=1:=by
    rw [←Complex.cpow_add _ _ hq,←Complex.cpow_natCast q 2,
      ←Complex.cpow_add _ _ hq]
    norm_num
  calc
    sourceArithmeticResidue (h*p)=
        (q^(-(2/3:ℂ))*q^(-(4/3:ℂ))*q^2)*sourceArithmeticResidue (h*p):=by rw [hpower,one_mul]
    _=q^(-(2/3:ℂ))*q*primeCubicGauss p hp hprimary 2 (9*h)*
        (q^(-(4/3:ℂ))*primeCubicGauss p hp hprimary 1 (9*h)*sourceArithmeticResidue (h*p)):=by
      calc
        _=q^(-(2/3:ℂ))*q^(-(4/3:ℂ))*q*
          (primeCubicGauss p hp hprimary 1 (9*h)*primeCubicGauss p hp hprimary 2 (9*h))*
          sourceArithmeticResidue (h*p):=by rw [hG];ring
        _=_:=by ring
    _=q^(-(2/3:ℂ))*q*primeCubicGauss p hp hprimary 2 (9*h)*(q⁻¹*sourceArithmeticResidue h):=by rw [hrel]
    _=_:=by
      change q^(-(2/3:ℂ))*q*primeCubicGauss p hp hprimary 2 (9*h)*(q⁻¹*sourceArithmeticResidue h)=
        q^(-(2/3:ℂ))*primeCubicGauss p hp hprimary 2 (9*h)*sourceArithmeticResidue h
      field_simp [hq]

theorem sourceArithmeticResidue_prime_power_table (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (n:ℕ) :
    sourceArithmeticResidue (h*p^n)=
      if n%3=0 then sourceArithmeticResidue h
      else if n%3=1 then
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ))*
          primeCubicGauss p hp hprimary 2 (9*h)*sourceArithmeticResidue h
      else 0 := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  rw [sourceArithmeticResidue_prime_pow_mod p hp hprimary h hh n]
  split_ifs with h0 h1
  · simp only [h0,pow_zero,mul_one]
  · simp only [h1,pow_one]
    exact sourceArithmeticResidue_prime_factor p hp hprimary h hph
  · have hn:n%3=2:=by omega
    rw [hn,sourceArithmeticResidue_prime_square p hp hprimary h hph]

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma primeCubicMulChar_inverse (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) :
    (primeCubicMulChar p hp hprimary)⁻¹=primeCubicMulChar p hp hprimary^2 := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [←pow_succ'] using primeCubicMulChar_cube p hp hprimary

lemma primeCubicGauss_two_eq_star (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (h:Eis) :
    primeCubicGauss p hp hprimary 2 h=star (primeCubicGauss p hp hprimary 1 h) := by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let:Field (Eis⧸Ideal.span {p}):=Ideal.Quotient.field _
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  rw [primeCubicGauss_eq_gaussSum,primeCubicGauss_eq_gaussSum,pow_one,star_gaussSum_eq,
    primeCubicMulChar_inverse]
  have he:=mul_gaussSum_inv_eq_gaussSum
    (primeCubicMulChar p hp hprimary^2) ((quotientTrace p hp.ne_zero).mulShift (Ideal.Quotient.mk _ h))
  have hm:(primeCubicMulChar p hp hprimary^2) (-1 : Eis⧸Ideal.span {p})=1:=by
    rw [MulChar.pow_apply' _ (by decide : (2:ℕ)≠0),←map_pow]
    norm_num
  rw [hm,one_mul] at he
  exact he.symm

lemma primeCubicGauss_one_normalized (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    [(Ideal.span {p}:Ideal Eis).IsMaximal] (hg:lambda∉(Ideal.span {p}:Ideal Eis)) :
    primeCubicGauss p hp hprimary 1 1/(‖eisEmbedding p‖:ℂ)=
      breveGamma2 (Ideal.span {p}) hg p rfl hp.ne_zero := by
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  unfold breveGamma2
  rw [primeCubicGauss_eq_gaussSum,pow_one,canonicalSextic_pow_two]
  simp only [map_one,AddChar.mulShift_one]
  congr 2
  apply DFunLike.ext
  intro x
  obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
  simp only [primeCubicMulChar_mk,MulChar.ringHomComp_apply,
    symbol_prime p hp hprimary,primeValue_eq _ hg]

lemma primeCubicGauss_two_twist (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (h:Eis) (hph:¬p∣h) :
    primeCubicGauss p hp hprimary 2 h=eisEmbedding (symbol h p)*primeCubicGauss p hp hprimary 2 1 := by
  have hcop:IsCoprime p h:=hp.coprime_iff_not_dvd.mpr hph
  have he:=cubicUnitGaussSum_frequency_twist (1:Eis) p h hp.ne_zero hprimary hcop
  simp only [one_mul,←primeCubicGauss_one_eq p hp hprimary] at he
  have hs:(eisEmbedding (symbol h p))^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime h p hprimary hcop.symm,map_one]
  have hstar:star (eisEmbedding (symbol h p))*eisEmbedding (symbol h p)=1:=by
    have hn:‖eisEmbedding (symbol h p)‖=1:=by
      have hn:=congrArg norm hs
      simp only [norm_pow,norm_one] at hn
      exact (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3:ℕ)≠0)).mp (by simpa using hn)
    rw [mul_comm]
    simpa only [Complex.star_def,Complex.normSq_eq_norm_sq,hn,one_pow,Complex.ofReal_one] using Complex.mul_conj (eisEmbedding (symbol h p))
  have hconj:=congrArg star he
  simp only [star_mul,←primeCubicGauss_two_eq_star] at hconj
  calc
    _=(star (eisEmbedding (symbol h p))*eisEmbedding (symbol h p))*primeCubicGauss p hp hprimary 2 h:=by rw [hstar,one_mul]
    _=eisEmbedding (symbol h p)*(star (eisEmbedding (symbol h p))*primeCubicGauss p hp hprimary 2 h):=by ring
    _=_:=by rw [mul_comm (star (eisEmbedding (symbol h p))),hconj]

lemma cubicBesselNormalizer_mul (h p:Eis) :
    cubicBesselNormalizer (h*p)=(‖eisEmbedding p‖:ℂ)^(1/3:ℂ)*cubicBesselNormalizer h := by
  have hfreq:‖cuspFrequency (h*p)‖=‖cuspFrequency h‖*‖eisEmbedding p‖:=by
    rw [cuspFrequency_mul_right,norm_mul]
  have he:(2*Real.pi*‖cuspFrequency (h*p)‖:ℂ)=
      (‖eisEmbedding p‖:ℂ)*((2*Real.pi*‖cuspFrequency h‖:ℝ):ℂ):=by rw [hfreq];push_cast;ring
  unfold cubicBesselNormalizer
  rw [he,Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (by positivity)]
  push_cast
  ring

lemma prime_normalizer_powers (p:Eis) (hp:p≠0) :
    (‖eisEmbedding p‖:ℂ)^(1/3:ℂ)*(Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ))=
      (‖eisEmbedding p‖:ℂ)⁻¹ := by
  have hr:(‖eisEmbedding p‖:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp))
  rw [←Complex.ofReal_natCast,←eisEmbedding_norm_sq_eq_absNorm_span,pow_two,
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _),
    ←mul_assoc,←Complex.cpow_add _ _ hr,←Complex.cpow_add _ _ hr]
  convert Complex.cpow_neg_one (‖eisEmbedding p‖:ℂ) using 1 ; congr 1 ; norm_num

theorem sourceResidualFourierCoefficient_prime_factor (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceResidualFourierCoefficient (h*p)=
      (primeCubicGauss p hp hprimary 2 (9*h)/(‖eisEmbedding p‖:ℂ))*sourceResidualFourierCoefficient h := by
  rw [sourceResidualFourierCoefficient,cubicBesselNormalizer_mul,
    sourceArithmeticResidue_prime_factor p hp hprimary h hph,sourceResidualFourierCoefficient]
  calc
    _=((‖eisEmbedding p‖:ℂ)^(1/3:ℂ)*(Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ)))*
      primeCubicGauss p hp hprimary 2 (9*h)*(cubicBesselNormalizer h*sourceArithmeticResidue h):=by ring
    _=_:=by rw [prime_normalizer_powers p hp.ne_zero];ring

theorem sourceResidualFourierCoefficient_prime_gamma (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) [(Ideal.span {p}:Ideal Eis).IsMaximal]
    (hg:lambda∉(Ideal.span {p}:Ideal Eis)) (h:Eis) (hph:¬p∣h) :
    sourceResidualFourierCoefficient (h*p)=
      eisEmbedding (symbol (9*h) p)*star (breveGamma2 (Ideal.span {p}) hg p rfl hp.ne_zero)*
        sourceResidualFourierCoefficient h := by
  have hp9:¬p∣9*h:=by
    have ht:=ramified_prime_frequency_not_dvd h p hp hprimary hph (1:Eisˣ) 0
    simpa only [Units.val_one,pow_zero,one_mul,mul_one,mul_comm 9 h] using ht
  rw [sourceResidualFourierCoefficient_prime_factor p hp hprimary h hph,
    primeCubicGauss_two_twist p hp hprimary (9*h) hp9,primeCubicGauss_two_eq_star,
    ←primeCubicGauss_one_normalized p hp hprimary hg,star_div₀,Complex.star_def,Complex.conj_ofReal]
  ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def normalizedCubicUnitGauss (n:Eis) : ℂ :=
  cubicUnitGaussSum 1 n/(‖eisEmbedding n‖:ℂ)

@[simp] lemma normalizedCubicUnitGauss_one : normalizedCubicUnitGauss 1=1 := by
  simp [normalizedCubicUnitGauss]

lemma cubicSymbol_star_mul (a b:Eis) (hb:lambda^2∣b-1) (hab:IsCoprime a b) :
    star (eisEmbedding (symbol a b))*eisEmbedding (symbol a b)=1 := by
  have hc:(eisEmbedding (symbol a b))^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime a b hb hab,map_one]
  have hn:‖eisEmbedding (symbol a b)‖=1:=by
    apply (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3:ℕ)≠0)).mp
    simpa only [norm_pow,norm_one,one_pow] using congrArg norm hc
  rw [mul_comm]
  simpa only [Complex.star_def,Complex.normSq_eq_norm_sq,hn,one_pow,Complex.ofReal_one] using
    Complex.mul_conj (eisEmbedding (symbol a b))

lemma normalizedCubicUnitGauss_coprime_product (a b:Eis) (ha:a≠0) (hb:b≠0)
    (hap:lambda^2∣a-1) (hbp:lambda^2∣b-1) (hab:IsCoprime a b) :
    star (normalizedCubicUnitGauss (a*b))=
      eisEmbedding (symbol a b)*star (normalizedCubicUnitGauss a)*star (normalizedCubicUnitGauss b) := by
  have hG:=cubicUnitGaussSum_coprime_product 1 a b ha hb hap hbp hab
  simp only [one_mul] at hG
  have ht:=cubicUnitGaussSum_frequency_twist 1 b a hb hbp hab.symm
  simp only [one_mul] at ht
  have hN:eisEmbedding (symbol a b)*normalizedCubicUnitGauss (a*b)=
      normalizedCubicUnitGauss a*normalizedCubicUnitGauss b:=by
    unfold normalizedCubicUnitGauss
    rw [hG,map_mul,norm_mul,Complex.ofReal_mul]
    calc
      _=cubicUnitGaussSum 1 a*(eisEmbedding (symbol a b)*cubicUnitGaussSum a b)/
        ((‖eisEmbedding a‖:ℂ)*(‖eisEmbedding b‖:ℂ)):=by ring
      _=_:=by rw [ht];ring
  have hs:=congrArg star hN
  simp only [star_mul] at hs
  have hc:=cubicSymbol_star_mul a b hbp hab
  calc
    _=(star (eisEmbedding (symbol a b))*eisEmbedding (symbol a b))*
        star (normalizedCubicUnitGauss (a*b)):=by rw [hc,one_mul]
    _=eisEmbedding (symbol a b)*(star (normalizedCubicUnitGauss (a*b))*
        star (eisEmbedding (symbol a b))):=by ring
    _=_:=by rw [hs];ring

lemma sourceResidualFourierCoefficient_prime_normalized (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceResidualFourierCoefficient (h*p)=
      eisEmbedding (symbol (9*h) p)*star (normalizedCubicUnitGauss p)*sourceResidualFourierCoefficient h := by
  have hp9:¬p∣9*h:=by
    have ht:=ramified_prime_frequency_not_dvd h p hp hprimary hph (1:Eisˣ) 0
    simpa only [Units.val_one,pow_zero,one_mul,mul_one,mul_comm 9 h] using ht
  rw [sourceResidualFourierCoefficient_prime_factor p hp hprimary h hph,
    primeCubicGauss_two_twist p hp hprimary (9*h) hp9,primeCubicGauss_two_eq_star,
    normalizedCubicUnitGauss,←primeCubicGauss_one_eq p hp hprimary,
    star_div₀,Complex.star_def,Complex.conj_ofReal]
  ring

lemma primary_finset_product {ι:Type*} (s:Finset ι) (p:ι→Eis)
    (hp:∀i∈s,lambda^2∣p i-1) : lambda^2∣(∏i∈s,p i)-1 := by
  classical
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert i s hi ih=>
    rw [Finset.prod_insert hi]
    exact primary_mul _ _ (hp i (Finset.mem_insert_self _ _))
      (ih (fun j hj=>hp j (Finset.mem_insert_of_mem hj)))

theorem sourceResidualFourierCoefficient_prime_product {ι:Type*}
    (s:Finset ι) (p:ι→Eis) (hp:∀i∈s,Prime (p i))
    (hprimary:∀i∈s,lambda^2∣p i-1)
    (hpair:∀i∈s,∀j∈s,i≠j→IsCoprime (p i) (p j))
    (h:Eis) (hph:∀i∈s,¬p i∣h) :
    sourceResidualFourierCoefficient (h*(∏i∈s,p i))=
      eisEmbedding (symbol (9*h) (∏i∈s,p i))*
        star (normalizedCubicUnitGauss (∏i∈s,p i))*sourceResidualFourierCoefficient h := by
  classical
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert i s hi ih=>
    have hpi:=hp i (Finset.mem_insert_self _ _)
    have hpri:=hprimary i (Finset.mem_insert_self _ _)
    have hps:∀j∈s,Prime (p j):=fun j hj=>hp j (Finset.mem_insert_of_mem hj)
    have hprs:∀j∈s,lambda^2∣p j-1:=fun j hj=>hprimary j (Finset.mem_insert_of_mem hj)
    have hcpi:IsCoprime (p i) (∏j∈s,p j):=IsCoprime.prod_right (fun j hj=>
      hpair i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) (by intro he;subst j;exact hi hj))
    have hbs:(∏j∈s,p j)≠0:=Finset.prod_ne_zero_iff.mpr (fun j hj=>(hps j hj).ne_zero)
    have hpb:¬p i∣h*(∏j∈s,p j):=by
      intro hd
      rcases hpi.dvd_mul.mp hd with hd|hd
      · exact hph i (Finset.mem_insert_self _ _) hd
      · exact hpi.not_isUnit (hcpi.isUnit_of_dvd hd)
    have hih:=ih hps hprs (fun j hj k hk hjk=>hpair j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk)
      (fun j hj=>hph j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hi,show h*(p i*(∏j∈s,p j))=(h*(∏j∈s,p j))*p i by ring,
      sourceResidualFourierCoefficient_prime_normalized (p i) hpi hpri _ hpb,hih]
    rw [mul_comm (p i) (∏j∈s,p j),
      normalizedCubicUnitGauss_coprime_product _ _ hbs hpi.ne_zero
        (primary_finset_product s p hprs) hpri hcpi.symm,
      symbol_mul_denominator,map_mul]
    rw [show (9:Eis)*(h*(∏j∈s,p j))=(9*h)*(∏j∈s,p j) by ring,
      symbol_mul_numerator _ _ (p i) hpri,map_mul]
    ring

lemma symbol_nine_eq_paperLambda (n:Eis) (hn:lambda^2∣n-1) :
    symbol 9 n=symbol ramifiedTraceLambda n := by
  have he:(9:Eis)=ramifiedTraceLambda^4:=by
    rw [show (4:ℕ)=2*2 from rfl,pow_mul,ramifiedTraceLambda_square]
    norm_num
  have hcop:IsCoprime ramifiedTraceLambda n:=
    ramified_character_coprime 0 1 _ n (Or.inl (by simp)) hn
  rw [he,symbol_pow_numerator _ _ hn,show (4:ℕ)=3+1 from rfl,pow_add,
    symbol_cube_of_isCoprime _ _ hn hcop,pow_one,one_mul]

theorem sourceResidualFourierCoefficient_primary_product {ι:Type*}
    (s:Finset ι) (p:ι→Eis) (hp:∀i∈s,Prime (p i))
    (hprimary:∀i∈s,lambda^2∣p i-1)
    (hpair:∀i∈s,∀j∈s,i≠j→IsCoprime (p i) (p j)) :
    star (sourceResidualFourierCoefficient (∏i∈s,p i))=
      star (sourceResidualFourierCoefficient 1)*
        star (eisEmbedding (symbol ramifiedTraceLambda (∏i∈s,p i)))*
        normalizedCubicUnitGauss (∏i∈s,p i) := by
  have he:=sourceResidualFourierCoefficient_prime_product s p hp hprimary hpair 1
    (fun i hi=>fun hd=>(hp i hi).not_isUnit (isUnit_of_dvd_one hd))
  simp only [one_mul,mul_one] at he
  rw [symbol_nine_eq_paperLambda _ (primary_finset_product s p hprimary)] at he
  rw [he,star_mul,star_mul,star_star]
  ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem sourceArithmeticResidue_primary_cube (b:Eis) (hb:b≠0)
    (hbprimary:lambda^2∣b-1) (h:Eis) (hh:h≠0) :
    sourceArithmeticResidue (h*b^3)=sourceArithmeticResidue h := by
  obtain ⟨s,hs,hpr⟩:=exists_primary_prime_factorization b hb hbprimary
  rw [←hs]
  clear hs hb hbprimary b
  induction s using Multiset.induction_on generalizing h with
  | empty=>simp
  | @cons p s ih=>
    have hp:=hpr p (Multiset.mem_cons_self _ _)
    have hs:∀q∈s,Prime q∧lambda^2∣q-1:=fun q hq=>hpr q (Multiset.mem_cons_of_mem hq)
    have hs0:s.prod≠0:=by
      intro hz
      exact (hs 0 (Multiset.prod_eq_zero_iff.mp hz)).1.ne_zero rfl
    rw [Multiset.prod_cons,show h*(p*s.prod)^3=(h*s.prod^3)*p^3 by ring,
      sourceArithmeticResidue_prime_cube p hp.1 hp.2 _ (mul_ne_zero hh (pow_ne_zero _ hs0))]
    exact ih h hh hs

theorem sourceResidualFourierCoefficient_primary_cube (b:Eis) (hb:b≠0)
    (hbprimary:lambda^2∣b-1) (h:Eis) (hh:h≠0) :
    sourceResidualFourierCoefficient (h*b^3)=
      (‖eisEmbedding b‖:ℂ)*sourceResidualFourierCoefficient h := by
  rw [sourceResidualFourierCoefficient,cubicBesselNormalizer_mul_cube h b hb,
    sourceArithmeticResidue_primary_cube b hb hbprimary h hh,sourceResidualFourierCoefficient]
  ring

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma cubicSymbol_prime_zero (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (x:Eis) (hpx:p∣x) : symbol x p=0 := by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg:lambda∉(Ideal.span {p}:Ideal Eis):=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  rw [symbol_prime p hp hprimary,primeValue_eq _ hg,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hpx),MulChar.map_zero]

lemma cubicSymbol_zero_of_not_coprime (n:Eis) (hn:n≠0) (hprimary:lambda^2∣n-1)
    (x:Eis) (hnot:¬IsCoprime n x) : symbol x n=0 := by
  obtain ⟨s,hs,hp⟩:=exists_primary_prime_factorization n hn hprimary
  rw [←hs] at hnot ⊢
  clear hs hn hprimary n
  induction s using Multiset.induction_on with
  | empty=>exact False.elim (hnot (by simpa using (isCoprime_one_left : IsCoprime (1:Eis) x)))
  | @cons p s ih=>
    have hprime:=hp p (Multiset.mem_cons_self _ _)
    have hrest:∀q∈s,Prime q∧lambda^2∣q-1:=fun q hq=>hp q (Multiset.mem_cons_of_mem hq)
    rw [Multiset.prod_cons,symbol_mul_denominator]
    by_cases hc:IsCoprime p x
    · have hnc:¬IsCoprime s.prod x:=fun h=>hnot (by simpa using hc.mul_left h)
      rw [ih hnc hrest,mul_zero]
    · rw [cubicSymbol_prime_zero p hprime.1 hprime.2 x
        (hprime.1.irreducible.dvd_iff_not_isCoprime.mpr hc),zero_mul]

lemma cubicRow_eq_idealSymbol (I:Ideal Eis) (hI:primaryGenerator I≠0)
    (hsq:Squarefree I) (a:Eis) :
    cubicRow I hI (Ideal.Quotient.mk I a)=eisEmbedding (idealSymbol I a) := by
  rw [cubicRow_mk]
  simp_rw [canonicalSextic_pow_two,MulChar.ringHomComp_apply,←primeValue_eq]
  change (∏P:primeSupport I,eisEmbedding (primeValue P.val a))=eisEmbedding (idealSymbol I a)
  rw [←Finset.prod_subtype (primeSupport I) (fun _=>Iff.rfl)
    (fun P=>eisEmbedding (primeValue P a)),←map_prod]
  have hI0:=primaryGenerator_ne_zero_ideal I hI
  have hnodup: (UniqueFactorizationMonoid.normalizedFactors I).Nodup:=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI0).mp hsq
  congr 1
  rw [idealSymbol,ite_eq_right hI0]
  change (((primeSupport I).val.map (fun P=>primeValue P a)).prod)=_
  have hv:(primeSupport I).val=UniqueFactorizationMonoid.normalizedFactors I:=by
    simpa only [primeSupport, Multiset.toFinset_val] using hnodup.dedup
  rw [hv]

lemma cubicUnitGaussSum_full (n:Eis) (hn:n≠0) (hprimary:lambda^2∣n-1) (h:Eis) :
    cubicUnitGaussSum h n=
      ∑'x:Eis⧸Ideal.span {n},eisEmbedding (symbol (GaussianShiftedPartition.representative n x) n)*
        quotientTrace n hn (Ideal.Quotient.mk _ h*x) := by
  let f:(Eis⧸Ideal.span {n})→ℂ:=fun x=>
    eisEmbedding (symbol (GaussianShiftedPartition.representative n x) n)*
      quotientTrace n hn (Ideal.Quotient.mk _ h*x)
  have hsup:Function.support f⊆{x|IsUnit x}:=by
    intro x hx
    by_contra hnot
    change ¬IsUnit x at hnot
    have hcop:¬IsCoprime n (GaussianShiftedPartition.representative n x):=by
      intro hc
      apply hnot
      have hh:=(isUnit_quotient_span_iff n (GaussianShiftedPartition.representative n x)).mpr hc
      simpa only [GaussianShiftedPartition.representative_spec] using hh
    exact hx (by simp only [f,cubicSymbol_zero_of_not_coprime n hn hprimary _ hcop,map_zero,zero_mul])
  change cubicUnitGaussSum h n=∑'x,f x
  rw [←tsum_subtype_eq_of_support_subset hsup]
  unfold cubicUnitGaussSum
  apply tsum_congr
  intro x
  dsimp only [f]
  rw [←GaussianShiftedPartition.representative_spec n x.val,quotientTrace_mk_product]
  simp only [GaussianShiftedPartition.representative_spec]

theorem normalizedCubicUnitGauss_eq_gaussTwo (I:Ideal Eis)
    (hI:primaryGenerator I≠0) (hsq:Squarefree I) :
    normalizedCubicUnitGauss (primaryGenerator I)=gaussTwo I hI := by
  let n:=primaryGenerator I
  let:Finite (Eis⧸Ideal.span {n}):=finite_quotient_span hI
  let:Fintype (Eis⧸Ideal.span {n}):=Fintype.ofFinite _
  let e:=Ideal.quotEquivOfEq (primaryGenerator_spec I hI).1
  rw [normalizedCubicUnitGauss,cubicUnitGaussSum_full _ hI (primaryGenerator_spec I hI).2 1,
    tsum_fintype]
  change (∑x:Eis⧸Ideal.span {n},eisEmbedding (symbol (GaussianShiftedPartition.representative n x) n)*
    quotientTrace n hI (Ideal.Quotient.mk _ 1*x))/(‖eisEmbedding n‖:ℂ)=
    (∑x:Eis⧸Ideal.span {n},cubicRow I hI (e x)*quotientTrace n hI x)/(‖eisEmbedding n‖:ℂ)
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective x
  rw [Ideal.quotEquivOfEq_mk,cubicRow_eq_idealSymbol I hI hsq]
  have hc:n∣GaussianShiftedPartition.representative n (Ideal.Quotient.mk (Ideal.span {n}) a)-a:=
    gaussRep_mk_congr n a
  have hs:symbol a n=idealSymbol I a:=by
    unfold symbol
    rw [(primaryGenerator_spec I hI).1]
  rw [symbol_congr hc,hs,map_one,one_mul]

end CubicEisenstein

end

end OAI
end OAIOriginalModule0303

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.SquarefreeCoefficients
Source SHA256: 9715a7b8385bebefefe4e642be887838c5f95165608dd7f35458bad395e0d2d8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0304


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

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma primaryGenerator_squarefree_support (I:Ideal Eis) (hI:primaryGenerator I≠0)
    (hsq:Squarefree I) : primaryGenerator I=∏P∈primeSupport I,primaryPrime P := by
  have hI0:=primaryGenerator_ne_zero_ideal I hI
  have hn: (UniqueFactorizationMonoid.normalizedFactors I).Nodup:=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI0).mp hsq
  have hv:(primeSupport I).val=UniqueFactorizationMonoid.normalizedFactors I:=by
    simpa only [primeSupport, Multiset.toFinset_val] using hn.dedup
  unfold primaryGenerator
  rw [ite_eq_right hI0]
  change _=((primeSupport I).val.map primaryPrime).prod
  rw [hv]

lemma primaryPrime_isPrime_of_mem (I P:Ideal Eis) (hI:primaryGenerator I≠0)
    (hP:P∈primeSupport I) : Prime (primaryPrime P) := by
  have hp0:=primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP)
  have hs:=primaryPrime_spec P hp0
  let:P.IsMaximal:=hs.1
  apply (Ideal.span_singleton_prime hp0).mp
  rw [hs.2.2.1]
  infer_instance

lemma primaryPrime_support_coprime (I:Ideal Eis) (hI:primaryGenerator I≠0)
    (P:Ideal Eis) (hP:P∈primeSupport I) (Q:Ideal Eis) (hQ:Q∈primeSupport I) (hne:P≠Q) :
    IsCoprime (primaryPrime P) (primaryPrime Q) := by
  have hp:=primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))
  have hq:=primaryPrime_spec Q (primaryPrime_factor_ne_zero I Q hI (Multiset.mem_toFinset.mp hQ))
  let:P.IsMaximal:=hp.1
  let:Q.IsMaximal:=hq.1
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [hp.2.2.1,hq.2.2.1]
  exact Ideal.isCoprime_of_isMaximal hne

def infinityCoefficientScalar : ℂ := star (sourceResidualFourierCoefficient 1)

theorem infinityCoefficient_squarefree (I:Ideal Eis) (hI:primaryGenerator I≠0)
    (hsq:Squarefree I) :
    star (sourceResidualFourierCoefficient (primaryGenerator I))=
      infinityCoefficientScalar*
        star (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*gaussTwo I hI := by
  have hpr:∀P∈primeSupport I,lambda^2∣primaryPrime P-1:=by
    intro P hP
    exact (primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2
  have he:=sourceResidualFourierCoefficient_primary_product (primeSupport I) primaryPrime
    (fun P hP=>primaryPrime_isPrime_of_mem I P hI hP) hpr
    (primaryPrime_support_coprime I hI)
  rw [←primaryGenerator_squarefree_support I hI hsq,normalizedCubicUnitGauss_eq_gaussTwo I hI hsq] at he
  exact he

theorem infinityCoefficient_squarefree_cube (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) (hsq:Squarefree I) :
    star (sourceResidualFourierCoefficient (primaryGenerator I*(primaryGenerator J)^3))=
      infinityCoefficientScalar*(‖eisEmbedding (primaryGenerator J)‖:ℂ)*
        star (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*gaussTwo I hI := by
  rw [sourceResidualFourierCoefficient_primary_cube _ hJ (primaryGenerator_spec J hJ).2 _ hI,
    star_mul,infinityCoefficient_squarefree I hI hsq]
  simp only [Complex.star_def,Complex.conj_ofReal]
  ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

theorem sourceArithmeticResidue_valuation_ne_two (I P:Ideal Eis)
    (hI:primaryGenerator I≠0) (hP:P∈normalizedFactors I)
    (hS:sourceArithmeticResidue (primaryGenerator I)≠0) :
    (normalizedFactors I).count P%3≠2 := by
  have hI0:=primaryGenerator_ne_zero_ideal I hI
  have hprime:=prime_of_normalized_factor P hP
  let p:=primaryPrime P
  have hp0:p≠0:=primaryPrime_factor_ne_zero I P hI hP
  have hps:=primaryPrime_spec P hp0
  have hp:Prime p:=primaryPrime_isPrime_of_mem I P hI (Multiset.mem_toFinset.mpr hP)
  obtain ⟨J,hJ,hnot⟩:=(FiniteMultiplicity.of_prime_left hprime hI0).exists_eq_pow_mul_and_not_dvd
  have hgen:primaryGenerator I=p^(multiplicity P I)*primaryGenerator J:=by
    calc
      _=primaryGenerator (P^(multiplicity P I)*J):=congrArg primaryGenerator hJ
      _=p^(multiplicity P I)*primaryGenerator J:=by
        rw [primaryGenerator_mul,primaryGenerator_pow]
        have he:primaryGenerator P=p:=by
          rw [←hps.2.2.1,primaryGenerator_span p hp0 hps.2.2.2]
        rw [he]
  have hgJ:primaryGenerator J≠0:=by
    intro hz
    exact hI (by rw [hgen,hz,mul_zero])
  have hpd:¬p∣primaryGenerator J:=by
    intro hd
    apply hnot
    rw [Ideal.dvd_iff_le,←hps.2.2.1,←(primaryGenerator_spec J hgJ).1,
      Ideal.span_singleton_le_span_singleton]
    exact hd
  have hcount:=multiplicity_eq_count_normalizedFactors hprime.irreducible hI0
  rw [normalize_normalized_factor P hP] at hcount
  intro hc
  have hm:(multiplicity P I)%3=2:=by rwa [hcount]
  apply hS
  rw [hgen,mul_comm,sourceArithmeticResidue_prime_power_table p hp hps.2.2.2 _ hpd,
    hm]
  norm_num

def thetaSquarefreePart (I:Ideal Eis) : Ideal Eis :=
  ∏P∈(primeSupport I).filter (fun P=>(normalizedFactors I).count P%3=1),P

def thetaCubePart (I:Ideal Eis) : Ideal Eis :=
  ∏P∈primeSupport I,P^((normalizedFactors I).count P/3)

lemma thetaSquarefreePart_squarefree (I:Ideal Eis) : Squarefree (thetaSquarefreePart I) := by
  apply IdealMobiusDivisorSum.squarefree_support_product
  exact Finset.filter_subset _ _

lemma thetaParts_mul_cube (I:Ideal Eis) (hI:I≠0)
    (he:∀P∈normalizedFactors I,(normalizedFactors I).count P%3≠2) :
    thetaSquarefreePart I*thetaCubePart I^3=I := by
  rw [thetaSquarefreePart,Finset.prod_filter,thetaCubePart,←Finset.prod_pow,←Finset.prod_mul_distrib]
  calc
    _=∏P∈primeSupport I,P^((normalizedFactors I).count P):=by
      apply Finset.prod_congr rfl
      intro P hP
      have hp:=he P (Multiset.mem_toFinset.mp hP)
      have hm:(normalizedFactors I).count P%3=0 ∨ (normalizedFactors I).count P%3=1:=by omega
      rcases hm with hm|hm
      · rw [ite_eq_right (by omega),one_mul,←pow_mul]
        congr 1
        omega
      · rw [ite_eq_left hm,←pow_mul,←pow_succ']
        congr 1
        omega
    _=(normalizedFactors I).prod:=(Finset.prod_multiset_count (normalizedFactors I)).symm
    _=I:=Ideal.prod_normalizedFactors_eq_self hI

theorem sourceArithmeticResidue_squarefree_cube_support (I:Ideal Eis)
    (hI:primaryGenerator I≠0) (hS:sourceArithmeticResidue (primaryGenerator I)≠0) :
    Squarefree (thetaSquarefreePart I) ∧
    primaryGenerator (thetaSquarefreePart I)≠0 ∧
    primaryGenerator (thetaCubePart I)≠0 ∧
    thetaSquarefreePart I*thetaCubePart I^3=I := by
  have he:=thetaParts_mul_cube I (primaryGenerator_ne_zero_ideal I hI)
    (fun P hP=>sourceArithmeticResidue_valuation_ne_two I P hI hP hS)
  have hgen:primaryGenerator I=
      primaryGenerator (thetaSquarefreePart I)*(primaryGenerator (thetaCubePart I))^3:=by
    calc
      _=primaryGenerator (thetaSquarefreePart I*thetaCubePart I^3):=congrArg primaryGenerator he.symm
      _=_:=by rw [primaryGenerator_mul,primaryGenerator_pow]
  have hA:primaryGenerator (thetaSquarefreePart I)≠0:=by
    intro hz
    exact hI (by rw [hgen,hz,zero_mul])
  have hB:primaryGenerator (thetaCubePart I)≠0:=by
    intro hz
    exact hI (by rw [hgen,hz,zero_pow (by decide : (3:ℕ)≠0),mul_zero])
  exact ⟨thetaSquarefreePart_squarefree I,hA,hB,he⟩

theorem sourceFourier_squarefree_cube_support (I:Ideal Eis)
    (hI:primaryGenerator I≠0) (hS:sourceResidualFourierCoefficient (primaryGenerator I)≠0) :
    ∃A B:Ideal Eis,Squarefree A ∧ primaryGenerator A≠0 ∧ primaryGenerator B≠0 ∧ A*B^3=I := by
  have hs:sourceArithmeticResidue (primaryGenerator I)≠0:=by
    intro hz
    exact hS (by rw [sourceResidualFourierCoefficient,hz,mul_zero])
  exact ⟨thetaSquarefreePart I,thetaCubePart I,
    sourceArithmeticResidue_squarefree_cube_support I hI hs⟩

theorem sourceFourier_primary_zero_of_base_zero (hC:infinityCoefficientScalar=0)
    (n:Eis) (hprimary:lambda^2∣n-1) : sourceResidualFourierCoefficient n=0 := by
  have hn:n≠0:=primary_ne_zero n hprimary
  let I:Ideal Eis:=Ideal.span {n}
  have hgen:primaryGenerator I=n:=primaryGenerator_span n hn hprimary
  have hI:primaryGenerator I≠0:=by rwa [hgen]
  by_contra hT
  have hTI:sourceResidualFourierCoefficient (primaryGenerator I)≠0:=by rwa [hgen]
  obtain ⟨A,B,hA,hAg,hBg,hAB⟩:=sourceFourier_squarefree_cube_support I hI hTI
  have harg:primaryGenerator A*(primaryGenerator B)^3=n:=by
    have he:=congrArg primaryGenerator hAB
    simpa only [primaryGenerator_mul,primaryGenerator_pow,hgen] using he
  have he:=infinityCoefficient_squarefree_cube A B hAg hBg hA
  rw [harg,hC,zero_mul,zero_mul,zero_mul] at he
  exact hT (star_eq_zero.mp he)

end

section
open Filter
open scoped BigOperators Classical Topology

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma unramifiedGaussResidue_eq_of_initial_eq (h k:Eis)
    (he:∀s:ℂ,4<s.re→0<s.im→
      unramifiedCubicGaussSeries s h=unramifiedCubicGaussSeries s k) :
    unramifiedGaussResidue h=unramifiedGaussResidue k := by
  have hh:=unramifiedGaussResidue_of_initial_relation h k 0 (fun _=>1) (fun _=>0)
    (fun _ _=>analyticAt_const) (fun _ _=>analyticAt_const)
    continuousAt_const continuousAt_const (fun s hs hi=>by simpa using he s hs hi)
  simpa only [one_mul,zero_mul,add_zero] using hh

theorem unramifiedGaussResidue_neg (h:Eis) :
    unramifiedGaussResidue (-h)=unramifiedGaussResidue h :=
  unramifiedGaussResidue_eq_of_initial_eq _ _ (fun s _ _=>unramifiedCubicGaussSeries_neg s h)

theorem unramifiedGaussResidue_lambda_pow (h:Eis) (n:ℕ) :
    unramifiedGaussResidue (h*lambda^n)=
      unramifiedGaussResidue (h*lambda^(n%3)) :=
  unramifiedGaussResidue_eq_of_initial_eq _ _ (fun s _ _=>unramifiedCubicGaussSeries_lambda_pow s h n)

theorem unramifiedGaussResidue_lambda_cube (h:Eis) :
    unramifiedGaussResidue (h*lambda^3)=unramifiedGaussResidue h := by
  simpa using unramifiedGaussResidue_lambda_pow h 3

theorem unramifiedGaussResidue_nine_family (h:Eis) (u:Eisˣ) (n:ℕ) :
    ∃j k:Fin 3,unramifiedGaussResidue (h*(9*((u:Eis)*lambda^n)))=
      unramifiedGaussResidue (h*omega^j.val*lambda^k.val) := by
  obtain ⟨j,k,hjk⟩:=unramifiedCubicGaussSeries_nine_family h u n
  exact ⟨j,k,unramifiedGaussResidue_eq_of_initial_eq _ _ (fun s _ _=>hjk s)⟩

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def ramifiedResidueFamilyMass (h:Eis) : ℝ :=
  ∑a:Fin 3×Fin 3,‖unramifiedGaussResidue (h*omega^a.1.val*lambda^a.2.val)‖

lemma ramifiedResidueFamilyMass_nonneg (h:Eis) : 0≤ramifiedResidueFamilyMass h :=
  Finset.sum_nonneg (fun _ _=>norm_nonneg _)

lemma unramifiedGaussResidue_family_norm_le (h:Eis) (j k:Fin 3) :
    ‖unramifiedGaussResidue (h*omega^j.val*lambda^k.val)‖≤ramifiedResidueFamilyMass h := by
  unfold ramifiedResidueFamilyMass
  exact Finset.single_le_sum (a:=(j,k)) (s:=Finset.univ)
    (f:=fun a:Fin 3×Fin 3=>‖unramifiedGaussResidue (h*omega^a.1.val*lambda^a.2.val)‖)
    (fun _ _=>norm_nonneg _) (Finset.mem_univ (j,k))

lemma unramifiedGaussResidue_nine_norm_le (h:Eis) (u:Eisˣ) (n:ℕ) :
    ‖unramifiedGaussResidue (h*(9*((u:Eis)*lambda^n)))‖≤ramifiedResidueFamilyMass h := by
  obtain ⟨j,k,hjk⟩:=unramifiedGaussResidue_nine_family h u n
  rw [hjk]
  exact unramifiedGaussResidue_family_norm_le h j k

theorem unramifiedGaussResidue_unit_lambda_family (u:Eisˣ) (n:ℕ) :
    ∃j k:Fin 3,unramifiedGaussResidue ((u:Eis)*lambda^n)=
      unramifiedGaussResidue (omega^j.val*lambda^k.val) := by
  obtain ⟨j,hj⟩:=unit_eq_sign_omega u
  refine ⟨j,⟨n%3,Nat.mod_lt _ (by decide)⟩,?_⟩
  rcases hj with hj|hj
  · rw [hj,unramifiedGaussResidue_lambda_pow]
  · rw [hj,neg_mul,unramifiedGaussResidue_neg,unramifiedGaussResidue_lambda_pow]

lemma unramifiedGaussResidue_unit_lambda_norm_le (u:Eisˣ) (n:ℕ) :
    ‖unramifiedGaussResidue ((u:Eis)*lambda^n)‖≤ramifiedResidueFamilyMass 1 := by
  obtain ⟨j,k,hjk⟩:=unramifiedGaussResidue_unit_lambda_family u n
  rw [hjk]
  simpa only [one_mul] using unramifiedGaussResidue_family_norm_le 1 j k

lemma ramifiedResidueFamilyMass_unit_lambda_le (u:Eisˣ) (n:ℕ) :
    ramifiedResidueFamilyMass ((u:Eis)*lambda^n)≤9*ramifiedResidueFamilyMass 1 := by
  calc
    _≤∑a:Fin 3×Fin 3,ramifiedResidueFamilyMass 1:=by
      apply Finset.sum_le_sum
      intro a ha
      let v:Eisˣ:=u*ramifiedOmegaUnit^a.1.val
      have he:((u:Eis)*lambda^n)*omega^a.1.val*lambda^a.2.val=
          (v:Eis)*lambda^(n+a.2.val):=by
        simp only [v,Units.val_mul,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,pow_add]
        ring
      rw [he]
      exact unramifiedGaussResidue_unit_lambda_norm_le v _
    _=_:=by simp

theorem sourceArithmeticResidue_family_bound (h:Eis) (hh:h≠0) :
    ‖sourceArithmeticResidue h‖≤
      ((∑i:PrincipalRamifiedIndex h,‖principalRamifiedWeight h i (4/3)‖)+3)*
        ramifiedResidueFamilyMass h/(4*(9*Real.sqrt 3/2)) := by
  have hM:=ramifiedResidueFamilyMass_nonneg h
  have hden:0<4*(9*Real.sqrt 3/2):=by positivity
  rw [sourceArithmeticResidue_eq_ramified_table h hh]
  split_ifs with hphase
  · rw [norm_div,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (show 0<(9*Real.sqrt 3/2:ℝ) by positivity)]
    apply div_le_div_of_nonneg_right _ hden.le
    calc
      _≤‖∑i:PrincipalRamifiedIndex h,principalRamifiedWeight h i (4/3)*
          unramifiedGaussResidue (principalRamifiedIndex h i)‖+
          ‖(3:ℂ)*unramifiedGaussResidue (9*h)‖:=norm_add_le _ _
      _≤(∑i:PrincipalRamifiedIndex h,‖principalRamifiedWeight h i (4/3)‖)*
          ramifiedResidueFamilyMass h+3*ramifiedResidueFamilyMass h:=by
        apply add_le_add
        · calc
            _≤∑i:PrincipalRamifiedIndex h,‖principalRamifiedWeight h i (4/3)*
                unramifiedGaussResidue (principalRamifiedIndex h i)‖:=norm_sum_le _ _
            _≤∑i:PrincipalRamifiedIndex h,‖principalRamifiedWeight h i (4/3)‖*
                ramifiedResidueFamilyMass h:=by
              apply Finset.sum_le_sum
              intro i hi
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left
                (unramifiedGaussResidue_nine_norm_le h i.1 (i.2.val+2)) (norm_nonneg _)
            _=_:=by rw [Finset.sum_mul]
        · rw [norm_mul,Complex.norm_ofNat]
          have hb:=unramifiedGaussResidue_nine_norm_le h (1:Eisˣ) 0
          simp only [Units.val_one,pow_zero,mul_one] at hb
          simpa only [mul_comm 9 h] using mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤3)
      _=_:=by ring
  · rw [norm_zero]
    positivity

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def ramifiedDecayRatio : ℝ := (3:ℝ)^(-(1/3:ℝ))

lemma ramifiedDecayRatio_pos : 0<ramifiedDecayRatio :=
  Real.rpow_pos_of_pos (by norm_num) _

lemma ramifiedDecayRatio_lt_one : ramifiedDecayRatio<1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

lemma explicitRamifiedCoefficient_norm_le (h:Eis) (u:Eisˣ) (n:ℕ) :
    ‖explicitRamifiedCoefficient h u n‖≤(3^n:ℕ) := by
  unfold explicitRamifiedCoefficient
  split_ifs with hd
  · dsimp only
    split_ifs <;> simp [residueAdditive,breveE_norm]
  · simp

lemma ramifiedWeight_norm_scalar (n:ℕ) :
    ‖((3^n:ℕ):ℂ)^(-(4/3:ℂ))‖*(3^n:ℕ)=ramifiedDecayRatio^n := by
  have ha:0<(3:ℝ)^n:=pow_pos (by norm_num) _
  have hn:‖((3:ℂ)^n)^(-(4/3:ℂ))‖=((3:ℝ)^n)^(-(4/3:ℝ)):=by
    have he:=Complex.norm_cpow_eq_rpow_re_of_pos ha (-(4/3:ℂ))
    have hre:(-(4/3:ℂ)).re=-(4/3:ℝ):=by norm_num
    rw [hre] at he
    simpa only [Complex.ofReal_pow,Complex.ofReal_ofNat] using he
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  rw [hn]
  calc
    ((3:ℝ)^n)^(-(4/3:ℝ))*(3:ℝ)^n=
        ((3:ℝ)^n)^(-(4/3:ℝ))*((3:ℝ)^n)^(1:ℝ):=by rw [Real.rpow_one]
    _=((3:ℝ)^n)^(-(1/3:ℝ)):=by
      rw [←Real.rpow_add ha]
      congr 1
      norm_num
    _=(3:ℝ)^((n:ℝ)*(-(1/3:ℝ))):=(Real.rpow_natCast_mul (by norm_num) n _).symm
    _=(3:ℝ)^((-(1/3:ℝ))*(n:ℝ)):=by rw [mul_comm]
    _=ramifiedDecayRatio^n:=by
      rw [Real.rpow_mul (by norm_num),Real.rpow_natCast]
      rfl

lemma principalRamifiedWeight_norm_le (h:Eis) (i:PrincipalRamifiedIndex h) :
    ‖principalRamifiedWeight h i (4/3)‖≤ramifiedDecayRatio^(i.2.val+2) := by
  unfold principalRamifiedWeight
  rw [norm_mul]
  calc
    _≤‖((3^(i.2.val+2):ℕ):ℂ)^(-(4/3:ℂ))‖*(3^(i.2.val+2):ℕ):=
      mul_le_mul_of_nonneg_left (explicitRamifiedCoefficient_norm_le h i.1 _) (norm_nonneg _)
    _=_:=ramifiedWeight_norm_scalar _

theorem principalRamifiedWeight_sum_norm_le (h:Eis) :
    (∑i:PrincipalRamifiedIndex h,‖principalRamifiedWeight h i (4/3)‖)≤
      6*ramifiedDecayRatio^2/(1-ramifiedDecayRatio) := by
  have ht0:=ramifiedDecayRatio_pos.le
  have ht1:=ramifiedDecayRatio_lt_one
  have hfin:(∑n:Fin (ramifiedFrequencyBound h+1),ramifiedDecayRatio^(n.val+2))≤
      ramifiedDecayRatio^2/(1-ramifiedDecayRatio):=by
    rw [Fin.sum_univ_eq_sum_range (fun n:ℕ=>ramifiedDecayRatio^(n+2))]
    simp_rw [pow_add,mul_comm _ (ramifiedDecayRatio^2)]
    rw [←Finset.mul_sum]
    have hs: (∑n∈Finset.range (ramifiedFrequencyBound h+1),ramifiedDecayRatio^n)≤
        (1-ramifiedDecayRatio)⁻¹:=by
      rw [←tsum_geometric_of_lt_one ht0 ht1]
      exact (summable_geometric_of_lt_one ht0 ht1).sum_le_tsum _ (fun n _=>pow_nonneg ht0 n)
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hs (sq_nonneg ramifiedDecayRatio)
  calc
    _≤∑i:PrincipalRamifiedIndex h,ramifiedDecayRatio^(i.2.val+2):=
      Finset.sum_le_sum (fun i _=>principalRamifiedWeight_norm_le h i)
    _=(6:ℝ)*(∑n:Fin (ramifiedFrequencyBound h+1),ramifiedDecayRatio^(n.val+2)):=by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      have hc:Fintype.card Eisˣ=6:=by
        simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six
      rw [hc]
      norm_num
    _≤6*(ramifiedDecayRatio^2/(1-ramifiedDecayRatio)):=mul_le_mul_of_nonneg_left hfin (by norm_num)
    _=_:=by ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def ramifiedSourceFamilyConstant : ℝ :=
  (6*ramifiedDecayRatio^2/(1-ramifiedDecayRatio)+3)/(4*(9*Real.sqrt 3/2))

lemma ramifiedSourceFamilyConstant_nonneg : 0≤ramifiedSourceFamilyConstant := by
  have ht:0<1-ramifiedDecayRatio:=sub_pos.mpr ramifiedDecayRatio_lt_one
  unfold ramifiedSourceFamilyConstant
  positivity

theorem sourceArithmeticResidue_nine_family_bound (h:Eis) (hh:h≠0) :
    ‖sourceArithmeticResidue h‖≤ramifiedSourceFamilyConstant*ramifiedResidueFamilyMass h := by
  have hm:=ramifiedResidueFamilyMass_nonneg h
  refine (sourceArithmeticResidue_family_bound h hh).trans ?_
  have hw:(∑i:PrincipalRamifiedIndex h,‖principalRamifiedWeight h i (4/3)‖)+3≤
      6*ramifiedDecayRatio^2/(1-ramifiedDecayRatio)+3:=by
    linarith [principalRamifiedWeight_sum_norm_le h]
  calc
    _≤(6*ramifiedDecayRatio^2/(1-ramifiedDecayRatio)+3)*
        ramifiedResidueFamilyMass h/(4*(9*Real.sqrt 3/2)):=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hw hm) (by positivity)
    _=ramifiedSourceFamilyConstant*ramifiedResidueFamilyMass h:=by
      unfold ramifiedSourceFamilyConstant
      ring

theorem sourceArithmeticResidue_unit_lambda_bound (u:Eisˣ) (n:ℕ) :
    ‖sourceArithmeticResidue ((u:Eis)*lambda^n)‖≤
      9*ramifiedSourceFamilyConstant*ramifiedResidueFamilyMass 1 := by
  refine (sourceArithmeticResidue_nine_family_bound _ (ramifiedElement_ne_zero u n)).trans ?_
  have he:=mul_le_mul_of_nonneg_left (ramifiedResidueFamilyMass_unit_lambda_le u n)
    ramifiedSourceFamilyConstant_nonneg
  convert he using 1 ; ring

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def extraPeriodWitness : levelThree := by
  let M:SL(2,Eis):=⟨!![1+3*omega,3*omega^2;-3,1-3*omega],by
    rw [Matrix.det_fin_two_of]
    ring⟩
  refine ⟨M,levelThree_of_entries M ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨omega,by change 1+3*omega-1=3*omega;ring⟩
  · exact ⟨omega^2,by change 3*omega^2-0=3*omega^2;ring⟩
  · exact ⟨-1,by change -3-(0:Eis)=3*(-1);ring⟩
  · exact ⟨-omega,by change 1-3*omega-1=3*(-omega);ring⟩

def rationalLowerMinusThree : SL(2,ℤ):=⟨!![1,0;-3,1],by simp [Matrix.det_fin_two]⟩

lemma extraPeriodWitness_factor :
    integralComplexMatrix (extraPeriodWitness:SL(2,Eis))=
      complexTranslation (-eisEmbedding omega)*
        integralComplexMatrix (rationalEmbedding rationalLowerMinusThree)*
        complexTranslation (eisEmbedding omega) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, integralComplexMatrix_apply,
    rationalEmbedding, Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;>
    simp [extraPeriodWitness, rationalLowerMinusThree, complexTranslation, map_ofNat] <;> ring

lemma extraPeriodWitness_character : complexCharacter extraPeriodWitness=eisEmbedding omega := by
  change eisEmbedding (symbol (-3) (1+3*omega))=eisEmbedding omega
  apply congrArg eisEmbedding
  have hp:lambda^2∣(1+3*omega)-1:=lambda_sq_dvd_three.trans ⟨omega,by ring⟩
  rw [symbol_neg_numerator _ _ hp]
  have he:=ramified_symbol_at_omega (-(ramifiedOmegaUnit^2)) 2 2
    (Or.inr (by simp only [Units.val_neg,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val]))
  have hl:lambda^2=-3*omega:=by
    change (omega-1)^2=-3*omega
    linear_combination ramified_omega_relation
  have hnum:((-(ramifiedOmegaUnit^2):Eisˣ):Eis)*lambda^2=3:=by
    simp only [Units.val_neg,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val]
    rw [hl]
    calc
      _=3*omega^3:=by ring
      _=3:=by rw [omega_primitive.pow_eq_one];ring
  rw [hnum] at he
  have hw:omega^(2*2)=omega:=by
    norm_num only [Nat.reduceMul]
    calc
      omega^4=omega^3*omega:=by ring
      _=omega:=by rw [omega_primitive.pow_eq_one,one_mul]
  exact he.trans hw

lemma extraPeriodWitness_character_ne_one : complexCharacter extraPeriodWitness≠1 := by
  rw [extraPeriodWitness_character]
  intro he
  exact omega_primitive.ne_one (by decide) (eisEmbedding_injective (by simpa only [map_one] using he))

theorem cubicSource_not_eisenstein_periodic :
    ¬(∀a:Eis,∀w:HyperbolicSpace,
      cubicSourceResidualFunction (complexTranslation (eisEmbedding a) • w)=
        cubicSourceResidualFunction w) := by
  intro hperiod
  apply cubicSourceResidualFunction_ne_zero
  funext w
  have hneg (u:HyperbolicSpace):
      cubicSourceResidualFunction (complexTranslation (-eisEmbedding omega) • u)=
        cubicSourceResidualFunction u:=by
    simpa only [map_neg] using hperiod (-omega) u
  have hinv:cubicSourceResidualFunction
      (integralComplexMatrix (extraPeriodWitness:SL(2,Eis)) • w)=cubicSourceResidualFunction w:=by
    rw [extraPeriodWitness_factor,mul_smul,mul_smul,hneg,
      cubicSourceResidualFunction_rational_invariant,hperiod]
  have hchar:=cubicSourceResidualFunction_automorphy (sourceLevelInclusion extraPeriodWitness) w
  change cubicSourceResidualFunction (integralComplexMatrix (extraPeriodWitness:SL(2,Eis)) • w)=
    levelTwoComplexCharacter ⟨(extraPeriodWitness:SL(2,Eis)),levelThree_le_levelTwo extraPeriodWitness.property⟩*
      cubicSourceResidualFunction w at hchar
  rw [levelTwoComplexCharacter_restrict] at hchar
  change cubicSourceResidualFunction (integralComplexMatrix (extraPeriodWitness:SL(2,Eis)) • w)=
    complexCharacter extraPeriodWitness*cubicSourceResidualFunction w at hchar
  rw [hinv] at hchar
  have hz:(complexCharacter extraPeriodWitness-1)*cubicSourceResidualFunction w=0:=by
    linear_combination -hchar
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr extraPeriodWitness_character_ne_one)

end CubicEisenstein

end

end OAI
end OAIOriginalModule0304

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.SourceMellinInversion
Source SHA256: 980fda0a1173f92dabc089e7f002c889b858db6bda4e8c07c6fcd29c184ea4e4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0305


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
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma source_period_of_three_supported
    (hs:∀h:Eis,¬(3:Eis)∣h→sourceResidualFourierCoefficient h=0)
    (a:Eis) (z:ℂ) (v:ℝ) (hv:0<v) :
    cubicSourceResidualFunction (upperPoint (z+eisEmbedding a) v hv)=
      cubicSourceResidualFunction (upperPoint z v hv) := by
  rw [cubicSourceResidualFunction_bessel,cubicSourceResidualFunction_bessel]
  apply congrArg (fun t:ℂ=>(3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ)+t)
  apply tsum_congr
  intro h
  by_cases hd:(3:Eis)∣h
  · obtain ⟨b,rfl⟩:=hd
    have hp:ShortDraftTrace.breveE (cuspFrequency (3*b)*eisEmbedding a)=1:=by
      have he:cuspFrequency (3*b)*eisEmbedding a=cuspFrequency b*(3*eisEmbedding a):=by
        unfold cuspFrequency
        rw [map_mul,map_ofNat]
        ring
      rw [he,cuspFrequency_period]
    rw [mul_add,AddChar.map_add_eq_mul,hp,mul_one]
  · rw [hs h hd]
    by_cases hh:h=0 <;> simp [hh]

theorem exists_source_coefficient_not_three :
    ∃h:Eis,¬(3:Eis)∣h ∧ sourceResidualFourierCoefficient h≠0 := by
  by_contra hn
  have hs:∀h:Eis,¬(3:Eis)∣h→sourceResidualFourierCoefficient h=0:=by
    intro h hh
    by_contra hne
    exact hn ⟨h,hh,hne⟩
  apply cubicSource_not_eisenstein_periodic
  intro a w
  obtain ⟨z,v,hv,rfl⟩:=upperPoint_surjective w
  rw [complexTranslation_action]
  exact source_period_of_three_supported hs a z v hv

theorem exists_sourceArithmeticResidue_not_three :
    ∃h:Eis,¬(3:Eis)∣h ∧ sourceArithmeticResidue h≠0 := by
  obtain ⟨h,hh,ht⟩:=exists_source_coefficient_not_three
  refine ⟨h,hh,?_⟩
  intro hz
  apply ht
  simp only [sourceResidualFourierCoefficient,hz,mul_zero]

end CubicEisenstein

namespace CompletedGauss

section
open Filter MeasureTheory
open scoped Classical BigOperators Topology FourierTransform SchwartzMap ContDiff

lemma compactMellin_vertical_integrable (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V) (σ : ℝ) :
    Complex.VerticalIntegrable (mellin V) σ := by
  have hc : HasCompactSupport (CubicReflectionKernel.mellinLogFamily V σ) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (CubicReflectionKernel.mellinLogFamily_support V a b ha hsupp σ)
  have hd : ContDiff ℝ ∞ (CubicReflectionKernel.mellinLogFamily V σ) :=
    (CubicReflectionKernel.mellinLogFamily_smooth V hV).comp (contDiff_const.prodMk contDiff_id)
  let f : 𝓢(ℝ,ℂ) := hc.toSchwartzMap hd
  have hf : Integrable (fun t : ℝ=>(𝓕 f) (t/(2*Real.pi))) := by
    simpa only [div_eq_mul_inv] using
      (𝓕 f).integrable.comp_mul_right' (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  change Integrable (fun t : ℝ=>mellin V ((σ:ℂ)+t*Complex.I))
  have hfcoe : (f:ℝ→ℂ)=CubicReflectionKernel.mellinLogFamily V σ := rfl
  simpa only [CubicReflectionKernel.mellin_eq_logFamily_fourier,
    SchwartzMap.fourier_coe,hfcoe] using hf

theorem compactMellin_inversion (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (σ x : ℝ) (hx : 0<x) :
    V x=(1/(2*Real.pi):ℂ)*∫t : ℝ,
      (x:ℂ)^(-((σ:ℂ)+t*Complex.I))*mellin V ((σ:ℂ)+t*Complex.I) := by
  have hm := mellinInv_mellin_eq σ V hx
    (CubicReflectionKernel.compact_source_mellin_convergent V a b ha hsupp hV σ)
    (compactMellin_vertical_integrable V a b ha hsupp hV σ) hV.continuous.continuousAt
  simpa only [mellinInv,smul_eq_mul,Complex.real_smul,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_ofNat] using hm.symm

end

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

lemma positive_cpow_vertical_norm (r σ t : ℝ) (hr : 0<r) :
    ‖(r:ℂ)^((σ:ℂ)+t*Complex.I)‖=r^σ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp

lemma positive_cpow_negative_vertical_norm (r σ t : ℝ) (hr : 0<r) :
    ‖(r:ℂ)^(-((σ:ℂ)+t*Complex.I))‖=r^(-σ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp

lemma positive_cpow_vertical_continuous (r σ : ℝ) (hr : 0<r) :
    Continuous (fun t : ℝ=>(r:ℂ)^((σ:ℂ)+t*Complex.I)) := by
  let : NeZero (r:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hr.ne'⟩
  exact (_root_.continuous_const_cpow (r:ℂ)).comp (by fun_prop)

lemma positive_cpow_negative_vertical_continuous (r σ : ℝ) (hr : 0<r) :
    Continuous (fun t : ℝ=>(r:ℂ)^(-((σ:ℂ)+t*Complex.I))) := by
  let : NeZero (r:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hr.ne'⟩
  exact (_root_.continuous_const_cpow (r:ℂ)).comp (by fun_prop)

lemma vertical_power_mul_integrable (M : ℝ→ℂ) (hM : Integrable M)
    (r σ : ℝ) (hr : 0<r) :
    Integrable (fun t : ℝ=>(r:ℂ)^((σ:ℂ)+t*Complex.I)*M t) := by
  apply (hM.norm.const_mul (r^σ)).mono'
    ((positive_cpow_vertical_continuous r σ hr).aestronglyMeasurable.mul hM.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun t=>by simp only [Pi.mul_apply,norm_mul,positive_cpow_vertical_norm r σ t hr,le_refl])

lemma weighted_vertical_power_integrable (M : ℝ→ℂ) (hM : Integrable M)
    (r σ : ℝ) (hr : 0<r) (c : ℂ) :
    Integrable (fun t : ℝ=>c*(r:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t) := by
  apply (hM.norm.const_mul (‖c‖*r^(-σ))).mono'
    ((continuous_const.mul (positive_cpow_negative_vertical_continuous r σ hr)).aestronglyMeasurable.mul hM.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun t=>by
    simp only [Pi.mul_apply,norm_mul,positive_cpow_negative_vertical_norm r σ t hr,le_refl])

lemma weighted_vertical_power_integral_norm (M : ℝ→ℂ) (r σ : ℝ) (hr : 0<r) (c : ℂ) :
    (∫t : ℝ,‖c*(r:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t‖)=
      (‖c‖*r^(-σ))*(∫t : ℝ,‖M t‖) := by
  simp only [norm_mul,positive_cpow_negative_vertical_norm r σ _ hr,integral_const_mul]

theorem weighted_vertical_sum_integral {α : Type*} [Countable α]
    (r : α→ℝ) (hr : ∀i,0<r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ)))
    (M : ℝ→ℂ) (hM : Integrable M) :
    (∑' i,∫t : ℝ,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t)=
      ∫t : ℝ,(∑' i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I)))*M t := by
  have hi (i : α) := weighted_vertical_power_integrable M hM (r i) σ (hr i) (c i)
  have hs : Summable (fun i=>∫t : ℝ,‖c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t‖) := by
    simp only [weighted_vertical_power_integral_norm M _ σ (hr _) _]
    exact hc.mul_right _
  rw [integral_tsum_of_summable_integral_norm hi hs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t=>tsum_mul_right)

lemma positive_quotient_cpow_neg (r X : ℝ) (hr : 0<r) (hX : 0<X) (s : ℂ) :
    ((r/X:ℝ):ℂ)^(-s)=(r:ℂ)^(-s)*(X:ℂ)^s := by
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg hr.le hX.le,
    Complex.cpow_neg,Complex.cpow_neg,div_inv_eq_mul]

theorem weightedMellin_inversion {α : Type*} [Countable α]
    (r : α→ℝ) (hr : ∀i,0<r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ)))
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) :
    (∑'i,c i*V (r i/X))=(1/(2*Real.pi):ℂ)*∫t : ℝ,
      mellin V ((σ:ℂ)+t*Complex.I)*(X:ℂ)^((σ:ℂ)+t*Complex.I)*
        (∑'i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))) := by
  let M : ℝ→ℂ := fun t=>(X:ℂ)^((σ:ℂ)+t*Complex.I)*mellin V ((σ:ℂ)+t*Complex.I)
  have hM : Integrable M := vertical_power_mul_integrable _
    (compactMellin_vertical_integrable V a b ha hsupp hV σ) X σ hX
  have hi (i : α) : c i*V (r i/X)=(1/(2*Real.pi):ℂ)*
      ∫t : ℝ,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t := by
    rw [compactMellin_inversion V a b ha hsupp hV σ _ (div_pos (hr i) hX)]
    rw [←mul_assoc,mul_comm (c i),mul_assoc,←integral_const_mul]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t=>by
      dsimp only
      rw [positive_quotient_cpow_neg _ _ (hr i) hX]
      dsimp only [M]
      ring)
  simp_rw [hi]
  rw [tsum_mul_left,weighted_vertical_sum_integral r hr c σ hc M hM]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t=>by dsimp only [M];ring)

end CompletedGauss

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CompletedGauss

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma angularFactor_norm_le_one (a : ActualEisensteinCubic.O) : ‖FiniteGaussPhase.angularFactor a‖≤1 := by
  by_cases ha : a=0
  · subst a; simp [FiniteGaussPhase.angularFactor]
  · exact (FiniteGaussPhase.norm_angularFactor a ha).le

lemma cubicRow_norm_le_one (I : Ideal ActualEisensteinCubic.O) (hI : primaryGenerator I≠0) (x : ActualEisensteinCubic.O⧸I) :
    ‖cubicRow I hI x‖≤1 := by
  unfold cubicRow
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro i hi; exact norm_nonneg _
  · intro i hi
    exact FiniteRayExpansion.norm_char_le_one _ _

lemma gaussTwo_norm_le_sqrt (I : Ideal ActualEisensteinCubic.O) (hI : primaryGenerator I≠0) :
    ‖gaussTwo I hI‖≤Real.sqrt (Ideal.absNorm I:ℝ) := by
  let n := primaryGenerator I
  let : Finite (ActualEisensteinCubic.O⧸Ideal.span {n}) := finite_quotient_span hI
  let : Fintype (ActualEisensteinCubic.O⧸Ideal.span {n}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (primaryGenerator_spec I hI).1
  let ψ := eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates n hI
  have hN : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h=>primaryGenerator_ne_zero_ideal I hI (Ideal.absNorm_eq_zero_iff.mp h))
  have hn : ‖eisEmbedding n‖=Real.sqrt (Ideal.absNorm I:ℝ) := primaryGenerator_norm I hI
  have hsum : ‖∑x : ActualEisensteinCubic.O⧸Ideal.span {n},cubicRow I hI (e x)*ψ x‖≤(Ideal.absNorm I:ℝ) := by
    calc
      _≤∑x : ActualEisensteinCubic.O⧸Ideal.span {n},‖cubicRow I hI (e x)*ψ x‖ := norm_sum_le _ _
      _≤∑_x : ActualEisensteinCubic.O⧸Ideal.span {n},(1:ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [norm_mul,AddChar.norm_apply,mul_one]
        exact cubicRow_norm_le_one I hI (e x)
      _=(Ideal.absNorm I:ℝ) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
        congr 1
        rw [←Nat.card_eq_fintype_card,←Submodule.cardQuot_apply,←Ideal.absNorm_apply,
          (primaryGenerator_spec I hI).1]
  change ‖(∑x : ActualEisensteinCubic.O⧸Ideal.span {n},cubicRow I hI (e x)*ψ x)/(‖eisEmbedding n‖:ℂ)‖≤_
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),hn]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hN)).mpr
  simpa only [Real.mul_self_sqrt hN.le] using hsum

lemma columnWeight_div_sqrt_norm_le_one (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1) (I : Ideal ActualEisensteinCubic.O) :
    ‖columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I:ℝ):ℂ)‖≤1 := by
  by_cases hI : Squarefree I ∧ primaryGenerator I≠0
  · have hN : 0<(Ideal.absNorm I:ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h=>primaryGenerator_ne_zero_ideal I hI.2 (Ideal.absNorm_eq_zero_iff.mp h))
    rw [columnWeight_eq Ψ I hI.1 hI.2,norm_div,norm_mul,norm_mul,norm_star,
      FiniteGaussPhase.norm_angularFactor _ hI.2,one_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    apply (div_le_one (Real.sqrt_pos.mpr hN)).mpr
    exact (mul_le_of_le_one_right (norm_nonneg _) (hΨ _)).trans (gaussTwo_norm_le_sqrt I hI.2)
  · simp only [columnWeight,squarefreeGaussCoefficient,dite_eq_right hI,zero_mul,zero_div,norm_zero,zero_le_one]

lemma cubeWeight_norm_le_one (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1) (I : Ideal ActualEisensteinCubic.O) :
    ‖cubeWeight Ψ I‖≤1 := by
  by_cases hI : I=0
  · subst I; simp
  have hN : (1:ℝ)≤(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h=>hI (Ideal.absNorm_eq_zero_iff.mp h))
  have hn : 0<(Ideal.absNorm I:ℝ) := lt_of_lt_of_le zero_lt_one hN
  change ‖star (FiniteGaussPhase.angularFactor (primaryGenerator I))^3*
    Ψ (primaryGenerator I)^3/(Ideal.absNorm I:ℂ)‖≤1
  rw [norm_div,norm_mul,norm_pow,norm_star,norm_pow,Complex.norm_natCast]
  apply (div_le_one hn).mpr
  apply le_trans _ hN
  calc
    _≤(1:ℝ)*1 := mul_le_mul
      (pow_le_one₀ (norm_nonneg _) (angularFactor_norm_le_one _))
      (pow_le_one₀ (norm_nonneg _) (hΨ _)) (pow_nonneg (norm_nonneg _) _) zero_le_one
    _=1 := one_mul _

end

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

section
open ActualEisensteinCubic CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

abbrev CompletedMellinIndex := NonzeroIdeal×NonzeroIdeal

def completedMellinLength (p : CompletedMellinIndex) : ℝ :=
  (Ideal.absNorm p.1.1:ℝ)*(Ideal.absNorm p.2.1:ℝ)^3

def completedMellinCoefficient (Ψ : ActualEisensteinCubic.O→*ℂ) (p : CompletedMellinIndex) : ℂ :=
  columnWeight Ψ p.1.1/(Real.sqrt (Ideal.absNorm p.1.1:ℝ):ℂ)*cubeWeight Ψ p.2.1

lemma nonzeroIdeal_norm_pos (I : NonzeroIdeal) : 0<(Ideal.absNorm I.1:ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (fun h=>I.2 (Ideal.absNorm_eq_zero_iff.mp h))

lemma completedMellinLength_pos (p : CompletedMellinIndex) : 0<completedMellinLength p :=
  mul_pos (nonzeroIdeal_norm_pos p.1) (pow_pos (nonzeroIdeal_norm_pos p.2) 3)

lemma completedMellinCoefficient_norm_le_one (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (p : CompletedMellinIndex) : ‖completedMellinCoefficient Ψ p‖≤1 := by
  rw [completedMellinCoefficient,norm_mul]
  exact (mul_le_mul_of_nonneg_right (columnWeight_div_sqrt_norm_le_one Ψ hΨ p.1.1)
    (norm_nonneg _)).trans (by simpa only [one_mul] using cubeWeight_norm_le_one Ψ hΨ p.2.1)

lemma nonzeroIdeal_norm_rpow_summable (σ : ℝ) (hσ : 1<σ) :
    Summable (fun I : NonzeroIdeal=>(Ideal.absNorm I.1:ℝ)^(-σ)) := by
  have h := (fullIdealWeight_summable_norm (σ:ℂ) (by simpa using hσ)).subtype (fun I=>I≠0)
  apply h.congr
  intro I
  change ‖fullIdealWeight (σ:ℂ) I.1‖=(Ideal.absNorm I.1:ℝ)^(-σ)
  rw [fullIdealWeight,ite_eq_right I.2]
  simpa only [Complex.neg_re,Complex.ofReal_re,Complex.ofReal_natCast] using
    (Complex.norm_cpow_eq_rpow_re_of_pos (nonzeroIdeal_norm_pos I) (-(σ:ℂ)))

lemma completedMellinLength_rpow (p : CompletedMellinIndex) (σ : ℝ) :
    (completedMellinLength p)^(-σ)=
      (Ideal.absNorm p.1.1:ℝ)^(-σ)*(Ideal.absNorm p.2.1:ℝ)^(-(3*σ)) := by
  rw [completedMellinLength,Real.mul_rpow (nonzeroIdeal_norm_pos p.1).le
    (pow_nonneg (nonzeroIdeal_norm_pos p.2).le _),←Real.rpow_natCast_mul (nonzeroIdeal_norm_pos p.2).le]
  congr 1
  congr 1
  ring

theorem completedMellinCoefficient_summable (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (σ : ℝ) (hσ : 1<σ) :
    Summable (fun p=>‖completedMellinCoefficient Ψ p‖*(completedMellinLength p)^(-σ)) := by
  have hI := nonzeroIdeal_norm_rpow_summable σ hσ
  have hJ := nonzeroIdeal_norm_rpow_summable (3*σ) (by linarith)
  have hp := hI.mul_of_nonneg hJ (fun I=>Real.rpow_nonneg (nonzeroIdeal_norm_pos I).le _)
    (fun J=>Real.rpow_nonneg (nonzeroIdeal_norm_pos J).le _)
  apply hp.of_nonneg_of_le
  · intro p; exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (completedMellinLength_pos p).le _)
  · intro p
    rw [←completedMellinLength_rpow]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (completedMellinLength_pos p).le _)
      (completedMellinCoefficient_norm_le_one Ψ hΨ p)

def completedDirichletSeries (Ψ : ActualEisensteinCubic.O→*ℂ) (s : ℂ) : ℂ :=
  ∑'p : CompletedMellinIndex,completedMellinCoefficient Ψ p*
    (completedMellinLength p:ℂ)^(1/2-s)

theorem completedT_eq_mellin_index (Ψ : ActualEisensteinCubic.O→*ℂ) (W : ℝ→ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0<X) :
    completedT Ψ W X=∑'p : CompletedMellinIndex,
      completedMellinCoefficient Ψ p*Vstar W (completedMellinLength p/X) := by
  have hfull := completedT_summable Ψ W hW X hX
  have hinj : Function.Injective (fun p : CompletedMellinIndex=>(p.1.1,p.2.1)) := by
    intro p q h
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have hsub := hfull.comp_injective hinj
  calc
    completedT Ψ W X=∑'I : NonzeroIdeal,∑'J : Ideal ActualEisensteinCubic.O,summand Ψ W X I.1 J := by
      symm
      unfold completedT
      apply tsum_subtype_eq_of_support_subset
        (s:={I:Ideal ActualEisensteinCubic.O|I≠0}) (f:=fun I:Ideal ActualEisensteinCubic.O=>∑'J:Ideal ActualEisensteinCubic.O,summand Ψ W X I J)
      intro I hI hz
      subst I
      exact hI (by simp only [summand_zero_left,tsum_zero])
    _=∑'I : NonzeroIdeal,∑'J : NonzeroIdeal,summand Ψ W X I.1 J.1 := by
      apply tsum_congr
      intro I
      symm
      apply tsum_subtype_eq_of_support_subset
        (s:={J:Ideal ActualEisensteinCubic.O|J≠0}) (f:=fun J:Ideal ActualEisensteinCubic.O=>summand Ψ W X I.1 J)
      intro J hJ hz
      subst J
      exact hJ (summand_zero_right Ψ W X I.1)
    _=∑'p : CompletedMellinIndex,summand Ψ W X p.1.1 p.2.1 := hsub.tsum_prod.symm
    _=_ := rfl

theorem completedT_initial_mellin (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0<X) :
    completedT Ψ W X=(1/(2*Real.pi):ℂ)*∫t : ℝ,
      mellin (Vstar W) ((3/2:ℂ)+t*Complex.I)*(X:ℂ)^((3/2:ℂ)+t*Complex.I)*
        completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I) := by
  let : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let : Countable (Ideal ActualEisensteinCubic.O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
  have hWc : HasCompactSupport W :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  rw [completedT_eq_mellin_index Ψ W hWc X hX]
  have h := weightedMellin_inversion completedMellinLength completedMellinLength_pos
    (completedMellinCoefficient Ψ) (3/2)
    (completedMellinCoefficient_summable Ψ hΨ (3/2) (by norm_num))
    (Vstar W) a b ha (Vstar_support W a b hsupp) (Vstar_contDiff W a b ha hsupp hW) X hX
  have hd (t : ℝ) : completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I)=
      ∑'p : CompletedMellinIndex,completedMellinCoefficient Ψ p*
        (completedMellinLength p:ℂ)^(-((3/2:ℂ)+t*Complex.I)) := by
    unfold completedDirichletSeries
    apply tsum_congr
    intro p
    congr 2
    ring
  simpa only [hd,Complex.ofReal_div,Complex.ofReal_ofNat] using h

end

section
open ActualEisensteinCubic CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma nat_sqrt_cpow_half (a : ℕ) :
    (Real.sqrt (a:ℝ):ℂ)=(a:ℂ)^(1/2:ℂ) := by
  simpa only [Real.sqrt_eq_rpow,Complex.ofReal_natCast,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_ofNat] using
    (Complex.ofReal_cpow (Nat.cast_nonneg a) (1/2:ℝ))

lemma nat_half_shift_product (a b : ℕ) (ha : a≠0) (hb : b≠0) (C D s : ℂ) :
    (C/(Real.sqrt (a:ℝ):ℂ)*(D/(b:ℂ)))*((a:ℂ)*(b:ℂ)^3)^(1/2-s)=
      C*D*(b:ℂ)^(1/2-3*s)*(a:ℂ)^(-s) := by
  have ha0 : (a:ℂ)≠0 := Nat.cast_ne_zero.mpr ha
  have hb0 : (b:ℂ)≠0 := Nat.cast_ne_zero.mpr hb
  have hhalf : (a:ℂ)^(1/2:ℂ)≠0 := (Complex.cpow_ne_zero_iff).mpr (Or.inl ha0)
  rw [nat_sqrt_cpow_half]
  have hmul : ((a:ℂ)*(b:ℂ)^3)^(1/2-s)=
      (a:ℂ)^(1/2-s)*(b:ℂ)^(3*(1/2-s)) := by
    rw [←Nat.cast_pow,Complex.natCast_mul_natCast_cpow,Nat.cast_pow,
      ←Complex.natCast_cpow_natCast_mul]
    norm_num
  rw [hmul]
  have hA : (a:ℂ)^(1/2-s)=(a:ℂ)^(1/2:ℂ)*(a:ℂ)^(-s) := by
    rw [sub_eq_add_neg,Complex.cpow_add _ _ ha0]
  have hB : (b:ℂ)^(3*(1/2-s))=(b:ℂ)*(b:ℂ)^(1/2-3*s) := by
    rw [show (3:ℂ)*(1/2-s)=1+(1/2-3*s) by ring,
      Complex.cpow_add _ _ hb0,Complex.cpow_one]
  rw [hA,hB]
  field_simp

lemma completedDirichletTerm_expanded (Ψ : ActualEisensteinCubic.O→*ℂ) (s : ℂ) (p : CompletedMellinIndex) :
    completedMellinCoefficient Ψ p*(completedMellinLength p:ℂ)^(1/2-s)=
      columnWeight Ψ p.1.1*star (FiniteGaussPhase.angularFactor (primaryGenerator p.2.1))^3*
      Ψ (primaryGenerator p.2.1)^3*(Ideal.absNorm p.2.1:ℂ)^(1/2-3*s)*
      (Ideal.absNorm p.1.1:ℂ)^(-s) := by
  have ha : Ideal.absNorm p.1.1≠0 := fun h=>p.1.2 (Ideal.absNorm_eq_zero_iff.mp h)
  have hb : Ideal.absNorm p.2.1≠0 := fun h=>p.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
  unfold completedMellinCoefficient completedMellinLength
  change (columnWeight Ψ p.1.1/(Real.sqrt (Ideal.absNorm p.1.1:ℝ):ℂ)*
    (star (FiniteGaussPhase.angularFactor (primaryGenerator p.2.1))^3*
      Ψ (primaryGenerator p.2.1)^3/(Ideal.absNorm p.2.1:ℂ)))*
    (((Ideal.absNorm p.1.1:ℝ)*(Ideal.absNorm p.2.1:ℝ)^3:ℝ):ℂ)^(1/2-s)=_
  rw [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast,Complex.ofReal_natCast]
  rw [nat_half_shift_product _ _ ha hb]
  ring

theorem completedDirichletSeries_expanded (Ψ : ActualEisensteinCubic.O→*ℂ) (s : ℂ) :
    completedDirichletSeries Ψ s=∑'p : CompletedMellinIndex,
      columnWeight Ψ p.1.1*star (FiniteGaussPhase.angularFactor (primaryGenerator p.2.1))^3*
      Ψ (primaryGenerator p.2.1)^3*(Ideal.absNorm p.2.1:ℂ)^(1/2-3*s)*
      (Ideal.absNorm p.1.1:ℂ)^(-s) := by
  unfold completedDirichletSeries
  exact tsum_congr (completedDirichletTerm_expanded Ψ s)

end

open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

lemma weighted_vertical_series_continuous {α : Type*}
    (r : α→ℝ) (hr : ∀i,0<r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ))) :
    Continuous (fun t : ℝ=>∑'i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))) := by
  apply continuous_tsum
    (fun i=>continuous_const.mul (positive_cpow_negative_vertical_continuous (r i) σ (hr i))) hc
  intro i t
  change ‖c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))‖≤‖c i‖*(r i)^(-σ)
  rw [norm_mul,positive_cpow_negative_vertical_norm _ _ _ (hr i)]

lemma weighted_vertical_series_norm {α : Type*}
    (r : α→ℝ) (hr : ∀i,0<r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ))) (t : ℝ) :
    ‖∑'i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))‖≤∑'i,‖c i‖*(r i)^(-σ) := by
  have he (i : α) : ‖c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))‖=‖c i‖*(r i)^(-σ) := by
    rw [norm_mul,positive_cpow_negative_vertical_norm _ _ _ (hr i)]
  simpa only [he] using norm_tsum_le_tsum_norm (hc.congr (fun i=>(he i).symm))

lemma completedDirichletSeries_initial (Ψ : ActualEisensteinCubic.O→*ℂ) (t : ℝ) :
    completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I)=
      ∑'p : CompletedMellinIndex,completedMellinCoefficient Ψ p*
        (completedMellinLength p:ℂ)^(-((3/2:ℂ)+t*Complex.I)) := by
  unfold completedDirichletSeries
  apply tsum_congr
  intro p
  congr 2
  ring

theorem completedT_initial_mellin_integrable (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0<X) :
    Integrable (fun t : ℝ=>mellin (Vstar W) ((3/2:ℂ)+t*Complex.I)*
      (X:ℂ)^((3/2:ℂ)+t*Complex.I)*completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I)) := by
  have hsum := completedMellinCoefficient_summable Ψ hΨ (3/2) (by norm_num)
  have hc := weighted_vertical_series_continuous completedMellinLength completedMellinLength_pos
    (completedMellinCoefficient Ψ) (3/2) hsum
  have hb := weighted_vertical_series_norm completedMellinLength completedMellinLength_pos
    (completedMellinCoefficient Ψ) (3/2) hsum
  have hmi : Integrable (fun t : ℝ=>mellin (Vstar W) ((3/2:ℂ)+t*Complex.I)) := by
    simpa only [Complex.VerticalIntegrable,Complex.ofReal_div,Complex.ofReal_ofNat] using
      (compactMellin_vertical_integrable (Vstar W) a b ha (Vstar_support W a b hsupp)
        (Vstar_contDiff W a b ha hsupp hW) (3/2))
  have hbase := vertical_power_mul_integrable _ hmi X (3/2) hX
  have hi := hbase.mul_bdd hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  simpa only [Complex.ofReal_div,Complex.ofReal_ofNat,completedDirichletSeries_initial,
    mul_comm (mellin (Vstar W) _)] using hi

end CompletedGauss

open scoped BigOperators Classical
open Finset AddChar MulChar EisensteinEmbedding

namespace CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def dualIdealDyad (j : ℕ) : Finset (Ideal Eis) :=
  (ConcretePrimeRowBridge.idealsUpTo (2^j)).filter
    (fun I => Nat.clog 2 (Ideal.absNorm I)=j)

lemma mem_dualIdealDyad (I : Ideal Eis) (j : ℕ) :
    I∈dualIdealDyad j ↔ I≠0 ∧ Nat.clog 2 (Ideal.absNorm I)=j := by
  simp only [dualIdealDyad,Finset.mem_filter,ConcretePrimeRowBridge.mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hI,_⟩,hj⟩
    exact ⟨fun h => by simp [h] at hI, hj⟩
  · rintro ⟨hI,hj⟩
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI),?_⟩,hj⟩
    simpa only [hj] using Nat.le_pow_clog (by norm_num : 1<2) (Ideal.absNorm I)

lemma dualIdealDyad_bounds (j : ℕ) (I : Ideal Eis) (hI : I∈dualIdealDyad j) :
    I≠0 ∧ (2:ℝ)^j/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^j := by
  obtain ⟨hn,hj⟩:= (mem_dualIdealDyad I j).mp hI
  have hu:=Nat.le_pow_clog (by norm_num : 1<2) (Ideal.absNorm I)
  have hl:=two_pow_clog_le_double (Ideal.absNorm I)
    (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hn))
  rw [hj] at hu hl
  refine ⟨hn,?_,by exact_mod_cast hu⟩
  have he : (2:ℝ)^j≤2*(Ideal.absNorm I:ℝ):=by exact_mod_cast hl
  linarith

abbrev NonzeroDualIdeal := {I : Ideal Eis // I≠0}

def dualDyadicIndexEquiv :
    (ℕ×NonzeroDualIdeal×NonzeroDualIdeal) ≃
      (Σ i : ℕ×ℕ×ℕ, (dualIdealDyad i.2.2)×(dualIdealDyad i.2.1)) where
  toFun x := ⟨(x.1,Nat.clog 2 (Ideal.absNorm x.2.2.val),Nat.clog 2 (Ideal.absNorm x.2.1.val)),
    ⟨⟨x.2.1.val,(mem_dualIdealDyad _ _).mpr ⟨x.2.1.property,rfl⟩⟩,
      ⟨x.2.2.val,(mem_dualIdealDyad _ _).mpr ⟨x.2.2.property,rfl⟩⟩⟩⟩
  invFun x := ⟨x.1.1,⟨x.2.1.val,((mem_dualIdealDyad _ _).mp x.2.1.property).1⟩,
    ⟨x.2.2.val,((mem_dualIdealDyad _ _).mp x.2.2.property).1⟩⟩
  left_inv x := by cases x; rfl
  right_inv x := by
    rcases x with ⟨⟨m,j,k⟩,⟨⟨I,hI⟩,⟨J,hJ⟩⟩⟩
    have hi:=((mem_dualIdealDyad I k).mp hI).2
    have hj:=((mem_dualIdealDyad J j).mp hJ).2
    dsimp only
    subst k
    subst j
    rfl

theorem tsum_dualIdealDyads
    (f : ℕ×NonzeroDualIdeal×NonzeroDualIdeal → ℂ) (hf : Summable f) :
    (∑'x, f x) = ∑'i : ℕ×ℕ×ℕ,
      ∑n : dualIdealDyad i.2.2, ∑b : dualIdealDyad i.2.1,
        f (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
          ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) := by
  let g := f ∘ dualDyadicIndexEquiv.symm
  have hg : Summable g := dualDyadicIndexEquiv.symm.summable_iff.mpr hf
  calc
    _ = ∑'x,g x := (dualDyadicIndexEquiv.symm.tsum_eq f).symm
    _ = ∑'i,∑'x,g ⟨i,x⟩ := Summable.tsum_sigma' (fun _=>hasSum_fintype _ |>.summable) hg
    _ = _ := by
      apply tsum_congr
      intro i
      rw [tsum_fintype,Fintype.sum_prod_type]
      rfl

end CompletedGauss

end

end OAI
end OAIOriginalModule0305

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.BesselReflection
Source SHA256: d25806f3923da61e1f3cd5fd70b0c28febcc2d51f70765c14e97b0042d703ffb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0306



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

namespace CompletedGauss
open Filter MeasureTheory
open scoped Classical BigOperators Topology

section
open CubicEisenstein

def completedBesselProfile (Ψ : ActualEisensteinCubic.O→*ℂ) (q : ℝ) : ℝ→ℂ :=
  radialBesselProfile completedMellinLength (completedMellinCoefficient Ψ) q

def besselMellinFactor (q : ℝ) (s : ℂ) : ℂ :=
  ((2:ℂ)^(2*s-1)*Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))/
    ((4*Real.pi*q:ℝ):ℂ)^(2*s+1)

def inverseBesselMellinFactor (q : ℝ) (s : ℂ) : ℂ :=
  ((4*Real.pi*q:ℝ):ℂ)^(2*s+1)*(2:ℂ)^(1-2*s)*
    (Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))⁻¹

theorem completedBesselProfile_mellin (Ψ : ActualEisensteinCubic.O→*ℂ)
    (hΨ : ∀a,‖Ψ a‖≤1) (q : ℝ) (hq : 0<q) (s : ℂ) (hs : 3/2<s.re) :
    mellin (completedBesselProfile Ψ q) (2*s)=
      besselMellinFactor q s*completedDirichletSeries Ψ s := by
  let : Countable ActualEisensteinCubic.O :=
    ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let : Countable (Ideal ActualEisensteinCubic.O) :=
    ConcretePrimeRowBridge.idealGenerator_injective.countable
  have hsum := completedMellinCoefficient_summable Ψ hΨ (s.re-1/2) (by linarith)
  have he : -(s.re-1/2)=1/2-s.re := by ring
  simp only [he] at hsum
  exact radialBesselProfile_mellin completedMellinLength completedMellinLength_pos
    (completedMellinCoefficient Ψ) q hq s (by linarith) hsum

lemma inverseBesselMellinFactor_mul (q : ℝ) (hq : 0<q) (s : ℂ)
    (hs : -(1/3)<s.re) :
    inverseBesselMellinFactor q s*besselMellinFactor q s=1 := by
  have hq0 : (((4*Real.pi*q:ℝ):ℂ)^(2*s+1))≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity)))
  have h1 : Complex.Gamma (s+1/3)≠0 := Complex.Gamma_ne_zero_of_re_pos (by simp;linarith)
  have h2 : Complex.Gamma (s+2/3)≠0 := Complex.Gamma_ne_zero_of_re_pos (by simp;linarith)
  have hp : (2:ℂ)^(1-2*s)*(2:ℂ)^(2*s-1)=1 := by
    rw [←Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    simp
  unfold inverseBesselMellinFactor besselMellinFactor
  calc
    _=((((4*Real.pi*q:ℝ):ℂ)^(2*s+1))/(((4*Real.pi*q:ℝ):ℂ)^(2*s+1)))*
        ((2:ℂ)^(1-2*s)*(2:ℂ)^(2*s-1))*
        ((Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))⁻¹*
          (Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))) := by ring
    _=1 := by rw [div_self hq0,hp,inv_mul_cancel₀ (mul_ne_zero h1 h2)];ring

theorem completedDirichletSeries_eq_mellin (Ψ : ActualEisensteinCubic.O→*ℂ)
    (hΨ : ∀a,‖Ψ a‖≤1) (q : ℝ) (hq : 0<q) (s : ℂ) (hs : 3/2<s.re) :
    completedDirichletSeries Ψ s=
      inverseBesselMellinFactor q s*mellin (completedBesselProfile Ψ q) (2*s) := by
  rw [completedBesselProfile_mellin Ψ hΨ q hq s hs,←mul_assoc,
    inverseBesselMellinFactor_mul q hq s (by linarith),one_mul]

end

theorem inverseBesselMellinFactor_differentiable (q : ℝ) (hq : 0<q) :
    Differentiable ℂ (inverseBesselMellinFactor q) := by
  have hq0 : ((4*Real.pi*q:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have h1 : Differentiable ℂ (fun s : ℂ=>((4*Real.pi*q:ℝ):ℂ)^(2*s+1)) :=
    (show Differentiable ℂ (fun s : ℂ=>2*s+1) from by fun_prop).const_cpow (Or.inl hq0)
  have h2 : Differentiable ℂ (fun s : ℂ=>(2:ℂ)^(1-2*s)) :=
    (show Differentiable ℂ (fun s : ℂ=>1-2*s) from by fun_prop).const_cpow
      (Or.inl (by norm_num : (2:ℂ)≠0))
  have h3 : Differentiable ℂ (fun s : ℂ=>(Complex.Gamma (s+1/3))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp (by fun_prop)
  have h4 : Differentiable ℂ (fun s : ℂ=>(Complex.Gamma (s+2/3))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp (by fun_prop)
  convert (h1.mul h2).mul (h4.mul h3) using 1
  ext s
  simp only [inverseBesselMellinFactor,Pi.mul_apply,mul_inv_rev]

theorem inverseBesselMellinFactor_strip_bound (q : ℝ) (hq : 0<q) (a b : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀s : ℂ,s.re∈Set.Icc a b →
      ‖inverseBesselMellinFactor q s‖≤C*Real.exp (2*Real.pi*|s.im|) := by
  obtain ⟨Cg,hCg,hg⟩ := CubicGammaExponential.inverse_cubic_Gamma_pair_strip_bound a b
  let Ca := (4*Real.pi*q)^(2*a+1)+(4*Real.pi*q)^(2*b+1)
  let Cb := (2:ℝ)^(1-2*b)+(2:ℝ)^(1-2*a)
  have hqpos : 0<4*Real.pi*q := by positivity
  have hCa : 0≤Ca := by dsimp [Ca];positivity
  have hCb : 0≤Cb := by dsimp [Cb];positivity
  refine ⟨Ca*Cb*Cg,by positivity,?_⟩
  intro s hs
  have hp1 : ‖((4*Real.pi*q:ℝ):ℂ)^(2*s+1)‖≤Ca := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hqpos]
    have hr : (2*s+1).re=2*s.re+1 := by simp
    rw [hr]
    exact VerticalContourShift.rpow_between_endpoints _ _ _ _ hqpos
      (by linarith [hs.1]) (by linarith [hs.2])
  have hp2 : ‖(2:ℂ)^(1-2*s)‖≤Cb := by
    change ‖((2:ℝ):ℂ)^(1-2*s)‖≤Cb
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : 0<(2:ℝ))]
    have hr : (1-2*s).re=1-2*s.re := by simp
    rw [hr]
    exact VerticalContourShift.rpow_between_endpoints _ _ _ _ (by norm_num)
      (by linarith [hs.2]) (by linarith [hs.1])
  simp only [inverseBesselMellinFactor,norm_mul]
  calc
    _≤(Ca*Cb)*(Cg*Real.exp (2*Real.pi*|s.im|)) :=
      mul_le_mul (mul_le_mul hp1 hp2 (norm_nonneg _) hCa) (hg s hs)
        (norm_nonneg _) (mul_nonneg hCa hCb)
    _=_ := by ring

def continuedBesselDirichlet (F : ℝ→ℂ) (q : ℝ) (s : ℂ) : ℂ :=
  inverseBesselMellinFactor q s*mellin F (2*s)

theorem continuedBesselDirichlet_differentiable (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (hF : Differentiable ℂ (mellin F)) :
    Differentiable ℂ (continuedBesselDirichlet F q) :=
  (inverseBesselMellinFactor_differentiable q hq).mul (hF.comp (by fun_prop))

theorem continuedBesselDirichlet_strip_bound (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (a b : ℝ) (ha : MellinConvergent F ((2*a:ℝ):ℂ))
    (hb : MellinConvergent F ((2*b:ℝ):ℂ)) :
    ∃C : ℝ,0≤C ∧ ∀s : ℂ,s.re∈Set.Icc a b →
      ‖continuedBesselDirichlet F q s‖≤C*Real.exp (2*Real.pi*|s.im|) := by
  obtain ⟨Ci,hCi,hi⟩ := inverseBesselMellinFactor_strip_bound q hq a b
  obtain ⟨Cm,hCm,hm⟩ := VerticalContourShift.mellin_uniform_strip_bound F (2*a) (2*b) ha hb
  refine ⟨Ci*Cm,mul_nonneg hCi hCm,?_⟩
  intro s hs
  have hms : ‖mellin F (2*s)‖≤Cm := hm (2*s)
    (by simp;linarith [hs.1]) (by simp;linarith [hs.2])
  rw [continuedBesselDirichlet,norm_mul]
  calc
    _≤(Ci*Real.exp (2*Real.pi*|s.im|))*Cm :=
      mul_le_mul (hi s hs) hms (norm_nonneg _) (mul_nonneg hCi (Real.exp_pos _).le)
    _=_ := by ring

theorem continuedBesselDirichlet_eq_initial (Ψ : ActualEisensteinCubic.O→*ℂ)
    (hΨ : ∀a,‖Ψ a‖≤1) (q : ℝ) (hq : 0<q) (s : ℂ) (hs : 3/2<s.re) :
    continuedBesselDirichlet (completedBesselProfile Ψ q) q s=
      completedDirichletSeries Ψ s :=
  (completedDirichletSeries_eq_mellin Ψ hΨ q hq s hs).symm

end CompletedGauss

namespace CubicEisenstein
open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology MatrixGroups

section
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedSource_horizontal_hasDerivAt (side:Bool) (v:ℝ) (hv:0<v)
    (z direction:ℂ) (t:ℝ) :
    HasDerivAt (fun x:ℝ => ramifiedSourceFunction (ramifiedCuspRoot side:Eis)
      (upperPoint (z+(x:ℂ)*direction) v hv))
      (∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3)
        (z/3+(t:ℂ)*(direction/3)) (direction/3)) t := by
  have he : (fun x:ℝ => ramifiedSourceFunction (ramifiedCuspRoot side:Eis)
      (upperPoint (z+(x:ℂ)*direction) v hv)) =
      (fun x:ℝ => (ramifiedBesselCoefficients side).series
        (v/3,z/3+(x:ℂ)*(direction/3))) := by
    funext x
    rw [ramifiedSource_eq_series]
    congr 2
    ring
  rw [he]
  exact (ramifiedBesselCoefficients side).series_horizontal_hasDerivAt
    (v/3) (by positivity) (z/3) (direction/3) t

lemma ramifiedSource_wirtingerBar_cusp_decay (side:Bool) (a:ℝ) (ha:0<a) :
    ∃C:ℝ,0≤C ∧ ∀(v:ℝ)(hv:0<v)(z:ℂ),a≤v →
      ‖horizontalWirtingerBar (fun w => ramifiedSourceFunction (ramifiedCuspRoot side:Eis)
        (upperPoint w v hv)) z‖ ≤ C*Real.exp (-(residualCuspDecayRate/3)*v) := by
  obtain ⟨C1,hC1,h1b⟩ := (ramifiedBesselCoefficients side).directionalSeries_cusp_decay
    (a/3) (by positivity) (1/3)
  obtain ⟨CI,hCI,hIb⟩ := (ramifiedBesselCoefficients side).directionalSeries_cusp_decay
    (a/3) (by positivity) (Complex.I/3)
  refine ⟨(C1+CI)/2,by positivity,?_⟩
  intro v hv z hav
  have h1 := (ramifiedSource_horizontal_hasDerivAt side v hv z 1 0).deriv
  have hI := (ramifiedSource_horizontal_hasDerivAt side v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  have he : -residualCuspDecayRate*(v/3)=-(residualCuspDecayRate/3)*v := by ring
  have hb1 := h1b (v/3) (z/3) (by linarith)
  have hbI := hIb (v/3) (z/3) (by linarith)
  rw [he] at hb1 hbI
  rw [horizontalWirtingerBar,h1,hI,norm_mul]
  have hhalf : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [hhalf]
  calc
    _ ≤ (1/2:ℝ)*(‖∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (1/3)‖+
      ‖Complex.I*(∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (Complex.I/3))‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = (1/2:ℝ)*(‖∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (1/3)‖+
      ‖∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (Complex.I/3)‖) := by
        rw [norm_mul,Complex.norm_I,one_mul]
    _ ≤ (1/2:ℝ)*(C1*Real.exp (-(residualCuspDecayRate/3)*v)+
      CI*Real.exp (-(residualCuspDecayRate/3)*v)) :=
        mul_le_mul_of_nonneg_left (add_le_add hb1 hbI) (by norm_num)
    _ = _ := by ring

lemma ramifiedSource_wirtingerZ_cusp_decay (side:Bool) (a:ℝ) (ha:0<a) :
    ∃C:ℝ,0≤C ∧ ∀(v:ℝ)(hv:0<v)(z:ℂ),a≤v →
      ‖horizontalWirtingerZ (fun w => ramifiedSourceFunction (ramifiedCuspRoot side:Eis)
        (upperPoint w v hv)) z‖ ≤ C*Real.exp (-(residualCuspDecayRate/3)*v) := by
  obtain ⟨C1,hC1,h1b⟩ := (ramifiedBesselCoefficients side).directionalSeries_cusp_decay
    (a/3) (by positivity) (1/3)
  obtain ⟨CI,hCI,hIb⟩ := (ramifiedBesselCoefficients side).directionalSeries_cusp_decay
    (a/3) (by positivity) (Complex.I/3)
  refine ⟨(C1+CI)/2,by positivity,?_⟩
  intro v hv z hav
  have h1 := (ramifiedSource_horizontal_hasDerivAt side v hv z 1 0).deriv
  have hI := (ramifiedSource_horizontal_hasDerivAt side v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  have he : -residualCuspDecayRate*(v/3)=-(residualCuspDecayRate/3)*v := by ring
  have hb1 := h1b (v/3) (z/3) (by linarith)
  have hbI := hIb (v/3) (z/3) (by linarith)
  rw [he] at hb1 hbI
  rw [horizontalWirtingerZ,h1,hI,norm_mul]
  have hhalf : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [hhalf]
  calc
    _ ≤ (1/2:ℝ)*(‖∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (1/3)‖+
      ‖Complex.I*(∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (Complex.I/3))‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ = (1/2:ℝ)*(‖∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (1/3)‖+
      ‖∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (Complex.I/3)‖) := by
        rw [norm_mul,Complex.norm_I,one_mul]
    _ ≤ (1/2:ℝ)*(C1*Real.exp (-(residualCuspDecayRate/3)*v)+
      CI*Real.exp (-(residualCuspDecayRate/3)*v)) :=
        mul_le_mul_of_nonneg_left (add_le_add hb1 hbI) (by norm_num)
    _ = _ := by ring

lemma ramifiedConjugate_barProfile_isBigO (side:Bool) (z:ℂ) :
    cuspBarProfile (fun w => cubicSourceConjugateFunction
      (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis)) • w)) z
      =O[atTop] (fun v:ℝ => Real.exp (-(residualCuspDecayRate/3)*v)) := by
  obtain ⟨C,hC,hb⟩ := ramifiedSource_wirtingerZ_cusp_decay side 1 (by norm_num)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1:ℝ)] with v hv
  have hvp:0<v := lt_of_lt_of_le (by norm_num) hv
  rw [cuspBarProfile_positive _ _ _ hvp,Real.norm_of_nonneg (Real.exp_pos _).le]
  change ‖horizontalWirtingerBar (fun w => star (ramifiedSourceFunction
    (ramifiedCuspRoot side:Eis) (upperPoint w v hvp))) z‖ ≤ _
  rw [horizontalWirtingerBar_star,norm_star]
  exact hb v hvp z hv

lemma ramifiedConjugate_zProfile_isBigO (side:Bool) (z:ℂ) :
    cuspZProfile (fun w => cubicSourceConjugateFunction
      (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis)) • w)) z
      =O[atTop] (fun v:ℝ => Real.exp (-(residualCuspDecayRate/3)*v)) := by
  obtain ⟨C,hC,hb⟩ := ramifiedSource_wirtingerBar_cusp_decay side 1 (by norm_num)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1:ℝ)] with v hv
  have hvp:0<v := lt_of_lt_of_le (by norm_num) hv
  rw [cuspZProfile_positive _ _ _ hvp,Real.norm_of_nonneg (Real.exp_pos _).le]
  change ‖horizontalWirtingerZ (fun w => star (ramifiedSourceFunction
    (ramifiedCuspRoot side:Eis) (upperPoint w v hvp))) z‖ ≤ _
  rw [horizontalWirtingerZ_star,norm_star]
  exact hb v hvp z hv

end

local notation "Eis" => ActualEisensteinCubic.O

lemma reflectedCuspProfile_eq_inv_square (A:ℂ) (Q:ℝ) (g:ℝ→ℂ) (v:ℝ) :
    reflectedCuspProfile A Q g v=A/(v:ℂ)^2*g ((Q*v)⁻¹) := by
  unfold reflectedCuspProfile
  rw [Complex.cpow_neg,Complex.cpow_ofNat]
  ring

lemma reflectedCuspProfile_reverse (A:ℂ) (hA:A≠0) (Q:ℝ) (hQ:0<Q)
    (f g:ℝ→ℂ) (hfg:∀v:ℝ,0<v→f v=reflectedCuspProfile A Q g v)
    (v:ℝ) (hv:0<v) :
    g v=reflectedCuspProfile (A⁻¹/(Q:ℂ)^2) Q f v := by
  have he:=hfg (Q*v)⁻¹ (by positivity)
  have harg:(Q*(Q*v)⁻¹)⁻¹=v := by field_simp
  rw [reflectedCuspProfile_eq_inv_square,harg] at he
  rw [reflectedCuspProfile_eq_inv_square,he,Complex.ofReal_inv,Complex.ofReal_mul]
  have hcQ:(Q:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hQ.ne'
  have hcv:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv.ne'
  field_simp

theorem cusp_mellin_entire_both (f g:ℝ→ℂ) (A:ℂ) (hA:A≠0)
    (Q decayF decayG:ℝ) (hQ:0<Q) (hdecayF:0<decayF) (hdecayG:0<decayG)
    (hf:ContinuousOn f (Set.Ioi 0)) (hg:ContinuousOn g (Set.Ioi 0))
    (hfbound:f =O[atTop] (fun v:ℝ=>Real.exp (-decayF*v)))
    (hgbound:g =O[atTop] (fun v:ℝ=>Real.exp (-decayG*v)))
    (hfg:∀v:ℝ,0<v→f v=reflectedCuspProfile A Q g v) :
    ((∀s:ℂ,MellinConvergent f s) ∧ Differentiable ℂ (mellin f)) ∧
    ((∀s:ℂ,MellinConvergent g s) ∧ Differentiable ℂ (mellin g)) := by
  constructor
  · exact cusp_mellin_entire f g A Q decayF decayG hQ hdecayF hdecayG
      hf hg hfbound hgbound hfg
  · exact cusp_mellin_entire g f (A⁻¹/(Q:ℂ)^2) Q decayG decayF hQ hdecayG hdecayF
      hg hf hgbound hfbound (reflectedCuspProfile_reverse A hA Q hQ f g hfg)

theorem conjugateSource_ramified_cusp_mellin_entire (side:Bool)
    (G:CubicKubota.levelThree) (g:SL(2,ℂ))
    (hfactor:g=complexMatrix G*integralComplexMatrix
      (lowerCuspMatrix (ramifiedCuspRoot side:Eis))) (hc:g 1 0≠0) :
    ((∀s:ℂ,MellinConvergent
      (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0)) s) ∧
      Differentiable ℂ (mellin (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0)))) ∧
    ((∀s:ℂ,MellinConvergent
      (cuspZProfile (fun w=>cubicSourceConjugateFunction
        (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis)) • w))
        (-g 1 1/g 1 0)) s) ∧
      Differentiable ℂ (mellin
        (cuspZProfile (fun w=>cubicSourceConjugateFunction
          (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis)) • w))
          (-g 1 1/g 1 0)))) := by
  have hchar:CubicKubota.complexCharacter G≠0 := by
    intro hz
    have hn:=CubicKubota.norm_complexCharacter G
    rw [hz,norm_zero] at hn
    norm_num at hn
  have hscalar : -star (CubicKubota.complexCharacter G)/(g 1 0)^2≠0 :=
    div_ne_zero (neg_ne_zero.mpr (star_ne_zero.mpr hchar)) (pow_ne_zero 2 hc)
  exact cusp_mellin_entire_both
    (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0))
    (cuspZProfile (fun w=>cubicSourceConjugateFunction
      (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis)) • w))
      (-g 1 1/g 1 0))
    (-star (CubicKubota.complexCharacter G)/(g 1 0)^2) hscalar (‖g 1 0‖^2)
    residualCuspDecayRate (residualCuspDecayRate/3)
    (sq_pos_of_pos (norm_pos_iff.mpr hc)) residualCuspDecayRate_pos
    (div_pos residualCuspDecayRate_pos (by norm_num))
    (cuspBarProfile_conjugate_continuousOn _)
    (cuspZProfile_conjugate_translate_continuousOn _ _)
    (cuspBarProfile_conjugate_isBigO _)
    (ramifiedConjugate_zProfile_isBigO side _)
    (fun v hv=>cuspBarProfile_conjugate_reflection G g _ hfactor hc v hv)

end CubicEisenstein

open scoped BigOperators Classical

namespace CompletedGauss

section
open UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

theorem squarefree_cube_decomposition_unique {I J I' J':Ideal Eis}
    (hJ:J≠0) (hJ':J'≠0) (hI:Squarefree I) (hI':Squarefree I')
    (h:I*J^3=I'*J'^3) : I=I' ∧ J=J' := by
  have hf:=congrArg normalizedFactors h
  rw [normalizedFactors_mul hI.ne_zero (pow_ne_zero _ hJ),
    normalizedFactors_mul hI'.ne_zero (pow_ne_zero _ hJ'),
    normalizedFactors_pow,normalizedFactors_pow] at hf
  have hi:=(squarefree_iff_nodup_normalizedFactors hI.ne_zero).mp hI
  have hi':=(squarefree_iff_nodup_normalizedFactors hI'.ne_zero).mp hI'
  have hc (P:Ideal Eis) :
      (normalizedFactors I).count P=(normalizedFactors I').count P ∧
      (normalizedFactors J).count P=(normalizedFactors J').count P := by
    have he:=congrArg (Multiset.count P) hf
    simp only [Multiset.count_add,Multiset.count_nsmul] at he
    have h1:=Multiset.nodup_iff_count_le_one.mp hi P
    have h2:=Multiset.nodup_iff_count_le_one.mp hi' P
    omega
  constructor
  · calc
      I=(normalizedFactors I).prod:=(Ideal.prod_normalizedFactors_eq_self hI.ne_zero).symm
      _=(normalizedFactors I').prod:=congrArg Multiset.prod (Multiset.ext.mpr (fun P=>(hc P).1))
      _=I':=Ideal.prod_normalizedFactors_eq_self hI'.ne_zero
  · calc
      J=(normalizedFactors J).prod:=(Ideal.prod_normalizedFactors_eq_self hJ).symm
      _=(normalizedFactors J').prod:=congrArg Multiset.prod (Multiset.ext.mpr (fun P=>(hc P).2))
      _=J':=Ideal.prod_normalizedFactors_eq_self hJ'

theorem primary_squarefree_cube_eq_iff {I J I' J':Ideal Eis}
    (hI:Squarefree I) (hI':Squarefree I')
    (hgI:primaryGenerator I≠0) (hgJ:primaryGenerator J≠0)
    (hgI':primaryGenerator I'≠0) (hgJ':primaryGenerator J'≠0) :
    primaryGenerator I*(primaryGenerator J)^3=
      primaryGenerator I'*(primaryGenerator J')^3 ↔ I=I' ∧ J=J' := by
  constructor
  · intro h
    have hleft:primaryGenerator (I*J^3)≠0:=by
      rw [primaryGenerator_mul,CubicEisenstein.primaryGenerator_pow]
      exact mul_ne_zero hgI (pow_ne_zero _ hgJ)
    have hright:primaryGenerator (I'*J'^3)≠0:=by
      rw [primaryGenerator_mul,CubicEisenstein.primaryGenerator_pow]
      exact mul_ne_zero hgI' (pow_ne_zero _ hgJ')
    have he:I*J^3=I'*J'^3:=by
      calc
        I*J^3=Ideal.span {primaryGenerator (I*J^3)}:=(primaryGenerator_spec _ hleft).1.symm
        _=Ideal.span {primaryGenerator (I'*J'^3)}:=by
          apply congrArg (fun z:Eis => (Ideal.span {z}:Ideal Eis))
          simpa only [primaryGenerator_mul,CubicEisenstein.primaryGenerator_pow] using h
        _=I'*J'^3:=(primaryGenerator_spec _ hright).1
    exact squarefree_cube_decomposition_unique
      (primaryGenerator_ne_zero_ideal J hgJ) (primaryGenerator_ne_zero_ideal J' hgJ') hI hI' he
  · rintro ⟨rfl,rfl⟩
    rfl

theorem primary_squarefree_cube_injective :
    Function.Injective (fun x:
      {I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
      {J:Ideal Eis // primaryGenerator J≠0} =>
        primaryGenerator x.1.val*(primaryGenerator x.2.val)^3) := by
  intro x y he
  have h:= (primary_squarefree_cube_eq_iff x.1.property.1 y.1.property.1
    x.1.property.2 x.2.property y.1.property.2 y.2.property).mp he
  exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)

end

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

def besselSmoothingIntegrand (F : ℝ→ℂ) (q : ℝ) (V : ℝ→ℂ) (X : ℝ) (s : ℂ) : ℂ :=
  mellin V (s-1/2)*(X:ℂ)^(s-1/2)*continuedBesselDirichlet F q s

lemma besselSmoothingIntegrand_differentiable (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (hF : Differentiable ℂ (mellin F)) (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hVs : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) : Differentiable ℂ (besselSmoothingIntegrand F q V X) := by
  have hm := (CubicReflectionKernel.compact_source_mellin_differentiable V a b ha hVs hV).comp
    (show Differentiable ℂ (fun s : ℂ=>s-1/2) from by fun_prop)
  have hp : Differentiable ℂ (fun s : ℂ=>(X:ℂ)^(s-1/2)) :=
    (show Differentiable ℂ (fun s : ℂ=>s-1/2) from by fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  exact (hm.mul hp).mul (continuedBesselDirichlet_differentiable F q hq hF)

lemma besselSmoothingIntegrand_strip_bound (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (lo hi : ℝ) (hF : ∀s : ℂ,MellinConvergent F s)
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hVs : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) :
    ∃C : ℝ,0≤C ∧ ∀s : ℂ,s.re∈Set.Icc lo hi →
      ‖besselSmoothingIntegrand F q V X s‖≤C*Real.exp (2*Real.pi*|s.im|) := by
  obtain ⟨Cd,hCd,hd⟩ := continuedBesselDirichlet_strip_bound F q hq lo hi (hF _) (hF _)
  have hVc (s : ℂ) := CubicReflectionKernel.compact_source_mellin_convergent V a b ha hVs hV s
  obtain ⟨Cv,hCv,hv⟩ := VerticalContourShift.mellin_uniform_strip_bound V (lo-1/2) (hi-1/2)
    (hVc _) (hVc _)
  let Cx : ℝ := X^(lo-1/2)+X^(hi-1/2)
  have hCx : 0≤Cx := by dsimp [Cx];positivity
  refine ⟨Cv*Cx*Cd,mul_nonneg (mul_nonneg hCv hCx) hCd,?_⟩
  intro s hs
  have hvb : ‖mellin V (s-1/2)‖≤Cv := hv (s-1/2)
    (by simp;linarith [hs.1]) (by simp;linarith [hs.2])
  have hxb : ‖(X:ℂ)^(s-1/2)‖≤Cx := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
    have he : (s-1/2).re=s.re-1/2 := by simp
    rw [he]
    exact VerticalContourShift.rpow_between_endpoints X (lo-1/2) (hi-1/2) (s.re-1/2) hX
      (by linarith [hs.1]) (by linarith [hs.2])
  rw [besselSmoothingIntegrand,norm_mul,norm_mul]
  calc
    _≤(Cv*Cx)*(Cd*Real.exp (2*Real.pi*|s.im|)) :=
      mul_le_mul (mul_le_mul hvb hxb (norm_nonneg _) hCv) (hd s hs)
        (norm_nonneg _) (mul_nonneg hCv hCx)
    _=_ := by ring

theorem besselSmoothingIntegrand_contour_eq (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (hF : ∀s : ℂ,MellinConvergent F s) (hFe : Differentiable ℂ (mellin F))
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hVs : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) (lo hi : ℝ) (hlh : lo≤hi)
    (hl : Integrable (fun t : ℝ=>besselSmoothingIntegrand F q V X ((lo:ℂ)+t*Complex.I)))
    (hh : Integrable (fun t : ℝ=>besselSmoothingIntegrand F q V X ((hi:ℂ)+t*Complex.I))) :
    (∫t : ℝ,besselSmoothingIntegrand F q V X ((lo:ℂ)+t*Complex.I))=
      ∫t : ℝ,besselSmoothingIntegrand F q V X ((hi:ℂ)+t*Complex.I) := by
  obtain ⟨C,hC,hb⟩ := besselSmoothingIntegrand_strip_bound F q hq lo hi hF V a b ha hVs hV X hX
  apply VerticalContourShift.integral_eq_of_exponential_strip_growth
    (besselSmoothingIntegrand F q V X) lo hi (2*Real.pi) C hlh (by positivity) hC
  · intro z hz1 hz2
    exact (besselSmoothingIntegrand_differentiable F q hq hFe V a b ha hVs hV X hX) z
  · exact hl
  · exact hh
  · intro σ hσ t
    simpa only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_zero,add_zero,
      Complex.add_im,Complex.mul_im,mul_one,zero_add] using
      hb ((σ:ℂ)+t*Complex.I) (by simpa using hσ)

theorem completedT_mellin_shift (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (q : ℝ) (hq : 0<q)
    (hF : ∀s : ℂ,MellinConvergent (completedBesselProfile Ψ q) s)
    (hFe : Differentiable ℂ (mellin (completedBesselProfile Ψ q)))
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0<X) (lo : ℝ) (hl : lo≤2)
    (hleft : Integrable (fun t : ℝ=>
      besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((lo:ℂ)+t*Complex.I))) :
    completedT Ψ W X=(1/(2*Real.pi):ℂ)*∫t : ℝ,
      besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((lo:ℂ)+t*Complex.I) := by
  have hid (t : ℝ) :
      besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((2:ℂ)+t*Complex.I)=
      mellin (Vstar W) ((3/2:ℂ)+t*Complex.I)*(X:ℂ)^((3/2:ℂ)+t*Complex.I)*
        completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I) := by
    rw [besselSmoothingIntegrand,continuedBesselDirichlet_eq_initial Ψ hΨ q hq _ (by norm_num)]
    rw [show (2:ℂ)+t*Complex.I-1/2=3/2+t*Complex.I by ring]
  have hr : Integrable (fun t : ℝ=>
      besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((2:ℂ)+t*Complex.I)) := by
    simp only [hid]
    exact completedT_initial_mellin_integrable Ψ hΨ W a b ha hWs hW X hX
  have he := besselSmoothingIntegrand_contour_eq (completedBesselProfile Ψ q) q hq hF hFe
    (Vstar W) a b ha (Vstar_support W a b hWs) (Vstar_contDiff W a b ha hWs hW)
    X hX lo 2 hl hleft hr
  rw [he]
  simpa only [Complex.ofReal_ofNat,hid] using
    completedT_initial_mellin Ψ hΨ W a b ha hWs hW X hX

end CompletedGauss

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CompletedGauss
open CubicEisenstein

def besselReflectionFactor (q d : ℝ) (s : ℂ) : ℂ :=
  ((4*Real.pi*q:ℝ):ℂ)^(2*s+1)*(2:ℂ)^(2-4*s)/
    ((4*Real.pi*d:ℝ):ℂ)^(3-2*s)

lemma besselMellinFactor_reflection (q d : ℝ) (s : ℂ) :
    inverseBesselMellinFactor q s*besselMellinFactor d (1-s)=
      besselReflectionFactor q d s*CubicReflectionKernel.gammaMultiplier (1/2-s) := by
  have hp : (2:ℂ)^(1-2*s)*(2:ℂ)^(1-2*s)=(2:ℂ)^(2-4*s) := by
    rw [←Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    congr 1
    ring
  unfold inverseBesselMellinFactor besselMellinFactor besselReflectionFactor
    CubicReflectionKernel.gammaMultiplier
  rw [show (2:ℂ)*(1-s)-1=1-2*s by ring,
    show (2:ℂ)*(1-s)+1=3-2*s by ring,
    show (1:ℂ)-s+1/3=4/3-s by ring,
    show (1:ℂ)-s+2/3=5/3-s by ring,
    show (7/6:ℂ)+(1/2-s)=5/3-s by ring,
    show (5/6:ℂ)+(1/2-s)=4/3-s by ring,
    show (7/6:ℂ)-(1/2-s)=s+2/3 by ring,
    show (5/6:ℂ)-(1/2-s)=s+1/3 by ring]
  have he := congrArg (fun z : ℂ=>
    (((4*Real.pi*q:ℝ):ℂ)^(2*s+1)*
      (Complex.Gamma (s+1/3))⁻¹*(Complex.Gamma (s+2/3))⁻¹*
      Complex.Gamma (4/3-s)*Complex.Gamma (5/3-s)*
      (((4*Real.pi*d:ℝ):ℂ)^(3-2*s))⁻¹)*z) hp
  simp only [div_eq_mul_inv,mul_inv_rev] at he ⊢
  linear_combination he

lemma besselReflectionFactor_norm (q d : ℝ) (hq : 0<q) (hd : 0<d) (s : ℂ) :
    ‖besselReflectionFactor q d s‖=
      (4*Real.pi*q)^(2*s.re+1)*(2:ℝ)^(2-4*s.re)/
        (4*Real.pi*d)^(3-2*s.re) := by
  unfold besselReflectionFactor
  have h2 : ‖(2:ℂ)^(2-4*s)‖=(2:ℝ)^(2-4*s.re) := by
    simpa only [Complex.ofReal_ofNat,show (2-4*s).re=2-4*s.re by simp] using
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : 0<(2:ℝ)) (2-4*s)
  rw [norm_div,norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0<4*Real.pi*q),
    h2,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0<4*Real.pi*d)]
  norm_num

theorem continuedBesselDirichlet_reflection {α : Type*} [Countable α]
    (F : ℝ→ℂ) (r : α→ℝ) (hr : ∀i,0<r i) (a : α→ℂ)
    (q d Q : ℝ) (hd : 0<d) (hQ : 0<Q) (A : ℂ)
    (hreflect : ∀v : ℝ,0<v→F v=
      A*((v:ℂ)^(-2:ℂ)*radialBesselProfile r a d ((Q*v)⁻¹)))
    (s : ℂ) (hs : s.re<4/3)
    (ha : Summable (fun i=>‖a i‖*(r i)^(s.re-1/2))) :
    continuedBesselDirichlet F q s=
      (A*(Q:ℂ)^(2-2*s)*besselReflectionFactor q d s)*
        CubicReflectionKernel.gammaMultiplier (1/2-s)*
        (∑'i,a i*(r i:ℂ)^(s-1/2)) := by
  have hs' : -(1/3)<(1-s).re := by simp;linarith
  have ha' : Summable (fun i=>‖a i‖*(r i)^(1/2-(1-s).re)) := by
    convert ha using 1
    funext i
    congr 2
    simp
    ring
  have hm := radialBesselProfile_mellin r hr a d hd (1-s) hs' ha'
  have hc := cusp_mellin_reflection_of_identity F (radialBesselProfile r a d) A s Q hQ hreflect
  have hm' : mellin (radialBesselProfile r a d) (2-2*s)=
      besselMellinFactor d (1-s)*(∑'i,a i*(r i:ℂ)^(s-1/2)) := by
    calc
      _=mellin (radialBesselProfile r a d) (2*(1-s)) := by congr 1;ring
      _=_ := by simpa only [besselMellinFactor,show (1/2:ℂ)-(1-s)=s-1/2 by ring] using hm
  rw [hm'] at hc
  rw [continuedBesselDirichlet,hc]
  calc
    _=A*(Q:ℂ)^(2-2*s)*(inverseBesselMellinFactor q s*besselMellinFactor d (1-s))*
        (∑'i,a i*(r i:ℂ)^(s-1/2)) := by ring
    _=_ := by rw [besselMellinFactor_reflection];ring

end CompletedGauss

end

end OAI
end OAIOriginalModule0306

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.DualKernelSummability
Source SHA256: 0e698285af1dba4ade360062aa2095fe1f9ea45776cf7b656b2df0d26c7f2c8a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0307


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

namespace CompletedGauss
open scoped BigOperators Classical ContDiff
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "Eis" => ActualEisensteinCubic.O

lemma nonzeroDualIdeal_norm_pos (I : NonzeroDualIdeal) :
    0<(Ideal.absNorm I.val:ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.property)

lemma nonzeroDualIdeal_inv_pow_summable (n : ℕ) (hn : 1<n) :
    Summable (fun I : NonzeroDualIdeal => ((Ideal.absNorm I.val:ℝ)^n)⁻¹) := by
  have hs := (CubicEisenstein.fullIdealWeight_summable_norm (n:ℂ)
    (by exact_mod_cast hn)).subtype (fun I : Ideal Eis => I≠0)
  apply hs.congr
  intro I
  simp only [Function.comp_apply,CubicEisenstein.fullIdealWeight,ite_eq_right I.property,
    Complex.cpow_neg,Complex.cpow_natCast,norm_inv,norm_pow,Complex.norm_natCast]

def rawDualKernelTerm (V : ℝ→ℂ) (scale ρ q : ℝ)
    (β : ℕ→Ideal Eis→Ideal Eis→ℂ) (x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal) : ℂ :=
  β x.1 x.2.1.val x.2.2.val * CubicReflectionKernel.paperKernel V
    (scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3)

lemma rawDualKernel_inverse_square (scale ρ q : ℝ) (x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal) :
    ((scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3)^2)⁻¹ =
      (scale^2*ρ^6)⁻¹*((q^6)⁻¹)^x.1 *
        (((Ideal.absNorm x.2.1.val:ℝ)^2)⁻¹*((Ideal.absNorm x.2.2.val:ℝ)^6)⁻¹) := by
  simp only [mul_pow,mul_inv_rev,←pow_mul,←inv_pow]
  ring

theorem rawDualKernelTerm_summable_norm
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (scale ρ q B : ℝ) (hscale : 0<scale) (hρ : 0<ρ) (hq : 1<q)
    (hB : 0≤B) (β : ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hβ : ∀m,∀I J : NonzeroDualIdeal,‖β m I.val J.val‖≤B) :
    Summable (fun x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal =>
      ‖rawDualKernelTerm V scale ρ q β x‖) := by
  obtain ⟨C,hC,hdec⟩:=CubicReflectionKernel.paperKernel_euler_power_decay
    V a b ha hsupp hV 2 0
  have hq6 : 1<q^6 := one_lt_pow₀ hq (by norm_num)
  have hg : Summable (fun m : ℕ => ((q^6)⁻¹)^m) :=
    summable_geometric_of_lt_one (by positivity) ((inv_lt_one₀ (by positivity)).mpr hq6)
  have hi := nonzeroDualIdeal_inv_pow_summable 2 (by norm_num)
  have hj := nonzeroDualIdeal_inv_pow_summable 6 (by norm_num)
  have hij := hi.mul_of_nonneg hj (fun I=>by positivity) (fun J=>by positivity)
  have hs := hg.mul_of_nonneg hij (fun m=>by positivity) (fun IJ=>by positivity)
  have hmajor := hs.mul_left (B*C*(scale^2*ρ^6)⁻¹)
  apply hmajor.of_nonneg_of_le (fun _=>norm_nonneg _)
  intro x
  have hn:=nonzeroDualIdeal_norm_pos x.2.1
  have hb:=nonzeroDualIdeal_norm_pos x.2.2
  have hx : 0<scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3 := by positivity
  have hk := (hdec _ hx).2
  simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hk
  norm_num only [Nat.cast_ofNat] at hk
  have hr : (scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3)^(-(2:ℝ))=
      ((scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3)^2)⁻¹ := by
    rw [Real.rpow_neg hx.le,Real.rpow_two]
  rw [hr,rawDualKernel_inverse_square] at hk
  calc
    _ = ‖β x.1 x.2.1.val x.2.2.val‖*
        ‖CubicReflectionKernel.paperKernel V
          (scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3)‖ := by
        rw [rawDualKernelTerm,norm_mul]
    _ ≤ B*(C*((scale^2*ρ^6)⁻¹*((q^6)⁻¹)^x.1 *
        (((Ideal.absNorm x.2.1.val:ℝ)^2)⁻¹*((Ideal.absNorm x.2.2.val:ℝ)^6)⁻¹))) :=
      mul_le_mul (hβ x.1 x.2.1 x.2.2) hk (norm_nonneg _) hB
    _ = _ := by ring

end

section
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

lemma canonical_dual_kernel_argument (K Y ρ q : ℝ) (i : ℕ×ℕ×ℕ)
    (k n b : Ideal Eis) (hK : 0<K) (hk : k≠0) (hn : n≠0) (hb : b≠0) :
    (Y⁻¹*(ramifiedScale ρ q i.1)^3*((2:ℝ)^i.2.1)^3*(2:ℝ)^i.2.2)*
      Real.exp (-2*Real.log ((Ideal.absNorm k:ℝ)/K)+
        Real.log ((Ideal.absNorm n:ℝ)/(2:ℝ)^i.2.2)+
        3*Real.log ((Ideal.absNorm b:ℝ)/(2:ℝ)^i.2.1)) =
    (Y⁻¹*(K/(Ideal.absNorm k:ℝ))^2)*(ρ*q^i.1)^3*
      (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3 := by
  rw [positive_log_scale_identity _ _ _ _ _ _ _
    (nonzeroDualIdeal_norm_pos ⟨k,hk⟩) (nonzeroDualIdeal_norm_pos ⟨n,hn⟩)
    (nonzeroDualIdeal_norm_pos ⟨b,hb⟩) hK (by positivity) (by positivity)]
  unfold ramifiedScale
  field_simp

def canonicalRawBranchCoefficient {ι : Type*} [Fintype ι]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (ρ q : ℝ)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ) (σ : ℕ→ℂ) (k : Ideal Eis)
    (m : ℕ) (n b : Ideal Eis) : ℂ :=
  σ m*quadraticRow k (primaryGenerator (n*b))*
    reflectedDyadicCoefficient P hg j e (η m) (ramifiedScale ρ q m) n b

lemma canonicalRawBranchCoefficient_norm {ι : Type*} [Fintype ι]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (ρ q : ℝ) (hρ : 0<ρ) (hq : 1≤q)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ) (σ : ℕ→ℂ)
    (hη : ∀m,∀n b : NonzeroDualIdeal,‖η m n.val b.val‖≤1)
    (hσ : ∀m,‖σ m‖≤1) (k : Ideal Eis) (m : ℕ) (n b : NonzeroDualIdeal) :
    ‖canonicalRawBranchCoefficient P hg j e ρ q η σ k m n.val b.val‖≤1/ρ := by
  have hn:=norm_at_least_one n.val n.property
  have hb:=norm_at_least_one b.val b.property
  have hr:=ramifiedScale_pos ρ q hρ (lt_of_lt_of_le zero_lt_one hq) m
  have hc:=reflectedDyadicCoefficient_norm P hg j e (η m) (ramifiedScale ρ q m) 1 1
    hr (by norm_num) (by norm_num) n.val b.val n.property b.property (hη m n b)
    (by linarith) (by linarith)
  have hdiv (v : Fin 3) : 1≤(Ideal.absNorm (reflectionExtractedDivisor P j e v):ℝ) :=
    norm_at_least_one _ (reflectionExtractedDivisor_ne_zero P (fun i=>NeZero.ne (P i)) j e v)
  have hroot : 1≤Real.sqrt ((Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
      (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [hdiv 0,hdiv 2]
  have hrho : ρ≤ramifiedScale ρ q m := by
    exact le_mul_of_one_le_right hρ.le (one_le_pow₀ hq)
  have hden := hrho.trans (le_mul_of_one_le_right hr.le hroot)
  simp only [Real.sqrt_one,one_mul] at hc
  have hcoeff:=hc.trans (div_le_div_of_nonneg_left (by norm_num) hρ hden)
  rw [canonicalRawBranchCoefficient,norm_mul,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _) (hσ m)).trans (quadraticRow_norm_le_one _ _))).trans hcoeff

theorem reflectedBranchBlock_canonical {ι : Type*} [Fintype ι]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (W : ℝ→ℂ) (K Y ρ q : ℝ)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ) (σ : ℕ→idealRange K→ℂ)
    (i : ℕ×ℕ×ℕ) (k : idealRange K) (hK : 0<K)
    (hk : K/2≤(Ideal.absNorm k.val:ℝ)) :
    reflectedBranchBlock P hg j e W K Y ρ q
      (fun l=>dualIdealDyad l.2.2) (fun l=>dualIdealDyad l.2.1)
      (fun l=>η l.1) (fun l=>σ l.1) i k =
    ∑n : dualIdealDyad i.2.2, ∑b : dualIdealDyad i.2.1,
      rawDualKernelTerm (Vstar W) (Y⁻¹*(K/(Ideal.absNorm k.val:ℝ))^2) ρ q
        (canonicalRawBranchCoefficient P hg j e ρ q η (fun m=>σ m k) k.val)
        (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
          ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) := by
  have hkm:=mem_idealRange.mp k.property
  have hwk:=completedShellWindow_log (Ideal.absNorm k.val:ℝ) K
    (nonzeroDualIdeal_norm_pos ⟨k.val,hkm.1.1⟩) hK hk hkm.2
  simp only [reflectedBranchBlock,completedSmoothDyadicBlock,Finset.mul_sum]
  rw [←Finset.sum_coe_sort (dualIdealDyad i.2.2)]
  apply Finset.sum_congr rfl
  intro n _
  rw [←Finset.sum_coe_sort (dualIdealDyad i.2.1)]
  apply Finset.sum_congr rfl
  intro b _
  have hn:=dualIdealDyad_bounds _ n.val n.property
  have hb:=dualIdealDyad_bounds _ b.val b.property
  have hwn:=completedShellWindow_log (Ideal.absNorm n.val:ℝ) ((2:ℝ)^i.2.2)
    (nonzeroDualIdeal_norm_pos ⟨n.val,hn.1⟩) (by positivity) hn.2.1 hn.2.2
  have hwb:=completedShellWindow_log (Ideal.absNorm b.val:ℝ) ((2:ℝ)^i.2.1)
    (nonzeroDualIdeal_norm_pos ⟨b.val,hb.1⟩) (by positivity) hb.2.1 hb.2.2
  rw [hwk,hwn,hwb,canonical_dual_kernel_argument K Y ρ q i k.val n.val b.val hK hkm.1.1 hn.1 hb.1]
  simp only [rawDualKernelTerm,canonicalRawBranchCoefficient]
  ring

theorem canonicalRawBranch_summable_norm {ι : Type*} [Fintype ι]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (K Y ρ q : ℝ) (hK : 0<K) (hY : 0<Y) (hρ : 0<ρ) (hq : 1<q)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ) (σ : ℕ→ℂ)
    (hη : ∀m,∀n b : NonzeroDualIdeal,‖η m n.val b.val‖≤1)
    (hσ : ∀m,‖σ m‖≤1) (k : Ideal Eis) (hk : k≠0) :
    Summable (fun x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal =>
      ‖rawDualKernelTerm (Vstar W) (Y⁻¹*(K/(Ideal.absNorm k:ℝ))^2) ρ q
        (canonicalRawBranchCoefficient P hg j e ρ q η σ k) x‖) := by
  have hkn:=nonzeroDualIdeal_norm_pos ⟨k,hk⟩
  exact rawDualKernelTerm_summable_norm (Vstar W) a b ha (Vstar_support W a b hsupp)
    (Vstar_contDiff W a b ha hsupp hW) _ ρ q (1/ρ) (by positivity) hρ hq (by positivity)
    _ (fun m n b=>canonicalRawBranchCoefficient_norm P hg j e ρ q hρ hq.le η σ hη hσ k m n b)

theorem canonical_reflected_series {ι : Type*} [Fintype ι]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (K Y ρ q : ℝ) (hK : 0<K) (hY : 0<Y) (hρ : 0<ρ) (hq : 1<q)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ) (σ : ℕ→idealRange K→ℂ)
    (hη : ∀m,∀n b : NonzeroDualIdeal,‖η m n.val b.val‖≤1)
    (hσ : ∀m k,‖σ m k‖≤1) (k : idealRange K)
    (hk : K/2≤(Ideal.absNorm k.val:ℝ)) :
    (∑'i : ℕ×ℕ×ℕ, reflectedBranchBlock P hg j e W K Y ρ q
      (fun l=>dualIdealDyad l.2.2) (fun l=>dualIdealDyad l.2.1)
      (fun l=>η l.1) (fun l=>σ l.1) i k) =
    ∑'x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      rawDualKernelTerm (Vstar W) (Y⁻¹*(K/(Ideal.absNorm k.val:ℝ))^2) ρ q
        (canonicalRawBranchCoefficient P hg j e ρ q η (fun m=>σ m k) k.val) x := by
  have hs:=canonicalRawBranch_summable_norm P hg j e W a b ha hsupp hW K Y ρ q
    hK hY hρ hq η (fun m=>σ m k) hη (fun m=>hσ m k) k.val
    (mem_idealRange.mp k.property).1.1
  rw [tsum_dualIdealDyads _ hs.of_norm]
  apply tsum_congr
  intro i
  exact reflectedBranchBlock_canonical P hg j e W K Y ρ q η σ i k hK hk

end

open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

namespace ReflectedBranchData

def withCanonicalCuspArray {levelBound K : ℝ} {I F Q : Ideal Eis}
    (d : ReflectedBranchData levelBound K I F Q)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hη : ∀m,∀n b : NonzeroDualIdeal,‖η m n.val b.val‖≤1)
    (σ : ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hσ : ∀m k,‖σ m k‖≤1) : ReflectedBranchData levelBound K I F Q :=
  { d with
    nColumns := fun i=>dualIdealDyad i.2.2
    bColumns := fun i=>dualIdealDyad i.2.1
    nBounds := fun i n hn=>dualIdealDyad_bounds i.2.2 n hn
    bBounds := fun i b hb=>dualIdealDyad_bounds i.2.1 b hb
    amplitude := fun i=>η i.1
    amplitude_bound := fun i n hn b hb=>hη i.1
      ⟨n,((mem_dualIdealDyad _ _).mp hn).1⟩ ⟨b,((mem_dualIdealDyad _ _).mp hb).1⟩
    rowPhase := fun i=>σ i.1
    rowPhase_bound := fun i k=>hσ i.1 k }

def rawValue {levelBound K : ℝ} {I F Q : Ideal Eis}
    (d : ReflectedBranchData levelBound K I F Q)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ)
    (σ : ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) : ℂ := by
  letI : ∀p : d.primes,p.val.IsMaximal:=d.maximal
  exact ∑'x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
    rawDualKernelTerm (Vstar W)
      ((completedBranchScale K (X/d.levelScale) I F Q (fun p : d.primes=>p.val) d.label)⁻¹*
        (completedResidualScale K I Q/(Ideal.absNorm k.val:ℝ))^2) ρ q
      (canonicalRawBranchCoefficient (fun p : d.primes=>p.val) d.good
        (fun p=>completedLocalExponent I F p.val) d.label ρ q η (fun m=>σ m k) k.val) x

theorem withCanonicalCuspArray_value {levelBound K : ℝ} {I F Q : Ideal Eis}
    (d : ReflectedBranchData levelBound K I F Q)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hη : ∀m,∀n b : NonzeroDualIdeal,‖η m n.val b.val‖≤1)
    (σ : ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hσ : ∀m k,‖σ m k‖≤1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X ρ q : ℝ) (hX : 0<X) (hρ : 0<ρ) (hq : 1<q)
    (hK : 0<completedResidualScale K I Q)
    (k : idealRange (completedResidualScale K I Q))
    (hk : completedResidualScale K I Q/2≤(Ideal.absNorm k.val:ℝ)) :
    (d.withCanonicalCuspArray η hη σ hσ).value W X ρ q k =
      d.rawValue η σ W X ρ q k := by
  let : ∀p : d.primes,p.val.IsMaximal:=d.maximal
  have hn (J : Ideal Eis) (hJ : J≠0) : 0<(Ideal.absNorm J:ℝ) :=
    nonzeroDualIdeal_norm_pos ⟨J,hJ⟩
  have hprod:=hn (∏p : d.primes,p.val)
    (Finset.prod_ne_zero_iff.mpr (fun p _=>NeZero.ne p.val))
  have hd:=hn _ (reflectionExtractedDivisor_ne_zero (fun p : d.primes=>p.val)
    (fun p=>NeZero.ne p.val) (fun p=>completedLocalExponent I F p.val) d.label 1)
  have he:=hn _ (reflectionExtractedDivisor_ne_zero (fun p : d.primes=>p.val)
    (fun p=>NeZero.ne p.val) (fun p=>completedLocalExponent I F p.val) d.label 2)
  have hy : 0<completedBranchScale K (X/d.levelScale) I F Q
      (fun p : d.primes=>p.val) d.label := by
    unfold completedBranchScale
    have hl:=d.levelScale_pos
    positivity
  exact canonical_reflected_series (fun p : d.primes=>p.val) d.good
    (fun p=>completedLocalExponent I F p.val) d.label W a b ha hsupp hW
    (completedResidualScale K I Q)
    (completedBranchScale K (X/d.levelScale) I F Q (fun p : d.primes=>p.val) d.label)
    ρ q hK hy hρ hq η σ hη hσ k hk

def restrictRows {levelBound K : ℝ} {I F Q : Ideal Eis}
    (d : ReflectedBranchData levelBound K I F Q)
    (sector : idealRange (completedResidualScale K I Q)→Prop) :
    ReflectedBranchData levelBound K I F Q :=
  { d with
    rowPhase := fun i k=>if sector k then d.rowPhase i k else 0
    rowPhase_bound := by
      intro i k
      split_ifs
      · exact d.rowPhase_bound i k
      · simp }

theorem restrictRows_value {levelBound K : ℝ} {I F Q : Ideal Eis}
    (d : ReflectedBranchData levelBound K I F Q)
    (sector : idealRange (completedResidualScale K I Q)→Prop)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) :
    (d.restrictRows sector).value W X ρ q k =
      if sector k then d.value W X ρ q k else 0 := by
  by_cases hk:sector k
  · simp only [value,restrictRows,reflectedBranchBlock,ite_eq_left hk]
    rfl
  · simp only [value,restrictRows,reflectedBranchBlock,ite_eq_right hk,zero_mul,tsum_zero]

theorem sum_restrictRows_selected {ι : Type*} [Fintype ι] [DecidableEq ι]
    {levelBound K : ℝ} {I F Q : Ideal Eis}
    (d : ι→ReflectedBranchData levelBound K I F Q)
    (sector : idealRange (completedResidualScale K I Q)→ι)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) :
    (∑s : ι,((d s).restrictRows (fun k=>sector k=s)).value W X ρ q k)=
      (d (sector k)).value W X ρ q k := by
  calc
    _ = ((d (sector k)).restrictRows (fun k'=>sector k'=sector k)).value W X ρ q k := by
      apply Finset.sum_eq_single (sector k)
      · intro s _ hs
        rw [restrictRows_value,ite_eq_right (Ne.symm hs)]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    _ = _ := by rw [restrictRows_value,ite_eq_left rfl]

end ReflectedBranchData

end CompletedGauss

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance ramifiedFrequencyUnitsFintype : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

lemma ramifiedFrequencyChar_neg_unit (k:Eis) (u:Eisˣ) (n:ℕ) :
    ramifiedFrequencyChar k (-u) n=ramifiedFrequencyChar k u n := by
  ext x
  obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
  have hp:lambda^2∣(1+3*d)-1:=by
    rw [add_sub_cancel_left]
    exact dvd_mul_of_dvd_left lambda_sq_dvd_three d
  rw [ramifiedFrequencyChar_mk,ramifiedFrequencyChar_mk,Units.val_neg,neg_mul,
    symbol_neg_numerator _ _ hp]

lemma arithmeticResidueSum_neg_unit (h:Eis) (u:Eisˣ) (n:ℕ) (hn:2≤n) :
    arithmeticResidueSum (-h) (u.val*lambda^n)=
      arithmeticResidueSum h ((-u).val*lambda^n) := by
  by_cases hd:u.val*lambda^n∣3*(-h)
  · obtain ⟨k,hk⟩:=hd
    have hk':3*h=((-u).val*lambda^n)*k:=by
      simp only [Units.val_neg]
      linear_combination -hk
    rw [ramified_arithmetic_character_test (-h) k u n hn hk,
      ramified_arithmetic_character_test h k (-u) n hn hk',ramifiedFrequencyChar_neg_unit]
  · have hl:arithmeticResidueSum (-h) (u.val*lambda^n)=0:=by
      by_contra he
      exact hd (ramified_arithmetic_support (-h) u n hn he)
    have hr:arithmeticResidueSum h ((-u).val*lambda^n)=0:=by
      by_contra he
      obtain ⟨k,hk⟩:=ramified_arithmetic_support h (-u) n hn he
      apply hd
      refine ⟨k,?_⟩
      simp only [Units.val_neg] at hk
      linear_combination -hk
    rw [hl,hr]

lemma principalResidueTerm_neg (h:Eis) (u:Eisˣ) (n:ℕ) :
    principalResidueTerm (-h) u n=principalResidueTerm h (-u) n := by
  unfold principalResidueTerm
  rw [arithmeticResidueSum_neg_unit h u (n+2) (by omega)]
  congr 2
  simp only [Units.val_neg]
  ring

lemma principalArithmeticResidue_neg (h:Eis) :
    principalArithmeticResidue (-h)=principalArithmeticResidue h := by
  by_cases hh:h=0
  · rw [hh,neg_zero]
  let N:=max (ramifiedFrequencyBound (-h)+1) (ramifiedFrequencyBound h+1)
  rw [principalArithmeticResidue_eq_sum (-h) (neg_ne_zero.mpr hh) N (le_max_left _ _),
    principalArithmeticResidue_eq_sum h hh N (le_max_right _ _)]
  apply congrArg (fun z:ℂ=>z/((9*Real.sqrt 3/2:ℝ):ℂ))
  simp_rw [principalResidueTerm_neg]
  exact Fintype.sum_equiv (Equiv.neg Eisˣ)
    (fun u=>∑n∈Finset.range N,principalResidueTerm h (-u) n)
    (fun u=>∑n∈Finset.range N,principalResidueTerm h u n) (fun _=>rfl)

theorem sourceArithmeticResidue_neg (h:Eis) :
    sourceArithmeticResidue (-h)=sourceArithmeticResidue h := by
  have hU:unramifiedGaussResidue (-(9*h))=unramifiedGaussResidue (9*h):=by
    have he:=unramifiedGaussResidue_of_initial_relation (-(9*h)) (9*h) 0
      (fun _=>1) (fun _=>0) (fun _ _=>analyticAt_const) (fun _ _=>analyticAt_const)
      continuousAt_const continuousAt_const
      (fun s hs hi=>by simpa only [one_mul,zero_mul,add_zero] using unramifiedCubicGaussSeries_neg s (9*h))
    simpa only [one_mul,zero_mul,add_zero] using he
  simp only [sourceArithmeticResidue,cuspFrequency_neg,
    AddChar.map_neg_eq_inv,inv_eq_one,principalArithmeticResidue_neg,
    mul_neg,hU]

lemma cubicBesselNormalizer_neg (h:Eis) : cubicBesselNormalizer (-h)=cubicBesselNormalizer h := by
  simp only [cubicBesselNormalizer,cuspFrequency_neg,norm_neg]

theorem sourceResidualFourierCoefficient_neg (h:Eis) :
    sourceResidualFourierCoefficient (-h)=sourceResidualFourierCoefficient h := by
  rw [sourceResidualFourierCoefficient,sourceResidualFourierCoefficient,
    cubicBesselNormalizer_neg,sourceArithmeticResidue_neg]

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceRayPhase_eq_one_iff_coordinate (h:Eis) :
    ShortDraftTrace.breveE (cuspFrequency h)=1 ↔
      (3:ℤ)∣(ActualEisensteinCoordinates.coords h).2 := by
  have he:ShortDraftTrace.breveE (cuspFrequency h)=
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
        3 (by norm_num) (Ideal.Quotient.mk _ h):=by
    rw [eisTraceModChar,IdealGaussCRT.traceModChar_mk]
    unfold cuspFrequency
    simp only [map_ofNat]
  rw [he,trace_third_coordinate]
  simpa only [pow_zero,one_mul,Nat.cast_zero,zero_add] using
    omega3_pow_exp_eq_one_iff 0 (ActualEisensteinCoordinates.coords h).2

lemma primary_or_negative_primary_of_source_mask (h:Eis) (h3:¬(3:Eis)∣h)
    (hphase:ShortDraftTrace.breveE (cuspFrequency h)=1) :
    lambda^2∣h-1 ∨ lambda^2∣(-h)-1 := by
  let a:ℤ:=(ActualEisensteinCoordinates.coords h).1
  let b:ℤ:=(ActualEisensteinCoordinates.coords h).2
  have heval:h=(a:Eis)+(b:Eis)*omega:=
    (ActualEisensteinCoordinates.eval_coords h).symm
  obtain ⟨B,hB⟩:=(sourceRayPhase_eq_one_iff_coordinate h).mp hphase
  have hBc:(b:Eis)=3*(B:Eis):=by exact_mod_cast hB
  have ha:¬(3:ℤ)∣a:=by
    rintro ⟨A,hA⟩
    apply h3
    refine ⟨(A:Eis)+(B:Eis)*omega,?_⟩
    have hAc:(a:Eis)=3*(A:Eis):=by exact_mod_cast hA
    rw [heval,hAc,hBc]
    ring
  have hcases:(3:ℤ)∣a-1 ∨ (3:ℤ)∣a+1:=by omega
  rcases hcases with ⟨A,hA⟩|⟨A,hA⟩
  · left
    apply lambda_sq_dvd_three.trans
    refine ⟨(A:Eis)+(B:Eis)*omega,?_⟩
    have hAc:(a:Eis)-1=3*(A:Eis):=by exact_mod_cast hA
    rw [heval,hBc]
    linear_combination hAc
  · right
    apply lambda_sq_dvd_three.trans
    refine ⟨-((A:Eis)+(B:Eis)*omega),?_⟩
    have hAc:(a:Eis)+1=3*(A:Eis):=by exact_mod_cast hA
    rw [heval,hBc]
    linear_combination -hAc

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem sourceFourier_supported_three_of_base_zero (hC:infinityCoefficientScalar=0)
    (h:Eis) (h3:¬(3:Eis)∣h) : sourceResidualFourierCoefficient h=0 := by
  by_cases hm:ShortDraftTrace.breveE (cuspFrequency h)=1
  · rcases primary_or_negative_primary_of_source_mask h h3 hm with hh|hh
    · exact sourceFourier_primary_zero_of_base_zero hC h hh
    · rw [←sourceResidualFourierCoefficient_neg h]
      exact sourceFourier_primary_zero_of_base_zero hC (-h) hh
  · simp only [sourceResidualFourierCoefficient,sourceArithmeticResidue,ite_eq_right hm,mul_zero]

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

theorem infinityCoefficientScalar_ne_zero : infinityCoefficientScalar≠0 := by
  intro hC
  obtain ⟨h,h3,hn⟩:=exists_source_coefficient_not_three
  exact hn (sourceFourier_supported_three_of_base_zero hC h h3)

lemma sourceResidualFourierCoefficient_one_ne_zero : sourceResidualFourierCoefficient 1≠0 := by
  intro h
  exact infinityCoefficientScalar_ne_zero (by simp only [infinityCoefficientScalar,h,star_zero])

lemma sourceArithmeticResidue_one_ne_zero : sourceArithmeticResidue 1≠0 := by
  intro h
  exact sourceResidualFourierCoefficient_one_ne_zero (by rw [sourceResidualFourierCoefficient,h,mul_zero])

theorem normalized_infinityCoefficient_squarefree_cube (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) (hsq:Squarefree I) :
    infinityCoefficientScalar⁻¹*
      star (sourceResidualFourierCoefficient (primaryGenerator I*(primaryGenerator J)^3))=
      (‖eisEmbedding (primaryGenerator J)‖:ℂ)*
        star (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*gaussTwo I hI := by
  rw [infinityCoefficient_squarefree_cube I J hI hJ hsq]
  simp only [←mul_assoc,inv_mul_cancel₀ infinityCoefficientScalar_ne_zero,one_mul]

end CubicEisenstein

end

end OAI
end OAIOriginalModule0307

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.FiniteTranslations
Source SHA256: 433fc19b3771f3d14f595ec15f121fa25d1e579047291ee4ce8d8c6ef21f683e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0308



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

namespace CompletedGauss
open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

open CubicEisenstein

lemma positive_cpow_comp_continuous (r : ℝ) (hr : 0<r)
    (f : ℝ→ℂ) (hf : Continuous f) : Continuous (fun t=>(r:ℂ)^(f t)) := by
  let : NeZero (r:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hr.ne'⟩
  exact (_root_.continuous_const_cpow (r:ℂ)).comp hf

theorem besselSmoothingIntegrand_reflected_integrable {α : Type*} [Countable α]
    (F : ℝ→ℂ) (r : α→ℝ) (hr : ∀i,0<r i) (a : α→ℂ)
    (q d Q : ℝ) (hq : 0<q) (hd : 0<d) (hQ : 0<Q) (A : ℂ)
    (hreflect : ∀v : ℝ,0<v→F v=
      A*((v:ℂ)^(-2:ℂ)*radialBesselProfile r a d ((Q*v)⁻¹)))
    (has : Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V : ℝ→ℂ) (v0 v1 : ℝ) (hv0 : 0<v0)
    (hVs : Function.support V⊆Set.Icc v0 v1) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) :
    Integrable (fun t : ℝ=>besselSmoothingIntegrand F q V X ((-1:ℂ)+t*Complex.I)) := by
  let P : ℝ→ℂ := fun t=>
    A*(Q:ℂ)^(2-2*((-1:ℂ)+t*Complex.I))*
      besselReflectionFactor q d ((-1:ℂ)+t*Complex.I)*
        (X:ℂ)^(((-1:ℂ)+t*Complex.I)-1/2)
  let D : ℝ→ℂ := fun t=>∑'i,a i*(r i:ℂ)^(-((3/2:ℂ)+(-t)*Complex.I))
  let K : ℝ→ℂ := fun t=>CubicReflectionKernel.mellinEulerData V 0 ((3/2:ℂ)+(-t)*Complex.I)
  have hK : Integrable K := by
    have hh := CubicReflectionKernel.mellinEulerData_vertical_integrable V v0 v1 hv0 hVs hV
      2 0 (3/2) (by norm_num)
    simpa only [K,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_neg] using hh.comp_neg
  have hD : Continuous D := by
    have hh := (weighted_vertical_series_continuous r hr a (3/2) has).comp continuous_neg
    simpa only [D,Function.comp_def,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_neg] using hh
  have hDb (t : ℝ) : ‖D t‖≤∑'i,‖a i‖*(r i)^(-(3/2:ℝ)) := by
    simpa only [D,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_neg] using
      weighted_vertical_series_norm r hr a (3/2) has (-t)
  have hP : Continuous P := by
    have h1 := positive_cpow_comp_continuous Q hQ
      (fun t : ℝ=>2-2*((-1:ℂ)+t*Complex.I)) (by fun_prop)
    have h2 := positive_cpow_comp_continuous (4*Real.pi*q) (by positivity)
      (fun t : ℝ=>2*((-1:ℂ)+t*Complex.I)+1) (by fun_prop)
    have h3 := positive_cpow_comp_continuous 2 (by norm_num)
      (fun t : ℝ=>2-4*((-1:ℂ)+t*Complex.I)) (by fun_prop)
    have h4 := positive_cpow_comp_continuous (4*Real.pi*d) (by positivity)
      (fun t : ℝ=>3-2*((-1:ℂ)+t*Complex.I)) (by fun_prop)
    have h5 := positive_cpow_comp_continuous X hX
      (fun t : ℝ=>((-1:ℂ)+t*Complex.I)-1/2) (by fun_prop)
    have hn (t : ℝ) : (((4*Real.pi*d:ℝ):ℂ)^(3-2*((-1:ℂ)+t*Complex.I)))≠0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity)))
    convert (((continuous_const (y:=A)).mul h1).mul ((h2.mul h3).div h4 hn)).mul h5 using 1 ;
      (ext t; simp only [P,besselReflectionFactor,Pi.mul_apply,Pi.div_apply,Complex.ofReal_ofNat])
  have hPn (t : ℝ) : ‖P t‖=‖P 0‖ := by
    simp only [P,norm_mul,besselReflectionFactor_norm q d hq hd,
      Complex.norm_cpow_eq_rpow_re_of_pos hQ,Complex.norm_cpow_eq_rpow_re_of_pos hX]
    norm_num
  have hi := (hK.mul_bdd hP.aestronglyMeasurable
    (Eventually.of_forall (fun t=>(hPn t).le))).mul_bdd hD.aestronglyMeasurable
      (Eventually.of_forall hDb)
  apply hi.congr
  filter_upwards with t
  have he : ((-1:ℂ)+t*Complex.I).re-1/2=-(3/2:ℝ) := by norm_num
  have hsum : Summable (fun i=>‖a i‖*(r i)^(((-1:ℂ)+t*Complex.I).re-1/2)) := by
    simpa only [he] using has
  have href := continuedBesselDirichlet_reflection F r hr a q d Q hd hQ A hreflect
    ((-1:ℂ)+t*Complex.I) (by norm_num) hsum
  change K t*P t*D t=besselSmoothingIntegrand F q V X ((-1:ℂ)+t*Complex.I)
  rw [besselSmoothingIntegrand,href]
  dsimp only [K,P,D]
  unfold CubicReflectionKernel.mellinEulerData CubicReflectionKernel.mellinData
  simp only [pow_zero,one_mul]
  have he1 : (1/2:ℂ)-((-1:ℂ)+t*Complex.I)=(3/2:ℂ)+(-t)*Complex.I := by ring
  have he2 : ((-1:ℂ)+t*Complex.I)-1/2=-((3/2:ℂ)+(-t)*Complex.I) := by ring
  rw [he1,he2]
  ring

end CompletedGauss

namespace CubicEisenstein

section
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "Eis" => ActualEisensteinCubic.O

def finiteTranslationMultiplier {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (h : Eis) : ℂ :=
  ∑i,weight i*ShortDraftTrace.breveE (cuspFrequency h*shift i)

lemma finiteTranslationMultiplier_norm {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (h : Eis) :
    ‖finiteTranslationMultiplier shift weight h‖≤∑i,‖weight i‖ := by
  unfold finiteTranslationMultiplier
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul,breveE_norm,mul_one]

namespace SubexponentialBesselCoefficients

def finiteTranslate {ι : Type*} [Fintype ι] (coeff : SubexponentialBesselCoefficients)
    (shift weight : ι→ℂ) : SubexponentialBesselCoefficients where
  value h := finiteTranslationMultiplier shift weight h*coeff.value h
  growth epsilon he := by
    obtain ⟨C,hC,hbound⟩:=coeff.growth epsilon he
    refine ⟨(∑i,‖weight i‖)*C,by positivity,?_⟩
    intro h hh
    rw [norm_mul]
    calc
      _ ≤ (∑i,‖weight i‖)*(C*Real.exp (epsilon*‖cuspFrequency h‖)) :=
        mul_le_mul (finiteTranslationMultiplier_norm shift weight h) (hbound h hh)
          (norm_nonneg _) (Finset.sum_nonneg (fun _ _=>norm_nonneg _))
      _ = _ := by ring

lemma term_horizontal_translate (coeff : SubexponentialBesselCoefficients)
    (h : Eis) (v : ℝ) (z a : ℂ) :
    coeff.term h (v,z+a)=ShortDraftTrace.breveE (cuspFrequency h*a)*coeff.term h (v,z) := by
  by_cases hh:h=0
  · simp only [term,ite_eq_left hh,mul_zero]
  · simp only [term,ite_eq_right hh,mul_add,AddChar.map_add_eq_mul]
    ring

lemma finiteTranslate_term {ι : Type*} [Fintype ι]
    (coeff : SubexponentialBesselCoefficients) (shift weight : ι→ℂ)
    (h : Eis) (v : ℝ) (z : ℂ) :
    (coeff.finiteTranslate shift weight).term h (v,z)=
      ∑i,weight i*coeff.term h (v,z+shift i) := by
  simp_rw [term_horizontal_translate]
  rw [show (∑i,weight i*(ShortDraftTrace.breveE (cuspFrequency h*shift i)*coeff.term h (v,z)))=
      finiteTranslationMultiplier shift weight h*coeff.term h (v,z) by
    simp only [finiteTranslationMultiplier,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  by_cases hh:h=0
  · simp only [term,ite_eq_left hh,mul_zero]
  · simp only [term,ite_eq_right hh,finiteTranslate]
    ring

theorem finiteTranslate_series {ι : Type*} [Fintype ι]
    (coeff : SubexponentialBesselCoefficients) (shift weight : ι→ℂ)
    (v : ℝ) (hv : 0<v) (z : ℂ) :
    (coeff.finiteTranslate shift weight).series (v,z)=
      ∑i,weight i*coeff.series (v,z+shift i) := by
  simp only [series,finiteTranslate_term]
  rw [Summable.tsum_finsetSum (fun i hi=>(coeff.summable (v,z+shift i) hv).mul_left (weight i))]
  apply Finset.sum_congr rfl
  intro i hi
  exact tsum_mul_left

theorem finiteTranslate_fullFunction {ι : Type*} [Fintype ι]
    (coeff : SubexponentialBesselCoefficients) (shift weight : ι→ℂ) (constant : ℂ)
    (v : ℝ) (hv : 0<v) (z : ℂ) :
    (coeff.finiteTranslate shift weight).fullFunction ((∑i,weight i)*constant) (upperPoint z v hv)=
      ∑i,weight i*coeff.fullFunction constant (upperPoint (z+shift i) v hv) := by
  simp only [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint,
    finiteTranslate_series coeff shift weight v hv,Finset.sum_mul,mul_add,
    Finset.sum_add_distrib]
  have hconst : (∑i,weight i*constant*(v:ℂ)^(2/3:ℂ))=
      ∑i,constant*(v:ℂ)^(2/3:ℂ)*weight i := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hconst]
  ring_nf

end SubexponentialBesselCoefficients

theorem cubicSource_finite_translation {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) :
    (∑i,weight i*cubicSourceResidualFunction (upperPoint (z+shift i) v hv))=
      (sourceBesselCoefficients.finiteTranslate shift weight).fullFunction
        ((∑i,weight i)*((3*(Real.pi:ℂ))*constantArithmeticResidue)) (upperPoint z v hv) := by
  simp only [cubicSourceResidualFunction_eq_bessel,sourceBesselFunction]
  exact (sourceBesselCoefficients.finiteTranslate_fullFunction shift weight _ v hv z).symm

end

section
local notation "Eis" => ActualEisensteinCubic.O

def finiteAdditiveFourierCoeff {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (φ : R→ℂ) (h : R) : ℂ :=
  (∑x,φ x*ψ (-h*x))/(Fintype.card R:ℂ)

lemma finiteAdditiveFourier_inversion {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (φ : R→ℂ) (x : R) :
    (∑h,finiteAdditiveFourierCoeff ψ φ h*ψ (h*x))=φ x := by
  have hN : (Fintype.card R:ℂ)≠0:=by exact_mod_cast Fintype.card_ne_zero
  calc
    _ = (∑h,∑y,φ y*ψ (-h*y)*ψ (h*x))/(Fintype.card R:ℂ) := by
      simp only [finiteAdditiveFourierCoeff,div_mul_eq_mul_div,Finset.sum_mul,Finset.sum_div]
    _ = (∑y,φ y*∑h,ψ (h*(x-y)))/(Fintype.card R:ℂ) := by
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [mul_assoc,←AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = (∑y,φ y*(if x-y=0 then (Fintype.card R:ℂ) else 0))/(Fintype.card R:ℂ) := by
      simp only [AddChar.sum_mulShift _ hψ,apply_ite,Nat.cast_zero]
    _ = φ x := by
      have he : (∑y,φ y*(if x-y=0 then (Fintype.card R:ℂ) else 0))=
          φ x*(Fintype.card R:ℂ) := by
        simp [sub_eq_zero]
      rw [he,mul_div_cancel_right₀ _ hN]

lemma finiteAdditiveFourierCoeff_norm {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (φ : R→ℂ) (hφ : ∀x,‖φ x‖≤1) (h : R) :
    ‖finiteAdditiveFourierCoeff ψ φ h‖≤1 := by
  have hN : (0:ℝ)<Fintype.card R:=by exact_mod_cast Fintype.card_pos
  rw [finiteAdditiveFourierCoeff,norm_div,Complex.norm_natCast]
  apply (div_le_one hN).mpr
  calc
    _ ≤ ∑x,‖φ x*ψ (-h*x)‖ := norm_sum_le _ _
    _ ≤ ∑_x : R,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      simpa only [norm_mul,AddChar.norm_apply,mul_one] using hφ x
    _ = _ := by simp

def thetaFourierTranslation (c : Eis) (h : Eis⧸Ideal.span {c}) : ℂ :=
  ConcreteTraceCRT.eisLam^2*ConcreteTraceCRT.eisEmbedding (Quotient.out h)/
    ConcreteTraceCRT.eisEmbedding c

lemma thetaFourierTranslation_phase (c : Eis) (hc : c≠0)
    (h : Eis⧸Ideal.span {c}) (x : Eis) :
    ShortDraftTrace.breveE (-cuspFrequency x*thetaFourierTranslation c h)=
      quotientTrace c hc (h*Ideal.Quotient.mk _ x) := by
  have hm : h*Ideal.Quotient.mk _ x=Ideal.Quotient.mk _ (Quotient.out h*x) := by
    rw [map_mul,Ideal.Quotient.mk_out]
  rw [hm]
  simp only [quotientTrace,ConcreteTraceCRT.eisTraceModChar,IdealGaussCRT.traceModChar_mk]
  congr 1
  unfold cuspFrequency thetaFourierTranslation
  rw [map_mul]
  have hc0:=ConcreteTraceCRT.eisEmbedding_ne_zero hc
  have hl:=ConcreteTraceCRT.eisLam_ne_zero
  field_simp
  linear_combination -(ConcreteTraceCRT.eisEmbedding x*
    ConcreteTraceCRT.eisEmbedding (Quotient.out h))*TraceLambdaPhase.eisLam_sq

lemma thetaFourierTranslation_inversion (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (φ : (Eis⧸Ideal.span {c})→ℂ) (x : Eis) :
    (∑h,finiteAdditiveFourierCoeff (quotientTrace c hc) φ h*
      ShortDraftTrace.breveE (-cuspFrequency x*thetaFourierTranslation c h))=
      φ (Ideal.Quotient.mk _ x) := by
  simp only [thetaFourierTranslation_phase c hc]
  exact finiteAdditiveFourier_inversion (quotientTrace c hc)
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc) φ _

end

section
local notation "Eis" => ActualEisensteinCubic.O

lemma breveE_star (z : ℂ) : star (ShortDraftTrace.breveE z)=ShortDraftTrace.breveE (-z) := by
  change (starRingEnd ℂ) (Complex.exp (2*Real.pi*Complex.I*(z+starRingEnd ℂ z)))=
    Complex.exp (2*Real.pi*Complex.I*((-z)+starRingEnd ℂ (-z)))
  rw [←Complex.exp_conj]
  congr 1
  simp only [map_mul,map_add,map_neg,map_ofNat,Complex.conj_ofReal,Complex.conj_I,
    starRingEnd_self_apply]
  ring

lemma finiteTranslationMultiplier_star {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (h : Eis) :
    star (finiteTranslationMultiplier shift (fun i=>star (weight i)) h)=
      ∑i,weight i*ShortDraftTrace.breveE (-cuspFrequency h*shift i) := by
  simp only [finiteTranslationMultiplier,star_sum,star_mul,star_star,breveE_star,neg_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma finiteTranslate_term_multiplier {ι : Type*} [Fintype ι]
    (coeff : SubexponentialBesselCoefficients) (shift weight : ι→ℂ)
    (h : Eis) (v : ℝ) (z : ℂ) :
    (coeff.finiteTranslate shift weight).term h (v,z)=
      finiteTranslationMultiplier shift weight h*coeff.term h (v,z) := by
  by_cases hh:h=0
  · simp only [SubexponentialBesselCoefficients.term,ite_eq_left hh,mul_zero]
  · simp only [SubexponentialBesselCoefficients.term,ite_eq_right hh,
      SubexponentialBesselCoefficients.finiteTranslate]
    ring

def finiteConjugateSource {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) : ℂ :=
  ∑i,weight i*cubicSourceConjugateFunction (upperPoint (z+shift i) v hv)

lemma finiteConjugateSource_eq_bessel {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) :
    finiteConjugateSource shift weight v hv z=
      star ((sourceBesselCoefficients.finiteTranslate shift (fun i=>star (weight i))).fullFunction
        ((∑i,star (weight i))*((3*(Real.pi:ℂ))*constantArithmeticResidue)) (upperPoint z v hv)) := by
  rw [sourceBesselCoefficients.finiteTranslate_fullFunction]
  simp only [star_sum,star_mul,star_star,finiteConjugateSource,cubicSourceConjugateFunction,
    cubicSourceResidualFunction_eq_bessel,sourceBesselFunction]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem finiteConjugateSource_wirtingerBar {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerBar (finiteConjugateSource shift weight v hv) z=
      ∑'h : Eis,(-2*Real.pi*Complex.I*star (cuspFrequency h))*
        (∑i,weight i*ShortDraftTrace.breveE (-cuspFrequency h*shift i))*
          star (sourceBesselCoefficients.term h (v,z)) := by
  have hf : finiteConjugateSource shift weight v hv = fun z=>
      star ((sourceBesselCoefficients.finiteTranslate shift (fun i=>star (weight i))).fullFunction
        ((∑i,star (weight i))*((3*(Real.pi:ℂ))*constantArithmeticResidue)) (upperPoint z v hv)) :=
    funext (finiteConjugateSource_eq_bessel shift weight v hv)
  rw [hf,horizontalWirtingerBar_star,
    SubexponentialBesselCoefficients.fullFunction_wirtingerZ,tsum_star]
  apply tsum_congr
  intro h
  rw [finiteTranslate_term_multiplier,star_mul,star_mul,finiteTranslationMultiplier_star]
  have hphase : star (2*Real.pi*Complex.I*cuspFrequency h)=
      -2*Real.pi*Complex.I*star (cuspFrequency h) := by
    simp only [star_mul,Complex.star_def,map_ofNat,Complex.conj_ofReal,Complex.conj_I]
    ring
  rw [hphase]
  ring

def traceTwistedConjugateSource (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (φ : (Eis⧸Ideal.span {c})→ℂ)
    (v : ℝ) (hv : 0<v) (z : ℂ) : ℂ :=
  finiteConjugateSource (thetaFourierTranslation c)
    (finiteAdditiveFourierCoeff (quotientTrace c hc) φ) v hv z

theorem traceTwistedConjugateSource_wirtingerBar (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (φ : (Eis⧸Ideal.span {c})→ℂ)
    (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerBar (traceTwistedConjugateSource c hc φ v hv) z=
      ∑'h : Eis,(-2*Real.pi*Complex.I*star (cuspFrequency h))*
        φ (Ideal.Quotient.mk _ h)*star (sourceBesselCoefficients.term h (v,z)) := by
  change horizontalWirtingerBar (finiteConjugateSource (thetaFourierTranslation c)
    (finiteAdditiveFourierCoeff (quotientTrace c hc) φ) v hv) z = _
  rw [finiteConjugateSource_wirtingerBar]
  simp only [thetaFourierTranslation_inversion c hc]

theorem traceTwistedConjugateSource_wirtingerBar_zero (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (φ : (Eis⧸Ideal.span {c})→ℂ)
    (v : ℝ) (hv : 0<v) :
    horizontalWirtingerBar (traceTwistedConjugateSource c hc φ v hv) 0=
      ∑'h : Eis,(-2*Real.pi*Complex.I*star (cuspFrequency h))*
        φ (Ideal.Quotient.mk _ h)*star (sourceResidualFourierCoefficient h)*
          (v:ℂ)*schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v) := by
  rw [traceTwistedConjugateSource_wirtingerBar]
  apply tsum_congr
  intro h
  by_cases hh:h=0
  · subst h
    simp [cuspFrequency]
  · rw [sourceBesselCoefficients.term_bessel h hh v hv]
    have hx : 0<4*Real.pi*‖cuspFrequency h‖*v :=
      mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos)
        (norm_pos_iff.mpr (cuspFrequency_ne_zero h hh))) hv
    rw [schlafliBesselK_cubic_real _ hx]
    have he0 : ShortDraftTrace.breveE (0:ℂ)=1 := by
      simp [ShortDraftTrace.breveE]
    simp only [mul_zero,he0,mul_one,star_mul,
      Complex.star_def,Complex.conj_ofReal,sourceBesselCoefficients]
    ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def fixedThetaTwist (Ψ : Eis→*ℂ) (x : Eis) : ℂ :=
  if lambda^2∣x-1 then eisEmbedding (symbol ramifiedTraceLambda x)*Ψ x else 0

lemma fixedThetaTwist_primary (Ψ : Eis→*ℂ) (x : Eis) (hx : lambda^2∣x-1) :
    fixedThetaTwist Ψ x=eisEmbedding (symbol ramifiedTraceLambda x)*Ψ x := by
  simp only [fixedThetaTwist,ite_eq_left hx]

lemma fixedThetaTwist_not_primary (Ψ : Eis→*ℂ) (x : Eis) (hx : ¬lambda^2∣x-1) :
    fixedThetaTwist Ψ x=0 := by
  simp only [fixedThetaTwist,ite_eq_right hx]

lemma paperLambda_symbol_cube (x : Eis) (hx : lambda^2∣x-1) :
    (eisEmbedding (symbol ramifiedTraceLambda x))^3=1 := by
  rw [←map_pow,symbol_cube_of_isCoprime _ _ hx
    (ramified_character_coprime 0 1 _ x (Or.inl (by simp)) hx),map_one]

lemma paperLambda_symbol_norm (x : Eis) (hx : lambda^2∣x-1) :
    ‖eisEmbedding (symbol ramifiedTraceLambda x)‖=1 := by
  apply (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3:ℕ)≠0)).mp
  simpa only [norm_pow,norm_one,one_pow] using congrArg norm (paperLambda_symbol_cube x hx)

lemma fixedThetaTwist_norm_le_one (Ψ : Eis→*ℂ) (hΨ : ∀x,‖Ψ x‖≤1) (x : Eis) :
    ‖fixedThetaTwist Ψ x‖≤1 := by
  by_cases hx : lambda^2∣x-1
  · rw [fixedThetaTwist_primary Ψ x hx,norm_mul,paperLambda_symbol_norm x hx,one_mul]
    exact hΨ x
  · rw [fixedThetaTwist_not_primary Ψ x hx,norm_zero]
    norm_num

theorem fixedThetaTwist_periodic (Ψ : Eis→*ℂ) (Q : Ideal Eis)
    (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ) (x y : Eis)
    (hxy : x-y∈Ideal.span {(9:Eis)}*Q) : fixedThetaTwist Ψ x=fixedThetaTwist Ψ y := by
  have h9 : (9:Eis)∣x-y := Ideal.mem_span_singleton.mp (Ideal.mul_le_left hxy)
  have hd : lambda^2∣x-y := lambda_sq_dvd_three.trans ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9)
  have hp : lambda^2∣x-1 ↔ lambda^2∣y-1 := by
    constructor
    · intro hx
      convert dvd_sub hx hd using 1 ; ring
    · intro hy
      convert dvd_add hd hy using 1 ; ring
  by_cases hx : lambda^2∣x-1
  · have hy := hp.mp hx
    rw [fixedThetaTwist_primary Ψ x hx,fixedThetaTwist_primary Ψ y hy,
      hΨ x y (Ideal.mul_le_right hxy)]
    congr 2
    exact CubicRamified.symbol_traceLambda_congr_mod_nine x y hx hy h9
  · rw [fixedThetaTwist_not_primary Ψ x hx,
      fixedThetaTwist_not_primary Ψ y (fun hy=>hx (hp.mpr hy))]

def fixedThetaQuotient (Ψ : Eis→*ℂ) (c : Eis) (x : Eis⧸Ideal.span {c}) : ℂ :=
  fixedThetaTwist Ψ (Quotient.out x)

lemma fixedThetaQuotient_mk (Ψ : Eis→*ℂ) (Q : Ideal Eis)
    (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ) (c : Eis)
    (hc : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q) (x : Eis) :
    fixedThetaQuotient Ψ c (Ideal.Quotient.mk _ x)=fixedThetaTwist Ψ x := by
  apply fixedThetaTwist_periodic Ψ Q hΨ
  exact hc (Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk (Ideal.span {c}) x)))

lemma fixedThetaQuotient_norm_le_one (Ψ : Eis→*ℂ) (hΨ : ∀x,‖Ψ x‖≤1)
    (c : Eis) (x : Eis⧸Ideal.span {c}) : ‖fixedThetaQuotient Ψ c x‖≤1 :=
  fixedThetaTwist_norm_le_one Ψ hΨ _

lemma paperLambda_symbol_squarefree_cube (n b : Eis) (hb : lambda^2∣b-1) :
    eisEmbedding (symbol ramifiedTraceLambda (n*b^3))=
      eisEmbedding (symbol ramifiedTraceLambda n) := by
  rw [symbol_mul_denominator,cubicSymbol_pow_denominator,map_mul,map_pow,
    paperLambda_symbol_cube b hb,mul_one]

theorem fixedThetaTwist_infinity_coefficient (Ψ : Eis→*ℂ) (I J : Ideal Eis)
    (hI : primaryGenerator I≠0) (hJ : primaryGenerator J≠0) (hsq : Squarefree I) :
    infinityCoefficientScalar⁻¹ *
      star (sourceResidualFourierCoefficient (primaryGenerator I*(primaryGenerator J)^3))*
        fixedThetaTwist Ψ (primaryGenerator I*(primaryGenerator J)^3)=
      (‖eisEmbedding (primaryGenerator J)‖:ℂ)*gaussTwo I hI*
        Ψ (primaryGenerator I)*(Ψ (primaryGenerator J))^3 := by
  have hn := (primaryGenerator_spec I hI).2
  have hb := (primaryGenerator_spec J hJ).2
  have hnb : lambda^2∣primaryGenerator I*(primaryGenerator J)^3-1 :=
    CubicJacobiGlobal.primary_mul _ _ hn (primary_pow_congruence _ hb 3)
  rw [normalized_infinityCoefficient_squarefree_cube I J hI hJ hsq,
    fixedThetaTwist_primary Ψ _ hnb,paperLambda_symbol_squarefree_cube _ _ hb,map_mul,map_pow]
  have hunit : star (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*
      eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I))=1 := by
    simpa only [Complex.star_def,paperLambda_symbol_norm _ hn,one_pow,
      Complex.ofReal_one] using Complex.conj_mul' (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))
  calc
    _ = (star (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*
        eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*
        ((‖eisEmbedding (primaryGenerator J)‖:ℂ)*gaussTwo I hI*
          Ψ (primaryGenerator I)*(Ψ (primaryGenerator J))^3) := by ring
    _ = _ := by rw [hunit,one_mul]

end

open ActualEisensteinCubic CompletedGauss CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceFourier_primary_squarefree_cube_preimage (x:Eis)
    (hx:lambda^2∣x-1) (hT:sourceResidualFourierCoefficient x≠0) :
    ∃p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
      {J:Ideal Eis // primaryGenerator J≠0}),
      primaryGenerator p.1.val*(primaryGenerator p.2.val)^3=x := by
  have hx0:x≠0:=primary_ne_zero x hx
  have hgen:primaryGenerator (Ideal.span {x})=x:=primaryGenerator_span x hx0 hx
  have hg:primaryGenerator (Ideal.span {x})≠0:=by rwa [hgen]
  have ht:sourceResidualFourierCoefficient (primaryGenerator (Ideal.span {x}))≠0:=by
    rwa [hgen]
  obtain ⟨I,J,hI,hgI,hgJ,hIJ⟩:=sourceFourier_squarefree_cube_support (Ideal.span {x}) hg ht
  refine ⟨(⟨I,hI,hgI⟩,⟨J,hgJ⟩),?_⟩
  have he:=congrArg primaryGenerator hIJ
  simpa only [primaryGenerator_mul,primaryGenerator_pow,hgen] using he

theorem sourceFourier_tsum_primary_pairs (w:Eis→ℂ)
    (hw:∀x:Eis,w x≠0→lambda^2∣x-1) :
    (∑'x:Eis,w x*star (sourceResidualFourierCoefficient x))=
      ∑'p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
        {J:Ideal Eis // primaryGenerator J≠0}),
        w (primaryGenerator p.1.val*(primaryGenerator p.2.val)^3)*
          star (sourceResidualFourierCoefficient
            (primaryGenerator p.1.val*(primaryGenerator p.2.val)^3)) := by
  let P:=({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
    {J:Ideal Eis // primaryGenerator J≠0})
  let phi:P→Eis:=fun p=>primaryGenerator p.1.val*(primaryGenerator p.2.val)^3
  let f:Eis→ℂ:=fun x=>w x*star (sourceResidualFourierCoefficient x)
  change (∑'x:Eis,f x)=∑'p:P,f (phi p)
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun p:Function.support (fun p:P=>f (phi p))=>phi p.val)
  · exact primary_squarefree_cube_injective.comp Subtype.val_injective
  · intro x hx
    have hwx:w x≠0:=by
      intro hz
      exact hx (by simp only [f,hz,zero_mul])
    have hTx:sourceResidualFourierCoefficient x≠0:=by
      intro hz
      exact hx (by simp only [f,hz,star_zero,mul_zero])
    obtain ⟨p,hp⟩:=sourceFourier_primary_squarefree_cube_preimage x (hw x hwx) hTx
    have hphi:phi p=x:=hp
    have hfp:f (phi p)≠0:=by rwa [hphi]
    exact ⟨⟨p,hfp⟩,hphi⟩
  · intro p
    rfl

end CubicEisenstein

end

end OAI
end OAIOriginalModule0308

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.MellinSupport
Source SHA256: f1421d1fb2a954d78b1f618d85156aca861ee8fb97a5eb41b7cf24b4fff3b429
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0309


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

namespace CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma cubeWeight_zero_of_primaryGenerator_zero (Ψ:Eis→*ℂ) (I:Ideal Eis)
    (h:primaryGenerator I=0) : cubeWeight Ψ I=0 := by
  simp [cubeWeight,h,FiniteGaussPhase.angularFactor]

lemma completedMellinCoefficient_support (Ψ:Eis→*ℂ) (p:CompletedMellinIndex)
    (hp:completedMellinCoefficient Ψ p≠0) :
    Squarefree p.1.val ∧ primaryGenerator p.1.val≠0 ∧ primaryGenerator p.2.val≠0 := by
  have hleft:Squarefree p.1.val ∧ primaryGenerator p.1.val≠0 := by
    by_contra hh
    apply hp
    simp only [completedMellinCoefficient,columnWeight,squarefreeGaussCoefficient,
      dite_eq_right hh,zero_mul,zero_div]
  refine ⟨hleft.1,hleft.2,?_⟩
  intro hright
  apply hp
  rw [completedMellinCoefficient,cubeWeight_zero_of_primaryGenerator_zero Ψ _ hright,mul_zero]

lemma completedMellinCoefficient_zero_off_support (Ψ:Eis→*ℂ) (p:CompletedMellinIndex)
    (hp:¬(Squarefree p.1.val ∧ primaryGenerator p.1.val≠0 ∧ primaryGenerator p.2.val≠0)) :
    completedMellinCoefficient Ψ p=0 := by
  by_contra hn
  exact hp (completedMellinCoefficient_support Ψ p hn)

def primaryCubePairToMellinIndex
    (p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
      {J:Ideal Eis // primaryGenerator J≠0})) : CompletedMellinIndex :=
  (⟨p.1.val,p.1.property.1.ne_zero⟩,
    ⟨p.2.val,primaryGenerator_ne_zero_ideal p.2.val p.2.property⟩)

lemma primaryCubePairToMellinIndex_injective : Function.Injective primaryCubePairToMellinIndex := by
  intro p q hpq
  exact Prod.ext
    (Subtype.ext (congrArg (fun x:CompletedMellinIndex=>x.1.val) hpq))
    (Subtype.ext (congrArg (fun x:CompletedMellinIndex=>x.2.val) hpq))

theorem completedMellinCoefficient_tsum_primary_pairs (Ψ:Eis→*ℂ)
    (w:CompletedMellinIndex→ℂ) :
    (∑'p:CompletedMellinIndex,completedMellinCoefficient Ψ p*w p)=
      ∑'p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
        {J:Ideal Eis // primaryGenerator J≠0}),
        completedMellinCoefficient Ψ (primaryCubePairToMellinIndex p)*
          w (primaryCubePairToMellinIndex p) := by
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun p=>primaryCubePairToMellinIndex p.val)
  · exact primaryCubePairToMellinIndex_injective.comp Subtype.val_injective
  · intro p hp
    change completedMellinCoefficient Ψ p*w p≠0 at hp
    have hc:completedMellinCoefficient Ψ p≠0 := by
      intro hz
      exact hp (by rw [hz,zero_mul])
    obtain ⟨hs,hI,hJ⟩:=completedMellinCoefficient_support Ψ p hc
    let q:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
      {J:Ideal Eis // primaryGenerator J≠0}):=(⟨p.1.val,hs,hI⟩,⟨p.2.val,hJ⟩)
    have hq:primaryCubePairToMellinIndex q=p := by
      exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
    refine ⟨⟨q,?_⟩,hq⟩
    change completedMellinCoefficient Ψ (primaryCubePairToMellinIndex q)*
      w (primaryCubePairToMellinIndex q)≠0
    simpa only [hq] using hp
  · intro p
    rfl

theorem completedBesselProfile_primary_pairs (Ψ:Eis→*ℂ) (q v:ℝ) :
    completedBesselProfile Ψ q v=
      ∑'p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
        {J:Ideal Eis // primaryGenerator J≠0}),
        (completedMellinCoefficient Ψ (primaryCubePairToMellinIndex p)*
          (completedMellinLength (primaryCubePairToMellinIndex p):ℂ))*(v:ℂ)*
            CubicEisenstein.schlafliBesselK (1/3)
              (4*Real.pi*q*Real.sqrt (completedMellinLength (primaryCubePairToMellinIndex p))*v) := by
  unfold completedBesselProfile CubicEisenstein.radialBesselProfile
  simpa only [mul_assoc] using completedMellinCoefficient_tsum_primary_pairs Ψ
    (fun p=>(completedMellinLength p:ℂ)*(v:ℂ)*CubicEisenstein.schlafliBesselK (1/3)
      (4*Real.pi*q*Real.sqrt (completedMellinLength p)*v))

end CompletedGauss

namespace CubicEisenstein
open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology MatrixGroups

section
open CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

lemma cubicSourceConjugateFunction_levelTwo (G:levelTwo) (w:HyperbolicSpace) :
    cubicSourceConjugateFunction (integralComplexMatrix (G:SL(2,Eis)) • w)=
      star (levelTwoComplexCharacter G)*cubicSourceConjugateFunction w := by
  simp only [cubicSourceConjugateFunction,cubicSourceResidualFunction_automorphy,star_mul]
  ring

theorem cubicSourceConjugateFunction_cuspDerivative_levelTwo (G:levelTwo)
    (g H:SL(2,ℂ)) (hfactor:g=integralComplexMatrix (G:SL(2,Eis))*H)
    (hc:g 1 0≠0) (v:ℝ) (hv:0<v) :
    horizontalWirtingerBar (fun z=>cubicSourceConjugateFunction (upperPoint z v hv)) (g 0 0/g 1 0)=
      (star (levelTwoComplexCharacter G)*(-1/((g 1 0)^2*(v:ℂ)^2)))*
        horizontalWirtingerZ
          (fun z=>cubicSourceConjugateFunction (H • upperPoint z (1/(‖g 1 0‖^2*v)) (by positivity)))
          (-g 1 1/g 1 0) := by
  refine cuspDerivative_of_transform cubicSourceConjugateFunction g H
    (star (levelTwoComplexCharacter G)) ?_ hc v hv ?_
  · intro w
    rw [hfactor,mul_smul,cubicSourceConjugateFunction_levelTwo]
  · exact cubicSourceConjugateFunction_translate_split_differentiableAt H _ (by positivity)

lemma cuspBarProfile_conjugate_reflection_levelTwo (G:levelTwo)
    (g H:SL(2,ℂ)) (hfactor:g=integralComplexMatrix (G:SL(2,Eis))*H)
    (hc:g 1 0≠0) (v:ℝ) (hv:0<v) :
    cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0) v=
      reflectedCuspProfile (-star (levelTwoComplexCharacter G)/(g 1 0)^2)
        (‖g 1 0‖^2)
        (cuspZProfile (fun w=>cubicSourceConjugateFunction (H • w)) (-g 1 1/g 1 0)) v := by
  have hdual:0<(‖g 1 0‖^2*v)⁻¹ := by positivity
  rw [cuspBarProfile_positive _ _ _ hv,reflectedCuspProfile,cuspZProfile_positive _ _ _ hdual]
  have he:=cubicSourceConjugateFunction_cuspDerivative_levelTwo G g H hfactor hc v hv
  have hp:(v:ℂ)^(-2:ℂ)=((v:ℂ)^2)⁻¹ := by
    rw [Complex.cpow_neg,Complex.cpow_ofNat]
  rw [hp]
  simp only [one_div] at he
  rw [he]
  ring

lemma conjugateSource_cuspRepresentative_zProfile_decay (j:Fin 3) (z:ℂ) :
    ∃deltaLoss:ℝ,0<deltaLoss ∧ cuspZProfile (fun w=>cubicSourceConjugateFunction
      (integralComplexMatrix (cuspRepresentative j) • w)) z
        =O[atTop] (fun v:ℝ=>Real.exp (-deltaLoss*v)) := by
  fin_cases j
  · refine ⟨residualCuspDecayRate,residualCuspDecayRate_pos,?_⟩
    simpa [cuspRepresentative,cuspParameter,lowerCuspMatrix_zero]
      using cuspZProfile_conjugate_isBigO z
  · refine ⟨residualCuspDecayRate/3,div_pos residualCuspDecayRate_pos (by norm_num),?_⟩
    simpa [cuspRepresentative,cuspParameter,ramifiedCuspRoot,ramifiedOmegaUnit_val]
      using ramifiedConjugate_zProfile_isBigO false z
  · refine ⟨residualCuspDecayRate/3,div_pos residualCuspDecayRate_pos (by norm_num),?_⟩
    simpa [cuspRepresentative,cuspParameter,ramifiedCuspRoot,ramifiedOmegaUnit_val]
      using ramifiedConjugate_zProfile_isBigO true z

theorem conjugateSource_levelTwo_three_cusp_mellin_entire (G:levelTwo)
    (j:Fin 3) (g:SL(2,ℂ))
    (hfactor:g=integralComplexMatrix (G:SL(2,Eis))*integralComplexMatrix (cuspRepresentative j))
    (hc:g 1 0≠0) :
    ((∀s:ℂ,MellinConvergent
      (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0)) s) ∧
      Differentiable ℂ (mellin (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0)))) ∧
    ((∀s:ℂ,MellinConvergent
      (cuspZProfile (fun w=>cubicSourceConjugateFunction
        (integralComplexMatrix (cuspRepresentative j) • w)) (-g 1 1/g 1 0)) s) ∧
      Differentiable ℂ (mellin
        (cuspZProfile (fun w=>cubicSourceConjugateFunction
          (integralComplexMatrix (cuspRepresentative j) • w)) (-g 1 1/g 1 0)))) := by
  have hchar:levelTwoComplexCharacter G≠0 := by
    intro hz
    have hn:=norm_levelTwoComplexCharacter G
    rw [hz,norm_zero] at hn
    exact zero_ne_one hn
  have hscalar:-star (levelTwoComplexCharacter G)/(g 1 0)^2≠0 :=
    div_ne_zero (neg_ne_zero.mpr (star_ne_zero.mpr hchar)) (pow_ne_zero 2 hc)
  obtain ⟨deltaLoss,hδ,hb⟩:=conjugateSource_cuspRepresentative_zProfile_decay j (-g 1 1/g 1 0)
  exact cusp_mellin_entire_both
    (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0))
    (cuspZProfile (fun w=>cubicSourceConjugateFunction
      (integralComplexMatrix (cuspRepresentative j) • w)) (-g 1 1/g 1 0))
    (-star (levelTwoComplexCharacter G)/(g 1 0)^2) hscalar (‖g 1 0‖^2)
    residualCuspDecayRate deltaLoss (sq_pos_of_pos (norm_pos_iff.mpr hc)) residualCuspDecayRate_pos hδ
    (cuspBarProfile_conjugate_continuousOn _) (cuspZProfile_conjugate_translate_continuousOn _ _)
    (cuspBarProfile_conjugate_isBigO _) hb
    (fun v hv=>cuspBarProfile_conjugate_reflection_levelTwo G g _ hfactor hc v hv)

end

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma upper_triangular_right_cusp_ratio (g T:SL(2,ℂ)) (hT:T 1 0=0)
    (hc:(g*T) 1 0≠0) :
    g 1 0≠0 ∧ (g*T) 0 0/(g*T) 1 0=g 0 0/g 1 0 := by
  have hcol (i:Fin 2) : (g*T) i 0=g i 0*T 0 0 := by
    change (∑k:Fin 2,g i k*T k 0)=_
    rw [Fin.sum_univ_two,hT,mul_zero,add_zero]
  have hn:g 1 0*T 0 0≠0:=by rwa [hcol] at hc
  have hg: g 1 0≠0:=(mul_ne_zero_iff.mp hn).1
  have ht:T 0 0≠0:=(mul_ne_zero_iff.mp hn).2
  refine ⟨hg,?_⟩
  rw [hcol,hcol]
  field_simp

theorem conjugateSource_integral_cusp_mellin_entire (M:SL(2,Eis)) (hc:M 1 0≠0) :
    (∀s:ℂ,MellinConvergent
      (cuspBarProfile cubicSourceConjugateFunction
        (eisEmbedding (M 0 0)/eisEmbedding (M 1 0))) s) ∧
    Differentiable ℂ (mellin (cuspBarProfile cubicSourceConjugateFunction
      (eisEmbedding (M 0 0)/eisEmbedding (M 1 0)))) := by
  obtain ⟨G,j,T,hT,_,_,hM⟩:=three_cusp_decomposition M
  let g:SL(2,ℂ):=integralComplexMatrix (G:SL(2,Eis))*integralComplexMatrix (cuspRepresentative j)
  have he:integralComplexMatrix M=g*integralComplexMatrix T:=by
    rw [hM,map_mul,map_mul]
  have ht:integralComplexMatrix T 1 0=0:=by
    rw [integralComplexMatrix_apply,hT,map_zero]
  have hmc:(g*integralComplexMatrix T) 1 0≠0:=by
    rw [←he,integralComplexMatrix_apply]
    exact eisEmbedding_ne_zero hc
  obtain ⟨hg,hratio⟩:=upper_triangular_right_cusp_ratio g (integralComplexMatrix T) ht hmc
  have hresult:=(conjugateSource_levelTwo_three_cusp_mellin_entire G j g rfl hg).1
  rw [←hratio,←he] at hresult
  simpa only [integralComplexMatrix_apply] using hresult

lemma exists_integral_matrix_cusp_ratio (a c:Eis) (hc:c≠0) :
    ∃M:SL(2,Eis),M 1 0≠0 ∧
      eisEmbedding (M 0 0)/eisEmbedding (M 1 0)=eisEmbedding a/eisEmbedding c := by
  let d:Eis:=IsBezout.gcd a c
  obtain ⟨a',ha⟩:=IsBezout.gcd_dvd_left a c
  obtain ⟨c',hc'⟩:=IsBezout.gcd_dvd_right a c
  change a=d*a' at ha
  change c=d*c' at hc'
  have hd:d≠0:=by
    intro hz
    exact hc (by rw [hc',hz,zero_mul])
  have hcp:c'≠0:=by
    intro hz
    exact hc (by rw [hc',hz,mul_zero])
  obtain ⟨u,v,huv⟩:=IsBezout.gcd_eq_sum a c
