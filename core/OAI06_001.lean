        rw [div_eq_mul_inv,norm_mul]
        exact (mul_le_mul (ht' k 2) hv (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
      linarith
    _ = _ := by norm_num

include hc in
theorem rowClosedMarked_first_region (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) (hxw : 1≤x.re+w.re) (j : ℕ) (hj : j<6) :
    ‖rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j‖≤128 := by
  have h02 := rowBaseFinite_first_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz hxw j 0 2 hj (by omega)
  have h10 := rowBaseFinite_first_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz hxw j 1 0 hj (by omega)
  have h01 := rowBaseFinite_first_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz hxw j 0 1 hj (by omega)
  have h11 := rowBaseFinite_first_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz hxw j 1 1 hj (by omega)
  have hr := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_R_half _ hQ a x z ha hx hz)
  simp only [Complex.ofReal_natCast] at hr
  unfold rowClosedMarked
  rw [div_eq_mul_inv,norm_mul]
  apply (mul_le_mul_of_nonneg_right
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add h02 h10)) h01)) h11)) (norm_nonneg _)).trans
  nlinarith

include hc in
theorem ramifiedClosed_first_region_bound (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) (hxw : 1≤x.re+w.re) (j : ℕ) (hj : j<6) :
    ‖ramifiedClosed p hp hg eta a rho x w z j‖≤193 := by
  have hb := rowClosedMarked_first_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz hxw j hj
  have hv := first_region_V_half _ hQ z hz
  have hs := norm_sub_le (1:ℂ) (coordV (Ideal.absNorm (Ideal.span {p})) z)
  simp only [norm_one] at hs
  unfold ramifiedClosed
  apply (norm_add_le _ _).trans
  rw [norm_one,norm_mul]
  have hm := mul_le_mul (show ‖1-coordV (Ideal.absNorm (Ideal.span {p})) z‖≤3/2 by linarith)
    hb (norm_nonneg _) (by norm_num : (0:ℝ)≤3/2)
  linarith

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1411

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedTerms
Source SHA256: afe6f02b31c606603f877cd12146ce8c7f73ffe2b97d24f47e41a2619c22ab39
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1412


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
lemma sourceRowTerm_norm_from_scalar_power (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (j e l k m : ℕ) (nu B : ℝ)
    (hs : ‖sourceScalar p hp hg (e+3*l) k (j+6*m)‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^nu)
    (he : nu-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)≤B) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^B := by
  have hP : Prime (Ideal.span {p}:Ideal O) := Ideal.prime_span_singleton_iff.mpr hp
  have hQ2 : (2:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le ⟨_,hP⟩
  have hQ : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hrho := Complex.norm_eq_one_of_pow_eq_one hρ (by decide : (6:ℕ)≠0)
  rw [sourceRowTerm,norm_mul,norm_div,norm_pow,norm_pow,hrho,one_pow,one_pow,div_self (by norm_num : (1:ℝ)≠0),one_mul]
  apply (sourceWeightedScalar_norm_le _ hQ eta a _ _ _ x w z _ heta ha
    (localGamma_norm_one p hp.ne_zero hg hc 1 (by decide) (by decide))
    (by rw [norm_star];exact localGamma_norm_one p hp.ne_zero hg hc 3 (by decide) (by decide))
    (Complex.norm_eq_one_of_pow_eq_one (actualSextic_neg_one_sq _ hg) (by decide)) e l k m).trans
  calc
    _ ≤ (2*(Ideal.absNorm (Ideal.span {p}):ℝ)^nu)*
      (Ideal.absNorm (Ideal.span {p}):ℝ)^(-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = 2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(nu-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)) := by
      rw [mul_assoc,←Real.rpow_add hQ]
      congr 2
      ring
    _ ≤ 2*(Ideal.absNorm (Ideal.span {p}):ℝ)^B := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.rpow_le_rpow_of_exponent_le (show (1:ℝ)≤Ideal.absNorm (Ideal.span {p}) by linarith) he

include hc in
theorem sourceRowTerm_selected_base (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (_hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (j e l k m : ℕ) (hj : j<6) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ : 0<Q := by
    dsimp only [Q]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hm0 : (0:ℝ)≤m := Nat.cast_nonneg m
  have hb0 : (0:ℝ)≤max (1-w.re) 0 := le_max_right _ _
  have hb1 : 1-w.re≤max (1-w.re) 0 := le_max_left _ _
  have hzm : 0≤6*z.re*(m:ℝ) := by positivity
  have hzm1 (hm : m≠0) : 6*z.re≤6*z.re*(m:ℝ) := by
    have hm1 : (1:ℝ)≤m := by exact_mod_cast (by omega : 1≤m)
    nlinarith
  have hrelax (v : ℝ) : Q^v≤2*Q^v := by nlinarith [Real.rpow_nonneg hQ.le v]
  have hz0 (t k : ℕ) (ht : t≠0) : sourceScalar p hp hg t k (j+6*m)=
      positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (t-1) k (j+6*m) := by
    rw [sourceScalar,ite_eq_right ht]
  rcases hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · by_cases hm : m=0
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 2 0 m 5 (-x.re+max (1-w.re) 0)
        · have hs := even_base_kzero_norm p hp hg hc m j hj
          rw [ite_eq_left hm] at hs
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 0 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^5≤2*Q^5 by nlinarith [pow_nonneg hQ.le 5])
        · norm_num only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,sub_zero]
          linarith
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 2 0 m 6 (-x.re+max (1-w.re) 0)
        · have hs := even_base_kzero_norm p hp hg hc m j hj
          rw [ite_eq_right hm] at hs
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 0 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^6≤2*Q^6 by nlinarith [pow_nonneg hQ.le 6])
        · norm_num only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,sub_zero]
          nlinarith [hzm1 hm]
    · by_cases hm : m=0
      · subst m
        simp only [sourceRowTerm,sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,
          Nat.reduceEqDiff,ite_false,mul_zero,add_zero,even_base_kone_zero p hp hg hc j hj,
          sourceWeightedScalar,zero_mul,mul_zero,norm_zero]
        positivity
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 2 1 m 6 (-x.re+max (1-w.re) 0)
        · have hs := nonprincipal_kone_norm p hp hg hc 5 (j+6*m) (by decide) (by decide)
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^6≤2*Q^6 by nlinarith [pow_nonneg hQ.le 6])
        · norm_num only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,sub_zero]
          nlinarith [hzm1 hm]
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 0 0 m (1/2) (-x.re+max (1-w.re) 0)
      · have hs := nonprincipal_kzero_norm p hp hg hc 0 (j+6*m) (by decide)
        simp only [pow_zero,one_mul,Real.sqrt_eq_rpow] at hs
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 1 0 (by decide),Nat.reduceSub] using hs.trans (hrelax (1/2))
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 0 1 m (3/2) (-x.re+max (1-w.re) 0)
      · have hs := positiveScalar_norm_le p hp hg hc 0 1 (j+6*m) (by decide)
        simp only [Nat.zero_add,pow_one] at hs
        have he : 2*Q*Real.sqrt Q=2*Q^(3/2:ℝ) := by
          have ht := pow_mul_sqrt Q hQ 1
          norm_num at ht
          rw [mul_assoc,ht]
        rw [he] at hs
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 1 1 (by decide),Nat.reduceSub] using hs
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 1 0 m (5/2) (-x.re+max (1-w.re) 0)
      · have hs := nonprincipal_kzero_norm p hp hg hc 2 (j+6*m) (by decide)
        rw [pow_mul_sqrt _ hQ] at hs
        norm_num only [Nat.cast_ofNat] at hs
        convert hs.trans (hrelax (5/2)) using 1 ;
          simp only [sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceEqDiff,ite_false,Nat.reduceSub]
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 1 1 m 3 (-x.re+max (1-w.re) 0)
      · have hs := nonprincipal_kone_norm p hp hg hc 2 (j+6*m) (by decide) (by decide)
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 3 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
          hs.trans (show Q^3≤2*Q^3 by nlinarith [pow_nonneg hQ.le 3])
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 1 0 m (7/2) (-x.re+max (1-w.re) 0)
      · have hs := nonprincipal_kzero_norm p hp hg hc 3 (j+6*m) (by decide)
        rw [pow_mul_sqrt _ hQ] at hs
        norm_num only [Nat.cast_ofNat] at hs
        convert hs.trans (hrelax (7/2)) using 1 ;
          simp only [sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceEqDiff,ite_false,Nat.reduceSub]
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 1 1 m 4 (-x.re+max (1-w.re) 0)
      · have hs := nonprincipal_kone_norm p hp hg hc 3 (j+6*m) (by decide) (by decide)
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 4 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
          hs.trans (show Q^4≤2*Q^4 by nlinarith [pow_nonneg hQ.le 4])
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1412

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsCentralStrict
Source SHA256: 4c4cbd363da475961b016844b8bb21776ac3551e63be9316d32d87df59360e49
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1413


namespace OAI

noncomputable section
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
include hc in
lemma squarefree_base_boundary_norm (j : ℕ) (hj : j≤1) :
    ‖positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 0 1 j‖≤
      Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) := by
  have he := row_squarefree_kone p hp hg hc 0 0 j (by omega)
  norm_num only [Nat.mul_zero,zero_add,mul_zero,add_zero,pow_zero,one_mul] at he
  rw [he,ite_eq_right (by omega)]
  split_ifs
  · rw [norm_mul,norm_mul,norm_inv,
      Complex.norm_eq_one_of_pow_eq_one (actualSextic_neg_one_sq _ hg) (by decide),
      inv_one,one_mul,primeGauss_actual_norm p hp.ne_zero hg hc]
    norm_num
  · simp only [mul_zero,norm_zero]
    positivity

include hc in
lemma squarefree_base_strict_norm (j : ℕ) (hj : j<6) :
    ‖positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 0 1 j‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ)^(3/2:ℝ) := by
  have he := row_squarefree_kone p hp hg hc 0 0 j hj
  norm_num only [Nat.mul_zero,zero_add,mul_zero,add_zero,pow_zero,one_mul] at he
  have hQ : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hQ1 : (1:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by
    have hh := SmoothMobiusCorrection.prime_norm_two_le
      ⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩
    change 2≤Ideal.absNorm (Ideal.span {p}) at hh
    exact_mod_cast (show 1≤Ideal.absNorm (Ideal.span {p}) by omega)
  have hfac : ‖if 1<j then (Ideal.absNorm (Ideal.span {p}):ℂ)-1 else if j=1 ∧ True then -(1:ℂ) else 0‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    split_ifs
    · rw [←Complex.ofReal_natCast,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (by linarith)]
      linarith
    · simpa using hQ1
    · simp
  rw [he,norm_mul,norm_mul,norm_inv,
    Complex.norm_eq_one_of_pow_eq_one (actualSextic_neg_one_sq _ hg) (by decide),
    inv_one,one_mul,primeGauss_actual_norm p hp.ne_zero hg hc]
  calc
    _≤Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ)*(Ideal.absNorm (Ideal.span {p}):ℝ) :=
      mul_le_mul_of_nonneg_left hfac (Real.sqrt_nonneg _)
    _=(Ideal.absNorm (Ideal.span {p}):ℝ)^(3/2:ℝ) := by
      rw [mul_comm]
      convert ProbeEuler.pow_mul_sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) hQ 1 using 1 <;> norm_num
end SevenEighths.ProbePrimePower
end

end OAI
end OAIOriginalModule1413

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsCentralEntry
Source SHA256: 0d39c172997b49257e34fdb76f412399c4f203be884369727dc1e3fba979ac4c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1414


namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
lemma sourceRowTerm_central_strict_norm (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1) (j : ℕ) (hj : j<6) :
    ‖sourceRowTerm p hp hg eta a rho x w z j 1 0 1 0‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1-x.re-w.re) := by
  apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ
    j 1 0 1 0 (3/2) (1-x.re-w.re)
  · have hb := squarefree_base_strict_norm p hp hg hc j hj
    have ht : 0≤(Ideal.absNorm (Ideal.span {p}):ℝ)^(3/2:ℝ) := by positivity
    simpa only [sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,ite_false,
      Nat.reduceEqDiff,mul_zero,add_zero] using hb.trans (show _≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(3/2:ℝ) by linarith)
  · norm_num ; linarith

include hc in
lemma sourceRowTerm_central_boundary_norm (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1) (j : ℕ) (hj : j≤1) :
    ‖sourceRowTerm p hp hg eta a rho x w z j 1 0 1 0‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re-w.re) := by
  apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ
    j 1 0 1 0 (1/2) (-x.re-w.re)
  · have hb := squarefree_base_boundary_norm p hp hg hc j hj
    rw [Real.sqrt_eq_rpow] at hb
    have ht : 0≤(Ideal.absNorm (Ideal.span {p}):ℝ)^(1/2:ℝ) := by positivity
    simpa only [sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,ite_false,
      Nat.reduceEqDiff,mul_zero,add_zero] using hb.trans (show _≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1/2:ℝ) by linarith)
  · norm_num
end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1414

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsCentralTerms
Source SHA256: 1dc96de56d0f64bba14ba663b728aba48943aaa3ce25cc8b0dfb6e1f2e3eb987
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1415


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
theorem sourceRowTerm_central_nonstrict (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j e l k m : ℕ) (hj : j<6) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1))
    (hstrict : ¬(e=1 ∧ l=0 ∧ k=1 ∧ m=0)) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1/2-x.re) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ : 0<Q := by
    dsimp only [Q]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hm0 : (0:ℝ)≤m := Nat.cast_nonneg m
  have hzpos : 0<z.re := by rw [hz];norm_num
  have hzm : 0≤6*z.re*(m:ℝ) := by positivity
  have hzm1 (hm : m≠0) : 6*z.re≤6*z.re*(m:ℝ) := by
    have hm1 : (1:ℝ)≤m := by exact_mod_cast (by omega : 1≤m)
    nlinarith
  have hrelax (v : ℝ) : Q^v≤2*Q^v := by nlinarith [Real.rpow_nonneg hQ.le v]
  have hz0 (t k : ℕ) (ht : t≠0) : sourceScalar p hp hg t k (j+6*m)=
      positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (t-1) k (j+6*m) := by
    rw [sourceScalar,ite_eq_right ht]
  rcases hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · by_cases hm : m=0
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 2 0 m 5 (1/2-x.re)
        · have hs := even_base_kzero_norm p hp hg hc m j hj
          rw [ite_eq_left hm] at hs
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 0 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^5≤2*Q^5 by nlinarith [pow_nonneg hQ.le 5])
        · norm_num only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,sub_zero]
          linarith
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 2 0 m 6 (1/2-x.re)
        · have hs := even_base_kzero_norm p hp hg hc m j hj
          rw [ite_eq_right hm] at hs
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 0 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^6≤2*Q^6 by nlinarith [pow_nonneg hQ.le 6])
        · norm_num only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,sub_zero]
          nlinarith [hzm1 hm]
    · by_cases hm : m=0
      · subst m
        simp only [sourceRowTerm,sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,
          Nat.reduceEqDiff,ite_false,mul_zero,add_zero,even_base_kone_zero p hp hg hc j hj,
          sourceWeightedScalar,zero_mul,mul_zero,norm_zero]
        positivity
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 2 1 m 6 (1/2-x.re)
        · have hs := nonprincipal_kone_norm p hp hg hc 5 (j+6*m) (by decide) (by decide)
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^6≤2*Q^6 by nlinarith [pow_nonneg hQ.le 6])
        · norm_num only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,sub_zero]
          nlinarith [hzm1 hm]
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 0 0 m (1/2) (1/2-x.re)
      · have hs := nonprincipal_kzero_norm p hp hg hc 0 (j+6*m) (by decide)
        simp only [pow_zero,one_mul,Real.sqrt_eq_rpow] at hs
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 1 0 (by decide),Nat.reduceSub] using hs.trans (hrelax (1/2))
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
    · have hm : m≠0 := by intro hm;exact hstrict ⟨rfl,rfl,rfl,hm⟩
      apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 0 1 m (3/2) (1/2-x.re)
      · have hs := positiveScalar_norm_le p hp hg hc 0 1 (j+6*m) (by decide)
        simp only [Nat.zero_add,pow_one] at hs
        have he : 2*Q*Real.sqrt Q=2*Q^(3/2:ℝ) := by
          have ht := pow_mul_sqrt Q hQ 1
          norm_num at ht
          rw [mul_assoc,ht]
        rw [he] at hs
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 1 1 (by decide),Nat.reduceSub] using hs
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        nlinarith [hzm1 hm]
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 1 0 m (5/2) (1/2-x.re)
      · have hs := nonprincipal_kzero_norm p hp hg hc 2 (j+6*m) (by decide)
        rw [pow_mul_sqrt _ hQ] at hs
        norm_num only [Nat.cast_ofNat] at hs
        convert hs.trans (hrelax (5/2)) using 1 ;
          simp only [sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceEqDiff,ite_false,Nat.reduceSub]
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 1 1 m 3 (1/2-x.re)
      · have hs := nonprincipal_kone_norm p hp hg hc 2 (j+6*m) (by decide) (by decide)
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 3 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
          hs.trans (show Q^3≤2*Q^3 by nlinarith [pow_nonneg hQ.le 3])
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 1 0 m (7/2) (1/2-x.re)
      · have hs := nonprincipal_kzero_norm p hp hg hc 3 (j+6*m) (by decide)
        rw [pow_mul_sqrt _ hQ] at hs
        norm_num only [Nat.cast_ofNat] at hs
        convert hs.trans (hrelax (7/2)) using 1 ;
          simp only [sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceEqDiff,ite_false,Nat.reduceSub]
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 1 1 m 4 (1/2-x.re)
      · have hs := nonprincipal_kone_norm p hp hg hc 3 (j+6*m) (by decide) (by decide)
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 4 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
          hs.trans (show Q^4≤2*Q^4 by nlinarith [pow_nonneg hQ.le 4])
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1415

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsCentralBase
Source SHA256: 763b0be49968c271226bbac5a96dc6e2e8bf7d5a973754091e6513afc61e4d38
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1416


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
lemma rowBaseFinite_central_remainder (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j e l : ℕ) (hj : j<6)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let T := fun k m=>rowMarkedTerm p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j e l k m
    ‖rowBaseFinite p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j e l-
      (if e=1 ∧ l=0 then T 1 0 else 0)‖≤16*Q^(1/2-x.re) := by
  dsimp only
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  let T := fun k m=>rowMarkedTerm p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j e l k m
  have hpow : 0≤Q^(1/2-x.re) := by positivity
  have hv := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_V_half _ hQ z (by rw [hz]))
  have ht (k m : ℕ) (hk : k≤1) (hstrict : ¬(e=1 ∧ l=0 ∧ k=1 ∧ m=0)) :
      ‖T k m‖≤2*Q^(1/2-x.re) := by
    have ht0 : e+3*l≠0 := by rcases hf with h|h|h|h <;> omega
    dsimp only [T,Q]
    simp only [Complex.ofReal_natCast]
    rw [←sourceRowTerm_pos p hp hg eta a rho x w z j e l k m ht0]
    exact sourceRowTerm_central_nonstrict p hp hg hc eta a rho x w z alpha eps
      heta ha hρ halpha halpha1 heps heps1 hx hw hz j e l k m hj hk hf hstrict
  have hd (k : ℕ) (hk : k≤1) : ‖T k 2/(1-coordV Q z)‖≤4*Q^(1/2-x.re) := by
    rw [div_eq_mul_inv,norm_mul]
    exact (mul_le_mul (ht k 2 hk (by omega)) hv (norm_nonneg _) (by positivity)).trans_eq (by ring)
  by_cases hb : e=1 ∧ l=0
  · rw [ite_eq_left hb]
    have hid : rowBaseFinite p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j e l-T 1 0=
        ((T 0 0+T 0 1+T 0 2/(1-coordV Q z))+T 1 1)+T 1 2/(1-coordV Q z) := by
      simp only [rowBaseFinite,Fin.sum_univ_two]
      dsimp only [T]
      norm_num only [Fin.val_zero,Fin.val_one]
      ring
    change ‖rowBaseFinite p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j e l-T 1 0‖≤_
    rw [hid]
    have h00 := ht 0 0 (by omega) (by omega)
    have h01 := ht 0 1 (by omega) (by omega)
    have h11 := ht 1 1 (by omega) (by omega)
    have hn := (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h00 h01)) (hd 0 (by omega)))) h11)) (hd 1 (by omega)))
    exact hn.trans (by linarith)
  · rw [ite_eq_right hb,sub_zero]
    unfold rowBaseFinite
    apply (norm_sum_le _ _).trans
    calc
      _≤∑ _k : Fin 2,8*Q^(1/2-x.re) := by
        apply Finset.sum_le_sum
        intro k hk
        have h0 := ht k.val 0 (by omega) (by tauto)
        have h1 := ht k.val 1 (by omega) (by omega)
        exact ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h0 h1)) (hd k.val (by omega)))).trans_eq (by ring)
      _=16*Q^(1/2-x.re) := by simp;ring

include hc in
theorem rowClosedMarked_central_remainder (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let R := evenRatio Q a ((Q:ℂ)^(-x)) (coordV Q z)
    let T := rowMarkedTerm p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j 1 0 1 0
    ‖rowClosedMarked p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j-T/(1-R)‖≤
      128*Q^(1/2-x.re) := by
  dsimp only
  have h02 := rowBaseFinite_central_remainder p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ halpha halpha1 heps heps1 hx hw hz j 0 2 hj (by omega)
  have h10 := rowBaseFinite_central_remainder p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ halpha halpha1 heps heps1 hx hw hz j 1 0 hj (by omega)
  have h01 := rowBaseFinite_central_remainder p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ halpha halpha1 heps heps1 hx hw hz j 0 1 hj (by omega)
  have h11 := rowBaseFinite_central_remainder p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ halpha halpha1 heps heps1 hx hw hz j 1 1 hj (by omega)
  dsimp only at h02 h10 h01 h11
  norm_num only [and_true,true_and,and_false,false_and,Nat.reduceEqDiff,ite_true,ite_false,sub_zero] at h02 h10 h01 h11
  have hr := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_R_half _ hQ a x z ha (by rw [hx];linarith) (by rw [hz]))
  simp only [Complex.ofReal_natCast] at *
  unfold rowClosedMarked
  rw [←sub_div,div_eq_mul_inv,norm_mul]
  have heq (A B C D T : ℂ) : A+B+C+D-T=A+(B-T)+C+D := by ring
  rw [heq]
  apply (mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h02 h10)) h01)) h11)) (norm_nonneg _)).trans
  calc
    _≤(16*(_ : ℝ)+16*_+16*_+16*_)*2 := mul_le_mul_of_nonneg_left hr (by positivity)
    _=_ := by ring
end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1416

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsCentralDefect
Source SHA256: 8c28ef550ba8b3e5d607fd48f4fc95def6a27d2818c46833909573df240d34cd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1417



namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
include hc in
lemma rowClosedMarked_central_size (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    ‖rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j‖≤
      132*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-10*eps) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ1 : 1≤Q := by dsimp [Q];linarith
  have hrem := rowClosedMarked_central_remainder p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  dsimp only at hrem
  simp only [Complex.ofReal_natCast] at hrem
  have ht := sourceRowTerm_central_strict_norm p hp hg hc eta a rho x w z heta ha hρ j hj
  rw [sourceRowTerm_pos p hp hg eta a rho x w z j 1 0 1 0 (by omega)] at ht
  have hr := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_R_half _ hQ a x z ha (by rw [hx];linarith) (by rw [hz]))
  have he : Q^(1-x.re-w.re)=Q^(-10*eps) := by congr 1;rw [hx,hw];ring
  have hn : Q^(1/2-x.re)≤Q^(-10*eps) := Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hx];linarith)
  have hdiv : ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV Q z) rho j 1 0 1 0 /
      (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV Q z))‖≤4*Q^(-10*eps) := by
    rw [div_eq_mul_inv,norm_mul]
    have hh := mul_le_mul ht hr (norm_nonneg _) (by positivity)
    exact hh.trans_eq (by change (2*Q^(1-x.re-w.re))*2=4*Q^(-10*eps);rw [he];ring)
  dsimp only [Q] at hdiv
  have hh := (norm_add_le _ _).trans (add_le_add hrem hdiv)
  simp only [sub_add_cancel] at hh
  exact hh.trans (by change 128*Q^(1/2-x.re)+4*Q^(-10*eps)≤132*Q^(-10*eps);nlinarith)

include hc in
theorem ramifiedClosed_central_defect (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    ‖ramifiedClosed p hp hg eta a rho x w z j-1‖≤
      198*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-10*eps) := by
  have hb := rowClosedMarked_central_size p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  have hv := first_region_V_half _ hQ z (by rw [hz])
  have hs := norm_sub_le (1:ℂ) (coordV (Ideal.absNorm (Ideal.span {p})) z)
  rw [norm_one] at hs
  unfold ramifiedClosed
  rw [add_sub_cancel_left,norm_mul]
  apply (mul_le_mul (show ‖1-coordV (Ideal.absNorm (Ideal.span {p})) z‖≤3/2 by linarith)
    hb (norm_nonneg _) (by norm_num : (0:ℝ)≤3/2)).trans_eq
  ring
end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1417

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsCentralLower
Source SHA256: 9bd906af49b4a5f6533d6857700def19df6c6d61588ba425b07190022128cad7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1418


namespace OAI

noncomputable section
open scoped Topology
open Filter
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

theorem central_correction_threshold (eps : ℝ) (heps : 0<eps) :
    ∃Q0 : ℝ,480≤Q0 ∧ ∀Q : ℝ,Q0≤Q→198*Q^(-10*eps)≤1/2 := by
  have hh : Tendsto (fun Q : ℝ=>198*Q^(-10*eps)) atTop (nhds 0) := by
    simpa only [mul_zero,neg_mul] using
      (tendsto_rpow_neg_atTop (show 0<10*eps by positivity)).const_mul (198:ℝ)
  have he := hh.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))
  obtain ⟨Q0,hQ0⟩ := Filter.eventually_atTop.mp he
  refine ⟨max 480 Q0,le_max_left _ _,?_⟩
  intro Q hQ
  exact (hQ0 Q ((le_max_right _ _).trans hQ)).le

variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
include hc in
theorem ramifiedClosed_central_lower (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (hsmall : 198*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-10*eps)≤1/2)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    1/2≤‖ramifiedClosed p hp hg eta a rho x w z j‖ := by
  have hd := ramifiedClosed_central_defect p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  have hh := norm_add_le (1-ramifiedClosed p hp hg eta a rho x w z j)
    (ramifiedClosed p hp hg eta a rho x w z j)
  rw [sub_add_cancel,norm_one,norm_sub_rev] at hh
  linarith
end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1418

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedBound
Source SHA256: 0441eff7953b701e40123f25aa890fc9388166f7e76a7f138b14b88b214563cb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1419


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
lemma rowBaseFinite_selected_bound (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (j e l : ℕ) (hj : j<6)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    ‖rowBaseFinite p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
      rho j e l‖≤16*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
  have hpow : 0≤(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by positivity
  have hv := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_V_half _ hQ z hz)
  have ht' (k : Fin 2) (m : ℕ) :
      ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
        rho j e l k.val m‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
    have ht : e+3*l≠0 := by rcases hf with h|h|h|h <;> omega
    rw [←sourceRowTerm_pos p hp hg eta a rho x w z j e l k.val m ht]
    exact sourceRowTerm_selected_base p hp hg hc eta a rho x w z heta ha hρ hx hw hz
      j e l k.val m hj (by omega) hf
  unfold rowBaseFinite
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _k : Fin 2,8*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
      apply Finset.sum_le_sum
      intro k hk
      apply (norm_add_le _ _).trans
      have hab := (norm_add_le _ _).trans (add_le_add (ht' k 0) (ht' k 1))
      have hd : ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
          rho j e l k.val 2/(1-coordV (Ideal.absNorm (Ideal.span {p})) z)‖≤4*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
        rw [div_eq_mul_inv,norm_mul]
        exact (mul_le_mul (ht' k 2) hv (norm_nonneg _) (by positivity)).trans_eq (by ring)
      linarith
    _ = _ := by simp;ring

include hc in
theorem rowClosedMarked_selected_bound (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) (j : ℕ) (hj : j<6) :
    ‖rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j‖≤128*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
  have hpow : 0≤(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by positivity
  have h02 := rowBaseFinite_selected_bound p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 0 2 hj (by omega)
  have h10 := rowBaseFinite_selected_bound p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 1 0 hj (by omega)
  have h01 := rowBaseFinite_selected_bound p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 0 1 hj (by omega)
  have h11 := rowBaseFinite_selected_bound p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 1 1 hj (by omega)
  have hr := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_R_half _ hQ a x z ha (by linarith) hz)
  simp only [Complex.ofReal_natCast] at hr
  unfold rowClosedMarked
  rw [div_eq_mul_inv,norm_mul]
  apply (mul_le_mul_of_nonneg_right
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add h02 h10)) h01)) h11)) (norm_nonneg _)).trans
  nlinarith

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1419

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedRamified
Source SHA256: 6a12233fc2e5cfbe665021090709bb4b16e051e8f6e2d0ca6cb299c265277e1b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1420


namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

def ramifiedSelected (eta a rho x w z : ℂ) (j : ℕ) : ℂ :=
  star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x*(1-coordV (Ideal.absNorm (Ideal.span {p})) z)*
    rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j -
    (Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)*ramifiedClosed p hp hg eta a rho x w z j

lemma ramifiedSelected_eq_replacement (eta a rho x w z : ℂ) (j : ℕ) :
    ramifiedSelected p hp hg eta a rho x w z j =
      ProbeLocal.compensatedReplacement (coordV (Ideal.absNorm (Ideal.span {p})) z) 0 0
        (rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j)
        (star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) := by
  rw [ProbeLocal.continued_ramified_compensation]
  simp only [ramifiedSelected,ramifiedClosed,ProbeLocal.continuedCorrection,mul_zero,sub_zero,mul_one,div_one]

include hc in
theorem ramifiedSelected_bound (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) (j : ℕ) (hj : j<6) :
    ‖ramifiedSelected p hp hg eta a rho x w z j‖≤385*(Ideal.absNorm (Ideal.span {p}):ℝ)^(max (1-w.re) 0) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  let B : ℝ := max (1-w.re) 0
  have hQ0 : 0<Q := by dsimp [Q];linarith
  have hQ1 : 1≤Q := by dsimp [Q];linarith
  have hB0 : 0≤B := le_max_right _ _
  have hM := rowClosedMarked_selected_bound p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j hj
  have hH := ramifiedClosed_first_region_bound p hp hg hc eta a rho x w z hQ heta ha hρ
    (by linarith) (by linarith) hz (by linarith) j hj
  have hV := first_region_V_half _ hQ z hz
  have h1V : ‖1-coordV (Ideal.absNorm (Ideal.span {p})) z‖≤3/2 := by
    have hh := norm_sub_le (1:ℂ) (coordV (Ideal.absNorm (Ideal.span {p})) z)
    simp only [norm_one] at hh
    linarith
  have hphase : ‖star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x‖≤Q^x.re := by
    change ‖star eta*(Q:ℂ)^x‖≤Q^x.re
    rw [norm_mul,norm_star,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  have hq : ‖(Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)‖≤Q^B := by
    change ‖(Q:ℂ)^(-w)‖≤Q^B
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by dsimp [B];linarith)
  have he : Q^x.re*Q^(-x.re+B)=Q^B := by rw [←Real.rpow_add hQ0];congr 1;ring
  unfold ramifiedSelected
  apply (norm_sub_le _ _).trans
  simp only [norm_mul] at hphase ⊢
  calc
    _ ≤ (Q^x.re*(3/2))*(128*Q^(-x.re+B))+Q^B*193 := by
      gcongr
    _ = 385*Q^B := by nlinarith [he]

include hc in
theorem ramifiedSelected_small_bound (eta a rho x z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re) (t : ℝ) (j : ℕ) (hj : j<6) :
    ‖ramifiedSelected p hp hg eta a rho x ((1/2:ℂ)+t*Complex.I) z j‖≤
      385*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1/2:ℝ) := by
  have hh := ramifiedSelected_bound p hp hg hc eta a rho x ((1/2:ℂ)+t*Complex.I) z hQ heta ha hρ hx
    (by norm_num [Complex.mul_re]) hz j hj
  norm_num [Complex.mul_re] at hh ⊢
  exact hh

include hc in
theorem ramifiedSelected_large_bound (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (hw : 1≤w.re) (hz : (17/50:ℝ)≤z.re) (j : ℕ) (hj : j<6) :
    ‖ramifiedSelected p hp hg eta a rho x w z j‖≤385 := by
  have hh := ramifiedSelected_bound p hp hg hc eta a rho x w z hQ heta ha hρ hx (by linarith) hz j hj
  simpa only [max_eq_right (by linarith : 1-w.re≤0),Real.rpow_zero,mul_one] using hh

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1420

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsCentralRamified
Source SHA256: cb213e5903bdea0f731b65b5cd3f3031fa06ae8922ffdeda1f6235e3b5b8557f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1421




namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

def ramifiedStrictSelected (eta a rho x w z : ℂ) (j : ℕ) : ℂ :=
  star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x*(1-coordV (Ideal.absNorm (Ideal.span {p})) z)*
    (rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j 1 0 1 0 /
      (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        (coordV (Ideal.absNorm (Ideal.span {p})) z)))

include hc in
theorem ramifiedSelected_central_regular (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    ‖ramifiedSelected p hp hg eta a rho x w z j-ramifiedStrictSelected p hp hg eta a rho x w z j‖≤
      385*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1/2:ℝ) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ0 : 0<Q := by dsimp [Q];linarith
  have hQ1 : 1≤Q := by linarith
  have hrem := rowClosedMarked_central_remainder p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  dsimp only at hrem
  simp only [Complex.ofReal_natCast] at hrem
  have hH := ramifiedClosed_first_region_bound p hp hg hc eta a rho x w z hQ heta ha hρ
    (by rw [hx];linarith) (by rw [hw];linarith) (by rw [hz]) (by rw [hx,hw];linarith) j hj
  have hV := first_region_V_half _ hQ z (by rw [hz])
  have h1V : ‖1-coordV Q z‖≤3/2 := by
    have h := norm_sub_le (1:ℂ) (coordV Q z)
    rw [norm_one] at h
    change ‖coordV Q z‖≤1/2 at hV
    linarith
  have hphase : ‖star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x‖≤Q^x.re := by
    rw [norm_mul,norm_star,←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  have hqw : ‖(Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)‖≤Q^(1/2:ℝ) := by
    rw [←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith)
  have hid (B V M T q H : ℂ) : B*V*M-q*H-B*V*T=B*V*(M-T)-q*H := by ring
  unfold ramifiedSelected ramifiedStrictSelected
  rw [hid]
  apply (norm_sub_le _ _).trans
  simp only [norm_mul] at hphase ⊢
  calc
    _≤(Q^x.re*(3/2))*(128*Q^(1/2-x.re))+Q^(1/2:ℝ)*193 := by
      gcongr
    _=385*Q^(1/2:ℝ) := by
      have ht : Q^x.re*Q^(1/2-x.re)=Q^(1/2:ℝ) := by rw [←Real.rpow_add hQ0];congr 1;ring
      nlinarith [ht]
end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1421

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsCentralStrictSelected
Source SHA256: d4f77f1a73bb948272eb58d696ad4876d90a065e10a9d9473d0d00d66ee22642
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1422


namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

lemma ramifiedStrictSelected_from_entry (eta a rho x w z : ℂ) (j : ℕ) (b : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (heta : ‖eta‖≤1) (ha : ‖a‖≤1)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (ht : ‖sourceRowTerm p hp hg eta a rho x w z j 1 0 1 0‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^b) :
    ‖ramifiedStrictSelected p hp hg eta a rho x w z j‖≤
      6*(Ideal.absNorm (Ideal.span {p}):ℝ)^(x.re+b) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ0 : 0<Q := by dsimp [Q];linarith
  rw [sourceRowTerm_pos p hp hg eta a rho x w z j 1 0 1 0 (by omega)] at ht
  have hr := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_R_half _ hQ a x z ha hx hz)
  simp only [Complex.ofReal_natCast] at hr
  have hv := first_region_V_half _ hQ z hz
  have hs := norm_sub_le (1:ℂ) (coordV Q z)
  rw [norm_one] at hs
  have h1V : ‖1-coordV Q z‖≤3/2 := by change ‖coordV Q z‖≤1/2 at hv;linarith
  have hphase : ‖star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x‖≤Q^x.re := by
    rw [norm_mul,norm_star,←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  unfold ramifiedStrictSelected
  rw [div_eq_mul_inv]
  simp only [norm_mul] at hphase ⊢
  calc
    _≤(Q^x.re*(3/2))*((2*Q^b)*2) := by gcongr
    _=6*Q^(x.re+b) := by rw [Real.rpow_add hQ0];ring

include hc in
theorem ramifiedStrictSelected_central_norm (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re) (j : ℕ) (hj : j<6) :
    ‖ramifiedStrictSelected p hp hg eta a rho x w z j‖≤
      6*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1-w.re) := by
  have hb := ramifiedStrictSelected_from_entry p hp hg eta a rho x w z j (1-x.re-w.re)
    hQ heta ha hx hz (sourceRowTerm_central_strict_norm p hp hg hc eta a rho x w z heta ha hρ j hj)
  convert hb using 1 ; congr 2 ; ring

include hc in
theorem ramifiedStrictSelected_boundary_norm (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re) (j : ℕ) (hj : j≤1) :
    ‖ramifiedStrictSelected p hp hg eta a rho x w z j‖≤
      6*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-w.re) := by
  have hb := ramifiedStrictSelected_from_entry p hp hg eta a rho x w z j (-x.re-w.re)
    hQ heta ha hx hz (sourceRowTerm_central_boundary_norm p hp hg hc eta a rho x w z heta ha hρ j hj)
  convert hb using 1 ; congr 2 ; ring
end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1422

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsCentralRamifiedQuotient
Source SHA256: 77b3b626606f126fc6a1addacd0d61dc68653a7497f92fb6bfe7f79ce097273f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1423



namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma norm_div_le_twice (A H : ℂ) (hH : 1/2≤‖H‖) : ‖A/H‖≤2*‖A‖ := by
  rw [norm_div]
  apply (div_le_iff₀ (by linarith : 0<‖H‖)).mpr
  nlinarith [norm_nonneg A]

variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
include hc in
theorem ramifiedSelected_central_quotient (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (hsmall : 198*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-10*eps)≤1/2)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    Q^(-1:ℝ)*‖ramifiedSelected p hp hg eta a rho x w z j /
      ramifiedClosed p hp hg eta a rho x w z j‖≤
      800*Q^(-(1/2:ℝ))+(if 2≤j then 12*Q^(-w.re) else 0) := by
  dsimp only
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ0 : 0<Q := by dsimp [Q];linarith
  have hQ1 : 1≤Q := by linarith
  have hH := ramifiedClosed_central_lower p hp hg hc eta a rho x w z alpha eps hQ hsmall heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  have hreg := ramifiedSelected_central_regular p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  have hnorm := norm_div_le_twice (ramifiedSelected p hp hg eta a rho x w z j)
    (ramifiedClosed p hp hg eta a rho x w z j) hH
  have htri := (norm_add_le _ _).trans (add_le_add hreg (le_refl ‖ramifiedStrictSelected p hp hg eta a rho x w z j‖))
  rw [sub_add_cancel] at htri
  have hpow : Q^(-1:ℝ)*Q^(1/2:ℝ)=Q^(-(1/2:ℝ)) := by rw [←Real.rpow_add hQ0];norm_num
  have hqi : 0≤Q^(-1:ℝ) := Real.rpow_nonneg hQ0.le _
  by_cases hj2 : 2≤j
  · rw [ite_eq_left hj2]
    have hs := ramifiedStrictSelected_central_norm p hp hg hc eta a rho x w z hQ heta ha hρ
      (by rw [hx];linarith) (by rw [hz]) j hj
    have hb : ‖ramifiedSelected p hp hg eta a rho x w z j‖≤385*Q^(1/2:ℝ)+6*Q^(1-w.re) := by linarith
    have hprod : Q^(-1:ℝ)*Q^(1-w.re)=Q^(-w.re) := by rw [←Real.rpow_add hQ0];congr 1;ring
    calc
      _≤Q^(-1:ℝ)*(2*(385*Q^(1/2:ℝ)+6*Q^(1-w.re))) := mul_le_mul_of_nonneg_left (hnorm.trans (by linarith)) hqi
      _=770*Q^(-(1/2:ℝ))+12*Q^(-w.re) := by nlinarith [hpow,hprod]
      _≤_ := by nlinarith [Real.rpow_nonneg hQ0.le (-(1/2:ℝ))]
  · rw [ite_eq_right hj2,add_zero]
    have hs := ramifiedStrictSelected_boundary_norm p hp hg hc eta a rho x w z hQ heta ha hρ
      (by rw [hx];linarith) (by rw [hz]) j (by omega)
    have hqw : Q^(-w.re)≤Q^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith)
    have hb : ‖ramifiedSelected p hp hg eta a rho x w z j‖≤391*Q^(1/2:ℝ) := by nlinarith
    calc
      _≤Q^(-1:ℝ)*(2*(391*Q^(1/2:ℝ))) := mul_le_mul_of_nonneg_left (hnorm.trans (by linarith)) hqi
      _=782*Q^(-(1/2:ℝ)) := by nlinarith [hpow]
      _≤_ := mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hQ0.le _)
end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1423

/-! Original module: OAI.NumberTheory.DirichletL.Detector.MarkedValuations
Source SHA256: f5e6f9005f17f817ea15608aeb334ef361e50b12b502fb8558e018f9dd822037
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1424



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic UniqueFactorizationMonoid ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma prime_dvd_iff_valuation (P : PrimeIdeal) (I : Id) (hI : I≠0) :
    P.val∣I ↔ primeValuations I P≠0 := by
  rw [primeValuations_apply,Multiset.count_ne_zero,mem_normalizedFactors_iff hI]
  exact ⟨fun h=>⟨P.property,h⟩,fun h=>h.2⟩

lemma prime_dvd_high_completed (P : PrimeIdeal) (v : PrimeIdeal→₀HighValuation) :
    P.val∣(highIdeals v).1.1*(highIdeals v).1.2^3 ↔ (v P).1.1+3*(v P).1.2≠0 := by
  have hI : (highIdeals v).1.1≠0 := idealFromValuations_ne_zero _
  have hJ : (highIdeals v).1.2≠0 := idealFromValuations_ne_zero _
  rw [prime_dvd_iff_valuation P _ (mul_ne_zero hI (pow_ne_zero _ hJ)),
    primeValuations_mul _ _ hI (pow_ne_zero _ hJ),primeValuations_pow]
  simp only [highIdeals,primeValuations_idealFromValuations,Finsupp.add_apply,
    Finsupp.mapRange_apply,Finsupp.coe_smul,Pi.smul_apply,smul_eq_mul]

lemma primeProduct_dvd (T : Finset PrimeIdeal) (I : Id) :
    (∏P∈T,P.val)∣I ↔ ∀P∈T,P.val∣I := by
  constructor
  · intro h P hP
    exact (Finset.dvd_prod_of_mem _ hP).trans h
  · intro h
    exact Finset.prod_dvd_of_coprime (fun P _ Q _ hPQ=>primeIdeal_coprime P Q hPQ) h

def completedValuationMark (_P : PrimeIdeal) (b : HighValuation) : ℂ :=
  if b.1.1+3*b.1.2≠0 then 1 else 0

lemma completedValuationMark_norm (_P : PrimeIdeal) (b : HighValuation) :
    ‖completedValuationMark _P b‖≤1 := by
  unfold completedValuationMark
  split_ifs <;> norm_num

lemma completedValuationMark_product (T : Finset PrimeIdeal) (v : PrimeIdeal→₀HighValuation) :
    (∏P∈T,completedValuationMark P (v P))=
      if (∏P∈T,P.val)∣(highIdeals v).1.1*(highIdeals v).1.2^3 then 1 else 0 := by
  rw [primeProduct_dvd]
  simp only [prime_dvd_high_completed]
  by_cases h : ∀P∈T,(v P).1.1+3*(v P).1.2≠0
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro P hP
    exact ite_eq_left (h P hP)
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨P,hP,hv⟩ := h
    apply Finset.prod_eq_zero hP
    simp only [completedValuationMark,hv,ne_eq,not_true_eq_false,ite_false]

lemma highIdealMask_mark (S : Finset Id) (D I J K L : Id) :
    highIdealMask S D I J K L=(if D∣I*J^3 then 1 else 0)*highIdealMask S 1 I J K L := by
  unfold highIdealMask completedMask
  simp only [one_dvd,true_and]
  split_ifs <;> simp_all

lemma markedIdealHighSummand_mark (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) (I J K L : Id) :
    markedIdealHighSummand S D η u x w z I J K L=
      (if D∣I*J^3 then 1 else 0)*markedIdealHighSummand S 1 η u x w z I J K L := by
  rw [markedIdealHighSummand,highIdealMask_mark,markedIdealHighSummand,mul_assoc]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1424

/-! Original module: OAI.NumberTheory.DirichletL.Detector.MarkedEuler
Source SHA256: b1c397140e68d81ff368e0916083cbfb427c8a697a982148b62896c82dbb2001
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1425


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeEulerFinsupp
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def excludedHighArray (S : Finset Id) (η : HeckeFamily.Character) (x w z : ℂ) (a : HighIdeal) : ℂ :=
  markedIdealHighSummand S 1 η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2

lemma excludedHighArray_one (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ) : excludedHighArray S η x w z 1=1 := by
  simp only [excludedHighArray,Prod.fst_one,Prod.snd_one,markedIdealHighSummand,
    highIdealMask_unmarked_one S hS,bareIdealHighSummand_one,one_mul]

lemma excludedHighArray_mul (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ) (a b : HighIdeal)
    (hc : IsCoprime (a.1.1*a.1.2*a.2.1*a.2.2) (b.1.1*b.1.2*b.2.1*b.2.2)) :
    excludedHighArray S η x w z (a*b)=excludedHighArray S η x w z a*excludedHighArray S η x w z b := by
  simp only [excludedHighArray,Prod.fst_mul,Prod.snd_mul,markedIdealHighSummand,
    highIdealMask_unmarked_mul S hS a b,
    bareIdealHighSummand_mul η x w z _ _ _ _ _ _ _ _ hc]
  ring

def excludedHighPrimeTerm (S : Finset Id) (η : HeckeFamily.Character) (x w z : ℂ)
    (P : PrimeIdeal) (b : HighValuation) : ℂ :=
  excludedHighArray S η x w z ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))

lemma excludedHighArray_prod (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ) (v : PrimeIdeal→₀HighValuation) :
    excludedHighArray S η x w z (highIdeals v)=v.prod (excludedHighPrimeTerm S η x w z) :=
  highArray_val_prod _ (excludedHighArray_one S hS η x w z) (excludedHighArray_mul S hS η x w z) v

lemma markedHighArray_val (S : Finset Id) (hS : ∀P∈S,Prime P) (T : Finset PrimeIdeal)
    (η : HeckeFamily.Character) (x w z : ℂ) (v : PrimeIdeal→₀HighValuation) :
    markedIdealHighSummand S (∏P∈T,P.val) η 1 x w z
      (highIdeals v).1.1 (highIdeals v).1.2 (highIdeals v).2.1 (highIdeals v).2.2=
        markedArray T completedValuationMark (excludedHighPrimeTerm S η x w z) v := by
  rw [markedIdealHighSummand_mark,markedArray,completedValuationMark_product]
  change _*excludedHighArray S η x w z (highIdeals v)=_
  rw [excludedHighArray_prod S hS]

theorem markedIdealHighSeries_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (T : Finset PrimeIdeal) (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑'b : HighValuation,
      markedLocal T completedValuationMark (excludedHighPrimeTerm S η x w z) P b)
      (markedIdealHighSeries S (∏P∈T,P.val) η 1 x w z) := by
  have h0 (P : PrimeIdeal) : excludedHighPrimeTerm S η x w z P 0=1 := by
    simp only [excludedHighPrimeTerm,Prod.fst_zero,Prod.snd_zero,pow_zero]
    exact excludedHighArray_one S hS η x w z
  have hs := (markedIdealHighSummand_summable S 1 η 1 x w z hx hw hz).norm.comp_injective highIdeals_injective
  change Summable (fun v=>‖excludedHighArray S η x w z (highIdeals v)‖) at hs
  simp only [excludedHighArray_prod S hS] at hs
  have he := marked_hasProd T completedValuationMark (excludedHighPrimeTerm S η x w z) h0 hs
    (fun P _ b=>completedValuationMark_norm P b)
  have hsum : (∑'v : PrimeIdeal→₀HighValuation,
      markedArray T completedValuationMark (excludedHighPrimeTerm S η x w z) v)=
      markedIdealHighSeries S (∏P∈T,P.val) η 1 x w z := by
    simp only [←markedHighArray_val S hS T η x w z]
    unfold markedIdealHighSeries
    apply highIdeals_injective.tsum_eq (f:=fun a : HighIdeal=>
      markedIdealHighSummand S (∏P∈T,P.val) η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2)
    intro a ha
    have hh : bareIdealHighSummand η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2≠0 :=
      (mul_ne_zero_iff.mp ha).2
    have hc := bareIdealHighSummand_support η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2 hh
    let b : (NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal) :=
      ((⟨a.1.1,hc.2.1.1⟩,⟨a.1.2,hc.2.2.1.1⟩),(⟨a.2.1,hc.2.2.2.1.1⟩,⟨a.2.2,hc.2.2.2.2.1⟩))
    refine ⟨highValuationEquiv b,?_⟩
    rw [highIdeals_eq_equiv,highValuationEquiv.symm_apply_apply]
  simpa only [hsum] using he

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1425

/-! Original module: OAI.NumberTheory.DirichletL.Detector.MarkedLocal
Source SHA256: eb543169fd2fcdfd23d30d92490479dda536336b3cc6af63818bfb67cd855cb1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1426




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ProbeEuler ProbeRow ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def idealMarkedLocalFactor (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  ∑e : Fin 2,∑'l,∑'k,∑'m,
    completedValuationMark P ((e.val,l),(k,m))*highPrimeTerm η x w z P ((e.val,l),(k,m))

lemma markedPrimeTerm_summable_norm (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    Summable (fun b : HighValuation=>‖completedValuationMark P b*highPrimeTerm η x w z P b‖) := by
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ (highPrimeTerm_summable_norm η x w z hx hw hz P)
  intro b
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (completedValuationMark_norm P b)

lemma markedPrimeTerm_tsum (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    (∑'b : HighValuation,completedValuationMark P b*highPrimeTerm η x w z P b)=
      idealMarkedLocalFactor η P x w z := by
  have hs := (markedPrimeTerm_summable_norm η P x w z hx hw hz).of_norm
  rw [hs.tsum_prod,hs.prod.tsum_prod]
  have he (e l : ℕ) : (∑'b : ℕ×ℕ,completedValuationMark P ((e,l),b)*highPrimeTerm η x w z P ((e,l),b))=
      ∑'k,∑'m,completedValuationMark P ((e,l),(k,m))*highPrimeTerm η x w z P ((e,l),(k,m)) :=
    (hs.prod_factor (e,l)).tsum_prod
  simp_rw [he]
  rw [tsum_eq_sum (s:=Finset.range 2) (fun e he=>by
    have hh : 2≤e := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using he)
    simp only [highPrimeTerm_zero_of_two_le η x w z P e _ _ _ hh,mul_zero,tsum_zero]),
    ←Fin.sum_univ_eq_sum_range]
  rfl

lemma selectedLocal_outside (S : Finset Id) (hS : ∀P∈S,Prime P) (T : Finset PrimeIdeal)
    (η : HeckeFamily.Character) (P : PrimeIdeal) (hP : P.val∉S) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    (∑'b : HighValuation,ProbeEulerFinsupp.markedLocal T completedValuationMark
      (excludedHighPrimeTerm S η x w z) P b)=
      if P∈T then idealMarkedLocalFactor η P x w z else idealHighLocalFactor η P.val x w z := by
  have he (b : HighValuation) : excludedHighPrimeTerm S η x w z P b=highPrimeTerm η x w z P b := by
    simp only [excludedHighPrimeTerm,excludedHighArray,markedIdealHighSummand,
      highIdealMask_prime_outside S hS P hP,one_mul,highPrimeTerm]
  simp only [ProbeEulerFinsupp.markedLocal,he]
  by_cases hPT : P∈T
  · simp only [ite_eq_left hPT]
    exact markedPrimeTerm_tsum η P x w z hx hw hz
  · simp only [ite_eq_right hPT,one_mul]
    exact highPrimeTerm_tsum_eq_localFactor η x w z hx hw hz P

lemma idealMarkedLocalFactor_eq_source (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    let p := primaryGenerator P.val
    let hp := supported_primeGenerator_prime P hs
    letI : (Ideal.span {p}:Id).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    let hg := (supported_prime_data p hp ((span_primaryGenerator_of_supported P.val hs).symm ▸ hs)).1
    idealMarkedLocalFactor η P x w z=
      principalMarkedSeries p hp hg (targetMonoid η p) (actualACube η p)
        ((Ideal.absNorm P.val:ℂ)^(-x)) ((Ideal.absNorm P.val:ℂ)^(-w))
        (coordV (Ideal.absNorm P.val) z) := by
  dsimp only
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Id).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hprimary := (primaryGenerator_spec P.val (supported_primaryGenerator_ne_zero P.val hs)).2
  unfold idealMarkedLocalFactor principalMarkedSeries principalInner
  apply Finset.sum_congr rfl
  intro e he
  apply tsum_congr
  intro l
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  change completedValuationMark P ((e.val,l),(k,m))*bareIdealHighSummand η 1 x w z
    (P.val^e.val) (P.val^l) (P.val^k) (P.val^m)=_
  have hterm := bareIdealHighSummand_at_prime η p hp hg.1 hg.2 hprimary hsp e.val l k m (by omega) x w z
  conv_lhs at hterm => rw [hspan]
  rw [hterm]
  by_cases ht : e.val+3*l=0
  · have he0 : e.val=0 := by omega
    have hl0 : l=0 := by omega
    simp only [completedValuationMark,ht,ne_eq,not_true_eq_false,ite_false,zero_mul]
    rw [he0,hl0]
    simpa only [hspan] using (markedTerm_zero_index p hp hg.1 (targetMonoid η p)
      (actualACube η p) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) k m).symm
  · simp only [completedValuationMark,ht,ne_eq,not_false_eq_true,ite_true,one_mul]
    simpa only [hspan] using sourcePrincipalTerm_pos p hp hg.1 (targetMonoid η p) (actualACube η p) x w z e.val l k m ht

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1426

/-! Original module: OAI.NumberTheory.DirichletL.Detector.MarkedRational
Source SHA256: 6a8890944d7f0a04f03919e98e0152c020bf3d4a1fba05255559dbcd20017eaf
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1427


namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open ProbeEuler ProbeRow ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

def idealMarkedClosed (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  let Q : ℝ := Ideal.absNorm P.val
  let R := coordR Q (actualAPhase η (primaryGenerator P.val)) x z
  markedFactor R (coordV Q z) (Q:ℂ)⁻¹ (coordK Q (HeckeFamily.idealCoeff η P.val) x w)
    (-coordD Q (HeckeFamily.idealCoeff η P.val) 1 x+coordW Q 1 w*R) 1

theorem idealMarkedLocalFactor_rational (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) (hx : 3/2<x.re) (hz : 1/6<z.re) :
    idealMarkedLocalFactor η P x w z=idealMarkedClosed η P x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hQ2 : (2:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by
    rw [hspan]
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P
  have hQ0 : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hQ1 : (1:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1 := by
    rw [coordV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) ((actualACube η p)^2) x z‖<1 := by
    rw [actualACube_sq]
    apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η p)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hr := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ0 (actualACube η p) x z
  simp only [Complex.ofReal_natCast] at hr
  have he := principalMarkedSeries_eq p hp hg.1 hg.2 (targetMonoid η p) (actualACube η p)
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
    (coordV (Ideal.absNorm (Ideal.span {p})) z) hV (by simpa only [hr] using hR)
  have hsource := idealMarkedLocalFactor_eq_source η P hs x w z
  dsimp only at hsource
  rw [hsource]
  have hk := coordK_eq_geometric (Ideal.absNorm (Ideal.span {p}):ℝ) hQ0 (targetMonoid η p) x w
  simp only [Complex.ofReal_natCast] at hr hk
  rw [hr,←hk] at he
  simp only [actualACube_sq] at he
  convert he using 1
  · congr 2 <;> simp only [hspan,p]
  · simp only [idealMarkedClosed,coordD,coordW,star_one,mul_one,one_mul]
    simp only [hspan,p,targetMonoid_primaryGenerator η P.val hs,Complex.ofReal_natCast,neg_mul]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1427

/-! Original module: OAI.NumberTheory.DirichletL.Detector.SourceExclusions
Source SHA256: 1430bb9bf9e3d40b8162a9155578ac7c9e80c3d8416016614ebdc4e0533fffcd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1428


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve UniqueFactorizationMonoid ProbeEuler
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma outside_prime_supported (S : Finset Id) (hbad : fixedBadPrimes⊆S)
    (P : PrimeIdeal) (hP : P.val∉S) : Supported P.val := by
  let : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  let : P.val.IsMaximal := Ideal.IsPrime.isMaximal inferInstance P.property.ne_zero
  refine ⟨P.property.ne_zero,?_⟩
  intro Q hQ
  have heq : Q=P.val := by
    simpa only [normalizedFactors_irreducible P.property.irreducible,normalize_eq,
      Multiset.mem_singleton] using hQ
  subst Q
  exact (prime_good_iff_not_bad P.val).mpr (fun h=>hP (hbad h))

structure SourceExclusions (S : Finset Id) : Prop where
  prime : ∀P∈S,Prime P
  bad : fixedBadPrimes⊆S
  tail : CorrectionTail S

theorem exists_source_exclusions (S₀ : Finset Id) (hp : ∀P∈S₀,Prime P)
    (hbad : fixedBadPrimes⊆S₀) :
    ∃S : Finset Id,S₀⊆S ∧ SourceExclusions S := by
  obtain ⟨N,hN,hcut⟩ := exists_uniform_global_cutoff
  refine ⟨S₀∪smallPrimeSet N,Finset.subset_union_left,?_⟩
  constructor
  · intro P hP
    rcases Finset.mem_union.mp hP with hP|hP
    · exact hp P hP
    · exact (Finset.mem_filter.mp hP).2
  · exact hbad.trans Finset.subset_union_left
  · apply hcut
    intro P hP
    exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)

theorem source_principalHigh_L_factorization (S : Finset Id) (hS : SourceExclusions S)
    (η : HeckeFamily.Character) (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S 1 η 1 x w z =
      HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
      HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
        HeckeFamily.LFunction (η.excludePrimes S hS.prime) x * globalClosedCorrection η S x w z :=
  principalHigh_L_factorization S hS.prime (outside_prime_supported S hS.bad) hS.tail η x w z hx hw hz

theorem source_globalCorrection_principal (S : Finset Id) (hS : SourceExclusions S)
    (η : HeckeFamily.Character) (x : ℂ) :
    globalClosedCorrection η S x 1 (1/6)=principalCorrection η S x :=
  globalClosedCorrection_principal η S (outside_prime_supported S hS.bad) x

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1428

/-! Original module: OAI.NumberTheory.DirichletL.Detector.MarkedProduct
Source SHA256: efbc67fd5af2c9e1137415b22e5d5b82b74baa46e1ded3b979a187a098b97f1e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1429



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeEuler ProbeEulerFinsupp
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma source_idealHighLocalFactor_ne_zero (S : Finset Id) (hS : SourceExclusions S)
    (η : HeckeFamily.Character) (P : PrimeIdeal) (hP : P.val∉S) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    idealHighLocalFactor η P.val x w z≠0 := by
  rw [idealHighLocalFactor_rational η P (outside_prime_supported S hS.bad P hP) x w z hx hw hz]
  have hQ : (1:ℝ)<Ideal.absNorm P.val := by
    have hh := hS.tail.norm_four P hP
    exact_mod_cast (by omega : 1<Ideal.absNorm P.val)
  have hQ0 : (0:ℝ)<Ideal.absNorm P.val := by linarith
  have hD : ‖HeckeFamily.idealCoeff η P.val*(Ideal.absNorm P.val:ℂ)^(-x)‖<1 := by
    rw [norm_mul,Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hQ0),Complex.neg_re]
    apply (mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) (HeckeFamily.idealCoeff_norm_le_one η P.val)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  have hV : ‖(Ideal.absNorm P.val:ℂ)^(-6*z)‖<1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hQ0)]
    apply Real.rpow_lt_one_of_one_lt_of_neg hQ
    norm_num [Complex.mul_re]
    linarith
  have hW : ‖(Ideal.absNorm P.val:ℂ)^(-w)‖<1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hQ0),Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  apply mul_ne_zero
  · exact div_ne_zero (one_sub_ne_zero_of_norm_lt_one _ hD)
      (mul_ne_zero (one_sub_ne_zero_of_norm_lt_one _ hV) (one_sub_ne_zero_of_norm_lt_one _ hW))
  · exact factor_ne_zero_of_defect _ ((idealClosedCorrection_bound η P (hS.tail.norm_four P hP)
      x w z (by linarith) (by linarith) (by linarith)).trans (hS.tail.half ⟨P,hP⟩))

theorem markedIdealHighSeries_eq_product (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η 1 x w z=
      markedIdealHighSeries S 1 η 1 x w z *
        ∏P∈T,idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z := by
  let R := fun P : PrimeIdeal=>if P∈T then
    idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z else 1
  have hR : HasProd R (∏P∈T,idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T) (f:=R) (L:=SummationFilter.unconditional PrimeIdeal) (fun P hP=>ite_eq_right hP)
    simpa only [R,Finset.prod_ite_mem,Finset.inter_self] using hh
  have he := (excludedIdealHighSeries_hasProd S hS.prime η x w z hx hw hz).mul hR
  have heq (P : PrimeIdeal) :
      (∑'b : HighValuation,excludedHighPrimeTerm S η x w z P b)*R P=
      ∑'b : HighValuation,markedLocal T completedValuationMark (excludedHighPrimeTerm S η x w z) P b := by
    by_cases hp : P∈T
    · rw [selectedLocal_outside S hS.prime T η P (hT P hp) x w z hx hw hz,ite_eq_left hp]
      have hu : (∑'b : HighValuation,excludedHighPrimeTerm S η x w z P b)=idealHighLocalFactor η P.val x w z := by
        simpa only [excludedHighPrimeTerm,excludedHighArray,ite_eq_right (hT P hp)] using
          excludedHighLocalFactor S hS.prime η x w z hx hw hz P
      rw [hu,show R P=idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z from ite_eq_left hp]
      exact mul_div_cancel₀ _ (source_idealHighLocalFactor_ne_zero S hS η P (hT P hp) x w z hx hw hz)
    · simp only [R,hp,ite_false,mul_one,markedLocal,one_mul]
  have he' : HasProd (fun P : PrimeIdeal=>∑'b : HighValuation,
      markedLocal T completedValuationMark (excludedHighPrimeTerm S η x w z) P b)
      (markedIdealHighSeries S 1 η 1 x w z *
        ∏P∈T,idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z) := by
    convert he using 1
    funext P
    exact (heq P).symm
  exact (markedIdealHighSeries_hasProd S hS.prime T η x w z hx hw hz).unique he'

theorem source_markedHigh_L_factorization (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η 1 x w z=
      (HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
       HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
       HeckeFamily.LFunction (η.excludePrimes S hS.prime) x * globalClosedCorrection η S x w z) *
        ∏P∈T,idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z := by
  rw [markedIdealHighSeries_eq_product S hS T hT η x w z hx hw hz,
    source_principalHigh_L_factorization S hS η x w z hx hw hz]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1429

/-! Original module: OAI.NumberTheory.DirichletL.Detector.SpectralCoefficient
Source SHA256: 65b87b9b5a9b516004c06b7385bf1f54ede41b6d779ef5dd4ffae03bd59d688d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1430



namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted ProbeRow ProbePhase ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma rayMask_supported (a : O) (ha : Supported (Ideal.span {a})) : RayFourExpansion.rayMask a=1 := by
  let : (Ideal.span {(2:O)}).IsMaximal := by
    simpa only [cubicTwoIdeal,Ideal.span_singleton_neg] using cubicTwoIdeal_isMaximal
  let : Field (O⧸Ideal.span {(2:O)}) := Ideal.Quotient.field _
  have h2 : IsCoprime (2:O) a := by
    apply (isUnit_quotient_span_iff _ _).mp
    apply isUnit_iff_ne_zero.mpr
    intro hz
    exact ((supported_span_iff a).mp ha).2
      (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  have h4 : IsCoprime (4:O) a := by
    simpa only [show (2:O)^2=4 by norm_num] using (h2.pow_left : IsCoprime ((2:O)^2) a)
  exact ite_eq_left ((isUnit_quotient_span_iff (4:O) a).mpr h4)

lemma completedCorrection_supported (I J : Ideal O) (hI : Supported I) (hJ : Supported J) :
    completedCorrection I J=star (G (completedIndex I J)) := by
  rw [completedCorrection_eq_phase,rayMask_supported]
  · exact one_mul _
  · exact supported_completed _ _ ((supported_span_primaryGenerator_iff I).mpr hI)
      ((supported_span_primaryGenerator_iff J).mpr hJ)

lemma baseRowCoefficient_unit_apply (η : HeckeFamily.Character) (C : CalibrationData)
    (s : O) (hs : Supported (Ideal.span {s})) (A : O) (hA : Supported (Ideal.span {A}))
    (hcop : IsCoprime C.generator A) :
    baseRowCoefficient η C.Xi s hs A=targetMonoid η A*(C.Xi A)⁻¹*reciprocitySign A s := by
  change targetMonoid η A*star (C.Xi A)*sexticReciprocityPhase s A=_
  have hc : star (C.Xi A)=(C.Xi A)⁻¹ := (Complex.inv_eq_conj (C.Xi_norm_one A hA hcop)).symm
  rw [hc]
  congr 1
  exact congrArg (fun n : ℤ=>(n:ℂ)) (QuadraticAllOddCRT.quadraticRaySign_symm _ _)

theorem spectralSummand_source_coefficient (S : Finset (Ideal O)) (D I J : Ideal O)
    (η : HeckeFamily.Character) (C : CalibrationData) (s : O) (hs : Supported (Ideal.span {s}))
    (hI : Supported I) (hJ : Supported J) (hsf : Squarefree I)
    (hcop : IsCoprime C.generator (completedIndex I J)) (t : ℂ) :
    spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J=
      completedMask S D I J *
        (gaussTwo I (supported_primaryGenerator_ne_zero I hI)*
          star (FiniteGaussPhase.angularFactor (completedIndex I J)*G (completedIndex I J))*
          targetMonoid η (completedIndex I J)*(C.Xi (completedIndex I J))⁻¹*
          reciprocitySign (completedIndex I J) s) /
        ((Real.sqrt (Ideal.absNorm I):ℂ)*(Ideal.absNorm J:ℂ)) *
        (fullIdealWeight t I*fullIdealWeight (3*t) J) := by
  have hA := supported_completed _ _ ((supported_span_primaryGenerator_iff I).mpr hI)
    ((supported_span_primaryGenerator_iff J).mpr hJ)
  have hb := baseRowCoefficient_unit_apply η C s hs (completedIndex I J) hA hcop
  have hangle : FiniteGaussPhase.angularFactor (completedIndex I J)=
      FiniteGaussPhase.angularFactor (primaryGenerator I)*FiniteGaussPhase.angularFactor (primaryGenerator J)^3 := by
    rw [completedIndex,angularFactor_mul,show primaryGenerator J^3=(primaryGenerator J*primaryGenerator J)*primaryGenerator J by ring,
      angularFactor_mul,angularFactor_mul]
    ring
  have hm : baseRowCoefficient η C.Xi s hs (primaryGenerator I)*
      baseRowCoefficient η C.Xi s hs (primaryGenerator J)^3=
        targetMonoid η (completedIndex I J)*(C.Xi (completedIndex I J))⁻¹*reciprocitySign (completedIndex I J) s := by
    rw [←map_pow,←map_mul]
    exact hb
  unfold spectralSummand CompletedGauss.columnWeight
  rw [completedCorrection_supported I J hI hJ,squarefreeGaussCoefficient_eq I hsf
    (supported_primaryGenerator_ne_zero I hI)]
  change _*(star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3*
      baseRowCoefficient η C.Xi s hs (primaryGenerator J)^3/(Ideal.absNorm J:ℂ))*_=_
  rw [hangle]
  simp only [star_mul,star_pow]
  calc
    _ = completedMask S D I J*
      (gaussTwo I (supported_primaryGenerator_ne_zero I hI)*
        (star (FiniteGaussPhase.angularFactor (primaryGenerator I))*
         star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3)*star (G (completedIndex I J))*
        (baseRowCoefficient η C.Xi s hs (primaryGenerator I)*baseRowCoefficient η C.Xi s hs (primaryGenerator J)^3)) /
      ((Real.sqrt (Ideal.absNorm I):ℂ)*(Ideal.absNorm J:ℂ))*(fullIdealWeight t I*fullIdealWeight (3*t) J) := by ring
    _ = _ := by rw [hm];ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1430

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PhysicalCoefficientScaling
Source SHA256: a30f9eda13fa221ba38775b389c7925951aefafb772a569c5243bff5d9bb6529
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1431




namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted ProbeRow CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem physical_spectral_coefficient_scale (S : Finset (Ideal O)) (D I J : Ideal O)
    (η : HeckeFamily.Character) (C : CalibrationData) (s : O) (hs : Supported (Ideal.span {s}))
    (hI : Supported I) (hJ : Supported J) (hsf : Squarefree I)
    (hcop : IsCoprime C.generator (completedIndex I J)) (X : ℝ) (hX : 0<X) (t : ℂ) (H : O) :
    let A := completedIndex I J
    let hA := supportedElement_ne_zero A (supported_completed _ _
      ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ))
    let K := elementNorm C.generator*elementNorm s*X
    idealRowHom C.generator (Ideal.span {s}) /
      (C.tau*C.residueMonoid s*(Real.sqrt K:ℂ)) * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*A):ℝ):ℂ)*actualCongruenceCoefficient C A s hA H =
    (Real.sqrt X:ℂ) * completedMask S D I J *
      calibratedHighCoefficient C η I (supported_primaryGenerator_ne_zero I hI) A s hA H /
      ((elementNorm A:ℂ)*(Real.sqrt (Ideal.absNorm I):ℂ)*(Ideal.absNorm J:ℂ)) *
      (fullIdealWeight t I*fullIdealWeight (3*t) J) := by
  dsimp only
  have hA := supportedElement_ne_zero (completedIndex I J) (supported_completed _ _
    ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ))
  have he := physical_poisson_prefactor (elementNorm C.generator) (elementNorm (completedIndex I J))
    (elementNorm s) X (elementNorm_pos _ C.generator_ne_zero) (elementNorm_pos _ hA)
    (elementNorm_pos _ (supportedElement_ne_zero s hs)) hX
  rw [spectralSummand_source_coefficient S D I J η C s hs hI hJ hsf hcop t]
  simp only [elementNorm_mul,Complex.ofReal_div,Complex.ofReal_mul] at he ⊢
  unfold calibratedHighCoefficient
  have hh := congrArg (fun v : ℂ=>v*
    (idealRowHom C.generator (Ideal.span {s})/(C.tau*C.residueMonoid s))*
    (completedMask S D I J *
      (gaussTwo I (supported_primaryGenerator_ne_zero I hI)*
        star (FiniteGaussPhase.angularFactor (completedIndex I J)*ProbePhase.G (completedIndex I J))*
        targetMonoid η (completedIndex I J)*(C.Xi (completedIndex I J))⁻¹*
        ProbePhase.reciprocitySign (completedIndex I J) s)/
      ((Real.sqrt (Ideal.absNorm I):ℂ)*(Ideal.absNorm J:ℂ)))*
    (fullIdealWeight t I*fullIdealWeight (3*t) J)*
    actualCongruenceCoefficient C (completedIndex I J) s hA H) he
  convert hh using 1 <;> ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1431

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PhysicalMellinCoefficient
Source SHA256: 60fb71f6f6d55ef930eafcd18cacdb6889d3bbc58c2c04d6e0d23b4fa1bef4ad
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1432



namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted ProbeRow CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma completedIndex_norm (I J : Ideal O) (hI : Supported I) (hJ : Supported J) :
    elementNorm (completedIndex I J)=(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3 := by
  rw [completedIndex, elementNorm_mul, elementNorm_pow]
  unfold elementNorm
  rw [(primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).1,
    (primaryGenerator_spec J (supported_primaryGenerator_ne_zero J hJ)).1]

theorem physical_mellin_coefficient (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (D I J : Ideal O) (η : HeckeFamily.Character) (s : O) (hs : Supported (Ideal.span {s}))
    (hI : Supported I) (hJ : Supported J) (hsf : Squarefree I)
    (hcop : IsCoprime (calibrationForSet S hS).generator (completedIndex I J*s))
    (X : ℝ) (hX : 0<X) (H : O) (hH : H≠0) (t z : ℂ) :
    let C := calibrationForSet S hS
    let A := completedIndex I J
    let hA := supportedElement_ne_zero A (supported_completed _ _
      ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ))
    let K := elementNorm C.generator*elementNorm s*X
    idealRowHom C.generator (Ideal.span {s}) /
      (C.tau*C.residueMonoid s*(Real.sqrt K:ℂ)) * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*A):ℝ):ℂ)*actualCongruenceCoefficient C A s hA H *
      ((K*elementNorm H/elementNorm ((C.generator*A)*s)):ℂ)^(-z) =
    (X:ℂ)^(1/2-z)*(elementNorm H:ℂ)^(-z)*completedMask S D I J*star (C.residueMonoid H)*
      bareSourceCoefficient η I (supported_primaryGenerator_ne_zero I hI) A s hA H *
      (fullIdealWeight (t+1-z+1/2) I*fullIdealWeight (1+3*(t+1-z)) J) := by
  dsimp only
  have hA : Supported (Ideal.span {completedIndex I J}) := supported_completed _ _ ((supported_span_primaryGenerator_iff I).mpr hI)
    ((supported_span_primaryGenerator_iff J).mpr hJ)
  rw [physical_spectral_coefficient_scale S D I J η (calibrationForSet S hS) s hs hI hJ hsf
    hcop.of_mul_right_left X hX t H]
  rw [calibratedHighCoefficient_eq_bare S hS η I (supported_primaryGenerator_ne_zero I hI)
    (completedIndex I J) s hA hs hcop H]
  have hr := congrArg (fun r : ℝ => (r : ℂ)) (physical_radial_argument
    (calibrationForSet S hS).generator (completedIndex I J) s H X
    (elementNorm_pos _ (calibrationForSet S hS).generator_ne_zero).ne'
    (elementNorm_pos _ (supportedElement_ne_zero s hs)).ne')
  simp only [Complex.ofReal_div, Complex.ofReal_mul] at hr
  simp only [Complex.ofReal_mul]
  rw [hr]
  rw [completedIndex_norm I J hI hJ]
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ.1)
  have hn := sourceNormPower_identity (Ideal.absNorm I) (Ideal.absNorm J) (elementNorm H) X
    hi hj (elementNorm_pos H hH) hX t z
  rw [show -(t+1-z)-1/2= -(t+1-z+1/2) by ring] at hn
  simp only [fullIdealWeight,hI.1,hJ.1,ite_false,Complex.ofReal_natCast,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow] at hn ⊢
  have he := congrArg (fun v : ℂ=>v*completedMask S D I J*
    star ((calibrationForSet S hS).residueMonoid H)*
    bareSourceCoefficient η I (supported_primaryGenerator_ne_zero I hI) (completedIndex I J) s
      (supportedElement_ne_zero _ hA) H) hn
  convert he using 1 <;> ring_nf

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1432

/-! Original module: OAI.NumberTheory.DirichletL.Detector.SpectralCompensation
Source SHA256: 381c5b2cc795b103df2bccb08c84e0e44a6af830085e5039c0079ad61dee1552
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1433




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def spectralCompensatedHigh (S : Finset Id) (T : Finset PrimeIdeal)
    (η : HeckeFamily.Character) (x w z : ℂ) (B q : PrimeIdeal→ℂ) : ℂ :=
  ∑J∈T.powerset,(-1:ℂ)^J.card*(∏P∈J,q P)*(∏P∈T\J,B P)*
    markedIdealHighSeries S (∏P∈T\J,P.val) η 1 x w z

theorem spectralCompensatedHigh_eq_product (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    spectralCompensatedHigh S T η x w z B q=
      markedIdealHighSeries S 1 η 1 x w z *
        ∏P∈T,(B P*idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z-q P) := by
  rw [spectralCompensatedHigh,Finset.prod_sub,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [markedIdealHighSeries_eq_product S hS (T\J)
    (fun P hP=>hT P (Finset.mem_sdiff.mp hP).1) η x w z hx hw hz]
  simp only [mul_div_assoc,Finset.prod_mul_distrib]
  ring

theorem spectralCompensatedHigh_L_factorization (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    spectralCompensatedHigh S T η x w z B q=
      (HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
       HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
       HeckeFamily.LFunction (η.excludePrimes S hS.prime) x * globalClosedCorrection η S x w z) *
        ∏P∈T,(B P*idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z-q P) := by
  rw [spectralCompensatedHigh_eq_product S hS T hT η x w z B q hx hw hz,
    source_principalHigh_L_factorization S hS η x w z hx hw hz]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1433

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CompensationActual
Source SHA256: c7f72f741d57675d44a573b4a6e0f2a62323f193e31b5462d57fe9d1535497ce
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1434


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeEuler ProbeLocal
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma initialPrime_denominators (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ)
    (hx : 0<x.re) (hw : 0<w.re) (hz : 0<z.re) :
    let Q : ℝ := Ideal.absNorm P.val
    (1-coordV Q z≠0) ∧ (1-coordW Q 1 w≠0) ∧
      (1-coordD Q (HeckeFamily.idealCoeff η P.val) 1 x≠0) := by
  dsimp only
  have hQ : (1:ℝ)<Ideal.absNorm P.val := by
    have hh := SmoothMobiusCorrection.prime_norm_two_le P
    exact_mod_cast (by omega : 1<Ideal.absNorm P.val)
  have hQ0 : (0:ℝ)<Ideal.absNorm P.val := by linarith
  constructor
  · apply one_sub_ne_zero_of_norm_lt_one
    rw [coordV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  constructor
  · apply one_sub_ne_zero_of_norm_lt_one
    apply (coordW_norm_le _ hQ0 1 w (by simp)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  · apply one_sub_ne_zero_of_norm_lt_one
    apply (coordD_norm_le _ hQ0 _ 1 x (HeckeFamily.idealCoeff_norm_le_one η P.val) (by simp)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)

lemma idealClosedCorrection_eq_continued (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ) :
    let Q : ℝ := Ideal.absNorm P.val
    idealClosedCorrection η P x w z=continuedCorrection (coordV Q z) (coordW Q 1 w)
      (coordD Q (HeckeFamily.idealCoeff η P.val) 1 x) (idealMarkedClosed η P x w z) := rfl

lemma standardFactor_times_continued (V W D M : ℂ)
    (hV : 1-V≠0) (hW : 1-W≠0) (hD : 1-D≠0) :
    (1-D)/((1-V)*(1-W))*continuedCorrection V W D M=localFactor V W M := by
  unfold continuedCorrection localFactor
  field_simp
  ring

lemma idealHighLocalFactor_eq_raw (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hs : CanonicalQuadraticSieve.Supported P.val) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let Q : ℝ := Ideal.absNorm P.val
    idealHighLocalFactor η P.val x w z=
      localFactor (coordV Q z) (coordW Q 1 w) (idealMarkedClosed η P x w z) := by
  have hd := initialPrime_denominators η P x w z (by linarith) (by linarith) (by linarith)
  have he := idealHighLocalFactor_rational η P hs x w z hx hw hz
  have hc := standardFactor_times_continued (coordV (Ideal.absNorm P.val) z)
    (coordW (Ideal.absNorm P.val) 1 w) (coordD (Ideal.absNorm P.val) (HeckeFamily.idealCoeff η P.val) 1 x)
    (idealMarkedClosed η P x w z) hd.1 hd.2.1 hd.2.2
  rw [←idealClosedCorrection_eq_continued] at hc
  dsimp only at he hc ⊢
  rw [he]
  simpa only [coordV,coordW,coordD,star_one,mul_one,one_mul] using hc

theorem idealCompensatedRatio_eq_continued (S : Finset Id) (hS : SourceExclusions S)
    (η : HeckeFamily.Character) (P : PrimeIdeal) (hP : P.val∉S) (x w z B q : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let Q : ℝ := Ideal.absNorm P.val
    B*idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z-q=
      compensatedReplacement (coordV Q z) (coordW Q 1 w)
        (coordD Q (HeckeFamily.idealCoeff η P.val) 1 x) (idealMarkedClosed η P x w z) B q /
          idealClosedCorrection η P x w z := by
  have hs := outside_prime_supported S hS.bad P hP
  have hd := initialPrime_denominators η P x w z (by linarith) (by linarith) (by linarith)
  have hraw := idealHighLocalFactor_eq_raw η P hs x w z hx hw hz
  have hn := source_idealHighLocalFactor_ne_zero S hS η P hP x w z hx hw hz
  rw [hraw] at hn
  have hH : idealClosedCorrection η P x w z≠0 :=
    factor_ne_zero_of_defect _ ((idealClosedCorrection_bound η P (hS.tail.norm_four P hP)
      x w z (by linarith) (by linarith) (by linarith)).trans (hS.tail.half ⟨P,hP⟩))
  have he := compensatedReplacement_eq_raw (coordV (Ideal.absNorm P.val) z)
    (coordW (Ideal.absNorm P.val) 1 w) (coordD (Ideal.absNorm P.val) (HeckeFamily.idealCoeff η P.val) 1 x)
    (idealMarkedClosed η P x w z) B q hd.1 hd.2.1 hd.2.2 hn
  rw [←continuedCorrection_eq_raw _ _ _ _ hd.1 hd.2.1 hd.2.2,
    ←idealClosedCorrection_eq_continued] at he
  dsimp only at hraw he ⊢
  rw [idealMarkedLocalFactor_rational η P hs x w z hx hz,hraw,he]
  exact (mul_div_cancel_left₀ _ hH).symm

theorem spectralCompensatedHigh_continued (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    spectralCompensatedHigh S T η x w z B q=
      (HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
       HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
       HeckeFamily.LFunction (η.excludePrimes S hS.prime) x * globalClosedCorrection η S x w z) *
        ∏P∈T,(compensatedReplacement (coordV (Ideal.absNorm P.val) z)
          (coordW (Ideal.absNorm P.val) 1 w)
          (coordD (Ideal.absNorm P.val) (HeckeFamily.idealCoeff η P.val) 1 x)
          (idealMarkedClosed η P x w z) (B P) (q P) / idealClosedCorrection η P x w z) := by
  rw [spectralCompensatedHigh_L_factorization S hS T hT η x w z B q hx hw hz]
  congr 1
  apply Finset.prod_congr rfl
  intro P hP
  exact idealCompensatedRatio_eq_continued S hS η P (hT P hP) x w z (B P) (q P) hx hw hz

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1434

/-! Original module: OAI.NumberTheory.DirichletL.Detector.SpectralSupport
Source SHA256: 50d90d7dd10d083f05af694cbf365fab833b6e51ab2632e948ca51ef6f5e81f7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1435



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open ProbeCompleted ProbeRow SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O

lemma supported_of_source_exclusions (S : Finset (Ideal O))
    (hbad : fixedBadPrimes⊆S) (I : Ideal O) (hI : I≠0)
    (hS : ∀P∈S,¬P∣I) : Supported I := by
  refine ⟨hI,?_⟩
  intro P hP
  have hp : Prime P := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  apply (prime_good_iff_not_bad P).mpr
  intro hb
  exact hS P (hbad hb) (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)

lemma spectralSummand_support (S : Finset (Ideal O)) (hbad : fixedBadPrimes⊆S)
    (D I J : Ideal O) (Ψ : O→*ℂ) (t : ℂ)
    (h : spectralSummand S D Ψ t I J≠0) :
    Squarefree I ∧ Supported I ∧ Supported J := by
  have hI : I≠0 := by
    intro hz
    subst I
    exact h (by simp [spectralSummand])
  have hJ : J≠0 := by
    intro hz
    subst J
    exact h (by simp [spectralSummand])
  have hsf : Squarefree I := by
    by_contra hn
    exact h (by simp [spectralSummand,columnWeight,squarefreeGaussCoefficient,hn])
  have hm := spectralSummand_mask_nonzero S D I J Ψ t h
  have hex : ∀P∈S,¬P∣I*J^3 := by
    unfold completedMask at hm
    split_ifs at hm with hd
    · exact hd.2
    · exact False.elim (hm rfl)
  refine ⟨hsf,supported_of_source_exclusions S hbad I hI ?_,
    supported_of_source_exclusions S hbad J hJ ?_⟩
  · intro P hP hd
    exact hex P hP (dvd_mul_of_dvd_left hd _)
  · intro P hP hd
    exact hex P hP (dvd_mul_of_dvd_right (hd.trans (dvd_pow_self J (by decide : 3≠0))) _)

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1435

/-! Original module: OAI.NumberTheory.DirichletL.Detector.MellinGuarded
Source SHA256: cf2dd37a6a13766af08d4f0d0bbee03183f7f99cf40e5c75aea5a5bb2c0723bb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1436




namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion
open ProbeCompleted ProbeRow CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def physicalMellinCoefficientTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D I J : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (X : ℝ) (H : O) (t z : ℂ) : ℂ :=
  if hA : completedIndex I J≠0 then
    let K := elementNorm C.generator*elementNorm s*X
    idealRowHom C.generator (Ideal.span {s}) /
      (C.tau*C.residueMonoid s*(Real.sqrt K:ℂ)) * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*completedIndex I J):ℝ):ℂ)*
      actualCongruenceCoefficient C (completedIndex I J) s hA H *
      ((K*elementNorm H/elementNorm ((C.generator*completedIndex I J)*s)):ℂ)^(-z)
  else 0

def guardedHighMellinCoefficient (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D I J : Ideal O) (s : O) (X : ℝ) (H : O) (x z : ℂ) : ℂ :=
  if h : Squarefree I ∧ Supported I ∧ Supported J then
    (X:ℂ)^(1/2-z)*(elementNorm H:ℂ)^(-z)*completedMask S D I J*star (C.residueMonoid H)*
      bareSourceCoefficient η I (supported_primaryGenerator_ne_zero I h.2.1)
        (completedIndex I J) s (supportedElement_ne_zero _ (supported_completed _ _
          ((supported_span_primaryGenerator_iff I).mpr h.2.1)
          ((supported_span_primaryGenerator_iff J).mpr h.2.2))) H *
      (fullIdealWeight (x+1/2) I*fullIdealWeight (1+3*x) J)
  else 0

theorem physicalMellinCoefficientTerm_eq_guarded (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (D I J : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (hcs : IsCoprime (calibrationForSet S hS).generator s)
    (X : ℝ) (hX : 0<X) (H : O) (hH : H≠0) (t z : ℂ) :
    physicalMellinCoefficientTerm η (calibrationForSet S hS) S D I J s hs X H t z=
      guardedHighMellinCoefficient η (calibrationForSet S hS) S D I J s X H (t+1-z) z := by
  by_cases hg : Squarefree I ∧ Supported I ∧ Supported J
  · have hA : completedIndex I J≠0 := supportedElement_ne_zero _ (supported_completed _ _
      ((supported_span_primaryGenerator_iff I).mpr hg.2.1)
      ((supported_span_primaryGenerator_iff J).mpr hg.2.2))
    rw [physicalMellinCoefficientTerm,dite_eq_left hA,guardedHighMellinCoefficient,dite_eq_left hg]
    dsimp only
    by_cases hm : completedMask S D I J=0
    · simp only [spectralSummand,hm,zero_mul,mul_zero]
    · have hc : IsCoprime (calibrationForSet S hS).generator (completedIndex I J) := by
        apply calibrationForSet_coprime_of_excluded S hS
        rw [completedIndex_eq_primaryGenerator] at hA ⊢
        rw [(primaryGenerator_spec (I*J^3) hA).1]
        unfold completedMask at hm
        split_ifs at hm with hd
        · exact hd.2
        · exact False.elim (hm rfl)
      exact physical_mellin_coefficient S hS D I J η s hs hg.2.1 hg.2.2 hg.1
        (hc.mul_right hcs) X hX H hH t z
  · have hz : spectralSummand S D (baseRowCoefficient η (calibrationForSet S hS).Xi s hs) t I J=0 := by
      by_contra hn
      exact hg (spectralSummand_support S hbad D I J _ t hn)
    rw [guardedHighMellinCoefficient,dite_eq_right hg]
    unfold physicalMellinCoefficientTerm
    split_ifs <;> simp only [hz,mul_zero,zero_mul]

theorem guardedHighMellinCoefficient_eq_high (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (D I J K : Ideal O)
    (hK : Supported K) (hKS : ∀P∈S,¬P∣K) (X : ℝ) (H : O) (x w z : ℂ) :
    guardedHighMellinCoefficient η C S D I J (primaryGenerator K) X H x z *
      fullIdealWeight w K =
    (X:ℂ)^(1/2-z)*(elementNorm H:ℂ)^(-z)*star (C.residueMonoid H)*
      markedIdealHighSummand S D η H x w z I J K 1 := by
  have h1 : ∀P∈S,¬P∣(1:Ideal O) := by
    intro P hP hd
    exact (hS P hP).not_isUnit (isUnit_of_dvd_one hd)
  have hw : fullIdealWeight (6*z) (1:Ideal O)=1 := (IdealEuler.normWeight (6*z)).map_one
  unfold guardedHighMellinCoefficient markedIdealHighSummand highIdealMask
    bareIdealHighSummand bareIdealHighCoefficient
  simp only [ite_eq_left hKS,ite_eq_left h1,mul_one,hw,primaryGenerator_one,one_pow]
  by_cases hg : Squarefree I ∧ Supported I ∧ Supported J
  · have hfull : Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported (1:Ideal O) :=
      ⟨hg.1,hg.2.1,hg.2.2,hK,supported_one_ideal⟩
    rw [dite_eq_left hg,dite_eq_left hfull]
    dsimp only [completedIndex]
    ring
  · have hfull : ¬(Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported (1:Ideal O)) :=
      fun h=>hg ⟨h.1,h.2.1,h.2.2.1⟩
    rw [dite_eq_right hg,dite_eq_right hfull]
    simp only [mul_zero,zero_mul]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1436

/-! Original module: OAI.NumberTheory.DirichletL.Detector.SixthMask
Source SHA256: 494806ed075034ccf48004359c047e57077210b1a189f075bb7fec265c0b54f4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1437



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve CubicEisenstein
open HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O

lemma calibration_sixth_ideal_mask (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (L : Ideal O) :
    (calibrationForSet S hS).residueMonoid (idealGenerator L)^6=
      if ∀P∈S,¬P∣L then 1 else 0 := by
  by_cases hL : ∀P∈S,¬P∣L
  · rw [ite_eq_left hL]
    apply calibrationForSet_residue_sixth
    apply calibrationForSet_coprime_of_excluded
    simpa only [span_idealGenerator] using hL
  · rw [ite_eq_right hL]
    have hz : (calibrationForSet S hS).residueMonoid (idealGenerator L)=0 := by
      by_contra hn
      have hu := (calibrationForSet S hS).residue.apply_ne_zero_iff.mp hn
      have hc := (isUnit_quotient_span_iff (calibrationForSet S hS).generator (idealGenerator L)).mp hu
      have ho := (calibrationForSet_coprime_iff S hS (idealGenerator L)).mp hc
      apply hL
      intro P hP hd
      apply ho P hP
      apply (Ideal.dvd_iff_le.mp hd)
      have hm : idealGenerator L∈Ideal.span ({idealGenerator L}:Set O) := Ideal.subset_span (by simp)
      rw [span_idealGenerator L] at hm
      exact hm
    rw [hz,zero_pow (by decide : 6≠0)]

lemma calibration_sixth_frequency_mask (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (u : O) (L : Ideal O) :
    star ((calibrationForSet S hS).residueMonoid (u*idealGenerator L^6))=
      star ((calibrationForSet S hS).residueMonoid u)*(if ∀P∈S,¬P∣L then 1 else 0) := by
  rw [map_mul,map_pow,calibration_sixth_ideal_mask]
  split_ifs <;> simp only [mul_one,mul_zero,star_zero]

lemma sixthFrequencyWeight (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal) (z : ℂ) :
    frequencyWeight z (sixthFrequencyEquiv p)=
      frequencyWeight z ⟨p.1.val,p.1.property.1⟩*fullIdealWeight (6*z) p.2.val := by
  have hu : 0<elementNorm p.1.val := elementNorm_pos _ p.1.property.1
  have hl : 0<(Ideal.absNorm p.2.val:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.2.property)
  have hn : elementNorm (sixthFrequencyEquiv p).val=
      elementNorm p.1.val*(Ideal.absNorm p.2.val:ℝ)^6 := by
    unfold elementNorm
    exact_mod_cast rowMap_norm p
  simp only [frequencyWeight,fullIdealWeight,ite_eq_right p.2.property,hn,Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg hu.le (pow_nonneg hl.le 6)]
  congr 1
  have he := Complex.cpow_mul_ofReal_nonneg hl.le (6:ℝ) (-z)
  simp only [Real.rpow_ofNat,Complex.ofReal_pow,Complex.ofReal_ofNat,Complex.ofReal_natCast] at he
  simp only [Complex.ofReal_pow,Complex.ofReal_natCast]
  rw [←he]
  congr 1
  ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1437

/-! Original module: OAI.NumberTheory.DirichletL.Moments.Active
Source SHA256: 5191b04dec92cf69d89703a75265c192d84b1101a54e1b8a4f43ec9d0666e173
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1438



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentActive
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
open CanonicalRowCompletion CenteredMomentCanonical

def netExponent (c d : ℕ) : ℕ := (c + 5 * d) % 6

theorem local_pair_reduction (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (c d : ℕ) (x : O ⧸ P) :
    (actualSextic P hg ^ c) x * star ((actualSextic P hg ^ d) x) =
      (actualSextic P hg ^ netExponent c d) x := by
  have h6 : actualSextic P hg ^ 6 = 1 := by
    rw [← actualSextic_order_six P hg hchar]
    exact pow_orderOf_eq_one _
  have h5 : actualSextic P hg ^ 5 = (actualSextic P hg)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa only [← pow_succ] using h6
  rw [MulChar.star_apply', ← MulChar.mul_apply]
  congr 1
  unfold netExponent
  rw [← actualSextic_order_six P hg hchar, pow_mod_orderOf,
    pow_add, pow_mul, h5, inv_pow]

def activeSupport {ι : Type*} (B : Finset ι) (c d : ι → ℕ) : Finset ι :=
  B.filter (fun i => netExponent (c i) (d i) ≠ 0)

def principalSupport {ι : Type*} (B : Finset ι) (c d : ι → ℕ) : Finset ι :=
  B.filter (fun i => netExponent (c i) (d i) = 0)

theorem netExponent_ne_zero {ι : Type*} (B : Finset ι) (c d : ι → ℕ)
    (i : activeSupport B c d) : netExponent (c i.val) (d i.val) ≠ 0 :=
  (Finset.mem_filter.mp i.property).2

theorem netExponent_lt_six (c d : ℕ) : netExponent c d < 6 := Nat.mod_lt _ (by decide)

theorem principal_product_eq_mask {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (B : Finset ι) (z : O) :
    (∏ i ∈ B, (1 : MulChar (O ⧸ P i) ℂ) (Ideal.Quotient.mk (P i) z)) =
      rowCoprimeMask P B z := by
  by_cases h : ∃ i ∈ B, z ∈ P i
  · rw [rowCoprimeMask, ite_eq_left h]
    obtain ⟨i, hi, hz⟩ := h
    apply Finset.prod_eq_zero hi
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, MulChar.map_zero]
  · rw [rowCoprimeMask, ite_eq_right h]
    apply Finset.prod_eq_one
    intro i hi
    apply MulChar.one_apply
    let : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
    apply isUnit_iff_ne_zero.mpr
    exact fun hz => h ⟨i, hi, Ideal.Quotient.eq_zero_iff_mem.mp hz⟩

variable {ι : Type*}

theorem common_ideal_pair_active (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (B : Finset ι) (c d : ι → ℕ)
    (hc : ∀ i ∈ B, c i ≠ 0) (hd : ∀ i ∈ B, d i ≠ 0) (z : O) :
    idealRowHom z (∏ i ∈ B, P i ^ c i) *
      star (idealRowHom z (∏ i ∈ B, P i ^ d i)) =
      rowCoprimeMask P (principalSupport B c d) z *
        finiteSexticRow (fun i : activeSupport B c d => P i.val)
          (fun i => hg i.val) (fun i => netExponent (c i.val) (d i.val)) z := by
  let f := fun i => (actualSextic (P i) (hg i) ^ netExponent (c i) (d i))
    (Ideal.Quotient.mk (P i) z)
  have hlocal : idealRowHom z (∏ i ∈ B, P i ^ c i) *
      star (idealRowHom z (∏ i ∈ B, P i ^ d i)) = ∏ i ∈ B, f i := by
    simp only [map_prod, map_pow, star_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [idealRowHom_prime z (P i) (hg i),
      ← MulChar.pow_apply' _ (hc i hi), ← MulChar.pow_apply' _ (hd i hi)]
    exact local_pair_reduction (P i) (hg i) (hchar i) (c i) (d i) _
  have hzero : (∏ i ∈ B.filter (fun i => netExponent (c i) (d i) = 0), f i) =
      rowCoprimeMask P (principalSupport B c d) z := by
    rw [← principal_product_eq_mask]
    apply Finset.prod_congr rfl
    intro i hi
    have he := (Finset.mem_filter.mp hi).2
    simp only [f, he, pow_zero]
  rw [hlocal, ← Finset.prod_filter_mul_prod_filter_not B
    (fun i => netExponent (c i) (d i) = 0) f, hzero]
  congr 1
  exact (Finset.prod_coe_sort (s := activeSupport B c d) (f := f)).symm

theorem activePrimes_pairwise_coprime (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (B : Finset ι) (c d : ι → ℕ) :
    Pairwise (Function.onFun IsCoprime (fun i : activeSupport B c d => P i.val)) := by
  intro i j hij
  apply Ideal.isCoprime_of_isMaximal
  exact fun he => hij (Subtype.ext (hinj he))

theorem active_gauss_norm (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, goodLambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2) (B : Finset ι) (c d : ι → ℕ) :
    ‖canonicalNormalizedGauss (fun i : activeSupport B c d => P i.val)
      (activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
      (fun i => netExponent (c i.val) (d i.val))‖ = 1 :=
  norm_canonicalNormalizedGauss (fun i : activeSupport B c d => P i.val)
    (activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
    (fun i => hchar i.val) (fun i => netExponent (c i.val) (d i.val))
    (netExponent_ne_zero B c d) (fun _i => netExponent_lt_six _ _)

open ConcreteTraceCRT EisensteinSchwartzPoisson

theorem common_ideal_pair_poisson (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, goodLambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (B : Finset ι) (c d : ι → ℕ)
    (hc : ∀ i ∈ B, c i ≠ 0) (hd : ∀ i ∈ B, d i ≠ 0)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    let Q := fun i : activeSupport B c d => P i.val
    let row := finiteSexticRow Q (fun i => hg i.val)
      (fun i => netExponent (c i.val) (d i.val))
    let r := finitePrimeModulus Q
    (∑' z : O, (idealRowHom z (∏ i ∈ B, P i ^ c i) *
      star (idealRowHom z (∏ i ∈ B, P i ^ d i))) *
      W (‖eisEmbedding z‖ ^ 2 / K)) =
      ((K : ℂ) * canonicalNormalizedGauss Q
        (activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
        (fun i => netExponent (c i.val) (d i.val)) / (‖eisEmbedding r‖ : ℂ)) *
      ∑ E ∈ (principalSupport B c d).powerset,
        let e := primeSubsetGenerator P E
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) * row e /
          (‖eisEmbedding e‖ ^ 2 : ℝ)) *
        ∑' h : O, star (row h) * paperRadialFourier W
          (K * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding r‖ ^ 2)) := by
  simp_rw [common_ideal_pair_active P hg hchar B c d hc hd]
  exact canonical_masked_radial_poisson_collected P hinj (principalSupport B c d)
    (fun i : activeSupport B c d => P i.val)
    (activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
    (fun i => hchar i.val) (fun i => netExponent (c i.val) (d i.val))
    (netExponent_ne_zero B c d) (fun i => netExponent_lt_six _ _) W K hK

end SevenEighths.CenteredMomentActive
end

end OAI
end OAIOriginalModule1438

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstMixed
Source SHA256: 090a4c5a631abc46004b0ad7a085c8d6f906fb3f3690ff9d353ade5566e50322
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1439


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstMixed
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

theorem frequencyReduction_comp (d n M : O) (hd : d∣n) (hn : n∣M) (x : Residue M) :
    frequencyReduction d n hd (frequencyReduction n M hn x)=frequencyReduction d M (hd.trans hn) x := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [frequencyReduction_mk]

theorem three_factor_mixed_fourier (a b c : O) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (habc : IsCoprime a (b*c)) (hbc : IsCoprime b c)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue c)]
    [Fintype (Residue (b*c))] [Fintype (Residue (a*(b*c)))]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (G : Residue c → ℂ)
    (h : Residue (a*(b*c))) :
    (∑ x : Residue (a*(b*c)),
      χa (frequencyReduction a (a*(b*c)) (dvd_mul_right _ _) x)*
      χb (frequencyReduction b (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x)*
      G (frequencyReduction c (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x)*
        quotientTrace (a*(b*c)) (mul_ne_zero ha (mul_ne_zero hb hc)) (h*x)) =
      χa (Ideal.Quotient.mk _ (b*c))*χb (Ideal.Quotient.mk _ (a*c))*
        residueGauss a ha χa (frequencyReduction a (a*(b*c)) (dvd_mul_right _ _) h)*
        residueGauss b hb χb (frequencyReduction b (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) h)*
        (∑ y : Residue c,G (Ideal.Quotient.mk _ (a*b)*y)*
          quotientTrace c hc (frequencyReduction c (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) h*y)) := by
  let F : Residue (b*c) → ℂ := fun y =>
    χb (frequencyReduction b (b*c) (dvd_mul_right _ _) y)*
      G (frequencyReduction c (b*c) (dvd_mul_left _ _) y)
  let h' := frequencyReduction (b*c) (a*(b*c)) (dvd_mul_left _ _) h
  have he (x : Residue (a*(b*c))) :
      χa (frequencyReduction a (a*(b*c)) (dvd_mul_right _ _) x)*
        F (frequencyReduction (b*c) (a*(b*c)) (dvd_mul_left _ _) x) =
      χa (frequencyReduction a (a*(b*c)) (dvd_mul_right _ _) x)*
        χb (frequencyReduction b (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x)*
        G (frequencyReduction c (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x) := by
    dsimp only [F]
    rw [frequencyReduction_comp,frequencyReduction_comp]
    ring
  simp_rw [← he]
  rw [ProbePhysical.coprime_mixed_fourier a (b*c) ha (mul_ne_zero hb hc) habc χa F h]
  have hf (y : Residue (b*c)) : F (Ideal.Quotient.mk _ a*y)=
      χb (Ideal.Quotient.mk _ a)*
        (χb (frequencyReduction b (b*c) (dvd_mul_right _ _) y)*
          G (Ideal.Quotient.mk _ a*frequencyReduction c (b*c) (dvd_mul_left _ _) y)) := by
    simp only [F,map_mul,frequencyReduction_mk]
    ring
  simp_rw [hf,mul_assoc]
  rw [← Finset.mul_sum]
  have hh := ProbePhysical.coprime_mixed_fourier b c hb hc hbc χb
    (fun y => G (Ideal.Quotient.mk _ a*y)) h'
  simp only [mul_assoc] at hh
  rw [hh]
  simp only [h',frequencyReduction_comp,map_mul,mul_assoc]
  ring

end SevenEighths.CenteredMomentFirstMixed

end

end OAI
end OAIOriginalModule1439

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstReduced
Source SHA256: 47b1c62b2c400acbb50b3d049d1751a5c5a76071f7ab5a97d77168daccc7e764
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1440



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstReduced
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier
open CenteredMomentFirstMixed CenteredMomentActive
local notation "O" => ActualEisensteinCubic.O

def tripleRow (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ) (z : O) : ℂ :=
  χa (Ideal.Quotient.mk _ z)*χb (Ideal.Quotient.mk _ z)*G (Ideal.Quotient.mk _ z)

def tripleResidue (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ) (x : Residue (a*(b*r))) : ℂ :=
  χa (frequencyReduction a _ (dvd_mul_right _ _) x)*
    χb (frequencyReduction b _ (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x)*
    G (frequencyReduction r _ (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x)

@[simp] theorem tripleResidue_mk (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ) (z : O) :
    tripleResidue a b r χa χb G (Ideal.Quotient.mk _ z)=tripleRow a b r χa χb G z := by
  simp only [tripleResidue,tripleRow,frequencyReduction_mk]

theorem tripleRow_mul (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ)
    (hG : ∀ x y,G (x*y)=G x*G y) (x y : O) :
    tripleRow a b r χa χb G (x*y)=tripleRow a b r χa χb G x*tripleRow a b r χa χb G y := by
  simp only [tripleRow,map_mul,hG]
  ring

def tripleFourier (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (h : O) : ℂ :=
  ∑' x : Residue (a*(b*r)),tripleResidue a b r χa χb G x*
    quotientTrace (a*(b*r)) (mul_ne_zero ha (mul_ne_zero hb hr)) (Ideal.Quotient.mk _ h*x)

theorem tripleRow_radial_summable (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z : O => tripleRow a b r χa χb G z*W (‖eisEmbedding z‖^2/K)) := by
  let := finite_quotient_span (mul_ne_zero ha (mul_ne_zero hb hr))
  let : Fintype (Residue (a*(b*r))) := Fintype.ofFinite _
  have hh := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
    (Ideal.Quotient.mk (Ideal.span {a*(b*r)})) (tripleResidue a b r χa χb G)
  simpa only [tripleResidue_mk,scaledRadialTest_apply] using hh

theorem tripleRow_poisson (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑' z : O,tripleRow a b r χa χb G z*W (‖eisEmbedding z‖^2/K)) =
      ((K/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*∑' h : O,
        tripleFourier a b r ha hb hr χa χb G h*
          paperRadialFourier W (K*‖eisEmbedding h‖^2/‖eisEmbedding (a*(b*r))‖^2) := by
  let := finite_quotient_span (mul_ne_zero ha (mul_ne_zero hb hr))
  let : Fintype (Residue (a*(b*r))) := Fintype.ofFinite _
  have hh := actual_radial_paper_poisson_trace W K hK (a*(b*r))
    (mul_ne_zero ha (mul_ne_zero hb hr)) (tripleResidue a b r χa χb G)
  simpa only [tripleResidue_mk,tripleFourier,quotientTrace,tsum_fintype,Complex.real_smul] using hh

theorem masked_triple_poisson {α : Type*} (P : α → Ideal O)
    [∀ i,(P i).IsMaximal] (hinj : Function.Injective P) (S : Finset α)
    (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (hG : ∀ x y,G (x*y)=G x*G y)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑' z : O,rowCoprimeMask P S z*tripleRow a b r χa χb G z*W (‖eisEmbedding z‖^2/K)) =
      ∑ E ∈ S.powerset,
        let e := primeSubsetGenerator P E
        let k := K/‖eisEmbedding e‖^2
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E,P i):ℂ)*tripleRow a b r χa χb G e*
          (((k/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*∑' h : O,
            tripleFourier a b r ha hb hr χa χb G h*
              paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a*(b*r))‖^2)) := by
  rw [tsum_masked_radial_dilations P hinj S _ (tripleRow_mul a b r χa χb G hG) W K
    (tripleRow_radial_summable a b r ha hb hr χa χb G W K hK)]
  apply Finset.sum_congr rfl
  intro E hE
  rw [tripleRow_poisson a b r ha hb hr χa χb G W _ (primeSubset_reducedScale_pos P E hK)]

theorem principalSexticRow_mul {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (j : ι → ℕ) (r : O) (hr : Ideal.span {r}=∏ i,P i) (x y : Residue r) :
    principalSexticRow P hcop hg j r hr (x*y)=
      principalSexticRow P hcop hg j r hr x*principalSexticRow P hcop hg j r hr y := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul,principalSexticRow_mk P hcop hg j r hr (x*y),
    principalSexticRow_mk P hcop hg j r hr x,principalSexticRow_mk P hcop hg j r hr y,
    finiteSexticRow_mul P hg j x y]

theorem common_residual_reduced_poisson {ι : Type*}
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i) (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (B : Finset ι) (c d : ι → ℕ) (hc : ∀ i∈B,c i≠0) (hd : ∀ i∈B,d i≠0)
    (a b : O) (ha : a≠0) (hb : b≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    let Q := fun i : activeSupport B c d => P i.val
    let hj := fun i : activeSupport B c d => netExponent (c i.val) (d i.val)
    let r := finitePrimeModulus Q
    let G := principalSexticRow Q (activePrimes_pairwise_coprime P hinj B c d)
      (fun i => hg i.val) hj r (span_finitePrimeModulus Q)
    (∑' z : O,χa (Ideal.Quotient.mk _ z)*χb (Ideal.Quotient.mk _ z)*
      (CanonicalRowCompletion.idealRowHom z (∏ i∈B,P i^c i)*
        star (CanonicalRowCompletion.idealRowHom z (∏ i∈B,P i^d i)))*
      W (‖eisEmbedding z‖^2/K)) =
      ∑ E ∈ (principalSupport B c d).powerset,
        let e := primeSubsetGenerator P E
        let k := K/‖eisEmbedding e‖^2
        (UniqueFactorizationMonoid.moebius (∏ i∈E,P i):ℂ)*tripleRow a b r χa χb G e*
          (((k/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*∑' h : O,
            tripleFourier a b r ha hb (finitePrimeModulus_ne_zero Q) χa χb G h*
              paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a*(b*r))‖^2)) := by
  dsimp only
  rw [← masked_triple_poisson P hinj (principalSupport B c d) a b _ ha hb
    (finitePrimeModulus_ne_zero _) χa χb _
    (principalSexticRow_mul _ _ _ _ _ _) W K hK]
  apply tsum_congr
  intro z
  rw [common_ideal_pair_active P hg hchar B c d hc hd]
  simp only [tripleRow,principalSexticRow_mk (fun i : activeSupport B c d => P i.val)
    (activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
    (fun i => netExponent (c i.val) (d i.val)) _ (span_finitePrimeModulus _) z]
  ring

end SevenEighths.CenteredMomentFirstReduced

end

end OAI
end OAIOriginalModule1440

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstActiveFourier
Source SHA256: 43e18188c6bce00c925ac8b8b3e723266460753a19f882c58abdd88a6a0306bd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1441


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstActiveFourier
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier
open CenteredMomentFirstMixed CenteredMomentFirstReduced
local notation "O" => ActualEisensteinCubic.O

theorem shifted_active_fourier {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6) (v h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    (∑' x : Residue r,G (Ideal.Quotient.mk _ v*x)*
      quotientTrace r (finitePrimeModulus_ne_zero P) (Ideal.Quotient.mk _ h*x)) =
      finiteSexticRow P hg j v*star (finiteSexticRow P hg j h)*canonicalGaussSum P hcop hg j := by
  dsimp only
  let := finite_quotient_span (finitePrimeModulus_ne_zero P)
  let : Fintype (Residue (finitePrimeModulus P)) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (span_finitePrimeModulus P)
  let : Fintype (O ⧸ ∏ i,P i) := Fintype.ofEquiv (Residue (finitePrimeModulus P)) e.toEquiv
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  rw [tsum_fintype]
  simp_rw [CenteredMomentFirstReduced.principalSexticRow_mul P hcop hg j
    (finitePrimeModulus P) (span_finitePrimeModulus P),
    principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P),mul_assoc]
  rw [← Finset.mul_sum,canonical_principal_gauss_transform P hcop hg hchar j hj0 hj6,
    principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P)]
  change finiteSexticRow P hg j v*(star (finiteSexticRow P hg j h)*canonicalGaussSum P hcop hg j)=_
  ring

theorem tripleFourier_active {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (a b : O) (ha : a≠0) (hb : b≠0)
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    tripleFourier a b r ha hb (finitePrimeModulus_ne_zero P) χa χb G h =
      χa (Ideal.Quotient.mk _ (b*r))*χb (Ideal.Quotient.mk _ (a*r))*
        residueGauss a ha χa (Ideal.Quotient.mk _ h)*residueGauss b hb χb (Ideal.Quotient.mk _ h)*
        (finiteSexticRow P hg j (a*b)*star (finiteSexticRow P hg j h)*canonicalGaussSum P hcop hg j) := by
  dsimp only
  let := finite_quotient_span ha
  let := finite_quotient_span hb
  let := finite_quotient_span (finitePrimeModulus_ne_zero P)
  let := finite_quotient_span (mul_ne_zero hb (finitePrimeModulus_ne_zero P))
  let := finite_quotient_span (mul_ne_zero ha (mul_ne_zero hb (finitePrimeModulus_ne_zero P)))
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (finitePrimeModulus P)) := Fintype.ofFinite _
  let : Fintype (Residue (b*finitePrimeModulus P)) := Fintype.ofFinite _
  let : Fintype (Residue (a*(b*finitePrimeModulus P))) := Fintype.ofFinite _
  unfold tripleFourier tripleResidue
  rw [tsum_fintype,three_factor_mixed_fourier a b (finitePrimeModulus P) ha hb
    (finitePrimeModulus_ne_zero P) har hbr]
  simp only [frequencyReduction_mk]
  have hs := shifted_active_fourier P hcop hg hchar j hj0 hj6 (a*b) h
  dsimp only at hs
  rw [tsum_fintype] at hs
  rw [hs]

theorem tripleFourier_active_norm_le {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (a b : O) (ha : a≠0) (hb : b≠0)
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    ‖tripleFourier a b r ha hb (finitePrimeModulus_ne_zero P) χa χb G h‖ ≤
      ‖eisEmbedding r‖*‖residueGauss a ha χa (Ideal.Quotient.mk _ h)‖*
        ‖residueGauss b hb χb (Ideal.Quotient.mk _ h)‖ := by
  dsimp only
  let := finite_quotient_span ha
  let := finite_quotient_span hb
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  rw [tripleFourier_active P hcop hg hchar j hj0 hj6 a b ha hb har hbr]
  simp only [norm_mul,norm_star,norm_canonicalGaussSum P hcop hg hchar j hj0 hj6]
  have hχa := QuadraticInitialBound.norm_finite_character_le_one χa (Ideal.Quotient.mk _ (b*finitePrimeModulus P))
  have hχb := QuadraticInitialBound.norm_finite_character_le_one χb (Ideal.Quotient.mk _ (a*finitePrimeModulus P))
  have hv := QuadraticInitialBound.finiteSexticRow_norm_le_one P hg j (a*b)
  have hh := QuadraticInitialBound.finiteSexticRow_norm_le_one P hg j h
  calc
    _ ≤ 1*1*‖residueGauss a ha χa (Ideal.Quotient.mk _ h)‖*
      ‖residueGauss b hb χb (Ideal.Quotient.mk _ h)‖*(1*1*‖eisEmbedding (finitePrimeModulus P)‖) := by
        gcongr
    _ = _ := by ring

end SevenEighths.CenteredMomentFirstActiveFourier

end

end OAI
end OAIOriginalModule1441

/-! Original module: OAI.NumberTheory.DirichletL.Moments.PrimaryCharacter
Source SHA256: 2862ea64b31464b3f3aae20bd6734bf165509076c2d9401baa87ba5995a7590c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1442


namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentPrimaryCharacter
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentPrimary CenteredMomentCommonSupport
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def rawPrimaryHom (r : O) (χ : MulChar (Residue r) ℂ) : O →* ℂ where
  toFun n := primaryIdealCharacter r χ (Ideal.span {n})
  map_one' := by simp [← Ideal.one_eq_top]
  map_mul' x y := by rw [← Ideal.span_singleton_mul_span_singleton,map_mul]

def maskedPrimaryHom (r : O) (χ : MulChar (Residue r) ℂ) : O →* ℂ :=
  coprimalityMask (3:O)*rawPrimaryHom r χ

theorem maskedPrimaryHom_unit_mul (r : O) (χ : MulChar (Residue r) ℂ) (u : Oˣ) (n : O) :
    maskedPrimaryHom r χ ((u:O)*n)=maskedPrimaryHom r χ n := by
  change (if IsCoprime (3:O) ((u:O)*n) then (1:ℂ) else 0)*
      primaryIdealCharacter r χ (Ideal.span {(u:O)*n}) =
    (if IsCoprime (3:O) n then (1:ℂ) else 0)*primaryIdealCharacter r χ (Ideal.span {n})
  rw [isCoprime_mul_unit_left_right u.isUnit,Ideal.span_singleton_mul_left_unit u.isUnit]

theorem maskedPrimaryHom_ramified (r : O) (χ : MulChar (Residue r) ℂ) (n : O) (hn : λ₀∣n) :
    maskedPrimaryHom r χ n=0 := by
  have h3 : λ₀∣(3:O) := (dvd_pow_self λ₀ (by decide : 2≠0)).trans ActualEisensteinCubic.lambda_sq_dvd_three
  have hc : ¬IsCoprime (3:O) n := fun hc =>
    PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit (hc.isUnit_of_dvd' h3 hn)
  change (if IsCoprime (3:O) n then (1:ℂ) else 0)*_=0
  rw [ite_eq_right hc,zero_mul]

theorem maskedPrimaryHom_primary (r : O) (χ : MulChar (Residue r) ℂ) (n : O)
    (hn : λ₀^2∣n-1) : maskedPrimaryHom r χ n=χ (Ideal.Quotient.mk _ n) := by
  change (if IsCoprime (3:O) n then (1:ℂ) else 0)*
    χ (Ideal.Quotient.mk _ (CompletedGauss.primaryGenerator (Ideal.span {n})))=_
  rw [ite_eq_left (CubicEisenstein.primary_coprime_three n hn).symm,one_mul,
    CompletedGauss.primaryGenerator_span n (CubicJacobiGlobal.primary_ne_zero n hn) hn]

theorem maskedPrimaryHom_periodic (r : O) (χ : MulChar (Residue r) ℂ) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {3*r}) (maskedPrimaryHom r χ) := by
  let F : O →* ℂ := χ.toMonoidHom.comp (Ideal.Quotient.mk (Ideal.span {r})).toMonoidHom
  apply periodic_of_primary _ _ _ F _ (maskedPrimaryHom_unit_mul r χ)
    (maskedPrimaryHom_ramified r χ) (maskedPrimaryHom_primary r χ)
  · apply Ideal.span_singleton_le_span_singleton.mpr
    exact ActualEisensteinCubic.lambda_sq_dvd_three.trans (dvd_mul_right _ _)
  · intro x y hxy
    apply congrArg χ
    apply Ideal.Quotient.eq.mpr
    exact Ideal.mem_span_singleton.mpr ((dvd_mul_left r 3).trans (Ideal.mem_span_singleton.mp hxy))

def primaryCharacter (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) : Character :=
  rowCharacter (Ideal.span {3*r})
    (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (by norm_num) hr))
    (maskedPrimaryHom r χ) (maskedPrimaryHom_periodic r χ)
    (fun u => by simpa only [mul_one,map_one] using maskedPrimaryHom_unit_mul r χ u 1)

@[simp] theorem primaryCharacter_modulus (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) :
    (primaryCharacter r hr χ).modulus=Ideal.span {3*r} := rfl

theorem primaryCharacter_primary (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) (n : O)
    (hn : λ₀^2∣n-1) : elementCoeff (primaryCharacter r hr χ) n=χ (Ideal.Quotient.mk _ n) := by
  rw [primaryCharacter,elementCoeff_rowCharacter,maskedPrimaryHom_primary r χ n hn]
  split_ifs with hc
  · rfl
  · symm
    apply MulChar.map_nonunit
    intro hu
    apply hc
    apply isUnit_residue_of_coprime
    apply (CubicEisenstein.primary_coprime_three n hn).symm.mul_left
    exact (CubicEisenstein.isUnit_quotient_span_iff r n).mp hu

theorem primaryCharacter_all (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) (n : O) :
    elementCoeff (primaryCharacter r hr χ) n=maskedPrimaryHom r χ n := by
  by_cases hn : λ₀∣n
  · rw [primaryCharacter,elementCoeff_rowCharacter,maskedPrimaryHom_ramified r χ n hn]
    split_ifs <;> rfl
  · have hg := (PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff n).mpr hn
    have hs := CompletedGauss.primaryGenerator_spec (Ideal.span {n}) hg
    obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs.1.symm
    have hp : λ₀^2∣(u:O)*n-1 := by
      have hp' : λ₀^2∣CompletedGauss.primaryGenerator (Ideal.span {n})-1 := hs.2
      rwa [mul_comm,hu]
    rw [← elementCoeff_unit_mul (primaryCharacter r hr χ) u n,
      ← maskedPrimaryHom_unit_mul r χ u n,primaryCharacter_primary r hr χ _ hp,
      maskedPrimaryHom_primary r χ _ hp]

theorem primaryCharacter_ideal (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ)
    (I : Ideal O) (hI : Supported I) :
    idealCoeff (primaryCharacter r hr χ) I=
      χ (Ideal.Quotient.mk _ (CompletedGauss.primaryGenerator I)) := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := CompletedGauss.primaryGenerator_spec I hn
  calc
    _ = elementCoeff (primaryCharacter r hr χ) (CompletedGauss.primaryGenerator I) := by
      rw [← idealCoeff_span _ hn,hs.1]
    _ = _ := primaryCharacter_primary r hr χ _ hs.2

theorem primaryCharacter_modulus_norm (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) :
    (primaryCharacter r hr χ).modulus.absNorm=
      (Ideal.span {(3:O)}).absNorm*(Ideal.span {r}).absNorm := by
  rw [primaryCharacter_modulus,← Ideal.span_singleton_mul_span_singleton,map_mul]

end SevenEighths.CenteredMomentPrimaryCharacter

end

end OAI
end OAIOriginalModule1442

/-! Original module: OAI.NumberTheory.DirichletL.Moments.Primitive
Source SHA256: 195afc93f5452246997e970cb85d474dc2bbeb82bce6686ad34834b4d4a681b6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1443


namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentPrimitive
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier

def primitiveCharacter {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (j : ι → ℕ) :
    MulChar (Residue (finitePrimeModulus P)) ℂ :=
  crtCharacter ((Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
    (IdealGaussCRT.quotientProdEquivPi P hcop)) (fun i => actualSextic (P i) (hg i) ^ j i)

theorem primitiveCharacter_apply {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (j : ι → ℕ) (x : Residue (finitePrimeModulus P)) :
    primitiveCharacter P hcop hg j x =
      principalSexticRow P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P) x := rfl

@[simp] theorem primitiveCharacter_mk {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (j : ι → ℕ) (x : O) :
    primitiveCharacter P hcop hg j (Ideal.Quotient.mk _ x) =
      finiteSexticRow P hg j x := by
  exact (primitiveCharacter_apply P hcop hg j _).trans
    (principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P) x)

theorem primitive_gauss_transform {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6) (h : O) :
    residueGauss (finitePrimeModulus P) (finitePrimeModulus_ne_zero P)
      (primitiveCharacter P hcop hg j) (Ideal.Quotient.mk _ h) =
      star (finiteSexticRow P hg j h) * canonicalGaussSum P hcop hg j := by
  let r := finitePrimeModulus P
  let := finite_quotient_span (finitePrimeModulus_ne_zero P)
  let : Fintype (Residue r) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (span_finitePrimeModulus P)
  let : Fintype (O ⧸ ∏ i, P i) := Fintype.ofEquiv (Residue r) e.toEquiv
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  simp only [residueGauss, tsum_fintype, primitiveCharacter_apply]
  rw [canonical_principal_gauss_transform P hcop hg hchar j hj0 hj6
    (finitePrimeModulus P) (span_finitePrimeModulus P)]
  exact congrArg (fun z : ℂ => star z * canonicalGaussSum P hcop hg j)
    (principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P) h)

lemma sqrt_absNorm (r : O) :
    Real.sqrt (Ideal.absNorm (Ideal.span {r}) : ℝ) = ‖eisEmbedding r‖ := by
  rw [← eisEmbedding_norm_sq_eq_absNorm_span, Real.sqrt_sq (norm_nonneg _)]

theorem normalized_primitive_gauss_norm_le_one {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6) (h : O) :
    ‖normalizedResidueGauss (finitePrimeModulus P) (finitePrimeModulus_ne_zero P)
      (primitiveCharacter P hcop hg j) (Ideal.Quotient.mk _ h)‖ ≤ 1 := by
  rw [normalizedResidueGauss, primitive_gauss_transform P hcop hg hchar j hj0 hj6,
    sqrt_absNorm, mul_div_assoc]
  change ‖star (finiteSexticRow P hg j h) * canonicalNormalizedGauss P hcop hg j‖ ≤ 1
  rw [norm_mul, norm_star, norm_canonicalNormalizedGauss P hcop hg hchar j hj0 hj6, mul_one]
  exact QuadraticInitialBound.finiteSexticRow_norm_le_one P hg j h

end SevenEighths.CenteredMomentPrimitive
end

end OAI
end OAIOriginalModule1443

/-! Original module: OAI.NumberTheory.DirichletL.Moments.Bridge
Source SHA256: 89b80c801e704ca580c1456c367dc3514f15083b6dbde48333c36b32ff1256fb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1444



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentBridge
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentFirstPoisson

def productCharacter (a b : O) (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) :
    MulChar (Residue (a * b)) ℂ where
  toFun x := χa ((principalCRT a b hcop x).1) * χb ((principalCRT a b hcop x).2)
  map_one' := by simp
  map_mul' := by intro x y; simp [map_mul]; ring
  map_nonunit' := by
    intro x hx
    have hn : ¬IsUnit (principalCRT a b hcop x) := fun h =>
      hx ((isUnit_map_iff (principalCRT a b hcop) x).mp h)
    rw [Prod.isUnit_iff] at hn
    by_cases h : IsUnit (principalCRT a b hcop x).1
    · rw [χb.map_nonunit (fun hb => hn ⟨h, hb⟩), mul_zero]
    · rw [χa.map_nonunit h, zero_mul]

theorem productCharacter_apply (a b : O) (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (x : Residue (a * b)) :
    productCharacter a b hcop χa χb x =
      χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        χb (frequencyReduction b (a * b) (dvd_mul_left b a) x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [productCharacter, MulChar.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    principalCRT_mk, frequencyReduction_mk]

@[simp] theorem productCharacter_mk (a b : O) (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (x : O) :
    productCharacter a b hcop χa χb (Ideal.Quotient.mk _ x) =
      χa (Ideal.Quotient.mk _ x) * χb (Ideal.Quotient.mk _ x) := by
  rw [productCharacter_apply, frequencyReduction_mk, frequencyReduction_mk]

theorem productCharacter_gauss (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (h : Residue (a * b)) :
    residueGauss (a * b) (mul_ne_zero ha hb) (productCharacter a b hcop χa χb) h =
      χa (Ideal.Quotient.mk _ b) * χb (Ideal.Quotient.mk _ a) *
        residueGauss a ha χa (frequencyReduction a (a * b) (dvd_mul_right a b) h) *
        residueGauss b hb χb (frequencyReduction b (a * b) (dvd_mul_left b a) h) := by
  let := finite_quotient_span ha
  let := finite_quotient_span hb
  let := finite_quotient_span (mul_ne_zero ha hb)
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  simpa only [residueGauss, tsum_fintype, productCharacter_apply] using
    coprime_character_fourier a b ha hb hcop χa χb h

theorem triple_pair_gauss (r a b : O) (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrab : IsCoprime r (a * b)) (hab : IsCoprime a b)
    (ξ : MulChar (Residue r) ℂ) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (j : O) :
    residueGauss (r * (a * b)) (mul_ne_zero hr (mul_ne_zero ha hb))
      (productCharacter r (a * b) hrab ξ (productCharacter a b hab χa χb⁻¹))
      (Ideal.Quotient.mk _ j) =
      (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
        star (χb (Ideal.Quotient.mk _ (r * a)))) *
      (residueGauss r hr ξ (Ideal.Quotient.mk _ j) *
        residueGauss a ha χa (Ideal.Quotient.mk _ j) *
        star (residueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) := by
  let := finite_quotient_span hb
  rw [productCharacter_gauss r (a * b) hr (mul_ne_zero ha hb),
    frequencyReduction_mk, frequencyReduction_mk,
    productCharacter_mk, productCharacter_gauss a b ha hb, frequencyReduction_mk,
    frequencyReduction_mk, residueGauss_inverse, ← map_neg]
  simp only [map_mul, star_mul, MulChar.star_apply']
  ring

theorem triple_pair_poisson (r a b : O) (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrab : IsCoprime r (a * b)) (hab : IsCoprime a b)
    (ξ : MulChar (Residue r) ℂ) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O, (ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
      star (χb (Ideal.Quotient.mk _ z))) * W (‖eisEmbedding z‖ ^ 2 / K)) =
      ((K / ‖eisEmbedding (r * (a * b))‖ ^ 2 : ℝ) : ℂ) *
      (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
        star (χb (Ideal.Quotient.mk _ (r * a)))) *
      ∑' j : O, (residueGauss r hr ξ (Ideal.Quotient.mk _ j) *
        residueGauss a ha χa (Ideal.Quotient.mk _ j) *
        star (residueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) *
        paperRadialFourier W
          (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (r * (a * b))‖ ^ 2) := by
  let χ := productCharacter r (a * b) hrab ξ (productCharacter a b hab χa χb⁻¹)
  have hm : r * (a * b) ≠ 0 := mul_ne_zero hr (mul_ne_zero ha hb)
  let := finite_quotient_span hm
  let := finite_quotient_span hb
  let : Fintype (Residue (r * (a * b))) := Fintype.ofFinite _
  have hχ (z : O) : χ (Ideal.Quotient.mk _ z) =
      ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
        star (χb (Ideal.Quotient.mk _ z)) := by
    simp only [χ, productCharacter_mk, MulChar.star_apply', mul_assoc]
  have hp := actual_radial_paper_poisson_trace W K hK (r * (a * b)) hm χ
  change (∑' z : O, χ (Ideal.Quotient.mk _ z) * W (‖eisEmbedding z‖ ^ 2 / K)) =
    (K / ‖eisEmbedding (r * (a * b))‖ ^ 2 : ℝ) •
    ∑' j : O, (∑ x : Residue (r * (a * b)),
      χ x * quotientTrace (r * (a * b)) hm (Ideal.Quotient.mk _ j * x)) *
      paperRadialFourier W
        (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (r * (a * b))‖ ^ 2) at hp
  simp only [hχ] at hp
  rw [hp]
  have hcoeff (j : O) : (∑ x : Residue (r * (a * b)),
      χ x * quotientTrace (r * (a * b)) hm (Ideal.Quotient.mk _ j * x)) =
      residueGauss (r * (a * b)) hm χ (Ideal.Quotient.mk _ j) := by
    simp only [residueGauss, tsum_fintype]
  simp_rw [hcoeff]
  simp_rw [χ, triple_pair_gauss r a b hr ha hb hrab hab ξ χa χb]
  simp_rw [mul_assoc, tsum_mul_left]
  rw [Complex.real_smul]

theorem masked_triple_pair_poisson {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι)
    (r a b : O) (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrab : IsCoprime r (a * b)) (hab : IsCoprime a b)
    (ξ : MulChar (Residue r) ℂ) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O, rowCoprimeMask P S z *
      (ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
        star (χb (Ideal.Quotient.mk _ z))) * W (‖eisEmbedding z‖ ^ 2 / K)) =
      ∑ E ∈ S.powerset,
        let e := primeSubsetGenerator P E
        let Ke := K / ‖eisEmbedding e‖ ^ 2
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
        (ξ (Ideal.Quotient.mk _ e) * χa (Ideal.Quotient.mk _ e) *
          star (χb (Ideal.Quotient.mk _ e))) *
        ((Ke / ‖eisEmbedding (r * (a * b))‖ ^ 2 : ℝ) : ℂ) *
        (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
          star (χb (Ideal.Quotient.mk _ (r * a)))) *
        ∑' j : O, (residueGauss r hr ξ (Ideal.Quotient.mk _ j) *
          residueGauss a ha χa (Ideal.Quotient.mk _ j) *
          star (residueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) *
          paperRadialFourier W
            (Ke * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (r * (a * b))‖ ^ 2) := by
  let χ := productCharacter r (a * b) hrab ξ (productCharacter a b hab χa χb⁻¹)
  have hm : r * (a * b) ≠ 0 := mul_ne_zero hr (mul_ne_zero ha hb)
  let := finite_quotient_span hm
  let := finite_quotient_span hb
  let : Fintype (Residue (r * (a * b))) := Fintype.ofFinite _
  let row := fun z : O => ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
    star (χb (Ideal.Quotient.mk _ z))
  have hχ (z : O) : χ (Ideal.Quotient.mk _ z) = row z := by
    simp only [χ, row, productCharacter_mk, MulChar.star_apply', mul_assoc]
  have hsum : Summable (fun z : O => row z * W (‖eisEmbedding z‖ ^ 2 / K)) := by
    have hs := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
      (Ideal.Quotient.mk (Ideal.span {r * (a * b)})) χ
    simpa only [hχ, scaledRadialTest_apply] using hs
  have hmul (x y : O) : row (x * y) = row x * row y := by
    simp only [row, map_mul, star_mul]
    ring
  rw [tsum_masked_radial_dilations P hinj S row hmul W K hsum]
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only
  rw [triple_pair_poisson r a b hr ha hb hrab hab ξ χa χb W
    (K / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2)
    (primeSubset_reducedScale_pos P E hK)]
  ring

theorem normalized_triple_pair_poisson
    (r a b : O) (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrab : IsCoprime r (a * b)) (hab : IsCoprime a b)
    (ξ : MulChar (Residue r) ℂ) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O, (ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
      star (χb (Ideal.Quotient.mk _ z))) * W (‖eisEmbedding z‖ ^ 2 / K)) =
      ((K : ℂ) / ((Real.sqrt (Ideal.absNorm (Ideal.span {r}) : ℝ) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {a}) : ℝ) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {b}) : ℝ) : ℂ))) *
      (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
        star (χb (Ideal.Quotient.mk _ (r * a)))) *
      ∑' j : O, (normalizedResidueGauss r hr ξ (Ideal.Quotient.mk _ j) *
        normalizedResidueGauss a ha χa (Ideal.Quotient.mk _ j) *
        star (normalizedResidueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) *
        paperRadialFourier W
          (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (r * (a * b))‖ ^ 2) := by
  have hnr : (‖eisEmbedding r‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hr))
  have hna : (‖eisEmbedding a‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero ha))
  have hnb : (‖eisEmbedding b‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hb))
  have hpoint (j : O) : residueGauss r hr ξ (Ideal.Quotient.mk _ j) *
      residueGauss a ha χa (Ideal.Quotient.mk _ j) *
      star (residueGauss b hb χb (Ideal.Quotient.mk _ (-j))) =
      ((‖eisEmbedding r‖ : ℂ) * (‖eisEmbedding a‖ : ℂ) * (‖eisEmbedding b‖ : ℂ)) *
      (normalizedResidueGauss r hr ξ (Ideal.Quotient.mk _ j) *
        normalizedResidueGauss a ha χa (Ideal.Quotient.mk _ j) *
        star (normalizedResidueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) := by
    simp only [normalizedResidueGauss, CenteredMomentPrimitive.sqrt_absNorm,
      star_div₀, Complex.star_def, Complex.conj_ofReal]
    field_simp
  rw [triple_pair_poisson r a b hr ha hb hrab hab ξ χa χb W K hK]
  simp_rw [hpoint, mul_assoc, tsum_mul_left, CenteredMomentPrimitive.sqrt_absNorm]
  simp only [map_mul, norm_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_mul]
  field_simp

end SevenEighths.CenteredMomentBridge
end

end OAI
end OAIOriginalModule1444

/-! Original module: OAI.NumberTheory.DirichletL.Moments.Initial
Source SHA256: 177e295031bce4d28c87389435315cbfc2ef0ffad4b25ddaf7aa9f20189f1be8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1445


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentInitial
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentSupportedCorrelation
open CenteredMomentPrimitive CenteredMomentBridge

variable {ι : Type*}

abbrev activeModulus (P : ι → Ideal O) (B : Finset ι) (c d : ι → ℕ) : O :=
  finitePrimeModulus (fun i : CenteredMomentActive.activeSupport B c d => P i.val)

def commonCharacter (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, goodLambda ∉ P i)
    (B : Finset ι) (c d : ι → ℕ) : MulChar (Residue (activeModulus P B c d)) ℂ :=
  primitiveCharacter (fun i : CenteredMomentActive.activeSupport B c d => P i.val)
    (CenteredMomentActive.activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
    (fun i => CenteredMomentActive.netExponent (c i.val) (d i.val))

theorem activeModulus_ne_zero (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (B : Finset ι) (c d : ι → ℕ) : activeModulus P B c d ≠ 0 :=
  finitePrimeModulus_ne_zero _

theorem activeModulus_coprime (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (B : Finset ι) (c d : ι → ℕ) (v : O)
    (hcop : ∀ i ∈ B, IsCoprime (P i) (Ideal.span {v})) :
    IsCoprime (activeModulus P B c d) v := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [activeModulus, span_finitePrimeModulus]
  apply IsCoprime.prod_left
  intro i _
  exact hcop i.val (Finset.mem_filter.mp i.property).1

theorem allocated_pair_factor (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, goodLambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (B : Finset ι) (c d : ι → ℕ)
    (hc : ∀ i ∈ B, c i ≠ 0) (hd : ∀ i ∈ B, d i ≠ 0)
    (a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) (z : O) :
    idealRowHom z ((∏ i ∈ B, P i ^ c i) * Ideal.span {a}) *
      star (idealRowHom z ((∏ i ∈ B, P i ^ d i) * Ideal.span {b})) =
      rowCoprimeMask P (CenteredMomentActive.principalSupport B c d) z *
      (commonCharacter P hinj hg B c d (Ideal.Quotient.mk _ z) *
        supportedModulusCharacter a ha (Ideal.Quotient.mk _ z) *
        star (supportedModulusCharacter b hb (Ideal.Quotient.mk _ z))) := by
  calc
    _ = (idealRowHom z (∏ i ∈ B, P i ^ c i) *
        star (idealRowHom z (∏ i ∈ B, P i ^ d i))) *
        (idealRowHom z (Ideal.span {a}) * star (idealRowHom z (Ideal.span {b}))) := by
      rw [map_mul, map_mul, star_mul]
      ring
    _ = _ := by
      rw [CenteredMomentActive.common_ideal_pair_active P hg hchar B c d hc hd]
      simp only [commonCharacter, primitiveCharacter_mk, supportedModulusCharacter_mk]
      ring

theorem allocated_pair_poisson {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, goodLambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (B : Finset ι) (c d : ι → ℕ)
    (hc : ∀ i ∈ B, c i ≠ 0) (hd : ∀ i ∈ B, d i ≠ 0)
    (a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hcop : ∀ i ∈ B, IsCoprime (P i) (Ideal.span {a * b})) (hab : IsCoprime a b)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    let r := activeModulus P B c d
    let ξ := commonCharacter P hinj hg B c d
    let χa := supportedModulusCharacter a ha
    let χb := supportedModulusCharacter b hb
    (∑' z : O, (idealRowHom z ((∏ i ∈ B, P i ^ c i) * Ideal.span {a}) *
      star (idealRowHom z ((∏ i ∈ B, P i ^ d i) * Ideal.span {b}))) *
      W (‖eisEmbedding z‖ ^ 2 / K)) =
      ∑ E ∈ (CenteredMomentActive.principalSupport B c d).powerset,
        let e := primeSubsetGenerator P E
        let Ke := K / ‖eisEmbedding e‖ ^ 2
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
        (ξ (Ideal.Quotient.mk _ e) * χa (Ideal.Quotient.mk _ e) *
          star (χb (Ideal.Quotient.mk _ e))) *
        ((Ke / ‖eisEmbedding (r * (a * b))‖ ^ 2 : ℝ) : ℂ) *
        (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
          star (χb (Ideal.Quotient.mk _ (r * a)))) *
        ∑' j : O, (residueGauss r (activeModulus_ne_zero P B c d) ξ (Ideal.Quotient.mk _ j) *
          residueGauss a (supported_element_ne_zero a ha) χa (Ideal.Quotient.mk _ j) *
          star (residueGauss b (supported_element_ne_zero b hb) χb (Ideal.Quotient.mk _ (-j)))) *
          paperRadialFourier W
            (Ke * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (r * (a * b))‖ ^ 2) := by
  simp_rw [allocated_pair_factor P hinj hg hchar B c d hc hd a b ha hb]
  exact masked_triple_pair_poisson P hinj (CenteredMomentActive.principalSupport B c d)
    (activeModulus P B c d) a b (activeModulus_ne_zero P B c d)
    (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
    (activeModulus_coprime P B c d (a * b) hcop) hab
    (commonCharacter P hinj hg B c d) (supportedModulusCharacter a ha)
    (supportedModulusCharacter b hb) W K hK

theorem common_gauss_norm_le_one (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, goodLambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (B : Finset ι) (c d : ι → ℕ) (h : O) :
    ‖normalizedResidueGauss (activeModulus P B c d) (activeModulus_ne_zero P B c d)
      (commonCharacter P hinj hg B c d) (Ideal.Quotient.mk _ h)‖ ≤ 1 :=
  normalized_primitive_gauss_norm_le_one
    (fun i : CenteredMomentActive.activeSupport B c d => P i.val)
    (CenteredMomentActive.activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
    (fun i => hchar i.val) (fun i => CenteredMomentActive.netExponent (c i.val) (d i.val))
    (CenteredMomentActive.netExponent_ne_zero B c d)
    (fun _i => CenteredMomentActive.netExponent_lt_six _ _) h

end SevenEighths.CenteredMomentInitial
end

end OAI
end OAIOriginalModule1445

/-! Original module: OAI.NumberTheory.DirichletL.Moments.Rankin
Source SHA256: ca3d37208cc7d7e9586e814398a8853ef92645f77eea0436f42567d26bbc50a9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1446


namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter
namespace SevenEighths.CenteredMomentRankin
open IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

def primeMass (P : Ideal O) (δ : ℝ) : ℝ := ((Ideal.absNorm P:ℝ)^δ-1)⁻¹

theorem prime_norm_ge_two (P : Ideal O) (hp : Prime P) : 2 ≤ Ideal.absNorm P := by
  have h0 := Ideal.absNorm_eq_zero_iff.not.mpr hp.ne_zero
  have h1 : Ideal.absNorm P ≠ 1 := by
    intro hn
    exact hp.not_isUnit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp hn))
  omega

theorem primeMass_nonneg (P : Ideal O) (hp : Prime P) (δ : ℝ) (hδ : 0 < δ) :
    0 ≤ primeMass P δ := by
  apply inv_nonneg.mpr
  have hn : (1:ℝ) < Ideal.absNorm P := by exact_mod_cast (prime_norm_ge_two P hp)
  exact (sub_pos.mpr (Real.one_lt_rpow hn hδ)).le

theorem primeMass_le_fixed (P : Ideal O) (hp : Prime P) (δ : ℝ) (hδ : 0 < δ) :
    primeMass P δ ≤ ((2:ℝ)^δ-1)⁻¹ := by
  apply inv_anti₀ (sub_pos.mpr (Real.one_lt_rpow (by norm_num) hδ))
  exact sub_le_sub_right (Real.rpow_le_rpow (by norm_num)
    (by exact_mod_cast prime_norm_ge_two P hp) hδ.le) 1

theorem uniform_primeMass_product (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : Finset (Ideal O), (∀ P ∈ S,Prime P) →
      (∏ P ∈ S,primeMass P δ) ≤ C := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)^δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2:ℝ)))
  let small : Finset (Ideal O) := (Ideal.finite_setOfPred_absNorm_le (S := O) N).toFinset
  let B : ℝ := max 1 (((2:ℝ)^δ-1)⁻¹)
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨B^small.card,pow_pos (zero_lt_one.trans_le hB) _,?_⟩
  intro S hp
  have hs (P : Ideal O) (hP : P ∈ S∩small) : primeMass P δ ≤ B :=
    (primeMass_le_fixed P (hp P (Finset.mem_inter.mp hP).1) δ hδ).trans (le_max_right _ _)
  have hl (P : Ideal O) (hP : P ∈ S\small) : primeMass P δ ≤ 1 := by
    have hn : N < Ideal.absNorm P := by
      by_contra hn
      apply (Finset.mem_sdiff.mp hP).2
      simpa only [small,Set.Finite.mem_toFinset,Set.mem_ofPred_eq] using le_of_not_gt hn
    have hpow := hN (Ideal.absNorm P) hn.le
    apply inv_le_one_of_one_le₀
    linarith
  have he : S=(S∩small)∪(S\small) := by
    ext P
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  have hdis : Disjoint (S∩small) (S\small) := Finset.disjoint_left.mpr
    (fun P hP hQ => (Finset.mem_sdiff.mp hQ).2 (Finset.mem_inter.mp hP).2)
  rw [he,Finset.prod_union hdis]
  have hleft : (∏ P ∈ S∩small,primeMass P δ) ≤ B^small.card := by
    calc
      _ ≤ ∏ _P ∈ S∩small,B := Finset.prod_le_prod₀
        (fun P hP => primeMass_nonneg P (hp P (Finset.mem_inter.mp hP).1) δ hδ) hs
      _ = B^(S∩small).card := by simp
      _ ≤ _ := pow_le_pow_right₀ hB (Finset.card_le_card Finset.inter_subset_right)
  have hright : (∏ P ∈ S\small,primeMass P δ) ≤ 1 :=
    Finset.prod_le_one₀ (fun P hP => primeMass_nonneg P (hp P (Finset.mem_sdiff.mp hP).1) δ hδ) hl
  exact (mul_le_mul hleft hright (Finset.prod_nonneg
    (fun P hP => primeMass_nonneg P (hp P (Finset.mem_sdiff.mp hP).1) δ hδ)) (by positivity)).trans_eq (mul_one _)

theorem local_power_sum (P : Ideal O) (hp : Prime P) (δ : ℝ) (hδ : 0 < δ) (K : ℕ) :
    (∑ n ∈ Finset.range K,((Ideal.absNorm P:ℝ)^(n+1))^(-δ)) ≤ primeMass P δ := by
  let q : ℝ := (Ideal.absNorm P:ℝ)^δ
  have hNP : (1:ℝ)<Ideal.absNorm P := by exact_mod_cast prime_norm_ge_two P hp
  have hq : 1 < q := Real.one_lt_rpow hNP hδ
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hr0 : 0 ≤ q⁻¹ := inv_nonneg.mpr hq0.le
  have hr1 : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have hsum := ((hasSum_geometric_of_lt_one hr0 hr1).mul_left q⁻¹).summable.sum_le_tsum
    (Finset.range K) (fun n _ => mul_nonneg hr0 (pow_nonneg hr0 n))
  rw [((hasSum_geometric_of_lt_one hr0 hr1).mul_left q⁻¹).tsum_eq] at hsum
  have he (n : ℕ) : ((Ideal.absNorm P:ℝ)^(n+1))^(-δ)=q⁻¹*(q⁻¹)^n := by
    rw [← Real.rpow_natCast_mul (by linarith : (0:ℝ)≤Ideal.absNorm P),mul_comm,
      Real.rpow_mul_natCast (by linarith : (0:ℝ)≤Ideal.absNorm P),Real.rpow_neg (by linarith),pow_succ]
    dsimp only [q]
    ring
  simp_rw [he]
  apply hsum.trans_eq
  change q⁻¹*(1-q⁻¹)⁻¹=(q-1)⁻¹
  field_simp

end SevenEighths.CenteredMomentRankin

end

end OAI
end OAIOriginalModule1446

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RankinCount
Source SHA256: 9855ba9a713837837fd3a4ade1e7734b0478f3189448375fc48a6e12738e5283
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1447


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRankinCount
open IdealMobiusDivisorSum UniqueFactorizationMonoid CenteredMomentRankin
local notation "O" => ActualEisensteinCubic.O

def powerCode (R : Finset (Ideal O)) (I : Ideal O) (P : R) : ℕ :=
  (normalizedFactors I).count (P:Ideal O)-1

theorem powerCode_reconstruct (R : Finset (Ideal O)) (I : Ideal O) (hI : I ≠ 0)
    (hR : primeSupport I=R) :
    I=∏ P : R,(P:Ideal O)^(powerCode R I P+1) := by
  have he (P : R) : powerCode R I P+1=(normalizedFactors I).count (P:Ideal O) := by
    have hp : (P:Ideal O) ∈ primeSupport I := hR ▸ P.property
    have hc := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hp)
    dsimp only [powerCode]
    omega
  simp_rw [he]
  calc
    I=(normalizedFactors I).prod := (Ideal.prod_normalizedFactors_eq_self hI).symm
    _=∏ P ∈ (normalizedFactors I).toFinset,P^(normalizedFactors I).count P := Finset.prod_multiset_count _
    _=∏ P : R,(P:Ideal O)^(normalizedFactors I).count (P:Ideal O) := by
      rw [Finset.prod_coe_sort R (fun P : Ideal O => P^(normalizedFactors I).count P)]
      change _=∏ P ∈ R,P^(normalizedFactors I).count P
      rw [← hR]
      rfl

theorem powerCode_injOn (R : Finset (Ideal O)) (S : Finset (Ideal O))
    (hS : ∀ I ∈ S,I ≠ 0) (hR : ∀ I ∈ S,primeSupport I=R) :
    Set.InjOn (powerCode R) S := by
  intro I hI J hJ he
  rw [powerCode_reconstruct R I (hS I hI) (hR I hI),powerCode_reconstruct R J (hS J hJ) (hR J hJ),he]

theorem ideal_mass_eq (R : Finset (Ideal O)) (I : Ideal O) (hI : I ≠ 0)
    (hR : primeSupport I=R) (δ : ℝ) :
    (Ideal.absNorm I:ℝ)^(-δ)=
      ∏ P : R,((Ideal.absNorm (P:Ideal O):ℝ)^(powerCode R I P+1))^(-δ) := by
  have he := congrArg (fun J : Ideal O => (Ideal.absNorm J:ℝ)^(-δ))
    (powerCode_reconstruct R I hI hR)
  simp only [map_prod,map_pow,Nat.cast_prod,Nat.cast_pow] at he
  rw [he]
  exact (Real.finsetProd_rpow _ _ (fun _ _ => pow_nonneg (Nat.cast_nonneg _) _) _).symm

theorem fixed_support_mass (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R S : Finset (Ideal O)),
      (∀ P ∈ R,Prime P) → (∀ I ∈ S,I ≠ 0) → (∀ I ∈ S,primeSupport I=R) →
      (∑ I ∈ S,(Ideal.absNorm I:ℝ)^(-δ)) ≤ C := by
  obtain ⟨C,hC,hprod⟩ := uniform_primeMass_product δ hδ
  refine ⟨C,hC,?_⟩
  intro R S hR hS hsupport
  let K : ℕ := S.sup (fun I => Finset.univ.sup (powerCode R I))+1
  let mass : (R → ℕ) → ℝ := fun v => ∏ P : R,((Ideal.absNorm (P:Ideal O):ℝ)^(v P+1))^(-δ)
  have hm (v : R → ℕ) : 0 ≤ mass v := Finset.prod_nonneg
    (fun _ _ => Real.rpow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _)
  have hsub : S.image (powerCode R) ⊆ Fintype.piFinset (fun _P : R => Finset.range K) := by
    intro v hv
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hv
    apply Fintype.mem_piFinset.mpr
    intro P
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le ((Finset.le_sup (f := powerCode R I) (Finset.mem_univ P)).trans
      (Finset.le_sup (f := fun I => Finset.univ.sup (powerCode R I)) hI))
  calc
    _ = ∑ v ∈ S.image (powerCode R),mass v := by
      rw [Finset.sum_image (powerCode_injOn R S hS hsupport)]
      apply Finset.sum_congr rfl
      intro I hI
      exact ideal_mass_eq R I (hS I hI) (hsupport I hI) δ
    _ ≤ ∑ v ∈ Fintype.piFinset (fun _P : R => Finset.range K),mass v :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => hm v)
    _ = ∏ P : R,∑ n ∈ Finset.range K,((Ideal.absNorm (P:Ideal O):ℝ)^(n+1))^(-δ) := by
      exact (Finset.prod_univ_sum (fun _P : R => Finset.range K)
        (fun P n => ((Ideal.absNorm (P:Ideal O):ℝ)^(n+1))^(-δ))).symm
    _ ≤ ∏ P : R,primeMass P δ := Finset.prod_le_prod₀
      (fun _ _ => Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _))
      (fun P _ => local_power_sum P (hR P P.property) δ hδ K)
    _ ≤ C := by
      have he := Finset.prod_coe_sort R (fun P => primeMass P δ)
      rw [he]
      exact hprod R hR

theorem fixed_support_count (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R S : Finset (Ideal O)),
      (∀ P ∈ R,Prime P) → (∀ I ∈ S,I ≠ 0) → (∀ I ∈ S,primeSupport I=R) →
      ∀ X : ℝ,0 < X → (∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ X) →
      (S.card:ℝ) ≤ C*X^δ := by
  obtain ⟨C,hC,hmass⟩ := fixed_support_mass δ hδ
  refine ⟨C,hC,?_⟩
  intro R S hR hS hs X hX hN
  have hterm (I : Ideal O) (hI : I ∈ S) : (1:ℝ) ≤ X^δ*(Ideal.absNorm I:ℝ)^(-δ) := by
    have hn : (0:ℝ)<Ideal.absNorm I := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hI))
    have hr := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hn.le (hN I hI) hδ.le)
      (Real.rpow_nonneg hn.le (-δ))
    simpa only [← Real.rpow_add hn,add_neg_cancel,Real.rpow_zero] using hr
  calc
    _ = ∑ _I ∈ S,(1:ℝ) := by simp
    _ ≤ ∑ I ∈ S,X^δ*(Ideal.absNorm I:ℝ)^(-δ) := Finset.sum_le_sum (fun I hI => hterm I hI)
    _ = X^δ*∑ I ∈ S,(Ideal.absNorm I:ℝ)^(-δ) := (Finset.mul_sum _ _ _).symm
    _ ≤ X^δ*C := mul_le_mul_of_nonneg_left (hmass R S hR hS hs) (Real.rpow_nonneg hX.le _)
    _ = _ := mul_comm _ _

end SevenEighths.CenteredMomentRankinCount

end

end OAI
end OAIOriginalModule1447

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RankinSubset
Source SHA256: c52925938d308c998a23172e8d1400250be5b57d79b33ba4d623b84bed8a0383
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1448


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRankinSubset
open IdealMobiusDivisorSum CenteredMomentRankinCount
local notation "O" => ActualEisensteinCubic.O

theorem supported_power_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (Q : Ideal O),Q ≠ 0 → ∀ S : Finset (Ideal O),
      (∀ I ∈ S,I ≠ 0) → (∀ I ∈ S,primeSupport I ⊆ primeSupport Q) →
      ∀ X : ℝ,0 < X → (∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ X) →
      (S.card:ℝ) ≤ C*X^a*(Ideal.absNorm Q:ℝ)^ε := by
  obtain ⟨C,hC,hcount⟩ := fixed_support_count a ha
  obtain ⟨D,hD,hsub⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro Q hQ S hS hs X hX hN
  have hf : ∀ I ∈ S,primeSupport I ∈ (primeSupport Q).powerset :=
    fun I hI => Finset.mem_powerset.mpr (hs I hI)
  have he := Finset.card_eq_sum_card_fiberwise hf
  have hfiber (R : Finset (Ideal O)) (hR : R ∈ (primeSupport Q).powerset) :
      ((S.filter (fun I => primeSupport I=R)).card:ℝ) ≤ C*X^a := by
    apply hcount R _ (fun P hP => support_prime ((Finset.mem_powerset.mp hR) hP))
      (fun I hI => hS I (Finset.mem_filter.mp hI).1)
      (fun I hI => (Finset.mem_filter.mp hI).2) X hX
      (fun I hI => hN I (Finset.mem_filter.mp hI).1)
  calc
    _ = ∑ R ∈ (primeSupport Q).powerset,((S.filter (fun I => primeSupport I=R)).card:ℝ) := by
      exact_mod_cast he
    _ ≤ ∑ _R ∈ (primeSupport Q).powerset,C*X^a := Finset.sum_le_sum hfiber
    _ = (2:ℝ)^(primeSupport Q).card*(C*X^a) := by simp
    _ ≤ (D*(Ideal.absNorm Q:ℝ)^ε)*(C*X^a) :=
      mul_le_mul_of_nonneg_right (hsub Q hQ) (mul_nonneg hC.le (Real.rpow_nonneg hX.le _))
    _ = _ := by ring

theorem supported_power_pair_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (Q : Ideal O),Q ≠ 0 → ∀ S : Finset (Ideal O × Ideal O),
      (∀ v ∈ S,v.1 ≠ 0 ∧ v.2 ≠ 0) →
      (∀ v ∈ S,primeSupport v.1 ⊆ primeSupport Q ∧ primeSupport v.2 ⊆ primeSupport Q) →
      ∀ X Y : ℝ,0 < X → 0 < Y →
      (∀ v ∈ S,(Ideal.absNorm v.1:ℝ) ≤ X ∧ (Ideal.absNorm v.2:ℝ) ≤ Y) →
      (S.card:ℝ) ≤ C*X^a*Y^a*(Ideal.absNorm Q:ℝ)^ε := by
  obtain ⟨C,hC,hcount⟩ := supported_power_count a (ε/2) ha (by positivity)
  refine ⟨C^2,pow_pos hC _,?_⟩
  intro Q hQ S hS hs X Y hX hY hN
  have hfst : ((S.image Prod.fst).card:ℝ) ≤ C*X^a*(Ideal.absNorm Q:ℝ)^(ε/2) := by
    refine hcount Q hQ _ ?_ ?_ X hX ?_
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hS v hv).1
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hs v hv).1
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hN v hv).1
  have hsnd : ((S.image Prod.snd).card:ℝ) ≤ C*Y^a*(Ideal.absNorm Q:ℝ)^(ε/2) := by
    refine hcount Q hQ _ ?_ ?_ Y hY ?_
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hS v hv).2
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hs v hv).2
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hN v hv).2
  have hin : S ⊆ (S.image Prod.fst) ×ˢ (S.image Prod.snd) := by
    intro v hv
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hv,Finset.mem_image_of_mem _ hv⟩
  have hn : (0:ℝ) < Ideal.absNorm Q := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hQ)
  calc
    _ ≤ ((S.image Prod.fst).card:ℝ)*((S.image Prod.snd).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hin).trans_eq (Finset.card_product _ _)
    _ ≤ (C*X^a*(Ideal.absNorm Q:ℝ)^(ε/2))*(C*Y^a*(Ideal.absNorm Q:ℝ)^(ε/2)) :=
      mul_le_mul hfst hsnd (Nat.cast_nonneg _) (by positivity)
    _ = C^2*X^a*Y^a*((Ideal.absNorm Q:ℝ)^(ε/2)*(Ideal.absNorm Q:ℝ)^(ε/2)) := by ring
    _ = _ := by rw [← Real.rpow_add hn]; congr 2; ring

end SevenEighths.CenteredMomentRankinSubset

end

end OAI
end OAIOriginalModule1448

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RetainedProfile
Source SHA256: da6726e7032ec19f14a58902119d9e219b7d1a7e0f1687b63b0fc43543fb6ebd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1449



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentRetainedProfile
open CenteredMomentLattice CenteredMomentTwist CenteredMomentHeckeTwist
open CenteredMomentHeckeHeight CenteredMomentHeckeVolume CenteredMomentHeckeCancellation HeckeFamily
open EisensteinSchwartzPoisson QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O

def dilated (W : ℝ → ℂ) (c : ℝ) : ℝ → ℂ := fun x => W (c * x)

theorem dilated_contDiff (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (c : ℝ) :
    ContDiff ℝ ∞ (dilated W c) :=
  hW.comp (contDiff_const.mul contDiff_id)

theorem dilated_support (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) :
    Function.support (dilated W c) ⊆ Set.Icc (a / B) b := by
  intro x hx
  have hv := hs hx
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hx0 : 0 < x := (mul_pos_iff.mp (lt_of_lt_of_le ha hv.1)).resolve_right
    (by intro h; linarith [h.1]) |>.2
  constructor
  · apply (div_le_iff₀ hB0).mpr
    exact hv.1.trans (by nlinarith)
  · exact (show x ≤ c * x by nlinarith).trans hv.2

theorem seminorm_dilation_le (f g : 𝓢(ℝ, ℂ)) (ζ : ℂ) (c B : ℝ)
    (hζ : ‖ζ‖ = 1) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hg : ∀ x, g x = ζ * f (c * x)) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n g ≤ B ^ n * SchwartzMap.seminorm ℝ k n f := by
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hB0 : 0 ≤ B := hc0.trans hcB
  have he : (g : ℝ → ℂ) = fun x => ζ * f (c * x) := funext hg
  apply SchwartzMap.seminorm_le_bound' ℝ k n g (by positivity)
  intro x
  rw [he, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_smul (f.smooth n), norm_mul, hζ,
    one_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hc0 n)]
  have hx : |x| ^ k ≤ |c * x| ^ k := by
    apply pow_le_pow_left₀ (abs_nonneg x)
    rw [abs_mul, abs_of_nonneg hc0]
    nlinarith [abs_nonneg x]
  calc
    _ = c ^ n * (|x| ^ k * ‖iteratedDeriv n f (c * x)‖) := by ring
    _ ≤ c ^ n * (|c * x| ^ k * ‖iteratedDeriv n f (c * x)‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hx (norm_nonneg _)) (pow_nonneg hc0 n)
    _ ≤ c ^ n * SchwartzMap.seminorm ℝ k n f :=
      mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm' ℝ k n f (c * x))
        (pow_nonneg hc0 n)
    _ ≤ B ^ n * SchwartzMap.seminorm ℝ k n f :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc0 hcB _) (apply_nonneg _ _)

theorem normPowerProfile_dilated (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (t x : ℝ) :
    normPowerProfile (dilated W c) (a / B) b
      (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
      (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t x =
      ((c : ℂ) ^ (Complex.I * t))⁻¹ *
        normPowerProfile W a b ha hs hW t (c * x) := by
  rw [normPowerProfile_apply, normPowerProfile_apply]
  by_cases hz : W (c * x) = 0
  · simp [dilated, hz]
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hx : 0 < x := (mul_pos_iff.mp (lt_of_lt_of_le ha (hs hz).1)).resolve_right
    (by intro h; linarith [h.1]) |>.2
  have hp := Complex.mul_cpow_ofReal_nonneg hc0.le hx.le (Complex.I * t)
  rw [← Complex.ofReal_mul] at hp
  rw [hp]
  have hn : (c : ℂ) ^ (Complex.I * t) ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [norm_real_imaginary_power c t hc0]; norm_num)
  dsimp only [dilated]
  simp only [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem normPowerProfile_dilated_seminorm (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t : ℝ) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n
      (normPowerProfile (dilated W c) (a / B) b
        (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
        (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t) ≤
      B ^ n * SchwartzMap.seminorm ℝ k n (normPowerProfile W a b ha hs hW t) := by
  apply seminorm_dilation_le _ _ ((c : ℂ) ^ (Complex.I * t))⁻¹ c B
    (by rw [norm_inv, norm_real_imaginary_power c t (lt_of_lt_of_le zero_lt_one hc), inv_one])
    hc hcB
  intro x
  exact normPowerProfile_dilated W a b B c ha hB hc hcB hs hW t x

theorem normPowerProfile_dilated_finite (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t : ℝ) (F : Finset (ℕ × ℕ)) :
    F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (normPowerProfile (dilated W c) (a / B) b
        (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
        (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t) ≤
      B ^ (F.sup Prod.snd) *
        F.sup (schwartzSeminormFamily ℝ ℝ ℂ) (normPowerProfile W a b ha hs hW t) := by
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  apply (normPowerProfile_dilated_seminorm W a b B c ha hB hc hcB hs hW t z.1 z.2).trans
  exact mul_le_mul (pow_le_pow_right₀ hB (Finset.le_sup hz))
    (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ ℝ ℂ) hz) (apply_nonneg _ _) (by positivity)

theorem dilated_normPowerProfile_uniform_degree (a b B : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (F : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧
      ∀ c : ℝ, ∀ hc : 1 ≤ c, ∀ hcB : c ≤ B, ∀ t : ℝ,
      F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (normPowerProfile (dilated W c) (a / B) b
          (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
          (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t) ≤
        C * (1 + ‖t‖) ^ J := by
  obtain ⟨J, hJ⟩ := normPowerProfile_uniform_degree a b ha F
  refine ⟨J, ?_⟩
  intro W hs hW
  obtain ⟨C, hC, hbound⟩ := hJ W hs hW
  refine ⟨B ^ (F.sup Prod.snd) * C, mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one hB) _) hC, ?_⟩
  intro c hc hcB t
  have ht : (1 + ‖t / (2 * Real.pi)‖) ^ J ≤ (1 + ‖t‖) ^ J := by
    gcongr
    exact CenteredMomentHeight.normalized_height_le t
  calc
    _ ≤ B ^ (F.sup Prod.snd) *
        F.sup (schwartzSeminormFamily ℝ ℝ ℂ) (normPowerProfile W a b ha hs hW t) :=
      normPowerProfile_dilated_finite W a b B c ha hB hc hcB hs hW t F
    _ ≤ B ^ (F.sup Prod.snd) * (C * (1 + ‖t‖) ^ J) :=
      mul_le_mul_of_nonneg_left
        ((hbound t).trans (mul_le_mul_of_nonneg_left ht hC.le)) (by positivity)
    _ = _ := by ring

def clippedScale (S : ℝ) : ℝ := max 1 S

def clipDilation (S : ℝ) : ℝ := clippedScale S / S

theorem clippedScale_ge_one (S : ℝ) : 1 ≤ clippedScale S := le_max_left _ _

theorem clipDilation_ge_one (S : ℝ) (hS : 0 < S) : 1 ≤ clipDilation S := by
  rw [clipDilation, le_div_iff₀ hS, one_mul]
  exact le_max_right _ _

theorem clipDilation_le (b S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) :
    clipDilation S ≤ max 1 b := by
  rw [clipDilation, div_le_iff₀ hS]
  apply max_le
  · exact hret.trans (by nlinarith [le_max_right (1 : ℝ) b])
  · nlinarith [le_max_left (1 : ℝ) b]

theorem clipDilation_eq_one (S : ℝ) (hS : 1 ≤ S) : clipDilation S = 1 := by
  simp [clipDilation, clippedScale, max_eq_right hS, ne_of_gt (lt_of_lt_of_le zero_lt_one hS)]

theorem clipDilation_subunit (S : ℝ) (hS : S ≤ 1) :
    clipDilation S = 1 / S := by simp [clipDilation, clippedScale, max_eq_left hS]

theorem clipped_source (W : ℝ → ℂ) (S x : ℝ) (hS : 0 < S) :
    dilated W (clipDilation S) (x / clippedScale S) = W (x / S) := by
  have hclip : clippedScale S ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (clippedScale_ge_one S))
  unfold dilated clipDilation
  congr 1
  field_simp

theorem strict_subunit_ideal_zero (W : ℝ → ℂ) (b S : ℝ) (hS : 0 < S)
    (hs : Function.support W ⊆ Set.Iic b) (hstrict : S * b < 1)
    (I : Ideal O) (hI : I ≠ 0) : W ((Ideal.absNorm I : ℝ) / S) = 0 := by
  by_contra h
  have hn : 1 ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hu := (div_le_iff₀ hS).mp (hs h)
  nlinarith

theorem strict_subunit_sum_zero (A : Ideal O → ℂ) (hA : A 0 = 0)
    (W : ℝ → ℂ) (b S : ℝ) (hS : 0 < S)
    (hs : Function.support W ⊆ Set.Iic b) (hstrict : S * b < 1) :
    (∑' I : Ideal O, A I * W ((Ideal.absNorm I : ℝ) / S)) = 0 := by
  calc
    _ = ∑' _I : Ideal O, (0 : ℂ) := by
      apply tsum_congr
      intro I
      by_cases hI : I = 0
      · rw [hI, hA, zero_mul]
      · rw [strict_subunit_ideal_zero W b S hS hs hstrict I hI, mul_zero]
    _ = 0 := tsum_zero

theorem clipped_ideal_sum (A : Ideal O → ℂ) (W : ℝ → ℂ) (S : ℝ) (hS : 0 < S) :
    (∑' I : Ideal O, A I * W ((Ideal.absNorm I : ℝ) / S)) =
      ∑' I : Ideal O, A I * dilated W (clipDilation S)
        ((Ideal.absNorm I : ℝ) / clippedScale S) := by
  apply tsum_congr
  intro I
  rw [clipped_source W S _ hS]

theorem clipped_twistedIdealSum (χ : Character) (W : ℝ → ℂ) (t S : ℝ) (hS : 0 < S) :
    twistedIdealSum χ W t S =
      twistedIdealSum χ (dilated W (clipDilation S)) t (clippedScale S) :=
  clipped_ideal_sum _ W S hS

theorem strict_subunit_twistedIdealSum_zero (χ : Character) (W : ℝ → ℂ)
    (b t S : ℝ) (hS : 0 < S) (hs : Function.support W ⊆ Set.Iic b)
    (hstrict : S * b < 1) : twistedIdealSum χ W t S = 0 := by
  apply strict_subunit_sum_zero _ _ W b S hS hs hstrict
  simp only [map_zero, zero_mul]

theorem clipped_rowTwistedSum (η : Character) (m A₀ z : O)
    (W : ℝ → ℂ) (t S : ℝ) (hS : 0 < S) :
    rowTwistedSum η m A₀ z W t S =
      rowTwistedSum η m A₀ z (dilated W (clipDilation S)) t (clippedScale S) :=
  clipped_ideal_sum _ W S hS

theorem strict_subunit_rowTwistedSum_zero (η : Character) (m A₀ z : O)
    (W : ℝ → ℂ) (b t S : ℝ) (hS : 0 < S) (hs : Function.support W ⊆ Set.Iic b)
    (hstrict : S * b < 1) : rowTwistedSum η m A₀ z W t S = 0 := by
  apply strict_subunit_sum_zero _ _ W b S hS hs hstrict
  simp only [map_zero, zero_mul]

def retainedProfile (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) (t : ℝ) : 𝓢(ℝ, ℂ) :=
  normPowerProfile (dilated W (clipDilation S)) (a / max 1 b) b
    (div_pos ha (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    (dilated_support W a b (max 1 b) (clipDilation S) ha (le_max_left _ _)
      (clipDilation_ge_one S hS) (clipDilation_le b S hS hret) hs)
    (dilated_contDiff W hW (clipDilation S)) t

theorem retainedProfile_apply (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) (t x : ℝ) :
    retainedProfile W a b ha hs hW S hS hret t x =
      (x : ℂ) ^ (Complex.I * t) * W (clipDilation S * x) :=
  normPowerProfile_apply _ _ _ _ _ _ _ _

theorem retainedProfile_support (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) (t : ℝ) :
    Function.support (retainedProfile W a b ha hs hW S hS hret t : ℝ → ℂ) ⊆
      Set.Icc (a / max 1 b) b := by
  apply (normPowerProfile_support _ _ _ _ _ _ _).trans
  exact dilated_support W a b (max 1 b) (clipDilation S) ha (le_max_left _ _)
    (clipDilation_ge_one S hS) (clipDilation_le b S hS hret) hs

theorem retainedProfile_uniform_degree (a b : ℝ) (ha : 0 < a)
    (F : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧
      ∀ S : ℝ, ∀ hS : 0 < S, ∀ hret : 1 ≤ S * b, ∀ t : ℝ,
      F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (retainedProfile W a b ha hs hW S hS hret t) ≤ C * (1 + ‖t‖) ^ J := by
  obtain ⟨J, hJ⟩ := dilated_normPowerProfile_uniform_degree a b (max 1 b) ha (le_max_left _ _) F
  refine ⟨J, ?_⟩
  intro W hs hW
  obtain ⟨C, hC, hbound⟩ := hJ W hs hW
  exact ⟨C, hC, fun S hS hret t =>
    hbound (clipDilation S) (clipDilation_ge_one S hS) (clipDilation_le b S hS hret) t⟩

theorem two_retainedProfile_uniform_degree (a₁ b₁ a₂ b₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (F : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∀ W₁ W₂ : ℝ → ℂ,
      ∀ hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ hW₁ : ContDiff ℝ ∞ W₁, ∀ hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ S₁ S₂ : ℝ, ∀ hS₁ : 0 < S₁, ∀ hS₂ : 0 < S₂,
      ∀ hret₁ : 1 ≤ S₁ * b₁, ∀ hret₂ : 1 ≤ S₂ * b₂, ∀ t : ℝ,
      F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (retainedProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ S₁ hS₁ hret₁ t) +
      F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (retainedProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ S₂ hS₂ hret₂ t) ≤ C * (1 + ‖t‖) ^ J := by
  obtain ⟨J₁, hJ₁⟩ := retainedProfile_uniform_degree a₁ b₁ ha₁ F
  obtain ⟨J₂, hJ₂⟩ := retainedProfile_uniform_degree a₂ b₂ ha₂ F
  refine ⟨max J₁ J₂, ?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C₁, hC₁, hb₁⟩ := hJ₁ W₁ hs₁ hW₁
  obtain ⟨C₂, hC₂, hb₂⟩ := hJ₂ W₂ hs₂ hW₂
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro S₁ S₂ hS₁ hS₂ hret₁ hret₂ t
  have ht : 1 ≤ 1 + ‖t‖ := by linarith [norm_nonneg t]
  have h₁ := (hb₁ S₁ hS₁ hret₁ t).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (le_max_left J₁ J₂)) hC₁.le)
  have h₂ := (hb₂ S₂ hS₂ hret₂ t).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (le_max_right J₁ J₂)) hC₂.le)
  nlinarith

theorem retained_row_rectangle (η : Character) (m A₀ z : O)
    (W₁ W₂ : ℝ → ℂ) (t S₁ S₂ : ℝ) (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (A : ℂ) :
    A * (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂) =
      A * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
        rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂)) := by
  rw [clipped_rowTwistedSum η m A₀ z W₁ t S₁ hS₁,
    clipped_rowTwistedSum η m A₀ z W₂ t S₂ hS₂]

theorem strict_subunit_row_rectangle_zero (η : Character) (m A₀ z : O)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ t S₁ S₂ : ℝ) (hS₁ : 0 < S₁) (hS₂ : 0 < S₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hstrict : S₁ * b₁ < 1 ∨ S₂ * b₂ < 1) (A : ℂ) :
    A * (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂) = 0 := by
  rcases hstrict with h₁ | h₂
  · rw [strict_subunit_rowTwistedSum_zero η m A₀ z W₁ b₁ t S₁ hS₁ hs₁ h₁, zero_mul, mul_zero]
  · rw [strict_subunit_rowTwistedSum_zero η m A₀ z W₂ b₂ t S₂ hS₂ hs₂ h₂, mul_zero, mul_zero]

theorem two_retained_row_rectangles (η : Character) (m A₀ z : O)
    (W₁ W₂ : ℝ → ℂ) (t S₁ S₂ T₁ T₂ : ℝ)
    (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (A : ℂ) :
    ‖A * (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂ -
      rowTwistedSum η m A₀ z W₁ t T₁ * rowTwistedSum η m A₀ z W₂ t T₂)‖ ≤
      ‖A * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
        rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂))‖ +
      ‖A * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation T₁)) t (clippedScale T₁) *
        rowTwistedSum η m A₀ z (dilated W₂ (clipDilation T₂)) t (clippedScale T₂))‖ := by
  rw [mul_sub, retained_row_rectangle η m A₀ z W₁ W₂ t S₁ S₂ hS₁ hS₂ A,
    retained_row_rectangle η m A₀ z W₁ W₂ t T₁ T₂ hT₁ hT₂ A]
  exact norm_sub_le _ _

theorem two_retained_row_energies (η : Character) (m A₀ : O)
    (W₁ W₂ : ℝ → ℂ) (t S₁ S₂ T₁ T₂ : ℝ)
    (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (rows : Finset O) (A : O → ℂ) (w : O → ℝ) (hw : ∀ z ∈ rows, 0 ≤ w z) :
    (∑ z ∈ rows, w z * ‖A z *
      (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂ -
        rowTwistedSum η m A₀ z W₁ t T₁ * rowTwistedSum η m A₀ z W₂ t T₂)‖ ^ 2) ≤
      2 * (∑ z ∈ rows, w z * ‖A z *
        (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂))‖ ^ 2) +
      2 * (∑ z ∈ rows, w z * ‖A z *
        (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation T₁)) t (clippedScale T₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation T₂)) t (clippedScale T₂))‖ ^ 2) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro z hz
  have hb := two_retained_row_rectangles η m A₀ z W₁ W₂ t S₁ S₂ T₁ T₂ hS₁ hS₂ hT₁ hT₂ (A z)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hnorm : ‖A z *
      (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂ -
        rowTwistedSum η m A₀ z W₁ t T₁ * rowTwistedSum η m A₀ z W₂ t T₂)‖ ^ 2 ≤
      2 * ‖A z *
        (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂))‖ ^ 2 +
      2 * ‖A z *
        (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation T₁)) t (clippedScale T₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation T₂)) t (clippedScale T₂))‖ ^ 2 := by
    nlinarith [sq_nonneg
      (‖A z * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂))‖ -
       ‖A z * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation T₁)) t (clippedScale T₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation T₂)) t (clippedScale T₂))‖)]
  convert mul_le_mul_of_nonneg_left hnorm (hw z hz) using 1; ring

theorem retained_volumeControl_le (Q : Ideal O) (χ : Character)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) (t : ℝ) :
    volumeControl Q χ (retainedProfile W a b ha hs hW S hS hret t) ≤
      (max 1 b) ^ (pvSeminorms.sup Prod.snd) *
        volumeControl Q χ (normPowerProfile W a b ha hs hW t) := by
  have h := normPowerProfile_dilated_finite W a b (max 1 b) (clipDilation S)
    ha (le_max_left _ _) (clipDilation_ge_one S hS) (clipDilation_le b S hS hret) hs hW t pvSeminorms
  change pvSeminorms.sup (schwartzSeminormFamily ℝ ℝ ℂ)
    (retainedProfile W a b ha hs hW S hS hret t) ≤ _ at h
  unfold volumeControl pvControl
  have hh := mul_le_mul_of_nonneg_left h
    (show 0 ≤ ((IdealMobiusDivisorSum.idealDivisors χ.modulus).card : ℝ) *
      (Nat.card (O ⧸ Ideal.span {fixedPeriod Q}) : ℝ) * pvConstant from
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) pvConstant_pos.le)
  convert hh using 1 <;> ring

theorem retained_volumeControl_uniform_degree (Q : Ideal O) (a b ε B : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧
      ∀ Z : ℝ, 1 ≤ Z → ∀ χ : Character, (Ideal.absNorm χ.modulus : ℝ) ≤ Z ^ B →
      ∀ S : ℝ, ∀ hS : 0 < S, ∀ hret : 1 ≤ S * b, ∀ t : ℝ,
      volumeControl Q χ (retainedProfile W a b ha hs hW S hS hret t) ≤
        C * Z ^ ε * (1 + ‖t‖) ^ J := by
  obtain ⟨J, hJ⟩ := volumeControl_polynomial_height Q a b ε B ha hε hB
  refine ⟨J, ?_⟩
  intro W hs hW
  obtain ⟨C, hC, hbound⟩ := hJ W hs hW
  let D := (max 1 b) ^ (pvSeminorms.sup Prod.snd)
  have hD : 0 < D := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  refine ⟨D * C, mul_pos hD hC, ?_⟩
  intro Z hZ χ hχ S hS hret t
  calc
    _ ≤ D * volumeControl Q χ (normPowerProfile W a b ha hs hW t) :=
      retained_volumeControl_le Q χ W a b ha hs hW S hS hret t
    _ ≤ D * (C * Z ^ ε * (1 + ‖t‖) ^ J) :=
      mul_le_mul_of_nonneg_left (hbound Z hZ χ hχ t) hD.le
    _ = _ := by ring

end SevenEighths.CenteredMomentRetainedProfile

end

end OAI
end OAIOriginalModule1449

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalVolume
Source SHA256: bff775dabfc5195af50c00b8d4e8ea71cab1605ef7be8c795cbb6994ce1d8934
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1450



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentLattice CenteredMomentHeckeVolume
open CenteredMomentHeckeCancellation CenteredMomentHeckeHeight
open CenteredMomentMask
open QuadraticInitialBound EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

theorem volumeControl_source_control (a b ε B : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ n : ℕ, ∃ S : Finset (ℕ × ℕ), (0,0) ∈ S ∧
      ∀ Q : Ideal O, ∃ C : ℝ, 0 < C ∧
      ∀ W : 𝓢(ℝ,ℂ), ∀ hs : Function.support (W:ℝ→ℂ) ⊆ Set.Icc a b,
      ∀ Z : ℝ, 1 ≤ Z → ∀ χ : Character,
      (Ideal.absNorm χ.modulus : ℝ) ≤ Z^B → ∀ t : ℝ,
      volumeControl Q χ (normPowerProfile W a b ha hs (W.smooth ⊤) t) ≤
        C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * Z^ε * (1+‖t‖)^n := by
  obtain ⟨n,T,C,hC,hprofile⟩ := normPowerProfile_source_control a b ha pvSeminorms
  obtain ⟨D,hD,hdiv⟩ := polynomial_mask_divisor_bound ε B hε hB
  let S := insert (0,0) T
  refine ⟨n,S,by simp [S],?_⟩
  intro Q
  let mass : ℝ := Nat.card (O ⧸ Ideal.span {fixedPeriod Q})
  let A := D*mass*pvConstant*C
  have hmass : 0 ≤ mass := Nat.cast_nonneg _
  have hpv := pvConstant_pos
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨1+A,by positivity,?_⟩
  intro W hs Z hZ χ hnorm t
  have hTS : T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro z hz
    exact Seminorm.le_finset_sup_apply (Finset.mem_insert_of_mem hz)
  have hp := (hprofile W hs t).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTS hC.le) (by positivity))
  have herr : volumeControl Q χ (normPowerProfile W a b ha hs (W.smooth ⊤) t) ≤
      (D*Z^ε)*(mass*(pvConstant*(C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(1+‖t‖)^n))) := by
    unfold volumeControl pvControl
    rw [mul_assoc]
    apply mul_le_mul (hdiv Z hZ χ.modulus χ.modulus_ne_bot hnorm)
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp pvConstant_pos.le) hmass)
    · exact mul_nonneg hmass (mul_nonneg hpv.le (apply_nonneg _ _))
    · exact mul_nonneg hD.le (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  calc
    _ ≤ _ := herr
    _ = A*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Z^ε*(1+‖t‖)^n := by dsimp [A]; ring
    _ ≤ (1+A)*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Z^ε*(1+‖t‖)^n := by
      gcongr
      linarith

theorem retained_volumeControl_source_control (a b ε B : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ n : ℕ, ∃ S : Finset (ℕ × ℕ), (0,0) ∈ S ∧
      ∀ Q : Ideal O, ∃ C : ℝ, 0 < C ∧
      ∀ W : 𝓢(ℝ,ℂ), ∀ hs : Function.support (W:ℝ→ℂ) ⊆ Set.Icc a b,
      ∀ Z : ℝ, 1 ≤ Z → ∀ χ : Character,
