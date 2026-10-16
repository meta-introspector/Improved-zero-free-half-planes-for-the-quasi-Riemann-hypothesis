  refine ⟨by linarith,by linarith,?_⟩
  have heq : 6*(3/4+2*Δ)=9/2+12*Δ := by ring
  rw [heq,mul_sub,mul_div_cancel₀ _ hd.ne']
  nlinarith [mul_nonneg hd.le hν]

end SevenEighths.HeckeDetectorBranchBudget

end

end OAI
end OAIOriginalModule2060

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountEndpoint
Source SHA256: 79717dfc44a31432e01eba2992f2e136589659929168f4f33a70df4b2caef875
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2061



namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorRowCount

lemma denominator_endpoint (x : ℝ) : denominator x=Endpoint.denominator (1/2-x) := by
  unfold denominator Endpoint.denominator
  ring

lemma primeWeight_endpoint (x : ℝ) : primeWeight x=Endpoint.primeWeight (1/2-x) := by
  unfold primeWeight Endpoint.primeWeight
  ring

theorem balanced_cutoff_bounds {δ x : ℝ} (hδ : 0≤δ) (hδ' : δ≤5/6)
    (hx : 0≤x) (hx' : x≤1/2) :
    1≤Endpoint.balancedCutoff δ (1/2-x) ∧ Endpoint.balancedCutoff δ (1/2-x)≤3/2 := by
  have hy : 0≤1/2-x := by linarith
  have hy' : 1/2-x≤1/2 := by linarith
  have hd := Endpoint.denominator_bounds hy hy'
  have hp := Endpoint.primeWeight_bounds hy hy'
  have hJ := Endpoint.balanceDenominator_bounds hδ hδ' hy hy'
  have hJp : 0<Endpoint.balanceDenominator δ (1/2-x) := by linarith [hJ.1]
  unfold Endpoint.balancedCutoff
  constructor
  · exact le_add_of_nonneg_right (div_nonneg (mul_nonneg hδ (by linarith [hp.1])) (by positivity))
  · have hnum : δ*Endpoint.primeWeight (1/2-x)≤Endpoint.balanceDenominator δ (1/2-x) := by
      unfold Endpoint.balanceDenominator
      have hh := mul_nonneg (sub_nonneg.mpr hδ') (show 0≤Endpoint.denominator (1/2-x) by linarith [hd.1])
      linarith
    have hh : δ*Endpoint.primeWeight (1/2-x)/(2*Endpoint.balanceDenominator δ (1/2-x))≤1/2 :=
      (div_le_iff₀ (by positivity)).mpr (by linarith)
    linarith

theorem balanced_count_identity {δ x : ℝ} (hδ : 0≤δ) (hδ' : δ≤5/6)
    (hx : 0≤x) (hx' : x≤1/2) :
    max (shortExponent δ x (Endpoint.balancedCutoff δ (1/2-x)))
        (longExponent δ (Endpoint.balancedCutoff δ (1/2-x))) =
      Endpoint.balancedRowCount δ (1/2-x) := by
  have hy : 0≤1/2-x := by linarith
  have hy' : 1/2-x≤1/2 := by linarith
  have hDb : 0<Endpoint.denominator (1/2-x) := by
    have hh := Endpoint.denominator_bounds hy hy'
    linarith [hh.1]
  have hJb : 0<Endpoint.balanceDenominator δ (1/2-x) := by
    have hh := Endpoint.balanceDenominator_bounds hδ hδ' hy hy'
    linarith [hh.1]
  have hl : longExponent δ (Endpoint.balancedCutoff δ (1/2-x))=
      Endpoint.balancedRowCount δ (1/2-x) := by
    unfold longExponent Endpoint.balancedRowCount
    ring
  have hs : shortExponent δ x (Endpoint.balancedCutoff δ (1/2-x))=
      Endpoint.balancedRowCount δ (1/2-x) := by
    unfold shortExponent
    rw [denominator_endpoint,primeWeight_endpoint]
    unfold Endpoint.balancedRowCount Endpoint.balancedCutoff
    generalize hDd : Endpoint.denominator (1/2-x) = D at *
    generalize hPd : Endpoint.primeWeight (1/2-x) = P at *
    generalize hJd : Endpoint.balanceDenominator δ (1/2-x) = J at *
    have hJdef : J=(5/6-δ)*D+δ*P := by
      rw [←hJd, Endpoint.balanceDenominator, hDd, hPd]
    have hD : D ≠ 0 := hDb.ne'
    have hJ : J ≠ 0 := hJb.ne'
    field_simp [hD,hJ]
    rw [hJdef]
    ring
  rw [hl,hs,max_self]

theorem high_bin_count {B C U δ r ε γ : ℝ}
    (hC : 0≤C) (hU : 1≤U) (hδ : 5/6≤δ) (hδ' : δ≤1)
    (hγ : 0≤γ) (hr : 1-γ≤r)
    (hI : B≤C*U^(max 1 ((1+5*r)/6)-δ*r+ε)) :
    B≤C*U^(1-δ+ε+γ) := by
  apply hI.trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_le hU
  by_cases hr1 : 1≤r
  · rw [max_eq_right (show 1≤(1+5*r)/6 by linarith)]
    have hh := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hδ) (sub_nonneg.mpr hr1)
    nlinarith
  · rw [max_eq_left (show (1+5*r)/6≤1 by linarith)]
    have hh := mul_le_mul_of_nonneg_left hr (show 0≤δ by linarith)
    have hh' := mul_le_mul_of_nonneg_right hδ' hγ
    nlinarith

theorem high_bin_endpoint {δ q R loss : ℝ} (_hδ : 5/6≤δ)
    (hq : q≤δ/2) (hR : R≤1-δ+loss) :
    -(1/48 : ℝ)+(2/3)*δ+q/6-(13/16)*(1-R)≤
      -1/48-δ/16+(13/16)*loss := by
  linarith

theorem balanced_endpoint_with_loss {δ x R loss : ℝ}
    (hδ : 0≤δ) (hδ' : δ≤5/6) (hx : 0≤x) (hx' : x≤1/2)
    (hR : R≤max (shortExponent δ x (Endpoint.balancedCutoff δ (1/2-x)))
      (longExponent δ (Endpoint.balancedCutoff δ (1/2-x)))+loss) :
    -(1/48 : ℝ)+(2/3)*δ+(δ*x)/6-(13/16)*(1-R)≤
      -49/440640+(13/16)*loss := by
  rw [balanced_count_identity hδ hδ' hx hx'] at hR
  have hh := Endpoint.balanced_endpoint_margin hδ hδ'
    (show 0≤1/2-x by linarith) (show 1/2-x≤1/2 by linarith)
  unfold Endpoint.balancedExponent at hh
  nlinarith

end SevenEighths.HeckeDetectorRowCount

end

end OAI
end OAIOriginalModule2061

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CentralExponent
Source SHA256: c138e38592cb202bbc4c13021d65378163c77988ebda575a2af39c6961b92a83
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2062




namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeCentralExponent

def sourceExponent (a d R q : ℝ) : ℝ :=
  (17/48)*(1/2-17/50)+a+17/50-1-a*(23/48)-d*(17/50)+d*R+
    d*(a-1/2)+(1/6)*(17/50-1/2+q)

def relativeExponent (δ d R q : ℝ) : ℝ :=
  -1/48+(2/3)*δ+q/6-(13/16)*(1-R)+(d-13/16)*(R+δ/2-17/50)

lemma original_exponent_identity (a d R q : ℝ) :
    sourceExponent a d R q=3/16+relativeExponent (2*a-1) d R q := by
  unfold sourceExponent relativeExponent
  ring

lemma frequency_slope_bounds (δ R : ℝ) (_hδ : 0≤δ) (hδ1 : δ≤1)
    (hRlo : 1-δ≤R) (hRhi : R≤139/96) :
    4/25≤R+δ/2-17/50 ∧ R+δ/2-17/50≤2 := by
  constructor <;> linarith

lemma relative_extend (δ d R q ζ : ℝ) (hζ : 0≤ζ) (hd : d≤13/16+ζ)
    (hslo : 0≤R+δ/2-17/50) (hshi : R+δ/2-17/50≤2) :
    relativeExponent δ d R q≤relativeExponent δ (13/16) R q+2*ζ := by
  have hh := mul_le_mul_of_nonneg_right (show d-13/16≤ζ by linarith) hslo
  have hh' := mul_le_mul_of_nonneg_left hshi hζ
  unfold relativeExponent
  nlinarith

lemma balanced_source_margin (δ x R Δ loss ζ d : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤5/6) (hx : 0≤x) (hx1 : x≤1/2)
    (hR : R≤Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss)
    (hζ : 0≤ζ) (hd : d≤13/16+ζ)
    (hslo : 0≤R+δ/2-17/50) (hshi : R+δ/2-17/50≤2) :
    sourceExponent ((1+δ)/2) d R (δ*x)-(3/16+Δ)≤
      -49/440640-(51/64)*Δ+(13/16)*loss+2*ζ := by
  have hb := Endpoint.balanced_endpoint_margin hδ hδ1
    (show 0≤1/2-x by linarith) (show 1/2-x≤1/2 by linarith)
  have he := relative_extend δ d R (δ*x) ζ hζ hd hslo hshi
  rw [original_exponent_identity]
  have hid : 2*((1+δ)/2)-1=δ := by ring
  rw [hid]
  unfold Endpoint.balancedExponent at hb
  unfold relativeExponent at he ⊢
  nlinarith

lemma high_source_margin (δ R q Δ loss ζ d : ℝ)
    (hq : q≤δ/2) (hR : R≤1-δ+loss)
    (hζ : 0≤ζ) (hd : d≤13/16+ζ)
    (hslo : 0≤R+δ/2-17/50) (hshi : R+δ/2-17/50≤2) :
    sourceExponent ((1+δ)/2) d R q-(3/16+Δ)≤
      -1/48-δ/16-Δ+(13/16)*loss+2*ζ := by
  have he := relative_extend δ d R q ζ hζ hd hslo hshi
  rw [original_exponent_identity]
  have hid : 2*((1+δ)/2)-1=δ := by ring
  rw [hid]
  unfold relativeExponent at he ⊢
  nlinarith

lemma floor_source_margin (q Δ ζ d : ℝ) (hq : q≤1/100)
    (hζ : 0≤ζ) (hd : d≤13/16+ζ) :
    sourceExponent (51/100) d 1 q-(3/16+Δ)≤-7/1200-Δ+2*ζ := by
  have he := relative_extend (1/50) d 1 q ζ hζ hd (by norm_num) (by norm_num)
  rw [original_exponent_identity]
  norm_num only at *
  unfold relativeExponent at he ⊢
  nlinarith

lemma intermediate_source_margin (δ q Δ d : ℝ) (_hδ : 0≤δ) (hδ1 : δ≤5/6)
    (hq : q≤δ/2) (hd : d≤1/2) :
    sourceExponent ((1+δ)/2) d (76/75-(2/3)*δ) q-(3/16+Δ)≤-49/14400-Δ := by
  have hs : 0≤(76/75-(2/3)*δ)+δ/2-17/50 := by linarith
  have hm := mul_le_mul_of_nonneg_right hd hs
  unfold sourceExponent
  nlinarith

def realLoss (N : ℕ) (d e eps heightLoss mesh : ℝ) : ℝ :=
  (105/8)*e+12*d*e+d*eps*(N+8)+heightLoss+mesh/6

lemma realLoss_bound (N : ℕ) (d e eps heightLoss mesh : ℝ)
    (hd : d≤1) (he : 0≤e) (heps : 0≤eps) :
    realLoss N d e eps heightLoss mesh≤26*e+(N+8)*eps+heightLoss+mesh/6 := by
  have h1 := mul_le_mul_of_nonneg_right hd he
  have h2 := mul_le_mul_of_nonneg_right hd (show 0≤eps*(N+8) by positivity)
  unfold realLoss
  nlinarith

lemma physical_scale_identity (Z a e : ℝ) (hZ : 0<Z) :
    (Z^(17/48:ℝ))^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^(23/48:ℝ))^(-a-6*e)=
      Z^((25/48)*a-181/300+(105/8)*e) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring
end SevenEighths.ProbeCentralExponent

end

end OAI
end OAIOriginalModule2062

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorRowwise
Source SHA256: f8e678f568a18ac5029c33c7293ace7482797b5c2316af7969696acf1cdd4dc6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2063



namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory Set
namespace SevenEighths.HeckeDetectorRowwise

theorem norm_sq_le_anchor_integral (F F' : ℝ→ℂ)
    (hF : Continuous F) (hF' : Continuous F')
    (hd : ∀ x, HasDerivAt F (F' x) x) {a b x : ℝ} (hx : x∈Icc a b) :
    ‖F x‖^2≤‖F a‖^2+∫ t in a..b, (‖F t‖^2+‖F' t‖^2) := by
  let G : ℝ→ℝ := fun t => ‖F t‖^2+‖F' t‖^2
  have hG : Continuous G := (hF.norm.pow 2).add (hF'.norm.pow 2)
  have hh := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hx.1
    (hF.norm.pow 2).continuousOn
    (fun t ht => (hd t).norm_sq.hasDerivWithinAt)
    (hG.continuousOn.integrableOn_Icc)
    (fun t ht => show 2*inner (𝕜:=ℝ) (F t) (F' t)≤G t by
      dsimp [G]
      have hc := real_inner_le_norm (F t) (F' t)
      change (F' t * (starRingEnd ℂ) (F t)).re ≤ ‖F t‖*‖F' t‖ at hc
      nlinarith [sq_nonneg (‖F t‖-‖F' t‖)])
  simp only [Pi.pow_apply] at hh
  have hm := intervalIntegral.integral_mono_interval (μ:=volume) (le_refl a) hx.1 hx.2
    (Filter.Eventually.of_forall (fun t => show 0≤G t by dsimp [G]; positivity))
    (hG.intervalIntegrable a b)
  change ‖F x‖^2≤‖F a‖^2+∫ t in a..b, G t
  linarith

theorem rowwise_energy {ι : Type*} (rows : Finset ι) (F F' : ι→ℝ→ℂ)
    (hF : ∀ i∈rows, Continuous (F i)) (hF' : ∀ i∈rows, Continuous (F' i))
    (hd : ∀ i∈rows, ∀ x, HasDerivAt (F i) (F' i x) x)
    (a b E : ℝ) (hab : a≤b) (choice : ι→ℝ)
    (hc : ∀ i∈rows, choice i∈Icc a b)
    (henergy : ∀ t∈Icc a b, ∑ i∈rows, ‖F i t‖^2≤E)
    (henergy' : ∀ t∈Icc a b, ∑ i∈rows, ‖F' i t‖^2≤E) :
    ∑ i∈rows, ‖F i (choice i)‖^2≤(1+2*(b-a))*E := by
  have hg (i : ι) (hi : i∈rows) :
      Continuous (fun t => ‖F i t‖^2+‖F' i t‖^2) :=
    ((hF i hi).norm.pow 2).add ((hF' i hi).norm.pow 2)
  have hs := Finset.sum_le_sum (fun i hi =>
    norm_sq_le_anchor_integral (F i) (F' i) (hF i hi) (hF' i hi) (hd i hi) (hc i hi))
  rw [Finset.sum_add_distrib,←intervalIntegral.integral_finsetSum
    (fun i hi => (hg i hi).intervalIntegrable a b)] at hs
  have hm : (∫ t in a..b, ∑ i∈rows, (‖F i t‖^2+‖F' i t‖^2))≤(b-a)*(2*E) := by
    have hh := intervalIntegral.integral_mono_on (μ:=volume) hab
      ((continuous_finsetSum rows (fun i hi => hg i hi)).intervalIntegrable a b)
      (continuous_const.intervalIntegrable a b)
      (fun t ht => show (∑ i∈rows, (‖F i t‖^2+‖F' i t‖^2))≤2*E by
        rw [Finset.sum_add_distrib]
        linarith [henergy t ht,henergy' t ht])
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using hh
  have ha := henergy a ⟨le_refl a,hab⟩
  nlinarith

theorem rowwise_energy_two {ι : Type*} (rows : Finset ι)
    (F : Fin 2→Fin 2→ι→ℝ→ℝ→ℂ)
    (hcont : ∀ j k i, i∈rows → Continuous (Function.uncurry (F j k i)))
    (hdx : ∀ k i, i∈rows → ∀ x y,
      HasDerivAt (fun u => F 0 k i u y) (F 1 k i x y) x)
    (hdy : ∀ j i, i∈rows → ∀ x y,
      HasDerivAt (F j 0 i x) (F j 1 i x y) y)
    (a b c d E : ℝ) (hab : a≤b) (hcd : c≤d) (px py : ι→ℝ)
    (hpx : ∀ i∈rows, px i∈Icc a b) (hpy : ∀ i∈rows, py i∈Icc c d)
    (henergy : ∀ j k x, x∈Icc a b → ∀ y, y∈Icc c d →
      ∑ i∈rows, ‖F j k i x y‖^2≤E) :
    ∑ i∈rows, ‖F 0 0 i (px i) (py i)‖^2≤
      (1+2*(b-a))*((1+2*(d-c))*E) := by
  have cx (j k : Fin 2) (i : ι) (hi : i∈rows) (y : ℝ) :
      Continuous (fun x => F j k i x y) :=
    (hcont j k i hi).comp (continuous_id.prodMk continuous_const)
  have cy (j k : Fin 2) (i : ι) (hi : i∈rows) (x : ℝ) :
      Continuous (F j k i x) :=
    (hcont j k i hi).comp (continuous_const.prodMk continuous_id)
  have he (j : Fin 2) (x : ℝ) (hx : x∈Icc a b) :
      ∑ i∈rows, ‖F j 0 i x (py i)‖^2≤(1+2*(d-c))*E :=
    rowwise_energy rows (fun i => F j 0 i x) (fun i => F j 1 i x)
      (fun i hi => cy j 0 i hi x) (fun i hi => cy j 1 i hi x)
      (fun i hi y => hdy j i hi x y) c d E hcd py hpy
      (fun y hy => henergy j 0 x hx y hy) (fun y hy => henergy j 1 x hx y hy)
  exact rowwise_energy rows (fun i x => F 0 0 i x (py i))
    (fun i x => F 1 0 i x (py i))
    (fun i hi => cx 0 0 i hi (py i)) (fun i hi => cx 1 0 i hi (py i))
    (fun i hi x => hdx 0 i hi x (py i)) a b ((1+2*(d-c))*E) hab px hpx
    (he 0) (he 1)

theorem source_height_cost {T E : ℝ} (_hT : 0≤T) (hE : 0≤E) :
    (1+2*((1:ℝ)-0))*((1+2*(T-(-T)))*E)≤12*(1+T)*E := by
  nlinarith

end SevenEighths.HeckeDetectorRowwise

end

end OAI
end OAIOriginalModule2063

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorRowwiseChain
Source SHA256: 77e379be5bc80840034768e5d13db3422ce63fae24f94913070da84ebdbab214
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2064


namespace OAI

noncomputable section
open scoped BigOperators Classical
open Set Complex
namespace SevenEighths.HeckeDetectorRowwise

theorem chain_rowwise {ι : Type*} (rows : Finset ι) (M : ℕ→ι→ℝ→ℝ→ℂ)
    (cm : ∀ n i, n≤2 → Continuous (Function.uncurry (M n i)))
    (dx : ∀ n i x y, n≤1 → HasDerivAt (fun u => M n i u y) (-M (n+1) i x y) x)
    (dy : ∀ n i x y, n≤1 → HasDerivAt (M n i x) (I*M (n+1) i x y) y)
    (a b c d E : ℝ) (hab : a≤b) (hcd : c≤d)
    (σ freq : ι→ℝ) (hσ : ∀ i∈rows, σ i∈Icc a b)
    (hf : ∀ i∈rows, freq i∈Icc c d)
    (henergy : ∀ n, n≤2 → ∀ x∈Icc a b, ∀ y∈Icc c d,
      ∑ i∈rows, ‖M n i x y‖^2≤E) :
    ∑ i∈rows, ‖M 0 i (σ i) (freq i)‖^2≤
      (1+2*(b-a))*((1+2*(d-c))*E) := by
  let F : Fin 2→Fin 2→ι→ℝ→ℝ→ℂ := fun j k i x y =>
    if j=0 then (if k=0 then M 0 i x y else I*M 1 i x y)
    else (if k=0 then -M 1 i x y else -(I*M 2 i x y))
  have cF (j k : Fin 2) (i : ι) (hi : i∈rows) : Continuous (Function.uncurry (F j k i)) := by
    have c0 := cm 0 i (by norm_num)
    have c1 := cm 1 i (by norm_num)
    have c2 := cm 2 i (by norm_num)
    fin_cases j <;> fin_cases k
    · simpa [F] using c0
    · convert c1.const_mul I using 1
      ext p
      simp [F]
      rfl
    · convert c1.neg using 1
      ext p
      simp [F]
      rfl
    · convert (c2.const_mul I).neg using 1
      ext p
      simp [F]
      rfl
  have dFx (k : Fin 2) (i : ι) (hi : i∈rows) (x y : ℝ) :
      HasDerivAt (fun u => F 0 k i u y) (F 1 k i x y) x := by
    fin_cases k
    · simpa [F] using dx 0 i x y (by norm_num)
    · simpa [F] using (dx 1 i x y (by norm_num)).const_mul I
  have dFy (j : Fin 2) (i : ι) (hi : i∈rows) (x y : ℝ) :
      HasDerivAt (F j 0 i x) (F j 1 i x y) y := by
    fin_cases j
    · simpa [F] using dy 0 i x y (by norm_num)
    · convert (dy 1 i x y (by norm_num)).neg using 1
      · ext t
        simp [F]
      · simp [F]
  have eF (j k : Fin 2) (x : ℝ) (hx : x∈Icc a b) (y : ℝ) (hy : y∈Icc c d) :
      ∑ i∈rows, ‖F j k i x y‖^2≤E := by
    fin_cases j <;> fin_cases k
    · simpa [F] using henergy 0 (by norm_num) x hx y hy
    · simpa [F,norm_mul] using henergy 1 (by norm_num) x hx y hy
    · simpa [F] using henergy 1 (by norm_num) x hx y hy
    · simpa [F,norm_mul] using henergy 2 (by norm_num) x hx y hy
  simpa only [F,ite_true] using
    rowwise_energy_two rows F cF dFx dFy a b c d E hab hcd σ freq hσ hf eF

end SevenEighths.HeckeDetectorRowwise

end

end OAI
end OAIOriginalModule2064

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorRowwisePolynomial
Source SHA256: 0b423728a729766e8540c39f3bfc9db72df4c9cea9210ef475b582d9703bed0c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2065


namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff Topology
open Set Complex
namespace SevenEighths.HeckeDetectorRowwisePolynomial
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge

def logProfile (W : ℝ→ℂ) (x : ℝ) : ℂ := (Real.log x : ℂ)*W x

theorem logProfile_cover (W : ℝ→ℂ) (D : ℝ) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    ∀ J : Ideal O, J≠0 → logProfile W ((J.absNorm : ℝ)/D)≠0 → J∈S := by
  intro J hJ hw
  exact hc J hJ (fun hz => hw (by simp [logProfile,hz]))

theorem logProfile_support (W : ℝ→ℂ) :
    Function.support (logProfile W)⊆Function.support W := by
  intro x hx hw
  exact hx (by simp [logProfile,hw])

theorem logProfile_smooth (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (logProfile W) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    have he : logProfile W =ᶠ[nhds (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [isOpen_Iio.mem_nhds ha] with y hy
      have hw : W y=0 := by
        by_contra hn
        exact (not_le_of_gt hy) (hs hn).1
      simp [logProfile,hw]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (Real.contDiffAt_log.mpr hx)).mul hW.contDiffAt

lemma power_sigma_deriv (x σ freq : ℝ) (hx : 0<x) :
    HasDerivAt (fun u : ℝ => (x : ℂ)^(-HeckeDyadic.shift u freq))
      (-(Real.log x : ℂ)*(x : ℂ)^(-HeckeDyadic.shift σ freq)) σ := by
  have hd := (((hasDerivAt_id (σ : ℂ)).neg).add_const ((freq : ℂ)*I)).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hh := hd.comp_ofReal
  rw [←Complex.ofReal_log hx.le] at hh
  convert hh using 1
  · ext u
    congr 1
    simp only [HeckeDyadic.shift,neg_sub,Pi.neg_apply,id_eq]
    ring
  · have he : -HeckeDyadic.shift σ freq= -(σ : ℂ)+(freq : ℂ)*I := by unfold HeckeDyadic.shift; ring
    rw [he]
    simp only [Pi.neg_apply,id_eq]
    ring

lemma power_freq_deriv (x σ freq : ℝ) (hx : 0<x) :
    HasDerivAt (fun u : ℝ => (x : ℂ)^(-HeckeDyadic.shift σ u))
      (I*(Real.log x : ℂ)*(x : ℂ)^(-HeckeDyadic.shift σ freq)) freq := by
  have hd := (((hasDerivAt_id (freq : ℂ)).mul_const I).const_add (-(σ : ℂ))).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hh := hd.comp_ofReal
  rw [←Complex.ofReal_log hx.le] at hh
  convert hh using 1
  · ext u
    congr 1
    simp [HeckeDyadic.shift]
    ring
  · have he : -HeckeDyadic.shift σ freq= -(σ : ℂ)+(freq : ℂ)*I := by unfold HeckeDyadic.shift; ring
    rw [he]
    simp only [id_eq]
    ring

theorem polynomial_sigma_deriv (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    HasDerivAt (fun u => polynomial χ inv W D u freq)
      (-polynomial χ inv (logProfile W) D σ freq) σ := by
  simp_rw [polynomial_eq_finite χ inv W D _ _ S hc]
  rw [polynomial_eq_finite χ inv (logProfile W) D σ freq S (logProfile_cover W D S hc)]
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun u => coefficient χ inv J*W ((J.absNorm : ℝ)/D)*
        (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift u freq))
      (-coefficient χ inv J*logProfile W ((J.absNorm : ℝ)/D)*
        (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq)) σ := by
    by_cases hz : J=0
    · subst J
      simpa only [coefficient_zero,zero_mul,neg_zero] using hasDerivAt_const σ (0 : ℂ)
    have hn : 0<(J.absNorm : ℝ)/D := div_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hz)) hD
    convert (power_sigma_deriv _ σ freq hn).const_mul
      (coefficient χ inv J*W ((J.absNorm : ℝ)/D)) using 1
    unfold logProfile
    ring
  convert (HasDerivAt.sum (u:=S) hd).const_mul ((D : ℂ)^(-(1/2 : ℂ))) using 1
  all_goals simp only [Finset.sum_apply,neg_mul,Finset.sum_neg_distrib,mul_neg]

theorem polynomial_freq_deriv (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    HasDerivAt (fun u => polynomial χ inv W D σ u)
      (I*polynomial χ inv (logProfile W) D σ freq) freq := by
  simp_rw [polynomial_eq_finite χ inv W D _ _ S hc]
  rw [polynomial_eq_finite χ inv (logProfile W) D σ freq S (logProfile_cover W D S hc)]
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun u => coefficient χ inv J*W ((J.absNorm : ℝ)/D)*
        (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ u))
      (I*(coefficient χ inv J*logProfile W ((J.absNorm : ℝ)/D)*
        (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq))) freq := by
    by_cases hz : J=0
    · subst J
      simpa only [coefficient_zero,zero_mul,mul_zero] using hasDerivAt_const freq (0 : ℂ)
    have hn : 0<(J.absNorm : ℝ)/D := div_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hz)) hD
    convert (power_freq_deriv _ σ freq hn).const_mul
      (coefficient χ inv J*W ((J.absNorm : ℝ)/D)) using 1
    unfold logProfile
    ring
  convert (HasDerivAt.sum (u:=S) hd).const_mul ((D : ℂ)^(-(1/2 : ℂ))) using 1
  all_goals simp only [Finset.sum_apply,←Finset.mul_sum]
  ring

theorem polynomial_continuous (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    Continuous (fun p : ℝ×ℝ => polynomial χ inv W D p.1 p.2) := by
  simp_rw [polynomial_eq_finite χ inv W D _ _ S hc]
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro J hJ
  by_cases hz : J=0
  · subst J
    simp only [coefficient_zero,zero_mul]
    exact continuous_const
  have hn : 0<(J.absNorm : ℝ)/D := div_pos
    (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hz)) hD
  apply Continuous.const_mul
  apply Continuous.const_cpow _ (Or.inl (Complex.ofReal_ne_zero.mpr hn.ne'))
  unfold HeckeDyadic.shift
  fun_prop

end SevenEighths.HeckeDetectorRowwisePolynomial

end

end OAI
end OAIOriginalModule2065

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorRowwiseMarked
Source SHA256: 12eb24e111a1effaa70d5cb05530024c9c00c84c28253515cb25713503bd7240
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2066



namespace OAI

noncomputable section
open scoped BigOperators Classical
open Set Complex
namespace SevenEighths.HeckeDetectorRowwiseMarked
open HeckeFamily HeckeDyadic HeckeDetectorRowwise HeckeDetectorRowwisePolynomial

theorem marked_rowwise {ι : Type*} (rows : Finset ι) (χ : ι→Character)
    (inv : Bool) (W : ℝ→ℂ) (D : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S)
    (P : ι→ℂ) (a b c d E : ℝ) (hab : a≤b) (hcd : c≤d)
    (σ freq : ι→ℝ) (hσ : ∀ i∈rows, σ i∈Icc a b)
    (hf : ∀ i∈rows, freq i∈Icc c d)
    (h0 : ∀ x∈Icc a b, ∀ y∈Icc c d,
      ∑ i∈rows, ‖polynomial (χ i) inv W D x y*P i‖^2≤E)
    (h1 : ∀ x∈Icc a b, ∀ y∈Icc c d,
      ∑ i∈rows, ‖polynomial (χ i) inv (logProfile W) D x y*P i‖^2≤E)
    (h2 : ∀ x∈Icc a b, ∀ y∈Icc c d,
      ∑ i∈rows, ‖polynomial (χ i) inv (logProfile (logProfile W)) D x y*P i‖^2≤E) :
    ∑ i∈rows, ‖polynomial (χ i) inv W D (σ i) (freq i)*P i‖^2≤
      (1+2*(b-a))*((1+2*(d-c))*E) := by
  let M (n : ℕ) (i : ι) (x y : ℝ) :=
    polynomial (χ i) inv ((logProfile^[n]) W) D x y*P i
  have hc1 := logProfile_cover W D S hc
  have hc2 := logProfile_cover (logProfile W) D S hc1
  have cm (n : ℕ) (i : ι) (hn : n≤2) : Continuous (Function.uncurry (M n i)) := by
    interval_cases n
    all_goals
      dsimp [M,Function.uncurry]
      apply Continuous.mul_const
    · exact polynomial_continuous (χ i) inv W D hD S hc
    · exact polynomial_continuous (χ i) inv (logProfile W) D hD S hc1
    · exact polynomial_continuous (χ i) inv (logProfile (logProfile W)) D hD S hc2
  have dx (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (fun u => M n i u y) (-M (n+1) i x y) x := by
    interval_cases n
    · simpa [M] using (polynomial_sigma_deriv (χ i) inv W D x y hD S hc).mul_const (P i)
    · simpa [M] using (polynomial_sigma_deriv (χ i) inv (logProfile W) D x y hD S hc1).mul_const (P i)
  have dy (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (M n i x) (I*M (n+1) i x y) y := by
    interval_cases n
    · simpa [M,mul_assoc] using (polynomial_freq_deriv (χ i) inv W D x y hD S hc).mul_const (P i)
    · simpa [M,mul_assoc] using (polynomial_freq_deriv (χ i) inv (logProfile W) D x y hD S hc1).mul_const (P i)
  have he (n : ℕ) (hn : n≤2) (x : ℝ) (hx : x∈Icc a b) (y : ℝ) (hy : y∈Icc c d) :
      ∑ i∈rows, ‖M n i x y‖^2≤E := by
    interval_cases n
    · simpa [M] using h0 x hx y hy
    · simpa [M] using h1 x hx y hy
    · simpa [M] using h2 x hx y hy
  exact chain_rowwise rows M cm dx dy a b c d E hab hcd σ freq hσ hf he

end SevenEighths.HeckeDetectorRowwiseMarked

end

end OAI
end OAIOriginalModule2066

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorRowwisePlain
Source SHA256: ae1459a1396d719e2741f98db6618a06340ec439aa22943e66c9c185e3cd8e3e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2067


namespace OAI

noncomputable section
open scoped BigOperators Classical
open Set Complex
namespace SevenEighths.HeckeDetectorRowwisePlain
open HeckeFamily HeckeDyadic HeckeDetectorRowwise HeckeDetectorRowwisePolynomial

lemma norm_sum_sq_le (u v : ℂ) : ‖u+v‖^2≤2*(‖u‖^2+‖v‖^2) := by
  have h := norm_add_le u v
  nlinarith [norm_nonneg (u+v),norm_nonneg u,norm_nonneg v,sq_nonneg (‖u‖-‖v‖)]

theorem plain_squared_rowwise {ι : Type*} (rows : Finset ι) (χ : ι→Character)
    (W : ℝ→ℂ) (D : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S)
    (P : ι→ℂ) (a b c d E : ℝ) (hab : a≤b) (hcd : c≤d) (hE : 0≤E)
    (σ freq : ι→ℝ) (hσ : ∀ i∈rows, σ i∈Icc a b)
    (hf : ∀ i∈rows, freq i∈Icc c d)
    (henergy : ∀ j k : ℕ, j+k≤2 → ∀ x∈Icc a b, ∀ y∈Icc c d,
      ∑ i∈rows, ‖polynomial (χ i) false ((logProfile^[j]) W) D x y*
        polynomial (χ i) false ((logProfile^[k]) W) D x y*P i‖^2≤E) :
    ∑ i∈rows, ‖polynomial (χ i) false W D (σ i) (freq i)*
      polynomial (χ i) false W D (σ i) (freq i)*P i‖^2≤
      (1+2*(b-a))*((1+2*(d-c))*(16*E)) := by
  let Q (n : ℕ) (i : ι) (x y : ℝ) := polynomial (χ i) false ((logProfile^[n]) W) D x y
  let M (n : ℕ) (i : ι) (x y : ℝ) :=
    if n=0 then Q 0 i x y*Q 0 i x y*P i
    else if n=1 then 2*Q 0 i x y*Q 1 i x y*P i
    else 2*(Q 1 i x y*Q 1 i x y+Q 0 i x y*Q 2 i x y)*P i
  have hc1 := logProfile_cover W D S hc
  have hc2 := logProfile_cover (logProfile W) D S hc1
  have cq (n : ℕ) (i : ι) (hn : n≤2) : Continuous (Function.uncurry (Q n i)) := by
    interval_cases n
    · exact polynomial_continuous (χ i) false W D hD S hc
    · exact polynomial_continuous (χ i) false (logProfile W) D hD S hc1
    · exact polynomial_continuous (χ i) false (logProfile (logProfile W)) D hD S hc2
  have qx (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (fun u => Q n i u y) (-Q (n+1) i x y) x := by
    interval_cases n
    · exact polynomial_sigma_deriv (χ i) false W D x y hD S hc
    · exact polynomial_sigma_deriv (χ i) false (logProfile W) D x y hD S hc1
  have qy (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (Q n i x) (I*Q (n+1) i x y) y := by
    interval_cases n
    · exact polynomial_freq_deriv (χ i) false W D x y hD S hc
    · exact polynomial_freq_deriv (χ i) false (logProfile W) D x y hD S hc1
  have cm (n : ℕ) (i : ι) (hn : n≤2) : Continuous (Function.uncurry (M n i)) := by
    have c0 := cq 0 i (by norm_num)
    have c1 := cq 1 i (by norm_num)
    have c2 := cq 2 i (by norm_num)
    change Continuous (fun p : ℝ×ℝ => M n i p.1 p.2)
    change Continuous (fun p : ℝ×ℝ => Q 0 i p.1 p.2) at c0
    change Continuous (fun p : ℝ×ℝ => Q 1 i p.1 p.2) at c1
    change Continuous (fun p : ℝ×ℝ => Q 2 i p.1 p.2) at c2
    interval_cases n <;> dsimp [M] <;> fun_prop
  have dx (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (fun u => M n i u y) (-M (n+1) i x y) x := by
    interval_cases n
    · convert ((qx 0 i x y (by norm_num)).mul (qx 0 i x y (by norm_num))).mul_const (P i) using 1
      · ext u; simp [M]
      · simp [M]; ring
    · convert (((qx 0 i x y (by norm_num)).mul (qx 1 i x y (by norm_num))).const_mul 2).mul_const (P i) using 1
      · ext u; dsimp [M]; ring
      · simp [M]; ring
  have dy (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (M n i x) (I*M (n+1) i x y) y := by
    interval_cases n
    · convert ((qy 0 i x y (by norm_num)).mul (qy 0 i x y (by norm_num))).mul_const (P i) using 1
      · ext u; simp [M]
      · simp [M]; ring
    · convert (((qy 0 i x y (by norm_num)).mul (qy 1 i x y (by norm_num))).const_mul 2).mul_const (P i) using 1
      · ext u; dsimp [M]; ring
      · simp [M]; ring
  have he (n : ℕ) (hn : n≤2) (x : ℝ) (hx : x∈Icc a b) (y : ℝ) (hy : y∈Icc c d) :
      ∑ i∈rows, ‖M n i x y‖^2≤16*E := by
    have e00 := henergy 0 0 (by norm_num) x hx y hy
    have e01 := henergy 0 1 (by norm_num) x hx y hy
    have e11 := henergy 1 1 (by norm_num) x hx y hy
    have e02 := henergy 0 2 (by norm_num) x hx y hy
    change ∑ i∈rows, ‖Q 0 i x y*Q 0 i x y*P i‖^2≤E at e00
    change ∑ i∈rows, ‖Q 0 i x y*Q 1 i x y*P i‖^2≤E at e01
    change ∑ i∈rows, ‖Q 1 i x y*Q 1 i x y*P i‖^2≤E at e11
    change ∑ i∈rows, ‖Q 0 i x y*Q 2 i x y*P i‖^2≤E at e02
    interval_cases n
    · simpa only [M,ite_true] using e00.trans (show E≤16*E by linarith)
    · have heq : (∑ i∈rows, ‖M 1 i x y‖^2)=4*∑ i∈rows, ‖Q 0 i x y*Q 1 i x y*P i‖^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hm : M 1 i x y=2*(Q 0 i x y*Q 1 i x y*P i) := by simp [M]; ring
        rw [hm,norm_mul,mul_pow]
        norm_num
      rw [heq]
      linarith
    · have hh : (∑ i∈rows, ‖M 2 i x y‖^2)≤
          8*((∑ i∈rows, ‖Q 1 i x y*Q 1 i x y*P i‖^2)+
          ∑ i∈rows, ‖Q 0 i x y*Q 2 i x y*P i‖^2) := by
        rw [←Finset.sum_add_distrib,Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        have hm : M 2 i x y=2*(Q 1 i x y*Q 1 i x y*P i+Q 0 i x y*Q 2 i x y*P i) := by simp [M]; ring
        rw [hm,norm_mul,mul_pow]
        norm_num
        have hh := norm_sum_sq_le (Q 1 i x y*Q 1 i x y*P i) (Q 0 i x y*Q 2 i x y*P i)
        simp only [norm_mul] at hh
        nlinarith
      linarith
  simpa only [M,ite_true,Q,Function.iterate_zero,id_eq] using
    chain_rowwise rows M cm dx dy a b c d (16*E) hab hcd σ freq hσ hf he

end SevenEighths.HeckeDetectorRowwisePlain

end

end OAI
end OAIOriginalModule2067

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorSimultaneousSupport
Source SHA256: fe274df3b8e03b30832ac3e87c995e7284144ee23c80e6c9dee940f696f8f0b3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2068



namespace OAI

noncomputable section

open scoped Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorSimultaneousSupport
open HeckeFamily HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorDyadicGeometry HeckeDetectorSaturation HeckeDetectorNormalized

theorem from_actual_zero (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀≤Z → ∀ d : ℝ, dmin≤d → d≤dmax →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j, (χ j).residue≠1)
        (a : ℝ) (i : ℕ), i≤I → 51/100≤a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
        ∀ j : ι, (χ j).modulus.absNorm≤Z^d → ∀ ρ : ℂ,
        LFunction (χ j) ρ=0 → a≤ρ.re → |ρ.im|≤(3*i : ℕ)*Z^τ →
        ∀ tstar : ℝ, 1≤tstar → tstar≤3/2 →
        ∃ J∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
          ∃ K∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
            ∃ ν r m : ℝ,
              ‖ν‖≤(Z^d)^(τ/(2*dmax)) ∧ (Z^d)^r=(2 : ℝ)^J ∧ (Z^d)^m=(2 : ℝ)^K ∧
              tstar-1/2-76*ε≤r ∧ r≤tstar+ε ∧ 0≤m ∧ m≤1/2+75*ε ∧ tstar-r-ε≤m ∧
              (Z^d)^((2*a-1)*r-2*ε)≤
                ‖polynomial (χ j) true
                  (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular ((Z^d)^tstar) ((Z^d)^r))
                  ((Z^d)^r) ρ.re (2*Real.pi*ν-ρ.im)‖^2 ∧
              (Z^d)^((2*a-1)*m-2*ε)≤
                ‖polynomial (χ j) false positiveAnnular ((Z^d)^m) ρ.re (2*Real.pi*ν-ρ.im)‖^2 := by
  have hdmaxp : 0<dmax := hdmin.trans_le hdmax
  have hτF : 0<τ/(2*dmax) := by positivity
  obtain ⟨C,UN,hC,hN⟩ := exists_normalized_product 1 (1/2) (τ/(2*dmax))
    (by norm_num) (by norm_num) (by norm_num) hτF
  obtain ⟨US,hS⟩ := actual_saturation 22 dmax τ ε e κ η C
    (by norm_num) hdmaxp.le hτ hε he he' hκ hκ' hη hbudget hC.le
  have hscale := uniform_scale_threshold dmin (max 8 (max UN US)) hdmin
  have hzeroH := uniform_zero_height dmin τ I hτzero
  have hbudgetH := uniform_height_budget dmin τ η I hτ.le hη hτheight
  have hFourier := uniform_fourier_allowance dmax τ hdmaxp hτ
  have hcost := uniform_power_allowance 8 0 dmin ε hε.le (mul_pos hdmin hε)
  have hT := (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2 : ℝ))
  have hall := hscale.and (hzeroH.and (hbudgetH.and (hFourier.and (hcost.and
    (hT.and (eventually_ge_atTop (1 : ℝ)))))))
  obtain ⟨Z₀,hZ₀⟩ := Filter.eventually_atTop.mp hall
  refine ⟨Z₀,?_⟩
  intro Z hZlarge d hd hd' ι _ χ hχ a i hi ha ha' hmax j hQ ρ hzero hρ him tstar ht ht'
  obtain ⟨hscale,hzeroH,hbudgetH,hFourier,hcost,hT,hZ⟩ := hZ₀ Z hZlarge
  let U := Z^d
  have hd0 : 0≤d := (hdmin.trans_le hd).le
  have hlarge := hscale d hd
  have hU8 : 8≤U := (le_max_left _ _).trans hlarge
  have hUN : UN≤U := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hUS : US≤U := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hU2 : 2≤U := by linarith
  have hU1 : 1<U := by linarith
  have hUp : 0<U := by linarith
  have hρlo : 51/100≤ρ.re := ha.trans hρ
  have hρhi : ρ.re≤1 := le_of_lt (lt_of_not_ge (fun hh =>
    LFunction_ne_zero_of_one_le_re (χ j) hh (Or.inr (hχ j)) hzero))
  have hh := him.trans (hzeroH d hd i hi)
  obtain ⟨hDs,hDs'⟩ := truncation_scale U tstar hU2 ht ht'
  obtain ⟨J,hJ,K,hK,ν,hν,hprod,hD,hDN,hterminal⟩ :=
    hN U hUN (χ j) (hχ j) (U^tstar) hDs hDs' (by simpa using hQ) ρ hρlo hzero hh
  obtain ⟨hr,hr',hm,hm',heJ,heK⟩ := dyadic_scale_bounds U hU8 J K hterminal
  let r := Real.logb U ((2 : ℝ)^J)
  let m := Real.logb U ((2 : ℝ)^K)
  change U^r=(2 : ℝ)^J at heJ
  change U^m=(2 : ℝ)^K at heK
  have hJpow : (Z^d)^r=(2 : ℝ)^J := heJ
  have hKpow : (Z^d)^m=(2 : ℝ)^K := heK
  have hcostU : 8≤U^ε := by simpa using hcost d hd
  have hsupport := support_exponents U tstar r m ε hU1 hcostU
    (by simpa only [heJ] using hD) (by simpa only [heJ,heK] using hDN)
  have hfreq : |2*Real.pi*ν-ρ.im|+(Z^τ)/2≤(3*i+2 : ℕ)*Z^τ := by
    have habs : |ν|≤U^(τ/(2*dmax)) := by simpa only [Real.norm_eq_abs] using hν
    have hnu := (mul_le_mul_of_nonneg_left habs (show 0≤2*Real.pi by positivity)).trans
      (hFourier d hd0 hd')
    have hbase : |2*Real.pi*ν-ρ.im|≤2*Real.pi*|ν|+|ρ.im| := by
      simpa only [sub_zero,zero_sub,abs_neg,abs_mul,
        abs_of_pos (show 0<2*Real.pi by positivity)] using
        (abs_sub_le (2*Real.pi*ν) 0 ρ.im)
    push_cast at him ⊢
    nlinarith
  have hs := hS Z d hZ hd0 hd' hT hUS hU1 χ hχ a i ha ha' hmax j (U^tstar)
    r m ρ.re (2*Real.pi*ν-ρ.im) hQ (by positivity) hr hr' hm hm'
    (by simpa only [hJpow] using hD.le) hρ hρhi hfreq (hbudgetH d hd i hi)
    (by simpa only [hJpow,hKpow] using hprod)
  refine ⟨J,hJ,K,hK,ν,r,m,hν,heJ,heK,?_,hsupport.1,hm,hs.1,
    (by linarith [hsupport.2]),hs.2.1,hs.2.2⟩
  linarith [hsupport.2,hs.1]

theorem from_actual_maximum (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀≤Z → ∀ d : ℝ, dmin≤d → d≤dmax →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j, (χ j).residue≠1)
        (a : ℝ) (i : ℕ), i≤I → 51/100<a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
        a≤HeckeDetectorZeros.zeroMaximum χ hχ ((3*i : ℕ)*Z^τ) →
        (∀ j : ι, (χ j).modulus.absNorm≤Z^d) →
        ∀ tstar : ℝ, 1≤tstar → tstar≤3/2 →
        ∃ j : ι, ∃ ρ : ℂ, LFunction (χ j) ρ=0 ∧ a≤ρ.re ∧ |ρ.im|≤(3*i : ℕ)*Z^τ ∧
        ∃ J∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
          ∃ K∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
            ∃ ν r m : ℝ,
              ‖ν‖≤(Z^d)^(τ/(2*dmax)) ∧ (Z^d)^r=(2 : ℝ)^J ∧ (Z^d)^m=(2 : ℝ)^K ∧
              tstar-1/2-76*ε≤r ∧ r≤tstar+ε ∧ 0≤m ∧ m≤1/2+75*ε ∧ tstar-r-ε≤m ∧
              (Z^d)^((2*a-1)*r-2*ε)≤
                ‖polynomial (χ j) true
                  (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular ((Z^d)^tstar) ((Z^d)^r))
                  ((Z^d)^r) ρ.re (2*Real.pi*ν-ρ.im)‖^2 ∧
              (Z^d)^((2*a-1)*m-2*ε)≤
                ‖polynomial (χ j) false positiveAnnular ((Z^d)^m) ρ.re (2*Real.pi*ν-ρ.im)‖^2 := by
  obtain ⟨Z₀,hZ₀⟩ := from_actual_zero dmin dmax τ ε e κ η I hdmin hdmax hτ
    hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' ι _ χ hχ a i hi ha ha' hnext hcurrent hQ tstar ht ht'
  obtain ⟨j,ρ,hzero,him,heq⟩ := HeckeDetectorZeros.maximum_attained χ hχ
    ((3*i : ℕ)*Z^τ) (ha.trans_le hcurrent)
  have hρ : a≤ρ.re := by rw [heq]; exact hcurrent
  exact ⟨j,ρ,hzero,hρ,him,hZ₀ Z hZ d hd hd' χ hχ a i hi ha.le ha' hnext j
    (hQ j) ρ hzero hρ him tstar ht ht'⟩

end SevenEighths.HeckeDetectorSimultaneousSupport

end

end OAI
end OAIOriginalModule2068

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorSlotSelection
Source SHA256: 38f9b0897fec2028bd01afc2f8c04e3d49d7af056dbd22d1a376f2b69ff066ac
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2069


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorSlotSelection

theorem whole_slots {α : Type*} (s : Finset α) (w g : α→ℝ) (G mesh : ℝ)
    (hG : 0≤G) (hmesh : 0≤mesh)
    (hw : ∀ i∈s, 0≤w i) (hwm : ∀ i∈s, w i≤mesh)
    (hg : ∀ i∈s, 0≤g i) (hgG : ∀ i∈s, g i≤G)
    (q z : ℝ) (hq : 0≤q) (hqG : q≤G) (hz : 0≤z)
    (hzs : z≤∑ i∈s, w i) (hmean : q*(∑ i∈s, w i)≤∑ i∈s, w i*g i) :
    ∃ T : Finset α, T⊆s ∧ (∑ i∈T, w i)≤z ∧ q*z-G*mesh≤∑ i∈T, w i*g i := by
  classical
  induction s using Finset.strongInductionOn generalizing q z with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨a,ha,hmax⟩ := s.exists_max_image g hs
      by_cases hza : z≤w a
      · refine ⟨∅,Finset.empty_subset _,by simpa using hz,?_⟩
        have hzmesh : z≤mesh := hza.trans (hwm a ha)
        have hprod := mul_le_mul hqG hzmesh hz hG
        simpa only [Finset.sum_empty] using (sub_nonpos.mpr hprod)
      have haz : w a<z := lt_of_not_ge hza
      let s' := s.erase a
      have hss : s'⊂s := Finset.erase_ssubset ha
      have hsub : s'⊆s := Finset.erase_subset a s
      have hsum : ∑ i∈s, w i=w a+∑ i∈s', w i := by
        simpa [s',add_comm] using (Finset.sum_erase_add s w ha).symm
      have hgain : ∑ i∈s, w i*g i=w a*g a+∑ i∈s', w i*g i := by
        simpa [s',add_comm] using (Finset.sum_erase_add s (fun i => w i*g i) ha).symm
      let W := ∑ i∈s', w i
      let A := ∑ i∈s', w i*g i
      have hW : 0<W := by rw [hsum] at hzs; dsimp [W]; linarith
      have hA : 0≤A := Finset.sum_nonneg (fun i hi => mul_nonneg (hw i (hsub hi)) (hg i (hsub hi)))
      have hAg : A≤W*g a := by
        calc
          _ ≤ ∑ i∈s', w i*g a := Finset.sum_le_sum (fun i hi =>
            mul_le_mul_of_nonneg_left (hmax i (hsub hi)) (hw i (hsub hi)))
          _ = _ := by dsimp [W]; rw [Finset.sum_mul]
      let q' := A/W
      have hq' : 0≤q' := div_nonneg hA hW.le
      have hq'a : q'≤g a := (div_le_iff₀ hW).mpr (by simpa [mul_comm] using hAg)
      have hq'G : q'≤G := hq'a.trans (hgG a ha)
      have he : q'*W=A := div_mul_cancel₀ A hW.ne'
      have hz' : 0≤z-w a := sub_nonneg.mpr haz.le
      have hzs' : z-w a≤∑ i∈s', w i := by rw [hsum] at hzs; linarith
      obtain ⟨T,hTs,hTz,hTgain⟩ := ih s' hss
        (fun i hi => hw i (hsub hi)) (fun i hi => hwm i (hsub hi))
        (fun i hi => hg i (hsub hi)) (fun i hi => hgG i (hsub hi))
        q' (z-w a) hq' hq'G hz' hzs' he.le
      have haT : a∉T := fun h => (Finset.mem_erase.mp (hTs h)).1 rfl
      refine ⟨insert a T,Finset.insert_subset_iff.mpr ⟨ha,hTs.trans hsub⟩,?_,?_⟩
      · rw [Finset.sum_insert haT]
        linarith
      · rw [Finset.sum_insert haT]
        have hprefix : q*z≤w a*g a+q'*(z-w a) := by
          rw [hsum,hgain] at hmean
          change q*(w a+W)≤w a*g a+A at hmean
          rw [←he] at hmean
          by_cases hqq : q≤q'
          · have h1 := mul_le_mul_of_nonneg_right hqq hz
            have h2 := mul_le_mul_of_nonneg_left hq'a (hw a ha)
            nlinarith
          · have hqq' : 0≤q-q' := by linarith
            have h1 := mul_le_mul_of_nonneg_left hzs hqq'
            rw [hsum] at h1
            change (q-q')*z≤(q-q')*(w a+W) at h1
            nlinarith
        linarith
    · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      have hz0 : z=0 := by simpa using le_antisymm hzs hz
      refine ⟨∅,Finset.empty_subset _,by simpa using hz,?_⟩
      simp only [Finset.sum_empty,hz0,mul_zero,zero_sub]
      exact neg_nonpos.mpr (mul_nonneg hG hmesh)

theorem whole_positive_slots {α : Type*} (s : Finset α) (w g : α→ℝ) (G mesh : ℝ)
    (hG : 0≤G) (hmesh : 0≤mesh)
    (hw : ∀ i∈s, 0≤w i) (hwm : ∀ i∈s, w i≤mesh)
    (hgG : ∀ i∈s, g i≤G)
    (q z : ℝ) (hq : 0≤q) (hqG : q≤G) (hz : 0≤z)
    (hzs : z≤∑ i∈s, w i) (hmean : q*(∑ i∈s, w i)≤∑ i∈s, w i*max (g i) 0) :
    ∃ T : Finset α, T⊆s ∧ (∀ i∈T, 0<g i) ∧
      (∑ i∈T, w i)≤z ∧ q*z-G*mesh≤∑ i∈T, w i*g i := by
  classical
  obtain ⟨T,hTs,hTz,hTgain⟩ := whole_slots s w (fun i => max (g i) 0) G mesh hG hmesh
    hw hwm (fun i hi => le_max_right _ _) (fun i hi => max_le (hgG i hi) hG)
    q z hq hqG hz hzs hmean
  let P := T.filter (fun i => 0<g i)
  have hPT : P⊆T := Finset.filter_subset _ _
  refine ⟨P,hPT.trans hTs,fun i hi => (Finset.mem_filter.mp hi).2,?_,?_⟩
  · exact (Finset.sum_le_sum_of_subset_of_nonneg hPT (fun i hi _ => hw i (hTs hi))).trans hTz
  · have he : (∑ i∈T, w i*max (g i) 0)=∑ i∈P, w i*g i := by
      calc
        _ = ∑ i∈P, w i*max (g i) 0 := by
          symm
          apply Finset.sum_subset hPT
          intro i hi hn
          have hg : g i≤0 := le_of_not_gt (fun h => hn (Finset.mem_filter.mpr ⟨hi,h⟩))
          rw [max_eq_right hg,mul_zero]
        _ = _ := Finset.sum_congr rfl (fun i hi => by
          rw [max_eq_left (Finset.mem_filter.mp hi).2.le])
    rwa [he] at hTgain

theorem selected_product_spike {α : Type*} (s : Finset α) (w g : α→ℝ)
    (U δ mesh q z : ℝ) (hU : 1≤U) (hδ : 0≤δ) (hmesh : 0≤mesh)
    (hw : ∀ i∈s, 0≤w i) (hwm : ∀ i∈s, w i≤mesh)
    (hg : ∀ i∈s, g i≤δ/2) (hq : 0≤q) (hqδ : q≤δ/2) (hz : 0≤z)
    (hzs : z≤∑ i∈s, w i) (hmean : q*(∑ i∈s, w i)≤∑ i∈s, w i*max (g i) 0)
    : ∃ T : Finset α, T⊆s ∧ (∀ i∈T, 0<g i) ∧ (∑ i∈T, w i)≤z ∧
      ∀ Q : α→ℂ, (∀ i∈s, 0<g i → U^(2*w i*g i)≤‖Q i‖^2) →
        U^(2*q*z-δ*mesh)≤‖∏ i∈T, Q i‖^2 := by
  obtain ⟨T,hTs,hTpos,hTz,hgain⟩ := whole_positive_slots s w g (δ/2) mesh
    (by positivity) hmesh hw hwm hg q z hq hqδ hz hzs hmean
  refine ⟨T,hTs,hTpos,hTz,?_⟩
  intro Q hQ
  have hUp : 0<U := by linarith
  calc
    _ ≤ U^(∑ i∈T, 2*w i*g i) := Real.rpow_le_rpow_of_exponent_le hU (by
      have he : (∑ i∈T, 2*w i*g i)=2*(∑ i∈T, w i*g i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [he]
      linarith)
    _ = ∏ i∈T, U^(2*w i*g i) := Real.rpow_sum_of_pos hUp _ _
    _ ≤ ∏ i∈T, ‖Q i‖^2 := Finset.prod_le_prod₀ (fun i hi => Real.rpow_nonneg hUp.le _)
      (fun i hi => hQ i (hTs hi) (hTpos i hi))
    _ = _ := by rw [norm_prod,Finset.prod_pow]

theorem selected_product_with_decrement {α : Type*} (s : Finset α) (w g : α→ℝ)
    (U δ mesh q z ν : ℝ) (hU : 1≤U) (hδ : 0≤δ) (hmesh : 0≤mesh)
    (hw : ∀ i∈s, 0≤w i) (hwm : ∀ i∈s, w i≤mesh)
    (hg : ∀ i∈s, g i≤δ/2) (hq : 0≤q) (hqδ : q≤δ/2) (hz : 0≤z) (hν : 0≤ν)
    (hzs : z≤∑ i∈s, w i) (hmean : q*(∑ i∈s, w i)≤∑ i∈s, w i*max (g i) 0) :
    ∃ T : Finset α, T⊆s ∧ (∀ i∈T, 0<g i) ∧
      (∑ i∈T, w i)≤max 0 (z-ν) ∧
      ∀ Q : α→ℂ, (∀ i∈s, 0<g i → U^(2*w i*g i)≤‖Q i‖^2) →
        U^(2*q*z-2*q*ν-δ*mesh)≤‖∏ i∈T, Q i‖^2 := by
  have hcap : max 0 (z-ν)≤z := max_le hz (by linarith)
  obtain ⟨T,hTs,hTp,hTw,hTb⟩ := selected_product_spike s w g U δ mesh q (max 0 (z-ν))
    hU hδ hmesh hw hwm hg hq hqδ (le_max_left _ _) (hcap.trans hzs) hmean
  refine ⟨T,hTs,hTp,hTw,?_⟩
  intro Q hQ
  apply le_trans _ (hTb Q hQ)
  apply Real.rpow_le_rpow_of_exponent_le hU
  have hh := mul_le_mul_of_nonneg_left (le_max_right 0 (z-ν)) (show 0≤2*q by positivity)
  nlinarith

end SevenEighths.HeckeDetectorSlotSelection

end

end OAI
end OAIOriginalModule2069

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorWitnessRows
Source SHA256: fb3f851ef3d6f4a260a584bf5511fe09704dad364da6f1f2bdf4c4fe7720d15b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2070


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorWitnessRows
open HeckeFamily HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles

def dyadicLength (U : ℝ) : ℕ := HeckeDetectorPartition.length (⌈2*U^21⌉₊ : ℝ)+1

structure Witness {ι : Type*} (χ : ι→Character) (U a ε tstar T allowance : ℝ) (i : ℕ) where
  label : ι
  zero : ℂ
  zero_eq : LFunction (χ label) zero=0
  zero_lower : a≤zero.re
  zero_height : |zero.im|≤(3*i : ℕ)*T
  left : Fin (dyadicLength U)
  right : Fin (dyadicLength U)
  nu : ℝ
  r : ℝ
  m : ℝ
  nu_bound : ‖nu‖≤allowance
  left_scale : U^r=(2 : ℝ)^left.val
  right_scale : U^m=(2 : ℝ)^right.val
  inverse_length_lower : tstar-1/2-76*ε≤r
  inverse_length_upper : r≤tstar+ε
  plain_length_lower : 0≤m
  plain_length_upper : m≤1/2+75*ε
  inverse_spike : U^((2*a-1)*r-2*ε)≤
    ‖polynomial (χ label) true
      (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular (U^tstar) (U^r))
      (U^r) zero.re (2*Real.pi*nu-zero.im)‖^2
  plain_spike : U^((2*a-1)*m-2*ε)≤
    ‖polynomial (χ label) false positiveAnnular (U^m) zero.re (2*Real.pi*nu-zero.im)‖^2

def Witness.frequency {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) : ℝ := 2*Real.pi*w.nu-w.zero.im

theorem Witness.frequency_bound {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) :
    |w.frequency|≤2*Real.pi*allowance+(3*i : ℕ)*T := by
  have hnu : |w.nu|≤allowance := by simpa only [Real.norm_eq_abs] using w.nu_bound
  have hh := abs_sub_le (2*Real.pi*w.nu) 0 w.zero.im
  simp only [sub_zero,zero_sub,abs_neg,abs_mul,
    abs_of_pos (show 0<2*Real.pi by positivity)] at hh
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hnu (by positivity)) w.zero_height)

theorem Witness.real_part_upper {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) : w.zero.re≤1 := by
  by_contra hn
  exact LFunction_ne_zero_of_one_lt_re (χ w.label) (lt_of_not_ge hn) w.zero_eq

theorem Witness.left_exponent {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) (hU : 1<U) :
    w.r=Real.logb U ((2 : ℝ)^w.left.val) := by
  rw [←w.left_scale,Real.logb_rpow (zero_lt_one.trans hU) hU.ne']

theorem Witness.right_exponent {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) (hU : 1<U) :
    w.m=Real.logb U ((2 : ℝ)^w.right.val) := by
  rw [←w.right_scale,Real.logb_rpow (zero_lt_one.trans hU) hU.ne']

theorem exists_from_maximum (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀≤Z → ∀ d : ℝ, dmin≤d → d≤dmax →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j,(χ j).residue≠1)
        (a : ℝ) (i : ℕ), i≤I → 51/100<a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*Z^τ)<a+2*e →
        a≤HeckeDetectorZeros.zeroMaximum χ hχ ((3*i : ℕ)*Z^τ) →
        (∀ j,(χ j).modulus.absNorm≤Z^d) →
        ∀ tstar : ℝ, 1≤tstar → tstar≤3/2 →
          Nonempty (Witness χ (Z^d) a ε tstar (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z₀,hZ₀⟩ := HeckeDetectorSimultaneous.from_actual_maximum dmin dmax τ ε e κ η I
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' ι _ χ hχ a i hi ha ha' hnext hcurrent hQ tstar ht ht'
  obtain ⟨j,ρ,hzero,hρ,hheight,J,hJ,K,hK,nu,r,m,hnu,hleft,hright,hr,hr',hm,hm',hM,hS⟩ :=
    hZ₀ Z hZ d hd hd' χ hχ a i hi ha ha' hnext hcurrent hQ tstar ht ht'
  exact ⟨⟨j,ρ,hzero,hρ,hheight,⟨J,Finset.mem_range.mp hJ⟩,⟨K,Finset.mem_range.mp hK⟩,
    nu,r,m,hnu,hleft,hright,hr,hr',hm,hm',hM,hS⟩⟩

end SevenEighths.HeckeDetectorWitnessRows

end

end OAI
end OAIOriginalModule2070

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorDynamicSelection
Source SHA256: 46cd5eddb45bff5314458f1ea249763136afd25d24482772b6fc68f0f04ea3ee
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2071


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorDynamicSelection
open HeckeFamily HeckeDetectorWitnessRows

theorem actual_witness_family (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀≤Z → ∀ d : ℝ, dmin≤d → d≤dmax →
      ∀ {Row Label : Type*} [Fintype Label] (χ : Row→Label→Character)
        (hχ : ∀ u j,(χ u j).residue≠1) (a : ℝ) (i : ℕ), i≤I → 51/100<a → a≤1 →
        (∀ u, HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) (3*(i+1 : ℕ)*Z^τ)<a+2*e) →
        (∀ u, a≤HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) ((3*i : ℕ)*Z^τ)) →
        (∀ u j,(χ u j).modulus.absNorm≤Z^d) →
        ∀ tstar : ℝ, 1≤tstar → tstar≤3/2 →
          Nonempty (∀ u,Witness (χ u) (Z^d) a ε tstar (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z₀,hZ₀⟩ := exists_from_maximum dmin dmax τ ε e κ η I hdmin hdmax hτ
    hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' Row Label _ χ hχ a i hi ha ha' hnext hcurrent hQ tstar ht ht'
  exact ⟨fun u => Classical.choice (hZ₀ Z hZ d hd hd' (χ u) (hχ u) a i hi ha ha'
    (hnext u) (hcurrent u) (hQ u) tstar ht ht')⟩

def fiber {Row Label : Type*} (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U)) : Finset Row :=
  rows.filter (fun u => (w u).label=label ∧ (w u).left=J ∧ (w u).right=K)

theorem card_eq_sum_fibers {Row Label : Type*} [Fintype Label]
    (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,Witness (χ u) U a ε tstar T allowance i) :
    rows.card=∑ label : Label, ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
      (fiber rows χ U a ε tstar T allowance i w label J K).card := by
  have hh := Finset.card_eq_sum_card_fiberwise (s:=rows) (t:=Finset.univ)
    (f:=fun u => ((w u).label,(w u).left,(w u).right))
    (by intro u hu; exact Finset.mem_univ _)
  simpa only [Fintype.sum_prod_type,Prod.mk.injEq,fiber] using hh

end SevenEighths.HeckeDetectorDynamicSelection

end

end OAI
end OAIOriginalModule2071

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorSupportedWitness
Source SHA256: b1bd8fc046e2adf721bd06c8c9c206a0f19f02637668e8206d235739f03917e5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2072



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorSupportedWitness
open HeckeFamily HeckeDetectorWitnessRows

structure SupportedWitness {Label : Type*} (χ : Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    extends Witness χ U a ε tstar T allowance i where
  product_length_lower : tstar-r-ε≤m

theorem actual_supported_witness_family (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ,∀ Z : ℝ,Z₀≤Z → ∀ d : ℝ,dmin≤d → d≤dmax →
      ∀ {Row Label : Type*} [Fintype Label] (χ : Row→Label→Character)
        (hχ : ∀ u j,(χ u j).residue≠1) (a : ℝ) (i : ℕ),i≤I → 51/100<a → a≤1 →
        (∀ u,HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) (3*(i+1 : ℕ)*Z^τ)<a+2*e) →
        (∀ u,a≤HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) ((3*i : ℕ)*Z^τ)) →
        (∀ u j,(χ u j).modulus.absNorm≤Z^d) →
        ∀ tstar : ℝ,1≤tstar → tstar≤3/2 →
          Nonempty (∀ u,SupportedWitness (χ u) (Z^d) a ε tstar (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z₀,hZ₀⟩ := HeckeDetectorSimultaneousSupport.from_actual_maximum dmin dmax τ ε e κ η I
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' Row Label _ χ hχ a i hi ha ha' hnext hcurrent hQ tstar ht ht'
  have hw (u : Row) : Nonempty (SupportedWitness (χ u) (Z^d) a ε tstar (Z^τ)
      ((Z^d)^(τ/(2*dmax))) i) := by
    obtain ⟨j,ρ,hzero,hρ,hheight,J,hJ,K,hK,nu,r,m,hnu,hleft,hright,hr,hr',hm,hm',hprod,hM,hS⟩ :=
      hZ₀ Z hZ d hd hd' (χ u) (hχ u) a i hi ha ha' (hnext u) (hcurrent u) (hQ u) tstar ht ht'
    exact ⟨⟨⟨j,ρ,hzero,hρ,hheight,⟨J,Finset.mem_range.mp hJ⟩,⟨K,Finset.mem_range.mp hK⟩,
      nu,r,m,hnu,hleft,hright,hr,hr',hm,hm',hM,hS⟩,hprod⟩⟩
  exact ⟨fun u => Classical.choice (hw u)⟩

theorem fiber_lengths {Row Label : Type*} (rows : Finset Row) (hne : rows.Nonempty)
    (χ : Row→Label→Character) (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (J K : Fin (dyadicLength U))
    (hJ : ∀ u∈rows,(w u).left=J) (hK : ∀ u∈rows,(w u).right=K) :
    let r := Real.logb U ((2 : ℝ)^J.val)
    let m := Real.logb U ((2 : ℝ)^K.val)
    tstar-r-ε≤m ∧ r≤tstar+ε ∧ m≤1/2+75*ε ∧ tstar-1/2-76*ε≤r ∧ 0≤m := by
  obtain ⟨u,hu⟩ := hne
  have hr : (w u).r=Real.logb U ((2 : ℝ)^J.val) := by
    rw [(w u).toWitness.left_exponent hU,hJ u hu]
  have hm : (w u).m=Real.logb U ((2 : ℝ)^K.val) := by
    rw [(w u).toWitness.right_exponent hU,hK u hu]
  exact hr ▸ hm ▸ ⟨(w u).product_length_lower,(w u).inverse_length_upper,
    (w u).plain_length_upper,(w u).inverse_length_lower,(w u).plain_length_lower⟩

end SevenEighths.HeckeDetectorSupportedWitness

end

end OAI
end OAIOriginalModule2072

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorAdaptiveCutoff
Source SHA256: 494cc048ad3438976fcab45b364e3c2828e51cdaee3aa2eac00268119514f92a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2073



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorAdaptiveCutoff
open HeckeFamily HeckeDetectorSupportedWitness HeckeDetectorRowCount

def cutoff (δ q : ℝ) : ℝ :=
  if δ≤5/6 then Endpoint.balancedCutoff δ (1/2-min (1/2) (max 0 (q/δ))) else 3/2

theorem cutoff_bounds (δ q : ℝ) (hδ : 0≤δ) : 1≤cutoff δ q ∧ cutoff δ q≤3/2 := by
  unfold cutoff
  split_ifs with hd
  · exact balanced_cutoff_bounds hδ hd (le_min (by norm_num) (le_max_left _ _)) (min_le_left _ _)
  · norm_num

theorem cutoff_eq_balanced (δ q : ℝ) (hδ : 0<δ) (hd : δ≤5/6)
    (hq : 0≤q) (hq' : q≤δ/2) :
    cutoff δ q=Endpoint.balancedCutoff δ (1/2-q/δ) := by
  have hx : 0≤q/δ := div_nonneg hq hδ.le
  have hx' : q/δ≤1/2 := (div_le_iff₀ hδ).mpr (by linarith)
  simp only [cutoff,ite_eq_left hd,max_eq_right hx,min_eq_right hx']

theorem cutoff_eq_high (δ q : ℝ) (hδ : 5/6<δ) : cutoff δ q=3/2 := by
  simp only [cutoff,ite_eq_right (not_le_of_gt hδ)]

theorem actual_adaptive_witnesses (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ,∀ Z : ℝ,Z₀≤Z → ∀ d : ℝ,dmin≤d → d≤dmax →
      ∀ {Row Label : Type*} [Fintype Label] (χ : Row→Label→Character)
        (hχ : ∀ u j,(χ u j).residue≠1) (a : ℝ) (i : ℕ),i≤I → 51/100<a → a≤1 →
        (∀ u,HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) (3*(i+1 : ℕ)*Z^τ)<a+2*e) →
        (∀ u,a≤HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) ((3*i : ℕ)*Z^τ)) →
        (∀ u j,(χ u j).modulus.absNorm≤Z^d) → ∀ q : Row→ℝ,
          Nonempty (∀ u,SupportedWitness (χ u) (Z^d) a ε (cutoff (2*a-1) (q u))
            (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z₀,hZ₀⟩ := actual_supported_witness_family dmin dmax τ ε e κ η I hdmin hdmax hτ
    hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' Row Label _ χ hχ a i hi ha ha' hnext hcurrent hQ q
  have hδ : 0≤2*a-1 := by linarith
  exact ⟨fun u => (Classical.choice (hZ₀ Z hZ d hd hd' χ hχ a i hi ha ha'
    hnext hcurrent hQ (cutoff (2*a-1) (q u))
      (cutoff_bounds (2*a-1) (q u) hδ).1 (cutoff_bounds (2*a-1) (q u) hδ).2)) u⟩

end SevenEighths.HeckeDetectorAdaptiveCutoff

end

end OAI
end OAIOriginalModule2073

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationScale
Source SHA256: 8960ab7f090f31a1d0d67fdd84c449c767380134deb74a5486696389b5852c60
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2074



namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge HeckeDetectorRowwise

def scaleProfile (W : ℝ→ℂ) (y : ℝ) : ℂ := -W y/2-(y : ℂ)*deriv W y

def scaleSum (χ : Character) (W : ℝ→ℂ) (S : Finset (Ideal O)) (l : ℝ) : ℂ :=
  Complex.exp (-(l : ℂ)/2)*∑ J∈S,
    coefficient χ true J*W ((J.absNorm : ℝ)*Real.exp (-l))

theorem scaleProfile_continuous (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) :
    Continuous (scaleProfile W) := by
  have hd := hW.continuous_deriv (by simp)
  unfold scaleProfile
  fun_prop

theorem scaleProfile_support (W : ℝ→ℂ) (a b : ℝ)
    (hs : Function.support W⊆Icc a b) : Function.support (scaleProfile W)⊆Icc a b := by
  intro y hy
  by_contra hn
  have hw : W y=0 := by by_contra hw; exact hn (hs hw)
  have hd : deriv W y=0 := by
    apply deriv_of_notMem_tsupport
    exact fun h => hn ((closure_minimal hs isClosed_Icc) h)
  exact hy (by simp [scaleProfile,hw,hd])

theorem scaleSum_continuous (χ : Character) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (hW : Continuous W) : Continuous (scaleSum χ W S) := by
  unfold scaleSum
  fun_prop

theorem scaleSum_deriv (χ : Character) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (hW : Differentiable ℝ W) (l : ℝ) :
    HasDerivAt (scaleSum χ W S) (scaleSum χ (scaleProfile W) S l) l := by
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ)/2))
      (Complex.exp (-(l : ℂ)/2)*(-(1 : ℂ)/2)) l := by
    convert ((Complex.ofRealCLM.hasDerivAt (x:=l)).neg.div_const (2 : ℂ)).cexp using 1
    all_goals rfl
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun t => coefficient χ true J*W ((J.absNorm : ℝ)*Real.exp (-t)))
        (coefficient χ true J*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))) l := by
    have hy := ((hasDerivAt_id l).neg.exp).const_mul (J.absNorm : ℝ)
    convert ((hW _).hasDerivAt.scomp l hy).const_mul (coefficient χ true J) using 1
    · rfl
    · change coefficient χ true J*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))=
        coefficient χ true J*(((J.absNorm : ℝ)*(Real.exp (-l)*(-1))) •
          deriv W ((J.absNorm : ℝ)*Real.exp (-l)))
      rw [Complex.real_smul]
      push_cast
      ring
  convert hE.mul (HasDerivAt.sum (u:=S) hd) using 1
  · ext t
    simp only [scaleSum,Pi.mul_apply,Finset.sum_apply]
  · dsimp [scaleSum,scaleProfile]
    simp only [Finset.sum_apply]
    simp_rw [Finset.mul_sum]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    push_cast
    ring

theorem scale_normalization (l : ℝ) :
    ((Real.exp l : ℝ) : ℂ)^(-(1/2 : ℂ))=Complex.exp (-(l : ℂ)/2) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos l).ne'),
    ←Complex.ofReal_log (Real.exp_pos l).le,Real.log_exp]
  congr 1
  ring

theorem scaleSum_eq_polynomial (χ : Character) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (l : ℝ) (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈S) :
    scaleSum χ W S l=polynomial χ true W (Real.exp l) 0 0 := by
  rw [polynomial_eq_finite χ true W (Real.exp l) 0 0 S hc,scale_normalization]
  simp only [HeckeDyadic.shift,ofReal_zero,zero_mul,sub_self,neg_zero,Complex.cpow_zero,mul_one]
  unfold scaleSum
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Real.exp_neg,div_eq_mul_inv]

end SevenEighths.HeckeInverseAmplification

end

end OAI
end OAIOriginalModule2074

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationConjugation
Source SHA256: 9ca4335527c05e335587d807b24d3600f28477744ffb28f63174eb386af2aeac
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2075




namespace OAI

noncomputable section
open scoped Classical ComplexConjugate ContDiff
open Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem coefficient_inverse_conj (χ : Character) (inv : Bool) (J : Ideal O) :
    coefficient χ.inverse inv J=conj (coefficient χ inv J) := by
  cases inv <;> simp [coefficient,idealCoeff_inverse_conj]

theorem conj_positive_cpow (x : ℝ) (hx : 0<x) (z : ℂ) :
    conj ((x : ℂ)^z)=(x : ℂ)^(conj z) := by
  have hh := Complex.cpow_conj (x : ℂ) z
    (by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm)
  simpa only [conj_ofReal] using hh.symm

theorem conj_shift (σ freq : ℝ) : conj (shift σ freq)=shift σ (-freq) := by
  simp only [HeckeDyadic.shift,map_sub,map_mul,conj_ofReal,conj_I,ofReal_neg]
  ring

theorem conj_polynomial (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) :
    conj (polynomial χ inv W D σ freq)=
      polynomial χ.inverse inv (fun x => conj (W x)) D σ (-freq) := by
  unfold polynomial
  rw [map_mul,conj_tsum,conj_positive_cpow D hD]
  have hhalf : conj (-(1/2 : ℂ))= -(1/2 : ℂ) := by
    simp only [map_neg,map_div₀,map_one,map_ofNat]
  rw [hhalf]
  congr 1
  apply tsum_congr
  intro J
  simp only [summand,map_mul,←coefficient_inverse_conj]
  rw [conj_positive_cpow _ (div_pos (norm_pos J) hD),map_neg,conj_shift]

theorem polynomial_inverse_norm (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial χ.inverse inv (fun x => conj (W x)) D σ (-freq)‖=
      ‖polynomial χ inv W D σ freq‖ := by
  rw [←conj_polynomial χ inv W D σ freq hD,norm_conj]

theorem conjugate_profile_support (W : ℝ→ℂ) :
    Function.support (fun x => conj (W x))=Function.support W := by
  ext x
  simp

theorem conjugate_profile_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (fun x => conj (W x)) := by
  exact Complex.conjCLE.contDiff.comp hW

theorem scaleProfile_conjugate (W : ℝ→ℂ) (x : ℝ) :
    scaleProfile (fun y => conj (W y)) x=conj (scaleProfile W x) := by
  have hd : deriv (fun y => conj (W y)) x=conj (deriv W x) := by
    simpa only [star_def] using (deriv.star (f:=W) (x:=x))
  simp only [scaleProfile,hd,map_sub,map_div₀,map_neg,map_mul,conj_ofReal,map_ofNat]

theorem logProfile_conjugate (W : ℝ→ℂ) (x : ℝ) :
    HeckeDetectorRowwisePolynomial.logProfile (fun y => conj (W y)) x=
      conj (HeckeDetectorRowwisePolynomial.logProfile W x) := by
  simp only [HeckeDetectorRowwisePolynomial.logProfile,map_mul,conj_ofReal]

end SevenEighths.HeckeInverseAmplification

end

end OAI
end OAIOriginalModule2075

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorCoefficientTransfer
Source SHA256: 7a9d7381e364c5dcf8189d1f2b3b61b40d75de1a5a7a45b4ba2e44a859f0adbd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2076


namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
open Complex
namespace SevenEighths.HeckeDetectorCoefficientTransfer
open HeckeFamily HeckeDyadic HeckeInverseAmplification

theorem polynomial_eq_of_idealCoeff (χ ψ : Character)
    (hc : ∀ J : Ideal O,idealCoeff χ J=idealCoeff ψ J)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) :
    polynomial χ inv W D σ freq=polynomial ψ inv W D σ freq := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  simp only [summand,coefficient,hc]

def orientedProfile (reverse : Bool) (W : ℝ→ℂ) : ℝ→ℂ :=
  if reverse then fun x => conj (W x) else W

def orientedFrequency (reverse : Bool) (freq : ℝ) : ℝ := if reverse then -freq else freq

theorem norm_of_oriented_coefficients (χ ψ : Character) (reverse : Bool)
    (hc : ∀ J : Ideal O,idealCoeff χ J=
      if reverse then conj (idealCoeff ψ J) else idealCoeff ψ J)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial χ inv W D σ freq‖=
      ‖polynomial ψ inv (orientedProfile reverse W) D σ (orientedFrequency reverse freq)‖ := by
  cases reverse
  · exact congrArg (fun z : ℂ => ‖z‖) (polynomial_eq_of_idealCoeff χ ψ hc inv W D σ freq)
  · have hc' : ∀ J : Ideal O,idealCoeff χ J=idealCoeff ψ.inverse J := by
      intro J
      simpa only [Bool.true_eq,ite_true,idealCoeff_inverse_conj] using hc J
    rw [polynomial_eq_of_idealCoeff χ ψ.inverse hc' inv W D σ freq]
    have hh := polynomial_inverse_norm ψ inv (fun x => conj (W x)) D σ (-freq) hD
    simpa only [orientedProfile,orientedFrequency,Bool.true_eq,ite_true,conj_conj,neg_neg] using hh

theorem orientedFrequency_abs (reverse : Bool) (freq : ℝ) :
    |orientedFrequency reverse freq|=|freq| := by cases reverse <;> simp [orientedFrequency]

end SevenEighths.HeckeDetectorCoefficientTransfer

end

end OAI
end OAIOriginalModule2076

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationScaleSup
Source SHA256: 3bb1b731ea80b8899c1980c48cc2a0f6be279511ac7825beddc1674ec5296529
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2077


namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeDetectorRowwise
open ConcretePrimeRowBridge hiding O

def scaleSupport (upper b : ℝ) : Finset (Ideal O) := idealsUpTo ⌈Real.exp upper*b⌉₊

theorem scaleSupport_cover (W : ℝ→ℂ) (a b upper l : ℝ) (hb : 0≤b)
    (hWs : Function.support W⊆Icc a b) (hl : l≤upper) :
    ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈scaleSupport upper b := by
  intro J hJ hw
  apply mem_idealsUpTo.mpr
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ),?_⟩
  have hh := (div_le_iff₀ (Real.exp_pos l)).mp (hWs hw).2
  have hm := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hl) hb
  have hn : (J.absNorm : ℝ)≤Real.exp upper*b := by nlinarith
  exact_mod_cast hn.trans (Nat.le_ceil _)

theorem rowwise_scales {ι : Type*} (rows : Finset ι) (χ : ι→Character)
    (W : ℝ→ℂ) (a b : ℝ) (hb : 0≤b) (hWs : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (lo hi E : ℝ) (hlh : lo≤hi) (l : ι→ℝ)
    (hl : ∀ i∈rows, l i∈Icc lo hi)
    (h0 : ∀ t∈Icc lo hi, ∑ i∈rows, ‖polynomial (χ i) true W (Real.exp t) 0 0‖^2≤E)
    (h1 : ∀ t∈Icc lo hi, ∑ i∈rows,
      ‖polynomial (χ i) true (scaleProfile W) (Real.exp t) 0 0‖^2≤E) :
    ∑ i∈rows, ‖polynomial (χ i) true W (Real.exp (l i)) 0 0‖^2≤(1+2*(hi-lo))*E := by
  let S := scaleSupport hi b
  have hsp := scaleProfile_support W a b hWs
  have eq0 (i : ι) (t : ℝ) (ht : t∈Icc lo hi) :=
    scaleSum_eq_polynomial (χ i) W S t (scaleSupport_cover W a b hi t hb hWs ht.2)
  have eq1 (i : ι) (t : ℝ) (ht : t∈Icc lo hi) :=
    scaleSum_eq_polynomial (χ i) (scaleProfile W) S t
      (scaleSupport_cover (scaleProfile W) a b hi t hb hsp ht.2)
  have hh := rowwise_energy rows (fun i => scaleSum (χ i) W S)
    (fun i => scaleSum (χ i) (scaleProfile W) S)
    (fun i hi => scaleSum_continuous (χ i) W S hW.continuous)
    (fun i hi => scaleSum_continuous (χ i) (scaleProfile W) S (scaleProfile_continuous W hW))
    (fun i hi t => scaleSum_deriv (χ i) W S (hW.differentiable (by simp)) t)
    lo hi E hlh l hl
    (fun t ht => by simpa only [eq0 _ t ht] using h0 t ht)
    (fun t ht => by simpa only [eq1 _ t ht] using h1 t ht)
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [eq0 i (l i) (hl i hi)]

theorem exists_scale_majorant {ι : Type*} (rows : Finset ι) (χ : ι→Character)
    (W : ℝ→ℂ) (a b : ℝ) (hb : 0≤b) (hWs : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (lo hi E : ℝ) (hlh : lo≤hi)
    (h0 : ∀ t∈Icc lo hi, ∑ i∈rows, ‖polynomial (χ i) true W (Real.exp t) 0 0‖^2≤E)
    (h1 : ∀ t∈Icc lo hi, ∑ i∈rows,
      ‖polynomial (χ i) true (scaleProfile W) (Real.exp t) 0 0‖^2≤E) :
    ∃ B : ι→ℝ, (∀ i, 0≤B i) ∧
      (∀ i, ∀ t∈Icc lo hi, ‖polynomial (χ i) true W (Real.exp t) 0 0‖^2≤B i) ∧
      (∑ i∈rows, B i)≤(1+2*(hi-lo))*E := by
  let S := scaleSupport hi b
  have hm (i : ι) : ∃ t∈Icc lo hi, ∀ u∈Icc lo hi,
      ‖scaleSum (χ i) W S u‖^2≤‖scaleSum (χ i) W S t‖^2 := by
    exact isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hlh)
      ((scaleSum_continuous (χ i) W S hW.continuous).norm.pow 2).continuousOn
  choose t ht hmax using hm
  refine ⟨fun i => ‖polynomial (χ i) true W (Real.exp (t i)) 0 0‖^2,
    fun i => sq_nonneg _,?_,?_⟩
  · intro i u hu
    have hh := hmax i u hu
    rw [scaleSum_eq_polynomial (χ i) W S u (scaleSupport_cover W a b hi u hb hWs hu.2),
      scaleSum_eq_polynomial (χ i) W S (t i) (scaleSupport_cover W a b hi (t i) hb hWs (ht i).2)] at hh
    exact hh
  · exact rowwise_scales rows χ W a b hb hWs hW lo hi E hlh t (fun i hi => ht i) h0 h1

theorem polynomial_zero_small_scale (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (a b D σ freq : ℝ) (hD : 0<D) (hs : Function.support W⊆Icc a b)
    (hsmall : D*b<1) : polynomial χ inv W D σ freq=0 := by
  unfold polynomial
  suffices hh : (∑' J : HeckeDyadic.NonzeroIdeal, summand χ inv W D σ freq J)=0 by
    rw [hh,mul_zero]
  have hz : ∀ J : HeckeDyadic.NonzeroIdeal, summand χ inv W D σ freq J=0 := by
    intro J
    have hw : W (norm J/D)=0 := by
      by_contra hn
      have hb := (div_le_iff₀ hD).mp (hs hn).2
      have hN : 1≤norm J := by
        change (1 : ℝ) ≤ (J.val.absNorm : ℝ)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr J.property)
      nlinarith
    simp only [summand,hw,mul_zero,zero_mul]
  simp only [hz,tsum_zero]

end SevenEighths.HeckeInverseAmplification

end

end OAI
end OAIOriginalModule2077

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationAggregate
Source SHA256: 852cb55e661ce0a465e310b20c73f05e9909d37c68ee118c5d15d088b6f9e836
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2078



namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic
abbrev PrimeIdeal := SmoothMobiusCorrection.PrimeIdeal

def primeRowMap (p : FreeRow×PrimeIdeal) : NonzeroElement :=
  amplifiedElement ⟨p.1.val,p.1.property.1⟩ ⟨p.2.val,p.2.property.ne_zero⟩

theorem primeRowMap_injective : Function.Injective primeRowMap := by
  intro p q hpq
  have he : rowMap (p.1,⟨p.2.val,p.2.property.ne_zero⟩)=
      rowMap (q.1,⟨q.2.val,q.2.property.ne_zero⟩) := congrArg Subtype.val hpq
  have hh := rowMap_injective he
  apply Prod.ext
  · exact congrArg (fun r : FreeRow×NonzeroIdeal => r.1) hh
  · apply Subtype.ext
    exact congrArg (fun r : FreeRow×NonzeroIdeal => r.2.val) hh

theorem primeRowMap_norm_bound (p : FreeRow×PrimeIdeal) (U V : ℝ)
    (hU : (Ideal.span {p.1.val}).absNorm≤U) (hV : (p.2.val.absNorm : ℝ)≤V) :
    ((Ideal.span {((primeRowMap p).val)}).absNorm : ℝ)≤U*V^6 := by
  have hn := rowMap_norm (p.1,⟨p.2.val,p.2.property.ne_zero⟩)
  change ((Ideal.span {rowMap (p.1,⟨p.2.val,p.2.property.ne_zero⟩)}).absNorm : ℝ)≤_
  rw [hn,Nat.cast_mul,Nat.cast_pow]
  exact mul_le_mul hU (pow_le_pow_left₀ (Nat.cast_nonneg _) hV 6)
    (by positivity) ((Nat.cast_nonneg _).trans hU)

theorem averaged_energy (data : RowData) (rows : Finset FreeRow) (primes : Finset PrimeIdeal)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hb : 0≤b)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D U V E : ℝ) (hD : 0<D) (hV : 1≤V)
    (hrows : ∀ u∈rows, ((Ideal.span {u.val}).absNorm : ℝ)≤U)
    (hprimes : ∀ P∈primes, (P.val.absNorm : ℝ)≤V)
    (hraw0 : ∀ R : Finset NonzeroElement,
      (∀ v∈R, ((Ideal.span {v.val}).absNorm : ℝ)≤U*V^6) →
      ∀ l∈Icc (Real.log D-Real.log V) (Real.log D),
      ∑ v∈R, ‖polynomial (data.character v) true W (Real.exp l) 0 0‖^2≤E)
    (hraw1 : ∀ R : Finset NonzeroElement,
      (∀ v∈R, ((Ideal.span {v.val}).absNorm : ℝ)≤U*V^6) →
      ∀ l∈Icc (Real.log D-Real.log V) (Real.log D),
      ∑ v∈R, ‖polynomial (data.character v) true (scaleProfile W) (Real.exp l) 0 0‖^2≤E) :
    (primes.card : ℝ)*∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2≤
      4*(1+2*Real.log V)*E := by
  let R := (rows×ˢprimes).image primeRowMap
  have hR : ∀ v∈R, ((Ideal.span {v.val}).absNorm : ℝ)≤U*V^6 := by
    intro v hv
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hu,hP⟩ := Finset.mem_product.mp hp
    exact primeRowMap_norm_bound p U V (hrows p.1 hu) (hprimes p.2 hP)
  have hl : Real.log D-Real.log V≤Real.log D := by linarith [Real.log_nonneg hV]
  obtain ⟨B,hB,hmajor,henergy⟩ := exists_scale_majorant R data.character W a b hb hWs hW
    (Real.log D-Real.log V) (Real.log D) E hl (hraw0 R hR) (hraw1 R hR)
  have hamp (u : FreeRow) (hu : u∈rows) (P : PrimeIdeal) (hP : P∈primes) :
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2≤4*B (primeRowMap (u,P)) := by
    have hN : (1 : ℝ)≤P.val.absNorm := by
      exact_mod_cast (show 1≤P.val.absNorm from (SmoothMobiusCorrection.prime_norm_two_le P).trans' (by norm_num))
    have hNp : (0 : ℝ)<P.val.absNorm := by linarith
    have hlog : Real.log (P.val.absNorm : ℝ)≤Real.log V :=
      Real.log_le_log hNp (hprimes P hP)
    have hDV : Real.log (D/(P.val.absNorm : ℝ))∈Icc (Real.log D-Real.log V) (Real.log D) := by
      rw [Real.log_div hD.ne' hNp.ne']
      constructor <;> linarith [Real.log_nonneg hN]
    have hbase := hmajor (primeRowMap (u,P)) (Real.log D) ⟨hl,le_refl _⟩
    have hlow := hmajor (primeRowMap (u,P)) (Real.log (D/(P.val.absNorm : ℝ))) hDV
    rw [Real.exp_log hD] at hbase
    rw [Real.exp_log (div_pos hD hNp)] at hlow
    have hh := data.prime_energy ⟨u.val,u.property.1⟩ P W a b ha hWs hW D 0 0 hD
    change ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2≤
      2*(‖polynomial (data.character (primeRowMap (u,P))) true W D 0 0‖^2+
        ‖polynomial (data.character (primeRowMap (u,P))) true W (D/(P.val.absNorm : ℝ)) 0 0‖^2) at hh
    linarith
  have hs : (primes.card : ℝ)*∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2≤4*∑ v∈R, B v := by
    calc
      _ = ∑ p∈rows×ˢprimes,
          ‖polynomial (data.character ⟨p.1.val,p.1.property.1⟩) true W D 0 0‖^2 := by
        rw [Finset.sum_product]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        change (primes.card : ℝ) *
          ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2 =
          ∑ _P∈primes, ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p∈rows×ˢprimes, 4*B (primeRowMap p) := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hu,hP⟩ := Finset.mem_product.mp hp
        exact hamp p.1 hu p.2 hP
      _ = _ := by
        dsimp [R]
        rw [Finset.mul_sum,Finset.sum_image]
        exact fun p hp q hq h => primeRowMap_injective h
  have hh := mul_le_mul_of_nonneg_left henergy (by norm_num : (0 : ℝ)≤4)
  nlinarith

end SevenEighths.HeckeInverseAmplification

end

end OAI
end OAIOriginalModule2078

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationPrimePool
Source SHA256: 17dab5c7c9e4ce7233739f9edab79113d04d6c961cb50c9ba35dd4ecc90f2ada
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2079



namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

def RawScaleEnergy (data : RowData) (W : ℝ→ℂ) (U D V E : ℝ) : Prop :=
  ∀ R : Finset NonzeroElement,
    (∀ v∈R, ((Ideal.span {v.val}).absNorm : ℝ)≤U*V^6) →
    ∀ l∈Icc (Real.log D-Real.log V) (Real.log D),
      ∑ v∈R, ‖polynomial (data.character v) true W (Real.exp l) 0 0‖^2≤E

def typedPrimePool (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (a b x : ℝ) : Finset PrimeIdeal :=
  (CenteredMomentPrimePool.primePool M H S a b x).subtype Prime

theorem typedPrimePool_card (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (a b x : ℝ) :
    (typedPrimePool M H S a b x).card=
      (CenteredMomentPrimePool.primePool M H S a b x).card := by
  rw [typedPrimePool,Finset.card_subtype]
  congr 1
  apply Finset.filter_eq_self.mpr
  intro P hP
  exact ((PNT.AnnularPrimeMass.mem_annularPrimeIdeals _ _ _ _ _).mp
    (Finset.mem_sdiff.mp hP).1).2.1

theorem typedPrimePool_norm (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (a b x : ℝ) (ha : 0≤a) (hab : a≤b) (hx : 0<x)
    (P : PrimeIdeal) (hP : P∈typedPrimePool M H S a b x) :
    (P.val.absNorm : ℝ)≤x*b := by
  have hh := Finset.mem_subtype.mp hP
  exact (PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals ha hab hx
    (Finset.mem_sdiff.mp hh).1).2

theorem eventually_fixed_ray_amplification
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y, 0≤φ y) (hφne : φ≠0)
    (a b B : ℝ) (ha : 0<a) (hab : a≤b) (hB : 0<B)
    (hφs : Function.support φ⊆Ioo a b) (hφB : ∀ y, φ y≤B) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (data : RowData) (rows : Finset FreeRow) (W : ℝ→ℂ)
        (wa wb D U E : ℝ),
      0<wa → 0≤wb → Function.support W⊆Icc wa wb → ContDiff ℝ ∞ W →
      0<D → (∀ u∈rows, ((Ideal.span {u.val}).absNorm : ℝ)≤U) →
      RawScaleEnergy data W U D (x*b) E →
      RawScaleEnergy data (scaleProfile W) U D (x*b) E →
      (∑ u∈rows, ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2)≤
        4*(1+2*Real.log (x*b))*E*Real.log x/(c*x) := by
  obtain ⟨c,hc,hcard⟩ := CenteredMomentPrimePool.eventually_primePool_card M H hH S
    φ hφ hφc hφp hφ0 hφne a b B ha hab hB hφs hφB
  have hb : 0<b := ha.trans_le hab
  refine ⟨c,hc,?_⟩
  filter_upwards [hcard,eventually_gt_atTop (1 : ℝ),eventually_ge_atTop (1/b)] with x hcard hx hxB
  intro data rows W wa wb D U E hwa hwb hWs hW hD hrows hraw0 hraw1
  have hx0 : 0<x := zero_lt_one.trans hx
  have hxblog : 1≤x*b := (div_le_iff₀ hb).mp hxB
  have hlog : 0<Real.log x := Real.log_pos hx
  have hc' : c*x/Real.log x≤((typedPrimePool M H S a b x).card : ℝ) := by
    rw [typedPrimePool_card]
    exact hcard
  have havg := averaged_energy data rows (typedPrimePool M H S a b x) W wa wb hwa hwb
    hWs hW D U (x*b) E hD hxblog hrows
    (fun P hP => typedPrimePool_norm M H S a b x ha.le hab hx0 P hP) hraw0 hraw1
  have hsum : 0≤∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hh := (mul_le_mul_of_nonneg_right hc' hsum).trans havg
  apply (le_div_iff₀ (mul_pos hc hx0)).mpr
  calc
    _ = (c*x/Real.log x*(∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2))*Real.log x := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hh hlog.le

end SevenEighths.HeckeInverseAmplification

end

end OAI
end OAIOriginalModule2079

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationBudget
Source SHA256: 25ac5ce13723bf3f0660d8845a3c7b1579852016b46d6b05d8589249b3a55e83
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2080


namespace OAI

noncomputable section
open Filter
namespace SevenEighths.HeckeInverseAmplification

def amplificationPower (c r : ℝ) : ℝ := max 0 (((1+c)*r-1)/6)
def sourceExponent (r : ℝ) : ℝ := max 1 ((1+5*r)/6)

theorem amplificationPower_nonneg (c r : ℝ) : 0≤amplificationPower c r := le_max_left _ _

theorem amplificationPower_upper (c r R : ℝ) (hc : c≤1) (hr : 0≤r)
    (hrR : r≤R) : amplificationPower c r≤R/3 := by
  apply max_le (by linarith)
  have hh := mul_le_mul_of_nonneg_right hc hr
  nlinarith

theorem amplified_exponent (c r : ℝ) :
    1+5*amplificationPower c r=max 1 ((1+5*(1+c)*r)/6) := by
  unfold amplificationPower
  by_cases h : 0≤((1+c)*r-1)/6
  · rw [max_eq_right h,max_eq_right (by linarith)]
    ring
  · rw [max_eq_left (le_of_not_ge h),max_eq_left (by linarith)]
    ring

theorem amplified_exponent_le (c r R : ℝ) (hc : 0≤c) (hrR : r≤R)
    (hR : 0≤R) : 1+5*amplificationPower c r≤sourceExponent r+5*c*R/6 := by
  rw [amplified_exponent]
  apply max_le
  · have hh := le_max_left 1 ((1+5*r)/6)
    unfold sourceExponent
    nlinarith [mul_nonneg hc hR]
  · have hh := le_max_right 1 ((1+5*r)/6)
    have hh' := mul_le_mul_of_nonneg_left hrR hc
    unfold sourceExponent
    nlinarith

theorem exists_amplification_budget (R ε : ℝ) (hR : 0≤R) (hε : 0<ε) :
    ∃ c κ : ℝ, 0<c ∧ c≤1 ∧ 0<κ ∧
      ∀ r : ℝ, 0≤r → r≤R →
      1+5*amplificationPower c r+κ*(1+6*amplificationPower c r+r)≤
        sourceExponent r+ε/2 := by
  let c := min 1 (ε/(4*(R+1)))
  let κ := ε/(4*(1+3*R))
  have hc : 0<c := lt_min zero_lt_one (div_pos hε (by positivity))
  have hκ : 0<κ := div_pos hε (by positivity)
  have hc1 : c≤1 := min_le_left _ _
  have hcb : c*(4*(R+1))≤ε := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hκb : κ*(4*(1+3*R))=ε := by dsimp [κ]; field_simp
  refine ⟨c,κ,hc,hc1,hκ,?_⟩
  intro r hr hrR
  have hp := amplificationPower_upper c r R hc1 hr hrR
  have he := amplified_exponent_le c r R hc.le hrR hR
  have hraw : κ*(1+6*amplificationPower c r+r)≤κ*(1+3*R) := by
    apply mul_le_mul_of_nonneg_left _ hκ.le
    linarith
  nlinarith

theorem logarithmic_cost_eventually (A b P η : ℝ) (hA : 1≤A)
    (hbA : 1≤b*A) (hP : 0≤P) (hη : 0<η) :
    ∃ K : ℝ, 0≤K ∧ ∀ᶠ U : ℝ in atTop, ∀ p : ℝ, 0≤p → p≤P →
      (1+2*Real.log (b*(A*U^p)))*Real.log (A*U^p)≤K*U^η := by
  let K := (1+2*Real.log (b*A)+2*P)*(Real.log A+P)
  have hLA : 0≤Real.log A := Real.log_nonneg hA
  have hLB : 0≤Real.log (b*A) := Real.log_nonneg hbA
  have hK : 0≤K := mul_nonneg (by positivity) (by positivity)
  have hlog := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hη).bound (by norm_num : (0 : ℝ)<1)
  refine ⟨K,hK,?_⟩
  filter_upwards [hlog,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℝ)] with U hlog hLU hU
  intro p hp hpP
  have hUp : 0<U := zero_lt_one.trans_le hU
  have hpow : 0<U^p := Real.rpow_pos_of_pos hUp _
  have hx : 1≤A*U^p := one_le_mul_of_one_le_of_one_le hA (Real.one_le_rpow hU hp)
  have hlogx : Real.log (A*U^p)=Real.log A+p*Real.log U := by
    rw [Real.log_mul (ne_of_gt (zero_lt_one.trans_le hA)) hpow.ne',Real.log_rpow hUp]
  have hlogbx : Real.log (b*(A*U^p))=Real.log (b*A)+p*Real.log U := by
    rw [show b*(A*U^p)=b*A*U^p by ring,
      Real.log_mul (ne_of_gt (zero_lt_one.trans_le hbA)) hpow.ne',Real.log_rpow hUp]
  have hfirst : 1+2*Real.log (b*(A*U^p))≤(1+2*Real.log (b*A)+2*P)*Real.log U := by
    rw [hlogbx]
    nlinarith [mul_le_mul_of_nonneg_right hpP (by linarith : 0≤Real.log U),
      mul_le_mul_of_nonneg_left hLU hLB]
  have hsecond : Real.log (A*U^p)≤(Real.log A+P)*Real.log U := by
    rw [hlogx]
    nlinarith [mul_le_mul_of_nonneg_right hpP (by linarith : 0≤Real.log U),
      mul_le_mul_of_nonneg_left hLU hLA]
  have hsq : (Real.log U)^2≤U^η := by
    simpa only [Real.rpow_two,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.log U)),
      abs_of_nonneg (Real.rpow_nonneg hUp.le _),one_mul] using hlog
  calc
    _ ≤ ((1+2*Real.log (b*A)+2*P)*Real.log U)*((Real.log A+P)*Real.log U) :=
      mul_le_mul hfirst hsecond (Real.log_nonneg hx) (by positivity)
    _ = K*(Real.log U)^2 := by dsimp [K]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq hK

end SevenEighths.HeckeInverseAmplification

end

end OAI
end OAIOriginalModule2080

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationPowers
Source SHA256: 6eb9afc7d2422e10b9609db850dab9fa495b658b61bb838402c5e69c2121f6f1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2081


namespace OAI

noncomputable section
namespace SevenEighths.HeckeInverseAmplification

theorem amplified_norm_power (U A b p : ℝ) (hU : 0<U) :
    U*(b*(A*U^p))^6=(b*A)^6*U^(1+6*p) := by
  have h6 : (U^p)^6=U^(6*p) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hU.le]
    congr 1
    norm_num
    ring
  calc
    _ = (b*A)^6*(U^(1 : ℝ)*U^(6*p)) := by
      rw [show b*(A*U^p)=(b*A)*U^p by ring,mul_pow,h6,Real.rpow_one]
      ring
    _ = _ := by rw [←Real.rpow_add hU]

theorem amplified_energy_power (U A b p r κ : ℝ) (hU : 0<U) :
    (U*(b*(A*U^p))^6)*((U*(b*(A*U^p))^6)*U^r)^κ/(A*U^p)=
      ((b*A)^6*((b*A)^6)^κ/A)*U^(1+5*p+κ*(1+6*p+r)) := by
  rw [amplified_norm_power U A b p hU]
  have hHD : ((b*A)^6*U^(1+6*p))*U^r=(b*A)^6*U^(1+6*p+r) := by
    rw [mul_assoc,←Real.rpow_add hU]
  rw [hHD,Real.mul_rpow (by positivity) (Real.rpow_nonneg hU.le _),
    ←Real.rpow_mul hU.le]
  calc
    _ = ((b*A)^6*((b*A)^6)^κ/A)*
        ((U^(1+6*p)*U^((1+6*p+r)*κ))/U^p) := by ring
    _ = ((b*A)^6*((b*A)^6)^κ/A)*U^((1+6*p)+(1+6*p+r)*κ-p) := by
      rw [←Real.rpow_add hU,←Real.rpow_sub hU]
    _ = _ := by congr 2; ring

theorem fixed_multiplier_lower (U A p : ℝ) (hU : 1≤U) (hA : 0≤A) (hp : 0≤p) :
    A≤A*U^p := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.one_le_rpow hU hp) hA

theorem amplified_norm_dominates (U A b c r : ℝ) (hU : 1≤U) (hbA : 1≤b*A) :
    (U^r)^(1+c)≤U*(b*(A*U^(amplificationPower c r)))^6 := by
  have hUp : 0<U := zero_lt_one.trans_le hU
  rw [amplified_norm_power U A b _ hUp,←Real.rpow_mul hUp.le]
  have he : r*(1+c)≤1+6*amplificationPower c r := by
    have hh := le_max_right 0 (((1+c)*r-1)/6)
    unfold amplificationPower
    nlinarith
  have hp := Real.rpow_le_rpow_of_exponent_le hU he
  have hconst : (1 : ℝ)≤(b*A)^6 := one_le_pow₀ hbA
  exact hp.trans (le_mul_of_one_le_left (Real.rpow_nonneg hUp.le _) hconst)

end SevenEighths.HeckeInverseAmplification

end

end OAI
end OAIOriginalModule2081

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationRaw
Source SHA256: b769af45d6c89e213a94e1c964486b5c9cfaa186824678a734d44008093e29c6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2082


namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

def RawMoment (data : RowData) (W : ℝ→ℂ) (c κ C : ℝ) : Prop :=
  ∀ H D : ℝ, 1≤H → 0<D → D^(1+c)≤H →
    ∀ rows : Finset NonzeroElement,
      (∀ v∈rows, ((Ideal.span {v.val}).absNorm : ℝ)≤H) →
      ∑ v∈rows, ‖polynomial (data.character v) true W D 0 0‖^2≤
        C*H*(H*max 1 D)^κ

theorem RawMoment.scaleEnergy {data : RowData} {W : ℝ→ℂ} {c κ C : ℝ}
    (hraw : RawMoment data W c κ C) (hc : 0≤c) (hκ : 0≤κ) (hC : 0≤C)
    (U D V : ℝ) (hD : 1≤D) (hH : 1≤U*V^6) (hHD : D^(1+c)≤U*V^6) :
    RawScaleEnergy data W U D V (C*(U*V^6)*((U*V^6)*D)^κ) := by
  intro rows hrows l hl
  have hDp : 0<D := zero_lt_one.trans_le hD
  have hHp : 0<U*V^6 := zero_lt_one.trans_le hH
  have hexp : Real.exp l≤D := by
    rw [←Real.exp_log hDp]
    exact Real.exp_le_exp.mpr hl.2
  have hp : (Real.exp l)^(1+c)≤U*V^6 :=
    (Real.rpow_le_rpow (Real.exp_pos l).le hexp (by linarith)).trans hHD
  have hh := hraw (U*V^6) (Real.exp l) hH (Real.exp_pos l) hp rows hrows
  refine hh.trans ?_
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hHp.le)
  apply Real.rpow_le_rpow (by positivity) _ hκ
  exact mul_le_mul_of_nonneg_left (max_le hD hexp) hHp.le

end SevenEighths.HeckeInverseAmplification

end

end OAI
end OAIOriginalModule2082

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseRawGeometry
Source SHA256: 7ba7f551e6e4353798853bd092779ea5c10a961fbac9a7ba62c274b56d10b70c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2083



namespace OAI

noncomputable section
namespace SevenEighths.DetectorDictionaryInverseRawGeometry
open InverseMoment InverseInitialCanonicalState

def capacityGap (c : ℝ) : ℝ:=c/(1+c)

theorem capacityGap_pos (c : ℝ) (hc : 0<c) : 0<capacityGap c :=
  div_pos hc (by linarith)

theorem capacityGap_lt_one (c : ℝ) (hc : 0<c) : capacityGap c<1 := by
  apply (div_lt_one (by linarith : 0<1+c)).mpr
  linarith

theorem raw_log_capacity (H D c : ℝ) (hH : 1<H) (hD : 1≤D) (hc : 0<c)
    (hcap : D^(1+c)≤H) :
    0≤Real.logb H D ∧ Real.logb H D≤1-capacityGap c ∧
    2*Real.logb H D≤3-capacityGap c ∧ H^(Real.logb H D)=D := by
  have hHp : 0<H:=zero_lt_one.trans hH
  have hDp : 0<D:=zero_lt_one.trans_le hD
  have hlogH : 0<Real.log H:=Real.log_pos hH
  have hh:=Real.log_le_log (Real.rpow_pos_of_pos hDp (1+c)) hcap
  rw [Real.log_rpow hDp] at hh
  have hr : Real.logb H D≤1/(1+c) := by
    unfold Real.logb
    apply (le_div_iff₀ (by linarith : 0<1+c)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hlogH).mpr
    simpa only [mul_div_assoc,mul_comm,mul_left_comm,one_mul] using hh
  have he : 1/(1+c)=1-capacityGap c := by
    unfold capacityGap
    field_simp
    ring
  have hg:=(capacityGap_pos c hc).le
  exact ⟨div_nonneg (Real.log_nonneg hD) hlogH.le,hr.trans_eq he,
    by linarith [hr.trans_eq he],Real.rpow_logb hHp (ne_of_gt hH) hDp⟩

theorem raw_fixed_reserves (c κ : ℝ) (hc : 0<c) (hκ : 0<κ) :
    ∃η τ π ε : ℝ,0<η ∧ 0<τ ∧ 0<π ∧ 0<ε ∧
      η≤1 ∧ η≤capacityGap c/200 ∧ τ≤capacityGap c/200 ∧
      40*η+π+ε≤κ := by
  let η:=min (capacityGap c/200) (min (κ/100) (1/100))
  have hg:=capacityGap_pos c hc
  have hη : 0<η:=lt_min (by positivity)
    (lt_min (by positivity) (by norm_num))
  have hηg : η≤capacityGap c/200:=min_le_left _ _
  have hηκ : η≤κ/100:=(min_le_right _ _).trans (min_le_left _ _)
  have hη1 : η≤1/100:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η,η,κ/4,κ/4,hη,hη,by positivity,by positivity,by linarith,hηg,hηg,?_⟩
  linarith

theorem raw_retained_margins (H D c B θ v Hfreq η τ Q : ℝ)
    (hH : 1<H) (hD : 1≤D) (hc : 0<c) (hcap : D^(1+c)≤H)
    (hP : -2*η≤B-θ) (hQ : Q≤B-θ+3*η) (hη : 0≤η)
    (hηsmall : η≤capacityGap c/100) (hτ : τ≤capacityGap c/100)
    (hcut : InverseInitialProfile.radialCenter 1 Hfreq θ (Real.logb H D) B≤4*η+τ) :
    CanonicalMargins
      (max 0 (Real.logb H D-B-v)+(θ+v+2*η)) (θ+Hfreq+2*η) Q 0
      (3*capacityGap c/4) := by
  obtain ⟨hr,hfirst,hsecond,_⟩:=raw_log_capacity H D c hH hD hc hcap
  have hh:=enlarged_initial_margins 1 (Real.logb H D) 0 0 B θ v Hfreq η τ Q
    (capacityGap c) (capacityGap c)
    (by simpa using hfirst) (by simpa using hsecond) (by norm_num) hP
    (by simpa using hQ) (by simpa using (capacityGap_pos c hc).le) hη
    (by simpa using hηsmall) (by simpa using hτ) (by simpa using hcut)
  simpa using hh

theorem raw_output_budget (H D κ e : ℝ) (hH : 1≤H) (hκ : 0≤κ) (he : e≤κ) :
    H^(1+e)≤H*(H*max 1 D)^κ := by
  have hHp : 0<H:=zero_lt_one.trans_le hH
  rw [Real.rpow_add hHp,Real.rpow_one]
  apply mul_le_mul_of_nonneg_left _ hHp.le
  calc
    H^e≤H^κ:=Real.rpow_le_rpow_of_exponent_le hH he
    _≤(H*max 1 D)^κ:=Real.rpow_le_rpow hHp.le (by nlinarith [le_max_left 1 D]) hκ

end SevenEighths.DetectorDictionaryInverseRawGeometry

end

end OAI
end OAIOriginalModule2083

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationEndpoint
Source SHA256: 11580ed37a1c8f2ecfd4d58ed1f90836818aaf812d2052c27343c2ac5bd3d5b4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2084


namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem no_slot_endpoint
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y, 0≤φ y) (hφne : φ≠0)
    (a b B : ℝ) (ha : 0<a) (hab : a≤b) (hB : 0<B)
    (hφs : Function.support φ⊆Ioo a b) (hφB : ∀ y, φ y≤B)
    (R ε : ℝ) (hR : 0≤R) (hε : 0<ε) :
    ∃ c κ K : ℝ, 0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (r : ℝ) (data : RowData) (rows : Finset FreeRow) (W : ℝ→ℂ)
        (wa wb C : ℝ),
      0≤r → r≤R → 0≤C →
      0<wa → 0≤wb → Function.support W⊆Icc wa wb → ContDiff ℝ ∞ W →
      (∀ u∈rows, ((Ideal.span {u.val}).absNorm : ℝ)≤U) →
      RawMoment data W c κ C → RawMoment data (scaleProfile W) c κ C →
      (∑ u∈rows, ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W (U^r) 0 0‖^2)≤
        C*K*U^(sourceExponent r+ε) := by
  obtain ⟨c,κ,hc,hc1,hκ,hbudget⟩ := exists_amplification_budget R ε hR hε
  obtain ⟨d,hd,havg⟩ := eventually_fixed_ray_amplification M H hH S φ hφ hφc hφp
    hφ0 hφne a b B ha hab hB hφs hφB
  obtain ⟨x0,hx0⟩ := eventually_atTop.mp havg
  let A := max 1 (max x0 (1/b))
  have hb : 0<b := ha.trans_le hab
  have hA : 1≤A := le_max_left _ _
  have hAp : 0<A := zero_lt_one.trans_le hA
  have hAx0 : x0≤A := (le_max_left _ _).trans (le_max_right _ _)
  have hbA : 1≤b*A := by
    have hh : 1/b≤A := (le_max_right _ _).trans (le_max_right _ _)
    have hh' := (div_le_iff₀ hb).mp hh
    nlinarith
  obtain ⟨Klog,hKlog,hlog⟩ := logarithmic_cost_eventually A b (R/3) (ε/2)
    hA hbA (by positivity) (by positivity)
  let F := (b*A)^6*((b*A)^6)^κ/A
  let K := (4/d)*F*Klog
  have hF : 0≤F := by dsimp [F]; positivity
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨c,κ,K,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hlog,eventually_ge_atTop (1 : ℝ)] with U hlog hU
  intro r data rows W wa wb C hr hrR hC hwa hwb hWs hW hrows hraw0 hraw1
  let p := amplificationPower c r
  let x := A*U^p
  let D := U^r
  let V := b*x
  let N := U*V^6
  have hUp : 0<U := zero_lt_one.trans_le hU
  have hp : 0≤p := amplificationPower_nonneg c r
  have hpR : p≤R/3 := amplificationPower_upper c r R hc1 hr hrR
  have hxA : A≤x := fixed_multiplier_lower U A p hU hAp.le hp
  have hV : 1≤V := by
    change 1≤b*(A*U^p)
    rw [←mul_assoc]
    exact one_le_mul_of_one_le_of_one_le hbA (Real.one_le_rpow hU hp)
  have hD : 1≤D := Real.one_le_rpow hU hr
  have hDp : 0<D := zero_lt_one.trans_le hD
  have hN : 1≤N := one_le_mul_of_one_le_of_one_le hU (one_le_pow₀ hV)
  have hDN : D^(1+c)≤N := amplified_norm_dominates U A b c r hU hbA
  have hxb : x*b=V := mul_comm x b
  have hav := hx0 x (hAx0.trans hxA) data rows W wa wb D U
    (C*N*(N*D)^κ) hwa hwb hWs hW hDp hrows
    (by rw [hxb]; exact hraw0.scaleEnergy hc.le hκ.le hC U D V hD hN hDN)
    (by rw [hxb]; exact hraw1.scaleEnergy hc.le hκ.le hC U D V hD hN hDN)
  have hlog' := hlog p hp hpR
  have hnorm : N*(N*D)^κ/x=F*U^(1+5*p+κ*(1+6*p+r)) :=
    amplified_energy_power U A b p r κ hUp
  have hexp := hbudget r hr hrR
  have hpow : U^(1+5*p+κ*(1+6*p+r)+ε/2)≤U^(sourceExponent r+ε) :=
    Real.rpow_le_rpow_of_exponent_le hU (by dsimp [p]; linarith)
  calc
    _ ≤ 4*(1+2*Real.log (x*b))*(C*N*(N*D)^κ)*Real.log x/(d*x) := hav
    _ = C*(4/d)*(N*(N*D)^κ/x)*((1+2*Real.log (b*x))*Real.log x) := by
      rw [mul_comm x b]
      ring
    _ = (C*(4/d)*F)*((1+2*Real.log (b*x))*Real.log x)*
        U^(1+5*p+κ*(1+6*p+r)) := by rw [hnorm]; ring
    _ ≤ (C*(4/d)*F)*(Klog*U^(ε/2))*U^(1+5*p+κ*(1+6*p+r)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hUp.le _)
      exact mul_le_mul_of_nonneg_left hlog' (by positivity)
    _ = C*K*U^(1+5*p+κ*(1+6*p+r)+ε/2) := by
      rw [Real.rpow_add hUp (1+5*p+κ*(1+6*p+r)) (ε/2)]
      dsimp [K]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (mul_nonneg hC hK)

end SevenEighths.HeckeInverseAmplification

end

end OAI
end OAIOriginalModule2084

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationProfiles
Source SHA256: d3cd9a85d492c9e8472a0b36938ba84a3273e8bfca6a3f3cd91d95524c9e408e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2085



namespace OAI

noncomputable section
open scoped Classical ContDiff Topology
open Set Filter Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

def twistProfile (W : ℝ→ℂ) (σ freq x : ℝ) : ℂ := W x*(x : ℂ)^(-shift σ freq)

theorem twistProfile_support (W : ℝ→ℂ) (σ freq : ℝ) :
    Function.support (twistProfile W σ freq)⊆Function.support W := by
  intro x hx hw
  exact hx (by simp [twistProfile,hw])

theorem polynomial_twistProfile (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) :
    polynomial χ inv (twistProfile W σ freq) D 0 0=polynomial χ inv W D σ freq := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  simp [summand,twistProfile,HeckeDyadic.shift,mul_assoc]

theorem twistProfile_smooth (W : ℝ→ℂ) (σ freq a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (twistProfile W σ freq) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : 0<x
  · have he : twistProfile W σ freq =ᶠ[nhds x]
        (fun y : ℝ => W y*Complex.exp ((Real.log y : ℂ)*(-shift σ freq))) := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      unfold twistProfile
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
        ←Complex.ofReal_log hy.le]
    apply ContDiffAt.congr_of_eventuallyEq _ he
    apply hW.contDiffAt.mul
    apply Complex.contDiff_exp.contDiffAt.comp x
    have hl : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log y : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_log.mpr hx.ne')
    exact hl.mul contDiffAt_const
  · have hxa : x<a := lt_of_le_of_lt (le_of_not_gt hx) ha
    have he : twistProfile W σ freq =ᶠ[nhds x] (fun _ => 0) := by
      filter_upwards [isOpen_Iio.mem_nhds hxa] with y hy
      have hw : W y=0 := by
        by_contra hn
        exact (not_le_of_gt hy) (hs hn).1
      simp [twistProfile,hw]
    exact contDiffAt_const.congr_of_eventuallyEq he

end SevenEighths.HeckeInverseAmplification

end

end OAI
end OAIOriginalModule2085

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationRowwise
Source SHA256: cce7c7a2c63b24649183bb14120cde67bc43bb1cc088b92d343b1a72c971895f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2086



namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeDetectorRowwisePolynomial

def logTest (W : ℝ→ℂ) : ℕ→ℝ→ℂ
  | 0 => W
  | n+1 => logProfile (logTest W n)

theorem logTest_support (W : ℝ→ℂ) (n : ℕ) :
    Function.support (logTest W n)⊆Function.support W := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact (logProfile_support (logTest W n)).trans ih

theorem logTest_smooth (W : ℝ→ℂ) (n : ℕ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (logTest W n) := by
  induction n with
  | zero => exact hW
  | succ n ih => exact logProfile_smooth (logTest W n) a b ha ((logTest_support W n).trans hs) ih

theorem no_slot_rowwise_endpoint
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y, 0≤φ y) (hφne : φ≠0)
    (a b B : ℝ) (ha : 0<a) (hab : a≤b) (hB : 0<B)
    (hφs : Function.support φ⊆Ioo a b) (hφB : ∀ y, φ y≤B)
    (R ε : ℝ) (hR : 0≤R) (hε : 0<ε) :
    ∃ c κ K : ℝ, 0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (r : ℝ) (data : RowData) (rows : Finset FreeRow) (W : ℝ→ℂ)
        (wa wb C T : ℝ) (σ freq : FreeRow→ℝ),
      0≤r → r≤R → 0≤C → 0≤T →
      0<wa → 0≤wb → Function.support W⊆Icc wa wb → ContDiff ℝ ∞ W →
      (∀ u∈rows, ((Ideal.span {u.val}).absNorm : ℝ)≤U) →
      (∀ u∈rows, σ u∈Icc 0 1) → (∀ u∈rows, freq u∈Icc (-T) T) →
      (∀ n : ℕ, n≤2 → ∀ s∈Icc (0 : ℝ) 1, ∀ t∈Icc (-T) T,
        RawMoment data (twistProfile (logTest W n) s t) c κ C ∧
        RawMoment data (scaleProfile (twistProfile (logTest W n) s t)) c κ C) →
      (∑ u∈rows, ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W (U^r) (σ u) (freq u)‖^2)≤
        12*(1+T)*(C*K*U^(sourceExponent r+ε)) := by
  obtain ⟨c,κ,K,hc,hc1,hκ,hK,he⟩ := no_slot_endpoint M H hH S φ hφ hφc hφp hφ0 hφne
    a b B ha hab hB hφs hφB R ε hR hε
  refine ⟨c,κ,K,hc,hc1,hκ,hK,?_⟩
  filter_upwards [he,eventually_ge_atTop (1 : ℝ)] with U he hU
  intro r data rows W wa wb C T σ freq hr hrR hC hT hwa hwb hWs hW hrows hσ hf hraw
  have hUp : 0<U := zero_lt_one.trans_le hU
  have hD : 0<U^r := Real.rpow_pos_of_pos hUp _
  have henergy (n : ℕ) (hn : n≤2) (s : ℝ) (hs : s∈Icc (0 : ℝ) 1)
      (t : ℝ) (ht : t∈Icc (-T) T) :
      ∑ u∈rows, ‖polynomial (data.character ⟨u.val,u.property.1⟩) true (logTest W n) (U^r) s t‖^2≤
        C*K*U^(sourceExponent r+ε) := by
    have hlW := (logTest_support W n).trans hWs
    have htW := (twistProfile_support (logTest W n) s t).trans hlW
    have hlS := logTest_smooth W n wa wb hwa hWs hW
    have htS := twistProfile_smooth (logTest W n) s t wa wb hwa hlW hlS
    have hh := he r data rows (twistProfile (logTest W n) s t) wa wb C hr hrR hC
      hwa hwb htW htS hrows (hraw n hn s hs t ht).1 (hraw n hn s hs t ht).2
    simpa only [polynomial_twistProfile] using hh
  let Q := scaleSupport (Real.log (U^r)) wb
  have hcover : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/(U^r))≠0 → J∈Q := by
    simpa only [Real.exp_log hD] using scaleSupport_cover W wa wb (Real.log (U^r))
      (Real.log (U^r)) hwb hWs (le_refl _)
  have hh := HeckeDetectorRowwiseMarked.marked_rowwise rows
    (fun u : FreeRow => data.character ⟨u.val,u.property.1⟩) true W (U^r) hD Q hcover
    (fun _ => 1) 0 1 (-T) T (C*K*U^(sourceExponent r+ε)) (by norm_num) (by linarith)
    σ freq hσ hf
    (by simpa only [mul_one,logTest] using henergy 0 (by omega))
    (by simpa only [mul_one,logTest] using henergy 1 (by omega))
    (by simpa only [mul_one,logTest] using henergy 2 (by omega))
  simp only [mul_one] at hh
  refine hh.trans ?_
  have hE : 0≤C*K*U^(sourceExponent r+ε) := by positivity
  nlinarith

end SevenEighths.HeckeInverseAmplification

end

end OAI
end OAIOriginalModule2086

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicControl
Source SHA256: d8ce3846425186e749828db7303de5a37f385e44660a9d26974d5bbc8c84b4df
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2087



namespace OAI

noncomputable section
open scoped Classical Topology
open Set Metric Complex
namespace SevenEighths.HeckePrimeDyadicControl
open HeckeFamily HeckeLogarithmicInput HeckeLogarithmic HeckeFiniteDeletion
open HeckeDeletionBounds HeckeReciprocalGrowth

theorem logDeriv_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    (hχ : χ.residue ≠ 1) {s : ℂ} (hs : 0 < s.re)
    (hψs : LFunction ψ s ≠ 0) :
    logDeriv (LFunction χ) s = logDeriv (LFunction ψ) s +
      logDeriv (factors χ.modulus ψ) s := by
  have hψ : ψ.residue ≠ 1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
  have heq : LFunction χ =ᶠ[nhds s] (fun z => LFunction ψ z * factors χ.modulus ψ z) := by
    filter_upwards [(Complex.isOpen_re_gt 0).mem_nhds hs] with z hz
    exact LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hz
  rw [(logDeriv_congr_nhds heq).self_of_nhds]
  exact logDeriv_fun_mul s hψs (factors_ne_zero _ _ hs)
    (LFunction_entire_nonprincipal ψ hψ s) (factors_differentiable _ _ s)

theorem original_disk_control (e : ℝ) (he : 0<e) (he' : e<1/1000) :
    ∃ B : ℝ, 0≤B ∧ ∀ (χ : Character), χ.residue ≠ 1 → ∀ a t : ℝ,
      1/2≤a → a≤1 →
      (∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), LFunction χ z ≠ 0) →
      ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-8*e),
        ‖logDeriv (LFunction χ) z‖ ≤ B*Real.log (complexity χ t) +
          localBound (1/2)*Real.log ((radical χ.modulus).absNorm : ℝ) := by
  obtain ⟨Dp,B,_,hB,hprimitive⟩ := HeckeLogarithmicActual.disk_control e 1 he he' (by norm_num)
  refine ⟨B,hB,?_⟩
  intro χ hχ a t ha ha' hzero z hz
  obtain ⟨ψ,_,hp,hn,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue ≠ 1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
  have hregular : regular ψ = LFunction ψ := regular_eq_nonprincipal ψ hψ
  have hzeroψ : ∀ w ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), regular ψ w ≠ 0 := by
    intro w hw
    rw [hregular]
    have hwp : 0 < w.re := by
      have hr := LogarithmicControl.disk_re_gt hw
      linarith
    intro hh
    apply hzero w hw
    rw [LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hwp, hh, zero_mul]
  have hbound := (hprimitive ψ hp a t ha ha' hzeroψ).2 z hz
  rw [hregular] at hbound
  have hz2 : z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e) :=
    closedBall_subset_ball (by linarith) hz
  have hzre : (1/2 : ℝ) ≤ z.re := by
    have hr := LogarithmicControl.disk_re_gt hz2
    linarith
  have hzpos : 0 < z.re := by linarith
  have hdel := HeckeDeletionDerivative.factors_logDeriv_norm (1/2) (by norm_num)
    χ.modulus ψ hzre
  have hQ : complexity ψ t ≤ complexity χ t := by
    unfold complexity
    have hn' : (ψ.modulus.absNorm : ℝ) ≤ χ.modulus.absNorm := by exact_mod_cast hn
    gcongr
  have hc0 : 0 < complexity ψ t := (Real.exp_pos 1).trans_le (complexity_ge_exp ψ t)
  rw [logDeriv_eq_of_mask χ ψ hmask hχ hzpos (by simpa [hregular] using hzeroψ z hz2)]
  apply (norm_add_le _ _).trans
  exact add_le_add (hbound.trans (mul_le_mul_of_nonneg_left (Real.log_le_log hc0 hQ) hB)) hdel

theorem buffered_original_control (e : ℝ) (he : 0<e) (he' : e<1/1000) :
    ∃ B : ℝ, 0≤B ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue ≠ 1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T) < a+2*e →
      ∀ (j : ι) (t : ℝ), |t| ≤ (3*i+2 : ℕ)*T →
      ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-8*e),
        ‖logDeriv (LFunction (χ j)) z‖ ≤ B*Real.log (complexity (χ j) t) +
          localBound (1/2)*Real.log ((radical (χ j).modulus).absNorm : ℝ) := by
  obtain ⟨B,hB,hbound⟩ := original_disk_control e he he'
  refine ⟨B,hB,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j t ht z hz
  exact hbound (χ j) (hχ j) a t (by linarith) ha'
    (fun w hw => HeckeDetectorZeros.nonzero_on_buffered_disk χ hχ T a e i hT ha he
      hmax j t ht (ball_subset_closedBall hw)) z hz

theorem buffered_rectangle_control (e : ℝ)
    (he : 0<e) (he' : e<1/1000) :
    ∃ B : ℝ, 0≤B ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (z : ℂ), a+8*e≤z.re → z.re≤2 →
      |z.im|≤(3*i+2 : ℕ)*T →
      LFunction (χ j) z≠0 ∧
      ‖logDeriv (LFunction (χ j)) z‖≤
        B*Real.log (complexity (χ j) ((3*i+2 : ℕ)*T)) +
          localBound (1/2)*Real.log ((radical (χ j).modulus).absNorm : ℝ) := by
  obtain ⟨B,hB,hbound⟩ := buffered_original_control e he he'
  refine ⟨B,hB,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j z hzl hzr hzi
  have hz6 : z ∈ closedBall ((2 : ℂ)+z.im*I) (2-a-8*e) := by
    rw [mem_closedBall,dist_eq_norm]
    have heq : z-((2 : ℂ)+z.im*I)=((z.re-2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [heq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith : z.re-2≤0)]
    linarith
  have hz2 : z ∈ closedBall ((2 : ℂ)+z.im*I) (2-a-2*e) :=
    closedBall_subset_closedBall (by linarith) hz6
  refine ⟨HeckeDetectorZeros.nonzero_on_buffered_disk χ hχ T a e i hT ha he
    hmax j z.im hzi hz2, ?_⟩
  apply (hbound χ hχ T a i hT ha ha' hmax j z.im hzi z hz6).trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ hB
  apply Real.log_le_log ((Real.exp_pos 1).trans_le (complexity_ge_exp _ _))
  unfold complexity
  have hH : 0 ≤ (3*i+2 : ℕ)*T := (abs_nonneg z.im).trans hzi
  rw [abs_of_nonneg hH]
  gcongr

end SevenEighths.HeckePrimeDyadicControl

end

end OAI
end OAIOriginalModule2087

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicEstimates
Source SHA256: 2f437de15a7e36581100f57a833e7f6c88524cce65384bee1845dd124a044c01
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2088




namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

theorem absolute_tail_bound (χ : Character) (W : ℝ → ℂ)
    (D r σ freq C T : ℝ) (n : ℕ) (hD : 0<D) (hr : 1<r+σ) (hC : 0≤C) (hT : 0≤T)
    (hm : ∀ t : ℝ, (1+|t|)^(n+2)*‖mellin W ((r : ℂ)+t*I)‖≤C) :
    ‖∫ t : ℝ in (Icc (-T) T)ᶜ, integrand χ W D σ freq ((r : ℂ)+t*I)‖ ≤
      (C*D^(r+σ-1/2)*eulerBound (r+σ))/(1+T)^n*Real.pi := by
  apply rapid_tail_bound _ _ T n
  · exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hD.le _))
      (tsum_nonneg (fun I => mul_nonneg (IdealMangoldt.value_nonneg _) (Real.rpow_nonneg (norm_pos I).le _)))
  · exact hT
  · intro t
    rw [integrand_norm χ W D σ freq hD]
    have hb := series_norm_le χ hr (s := (r : ℂ)+t*I+shift σ freq) (by simp)
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
      sub_self, add_zero]
    calc
      _ = ((1+|t|)^(n+2)*‖mellin W ((r : ℂ)+t*I)‖)*D^(r+σ-1/2)*
        ‖series χ ((r : ℂ)+t*I+shift σ freq)‖ := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right (hm t) (Real.rpow_nonneg hD.le _))
        hb (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg hD.le _))

theorem central_segment_bound (χ : Character) (W : ℝ → ℂ)
    (D l σ freq C K T : ℝ) (hD : 0<D) (hC : 0≤C) (hK : 0≤K) (hT : 0≤T)
    (hm : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤C)
    (hs : ∀ t ∈ Icc (-T) T, ‖series χ ((l : ℂ)+t*I+shift σ freq)‖≤K) :
    ‖∫ t : ℝ in -T..T, integrand χ W D σ freq ((l : ℂ)+t*I)‖ ≤
      C*D^(l+σ-1/2)*K*Real.pi := by
  rw [intervalIntegral.integral_of_le (by linarith : -T≤T)]
  have hint := integrable_inv_one_add_sq.const_mul (C*D^(l+σ-1/2)*K)
  calc
    _ ≤ ∫ t : ℝ in Ioc (-T) T, (C*D^(l+σ-1/2)*K)*(1+t^2)⁻¹ := by
      apply norm_integral_le_of_norm_le hint.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [integrand_norm χ W D σ freq hD]
      have hb := CubicReflectionKernel.weighted_two_to_cauchy (norm_nonneg _) t (hm t)
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
        sub_self, add_zero]
      calc
        _ ≤ (C/(1+t^2))*D^(l+σ-1/2)*K :=
          mul_le_mul (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hD.le _))
            (hs t ⟨ht.1.le,ht.2⟩) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ ≤ ∫ t : ℝ, (C*D^(l+σ-1/2)*K)*(1+t^2)⁻¹ :=
      integral_mono_measure Measure.restrict_le_self (by filter_upwards [] with t; positivity) hint
    _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

theorem horizontal_join_bound (χ : Character) (W : ℝ → ℂ)
    (D σ freq l r y C K : ℝ) (n : ℕ)
    (hD : 1≤D) (hlr : l≤r) (hC : 0≤C) (_hK : 0≤K)
    (hm : ∀ x ∈ Icc l r, (1+|y|)^n*‖mellin W ((x : ℂ)+y*I)‖≤C)
    (hs : ∀ x ∈ Icc l r, ‖series χ ((x : ℂ)+y*I+shift σ freq)‖≤K) :
    ‖∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+y*I)‖ ≤
      (C*D^(r+σ-1/2)*K/(1+|y|)^n)*|r-l| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  have hx' : x ∈ Icc l r := by simpa [uIcc_of_le hlr] using uIoc_subset_uIcc hx
  have hb : ‖mellin W ((x : ℂ)+y*I)‖≤C/(1+|y|)^n := by
    apply (le_div_iff₀ (by positivity : 0<(1+|y|)^n)).mpr
    simpa [mul_comm] using hm x hx'
  have hpow : D^(x+σ-1/2)≤D^(r+σ-1/2) :=
    Real.rpow_le_rpow_of_exponent_le hD (by linarith [hx'.2])
  rw [integrand_norm χ W D σ freq (by linarith)]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
    sub_self, add_zero]
  calc
    _ ≤ (C/(1+|y|)^n)*D^(r+σ-1/2)*K :=
      mul_le_mul (mul_le_mul hb hpow (by positivity) (by positivity))
        (hs x hx') (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem polynomial_bound_of_rectangle (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T C₂ Cn K : ℝ) (n : ℕ)
    (hD : 1≤D) (hlr : l≤r) (hr : 1<r+σ) (hT : 0≤T)
    (hC₂ : 0≤C₂) (hCn : 0≤Cn) (hK : 0≤K)
    (hm₂ : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤C₂)
    (hmn : ∀ x ∈ Icc l r, ∀ t : ℝ,
      (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), LFunction χ (s+shift σ freq)≠0)
    (hs : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T),
      ‖series χ (s+shift σ freq)‖≤K) :
    ‖polynomial χ W D σ freq‖≤(1/(2*Real.pi))*
      (C₂*D^(l+σ-1/2)*K*Real.pi +
       2*(Cn*D^(r+σ-1/2)*K/(1+T)^n)*|r-l| +
       (Cn*D^(r+σ-1/2)*eulerBound (r+σ))/(1+T)^n*Real.pi) := by
  have hDp : 0<D := by linarith
  have hmem (x t : ℝ) (hx : x∈Icc l r) (ht : t∈Icc (-T) T) :
      ((x : ℂ)+t*I) ∈ (uIcc l r ×ℂ uIcc (-T) T) := by
    change (((x : ℂ)+t*I).re∈uIcc l r) ∧ (((x : ℂ)+t*I).im∈uIcc (-T) T)
    simpa [uIcc_of_le hlr,uIcc_of_le (by linarith : -T≤T)] using And.intro hx ht
  have hcentral := central_segment_bound χ W D l σ freq C₂ K T hDp hC₂ hK hT
    hm₂ (fun t ht => hs _ (hmem l t ⟨le_rfl,hlr⟩ ht))
  have hm (x : ℝ) (hx : x∈Icc l r) (t : ℝ) :
      (1+|t|)^n*‖mellin W ((x : ℂ)+t*I)‖≤Cn := by
    apply le_trans _ (hmn x hx t)
    gcongr
    · exact le_add_of_nonneg_right (abs_nonneg t)
    · omega
  have hbottom := horizontal_join_bound χ W D σ freq l r (-T) Cn K n hD hlr hCn hK
    (fun x hx => hm x hx (-T)) (fun x hx => hs _ (hmem x (-T) hx ⟨le_rfl,by linarith⟩))
  have htop := horizontal_join_bound χ W D σ freq l r T Cn K n hD hlr hCn hK
    (fun x hx => hm x hx T) (fun x hx => hs _ (hmem x T hx ⟨by linarith,le_rfl⟩))
  simp only [abs_neg,abs_of_nonneg hT,ofReal_neg] at hbottom htop
  have htail := absolute_tail_bound χ W D r σ freq Cn T n hDp hr hCn hT
    (hmn r ⟨hlr,le_rfl⟩)
  rw [polynomial_finite_shift χ hχ W a b ha hWs hW D σ freq l r T hDp hr hT hz,
    norm_mul]
  have hnorm : ‖(1/(2*Real.pi) : ℂ)‖=(1/(2*Real.pi) : ℝ) := by
    simp [Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_four_sides _ _ _ _).trans (by linarith)

end SevenEighths.HeckePrimeDyadic

end

end OAI
end OAIOriginalModule2088

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicBuffered
Source SHA256: be851888a811a898dfbe764dc10c1ea2c1bf12dcee516a976a379334f597c5bd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2089



namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set Metric MeasureTheory Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic HeckeLogarithmic HeckeDeletionBounds

def binCost (B : ℝ) (χ : Character) (H : ℝ) : ℝ :=
  B*Real.log (complexity χ H) + localBound (1/2)*Real.log ((radical χ.modulus).absNorm : ℝ)

theorem binCost_nonneg {B : ℝ} (hB : 0≤B) (χ : Character) (H : ℝ) : 0≤binCost B χ H := by
  have hc : 1≤complexity χ H :=
    (Real.one_le_exp (by norm_num : (0 : ℝ)≤1)).trans (complexity_ge_exp χ H)
  have hr : (1 : ℝ)≤(radical χ.modulus).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero χ.modulus))
  exact add_nonneg (mul_nonneg hB (Real.log_nonneg hc))
    (mul_nonneg (localBound_pos (by norm_num : (0 : ℝ)<1/2)).le (Real.log_nonneg hr))

theorem polynomial_bound_in_bin (e : ℝ) (he : 0<e) (he' : e<1/1000) :
    ∃ B : ℝ, 0≤B ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι→Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (W : ℝ→ℂ) (α β : ℝ), 0<α → Function.support W⊆Icc α β →
      ContDiff ℝ ∞ W → ∀ D σ freq L C₂ Cn : ℝ, ∀ n : ℕ,
      1≤D → 0≤L → 0≤C₂ → 0≤Cn → |freq|+L≤(3*i+2 : ℕ)*T →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((a+8*e-σ : ℝ) : ℂ)+t*I)‖≤C₂) →
      (∀ x∈Icc (a+8*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn) →
      ‖polynomial (χ j) W D σ freq‖ ≤ (1/(2*Real.pi))*
        (C₂*D^(a+8*e-1/2)*binCost B (χ j) ((3*i+2 : ℕ)*T)*Real.pi +
          2*(Cn*D^(3/2 : ℝ)*binCost B (χ j) ((3*i+2 : ℕ)*T)/(1+L)^n)*|2-a-8*e| +
          (Cn*D^(3/2 : ℝ)*eulerBound 2)/(1+L)^n*Real.pi) := by
  obtain ⟨B,hB,hbound⟩ := HeckePrimeDyadicControl.buffered_rectangle_control e he he'
  refine ⟨B,hB,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j W α β hα hWs hW D σ freq L C₂ Cn n
    hD hL hC₂ hCn hfreq hm₂ hmn
  have hlr : a+8*e-σ≤2-σ := by linarith
  have hmem (s : ℂ) (hs : s ∈ (uIcc (a+8*e-σ) (2-σ) ×ℂ uIcc (-L) L)) :
      a+8*e≤(s+HeckeDyadic.shift σ freq).re ∧ (s+HeckeDyadic.shift σ freq).re≤2 ∧
        |(s+HeckeDyadic.shift σ freq).im|≤(3*i+2 : ℕ)*T := by
    convert HeckeDyadic.translated_rectangle_mem (a := a+2*e) (e := e)
      (by linarith) (by linarith) hlr hL hfreq hs using 1 ; ring_nf
  have hs (s : ℂ) (hs : s ∈ (uIcc (a+8*e-σ) (2-σ) ×ℂ uIcc (-L) L)) :=
    hbound χ hχ T a i hT ha ha' hmax j (s+HeckeDyadic.shift σ freq)
      (hmem s hs).1 (hmem s hs).2.1 (hmem s hs).2.2
  have hh := polynomial_bound_of_rectangle (χ j) (hχ j) W α β hα hWs hW
    D σ freq (a+8*e-σ) (2-σ) L C₂ Cn (binCost B (χ j) ((3*i+2 : ℕ)*T)) n
    hD hlr (by linarith) hL hC₂ hCn (binCost_nonneg hB _ _)
    hm₂ hmn (fun s h => (hs s h).1) (fun s h => by
      simpa only [series, neg_div, norm_neg, logDeriv_apply, binCost] using (hs s h).2)
  convert hh using 1 ; congr 1 ; ring_nf

end SevenEighths.HeckePrimeDyadic

end

end OAI
end OAIOriginalModule2089

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicScale
Source SHA256: cfb00ec2c4a51977ffc5fd4abe1e316487530002b9b57c18cd1f385822afd8b0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2090



namespace OAI

noncomputable section
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic HeckeDeletionBounds HeckeLogarithmic

theorem binCost_le_log (χ : Character) (B U H η : ℝ)
    (hB : 0≤B) (hU : 2≤U) (hQ : (χ.modulus.absNorm : ℝ)≤U)
    (hheight : (3+|H|)^2≤U^η) :
    binCost B χ H ≤ (B*(2+η)+localBound (1/2))*Real.log U := by
  have hUp : 0<U := by linarith
  have hcp : 0<complexity χ H := (Real.exp_pos 1).trans_le (complexity_ge_exp χ H)
  have hcomplex : complexity χ H ≤ 2*U^(1+η) := by
    unfold complexity
    calc
      2*(χ.modulus.absNorm : ℝ)*(3+|H|)^2 ≤ 2*U*U^η := by gcongr
      _ = _ := by rw [Real.rpow_add hUp, Real.rpow_one]; ring
  have hlog : Real.log (complexity χ H) ≤ (2+η)*Real.log U := by
    apply (Real.log_le_log hcp hcomplex).trans
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hUp _).ne', Real.log_rpow hUp]
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ)<2) hU
    nlinarith
  have hrad : 0<((radical χ.modulus).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero χ.modulus))
  have hrlog := Real.log_le_log hrad ((radical_norm_le_modulus χ).trans hQ)
  unfold binCost
  calc
    _ ≤ B*((2+η)*Real.log U)+localBound (1/2)*Real.log U :=
      add_le_add (mul_le_mul_of_nonneg_left hlog hB)
        (mul_le_mul_of_nonneg_left hrlog (localBound_pos (by norm_num : (0 : ℝ)<1/2)).le)
    _ = _ := by ring

theorem binCost_le_power (χ : Character) (B U H η ε : ℝ)
    (hB : 0≤B) (hU : 2≤U) (hQ : (χ.modulus.absNorm : ℝ)≤U)
    (hη : 0≤η) (hε : 0<ε) (hheight : (3+|H|)^2≤U^η) :
    binCost B χ H ≤ ((B*(2+η)+localBound (1/2))/ε)*U^ε := by
  apply (binCost_le_log χ B U H η hB hU hQ hheight).trans
  have hc : 0≤B*(2+η)+localBound (1/2) := by
    exact add_nonneg (mul_nonneg hB (by linarith))
      (localBound_pos (by norm_num : (0 : ℝ)<1/2)).le
  have hh := mul_le_mul_of_nonneg_left
    (Real.log_le_rpow_div (by linarith : 0≤U) hε) hc
  convert hh using 1 ; ring

end SevenEighths.HeckePrimeDyadic

end

end OAI
end OAIOriginalModule2090

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicScaled
Source SHA256: 90b849b5756d6c4a681ba7c9481199233079021ae93c9057854b8312d24f3f87
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2091


namespace OAI

noncomputable section

open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic HeckeDeletionBounds

theorem scaled_direct_bound (e κ η : ℝ) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hη : 0≤η) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (W : ℝ → ℂ) (A B : ℝ),
      0<A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ (U r R σ freq V C₂ Cn : ℝ) (n : ℕ),
      2≤U → (χ j).modulus.absNorm≤U → 0≤r → r≤R → 0≤V →
      |freq|+V≤(3*i+2 : ℕ)*T → (3+(3*i+2 : ℕ)*T)^2≤U^η → 0≤C₂ → 0≤Cn →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((a+8*e-σ : ℝ) : ℂ)+t*I)‖≤C₂) →
      (∀ x ∈ Icc (a+8*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn) →
      ‖polynomial (χ j) W (U^r) σ freq‖≤
        C*C₂*U^((a-1/2+8*e)*r+κ)+C*Cn*U^(2*R+κ)/(1+V)^n := by
  obtain ⟨B,hB,hbound⟩ := polynomial_bound_in_bin e he he'
  let Cb := (B*(2+η)+localBound (1/2))/κ
  have hCb : 0<Cb := div_pos
    (add_pos_of_nonneg_of_pos (mul_nonneg hB (by linarith))
      (localBound_pos (by norm_num : (0 : ℝ)<1/2))) hκ
  let E := eulerBound 2
  have hE : 0≤E := tsum_nonneg (fun I => mul_nonneg (IdealMangoldt.value_nonneg _) (Real.rpow_nonneg (norm_pos I).le _))
  let C := 1+Cb*Real.pi+4*Cb+E*Real.pi
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j W A B' hA hWs hW
    U r R σ freq V C₂ Cn n hU2 hQ hr hrR hV hfreq hheight hC₂ hCn hm₂ hmn
  let H : ℝ := (3*i+2 : ℕ)*T
  have hH : 0≤H := by dsimp [H]; positivity
  have hU : 1≤U := (HeckeLogarithmicInput.modulus_norm_ge_one (χ j)).trans hQ
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hD : 1≤U^r := Real.one_le_rpow hU hr
  have hb := hbound χ hχ T a i hT ha ha' hmax j W A B' hA hWs hW
    (U^r) σ freq V C₂ Cn n hD hV hC₂ hCn hfreq hm₂ hmn
  have hcost : binCost B (χ j) H ≤ Cb*U^κ :=
    binCost_le_power (χ j) B U H η κ hB hU2 hQ hη hκ (by rw [abs_of_nonneg hH]; exact hheight)
  have hcentral : (U^r)^(a+8*e-1/2)*binCost B (χ j) H ≤
      Cb*U^((a-1/2+8*e)*r+κ) := by
    calc
      _ ≤ (U^r)^(a+8*e-1/2)*(Cb*U^κ) :=
        mul_le_mul_of_nonneg_left hcost (Real.rpow_nonneg (Real.rpow_nonneg hUp.le _) _)
      _ = _ := by rw [←Real.rpow_mul hUp.le, mul_left_comm, ←Real.rpow_add hUp]; congr 2; ring
  have hexternal : (U^r)^(3/2 : ℝ)*binCost B (χ j) H ≤ Cb*U^(2*R+κ) := by
    calc
      _ ≤ (U^r)^(3/2 : ℝ)*(Cb*U^κ) :=
        mul_le_mul_of_nonneg_left hcost (Real.rpow_nonneg (Real.rpow_nonneg hUp.le _) _)
      _ = Cb*U^(r*(3/2)+κ) := by rw [←Real.rpow_mul hUp.le, mul_left_comm, ←Real.rpow_add hUp]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)) hCb.le
  have hpow : (U^r)^(3/2 : ℝ)≤U^(2*R+κ) := by
    rw [←Real.rpow_mul hUp.le]
    exact Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)
  have hwidth : |2-a-8*e|≤2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hc : C₂*(U^r)^(a+8*e-1/2)*binCost B (χ j) H*Real.pi≤
      (Cb*Real.pi)*C₂*U^((a-1/2+8*e)*r+κ) := by
    calc
      _ = (C₂*Real.pi)*((U^r)^(a+8*e-1/2)*binCost B (χ j) H) := by ring
      _ ≤ (C₂*Real.pi)*(Cb*U^((a-1/2+8*e)*r+κ)) :=
        mul_le_mul_of_nonneg_left hcentral (by positivity)
      _ = _ := by ring
  have hj : 2*(Cn*(U^r)^(3/2 : ℝ)*binCost B (χ j) H/(1+V)^n)*|2-a-8*e|≤
      (4*Cb)*Cn*U^(2*R+κ)/(1+V)^n := by
    calc
      _ = 2*Cn*((U^r)^(3/2 : ℝ)*binCost B (χ j) H)/(1+V)^n*|2-a-8*e| := by ring
      _ ≤ 2*Cn*(Cb*U^(2*R+κ))/(1+V)^n*2 := by gcongr
      _ = _ := by ring
  have ht : (Cn*(U^r)^(3/2 : ℝ)*E)/(1+V)^n*Real.pi≤
      (E*Real.pi)*Cn*U^(2*R+κ)/(1+V)^n := by
    calc
      _ ≤ (Cn*U^(2*R+κ)*E)/(1+V)^n*Real.pi := by gcongr
      _ = _ := by ring
  have hfac : 1/(2*Real.pi)≤(1 : ℝ) := by
    apply (div_le_one (by positivity)).mpr
    linarith [Real.pi_gt_three]
  have hcomp : 0≤binCost B (χ j) H := binCost_nonneg hB _ _
  apply (hb.trans (mul_le_of_le_one_left (by positivity) hfac)).trans
  change _ ≤ _ at hc hj ht
  have hcC : Cb*Real.pi≤C := by dsimp [C]; nlinarith only [hCb, mul_nonneg hE Real.pi_pos.le]
  have heC : 4*Cb+E*Real.pi≤C := by dsimp [C]; nlinarith only [mul_nonneg hCb.le Real.pi_pos.le]
  calc
    _ ≤ (Cb*Real.pi)*C₂*U^((a-1/2+8*e)*r+κ)+
        (4*Cb)*Cn*U^(2*R+κ)/(1+V)^n+(E*Real.pi)*Cn*U^(2*R+κ)/(1+V)^n := by
      exact add_le_add (add_le_add hc hj) ht
    _ = (Cb*Real.pi)*C₂*U^((a-1/2+8*e)*r+κ)+
        (4*Cb+E*Real.pi)*Cn*U^(2*R+κ)/(1+V)^n := by ring
    _ ≤ _ := by gcongr

end SevenEighths.HeckePrimeDyadic

end

end OAI
end OAIOriginalModule2091

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicSource
Source SHA256: f049474faa33b014c815f296c3c08574fba15b6237b412ce5ece05d05b6db1f4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2092




namespace OAI

noncomputable section

open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

theorem source_log_profile_bound (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmax τ ε e κ η σmin σmax : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (he : 0<e)
    (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*R+κ≤ε) :
    ∃ C : ℝ, 0<C ∧ ∀ Z d : ℝ, 1≤Z → 0≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j, (χ j).residue≠1)
      (a : ℝ) (i : ℕ), 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*Z^τ)<a+2*e →
    ∀ r σ freq L : ℝ,
      0≤r → r≤R → σmin≤σ → σ≤σmax → L∈Icc (0 : ℝ) 1 →
      ∀ k : ι, (χ k).modulus.absNorm≤Z^d →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
      ‖polynomial (χ k) (PrimeLogProfile.profile W L) ((Z^d)^r) σ freq‖≤
        C*(Z^d)^((a-1/2)*r+ε) := by
  obtain ⟨Cd,hCd,hdirect⟩ := scaled_direct_bound e κ η he he' hκ hη
  obtain ⟨n,htail⟩ := uniform_external_tail_order τ dmax (2*R+κ) 0
    hτ hdmax (by positivity) (by norm_num)
  obtain ⟨C₂,hC₂,hm₂⟩ := PrimeLogProfile.uniform_mellin_decay W A B hA hWs hW
    (-σmax) (2-σmin) 2
  obtain ⟨Cn,hCn,hmn⟩ := PrimeLogProfile.uniform_mellin_decay W A B hA hWs hW
    (-σmax) (2-σmin) (n+2)
  refine ⟨Cd*C₂+Cd*Cn*(2 : ℝ)^n,by positivity,?_⟩
  intro Z d hZ hd hd' hU2 hT ι _ χ hχ a i ha ha' hmax r σ freq L
    hr hrR hσmin hσmax hL k hQ hfreq hheight
  let U := Z^d
  have hU : 1≤U := Real.one_le_rpow hZ hd
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hs : Icc (a+8*e-σ) (2-σ)⊆Icc (-σmax) (2-σmin) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hleft : a+8*e-σ∈Icc (-σmax) (2-σmin) := by
    constructor <;> linarith
  have hb := hdirect χ hχ (Z^τ) a i hT ha ha' hmax k
    (PrimeLogProfile.profile W L) A B hA
    ((PrimeLogProfile.profile_support W L).trans hWs)
    (PrimeLogProfile.profile_smooth W A B hA hWs hW L)
    U r R σ freq (Z^τ/2) C₂ Cn n hU2 hQ hr hrR (by positivity)
    hfreq hheight hC₂.le hCn.le (hm₂ L hL _ hleft) (fun x hx => hmn L hL x (hs hx))
  have htail' := htail Z d 0 hZ hd hd' (by norm_num)
  simp only [Real.rpow_zero,mul_one] at htail'
  have hexp : (a-1/2+8*e)*r+κ≤(a-1/2)*r+ε := by
    nlinarith [mul_le_mul_of_nonneg_left hrR (by positivity : 0≤8*e)]
  have hp : 0≤(a-1/2)*r+ε := by
    have : 0≤8*e*R := by positivity
    nlinarith [mul_nonneg (show 0≤a-1/2 by linarith) hr]
  calc
    _ ≤ Cd*C₂*U^((a-1/2)*r+ε)+Cd*Cn*(2 : ℝ)^n := by
      apply hb.trans
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hexp) (by positivity)
      · calc
          _ = (Cd*Cn)*(U^(2*R+κ)/(1+Z^τ/2)^n) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left htail' (by positivity)
    _ ≤ (Cd*C₂+Cd*Cn*(2 : ℝ)^n)*U^((a-1/2)*r+ε) := by
      rw [add_mul]
      apply add_le_add (le_refl _)
      exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hU hp)

end SevenEighths.HeckePrimeDyadic

end

end OAI
end OAIOriginalModule2092

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.PrimeBin
Source SHA256: c0d0f071e7999c249d61416bf4822a6a9497de324cd5af821af8021ab253b2d2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2093



namespace OAI

noncomputable section

open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckePrimeAnnular
open HeckeFamily HeckeDyadic

theorem prime_bin_bound (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmax τ ε e κ η σmin σmax : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε) (he : 0<e)
    (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*R+κ≤ε) :
    ∃ C : ℝ, 0<C ∧ ∀ Z d : ℝ, 1≤Z → 0≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j, (χ j).residue≠1)
      (a : ℝ) (i : ℕ), 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*Z^τ)<a+2*e →
    ∀ r σ freq : ℝ, 0≤r → r≤R → σmin≤σ → σ≤σmax →
      2*(|Real.log A|+|Real.log B|)+1≤Real.log ((Z^d)^r) →
      ∀ k : ι, (χ k).modulus.absNorm≤Z^d →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
      ‖primePolynomial (χ k) W B ((Z^d)^r) σ freq‖≤
        C*(Z^d)^((a-1/2)*r+ε) := by
  obtain ⟨Cp,hCp,hprime⟩ := HeckePrimeDyadic.source_log_profile_bound W A B hA hWs hW
    R dmax τ ε e κ η σmin σmax hR hdmax hτ he he' hκ hη hbudget
  let ξ := ε/(R+1)
  have hξ : 0<ξ := div_pos hε (by positivity)
  obtain ⟨Ce,hCe,herror⟩ := extraction_bound ξ hξ
  obtain ⟨Bf,hBf,hprofile⟩ := fixed_profile_norm_bound W hW.continuous A B σmin σmax hA
  let E := Ce*(max 1 B)^(1/2+ξ)*Bf
  have hE : 0<E := by dsimp [E]; positivity
  refine ⟨Cp+E,by positivity,?_⟩
  intro Z d hZ hd hd' hU2 hT ι _ χ hχ a i ha ha' hmax r σ freq hr hrR
    hσmin hσmax hlarge k hQ hfreq hheight
  let U := Z^d
  let D := U^r
  have hU : 1≤U := Real.one_le_rpow hZ hd
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hD : 1≤D := Real.one_le_rpow hU hr
  have hlog : 1≤Real.log D := by
    linarith [abs_nonneg (Real.log A),abs_nonneg (Real.log B)]
  have hL : 1/Real.log D∈Icc (0 : ℝ) 1 :=
    ⟨by positivity,(div_le_one (by linarith)).mpr hlog⟩
  have hp := hprime Z d hZ hd hd' hU2 hT χ hχ a i ha ha' hmax
    r σ freq (1/Real.log D) hr hrR hσmin hσmax hL k hQ hfreq hheight
  have he := herror (χ k) W A B D σ freq Bf hA hD hWs hlarge hBf.le
    (hprofile σ ⟨hσmin,hσmax⟩)
  have hpow : D^ξ≤U^((a-1/2)*r+ε) := by
    dsimp [D]
    rw [←Real.rpow_mul hUp.le]
    apply Real.rpow_le_rpow_of_exponent_le hU
    have hxi : ξ*(R+1)=ε := by dsimp [ξ]; field_simp
    nlinarith [mul_nonneg (show 0≤a-1/2 by linarith) hr,
      mul_le_mul_of_nonneg_right hrR hξ.le]
  have he' : ‖HeckePrimeDyadic.polynomial (χ k) (PrimeLogProfile.profile W (1/Real.log D)) D σ freq-
      primePolynomial (χ k) W B D σ freq‖≤E*U^((a-1/2)*r+ε) := by
    apply he.trans
    calc
      _ = E*D^ξ := by dsimp [E]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hE.le
  calc
    _ ≤ ‖HeckePrimeDyadic.polynomial (χ k) (PrimeLogProfile.profile W (1/Real.log D)) D σ freq‖+
        ‖HeckePrimeDyadic.polynomial (χ k) (PrimeLogProfile.profile W (1/Real.log D)) D σ freq-
          primePolynomial (χ k) W B D σ freq‖ := by
      have hid : primePolynomial (χ k) W B D σ freq =
          HeckePrimeDyadic.polynomial (χ k) (PrimeLogProfile.profile W (1/Real.log D)) D σ freq-
          (HeckePrimeDyadic.polynomial (χ k) (PrimeLogProfile.profile W (1/Real.log D)) D σ freq-
            primePolynomial (χ k) W B D σ freq) := by ring
      conv_lhs => rw [hid]
      exact norm_sub_le _ _
    _ ≤ Cp*U^((a-1/2)*r+ε)+E*U^((a-1/2)*r+ε) := add_le_add hp he'
    _ = _ := by ring

end SevenEighths.HeckePrimeAnnular

end

end OAI
end OAIOriginalModule2093

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.PrimeRay
Source SHA256: 262e079333d693fb895b4e64a929838af480c378e0e39b3e59de73a51436ed00
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2094




namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.HeckePrimeRay
open HeckeFamily HeckePrimeAnnular
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def twistedFamily (η : Character) (θ : RayQuotient.Characters M H) : Character :=
  η.product (HeckeRayQuotient.character M H hH θ)

def rayPrimePolynomial (η : Character) (W : ℝ→ℂ) (b D σ freq : ℝ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ))*∑ I∈(annulusSet b D).filter
    (fun I => Prime I ∧ I∈RayQuotient.identityClass M H),
      idealCoeff η I*annularWeight W D σ freq I

theorem finite_average (η : Character) (S : Finset (Ideal O)) (f : Ideal O→ℂ) :
    (∑ I∈S.filter (fun I => I∈RayQuotient.identityClass M H), idealCoeff η I*f I) =
      (RayQuotient.classNumber M H : ℂ)⁻¹ *
        ∑ θ : RayQuotient.Characters M H, ∑ I∈S,
          idealCoeff (twistedFamily M H hH η θ) I*f I := by
  rw [Finset.sum_filter,Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  simp only [twistedFamily,idealCoeff_product]
  have hs : (∑ θ : RayQuotient.Characters M H,
      idealCoeff η I*idealCoeff (HeckeRayQuotient.character M H hH θ) I*f I) =
      (idealCoeff η I*f I)*∑ θ : RayQuotient.Characters M H,
        idealCoeff (HeckeRayQuotient.character M H hH θ) I := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro θ _
    ring
  rw [hs,mul_left_comm,HeckeRayQuotient.average_idealCoeff M H hH I]
  split_ifs <;> simp

theorem rayPrimePolynomial_eq_average (η : Character) (W : ℝ→ℂ) (b D σ freq : ℝ) :
    rayPrimePolynomial M H η W b D σ freq =
      (RayQuotient.classNumber M H : ℂ)⁻¹ *
        ∑ θ : RayQuotient.Characters M H,
          primePolynomial (twistedFamily M H hH η θ) W b D σ freq := by
  unfold rayPrimePolynomial
  have hfilter : (annulusSet b D).filter (fun I => Prime I ∧ I∈RayQuotient.identityClass M H) =
      ((annulusSet b D).filter Prime).filter (fun I => I∈RayQuotient.identityClass M H) := by
    ext I
    simp only [Finset.mem_filter]
    tauto
  rw [hfilter,finite_average M H hH η _ (annularWeight W D σ freq)]
  simp only [primePolynomial]
  rw [←Finset.mul_sum]
  ring

theorem rayPrimePolynomial_norm_le (η : Character) (W : ℝ→ℂ) (b D σ freq C : ℝ)
    (hbound : ∀ θ : RayQuotient.Characters M H,
      ‖primePolynomial (twistedFamily M H hH η θ) W b D σ freq‖≤C) :
    ‖rayPrimePolynomial M H η W b D σ freq‖≤C := by
  rw [rayPrimePolynomial_eq_average M H hH η W b D σ freq,norm_mul,norm_inv]
  have hcard : (0 : ℝ)<RayQuotient.classNumber M H := by
    exact_mod_cast RayQuotient.classNumber_pos M H
  have heq : Fintype.card (RayQuotient.Characters M H)=RayQuotient.classNumber M H :=
    RayOrthogonality.card_characters H
  have hn : ‖(RayQuotient.classNumber M H : ℂ)‖=(RayQuotient.classNumber M H : ℝ) := by simp
  rw [hn]
  calc
    _ ≤ (RayQuotient.classNumber M H : ℝ)⁻¹ *
        ∑ θ : RayQuotient.Characters M H, C :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun θ _ => hbound θ)))
        (by positivity)
    _ = C := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,heq]; rw [←mul_assoc,inv_mul_cancel₀ hcard.ne',one_mul]

theorem ray_prime_bin_bound (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmax τ ε e κ η σmin σmax : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε) (he : 0<e)
    (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*R+κ≤ε) :
    ∃ C : ℝ, 0<C ∧ ∀ Z d : ℝ, 1≤Z → 0≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ (ηrow : Character) (hχ : ∀ θ : RayQuotient.Characters M H,
      (twistedFamily M H hH ηrow θ).residue≠1)
      (a : ℝ) (i : ℕ), 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum (twistedFamily M H hH ηrow) hχ (3*(i+1 : ℕ)*Z^τ)<a+2*e →
    ∀ r σ freq : ℝ, 0≤r → r≤R → σmin≤σ → σ≤σmax →
      2*(|Real.log A|+|Real.log B|)+1≤Real.log ((Z^d)^r) →
      (∀ θ : RayQuotient.Characters M H,
        (twistedFamily M H hH ηrow θ).modulus.absNorm≤Z^d) →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
      ‖rayPrimePolynomial M H ηrow W B ((Z^d)^r) σ freq‖≤
        C*(Z^d)^((a-1/2)*r+ε) := by
  obtain ⟨C,hC,hbound⟩ := prime_bin_bound W A B hA hWs hW
    R dmax τ ε e κ η σmin σmax hR hdmax hτ hε he he' hκ hη hbudget
  refine ⟨C,hC,?_⟩
  intro Z d hZ hd hd' hU hT ηrow hχ a i ha ha' hmax r σ freq hr hrR
    hσmin hσmax hlarge hQ hfreq hheight
  apply rayPrimePolynomial_norm_le M H hH
  intro θ
  exact hbound Z d hZ hd hd' hU hT (twistedFamily M H hH ηrow) hχ a i ha ha' hmax
    r σ freq hr hrR hσmin hσmax hlarge θ (hQ θ) hfreq hheight

end SevenEighths.HeckePrimeRay

end

end OAI
end OAIOriginalModule2094

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.PrimeAmplitudeBins
Source SHA256: fe9012a1add7ab3b15376230ad41e10e89e8620c0fb507b6f7da200e7fe86ae6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2095



namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckePrimeAmplitudeBins

def amplitude (P cap mesh : ℝ) (Q : ℂ) : ℝ :=
  if Q=0 then 0 else min cap (max 0 (mesh*(⌊Real.log ‖Q‖/(mesh*Real.log P)⌋ : ℤ)))

theorem amplitude_bounds (P cap mesh : ℝ) (Q : ℂ) (hcap : 0≤cap) :
    0≤amplitude P cap mesh Q ∧ amplitude P cap mesh Q≤cap := by
  unfold amplitude
  split_ifs
  · exact ⟨le_rfl,hcap⟩
  · exact ⟨le_min hcap (le_max_left _ _),min_le_left _ _⟩

theorem amplitude_upper (P cap mesh : ℝ) (Q : ℂ) (hP : 1<P) (hm : 0<mesh)
    (hbound : ‖Q‖≤P^(cap+mesh)) :
    ‖Q‖≤P^(amplitude P cap mesh Q+mesh) := by
  by_cases hQ : Q=0
  · subst Q
    simp only [norm_zero,amplitude,ite_true,zero_add]
    exact Real.rpow_nonneg (by linarith) _
  have hx : 0<‖Q‖ := norm_pos_iff.mpr hQ
  have hl : 0<Real.log P := Real.log_pos hP
  have hd : 0<mesh*Real.log P := mul_pos hm hl
  let n : ℤ := ⌊Real.log ‖Q‖/(mesh*Real.log P)⌋
  by_cases hc : cap≤max 0 (mesh*(n : ℝ))
  · simpa [amplitude,hQ,n,min_eq_left hc] using hbound
  · have he : amplitude P cap mesh Q=max 0 (mesh*(n : ℝ)) := by
      simp only [amplitude,ite_eq_right hQ]
      exact min_eq_right (le_of_not_ge hc)
    rw [he]
    apply (Real.le_rpow_iff_log_le hx (by linarith : 0<P)).mpr
    have hn : Real.log ‖Q‖/(mesh*Real.log P)<(n : ℝ)+1 := Int.lt_floor_add_one _
    have hn' := (div_lt_iff₀ hd).mp hn
    have hg := mul_le_mul_of_nonneg_right (le_max_right 0 (mesh*(n : ℝ))) hl.le
    nlinarith

theorem amplitude_lower (P cap mesh : ℝ) (Q : ℂ) (hP : 1<P) (hm : 0<mesh)
    (hg : 0<amplitude P cap mesh Q) :
    P^(amplitude P cap mesh Q)≤‖Q‖ := by
  have hQ : Q≠0 := by intro h; simp [amplitude,h] at hg
  have hx : 0<‖Q‖ := norm_pos_iff.mpr hQ
  have hl : 0<Real.log P := Real.log_pos hP
  have hd : 0<mesh*Real.log P := mul_pos hm hl
  let n : ℤ := ⌊Real.log ‖Q‖/(mesh*Real.log P)⌋
  have hpos : 0<mesh*(n : ℝ) := by
    have hmin : amplitude P cap mesh Q≤max 0 (mesh*(n : ℝ)) := by
      simp only [amplitude,ite_eq_right hQ]
      exact min_le_right _ _
    have ht : 0<max 0 (mesh*(n : ℝ)) := hg.trans_le hmin
    exact (lt_max_iff.mp ht).resolve_left (lt_irrefl _)
  have he : amplitude P cap mesh Q=min cap (mesh*(n : ℝ)) := by
    simp only [amplitude,ite_eq_right hQ]
    rw [max_eq_right hpos.le]
  have hn : (n : ℝ)≤Real.log ‖Q‖/(mesh*Real.log P) := Int.floor_le _
  have hn' := (le_div_iff₀ hd).mp hn
  have hb : amplitude P cap mesh Q*Real.log P≤Real.log ‖Q‖ := by
    rw [he]
    have hh := mul_le_mul_of_nonneg_right (min_le_right cap (mesh*(n : ℝ))) hl.le
    nlinarith
  have hpow : 0<P^(amplitude P cap mesh Q) := Real.rpow_pos_of_pos (by linarith) _
  apply (Real.log_le_log_iff hpow hx).mp
  rw [Real.log_rpow (by linarith : 0<P)]
  exact hb

def labels (cap mesh : ℝ) : Finset ℝ :=
  insert 0 (insert cap ((Finset.Icc (0 : ℤ) ⌈cap/mesh⌉).image (fun n : ℤ => mesh*(n : ℝ))))

theorem amplitude_mem_labels (P cap mesh : ℝ) (Q : ℂ) (hm : 0<mesh) :
    amplitude P cap mesh Q∈labels cap mesh := by
  by_cases hQ : Q=0
  · simp [amplitude,hQ,labels]
  let n : ℤ := ⌊Real.log ‖Q‖/(mesh*Real.log P)⌋
  have he : amplitude P cap mesh Q=min cap (max 0 (mesh*(n : ℝ))) := by
    simp only [amplitude,ite_eq_right hQ]
    rfl
  rw [he]
  by_cases hc : cap≤max 0 (mesh*(n : ℝ))
  · rw [min_eq_left hc]
    simp [labels]
  rw [min_eq_right (le_of_not_ge hc)]
  by_cases hn : mesh*(n : ℝ)≤0
  · rw [max_eq_left hn]
    simp [labels]
  have hn' : 0<mesh*(n : ℝ) := lt_of_not_ge hn
  rw [max_eq_right hn'.le]
  apply Finset.mem_insert_of_mem
  apply Finset.mem_insert_of_mem
  apply Finset.mem_image.mpr
  refine ⟨n,Finset.mem_Icc.mpr ⟨?_,?_⟩,rfl⟩
  · have hh : (0 : ℝ)≤(n : ℝ) := by nlinarith
    exact_mod_cast hh
  · have hh : (n : ℝ)≤cap/mesh := by
      apply (le_div_iff₀ hm).mpr
      have hlt : max 0 (mesh*(n : ℝ))<cap := lt_of_not_ge hc
      have : mesh*(n : ℝ)≤max 0 (mesh*(n : ℝ)) := le_max_right _ _
      nlinarith
    exact_mod_cast hh.trans (Int.le_ceil _)

theorem squared_spike (U w cap mesh : ℝ) (Q : ℂ) (hU : 1<U) (hw : 0<w)
    (hm : 0<mesh) (hg : 0<amplitude (U^w) cap mesh Q) :
    U^(2*w*amplitude (U^w) cap mesh Q)≤‖Q‖^2 := by
  have hP : 1<U^w := Real.one_lt_rpow hU hw
  have hb := amplitude_lower (U^w) cap mesh Q hP hm hg
  have hs := (sq_le_sq₀ (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _) (norm_nonneg _)).mpr hb
  convert hs using 1
  rw [←Real.rpow_natCast,←Real.rpow_mul (Real.rpow_nonneg (by linarith : (0 : ℝ)≤U) _),
    ←Real.rpow_mul (by linarith : (0 : ℝ)≤U)]
  congr 1
  ring

theorem product_upper {ι : Type*} (slots : Finset ι) (w : ι→ℝ) (Q : ι→ℂ)
    (U cap mesh : ℝ) (hU : 1<U) (hm : 0<mesh)
    (hw : ∀ i∈slots, 0<w i)
    (hQ : ∀ i∈slots, ‖Q i‖≤(U^(w i))^(cap+mesh)) :
    ‖∏ i∈slots, Q i‖≤U^((∑ i∈slots, w i*amplitude (U^(w i)) cap mesh (Q i))+
      mesh*(∑ i∈slots,w i)) := by
  rw [norm_prod]
  calc
    _ ≤ ∏ i∈slots, (U^(w i))^(amplitude (U^(w i)) cap mesh (Q i)+mesh) :=
      Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i hi =>
        amplitude_upper _ cap mesh (Q i) (Real.one_lt_rpow hU (hw i hi)) hm (hQ i hi))
    _ = ∏ i∈slots, U^(w i*(amplitude (U^(w i)) cap mesh (Q i)+mesh)) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (Real.rpow_mul (by linarith : (0 : ℝ)≤U) _ _).symm
    _ = _ := by
      rw [←Real.rpow_sum_of_pos (by linarith : 0<U)]
      congr 1
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib,←Finset.sum_mul, mul_comm mesh]

theorem common_bin_selection {ι : Type*} (slots : Finset ι) (w g : ι→ℝ)
    (U δ mesh binWidth q z : ℝ) (hU : 1<U) (hδ : 0≤δ) (hmesh : 0≤mesh)
    (hbin : 0<binWidth) (hw : ∀ i∈slots, 0<w i) (hwm : ∀ i∈slots, w i≤mesh)
    (hg : ∀ i∈slots, 0≤g i ∧ g i≤δ/2)
    (hq : 0≤q) (hqδ : q≤δ/2) (hz : 0≤z)
    (hzs : z≤∑ i∈slots,w i) (hmean : q*(∑ i∈slots,w i)≤∑ i∈slots,w i*g i) :
    ∃ T : Finset ι, T⊆slots ∧ (∀ i∈T,0<g i) ∧ (∑ i∈T,w i)≤z ∧
      ∀ Q : ι→ℂ, (∀ i∈slots,amplitude (U^(w i)) (δ/2) binWidth (Q i)=g i) →
        U^(2*q*z-δ*mesh)≤‖∏ i∈T,Q i‖^2 := by
  have hm : q*(∑ i∈slots,w i)≤∑ i∈slots,w i*max (g i) 0 := by
    convert hmean using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [max_eq_left (hg i hi).1]
  obtain ⟨T,hTs,hTp,hTw,hTb⟩ := HeckeDetectorSlotSelection.selected_product_spike
    slots w g U δ mesh q z hU.le hδ hmesh (fun i hi => (hw i hi).le) hwm
    (fun i hi => (hg i hi).2) hq hqδ hz hzs hm
  refine ⟨T,hTs,hTp,hTw,?_⟩
  intro Q hQ
  apply hTb Q
  intro i hi hgi
  rw [←hQ i hi] at hgi ⊢
  exact squared_spike U (w i) (δ/2) binWidth (Q i) hU (hw i hi) hbin hgi

end SevenEighths.HeckePrimeAmplitudeBins

end

end OAI
end OAIOriginalModule2095

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.PrimeAmplitudeScale
Source SHA256: c192c92fb5a91c7cda09833ec5c417f0a83ca1054cbce718cbbadc225aec8b8e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2096



namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace SevenEighths.HeckePrimeAmplitudeBins

theorem upper_allowance_eventually (C dmin rmin ε mesh : ℝ)
    (hd : 0<dmin) (hmesh : 0<mesh) (hgap : ε<rmin*mesh) :
    ∀ᶠ Z : ℝ in atTop, ∀ d r cap : ℝ, dmin≤d → rmin≤r →
      C*(Z^d)^(cap*r+ε)≤((Z^d)^r)^(cap+mesh) := by
  have hh := HeckeDyadic.constant_absorbed_eventually C (dmin*(rmin*mesh-ε))
    (mul_pos hd (by linarith))
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hC hZ
  intro d r cap hd' hr'
  have hZp : 0<Z := by linarith
  have hU : 0<Z^d := Real.rpow_pos_of_pos hZp _
  have hgr : rmin*mesh-ε≤r*mesh-ε := by nlinarith
  have hexp : dmin*(rmin*mesh-ε)≤d*(r*mesh-ε) :=
    mul_le_mul hd' hgr (by linarith) (hd.trans_le hd').le
  have hc : C≤(Z^d)^(r*mesh-ε) := by
    apply hC.trans
    rw [←Real.rpow_mul hZp.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ hexp
  calc
    _ ≤ (Z^d)^(r*mesh-ε)*(Z^d)^(cap*r+ε) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hU.le _)
    _ = ((Z^d)^r)^(cap+mesh) := by
      rw [←Real.rpow_add hU,←Real.rpow_mul hU.le]
      congr 1
      ring

theorem actual_bins_eventually (C dmin rmin ε mesh : ℝ)
    (hd : 0<dmin) (hr : 0<rmin) (hmesh : 0<mesh) (hgap : ε<rmin*mesh) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → ∀ r cap : ℝ, rmin≤r → 0≤cap →
      ∀ Q : ℂ, ‖Q‖≤C*(Z^d)^(cap*r+ε) →
      0≤amplitude ((Z^d)^r) cap mesh Q ∧
      amplitude ((Z^d)^r) cap mesh Q≤cap ∧
      amplitude ((Z^d)^r) cap mesh Q∈labels cap mesh ∧
      ‖Q‖≤((Z^d)^r)^(amplitude ((Z^d)^r) cap mesh Q+mesh) ∧
      (0<amplitude ((Z^d)^r) cap mesh Q →
        (Z^d)^(2*r*amplitude ((Z^d)^r) cap mesh Q)≤‖Q‖^2) := by
  filter_upwards [upper_allowance_eventually C dmin rmin ε mesh hd hmesh hgap,
    eventually_gt_atTop (1 : ℝ)] with Z hallow hZ
  intro d hd' r cap hr' hcap Q hQ
  have hU : 1<Z^d := Real.one_lt_rpow hZ (hd.trans_le hd')
  have hP : 1<(Z^d)^r := Real.one_lt_rpow hU (hr.trans_le hr')
  have hb := amplitude_bounds ((Z^d)^r) cap mesh Q hcap
  exact ⟨hb.1,hb.2,amplitude_mem_labels _ cap mesh Q hmesh,
    amplitude_upper _ cap mesh Q hP hmesh (hQ.trans (hallow d r cap hd' hr')),
    squared_spike (Z^d) r cap mesh Q hU (hr.trans_le hr') hmesh⟩

end SevenEighths.HeckePrimeAmplitudeBins

end

end OAI
end OAIOriginalModule2096

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.PrimeRow
Source SHA256: a19dbab6d87b075b90f272b819e8ce37e744284c92e9a25a806480cfc0bc1f28
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2097




namespace OAI

noncomputable section
open scoped Classical ComplexConjugate BigOperators
namespace SevenEighths.HeckePrimeRow
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem identityClass_coprime {I : Ideal O} (hI : I∈RayQuotient.identityClass M H) :
    IsCoprime I M := by
  obtain ⟨hI,a,ha,u,hu,huH⟩ := hI
  rw [←ha]
  exact (IdealCharacter.isUnit_mk_iff_isCoprime M a).mp (hu ▸ u.isUnit)

omit [NeZero M] in
theorem identityClass_coprime_larger {I J : Ideal O}
    (hI : I∈RayQuotient.identityClass M H) (hMJ : M≤J) : IsCoprime I J := by
  rw [Ideal.isCoprime_iff_sup_eq]
  apply top_unique
  rw [←Ideal.isCoprime_iff_sup_eq.mp (identityClass_coprime M H hI)]
  exact sup_le_sup_left hMJ I

omit [NeZero M] in
theorem identityClass_prime_good (m : O) (hmLam : λ₀∣m) (hMm : M≤Ideal.span {m})
    (P : Ideal O) [P.IsMaximal] (hP : P∈RayQuotient.identityClass M H) : λ₀∉P := by
  have hm : m∉P := (SixthPowerAverage.prime_coprime_span_iff P m).mp
    (identityClass_coprime_larger M H hP hMm)
  intro hLam
  obtain ⟨a,rfl⟩ := hmLam
  exact hm (P.mul_mem_right a hLam)

include hH in
theorem identityClass_principal_coeff {I : Ideal O} (hI : I∈RayQuotient.identityClass M H) :
    idealCoeff (HeckeRayFamily.character M 1) I=1 := by
  have hc := identityClass_coprime M H hI
  change RayQuotient.idealCharacter M H hH 1 I=1
  rw [RayQuotient.idealCharacter_one M H hH I,ite_eq_right hI.1,ite_eq_left hc]

include hH in
theorem exists_actual_prime_row (m u : O) (hm : m≠0) (hu : u≠0)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m) (hMm : M≤Ideal.span {m}) :
    ∃ χ : Character, χ.modulus.absNorm≤rowConductorBound (HeckeRayFamily.character M 1) m 1 u ∧
      ∀ (P : Ideal O) [P.IsMaximal] (hg : λ₀∉P),
      P∈RayQuotient.identityClass M H →
      idealCoeff χ P = starRingEnd ℂ
        (CompletedGauss.actualSextic P hg (Ideal.Quotient.mk P u)) := by
  obtain ⟨χ,hbound,hχ⟩ := exists_row_character_with_conductor (HeckeRayFamily.character M 1) m 1 u hm one_ne_zero hu hmLam hm2
  refine ⟨χ.inverse,hbound,?_⟩
  intro P _ hg hP
  have hc : IsCoprime P (Ideal.span {m}) := by
    rw [Ideal.isCoprime_iff_sup_eq] at ⊢
    apply top_unique
    rw [←Ideal.isCoprime_iff_sup_eq.mp (identityClass_coprime M H hP)]
    exact sup_le_sup_left hMm P
  rw [idealCoeff_inverse_conj,idealCoeff_eq_row _ χ m 1 u hχ,
    identityClass_principal_coeff M H hH hP,one_mul,one_pow,mul_one,
    idealRowHom_argument_mul,idealRowHom_prime_sixth_mask m P hg,ite_eq_left hc,one_mul,
    idealRowHom_prime u P hg]

def canonicalPrimeAmplitude (u : O) (W : ℝ→ℂ) (b D : ℝ) (z : ℂ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ))*∑ P∈(HeckePrimeAnnular.annulusSet b D).filter
    (fun P => Prime P ∧ P∈RayQuotient.identityClass M H),
    starRingEnd ℂ (idealRowHom u P)*W ((P.absNorm : ℝ)/D)*
      (((P.absNorm : ℝ)/D : ℝ) : ℂ)^(z-1)

include hH in

theorem exists_amplitude_character (m u : O) (hm : m≠0) (hu : u≠0)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m) (hMm : M≤Ideal.span {m}) :
    ∃ χ : Character, χ.modulus.absNorm≤rowConductorBound (HeckeRayFamily.character M 1) m 1 u ∧
      ∀ (W : ℝ→ℂ) (b D : ℝ) (z : ℂ),
        canonicalPrimeAmplitude M H u W b D z =
          HeckePrimeRay.rayPrimePolynomial M H χ W b D (1-z.re) z.im := by
  obtain ⟨χ,hbound,hχ⟩ := exists_actual_prime_row M H hH m u hm hu hmLam hm2 hMm
  refine ⟨χ,hbound,?_⟩
  intro W b D z
  unfold canonicalPrimeAmplitude HeckePrimeRay.rayPrimePolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  obtain ⟨_,hprime,hclass⟩ := Finset.mem_filter.mp hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  have hg := identityClass_prime_good M H m hmLam hMm P hclass
  have hc := hχ P hg hclass
  rw [←idealRowHom_prime u P hg] at hc
  rw [hc]
  have he : -HeckeDyadic.shift (1-z.re) z.im=z-1 := by
    apply Complex.ext <;> simp [HeckeDyadic.shift]
  simp only [HeckePrimeAnnular.annularWeight,he]
  ring

end SevenEighths.HeckePrimeRow

end

end OAI
end OAIOriginalModule2097

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.PrimeNonprincipal
Source SHA256: b831d55708c640f42f4bdb5f78cf0074af4fc134cb974e3b94a6b8b6ee1e11d9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2098



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckePrimeNonprincipal
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem inverse_twist_elementCoeff (η χ θ : Character) (m f z : O)
    (hχ : ∀ n, elementCoeff χ n=rowTwist (elementHom η) m f z n) (n : O) :
    elementCoeff ((χ.inverse.product θ).inverse) n =
      rowTwist (elementHom (η.product θ.inverse)) m f z n := by
  rw [elementCoeff_inverse,elementCoeff_product,elementCoeff_inverse,mul_inv_rev,inv_inv,hχ]
  change _ = elementCoeff (η.product θ.inverse) n * idealRowHom (m^6*f^4*z) (Ideal.span {n})
  rw [elementCoeff_product,elementCoeff_inverse]
  change (elementCoeff θ n)⁻¹ *
    (elementCoeff η n * idealRowHom (m^6*f^4*z) (Ideal.span {n})) = _
  ring

theorem twisted_nonprincipal (η χ θ : Character) (m f z : O)
    (hχ : ∀ n, elementCoeff χ n=rowTwist (elementHom η) m f z n)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀^2∣r-1) (hx : f^4*z=(u : O)*λ₀^a*(2 : O)^b*r)
    (P J : Ideal O) [P.IsMaximal] (hg : λ₀∉P) (hchar : ringChar (O ⧸ P)≠2)
    (hJ : CanonicalQuadraticSieve.Supported J) {c : ℕ} (hc : 1≤c) (hc6 : ¬6∣c)
    (hsplit : Ideal.span {r}=P^c*J)
    (hcop : IsCoprime (((η.product θ.inverse).modulus*Ideal.span {m}*Ideal.span {(72 : O)})*J) (P^c)) :
    (χ.inverse.product θ).residue≠1 := by
  have hn := HeckeRowNonprincipal.actual_row_nonprincipal (η.product θ.inverse)
    ((χ.inverse.product θ).inverse) m f z hmLam hm2 u a b r hr hpr hx P J hg hchar hJ
    hc hc6 hsplit hcop (inverse_twist_elementCoeff η χ θ m f z hχ)
  intro h
  apply hn
  change (χ.inverse.product θ).residue⁻¹=1
  rw [h,inv_one]

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem fixed_twist_modulus (θ : RayQuotient.Characters M H) :
    ((HeckeRayFamily.character M 1).product
      (HeckeRayQuotient.character M H hH θ).inverse).modulus=M := by
  change M⊓M=M
  simp

theorem fixed_ray_twisted_nonprincipal (χ : Character) (m f z : O)
    (hχ : ∀ n, elementCoeff χ n=rowTwist (elementHom (HeckeRayFamily.character M 1)) m f z n)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀^2∣r-1) (hx : f^4*z=(u : O)*λ₀^a*(2 : O)^b*r)
    (P J : Ideal O) [P.IsMaximal] (hg : λ₀∉P) (hchar : ringChar (O ⧸ P)≠2)
    (hJ : CanonicalQuadraticSieve.Supported J) {c : ℕ} (hc : 1≤c) (hc6 : ¬6∣c)
    (hsplit : Ideal.span {r}=P^c*J)
    (hcop : IsCoprime ((M*Ideal.span {m}*Ideal.span {(72 : O)})*J) (P^c))
    (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH χ.inverse θ).residue≠1 := by
  apply twisted_nonprincipal (HeckeRayFamily.character M 1) χ
    (HeckeRayQuotient.character M H hH θ) m f z hχ hmLam hm2 u a b r hr hpr hx
    P J hg hchar hJ hc hc6 hsplit
  rwa [fixed_twist_modulus M H hH θ]

end SevenEighths.HeckePrimeNonprincipal

end

end OAI
end OAIOriginalModule2098

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.PrimeScale
Source SHA256: a8e153a9a63be08a449498fce4fce1665fe50a605feb1d9ce6cc9aa700d74a64
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2099



namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace SevenEighths.HeckePrimeScale
open HeckeFamily

theorem log_scale_eventually (dmin rmin K : ℝ) (hd : 0<dmin) (hr : 0<rmin) :
    ∀ᶠ Z : ℝ in atTop, ∀ d r : ℝ, dmin≤d → rmin≤r →
      K≤Real.log ((Z^d)^r) := by
  have hlog : ∀ᶠ Z : ℝ in atTop, max 0 (K/(dmin*rmin))≤Real.log Z :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hlog,eventually_ge_atTop (1 : ℝ)] with Z hlog hZ
  intro d r hd' hr'
  have hZp : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  rw [Real.log_rpow (Real.rpow_pos_of_pos hZp _),Real.log_rpow hZp]
  have hp : 0<dmin*rmin := mul_pos hd hr
  have hk : K≤dmin*rmin*Real.log Z := by
    have hh := (div_le_iff₀ hp).mp ((le_max_right 0 _).trans hlog)
    nlinarith
  have hprod : dmin*rmin≤d*r := mul_le_mul hd' hr' hr.le (hd.trans_le hd').le
  have hl : 0≤Real.log Z := (le_max_left _ _).trans hlog
  nlinarith [mul_le_mul_of_nonneg_right hprod hl]

theorem product_modulus_bound (χ ψ : Character) :
    (χ.product ψ).modulus.absNorm≤χ.modulus.absNorm*ψ.modulus.absNorm := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Finite (O ⧸ ψ.modulus) := Ring.HasFiniteQuotients.finiteQuotient ψ.modulus_ne_bot
  exact FiniteConductor.absNorm_inf_le_mul χ.modulus ψ.modulus

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem twisted_modulus_bound (χ : Character) (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH χ θ).modulus.absNorm≤χ.modulus.absNorm*M.absNorm :=
  product_modulus_bound χ (HeckeRayQuotient.character M H hH θ)

theorem twisted_row_modulus_bound (χ : Character) (m u : O)
    (hχ : χ.modulus.absNorm≤HeckeRowClosure.rowConductorBound (HeckeRayFamily.character M 1) m 1 u)
    (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH χ θ).modulus.absNorm≤
      M.absNorm^2*(Ideal.span {m}).absNorm*(Ideal.span {(72 : O)}).absNorm*(Ideal.span {u}).absNorm := by
  apply (twisted_modulus_bound M H hH χ θ).trans
  have hn := Nat.mul_le_mul_right M.absNorm hχ
  simpa [HeckeRowClosure.rowConductorBound,HeckeRayFamily.character,
    Character.ofResidue,pow_two,mul_assoc,mul_left_comm,mul_comm] using hn

end SevenEighths.HeckePrimeScale

end

end OAI
end OAIOriginalModule2099

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorPrimeFamily
Source SHA256: c0b3ade88e0c84f1739e4ee55ed9cc45cfc22fc5a16c18b93d3def57693782ec
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2100




namespace OAI

noncomputable section
open scoped Classical ComplexConjugate BigOperators
namespace SevenEighths.HeckeDetectorPrimeFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

structure RowData (M : Ideal O) where
  m : O
  u : O
  m_ne_zero : m≠0
  u_ne_zero : u≠0
  lambda_dvd : λ₀∣m
  two_dvd : (2 : O)∣m
  modulus_le : M≤Ideal.span {m}

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

def RowData.base (data : RowData M) : Character :=
  Classical.choose (exists_row_character_with_conductor (HeckeRayFamily.character M 1)
    data.m 1 data.u data.m_ne_zero one_ne_zero data.u_ne_zero data.lambda_dvd data.two_dvd)

theorem RowData.base_spec (data : RowData M) (n : O) :
    elementCoeff (data.base M) n=
      rowTwist (elementHom (HeckeRayFamily.character M 1)) data.m 1 data.u n :=
  (Classical.choose_spec (exists_row_character_with_conductor (HeckeRayFamily.character M 1)
    data.m 1 data.u data.m_ne_zero one_ne_zero data.u_ne_zero data.lambda_dvd data.two_dvd)).2 n

theorem RowData.base_conductor (data : RowData M) :
    (data.base M).modulus.absNorm≤rowConductorBound (HeckeRayFamily.character M 1) data.m 1 data.u :=
  (Classical.choose_spec (exists_row_character_with_conductor (HeckeRayFamily.character M 1)
    data.m 1 data.u data.m_ne_zero one_ne_zero data.u_ne_zero data.lambda_dvd data.two_dvd)).1

def RowData.character (data : RowData M) : Character := (data.base M).inverse

variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

include hH in
theorem RowData.coefficient_on_ray (data : RowData M) (P : Ideal O) [P.IsMaximal]
    (hg : λ₀∉P) (hP : P∈RayQuotient.identityClass M H) :
    idealCoeff (data.character M) P=starRingEnd ℂ (idealRowHom data.u P) := by
  have hc := HeckePrimeRow.identityClass_coprime_larger M H hP data.modulus_le
  rw [RowData.character,idealCoeff_inverse_conj,
    idealCoeff_eq_row _ (data.base M) data.m 1 data.u (data.base_spec M),
    HeckePrimeRow.identityClass_principal_coeff M H hH hP,one_mul,one_pow,mul_one,
    idealRowHom_argument_mul,idealRowHom_prime_sixth_mask data.m P hg,ite_eq_left hc,one_mul]

include hH in
theorem RowData.amplitude_eq (data : RowData M) (W : ℝ→ℂ) (b D : ℝ) (z : ℂ) :
    HeckePrimeRow.canonicalPrimeAmplitude M H data.u W b D z=
      HeckePrimeRay.rayPrimePolynomial M H (data.character M) W b D (1-z.re) z.im := by
  unfold HeckePrimeRow.canonicalPrimeAmplitude HeckePrimeRay.rayPrimePolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  obtain ⟨_,hprime,hclass⟩ := Finset.mem_filter.mp hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  have hg := HeckePrimeRow.identityClass_prime_good M H data.m data.lambda_dvd data.modulus_le P hclass
  rw [data.coefficient_on_ray M H hH P hg hclass]
  have he : -HeckeDyadic.shift (1-z.re) z.im=z-1 := by
    apply Complex.ext <;> simp [HeckeDyadic.shift]
  simp only [HeckePrimeAnnular.annularWeight,he]
  ring

theorem RowData.twisted_conductor (data : RowData M) (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH (data.character M) θ).modulus.absNorm≤
      M.absNorm^2*(Ideal.span {data.m}).absNorm*(Ideal.span {(72 : O)}).absNorm*
        (Ideal.span {data.u}).absNorm := by
  apply HeckePrimeScale.twisted_row_modulus_bound M H hH (data.character M) data.m data.u
  exact data.base_conductor M

theorem RowData.twisted_nonprincipal (data : RowData M)
    (unit : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀^2∣r-1) (hx : data.u=(unit : O)*λ₀^a*(2 : O)^b*r)
    (P J : Ideal O) [P.IsMaximal] (hg : λ₀∉P) (hchar : ringChar (O ⧸ P)≠2)
    (hJ : CanonicalQuadraticSieve.Supported J) {c : ℕ} (hc : 1≤c) (hc6 : ¬6∣c)
    (hsplit : Ideal.span {r}=P^c*J)
    (hcop : IsCoprime ((M*Ideal.span {data.m}*Ideal.span {(72 : O)})*J) (P^c))
    (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH (data.character M) θ).residue≠1 := by
  exact HeckePrimeNonprincipal.fixed_ray_twisted_nonprincipal M H hH (data.base M)
    data.m 1 data.u (data.base_spec M) data.lambda_dvd data.two_dvd unit a b r hr hpr
    (by simpa using hx) P J hg hchar hJ hc hc6 hsplit hcop θ

structure Ramification (data : RowData M) where
  unit : Oˣ
  lambda_power : ℕ
  two_power : ℕ
  remaining : O
  supported : CanonicalQuadraticSieve.Supported (Ideal.span {remaining})
  primary : λ₀^2∣remaining-1
  decomposition : data.u=(unit : O)*λ₀^lambda_power*(2 : O)^two_power*remaining
  prime : Ideal O
  rest : Ideal O
  maximal : prime.IsMaximal
  prime_good : λ₀∉prime
  odd : ringChar (O ⧸ prime)≠2
  rest_supported : CanonicalQuadraticSieve.Supported rest
  multiplicity : ℕ
  multiplicity_pos : 1≤multiplicity
  not_sixfold : ¬6∣multiplicity
  split : Ideal.span {remaining}=prime^multiplicity*rest
  coprime : IsCoprime ((M*Ideal.span {data.m}*Ideal.span {(72 : O)})*rest) (prime^multiplicity)

theorem Ramification.nonprincipal {data : RowData M} (cert : Ramification M data)
    (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH (data.character M) θ).residue≠1 := by
  let := cert.maximal
  exact data.twisted_nonprincipal M H hH cert.unit cert.lambda_power cert.two_power
    cert.remaining cert.supported cert.primary cert.decomposition cert.prime cert.rest cert.prime_good
    cert.odd cert.rest_supported cert.multiplicity_pos cert.not_sixfold cert.split cert.coprime θ

end SevenEighths.HeckeDetectorPrimeFamily

end

end OAI
end OAIOriginalModule2100

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorRelativePrime
Source SHA256: f3ec824537fd87cd3ccabb4a4c5c67c300c02ee8058d196415fb34d491beb814
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2101


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRelativePrime
open HeckeFamily HeckeDetectorPrimeFamily

theorem idealCoeff_ne_zero_of_coprime (ν : Character) (J : Ideal O)
    (hJ : J≠0) (hc : IsCoprime J ν.modulus) : idealCoeff ν J≠0 := by
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero J hJ
  rw [←ConcretePrimeRowBridge.span_idealGenerator J,idealCoeff_span ν hg]
  apply MulChar.apply_ne_zero_iff.mpr
  apply (IdealCharacter.isUnit_mk_iff_isCoprime ν.modulus _).mpr
  simpa only [ConcretePrimeRowBridge.span_idealGenerator] using hc

theorem idealCoeff_inverse (ν : Character) (J : Ideal O) :
    idealCoeff ν.inverse J=(idealCoeff ν J)⁻¹ := by
  by_cases hJ : J=0
  · subst J
    simp only [map_zero,inv_zero]
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero J hJ
  rw [←ConcretePrimeRowBridge.span_idealGenerator J,idealCoeff_span ν.inverse hg,
    idealCoeff_span ν hg,HeckeFamily.elementCoeff_inverse]

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem relative_coefficient_on_ray (ν χ : Character) (hM : M≤ν.modulus)
    (J : Ideal O) (hJ : J∈RayQuotient.identityClass M H) :
    idealCoeff ((ν.product χ).product ν.inverse) J=idealCoeff χ J := by
  have hn := idealCoeff_ne_zero_of_coprime ν J hJ.1
    (HeckePrimeRow.identityClass_coprime_larger M H hJ hM)
  rw [idealCoeff_product,idealCoeff_product,idealCoeff_inverse]
  field_simp

theorem physical_eq_relative_average (data : RowData M) (ν : Character)
    (hM : M≤ν.modulus) (W : ℝ→ℂ) (b D : ℝ) (z : ℂ) :
    HeckePrimeRow.canonicalPrimeAmplitude M H data.u W b D z=
      (RayQuotient.classNumber M H : ℂ)⁻¹ *
        ∑ θ : RayQuotient.Characters M H,
          HeckePrimeAnnular.primePolynomial
            ((ν.product (data.character M)).product
              (ν.inverse.product (HeckeRayQuotient.character M H hH θ)))
            W b D (1-z.re) z.im := by
  rw [data.amplitude_eq M H hH]
  have he : HeckePrimeRay.rayPrimePolynomial M H (data.character M) W b D (1-z.re) z.im=
      HeckePrimeRay.rayPrimePolynomial M H ((ν.product (data.character M)).product ν.inverse)
        W b D (1-z.re) z.im := by
    unfold HeckePrimeRay.rayPrimePolynomial
    congr 1
    apply Finset.sum_congr rfl
    intro J hJ
    rw [relative_coefficient_on_ray M H ν (data.character M) hM J (Finset.mem_filter.mp hJ).2.2]
  rw [he,HeckePrimeRay.rayPrimePolynomial_eq_average M H hH]
  congr 1
  apply Finset.sum_congr rfl
  intro θ hθ
  unfold HeckePrimeAnnular.primePolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [HeckePrimeRay.twistedFamily,idealCoeff_product]
  ring

end SevenEighths.HeckeDetectorRelativePrime

end

end OAI
end OAIOriginalModule2101

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.PrimeAmplitudeActual
Source SHA256: 4d1c7744d802cae443a1c2f6c7d71390582647370efd28d869b5f6c98e73e387
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2102



namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace SevenEighths.HeckePrimeAmplitudeActual
open HeckeFamily HeckePrimeRay HeckePrimeAmplitudeBins
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem ray_amplitude_bins (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmin dmax rmin τ ε e κ η mesh σmin σmax : ℝ)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hη : 0≤η) (hmesh : 0<mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ (χ : Character) (hχ : ∀ θ : RayQuotient.Characters M H,
      (twistedFamily M H hH χ θ).residue≠1) (a : ℝ) (i : ℕ),
      51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum (twistedFamily M H hH χ) hχ (3*(i+1 : ℕ)*Z^τ)<a+2*e →
    ∀ r σ freq : ℝ, rmin≤r → r≤R → σmin≤σ → σ≤σmax →
      (∀ θ : RayQuotient.Characters M H,(twistedFamily M H hH χ θ).modulus.absNorm≤Z^d) →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ → (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
    let Q := rayPrimePolynomial M H χ W B ((Z^d)^r) σ freq
    let g := amplitude ((Z^d)^r) (a-1/2) mesh Q
    0≤g ∧ g≤a-1/2 ∧ g∈labels (a-1/2) mesh ∧
      ‖Q‖≤((Z^d)^r)^(g+mesh) ∧ (0<g → (Z^d)^(2*r*g)≤‖Q‖^2) := by
  obtain ⟨C,hC,hbound⟩ := ray_prime_bin_bound M H hH W A B hA hWs hW
    R dmax τ ε e κ η σmin σmax hR hdmax hτ hε he he' hκ hη hbudget
  have hbins := actual_bins_eventually C dmin rmin ε mesh hdmin hrmin hmesh hgap
