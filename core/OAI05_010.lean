    hFn hRn hinv hmargin hVd hhd hd parents hparents hcard lists H hdis hmax hgood hprime hodd
    hH1 hH hprod Ψ hΨnorm hΨperiod u θ w hw
  let S := reflectionExcludedPrimes q
  let lists' := punctureLists lists S
  have hsub (i : σ) : lists' i⊆lists i := Finset.filter_subset _ _
  let w' : ∀ i,lists' i→ℂ := fun i P => w i ⟨P.val,hsub i P.property⟩
  have hh := he (σ:=σ) F hF m hm Z N V M z₀ margin hhat d hZ hN hM hMc hVc hzc hhc
    hFn hRn hinv hmargin hVd hhd hd parents hparents hcard lists' H
    (fun i j hij => (hdis hij).mono (hsub i) (hsub j))
    (fun i P hP => hmax i P (hsub i hP)) (fun i P hP => hgood i P (hsub i hP))
    (fun i P hP => hprime i P (hsub i hP)) (fun i P hP => hodd i P (hsub i hP))
    (fun i P hP => (Finset.mem_filter.mp hP).2) hH1 (fun i P hP => hH i P (hsub i hP)) hprod
    Ψ hΨnorm hΨperiod u θ w' (fun i P => hw i ⟨P.val,hsub i P.property⟩)
  apply le_trans (le_of_eq ?_) hh
  apply Finset.sum_congr rfl
  intro I hI
  exact congrArg (fun z : ℂ => ‖z‖^2) (original_completed_puncture_lists lists hprime S Ψ m
    (ConcretePrimeRowBridge.idealGenerator F) (u.val*ConcretePrimeRowBridge.idealGenerator I)
    (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat)) w)
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1178

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.CubeCompletedEnergyUniformDegree
Source SHA256: e534f3f1e6ac223bdabd462b5c3f217e478343003670f22b3254be8150ff1242
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1179



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem canonical_cube_shifted_completed_energy_uniform_degree
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar η : ℝ) (hL : 0≤L) (hcstar : 0<cstar) (hη : 0<η)
    (hη1 : η≤1) (hηc : η≤cstar/100000) (rmax : ℕ) :
    ∃ (degree : ℕ), ∀ (q : ℕ) (_hq : q≠0), ∃ (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (F : Ideal Eis) (_hF : Squarefree F)
      (m : Eis) (_hm : m≠0) (Z N V M z₀ margin hhat d : ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hhat≤L →
      (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      V≤d → hhat≤d+η → d≤cstar/200 →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^M) →
      Fintype.card σ≤rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (Hcube : Ideal Eis),Hcube≠0 → (Ideal.absNorm Hcube:ℝ)≤Z^hhat →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈parents,
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(N-3*hhat)) (fun A => ∏ i,if (p i).val∣Hcube^3*A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/64) := by
  obtain ⟨degree,hu⟩ := canonical_original_completed_energy_uniform_degree lo hi hlo W hWs hW
    L cstar η hL hcstar hη hη1 hηc rmax
  refine ⟨degree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,he⟩ := hu q hq
  let ε := cstar/(64*(L+1))
  have hε : 0<ε := by dsimp [ε];positivity
  obtain ⟨D,hD,hcube⟩ := original_cube_shifted_tuple_energy rmax ε hε
  refine ⟨D*C,Z₀,mul_pos hD hC,hZ₀,?_⟩
  intro σ _ _ F hF m hm Z N V M z₀ margin hhat d hZ hN hM hMc hVc hzc hhc
    hFn hRn hinv hmargin hVd hhd hd parents hparents hcard lists H hdis hmax hgood hprime hodd
    hH1 hH hprod Ψ hΨnorm hΨperiod Hcube hcube0 hcuben u θ w hw
  have hz1 : 1≤Z := (lt_of_lt_of_le hZ₀ hZ).le
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hz1
  have hremain (T : Finset σ) :
      (∑ I∈parents,‖∑ a : ∀ i : T,cubeAwayList Hcube (lists i.val),
        (∏ i : T,w i.val ⟨(a i).val,(Finset.mem_filter.mp (a i).property).1⟩)*
          markedCompletedT (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
            (Z^(N-3*hhat)) (fun A => ∏ i : T,if (a i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/32) := by
    have hsub (i : T) : cubeAwayList Hcube (lists i.val)⊆lists i.val := Finset.filter_subset _ _
    have hcardT : Fintype.card T≤rmax := by
      rw [Fintype.card_coe]
      exact (Finset.card_le_univ T).trans hcard
    have hprodT : (∏ i : T,H i.val)≤Z^z₀ := by
      apply le_trans ?_ hprod
      rw [Finset.prod_coe_sort]
      exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ T)
        (fun i hi => (hH1 i).trans' (by norm_num)) (fun i hi hnot => hH1 i)
    exact he (σ:=T) F hF m hm Z N V M z₀ margin hhat d hZ hN hM hMc hVc hzc hhc
      hFn hRn hinv hmargin hVd hhd hd parents hparents hcardT
      (fun i : T => cubeAwayList Hcube (lists i.val)) (fun i : T => H i.val)
      (fun i j hij => (hdis (fun he => hij (Subtype.ext he))).mono (hsub i) (hsub j))
      (fun i P hP => hmax i.val P (hsub i hP)) (fun i P hP => hgood i.val P (hsub i hP))
      (fun i P hP => hprime i.val P (hsub i hP)) (fun i P hP => hodd i.val P (hsub i hP))
      (fun i => hH1 i.val) (fun i P hP => hH i.val P (hsub i hP)) hprodT
      Ψ hΨnorm hΨperiod u θ (fun i P => w i.val ⟨P.val,hsub i P.property⟩)
      (fun i P => hw i.val ⟨P.val,hsub i P.property⟩)
  have hh := hcube Hcube hcube0 lists hmax hgood w hw hcard parents
    (fun I => rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
      (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
    (Z^(N-3*hhat)) (C*(1+‖θ‖)^degree*Z^(N+V-cstar/32)) (by positivity) hremain
  have hεcap : hhat*ε≤cstar/64 := by
    have hhε : ε*(64*(L+1))=cstar := by dsimp [ε];field_simp
    nlinarith [mul_le_mul_of_nonneg_right hhc hε.le]
  have hn : (Ideal.absNorm Hcube:ℝ)^ε≤Z^(cstar/64) := by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hcuben hε.le).trans
    rw [←Real.rpow_mul hz.le]
    exact Real.rpow_le_rpow_of_exponent_le hz1 hεcap
  apply hh.trans
  calc
    _ ≤ D*Z^(cstar/64)*(C*(1+‖θ‖)^degree*Z^(N+V-cstar/32)) := by gcongr
    _ = (D*C)*(1+‖θ‖)^degree*(Z^(cstar/64)*Z^(N+V-cstar/32)) := by ring
    _ = _ := by rw [←Real.rpow_add hz];congr 2;ring
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1179

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.ReflectedShortUniformDegree
Source SHA256: caadbb609fe195bf6fa12b604f46953c6d26c8acb33563a940596ecd7e7b70ef
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1180



namespace OAI
noncomputable section
open scoped BigOperators Classical ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open InverseTerminalWidths InverseReflectedPhase CompletedHeight
local notation "Eis"=>ActualEisensteinCubic.O
universe u v

theorem canonical_short_completed_energy_uniform_degree
    (lo hi:ℝ) (hlo:0<lo) (W:ℝ→ℂ)
    (hWs:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W)
    (L cstar eta:ℝ) (hL:0≤L) (hcstar:0<cstar) (heta:0<eta)
    (heta1:eta≤1) (hetac:eta≤cstar/100000) (rmax:ℕ):
    ∃ (degree : ℕ), ∀ (q : ℕ) (_hq : q≠0), ∃ (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀{σ:Type v} [Fintype σ] [DecidableEq σ],∀(F:Ideal Eis)(_hF:Squarefree F)
      (m:Eis)(_hm:m≠0)(Z N V M z₀ margin hcut d:ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hcut≤L →
      (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      V≤d → hcut≤d+eta → d≤cstar/200 →
    ∀(parents:Finset (Ideal Eis)),(∀I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^M) →
      Fintype.card σ≤rmax → ∀(lists:σ→Finset (Ideal Eis))(H:σ→ℝ),
      Pairwise (fun i j=>Disjoint (lists i) (lists j)) →
      (∀i,∀P∈lists i,P.IsMaximal) →
      (∀i,∀P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀i,∀P∈lists i,Prime P) → (∀i,∀P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀i,1≤H i) → (∀i,∀P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏i,H i)≤Z^z₀ →
    ∀(Ψ:Eis→*ℂ),(∀n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀(u:Eisˣ)(θ:ℝ)(w:∀i,lists i→ℂ),(∀i P,‖w i P‖≤1) →
      (∑I∈parents,‖markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
          (u.val*ConcretePrimeRowBridge.idealGenerator I)) (normTwistedSource W θ)
        (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/64)*(256*(columnDyadicLength (Z^hcut)+1:ℝ))^2 := by
  obtain ⟨degree,hu⟩ := canonical_cube_shifted_completed_energy_uniform_degree lo hi hlo W hWs hW L cstar eta hL hcstar heta heta1 hetac rmax
  refine ⟨degree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,he⟩ := hu q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ F hF m hm Z N V M z₀ margin hcut d hZ hN hM hMc hVc hzc hcutc hFn hRn
    hmargin hreserve hVd hcutd hd parents hparents hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod
    Ψ hΨ hperiod u θ w hw
  have hZ1:1<Z:=lt_of_lt_of_le hZ₀ hZ
  have hz:0<Z:=zero_lt_one.trans hZ1
  have htw:HasCompactSupport (normTwistedSource W θ):=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((normTwistedSource_support W θ).trans hWs)
  have hcompleted (J:Ideal Eis) (hJ:J∈shortCubeRange (Z^hcut)):
      (∑I∈parents,‖markedCompletedT
        (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
          (u.val*ConcretePrimeRowBridge.idealGenerator I)) (normTwistedSource W θ)
        (Z^N/(Ideal.absNorm J:ℝ)^3) (fun A=>tupleDivisibilityMark lists w (J^3*A))‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/64):=by
    obtain ⟨hJ0,hJnorm⟩:=(mem_shortCubeRange _ J).mp hJ
    have hn:0<(Ideal.absNorm J:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (fun hn=>hJ0 (Ideal.absNorm_eq_zero_iff.mp hn))
    have hc:Real.logb Z (Ideal.absNorm J:ℝ)≤hcut:=
      (Real.logb_le_iff_le_rpow hZ1 hn).mpr hJnorm.le
    have hjpow:(Ideal.absNorm J:ℝ)≤Z^(Real.logb Z (Ideal.absNorm J:ℝ)):=by
      rw [Real.rpow_logb hz (ne_of_gt hZ1) hn]
    have h:=he F hF m hm Z N V M z₀ margin (Real.logb Z (Ideal.absNorm J:ℝ)) d
      hZ hN hM hMc hVc hzc (hc.trans hcutc) hFn hRn hmargin hreserve hVd (hc.trans hcutd) hd
      parents hparents hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod Ψ hΨ hperiod J hJ0 hjpow u θ w hw
    rw [short_cube_exact_scale Z N hZ1 J hJ0] at h
    simpa only [completed_tuple_mark lists w _ _ htw _ (div_pos (Real.rpow_pos_of_pos hz _) (pow_pos hn _)) J] using h
  have hh:=marked_short_completed_energy
    (fun I:parents=>rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
      (u.val*ConcretePrimeRowBridge.idealGenerator I.val))
    (fun I n=>rowTwist_norm Ψ hΨ _ _ _ n) (fun _=>tupleDivisibilityMark lists w)
    (normTwistedSource W θ) (Z^N) (Z^hcut) (C*(1+‖θ‖)^degree*Z^(N+V-cstar/64))
    (by positivity) (fun J hJ=>by
      rw [Finset.sum_coe_sort parents (fun I:Ideal Eis=>‖markedCompletedT
        (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
          (u.val*ConcretePrimeRowBridge.idealGenerator I)) (normTwistedSource W θ)
        (Z^N/(Ideal.absNorm J:ℝ)^3) (fun A=>tupleDivisibilityMark lists w (J^3*A))‖^2)]
      exact hcompleted J hJ)
  rw [Finset.sum_coe_sort parents (fun I:Ideal Eis=>‖markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
          (u.val*ConcretePrimeRowBridge.idealGenerator I)) (normTwistedSource W θ)
        (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)] at hh
  exact hh

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule1180

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.ReflectedShortPowerUniformDegree
Source SHA256: 2b3923e0949c24c09267fb968b6636ca273ed7447d6acf76948a545a504f4c62
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1181



namespace OAI
noncomputable section
open scoped BigOperators Classical ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open InverseTerminalWidths InverseReflectedPhase CompletedHeight
local notation "Eis"=>ActualEisensteinCubic.O
universe u v

theorem canonical_short_completed_power_energy_uniform_degree
    (lo hi:ℝ) (hlo:0<lo) (W:ℝ→ℂ)
    (hWs:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W)
    (L cstar eta:ℝ) (hL:0≤L) (hcstar:0<cstar) (heta:0<eta)
    (heta1:eta≤1) (hetac:eta≤cstar/100000) (rmax:ℕ):
    ∃ (degree : ℕ), ∀ (q : ℕ) (_hq : q≠0), ∃ (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀{σ:Type v} [Fintype σ] [DecidableEq σ],∀(F:Ideal Eis)(_hF:Squarefree F)
      (m:Eis)(_hm:m≠0)(Z N V M z₀ margin hcut d:ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → 0≤hcut → hcut≤L →
      (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      V≤d → hcut≤d+eta → d≤cstar/200 →
    ∀(parents:Finset (Ideal Eis)),(∀I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^M) →
      Fintype.card σ≤rmax → ∀(lists:σ→Finset (Ideal Eis))(H:σ→ℝ),
      Pairwise (fun i j=>Disjoint (lists i) (lists j)) →
      (∀i,∀P∈lists i,P.IsMaximal) →
      (∀i,∀P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀i,∀P∈lists i,Prime P) → (∀i,∀P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀i,1≤H i) → (∀i,∀P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏i,H i)≤Z^z₀ →
    ∀(Ψ:Eis→*ℂ),(∀n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀(u:Eisˣ)(θ:ℝ)(w:∀i,lists i→ℂ),(∀i P,‖w i P‖≤1) →
      (∑I∈parents,‖markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
          (u.val*ConcretePrimeRowBridge.idealGenerator I)) (normTwistedSource W θ)
        (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/128) := by
  obtain ⟨degree,hu⟩ := canonical_short_completed_energy_uniform_degree lo hi hlo W hWs hW L cstar eta hL hcstar heta heta1 hetac rmax
  refine ⟨degree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,he⟩ := hu q hq
  obtain ⟨B,hB,hbound⟩:=short_harmonic_small_power L (cstar/128) hL (by positivity)
  refine ⟨C*B,Z₀,mul_pos hC hB,hZ₀,?_⟩
  intro σ _ _ F hF m hm Z N V M z₀ margin hcut d hZ hN hM hMc hVc hzc hcut0 hcutc hFn hRn
    hmargin hreserve hVd hcutd hd parents hparents hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod
    Ψ hΨ hperiod u θ w hw
  have hz:0<Z:=zero_lt_one.trans (lt_of_lt_of_le hZ₀ hZ)
  have hh:=he F hF m hm Z N V M z₀ margin hcut d hZ hN hM hMc hVc hzc hcutc hFn hRn
    hmargin hreserve hVd hcutd hd parents hparents hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod
    Ψ hΨ hperiod u θ w hw
  apply hh.trans
  calc
    _≤C*(1+‖θ‖)^degree*Z^(N+V-cstar/64)*(B*Z^(cstar/128)):=
      mul_le_mul_of_nonneg_left (hbound Z hcut (lt_of_lt_of_le hZ₀ hZ).le hcut0 hcutc) (by positivity)
    _=(C*B)*(1+‖θ‖)^degree*Z^(N+V-cstar/128):=by
      rw [show N+V-cstar/128=(N+V-cstar/64)+cstar/128 by ring,Real.rpow_add hz]
      ring

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule1181

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.ReflectedShortGeneratorUniformDegree
Source SHA256: a3a79bcd2414e93d6e886d5caa5e747cfdc422cd06c3bcb23760482a65aee8c8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1182



namespace OAI
noncomputable section
open scoped BigOperators Classical ContDiff
namespace SevenEighths.InverseShortCanonicalNormalization
open ActualEisensteinCubic IdealMobiusDivisorSum CompletedGauss CanonicalRowCompletion
open InverseMoment InverseReflectedPhase InverseTerminalWidths CompletedHeight
local notation "Eis" => ActualEisensteinCubic.O
universe u v

theorem canonical_short_normalized_generator_energy_uniform_degree
    (lo hi : ℝ) (hlo : 0<lo) (W : ℝ→ℂ)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar eta : ℝ) (hL : 0≤L) (hcstar : 0<cstar) (heta : 0<eta)
    (heta1 : eta≤1) (hetac : eta≤cstar/100000) (rmax K : ℕ) :
    ∃ (degree : ℕ), ∀ (q : ℕ) (_hq : q≠0), ∃ (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],
    ∀ (m : Eis) (_hm : m≠0) (Z N V M z₀ margin hcut d : ℝ),
      Z₀≤Z → 0≤N → 0≤V → 0≤M → M≤L → V≤L → z₀≤L → 0≤hcut → hcut≤L →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      V≤d → hcut≤d+eta → d≤cstar/200 →
    ∀ (labels : Finset (Ideal Eis)),
      (∀ f∈labels,Squarefree f ∧ (Ideal.absNorm f:ℝ)≤Z^V) →
    ∀ (labelGenerator : Ideal Eis→Eis),(∀ f∈labels,Ideal.span {labelGenerator f}=f) →
    ∀ (T : Finset Eis),(∀ k∈T,k≠0 ∧ (Ideal.absNorm (Ideal.span {k}):ℝ)≤Z^M) →
      Fintype.card σ≤rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) → (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ f∈labels,secondLabelWeight K f * ∑ k∈T,
        ‖((Z^(-(N+V)/2):ℝ):ℂ)*((Real.sqrt (Z^N):ℝ):ℂ)*markedShortCompletedSum
          (rowTwist Ψ (ActualFiber.maskElement q m) (labelGenerator f) k)
          (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤
        C*(1+‖θ‖)^degree*Z^(N+V-cstar/256) := by
  let : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
  obtain ⟨degree,hu⟩ := canonical_short_completed_power_energy_uniform_degree lo hi hlo W hWs hW L cstar eta hL hcstar heta heta1 hetac rmax
  refine ⟨degree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,he⟩ := hu q hq
  obtain ⟨D,hD,hlabels⟩ := divisor_weight_sum K L (cstar/256) hL (by positivity)
  refine ⟨D*(6*C),Z₀,by positivity,hZ₀,?_⟩
  intro σ _ _ m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc
    hRn hmargin hreserve hVd hcutd hd labels hlabelsN labelGenerator hlabelGenerator T hT hcard lists H hdis hmax hgood hprime hodd
    hH1 hH hprod Ψ hΨ hperiod θ w hw
  have hz1 : 1≤Z := (lt_of_lt_of_le hZ₀ hZ).le
  have hz : 0<Z := zero_lt_one.trans_le hz1
  let rows := T.image (fun k => Ideal.span {k})
  have hrows := CompletedUnitRows.image_span_nonzero_norm T (Z^M) hT
  let E := C*(1+‖θ‖)^degree*Z^(N+V-cstar/128)
  have hf (f : Ideal Eis) (hfl : f∈labels) :
      (∑ k∈T,‖markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (labelGenerator f) k)
        (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤6*E := by
    let uf := CompletedUnitRows.rowUnit (labelGenerator f)
    have hgf : labelGenerator f=uf.val*ConcretePrimeRowBridge.idealGenerator f :=
      label_eq_rowUnit_generator f (hlabelsN f hfl).1.ne_zero (labelGenerator f) (hlabelGenerator f hfl)
    apply (CompletedUnitRows.sum_nonzero_element_le_units T (fun k hk => (hT k hk).1)
      (fun k => ‖markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (labelGenerator f) k)
        (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)
      (fun k => sq_nonneg _)).trans
    have hb (u : Eisˣ) :
        (∑ I∈rows,‖markedShortCompletedSum
          (rowTwist Ψ (ActualFiber.maskElement q m) (labelGenerator f)
            (u.val*ConcretePrimeRowBridge.idealGenerator I))
          (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤E := by
      have hh := he f (hlabelsN f hfl).1 m hm Z N V M z₀ margin hcut d
        hZ hN hM hMc hVc hzc hcut0 hcutc (hlabelsN f hfl).2 hRn hmargin hreserve hVd hcutd hd
        rows hrows hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod Ψ hΨ hperiod (uf^4*u) θ w hw
      simpa only [hgf,rowTwist_label_transfer,Units.val_mul,Units.val_pow_eq_pow_val,E,mul_assoc] using hh
    calc
      _ ≤ ∑ _u : Eisˣ,E := Finset.sum_le_sum (fun u _ => hb u)
      _ = 6*E := by simp only [Finset.sum_const,Finset.card_univ,CompletedUnitRows.unit_card,nsmul_eq_mul,Nat.cast_ofNat]
  have hl : (∑ f∈labels,secondLabelWeight K f)≤D*Z^(V+cstar/256) :=
    hlabels Z V hz1 hV hVc labels (fun f hfl => ⟨(hlabelsN f hfl).1.ne_zero,(hlabelsN f hfl).2⟩)
  simp_rw [normalization_norm_sq Z N V hz,←Finset.mul_sum]
  calc
    _ ≤ ∑ f∈labels,secondLabelWeight K f*(Z^(-V)*(6*E)) := by
      apply Finset.sum_le_sum
      intro f hfl
      apply mul_le_mul_of_nonneg_left _ (by unfold secondLabelWeight; positivity)
      exact mul_le_mul_of_nonneg_left (hf f hfl) (Real.rpow_nonneg hz.le _)
    _ = (∑ f∈labels,secondLabelWeight K f)*(Z^(-V)*(6*E)) := by rw [Finset.sum_mul]
    _ ≤ (D*Z^(V+cstar/256))*(Z^(-V)*(6*E)) := mul_le_mul_of_nonneg_right hl (by dsimp [E]; positivity)
    _ = (D*(6*C))*(1+‖θ‖)^degree*Z^(N+V-cstar/256) := by
      dsimp only [E]
      have hr : Z^(V+cstar/256)*Z^(-V)*Z^(N+V-cstar/128)=Z^(N+V-cstar/256) := by
        rw [←Real.rpow_add hz,←Real.rpow_add hz]
        congr 1
        ring
      calc
        _ = (D*(6*C))*(1+‖θ‖)^degree*(Z^(V+cstar/256)*Z^(-V)*Z^(N+V-cstar/128)) := by ring
        _ = _ := by rw [hr]

end SevenEighths.InverseShortCanonicalNormalization

end

end OAI
end OAIOriginalModule1182

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.ReflectedShortNormalizedUniformDegree
Source SHA256: dcdf8809918369109c0e8ae49707599691fc92b97979d5d0c21344874ee16006
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1183



namespace OAI
noncomputable section
open scoped BigOperators Classical ContDiff
namespace SevenEighths.InverseShortCanonicalNormalization
open ActualEisensteinCubic IdealMobiusDivisorSum CompletedGauss CanonicalRowCompletion
open InverseMoment InverseReflectedPhase InverseTerminalWidths CompletedHeight
local notation "Eis" => ActualEisensteinCubic.O
universe u v

theorem canonical_short_normalized_energy_uniform_degree
    (lo hi : ℝ) (hlo : 0<lo) (W : ℝ→ℂ)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar eta : ℝ) (hL : 0≤L) (hcstar : 0<cstar) (heta : 0<eta)
    (heta1 : eta≤1) (hetac : eta≤cstar/100000) (rmax K : ℕ) :
    ∃ (degree : ℕ), ∀ (q : ℕ) (_hq : q≠0), ∃ (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],
    ∀ (m : Eis) (_hm : m≠0) (Z N V M z₀ margin hcut d : ℝ),
      Z₀≤Z → 0≤N → 0≤V → 0≤M → M≤L → V≤L → z₀≤L → 0≤hcut → hcut≤L →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      V≤d → hcut≤d+eta → d≤cstar/200 →
    ∀ (labels : Finset (Ideal Eis)),
      (∀ f∈labels,Squarefree f ∧ (Ideal.absNorm f:ℝ)≤Z^V) →
    ∀ (T : Finset Eis),(∀ k∈T,k≠0 ∧ (Ideal.absNorm (Ideal.span {k}):ℝ)≤Z^M) →
      Fintype.card σ≤rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) → (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ f∈labels,secondLabelWeight K f * ∑ k∈T,
        ‖((Z^(-(N+V)/2):ℝ):ℂ)*((Real.sqrt (Z^N):ℝ):ℂ)*markedShortCompletedSum
          (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator f) k)
          (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤
        C*(1+‖θ‖)^degree*Z^(N+V-cstar/256) := by
  obtain ⟨degree,hu⟩ := canonical_short_normalized_generator_energy_uniform_degree lo hi hlo W hWs hW L cstar eta hL hcstar heta heta1 hetac rmax K
  refine ⟨degree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,he⟩ := hu q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc
    hRn hmargin hreserve hVd hcutd hd labels hlabelsN T hT hcard lists H hdis hmax hgood hprime hodd
    hH1 hH hprod Ψ hΨ hperiod θ w hw
  exact he m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc hRn
    hmargin hreserve hVd hcutd hd labels hlabelsN ConcretePrimeRowBridge.idealGenerator
    (fun f _ => ConcretePrimeRowBridge.span_idealGenerator f) T hT hcard lists H hdis hmax hgood hprime hodd
    hH1 hH hprod Ψ hΨ hperiod θ w hw

end SevenEighths.InverseShortCanonicalNormalization

end

end OAI
end OAIOriginalModule1183

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalShortFinite
Source SHA256: 178e2e3f853dd5eeb782ae25dffef79a8985372f1128eb692e42fef88d49ff34
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1184



namespace OAI

noncomputable section

open scoped BigOperators Classical ContDiff
namespace SevenEighths.InverseCanonicalShortAttachment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve InverseMoment InverseReflectedPhase InverseTerminalWidths CompletedHeight
local notation "Eis"=>ActualEisensteinCubic.O
universe u v
theorem actual_complete_short_finite_uniform_degree
    (lo hi : ℝ) (hlo : 0<lo) (W : ℝ→ℂ)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar eta : ℝ) (hL : 0≤L) (hcstar : 0<cstar) (heta : 0<eta)
    (heta1 : eta≤1) (hetac : eta≤cstar/100000) (rmax K : ℕ) :
    ∃ (degree : ℕ), ∀ (q:ℕ)(_hq:q≠0), ∃ (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [DecidableEq σ],
    ∀ (m : Eis),m≠0 → ∀ (Z N V M z₀ margin hcut d : ℝ),
      Z₀≤Z → 0≤N → 0≤V → 0≤M → M≤L → V≤L → z₀≤L → 0≤hcut → hcut≤L →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      V≤d → hcut≤d+eta → d≤cstar/200 →
    ∀ (labels : Finset (Ideal Eis)),
      (∀f∈labels,Supported f ∧ Squarefree f ∧ (Ideal.absNorm f:ℝ)≤Z^V) →
    ∀ (T : Finset Eis),(∀k∈T,k≠0 ∧ (Ideal.absNorm (Ideal.span {k}):ℝ)≤Z^M) →
    ∀ D : ℕ,hi*Z^N≤D → ∀ slots : Finset σ,slots.card≤rmax →
    ∀ (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
      (H : σ→ℝ),
      (slots:Set σ).Pairwise (fun j k=>Disjoint (lists j) (lists k)) →
      (∀j∈slots,1≤H j) → (∀j∈slots,∀i∈lists j,(Ideal.absNorm i.val:ℝ)≤H j) →
      (∏j∈slots,H j)≤Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (θ : ℝ)
      (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ),
      (∀j∈slots,∀i∈lists j,‖a j i‖≤1) →
      let S:=reflectionExcludedPrimes q
      let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
      let mark:=indexedIdealMark (fun i:primePool F=>i.val) slots lists a
      Z^(-V)*(∑f∈labels,secondLabelWeight K f*∑k∈T,
        ‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator f) k)
          (normTwistedSource W θ) (Z^N) (Z^hcut) mark‖^2)≤
        C*(1+‖θ‖)^degree*Z^(N+V-cstar/256) := by
  obtain ⟨degree,hu⟩:=InverseShortCanonicalNormalization.canonical_short_normalized_energy_uniform_degree
    lo hi hlo W hWs hW L cstar eta hL hcstar heta heta1 hetac rmax K
  refine ⟨degree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,he⟩:=hu q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro σ _ m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc
    hRn hmargin hreserve hVd hcutd hd labels hlabels T hT D hD slots hcard lists H hdis hH1 hH hprod
    Ψ hΨ hperiod θ a ha
  dsimp only
  let S:=reflectionExcludedPrimes q
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF : ∀I∈F,Admissible I:=InitialMeanSquare.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q)
  let ilists:slots→Finset (Ideal Eis):=fun j=>idealLists F lists j.val
  let iw:∀j,ilists j→ℂ:=fun j=>idealWeights F lists a j.val
  have hp (j:slots) (P:Ideal Eis) (hP:P∈ilists j) := idealLists_prime_data F hF lists j.val P hP
  have hcap : ∀j:slots,∀P∈ilists j,(Ideal.absNorm P:ℝ)≤H j.val := by
    intro j P hP
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hP
    exact hH j.val j.property i hi
  have hw : ∀j:slots,∀P:ilists j,‖iw j P‖≤1 := by
    intro j P
    obtain ⟨i,hi,hh⟩:=Finset.mem_image.mp P.property
    change ‖transportCoeff F a j.val P.val‖≤1
    rw [←hh,transportCoeff_val]
    exact ha j.val j.property i hi
  have henergy:=he (σ:=slots) m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc
    hRn hmargin hreserve hVd hcutd hd labels (fun f hf=>(hlabels f hf).2) T hT (by simpa using hcard)
    ilists (fun j:slots=>H j.val) (idealLists_disjoint F slots lists hdis)
    (fun j P hP=>(hp j P hP).1) (fun j P hP=>(hp j P hP).2.1)
    (fun j P hP=>(hp j P hP).2.2.1) (fun j P hP=>(hp j P hP).2.2.2)
    (fun j=>hH1 j.val j.property) hcap (by simpa only [Finset.prod_coe_sort] using hprod)
    Ψ hΨ hperiod θ iw hw
  have hz:0<Z:=zero_lt_one.trans (lt_of_lt_of_le hZ₀ hZ)
  have hn:‖((Z^(-(N+V)/2):ℝ):ℂ)*((Real.sqrt (Z^N):ℝ):ℂ)‖^2=Z^(-V) := by
    rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hz _),Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (Real.rpow_nonneg hz.le _),
      ←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz]
    congr 1
    ring
  have hmark:indexedIdealMark (fun i:primePool F=>i.val) slots lists a=tupleDivisibilityMark ilists iw:=
    funext (indexed_mark_eq_tuple F slots lists a)
  rw [hmark]
  change Z^(-V)*(∑f∈labels,secondLabelWeight K f*∑k∈T,
    ‖markedShortCompletedSum (rowTwist Ψ (ActualFiber.maskElement q m) (idealGenerator f) k)
      (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark ilists iw)‖^2)≤_
  simp only [norm_mul,mul_pow] at henergy
  have hn':‖((Z^(-(N+V)/2):ℝ):ℂ)‖^2*‖((Real.sqrt (Z^N):ℝ):ℂ)‖^2=Z^(-V):=by
    simpa only [norm_mul,mul_pow] using hn
  simp only [←mul_assoc,hn',←Finset.mul_sum] at henergy
  convert henergy using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros
  ring

end SevenEighths.InverseCanonicalShortAttachment

end

end OAI
end OAIOriginalModule1184

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalCompleteState
Source SHA256: c383988283e3a3e02324a73c7211f71fe374cd1ba000490cb2e1ad6d850aaf83
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1185



namespace OAI

noncomputable section

open scoped BigOperators Classical ContDiff
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve InverseReflectedPhase InverseTerminalWidths CompletedHeight
open InverseCanonicalShortAttachment InverseSecondFibers FirstPassCubeLabels SecondPassArithmetic
local notation "O"=>ActualEisensteinCubic.O
universe v

theorem actual_complete_state_from_live_bins
    (lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)(W:ℝ→ℂ)
    (hWs:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W)
    (L cstar eta eps:ℝ)(hL:0≤L)(hcstar:0<cstar)(heta:0<eta)
    (heta1:eta≤1)(hetac:eta≤cstar/100000)(heps:0<eps)(rmax K:ℕ) :
    ∃degree:ℕ,∀(q:ℕ)(_hq:q≠0),∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀{σ:Type v}[DecidableEq σ](m:O),m≠0 → ∀Z N V M z₀ margin cutoff:ℝ,
      Z₀≤Z → 0≤N → N≤L → 0≤V → V≤L → 0≤M → M≤L → z₀≤L →
      0≤cutoff → cutoff≤L → cutoff≤cstar/200 →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
    ∀labels:Finset (Ideal O),(∀I∈labels,Supported I ∧ Squarefree I ∧ (I.absNorm:ℝ)≤Z^V) →
    ∀D:ℕ,hi*Z^N≤D → ∀slots:Finset σ,slots.card≤rmax →
    ∀(lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))(H:σ→ℝ),
      (slots:Set σ).Pairwise (fun i j=>Disjoint (lists i) (lists j)) →
      (∀i∈slots,1≤H i) → (∀i∈slots,∀P∈lists i,(Ideal.absNorm P.val:ℝ)≤H i) → (∏i∈slots,H i)≤Z^z₀ →
    ∀(Ψ:O→*ℂ),(∀u,‖Ψ u‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀(theta:ℝ)(a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ),
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1) → ∀E:ℝ,0≤E →
      let S:=reflectionExcludedPrimes q;
      let test:=normTwistedSource W theta;
      (∀j∈cubeLogRange hi (Z^N),
        (progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D hi (Z^N) j)).Nonempty →
        Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
          (progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D hi (Z^N) j))
          Ψ m (idealGenerator I) z test (Z^N) (Z^(cutoff-V)) slots lists a) (Z^M)≤E) →
      Z^(-(N+V))*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 (Z^M),
        ‖outsideCanonicalMarkedRow S D (reflectionExcludedPrimes_bad q) Ψ m (idealGenerator I) z
          slots lists a test (Z^N)‖^2)≤
      C*((1+‖theta‖)^degree*Z^(N+V-cstar/256)+Z^eps*E) := by
  obtain ⟨degree,hs⟩:=actual_complete_short_finite_uniform_degree lo hi hlo W hWs hW L cstar eta
    hL hcstar heta heta1 hetac rmax K
  obtain ⟨Cl,hCl,hl⟩:=actual_complete_energy_from_live_bins K hi L eps hhi hL heps
  refine ⟨degree,?_⟩
  intro q hq
  obtain ⟨Cs,Z₀,hCs,hZ₀,hshort⟩:=hs q hq
  refine ⟨2*Cs+Cl,Z₀,by positivity,hZ₀,?_⟩
  intro σ _ m hm Z N V M z₀ margin cutoff hZ hN hNL hV hVL hM hML hzL hcut hcutL hcutc
    hmN hmargin hreserve labels hlabels D hD slots hcard lists H hdis hH1 hH hprod Ψ hΨ hperiod theta a ha E hE
  dsimp only
  intro hbins
  have hz:0<Z:=zero_lt_one.trans (lt_of_lt_of_le hZ₀ hZ)
  have hZ1:1≤Z:=(hZ₀.trans_le hZ).le
  let S:=reflectionExcludedPrimes q
  let test:=normTwistedSource W theta
  let mark:=indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a
  have htest:HasCompactSupport test:=HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((normTwistedSource_support W theta).trans hWs)
  have hupper:∀x,test x≠0 → x≤hi:=fun x hx=>(hWs (normTwistedSource_support W theta hx)).2
  have hT:∀z∈nonzeroChildFrequencyBall 1 (Z^M),z≠0 ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤Z^M := by
    intro z hz
    have hh:=(mem_nonzeroChildFrequencyBall 1 one_ne_zero (Z^M) z).mp hz
    constructor
    · intro he
      simp only [he,mul_zero,map_zero,norm_zero,pow_succ,lt_self_iff_false] at hh
      exact hh.1
    · rw [←eisEmbedding_norm_sq_eq_absNorm_span]
      simpa only [one_mul] using hh.2
  have hshortbound:Z^(-V)*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 (Z^M),
      ‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z)
        test (Z^N) (Z^(cutoff-V)) mark‖^2)≤Cs*(1+‖theta‖)^degree*Z^(N+V-cstar/256) := by
    by_cases hbig:cutoff≤V
    · have he (I:Ideal O)(z:O):markedShortCompletedSum
          (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z) test (Z^N) (Z^(cutoff-V)) mark=0:=
        short_sum_zero_of_label_large _ _ _ _ _ _ _ hZ1 hbig
      simp only [he,norm_zero,zero_pow (by decide:2≠0),Finset.sum_const_zero,mul_zero]
      positivity
    · exact hshort m hm Z N V M z₀ margin (cutoff-V) cutoff hZ hN hV hM hML hVL hzL
        (by linarith) (by linarith) hmN hmargin hreserve (by linarith) (by linarith) hcutc
        labels hlabels (nonzeroChildFrequencyBall 1 (Z^M)) hT D hD slots hcard lists H
        hdis hH1 hH hprod Ψ hΨ hperiod theta a ha
  have hb:=hl S D (reflectionExcludedPrimes_bad q) (reflectionExcludedPrimes_prime q) labels
    (fun I hI=>(hlabels I hI).1.1) Ψ m slots lists a test htest Z N V (Z^M)
    (Z^(cutoff-V)) (Cs*(1+‖theta‖)^degree*Z^(N+V-cstar/256)) E
    hZ1 (Real.rpow_pos_of_pos hz _) hNL hVL (fun I hI=>(hlabels I hI).2.2)
    hupper hD hE hshortbound hbins
  apply hb.trans
  have hA:0≤(1+‖theta‖)^degree*Z^(N+V-cstar/256):=by positivity
  have hB:0≤Z^eps*E:=by positivity
  nlinarith

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule1185

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalLongCosts
Source SHA256: c621fc457e516eded9963006e3b80d621c3a4f0513d83fac1253a70128be752f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1186



namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment

theorem actual_long_coefficient_cost (Z ell L epsilon Ccoef:ℝ)
    (hZ:1≤Z)(hell:ell≤L)(heps:0≤epsilon):
    (Ccoef*(Real.exp 1*Z^ell)^epsilon)^2≤
      Ccoef^2*Real.exp (2*epsilon)*Z^(2*L*epsilon) := by
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hex:(Real.exp 1)^epsilon=Real.exp epsilon:=by rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,one_mul]
  have hex2:(Real.exp epsilon)^2=Real.exp (2*epsilon):=by rw [←Real.exp_nat_mul];norm_num
  have hid:(Ccoef*(Real.exp 1*Z^ell)^epsilon)^2=
      Ccoef^2*Real.exp (2*epsilon)*Z^(2*ell*epsilon) := by
    rw [Real.mul_rpow (Real.exp_pos _).le (Real.rpow_nonneg hz.le _),hex,
      ←Real.rpow_mul hz.le,mul_pow,mul_pow,hex2,
      ←Real.rpow_mul_natCast hz.le]
    ring_nf
  rw [hid]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hZ
  nlinarith

theorem actual_long_uniform_parent_cost (Z ell N V L epsilon Ccoef C A loss:ℝ)
    (hZ:1≤Z)(hell:ell≤L)(heps:0≤epsilon)(hC:0≤C)(hA:0≤A):
    C*(Ccoef*(Real.exp 1*Z^ell)^epsilon)^2*(1+A)*Z^((N-3*ell)+3*ell+V+loss)≤
      (C*Ccoef^2*Real.exp (2*epsilon))*(1+A)*Z^(N+V+loss+2*L*epsilon) := by
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have h:=actual_long_coefficient_cost Z ell L epsilon Ccoef hZ hell heps
  have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left h hC) (by linarith:0≤1+A))
    (Real.rpow_nonneg hz.le ((N-3*ell)+3*ell+V+loss))
  apply hh.trans_eq
  have hpow:Z^(2*L*epsilon)*Z^((N-3*ell)+3*ell+V+loss)=Z^(N+V+loss+2*L*epsilon):=by
    rw [←Real.rpow_add hz];congr 1;ring
  calc
    _=(C*Ccoef^2*Real.exp (2*epsilon))*(1+A)*
        (Z^(2*L*epsilon)*Z^((N-3*ell)+3*ell+V+loss)):=by ring
    _=_:=by rw [hpow]

theorem complete_state_power_absorption (Z F cstar eps loss C A height E:ℝ)
    (hZ:1≤Z)(hc:0≤cstar)(heps:0≤eps)(hloss:0≤loss)
    (hC:0≤C)(_hA:0≤A)(hheight:0≤height)
    (hE:E≤A*height*Z^(F+loss)):
    C*(height*Z^(F-cstar/256)+Z^eps*E)≤
      C*(1+A)*height*Z^(F+loss+eps) := by
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hs:height*Z^(F-cstar/256)≤height*Z^(F+loss+eps):=by
    apply mul_le_mul_of_nonneg_left _ hheight
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have ht:Z^eps*E≤A*height*Z^(F+loss+eps):=by
    have hh:=mul_le_mul_of_nonneg_left hE (Real.rpow_nonneg hz.le eps)
    apply hh.trans_eq
    rw [Real.rpow_add hz (F+loss) eps]
    ring
  have hh:=mul_le_mul_of_nonneg_left (add_le_add hs ht) hC
  convert hh using 1 ; ring

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule1186

/-! Original module: OAI.NumberTheory.DirichletL.Supremum
Source SHA256: 4731fe9e9d86cde2ba9accf807fa8e257fe8114674a304040d7515a0aee1880d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1187



namespace OAI

namespace SevenEighths.Supremum

noncomputable section

def continuationMargin (β ω σ : ℝ) : ℝ := min (β - 7 / 8 - ω) σ

theorem continuationMargin_pos {β ω σ : ℝ}
    (hω : ω < β - 7 / 8) (hσ : 0 < σ) :
    0 < continuationMargin β ω σ := by
  exact lt_min (sub_pos.mpr hω) hσ

theorem continuationMargin_le_gap (β ω σ : ℝ) :
    continuationMargin β ω σ ≤ β - 7 / 8 - ω :=
  min_le_left _ _

theorem continuationMargin_le_sigma (β ω σ : ℝ) :
    continuationMargin β ω σ ≤ σ :=
  min_le_right _ _

theorem continuation_boundary_gt {β ω σ : ℝ} (hω : 0 < ω) :
    7 / 8 < β - continuationMargin β ω σ := by
  have h := continuationMargin_le_gap β ω σ
  linarith

theorem max_signal_exponents (β ω σ c : ℝ) :
    max (7 / 8 + c + ω) (β + c - σ) =
      β + c - continuationMargin β ω σ := by
  unfold continuationMargin
  rcases le_total (β - 7 / 8 - ω) σ with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
    linarith
  · rw [min_eq_right h, max_eq_right (by linarith)]

theorem max_normalized_signal_exponents (β ω σ : ℝ) :
    max (3 / 16 + ω) (β - 11 / 16 - σ) =
      β - 11 / 16 - continuationMargin β ω σ := by
  have h : (7 / 8 : ℝ) + -(11 / 16) = 3 / 16 := by norm_num
  simpa only [sub_eq_add_neg, h] using max_signal_exponents β ω σ (-(11 / 16))

theorem exists_gt_supremum_sub {S : Set ℝ} (hne : S.Nonempty)
    (hbounded : BddAbove S) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ S, sSup S - ε < x := by
  apply (lt_csSup_iff hbounded hne).mp
  linarith

theorem uniform_bound_below_supremum_false {S : Set ℝ}
    (hne : S.Nonempty) (hbounded : BddAbove S) {ε : ℝ} (hε : 0 < ε)
    (hbound : ∀ x ∈ S, x ≤ sSup S - ε) : False := by
  obtain ⟨x, hx, hlt⟩ := exists_gt_supremum_sub hne hbounded hε
  exact (not_lt_of_ge (hbound x hx)) hlt

theorem exists_gt_supremum_sub_of_insert {S : Set ℝ} {a ε : ℝ}
    (hbounded : BddAbove (insert a S)) (hε : 0 < ε)
    (ha : a ≤ sSup (insert a S) - ε) :
    ∃ x ∈ S, sSup (insert a S) - ε < x := by
  obtain ⟨x, hx, hlt⟩ :=
    exists_gt_supremum_sub (Set.insert_nonempty a S) hbounded hε
  rcases Set.mem_insert_iff.mp hx with hxa | hxS
  · subst x
    exact False.elim ((not_lt_of_ge ha) hlt)
  · exact ⟨x, hxS, hlt⟩

theorem seven_eighths_of_uniform_margin {S : Set ℝ}
    (hne : S.Nonempty) (hbounded : BddAbove S)
    (hbound : 7 / 8 < sSup S →
      ∃ ω σ : ℝ, ω < sSup S - 7 / 8 ∧ 0 < σ ∧
        ∀ x ∈ S, x ≤ sSup S - continuationMargin (sSup S) ω σ) :
    sSup S ≤ 7 / 8 := by
  by_contra h
  obtain ⟨ω, σ, hω, hσ, hbound⟩ := hbound (lt_of_not_ge h)
  exact uniform_bound_below_supremum_false hne hbounded
    (continuationMargin_pos hω hσ) hbound

theorem seven_eighths_of_uniform_margin_with_sentinel {S : Set ℝ}
    (hbounded : BddAbove (insert (1 / 2 : ℝ) S))
    (hbound : 7 / 8 < sSup (insert (1 / 2 : ℝ) S) →
      ∃ ω σ : ℝ, 0 < ω ∧ ω < sSup (insert (1 / 2 : ℝ) S) - 7 / 8 ∧
        0 < σ ∧ ∀ x ∈ S, x ≤ sSup (insert (1 / 2 : ℝ) S) -
          continuationMargin (sSup (insert (1 / 2 : ℝ) S)) ω σ) :
    sSup (insert (1 / 2 : ℝ) S) ≤ 7 / 8 := by
  by_contra h
  obtain ⟨ω, σ, hω0, hω, hσ, hbound⟩ := hbound (lt_of_not_ge h)
  have hε := continuationMargin_pos hω hσ
  have hboundary := continuation_boundary_gt (β := sSup (insert (1 / 2 : ℝ) S))
    (σ := σ) hω0
  have hsentinel : (1 / 2 : ℝ) ≤ sSup (insert (1 / 2 : ℝ) S) -
      continuationMargin (sSup (insert (1 / 2 : ℝ) S)) ω σ := by
    linarith
  obtain ⟨x, hx, hlt⟩ := exists_gt_supremum_sub_of_insert hbounded hε hsentinel
  exact (not_lt_of_ge (hbound x hx)) hlt

end

end SevenEighths.Supremum

end OAI
end OAIOriginalModule1187

/-! Original module: OAI.NumberTheory.DirichletL.Continuation
Source SHA256: 5e82c4cd2ddfad95227dbcd9f7a87c8cf9e16d62c46fee297309c0a99a9678ac
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1188







namespace OAI

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace SevenEighths.Continuation

def signalMellin (f : ℝ → ℂ) (c : ℝ) (s : ℂ) : ℂ :=
  mellin f (-(s + (c : ℂ)))

def RapidDecayAtZero (f : ℝ → ℂ) : Prop :=
  ∀ B : ℝ, f =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ B)

theorem rpow_isBigO_atTop_of_le {a b : ℝ} (h : a ≤ b) :
    (fun x : ℝ => x ^ a) =O[atTop] (fun x : ℝ => x ^ b) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  simpa only [one_mul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) _)] using
    Real.rpow_le_rpow_of_exponent_le hx h

theorem common_signal_bound (J f : ℝ → ℂ) (a b : ℝ)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ a))
    (herror : (fun x => J x - f x) =O[atTop] (fun x : ℝ => x ^ b)) :
    f =O[atTop] (fun x : ℝ => x ^ max a b) := by
  have h₁ := hJ.trans (rpow_isBigO_atTop_of_le (le_max_left a b))
  have h₂ := herror.trans (rpow_isBigO_atTop_of_le (le_max_right a b))
  simpa only [sub_sub_cancel] using h₁.sub h₂

theorem common_signal_bound_with_margin (J f : ℝ → ℂ) (β ω σ c : ℝ)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (7 / 8 + c + ω)))
    (herror : (fun x => J x - f x) =O[atTop]
      (fun x : ℝ => x ^ (β + c - σ))) :
    f =O[atTop] (fun x : ℝ =>
      x ^ (β + c - Supremum.continuationMargin β ω σ)) := by
  simpa only [Supremum.max_signal_exponents] using
    common_signal_bound J f (7 / 8 + c + ω) (β + c - σ) hJ herror

theorem signalMellin_convergent (f : ℝ → ℂ) (a c : ℝ)
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (htop : f =O[atTop] (fun x : ℝ => x ^ (a + c)))
    (hzero : RapidDecayAtZero f) {s : ℂ} (hs : a < s.re) :
    MellinConvergent f (-(s + (c : ℂ))) := by
  apply mellinConvergent_of_isBigO_rpow (a := -(a+c))
    (b := (-(s + (c : ℂ))).re - 1) hlocal
  · simpa only [neg_neg] using htop
  · simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re]
    linarith
  · exact hzero _
  · linarith

theorem signalMellin_analytic (f : ℝ → ℂ) (a c : ℝ)
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (htop : f =O[atTop] (fun x : ℝ => x ^ (a + c)))
    (hzero : RapidDecayAtZero f) :
    AnalyticOnNhd ℂ (signalMellin f c) {s : ℂ | a < s.re} := by
  apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt a)).2
  intro s hs
  have hd : DifferentiableAt ℂ (mellin f) (-(s + (c : ℂ))) := by
    apply mellin_differentiableAt_of_isBigO_rpow (a := -(a+c))
      (b := (-(s + (c : ℂ))).re - 1) hlocal
    · simpa only [neg_neg] using htop
    · simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re]
      change a < s.re at hs
      linarith
    · exact hzero _
    · linarith
  exact (hd.comp s ((differentiableAt_id.add_const (c : ℂ)).neg)).differentiableWithinAt

theorem product_identity_on_halfPlane (a b : ℝ) (L M W : ℂ → ℂ)
    (hL : AnalyticOnNhd ℂ L {s : ℂ | a < s.re})
    (hM : AnalyticOnNhd ℂ M {s : ℂ | a < s.re})
    (hW : AnalyticOnNhd ℂ W {s : ℂ | a < s.re})
    (heq : ∀ s : ℂ, max a b < s.re → L s * M s = W s) :
    Set.EqOn (fun s => L s * M s) W {s : ℂ | a < s.re} := by
  let z : ℂ := (max a b + 1 : ℝ)
  have hz : a < z.re := by dsimp [z]; linarith [le_max_left a b]
  have hz' : max a b < z.re := by dsimp [z]; simp
  have hev : (fun s => L s * M s) =ᶠ[𝓝 z] W := by
    filter_upwards [(Complex.isOpen_re_gt (max a b)).mem_nhds hz'] with s hs
    exact heq s hs
  exact (hL.mul hM).eqOn_of_preconnected_of_eventuallyEq hW
    (convex_halfSpace_re_gt a).isPreconnected hz hev

theorem nonzero_of_regularized_signal (a b c : ℝ)
    (L Lregular R W : ℂ → ℂ) (f : ℝ → ℂ)
    (hL : AnalyticOnNhd ℂ Lregular {s : ℂ | a < s.re})
    (hR : AnalyticOnNhd ℂ R {s : ℂ | a < s.re})
    (hW : AnalyticOnNhd ℂ W {s : ℂ | a < s.re})
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (htop : f =O[atTop] (fun x : ℝ => x ^ (a + c)))
    (hzero : RapidDecayAtZero f)
    (heq : ∀ s : ℂ, max a b < s.re →
      Lregular s * signalMellin f c s = R s * W s)
    {ρ : ℂ} (hρ : a < ρ.re)
    (hregular : Lregular ρ = R ρ * L ρ)
    (hRρ : R ρ ≠ 0) (hWρ : W ρ ≠ 0) : L ρ ≠ 0 := by
  have hid := product_identity_on_halfPlane a b Lregular (signalMellin f c)
    (fun s => R s * W s) hL (signalMellin_analytic f a c hlocal htop hzero)
    (hR.mul hW) heq hρ
  intro hz
  change Lregular ρ * signalMellin f c ρ = R ρ * W ρ at hid
  rw [hregular, hz, mul_zero, zero_mul] at hid
  exact (mul_ne_zero hRρ hWρ) hid.symm

theorem multiplier_ne_zero {H : ℂ → ℂ} {s : ℂ}
    (h : ‖H s - 1‖ ≤ (1 / 2 : ℝ)) : H s ≠ 0 := by
  intro hz
  simp [hz] at h
  norm_num at h

def gaussianMultiplier (H : ℂ → ℂ) (s : ℂ) : ℂ :=
  Complex.exp ((s - 5 / 6) ^ 2) * H s

theorem gaussianMultiplier_analytic {H : ℂ → ℂ} {U : Set ℂ}
    (hH : AnalyticOnNhd ℂ H U) : AnalyticOnNhd ℂ (gaussianMultiplier H) U := by
  exact ((analyticOnNhd_id.sub analyticOnNhd_const).pow 2).cexp.mul hH

theorem gaussianMultiplier_ne_zero {H : ℂ → ℂ} {s : ℂ}
    (hH : ‖H s - 1‖ ≤ (1 / 2 : ℝ)) : gaussianMultiplier H s ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) (multiplier_ne_zero hH)

theorem nonzero_of_common_signal (β ω σ c : ℝ) (hω : 0 < ω)
    (L Lregular R H : ℂ → ℂ) (J f : ℝ → ℂ)
    (hL : AnalyticOnNhd ℂ Lregular
      {s : ℂ | β - Supremum.continuationMargin β ω σ < s.re})
    (hR : AnalyticOnNhd ℂ R
      {s : ℂ | β - Supremum.continuationMargin β ω σ < s.re})
    (hH : AnalyticOnNhd ℂ H {s : ℂ | 7 / 8 < s.re})
    (hcontract : ∀ s : ℂ, 7 / 8 < s.re → ‖H s - 1‖ ≤ (1 / 2 : ℝ))
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (hzero : RapidDecayAtZero f)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (7 / 8 + c + ω)))
    (herror : (fun x => J x - f x) =O[atTop]
      (fun x : ℝ => x ^ (β + c - σ)))
    (heq : ∀ s : ℂ, max (β - Supremum.continuationMargin β ω σ) 1 < s.re →
      Lregular s * signalMellin f c s = R s * gaussianMultiplier H s)
    {ρ : ℂ} (hρ : β - Supremum.continuationMargin β ω σ < ρ.re)
    (hregular : Lregular ρ = R ρ * L ρ) (hRρ : R ρ ≠ 0) : L ρ ≠ 0 := by
  have hboundary := Supremum.continuation_boundary_gt (β := β) (σ := σ) hω
  have hH' : AnalyticOnNhd ℂ H
      {s : ℂ | β - Supremum.continuationMargin β ω σ < s.re} :=
    hH.mono (fun s hs => lt_trans hboundary hs)
  have htop : f =O[atTop] (fun x : ℝ =>
      x ^ ((β - Supremum.continuationMargin β ω σ) + c)) := by
    have hexp : (β - Supremum.continuationMargin β ω σ) + c =
        β + c - Supremum.continuationMargin β ω σ := by ring
    simpa only [hexp] using common_signal_bound_with_margin J f β ω σ c hJ herror
  exact nonzero_of_regularized_signal _ 1 c L Lregular R (gaussianMultiplier H) f
    hL hR (gaussianMultiplier_analytic hH') hlocal htop hzero heq hρ hregular
    hRρ (gaussianMultiplier_ne_zero (hcontract ρ (lt_trans hboundary hρ)))

end SevenEighths.Continuation

end

end OAI
end OAIOriginalModule1188

/-! Original module: OAI.NumberTheory.DirichletL.ContinuationInversion
Source SHA256: 166139695fcd8753df43d21f7e0b3a5a0ffc774bd75d0535fb4d0b33757170d8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1189



namespace OAI

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology FourierTransform
namespace SevenEighths.Continuation

theorem integrable_logProfile {f : ℝ → ℂ} {σ : ℝ}
    (hf : MellinConvergent f (σ : ℂ)) :
    Integrable (fun u : ℝ => Real.exp (-σ * u) • f (Real.exp (-u))) := by
  have hder : ∀ x ∈ (univ : Set ℝ),
      HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) univ x :=
    fun x _ => mul_neg_one (Real.exp (-x)) ▸
      ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt
  have himage : Real.exp ∘ Neg.neg '' (univ : Set ℝ) = Ioi 0 := by
    rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective,
      Set.image_univ, Real.range_exp]
  have hinj : univ.InjOn (Real.exp ∘ Neg.neg) :=
    Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)
  rw [MellinConvergent, ← himage,
    integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hder hinj] at hf
  have heq (u : ℝ) :
      |-(Real.exp (-u))| • ((Real.exp (-u) : ℂ) ^ ((σ : ℂ) - 1) • f (Real.exp (-u))) =
        Real.exp (-σ * u) • f (Real.exp (-u)) := by
    rw [abs_neg, abs_of_pos (Real.exp_pos _)]
    change (Real.exp (-u) : ℂ) *
      ((Real.exp (-u) : ℂ) ^ ((σ : ℂ) - 1) * f (Real.exp (-u))) =
        (Real.exp (-σ * u) : ℂ) * f (Real.exp (-u))
    rw [← mul_assoc]
    congr 1
    rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow (Real.exp_pos (-u)).le]
    norm_cast
    rw [Real.rpow_def_of_pos (Real.exp_pos (-u)), Real.log_exp, ← Real.exp_add]
    congr 1
    ring
  simpa only [Function.comp_apply, integrableOn_univ, heq] using hf

theorem mellin_mellinInv_eq (σ : ℝ) (F : ℂ → ℂ) (f : ℝ → ℂ)
    (hf : MellinConvergent f (σ : ℂ))
    (hF : Integrable (fun y : ℝ => F ((σ : ℂ) + 2 * Real.pi * y * Complex.I)))
    (hcont : Continuous (fun y : ℝ => F ((σ : ℂ) + 2 * Real.pi * y * Complex.I)))
    (hrep : ∀ x : ℝ, 0 < x → f x = mellinInv σ F x) (y : ℝ) :
    mellin f ((σ : ℂ) + 2 * Real.pi * y * Complex.I) =
      F ((σ : ℂ) + 2 * Real.pi * y * Complex.I) := by
  let A : ℝ → ℂ := fun y => F ((σ : ℂ) + 2 * Real.pi * y * Complex.I)
  let g : ℝ → ℂ := fun u => Real.exp (-σ * u) • f (Real.exp (-u))
  have hg : Integrable g := integrable_logProfile hf
  have hginv : g = 𝓕⁻ A := by
    funext u
    dsimp [g]
    rw [hrep _ (Real.exp_pos _), mellinInv_eq_fourierInv _ _ (Real.exp_pos _)]
    simp only [Real.log_exp, neg_neg]
    change (Real.exp (-σ * u) : ℂ) *
      ((Real.exp (-u) : ℂ) ^ (-(σ : ℂ)) * 𝓕⁻ A u) = 𝓕⁻ A u
    rw [← mul_assoc, ← Complex.ofReal_neg,
      ← Complex.ofReal_cpow (Real.exp_pos (-u)).le]
    have hc : Real.exp (-σ * u) * Real.exp (-u) ^ (-σ) = 1 := by
      rw [Real.rpow_def_of_pos (Real.exp_pos (-u)), Real.log_exp, ← Real.exp_add]
      rw [show -σ * u + -u * -σ = 0 by ring, Real.exp_zero]
    rw [← Complex.ofReal_mul, hc, Complex.ofReal_one, one_mul]
  have hfourier : Integrable (𝓕 A) := by
    have hn := hg.comp_neg
    rw [hginv] at hn
    simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using hn
  rw [mellin_eq_fourier]
  have hre : ((σ : ℂ) + 2 * Real.pi * y * Complex.I).re = σ := by simp
  have him : ((σ : ℂ) + 2 * Real.pi * y * Complex.I).im / (2 * Real.pi) = y := by
    simp
  rw [hre, him]
  change 𝓕 g y = A y
  rw [hginv]
  exact hF.fourier_fourierInv_eq hfourier hcont.continuousAt

def normalizedSignal (f : ℝ → ℂ) (c : ℝ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-(c : ℂ)) • f x

theorem mellin_normalizedSignal (f : ℝ → ℂ) (c : ℝ) (s : ℂ) :
    mellin (normalizedSignal f c) (-s) = signalMellin f c s := by
  unfold normalizedSignal signalMellin
  rw [mellin_cpow_smul]
  congr 1
  ring

theorem signalMellin_eq_on_line (f : ℝ → ℂ) (A : ℂ → ℂ) (c d : ℝ)
    (hf : MellinConvergent f (-((d : ℂ) + (c : ℂ))))
    (hA : Integrable (fun y : ℝ => A ((d : ℂ) - 2 * Real.pi * y * Complex.I)))
    (hcont : Continuous (fun y : ℝ => A ((d : ℂ) - 2 * Real.pi * y * Complex.I)))
    (hrep : ∀ x : ℝ, 0 < x → normalizedSignal f c x =
      mellinInv (-d) (fun s => A (-s)) x) (y : ℝ) :
    signalMellin f c ((d : ℂ) - 2 * Real.pi * y * Complex.I) =
      A ((d : ℂ) - 2 * Real.pi * y * Complex.I) := by
  have hf' : MellinConvergent (normalizedSignal f c) ((-d : ℝ) : ℂ) := by
    unfold normalizedSignal
    apply MellinConvergent.cpow_smul.mpr
    convert hf using 1; push_cast; ring
  have harg (y : ℝ) : -(((-d : ℝ) : ℂ) + 2 * Real.pi * y * Complex.I) =
      (d : ℂ) - 2 * Real.pi * y * Complex.I := by push_cast; ring
  have hA' : Integrable
      (fun y : ℝ => A (-(((-d : ℝ) : ℂ) + 2 * Real.pi * y * Complex.I))) := by
    simpa only [harg] using hA
  have hcont' : Continuous
      (fun y : ℝ => A (-(((-d : ℝ) : ℂ) + 2 * Real.pi * y * Complex.I))) := by
    simpa only [harg] using hcont
  have hid := mellin_mellinInv_eq (-d) (fun s => A (-s))
    (normalizedSignal f c) hf' hA' hcont' hrep y
  rw [harg] at hid
  rw [← mellin_normalizedSignal]
  convert hid using 1; congr 1; push_cast; ring

end SevenEighths.Continuation

end

end OAI
end OAIOriginalModule1189

/-! Original module: OAI.NumberTheory.DirichletL.ContinuationContour
Source SHA256: 3c29ca9681de5e41e20b9b8ada0a90b033efc4c4ce02583d32b89c0a33d81aac
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1190




namespace OAI

noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology
namespace SevenEighths.Continuation

theorem vertical_integral_eq_of_horizontal_vanish (F : ℂ → ℂ) {a b : ℝ}
    (hab : a ≤ b) (hhol : DifferentiableOn ℂ F {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (ha : Integrable (fun y : ℝ => F ((a : ℂ) + y * I)))
    (hb : Integrable (fun y : ℝ => F ((b : ℂ) + y * I)))
    (hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x : ℂ) + (-T) * I))
      atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x : ℂ) + T * I))
      atTop (𝓝 0)) :
    (∫ y : ℝ, F ((a : ℂ) + y * I)) = ∫ y : ℝ, F ((b : ℂ) + y * I) := by
  have hrect (T : ℝ) :
      (∫ x : ℝ in a..b, F ((x : ℂ) + (-T) * I)) -
      (∫ x : ℝ in a..b, F ((x : ℂ) + T * I)) +
      I * (∫ y : ℝ in -T..T, F ((b : ℂ) + y * I)) -
      I * (∫ y : ℝ in -T..T, F ((a : ℂ) + y * I)) = 0 := by
    have h := integral_boundary_rect_eq_zero_of_differentiableOn F
      ((a : ℂ) + (-T) * I) ((b : ℂ) + T * I) (hhol.mono ?_)
    · simpa [smul_eq_mul] using h
    · intro z hz
      have hzre := hz.1
      simpa [uIcc_of_le hab] using hzre
  have hlim := ((hbot.sub htop).add
    ((intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id).const_mul I)).sub
    ((intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id).const_mul I)
  have hzero : (0 : ℂ) - 0 + I * (∫ y : ℝ, F ((b : ℂ) + y * I)) -
      I * (∫ y : ℝ, F ((a : ℂ) + y * I)) = 0 :=
    tendsto_nhds_unique hlim (by simpa only [id_eq, hrect] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0)))
  have heq : I * (∫ y : ℝ, F ((b : ℂ) + y * I)) =
      I * (∫ y : ℝ, F ((a : ℂ) + y * I)) := by simpa using sub_eq_zero.mp hzero
  exact (mul_left_cancel₀ I_ne_zero heq).symm

theorem horizontal_integral_tendsto_zero (F : ℂ → ℂ) (a b C : ℝ)
    (hbound : ∀ x ∈ Set.uIcc a b, ∀ y : ℝ,
      ‖F ((x : ℂ) + y * I)‖ ≤ C * Real.exp (-(y ^ 2))) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x : ℂ) + T * I)) atTop (𝓝 0) := by
  have hnorm (T : ℝ) : ‖∫ x : ℝ in a..b, F ((x : ℂ) + T * I)‖ ≤
      C * Real.exp (-(T ^ 2)) * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x hx => hbound x (uIoc_subset_uIcc hx) T)
  have hexp : Tendsto (fun T : ℝ => Real.exp (-(T ^ 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop (by decide)))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) hnorm
    (by simpa using (hexp.const_mul C).mul_const |b-a|)

theorem integrable_of_gaussian_bound (f : ℝ → ℂ) (C : ℝ)
    (hmeas : AEStronglyMeasurable f) (hbound : ∀ y, ‖f y‖ ≤ C * Real.exp (-(y ^ 2))) :
    Integrable f := by
  have hg : Integrable (fun y : ℝ => C * Real.exp (-(y ^ 2))) := by
    simpa using (integrable_exp_neg_mul_sq (b := 1) (by norm_num)).const_mul C
  exact hg.mono' hmeas (ae_of_all _ hbound)

theorem vertical_integral_eq_of_gaussian_bound (F : ℂ → ℂ) {a b C : ℝ}
    (hab : a ≤ b) (hhol : DifferentiableOn ℂ F {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (hbound : ∀ x ∈ Icc a b, ∀ y : ℝ,
      ‖F ((x : ℂ) + y * I)‖ ≤ C * Real.exp (-(y ^ 2))) :
    (∫ y : ℝ, F ((a : ℂ) + y * I)) = ∫ y : ℝ, F ((b : ℂ) + y * I) := by
  have hc (x : ℝ) (hx : x ∈ Icc a b) : Continuous (fun y : ℝ => F ((x : ℂ) + y * I)) :=
    hhol.continuousOn.comp_continuous (by fun_prop) (by intro y; simpa using hx)
  apply vertical_integral_eq_of_horizontal_vanish F hab hhol
    (integrable_of_gaussian_bound _ C (hc a ⟨le_rfl, hab⟩).aestronglyMeasurable
      (hbound a ⟨le_rfl, hab⟩))
    (integrable_of_gaussian_bound _ C (hc b ⟨hab, le_rfl⟩).aestronglyMeasurable
      (hbound b ⟨hab, le_rfl⟩))
  · have h := horizontal_integral_tendsto_zero (fun s => F ((s.re : ℂ) - s.im * I)) a b C ?_
    · simpa [sub_eq_add_neg, neg_mul] using h
    · intro x hx y
      simpa [sub_eq_add_neg, neg_mul] using hbound x (by simpa [uIcc_of_le hab] using hx) (-y)
  · exact horizontal_integral_tendsto_zero F a b C
      (by simpa [uIcc_of_le hab] using hbound)

def gaussianContourIntegrand (G : ℂ → ℂ) (c Z : ℝ) (s : ℂ) : ℂ :=
  (Z : ℂ) ^ (s + (c : ℂ)) * Complex.exp ((s - 5 / 6) ^ 2) * G s

theorem norm_gaussianContourIntegrand (G : ℂ → ℂ) (c x y : ℝ) {Z : ℝ}
    (hZ : 0 < Z) :
    ‖gaussianContourIntegrand G c Z ((x : ℂ) + y * I)‖ =
      Z ^ (x + c) * Real.exp ((x - 5 / 6) ^ 2) *
        ‖G ((x : ℂ) + y * I)‖ * Real.exp (-(y ^ 2)) := by
  unfold gaussianContourIntegrand
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hZ, Complex.norm_exp]
  have hre : ((((x : ℂ) + y * I) - 5 / 6) ^ 2).re = (x - 5 / 6) ^ 2 - y ^ 2 := by
    simp [pow_two]
  rw [hre, Real.exp_sub]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, zero_mul, sub_self,
    add_zero, Real.exp_neg]
  ring

theorem gaussianContourIntegrand_differentiableOn {G : ℂ → ℂ} {U : Set ℂ}
    (hG : DifferentiableOn ℂ G U) (c : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    DifferentiableOn ℂ (gaussianContourIntegrand G c Z) U := by
  apply DifferentiableOn.mul _ hG
  apply DifferentiableOn.mul
  · exact ((differentiable_id.add_const (c : ℂ)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))).differentiableOn
  · exact (((differentiable_id.sub_const (5 / 6 : ℂ)).pow 2).cexp).differentiableOn

end SevenEighths.Continuation

end

end OAI
end OAIOriginalModule1190

/-! Original module: OAI.NumberTheory.DirichletL.ContinuationPolynomialContour
Source SHA256: ca696aa09c2045be9482062c22c0e89d997c02b802af1605348765a91682253d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1191



namespace OAI

noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology
namespace SevenEighths.Continuation

def polynomialGaussian (n : ℕ) (y : ℝ) : ℝ :=
  (1+|y|^n)*Real.exp (-(y^2))

theorem polynomialGaussian_nonneg (n : ℕ) (y : ℝ) : 0 ≤ polynomialGaussian n y := by
  unfold polynomialGaussian
  positivity

theorem polynomialGaussian_even (n : ℕ) (y : ℝ) :
    polynomialGaussian n (-y) = polynomialGaussian n y := by
  simp [polynomialGaussian]

theorem polynomialGaussian_integrable (n : ℕ) : Integrable (polynomialGaussian n) := by
  have hp := (integrable_rpow_mul_exp_neg_mul_sq
    (by norm_num : (0 : ℝ)<1) (show (-1 : ℝ)<(n : ℝ) by linarith [Nat.cast_nonneg (α := ℝ) n])).norm
  have hg := integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  have he : (fun y : ℝ => ‖y^(n : ℝ)*Real.exp (-1*y^2)‖) =
      fun y : ℝ => |y|^n*Real.exp (-(y^2)) := by
    funext y
    simp [Real.rpow_natCast, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [he] at hp
  convert hg.add hp using 1
  funext y
  simp [polynomialGaussian, add_mul]

theorem polynomialGaussian_tendsto (n : ℕ) :
    Tendsto (polynomialGaussian n) atTop (𝓝 0) := by
  have hp := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
    (by norm_num : (0 : ℝ)<1) (n : ℝ)
  rw [cocompact_eq_atBot_atTop] at hp
  have hp' := hp.mono_left le_sup_right
  have hg : Tendsto (fun y : ℝ => Real.exp (-(y^2))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop (by decide)))
  change Tendsto (fun y : ℝ => (1+|y|^n)*Real.exp (-(y^2))) atTop (𝓝 0)
  simpa [Real.rpow_natCast, add_mul] using hg.add hp'

theorem vertical_integral_eq_of_even_envelope (F : ℂ → ℂ) {a b C : ℝ}
    (E : ℝ → ℝ) (hE : Integrable E) (heven : ∀ y, E (-y)=E y)
    (hlim : Tendsto E atTop (𝓝 0)) (hab : a ≤ b)
    (hhol : DifferentiableOn ℂ F {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (hbound : ∀ x ∈ Icc a b, ∀ y : ℝ, ‖F ((x : ℂ)+y*I)‖ ≤ C*E y) :
    (∫ y : ℝ, F ((a : ℂ)+y*I)) = ∫ y : ℝ, F ((b : ℂ)+y*I) := by
  have hc (x : ℝ) (hx : x ∈ Icc a b) : Continuous (fun y : ℝ => F ((x : ℂ)+y*I)) :=
    hhol.continuousOn.comp_continuous (by fun_prop) (by intro y; simpa using hx)
  have hint (x : ℝ) (hx : x ∈ Icc a b) : Integrable (fun y : ℝ => F ((x : ℂ)+y*I)) :=
    (hE.const_mul C).mono' (hc x hx).aestronglyMeasurable (ae_of_all _ (hbound x hx))
  have hhorizontal (sgn : ℝ) (heq : ∀ y, E (sgn*y)=E y) :
      Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x : ℂ)+(sgn*T)*I)) atTop (𝓝 0) := by
    have hnorm (T : ℝ) : ‖∫ x : ℝ in a..b, F ((x : ℂ)+(sgn*T)*I)‖ ≤ C*E T*|b-a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      simpa only [heq, Complex.ofReal_mul] using hbound x (by simpa [uIcc_of_le hab] using uIoc_subset_uIcc hx) (sgn*T)
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hnorm
      (by simpa using (hlim.const_mul C).mul_const |b-a|)
  apply vertical_integral_eq_of_horizontal_vanish F hab hhol
    (hint a ⟨le_rfl,hab⟩) (hint b ⟨hab,le_rfl⟩)
  · simpa only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul] using hhorizontal (-1) (by simpa only [neg_one_mul] using heven)
  · simpa only [Complex.ofReal_one, one_mul] using hhorizontal 1 (by simp)

theorem vertical_integral_eq_of_polynomial_gaussian_bound (F : ℂ → ℂ)
    {a b C : ℝ} (n : ℕ) (hab : a ≤ b)
    (hhol : DifferentiableOn ℂ F {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (hbound : ∀ x ∈ Icc a b, ∀ y : ℝ,
      ‖F ((x : ℂ)+y*I)‖ ≤ C*polynomialGaussian n y) :
    (∫ y : ℝ, F ((a : ℂ)+y*I)) = ∫ y : ℝ, F ((b : ℂ)+y*I) :=
  vertical_integral_eq_of_even_envelope F _ (polynomialGaussian_integrable n)
    (polynomialGaussian_even n) (polynomialGaussian_tendsto n) hab hhol hbound

end SevenEighths.Continuation

end

end OAI
end OAIOriginalModule1191

/-! Original module: OAI.NumberTheory.DirichletL.ContinuationShiftedGaussian
Source SHA256: a0d495d50a5f6d6bb4ddc44f886fddb86c33e9a7798d8d5d8b4854c671e0cd35
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1192


namespace OAI

noncomputable section
open MeasureTheory Set Filter Complex
namespace SevenEighths.Continuation

theorem vertical_integral_eq_of_shifted_polynomial_gaussian_bound (F : ℂ→ℂ)
    {a b C : ℝ} (q : ℝ) (n : ℕ) (hab : a≤b)
    (hhol : DifferentiableOn ℂ F {s : ℂ | a≤s.re ∧ s.re≤b})
    (hbound : ∀x∈Icc a b,∀t : ℝ,
      ‖F ((x:ℂ)+t*I)‖≤C*polynomialGaussian n (t+q)) :
    (∫t : ℝ,F ((a:ℂ)+t*I))=∫t : ℝ,F ((b:ℂ)+t*I) := by
  let G : ℂ→ℂ := fun s=>F (s-(q:ℂ)*I)
  have hg : DifferentiableOn ℂ G {s : ℂ | a≤s.re ∧ s.re≤b} := by
    apply hhol.comp (differentiable_id.sub_const ((q:ℂ)*I)).differentiableOn
    intro s hs
    simpa using hs
  have hbnd (x : ℝ) (hx : x∈Icc a b) (t : ℝ) :
      ‖G ((x:ℂ)+t*I)‖≤C*polynomialGaussian n t := by
    have heq : (x:ℂ)+t*I-(q:ℂ)*I=(x:ℂ)+(t-q)*I := by ring
    simpa only [G,heq,sub_add_cancel,Complex.ofReal_sub] using hbound x hx (t-q)
  have hi := vertical_integral_eq_of_polynomial_gaussian_bound G n hab hg hbnd
  have heq (x : ℝ) : (∫t : ℝ,G ((x:ℂ)+t*I))=∫t : ℝ,F ((x:ℂ)+t*I) := by
    have hg' : (fun t : ℝ=>G ((x:ℂ)+t*I))=(fun t : ℝ=>F ((x:ℂ)+(t+(-q))*I)) := by
      funext t
      dsimp [G]
      congr 1
      ring
    rw [hg']
    simpa only [Complex.ofReal_add,Complex.ofReal_neg] using
      (integral_add_right_eq_self (fun t : ℝ=>F ((x:ℂ)+t*I)) (-q) (μ:=volume))
  simpa only [heq] using hi

lemma shifted_height_two (t q : ℝ) :
    (3+|t|)^2≤2*(3+|q|)^2*(1+|t+q|^2) := by
  have ht : |t|≤|t+q|+|q| := by
    calc
      |t|=|(t+q)+(-q)| := by ring_nf
      _ ≤ |t+q|+|-q| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  have hq : 0≤|q| := abs_nonneg _
  have hu : 0≤|t+q| := abs_nonneg _
  have hb : (3+|t|)^2≤(3+|q|+|t+q|)^2 := by
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hs := sq_nonneg ((3+|q|)-|t+q|)
  have hm : 0≤((3+|q|)^2-1)*|t+q|^2 := mul_nonneg (by nlinarith) (sq_nonneg _)
  nlinarith

end SevenEighths.Continuation

end

end OAI
end OAIOriginalModule1192

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.MellinIdentity
Source SHA256: 8b1f94243f41d7c3ff5389878798161c84f0fef545fd5d28c277d805ccae1f14
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1193



namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace SevenEighths.HeckeMellinIdentity

def regularized (P : WeakFEPair ℂ) (s : ℂ) : ℂ :=
  s * (s - 1) * P.Λ₀ s - (s - 1) * P.f₀ + s * P.ε * P.g₀

theorem regularized_entire (P : WeakFEPair ℂ) : Differentiable ℂ (regularized P) := by
  unfold regularized
  have hd := P.differentiable_Λ₀
  fun_prop

theorem regularized_eq (P : WeakFEPair ℂ) (hk : P.k = 1) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) : regularized P s = s * (s-1) * P.Λ s := by
  unfold regularized WeakFEPair.Λ
  rw [hk]
  simp only [smul_eq_mul, Complex.ofReal_one]
  have h1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  ring

theorem scaled_eq (P Q : WeakFEPair ℂ) (hP : P.k = 1) (hQ : Q.k = 1)
    (A : ℝ) (hA : 0 < A)
    (hright : ∀ s : ℂ, 1 < s.re → P.Λ s = (A : ℂ)^(-s) * Q.Λ s)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    P.Λ s = (A : ℂ)^(-s) * Q.Λ s := by
  have hd : Differentiable ℂ (fun z : ℂ => (A : ℂ)^(-z) * regularized Q z) :=
    ((differentiable_id.neg).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hA.ne'))).mul (regularized_entire Q)
  have he : regularized P = fun z : ℂ => (A : ℂ)^(-z) * regularized Q z := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr (regularized_entire P)).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hd) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
    have hz1 : z ≠ 1 := by intro h; norm_num [h] at hz
    rw [regularized_eq P hP hz0 hz1, regularized_eq Q hQ hz0 hz1, hright z hz]
    ring
  have heq := congr_fun he s
  rw [regularized_eq P hP h0 h1, regularized_eq Q hQ h0 h1] at heq
  apply mul_left_cancel₀ (mul_ne_zero h0 (sub_ne_zero.mpr h1))
  calc
    s * (s - 1) * P.Λ s = (A : ℂ)^(-s) * (s * (s-1) * Q.Λ s) := heq
    _ = s * (s-1) * ((A : ℂ)^(-s) * Q.Λ s) := by ring

theorem eq_of_f (P Q : WeakFEPair ℂ) (hP : P.k = 1) (hQ : Q.k = 1)
    (hf : ∀ t : ℝ, 0 < t → P.f t = Q.f t) (hf₀ : P.f₀ = Q.f₀)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : P.Λ s = Q.Λ s := by
  have h := scaled_eq P Q hP hQ 1 zero_lt_one (fun z hz => by
    simp only [Complex.ofReal_one, Complex.one_cpow, one_mul]
    rw [← (P.hasMellin (by rwa [hP])).2, ← (Q.hasMellin (by rwa [hQ])).2]
    unfold mellin
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [hf t ht, hf₀]) h0 h1
  simpa only [Complex.ofReal_one, Complex.one_cpow, one_mul] using h

end SevenEighths.HeckeMellinIdentity

end

end OAI
end OAIOriginalModule1193

/-! Original module: OAI.NumberTheory.DirichletL.ThetaProduct
Source SHA256: 6748e3720bcd136b2c688b12b5cc50f7fab6a764d9da82ba87e7149b86d75595
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1194



namespace OAI

noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology

namespace SevenEighths.ThetaProduct

theorem rapid_product_sub (f g : ℝ → ℂ) (a b : ℂ)
    (hf : ∀ r : ℝ, (fun x => f x - a) =O[atTop] (fun x : ℝ => x ^ r))
    (hg : ∀ r : ℝ, (fun x => g x - b) =O[atTop] (fun x : ℝ => x ^ r))
    (r : ℝ) :
    (fun x => f x * g x - a * b) =O[atTop] (fun x : ℝ => x ^ r) := by
  have hg0 : g =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
    have hc : (fun _ : ℝ => b) =O[atTop] (fun x : ℝ => x ^ (0 : ℝ)) := by
      simpa using (isBigO_const_one ℝ b (atTop : Filter ℝ))
    have h := (hg 0).add hc
    simpa using h
  have h₁ := (hf r).mul hg0
  have h₂ := (hg r).const_mul_left a
  have hid : (fun x => f x * g x - a * b) =
      fun x => (f x - a) * g x + a * (g x - b) := by
    funext x
    ring
  rw [hid]
  have h₁' : (fun x => (f x - a) * g x) =O[atTop] (fun x : ℝ => x ^ r) := by
    simpa using h₁
  exact h₁'.add h₂

def product (P Q : WeakFEPair ℂ)
    (hPf : ContinuousOn P.f (Ioi 0)) (hPg : ContinuousOn P.g (Ioi 0))
    (hQf : ContinuousOn Q.f (Ioi 0)) (hQg : ContinuousOn Q.g (Ioi 0)) :
    WeakFEPair ℂ where
  f := fun x => P.f x * Q.f x
  g := fun x => P.g x * Q.g x
  k := P.k + Q.k
  ε := P.ε * Q.ε
  f₀ := P.f₀ * Q.f₀
  g₀ := P.g₀ * Q.g₀
  hf_int := (hPf.mul hQf).locallyIntegrableOn measurableSet_Ioi
  hg_int := (hPg.mul hQg).locallyIntegrableOn measurableSet_Ioi
  hk := add_pos P.hk Q.hk
  hε := mul_ne_zero P.hε Q.hε
  h_feq x hx := by
    rw [P.h_feq x hx, Q.h_feq x hx, Real.rpow_add hx]
    simp only [smul_eq_mul, Complex.ofReal_mul]
    ring
  hf_top := rapid_product_sub P.f Q.f P.f₀ Q.f₀ P.hf_top Q.hf_top
  hg_top := rapid_product_sub P.g Q.g P.g₀ Q.g₀ P.hg_top Q.hg_top

theorem rapid_rescale (f : ℝ → ℂ) (a : ℂ)
    (hf : ∀ r : ℝ, (fun x => f x - a) =O[atTop] (fun x : ℝ => x ^ r))
    {u : ℝ} (hu : 0 < u) (r : ℝ) :
    (fun x => f (u * x) - a) =O[atTop] (fun x : ℝ => x ^ r) := by
  have ht : Tendsto (fun x : ℝ => u * x) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hu).2 tendsto_id
  have h := (hf r).comp_tendsto ht
  have heq : (fun x : ℝ => (u * x) ^ r) =ᶠ[atTop]
      (fun x : ℝ => u ^ r * x ^ r) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact Real.mul_rpow hu.le hx
  exact h.trans (heq.isBigO.trans ((isBigO_refl (fun x : ℝ => x ^ r) atTop).const_mul_left _))

def rescale (P : WeakFEPair ℂ)
    (hPf : ContinuousOn P.f (Ioi 0)) (hPg : ContinuousOn P.g (Ioi 0))
    (u : ℝ) (hu : 0 < u) : WeakFEPair ℂ where
  f := fun x => P.f (u * x)
  g := fun x => P.g (u⁻¹ * x)
  k := P.k
  ε := P.ε * (u ^ (-P.k) : ℝ)
  f₀ := P.f₀
  g₀ := P.g₀
  hf_int := (hPf.comp (by fun_prop) (fun x hx => mul_pos hu hx)).locallyIntegrableOn
    measurableSet_Ioi
  hg_int := (hPg.comp (by fun_prop) (fun x hx => mul_pos (inv_pos.mpr hu) hx)).locallyIntegrableOn
    measurableSet_Ioi
  hk := P.hk
  hε := mul_ne_zero P.hε (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hu _).ne')
  h_feq x hx := by
    have heq : u * (1 / x) = 1 / (u⁻¹ * x) := by field_simp
    rw [heq, P.h_feq _ (mul_pos (inv_pos.mpr hu) hx),
      Real.mul_rpow (inv_pos.mpr hu).le hx.le, Real.inv_rpow hu.le,
      ← Real.rpow_neg hu.le]
    simp only [smul_eq_mul, Complex.ofReal_mul]
    ring
  hf_top := rapid_rescale P.f P.f₀ P.hf_top hu
  hg_top := rapid_rescale P.g P.g₀ P.hg_top (inv_pos.mpr hu)

def shiftedPair (a b : UnitAddCircle) : WeakFEPair ℂ :=
  product (HurwitzZeta.hurwitzEvenFEPair a) (HurwitzZeta.hurwitzEvenFEPair b)
    (Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_evenKernel a))
    (Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_cosKernel a))
    (Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_evenKernel b))
    (Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_cosKernel b))

@[simp] theorem shiftedPair_k (a b : UnitAddCircle) : (shiftedPair a b).k = 1 := by
  norm_num [shiftedPair, product, HurwitzZeta.hurwitzEvenFEPair]

@[simp] theorem shiftedPair_f (a b : UnitAddCircle) (t : ℝ) :
    (shiftedPair a b).f t =
      (HurwitzZeta.evenKernel a t : ℂ) * (HurwitzZeta.evenKernel b t : ℂ) := rfl

theorem shiftedPair_differentiableAt (a b : UnitAddCircle) {s : ℂ}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    DifferentiableAt ℂ (shiftedPair a b).Λ s := by
  exact (shiftedPair a b).differentiableAt_Λ (Or.inl hs₀)
    (Or.inl (by simpa using hs₁))

def scaledEvenPair (a : UnitAddCircle) (u : ℝ) (hu : 0 < u) : WeakFEPair ℂ :=
  rescale (HurwitzZeta.hurwitzEvenFEPair a)
    (Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_evenKernel a))
    (Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_cosKernel a)) u hu

theorem scaledEvenPair_f_continuous (a : UnitAddCircle) (u : ℝ) (hu : 0 < u) :
    ContinuousOn (scaledEvenPair a u hu).f (Ioi 0) :=
  (Complex.continuous_ofReal.comp_continuousOn
    (HurwitzZeta.continuousOn_evenKernel a)).comp (by fun_prop)
      (fun x hx => mul_pos hu hx)

theorem scaledEvenPair_g_continuous (a : UnitAddCircle) (u : ℝ) (hu : 0 < u) :
    ContinuousOn (scaledEvenPair a u hu).g (Ioi 0) :=
  (Complex.continuous_ofReal.comp_continuousOn
    (HurwitzZeta.continuousOn_cosKernel a)).comp (by fun_prop)
      (fun x hx => mul_pos (inv_pos.mpr hu) hx)

def rectangularPair (a b : UnitAddCircle) (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    WeakFEPair ℂ :=
  product (scaledEvenPair a u hu) (scaledEvenPair b v hv)
    (scaledEvenPair_f_continuous a u hu) (scaledEvenPair_g_continuous a u hu)
    (scaledEvenPair_f_continuous b v hv) (scaledEvenPair_g_continuous b v hv)

@[simp] theorem rectangularPair_k (a b : UnitAddCircle) (u v : ℝ)
    (hu : 0 < u) (hv : 0 < v) : (rectangularPair a b u v hu hv).k = 1 := by
  norm_num [rectangularPair, scaledEvenPair, rescale, product, HurwitzZeta.hurwitzEvenFEPair]

theorem rectangularPair_hasSum (a b u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ =>
      (Real.exp (-Real.pi * (u * (n.1 + a) ^ 2 + v * (n.2 + b) ^ 2) * t) : ℂ))
      ((rectangularPair a b u v hu hv).f t) := by
  have h₁ := HurwitzZeta.hasSum_int_evenKernel a (mul_pos hu ht)
  have h₂ := HurwitzZeta.hasSum_int_evenKernel b (mul_pos hv ht)
  have hprod := h₁.mul h₂ (h₁.summable.mul_of_nonneg h₂.summable
    (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le))
  have hid (n : ℤ × ℤ) :
      Real.exp (-Real.pi * (u * (n.1 + a) ^ 2 + v * (n.2 + b) ^ 2) * t) =
      Real.exp (-Real.pi * (n.1 + a) ^ 2 * (u * t)) *
        Real.exp (-Real.pi * (n.2 + b) ^ 2 * (v * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [hid]
  simpa only [rectangularPair, product, scaledEvenPair, rescale,
    HurwitzZeta.hurwitzEvenFEPair, Function.comp_apply, Complex.ofReal_mul] using
    (Complex.hasSum_ofReal.mpr hprod)

theorem rectangularPair_differentiableAt (a b : UnitAddCircle) (u v : ℝ)
    (hu : 0 < u) (hv : 0 < v) {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    DifferentiableAt ℂ (rectangularPair a b u v hu hv).Λ s := by
  exact (rectangularPair a b u v hu hv).differentiableAt_Λ (Or.inl hs₀)
    (Or.inl (by simpa using hs₁))

end SevenEighths.ThetaProduct

end

end OAI
end OAIOriginalModule1194

/-! Original module: OAI.NumberTheory.DirichletL.EisensteinTheta
Source SHA256: da30674e27b65d10a3f472564263c57e26c24a9f1986e22cdcab26209e79da17
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1195




namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace SevenEighths.EisensteinTheta
open ThetaProduct

def normForm (x y : ℝ) : ℝ := x ^ 2 - x * y + y ^ 2

def shearEquiv : (ℤ × (ℤ × Fin 2)) ≃ (Fin 2 × (ℤ × ℤ)) where
  toFun n := (n.2.2, (n.1 - n.2.1, n.2.1))
  invFun p := (p.2.1 + p.2.2, (p.2.2, p.1))
  left_inv n := by simp
  right_inv p := by simp

def parityEquiv : (ℤ × ℤ) ≃ (Fin 2 × (ℤ × ℤ)) :=
  (Equiv.prodCongr (Equiv.refl ℤ) (Int.divModEquiv 2)).trans shearEquiv

def xShift (a b L : ℝ) (e : Fin 2) : ℝ := (2 * a - b - L * e) / (2 * L)
def yShift (b L : ℝ) (e : Fin 2) : ℝ := (b + L * e) / (2 * L)

theorem normForm_parity (a b L : ℝ) (hL : L ≠ 0) (e : Fin 2) (i j : ℤ) :
    normForm (a + L * (i + j)) (b + L * (2 * j + e)) =
      L ^ 2 * (i + xShift a b L e) ^ 2 +
        (3 * L ^ 2) * (j + yShift b L e) ^ 2 := by
  unfold normForm xShift yShift
  field_simp
  ring

def cosetTheta (a b L t : ℝ) : ℂ :=
  ∑' n : ℤ × ℤ,
    (Real.exp (-Real.pi * normForm (a + L * n.1) (b + L * n.2) * t) : ℂ)

def parityPair (a b L : ℝ) (hL : 0 < L) (e : Fin 2) : WeakFEPair ℂ :=
  rectangularPair (xShift a b L e) (yShift b L e) (L ^ 2) (3 * L ^ 2)
    (sq_pos_of_pos hL) (mul_pos (by norm_num) (sq_pos_of_pos hL))

theorem cosetTheta_hasSum (a b L : ℝ) (hL : 0 < L) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ =>
      (Real.exp (-Real.pi * normForm (a + L * n.1) (b + L * n.2) * t) : ℂ))
      (∑ e : Fin 2, (parityPair a b L hL e).f t) := by
  let F : Fin 2 × (ℤ × ℤ) → ℝ := fun p =>
    Real.exp (-Real.pi * (L ^ 2 * (p.2.1 + xShift a b L p.1) ^ 2 +
      (3 * L ^ 2) * (p.2.2 + yShift b L p.1) ^ 2) * t)
  have hsum (e : Fin 2) : HasSum (fun n : ℤ × ℤ => (F (e, n) : ℂ))
      ((parityPair a b L hL e).f t) :=
    rectangularPair_hasSum (xShift a b L e) (yShift b L e) (L ^ 2) (3 * L ^ 2) (sq_pos_of_pos hL)
      (mul_pos (by norm_num) (sq_pos_of_pos hL)) ht
  have hreal (e : Fin 2) : Summable (fun n : ℤ × ℤ => F (e, n)) :=
    Complex.summable_ofReal.mp (hsum e).summable
  have hF : Summable F :=
    (summable_prod_of_nonneg (fun _ => (Real.exp_pos _).le)).2
      ⟨hreal, (hasSum_fintype _).summable⟩
  have hFC : Summable (fun p => (F p : ℂ)) := Complex.summable_ofReal.mpr hF
  have hid (p : Fin 2 × (ℤ × ℤ)) :
      Real.exp (-Real.pi * normForm
        (a + L * (parityEquiv.symm p).1) (b + L * (parityEquiv.symm p).2) * t) = F p := by
    change Real.exp (-Real.pi * normForm
      (a + L * ((p.2.1 + p.2.2 : ℤ) : ℝ))
      (b + L * ((p.2.2 * 2 + (p.1 : ℕ) : ℤ) : ℝ)) * t) = _
    push_cast
    rw [show (p.2.2 : ℝ) * 2 = 2 * p.2.2 from mul_comm _ _]
    rw [normForm_parity a b L hL.ne']
  apply parityEquiv.symm.hasSum_iff.mp
  change HasSum (fun p : Fin 2 × (ℤ × ℤ) =>
    (Real.exp (-Real.pi * normForm (a + L * (parityEquiv.symm p).1)
      (b + L * (parityEquiv.symm p).2) * t) : ℂ)) _
  simp_rw [hid]
  convert hFC.hasSum using 1
  rw [hFC.tsum_prod, tsum_fintype]
  exact (Finset.sum_congr rfl (fun e _ => (hsum e).tsum_eq)).symm

theorem cosetTheta_eq_parity_sum (a b L : ℝ) (hL : 0 < L) {t : ℝ} (ht : 0 < t) :
    cosetTheta a b L t = ∑ e : Fin 2, (parityPair a b L hL e).f t :=
  (cosetTheta_hasSum a b L hL ht).tsum_eq

@[simp] theorem parityPair_k (a b L : ℝ) (hL : 0 < L) (e : Fin 2) :
    (parityPair a b L hL e).k = 1 := rectangularPair_k _ _ _ _ _ _

def cosetConstant (a b L : ℝ) (hL : 0 < L) : ℂ :=
  ∑ e : Fin 2, (parityPair a b L hL e).f₀

theorem parityPair_f₀ (a b L : ℝ) (hL : 0 < L) (e : Fin 2) :
    (parityPair a b L hL e).f₀ =
      (if (xShift a b L e : UnitAddCircle) = 0 then 1 else 0) *
      (if (yShift b L e : UnitAddCircle) = 0 then 1 else 0) := rfl

theorem cosetConstant_eq (a b L : ℝ) (hL : 0 < L)
    (ha₀ : 0 ≤ a) (haL : a < L) (hb₀ : 0 ≤ b) (hbL : b < L) :
    cosetConstant a b L hL = if a = 0 ∧ b = 0 then 1 else 0 := by
  have htwo : 0 < 2 * L := by positivity
  have hy1 : yShift b L 1 ∈ Set.Ico (0 : ℝ) 1 := by
    simp only [yShift, Fin.val_one, Nat.cast_one, mul_one, Set.mem_Ico]
    constructor
    · positivity
    · apply (div_lt_one htwo).2
      linarith
  have hy1pos : 0 < yShift b L 1 := by
    simp only [yShift, Fin.val_one, Nat.cast_one, mul_one]
    exact div_pos (by linarith) htwo
  have hy1ne : (yShift b L 1 : UnitAddCircle) ≠ 0 := by
    intro h
    have := (AddCircle.coe_eq_zero_iff_of_mem_Ico hy1).mp h
    linarith
  have hy0 : yShift b L 0 ∈ Set.Ico (0 : ℝ) 1 := by
    simp only [yShift, Fin.val_zero, Nat.cast_zero, mul_zero, add_zero, Set.mem_Ico]
    constructor
    · positivity
    · apply (div_lt_one htwo).2
      linarith
  have hy0iff : (yShift b L 0 : UnitAddCircle) = 0 ↔ b = 0 := by
    rw [AddCircle.coe_eq_zero_iff_of_mem_Ico hy0]
    simp [yShift, div_eq_zero_iff, hL.ne']
  rw [cosetConstant, Fin.sum_univ_two, parityPair_f₀, parityPair_f₀,
    ite_eq_right hy1ne, mul_zero, add_zero]
  by_cases hb : b = 0
  · subst b
    rw [ite_eq_left (hy0iff.mpr rfl), mul_one]
    have hx : xShift a 0 L 0 = a / L := by
      simp only [xShift, sub_zero, Fin.val_zero, Nat.cast_zero, mul_zero]
      field_simp
    have hxmem : a / L ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨div_nonneg ha₀ hL.le, (div_lt_one hL).2 haL⟩
    have hxiff : (xShift a 0 L 0 : UnitAddCircle) = 0 ↔ a = 0 := by
      rw [hx, AddCircle.coe_eq_zero_iff_of_mem_Ico hxmem]
      simp [div_eq_zero_iff, hL.ne']
    simp only [hxiff, and_true]
  · rw [ite_eq_right (fun h => hb (hy0iff.mp h)), mul_zero, ite_eq_right (fun h => hb h.2)]

def completedCoset (a b L : ℝ) (hL : 0 < L) (s : ℂ) : ℂ :=
  ∑ e : Fin 2, (parityPair a b L hL e).Λ s

theorem completedCoset_differentiableAt (a b L : ℝ) (hL : 0 < L)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    DifferentiableAt ℂ (completedCoset a b L hL) s := by
  apply DifferentiableAt.fun_sum
  intro e _
  exact rectangularPair_differentiableAt (xShift a b L e) (yShift b L e)
    (L ^ 2) (3 * L ^ 2) _ _ hs₀ hs₁

end SevenEighths.EisensteinTheta

end

end OAI
end OAIOriginalModule1195

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.Theta
Source SHA256: 5fe20e38278c74632a0b77aac4bc7a2b6217360378178e0b7dc5085cd73954c9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1196




namespace OAI

noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology BigOperators
namespace SevenEighths.HeckeTheta
open EisensteinTheta

theorem locallyIntegrableOn_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℂ) (hf : ∀ i ∈ s, LocallyIntegrableOn (f i) (Ioi 0)) :
    LocallyIntegrableOn (∑ i ∈ s, f i) (Ioi 0) := by
  exact Finset.sum_induction f (fun g => LocallyIntegrableOn g (Ioi 0))
    (fun _ _ => LocallyIntegrableOn.add) (locallyIntegrableOn_const 0) hf

def finitePair {ι : Type*} [Fintype ι] (P : ι → WeakFEPair ℂ)
    (hk : ∀ i, (P i).k = 1) (w : ι → ℂ) : WeakFEPair ℂ where
  f := ∑ i, w i • (P i).f
  g := ∑ i, (w i * (P i).ε) • (P i).g
  k := 1
  ε := 1
  f₀ := ∑ i, w i * (P i).f₀
  g₀ := ∑ i, w i * (P i).ε * (P i).g₀
  hf_int := locallyIntegrableOn_sum Finset.univ _
    (fun i _ => (P i).hf_int.smul (w i))
  hg_int := locallyIntegrableOn_sum Finset.univ _
    (fun i _ => (P i).hg_int.smul (w i * (P i).ε))
  hk := by norm_num
  hε := one_ne_zero
  h_feq x hx := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, one_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [(P i).h_feq x hx, hk i]
    simp only [smul_eq_mul]
    ring
  hf_top r := by
    have h := Asymptotics.IsBigO.fun_sum (s := Finset.univ)
      (fun i _ => ((P i).hf_top r).const_mul_left (w i))
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_sub_distrib,
      mul_sub] using h
  hg_top r := by
    have h := Asymptotics.IsBigO.fun_sum (s := Finset.univ)
      (fun i _ => ((P i).hg_top r).const_mul_left (w i * (P i).ε))
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_sub_distrib,
      mul_sub] using h

def regroup (N : ℕ) : ((ℤ × Fin N) × (ℤ × Fin N)) ≃ ((Fin N × Fin N) × (ℤ × ℤ)) where
  toFun p := ((p.1.2, p.2.2), (p.1.1, p.2.1))
  invFun p := ((p.2.1, p.1.1), (p.2.2, p.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

def residueEquiv (N : ℕ) [NeZero N] : (ℤ × ℤ) ≃ ((Fin N × Fin N) × (ℤ × ℤ)) :=
  (Equiv.prodCongr (Int.divModEquiv N) (Int.divModEquiv N)).trans (regroup N)

def periodicCoeff {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (n : ℤ × ℤ) : ℂ :=
  w (residueEquiv N n).1

def theta {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℤ × ℤ, periodicCoeff w n *
    (Real.exp (-Real.pi * normForm n.1 n.2 * t) : ℂ)

def pair {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) : WeakFEPair ℂ :=
  finitePair (fun p : (Fin N × Fin N) × Fin 2 =>
    parityPair p.1.1 p.1.2 N (Nat.cast_pos.mpr (NeZero.pos N)) p.2)
    (fun _ => ThetaProduct.rectangularPair_k ..) (fun p => w p.1)

@[simp] theorem pair_k {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    (pair w).k = 1 := rfl

theorem theta_hasSum {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ => periodicCoeff w n *
      (Real.exp (-Real.pi * normForm n.1 n.2 * t) : ℂ)) ((pair w).f t) := by
  let hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  let F : (Fin N × Fin N) × (ℤ × ℤ) → ℂ := fun p => w p.1 *
    (Real.exp (-Real.pi * normForm (p.1.1 + (N : ℝ) * p.2.1)
      (p.1.2 + (N : ℝ) * p.2.2) * t) : ℂ)
  have hinner (a : Fin N × Fin N) : HasSum (fun n : ℤ × ℤ => F (a,n))
      (w a * ∑ e : Fin 2, (parityPair a.1 a.2 N hN e).f t) :=
    (cosetTheta_hasSum a.1 a.2 N hN ht).mul_left (w a)
  have hFnorm : Summable (fun p => ‖F p‖) :=
    (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
      ⟨fun a => (hinner a).summable.norm, (hasSum_fintype _).summable⟩
  have hF : Summable F := hFnorm.of_norm
  have hid (p : (Fin N × Fin N) × (ℤ × ℤ)) :
      periodicCoeff w ((residueEquiv N).symm p) *
        (Real.exp (-Real.pi * normForm (((residueEquiv N).symm p).1)
          (((residueEquiv N).symm p).2) * t) : ℂ) = F p := by
    simp only [periodicCoeff, Equiv.apply_symm_apply]
    change w p.1 * (Real.exp (-Real.pi * normForm
      ((p.2.1 * (N : ℤ) + p.1.1 : ℤ) : ℝ)
      ((p.2.2 * (N : ℤ) + p.1.2 : ℤ) : ℝ) * t) : ℂ) = F p
    simp only [F, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    congr 4 ; ring_nf
  apply (residueEquiv N).symm.hasSum_iff.mp
  change HasSum (fun p => periodicCoeff w ((residueEquiv N).symm p) *
    (Real.exp (-Real.pi * normForm (((residueEquiv N).symm p).1)
      (((residueEquiv N).symm p).2) * t) : ℂ)) _
  simp_rw [hid]
  convert hF.hasSum using 1
  rw [hF.tsum_prod, tsum_fintype]
  simp_rw [(hinner _).tsum_eq]
  simp only [pair, finitePair, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Fintype.sum_prod_type, Finset.mul_sum]

theorem theta_eq_pair {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {t : ℝ} (ht : 0 < t) : theta w t = (pair w).f t :=
  (theta_hasSum w ht).tsum_eq

theorem pair_f₀ {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    (pair w).f₀ = w (0, 0) := by
  have hconst (a : Fin N × Fin N) :
      cosetConstant a.1 a.2 N (Nat.cast_pos.mpr (NeZero.pos N)) =
        if a = (0, 0) then 1 else 0 := by
    rw [cosetConstant_eq _ _ _ _ (by positivity) (by exact_mod_cast a.1.isLt)
      (by positivity) (by exact_mod_cast a.2.isLt)]
    have hz : (a.1 : ℝ) = 0 ∧ (a.2 : ℝ) = 0 ↔ a = (0, 0) := by
      simp only [Prod.ext_iff, Fin.ext_iff, Fin.val_zero, Nat.cast_eq_zero]
    simp only [hz]
  change (∑ p : (Fin N × Fin N) × Fin 2,
    w p.1 * (parityPair p.1.1 p.1.2 N _ p.2).f₀) = _
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  change (∑ a : Fin N × Fin N, w a * cosetConstant a.1 a.2 N _) = _
  simp_rw [hconst]
  simp

def dualScalar (N : ℕ) : ℂ :=
  ((((N : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    (((3 * (N : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)

theorem pair_g₀ {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    (pair w).g₀ = 2 * dualScalar N * ∑ a, w a := by
  simp only [pair, finitePair, parityPair, ThetaProduct.rectangularPair,
    ThetaProduct.product, ThetaProduct.scaledEvenPair, ThetaProduct.rescale,
    HurwitzZeta.hurwitzEvenFEPair, one_mul, mul_one]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  simp_rw [← two_mul]
  rw [← Finset.mul_sum]
  simp only [← Finset.sum_mul, dualScalar]
  ring

theorem pair_g₀_eq_zero {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    (hw : ∑ a, w a = 0) : (pair w).g₀ = 0 := by rw [pair_g₀, hw, mul_zero]

def completed {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) : ℂ → ℂ := (pair w).Λ

theorem completed_differentiableAt {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) : DifferentiableAt ℂ (completed w) s :=
  (pair w).differentiableAt_Λ (Or.inl hs₀) (Or.inl (by simpa using hs₁))

theorem pair_hasMellin {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun t => (pair w).f t - (pair w).f₀) s (completed w s) :=
  (pair w).hasMellin (by simpa using hs)

def latticeL {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹ * completed w s

theorem completed_differentiableAt_of_mean_zero {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) (hw : ∑ a, w a = 0) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (completed w) s :=
  (pair w).differentiableAt_Λ (Or.inl hs₀) (Or.inr (pair_g₀_eq_zero w hw))

theorem latticeL_differentiableAt {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ ∑ a, w a = 0) :
    DifferentiableAt ℂ (latticeL w) s := by
  have hΛ : DifferentiableAt ℂ (completed w) s := by
    rcases hs₁ with hs₁ | hw
    · exact completed_differentiableAt w hs₀ hs₁
    · exact completed_differentiableAt_of_mean_zero w hw hs₀
  exact (((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableAt).mul
      (Complex.differentiable_one_div_Gamma s)).mul hΛ

def regularizedCompleted {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (s : ℂ) : ℂ :=
  (s - 1) * ((pair w).Λ₀ s - s⁻¹ * (pair w).f₀) + (pair w).g₀

theorem regularizedCompleted_differentiableAt {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (regularizedCompleted w) s := by
  exact (((differentiableAt_id.sub_const 1).mul
    (((pair w).differentiable_Λ₀ s).sub
      ((differentiableAt_id.inv hs₀).mul_const (pair w).f₀))).add_const (pair w).g₀)

theorem regularizedCompleted_eq {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    regularizedCompleted w s = (s - 1) * completed w s := by
  unfold regularizedCompleted completed WeakFEPair.Λ
  simp only [pair_k, Complex.ofReal_one, show (pair w).ε = 1 from rfl,
    smul_eq_mul, one_div]
  have hsub : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs₁.symm
  field_simp
  ring

def regularizedLatticeL {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹ * regularizedCompleted w s

theorem regularizedLatticeL_differentiableAt {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (regularizedLatticeL w) s := by
  exact (((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableAt).mul
      (Complex.differentiable_one_div_Gamma s)).mul
        (regularizedCompleted_differentiableAt w hs₀)

theorem regularizedLatticeL_eq {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    regularizedLatticeL w s = (s - 1) * latticeL w s := by
  unfold regularizedLatticeL latticeL
  rw [regularizedCompleted_eq w hs₀ hs₁]
  ring

theorem completed_functional_equation {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) (s : ℂ) :
    completed w (1 - s) = (pair w).symm.Λ s := by
  change (pair w).Λ (1 - s) = (pair w).symm.Λ s
  simpa only [pair_k, Complex.ofReal_one, show (pair w).ε = 1 from rfl, one_smul] using
    (pair w).functional_equation s

end SevenEighths.HeckeTheta

end

end OAI
end OAIOriginalModule1196

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.Family
Source SHA256: 9871d175749b34ec40cf66ccc14b4faa0a9ef08831cb3fa901c944e57c7b9ec6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1197






namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeFamily

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ

def omega : O := (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger

def coordinateElement (x y : ℤ) : O := (x : O) + (y : O) * omega

structure Character where
  modulus : Ideal O
  modulus_ne_bot : modulus ≠ ⊥
  residue : MulChar (O ⧸ modulus) ℂ
  unit_trivial : ∀ u : Oˣ, residue (Ideal.Quotient.mk modulus (u : O)) = 1
  period : ℕ
  period_pos : 0 < period
  period_mem : (period : O) ∈ modulus

def Character.ofResidue (M : Ideal O) (hM : M ≠ ⊥)
    (χ : MulChar (O ⧸ M) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk M (u : O)) = 1) : Character := by
  letI : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient hM
  letI : Fintype (O ⧸ M) := Fintype.ofFinite _
  exact {
    modulus := M
    modulus_ne_bot := hM
    residue := χ
    unit_trivial := hu
    period := Fintype.card (O ⧸ M)
    period_pos := Fintype.card_pos
    period_mem := Ideal.Quotient.eq_zero_iff_mem.mp (by
      simpa only [map_natCast] using Nat.cast_card_eq_zero (O ⧸ M)) }

instance (χ : Character) : NeZero χ.period := ⟨Nat.ne_of_gt χ.period_pos⟩

def elementCoeff (χ : Character) (z : O) : ℂ := χ.residue (Ideal.Quotient.mk χ.modulus z)

def coefficients (χ : Character) (a : Fin χ.period × Fin χ.period) : ℂ :=
  elementCoeff χ (coordinateElement a.1 a.2)

@[simp] theorem elementCoeff_one (χ : Character) : elementCoeff χ 1 = 1 := by
  simp [elementCoeff]

theorem elementCoeff_mul (χ : Character) (z w : O) :
    elementCoeff χ (z * w) = elementCoeff χ z * elementCoeff χ w := by
  simp [elementCoeff, map_mul]

theorem elementCoeff_unit_mul (χ : Character) (u : Oˣ) (z : O) :
    elementCoeff χ ((u : O) * z) = elementCoeff χ z := by
  rw [elementCoeff_mul]
  have hu : elementCoeff χ (u : O) = 1 := χ.unit_trivial u
  rw [hu, one_mul]

theorem quotient_period (χ : Character) :
    Ideal.Quotient.mk χ.modulus (χ.period : O) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr χ.period_mem

theorem elementCoeff_add_period_mul (χ : Character) (z w : O) :
    elementCoeff χ (z + (χ.period : O) * w) = elementCoeff χ z := by
  simp [elementCoeff, map_add, map_mul, quotient_period χ]

theorem periodicCoeff_eq_elementCoeff (χ : Character) (n : ℤ × ℤ) :
    HeckeTheta.periodicCoeff (coefficients χ) n =
      elementCoeff χ (coordinateElement n.1 n.2) := by
  obtain ⟨p, rfl⟩ := (HeckeTheta.residueEquiv χ.period).symm.surjective n
  simp only [HeckeTheta.periodicCoeff, Equiv.apply_symm_apply, coefficients]
  change elementCoeff χ (coordinateElement p.1.1 p.1.2) =
    elementCoeff χ (coordinateElement (p.2.1 * (χ.period : ℤ) + p.1.1)
      (p.2.2 * (χ.period : ℤ) + p.1.2))
  have heq : coordinateElement (p.2.1 * (χ.period : ℤ) + p.1.1)
      (p.2.2 * (χ.period : ℤ) + p.1.2) =
      coordinateElement p.1.1 p.1.2 + (χ.period : O) *
        ((p.2.1 : O) + (p.2.2 : O) * omega) := by
    unfold coordinateElement
    push_cast
    ring
  rw [heq, elementCoeff_add_period_mul]

def continuedLattice (χ : Character) : ℂ → ℂ := HeckeTheta.latticeL (coefficients χ)

theorem continuedLattice_differentiableAt (χ : Character) {s : ℂ}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ ∑ a, (coefficients χ) a = 0) :
    DifferentiableAt ℂ (continuedLattice χ) s :=
  HeckeTheta.latticeL_differentiableAt (coefficients χ) hs₀ hs₁

end SevenEighths.HeckeFamily

end

end OAI
end OAIOriginalModule1197

/-! Original module: OAI.NumberTheory.DirichletL.Detector.Row
Source SHA256: 94cd0a68ced17d2ad52c67c13af03a3d199568862ebe43fde2f9f0ed96949ce0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1198




namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve InitialMeanSquare ProbeCompleted

local notation "O" => ActualEisensteinCubic.O

def targetMonoid (η : HeckeFamily.Character) : O →* ℂ where
  toFun := HeckeFamily.elementCoeff η
  map_one' := HeckeFamily.elementCoeff_one η
  map_mul' := HeckeFamily.elementCoeff_mul η

theorem targetMonoid_norm_le_one (η : HeckeFamily.Character) (a : O) :
    ‖targetMonoid η a‖ ≤ 1 := by
  let : Finite (O ⧸ η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (O ⧸ η.modulus) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one η.residue (Ideal.Quotient.mk η.modulus a)

def rowCoefficient (η : HeckeFamily.Character) (Xi : O →* ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m : O) : O →* ℂ :=
  targetMonoid η * conjugateMonoid Xi * reciprocityPhaseMonoid s hs *
    (idealRowHom m).toMonoidHom.comp principalIdealHom.toMonoidHom

theorem rowCoefficient_apply (η : HeckeFamily.Character) (Xi : O →* ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m a : O) :
    rowCoefficient η Xi s hs m a = HeckeFamily.elementCoeff η a * star (Xi a) *
      sexticReciprocityPhase s a * idealRowHom m (Ideal.span {a}) := rfl

theorem rowCoefficient_apply_unit (η : HeckeFamily.Character) (Xi : O →* ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m a : O) (hXi : ‖Xi a‖ = 1) :
    rowCoefficient η Xi s hs m a = HeckeFamily.elementCoeff η a * (Xi a)⁻¹ *
      sexticReciprocityPhase a s * idealRowHom m (Ideal.span {a}) := by
  rw [rowCoefficient_apply]
  have hc : star (Xi a) = (Xi a)⁻¹ := (Complex.inv_eq_conj hXi).symm
  have hsym : sexticReciprocityPhase s a = sexticReciprocityPhase a s := by
    simp only [sexticReciprocityPhase, QuadraticAllOddCRT.quadraticRaySign_symm]
  rw [hc, hsym]

theorem rowCoefficient_norm_le_one (η : HeckeFamily.Character) (Xi : O →* ℂ)
    (hXi : ∀ a, ‖Xi a‖ ≤ 1) (s : O) (hs : Supported (Ideal.span {s})) (m a : O) :
    ‖rowCoefficient η Xi s hs m a‖ ≤ 1 := by
  rw [rowCoefficient_apply]
  simp only [norm_mul, norm_star]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (idealRowHom_norm _ _)
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (sexticReciprocityPhase_norm _ _)
  exact (mul_le_of_le_one_left (norm_nonneg _) (targetMonoid_norm_le_one η a)).trans (hXi a)

def spectralSummand (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (t : ℂ) (I J : Ideal O) : ℂ :=
  (completedMask S D I J * completedCorrection I J *
    (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I) : ℂ)) * cubeWeight Ψ J) *
      (CubicEisenstein.fullIdealWeight t I * CubicEisenstein.fullIdealWeight (3 * t) J)

def spectralRow (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ) (t : ℂ) : ℂ :=
  ∑' p : Ideal O × Ideal O, spectralSummand S D Ψ t p.1 p.2

theorem spectralSummand_norm_le (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (t : ℂ) (I J : Ideal O) :
    ‖spectralSummand S D Ψ t I J‖ ≤
      2 * (‖CubicEisenstein.fullIdealWeight t I‖ *
        ‖CubicEisenstein.fullIdealWeight (3 * t) J‖) := by
  have hmc : ‖completedMask S D I J * completedCorrection I J‖ ≤ 2 := by
    rw [norm_mul]
    exact (mul_le_mul (completedMask_norm_le_one S D I J)
      (completedCorrection_norm_le_two I J) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hcol := columnWeight_div_sqrt_norm_le_one Ψ hΨ I
  have hcube := cubeWeight_norm_le_one Ψ hΨ J
  have hc : ‖completedMask S D I J * completedCorrection I J *
      (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I) : ℂ)) * cubeWeight Ψ J‖ ≤ 2 := by
    rw [norm_mul, norm_mul]
    exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hcube).trans
      ((mul_le_of_le_one_right (norm_nonneg _) hcol).trans hmc)
  unfold spectralSummand
  simpa only [norm_mul] using mul_le_mul_of_nonneg_right hc (mul_nonneg
    (norm_nonneg (CubicEisenstein.fullIdealWeight t I))
    (norm_nonneg (CubicEisenstein.fullIdealWeight (3 * t) J)))

theorem spectralRow_summable (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (t : ℂ) (ht : 1 < t.re) :
    Summable (fun p : Ideal O × Ideal O => spectralSummand S D Ψ t p.1 p.2) := by
  have ht3 : 1 < (3 * t).re := by
    norm_num [Complex.mul_re]
    linarith
  have h1 := CubicEisenstein.fullIdealWeight_summable_norm t ht
  have h3 := CubicEisenstein.fullIdealWeight_summable_norm (3 * t) ht3
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => spectralSummand_norm_le S D Ψ hΨ t p.1 p.2)
    ((h1.mul_of_nonneg h3 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left 2)

end SevenEighths.ProbeRow
end

end OAI
end OAIOriginalModule1198

/-! Original module: OAI.NumberTheory.DirichletL.Detector.EulerCoordinates
Source SHA256: 3c3a1b462473693820fd0a530b1b3a860b9b55fec2b2e38ebabf543ffc3a2943
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1199



namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss
local notation "O" => ActualEisensteinCubic.O

def coordV (Q : ℝ) (z : ℂ) : ℂ := (Q : ℂ) ^ (-6*z)
def coordR (Q : ℝ) (A x z : ℂ) : ℂ := A * (Q : ℂ) ^ (4-6*x-6*z)
def coordW (Q : ℝ) (v w : ℂ) : ℂ := v * (Q : ℂ) ^ (-w)
def coordD (Q : ℝ) (eta v x : ℂ) : ℂ := eta * star v * (Q : ℂ) ^ (-x)
def coordK (Q : ℝ) (eta x w : ℂ) : ℂ := eta * (Q-1) * (Q : ℂ) ^ (-x-w)

def unramifiedClosed (Q : ℝ) (A eta v x w z : ℂ) : ℂ :=
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  ProbeLocal.continuedCorrection V W D (markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1)

def actualAPhase (eta : HeckeFamily.Character) (p : O) : ℂ :=
  star (FiniteGaussPhase.angularFactor p) ^ 6 * HeckeFamily.elementCoeff eta p ^ 6

def actualUnramifiedClosed (eta : HeckeFamily.Character) (p u : O)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p}) (x w z : ℂ) : ℂ :=
  unramifiedClosed (Ideal.absNorm (Ideal.span {p})) (actualAPhase eta p)
    (HeckeFamily.elementCoeff eta p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ u)) x w z

lemma actualAPhase_norm_le_one (eta : HeckeFamily.Character) (p : O) :
    ‖actualAPhase eta p‖ ≤ 1 := by
  simp only [actualAPhase, norm_mul, norm_pow, norm_star]
  exact (mul_le_of_le_one_left (by positivity)
    (pow_le_one₀ (norm_nonneg _) (CompletedGauss.angularFactor_norm_le_one p))).trans
    (pow_le_one₀ (norm_nonneg _) (ProbeRow.targetMonoid_norm_le_one eta p))

lemma coordV_norm (Q : ℝ) (hQ : 0 < Q) (z : ℂ) :
    ‖coordV Q z‖ = Q ^ (-6*z.re) := by
  rw [coordV, Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  simp

lemma coordR_norm_le (Q : ℝ) (hQ : 0 < Q) (A x z : ℂ) (hA : ‖A‖ ≤ 1) :
    ‖coordR Q A x z‖ ≤ Q ^ (4-6*x.re-6*z.re) := by
  rw [coordR, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, sub_zero]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hQ.le _) hA

lemma coordW_norm_le (Q : ℝ) (hQ : 0 < Q) (v w : ℂ) (hv : ‖v‖ ≤ 1) :
    ‖coordW Q v w‖ ≤ Q ^ (-w.re) := by
  rw [coordW, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hQ.le _) hv

lemma coordD_norm_le (Q : ℝ) (hQ : 0 < Q) (eta v x : ℂ)
    (he : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖coordD Q eta v x‖ ≤ Q ^ (-x.re) := by
  rw [coordD, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]
  apply mul_le_of_le_one_left (Real.rpow_nonneg hQ.le _)
  rw [norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) he).trans hv

lemma coordK_norm_le (Q : ℝ) (hQ : 1 ≤ Q) (eta x w : ℂ) (he : ‖eta‖ ≤ 1) :
    ‖coordK Q eta x w‖ ≤ Q ^ (1-x.re-w.re) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hsub : ‖(Q:ℂ)-1‖ = Q-1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hQ)]
  rw [coordK, norm_mul, norm_mul, hsub, Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
  have heq : (1-x.re-w.re) = 1 + (-x.re-w.re) := by ring
  rw [heq, Real.rpow_add hQ0, Real.rpow_one]
  simp only [Complex.sub_re, Complex.neg_re]
  gcongr
  calc ‖eta‖*(Q-1) ≤ 1*(Q-1) := mul_le_mul_of_nonneg_right he (sub_nonneg.mpr hQ)
       _ ≤ Q := by linarith

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1199

/-! Original module: OAI.NumberTheory.DirichletL.Detector.EulerRegion
Source SHA256: 11b6a0464af2b386a26ad8a5ad67da54f983944c2ba11310625677e8db2fc911
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1200


namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma rpow_le_half (Q a : ℝ) (hQ : 4 ≤ Q) (ha : a ≤ -(1/2)) : Q^a ≤ 1/2 := by
  have hQ0 : 0 < Q := by linarith
  have hs : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ0
  have hs2 := Real.sq_sqrt hQ0.le
  calc
    Q^a ≤ Q^(-(1/2:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) ha
    _ = (Real.sqrt Q)⁻¹ := by rw [Real.rpow_neg hQ0.le, ← Real.sqrt_eq_rpow]
    _ ≤ 1/2 := by rw [← one_div, div_le_iff₀ hs]; nlinarith [Real.sqrt_nonneg Q]

theorem unramifiedClosed_second_region_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (7/8:ℝ) ≤ x.re) (hw : (19/20:ℝ) ≤ w.re) (hz : (33/200:ℝ) ≤ z.re) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤ 240 * Q ^ (-(363/200:ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  have hV : ‖V‖ ≤ Q ^ (-(99/100:ℝ)) := by
    rw [show V = coordV Q z from rfl, coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖ ≤ Q ^ (-(56/25:ℝ)) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖ ≤ Q ^ (-(19/20:ℝ)) :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖ ≤ Q ^ (-(7/8:ℝ)) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖ ≤ Q ^ (-(33/40:ℝ)) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖ ≤ 1/2 := hV.trans (rpow_le_half Q _ hQ (by norm_num))
  have hRh : ‖R‖ ≤ 1/2 := hR.trans (rpow_le_half Q _ hQ (by norm_num))
  have hDh : ‖D‖ ≤ 1/2 := hD.trans (rpow_le_half Q _ hQ (by norm_num))
  have hWh : ‖W‖ ≤ 1 := by
    exact hW.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : -(19/20:ℝ) ≤ 0)).trans_eq (Real.rpow_zero Q))
  have hqi : ‖(Q:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0, ← one_div]
    exact (div_le_one hQ0).mpr hQ1
  let T := Q ^ (-(363/200:ℝ))
  have hT : 0 ≤ T := Real.rpow_nonneg hQ0.le _
  have hRT : ‖R‖ ≤ T := hR.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num))
  have hprod (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (haa : a ≤ Q^a') (hbb : b ≤ Q^b') (he : a'+b' ≤ -(363/200:ℝ)) : a*b ≤ T := by
    calc
      a*b ≤ Q^a' * Q^b' := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _ = Q^(a'+b') := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hQ1 he
  have hKV : ‖K‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by norm_num)
  have hDV : ‖D‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV (by norm_num)
  have hDW : ‖D‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hW (by norm_num)
  have hVW : ‖V‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW (by norm_num)
  have hDVW : ‖D‖*‖V‖*‖W‖ ≤ T :=
    (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hWh).trans hDV
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hE : ‖P+D‖ ≤ 28*T := by
    have h := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    have hrw : ‖R‖*(1+‖W‖) ≤ 2*T := by
      calc
        _ ≤ ‖R‖*2 := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ ≤ _ := by nlinarith
    dsimp only [P]
    nlinarith
  have h := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P-1‖ ≤ 240*T
  have hWE : (1+‖W‖)*‖P+D‖ ≤ 56*T := by
    calc
      _ ≤ 2*(28*T) := mul_le_mul (by linarith) hE (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  nlinarith

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1200

/-! Original module: OAI.NumberTheory.DirichletL.Detector.EulerHolomorphic
Source SHA256: 18c6e835736b404bedb9916d1419aec59ff41b25b6687e1f649efc406c527752
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1201


namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma coordR_differentiable (Q : ℝ) (hQ : 0 < Q) (A z : ℂ) :
    Differentiable ℂ (fun x : ℂ => coordR Q A x z) := by
  unfold coordR
  have hn : (Q:ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  exact (((differentiable_const (4:ℂ)).sub (differentiable_id.const_mul 6)).sub_const (6*z)).const_cpow
    (Or.inl hn) |>.const_mul A

lemma coordD_differentiable (Q : ℝ) (hQ : 0 < Q) (eta v : ℂ) :
    Differentiable ℂ (fun x : ℂ => coordD Q eta v x) := by
  unfold coordD
  have hn : (Q:ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  exact (differentiable_id.neg.const_cpow (Or.inl hn)).const_mul (eta*star v)

lemma coordK_differentiable (Q : ℝ) (hQ : 0 < Q) (eta w : ℂ) :
    Differentiable ℂ (fun x : ℂ => coordK Q eta x w) := by
  unfold coordK
  have hn : (Q:ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  exact ((differentiable_id.neg.sub_const w).const_cpow (Or.inl hn)).const_mul (eta*(Q-1))

lemma unramifiedClosed_differentiableAt (Q : ℝ) (hQ : 0 < Q) (A eta v x w z : ℂ)
    (hR : 1-coordR Q A x z ≠ 0) (_hV : 1-coordV Q z ≠ 0)
    (hD : 1-coordD Q eta v x ≠ 0) :
    DifferentiableAt ℂ (fun s : ℂ => unramifiedClosed Q A eta v s w z) x := by
  have hr := coordR_differentiable Q hQ A z
  have hd := coordD_differentiable Q hQ eta v
  have hk := coordK_differentiable Q hQ eta w
  have hp : DifferentiableAt ℂ (fun s : ℂ =>
      markedFactor (coordR Q A s z) (coordV Q z) (Q:ℂ)⁻¹
        (coordK Q eta s w) (-coordD Q eta v s + coordW Q v w*coordR Q A s z) 1) x := by
    unfold markedFactor
    fun_prop (disch := assumption)
  unfold unramifiedClosed ProbeLocal.continuedCorrection
  dsimp only
  fun_prop (disch := assumption)

theorem principalClosed_analytic (Q : ℝ) (hQ : 4 ≤ Q) (A eta : ℂ)
    (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) :
    AnalyticOnNhd ℂ (fun s : ℂ => unramifiedClosed Q A eta 1 s 1 (1/6))
      {s : ℂ | 7/8 < s.re} := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hv : 1-coordV Q (1/6) ≠ 0 := by
    apply ProbeLocal.one_sub_ne_zero_of_norm_le_half
    rw [coordV_norm Q hQ0]
    apply rpow_le_half Q _ hQ
    norm_num
  have hdif : DifferentiableOn ℂ (fun s : ℂ => unramifiedClosed Q A eta 1 s 1 (1/6))
      {s : ℂ | 7/8 < s.re} := by
    intro s hs
    apply (unramifiedClosed_differentiableAt Q hQ0 A eta 1 s 1 (1/6) ?_ hv ?_).differentiableWithinAt
    · apply ProbeLocal.one_sub_ne_zero_of_norm_le_half
      apply (coordR_norm_le Q hQ0 A s (1/6) hA).trans
      apply rpow_le_half Q _ hQ
      norm_num
      change (7/8:ℝ) < s.re at hs
      linarith
    · apply ProbeLocal.one_sub_ne_zero_of_norm_le_half
      apply (coordD_norm_le Q hQ0 eta 1 s heta (by simp)).trans
      apply rpow_le_half Q _ hQ
      change (7/8:ℝ) < s.re at hs
      linarith
  exact hdif.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1201

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GlobalRegion
Source SHA256: ad70278668b25b0aa988c583dca9632affebda26aa009a159dd5f92a20a6d2ee
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1202


namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

theorem unramifiedClosed_open_region_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (7/8:ℝ) ≤ x.re) (hw : (9/10:ℝ) ≤ w.re) (hz : (4/25:ℝ) ≤ z.re) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤ 240 * Q ^ (-(17/10:ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  have hV : ‖V‖ ≤ Q ^ (-(24/25:ℝ)) := by
    rw [show V = coordV Q z from rfl, coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖ ≤ Q ^ (-(221/100:ℝ)) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖ ≤ Q ^ (-(9/10:ℝ)) :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖ ≤ Q ^ (-(7/8:ℝ)) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖ ≤ Q ^ (-(31/40:ℝ)) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖ ≤ 1/2 := hV.trans (rpow_le_half Q _ hQ (by norm_num))
  have hRh : ‖R‖ ≤ 1/2 := hR.trans (rpow_le_half Q _ hQ (by norm_num))
  have hDh : ‖D‖ ≤ 1/2 := hD.trans (rpow_le_half Q _ hQ (by norm_num))
  have hWh : ‖W‖ ≤ 1 := by
    exact hW.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : -(9/10:ℝ) ≤ 0)).trans_eq (Real.rpow_zero Q))
  have hqi : ‖(Q:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0, ← one_div]
    exact (div_le_one hQ0).mpr hQ1
  let T := Q ^ (-(17/10:ℝ))
  have hT : 0 ≤ T := Real.rpow_nonneg hQ0.le _
  have hRT : ‖R‖ ≤ T := hR.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num))
  have hprod (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (haa : a ≤ Q^a') (hbb : b ≤ Q^b') (he : a'+b' ≤ -(17/10:ℝ)) : a*b ≤ T := by
    calc
      a*b ≤ Q^a' * Q^b' := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _ = Q^(a'+b') := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hQ1 he
  have hKV : ‖K‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by norm_num)
  have hDV : ‖D‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV (by norm_num)
  have hDW : ‖D‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hW (by norm_num)
  have hVW : ‖V‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW (by norm_num)
  have hDVW : ‖D‖*‖V‖*‖W‖ ≤ T :=
    (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hWh).trans hDV
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hE : ‖P+D‖ ≤ 28*T := by
    have h := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    have hrw : ‖R‖*(1+‖W‖) ≤ 2*T := by
      calc
        _ ≤ ‖R‖*2 := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ ≤ _ := by nlinarith
    dsimp only [P]
    nlinarith
  have h := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P-1‖ ≤ 240*T
  have hWE : (1+‖W‖)*‖P+D‖ ≤ 56*T := by
    calc
      _ ≤ 2*(28*T) := mul_le_mul (by linarith) hE (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  nlinarith

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1202

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GlobalHolomorphic
Source SHA256: b80c82079e56bf6188afc6b957d4e24c1346a2b50f90f835edb7439de0586591
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1203



namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma coordV_differentiable (Q : ℝ) (hQ : 0<Q) : Differentiable ℂ (coordV Q) := by
  unfold coordV
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  exact (differentiable_id.const_mul (-6)).const_cpow (Or.inl hn)

lemma coordW_differentiable (Q : ℝ) (hQ : 0<Q) (v : ℂ) : Differentiable ℂ (coordW Q v) := by
  unfold coordW
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  exact (differentiable_id.neg.const_cpow (Or.inl hn)).const_mul v

lemma coordR_z_differentiable (Q : ℝ) (hQ : 0<Q) (A x : ℂ) :
    Differentiable ℂ (fun z=>coordR Q A x z) := by
  unfold coordR
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  exact (((differentiable_id.const_mul 6).const_sub (4-6*x)).const_cpow (Or.inl hn)).const_mul A

lemma coordK_w_differentiable (Q : ℝ) (hQ : 0<Q) (eta x : ℂ) :
    Differentiable ℂ (fun w=>coordK Q eta x w) := by
  unfold coordK
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  exact ((differentiable_id.const_sub (-x)).const_cpow (Or.inl hn)).const_mul (eta*(Q-1))

lemma unramifiedClosed_differentiableAt_w (Q : ℝ) (hQ : 0<Q) (A eta v x w z : ℂ)
    (_hR : 1-coordR Q A x z≠0) (_hV : 1-coordV Q z≠0) (_hD : 1-coordD Q eta v x≠0) :
    DifferentiableAt ℂ (fun t=>unramifiedClosed Q A eta v x t z) w := by
  have hw := coordW_differentiable Q hQ v
  have hk := coordK_w_differentiable Q hQ eta x
  have hp : DifferentiableAt ℂ (fun t=>
      markedFactor (coordR Q A x z) (coordV Q z) (Q:ℂ)⁻¹
        (coordK Q eta x t) (-coordD Q eta v x+coordW Q v t*coordR Q A x z) 1) w := by
    unfold markedFactor
    fun_prop (disch := assumption)
  unfold unramifiedClosed ProbeLocal.continuedCorrection
  dsimp only
  fun_prop (disch := assumption)

lemma unramifiedClosed_differentiableAt_z (Q : ℝ) (hQ : 0<Q) (A eta v x w z : ℂ)
    (hR : 1-coordR Q A x z≠0) (hV : 1-coordV Q z≠0) (_hD : 1-coordD Q eta v x≠0) :
    DifferentiableAt ℂ (fun t=>unramifiedClosed Q A eta v x w t) z := by
  have hv := coordV_differentiable Q hQ
  have hr := coordR_z_differentiable Q hQ A x
  have hp : DifferentiableAt ℂ (fun t=>
      markedFactor (coordR Q A x t) (coordV Q t) (Q:ℂ)⁻¹
        (coordK Q eta x w) (-coordD Q eta v x+coordW Q v w*coordR Q A x t) 1) z := by
    unfold markedFactor
    fun_prop (disch := assumption)
  unfold unramifiedClosed ProbeLocal.continuedCorrection
  dsimp only
  fun_prop (disch := assumption)

lemma open_region_denominators (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : 7/8≤x.re) (hz : 4/25≤z.re) :
    1-coordR Q A x z≠0 ∧ 1-coordV Q z≠0 ∧ 1-coordD Q eta v x≠0 := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  have hR : ‖coordR Q A x z‖≤1/2 := by
    apply (coordR_norm_le Q hQ0 A x z hA).trans
    apply rpow_le_half Q _ hQ
    linarith
  have hV : ‖coordV Q z‖≤1/2 := by
    rw [coordV_norm Q hQ0]
    apply rpow_le_half Q _ hQ
    linarith
  have hD : ‖coordD Q eta v x‖≤1/2 := by
    apply (coordD_norm_le Q hQ0 eta v x he hv).trans
    apply rpow_le_half Q _ hQ
    linarith
  exact ⟨ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hR,
    ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV,ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hD⟩

theorem unramifiedClosed_analytic_x (Q : ℝ) (A eta v w z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hz : 4/25≤z.re) :
    AnalyticOnNhd ℂ (fun x=>unramifiedClosed Q A eta v x w z) {x : ℂ|7/8<x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := open_region_denominators Q A eta v x z hQ hA he hv hx.le hz
  exact (unramifiedClosed_differentiableAt Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem unramifiedClosed_analytic_w (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : 7/8≤x.re) (hz : 4/25≤z.re) :
    AnalyticOnNhd ℂ (fun w=>unramifiedClosed Q A eta v x w z) {w : ℂ|9/10<w.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w hw
  have hd := open_region_denominators Q A eta v x z hQ hA he hv hx hz
  exact (unramifiedClosed_differentiableAt_w Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem unramifiedClosed_analytic_z (Q : ℝ) (A eta v x w : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hx : 7/8≤x.re) :
    AnalyticOnNhd ℂ (fun z=>unramifiedClosed Q A eta v x w z) {z : ℂ|4/25<z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := open_region_denominators Q A eta v x z hQ hA he hv hx hz.le
  exact (unramifiedClosed_differentiableAt_z Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1203

/-! Original module: OAI.NumberTheory.DirichletL.Detector.Physical
Source SHA256: 324e33aaa6f25f99f984f75231e292d08d37ee971826d927b539861c326d5544
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1204




namespace OAI

noncomputable section

open scoped BigOperators Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open CubicEisenstein ProbeCompleted ProbeRow

local notation "O" => ActualEisensteinCubic.O

structure CalibrationData where
  excluded : Finset (Ideal O)
  generator : O
  generator_ne_zero : generator ≠ 0
  residue : MulChar (O ⧸ Ideal.span {generator}) ℂ

def elementNorm (a : O) : ℝ := Ideal.absNorm (Ideal.span {a})

def CalibrationData.residueMonoid (C : CalibrationData) : O →* ℂ :=
  C.residue.toMonoidHom.comp (Ideal.Quotient.mk (Ideal.span {C.generator})).toMonoidHom

def CalibrationData.Xi (C : CalibrationData) : O →* ℂ :=
  C.residueMonoid * (idealRowHom C.generator).toMonoidHom.comp principalIdealHom.toMonoidHom

def CalibrationData.tau (C : CalibrationData) : ℂ :=
  (∑' d : O ⧸ Ideal.span {C.generator}, C.residue d *
    quotientTrace C.generator C.generator_ne_zero d) /
      (Real.sqrt (elementNorm C.generator) : ℂ)

def sexticGauss (s : O) (hs : s ≠ 0) (h : O) : ℂ :=
  ∑' d : O ⧸ Ideal.span {s},
    idealRowHom (GaussianShiftedPartition.representative s d) (Ideal.span {s}) *
      quotientTrace s hs (Ideal.Quotient.mk _ h * d)

theorem sexticGauss_coefficient_mk (s : O) (a : O) :
    idealRowHom (GaussianShiftedPartition.representative s
      (Ideal.Quotient.mk (Ideal.span {s}) a)) (Ideal.span {s}) =
      idealRowHom a (Ideal.span {s}) := by
  apply idealRowHom_congr_mod
  apply Ideal.Quotient.eq.mp
  exact GaussianShiftedPartition.representative_spec _ _

def verticalIntegral (σ : ℝ) (F : ℂ → ℂ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, F ((σ : ℂ) + y * Complex.I)

def markedPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W₀ W₁ : ℝ → ℂ) (X Y Z : ℝ) : ℂ :=
  (Y : ℂ)⁻¹ * ∑' s : {I : Ideal O // Supported I},
    if ∀ p ∈ C.excluded, ¬p ∣ s.val then
      let a := primaryGenerator s.val
      let ha := supported_primaryGenerator_ne_zero s.val s.property
      let has := (supported_span_primaryGenerator_iff s.val).mpr s.property
      let q_s : ℝ := Ideal.absNorm s.val
      W₁ (q_s / Y) * idealRowHom C.generator s.val /
        (C.tau * C.residueMonoid a * (Real.sqrt (elementNorm C.generator * q_s * X) : ℂ)) *
      ∑' m : O,
        C.residueMonoid m * (Real.sqrt q_s : ℂ)⁻¹ * sexticGauss a ha (-m) *
          W₀ (elementNorm m / (elementNorm C.generator * q_s * X)) *
          verticalIntegral 4 (fun t => (Z : ℂ) ^ t * Complex.exp (t ^ 2) *
            spectralRow C.excluded D (rowCoefficient η C.Xi a has m) t)
    else 0

def physicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (X Y Z : ℝ) : ℂ :=
  markedPhysicalProbe η C 1 W₀ W₁ X Y Z

def slotProduct {K : ℕ} (p : Fin K → O) (J : Finset (Fin K)) : O := ∏ i ∈ J, p i

def compensatedTuple {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (p : Fin K → O) (X Y Z : ℝ) : ℂ :=
  ProbeCompensation.tupleOperation p elementNorm (HeckeFamily.elementCoeff η)
    (fun a => markedPhysicalProbe η C (Ideal.span {a}) W₀ W₁) X Y Z

@[simp] theorem elementNorm_one : elementNorm (1 : O) = 1 := by
  simp [elementNorm]

attribute [local irreducible] markedPhysicalProbe

theorem compensatedTuple_zero (η : HeckeFamily.Character) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (p : Fin 0 → O) (X Y Z : ℝ) :
    compensatedTuple η C W₀ W₁ p X Y Z = physicalProbe η C W₀ W₁ X Y Z := by
  unfold compensatedTuple
  rw [ProbeCompensation.tupleOperation_zero p elementNorm (HeckeFamily.elementCoeff η)
    elementNorm_one (HeckeFamily.elementCoeff_one η)]
  change markedPhysicalProbe η C (Ideal.span {(1 : O)}) W₀ W₁ X Y Z =
    markedPhysicalProbe η C 1 W₀ W₁ X Y Z
  rw [Ideal.span_singleton_one, Ideal.one_eq_top]

theorem compensatedTuple_one (η : HeckeFamily.Character) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (p : Fin 1 → O) (X Y Z : ℝ) :
    compensatedTuple η C W₀ W₁ p X Y Z =
      star (HeckeFamily.elementCoeff η (p 0)) *
        markedPhysicalProbe η C (Ideal.span {p 0}) W₀ W₁ X Y (Z * elementNorm (p 0)) -
      (elementNorm (p 0) ^ (-(3 / 2 : ℝ)) : ℝ) *
        physicalProbe η C W₀ W₁ (X / elementNorm (p 0)) (Y / elementNorm (p 0)) Z := by
  unfold compensatedTuple
  rw [ProbeCompensation.tupleOperation_one p elementNorm (HeckeFamily.elementCoeff η)
    elementNorm_one (HeckeFamily.elementCoeff_one η)]
  change _ = _ - _ * markedPhysicalProbe η C 1 W₀ W₁ _ _ Z
  rw [Ideal.span_singleton_one, Ideal.one_eq_top]

def compensatedPhysicalProbe {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (slotPrimes : Fin K → Finset O)
    (slotWindow : Fin K → ℝ → ℂ) (slotScale : Fin K → ℝ) (X Y Z : ℝ) : ℂ :=
  ∑ p : ((i : Fin K) → {a : O // a ∈ slotPrimes i}),
    (∏ i : Fin K, slotWindow i (elementNorm (p i).val / slotScale i)) *
      compensatedTuple η C W₀ W₁ (fun i => (p i).val) X Y Z

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1204

/-! Original module: OAI.NumberTheory.DirichletL.Detector.Calibration
Source SHA256: d8721f13440e278aab51b6625c948b89095b74ef89615eeb78fcb52cff1726c9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1205



namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def crtCharacter {ι T : Type*} [Fintype ι] [CommRing T]
    (R : ι → Type*) [∀ i, Field (R i)] (e : T ≃+* ∀ i, R i)
    (χ : ∀ i, MulChar (R i) ℂ) : MulChar T ℂ where
  toFun x := ∏ i, χ i (e x i)
  map_one' := by simp
  map_mul' x y := by simp [Finset.prod_mul_distrib]
  map_nonunit' x hx := by
    have he : ¬∀ i, IsUnit (e x i) := by
      intro h
      apply hx
      have hu := (Pi.isUnit_iff.mpr h).map e.symm.toMonoidHom
      simpa using hu
    obtain ⟨i, hi⟩ := not_forall.mp he
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact (χ i).map_nonunit hi

theorem crtCharacter_pow_six {ι T : Type*} [Fintype ι] [CommRing T]
    (R : ι → Type*) [∀ i, Field (R i)] (e : T ≃+* ∀ i, R i)
    (χ : ∀ i, MulChar (R i) ℂ) (hχ : ∀ i, χ i ^ 6 = 1) :
    crtCharacter R e χ ^ 6 = 1 := by
  apply MulChar.ext
  intro x
  rw [MulChar.pow_apply' _ (by decide : (6 : ℕ) ≠ 0), MulChar.one_apply x.isUnit]
  change (∏ i, χ i (e x i)) ^ 6 = 1
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i _
  have hu : IsUnit (e x i) := (Pi.isUnit_iff.mp (x.isUnit.map e.toMonoidHom)) i
  have he := congrArg (fun f : MulChar (R i) ℂ => f (e x i)) (hχ i)
  simpa only [MulChar.pow_apply' _ (by decide : (6 : ℕ) ≠ 0), MulChar.one_apply hu] using he

theorem residue_char_ne_two_of_lambda_mem (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∈ P) : ringChar (O ⧸ P) ≠ 2 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field _
  intro hc
  have hd : goodLambda ∣ (3 : O) :=
    (dvd_pow_self goodLambda (by decide : (2 : ℕ) ≠ 0)).trans lambda_sq_dvd_three
  obtain ⟨k, hk⟩ := hd
  have h3m : (3 : O) ∈ P := by rw [hk]; exact P.mul_mem_right k hg
  have h3 : (3 : O ⧸ P) = 0 := by
    simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr h3m
  have h2 : (2 : O ⧸ P) = 0 := by
    exact (ringChar.spec (O ⧸ P) 2).mpr (by rw [hc])
  have h1 : (1 : O ⧸ P) = 0 := by linear_combination h3 - h2
  exact one_ne_zero h1

theorem exists_local_calibration (P : Ideal O) [P.IsMaximal] :
    ∃ χ : MulChar (O ⧸ P) ℂ, χ ≠ 1 ∧ χ ^ 6 = 1 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field _
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  by_cases hg : goodLambda ∉ P
  · refine ⟨actualSextic P hg ^ 2, ?_, ?_⟩
    · intro h
      exact ((MulChar.ringHomComp_ne_one_iff eisEmbedding_injective).mpr
        (cubicChar_ne_one P hg)) ((canonicalSextic_pow_two P hg).symm.trans h)
    · calc
        (actualSextic P hg ^ 2) ^ 6 = actualSextic P hg ^ (2 * 6) := (pow_mul _ 2 6).symm
        _ = actualSextic P hg ^ (6 * 2) := rfl
        _ = (actualSextic P hg ^ 6) ^ 2 := pow_mul _ 6 2
        _ = (1 : MulChar (O ⧸ P) ℂ) ^ 2 :=
          congrArg (fun χ : MulChar (O ⧸ P) ℂ => χ ^ 2)
            (CanonicalRowCompletion.actualSextic_sixth_one P hg)
        _ = 1 := one_pow 2
  · have hchar := residue_char_ne_two_of_lambda_mem P (not_not.mp hg)
    let χ : MulChar (O ⧸ P) ℂ := (quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom ℂ)
    refine ⟨χ, ?_, ?_⟩
    · exact (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr (quadraticChar_ne_one hchar)
    · have h2 : χ ^ 2 = 1 := by
        dsimp only [χ]
        rw [MulChar.ringHomComp_pow, (quadraticChar_isQuadratic (O ⧸ P)).sq_eq_one,
          MulChar.ringHomComp_one]
      rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul, h2, one_pow]

def localCalibration (P : Ideal O) [P.IsMaximal] : MulChar (O ⧸ P) ℂ :=
  Classical.choose (exists_local_calibration P)

theorem localCalibration_nonprincipal (P : Ideal O) [P.IsMaximal] :
    localCalibration P ≠ 1 := (Classical.choose_spec (exists_local_calibration P)).1

theorem localCalibration_pow_six (P : Ideal O) [P.IsMaximal] :
    localCalibration P ^ 6 = 1 := (Classical.choose_spec (exists_local_calibration P)).2

def calibrationFromPrimes {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) : CalibrationData := by
  letI (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  exact {
    excluded := Finset.univ.image P
    generator := finitePrimeModulus P
    generator_ne_zero := finitePrimeModulus_ne_zero P
    residue := crtCharacter (fun i => O ⧸ P i)
      ((Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
        (IdealGaussCRT.quotientProdEquivPi P hcop)) (fun i => localCalibration (P i)) }

theorem calibrationFromPrimes_pow_six {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    (calibrationFromPrimes P hcop).residue ^ 6 = 1 := by
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  exact crtCharacter_pow_six _ _ _ (fun i => localCalibration_pow_six (P i))

theorem calibrationFromPrimes_tau_norm {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    ‖(calibrationFromPrimes P hcop).tau‖ = 1 := by
  let b := finitePrimeModulus P
  have hb : b ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {b}) := ConcreteTraceCRT.finite_quotient_span hb
  let : Fintype (O ⧸ Ideal.span {b}) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let e : (O ⧸ Ideal.span {b}) ≃+* ∀ i, O ⧸ P i :=
    (Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
      (IdealGaussCRT.quotientProdEquivPi P hcop)
  let ψ := quotientTrace b hb
  have hψ : ψ.IsPrimitive := GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive b hb
  have hg := IdealGaussCRT.norm_gauss_finite_crt_sq (fun i => O ⧸ P i) e
    (fun i => localCalibration (P i)) ψ (fun i => localCalibration_nonprincipal (P i))
    (fun i => IdealGaussCRT.coordinateAddChar_isPrimitive _ e ψ hψ i)
  have hcard : (Fintype.card (O ⧸ Ideal.span {b}) : ℝ) = elementNorm b := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [hcard] at hg
  have hQ : 0 < elementNorm b := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hb))
  have hn : ‖∑ x : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e x i)) * ψ x‖ =
      Real.sqrt (elementNorm b) := by
    have hs := Real.sq_sqrt hQ.le
    have hs0 := Real.sqrt_nonneg (elementNorm b)
    have hn0 := norm_nonneg (∑ x : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e x i)) * ψ x)
    nlinarith
  change ‖(∑' d : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e d i)) * ψ d) /
    (Real.sqrt (elementNorm b) : ℂ)‖ = 1
  rw [tsum_fintype, norm_div, hn, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_self (Real.sqrt_pos.mpr hQ).ne']

theorem calibrationFromPrimes_tau_ne_zero {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    (calibrationFromPrimes P hcop).tau ≠ 0 := by
  exact norm_ne_zero_iff.mp (by rw [calibrationFromPrimes_tau_norm]; norm_num)

def calibrationForSet (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) : CalibrationData := by
  letI (P : S) : P.val.IsMaximal := hS P.val P.property
  exact calibrationFromPrimes (fun P : S => P.val)
    (fun P Q hPQ => Ideal.isCoprime_of_isMaximal (fun h => hPQ (Subtype.ext h)))

theorem calibrationForSet_excluded (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    (calibrationForSet S hS).excluded = S := by
  change Finset.univ.image (fun P : S => P.val) = S
  ext P
  simp

theorem calibrationForSet_span (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    Ideal.span {(calibrationForSet S hS).generator} = ∏ P ∈ S, P := by
  change Ideal.span {finitePrimeModulus (fun P : S => P.val)} = _
  rw [span_finitePrimeModulus]
  exact Finset.prod_coe_sort S (fun P : Ideal O => P)

theorem calibrationForSet_pow_six (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    (calibrationForSet S hS).residue ^ 6 = 1 := by
  let (P : S) : P.val.IsMaximal := hS P.val P.property
  unfold calibrationForSet
  apply calibrationFromPrimes_pow_six

theorem calibrationForSet_tau_norm (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    ‖(calibrationForSet S hS).tau‖ = 1 := by
  let (P : S) : P.val.IsMaximal := hS P.val P.property
  unfold calibrationForSet
  apply calibrationFromPrimes_tau_norm

theorem calibrationForSet_tau_ne_zero (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    (calibrationForSet S hS).tau ≠ 0 := by
  exact norm_ne_zero_iff.mp (by rw [calibrationForSet_tau_norm]; norm_num)

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1205

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CalibrationFourier
Source SHA256: 38d5b05a2473ea3fdb4de76fa3ee8ee3db2d2463657e409f4dbe5af726ba9f1a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1206


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def calibrationGauss (C : CalibrationData) (h : O) : ℂ :=
  ∑' d : O ⧸ Ideal.span {C.generator}, C.residue d *
    quotientTrace C.generator C.generator_ne_zero
      (Ideal.Quotient.mk (Ideal.span {C.generator}) h * d)

theorem calibrationGauss_one (C : CalibrationData) :
    calibrationGauss C 1 = (Real.sqrt (elementNorm C.generator) : ℂ) * C.tau := by
  have hn : 0 < elementNorm C.generator := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))
  have hc : (Real.sqrt (elementNorm C.generator) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hn).ne'
  simp only [calibrationGauss, map_one, one_mul, CalibrationData.tau]
  field_simp

theorem calibrationFromPrimes_gauss {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) (h : O) :
    calibrationGauss (calibrationFromPrimes P hcop) h =
      ((calibrationFromPrimes P hcop).residueMonoid h)⁻¹ *
        calibrationGauss (calibrationFromPrimes P hcop) 1 := by
  let b := finitePrimeModulus P
  have hb : b ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {b}) := ConcreteTraceCRT.finite_quotient_span hb
  let : Fintype (O ⧸ Ideal.span {b}) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let e : (O ⧸ Ideal.span {b}) ≃+* ∀ i, O ⧸ P i :=
    (Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
      (IdealGaussCRT.quotientProdEquivPi P hcop)
  let ψ := quotientTrace b hb
  have ht := IdealGaussCRT.gauss_transform_finite_crt_scalar (fun i => O ⧸ P i) e
    (fun i => localCalibration (P i)) ψ (fun i => localCalibration_nonprincipal (P i))
    (Ideal.Quotient.mk (Ideal.span {b}) h)
  change (∑' d : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e d i)) *
      ψ (Ideal.Quotient.mk (Ideal.span {b}) h * d)) =
    (∏ i, localCalibration (P i) (e (Ideal.Quotient.mk (Ideal.span {b}) h) i))⁻¹ *
      ∑' d : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e d i)) *
        ψ (Ideal.Quotient.mk (Ideal.span {b}) 1 * d)
  simpa only [tsum_fintype, map_one, one_mul] using ht

theorem calibrationForSet_gauss (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (h : O) :
    calibrationGauss (calibrationForSet S hS) h =
      star ((calibrationForSet S hS).residueMonoid h) *
        (Real.sqrt (elementNorm (calibrationForSet S hS).generator) : ℂ) *
        (calibrationForSet S hS).tau := by
  let C := calibrationForSet S hS
  let : Finite (O ⧸ Ideal.span {C.generator}) :=
    ConcreteTraceCRT.finite_quotient_span C.generator_ne_zero
  have hc : star (C.residueMonoid h) = (C.residueMonoid h)⁻¹ := by
    exact (MulChar.star_apply' C.residue (Ideal.Quotient.mk _ h)).trans
      (MulChar.inv_apply_eq_inv' _ _)
  have he : calibrationGauss C h = (C.residueMonoid h)⁻¹ * calibrationGauss C 1 := by
    let (P : S) : P.val.IsMaximal := hS P.val P.property
    unfold C calibrationForSet
    apply calibrationFromPrimes_gauss
  rw [he, calibrationGauss_one, ← hc]
  ring

theorem calibrationForSet_residue_sixth (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (a : O) (ha : IsCoprime (calibrationForSet S hS).generator a) :
    (calibrationForSet S hS).residueMonoid a ^ 6 = 1 := by
  let C := calibrationForSet S hS
  have hu := (isUnit_quotient_span_iff C.generator a).mpr ha
  have h6 := congrArg (fun χ : MulChar (O ⧸ Ideal.span {C.generator}) ℂ =>
    χ (Ideal.Quotient.mk _ a)) (calibrationForSet_pow_six S hS)
  change C.residue (Ideal.Quotient.mk _ a) ^ 6 = 1
  simpa only [MulChar.pow_apply' _ (by decide : (6 : ℕ) ≠ 0), MulChar.one_apply hu] using h6

theorem calibrationForSet_quotient_conjugate (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, P.IsMaximal) (s k u a : O)
    (hs : IsCoprime (calibrationForSet S hS).generator s)
    (ha : IsCoprime (calibrationForSet S hS).generator a)
    (hrel : s * k = u * a ^ 6) :
    star ((calibrationForSet S hS).residueMonoid k) =
      star ((calibrationForSet S hS).residueMonoid u) *
        (calibrationForSet S hS).residueMonoid s := by
  let C := calibrationForSet S hS
  let : Finite (O ⧸ Ideal.span {C.generator}) :=
    ConcreteTraceCRT.finite_quotient_span C.generator_ne_zero
  have hc (x : O) : star (C.residueMonoid x) = (C.residueMonoid x)⁻¹ := by
    exact (MulChar.star_apply' C.residue (Ideal.Quotient.mk _ x)).trans
      (MulChar.inv_apply_eq_inv' _ _)
  have hu := (isUnit_quotient_span_iff C.generator s).mpr hs
  have hsn : C.residueMonoid s ≠ 0 := C.residue.apply_ne_zero_iff.mpr hu
  have he := congrArg C.residueMonoid hrel
  simp only [map_mul, map_pow] at he
  have h6 : C.residueMonoid a ^ 6 = 1 := calibrationForSet_residue_sixth S hS a ha
  rw [h6, mul_one] at he
  have hk : C.residueMonoid k = (C.residueMonoid s)⁻¹ * C.residueMonoid u := by
    rw [← he, ← mul_assoc, inv_mul_cancel₀ hsn, one_mul]
  change star (C.residueMonoid k) = star (C.residueMonoid u) * C.residueMonoid s
  rw [hc k, hc u, hk, mul_inv_rev, inv_inv]

theorem calibrationForSet_gauss_sixth_row (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, P.IsMaximal) (s k u a : O)
    (hs : IsCoprime (calibrationForSet S hS).generator s)
    (ha : IsCoprime (calibrationForSet S hS).generator a)
    (hrel : s * k = u * a ^ 6) :
    calibrationGauss (calibrationForSet S hS) k =
      star ((calibrationForSet S hS).residueMonoid u) *
        (calibrationForSet S hS).residueMonoid s *
        (Real.sqrt (elementNorm (calibrationForSet S hS).generator) : ℂ) *
        (calibrationForSet S hS).tau := by
  rw [calibrationForSet_gauss,
    calibrationForSet_quotient_conjugate S hS s k u a hs ha hrel]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1206

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowRow
Source SHA256: 1fb24adb6a1570727206a17be60f3f0390006e4b386e07ac8c4e8e116fee63e8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1207



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def physicalRowBase (η : HeckeFamily.Character) (Xi : O→*ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) : O→*ℂ :=
  targetMonoid η*conjugateMonoid Xi*reciprocityPhaseMonoid s hs

lemma physicalRowBase_norm (η : HeckeFamily.Character) (Xi : O→*ℂ)
    (hXi : ∀a,‖Xi a‖≤1) (s : O) (hs : Supported (Ideal.span {s})) (a : O) :
    ‖physicalRowBase η Xi s hs a‖≤1 := by
  change ‖(targetMonoid η a*star (Xi a))*sexticReciprocityPhase s a‖≤1
  rw [norm_mul,norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) ((mul_le_of_le_one_left (norm_nonneg _) (targetMonoid_norm_le_one η a)).trans (hXi a))).trans (sexticReciprocityPhase_norm s a)

lemma ray_rowCoefficient_eq_rowTwist (η : HeckeFamily.Character) (Xi : O→*ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m f z n : O) (hn : n=m^6*f^4*z)
    (χ : RayCharacter) :
    rayMonoid χ*rowCoefficient η Xi s hs n=
      rowTwist (rayMonoid χ*physicalRowBase η Xi s hs) m f z := by
  subst n
  ext a
  change rayMonoid χ a*((targetMonoid η a*star (Xi a))*sexticReciprocityPhase s a*
      idealRowHom (m^6*f^4*z) (Ideal.span {a}))=
    (rayMonoid χ a*((targetMonoid η a*star (Xi a))*sexticReciprocityPhase s a))*
      idealRowHom (m^6*f^4*z) (Ideal.span {a})
  ring

def wholeIdealMask (S : Finset Id) (D A : Id) : ℂ :=
  if D∣A ∧ ∀P∈S,¬P∣A then 1 else 0

lemma markedCompletedT_eq_inverse (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0<X) :
    ProbeCompleted.markedCompletedT S D Ψ W X=
      InverseMoment.markedCompletedT Ψ W X (wholeIdealMask S D) := by
  rw [InverseMoment.markedCompletedT_eq_tsum Ψ W hW X hX]
  unfold ProbeCompleted.markedCompletedT
  apply tsum_congr
  intro p
  change completedMask S D p.1 p.2*summand Ψ W X p.1 p.2=
    summand Ψ W X p.1 p.2*wholeIdealMask S D (p.1*p.2^3)
  exact mul_comm _ _

theorem correctedPhysicalRow_eq_inverse_rows (η : HeckeFamily.Character) (Xi : O→*ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m f z n : O) (hn : n=m^6*f^4*z)
    (S : Finset Id) (D : Id) (W : ℝ→ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0<X) :
    correctedCompletedT S D (rowCoefficient η Xi s hs n) W X=
      ∑χ : RayCharacter,correctionCoeff χ*
        InverseMoment.markedCompletedT (rowTwist (rayMonoid χ*physicalRowBase η Xi s hs) m f z)
          W X (wholeIdealMask S D) := by
  rw [correctedCompletedT_ray_expansion S D _ W hW X hX]
  apply Finset.sum_congr rfl
  intro χ _
  rw [markedCompletedT_eq_inverse S D _ W hW X hX,ray_rowCoefficient_eq_rowTwist η Xi s hs m f z n hn χ]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1207

/-! Original module: OAI.NumberTheory.DirichletL.Detector.MellinScaling
Source SHA256: 7304cb26073a299f790e6469fcb6d8ca6c8539475b5e1956f07bbc6e48537fb4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1208



namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open EisensteinSchwartzPoisson

def sourceMellinWeight (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(x+z-1)*(Y:ℂ)^(w-1)*
    Complex.exp ((x+z-1)^2)*mellin (paperRadialFourier W0) z*mellin W1 w

lemma sourceMellinWeight_marked (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z Q : ℝ)
    (hZ : 0<Z) (hQ : 0<Q) (x w z : ℂ) :
    sourceMellinWeight W0 W1 X Y (Z*Q) x w z=
      (Q:ℂ)^(x+z-1)*sourceMellinWeight W0 W1 X Y Z x w z := by
  unfold sourceMellinWeight
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hZ.le hQ.le]
  ring

lemma sourceMellinWeight_rescaled (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z Q : ℝ)
    (hX : 0<X) (hY : 0<Y) (hQ : 0<Q) (x w z : ℂ) :
    ((Q^(-(3/2:ℝ)):ℝ):ℂ)*sourceMellinWeight W0 W1 (X/Q) (Y/Q) Z x w z=
      (Q:ℂ)^(z-w-1)*sourceMellinWeight W0 W1 X Y Z x w z := by
  have hQc : (Q:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  unfold sourceMellinWeight
  rw [Complex.ofReal_div,Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg hX.le hQ.le,Complex.div_cpow_ofReal_nonneg hY.le hQ.le,
    Complex.ofReal_cpow hQ.le]
  simp only [div_eq_mul_inv,←Complex.cpow_neg]
  have he : (Q:ℂ)^((-(3/2:ℝ):ℝ):ℂ)*(Q:ℂ)^(-(1/2-z))*(Q:ℂ)^(-(w-1))=(Q:ℂ)^(z-w-1) := by
    rw [←Complex.cpow_add _ _ hQc,←Complex.cpow_add _ _ hQc]
    congr 1
    push_cast
    ring
  calc
    _ = ((Q:ℂ)^((-(3/2:ℝ):ℝ):ℂ)*(Q:ℂ)^(-(1/2-z))*(Q:ℂ)^(-(w-1))) *
        ((X:ℂ)^(1/2-z)*(Z:ℂ)^(x+z-1)*(Y:ℂ)^(w-1)*
        Complex.exp ((x+z-1)^2)*mellin (paperRadialFourier W0) z*mellin W1 w) := by ring_nf
    _ = _ := by rw [he]; simp only [div_eq_mul_inv]

lemma sourceMellinWeight_marked_factor (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z Q : ℝ)
    (hZ : 0<Z) (hQ : 0<Q) (eta x w z : ℂ) :
    star eta*sourceMellinWeight W0 W1 X Y (Z*Q) x w z=
      (Q:ℂ)^(z-1)*(star eta*(Q:ℂ)^x)*sourceMellinWeight W0 W1 X Y Z x w z := by
  rw [sourceMellinWeight_marked W0 W1 X Y Z Q hZ hQ x w z]
  rw [show x+z-1=(z-1)+x by ring,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hQ.ne')]
  ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1208

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PhysicalFourier
Source SHA256: 926b9974a073f7ff4b3d979415254858e76c57bf6c8bd806799cbda8f974ec91
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1209



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein GaussianShiftedPartition ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

def rawFourier (a : O) (ha : a≠0) (F : (O ⧸ Ideal.span {a}) → ℂ) (H : O) : ℂ :=
  ∑' m : O ⧸ Ideal.span {a}, F m * quotientTrace a ha (Ideal.Quotient.mk _ H * m)

theorem rawFourier_exactQuotient (a s : O) (ha : a≠0) (hs : s≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (H : O) :
    conductorFourier a s ha hs F H =
      (Ideal.absNorm (Ideal.span {s}):ℂ) *
        (if h : s∣H then rawFourier a ha F (exactQuotient H s h) else 0) := by
  by_cases h : s∣H
  · rw [dite_eq_left h]
    conv_lhs => rw [exactQuotient_spec H s h]
    exact conductorFourier_lift a s ha hs F _
  · rw [dite_eq_right h, mul_zero]
    by_contra hn
    exact h (conductorFourier_support a s ha hs F H hn)

def congruenceCoefficient (a s : O) (ha : a≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (χ : (O ⧸ Ideal.span {s}) → ℂ) (H : O) : ℂ :=
  ∑' d : O ⧸ Ideal.span {s}, χ d *
    (if h : s ∣ H-a*representative s d then
      rawFourier a ha F (exactQuotient (H-a*representative s d) s h) else 0)

lemma trace_split_product (a s : O) (ha : a≠0) (hs : s≠0) (H m d : O) :
    quotientTrace (a*s) (mul_ne_zero ha hs) (Ideal.Quotient.mk _ (H*m)) *
      quotientTrace s hs (Ideal.Quotient.mk _ ((-m)*d)) =
    quotientTrace (a*s) (mul_ne_zero ha hs) (Ideal.Quotient.mk _ ((H-a*d)*m)) := by
  have he := quotientTrace_split_frequency s a hs ha H d m
  simp only [quotientTrace_mk] at he ⊢
  simpa only [mul_comm s a] using he.symm

def fullFourier (a s : O) (ha : a≠0) (hs : s≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (χ : (O ⧸ Ideal.span {s}) → ℂ) (H : O) : ℂ :=
  ∑' m : O ⧸ Ideal.span {a*s}, F (conductorReduction a s m) *
    rawFourier s hs χ (-representative (a*s) m) *
    quotientTrace (a*s) (mul_ne_zero ha hs) (Ideal.Quotient.mk _ H*m)

theorem fullFourier_eq_congruence (a s : O) (ha : a≠0) (hs : s≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (χ : (O ⧸ Ideal.span {s}) → ℂ) (H : O) :
    fullFourier a s ha hs F χ H =
      (Ideal.absNorm (Ideal.span {s}):ℂ) * congruenceCoefficient a s ha F χ H := by
  let : Finite (O ⧸ Ideal.span {a*s}) := finite_quotient_span (mul_ne_zero ha hs)
  let : Finite (O ⧸ Ideal.span {s}) := finite_quotient_span hs
  let : Fintype (O ⧸ Ideal.span {a*s}) := Fintype.ofFinite _
  let : Fintype (O ⧸ Ideal.span {s}) := Fintype.ofFinite _
  unfold fullFourier rawFourier
  simp_rw [tsum_fintype, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold congruenceCoefficient
  rw [tsum_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  calc
    _ = χ d * conductorFourier a s ha hs F (H-a*representative s d) := by
      rw [conductorFourier, tsum_fintype, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have ht := trace_split_product a s ha hs H (representative (a*s) m) (representative s d)
      simp only [map_mul, representative_spec] at ht
      rw [← ht]
      ring
    _ = _ := by rw [rawFourier_exactQuotient]; ring

theorem rawFourier_norm_le (a : O) (ha : a≠0) (F : (O ⧸ Ideal.span {a}) → ℂ)
    (hF : ∀ m, ‖F m‖≤1) (H : O) :
    ‖rawFourier a ha F H‖ ≤ (Ideal.absNorm (Ideal.span {a}):ℝ) := by
  let := finite_quotient_span ha
  let : Fintype (O ⧸ Ideal.span {a}) := Fintype.ofFinite _
  rw [rawFourier, tsum_fintype]
  calc
    _ ≤ ∑ m : O ⧸ Ideal.span {a}, ‖F m * quotientTrace a ha (Ideal.Quotient.mk _ H*m)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m : O ⧸ Ideal.span {a}, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul, AddChar.norm_apply, mul_one]
      exact hF m
    _ = _ := by simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

theorem congruenceCoefficient_norm_le (a s : O) (ha : a≠0) (hs : s≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (χ : (O ⧸ Ideal.span {s}) → ℂ)
    (hF : ∀ m, ‖F m‖≤1) (hχ : ∀ d, ‖χ d‖≤1) (H : O) :
    ‖congruenceCoefficient a s ha F χ H‖ ≤
      (Ideal.absNorm (Ideal.span {s}):ℝ) * (Ideal.absNorm (Ideal.span {a}):ℝ) := by
  let := finite_quotient_span hs
  let : Fintype (O ⧸ Ideal.span {s}) := Fintype.ofFinite _
  unfold congruenceCoefficient
  rw [tsum_fintype]
  calc
    _ ≤ ∑ d : O ⧸ Ideal.span {s}, ‖χ d *
        (if h : s ∣ H-a*representative s d then
          rawFourier a ha F (exactQuotient (H-a*representative s d) s h) else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _d : O ⧸ Ideal.span {s}, (Ideal.absNorm (Ideal.span {a}):ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      split_ifs
      · rw [norm_mul]
        exact (mul_le_mul (hχ d) (rawFourier_norm_le a ha F hF _)
          (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      · simp only [mul_zero, norm_zero]
        positivity
    _ = _ := by simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1209

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PhysicalCoefficient
Source SHA256: cc0d219fc811ba2c1198a4f75dd08cd5f7dc40fdd9a6dba9eacd185085c46d1d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1210


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O

def calibratedNumerator (C : CalibrationData) (A m : O) : ℂ :=
  C.residueMonoid m * idealRowHom m (Ideal.span {A})

lemma calibratedNumerator_congr (C : CalibrationData) (A m n : O)
    (h : m-n ∈ (Ideal.span {C.generator*A} : Ideal O)) :
    calibratedNumerator C A m = calibratedNumerator C A n := by
  have hd : C.generator*A ∣ m-n := Ideal.mem_span_singleton.mp h
  have hb : Ideal.Quotient.mk (Ideal.span {C.generator}) m =
      Ideal.Quotient.mk (Ideal.span {C.generator}) n := by
    apply Ideal.Quotient.eq.mpr
    exact Ideal.mem_span_singleton.mpr ((dvd_mul_right C.generator A).trans hd)
  have hA : m-n ∈ (Ideal.span {A} : Ideal O) :=
    Ideal.mem_span_singleton.mpr ((dvd_mul_left A C.generator).trans hd)
  unfold calibratedNumerator CalibrationData.residueMonoid
  simp only [MonoidHom.comp_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, hb, idealRowHom_congr_mod (Ideal.span {A}) m n hA]

def calibratedQuotient (C : CalibrationData) (A : O)
    (m : O ⧸ Ideal.span {C.generator*A}) : ℂ :=
  calibratedNumerator C A (representative (C.generator*A) m)

lemma calibratedQuotient_mk (C : CalibrationData) (A m : O) :
    calibratedQuotient C A (Ideal.Quotient.mk _ m) = calibratedNumerator C A m := by
  apply calibratedNumerator_congr
  exact Ideal.Quotient.eq.mp (representative_spec _ _)

def outerQuotient (s : O) (d : O ⧸ Ideal.span {s}) : ℂ :=
  idealRowHom (representative s d) (Ideal.span {s})

lemma rawFourier_outer (s : O) (hs : s≠0) (h : O) :
    rawFourier s hs (outerQuotient s) h = sexticGauss s hs h := rfl

def actualCongruenceCoefficient (C : CalibrationData) (A s : O) (hA : A≠0) (H : O) : ℂ :=
  congruenceCoefficient (C.generator*A) s (mul_ne_zero C.generator_ne_zero hA)
    (calibratedQuotient C A) (outerQuotient s) H

def actualPhysicalFourier (C : CalibrationData) (A s : O) (hA : A≠0) (hs : s≠0) (H : O) : ℂ :=
  ∑' m : O ⧸ Ideal.span {(C.generator*A)*s},
    calibratedNumerator C A (representative ((C.generator*A)*s) m) *
    sexticGauss s hs (-representative ((C.generator*A)*s) m) *
    quotientTrace ((C.generator*A)*s) (mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs)
      (Ideal.Quotient.mk _ H*m)

theorem actualPhysicalFourier_eq (C : CalibrationData) (A s : O) (hA : A≠0) (hs : s≠0) (H : O) :
    actualPhysicalFourier C A s hA hs H =
      (Ideal.absNorm (Ideal.span {s}):ℂ) * actualCongruenceCoefficient C A s hA H := by
  unfold actualCongruenceCoefficient
  rw [← fullFourier_eq_congruence (C.generator*A) s (mul_ne_zero C.generator_ne_zero hA) hs]
  unfold actualPhysicalFourier fullFourier
  apply tsum_congr
  intro m
  rw [rawFourier_outer]
  have he : conductorReduction (C.generator*A) s m =
      Ideal.Quotient.mk (Ideal.span {C.generator*A}) (representative ((C.generator*A)*s) m) := by
    conv_lhs => rw [← representative_spec ((C.generator*A)*s) m]
    rfl
  rw [he, calibratedQuotient_mk]

lemma calibratedNumerator_norm_le (C : CalibrationData) (A m : O) :
    ‖calibratedNumerator C A m‖≤1 := by
  let := ConcreteTraceCRT.finite_quotient_span C.generator_ne_zero
  let : Fintype (O ⧸ Ideal.span {C.generator}) := Fintype.ofFinite _
  have hC : ‖C.residueMonoid m‖≤1 :=
    QuadraticInitialBound.norm_finite_character_le_one C.residue _
  rw [calibratedNumerator, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hC).trans (idealRowHom_norm _ _)

theorem actualCongruenceCoefficient_norm_le (C : CalibrationData) (A s : O)
    (hA : A≠0) (hs : s≠0) (H : O) :
    ‖actualCongruenceCoefficient C A s hA H‖ ≤
      (Ideal.absNorm (Ideal.span {s}):ℝ) *
        (Ideal.absNorm (Ideal.span {C.generator*A}):ℝ) := by
  apply congruenceCoefficient_norm_le _ _ _ hs
  · intro m
    exact calibratedNumerator_norm_le C A _
  · intro d
    exact idealRowHom_norm _ _

theorem normalizedPhysicalFourier_eq (C : CalibrationData) (A s : O)
    (hA : A≠0) (hs : s≠0) (H : O) :
    (Real.sqrt (Ideal.absNorm (Ideal.span {s})):ℂ)⁻¹ * actualPhysicalFourier C A s hA hs H =
      (Real.sqrt (Ideal.absNorm (Ideal.span {s})):ℂ) * actualCongruenceCoefficient C A s hA H := by
  have hQ : 0<(Ideal.absNorm (Ideal.span {s}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hs))
  have hroot : (Real.sqrt (Ideal.absNorm (Ideal.span {s})):ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hQ).ne'
  have he : (Ideal.absNorm (Ideal.span {s}):ℂ) =
      (Real.sqrt (Ideal.absNorm (Ideal.span {s})):ℂ)^2 := by
    exact_mod_cast (Real.sq_sqrt hQ.le).symm
  rw [actualPhysicalFourier_eq, he]
  field_simp

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1210

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PhysicalPoisson
Source SHA256: e11d050153c35e821df8372f14c29a250302bbb47ff95fb7cfbd56bee630818a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1211


namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition ConcreteTraceCRT
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

lemma sexticGauss_frequency_congr (s : O) (hs : s≠0) (h k : O)
    (he : h-k ∈ (Ideal.span {s}:Ideal O)) : sexticGauss s hs h = sexticGauss s hs k := by
  have hmk := Ideal.Quotient.eq.mpr he
  simp only [sexticGauss, hmk]

def physicalQuotient (C : CalibrationData) (A s : O) (hs : s≠0)
    (m : O ⧸ Ideal.span {(C.generator*A)*s}) : ℂ :=
  calibratedNumerator C A (representative ((C.generator*A)*s) m) *
    sexticGauss s hs (-representative ((C.generator*A)*s) m)

lemma physicalQuotient_mk (C : CalibrationData) (A s : O) (hs : s≠0) (m : O) :
    physicalQuotient C A s hs (Ideal.Quotient.mk _ m) =
      calibratedNumerator C A m * sexticGauss s hs (-m) := by
  have hd : (C.generator*A)*s ∣ representative ((C.generator*A)*s) (Ideal.Quotient.mk _ m)-m :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (representative_spec _ _))
  have hA : representative ((C.generator*A)*s) (Ideal.Quotient.mk _ m)-m ∈
      (Ideal.span {C.generator*A}:Ideal O) :=
    Ideal.mem_span_singleton.mpr ((dvd_mul_right (C.generator*A) s).trans hd)
  have hs' : -representative ((C.generator*A)*s) (Ideal.Quotient.mk _ m)-(-m) ∈
      (Ideal.span {s}:Ideal O) := by
    apply Ideal.mem_span_singleton.mpr
    rw [show -representative ((C.generator*A)*s) (Ideal.Quotient.mk _ m)-(-m) =
      -(representative ((C.generator*A)*s) (Ideal.Quotient.mk _ m)-m) by ring]
    exact dvd_neg.mpr ((dvd_mul_left s (C.generator*A)).trans hd)
  unfold physicalQuotient
  rw [calibratedNumerator_congr C A _ m hA, sexticGauss_frequency_congr s hs _ (-m) hs']

theorem physical_row_poisson (C : CalibrationData) (A s : O) (hA : A≠0) (hs : s≠0)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W)
    (K : ℝ) (hK : 0<K) :
    (∑' m : O, calibratedNumerator C A m * sexticGauss s hs (-m) * W (elementNorm m/K)) =
      ((K / elementNorm (C.generator*A) : ℝ):ℂ) *
        ∑' H : O, actualCongruenceCoefficient C A s hA H *
          paperRadialFourier W (K*elementNorm H/elementNorm ((C.generator*A)*s)) := by
  let c := (C.generator*A)*s
  have hc : c≠0 := mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs
  let := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  have ht := actual_compact_radial_paper_poisson_trace W hWc hWs K hK c hc
    (physicalQuotient C A s hs)
  change (∑' m : O, physicalQuotient C A s hs (Ideal.Quotient.mk _ m) *
    W (‖eisEmbedding m‖^2/K)) =
    (K/‖eisEmbedding c‖^2:ℝ) • ∑' H : O,
      (∑ r : O ⧸ Ideal.span {c}, physicalQuotient C A s hs r *
        quotientTrace c hc (Ideal.Quotient.mk _ H*r)) *
        paperRadialFourier W (K*‖eisEmbedding H‖^2/‖eisEmbedding c‖^2) at ht
  have hf (H : O) : (∑ r : O ⧸ Ideal.span {c}, physicalQuotient C A s hs r *
      quotientTrace c hc (Ideal.Quotient.mk _ H*r)) =
        (Ideal.absNorm (Ideal.span {s}):ℂ) * actualCongruenceCoefficient C A s hA H := by
    rw [← actualPhysicalFourier_eq C A s hA hs H]
    exact (tsum_fintype _).symm
  simp_rw [physicalQuotient_mk, eisEmbedding_norm_sq_eq_absNorm_span, hf] at ht
  change (∑' m : O, calibratedNumerator C A m * sexticGauss s hs (-m) * W (elementNorm m/K)) =
    (K/elementNorm c:ℝ) • ∑' H : O,
      ((Ideal.absNorm (Ideal.span {s}):ℂ) * actualCongruenceCoefficient C A s hA H) *
        paperRadialFourier W (K*elementNorm H/elementNorm c) at ht
  rw [ht]
  simp only [mul_assoc, tsum_mul_left, Complex.real_smul, Complex.ofReal_div]
  have hn : (elementNorm s:ℂ)≠0 := by
    simp only [elementNorm, Complex.ofReal_natCast]
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hs)
  have hnorm : elementNorm c = elementNorm (C.generator*A) * elementNorm s := by
    dsimp only [elementNorm, c]
    rw [← Ideal.span_singleton_mul_span_singleton, map_mul, Nat.cast_mul]
  simp only [← mul_assoc C.generator A s]
  rw [hnorm, Complex.ofReal_mul]
  simp only [elementNorm, Complex.ofReal_natCast] at hn ⊢
  field_simp

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1211

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PrincipalEulerIdentity
Source SHA256: 8edd1fc6579727fc2ab6ac39dd467b89840ba43f26bf48a6201d2cc5e8515e0d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1212



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma evenRatio_eq_coordR (Q : ℝ) (hQ : 0<Q) (a x z : ℂ) :
    evenRatio Q a ((Q:ℂ)^(-x)) (coordV Q z) = coordR Q (a^2) x z := by
  have hn : (Q:ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  unfold evenRatio coordR coordV
  calc
    _ = a^2 * ((Q:ℂ)^4 * ((Q:ℂ)^(-x))^6 * (Q:ℂ)^(-6*z)) := by ring
    _ = a^2 * ((Q:ℂ)^(4:ℂ) * (Q:ℂ)^((6:ℂ)*(-x)) * (Q:ℂ)^(-6*z)) := by
      rw [Complex.cpow_ofNat]
      have h6 : (Q:ℂ)^((6:ℂ)*(-x)) = ((Q:ℂ)^(-x))^6 := by
        simpa using Complex.cpow_nat_mul (Q:ℂ) 6 (-x)
      rw [h6]
    _ = a^2 * (Q:ℂ)^((4:ℂ)+6*(-x)+(-6*z)) := by
      rw [← Complex.cpow_add _ _ hn, ← Complex.cpow_add _ _ hn]
    _ = _ := by congr 2; ring

lemma coordK_eq_geometric (Q : ℝ) (hQ : 0<Q) (eta x w : ℂ) :
    coordK Q eta x w = eta*((Q:ℂ)-1)*((Q:ℂ)^(-x))*((Q:ℂ)^(-w)) := by
  have hn : (Q:ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  unfold coordK
  rw [show -x-w = -x+(-w) by ring, Complex.cpow_add _ _ hn]
  ring

lemma one_sub_ne_zero_of_norm_lt_one (a : ℂ) (ha : ‖a‖<1) : 1-a ≠ 0 := by
  intro h
  have he : a=1 := by linear_combination -h
  rw [he, norm_one] at ha
  exact lt_irrefl _ ha

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def principalFullSeries (eta a X W V : ℂ) : ℂ :=
  1/(1-V)+W/(1-W)+principalMarkedSeries p hp hg eta a X W V

include hc

theorem principalFullSeries_euler_identity (eta a x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) (a^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) eta 1 x ≠ 0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    principalFullSeries p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) =
      (1-coordD Q eta 1 x) / ((1-coordV Q z)*(1-coordW Q 1 w)) *
        unramifiedClosed Q (a^2) eta 1 x w z := by
  dsimp only
  have hQ : 0 < (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  simp only [Complex.ofReal_natCast]
  have hratio := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ a x z
  simp only [Complex.ofReal_natCast] at hratio
  have hr : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1 := by
    rw [hratio]
    exact hR
  rw [principalFullSeries, principalMarkedSeries_eq p hp hg hc _ _ _ _ _ hV hr,
    hratio]
  unfold unramifiedClosed
  dsimp only
  rw [coordK_eq_geometric _ hQ]
  have hv := one_sub_ne_zero_of_norm_lt_one _ hV
  have hw := one_sub_ne_zero_of_norm_lt_one _ hW
  simp only [coordW, coordD, star_one, mul_one, one_mul, Complex.ofReal_natCast] at hD hw ⊢
  unfold ProbeLocal.continuedCorrection
  field_simp [hD, hv, hw]
  ring

omit hc

def actualACube (eta : HeckeFamily.Character) (p : O) : ℂ :=
  star (FiniteGaussPhase.angularFactor p)^3 * HeckeFamily.elementCoeff eta p^3

lemma actualACube_sq (eta : HeckeFamily.Character) (p : O) :
    actualACube eta p ^ 2 = actualAPhase eta p := by
  unfold actualACube actualAPhase
  ring

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1212

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PrincipalProduct
Source SHA256: aae40d351969536fa8e3faae9f588ba4b94f1ad0e0429e74bcdcce5da414a198
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1213



namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss SmoothMobiusCorrection
local notation "O" => ActualEisensteinCubic.O

def primeDefectBound (P : PrimeIdeal) : ℝ :=
  240 * (Ideal.absNorm P.val : ℝ) ^ (-(363/200:ℝ))

def principalLocal (eta : HeckeFamily.Character) (P : PrimeIdeal) (s : ℂ) : ℂ :=
  unramifiedClosed (Ideal.absNorm P.val) (actualAPhase eta (primaryGenerator P.val))
    (HeckeFamily.elementCoeff eta (primaryGenerator P.val)) 1 s 1 (1/6)

def principalCorrection (eta : HeckeFamily.Character) (S : Finset (Ideal O)) (s : ℂ) : ℂ :=
  ∏' P : {P : PrimeIdeal // P.val ∉ S}, principalLocal eta P.val s

lemma primeDefectBound_nonneg (P : PrimeIdeal) : 0 ≤ primeDefectBound P := by
  unfold primeDefectBound
  positivity

lemma primeDefectBound_summable : Summable primeDefectBound := by
  have h : Summable (fun P : PrimeIdeal => ‖CubicEisenstein.fullIdealWeight ((363/200:ℝ):ℂ) P.val‖) :=
    (CubicEisenstein.fullIdealWeight_summable_norm ((363/200:ℝ):ℂ) (by norm_num)).comp_injective
      Subtype.val_injective
  apply (h.mul_left 240).congr
  intro P
  unfold primeDefectBound CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero, ite_false]
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  norm_num

lemma principalLocal_bound (eta : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4 ≤ Ideal.absNorm P.val) (s : ℂ) (hs : 7/8 < s.re) :
    ‖principalLocal eta P s-1‖ ≤ primeDefectBound P := by
  apply unramifiedClosed_second_region_bound
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one eta _
  · exact ProbeRow.targetMonoid_norm_le_one eta _
  · simp
  · exact hs.le
  · norm_num
  · norm_num

lemma principalLocal_analytic (eta : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4 ≤ Ideal.absNorm P.val) :
    AnalyticOnNhd ℂ (principalLocal eta P) {s : ℂ | 7/8 < s.re} := by
  apply principalClosed_analytic
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one eta _
  · exact ProbeRow.targetMonoid_norm_le_one eta _

theorem exists_uniform_principal_cutoff :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ (S : Finset (Ideal O)),
      (∀ P : PrimeIdeal, Ideal.absNorm P.val ≤ N → P.val ∈ S) →
      ∀ eta : HeckeFamily.Character,
        AnalyticOnNhd ℂ (principalCorrection eta S) {s : ℂ | 7/8 < s.re} ∧
        ∀ s : ℂ, 7/8 < s.re → ‖principalCorrection eta S s-1‖ ≤ 1/2 := by
  have ht := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero primeDefectBound)).2 (1/6) (by norm_num)
  obtain ⟨F, hF⟩ := ht.exists
  let N := max 4 (F.sup (fun P => Ideal.absNorm P.val))
  refine ⟨N, le_max_left _ _, ?_⟩
  intro S hS eta
  let T := {P : PrimeIdeal // P.val ∉ S}
  have hnot (P : T) : P.val ∉ F := by
    intro hm
    apply P.property
    apply hS P.val
    exact (Finset.le_sup (f := fun Q : PrimeIdeal => Ideal.absNorm Q.val) hm).trans (le_max_right _ _)
  let inc : T → {P : PrimeIdeal // P ∉ F} := fun P => ⟨P.val, hnot P⟩
  have hi : Function.Injective inc := by
    intro P Q h
    apply Subtype.ext
    exact congrArg (fun t : {P : PrimeIdeal // P ∉ F} => t.val) h
  have hnorm (P : T) : 4 ≤ Ideal.absNorm P.val.val := by
    have hh : ¬ Ideal.absNorm P.val.val ≤ N := fun h => P.property (hS P.val h)
    exact (le_max_left _ _).trans (Nat.le_of_lt (Nat.lt_of_not_ge hh))
  have hsum : Summable (fun P : T => primeDefectBound P.val) :=
    primeDefectBound_summable.subtype _
  have hsmall : (∑' P : T, primeDefectBound P.val) ≤ 1/6 := by
    apply le_trans ?_ hF.le
    exact Summable.tsum_le_tsum_of_inj inc hi
      (fun P _ => primeDefectBound_nonneg P.val) (fun _ => le_rfl)
      hsum (primeDefectBound_summable.subtype _)
  have hhalf (P : T) : primeDefectBound P.val ≤ 1/2 := by
    have hterm := Summable.le_tsum hsum P (fun Q _ => primeDefectBound_nonneg Q.val)
    linarith
  constructor
  · exact normalProduct_analytic (fun P : T => principalLocal eta P.val)
      (fun P : T => primeDefectBound P.val) _ (Complex.isOpen_re_gt _) hsum
      (fun P => principalLocal_analytic eta P.val (hnorm P))
      (fun P s hs => principalLocal_bound eta P.val (hnorm P) s hs) hhalf
  · intro s hs
    exact product_defect_le (fun P : T => principalLocal eta P.val s)
      (fun P : T => primeDefectBound P.val) hsum
      (fun P => principalLocal_bound eta P.val (hnorm P) s hs) hhalf hsmall

def smallPrimeSet (N : ℕ) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_le N).toFinset.filter Prime

lemma mem_smallPrimeSet (N : ℕ) (P : PrimeIdeal) :
    P.val ∈ smallPrimeSet N ↔ Ideal.absNorm P.val ≤ N := by
  simp [smallPrimeSet, P.property]

theorem exists_principal_correction (S₀ : Finset (Ideal O)) :
    ∃ S : Finset (Ideal O), S₀ ⊆ S ∧ ∀ eta : HeckeFamily.Character,
      AnalyticOnNhd ℂ (principalCorrection eta S) {s : ℂ | 7/8 < s.re} ∧
      ∀ s : ℂ, 7/8 < s.re → ‖principalCorrection eta S s-1‖ ≤ 1/2 := by
  obtain ⟨N, hN, hcut⟩ := exists_uniform_principal_cutoff
  refine ⟨S₀ ∪ smallPrimeSet N, Finset.subset_union_left, ?_⟩
  apply hcut
  intro P hP
  exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1213

/-! Original module: OAI.NumberTheory.DirichletL.Detector.RowAnalytic
Source SHA256: 0feee26f076e10767a3f7426fe13c89e56db7e60a8bb1e0dc73fb5684d609511
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1214




namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem fullIdealWeight_norm_eq_of_re (s t : ℂ) (h : s.re = t.re) (I : Ideal O) :
    ‖fullIdealWeight s I‖ = ‖fullIdealWeight t I‖ := by
  by_cases hI : I = 0
  · simp [hI, fullIdealWeight]
  · exact (norm_fullIdealWeight s ⟨I, hI⟩).trans
      ((by rw [h] : _ = _).trans (norm_fullIdealWeight t ⟨I, hI⟩).symm)

theorem fullIdealWeight_continuous (I : Ideal O) : Continuous (fun t => fullIdealWeight t I) := by
  by_cases hI : I = 0
  · simp only [hI, fullIdealWeight]
    exact continuous_const
  · have hn : (Ideal.absNorm I : ℂ) ≠ 0 := by
      exact_mod_cast (Ideal.absNorm_ne_zero_iff I).mpr
        (Ring.HasFiniteQuotients.finiteQuotient hI)
    simp only [fullIdealWeight, ite_eq_right hI]
    exact continuous_id.neg.const_cpow (Or.inl hn)

def rowMajorant (σ : ℝ) (p : Ideal O × Ideal O) : ℝ :=
  2 * (‖fullIdealWeight (σ : ℂ) p.1‖ * ‖fullIdealWeight (3 * (σ : ℂ)) p.2‖)

theorem rowMajorant_summable (σ : ℝ) (hσ : 1 < σ) : Summable (rowMajorant σ) := by
  have h3 : 1 < (3 * (σ : ℂ)).re := by norm_num; linarith
  exact ((fullIdealWeight_summable_norm (σ : ℂ) hσ).mul_of_nonneg
    (fullIdealWeight_summable_norm (3 * (σ : ℂ)) h3)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left 2

theorem spectralSummand_vertical_bound (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ y : ℝ) (p : Ideal O × Ideal O) :
    ‖spectralSummand S D Ψ ((σ : ℂ) + y * Complex.I) p.1 p.2‖ ≤ rowMajorant σ p := by
  have h1 : ((σ : ℂ) + y * Complex.I).re = (σ : ℂ).re := by simp
  have h3 : (3 * ((σ : ℂ) + y * Complex.I)).re = (3 * (σ : ℂ)).re := by simp
  simpa only [rowMajorant, fullIdealWeight_norm_eq_of_re _ _ h1,
    fullIdealWeight_norm_eq_of_re _ _ h3] using
    spectralSummand_norm_le S D Ψ hΨ ((σ : ℂ) + y * Complex.I) p.1 p.2

theorem spectralRow_continuous_vertical (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ) :
    Continuous (fun y : ℝ => spectralRow S D Ψ ((σ : ℂ) + y * Complex.I)) := by
  apply continuous_tsum _ (rowMajorant_summable σ hσ)
    (fun p y => spectralSummand_vertical_bound S D Ψ hΨ σ y p)
  intro p
  have hc : Continuous (fun y : ℝ => (σ : ℂ) + y * Complex.I) := by fun_prop
  exact continuous_const.mul ((fullIdealWeight_continuous p.1).comp hc |>.mul
    ((fullIdealWeight_continuous p.2).comp (continuous_const.mul hc)))

theorem spectralRow_vertical_bound (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ) (y : ℝ) :
    ‖spectralRow S D Ψ ((σ : ℂ) + y * Complex.I)‖ ≤ ∑' p, rowMajorant σ p := by
  have hs := spectralRow_summable S D Ψ hΨ ((σ : ℂ) + y * Complex.I) (by simpa using hσ)
  exact (norm_tsum_le_tsum_norm hs.norm).trans
    (hs.norm.tsum_le_tsum (fun p => spectralSummand_vertical_bound S D Ψ hΨ σ y p)
      (rowMajorant_summable σ hσ))

theorem verticalKernel_norm (Z : ℝ) (hZ : 0 < Z) (σ y : ℝ) :
    ‖(Z : ℂ) ^ ((σ : ℂ) + y * Complex.I) *
      Complex.exp (((σ : ℂ) + y * Complex.I) ^ 2)‖ =
      Z ^ σ * Real.exp (σ ^ 2) * Real.exp (-1 * y ^ 2) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hZ, Complex.norm_exp]
  have hre : (((σ : ℂ) + y * Complex.I) ^ 2).re = σ ^ 2 + (-1 * y ^ 2) := by
    simp [pow_two, Complex.mul_re, Complex.mul_im]
    ring
  rw [hre, Real.exp_add]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  ring

theorem spectralRow_vertical_integrable (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ)
    (Z : ℝ) (hZ : 0 < Z) :
    Integrable (fun y : ℝ => (Z : ℂ) ^ ((σ : ℂ) + y * Complex.I) *
      Complex.exp (((σ : ℂ) + y * Complex.I) ^ 2) *
      spectralRow S D Ψ ((σ : ℂ) + y * Complex.I)) := by
  let B : ℝ := ∑' p, rowMajorant σ p
  have hg := (integrable_exp_neg_mul_sq (b := 1) (by norm_num)).const_mul
    (Z ^ σ * Real.exp (σ ^ 2) * B)
  have hc : Continuous (fun y : ℝ => (σ : ℂ) + y * Complex.I) := by fun_prop
  have hk := (hc.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))).mul ((hc.pow 2).cexp)
  apply hg.mono' (hk.mul (spectralRow_continuous_vertical S D Ψ hΨ σ hσ)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro y
  dsimp only [Pi.mul_apply, Pi.pow_apply]
  rw [norm_mul, verticalKernel_norm Z hZ σ y]
  calc
    _ ≤ (Z ^ σ * Real.exp (σ ^ 2) * Real.exp (-1 * y ^ 2)) * B :=
      mul_le_mul_of_nonneg_left (spectralRow_vertical_bound S D Ψ hΨ σ hσ y)
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg hZ.le _) (Real.exp_pos _).le) (Real.exp_pos _).le)
    _ = _ := by ring
