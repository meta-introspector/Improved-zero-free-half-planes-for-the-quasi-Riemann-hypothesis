    ConcreteTraceCRT.finite_quotient_span (pow_ne_zero 2 (mul_ne_zero (by norm_num) hc))
  let : Fintype (Eis⧸Ideal.span {((9:Eis)*c)^2}) := Fintype.ofFinite _
  let mask := Ideal.span {m}*F
  have hmask0 : mask≠0 := mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm) hF.ne_zero
  let E := fixedFourierGeometry c hc
  have hEc : ∀ h,(E h).c0≠0 := fun h => (E h).denominator_ne_zero
  have hEN : ∀ h,(9:Eis)*(E h).c0∣(9:Eis)*c := fun h => mul_dvd_mul_left (9:Eis) (E h).denominator_dvd
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := perturbed_original_frozen_energy L hL0 hL1
    (fun h => (E h).a0) (fun h => (E h).c0) (fun h => (E h).mode) lo hi hlo W hWs hW
    (fun h => (E h).shape) hEc hEN (fun h => (E h).primary) (fun h => (E h).coprime)
    mask hmask0 Ck η hCk hη hη1 rmax
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ J hJ Z d ell0 shift hZ hd hd1 hell hellcap hshift hJn
    parents hparents hcard lists H hdis hmax hgood hprime hodd hLP hH1 hH hprod Ψ hΨnorm hΨperiod u θ w hw
  let rows := originalResidualRows parents J mask
  have hparents0 : ∀ I∈parents,I≠0 := fun I hI => (hparents I hI).1
  let hrows : ∀ K∈rows,Admissible K := originalResidualAdmissible parents J F m hbad
  have hcop : ∀ K∈rows,IsCoprime Q₀ K := by
    intro K hK
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
    exact rowResidualPart_coprime_period I F Q₀ m hperiod
  have hGN : ∀ f,IsCoprime (Ideal.span {(9:Eis)*c}) ((poolPrimeFamily J mask Q₀).ideal f) :=
    (poolPrimeFamily J mask Q₀).level_coprime Q₀ c hcQ (poolPrimeFamily_period J mask Q₀)
  have hrowcop : ∀ K∈rows,(∀ f,IsCoprime ((poolPrimeFamily J mask Q₀).ideal f) K) ∧ IsCoprime (Ideal.span {(9:Eis)*c}) K := by
    intro K hK
    refine ⟨?_,residual_level_coprime K Q₀ (hrows K hK) c hcQ (hcop K hK)⟩
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨hIp,hpow,hmask'⟩ := Finset.mem_filter.mp hI
    exact poolPrimeFamily_fiber_row_coprime J I mask Q₀ hJ (hparents0 I hIp) hmask0 hpow.symm hmask'.symm
  have hLN : ∀ i,∀ P∈lists i,IsCoprime (Ideal.span {(9:Eis)*c}) P :=
    fun i P hP => maximal_prime_level_coprime P (hmax i P hP) (hgood i P hP) Q₀ c hcQ (hLP i P hP)
  have hz : 1< Z := lt_of_lt_of_le hZ₀ hZ
  have hzp : 0< Z := lt_trans zero_lt_one hz
  let O := normWidth Z (rowPowerfulPart J)
  have hO : 0≤ O := normWidth_nonneg Z hz _ (rowPowerfulPart_ne_zero J)
  have hPowPos : 0<(Ideal.absNorm (rowPowerfulPart J):ℝ) := by
    have := QuadraticMainBoundary.norm_one_le (rowPowerfulPart_ne_zero J)
    linarith
  obtain ⟨D,hD⟩ := he (σ:=σ) J F Q₀ hJ hF.ne_zero Z d ell0 shift O
    hZ hd hd1 hell hellcap hshift rfl hJn parents rows hparents (Finset.Subset.refl _) hbad
    hcard lists H hdis hmax hgood hprime hrows hH1 hH hprod hGN (poolPrimeFamily_odd J mask Q₀)
    hrowcop hLN hodd
  let scalar := fun h (K : rows) => fixedThetaRowCoeff c hc
    ((residualOriginalData parents J F hF m hm hparents0 u K).fixedFactor Ψ Q) h
  have hscalar : ∀ h K,‖scalar h K‖≤1 := fun h K =>
    (residualOriginalData parents J F hF m hm hparents0 u K).fixedCoefficient_norm Ψ Q hΨnorm c hc h
  have henergy := hD θ w scalar hw hscalar
  have hTw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) :=
    CanonicalRowCompletion.normTwistedSource_contDiff W lo hi hlo hWs hW θ
  have hTs := (CompletedHeight.normTwistedSource_support W θ).trans hWs
  have hTc : HasCompactSupport (CompletedHeight.normTwistedSource W θ) :=
    HasCompactSupport.intro isCompact_Icc (fun x hx => by
      by_contra hn
      exact hx (hTs hn))
  have hid (K : rows) := original_completed_residual_source parents J F hJ hF m hm hparents0 u hbad
    Q hQ c hc hcQ E hcop lists hmax hgood hdis hodd hLP D Ψ hΨnorm hΨperiod hmLam hm2
    (CompletedHeight.normTwistedSource W θ) hTc lo hi hlo hTs hTw (Z^(1+ell0+shift)) (Real.rpow_pos_of_pos hzp _) w K
  have hre := original_fiber_energy_reindex parents J (mask) hparents0
    (fun I => ∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
        (u.val*ConcretePrimeRowBridge.idealGenerator I))
      (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift))
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0))
  rw [hre]
  have heq : (∑ K : rows,‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
        (u.val*ConcretePrimeRowBridge.idealGenerator (reconstructFiberRow J mask K.val)))
      (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift))
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)=
      ∑ K : rows,‖thetaDerivativeScalar⁻¹*∑ h,scalar h K*
        ∑ A : Finset (FreeReflection.pool J mask Q₀),frozenInactiveWeight J F mask Q₀ A*
          ∑ T : Finset σ,originalInactivePhysical ((poolPrimeFamily J mask Q₀).restrict A)
            (poolPrimeFamily J mask Q₀).ideal rows hrows lists hmax hgood T (D h A T) (E h).shape (E h).denominator_ne_zero
            (fun b : A => completedLocalExponent J F b.val.val)
            (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift)) w K‖^2 := by
    apply Finset.sum_congr rfl
    intro K hK
    exact congrArg (fun z : ℂ => ‖z‖^2) (hid K)
  have hbound := heq.trans_le henergy
  have hp : Z^O=(Ideal.absNorm (rowPowerfulPart J):ℝ) := Real.rpow_logb hzp (ne_of_gt hz) hPowPos
  have hR : C*(1+‖θ‖)^degree*Z^((1-L-2*d)+max (d+5*L-1) 0/4+506*η-O/2)=
      C*(1+‖θ‖)^degree*Z^((1-L-2*d)+max (d+5*L-1) 0/4+506*η)*(Ideal.absNorm (rowPowerfulPart J):ℝ)^(-(1/2:ℝ)) := by
    rw [show (1-L-2*d)+max (d+5*L-1) 0/4+506*η-O/2=((1-L-2*d)+max (d+5*L-1) 0/4+506*η)+O*(-(1/2:ℝ)) by ring,
      Real.rpow_add hzp,Real.rpow_mul hzp.le,hp]
    ring
  have hs := Finset.sum_coe_sort rows (fun K : Ideal Eis =>
    ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
        (u.val*ConcretePrimeRowBridge.idealGenerator (reconstructFiberRow J mask K)))
      (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift))
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)
  exact hs.symm.trans_le (hbound.trans_eq hR)
end
end SevenEighths.InverseReflectedPhase

end OAI

end LocalModule78
/- END analytic_low.PerturbedCompletedFiber -/

/- BEGIN original module analytic_low.PerturbedCompletedRows -/
section LocalModule79

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem perturbed_completed_rows_energy (L : ℝ) (hL0 : 0≤ L) (hL1 : L≤1/5) (Q : Ideal Eis) (hQ : Q≠0)
    (F : Ideal Eis) (hF : Squarefree F) (m : Eis) (hm : m≠0)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (hperiod : Q*Ideal.span {(72:Eis)}∣Ideal.span {m})
    (hbad : ∀ P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (lo hi : ℝ) (hlo : 0< lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Ck η : ℝ) (hCk : 0< Ck) (hη : 0<η) (hη1 : η≤1) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0< C ∧ 1< Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (Z d ell0 shift : ℝ), Z₀≤ Z → 0≤ d → d≤ L → 0≤ ell0 → ell0≤ L-d+η → |shift|≤η →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Ck*Z^(1-L-2*d)) →
      Fintype.card σ≤ rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,∀ P∈lists i,IsCoprime (Q*Ideal.span {(72:Eis)}) P) →
      (∀ i,1≤ H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤ H i) → (∏ i,H i)≤ Z^ell0 →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo Q Ψ →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈parents,
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(1+ell0+shift)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^((1-L-2*d)+max (d+5*L-1) 0/4+507*η) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := perturbed_completed_fiber_energy L hL0 hL1 Q hQ F hF m hm hmLam hm2 hperiod hbad
    lo hi hlo W hWs hW Ck η hCk hη hη1 rmax
  obtain ⟨D,hD,ha⟩ := completed_representative_aggregation 2 η (by norm_num) hη
  let mask := Ideal.span {m}*F
  let Z₁ := max Z₀ (max 2 (max Ck (Ideal.absNorm mask:ℝ)))
  refine ⟨degree,D*C,Z₁,mul_pos hD hC,lt_of_lt_of_le hZ₀ (le_max_left _ _),?_⟩
  intro σ _ _ Z d ell0 shift hZ hd hd1 hell hellcap hshift
    parents hparents hcard lists H hdis hmax hgood hprime hodd hLP hH1 hH hprod Ψ hΨnorm hΨperiod u θ w hw
  have hZZ : Z₀≤ Z := (le_max_left _ _).trans hZ
  have hZ2 : 2≤ Z := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hZ
  have hz : 0< Z := by linarith
  have hz1 : 1≤ Z := by linarith
  have hCkZ : Ck≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hmaskZ : (Ideal.absNorm mask:ℝ)≤ Z := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hmaskn : (Ideal.absNorm mask:ℝ)≤ Z^(2:ℝ) := hmaskZ.trans
    (by simpa using Real.rpow_le_rpow_of_exponent_le hz1 (show (1:ℝ)≤2 by norm_num))
  have hparentn : ∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Z^(2:ℝ) := by
    intro I hI
    refine ⟨(hparents I hI).1,(hparents I hI).2.trans ?_⟩
    calc
      _ ≤ Z*Z^(1-L-2*d) := mul_le_mul_of_nonneg_right hCkZ (Real.rpow_nonneg hz.le _)
      _ = Z^(1+(1-L-2*d)) := by rw [Real.rpow_add hz,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)
  have hh := ha Z hZ2 parents mask hparentn
    (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm) hF.ne_zero) hmaskn
    (C*(1+‖θ‖)^degree*Z^((1-L-2*d)+max (d+5*L-1) 0/4+506*η))
    (fun I => ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
        (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
      (Z^(1+ell0+shift)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)
    (by positivity) (fun J hJ => he (σ:=σ) J (hparents J hJ).1 Z d ell0 shift
      hZZ hd hd1 hell hellcap hshift (hparents J hJ).2
      parents hparents hcard lists H hdis hmax hgood hprime hodd hLP hH1 hH hprod
      Ψ hΨnorm hΨperiod u θ w hw)
  apply hh.trans_eq
  calc
    _ = (D*C)*(1+‖θ‖)^degree*(Z^η*Z^((1-L-2*d)+max (d+5*L-1) 0/4+506*η)) := by ring
    _ = _ := by rw [←Real.rpow_add hz]; congr 2; ring
end
end SevenEighths.InverseReflectedPhase

end OAI

end LocalModule79
/- END analytic_low.PerturbedCompletedRows -/

/- BEGIN original module analytic_low.PerturbedOriginalEnergy -/
section LocalModule80

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem perturbed_original_completed_energy (L : ℝ) (hL0 : 0≤ L) (hL1 : L≤1/5) (Q : Ideal Eis) (hQ : Q≠0)
    (F : Ideal Eis) (hF : Squarefree F) (m : Eis) (hm : m≠0)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (hperiod : Q*Ideal.span {(72:Eis)}∣Ideal.span {m})
    (hbad : ∀ P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (lo hi : ℝ) (hlo : 0< lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Ck η : ℝ) (hCk : 0< Ck) (hη : 0<η) (hη1 : η≤1) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0< C ∧ 1< Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (Z d ell0 shift : ℝ), Z₀≤ Z → 0≤ d → d≤ L → 0≤ ell0 → ell0≤ L-d+η → |shift|≤η →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Ck*Z^(1-L-2*d)) →
      Fintype.card σ≤ rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,1≤ H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤ H i) → (∏ i,H i)≤ Z^ell0 →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo Q Ψ →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈parents,
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(1+ell0+shift)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^((1-L-2*d)+max (d+5*L-1) 0/4+507*η) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := perturbed_completed_rows_energy L hL0 hL1 Q hQ F hF m hm hmLam hm2 hperiod hbad
    lo hi hlo W hWs hW Ck η hCk hη hη1 rmax
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ Z d ell0 shift hZ hd hd1 hell hellcap hshift
    parents hparents hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod Ψ hΨnorm hΨperiod u θ w hw
  let S := actualPuncturePrimes lists m
  let lists' := punctureLists lists S
  have hsub (i : σ) : lists' i⊆lists i := Finset.filter_subset _ _
  let w' : ∀ i,lists' i→ℂ := fun i P => w i ⟨P.val,hsub i P.property⟩
  have hLP (i : σ) (P : Ideal Eis) (hP : P∈lists' i) : IsCoprime (Q*Ideal.span {(72:Eis)}) P := by
    apply puncture_period_coprime _ m hperiod P (hmax i P (hsub i hP))
    intro hmP
    exact (Finset.mem_filter.mp hP).2 ((actualPuncturePrimes_mem lists m i P (hsub i hP)).mpr hmP)
  have hh := he (σ:=σ) Z d ell0 shift hZ hd hd1 hell hellcap hshift
    parents hparents hcard lists' H
    (fun i j hij => (hdis hij).mono (hsub i) (hsub j))
    (fun i P hP => hmax i P (hsub i hP)) (fun i P hP => hgood i P (hsub i hP))
    (fun i P hP => hprime i P (hsub i hP)) (fun i P hP => hodd i P (hsub i hP))
    hLP hH1 (fun i P hP => hH i P (hsub i hP)) hprod
    Ψ hΨnorm hΨperiod u θ w' (fun i P => hw i ⟨P.val,hsub i P.property⟩)
  apply le_trans (le_of_eq ?_) hh
  apply Finset.sum_congr rfl
  intro I hI
  exact congrArg (fun z : ℂ => ‖z‖^2) (original_completed_actual_puncture_lists lists hprime Ψ m
    (ConcretePrimeRowBridge.idealGenerator F) (u.val*ConcretePrimeRowBridge.idealGenerator I)
    (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift)) w)
end
end SevenEighths.InverseReflectedPhase

end OAI

end LocalModule80
/- END analytic_low.PerturbedOriginalEnergy -/

/- BEGIN original module analytic_low.PerturbedSelectedBound -/
section LocalModule81

namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

theorem perturbed_selected_physical_energy (L : ℝ) (hL0 : 0≤ L) (hL1 : L≤1/5) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (K : ℕ) (Ck ε : ℝ) (hCk : 0< Ck) (hε : 0<ε) (hε1 : ε≤1) :
    ∃degree : ℕ,∃C Z₀ : ℝ,0< C ∧ 1< Z₀ ∧
    ∀(Z d ell0 shift : ℝ),Z₀≤ Z→0≤ d→d≤ L→0≤ ell0→ell0≤ L-d+ε→|shift|≤ε→
    ∀(R : Finset O),(∀z∈R,z≠0 ∧ elementNorm z≤ Ck*Z^(1-L-2*d))→
    ∀(T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=> Disjoint (T i) (T j))→
    ∀(J : Finset (Fin K))(H : SelectedSlot J→ℝ),
      (∀i,1≤ H i)→(∀i P,P∈T i.val→(Ideal.absNorm P.val:ℝ)≤ H i)→(∏i,H i)≤ Z^ell0→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀(Y : Fin K→ℝ)(t : ℝ)(σ : RayRing),
      (∑z∈R,‖lowSelectedInverseRow Finset.univ
        (lowSelectedWeight η (fun i=> canonicalSlotSupport (T i)) J W Y t)
        η S hS (lowSelectedIdeal (fun i=> canonicalSlotSupport (T i)) J) (Z^(1+ell0+shift)) t σ z‖^2)≤
        C*(1+‖t‖)^degree*Z^((1-L-2*d)+max (d+5*L-1) 0/4+507*ε) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := InverseReflectedPhase.perturbed_original_completed_energy L hL0 hL1
    (lowReflectionPeriod η S hS) (lowReflectionPeriod_ne_zero η S hS)
    (1:Id) squarefree_one (lowReflectionMask η S hS) (lowReflectionMask_ne_zero η S hS)
    (lowReflectionMask_bad η S hS hbad).1 (lowReflectionMask_bad η S hS hbad).2
    (lowReflectionMask_period η S hS) (lowReflectionMask_bad_ideals η S hS hbad)
    (1/2) 2 (by norm_num) gaussianFixedWindow gaussianFixedWindow_support gaussianFixedWindow_contDiff
    Ck ε hCk hε hε1 K
  let C0 := (lowCorrectionEnergy+1)*((Fintype.card RayCharacter:ℝ)+1)*6*C
  have hC0 : 0< C0 := by have hh := lowCorrectionEnergy_nonneg;dsimp [C0];positivity
  refine ⟨degree,C0,Z₀,hC0,hZ₀,?_⟩
  intro Z d ell0 shift hZ hd hd1 hell hellcap hshift R hR T hT hout hdis J H hH1 hH hprod W hW Y t σ
  let lists := fun i : SelectedSlot J=> lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val))
  have hLP (i : SelectedSlot J) : lowPeriodPrimeList η S hS (T i.val)⊆T i.val := Finset.filter_subset _ _
  have hLS (i : SelectedSlot J) : ∀P∈lowPeriodPrimeList η S hS (T i.val),Supported P.val :=
    fun P hP=> hT i.val P (hLP i hP)
  have hlists : Pairwise (fun i j=> Disjoint (lists i) (lists j)) :=
    lowPrimeIdealList_disjoint _ (lowPeriodPrimeList_disjoint η S hS _
      (fun i j hij=> hdis (fun h=> hij (Subtype.ext h))))
  have hparents : ∀I∈lowIdealRows R,I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Ck*Z^(1-L-2*d) :=
    fun I hI=>⟨lowIdealRows_nonzero R (fun z hz=>(hR z hz).1) I hI,
      lowIdealRows_norm_bound R _ (fun z hz=>(hR z hz).2) I hI⟩
  have hcard : Fintype.card (SelectedSlot J)≤ K := by
    simpa only [Fintype.card_coe,Finset.card_univ,Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Finset.univ\J))
  have hrow (χ : RayCharacter) (u : Oˣ) :
      (∑I∈lowIdealRows R,‖lowActualIdealPolynomial lists
        (fun i I=> lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator I))
        (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS)
          (ConcretePrimeRowBridge.idealGenerator (1:Id)) (u.val*ConcretePrimeRowBridge.idealGenerator I))
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) (Z^(1+ell0+shift))‖^2)≤
          C*(1+‖t‖)^degree*Z^((1-L-2*d)+max (d+5*L-1) 0/4+507*ε) := by
    convert he Z d ell0 shift hZ hd hd1 hell hellcap hshift (lowIdealRows R) hparents hcard lists H
      hlists (fun i=> lowPrimeIdealList_maximal _)
      (fun i P hP=>(lowPrimeIdealList_good_odd _ (hLS i) P hP).1)
      (fun i=> lowPrimeIdealList_prime _)
      (fun i P hP=>(lowPrimeIdealList_good_odd _ (hLS i) P hP).2)
      hH1 (fun i=> lowPrimeIdealList_norm _ _ (fun P hP=> hH i P (hLP i hP))) hprod
      (physicalRayPeriodicBase η S hS σ χ) (lowReflectionPeriod_actual η S hS σ χ).2
      (lowReflectionPeriod_actual η S hS σ χ).1 u t
      (fun i P=> lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator P.val))
      (fun i P=> low_actual_ideal_weight_bound η (W i.val) (hW i.val) (Y i.val) t P.val) using 1
    apply Finset.sum_congr rfl
    intro I hI
    congr 2
    unfold lowActualIdealPolynomial
    congr 1
    ext p
    simp
  apply (lowSelectedInverseRow_actual_reflected_energy η S hS hbad T hT hout hdis J W Y
    (Z^(1+ell0+shift)) t σ R (fun z hz=>(hR z hz).1)).trans
  have hh := Finset.sum_le_sum (fun χ (_ : χ∈(Finset.univ:Finset RayCharacter))=>
    Finset.sum_le_sum (fun u (_ : u∈(Finset.univ:Finset Oˣ))=> hrow χ u))
  have hm := mul_le_mul_of_nonneg_left hh lowCorrectionEnergy_nonneg
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,low_unit_card] at hm
  simp only [Nat.cast_ofNat,Real.norm_eq_abs] at hm ⊢
  apply hm.trans
  dsimp [C0]
  have hc0 := lowCorrectionEnergy_nonneg
  have hcount : 0≤(Fintype.card RayCharacter:ℝ) := Nat.cast_nonneg _
  have hzpos : 0≤ Z^((1-L-2*d)+max (d+5*L-1) 0/4+507*ε) := Real.rpow_nonneg (le_trans zero_le_one (hZ₀.le.trans hZ)) _
  have htpos : 0≤(1+|t|)^degree := by positivity
  calc
    _=(lowCorrectionEnergy*(Fintype.card RayCharacter:ℝ)*6*C)*(1+|t|)^degree*
        Z^((1-L-2*d)+max (d+5*L-1) 0/4+507*ε) := by ring
    _≤_ := by gcongr <;> linarith

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule81
/- END analytic_low.PerturbedSelectedBound -/

/- BEGIN original module analytic_low.PerturbedNominalGeometry -/
section LocalModule82

namespace OAI
noncomputable section
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRaySlots
lemma perturbed_lowLength_bounds (lengthCap : ℝ) {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i)
    (hsum : ∑i,ell i≤ lengthCap) (J : Finset (Fin K)) :
    0≤ lowUnselectedLength ell J ∧ lowUnselectedLength ell J≤ lengthCap ∧
    0≤ lowSelectedLength ell J ∧ lowSelectedLength ell J≤ lengthCap-lowUnselectedLength ell J := by
  have hu : 0≤ lowUnselectedLength ell J := Finset.sum_nonneg (fun i _=> hell i)
  have hs : 0≤ lowSelectedLength ell J := Finset.sum_nonneg (fun i _=> hell i.val)
  have he := lowLength_sum ell J
  exact ⟨hu,by linarith,hs,by linarith⟩

lemma perturbed_lowPhysicalScale_source (lengthCap x y : ℝ) (hxy : x+y=1-lengthCap) (C : CalibrationData) (Z L : ℝ) (hZ : 0< Z) :
    lowPhysicalScale C (Z^(x)/L) (Z^(y)/L)=
      elementNorm C.generator*Z^(1-lengthCap)/L^2 := by
  unfold lowPhysicalScale
  have he : Z^(x)*Z^(y)=Z^(1-lengthCap) := by rw [←Real.rpow_add hZ]; rw [hxy]
  rw [←he]
  ring

lemma perturbed_lowPhysicalScale_nominal_bound (lengthCap x y : ℝ) (hxy : x+y=1-lengthCap) (C : CalibrationData) (Z L c d : ℝ)
    (hZ : 0< Z) (hc : 0< c) (hL : c*Z^d≤ L) :
    lowPhysicalScale C (Z^(x)/L) (Z^(y)/L)≤
      (elementNorm C.generator/c^2)*Z^(1-lengthCap-2*d) := by
  have hl : 0< L := lt_of_lt_of_le (by positivity) hL
  rw [perturbed_lowPhysicalScale_source lengthCap x y hxy C Z L hZ]
  calc
    _≤ elementNorm C.generator*Z^(1-lengthCap)/(c*Z^d)^2 :=
      div_le_div_of_nonneg_left (by unfold elementNorm;positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) hL 2)
    _=_ := by
      have hp : (Z^d)^2=Z^(2*d) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
        congr 1
        push_cast
        ring
      have hquot : Z^(1-lengthCap-2*d)=Z^(1-lengthCap)/Z^(2*d) :=
        Real.rpow_sub hZ _ _
      rw [mul_pow,hp,hquot]
      ring


end SevenEighths.ProbePhysical
end
end OAI

end LocalModule82
/- END analytic_low.PerturbedNominalGeometry -/

/- BEGIN original module analytic_low.PerturbedNominalEnergy -/
section LocalModule83

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem perturbed_selected_nominal_energy (L : ℝ) (hL0 : 0≤ L) (hL1 : L≤1/5) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ L)
    (Ck b ε : ℝ) (hCk : 0< Ck) (hε : 0<ε) (hε1 : ε≤1) :
    ∃degree : ℕ,∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
    ∀(T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=> Disjoint (T i) (T j))→
      (∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))→
    ∀(J : Finset (Fin K))(R : Finset O),
      (∀z∈R,z≠0 ∧ elementNorm z≤ Ck*Z^(1-L-2*lowUnselectedLength ell J))→
    ∀X : ℝ,0< X→Z^(1+lowSelectedLength ell J-ε/2)≤ X→X≤ Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀(Y : Fin K→ℝ)(t : ℝ)(σ : RayRing),
      (∑z∈R,‖lowSelectedInverseRow Finset.univ
        (lowSelectedWeight η (fun i=> canonicalSlotSupport (T i)) J W Y t)
        η S hS (lowSelectedIdeal (fun i=> canonicalSlotSupport (T i)) J) X t σ z‖^2)≤
        C*(1+‖t‖)^degree*Z^((1-L-2*lowUnselectedLength ell J)+max (lowUnselectedLength ell J+5*L-1) 0/4+507*ε) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := perturbed_selected_physical_energy L hL0 hL1 η S hS hbad K Ck ε hCk hε hε1
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [eventually_low_selected_caps ell hell b ε hε,Filter.eventually_ge_atTop Z₀] with Z hc hZ
  refine ⟨hc.1,?_⟩
  intro T hT hout hdis hnorm J R hR X hX hXlo hXhi W hW Y t σ
  obtain ⟨hd,hd1,hs,hscap⟩ := perturbed_lowLength_bounds L ell hell hsum J
  have hscale := lowCentralShift_scale Z X (lowSelectedLength ell J+ε/2) hc.1 hX
  rw [←hscale]
  apply he Z (lowUnselectedLength ell J) (lowSelectedLength ell J+ε/2)
    (lowCentralShift Z X (lowSelectedLength ell J+ε/2)) hZ hd hd1 (by linarith) (by linarith)
    (lowCentralShift_bound Z X (lowSelectedLength ell J) ε hc.1 hX hε.le hXlo hXhi)
    R hR T hT hout hdis J (fun i=> max 1 (b*Z^(ell i.val)))
    (fun i=> le_max_left _ _)
    (fun i P hP=>(hnorm i.val P hP).trans (le_max_right _ _)) (hc.2 J) W hW Y t σ

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule83
/- END analytic_low.PerturbedNominalEnergy -/

/- BEGIN original module analytic_low.PerturbedInverseNormalize -/
section LocalModule84

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

lemma perturbed_low_inverse_power_cancel (lengthCap Z d α : ℝ) (hZ : 0< Z) :
    Z^(1-lengthCap-2*d+α)*(Z^d)^2/Z^(1-lengthCap)=Z^α := by
  have hp : (Z^d)^2=Z^(2*d) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
    congr 1
    push_cast
    ring
  rw [hp,←Real.rpow_add hZ,←Real.rpow_sub hZ]
  congr 1
  ring

lemma perturbed_low_inverse_sqrt_normalized (lengthCap q C B Z L d α H E : ℝ) (n : ℕ)
    (hq : 0< q) (hC : 0≤ C) (_hB : 0≤ B) (hZ : 0< Z) (hL : 0< L) (hH : 1≤ H)
    (hE : 0≤ E) (hEL : E≤ C*H^n*Z^(1-lengthCap-2*d+α)) (hLB : L≤ B*Z^d) :
    Real.sqrt E/Real.sqrt (q*Z^(1-lengthCap)/L^2)≤
      Real.sqrt (C*B^2/q)*H^n*Z^(α/2) := by
  have hratio : E/(q*Z^(1-lengthCap)/L^2)≤(C*B^2/q)*H^n*Z^α := by
    calc
      _≤(C*H^n*Z^(1-lengthCap-2*d+α))/(q*Z^(1-lengthCap)/L^2) :=
        div_le_div_of_nonneg_right hEL (by positivity)
      _=(C*H^n*Z^(1-lengthCap-2*d+α))*L^2/(q*Z^(1-lengthCap)) := by field_simp
      _≤(C*H^n*Z^(1-lengthCap-2*d+α))*(B*Z^d)^2/(q*Z^(1-lengthCap)) := by
        gcongr
      _=(C*B^2/q)*H^n*(Z^(1-lengthCap-2*d+α)*(Z^d)^2/Z^(1-lengthCap)) := by ring
      _=_ := by rw [perturbed_low_inverse_power_cancel lengthCap Z d α hZ]
  rw [←Real.sqrt_div hE]
  apply (Real.sqrt_le_sqrt hratio).trans
  rw [Real.sqrt_mul (by positivity),Real.sqrt_mul (by positivity)]
  have hp : Real.sqrt (Z^α)=Z^(α/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
    congr 1
    ring
  rw [hp]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_self_iff.mpr (Or.inr (one_le_pow₀ hH))) (by positivity)) (by positivity)

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule84
/- END analytic_low.PerturbedInverseNormalize -/

/- BEGIN original module analytic_low.PerturbedPhysicalInverseBound -/
section LocalModule85

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem perturbed_low_physical_inverse_normalized (lengthCap x y : ℝ) (hxy : x+y=1-lengthCap) (hL0 : 0≤ lengthCap) (hL1 : lengthCap≤1/5) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ lengthCap)
    (a b aCut bCut ε : ℝ) (ha : 0< a) (haCut : 0< aCut) (hbCut : 0< bCut)
    (hε : 0<ε) (hε1 : ε≤1) :
    ∃degree : ℕ,∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
    ∀(T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=> Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))→
    ∀(J : Finset (Fin K))(p : LowUnselectedTuple (fun i=> canonicalSlotSupport (T i)) J),
    ∀X : ℝ,0< X→Z^(1+lowSelectedLength ell J-ε/2)≤ X→X≤ Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀t : ℝ,
      let L := elementNorm (∏i : J,(p i).val)
      let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(x)/L) (Z^(y)/L)
      ∀(hX0 : 0< Z^(x)/L)(hY0 : 0< Z^(y)/L),
      (Real.sqrt Q)⁻¹/(2*Real.pi)*
        lowInverseMass (calibrationForSet S hS) aCut bCut haCut hbCut
          (Z^(x)/L) (Z^(y)/L) hX0 hY0
          (lowSelectedInverseRow Finset.univ
            (lowSelectedWeight η (fun i=> canonicalSlotSupport (T i)) J W (fun i=> Z^(ell i)) t)
            η S hS (lowSelectedIdeal (fun i=> canonicalSlotSupport (T i)) J) X t)≤
        C*(1+‖t‖)^degree*Z^(max (lowUnselectedLength ell J+5*lengthCap-1) 0/8+507*ε/2) := by
  let q := elementNorm (calibrationForSet S hS).generator
  let c := (min 1 a)^K
  let B := (max 1 b)^K
  have hq : 0< q := calibration_elementNorm_pos _
  have hc : 0< c := by dsimp [c];positivity
  have hB : 0< B := by dsimp [B];positivity
  let Ck := 2*bCut*(q/c^2)
  have hCk : 0< Ck := by dsimp [Ck];positivity
  obtain ⟨degree,C,ZC,hbound⟩ := perturbed_selected_nominal_energy lengthCap hL0 hL1 η S hS hbad ell hell hsum Ck b ε hCk hε hε1
  let C0 := ((Fintype.card RayRing:ℝ)+1)*Real.sqrt (C*B^2/q)/(2*Real.pi)
  have hC0 : 0< C0 := by dsimp [C0];positivity
  refine ⟨degree,C0,hC0,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T hT hout hdis hnorm J p X hX hXlo hXhi W hW t
  dsimp only
  let L := elementNorm (∏i : J,(p i).val)
  let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(x)/L) (Z^(y)/L)
  intro hX0 hY0
  have hz : 0< Z := lt_trans zero_lt_one hZ.1
  have hL : 0< L := lowUnselectedProduct_norm_pos _
    (fun i n hn=> canonicalSlotSupport_nonzero _ (hT i) n hn) J p
  have hnormE (i : Fin K) (n : O) (hn : n∈canonicalSlotSupport (T i)) :
      a*Z^(ell i)≤ elementNorm n ∧ elementNorm n≤ b*Z^(ell i) := by
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact hnorm i P hP
  have hLlo : c*Z^(lowUnselectedLength ell J)≤ L :=
    lowUnselectedProduct_norm_lower ell a Z ha hz _ (fun i n hn=>(hnormE i n hn).1) J p
  have hLhi : L≤ B*Z^(lowUnselectedLength ell J) :=
    lowUnselectedProduct_norm_upper_nominal ell b Z hz _ (fun i n hn=>(hnormE i n hn).2) J p
  have hQ : 0< Q := lowPhysicalScale_pos _ _ _ hX0 hY0
  let R := lowNumeratorRows aCut bCut haCut hbCut Q hQ
  let row := lowSelectedInverseRow Finset.univ
    (lowSelectedWeight η (fun i=> canonicalSlotSupport (T i)) J W (fun i=> Z^(ell i)) t)
    η S hS (lowSelectedIdeal (fun i=> canonicalSlotSupport (T i)) J) X t
  have hrows : ∀z∈R,z≠0 ∧ elementNorm z≤ Ck*Z^(1-lengthCap-2*lowUnselectedLength ell J) := by
    intro z hzR
    refine ⟨lowNumeratorRows_nonzero aCut bCut haCut hbCut Q hQ z hzR,?_⟩
    apply (lowNumeratorRows_norm_bound aCut bCut haCut hbCut Q hQ z hzR).trans
    have hh := mul_le_mul_of_nonneg_left
      (perturbed_lowPhysicalScale_nominal_bound lengthCap x y hxy (calibrationForSet S hS) Z L c (lowUnselectedLength ell J) hz hc hLlo)
      (show 0≤2*bCut by positivity)
    simpa only [Ck,mul_assoc] using hh
  have he (σ : RayRing) : (∑z∈R,‖row σ z‖^2)≤
      C*(1+‖t‖)^degree*Z^(1-lengthCap-2*lowUnselectedLength ell J+max (lowUnselectedLength ell J+5*lengthCap-1) 0/4+507*ε) :=
    hZ.2 T hT hout hdis (fun i P hP=>(hnorm i P hP).2) J R hrows X hX hXlo hXhi W hW (fun i=> Z^(ell i)) t σ
  have hn (σ : RayRing) : Real.sqrt (∑z∈R,‖row σ z‖^2)/Real.sqrt Q≤
      Real.sqrt (C*B^2/q)*(1+‖t‖)^degree*Z^(max (lowUnselectedLength ell J+5*lengthCap-1) 0/8+507*ε/2) := by
    dsimp only [Q]
    rw [perturbed_lowPhysicalScale_source lengthCap x y hxy _ Z L hz]
    convert perturbed_low_inverse_sqrt_normalized lengthCap q C B Z L (lowUnselectedLength ell J) (max (lowUnselectedLength ell J+5*lengthCap-1) 0/4+507*ε) (1+‖t‖)
      (∑z∈R,‖row σ z‖^2) degree hq ZC.le hB.le hz hL (le_add_of_nonneg_right (norm_nonneg t))
      (Finset.sum_nonneg (fun _ _=> sq_nonneg _)) (by simpa only [add_assoc] using he σ) hLhi using 1
    congr 1
    ring
  change (Real.sqrt Q)⁻¹/(2*Real.pi)*(∑σ : RayRing,Real.sqrt (∑z∈R,‖row σ z‖^2))≤_
  calc
    _=(∑σ : RayRing,Real.sqrt (∑z∈R,‖row σ z‖^2)/Real.sqrt Q)/(2*Real.pi) := by
      rw [←Finset.sum_div]
      ring
    _≤(∑σ : RayRing,Real.sqrt (C*B^2/q)*(1+‖t‖)^degree*Z^(max (lowUnselectedLength ell J+5*lengthCap-1) 0/8+507*ε/2))/(2*Real.pi) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun σ _=> hn σ)) (by positivity)
    _≤_ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      dsimp [C0]
      calc
        _=((Fintype.card RayRing:ℝ)*Real.sqrt (C*B^2/q)/(2*Real.pi))*(1+|t|)^degree*Z^(max (lowUnselectedLength ell J+5*lengthCap-1) 0/8+507*ε/2) := by ring
        _≤_ := by gcongr ; linarith

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule85
/- END analytic_low.PerturbedPhysicalInverseBound -/

/- BEGIN original module analytic_low.PerturbedSourceScales -/
section LocalModule86

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

lemma perturbed_source_gram_power (Z δ : ℝ) (hZ : 0< Z) :
    Z^(21247/60000:ℝ)*(Z^(1/8:ℝ))^(1/6:ℝ)*(Z^(28747/60000:ℝ))^δ=
      Z^(7499/20000+(28747/60000)*δ:ℝ) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

lemma perturbed_source_gram_sqrt_power (Z δ : ℝ) (hZ : 0< Z) :
    Real.sqrt (Z^(7499/20000+(28747/60000)*δ:ℝ))=Z^(7499/40000+(28747/120000)*δ:ℝ) := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
  congr 1
  ring

lemma perturbed_source_scale_ratio (Z : ℝ) (hZ : 0< Z) :
    Z^(28747/60000:ℝ)/Z^(21247/60000:ℝ)=Z^(1/8:ℝ) := by
  rw [←Real.rpow_sub hZ]
  norm_num

lemma perturbed_source_scale_square (Z : ℝ) (hZ : 0< Z) :
    Z^(13747/60000:ℝ)*Z^(28747/60000:ℝ)=(Z^(21247/60000:ℝ))^2 := by
  rw [←Real.rpow_add hZ,←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  norm_num

lemma perturbed_source_compensated_scale_admissible (q Z L : ℝ) (hq : 1≤ q) (hZ : 1≤ Z)
    (hL : 1≤ L) (hql : q≤ Z^(1/8:ℝ)) (hLl : L≤ Z^(13747/60000:ℝ)) :
    1≤ Z^(28747/60000:ℝ)/L ∧
    q*Z^(21247/60000:ℝ)≤ Z^(28747/60000:ℝ) ∧
    L*Z^(28747/60000:ℝ)≤ q^2*(Z^(21247/60000:ℝ))^2 := by
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0< L := lt_of_lt_of_le zero_lt_one hL
  constructor
  · apply (le_div_iff₀ hl).mpr
    simpa using hLl.trans (Real.rpow_le_rpow_of_exponent_le hZ (show (13747/60000:ℝ)≤28747/60000 by norm_num))
  constructor
  · apply (le_div_iff₀ (Real.rpow_pos_of_pos hz (21247/60000))).mp
    rwa [perturbed_source_scale_ratio Z hz]
  · calc
      _≤ Z^(13747/60000:ℝ)*Z^(28747/60000:ℝ) := mul_le_mul_of_nonneg_right hLl (by positivity)
      _=(Z^(21247/60000:ℝ))^2 := perturbed_source_scale_square Z hz
      _≤_ := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq)

lemma perturbed_source_compensated_gram_scale (q Z L δ : ℝ) (hq : 1≤ q) (hZ : 1≤ Z)
    (hL : 1≤ L) (hql : q≤ Z^(1/8:ℝ)) (hLl : L≤ Z^(13747/60000:ℝ)) (hδ : 0≤δ) :
    (q*(Z^(21247/60000:ℝ)/L)*(Z^(28747/60000:ℝ)/L)/(Z^(28747/60000:ℝ)/L))*
      (1+((Z^(28747/60000:ℝ)/L)^2/(q*(Z^(21247/60000:ℝ)/L)*(Z^(28747/60000:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(28747/60000:ℝ)/L)^2/(q*(Z^(21247/60000:ℝ)/L)*(Z^(28747/60000:ℝ)/L)))^2/(Z^(28747/60000:ℝ)/L))*
      (Z^(28747/60000:ℝ)/L)^δ ≤
        (3*q/L)*Z^(7499/20000+(28747/60000)*δ:ℝ) := by
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hq0 : 0< q := lt_of_lt_of_le zero_lt_one hq
  have hL0 : 0< L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨_,hqp,ht⟩ := perturbed_source_compensated_scale_admissible q Z L hq hZ hL hql hLl
  have hb := compensated_gram_scale_bound q (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) L δ hq0
    (by positivity) (by positivity) hL hδ hqp ht
  apply hb.trans
  have hratio : Z^(28747/60000:ℝ)/(q*Z^(21247/60000:ℝ))≤ Z^(1/8:ℝ) := by
    rw [←perturbed_source_scale_ratio Z hz]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_mul_of_one_le_left (by positivity) hq)
  have hp := Real.rpow_le_rpow (by positivity : 0≤ Z^(28747/60000:ℝ)/(q*Z^(21247/60000:ℝ))) hratio (show 0≤(1/6:ℝ) by norm_num)
  calc
    _≤3*(q*Z^(21247/60000:ℝ)/L)*(Z^(1/8:ℝ))^(1/6:ℝ)*(Z^(28747/60000:ℝ))^δ := by gcongr
    _=(3*q/L)*(Z^(21247/60000:ℝ)*(Z^(1/8:ℝ))^(1/6:ℝ)*(Z^(28747/60000:ℝ))^δ) := by ring
    _=_ := by rw [perturbed_source_gram_power Z δ hz]

lemma perturbed_source_compensated_gram_sqrt (q Z L δ : ℝ) (hq : 1≤ q) (hZ : 1≤ Z)
    (hL : 1≤ L) (hql : q≤ Z^(1/8:ℝ)) (hLl : L≤ Z^(13747/60000:ℝ)) (hδ : 0≤δ) :
    Real.sqrt ((q*(Z^(21247/60000:ℝ)/L)*(Z^(28747/60000:ℝ)/L)/(Z^(28747/60000:ℝ)/L))*
      (1+((Z^(28747/60000:ℝ)/L)^2/(q*(Z^(21247/60000:ℝ)/L)*(Z^(28747/60000:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(28747/60000:ℝ)/L)^2/(q*(Z^(21247/60000:ℝ)/L)*(Z^(28747/60000:ℝ)/L)))^2/(Z^(28747/60000:ℝ)/L))*
      (Z^(28747/60000:ℝ)/L)^δ) ≤
        Real.sqrt (3*q/L)*Z^(7499/40000+(28747/120000)*δ:ℝ) := by
  apply (Real.sqrt_le_sqrt (perturbed_source_compensated_gram_scale q Z L δ hq hZ hL hql hLl hδ)).trans_eq
  rw [Real.sqrt_mul (by positivity),perturbed_source_gram_sqrt_power Z δ (lt_of_lt_of_le zero_lt_one hZ)]

lemma perturbed_lowGramFactor_source_bound (C : CalibrationData) (Z L δ : ℝ) (hZ : 1≤ Z)
    (hL : 1≤ L) (hql : elementNorm C.generator≤ Z^(1/8:ℝ))
    (hLl : L≤ Z^(13747/60000:ℝ)) (hδ : 0≤δ) :
    lowGramFactor C (Z^(21247/60000:ℝ)/L) (Z^(28747/60000:ℝ)/L) δ≤
      Real.sqrt (3*elementNorm C.generator/L)*Z^(7499/40000+(28747/120000)*δ:ℝ) :=
  perturbed_source_compensated_gram_sqrt _ Z L δ (calibration_elementNorm_ge_one C) hZ hL hql hLl hδ

lemma perturbed_eventually_compensated_source_scales (C : CalibrationData) (B : ℝ) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤ Z ∧ elementNorm C.generator≤ Z^(1/8:ℝ) ∧
      ∀L : ℝ,1≤ L→L≤ B*Z^(5003/30000:ℝ)→
        1≤ Z^(28747/60000:ℝ)/L ∧
        1≤(Z^(28747/60000:ℝ)/L)^2/lowPhysicalScale C (Z^(21247/60000:ℝ)/L) (Z^(28747/60000:ℝ)/L) ∧
        ∀δ : ℝ,0≤δ→lowGramFactor C (Z^(21247/60000:ℝ)/L) (Z^(28747/60000:ℝ)/L) δ≤
          Real.sqrt (3*elementNorm C.generator/L)*Z^(7499/40000+(28747/120000)*δ:ℝ) := by
  have hq := (tendsto_rpow_atTop (show 0<(1/8:ℝ) by norm_num)).eventually
    (Filter.eventually_ge_atTop (elementNorm C.generator))
  have hb := (tendsto_rpow_atTop (show 0<(1241/20000:ℝ) by norm_num)).eventually
    (Filter.eventually_ge_atTop B)
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ),hq,hb] with Z hZ hq hb
  refine ⟨hZ,hq,?_⟩
  intro L hL hLB
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0< L := lt_of_lt_of_le zero_lt_one hL
  have hLl : L≤ Z^(13747/60000:ℝ) := calc
    L≤ B*Z^(5003/30000:ℝ) := hLB
    _≤ Z^(1241/20000:ℝ)*Z^(5003/30000:ℝ) := mul_le_mul_of_nonneg_right hb (by positivity)
    _=Z^(13729/60000:ℝ) := by rw [←Real.rpow_add hz];norm_num
    _≤ Z^(13747/60000:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)
  obtain ⟨hy,hp,_⟩ := perturbed_source_compensated_scale_admissible _ Z L (calibration_elementNorm_ge_one C) hZ hL hq hLl
  refine ⟨hy,?_,fun δ hδ=> perturbed_lowGramFactor_source_bound C Z L δ hZ hL hq hLl hδ⟩
  rw [lowPhysicalScale,compensated_gram_ratio _ _ _ _ (calibration_elementNorm_pos C)
    (by positivity) (by positivity) hl]
  exact (le_div_iff₀ (mul_pos (calibration_elementNorm_pos C) (by positivity))).mpr (by simpa using hp)

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule86
/- END analytic_low.PerturbedSourceScales -/

/- BEGIN original module analytic_low.PerturbedSlotScales -/
section LocalModule87

namespace OAI
noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss
local notation "O" => ActualEisensteinCubic.O

lemma perturbed_lowUnselectedProduct_norm_bound {K : ℕ} (ell : Fin K→ℝ)
    (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤5003/30000)
    (b Z : ℝ) (hb : 1≤ b) (hZ : 1≤ Z) (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→elementNorm x≤ b*Z^(ell i))
    (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) :
    elementNorm (∏i : J,(a i).val)≤ b^K*Z^(5003/30000:ℝ) := by
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hsub : ∑i∈J,ell i≤5003/30000 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=> hell i)).trans hsum
  have hc : J.card≤ K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤∏i : J,b*Z^(ell i.val) := Finset.prod_le_prod₀ (fun _ _=> by unfold elementNorm;positivity)
      (fun i _=> hslots i.val _ (a i).property)
    _=b^J.card*Z^(∑i∈J,ell i) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hz,Finset.sum_coe_sort]
    _≤ b^K*Z^(5003/30000:ℝ) := mul_le_mul (pow_le_pow_right₀ hb hc)
      (Real.rpow_le_rpow_of_exponent_le hZ hsub) (by positivity) (by positivity)

theorem perturbed_eventually_original_slot_scales {K : ℕ} (C : CalibrationData) (ell : Fin K→ℝ)
    (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤5003/30000) (b : ℝ) (hb : 1≤ b) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤ Z ∧
      ∀(slots : Fin K→Finset O)(_hslots : ∀i x,x∈slots i→x≠0),
      (∀i x,x∈slots i→elementNorm x≤ b*Z^(ell i))→
      ∀(J : Finset (Fin K))(a : LowUnselectedTuple slots J),
      let L := elementNorm (∏i : J,(a i).val)
      1≤ Z^(28747/60000:ℝ)/L ∧
      1≤(Z^(28747/60000:ℝ)/L)^2/lowPhysicalScale C (Z^(21247/60000:ℝ)/L) (Z^(28747/60000:ℝ)/L) ∧
      ∀δ : ℝ,0≤δ→lowGramFactor C (Z^(21247/60000:ℝ)/L) (Z^(28747/60000:ℝ)/L) δ≤
        Real.sqrt (3*elementNorm C.generator/L)*Z^(7499/40000+(28747/120000)*δ:ℝ) := by
  filter_upwards [perturbed_eventually_compensated_source_scales C (b^K)] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro slots hslots hnorm J a
  exact hZ.2.2 _ (lowUnselectedProduct_norm_ge_one slots hslots J a)
    (perturbed_lowUnselectedProduct_norm_bound ell hell hsum b Z hb hZ.1 slots hnorm J a)

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule87
/- END analytic_low.PerturbedSlotScales -/

/- BEGIN original module analytic_low.PerturbedUnselectedMass -/
section LocalModule88

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "SupportedIdeal" => {I : Ideal O // Supported I}

lemma perturbed_canonical_slot_three_halves : ∃C : ℝ,0< C ∧
    ∀(T : Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)(_hT : ∀P∈T,Supported P.val),
      (∑a : canonicalSlotSupport T,elementNorm a.val^(-(3/2:ℝ)))≤ C := by
  obtain ⟨C,hC,hb⟩ := ProbeGramCommon.supportedIdeal_rpow_finite_bound (-(3/2)) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro T hT
  let f : T→SupportedIdeal := fun P=>⟨P.val.val,hT P.val P.property⟩
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun I : SupportedIdeal=> I.val) h
  have he : (∑a : canonicalSlotSupport T,elementNorm a.val^(-(3/2:ℝ)))=
      ∑I∈Finset.univ.image f,ProbeGramCommon.gramIdealNorm I^(-(3/2:ℝ)) := by
    rw [Finset.sum_image (fun P _ Q _ h=> hf h)]
    have hh := (canonicalSlotEquiv T hT).sum_comp (fun a=> elementNorm a.val^(-(3/2:ℝ)))
    rw [←hh]
    apply Finset.sum_congr rfl
    intro P hP
    rw [canonicalSlotEquiv_norm]
    rfl
  rw [he]
  exact hb _

lemma perturbed_lowUnselectedWeight_norm_identity {K : ℕ} (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (a : LowUnselectedTuple slots J) :
    ‖lowUnselectedWeight slots J W P a‖*elementNorm (∏i : J,(a i).val)^(0:ℝ)=
      ∏i : J,elementNorm (a i).val^(-(3/2:ℝ))*‖W i.val (elementNorm (a i).val/P i.val)‖ := by
  have hL := lowUnselectedProduct_norm_pos slots hslots J a
  rw [lowUnselectedWeight,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hL.le _),norm_prod]
  calc
    _=(elementNorm (∏i : J,(a i).val)^(-(3/2:ℝ))*elementNorm (∏i : J,(a i).val)^(0:ℝ))*
        ∏i : J,‖W i.val (elementNorm (a i).val/P i.val)‖ := by ring
    _=elementNorm (∏i : J,(a i).val)^(-(3/2:ℝ))*∏i : J,‖W i.val (elementNorm (a i).val/P i.val)‖ := by
      rw [←Real.rpow_add hL]
      norm_num
    _=_ := by
      rw [elementNorm_finset_prod,Finset.prod_mul_distrib,Real.finsetProd_rpow Finset.univ
        (fun i : J=> elementNorm (a i).val) (fun i _=> by unfold elementNorm;positivity)]

theorem perturbed_lowUnselectedMass_bound (K : ℕ) (M : ℝ) (hM : 0≤ M) :
    ∃C : ℝ,0< C ∧ ∀(T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)(_hT : ∀i P,P∈T i→Supported P.val)
      (J : Finset (Fin K))(W : Fin K→ℝ→ℂ)(P : Fin K→ℝ),
      (∀i x,‖W i x‖≤ M)→
      (∑a : LowUnselectedTuple (fun i=> canonicalSlotSupport (T i)) J,
        ‖lowUnselectedWeight (fun i=> canonicalSlotSupport (T i)) J W P a‖*
          elementNorm (∏i : J,(a i).val)^(0:ℝ))≤ C := by
  obtain ⟨C,hC,hb⟩ := perturbed_canonical_slot_three_halves
  refine ⟨(max 1 (C*M))^K,by positivity,?_⟩
  intro T hT J W P hW
  simp_rw [perturbed_lowUnselectedWeight_norm_identity _ (fun i=> canonicalSlotSupport_nonzero _ (hT i))]
  rw [←Fintype.prod_sum (fun (i : J) (a : canonicalSlotSupport (T i.val))=>
    elementNorm a.val^(-(3/2:ℝ))*‖W i.val (elementNorm a.val/P i.val)‖)]
  calc
    _≤∏i : J,C*M := by
      apply Finset.prod_le_prod₀ (fun i _=> Finset.sum_nonneg (fun a _=> mul_nonneg (Real.rpow_nonneg (by unfold elementNorm;positivity) _) (norm_nonneg _)))
      intro i hi
      calc
        _≤∑a : canonicalSlotSupport (T i.val),elementNorm a.val^(-(3/2:ℝ))*M := by
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left (hW i.val _) (Real.rpow_nonneg (by unfold elementNorm;positivity) _)
        _=(∑a : canonicalSlotSupport (T i.val),elementNorm a.val^(-(3/2:ℝ)))*M := (Finset.sum_mul ..).symm
        _≤ C*M := mul_le_mul_of_nonneg_right (hb _ (hT i.val)) hM
    _≤∏_i : J,max 1 (C*M) := Finset.prod_le_prod₀ (fun _ _=> by positivity) (fun _ _=> le_max_right _ _)
    _≤_ := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_coe]
      exact pow_le_pow_right₀ (le_max_left _ _) (by simpa using Finset.card_le_card (Finset.subset_univ J))

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule88
/- END analytic_low.PerturbedUnselectedMass -/

/- BEGIN original module analytic_low.CompensationPower -/
section LocalModule89

namespace OAI.SevenEighths.ProbePhysical

lemma perturbed_compensation_factor (L Z R c d : ℝ)
    (hL : L≤1/5) (hZ : 1≤ Z) (hc : 0< c) (hd : 0≤ d)
    (hR : c*Z^d≤ R) :
    R^(-(1/2:ℝ))*Z^(max (d+5*L-1) 0/8)≤ c^(-(1/2:ℝ)) := by
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hb : 0< c*Z^d := mul_pos hc (Real.rpow_pos_of_pos hz _)
  have hm : max (d+5*L-1) 0/8≤ d/2 := by
    have hh : max (d+5*L-1) 0≤ d := max_le (by linarith) hd
    linarith
  calc
    _≤(c*Z^d)^(-(1/2:ℝ))*Z^(d/2) := by
      apply mul_le_mul
      · exact Real.rpow_le_rpow_of_nonpos hb hR (by norm_num)
      · exact Real.rpow_le_rpow_of_exponent_le hZ hm
      · positivity
      · positivity
    _=c^(-(1/2:ℝ)) := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg hz.le _),←Real.rpow_mul hz.le]
      rw [mul_assoc,←Real.rpow_add hz]
      have he : d*(-(1/2:ℝ))+d/2=0 := by ring
      rw [he,Real.rpow_zero,mul_one]

end OAI.SevenEighths.ProbePhysical

end LocalModule89
/- END analytic_low.CompensationPower -/

/- BEGIN original module analytic_low.PerturbedCentralTuple -/
section LocalModule90

namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma perturbed_compensated_sqrt_factor (q L : ℝ) (hq : 0≤ q) (hL : 0< L) :
    Real.sqrt (3*q/L)=Real.sqrt (3*q)*L^(-(1/2:ℝ)) := by
  rw [Real.sqrt_div (by positivity)]
  simp only [div_eq_mul_inv,Real.sqrt_eq_rpow,Real.rpow_neg hL.le]

theorem perturbed_low_central_compensated_tuple (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤5003/30000)
    (a b ε : ℝ) (ha : 0< a) (hε : 0<ε) (hε1 : ε<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hab1 : a1< b1) (hM : 0≤ M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤ M) :
    ∃degree : ℕ,∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
    ∀(T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=> Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))→
    ∀(J : Finset (Fin K))(X : ℝ),0< X→
      Z^(1+lowSelectedLength ell J-ε/2)≤ X→X≤ Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀t : ℝ,
      ‖∑p : ∀i,canonicalSlotSupport (T i),
        compensationSubsetWeight η W (fun i=> Z^(ell i)) (fun i=>(p i).val) J*
          compensationRowTest η (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) J
            (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) X t*
          selectedSlotFactor W (fun i=> Z^(ell i)) (fun i=>(p i).val) J t‖≤
        C*(1+‖t‖)^degree*Z^(7499/40000+254*ε) := by
  obtain ⟨Cg,hCg,hgram⟩ := compensation_tuple_actual_gram ε hε hε1 W0 W1
    a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM S hS hbad
  obtain ⟨degree,Ci,hCi,hinverse⟩ := perturbed_low_physical_inverse_normalized (5003/30000) (21247/60000) (28747/60000) (by norm_num) (by norm_num) (by norm_num) η S hS hbad ell hell hsum
    a b (a0*a1) (max 1 (b0*b1)) ε ha (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hε hε1.le
  obtain ⟨Cu,hCu,hmass⟩ := perturbed_lowUnselectedMass_bound K 1 (by norm_num)
  let q := elementNorm (calibrationForSet S hS).generator
  have hq : 0< q := calibration_elementNorm_pos _
  let c := (min 1 a)^K
  have hc : 0< c := by dsimp [c];positivity
  let C0 := Cg*Ci*Real.sqrt (3*q)*c^(-(1/2:ℝ))*Cu
  have hC0 : 0< C0 := by dsimp [C0];positivity
  refine ⟨degree,C0,hC0,?_⟩
  filter_upwards [hinverse,perturbed_eventually_original_slot_scales (calibrationForSet S hS)
    ell hell hsum (max 1 b) (le_max_left _ _)] with Z hInv hScale
  refine ⟨hInv.1,?_⟩
  intro T hT hout hdis hnorm J X hX hXlo hXhi W hW t
  let slots := fun i=> canonicalSlotSupport (T i)
  let Yp := fun i=> Z^(ell i)
  have hz : 0< Z := lt_trans zero_lt_one hInv.1
  have hslots : ∀i n,n∈slots i→n≠0 := fun i=> canonicalSlotSupport_nonzero _ (hT i)
  have hnormE : ∀i n,n∈slots i→elementNorm n≤ max 1 b*Z^(ell i) := by
    intro i n hn
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact (hnorm i P hP).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hs := hScale.2 slots hslots hnormE J
  have hg := hgram K η slots hslots J W Yp (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) X t
    (by positivity) (by positivity) hX (fun p=>(hs p).1) (fun p=>(hs p).2.1)
  apply hg.trans
  let G := Z^(7499/40000+(28747/120000)*ε:ℝ)
  let correction := max (lowUnselectedLength ell J+5*(5003/30000:ℝ)-1) 0/8
  let V := Ci*(1+‖t‖)^degree*Z^(correction+507*ε/2)
  have hGV : G*V≤ Ci*(1+‖t‖)^degree*Z^(7499/40000+254*ε+correction) := by
    dsimp only [G,V]
    calc
      _=Ci*(1+‖t‖)^degree*(Z^(7499/40000+(28747/120000)*ε:ℝ)*Z^(correction+507*ε/2)) := by ring
      _≤_ := by
        rw [←Real.rpow_add hz]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hInv.1.le (by linarith)
  have hterm (p : LowUnselectedTuple slots J) :
      let L := elementNorm (∏i : J,(p i).val)
      let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(21247/60000:ℝ)/L) (Z^(28747/60000:ℝ)/L)
      ‖lowUnselectedWeight slots J W Yp p‖*((Real.sqrt Q)⁻¹/(2*Real.pi))*
        lowGramFactor (calibrationForSet S hS) (Z^(21247/60000:ℝ)/L) (Z^(28747/60000:ℝ)/L) ε*
        lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
          (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
          (Z^(21247/60000:ℝ)/L) (Z^(28747/60000:ℝ)/L)
          (div_pos (by positivity) (lowUnselectedProduct_norm_pos slots hslots J p))
          (div_pos (by positivity) (lowUnselectedProduct_norm_pos slots hslots J p))
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t)
            η S hS (lowSelectedIdeal slots J) X t)≤
      (Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*Z^(7499/40000+254*ε))*c^(-(1/2:ℝ))*
        (‖lowUnselectedWeight slots J W Yp p‖*L^(0:ℝ)) := by
    dsimp only
    let L := elementNorm (∏i : J,(p i).val)
    let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(21247/60000:ℝ)/L) (Z^(28747/60000:ℝ)/L)
    have hL := lowUnselectedProduct_norm_pos slots hslots J p
    have hgb := (hs p).2.2 ε hε.le
    have hib := hInv.2 T hT hout hdis hnorm J p X hX hXlo hXhi W hW t
      (div_pos (by positivity) hL) (div_pos (by positivity) hL)
    have hgn : 0≤ lowGramFactor (calibrationForSet S hS) (Z^(21247/60000:ℝ)/L) (Z^(28747/60000:ℝ)/L) ε := Real.sqrt_nonneg _
    have hh := mul_le_mul_of_nonneg_left hib
      (mul_nonneg (norm_nonneg (lowUnselectedWeight slots J W Yp p)) hgn)
    have hh2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgb (norm_nonneg (lowUnselectedWeight slots J W Yp p)))
      (show 0≤ V by dsimp [V];positivity)
    calc
      _=‖lowUnselectedWeight slots J W Yp p‖*
        lowGramFactor (calibrationForSet S hS) (Z^(21247/60000:ℝ)/L) (Z^(28747/60000:ℝ)/L) ε*
        (Real.sqrt Q)⁻¹/(2*Real.pi)*
        lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
          (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (Z^(21247/60000:ℝ)/L) (Z^(28747/60000:ℝ)/L)
          (div_pos (by positivity) hL) (div_pos (by positivity) hL)
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t) η S hS (lowSelectedIdeal slots J) X t) := by ring
      _≤(‖lowUnselectedWeight slots J W Yp p‖*Real.sqrt (3*q/L))*(G*V) := by
        have hh3 := hh.trans hh2
        simp only [G,V,div_eq_mul_inv,mul_assoc] at hh3 ⊢
        convert hh3 using 1 ; congr 7
      _≤(‖lowUnselectedWeight slots J W Yp p‖*Real.sqrt (3*q/L))*
          (Ci*(1+‖t‖)^degree*Z^(7499/40000+254*ε+correction)) :=
        mul_le_mul_of_nonneg_left hGV (by positivity)
      _≤_ := by
        have hnormlo : ∀i n,n∈slots i→a*Z^(ell i)≤ elementNorm n := by
          intro i n hn
          obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
          rw [primaryTuple_norm P (hT i P hP)]
          exact (hnorm i P hP).1
        have hLlo : c*Z^(lowUnselectedLength ell J)≤ L :=
          lowUnselectedProduct_norm_lower ell a Z ha hz slots hnormlo J p
        have hd := (perturbed_lowLength_bounds (5003/30000) ell hell hsum J).1
        have hf := perturbed_compensation_factor (5003/30000) Z L c (lowUnselectedLength ell J)
          (by norm_num) hInv.1.le hc hd hLlo
        rw [perturbed_compensated_sqrt_factor q L hq.le hL]
        rw [Real.rpow_add hz]
        have hh := mul_le_mul_of_nonneg_left hf
          (show 0≤ Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*Z^(7499/40000+254*ε)*‖lowUnselectedWeight slots J W Yp p‖ by positivity)
        simp only [Real.rpow_zero]
        convert hh using 1 <;> ring
  have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=Finset.univ) (fun p _=> hterm p)) hCg.le
  apply hh.trans
  rw [←Finset.mul_sum]
  have hm := hmass T hT J W Yp hW
  calc
    _≤ Cg*((Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*Z^(7499/40000+254*ε))*c^(-(1/2:ℝ))*Cu) := by gcongr
    _=_ := by dsimp [C0];ring

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule90
/- END analytic_low.PerturbedCentralTuple -/

/- BEGIN original module analytic_low.PerturbedGaussianDyad -/
section LocalModule91

namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem perturbed_low_central_gaussian_dyad (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤5003/30000)
    (a b ε : ℝ) (ha : 0< a) (hε : 0<ε) (hε1 : ε<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hab1 : a1< b1) (hM : 0≤ M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤ M) :
    ∃degree : ℕ,∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
    ∀(T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=> Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))→
    ∀(J : Finset (Fin K))(U : ℝ),0< U→
      Z^(1+lowSelectedLength ell J-ε/2)≤ U→U≤ Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
    ∀(V : SchwartzMap ℝ ℂ)(hV : HasCompactSupport (V:ℝ→ℂ)),
      ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=> canonicalSlotSupport (T i))
        W (fun i=> Z^(ell i)) J (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) U
          (Z^(1+lowSelectedLength ell J)) V hV‖≤
        C*Z^(7499/40000+254*ε)*gaussianJointMoment V hV degree (U/Z^(1+lowSelectedLength ell J)) := by
  obtain ⟨degree,C,hC,he⟩ := perturbed_low_central_compensated_tuple η S hS hbad ell hell hsum
    a b ε ha hε hε1 W0 W1 a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [he] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T hT hout hdis hnorm J U hU hlo hhi W hW V hV
  apply lowCommonDyad_norm_of_bound
  intro t
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hZ.2 T hT hout hdis hnorm J U hU hlo hhi W hW t

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule91
/- END analytic_low.PerturbedGaussianDyad -/

/- BEGIN original module analytic_low.PerturbedRemoteMass -/
section LocalModule92
namespace OAI
noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
lemma perturbed_canonicalTuple_count {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i)
    (hsum : ∑i,ell i≤5003/30000) (b Z : ℝ) (hZ : 1≤ Z)
    (T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (hnorm : ∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i)) :
    (Fintype.card (∀i,canonicalSlotSupport (T i)):ℝ)≤(128*max 1 b)^K*Z^(5003/30000:ℝ) := by
  rw [Fintype.card_pi,Nat.cast_prod]
  calc
    _≤∏i,128*(max 1 b*Z^(ell i)) := by
      apply Finset.prod_le_prod₀ (fun i _=> Nat.cast_nonneg _)
      intro i hi
      simp only [Fintype.card_coe]
      apply canonicalSlot_count _ (hT i) _
        (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hZ (hell i)))
      intro P hP
      exact (hnorm i P hP).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    _=(128*max 1 b)^K*Z^(∑i,ell i) := by
      simp_rw [←mul_assoc]
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
        ←Real.rpow_sum_of_pos (lt_of_lt_of_le zero_lt_one hZ)]
    _≤_ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hsum) (by positivity)

lemma perturbed_compensation_scale_mass_bound {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤5003/30000)
    (b Z : ℝ) (hZ : 1≤ Z) (T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)
    (hnorm : ∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (hW : ∀i x,‖W i x‖≤1) :
    gaussianPhysicalScaleMass C (Finset.univ : Finset (∀i,canonicalSlotSupport (T i)))
      (fun p=> compensationSubsetWeight η W (fun i=> Z^(ell i)) (fun i=>(p i).val) J)
      (fun p=> Z^(21247/60000:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun p=> Z^(28747/60000:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun i : SelectedSlot J=> W i.val)
      (fun p i=> elementNorm (p i.val).val/Z^(ell i.val))≤
        (elementNorm C.generator*(128*max 1 b)^K)*Z := by
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hp (p : ∀i,canonicalSlotSupport (T i)) (i : Fin K) : (p i).val≠0 :=
    canonicalSlotSupport_nonzero _ (hT i) _ (p i).property
  have hterm (p : ∀i,canonicalSlotSupport (T i)) :
      ‖compensationSubsetWeight η W (fun i=> Z^(ell i)) (fun i=>(p i).val) J‖*
        (∏i : SelectedSlot J,‖W i.val (elementNorm (p i.val).val/Z^(ell i.val))‖)*
        lowPhysicalScale C (Z^(21247/60000:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
          (Z^(28747/60000:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))≤
      elementNorm C.generator*Z^(24997/30000:ℝ) := by
    have hcoeff : ‖compensationSubsetWeight η W (fun i=> Z^(ell i)) (fun i=>(p i).val) J‖*
        (∏i : SelectedSlot J,‖W i.val (elementNorm (p i.val).val/Z^(ell i.val))‖)≤1 := (mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _=> norm_nonneg _)) (compensationSubsetWeight_norm_le_one η W hW _ _ (hp p) J)).trans (Finset.prod_le_one₀ (fun _ _=> norm_nonneg _) (fun (i : SelectedSlot J) _=> hW i.val _))
    have hL := slotProduct_norm_ge_one _ (hp p) J
    rw [perturbed_lowPhysicalScale_source (5003/30000) (21247/60000) (28747/60000) (by norm_num) C Z _ hz]
    rw [show (1-(5003/30000:ℝ))=24997/30000 by norm_num]
    apply (mul_le_of_le_one_left (by unfold elementNorm;positivity) hcoeff).trans
    exact div_le_self (by unfold elementNorm;positivity) (one_le_pow₀ hL)
  unfold gaussianPhysicalScaleMass
  apply (Finset.sum_le_sum (fun p _=> hterm p)).trans
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc := mul_le_mul_of_nonneg_right (perturbed_canonicalTuple_count ell hell hsum b Z hZ T hT hnorm)
    (show 0≤ elementNorm C.generator*Z^(24997/30000:ℝ) by unfold elementNorm;positivity)
  apply hc.trans_eq
  calc
    _=(elementNorm C.generator*(128*max 1 b)^K)*(Z^(5003/30000:ℝ)*Z^(24997/30000:ℝ)) := by ring
    _=_ := by rw [←Real.rpow_add hz];norm_num

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule92
/- END analytic_low.PerturbedRemoteMass -/

/- BEGIN original module analytic_low.PerturbedGaussianRemote -/
section LocalModule93

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma perturbed_eventually_low_physical_scales {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i)
    (hsum : ∑i,ell i≤5003/30000) (b : ℝ) :
    ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
      ∀(slots : Fin K→Finset O),(∀i x,x∈slots i→x≠0)→
      (∀i x,x∈slots i→elementNorm x≤ b*Z^(ell i))→
      ∀(J : Finset (Fin K))(p : ∀i,slots i),
      1≤ Z^(21247/60000:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J) ∧
      1≤ Z^(28747/60000:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J) := by
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (show 0<(11241/60000:ℝ) by norm_num)).eventually
      (Filter.eventually_ge_atTop ((max 1 b)^K))] with Z hZ hc
  refine ⟨hZ,?_⟩
  intro slots hn hnorm J p
  have hl : 0< elementNorm (slotProduct (fun i=>(p i).val) J) :=
    slotProduct_norm_pos _ (fun i=> hn i _ (p i).property) J
  have hb := perturbed_lowUnselectedProduct_norm_bound ell hell hsum (max 1 b) Z (le_max_left _ _) hZ.le
    slots (fun i n hm=>(hnorm i n hm).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
    J (fun i=> p i.val)
  rw [←slotProduct_subtype (fun i=>(p i).val) J] at hb
  have hLX : elementNorm (slotProduct (fun i=>(p i).val) J)≤ Z^(21247/60000:ℝ) := by
    apply hb.trans
    calc
      _≤ Z^(11241/60000:ℝ)*Z^(5003/30000:ℝ) := mul_le_mul_of_nonneg_right hc (by positivity)
      _=_ := by rw [←Real.rpow_add (lt_trans zero_lt_one hZ)];norm_num
  constructor
  · exact (one_le_div hl).mpr hLX
  · exact (one_le_div hl).mpr (hLX.trans
      (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)))

lemma perturbed_low_remote_power (Z ell ε : ℝ) (N : ℕ) (hZ : 1≤ Z) (hell : ell≤5003/30000)
    (hN : 9/2≤(ε/2)*(N:ℝ)) :
    Z*(Z^(1+ell))^2/(Z^(ε/2))^N≤ Z^(-1:ℝ) := by
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hsq : (Z^(1+ell))^2=Z^(2*(1+ell)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
    congr 1
    push_cast
    ring
  have hn : (Z^(ε/2))^N=Z^((ε/2)*(N:ℝ)) := by rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
  rw [hsq,hn,show Z*Z^(2*(1+ell))=Z^(1+2*(1+ell)) by rw [Real.rpow_add hz,Real.rpow_one],←Real.rpow_sub hz]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

theorem perturbed_low_remote_gaussian_dyads (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤5003/30000)
    (b ε : ℝ) (hε : 0<ε) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hB0 : 0≤ B0) (hB1 : 0≤ B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWB0 : ∀x,‖W0 x‖≤ B0) (hWB1 : ∀x,‖W1 x‖≤ B1) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
    ∀(η : HeckeFamily.Character)(T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=> if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then
        ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=> canonicalSlotSupport (T i))
          W (fun i=> Z^(ell i)) J (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength ell J)) V hV‖ else 0
      Summable f ∧ (∑'j : ℕ,f j)≤ C*Z^(-1:ℝ) := by
  have hep : 0<ε/2 := by linarith
  obtain ⟨N,hN⟩ := exists_nat_gt ((9/2:ℝ)/(ε/2))
  have hN' : (9/2:ℝ)≤(ε/2)*(N:ℝ) := by
    have hh := (div_lt_iff₀ hep).mp hN
    nlinarith
  obtain ⟨Cg,hCg,he⟩ := gaussianPhysicalFamily_remote_polynomial V hV N
    a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1
  let q := elementNorm (calibrationForSet S hS).generator
  let C0 := Cg*(q*(128*max 1 b)^K)
  have hq : 0< q := calibration_elementNorm_pos _
  refine ⟨C0,by dsimp [C0];positivity,?_⟩
  filter_upwards [perturbed_eventually_low_physical_scales ell hell hsum b] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro η T hT hnorm J W hW
  dsimp only [lowRemote]
  have hz : 0< Z := lt_trans zero_lt_one hZ.1
  have hslots : ∀i n,n∈canonicalSlotSupport (T i)→n≠0 := fun i=> canonicalSlotSupport_nonzero _ (hT i)
  have hnormE : ∀i n,n∈canonicalSlotSupport (T i)→elementNorm n≤ b*Z^(ell i) := by
    intro i n hn
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact hnorm i P hP
  have hs := hZ.2 _ hslots hnormE J
  have hh := he η S hS W0 W1
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0)
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    hW0 hW1 hWB0 hWB1 (Finset.univ : Finset (∀i,canonicalSlotSupport (T i)))
    (fun p=> compensationSubsetWeight η W (fun i=> Z^(ell i)) (fun i=>(p i).val) J)
    (fun p=> Ideal.span {slotProduct (fun i=>(p i).val) (Finset.univ\J)})
    (fun p=> Z^(21247/60000:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
    (fun p=> Z^(28747/60000:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
    (fun p _=>(hs p).1) (fun p _=>(hs p).2)
    (fun i : SelectedSlot J=> W i.val) (fun p i=> elementNorm (p i.val).val/Z^(ell i.val))
    (Z^(1+lowSelectedLength ell J)) (Z^(ε/2)) (by positivity) (Real.one_le_rpow hZ.1.le hep.le)
  simp only [←lowCommonDyad_eq_family] at hh
  refine ⟨?_,?_⟩
  · convert hh.1 using 1
    funext j
    split_ifs with h <;> simp_all only [ite_true, ite_false]
  · have hhFinal := hh.2.trans (show _≤ C0*Z^(-1:ℝ) from by
      have hm := perturbed_compensation_scale_mass_bound η (calibrationForSet S hS) ell hell hsum b Z hZ.1.le T hT hnorm J W hW
      calc
        _≤ Cg*((q*(128*max 1 b)^K)*Z)*(Z^(1+lowSelectedLength ell J))^2/(Z^(ε/2))^N := by gcongr
        _=C0*(Z*(Z^(1+lowSelectedLength ell J))^2/(Z^(ε/2))^N) := by dsimp [C0];ring
        _≤_ := mul_le_mul_of_nonneg_left (perturbed_low_remote_power Z (lowSelectedLength ell J) ε N hZ.1.le
          (by have hb := perturbed_lowLength_bounds (5003/30000) ell hell hsum J;linarith) hN') (by dsimp [C0];positivity))
    convert hhFinal using 1
    apply tsum_congr
    intro j
    split_ifs with h <;> simp_all only [ite_true, ite_false]

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule93
/- END analytic_low.PerturbedGaussianRemote -/

/- BEGIN original module analytic_low.PerturbedGaussianCentral -/
section LocalModule94

namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem perturbed_low_central_gaussian_dyads (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤5003/30000)
    (a b ε : ℝ) (ha : 0< a) (hε : 0<ε) (hε1 : ε<1)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hab1 : a1< b1) (hM : 0≤ M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤ M) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
    ∀(T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=> Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=> if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then 0 else
        ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=> canonicalSlotSupport (T i))
          W (fun i=> Z^(ell i)) J (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength ell J)) V hV‖
      Summable f ∧ (∑'j : ℕ,f j)≤ C*Z^(7499/40000+256*ε) := by
  obtain ⟨degree,C,hC,he⟩ := perturbed_low_central_gaussian_dyad η S hS hbad ell hell hsum
    a b ε ha hε hε1 W0 W1 a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM
  obtain ⟨Cm,hCm,hm⟩ := gaussianJointMoment_summed V hV degree ε hε
  refine ⟨C*Cm,mul_pos hC hCm,?_⟩
  filter_upwards [he] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T hT hout hdis hnorm J W hW
  let R := Z^(1+lowSelectedLength ell J)
  let f := fun j : ℕ=> if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then 0 else
    ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=> canonicalSlotSupport (T i))
      W (fun i=> Z^(ell i)) J (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) ((2:ℝ)^j) R V hV‖
  have hz : 0< Z := lt_trans zero_lt_one hZ.1
  obtain ⟨hsm,hmb⟩ := hm R (by dsimp [R];positivity)
  have hb (j : ℕ) : f j≤(C*Z^(7499/40000+254*ε))*
      (((2:ℝ)^j)^ε*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) := by
    dsimp only [f]
    split_ifs with hj
    · exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (gaussianJointMoment_nonneg V hV degree _))
    · obtain ⟨hlo,hhi⟩ := not_lowRemote_bounds Z (lowSelectedLength ell J) ε ((2:ℝ)^j) hz hj
      apply (hZ.2 T hT hout hdis hnorm J ((2:ℝ)^j) (by positivity) hlo hhi W hW V hV).trans
      have hp : 1≤((2:ℝ)^j)^ε := Real.one_le_rpow (one_le_pow₀ (by norm_num)) hε.le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact le_mul_of_one_le_left (gaussianJointMoment_nonneg V hV degree _) hp
  have hn (j : ℕ) : 0≤ f j := by dsimp [f];split_ifs <;> positivity
  have hsumf := Summable.of_nonneg_of_le hn hb (hsm.mul_left (C*Z^(7499/40000+254*ε)))
  refine ⟨hsumf,?_⟩
  calc
    _≤∑'j : ℕ,(C*Z^(7499/40000+254*ε))*(((2:ℝ)^j)^ε*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) :=
      hsumf.tsum_le_tsum hb (hsm.mul_left _)
    _=(C*Z^(7499/40000+254*ε))*(∑'j : ℕ,((2:ℝ)^j)^ε*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) := tsum_mul_left
    _≤(C*Z^(7499/40000+254*ε))*(Cm*R^ε) := mul_le_mul_of_nonneg_left hmb (by positivity)
    _≤_ := by
      dsimp only [R]
      rw [←Real.rpow_mul hz.le]
      calc
        _=(C*Cm)*(Z^(7499/40000+254*ε)*Z^((1+lowSelectedLength ell J)*ε)) := by ring
        _≤_ := by
          rw [←Real.rpow_add hz]
          apply mul_le_mul_of_nonneg_left _ (mul_pos hC hCm).le
          have hh := perturbed_lowLength_bounds (5003/30000) ell hell hsum J
          exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by nlinarith)

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule94
/- END analytic_low.PerturbedGaussianCentral -/

/- BEGIN original module analytic_low.PerturbedGaussianSum -/
section LocalModule95

namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem perturbed_low_all_gaussian_dyads (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤5003/30000)
    (a b ε : ℝ) (ha : 0< a) (hε : 0<ε) (hε1 : ε<1)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hab1 : a1< b1) (hB0 : 0≤ B0) (hB1 : 0≤ B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤ B0) (hWB1 : ∀x,‖W1 x‖≤ B1) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
    ∀(T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=> Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=> lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=> canonicalSlotSupport (T i))
          W (fun i=> Z^(ell i)) J (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength ell J)) V hV
      Summable f ∧ ‖∑'j : ℕ,f j‖≤ C*Z^(7499/40000+256*ε) := by
  obtain ⟨Cc,hCc,hcentral⟩ := perturbed_low_central_gaussian_dyads η S hS hbad ell hell hsum
    a b ε ha hε hε1 V hV W0 W1 a0 b0 a1 b1 B1 ha0 ha1 hab1 hB1 hW0 hW1 hW0s hW1s hWB1
  obtain ⟨Cr,hCr,hremote⟩ := perturbed_low_remote_gaussian_dyads S hS ell hell hsum b ε hε V hV
    W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1 hW0 hW1 hWB0 hWB1
  refine ⟨Cc+Cr,add_pos hCc hCr,?_⟩
  filter_upwards [hcentral,hremote] with Z hc hr
  refine ⟨hc.1,?_⟩
  intro T hT hout hdis hnorm J W hW
  have hc' := hc.2 T hT hout hdis hnorm J W hW
  have hr' := hr.2 η T hT (fun i P hP=>(hnorm i P hP).2) J W hW
  dsimp only at hc' hr' ⊢
  have hh := low_dyad_norm_split _ (fun j=> lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j)) hc'.1 hr'.1
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hp : Z^(-1:ℝ)≤ Z^(7499/40000+256*ε) := Real.rpow_le_rpow_of_exponent_le hc.1.le (by linarith)
  calc
    _≤ Cc*Z^(7499/40000+256*ε)+Cr*Z^(-1:ℝ) := add_le_add hc'.2 hr'.2
    _≤ Cc*Z^(7499/40000+256*ε)+Cr*Z^(7499/40000+256*ε) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hp hCr.le)
    _=_ := by ring

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule95
/- END analytic_low.PerturbedGaussianSum -/

/- BEGIN original module analytic_low.PerturbedCommonBound -/
section LocalModule96

namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem perturbed_compensatedPhysicalProbe_low (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤5003/30000)
    (a b ε : ℝ) (ha : 0< a) (hε : 0<ε) (hε1 : ε<1)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hab1 : a1< b1) (hB0 : 0≤ B0) (hB1 : 0≤ B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤ B0) (hWB1 : ∀x,‖W1 x‖≤ B1) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
    ∀(T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=> Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))→
      ‖compensatedPhysicalProbe η (calibrationForSet S hS) W0 W1
        (fun i=> canonicalSlotSupport (T i)) W (fun i=> Z^(ell i))
        (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z‖≤ C*Z^(7499/40000+256*ε) := by
  obtain ⟨V,hV,hbudget,hidentity⟩ := compensatedPhysicalProbe_common_gaussian W
    (fun _=>|Real.log a|+|Real.log b|) (fun _=> by positivity)
    (fun i=> low_window_log_support (W i) a b ha (hW i))
  choose C hC he using fun A : Finset (Fin K)=> perturbed_low_all_gaussian_dyads η S hS hbad ell hell hsum
    a b ε ha hε hε1 (V A) (hV A) W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  let C0 := (∑A∈(Finset.univ : Finset (Fin K)).powerset,C A)+1
  have hC0 : 0< C0 := by
    have hn := Finset.sum_nonneg (fun A (_ : A∈(Finset.univ : Finset (Fin K)).powerset)=>(hC A).le)
    dsimp only [C0]
    linarith
  refine ⟨C0,hC0,?_⟩
  filter_upwards [Filter.eventually_all.mpr he] with Z hZ
  have hz1 : 1< Z := (hZ ∅).1
  have hz : 0< Z := lt_trans zero_lt_one hz1
  refine ⟨hz1,?_⟩
  intro T hT hout hdis hnorm
  have hslots : ∀i n,n∈canonicalSlotSupport (T i)→n≠0 := fun i=> canonicalSlotSupport_nonzero _ (hT i)
  rw [hidentity η (calibrationForSet S hS) W0 W1
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0)
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    _ hslots (fun i=> Z^(ell i)) (fun i=> by positivity)
    (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z (by positivity) (by positivity) hz]
  apply (norm_sum_le _ _).trans
  have hterm (A : Finset (Fin K)) :
      ‖∑'j : ℕ,lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=> canonicalSlotSupport (T i)) W
        (fun i=> Z^(ell i)) A (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) ((2:ℝ)^j)
        (Z*∏i∈Finset.univ\A,Z^(ell i)) (V A) (hV A)‖≤ C A*Z^(7499/40000+256*ε) := by
    have hc : Z*(∏i∈Finset.univ\A,Z^(ell i))=Z^(1+lowSelectedLength ell A) := by
      rw [lowSelectedScale_product ell A Z hz,Real.rpow_add hz,Real.rpow_one]
    rw [hc]
    exact ((hZ A).2 T hT hout hdis hnorm A W hWnorm).2
  have hh := Finset.sum_le_sum (fun A (_ : A∈(Finset.univ : Finset (Fin K)).powerset)=> hterm A)
  apply hh.trans
  rw [←Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (by dsimp [C0];linarith) (Real.rpow_nonneg hz.le _)

theorem perturbed_original_ray_compensatedPhysicalProbe_low (η : HeckeFamily.Character)
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hinj : Function.Injective ell)
    (hsum : ∑i,ell i≤5003/30000) (R : Set Id)
    (a b ε : ℝ) (ha : 0< a) (hab : a≤ b) (hε : 0<ε) (hε1 : ε<1)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hab1 : a1< b1) (hB0 : 0≤ B0) (hB1 : 0≤ B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤ B0) (hWB1 : ∀x,‖W1 x‖≤ B1) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun i=> canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) W (fun i=> Z^(ell i))
        (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z‖≤ C*Z^(7499/40000+256*ε) := by
  obtain ⟨C,hC,he⟩ := perturbed_compensatedPhysicalProbe_low η S hmax hS.bad ell hell hsum
    a b ε ha hε hε1 W hW hWnorm W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  refine ⟨C,hC,?_⟩
  filter_upwards [he,ProbeRaySlots.power_pools_eventually_disjoint R S (fun _=> a) (fun _=> b) ell
    (fun _=> ha) (fun _=> hab) hinj] with Z hZ hd
  have hz : 0< Z := lt_trans zero_lt_one hZ.1
  apply hZ.2 _ (fun i=> ProbeRaySlots.pool_supported R S hS a b (Z^(ell i)))
    (fun i P hP=>((ProbeRaySlots.mem_pool R S a b (Z^(ell i)) P).mp hP).2.2.2)
    (fun i j hij=> hd i j hij)
  intro i P hP
  have hh := ProbeRaySlots.pool_norm_bounds R S ha.le hab (Real.rpow_pos_of_pos hz _) P hP
  simpa only [mul_comm] using And.intro hh.1.le hh.2

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule96
/- END analytic_low.PerturbedCommonBound -/

/- BEGIN original module analytic_low.PerturbedWindowBound -/
section LocalModule97

namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem perturbed_original_ray_compensatedPhysicalProbe_low_loss
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hinj : Function.Injective ell)
    (hsum : ∑i,ell i≤5003/30000) (R : Set Id)
    (a b B loss : ℝ) (ha : 0< a) (hab : a≤ b) (hloss : 0< loss)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤ B)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hab1 : a1< b1) (hB0 : 0≤ B0) (hB1 : 0≤ B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤ B0) (hWB1 : ∀x,‖W1 x‖≤ B1) :
    ∀η : HeckeFamily.Character,∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun i=> canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) W (fun i=> Z^(ell i))
        (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z‖≤ C*Z^(7499/40000+loss) := by
  let D := max 1 B
  have hD : 0< D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hDc : (D:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hD.ne'
  let Wn := fun i x=> W i x/(D:ℂ)
  have hWn : ∀i,Function.support (Wn i)⊆Set.Icc a b := by
    intro i x hx
    apply hW i
    intro hz
    exact hx (by dsimp [Wn];rw [hz,zero_div])
  have hn : ∀i x,‖Wn i x‖≤1 := by
    intro i x
    dsimp only [Wn]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hD]
    exact (div_le_one hD).mpr ((hWnorm i x).trans (le_max_right _ _))
  have hscale : (fun i x=>(D:ℂ)*Wn i x)=W := by
    funext i x
    dsimp [Wn]
    field_simp
  let ε := min (loss/512) (1/2)
  have he : 0<ε := by dsimp [ε];positivity
  have he1 : ε<1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have heloss : 256*ε≤ loss := by have hh := min_le_left (loss/512) (1/2:ℝ);dsimp only [ε];linarith
  intro η
  obtain ⟨C,hC,hbound⟩ := perturbed_original_ray_compensatedPhysicalProbe_low η S hS hmax ell hell hinj hsum R
    a b ε ha hab he he1 Wn hWn hn W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  refine ⟨D^K*C,by positivity,?_⟩
  filter_upwards [hbound,Filter.eventually_ge_atTop (1:ℝ)] with Z hb hZ
  have heq := compensatedPhysicalProbe_window_scale η (calibrationForSet S hmax) W0 W1
    (fun i=> canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) Wn (fun i=> Z^(ell i))
    (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z (D:ℂ)
  rw [hscale] at heq
  rw [heq,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hD]
  calc
    _≤ D^K*(C*Z^(7499/40000+256*ε)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _≤ D^K*(C*Z^(7499/40000+loss)) := by gcongr
    _=_ := by ring

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule97
/- END analytic_low.PerturbedWindowBound -/

/- BEGIN original module analytic_low.PerturbedNormalizer -/
section LocalModule98

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison
open PrincipalMellinResidues ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

theorem perturbed_actual_ray_normalizer_inverse (lengthCap : ℝ) {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (c b : ℝ) (hc : 0< c) (hcb : c≤ b)
    (ell : Fin K→ℝ) (hell : ∀j,0< ell j) (hellsum : ∑j,ell j=lengthCap)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c b) (hp : ∀j y,0≤ W j y) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0< nu) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=> pool (RayQuotient.identityClass M H) S c b (Z^(ell j))
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (lengthCap)
          (slotMass T (residueWeights W (fun j=> Z^(ell j)))) : ℂ)
      normer≠0 ∧ ‖normer⁻¹‖≤ C*Z^nu := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let cs := sourceResidueConstant W0 W1 (∏P∈S,P)
  refine ⟨‖cs⁻¹‖+1,by positivity,?_⟩
  have hpos (j : Fin K) : tsupport (W j)⊆Set.Ioi 0 := by
    apply Set.Subset.trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy
    exact lt_of_lt_of_le hc hy.1
  filter_upwards [power_ray_mass_and_normalizer M H hH S W c b hc hcb hsupp hW hcompact hpos hp hne ell hell nu hnu,
    eventually_gt_atTop (0:ℝ)] with Z hmass hZ
  dsimp only
  refine ⟨ProbePrincipalNormalizer.signed_source_normalizer_ne_zero (∏P∈S,P)
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 Finset.univ
    (fun j=> pool (RayQuotient.identityClass M H) S c b (Z^(ell j)))
    (residueWeights W (fun j=> Z^(ell j))) Z (lengthCap) hZ (fun j _=> hmass.1 j),?_⟩
  have hb : ‖(sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z (lengthCap)
        (slotMass (fun j=> pool (RayQuotient.identityClass M H) S c b (Z^(ell j)))
          (residueWeights W (fun j=> Z^(ell j)))) : ℂ))⁻¹‖≤‖cs⁻¹‖*Z^nu := by
    rw [mul_inv_rev,norm_mul,←Complex.ofReal_inv,Complex.norm_real]
    simpa only [hellsum,Real.norm_eq_abs,mul_comm] using
      mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hZ.le _))

end SevenEighths.ProbeHighRowFamily

end

end OAI

end LocalModule98
/- END analytic_low.PerturbedNormalizer -/

/- BEGIN original module analytic_low.PerturbedNormalized -/
section LocalModule99

namespace OAI

noncomputable section
open scoped Classical ContDiff
open Filter
namespace SevenEighths.ProbePhysical
open ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

theorem perturbed_normalized_compensatedPhysicalProbe_low {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (a b B loss : ℝ) (ha : 0< a) (hab : a≤ b) (hloss : 0< loss)
    (ell : Fin K→ℝ) (hell : ∀j,0< ell j) (hinj : Function.Injective ell) (hsum : ∑j,ell j=5003/30000)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hWB : ∀j y,0≤ W j y ∧ W j y≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : HeckeFamily.Character,∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,
      let Yp := fun j=> Z^(ell j)
      let T := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (5003/30000) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun j=> canonicalSlotSupport (T j)) WC Yp (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z/normer‖≤
        C*Z^(7499/40000+loss) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWC (j : Fin K) : Function.support (WC j)⊆Set.Icc a b := by
    intro y hy
    apply Set.Ioo_subset_Icc_self (hsupp j _)
    intro hz
    exact hy (by dsimp [WC];rw [hz];simp)
  have hWCB (j : Fin K) (y : ℝ) : ‖WC j y‖≤ B := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  have hW1' : Function.support W1⊆Set.Icc a1 (max b1 (a1+1)) := by
    intro y hy
    exact ⟨(hW1 hy).1,(hW1 hy).2.trans (le_max_left _ _)⟩
  have hab1 : a1< max b1 (a1+1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  obtain ⟨Cn,hCn,hnorm⟩ := ProbeHighRowFamily.perturbed_actual_ray_normalizer_inverse (5003/30000) M H hH S hS a b ha hab
    ell hell hsum W hW hcompact hsupp (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1
    hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 (loss/2) (by positivity)
  intro η
  obtain ⟨Cp,hCp,hprobe⟩ := perturbed_original_ray_compensatedPhysicalProbe_low_loss S hS hmax ell
    (fun j=>(hell j).le) hinj hsum.le (RayQuotient.identityClass M H) a b B (loss/2)
    ha hab (by positivity) WC hWC hWCB W0 W1 a0 b0 a1 (max b1 (a1+1))
    (SchwartzMap.seminorm ℝ 0 0 W0) (SchwartzMap.seminorm ℝ 0 0 W1)
    ha0 ha1 hab1 (by positivity) (by positivity) hW0 hW1' (W0.smooth (⊤ : ℕ∞)) (W1.smooth (⊤ : ℕ∞))
    (SchwartzMap.norm_le_seminorm ℝ W0) (SchwartzMap.norm_le_seminorm ℝ W1) η
  refine ⟨Cp*Cn,by positivity,?_⟩
  filter_upwards [hprobe,hnorm,eventually_gt_atTop (0:ℝ)] with Z hp hn hZ
  dsimp only at hn ⊢
  refine ⟨hn.1,?_⟩
  rw [div_eq_mul_inv,norm_mul]
  calc
    _≤(Cp*Z^(7499/40000+loss/2))*(Cn*Z^(loss/2)) :=
      mul_le_mul hp hn.2 (norm_nonneg _) (by positivity)
    _=(Cp*Cn)*Z^(7499/40000+loss) := by
      rw [mul_mul_mul_comm,←Real.rpow_add hZ]
      congr 2
      ring

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule99
/- END analytic_low.PerturbedNormalized -/

/- BEGIN original module RHZeroFreeExtension.ActualSourceAnalytic -/
section LocalModule100

/-! The actual upstream correction H has the required new-domain analytic and
contraction properties. This does not supply the physical J/error bounds. -/
namespace RHZeroFreeExtension.ActualSourceAnalytic
noncomputable section
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeEuler PrincipalSignalComparison
open RHZeroFreeExtension.AnalyticHigh

theorem source_analytic_at_new_boundary (S : Finset (Ideal O))
    (hS : SourceExclusions S) (η : Character) :
    AnalyticOnNhd ℂ (sourceCorrection η S) {s : ℂ | (34999/40000 : ℝ) < s.re} := by
  exact perturbed_globalClosedCorrection_analytic_x η S hS.tail 1 (1/6)
    (by norm_num) (by norm_num)

theorem source_contraction_at_new_boundary (S : Finset (Ideal O))
    (hS : SourceExclusions S) (η : Character) (s : ℂ)
    (hs : (34999/40000 : ℝ) < s.re) :
    ‖sourceCorrection η S s - 1‖ ≤ (1/2 : ℝ) := by
  exact perturbed_globalClosedCorrection_bound η S hS.tail s 1 (1/6)
    hs.le (by norm_num) (by norm_num)

#print axioms source_analytic_at_new_boundary
#print axioms source_contraction_at_new_boundary
end
end RHZeroFreeExtension.ActualSourceAnalytic

end LocalModule100
/- END RHZeroFreeExtension.ActualSourceAnalytic -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedFinalSource -/
section LocalModule101
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical ContDiff
open Filter Asymptotics
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues
open ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
def perturbed_normalizedProbe {K : ℕ} (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    [NeZero (∏P∈S,P)] (ell : Fin K→ℝ) (a b : ℝ) (W : Fin K→ℝ→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (η : Character) (Z : ℝ) : ℂ :=
  let Yp := fun j=> Z^(ell j)
  let T := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
  compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
    (fun j=> canonicalSlotSupport (T j)) (fun j y=>(W j y:ℂ)) Yp
    (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z /
    (sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z (5003/30000) (slotMass T (residueWeights W Yp)) : ℂ))

lemma isBigO_rpow_of_eventual_norm_bound (f : ℝ→ℂ) (r : ℝ)
    (h : ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,‖f Z‖≤ C*Z^r) :
    f=O[atTop](fun Z : ℝ=> Z^r) := by
  obtain ⟨C,hC,hb⟩ := h
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [hb,eventually_ge_atTop (0:ℝ)] with Z hb hZ
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hZ r)] using hb

theorem perturbed_normalizedProbe_low {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (a b B loss : ℝ) (ha : 0< a) (hab : a≤ b) (hloss : 0< loss)
    (ell : Fin K→ℝ) (hell : ∀j,0< ell j) (hinj : Function.Injective ell) (hsum : ∑j,ell j=5003/30000)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hWB : ∀j y,0≤ W j y ∧ W j y≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : Character,perturbed_normalizedProbe M H S hmax ell a b W W0 W1 η=O[atTop](fun Z : ℝ=> Z^(7499/40000+loss)) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  intro η
  obtain ⟨C,hC,hb⟩ := perturbed_normalized_compensatedPhysicalProbe_low M H hH S hS hmax
    a b B loss ha hab hloss ell hell hinj hsum W hW hcompact hsupp hWB hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 η
  apply isBigO_rpow_of_eventual_norm_bound
  exact ⟨C,hC,hb.mono (fun Z h=> h.2)⟩

end
end RHZeroFreeExtension.AnalyticHigh

end LocalModule101
/- END RHZeroFreeExtension.analytic_high.PerturbedFinalSource -/

/- BEGIN original module geometry.SlotLengths -/
section LocalModule102


noncomputable section
open scoped BigOperators
namespace RHSlotLengths

theorem exists_even_distinct_slot_lengths (total L : ℝ) (htotal : 0< total) (hL : 0< L) :
    ∃N : ℕ,0< N ∧ Even N ∧ ∃ell : Fin N→ℝ,Function.Injective ell ∧
      (∀j,0< ell j ∧ ell j< L) ∧ (∑j,ell j)=total := by
  obtain ⟨M,hM⟩ := exists_nat_gt (max 1 (2*total/L))
  let N := 2*M
  have hM0 : 0 < (M : ℝ) := by linarith [le_max_left (1 : ℝ) (2*total/L)]
  have hN : max 1 (2*total/L) < (N : ℝ) := by
    apply hM.trans_le
    dsimp [N]
    push_cast
    linarith
  have hNeven : Even N := ⟨M, by dsimp [N]; omega⟩
  have hN1 : (1:ℝ)< N := (le_max_left _ _).trans_lt hN
  have hNp : 0<(N:ℝ) := by linarith
  have hNnat : 0< N := by exact_mod_cast hNp
  have hNL : 2*total/L<(N:ℝ) := (le_max_right _ _).trans_lt hN
  have hsmall : 2*total/(N:ℝ)< L := by
    have hh := (div_lt_iff₀ hL).mp hNL
    apply (div_lt_iff₀ hNp).mpr
    nlinarith
  let w : Fin N→ℝ := fun j=>1+(j.val:ℝ)/(N:ℝ)
  let A : ℝ := ∑j,w j
  have hw (j : Fin N) : 1≤ w j ∧ w j<2 := by
    have hj : (j.val:ℝ)< N := by exact_mod_cast j.isLt
    have hdiv : (j.val:ℝ)/(N:ℝ)<1 := (div_lt_one hNp).mpr hj
    dsimp only [w]
    constructor
    · linarith [div_nonneg (Nat.cast_nonneg j.val) hNp.le]
    · linarith
  have hA : (N:ℝ)≤ A := by
    calc
      _ = ∑_j : Fin N,(1:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _=>(hw j).1
  have hAp : 0< A := hNp.trans_le hA
  let ell : Fin N→ℝ := fun j=> total*w j/A
  refine ⟨N,hNnat,hNeven,ell,?_,?_,?_⟩
  · intro j k he
    have heq : total*w j=total*w k := (div_left_inj' hAp.ne').mp he
    have hwjk : w j=w k := (mul_right_inj' htotal.ne').mp heq
    have hjk : (j.val:ℝ)/(N:ℝ)=(k.val:ℝ)/(N:ℝ) := by dsimp [w] at hwjk;linarith
    have he' : (j.val:ℝ)=(k.val:ℝ) := (div_left_inj' hNp.ne').mp hjk
    apply Fin.ext
    exact_mod_cast he'
  · intro j
    constructor
    · exact div_pos (mul_pos htotal (by linarith [(hw j).1])) hAp
    · calc
        ell j < 2*total/A := (div_lt_div_iff_of_pos_right hAp).mpr (by nlinarith [(hw j).2])
        _ ≤ 2*total/(N:ℝ) := div_le_div_of_nonneg_left (by positivity) hNp hA
        _ < L := hsmall
  · dsimp only [ell]
    rw [←Finset.sum_div, ←Finset.mul_sum]
    change total*A/A=total
    field_simp

theorem exists_distinct_slot_lengths (total L : ℝ) (htotal : 0 < total) (hL : 0 < L) :
    ∃ N : ℕ, 0 < N ∧ ∃ ell : Fin N → ℝ, Function.Injective ell ∧
      (∀ j, 0 < ell j ∧ ell j < L) ∧ (∑ j, ell j) = total := by
  obtain ⟨N,hN,_hEven,ell,hInject,hBounds,hSum⟩ :=
    exists_even_distinct_slot_lengths total L htotal hL
  exact ⟨N,hN,ell,hInject,hBounds,hSum⟩

theorem exists_physical_slot_lengths (total : ℝ) (htotal : 0< total) (dmin dmax mesh R : ℝ)
    (hdmin : 0< dmin) (hd : dmin≤ dmax) (hm : 0 < mesh) (hR : 0< R) :
    ∃N : ℕ,0< N ∧ ∃ell : Fin N→ℝ,∃rmin : ℝ,0< rmin ∧
      Function.Injective ell ∧ (∑j,ell j)=total ∧
      (∀j,0< ell j ∧ dmax*rmin≤ ell j ∧ ell j≤ dmin*mesh ∧ ell j≤ dmin*R) ∧
      (∀d : ℝ,dmin≤ d → d≤ dmax → ∀j,rmin≤ ell j/d ∧ ell j/d≤ mesh ∧ ell j/d≤ R) := by
  obtain ⟨N,hN,ell,hi,he,hS⟩ := exists_distinct_slot_lengths total (dmin*min mesh R) htotal
    (mul_pos hdmin (lt_min hm hR))
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  obtain ⟨j,hj,hjmin⟩ := Finset.exists_min_image Finset.univ ell hne
  have hmax : 0< dmax := hdmin.trans_le hd
  let rmin := ell j/(2*dmax)
  have hr : 0< rmin := div_pos (he j).1 (by positivity)
  have hlo (k : Fin N) : dmax*rmin≤ ell k := by
    have hk := hjmin k (Finset.mem_univ k)
    have hiden : dmax*rmin=ell j/2 := by dsimp [rmin]; field_simp
    rw [hiden]
    linarith [(he j).1]
  have hup (k : Fin N) : ell k≤ dmin*mesh ∧ ell k≤ dmin*R := by
    constructor
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hdmin.le)
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hdmin.le)
  refine ⟨N,hN,ell,rmin,hr,hi,hS,fun k=>⟨(he k).1,hlo k,(hup k).1,(hup k).2⟩,?_⟩
  intro d hd' hd'' k
  have hd0 : 0< d := hdmin.trans_le hd'
  refine ⟨(le_div_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_⟩
  · exact (by nlinarith : rmin*d≤ dmax*rmin).trans (hlo k)
  · exact (hup k).1.trans (by nlinarith)
  · exact (hup k).2.trans (by nlinarith)

end RHSlotLengths

end

#print axioms RHSlotLengths.exists_distinct_slot_lengths
#print axioms RHSlotLengths.exists_physical_slot_lengths

#print axioms RHSlotLengths.exists_even_distinct_slot_lengths

end LocalModule102
/- END geometry.SlotLengths -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedHighData -/
section LocalModule103


noncomputable section
open scoped BigOperators
namespace RHZeroFreeExtension.AnalyticHigh
open OAI.SevenEighths.Parameters

structure HighData (Δ : ℝ) where
  t : ℝ
  N : ℕ
  ell : Fin N → ℝ
  rmin : ℝ
  ε : ℝ
  e : ℝ
  κ : ℝ
  cost : ℝ
  eps : ℝ
  sigma : ℝ
  t_pos : 0 < t
  t_delta : t < Δ/4
  t_small : t ≤ 1/100000000
  slots_even : Even N
  slots_pos : 0 < N
  slots_injective : Function.Injective ell
  slots_sum : (∑j,ell j)=5003/30000
  slots_bounds :  ∀ j,0 < ell j  ∧  (7/8)*rmin ≤ ell j  ∧  ell j ≤ (1/200)*t
  rmin_pos : 0 < rmin
  epsilon_pos : 0 < ε
  epsilon_small : ε ≤ 1/1000
  epsilon_gap : ε < rmin*t
  e_pos : 0 < e
  e_small : e < 1/1000
  kappa_pos : 0 < κ
  kappa_small : κ ≤ 1
  cost_pos : 0 < cost
  eps_pos : 0 < eps
  eps_small : eps ≤ 1
  sigma_pos : 0 < sigma
  detector_budget : 288*e+8*κ+2*cost ≤ ε/2
  phase_budget : 8*e*t+κ ≤ ε
  count_budget : 159*ε+t+t+7*t ≤ 1/32
  central_budget : (16253/20000)*(159*ε+t+t+7*t)+2*t+(3/2)*(2*t)+
    (26*e+(N+8)*eps+t+(5003/30000)*t)+(t+t+t)+t ≤ 19/320000
  geometric_budget : sigma+8*e+t/8 ≤ 39337/500000
  principal_budget : sigma+t/8 ≤ 17/48000
  window_budget : sigma+e ≤ (34999/40000)*((7/8)*rmin)
  floor_budget : 2*t+26*e+(N+8)*eps+t+(5003/30000)*t+t/8+sigma ≤ 1093/192000
  high_saving : sigma+t/8+t/8 ≤ t
  height_choice :  ∀ J : ℝ,0 ≤ J  →   ∃ τ : ℝ,0 < τ  ∧  τ < (1/200)/2  ∧ 
    4*τ < (1/200)*cost  ∧  τ < t  ∧  2*τ*(1+J) ≤ t  ∧  τ*(2+4*eps) < t

theorem exists_high_data_fine (Δ : ℝ) (hΔ : 0 < Δ) (mesh : ℝ → ℝ)
    (hmesh : ∀ t : ℝ,0 < t → 0 < mesh t) :  ∃ D : HighData Δ, ∀ j,D.ell j ≤ mesh D.t/200 := by
  let t : ℝ := min (Δ/8) (1/1000000000000)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have htΔ : t < Δ/4 := by have hh:=min_le_left (Δ/8) (1/1000000000000:ℝ);dsimp [t];linarith
  have htTiny : t ≤ 1/1000000000000 := min_le_right _ _
  have ht1 : t ≤ 1/100000000 := by linarith
  let L : ℝ := min t (mesh t)/200
  have hL : 0 < L := div_pos (lt_min ht (hmesh t ht)) (by norm_num)
  obtain ⟨N,hN,hEven,ell,hell,hbounds,hsum⟩ :=
    RHSlotLengths.exists_even_distinct_slot_lengths (5003/30000) L (by norm_num) hL
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  obtain ⟨j,_hj,hminj⟩ := Finset.exists_min_image Finset.univ ell hne
  let rmin : ℝ := ell j/(2*(7/8))
  have hr : 0 < rmin := div_pos (hbounds j).1 (by norm_num)
  have hlo (k : Fin N) : (7/8:ℝ)*rmin ≤ ell k := by
    have hh := hminj k (Finset.mem_univ k)
    have hi : (7/8:ℝ)*rmin=ell j/2 := by dsimp [rmin];ring
    rw [hi];linarith [(hbounds j).1]
  have hup (k : Fin N) : ell k ≤ t/200 := by
    exact (hbounds k).2.le.trans ((div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 200)).mpr (min_le_left _ _))
  have hfine (k : Fin N) : ell k ≤ mesh t/200 := by
    exact (hbounds k).2.le.trans ((div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 200)).mpr (min_le_right _ _))
  let small := t/((N:ℝ)+2000)
  have hsmall : 0 < small := div_pos ht (by positivity)
  have hst : small ≤ t/((N:ℝ)+2000) := le_rfl
  have hst0 : small ≤ t/2000 := hst.trans
    (div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N]))
  let ellMin := (7/8:ℝ)*rmin
  have hmin : 0 < ellMin := mul_pos (by norm_num) hr
  obtain ⟨ε,e,κ,cost,τ₀,hε,hε1,hεgap,hεa,he,he1,heell,hea,hκ,hκ1,hcost,
    hdet,hphase,_,_,_,_,_⟩ :=
    exists_detector_scales t rmin t (1/200) t ellMin small 0
      ht.le hr ht (by norm_num) ht hmin hsmall (by norm_num)
  let eps := small/2
  have heps : 0 < eps := by dsimp [eps];positivity
  have hepss : eps ≤ small := by dsimp [eps];linarith only [hsmall]
  have heps1 : eps ≤ 1 := by linarith only [hepss, hst0, ht1]
  have heN : ((N:ℝ)+2000)*eps ≤ t := by
    have h := (le_div_iff₀ (show 0 < (N:ℝ)+2000 by positivity)).mp (hepss.trans hst)
    simpa only [mul_comm] using h
  have he8 : ((N:ℝ)+8)*eps ≤ t := by nlinarith only [heN, heps.le]
  have het : 2000*e ≤ t := by linarith only [hea, hst0]
  let sigma := min (t/2) (ellMin/4)
  have hs : 0 < sigma := lt_min (by positivity) (by positivity)
  have hst2 : sigma ≤ t/2 := min_le_left _ _
  have hsell : sigma ≤ ellMin/4 := min_le_right _ _
  refine ⟨{
    t:=t,N:=N,ell:=ell,rmin:=rmin,ε:=ε,e:=e,κ:=κ,cost:=cost,eps:=eps,sigma:=sigma
    t_pos:=ht,t_delta:=htΔ,t_small:=ht1,slots_even:=hEven,slots_pos:=hN,slots_injective:=hell,slots_sum:=hsum
    slots_bounds:=fun k=>⟨(hbounds k).1,hlo k,by simpa only [div_eq_mul_inv, one_mul, mul_comm] using hup k⟩
    rmin_pos:=hr,epsilon_pos:=hε,epsilon_small:=hε1,epsilon_gap:=hεgap
    e_pos:=he,e_small:=he1,kappa_pos:=hκ,kappa_small:=hκ1,cost_pos:=hcost
    eps_pos:=heps,eps_small:=heps1,sigma_pos:=hs,detector_budget:=by linarith only [hdet]
    phase_budget:=hphase,count_budget:=by linarith only [hεa,hst0,htTiny]
    central_budget:=by linarith only [hεa,hst0,het,he8,htTiny]
    geometric_budget:=by linarith only [hst2, het, htTiny]
    principal_budget:=by linarith only [hst2, htTiny]
    window_budget:=by change sigma+e ≤ (34999/40000)*ellMin;linarith only [hsell, heell, hmin]
    floor_budget:=by linarith only [hst2, het, he8, htTiny]
    high_saving:=by linarith only [hst2, ht]
    height_choice:=?_ },?_⟩
  · intro J hJ
    let τ := min ((1/200:ℝ)*cost/16) (min (1/800) (t/(4*(J+7))))
    have htau : 0 < τ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
    have hτc : τ ≤ (1/200:ℝ)*cost/16 := min_le_left _ _
    have hτd : τ ≤ 1/800 := (min_le_right _ _).trans (min_le_left _ _)
    have hτt : τ ≤ t/(4*(J+7)) := (min_le_right _ _).trans (min_le_right _ _)
    have hτJ : τ*(4*(J+7)) ≤ t := (le_div_iff₀ (by positivity)).mp hτt
    have hprod : 0 ≤ τ*J := mul_nonneg htau.le hJ
    have hprodeps := mul_le_mul_of_nonneg_left heps1 htau.le
    refine ⟨τ,htau,by linarith only [hτd],by linarith only [hτc, hcost],
        by nlinarith only [hτJ, hprod, htau],by nlinarith only [hτJ, hprod, htau],
        by nlinarith only [hτJ, hprod, hprodeps, htau]⟩
  · exact hfine

theorem fine_slot_widths {gap : ℝ} (D : HighData gap) (mesh : ℝ → ℝ)
    (_hmesh : 0 < mesh D.t) (hfine : ∀ j, D.ell j ≤ mesh D.t/200)
    (d : ℝ) (hd : (1/200 : ℝ) ≤ d) (j : Fin D.N) :
    0 < D.ell j/d ∧ D.ell j/d ≤ mesh D.t := by
  have hd0 : 0 < d := by linarith
  refine ⟨div_pos (D.slots_bounds j).1 hd0, (div_le_iff₀ hd0).mpr ?_⟩
  have hh := hfine j
  nlinarith

end RHZeroFreeExtension.AnalyticHigh
end

#print axioms RHZeroFreeExtension.AnalyticHigh.exists_high_data_fine

#print axioms RHZeroFreeExtension.AnalyticHigh.fine_slot_widths

end LocalModule103
/- END RHZeroFreeExtension.analytic_high.PerturbedHighData -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedFinalData -/
section LocalModule104


noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace RHZeroFreeExtension.AnalyticHigh
open OAI.SevenEighths.ProbeFinalAssembly
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
local notation "O" => HeckeFamily.O

structure SourceData {Δ : ℝ} (D : HighData Δ) where
  S : Finset (Ideal O)
  exclusions : SourceExclusions S
  maximal :  ∀ P∈S,P.IsMaximal
  first : FirstTail (4*D.e) S
  w : ℝ → ℝ
  W : SchwartzMap ℝ ℂ
  smooth : ContDiff ℝ ∞ w
  compact : HasCompactSupport w
  support : Function.support w⊆Set.Ioo 1 2
  positive_support : tsupport w⊆Set.Ioi 0
  bounded :  ∀ x,0 ≤ w x  ∧  w x ≤ 1
  nonzero : w≠0
  complex_eq :  ∀ x,W x=(w x:ℂ)
  complex_nonzero : W≠0
  complex_support : Function.support W⊆Set.Icc 1 2
  real :  ∀ x,(W x).im=0
  nonnegative :  ∀ x,0 ≤ (W x).re

theorem exists_source_data {Δ : ℝ} (D : HighData Δ) : Nonempty (SourceData D) := by
  obtain ⟨S,_,hS,hfirst,hmax⟩ := exists_fixed_source D.e D.e_pos ∅ (by simp)
  obtain ⟨w,W,hw,hc,hs,hp,hb,hn,he,hWn,hWs,hr,hWpos⟩ := exists_fixed_probe_window
  exact ⟨⟨S,hS,hmax,hfirst,w,W,hw,hc,hs,hp,hb,hn,he,hWn,hWs,hr,hWpos⟩⟩

def SourceData.modulus {Δ : ℝ} {D : HighData Δ} (F : SourceData D) : Ideal O := ∏P∈F.S,P

instance {Δ : ℝ} {D : HighData Δ} (F : SourceData D) : NeZero F.modulus :=
  ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩

instance {Δ : ℝ} {D : HighData Δ} (F : SourceData D) : Finite (O ⧸ F.modulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne F.modulus)

theorem source_count_parameters {Δ : ℝ} {D : HighData Δ} (F : SourceData D) :
    Nonempty (CountParameters F.modulus ⊤ D.t) := by
  exact exists_count_parameters F.modulus ⊤ le_top F.S F.w F.smooth F.compact
    F.positive_support (fun x=>(F.bounded x).1) F.nonzero 1 2 1 (by norm_num) (by norm_num)
    (by norm_num) F.support (fun x=>(F.bounded x).2) D.t D.t_pos

def SourceData.probe {Δ : ℝ} {D : HighData Δ} (F : SourceData D) (η : Character) : ℝ → ℂ :=
  letI : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  perturbed_normalizedProbe F.modulus ⊤ F.S F.maximal D.ell 1 2 (fun _=> F.w) F.W F.W η

theorem SourceData.probe_low {Δ : ℝ} {D : HighData Δ} (F : SourceData D)
    (loss : ℝ) (hloss : 0 < loss) (η : Character) :
    F.probe η=O[atTop](fun Z : ℝ=> Z^(7499/40000+loss)) := by
  exact perturbed_normalizedProbe_low F.modulus ⊤ le_top F.S F.exclusions F.maximal 1 2 1 loss
    (by norm_num) (by norm_num) hloss D.ell (fun j=>(D.slots_bounds j).1) D.slots_injective D.slots_sum
    (fun _=> F.w) (fun _=> F.smooth) (fun _=> F.compact) (fun _=> F.support)
    (fun _=> F.bounded) (fun _=> F.nonzero) F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero η

end RHZeroFreeExtension.AnalyticHigh

end


#print axioms RHZeroFreeExtension.AnalyticHigh.exists_source_data
#print axioms RHZeroFreeExtension.AnalyticHigh.source_count_parameters
#print axioms RHZeroFreeExtension.AnalyticHigh.SourceData.probe_low

end LocalModule104
/- END RHZeroFreeExtension.analytic_high.PerturbedFinalData -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedFinalMomentInput -/
section LocalModule105


noncomputable section
open scoped Classical BigOperators
open Filter
namespace RHZeroFreeExtension.AnalyticHigh
open OAI.SevenEighths.ProbeFinalAssembly
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
open HeckeInverseAmplification

def SourceMomentBound {Δ : ℝ} {D : HighData Δ} (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t) (η : Character)
    (Z τ C height : ℝ) : Prop :=
   ∀ rows : Finset FreeRow, ∀ d a : ℝ, (1/200:ℝ) ≤ d  →  d ≤ 7/8  →  51/100 < a  →  a ≤ 1  → 
    ( ∀ u∈rows,u.val≠1  ∧  Z^(1/100:ℝ) ≤ rowNorm u  ∧ 
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0  ∧  rowNorm u ≤ Z^(d-D.t))  → 
     ∀ i : ℕ, ∀ z : ℂ,z.re=17/50  →  |z.im| ≤ height  → 
    SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell (fun _ y=>(F.w y:ℂ))
      Z d a D.ε τ (7/8) 2 D.t D.t i z (0:ℝ)
      (if 2*a-1 ≤ 5/6 then counts.cB else counts.cH)
      (if 2*a-1 ≤ 5/6 then counts.kB else counts.kH) C height D.t

lemma SourceMomentBound.mono_constant {Δ : ℝ} {D : HighData Δ} {F : SourceData D}
    {counts : CountParameters F.modulus ⊤ D.t} {η : Character} {Z τ C C' height : ℝ}
    (hZ : 0 ≤ Z) (h : SourceMomentBound F counts η Z τ C height) (hC : C ≤ C') :
    SourceMomentBound F counts η Z τ C' height := by
  intro rows d a hd hd' ha ha' hrows i z hz hzh
  exact sourceMomentsAt_mono_constant F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell
    (fun _ y=>(F.w y:ℂ)) Z d a D.ε τ (7/8) 2 D.t D.t i z (0:ℝ) _ _ C C' height D.t
    hZ hC (h rows d a hd hd' ha ha' hrows i z hz hzh)

def RawMomentInput : Prop :=
   ∀ _hβ : (34999/40000:ℝ) < HeckeZeroSupremum.beta,
     ∀ D : HighData (HeckeZeroSupremum.beta-34999/40000), ∀ F : SourceData D,
     ∀ counts : CountParameters F.modulus ⊤ D.t,
     ∃ J : ℝ,0 ≤ J  ∧   ∀ η : Character, ∃ C : ℝ,0 < C  ∧ 
       ∀ τ : ℝ,0 < τ  →  τ ≤ 1  →   ∀ᶠ Z : ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))

lemma polynomial_height_absorption (C Z τ J t : ℝ)
    (hC : 0 ≤ C) (hZ : 1 ≤ Z) (hτ : 0 ≤ τ) (hJ : 0 ≤ J) (hbudget : 2*τ*(1+J) ≤ t) :
    C*(1+Z^(2*τ))^J ≤ (C*2^J)*Z^t := by
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hscale : 1 ≤ Z^(2*τ) := Real.one_le_rpow hZ (by positivity)
  calc
    _ ≤ C*(2*Z^(2*τ))^J := by gcongr;linarith
    _=(C*2^J)*Z^(2*τ*J) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Real.rpow_nonneg hZp.le _),←Real.rpow_mul hZp.le]
      ring
    _ ≤ (C*2^J)*Z^t := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)

theorem raw_input_chosen_height (h : RawMomentInput) (hβ : (34999/40000:ℝ) < HeckeZeroSupremum.beta)
    (D : HighData (HeckeZeroSupremum.beta-34999/40000)) (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t) :
     ∃ τ : ℝ,0 < τ  ∧  τ < (1/200:ℝ)/2  ∧  4*τ < (1/200:ℝ)*D.cost  ∧  τ < D.t  ∧ 
      2*τ ≤ D.t  ∧  τ*(2+4*D.eps) < D.t  ∧ 
       ∀ η : Character, ∃ C : ℝ,0 < C  ∧   ∀ᶠ Z : ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*Z^D.t) (Z^(2*τ)) := by
  obtain ⟨J,hJ,hbound⟩ := h hβ D F counts
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτJ,hτeps⟩ := D.height_choice J hJ
  have htau1 : τ ≤ 1 := by linarith
  refine ⟨τ,hτ,hτd,hτcost,hτt,by nlinarith,hτeps,?_⟩
  intro η
  obtain ⟨C,hC,hbound⟩ := hbound η
  refine ⟨C*2^J,by positivity,?_⟩
  filter_upwards [hbound τ hτ htau1,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  exact hb.mono_constant (by linarith) (polynomial_height_absorption C Z τ J D.t hC.le hZ hτ.le hJ hτJ)

end RHZeroFreeExtension.AnalyticHigh

end


#print axioms RHZeroFreeExtension.AnalyticHigh.raw_input_chosen_height

end LocalModule105
/- END RHZeroFreeExtension.analytic_high.PerturbedFinalMomentInput -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedFinalFixedHigh -/
section LocalModule106


noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace RHZeroFreeExtension.AnalyticHigh
open OAI.SevenEighths.ProbeFinalAssembly
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison
open HeckeInverseAmplification HeckeDetectorPhysicalSelection HeckeDetectorFiberPartition
open ProbeMellinBoundary

theorem fixed_high_bound (hβ : (34999/40000:ℝ) < HeckeZeroSupremum.beta)
    (D : HighData (HeckeZeroSupremum.beta-34999/40000)) (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t) (τ : ℝ)
    (hτ : 0 < τ) (hτd : τ < (1/200:ℝ)/2) (hτcost : 4*τ < (1/200:ℝ)*D.cost)
    (hτt : τ < D.t) (hτ2 : 2*τ ≤ D.t) (hτeps : τ*(2+4*D.eps) < D.t) :
     ∃ C : ℝ,0 < C  ∧   ∀ η : Character, ∃ Ct : ℝ,0 < Ct  ∧   ∀ᶠ Z : ℝ in atTop,
       ∀ C0 : ℝ,0 ≤ C0  →  SourceMomentBound F counts η Z τ (C0*Z^D.t) (Z^(2*τ))  → 
      ‖F.probe η Z-HeckeSignal.signal (η.excludePrimes F.S F.exclusions.prime)
        (sourceCorrection η F.S) (-11/16) Z‖ ≤ 
        (Ct+C*C0*(η.modulus.absNorm:ℝ)^(2*D.eps))*Z^(HeckeZeroSupremum.beta-11/16-D.sigma) := by
  let : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  have ht := D.t_pos
  have ht1 := D.t_small
  have hconductor : (16253/20000:ℝ)+D.t+2*D.t ≤ 7/8 := by linarith
  obtain ⟨n,hn,C,hC,hbound⟩ := perturbed_fixed_actual_high_probe_from_raw_moments F.modulus ⊤ le_top D.N
    D.e D.eps 1 2 1 D.t (1/200) (7/8) D.rmin τ D.ε D.κ D.cost D.t D.t D.t
    D.e_pos D.e_small D.eps_pos (by norm_num) (by norm_num) (by norm_num)
    ht.le (by norm_num) (by norm_num) (by norm_num) D.rmin_pos hτ D.epsilon_pos D.kappa_pos
    D.cost_pos.le ht D.phase_budget D.epsilon_gap ht (by linarith) hτeps
    F.S F.exclusions F.first F.maximal D.ell D.slots_injective
    (fun j=>(D.slots_bounds j).2.1) (fun j=>(D.slots_bounds j).2.2)
    (fun _=> F.w) (fun _=> F.support) (fun _=> F.smooth) (fun _=> F.bounded)
    (fun _=> F.compact) (fun _=> F.nonzero) D.slots_sum
    (by norm_num) D.epsilon_small D.kappa_small hτd hτcost (by nlinarith [D.detector_budget])
    F.w F.smooth F.compact F.positive_support (fun y=>(F.bounded y).1) F.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num) F.support (fun y=>(F.bounded y).2)
    D.t D.t D.t (2*τ) D.t ht ht ht (by linarith)
    D.t (2*D.t) D.t ht (by linarith) (by positivity) D.count_budget (by nlinarith [D.central_budget])
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    (D.t/8) (by positivity) (D.t/8) (by positivity) (by norm_num) hconductor (by linarith) hβ.le
    D.sigma D.sigma_pos D.geometric_budget D.principal_budget D.window_budget D.floor_budget D.high_saving counts
  refine ⟨C,hC,?_⟩
  intro η
  obtain ⟨Ct,hCt,hb⟩ := hbound η
  refine ⟨Ct,hCt,?_⟩
  filter_upwards [hb,sourceDyad_geometry_eventually (1/200) (7/8) D.t (16253/20000+D.t)
    (by norm_num) (by norm_num) ht hconductor,
    HeckeDyadic.constant_absorbed_eventually (3*(n:ℝ)+1) τ hτ,
    eventually_gt_atTop (1:ℝ)] with Z hb hgeo hnheight hZ
  intro C0 hC0 hmom
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,hestimate⟩ := hb
  apply hestimate C0 hC0
  intro k hk i hi j hj
  dsimp only
  intro hne t htheight
  let rows := supportedNonfloorRows F.S F.maximal (rowBand (Z^(1/100:ℝ)) (Z^((16253/20000:ℝ)+D.t))) grid
  let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
  have hsub : rows'⊆rows∩dyadicRows 1 k := Finset.filter_subset _ _
  have hsubr : rows'⊆rows := hsub.trans Finset.inter_subset_left
  have hrows :  ∀ u∈rows,u.val≠1  ∧  Z^(1/100:ℝ) ≤ rowNorm u  ∧  rowNorm u ≤ Z^(16253/20000+D.t) := by
    intro u hu
    have hh := mem_rowBand.mp ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu).1
    exact ⟨hh.1,hh.2.1,hh.2.2.le⟩
  have hg := hgeo rows hrows k (hne.mono hsub)
  obtain ⟨u,hu⟩ := hne
  have huj : grid u=j := ((mem_cubeBinRows _ idx grid i j u).mp hu).2.2
  have hjne : j≠0 := huj ▸ ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp (hsubr hu)).2.2
  have ha : (51/100:ℝ) < 51/100+D.e*j := by
    have hjp : (0:ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hjne
    nlinarith [D.e_pos]
  have ha' : (51/100:ℝ)+D.e*j ≤ 1 := by simpa only [huj] using (hbins u).2.1
  have hrow' :  ∀ v∈rows',v.val≠1  ∧  Z^(1/100:ℝ) ≤ rowNorm v  ∧ 
      (calibrationForSet F.S F.maximal).residueMonoid v.val≠0  ∧ 
      rowNorm v ≤ Z^(sourceDyadConductor Z D.t k-D.t) := by
    intro v hv
    exact ⟨(hrows v (hsubr hv)).1,(hrows v (hsubr hv)).2.1,
      ((mem_supportedNonfloorRows F.S F.maximal _ grid v).mp (hsubr hv)).2.1,hg.2.2.2.2.2 v (hsub hv)⟩
  have hi' : (i:ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hheight : (3*i+1:ℕ)*Z^τ ≤ Z^(2*τ) := by
    have hZp : 0 < Z := zero_lt_one.trans hZ
    calc
      _ ≤ (3*(n:ℝ)+1)*Z^τ := by push_cast;gcongr
      _ ≤ Z^τ*Z^τ := mul_le_mul_of_nonneg_right hnheight (by positivity)
      _=Z^(2*τ) := by rw [←Real.rpow_add hZp];congr 1;ring
  apply hmom rows' (sourceDyadConductor Z D.t k) (51/100+D.e*j) hg.2.2.1 hg.2.2.2.1 ha ha' hrow' i
    ((17/50:ℂ)+t.1.2*Complex.I)
  · simp
  · simpa using htheight.2.trans hheight

end RHZeroFreeExtension.AnalyticHigh

end


#print axioms RHZeroFreeExtension.AnalyticHigh.fixed_high_bound

end LocalModule106
/- END RHZeroFreeExtension.analytic_high.PerturbedFinalFixedHigh -/

/- BEGIN original module RHZeroFreeExtension.ActualHeckeContinuation -/
section LocalModule107

/-!
Generic continuation for the actual upstream Hecke L-function and signal.
This proves an implication from explicit probe estimates. It does not construct
those estimates and does not assert the improved zero-free theorem.
-/

namespace RHZeroFreeExtension.ActualHeckeContinuation

noncomputable section
open Filter Asymptotics Set
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open OAI.SevenEighths.HeckeSignal OAI.SevenEighths.Continuation

def probeMargin (boundary beta omega saving : ℝ) : ℝ :=
  min (beta - boundary - omega) saving

theorem nonzero_of_actual_probe_bounds
    (chi : Character) (H : ℂ → ℂ) (J : ℝ → ℂ)
    (boundary beta omega saving c : ℝ)
    (hboundary : 0 < boundary) (hboundaryOld : boundary ≤ (7 / 8 : ℝ))
    (hbeta : beta ≤ 1) (homega : 0 < omega)
    (homegaGap : omega < beta - boundary) (hsaving : 0 < saving)
    (hH : AnalyticOnNhd ℂ H {s : ℂ | boundary < s.re})
    (hcontract : ∀ s : ℂ, boundary < s.re → ‖H s - 1‖ ≤ (1 / 2 : ℝ))
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (boundary + c + omega)))
    (herror : (fun x => J x - signal chi H c x) =O[atTop]
      (fun x : ℝ => x ^ (beta + c - saving)))
    {rho : ℂ}
    (hrho : beta - probeMargin boundary beta omega saving < rho.re)
    (hpole : rho ≠ 1 ∨ chi.residue ≠ 1) : LFunction chi rho ≠ 0 := by
  let a := beta - probeMargin boundary beta omega saving
  have hmargin : 0 < probeMargin boundary beta omega saving := by
    exact lt_min (by linarith) hsaving
  have hmarginGap : probeMargin boundary beta omega saving ≤ beta - boundary - omega :=
    min_le_left _ _
  have hboundaryA : boundary < a := by dsimp [a]; linarith
  have haTwo : a < 2 := by dsimp [a]; linarith
  have hexponents : max (boundary + c + omega) (beta + c - saving) = a + c := by
    dsimp only [a, probeMargin]
    rcases le_total (beta - boundary - omega) saving with h | h
    · rw [min_eq_left h, max_eq_left (by linarith)]
      ring
    · rw [min_eq_right h, max_eq_right (by linarith)]
      ring
  have htop : signal chi H c =O[atTop] (fun x : ℝ => x ^ (a + c)) := by
    simpa only [hexponents] using
      common_signal_bound J (signal chi H c) (boundary + c + omega)
        (beta + c - saving) hJ herror
  have hHOld : AnalyticOnNhd ℂ H {s : ℂ | (7 / 8 : ℝ) < s.re} :=
    hH.mono (fun _ hs => lt_of_le_of_lt hboundaryOld hs)
  have hcontractOld : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → ‖H s - 1‖ ≤ (1 / 2 : ℝ) :=
    fun s hs => hcontract s (lt_of_le_of_lt hboundaryOld hs)
  have hHd := hHOld.differentiableOn
  have hHa : AnalyticOnNhd ℂ H {s : ℂ | a < s.re} :=
    hH.mono (fun _ hs => lt_trans hboundaryA hs)
  have hregularAnalytic : AnalyticOnNhd ℂ (regularL chi) {s : ℂ | a < s.re} :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr (regularL_entire chi)).mono
      (Set.subset_univ _)
  have hregularizerAnalytic : AnalyticOnNhd ℂ (targetRegularizer chi)
      {s : ℂ | a < s.re} :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (targetRegularizer_entire chi)).mono (Set.subset_univ _)
  have hidentity : ∀ s : ℂ, max a 1 < s.re →
      regularL chi s * signalMellin (signal chi H c) c s =
        targetRegularizer chi s * gaussianMultiplier H s := by
    intro s hs
    have hsOne : 1 < s.re := (le_max_right a 1).trans_lt hs
    have hsZero : s ≠ 0 := by intro h; norm_num [h] at hsOne
    have hsNotOne : s ≠ 1 := by intro h; norm_num [h] at hsOne
    rw [regularL_eq chi hsZero (Or.inl hsNotOne),
      signalMellin_eq_amplitude chi H hHd hcontractOld c a haTwo htop hs]
    unfold amplitude quotient gaussianMultiplier
    rw [OAI.SevenEighths.HeckeReciprocal.reciprocal_eq_inv chi hsZero hsNotOne]
    have hnonzero := LFunction_ne_zero_of_one_lt_re chi hsOne
    field_simp
  have hrhoA : a < rho.re := hrho
  have hrhoZero : rho ≠ 0 := by
    intro h
    rw [h] at hrhoA
    norm_num at hrhoA
    linarith
  exact nonzero_of_regularized_signal a 1 c (LFunction chi) (regularL chi)
    (targetRegularizer chi) (gaussianMultiplier H) (signal chi H c)
    hregularAnalytic hregularizerAnalytic (gaussianMultiplier_analytic hHa)
    (signal_locallyIntegrable chi H hHd hcontractOld c) htop
    (signal_rapidDecayAtZero chi H hHd hcontractOld c) hidentity hrhoA
    (regularL_eq chi hrhoZero hpole) (targetRegularizer_ne_zero chi hpole)
    (gaussianMultiplier_ne_zero (hcontract rho (hboundaryA.trans hrhoA)))

end
end RHZeroFreeExtension.ActualHeckeContinuation

end LocalModule107
/- END RHZeroFreeExtension.ActualHeckeContinuation -/

/- BEGIN original module RHZeroFreeExtension.ActualPrimitiveContinuation -/
section LocalModule108

/-!
The endpoint-independent primitive-supremum deduction for the actual Hecke
family. The premise lists the physical probe estimates and finite-deletion
identity explicitly. Their construction is a separate obligation; this module
does not claim that those estimates have been proved for the new geometry.
-/

namespace RHZeroFreeExtension.ActualPrimitiveContinuation

noncomputable section
open scoped Classical
open Filter Asymptotics
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open OAI.SevenEighths.HeckeZeroSupremum
open RHZeroFreeExtension.ActualHeckeContinuation

theorem beta_le_of_uniform_physical_probes
    (boundary : ℝ) (hhalf : (1 / 2 : ℝ) ≤ boundary)
    (hboundaryOld : boundary ≤ (7 / 8 : ℝ))
    (hprobes : boundary < beta →
      ∃ omega saving : ℝ, 0 < omega ∧ omega < beta - boundary ∧ 0 < saving ∧
        ∀ eta : Character, FiniteFourier.IsPrimitiveOnIdeals eta.residue →
          ∃ (chi : Character) (H : ℂ → ℂ) (J : ℝ → ℂ) (c : ℝ),
            (∀ I, idealCoeff chi I =
              if IsCoprime I chi.modulus then idealCoeff eta I else 0) ∧
            AnalyticOnNhd ℂ H {s : ℂ | boundary < s.re} ∧
            (∀ s : ℂ, boundary < s.re → ‖H s - 1‖ ≤ (1 / 2 : ℝ)) ∧
            J =O[atTop] (fun x : ℝ => x ^ (boundary + c + omega)) ∧
            (fun x => J x - HeckeSignal.signal chi H c x) =O[atTop]
              (fun x : ℝ => x ^ (beta + c - saving))) :
    beta ≤ boundary := by
  by_contra hn
  obtain ⟨omega, saving, homega, homegaGap, hsaving, hprobesAll⟩ :=
    hprobes (lt_of_not_ge hn)
  have hmargin : 0 < probeMargin boundary beta omega saving :=
    lt_min (by linarith) hsaving
  have hmarginGap : probeMargin boundary beta omega saving ≤ beta - boundary - omega :=
    min_le_left _ _
  have hsmall : (1 / 2 : ℝ) ≤ beta - probeMargin boundary beta omega saving := by
    linarith
  obtain ⟨eta, rho, hp, hrhoHalf, _, hpole, hz, hnear⟩ :=
    HeckePrimitiveSupremum.exists_primitive_zero_near_beta hmargin hsmall
  obtain ⟨chi, H, J, c, hmask, hH, hcontract, hJ, herror⟩ := hprobesAll eta hp
  have hpoleChi : rho ≠ 1 ∨ chi.residue ≠ 1 := by
    rcases hpole with hOne | hEta
    · exact Or.inl hOne
    · exact Or.inr (fun hChi =>
        hEta ((HeckeFiniteDeletion.principal_iff_of_mask chi eta hmask).mp hChi))
  have hzChi : LFunction chi rho = 0 := by
    rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonpole chi eta hmask
      (by linarith) hpoleChi, hz, zero_mul]
  exact (nonzero_of_actual_probe_bounds chi H J boundary beta omega saving c
    (by linarith) hboundaryOld beta_le_one homega homegaGap hsaving
    hH hcontract hJ herror hnear hpoleChi) hzChi

theorem hecke_nonzero_of_uniform_physical_probes
    (boundary : ℝ) (hhalf : (1 / 2 : ℝ) ≤ boundary)
    (hboundaryOld : boundary ≤ (7 / 8 : ℝ))
    (hprobes : boundary < beta →
      ∃ omega saving : ℝ, 0 < omega ∧ omega < beta - boundary ∧ 0 < saving ∧
        ∀ eta : Character, FiniteFourier.IsPrimitiveOnIdeals eta.residue →
          ∃ (chi : Character) (H : ℂ → ℂ) (J : ℝ → ℂ) (c : ℝ),
            (∀ I, idealCoeff chi I =
              if IsCoprime I chi.modulus then idealCoeff eta I else 0) ∧
            AnalyticOnNhd ℂ H {s : ℂ | boundary < s.re} ∧
            (∀ s : ℂ, boundary < s.re → ‖H s - 1‖ ≤ (1 / 2 : ℝ)) ∧
            J =O[atTop] (fun x : ℝ => x ^ (boundary + c + omega)) ∧
            (fun x => J x - HeckeSignal.signal chi H c x) =O[atTop]
              (fun x : ℝ => x ^ (beta + c - saving)))
    (chi : Character) {s : ℂ} (hs : boundary < s.re)
    (hpole : s ≠ 1 ∨ chi.residue ≠ 1) : LFunction chi s ≠ 0 := by
  exact LFunction_ne_zero_of_beta_lt chi
    ((beta_le_of_uniform_physical_probes boundary hhalf hboundaryOld hprobes).trans_lt hs)
    hpole

end
end RHZeroFreeExtension.ActualPrimitiveContinuation

end LocalModule108
/- END RHZeroFreeExtension.ActualPrimitiveContinuation -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedFinalChosenData -/
section LocalModule109


noncomputable section
open scoped Classical
open Filter

namespace RHZeroFreeExtension.AnalyticHigh
open OAI.SevenEighths.ProbeFinalAssembly
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison

def ChosenMomentInput:Prop:=
   ∀ _hβ:(34999/40000:ℝ) < HeckeZeroSupremum.beta,
     ∃ D:HighData (HeckeZeroSupremum.beta-34999/40000), ∃ F:SourceData D,
     ∃ counts:CountParameters F.modulus ⊤ D.t,
     ∃ J:ℝ,0 ≤ J  ∧   ∀ η:Character, ∃ C:ℝ,0 < C  ∧ 
       ∀ τ:ℝ,0 < τ → τ ≤ 1 →  ∀ᶠ Z:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))

def FineMomentInput:Prop:=
   ∀ _hβ:(34999/40000:ℝ) < HeckeZeroSupremum.beta,
     ∃ mesh:ℝ → ℝ,( ∀ t:ℝ,0 < t → 0 < mesh t)  ∧ 
     ∀ D:HighData (HeckeZeroSupremum.beta-34999/40000),( ∀ j,D.ell j ≤ mesh D.t/200) → 
     ∀ F:SourceData D, ∀ counts:CountParameters F.modulus ⊤ D.t,
     ∃ J:ℝ,0 ≤ J  ∧   ∀ η:Character, ∃ C:ℝ,0 < C  ∧ 
       ∀ τ:ℝ,0 < τ → τ ≤ 1 →  ∀ᶠ Z:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))

theorem chosen_input_of_fine (h:FineMomentInput):ChosenMomentInput:=by
  intro hβ
  obtain ⟨mesh,hmesh,hmom⟩:=h hβ
  obtain ⟨D,hD⟩:=exists_high_data_fine (HeckeZeroSupremum.beta-34999/40000) (by linarith) mesh hmesh
  obtain ⟨F⟩:=exists_source_data D
  obtain ⟨counts⟩:=source_count_parameters F
  exact ⟨D,F,counts,hmom D hD F counts⟩

theorem chosen_data_height {Δ:ℝ}(D:HighData Δ)(F:SourceData D)
    (counts:CountParameters F.modulus ⊤ D.t)(J:ℝ)(hJ:0 ≤ J)
    (hbound: ∀ η:Character, ∃ C:ℝ,0 < C  ∧ 
       ∀ τ:ℝ,0 < τ → τ ≤ 1 →  ∀ᶠ Z:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))):
     ∃ τ:ℝ,0 < τ  ∧  τ < (1/200:ℝ)/2  ∧  4*τ < (1/200)*D.cost  ∧  τ < D.t  ∧ 
      2*τ ≤ D.t  ∧  τ*(2+4*D.eps) < D.t  ∧ 
       ∀ η:Character, ∃ C:ℝ,0 < C  ∧   ∀ᶠ Z:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*Z^D.t) (Z^(2*τ)):=by
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτJ,hτeps⟩:=D.height_choice J hJ
  have htau1:τ ≤ 1:=by linarith
  refine ⟨τ,hτ,hτd,hτcost,hτt,by nlinarith,hτeps,?_⟩
  intro η
  obtain ⟨C,hC,hbound⟩:=hbound η
  refine ⟨C*2^J,by positivity,?_⟩
  filter_upwards [hbound τ hτ htau1,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  exact hb.mono_constant (by linarith)
    (polynomial_height_absorption C Z τ J D.t hC.le hZ hτ.le hJ (by linarith))

theorem beta_le_of_chosen_moments (hmom : ChosenMomentInput) :
    HeckeZeroSupremum.beta ≤ (34999/40000:ℝ) := by
  apply RHZeroFreeExtension.ActualPrimitiveContinuation.beta_le_of_uniform_physical_probes
    (34999/40000) (by norm_num) (by norm_num)
  intro hβ
  obtain ⟨D,F,counts,J,hJ,hmom⟩ := hmom hβ
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτ2,hτeps,hsource⟩ := chosen_data_height D F counts J hJ hmom
  obtain ⟨C,hC,hhigh⟩ := fixed_high_bound hβ D F counts τ hτ hτd hτcost hτt hτ2 hτeps
  let loss := (HeckeZeroSupremum.beta-34999/40000)/2
  have hloss : 0 < loss := by dsimp [loss];linarith
  have hlossgap : loss < HeckeZeroSupremum.beta-34999/40000 := by dsimp [loss];linarith
  refine ⟨loss,D.sigma,hloss,hlossgap,D.sigma_pos,?_⟩
  intro η _hprimitive
  obtain ⟨hmask,_hOldAnalytic,_hOldBound⟩ :=
    ProbeFinalAssembly.actual_source_analytic F.S F.exclusions η
  refine ⟨η.excludePrimes F.S F.exclusions.prime,sourceCorrection η F.S,F.probe η,
    (-11/16),hmask,?_,?_,?_,?_⟩
  · exact RHZeroFreeExtension.ActualSourceAnalytic.source_analytic_at_new_boundary F.S F.exclusions η
  · exact RHZeroFreeExtension.ActualSourceAnalytic.source_contraction_at_new_boundary F.S F.exclusions η
  · have hexp : (34999/40000 : ℝ)+(-11/16)=7499/40000 := by norm_num
    simpa only [hexp] using F.probe_low loss hloss η
  · obtain ⟨Ct,hCt,hhigh⟩ := hhigh η
    obtain ⟨Cm,hCm,hsource⟩ := hsource η
    apply isBigO_rpow_of_eventual_norm_bound
    refine ⟨Ct+C*Cm*(η.modulus.absNorm:ℝ)^(2*D.eps),by positivity,?_⟩
    filter_upwards [hhigh,hsource] with Z hh hs
    simpa only [sub_eq_add_neg, neg_div] using hh Cm hCm.le hs

theorem beta_le_of_fine_moments (hmom : FineMomentInput) :
    HeckeZeroSupremum.beta ≤ (34999/40000:ℝ) :=
  beta_le_of_chosen_moments (chosen_input_of_fine hmom)

end RHZeroFreeExtension.AnalyticHigh
end
#print axioms RHZeroFreeExtension.AnalyticHigh.beta_le_of_fine_moments

namespace RHZeroFreeExtension.AnalyticHigh
/-- Assembly keeps the original headline only as an input needed to construct
the finite-kappa moment family; it is not the improved conclusion. -/
theorem beta_le_of_original_headline_and_fine_moment_construction
    (hOld : OAI.SevenEighths.HeckeZeroSupremum.beta ≤ (7/8 : ℝ))
    (hconstruct : OAI.SevenEighths.HeckeZeroSupremum.beta ≤ (7/8 : ℝ) → FineMomentInput) :
    OAI.SevenEighths.HeckeZeroSupremum.beta ≤ (34999/40000 : ℝ) :=
  beta_le_of_fine_moments (hconstruct hOld)
end RHZeroFreeExtension.AnalyticHigh

end LocalModule109
/- END RHZeroFreeExtension.analytic_high.PerturbedFinalChosenData -/

/- BEGIN original module RHZeroFreeExtension.moment_adapters.DetectorMomentPrimeGeometry -/
section LocalModule110

/-! Actual perturbed source prime geometry. The generic separation, capacity,
large-prime and fixed-character norm results are reused unchanged. Only the
window/SourceData wrappers are rederived at the genuine new slot lengths. -/
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.PerturbedHeckeDetectorMomentPrimeGeometry
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialPhysicalSlots
open HeckeDetectorBatch HeckeDetectorRawFiber HeckeDetectorFiberPartition ProbeHighRowFamily
local notation "O" => HeckeFamily.O

theorem sourceMoment_primeProfile_norm {Δ : ℝ} {D : RHZeroFreeExtension.AnalyticHigh.HighData Δ}
    (F : RHZeroFreeExtension.AnalyticHigh.SourceData D) (X : ℝ) (ζ : ℂ) (hz : ζ.re≤1)
    (P : Ideal O) : ‖primeProfile F.W X ζ P‖≤1 := by
  by_cases hw : F.W ((P.absNorm:ℝ)/X)=0
  · simp [primeProfile,hw]
  have hx := F.complex_support hw
  have hp : 0<(P.absNorm:ℝ)/X := lt_of_lt_of_le (by norm_num) hx.1
  have hnorm : ‖F.W ((P.absNorm:ℝ)/X)‖≤1 := by
    rw [F.complex_eq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (F.bounded _).1]
    exact (F.bounded _).2
  rw [primeProfile,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hp]
  have hr : ((P.absNorm:ℝ)/X)^((ζ-1).re)≤1 :=
    (Real.rpow_le_rpow_of_exponent_le hx.1
      (show (ζ-1).re≤0 by simp only [Complex.sub_re,Complex.one_re];linarith)).trans_eq
        (Real.rpow_zero _)
  simpa only [one_mul] using mul_le_mul hnorm hr (Real.rpow_nonneg hp.le _) (by norm_num : (0:ℝ)≤1)

section Live
variable (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ)

theorem sourceMoment_live_disjoint {Δ : ℝ} {D : RHZeroFreeExtension.AnalyticHigh.HighData Δ}
    (F : RHZeroFreeExtension.AnalyticHigh.SourceData D) {ι : Type*} (ell : ι→ℝ)
    (U : ℝ) (hU : 0< U) (s t : ι)
    (hsep : 2*U^(ell s)<1*U^(ell t) ∨ 2*U^(ell t)<1*U^(ell s)) :
    Disjoint (livePrimes M H F.W 2 (U^(ell s))) (livePrimes M H F.W 2 (U^(ell t))) := by
  apply Finset.disjoint_left.mpr
  intro P hs ht
  have hs' := livePrime_data M H F.W 1 2 (U^(ell s))
    (Real.rpow_pos_of_pos hU _) F.complex_support P hs
  have ht' := livePrime_data M H F.W 1 2 (U^(ell t))
    (Real.rpow_pos_of_pos hU _) F.complex_support P ht
  rcases hsep with hsep|hsep <;> linarith [hs'.2.2.1,hs'.2.2.2,ht'.2.2.1,ht'.2.2.2]

theorem sourceMoment_live_denominator {Δ : ℝ} {D : RHZeroFreeExtension.AnalyticHigh.HighData Δ}
    (F : RHZeroFreeExtension.AnalyticHigh.SourceData D) {ι : Type*} [Fintype ι]
    (data : RowData) (U : ℝ) (ell : ι→ℝ) (hU : 0< U)
    (hlarge : ∀s,((baseCharacter data).modulus.absNorm:ℝ)<1*U^(ell s))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset (fun s=> livePrimes M H F.W 2 (U^(ell s)))) :
    ‖fixedBase data.η data.m data.f (∏s,p s)‖=1 := by
  rw [map_prod,norm_prod]
  apply Finset.prod_eq_one
  intro s _
  have hs := livePrime_data M H F.W 1 2 (U^(ell s))
    (Real.rpow_pos_of_pos hU _) F.complex_support (p s) (Fintype.mem_piFinset.mp hp s)
  exact sourceMoment_fixedBase_norm_one data (p s) hs.1 ((hlarge s).trans_le hs.2.2.1)

theorem sourceMoment_live_quotient_norm {Δ : ℝ} {D : RHZeroFreeExtension.AnalyticHigh.HighData Δ}
    (F : RHZeroFreeExtension.AnalyticHigh.SourceData D) {ι : Type*} [Fintype ι]
    (data : RowData) (U : ℝ) (ell : ι→ℝ) (ζ : ι→ℂ) (hU : 0< U)
    (hz : ∀s,(ζ s).re=17/50)
    (hlarge : ∀s,((baseCharacter data).modulus.absNorm:ℝ)<1*U^(ell s))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset (fun s=> livePrimes M H F.W 2 (U^(ell s)))) :
    ‖star (∏s,primeProfile F.W (U^(ell s)) (ζ s) (p s))/
      fixedBase data.η data.m data.f (∏s,p s)‖≤1 := by
  rw [norm_div,norm_star,sourceMoment_live_denominator M H F data U ell hU hlarge p hp,
    div_one,norm_prod]
  exact Finset.prod_le_one₀ (fun s _=> norm_nonneg _)
    (fun s _=> sourceMoment_primeProfile_norm F _ _ (by rw [hz s];norm_num) _)
end Live

section Source
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem sourceMoment_fiber_prime_geometry_eventually
    {Δ : ℝ} {D : RHZeroFreeExtension.AnalyticHigh.HighData Δ} (F : RHZeroFreeExtension.AnalyticHigh.SourceData D)
    (η : Character) (εg : ℝ) (hεg : 0<εg) :
    ∀ᶠ Z : ℝ in atTop,1≤ Z ∧ ∀d : ℝ,1/200≤ d→
      ∀(a ε tstar T allowance : ℝ)(i : ℕ)
      (B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),
      B.data=sourceMomentData M H hH F.S F.exclusions.prime η→
      B.profile=(fun _ x=>(F.w x:ℂ))→B.upper=(fun _=>2)→
      B.widths=(fun s=> D.ell s/d)→(∀s,(B.external s).re=17/50)→
      ∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
      let f:=B.fiber bin j J K hne
      (∀s t,s≠t→Disjoint
        (livePrimes M H (f.profile s) (f.upper s) ((Z^d)^(f.widths s)))
        (livePrimes M H (f.profile t) (f.upper t) ((Z^d)^(f.widths t)))) ∧
      ∀selected : Finset (Fin D.N),
        (∀s:selected,1≤2*(Z^d)^(f.widths s)) ∧
        (∏s:selected,2*(Z^d)^(f.widths s))≤
          (Z^d)^((∑s:selected,f.widths s)+εg) ∧
        ∀p : selected→Ideal O,
        p∈Fintype.piFinset (fun s:selected=>
          livePrimes M H (f.profile s) (f.upper s) ((Z^d)^(f.widths s)))→
        Function.Injective p ∧ CanonicalQuadraticSieve.Admissible (∏s:selected,p s) ∧
        (∀s:selected,((p s).absNorm:ℝ)≤2*(Z^d)^(f.widths s)) ∧
        ‖fixedBase f.rowData.η f.rowData.m f.rowData.f (∏s:selected,p s)‖=1 ∧
        ‖star (∏s:selected,primeProfile (f.profile s) ((Z^d)^(f.widths s)) (f.external s) (p s))/
          fixedBase f.rowData.η f.rowData.m f.rowData.f (∏s:selected,p s)‖≤1 := by
  filter_upwards [sourceMoment_separation_eventually D.ell D.slots_injective,
    sourceMoment_capacity_eventually D.ell (fun s=>(D.slots_bounds s).1.le) εg hεg,
    sourceMoment_fiber_large_eventually M H hH F.S F.exclusions.prime η
      D.ell (fun s=>(D.slots_bounds s).1)] with Z hsep hcap hlarge
  refine ⟨hsep.1,?_⟩
  intro d hd a ε tstar T allowance i B hdata hprofile0 hupper hwidths hz bin j J K hne
  have hprofile : B.profile=(fun _=>(F.W:ℝ→ℂ)) := by
    rw [hprofile0]
    funext s x
    exact (F.complex_eq x).symm
  have hd0 : 0< d := by linarith
  have hu : 0< Z^d := Real.rpow_pos_of_pos (zero_lt_one.trans_le hsep.1) _
  have hs := hsep.2 d hd0
  have hc := hcap.2 d hd
  have hl := hlarge.2 d hd0 a ε tstar T allowance i B hdata hwidths bin j J K hne
  dsimp only
  change (∀s t,s≠t→Disjoint
      (livePrimes M H (B.profile s) (B.upper s) ((Z^d)^(B.widths s)))
      (livePrimes M H (B.profile t) (B.upper t) ((Z^d)^(B.widths t)))) ∧ _
  refine ⟨?_,?_⟩
  · intro s t hst
    rw [hprofile,hupper,hwidths]
    exact sourceMoment_live_disjoint M H F (fun s=> D.ell s/d) (Z^d) hu s t (hs s t hst)
  · intro selected
    change (∀s:selected,1≤2*(Z^d)^(B.widths s)) ∧
      (∏s:selected,2*(Z^d)^(B.widths s))≤(Z^d)^((∑s:selected,B.widths s)+εg) ∧ _
    refine ⟨?_,?_,?_⟩
    · rw [hwidths]
      exact fun s=> hc.1 s
    · rw [hwidths]
      exact hc.2 selected
    · intro p hp
      have hp' : p∈Fintype.piFinset (fun s:selected=> livePrimes M H F.W 2 ((Z^d)^(D.ell s/d))) := by
        change p∈Fintype.piFinset (fun s:selected=> livePrimes M H (B.profile s) (B.upper s) ((Z^d)^(B.widths s))) at hp
        simpa only [hprofile,hupper,hwidths] using hp
      have hl' : ∀s:selected,((baseCharacter (B.data j)).modulus.absNorm:ℝ)<1*(Z^d)^(D.ell s/d) := by
        intro s
        have hh:=hl s
        change ((baseCharacter (B.data j)).modulus.absNorm:ℝ)<1*(Z^d)^(B.widths s) at hh
        simpa only [hwidths] using hh
      have hs' : ∀s t:selected,s≠t→2*(Z^d)^(D.ell s/d)<1*(Z^d)^(D.ell t/d) ∨
          2*(Z^d)^(D.ell t/d)<1*(Z^d)^(D.ell s/d) := by
        intro s t hst
        exact hs s t (fun he=> hst (Subtype.ext he))
      refine ⟨?_,?_,?_,?_,?_⟩
      · exact live_tuple_injective M H (fun _=> F.W) (fun _=>1) (fun _=>2)
          (fun s:selected=> D.ell s/d) (Z^d) hu (fun _=> F.complex_support) hs' p (by simpa only [Fintype.mem_piFinset] using hp')
      · exact live_tuple_admissible M H (B.data j) (fun _=> F.W) (fun _=>1) (fun _=>2)
          (fun s:selected=> D.ell s/d) (Z^d) hu (fun _=> F.complex_support) hl' hs' p (by simpa only [Fintype.mem_piFinset] using hp')
      · intro s
        change ((p s).absNorm:ℝ)≤2*(Z^d)^(B.widths s)
        rw [hwidths]
        exact (livePrime_data M H F.W 1 2 ((Z^d)^(D.ell s/d))
          (Real.rpow_pos_of_pos hu _) F.complex_support (p s) (Fintype.mem_piFinset.mp (by simpa only [Fintype.mem_piFinset] using hp') s)).2.2.2
      · exact sourceMoment_live_denominator M H F (B.data j) (Z^d)
          (fun s:selected=> D.ell s/d) hu hl' p (by simpa only [Fintype.mem_piFinset] using hp')
      · change ‖star (∏s:selected,primeProfile (B.profile s) ((Z^d)^(B.widths s)) (B.external s) (p s))/
          fixedBase (B.data j).η (B.data j).m (B.data j).f (∏s:selected,p s)‖≤1
        rw [hprofile,hwidths]
        exact sourceMoment_live_quotient_norm M H F (B.data j) (Z^d)
          (fun s:selected=> D.ell s/d) (fun s:selected=> B.external s) hu (fun s=> hz s) hl' p (by simpa only [Fintype.mem_piFinset] using hp')

end Source
end SevenEighths.PerturbedHeckeDetectorMomentPrimeGeometry
end
end OAI

#print axioms OAI.SevenEighths.PerturbedHeckeDetectorMomentPrimeGeometry.sourceMoment_fiber_prime_geometry_eventually

end LocalModule110
/- END RHZeroFreeExtension.moment_adapters.DetectorMomentPrimeGeometry -/

/- BEGIN original module RHZeroFreeExtension.moment_adapters.InverseMarkedReferencePrimeGates -/
section LocalModule111

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
namespace SevenEighths.PerturbedDetectorDictionaryInverseMarkedReference
open DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialPhysicalSlots
open DetectorDictionaryInverseRawInitialGates InverseInitialExcludedPeriod
open InverseInitialExcludedPool InverseInitialExcludedOverlap Filter CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O"=> HeckeFamily.O

theorem deleted_large_eventually {Label Slot:Type*}[Fintype Label][Fintype Slot]
    (data:Label→RowData)(ell:Slot→ℝ)(hell:∀s,0< ell s) :
    ∀ᶠZ:ℝ in atTop,1≤ Z ∧ ∀d:ℝ,0< d→∀j:Label,∀s:Slot,
      ((deletedBase (data j)).modulus.absNorm:ℝ)<(Z^d)^(ell s/d) := by
  have ht:∀ᶠZ:ℝ in atTop,∀j:Label,∀s:Slot,
      ((deletedBase (data j)).modulus.absNorm:ℝ)< Z^(ell s) := by
    apply Filter.eventually_all.mpr
    intro j
    apply Filter.eventually_all.mpr
    intro s
    exact (tendsto_rpow_atTop (hell s)).eventually (eventually_gt_atTop _)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht] with Z hZ ht
  refine ⟨hZ,?_⟩
  intro d hd j s
  rw [←Real.rpow_mul (by linarith:0≤ Z),mul_div_cancel₀ _ hd.ne']
  exact ht j s

theorem deletedBase_supported (data:RowData)(I:Ideal O)
    (hI:idealCoeff (deletedBase data) I≠0) : CanonicalQuadraticSieve.Supported I := by
  by_contra hn
  exact hI (deletedBase_zero_unsupported data I hn)

theorem deleted_source_live_prime {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.HighData Δ}
    (F:RHZeroFreeExtension.AnalyticHigh.SourceData D)(data:RowData)
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)
    (X:ℝ)(hX:0< X)(ζ:ℂ)(hζ:ζ.re≤1)
    (hlarge:((deletedBase data).modulus.absNorm:ℝ)< X)
    (P:Ideal O)(hP:P∈livePrimes M H F.W 2 X) :
    Prime P ∧ InverseInitialExcludedPool.outside (excluded data) P ∧
      idealCoeff (deletedBase data) P≠0 ∧ ‖idealCoeff (deletedBase data) P‖=1 ∧
      ‖star (primeProfile F.W X ζ P)/idealCoeff (deletedBase data) P‖≤1 := by
  have hd:=livePrime_data M H F.W 1 2 X hX F.complex_support P hP
  have hcop:=ProbeRaySlots.prime_coprime_of_norm_gt (deletedBase data) ⟨P,hd.1⟩
    (hlarge.trans_le (by simpa only [one_mul] using hd.2.2.1))
  have hn:=PrincipalSignalComparison.idealCoeff_norm_one_of_coprime (deletedBase data) P hd.1.ne_zero hcop
  have hne:=HeckeDetectorRelativePrime.idealCoeff_ne_zero_of_coprime (deletedBase data) P hd.1.ne_zero hcop
  have hout:outside (excluded data) P := by
    by_contra hh
    exact hne (deleted_zero_outside (baseCharacter data) (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data)) P hh)
  refine ⟨hd.1,hout,hne,hn,?_⟩
  rw [norm_div,norm_star,hn,div_one]
  exact PerturbedHeckeDetectorMomentPrimeGeometry.sourceMoment_primeProfile_norm F X ζ hζ P

end SevenEighths.PerturbedDetectorDictionaryInverseMarkedReference

end

end OAI

#print axioms OAI.SevenEighths.PerturbedDetectorDictionaryInverseMarkedReference.deleted_source_live_prime

end LocalModule111
/- END RHZeroFreeExtension.moment_adapters.InverseMarkedReferencePrimeGates -/

/- BEGIN original module RHZeroFreeExtension.moment_adapters.InverseMarkedReferenceDeletedEnergy -/
section LocalModule112

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff Topology
namespace SevenEighths.PerturbedDetectorDictionaryInverseMarkedReference
open DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeInverseAmplification HeckeDyadic CanonicalQuadraticSieve
open CanonicalRowCompletion ConcretePrimeRowBridge ConcreteTraceCRT
open InverseInitialDetectorSource
open InverseMoment InverseInitialProfile InverseInitialRawDictionary InverseInitialPhysicalSlots
open InverseInitialConjugateEnergy InverseInitialEnergyCallerWindow InverseInitialExcludedPeriod
open DetectorDictionaryInverseRawInitialGates DetectorDictionaryInverseRawConjugateGates
open IdealMobiusDivisorSum Filter
local notation "O"=> HeckeFamily.O

theorem deletedSelectedSource_tuple {ι:Type*}[Fintype ι](data:RowData)
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(W:ℝ→ℂ)(V:ι→ℝ→ℂ)
    (U r bW:ℝ)(b ell:ι→ℝ)(ζ:ι→ℂ)(u:O):
    deletedSelectedSource data M H W V U r 0 0 bW b ell ζ u=
      ∑x:Tuple (fun i=> livePrimes M H (V i) (b i) (U^(ell i))),
        (∏i,star (primeProfile (V i) (U^(ell i)) (ζ i) (x i).val)/
          idealCoeff (deletedBase data) (x i).val)*
        originalTotalPolynomial (originalSource U r bW) (∏i,(x i).val)
          (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1) W U r (∑i,ell i) u := by
  rw [sum_tuple_original (fun i=> livePrimes M H (V i) (b i) (U^(ell i)))
    (fun x=>(∏i,star (primeProfile (V i) (U^(ell i)) (ζ i) (x i))/
      idealCoeff (deletedBase data) (x i))*
      originalTotalPolynomial (originalSource U r bW) (∏i,x i)
        (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1) W U r (∑i,ell i) u)]
  unfold deletedSelectedSource
  apply Finset.sum_congr rfl
  intro x hx
  simp only [star_prod,map_prod,Finset.prod_div_distrib]
  have ht:twistedProfile W 0 0=W:=by
    funext t
    simp [twistedProfile,HeckeDyadic.shift]
  rw [ht]
  rfl

theorem deleted_source_energy {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.HighData Δ}
    (F:RHZeroFreeExtension.AnalyticHigh.SourceData D)
    (W:ℝ→ℂ)(ao bo:ℝ)(hao:0< ao)(hab:ao≤ bo)
    (hsW:Function.support W⊆Set.Icc ao bo)(hW:ContDiff ℝ ∞ W)
    (εm:ℝ)(hεm:0<εm)(K:ℕ):
    ∃degree:ℕ,∀data:RowData,∃C U₀:ℝ,0< C ∧ 1< U₀ ∧
    ∀U:ℝ,U₀≤ U →
    ∀{ι:Type}[Fintype ι],Fintype.card ι≤ K →
    ∀(M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(ell:ι→ℝ)(ζ:ι→ℂ),
      (∀i,0≤ ell i) → (∀i,(ζ i).re≤1) →
      (((Finset.univ:Finset ι):Set ι).PairwiseDisjoint
        (fun i=> livePrimes M H F.W 2 (U^(ell i)))) →
      (∀i,((deletedBase data).modulus.absNorm:ℝ)< U^(ell i)) →
    ∀r:ℝ,0≤ r → r+2*(∑i,ell i)<1 → 2*r+8*(∑i,ell i)<3 →
    ∀j∈idealDivisors (∏P∈excluded data,P),
    ∀rows:Finset O,(∀u∈rows,‖eisEmbedding u‖^2≤ U) → ∀θ:ℝ,
      (∑u∈rows,‖deletedSelectedSource data M H (childLogTest W θ) (fun _=> F.W)
        U (shiftedExponent data U r j) 0 0 bo (fun _=>2) ell ζ u‖^2)≤
        C*U^(1+εm)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨eta,heta,degree,henergy⟩:=padded_source_energy W ao bo hao hab hsW hW εm hεm K
  refine ⟨degree,?_⟩
  intro data
  obtain ⟨hq,hqset,hn,hperiod⟩:=raw_conjugate_base_gates data
  obtain ⟨C,U₀,hC,hU₀,henergy⟩:=henergy (deletedPeriod (basePeriod data)) hq
  obtain ⟨Ushift,hshift⟩:=eventually_atTop.mp (marked_shift_eventually data eta heta)
  refine ⟨C,max U₀ Ushift,hC,lt_max_of_lt_left hU₀,?_⟩
  intro U hU ι inst hK M neM H ell ζ hell hζ hdis hlarge r hr hfirst hsecond j hj rows hrows θ
  have hU0:U₀≤ U:=(le_max_left _ _).trans hU
  have hUone:1< U:=hU₀.trans_le hU0
  have hUp:0< U:=zero_lt_one.trans hUone
  have hjshift: r-eta≤ shiftedExponent data U r j ∧ shiftedExponent data U r j≤ r ∧
      U^(shiftedExponent data U r j)=U^r/(j.absNorm:ℝ):=
    (hshift U ((le_max_right _ _).trans hU)).2 j hj r
  let L:ι→Finset (Ideal O):=fun i=> livePrimes M H F.W 2 (U^(ell i))
  let coeff:ι→Ideal O→ℂ:=fun i P=> star (primeProfile F.W (U^(ell i)) (ζ i) P)/
    idealCoeff (deletedBase data) P
  have hg (i:ι)(P:Ideal O)(hP:P∈L i):
      Prime P ∧ InverseInitialExcludedPool.outside (excluded data) P ∧
      idealCoeff (deletedBase data) P≠0 ∧ ‖idealCoeff (deletedBase data) P‖=1 ∧
      ‖coeff i P‖≤1:=
    deleted_source_live_prime F data M H _ (Real.rpow_pos_of_pos hUp _) (ζ i) (hζ i) (hlarge i) P hP
  have hratio (i:ι)(P:Ideal O)(hP:P∈L i):((P.absNorm:ℝ)/U^(ell i))∈Set.Icc (1:ℝ) 2:=
    F.complex_support (Finset.mem_filter.mp hP).2
  have hh:=henergy U hU0 hK L ell coeff hell
    (fun i P hP=>(hg i P hP).1)
    (fun i P hP=> deletedBase_supported data P (hg i P hP).2.2.1)
    hdis hratio (fun i P hP=>(hg i P hP).2.2.2.2)
    (fun i P hP=> by rw [hqset];exact (hg i P hP).2.1)
    (fun _=> F.W) (fun _=> F.complex_support)
    (fun i P hP=>(Finset.mem_filter.mp hP).2)
    (idealCoeff (deletedBase data)).toMonoidHom (idealCoeff_norm_le_one (deletedBase data))
    hperiod (fun I hI=> raw_conjugate_zero_outside data I (by simpa [hqset] using hI))
    r (shiftedExponent data U r j) hr hjshift.1 hjshift.2.1 hfirst hsecond rows hrows θ
  simpa only [deletedSelectedSource_tuple,L,coeff] using hh

end SevenEighths.PerturbedDetectorDictionaryInverseMarkedReference

end

end OAI

#print axioms OAI.SevenEighths.PerturbedDetectorDictionaryInverseMarkedReference.deleted_source_energy

end LocalModule112
/- END RHZeroFreeExtension.moment_adapters.InverseMarkedReferenceDeletedEnergy -/

/- BEGIN original module RHZeroFreeExtension.moment_adapters.InverseMarkedReferenceFiberEnergy -/
section LocalModule113

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.PerturbedDetectorDictionaryInverseMarkedReference
open DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeInverseAmplification HeckeDyadic HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer InverseMoment InverseInitialProfile
open ConcreteTraceCRT ConcretePrimeRowBridge CanonicalRowCompletion
open DetectorDictionaryInverseRawInitialGates DetectorDictionaryInverseMarkedPhysicalRows
open InverseInitialPhysicalSlots IdealMobiusDivisorSum
local notation "O"=> HeckeFamily.O

theorem fiber_reference_energy {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.HighData Δ}
    (S:RHZeroFreeExtension.AnalyticHigh.SourceData D)
    (W:ℝ→ℂ)(ao bo:ℝ)(hao:0< ao)(hab:ao≤ bo)
    (hsW:Function.support W⊆Set.Icc ao bo)(hW:ContDiff ℝ ∞ W)
    (εm:ℝ)(hεm:0<εm)(K:ℕ):
    ∃degree:ℕ,∀data:RowData,∃C U₀:ℝ,0< C ∧ 1< U₀ ∧
    ∀U:ℝ,U₀≤ U →
    ∀(M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)
      {Label Slot:Type}{a ε tstar T allowance:ℝ}{i:ℕ}
      (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot),
      F.rowData=data → selected.card≤ K →
      (∀s∈selected,F.profile s=S.W) → (∀s∈selected,F.upper s=2) →
      (∀s∈selected,0≤ F.widths s) → (∀s∈selected,(F.external s).re≤1) →
      (((Finset.univ:Finset selected):Set selected).PairwiseDisjoint (fiberLists F selected)) →
      (∀s∈selected,((deletedBase data).modulus.absNorm:ℝ)< U^(F.widths s)) →
      0≤ F.r → F.r+2*(∑s∈selected,F.widths s)<1 →
      2*F.r+8*(∑s∈selected,F.widths s)<3 → ∀v:ℝ,
      (∑u∈F.rows,‖polynomial (F.family u F.label) true (childLogTest W v) (U^F.r) 0 0*
        F.physicalProduct selected u‖^2)≤ C*U^(1+εm)*((1+‖v‖)^degree)^2 := by
  have hsor (b:Bool):Function.support (orientedProfile b W)⊆Set.Icc ao bo := by
    cases b
    · exact hsW
    · intro x hx
      apply hsW
      simpa [orientedProfile] using hx
  have hWor (b:Bool):ContDiff ℝ ∞ (orientedProfile b W) := by
    cases b
    · exact hW
    · exact Complex.conjCLE.contDiff.comp hW
  choose J hj using fun b:Bool=> deleted_source_energy S (orientedProfile b W) ao bo hao hab
    (hsor b) (hWor b) εm hεm K
  refine ⟨∑b:Bool,J b,?_⟩
  intro data
  choose C U₀ hC hU₀ hb using fun b:Bool=> hj b data
  let Tbad:=idealDivisors (∏P∈excluded data,P)
  let Ctotal:ℝ:=((Tbad.card:ℝ)+1)^2*(∑b:Bool,C b)
  have hCsum:0<∑b:Bool,C b:=Finset.sum_pos (fun b _=> hC b) Finset.univ_nonempty
  refine ⟨Ctotal,max (U₀ false) (U₀ true),by dsimp [Ctotal];positivity,
    lt_max_of_lt_left (hU₀ false),?_⟩
  intro U hU M neM H Label Slot a ε tstar T allowance i F selected hdata hK hprofile hupper
    hell hext hdis hlarge hr hfirst hsecond v
  have hUb (b:Bool):U₀ b≤ U:=by cases b <;> exact le_trans (by simp) hU
  have hUone:1< U:=(hU₀ false).trans_le (hUb false)
  have hpr (s:selected):F.profile s=S.W:=hprofile s s.property
  have hup (s:selected):F.upper s=2:=hupper s s.property
  have hprof:(fun s:selected=> F.profile s)=(fun _=>(S.W:ℝ→ℂ)):=funext hpr
  have hups:(fun s:selected=> F.upper s)=(fun _=>2):=funext hup
  have hslots:∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (1:ℝ) (F.upper s) := by
    intro s hs x hx
    rw [hprofile s hs] at hx
    rw [hupper s hs]
    exact S.complex_support hx
  have hlarge':∀s∈selected,((deletedBase F.rowData).modulus.absNorm:ℝ)<1*U^(F.widths s):=by
    simpa only [hdata,one_mul] using hlarge
  have hphys:=fiber_child_rows_le_deleted_sources F selected W v bo (fun _=>1) hUone
    (fun x hx=>(hsW hx).2) hslots hlarge'
  rw [hdata] at hphys
  let rows:Finset O:=F.rows.image (fun u=> u.val)
  have hsum (f:O→ℝ):(∑u∈rows,f u)=∑u∈F.rows,f u.val:=
    Finset.sum_image (fun u _ w _ he=> Subtype.ext he)
  have hrows:∀u∈rows,‖eisEmbedding u‖^2≤ U := by
    intro u hu
    obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hu
    rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    exact F.row_norm w hw
  have hpow (b:Bool):((1+‖orientedFrequency b v‖)^(J b))^2≤
      ((1+‖v‖)^(∑b:Bool,J b))^2 := by
    have hn:‖orientedFrequency b v‖=‖v‖:=by cases b <;> simp [orientedFrequency]
    rw [hn]
    apply pow_le_pow_left₀ (by positivity)
    apply pow_le_pow_right₀ (by linarith [norm_nonneg v])
    exact Finset.single_le_sum (fun b _=> Nat.zero_le _) (Finset.mem_univ b)
  have hterm (j:Ideal O)(hj:j∈Tbad):
      (∑u∈F.rows,‖deletedSelectedSource data M H
        (childLogTest (orientedProfile F.reverse W) (orientedFrequency F.reverse v))
        (fun s:selected=> F.profile s) U (shiftedExponent data U F.r j)
        0 0 bo (fun s:selected=> F.upper s) (fun s:selected=> F.widths s)
        (fun s:selected=> F.external s) u.val‖^2)≤
      (∑b:Bool,C b)*U^(1+εm)*((1+‖v‖)^(∑b:Bool,J b))^2 := by
    rw [hprof,hups]
    have hdis':((Finset.univ:Finset selected):Set selected).PairwiseDisjoint
        (fun s:selected=> livePrimes M H S.W 2 (U^(F.widths s))) := by
      have heL:fiberLists F selected=(fun s:selected=> livePrimes M H S.W 2 (U^(F.widths s))) := by
        funext s
        dsimp only [fiberLists]
        rw [hpr s,hup s]
      rwa [heL] at hdis
    have hh:=hb F.reverse U (hUb F.reverse) (by simpa using hK)
      M H (fun s:selected=> F.widths s) (fun s:selected=> F.external s)
      (fun s=> hell s s.property) (fun s=> hext s s.property) hdis'
      (fun s=> hlarge s s.property) F.r hr
      (by simpa only [Finset.sum_coe_sort] using hfirst)
      (by simpa only [Finset.sum_coe_sort] using hsecond) j hj rows hrows (orientedFrequency F.reverse v)
    rw [hsum] at hh
    refine hh.trans ?_
    apply mul_le_mul _ (hpow F.reverse) (by positivity) (by positivity)
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
    exact Finset.single_le_sum (fun b _=>(hC b).le) (Finset.mem_univ F.reverse)
  refine hphys.trans ?_
  change (Tbad.card:ℝ)*(∑j∈Tbad,_)≤_
  calc
    _≤(Tbad.card:ℝ)*(∑j∈Tbad,(∑b:Bool,C b)*U^(1+εm)*
        ((1+‖v‖)^(∑b:Bool,J b))^2):=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _=(Tbad.card:ℝ)^2*(∑b:Bool,C b)*U^(1+εm)*((1+‖v‖)^(∑b:Bool,J b))^2:=by
      simp only [Finset.sum_const,nsmul_eq_mul];ring
    _≤ Ctotal*U^(1+εm)*((1+‖v‖)^(∑b:Bool,J b))^2:=by
      dsimp [Ctotal]
      gcongr
      nlinarith [show 0≤(Tbad.card:ℝ) by positivity]

end SevenEighths.PerturbedDetectorDictionaryInverseMarkedReference

end

end OAI

#print axioms OAI.SevenEighths.PerturbedDetectorDictionaryInverseMarkedReference.fiber_reference_energy

end LocalModule113
/- END RHZeroFreeExtension.moment_adapters.InverseMarkedReferenceFiberEnergy -/

/- BEGIN original module RHZeroFreeExtension.moment_adapters.DetectorInverseMarkedField -/
section LocalModule114

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.ProbeDetectorInverseMarkedField
open RHZeroFreeExtension.AnalyticHigh

open scoped Classical BigOperators Topology SchwartzMap ContDiff
namespace SevenEighths.PerturbedProbeDetectorInverseMarkedField
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorCoefficientTransfer
open ProbeHighRowFamily ProbeFinalAssembly Filter
open DetectorDictionaryInverseMarkedReference DetectorDictionaryInverseClippedUniform
local notation "O"=> HeckeFamily.O

variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)
local instance:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _

theorem source_batch_inverse_marked {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.HighData Δ}
    (S:RHZeroFreeExtension.AnalyticHigh.SourceData D):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,
    1< Z ∧ ∀d:ℝ,(1/200:ℝ)≤ d →
    ∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),
      B.data=sourceMomentData M H hH S.S S.exclusions.prime η →
      B.profile=(fun _ x=>(S.w x:ℂ)) → B.upper=(fun _=>2) →
      B.widths=(fun s=> D.ell s/d) → (∀s,(B.external s).re=17/50) →
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤ height →
    let F:=B.fiber bin label left right hne;
    ∀selected:Finset (Fin D.N),selected⊆F.slots →
      F.r+2*(∑s∈selected,F.widths s)<1 → 2*F.r+8*(∑s∈selected,F.widths s)<3 →
    ∀n:ℕ,n≤2 → ∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      (∑u∈F.rows,‖polynomial (F.family u F.label) true
        ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
        ((Z^d)^F.r) s t*F.physicalProduct selected u‖^2)≤
        (C*(1+height)^J)*(Z^d)^(1+D.t) := by
  obtain ⟨Jref,hreference⟩:=PerturbedDetectorDictionaryInverseMarkedReference.fiber_reference_energy S referenceWindow (1/18) (13/4)
    (by norm_num) (by norm_num)
    (fun x hx=> referenceWindow_support (subset_tsupport _ hx)) (referenceWindow.smooth ⊤)
    D.t D.t_pos D.N
  obtain ⟨J,Cfourier,hCfourier,hfourier⟩:=DetectorDictionaryInverseMarkedUniform.fiber_inverse_height_uniform Jref
  refine ⟨J,?_⟩
  intro η
  let data:=sourceMomentData M H hH S.S S.exclusions.prime η
  choose C U₀ hC hU₀ hb using fun label=> hreference (data label)
  let Csum:ℝ:=1+∑label,C label
  have hCsum:0< Csum:=by
    have hh:=Finset.sum_nonneg (fun label (_:label∈Finset.univ)=>(hC label).le)
    dsimp [Csum];linarith
  have hClabel (label):C label≤ Csum:=by
    have hh:=Finset.single_le_sum (fun label (_:label∈Finset.univ)=>(hC label).le) (Finset.mem_univ label)
    dsimp [Csum];linarith
  have hscale:∀ᶠZ:ℝ in atTop,∀label,∀d:ℝ,(1/200:ℝ)≤ d → U₀ label≤ Z^d := by
    apply Filter.eventually_all.mpr
    intro label
    exact HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) (U₀ label) (by norm_num)
  refine ⟨Cfourier*Csum,mul_pos hCfourier hCsum,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),hscale,
    deleted_large_eventually data D.ell (fun s=>(D.slots_bounds s).1),
    PerturbedHeckeDetectorMomentPrimeGeometry.sourceMoment_fiber_prime_geometry_eventually M H hH S η D.t D.t_pos] with Z hZ hscale hlarge hgeom
  refine ⟨hZ,?_⟩
  intro d hd a ε tstar T allowance i B hdata hprofile0 hupper hwidths hz bin label left right hne
    height hheight F selected hselected hfirst hsecond n hn s hs t ht
  have hd0:0< d:=by linarith
  have hUone:1< Z^d:=Real.one_lt_rpow hZ hd0
  have hUp:0< Z^d:=zero_lt_one.trans hUone
  have hprofile:B.profile=(fun _=>(S.W:ℝ→ℂ)) := by
    rw [hprofile0]
    funext j x
    exact (S.complex_eq x).symm
  have hfd:F.rowData=data label:=by change B.data label=data label;rw [hdata]
  have hfp (j):F.profile j=S.W:=by change B.profile j=S.W;rw [hprofile]
  have hfu (j):F.upper j=2:=by change B.upper j=2;rw [hupper]
  have hfw (j):F.widths j=D.ell j/d:=by change B.widths j=_;rw [hwidths]
  have hfe (j):(F.external j).re≤1:=by change (B.external j).re≤1;rw [hz j];norm_num
  have hdis:((Finset.univ:Finset selected):Set selected).PairwiseDisjoint (fiberLists F selected) := by
    intro j hj k hk hjk
    exact (hgeom.2 d hd a ε tstar T allowance i B hdata hprofile0 hupper hwidths hz
      bin label left right hne).1 j k (fun he=> hjk (Subtype.ext he))
  have hlargeF:∀j∈selected,((DetectorDictionaryInverseRawInitialGates.deletedBase (data label)).modulus.absNorm:ℝ)<
      (Z^d)^(F.widths j) := by
    intro j hj
    rw [hfw]
    exact hlarge.2 d hd0 label j
  have hr:0≤ F.r:=Real.logb_nonneg hUone (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have href (v:ℝ):
      (∑u∈F.rows,‖polynomial (F.family u F.label) true (childLogTest referenceWindow v)
        ((Z^d)^F.r) 0 0*F.physicalProduct selected u‖^2)≤
      (Csum*(Z^d)^(1+D.t))*(1+‖v‖)^(2*Jref) := by
    have hh:=hb label (Z^d) (hscale label d hd) M H F selected hfd
      (by simpa using Finset.card_le_univ selected) (fun j _=> hfp j) (fun j _=> hfu j)
      (fun j hj=>(F.widths_pos j (hselected hj)).le) (fun j _=> hfe j) hdis hlargeF hr hfirst hsecond v
    rw [(show 2*Jref=Jref*2 by omega),pow_mul]

    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right (hClabel label) (Real.rpow_nonneg hUp.le _)
  have hh:=hfourier F selected hUp (Csum*(Z^d)^(1+D.t)) (by positivity) href
    n hn s hs height t hheight ht
  convert hh using 1 ; ring

end SevenEighths.PerturbedProbeDetectorInverseMarkedField

end

end OAI

end LocalModule114
/- END RHZeroFreeExtension.moment_adapters.DetectorInverseMarkedField -/

/- BEGIN original module RHZeroFreeExtension.moment_adapters.DetectorInverseFields -/
section LocalModule115

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.ProbeDetectorInverseFields
open RHZeroFreeExtension.AnalyticHigh

open scoped Classical BigOperators Topology
namespace SevenEighths.PerturbedProbeDetectorInverseFields
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorCoefficientTransfer
open ProbeHighRowFamily ProbeFinalAssembly Filter
local notation "O"=> HeckeFamily.O
variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)
local instance:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _

private lemma raw_mono (data:RowData)(W:ℝ→ℂ)(c κ A B:ℝ)
    (hAB:A≤ B)(h:RawMoment data W c κ A):RawMoment data W c κ B:=by
  intro X D hX hD hcap rows hrows
  apply (h X D hX hD hcap rows hrows).trans
  gcongr

theorem source_batch_inverse_fields {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.HighData Δ}
    (S:RHZeroFreeExtension.AnalyticHigh.SourceData D)(counts:CountParameters M H D.t):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,
    1< Z ∧ ∀d:ℝ,(1/200:ℝ)≤ d →
    ∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),
      B.data=sourceMomentData M H hH S.S S.exclusions.prime η →
      B.profile=(fun _ x=>(S.w x:ℂ)) → B.upper=(fun _=>2) →
      B.widths=(fun s=> D.ell s/d) → (∀s,(B.external s).re=17/50) →
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤ height →
    let F:=B.fiber bin label left right hne;
    (∀n:ℕ,n≤2 → ∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let W:=twistProfile (logTest (orientedProfile F.reverse F.inverseProfile) n) s t;
      RawMoment F.rowData W (if 2*a-1≤5/6 then counts.cB else counts.cH)
        (if 2*a-1≤5/6 then counts.kB else counts.kH) (C*(1+height)^J) ∧
      RawMoment F.rowData (scaleProfile W) (if 2*a-1≤5/6 then counts.cB else counts.cH)
        (if 2*a-1≤5/6 then counts.kB else counts.kH) (C*(1+height)^J)) ∧
    (∀selected:Finset (Fin D.N),selected⊆F.slots →
      F.r+2*(∑s∈selected,F.widths s)<1 → 2*F.r+8*(∑s∈selected,F.widths s)<3 →
      ∀n:ℕ,n≤2 → ∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
        (∑u∈F.rows,‖polynomial (F.family u F.label) true
          ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
          ((Z^d)^F.r) s t*F.physicalProduct selected u‖^2)≤
          (C*(1+height)^J)*(Z^d)^(1+D.t)) := by
  obtain ⟨Jr,hr⟩ := ProbeDetectorInverseRawField.source_batch_inverse_raw
    M H hH S.S S.exclusions.prime D.t counts
  obtain ⟨Jm,hm⟩ := PerturbedProbeDetectorInverseMarkedField.source_batch_inverse_marked M H hH S
  refine ⟨Jr+Jm,?_⟩
  intro η
  obtain ⟨Cr,hCr,hr⟩ := hr η
  obtain ⟨Cm,hCm,hm⟩ := hm η
  refine ⟨Cr+Cm,add_pos hCr hCm,?_⟩
  filter_upwards [hm] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d hd a ε tstar T allowance i B hdata hprofile hupper hwidths hex
    bin label left right hne height hheight F
  have hU:0< Z^d := Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _
  have hscale:1≤1+height := by linarith
  have hraw:Cr*(1+height)^Jr≤(Cr+Cm)*(1+height)^(Jr+Jm) := by
    apply mul_le_mul
    · linarith
    · exact pow_le_pow_right₀ hscale (Nat.le_add_right _ _)
    · positivity
    · positivity
  have hmarked:Cm*(1+height)^Jm≤(Cr+Cm)*(1+height)^(Jr+Jm) := by
    apply mul_le_mul
    · linarith
    · exact pow_le_pow_right₀ hscale (Nat.le_add_left _ _)
    · positivity
    · positivity
  constructor
  · intro n hn s hs t ht
    have hh:=hr hU B hdata bin label left right hne height hheight n hn s hs t ht
    exact ⟨raw_mono _ _ _ _ _ _ hraw hh.1,raw_mono _ _ _ _ _ _ hraw hh.2⟩
  · intro selected hselected hfirst hsecond n hn s hs t ht
    have hh:=hZ.2 d hd a ε tstar T allowance i B hdata hprofile hupper hwidths hex
      bin label left right hne height hheight selected hselected hfirst hsecond n hn s hs t ht
    exact hh.trans (mul_le_mul_of_nonneg_right hmarked (Real.rpow_nonneg hU.le _))

end SevenEighths.PerturbedProbeDetectorInverseFields

end

end OAI

end LocalModule115
/- END RHZeroFreeExtension.moment_adapters.DetectorInverseFields -/

/- BEGIN original module RHZeroFreeExtension.moment_adapters.NaturalFixedRaySourceFixedIdeal -/
section LocalModule116

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators

namespace SevenEighths.PerturbedCenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

variable {Δ : ℝ} {D : RHZeroFreeExtension.AnalyticHigh.HighData Δ}

def sourceFixedIdeal (F : RHZeroFreeExtension.AnalyticHigh.SourceData D) : Ideal O :=
  F.modulus⊓Ideal.span {(72:O)}

lemma sourceFixedIdeal_ne_zero (F : RHZeroFreeExtension.AnalyticHigh.SourceData D) : sourceFixedIdeal F≠0 :=
  Ideal.inf_ne_bot_of_ne_bot (NeZero.ne F.modulus)
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0))

lemma sourceFixedIdeal_ne_top (F : RHZeroFreeExtension.AnalyticHigh.SourceData D) : sourceFixedIdeal F≠⊤ := by
  have hmem : Ideal.span {goodLambda}∈F.S := by
    apply F.exclusions.bad
    change Ideal.span {goodLambda}∈({Ideal.span {goodLambda},Ideal.span {(2:O)}} : Finset (Ideal O))
    simp
  have hle : F.modulus≤ Ideal.span {goodLambda} := by
    apply Ideal.dvd_iff_le.mp
    exact Finset.dvd_prod_of_mem (fun P : Ideal O=> P) hmem
  have hprime := (F.maximal _ hmem).isPrime
  intro h
  exact hprime.ne_top (top_le_iff.mp (h ▸ (inf_le_left.trans hle : sourceFixedIdeal F≤ Ideal.span {goodLambda})))

lemma sourceFixedIdeal_le_modulus (F : RHZeroFreeExtension.AnalyticHigh.SourceData D) : sourceFixedIdeal F≤ F.modulus := inf_le_left
lemma sourceFixedIdeal_le_72 (F : RHZeroFreeExtension.AnalyticHigh.SourceData D) : sourceFixedIdeal F≤ Ideal.span {(72:O)} := inf_le_right

def sourceExceptional (F : RHZeroFreeExtension.AnalyticHigh.SourceData D) (η : Character) (u : FreeRow) : Prop :=
  FixedInducingRow η (internalQ (sourceFixedIdeal F) η)
    (fixedBadMask*idealGenerator 1) 1 u.val

theorem source_retained_sector_nonprincipal (F : RHZeroFreeExtension.AnalyticHigh.SourceData D)
    (η : Character) (u : FreeRow) (hu : ¬sourceExceptional F η u)
    (θ : RayQuotient.Characters F.modulus ⊤) :
    ((naturalRow η u.val u.property.1).character.product
      (relativeCharacter F.modulus ⊤ le_top η θ)).residue≠1 :=
  internal_sector_nonprincipal F.modulus ⊤ le_top (naturalRow η u.val u.property.1)
    η θ (sourceFixedIdeal F) 1 (sourceFixedIdeal_le_modulus F) one_ne_zero u.property.1 hu

theorem source_energy_split (F : RHZeroFreeExtension.AnalyticHigh.SourceData D) (η : Character)
    (rows : Finset FreeRow) (f : FreeRow→ℂ) :
    (∑u∈rows,‖f u‖^2)=
      (∑u∈rows.filter (fun u=>¬sourceExceptional F η u),‖f u‖^2)+
      ∑u∈rows.filter (sourceExceptional F η),‖f u‖^2 := by
  simpa only [not_not] using
    (Finset.sum_filter_add_sum_filter_not rows (fun u=>¬sourceExceptional F η u)
      (fun u=>‖f u‖^2)).symm

end SevenEighths.PerturbedCenteredMomentNaturalFixedRaySource

end

end OAI

end LocalModule116
/- END RHZeroFreeExtension.moment_adapters.NaturalFixedRaySourceFixedIdeal -/

/- BEGIN original module RHZeroFreeExtension.moment_adapters.DetectorEnergyInitialState -/
section LocalModule117

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentDetectorEnergyInitialState
open OAI.SevenEighths.CenteredMomentDetectorPlainFiberSource
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators SchwartzMap Topology
open Filter

namespace SevenEighths.PerturbedCenteredMomentDetectorEnergyInitialState
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentRadialEligibleEnergy
open CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open PerturbedCenteredMomentNaturalFixedRaySource ConcretePrimeRowBridge
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorDictionary
open CenteredMomentFiniteProfileExceptional
local notation "O"=> HeckeFamily.O

def initialKeep (η:Character)(Q:Ideal O)(z:O):Prop:=
  z≠0 ∧ ¬FixedInducingRow η Q (fixedBadMask*idealGenerator 1) 1 z

def initialState (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ U δ:ℝ)
    (hU:1≤ U)(hδ:0≤δ)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0≤(Φ x).re)(hη:(η.modulus.absNorm:ℝ)≤ U^δ):NaturalState U 0 bΦ where
  character:=η
  fixedModulus:=Q
  puncture:=1
  radial := {
    keep := initialKeep η Q
    profile := Φ
    scale := U
    scale_pos := zero_lt_one.trans_le hU
    nonneg := fun z => hp _ }
  rowWidth:=1
  characterWidth:=δ
  base_ge_one:=hU
  row_nonneg:=by norm_num
  character_nonneg:=hδ
  scale_eq:=by simp
  modulus_bound:=hη
  puncture_ne_zero:=one_ne_zero
  puncture_bound:=by simp
  radial_support:=hs
  row_ne_zero:=fun _ h=> h.1
  nonexceptional:=fun _ h=> h.2

lemma initialState_width (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ U δ:ℝ)
    (hU:1≤ U)(hδ:0≤δ)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0≤(Φ x).re)(hη:(η.modulus.absNorm:ℝ)≤ U^δ):
    (initialState η Q Φ bΦ U δ hU hδ hs hp hη).width=1+δ:=rfl

def detectorProfiles (reverse:Bool)(j k:ℕ)(σ t:ℝ):Profiles (1/4) (9/4) where
  profile:=fun n=> detectorSchwartz reverse (if n=0 then j else k) σ t
  support:=by
    intro n x hx
    have he:(detectorSchwartz reverse (if n=0 then j else k) σ t:ℝ→ℂ)=
      HeckeInverseAmplification.twistProfile
        (HeckeDetectorCoefficientTransfer.orientedProfile reverse
          ((HeckeDetectorRowwisePolynomial.logProfile^[if n=0 then j else k])
            HeckeDetectorDyadicProfiles.positiveAnnular)) σ
          (HeckeDetectorCoefficientTransfer.orientedFrequency reverse t):=by
      funext y;exact detectorSchwartz_apply _ _ _ _ _
    rw [he] at hx
    exact detector_profile_support _ _ _ _ hx

theorem radialMajorant_support_bound:
    ∃bΦ:ℝ,0< bΦ ∧ Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ:=by
  obtain ⟨b,hb⟩:=radialMajorant_compact.isCompact.bddAbove
  refine ⟨max 1 b,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro x hx
  exact (hb (subset_tsupport _ hx)).trans (le_max_right _ _)

variable {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.HighData Δ}

theorem source_label_modulus_eventually (F:RHZeroFreeExtension.AnalyticHigh.SourceData D)
    (η:Character)(δ:ℝ)(hδ:0<δ):
    ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀label:Sum Bool (RayQuotient.Characters F.modulus ⊤),∀d:ℝ,(1/200:ℝ)≤ d→
      ((sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label).modulus.absNorm:ℝ)
        ≤(Z^d)^δ:=by
  have hc:∀ᶠZ:ℝ in atTop,∀label:Sum Bool (RayQuotient.Characters F.modulus ⊤),
      ((sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label).modulus.absNorm:ℝ)
        ≤ Z^((1/200)*δ):=by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop (mul_pos (by norm_num) hδ)).eventually (eventually_ge_atTop _)
  filter_upwards [hc,eventually_gt_atTop (1:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  intro label d hd
  apply (hz label).trans
  rw [←Real.rpow_mul (zero_lt_one.trans hZ).le]
  exact Real.rpow_le_rpow_of_exponent_le hZ.le (mul_le_mul_of_nonneg_right hd hδ.le)

lemma source_keep_iff (F:RHZeroFreeExtension.AnalyticHigh.SourceData D)(η:Character)(u:FreeRow):
    initialKeep η (internalQ (sourceFixedIdeal F) η) u.val↔¬sourceExceptional F η u:=by
  exact and_iff_right u.property.1

lemma source_fixed_gates (F:RHZeroFreeExtension.AnalyticHigh.SourceData D)(η:Character):
    internalQ (sourceFixedIdeal F) η≠0 ∧
    internalQ (sourceFixedIdeal F) η≤ F.modulus ∧
    internalQ (sourceFixedIdeal F) η≤η.modulus ∧
    internalQ (sourceFixedIdeal F) η≤ Ideal.span {(72:O)}:=
  ⟨internalQ_ne_zero _ (sourceFixedIdeal_ne_zero F) η,
    inf_le_left.trans (sourceFixedIdeal_le_modulus F),inf_le_right,
    inf_le_left.trans (sourceFixedIdeal_le_72 F)⟩

theorem source_energy_split_state (F:RHZeroFreeExtension.AnalyticHigh.SourceData D)(η:Character)
    (rows:Finset FreeRow)(f:FreeRow→ℂ):
    (∑u∈rows,‖f u‖^2)=
      (∑u∈rows.filter (fun u=> initialKeep η (internalQ (sourceFixedIdeal F) η) u.val),‖f u‖^2)+
      ∑u∈rows.filter (sourceExceptional F η),‖f u‖^2:=by
  simpa only [source_keep_iff] using source_energy_split F η rows f

theorem source_initial_states (F:RHZeroFreeExtension.AnalyticHigh.SourceData D):
    ∃bΦ:ℝ,0< bΦ ∧ ∀η:Character,∀δ:ℝ,0<δ→
      ∀ᶠZ:ℝ in atTop,∀label:Sum Bool (RayQuotient.Characters F.modulus ⊤),
      ∀d:ℝ,(1/200:ℝ)≤ d→
      let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label;
      ∃s:NaturalState (Z^d) 0 bΦ,
        s.character=η₀ ∧ s.fixedModulus=internalQ (sourceFixedIdeal F) η₀ ∧
        s.puncture=1 ∧ s.radial.profile=radialMajorant ∧ s.radial.scale=Z^d ∧
        s.radial.keep=initialKeep η₀ (internalQ (sourceFixedIdeal F) η₀) ∧
        s.rowWidth=1 ∧ s.characterWidth=δ ∧ s.width=1+δ:=by
  obtain ⟨bΦ,hbΦ,hs⟩:=radialMajorant_support_bound
  refine ⟨bΦ,hbΦ,?_⟩
  intro η δ hδ
  filter_upwards [source_label_modulus_eventually F η δ hδ] with Z hz
  intro label d hd
  have hd0:0< d:=by linarith
  have hU:1≤ Z^d:=(Real.one_lt_rpow hz.1 hd0).le
  dsimp only
  refine ⟨initialState (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label)
    (internalQ (sourceFixedIdeal F) (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label))
    radialMajorant bΦ (Z^d) δ hU hδ.le hs
    radialMajorant_nonneg (hz.2 label d hd),?_⟩
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end SevenEighths.PerturbedCenteredMomentDetectorEnergyInitialState

end

end OAI

end LocalModule117
/- END RHZeroFreeExtension.moment_adapters.DetectorEnergyInitialState -/

/- BEGIN original module RHZeroFreeExtension.moment_adapters.NaturalFixedRaySourceFreeExceptional -/
section LocalModule118

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.PerturbedCenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily UniqueFactorizationMonoid
open CenteredMomentDetectorDictionary CenteredExceptionalProfile CenteredExceptionalCount
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

theorem fixed_inducing_free_support (η : Character) (Q : Ideal O)
    (hQ0 : Q≠0) (hQ : Q≠⊤) (hQ72 : Q≤ Ideal.span {(72:O)}) (hQη : Q≤η.modulus)
    (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (u : FreeRow) (hu : FixedInducingRow η Q m 1 u.val) :
    u.val∈HeckeExceptionalRows.rows (normalizedFactors Q).toFinset := by
  obtain ⟨χ,ψ,hprim,hind,hψ,hχ⟩:=hu
  refine ⟨u.property.1,?_⟩
  intro P hP
  refine ⟨?_,u.property.2 P⟩
  by_contra hout
  have hp : Prime P:=prime_of_normalized_factor P hP
  let : P.IsMaximal:=(Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  obtain ⟨hl,h2,hQP⟩:=outside_fixed_support Q hQ0 hQ72 P hp hout
  have hηP : IsCoprime η.modulus P:=hQP.of_isCoprime_of_dvd_left (Ideal.dvd_iff_le.mpr hQη)
  have hz:=actual_row_numerator_valuation_zero η χ ψ hind Q hQ hQ72 hψ
    m 1 u.val hm one_ne_zero u.property.1 hml hm2
    (by simpa only [one_mul] using hχ) P hl h2 hQP hηP
  simp only [one_pow,one_mul,valuation] at hz
  have hpos:=Multiset.count_pos.mpr hP
  have hlt:=u.property.2 P
  omega

variable {Δ : ℝ} {D : RHZeroFreeExtension.AnalyticHigh.HighData Δ}

def sourceExceptionalBound (F : RHZeroFreeExtension.AnalyticHigh.SourceData D) (η : Character) : ℕ :=
  HeckeExceptionalRows.bound (normalizedFactors (internalQ (sourceFixedIdeal F) η)).toFinset

lemma source_exceptional_norm (F : RHZeroFreeExtension.AnalyticHigh.SourceData D) (η : Character)
    (u : FreeRow) (hu : sourceExceptional F η u) :
    (Ideal.span {u.val}).absNorm≤ sourceExceptionalBound F η := by
  apply HeckeExceptionalRows.row_norm_bound _
    (fun P hP=> prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP))
  apply fixed_inducing_free_support η (internalQ (sourceFixedIdeal F) η)
    (internalQ_ne_zero _ (sourceFixedIdeal_ne_zero F) η)
    (internalQ_ne_top _ (sourceFixedIdeal_ne_top F) η)
    (inf_le_left.trans (sourceFixedIdeal_le_72 F)) inf_le_right
    (fixedBadMask*idealGenerator 1)
    (mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero _ one_ne_zero))
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _)) u hu

theorem eventually_source_no_exceptional (F : RHZeroFreeExtension.AnalyticHigh.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),∀u : FreeRow,
      Z^(1/100:ℝ)≤ rowNorm u →
      ¬sourceExceptional F (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label) u := by
  have hh : ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      (sourceExceptionalBound F (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ)< Z^(1/100:ℝ) := by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/100)).eventually (eventually_gt_atTop _)
  filter_upwards [hh] with Z hz
  intro label u hu hex
  have hb : rowNorm u≤(sourceExceptionalBound F
      (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ) := by
    change ((Ideal.span {u.val}).absNorm:ℝ)≤_
    exact_mod_cast source_exceptional_norm F _ u hex
  exact (not_lt_of_ge (hu.trans hb)) (hz label)

theorem eventually_source_sector_gate (F : RHZeroFreeExtension.AnalyticHigh.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      ∀d : ℝ,∀u : FreeRow,Z^(1/100:ℝ)≤ rowNorm u→ rowNorm u≤ Z^(d-D.t) →
      ∀θ : RayQuotient.Characters F.modulus ⊤,
      let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
      let χ:=(CenteredMomentNaturalRowSource.naturalRow η₀ u.val u.property.1).character.product
        (relativeCharacter F.modulus ⊤ le_top η₀ θ)
      χ.residue≠1 ∧ (χ.modulus.absNorm:ℝ)≤ Z^d := by
  filter_upwards [eventually_source_no_exceptional F η,
    eventually_source_sector_capacity F.modulus ⊤ le_top F.S F.exclusions.prime η D.t D.t_pos]
    with Z hn hc
  intro label d u hlo hhi θ
  exact ⟨source_retained_sector_nonprincipal F _ u (hn label u hlo) θ,hc label d u hhi θ⟩

end SevenEighths.PerturbedCenteredMomentNaturalFixedRaySource

end

end OAI

end LocalModule118
/- END RHZeroFreeExtension.moment_adapters.NaturalFixedRaySourceFreeExceptional -/

/- BEGIN original module RHZeroFreeExtension.moment_adapters.DetectorPlainExceptional -/
section LocalModule119

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentDetectorPlainExceptional
open OAI.SevenEighths.CenteredMomentDetectorPlainFiberSource
open OAI.SevenEighths.CenteredMomentDetectorPlainSource
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators SchwartzMap Topology
open Filter

namespace SevenEighths.PerturbedCenteredMomentDetectorPlainExceptional
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSource
open CenteredMomentDetectorPlainFiberSource PerturbedCenteredMomentDetectorEnergyInitialState
open CenteredMomentRetainedEnergy CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentUncenteredTerminal CenteredMomentHeckeColumnWindow
open CenteredMomentSourceRectangleEnergy CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open PerturbedCenteredMomentNaturalFixedRaySource ProbeHighRowFamily HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentPrimeSlot CanonicalQuadraticSieve CenteredMomentRowNorm
open CenteredMomentSecondHeightFamily ConcreteTraceCRT ActualEisensteinCubic
local notation "O"=> HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}

def retainedSourceEnergy (keep:O→Prop)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(Φ:𝓢(ℝ,ℂ)):ℝ:=
  sourceRestrictedEnergy keep (finiteColumns (fiberPool F selected))
    (fiberCoefficient F η selected j k σ t) (heightCoeff η 0) Φ U /
    ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val))

theorem retained_positive_energy_le_source
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(η:Character)
    (selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(hU:0< U)
    (hkeep:∀u∈F.rows,keep u.val):
    (∑u∈F.rows,‖detectorPositiveRow F η selected j k σ t u‖^2)≤
      retainedSourceEnergy keep F η selected j k σ t Φ:=by
  let Q:=finiteColumns (fiberPool F selected)
  let c:=fun I:supportedColumns Q=> fiberCoefficient F η selected j k σ t I*heightCoeff η 0 I
  let rows:Finset O:=F.rows.image Subtype.val
  have ht:0<(U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val):=
    mul_pos (mul_pos (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _))
      (Finset.prod_pos (fun _ _=> Real.rpow_pos_of_pos hU _))
  have he (u:FreeRow):
      ‖detectorPositiveRow F η selected j k σ t u‖^2=
      ‖rowPolynomial Finset.univ (sourceGenerator Q) c u.val‖^2/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
    rw [detector_row_eq_source F η selected j k σ t u hU,
      CenteredMomentDivisorRawEnergy.normalized_norm_sq _ ht]
    congr 1
    exact congrArg (fun w : ℂ=>‖w‖^2)
      (height_source_row η 0 Q (fiberCoefficient F η selected j k σ t) u.val).symm
  have hb:=finite_energy_le_restricted keep Finset.univ
    (sourceGenerator Q) (sourceGenerator_supported Q) c Φ U hU rows
    (by
      intro z hz
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
      exact hkeep u hu) (fun z=> hΦ _) (by
      intro z hz
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
      have hn:‖eisEmbedding u.val‖^2/U∈Set.Icc (0:ℝ) 1:=by
        refine ⟨div_nonneg (sq_nonneg _) hU.le,(div_le_one hU).mpr ?_⟩
        rw [eisEmbedding_norm_sq_eq_absNorm_span]
        exact F.row_norm u hu
      rw [hone _ hn,Complex.one_re])
  calc
    _=(∑u∈F.rows,‖rowPolynomial Finset.univ (sourceGenerator Q) c u.val‖^2)/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
      simp_rw [he]
      rw [Finset.sum_div]
    _=(∑z∈rows,‖rowPolynomial Finset.univ (sourceGenerator Q) c z‖^2)/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
      rw [Finset.sum_image (fun x _ y _ hxy=> Subtype.val_injective hxy)]
    _≤_:=div_le_div_of_nonneg_right hb ht.le

variable {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.HighData Δ}

theorem source_fibers_eventually_retained (S:RHZeroFreeExtension.AnalyticHigh.SourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀(d a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      (∀u∈(B.fiber bin label J K hne).rows,
        initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀) u.val) ∧
      ((B.fiber bin label J K hne).rows.filter (sourceExceptional S η₀))=∅:=by
  filter_upwards [eventually_source_no_exceptional S η] with Z hz
  intro rows hrows d a ε tstar T allowance i B hB bin label J K hne η₀
  have hk:∀u∈(B.fiber bin label J K hne).rows,
      initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀) u.val:=by
    intro u hu
    apply (source_keep_iff S η₀ u).mpr
    apply hz label u
    apply hrows u
    apply hB
    simp only [Batch.fiber,HeckeDetectorFiberPartition.toFiber,
      HeckeDetectorFiberPartition.fiber,Finset.mem_filter] at hu
    exact hu.1
  refine ⟨hk,?_⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨hu,hex⟩:=Finset.mem_filter.mp hu
  exact ((source_keep_iff S η₀ u).mp (hk u hu)) hex

theorem source_exceptional_energy_eventually_zero (S:RHZeroFreeExtension.AnalyticHigh.SourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀label:Sum Bool (RayQuotient.Characters S.modulus ⊤),∀f:FreeRow→ℂ,
      (∑u∈rows.filter (sourceExceptional S
        (sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label)),‖f u‖^2)=0:=by
  filter_upwards [eventually_source_no_exceptional S η] with Z hz
  intro rows hrows label f
  apply Finset.sum_eq_zero
  intro u hu
  obtain ⟨hu,hex⟩:=Finset.mem_filter.mp hu
  exact False.elim ((hz label u (hrows u hu)) hex)

theorem source_batch_plain_retained (S:RHZeroFreeExtension.AnalyticHigh.SourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀d:ℝ,d≠0→∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=> D.ell s/d)→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      ∀selected:Finset (Fin D.N),∀j k:ℕ,∀σ t:ℝ,
      let F:=B.fiber bin label J K hne;
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2)≤
        retainedSourceEnergy (initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀))
          F η₀ selected j k σ t radialMajorant:=by
  filter_upwards [source_fibers_eventually_retained S η,
    eventually_source_slots_coprime S.modulus ⊤ le_top S.S S.exclusions.prime η
      D.ell (fun s=>(D.slots_bounds s).1) 1 (by norm_num),eventually_gt_atTop (1:ℝ)] with Z hret hcop hZ
  refine ⟨hZ,?_⟩
  intro rows hrows d hd a ε tstar T allowance i B hB hdata hprofile hwidth
    bin label J K hne selected j k σ t F η₀
  have hU:0< Z^d:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hdataF:F.rowData=momentData η₀:=by
    change B.data label=momentData η₀
    rw [hdata,sourceMomentData_base]
  have hMm:S.modulus≤ Ideal.span {rowMaskElement}:=source_product_le_rowMask S.S S.exclusions.bad
  have hη:∀s∈selected,∀I∈primePool S.modulus ⊤ (F.upper s) ((Z^d)^(F.widths s)),
      F.profile s ((I.absNorm:ℝ)/((Z^d)^(F.widths s)))≠0→IsCoprime I η₀.modulus:=by
    intro s hs I hI hn
    change I∈primePool S.modulus ⊤ (B.upper s) ((Z^d)^(B.widths s)) at hI
    change B.profile s ((I.absNorm:ℝ)/((Z^d)^(B.widths s)))≠0 at hn
    rw [hwidth] at hI
    rw [hwidth,hprofile] at hn
    exact hcop label s d hd (fun x=>(S.w x:ℂ)) (B.upper s)
      (by
        intro x hx
        have hn:S.w x≠0:=by simpa using hx
        exact (S.support hn).1.le) I hI hn
  rw [fiber_plain_energy_eq F η₀ hdataF hMm hU selected j k σ t hη]
  exact retained_positive_energy_le_source _ radialMajorant radialMajorant_nonneg radialMajorant_one
    F η₀ selected j k σ t hU (hret rows hrows d a ε tstar T allowance i B hB bin label J K hne).1

end SevenEighths.PerturbedCenteredMomentDetectorPlainExceptional

end

end OAI

end LocalModule119
/- END RHZeroFreeExtension.moment_adapters.DetectorPlainExceptional -/

/- BEGIN original module RHZeroFreeExtension.moment_adapters.DetectorPlainSlotProfile -/
section LocalModule120

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentDetectorPlainSlotProfile
open RHZeroFreeExtension.AnalyticHigh

open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
namespace SevenEighths.PerturbedCenteredMomentDetectorPlainSlotProfile
open HeckeFamily HeckeInverseAmplification HeckeDyadic CenteredMomentDetectorDictionary
open CenteredMomentRetainedEnergy
local notation "O"=> HeckeFamily.O
variable {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.HighData Δ}

lemma conjugate_source_support (F:RHZeroFreeExtension.AnalyticHigh.SourceData D):
    Function.support (fun x=> conj (F.W x))⊆Set.Icc (1:ℝ) 2 := by
  intro x hx
  exact F.complex_support (by simpa using hx)

private lemma conjugate_source_smooth (F : RHZeroFreeExtension.AnalyticHigh.SourceData D) :
    ContDiff ℝ ∞ (fun x => conj (F.W x)) := by
  exact Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)

def slotSchwartz (F:RHZeroFreeExtension.AnalyticHigh.SourceData D)(ζ:ℂ):𝓢(ℝ,ℂ):=
  interpolatedProfile (fun x=> conj (F.W x)) 1 2 (by norm_num)
    (conjugate_source_support F) (conjugate_source_smooth F)
    (1-ζ.re) (-ζ.im)

theorem slotSchwartz_apply (F:RHZeroFreeExtension.AnalyticHigh.SourceData D)(ζ:ℂ)(x:ℝ):
    slotSchwartz F ζ x=conj (F.W x*(x:ℂ)^(ζ-1)) := by
  rw [slotSchwartz,interpolatedProfile_apply]
  unfold twistProfile
  by_cases hw:F.W x=0
  · simp [hw]
  have hx:0< x:=lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (F.complex_support hw).1
  rw [map_mul,conj_positive_cpow _ hx]
  congr 1
  congr 1
  apply Complex.ext <;> simp [HeckeDyadic.shift]

theorem slotSchwartz_support (F:RHZeroFreeExtension.AnalyticHigh.SourceData D)(ζ:ℂ):
    Function.support (slotSchwartz F ζ:ℝ→ℂ)⊆Set.Icc (1:ℝ) 2 := by
  intro x hx
  apply F.complex_support
  intro hw
  exact hx (by rw [slotSchwartz_apply,hw,zero_mul,map_zero])

theorem slotSchwartz_smooth (F:RHZeroFreeExtension.AnalyticHigh.SourceData D)(ζ:ℂ):
    ContDiff ℝ ∞ (slotSchwartz F ζ:ℝ→ℂ):=(slotSchwartz F ζ).smooth ⊤

theorem slotSchwartz_norm (F:RHZeroFreeExtension.AnalyticHigh.SourceData D)(ζ:ℂ)(hζ:ζ.re≤1)(x:ℝ):
    ‖slotSchwartz F ζ x‖≤1 := by
  rw [slotSchwartz_apply,RCLike.norm_conj]
  by_cases hw:F.W x=0
  · simp [hw]
  have hx:=F.complex_support hw
  have hxpos:0< x:=lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hx.1
  have hW:‖F.W x‖≤1 := by
    rw [F.complex_eq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (F.bounded x).1]
    exact (F.bounded x).2
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  have hp:x^((ζ-1).re)≤1:=
    (Real.rpow_le_rpow_of_exponent_le hx.1 (by simp only [Complex.sub_re,Complex.one_re];linarith)).trans_eq
      (Real.rpow_zero _)
  simpa only [one_mul] using mul_le_mul hW hp (Real.rpow_nonneg hxpos.le _) zero_le_one

theorem physical_coefficient (F:RHZeroFreeExtension.AnalyticHigh.SourceData D)(η:Character)
    (P:ℝ)(ζ:ℂ)(I:Ideal O):
    physicalSlotCoefficient η F.W P ζ I=
      idealCoeff η.inverse I*slotSchwartz F ζ ((I.absNorm:ℝ)/P) := by
  rw [slotSchwartz_apply]
  rfl

theorem physical_coefficient_norm (F:RHZeroFreeExtension.AnalyticHigh.SourceData D)(η:Character)
    (P:ℝ)(ζ:ℂ)(hζ:ζ.re≤1)(I:Ideal O):
    ‖physicalSlotCoefficient η F.W P ζ I‖≤1 := by
  rw [physical_coefficient,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
