end

end OAI
end OAIOriginalModule1492

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramAnnularCount
Source SHA256: 74668d84719e3a951e4f323bba16f71a338eb93e6195c0237f9247086f1e12f8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1493


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma nonzero_norm_one_le (z : O) (hz : z≠0) : (1:ℝ)≤‖eisEmbedding z‖^2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hz))

theorem annular_element_count (F : Finset O) (b N : ℝ) (hb : 0≤b) (hN : 0≤N)
    (hzero : ∀z∈F,z≠0) (hbound : ∀z∈F,‖eisEmbedding z‖^2≤b*N) :
    (F.card:ℝ)≤128*b*N := by
  by_cases hF : F.Nonempty
  · obtain ⟨z,hz⟩ := hF
    have hscale : 1≤b*N := (nonzero_norm_one_le z (hzero z hz)).trans (hbound z hz)
    simpa only [mul_assoc] using DescentFiberCost.finite_element_count_real F (b*N) hscale hbound
  · rw [Finset.not_nonempty_iff_eq_empty.mp hF,Finset.card_empty,Nat.cast_zero]
    positivity

theorem annular_pair_count (F G : Finset O) (b N : ℝ) (hb : 0≤b) (hN : 0≤N)
    (hFzero : ∀z∈F,z≠0) (hGzero : ∀z∈G,z≠0)
    (hFbound : ∀z∈F,‖eisEmbedding z‖^2≤b*N)
    (hGbound : ∀z∈G,‖eisEmbedding z‖^2≤b*N) :
    ((F×ˢG).card:ℝ)≤(128*b)^2*N^2 := by
  rw [Finset.card_product,Nat.cast_mul]
  have hf := annular_element_count F b N hb hN hFzero hFbound
  have hg := annular_element_count G b N hb hN hGzero hGbound
  calc
    _ ≤ (128*b*N)*(128*b*N) := mul_le_mul hf hg (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1493

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramLatticeWindow
Source SHA256: 6edda56ed73b619b8452c10b912df76ad5b7da448e79ef7b97e5b15a9f356343
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1494



namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def shellLatticeColumns (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N) : Finset O :=
  (elementWindow_finite_support W hW N hN).toFinset

lemma shellLatticeColumns_mem (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N) (n : O) :
    n∈shellLatticeColumns W hW N hN ↔ W (‖eisEmbedding n‖^2/N)≠0 := by
  simp only [shellLatticeColumns,Set.Finite.mem_toFinset,Function.mem_support]
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  rfl

lemma shellLatticeColumns_nonzero (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b) (n : O)
    (hn : n∈shellLatticeColumns W hW N hN) : n≠0 := by
  intro hz
  have hh := (hs ((shellLatticeColumns_mem W hW N hN n).mp hn)).1
  simp only [hz,map_zero,norm_zero,zero_pow (by decide : 2≠0),zero_div] at hh
  linarith

lemma shellLatticeColumns_norm (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (a b : ℝ) (hs : Function.support W⊆Set.Icc a b) (n : O)
    (hn : n∈shellLatticeColumns W hW N hN) : ‖eisEmbedding n‖^2≤b*N :=
  (div_le_iff₀ hN).mp (hs ((shellLatticeColumns_mem W hW N hN n).mp hn)).2

lemma shell_lattice_support (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) (n m : O)
    (h : n∉shellLatticeColumns W hW N hN ∨ m∉shellLatticeColumns W hW N hN) :
    shellProfile W v U T (‖eisEmbedding n‖^2/N) (‖eisEmbedding m‖^2/N)=0 := by
  rcases h with h|h
  · apply shellProfile_zero_left
    simpa only [shellLatticeColumns_mem,not_not] using h
  · apply shellProfile_zero_right
    simpa only [shellLatticeColumns_mem,not_not] using h

lemma shell_lattice_summable (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) (f : O→O→ℂ) :
    Summable (fun m : O×O=>f m.1 m.2*shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)) := by
  apply summable_of_ne_finset_zero (s:=(shellLatticeColumns W hW N hN)×ˢ(shellLatticeColumns W hW N hN))
  intro m hm
  have h : m.1∉shellLatticeColumns W hW N hN ∨ m.2∉shellLatticeColumns W hW N hN := by simpa only [Finset.mem_product,not_and_or] using hm
  rw [shell_lattice_support W hW N hN U v T m.1 m.2 h,mul_zero]

lemma shell_lattice_tsum (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) (f : O→O→ℂ) :
    (∑'m : O×O,f m.1 m.2*shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N))=
      ∑n∈shellLatticeColumns W hW N hN,∑m∈shellLatticeColumns W hW N hN,
        f n m*shellProfile W v U T (‖eisEmbedding n‖^2/N) (‖eisEmbedding m‖^2/N) := by
  rw [tsum_eq_sum (s:=(shellLatticeColumns W hW N hN)×ˢ(shellLatticeColumns W hW N hN)) (by
    intro m hm
    have h : m.1∉shellLatticeColumns W hW N hN ∨ m.2∉shellLatticeColumns W hW N hN := by simpa only [Finset.mem_product,not_and_or] using hm
    rw [shell_lattice_support W hW N hN U v T m.1 m.2 h,mul_zero])]
  exact Finset.sum_product _ _ _

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1494

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowGramPoisson
Source SHA256: e1c3965801756a42476c88d277cbe77c03015e89f396b5e4cb07a96507646b5d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1495


namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowGram_pair_prefactor (C : CalibrationData) (W1 : ℝ→ℂ)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v Q : ℝ) (s t : {I : Id // Supported I}) :
    (lowGaussColumn C W1 Y σ v s*star (lowGaussColumn C W1 Y σ v t))*
      ((Q:ℂ)/((Real.sqrt (Ideal.absNorm s.val:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm t.val:ℝ):ℂ)))=
      ((Q/Y^3:ℝ):ℂ)*
        ((lowGramCoefficient C σ s*lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y))*
          star (lowGramCoefficient C σ t*lowGramProfile W1 v ((Ideal.absNorm t.val:ℝ)/Y))) := by
  calc
    _ = (Q:ℂ)*(lowGaussColumn C W1 Y σ v s/(Real.sqrt (Ideal.absNorm s.val:ℝ):ℂ))*
        star (lowGaussColumn C W1 Y σ v t/(Real.sqrt (Ideal.absNorm t.val:ℝ):ℂ)) := by
      simp only [Complex.star_def,map_mul,map_inv₀,Complex.conj_ofReal,div_eq_mul_inv,mul_inv_rev]
      ring
    _ = (Q:ℂ)*(lowGramScale Y*star (lowGramScale Y))*
        ((lowGramCoefficient C σ s*lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y))*
          star (lowGramCoefficient C σ t*lowGramProfile W1 v ((Ideal.absNorm t.val:ℝ)/Y))) := by
      rw [lowGaussColumn_unnormalized C W1 Y hY σ v s,lowGaussColumn_unnormalized C W1 Y hY σ v t]
      simp only [star_mul]
      ring
    _ = _ := by rw [lowGramScale_mul_star Y hY];simp only [div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv]

theorem lowGram_source_poisson (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ)
    (U : SchwartzMap ℝ ℂ) (Q : ℝ) (hQ : 0<Q) :
    gaussEnergy (lowGaussColumns W1 hW1 Y hY) (fun s=>primaryGenerator s.val)
      (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property)
      (lowGaussColumn C W1 Y σ v) U Q=
      ((Q/Y^3:ℝ):ℂ)*
        ∑s∈lowGaussColumns W1 hW1 Y hY,∑t∈lowGaussColumns W1 hW1 Y hY,
          ((lowGramCoefficient C σ s*lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y))*
            star (lowGramCoefficient C σ t*lowGramProfile W1 v ((Ideal.absNorm t.val:ℝ)/Y)))*
          ∑'h : O,actualCorrelation (primaryGenerator s.val) (primaryGenerator t.val)
            ((supported_span_primaryGenerator_iff s.val).mpr s.property)
            ((supported_span_primaryGenerator_iff t.val).mpr t.property) (-h)*
            paperRadialFourier U (Q*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator s.val*primaryGenerator t.val)‖^2) := by
  rw [gaussEnergy_poisson _ _ _ _ U Q hQ]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  have hes := congrArg Ideal.absNorm ((primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1)
  have het := congrArg Ideal.absNorm ((primaryGenerator_spec t.val (supported_primaryGenerator_ne_zero t.val t.property)).1)
  rw [hes,het,←mul_assoc,lowGram_pair_prefactor C W1 Y hY σ v Q s t,mul_assoc]

theorem lowGram_kernel_scale (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (s t : {I : Id // Supported I}) (h : O) :
    Q*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator s.val*primaryGenerator t.val)‖^2=
      ‖eisEmbedding h‖^2/((Y^2/Q)*((Ideal.absNorm s.val:ℝ)/Y)*((Ideal.absNorm t.val:ℝ)/Y)) := by
  simp_rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  rw [←Ideal.span_singleton_mul_span_singleton]
  rw [(primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1,
    (primaryGenerator_spec t.val (supported_primaryGenerator_ne_zero t.val t.property)).1,map_mul,Nat.cast_mul]
  field_simp

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1495

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramGcdSource
Source SHA256: 55e6534bc06ff1b66ce12bb41ec2be3b71b4610502db15ff360dd1c72af2b74f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1496



namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentCorrelation CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

lemma gcd_generator_left (I J : SupportedIdeal) :
    primaryGenerator I.val=primaryGenerator (gcdCommon I J).val*primaryGenerator (gcdLeft I J).val := by
  rw [←primaryGenerator_mul,gcd_common_left]

lemma gcd_generator_right (I J : SupportedIdeal) :
    primaryGenerator J.val=primaryGenerator (gcdCommon I J).val*primaryGenerator (gcdRight I J).val := by
  rw [←primaryGenerator_mul,gcd_common_right]

lemma gcd_generator_coprime (I J : SupportedIdeal) :
    IsCoprime (primaryGenerator (gcdLeft I J).val) (primaryGenerator (gcdRight I J).val) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [(primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (gcdLeft I J).property)).1,
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (gcdRight I J).property)).1]
  exact gcd_residual_coprime I J

theorem actual_gcd_lift (I J : SupportedIdeal) (k : O) :
    let C:=primaryGenerator (gcdCommon I J).val
    let n₁:=primaryGenerator (gcdLeft I J).val
    let n₂:=primaryGenerator (gcdRight I J).val
    actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) (C*k)=
      idealRowHom k (gcdLeft I J).val*star (idealRowHom (-k) (gcdRight I J).val)*
        sexticReciprocityPhase n₁ n₂*
          actualCommon C ((supported_span_primaryGenerator_iff _).mpr (gcdCommon I J).property) n₁ n₂ k := by
  dsimp only
  have h₁ := (supported_span_primaryGenerator_iff _).mpr (gcdLeft I J).property
  have h₂ := (supported_span_primaryGenerator_iff _).mpr (gcdRight I J).property
  have hp₁ : ConcretePrimeRowBridge.goodLambda^2∣primaryGenerator (gcdLeft I J).val-1 :=
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (gcdLeft I J).property)).2
  have hp₂ : ConcretePrimeRowBridge.goodLambda^2∣primaryGenerator (gcdRight I J).val-1 :=
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (gcdRight I J).property)).2
  have hh := actual_common_lift (primaryGenerator (gcdCommon I J).val)
    (primaryGenerator (gcdLeft I J).val) (primaryGenerator (gcdRight I J).val) k
    ((supported_span_primaryGenerator_iff _).mpr (gcdCommon I J).property) h₁ h₂ hp₁ hp₂
    (gcd_generator_coprime I J)
  simpa only [←gcd_generator_left I J,←gcd_generator_right I J,
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (gcdLeft I J).property)).1,
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (gcdRight I J).property)).1] using hh

theorem actual_gcd_frequency_source (I J : SupportedIdeal) (U : SchwartzMap ℝ ℂ) (Q : ℝ) :
    (∑'h : O,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) (-h)*
      paperRadialFourier U (Q*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))=
      ∑'k : O,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
        ((supported_span_primaryGenerator_iff _).mpr I.property)
        ((supported_span_primaryGenerator_iff _).mpr J.property) (primaryGenerator (gcdCommon I J).val*k)*
        paperRadialFourier U (Q*‖eisEmbedding (primaryGenerator (gcdCommon I J).val*k)‖^2/
          ‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2) := by
  have hneg := (Equiv.neg O).tsum_eq (fun h : O=>
    actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) h*
      paperRadialFourier U (Q*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))
  simp only [Equiv.neg_apply,map_neg,norm_neg] at hneg
  rw [hneg]
  have hh := actual_common_frequency_tsum (primaryGenerator (gcdCommon I J).val)
    (primaryGenerator (gcdLeft I J).val) (primaryGenerator (gcdRight I J).val)
    ((supported_span_primaryGenerator_iff _).mpr (gcdCommon I J).property)
    ((supported_span_primaryGenerator_iff _).mpr (gcdLeft I J).property)
    ((supported_span_primaryGenerator_iff _).mpr (gcdRight I J).property)
    (fun h=>paperRadialFourier U (Q*‖eisEmbedding h‖^2/
      ‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))
  simpa only [←gcd_generator_left I J,←gcd_generator_right I J] using hh

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1496

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramPrimaryLattice
Source SHA256: ca5d6293ecc2593ff36929083a4c0353027b1f1cba38d4ffcd0318a048cf323f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1497



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

abbrev PrimaryElement := {n : O // Supported (Ideal.span {n}) ∧ λ₀^2∣n-1}

def primaryIdealEquiv : SupportedIdeal≃PrimaryElement where
  toFun I := ⟨primaryGenerator I.val,(supported_span_primaryGenerator_iff _).mpr I.property,
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).2⟩
  invFun n := ⟨Ideal.span {n.val},n.property.1⟩
  left_inv I := Subtype.ext (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).1
  right_inv n := Subtype.ext (primaryGenerator_span n.val (supported_element_ne_zero _ n.property.1) n.property.2)

lemma primaryCoefficient_nonzero_supported (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (n : O) (hn : primaryCoefficient S hS σ n≠0) :
    Supported (Ideal.span {n}) ∧ λ₀^2∣n-1 := by
  have hp : λ₀^2∣n-1 := by
    by_contra h
    exact hn (by simp [primaryCoefficient,h])
  have hc : IsCoprime (calibrationForSet S hS).generator n := by
    by_contra h
    exact hn (by rw [primaryCoefficient,ite_eq_left hp,gramCoefficientExtension_zero S hS σ n h])
  have hb := calibration_generator_bad S hS hbad
  exact ⟨supported_of_coprime_bad _ n hb.1 hb.2 hc,hp⟩

lemma primary_factor_right (A n : O) (hA : λ₀^2∣A-1) (hAn : λ₀^2∣A*n-1) : λ₀^2∣n-1 := by
  have h := dvd_sub hAn (hA.mul_right n)
  convert h using 1 ; ring

lemma primaryCoefficient_residual (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (A n : O) (hA : λ₀^2∣A-1)
    (hn : primaryCoefficient S hS σ (A*n)≠0) :
    Supported (Ideal.span {n}) ∧ λ₀^2∣n-1 := by
  have hs := primaryCoefficient_nonzero_supported S hS hbad σ (A*n) hn
  have hsp : Supported (Ideal.span {A}*Ideal.span {n}) := by
    rw [Ideal.span_singleton_mul_span_singleton]
    exact hs.1
  exact ⟨((supported_mul_iff _ _).mp hsp).2,primary_factor_right A n hA hs.2⟩

theorem primary_ideal_tsum (f : O→ℂ)
    (hz : ∀n,¬(Supported (Ideal.span {n}) ∧ λ₀^2∣n-1)→f n=0) :
    (∑'I : SupportedIdeal,f (primaryGenerator I.val))=∑'n : O,f n := by
  have he := primaryIdealEquiv.tsum_eq (fun n : PrimaryElement=>f n.val)
  change (∑'I : SupportedIdeal,f (primaryGenerator I.val))=∑'n : PrimaryElement,f n.val at he
  rw [he]
  exact tsum_subtype_eq_of_support_subset (by intro n hn;by_contra h;exact hn (hz n h))

theorem primary_ideal_pair_tsum (f : O→O→ℂ)
    (hl : ∀n m,¬(Supported (Ideal.span {n}) ∧ λ₀^2∣n-1)→f n m=0)
    (hr : ∀n m,¬(Supported (Ideal.span {m}) ∧ λ₀^2∣m-1)→f n m=0) :
    (∑'I : SupportedIdeal,∑'J : SupportedIdeal,f (primaryGenerator I.val) (primaryGenerator J.val))=
      ∑'n : O,∑'m : O,f n m := by
  have hinner (n : O) : (∑'J : SupportedIdeal,f n (primaryGenerator J.val))=∑'m : O,f n m :=
    primary_ideal_tsum (fun m=>f n m) (fun m h=>hr n m h)
  simp_rw [hinner]
  apply primary_ideal_tsum (fun n=>∑'m : O,f n m)
  intro n hn
  simp only [hl n _ hn,tsum_zero]

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1497

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramLatticeSource
Source SHA256: 5e57d800caacd449f2fa0468a30ddf3de1a0d5652b8d4031cd981df5c46782d1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1498


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

lemma jointExtension_zero_off_primary_left (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k d : O)
    (hCd : λ₀^2∣C*d-1) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (n m : O) (hn : ¬(Supported (Ideal.span {n}) ∧ λ₀^2∣n-1)) :
    jointExtension S hS σ C k u a b r hr P hg c (d*n) (d*m)=0 := by
  have hz : primaryCoefficient S hS σ (C*(d*n))=0 := by
    by_contra h
    apply hn
    apply primaryCoefficient_residual S hS hbad σ (C*d) n hCd
    simpa only [mul_assoc] using h
  simp only [jointExtension,jointFixed,hz,zero_mul]

lemma jointExtension_zero_off_primary_right (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k d : O)
    (hCd : λ₀^2∣C*d-1) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (n m : O) (hm : ¬(Supported (Ideal.span {m}) ∧ λ₀^2∣m-1)) :
    jointExtension S hS σ C k u a b r hr P hg c (d*n) (d*m)=0 := by
  have hz : primaryCoefficient S hS σ (C*(d*m))=0 := by
    by_contra h
    apply hm
    apply primaryCoefficient_residual S hS hbad σ (C*d) m hCd
    simpa only [mul_assoc] using h
  simp only [jointExtension,jointFixed,hz,star_zero,mul_zero,zero_mul]

theorem jointExtension_ideal_lattice (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k d : O)
    (hCd : λ₀^2∣C*d-1) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ) (W : O→O→ℂ) :
    (∑'I : SupportedIdeal,∑'J : SupportedIdeal,
      jointExtension S hS σ C k u a b r hr P hg c (d*primaryGenerator I.val) (d*primaryGenerator J.val)*
        W (primaryGenerator I.val) (primaryGenerator J.val))=
      ∑'n : O,∑'m : O,jointExtension S hS σ C k u a b r hr P hg c (d*n) (d*m)*W n m := by
  apply primary_ideal_pair_tsum (fun n m=>jointExtension S hS σ C k u a b r hr P hg c (d*n) (d*m)*W n m)
  · intro n m hn
    rw [jointExtension_zero_off_primary_left S hS hbad σ C k d hCd u a b r hr P hg c n m hn,zero_mul]
  · intro n m hm
    rw [jointExtension_zero_off_primary_right S hS hbad σ C k d hCd u a b r hr P hg c n m hm,zero_mul]

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1498

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramMobiusLattice
Source SHA256: ecfa16f5b6220157bb39b0bb11eabead83d9f712d0a466d9fb1d1e21111e6302
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1499



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

lemma primary_product (C d : O) (hC : λ₀^2∣C-1) (hd : λ₀^2∣d-1) : λ₀^2∣C*d-1 := by
  have h := dvd_add (hC.mul_right d) hd
  convert h using 1 ; ring

theorem jointExtension_divisor_lattice (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k : O) (hC : λ₀^2∣C-1)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (D : SupportedIdeal) (W : O→O→ℂ) :
    (∑'I : SupportedIdeal,∑'J : SupportedIdeal,
      if D.val∣I.val ∧ D.val∣J.val then
        jointExtension S hS σ C k u a b r hr P hg c (primaryGenerator I.val) (primaryGenerator J.val)*
          W (primaryGenerator I.val) (primaryGenerator J.val) else 0)=
      ∑'n : O,∑'m : O,
        jointExtension S hS σ C k u a b r hr P hg c (primaryGenerator D.val*n) (primaryGenerator D.val*m)*
          W (primaryGenerator D.val*n) (primaryGenerator D.val*m) := by
  rw [supported_divisor_pair_tsum D (fun I J=>
    jointExtension S hS σ C k u a b r hr P hg c (primaryGenerator I.val) (primaryGenerator J.val)*
      W (primaryGenerator I.val) (primaryGenerator J.val))]
  simp only [supported_dilation_generator]
  have hd : λ₀^2∣primaryGenerator D.val-1 :=
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ D.property)).2
  exact jointExtension_ideal_lattice S hS hbad σ C k (primaryGenerator D.val) (primary_product C _ hC hd)
    u a b r hr P hg c (fun n m=>W (primaryGenerator D.val*n) (primaryGenerator D.val*m))

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1499

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramPhysicalScale
Source SHA256: fb99e339c680f2577938e7ced8103ffeaa6599947262630cb99c53cf052140ec
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1500



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

 def residualScale (C D : SupportedIdeal) (Y : ℝ) : ℝ :=
  Y/((Ideal.absNorm C.val:ℝ)*Ideal.absNorm D.val)

lemma residualScale_pos (C D : SupportedIdeal) (Y : ℝ) (hY : 0<Y) : 0<residualScale C D Y := by
  have hc : (0:ℝ)<Ideal.absNorm C.val := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr C.property.1)
  have hd : (0:ℝ)<Ideal.absNorm D.val := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr D.property.1)
  exact div_pos hY (mul_pos hc hd)

lemma residual_column_ratio (C D I : SupportedIdeal) (Y : ℝ) (hY : 0<Y) :
    (Ideal.absNorm (supportedIdealProduct C (supportedIdealProduct D I)).val:ℝ)/Y=
      (Ideal.absNorm I.val:ℝ)/residualScale C D Y := by
  simp only [supportedIdealProduct,map_mul,Nat.cast_mul,residualScale]
  field_simp

 def frequencyScale (C : SupportedIdeal) (k : O) (Y Q : ℝ) : ℝ :=
  (Ideal.absNorm C.val:ℝ)*‖eisEmbedding k‖^2/(Y^2/Q)

lemma frequencyScale_nonneg (C : SupportedIdeal) (k : O) (Y Q : ℝ) (hQ : 0≤Q) :
    0≤frequencyScale C k Y Q := by unfold frequencyScale;positivity

theorem original_kernel_residual_scale (C D I J : SupportedIdeal) (k : O)
    (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q) :
    Q*‖eisEmbedding (primaryGenerator C.val*k)‖^2/
      ‖eisEmbedding (primaryGenerator (supportedIdealProduct C (supportedIdealProduct D I)).val*
        primaryGenerator (supportedIdealProduct C (supportedIdealProduct D J)).val)‖^2=
      frequencyScale C k Y Q/
        (((Ideal.absNorm I.val:ℝ)/residualScale C D Y)*((Ideal.absNorm J.val:ℝ)/residualScale C D Y)) := by
  rw [lowGram_kernel_scale Y Q hY hQ _ _ (primaryGenerator C.val*k),
    residual_column_ratio C D I Y hY,residual_column_ratio C D J Y hY]
  rw [map_mul,norm_mul,mul_pow,ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    (primaryGenerator_spec C.val (supported_primaryGenerator_ne_zero C.val C.property)).1]
  unfold frequencyScale
  ring

lemma physicalPoint_first_norm (N : ℝ) (hN : 0<N) (m : O×O) :
    ‖(WithLp.ofLp (ProbeGramLatticeDecay.physicalPoint N m)).1‖^2=‖eisEmbedding m.1‖^2/N := by
  simp only [ProbeGramLatticeDecay.physicalPoint,ProbeGramLatticeDecay.point,WithLp.ofLp_toLp]
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.sqrt_pos.mpr hN),div_pow,Real.sq_sqrt hN.le]

lemma physicalPoint_second_norm (N : ℝ) (hN : 0<N) (m : O×O) :
    ‖(WithLp.ofLp (ProbeGramLatticeDecay.physicalPoint N m)).2‖^2=‖eisEmbedding m.2‖^2/N := by
  simp only [ProbeGramLatticeDecay.physicalPoint,ProbeGramLatticeDecay.point,WithLp.ofLp_toLp]
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.sqrt_pos.mpr hN),div_pow,Real.sq_sqrt hN.le]

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1500

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramSourceBlock
Source SHA256: a4ebe1af82819e3b2bb0d3bd97f53020ba52144f36fc38fdcd9d085c79c7b82c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1501




namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge UniqueFactorizationMonoid ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma jointProfile_physicalPoint (W : ℝ→ℂ) (U : SchwartzMap ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (v T : ℝ) (hT : 0≤T) (N : ℝ) (hN : 0<N) (m : O×O) :
    ProbeGramJointConstruction.jointProfile W U a b ha hab hs hW v T hT
      (ProbeGramLatticeDecay.physicalPoint N m)=
      shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N) := by
  rw [ProbeGramJointConstruction.jointProfile_apply]
  unfold ProbeGramJointConstruction.rawProfile ProbeGramJointConstruction.q1 ProbeGramJointConstruction.q2
  change lowGramProfile W v _ * star (lowGramProfile W v _) * _ = _
  have h₁ : ‖WithLp.fst (ProbeGramLatticeDecay.physicalPoint N m)‖^2=‖eisEmbedding m.1‖^2/N := physicalPoint_first_norm N hN m
  have h₂ : ‖WithLp.snd (ProbeGramLatticeDecay.physicalPoint N m)‖^2=‖eisEmbedding m.2‖^2/N := physicalPoint_second_norm N hN m
  rw [h₁,h₂]
  rfl

theorem literal_nonexceptional_source (A B : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃(J : ℕ)(H : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a₀ b₀)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧
      ∀{ι : Type*}[Fintype ι],∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C k : O)(_hC : C≠0)(_hk0 : k≠0)(u : Oˣ)(a b : ℕ)(r : O)
      (hr : Supported (Ideal.span {r})),k=u.val*goodLambda^a*(2:O)^b*r→
      ∀(P : ι→Id)[_hmax : ∀i,(P i).IsMaximal](hg : ∀i,goodLambda∉P i)(c : ι→ℕ),
      (∀i,1≤c i)→Ideal.span {C}=∏i,P i^c i→
      ∀(p : Id)[_hpmax : p.IsMaximal],p≠0→∀_hgp : goodLambda∉p,
      ringChar (O⧸p)≠2→(¬p∣jointFixedModulus S hS)→(¬p∣∏i,P i)→
      (¬6∣(normalizedFactors (Ideal.span {k})).count p)→
      ∀(U : SchwartzMap ℝ ℂ)(v T : ℝ),0≤T→∀(d : O)(N : ℝ),0<N→
      Summable (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)) ∧
      ‖∑'m : O×O,jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)‖≤
        K*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J/(1+T)^B*
          (Ideal.absNorm (Ideal.span {C}):ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm (Ideal.span {C})*
            Ideal.absNorm (Ideal.span {k})/N)^A) := by
  obtain ⟨H₀,K₀,hK₀,hblock⟩ := literal_nonexceptional_block A hA a₀ b₀ ha₀ hab
  obtain ⟨J,H,hprofile⟩ := ProbeGramJointProfile.jointProfile_uniform_degree a₀ b₀ ha₀ hab B H₀
  refine ⟨J,H,?_⟩
  intro W hs hW
  obtain ⟨K₁,hK₁,hprofile⟩ := hprofile W hs hW
  refine ⟨K₀*K₁,mul_pos hK₀ hK₁,?_⟩
  intro ι inst S hS σ C k hC hk0 u a b r hr hk P hmax hg c hc hfac p hpmax hp0 hgp hchar hfixed hcommon he U v T hT d N hN
  let V := ProbeGramJointConstruction.jointProfile W U a₀ b₀ ha₀ hab hs hW v T hT
  have hv := ProbeGramJointConstruction.jointProfile_annularSupport W U a₀ b₀ ha₀ hab hs hW v T hT
  have hb := hblock S hS σ C k hC hk0 u a b r hr hk P hg c hc hfac p hp0 hgp hchar hfixed hcommon he V hv d N hN
  have hfun : (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
      V (ProbeGramLatticeDecay.physicalPoint N m))=
      (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)) := by
    funext m
    rw [jointProfile_physicalPoint W U a₀ b₀ ha₀ hab hs hW v T hT N hN m]
  rw [hfun] at hb
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hm : 0≤min (1:ℝ) (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm (Ideal.span {C})*
      Ideal.absNorm (Ideal.span {k})/N)^A) := by positivity
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hprofile U v T hT) hK₀.le)
        (Nat.cast_nonneg (Ideal.absNorm (Ideal.span {C})))) (sq_nonneg N)) hm
  convert hh using 1 ; ring

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1501

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramWindowMobius
Source SHA256: 7ca32dbbb91f3ab9fdd048ebb3d78a2c7372a93c5537c241db5bf50146e89bb9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1502




namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT CenteredMomentMobiusRegroup UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

lemma primary_norm (I : SupportedIdeal) :
    ‖eisEmbedding (primaryGenerator I.val)‖^2=(Ideal.absNorm I.val:ℝ) := by
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).1]

lemma shell_dilated_column (D I : SupportedIdeal) (N : ℝ) :
    (Ideal.absNorm (supportedIdealProduct D I).val:ℝ)/N=
      ‖eisEmbedding (primaryGenerator I.val)‖^2/(N/Ideal.absNorm D.val) := by
  rw [primary_norm,supported_dilation_norm,Nat.cast_mul]
  rw [div_div_eq_mul_div]
  ring

lemma shell_window_support (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) (I J : SupportedIdeal)
    (h : I∉lowGaussColumns W hW N hN ∨ J∉lowGaussColumns W hW N hN) :
    shellProfile W v U T ((Ideal.absNorm I.val:ℝ)/N) ((Ideal.absNorm J.val:ℝ)/N)=0 := by
  rcases h with h|h
  · apply shellProfile_zero_left
    simpa only [lowGaussColumns_mem,not_not] using h
  · apply shellProfile_zero_right
    simpa only [lowGaussColumns_mem,not_not] using h

theorem original_window_mobius_lattice (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k : O) (hC : λ₀^2∣C-1)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) :
    (∑I∈lowGaussColumns W hW N hN,∑J∈lowGaussColumns W hW N hN,
      if IsCoprime I.val J.val then
        jointExtension S hS σ C k u a b r hr P hg c (primaryGenerator I.val) (primaryGenerator J.val)*
          shellProfile W v U T ((Ideal.absNorm I.val:ℝ)/N) ((Ideal.absNorm J.val:ℝ)/N) else 0)=
      ∑D∈divisorPool (lowGaussColumns W hW N hN) Subtype.val,(moebius D:ℂ)*
        ∑'n : O,∑'m : O,
          jointExtension S hS σ C k u a b r hr P hg c (primaryGenerator D*n) (primaryGenerator D*m)*
            shellProfile W v U T (‖eisEmbedding n‖^2/(N/Ideal.absNorm D))
              (‖eisEmbedding m‖^2/(N/Ideal.absNorm D)) := by
  let F := lowGaussColumns W hW N hN
  let f := fun I J : SupportedIdeal=>jointExtension S hS σ C k u a b r hr P hg c
    (primaryGenerator I.val) (primaryGenerator J.val)*
      shellProfile W v U T ((Ideal.absNorm I.val:ℝ)/N) ((Ideal.absNorm J.val:ℝ)/N)
  have hf : ∀I J,I∉F ∨ J∉F→f I J=0 := by
    intro I J h
    dsimp [f]
    rw [shell_window_support W hW N hN U v T I J h,mul_zero]
  change (∑I∈F,∑J∈F,if IsCoprime I.val J.val then f I J else 0)=_
  rw [finite_pair_mobius_dilation F F f hf]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  let D₀ := poolDivisor F D
  have hd : D₀.val=D := poolDivisor_val F D hD
  have hdp : λ₀^2∣primaryGenerator D₀.val-1 :=
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ D₀.property)).2
  have he := jointExtension_ideal_lattice S hS hbad σ C k (primaryGenerator D₀.val)
    (primary_product C _ hC hdp) u a b r hr P hg c
    (fun n m=>shellProfile W v U T (‖eisEmbedding n‖^2/(N/Ideal.absNorm D₀.val))
      (‖eisEmbedding m‖^2/(N/Ideal.absNorm D₀.val)))
  dsimp only [f]
  simp only [supported_dilation_generator,shell_dilated_column]
  convert he using 1
  rw [hd]

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1502

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramCommonSource
Source SHA256: 0074d2abd52ad97dd071591523545937c1c9988768486f38ba8f3d957c1efef1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1503



namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT CenteredMomentMobiusRegroup UniqueFactorizationMonoid
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

def commonResidualScale (C : SupportedIdeal) (Y : ℝ) : ℝ := Y/Ideal.absNorm C.val
lemma commonResidualScale_pos (C : SupportedIdeal) (Y : ℝ) (hY : 0<Y) : 0<commonResidualScale C Y :=
  div_pos hY (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr C.property.1))
lemma common_column_ratio (C I : SupportedIdeal) (Y : ℝ) :
    (Ideal.absNorm (supportedIdealProduct C I).val:ℝ)/Y=(Ideal.absNorm I.val:ℝ)/commonResidualScale C Y := by
  rw [supported_dilation_norm,Nat.cast_mul,commonResidualScale,div_div_eq_mul_div]
  ring
lemma common_kernel_scale (C I J : SupportedIdeal) (k : O) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q) :
    Q*‖eisEmbedding (primaryGenerator C.val*k)‖^2/
      ‖eisEmbedding (primaryGenerator (supportedIdealProduct C I).val*primaryGenerator (supportedIdealProduct C J).val)‖^2=
      frequencyScale C k Y Q/
        (((Ideal.absNorm I.val:ℝ)/commonResidualScale C Y)*((Ideal.absNorm J.val:ℝ)/commonResidualScale C Y)) := by
  rw [lowGram_kernel_scale Y Q hY hQ,common_column_ratio,common_column_ratio,
    map_mul,norm_mul,mul_pow,primary_norm]
  unfold frequencyScale
  ring

theorem original_common_window_source (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C : SupportedIdeal) (k : O)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (hpr : λ₀^2∣r-1) (hk : k=u.val*λ₀^a*(2:O)^b*r)
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (hc : ∀i,1≤c i) (hcop : Pairwise (Function.onFun IsCoprime P)) (he : C.val=∏i,P i^c i)
    [Fintype (O⧸∏i,P i^c i)] [∀i,Fintype (O⧸P i^c i)]
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    let N:=commonResidualScale C Y
    let hN:=commonResidualScale_pos C Y hY
    let F:=lowGaussColumns W hW N hN
    (∑I∈F,∑J∈F,if IsCoprime I.val J.val then
      (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C I)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C I).val:ℝ)/Y))*
      star (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C J)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C J).val:ℝ)/Y))*
      actualCorrelation (primaryGenerator (supportedIdealProduct C I).val)
        (primaryGenerator (supportedIdealProduct C J).val)
        ((supported_span_primaryGenerator_iff _).mpr (supportedIdealProduct C I).property)
        ((supported_span_primaryGenerator_iff _).mpr (supportedIdealProduct C J).property)
        (primaryGenerator C.val*k)*
      paperRadialFourier U (Q*‖eisEmbedding (primaryGenerator C.val*k)‖^2/
        ‖eisEmbedding (primaryGenerator (supportedIdealProduct C I).val*primaryGenerator (supportedIdealProduct C J).val)‖^2)
      else 0)=
      ∑D∈divisorPool F Subtype.val,(moebius D:ℂ)*∑'n : O,∑'m : O,
        jointExtension S hS σ (primaryGenerator C.val) k u a b r hr P hg c (primaryGenerator D*n) (primaryGenerator D*m)*
          shellProfile W v U (frequencyScale C k Y Q) (‖eisEmbedding n‖^2/(N/Ideal.absNorm D))
            (‖eisEmbedding m‖^2/(N/Ideal.absNorm D)) := by
  dsimp only
  have hpc : λ₀^2∣primaryGenerator C.val-1 :=
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ C.property)).2
  rw [←original_window_mobius_lattice S hS hbad σ (primaryGenerator C.val) k hpc
    u a b r hr P hg c W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)
    U v (frequencyScale C k Y Q)]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  split_ifs with hIJ
  · have hni : Supported (Ideal.span {primaryGenerator I.val}) := (supported_span_primaryGenerator_iff _).mpr I.property
    have hnj : Supported (Ideal.span {primaryGenerator J.val}) := (supported_span_primaryGenerator_iff _).mpr J.property
    have hpi : λ₀^2∣primaryGenerator I.val-1 := (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).2
    have hpj : λ₀^2∣primaryGenerator J.val-1 := (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ J.property)).2
    have hij : IsCoprime (primaryGenerator I.val) (primaryGenerator J.val) := by
      apply (Ideal.isCoprime_span_singleton_iff _ _).mp
      simpa only [(primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).1,
        (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ J.property)).1] using hIJ
    have hf : Ideal.span {primaryGenerator C.val}=∏i,P i^c i := by
      rw [(primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ C.property)).1,he]
    rw [jointExtension_source S hS σ (primaryGenerator C.val) k
      ((supported_span_primaryGenerator_iff _).mpr C.property) u a b r hr hpr hk P hg c hc hcop hf
      _ _ hni hnj hpi hpj hij]
    rw [lowGramCoefficient_eq_primary S hS hbad σ,lowGramCoefficient_eq_primary S hS hbad σ,
      common_kernel_scale C I J k Y Q hY hQ,common_column_ratio,common_column_ratio]
    simp only [supported_dilation_generator,shellProfile,star_mul]
    ring
  · rfl

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1503

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramCanonical
Source SHA256: 358f7b0daa24d6c9c2ca50672ab84dbbe46e67eb270b4dc61ca6a614cedce532
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1504



namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

abbrev GramFrequency := {k : O // k≠0}
abbrev GramPrime (C : SupportedIdeal) := {P : Id // P∈IdealMobiusDivisorSum.primeSupport C.val}
def gramPrime (C : SupportedIdeal) (P : GramPrime C) : Id := P.val
instance gramPrimeMaximal (C : SupportedIdeal) (P : GramPrime C) : (gramPrime C P).IsMaximal :=
  (Ideal.isPrime_of_prime (support_prime P.property)).isMaximal (support_prime P.property).ne_zero

def gramExponent (C : SupportedIdeal) (P : GramPrime C) : ℕ := (normalizedFactors C.val).count P.val
lemma gramExponent_pos (C : SupportedIdeal) (P : GramPrime C) : 1≤gramExponent C P :=
  Multiset.count_pos.mpr (Multiset.mem_toFinset.mp P.property)
lemma gramPrime_good (C : SupportedIdeal) (P : GramPrime C) : λ₀∉gramPrime C P :=
  (supported_factors_good C.val C.property P.val (Multiset.mem_toFinset.mp P.property)).2.1
lemma gramPrime_coprime (C : SupportedIdeal) : Pairwise (Function.onFun IsCoprime (gramPrime C)) := by
  intro P Q hpq
  exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hpq)
lemma gramPrime_product (C : SupportedIdeal) : C.val=∏P : GramPrime C,gramPrime C P^gramExponent C P := by
  calc
    C.val=(normalizedFactors C.val).prod := (Ideal.prod_normalizedFactors_eq_self C.property.1).symm
    _=∏P∈IdealMobiusDivisorSum.primeSupport C.val,P^(normalizedFactors C.val).count P := Finset.prod_multiset_count _
    _=_ := (Finset.prod_coe_sort _ _).symm

instance gramPrimePowerFinite (C : SupportedIdeal) (P : GramPrime C) :
    Finite (O⧸gramPrime C P^gramExponent C P) :=
  Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ (support_prime P.property).ne_zero)
instance gramPrimePowerFintype (C : SupportedIdeal) (P : GramPrime C) :
    Fintype (O⧸gramPrime C P^gramExponent C P) := Fintype.ofFinite _
instance gramProductFinite (C : SupportedIdeal) : Finite (O⧸∏P : GramPrime C,gramPrime C P^gramExponent C P) := by
  apply Ring.HasFiniteQuotients.finiteQuotient
  rw [←gramPrime_product C]
  exact C.property.1
instance gramProductFintype (C : SupportedIdeal) : Fintype (O⧸∏P : GramPrime C,gramPrime C P^gramExponent C P) := Fintype.ofFinite _

structure GramNumeratorData (k : GramFrequency) where
  unit : Oˣ
  lambdaExponent : ℕ
  twoExponent : ℕ
  good : O
  supported : Supported (Ideal.span {good})
  primary : λ₀^2∣good-1
  factor : k.val=unit.val*λ₀^lambdaExponent*(2:O)^twoExponent*good

lemma gramNumeratorData_nonempty (k : GramFrequency) : Nonempty (GramNumeratorData k) := by
  obtain ⟨u,a,b,r,hr,hpr,hf⟩ := exists_supported_numerator_factorization k.val k.property
  exact ⟨⟨u,a,b,r,hr,hpr,hf⟩⟩
def gramNumeratorData (k : GramFrequency) : GramNumeratorData k := Classical.choice (gramNumeratorData_nonempty k)

def canonicalJoint (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (C : SupportedIdeal) (k : GramFrequency) (n m : O) : ℂ :=
  let f:=gramNumeratorData k
  jointExtension S hS σ (primaryGenerator C.val) k.val f.unit f.lambdaExponent f.twoExponent
    f.good f.supported (gramPrime C) (gramPrime_good C) (gramExponent C) n m

lemma canonicalJoint_norm (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (C : SupportedIdeal) (k : GramFrequency) (n m : O) : ‖canonicalJoint S hS σ C k n m‖≤(Ideal.absNorm C.val:ℝ) := by
  have hh := jointExtension_norm S hS σ (primaryGenerator C.val) k.val
    (gramNumeratorData k).unit (gramNumeratorData k).lambdaExponent (gramNumeratorData k).twoExponent
    (gramNumeratorData k).good (gramNumeratorData k).supported (gramPrime C) (gramPrime_good C)
    (gramExponent C) (gramExponent_pos C) n m
  simpa only [←gramPrime_product C,canonicalJoint] using hh

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1504

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramClassification
Source SHA256: 521c571705d26372e1f4da19c6de934c464ca18821d78b823a6a1d8ffb910018
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1505



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredExceptionalCount
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def exceptionalModulus (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) : Id :=
  jointFixedModulus S hS*C.val
lemma exceptionalModulus_nonzero (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) :
    exceptionalModulus S hS C≠0 := mul_ne_zero (jointFixedModulus_nonzero S hS) C.property.1
lemma exceptionalModulus_norm (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) :
    Ideal.absNorm (exceptionalModulus S hS C)=Ideal.absNorm (jointFixedModulus S hS)*Ideal.absNorm C.val :=
  map_mul Ideal.absNorm _ _

def ExceptionalFrequency (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) (k : GramFrequency) : Prop :=
  ∀p∉IdealMobiusDivisorSum.primeSupport (exceptionalModulus S hS C),valuation (Ideal.span {k.val}) p%6=0

lemma nonexceptional_prime (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) (k : GramFrequency)
    (hk : ¬ExceptionalFrequency S hS C k) :
    ∃p : Id,Prime p ∧ p∉IdealMobiusDivisorSum.primeSupport (exceptionalModulus S hS C) ∧
      ¬6∣(normalizedFactors (Ideal.span {k.val})).count p := by
  unfold ExceptionalFrequency at hk
  push Not at hk
  obtain ⟨p,hp,he⟩ := hk
  have hcount : (normalizedFactors (Ideal.span {k.val})).count p≠0 := by
    intro hz
    apply he
    simp [valuation,hz]
  have hprime := prime_of_normalized_factor p (Multiset.count_pos.mp (Nat.pos_of_ne_zero hcount))
  exact ⟨p,hprime,hp,fun hd=>he (Nat.mod_eq_zero_of_dvd hd)⟩

lemma outside_exceptional_not_dvd (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal)
    (p : Id) (hp : Prime p) (hout : p∉IdealMobiusDivisorSum.primeSupport (exceptionalModulus S hS C)) :
    (¬p∣jointFixedModulus S hS) ∧ (¬p∣∏i : GramPrime C,gramPrime C i) := by
  have hnot : ¬p∣exceptionalModulus S hS C := by
    intro hd
    apply hout
    exact Multiset.mem_toFinset.mpr ((Ideal.mem_normalizedFactors_iff (exceptionalModulus_nonzero S hS C)).mpr
      ⟨Ideal.isPrime_of_prime hp,Ideal.dvd_iff_le.mp hd⟩)
  refine ⟨fun hd=>hnot (dvd_mul_of_dvd_left hd _),?_⟩
  intro hd
  apply hnot
  apply dvd_mul_of_dvd_right
  apply dvd_trans hd
  calc
    _∣∏i : GramPrime C,gramPrime C i^gramExponent C i :=
      Finset.prod_dvd_prod_of_dvd _ _ (fun i _=>dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp (gramExponent_pos C i)))
    _=C.val := (gramPrime_product C).symm

lemma outside_exceptional_good (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal)
    (p : Id) (hp : Prime p) (hout : p∉IdealMobiusDivisorSum.primeSupport (exceptionalModulus S hS C)) :
    λ₀∉p ∧ ringChar (O⧸p)≠2 := by
  let : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hle : exceptionalModulus S hS C≤Ideal.span {(72:O)} :=
    le_trans Ideal.mul_le_left Ideal.mul_le_right
  have hh := CenteredExceptionalProfile.outside_fixed_support _ (exceptionalModulus_nonzero S hS C) hle p hp hout
  exact ⟨hh.1,ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem p hh.2.1⟩

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1505

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramCanonicalBlock
Source SHA256: 6365678c7730e30aa63722623c0ed2478b0e5e9352c0342162db11bc9cb88064
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1506



namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def canonicalLatticeBlock (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (C : SupportedIdeal) (k : GramFrequency) (d : O) (W : ℝ→ℂ) (U : SchwartzMap ℝ ℂ)
    (v T N : ℝ) : ℂ :=
  ∑'m : O×O,canonicalJoint S hS σ C k (d*m.1) (d*m.2)*
    shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)

theorem canonical_nonexceptional_block (A B : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃(J : ℕ)(H : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a₀ b₀)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧ ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(k : GramFrequency),¬ExceptionalFrequency S hS C k→
      ∀(d : O)(U : SchwartzMap ℝ ℂ)(v T N : ℝ),0≤T→0<N→
        ‖canonicalLatticeBlock S hS σ C k d W U v T N‖≤
        K*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J/(1+T)^B*
          (Ideal.absNorm C.val:ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*
            Ideal.absNorm (Ideal.span {k.val})/N)^A) := by
  obtain ⟨J,H,hsource⟩ := literal_nonexceptional_source A B hA a₀ b₀ ha₀ hab
  refine ⟨J,H,?_⟩
  intro W hs hW
  obtain ⟨K,hK,hsource⟩ := hsource W hs hW
  refine ⟨K,hK,?_⟩
  intro S hS σ C k hk d U v T N hT hN
  obtain ⟨p,hp,hout,he⟩ := nonexceptional_prime S hS C k hk
  let : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hg := outside_exceptional_good S hS C p hp hout
  have hd := outside_exceptional_not_dvd S hS C p hp hout
  have hcspan := (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ C.property)).1
  have hf : Ideal.span {primaryGenerator C.val}=∏i : GramPrime C,gramPrime C i^gramExponent C i := hcspan.trans (gramPrime_product C)
  have hh := hsource S hS σ (primaryGenerator C.val) k.val
    (supported_primaryGenerator_ne_zero _ C.property) k.property
    (gramNumeratorData k).unit (gramNumeratorData k).lambdaExponent (gramNumeratorData k).twoExponent
    (gramNumeratorData k).good (gramNumeratorData k).supported (gramNumeratorData k).factor
    (gramPrime C) (gramPrime_good C) (gramExponent C) (gramExponent_pos C) hf
    p hp.ne_zero hg.1 hg.2 hd.1 hd.2 he U v T hT d N hN
  simpa only [canonicalLatticeBlock,canonicalJoint,hcspan] using hh.2

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1506

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramCanonicalSource
Source SHA256: 0d5606064e55ed70638741ede5f837bef021040a342c3d0ff05cae82d5e084a9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1507


namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT CenteredMomentMobiusRegroup UniqueFactorizationMonoid
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def originalCommonBlock (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (C : SupportedIdeal) (k : GramFrequency) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0<Y) (U : SchwartzMap ℝ ℂ) (v : ℝ) : ℂ :=
  let N:=commonResidualScale C Y
  let hN:=commonResidualScale_pos C Y hY
  let F:=lowGaussColumns W hW N hN
  (∑I∈F,∑J∈F,if IsCoprime I.val J.val then
      (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C I)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C I).val:ℝ)/Y))*
      star (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C J)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C J).val:ℝ)/Y))*
      actualCorrelation (primaryGenerator (supportedIdealProduct C I).val)
        (primaryGenerator (supportedIdealProduct C J).val)
        ((supported_span_primaryGenerator_iff _).mpr (supportedIdealProduct C I).property)
        ((supported_span_primaryGenerator_iff _).mpr (supportedIdealProduct C J).property)
        (primaryGenerator C.val*k.val)*
      paperRadialFourier U (Q*‖eisEmbedding (primaryGenerator C.val*k.val)‖^2/
        ‖eisEmbedding (primaryGenerator (supportedIdealProduct C I).val*primaryGenerator (supportedIdealProduct C J).val)‖^2)
      else 0)

theorem originalCommonBlock_eq_lattice (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C : SupportedIdeal) (k : GramFrequency)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    originalCommonBlock S hS σ C k W hW Y Q hY U v=
      ∑D∈divisorPool (lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)) Subtype.val,
        (moebius D:ℂ)*canonicalLatticeBlock S hS σ C k (primaryGenerator D) W U v
          (frequencyScale C k.val Y Q) (commonResidualScale C Y/Ideal.absNorm D) := by
  have hh := original_common_window_source S hS hbad σ C k.val
    (gramNumeratorData k).unit (gramNumeratorData k).lambdaExponent (gramNumeratorData k).twoExponent
    (gramNumeratorData k).good (gramNumeratorData k).supported (gramNumeratorData k).primary
    (gramNumeratorData k).factor (gramPrime C) (gramPrime_good C) (gramExponent C)
    (gramExponent_pos C) (gramPrime_coprime C) (gramPrime_product C) W hW Y Q hY hQ U v
  change originalCommonBlock S hS σ C k W hW Y Q hY U v=_ at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  have hD0 := (divisorPool_supported _ D hD).1
  have hN : 0<commonResidualScale C Y/(Ideal.absNorm D:ℝ) :=
    div_pos (commonResidualScale_pos C Y hY) (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD0))
  exact (shell_lattice_summable W hW _ hN U v (frequencyScale C k.val Y Q)
    (fun n m=>canonicalJoint S hS σ C k (primaryGenerator D*n) (primaryGenerator D*m))).tsum_prod.symm

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1507

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramCanonicalTrivial
Source SHA256: 40d0da6ba5b0fff76855205f2b057579a8ac28b9f182632287f9d7c7a80bb44d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1508


namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem canonical_trivial_block (a b B : ℝ) (ha : 0<a) (hb : 0≤b) (hB : 0≤B) (A : ℕ) :
    ∃s : Finset (ℕ×ℕ),∃K : ℝ,0<K ∧
      ∀(W : ℝ→ℂ)(_hcompact : HasCompactSupport W),
      (Function.support W⊆Set.Icc a b)→(∀x,‖W x‖≤B)→
      ∀(U : SchwartzMap ℝ ℂ)(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(k : GramFrequency)(d : O)(N T v : ℝ),0<N→0≤T→
      (1+T)^A*‖canonicalLatticeBlock S hS σ C k d W U v T N‖≤
        K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Ideal.absNorm C.val:ℝ)*N^2 := by
  obtain ⟨s,K,hK,hprofile⟩ := shellProfile_weighted_bound a b B ha hB A
  refine ⟨s,(1+128*b)^2*K,by positivity,?_⟩
  intro W hcompact hs hW U S hS σ C k d N T v hN hT
  let F:=shellLatticeColumns W hcompact N hN
  let G:=F
  have hF0 : ∀z∈F,z≠0 := shellLatticeColumns_nonzero W hcompact N hN a b ha hs
  have hG0 : ∀z∈G,z≠0 := hF0
  have hFN : ∀z∈F,‖eisEmbedding z‖^2≤b*N := shellLatticeColumns_norm W hcompact N hN a b hs
  have hGN : ∀z∈G,‖eisEmbedding z‖^2≤b*N := hFN
  unfold canonicalLatticeBlock
  rw [shell_lattice_tsum W hcompact N hN U v T (fun n m=>canonicalJoint S hS σ C k (d*n) (d*m))]
  have hcoef (n m : O) : ‖canonicalJoint S hS σ C k (d*n) (d*m)‖≤(Ideal.absNorm C.val:ℝ) :=
    canonicalJoint_norm S hS σ C k _ _
  have hpoint (n m : O) : (1+T)^A*‖canonicalJoint S hS σ C k (d*n) (d*m)*
      shellProfile W v U T (‖eisEmbedding n‖^2/N) (‖eisEmbedding m‖^2/N)‖≤
      (Ideal.absNorm C.val:ℝ)*(K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U) := by
    rw [norm_mul]
    calc
      _ = ‖canonicalJoint S hS σ C k (d*n) (d*m)‖*
          ((1+T)^A*‖shellProfile W v U T (‖eisEmbedding n‖^2/N) (‖eisEmbedding m‖^2/N)‖) := by ring
      _ ≤ _ := mul_le_mul (hcoef n m) (hprofile W hs hW U v T _ _ hT) (by positivity) (by positivity)
  have hcount := annular_pair_count F G b N hb hN.le hF0 hG0 hFN hGN
  calc
    _ ≤ (1+T)^A*(∑n∈F,∑m∈G,‖canonicalJoint S hS σ C k (d*n) (d*m)*
        shellProfile W v U T (‖eisEmbedding n‖^2/N) (‖eisEmbedding m‖^2/N)‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _=>norm_sum_le _ _)
    _ ≤ (F.card:ℝ)*G.card*((Ideal.absNorm C.val:ℝ)*(K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)) := by
      simp_rw [Finset.mul_sum]
      calc
        _ ≤ ∑n∈F,∑m∈G,(Ideal.absNorm C.val:ℝ)*(K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U) :=
          Finset.sum_le_sum (fun n _=>Finset.sum_le_sum (fun m _=>hpoint n m))
        _ = _ := by simp;ring
    _ ≤ ((128*b)^2*N^2)*((Ideal.absNorm C.val:ℝ)*(K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [Finset.card_product,Nat.cast_mul] using hcount
    _ ≤ _ := by
      have hb' : (128*b)^2≤(1+128*b)^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hb' (show 0≤N^2*((Ideal.absNorm C.val:ℝ)*
        (K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)) by positivity)]

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1508

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramFiniteGcd
Source SHA256: 0cfc6f8f38d312936b6d49952d7b49f18cd2deb5737780725d83ffac83b4707c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1509


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => ActualEisensteinCubic.O

lemma supportedIdealProduct_injective (C : SupportedIdeal) : Function.Injective (supportedIdealProduct C) := by
  intro I J h
  apply Subtype.ext
  exact mul_left_cancel₀ C.property.1 (congrArg Subtype.val h)

def commonPool (F : Finset SupportedIdeal) : Finset SupportedIdeal :=
  (F×ˢF).image (fun p=>gcdCommon p.1 p.2)
def commonColumns (F : Finset SupportedIdeal) (C : SupportedIdeal) : Finset SupportedIdeal :=
  F.preimage (supportedIdealProduct C) (supportedIdealProduct_injective C).injOn
lemma commonColumns_mem (F : Finset SupportedIdeal) (C I : SupportedIdeal) :
    I∈commonColumns F C ↔ supportedIdealProduct C I∈F := Finset.mem_preimage

def commonTriples (F : Finset SupportedIdeal) : Finset ((_C : SupportedIdeal)×(SupportedIdeal×SupportedIdeal)) :=
  (commonPool F).sigma (fun C=>(commonColumns F C×ˢcommonColumns F C).filter (fun p=>IsCoprime p.1.val p.2.val))

theorem finite_pair_gcd (F : Finset SupportedIdeal) (f : SupportedIdeal→SupportedIdeal→ℂ) :
    (∑I∈F,∑J∈F,f I J)=
      ∑C∈commonPool F,∑I∈commonColumns F C,∑J∈commonColumns F C,
        if IsCoprime I.val J.val then f (supportedIdealProduct C I) (supportedIdealProduct C J) else 0 := by
  have he : (∑p∈F×ˢF,f p.1 p.2)=
      ∑t∈commonTriples F,f (supportedIdealProduct t.1 t.2.1) (supportedIdealProduct t.1 t.2.2) := by
    apply Finset.sum_bij (fun p _=>⟨gcdCommon p.1 p.2,gcdLeft p.1 p.2,gcdRight p.1 p.2⟩)
    · intro p hp
      have hl : supportedIdealProduct (gcdCommon p.1 p.2) (gcdLeft p.1 p.2)=p.1 := Subtype.ext (gcd_common_left _ _)
      have hr : supportedIdealProduct (gcdCommon p.1 p.2) (gcdRight p.1 p.2)=p.2 := Subtype.ext (gcd_common_right _ _)
      simp only [commonTriples,Finset.mem_sigma,Finset.mem_filter,Finset.mem_product,commonColumns_mem]
      exact ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,⟨by rw [hl];exact (Finset.mem_product.mp hp).1,by rw [hr];exact (Finset.mem_product.mp hp).2⟩,gcd_residual_coprime _ _⟩
    · intro p hp q hq he
      have hc := congrArg Sigma.fst he
      have hl := congrArg (fun t : (C : SupportedIdeal)×(SupportedIdeal×SupportedIdeal)=>t.2.1) he
      have hr := congrArg (fun t : (C : SupportedIdeal)×(SupportedIdeal×SupportedIdeal)=>t.2.2) he
      apply Prod.ext <;> apply Subtype.ext
      · rw [←gcd_common_left p.1 p.2,←gcd_common_left q.1 q.2]
        rw [show gcdCommon p.1 p.2=gcdCommon q.1 q.2 from hc,show gcdLeft p.1 p.2=gcdLeft q.1 q.2 from hl]
      · rw [←gcd_common_right p.1 p.2,←gcd_common_right q.1 q.2]
        rw [show gcdCommon p.1 p.2=gcdCommon q.1 q.2 from hc,show gcdRight p.1 p.2=gcdRight q.1 q.2 from hr]
    · intro t ht
      have ht' : t.1∈commonPool F ∧ (t.2.1∈commonColumns F t.1 ∧ t.2.2∈commonColumns F t.1) ∧ IsCoprime t.2.1.val t.2.2.val := by
        simpa only [commonTriples,Finset.mem_sigma,Finset.mem_filter,Finset.mem_product] using ht
      let u : CoprimeTriple:=⟨(t.1,t.2),ht'.2.2⟩
      refine ⟨(supportedIdealProduct t.1 t.2.1,supportedIdealProduct t.1 t.2.2),?_,?_⟩
      · exact Finset.mem_product.mpr ⟨(commonColumns_mem F _ _).mp ht'.2.1.1,(commonColumns_mem F _ _).mp ht'.2.1.2⟩
      · have h:=congrArg Subtype.val (gcdTriple_multiply u)
        exact congrArg (fun p : SupportedIdeal×(SupportedIdeal×SupportedIdeal)=>(⟨p.1,p.2⟩ : (C : SupportedIdeal)×(SupportedIdeal×SupportedIdeal))) h
    · intro p hp
      have hl : supportedIdealProduct (gcdCommon p.1 p.2) (gcdLeft p.1 p.2)=p.1 := Subtype.ext (gcd_common_left _ _)
      have hr : supportedIdealProduct (gcdCommon p.1 p.2) (gcdRight p.1 p.2)=p.2 := Subtype.ext (gcd_common_right _ _)
      simp only [hl,hr]
  rw [Finset.sum_product] at he
  rw [he,commonTriples,Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro C hC
  rw [Finset.sum_filter,Finset.sum_product]

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1509

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramNonzeroFrequency
Source SHA256: 3139cc2d821268fa31de88d4e30999075f0864ffcbead6dd4867988af4359bab
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1510


namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

lemma nonzero_tsum_indicator (f : O→ℂ) :
    (∑'k : O,if k=0 then 0 else f k)=∑'k : GramFrequency,f k.val := by
  rw [←tsum_subtype_eq_of_support_subset (s:={k : O | k≠0}) (by
    intro k hk hz
    subst k
    exact hk (by simp))]
  apply tsum_congr
  intro k
  exact ite_eq_right k.property

def gramFrequencyNeg : GramFrequency≃GramFrequency where
  toFun k:=⟨-k.val,neg_ne_zero.mpr k.property⟩
  invFun k:=⟨-k.val,neg_ne_zero.mpr k.property⟩
  left_inv k:=Subtype.ext (neg_neg k.val)
  right_inv k:=Subtype.ext (neg_neg k.val)

lemma actual_common_nonzero_tsum (C n₁ n₂ : O)
    (hC : Supported (Ideal.span {C})) (h₁ : Supported (Ideal.span {n₁})) (h₂ : Supported (Ideal.span {n₂}))
    (F : O→ℂ) :
    (∑'j : GramFrequency,actualCorrelation (C*n₁) (C*n₂)
      (supported_mul_elements C n₁ hC h₁) (supported_mul_elements C n₂ hC h₂) j.val*F j.val)=
      ∑'k : GramFrequency,actualCorrelation (C*n₁) (C*n₂)
        (supported_mul_elements C n₁ hC h₁) (supported_mul_elements C n₂ hC h₂) (C*k.val)*F (C*k.val) := by
  have hh := actual_common_frequency_tsum C n₁ n₂ hC h₁ h₂ (fun j=>if j=0 then 0 else F j)
  have hc0 := supported_element_ne_zero C hC
  simp only [mul_ite,mul_zero,mul_eq_zero,hc0,false_or] at hh
  simpa only [nonzero_tsum_indicator] using hh

lemma actual_gcd_nonzero_frequency_source (I J : SupportedIdeal) (U : SchwartzMap ℝ ℂ) (Q : ℝ) :
    (∑'h : GramFrequency,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) (-h.val)*
      paperRadialFourier U (Q*‖eisEmbedding h.val‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))=
      ∑'k : GramFrequency,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
        ((supported_span_primaryGenerator_iff _).mpr I.property)
        ((supported_span_primaryGenerator_iff _).mpr J.property) (primaryGenerator (gcdCommon I J).val*k.val)*
        paperRadialFourier U (Q*‖eisEmbedding (primaryGenerator (gcdCommon I J).val*k.val)‖^2/
          ‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2) := by
  have hn := gramFrequencyNeg.tsum_eq (fun h : GramFrequency=>
    actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) h.val*
      paperRadialFourier U (Q*‖eisEmbedding h.val‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))
  simp only [gramFrequencyNeg,Equiv.coe_fn_mk,map_neg,norm_neg] at hn
  rw [hn]
  have hh := actual_common_nonzero_tsum (primaryGenerator (gcdCommon I J).val)
    (primaryGenerator (gcdLeft I J).val) (primaryGenerator (gcdRight I J).val)
    ((supported_span_primaryGenerator_iff _).mpr (gcdCommon I J).property)
    ((supported_span_primaryGenerator_iff _).mpr (gcdLeft I J).property)
    ((supported_span_primaryGenerator_iff _).mpr (gcdRight I J).property)
    (fun h=>paperRadialFourier U (Q*‖eisEmbedding h‖^2/
      ‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))
  simpa only [←gcd_generator_left I J,←gcd_generator_right I J] using hh

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1510

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramWeightedFrequency
Source SHA256: 874fd2793a62a44ab2c420e96caa6cf82247299611b1454411aad0b8d5e52640
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1511


namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma min_product_amplification (L T : ℝ) (hL : 0≤L) (hT : 0≤T) (A : ℕ) :
    min 1 ((L*T)^A)≤(1+T)^A*min 1 (L^A) := by
  by_cases h : L^A≤1
  · rw [min_eq_right h]
    apply (min_le_right _ _).trans
    rw [mul_pow,mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hT (by linarith) _) (pow_nonneg hL _)
  · rw [min_eq_left (le_of_not_ge h),mul_one]
    exact (min_le_left _ _).trans (one_le_pow₀ (by linarith))

lemma frequencyScale_ratio (C : SupportedIdeal) (k : GramFrequency) (Y Q : ℝ) :
    frequencyScale C k.val Y Q=(Ideal.absNorm (Ideal.span {k.val}):ℝ)/((Y^2/Q)/Ideal.absNorm C.val) := by
  rw [frequencyScale,ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,div_div_eq_mul_div]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

theorem canonical_nonexceptional_weighted (A : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃(J : ℕ)(H₀ : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a₀ b₀)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧ ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(k : GramFrequency),¬ExceptionalFrequency S hS C k→
      ∀(d : O)(U : SchwartzMap ℝ ℂ)(v H N : ℝ),0<H→0<N→
        ‖canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*
          (Ideal.absNorm C.val:ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*H/N)^A)*
          (1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ) := by
  obtain ⟨J,H₀,hblock⟩ := canonical_nonexceptional_block A (A+2) hA a₀ b₀ ha₀ hab
  refine ⟨J,H₀,?_⟩
  intro W hs hW
  obtain ⟨K,hK,hblock⟩ := hblock W hs hW
  refine ⟨K,hK,?_⟩
  intro S hS σ C k hk d U v H N hH hN
  let t : ℝ := (Ideal.absNorm (Ideal.span {k.val}):ℝ)/H
  let L : ℝ := (Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*H/N
  have ht : 0≤t := by dsimp [t];positivity
  have hL : 0≤L := by dsimp [L];positivity
  have htp : 0<1+t := by linarith
  have he : (Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*Ideal.absNorm (Ideal.span {k.val})/N=L*t := by
    dsimp [L,t]
    field_simp
  have hb := hblock S hS σ C k hk d U v t N ht hN
  rw [he] at hb
  apply hb.trans
  calc
    _≤K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J/(1+t)^(A+2)*
        (Ideal.absNorm C.val:ℝ)*N^2*((1+t)^A*min 1 (L^A)) :=
      mul_le_mul_of_nonneg_left (min_product_amplification L t hL ht A) (by positivity)
    _=K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Ideal.absNorm C.val:ℝ)*N^2*
        min 1 (L^A)*(1+t)^(-2:ℝ) := by
      rw [Real.rpow_neg htp.le,Real.rpow_two,pow_add]
      field_simp
    _=_ := rfl

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1511

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramFrequencyMass
Source SHA256: 9458192dc499582ef78016a73226122a4b3dba20d55d77ca0acf6d0e46d300d0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1512




namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma gramFrequency_image_sum (E : Finset GramFrequency) (f : O→ℝ) :
    (∑k∈E.image Subtype.val,f k)=∑k∈E,f k.val :=
  Finset.sum_image (fun _ _ _ _ h=>Subtype.val_injective h)

theorem canonical_nonexceptional_frequency_sum (A : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃(J : ℕ)(H₀ : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a₀ b₀)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧ ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(E : Finset GramFrequency),
      (∀k∈E,¬ExceptionalFrequency S hS C k)→
      ∀(d : O)(U : SchwartzMap ℝ ℂ)(v H N : ℝ),0<H→0<N→
        ‖∑k∈E,canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*
          (Ideal.absNorm C.val:ℝ)*N^2*H*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*H/N)^A) := by
  obtain ⟨J,H₀,hblock⟩ := canonical_nonexceptional_weighted A hA a₀ b₀ ha₀ hab
  obtain ⟨L,hL,hcount⟩ := ProbeGramFrequencySummation.frequency_weighted_sum
  refine ⟨J,H₀,?_⟩
  intro W hs hW
  obtain ⟨K,hK,hblock⟩ := hblock W hs hW
  refine ⟨K*L,mul_pos hK hL,?_⟩
  intro S hS σ C E hE d U v H N hH hN
  have hc := hcount (E.image Subtype.val) H hH (by
    intro k hk;obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk;exact j.property)
  rw [gramFrequency_image_sum] at hc
  let V := K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Ideal.absNorm C.val:ℝ)*N^2*
    min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*H/N)^A)
  have hV : 0≤V := by dsimp [V];positivity
  calc
    _≤∑k∈E,‖canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖ := norm_sum_le _ _
    _≤∑k∈E,V*(1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ) :=
      Finset.sum_le_sum (fun k hk=>hblock S hS σ C k (hE k hk) d U v H N hH hN)
    _=V*(∑k∈E,(1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ)) := (Finset.mul_sum ..).symm
    _≤V*(L*H) := mul_le_mul_of_nonneg_left hc hV
    _=_ := by dsimp [V];ring

theorem canonical_exceptional_frequency_sum (a b M ε : ℝ) (ha : 0<a) (hb : 0≤b)
    (hM : 0≤M) (hε : 0<ε) :
    ∃H₀ : Finset (ℕ×ℕ),∃K : ℝ,0<K ∧
      ∀(W : ℝ→ℂ)(_hcompact : HasCompactSupport W),
      (Function.support W⊆Set.Icc a b)→(∀x,‖W x‖≤M)→
      ∀(U : SchwartzMap ℝ ℂ)(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(E : Finset GramFrequency),
      (∀k∈E,ExceptionalFrequency S hS C k)→
      ∀(d : O)(v H N : ℝ),0<H→0<N→
        ‖∑k∈E,canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Ideal.absNorm C.val:ℝ)*N^2*
          ((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val)^ε*H^(1/6:ℝ) := by
  obtain ⟨H₀,K,hK,hblock⟩ := canonical_trivial_block a b M ha hb hM 2
  obtain ⟨L,hL,hcount⟩ := ProbeGramFrequencySummation.exceptional_frequency_weighted_sum ε hε
  refine ⟨H₀,K*L,mul_pos hK hL,?_⟩
  intro W hcompact hs hW U S hS σ C E hE d v H N hH hN
  have hc := hcount (exceptionalModulus S hS C) (exceptionalModulus_nonzero S hS C)
    (E.image Subtype.val) H hH
    (by intro k hk;obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk;exact j.property)
    (by intro k hk;obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk;exact hE j hj)
  rw [gramFrequency_image_sum,exceptionalModulus_norm,Nat.cast_mul] at hc
  let V := K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Ideal.absNorm C.val:ℝ)*N^2
  have hV : 0≤V := by dsimp [V];positivity
  have hp (k : GramFrequency) :
      ‖canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖≤
        V*(1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ) := by
    have ht : 0≤(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H := by positivity
    have hb := hblock W hcompact hs hW U S hS σ C k d N _ v hN ht
    have hpos : 0<1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H := by positivity
    rw [Real.rpow_neg hpos.le,Real.rpow_two,←div_eq_mul_inv]
    apply (le_div_iff₀ (sq_pos_of_pos hpos)).mpr
    convert hb using 1 ; dsimp [V] ; ring
  calc
    _≤∑k∈E,‖canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖ := norm_sum_le _ _
    _≤∑k∈E,V*(1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ) := Finset.sum_le_sum (fun k _=>hp k)
    _=V*(∑k∈E,(1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ)) := (Finset.mul_sum ..).symm
    _≤V*(L*((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val)^ε*H^(1/6:ℝ)) := mul_le_mul_of_nonneg_left hc hV
    _=_ := by dsimp [V];ring

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1512

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramPrefactor
Source SHA256: 00f30d368754a0c3c4db1f2da0de68d552066455dc002bbe2045d4e2d463c492
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1513



namespace OAI

noncomputable section
namespace SevenEighths.ProbeGramCommon

lemma nonexceptional_prefactor (c d F P Y Q : ℝ)
    (hc : 0<c) (hd : 0<d) (hF : 0<F) (hP : 0<P) (hY : 0<Y) (A : ℕ) :
    (Q/Y^3)*c*(Y/(c*d))^2*(P/c)*min 1 ((F*c*(P/c)/(Y/(c*d)))^A)=
      (Q/Y)*P*(c^(-2:ℝ)*d^(-2:ℝ)*min 1 ((c*d/(Y/(F*P)))^A)) := by
  have he : F*c*(P/c)/(Y/(c*d))=c*d/(Y/(F*P)) := by field_simp
  rw [he,Real.rpow_neg hc.le,Real.rpow_neg hd.le,Real.rpow_two,Real.rpow_two]
  field_simp

lemma exceptional_prefactor (c d F P Y Q ε : ℝ)
    (hc : 0<c) (hd : 0<d) (hF : 0<F) (hP : 0<P) (hY : 0<Y) :
    (Q/Y^3)*c*(Y/(c*d))^2*(F*c)^ε*(P/c)^(1/6:ℝ)=
      (Q/Y)*F^ε*P^(1/6:ℝ)*(c^(-7/6+ε:ℝ)*d^(-2:ℝ)) := by
  rw [Real.mul_rpow hF.le hc.le,Real.div_rpow hP.le hc.le,
    show (-7/6+ε:ℝ)=ε+(-1)+(-(1/6)) by ring,
    Real.rpow_add hc,Real.rpow_add hc,Real.rpow_neg_one,
    Real.rpow_neg hc.le,Real.rpow_neg hd.le,Real.rpow_two]
  field_simp

lemma supported_nonexceptional_prefactor (C D : SupportedIdeal) (F P Y Q : ℝ)
    (hF : 0<F) (hP : 0<P) (hY : 0<Y) (A : ℕ) :
    (Q/Y^3)*gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*(P/gramIdealNorm C)*
      min 1 ((F*gramIdealNorm C*(P/gramIdealNorm C)/(Y/(gramIdealNorm C*gramIdealNorm D)))^A)=
      (Q/Y)*P*(gramIdealNorm C^(-2:ℝ)*gramIdealNorm D^(-2:ℝ)*
        min 1 ((gramIdealNorm C*gramIdealNorm D/(Y/(F*P)))^A)) :=
  nonexceptional_prefactor _ _ _ _ _ _ (gramIdealNorm_pos C) (gramIdealNorm_pos D) hF hP hY A

lemma supported_exceptional_prefactor (C D : SupportedIdeal) (F P Y Q ε : ℝ)
    (hF : 0<F) (hP : 0<P) (hY : 0<Y) :
    (Q/Y^3)*gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*
      (F*gramIdealNorm C)^ε*(P/gramIdealNorm C)^(1/6:ℝ)=
      (Q/Y)*F^ε*P^(1/6:ℝ)*(gramIdealNorm C^(-7/6+ε:ℝ)*gramIdealNorm D^(-2:ℝ)) :=
  exceptional_prefactor _ _ _ _ _ _ _ (gramIdealNorm_pos C) (gramIdealNorm_pos D) hF hP hY

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1513

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramIdealMass
Source SHA256: a9124c17ba994abe66240bba7eef0eaf47fdb4fd58274f181d60ab366be5c72e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1514



namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma normalized_double_sum_bound (F G : Finset SupportedIdeal) (α V : SupportedIdeal→SupportedIdeal→ℂ)
    (hα : ∀C∈F,∀D∈G,‖α C D‖≤1) (p : ℝ) (hp : 0≤p) :
    ‖(p:ℂ)*(∑C∈F,∑D∈G,α C D*V C D)‖≤∑C∈F,∑D∈G,p*‖V C D‖ := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp]
  calc
    _≤p*(∑C∈F,∑D∈G,‖α C D*V C D‖) := mul_le_mul_of_nonneg_left
      ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _=>norm_sum_le _ _))) hp
    _≤p*(∑C∈F,∑D∈G,‖V C D‖) := by
      apply mul_le_mul_of_nonneg_left _ hp
      apply Finset.sum_le_sum
      intro C hC
      apply Finset.sum_le_sum
      intro D hD
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hα C hC D hD) (norm_nonneg _)).trans_eq (one_mul _)
    _=_ := by simp only [Finset.mul_sum]

theorem canonical_nonexceptional_ideal_sum (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (A : ℕ) (hA : 2<A) (a b : ℝ) (ha : 0<a) (hab : a<b) :
    ∃(J : ℕ)(H₀ : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a b)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧ ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (F G : Finset SupportedIdeal)(E : SupportedIdeal→SupportedIdeal→Finset GramFrequency)
      (α : SupportedIdeal→SupportedIdeal→ℂ),
      (∀C∈F,∀D∈G,‖α C D‖≤1)→(∀C∈F,∀D∈G,∀k∈E C D,¬ExceptionalFrequency S hS C k)→
      ∀(U : SchwartzMap ℝ ℂ)(v P Y Q : ℝ),0<P→0<Y→0≤Q→
        ‖((Q/Y^3:ℝ):ℂ)*(∑C∈F,∑D∈G,α C D*∑k∈E C D,
          canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
            ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/(P/gramIdealNorm C))
            (Y/(gramIdealNorm C*gramIdealNorm D)))‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y)*P*
          (Y/((Ideal.absNorm (jointFixedModulus S hS):ℝ)*P))^(-1+δ) := by
  obtain ⟨J,H₀,hfreq⟩ := canonical_nonexceptional_frequency_sum A hA a b ha hab
  obtain ⟨L,hL,hideal⟩ := gram_supported_double_sum δ hδ hδ1
  refine ⟨J,H₀,?_⟩
  intro W hs hW
  obtain ⟨K,hK,hfreq⟩ := hfreq W hs hW
  refine ⟨K*L,mul_pos hK hL,?_⟩
  intro S hS σ F G E α hα hE U v P Y Q hP hY hQ
  let M : ℝ := Ideal.absNorm (jointFixedModulus S hS)
  have hM : 0<M := by dsimp [M];exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (jointFixedModulus_nonzero S hS))
  let V := fun C D : SupportedIdeal=>∑k∈E C D,
    canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
      ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/(P/gramIdealNorm C)) (Y/(gramIdealNorm C*gramIdealNorm D))
  let B := K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y)*P
  have hB : 0≤B := by dsimp [B];positivity
  have ht (C D : SupportedIdeal) (hC : C∈F) (hD : D∈G) :
      (Q/Y^3)*‖V C D‖≤B*(gramIdealNorm C^(-2:ℝ)*gramIdealNorm D^(-2:ℝ)*
        min 1 ((gramIdealNorm C*gramIdealNorm D/(Y/(M*P)))^A)) := by
    have hc := gramIdealNorm_pos C
    have hd := gramIdealNorm_pos D
    have hh := hfreq S hS σ C (E C D) (hE C hC D hD) (primaryGenerator D.val) U v
      (P/gramIdealNorm C) (Y/(gramIdealNorm C*gramIdealNorm D)) (by positivity) (by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (show 0≤Q/Y^3 by positivity)
    apply hh'.trans_eq
    change (Q/Y^3)*(K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*
      gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*(P/gramIdealNorm C)*
      min 1 ((M*gramIdealNorm C*(P/gramIdealNorm C)/(Y/(gramIdealNorm C*gramIdealNorm D)))^A))=_
    calc
      _=(K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J)*
        ((Q/Y^3)*gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*(P/gramIdealNorm C)*
        min 1 ((M*gramIdealNorm C*(P/gramIdealNorm C)/(Y/(gramIdealNorm C*gramIdealNorm D)))^A)) := by ring
      _=_ := by rw [supported_nonexceptional_prefactor C D M P Y Q hM hP hY A];dsimp [B];ring
  calc
    _≤∑C∈F,∑D∈G,(Q/Y^3)*‖V C D‖ := normalized_double_sum_bound F G α V hα _ (by positivity)
    _≤∑C∈F,∑D∈G,B*(gramIdealNorm C^(-2:ℝ)*gramIdealNorm D^(-2:ℝ)*
        min 1 ((gramIdealNorm C*gramIdealNorm D/(Y/(M*P)))^A)) := Finset.sum_le_sum (fun C hC=>Finset.sum_le_sum (fun D hD=>ht C D hC hD))
    _=B*(∑C∈F,∑D∈G,gramIdealNorm C^(-2:ℝ)*gramIdealNorm D^(-2:ℝ)*
        min 1 ((gramIdealNorm C*gramIdealNorm D/(Y/(M*P)))^A)) := by simp only [Finset.mul_sum]
    _≤B*(L*(Y/(M*P))^(-1+δ)) := mul_le_mul_of_nonneg_left (hideal A (by omega) _ (by positivity) F G) hB
    _=_ := by dsimp [B,M];ring

theorem canonical_exceptional_ideal_sum (ε : ℝ) (hε : 0<ε) (hε1 : ε<1/6)
    (a b M₀ : ℝ) (ha : 0<a) (hb : 0≤b) (hM₀ : 0≤M₀) :
    ∃H₀ : Finset (ℕ×ℕ),∃K : ℝ,0<K ∧
      ∀(W : ℝ→ℂ)(_hcompact : HasCompactSupport W),
      (Function.support W⊆Set.Icc a b)→(∀x,‖W x‖≤M₀)→
      ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (F G : Finset SupportedIdeal)(E : SupportedIdeal→SupportedIdeal→Finset GramFrequency)
      (α : SupportedIdeal→SupportedIdeal→ℂ),
      (∀C∈F,∀D∈G,‖α C D‖≤1)→(∀C∈F,∀D∈G,∀k∈E C D,ExceptionalFrequency S hS C k)→
      ∀(U : SchwartzMap ℝ ℂ)(v P Y Q : ℝ),0<P→0<Y→0≤Q→
        ‖((Q/Y^3:ℝ):ℂ)*(∑C∈F,∑D∈G,α C D*∑k∈E C D,
          canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
            ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/(P/gramIdealNorm C))
            (Y/(gramIdealNorm C*gramIdealNorm D)))‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Q/Y)*
          (Ideal.absNorm (jointFixedModulus S hS):ℝ)^ε*P^(1/6:ℝ) := by
  obtain ⟨H₀,K,hK,hfreq⟩ := canonical_exceptional_frequency_sum a b M₀ ε ha hb hM₀ hε
  obtain ⟨L,hL,hideal⟩ := gram_supported_exceptional_sum ε hε.le hε1
  refine ⟨H₀,K*L,mul_pos hK hL,?_⟩
  intro W hcompact hs hW S hS σ F G E α hα hE U v P Y Q hP hY hQ
  let M : ℝ := Ideal.absNorm (jointFixedModulus S hS)
  have hM : 0<M := by dsimp [M];exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (jointFixedModulus_nonzero S hS))
  let V := fun C D : SupportedIdeal=>∑k∈E C D,
    canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
      ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/(P/gramIdealNorm C)) (Y/(gramIdealNorm C*gramIdealNorm D))
  let B := K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Q/Y)*M^ε*P^(1/6:ℝ)
  have hB : 0≤B := by dsimp [B];positivity
  have ht (C D : SupportedIdeal) (hC : C∈F) (hD : D∈G) :
      (Q/Y^3)*‖V C D‖≤B*(gramIdealNorm C^(-7/6+ε:ℝ)*gramIdealNorm D^(-2:ℝ)) := by
    have hc := gramIdealNorm_pos C
    have hd := gramIdealNorm_pos D
    have hh := hfreq W hcompact hs hW U S hS σ C (E C D) (hE C hC D hD) (primaryGenerator D.val) v
      (P/gramIdealNorm C) (Y/(gramIdealNorm C*gramIdealNorm D)) (by positivity) (by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (show 0≤Q/Y^3 by positivity)
    apply hh'.trans_eq
    change (Q/Y^3)*(K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*
      gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*(M*gramIdealNorm C)^ε*(P/gramIdealNorm C)^(1/6:ℝ))=_
    calc
      _=(K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)*
        ((Q/Y^3)*gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*(M*gramIdealNorm C)^ε*(P/gramIdealNorm C)^(1/6:ℝ)) := by ring
      _=_ := by rw [supported_exceptional_prefactor C D M P Y Q ε hM hP hY];dsimp [B];ring
  calc
    _≤∑C∈F,∑D∈G,(Q/Y^3)*‖V C D‖ := normalized_double_sum_bound F G α V hα _ (by positivity)
    _≤∑C∈F,∑D∈G,B*(gramIdealNorm C^(-7/6+ε:ℝ)*gramIdealNorm D^(-2:ℝ)) :=
      Finset.sum_le_sum (fun C hC=>Finset.sum_le_sum (fun D hD=>ht C D hC hD))
    _=B*(∑C∈F,∑D∈G,gramIdealNorm C^(-7/6+ε:ℝ)*gramIdealNorm D^(-2:ℝ)) := by simp only [Finset.mul_sum]
    _≤B*L := mul_le_mul_of_nonneg_left (hideal F G) hB
    _=_ := by dsimp [B,M];ring

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1514

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramWindowGcd
Source SHA256: 940fed03536fbef774a1de0ac9d5a33b83a84f08be0efe58bea2cfdf10b3c162
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1515


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss

lemma commonColumns_window (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y) (C : SupportedIdeal) :
    commonColumns (lowGaussColumns W hW Y hY) C=
      lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY) := by
  ext I
  rw [commonColumns_mem,lowGaussColumns_mem,lowGaussColumns_mem,common_column_ratio]

theorem original_window_gcd (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y)
    (f : SupportedIdeal→SupportedIdeal→ℂ) :
    (∑I∈lowGaussColumns W hW Y hY,∑J∈lowGaussColumns W hW Y hY,f I J)=
      ∑C∈commonPool (lowGaussColumns W hW Y hY),
        ∑I∈lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY),
        ∑J∈lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY),
        if IsCoprime I.val J.val then f (supportedIdealProduct C I) (supportedIdealProduct C J) else 0 := by
  rw [finite_pair_gcd]
  simp_rw [commonColumns_window]

lemma commonPool_norm_bound (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y)
    (a b : ℝ) (hs : Function.support W⊆Set.Icc a b)
    (C : SupportedIdeal) (hC : C∈commonPool (lowGaussColumns W hW Y hY)) :
    (Ideal.absNorm C.val:ℝ)≤b*Y := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hC
  have hnp : (Ideal.absNorm p.1.val:ℝ)≤b*Y :=
    (div_le_iff₀ hY).mp (hs ((lowGaussColumns_mem W hW Y hY p.1).mp (Finset.mem_product.mp hp).1)).2
  have hg : Ideal.absNorm (gcdCommon p.1 p.2).val≤Ideal.absNorm p.1.val :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.1.property.1))
      (map_dvd Ideal.absNorm (gcd_dvd_left p.1.val p.2.val))
  exact (by exact_mod_cast hg : (Ideal.absNorm (gcdCommon p.1 p.2).val:ℝ)≤Ideal.absNorm p.1.val).trans hnp

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1515

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PhysicalCrudeMass
Source SHA256: 24664fd23cc50756de05eeb3912a5984b9b781d0661387b60324a7626286d222
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1516


namespace OAI

noncomputable section
open scoped Classical
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion ConcreteTraceCRT CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma calibration_elementNorm_ge_one (C : CalibrationData) : 1≤elementNorm C.generator := by
  unfold elementNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))

lemma sexticGauss_norm_le (s : O) (hs : s≠0) (m : O) : ‖sexticGauss s hs m‖≤elementNorm s := by
  let := finite_quotient_span hs
  let : Fintype (O⧸Ideal.span {s}) := Fintype.ofFinite _
  rw [sexticGauss,tsum_fintype]
  calc
    _ ≤ ∑d : O⧸Ideal.span {s},‖idealRowHom (GaussianShiftedPartition.representative s d) (Ideal.span {s})*
      quotientTrace s hs (Ideal.Quotient.mk _ m*d)‖ := norm_sum_le _ _
    _ ≤ ∑_d : O⧸Ideal.span {s},(1:ℝ) := Finset.sum_le_sum (fun d _=>by
      rw [norm_mul,(quotientTrace s hs).norm_apply,mul_one]
      exact idealRowHom_norm _ _)
    _ = _ := by simp [elementNorm,Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

lemma physicalRowWeight_arithmetic_form (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (X Y : ℝ) (r : PhysicalRowIndex) :
    physicalRowWeight C W0 W1 X Y r=
      (Y:ℂ)⁻¹*W1 ((Ideal.absNorm r.1.val:ℝ)/Y)*lowArithmeticCoefficient C r.1*
        (Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X):ℂ)⁻¹*
        C.residueMonoid r.2*(Real.sqrt (Ideal.absNorm r.1.val):ℂ)⁻¹*
        sexticGauss (primaryGenerator r.1.val) (supported_primaryGenerator_ne_zero r.1.val r.1.property) (-r.2)*
        W0 (elementNorm r.2/(elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X)) := by
  unfold physicalRowWeight lowArithmeticCoefficient
  split_ifs <;> simp only [mul_zero,zero_mul]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma physicalRowWeight_crude_point (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (B0 B1 : ℝ) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : ∀x,‖W0 x‖≤B0) (hW1 : ∀x,‖W1 x‖≤B1)
    (X Y : ℝ) (hX : 1≤X) (hY : 0<Y) (r : PhysicalRowIndex) :
    ‖physicalRowWeight C W0 W1 X Y r‖≤B0*B1*‖C.tau‖⁻¹/Y := by
  have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
  have hb := calibration_elementNorm_ge_one C
  have hscale : 0<elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X :=
    physicalRowScale_pos C X (lt_of_lt_of_le zero_lt_one hX) r.1
  have hqscale : (Ideal.absNorm r.1.val:ℝ)≤elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X := by
    have hbx : 1≤elementNorm C.generator*X := one_le_mul_of_one_le_of_one_le hb hX
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hqscale
  have hrad : (Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))⁻¹*
      (Real.sqrt (Ideal.absNorm r.1.val:ℝ))⁻¹*(Ideal.absNorm r.1.val:ℝ)≤1 := by
    have hspos : 0<Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X)*
      Real.sqrt (Ideal.absNorm r.1.val:ℝ) := mul_pos (Real.sqrt_pos.mpr hscale) (Real.sqrt_pos.mpr hq)
    calc
      _ = (Ideal.absNorm r.1.val:ℝ)/(Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X)*
        Real.sqrt (Ideal.absNorm r.1.val:ℝ)) := by simp only [div_eq_mul_inv,mul_inv_rev];ring
      _ ≤ 1 := (div_le_one hspos).mpr (by nlinarith [mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg (Ideal.absNorm r.1.val:ℝ)), Real.sq_sqrt hq.le])
  have hg := sexticGauss_norm_le (primaryGenerator r.1.val) (supported_primaryGenerator_ne_zero r.1.val r.1.property) (-r.2)
  have he := (primaryGenerator_spec r.1.val (supported_primaryGenerator_ne_zero r.1.val r.1.property)).1
  unfold elementNorm at hg
  rw [he] at hg
  rw [physicalRowWeight_arithmetic_form]
  simp only [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Y⁻¹*B1*‖C.tau‖⁻¹*(Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))⁻¹*
      1*(Real.sqrt (Ideal.absNorm r.1.val:ℝ))⁻¹*(Ideal.absNorm r.1.val:ℝ)*B0 := by
      gcongr
      · exact hW1 _
      · exact lowArithmeticCoefficient_norm C r.1
      · exact C.residueMonoid_norm_le_one r.2
      · exact hW0 _
    _ = (B0*B1*‖C.tau‖⁻¹/Y)*((Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))⁻¹*
        (Real.sqrt (Ideal.absNorm r.1.val:ℝ))⁻¹*(Ideal.absNorm r.1.val:ℝ)) := by ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hrad

lemma lowNumeratorRows_card (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 1≤Q) :
    ((lowNumeratorRows a b ha hb Q (lt_of_lt_of_le zero_lt_one hQ)).card:ℝ)≤256*max 1 b*Q := by
  have hscale : 1≤2*max 1 b*Q := by nlinarith [le_max_left 1 b]
  have hh := DescentFiberCost.finite_element_count_real (lowNumeratorRows a b ha hb Q (lt_of_lt_of_le zero_lt_one hQ)) _ hscale
    (by
      intro m hm
      have h := (lowOuterCutoff_support a b ha hb ((lowNumeratorRows_mem a b ha hb Q (lt_of_lt_of_le zero_lt_one hQ) m).mp hm)).2
      have hn := (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hQ)).mp h
      rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
      change elementNorm m≤2*max 1 b*Q
      exact hn.trans (by gcongr;exact le_max_right _ _))
  convert hh using 1 ; ring

lemma lowPhysicalScale_ge_one (C : CalibrationData) (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    1≤lowPhysicalScale C X Y :=
  one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (calibration_elementNorm_ge_one C) hX) hY

lemma physicalRowWeight_source_rectangle (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW1c : HasCompactSupport W1) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : PhysicalRowIndex)
    (hr : r∉(lowGaussColumns W1 hW1c Y hY) ×ˢ
      (lowNumeratorRows (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
        (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (lowPhysicalScale C X Y)
        (lowPhysicalScale_pos C X Y hX hY))) :
    physicalRowWeight C W0 W1 X Y r=0 := by
  by_cases hs : r.1∈lowGaussColumns W1 hW1c Y hY
  · have hm : r.2∉lowNumeratorRows (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
        (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (lowPhysicalScale C X Y)
        (lowPhysicalScale_pos C X Y hX hY) := fun hm=>hr (Finset.mem_product.mpr ⟨hs,hm⟩)
    have hz : lowOuterCutoff (a0*a1) (max 1 (b0*b1)) (elementNorm r.2/lowPhysicalScale C X Y)=0 := by
      simpa only [lowNumeratorRows_mem,not_not] using hm
    rw [physicalRowWeight_insert_cutoff C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y hY r]
    change lowOuterCutoff _ _ (elementNorm r.2/lowPhysicalScale C X Y)*_=0
    rw [hz,zero_mul]
  · apply physicalRowWeight_outer_zero
    simpa only [lowGaussColumns_mem,not_not] using hs

theorem physicalRowWeight_source_mass (a0 b0 a1 b1 B0 B1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hB0 : 0≤B0) (hB1 : 0≤B1) :
    ∃K : ℝ,0<K ∧ ∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W0 W1 : ℝ→ℂ,∀_hW1c : HasCompactSupport W1,
      Function.support W0⊆Set.Icc a0 b0 → Function.support W1⊆Set.Icc a1 b1 →
      (∀x,‖W0 x‖≤B0) → (∀x,‖W1 x‖≤B1) →
      ∀X Y : ℝ,1≤X → 1≤Y →
      (∑'r : PhysicalRowIndex,‖physicalRowWeight (calibrationForSet S hS) W0 W1 X Y r‖)≤
        K*lowPhysicalScale (calibrationForSet S hS) X Y := by
  let K := 32768*max 1 b1*max 1 (b0*b1)*B0*B1+1
  refine ⟨K,by dsimp only [K];positivity,?_⟩
  intro S hS W0 W1 hW1c hW0 hW1 hWB0 hWB1 X Y hX hY
  let C := calibrationForSet S hS
  have hx : 0<X := lt_of_lt_of_le zero_lt_one hX
  have hy : 0<Y := lt_of_lt_of_le zero_lt_one hY
  let Q := lowPhysicalScale C X Y
  have hQ : 1≤Q := lowPhysicalScale_ge_one C X Y hX hY
  let F := lowGaussColumns W1 hW1c Y hy
  let R := lowNumeratorRows (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) Q (lowPhysicalScale_pos C X Y hx hy)
  have hzero (r : PhysicalRowIndex) (hr : r∉F×ˢR) : ‖physicalRowWeight C W0 W1 X Y r‖=0 := by
    rw [physicalRowWeight_source_rectangle C W0 W1 hW1c a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y hx hy r hr,norm_zero]
  have hpoint (r : PhysicalRowIndex) : ‖physicalRowWeight C W0 W1 X Y r‖≤B0*B1/Y := by
    have h := physicalRowWeight_crude_point C W0 W1 B0 B1 hB0 hB1 hWB0 hWB1 X Y hX hy r
    simpa only [C,calibrationForSet_tau_norm,inv_one,mul_one] using h
  have hF : (F.card:ℝ)≤128*max 1 b1*Y := lowGaussColumns_card W1 hW1c Y hY a1 b1 hW1
  have hR : (R.card:ℝ)≤256*max 1 (b0*b1)*Q := by
    simpa only [R,max_eq_right (le_max_left 1 (b0*b1))] using lowNumeratorRows_card (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) Q hQ
  rw [tsum_eq_sum (s:=F×ˢR) hzero]
  calc
    _ ≤ ∑_r∈F×ˢR,B0*B1/Y := Finset.sum_le_sum (fun r _=>hpoint r)
    _ = (F.card:ℝ)*(R.card:ℝ)*(B0*B1/Y) := by simp [Finset.card_product,mul_assoc]
    _ ≤ (128*max 1 b1*Y)*(256*max 1 (b0*b1)*Q)*(B0*B1/Y) := by gcongr
    _ = (32768*max 1 b1*max 1 (b0*b1)*B0*B1)*Q := by field_simp;ring
    _ ≤ K*Q := mul_le_mul_of_nonneg_right (by dsimp only [K];linarith) (le_trans zero_le_one hQ)

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1516

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianPhysicalMass
Source SHA256: 2cbd12dbfc4ab2a97160cd8d9733e7867ac7e0c75c9c974fe37be5498d4d0c32
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1517



namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gaussianPhysicalScaleMass {α ι : Type*} [Fintype ι]
    (C : CalibrationData) (F : Finset α) (a : α→ℂ) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) : ℝ :=
  ∑k∈F,‖a k‖*(∏i,‖W i (q k i)‖)*lowPhysicalScale C (X k) (Y k)

theorem gaussianPhysicalFamily_mass_bound (a0 b0 a1 b1 B0 B1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hB0 : 0≤B0) (hB1 : 0≤B1) :
    ∃K : ℝ,0<K ∧ ∀{α ι : Type*} [Fintype ι],
      ∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W0 W1 : ℝ→ℂ,∀_hW1c : HasCompactSupport W1,
      Function.support W0⊆Set.Icc a0 b0 → Function.support W1⊆Set.Icc a1 b1 →
      (∀x,‖W0 x‖≤B0) → (∀x,‖W1 x‖≤B1) →
      ∀F : Finset α,∀a : α→ℂ,∀X Y : α→ℝ,
      (∀k∈F,1≤X k)→(∀k∈F,1≤Y k)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      gaussianPhysicalFamilyMass (calibrationForSet S hS) W0 W1 F a X Y W q≤
        K*gaussianPhysicalScaleMass (calibrationForSet S hS) F a X Y W q := by
  obtain ⟨K,hK,hb⟩ := physicalRowWeight_source_mass a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1
  refine ⟨K,hK,?_⟩
  intro α ι _ S hS W0 W1 hW1c hW0 hW1 hWB0 hWB1 F a X Y hX hY W q
  unfold gaussianPhysicalFamilyMass gaussianPhysicalScaleMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  calc
    _ ≤ (‖a k‖*(∏i,‖W i (q k i)‖))*(K*lowPhysicalScale (calibrationForSet S hS) (X k) (Y k)) :=
      mul_le_mul_of_nonneg_left (hb S hS W0 W1 hW1c hW0 hW1 hWB0 hWB1 (X k) (Y k) (hX k hk) (hY k hk)) (by positivity)
    _ = _ := by ring

theorem gaussianPhysicalFamily_remote_polynomial (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (N : ℕ)
    (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1) (hB0 : 0≤B0) (hB1 : 0≤B1) :
    ∃K : ℝ,0<K ∧ ∀{α ι : Type*} [Fintype ι],
      ∀η : HeckeFamily.Character,∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W0 W1 : ℝ→ℂ,HasCompactSupport W0→HasCompactSupport W1→
      Function.support W0⊆Set.Icc a0 b0 → Function.support W1⊆Set.Icc a1 b1 →
      (∀x,‖W0 x‖≤B0) → (∀x,‖W1 x‖≤B1) →
      ∀F : Finset α,∀a : α→ℂ,∀D : α→Id,∀X Y : α→ℝ,
      (∀k∈F,1≤X k)→(∀k∈F,1≤Y k)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      ∀Z A : ℝ,0<Z→1≤A→
      Summable (fun j : ℕ=>if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianPhysicalFamilyIntegral η (calibrationForSet S hS) W0 W1 F a D X Y W q V hV ((2:ℝ)^j) Z‖ else 0) ∧
      (∑'j : ℕ,if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianPhysicalFamilyIntegral η (calibrationForSet S hS) W0 W1 F a D X Y W q V hV ((2:ℝ)^j) Z‖ else 0)≤
          K*gaussianPhysicalScaleMass (calibrationForSet S hS) F a X Y W q*Z^2/A^N := by
  obtain ⟨C0,hC0,hremote⟩ := gaussianPhysicalFamily_remote V hV N
  obtain ⟨C1,hC1,hmass⟩ := gaussianPhysicalFamily_mass_bound a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1
  refine ⟨C0*C1,mul_pos hC0 hC1,?_⟩
  intro α ι _ η S hS W0 W1 hW0c hW1c hW0 hW1 hWB0 hWB1 F a D X Y hX hY W q Z A hZ hA
  have hh := hremote η (calibrationForSet S hS) W0 W1 hW0c hW1c F a D X Y
    (fun k hk=>lt_of_lt_of_le zero_lt_one (hX k hk)) (fun k hk=>lt_of_lt_of_le zero_lt_one (hY k hk)) W q Z A hZ hA
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hm := hmass S hS W0 W1 hW1c hW0 hW1 hWB0 hWB1 F a X Y hX hY W q
  calc
    _ ≤ C0*(C1*gaussianPhysicalScaleMass (calibrationForSet S hS) F a X Y W q)*Z^2/A^N := by gcongr
    _ = _ := by ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1517

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RestrictedEnergy
Source SHA256: 9379aa46d3688feb0e18b78584aa660ff69de898771519376713d8d8180975b7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1518



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentRestrictedEnergy
open CanonicalQuadraticSieve CanonicalRowCompletion CenteredMomentRowNorm
open CenteredMomentPlainEnergy CenteredMomentPlainChildEnergy CenteredMomentCauchy CenteredMomentSmooth
open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def restrictedEnergy {α : Type*} (keep : O → Prop) (S : Finset α) (a : α → O)
    (c : α → ℂ) (W : 𝓢(ℝ, ℂ)) (K : ℝ) : ℝ :=
  ∑' z : O, if keep z then ‖rowPolynomial S a c z‖^2*(W (‖eisEmbedding z‖^2/K)).re else 0

theorem restricted_summable {α : Type*} (keep : O → Prop) (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O => if keep z then
      ‖rowPolynomial S a c z‖^2*(W (‖eisEmbedding z‖^2/K)).re else 0) := by
  have hs := Complex.hasSum_re (rowEnergy_summable S a ha c W K hK).hasSum
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hs
  exact hs.summable.indicator {z | keep z}

theorem finite_energy_le_restricted {α : Type*} (keep : O → Prop) (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hkeep : ∀ z ∈ rows, keep z)
    (hW : ∀ z : O, 0 ≤ (W (‖eisEmbedding z‖^2/K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖eisEmbedding z‖^2/K)).re) :
    (∑ z ∈ rows, ‖rowPolynomial S a c z‖^2) ≤ restrictedEnergy keep S a c W K := by
  calc
    _ ≤ ∑ z ∈ rows, if keep z then
        ‖rowPolynomial S a c z‖^2*(W (‖eisEmbedding z‖^2/K)).re else 0 := by
      apply Finset.sum_le_sum
      intro z hz
      rw [ite_eq_left (hkeep z hz)]
      exact le_mul_of_one_le_right (sq_nonneg _) (hmajor z hz)
    _ ≤ _ := sum_le_hasSum rows
      (by intro z hz; split_ifs; exact mul_nonneg (sq_nonneg _) (hW z); exact le_rfl)
      (restricted_summable keep S a ha c W K hK).hasSum

theorem finite_negative_energy_le_restricted {α : Type*} (keep : O → Prop)
    (S : Finset α) (a : α → O) (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hkeep : ∀ z ∈ rows, keep (-z))
    (hW : ∀ z : O, 0 ≤ (W (‖eisEmbedding z‖^2/K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖eisEmbedding z‖^2/K)).re) :
    (∑ z ∈ rows, ‖rowPolynomial S a c (-z)‖^2) ≤ restrictedEnergy keep S a c W K := by
  have he := finite_energy_le_restricted keep S a ha c W K hK (rows.image Neg.neg)
    (by intro z hz; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz; exact hkeep w hw) hW
    (by intro z hz; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
        simpa only [map_neg,norm_neg] using hmajor w hw)
  rwa [Finset.sum_image (fun x hx y hy hxy => neg_injective hxy)] at he

def nonexceptional (η : HeckeFamily.Character) (χ : RayFourExpansion.RayCharacter)
    (Q : Ideal O) (m A₀ z : O) : Prop :=
  z ≠ 0 ∧ ¬CenteredExceptionalProfile.FixedInducingRow
    (CenteredMomentChildRows.childCharacter η χ) Q m A₀ z

theorem nonexceptional_reflection (η : HeckeFamily.Character)
    (χ ξ : RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72:O)}) (m A₀ z : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    nonexceptional η χ Q m A₀ z ↔ nonexceptional η ξ Q m A₀ (-z) := by
  unfold nonexceptional
  rw [neg_ne_zero]
  exact and_congr Iff.rfl (CenteredMomentExceptionalReflection.not_fixedInducingRow_reflection_iff
    η χ ξ Q hQ m A₀ z hmLam hm2)

theorem nonexceptional_ray_independent (η : HeckeFamily.Character)
    (χ ξ : RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72:O)}) (m A₀ z : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    nonexceptional η χ Q m A₀ z ↔ nonexceptional η ξ Q m A₀ z := by
  have h₁ := nonexceptional_reflection η χ ξ Q hQ m A₀ z hmLam hm2
  have h₂ := nonexceptional_reflection η ξ ξ Q hQ m A₀ (-z) hmLam hm2
  simpa only [neg_neg] using h₁.trans h₂

theorem whole_kernel_restricted_child_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (a : α → O) (b : β → O)
        (_ha : ∀ i, Supported (Ideal.span {a i}))
        (_hb : ∀ j, Supported (Ideal.span {b j}))
        (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ) (η : O → ℂ) (keep₁ keep₂ : O → Prop),
      (∀ z ∈ rows, keep₁ z) → (∀ z ∈ rows, keep₂ (-z)) →
      (∀ z ∈ rows, ‖η z‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      ∀ E₁ E₂ : ℝ, 0 ≤ E₁ → 0 ≤ E₂ →
      (∀ t : ℝ, (restrictedEnergy keep₁ S a (fun i => c i * columnPhase (V 2) (u i) t) U K) ≤
        (E₁ * (1 + ‖t‖) ^ J₁) ^ 2) →
      (∀ t : ℝ, (restrictedEnergy keep₂ T b (fun j => d j * star (columnPhase (V 3) (v j) t)) U K) ≤
        (E₂ * (1 + ‖t‖) ^ J₂) ^ 2) →
      (1 + R) ^ A * ‖∑ z ∈ rows, η z *
        (∑ i ∈ S, ∑ j ∈ T,
          ((c i * idealRowHom z (Ideal.span {a i})) * star (d j * idealRowHom (-z) (Ideal.span {b j}))) *
            wholeKernel W V R (ρ z) (x z) (u i) (v j))‖ ≤ C * (E₁ * E₂) := by
  obtain ⟨C, hC, hbound⟩ := whole_kernel_row_estimate W V M hM hV A (J₁ + J₂)
  refine ⟨C, hC, ?_⟩
  intro R hR α β rows S T a b ha hb c d u v ρ x η keep₁ keep₂ hkeep₁ hkeep₂ hη hV₀ hV₁ U K hK hU hmajor
    E₁ E₂ hE₁ hE₂ hleft hright
  apply hbound R hR rows S T
    (fun z i => c i * idealRowHom z (Ideal.span {a i}))
    (fun z j => d j * idealRowHom (-z) (Ideal.span {b j})) u v ρ x η hη hV₀ hV₁
    (E₁ * E₂) (mul_nonneg hE₁ hE₂)
  intro t
  have hL := (finite_energy_le_restricted keep₁ S a ha
    (fun i => c i * columnPhase (V 2) (u i) t) U K hK rows hkeep₁ hU hmajor).trans (hleft t)
  have hR' := (finite_negative_energy_le_restricted keep₂ T b hb
    (fun j => d j * star (columnPhase (V 3) (v j) t)) U K hK rows hkeep₂ hU hmajor).trans (hright t)
  have hl : Real.sqrt (∑ z ∈ rows,
      ‖rowPolynomial S a (fun i => c i * columnPhase (V 2) (u i) t) z‖ ^ 2) ≤
      E₁ * (1 + ‖t‖) ^ J₁ := (Real.sqrt_le_iff).mpr ⟨by positivity, hL⟩
  have hr : Real.sqrt (∑ z ∈ rows,
      ‖rowPolynomial T b (fun j => d j * star (columnPhase (V 3) (v j) t)) (-z)‖ ^ 2) ≤
      E₂ * (1 + ‖t‖) ^ J₂ := (Real.sqrt_le_iff).mpr ⟨by positivity, hR'⟩
  simp only [leftColumn_eq_rowPolynomial, rightColumn_eq_star_rowPolynomial, norm_star]
  calc
    _ ≤ (E₁ * (1 + ‖t‖) ^ J₁) * (E₂ * (1 + ‖t‖) ^ J₂) :=
      mul_le_mul hl hr (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

end SevenEighths.CenteredMomentRestrictedEnergy

end

end OAI
end OAIOriginalModule1518

/-! Original module: OAI.NumberTheory.DirichletL.Moments.Scale
Source SHA256: 2aa15a33c9a28a32f1513097b165546faee8c7c2a6aa2a6b0bba377e4ca976d4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1519


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentScale
open CenteredMomentSmooth EisensteinSchwartzPoisson

theorem logarithmic_kernel_argument (K H A B K₀ H₀ A₀ B₀ : ℝ)
    (hK : 0 < K) (hH : 0 < H) (hA : 0 < A) (hB : 0 < B)
    (hK₀ : 0 < K₀) (hH₀ : 0 < H₀) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) :
    (K₀ * H₀ / (A₀ * B₀)) *
      Real.exp (Real.log (K / K₀) + Real.log (H / H₀) -
        Real.log (A / A₀) - Real.log (B / B₀)) = K * H / (A * B) := by
  rw [Real.exp_sub, Real.exp_sub, Real.exp_add,
    Real.exp_log (div_pos hK hK₀), Real.exp_log (div_pos hH hH₀),
    Real.exp_log (div_pos hA hA₀), Real.exp_log (div_pos hB hB₀)]
  field_simp

theorem rootWindow_log_ratio (V : ℝ → ℂ) (A A₀ : ℝ) (hA : 0 < A) (hA₀ : 0 < A₀) :
    rootWindow V (Real.log (A / A₀)) =
      (Real.sqrt A₀ : ℂ) * V (Real.log (A / A₀)) / (Real.sqrt A : ℂ) := by
  rw [rootWindow, Real.exp_log (div_pos hA hA₀), Real.sqrt_div hA.le, Complex.ofReal_div]
  field_simp

theorem wholeKernel_actual (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (K H A B K₀ H₀ A₀ B₀ : ℝ)
    (hK : 0 < K) (hH : 0 < H) (hA : 0 < A) (hB : 0 < B)
    (hK₀ : 0 < K₀) (hH₀ : 0 < H₀) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) :
    wholeKernel W V (K₀ * H₀ / (A₀ * B₀))
      (Real.log (K / K₀)) (Real.log (H / H₀))
      (Real.log (A / A₀)) (Real.log (B / B₀)) =
      (((Real.sqrt A₀ : ℂ) * (Real.sqrt B₀ : ℂ)) /
        ((Real.sqrt A : ℂ) * (Real.sqrt B : ℂ))) *
      (V 0 (Real.log (K / K₀)) * V 1 (Real.log (H / H₀)) *
        V 2 (Real.log (A / A₀)) * V 3 (Real.log (B / B₀))) *
      paperRadialFourier W (K * H / (A * B)) := by
  rw [wholeKernel, rootWindow_log_ratio _ A A₀ hA hA₀,
    rootWindow_log_ratio _ B B₀ hB hB₀,
    logarithmic_kernel_argument K H A B K₀ H₀ A₀ B₀ hK hH hA hB hK₀ hH₀ hA₀ hB₀]
  ring

theorem normalized_kernel_actual (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (K H A B K₀ H₀ A₀ B₀ : ℝ)
    (hK : 0 < K) (hH : 0 < H) (hA : 0 < A) (hB : 0 < B)
    (hK₀ : 0 < K₀) (hH₀ : 0 < H₀) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) :
    (K : ℂ) / ((Real.sqrt A : ℂ) * (Real.sqrt B : ℂ)) *
      (V 0 (Real.log (K / K₀)) * V 1 (Real.log (H / H₀)) *
        V 2 (Real.log (A / A₀)) * V 3 (Real.log (B / B₀))) *
      paperRadialFourier W (K * H / (A * B)) =
    (K : ℂ) / ((Real.sqrt A₀ : ℂ) * (Real.sqrt B₀ : ℂ)) *
      wholeKernel W V (K₀ * H₀ / (A₀ * B₀))
        (Real.log (K / K₀)) (Real.log (H / H₀))
        (Real.log (A / A₀)) (Real.log (B / B₀)) := by
  rw [wholeKernel_actual W V K H A B K₀ H₀ A₀ B₀ hK hH hA hB hK₀ hH₀ hA₀ hB₀]
  have ha : (Real.sqrt A₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hA₀).ne'
  have hb : (Real.sqrt B₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hB₀).ne'
  field_simp

end SevenEighths.CenteredMomentScale

end

end OAI
end OAIOriginalModule1519

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondDescent
Source SHA256: 5208e01f67df6a509688af29269f9e6e0987cddc5b4f3c5fd0727016c1deb6b1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1520



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondDescent
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentFixedRay
open CenteredMomentRowNorm CenteredMomentSmooth CenteredMomentPlainChildEnergy RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

private theorem weighted_norm_sum {α : Type*} (S : Finset α) (a f : α → ℂ)
    (r : ℝ) (hr : 0 ≤ r) (B : α → ℝ)
    (hB : ∀ i ∈ S, r*‖f i‖ ≤ B i) :
    r*‖∑ i ∈ S, a i*f i‖ ≤ ∑ i ∈ S, ‖a i‖*B i := by
  calc
    _ ≤ r*∑ i ∈ S, ‖a i*f i‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hr
    _ = ∑ i ∈ S, ‖a i‖*(r*‖f i‖) := by simp only [Finset.mul_sum,norm_mul]; congr 1; funext i; ring
    _ ≤ _ := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hB i hi) (norm_nonneg _))

theorem actual_row_children {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
    (D E : O) (a : α → O) (b : β → O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j}))
    (hpD : ConcretePrimeRowBridge.goodLambda^2 ∣ D-1)
    (hpE : ConcretePrimeRowBridge.goodLambda^2 ∣ E-1)
    (hpa : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1)
    (hpb : ∀ j, ConcretePrimeRowBridge.goodLambda^2 ∣ b j-1)
    (hcopA : ∀ i, IsCoprime (D*E) (a i)) (hcopB : ∀ j, IsCoprime (D*E) (b j))
    (q : O → ℂ) (c : α → ℂ) (d : β → ℂ) (K : O → α → β → ℂ) :
    (∑ z ∈ rows, q z * ∑ i ∈ S, ∑ j ∈ T,
      (if IsCoprime (a i) (b j) then
        actualCorrelation (D*a i) (E*b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) z
        else 0) * (c i*star (d j))*K z i j) =
      ∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
        (UniqueFactorizationMonoid.moebius L : ℂ) *
          ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (phaseTable D E) χ ξ *
            ∑ z ∈ rows, (q z*actualCorrelation D E hD hE z) *
              ∑ i ∈ S, ∑ j ∈ T,
                ((divisorCoefficient L a c χ i*idealRowHom z (Ideal.span {a i})) *
                  star (divisorCoefficient L b d (ξ⁻¹) j*idealRowHom (-z) (Ideal.span {b j}))) * K z i j := by
  simp_rw [finite_correlation_children S T D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro L hL
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro ξ hξ
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem finite_ray_divisor_bound (L : Finset (Ideal O)) (D E : O)
    (F : Ideal O → RayCharacter → RayCharacter → ℂ)
    (r C : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C) (B₁ B₂ : Ideal O → ℝ)
    (hB₁ : ∀ I ∈ L, 0 ≤ B₁ I) (hB₂ : ∀ I ∈ L, 0 ≤ B₂ I)
    (hF : ∀ I ∈ L, ∀ χ ξ, r*‖F I χ ξ‖ ≤ C*(B₁ I*B₂ I)) :
    r*‖∑ I ∈ L, (UniqueFactorizationMonoid.moebius I : ℂ)*
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (phaseTable D E) χ ξ * F I χ ξ‖ ≤
      (256*C)*∑ I ∈ L, ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖*(B₁ I*B₂ I) := by
  have he (I : Ideal O) (hI : I ∈ L) :
      r*‖∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff (phaseTable D E) χ ξ*F I χ ξ‖ ≤ (256*C)*(B₁ I*B₂ I) := by
    calc
      _ ≤ ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          ‖pairCoeff (phaseTable D E) χ ξ‖*(C*(B₁ I*B₂ I)) := by
        have h := weighted_norm_sum Finset.univ (fun _ : RayCharacter => (1 : ℂ))
          (fun χ => ∑ ξ : RayCharacter, pairCoeff (phaseTable D E) χ ξ*F I χ ξ) r hr
          (fun χ => ∑ ξ : RayCharacter, ‖pairCoeff (phaseTable D E) χ ξ‖*(C*(B₁ I*B₂ I)))
          (fun χ _ => weighted_norm_sum Finset.univ _ _ r hr _ (fun ξ _ => hF I hI χ ξ))
        simpa only [one_mul,norm_one] using h
      _ = (∑ χ : RayCharacter, ∑ ξ : RayCharacter, ‖pairCoeff (phaseTable D E) χ ξ‖)*
          (C*(B₁ I*B₂ I)) := by simp only [Finset.sum_mul]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right (phaseTable_mass D E)
          (mul_nonneg hC (mul_nonneg (hB₁ I hI) (hB₂ I hI)))
        convert h using 1 ; ring
  have h := weighted_norm_sum L (fun I => (UniqueFactorizationMonoid.moebius I : ℂ))
    (fun I => ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (phaseTable D E) χ ξ*F I χ ξ)
    r hr (fun I => (256*C)*(B₁ I*B₂ I)) he
  convert h using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  ring

theorem whole_kernel_actual_second_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (D E : O) (a : α → O) (b : β → O)
        (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
        (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j})),
      (ConcretePrimeRowBridge.goodLambda^2 ∣ D-1) →
      (ConcretePrimeRowBridge.goodLambda^2 ∣ E-1) →
      (∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1) →
      (∀ j, ConcretePrimeRowBridge.goodLambda^2 ∣ b j-1) →
      (∀ i, IsCoprime (D*E) (a i)) → (∀ j, IsCoprime (D*E) (b j)) →
      ∀ (q : O → ℂ) (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ),
      (∀ z ∈ rows, ‖q z*actualCorrelation D E hD hE z‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      ∀ (B₁ B₂ : Ideal O → ℝ),
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₁ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₂ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ χ : RayCharacter, ∀ t : ℝ,
        (rowEnergy S a (fun i => divisorCoefficient L a c χ i*columnPhase (V 2) (u i) t) U K).re ≤
          (B₁ L*(1+‖t‖)^J₁)^2) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ ξ : RayCharacter, ∀ t : ℝ,
        (rowEnergy T b (fun j => divisorCoefficient L b d ξ j*star (columnPhase (V 3) (v j) t)) U K).re ≤
          (B₂ L*(1+‖t‖)^J₂)^2) →
      (1+R)^A * ‖∑ z ∈ rows, q z * ∑ i ∈ S, ∑ j ∈ T,
        (if IsCoprime (a i) (b j) then
          actualCorrelation (D*a i) (E*b j)
            (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) z
          else 0) * (c i*star (d j))*wholeKernel W V R (ρ z) (x z) (u i) (v j)‖ ≤
        C*∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
          ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖*(B₁ L*B₂ L) := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_plain_child_bound W V M hM hV A J₁ J₂
  refine ⟨256*C,mul_nonneg (by norm_num) hC,?_⟩
  intro R hR α β rows S T D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB
    q c d u v ρ x hq hV₀ hV₁ U K hK hU hmajor B₁ B₂ hB₁ hB₂ hleft hright
  rw [actual_row_children rows S T D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB]
  apply finite_ray_divisor_bound _ D E _ ((1+R)^A) C (by positivity) hC B₁ B₂ hB₁ hB₂
  intro L hL χ ξ
  exact hbound R hR rows S T a b ha hb
    (divisorCoefficient L a c χ) (divisorCoefficient L b d (ξ⁻¹)) u v ρ x
    (fun z => q z*actualCorrelation D E hD hE z) hq hV₀ hV₁ U K hK hU hmajor
    (B₁ L) (B₂ L) (hB₁ L hL) (hB₂ L hL) (hleft L hL χ) (hright L hL (ξ⁻¹))

end SevenEighths.CenteredMomentSecondDescent

end

end OAI
end OAIOriginalModule1520

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondDiagonal
Source SHA256: bf84acd6f2501049af78b952def37a0e69a11f4adde76a136a7dafa60ac63c67
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1521



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondDiagonal
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem full_zero_off_diagonal (u v : O)
    [Fintype (Residue u)] [Fintype (Residue v)]
    (χ : MulChar (Residue u) ℂ) (ψ : MulChar (Residue v) ℂ)
    (hne : (Ideal.span {u} : Ideal O) ≠ Ideal.span {v}) :
    fullModulusCorrelation u v χ ψ 0 = 0 := by
  unfold fullModulusCorrelation fullCorrelation
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_congruence]
  split_ifs with hc
  · by_cases hx0 : χ (Ideal.Quotient.mk _ x) = 0
    · rw [hx0,zero_mul]
    by_cases hy0 : ψ (Ideal.Quotient.mk _ y) = 0
    · rw [hy0,star_zero,mul_zero]
    have hux : IsCoprime u x := ((Ideal.isCoprime_span_singleton_iff x u).mp
      ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp hx0))).symm
    have hvy : IsCoprime v y := ((Ideal.isCoprime_span_singleton_iff y v).mp
      ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp hy0))).symm
    simp only [sub_zero] at hc
    have hu : u ∣ v*x := by
      have he := dvd_add ((dvd_mul_right u v).trans hc) (dvd_mul_right u y)
      convert he using 1 ; ring
    have hv : v ∣ u*y := by
      have he := dvd_sub (dvd_mul_right v x) ((dvd_mul_left v u).trans hc)
      convert he using 1 ; ring
    have huv := hux.dvd_of_dvd_mul_right hu
    have hvu := hvy.dvd_of_dvd_mul_right hv
    exact False.elim (hne (le_antisymm (Ideal.span_singleton_le_span_singleton.mpr hvu)
      (Ideal.span_singleton_le_span_singleton.mpr huv)))
  · rfl

theorem full_same_zero (u : O) (hu : u ≠ 0) [Fintype (Residue u)]
    (χ : MulChar (Residue u) ℂ) :
    fullModulusCorrelation u u χ χ 0 = ∑ x : Residue u, χ x*star (χ x) := by
  have hcong (x y : Residue u) :
      scaledResidue u u (u*u) rfl x - scaledResidue u u (u*u) (mul_comm u u) y =
        Ideal.Quotient.mk (Ideal.span {u*u}) 0 ↔ x=y := by
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [scaledResidue_congruence,sub_zero,← mul_sub,mul_dvd_mul_iff_left hu]
    exact Ideal.mem_span_singleton.symm.trans Ideal.Quotient.eq.symm
  simp only [fullModulusCorrelation,fullCorrelation,hcong,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem full_same_zero_norm_le (u : O) (hu : u ≠ 0) [Fintype (Residue u)]
    (χ : MulChar (Residue u) ℂ) :
    ‖fullModulusCorrelation u u χ χ 0‖ ≤ (Fintype.card (Residue u) : ℝ) := by
  rw [full_same_zero u hu χ]
  calc
    _ ≤ ∑ x : Residue u, ‖χ x*star (χ x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue u, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hn : χ x = 0
      · simp only [hn,zero_mul,norm_zero,zero_le_one]
      · rw [MulChar.star_apply',MulChar.inv_apply_eq_inv',mul_inv_cancel₀ hn,norm_one]
    _ = _ := by simp

theorem actual_zero_off_diagonal (u v : O) (hu : Supported (Ideal.span {u}))
    (hv : Supported (Ideal.span {v}))
    (hpu : ConcretePrimeRowBridge.goodLambda^2 ∣ u-1)
    (hpv : ConcretePrimeRowBridge.goodLambda^2 ∣ v-1) (hne : u ≠ v) :
    actualCorrelation u v hu hv 0 = 0 := by
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero u hu)
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero v hv)
  let : Fintype (Residue u) := Fintype.ofFinite _
  let : Fintype (Residue v) := Fintype.ofFinite _
  apply full_zero_off_diagonal u v
  intro he
  apply hne
  rw [← primaryGenerator_span u (supported_element_ne_zero u hu) hpu,
    ← primaryGenerator_span v (supported_element_ne_zero v hv) hpv,he]

theorem actual_same_zero_norm_le (u : O) (hu : Supported (Ideal.span {u})) :
    ‖actualCorrelation u u hu hu 0‖ ≤ (Ideal.absNorm (Ideal.span {u}) : ℝ) := by
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero u hu)
  let : Fintype (Residue u) := Fintype.ofFinite _
  have hb := full_same_zero_norm_le u (supported_element_ne_zero u hu) (supportedModulusCharacter u hu)
  simpa only [actualCorrelation,supportedCorrelation,Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card] using hb

theorem divisible_ideal_card (S : Finset (Ideal O)) (s : Ideal O) (hs : s ≠ 0)
    (hS : ∀ I ∈ S, I ≠ 0) (hdiv : ∀ I ∈ S, s ∣ I)
    (Y : ℝ) (hY : 0 ≤ Y) (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y) :
    (S.card : ℝ) ≤ 128*Y/(Ideal.absNorm s : ℝ) := by
  by_cases hempty : S.Nonempty
  · have hquot (I : Ideal O) (hI : I ∈ S) : idealQuotient s I ≠ 0 :=
      ne_zero_of_dvd_ne_zero (hS I hI) (idealQuotient_dvd (hdiv I hI))
    have hbound (I : Ideal O) (hI : I ∈ S) := idealQuotient_norm_le hs (hdiv I hI) Y (hN I hI)
    obtain ⟨I,hI⟩ := hempty
    have hscale : 1 ≤ Y/(Ideal.absNorm s : ℝ) := by
      have hn : (1:ℝ) ≤ Ideal.absNorm (idealQuotient s I) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hquot I hI))
      exact hn.trans (hbound I hI)
    have hc := DescentFiberCost.finite_ideal_count_real (S.image (idealQuotient s)) _ hscale
      (by intro J hJ; obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ; exact hquot I hI)
      (by intro J hJ; obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ; exact hbound I hI)
    rw [Finset.card_image_of_injOn (fun I hI J hJ he => idealQuotient_injective_on s
      (hdiv I hI) (hdiv J hJ) he)] at hc
    convert hc using 1 ; ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hempty,Finset.card_empty,Nat.cast_zero]
    positivity

def secondZeroEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) : ℂ :=
  ∑ i ∈ S, ∑ j ∈ S, (c i*star (c j)) *
    (actualCorrelation (a i) (a j) (ha i) (ha j) 0 /
      ((Real.sqrt (Ideal.absNorm (Ideal.span {a i}) : ℝ) : ℂ)*
       (Real.sqrt (Ideal.absNorm (Ideal.span {a j}) : ℝ) : ℂ)))

theorem secondZeroEnergy_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hp : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1)
    (hinj : Set.InjOn a S) (c : α → ℂ) :
    ‖secondZeroEnergy S a ha c‖ ≤ ∑ i ∈ S, ‖c i‖^2 := by
  have hroot (i : α) :
      ((Real.sqrt (Ideal.absNorm (Ideal.span {a i}) : ℝ) : ℂ)*
       (Real.sqrt (Ideal.absNorm (Ideal.span {a i}) : ℝ) : ℂ)) =
        (Ideal.absNorm (Ideal.span {a i}) : ℂ) := by
    rw [← Complex.ofReal_mul,Real.mul_self_sqrt (Nat.cast_nonneg _),Complex.ofReal_natCast]
  have he : secondZeroEnergy S a ha c =
      ∑ i ∈ S, (c i*star (c i)) *
        (actualCorrelation (a i) (a i) (ha i) (ha i) 0 /(Ideal.absNorm (Ideal.span {a i}) : ℂ)) := by
    unfold secondZeroEnergy
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · rw [hroot]
    · intro j hj hji
      have hne : a i ≠ a j := fun he => hji (hinj hi hj he).symm
      rw [actual_zero_off_diagonal _ _ (ha i) (ha j) (hp i) (hp j) hne,zero_div,mul_zero]
    · exact fun hnot => False.elim (hnot hi)
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul,norm_mul,norm_star,norm_div,Complex.norm_natCast,← pow_two]
  have hN : 0 < (Ideal.absNorm (Ideal.span {a i}) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (ha i).1)
  exact mul_le_of_le_one_right (sq_nonneg _) ((div_le_one hN).mpr (actual_same_zero_norm_le _ (ha i)))

theorem primary_column_card {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hp : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1)
    (hinj : Set.InjOn a S) (s : Ideal O) (hs : s ≠ 0)
    (hdiv : ∀ i ∈ S, s ∣ Ideal.span {a i}) (Y : ℝ) (hY : 0 ≤ Y)
    (hN : ∀ i ∈ S, (Ideal.absNorm (Ideal.span {a i}) : ℝ) ≤ Y) :
    (S.card : ℝ) ≤ 128*Y/(Ideal.absNorm s : ℝ) := by
  have hspan : Set.InjOn (fun i => (Ideal.span {a i} : Ideal O)) S := by
    intro i hi j hj he
    dsimp only at he
    apply hinj hi hj
    rw [← primaryGenerator_span (a i) (supported_element_ne_zero _ (ha i)) (hp i),
      ← primaryGenerator_span (a j) (supported_element_ne_zero _ (ha j)) (hp j),he]
  have hb := divisible_ideal_card (S.image (fun i => Ideal.span {a i})) s hs
    (by intro I hI; obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI; exact (ha i).1)
    (by intro I hI; obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI; exact hdiv i hi)
    Y hY (by intro I hI; obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI; exact hN i hi)
  rwa [Finset.card_image_of_injOn hspan] at hb

theorem secondZeroEnergy_divisor_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hp : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1)
    (hinj : Set.InjOn a S) (c : α → ℂ) (B : ℝ) (_hB : 0 ≤ B)
    (hc : ∀ i ∈ S, ‖c i‖ ≤ B) (s : Ideal O) (hs : s ≠ 0)
    (hdiv : ∀ i ∈ S, s ∣ Ideal.span {a i}) (Y : ℝ) (hY : 0 ≤ Y)
    (hN : ∀ i ∈ S, (Ideal.absNorm (Ideal.span {a i}) : ℝ) ≤ Y) :
    ‖secondZeroEnergy S a ha c‖ ≤ 128*B^2*Y/(Ideal.absNorm s : ℝ) := by
  calc
    _ ≤ ∑ i ∈ S, ‖c i‖^2 := secondZeroEnergy_bound S a ha hp hinj c
    _ ≤ ∑ _i ∈ S, B^2 := Finset.sum_le_sum (fun i hi =>
      pow_le_pow_left₀ (norm_nonneg _) (hc i hi) 2)
    _ = B^2*(S.card : ℝ) := by simp [mul_comm]
    _ ≤ B^2*(128*Y/(Ideal.absNorm s : ℝ)) :=
      mul_le_mul_of_nonneg_left (primary_column_card S a ha hp hinj s hs hdiv Y hY hN) (sq_nonneg _)
    _ = _ := by ring

theorem normalized_secondZeroEnergy_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hp : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1)
    (hinj : Set.InjOn a S) (c : α → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hc : ∀ i ∈ S, ‖c i‖ ≤ B) (s : Ideal O) (hs : s ≠ 0)
    (hdiv : ∀ i ∈ S, s ∣ Ideal.span {a i}) (Y : ℝ) (hY : 0 ≤ Y)
    (hN : ∀ i ∈ S, (Ideal.absNorm (Ideal.span {a i}) : ℝ) ≤ Y)
    (κ : ℂ) (T : ℝ) (hT : 0 < T) :
    ‖(κ/(T:ℂ))*secondZeroEnergy S a ha c‖ ≤
      128*‖κ‖*B^2*Y/(T*(Ideal.absNorm s : ℝ)) := by
  rw [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hT]
  calc
    _ ≤ (‖κ‖/T)*(128*B^2*Y/(Ideal.absNorm s : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (secondZeroEnergy_divisor_bound S a ha hp hinj c B hB hc s hs hdiv Y hY hN)
        (div_nonneg (norm_nonneg _) hT.le)
    _ = _ := by ring

end SevenEighths.CenteredMomentSecondDiagonal

end

end OAI
end OAIOriginalModule1521

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowGramDiagonal
Source SHA256: 647bc9d9e54c15a55fb52539a12d70cfeeb9d2a3da6e23dd84747cbcea53227b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1522



namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
open CenteredMomentSupportedCorrelation CenteredMomentSecondDiagonal EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGramZeroMode (C : CalibrationData) (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (U : SchwartzMap ℝ ℂ) (Q : ℝ) : ℂ :=
  (Q:ℂ)*paperRadialFourier U 0*
    secondZeroEnergy (lowGaussColumns W1 hW1 Y hY) (fun s=>primaryGenerator s.val)
      (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property) (lowGaussColumn C W1 Y σ v)

lemma lowGramZeroMode_eq_source (C : CalibrationData) (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (U : SchwartzMap ℝ ℂ) (Q : ℝ) :
    lowGramZeroMode C W1 hW1 Y hY σ v U Q=
      ((Q/Y^3:ℝ):ℂ)*
        ∑s∈lowGaussColumns W1 hW1 Y hY,∑t∈lowGaussColumns W1 hW1 Y hY,
          ((lowGramCoefficient C σ s*lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y))*
            star (lowGramCoefficient C σ t*lowGramProfile W1 v ((Ideal.absNorm t.val:ℝ)/Y)))*
          actualCorrelation (primaryGenerator s.val) (primaryGenerator t.val)
            ((supported_span_primaryGenerator_iff s.val).mpr s.property)
            ((supported_span_primaryGenerator_iff t.val).mpr t.property) 0*paperRadialFourier U 0 := by
  unfold lowGramZeroMode secondZeroEnergy
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  have hes := congrArg Ideal.absNorm ((primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1)
  have het := congrArg Ideal.absNorm ((primaryGenerator_spec t.val (supported_primaryGenerator_ne_zero t.val t.property)).1)
  rw [hes,het]
  calc
    _ = ((lowGaussColumn C W1 Y σ v s*star (lowGaussColumn C W1 Y σ v t))*
        ((Q:ℂ)/((Real.sqrt (Ideal.absNorm s.val:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm t.val:ℝ):ℂ))))*
        actualCorrelation (primaryGenerator s.val) (primaryGenerator t.val) _ _ 0*paperRadialFourier U 0 := by ring
    _ = _ := by rw [lowGram_pair_prefactor C W1 Y hY σ v Q s t];ring

lemma lowGramZeroMode_bound (C : CalibrationData) (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (U : SchwartzMap ℝ ℂ) (Q : ℝ) (hQ : 0≤Q) :
    ‖lowGramZeroMode C W1 hW1 Y hY σ v U Q‖≤
      Q*‖paperRadialFourier U 0‖*∑s∈lowGaussColumns W1 hW1 Y hY,‖lowGaussColumn C W1 Y σ v s‖^2 := by
  rw [lowGramZeroMode,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hQ]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply secondZeroEnergy_bound
  · intro s
    exact (primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).2
  · intro s hs t ht h
    apply Subtype.ext
    have hes := (primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1
    have het := (primaryGenerator_spec t.val (supported_primaryGenerator_ne_zero t.val t.property)).1
    rw [←hes,←het]
    exact congrArg (fun z : O=>Ideal.span {z}) h

theorem lowGramZeroMode_source_bound (a b B : ℝ) (ha : 0<a) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W1 : ℝ→ℂ,∀hW1 : HasCompactSupport W1,
      Function.support W1⊆Set.Icc a b→(∀x,‖W1 x‖≤B)→
      ∀Y : ℝ,∀hY : 1≤Y,∀σ : RayRing,∀v : ℝ,∀U : SchwartzMap ℝ ℂ,∀Q : ℝ,0≤Q→
      ‖lowGramZeroMode (calibrationForSet S hS) W1 hW1 Y (lt_of_lt_of_le zero_lt_one hY) σ v U Q‖≤
        C*‖paperRadialFourier U 0‖*Q/Y := by
  obtain ⟨C,hC,hb⟩ := lowGaussColumn_l2_bound a b B ha hB
  refine ⟨C,hC,?_⟩
  intro S hS W1 hW1 hWS hWB Y hY σ v U Q hQ
  apply (lowGramZeroMode_bound (calibrationForSet S hS) W1 hW1 Y (lt_of_lt_of_le zero_lt_one hY) σ v U Q hQ).trans
  calc
    _ ≤ Q*‖paperRadialFourier U 0‖*(C/Y) := by
      exact mul_le_mul_of_nonneg_left (hb S hS W1 hW1 hWS hWB Y hY σ v) (by positivity)
    _ = _ := by ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1522

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RankinRadical
Source SHA256: 5a2df3014c500ba0d83e89914fa83d1ccbd6df9572f721137ae2979288a00761
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1523



namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRankinRadical
open IdealMobiusDivisorSum UniqueFactorizationMonoid CenteredMomentDivisorAllocation
local notation "O" => ActualEisensteinCubic.O

def commonRadical (I J : Ideal O) : Ideal O :=
  ∏ P ∈ primeSupport I ∩ primeSupport J,P

theorem commonRadical_ne_zero (I J : Ideal O) : commonRadical I J ≠ 0 :=
  support_product_ne_zero Finset.inter_subset_left

theorem commonRadical_squarefree (I J : Ideal O) : Squarefree (commonRadical I J) :=
  squarefree_support_product Finset.inter_subset_left

theorem commonRadical_support (I J : Ideal O) :
    primeSupport (commonRadical I J)=primeSupport I∩primeSupport J := by
  unfold primeSupport commonRadical
  rw [factors_support_product Finset.inter_subset_left]
  simp [primeSupport]

theorem old_mask_dvd_commonRadical (s I J : Ideal O) (hs : Squarefree s)
    (hI : I ≠ 0) (hJ : J ≠ 0) (hsI : s ∣ I) (hsJ : s ∣ J) :
    s ∣ commonRadical I J := by
  apply (squarefree_dvd_iff s _ hs).mpr
  intro P hP
  have hp := support_prime hP
  have hd := dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)
  have hi : P ∈ primeSupport I := by
    simpa only [primeSupport,Multiset.mem_toFinset,mem_normalizedFactors_iff hI,hp,true_and]
      using hd.trans hsI
  have hj : P ∈ primeSupport J := by
    simpa only [primeSupport,Multiset.mem_toFinset,mem_normalizedFactors_iff hJ,hp,true_and]
      using hd.trans hsJ
  exact Finset.dvd_prod_of_mem id (Finset.mem_inter.mpr ⟨hi,hj⟩)

theorem old_mask_radical_count {α : Type*} (S : Finset α) (I J : α → Ideal O)
    (s : Ideal O) (hs : Squarefree s) (hs0 : s ≠ 0)
    (hI : ∀ a ∈ S,I a ≠ 0) (hJ : ∀ a ∈ S,J a ≠ 0)
    (hsi : ∀ a ∈ S,s ∣ I a) (hsj : ∀ a ∈ S,s ∣ J a)
    (Y : ℝ) (hY : 0 ≤ Y)
    (hN : ∀ a ∈ S,(Ideal.absNorm (commonRadical (I a) (J a)):ℝ) ≤ Y) :
    ((S.image (fun a => commonRadical (I a) (J a))).card:ℝ) ≤
      128*Y/(Ideal.absNorm s:ℝ) := by
  refine CenteredMomentSecondDiagonal.divisible_ideal_card _ s hs0 ?_ ?_ Y hY ?_
  · intro R hR
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hR
    exact commonRadical_ne_zero _ _
  · intro R hR
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hR
    exact old_mask_dvd_commonRadical s _ _ hs (hI a ha) (hJ a ha) (hsi a ha) (hsj a ha)
  · intro R hR
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hR
    exact hN a ha

end SevenEighths.CenteredMomentRankinRadical

end

end OAI
end OAIOriginalModule1523

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CompleteCommon
Source SHA256: efcfd09aba0b9c2bd96512218cb900f821f5ae62f51c14defa2640c1f62b8dfc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1524




namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCompleteCommon
open UniqueFactorizationMonoid IdealMobiusDivisorSum CenteredMomentSupport
open CenteredExceptionalCount CenteredMomentRankinRadical CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

def commonSupport (I J : Ideal O) : Finset (Ideal O) := primeSupport I ∩ primeSupport J

def commonPart (I J : Ideal O) : Ideal O :=
  ∏ P ∈ commonSupport I J, P ^ valuation I P

def residualPart (I J : Ideal O) : Ideal O :=
  ∏ P ∈ primeSupport I \ primeSupport J, P ^ valuation I P

theorem commonSupport_comm (I J : Ideal O) : commonSupport I J = commonSupport J I :=
  Finset.inter_comm _ _

theorem supportExtract_eq_power_product (I : Ideal O) (S : Finset (Ideal O)) :
    supportExtract I S = ∏ P ∈ primeSupport I ∩ S, P ^ valuation I P := by
  unfold supportExtract
  rw [Finset.prod_multiset_count_of_subset _ (primeSupport I ∩ S) (by
    intro P hP
    exact Finset.mem_inter.mpr ⟨Multiset.mem_toFinset.mpr (Multiset.mem_filter.mp
      (Multiset.mem_toFinset.mp hP)).1, (Multiset.mem_filter.mp
      (Multiset.mem_toFinset.mp hP)).2⟩)]
  apply Finset.prod_congr rfl
  intro P hP
  simp only [Multiset.count_filter, (Finset.mem_inter.mp hP).2, ↓reduceIte]
  rfl

theorem supportResidual_eq_power_product (I : Ideal O) (S : Finset (Ideal O)) :
    supportResidual I S = ∏ P ∈ primeSupport I \ S, P ^ valuation I P := by
  unfold supportResidual
  rw [Finset.prod_multiset_count_of_subset _ (primeSupport I \ S) (by
    intro P hP
    exact Finset.mem_sdiff.mpr ⟨Multiset.mem_toFinset.mpr (Multiset.mem_filter.mp
      (Multiset.mem_toFinset.mp hP)).1, (Multiset.mem_filter.mp
      (Multiset.mem_toFinset.mp hP)).2⟩)]
  apply Finset.prod_congr rfl
  intro P hP
  simp only [Multiset.count_filter, (Finset.mem_sdiff.mp hP).2]
  rfl

theorem commonPart_eq_supportExtract (I J : Ideal O) :
    commonPart I J = supportExtract I (commonSupport I J) := by
  rw [supportExtract_eq_power_product]
  simp only [commonPart, commonSupport, ← Finset.inter_assoc, Finset.inter_self]

theorem residualPart_eq_supportResidual (I J : Ideal O) :
    residualPart I J = supportResidual I (commonSupport I J) := by
  rw [supportResidual_eq_power_product]
  have he : primeSupport I \ commonSupport I J = primeSupport I \ primeSupport J := by
    ext P
    simp only [Finset.mem_sdiff, commonSupport, Finset.mem_inter]
    tauto
  rw [he]
  rfl

theorem commonPart_ne_zero (I J : Ideal O) : commonPart I J ≠ 0 := by
  rw [commonPart_eq_supportExtract]
  exact supportExtract_ne_zero _ _

theorem residualPart_ne_zero (I J : Ideal O) : residualPart I J ≠ 0 := by
  rw [residualPart_eq_supportResidual]
  exact supportResidual_ne_zero _ _

theorem reconstruct (I J : Ideal O) (hI : I ≠ 0) :
    I = commonPart I J * residualPart I J := by
  rw [commonPart_eq_supportExtract, residualPart_eq_supportResidual]
  exact (support_reconstruct I hI _).symm

theorem commonPart_support (I J : Ideal O) :
    primeSupport (commonPart I J) = commonSupport I J := by
  rw [commonPart_eq_supportExtract, supportExtract_support]
  simp only [commonSupport, ← Finset.inter_assoc, Finset.inter_self]

theorem commonParts_equal_support (I J : Ideal O) :
    primeSupport (commonPart I J) = primeSupport (commonPart J I) := by
  rw [commonPart_support, commonPart_support, commonSupport_comm I J]

theorem residualPart_support (I J : Ideal O) :
    primeSupport (residualPart I J) = primeSupport I \ primeSupport J := by
  rw [residualPart_eq_supportResidual, supportResidual_support]
  ext P
  simp only [Finset.mem_sdiff, commonSupport, Finset.mem_inter]
  tauto

theorem commonPart_valuation (I J P : Ideal O) :
    valuation (commonPart I J) P = if P ∈ commonSupport I J then valuation I P else 0 := by
  rw [commonPart_eq_supportExtract]
  exact supportExtract_count I P _

theorem residualPart_valuation (I J P : Ideal O) :
    valuation (residualPart I J) P = if P ∈ commonSupport I J then 0 else valuation I P := by
  rw [residualPart_eq_supportResidual]
  exact supportResidual_count I P _

theorem commonPart_residualPart_coprime (I J : Ideal O) :
    IsCoprime (commonPart I J) (residualPart J I) := by
  rw [commonPart_eq_supportExtract, residualPart_eq_supportResidual, ← commonSupport_comm I J]
  exact extracted_residual_coprime I J _

theorem commonPart_own_residual_coprime (I J : Ideal O) :
    IsCoprime (commonPart I J) (residualPart I J) := by
  rw [commonPart_eq_supportExtract, residualPart_eq_supportResidual]
  exact extracted_residual_coprime I I _

theorem commonProduct_leftResidual_coprime (I J : Ideal O) :
    IsCoprime (commonPart I J * commonPart J I) (residualPart I J) :=
  (commonPart_own_residual_coprime I J).mul_left (commonPart_residualPart_coprime J I)

theorem commonProduct_rightResidual_coprime (I J : Ideal O) :
    IsCoprime (commonPart I J * commonPart J I) (residualPart J I) :=
  (commonPart_residualPart_coprime I J).mul_left (commonPart_own_residual_coprime J I)

theorem residualParts_coprime (I J : Ideal O) :
    IsCoprime (residualPart I J) (residualPart J I) := by
  rw [residualPart_eq_supportResidual, residualPart_eq_supportResidual, ← commonSupport_comm I J]
  exact common_support_residual_coprime I J

theorem canonical_complete_extraction (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    I = commonPart I J * residualPart I J ∧
    J = commonPart J I * residualPart J I ∧
    commonPart I J ≠ 0 ∧ commonPart J I ≠ 0 ∧
    residualPart I J ≠ 0 ∧ residualPart J I ≠ 0 ∧
    primeSupport (commonPart I J) = commonSupport I J ∧
    primeSupport (commonPart J I) = commonSupport I J ∧
    primeSupport (residualPart I J) = primeSupport I \ primeSupport J ∧
    primeSupport (residualPart J I) = primeSupport J \ primeSupport I ∧
    IsCoprime (commonPart I J * commonPart J I) (residualPart I J) ∧
    IsCoprime (commonPart I J * commonPart J I) (residualPart J I) ∧
    IsCoprime (residualPart I J) (residualPart J I) := by
  exact ⟨reconstruct I J hI, reconstruct J I hJ,
    commonPart_ne_zero I J, commonPart_ne_zero J I,
    residualPart_ne_zero I J, residualPart_ne_zero J I,
    commonPart_support I J, (commonPart_support J I).trans (commonSupport_comm J I),
    residualPart_support I J, residualPart_support J I,
    commonProduct_leftResidual_coprime I J, commonProduct_rightResidual_coprime I J,
    residualParts_coprime I J⟩

theorem commonPart_dvd (I J : Ideal O) (hI : I ≠ 0) : commonPart I J ∣ I :=
  ⟨residualPart I J, reconstruct I J hI⟩

theorem residualPart_dvd (I J : Ideal O) (hI : I ≠ 0) : residualPart I J ∣ I :=
  ⟨commonPart I J, (reconstruct I J hI).trans (mul_comm _ _)⟩

theorem residualPart_original_coprime (I J : Ideal O) (hJ : J ≠ 0) :
    IsCoprime (residualPart I J) J := by
  conv_rhs => rw [reconstruct J I hJ]
  exact (commonPart_residualPart_coprime J I).symm.mul_right (residualParts_coprime I J)

theorem commonPart_eq_one_of_empty (I J : Ideal O) (h : commonSupport I J = ∅) :
    commonPart I J = 1 := by simp only [commonPart, h, Finset.prod_empty]

theorem residualPart_eq_of_empty (I J : Ideal O) (hI : I ≠ 0)
    (h : commonSupport I J = ∅) : residualPart I J = I := by
  have he := reconstruct I J hI
  rw [commonPart_eq_one_of_empty I J h, one_mul] at he
  exact he.symm

theorem commonSupport_empty_iff (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    commonSupport I J = ∅ ↔ IsCoprime I J := by
  rw [← IdealCoprimeSieveOperator.primeSupport_disjoint_iff hI hJ,
    Finset.disjoint_iff_inter_eq_empty]
  rfl

theorem commonPart_one_right (I : Ideal O) : commonPart I 1 = 1 := by
  apply commonPart_eq_one_of_empty
  simp only [commonSupport, primeSupport, normalizedFactors_one, Multiset.toFinset_zero, Finset.inter_empty]

theorem commonPart_one_left (J : Ideal O) : commonPart 1 J = 1 := by
  apply commonPart_eq_one_of_empty
  simp only [commonSupport, primeSupport, normalizedFactors_one, Multiset.toFinset_zero, Finset.empty_inter]

theorem residualPart_one_right (I : Ideal O) (hI : I ≠ 0) : residualPart I 1 = I := by
  apply residualPart_eq_of_empty I 1 hI
  simp only [commonSupport, primeSupport, normalizedFactors_one, Multiset.toFinset_zero, Finset.inter_empty]

theorem residualPart_one_left (J : Ideal O) : residualPart 1 J = 1 := by
  simp only [residualPart, primeSupport, normalizedFactors_one, Multiset.toFinset_zero, Finset.empty_sdiff, Finset.prod_empty]

theorem extracted_commonRadical (I J : Ideal O) :
    commonRadical (commonPart I J) (commonPart J I) = commonRadical I J := by
  unfold commonRadical
  rw [commonPart_support, commonPart_support, commonSupport_comm J I, Finset.inter_self]
  rfl

theorem commonRadical_dvd_commonPart (I J : Ideal O) : commonRadical I J ∣ commonPart I J := by
  apply support_product_dvd (commonPart_ne_zero I J)
  rw [commonPart_support]
  exact Finset.Subset.refl _

theorem squarefree_mask_survives (s I J : Ideal O) (hs : Squarefree s)
    (hI : I ≠ 0) (hJ : J ≠ 0) (hsI : s ∣ I) (hsJ : s ∣ J) :
    s ∣ commonRadical I J ∧ s ∣ commonPart I J ∧ s ∣ commonPart J I ∧
      IsCoprime s (residualPart I J) ∧ IsCoprime s (residualPart J I) := by
  have hR := old_mask_dvd_commonRadical s I J hs hI hJ hsI hsJ
  have hC := hR.trans (commonRadical_dvd_commonPart I J)
  have hD : s ∣ commonPart J I := by
    have he : commonRadical I J = commonRadical J I := by
      simp only [commonRadical, Finset.inter_comm]
    exact (he ▸ hR).trans (commonRadical_dvd_commonPart J I)
  exact ⟨hR, hC, hD,
    (commonPart_own_residual_coprime I J).of_isCoprime_of_dvd_left hC,
    (commonPart_own_residual_coprime J I).of_isCoprime_of_dvd_left hD⟩

theorem commonPart_supported (I J : Ideal O) (hI : Supported I) : Supported (commonPart I J) := by
  rw [commonPart_eq_supportExtract]
  exact supportExtract_supported I hI _

theorem residualPart_supported (I J : Ideal O) (hI : Supported I) : Supported (residualPart I J) := by
  rw [residualPart_eq_supportResidual]
  exact supportResidual_supported I hI _

theorem primaryGenerator_reconstruct (I J : Ideal O) (hI : I ≠ 0) :
    CompletedGauss.primaryGenerator I =
      CompletedGauss.primaryGenerator (commonPart I J) *
        CompletedGauss.primaryGenerator (residualPart I J) := by
  rw [← CompletedGauss.primaryGenerator_mul, ← reconstruct I J hI]

theorem primary_complete_extraction (I J : Ideal O) (hI : Supported I) (hJ : Supported J) :
    let C := CompletedGauss.primaryGenerator (commonPart I J)
    let D := CompletedGauss.primaryGenerator (commonPart J I)
    let a := CompletedGauss.primaryGenerator (residualPart I J)
    let b := CompletedGauss.primaryGenerator (residualPart J I)
    CompletedGauss.primaryGenerator I = C * a ∧
    CompletedGauss.primaryGenerator J = D * b ∧
    IsCoprime (C * D) a ∧ IsCoprime (C * D) b ∧ IsCoprime a b := by
  dsimp only
  have hC := commonPart_supported I J hI
  have hD := commonPart_supported J I hJ
  have ha := residualPart_supported I J hI
  have hb := residualPart_supported J I hJ
  have hpC := CompletedGauss.primaryGenerator_spec _
    (CanonicalQuadraticSieve.supported_primaryGenerator_ne_zero _ hC)
  have hpD := CompletedGauss.primaryGenerator_spec _
    (CanonicalQuadraticSieve.supported_primaryGenerator_ne_zero _ hD)
  have hpa := CompletedGauss.primaryGenerator_spec _
    (CanonicalQuadraticSieve.supported_primaryGenerator_ne_zero _ ha)
  have hpb := CompletedGauss.primaryGenerator_spec _
    (CanonicalQuadraticSieve.supported_primaryGenerator_ne_zero _ hb)
  refine ⟨primaryGenerator_reconstruct I J hI.1, primaryGenerator_reconstruct J I hJ.1, ?_, ?_, ?_⟩
  · apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [← Ideal.span_singleton_mul_span_singleton, hpC.1, hpD.1, hpa.1]
    exact commonProduct_leftResidual_coprime I J
  · apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [← Ideal.span_singleton_mul_span_singleton, hpC.1, hpD.1, hpb.1]
    exact commonProduct_rightResidual_coprime I J
  · apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [hpa.1, hpb.1]
    exact residualParts_coprime I J

theorem common_valuations_pos (I J P : Ideal O) (hP : P ∈ commonSupport I J) :
    0 < valuation I P ∧ 0 < valuation J P := by
  obtain ⟨hI, hJ⟩ := Finset.mem_inter.mp hP
  exact ⟨Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hI),
    Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hJ)⟩

theorem residualPart_self (I : Ideal O) : residualPart I I = 1 := by
  simp only [residualPart, Finset.sdiff_self, Finset.prod_empty]

theorem commonPart_self (I : Ideal O) (hI : I ≠ 0) : commonPart I I = I := by
  have h := reconstruct I I hI
  rw [residualPart_self, mul_one] at h
  exact h.symm

theorem absNorm_reconstruct (I J : Ideal O) (hI : I ≠ 0) :
    Ideal.absNorm I = Ideal.absNorm (commonPart I J) * Ideal.absNorm (residualPart I J) := by
  have h := congrArg Ideal.absNorm (reconstruct I J hI)
  simpa only [map_mul] using h

theorem absNorm_commonPart_le (I J : Ideal O) (hI : I ≠ 0) :
    Ideal.absNorm (commonPart I J) ≤ Ideal.absNorm I :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
    (map_dvd Ideal.absNorm (commonPart_dvd I J hI))

theorem absNorm_residualPart_le (I J : Ideal O) (hI : I ≠ 0) :
    Ideal.absNorm (residualPart I J) ≤ Ideal.absNorm I :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
    (map_dvd Ideal.absNorm (residualPart_dvd I J hI))

end SevenEighths.CenteredMomentCompleteCommon

end

end OAI
end OAIOriginalModule1524

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CanonicalFirst
Source SHA256: 33f6d67735150825c63200a09fe785aa1fed8b8601903d4c43ecca6982c909c8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1525



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentCanonicalFirst
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredExceptionalCount
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentSupportedCorrelation
open CenteredMomentFirstReduced CenteredMomentFirstActiveFourier CenteredMomentActive
open CenteredMomentCompleteCommon UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

abbrev CommonIndex (I J : Ideal O) := {P : Ideal O // P∈commonSupport I J}
instance commonIndexMaximal (I J : Ideal O) (P : CommonIndex I J) : P.val.IsMaximal := by
  have hp := prime_of_normalized_factor P.val (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

def leftExponent (I J : Ideal O) (P : CommonIndex I J) := valuation I P.val
def rightExponent (I J : Ideal O) (P : CommonIndex I J) := valuation J P.val

theorem common_good (I J : Ideal O) (hI : Supported I) (P : CommonIndex I J) :
    ConcretePrimeRowBridge.goodLambda ∉ P.val :=
  (supported_factors_good I hI P.val (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)).2.1

theorem common_odd (I J : Ideal O) (hI : Supported I) (P : CommonIndex I J) :
    ringChar (O ⧸ P.val)≠2 :=
  (supported_factors_good I hI P.val (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)).2.2

theorem leftExponent_pos (I J : Ideal O) (P : CommonIndex I J) : 0<leftExponent I J P :=
  (common_valuations_pos I J P.val P.property).1

theorem rightExponent_pos (I J : Ideal O) (P : CommonIndex I J) : 0<rightExponent I J P :=
  (common_valuations_pos I J P.val P.property).2

theorem commonPart_left_product (I J : Ideal O) :
    commonPart I J=∏ P : CommonIndex I J,P.val^leftExponent I J P := by
  exact (Finset.prod_coe_sort (s:=commonSupport I J) (f:=fun P => P^valuation I P)).symm

theorem commonPart_right_product (I J : Ideal O) :
    commonPart J I=∏ P : CommonIndex I J,P.val^rightExponent I J P := by
  unfold commonPart
  rw [commonSupport_comm J I]
  exact (Finset.prod_coe_sort (s:=commonSupport I J) (f:=fun P => P^valuation J P)).symm

abbrev ActiveIndex (I J : Ideal O) :=
  activeSupport (Finset.univ : Finset (CommonIndex I J)) (leftExponent I J) (rightExponent I J)
def activePrime (I J : Ideal O) (P : ActiveIndex I J) : Ideal O := P.val.val
instance activePrimeMaximal (I J : Ideal O) (P : ActiveIndex I J) : (activePrime I J P).IsMaximal :=
  commonIndexMaximal I J P.val

def activeConductor (I J : Ideal O) : O := finitePrimeModulus (activePrime I J)
def activeExponent (I J : Ideal O) (P : ActiveIndex I J) :=
  netExponent (leftExponent I J P.val) (rightExponent I J P.val)
theorem activeGood (I J : Ideal O) (hI : Supported I) (P : ActiveIndex I J) :
    ConcretePrimeRowBridge.goodLambda ∉ activePrime I J P := common_good I J hI P.val

theorem activeCoprime (I J : Ideal O) : Pairwise (Function.onFun IsCoprime (activePrime I J)) :=
  activePrimes_pairwise_coprime (fun P : CommonIndex I J => P.val) Subtype.val_injective
    Finset.univ (leftExponent I J) (rightExponent I J)

def activeFunction (I J : Ideal O) (hI : Supported I) : Residue (activeConductor I J) → ℂ :=
  principalSexticRow (activePrime I J) (activeCoprime I J) (activeGood I J hI)
    (activeExponent I J) (activeConductor I J) (span_finitePrimeModulus _)

def residualGenerator (I J : Ideal O) : O := CompletedGauss.primaryGenerator (residualPart I J)

theorem residualGenerator_span (I J : Ideal O) (hI : Supported I) :
    Ideal.span {residualGenerator I J}=residualPart I J :=
  (CompletedGauss.primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (residualPart_supported I J hI))).1

theorem residualGenerator_supported (I J : Ideal O) (hI : Supported I) :
    Supported (Ideal.span {residualGenerator I J}) := by
  rw [residualGenerator_span I J hI]
  exact residualPart_supported I J hI

def residualCharacter (I J : Ideal O) (hI : Supported I) : MulChar (Residue (residualGenerator I J)) ℂ :=
  supportedModulusCharacter _ (residualGenerator_supported I J hI)

@[simp] theorem residualCharacter_mk (I J : Ideal O) (hI : Supported I) (z : O) :
    residualCharacter I J hI (Ideal.Quotient.mk _ z)=idealRowHom z (residualPart I J) := by
  rw [residualCharacter,supportedModulusCharacter_mk,residualGenerator_span I J hI]

theorem original_pair_factor (I J : Ideal O) (hI : Supported I) (hJ : Supported J) (z : O) :
    idealRowHom z I*star (idealRowHom z J)=
      residualCharacter I J hI (Ideal.Quotient.mk _ z)*
        (residualCharacter J I hJ)⁻¹ (Ideal.Quotient.mk _ z)*
        (idealRowHom z (∏ P : CommonIndex I J,P.val^leftExponent I J P)*
          star (idealRowHom z (∏ P : CommonIndex I J,P.val^rightExponent I J P))) := by
  let := finite_quotient_span (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
  rw [← MulChar.star_apply',residualCharacter_mk,residualCharacter_mk,
    ← commonPart_left_product,← commonPart_right_product]
  have hi := congrArg (idealRowHom z) (reconstruct I J hI.1)
  have hj := congrArg (idealRowHom z) (reconstruct J I hJ.1)
  simp only [map_mul] at hi hj
  rw [hi,hj,star_mul]
  ring

def reducedFirstSum (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ E ∈ (principalSupport (Finset.univ : Finset (CommonIndex I J)) (leftExponent I J) (rightExponent I J)).powerset,
    let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
    let k := K/‖eisEmbedding e‖^2
    let a := residualGenerator I J
    let b := residualGenerator J I
    let r := activeConductor I J
    (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
      tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e*
      (((k/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*∑' h : O,
        tripleFourier a b r (supported_element_ne_zero _ (residualGenerator_supported I J hI))
          (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) h*
          paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a*(b*r))‖^2))

theorem canonical_pair_reduced_poisson (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑' z : O,(idealRowHom z I*star (idealRowHom z J))*W (‖eisEmbedding z‖^2/K))=
      reducedFirstSum I J hI hJ W K := by
  simp_rw [original_pair_factor I J hI hJ]
  exact common_residual_reduced_poisson (fun P : CommonIndex I J => P.val) Subtype.val_injective
    (common_good I J hI) (common_odd I J hI) Finset.univ (leftExponent I J) (rightExponent I J)
    (fun P _ => ne_of_gt (leftExponent_pos I J P)) (fun P _ => ne_of_gt (rightExponent_pos I J P))
    (residualGenerator I J) (residualGenerator J I)
    (supported_element_ne_zero _ (residualGenerator_supported I J hI))
    (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
    (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ W K hK

theorem activeConductor_span_dvd (I J : Ideal O) :
    Ideal.span {activeConductor I J} ∣ commonPart I J := by
  rw [activeConductor,span_finitePrimeModulus]
  change (∏ P : ActiveIndex I J,P.val.val) ∣ commonPart I J
  rw [Finset.prod_coe_sort]
  refine (Finset.prod_dvd_prod_of_subset _ Finset.univ
    (fun P : CommonIndex I J => P.val) (Finset.subset_univ _)).trans ?_
  rw [commonPart_left_product]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  simpa only [pow_one] using pow_dvd_pow P.val (leftExponent_pos I J P)

theorem residual_active_coprime (I J : Ideal O) (hI : Supported I) :
    IsCoprime (residualGenerator I J) (activeConductor I J) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [residualGenerator_span I J hI]
  exact (commonPart_own_residual_coprime I J).symm.of_isCoprime_of_dvd_right (activeConductor_span_dvd I J)

theorem opposite_residual_active_coprime (I J : Ideal O) (hJ : Supported J) :
    IsCoprime (residualGenerator J I) (activeConductor I J) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [residualGenerator_span J I hJ]
  exact (commonPart_residualPart_coprime I J).symm.of_isCoprime_of_dvd_right (activeConductor_span_dvd I J)

theorem residual_generators_coprime (I J : Ideal O) (hI : Supported I) (hJ : Supported J) :
    IsCoprime (residualGenerator I J) (residualGenerator J I) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [residualGenerator_span I J hI,residualGenerator_span J I hJ]
  exact residualParts_coprime I J

theorem canonical_tripleFourier_norm_le (I J : Ideal O) (hI : Supported I) (hJ : Supported J) (h : O) :
    ‖tripleFourier (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
      (supported_element_ne_zero _ (residualGenerator_supported I J hI))
      (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
      (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) h‖ ≤
      ‖eisEmbedding (activeConductor I J)‖*
        ‖residueGauss (residualGenerator I J) (supported_element_ne_zero _ (residualGenerator_supported I J hI))
          (residualCharacter I J hI) (Ideal.Quotient.mk _ h)‖*
        ‖residueGauss (residualGenerator J I) (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
          (residualCharacter J I hJ)⁻¹ (Ideal.Quotient.mk _ h)‖ := by
  exact tripleFourier_active_norm_le (activePrime I J) (activeCoprime I J) (activeGood I J hI)
    (fun P => common_odd I J hI P.val) (activeExponent I J)
    (netExponent_ne_zero _ _ _) (fun P => netExponent_lt_six _ _)
    (residualGenerator I J) (residualGenerator J I)
    (supported_element_ne_zero _ (residualGenerator_supported I J hI))
    (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
    ((residual_generators_coprime I J hI hJ).mul_right (residual_active_coprime I J hI))
    (opposite_residual_active_coprime I J hJ) _ _ h

end SevenEighths.CenteredMomentCanonicalFirst

end

end OAI
end OAIOriginalModule1525

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonSectors
Source SHA256: 8342a1e3c554fd784fa55516b70c3c71bdc2b6de681616f6271f764b4ddb13fc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1526


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonSectors
open CenteredMomentCompleteCommon CenteredMomentSupport IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

theorem primeSupport_mul (I J : Ideal O) (hI : I≠0) (hJ : J≠0) :
    primeSupport (I*J)=primeSupport I∪primeSupport J := by
  simp only [primeSupport,normalizedFactors_mul hI hJ,Multiset.toFinset_add]

theorem supportExtract_of_subset (I : Ideal O) (hI : I≠0) (S : Finset (Ideal O))
    (hS : primeSupport I⊆S) : supportExtract I S=I := by
  unfold supportExtract
  rw [Multiset.filter_eq_self.mpr (fun P hP => hS (Multiset.mem_toFinset.mpr hP))]
  exact Ideal.prod_normalizedFactors_eq_self hI

theorem supportExtract_of_disjoint (I : Ideal O) (S : Finset (Ideal O))
    (hS : Disjoint (primeSupport I) S) : supportExtract I S=1 := by
  unfold supportExtract
  rw [Multiset.filter_eq_nil.mpr (fun P hP => Finset.disjoint_left.mp hS (Multiset.mem_toFinset.mpr hP))]
  rfl

theorem reconstructed_commonSupport (C D a b : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : primeSupport C=primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b) :
    commonSupport (C*a) (D*b)=primeSupport C := by
  unfold commonSupport
  rw [primeSupport_mul C a hC ha,primeSupport_mul D b hD hb,← hCD]
  have h₁ := (IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC ha).mpr hCa
  have h₂ := (IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC hb).mpr hCb
  have h₃ := (IdealCoprimeSieveOperator.primeSupport_disjoint_iff ha hb).mpr hab
  ext P
  simp only [Finset.mem_inter,Finset.mem_union]
  constructor
  · rintro ⟨hc|ha',hd|hb'⟩
    · exact hc
    · exact hc
    · exact hd
    · exact False.elim (Finset.disjoint_left.mp h₃ ha' hb')
  · exact fun hp => ⟨Or.inl hp,Or.inl hp⟩

theorem reconstructed_commonParts (C D a b : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : primeSupport C=primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b) :
    commonPart (C*a) (D*b)=C ∧ commonPart (D*b) (C*a)=D := by
  have hs := reconstructed_commonSupport C D a b hC hD ha hb hCD hCa hCb hab
  have h₁ := (IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC ha).mpr hCa
  have h₂ := (IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC hb).mpr hCb
  constructor
  · rw [commonPart_eq_supportExtract,hs,supportExtract_mul C a hC ha,
      supportExtract_of_subset C hC _ (Finset.Subset.refl _),supportExtract_of_disjoint a _ h₁.symm,mul_one]
  · rw [commonPart_eq_supportExtract,commonSupport_comm (D*b) (C*a),hs,
      supportExtract_mul D b hD hb,
      supportExtract_of_subset D hD _ (by rw [hCD]),supportExtract_of_disjoint b _ h₂.symm,mul_one]

theorem reconstructed_residualParts (C D a b : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : primeSupport C=primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b) :
    residualPart (C*a) (D*b)=a ∧ residualPart (D*b) (C*a)=b := by
  obtain ⟨h₁,h₂⟩ := reconstructed_commonParts C D a b hC hD ha hb hCD hCa hCb hab
  constructor
  · apply mul_left_cancel₀ hC
    have he := reconstruct (C*a) (D*b) (mul_ne_zero hC ha)
    rw [h₁] at he
    exact he.symm
  · apply mul_left_cancel₀ hD
    have he := reconstruct (D*b) (C*a) (mul_ne_zero hD hb)
    rw [h₂] at he
    exact he.symm

end SevenEighths.CenteredMomentCommonSectors

end

end OAI
end OAIOriginalModule1526

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonAllocation
Source SHA256: 83a63da7d06b94c5b30a21fe471daa80d8bf49217152b657221940da2ba3051f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1527



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonAllocation
open CenteredMomentSupport CenteredMomentCommonSectors CenteredMomentExtraction
open CenteredMomentHeckeExpansion CenteredMomentRectangle HeckeFamily IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

theorem extract_coprime_product (C a : Ideal O) (hC : C≠0) (ha : a≠0)
    (hCa : IsCoprime C a) : supportExtract (C*a) (primeSupport C)=C := by
  rw [supportExtract_mul C a hC ha,
    supportExtract_of_subset C hC _ (Finset.Subset.refl _),
    supportExtract_of_disjoint a _ ((IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC ha).mpr hCa).symm,
    mul_one]

theorem residual_coprime_product (C a : Ideal O) (hC : C≠0) (ha : a≠0)
    (hCa : IsCoprime C a) : supportResidual (C*a) (primeSupport C)=a := by
  apply mul_left_cancel₀ hC
  have he := support_reconstruct (C*a) (mul_ne_zero hC ha) (primeSupport C)
  rwa [extract_coprime_product C a hC ha hCa] at he

theorem tuple_products {ι : Type*} [Fintype ι] (v : ι → Ideal O) (C a : Ideal O)
    (hC : C≠0) (ha : a≠0) (hCa : IsCoprime C a) (hv : ∏ i,v i=C*a) :
    (∏ i,supportExtract (v i) (primeSupport C))=C ∧
      (∏ i,supportResidual (v i) (primeSupport C))=a := by
  have hv0 : ∏ i,v i≠0 := hv.symm ▸ mul_ne_zero hC ha
  have hi (i : ι) : v i≠0 := Finset.prod_ne_zero_iff.mp hv0 i (Finset.mem_univ _)
  constructor
  · rw [← supportExtract_prod Finset.univ v (fun i _ => hi i),hv]
    exact extract_coprime_product C a hC ha hCa
  · rw [← supportResidual_prod Finset.univ v (fun i _ => hi i),hv]
    exact residual_coprime_product C a hC ha hCa

theorem residual_factor_coprime (C I : Ideal O) (hC : C≠0) :
    IsCoprime C (supportResidual I (primeSupport C)) := by
  have hh := extracted_residual_coprime C I (primeSupport C)
  rwa [supportExtract_of_subset C hC _ (Finset.Subset.refl _)] at hh

theorem slot_plain_products {ι : Type*} (T : Finset ι) (p : ι → Ideal O)
    (hp : ∀ i∈T,Prime (p i)) (I J C a : Ideal O) (hI : I≠0) (hJ : J≠0)
    (hC : C≠0) (ha : a≠0) (hCa : IsCoprime C a)
    (hprod : (∏ i∈T,p i)*I*J=C*a) :
    (∏ i∈T.filter (fun i => p i∈primeSupport C),p i)*
        supportExtract I (primeSupport C)*supportExtract J (primeSupport C)=C ∧
      (∏ i∈T.filter (fun i => p i∉primeSupport C),p i)*
        supportResidual I (primeSupport C)*supportResidual J (primeSupport C)=a := by
  have hp0 : (∏ i∈T,p i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i hi => (hp i hi).ne_zero)
  have hf := (prime_slot_allocation T p hp (primeSupport C)).1
  have hl := (prime_slot_allocation T p hp (primeSupport C)).2
  constructor
  · have he := extract_coprime_product C a hC ha hCa
    rw [← hprod,supportExtract_mul _ J (mul_ne_zero hp0 hI) hJ,
      supportExtract_mul _ I hp0 hI,hf] at he
    exact he
  · have he := residual_coprime_product C a hC ha hCa
    rw [← hprod,supportResidual_mul _ J (mul_ne_zero hp0 hI) hJ,
      supportResidual_mul _ I hp0 hI,hl] at he
    exact he

theorem centered_source_allocation {ι : Type*} (T : Finset ι) (p : ι → Ideal O)
    (ν : ι → ℂ) (η : Character) (m A z : O) (t : ℝ)
    (I J C a : Ideal O) (hI : I≠0) (hJ : J≠0)
    (hprod : (∏ i∈T,p i)*I*J=C*a)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) :
    (∏ i∈T,ν i)*rowWeight η m A z t ((∏ i∈T,p i)*I*J)*
      idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
      ((∏ i∈T.filter (fun i => p i∈primeSupport C),ν i)*rowWeight η m A z t C)*
        ((∏ i∈T.filter (fun i => p i∉primeSupport C),ν i)*rowWeight η m A z t a*
          idealRectangle W₁ W₂
            (X₁/Ideal.absNorm (supportExtract I (primeSupport C)))
            (X₂/Ideal.absNorm (supportExtract J (primeSupport C)))
            (Y₁/Ideal.absNorm (supportExtract I (primeSupport C)))
            (Y₂/Ideal.absNorm (supportExtract J (primeSupport C)))
            (supportResidual I (primeSupport C)) (supportResidual J (primeSupport C))) := by
  have hrect := idealRectangle_extract W₁ W₂ X₁ X₂ Y₁ Y₂
    (supportExtract I (primeSupport C)) (supportExtract J (primeSupport C))
    (supportResidual I (primeSupport C)) (supportResidual J (primeSupport C))
  rw [support_reconstruct I hI,support_reconstruct J hJ] at hrect
  rw [hprod,map_mul,hrect,← Finset.prod_filter_mul_prod_filter_not T (fun i => p i∈primeSupport C) ν]
  ring

end SevenEighths.CenteredMomentCommonAllocation

end

end OAI
end OAIOriginalModule1527

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstNormalization
Source SHA256: 76210aa2e5f0ec11d2f14ffba7205f5d88b91d386ebc3268c933693ad018c996
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1528




namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstNormalization
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalQuadraticSieve CenteredMomentCommonSupport CenteredMomentFourier
open CenteredMomentSupportedCorrelation CenteredMomentFirstReduced CenteredMomentFirstActiveFourier
open CenteredMomentGaussEnergy CenteredMomentPrimitive CenteredMomentFirstPoisson
local notation "O" => ActualEisensteinCubic.O

theorem residueGauss_eq_norm_mul_gaussRow (a : O) (ha : Supported (Ideal.span {a})) (h : O) :
    residueGauss a (supported_element_ne_zero a ha) (supportedModulusCharacter a ha) (Ideal.Quotient.mk _ h)=
      (‖eisEmbedding a‖:ℂ)*gaussRow a ha h := by
  have hn : (‖eisEmbedding a‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero a ha)))
  rw [gaussRow,residueGauss_supported_mk,sqrt_absNorm]
  field_simp

theorem normalized_active_coefficient {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
    (h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    tripleFourier a b r (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
      (finitePrimeModulus_ne_zero P) (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G h /
      (‖eisEmbedding (a*(b*r))‖^2:ℝ) =
      (canonicalNormalizedGauss P hcop hg j /
        ((‖eisEmbedding a‖:ℂ)*(‖eisEmbedding b‖:ℂ)*(‖eisEmbedding r‖:ℂ)))*
      (CanonicalRowCompletion.idealRowHom (b*r) (Ideal.span {a})*
        star (CanonicalRowCompletion.idealRowHom (a*r) (Ideal.span {b}))*finiteSexticRow P hg j (a*b))*
      (star (finiteSexticRow P hg j h)*gaussRow a ha h*star (gaussRow b hb (-h))) := by
  dsimp only
  let := finite_quotient_span (supported_element_ne_zero b hb)
  have hna : (‖eisEmbedding a‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero a ha)))
  have hnb : (‖eisEmbedding b‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero b hb)))
  have hnr : (‖eisEmbedding (finitePrimeModulus P)‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P)))
  rw [tripleFourier_active P hcop hg hchar j hj0 hj6 a b
    (supported_element_ne_zero a ha) (supported_element_ne_zero b hb) har hbr,
    residueGauss_inverse,← map_neg,residueGauss_eq_norm_mul_gaussRow a ha,
    residueGauss_eq_norm_mul_gaussRow b hb,← MulChar.star_apply',
    supportedModulusCharacter_mk,supportedModulusCharacter_mk]
  simp only [canonicalNormalizedGauss,map_mul,norm_mul,star_mul,Complex.star_def,
    Complex.conj_ofReal,Complex.ofReal_pow,Complex.ofReal_mul]
  field_simp

end SevenEighths.CenteredMomentFirstNormalization

end

end OAI
end OAIOriginalModule1528

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstColumns
Source SHA256: 8e25712197c1f47a50dd27f639795fa0553ff4d263592ebab9c2031d2e9583a6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1529




namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstColumns
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentFixedRay RayFourExpansion CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

def leftCoefficient (e r : O) (ρ : O → ℂ) (a : O) : ℂ :=
  idealRowHom (e*r) (Ideal.span {a})*ρ a

def rightCoefficient (e r : O) (ρ : O → ℂ) (b : O) : ℂ :=
  idealRowHom (e*r) (Ideal.span {b})*star (ρ b)

theorem first_phase_columns (e r a b : O) (ρ : O → ℂ)
    (hρ : ∀ x y,ρ (x*y)=ρ x*ρ y)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpa : ConcretePrimeRowBridge.goodLambda^2∣a-1)
    (hpb : ConcretePrimeRowBridge.goodLambda^2∣b-1) (hab : IsCoprime a b) :
    (idealRowHom e (Ideal.span {a})*star (idealRowHom e (Ideal.span {b}))*ρ e)*
      (idealRowHom (b*r) (Ideal.span {a})*star (idealRowHom (a*r) (Ideal.span {b}))*ρ (a*b)) =
      ρ e*sexticReciprocityPhase a b*leftCoefficient e r ρ a*star (rightCoefficient e r ρ b) := by
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero a ha)
  let : Fintype (CenteredMomentCommonSupport.Residue a) := Fintype.ofFinite _
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero b hb)
  let : Fintype (CenteredMomentCommonSupport.Residue b) := Fintype.ofFinite _
  have hp := supported_opposite_phase b a hb ha hpb hpa hab.symm
  rw [sexticReciprocityPhase_symm b a] at hp
  calc
    _ = ρ e*(idealRowHom b (Ideal.span {a})*star (idealRowHom a (Ideal.span {b})))*
        leftCoefficient e r ρ a*star (rightCoefficient e r ρ b) := by
      simp only [leftCoefficient,rightCoefficient,idealRowHom_argument_mul,hρ,star_mul,star_star]
      ring
    _ = _ := by rw [hp]

def firstPhaseTable (r s : RayRing) : ℂ :=
  (QuadraticAllOddCRT.quadraticRaySign (QuadraticGaussRay.residueQuotientFour r)
    (QuadraticGaussRay.residueQuotientFour s):ℂ)

theorem firstPhaseTable_mk (a b : O) :
    firstPhaseTable (Ideal.Quotient.mk _ a) (Ideal.Quotient.mk _ b)=sexticReciprocityPhase a b := by
  simp only [firstPhaseTable,QuadraticGaussRay.residueQuotientFour_mk,sexticReciprocityPhase]

theorem firstPhaseTable_expansion (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) :
    sexticReciprocityPhase a b=∑ χ : RayCharacter,∑ ξ : RayCharacter,
      pairCoeff firstPhaseTable χ ξ*rayCharacter χ a*rayCharacter ξ b := by
  have hh := pair_phase_expansion firstPhaseTable a b
  simpa only [supported_rayMask a ha,supported_rayMask b hb,one_mul,firstPhaseTable_mk] using hh

theorem firstPhaseTable_mass :
    (∑ χ : RayCharacter,∑ ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖)≤256 := by
  have hb : ∀ u v : RayRingˣ,‖firstPhaseTable u v‖≤1 := by
    intro u v
    unfold firstPhaseTable QuadraticAllOddCRT.quadraticRaySign
    split_ifs <;> norm_num
  simpa only [mul_one] using pairCoeff_sum_norm_le firstPhaseTable 1 hb

def firstExtension (e r : O) (ρ : O → ℂ) (a b : O) : ℂ :=
  ρ e*sexticReciprocityPhase a b*leftCoefficient e r ρ a*star (rightCoefficient e r ρ b)

theorem firstExtension_separated (e r a b : O) (ρ : O → ℂ)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) :
    firstExtension e r ρ a b=ρ e*∑ χ : RayCharacter,∑ ξ : RayCharacter,
      pairCoeff firstPhaseTable χ ξ*(leftCoefficient e r ρ a*rayCharacter χ a)*
        star (rightCoefficient e r ρ b*rayCharacter (ξ⁻¹) b) := by
  unfold firstExtension
  rw [firstPhaseTable_expansion a b ha hb]
  simp only [Finset.mul_sum,Finset.sum_mul,star_mul,CenteredMomentChildAssembly.rayCharacter_inverse_star]
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro ξ hξ
  ring

end SevenEighths.CenteredMomentFirstColumns

end

end OAI
end OAIOriginalModule1529

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstAssembly
Source SHA256: d31ed848fbcaa68c97fb10ec5d99ade40a4a47ebf08b6e4895cb3e5437ccae8b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1530


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstAssembly
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentFirstColumns CenteredMomentMobiusRegroup CenteredMomentChildAssembly
open CenteredMomentGaussEnergy RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

def originalPhase (e r : O) (ρ : O → ℂ) (a b : O) : ℂ :=
  (idealRowHom e (Ideal.span {a})*star (idealRowHom e (Ideal.span {b}))*ρ e)*
    (idealRowHom (b*r) (Ideal.span {a})*star (idealRowHom (a*r) (Ideal.span {b}))*ρ (a*b))

theorem originalPhase_eq (e r a b : O) (ρ : O → ℂ)
    (hρ : ∀ x y,ρ (x*y)=ρ x*ρ y)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpa : ConcretePrimeRowBridge.goodLambda^2∣a-1)
    (hpb : ConcretePrimeRowBridge.goodLambda^2∣b-1) (hab : IsCoprime a b) :
    originalPhase e r ρ a b=firstExtension e r ρ a b :=
  first_phase_columns e r a b ρ hρ ha hb hpa hpb hab

theorem first_divisor_pair {α β : Type*} (L : Ideal O)
    (a : α → O) (b : β → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (hb : ∀ j,Supported (Ideal.span {b j}))
    (c : α → ℂ) (d : β → ℂ) (e r : O) (ρ : O → ℂ) (h : O)
    (i : α) (j : β) (K : ℂ) :
    (if L∣Ideal.span {a i} ∧ L∣Ideal.span {b j} then
      firstExtension e r ρ (a i) (b j)*(c i*star (d j))*
        (gaussRow (a i) (ha i) h*star (gaussRow (b j) (hb j) (-h)))*K else 0) =
    ρ e*∑ χ : RayCharacter,∑ ξ : RayCharacter,
      pairCoeff firstPhaseTable χ ξ*
        ((divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*gaussRow (a i) (ha i) h)*
          star (divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) (ξ⁻¹) j*
            gaussRow (b j) (hb j) (-h)))*K := by
  by_cases hi : L∣Ideal.span {a i}
  · by_cases hj : L∣Ideal.span {b j}
    · simp only [hi,hj,and_self,ite_true,divisorCoefficient,star_mul,rayCharacter_inverse_star]
      rw [firstExtension_separated e r (a i) (b j) ρ (ha i) (hb j)]
      simp only [Finset.mul_sum,Finset.sum_mul,star_mul,rayCharacter_inverse_star]
      apply Finset.sum_congr rfl
      intro χ hχ
      apply Finset.sum_congr rfl
      intro ξ hξ
      ring
    · simp only [hi,hj,and_false,ite_false,divisorCoefficient,ite_true,zero_mul,star_zero,
        mul_zero,Finset.sum_const_zero]
  · simp only [hi,false_and,ite_false,divisorCoefficient,zero_mul,mul_zero,Finset.sum_const_zero]

theorem finite_first_children {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → O) (b : β → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (hb : ∀ j,Supported (Ideal.span {b j}))
    (hpa : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣a i-1)
    (hpb : ∀ j,ConcretePrimeRowBridge.goodLambda^2∣b j-1)
    (c : α → ℂ) (d : β → ℂ) (e r : O) (ρ : O → ℂ)
    (hρ : ∀ x y,ρ (x*y)=ρ x*ρ y) (h : O) (K : α → β → ℂ) :
    (∑ i∈S,∑ j∈T,(if IsCoprime (a i) (b j) then originalPhase e r ρ (a i) (b j) else 0)*
      (c i*star (d j))*(gaussRow (a i) (ha i) h*star (gaussRow (b j) (hb j) (-h)))*K i j) =
    ∑ L∈divisorPool T (fun j => Ideal.span {b j}),
      (UniqueFactorizationMonoid.moebius L:ℂ)*ρ e*
        ∑ χ : RayCharacter,∑ ξ : RayCharacter,
          pairCoeff firstPhaseTable χ ξ*∑ i∈S,∑ j∈T,
            ((divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*gaussRow (a i) (ha i) h)*
              star (divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) (ξ⁻¹) j*
                gaussRow (b j) (hb j) (-h)))*K i j := by
  have ht (i : α) (j : β) :
      (if IsCoprime (a i) (b j) then originalPhase e r ρ (a i) (b j) else 0)*
        (c i*star (d j))*(gaussRow (a i) (ha i) h*star (gaussRow (b j) (hb j) (-h)))*K i j =
      if IsCoprime (Ideal.span {a i}) (Ideal.span {b j}) then
        firstExtension e r ρ (a i) (b j)*(c i*star (d j))*
          (gaussRow (a i) (ha i) h*star (gaussRow (b j) (hb j) (-h)))*K i j else 0 := by
    rw [Ideal.isCoprime_span_singleton_iff]
    by_cases hc : IsCoprime (a i) (b j)
    · simp only [hc,ite_true,originalPhase_eq e r (a i) (b j) ρ hρ (ha i) (hb j) (hpa i) (hpb j) hc]
    · simp only [hc,ite_false,zero_mul]
  simp_rw [ht]
  rw [finite_pair_mobius S T (fun i => Ideal.span {a i}) (fun j => Ideal.span {b j})
    (fun j _ => (hb j).1)]
  apply Finset.sum_congr rfl
  intro L hL
  simp_rw [first_divisor_pair L a b ha hb c d e r ρ h]
  simp_rw [← Finset.mul_sum (s:=T),← Finset.mul_sum (s:=S)]
  rw [pair_ray_fubini]
  ring

theorem separated_first_gaussPolynomials {α β : Type*} (S : Finset α) (T : Finset β)
    (L : Ideal O) (a : α → O) (b : β → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (hb : ∀ j,Supported (Ideal.span {b j}))
    (c : α → ℂ) (d : β → ℂ) (e r : O) (ρ : O → ℂ) (χ ξ : RayCharacter)
    (f : α → ℂ) (g : β → ℂ) (h : O) :
    (∑ i∈S,∑ j∈T,
      ((divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*gaussRow (a i) (ha i) h)*
        star (divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) (ξ⁻¹) j*
          gaussRow (b j) (hb j) (-h)))*(f i*star (g j))) =
      gaussPolynomial S a ha (fun i => divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*f i) h*
        star (gaussPolynomial T b hb
          (fun j => divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) (ξ⁻¹) j*g j) (-h)) := by
  simp only [gaussPolynomial,star_sum,star_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end SevenEighths.CenteredMomentFirstAssembly

end

end OAI
end OAIOriginalModule1530

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstFamily
Source SHA256: 33543fe5566733ddeab2be8ac0db95a6b9ff6ec2144a215499b7345d673fbb1b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1531



namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentFirstFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentPrimaryCharacter CenteredMomentSupportedCorrelation
open CenteredMomentFixedRay CenteredMomentCommonSupport RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem exists_supported_row_presentation (η : Character) (m z : O)
    (hm : m≠0) (hz : Supported (Ideal.span {z})) (hmLam : λ₀∣m) (hm2 : (2:O)∣m) :
    ∃ τ : Character,
      τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {z} ∧
      ∀ n : O,elementCoeff τ n=rowTwist (elementHom η) m 1 z n := by
  let r := CompletedGauss.primaryGenerator (Ideal.span {z})
  have hr0 : r≠0 := supported_primaryGenerator_ne_zero _ hz
  have hs := CompletedGauss.primaryGenerator_spec (Ideal.span {z}) hr0
  have hr : Supported (Ideal.span {r}) := hs.1 ▸ hz
  obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs.1
  have hx : (1:O)^4*z=(u:O)*λ₀^0*(2:O)^0*r := by
    simpa only [one_pow,pow_zero,mul_one,mul_comm] using hu.symm
  let M := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {r}
  have hM : M≠⊥ := mul_ne_zero
    (mul_ne_zero (mul_ne_zero η.modulus_ne_bot (Ideal.span_singleton_eq_bot.not.mpr hm))
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))) (Ideal.span_singleton_eq_bot.not.mpr hr0)
  have hG := rowTwist_periodic η m 1 z hmLam hm2 u 0 0 r hr hs.2 hx
  refine ⟨rowCharacter M hM (rowTwist (elementHom η) m 1 z) hG (rowTwist_unit η m 1 z),?_,?_⟩
  · change M=_
    dsimp only [M]
    rw [hs.1]
  · intro n
    rw [elementCoeff_rowCharacter]
    split_ifs with hn
    · rfl
    · exact Eq.symm (not_not.mp (fun h => hn (rowTwist_nonzero_unit η m 1 z n hmLam hm2 u 0 0 r hx h)))

theorem first_period_contains (η : Character) (m e r : O) :
    let M := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r}
    M≤Ideal.span {3*r} ∧ M≤Ideal.span {(12:O)} := by
  dsimp only
  constructor
  · calc
      _ ≤ Ideal.span {(72:O)}*Ideal.span {e*r} := by
        rw [mul_assoc]
        exact Ideal.mul_le_right
      _ = Ideal.span {(72:O)*(e*r)} := Ideal.span_singleton_mul_span_singleton _ _
      _ ≤ _ := Ideal.span_singleton_le_span_singleton.mpr ⟨24*e,by ring⟩
  · exact (Ideal.mul_le_left.trans Ideal.mul_le_right).trans
      (Ideal.span_singleton_le_span_singleton.mpr ⟨6,by norm_num⟩)

theorem exists_first_character (η : Character) (m e r : O)
    (hm : m≠0) (he : Supported (Ideal.span {e})) (hr : Supported (Ideal.span {r}))
    (hmLam : λ₀∣m) (hm2 : (2:O)∣m)
    (χ : MulChar (Residue r) ℂ) (ξ : RayCharacter) :
    ∃ τ : Character,
      τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r} ∧
      (∀ n : O,elementCoeff τ n=
        rowTwist (elementHom η) m 1 (e*r) n*maskedPrimaryHom r χ n*
          elementCoeff (primaryRayCharacter ξ) n) ∧
      ∀ n : O,Supported (Ideal.span {n}) → λ₀^2∣n-1 →
        elementCoeff τ n=elementCoeff η n*coprimalityMask m n*
          idealRowHom (e*r) (Ideal.span {n})*χ (Ideal.Quotient.mk _ n)*rayCharacter ξ n := by
  obtain ⟨τ₀,hM,hτ⟩ := exists_supported_row_presentation η m (e*r) hm (supported_mul_elements e r he hr) hmLam hm2
  let τ := (τ₀.product (primaryCharacter r (supported_element_ne_zero r hr) χ)).product (primaryRayCharacter ξ)
  have hp := first_period_contains η m e r
  refine ⟨τ,?_,?_,?_⟩
  · change (τ₀.modulus ⊓ (primaryCharacter r (supported_element_ne_zero r hr) χ).modulus) ⊓
      (primaryRayCharacter ξ).modulus=_
    rw [hM,primaryCharacter_modulus,primaryRayCharacter_modulus,inf_eq_left.mpr hp.1,inf_eq_left.mpr hp.2]
  · intro n
    rw [show τ=(τ₀.product (primaryCharacter r (supported_element_ne_zero r hr) χ)).product (primaryRayCharacter ξ) from rfl,
      elementCoeff_product,elementCoeff_product,hτ,primaryCharacter_all]
  · intro n hn hpn
    rw [show τ=(τ₀.product (primaryCharacter r (supported_element_ne_zero r hr) χ)).product (primaryRayCharacter ξ) from rfl,
      elementCoeff_product,elementCoeff_product,hτ,primaryCharacter_primary r _ χ n hpn,
      primaryRayCharacter_primary ξ n hn hpn,rowTwist_extract_sixth_mask _ m 1 (e*r) n hn]
    simp only [one_pow,one_mul]
    rfl

end SevenEighths.CenteredMomentFirstFamily

end

end OAI
end OAIOriginalModule1531

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstCanonicalFamily
Source SHA256: d0bd45d1726ac00314e26bc88bf5e157ec2a7d312e72429eef9421bf7175155e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1532




namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstCanonicalFamily
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalRowCompletion CanonicalQuadraticSieve HeckeFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstFamily
open CenteredMomentFirstColumns CenteredMomentPrimitive CenteredMomentCommonSupport RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem supported_of_dvd (A B : Ideal O) (hB : Supported B) (hd : A∣B) : Supported A := by
  obtain ⟨Q,hQ⟩ := hd
  rw [hQ] at hB
  exact ((supported_mul_iff A Q).mp hB).1

theorem activeConductor_supported (I J : Ideal O) (hI : Supported I) :
    Supported (Ideal.span {activeConductor I J}) :=
  supported_of_dvd _ _ (commonPart_supported I J hI) (activeConductor_span_dvd I J)

theorem subsetGenerator_span_dvd (I J : Ideal O) (E : Finset (CommonIndex I J)) :
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) E}∣commonPart I J := by
  rw [primeSubsetGenerator,span_idealGenerator]
  refine (Finset.prod_dvd_prod_of_subset E Finset.univ
    (fun P : CommonIndex I J => P.val) (Finset.subset_univ _)).trans ?_
  rw [commonPart_left_product]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  simpa only [pow_one] using pow_dvd_pow P.val (leftExponent_pos I J P)

theorem subsetGenerator_supported (I J : Ideal O) (hI : Supported I)
    (E : Finset (CommonIndex I J)) :
    Supported (Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) E}) :=
  supported_of_dvd _ _ (commonPart_supported I J hI) (subsetGenerator_span_dvd I J E)

def canonicalActiveCharacter (I J : Ideal O) (hI : Supported I) :
    MulChar (Residue (activeConductor I J)) ℂ :=
  primitiveCharacter (activePrime I J) (activeCoprime I J) (activeGood I J hI) (activeExponent I J)

@[simp] theorem canonicalActiveCharacter_mk (I J : Ideal O) (hI : Supported I) (n : O) :
    canonicalActiveCharacter I J hI (Ideal.Quotient.mk _ n)=
      finiteSexticRow (activePrime I J) (activeGood I J hI) (activeExponent I J) n :=
  primitiveCharacter_mk _ _ _ _ n

theorem exists_canonical_first_pair (η : Character) (m : O) (hm : m≠0)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (I J : Ideal O) (hI : Supported I) (E : Finset (CommonIndex I J))
    (ξ₁ ξ₂ : RayCharacter) :
    let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
    let r := activeConductor I J
    let ρ := finiteSexticRow (activePrime I J) (activeGood I J hI) (activeExponent I J)
    let M := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : Character,τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ n : O,Supported (Ideal.span {n}) → goodLambda^2∣n-1 →
        elementCoeff τ₁ n=elementCoeff η n*coprimalityMask m n*leftCoefficient e r ρ n*rayCharacter ξ₁ n) ∧
      (∀ n : O,Supported (Ideal.span {n}) → goodLambda^2∣n-1 →
        elementCoeff τ₂ n=elementCoeff η n*coprimalityMask m n*rightCoefficient e r ρ n*rayCharacter ξ₂ n) := by
  dsimp only
  obtain ⟨τ₁,hM₁,_,h₁⟩ := exists_first_character η m
    (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) (activeConductor I J) hm
    (subsetGenerator_supported I J hI E) (activeConductor_supported I J hI) hmLam hm2
    (canonicalActiveCharacter I J hI) ξ₁
  obtain ⟨τ₂,hM₂,_,h₂⟩ := exists_first_character η m
    (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) (activeConductor I J) hm
    (subsetGenerator_supported I J hI E) (activeConductor_supported I J hI) hmLam hm2
    (canonicalActiveCharacter I J hI)⁻¹ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,?_,?_⟩
  · intro n hn hp
    rw [h₁ n hn hp,canonicalActiveCharacter_mk,leftCoefficient]
    ring
  · intro n hn hp
    let : Finite (Residue (activeConductor I J)) := finite_quotient_span (finitePrimeModulus_ne_zero (activePrime I J))
    rw [h₂ n hn hp,← MulChar.star_apply',canonicalActiveCharacter_mk,rightCoefficient]
    ring

theorem first_displayed_norm (η : Character) (m : O) (I J : Ideal O)
    (E : Finset (CommonIndex I J)) :
    (η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) E*activeConductor I J}).absNorm =
    η.modulus.absNorm*(Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm*
      ((∏ P∈E,P.val).absNorm*(Ideal.span {activeConductor I J}).absNorm) := by
  rw [← Ideal.span_singleton_mul_span_singleton,primeSubsetGenerator,span_idealGenerator]
  simp only [map_mul]

end SevenEighths.CenteredMomentFirstCanonicalFamily

end

end OAI
end OAIOriginalModule1532

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstFrequency
Source SHA256: 7a1cc679057f390ecb7da73f6ac71521c0ed474bd8ce42600034f1f96de53d19
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1533


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstFrequency
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentFirstNormalization CenteredMomentFirstReduced CenteredMomentFirstAssembly
open CenteredMomentFirstColumns CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
open CenteredMomentPrimitive CenteredMomentGaussEnergy CenteredMomentChildAssembly CenteredMomentMobiusRegroup
open RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem normalized_dilated_frequency {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (e a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
    (k : ℝ) (h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    let ρ := finiteSexticRow P hg j
    tripleRow a b r (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G e*
      ((k/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*
      tripleFourier a b r (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
        (finitePrimeModulus_ne_zero P) (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G h =
      ((k:ℂ)*canonicalNormalizedGauss P hcop hg j/(‖eisEmbedding r‖:ℂ))*star (ρ h)*
        originalPhase e r ρ a b*
        ((gaussRow a ha h/(‖eisEmbedding a‖:ℂ))*star (gaussRow b hb (-h)/(‖eisEmbedding b‖:ℂ))) := by
  dsimp only
  let := finite_quotient_span (supported_element_ne_zero b hb)
  have he := normalized_active_coefficient P hcop hg hchar j hj0 hj6 a b ha hb har hbr h
  dsimp only at he
  rw [Complex.ofReal_div]
  calc
    _ = (k:ℂ)*tripleRow a b (finitePrimeModulus P) (supportedModulusCharacter a ha)
        (supportedModulusCharacter b hb)⁻¹
        (principalSexticRow P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P)) e*
        (tripleFourier a b (finitePrimeModulus P) (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
          (finitePrimeModulus_ne_zero P) (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹
          (principalSexticRow P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P)) h /
          (‖eisEmbedding (a*(b*finitePrimeModulus P))‖^2:ℝ)) := by ring
    _ = _ := by
      rw [he,tripleRow,← MulChar.star_apply',supportedModulusCharacter_mk,
        supportedModulusCharacter_mk,
        principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P) e]
      simp only [originalPhase,Complex.star_def,map_div₀,Complex.conj_ofReal]
      ring

def dilatedFrequency {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i) (j : ι → ℕ)
    (e a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (k : ℝ) (h : O) : ℂ :=
  let r := finitePrimeModulus P
  let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
  tripleRow a b r (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G e*
    ((k/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*
    tripleFourier a b r (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
      (finitePrimeModulus_ne_zero P) (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G h

theorem finite_dilated_children {ι α β : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (S : Finset α) (T : Finset β) (a : α → O) (b : β → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (hb : ∀ l,Supported (Ideal.span {b l}))
    (hpa : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣a i-1)
    (hpb : ∀ l,ConcretePrimeRowBridge.goodLambda^2∣b l-1)
    (har : ∀ i,IsCoprime (a i) (finitePrimeModulus P))
    (hbr : ∀ l,IsCoprime (b l) (finitePrimeModulus P))
    (c : α → ℂ) (d : β → ℂ) (e : O) (k : ℝ) (h : O) (K : α → β → ℂ) :
    let r := finitePrimeModulus P
    let ρ := finiteSexticRow P hg j
    (∑ i∈S,∑ l∈T,
      (if IsCoprime (a i) (b l) then dilatedFrequency P hcop hg j e (a i) (b l) (ha i) (hb l) k h else 0)*
        (c i*star (d l))*K i l) =
      ((k:ℂ)*canonicalNormalizedGauss P hcop hg j/(‖eisEmbedding r‖:ℂ))*star (ρ h)*
        ∑ L∈divisorPool T (fun l => Ideal.span {b l}),
          (UniqueFactorizationMonoid.moebius L:ℂ)*ρ e*
            ∑ χ : RayCharacter,∑ ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*
              ∑ i∈S,∑ l∈T,
                ((divisorCoefficient L a (fun i => (c i/(‖eisEmbedding (a i)‖:ℂ))*leftCoefficient e r ρ (a i)) χ i*
                    gaussRow (a i) (ha i) h)*
                  star (divisorCoefficient L b (fun l => (d l/(‖eisEmbedding (b l)‖:ℂ))*rightCoefficient e r ρ (b l)) (ξ⁻¹) l*
                    gaussRow (b l) (hb l) (-h)))*K i l := by
  dsimp only
  let r := finitePrimeModulus P
  let ρ := finiteSexticRow P hg j
  let F := ((k:ℂ)*canonicalNormalizedGauss P hcop hg j/(‖eisEmbedding r‖:ℂ))*star (ρ h)
  have ht (i : α) (l : β) :
      (if IsCoprime (a i) (b l) then dilatedFrequency P hcop hg j e (a i) (b l) (ha i) (hb l) k h else 0)*
          (c i*star (d l))*K i l =
        F*((if IsCoprime (a i) (b l) then originalPhase e r ρ (a i) (b l) else 0)*
          ((c i/(‖eisEmbedding (a i)‖:ℂ))*star (d l/(‖eisEmbedding (b l)‖:ℂ)))*
