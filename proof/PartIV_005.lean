    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0< C ∧ ∀(η : Character) (Z : ℝ),1≤ Z → ∀R : ℕ→Finset FreeRow,
      (∀n u,u∈R n → u.val≠1 ∧ Z^((RHIVProbe.h:ℝ)+ζ)*(2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(Z^((RHIVProbe.h:ℝ)+ζ)*(2:ℝ)^n)) →
      ∀(T : Fin K→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=(RHIVProbe.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      Summable (fun n=> finitePhysicalRows S hmax η (R n) T W (fun i=> Z^(length i)) W0 W1
        (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z) ∧
      (∑'n,‖finitePhysicalRows S hmax η (R n) T W (fun i=> Z^(length i)) W0 W1
        (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z‖)
      ≤ C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  obtain ⟨r,C,hr,hC,hmain⟩ := iv_large_physical_tail_arbitrary_saving K δ a b B ζ saving hδ hδ' hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  let N : ℝ := ‖((1/(2*Real.pi):ℝ):ℂ)^3‖
  have hN : 0≤ N := norm_nonneg _
  refine ⟨(1+N)*C,by positivity,?_⟩
  intro η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  obtain ⟨hgs,hgb⟩ := hmain η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  let f : ℕ→ℂ := fun n=> finitePhysicalRows S hmax η (R n) T W (fun i=> Z^(length i)) W0 W1
    (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z
  let g : ℕ→ℝ := fun n=> absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=> Z^(length i)) W0 W1
    (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z 2 2 r
  have hbnd (n : ℕ) : ‖f n‖≤ N*g n := norm_finitePhysicalRows_le_absolute
    (1/2000) 2 2 r (by norm_num) (by norm_num) (by norm_num)
    (by linarith [HeckeZeroSupremum.beta_le_one]) (by norm_num) (by norm_num) (by norm_num) hr
    S hS hmax hfirst η (R n) (fun u hu=>(hR n u hu).1) T hT hdis W _ W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 _ _ Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
  have hns : Summable (fun n=>‖f n‖) := Summable.of_nonneg_of_le (fun n=> norm_nonneg _) hbnd (hgs.mul_left N)
  refine ⟨hns.of_norm,?_⟩
  calc
    (∑'n,‖f n‖) ≤ ∑'n,N*g n := hns.tsum_le_tsum hbnd (hgs.mul_left N)
    _ = N*(∑'n,g n) := tsum_mul_left
    _ ≤ N*(C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving)) := mul_le_mul_of_nonneg_left hgb hN
    _ ≤ (1+N)*(C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving)) :=
      mul_le_mul_of_nonneg_right (by linarith : N≤1+N) (by positivity)
    _ = _ := by ring

end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2TransportSmallTail
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem iv_small_physical_dyads_sum (K : ℕ) (e δ a b B : ℝ)
    (he : 0< e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0< a) (hb : 0< b) (hB : 0≤ B) (hβ : (RHIVProbe.boundary:ℝ)≤ HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0< C ∧ ∀(η : Character) (Z : ℝ),1≤ Z → ∀F : Finset ℕ,
      (∀n∈F,(2:ℝ)^n≤ Z^(1/100:ℝ)) → ∀R : ℕ→Finset FreeRow,
      (∀n∈F,∀u∈R n,u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n) →
      ∀(T : Fin K→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=(RHIVProbe.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      (∑n∈F,absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=> Z^(length i)) W0 W1
        (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z (HeckeZeroSupremum.beta+8*e+RHIVProbe.canonicalOffset) (1/2) (17/50))
      ≤ C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-RHIVProbe.smallSaving+8*e) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_dyad_integral K e δ a b (17/50) B
    (HeckeZeroSupremum.beta+8*e+RHIVProbe.canonicalOffset) (1/2) he he' hδ (by linarith) ha hb le_rfl hB
    (by linarith) (by linarith) le_rfl S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨D,hD,hsmall⟩ := small_dyadic_square_sum
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hYp (i : Fin K) : 1≤ Z^(length i) := Real.one_le_rpow hZ (hl0 i)
  let A : ℝ := C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-RHIVProbe.sourceSaving+8*e)
  have hA : 0≤ A := by dsimp [A];positivity
  have hbnd (n : ℕ) (hn : n∈F) :
      absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=> Z^(length i)) W0 W1
        (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z (HeckeZeroSupremum.beta+8*e+RHIVProbe.canonicalOffset) (1/2) (17/50)
      ≤ A*((2:ℝ)^n)^(2:ℝ) := by
    have hUn : 1≤(2:ℝ)^n := one_le_pow₀ (by norm_num)
    have hh := (hmain η ((2:ℝ)^n) hUn (R n) (hR n hn) T hT hdis (fun i=> Z^(length i)) hYp
      W hWS hWB (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z
      (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0).2
    have hpow : ((2:ℝ)^n)^(8/5+δ-(17/50:ℝ))≤((2:ℝ)^n)^(2:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hUn (by linarith)
    have hscale := iv_small_source_scale Z hZ0 length hl HeckeZeroSupremum.beta e
    calc
      _ ≤ (C*(η.modulus.absNorm:ℝ)^δ)*((2:ℝ)^n)^(8/5+δ-(17/50:ℝ))*
          Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-RHIVProbe.sourceSaving+8*e) := by
        apply hh.trans_eq
        rw [←hscale]
        ring
      _ ≤ (C*(η.modulus.absNorm:ℝ)^δ)*((2:ℝ)^n)^(2:ℝ)*
          Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-RHIVProbe.sourceSaving+8*e) := by gcongr
      _ = _ := by dsimp [A];ring
  calc
    _ ≤ ∑n∈F,A*((2:ℝ)^n)^(2:ℝ) := Finset.sum_le_sum hbnd
    _ = A*∑n∈F,((2:ℝ)^n)^(2:ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ A*(D*(Z^(1/100:ℝ))^(2:ℝ)) := mul_le_mul_of_nonneg_left
      (hsmall (Z^(1/100:ℝ)) (Real.rpow_pos_of_pos hZ0 _) F hF) hA
    _ = _ := by
      dsimp [A]
      rw [←Real.rpow_mul hZ0.le]
      have he : Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-RHIVProbe.sourceSaving+8*e)*Z^((1/100:ℝ)*2)=
          Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-RHIVProbe.smallSaving+8*e) := by
        rw [←Real.rpow_add hZ0]
        congr 1
        dsimp only [RHIVProbe.smallSaving]
        ring
      calc
        _ = (C*D)*(η.modulus.absNorm:ℝ)^δ*
            (Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-RHIVProbe.sourceSaving+8*e)*Z^((1/100:ℝ)*2)) := by ring
        _ = _ := by rw [he]

end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2TransportPhysicalSmallTail
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem iv_small_original_physical_tail (K : ℕ) (e δ a b B : ℝ)
    (he : 0< e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0< a) (hb : 0< b) (hB : 0≤ B) (hβ : (RHIVProbe.boundary:ℝ)≤ HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0< C ∧ ∀(η : Character) (Z : ℝ),1≤ Z → ∀F : Finset ℕ,
      (∀n∈F,(2:ℝ)^n≤ Z^(1/100:ℝ)) → ∀R : ℕ→Finset FreeRow,
      (∀n∈F,∀u∈R n,u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n) →
      ∀(T : Fin K→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=(RHIVProbe.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      (∑n∈F,‖finitePhysicalRows S hmax η (R n) T W (fun i=> Z^(length i)) W0 W1
        (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z‖)
      ≤ C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-RHIVProbe.smallSaving+8*e) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  obtain ⟨C,hC,hmain⟩ := iv_small_physical_dyads_sum K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  let N : ℝ := ‖((1/(2*Real.pi):ℝ):ℂ)^3‖
  have hN : 0≤ N := norm_nonneg _
  refine ⟨(1+N)*C,by positivity,?_⟩
  intro η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hmain' := hmain η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  let g : ℕ→ℝ := fun n=> absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=> Z^(length i)) W0 W1
    (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z (HeckeZeroSupremum.beta+8*e+RHIVProbe.canonicalOffset) (1/2) (17/50)
  have hbnd (n : ℕ) (hn : n∈F) :
      ‖finitePhysicalRows S hmax η (R n) T W (fun i=> Z^(length i)) W0 W1
        (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z‖≤ N*g n := norm_finitePhysicalRows_le_absolute
    e (HeckeZeroSupremum.beta+8*e+RHIVProbe.canonicalOffset) (1/2) (17/50) he he' (by linarith) (by linarith)
    (by linarith [HeckeZeroSupremum.beta_le_one]) le_rfl (by norm_num) le_rfl
    S hS hmax hfirst η (R n) (fun u hu=>(hR n hn u hu).1) T hT hdis W _ W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 _ _ Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
  calc
    _ ≤ ∑n∈F,N*g n := Finset.sum_le_sum hbnd
    _ = N*∑n∈F,g n := (Finset.mul_sum _ _ _).symm
    _ ≤ N*(C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-RHIVProbe.smallSaving+8*e)) :=
      mul_le_mul_of_nonneg_left hmain' hN
    _ ≤ (1+N)*(C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-RHIVProbe.smallSaving+8*e)) :=
      mul_le_mul_of_nonneg_right (by linarith : N≤1+N) (by positivity)
    _ = _ := by ring

end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2TransportCanonicalTails
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem iv_canonical_small_original_tail (K : ℕ) (e δ a b B : ℝ)
    (he : 0< e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0< a) (hb : 0< b) (hB : 0≤ B) (hβ : (RHIVProbe.boundary:ℝ)≤ HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0< C ∧ ∀(η : Character) (Z : ℝ),1≤ Z →
      ∀(T : Fin K→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=(RHIVProbe.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      ‖finitePhysicalRows S hmax η (rowBand 1 (Z^(1/100:ℝ))) T W (fun i=> Z^(length i)) W0 W1
        (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z‖
      ≤ C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-RHIVProbe.smallSaving+8*e) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  obtain ⟨C,hC,hmain⟩ := iv_small_original_physical_tail K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z hZ T hT hdis length hl0 hl W hWS hWB
  let L := Z^(1/100:ℝ)
  have hrows (n : ℕ) (hn : n∈smallDyadicIndices L) (u : FreeRow) (hu : u∈smallDyadicRows L n) :
      u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n := by
    have hh := mem_dyadicRows.mp (mem_smallDyadicRows.mp hu).1
    exact ⟨hh.1,by simpa only [one_mul,rowNorm] using hh.2.1,by simpa only [one_mul,rowNorm] using hh.2.2.le⟩
  have hbnd := hmain η Z hZ (smallDyadicIndices L) (fun n hn=> mem_smallDyadicIndices.mp hn)
    (smallDyadicRows L) hrows T hT hdis length hl0 hl W hWS hWB
  have heq := sum_small_dyadicRows L (physicalRowValue S hmax η T W (fun i=> Z^(length i)) W0 W1
    (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z)
  change finitePhysicalRows S hmax η (rowBand 1 L) T W (fun i=> Z^(length i)) W0 W1
    (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z=
    ∑n∈smallDyadicIndices L,finitePhysicalRows S hmax η (smallDyadicRows L n) T W (fun i=> Z^(length i)) W0 W1
      (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z at heq
  rw [heq]
  exact (norm_sum_le _ _).trans hbnd

theorem iv_canonical_large_original_tail (K : ℕ) (δ a b B ζ saving : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hζ : 0<ζ)
    (ha : 0< a) (hb : 0< b) (hB : 0≤ B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0< C ∧ ∀(η : Character) (Z : ℝ),1≤ Z →
      ∀(T : Fin K→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=(RHIVProbe.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      Summable (fun n=> finitePhysicalRows S hmax η (dyadicRows (Z^((RHIVProbe.h:ℝ)+ζ)) n) T W (fun i=> Z^(length i)) W0 W1
        (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z) ∧
      (∑'n,‖finitePhysicalRows S hmax η (dyadicRows (Z^((RHIVProbe.h:ℝ)+ζ)) n) T W (fun i=> Z^(length i)) W0 W1
        (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z‖)
      ≤ C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  obtain ⟨C,hC,hmain⟩ := iv_large_original_physical_tail K δ a b B ζ saving hδ hδ' hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z hZ T hT hdis length hl0 hl W hWS hWB
  apply hmain η Z hZ (dyadicRows (Z^((RHIVProbe.h:ℝ)+ζ))) _ T hT hdis length hl0 hl W hWS hWB
  intro n u hu
  have hh := mem_dyadicRows.mp hu
  exact ⟨hh.1,hh.2.1,hh.2.2.le⟩


end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2TransportCanonicalReduction
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
local notation "O" => HeckeFamily.O

theorem iv_canonical_probe_minus_central (K : ℕ) (e δ a b B ζ saving : ℝ)
    (he : 0< e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ)
    (ha : 0< a) (hb : 0< b) (hB : 0≤ B) (hβ : (RHIVProbe.boundary:ℝ)≤ HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0< C ∧ ∀(η : Character) (Z : ℝ),1≤ Z →
      ∀(T : Fin K→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=(RHIVProbe.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=> canonicalSlotSupport (T i)) W (fun i=> Z^(length i)) (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=> Z^(length i)) W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z-
        finitePhysicalRows S hmax η (rowBand (Z^(1/100:ℝ)) (Z^((RHIVProbe.h:ℝ)+ζ))) T W (fun i=> Z^(length i))
          W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z‖≤
        C*(η.modulus.absNorm:ℝ)^δ*(Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-RHIVProbe.smallSaving+8*e)+Z^(-saving)) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  obtain ⟨Cs,hCs,hs⟩ := iv_canonical_small_original_tail K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨Cl,hCl,hl⟩ := iv_canonical_large_original_tail K δ a b B ζ saving hδ (by linarith) hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨Cs+Cl,add_pos hCs hCl,?_⟩
  intro η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hdec := canonical_physical_probe_partition S hS hmax η T
    (fun i P hP=> outside_prime_supported S hS.bad P (hT i P hP)) W (fun i=> Z^(length i)) W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z
    (Z^(1/100:ℝ)) (Z^((RHIVProbe.h:ℝ)+ζ)) (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
    (Real.one_le_rpow hZ (by norm_num)) (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
  have hs' := hs η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hl' := hl η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hsmall : (∑n∈smallDyadicIndices (Z^(1/100:ℝ)),finitePhysicalRows S hmax η (smallDyadicRows (Z^(1/100:ℝ)) n)
      T W (fun i=> Z^(length i)) W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z)=
      finitePhysicalRows S hmax η (rowBand 1 (Z^(1/100:ℝ))) T W (fun i=> Z^(length i)) W0 W1
        (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z :=
    (sum_small_dyadicRows (Z^(1/100:ℝ)) (physicalRowValue S hmax η T W (fun i=> Z^(length i)) W0 W1
      (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z)).symm
  rw [hsmall] at hdec
  rw [hdec]
  have heq : principalPhysicalPool η S T W (fun i=> Z^(length i)) W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z=
      ∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Z^(length i)))*
        principalRowIntegral η S (fun i=> primaryGenerator (P i).val.val) W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z := rfl
  rw [←heq,add_sub_cancel_left]
  rw [show ∀a b c : ℂ,a+b+c-b=a+c from fun a b c=> by ring]
  apply (norm_add_le _ _).trans
  apply (add_le_add hs' ((norm_tsum_le_tsum_norm hl'.1.norm).trans hl'.2)).trans
  calc
    _ ≤ (Cs+Cl)*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-RHIVProbe.smallSaving+8*e)+
        (Cs+Cl)*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by gcongr <;> linarith
    _ = _ := by ring


end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2TransportCanonicalCubeReduction
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem iv_canonical_probe_minus_cube (K : ℕ) (e δ a b B ζ saving τ : ℝ)
    (he : 0< e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0< a) (hb : 0< b) (hB : 0≤ B) (hβ : (RHIVProbe.boundary:ℝ)≤ HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0< C ∧ ∀(η : Character) (Z : ℝ),1≤ Z →
      ∀(T : Fin K→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=(RHIVProbe.ell:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤ b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      ∀(alpha base H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((RHIVProbe.h:ℝ)+ζ)),
        (51/100:ℝ)≤ alpha u ∧ alpha u≤1 ∧ 2< base u ∧ Z^τ≤ H u ∧ H u≤(3*idx u+2:ℕ)*base u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*base u)< alpha u+2*e) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=> canonicalSlotSupport (T i)) W (fun i=> Z^(length i)) (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=> Z^(length i)) W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((RHIVProbe.h:ℝ)+ζ))) T hT W (fun i=> Z^(length i))
          W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z e alpha H‖≤
        C*(η.modulus.absNorm:ℝ)^2*(Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-RHIVProbe.smallSaving+8*e)+Z^(-saving)) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  obtain ⟨C0,hC0,h0⟩ := iv_canonical_probe_minus_central K e δ a b B ζ saving he he' hδ hδ' hζ ha hb hB hβ
    S hS hmax (hfirst.mono_parameter (by linarith)) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨C1,hC1,h1⟩ := iv_finite_cube_arbitrary_saving (ι:=ι) K τ saving b ζ B hτ hb hζ' hB e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C0+C1,add_pos_of_pos_of_nonneg hC0 hC1,?_⟩
  intro η Z hZ T hT hdis length hl0 hl hpool W hWS hWB alpha base H idx ψ hbin
  have h0' := h0 η Z hZ T hT hdis length hl0 hl W hWS hWB
  let R := rowBand (Z^(1/100:ℝ)) (Z^((RHIVProbe.h:ℝ)+ζ))
  have hR (u : FreeRow) (hu : u∈R) : u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z^((RHIVProbe.h:ℝ)+ζ) :=
    ⟨(mem_rowBand.mp hu).1,(mem_rowBand.mp hu).2.2.le⟩
  have h1' := h1 η Z hZ R hR T hT hdis length hl hpool W hWB alpha base H idx ψ hbin
  have hQ := HeckeLogarithmicInput.modulus_norm_ge_one η
  have hQδ : (η.modulus.absNorm:ℝ)^δ≤(η.modulus.absNorm:ℝ)^2 := by
    rw [←Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
  let E := Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-RHIVProbe.smallSaving+8*e)+Z^(-saving)
  have hE : 0≤ E := by dsimp [E];positivity
  have hsave : Z^(-saving)≤ E := by dsimp [E];have : 0≤ Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-RHIVProbe.smallSaving+8*e) := Real.rpow_nonneg (by linarith) _;linarith
  have h0'' : ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=> canonicalSlotSupport (T i)) W (fun i=> Z^(length i)) (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=> Z^(length i)) W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z-
        finitePhysicalRows S hmax η R T W (fun i=> Z^(length i)) W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z‖≤
      C0*(η.modulus.absNorm:ℝ)^2*E :=
    h0'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQδ hC0.le) hE)
  have h1'' := h1'.trans (mul_le_mul_of_nonneg_left hsave (mul_nonneg hC1 (sq_nonneg (η.modulus.absNorm:ℝ))))
  apply (norm_sub_le_norm_sub_add_norm_sub _
    (finitePhysicalRows S hmax η R T W (fun i=> Z^(length i)) W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z) _).trans
  exact (add_le_add h0'' h1'').trans_eq (by dsimp [E];ring)


end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2TransportCanonicalCubeChoice
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem iv_canonical_probe_exists_cube (K : ℕ) (e δ a b B ζ saving τ : ℝ)
    (he : 0< e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0< a) (hb : 0< b) (hB : 0≤ B) (hβ : (RHIVProbe.boundary:ℝ)≤ HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0< C ∧ ∃n : ℕ,0< n ∧ ∀(η : Character) (Z : ℝ),1≤ Z → 2< Z^τ →
      ∀(T : Fin K→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=(RHIVProbe.ell:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤ b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      ∀ψ : FreeRow→ι→Character,∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤ a ∧ a≤1 ∧
        a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*idx u*Z^τ)< a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*Z^τ)< a+2*e ∧
        (51/100< a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (ψ u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (ψ u) j).residue=1 ∧ s=1) ∧
          a≤ s.re ∧ s.re< a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let H : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=> canonicalSlotSupport (T i)) W (fun i=> Z^(length i)) (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=> Z^(length i)) W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((RHIVProbe.h:ℝ)+ζ))) T hT W (fun i=> Z^(length i))
          W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z e alpha H‖≤
        C*(η.modulus.absNorm:ℝ)^2*(Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-RHIVProbe.smallSaving+8*e)+Z^(-saving)) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  obtain ⟨C,hC,hbound⟩ := iv_canonical_probe_minus_cube (ι:=ι) K e δ a b B ζ saving τ
    he he' hδ hδ' hζ hζ' hτ ha hb hB hβ S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨n,hn,hwidth⟩ := exists_source_cube_bin_number e he
  refine ⟨C,hC,n,hn,?_⟩
  intro η Z hZ hZT T hT hdis length hl0 hl hpool W hWS hWB ψ
  obtain ⟨idx,grid,hbins⟩ := exists_source_cube_bins e (Z^τ) he hZT n hn hwidth S hS.prime η ψ
  refine ⟨idx,grid,?_,?_,?_⟩
  · intro u
    exact ⟨(hbins u).1,(hbins u).2.1,(hbins u).2.2.1,(hbins u).2.2.2.2.2.2.1⟩
  · intro u
    rcases hbins u with ⟨hi,hin,hgrid,ha0,ha1,hBH,hbuffer,hlo,hhi,hnext,hzero⟩
    exact ⟨ha0,ha1,hlo,hhi,hnext,hzero⟩
  · apply hbound η Z hZ T hT hdis length hl0 hl hpool W hWS hWB
      (fun u=>51/100+e*grid u) (fun _=> Z^τ) (fun u=>(3*idx u+1:ℕ)*Z^τ) idx ψ
    intro u hu
    rcases hbins u with ⟨hi,hin,hgrid,ha0,ha1,hBH,hbuffer,hlo,hhi,hnext,hzero⟩
    refine ⟨ha0,ha1,hZT,hBH,?_,hnext⟩
    have : 0≤ Z^τ := Real.rpow_nonneg (by linarith) _
    linarith


end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2TransportCanonicalRayCube
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

-- Reuse the unchanged upstream rayCubeFamily; only geometry is generalized.

theorem iv_canonical_probe_exists_ray_cube (K : ℕ) (e δ a b B ζ saving τ : ℝ)
    (he : 0< e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0< a) (hb : 0< b) (hB : 0≤ B) (hβ : (RHIVProbe.boundary:ℝ)≤ HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0< C ∧ ∃n : ℕ,0< n ∧ ∀ᶠ Z : ℝ in atTop,∀η : Character,
      ∀(T : Fin K→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=(RHIVProbe.ell:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤ b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤ a ∧ a≤1 ∧
        a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ)< a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ)< a+2*e ∧
        (51/100< a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a≤ s.re ∧ s.re< a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((RHIVProbe.h:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let H : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=> canonicalSlotSupport (T i)) W (fun i=> Z^(length i)) (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=> Z^(length i)) W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((RHIVProbe.h:ℝ)+ζ))) T hT W (fun i=> Z^(length i))
          W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z e alpha H‖≤
        C*(η.modulus.absNorm:ℝ)^2*(Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-RHIVProbe.smallSaving+8*e)+Z^(-saving)) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  obtain ⟨C,hC,n,hn,hchoice⟩ := iv_canonical_probe_exists_cube (ι:=RayQuotient.Characters M H)
    K e δ a b B ζ saving τ he he' hδ hδ' hζ hζ' hτ ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,n,hn,?_⟩
  filter_upwards [source_cube_height_eventually τ hτ,
    ProbeRayCharacterFamily.large_supported_twists_eventually M (1/100) (by norm_num)]
    with Z hZ hlarge
  intro η T hT hdis length hl0 hl hpool W hWS hWB
  obtain ⟨idx,grid,hlabel,hbins,herror⟩ := hchoice η Z hZ.1 hZ.2 T hT hdis length hl0 hl hpool W hWS hWB
    (rayCubeFamily M H hH)
  refine ⟨idx,grid,hlabel,hbins,?_,herror⟩
  intro u hu hcal
  have hs := calibration_nonzero_supported S hmax hS.bad u.val hcal
  have hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1 :=
    hlarge u (mem_rowBand.mp hu).2.1 hs H hH
  refine ⟨hnp,?_,?_⟩
  · exact ProbeRayCharacterFamily.raw_twisted_conductor M H hH u
  · intro hnp'
    exact (ProbeRayCharacterFamily.source_nonprincipal_maximum_dominates S hS.prime η u
      (rayCubeFamily M H hH u) hnp' _).trans_lt (hbins u).2.2.2.2.1


end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2TransportNormalizedTransport
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

omit [NeZero M] in
private theorem iv_transportPoolOutside (S : Finset (Ideal O)) (K : ℕ) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

lemma iv_normalized_central_transport (A P C F N : ℂ) (a b v : ℝ)
    (ha : ‖A-P-C‖≤ a) (hb : ‖P/N-F‖≤ b) (hv : ‖N⁻¹‖≤ v) (ha0 : 0≤ a) :
    ‖A/N-F-C/N‖≤ a*v+b := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  calc
    _ = ‖(A-P-C)*N⁻¹+(P/N-F)‖ := by congr 1;simp only [div_eq_mul_inv];ring
    _ ≤ ‖(A-P-C)*N⁻¹‖+‖P/N-F‖ := norm_add_le _ _
    _ ≤ a*v+b := by rw [norm_mul];gcongr

theorem iv_actual_normalized_probe_transport (K : ℕ) (e δ a b B ζ saving τ ellMin nu : ℝ)
    (he : 0< e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0< a) (hab : a≤ b) (hB : 0≤ B) (hmin : 0< ellMin) (hnu : 0< nu)
    (hβ : (RHIVProbe.boundary:ℝ)≤ HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin≤ ell j) (hellinj : Function.Injective ell) (hellsum : ∑j,ell j=RHIVProbe.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b) (hWB : ∀j y,0≤ W j y ∧ W j y≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0< n ∧ ∀η : Character,∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,
      let Yp := fun j=> Z^(ell j)
      let T := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
      let hT := iv_transportPoolOutside M H S K a b Yp
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (RHIVProbe.ell) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤ a ∧ a≤1 ∧
        a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ)< a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ)< a+2*e ∧
        (51/100< a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a≤ s.re ∧ s.re< a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((RHIVProbe.h:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let height : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=> canonicalSlotSupport (T j)) WC Yp (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-((4+RHIVProbe.b)/6)) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((RHIVProbe.h:ℝ)+ζ))) T hT WC Yp
          W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z e alpha height/normer‖≤
        C*(Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-RHIVProbe.smallSaving+8*e+nu)+Z^(-saving+nu)+
          Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-1/3000+nu)+
          Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)+e-(RHIVProbe.boundary)*ellMin)) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨Ca,hCa,n,hn,hcanonical⟩ := iv_canonical_probe_exists_ray_cube M H hH K e δ a b B ζ saving τ
    he he' hδ hδ' hζ hζ' hτ ha (ha.trans_le hab) hB hβ S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨Cn,hCn,hnormalizer⟩ := RHZeroFreeExtension.AnalyticHigh.iv_actual_ray_normalizer_inverse M H hH S hS a b ha hab ell
    (fun j=> hmin.trans_le (hell j)) hellsum W hW hcompact hsupp (fun j y=>(hWB j y).1) hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  refine ⟨n,hn,?_⟩
  intro η
  have hbetal := HeckeZeroSupremum.beta_le_one
  obtain ⟨Cp,hCp,hprincipal⟩ := RHZeroFreeExtension.AnalyticHigh.iv_actual_ray_principal_comparison M H hH η S hS
    a b B ellMin ha hab hB hmin ell hell hellinj hellsum W hW hcompact hsupp hWB hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 e nu he he'.le hnu
    (by linarith) (by linarith)
  let D : ℝ := Ca*(η.modulus.absNorm:ℝ)^2*Cn
  have hD : 0≤ D := by dsimp [D];positivity
  refine ⟨D+Cp,by positivity,?_⟩
  filter_upwards [hcanonical,hnormalizer,hprincipal,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _ : Fin K=> a) (fun _=> b) ell (fun _=> ha) (fun _=> hab) hellinj,
    eventually_gt_atTop (0:ℝ)] with Z hcan hnorm hprincipal hdis hZ
  dsimp only at hnorm hprincipal ⊢
  let Yp : Fin K→ℝ := fun j=> Z^(ell j)
  let T : Fin K→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
  let hT := iv_transportPoolOutside M H S K a b Yp
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWS (j : Fin K) : Function.support (WC j)⊆Icc a b := by
    intro y hy
    apply Ioo_subset_Icc_self (hsupp j _)
    intro hh
    exact hy (by dsimp [WC];rw [hh];simp)
  have hWCB (j : Fin K) (y : ℝ) : ‖WC j y‖≤ B := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  have hpool (j : Fin K) (P : OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : P∈T j) : (P.val.absNorm:ℝ)≤ b*Z^(ell j) := by
    have hh := (pool_norm_bounds (RayQuotient.identityClass M H) S ha.le hab
      (Real.rpow_pos_of_pos hZ (ell j)) P hP).2
    simpa only [mul_comm] using hh
  obtain ⟨idx,grid,hlabels,hbins,hray,herror⟩ := hcan η T hT hdis ell (fun j=>(hmin.trans_le (hell j)).le)
    hellsum hpool WC hWS hWCB
  refine ⟨hnorm.1,idx,grid,hlabels,hbins,hray,?_⟩
  have hh := iv_normalized_central_transport _ _ _ _ _ _ _ _ herror hprincipal.2 hnorm.2 (by positivity)
  apply hh.trans
  have heq : (Ca*(η.modulus.absNorm:ℝ)^2*(Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-RHIVProbe.smallSaving+8*e)+Z^(-saving)))*(Cn*Z^nu)=
      D*(Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-RHIVProbe.smallSaving+8*e+nu)+Z^(-saving+nu)) := by
    rw [Real.rpow_add hZ (HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-RHIVProbe.smallSaving+8*e) nu,
      Real.rpow_add hZ (-saving) nu]
    dsimp [D]
    ring
  rw [heq]
  have h1 : D≤ D+Cp := by linarith
  have h2 : Cp≤ D+Cp := by linarith
  calc
    _ ≤ (D+Cp)*(Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-RHIVProbe.smallSaving+8*e+nu)+Z^(-saving+nu))+
      (D+Cp)*(Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-1/3000+nu)+Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)+e-(RHIVProbe.boundary)*ellMin)) := by
      gcongr
    _ = _ := by ring


end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2TransportNormalizedTransportSaving
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

omit [NeZero M] in
private theorem iv_transportSavingPoolOutside (S : Finset (Ideal O)) (K : ℕ) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

theorem iv_actual_normalized_probe_transport_saving (K : ℕ) (e δ a b B ζ saving τ ellMin nu : ℝ)
    (he : 0< e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0< a) (hab : a≤ b) (hB : 0≤ B) (hmin : 0< ellMin) (hnu : 0< nu)
    (hβ : (RHIVProbe.boundary:ℝ)≤ HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin≤ ell j) (hellinj : Function.Injective ell) (hellsum : ∑j,ell j=RHIVProbe.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b) (hWB : ∀j y,0≤ W j y ∧ W j y≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (sigma : ℝ) (hsigma : 0< sigma)
    (_hgeometric : sigma+8*e+nu≤ RHIVProbe.smallSaving) (hprincipal : sigma+nu≤1/3000)
    (hwindow : sigma+e≤(RHIVProbe.boundary)*ellMin) (hlarge : sigma+nu≤ saving+RHIVProbe.lowExponent) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0< n ∧ ∀η : Character,∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,
      let Yp := fun j=> Z^(ell j)
      let T := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
      let hT := iv_transportSavingPoolOutside M H S K a b Yp
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (RHIVProbe.ell) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤ a ∧ a≤1 ∧
        a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ)< a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ)< a+2*e ∧
        (51/100< a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a≤ s.re ∧ s.re< a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((RHIVProbe.h:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let height : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=> canonicalSlotSupport (T j)) WC Yp (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-((4+RHIVProbe.b)/6)) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((RHIVProbe.h:ℝ)+ζ))) T hT WC Yp
          W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z e alpha height/normer‖≤
        C*Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-sigma) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  have hMatching := RHIVProbe.lowExponent_signal
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨n,hn,hbound⟩ := iv_actual_normalized_probe_transport M H hH K e δ a b B ζ saving τ ellMin nu
    he he' hδ hδ' hζ hζ' hτ ha hab hB hmin hnu hβ S hS hmax hfirst ell hell hellinj hellsum
    W hW hcompact hsupp hWB hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
  refine ⟨n,hn,?_⟩
  intro η
  obtain ⟨C,hC,hb⟩ := hbound η
  refine ⟨4*C,by positivity,?_⟩
  filter_upwards [hb,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  dsimp only at hb ⊢
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,herror⟩ := hb
  refine ⟨hnorm,idx,grid,hlabels,hbins,hray,herror.trans ?_⟩
  have h1 : Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-RHIVProbe.smallSaving+8*e+nu)≤ Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h2 : Z^(-saving+nu)≤ Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h3 : Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-1/3000+nu)≤ Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h4 : Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)+e-(RHIVProbe.boundary)*ellMin)≤ Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  calc
    _ ≤ C*(4*Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-sigma)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC.le
    _ = _ := by ring


end

end RHZeroFreeExtension.AnalyticHigh

#print axioms RHZeroFreeExtension.AnalyticHigh.iv_actual_normalized_probe_transport_saving

-- Parametric high adaptation: V2CubeSlotExponent

namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open ProbeHighRowFamily HeckeDetectorPhysicalSelection

lemma iv_source_slot_length_sum {Slot : Type*} (slots : Finset Slot) (ell : Slot→ℝ)
    (d : ℝ) (hell : ∑j∈slots,ell j=RHIVProbe.ell) :
    (∑j∈slots,ell j/d)=RHIVProbe.ell/d := by
  rw [←Finset.sum_div,hell]

lemma iv_source_slot_weightedMean {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (d : ℝ) (hd : d≠0) (hell : ∑j∈slots,ell j=RHIVProbe.ell) :
    weightedMean slots (fun j=> ell j/d) g=((RHIVProbe.ell)⁻¹)*(∑j∈slots,ell j*g j) := by
  unfold weightedMean
  simp_rw [div_mul_eq_mul_div]
  rw [←Finset.sum_div,←Finset.sum_div,hell]
  have hL : RHIVProbe.ell≠0 := RHIVProbe.analytic_geometry.1.ne'
  field_simp

lemma iv_source_slot_product {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (Z d mesh : ℝ) (hZ : 0< Z) (hd : d≠0) (hell : ∑j∈slots,ell j=RHIVProbe.ell) :
    (∏j∈slots,(Z^(ell j))^(-(4/25:ℝ)+g j+mesh))=
      Z^(-((RHIVProbe.ell*(4/25)):ℝ)+(RHIVProbe.ell)*weightedMean slots (fun j=> ell j/d) g+
        (RHIVProbe.ell)*mesh) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ]
  congr 1
  rw [iv_source_slot_weightedMean slots ell g d hd hell]
  simp_rw [mul_add,Finset.sum_add_distrib]
  rw [←Finset.sum_mul,←Finset.sum_mul,hell]
  have hL : RHIVProbe.ell≠0 := RHIVProbe.analytic_geometry.1.ne'
  field_simp

end
end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2CubeFloorArithmetic
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

omit [NeZero M] in
private theorem iv_floorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem iv_actual_floor_cube_arithmetic (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤ A)
    (hellsum : ∑j,ell j=RHIVProbe.ell) :
    ∃C : ℝ,0< C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v : ℝ),0≤ v → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,Z^v≤ rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e) →
      let Y : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      ‖cubeArithmeticSum S hS hmax η rows T (iv_floorPoolOutside M H S N c b Y) W Y (51/100) e t‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(v*(67/100+12*e+eps*(N+8))+loss-(RHIVProbe.ell*(3/20))+(RHIVProbe.ell)*mesh) := by
  obtain ⟨C,hC,hbound⟩ := actual_fixed_cube_prime_bound M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB
  let α : ℝ := 1/100+12*e+eps*(N+8)
  let AA := ProbeSelectedPrimeSums.annularPower 1 2 (α-17/50)
  have hAA : 0≤ AA := ProbeSelectedPrimeSums.annularPower_nonneg 1 2 _ (by norm_num)
  refine ⟨256*C*(AA+1),by positivity,?_⟩
  intro η
  filter_upwards [hbound η,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd' v hv rows hrows hnorm i hi hbin
  dsimp only
  intro t ht
  have hZp : 0< Z := zero_lt_one.trans_le hZ
  have hd0 : 0< d := hdmin.trans_le hd
  let Y : Fin N→ℝ := fun j=> Z^(ell j)
  let T : Fin N→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let F : FreeRow→ℝ := fun u=>‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
    (fun j=> iv_floorPoolOutside M H S N c b Y j _ (P j).property) W Y
    (((51/100+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-51/100-6*e:ℝ):ℂ)+t.2*Complex.I) z‖
  let D : ℝ := C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^loss*Z^(-(RHIVProbe.ell*(3/20))+(RHIVProbe.ell)*mesh)
  have hD : 0≤ D := by dsimp [D];positivity
  have hF (u : FreeRow) (hu : u∈rows) : F u≤ D*rowNorm u^α := by
    rcases hrows u hu with ⟨hu1,hulo,hcal,huhi⟩
    have hh := hb d hd hd' u hu1 hulo hcal huhi (51/100) i hi le_rfl (by norm_num) (hbin u hu) t ht
    dsimp only at hh
    let g : Fin N→ℝ := fun j=> HeckePrimeAmplitudeBins.amplitude (Y j) ((51/100:ℝ)-1/2) mesh
      (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z)
    have hellpos (j : Fin N) : 0≤ ell j := by
      exact (mul_nonneg hdmax hrmin.le).trans (hello j)
    have hq := weightedMean_bounds Finset.univ (fun j=> ell j/d) g (1/50)
      (fun j _=> div_nonneg (hellpos j) hd0.le)
      (by rw [iv_source_slot_length_sum _ _ _ hellsum];exact div_pos RHIVProbe.analytic_geometry.1 hd0)
      (fun j _=>⟨(hh.1 j).1,by have hhj := (hh.1 j).2.1;dsimp [g,Y,z];norm_num at hhj ⊢;exact hhj⟩)
    have hp : (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh))≤ Z^(-(RHIVProbe.ell*(3/20))+(RHIVProbe.ell)*mesh) := by
      rw [show (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh))=
        Z^(-((RHIVProbe.ell*(4/25)):ℝ)+(RHIVProbe.ell)*weightedMean Finset.univ (fun j=> ell j/d) g+(RHIVProbe.ell)*mesh) from
        iv_source_slot_product Finset.univ ell g Z d mesh hZp hd0.ne' hellsum]
      apply Real.rpow_le_rpow_of_exponent_le hZ
      have hm := mul_le_mul_of_nonneg_left hq.2 RHIVProbe.analytic_geometry.1.le
      linarith only [hm]
    have hN : 0≤ rowNorm u := (rowNorm_ge_one u).trans' (by norm_num)
    have h := hh.2.trans (mul_le_mul_of_nonneg_left hp (by positivity))
    convert h using 1 ; dsimp [F,D,α,Y,z,g] ; norm_num ; ring
  have hh := dyadic_weighted_rows α (17/50) D (Z^v) hD (Real.one_le_rpow hZ hv) rows hnorm
    F hF z (by simp [z])
  have hsum : ‖cubeArithmeticSum S hS hmax η rows T (iv_floorPoolOutside M H S N c b Y) W Y (51/100) e t‖≤
      ∑u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u := by
    unfold cubeArithmeticSum
    exact (norm_sum_le _ _).trans_eq (by apply Finset.sum_congr rfl;intro u hu;rw [norm_mul])
  apply (hsum.trans hh).trans
  have hpow : Z^loss*Z^(-(RHIVProbe.ell*(3/20))+(RHIVProbe.ell)*mesh)*(Z^v)^(1+α-17/50)=
      Z^(v*(67/100+12*e+eps*(N+8))+loss-(RHIVProbe.ell*(3/20))+(RHIVProbe.ell)*mesh) := by
    rw [←Real.rpow_mul hZp.le,←Real.rpow_add hZp,←Real.rpow_add hZp]
    congr 1
    dsimp [α]
    ring
  calc
    _ ≤ 256*D*(AA+1)*(Z^v)^(1+α-17/50) := by change 256*D*AA*_≤_;gcongr;linarith
    _ = _ := by
      dsimp [D]
      calc
        _ = (256*C*(AA+1))*(η.modulus.absNorm:ℝ)^(2*eps)*(Z^loss*Z^(-(RHIVProbe.ell*(3/20))+(RHIVProbe.ell)*mesh)*(Z^v)^(1+α-17/50)) := by ring
        _ = _ := by rw [hpow]

end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2CubeFloorGlobal
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

omit [NeZero M] in
private theorem iv_globalFloorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem iv_actual_global_floor_cube_arithmetic (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤ A)
    (hellsum : ∑j,ell j=RHIVProbe.ell) :
    ∃C : ℝ,0< C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v : ℝ),0≤ v → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,rowNorm u≤ Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e) →
      let Y : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      ‖cubeArithmeticSum S hS hmax η rows T (iv_globalFloorPoolOutside M H S N c b Y) W Y (51/100) e t‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(v*(67/100+12*e+eps*(N+8))+loss-(RHIVProbe.ell*(3/20))+(RHIVProbe.ell)*mesh) := by
  obtain ⟨C,hC,hbound⟩ := iv_actual_floor_cube_arithmetic M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
  let θ : ℝ := 67/100+12*e+eps*(N+8)
  have hθ : 0<θ := by dsimp [θ];positivity
  obtain ⟨Cg,hCg,hgeom⟩ := bounded_dyadic_power_sum θ hθ
  refine ⟨C*Cg,mul_pos hC hCg,?_⟩
  intro η
  filter_upwards [hbound η,eventually_gt_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd' v hv rows hrows hnorm i hi hbin
  dsimp only
  intro t ht
  have hZp : 0< Z := zero_lt_one.trans hZ
  let Y : Fin N→ℝ := fun j=> Z^(ell j)
  let T : Fin N→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
  let Rn : ℕ→Finset FreeRow := fun k=> rows∩dyadicRows 1 k
  let term : FreeRow→ℂ := fun u=> frequencyWeight ((17/50:ℂ)+t.1.2*Complex.I) ⟨u.val,u.property.1⟩*
    ∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
      (fun j=> iv_globalFloorPoolOutside M H S N c b Y j _ (P j).property) W Y
      (((51/100+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-51/100-6*e:ℝ):ℂ)+t.2*Complex.I)
      ((17/50:ℂ)+t.1.2*Complex.I)
  let D : ℝ := C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(loss-(RHIVProbe.ell*(3/20))+(RHIVProbe.ell)*mesh)
  have hD : 0≤ D := by dsimp [D];positivity
  have hdyad (k : ℕ) : ‖∑u∈Rn k,term u‖≤ D*((2:ℝ)^k)^θ := by
    let vk := Real.logb Z ((2:ℝ)^k)
    have hvk : 0≤ vk := Real.logb_nonneg hZ (one_le_pow₀ (by norm_num))
    have heq : Z^vk=(2:ℝ)^k := Real.rpow_logb hZp hZ.ne' (by positivity)
    have hsub : Rn k⊆rows := Finset.inter_subset_left
    have hn : ∀u∈Rn k,Z^vk≤ rowNorm u ∧ rowNorm u≤2*Z^vk := by
      intro u hu
      have h := (mem_dyadicRows.mp (Finset.mem_inter.mp hu).2).2
      simpa only [heq,one_mul] using And.intro h.1 h.2.le
    have hh := hb d hd hd' vk hvk (Rn k) (fun u hu=> hrows u (hsub hu)) hn i hi
      (fun u hu=> hbin u (hsub hu)) t ht
    change ‖∑u∈Rn k,term u‖≤_ at hh
    apply hh.trans_eq
    have hp : Z^(vk*θ+loss-(RHIVProbe.ell*(3/20))+(RHIVProbe.ell)*mesh)=Z^(loss-(RHIVProbe.ell*(3/20))+(RHIVProbe.ell)*mesh)*((2:ℝ)^k)^θ := by
      rw [show vk*θ+loss-(RHIVProbe.ell*(3/20))+(RHIVProbe.ell)*mesh=(loss-(RHIVProbe.ell*(3/20))+(RHIVProbe.ell)*mesh)+vk*θ by ring,Real.rpow_add hZp,
        Real.rpow_mul hZp.le,heq]
    change C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(vk*θ+loss-(RHIVProbe.ell*(3/20))+(RHIVProbe.ell)*mesh)=_
    rw [hp]
    dsimp [D]
    ring
  have hpart := retained_dyadic_sum rows (Z^v) (fun u hu=>⟨(hrows u hu).1,hnorm u hu⟩) term
  change ‖∑u∈rows,term u‖≤_
  rw [hpart]
  calc
    _ ≤ ∑k∈smallDyadicIndices (Z^v),‖∑u∈Rn k,term u‖ := norm_sum_le _ _
    _ ≤ ∑k∈smallDyadicIndices (Z^v),D*((2:ℝ)^k)^θ := Finset.sum_le_sum (fun k _=> hdyad k)
    _ = D*∑k∈smallDyadicIndices (Z^v),((2:ℝ)^k)^θ := (Finset.mul_sum _ _ _).symm
    _ ≤ D*(Cg*(Z^v)^θ) := mul_le_mul_of_nonneg_left
      (hgeom (Z^v) (by positivity) (smallDyadicIndices (Z^v)) (fun k hk=> mem_smallDyadicIndices.mp hk)) hD
    _ = _ := by
      have hp : Z^(loss-(RHIVProbe.ell*(3/20))+(RHIVProbe.ell)*mesh)*(Z^v)^θ=Z^(v*θ+loss-(RHIVProbe.ell*(3/20))+(RHIVProbe.ell)*mesh) := by
        rw [←Real.rpow_mul hZp.le,←Real.rpow_add hZp]
        congr 1
        ring
      dsimp [D]
      calc
        _ = (C*Cg)*(η.modulus.absNorm:ℝ)^(2*eps)*(Z^(loss-(RHIVProbe.ell*(3/20))+(RHIVProbe.ell)*mesh)*(Z^v)^θ) := by ring
        _ = _ := by rw [hp]

end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2CentralExponent
/-! Literal physical Mellin exponent at v2 geometry. The actual high
row sums remain separate. The contradiction gap, rather than a fixed
negative ideal endpoint, pays for rounding, contour and height losses. -/
namespace RHIVProbe
noncomputable section
def physicalExponent (a d rowExponent q s : ℝ) : ℝ :=
  x*(1/2-s)+a+s-1-a*y-d*s+d*rowExponent+d*(a-1/2)+ell*(s-1/2+q)

def signalExponent (beta : ℝ) : ℝ := beta-(4+b)/6

lemma physical_slope_identity (a d row q s : ℝ) :
    physicalExponent a d row q s =
      physicalExponent a h row q s+(d-h)*(row+a-1/2-s) := by
  unfold physicalExponent
  ring

lemma signal_gap_identity (beta : ℝ) :
    signalExponent beta = lowExponent+(beta-boundary) := by
  rw [lowExponent_signal]
  unfold signalExponent
  ring


end
end RHIVProbe
namespace RHIVProbe
noncomputable section
def endpointExponent (delta u row : ℝ) : ℝ :=
  -1/4+b/6+5*ell/4+(1/2+ell)*delta+ell*u*delta-h*(1-row)
lemma physical_endpoint_identity (delta u row s : ℝ) :
    physicalExponent ((1+delta)/2) h row (delta*u) s-lowExponent =
      endpointExponent delta u row := by
  unfold physicalExponent lowExponent endpointExponent x y h
  ring
/-- A scalar endpoint certificate is sufficient for the actual Mellin exponent.
The arithmetic row-count estimate is not a premise of this scalar lemma. -/
theorem balanced_physical_margin (delta u row ideal d s loss zeta beta : ℝ)
    (hend : endpointExponent delta u ideal ≤ 0)
    (hrow : row ≤ ideal+loss) (hzeta : 0 ≤ zeta) (hd : d ≤ h+zeta)
    (hslo : 0 ≤ row+delta/2-s) (hshi : row+delta/2-s ≤ 2) :
    physicalExponent ((1+delta)/2) d row (delta*u) s-signalExponent beta ≤
      h*loss+2*zeta-(beta-boundary) := by
  have hh := gate_h_positive
  have hm := mul_le_mul_of_nonneg_left hrow hh.le
  have hext := mul_le_mul_of_nonneg_right (show d-h ≤ zeta by linarith) hslo
  have hz := mul_le_mul_of_nonneg_left hshi hzeta
  have hi := physical_endpoint_identity delta u row s
  have hs := physical_slope_identity ((1+delta)/2) d row (delta*u) s
  have ha : row+(1+delta)/2-1/2-s = row+delta/2-s := by ring
  rw [ha] at hs
  rw [signal_gap_identity]
  unfold endpointExponent at hi hend
  nlinarith
end
end RHIVProbe

-- Parametric high adaptation: V2AdaptiveExponent

/-! The actual source adaptive count (Delta=0) at the v2 geometry.
This converts a count into an exponent; it does not assume or prove an
arithmetic row-moment estimate. -/
namespace RHIVProbe
noncomputable section
open OAI.SevenEighths

def mixedPhysicalExponent (a v d row q contour : ℝ) : ℝ :=
  physicalExponent a v row q contour+(d-v)*row

def realLoss (N : ℕ) (v e eps loss mesh : ℝ) : ℝ :=
  (16-6*y)*e+12*v*e+v*eps*(N+8)+loss+ell*mesh

lemma realLoss_bound (N : ℕ) (v e eps loss mesh : ℝ)
    (hv : v≤1) (he : 0≤ e) (heps : 0≤ eps) :
    realLoss N v e eps loss mesh≤26*e+(N+8)*eps+loss+ell*mesh := by
  have hy : 1/3≤ y := by iv_high_geometry
  have h1 := mul_le_mul_of_nonneg_right hv he
  have h2 := mul_le_mul_of_nonneg_right hv (show 0≤ eps*(N+8) by positivity)
  have h3 := mul_nonneg (show 0≤ y-1/3 by linarith) he
  unfold realLoss
  nlinarith

lemma central_class_exponent_identity (N : ℕ)
    (a v d row q e eps loss mesh overhead : ℝ) :
    ((1-y)*a+(4/25)*x-33/50+(16-6*y)*e)+
      (overhead+d*row+v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-
        ell*(4/25)+ell*q+ell*mesh) =
      mixedPhysicalExponent a v d row q (17/50)+realLoss N v e eps loss mesh+overhead := by
  unfold mixedPhysicalExponent physicalExponent realLoss
  ring


end
end RHIVProbe

-- Parametric high adaptation: V2ProfileScale
namespace RHIVProbe
noncomputable section
lemma physical_scale_identity (Z a e : ℝ) (hZ : 0< Z) :
    (Z^x)^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^y)^(-a-6*e) =
      Z^((1-y)*a+(4/25)*x-33/50+(16-6*y)*e) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring
#print axioms physical_scale_identity
end
end RHIVProbe

-- Parametric high adaptation: V2CentralScales
namespace RHIVProbe
noncomputable section
def sourceExponent (a d row q : ℝ) : ℝ := physicalExponent a d row q (17/50)
lemma floor_source_margin (q zeta d : ℝ) (hq : q≤1/100)
    (hzeta : 0≤ zeta) (hd : d≤ h+zeta) :
    sourceExponent (51/100) d 1 q-lowExponent≤-(1/200)+2*zeta := by
  have hm := mul_le_mul_of_nonneg_left hq analytic_geometry.1.le
  have hbase : sourceExponent (51/100) h 1 (1/100)-lowExponent≤-(1/200) := by
    dsimp only [sourceExponent,physicalExponent]
    iv_high_geometry
  have h1 : d-h≤ zeta := by linarith
  have hh := mul_le_mul_of_nonneg_right h1 (show (0:ℝ)≤67/100 by norm_num)
  have hz := mul_le_mul_of_nonneg_left (show (67/100:ℝ)≤2 by norm_num) hzeta
  have hi : sourceExponent (51/100) d 1 q=
      sourceExponent (51/100) h 1 (1/100)+(d-h)*(67/100)+ell*(q-1/100) := by
    unfold sourceExponent physicalExponent
    ring
  linarith
#print axioms floor_source_margin
end
end RHIVProbe

-- Parametric high adaptation: V2CubeFloorGlobalIntegral
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

omit [NeZero M] in
private theorem iv_globalFloorIntegralPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem iv_actual_global_floor_cube_norm (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤ A)
    (hellsum : ∑j,ell j=RHIVProbe.ell)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0< C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v : ℝ),0≤ v → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,rowNorm u≤ Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e) →
      let Yp : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Yp j)
      ‖finiteCentralCubeRows S hS hmax η rows T (iv_globalFloorIntegralPoolOutside M H S N c b Yp) W Yp
        W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z e (fun _=>51/100) (fun _=>(3*i+1:ℕ)*Z^τ)‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(RHIVProbe.sourceExponent (51/100) v 1 (1/100)+
            RHIVProbe.realLoss N v e eps loss mesh) := by
  obtain ⟨Ca,hCa,hbound⟩ := iv_actual_global_floor_cube_arithmetic M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
  obtain ⟨Cp,hCp,hprofile⟩ := actual_common_cube_aggregate_norm W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨Cp*Ca,mul_pos hCp hCa,?_⟩
  intro η
  filter_upwards [hbound η,source_cube_height_eventually τ hτ] with Z hb hZ
  intro d hd hd' v hv rows hrows hnorm i hi hbin
  dsimp only
  have hZp : 0< Z := zero_lt_one.trans_le hZ.1
  let Yp : Fin N→ℝ := fun j=> Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Yp j)
  have hheight : (3*i+1:ℕ)*Z^τ≤(3*i+2:ℕ)*Z^τ := by
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZp.le _)
    exact_mod_cast (show 3*i+1≤3*i+2 by omega)
  let mass : ℝ := Ca*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(v*(67/100+12*e+eps*(N+8))+loss-(RHIVProbe.ell*(3/20))+(RHIVProbe.ell)*mesh)
  have hp := hprofile e (51/100) (Z^τ) ((3*i+1:ℕ)*Z^τ) i he he1 le_rfl (by norm_num)
    hZ.2 hheight S hS hmax hfirst η rows (fun u hu=>(hrows u hu).1) T
    (iv_globalFloorIntegralPoolOutside M H S N c b Yp) (rayCubeFamily M H hH) hbin W Yp
    (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z (by positivity) (by positivity) hZp mass (by dsimp [mass];positivity)
    (hb d hd hd' v hv rows hrows hnorm i hi hbin)
  apply hp.trans_eq
  rw [RHIVProbe.physical_scale_identity Z (51/100) e hZp]
  have hpowers : Z^((1-RHIVProbe.y)*(51/100)+(4/25)*RHIVProbe.x-33/50+((16-6*RHIVProbe.y))*e)*
      Z^(v*(67/100+12*e+eps*(N+8))+loss-(RHIVProbe.ell*(3/20))+(RHIVProbe.ell)*mesh)=
      Z^(RHIVProbe.sourceExponent (51/100) v 1 (1/100)+
        RHIVProbe.realLoss N v e eps loss mesh) := by
    rw [←Real.rpow_add hZp]
    congr 1
    unfold RHIVProbe.sourceExponent RHIVProbe.physicalExponent RHIVProbe.realLoss
    ring
  dsimp [mass]
  calc
    _ = (Cp*Ca)*(η.modulus.absNorm:ℝ)^(2*eps)*(Z^((1-RHIVProbe.y)*(51/100)+(4/25)*RHIVProbe.x-33/50+((16-6*RHIVProbe.y))*e)*
      Z^(v*(67/100+12*e+eps*(N+8))+loss-(RHIVProbe.ell*(3/20))+(RHIVProbe.ell)*mesh)) := by ring
    _ = _ := by rw [hpowers]

end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2CubeFloorNormalized
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

omit [NeZero M] in
private theorem iv_normalizedFloorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem iv_actual_normalized_floor_cube (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤ W j t ∧ W j t≤ A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=RHIVProbe.ell)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0< nu) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0< C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v : ℝ),0≤ v → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,rowNorm u≤ Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e) →
      let Yp : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Yp j)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (RHIVProbe.ell)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (iv_normalizedFloorPoolOutside M H S N c b Yp) (fun j y=>(W j y:ℂ)) Yp
        W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z e (fun _=>51/100) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(RHIVProbe.sourceExponent (51/100) v 1 (1/100)+
            RHIVProbe.realLoss N v e eps loss mesh+nu) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWC (j : Fin N) : ContDiff ℝ ∞ (WC j) := Complex.ofRealCLM.contDiff.comp (hW j)
  have hWCs (j : Fin N) : Function.support (WC j)⊆Ioo c b := by
    intro y hy
    apply hWs j
    intro hh
    exact hy (by dsimp [WC];rw [hh];simp)
  have hWCB (j : Fin N) (y : ℝ) : ‖WC j y‖≤ A := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  obtain ⟨Cg,hCg,hbound⟩ := iv_actual_global_floor_cube_norm M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi WC hWCs hWC hWCB hellsum
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  have hellpos (j : Fin N) : 0< ell j :=
    (mul_pos (hdmin.trans_le hdRange) hrmin).trans_le (hello j)
  obtain ⟨Cn,hCn,hnormer⟩ := iv_actual_ray_normalizer_inverse M H hH S hS c b hc hcb ell hellpos hellsum
    W hW hcompact hWs (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  refine ⟨Cg*Cn,mul_pos hCg hCn,?_⟩
  intro η
  filter_upwards [hbound η,hnormer,eventually_gt_atTop (0:ℝ)] with Z hb hn hZ
  intro d hd hd' v hv rows hrows hnorm i hi hbin
  dsimp only at hn ⊢
  refine ⟨hn.1,?_⟩
  have hh := hb d hd hd' v hv rows hrows hnorm i hi hbin
  rw [div_eq_mul_inv,norm_mul]
  have hm := mul_le_mul hh hn.2 (norm_nonneg _) (by positivity)
  apply hm.trans_eq
  rw [Real.rpow_add hZ (RHIVProbe.sourceExponent (51/100) v 1 (1/100)+
    RHIVProbe.realLoss N v e eps loss mesh) nu]
  ring

end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2CubeFloorSaving
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

omit [NeZero M] in
private theorem iv_savingFloorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem iv_actual_floor_cube_saving (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤ W j t ∧ W j t≤ A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=RHIVProbe.ell)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0< nu)
    (ζ saving : ℝ) (hζ : 0≤ζ) (hζhi : ζ≤1/48) (_hsaving : 0< saving)
    (htotal : 2*ζ+26*e+(N+8)*eps+loss+(RHIVProbe.ell)*mesh+nu+saving≤1/200) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0< C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v : ℝ),0≤ v → v≤ RHIVProbe.h+ζ → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,rowNorm u≤ Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e) →
      let Yp : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Yp j)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (RHIVProbe.ell)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (iv_savingFloorPoolOutside M H S N c b Yp) (fun j y=>(W j y:ℂ)) Yp
        W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z e (fun _=>51/100) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(RHIVProbe.lowExponent-saving) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ := iv_actual_normalized_floor_cube M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  refine ⟨C,hC,?_⟩
  intro η
  filter_upwards [hbound η,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd' v hv hvhi rows hrows hnorm i hi hbin
  dsimp only
  have hh := hb d hd hd' v hv rows hrows hnorm i hi hbin
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hm := RHIVProbe.floor_source_margin (1/100) ζ v le_rfl hζ hvhi
  have hl := RHIVProbe.realLoss_bound N v e eps loss mesh (by
    have hh : RHIVProbe.h+(1/48:ℝ)≤1 := by iv_high_geometry
    linarith only [hh,hvhi,hζhi]) he.le heps.le
  apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ _) (by positivity)
  linarith

end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2CubeFloorCollected
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

omit [NeZero M] in
private theorem iv_collectedFloorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem iv_actual_floor_rows_saving (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤ W j t ∧ W j t≤ A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=RHIVProbe.ell)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0< nu)
    (ζ saving : ℝ) (hζ : 0≤ζ) (hζhi : ζ≤1/48) (hsaving : 0< saving)
    (htotal : 2*ζ+26*e+(N+8)*eps+loss+(RHIVProbe.ell)*mesh+nu+saving≤1/200) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0< C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v : ℝ),0≤ v → v≤ RHIVProbe.h+ζ → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,rowNorm u≤ Z^v) →
      ∀idx : FreeRow→ℕ,(∀u∈rows,idx u≤ n) →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(idx u+1:ℕ)*Z^τ)<51/100+2*e) →
      let Yp : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Yp j)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (RHIVProbe.ell)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (iv_collectedFloorPoolOutside M H S N c b Yp) (fun j y=>(W j y:ℂ)) Yp
        W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z e (fun _=>51/100) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(RHIVProbe.lowExponent-saving) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ := iv_actual_floor_cube_saving M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 nu hnu ζ saving hζ hζhi hsaving htotal
  refine ⟨(n+1:ℕ)*C,by positivity,?_⟩
  intro η
  filter_upwards [hbound η] with Z hb
  intro d hd hd' v hv hvhi rows hrows hnorm idx hidx hbin
  dsimp only
  let Yp : Fin N→ℝ := fun j=> Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Yp j)
  let hT := iv_collectedFloorPoolOutside M H S N c b Yp
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
    (Probe.principalScalar Finset.univ Z (RHIVProbe.ell)
      (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Yp)) : ℂ)
  let Ri : ℕ→Finset FreeRow := fun i=> rows.filter (fun u=> idx u=i)
  have hnormer := (hb d hd hd' v hv hvhi ∅ (by simp) (by simp) 0 (Nat.zero_le n) (by simp)).1
  refine ⟨hnormer,?_⟩
  have hpart := finiteCentralCubeRows_bin_partition S hS hmax η rows T hT WC Yp W0 W1
    (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z e (Z^τ) idx (fun _=>0) n 0 (fun u hu=>⟨hidx u hu,le_rfl⟩)
  have heq : finiteCentralCubeRows S hS hmax η rows T hT WC Yp W0 W1
      (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z e (fun _=>51/100) (fun u=>(3*idx u+1:ℕ)*Z^τ)=
      ∑i∈Finset.range (n+1),finiteCentralCubeRows S hS hmax η (Ri i) T hT WC Yp W0 W1
        (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z e (fun _=>51/100) (fun _=>(3*i+1:ℕ)*Z^τ) := by
    simpa [cubeBinRows,Ri] using hpart
  change ‖finiteCentralCubeRows S hS hmax η rows T hT WC Yp W0 W1
    (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z e (fun _=>51/100) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤_
  rw [heq,Finset.sum_div]
  apply (norm_sum_le _ _).trans
  have hboundi (i : ℕ) (hi : i∈Finset.range (n+1)) :
      ‖finiteCentralCubeRows S hS hmax η (Ri i) T hT WC Yp W0 W1
        (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z e (fun _=>51/100) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤
      C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(RHIVProbe.lowExponent-saving) := by
    have hsub : Ri i⊆rows := Finset.filter_subset _ _
    have hbi : ∀u∈Ri i,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e := by
      intro u hu
      have hh := hbin u (hsub hu)
      rwa [(Finset.mem_filter.mp hu).2] at hh
    exact (hb d hd hd' v hv hvhi (Ri i) (fun u hu=> hrows u (hsub hu))
      (fun u hu=> hnorm u (hsub hu)) i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hbi).2
  calc
    _ ≤ ∑i∈Finset.range (n+1),C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(RHIVProbe.lowExponent-saving) := Finset.sum_le_sum hboundi
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul];ring

end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2NonfloorTransport
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

omit [NeZero M] in
private theorem iv_nonfloorTransportPoolOutside (S : Finset (Ideal O)) (K : ℕ) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

theorem iv_actual_nonfloor_probe_transport (K : ℕ) (e δ a b B ζ saving τ ellMin nu : ℝ)
    (he : 0< e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0< a) (hab : a≤ b) (hB : 0≤ B) (hmin : 0< ellMin) (hnu : 0< nu)
    (hβ : (RHIVProbe.boundary:ℝ)≤ HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin≤ ell j) (hellinj : Function.Injective ell) (hellsum : ∑j,ell j=RHIVProbe.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b) (hWB : ∀j y,0≤ W j y ∧ W j y≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (sigma : ℝ) (hsigma : 0< sigma)
    (hgeometric : sigma+8*e+nu≤ RHIVProbe.smallSaving) (hprincipal : sigma+nu≤1/3000)
    (hwindow : sigma+e≤(RHIVProbe.boundary)*ellMin) (hlarge : sigma+nu≤ saving+RHIVProbe.lowExponent)
    (eps R dmin dmax rmin ε κ cost mesh margin loss : ℝ)
    (heps : 0< eps) (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax)
    (hrmin : 0< rmin) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh) (hmargin : 0< margin)
    (hphasebudget : 8*e*R+κ≤ε) (hphasegap : ε< rmin*mesh)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (hcap : RHIVProbe.h+ζ≤ dmax-margin)
    (helllo : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (hfloorbudget : 2*ζ+26*e+(K+8)*eps+loss+(RHIVProbe.ell)*mesh+nu+sigma≤1/200) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0< n ∧ ∀η : Character,∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,
      let Yp := fun j=> Z^(ell j)
      let T := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
      let hT := iv_nonfloorTransportPoolOutside M H S K a b Yp
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (RHIVProbe.ell) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤ a ∧ a≤1 ∧
        a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ)< a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ)< a+2*e ∧
        (51/100< a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a≤ s.re ∧ s.re< a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((RHIVProbe.h:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let height : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=> canonicalSlotSupport (T j)) WC Yp (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-(4+RHIVProbe.b)/6) Z-
        finiteCentralCubeRows S hS hmax η
          (supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((RHIVProbe.h:ℝ)+ζ))) grid) T hT WC Yp
          W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z e alpha height/normer‖≤
        C*Z^(RHIVProbe.signalExponent HeckeZeroSupremum.beta-sigma) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨n,hn,htransport⟩ := iv_actual_normalized_probe_transport_saving M H hH K e δ a b B ζ saving τ ellMin nu
    he he' hδ hδ' hζ hζ' hτ ha hab hB hmin hnu hβ S hS hmax hfirst ell hell hellinj hellsum
    W hW hcompact hsupp hWB hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    sigma hsigma hgeometric hprincipal hwindow hlarge
  obtain ⟨Cf,hCf,hfloor⟩ := iv_actual_floor_rows_saving M H hH K n e eps a b B R dmin dmax rmin τ ε κ cost mesh
    (1/100) margin loss he he' heps ha hab hB hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
    (by norm_num) hphasebudget hphasegap hmargin hheight hloss S hS hfirst hmax ell hellinj helllo hellhi
    W hsupp hW hWB hcompact hne hellsum W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    nu hnu ζ sigma hζ.le (by linarith) hsigma hfloorbudget
  refine ⟨n,hn,?_⟩
  intro η
  obtain ⟨Ct,hCt,htransport⟩ := htransport η
  let C := Ct+Cf*(η.modulus.absNorm:ℝ)^(2*eps)
  have hC : 0< C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [htransport,hfloor η,eventually_ge_atTop (1:ℝ)] with Z ht hf hZ
  dsimp only at ht ⊢
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,herror⟩ := ht
  refine ⟨hnorm,idx,grid,hlabels,hbins,hray,?_⟩
  let Yp : Fin K→ℝ := fun j=> Z^(ell j)
  let T : Fin K→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
  let hT := iv_nonfloorTransportPoolOutside M H S K a b Yp
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  let rows := rowBand (Z^(1/100:ℝ)) (Z^((RHIVProbe.h:ℝ)+ζ))
  let floors := supportedFloorRows S hmax rows grid
  have hrows : ∀u∈floors,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
      (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(dmax-margin) := by
    intro u hu
    rcases (mem_supportedFloorRows S hmax rows grid u).mp hu with ⟨hur,hcal,hg⟩
    have hm := mem_rowBand.mp hur
    exact ⟨hm.1,hm.2.1,hcal,hm.2.2.le.trans (Real.rpow_le_rpow_of_exponent_le hZ hcap)⟩
  have hnorms : ∀u∈floors,rowNorm u≤ Z^((RHIVProbe.h:ℝ)+ζ) := by
    intro u hu
    exact (mem_rowBand.mp ((mem_supportedFloorRows S hmax rows grid u).mp hu).1).2.2.le
  have hfloorbin : ∀u∈floors,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
      (3*(idx u+1:ℕ)*Z^τ)<51/100+2*e := by
    intro u hu
    have hg := ((mem_supportedFloorRows S hmax rows grid u).mp hu).2.2
    have hh := (hbins u).2.2.2.2.1
    simpa only [hg,Nat.cast_zero,mul_zero,add_zero] using hh
  have hb := (hf dmax hdRange le_rfl (RHIVProbe.h+ζ) (by linarith only [RHIVProbe.gate_h_positive,hζ]) le_rfl floors hrows hnorms idx
    (fun u hu=>(hlabels u).2.1) hfloorbin).2
  have hsplit := finiteCentralCubeRows_supported_split S hS hmax η rows T hT WC Yp W0 W1
    (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z e grid (fun u=>(3*idx u+1:ℕ)*Z^τ)
  change _≤ Ct*Z^(RHIVProbe.signalExponent HeckeZeroSupremum.beta-sigma) at herror
  rw [hsplit] at herror
  have hh := normalized_nonfloor_error _ _ _ _ _ _ _ herror hb
  simp only [neg_div] at hh ⊢
  apply hh.trans
  have hp : Z^(RHIVProbe.lowExponent-sigma)≤ Z^(RHIVProbe.signalExponent HeckeZeroSupremum.beta-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by rw [RHIVProbe.signal_gap_identity];linarith)
  calc
    _ ≤ Ct*Z^(RHIVProbe.signalExponent HeckeZeroSupremum.beta-sigma)+
      (Cf*(η.modulus.absNorm:ℝ)^(2*eps))*Z^(RHIVProbe.signalExponent HeckeZeroSupremum.beta-sigma) := by gcongr
    _ = _ := by dsimp [C];ring


end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2CentralClassArithmetic
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

omit [NeZero M] in
private theorem iv_classPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem iv_actual_class_cube_arithmetic (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤ A)
    (hellsum : ∑j,ell j=RHIVProbe.ell) :
    ∃C : ℝ,0< C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v a q D Rcount : ℝ),0≤ v → 51/100≤ a → a≤1 → 0≤ D → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,Z^v≤ rowNorm u ∧ rowNorm u≤2*Z^v) →
      (rows.card:ℝ)≤ D*(Z^d)^Rcount →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      let Y : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      (∀u∈rows,weightedMean Finset.univ (fun j=> ell j/d)
        (fun j=> HeckePrimeAmplitudeBins.amplitude (Y j) (a-1/2) mesh
          (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) ((17/50:ℂ)+t.1.2*Complex.I)))=q) →
      ‖cubeArithmeticSum S hS hmax η rows T (iv_classPoolOutside M H S N c b Y) W Y a e t‖≤
        C*D*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(d*Rcount+v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-(RHIVProbe.ell*(4/25))+(RHIVProbe.ell)*q+(RHIVProbe.ell)*mesh) := by
  obtain ⟨C,hC,hbound⟩ := actual_fixed_cube_prime_bound M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB
  let AA : ℝ := max 1 ((2:ℝ)^(4/25+12*e+eps*(N+8)))
  have hAA : 0< AA := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C*AA,mul_pos hC hAA,?_⟩
  intro η
  filter_upwards [hbound η,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd' v a q D Rcount hv ha ha' hD rows hrows hnorm hcard i hi hbin
  dsimp only
  intro t ht hq
  have hZp : 0< Z := zero_lt_one.trans_le hZ
  have hd0 : 0< d := hdmin.trans_le hd
  let Y : Fin N→ℝ := fun j=> Z^(ell j)
  let T : Fin N→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let α : ℝ := a-1/2+12*e+eps*(N+8)
  let F : FreeRow→ℝ := fun u=>‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
    (fun j=> iv_classPoolOutside M H S N c b Y j _ (P j).property) W Y
    (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I) z‖
  let E : ℝ := C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^loss*Z^(-(RHIVProbe.ell*(4/25))+(RHIVProbe.ell)*q+(RHIVProbe.ell)*mesh)
  have hE : 0≤ E := by dsimp [E];positivity
  have hF (u : FreeRow) (hu : u∈rows) : F u≤ E*rowNorm u^α := by
    rcases hrows u hu with ⟨hu1,hulo,hcal,huhi⟩
    have hh := hb d hd hd' u hu1 hulo hcal huhi a i hi ha ha' (hbin u hu) t ht
    dsimp only at hh
    let g : Fin N→ℝ := fun j=> HeckePrimeAmplitudeBins.amplitude (Y j) (a-1/2) mesh
      (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z)
    have hp : (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh))=Z^(-(RHIVProbe.ell*(4/25))+(RHIVProbe.ell)*q+(RHIVProbe.ell)*mesh) := by
      rw [show (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh))=
        Z^(-((RHIVProbe.ell*(4/25)):ℝ)+(RHIVProbe.ell)*weightedMean Finset.univ (fun j=> ell j/d) g+(RHIVProbe.ell)*mesh) from
        iv_source_slot_product Finset.univ ell g Z d mesh hZp hd0.ne' hellsum]
      rw [show weightedMean Finset.univ (fun j=> ell j/d) g=q from hq u hu]
    have hh' := hh.2
    rw [hp] at hh'
    convert hh' using 1 ; dsimp [F,E,α,Y,z,g] ; ring
  have hh := dyadic_weighted_rows_card α (17/50) E (Z^v) (D*(Z^d)^Rcount) hE
    (Real.rpow_pos_of_pos hZp _) rows hcard hnorm F hF z (by simp [z])
  have hsum : ‖cubeArithmeticSum S hS hmax η rows T (iv_classPoolOutside M H S N c b Y) W Y a e t‖≤
      ∑u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u := by
    unfold cubeArithmeticSum
    exact (norm_sum_le _ _).trans_eq (by apply Finset.sum_congr rfl;intro u hu;rw [norm_mul])
  have hAp : ProbeSelectedPrimeSums.annularPower 1 2 (α-17/50)≤ AA :=
    annular_power_uniform _ _ (by dsimp [α];linarith)
  apply (hsum.trans hh).trans
  have hpow : (Z^d)^Rcount*Z^loss*Z^(-(RHIVProbe.ell*(4/25))+(RHIVProbe.ell)*q+(RHIVProbe.ell)*mesh)*(Z^v)^(α-17/50)=
      Z^(d*Rcount+v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-(RHIVProbe.ell*(4/25))+(RHIVProbe.ell)*q+(RHIVProbe.ell)*mesh) := by
    simp_rw [←Real.rpow_mul hZp.le]
    rw [←Real.rpow_add hZp,←Real.rpow_add hZp,←Real.rpow_add hZp]
    congr 1
    dsimp [α]
    ring
  calc
    _ ≤ (D*(Z^d)^Rcount)*E*AA*(Z^v)^(α-17/50) := by gcongr
    _ = _ := by
      dsimp [E]
      calc
        _ = (C*AA)*D*(η.modulus.absNorm:ℝ)^(2*eps)*
          ((Z^d)^Rcount*Z^loss*Z^(-(RHIVProbe.ell*(4/25))+(RHIVProbe.ell)*q+(RHIVProbe.ell)*mesh)*(Z^v)^(α-17/50)) := by ring
        _ = _ := by rw [hpow]

end

end RHZeroFreeExtension.AnalyticHigh

#print axioms RHZeroFreeExtension.AnalyticHigh.iv_actual_nonfloor_probe_transport

#print axioms RHZeroFreeExtension.AnalyticHigh.iv_actual_class_cube_arithmetic



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch ProbePhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem iv_actual_source_amplitude_batches
    (cutoff : ℝ → ℝ → ℝ)
    (hcutoff : ∀ delta q : ℝ, 0≤ delta → 1≤ cutoff delta q ∧ cutoff delta q≤3/2) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth : ℝ) (I : ℕ)
    (hdmin : 0< dmin) (hdmax : dmin≤ dmax) (hdtop : dmax≤37/42) (hτ : 0<τ)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*heightCost)
    (hε : 0<ε) (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤ heightCost)
    (hmargin : 0< margin) (hm : 0≤ mesh) (hb : 0< binWidth)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*heightCost≤ε/2) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤ d → d≤ dmax →
    ∀(U : ℝ) (rows : Finset FreeRow),rows.Nonempty → rows⊆rowBand (Z^(1/100:ℝ)) U →
      (∀u∈rows,(calibrationForSet S hmax).residueMonoid u.val≠0) →
      (∀u∈rows,rowNorm u≤ Z^(d-margin)) →
    ∀(a : ℝ) (i : ℕ),i≤ I → 51/100< a → a≤1 →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^τ)) →
    ∀(N : ℕ) (ell : Fin N→ℝ),(∀j,0< ell j) → (∀j,ell j≤ dmin*mesh) → 1/6≤∑j,ell j →
    ∀(W : Fin N→ℝ→ℂ) (upper : Fin N→ℝ) (z : Fin N→ℂ),
    let Q := HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=> u.val)
      W upper (fun j=> ell j/d) z (Z^d)
    ∀bin : HeckeDetectorFiberPartition.BinLabel (Finset.univ : Finset (Fin N)) ((2*a-1)/2) binWidth,
    let rows' := HeckeDetectorAmplitudeFirst.amplitudeRows rows Finset.univ
      (Z^d) ((2*a-1)/2) binWidth hb (fun j=> ell j/d) Q bin
    rows'.Nonempty →
    let q := HeckeDetectorAmplitudeFirst.classMean Finset.univ ((2*a-1)/2) binWidth (fun j=> ell j/d) bin
    ∃B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
        (Z^d) a ε (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
      B.rows=rows' ∧ B.data=sourceMomentData M H hH S hS.prime η ∧
      B.reverse=sourceMomentReverse M H ∧ B.slots=Finset.univ ∧
      B.widths=(fun j=> ell j/d) ∧ B.profile=W ∧ B.upper=upper ∧ B.external=z ∧
      B.mesh=mesh ∧ B.binWidth=binWidth ∧
      (∀u∈rows',∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) ∧
      (∀u∈B.rows,HeckeDetectorAmplitudeFirst.rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=> u.val)
          B.profile B.upper B.widths B.external (Z^d)) u=q) := by
  have hbatches := perturbed_actual_source_batch M H hH S hS hmax η
    dmin dmax τ ε e κ heightCost margin mesh binWidth I hdmin hdmax hdtop hτ hτzero hτheight
    hε he he' hκ hκ' hheightCost hmargin hm hb hbudget
  filter_upwards [hbatches] with Z hbatch
  intro d hd hd' U rows hne hrows hcal hrow a i hi ha ha' hnext hcurrent N ell hell hsmall hsum W upper z
  dsimp only
  intro bin hne'
  let Q := HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=> u.val)
    W upper (fun j=> ell j/d) z (Z^d)
  let rows' := HeckeDetectorAmplitudeFirst.amplitudeRows rows Finset.univ
    (Z^d) ((2*a-1)/2) binWidth hb (fun j=> ell j/d) Q bin
  let q := HeckeDetectorAmplitudeFirst.classMean Finset.univ ((2*a-1)/2) binWidth (fun j=> ell j/d) bin
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hcut := hcutoff (2*a-1) q (by linarith)
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam⟩ :=
    hbatch d hd hd' U rows' hne' (hsub.trans hrows)
      (fun u hu=> hcal u (hsub hu)) (fun u hu=> hrow u (hsub hu)) a i hi ha ha'
      (fun u hu=> hnext u (hsub hu)) (fun u hu=> hcurrent u (hsub hu))
      (cutoff (2*a-1) q) hcut.1 hcut.2 N ell hell hsmall hsum W upper z
  refine ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam,?_⟩
  intro u hu
  have hu' : u∈rows' := hBr ▸ hu
  rw [hSlots,hWidths,hW,hUpper,hZ,hBin]
  exact HeckeDetectorAmplitudeFirst.rowMean_eq rows Finset.univ (Z^d) ((2*a-1)/2)
    binWidth hb (fun j=> ell j/d) Q bin u hu'
#print axioms iv_actual_source_amplitude_batches

end SevenEighths.ProbeHighRowFamily

end

end OAI

namespace RHIVProbe
noncomputable section
open OAI.SevenEighths
def R (delta u : ℝ) : ℝ := RHBootstrapCount.countR (5/6) (2/(3*momentKappa)) delta u
class CountGeometry [Geometry] [MomentParameter] : Prop where
  endpoint : ∀ delta u : ℝ, 0≤ delta → delta≤5/6 → 0≤ u → u≤1/2 →
    endpointExponent delta u (R delta u)≤0
variable [CountGeometry]
/-- The actual source count on the balanced branch, with a budget paid
from the contradiction gap. The upper bound on a includes all a≤7/8. -/
theorem adaptive_mixed_saving (N : ℕ)
    (a q epsilon epsilonM slotMesh nu zeta mu v d e eps loss mesh overhead saving beta : ℝ)
    (ha : 1/2< a) (ha' : a≤11/12) (hq : 0≤ q) (hq' : q≤(2*a-1)/2)
    (hepsilon : 0≤ epsilon) (hepsilonM : 0≤ epsilonM) (hslot : 0≤ slotMesh) (hnu : 0≤ nu)
    (hcount : 159*epsilon+epsilonM+slotMesh+7*nu≤1/32)
    (hzeta : 0≤ zeta) (hv : v≤ h+zeta) (hv1 : v≤1)
    (hmu : 0≤ mu) (hdv : d-v≤ mu) (he : 0≤ e) (heps : 0≤ eps)
    (hbudget : h*(159*epsilon+epsilonM+slotMesh+7*nu)+2*zeta+(3/2)*mu+
      (26*e+(N+8)*eps+loss+ell*mesh)+overhead+saving≤ beta-boundary) :
    mixedPhysicalExponent a v d
      (IVProbeHighRowFamily.adaptiveRowExponent momentKappa (2*a-1) q epsilon epsilonM slotMesh nu)
      q (17/50)+realLoss N v e eps loss mesh+overhead≤ signalExponent beta-saving := by
  let delta := 2*a-1
  let u := q/delta
  let countLoss := 159*epsilon+epsilonM+slotMesh+7*nu
  have hd0 : 0< delta := by dsimp [delta]; linarith
  have hd1 : delta≤5/6 := by dsimp [delta]; linarith
  have hu0 : 0≤ u := div_nonneg hq hd0.le
  have hu1 : u≤1/2 := (div_le_iff₀ hd0).mpr (by dsimp [delta] at *; linarith)
  have hl : 0≤ countLoss := by dsimp [countLoss]; positivity
  have hk := moment_range
  have hk0 : 0 < momentKappa := by linarith [hk.1]
  have hc0 : 0 < 2/(3*momentKappa) := by positivity
  have hc1 : 2/(3*momentKappa) < 1 := by
    apply (div_lt_one (by positivity)).2
    linarith [hk.1]
  have hr := RHBootstrapCount.countR_loss_range (2/(3*momentKappa)) delta u countLoss
    hc0 hc1 hd0.le hd1 hu0 hu1 hl hcount
  change 0≤ R delta u+countLoss ∧ R delta u+countLoss≤3/2 ∧
    0≤ R delta u+countLoss+delta/2-17/50 ∧ R delta u+countLoss+delta/2-17/50≤2 at hr
  have hslo : 0≤ R delta u+countLoss+delta/2-(17/50:ℝ) := hr.2.2.1
  have hshi : R delta u+countLoss+delta/2-(17/50:ℝ)≤2 := hr.2.2.2
  have hm := balanced_physical_margin delta u (R delta u+countLoss) (R delta u) v (17/50)
    countLoss zeta beta (CountGeometry.endpoint delta u hd0.le hd1 hu0 hu1) le_rfl hzeta hv hslo hshi
  have hmul := mul_le_mul_of_nonneg_right hdv (show 0≤ R delta u+countLoss by linarith [hr.1])
  have hmax := mul_le_mul_of_nonneg_left (show R delta u+countLoss≤3/2 by linarith [hr.2.1]) hmu
  have hloss := realLoss_bound N v e eps loss mesh hv1 he heps
  have haeq : (1+delta)/2=a := by dsimp [delta]; ring
  have hqeq : delta*u=q := mul_div_cancel₀ q hd0.ne'
  rw [haeq,hqeq] at hm
  change mixedPhysicalExponent a v d
    (if delta≤5/6 then R delta u+159*epsilon+epsilonM+slotMesh+7*nu
      else 1-delta+78*epsilon+epsilonM) q (17/50)+
      realLoss N v e eps loss mesh+overhead≤ signalExponent beta-saving
  rw [ite_eq_left hd1]
  have heq : R delta u+159*epsilon+epsilonM+slotMesh+7*nu =
      R delta u+countLoss := by dsimp only [countLoss]; ring
  rw [heq]
  unfold mixedPhysicalExponent
  dsimp only [countLoss] at hm hmul hmax
  dsimp only [countLoss]
  linarith

#print axioms adaptive_mixed_saving
end
end RHIVProbe

variable [RHIVProbe.CountGeometry]

/-! Actual analytic statements at the v2 boundary, CONDITIONAL on constructing
physical probes at the new radical geometry. The premise is explicit and is
not an axiom. V2Optimization proves the scalar certificates, not this premise.
-/
namespace RHIVProbe
noncomputable section
open scoped Classical
open Filter Asymptotics
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open OAI.SevenEighths.HeckeZeroSupremum

/-- The exact missing analytic obligation, preserving the actual coefficient
mask, primitive family, holomorphic correction and asymptotic quantifiers. -/
def PhysicalProbeEstimates : Prop := boundary < beta →
  ∃ omega saving : ℝ, 0 < omega ∧ omega < beta - boundary ∧ 0 < saving ∧
    ∀ eta : Character, FiniteFourier.IsPrimitiveOnIdeals eta.residue →
      ∃ (chi : Character) (H : ℂ → ℂ) (J : ℝ → ℂ) (c : ℝ),
        (∀ I, idealCoeff chi I =
          if IsCoprime I chi.modulus then idealCoeff eta I else 0) ∧
        AnalyticOnNhd ℂ H {s : ℂ | boundary < s.re} ∧
        (∀ s : ℂ, boundary < s.re → ‖H s - 1‖ ≤ (1/2 : ℝ)) ∧
        J =O[atTop] (fun x : ℝ => x ^ (boundary + c + omega)) ∧
        (fun x => J x - HeckeSignal.signal chi H c x) =O[atTop]
          (fun x : ℝ => x ^ (beta + c - saving))

/-- CONDITIONAL v2 supremum bound. The proof does not construct hprobes. -/
theorem beta_star_le_of_probes (hprobes : PhysicalProbeEstimates) : beta ≤ boundary := by
  apply RHZeroFreeExtension.ActualPrimitiveContinuation.beta_le_of_uniform_physical_probes
    boundary (by iv_high_geometry)
    (by iv_high_geometry) hprobes

theorem hecke_nonzero_of_probes (hprobes : PhysicalProbeEstimates)
    (chi : Character) (z : ℂ) (hz : boundary < z.re)
    (hpole : z ≠ 1 ∨ chi.residue ≠ 1) : LFunction chi z ≠ 0 :=
  LFunction_ne_zero_of_beta_lt chi ((beta_star_le_of_probes hprobes).trans_lt hz) hpole

theorem dirichlet_nonzero_of_probes (hprobes : PhysicalProbeEstimates)
    (q : ℕ) (hq : q ≠ 0) (chi : DirichletCharacter ℂ q) (z : ℂ)
    (hz : boundary < z.re) (hpole : ¬ (chi = 1 ∧ z = 1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction chi z ≠ 0 := by
  let : NeZero q := ⟨hq⟩
  apply RHZeroFreeExtension.ActualDirichletTransfer.dirichlet_nonzero_of_hecke_bound
    boundary (by iv_high_geometry) ?_ q chi z hz hpole
  intro eta s hs hp
  exact hecke_nonzero_of_probes hprobes eta s hs hp

theorem zeta_nonzero_of_probes (hprobes : PhysicalProbeEstimates)
    (z : ℂ) (hz : boundary < z.re) (_hpole : z ≠ 1) : riemannZeta z ≠ 0 := by
  apply RHZeroFreeExtension.ActualDirichletTransfer.zeta_nonzero_of_hecke_bound
    boundary (by iv_high_geometry) ?_ z hz
  intro eta s hs hp
  exact hecke_nonzero_of_probes hprobes eta s hs hp

#print axioms beta_star_le_of_probes
#print axioms hecke_nonzero_of_probes
#print axioms dirichlet_nonzero_of_probes
#print axioms zeta_nonzero_of_probes
end
end RHIVProbe


-- Final assembly adaptation: V2FixedNonfloorClass
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

omit [NeZero M] in
lemma iv_fixed_nonfloorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem iv_fixed_actual_nonfloor_class_from_raw_moments (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤ A)
    (hellsum : ∑j,ell j=RHIVProbe.ell)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hν : 0<ν)
    (hlog : 0< logCost) (hMomentHeight : τ< heightCost) (counts : IVProbeFinalAssembly.CountParameters M H εm) :
    ∃C : ℝ,0< C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v a C0 : ℝ),0≤ v → 51/100< a → a≤1 → 0≤ C0 →
      ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,Z^v≤ rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
      IVProbeHighRowFamily.SourceMomentsAt M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i z RHIVProbe.momentKappa
        (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH)
        (C0*Z^momentCost) (Z^heightCost) εm →
      let Q := physical M H (fun u : FreeRow=> u.val) W (fun _=> b) (fun j=> ell j/d) (fun _=> z) (Z^d)
      ∀bin : BinLabel (Finset.univ : Finset (Fin N)) ((2*a-1)/2) mesh,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) mesh hmesh (fun j=> ell j/d) Q bin
      let q := classMean Finset.univ ((2*a-1)/2) mesh (fun j=> ell j/d) bin
      rows'.Nonempty → 0≤ q ∧ q≤(2*a-1)/2 ∧
      ‖cubeArithmeticSum S hS hmax η rows' T (iv_fixed_nonfloorPoolOutside M H S N c b Y) W Y a e t‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(logCost+heightCost+momentCost+
            d*IVProbeHighRowFamily.adaptiveRowExponent RHIVProbe.momentKappa (2*a-1) q ε εm R ν+
            v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-(RHIVProbe.ell*(4/25))+(RHIVProbe.ell)*q+(RHIVProbe.ell)*mesh) := by
  have hdmax0 : 0< dmax := hdmin.trans_le hdRange
  obtain ⟨K,hK,hcount⟩ :=
    IVProbeFinalAssembly.adaptive_source_count_from_raw_moments M H hH S φ hφ hφc hφp hφ0 hφne
      a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
      (Sum Bool (RayQuotient.Characters M H)) N n dmin dmax τ logCost heightCost momentCost mesh
      hdmin hdmax0 hτ hlog hMomentHeight hmesh counts
  obtain ⟨C,hC,hphysical⟩ := iv_actual_class_cube_arithmetic M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh (1/100) margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh (by norm_num)
    hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro η
  have hbatches := iv_actual_source_amplitude_batches M H hH (IVAdaptiveCutoff.cutoff RHIVProbe.momentKappa)
    (fun delta q hd=> IVAdaptiveCutoff.cutoff_bounds _ delta q RHIVProbe.moment_range.1 hd) S hS hmax η
    dmin dmax τ ε e κ cost margin R mesh n hdmin hdRange hdtop hτ hτzero hτheight
    hε he he1 hκ hκ1 hcost hmargin hR hmesh hwbudget
  filter_upwards [hphysical η,hcount,hbatches,eventually_gt_atTop (1:ℝ)] with Z hphysical hcount hbatch hZ
  intro d hd hd' v a C0 hv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro t ht hmom bin hne
  have hZp : 0< Z := zero_lt_one.trans hZ
  have hd0 : 0< d := hdmin.trans_le hd
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let Q := physical M H (fun u : FreeRow=> u.val) W (fun _=> b) (fun j=> ell j/d) (fun _=> z) (Z^d)
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) mesh hmesh (fun j=> ell j/d) Q bin
  let q := classMean Finset.univ ((2*a-1)/2) mesh (fun j=> ell j/d) bin
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hrowne : rows.Nonempty := hne.mono hsub
  have hband : rows⊆rowBand (Z^(1/100:ℝ)) (2*Z^v+1) := by
    intro u hu
    exact mem_rowBand.mpr ⟨(hrows u hu).1,(hrows u hu).2.1,by linarith [(hnorm u hu).2]⟩
  have hellpos (j : Fin N) : 0< ell j := (mul_pos hdmax0 hrmin).trans_le (hello j)
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW',hUpper,hExternal,hMesh,hBin,hFam,hMean⟩ :=
    hbatch d hd hd' (2*Z^v+1) rows hrowne hband (fun u hu=>(hrows u hu).2.2.1)
      (fun u hu=>(hrows u hu).2.2.2) a i hi ha ha' hnext hcurrent
      N ell hellpos hellhi (by rw [hellsum];iv_high_geometry) W (fun _=> b) (fun _=> z) bin hne
  have hBsub : B.rows⊆rows := hBr ▸ hsub
  have hBfam : ∀u∈B.rows,∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j := by
    intro u hu j
    exact hFam u (hBr ▸ hu) j
  have hraw := hmom q B hBsub hBd hRev hSlots hWidths hW' hUpper hExternal hMesh hBin hBfam
  have hcard := hcount d hd hd' a ε RHIVProbe.momentKappa ν C0 q i hi ha ha' hε.le hε1 RHIVProbe.moment_range.1 RHIVProbe.moment_range.2 hν hC0 B
    (by rw [hSlots];simp) hBin (hBr.symm ▸ hne) hMean hraw
  rw [hBr,hMesh] at hcard
  have hqb := classMean_bounds rows Finset.univ (Z^d) (2*a-1) mesh hmesh (fun j=> ell j/d) Q bin
    (by linarith) (fun j _=> div_nonneg (hellpos j).le hd0.le)
    (by rw [iv_source_slot_length_sum Finset.univ ell d hellsum];exact div_pos RHIVProbe.analytic_geometry.1 hd0) hne
  refine ⟨hqb.1,hqb.2,?_⟩
  have hp := hphysical d hd hd' v a q (K*C0*Z^(logCost+heightCost+momentCost))
    (IVProbeHighRowFamily.adaptiveRowExponent RHIVProbe.momentKappa (2*a-1) q ε εm R ν) hv ha.le ha' (by positivity) rows'
    (fun u hu=> hrows u (hsub hu)) (fun u hu=> hnorm u (hsub hu)) hcard i hi
    (fun u hu=> hnext u (hsub hu)) t ht
    (fun u hu=> source_amplitude_class_mean M H ell W Z d b a mesh z hZp hd0.ne' hmesh rows bin u hu)
  apply hp.trans_eq
  rw [show logCost+heightCost+momentCost+
      d*IVProbeHighRowFamily.adaptiveRowExponent RHIVProbe.momentKappa (2*a-1) q ε εm R ν+
      v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-(RHIVProbe.ell*(4/25))+(RHIVProbe.ell)*q+(RHIVProbe.ell)*mesh=
      (logCost+heightCost+momentCost)+(d*IVProbeHighRowFamily.adaptiveRowExponent RHIVProbe.momentKappa (2*a-1) q ε εm R ν+
      v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-(RHIVProbe.ell*(4/25))+(RHIVProbe.ell)*q+(RHIVProbe.ell)*mesh) by ring,
    Real.rpow_add hZp (logCost+heightCost+momentCost)]
  ring


end

end RHZeroFreeExtension.AnalyticHigh


-- Final assembly adaptation: V2FixedNonfloorArithmetic
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily RHIVProbe
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem iv_fixed_actual_nonfloor_cube_arithmetic (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤ A)
    (hellsum : ∑j,ell j=RHIVProbe.ell)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hΔzero : Δ=0) (hν : 0<ν)
    (hlog : 0< logCost) (hMomentHeight : τ< heightCost)
    (ζ μ saving : ℝ) (hζ : 0≤ζ) (hζ1 : ζ≤1/48) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (RHIVProbe.h)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+(RHIVProbe.ell)*mesh)+(logCost+heightCost+momentCost)+saving≤ HeckeZeroSupremum.beta-RHIVProbe.boundary) (counts : IVProbeFinalAssembly.CountParameters M H εm) :
    ∃C : ℝ,0< C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v a C0 : ℝ),0≤ v → v≤ RHIVProbe.h+ζ → d-v≤μ →
      51/100< a → a≤11/12 → 0≤ C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,Z^v≤ rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      IVProbeHighRowFamily.SourceMomentsAt M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i
        ((17/50:ℂ)+t.1.2*Complex.I) RHIVProbe.momentKappa
        (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH)
        (C0*Z^momentCost) (Z^heightCost) εm →
      ‖cubeArithmeticSum S hS hmax η rows T (iv_fixed_nonfloorPoolOutside M H S N c b Y) W Y a e t‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(RHIVProbe.signalExponent HeckeZeroSupremum.beta-saving-((1-RHIVProbe.y)*a+(4/25)*RHIVProbe.x-33/50+(16-6*RHIVProbe.y)*e)) := by
  obtain ⟨C,hC,hclass⟩ :=
    iv_fixed_actual_nonfloor_class_from_raw_moments M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm Δ ν logCost heightCost momentCost hεm hΔ hΔ1 hν hlog hMomentHeight counts
  let cardCost : ℝ := (HeckeDetectorClassBudget.alphabetBound mesh:ℝ)^N
  have hcardCost : 0≤ cardCost := by dsimp [cardCost];positivity
  refine ⟨(cardCost+1)*C,by positivity,?_⟩
  intro η
  filter_upwards [hclass η,eventually_gt_atTop (1:ℝ)] with Z hclass hZ
  intro d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro t ht hmom
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let Y : Fin N→ℝ := fun j=> Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
  let Q := physical M H (fun u : FreeRow=> u.val) W (fun _=> b) (fun j=> ell j/d) (fun _=> z) (Z^d)
  let bound : ℝ := C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
    Z^(RHIVProbe.signalExponent HeckeZeroSupremum.beta-saving-((1-RHIVProbe.y)*a+(4/25)*RHIVProbe.x-33/50+(16-6*RHIVProbe.y)*e))
  have hb : 0≤ bound := by dsimp [bound];positivity
  have hpart := cubeArithmeticSum_class_uniform S hS hmax η rows T
    (iv_fixed_nonfloorPoolOutside M H S N c b Y) W Y a e t Finset.univ (Z^d) ((2*a-1)/2) mesh hmesh
    (by linarith) (fun j=> ell j/d) Q bound hb (by
      intro bin hne
      have hp := hclass d hd hd' v a C0 hv ha (ha'.trans (by norm_num)) hC0 rows hrows hnorm i hi hnext hcurrent t ht hmom bin hne
      dsimp only at hp
      let q := classMean Finset.univ ((2*a-1)/2) mesh (fun j=> ell j/d) bin
      have hs := RHIVProbe.adaptive_mixed_saving N a q ε εm R ν ζ μ v d e eps loss mesh
        (logCost+heightCost+momentCost) saving HeckeZeroSupremum.beta (by linarith) ha' hp.1 hp.2.1 hε.le hεm.le
        hR hν.le hcount hζ hv' (by
          have hh : RHIVProbe.h+(1/48:ℝ)≤1 := by iv_high_geometry
          linarith only [hh,hv',hζ1]) hμ hdv he.le heps.le hfinal
      have hid := RHIVProbe.central_class_exponent_identity N a v d
        (IVProbeHighRowFamily.adaptiveRowExponent RHIVProbe.momentKappa (2*a-1) q ε εm R ν) q e eps loss mesh (logCost+heightCost+momentCost)
      apply hp.2.2.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      linarith)
  simp only [Finset.card_univ,Fintype.card_fin] at hpart
  calc
    _ ≤ cardCost*bound := hpart
    _ ≤ (cardCost+1)*bound := mul_le_mul_of_nonneg_right (by linarith) hb
    _ = _ := by dsimp [bound];ring


end

end RHZeroFreeExtension.AnalyticHigh


-- Final assembly adaptation: V2FixedNonfloorIntegral
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem iv_fixed_actual_nonfloor_cube_norm (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤ A)
    (hellsum : ∑j,ell j=RHIVProbe.ell)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hΔzero : Δ=0) (hν : 0<ν)
    (hlog : 0< logCost) (hMomentHeight : τ< heightCost)
    (ζ μ saving : ℝ) (hζ : 0≤ζ) (hζ1 : ζ≤1/48) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (RHIVProbe.h)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+(RHIVProbe.ell)*mesh)+(logCost+heightCost+momentCost)+saving≤ HeckeZeroSupremum.beta-RHIVProbe.boundary)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) (counts : IVProbeFinalAssembly.CountParameters M H εm) :
    ∃C : ℝ,0< C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v a C0 : ℝ),0≤ v → v≤ RHIVProbe.h+ζ → d-v≤μ →
      51/100< a → a≤11/12 → 0≤ C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,Z^v≤ rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      IVProbeHighRowFamily.SourceMomentsAt M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i
        ((17/50:ℂ)+t.1.2*Complex.I) RHIVProbe.momentKappa
        (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH)
        (C0*Z^momentCost) (Z^heightCost) εm) →
      ‖finiteCentralCubeRows S hS hmax η rows T (iv_fixed_nonfloorPoolOutside M H S N c b Y) W Y
        W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z e (fun _=> a) (fun _=>(3*i+1:ℕ)*Z^τ)‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(RHIVProbe.signalExponent HeckeZeroSupremum.beta-saving) := by
  obtain ⟨C,hC,harith⟩ :=
    iv_fixed_actual_nonfloor_cube_arithmetic M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm Δ ν logCost heightCost momentCost hεm hΔ hΔ1 hΔzero hν hlog hMomentHeight
      ζ μ saving hζ hζ1 hμ hcount hfinal counts
  obtain ⟨D,hD,hprofile⟩ := actual_common_cube_aggregate_norm W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro η
  filter_upwards [harith η,(tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z harith hT hZ
  intro d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro hmom
  have hZp : 0< Z := zero_lt_one.trans hZ
  let Y : Fin N→ℝ := fun j=> Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
  let A : ℝ := C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
    Z^(RHIVProbe.signalExponent HeckeZeroSupremum.beta-saving-((1-RHIVProbe.y)*a+(4/25)*RHIVProbe.x-33/50+(16-6*RHIVProbe.y)*e))
  have hA : 0≤ A := by dsimp [A];positivity
  have hp := hprofile e a (Z^τ) ((3*i+1:ℕ)*Z^τ) i he he1 ha.le (ha'.trans (by norm_num)) hT
    (by gcongr;omega) S hS hmax hfirst η rows (fun u hu=>(hrows u hu).1)
    T (iv_fixed_nonfloorPoolOutside M H S N c b Y) (rayCubeFamily M H hH) hnext W Y
    (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z (by positivity) (by positivity) hZp A hA
    (fun t ht=> harith d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
      t ht (hmom t ht))
  apply hp.trans_eq
  rw [RHIVProbe.physical_scale_identity Z a e hZp]
  dsimp only [A]
  calc
    _ = (D*C)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
        (Z^((1-RHIVProbe.y)*a+(4/25)*RHIVProbe.x-33/50+(16-6*RHIVProbe.y)*e)*Z^(RHIVProbe.signalExponent HeckeZeroSupremum.beta-saving-((1-RHIVProbe.y)*a+(4/25)*RHIVProbe.x-33/50+(16-6*RHIVProbe.y)*e))) := by ring
    _ = _ := by rw [←Real.rpow_add hZp];congr 2;ring


end

end RHZeroFreeExtension.AnalyticHigh


-- Final assembly adaptation: V2FixedNonfloorNormalized
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem iv_fixed_actual_normalized_nonfloor_cube (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤ W j t ∧ W j t≤ A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=RHIVProbe.ell)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hΔzero : Δ=0) (hν : 0<ν)
    (hlog : 0< logCost) (hMomentHeight : τ< heightCost)
    (ζ μ saving : ℝ) (hζ : 0≤ζ) (hζ1 : ζ≤1/48) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (RHIVProbe.h)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+(RHIVProbe.ell)*mesh)+(logCost+heightCost+momentCost)+saving≤ HeckeZeroSupremum.beta-RHIVProbe.boundary)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0< nu) (counts : IVProbeFinalAssembly.CountParameters M H εm) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0< C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v a C0 : ℝ),0≤ v → v≤ RHIVProbe.h+ζ → d-v≤μ →
      51/100< a → a≤11/12 → 0≤ C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,Z^v≤ rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      IVProbeHighRowFamily.SourceMomentsAt M H hH S hS.prime η rows ell (fun j y=>(W j y:ℂ)) Z d a ε τ dmax b R mesh i
        ((17/50:ℂ)+t.1.2*Complex.I) RHIVProbe.momentKappa
        (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH)
        (C0*Z^momentCost) (Z^heightCost) εm) →
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (RHIVProbe.ell)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (iv_fixed_nonfloorPoolOutside M H S N c b Y) (fun j y=>(W j y:ℂ)) Y
        W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z e (fun _=> a) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(RHIVProbe.signalExponent HeckeZeroSupremum.beta-saving+nu) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWC (j : Fin N) : ContDiff ℝ ∞ (WC j) := Complex.ofRealCLM.contDiff.comp (hW j)
  have hWCs (j : Fin N) : Function.support (WC j)⊆Ioo c b := by
    intro y hy
    apply hWs j
    intro hh
    exact hy (by dsimp [WC];rw [hh];simp)
  have hWCB (j : Fin N) (y : ℝ) : ‖WC j y‖≤ A := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  obtain ⟨C,hC,hbound⟩ :=
    iv_fixed_actual_nonfloor_cube_norm M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi WC hWCs hWC hWCB hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm Δ ν logCost heightCost momentCost hεm hΔ hΔ1 hΔzero hν hlog hMomentHeight
      ζ μ saving hζ hζ1 hμ hcount hfinal
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 counts
  have hellpos (j : Fin N) : 0< ell j :=
    (mul_pos (hdmin.trans_le hdRange) hrmin).trans_le (hello j)
  obtain ⟨Cn,hCn,hnormer⟩ := iv_actual_ray_normalizer_inverse M H hH S hS c b hc hcb ell hellpos hellsum
    W hW hcompact hWs (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  refine ⟨C*Cn,mul_pos hC hCn,?_⟩
  intro η
  filter_upwards [hbound η,hnormer,eventually_gt_atTop (0:ℝ)] with Z hb hn hZ
  intro d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only at hn ⊢
  intro hmom
  refine ⟨hn.1,?_⟩
  have hh := hb d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent hmom
  rw [div_eq_mul_inv,norm_mul]
  have hm := mul_le_mul hh hn.2 (norm_nonneg _) (by positivity)
  apply hm.trans_eq
  rw [Real.rpow_add hZ (RHIVProbe.signalExponent HeckeZeroSupremum.beta-saving) nu]
  ring


end

end RHZeroFreeExtension.AnalyticHigh


-- Final assembly adaptation: V2FixedNonfloorCollected
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem iv_fixed_actual_nonfloor_rows_saving (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤ W j t ∧ W j t≤ A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=RHIVProbe.ell)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hΔzero : Δ=0) (hν : 0<ν)
    (hlog : 0< logCost) (hMomentHeight : τ< heightCost)
    (ζ μ saving : ℝ) (hζ : 0≤ζ) (hζ1 : ζ≤1/48) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (RHIVProbe.h)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+(RHIVProbe.ell)*mesh)+(logCost+heightCost+momentCost)+saving≤ HeckeZeroSupremum.beta-RHIVProbe.boundary)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0< nu)
    (m : ℕ) (dyadCost : ℝ) (hdyadCost : 0< dyadCost)
    (hdmin1 : dmin<1/100) (hconductor : RHIVProbe.h+ζ+2*margin≤ dmax)
    (hmuMargin : 2*margin≤μ) (counts : IVProbeFinalAssembly.CountParameters M H εm) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0< C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,∀C0 : ℝ,0≤ C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(RHIVProbe.h+ζ)) →
      ∀idx grid : FreeRow→ℕ,
      (∀u∈rows,idx u≤ n ∧ grid u≤ m ∧ grid u≠0 ∧ 51/100+e*grid u≤11/12) →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(idx u+1:ℕ)*Z^τ)<51/100+e*grid u+2*e) →
      (∀u∈rows,51/100+e*grid u≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*idx u:ℕ)*Z^τ)) →
      (∀k∈smallDyadicIndices (Z^(RHIVProbe.h+ζ)),∀i∈Finset.range (n+1),∀j∈Finset.range (m+1),
        let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
        rows'.Nonempty → ∀t : HeightSpace,
        ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
        IVProbeHighRowFamily.SourceMomentsAt M H hH S hS.prime η rows' ell (fun j y=>(W j y:ℂ)) Z
          (sourceDyadConductor Z margin k) (51/100+e*j) ε τ dmax b R mesh i
          ((17/50:ℂ)+t.1.2*Complex.I) RHIVProbe.momentKappa
          (if 2*(51/100+e*j)-1≤5/6 then counts.cB else counts.cH)
          (if 2*(51/100+e*j)-1≤5/6 then counts.kB else counts.kH)
          (C0*Z^momentCost) (Z^heightCost) εm) →
      let Y : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (RHIVProbe.ell)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (iv_fixed_nonfloorPoolOutside M H S N c b Y)
        (fun j y=>(W j y:ℂ)) Y W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z e
        (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(RHIVProbe.signalExponent HeckeZeroSupremum.beta-saving+nu+dyadCost) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ :=
    iv_fixed_actual_normalized_nonfloor_cube M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm Δ ν logCost heightCost momentCost hεm hΔ hΔ1 hΔzero hν hlog hMomentHeight
      ζ μ saving hζ hζ1 hμ hcount hfinal W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      hr0 hr1 hp0 hp1 hn0 hn1 nu hnu counts
  have hellpos (j : Fin N) : 0< ell j := (mul_pos (hdmin.trans_le hdRange) hrmin).trans_le (hello j)
  obtain ⟨Cn,hCn,hnormer⟩ := iv_actual_ray_normalizer_inverse M H hH S hS c b hc hcb ell hellpos hellsum
    W hW hcompact hWs (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  obtain ⟨Cd,hCd,hdyad⟩ := canonical_dyad_cost dyadCost hdyadCost
  refine ⟨Cd*(n+1:ℕ)*(m+1:ℕ)*C,by positivity,?_⟩
  intro η
  filter_upwards [hbound η,hnormer,
    sourceDyad_geometry_eventually dmin dmax margin (RHIVProbe.h+ζ) hdmin hdmin1 hmargin hconductor,
    eventually_gt_atTop (1:ℝ)] with Z hb hn hg hZ
  intro C0 hC0 rows hrows idx grid hlabels hnext hcurrent hmom
  dsimp only at hn ⊢
  refine ⟨hn.1,?_⟩
  have hZp : 0< Z := zero_lt_one.trans hZ
  let Y : Fin N→ℝ := fun j=> Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
  let hT := iv_fixed_nonfloorPoolOutside M H S N c b Y
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
    (Probe.principalScalar Finset.univ Z (RHIVProbe.ell)
      (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
  let D : ℝ := C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(RHIVProbe.signalExponent HeckeZeroSupremum.beta-saving+nu)
  have hD : 0≤ D := by dsimp [D];positivity
  let F : Finset FreeRow→(FreeRow→ℝ)→(FreeRow→ℝ)→ℂ := fun R a H=>
    finiteCentralCubeRows S hS hmax η R T hT WC Y W0 W1
      (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z e a H
  have hcell (k : ℕ) (hk : k∈smallDyadicIndices (Z^(RHIVProbe.h+ζ)))
      (i : ℕ) (hi : i∈Finset.range (n+1)) (j : ℕ) (hj : j∈Finset.range (m+1)) :
      ‖F (cubeBinRows (rows∩dyadicRows 1 k) idx grid i j)
        (fun _=>51/100+e*j) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤ D := by
    let Rk := rows∩dyadicRows 1 k
    let Rij := cubeBinRows Rk idx grid i j
    have hsubk : Rij⊆Rk := Finset.filter_subset _ _
    have hsub : Rij⊆rows := hsubk.trans Finset.inter_subset_left
    by_cases hne' : Rij.Nonempty
    · have hgeo := hg rows (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.1,(hrows u hu).2.2.2⟩) k
        (hne'.mono hsubk)
      obtain ⟨u,hu⟩ := hne'
      have huj : grid u=j := ((mem_cubeBinRows Rk idx grid i j u).mp hu).2.2
      have hju : j≠0 := huj ▸ (hlabels u (hsub hu)).2.2.1
      have ha : 51/100<51/100+e*j := by
        have hjp : (0:ℝ)< j := by exact_mod_cast Nat.pos_of_ne_zero hju
        nlinarith
      have ha' : 51/100+e*j≤11/12 := by simpa only [huj] using (hlabels u (hsub hu)).2.2.2
      have hnext' : ∀u∈Rij,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          (3*(i+1:ℕ)*Z^τ)<51/100+e*j+2*e := by
        intro u hu
        have hh := hnext u (hsub hu)
        have hm := (mem_cubeBinRows Rk idx grid i j u).mp hu
        rwa [hm.2.1,hm.2.2] at hh
      have hcurrent' : ∀u∈Rij,51/100+e*j≤ detectorMaximum
          (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^τ) := by
        intro u hu
        have hh := hcurrent u (hsub hu)
        have hm := (mem_cubeBinRows Rk idx grid i j u).mp hu
        rwa [hm.2.1,hm.2.2] at hh
      have hbounded := hb (sourceDyadConductor Z margin k) hgeo.2.2.1 hgeo.2.2.2.1
        (sourceDyadExponent Z k) (51/100+e*j) C0 hgeo.1 hgeo.2.1
        (by unfold sourceDyadConductor;linarith) ha ha' hC0 Rij
        (fun u hu=>⟨(hrows u (hsub hu)).1,(hrows u (hsub hu)).2.1,
          (hrows u (hsub hu)).2.2.1,hgeo.2.2.2.2.2 u (hsubk hu)⟩)
        (fun u hu=> hgeo.2.2.2.2.1 u (hsubk hu)) i (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        hnext' hcurrent' (fun t ht=> hmom k hk i hi j hj ⟨u,hu⟩ t ht)
      exact hbounded.2
    · have he : Rij=∅ := Finset.not_nonempty_iff_eq_empty.mp hne'
      simpa only [F,show cubeBinRows (rows∩dyadicRows 1 k) idx grid i j=∅ from he,
        finiteCentralCubeRows,Finset.sum_empty,zero_div,norm_zero] using hD
  have hpartition : F rows (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)=
      ∑k∈smallDyadicIndices (Z^(RHIVProbe.h+ζ)),
        F (rows∩dyadicRows 1 k) (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ) := by
    unfold F finiteCentralCubeRows
    exact retained_dyadic_sum rows _ (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.2.2⟩) _
  change ‖F rows (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤_
  rw [hpartition,Finset.sum_div]
  calc
    _ ≤ ∑k∈smallDyadicIndices (Z^(RHIVProbe.h+ζ)),(n+1:ℕ)*(m+1:ℕ)*D := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      have hpart := finiteCentralCubeRows_bin_partition S hS hmax η (rows∩dyadicRows 1 k) T hT WC Y
        W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z e (Z^τ) idx grid n m
        (fun u hu=>⟨(hlabels u (Finset.mem_inter.mp hu).1).1,(hlabels u (Finset.mem_inter.mp hu).1).2.1⟩)
      change ‖F (rows∩dyadicRows 1 k) (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤_
      dsimp only [F]
      rw [hpart,Finset.sum_div]
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑i∈Finset.range (n+1),∑j∈Finset.range (m+1),D := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.sum_div]
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j hj=> hcell k hk i hi j hj))
        _ = _ := by simp;ring
    _ = ((smallDyadicIndices (Z^(RHIVProbe.h+ζ))).card:ℝ)*((n+1:ℕ)*(m+1:ℕ)*D) := by simp
    _ ≤ (Cd*Z^dyadCost)*((n+1:ℕ)*(m+1:ℕ)*D) :=
      mul_le_mul_of_nonneg_right (hdyad Z (RHIVProbe.h+ζ) hZ.le (by linarith)) (by positivity)
    _ = _ := by dsimp [D];rw [Real.rpow_add hZp (RHIVProbe.signalExponent HeckeZeroSupremum.beta-saving+nu) dyadCost];ring


end

end RHZeroFreeExtension.AnalyticHigh


-- Final assembly adaptation: V2FinalAssemblyHigh
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

private lemma iv_zero_bin_upper (chi : Character) (a : ℝ) (s : ℂ)
    (ha : 0< a) (hz : LFunction chi s=0)
    (hp : ¬(chi.residue=1 ∧ s=1)) (has : a≤ s.re) : a≤11/12 := by
  have hpole : s≠1 ∨ chi.residue≠1 := by
    by_cases hs : s=1
    · exact Or.inr (fun hc=> hp ⟨hc,hs⟩)
    · exact Or.inl hs
  have hb := HeckeZeroSupremum.zero_re_le_beta chi (ha.trans_le has) hpole hz
  have hOld := RHZeroFreeExtension.ActualOriginalBoundary.beta_le_seven_eighths
  linarith

theorem iv_fixed_actual_high_probe_from_raw_moments (N : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤ W j t ∧ W j t≤ A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=RHIVProbe.ell)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hν : 0<ν)
    (hlog : 0< logCost) (hMomentHeight : τ< heightCost)
    (ζ μ saving : ℝ) (hζ : 0<ζ) (hζ1 : ζ≤1/48) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (RHIVProbe.h)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+(RHIVProbe.ell)*mesh)+(logCost+heightCost+momentCost)+saving≤ HeckeZeroSupremum.beta-RHIVProbe.boundary)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0< nu)
    (dyadCost : ℝ) (hdyadCost : 0< dyadCost)
    (hdmin1 : dmin<1/100) (hconductor : RHIVProbe.h+ζ+2*margin≤ dmax)
    (hmuMargin : 2*margin≤μ)
    (hβ : (RHIVProbe.boundary:ℝ)≤ HeckeZeroSupremum.beta)
    (sigma : ℝ) (hsigma : 0< sigma)
    (hgeometric : sigma+8*e+nu≤ RHIVProbe.smallSaving) (hprincipal : sigma+nu≤1/3000)
    (hwindow : sigma+e≤(RHIVProbe.boundary)*(dmax*rmin))
    (hfloorbudget : 2*ζ+26*e+(N+8)*eps+loss+(RHIVProbe.ell)*mesh+nu+sigma≤1/200)
    (hcentral : sigma+nu+dyadCost≤ saving) (counts : IVProbeFinalAssembly.CountParameters M H εm) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0< n ∧ ∃C : ℝ,
      0< C ∧
    ∀η : Character,∃Ct : ℝ,0< Ct ∧ ∀ᶠZ : ℝ in atTop,
      let Yp := fun j=> Z^(ell j)
      let T := fun j=> pool (RayQuotient.identityClass M H) S c b (Yp j)
      let _hT := iv_fixed_nonfloorPoolOutside M H S N c b Yp
      let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (RHIVProbe.ell) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤ a ∧ a≤1 ∧
        a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ)< a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ)< a+2*e ∧
        (51/100< a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a≤ s.re ∧ s.re< a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((RHIVProbe.h:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let rows := supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((RHIVProbe.h:ℝ)+ζ))) grid
      ∀C0 : ℝ,0≤ C0 →
      (∀k∈smallDyadicIndices (Z^(RHIVProbe.h+ζ)),∀i∈Finset.range (n+1),∀j∈Finset.range (⌊(49/100:ℝ)/e⌋₊+1),
        let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
        rows'.Nonempty → ∀t : HeightSpace,
        ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
        IVProbeHighRowFamily.SourceMomentsAt M H hH S hS.prime η rows' ell WC Z
          (sourceDyadConductor Z margin k) (51/100+e*j) ε τ dmax b R mesh i
          ((17/50:ℂ)+t.1.2*Complex.I) RHIVProbe.momentKappa
          (if 2*(51/100+e*j)-1≤5/6 then counts.cB else counts.cH)
          (if 2*(51/100+e*j)-1≤5/6 then counts.kB else counts.kH)
          (C0*Z^momentCost) (Z^heightCost) εm) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=> canonicalSlotSupport (T j)) WC Yp (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-(4+RHIVProbe.b)/6) Z‖≤
        (Ct+C*C0*(η.modulus.absNorm:ℝ)^(2*eps))*Z^(RHIVProbe.signalExponent HeckeZeroSupremum.beta-sigma) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hmin : 0< dmax*rmin := mul_pos (hdmin.trans_le hdRange) hrmin
  obtain ⟨n,hn,htransport⟩ := iv_actual_nonfloor_probe_transport M H hH N e (1/4) c b A ζ 1 τ (dmax*rmin) nu
    he he1 (by norm_num) (by norm_num) hζ hζ1 hτ hc hcb hA hmin hnu hβ S hS hmax hfirst
    ell hello hell hellsum W hW hcompact hWs hWB hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 sigma hsigma hgeometric hprincipal hwindow (by linarith only [hprincipal,RHIVProbe.analytic_geometry.2.2.2.2.2.1])
    eps R dmin dmax rmin ε κ cost mesh margin loss heps hR hdmin hdmax hdRange hrmin hε hκ hcost hmesh hmargin
    hbudget hgap hheight hloss (by linarith) hello hellhi hfloorbudget
  obtain ⟨C,hC,hbound⟩ :=
    iv_fixed_actual_nonfloor_rows_saving M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm (0:ℝ) ν logCost heightCost momentCost hεm (by norm_num) (by norm_num) (by norm_num) hν hlog hMomentHeight
      ζ μ saving hζ.le (by linarith) hμ hcount hfinal W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      hr0 hr1 hp0 hp1 hn0 hn1 nu hnu ⌊(49/100:ℝ)/e⌋₊ dyadCost hdyadCost hdmin1 hconductor hmuMargin counts
  refine ⟨n,hn,C,hC,?_⟩
  intro η
  obtain ⟨Ct,hCt,htransport⟩ := htransport η
  refine ⟨Ct,hCt,?_⟩
  filter_upwards [htransport,hbound η,eventually_ge_atTop (1:ℝ)] with Z ht hb hZ
  dsimp only at ht ⊢
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,herror⟩ := ht
  refine ⟨hnorm,idx,grid,hlabels,hbins,hray,?_⟩
  intro C0 hC0 hmom
  let rows := supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((RHIVProbe.h:ℝ)+ζ))) grid
  have hrows : ∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
      (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(RHIVProbe.h+ζ) := by
    intro u hu
    rcases (mem_supportedNonfloorRows S hmax _ grid u).mp hu with ⟨hur,hcal,hg⟩
    have hh := mem_rowBand.mp hur
    exact ⟨hh.1,hh.2.1,hcal,hh.2.2.le⟩
  have hlabel : ∀u∈rows,idx u≤ n ∧ grid u≤⌊(49/100:ℝ)/e⌋₊ ∧ grid u≠0 ∧ 51/100+e*grid u≤11/12 := by
    intro u hu
    have hg : grid u≠0 := ((mem_supportedNonfloorRows S hmax _ grid u).mp hu).2.2
    have ha : 51/100<51/100+e*grid u := by
      have hgpos : (0:ℝ)< grid u := by exact_mod_cast Nat.pos_of_ne_zero hg
      nlinarith only [he,hgpos]
    obtain ⟨j,s,hz,hp,has,_⟩ := (hbins u).2.2.2.2.2 ha
    exact ⟨(hlabels u).2.1,(hlabels u).2.2.1,hg,
      iv_zero_bin_upper _ _ s (by linarith only [ha]) hz hp has⟩
  have hnext : ∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
      (3*(idx u+1:ℕ)*Z^τ)<51/100+e*grid u+2*e := fun u _=>(hbins u).2.2.2.2.1
  have hcurrent : ∀u∈rows,51/100+e*grid u≤ detectorMaximum
      (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*idx u:ℕ)*Z^τ) := by
    intro u hu
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using (hbins u).2.2.1
  have hglobal := (hb C0 hC0 rows hrows idx grid hlabel hnext hcurrent hmom).2
  have hexp : Z^(RHIVProbe.signalExponent HeckeZeroSupremum.beta-saving+nu+dyadCost)≤
      Z^(RHIVProbe.signalExponent HeckeZeroSupremum.beta-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hcentral' := hglobal.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  have hsum := (norm_add_le _ _).trans (add_le_add herror hcentral')
  simpa only [rows,sub_add_cancel,add_mul] using hsum


end

end RHZeroFreeExtension.AnalyticHigh


-- Final assembly adaptation: V2FinalMomentInput


noncomputable section
open scoped Classical BigOperators
open Filter
namespace RHZeroFreeExtension.AnalyticHigh.IV
open OAI.SevenEighths.IVProbeFinalAssembly
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
open HeckeInverseAmplification

def RawMomentInput : Prop :=
   ∀ _hβ : (RHIVProbe.boundary:ℝ) < HeckeZeroSupremum.beta,
     ∀ D : HighData (HeckeZeroSupremum.beta-RHIVProbe.boundary), ∀ F : SourceData D,
     ∀ counts : CountParameters F.modulus ⊤ D.t,
     ∃ J : ℝ,0 ≤ J  ∧   ∀ η : Character, ∃ C : ℝ,0 < C  ∧ 
       ∀ τ : ℝ,0 < τ  →  τ ≤ 1  →   ∀ᶠ Z : ℝ in atTop,
        AdaptiveSourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))

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

theorem raw_input_chosen_height (h : RawMomentInput) (hβ : (RHIVProbe.boundary:ℝ) < HeckeZeroSupremum.beta)
    (D : HighData (HeckeZeroSupremum.beta-RHIVProbe.boundary)) (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t) :
     ∃ τ : ℝ,0 < τ  ∧  τ < (1/200:ℝ)/2  ∧  4*τ < (1/200:ℝ)*D.cost  ∧  τ < D.t  ∧ 
      2*τ ≤ D.t  ∧  τ*(2+4*D.eps) < D.t  ∧ 
       ∀ η : Character, ∃ C : ℝ,0 < C  ∧   ∀ᶠ Z : ℝ in atTop,
        AdaptiveSourceMomentBound F counts η Z τ (C*Z^D.t) (Z^(2*τ)) := by
  obtain ⟨J,hJ,hbound⟩ := h hβ D F counts
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτJ,hτeps⟩ := D.height_choice J hJ
  have htau1 : τ ≤ 1 := by linarith
  refine ⟨τ,hτ,hτd,hτcost,hτt,by nlinarith,hτeps,?_⟩
  intro η
  obtain ⟨C,hC,hbound⟩ := hbound η
  refine ⟨C*2^J,by positivity,?_⟩
  filter_upwards [hbound τ hτ htau1,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  exact hb.mono_constant (by linarith) (polynomial_height_absorption C Z τ J D.t hC.le hZ hτ.le hJ hτJ)

def ChosenMomentInput : Prop :=
  ∀ _hβ : RHIVProbe.boundary < HeckeZeroSupremum.beta,
    ∃ D : HighData (HeckeZeroSupremum.beta-RHIVProbe.boundary), ∃ F : SourceData D,
    ∃ counts : CountParameters F.modulus ⊤ D.t,
    ∃ J : ℝ, 0 ≤ J ∧ ∀ η : Character, ∃ C : ℝ, 0 < C ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ᶠ Z : ℝ in atTop,
        AdaptiveSourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))

def FineMomentInput : Prop :=
  ∀ _hβ : RHIVProbe.boundary < HeckeZeroSupremum.beta,
    ∃ mesh : ℝ → ℝ, (∀ t : ℝ, 0 < t → 0 < mesh t) ∧
      ∀ D : HighData (HeckeZeroSupremum.beta-RHIVProbe.boundary),
      (∀ j, D.ell j ≤ mesh D.t/200) →
      ∀ F : SourceData D, ∀ counts : CountParameters F.modulus ⊤ D.t,
      ∃ J : ℝ, 0 ≤ J ∧ ∀ η : Character, ∃ C : ℝ, 0 < C ∧
        ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ᶠ Z : ℝ in atTop,
          AdaptiveSourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))

theorem chosen_input_of_fine (h : FineMomentInput) : ChosenMomentInput := by
  intro hβ
  obtain ⟨mesh,hmesh,hmom⟩ := h hβ
  obtain ⟨D,hD⟩ := exists_high_data_fine (HeckeZeroSupremum.beta-RHIVProbe.boundary) (by linarith) mesh hmesh
  obtain ⟨F⟩ := exists_source_data D
  obtain ⟨counts⟩ := SourceData.full_count_parameters F
  exact ⟨D,F,counts,hmom D hD F counts⟩

end RHZeroFreeExtension.AnalyticHigh.IV

end


#print axioms RHZeroFreeExtension.AnalyticHigh.IV.raw_input_chosen_height


-- Final assembly adaptation: V2FinalFixedHigh


noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace RHZeroFreeExtension.AnalyticHigh.IV
open OAI.SevenEighths.IVProbeFinalAssembly
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison
open HeckeInverseAmplification HeckeDetectorPhysicalSelection HeckeDetectorFiberPartition
open ProbeMellinBoundary

theorem fixed_high_bound (hβ : (RHIVProbe.boundary:ℝ) < HeckeZeroSupremum.beta)
    (D : HighData (HeckeZeroSupremum.beta-RHIVProbe.boundary)) (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t) (τ : ℝ)
    (hτ : 0 < τ) (hτd : τ < (1/200:ℝ)/2) (hτcost : 4*τ < (1/200:ℝ)*D.cost)
    (hτt : τ < D.t) (hτ2 : 2*τ ≤ D.t) (hτeps : τ*(2+4*D.eps) < D.t) :
     ∃ C : ℝ,0 < C  ∧   ∀ η : Character, ∃ Ct : ℝ,0 < Ct  ∧   ∀ᶠ Z : ℝ in atTop,
       ∀ C0 : ℝ,0 ≤ C0  →  AdaptiveSourceMomentBound F counts η Z τ (C0*Z^D.t) (Z^(2*τ))  → 
      ‖F.probe η Z-HeckeSignal.signal (η.excludePrimes F.S F.exclusions.prime)
        (sourceCorrection η F.S) (-(4+RHIVProbe.b)/6) Z‖ ≤ 
        (Ct+C*C0*(η.modulus.absNorm:ℝ)^(2*D.eps))*Z^(RHIVProbe.signalExponent HeckeZeroSupremum.beta-D.sigma) := by
  let : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  have ht := D.t_pos
  have ht1 := D.t_small
  have hconductor : (RHIVProbe.h:ℝ)+D.t+2*D.t ≤ 7/8 := by
    have hh : RHIVProbe.h ≤ 5/6 := by iv_high_geometry
    linarith
  obtain ⟨n,hn,C,hC,hbound⟩ := iv_fixed_actual_high_probe_from_raw_moments F.modulus ⊤ le_top D.N
    D.e D.eps 1 2 1 D.t (1/200) (7/8) D.rmin τ D.ε D.κ D.cost D.t D.t D.t
    D.e_pos D.e_small D.eps_pos (by norm_num) (by norm_num) (by norm_num)
    ht.le (by norm_num) (by norm_num) (by norm_num) D.rmin_pos hτ D.epsilon_pos D.kappa_pos
    D.cost_pos.le ht D.phase_budget D.epsilon_gap ht (by linarith) hτeps
    F.S F.exclusions F.first F.maximal D.ell D.slots_injective
    (fun j=>(D.slots_bounds j).2.1) (fun j=>(D.slots_bounds j).2.2)
    (fun _=> F.w) (fun _=> F.support) (fun _=> F.smooth) (fun _=> F.bounded)
    (fun _=> F.compact) (fun _=> F.nonzero) D.slots_sum
    (by norm_num) D.epsilon_small D.kappa_small hτd hτcost (by linarith only [D.detector_budget])
    F.w F.smooth F.compact F.positive_support (fun y=>(F.bounded y).1) F.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num) F.support (fun y=>(F.bounded y).2)
    D.t D.t D.t (2*τ) D.t ht ht ht (by linarith)
    D.t (2*D.t) D.t ht (by linarith) (by positivity) D.count_budget (by linarith only [D.central_budget,hτ2,hβ])
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    (D.t/8) (by positivity) (D.t/8) (by positivity) (by norm_num) hconductor (by linarith) hβ.le
    D.sigma D.sigma_pos (D.geometric_budget.trans RHIVProbe.smallSaving_lower) D.principal_budget D.window_budget D.floor_budget D.high_saving counts
  refine ⟨C,hC,?_⟩
  intro η
  obtain ⟨Ct,hCt,hb⟩ := hbound η
  refine ⟨Ct,hCt,?_⟩
  filter_upwards [hb,sourceDyad_geometry_eventually (1/200) (7/8) D.t (RHIVProbe.h+D.t)
    (by norm_num) (by norm_num) ht hconductor,
    HeckeDyadic.constant_absorbed_eventually (3*(n:ℝ)+1) τ hτ,
    eventually_gt_atTop (1:ℝ)] with Z hb hgeo hnheight hZ
  intro C0 hC0 hmom
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,hestimate⟩ := hb
  apply hestimate C0 hC0
  intro k hk i hi j hj
  dsimp only
  intro hne t htheight
  let rows := supportedNonfloorRows F.S F.maximal (rowBand (Z^(1/100:ℝ)) (Z^((RHIVProbe.h:ℝ)+D.t))) grid
  let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
  have hsub : rows'⊆rows∩dyadicRows 1 k := Finset.filter_subset _ _
  have hsubr : rows'⊆rows := hsub.trans Finset.inter_subset_left
  have hrows :  ∀ u∈rows,u.val≠1  ∧  Z^(1/100:ℝ) ≤ rowNorm u  ∧  rowNorm u ≤ Z^(RHIVProbe.h+D.t) := by
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

end RHZeroFreeExtension.AnalyticHigh.IV

end


#print axioms RHZeroFreeExtension.AnalyticHigh.IV.fixed_high_bound


-- Final assembly adaptation: V2FinalChosenData


noncomputable section
open scoped Classical
open Filter

namespace RHZeroFreeExtension.AnalyticHigh.IV
open OAI.SevenEighths.IVProbeFinalAssembly
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison

theorem chosen_data_height {Δ:ℝ}(D:HighData Δ)(F:SourceData D)
    (counts:CountParameters F.modulus ⊤ D.t)(J:ℝ)(hJ:0 ≤ J)
    (hbound: ∀ η:Character, ∃ C:ℝ,0 < C  ∧ 
       ∀ τ:ℝ,0 < τ → τ ≤ 1 →  ∀ᶠ Z:ℝ in atTop,
        AdaptiveSourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))):
     ∃ τ:ℝ,0 < τ  ∧  τ < (1/200:ℝ)/2  ∧  4*τ < (1/200)*D.cost  ∧  τ < D.t  ∧ 
      2*τ ≤ D.t  ∧  τ*(2+4*D.eps) < D.t  ∧ 
       ∀ η:Character, ∃ C:ℝ,0 < C  ∧   ∀ᶠ Z:ℝ in atTop,
        AdaptiveSourceMomentBound F counts η Z τ (C*Z^D.t) (Z^(2*τ)):=by
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτJ,hτeps⟩:=D.height_choice J hJ
  have htau1:τ ≤ 1:=by linarith
  refine ⟨τ,hτ,hτd,hτcost,hτt,by nlinarith,hτeps,?_⟩
  intro η
  obtain ⟨C,hC,hbound⟩:=hbound η
  refine ⟨C*2^J,by positivity,?_⟩
  filter_upwards [hbound τ hτ htau1,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  exact hb.mono_constant (by linarith)
    (polynomial_height_absorption C Z τ J D.t hC.le hZ hτ.le hJ (by linarith))

theorem physical_probe_estimates_of_chosen_moments (hmom : ChosenMomentInput) :
    RHIVProbe.PhysicalProbeEstimates := by
  intro hβ
  obtain ⟨D,F,counts,J,hJ,hmom⟩ := hmom hβ
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτ2,hτeps,hsource⟩ := chosen_data_height D F counts J hJ hmom
  obtain ⟨C,hC,hhigh⟩ := fixed_high_bound hβ D F counts τ hτ hτd hτcost hτt hτ2 hτeps
  let loss := (HeckeZeroSupremum.beta-RHIVProbe.boundary)/2
  have hloss : 0 < loss := by dsimp [loss];linarith
  have hlossgap : loss < HeckeZeroSupremum.beta-RHIVProbe.boundary := by dsimp [loss];linarith
  refine ⟨loss,D.sigma,hloss,hlossgap,D.sigma_pos,?_⟩
  intro η _hprimitive
  obtain ⟨hmask,_hOldAnalytic,_hOldBound⟩ :=
    ProbeFinalAssembly.actual_source_analytic F.S F.exclusions η
  refine ⟨η.excludePrimes F.S F.exclusions.prime,sourceCorrection η F.S,F.probe η,
    (-(4+RHIVProbe.b)/6),hmask,?_,?_,?_,?_⟩
  · exact RHIVProbe.source_analytic F.S F.exclusions η
  · exact RHIVProbe.source_contraction F.S F.exclusions η
  · have hexp : (RHIVProbe.boundary : ℝ)+(-(4+RHIVProbe.b)/6)=RHIVProbe.lowExponent := by rw [RHIVProbe.lowExponent_signal];ring
    simpa only [hexp] using F.probe_low loss hloss η
  · obtain ⟨Ct,hCt,hhigh⟩ := hhigh η
    obtain ⟨Cm,hCm,hsource⟩ := hsource η
    apply isBigO_rpow_of_eventual_norm_bound
    refine ⟨Ct+C*Cm*(η.modulus.absNorm:ℝ)^(2*D.eps),by positivity,?_⟩
    filter_upwards [hhigh,hsource] with Z hh hs
    simpa only [RHIVProbe.signalExponent, sub_eq_add_neg, neg_div] using hh Cm hCm.le hs

theorem beta_le_of_chosen_moments (hmom : ChosenMomentInput) :
    HeckeZeroSupremum.beta ≤ RHIVProbe.boundary :=
  RHIVProbe.beta_star_le_of_probes (physical_probe_estimates_of_chosen_moments hmom)

theorem beta_le_of_fine_moments (hmom : FineMomentInput) :
    HeckeZeroSupremum.beta ≤ (RHIVProbe.boundary:ℝ) :=
  beta_le_of_chosen_moments (chosen_input_of_fine hmom)

end RHZeroFreeExtension.AnalyticHigh.IV
end
#print axioms RHZeroFreeExtension.AnalyticHigh.IV.physical_probe_estimates_of_chosen_moments
#print axioms RHZeroFreeExtension.AnalyticHigh.IV.beta_le_of_fine_moments

namespace RHZeroFreeExtension.AnalyticHigh.IV
/-- Assembly keeps the original headline only as an input needed to construct
the finite-kappa moment family; it is not the improved conclusion. -/
theorem beta_le_of_original_headline_and_fine_moment_construction
    (hOld : OAI.SevenEighths.HeckeZeroSupremum.beta ≤ (7/8 : ℝ))
    (hconstruct : OAI.SevenEighths.HeckeZeroSupremum.beta ≤ (7/8 : ℝ) → FineMomentInput) :
    OAI.SevenEighths.HeckeZeroSupremum.beta ≤ (RHIVProbe.boundary : ℝ) :=
  beta_le_of_fine_moments (hconstruct hOld)
end RHZeroFreeExtension.AnalyticHigh.IV

namespace RHZeroFreeExtension.AnalyticHigh.IV
open OAI.SevenEighths
/-- The extended physical induction constructs the fine moment input for every
preceding supremum bound allowed by the moment parameter. -/
theorem fine_moment_input_of_previous_bound
    (hOld : HeckeZeroSupremum.beta ≤ (1+RHIVProbe.momentKappa)/2) : FineMomentInput := by
  intro hBeta
  have hgap : 0< HeckeZeroSupremum.beta-RHIVProbe.boundary := sub_pos.mpr hBeta
  refine ⟨fun t=> IVProbeFinalAssemblyCertifiedBands.detectorMesh
    (HeckeZeroSupremum.beta-RHIVProbe.boundary) t,?_,?_⟩
  · intro t ht
    exact IVProbeFinalAssemblyCertifiedBands.detectorMesh_pos hgap ht
  · intro D hfine F counts
    exact actual_source_moments hgap F counts hOld
      (by
        have hb : (51/100:ℝ)< RHIVProbe.boundary := by iv_high_geometry
        linarith) hfine

/-- Actual physical probes, with no assumed row count or moment estimate. -/
theorem physical_probe_estimates_of_previous_bound
    (hOld : HeckeZeroSupremum.beta ≤ (1+RHIVProbe.momentKappa)/2) :
    RHIVProbe.PhysicalProbeEstimates :=
  physical_probe_estimates_of_chosen_moments
    (chosen_input_of_fine (fine_moment_input_of_previous_bound hOld))

/-- Analytic one-step improvement at every certified scalar geometry. -/
theorem beta_le_of_previous_bound
    (hOld : HeckeZeroSupremum.beta ≤ (1+RHIVProbe.momentKappa)/2) :
    HeckeZeroSupremum.beta ≤ RHIVProbe.boundary :=
  RHIVProbe.beta_star_le_of_probes (physical_probe_estimates_of_previous_bound hOld)
end RHZeroFreeExtension.AnalyticHigh.IV
#print axioms RHZeroFreeExtension.AnalyticHigh.IV.beta_le_of_previous_bound

end

end PartIVBlock9

/- BEGIN consolidated probe/EndpointGeometryActual.lean -/
section PartIVBlock10
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false



set_option warn.classDefReducibility false
set_option linter.unnecessarySeqFocus false
namespace CombineV22.EndpointGeometry
noncomputable section
open CombineV22.Uniform
lemma b_lower (t : ℝ) (ht : InInterval t) : (123/1000 : ℝ) < b t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hp : 0 < (((-25107 / 200) + ((-129786 / 125) * (t ^ 2)) + ((29358 / 125) * (t ^ 3)) + ((69107 / 100) * t)) : ℝ) := by
    have hid : (((-25107 / 200) + ((-129786 / 125) * (t ^ 2)) + ((29358 / 125) * (t ^ 3)) + ((69107 / 100) * t)) : ℝ) = (341699155501941 / 125000000000000000) + ((70705853398591 / 25000000000000000) * z ^ 0 * (1-z) ^ 3) + ((1048767245679001 / 125000000000000000) * z ^ 1 * (1-z) ^ 2) + ((1036937134158629 / 125000000000000000) * z ^ 2 * (1-z) ^ 1) + ((341699155501941 / 125000000000000000) * z ^ 3 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hden : 0 < (9 * (1 + (2 * t)) * (5 + ((-20) * t) + (24 * (t ^ 2)))) := by
    have h0 := base0_pos t ht
    have h2 := base2_pos t ht
    positivity
  unfold b
  apply (lt_div_iff₀ hden).2
  nlinarith only [hp]
lemma b_upper (t : ℝ) (ht : InInterval t) : b t < (124/1000 : ℝ) := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hp : 0 < (((6279 / 50) + ((-29304 / 125) * (t ^ 3)) + ((-17279 / 25) * t) + ((129768 / 125) * (t ^ 2))) : ℝ) := by
    have hid : (((6279 / 50) + ((-29304 / 125) * (t ^ 3)) + ((-17279 / 25) * t) + ((129768 / 125) * (t ^ 2))) : ℝ) = (15761113122493 / 3906250000000000) + ((15761113122493 / 3906250000000000) * z ^ 0 * (1-z) ^ 3) + ((4765248866293 / 390625000000000) * z ^ 1 * (1-z) ^ 2) + ((96043873461481 / 7812500000000000) * z ^ 2 * (1-z) ^ 1) + ((64522244757551 / 15625000000000000) * z ^ 3 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hden : 0 < (9 * (1 + (2 * t)) * (5 + ((-20) * t) + (24 * (t ^ 2)))) := by
    have h0 := base0_pos t ht
    have h2 := base2_pos t ht
    positivity
  unfold b
  apply (div_lt_iff₀ hden).2
  nlinarith only [hp]

lemma ell_box (t : ℝ) (ht : InInterval t) :
    (166/1000:ℝ) < ell t ∧ ell t < 167/1000 ∧ 1/6 < ell t := by
  have hd : 0 < 9+18*t := by linarith [ht.1]
  unfold ell
  refine ⟨?_, ?_, ?_⟩
  · apply (lt_div_iff₀ hd).2
    linarith [ht.2]
  · apply (div_lt_iff₀ hd).2
    linarith [ht.1]
  · apply (lt_div_iff₀ hd).2
    linarith [ht.2]

def geometry (t : ℝ) (ht : InInterval t) : RHIVProbe.Geometry where
  b := b t
  ell := ell t
  b_lo := (b_lower t ht).le
  b_hi := (b_upper t ht).le
  ell_lo := (ell_box t ht).1.le
  ell_hi := (ell_box t ht).2.1.le

theorem highGeometry (t : ℝ) (ht : InInterval t) :
    @RHIVProbe.HighGeometry (geometry t ht) := by
  exact @RHIVProbe.HighGeometry.mk (geometry t ht) (ell_box t ht).2.2

def momentParameter (t : ℝ) (ht : InInterval t) (hk : kappa t ≤ 3/4) :
    RHIVProbe.MomentParameter where
  kappa := kappa t
  lower := by linarith [kappa_lower_lower t ht]
  upper := hk

lemma physical_x (t : ℝ) (ht : InInterval t) :
    @RHIVProbe.x (geometry t ht) = lx t := by
  exact (geometry_lx t ht).symm
lemma physical_y (t : ℝ) (ht : InInterval t) :
    @RHIVProbe.y (geometry t ht) = ly t := by
  change (1+b t-ell t)/2 = ly t
  rw [geometry_ly t ht,geometry_lx t ht]
  ring
lemma physical_h (t : ℝ) (ht : InInterval t) :
    @RHIVProbe.h (geometry t ht) = h t := by
  change (1+b t+3*ell t)/2 = h t
  rw [geometry_h t ht,geometry_lx t ht]
  ring
lemma physical_boundary (t : ℝ) (ht : InInterval t) :
    @RHIVProbe.boundary (geometry t ht) = boundary t := by
  exact (geometry_boundary t ht).symm

lemma shifted_count (t delta u : ℝ) (ht : InInterval t) :
    RHBootstrapCount.countR (5/6) (2/(3*kappa t)) delta u =
      R t delta (1/2-u) := by
  rw [← moment_coefficient t ht]
  have hD : RHBootstrapCount.D (c t) u = D t (1/2-u) := by
    unfold RHBootstrapCount.D D; ring
  have hP : RHBootstrapCount.P (c t) u = P t (1/2-u) := by
    unfold RHBootstrapCount.P P; ring
  have hJ : RHBootstrapCount.J (5/6) (c t) delta u = J t delta (1/2-u) := by
    unfold RHBootstrapCount.J J
    rw [hD,hP]
  unfold RHBootstrapCount.countR R
  rw [hP,hJ]

lemma physical_endpoint_identity (t delta u : ℝ) (ht : InInterval t) :
    @RHIVProbe.endpointExponent (geometry t ht) delta u
      (RHBootstrapCount.countR (5/6) (2/(3*kappa t)) delta u) =
      E t delta (1/2-u) := by
  have hh : (1+b t+3*ell t)/2 = h t := by
    rw [geometry_h t ht,geometry_lx t ht]
    ring
  change -1/4+b t/6+5*ell t/4+(1/2+ell t)*delta+ell t*u*delta-
    ((1+b t+3*ell t)/2)*(1-RHBootstrapCount.countR (5/6) (2/(3*kappa t)) delta u) = _
  rw [hh,shifted_count t delta u ht]
  unfold E
  rw [geometry_C0 t ht]
  ring

theorem countGeometry (t : ℝ) (ht : InInterval t) (hk : kappa t ≤ 3/4) :
    @RHIVProbe.CountGeometry (geometry t ht) (momentParameter t ht hk) := by
  refine @RHIVProbe.CountGeometry.mk (geometry t ht) (momentParameter t ht hk) ?_
  intro delta u hd0 hd1 hu0 hu1
  change @RHIVProbe.endpointExponent (geometry t ht) delta u
      (RHBootstrapCount.countR (5/6) (2/(3*kappa t)) delta u) ≤ 0
  rw [physical_endpoint_identity t delta u ht]
  exact universal_endpoint t delta (1/2-u) ht hd0 hd1 (by linarith)

/-- The actual ideal count and all small nonnegative count losses have the
slope bounds required by the Mellin comparison. Uses CountMargins directly. -/
theorem ideal_count_loss_range (t delta u loss : ℝ) (ht : InInterval t)
    (hd0 : 0≤ delta) (hd1 : delta≤5/6) (hu0 : 0≤ u) (hu1 : u≤1/2)
    (hl0 : 0≤ loss) (hl1 : loss≤1/32) :
    0≤ RHBootstrapCount.countR (5/6) (2/(3*kappa t)) delta u+loss ∧
    RHBootstrapCount.countR (5/6) (2/(3*kappa t)) delta u+loss≤3/2 ∧
    0≤ RHBootstrapCount.countR (5/6) (2/(3*kappa t)) delta u+loss+delta/2-17/50 ∧
    RHBootstrapCount.countR (5/6) (2/(3*kappa t)) delta u+loss+delta/2-17/50≤2 := by
  rw [← moment_coefficient t ht]
  apply RHBootstrapCount.countR_loss_range (c t) delta u loss
  · linarith [c_positive_lower t ht]
  · linarith [c_upper_lower t ht]
  all_goals assumption

lemma optimality_kappa (t : ℝ) : CombineV22Optimality.kap t = kappa t := by
  unfold CombineV22Optimality.kap CombineV22Optimality.denom kappa
  congr 1 <;> ring
lemma optimality_boundary (t : ℝ) : CombineV22Optimality.boundary t = boundary t := by
  unfold CombineV22Optimality.boundary boundary
  congr 1 <;> ring
lemma optimality_length (t : ℝ) : CombineV22Optimality.length t = ell t := by
  unfold CombineV22Optimality.length ell
  congr 1 <;> ring
lemma root_in_interval : InInterval CombineV22Optimality.xiInf :=
  CombineV22Optimality.xiInf_mem_small
lemma root_kappa_upper : kappa CombineV22Optimality.xiInf ≤ 3/4 := by
  rw [← optimality_kappa]
  exact CombineV22Optimality.kap_xiInf_range.2

def rootGeometry : RHIVProbe.Geometry := geometry _ root_in_interval
def rootMomentParameter : RHIVProbe.MomentParameter :=
  momentParameter _ root_in_interval root_kappa_upper
theorem rootHighGeometry : @RHIVProbe.HighGeometry rootGeometry :=
  highGeometry _ root_in_interval
theorem rootCountGeometry : @RHIVProbe.CountGeometry rootGeometry rootMomentParameter :=
  countGeometry _ root_in_interval root_kappa_upper

#print axioms countGeometry
#print axioms ideal_count_loss_range
#print axioms rootCountGeometry
end
end CombineV22.EndpointGeometry

namespace CombineV22.CheckpointGeometry
noncomputable section
open CombineV22.Checkpoint

def geometry : RHIVProbe.Geometry where
  b := b
  ell := ell
  b_lo := by norm_num [b]
  b_hi := by norm_num [b]
  ell_lo := by norm_num [ell]
  ell_hi := by norm_num [ell]
theorem highGeometry : @RHIVProbe.HighGeometry geometry := by
  refine @RHIVProbe.HighGeometry.mk geometry ?_
  change (1/6:ℝ) < ell
  norm_num [ell]
def momentParameter : RHIVProbe.MomentParameter where
  kappa := kappa
  lower := kappa_range.1.le
  upper := kappa_range.2.le

lemma physical_x : @RHIVProbe.x geometry = lx := rfl
lemma physical_y : @RHIVProbe.y geometry = ly := by
  change (1+b-ell)/2 = lx+b
  unfold lx
  ring
lemma physical_h : @RHIVProbe.h geometry = h := rfl
lemma physical_boundary : @RHIVProbe.boundary geometry = boundary :=
  boundary_identity.symm
lemma actual_count (delta u : ℝ) :
    RHBootstrapCount.countR (5/6) (2/(3*kappa)) delta u = R delta u := rfl
lemma physical_endpoint_identity (delta u : ℝ) :
    @RHIVProbe.endpointExponent geometry delta u
      (RHBootstrapCount.countR (5/6) (2/(3*kappa)) delta u) = E delta u := rfl

theorem countGeometry : @RHIVProbe.CountGeometry geometry momentParameter := by
  refine @RHIVProbe.CountGeometry.mk geometry momentParameter ?_
  intro delta u hd0 hd1 hu0 hu1
  change @RHIVProbe.endpointExponent geometry delta u
    (RHBootstrapCount.countR (5/6) (2/(3*kappa)) delta u) ≤ 0
  rw [physical_endpoint_identity]
  exact (universal_endpoint delta u hd0 hd1 hu1).le

#print axioms countGeometry
end
end CombineV22.CheckpointGeometry

end PartIVBlock10

/- BEGIN consolidated System.lean -/
section PartIVBlock11
namespace CombineV22.System
noncomputable section
open RHBootstrapCount
/-! Critical witness obstruction and geometric necessity. These propositions
refer to the displayed exponents, never to lower bounds on actual counts. -/
def inv (d r : ℝ) : ℝ := if r ≤ 1 then 1-d*(1+r)/2 else longCount (5/6) d r
def plain (c d m : ℝ) : ℝ := 1-d*(2*m+(c/4)*(1-2*m))
def Witness (t r m : ℝ) : Prop := t-1/2 ≤ r ∧ r ≤ t ∧ 0 ≤ m ∧ m ≤ 1/2 ∧ t ≤ r+m

theorem critical_count_obstruction (c d t C : ℝ)
    (hc : 0< c) (hc1 : c<1) (hd : 19/50 ≤ d) (hd1 : d ≤ 39/100)
    (ht : 1≤ t) (ht1 : t≤3/2)
    (hcert : ∀ r m, Witness t r m → min (inv d r) (plain c d m) ≤ C) :
    countR (5/6) c d (1/2) ≤ C := by
  let r := rstar c (1/2) t
  have hlen := plain_length_bounds c (1/2) t hc hc1 (by norm_num) (by norm_num) ht ht1
  have hr1 := rstar_upper_one c (1/2) t hc hc1 (by norm_num) (by norm_num) ht1
  have hw : Witness t r (t-r) := by
    dsimp [Witness,r]
    exact ⟨by linarith,by linarith,by linarith,hlen.2,by ring_nf; rfl⟩
  have hh := hcert r (t-r) hw
  have hD := D_pos c (1/2) hc hc1 (by norm_num) (by norm_num)
  have hcross := crossing c (1/2) t hD.ne'
  have hshort := short_envelope_identity c (1/2) t hD.ne'
  have hi : inv d r = 1-d*invGain (1/2) r := by
    rw [inv,ite_eq_left hr1]
    unfold invGain
    ring
  have hp : plain c d (t-r)=1-d*plainGain c (1/2) t r := by
    unfold plain plainGain
    ring
  rw [hi,hp,←hcross,min_self] at hh
  have hshort' : shortCount c d (1/2) t ≤ C := by
    change 1-d+d*P c (1/2)*(3/2-t)/D c (1/2) ≤ C
    dsimp [r] at hh
    rw [hshort] at hh
    convert hh using 1 <;> ring
  have hw2 : Witness t t 0 := by unfold Witness; exact ⟨by linarith, le_rfl, le_rfl, by norm_num, by simp⟩
  have hh2 := hcert t 0 hw2
  have hi2 : inv d t=longCount (5/6) d t := by
    unfold inv
    split_ifs with ht'
    · have heq : t=1 := by linarith
      rw [heq]
      unfold longCount
      ring
    · rfl
  have hl : longCount (5/6) d t ≤ plain c d 0 := by
    have hd0 : 0≤ d := by linarith
    have hm := mul_nonneg (show 0≤5/6-d by linarith) (show 0≤3/2-t by linarith)
    have hcprod := mul_nonneg (show 0≤1-c by linarith) hd0
    unfold longCount plain
    nlinarith
  rw [hi2,min_eq_left hl] at hh2
  exact (balance_minimizes_max (5/6) c d (1/2) t hc hc1 (by norm_num) (by norm_num)
    (by linarith) (by linarith)).trans (max_le hshort' hh2)

def low0 (M ell : ℝ) : ℝ := 5/6+M/12-ell/6
def lowK (M ell : ℝ) : ℝ := 1/3+7*M/12+ell/3
def H (xi M ell : ℝ) : ℝ := 1+xi-(1+xi)*M/2+xi*ell
def physical (B lx ly ell delta g R z d : ℝ) : ℝ :=
  (1+delta)/2-B+(1-lx+ell)*(z-1/6)-(1+delta)*ly/2-ell/2+g*ell+d*(R+delta/2-z)

theorem critical_physical_identity (B lx ly ell xi R z : ℝ) :
    physical B lx ly ell xi (xi/2) R z (1-lx+ell) =
      H xi (lx+ly) ell-B+(1-lx+ell)*(R-2/3) := by
  unfold physical H
  ring

theorem direct_branches (lx ly ell k G B : ℝ)
    (hG : (ly-lx)/12≤ G) (hk : 0≤ k) (hk1 : lx+ly+ell-1≤ k)
    (hB : 5/6+lx/6+G-ell/6+k/2≤ B) :
    low0 (lx+ly) ell≤ B ∧ lowK (lx+ly) ell≤ B := by
  unfold low0 lowK
  constructor <;> linarith

theorem critical_necessary_branch (B lx ly ell xi R z : ℝ)
    (hh : 0<1-lx+ell) (hR : 2/3≤ R)
    (hE : physical B lx ly ell xi (xi/2) R z (1-lx+ell)≤0) :
    H xi (lx+ly) ell≤ B := by
  rw [critical_physical_identity] at hE
  have hm := mul_nonneg hh.le (show 0≤ R-2/3 by linarith)
  linarith

theorem floor_necessary_branch (B M ell xi delta h : ℝ)
    (_hh : 0< h) (hs : 0≤1-M/2+ell) (hdelta : xi≤ delta)
    (hE : H delta M ell-B+h/3≤0) : H xi M ell+h/3≤ B := by
  have hm := mul_nonneg (sub_nonneg.mpr hdelta) hs
  unfold H at *
  nlinarith

theorem global_contour_obstruction (beta gamma h ly omega : ℝ)
    (hb : beta≤7/8) (hg : 0< gamma) (hh : 3/4< h)
    (hly : 0≤ ly) (hly1 : ly<13/14) (hdom : 1< beta+gamma+omega) :
    (21/80:ℝ)< gamma+43*h/30+ly*(omega-1) := by
  have hm := mul_nonneg hly (show 0≤ beta+gamma+omega-1 by linarith)
  have hbprod := mul_nonneg (show 0≤7/8-beta by linarith) hly
  have hgprod := mul_pos hg (show 0<1-ly by linarith)
  nlinarith
end
end CombineV22.System

namespace CombineV22.System
noncomputable section
open RHBootstrapCount

open CombineV22Optimality in
theorem critical_count_eq (k x : ℝ) (hk : 13/18 ≤ k) (_hk1 : k ≤ 1)
    (hx : x ∈ Set.Icc (19/50:ℝ) (39/100:ℝ)) (hroot : critical k x = 0) :
    countR (5/6) (2/(3*k)) x (1/2) = 2/3 := by
  have hk0 : 0 < k := by linarith
  have hc0 : 0 < 2/(3*k) := by positivity
  have hc1 : 2/(3*k) < 1 := by
    apply (div_lt_iff₀ (by positivity : 0 < 3*k)).2
    linarith
  have hj := J_pos (5/6) (2/(3*k)) x (1/2) hc0 hc1
    (by norm_num) (by norm_num) (by linarith [hx.1]) (by linarith [hx.2])
  have hid : (countR (5/6) (2/(3*k)) x (1/2)-2/3) *
      J (5/6) (2/(3*k)) x (1/2) * (216*k) = critical k x := by
    unfold countR
    field_simp [hj.ne',hk0.ne']
    unfold J D P critical
    field_simp [hk0.ne']
    <;> ring
  rw [hroot] at hid
  rcases mul_eq_zero.mp hid with he | he
  · rcases mul_eq_zero.mp he with he | he
    · linarith
    · exact (hj.ne' he).elim
  · nlinarith

def fullK (M ell : ℝ) : ℝ := max (max 0 ((1+3*ell-2*M)/4))
  (max (M+ell-1) ((3*ell-1)/2))
def fullG (lx ly : ℝ) : ℝ := max (max 0 ((ly-lx)/12)) (ly-lx-ly/2)
def fullLow (lx ly ell : ℝ) : ℝ :=
  5/6+lx/6+fullG lx ly-ell/6+fullK (lx+ly) ell/2

theorem full_direct_branches (lx ly ell B : ℝ) (hB : fullLow lx ly ell ≤ B) :
    low0 (lx+ly) ell ≤ B ∧ lowK (lx+ly) ell ≤ B := by
  apply direct_branches lx ly ell (fullK (lx+ly) ell) (fullG lx ly) B
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact hB

/-- The hypotheses quantify supplied marginal exponents, not actual count lower bounds. -/
structure ComparisonData where
  k : ℝ
  x : ℝ
  lx : ℝ
  ly : ℝ
  ell : ℝ
  B : ℝ
  t : ℝ
  C : ℝ
  z : ℝ
  k_lower : 13/18 ≤ k
  k_upper : k ≤ 1
  x_interval : x ∈ Set.Icc (19/50:ℝ) (39/100:ℝ)
  critical_root : CombineV22Optimality.critical k x = 0
  endpoint : B ≤ (1+k)/2
  cutoff_lower : 1 ≤ t
  cutoff_upper : t ≤ 3/2
  height_positive : 0 < 1-lx+ell
  direct : fullLow lx ly ell ≤ B
  count_certificate : ∀ r m, Witness t r m → min (inv x r) (plain (2/(3*k)) x m) ≤ C

structure CentralCertificate extends ComparisonData where
  central : physical B lx ly ell x (x/2) C z (1-lx+ell) ≤ 0

theorem central_certificate_optimality (q : CentralCertificate) :
    CombineV22Optimality.boundary CombineV22Optimality.xiInf ≤ q.B := by
  have hk0 : 0 < q.k := by linarith [q.k_lower]
  have hc : 0 < 2/(3*q.k) := by positivity
  have hc1 : 2/(3*q.k) < 1 := by
    apply (div_lt_iff₀ (by positivity : 0 < 3*q.k)).2
    linarith [q.k_lower]
  have hR := critical_count_obstruction (2/(3*q.k)) q.x q.t q.C hc hc1
    q.x_interval.1 q.x_interval.2 q.cutoff_lower q.cutoff_upper q.count_certificate
  rw [critical_count_eq q.k q.x q.k_lower q.k_upper q.x_interval q.critical_root] at hR
  obtain ⟨h0,hK⟩ := full_direct_branches q.lx q.ly q.ell q.B q.direct
  have hH := critical_necessary_branch q.B q.lx q.ly q.ell q.x q.C q.z
    q.height_positive hR q.central
  exact (CombineV22Optimality.endpoint_compatible_optimality q.k q.x (q.lx+q.ly)
    q.ell q.B q.x_interval q.critical_root h0 hK hH q.endpoint).2

theorem inverse_enlarged_width (d r z w : ℝ) (hd : 0 ≤ d) (hd2 : d ≤ 2)
    (hw : 1 ≤ w) (hwidth : r+2*z ≤ w) :
    1-d*(1+r)/2 ≤ w-d*r-d*z := by
  have h1 := mul_nonneg (show 0 ≤ 1-d/2 by linarith) (sub_nonneg.mpr hw)
  have h2 := mul_nonneg (show 0 ≤ d/2 by linarith) (sub_nonneg.mpr hwidth)
  nlinarith

theorem inverse_enlarged_long (d r z w : ℝ) (hd2 : d ≤ 2)
    (hr : 1 ≤ r) (hz : 0 ≤ z) (hwidth : r+2*z ≤ w) :
    longCount (5/6) d r ≤ w-d*r-d*z := by
  have h2 := mul_nonneg (show 0 ≤ 2-d by linarith) hz
  unfold longCount
  nlinarith

theorem plain_enlarged_width (d k m z w : ℝ) (hd : 0 ≤ d)
    (hk : 0 < k) (hdk : d ≤ 6*k) (hw : 1 ≤ w) (hwidth : 2*m+6*k*z ≤ w) :
    1-2*d*m-d*(1-2*m)/(6*k) ≤ w-2*d*m-d*z := by
  have h1 := mul_nonneg (show 0 ≤ 6*k-d by linarith) (sub_nonneg.mpr hw)
  have h2 := mul_nonneg hd (sub_nonneg.mpr hwidth)
  apply (le_sub_iff_add_le).2
  apply (le_sub_iff_add_le).2
  have hk6 : 0 < 6*k := by positivity
  apply (mul_le_mul_iff_right₀ hk6).mp
  field_simp
  nlinarith

theorem marginal_interpolation (a b theta : ℝ) (ht : 0 ≤ theta) (ht1 : theta ≤ 1) :
    min a b ≤ theta*a+(1-theta)*b := by
  have h1 := mul_nonneg ht (sub_nonneg.mpr (min_le_left a b))
  have h2 := mul_nonneg (show 0 ≤ 1-theta by linarith) (sub_nonneg.mpr (min_le_right a b))
  nlinarith

theorem larger_moment_no_better (d m k k' : ℝ) (hd : 0 ≤ d) (hm : m ≤ 1/2)
    (hk : 0 < k) (hkk : k ≤ k') :
    1-2*d*m-d*(1-2*m)/(6*k) ≤ 1-2*d*m-d*(1-2*m)/(6*k') := by
  have hnum : 0 ≤ d*(1-2*m) := mul_nonneg hd (by linarith)
  have hdiv := div_le_div_of_nonneg_left hnum (show 0 < 6*k by positivity)
    (show 6*k ≤ 6*k' by linarith)
  linarith

theorem ordinary_count_obstructions (d : ℝ) (_hd : 19/50 ≤ d) (hd1 : d ≤ 39/100) :
    (2/3:ℝ) < 1-d/2 ∧ (2/3:ℝ) < 1-(2*(5/6)*d)/(3*(5/6)-d) := by
  constructor
  · linarith
  · have hp : 0 < 3*(5/6:ℝ)-d := by linarith
    have hfrac : (2*(5/6)*d)/(3*(5/6)-d) < (1/3:ℝ) := by
      apply (div_lt_iff₀ hp).2
      linarith
    linarith

theorem geometry_of_putative_improvement (lx ly ell B : ℝ)
    (hx : ell < lx) (hy : lx < ly) (he : 0 < ell)
    (hB : fullLow lx ly ell ≤ B) (hB1 : B < 7/8) :
    5/6 < B ∧ 3/4 < 1-lx+ell ∧ 1-lx+ell < 1 ∧
      0 < ly ∧ ly < 13/14 ∧ 0 < 1-(lx+ly)/2+ell := by
  obtain ⟨h0,hK⟩ := full_direct_branches lx ly ell B hB
  unfold low0 at h0
  unfold lowK at hK
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem euler_contour_obstruction (gamma h ly omega : ℝ)
    (hg : 0 < gamma) (hh : 0 < h) (hly : 0 ≤ ly) (ho : 1 < omega) :
    0 < gamma+5*h/6+ly*(omega-1) := by
  have hm := mul_nonneg hly (show 0 ≤ omega-1 by linarith)
  linarith

theorem absolute_contour_obstruction (sr wr beta h ly : ℝ)
    (hs : 1 < sr) (hw : 1 < wr) (hb : beta ≤ 7/8)
    (hh : 3/4 < h) (hly : 0 ≤ ly) :
    (3/4:ℝ) < (sr-beta)+ly*(wr-1)+5*h/6 := by
  have hm := mul_nonneg hly (show 0 ≤ wr-1 by linarith)
  linarith

/-- The five displayed comparison alternatives at the critical norm. All
tuple, puncture and deletion losses may be increased by a nonnegative cost. -/
def ComparisonAllowed (q : ComparisonData) : Prop :=
  physical q.B q.lx q.ly q.ell q.x (q.x/2) q.C q.z (1-q.lx+q.ell) ≤ 0 ∨
  (∃ delta, q.x ≤ delta ∧ H delta (q.lx+q.ly) q.ell-q.B+(1-q.lx+q.ell)/3 ≤ 0) ∨
  (∃ beta gamma omega cost, beta ≤ 7/8 ∧ 0 < gamma ∧ 1 < beta+gamma+omega ∧
    0 ≤ cost ∧ gamma+43*(1-q.lx+q.ell)/30+q.ly*(omega-1)+cost ≤ 0) ∨
  (∃ gamma omega cost, 0 < gamma ∧ 1 < omega ∧ 0 ≤ cost ∧
    gamma+5*(1-q.lx+q.ell)/6+q.ly*(omega-1)+cost ≤ 0) ∨
  (∃ sr wr beta cost, 1 < sr ∧ 1 < wr ∧ beta ≤ 7/8 ∧ 0 ≤ cost ∧
    (sr-beta)+q.ly*(wr-1)+5*(1-q.lx+q.ell)/6+cost ≤ 0)

structure DisplayedCertificate extends ComparisonData where
  ell_positive : 0 < ell
  lx_gt_ell : ell < lx
  ly_gt_lx : lx < ly
  comparison : ComparisonAllowed toComparisonData

theorem witness_uniform_envelope (c d t r m : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (hd : 0 ≤ d) (hd1 : d ≤ 5/6) (_ht : 1 ≤ t) (_ht1 : t ≤ 3/2)
    (hw : Witness t r m) :
    min (inv d r) (plain c d m) ≤ max (shortCount c d (1/2) t) (longCount (5/6) d t) := by
  have hD := D_pos c (1/2) hc hc1 (by norm_num) (by norm_num)
  have hshort := short_envelope_identity c (1/2) t hD.ne'
  have hcross := crossing c (1/2) t hD.ne'
  have hcontactI : 1-d*(1+rstar c (1/2) t)/2 = shortCount c d (1/2) t := by
    unfold invGain at hshort
    unfold shortCount
    calc 1-d*(1+rstar c (1/2) t)/2 = 1-d*(1/2+(1-1/2)*rstar c (1/2) t) := by ring
         _ = _ := by rw [hshort]; ring
  have hcontactP : plain c d (t-rstar c (1/2) t) = shortCount c d (1/2) t := by
    unfold invGain plainGain at hcross
    unfold plain
    rw [← hcontactI]
    have hc := congrArg (fun y : ℝ => d*y) hcross
    nlinarith [hc]
  obtain ⟨_,hrt,_,_,hrm⟩ := hw
  by_cases hr : r ≤ rstar c (1/2) t
  · have hcoef : 0 ≤ d*(2-c/2) := mul_nonneg hd (by linarith)
    have hm := mul_nonneg hcoef (show 0 ≤ m-(t-rstar c (1/2) t) by linarith)
    apply le_trans (min_le_right _ _) (le_trans _ (le_max_left _ _))
    rw [← hcontactP]
    unfold plain
    nlinarith
  · by_cases hr1 : r ≤ 1
    · have hm := mul_nonneg hd (show 0 ≤ r-rstar c (1/2) t by linarith)
      apply le_trans (min_le_left _ _) (le_trans _ (le_max_left _ _))
      rw [inv,ite_eq_left hr1,← hcontactI]
      nlinarith
    · have hm := mul_nonneg (show 0 ≤ 5/6-d by linarith) (sub_nonneg.mpr hrt)
      apply le_trans (min_le_left _ _) (le_trans _ (le_max_right _ _))
      rw [inv,ite_eq_right hr1]
      unfold longCount
      nlinarith

theorem balanced_count_certificate (c d : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (hd : 0 ≤ d) (hd1 : d < 5/6) :
    ∀ r m, Witness (tstar (5/6) c d (1/2)) r m →
      min (inv d r) (plain c d m) ≤ countR (5/6) c d (1/2) := by
  have ht := tstar_range (5/6) c d (1/2) hc hc1 (by norm_num) (by norm_num) hd hd1
  have hD := D_pos c (1/2) hc hc1 (by norm_num) (by norm_num)
  have hJ := J_pos (5/6) c d (1/2) hc hc1 (by norm_num) (by norm_num) hd hd1
  intro r m hw
  have h := witness_uniform_envelope c d (tstar (5/6) c d (1/2)) r m hc hc1 hd hd1.le ht.1 ht.2 hw
  rw [balance_identity (5/6) c d (1/2) hD.ne' hJ.ne',max_self,
    count_identity (5/6) c d (1/2) hJ.ne'] at h
  exact h


theorem displayed_certificate_lower_bound (q : DisplayedCertificate) :
    CombineV22Optimality.boundary CombineV22Optimality.xiInf ≤ q.B := by
  by_contra hn
  have hBU : CombineV22Optimality.boundary CombineV22Optimality.xiInf < (7/8:ℝ) := by
    have h := CombineV22Optimality.boundary_monotone CombineV22Optimality.xiInf_mem
      (by constructor <;> norm_num : (38859/100000:ℝ) ∈ Set.Icc (19/50:ℝ) (39/100:ℝ))
      CombineV22Optimality.xiInf_mem_small.2
    norm_num [CombineV22Optimality.boundary] at h
    unfold CombineV22Optimality.boundary
    linarith
  have hB : q.B < (7/8:ℝ) := lt_trans (lt_of_not_ge hn) hBU
  obtain ⟨_,hh,_,hly,hly1,hs⟩ := geometry_of_putative_improvement q.lx q.ly q.ell q.B
    q.lx_gt_ell q.ly_gt_lx q.ell_positive q.direct hB
  rcases q.comparison with hc | hf | hg | he | ha
  · exact hn (central_certificate_optimality ⟨q.toComparisonData,hc⟩)
  · obtain ⟨delta,hd,hE⟩ := hf
    have hH := floor_necessary_branch q.B (q.lx+q.ly) q.ell q.x delta
      (1-q.lx+q.ell) q.height_positive hs.le hd hE
    obtain ⟨h0,hK⟩ := full_direct_branches q.lx q.ly q.ell q.B q.direct
    have hb := (CombineV22Optimality.endpoint_compatible_optimality q.k q.x
      (q.lx+q.ly) q.ell q.B q.x_interval q.critical_root h0 hK
      (by change H q.x (q.lx+q.ly) q.ell ≤ q.B; linarith) q.endpoint).2
    exact hn hb
  · obtain ⟨beta,gamma,omega,cost,hbeta,hgamma,hdom,hcost,hE⟩ := hg
    have h := global_contour_obstruction beta gamma (1-q.lx+q.ell) q.ly omega
      hbeta hgamma hh hly.le hly1 hdom
    linarith
  · obtain ⟨gamma,omega,cost,hgamma,homega,hcost,hE⟩ := he
    have h := euler_contour_obstruction gamma (1-q.lx+q.ell) q.ly omega
      hgamma q.height_positive hly.le homega
    linarith
  · obtain ⟨sr,wr,beta,cost,hsr,hwr,hbeta,hcost,hE⟩ := ha
    have h := absolute_contour_obstruction sr wr beta (1-q.lx+q.ell) q.ly
      hsr hwr hbeta hh hly.le
    linarith

end
end CombineV22.System
#print axioms CombineV22.System.central_certificate_optimality
#print axioms CombineV22.System.displayed_certificate_lower_bound
#print axioms CombineV22.System.critical_count_obstruction
#print axioms CombineV22.System.critical_physical_identity
#print axioms CombineV22.System.direct_branches
#print axioms CombineV22.System.global_contour_obstruction

#print axioms CombineV22.System.balanced_count_certificate

end PartIVBlock11

/- BEGIN consolidated AlgebraicParameters.lean -/
section PartIVBlock12

set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace CombineV22.AlgebraicParameters
noncomputable section
open Polynomial
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

lemma primitive_irreducible_of_map {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] (f : R →+* S) {p : R[X]}
    (hp : p.IsPrimitive) (hl : f p.leadingCoeff ≠ 0)
    (hm : Irreducible (p.map f)) : Irreducible p := by
  refine ⟨fun hu => hm.not_isUnit (hu.map (Polynomial.mapRingHom f)), ?_⟩
  intro a b hab
  have hprod : f a.leadingCoeff * f b.leadingCoeff ≠ 0 := by
    rw [← map_mul, ← leadingCoeff_mul, ← hab]
    exact hl
  have ha : (a.map f).natDegree = a.natDegree :=
    natDegree_map_eq_iff.mpr (Or.inl (mul_ne_zero_iff.mp hprod).1)
  have hb : (b.map f).natDegree = b.natDegree :=
    natDegree_map_eq_iff.mpr (Or.inl (mul_ne_zero_iff.mp hprod).2)
  have hpa := isPrimitive_of_dvd hp (show a ∣ p from ⟨b,hab⟩)
  have hpb := isPrimitive_of_dvd hp (show b ∣ p from ⟨a,by rw [hab,mul_comm]⟩)
  rcases hm.isUnit_or_isUnit (by rw [hab,Polynomial.map_mul]) with h | h
  · left
    have heq := eq_C_of_natDegree_eq_zero (ha ▸ natDegree_eq_zero_of_isUnit h)
    rw [heq]
    exact isUnit_C.mpr (hpa (a.coeff 0) (by rw [← heq]))
  · right
    have heq := eq_C_of_natDegree_eq_zero (hb ▸ natDegree_eq_zero_of_isUnit h)
    rw [heq]
    exact isUnit_C.mpr (hpb (b.coeff 0) (by rw [← heq]))

def PB : ℤ[X] := C 7884*X^3+C (-18819)*X^2+C 14643*X+C (-3686)
def Pb : ℤ[X] := C 53835237*X^3+C 381756141*X^2+C 94706196*X+C (-17602208)
def modB : (ZMod 7)[X] := C 2*X^3+C (-3)*X^2+C (-1)*X+C 3
def modb : (ZMod 7)[X] := X^3+C (-3)*X^2+C (-3)*X+C (-1)

lemma map_PB : PB.map (Int.castRingHom (ZMod 7)) = modB := by
  have h0 : (7884:ZMod 7)=2 := by decide
  have h1 : (-18819:ZMod 7)= -3 := by decide
  have h2 : (14643:ZMod 7)= -1 := by decide
  have h3 : (-3686:ZMod 7)=3 := by decide
  simp only [PB,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X]
  change C (7884:ZMod 7)*X^3+C (-18819)*X^2+C 14643*X+C (-3686)=modB
  rw [h0,h1,h2,h3]
  rfl
lemma map_Pb : Pb.map (Int.castRingHom (ZMod 7)) = modb := by
  have h0 : (53835237:ZMod 7)=1 := by decide
  have h1 : (381756141:ZMod 7)= -3 := by decide
  have h2 : (94706196:ZMod 7)= -3 := by decide
  have h3 : (-17602208:ZMod 7)= -1 := by decide
  simp only [Pb,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X]
  change C (53835237:ZMod 7)*X^3+C 381756141*X^2+C 94706196*X+C (-17602208)=modb
  rw [h0,h1,h2,h3]
  simp [modb]
lemma modB_values :
    [modB.eval 0,modB.eval 1,modB.eval 2,modB.eval 3,modB.eval 4,modB.eval 5,modB.eval 6]=
      ([3,1,5,6,2,5,6] : List (ZMod 7)) := by
  simp only [modB,eval_add,eval_mul,eval_pow,eval_C,eval_X]
  decide
lemma modb_values :
    [modb.eval 0,modb.eval 1,modb.eval 2,modb.eval 3,modb.eval 4,modb.eval 5,modb.eval 6]=
      ([6,1,3,4,3,6,5] : List (ZMod 7)) := by
  simp only [modb,eval_add,eval_mul,eval_pow,eval_C,eval_X]
  decide
lemma modB_no_root (x : ZMod 7) : ¬ modB.IsRoot x := by
  simp only [IsRoot,modB,eval_add,eval_mul,eval_pow,eval_C,eval_X]
  fin_cases x <;> decide
lemma modb_no_root (x : ZMod 7) : ¬ modb.IsRoot x := by
  simp only [IsRoot,modb,eval_add,eval_mul,eval_pow,eval_C,eval_X]
  fin_cases x <;> decide
lemma modB_irreducible : Irreducible modB := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have h : modB.natDegree=3 := natDegree_cubic (by decide : (2:ZMod 7)≠0)
    simp [h]
  · exact modB_no_root
lemma modb_irreducible : Irreducible modb := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have h : modb.natDegree=3 := by
      unfold modb
      convert natDegree_cubic (by norm_num : (1:ZMod 7)≠0) (b:=(-3)) (c:=(-3)) (d:=(-1)) using 1 <;> simp
    simp [h]
  · exact modb_no_root

lemma PB_primitive : PB.IsPrimitive := by
  intro r hr
  have h0 := (C_dvd_iff_dvd_coeff r PB).mp hr 0
  have h1 := (C_dvd_iff_dvd_coeff r PB).mp hr 1
  norm_num [PB,coeff_X] at h0 h1
  apply isUnit_of_dvd_one
  have h := dvd_add (dvd_mul_of_dvd_right h0 (290:ℤ)) (dvd_mul_of_dvd_right h1 (-73:ℤ))
  norm_num at h
  exact h
lemma Pb_primitive : Pb.IsPrimitive := by
  intro r hr
  have h0 := (C_dvd_iff_dvd_coeff r Pb).mp hr 0
  have h3 := (C_dvd_iff_dvd_coeff r Pb).mp hr 3
  norm_num [Pb,coeff_X] at h0 h3
  apply isUnit_of_dvd_one
  have h := dvd_add (dvd_mul_of_dvd_right h0 (21729932:ℤ)) (dvd_mul_of_dvd_right h3 (-7104915:ℤ))
  norm_num at h
  exact h

lemma PB_irreducible : Irreducible PB := by
  apply primitive_irreducible_of_map (Int.castRingHom (ZMod 7)) PB_primitive
  · have hh : PB.leadingCoeff = 7884 := leadingCoeff_cubic (by norm_num)
    rw [hh]
    decide
  · rw [map_PB]; exact modB_irreducible
lemma Pb_irreducible : Irreducible Pb := by
  apply primitive_irreducible_of_map (Int.castRingHom (ZMod 7)) Pb_primitive
  · have hh : Pb.leadingCoeff = 53835237 := leadingCoeff_cubic (by norm_num)
