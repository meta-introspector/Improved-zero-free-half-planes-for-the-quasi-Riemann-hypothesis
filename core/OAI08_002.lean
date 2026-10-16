end OAIOriginalModule2488

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowOriginalPools
Source SHA256: a60bcbebdc46f6d24901d4e9a510d803ef52bf1f04c832885e6f348517820efe
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2489



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRaySlots
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma originalPool_element_norm (R : Set Id) (S : Finset Id) (hS : SourceExclusions S)
    (a b Y : ℝ) (ha : 0≤a) (hab : a≤b) (hY : 0<Y) (n : O)
    (hn : n∈canonicalSlotSupport (pool R S a b Y)) : elementNorm n≤Y*b := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
  rw [primaryTuple_norm P (pool_supported R S hS a b Y P hP)]
  exact (pool_norm_bounds R S ha hab hY P hP).2

theorem originalPools_low_scales {K : ℕ} (R : Set Id) (S : Finset Id)
    (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (a b : ℝ) (ha : 0≤a) (hab : a≤b) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧
      let T := fun i=>canonicalSlotSupport (pool R S a b (Z^(ell i)))
      ∀(J : Finset (Fin K))(p : LowUnselectedTuple T J),
      let L := elementNorm (∏i : J,(p i).val)
      1≤Z^(23/48:ℝ)/L ∧
      1≤(Z^(23/48:ℝ)/L)^2/lowPhysicalScale (calibrationForSet S hmax) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) ∧
      ∀δ : ℝ,0≤δ→lowGramFactor (calibrationForSet S hmax) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) δ≤
        Real.sqrt (3*elementNorm (calibrationForSet S hmax).generator/L)*Z^(3/16+(23/96)*δ:ℝ) := by
  filter_upwards [eventually_original_slot_scales (calibrationForSet S hmax) ell hell hsum
    (max 1 b) (le_max_left _ _)] with Z hZ
  refine ⟨hZ.1,?_⟩
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ.1
  apply hZ.2
  · intro i n hn
    exact canonicalSlotSupport_nonzero _ (pool_supported R S hS a b _) n hn
  · intro i n hn
    apply (originalPool_element_norm R S hS a b (Z^(ell i)) ha hab (by positivity) n hn).trans
    calc
      _≤Z^(ell i)*max 1 b := mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
      _=_ := mul_comm _ _

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule2489

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowNominalGeometry
Source SHA256: 83f5fbf5452eed0fef0955a2a8da86a08060ffdcd16d7c9736159dd88e77064d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2490


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRaySlots
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowUnselectedLength {K : ℕ} (ell : Fin K→ℝ) (J : Finset (Fin K)) : ℝ := ∑i∈J,ell i

def lowSelectedLength {K : ℕ} (ell : Fin K→ℝ) (J : Finset (Fin K)) : ℝ := ∑i : SelectedSlot J,ell i.val

lemma lowLength_sum {K : ℕ} (ell : Fin K→ℝ) (J : Finset (Fin K)) :
    lowUnselectedLength ell J+lowSelectedLength ell J=∑i,ell i := by
  rw [lowUnselectedLength,lowSelectedLength,Finset.sum_coe_sort]
  exact Finset.sum_add_sum_compl J ell

lemma lowLength_bounds {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (hsum : ∑i,ell i≤1/6) (J : Finset (Fin K)) :
    0≤lowUnselectedLength ell J ∧ lowUnselectedLength ell J≤1/6 ∧
    0≤lowSelectedLength ell J ∧ lowSelectedLength ell J≤1/6-lowUnselectedLength ell J := by
  have hu : 0≤lowUnselectedLength ell J := Finset.sum_nonneg (fun i _=>hell i)
  have hs : 0≤lowSelectedLength ell J := Finset.sum_nonneg (fun i _=>hell i.val)
  have he := lowLength_sum ell J
  exact ⟨hu,by linarith,hs,by linarith⟩

lemma lowUnselectedProduct_norm_lower {K : ℕ} (ell : Fin K→ℝ)
    (a Z : ℝ) (ha : 0<a) (hZ : 0<Z) (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→a*Z^(ell i)≤elementNorm x)
    (J : Finset (Fin K)) (p : LowUnselectedTuple slots J) :
    (min 1 a)^K*Z^(lowUnselectedLength ell J)≤elementNorm (∏i : J,(p i).val) := by
  have hc : J.card≤K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤a^J.card*Z^(lowUnselectedLength ell J) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (pow_le_pow_of_le_one (le_of_lt (lt_min zero_lt_one ha)) (min_le_left _ _) hc).trans
        (pow_le_pow_left₀ (by positivity) (min_le_right _ _) _)
    _=∏i : J,a*Z^(ell i.val) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hZ,Finset.sum_coe_sort]
      rfl
    _≤_ := Finset.prod_le_prod₀ (fun _ _=>by positivity) (fun i _=>hslots i.val _ (p i).property)

lemma originalPool_element_lower (R : Set Id) (S : Finset Id) (hS : SourceExclusions S)
    (a b Y : ℝ) (ha : 0≤a) (hab : a≤b) (hY : 0<Y) (n : O)
    (hn : n∈canonicalSlotSupport (pool R S a b Y)) : a*Y≤elementNorm n := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
  rw [primaryTuple_norm P (pool_supported R S hS a b Y P hP)]
  simpa only [mul_comm] using (pool_norm_bounds R S ha hab hY P hP).1.le

lemma lowPhysicalScale_source (C : CalibrationData) (Z L : ℝ) (hZ : 0<Z) :
    lowPhysicalScale C (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)=
      elementNorm C.generator*Z^(5/6:ℝ)/L^2 := by
  unfold lowPhysicalScale
  have he : Z^(17/48:ℝ)*Z^(23/48:ℝ)=Z^(5/6:ℝ) := by rw [←Real.rpow_add hZ];norm_num
  rw [←he]
  ring

lemma lowPhysicalScale_nominal_bound (C : CalibrationData) (Z L c d : ℝ)
    (hZ : 0<Z) (hc : 0<c) (hL : c*Z^d≤L) :
    lowPhysicalScale C (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)≤
      (elementNorm C.generator/c^2)*Z^(5/6-2*d:ℝ) := by
  have hl : 0<L := lt_of_lt_of_le (by positivity) hL
  rw [lowPhysicalScale_source C Z L hZ]
  calc
    _≤elementNorm C.generator*Z^(5/6:ℝ)/(c*Z^d)^2 :=
      div_le_div_of_nonneg_left (by unfold elementNorm;positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) hL 2)
    _=_ := by
      have hp : (Z^d)^2=Z^(2*d) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
        congr 1
        push_cast
        ring
      rw [mul_pow,hp,Real.rpow_sub hZ]
      ring

lemma lowSelectedScale_product {K : ℕ} (ell : Fin K→ℝ) (J : Finset (Fin K))
    (Z : ℝ) (hZ : 0<Z) :
    (∏i∈Finset.univ\J,Z^(ell i))=Z^(lowSelectedLength ell J) := by
  rw [lowSelectedLength,Finset.sum_coe_sort,Real.rpow_sum_of_pos hZ]

lemma lowSelectedCaps_product {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (J : Finset (Fin K)) (Z b : ℝ) (hZ : 1≤Z) :
    (∏i : SelectedSlot J,max 1 (b*Z^(ell i.val)))≤
      (max 1 b)^K*Z^(lowSelectedLength ell J) := by
  have hc : Fintype.card (SelectedSlot J)≤K := by
    simpa only [Fintype.card_coe,Finset.card_univ,Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ (Finset.univ\J))
  calc
    _≤∏i : SelectedSlot J,max 1 b*Z^(ell i.val) := by
      apply Finset.prod_le_prod₀ (fun _ _=>le_trans zero_le_one (le_max_left _ _))
      intro i hi
      apply max_le
      · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hZ (hell i.val))
      · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    _=(max 1 b)^(Fintype.card (SelectedSlot J))*Z^(lowSelectedLength ell J) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
        ←Real.rpow_sum_of_pos (lt_of_lt_of_le zero_lt_one hZ)]
      rfl
    _≤_ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_max_left _ _) hc) (by positivity)

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule2490

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowCentralGeometry
Source SHA256: c2b8de59af37fc88f509f02fdcf6608f1b91c848dbe1a5b74b83b1eb70850ef4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2491


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical

lemma lowUnselectedProduct_norm_upper_nominal {K : ℕ} (ell : Fin K→ℝ)
    (b Z : ℝ) (hZ : 0<Z) (slots : Fin K→Finset ActualEisensteinCubic.O)
    (hslots : ∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))
    (J : Finset (Fin K)) (p : LowUnselectedTuple slots J) :
    elementNorm (∏i : J,(p i).val)≤(max 1 b)^K*Z^(lowUnselectedLength ell J) := by
  have hc : J.card≤K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤∏i : J,max 1 b*Z^(ell i.val) := Finset.prod_le_prod₀
      (fun _ _=>by unfold elementNorm;positivity)
      (fun i _=>(hslots i.val _ (p i).property).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
    _=(max 1 b)^J.card*Z^(lowUnselectedLength ell J) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hZ,Finset.sum_coe_sort]
      rfl
    _≤_ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_max_left _ _) hc) (by positivity)

theorem eventually_low_selected_caps {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (b ε : ℝ) (hε : 0<ε) :
    ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧ ∀J : Finset (Fin K),
      (∏i : SelectedSlot J,max 1 (b*Z^(ell i.val)))≤Z^(lowSelectedLength ell J+ε/2) := by
  have hp : 0<ε/2 := by linarith
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop hp).eventually (Filter.eventually_ge_atTop ((max 1 b)^K))] with Z hZ hc
  refine ⟨hZ,?_⟩
  intro J
  apply (lowSelectedCaps_product ell hell J Z b hZ.le).trans
  calc
    _≤Z^(ε/2)*Z^(lowSelectedLength ell J) := mul_le_mul_of_nonneg_right hc (by positivity)
    _=_ := by rw [←Real.rpow_add (lt_trans zero_lt_one hZ)];congr 1;ring

def lowCentralShift (Z T ell0 : ℝ) : ℝ := Real.logb Z T-1-ell0

lemma lowCentralShift_scale (Z T ell0 : ℝ) (hZ : 1<Z) (hT : 0<T) :
    Z^(1+ell0+lowCentralShift Z T ell0)=T := by
  rw [lowCentralShift,show 1+ell0+(Real.logb Z T-1-ell0)=Real.logb Z T by ring]
  exact Real.rpow_logb (lt_trans zero_lt_one hZ) (ne_of_gt hZ) hT

lemma lowCentralShift_bound (Z T ell ε : ℝ) (hZ : 1<Z) (hT : 0<T) (hε : 0≤ε)
    (hlo : Z^(1+ell-ε/2)≤T) (hhi : T≤Z^(1+ell+ε/2)) :
    |lowCentralShift Z T (ell+ε/2)|≤ε := by
  have he := lowCentralShift_scale Z T (ell+ε/2) hZ hT
  rw [←he,Real.rpow_le_rpow_left_iff hZ] at hlo hhi
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma lowCentral_ratio_bounds (Z T ell ε : ℝ) (hZ : 0<Z)
    (hlo : Z^(-ε/2)≤T/Z^(1+ell)) (hhi : T/Z^(1+ell)≤Z^(ε/2)) :
    Z^(1+ell-ε/2)≤T ∧ T≤Z^(1+ell+ε/2) := by
  constructor
  · have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hZ (1+ell))).mp hlo
    convert hh using 1
    rw [←Real.rpow_add hZ]
    congr 1
    ring
  · have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hZ (1+ell))).mp hhi
    convert hh using 1
    rw [←Real.rpow_add hZ]
    congr 1
    ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule2491

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowInverseNormalize
Source SHA256: 384124deace73ecac59856f5d39090e5df9aed167825adf29728f68e83152648
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2492


namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

lemma low_inverse_power_cancel (Z d α : ℝ) (hZ : 0<Z) :
    Z^(5/6-2*d+α)*(Z^d)^2/Z^(5/6:ℝ)=Z^α := by
  have hp : (Z^d)^2=Z^(2*d) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
    congr 1
    push_cast
    ring
  rw [hp,←Real.rpow_add hZ,←Real.rpow_sub hZ]
  congr 1
  ring

lemma low_inverse_sqrt_normalized (q C B Z L d α H E : ℝ) (n : ℕ)
    (hq : 0<q) (hC : 0≤C) (_hB : 0≤B) (hZ : 0<Z) (hL : 0<L) (hH : 1≤H)
    (hE : 0≤E) (hEL : E≤C*H^n*Z^(5/6-2*d+α)) (hLB : L≤B*Z^d) :
    Real.sqrt E/Real.sqrt (q*Z^(5/6:ℝ)/L^2)≤
      Real.sqrt (C*B^2/q)*H^n*Z^(α/2) := by
  have hratio : E/(q*Z^(5/6:ℝ)/L^2)≤(C*B^2/q)*H^n*Z^α := by
    calc
      _≤(C*H^n*Z^(5/6-2*d+α))/(q*Z^(5/6:ℝ)/L^2) :=
        div_le_div_of_nonneg_right hEL (by positivity)
      _=(C*H^n*Z^(5/6-2*d+α))*L^2/(q*Z^(5/6:ℝ)) := by field_simp
      _≤(C*H^n*Z^(5/6-2*d+α))*(B*Z^d)^2/(q*Z^(5/6:ℝ)) := by
        gcongr
      _=(C*B^2/q)*H^n*(Z^(5/6-2*d+α)*(Z^d)^2/Z^(5/6:ℝ)) := by ring
      _=_ := by rw [low_inverse_power_cancel Z d α hZ]
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
end OAIOriginalModule2492

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowNominalEnergy
Source SHA256: f3ebfbc28c9d50e097c63c44214fda22391890846cb42d614d9e62420955d6e0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2493



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem low_selected_nominal_energy (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (Ck b ε : ℝ) (hCk : 0<Ck) (hε : 0<ε) (hε1 : ε≤1) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(R : Finset O),
      (∀z∈R,z≠0 ∧ elementNorm z≤Ck*Z^(5/6-2*lowUnselectedLength ell J))→
    ∀X : ℝ,0<X→Z^(1+lowSelectedLength ell J-ε/2)≤X→X≤Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀(Y : Fin K→ℝ)(t : ℝ)(σ : RayRing),
      (∑z∈R,‖lowSelectedInverseRow Finset.univ
        (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W Y t)
        η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t σ z‖^2)≤
        C*(1+‖t‖)^degree*Z^((5/6-2*lowUnselectedLength ell J)+507*ε) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_selected_physical_energy η S hS hbad K Ck ε hCk hε hε1
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [eventually_low_selected_caps ell hell b ε hε,Filter.eventually_ge_atTop Z₀] with Z hc hZ
  refine ⟨hc.1,?_⟩
  intro T hT hout hdis hnorm J R hR X hX hXlo hXhi W hW Y t σ
  obtain ⟨hd,hd1,hs,hscap⟩ := lowLength_bounds ell hell hsum J
  have hscale := lowCentralShift_scale Z X (lowSelectedLength ell J+ε/2) hc.1 hX
  rw [←hscale]
  apply he Z (lowUnselectedLength ell J) (lowSelectedLength ell J+ε/2)
    (lowCentralShift Z X (lowSelectedLength ell J+ε/2)) hZ hd hd1 (by linarith) (by linarith)
    (lowCentralShift_bound Z X (lowSelectedLength ell J) ε hc.1 hX hε.le hXlo hXhi)
    R hR T hT hout hdis J (fun i=>max 1 (b*Z^(ell i.val)))
    (fun i=>le_max_left _ _)
    (fun i P hP=>(hnorm i.val P hP).trans (le_max_right _ _)) (hc.2 J) W hW Y t σ

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule2493

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowPhysicalInverseBound
Source SHA256: 9991e2ce061afdfdeb0e12439364f38ac1bc3a734fcaa0b19905674563f14797
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2494



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem low_physical_inverse_normalized (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (a b aCut bCut ε : ℝ) (ha : 0<a) (haCut : 0<aCut) (hbCut : 0<bCut)
    (hε : 0<ε) (hε1 : ε≤1) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(p : LowUnselectedTuple (fun i=>canonicalSlotSupport (T i)) J),
    ∀X : ℝ,0<X→Z^(1+lowSelectedLength ell J-ε/2)≤X→X≤Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀t : ℝ,
      let L := elementNorm (∏i : J,(p i).val)
      let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)
      ∀(hX0 : 0<Z^(17/48:ℝ)/L)(hY0 : 0<Z^(23/48:ℝ)/L),
      (Real.sqrt Q)⁻¹/(2*Real.pi)*
        lowInverseMass (calibrationForSet S hS) aCut bCut haCut hbCut
          (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) hX0 hY0
          (lowSelectedInverseRow Finset.univ
            (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W (fun i=>Z^(ell i)) t)
            η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t)≤
        C*(1+‖t‖)^degree*Z^(507*ε/2) := by
  let q := elementNorm (calibrationForSet S hS).generator
  let c := (min 1 a)^K
  let B := (max 1 b)^K
  have hq : 0<q := calibration_elementNorm_pos _
  have hc : 0<c := by dsimp [c];positivity
  have hB : 0<B := by dsimp [B];positivity
  let Ck := 2*bCut*(q/c^2)
  have hCk : 0<Ck := by dsimp [Ck];positivity
  obtain ⟨degree,C,ZC,hbound⟩ := low_selected_nominal_energy η S hS hbad ell hell hsum Ck b ε hCk hε hε1
  let C0 := ((Fintype.card RayRing:ℝ)+1)*Real.sqrt (C*B^2/q)/(2*Real.pi)
  have hC0 : 0<C0 := by dsimp [C0];positivity
  refine ⟨degree,C0,hC0,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T hT hout hdis hnorm J p X hX hXlo hXhi W hW t
  dsimp only
  let L := elementNorm (∏i : J,(p i).val)
  let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)
  intro hX0 hY0
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  have hL : 0<L := lowUnselectedProduct_norm_pos _
    (fun i n hn=>canonicalSlotSupport_nonzero _ (hT i) n hn) J p
  have hnormE (i : Fin K) (n : O) (hn : n∈canonicalSlotSupport (T i)) :
      a*Z^(ell i)≤elementNorm n ∧ elementNorm n≤b*Z^(ell i) := by
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact hnorm i P hP
  have hLlo : c*Z^(lowUnselectedLength ell J)≤L :=
    lowUnselectedProduct_norm_lower ell a Z ha hz _ (fun i n hn=>(hnormE i n hn).1) J p
  have hLhi : L≤B*Z^(lowUnselectedLength ell J) :=
    lowUnselectedProduct_norm_upper_nominal ell b Z hz _ (fun i n hn=>(hnormE i n hn).2) J p
  have hQ : 0<Q := lowPhysicalScale_pos _ _ _ hX0 hY0
  let R := lowNumeratorRows aCut bCut haCut hbCut Q hQ
  let row := lowSelectedInverseRow Finset.univ
    (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W (fun i=>Z^(ell i)) t)
    η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t
  have hrows : ∀z∈R,z≠0 ∧ elementNorm z≤Ck*Z^(5/6-2*lowUnselectedLength ell J) := by
    intro z hzR
    refine ⟨lowNumeratorRows_nonzero aCut bCut haCut hbCut Q hQ z hzR,?_⟩
    apply (lowNumeratorRows_norm_bound aCut bCut haCut hbCut Q hQ z hzR).trans
    have hh := mul_le_mul_of_nonneg_left
      (lowPhysicalScale_nominal_bound (calibrationForSet S hS) Z L c (lowUnselectedLength ell J) hz hc hLlo)
      (show 0≤2*bCut by positivity)
    simpa only [Ck,mul_assoc] using hh
  have he (σ : RayRing) : (∑z∈R,‖row σ z‖^2)≤
      C*(1+‖t‖)^degree*Z^(5/6-2*lowUnselectedLength ell J+507*ε) :=
    hZ.2 T hT hout hdis (fun i P hP=>(hnorm i P hP).2) J R hrows X hX hXlo hXhi W hW (fun i=>Z^(ell i)) t σ
  have hn (σ : RayRing) : Real.sqrt (∑z∈R,‖row σ z‖^2)/Real.sqrt Q≤
      Real.sqrt (C*B^2/q)*(1+‖t‖)^degree*Z^(507*ε/2) := by
    dsimp only [Q]
    rw [lowPhysicalScale_source _ Z L hz]
    exact low_inverse_sqrt_normalized q C B Z L (lowUnselectedLength ell J) (507*ε) (1+‖t‖)
      (∑z∈R,‖row σ z‖^2) degree hq ZC.le hB.le hz hL (le_add_of_nonneg_right (norm_nonneg t))
      (Finset.sum_nonneg (fun _ _=>sq_nonneg _)) (he σ) hLhi
  change (Real.sqrt Q)⁻¹/(2*Real.pi)*(∑σ : RayRing,Real.sqrt (∑z∈R,‖row σ z‖^2))≤_
  calc
    _=(∑σ : RayRing,Real.sqrt (∑z∈R,‖row σ z‖^2)/Real.sqrt Q)/(2*Real.pi) := by
      rw [←Finset.sum_div]
      ring
    _≤(∑σ : RayRing,Real.sqrt (C*B^2/q)*(1+‖t‖)^degree*Z^(507*ε/2))/(2*Real.pi) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun σ _=>hn σ)) (by positivity)
    _≤_ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      dsimp [C0]
      calc
        _=((Fintype.card RayRing:ℝ)*Real.sqrt (C*B^2/q)/(2*Real.pi))*(1+|t|)^degree*Z^(507*ε/2) := by ring
        _≤_ := by gcongr ; linarith

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule2494

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowCentralTuple
Source SHA256: 874b63c1d6d28a956d7448a1a14d9ebbef2835c98fe43840f0cc7a895cae610c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2495



namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma low_compensated_sqrt_factor (q L : ℝ) (hq : 0≤q) (hL : 0<L) :
    Real.sqrt (3*q/L)=Real.sqrt (3*q)*L^(-(1/2:ℝ)) := by
  rw [Real.sqrt_div (by positivity)]
  simp only [div_eq_mul_inv,Real.sqrt_eq_rpow,Real.rpow_neg hL.le]

theorem low_central_compensated_tuple (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hM : 0≤M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(X : ℝ),0<X→
      Z^(1+lowSelectedLength ell J-ε/2)≤X→X≤Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀t : ℝ,
      ‖∑p : ∀i,canonicalSlotSupport (T i),
        compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J*
          compensationRowTest η (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) J
            (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) X t*
          selectedSlotFactor W (fun i=>Z^(ell i)) (fun i=>(p i).val) J t‖≤
        C*(1+‖t‖)^degree*Z^(3/16+254*ε) := by
  obtain ⟨Cg,hCg,hgram⟩ := compensation_tuple_actual_gram ε hε hε1 W0 W1
    a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM S hS hbad
  obtain ⟨degree,Ci,hCi,hinverse⟩ := low_physical_inverse_normalized η S hS hbad ell hell hsum
    a b (a0*a1) (max 1 (b0*b1)) ε ha (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hε hε1.le
  obtain ⟨Cu,hCu,hmass⟩ := lowUnselectedMass_bound K 1 (by norm_num)
  let q := elementNorm (calibrationForSet S hS).generator
  have hq : 0<q := calibration_elementNorm_pos _
  let C0 := Cg*Ci*Real.sqrt (3*q)*Cu
  have hC0 : 0<C0 := by dsimp [C0];positivity
  refine ⟨degree,C0,hC0,?_⟩
  filter_upwards [hinverse,eventually_original_slot_scales (calibrationForSet S hS)
    ell hell hsum (max 1 b) (le_max_left _ _)] with Z hInv hScale
  refine ⟨hInv.1,?_⟩
  intro T hT hout hdis hnorm J X hX hXlo hXhi W hW t
  let slots := fun i=>canonicalSlotSupport (T i)
  let Yp := fun i=>Z^(ell i)
  have hz : 0<Z := lt_trans zero_lt_one hInv.1
  have hslots : ∀i n,n∈slots i→n≠0 := fun i=>canonicalSlotSupport_nonzero _ (hT i)
  have hnormE : ∀i n,n∈slots i→elementNorm n≤max 1 b*Z^(ell i) := by
    intro i n hn
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact (hnorm i P hP).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hs := hScale.2 slots hslots hnormE J
  have hg := hgram K η slots hslots J W Yp (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) X t
    (by positivity) (by positivity) hX (fun p=>(hs p).1) (fun p=>(hs p).2.1)
  apply hg.trans
  let G := Z^(3/16+(23/96)*ε:ℝ)
  let V := Ci*(1+‖t‖)^degree*Z^(507*ε/2)
  have hGV : G*V≤Ci*(1+‖t‖)^degree*Z^(3/16+254*ε) := by
    dsimp only [G,V]
    calc
      _=Ci*(1+‖t‖)^degree*(Z^(3/16+(23/96)*ε:ℝ)*Z^(507*ε/2)) := by ring
      _≤_ := by
        rw [←Real.rpow_add hz]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hInv.1.le (by linarith)
  have hterm (p : LowUnselectedTuple slots J) :
      let L := elementNorm (∏i : J,(p i).val)
      let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)
      ‖lowUnselectedWeight slots J W Yp p‖*((Real.sqrt Q)⁻¹/(2*Real.pi))*
        lowGramFactor (calibrationForSet S hS) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) ε*
        lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
          (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
          (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)
          (div_pos (by positivity) (lowUnselectedProduct_norm_pos slots hslots J p))
          (div_pos (by positivity) (lowUnselectedProduct_norm_pos slots hslots J p))
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t)
            η S hS (lowSelectedIdeal slots J) X t)≤
      (Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*Z^(3/16+254*ε))*
        (‖lowUnselectedWeight slots J W Yp p‖*L^(-(1/2:ℝ))) := by
    dsimp only
    let L := elementNorm (∏i : J,(p i).val)
    let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)
    have hL := lowUnselectedProduct_norm_pos slots hslots J p
    have hgb := (hs p).2.2 ε hε.le
    have hib := hInv.2 T hT hout hdis hnorm J p X hX hXlo hXhi W hW t
      (div_pos (by positivity) hL) (div_pos (by positivity) hL)
    have hgn : 0≤lowGramFactor (calibrationForSet S hS) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) ε := Real.sqrt_nonneg _
    have hh := mul_le_mul_of_nonneg_left hib
      (mul_nonneg (norm_nonneg (lowUnselectedWeight slots J W Yp p)) hgn)
    have hh2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgb (norm_nonneg (lowUnselectedWeight slots J W Yp p)))
      (show 0≤V by dsimp [V];positivity)
    calc
      _=‖lowUnselectedWeight slots J W Yp p‖*
        lowGramFactor (calibrationForSet S hS) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) ε*
        (Real.sqrt Q)⁻¹/(2*Real.pi)*
        lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
          (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)
          (div_pos (by positivity) hL) (div_pos (by positivity) hL)
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t) η S hS (lowSelectedIdeal slots J) X t) := by ring
      _≤(‖lowUnselectedWeight slots J W Yp p‖*Real.sqrt (3*q/L))*(G*V) := by
        have hh3 := hh.trans hh2
        simp only [G,V,div_eq_mul_inv,mul_assoc] at hh3 ⊢
        convert hh3 using 1 ; congr 7
      _≤(‖lowUnselectedWeight slots J W Yp p‖*Real.sqrt (3*q/L))*
          (Ci*(1+‖t‖)^degree*Z^(3/16+254*ε)) :=
        mul_le_mul_of_nonneg_left hGV (by positivity)
      _=_ := by rw [low_compensated_sqrt_factor q L hq.le hL];ring
  have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=Finset.univ) (fun p _=>hterm p)) hCg.le
  apply hh.trans
  rw [←Finset.mul_sum]
  have hm := hmass T hT J W Yp hW
  calc
    _≤Cg*((Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*Z^(3/16+254*ε))*Cu) := by gcongr
    _=_ := by dsimp [C0];ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule2495

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowRemoteMass
Source SHA256: 8b864da5b8e13e548474693eaf72cd29ab0eca3d5bb970bf878613573da64043
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2496




namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma canonicalSlot_count (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (H : ℝ) (hH : 1≤H) (hnorm : ∀P∈T,(Ideal.absNorm P.val:ℝ)≤H) :
    ((canonicalSlotSupport T).card:ℝ)≤128*H := by
  have hh := DescentFiberCost.finite_ideal_count_real (lowPrimeIdealList T) H hH
    (fun I hI=>(lowPrimeIdealList_prime T I hI).ne_zero) (lowPrimeIdealList_norm T H hnorm)
  have he := Fintype.card_congr (canonicalSlotEquiv T hT)
  simp only [Fintype.card_coe] at he
  rw [lowPrimeIdealList,Finset.card_image_of_injective _ Subtype.val_injective,he] at hh
  exact hh

lemma canonicalTuple_count {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (hsum : ∑i,ell i≤1/6) (b Z : ℝ) (hZ : 1≤Z)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (hnorm : ∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤b*Z^(ell i)) :
    (Fintype.card (∀i,canonicalSlotSupport (T i)):ℝ)≤(128*max 1 b)^K*Z^(1/6:ℝ) := by
  rw [Fintype.card_pi,Nat.cast_prod]
  calc
    _≤∏i,128*(max 1 b*Z^(ell i)) := by
      apply Finset.prod_le_prod₀ (fun i _=>Nat.cast_nonneg _)
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

lemma slotProduct_norm_ge_one {K : ℕ} (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    1≤elementNorm (slotProduct p J) := by
  unfold elementNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr (slotProduct_nonzero p hp J)))

lemma compensationSubsetWeight_norm_le_one {K : ℕ} (η : HeckeFamily.Character)
    (W : Fin K→ℝ→ℂ) (hW : ∀i x,‖W i x‖≤1) (Y : Fin K→ℝ)
    (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    ‖compensationSubsetWeight η W Y p J‖≤1 := by
  rw [compensationSubsetWeight,norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) _).trans _
  · rw [compensationSubsetCoefficient,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (slotProduct_norm_pos p hp J).le _),norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos (slotProduct_norm_ge_one p hp J) (by norm_num))).trans (ProbeRow.targetMonoid_norm_le_one η _)
  · rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun i _=>hW i _)

lemma compensation_scale_mass_bound {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (b Z : ℝ) (hZ : 1≤Z) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)
    (hnorm : ∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (hW : ∀i x,‖W i x‖≤1) :
    gaussianPhysicalScaleMass C (Finset.univ : Finset (∀i,canonicalSlotSupport (T i)))
      (fun p=>compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J)
      (fun p=>Z^(17/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun p=>Z^(23/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun i : SelectedSlot J=>W i.val)
      (fun p i=>elementNorm (p i.val).val/Z^(ell i.val))≤
        (elementNorm C.generator*(128*max 1 b)^K)*Z := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hp (p : ∀i,canonicalSlotSupport (T i)) (i : Fin K) : (p i).val≠0 :=
    canonicalSlotSupport_nonzero _ (hT i) _ (p i).property
  have hterm (p : ∀i,canonicalSlotSupport (T i)) :
      ‖compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J‖*
        (∏i : SelectedSlot J,‖W i.val (elementNorm (p i.val).val/Z^(ell i.val))‖)*
        lowPhysicalScale C (Z^(17/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
          (Z^(23/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))≤
      elementNorm C.generator*Z^(5/6:ℝ) := by
    have hcoeff : ‖compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J‖*
        (∏i : SelectedSlot J,‖W i.val (elementNorm (p i.val).val/Z^(ell i.val))‖)≤1 := (mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _=>norm_nonneg _)) (compensationSubsetWeight_norm_le_one η W hW _ _ (hp p) J)).trans (Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun (i : SelectedSlot J) _=>hW i.val _))
    have hL := slotProduct_norm_ge_one _ (hp p) J
    rw [lowPhysicalScale_source C Z _ hz]
    apply (mul_le_of_le_one_left (by unfold elementNorm;positivity) hcoeff).trans
    exact div_le_self (by unfold elementNorm;positivity) (one_le_pow₀ hL)
  unfold gaussianPhysicalScaleMass
  apply (Finset.sum_le_sum (fun p _=>hterm p)).trans
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc := mul_le_mul_of_nonneg_right (canonicalTuple_count ell hell hsum b Z hZ T hT hnorm)
    (show 0≤elementNorm C.generator*Z^(5/6:ℝ) by unfold elementNorm;positivity)
  apply hc.trans_eq
  calc
    _=(elementNorm C.generator*(128*max 1 b)^K)*(Z^(1/6:ℝ)*Z^(5/6:ℝ)) := by ring
    _=_ := by rw [←Real.rpow_add hz];norm_num

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule2496

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowGaussianDyad
Source SHA256: 75b6ef5ee30a137c9ac18aff9807ca36657f33c8f868fc1e996ff02ffafeaf12
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2497




namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowCommonDyad {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slots : Fin K→Finset O) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (J : Finset (Fin K)) (X Y U R : ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) : ℂ :=
  ∫t : ℝ,(∑p : ∀i,slots i,compensationSubsetWeight η W Yp (fun i=>(p i).val) J*
    compensationRowTest η C W0 W1 (fun i=>(p i).val) J X Y U t*
      selectedSlotFactor W Yp (fun i=>(p i).val) J t)*gaussianJointDensity V hV (U/R) t

lemma lowCommonDyad_eq_family {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slots : Fin K→Finset O) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (J : Finset (Fin K)) (X Y U R : ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) :
    lowCommonDyad η C W0 W1 slots W Yp J X Y U R V hV=
    gaussianPhysicalFamilyIntegral η C W0 W1 (Finset.univ : Finset (∀i,slots i))
      (fun p=>compensationSubsetWeight η W Yp (fun i=>(p i).val) J)
      (fun p=>Ideal.span {slotProduct (fun i=>(p i).val) (Finset.univ\J)})
      (fun p=>X/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun p=>Y/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun i : SelectedSlot J=>W i.val)
      (fun p i=>elementNorm (p i.val).val/Yp i.val) V hV U R := rfl

lemma lowCommonDyad_norm_of_bound {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slots : Fin K→Finset O) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (J : Finset (Fin K)) (X Y U R B : ℝ) (degree : ℕ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ))
    (hb : ∀t : ℝ,‖∑p : ∀i,slots i,compensationSubsetWeight η W Yp (fun i=>(p i).val) J*
      compensationRowTest η C W0 W1 (fun i=>(p i).val) J X Y U t*
        selectedSlotFactor W Yp (fun i=>(p i).val) J t‖≤B*(1+‖t‖)^degree) :
    ‖lowCommonDyad η C W0 W1 slots W Yp J X Y U R V hV‖≤
      B*gaussianJointMoment V hV degree (U/R) := by
  let f := fun t : ℝ=>(∑p : ∀i,slots i,compensationSubsetWeight η W Yp (fun i=>(p i).val) J*
      compensationRowTest η C W0 W1 (fun i=>(p i).val) J X Y U t*
        selectedSlotFactor W Yp (fun i=>(p i).val) J t)*gaussianJointDensity V hV (U/R) t
  have hi := (JointLogSeparation.weighted_schwartz_integrable (gaussianJointDensity V hV (U/R)) degree).const_mul B
  have hmajor (t : ℝ) : ‖f t‖≤B*((1+‖t‖)^degree*‖gaussianJointDensity V hV (U/R) t‖) := by
    dsimp only [f]
    rw [norm_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hb t)
      (norm_nonneg (gaussianJointDensity V hV (U/R) t))
  have hh := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hmajor)
  simpa only [f,lowCommonDyad,gaussianJointMoment,integral_const_mul] using hh

theorem low_central_gaussian_dyad (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hM : 0≤M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(U : ℝ),0<U→
      Z^(1+lowSelectedLength ell J-ε/2)≤U→U≤Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
    ∀(V : SchwartzMap ℝ ℂ)(hV : HasCompactSupport (V:ℝ→ℂ)),
      ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
        W (fun i=>Z^(ell i)) J (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) U
          (Z^(1+lowSelectedLength ell J)) V hV‖≤
        C*Z^(3/16+254*ε)*gaussianJointMoment V hV degree (U/Z^(1+lowSelectedLength ell J)) := by
  obtain ⟨degree,C,hC,he⟩ := low_central_compensated_tuple η S hS hbad ell hell hsum
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
end OAIOriginalModule2497

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowGaussianRemote
Source SHA256: 1b8a49cf92868a2f64269607d0ef7edb1df20a04da83c27cd1a1985523987e42
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2498


namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma slotProduct_subtype {K : ℕ} (p : Fin K→O) (J : Finset (Fin K)) :
    slotProduct p J=∏i : J,p i.val := by rw [Finset.prod_coe_sort];rfl

lemma eventually_low_physical_scales {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (hsum : ∑i,ell i≤1/6) (b : ℝ) :
    ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
      ∀(slots : Fin K→Finset O),(∀i x,x∈slots i→x≠0)→
      (∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))→
      ∀(J : Finset (Fin K))(p : ∀i,slots i),
      1≤Z^(17/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J) ∧
      1≤Z^(23/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J) := by
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (show 0<(3/16:ℝ) by norm_num)).eventually
      (Filter.eventually_ge_atTop ((max 1 b)^K))] with Z hZ hc
  refine ⟨hZ,?_⟩
  intro slots hn hnorm J p
  have hl : 0<elementNorm (slotProduct (fun i=>(p i).val) J) :=
    slotProduct_norm_pos _ (fun i=>hn i _ (p i).property) J
  have hb := lowUnselectedProduct_norm_bound ell hell hsum (max 1 b) Z (le_max_left _ _) hZ.le
    slots (fun i n hm=>(hnorm i n hm).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
    J (fun i=>p i.val)
  rw [←slotProduct_subtype (fun i=>(p i).val) J] at hb
  have hLX : elementNorm (slotProduct (fun i=>(p i).val) J)≤Z^(17/48:ℝ) := by
    apply hb.trans
    calc
      _≤Z^(3/16:ℝ)*Z^(1/6:ℝ) := mul_le_mul_of_nonneg_right hc (by positivity)
      _=_ := by rw [←Real.rpow_add (lt_trans zero_lt_one hZ)];norm_num
  constructor
  · exact (one_le_div hl).mpr hLX
  · exact (one_le_div hl).mpr (hLX.trans
      (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)))

lemma low_remote_power (Z ell ε : ℝ) (N : ℕ) (hZ : 1≤Z) (hell : ell≤1/6)
    (hN : 13/3≤(ε/2)*(N:ℝ)) :
    Z*(Z^(1+ell))^2/(Z^(ε/2))^N≤Z^(-1:ℝ) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hsq : (Z^(1+ell))^2=Z^(2*(1+ell)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
    congr 1
    push_cast
    ring
  have hn : (Z^(ε/2))^N=Z^((ε/2)*(N:ℝ)) := by rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
  rw [hsq,hn,show Z*Z^(2*(1+ell))=Z^(1+2*(1+ell)) by rw [Real.rpow_add hz,Real.rpow_one],←Real.rpow_sub hz]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

def lowRemote (Z ell ε T : ℝ) : Prop :=
  T/Z^(1+ell)≤(Z^(ε/2))⁻¹ ∨ Z^(ε/2)≤T/Z^(1+ell)

theorem low_remote_gaussian_dyads (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (b ε : ℝ) (hε : 0<ε) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(η : HeckeFamily.Character)(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=>if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then
        ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
          W (fun i=>Z^(ell i)) J (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength ell J)) V hV‖ else 0
      Summable f ∧ (∑'j : ℕ,f j)≤C*Z^(-1:ℝ) := by
  have hep : 0<ε/2 := by linarith
  obtain ⟨N,hN⟩ := exists_nat_gt ((13/3:ℝ)/(ε/2))
  have hN' : (13/3:ℝ)≤(ε/2)*(N:ℝ) := by
    have hh := (div_lt_iff₀ hep).mp hN
    nlinarith
  obtain ⟨Cg,hCg,he⟩ := gaussianPhysicalFamily_remote_polynomial V hV N
    a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1
  let q := elementNorm (calibrationForSet S hS).generator
  let C0 := Cg*(q*(128*max 1 b)^K)
  have hq : 0<q := calibration_elementNorm_pos _
  refine ⟨C0,by dsimp [C0];positivity,?_⟩
  filter_upwards [eventually_low_physical_scales ell hell hsum b] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro η T hT hnorm J W hW
  dsimp only [lowRemote]
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  have hslots : ∀i n,n∈canonicalSlotSupport (T i)→n≠0 := fun i=>canonicalSlotSupport_nonzero _ (hT i)
  have hnormE : ∀i n,n∈canonicalSlotSupport (T i)→elementNorm n≤b*Z^(ell i) := by
    intro i n hn
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact hnorm i P hP
  have hs := hZ.2 _ hslots hnormE J
  have hh := he η S hS W0 W1
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0)
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    hW0 hW1 hWB0 hWB1 (Finset.univ : Finset (∀i,canonicalSlotSupport (T i)))
    (fun p=>compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J)
    (fun p=>Ideal.span {slotProduct (fun i=>(p i).val) (Finset.univ\J)})
    (fun p=>Z^(17/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
    (fun p=>Z^(23/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
    (fun p _=>(hs p).1) (fun p _=>(hs p).2)
    (fun i : SelectedSlot J=>W i.val) (fun p i=>elementNorm (p i.val).val/Z^(ell i.val))
    (Z^(1+lowSelectedLength ell J)) (Z^(ε/2)) (by positivity) (Real.one_le_rpow hZ.1.le hep.le)
  simp only [←lowCommonDyad_eq_family] at hh
  refine ⟨?_,?_⟩
  · convert hh.1 using 1
    funext j
    split_ifs with h <;> simp_all only [ite_true, ite_false]
  · have hhFinal := hh.2.trans (show _≤C0*Z^(-1:ℝ) from by
      have hm := compensation_scale_mass_bound η (calibrationForSet S hS) ell hell hsum b Z hZ.1.le T hT hnorm J W hW
      calc
        _≤Cg*((q*(128*max 1 b)^K)*Z)*(Z^(1+lowSelectedLength ell J))^2/(Z^(ε/2))^N := by gcongr
        _=C0*(Z*(Z^(1+lowSelectedLength ell J))^2/(Z^(ε/2))^N) := by dsimp [C0];ring
        _≤_ := mul_le_mul_of_nonneg_left (low_remote_power Z (lowSelectedLength ell J) ε N hZ.1.le
          (by have hb := lowLength_bounds ell hell hsum J;linarith) hN') (by dsimp [C0];positivity))
    convert hhFinal using 1
    apply tsum_congr
    intro j
    split_ifs with h <;> simp_all only [ite_true, ite_false]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule2498

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowGaussianCentral
Source SHA256: b283aa6bede21f0852977afe3fa894e9cff05b628c59abae4075efeb90c2f9b8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2499


namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma not_lowRemote_bounds (Z ell ε U : ℝ) (hZ : 0<Z)
    (h : ¬lowRemote Z ell ε U) :
    Z^(1+ell-ε/2)≤U ∧ U≤Z^(1+ell+ε/2) := by
  simp only [lowRemote,not_or,not_le] at h
  apply lowCentral_ratio_bounds Z U ell ε hZ
  · have he : Z^(-ε/2)=(Z^(ε/2))⁻¹ := by
      rw [show -ε/2=-(ε/2) by ring,Real.rpow_neg hZ.le]
    rw [he]
    exact h.1.le
  · exact h.2.le

theorem low_central_gaussian_dyads (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hM : 0≤M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=>if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then 0 else
        ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
          W (fun i=>Z^(ell i)) J (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength ell J)) V hV‖
      Summable f ∧ (∑'j : ℕ,f j)≤C*Z^(3/16+256*ε) := by
  obtain ⟨degree,C,hC,he⟩ := low_central_gaussian_dyad η S hS hbad ell hell hsum
    a b ε ha hε hε1 W0 W1 a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM
  obtain ⟨Cm,hCm,hm⟩ := gaussianJointMoment_summed V hV degree ε hε
  refine ⟨C*Cm,mul_pos hC hCm,?_⟩
  filter_upwards [he] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T hT hout hdis hnorm J W hW
  let R := Z^(1+lowSelectedLength ell J)
  let f := fun j : ℕ=>if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then 0 else
    ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
      W (fun i=>Z^(ell i)) J (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) ((2:ℝ)^j) R V hV‖
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  obtain ⟨hsm,hmb⟩ := hm R (by dsimp [R];positivity)
  have hb (j : ℕ) : f j≤(C*Z^(3/16+254*ε))*
      (((2:ℝ)^j)^ε*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) := by
    dsimp only [f]
    split_ifs with hj
    · exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (gaussianJointMoment_nonneg V hV degree _))
    · obtain ⟨hlo,hhi⟩ := not_lowRemote_bounds Z (lowSelectedLength ell J) ε ((2:ℝ)^j) hz hj
      apply (hZ.2 T hT hout hdis hnorm J ((2:ℝ)^j) (by positivity) hlo hhi W hW V hV).trans
      have hp : 1≤((2:ℝ)^j)^ε := Real.one_le_rpow (one_le_pow₀ (by norm_num)) hε.le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact le_mul_of_one_le_left (gaussianJointMoment_nonneg V hV degree _) hp
  have hn (j : ℕ) : 0≤f j := by dsimp [f];split_ifs <;>positivity
  have hsumf := Summable.of_nonneg_of_le hn hb (hsm.mul_left (C*Z^(3/16+254*ε)))
  refine ⟨hsumf,?_⟩
  calc
    _≤∑'j : ℕ,(C*Z^(3/16+254*ε))*(((2:ℝ)^j)^ε*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) :=
      hsumf.tsum_le_tsum hb (hsm.mul_left _)
    _=(C*Z^(3/16+254*ε))*(∑'j : ℕ,((2:ℝ)^j)^ε*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) := tsum_mul_left
    _≤(C*Z^(3/16+254*ε))*(Cm*R^ε) := mul_le_mul_of_nonneg_left hmb (by positivity)
    _≤_ := by
      dsimp only [R]
      rw [←Real.rpow_mul hz.le]
      calc
        _=(C*Cm)*(Z^(3/16+254*ε)*Z^((1+lowSelectedLength ell J)*ε)) := by ring
        _≤_ := by
          rw [←Real.rpow_add hz]
          apply mul_le_mul_of_nonneg_left _ (mul_pos hC hCm).le
          have hh := lowLength_bounds ell hell hsum J
          exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by nlinarith)

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule2499

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowGaussianSum
Source SHA256: 49657baf6a90f26fc2fda8654c53a3a65786030125130f0ede2c5fced7f12573
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2500


namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma low_dyad_norm_split (f : ℕ→ℂ) (p : ℕ→Prop) [DecidablePred p]
    (hc : Summable (fun j=>if p j then 0 else ‖f j‖))
    (hr : Summable (fun j=>if p j then ‖f j‖ else 0)) :
    Summable f ∧ ‖∑'j,f j‖≤(∑'j,if p j then 0 else ‖f j‖)+(∑'j,if p j then ‖f j‖ else 0) := by
  have he (j : ℕ) : ‖f j‖=(if p j then 0 else ‖f j‖)+(if p j then ‖f j‖ else 0) := by
    split_ifs <;>ring
  have hn : Summable (fun j=>‖f j‖) := (hc.add hr).congr (fun j=>(he j).symm)
  refine ⟨hn.of_norm,?_⟩
  apply (norm_tsum_le_tsum_norm hn).trans_eq
  exact (tsum_congr he).trans (hc.tsum_add hr)

theorem low_all_gaussian_dyads (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=>lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
          W (fun i=>Z^(ell i)) J (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength ell J)) V hV
      Summable f ∧ ‖∑'j : ℕ,f j‖≤C*Z^(3/16+256*ε) := by
  obtain ⟨Cc,hCc,hcentral⟩ := low_central_gaussian_dyads η S hS hbad ell hell hsum
    a b ε ha hε hε1 V hV W0 W1 a0 b0 a1 b1 B1 ha0 ha1 hab1 hB1 hW0 hW1 hW0s hW1s hWB1
  obtain ⟨Cr,hCr,hremote⟩ := low_remote_gaussian_dyads S hS ell hell hsum b ε hε V hV
    W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1 hW0 hW1 hWB0 hWB1
  refine ⟨Cc+Cr,add_pos hCc hCr,?_⟩
  filter_upwards [hcentral,hremote] with Z hc hr
  refine ⟨hc.1,?_⟩
  intro T hT hout hdis hnorm J W hW
  have hc' := hc.2 T hT hout hdis hnorm J W hW
  have hr' := hr.2 η T hT (fun i P hP=>(hnorm i P hP).2) J W hW
  dsimp only at hc' hr' ⊢
  have hh := low_dyad_norm_split _ (fun j=>lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j)) hc'.1 hr'.1
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hp : Z^(-1:ℝ)≤Z^(3/16+256*ε) := Real.rpow_le_rpow_of_exponent_le hc.1.le (by linarith)
  calc
    _≤Cc*Z^(3/16+256*ε)+Cr*Z^(-1:ℝ) := add_le_add hc'.2 hr'.2
    _≤Cc*Z^(3/16+256*ε)+Cr*Z^(3/16+256*ε) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hp hCr.le)
    _=_ := by ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule2500

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowCommonBound
Source SHA256: ea03172e8ef66b2fbd0ba0526704dbdfee44c241906d8c9bace5f3b84d636c22
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2501



namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma low_window_log_support (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Set.Icc a b) (y : ℝ) (hy : W (Real.exp y)≠0) :
    |y|≤|Real.log a|+|Real.log b| := by
  have hs := hW hy
  have hlo := Real.log_le_log ha hs.1
  have hhi := Real.log_le_log (Real.exp_pos y) hs.2
  rw [Real.log_exp] at hlo hhi
  exact abs_le.mpr ⟨by linarith [neg_abs_le (Real.log a),abs_nonneg (Real.log b)],
    by linarith [le_abs_self (Real.log b),abs_nonneg (Real.log a)]⟩

theorem compensatedPhysicalProbe_low (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
      ‖compensatedPhysicalProbe η (calibrationForSet S hS) W0 W1
        (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(ell i))
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖≤C*Z^(3/16+256*ε) := by
  obtain ⟨V,hV,hbudget,hidentity⟩ := compensatedPhysicalProbe_common_gaussian W
    (fun _=>|Real.log a|+|Real.log b|) (fun _=>by positivity)
    (fun i=>low_window_log_support (W i) a b ha (hW i))
  choose C hC he using fun A : Finset (Fin K)=>low_all_gaussian_dyads η S hS hbad ell hell hsum
    a b ε ha hε hε1 (V A) (hV A) W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  let C0 := (∑A∈(Finset.univ : Finset (Fin K)).powerset,C A)+1
  have hC0 : 0<C0 := by
    have hn := Finset.sum_nonneg (fun A (_ : A∈(Finset.univ : Finset (Fin K)).powerset)=>(hC A).le)
    dsimp only [C0]
    linarith
  refine ⟨C0,hC0,?_⟩
  filter_upwards [Filter.eventually_all.mpr he] with Z hZ
  have hz1 : 1<Z := (hZ ∅).1
  have hz : 0<Z := lt_trans zero_lt_one hz1
  refine ⟨hz1,?_⟩
  intro T hT hout hdis hnorm
  have hslots : ∀i n,n∈canonicalSlotSupport (T i)→n≠0 := fun i=>canonicalSlotSupport_nonzero _ (hT i)
  rw [hidentity η (calibrationForSet S hS) W0 W1
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0)
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    _ hslots (fun i=>Z^(ell i)) (fun i=>by positivity)
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (by positivity) (by positivity) hz]
  apply (norm_sum_le _ _).trans
  have hterm (A : Finset (Fin K)) :
      ‖∑'j : ℕ,lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i)) W
        (fun i=>Z^(ell i)) A (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) ((2:ℝ)^j)
        (Z*∏i∈Finset.univ\A,Z^(ell i)) (V A) (hV A)‖≤C A*Z^(3/16+256*ε) := by
    have hc : Z*(∏i∈Finset.univ\A,Z^(ell i))=Z^(1+lowSelectedLength ell A) := by
      rw [lowSelectedScale_product ell A Z hz,Real.rpow_add hz,Real.rpow_one]
    rw [hc]
    exact ((hZ A).2 T hT hout hdis hnorm A W hWnorm).2
  have hh := Finset.sum_le_sum (fun A (_ : A∈(Finset.univ : Finset (Fin K)).powerset)=>hterm A)
  apply hh.trans
  rw [←Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (by dsimp [C0];linarith) (Real.rpow_nonneg hz.le _)

theorem original_ray_compensatedPhysicalProbe_low (η : HeckeFamily.Character)
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hinj : Function.Injective ell)
    (hsum : ∑i,ell i≤1/6) (R : Set Id)
    (a b ε : ℝ) (ha : 0<a) (hab : a≤b) (hε : 0<ε) (hε1 : ε<1)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun i=>canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) W (fun i=>Z^(ell i))
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖≤C*Z^(3/16+256*ε) := by
  obtain ⟨C,hC,he⟩ := compensatedPhysicalProbe_low η S hmax hS.bad ell hell hsum
    a b ε ha hε hε1 W hW hWnorm W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  refine ⟨C,hC,?_⟩
  filter_upwards [he,ProbeRaySlots.power_pools_eventually_disjoint R S (fun _=>a) (fun _=>b) ell
    (fun _=>ha) (fun _=>hab) hinj] with Z hZ hd
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  apply hZ.2 _ (fun i=>ProbeRaySlots.pool_supported R S hS a b (Z^(ell i)))
    (fun i P hP=>((ProbeRaySlots.mem_pool R S a b (Z^(ell i)) P).mp hP).2.2.2)
    (fun i j hij=>hd i j hij)
  intro i P hP
  have hh := ProbeRaySlots.pool_norm_bounds R S ha.le hab (Real.rpow_pos_of_pos hz _) P hP
  simpa only [mul_comm] using And.intro hh.1.le hh.2

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule2501

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowWindowBound
Source SHA256: 680f8b3f8c85f574ba13982ea4962491fc47d163a0f10fb795aff7db948e3e18
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2502


namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma compensatedPhysicalProbe_window_scale {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slots : Fin K→Finset O) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (X Y Z : ℝ) (c : ℂ) :
    compensatedPhysicalProbe η C W0 W1 slots (fun i x=>c*W i x) Yp X Y Z=
      c^K*compensatedPhysicalProbe η C W0 W1 slots W Yp X Y Z := by
  unfold compensatedPhysicalProbe
  simp_rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_assoc]
  exact (Finset.mul_sum ..).symm

theorem original_ray_compensatedPhysicalProbe_low_loss
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hinj : Function.Injective ell)
    (hsum : ∑i,ell i≤1/6) (R : Set Id)
    (a b B loss : ℝ) (ha : 0<a) (hab : a≤b) (hloss : 0<loss)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤B)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∀η : HeckeFamily.Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun i=>canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) W (fun i=>Z^(ell i))
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖≤C*Z^(3/16+loss) := by
  let D := max 1 B
  have hD : 0<D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hDc : (D:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hD.ne'
  let Wn := fun i x=>W i x/(D:ℂ)
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
  have heloss : 256*ε≤loss := by have hh := min_le_left (loss/512) (1/2:ℝ);dsimp only [ε];linarith
  intro η
  obtain ⟨C,hC,hbound⟩ := original_ray_compensatedPhysicalProbe_low η S hS hmax ell hell hinj hsum R
    a b ε ha hab he he1 Wn hWn hn W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  refine ⟨D^K*C,by positivity,?_⟩
  filter_upwards [hbound,Filter.eventually_ge_atTop (1:ℝ)] with Z hb hZ
  have heq := compensatedPhysicalProbe_window_scale η (calibrationForSet S hmax) W0 W1
    (fun i=>canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) Wn (fun i=>Z^(ell i))
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (D:ℂ)
  rw [hscale] at heq
  rw [heq,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hD]
  calc
    _≤D^K*(C*Z^(3/16+256*ε)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _≤D^K*(C*Z^(3/16+loss)) := by gcongr
    _=_ := by ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule2502

/-! Original module: OAI.NumberTheory.DirichletL.Detector.RayPoolThresholds
Source SHA256: 0411f3084260288d0de442bb3f9cf17c55c90ea44e1506f0a5877ddbb8f9fe4d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2503



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical PrincipalSignalComparison ProbePrincipalResidueActual
local notation "Id" => Ideal HeckeFamily.O

theorem power_pool_thresholds {ι : Type*} [Fintype ι]
    (C : Set Id) (S : Finset Id) (η : Character) (c d ellMin : ℝ)
    (hc : 0<c) (hd : c≤d) (hmin : 0<ellMin)
    (ell : ι→ℝ) (hell : ∀j,ellMin≤ell j) :
    ∀ᶠZ : ℝ in atTop,
      1≤Z ∧ 480≤c*Z^ellMin ∧ 1440*(c*Z^ellMin)^(-(7/8:ℝ))≤1 ∧
      (∀j,480≤c*Z^(ell j) ∧ (η.modulus.absNorm:ℝ)<c*Z^(ell j)) ∧
      (∀j,∀P∈pool C S c d (Z^(ell j)),
        c*Z^ellMin≤(P.val.absNorm:ℝ) ∧ IsCoprime P.val η.modulus ∧ P.val∉S) := by
  have ht := (tendsto_rpow_atTop hmin).const_mul_atTop hc
  have hs : Tendsto (fun Z : ℝ=>1440*(c*Z^ellMin)^(-(7/8:ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero,Function.comp_def] using ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<7/8)).comp ht).const_mul (1440:ℝ)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually (eventually_ge_atTop (480:ℝ)),
    ht.eventually (eventually_gt_atTop (η.modulus.absNorm:ℝ)),
    hs.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with Z hZ h480 hmod hsmall
  have hZ0 : 0<Z := by linarith
  have hmono (j : ι) : c*Z^ellMin≤c*Z^(ell j) := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ (hell j)) hc.le
  refine ⟨hZ,h480,hsmall.le,fun j=>⟨h480.trans (hmono j),hmod.trans_le (hmono j)⟩,?_⟩
  intro j P hP
  have hp := pool_norm_bounds C S hc.le hd (Real.rpow_pos_of_pos hZ0 _) P hP
  have hn : c*Z^ellMin<(P.val.absNorm:ℝ) := (hmono j).trans_lt (by simpa only [mul_comm] using hp.1)
  exact ⟨hn.le,prime_coprime_of_norm_gt η P (hmod.trans hn),(mem_pool C S c d _ P).mp hP |>.2.2.2⟩

variable (M : Id) [NeZero M]
local instance : Finite (HeckeFamily.O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
include hH

theorem power_ray_mass_and_normalizer {ι : Type*} [Fintype ι]
    (S : Finset Id) (W : ι→ℝ→ℝ) (c d : ℝ) (hc : 0<c) (hd : c≤d)
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c d)
    (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hp : ∀j,tsupport (W j)⊆Set.Ioi 0) (hW0 : ∀j y,0≤W j y) (hne : ∀j,W j≠0)
    (ell : ι→ℝ) (hell : ∀j,0<ell j) (eps : ℝ) (heps : 0<eps) :
    ∀ᶠZ : ℝ in atTop,
      let T := fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
      (∀j,0<slotMass T (residueWeights W (fun j=>Z^(ell j))) j) ∧
      |(Probe.principalScalar Finset.univ Z (∑j,ell j)
        (slotMass T (residueWeights W (fun j=>Z^(ell j)))))⁻¹|≤Z^eps := by
  have hm : ∀ᶠZ : ℝ in atTop,∀j,0<slotMass
      (fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(ell j)))
      (residueWeights W (fun j=>Z^(ell j))) j := by
    apply Filter.eventually_all.mpr
    intro j
    exact (tendsto_rpow_atTop (hell j)).eventually
      (ray_pool_mass_eventually_positive M H hH S (W j) c d hc hd (hsupp j)
        (hW j) (hcompact j) (hp j) (hW0 j) (hne j))
  have hi := ProbeRayNormalization.ray_principalScalar_inverse_subpower M H hH Finset.univ S W
    (fun _=>c) (fun _=>d) ell (fun _ _=>hc) (fun _ _=>hd) (fun j _=>hsupp j)
    (fun j _=>hW j) (fun j _=>hcompact j) (fun j _=>hp j) (fun j _=>hW0 j) (fun j _=>hne j)
    (fun j _=>hell j) eps heps
  filter_upwards [hm,hi] with Z hmass hinv
  exact ⟨hmass,hinv⟩
end SevenEighths.ProbeRaySlots
end

end OAI
end OAIOriginalModule2503

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialDetectorSource
Source SHA256: 60842ed81b39c933ede65b0255bfeb6bbe6238dd41a753b3bdc8817aa33ebfa3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2504





namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexConjugate
namespace SevenEighths.InverseInitialDetectorSource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorCoefficientTransfer
open InverseInitialRawDictionary InverseInitialConjugateEnergy
local notation "O" => HeckeFamily.O

def baseCharacter (data : RowData) : Character := data.character ⟨1,one_ne_zero⟩

theorem baseCharacter_coeff (data : RowData) (I : Ideal O) :
    idealCoeff (baseCharacter data) I=fixedBase data.η data.m data.f I := by
  rw [HeckeRowClosure.idealCoeff_eq_row data.η (baseCharacter data) data.m data.f 1
    (data.character_spec ⟨1,one_ne_zero⟩),mul_one]
  rfl

theorem base_nonzero_prime (data : RowData) (P : Ideal O) (hP : Prime P)
    (hN : ((baseCharacter data).modulus.absNorm:ℝ)<(P.absNorm:ℝ)) :
    fixedBase data.η data.m data.f P≠0 := by
  rw [←baseCharacter_coeff]
  exact HeckeDetectorRelativePrime.idealCoeff_ne_zero_of_coprime _ P hP.ne_zero
    (ProbeRaySlots.prime_coprime_of_norm_gt (baseCharacter data) ⟨P,hP⟩ hN)

theorem character_eq_initial (data : RowData) (u : NonzeroElement)
    (W : ℝ→ℂ) (Z r σ freq b : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0 → x≤b) :
    polynomial (data.character u) true W (Z^r) σ freq=
      originalTotalPolynomial
        ((ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*b⌉₊).filter CanonicalQuadraticSieve.Supported)
        1 (fixedBase data.η data.m data.f) (fun _=>1)
        (twistedProfile W σ freq) Z r 0 u.val :=
  canonical_inverse_eq_supported_initial data.η (data.character u) data.m data.f u.val
    data.lambda_dvd data.two_dvd (data.character_spec u) W Z r σ freq b hZ hW

theorem oriented_character_norm_initial (data : RowData) (u : NonzeroElement)
    (χ : Character) (reverse : Bool)
    (hc : ∀I,idealCoeff χ I=if reverse then conj (idealCoeff (data.character u) I)
      else idealCoeff (data.character u) I)
    (W : ℝ→ℂ) (Z r σ freq b : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0 → x≤b) :
    ‖polynomial χ true W (Z^r) σ freq‖=
      ‖originalTotalPolynomial
        ((ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*b⌉₊).filter CanonicalQuadraticSieve.Supported)
        1 (fixedBase data.η data.m data.f) (fun _=>1)
        (twistedProfile (orientedProfile reverse W) σ (orientedFrequency reverse freq))
        Z r 0 u.val‖ := by
  rw [norm_of_oriented_coefficients χ (data.character u) reverse hc true W (Z^r) σ freq
    (Real.rpow_pos_of_pos hZ r)]
  rw [character_eq_initial data u (orientedProfile reverse W) Z r σ
    (orientedFrequency reverse freq) b hZ]
  intro x hx
  apply hW x
  intro hz
  exact hx (by cases reverse <;> simp [orientedProfile,hz])

def primeProfile (V : ℝ→ℂ) (D : ℝ) (ζ : ℂ) (P : Ideal O) : ℂ :=
  V ((P.absNorm:ℝ)/D)*(((P.absNorm:ℝ)/D:ℝ):ℂ)^(ζ-1)

theorem physical_slot_norm_initial (data : RowData) (u : NonzeroElement)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (W V : ℝ→ℂ) (Z r ell σ freq b bslot a : ℝ) (ζ : ℂ) (hZ : 0<Z)
    (hW : ∀x,W x≠0 → x≤b) (hV : ∀x,V x≠0 → a≤x)
    (hlarge : ((baseCharacter data).modulus.absNorm:ℝ)<a*Z^ell) :
    ‖polynomial (data.character u) true W (Z^r) σ freq*
      HeckePrimeRow.canonicalPrimeAmplitude M H u.val V bslot (Z^ell) ζ‖=
    ‖∑P∈(HeckePrimeAnnular.annulusSet bslot (Z^ell)).filter
        (fun P=>Prime P ∧ P∈RayQuotient.identityClass M H),
      (star (primeProfile V (Z^ell) ζ P)/fixedBase data.η data.m data.f P)*
        originalTotalPolynomial
          ((ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*b⌉₊).filter CanonicalQuadraticSieve.Supported)
          P (fixedBase data.η data.m data.f) (fun _=>1)
          (twistedProfile W σ freq) Z r ell u.val‖ := by
  let Pset := (HeckePrimeAnnular.annulusSet bslot (Z^ell)).filter
    (fun P=>Prime P ∧ P∈RayQuotient.identityClass M H)
  have hc := finite_source_cover W (Z^r) b (Real.rpow_pos_of_pos hZ r) hW
  have hbase (P : Ideal O) (hp : P∈Pset) (ha : primeProfile V (Z^ell) ζ P≠0) :
      fixedBase data.η data.m data.f P≠0 := by
    apply base_nonzero_prime data P (Finset.mem_filter.mp hp).2.1
    have hv : V ((P.absNorm:ℝ)/Z^ell)≠0 := by
      intro hz
      exact ha (by simp [primeProfile,hz])
    exact hlarge.trans_le ((le_div_iff₀ (Real.rpow_pos_of_pos hZ ell)).mp (hV _ hv))
  have he := inverse_times_conjugate_row_mark_norm (fixedBase data.η data.m data.f)
    (data.character u) u.val
    (fixedBase_row data.η (data.character u) data.m data.f u.val (data.character_spec u))
    W Z r ell σ freq hZ (ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*b⌉₊) Pset
    (primeProfile V (Z^ell) ζ) hbase hc
  have hp : HeckePrimeRow.canonicalPrimeAmplitude M H u.val V bslot (Z^ell) ζ=
      ((Z^(-ell/2):ℝ):ℂ)*∑P∈Pset,
        primeProfile V (Z^ell) ζ P*star (CanonicalRowCompletion.idealRowHom u.val P) := by
    unfold HeckePrimeRow.canonicalPrimeAmplitude
    rw [normalization_eq Z ell hZ]
    congr 1
    apply Finset.sum_congr rfl
    intro P hP
    change star (CanonicalRowCompletion.idealRowHom u.val P)*V _*_ =
      (V _*_)*star (CanonicalRowCompletion.idealRowHom u.val P)
    ring
  rw [hp,←mul_assoc,he]
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  rw [originalTotal_supported_source _ _ _
    (fixedBase_zero_unsupported data.η data.m data.f data.lambda_dvd data.two_dvd)]

end SevenEighths.InverseInitialDetectorSource

end

end OAI
end OAIOriginalModule2504

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseRawFourier
Source SHA256: e0731bd1892d2f24dbfdc4bda8afaa01f32e1aaa168d8023da37287c8eb7d0cd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2505



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory
namespace SevenEighths.DetectorDictionaryInverseRawFourier
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge InverseInitialRawDictionary
open InverseMoment InverseInitialClippedColumns InverseInitialOverlapFourier FourierBridge JointLogSeparation

private theorem child_cover (Wref : ℝ→ℂ) (b D : ℝ) (hD : 0<D)
    (hWref : ∀x,Wref x≠0 → x≤b) (s : ℝ) :
    ∀I : Ideal O,I≠0 → childLogTest Wref s ((I.absNorm:ℝ)/D)≠0 →
      I∈ConcretePrimeRowBridge.idealsUpTo ⌈D*b⌉₊ := by
  intro I hI hi
  apply finite_source_cover Wref D b hD hWref I hI
  intro hz
  exact hi (by simp [childLogTest,hz])

theorem polynomial_mode_integrable (χ : Character) (inv : Bool)
    (g : 𝓢(ℝ,ℂ)) (Wref : ℝ→ℂ) (b c θ D : ℝ) (hD : 0<D)
    (hWref : ∀x,Wref x≠0 → x≤b) :
    Integrable (fun v:ℝ=>density g (Real.log c) v*
      polynomial χ inv (childLogTest Wref (θ+v)) D 0 0) := by
  simp_rw [polynomial_eq_finite χ inv (childLogTest Wref (θ+_)) D 0 0
    (ConcretePrimeRowBridge.idealsUpTo ⌈D*b⌉₊) (child_cover Wref b D hD hWref _)]
  simp only [HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_zero,
    neg_zero,Complex.cpow_zero,mul_one,Finset.mul_sum]
  apply integrable_finsetSum
  intro I hI
  convert fourier_phase_integrable g
    (Real.log c+Real.log ((I.absNorm:ℝ)/D))
    ((D:ℂ)^(-(1/2:ℂ))*coefficient χ inv I*Wref ((I.absNorm:ℝ)/D)*
      logPhase θ (Real.log ((I.absNorm:ℝ)/D))) using 1
  funext v
  simp only [density,childLogTest,logPhase_add_frequency,logPhase_add]
  ring

theorem polynomial_clipped_fourier (χ : Character) (inv : Bool)
    (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Wref : ℝ→ℂ) (b c θ D : ℝ) (hc : 0<c) (hD : 0<D)
    (hWref : ∀x,Wref x≠0 → x≤b)
    (hagree : ∀y,0<y → Wref y*W (c*y)=W (c*y)) :
    polynomial χ inv (clippedTest W c θ) D 0 0=
      ∫v:ℝ,density (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW) (Real.log c) v*
        polynomial χ inv (childLogTest Wref (θ+v)) D 0 0 := by
  let S:=ConcretePrimeRowBridge.idealsUpTo ⌈D*b⌉₊
  have hcover : ∀I : Ideal O,I≠0 → clippedTest W c θ ((I.absNorm:ℝ)/D)≠0 → I∈S := by
    intro I hI hi
    have hIp : 0<(I.absNorm:ℝ)/D:=div_pos (by exact_mod_cast (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))) hD
    apply finite_source_cover Wref D b hD hWref I hI
    intro hz
    have he:=hagree _ hIp
    rw [hz,zero_mul] at he
    exact hi (by simp [clippedTest,childLogTest,←he])
  rw [polynomial_eq_finite χ inv (clippedTest W c θ) D 0 0 S hcover]
  simp_rw [polynomial_eq_finite χ inv (childLogTest Wref (θ+_)) D 0 0 S
    (child_cover Wref b D hD hWref _)]
  simp only [HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_zero,
    neg_zero,Complex.cpow_zero,mul_one,Finset.mul_sum]
  have hint (I : Ideal O) : Integrable (fun v:ℝ=>
      density (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW) (Real.log c) v*
        ((D:ℂ)^(-(1/2:ℂ))*(coefficient χ inv I*childLogTest Wref (θ+v) ((I.absNorm:ℝ)/D)))) := by
    convert fourier_phase_integrable (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)
      (Real.log c+Real.log ((I.absNorm:ℝ)/D))
      ((D:ℂ)^(-(1/2:ℂ))*coefficient χ inv I*Wref ((I.absNorm:ℝ)/D)*
        logPhase θ (Real.log ((I.absNorm:ℝ)/D))) using 1
    funext v
    simp only [density,childLogTest,logPhase_add_frequency,logPhase_add]
    ring
  rw [integral_finsetSum _ (fun I _=>hint I)]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hz : I=0
  · subst I
    simp only [coefficient_zero,zero_mul,mul_zero,integral_zero]
  have hIp : 0<(I.absNorm:ℝ)/D:=div_pos (by exact_mod_cast (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hz))) hD
  rw [clipped_test_fourier W lo hi hlo hs hW Wref c θ _ hc hIp (hagree _ hIp),
    ←integral_const_mul,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with v
  ring

end SevenEighths.DetectorDictionaryInverseRawFourier

end

end OAI
end OAIOriginalModule2505

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseRawEnergy
Source SHA256: 5c8ed5e967fd98ce8e65808ac7ade110af40473c3bbfab763d00170866663af6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2506



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory
namespace SevenEighths.DetectorDictionaryInverseRawFourier
open HeckeFamily HeckeDyadic InverseMoment InverseInitialClippedColumns
open InverseInitialOverlapFourier FourierBridge HeckeInverseAmplification

theorem polynomial_clipped_energy {ι : Type*} (rows : Finset ι)
    (χ : ι→Character) (inv : Bool) (A : ι→ℂ)
    (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Wref : ℝ→ℂ) (b c θ D E : ℝ) (J : ℕ) (hc : 0<c) (hD : 0<D) (hE : 0≤E)
    (hWref : ∀x,Wref x≠0 → x≤b)
    (hagree : ∀y,0<y → Wref y*W (c*y)=W (c*y))
    (he : ∀s, (∑i∈rows,‖polynomial (χ i) inv (childLogTest Wref s) D 0 0*A i‖^2)
      ≤E*(1+‖s‖)^(2*J)) :
    (∑i∈rows,‖polynomial (χ i) inv (clippedTest W c θ) D 0 0*A i‖^2)≤
      E*(1+‖θ‖)^(2*J)*
        (∫v:ℝ,(1+‖v‖)^J*‖(𝓕 (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)) v‖)^2 := by
  let g:=CubicReflectionKernel.logSchwartz W lo hi hlo hs hW
  let B:=density g (Real.log c)
  let φ : rows→ℝ→ℂ:=fun i v=>polynomial (χ i) inv (childLogTest Wref (θ+v)) D 0 0*A i
  have hint (i : rows) : Integrable (fun v:ℝ=>B v*φ i v) := by
    simpa only [B,φ,mul_assoc] using
      (polynomial_mode_integrable (χ i) inv g Wref b c θ D hD hWref).mul_const (A i)
  have hbound (v : ℝ) : (∑i:rows,‖φ i v‖^2)≤
      (E*(1+‖θ‖)^(2*J))*((1+‖v‖)^J)^2 := by
    dsimp only [φ]
    rw [Finset.sum_coe_sort rows (fun i=>‖polynomial (χ i) inv (childLogTest Wref (θ+v)) D 0 0*A i‖^2)]
    apply (he (θ+v)).trans
    have hh : 1+‖θ+v‖≤(1+‖θ‖)*(1+‖v‖) := by
      have hn:=norm_add_le θ v
      nlinarith [mul_nonneg (norm_nonneg θ) (norm_nonneg v)]
    calc
      _≤E*((1+‖θ‖)*(1+‖v‖))^(2*J):=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hh _) hE
      _= _:=by rw [mul_pow,pow_mul];ring
  have hden : Integrable (fun v:ℝ=>(1+‖v‖)^J*‖B v‖) := by
    simpa only [B,density_norm] using AnalyticBridge.schwartz_fourier_one_plus_integrable g J
  have hh:=CenteredMomentHeckeWindowEnergy.finite_weighted_integral_energy B φ
    (fun v:ℝ=>(1+‖v‖)^J) (by intro v;positivity)
    (E*(1+‖θ‖)^(2*J)) (by positivity) hden hint hbound
  have heq (i : rows) : (∫v:ℝ,B v*φ i v)=
      polynomial (χ i) inv (clippedTest W c θ) D 0 0*A i := by
    rw [polynomial_clipped_fourier (χ i) inv W lo hi hlo hs hW Wref b c θ D hc hD hWref hagree,
      ←integral_mul_const]
    apply integral_congr_ae
    filter_upwards with v
    dsimp [B,φ,g]
    ring
  simp_rw [heq] at hh
  rw [Finset.sum_coe_sort rows (fun i=>‖polynomial (χ i) inv (clippedTest W c θ) D 0 0*A i‖^2)] at hh
  simpa only [B,density_norm,g] using hh

theorem rawMoment_reference (data : RowData)
    (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Wref : ℝ→ℂ) (b c κ C : ℝ) (J : ℕ) (hC : 0≤C)
    (hWref : ∀x,Wref x≠0 → x≤b)
    (hagree : ∀y,0<y → Wref y*W y=W y)
    (he : ∀s,RawMoment data (childLogTest Wref s) c κ (C*(1+‖s‖)^(2*J))) :
    RawMoment data W c κ
      (C*(∫v:ℝ,(1+‖v‖)^J*‖(𝓕 (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)) v‖)^2) := by
  intro H D hH hD hHD rows hrows
  have hh:=polynomial_clipped_energy rows data.character true (fun _=>1)
    W lo hi hlo hs hW Wref b 1 0 D (C*H*(H*max 1 D)^κ) J (by norm_num) hD
    (by positivity) hWref (by simpa only [one_mul] using hagree) (by
      intro s
      have hb:=he s H D hH hD hHD rows hrows
      simpa only [mul_one,one_mul,mul_assoc,mul_left_comm,mul_comm] using hb)
  have heq : clippedTest W 1 0=W := by
    funext x
    simp [clippedTest,childLogTest,logPhase]
  rw [heq] at hh
  simpa only [mul_one,one_mul,norm_zero,add_zero,one_pow,mul_assoc,mul_left_comm,mul_comm] using hh

end SevenEighths.DetectorDictionaryInverseRawFourier

end

end OAI
end OAIOriginalModule2506

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseRawCompact
Source SHA256: 187dd0f0114c1693d264f45f5756b259570abd971fb726657770375c01278268
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2507



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.DetectorDictionaryInverseRawCompact
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment FourierBridge HeckePrimeAnnular
open CenteredMomentOriginalReflectionErrorMass CenteredMomentCounting
open ActualEisensteinCubic ConcreteTraceCRT

local notation "O" => HeckeFamily.O

lemma inverse_polynomial_all_ideals (χ : Character) (W : ℝ→ℂ) (D freq : ℝ) :
    polynomial χ true W D 0 freq =
      (D:ℂ)^(-(1/2:ℂ))*∑'I:Ideal O,coefficient χ true I*annularWeight W D 0 freq I := by
  unfold polynomial
  congr 1
  have he : (∑'I:HeckeDyadic.NonzeroIdeal,coefficient χ true I.val*annularWeight W D 0 freq I.val)=
      ∑'I:Ideal O,coefficient χ true I*annularWeight W D 0 freq I := by
    apply tsum_subtype_eq_of_support_subset (s:={I:Ideal O|I≠0})
      (f:=fun I:Ideal O=>coefficient χ true I*annularWeight W D 0 freq I)
    intro I hI hz
    subst I
    exact hI (by simp only [coefficient_zero,zero_mul])
  simpa only [summand,HeckeDyadic.norm,annularWeight,mul_assoc] using he

theorem inverse_polynomial_bound (χ : Character) (W : ℝ→ℂ) (b B D freq : ℝ)
    (hB : 0≤B) (hD : 0<D) (hW : ∀x,‖W x‖≤B)
    (hs : Function.support W⊆Set.Iic b) :
    ‖polynomial χ true W D 0 freq‖≤(128*max 1 b*B)*Real.sqrt D := by
  rw [inverse_polynomial_all_ideals]
  apply normalized_linear_bound D _ hD
  have hh:=norm_tsum_ideal_ball (fun I:Ideal O=>coefficient χ true I*annularWeight W D 0 freq I)
    (max 1 b*D) B (by positivity) hB (by
      change coefficient χ true (0:Ideal O)*_ = 0
      rw [coefficient_zero,zero_mul])
    (by
      intro I
      by_cases hI:I=0
      · subst I
        simpa only [coefficient_zero,zero_mul,norm_zero] using hB
      rw [norm_mul,annularWeight_zero_norm W D freq hD I hI]
      exact (mul_le_mul (coefficient_norm_le χ true I) (hW _) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul B))
    (by
      intro I hne
      have hw : W ((I.absNorm:ℝ)/D)≠0 := by
        intro hz
        exact hne (by simp only [annularWeight,hz,zero_mul,mul_zero])
      exact ((div_le_iff₀ hD).mp (hs hw)).trans
        (mul_le_mul_of_nonneg_right (le_max_right 1 b) hD.le))
  convert hh using 1; ring

lemma childLogTest_norm (W : ℝ→ℂ) (s x : ℝ) :
    ‖childLogTest W s x‖=‖W x‖ := by
  simp only [childLogTest,norm_mul,logPhase_norm,mul_one]

theorem inverse_reference_bound (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) :
    ∃A:ℝ,0<A ∧ ∀(χ:Character) (s D:ℝ),0<D →
      ‖polynomial χ true (childLogTest W s) D 0 0‖≤A*Real.sqrt D := by
  obtain ⟨B,hB,hbound⟩:=compact_norm_bound W a b ha hs W.continuous
  refine ⟨128*max 1 b*B,by positivity,?_⟩
  intro χ s D hD
  apply inverse_polynomial_bound χ (childLogTest W s) b B D 0 hB.le hD
  · intro x
    simpa only [childLogTest_norm] using hbound x
  · intro x hx
    have hw : W x≠0 := by
      intro hz
      exact hx (by simp only [childLogTest,hz,zero_mul])
    exact (hs hw).2

theorem nonzero_element_rows_card (rows : Finset NonzeroElement) (H : ℝ) (hH : 1≤H)
    (hrows : ∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) :
    (rows.card:ℝ)≤128*H := by
  have hh:=DescentFiberCost.finite_element_count_real (rows.image Subtype.val) H hH (by
    intro z hz
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact hrows v hv)
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
  exact hh

theorem reference_energy_linear (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) :
    ∃K:ℝ,0<K ∧ ∀(χ:NonzeroElement→Character) (rows:Finset NonzeroElement)
      (s H D:ℝ),1≤H → 0<D →
      (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) →
      (∑v∈rows,‖polynomial (χ v) true (childLogTest W s) D 0 0‖^2)≤K*H*D := by
  obtain ⟨A,hA,hbound⟩:=inverse_reference_bound W a b ha hs
  refine ⟨128*A^2,by positivity,?_⟩
  intro χ rows s H D hH hD hrows
  calc
    _≤∑v∈rows,A^2*D := by
      apply Finset.sum_le_sum
      intro v _
      have hh:=pow_le_pow_left₀ (norm_nonneg _) (hbound (χ v) s D hD) 2
      simpa only [mul_pow,Real.sq_sqrt hD.le] using hh
    _=(rows.card:ℝ)*(A^2*D) := by simp
    _≤(128*H)*(A^2*D) := mul_le_mul_of_nonneg_right
      (nonzero_element_rows_card rows H hH hrows) (by positivity)
    _=(128*A^2)*H*D := by ring

theorem subunit_rows_reference_energy (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) :
    ∃C0:ℝ,0<C0 ∧ ∀(χ:NonzeroElement→Character) (rows:Finset NonzeroElement)
      (s H D:ℝ),1≤H → 0<D → D≤1 →
      (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) →
      (∑v∈rows,‖polynomial (χ v) true (childLogTest W s) D 0 0‖^2)≤C0*H := by
  obtain ⟨K,hK,hbound⟩:=reference_energy_linear W a b ha hs
  refine ⟨K,hK,?_⟩
  intro χ rows s H D hH hD hD1 hrows
  exact (hbound χ rows s H D hH hD hrows).trans
    (mul_le_of_le_one_right (by positivity) hD1)

lemma scale_le_rows (c H D : ℝ) (hc : 0≤c) (hH : 1≤H)
    (_hD : 0<D) (hDH : D^(1+c)≤H) : D≤H := by
  by_cases hD1:D≤1
  · exact hD1.trans hH
  · have hd : 1≤D := le_of_not_ge hD1
    calc
      D=D^(1:ℝ) := (Real.rpow_one D).symm
      _≤D^(1+c) := Real.rpow_le_rpow_of_exponent_le hd (by linarith)
      _≤H := hDH

theorem small_rows_reference_energy (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (H0 : ℝ) (hH0 : 1≤H0) :
    ∃C0:ℝ,0<C0 ∧ ∀(χ:NonzeroElement→Character) (rows:Finset NonzeroElement)
      (s H D c:ℝ),1≤H → H≤H0 → 0≤c → 0<D → D^(1+c)≤H →
      (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) →
      (∑v∈rows,‖polynomial (χ v) true (childLogTest W s) D 0 0‖^2)≤C0*H := by
  obtain ⟨K,hK,hbound⟩:=reference_energy_linear W a b ha hs
  refine ⟨K*H0,by positivity,?_⟩
  intro χ rows s H D c hH hHH0 hc hD hDH hrows
  calc
    _≤K*H*D := hbound χ rows s H D hH hD hrows
    _≤K*H*H0 := mul_le_mul_of_nonneg_left ((scale_le_rows c H D hc hH hD hDH).trans hHH0)
      (by positivity)
    _=(K*H0)*H := by ring

lemma raw_majorant_ge_linear (C C0 H D κ s : ℝ) (J : ℕ)
    (hC : 0≤C) (hC0 : 0≤C0) (hH : 1≤H) (hκ : 0≤κ) :
    C0*H≤((C+C0)*(1+‖s‖)^(2*J))*H*(H*max 1 D)^κ := by
  have ht : 1≤(1+‖s‖)^(2*J) := one_le_pow₀ (by linarith [norm_nonneg s])
  have hb : 1≤H*max 1 D := hH.trans
    (le_mul_of_one_le_right (by positivity) (le_max_left _ _))
  have hp : 1≤(H*max 1 D)^κ := Real.one_le_rpow hb hκ
  calc
    C0*H≤(C+C0)*H := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _≤((C+C0)*(1+‖s‖)^(2*J))*H := mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (by positivity) ht) (by positivity)
    _≤_ := le_mul_of_one_le_right (by positivity) hp

theorem rawMoment_of_large_rows_ge_one (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (H0 : ℝ) (hH0 : 1≤H0) :
    ∃C0:ℝ,0<C0 ∧ ∀(data:RowData) (c κ C:ℝ) (J:ℕ),
      0≤c → 0≤κ → 0≤C →
      (∀(s H D:ℝ),H0≤H → 1≤D → D^(1+c)≤H →
        ∀rows:Finset NonzeroElement,
          (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) →
          (∑v∈rows,‖polynomial (data.character v) true (childLogTest W s) D 0 0‖^2)≤
            (C*(1+‖s‖)^(2*J))*H*(H*max 1 D)^κ) →
      ∀s:ℝ,RawMoment data (childLogTest W s) c κ ((C+C0)*(1+‖s‖)^(2*J)) := by
  obtain ⟨K,hK,hbound⟩:=reference_energy_linear W a b ha hs
  refine ⟨K*H0,by positivity,?_⟩
  intro data c κ C J hc hκ hC hlarge s H D hH hD hDH rows hrows
  have hsmall (hDH0:D≤H0) :
      (∑v∈rows,‖polynomial (data.character v) true (childLogTest W s) D 0 0‖^2)≤
        ((C+K*H0)*(1+‖s‖)^(2*J))*H*(H*max 1 D)^κ := by
    calc
      _≤K*H*D := hbound data.character rows s H D hH hD hrows
      _≤K*H*H0 := mul_le_mul_of_nonneg_left hDH0 (by positivity)
      _=(K*H0)*H := by ring
      _≤_ := raw_majorant_ge_linear C (K*H0) H D κ s J hC (by positivity) hH hκ
  by_cases hHH0:H≤H0
  · exact hsmall ((scale_le_rows c H D hc hH hD hDH).trans hHH0)
  by_cases hD1:D≤1
  · exact hsmall (hD1.trans hH0)
  · apply (hlarge s H D (le_of_not_ge hHH0) (le_of_not_ge hD1) hDH rows hrows).trans
    gcongr
    exact le_add_of_nonneg_right (by positivity)

theorem rawMoment_of_large_rows (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (H0 : ℝ) (hH0 : 1≤H0) :
    ∃C0:ℝ,0<C0 ∧ ∀(data:RowData) (c κ C:ℝ) (J:ℕ),
      0≤c → 0≤κ → 0≤C →
      (∀(s H D:ℝ),H0≤H → 0<D → D^(1+c)≤H →
        ∀rows:Finset NonzeroElement,
          (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) →
          (∑v∈rows,‖polynomial (data.character v) true (childLogTest W s) D 0 0‖^2)≤
            (C*(1+‖s‖)^(2*J))*H*(H*max 1 D)^κ) →
      ∀s:ℝ,RawMoment data (childLogTest W s) c κ ((C+C0)*(1+‖s‖)^(2*J)) := by
  obtain ⟨C0,hC0,hcomplete⟩:=rawMoment_of_large_rows_ge_one W a b ha hs H0 hH0
  refine ⟨C0,hC0,?_⟩
  intro data c κ C J hc hκ hC hlarge
  apply hcomplete data c κ C J hc hκ hC
  intro s H D hH hD hDH rows hrows
  exact hlarge s H D hH (zero_lt_one.trans_le hD) hDH rows hrows

end SevenEighths.DetectorDictionaryInverseRawCompact

end

end OAI
end OAIOriginalModule2507

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseRawRadial
Source SHA256: 10e9ccaaa23bb1ddae66bc3e0bdba5873bbd76f081a0003742ae8ceba36e0065
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2508



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.DetectorDictionaryInverseRawRadial
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialConjugateEnergy CanonicalQuadraticSieve
open ConcreteTraceCRT ActualEisensteinCubic
local notation "O"=>HeckeFamily.O

theorem exists_raw_radial_majorant :
    ∃Φ : 𝓢(ℝ,ℂ),HasCompactSupport (Φ:ℝ→ℂ) ∧
      (∀x,0≤(Φ x).re) ∧ (∀x∈Set.Icc (0:ℝ) 1,Φ x=1) := by
  have hsub : Set.Icc (0:ℝ) 1⊆Set.Ioo (-1) 2 := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  obtain ⟨f,hf,_,hs,hone⟩:=exists_contDiff_support_eq_eq_one_iff
    (n:=⊤) isOpen_Ioo isClosed_Icc hsub
  let v : ℝ→ℂ:=fun x=>((f x)^2:ℝ)
  have hv : ContDiff ℝ ∞ v:=Complex.ofRealCLM.contDiff.comp
    ((by simpa using hf : ContDiff ℝ ∞ f).pow 2)
  have hsupp : Function.support v⊆Set.Icc (-1) 2 := by
    intro x hx
    have hn : x∈Function.support f := by
      intro hz
      exact hx (by simp [v,hz])
    rw [hs] at hn
    exact ⟨hn.1.le,hn.2.le⟩
  have hvc:=HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  refine ⟨hvc.toSchwartzMap hv,hvc,?_,?_⟩
  · intro x
    change 0≤(f x)^2
    positivity
  · intro x hx
    change (((f x)^2:ℝ):ℂ)=1
    rw [(hone x).mp hx]
    norm_num

private theorem admissible_one : Admissible (1:Ideal O) := by
  refine ⟨one_ne_zero,squarefree_one,?_⟩
  simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero,false_implies,forall_const]

theorem finite_raw_le_initial_smoothed (Φ : 𝓢(ℝ,ℂ))
    (hΦ : ∀x,0≤(Φ x).re) (hone : ∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (data : RowData) (W : ℝ→ℂ) (b Z r σ t H : ℝ)
    (hZ : 0<Z) (hH : 0<H) (hW : ∀x,W x≠0 → x≤b)
    (rows : Finset NonzeroElement)
    (hrows : ∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤H) :
    (∑u∈rows,‖polynomial (data.character u) true W (Z^r) σ t‖^2)≤
      smoothedEnergy Φ H
        (originalTotalPolynomial
          ((ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*b⌉₊).filter Supported)
          1 (fixedBase data.η data.m data.f) (fun _=>1)
          (twistedProfile W σ t) Z r 0) := by
  let S:=(ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*b⌉₊).filter Supported
  let f:=originalTotalPolynomial S 1 (fixedBase data.η data.m data.f) (fun _=>1)
    (twistedProfile W σ t) Z r 0
  have hsum : Summable (fun u:O=>radialWeight Φ H u*‖f u‖^2) :=
    (original_smoothed_overlap_triangle S admissible_one
      (fun n hn _=>(Finset.mem_filter.mp hn).2) (fixedBase data.η data.m data.f)
      (fun _=>1) (twistedProfile W σ t) hZ r 0 (fun _=>0) Φ (fun x _=>hΦ x) hH).1
  have he (u : NonzeroElement) (hu : u∈rows) :
      ‖polynomial (data.character u) true W (Z^r) σ t‖^2=
        radialWeight Φ H u.val*‖f u.val‖^2 := by
    have hn : ‖eisEmbedding u.val‖^2/H∈Set.Icc (0:ℝ) 1 := by
      refine ⟨div_nonneg (sq_nonneg _) hH.le,?_⟩
      apply (div_le_one hH).mpr
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact hrows u hu
    rw [character_eq_initial data u W Z r σ t b hZ hW]
    change ‖f u.val‖^2=(Φ (‖eisEmbedding u.val‖^2/H)).re*‖f u.val‖^2
    rw [hone _ hn,Complex.one_re,one_mul]
  calc
    _=∑u∈rows,radialWeight Φ H u.val*‖f u.val‖^2:=Finset.sum_congr rfl he
    _=∑u∈rows.image Subtype.val,radialWeight Φ H u*‖f u‖^2:=by
      rw [Finset.sum_image (fun a _ b _ hab=>Subtype.val_injective hab)]
    _≤∑'u:O,radialWeight Φ H u*‖f u‖^2:=hsum.sum_le_tsum _
      (fun u _=>mul_nonneg (hΦ _) (sq_nonneg _))
    _= _:=rfl

end SevenEighths.DetectorDictionaryInverseRawRadial

end

end OAI
end OAIOriginalModule2508

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseRawInitialGates
Source SHA256: afd285280ae96eb3829e453d356a18ac061e2b86b640c53c8768aada0c6f9c62
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2509





namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap Topology
open Filter
namespace SevenEighths.DetectorDictionaryInverseRawInitialGates
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialRayAttachment InverseInitialExcludedPeriod
open InverseInitialExcludedPool InverseInitialExcludedOverlap InverseInitialExcludedPolynomial
open CanonicalRowCompletion CanonicalCoefficientClass CanonicalQuadraticSieve ConcreteTraceCRT
open ConcretePrimeRowBridge UniqueFactorizationMonoid IdealMobiusDivisorSum
open DetectorDictionaryInverseRawGeometry
local notation "O"=>HeckeFamily.O

def basePeriod (data:RowData):ℕ:=(baseCharacter data).period

def excluded (data:RowData):Finset (Ideal O):=reflectionExcludedPrimes (basePeriod data)

def deletedBase (data:RowData):Character:=
  (baseCharacter data).excludePrimes (excluded data) (reflectionExcludedPrimes_prime (basePeriod data))

theorem basePeriod_ne_zero (data:RowData):basePeriod data≠0:=Nat.ne_of_gt (Character.period_pos _)

theorem basePeriod_le (data:RowData):Ideal.span {(basePeriod data:O)}≤(baseCharacter data).modulus:=
  Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Character.period_mem _))

theorem raw_base_gates (data:RowData):
    deletedPeriod (basePeriod data)≠0 ∧
    reflectionExcludedPrimes (deletedPeriod (basePeriod data))=excluded data ∧
    (∀x,‖elementCharacter (idealCoeff (deletedBase data)).toMonoidHom x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod (basePeriod data)))
      (elementCharacter (idealCoeff (deletedBase data)).toMonoidHom):=
  deleted_physical_base_gates (baseCharacter data) (basePeriod data)
    (basePeriod_ne_zero data) (basePeriod_le data)

theorem actual_row_fixed_base (data:RowData)(u:NonzeroElement)(I:Ideal O):
    idealCoeff (data.character u) I=idealCoeff (baseCharacter data) I*idealRowHom u.val I:=by
  rw [baseCharacter_coeff]
  exact fixedBase_row data.η (data.character u) data.m data.f u.val (data.character_spec u) I

theorem actual_deleted_row (data:RowData)(u:NonzeroElement)(I:Ideal O):
    idealCoeff ((data.character u).excludePrimes (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data))) I=
      idealCoeff (deletedBase data) I*idealRowHom u.val I:=by
  unfold deletedBase excluded
  rw [idealCoeff_excludePrimes,idealCoeff_excludePrimes,actual_row_fixed_base]
  split_ifs <;> simp

def completeCutoff (H b Btree cap:ℝ):ℕ:=⌈max (Btree*H^(cap+1)) (b*H)⌉₊

theorem completeCutoff_tree (H b Btree cap:ℝ):
    Btree*H^(cap+1)≤(completeCutoff H b Btree cap:ℝ):=
  (le_max_left _ _).trans (Nat.le_ceil _)

theorem completeCutoff_columns (H b Btree cap D n:ℝ)(hb:0≤b)(hD:0≤D)
    (hDH:D≤H)(hn:1≤n):b*(D/n)≤(completeCutoff H b Btree cap:ℝ):=by
  have hn0:0<n:=zero_lt_one.trans_le hn
  have hdn:D/n≤D:=(div_le_iff₀ hn0).mpr (le_mul_of_one_le_right hD hn)
  exact (mul_le_mul_of_nonneg_left (hdn.trans hDH) hb).trans
    ((le_max_right _ _).trans (Nat.le_ceil _))

theorem excluded_divisor_norm (data:RowData)(j:Ideal O)
    (hj:j∈idealDivisors (∏P∈excluded data,P)):
    1≤(j.absNorm:ℝ) ∧ (j.absNorm:ℝ)≤((∏P∈excluded data,P).absNorm:ℝ):=by
  have hP:Squarefree (∏P∈excluded data,P):=
    prime_product_squarefree _ (reflectionExcludedPrimes_prime (basePeriod data))
  have hd: j∣∏P∈excluded data,P:=(mem_idealDivisors hP.ne_zero).mp hj
  have hj0:=ne_zero_of_dvd_ne_zero hP.ne_zero hd
  constructor
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj0)
  · exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero)) (map_dvd Ideal.absNorm hd)

theorem shifted_raw_geometry_eventually (data:RowData)(c eta:ℝ)(hc:0<c)(heta:0<eta):
    ∀ᶠH:ℝ in atTop,1<H ∧ ∀D:ℝ,1≤D→D^(1+c)≤H→
      ∀j∈idealDivisors (∏P∈excluded data,P),
      let r:=Real.logb H (D/(j.absNorm:ℝ));
      -eta≤r ∧ r≤1-capacityGap c ∧ 2*r≤3-capacityGap c ∧
      H^r=D/(j.absNorm:ℝ) ∧ r+7*eta≤1+7*eta ∧ D≤H:=by
  have ht:∀ᶠH:ℝ in atTop,((∏P∈excluded data,P).absNorm:ℝ)≤H^eta:=
    (tendsto_rpow_atTop heta).eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1:ℝ),ht] with H hH ht
  refine ⟨hH,?_⟩
  intro D hD hcap j hj r
  obtain ⟨hn,hnB⟩:=excluded_divisor_norm data j hj
  have hH0:0<H:=zero_lt_one.trans hH
  have hD0:0<D:=zero_lt_one.trans_le hD
  have hn0:0<(j.absNorm:ℝ):=zero_lt_one.trans_le hn
  obtain ⟨hr0,hr1,hr2,hex⟩:=raw_log_capacity H D c hH hD hc hcap
  have hr:r=Real.logb H D-Real.logb H (j.absNorm:ℝ):=
    Real.logb_div hD0.ne' hn0.ne'
  have hnlog:0≤Real.logb H (j.absNorm:ℝ):=
    div_nonneg (Real.log_nonneg hn) (Real.log_pos hH).le
  have hneta:Real.logb H (j.absNorm:ℝ)≤eta:=by
    exact (Real.logb_le_iff_le_rpow hH hn0).mpr (hnB.trans ht)
  have hrlo:-eta≤r:=by rw [hr];linarith
  have hrup:r≤1-capacityGap c:=by rw [hr];linarith
  refine ⟨hrlo,hrup,by rw [hr];linarith,
    Real.rpow_logb hH0 hH.ne' (div_pos hD0 hn0),?_,?_⟩
  · linarith [(capacityGap_pos c hc).le]
  · calc
      D=H^(Real.logb H D):=hex.symm
      _≤H^1:=Real.rpow_le_rpow_of_exponent_le hH.le (by linarith [(capacityGap_pos c hc).le])
      _=H:=Real.rpow_one _

theorem deleted_row_complete_polynomial (data:RowData)(u:NonzeroElement)
    (W:ℝ→ℂ)(H r sigma freq b:ℝ)(hH:0<H)
    (hW:∀x,W x≠0→x≤b)(Dpool:ℕ)(hbudget:b*H^r≤(Dpool:ℝ)):
    polynomial ((data.character u).excludePrimes (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data))) true W (H^r) sigma freq=
      InverseInitialConjugateEnergy.originalTotalPolynomial
        (InitialMeanSquare.outsideSquarefreeIdeals (excluded data) Dpool) 1
        (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1)
        (twistedProfile W sigma freq) H r 0 u.val:=by
  let χ:=(data.character u).excludePrimes (excluded data)
    (reflectionExcludedPrimes_prime (basePeriod data))
  let F:=InitialMeanSquare.outsideSquarefreeIdeals (excluded data) Dpool
  have hs:(∑'I:Ideal O,(moebius I:ℂ)*idealCoeff χ I*
      (W ((I.absNorm:ℝ)/H^r)*(((I.absNorm:ℝ)/H^r:ℝ):ℂ)^(-HeckeDyadic.shift sigma freq)))=
      ∑I∈F,(moebius I:ℂ)*idealCoeff χ I*
        (W ((I.absNorm:ℝ)/H^r)*(((I.absNorm:ℝ)/H^r:ℝ):ℂ)^(-HeckeDyadic.shift sigma freq)):=by
    apply tsum_eq_sum
    intro I hn
    by_cases hsq:Squarefree I
    · by_cases hout:outside (excluded data) I
      · by_cases hw:W ((I.absNorm:ℝ)/H^r)=0
        · simp only [hw,zero_mul,mul_zero]
        · have hN:(I.absNorm:ℝ)≤(Dpool:ℝ):=
            ((div_le_iff₀ (Real.rpow_pos_of_pos hH r)).mp (hW _ hw)).trans hbudget
          have hmem:I∈F:=by
            apply Finset.mem_filter.mpr
            refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,?_,hout⟩,hsq⟩
            · exact Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hsq.ne_zero)
            · exact_mod_cast hN
          exact False.elim (hn hmem)
      · have hz:=deleted_zero_outside (data.character u) (excluded data)
          (reflectionExcludedPrimes_prime (basePeriod data)) I hout
        simp only [χ,hz,mul_zero,zero_mul]
    · simp only [moebius_of_not_squarefree hsq,Int.cast_zero,zero_mul]
  rw [polynomial_all_ideals,hs,normalization_eq H r hH]
  unfold InverseInitialConjugateEnergy.originalTotalPolynomial
  simp only [add_zero,map_one,mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [actual_deleted_row]
  simp only [twistedProfile,InverseInitialPoissonBridge.heckeIdealCharacter_apply]
  change (moebius I:ℂ) * (idealCoeff (deletedBase data) I * idealRowHom u.val I) *
      (W ((I.absNorm:ℝ)/H^r)*(((I.absNorm:ℝ)/H^r:ℝ):ℂ)^(-shift sigma freq)) =
    (moebius I:ℂ) * (idealCoeff (deletedBase data) I * idealRowHom u.val I) *
      (W ((I.absNorm:ℝ)/H^r)*(((I.absNorm:ℝ)/H^r:ℝ):ℂ)^(-shift sigma freq))
  ring

theorem raw_complete_pool (data:RowData)(H D c b Btree cap:ℝ)
    (hH:1<H)(hD:1≤D)(hc:0<c)(hcap:D^(1+c)≤H)(hb:0≤b)
    (W:ℝ→ℂ)(hW:∀x,W x≠0→x≤b):
    Btree*H^(cap+1)≤(completeCutoff H b Btree cap:ℝ) ∧
    ∀j∈idealDivisors (∏P∈excluded data,P),∀u:NonzeroElement,∀sigma freq:ℝ,
      polynomial ((data.character u).excludePrimes (excluded data)
        (reflectionExcludedPrimes_prime (basePeriod data))) true W
        (D/(j.absNorm:ℝ)) sigma freq=
      InverseInitialConjugateEnergy.originalTotalPolynomial
        (InitialMeanSquare.outsideSquarefreeIdeals (excluded data)
          (completeCutoff H b Btree cap)) 1
        (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1)
        (twistedProfile W sigma freq) H (Real.logb H (D/(j.absNorm:ℝ))) 0 u.val:=by
  refine ⟨completeCutoff_tree _ _ _ _,?_⟩
  intro j hj u sigma freq
  have hn:= (excluded_divisor_norm data j hj).1
  have hH0:0<H:=zero_lt_one.trans hH
  have hD0:0<D:=zero_lt_one.trans_le hD
  have hn0:0<(j.absNorm:ℝ):=zero_lt_one.trans_le hn
  have hex:=Real.rpow_logb hH0 hH.ne' (div_pos hD0 hn0)
  obtain ⟨_,hr,_,heD⟩:=raw_log_capacity H D c hH hD hc hcap
  have hDH:D≤H:=by
    calc
      D=H^(Real.logb H D):=heD.symm
      _≤H^1:=Real.rpow_le_rpow_of_exponent_le hH.le
        (by linarith [(capacityGap_pos c hc).le])
      _=H:=Real.rpow_one _
  have hbudget:b*H^(Real.logb H (D/(j.absNorm:ℝ)))≤
      (completeCutoff H b Btree cap:ℝ):=by
    rw [hex]
    exact completeCutoff_columns H b Btree cap D _ hb hD0.le hDH hn
  simpa only [hex] using deleted_row_complete_polynomial data u W H
    (Real.logb H (D/(j.absNorm:ℝ))) sigma freq b hH0 hW _ hbudget

end SevenEighths.DetectorDictionaryInverseRawInitialGates

end

end OAI
end OAIOriginalModule2509

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseRawConjugateGates
Source SHA256: f707928da4d745a99bda52f5842be3bce13975892dd879541d618eb044ce9b5a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2510



namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseRawConjugateGates
open CanonicalRowCompletion
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialConjugateEnergy
open InverseInitialRayAttachment InverseInitialExcludedPeriod CanonicalCoefficientClass
open DetectorDictionaryInverseRawInitialGates InverseInitialExcludedPool
open InverseInitialExcludedOverlap InverseMoment InverseInitialProfile
local notation "O"=>HeckeFamily.O

theorem conjugate_element_apply (η:Ideal O→*ℂ)(x:O):
    elementCharacter (conjugateIdealCharacter η) x=star (elementCharacter η x):=rfl

theorem conjugate_element_factors (η:Ideal O→*ℂ)(Q:Ideal O)
    (h:FactorsModulo Q (elementCharacter η)):
    FactorsModulo Q (elementCharacter (conjugateIdealCharacter η)):=by
  intro x y hxy
  exact congrArg star (h x y hxy)

theorem conjugate_element_norm (η:Ideal O→*ℂ)(x:O):
    ‖elementCharacter (conjugateIdealCharacter η) x‖=‖elementCharacter η x‖:=by
  rw [conjugate_element_apply,norm_star]

theorem raw_conjugate_base_gates (data:RowData):
    deletedPeriod (basePeriod data)≠0 ∧
    reflectionExcludedPrimes (deletedPeriod (basePeriod data))=excluded data ∧
    (∀x,‖elementCharacter (conjugateIdealCharacter
      (idealCoeff (deletedBase data)).toMonoidHom) x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod (basePeriod data)))
      (elementCharacter (conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom)):=by
  obtain ⟨hq,he,hn,hp⟩:=raw_base_gates data
  refine ⟨hq,he,?_,conjugate_element_factors _ _ hp⟩
  intro x
  rw [conjugate_element_norm]
  exact hn x

theorem raw_conjugate_zero_outside (data:RowData)(I:Ideal O)
    (hI:¬outside (excluded data) I):
    conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom I=0:=by
  change star (idealCoeff (deletedBase data) I)=0
  rw [show idealCoeff (deletedBase data) I=0 from
    deleted_zero_outside (InverseInitialDetectorSource.baseCharacter data)
      (excluded data) (reflectionExcludedPrimes_prime (basePeriod data)) I hI,star_zero]

theorem childLogTest_conjugate (W:ℝ→ℂ)(θ:ℝ):
    (fun x=>star (childLogTest W θ x))=childLogTest (fun x=>star (W x)) (-θ):=by
  funext x
  simp only [childLogTest,star_mul,SecondPassIntegration.logPhase_conjugate]
  ring

theorem childLogTest_conjugate_norm (W:ℝ→ℂ)(θ x:ℝ):
    ‖childLogTest (fun x=>star (W x)) (-θ) x‖=‖W x‖:=by
  rw [InverseInitialProfileBounds.childLogTest_norm,norm_star]

theorem childLogTest_physical_profiles (W:ℝ→ℂ)(θ:ℝ):
    (fun x=>star (childLogTest W θ x))=clippedSource (fun x=>star (W x)) 1 (-θ) ∧
    childLogTest W θ=clippedSource W 1 θ:=by
  rw [childLogTest_conjugate]
  exact ⟨InverseInitialProfileBounds.childLogTest_eq_clipped _ _,
    InverseInitialProfileBounds.childLogTest_eq_clipped _ _⟩

end SevenEighths.DetectorDictionaryInverseRawConjugateGates

end

end OAI
end OAIOriginalModule2510

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseRawInitialEnergy
Source SHA256: 6ff17a5d4c32007bd82bfe00effe6e8244fe87e8577d8fc6d3a429b8a3971584
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2511



namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.DetectorDictionaryInverseRawInitialEnergy
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialConjugateEnergy
open InverseInitialRawDictionary InverseInitialExcludedPolynomial InverseInitialExcludedEnergy
open DetectorDictionaryInverseRawInitialGates CanonicalQuadraticSieve ConcreteTraceCRT
open ActualEisensteinCubic IdealMobiusDivisorSum CanonicalRowCompletion CanonicalCoefficientClass
local notation "O"=>HeckeFamily.O

private theorem admissible_one : Admissible (1:Ideal O) := by
  refine ⟨one_ne_zero,squarefree_one,?_⟩
  simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero,false_implies,forall_const]

def initialFunction (data:RowData)(W:ℝ→ℂ)(H b Btree cap D sigma freq:ℝ)(j:Ideal O):O→ℂ:=
  originalTotalPolynomial
    (InitialMeanSquare.outsideSquarefreeIdeals (excluded data) (completeCutoff H b Btree cap))
    1 (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1)
    (twistedProfile W sigma freq) H (Real.logb H (D/(j.absNorm:ℝ))) 0

theorem deleted_rows_le_initial
    (Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (data:RowData)(W:ℝ→ℂ)(H D c b Btree cap sigma freq:ℝ)
    (hH:1<H)(hD:1≤D)(hc:0<c)(hcapacity:D^(1+c)≤H)(hb:0≤b)
    (hW:∀x,W x≠0→x≤b)
    (j:Ideal O)(hj:j∈idealDivisors (∏P∈excluded data,P))
    (rows:Finset NonzeroElement)(hrows:∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤H):
    (∑u∈rows,‖polynomial ((data.character u).excludePrimes (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data))) true W (D/(j.absNorm:ℝ)) sigma freq‖^2)
      ≤smoothedEnergy Φ H (initialFunction data W H b Btree cap D sigma freq j) := by
  let F:=InitialMeanSquare.outsideSquarefreeIdeals (excluded data) (completeCutoff H b Btree cap)
  let f:=initialFunction data W H b Btree cap D sigma freq j
  have hFa:∀I∈F,Admissible I:=InitialMeanSquare.outsideSquarefree_admissible _ _
    (reflectionExcludedPrimes_bad (basePeriod data))
  have hs:Summable (fun u:O=>radialWeight Φ H u*‖f u‖^2):=
    (original_smoothed_overlap_triangle F admissible_one
      (fun I hI _=>admissible_supported (hFa I hI))
      (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1) (twistedProfile W sigma freq)
      (zero_lt_one.trans hH) (Real.logb H (D/(j.absNorm:ℝ))) 0 (fun _=>0)
      Φ (fun x _=>hΦ x) (zero_lt_one.trans hH)).1
  have he (u:NonzeroElement)(hu:u∈rows):
      ‖polynomial ((data.character u).excludePrimes (excluded data)
        (reflectionExcludedPrimes_prime (basePeriod data))) true W (D/(j.absNorm:ℝ)) sigma freq‖^2=
        radialWeight Φ H u.val*‖f u.val‖^2:=by
    have hn:‖eisEmbedding u.val‖^2/H∈Set.Icc (0:ℝ) 1:=by
      refine ⟨div_nonneg (sq_nonneg _) (zero_lt_one.trans hH).le,?_⟩
      apply (div_le_one (zero_lt_one.trans hH)).mpr
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact hrows u hu
    rw [(raw_complete_pool data H D c b Btree cap hH hD hc hcapacity hb W hW).2 j hj u sigma freq]
    change ‖f u.val‖^2=(Φ (‖eisEmbedding u.val‖^2/H)).re*‖f u.val‖^2
    rw [hone _ hn,Complex.one_re,one_mul]
  calc
    _=∑u∈rows,radialWeight Φ H u.val*‖f u.val‖^2:=Finset.sum_congr rfl he
    _=∑u∈rows.image Subtype.val,radialWeight Φ H u*‖f u‖^2:=by
      rw [Finset.sum_image (fun a _ b _ hab=>Subtype.val_injective hab)]
    _≤∑'u:O,radialWeight Φ H u*‖f u‖^2:=hs.sum_le_tsum _
      (fun u _=>mul_nonneg (hΦ _) (sq_nonneg _))
    _=_:=rfl

theorem raw_rows_le_initial
    (Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (data:RowData)(W:ℝ→ℂ)(H D c b Btree cap sigma freq:ℝ)
    (hH:1<H)(hD:1≤D)(hc:0<c)(hcapacity:D^(1+c)≤H)(hb:0≤b)
    (hW:∀x,W x≠0→x≤b)
    (rows:Finset NonzeroElement)(hrows:∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤H):
    (∑u∈rows,‖polynomial (data.character u) true W D sigma freq‖^2)≤
      ((idealDivisors (∏P∈excluded data,P)).card:ℝ)*
        ∑j∈idealDivisors (∏P∈excluded data,P),
          smoothedEnergy Φ H (initialFunction data W H b Btree cap D sigma freq j) := by
  have hd:=marked_family rows data.character (excluded data)
    (reflectionExcludedPrimes_prime (basePeriod data)) W D sigma freq b
    (zero_lt_one.trans_le hD) hW (fun _=>1) (fun _=>1) (by intros;norm_num)
  simp only [mul_one,one_mul] at hd
  apply hd.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro j hj
  exact deleted_rows_le_initial Φ hΦ hone data W H D c b Btree cap sigma freq
    hH hD hc hcapacity hb hW j hj rows hrows

end SevenEighths.DetectorDictionaryInverseRawInitialEnergy

end

end OAI
end OAIOriginalModule2511

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseRawInput
Source SHA256: 6414b80f468027bef17111ed8f6021dc15a3169b6504df0d203365a014f4359f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2512



namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseRawInput
open CompletedGauss
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open ConcreteTraceCRT FirstCauchyArithmetic SecondPassArithmetic IdealMobiusDivisorSum
open InverseInitialArithmetic InverseInitialRayAttachment InverseInitialConjugateEnergy
open InverseInitialPoissonBridge InverseInitialExcludedForcing InverseInitialExcludedPool
open UniqueFactorizationMonoid
local notation "O"=>HeckeFamily.O

private theorem admissible_one : Admissible (1:Ideal O):=by
  refine ⟨one_ne_zero,squarefree_one,?_⟩
  simp only [normalizedFactors_one,Multiset.notMem_zero,false_implies,forall_const]

theorem input_generator_one (F:Finset (Ideal O))(hF:∀I∈F,Admissible I)
    (η:O→*ℂ)(H:Finset (primePool F)→ℂ)(u:O):
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    inputConjugateRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ η
      (primaryGenerator (1:Ideal O)) 1 1 H u=
    inputConjugateRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ η 1 1 1 H u:=by
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF),
    initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  have he:(fun i:primePool F=>Ideal.span {poolPrimary F i})=(fun i=>i.val):=
    funext (poolPrimary_span F hF)
  have hm:rowCoprimeMask (fun i:primePool F=>Ideal.span {poolPrimary F i}) A
      (primaryGenerator (1:Ideal O))=1:=by
    rw [he]
    exact selected_mask F 1 admissible_one A isCoprime_one_right
  have ho:rowCoprimeMask (fun i:primePool F=>Ideal.span {poolPrimary F i}) A 1=1:=by
    simp [rowCoprimeMask,Ideal.IsPrime.one_notMem]
  simp only [hm,ho]

theorem complete_pool_selector (E:Finset (Ideal O))(hE:∀P∈E,Prime P)
    (Dpool:ℕ)(hbad:fixedBadPrimes⊆E)(W:ℝ→ℂ)(b Z r:ℝ)
    (hZ:0<Z)(hW:∀x,W x≠0→x≤b)(hbudget:b*Z^r≤(Dpool:ℝ)):
    let F:=InitialMeanSquare.outsideSquarefreeIdeals E Dpool;
    ∀A:Finset (primePool F),
      (if (∏i∈A,i.val)∈F then W (((∏i∈A,i.val).absNorm:ℝ)/Z^r) else 0)=
        W (((∏i∈A,i.val).absNorm:ℝ)/Z^r):=by
  intro F A
  by_cases hw:W (((∏i∈A,i.val).absNorm:ℝ)/Z^r)=0
  · simp only [hw,ite_self]
  have hF:=InitialMeanSquare.outsideSquarefree_admissible E Dpool hbad
  have hprod:=InitialMeanSquare.poolProduct_admissible F hF A
  have hout:outside E (∏i∈A,i.val):=
    pool_product_outside F E hE
      (fun I hI=>(mem_outsideIdealsUpTo.mp (Finset.mem_filter.mp hI).1).2.2) A
  have hN:((∏i∈A,i.val).absNorm:ℝ)≤(Dpool:ℝ):=
    ((div_le_iff₀ (Real.rpow_pos_of_pos hZ r)).mp (hW _ hw)).trans hbudget
  have hmem:(∏i∈A,i.val)∈F:=by
    apply Finset.mem_filter.mpr
    refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,?_,hout⟩,hprod.2.1⟩
    · exact Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hprod.1)
    · exact_mod_cast hN
  exact ite_eq_left hmem

theorem original_complete_star_input
    (E:Finset (Ideal O))(hE:∀P∈E,Prime P)(Dpool:ℕ)(hbad:fixedBadPrimes⊆E)
    (η:Ideal O→*ℂ)(W:ℝ→ℂ)(b Z r:ℝ)(hZ:0<Z)
    (hW:∀x,W x≠0→x≤b)(hbudget:b*Z^r≤(Dpool:ℝ))(u:O):
    let F:=InitialMeanSquare.outsideSquarefreeIdeals E Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible E Dpool hbad;
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    star (originalTotalPolynomial F 1 η (fun _=>1) W Z r 0 u)=
      ((Z^(-r/2):ℝ):ℂ)*inputConjugateRow (poolPrimary F) (poolPrimary_good F hF)
        Finset.univ (elementCharacter (conjugateIdealCharacter η)) 1 1 1
        (initialTest (poolPrimary F) (fun _=>1) (fun x=>star (W x)) Z r) u:=by
  intro F hF
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have he:=selected_conjugate_row F hF 1 admissible_one (fun _ _=>isCoprime_one_right)
    (conjugateIdealCharacter η) (fun I=>star (W ((I.absNorm:ℝ)/Z^r))) u
  dsimp only at he
  rw [input_generator_one F hF] at he
  have hselector:(fun A:Finset (primePool F)=>
      if (∏i∈A,i.val)∈F then star (W (((∏i∈A,i.val).absNorm:ℝ)/Z^r)) else 0)=
      initialTest (poolPrimary F) (fun _=>1) (fun x=>star (W x)) Z r:=by
    funext A
    rw [complete_pool_selector E hE Dpool hbad (fun x=>star (W x)) b Z r hZ
      (fun x hx=>hW x (by simpa only [star_ne_zero] using hx)) hbudget]
    simp only [initialTest,one_mul,InitialMeanSquare.poolPrimary_norm F hF]
    rfl
  rw [hselector] at he
  rw [←he]
  unfold originalTotalPolynomial
  have hscalar:star ((Z^(-r/2):ℝ):ℂ)=((Z^(-r/2):ℝ):ℂ):=by simp
  simp only [add_zero,map_one,mul_one,star_mul,star_sum,hscalar,
    conjugateIdealCharacter_apply,heckeIdealCharacter_apply]
  rw [mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  simp only [star_intCast]
  ring

theorem original_complete_child_norm
    (E:Finset (Ideal O))(hE:∀P∈E,Prime P)(Dpool:ℕ)(hbad:fixedBadPrimes⊆E)
    (η:Ideal O→*ℂ)(W:ℝ→ℂ)(b Z r t:ℝ)(hZ:0<Z)
    (hW:∀x,W x≠0→x≤b)(hbudget:b*Z^r≤(Dpool:ℝ))(u:O):
    let F:=InitialMeanSquare.outsideSquarefreeIdeals E Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible E Dpool hbad;
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    ‖originalTotalPolynomial F 1 η (fun _=>1) (InverseMoment.childLogTest W t) Z r 0 u‖^2=
      ‖((Z^(-r/2):ℝ):ℂ)*inputConjugateRow (poolPrimary F) (poolPrimary_good F hF)
        Finset.univ (elementCharacter (conjugateIdealCharacter η)) 1 1 1
        (initialTest (poolPrimary F) (fun _=>1)
          (InverseMoment.childLogTest (fun x=>star (W x)) (-t)) Z r) u‖^2:=by
  intro F hF
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have hw:∀x,InverseMoment.childLogTest W t x≠0→x≤b:=by
    intro x hx
    exact hW x ((mul_ne_zero_iff.mp hx).1)
  have he:=original_complete_star_input E hE Dpool hbad η
    (InverseMoment.childLogTest W t) b Z r hZ hw hbudget u
  dsimp only at he
  rw [DetectorDictionaryInverseRawConjugateGates.childLogTest_conjugate] at he
  have hn:=congrArg (fun z:ℂ=>‖z‖^2) he
  simpa only [norm_star] using hn

end SevenEighths.DetectorDictionaryInverseRawInput

end

end OAI
end OAIOriginalModule2512

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseRawRealRadial
Source SHA256: 7a9b421cd3d64466e9bf0676c0898d32e9856f9cd906aef21aa34bb866155b7f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2513


namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.DetectorDictionaryInverseRawRealRadial
open InverseInitialConjugateEnergy ConcreteTraceCRT
local notation "O"=>HeckeFamily.O

theorem exists_real_raw_radial_majorant:
    ∃Φ:𝓢(ℝ,ℂ),HasCompactSupport (Φ:ℝ→ℂ) ∧
      (∀x,0≤(Φ x).re) ∧ (∀x,(Φ x).im=0) ∧
      (∀x∈Set.Icc (0:ℝ) 1,Φ x=1):=by
  have hsub:Set.Icc (0:ℝ) 1⊆Set.Ioo (-1) 2:=by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  obtain ⟨f,hf,_,hs,hone⟩:=exists_contDiff_support_eq_eq_one_iff
    (n:=⊤) isOpen_Ioo isClosed_Icc hsub
  let v:ℝ→ℂ:=fun x=>((f x)^2:ℝ)
  have hv:ContDiff ℝ ∞ v:=Complex.ofRealCLM.contDiff.comp
    ((by simpa using hf:ContDiff ℝ ∞ f).pow 2)
  have hsupp:Function.support v⊆Set.Icc (-1) 2:=by
    intro x hx
    have hn:x∈Function.support f:=by
      intro hz
      exact hx (by simp [v,hz])
    rw [hs] at hn
    exact ⟨hn.1.le,hn.2.le⟩
  have hvc:=HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  refine ⟨hvc.toSchwartzMap hv,hvc,?_,?_,?_⟩
  · intro x
    change 0≤(f x)^2
    positivity
  · intro x
    exact Complex.ofReal_im _
  · intro x hx
    change (((f x)^2:ℝ):ℂ)=1
    rw [(hone x).mp hx]
    norm_num

theorem smoothedEnergy_eq_complex_norm (Φ:𝓢(ℝ,ℂ))
    (hΦ:∀x,0≤(Φ x).re)(hreal:∀x,(Φ x).im=0)
    (H:ℝ)(hH:0<H)(f:O→ℂ):
    smoothedEnergy Φ H f=
      ‖∑'u:O,Φ (‖eisEmbedding u‖^2/H)*(‖f u‖^2:ℝ)‖:=by
  rw [real_smoothed_sum_eq Φ (fun x _=>hreal x) hH,
    Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (smoothedEnergy_nonneg Φ (fun x _=>hΦ x) hH f)]

end SevenEighths.DetectorDictionaryInverseRawRealRadial

end

end OAI
end OAIOriginalModule2513

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseRawReference
Source SHA256: 72ba8916857bb07d0420518975cc1393facbd958b36932a13a0ef0e3ef28d0d1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2514






namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap Topology
open Filter
namespace SevenEighths.DetectorDictionaryInverseRawReference
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalRowCompletion CanonicalCoefficientClass CanonicalQuadraticSieve
open InverseInitialRawDictionary InverseInitialConjugateEnergy InverseInitialExcludedPeriod
open InverseInitialRayAttachment InverseInitialProfileBounds
open DetectorDictionaryInverseRawInitialGates DetectorDictionaryInverseRawInitialEnergy
open DetectorDictionaryInverseRawInput DetectorDictionaryInverseRawInputBound
open DetectorDictionaryInverseRawConjugateGates DetectorDictionaryInverseRawRealRadial
open DetectorDictionaryInverseRawGeometry IdealMobiusDivisorSum
local notation "O"=>HeckeFamily.O

theorem raw_reference_large (W:𝓢(ℝ,ℂ))(a b c κ:ℝ)(ha:0<a)(hb:0<b)
    (hs:Function.support W⊆Set.Icc a b)(hc:0<c)(hκ:0<κ):
    ∃J:ℕ,∀data:RowData,∃C H₀:ℝ,0<C ∧ 1<H₀ ∧
      ∀(t H D:ℝ),H₀≤H→1≤D→D^(1+c)≤H→∀rows:Finset NonzeroElement,
      (∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤H)→
      (∑u∈rows,‖polynomial (data.character u) true (childLogTest W t) D 0 0‖^2)≤
        (C*(1+‖t‖)^(2*J))*H*(H*max 1 D)^κ := by
  obtain ⟨Φ,hΦcompact,hΦ,hreal,hone⟩:=exists_real_raw_radial_majorant
  obtain ⟨η,τ,π,eps,hη,hτ,hπ,heps,hηone,hηgap,hτgap,hcost⟩:=
    raw_fixed_reserves c (κ/2) hc (by positivity)
  let gap:=capacityGap c/4
  have hgap:0<gap:=by dsimp [gap];exact div_pos (capacityGap_pos c hc) (by norm_num)
  have hηsmall:η≤gap/50:=by dsimp [gap];nlinarith
  have hτsmall:τ≤gap/50:=by dsimp [gap];nlinarith
  let Wbar:=SecondPassIntegration.conjugateProfile W
  have hsbar:Function.support Wbar⊆Set.Icc a b:=by
    intro x hx
    exact hs (by simpa only [Wbar,Function.mem_support,SecondPassIntegration.conjugateProfile_apply,star_ne_zero] using hx)
  obtain ⟨J,Btree,hBtree,hinput⟩:=raw_input_bound Wbar a b ha hsbar Φ
    gap eps π η τ (κ/4) hgap heps hπ hη hηone hηsmall hτ hτsmall (by positivity)
  refine ⟨J,?_⟩
  intro data
  obtain ⟨hq,hqset,hn,hperiod⟩:=raw_conjugate_base_gates data
  obtain ⟨C,Hq,hC,hHq,hinput⟩:=hinput (deletedPeriod (basePeriod data)) hq
  obtain ⟨Hg,hg⟩:=eventually_atTop.mp (shifted_raw_geometry_eventually data c η hc hη)
  let T:=idealDivisors (∏P∈excluded data,P)
  let Ctotal:=((T.card:ℝ)+1)^2*C
  refine ⟨Ctotal,max Hq Hg,by dsimp [Ctotal];positivity,lt_max_of_lt_left hHq,?_⟩
  intro t H D hH hD hcapacity rows hrows
  have hHq':Hq≤H:=(le_max_left _ _).trans hH
  obtain ⟨hHp,hgeom⟩:=hg H ((le_max_right _ _).trans hH)
  have hHpos:0<H:=zero_lt_one.trans hHp
  have hWt:∀x,childLogTest W t x≠0→x≤b:=by
    intro x hx
    exact (hs ((mul_ne_zero_iff.mp hx).1)).2
  have hraw:=raw_rows_le_initial Φ hΦ hone data (childLogTest W t) H D c b Btree 2 0 0
    hHp hD hc hcapacity hb.le hWt rows hrows
  have hterm (j:Ideal O)(hj:j∈T):
      smoothedEnergy Φ H (initialFunction data (childLogTest W t) H b Btree 2 D 0 0 j)≤
        C*H^(1+15*η+π+eps+κ/4)*(1+‖t‖)^(2*J):=by
    obtain ⟨hrlo,hr₁,hr₂,hex,hrcap,hDH⟩:=hgeom D hD hcapacity j hj
    let r:=Real.logb H (D/(j.absNorm:ℝ))
    let Dpool:=completeCutoff H b Btree 2
    have hpool:Btree*H^3≤(Dpool:ℝ):=by
      convert completeCutoff_tree H b Btree 2 using 1 ; norm_num
    have hbcover:b*H^r≤(Dpool:ℝ):=by
      rw [hex]
      exact completeCutoff_columns H b Btree 2 D _ hb.le (zero_lt_one.trans_le hD).le hDH
        (excluded_divisor_norm data j hj).1
    have hbound:=hinput H hHq' Dpool hpool
      (elementCharacter (conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom))
      hn hperiod r (-t) (by dsimp [r];linarith)
      (by dsimp [gap] at *;linarith [(capacityGap_pos c hc).le])
      (by dsimp [gap] at *;linarith [(capacityGap_pos c hc).le])
      (by have hh:=capacityGap_lt_one c hc;linarith)
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes (deletedPeriod (basePeriod data))) Dpool
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes (deletedPeriod (basePeriod data))) Dpool
      (reflectionExcludedPrimes_bad (deletedPeriod (basePeriod data)))
    let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by
      rw [poolPrimary_span F hF i];infer_instance
    have hf:initialFunction data (childLogTest W t) H b Btree 2 D 0 0 j=
        originalTotalPolynomial F 1 (idealCoeff (deletedBase data)).toMonoidHom
          (fun _=>1) (childLogTest W t) H r 0:=by
      unfold initialFunction
      dsimp only [F]
      rw [hqset]
      congr 1
      funext x
      simp [twistedProfile,HeckeDyadic.shift]
    rw [hf,smoothedEnergy_eq_complex_norm Φ hΦ hreal H hHpos]
    have he: (∑'u:O,Φ (‖eisEmbedding u‖^2/H)*
        (‖originalTotalPolynomial F 1 (idealCoeff (deletedBase data)).toMonoidHom
          (fun _=>1) (childLogTest W t) H r 0 u‖^2:ℝ))=
        (∑'u:O,Φ (‖eisEmbedding u‖^2/H)*
        (‖((H^(-r/2):ℝ):ℂ)*SecondPassArithmetic.inputConjugateRow
          (poolPrimary F) (poolPrimary_good F (InitialMeanSquare.outsideSquarefree_admissible
            (reflectionExcludedPrimes (deletedPeriod (basePeriod data))) Dpool
            (reflectionExcludedPrimes_bad (deletedPeriod (basePeriod data)))))
          Finset.univ (elementCharacter (conjugateIdealCharacter
            (idealCoeff (deletedBase data)).toMonoidHom)) 1 1 1
          (initialTest (poolPrimary F) (fun _=>1) (childLogTest Wbar (-t)) H r) u‖^2:ℝ)):=by
      apply tsum_congr
      intro u
      congr 2
      exact original_complete_child_norm (reflectionExcludedPrimes (deletedPeriod (basePeriod data)))
        (reflectionExcludedPrimes_prime (deletedPeriod (basePeriod data))) Dpool
        (reflectionExcludedPrimes_bad (deletedPeriod (basePeriod data))) _ W b H r t hHpos
        (fun x hx=>(hs hx).2) hbcover u
    rw [he]
    simpa only [norm_neg] using hbound
  apply hraw.trans
  calc
    _≤(T.card:ℝ)*∑j∈T,C*H^(1+15*η+π+eps+κ/4)*(1+‖t‖)^(2*J):=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (Nat.cast_nonneg _)
    _=(T.card:ℝ)^2*C*H^(1+15*η+π+eps+κ/4)*(1+‖t‖)^(2*J):=by
      simp only [Finset.sum_const,nsmul_eq_mul];ring
    _≤Ctotal*H^(1+15*η+π+eps+κ/4)*(1+‖t‖)^(2*J):=by
      dsimp [Ctotal]
      gcongr
      nlinarith [Nat.cast_nonneg (α:=ℝ) T.card]
    _≤(Ctotal*(1+‖t‖)^(2*J))*H*(H*max 1 D)^κ:=by
      have he:15*η+π+eps+κ/4≤κ:=by linarith
      have hh:=raw_output_budget H D κ (15*η+π+eps+κ/4) hHp.le hκ.le he
      rw [show (1+15*η+π+eps+κ/4:ℝ)=1+(15*η+π+eps+κ/4) by ring]
      nlinarith [mul_le_mul_of_nonneg_left hh
        (show 0≤Ctotal*(1+‖t‖)^(2*J) by dsimp [Ctotal];positivity)]

theorem raw_reference_moment (W:𝓢(ℝ,ℂ))(a b c κ:ℝ)(ha:0<a)(hb:0<b)
    (hs:Function.support W⊆Set.Icc a b)(hc:0<c)(hκ:0<κ):
    ∃J:ℕ,∀data:RowData,∃C:ℝ,0<C ∧ ∀t:ℝ,
      RawMoment data (childLogTest W t) c κ (C*(1+‖t‖)^(2*J)) := by
  obtain ⟨J,hlarge⟩:=raw_reference_large W a b c κ ha hb hs hc hκ
  refine ⟨J,?_⟩
  intro data
  obtain ⟨C,H₀,hC,hH₀,hlarge⟩:=hlarge data
  obtain ⟨C₀,hC₀,hcomplete⟩:=DetectorDictionaryInverseRawCompact.rawMoment_of_large_rows_ge_one
    W a b ha hs H₀ hH₀.le
  refine ⟨C+C₀,add_pos hC hC₀,?_⟩
  exact hcomplete data c κ C J hc.le hκ.le hC.le hlarge

end SevenEighths.DetectorDictionaryInverseRawReference

end

end OAI
end OAIOriginalModule2514

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseRawUniform
Source SHA256: db7fb9409d151965f45d81b2c45fc781d8a11bebee66442187df483fbc4cb1a4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2515



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory
namespace SevenEighths.DetectorDictionaryInverseRawUniform
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open DetectorDictionaryInverseUniform DetectorDictionaryInverseClippedUniform
open DetectorDictionaryInverseRawFourier

private theorem rawMoment_mono (data : RowData) (W : ℝ→ℂ) (c κ A B : ℝ)
    (hAB : A≤B) (h : RawMoment data W c κ A) : RawMoment data W c κ B := by
  intro H D hH hD hHD rows hrows
  apply (h H D hH hD hHD rows hrows).trans
  gcongr

theorem raw_family_uniform (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0<C ∧ ∀(data : RowData)(c κ A : ℝ),0≤A →
      (∀s,RawMoment data (childLogTest referenceWindow s) c κ (A*(1+‖s‖)^(2*J))) →
      ∀scaled reverse : Bool,∀n : ℕ,n≤2 → ∀U : ℝ,0<U →
      ∀tstar r : ℝ,∀σ∈Set.Icc (0:ℝ) 1,∀t : ℝ,
      RawMoment data (inverseSourceSchwartz scaled reverse n U tstar r σ t)
        c κ (A*C*(1+‖t‖)^K) := by
  obtain ⟨K,B,hB,hmass⟩:=familyDensity_moment J
  refine ⟨2*K,B^2,sq_pos_of_pos hB,?_⟩
  intro data c κ A hA href scaled reverse n hn U hU tstar r σ hσ t
  let W:=inverseSourceSchwartz scaled reverse n U tstar r σ t
  let hs:=source_support scaled reverse n U tstar r σ t
  let g:=CubicReflectionKernel.logSchwartz W (1/4) (9/4) (by norm_num) hs (W.smooth ⊤)
  have hw : ∀x,referenceWindow x≠0 → x≤(13/4:ℝ) := by
    intro x hx
    exact (referenceWindow_support (subset_tsupport _ hx)).2
  have hagree : ∀y,0<y → referenceWindow y*W y=W y := by
    intro y hy
    simpa only [one_mul,W] using referenceWindow_agrees scaled reverse n U tstar r σ t 1 y
      (by norm_num) (by norm_num) hy
  have hh:=rawMoment_reference data W (1/4) (9/4) (by norm_num) hs (W.smooth ⊤)
    referenceWindow (13/4) c κ A J hA hw hagree href
  have hm : (∫v:ℝ,(1+‖v‖)^J*‖(𝓕 g) v‖)≤B*(1+‖t‖)^K := by
    have hb:=hmass scaled reverse n hn U hU tstar r σ hσ t 1
    simpa only [familyDensity_norm,logSource_eq_logSchwartz,g,W,hs] using hb
  apply rawMoment_mono data W c κ _ _ _ hh
  change A*(∫v:ℝ,(1+‖v‖)^J*‖(𝓕 g) v‖)^2≤_
  calc
    _≤A*(B*(1+‖t‖)^K)^2:=mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (integral_nonneg (fun _=>by positivity)) hm 2) hA
    _= _:=by simp only [mul_pow,←pow_mul,Nat.mul_comm];ring

theorem raw_pair_uniform (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0<C ∧ ∀(data : RowData)(c κ A : ℝ),0≤A →
      (∀s,RawMoment data (childLogTest referenceWindow s) c κ (A*(1+‖s‖)^(2*J))) →
      ∀reverse : Bool,∀n : ℕ,n≤2 → ∀U : ℝ,0<U →
      ∀tstar r : ℝ,∀σ∈Set.Icc (0:ℝ) 1,∀t : ℝ,
      let W:=twistProfile
        (logTest (HeckeDetectorCoefficientTransfer.orientedProfile reverse
          (HeckeDetectorInverseFiberCount.inverseTest U tstar r)) n) σ t
      RawMoment data W c κ (A*C*(1+‖t‖)^K) ∧
      RawMoment data (scaleProfile W) c κ (A*C*(1+‖t‖)^K) := by
  obtain ⟨K,C,hC,hb⟩:=raw_family_uniform J
  refine ⟨K,C,hC,?_⟩
  intro data c κ A hA href reverse n hn U hU tstar r σ hσ t
  dsimp only
  have hefalse : (inverseSourceSchwartz false reverse n U tstar r σ t:ℝ→ℂ)=
      twistProfile (logTest (HeckeDetectorCoefficientTransfer.orientedProfile reverse
        (HeckeDetectorInverseFiberCount.inverseTest U tstar r)) n) σ t := by
    funext x
    simpa only [Bool.false_eq_true,ite_false] using inverseSourceSchwartz_apply false reverse n U tstar r σ t x
  have hetrue : (inverseSourceSchwartz true reverse n U tstar r σ t:ℝ→ℂ)=
      scaleProfile (twistProfile (logTest (HeckeDetectorCoefficientTransfer.orientedProfile reverse
        (HeckeDetectorInverseFiberCount.inverseTest U tstar r)) n) σ t) := by
    funext x
    simpa only [Bool.true_eq,ite_true] using inverseSourceSchwartz_apply true reverse n U tstar r σ t x
  exact ⟨hefalse ▸ hb data c κ A hA href false reverse n hn U hU tstar r σ hσ t,
    hetrue ▸ hb data c κ A hA href true reverse n hn U hU tstar r σ hσ t⟩

theorem raw_pair_height_uniform (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0<C ∧ ∀(data : RowData)(c κ A : ℝ),0≤A →
      (∀s,RawMoment data (childLogTest referenceWindow s) c κ (A*(1+‖s‖)^(2*J))) →
      ∀reverse : Bool,∀n : ℕ,n≤2 → ∀U : ℝ,0<U →
      ∀tstar r : ℝ,∀σ∈Set.Icc (0:ℝ) 1,∀height t : ℝ,0≤height →
      t∈Set.Icc (-height) height →
      let W:=twistProfile
        (logTest (HeckeDetectorCoefficientTransfer.orientedProfile reverse
          (HeckeDetectorInverseFiberCount.inverseTest U tstar r)) n) σ t
      RawMoment data W c κ (A*C*(1+height)^K) ∧
      RawMoment data (scaleProfile W) c κ (A*C*(1+height)^K) := by
  obtain ⟨K,C,hC,hb⟩:=raw_pair_uniform J
  refine ⟨K,C,hC,?_⟩
  intro data c κ A hA href reverse n hn U hU tstar r σ hσ height t hheight ht
  have hh:=hb data c κ A hA href reverse n hn U hU tstar r σ hσ t
  have hnorm : ‖t‖≤height := by simpa only [Real.norm_eq_abs,abs_le,Set.mem_Icc] using ht
  have hbound : A*C*(1+‖t‖)^K≤A*C*(1+height)^K := by gcongr
  exact ⟨rawMoment_mono data _ c κ _ _ hbound hh.1,
    rawMoment_mono data _ c κ _ _ hbound hh.2⟩

end SevenEighths.DetectorDictionaryInverseRawUniform

end

end OAI
end OAIOriginalModule2515

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialMarkedDictionary
Source SHA256: 76188e2eb11965ea223eb444d2f9264f058626ac05bbee1bac6c4d9900022cc8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2516


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialMarkedDictionary
open HeckeFamily HeckeDyadic InverseInitialRawDictionary InverseInitialConjugateEnergy
open InverseInitialPoissonBridge UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

theorem indexed_mark_initial {ι : Type*} (T : Finset ι) (P : ι→Ideal O) (A : ι→ℂ)
    (η : Ideal O →* ℂ) (χ : Character) (u : O)
    (hrow : ∀I,idealCoeff χ I=η I*CanonicalRowCompletion.idealRowHom u I)
    (W : ℝ→ℂ) (Z r z σ freq : ℝ) (hZ : 0<Z) (S : Finset (Ideal O))
    (hc : ∀I:Ideal O,I≠0 → W ((I.absNorm:ℝ)/Z^r)≠0 → I∈S) :
    polynomial χ true W (Z^r) σ freq*(Z^(-z/2):ℝ)*
      (∑i∈T,A i*idealCoeff χ (P i))=
      ∑i∈T,A i*originalTotalPolynomial S (P i) η (fun _=>1)
        (twistedProfile W σ freq) Z r z u := by
  rw [inverse_eq_initial_source η χ u hrow W Z r σ freq hZ S hc]
  have hn : ((Z^(-r/2):ℝ):ℂ)*((Z^(-z/2):ℝ):ℂ)=((Z^(-(r+z)/2):ℝ):ℂ) := by
    rw [←Complex.ofReal_mul,←Real.rpow_add hZ]
    congr 2
    ring
  unfold originalTotalPolynomial
  simp only [add_zero,map_one,mul_one,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro I hI
  rw [hrow]
  simp only [heckeIdealCharacter_apply]
  calc
    _ = (((Z^(-r/2):ℝ):ℂ)*((Z^(-z/2):ℝ):ℂ))*
      (A i*((moebius I:ℂ)*(η I*CanonicalRowCompletion.idealRowHom u I)*
      (η (P i)*CanonicalRowCompletion.idealRowHom u (P i))*
      twistedProfile W σ freq ((I.absNorm:ℝ)/Z^r))) := by ring
    _ = _ := by rw [hn];ring

theorem indexed_conjugate_mark_norm {ι : Type*} (T : Finset ι) (P : ι→Ideal O) (A : ι→ℂ)
    (η : Ideal O →* ℂ) (χ : Character) (u : O)
    (hrow : ∀I,idealCoeff χ I=η I*CanonicalRowCompletion.idealRowHom u I)
    (W : ℝ→ℂ) (Z r z σ freq : ℝ) (hZ : 0<Z) (S : Finset (Ideal O))
    (hc : ∀I:Ideal O,I≠0 → W ((I.absNorm:ℝ)/Z^r)≠0 → I∈S)
    (hη : ∀i∈T,A i≠0 → η (P i)≠0) :
    ‖polynomial χ true W (Z^r) σ freq*(Z^(-z/2):ℝ)*
      (∑i∈T,A i*star (CanonicalRowCompletion.idealRowHom u (P i)))‖=
      ‖∑i∈T,(star (A i)/η (P i))*originalTotalPolynomial S (P i) η (fun _=>1)
        (twistedProfile W σ freq) Z r z u‖ := by
  have hm : (∑i∈T,(star (A i)/η (P i))*idealCoeff χ (P i))=
      star (∑i∈T,A i*star (CanonicalRowCompletion.idealRowHom u (P i))) := by
    simp only [star_sum,star_mul,star_star]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases ha : A i=0
    · simp [ha]
    · rw [hrow]
      field_simp [hη i hi ha]
  rw [←indexed_mark_initial T P (fun i=>star (A i)/η (P i)) η χ u hrow W Z r z σ freq hZ S hc,hm]
  simp only [norm_mul,norm_star]

theorem conjugate_mark_product {ι : Type*} [Fintype ι]
    (T : ι→Finset (Ideal O)) (A : ι→Ideal O→ℂ) (u : O) :
    (∏i,∑P∈T i,A i P*star (CanonicalRowCompletion.idealRowHom u P))=
      ∑p∈Fintype.piFinset T,(∏i,A i (p i))*
        star (CanonicalRowCompletion.idealRowHom u (∏i,p i)) := by
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.prod_mul_distrib,map_prod,star_prod]

end SevenEighths.InverseInitialMarkedDictionary

end

end OAI
end OAIOriginalModule2516

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialPhysicalSlots
Source SHA256: 8649cca47ab87613b3251c38f8bbc141cd2caa121bce68ed8d88f7136edb4e49
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2517


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialPhysicalSlots
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open InverseInitialRawDictionary InverseInitialDetectorSource InverseInitialMarkedDictionary
open InverseInitialConjugateEnergy
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)

def livePrimes (V : ℝ→ℂ) (b D : ℝ) : Finset (Ideal O) :=
  ((HeckePrimeAnnular.annulusSet b D).filter
    (fun P=>Prime P ∧ P∈RayQuotient.identityClass M H)).filter
      (fun P=>V ((P.absNorm:ℝ)/D)≠0)

omit [NeZero M] in
theorem livePrime_data (V : ℝ→ℂ) (a b D : ℝ) (hD : 0<D)
    (hV : ∀x,V x≠0 → x∈Set.Icc a b) (P : Ideal O) (hp : P∈livePrimes M H V b D) :
    Prime P ∧ P∈RayQuotient.identityClass M H ∧ a*D≤(P.absNorm:ℝ) ∧ (P.absNorm:ℝ)≤b*D := by
  obtain ⟨hp,hv⟩ := Finset.mem_filter.mp hp
  obtain ⟨_,hp,hr⟩ := Finset.mem_filter.mp hp
  exact ⟨hp,hr,(le_div_iff₀ hD).mp (hV _ hv).1,(div_le_iff₀ hD).mp (hV _ hv).2⟩

omit [NeZero M] in
theorem amplitude_eq_live (u : O) (V : ℝ→ℂ) (b Z ell : ℝ) (ζ : ℂ) (hZ : 0<Z) :
    HeckePrimeRow.canonicalPrimeAmplitude M H u V b (Z^ell) ζ=
      ((Z^(-ell/2):ℝ):ℂ)*∑P∈livePrimes M H V b (Z^ell),
        primeProfile V (Z^ell) ζ P*star (CanonicalRowCompletion.idealRowHom u P) := by
  unfold HeckePrimeRow.canonicalPrimeAmplitude
  rw [normalization_eq Z ell hZ]
  congr 1
  rw [livePrimes]
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro P hP
  split_ifs with hv
  · change star (CanonicalRowCompletion.idealRowHom u P)*V _*_ =
      (V _*_)*star (CanonicalRowCompletion.idealRowHom u P)
    ring
  · simp only [not_not] at hv
    simp [hv]

theorem slot_normalization {ι : Type*} [Fintype ι] (Z : ℝ) (hZ : 0<Z) (ell : ι→ℝ) :
    (∏i,((Z^(-ell i/2):ℝ):ℂ))=((Z^(-(∑i,ell i)/2):ℝ):ℂ) := by
  rw [←Complex.ofReal_prod,←Real.rpow_sum_of_pos hZ]
  congr 2
  simp only [neg_div,Finset.sum_div,Finset.sum_neg_distrib]

omit [NeZero M] in
theorem amplitude_product_eq_tuples {ι : Type*} [Fintype ι] (u : O)
    (V : ι→ℝ→ℂ) (b ell : ι→ℝ) (ζ : ι→ℂ) (Z : ℝ) (hZ : 0<Z) :
    (∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u (V i) (b i) (Z^(ell i)) (ζ i))=
      ((Z^(-(∑i,ell i)/2):ℝ):ℂ)*
        ∑p∈Fintype.piFinset (fun i=>livePrimes M H (V i) (b i) (Z^(ell i))),
        (∏i,primeProfile (V i) (Z^(ell i)) (ζ i) (p i))*
          star (CanonicalRowCompletion.idealRowHom u (∏i,p i)) := by
  simp_rw [amplitude_eq_live M H _ _ _ _ _ _ hZ]
  rw [Finset.prod_mul_distrib,slot_normalization Z hZ,conjugate_mark_product]

omit [NeZero M] in
theorem physical_slots_norm_initial {ι : Type*} [Fintype ι]
    (data : RowData) (u : NonzeroElement) (W : ℝ→ℂ) (V : ι→ℝ→ℂ)
    (Z r σ freq bW : ℝ) (a b ell : ι→ℝ) (ζ : ι→ℂ) (hZ : 0<Z)
    (hW : ∀x,W x≠0 → x≤bW) (hV : ∀i x,V i x≠0 → x∈Set.Icc (a i) (b i))
    (hlarge : ∀i,((baseCharacter data).modulus.absNorm:ℝ)<a i*Z^(ell i)) :
    ‖polynomial (data.character u) true W (Z^r) σ freq*
      (∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u.val (V i) (b i) (Z^(ell i)) (ζ i))‖=
    ‖∑p∈Fintype.piFinset (fun i=>livePrimes M H (V i) (b i) (Z^(ell i))),
      (star (∏i,primeProfile (V i) (Z^(ell i)) (ζ i) (p i))/
        fixedBase data.η data.m data.f (∏i,p i))*
      originalTotalPolynomial
        ((ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
        (∏i,p i) (fixedBase data.η data.m data.f) (fun _=>1)
        (twistedProfile W σ freq) Z r (∑i,ell i) u.val‖ := by
  let T := fun i=>livePrimes M H (V i) (b i) (Z^(ell i))
  let A := fun p:ι→Ideal O=>∏i,primeProfile (V i) (Z^(ell i)) (ζ i) (p i)
  have hn (p : ι→Ideal O) (hp : p∈Fintype.piFinset T) (_ha : A p≠0) :
      fixedBase data.η data.m data.f (∏i,p i)≠0 := by
    rw [map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hpi := Fintype.mem_piFinset.mp hp i
    have hd := livePrime_data M H (V i) (a i) (b i) (Z^(ell i))
      (Real.rpow_pos_of_pos hZ _) (hV i) (p i) hpi
    exact base_nonzero_prime data (p i) hd.1 ((hlarge i).trans_le hd.2.2.1)
  have he := indexed_conjugate_mark_norm (Fintype.piFinset T) (fun p=>∏i,p i) A
    (fixedBase data.η data.m data.f) (data.character u) u.val
    (fixedBase_row data.η (data.character u) data.m data.f u.val (data.character_spec u))
    W Z r (∑i,ell i) σ freq hZ (ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*bW⌉₊)
    (finite_source_cover W (Z^r) bW (Real.rpow_pos_of_pos hZ _) hW) hn
  rw [amplitude_product_eq_tuples M H _ _ _ _ _ _ hZ,←mul_assoc]
  change ‖polynomial (data.character u) true W (Z^r) σ freq*↑(Z^(-(∑i,ell i)/2))*
    (∑p∈Fintype.piFinset T,A p*star (CanonicalRowCompletion.idealRowHom u (∏i,p i)))‖=_
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [originalTotal_supported_source _ _ _
    (fixedBase_zero_unsupported data.η data.m data.f data.lambda_dvd data.two_dvd)]

omit [NeZero M] in
theorem live_tuple_injective {ι : Type*} [Fintype ι]
    (V : ι→ℝ→ℂ) (a b ell : ι→ℝ) (Z : ℝ) (hZ : 0<Z)
    (hV : ∀i x,V i x≠0 → x∈Set.Icc (a i) (b i))
    (hsep : ∀i j,i≠j → b i*Z^(ell i)<a j*Z^(ell j) ∨
      b j*Z^(ell j)<a i*Z^(ell i))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset
      (fun i=>livePrimes M H (V i) (b i) (Z^(ell i)))) : Function.Injective p := by
  intro i j he
  by_contra hij
  have hi := livePrime_data M H (V i) (a i) (b i) (Z^(ell i))
    (Real.rpow_pos_of_pos hZ _) (hV i) (p i) (Fintype.mem_piFinset.mp hp i)
  have hj := livePrime_data M H (V j) (a j) (b j) (Z^(ell j))
    (Real.rpow_pos_of_pos hZ _) (hV j) (p j) (Fintype.mem_piFinset.mp hp j)
  rw [he] at hi
  rcases hsep i j hij with h|h <;> linarith [hi.2.2.1,hi.2.2.2,hj.2.2.1,hj.2.2.2]

omit [NeZero M] in
theorem live_tuple_admissible {ι : Type*} [Fintype ι]
    (data : RowData) (V : ι→ℝ→ℂ) (a b ell : ι→ℝ) (Z : ℝ) (hZ : 0<Z)
    (hV : ∀i x,V i x≠0 → x∈Set.Icc (a i) (b i))
    (hlarge : ∀i,((baseCharacter data).modulus.absNorm:ℝ)<a i*Z^(ell i))
    (hsep : ∀i j,i≠j → b i*Z^(ell i)<a j*Z^(ell j) ∨
      b j*Z^(ell j)<a i*Z^(ell i))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset
      (fun i=>livePrimes M H (V i) (b i) (Z^(ell i)))) :
    CanonicalQuadraticSieve.Admissible (∏i,p i) := by
  have hd i := livePrime_data M H (V i) (a i) (b i) (Z^(ell i))
    (Real.rpow_pos_of_pos hZ _) (hV i) (p i) (Fintype.mem_piFinset.mp hp i)
  have hs (i : ι) : CanonicalQuadraticSieve.Supported (p i) := by
    by_contra hn
    exact base_nonzero_prime data (p i) (hd i).1 ((hlarge i).trans_le (hd i).2.2.1)
      (fixedBase_zero_unsupported data.η data.m data.f data.lambda_dvd data.two_dvd (p i) hn)
  have hi := live_tuple_injective M H V a b ell Z hZ hV hsep p hp
  have hsprod : CanonicalQuadraticSieve.Supported (∏i,p i) := by
    have hh (S : Finset ι) : CanonicalQuadraticSieve.Supported (∏i∈S,p i) := by
      induction S using Finset.induction_on with
      | empty =>
        simp only [Finset.prod_empty]
        exact ⟨one_ne_zero,by intro P hP;simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero] at hP⟩
      | @insert i S hi ih =>
        rw [Finset.prod_insert hi]
        exact (CanonicalQuadraticSieve.supported_mul_iff _ _).mpr ⟨hs i,ih⟩
    exact hh Finset.univ
  refine ⟨hsprod.1,?_,?_⟩
  · apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i _ j _ hij
      let : (p i).IsMaximal := (Ideal.isPrime_of_prime (hd i).1).isMaximal (hd i).1.ne_zero
      let : (p j).IsMaximal := (Ideal.isPrime_of_prime (hd j).1).isMaximal (hd j).1.ne_zero
      exact (Ideal.isCoprime_of_isMaximal (hi.ne hij)).isRelPrime
    · intro i _
      exact (hd i).1.squarefree
  · intro P hP
    exact hsprod.2 P hP

end SevenEighths.InverseInitialPhysicalSlots

end

end OAI
end OAIOriginalModule2517

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseRawFiberSource
Source SHA256: ad5c8655f2aba6e08e20b002f3faf002d3c87de4d4b4765ec42d4d8d676467b7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2518



namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.DetectorDictionaryInverseRawFiberSource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer InverseInitialPhysicalSlots
open InverseInitialDetectorSource InverseInitialRawDictionary InverseInitialConjugateEnergy
open HeckeDetectorPhysicalSelection
local notation "O"=>HeckeFamily.O

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

theorem fiber_physical_norm_initial
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW : ℝ) (lower : Slot→ℝ)
    (hU : 0<U) (hW : ∀x,W x≠0 → x≤bW)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s))
    (u : FreeRow) (hu : u∈F.rows) :
    ‖polynomial (F.family u F.label) true W (U^F.r) σ t*F.physicalProduct selected u‖=
      ‖∑p∈Fintype.piFinset (fun s:selected=>
          livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))),
        (star (∏s:selected,primeProfile (F.profile s) (U^(F.widths s)) (F.external s) (p s))/
          fixedBase F.rowData.η F.rowData.m F.rowData.f (∏s:selected,p s))*
        originalTotalPolynomial
          ((ConcretePrimeRowBridge.idealsUpTo ⌈U^F.r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
          (∏s:selected,p s) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
          (twistedProfile (orientedProfile F.reverse W) σ (orientedFrequency F.reverse t))
          U F.r (∑s:selected,F.widths s) u.val‖ := by
  have hn:=norm_of_oriented_coefficients (F.family u F.label)
    (F.rowData.character ⟨u.val,u.property.1⟩) F.reverse (F.row_coeff u hu)
    true W (U^F.r) σ t (Real.rpow_pos_of_pos hU _)
  have hp : F.physicalProduct selected u=
      ∏s:selected,HeckePrimeRow.canonicalPrimeAmplitude M H u.val
        (F.profile s) (F.upper s) (U^(F.widths s)) (F.external s) := by
    simp only [Fiber.physicalProduct,physical]
    exact (Finset.prod_coe_sort selected _).symm
  rw [norm_mul,hn,←norm_mul,hp]
  have hh:=physical_slots_norm_initial M H F.rowData ⟨u.val,u.property.1⟩
    (orientedProfile F.reverse W) (fun s:selected=>F.profile s)
    U F.r σ (orientedFrequency F.reverse t) bW
    (fun s:selected=>lower s) (fun s:selected=>F.upper s) (fun s:selected=>F.widths s)
    (fun s:selected=>F.external s) hU
    (by intro x hx;apply hW x;intro hz;exact hx (by cases F.reverse <;> simp [orientedProfile,hz]))
    (fun s=>hV s s.property) (fun s=>hlarge s s.property)
  convert hh using 1 ; congr 2
  ext p
  simp only [Fintype.mem_piFinset]

theorem fiber_physical_energy_initial
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW : ℝ) (lower : Slot→ℝ)
    (hU : 0<U) (hW : ∀x,W x≠0 → x≤bW)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s)) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) true W (U^F.r) σ t*F.physicalProduct selected u‖^2)=
      ∑u∈F.rows,‖∑p∈Fintype.piFinset (fun s:selected=>
          livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))),
        (star (∏s:selected,primeProfile (F.profile s) (U^(F.widths s)) (F.external s) (p s))/
          fixedBase F.rowData.η F.rowData.m F.rowData.f (∏s:selected,p s))*
        originalTotalPolynomial
          ((ConcretePrimeRowBridge.idealsUpTo ⌈U^F.r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
          (∏s:selected,p s) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
          (twistedProfile (orientedProfile F.reverse W) σ (orientedFrequency F.reverse t))
          U F.r (∑s:selected,F.widths s) u.val‖^2 := by
  apply Finset.sum_congr rfl
  intro u hu
  rw [fiber_physical_norm_initial F selected W σ t bW lower hU hW hV hlarge u hu]

theorem fiber_inverse_log_upper
    (F : Fiber M H Label Slot U a ε tstar T allowance i) (n : ℕ) :
    ∀x,((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile) x≠0 → x≤9/4 := by
  induction n with
  | zero =>
    intro x hx
    have hv : HeckeDetectorDyadicProfiles.positiveAnnular x≠0 := by
      intro hz
      exact hx (by simp [Fiber.inverseProfile,HeckeDetectorInverseFiberCount.inverseTest,
        HeckeDetectorDyadicBridge.inverseProfile,hz])
    exact (HeckeDetectorDyadicProfiles.positiveAnnular_support hv).2
  | succ n ih =>
    intro x hx
    rw [Function.iterate_succ_apply'] at hx
    exact ih x (HeckeDetectorRowwisePolynomial.logProfile_support _ hx)

theorem fiber_inverse_energy_initial
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (n : ℕ) (σ t : ℝ) (lower : Slot→ℝ)
    (hU : 0<U)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s)) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) true ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile) (U^F.r) σ t*F.physicalProduct selected u‖^2)=
      ∑u∈F.rows,‖∑p∈Fintype.piFinset (fun s:selected=>
          livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))),
        (star (∏s:selected,primeProfile (F.profile s) (U^(F.widths s)) (F.external s) (p s))/
          fixedBase F.rowData.η F.rowData.m F.rowData.f (∏s:selected,p s))*
        originalTotalPolynomial
          ((ConcretePrimeRowBridge.idealsUpTo ⌈U^F.r*(9/4)⌉₊).filter CanonicalQuadraticSieve.Supported)
          (∏s:selected,p s) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
          (twistedProfile (orientedProfile F.reverse ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)) σ (orientedFrequency F.reverse t))
          U F.r (∑s:selected,F.widths s) u.val‖^2 := by
  exact fiber_physical_energy_initial F selected
    ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile) σ t (9/4) lower
    hU (fiber_inverse_log_upper F n) hV hlarge

end SevenEighths.DetectorDictionaryInverseRawFiberSource

end

end OAI
end OAIOriginalModule2518

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedPadding
Source SHA256: 263e66031cf16795aa88727b83bd550b41421a0f70109d75b317896b8c604cba
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2519




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.DetectorDictionaryInverseMarkedPadding
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer InverseInitialPhysicalSlots
open InverseInitialDetectorSource InverseInitialRawDictionary InverseInitialConjugateEnergy
open HeckeDetectorPhysicalSelection ConcreteTraceCRT CanonicalQuadraticSieve ActualEisensteinCubic
local notation "O" => HeckeFamily.O

def radialMajorant : 𝓢(ℝ,ℂ) :=
  Classical.choose DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant

theorem radialMajorant_compact : HasCompactSupport (radialMajorant : ℝ→ℂ) :=
  (Classical.choose_spec DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant).1

theorem radialMajorant_nonneg (x : ℝ) : 0≤(radialMajorant x).re :=
  (Classical.choose_spec DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant).2.1 x

theorem radialMajorant_one (x : ℝ) (hx : x∈Set.Icc (0:ℝ) 1) : radialMajorant x=1 :=
  (Classical.choose_spec DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant).2.2 x hx

theorem compact_radial_summable (Φ : 𝓢(ℝ,ℂ))
    (hΦ : HasCompactSupport (Φ : ℝ→ℂ)) (Y : ℝ) (hY : 0<Y) (f : O→ℂ) :
    Summable (fun u : O=>radialWeight Φ Y u*‖f u‖^2) := by
  obtain ⟨B,hB⟩ := hΦ.isBounded.exists_norm_le
  let R := ShortDraftLatticeCount.rowNormBall ⌈B*Y⌉₊
  apply (hasSum_sum_of_ne_finset_zero (s:=R) ?_).summable
  intro u hu
  have hz : Φ (‖eisEmbedding u‖^2/Y)=0 := by
    by_contra hn
    have hb := hB _ (subset_tsupport Φ hn)
    have hnB : (Ideal.absNorm (Ideal.span {u}):ℝ)≤B*Y := by
      rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) hY.le)] at hb
      rw [eisEmbedding_norm_sq_eq_absNorm_span] at hb
      exact (div_le_iff₀ hY).mp hb
    apply hu
    apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
    exact_mod_cast hnB.trans (Nat.le_ceil (B*Y))
  simp [radialWeight,hz]

theorem radialMajorant_summable (Y : ℝ) (hY : 0<Y) (f : O→ℂ) :
    Summable (fun u : O=>radialWeight radialMajorant Y u*‖f u‖^2) :=
  compact_radial_summable radialMajorant radialMajorant_compact Y hY f

theorem finite_source_le_smoothed {Row : Type*} (rows : Finset Row)
    (row : Row→O) (hinj : Function.Injective row) (f : O→ℂ)
    (Y : ℝ) (hY : 0<Y)
    (hrows : ∀u∈rows,((Ideal.span {row u}).absNorm:ℝ)≤Y) :
    (∑u∈rows,‖f (row u)‖^2)≤smoothedEnergy radialMajorant Y f := by
  have he (u : Row) (hu : u∈rows) :
      ‖f (row u)‖^2=radialWeight radialMajorant Y (row u)*‖f (row u)‖^2 := by
    have hn : ‖eisEmbedding (row u)‖^2/Y∈Set.Icc (0:ℝ) 1 := by
      refine ⟨div_nonneg (sq_nonneg _) hY.le,?_⟩
      apply (div_le_one hY).mpr
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact hrows u hu
    simp [radialWeight,radialMajorant_one _ hn]
  calc
    _=∑u∈rows,radialWeight radialMajorant Y (row u)*‖f (row u)‖^2 :=
      Finset.sum_congr rfl he
    _=∑u∈rows.image row,radialWeight radialMajorant Y u*‖f u‖^2 := by
      rw [Finset.sum_image (fun a _ b _ hab=>hinj hab)]
    _≤∑'u : O,radialWeight radialMajorant Y u*‖f u‖^2 :=
      (radialMajorant_summable Y hY f).sum_le_tsum _
        (fun u _=>mul_nonneg (radialMajorant_nonneg _) (sq_nonneg _))
    _=smoothedEnergy radialMajorant Y f := rfl

variable {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

def selectedSource (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW : ℝ) (u : O) : ℂ :=
  ∑p∈Fintype.piFinset (fun s:selected=>
      livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))),
    (star (∏s:selected,primeProfile (F.profile s) (U^(F.widths s)) (F.external s) (p s))/
      fixedBase F.rowData.η F.rowData.m F.rowData.f (∏s:selected,p s))*
    originalTotalPolynomial
      ((ConcretePrimeRowBridge.idealsUpTo ⌈U^F.r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
      (∏s:selected,p s) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
      (twistedProfile (orientedProfile F.reverse W) σ (orientedFrequency F.reverse t))
      U F.r (∑s:selected,F.widths s) u

omit [NeZero M] in
theorem selectedSource_norm (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW : ℝ) (lower : Slot→ℝ)
    (hU : 0<U) (hW : ∀x,W x≠0 → x≤bW)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s))
    (u : FreeRow) (hu : u∈F.rows) :
    ‖polynomial (F.family u F.label) true W (U^F.r) σ t*F.physicalProduct selected u‖=
      ‖selectedSource F selected W σ t bW u.val‖ :=
  DetectorDictionaryInverseRawFiberSource.fiber_physical_norm_initial
    F selected W σ t bW lower hU hW hV hlarge u hu

omit [NeZero M] in
theorem selectedSource_summable
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW Y : ℝ) (hY : 0<Y) :
    Summable (fun u : O=>radialWeight radialMajorant Y u*
      ‖selectedSource F selected W σ t bW u‖^2) :=
  radialMajorant_summable Y hY _

omit [NeZero M] in
theorem selectedSource_energy
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW : ℝ) (lower : Slot→ℝ)
    (hU : 0<U) (hW : ∀x,W x≠0 → x≤bW)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s)) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) true W (U^F.r) σ t*
      F.physicalProduct selected u‖^2)=
      ∑u∈F.rows,‖selectedSource F selected W σ t bW u.val‖^2 :=
  DetectorDictionaryInverseRawFiberSource.fiber_physical_energy_initial
    F selected W σ t bW lower hU hW hV hlarge

omit [NeZero M] in
theorem fiber_physical_le_padded_smoothed
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW ρ : ℝ) (lower : Slot→ℝ)
    (hU : 1≤U) (hρ : 0≤ρ) (hW : ∀x,W x≠0 → x≤bW)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s)) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) true W (U^F.r) σ t*
      F.physicalProduct selected u‖^2)≤
      smoothedEnergy radialMajorant (U^(1+ρ)) (selectedSource F selected W σ t bW) := by
  have hU0 : 0<U := zero_lt_one.trans_le hU
  have hpad : U≤U^(1+ρ) := by
    calc
      U=U^(1:ℝ) := (Real.rpow_one U).symm
      _≤U^(1+ρ) := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  calc
    _=∑u∈F.rows,‖selectedSource F selected W σ t bW u.val‖^2 := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [selectedSource_norm F selected W σ t bW lower hU0 hW hV hlarge u hu]
    _≤_ := finite_source_le_smoothed F.rows (fun u : FreeRow=>u.val)
      Subtype.val_injective _ _ (Real.rpow_pos_of_pos hU0 _)
      (fun u hu=>(F.row_norm u hu).trans hpad)

omit [NeZero M] in
theorem fiber_inverse_le_padded_smoothed
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (n : ℕ) (σ t ρ : ℝ) (lower : Slot→ℝ)
    (hU : 1≤U) (hρ : 0≤ρ)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s)) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) true
      ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile) (U^F.r) σ t*
      F.physicalProduct selected u‖^2)≤
      smoothedEnergy radialMajorant (U^(1+ρ))
        (selectedSource F selected ((HeckeDetectorRowwisePolynomial.logProfile^[n])
          F.inverseProfile) σ t (9/4)) :=
  fiber_physical_le_padded_smoothed F selected _ σ t (9/4) ρ lower hU hρ
    (DetectorDictionaryInverseRawFiberSource.fiber_inverse_log_upper F n) hV hlarge

theorem fixed_padding_margins (r z ρ : ℝ) (hρ : 0≤ρ)
    (hfirst : r+2*z<1) (hsecond : 2*r+8*z<3) :
    r+2*z≤(1+ρ)-ρ ∧ 2*r+8*z≤3*(1+ρ)-3*ρ ∧
      InverseMoment.MarkedMargins (1+ρ) r z ρ := by
  unfold InverseMoment.MarkedMargins
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

omit [NeZero M] in
theorem fiber_padding_margins
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (ρ : ℝ) (hρ : 0≤ρ)
    (hfirst : F.r+2*(∑s∈selected,F.widths s)<1)
    (hsecond : 2*F.r+8*(∑s∈selected,F.widths s)<3) :
    F.r+2*(∑s∈selected,F.widths s)≤(1+ρ)-ρ ∧
      2*F.r+8*(∑s∈selected,F.widths s)≤3*(1+ρ)-3*ρ ∧
      InverseMoment.MarkedMargins (1+ρ) F.r (∑s∈selected,F.widths s) ρ :=
  fixed_padding_margins _ _ ρ hρ hfirst hsecond

theorem padded_output_budget (U C ρ loss εm : ℝ) (hU : 1≤U) (hC : 0≤C)
    (hbudget : ρ+loss≤εm) : C*U^(1+ρ+loss)≤C*U^(1+εm) := by
  apply mul_le_mul_of_nonneg_left _ hC
  exact Real.rpow_le_rpow_of_exponent_le hU (by linarith)

end SevenEighths.DetectorDictionaryInverseMarkedPadding

end

end OAI
end OAIOriginalModule2519

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceCoefficients
Source SHA256: 2a925836c10d1f75e3061f586e03487fec3a56d2b3671ed6b906736075060a50
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2520


namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open InverseInitialRawDictionary InverseInitialDetectorSource InverseInitialPhysicalSlots
open DetectorDictionaryInverseMarkedPadding
local notation "O"=>HeckeFamily.O

def slotCoefficient (data:RowData)(V:ℝ→ℂ)(Y:ℝ)(ζ:ℂ)(P:Ideal O) : ℂ :=
  star (primeProfile V Y ζ P)/fixedBase data.η data.m data.f P

theorem slotCoefficient_character (data:RowData)(V:ℝ→ℂ)(Y:ℝ)(ζ:ℂ)(P:Ideal O) :
    slotCoefficient data V Y ζ P=
      idealCoeff (baseCharacter data).inverse P*star (primeProfile V Y ζ P) := by
  rw [slotCoefficient,HeckeDetectorRelativePrime.idealCoeff_inverse,baseCharacter_coeff,
    div_eq_mul_inv,mul_comm]

theorem tuple_coefficient {ι:Type*}[Fintype ι](data:RowData)
    (V:ι→ℝ→ℂ)(Y:ι→ℝ)(ζ:ι→ℂ)(P:ι→Ideal O) :
    star (∏i,primeProfile (V i) (Y i) (ζ i) (P i))/
      fixedBase data.η data.m data.f (∏i,P i)=
      ∏i,slotCoefficient data (V i) (Y i) (ζ i) (P i) := by
  simp only [slotCoefficient,star_prod,map_prod,Finset.prod_div_distrib]

def normalizedSlotCoefficient (data:RowData)(V:ℝ→ℂ)(Y:ℝ)(ζ:ℂ)(C:ℝ)(P:Ideal O) : ℂ :=
  slotCoefficient data V Y ζ P/(C:ℂ)

theorem tuple_coefficient_normalized {ι:Type*}[Fintype ι](data:RowData)
    (V:ι→ℝ→ℂ)(Y:ι→ℝ)(ζ:ι→ℂ)(C:ι→ℝ)(hC:∀i,C i≠0)(P:ι→Ideal O) :
    star (∏i,primeProfile (V i) (Y i) (ζ i) (P i))/
      fixedBase data.η data.m data.f (∏i,P i)=
      (∏i,(C i:ℂ))*∏i,normalizedSlotCoefficient data (V i) (Y i) (ζ i) (C i) (P i) := by
  rw [tuple_coefficient,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [normalizedSlotCoefficient]
  field_simp [hC i]

variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
  {U a ε tstar T allowance:ℝ}{i:ℕ}

omit [NeZero M] in
theorem selectedSource_normalized (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(W:ℝ→ℂ)(σ t bW:ℝ)(C:Slot→ℝ)(hC:∀s∈selected,C s≠0)(u:O) :
    selectedSource F selected W σ t bW u=
      (∏s∈selected,(C s:ℂ))*
      ∑p∈Fintype.piFinset (fun s:selected=>livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))),
        (∏s:selected,normalizedSlotCoefficient F.rowData (F.profile s) (U^(F.widths s))
          (F.external s) (C s) (p s))*
        InverseInitialConjugateEnergy.originalTotalPolynomial
          ((ConcretePrimeRowBridge.idealsUpTo ⌈U^F.r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
          (∏s:selected,p s) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
          (twistedProfile (HeckeDetectorCoefficientTransfer.orientedProfile F.reverse W) σ
            (HeckeDetectorCoefficientTransfer.orientedFrequency F.reverse t))
          U F.r (∑s:selected,F.widths s) u := by
  unfold selectedSource
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [tuple_coefficient_normalized F.rowData (fun s:selected=>F.profile s)
    (fun s:selected=>U^(F.widths s)) (fun s:selected=>F.external s)
    (fun s:selected=>C s) (fun s=>hC s s.property) p]
  rw [Finset.prod_coe_sort selected (fun s=>(C s:ℂ))]
  ring

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end OAIOriginalModule2520

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceDivisors
Source SHA256: 68f5bfbeafb5e46f58d50a239e983b3808cf71b780917eac0e2047ad97e8bda4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2521



namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily IdealMobiusDivisorSum UniqueFactorizationMonoid
open InverseInitialConjugateEnergy InverseInitialPoissonBridge
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [DecidableEq ι] in
theorem tuple_product_squarefree (P:ι→Ideal O)(hP:∀i,Prime (P i))
    (hinj:Function.Injective P) : Squarefree (∏i,P i) := by
  have hs:∀Q∈Finset.univ.image P,Prime Q := by
    intro Q hQ
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hQ
    exact hP i
  have he:(∏Q∈Finset.univ.image P,Q)=∏i,P i :=
    Finset.prod_image (fun i hi j hj h=>hinj h)
  rw [←he]
  exact InverseInitialExcludedPolynomial.prime_product_squarefree _ hs

omit [DecidableEq ι] in
theorem tuple_product_support (P:ι→Ideal O)(hP:∀i,Prime (P i))
    (_hinj:Function.Injective P) : primeSupport (∏i,P i)=Finset.univ.image P := by
  have hn:(∏i,P i)≠0:=Finset.prod_ne_zero_iff.mpr (fun i hi=>(hP i).ne_zero)
  ext Q
  rw [primeSupport,Multiset.mem_toFinset,mem_normalizedFactors_iff hn,Finset.mem_image]
  constructor
  · rintro ⟨hQ,hd⟩
    obtain ⟨i,hi,hd⟩:=(hQ.dvd_finsetProd_iff P).mp hd
    have he:Q=P i:=associated_iff_eq.mp (hQ.associated_of_dvd (hP i) hd)
    exact ⟨i,hi,he.symm⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨hP i,Finset.dvd_prod_of_mem P hi⟩

omit [DecidableEq ι] in
theorem tuple_divisors_eq_subsets (P:ι→Ideal O)(hP:∀i,Prime (P i))
    (hinj:Function.Injective P) :
    idealDivisors (∏i,P i)=Finset.univ.powerset.image (fun J:Finset ι=>∏i∈J,P i) := by
  have hs:=tuple_product_squarefree P hP hinj
  have hf:(idealDivisors (∏i,P i)).filter Squarefree=idealDivisors (∏i,P i) := by
    apply Finset.filter_eq_self.mpr
    intro J hJ
    exact hs.squarefree_of_dvd ((mem_idealDivisors hs.ne_zero).mp hJ)
  rw [←hf,squarefree_divisors_eq_image _ hs.ne_zero,tuple_product_support P hP hinj,
    Finset.powerset_image,Finset.image_image]
  congr 1
  funext J
  exact Finset.prod_image (fun i hi j hj h=>hinj h)

omit [Fintype ι] in
theorem tuple_subset_product_injective (P:ι→Ideal O)(hP:∀i,Prime (P i))
    (hinj:Function.Injective P) : Function.Injective (fun J:Finset ι=>∏i∈J,P i) := by
  let:∀i,(P i).IsMaximal:=fun i=>(Ideal.isPrime_of_prime (hP i)).isMaximal (hP i).ne_zero
  exact FirstCauchyArithmetic.family_product_injective P hinj

theorem sum_tuple_divisors (P:ι→Ideal O)(hP:∀i,Prime (P i))
    (hinj:Function.Injective P)(f:Ideal O→ℂ) :
    (∑j∈idealDivisors (∏i,P i),f j)=∑J∈Finset.univ.powerset,f (∏i∈J,P i) := by
  rw [tuple_divisors_eq_subsets P hP hinj,Finset.sum_image
    (fun J hJ K hK he=>tuple_subset_product_injective P hP hinj he)]

theorem originalTotal_slot_subsets (S:Finset (Ideal O))
    (P:ι→Ideal O)(hP:∀i,Prime (P i))(hinj:Function.Injective P)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(hZ:0<Z)(u:O) :
    originalTotalPolynomial S (∏i,P i) η a W Z r z u=
      ∑J∈Finset.univ.powerset,
        originalFixedPolynomial S (∏i,P i) (∏i∈J,P i) η a W Z r z u := by
  rw [originalTotalPolynomial_eq_sectors S (tuple_product_squarefree P hP hinj)
    η a W hZ r z (fun _=>0),sum_tuple_divisors P hP hinj]

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end OAIOriginalModule2521

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceShift
Source SHA256: 5d9a952130fa1a9fc44adcf3f01363d910a93bdb48c27102e9e22ab45b33d091
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2522



namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeInverseAmplification Filter IdealMobiusDivisorSum
open DetectorDictionaryInverseRawInitialGates
local notation "O"=>HeckeFamily.O

def shiftedExponent (_data:RowData)(U r:ℝ)(j:Ideal O) : ℝ :=
  r-Real.logb U (j.absNorm:ℝ)

theorem marked_shift_eventually (data:RowData)(eta:ℝ)(heta:0<eta) :
    ∀ᶠU:ℝ in atTop,1<U ∧
      ∀j∈idealDivisors (∏P∈excluded data,P),∀r:ℝ,
        r-eta≤shiftedExponent data U r j ∧ shiftedExponent data U r j≤r ∧
        U^(shiftedExponent data U r j)=U^r/(j.absNorm:ℝ) := by
  have ht:∀ᶠU:ℝ in atTop,((∏P∈excluded data,P).absNorm:ℝ)≤U^eta :=
    (tendsto_rpow_atTop heta).eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1:ℝ),ht] with U hU ht
  refine ⟨hU,?_⟩
  intro j hj r
  obtain ⟨hn,hnB⟩:=excluded_divisor_norm data j hj
  have hU0:0<U:=zero_lt_one.trans hU
  have hn0:0<(j.absNorm:ℝ):=zero_lt_one.trans_le hn
  have hl0:0≤Real.logb U (j.absNorm:ℝ):=
    div_nonneg (Real.log_nonneg hn) (Real.log_pos hU).le
  have hl:Real.logb U (j.absNorm:ℝ)≤eta:=
    (Real.logb_le_iff_le_rpow hU hn0).mpr (hnB.trans ht)
  refine ⟨by dsimp [shiftedExponent];linarith,by dsimp [shiftedExponent];linarith,?_⟩
  rw [shiftedExponent,Real.rpow_sub hU0,Real.rpow_logb hU0 hU.ne' hn0]

theorem shifted_padding_capacities (r r' ell ρ gap eta:ℝ)
    (hr:0≤r)(hell:0≤ell)(hshift:r-eta≤r')(hshiftup:r'≤r)
    (hfirst:r+2*ell<1)(hsecond:2*r+8*ell<3)
    (hgap:2*gap≤ρ)(hgap₃:2*gap≤3*ρ) :
    -eta≤r' ∧ r'+2*ell≤(1+ρ)-2*gap ∧
      2*r'+8*ell≤3*(1+ρ)-2*gap ∧ r'+ell<1 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem shifted_source_box (r r' ell G eta:ℝ)(hr:0≤r)(hell:0≤ell)
    (_hG:0≤G)(hGell:G≤ell)(hshift:r-eta≤r')(hshiftup:r'≤r)
    (hfirst:r+2*ell<1)(_heta:0≤eta)(hetaSmall:eta≤1/7) :
    -2≤r'+ell-2*G ∧ r'+ell+7*eta≤2 := by
  constructor <;> linarith

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end OAIOriginalModule2522

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceTuples
Source SHA256: e6d953d30f31423f02a84c99092d4a527f2c5d59c3f5969c23df03df6659f02f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2523


namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

abbrev Tuple (L:ι→Finset (Ideal O)) := ∀i,↥(L i)
abbrev Assigned (L:ι→Finset (Ideal O))(J:Finset ι) := ∀i:↥J,↥(L i.val)
abbrev Remaining (L:ι→Finset (Ideal O))(J:Finset ι) := ∀i:{i:ι // i∉J},↥(L i.val)

def joinTuple (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)(y:Remaining L J) : Tuple L :=
  (Equiv.piEquivPiSubtypeProd (fun i=>i∈J) (fun i=>↥(L i))).symm (x,y)

theorem sum_tuple_split (L:ι→Finset (Ideal O))(J:Finset ι)(f:Tuple L→ℂ) :
    (∑q:Tuple L,f q)=∑x:Assigned L J,∑y:Remaining L J,f (joinTuple L J x y) := by
  rw [←(Equiv.piEquivPiSubtypeProd (fun i=>i∈J) (fun i=>↥(L i))).symm.sum_comp]
  exact Fintype.sum_prod_type _

theorem sum_tuple_original (L:ι→Finset (Ideal O))(f:(ι→Ideal O)→ℂ) :
    (∑q:Tuple L,f (fun i=>(q i).val))=∑q∈Fintype.piFinset L,f q := by
  symm
  apply Finset.sum_bij (fun q hq i=>⟨q i,Fintype.mem_piFinset.mp hq i⟩)
  · intro q hq
    exact Finset.mem_univ _
  · intro q hq r hr he
    funext i
    exact congrArg Subtype.val (congrFun he i)
  · intro q hq
    refine ⟨fun i=>(q i).val,Fintype.mem_piFinset.mpr (fun i=>(q i).property),?_⟩
    funext i
    rfl
  · intro q hq
    rfl

theorem tuple_injective (L:ι→Finset (Ideal O))
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(q:Tuple L) :
    Function.Injective (fun i=>(q i).val) := by
  intro i j he
  by_contra hij
  exact Finset.disjoint_left.mp (hdis (Finset.mem_univ i) (Finset.mem_univ j) hij)
    (q i).property (by simpa only [he] using (q j).property)

theorem original_selected_subset_sum (S:Finset (Ideal O))
    (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(coeff:ι→Ideal O→ℂ)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(hZ:0<Z)(u:O) :
    (∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η a W Z r z u)=
    ∑J∈Finset.univ.powerset,∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalFixedPolynomial S (∏i,(q i).val) (∏i∈J,(q i).val) η a W Z r z u := by
  calc
    _ = ∑q:Tuple L,∑J∈Finset.univ.powerset,(∏i,coeff i (q i).val)*
        originalFixedPolynomial S (∏i,(q i).val) (∏i∈J,(q i).val) η a W Z r z u := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [originalTotal_slot_subsets S _ (fun i=>hprime i _ (q i).property)
        (tuple_injective L hdis q) η a W Z r z hZ u,Finset.mul_sum]
    _ = _ := Finset.sum_comm

theorem original_selected_grouped (S:Finset (Ideal O))
    (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(coeff:ι→Ideal O→ℂ)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(hZ:0<Z)(u:O) :
    (∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η a W Z r z u)=
    ∑J∈Finset.univ.powerset,∑x:Assigned L J,∑y:Remaining L J,
      (∏i,coeff i (joinTuple L J x y i).val)*
        originalFixedPolynomial S (∏i,(joinTuple L J x y i).val)
          (∏i∈J,(joinTuple L J x y i).val) η a W Z r z u := by
  rw [original_selected_subset_sum S L hprime hdis coeff η a W Z r z hZ u]
  apply Finset.sum_congr rfl
  intro J hJ
  exact sum_tuple_split L J _

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end OAIOriginalModule2523

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceProducts
Source SHA256: 6c055681b8f5a0e7d1f0a98a8c487c98473e20537cbc93c13da82d76fbe5b8a2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2524


namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge InverseInitialOverlap
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def assignedIdeal (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J) : Ideal O :=
  ∏i:↥J,(x i).val

def remainingIdeal (L:ι→Finset (Ideal O))(J:Finset ι)(y:Remaining L J) : Ideal O :=
  ∏i:{i:ι // i∉J},(y i).val

omit [Fintype ι] in
@[simp] theorem joinTuple_assigned (L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J)(i:↥J) : joinTuple L J x y i.val=x i := by
  simp [joinTuple,Equiv.piEquivPiSubtypeProd_symm_apply,i.property]

omit [Fintype ι] in
@[simp] theorem joinTuple_remaining (L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J)(i:{i:ι // i∉J}) : joinTuple L J x y i.val=y i := by
  simp [joinTuple,Equiv.piEquivPiSubtypeProd_symm_apply,i.property]

omit [Fintype ι] in
theorem joinTuple_assigned_product (L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J) :
    (∏i∈J,(joinTuple L J x y i).val)=assignedIdeal L J x := by
  rw [←Finset.prod_coe_sort J (fun i=>(joinTuple L J x y i).val)]
  simp only [joinTuple_assigned,assignedIdeal]

theorem joinTuple_product (L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J) :
    (∏i,(joinTuple L J x y i).val)=assignedIdeal L J x*remainingIdeal L J y := by
  have he := (Fintype.prod_subtype_mul_prod_subtype (fun i=>i∈J)
      (fun i=>(joinTuple L J x y i).val)).symm
  simp only [joinTuple_assigned,joinTuple_remaining] at he
  convert he using 1
  try simp only [assignedIdeal,remainingIdeal]
  congr 2
  ext i
  simp

theorem joinTuple_coefficient_product (L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J)(coeff:ι→Ideal O→ℂ) :
    (∏i,coeff i (joinTuple L J x y i).val)=
      (∏i:↥J,coeff i.val (x i).val)*(∏i:{i:ι // i∉J},coeff i.val (y i).val) := by
  have he := (Fintype.prod_subtype_mul_prod_subtype (fun i=>i∈J)
      (fun i=>coeff i (joinTuple L J x y i).val)).symm
  simp only [joinTuple_assigned,joinTuple_remaining] at he
  convert he using 1
  try simp only [assignedIdeal,remainingIdeal]
  congr 2
  ext i
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem assignedIdeal_ne_zero (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (J:Finset ι)(x:Assigned L J) : assignedIdeal L J x≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _hi=>(hprime i.val _ (x i).property).ne_zero)

theorem residual_join (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (J:Finset ι)(x:Assigned L J)(y:Remaining L J) :
    residual (∏i,(joinTuple L J x y i).val) (assignedIdeal L J x)=remainingIdeal L J y := by
  rw [joinTuple_product,InverseInitialOverlap.residual,quotient_mul_cancel (assignedIdeal_ne_zero L hprime J x)]

theorem original_selected_grouped_products (S:Finset (Ideal O))
    (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(coeff:ι→Ideal O→ℂ)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(hZ:0<Z)(u:O) :
    (∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η a W Z r z u)=
    ∑J∈Finset.univ.powerset,∑x:Assigned L J,
      (∏i:↥J,coeff i.val (x i).val)*
      ∑y:Remaining L J,(∏i:{i:ι // i∉J},coeff i.val (y i).val)*
        originalFixedPolynomial S (assignedIdeal L J x*remainingIdeal L J y)
          (assignedIdeal L J x) η a W Z r z u := by
  rw [original_selected_grouped S L hprime hdis coeff η a W Z r z hZ u]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [joinTuple_coefficient_product,joinTuple_product,joinTuple_assigned_product]
  ring

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end OAIOriginalModule2524

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceOverlap
Source SHA256: 034fef443692274439aa3697ca5dc608d6c469de82a887e590f6bf895d29f54c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2525


namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge
open InverseInitialOverlap UniqueFactorizationMonoid ActualEisensteinCubic CanonicalRowCompletion
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def remainingResidual (S:Finset (Ideal O))(L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)(a:Ideal O→ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) : ℂ :=
  ∑y:Remaining L J,star ((∏i:{i:ι // i∉J},coeff i.val (y i).val)*
    (moebius (remainingIdeal L J y):ℂ))*
    conjugatedResidual S (assignedIdeal L J x*remainingIdeal L J y)
      (assignedIdeal L J x) η a W Z r z G u

theorem assigned_remaining_squarefree (L:ι→Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(y:Remaining L J) :
    Squarefree (assignedIdeal L J x*remainingIdeal L J y) := by
  rw [←joinTuple_product]
  exact tuple_product_squarefree _ (fun i=>hprime i _ (joinTuple L J x y i).property)
    (tuple_injective L hdis _)

theorem assigned_source_eq_remainingResidual (S:Finset (Ideal O))
    (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(coeff:ι→Ideal O→ℂ)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0<Z)(u:O) :
    (∑y:Remaining L J,(∏i:{i:ι // i∉J},coeff i.val (y i).val)*
      originalFixedPolynomial S (assignedIdeal L J x*remainingIdeal L J y)
        (assignedIdeal L J x) η a W Z r z u)=
    (moebius (assignedIdeal L J x):ℂ)*(Z^(-G):ℝ)*η (assignedIdeal L J x)^2*
      (idealRowHom u (assignedIdeal L J x))^2*
      star (remainingResidual S L J x coeff η a W Z r z G u) := by
  unfold remainingResidual
  simp only [star_sum,star_mul,star_star,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [originalFixedPolynomial_eq_conjugatedResidual S
    (assigned_remaining_squarefree L hprime hdis J x y) (dvd_mul_right _ _) η a W hZ r z G,
    InverseInitialOverlap.residual,quotient_mul_cancel (assignedIdeal_ne_zero L hprime J x)]
  ring

theorem original_selected_overlap (S:Finset (Ideal O))
    (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(coeff:ι→Ideal O→ℂ)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(G:Finset ι→ℝ)
    (hZ:0<Z)(u:O) :
    (∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η a W Z r z u)=
    ∑J∈Finset.univ.powerset,∑x:Assigned L J,
      (∏i:↥J,coeff i.val (x i).val)*(moebius (assignedIdeal L J x):ℂ)*
      (Z^(-G J):ℝ)*η (assignedIdeal L J x)^2*(idealRowHom u (assignedIdeal L J x))^2*
      star (remainingResidual S L J x coeff η a W Z r z (G J) u) := by
  rw [original_selected_grouped_products S L hprime hdis coeff η a W Z r z hZ u]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro x hx
  rw [assigned_source_eq_remainingResidual S L hprime hdis J x coeff η a W Z r z (G J) hZ u]
  ring

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end OAIOriginalModule2525

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceRemaining
Source SHA256: c92017f2ec708cc2ffad6850290abf8861f0fef1823988ac12a3e2e40b49fc00
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2526



namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge
open InverseInitialOverlap UniqueFactorizationMonoid ActualEisensteinCubic
open InverseInitialCommonRatios
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

theorem remaining_injective (L:ι→Finset (Ideal O))
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(y:Remaining L J) : Function.Injective (fun i=>(y i).val) := by
  intro i j he
  apply Subtype.ext
  by_contra hij
  exact Finset.disjoint_left.mp (hdis (Finset.mem_univ i.val) (Finset.mem_univ j.val) hij)
    (y i).property (by simpa only [he] using (y j).property)

theorem remaining_moebius (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(y:Remaining L J) :
    (moebius (remainingIdeal L J y):ℂ)=(-1:ℂ)^Fintype.card {i:ι // i∉J} := by
  let:∀i:{i:ι // i∉J},((y i).val).IsMaximal:=fun i=>
    (Ideal.isPrime_of_prime (hprime i.val _ (y i).property)).isMaximal
      (hprime i.val _ (y i).property).ne_zero
  simpa only [remainingIdeal,Finset.card_univ] using prime_product_moebius
    (fun i=>(y i).val) (fun i=>hprime i.val _ (y i).property)
    (remaining_injective L hdis J y) Finset.univ

def remainingPolynomial (S:Finset (Ideal O))(L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) : ℂ :=
  ∑y:Remaining L J,(∏i:{i:ι // i∉J},star (coeff i.val (y i).val))*
    residualNormalizedPolynomial S (assignedIdeal L J x*remainingIdeal L J y)
      (assignedIdeal L J x) (conjugateIdealCharacter η) (fun _=>1)
      (fun v=>star (W v)) Z r z G u

theorem remainingResidual_eq_polynomial (S:Finset (Ideal O))
    (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) :
    remainingResidual S L J x coeff η (fun _=>1) W Z r z G u=
      (-1:ℂ)^Fintype.card {i:ι // i∉J}*
      remainingPolynomial S L J x coeff η W Z r z G u := by
  unfold remainingResidual remainingPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [remaining_moebius L hprime hdis]
  simp only [star_mul,star_prod,star_pow,star_neg,star_one,conjugatedResidual]
  ring

theorem sum_tuple_pi (L:ι→Finset (Ideal O))
    (f:(∀i∈(Finset.univ:Finset ι),Ideal O)→ℂ) :
    (∑q:Tuple L,f (fun i _=>(q i).val))=
      ∑q∈(Finset.univ:Finset ι).pi L,f q := by
