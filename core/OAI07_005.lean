  have hlog := HeckePrimeScale.log_scale_eventually dmin rmin
    (2*(|Real.log A|+|Real.log B|)+1) hdmin hrmin
  filter_upwards [hbins,hlog,eventually_ge_atTop (1 : ℝ)] with Z hb hl hZ
  intro d hd hd' hU hT χ hχ a i ha ha' hmax r σ freq hr hr' hσ hσ' hQ hf ht
  have hestimate := hbound Z d hZ (hdmin.trans_le hd).le hd' hU hT χ hχ a i
    ha ha' hmax r σ freq (hrmin.trans_le hr).le hr' hσ hσ' (hl d r hd hr) hQ hf ht
  exact hb d hd r (a-1/2) hr (by linarith) _ hestimate

end SevenEighths.HeckePrimeAmplitudeActual

end

end OAI
end OAIOriginalModule2102

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorPhysicalBins
Source SHA256: 848222fd8257e5d78436e51d7a86f3020dec98b24e0e6f1789787f8e3628dfb4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2103



namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace SevenEighths.HeckeDetectorPhysicalBins
open HeckeFamily HeckeDetectorPrimeFamily HeckePrimeAmplitudeBins
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem physical_bins (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmin dmax rmin τ ε e κ η mesh σmin σmax : ℝ)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hη : 0≤η) (hmesh : 0<mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ (data : RowData M) (cert : Ramification M data) (a : ℝ) (i : ℕ),
      51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum
        (HeckePrimeRay.twistedFamily M H hH (data.character M))
        (cert.nonprincipal M H hH) (3*(i+1 : ℕ)*Z^τ)<a+2*e →
    ∀ (r : ℝ) (z : ℂ), rmin≤r → r≤R → σmin≤1-z.re → 1-z.re≤σmax →
      M.absNorm^2*(Ideal.span {data.m}).absNorm*(Ideal.span {(72 : O)}).absNorm*
        (Ideal.span {data.u}).absNorm≤Z^d →
      |z.im|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ → (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
    let Q := HeckePrimeRow.canonicalPrimeAmplitude M H data.u W B ((Z^d)^r) z
    let g := amplitude ((Z^d)^r) (a-1/2) mesh Q
    0≤g ∧ g≤a-1/2 ∧ g∈labels (a-1/2) mesh ∧
      ‖Q‖≤((Z^d)^r)^(g+mesh) ∧ (0<g → (Z^d)^(2*r*g)≤‖Q‖^2) := by
  have hh := HeckePrimeAmplitudeActual.ray_amplitude_bins M H hH W A B hA hWs hW
    R dmin dmax rmin τ ε e κ η mesh σmin σmax hR hdmin hdmax hrmin
    hτ hε he he' hκ hη hmesh hbudget hgap
  filter_upwards [hh] with Z hZ
  intro d hd hd' hU hT data cert a i ha ha' hnext r z hr hr' hs hs' hQ hf ht
  have hQ' (θ : RayQuotient.Characters M H) :
      ((HeckePrimeRay.twistedFamily M H hH (data.character M) θ).modulus.absNorm : ℝ)≤Z^d := by
    have hb := data.twisted_conductor M H hH θ
    have hb' : ((HeckePrimeRay.twistedFamily M H hH (data.character M) θ).modulus.absNorm : ℝ)≤
        ((M.absNorm^2*(Ideal.span {data.m}).absNorm*(Ideal.span {(72 : O)}).absNorm*
          (Ideal.span {data.u}).absNorm : ℕ) : ℝ) := by exact_mod_cast hb
    exact hb'.trans (by exact_mod_cast hQ)
  have hb := hZ d hd hd' hU hT (data.character M) (cert.nonprincipal M H hH)
    a i ha ha' hnext r (1-z.re) z.im hr hr' hs hs' hQ' hf ht
  simpa only [data.amplitude_eq M H hH] using hb

end SevenEighths.HeckeDetectorPhysicalBins

end

end OAI
end OAIOriginalModule2103

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorPhysicalSelection
Source SHA256: a2ec5a5a0eebc9396bea8b8c73f413d82acb5eed72e70db90ec46d5a7cb3f301
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2104



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorPhysicalSelection
open HeckeFamily HeckePrimeAmplitudeBins
variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)

def physical {Row Slot : Type*} (row : Row→O) (W : Slot→ℝ→ℂ)
    (b w : Slot→ℝ) (z : Slot→ℂ) (U : ℝ) (u : Row) (s : Slot) : ℂ :=
  HeckePrimeRow.canonicalPrimeAmplitude M H (row u) (W s) (b s) (U^(w s)) (z s)

def weightedMean {Slot : Type*} (slots : Finset Slot) (w g : Slot→ℝ) : ℝ :=
  (∑ s∈slots,w s*g s)/(∑ s∈slots,w s)

theorem weightedMean_bounds {Slot : Type*} (slots : Finset Slot) (w g : Slot→ℝ)
    (δ : ℝ) (hw : ∀ s∈slots,0≤w s) (hL : 0<∑ s∈slots,w s)
    (hg : ∀ s∈slots,0≤g s ∧ g s≤δ/2) :
    0≤weightedMean slots w g ∧ weightedMean slots w g≤δ/2 := by
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun s hs => mul_nonneg (hw s hs) (hg s hs).1)) hL.le
  · apply (div_le_iff₀ hL).mpr
    calc
      _ ≤ ∑ s∈slots,w s*(δ/2) := Finset.sum_le_sum (fun s hs =>
        mul_le_mul_of_nonneg_left (hg s hs).2 (hw s hs))
      _ = _ := by rw [←Finset.sum_mul]; ring

omit [NeZero M] in
theorem select_physical_product {Row Slot : Type*} (rows : Finset Row) (hne : rows.Nonempty)
    (slots : Finset Slot) (row : Row→O) (W : Slot→ℝ→ℂ) (b w g : Slot→ℝ)
    (zs : Slot→ℂ) (U δ mesh binWidth z : ℝ)
    (hU : 1<U) (hδ : 0≤δ) (hmesh : 0≤mesh) (hbin : 0<binWidth)
    (hw : ∀ s∈slots,0<w s) (hwm : ∀ s∈slots,w s≤mesh)
    (hL : 0<∑ s∈slots,w s) (hz : 0≤z) (hzL : z≤∑ s∈slots,w s)
    (hbins : ∀ u∈rows,∀ s∈slots,
      amplitude (U^(w s)) (δ/2) binWidth (physical M H row W b w zs U u s)=g s) :
    ∃ selected : Finset Slot, selected⊆slots ∧ (∀ s∈selected,0<g s) ∧
      (∑ s∈selected,w s)≤z ∧
      ∀ u∈rows, U^(2*weightedMean slots w g*z-δ*mesh)≤
        ‖∏ s∈selected,physical M H row W b w zs U u s‖^2 := by
  obtain ⟨u0,hu0⟩ := hne
  have hg (s : Slot) (hs : s∈slots) : 0≤g s ∧ g s≤δ/2 := by
    rw [←hbins u0 hu0 s hs]
    exact amplitude_bounds _ _ _ _ (by positivity)
  obtain ⟨hq,hqδ⟩ := weightedMean_bounds slots w g δ (fun s hs => (hw s hs).le) hL hg
  have hm : weightedMean slots w g*(∑ s∈slots,w s)≤∑ s∈slots,w s*g s := by
    unfold weightedMean
    rw [div_mul_cancel₀ _ hL.ne']
  obtain ⟨selected,hsub,hpositive,hlen,hspike⟩ := common_bin_selection slots w g U δ mesh binWidth
    (weightedMean slots w g) z hU hδ hmesh hbin hw hwm hg hq hqδ hz hzL hm
  exact ⟨selected,hsub,hpositive,hlen,fun u hu => hspike _ (hbins u hu)⟩

end SevenEighths.HeckeDetectorPhysicalSelection

end

end OAI
end OAIOriginalModule2104

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorFiberSpikes
Source SHA256: 212baef4b50c9b070ba6156b1aa038f6f5c8ae8c3e9fa50f4f10bb3d70282da6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2105



namespace OAI

noncomputable section
open scoped Classical
open Set
namespace SevenEighths.HeckeDetectorFiberSpikes
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles

theorem fiber_spikes {Row Label : Type*} (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 0≤a)
    (w : ∀ u, Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(w u).label=label)
    (hJ : ∀ u∈rows,(w u).left=J) (hK : ∀ u∈rows,(w u).right=K) :
    let r := Real.logb U ((2 : ℝ)^J.val)
    let m := Real.logb U ((2 : ℝ)^K.val)
    ∀ u∈rows,
      (w u).zero.re∈Icc (0 : ℝ) 1 ∧
      |(w u).frequency|≤2*Real.pi*allowance+(3*i : ℕ)*T ∧
      U^((2*a-1)*r-2*ε)≤
        ‖polynomial (χ u label) true
          (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular (U^tstar) (U^r))
          (U^r) (w u).zero.re (w u).frequency‖^2 ∧
      U^((2*a-1)*m-2*ε)≤
        ‖polynomial (χ u label) false positiveAnnular (U^m) (w u).zero.re (w u).frequency‖^2 := by
  dsimp only
  intro u hu
  have hr : (w u).r=Real.logb U ((2 : ℝ)^J.val) := by rw [(w u).left_exponent hU,hJ u hu]
  have hm : (w u).m=Real.logb U ((2 : ℝ)^K.val) := by rw [(w u).right_exponent hU,hK u hu]
  refine ⟨⟨ha.trans (w u).zero_lower,(w u).real_part_upper⟩,(w u).frequency_bound,?_,?_⟩
  · simpa only [hr,hlabel u hu,Witness.frequency] using (w u).inverse_spike
  · simpa only [hm,hlabel u hu,Witness.frequency] using (w u).plain_spike

end SevenEighths.HeckeDetectorFiberSpikes

end

end OAI
end OAIOriginalModule2105

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorFiberEnergy
Source SHA256: 3a2ebd4bb7ec55e8dd6f2b64682ab834d084c706e8e2e71dacc9c630544d643c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2106




namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeDetectorFiberEnergy
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorRowwisePolynomial

theorem inverse_energy {Row Label : Type*} (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (ha : 0≤a)
    (w : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (W : ℝ→ℂ) (D wa wb E : ℝ) (P : Row→ℂ)
    (hD : 0<D) (hwb : 0≤wb) (hs : Function.support W⊆Icc wa wb) (hE : 0≤E)
    (height : ℝ) (hh : 0≤height) (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hraw : ∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈rows,‖polynomial (χ u label) true ((logProfile^[n]) W) D s t*P u‖^2≤E) :
    ∑ u∈rows,‖polynomial (χ u label) true W D (w u).zero.re (w u).frequency*P u‖^2≤
      12*(1+height)*E := by
  let S := HeckeInverseAmplification.scaleSupport (Real.log D) wb
  have hcover : ∀ J : Ideal O,J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S := by
    simpa only [Real.exp_log hD] using HeckeInverseAmplification.scaleSupport_cover
      W wa wb (Real.log D) (Real.log D) hwb hs (le_refl _)
  have hσ (u : Row) (hu : u∈rows) : (w u).zero.re∈Icc (0 : ℝ) 1 :=
    ⟨ha.trans (w u).zero_lower,(w u).real_part_upper⟩
  have hf (u : Row) (hu : u∈rows) : (w u).frequency∈Icc (-height) height :=
    abs_le.mp ((w u).frequency_bound.trans hfreq)
  have hb := HeckeDetectorRowwiseMarked.marked_rowwise rows (fun u => χ u label) true W D hD S hcover
    P 0 1 (-height) height E (by norm_num) (by linarith) (fun u => (w u).zero.re)
    (fun u => (w u).frequency) hσ hf
    (by simpa using hraw 0 (by omega)) (by simpa using hraw 1 (by omega))
    (by simpa using hraw 2 (by omega))
  refine hb.trans ?_
  nlinarith

theorem plain_energy {Row Label : Type*} (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (ha : 0≤a)
    (w : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (W : ℝ→ℂ) (D wa wb E : ℝ) (P : Row→ℂ)
    (hD : 0<D) (hwb : 0≤wb) (hs : Function.support W⊆Icc wa wb) (hE : 0≤E)
    (height : ℝ) (hh : 0≤height) (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hraw : ∀ j k : ℕ,j+k≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) W) D s t*
        polynomial (χ u label) false ((logProfile^[k]) W) D s t*P u‖^2≤E) :
    ∑ u∈rows,‖polynomial (χ u label) false W D (w u).zero.re (w u).frequency*
      polynomial (χ u label) false W D (w u).zero.re (w u).frequency*P u‖^2≤
      192*(1+height)*E := by
  let S := HeckeInverseAmplification.scaleSupport (Real.log D) wb
  have hcover : ∀ J : Ideal O,J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S := by
    simpa only [Real.exp_log hD] using HeckeInverseAmplification.scaleSupport_cover
      W wa wb (Real.log D) (Real.log D) hwb hs (le_refl _)
  have hσ (u : Row) (hu : u∈rows) : (w u).zero.re∈Icc (0 : ℝ) 1 :=
    ⟨ha.trans (w u).zero_lower,(w u).real_part_upper⟩
  have hf (u : Row) (hu : u∈rows) : (w u).frequency∈Icc (-height) height :=
    abs_le.mp ((w u).frequency_bound.trans hfreq)
  have hb := HeckeDetectorRowwisePlain.plain_squared_rowwise rows (fun u => χ u label) W D hD S hcover
    P 0 1 (-height) height E (by norm_num) (by linarith) hE (fun u => (w u).zero.re)
    (fun u => (w u).frequency) hσ hf hraw
  refine hb.trans ?_
  nlinarith

end SevenEighths.HeckeDetectorFiberEnergy

end

end OAI
end OAIOriginalModule2106

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorInverseFiberCount
Source SHA256: 1c83fbceb4bb669db72e508f7363c8352861e6110b5336989ebf2bd06b195d47
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2107



namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeDetectorInverseFiberCount
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial

def inverseTest (U tstar r : ℝ) : ℝ→ℂ :=
  HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular (U^tstar) (U^r)

variable (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ)

theorem inverse_fiber_count {Row Label Slot : Type*}
    (rows : Finset Row) (hne : rows.Nonempty) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 1/2≤a)
    (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(witness u).label=label)
    (hJ : ∀ u∈rows,(witness u).left=J) (hK : ∀ u∈rows,(witness u).right=K)
    (slots : Finset Slot) (row : Row→O) (W : Slot→ℝ→ℂ) (b widths g : Slot→ℝ) (zs : Slot→ℂ)
    (mesh binWidth z εm C height : ℝ) (hmesh : 0≤mesh) (hbin : 0<binWidth)
    (hw : ∀ s∈slots,0<widths s) (hwm : ∀ s∈slots,widths s≤mesh)
    (hL : 0<∑ s∈slots,widths s) (hz : 0≤z) (hzL : z≤∑ s∈slots,widths s)
    (hbins : ∀ u∈rows,∀ s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth
        (physical M H row W b widths zs U u s)=g s)
    (hC : 0≤C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hcap1 : Real.logb U ((2 : ℝ)^J.val)+2*z<1)
    (hcap2 : 2*Real.logb U ((2 : ℝ)^J.val)+8*z<3)
    (hraw : ∀ selected : Finset Slot, selected⊆slots →
      Real.logb U ((2 : ℝ)^J.val)+2*(∑ s∈selected,widths s)<1 →
      2*Real.logb U ((2 : ℝ)^J.val)+8*(∑ s∈selected,widths s)<3 →
      ∀ n : ℕ,n≤2 → ∀ σ∈Icc (0 : ℝ) 1,∀ freq∈Icc (-height) height,
        ∑ u∈rows,‖polynomial (χ u label) true
          ((logProfile^[n]) (inverseTest U tstar (Real.logb U ((2 : ℝ)^J.val))))
          (U^(Real.logb U ((2 : ℝ)^J.val))) σ freq*
            (∏ s∈selected,physical M H row W b widths zs U u s)‖^2≤C*U^(1+εm)) :
    (rows.card : ℝ)≤(12*(1+height)*C)*
      U^(1-(2*a-1)*Real.logb U ((2 : ℝ)^J.val)-2*weightedMean slots widths g*z+
        2*ε+(2*a-1)*mesh+εm) := by
  let r := Real.logb U ((2 : ℝ)^J.val)
  have hδ : 0≤2*a-1 := by linarith
  obtain ⟨selected,hsub,hpositive,hlen,hspike⟩ := select_physical_product M H rows hne slots
    row W b widths g zs U (2*a-1) mesh binWidth z hU hδ hmesh hbin hw hwm hL hz hzL hbins
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε tstar T allowance i hU
    (by linarith) witness label J K hlabel hJ hK
  have hcap1' : r+2*(∑ s∈selected,widths s)<1 := by dsimp [r]; linarith
  have hcap2' : 2*r+8*(∑ s∈selected,widths s)<3 := by dsimp [r]; linarith
  have hUp : 0<U := zero_lt_one.trans hU
  have hDp : 0<U^r := Real.rpow_pos_of_pos hUp _
  have hE : 0≤C*U^(1+εm) := mul_nonneg hC (Real.rpow_nonneg hUp.le _)
  have he := HeckeDetectorFiberEnergy.inverse_energy rows χ U a ε tstar T allowance i
    (by linarith) witness label (inverseTest U tstar r) (U^r) (1/4) (9/4) (C*U^(1+εm))
    (fun u => ∏ s∈selected,physical M H row W b widths zs U u s) hDp (by norm_num)
    (HeckeDetectorDyadicActual.inverse_profile_support _ _) hE height hheight hfreq
    (hraw selected hsub hcap1' hcap2')
  have he' : ∑ u∈rows,
      ‖polynomial (χ u label) true (inverseTest U tstar r) (U^r) (witness u).zero.re
        (witness u).frequency*(∏ s∈selected,physical M H row W b widths zs U u s)‖^2≤
      (12*(1+height)*C)*U^(1+εm) := by
    convert he using 1; ring
  exact HeckeDetectorRowCount.inverse_count rows (fun u => χ u label)
    (inverseTest U tstar r) (U^r) (fun u => (witness u).zero.re) (fun u => (witness u).frequency)
    (fun u => ∏ s∈selected,physical M H row W b widths zs U u s)
    U (2*a-1) r (weightedMean slots widths g) z (2*ε) ((2*a-1)*mesh) εm
    (12*(1+height)*C) hUp (fun u hu => (hsp u hu).2.2.1) hspike he'

end SevenEighths.HeckeDetectorInverseFiberCount

end

end OAI
end OAIOriginalModule2107

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorPlainFiberCount
Source SHA256: 59d4e231e772f7e2b696add18b8a1480db7d36d6f54cd3e207ac6db2e94659cc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2108


namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeDetectorPlainFiberCount
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial
variable (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ)

theorem plain_fiber_count {Row Label Slot : Type*}
    (rows : Finset Row) (hne : rows.Nonempty) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 1/2≤a)
    (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(witness u).label=label)
    (hJ : ∀ u∈rows,(witness u).left=J) (hK : ∀ u∈rows,(witness u).right=K)
    (slots : Finset Slot) (row : Row→O) (W : Slot→ℝ→ℂ) (b widths g : Slot→ℝ) (zs : Slot→ℂ)
    (mesh binWidth z κplain εm C height : ℝ) (hmesh : 0≤mesh) (hbin : 0<binWidth)
    (hw : ∀ s∈slots,0<widths s) (hwm : ∀ s∈slots,widths s≤mesh)
    (hL : 0<∑ s∈slots,widths s) (hz : 0≤z) (hzL : z≤∑ s∈slots,widths s)
    (hbins : ∀ u∈rows,∀ s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth
        (physical M H row W b widths zs U u s)=g s)
    (hκ : 0≤κplain) (hC : 0≤C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hcap : 2*Real.logb U ((2 : ℝ)^K.val)+6*κplain*z≤1)
    (hraw : ∀ selected : Finset Slot, selected⊆slots →
      2*Real.logb U ((2 : ℝ)^K.val)+6*κplain*(∑ s∈selected,widths s)≤1 →
      ∀ j k : ℕ,j+k≤2 → ∀ σ∈Icc (0 : ℝ) 1,∀ freq∈Icc (-height) height,
        ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
          polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
            (∏ s∈selected,physical M H row W b widths zs U u s)‖^2≤C*U^(1+εm)) :
    (rows.card : ℝ)≤(192*(1+height)*C)*
      U^(1-2*(2*a-1)*Real.logb U ((2 : ℝ)^K.val)-2*weightedMean slots widths g*z+
        4*ε+(2*a-1)*mesh+εm) := by
  let m := Real.logb U ((2 : ℝ)^K.val)
  have hδ : 0≤2*a-1 := by linarith
  obtain ⟨selected,hsub,hpositive,hlen,hspike⟩ := select_physical_product M H rows hne slots
    row W b widths g zs U (2*a-1) mesh binWidth z hU hδ hmesh hbin hw hwm hL hz hzL hbins
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε tstar T allowance i hU
    (by linarith) witness label J K hlabel hJ hK
  have hcap' : 2*m+6*κplain*(∑ s∈selected,widths s)≤1 := by
    have hh := mul_le_mul_of_nonneg_left hlen (show 0≤6*κplain by positivity)
    dsimp [m]
    linarith
  have hUp : 0<U := zero_lt_one.trans hU
  have hDp : 0<U^m := Real.rpow_pos_of_pos hUp _
  have hE : 0≤C*U^(1+εm) := mul_nonneg hC (Real.rpow_nonneg hUp.le _)
  have he := HeckeDetectorFiberEnergy.plain_energy rows χ U a ε tstar T allowance i
    (by linarith) witness label positiveAnnular (U^m) (1/4) (9/4) (C*U^(1+εm))
    (fun u => ∏ s∈selected,physical M H row W b widths zs U u s) hDp (by norm_num)
    positiveAnnular_support hE height hheight hfreq (hraw selected hsub hcap')
  have he' : ∑ u∈rows,
      ‖polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency*
        polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency*
        (∏ s∈selected,physical M H row W b widths zs U u s)‖^2≤
      (192*(1+height)*C)*U^(1+εm) := by
    convert he using 1; ring
  have hc := HeckeDetectorRowCount.plain_count rows (fun u => χ u label)
    positiveAnnular (U^m) (fun u => (witness u).zero.re) (fun u => (witness u).frequency)
    (fun u => ∏ s∈selected,physical M H row W b widths zs U u s)
    U (2*a-1) m (weightedMean slots widths g) z (2*ε) ((2*a-1)*mesh) εm
    (192*(1+height)*C) hUp (fun u hu => (hsp u hu).2.2.2) hspike he'
  convert hc using 1; congr 2; ring

end SevenEighths.HeckeDetectorPlainFiberCount

end

end OAI
end OAIOriginalModule2108

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorNoSlotInverseCount
Source SHA256: 379a8ec696d698d261265c4a06704ebf3bcd8f715bf664edd3d095b44480b6a7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2109




namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter
namespace SevenEighths.HeckeDetectorNoSlotInverseCount
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeInverseAmplification
open HeckeDetectorCoefficientTransfer HeckeDetectorInverseFiberCount

theorem no_slot_inverse_count
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (R εm : ℝ) (hR : 0≤R) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ {Label : Type*} (rows : Finset FreeRow) (χ : FreeRow→Label→Character)
        (a ε tstar T allowance : ℝ) (i : ℕ), 1<U → 1/2≤a →
      ∀ (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
        (label : Label) (J K : Fin (dyadicLength U)),
      (∀ u∈rows,(witness u).label=label) →
      (∀ u∈rows,(witness u).left=J) → (∀ u∈rows,(witness u).right=K) →
      0≤Real.logb U ((2 : ℝ)^J.val) → Real.logb U ((2 : ℝ)^J.val)≤R →
      ∀ (data : RowData) (reverse : Bool) (C height : ℝ),0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      (∀ u∈rows,((Ideal.span {u.val}).absNorm : ℝ)≤U) →
      (∀ u∈rows,∀ I : Ideal O,idealCoeff (χ u label) I=
        if reverse then starRingEnd ℂ (idealCoeff (data.character ⟨u.val,u.property.1⟩) I)
        else idealCoeff (data.character ⟨u.val,u.property.1⟩) I) →
      (∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
        let W := twistProfile (logTest
          (orientedProfile reverse (inverseTest U tstar (Real.logb U ((2 : ℝ)^J.val)))) n) s t
        RawMoment data W c κ C ∧ RawMoment data (scaleProfile W) c κ C) →
      (rows.card : ℝ)≤(12*(1+height)*(C*K₀))*
        U^(sourceExponent (Real.logb U ((2 : ℝ)^J.val))-
          (2*a-1)*Real.logb U ((2 : ℝ)^J.val)+2*ε+εm) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,he⟩ := no_slot_rowwise_endpoint M H hH S φ hφ hφc hφp hφ0 hφne
    a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB R εm hR hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [he] with U he
  intro Label rows χ a ε tstar T allowance i hU ha witness label J K hlabel hJ hK hr hrR
    data reverse C height hC hheight hfreq hrows hcoeff hraw
  let r := Real.logb U ((2 : ℝ)^J.val)
  let V := orientedProfile reverse (inverseTest U tstar r)
  have hUp : 0<U := zero_lt_one.trans hU
  have hD : 0<U^r := Real.rpow_pos_of_pos hUp _
  have hbase := HeckeDetectorDyadicActual.inverse_profile_support (U^tstar) (U^r)
  have hs : Function.support V⊆Icc (1/4 : ℝ) (9/4) := by
    cases reverse
    · exact hbase
    · simpa only [V,orientedProfile,Bool.true_eq,ite_true,conjugate_profile_support,inverseTest] using hbase
  have hb := HeckeDetectorDyadicActual.inverse_profile_smooth (U^tstar) (U^r)
  have hV : ContDiff ℝ ∞ V := by
    cases reverse
    · exact hb
    · exact conjugate_profile_smooth _ hb
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε tstar T allowance i hU
    (by linarith) witness label J K hlabel hJ hK
  have hσ (u : FreeRow) (hu : u∈rows) : (witness u).zero.re∈Icc (0 : ℝ) 1 := (hsp u hu).1
  have hf (u : FreeRow) (hu : u∈rows) :
      orientedFrequency reverse (witness u).frequency∈Icc (-height) height := by
    apply abs_le.mp
    rw [orientedFrequency_abs]
    exact (hsp u hu).2.1.trans hfreq
  have hen := he r data rows V (1/4) (9/4) C height (fun u => (witness u).zero.re)
    (fun u => orientedFrequency reverse (witness u).frequency)
    hr hrR hC hheight (by norm_num) (by norm_num) hs hV hrows hσ hf hraw
  have hspike (u : FreeRow) (hu : u∈rows) : U^((2*a-1)*r-2*ε)≤
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true V (U^r) (witness u).zero.re
        (orientedFrequency reverse (witness u).frequency)‖^2 := by
    have hh := (hsp u hu).2.2.1
    rw [norm_of_oriented_coefficients (χ u label) (data.character ⟨u.val,u.property.1⟩)
      reverse (hcoeff u hu) true _ _ _ _ hD] at hh
    exact hh
  have hen' : ∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true V (U^r) (witness u).zero.re
        (orientedFrequency reverse (witness u).frequency)‖^2≤
      (12*(1+height)*(C*K₀))*U^(sourceExponent r+εm) := by
    convert hen using 1; ring
  have hc' := HeckeDetectorRowCount.card_of_energy rows _ U ((2*a-1)*r-2*ε)
    (sourceExponent r+εm) (12*(1+height)*(C*K₀)) hUp hspike hen'
  convert hc' using 1; congr 2; ring

end SevenEighths.HeckeDetectorNoSlotInverseCount

end

end OAI
end OAIOriginalModule2109

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorNoSlotPlainCount
Source SHA256: 59978157af54d9518bfcf2ddec8059ce393bc123606636180e3a868732923d23
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2110


namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeDetectorNoSlotPlainCount
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorRowwisePolynomial

theorem no_slot_plain_count {Row Label : Type*}
    (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 0≤a)
    (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(witness u).label=label)
    (hJ : ∀ u∈rows,(witness u).left=J) (hK : ∀ u∈rows,(witness u).right=K)
    (εm C height : ℝ) (hC : 0≤C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hraw : ∀ j k : ℕ,j+k≤2 → ∀ σ∈Icc (0 : ℝ) 1,∀ freq∈Icc (-height) height,
      ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
        (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
        polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
        (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq‖^2≤
          C*U^(max 1 (2*Real.logb U ((2 : ℝ)^K.val))+εm)) :
    (rows.card : ℝ)≤(192*(1+height)*C)*
      U^(max 1 (2*Real.logb U ((2 : ℝ)^K.val))-
        2*(2*a-1)*Real.logb U ((2 : ℝ)^K.val)+4*ε+εm) := by
  let m := Real.logb U ((2 : ℝ)^K.val)
  have hUp : 0<U := zero_lt_one.trans hU
  have hDp : 0<U^m := Real.rpow_pos_of_pos hUp _
  have hE : 0≤C*U^(max 1 (2*m)+εm) := mul_nonneg hC (Real.rpow_nonneg hUp.le _)
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε tstar T allowance i hU ha
    witness label J K hlabel hJ hK
  have he := HeckeDetectorFiberEnergy.plain_energy rows χ U a ε tstar T allowance i ha
    witness label positiveAnnular (U^m) (1/4) (9/4) (C*U^(max 1 (2*m)+εm))
    (fun _ => 1) hDp (by norm_num) positiveAnnular_support hE height hheight hfreq
    (by simpa only [mul_one] using hraw)
  simp only [mul_one] at he
  have hs (u : Row) (hu : u∈rows) : U^(2*((2*a-1)*m-2*ε))≤
      ‖polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency*
        polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency‖^2 := by
    rw [show 2*((2*a-1)*m-2*ε)=((2*a-1)*m-2*ε)+((2*a-1)*m-2*ε) by ring,
      Real.rpow_add hUp,norm_mul,mul_pow]
    exact mul_le_mul (hsp u hu).2.2.2 (hsp u hu).2.2.2
      (Real.rpow_nonneg hUp.le _) (sq_nonneg _)
  have he' : ∑ u∈rows,
      ‖polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency*
        polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency‖^2≤
      (192*(1+height)*C)*U^(max 1 (2*m)+εm) := by convert he using 1; ring
  have hh := HeckeDetectorRowCount.card_of_energy rows _ U (2*((2*a-1)*m-2*ε))
    (max 1 (2*m)+εm) (192*(1+height)*C) hUp hs he'
  convert hh using 1; congr 2; ring

end SevenEighths.HeckeDetectorNoSlotPlainCount

end

end OAI
end OAIOriginalModule2110

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorRawFiber
Source SHA256: 491911b0b17d19943fdb1b43f479e741279e0c0c2b9f1e9e9c5d11de24335c5d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2111





namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set
namespace SevenEighths.HeckeDetectorRawFiber
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorWitnessRows
open HeckeDetectorSupportedWitness HeckeDetectorCoefficientTransfer HeckeDetectorInverseFiberCount
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles

structure Fiber (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ) (Label Slot : Type*)
    (U a ε tstar T allowance : ℝ) (i : ℕ) where
  rows : Finset FreeRow
  nonempty : rows.Nonempty
  family : FreeRow→Label→Character
  witness : ∀ u,SupportedWitness (family u) U a ε tstar T allowance i
  label : Label
  left : Fin (dyadicLength U)
  right : Fin (dyadicLength U)
  fixed_label : ∀ u∈rows,(witness u).label=label
  fixed_left : ∀ u∈rows,(witness u).left=left
  fixed_right : ∀ u∈rows,(witness u).right=right
  row_norm : ∀ u∈rows,((Ideal.span {u.val}).absNorm : ℝ)≤U
  rowData : RowData
  reverse : Bool
  row_coeff : ∀ u∈rows,∀ J : Ideal O,idealCoeff (family u label) J=
    if reverse then starRingEnd ℂ (idealCoeff (rowData.character ⟨u.val,u.property.1⟩) J)
    else idealCoeff (rowData.character ⟨u.val,u.property.1⟩) J
  slots : Finset Slot
  profile : Slot→ℝ→ℂ
  upper : Slot→ℝ
  widths : Slot→ℝ
  external : Slot→ℂ
  bin : Slot→ℝ
  mesh : ℝ
  binWidth : ℝ
  mesh_nonneg : 0≤mesh
  binWidth_pos : 0<binWidth
  widths_pos : ∀ s∈slots,0<widths s
  widths_mesh : ∀ s∈slots,widths s≤mesh
  supply : 7/37≤∑ s∈slots,widths s
  fixed_bin : ∀ u∈rows,∀ s∈slots,
    HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth
      (physical M H (fun u : FreeRow => u.val) profile upper widths external U u s)=bin s

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

def Fiber.r (F : Fiber M H Label Slot U a ε tstar T allowance i) : ℝ := Real.logb U ((2 : ℝ)^F.left.val)
def Fiber.m (F : Fiber M H Label Slot U a ε tstar T allowance i) : ℝ := Real.logb U ((2 : ℝ)^F.right.val)
def Fiber.q (F : Fiber M H Label Slot U a ε tstar T allowance i) : ℝ := weightedMean F.slots F.widths F.bin
def Fiber.inverseProfile (F : Fiber M H Label Slot U a ε tstar T allowance i) : ℝ→ℂ := inverseTest U tstar F.r
def Fiber.physicalProduct (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (u : FreeRow) : ℂ :=
  ∏ s∈selected,physical M H (fun u : FreeRow => u.val) F.profile F.upper F.widths F.external U u s

structure Moments (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (Δ c κ C height εm : ℝ) : Prop where
  inverse_raw : ∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
    let W := twistProfile (logTest (orientedProfile F.reverse F.inverseProfile) n) s t
    RawMoment F.rowData W c κ C ∧ RawMoment F.rowData (scaleProfile W) c κ C
  inverse_marked : ∀ selected : Finset Slot,selected⊆F.slots →
    F.r+2*(∑ s∈selected,F.widths s)<1 → 2*F.r+8*(∑ s∈selected,F.widths s)<3 →
    ∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈F.rows,‖polynomial (F.family u F.label) true ((logProfile^[n]) F.inverseProfile)
        (U^F.r) s t*F.physicalProduct selected u‖^2≤C*U^(1+εm)
  plain_marked : ∀ selected : Finset Slot,selected⊆F.slots →
    2*F.m+6*(3/4+2*Δ)*(∑ s∈selected,F.widths s)≤1 →
    ∀ j k : ℕ,j+k≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) s t*
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) s t*
          F.physicalProduct selected u‖^2≤C*U^(1+εm)
  plain_unmarked : ∀ j k : ℕ,j+k≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) s t*
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) s t‖^2≤
          C*U^(max 1 (2*F.m)+εm)

theorem Fiber.mean_bounds (F : Fiber M H Label Slot U a ε tstar T allowance i) (ha : 1/2≤a) :
    0≤F.q ∧ F.q≤(2*a-1)/2 := by
  obtain ⟨u,hu⟩ := F.nonempty
  apply weightedMean_bounds F.slots F.widths F.bin (2*a-1)
    (fun s hs => (F.widths_pos s hs).le) (by linarith [F.supply])
  intro s hs
  rw [←F.fixed_bin u hu s hs]
  exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by linarith)

end SevenEighths.HeckeDetectorRawFiber

end

end OAI
end OAIOriginalModule2111

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorFiberPartition
Source SHA256: b79c31ccef2cfbbd8ffe03b6757ccbe69318f6ee0dbe7ae880f76161ef669173
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2112



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorFiberPartition
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection

abbrev BinLabel {Slot : Type*} (slots : Finset Slot) (cap mesh : ℝ) :=
  slots → ↥(HeckePrimeAmplitudeBins.labels cap mesh)

def amplitudeLabel {Row Slot : Type*} (slots : Finset Slot) (U cap mesh : ℝ)
    (hm : 0<mesh) (widths : Slot→ℝ) (physical : Row→Slot→ℂ) (u : Row) : BinLabel slots cap mesh :=
  fun s => ⟨HeckePrimeAmplitudeBins.amplitude (U^(widths s)) cap mesh (physical u s),
    HeckePrimeAmplitudeBins.amplitude_mem_labels _ _ _ _ hm⟩

def fiber {Row Label Slot : Type*} (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (slots : Finset Slot) (mesh : ℝ) (hm : 0<mesh) (widths : Slot→ℝ)
    (physical : Row→Slot→ℂ) (bin : BinLabel slots ((2*a-1)/2) mesh)
    (label : Label) (J K : Fin (dyadicLength U)) : Finset Row :=
  rows.filter (fun u => amplitudeLabel slots U ((2*a-1)/2) mesh hm widths physical u=bin ∧
    (w u).label=label ∧ (w u).left=J ∧ (w u).right=K)

theorem card_eq_sum_fibers {Row Label Slot : Type*} [Fintype Label]
    (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (slots : Finset Slot) (mesh : ℝ) (hm : 0<mesh) (widths : Slot→ℝ)
    (physical : Row→Slot→ℂ) :
    rows.card=∑ bin : BinLabel slots ((2*a-1)/2) mesh, ∑ label : Label,
      ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
        (fiber rows χ U a ε tstar T allowance i w slots mesh hm widths physical bin label J K).card := by
  have hh := Finset.card_eq_sum_card_fiberwise (s:=rows) (t:=Finset.univ)
    (f:=fun u => (amplitudeLabel slots U ((2*a-1)/2) mesh hm widths physical u,
      (w u).label,(w u).left,(w u).right)) (by intro u hu; exact Finset.mem_univ _)
  simpa only [Fintype.sum_prod_type,Prod.mk.injEq,fiber] using hh

def binValue {Slot : Type*} (slots : Finset Slot) (cap mesh : ℝ)
    (bin : BinLabel slots cap mesh) (s : Slot) : ℝ :=
  if hs : s∈slots then (bin ⟨s,hs⟩).val else 0

theorem fixed_bin {Row Label Slot : Type*}
    (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (slots : Finset Slot) (mesh : ℝ) (hm : 0<mesh) (widths : Slot→ℝ)
    (physical : Row→Slot→ℂ) (bin : BinLabel slots ((2*a-1)/2) mesh)
    (label : Label) (J K : Fin (dyadicLength U)) (u : Row)
    (hu : u∈fiber rows χ U a ε tstar T allowance i w slots mesh hm widths physical bin label J K)
    (s : Slot) (hs : s∈slots) :
    HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) mesh (physical u s)=
      binValue slots ((2*a-1)/2) mesh bin s := by
  have he := (Finset.mem_filter.mp hu).2.1
  have hv := congrArg (fun f : BinLabel slots ((2*a-1)/2) mesh => (f ⟨s,hs⟩).val) he
  simpa only [amplitudeLabel,binValue,dite_eq_left hs] using hv

def toFiber (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ) {Label Slot : Type*}
    (rows : Finset FreeRow) (χ : FreeRow→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (hrow : ∀ u∈rows,((Ideal.span {u.val}).absNorm : ℝ)≤U)
    (data : Label→RowData) (reverse : Label→Bool)
    (hcoeff : ∀ u∈rows,∀ j,∀ I : Ideal O,idealCoeff (χ u j) I=
      if reverse j then starRingEnd ℂ (idealCoeff ((data j).character ⟨u.val,u.property.1⟩) I)
      else idealCoeff ((data j).character ⟨u.val,u.property.1⟩) I)
    (slots : Finset Slot) (profile : Slot→ℝ→ℂ) (upper widths : Slot→ℝ) (external : Slot→ℂ)
    (mesh binWidth : ℝ) (hmesh : 0≤mesh) (hbw : 0<binWidth)
    (hw : ∀ s∈slots,0<widths s) (hwmesh : ∀ s∈slots,widths s≤mesh)
    (hsupply : 7/37≤∑ s∈slots,widths s)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) (label : Label)
    (J K : Fin (dyadicLength U))
    (hne : (fiber rows χ U a ε tstar T allowance i w slots binWidth hbw widths
      (physical M H (fun u : FreeRow => u.val) profile upper widths external U) bin label J K).Nonempty) :
    Fiber M H Label Slot U a ε tstar T allowance i where
  rows := fiber rows χ U a ε tstar T allowance i w slots binWidth hbw widths
    (physical M H (fun u : FreeRow => u.val) profile upper widths external U) bin label J K
  nonempty := hne
  family := χ
  witness := w
  label := label
  left := J
  right := K
  fixed_label := fun _u hu => (Finset.mem_filter.mp hu).2.2.1
  fixed_left := fun _u hu => (Finset.mem_filter.mp hu).2.2.2.1
  fixed_right := fun _u hu => (Finset.mem_filter.mp hu).2.2.2.2
  row_norm := fun u hu => hrow u (Finset.mem_filter.mp hu).1
  rowData := data label
  reverse := reverse label
  row_coeff := fun u hu => hcoeff u (Finset.mem_filter.mp hu).1 label
  slots := slots
  profile := profile
  upper := upper
  widths := widths
  external := external
  bin := binValue slots ((2*a-1)/2) binWidth bin
  mesh := mesh
  binWidth := binWidth
  mesh_nonneg := hmesh
  binWidth_pos := hbw
  widths_pos := hw
  widths_mesh := hwmesh
  supply := hsupply
  fixed_bin := fun u hu s hs => fixed_bin rows χ U a ε tstar T allowance i w slots binWidth hbw widths
    (physical M H (fun u : FreeRow => u.val) profile upper widths external U) bin label J K u hu s hs

end SevenEighths.HeckeDetectorFiberPartition

end

end OAI
end OAIOriginalModule2112

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorAmplitudeFirst
Source SHA256: d787f9d44bd8e3840aac72c2e26cd133cf0bc2e631fce7229c9e4f0623c7ca12
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2113



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorAmplitudeFirst
open HeckeFamily HeckeDetectorSupportedWitness HeckeDetectorFiberPartition
open HeckeDetectorPhysicalSelection HeckeDetectorAdaptiveCutoff

def amplitudeRows {Row Slot : Type*} (rows : Finset Row) (slots : Finset Slot)
    (U cap mesh : ℝ) (hm : 0<mesh) (widths : Slot→ℝ) (physical : Row→Slot→ℂ)
    (bin : BinLabel slots cap mesh) : Finset Row :=
  rows.filter (fun u => amplitudeLabel slots U cap mesh hm widths physical u=bin)

def rowMean {Row Slot : Type*} (slots : Finset Slot) (U cap mesh : ℝ)
    (widths : Slot→ℝ) (physical : Row→Slot→ℂ) (u : Row) : ℝ :=
  weightedMean slots widths (fun s => HeckePrimeAmplitudeBins.amplitude (U^(widths s)) cap mesh (physical u s))

def classMean {Slot : Type*} (slots : Finset Slot) (cap mesh : ℝ)
    (widths : Slot→ℝ) (bin : BinLabel slots cap mesh) : ℝ :=
  weightedMean slots widths (binValue slots cap mesh bin)

theorem rowMean_eq {Row Slot : Type*} (rows : Finset Row) (slots : Finset Slot)
    (U cap mesh : ℝ) (hm : 0<mesh) (widths : Slot→ℝ) (physical : Row→Slot→ℂ)
    (bin : BinLabel slots cap mesh) (u : Row)
    (hu : u∈amplitudeRows rows slots U cap mesh hm widths physical bin) :
    rowMean slots U cap mesh widths physical u=classMean slots cap mesh widths bin := by
  have he := (Finset.mem_filter.mp hu).2
  unfold rowMean classMean weightedMean
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  have hv := congrArg (fun f : BinLabel slots cap mesh => (f ⟨s,hs⟩).val) he
  have hval : HeckePrimeAmplitudeBins.amplitude (U^(widths s)) cap mesh (physical u s)=
      binValue slots cap mesh bin s := by
    simpa only [amplitudeLabel,binValue,dite_eq_left hs] using hv
  exact congrArg (fun x => widths s*x) hval

theorem classMean_bounds {Row Slot : Type*} (rows : Finset Row) (slots : Finset Slot)
    (U δ mesh : ℝ) (hm : 0<mesh) (widths : Slot→ℝ) (physical : Row→Slot→ℂ)
    (bin : BinLabel slots (δ/2) mesh) (hδ : 0≤δ)
    (hw : ∀ s∈slots,0≤widths s) (hsupply : 0<∑ s∈slots,widths s)
    (hne : (amplitudeRows rows slots U (δ/2) mesh hm widths physical bin).Nonempty) :
    0≤classMean slots (δ/2) mesh widths bin ∧ classMean slots (δ/2) mesh widths bin≤δ/2 := by
  obtain ⟨u,hu⟩ := hne
  rw [←rowMean_eq rows slots U (δ/2) mesh hm widths physical bin u hu]
  apply weightedMean_bounds slots widths _ δ hw hsupply
  intro s hs
  exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by linarith)

def recut {Label : Type*} {χ : Label→Character} {U a ε t t' T allowance : ℝ} {i : ℕ}
    (w : SupportedWitness χ U a ε t T allowance i) (he : t=t') :
    SupportedWitness χ U a ε t' T allowance i := he ▸ w

theorem recut_values {Label : Type*} {χ : Label→Character} {U a ε t t' T allowance : ℝ} {i : ℕ}
    (w : SupportedWitness χ U a ε t T allowance i) (he : t=t') :
    (recut w he).label=w.label ∧ (recut w he).zero=w.zero ∧
    (recut w he).left=w.left ∧ (recut w he).right=w.right ∧
    (recut w he).nu=w.nu ∧ (recut w he).r=w.r ∧ (recut w he).m=w.m := by
  cases he
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def classWitness {Row Label Slot : Type*} (rows : Finset Row) (slots : Finset Slot)
    (χ : Row→Label→Character) (U a ε T allowance mesh : ℝ) (i : ℕ) (hm : 0<mesh)
    (widths : Slot→ℝ) (physical : Row→Slot→ℂ)
    (w : ∀ u : rows,SupportedWitness (χ u) U a ε
      (cutoff (2*a-1) (rowMean slots U ((2*a-1)/2) mesh widths physical u)) T allowance i)
    (bin : BinLabel slots ((2*a-1)/2) mesh)
    (u : amplitudeRows rows slots U ((2*a-1)/2) mesh hm widths physical bin) :
    SupportedWitness (χ u) U a ε
      (cutoff (2*a-1) (classMean slots ((2*a-1)/2) mesh widths bin)) T allowance i :=
  recut (w ⟨u.val,(Finset.mem_filter.mp u.property).1⟩)
    (congrArg (cutoff (2*a-1))
      (rowMean_eq rows slots U ((2*a-1)/2) mesh hm widths physical bin u.val u.property))

theorem card_eq_sum_amplitudeRows {Row Slot : Type*} (rows : Finset Row) (slots : Finset Slot)
    (U cap mesh : ℝ) (hm : 0<mesh) (widths : Slot→ℝ) (physical : Row→Slot→ℂ) :
    rows.card=∑ bin : BinLabel slots cap mesh,(amplitudeRows rows slots U cap mesh hm widths physical bin).card := by
  exact Finset.card_eq_sum_card_fiberwise (s:=rows) (t:=Finset.univ)
    (f:=amplitudeLabel slots U cap mesh hm widths physical) (by intro u hu; exact Finset.mem_univ _)

end SevenEighths.HeckeDetectorAmplitudeFirst

end

end OAI
end OAIOriginalModule2113

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorBatch
Source SHA256: bd7bf9bedfe6b8c8bfa7584b5bd2455238663bb29dec0d51516847068e4e2c04
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2114


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorBatch
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorFiberPartition
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection

structure Batch (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ) (Label Slot : Type*)
    (U a ε tstar T allowance : ℝ) (i : ℕ) where
  rows : Finset FreeRow
  family : FreeRow→Label→Character
  witness : ∀ u,SupportedWitness (family u) U a ε tstar T allowance i
  row_norm : ∀ u∈rows,((Ideal.span {u.val}).absNorm : ℝ)≤U
  data : Label→RowData
  reverse : Label→Bool
  row_coeff : ∀ u∈rows,∀ j,∀ I : Ideal O,idealCoeff (family u j) I=
    if reverse j then starRingEnd ℂ (idealCoeff ((data j).character ⟨u.val,u.property.1⟩) I)
    else idealCoeff ((data j).character ⟨u.val,u.property.1⟩) I
  slots : Finset Slot
  profile : Slot→ℝ→ℂ
  upper : Slot→ℝ
  widths : Slot→ℝ
  external : Slot→ℂ
  mesh : ℝ
  binWidth : ℝ
  mesh_nonneg : 0≤mesh
  binWidth_pos : 0<binWidth
  widths_pos : ∀ s∈slots,0<widths s
  widths_mesh : ∀ s∈slots,widths s≤mesh
  supply : 7/37≤∑ s∈slots,widths s

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

abbrev Batch.Bin (B : Batch M H Label Slot U a ε tstar T allowance i) :=
  BinLabel B.slots ((2*a-1)/2) B.binWidth

def Batch.fiberRows (B : Batch M H Label Slot U a ε tstar T allowance i)
    (bin : B.Bin) (j : Label) (J K : Fin (dyadicLength U)) : Finset FreeRow :=
  fiber B.rows B.family U a ε tstar T allowance i B.witness B.slots B.binWidth B.binWidth_pos B.widths
    (physical M H (fun u : FreeRow => u.val) B.profile B.upper B.widths B.external U) bin j J K

def Batch.fiber (B : Batch M H Label Slot U a ε tstar T allowance i)
    (bin : B.Bin) (j : Label) (J K : Fin (dyadicLength U))
    (hne : (B.fiberRows bin j J K).Nonempty) : Fiber M H Label Slot U a ε tstar T allowance i :=
  toFiber M H B.rows B.family U a ε tstar T allowance i B.witness B.row_norm B.data B.reverse
    B.row_coeff B.slots B.profile B.upper B.widths B.external B.mesh B.binWidth B.mesh_nonneg
    B.binWidth_pos B.widths_pos B.widths_mesh B.supply bin j J K hne

def Batch.q (B : Batch M H Label Slot U a ε tstar T allowance i) (bin : B.Bin) : ℝ :=
  weightedMean B.slots B.widths (binValue B.slots ((2*a-1)/2) B.binWidth bin)

theorem Batch.card_eq_sum_fibers [Fintype Label] (B : Batch M H Label Slot U a ε tstar T allowance i) :
    B.rows.card=∑ bin : B.Bin, ∑ j : Label, ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
      (B.fiberRows bin j J K).card :=
  HeckeDetectorFiberPartition.card_eq_sum_fibers B.rows B.family U a ε tstar T allowance i B.witness
    B.slots B.binWidth B.binWidth_pos B.widths
    (physical M H (fun u : FreeRow => u.val) B.profile B.upper B.widths B.external U)

theorem Batch.card_bound [Fintype Label] (B : Batch M H Label Slot U a ε tstar T allowance i)
    (C : ℝ) (exponent : B.Bin→ℝ) (hC : 0≤C) (hU : 0<U)
    (hfiber : ∀ bin j J K,∀ hne : (B.fiberRows bin j J K).Nonempty,
      ((B.fiber bin j J K hne).rows.card : ℝ)≤C*U^(exponent bin)) :
    (B.rows.card : ℝ)≤(Fintype.card Label : ℝ)*(dyadicLength U : ℝ)^2*C*
      ∑ bin : B.Bin,U^(exponent bin) := by
  have he : (B.rows.card : ℝ)=∑ bin : B.Bin, ∑ j : Label,
      ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
        ((B.fiberRows bin j J K).card : ℝ) := by exact_mod_cast B.card_eq_sum_fibers
  rw [he]
  calc
    _ ≤ ∑ bin : B.Bin, ∑ j : Label, ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
        C*U^(exponent bin) := by
      apply Finset.sum_le_sum
      intro bin _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro J _
      apply Finset.sum_le_sum
      intro K _
      by_cases hn : (B.fiberRows bin j J K).Nonempty
      · exact hfiber bin j J K hn
      · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
        simp only [Finset.card_empty,Nat.cast_zero]
        exact mul_nonneg hC (Real.rpow_nonneg hU.le _)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      simp_rw [←mul_assoc]
      rw [←Finset.mul_sum]
      ring

end SevenEighths.HeckeDetectorBatch

end

end OAI
end OAIOriginalModule2114

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorClassBudget
Source SHA256: 5e6a0ec5c45c2204143d2a224f460e629de2038e958141fff469f09b8214e655
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2115



namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.HeckeDetectorClassBudget
open HeckeDetectorFiberPartition HeckeDetectorWitnessRows

def alphabetBound (mesh : ℝ) : ℕ := 2+(⌈(1/2 : ℝ)/mesh⌉+1 : ℤ).toNat

theorem labels_card_le (cap mesh : ℝ) (hcap : cap≤1/2) (hm : 0<mesh) :
    (HeckePrimeAmplitudeBins.labels cap mesh).card≤alphabetBound mesh := by
  have hceil : ⌈cap/mesh⌉≤⌈(1/2 : ℝ)/mesh⌉ :=
    Int.ceil_mono (div_le_div_of_nonneg_right hcap hm.le)
  have hsub : Finset.Icc (0 : ℤ) ⌈cap/mesh⌉ ⊆ Finset.Icc (0 : ℤ) ⌈(1/2 : ℝ)/mesh⌉ := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2.trans hceil⟩
  have h1 := Finset.card_insert_le (0 : ℝ)
    (insert cap ((Finset.Icc (0 : ℤ) ⌈cap/mesh⌉).image (fun n : ℤ => mesh*(n : ℝ))))
  have h2 := Finset.card_insert_le cap
    ((Finset.Icc (0 : ℤ) ⌈cap/mesh⌉).image (fun n : ℤ => mesh*(n : ℝ)))
  have h3 := Finset.card_image_le (s:=Finset.Icc (0 : ℤ) ⌈cap/mesh⌉)
    (f:=fun n : ℤ => mesh*(n : ℝ))
  have h4 := Finset.card_le_card hsub
  simp only [Int.card_Icc,sub_zero] at h4 h3
  unfold HeckePrimeAmplitudeBins.labels alphabetBound
  omega

theorem bin_card_le {Slot : Type*} (slots : Finset Slot) (cap mesh : ℝ)
    (hcap : cap≤1/2) (hm : 0<mesh) :
    Fintype.card (BinLabel slots cap mesh)≤(alphabetBound mesh)^slots.card := by
  simpa only [BinLabel,Fintype.card_fun,Fintype.card_coe] using
    Nat.pow_le_pow_left (labels_card_le cap mesh hcap hm) slots.card

theorem dyadic_cost_eventually (η : ℝ) (hη : 0<η) :
    ∃ K : ℝ,0≤K ∧ ∀ᶠ U : ℝ in atTop,(dyadicLength U : ℝ)^2≤K*U^η := by
  let K := 625/(Real.log 2)^2
  have hK : 0≤K := by positivity
  have hlog := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hη).bound (by norm_num : (0 : ℝ)<1)
  refine ⟨K,hK,?_⟩
  filter_upwards [hlog,eventually_ge_atTop (2 : ℝ)] with U hlog hU
  have hUp : 0<U := by linarith
  have hs : (Real.log U)^2≤U^η := by
    simpa only [Real.rpow_two,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.log U)),
      abs_of_nonneg (Real.rpow_nonneg hUp.le _),one_mul] using hlog
  have hd := HeckeDetectorBudget.source_pair_count_bound U hU
  calc
    (dyadicLength U : ℝ)^2 ≤ 625*(Real.logb 2 U)^2 := hd
    _ = K*(Real.log U)^2 := by unfold K Real.logb; ring
    _ ≤ K*U^η := mul_le_mul_of_nonneg_left hs hK

end SevenEighths.HeckeDetectorClassBudget

end

end OAI
end OAIOriginalModule2115

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorRawBranches
Source SHA256: 696bbacc691905ef06aa8934946185ae5d158907a93167d08005bd5da4ad3a4c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2116


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRawFiber
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open HeckeDetectorInverseFiberCount HeckeDetectorPlainFiberCount HeckeDetectorNoSlotPlainCount
variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

theorem Fiber.lengths (F : Fiber M H Label Slot U a ε tstar T allowance i) (hU : 1<U) :
    tstar-F.r-ε≤F.m ∧ F.r≤tstar+ε ∧ F.m≤1/2+75*ε ∧ tstar-1/2-76*ε≤F.r ∧ 0≤F.m :=
  fiber_lengths F.rows F.nonempty F.family U a ε tstar T allowance i hU F.witness
    F.left F.right F.fixed_left F.fixed_right

theorem Fiber.inverse_marked_count (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {Δ c κ C height εm : ℝ} (moments : Moments F Δ c κ C height εm)
    (hU : 1<U) (ha : 1/2≤a) (hC : 0≤C) (hh : 0≤height)
    (hf : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (z : ℝ) (hz : 0≤z) (hz' : z≤7/37) (hcap1 : F.r+2*z<1) (hcap2 : 2*F.r+8*z<3) :
    (F.rows.card : ℝ)≤(12*(1+height)*C)*U^(1-(2*a-1)*F.r-2*F.q*z+2*ε+(2*a-1)*F.mesh+εm) := by
  exact inverse_fiber_count M H F.rows F.nonempty F.family U a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    F.slots (fun u => u.val) F.profile F.upper F.widths F.bin F.external F.mesh F.binWidth z εm C height
    F.mesh_nonneg F.binWidth_pos F.widths_pos F.widths_mesh (by linarith [F.supply])
    hz (hz'.trans F.supply) F.fixed_bin hC hh hf hcap1 hcap2 moments.inverse_marked

theorem Fiber.plain_marked_count (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {Δ c κ C height εm : ℝ} (moments : Moments F Δ c κ C height εm)
    (hU : 1<U) (ha : 1/2≤a) (hΔ : 0≤Δ) (hC : 0≤C) (hh : 0≤height)
    (hf : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (z : ℝ) (hz : 0≤z) (hz' : z≤7/37) (hcap : 2*F.m+6*(3/4+2*Δ)*z≤1) :
    (F.rows.card : ℝ)≤(192*(1+height)*C)*U^(1-2*(2*a-1)*F.m-2*F.q*z+4*ε+(2*a-1)*F.mesh+εm) := by
  exact plain_fiber_count M H F.rows F.nonempty F.family U a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    F.slots (fun u => u.val) F.profile F.upper F.widths F.bin F.external F.mesh F.binWidth z (3/4+2*Δ) εm C height
    F.mesh_nonneg F.binWidth_pos F.widths_pos F.widths_mesh (by linarith [F.supply])
    hz (hz'.trans F.supply) F.fixed_bin (by linarith) hC hh hf hcap moments.plain_marked

theorem Fiber.plain_unmarked_count (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {Δ c κ C height εm : ℝ} (moments : Moments F Δ c κ C height εm)
    (hU : 1<U) (ha : 0≤a) (hC : 0≤C) (hh : 0≤height)
    (hf : 2*Real.pi*allowance+(3*i : ℕ)*T≤height) :
    (F.rows.card : ℝ)≤(192*(1+height)*C)*U^(max 1 (2*F.m)-2*(2*a-1)*F.m+4*ε+εm) := by
  exact no_slot_plain_count F.rows F.family U a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    εm C height hC hh hf moments.plain_unmarked

def fiberConstant (C height K : ℝ) : ℝ := (192*(1+height)*C)*max 1 K

theorem fiberConstant_bounds (C height K : ℝ) (hC : 0≤C) (hh : 0≤height) (hK : 0≤K) :
    0≤fiberConstant C height K ∧ 192*(1+height)*C≤fiberConstant C height K ∧
      12*(1+height)*C≤fiberConstant C height K ∧
      12*(1+height)*(C*K)≤fiberConstant C height K := by
  have h1 : 0≤192*(1+height)*C := by positivity
  have h2 : 12*(1+height)*C≤192*(1+height)*C := by nlinarith
  have hbig : 192*(1+height)*C≤fiberConstant C height K :=
    le_mul_of_one_le_right h1 (le_max_left _ _)
  refine ⟨h1.trans hbig,hbig,h2.trans hbig,?_⟩
  calc
    _ = (12*(1+height)*C)*K := by ring
    _ ≤ (192*(1+height)*C)*max 1 K := mul_le_mul h2 (le_max_right _ _) hK h1

end SevenEighths.HeckeDetectorRawFiber

end

end OAI
end OAIOriginalModule2116

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorCountFromMoments
Source SHA256: 5d29e2f64e2e52ac5beb54a873684c5ea7fb32511280e8d53fd4b378ac014149
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2117


namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeDetectorCountFromMoments
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBranchBudget
open HeckeDetectorRowCount

theorem count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε tstar T allowance Δ ν C height : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤5/6 → 0≤ε → ε≤1/1000 →
      1≤tstar → tstar≤3/2 → 0≤Δ → Δ≤1/8 → 0<ν → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type*} (F : Fiber M H Label Slot U a ε tstar T allowance i),
      Moments F Δ c κ C height εm →
      (F.rows.card : ℝ)≤fiberConstant C height K₀*
        U^(max (shortExponent (2*a-1) (F.q/(2*a-1)) tstar) (longExponent (2*a-1) tstar)+
          Δ/4+159*ε+εm+F.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hamp⟩ := HeckeDetectorNoSlotInverseCount.no_slot_inverse_count
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB 2 εm (by norm_num) hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hamp] with U hamp
  intro a ε tstar T allowance Δ ν C height i hU ha hδcap hε hεsmall ht ht' hΔ hΔ' hν hC hh hf
    Label Slot F moments
  let δ := 2*a-1
  let x := F.q/δ
  have hδ : 0<δ := by dsimp [δ]; linarith
  have ha' : 1/2≤a := by linarith
  have hδ1 : δ≤1 := by dsimp [δ]; linarith
  obtain ⟨hq0,hqδ⟩ := F.mean_bounds ha'
  have hx : 0≤x := div_nonneg hq0 hδ.le
  have hx' : x≤1/2 := (div_le_iff₀ hδ).mpr (by dsimp [δ]; linarith)
  have hqx : δ*x=F.q := by dsimp [x]; field_simp
  have hgeom := F.lengths hU
  have hr0 : 0≤F.r := by linarith [hgeom.2.2.2.1]
  have hr2 : F.r≤2 := by linarith [hgeom.2.1]
  have hUp : 0<U := zero_lt_one.trans hU
  obtain ⟨hconst,hconstP,hconstI,hconstI0⟩ := fiberConstant_bounds C height K₀ hC hh hK
  have promote (C' p q : ℝ) (hC' : C'≤fiberConstant C height K₀)
      (hb : (F.rows.card : ℝ)≤C'*U^p) (hpq : p≤q) :
      (F.rows.card : ℝ)≤fiberConstant C height K₀*U^q := by
    exact hb.trans ((mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg hUp.le _)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hpq) hconst))
  have hi0 := hamp F.rows F.family a ε tstar T allowance i hU ha'
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    hr0 hr2 F.rowData F.reverse C height hC hh hf F.row_norm F.row_coeff moments.inverse_raw
  have hI0 : (F.rows.card : ℝ)≤fiberConstant C height K₀*
      U^(max 1 ((1+5*F.r)/6)-δ*F.r+commonLoss ε εm F.mesh ν) := by
    apply promote _ _ _ hconstI0 hi0
    exact no_slot_inverse_loss F.r δ ε εm F.mesh ν hε F.mesh_nonneg hν.le
  have hp0 := F.plain_unmarked_count moments hU (by linarith) hC hh hf
  have hP0 : (F.rows.card : ℝ)≤fiberConstant C height K₀*
      U^(1-2*δ*F.m+commonLoss ε εm F.mesh ν) := by
    apply promote _ _ _ hconstP hp0
    exact no_slot_plain_loss F.m δ ε εm F.mesh ν hε hgeom.2.2.1 F.mesh_nonneg hν.le
  have hI : 23/37≤F.r → F.r<1 → ν<(1-F.r)/2 →
      (F.rows.card : ℝ)≤fiberConstant C height K₀*
        U^(inverseExponent δ x F.r+commonLoss ε εm F.mesh ν) := by
    intro hr hr1 hv
    obtain ⟨hz,hz',hcap1,hcap2⟩ := inverse_requested_capacity F.r ν hr hr1 hν hv
    have hb := F.inverse_marked_count moments hU ha' hC hh hf ((1-F.r)/2-ν) hz hz' hcap1 hcap2
    apply promote _ _ _ hconstI hb
    have hl := inverse_marked_loss F.r δ x ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
    rwa [hqx] at hl
  have hP : F.r≤crossing x tstar → F.m<1/2 → ν<(1-2*F.m)/(9/2+12*Δ) →
      (F.rows.card : ℝ)≤fiberConstant C height K₀*
        U^(1-2*δ*F.m-2*(δ*x)*(1-2*F.m)/(9/2+12*Δ)+commonLoss ε εm F.mesh ν) := by
    intro hr hm hv
    obtain ⟨hz,hz',hcap⟩ := plain_requested_capacity Δ x tstar F.r F.m ε ν hΔ hx hx' ht ht'
      hr hgeom.1 (by linarith) hν.le hv
    have hb := F.plain_marked_count moments hU ha' hΔ hC hh hf
      ((1-2*F.m)/(9/2+12*Δ)-ν) hz hz' hcap
    apply promote _ _ _ hconstP hb
    have hl := plain_marked_loss F.m δ x Δ ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
    simpa only [hqx] using hl
  have hc' := count_bound_of_source_branches (F.rows.card : ℝ) (fiberConstant C height K₀) U δ x Δ
    tstar F.r F.m (commonLoss ε εm F.mesh ν) ν ε hconst hU.le hδ.le hδcap hx hx' hΔ hΔ'
    ht ht' hν.le hε hgeom.1 hgeom.2.1 hI0 hP0 hI hP
  convert hc' using 1; congr 2
  unfold commonLoss
  ring

end SevenEighths.HeckeDetectorCountFromMoments

end

end OAI
end OAIOriginalModule2117

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorBatchCount
Source SHA256: b910426b7dfc442a1e5af94ec153debe617d8c7592d59e4f4b61e1142832b71d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2118



namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeDetectorBatchCount
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows HeckeDetectorRowCount

theorem batch_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε tstar T allowance Δ ν C height : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤5/6 → 0≤ε → ε≤1/1000 →
      1≤tstar → tstar≤3/2 → 0≤Δ → Δ≤1/8 → 0<ν → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε tstar T allowance i),
      (∀ bin j J K,∀ hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card : ℝ)≤(Fintype.card Label : ℝ)*(dyadicLength U : ℝ)^2* fiberConstant C height K₀*
        ∑ bin : B.Bin,U^(max (shortExponent (2*a-1) (B.q bin/(2*a-1)) tstar)
          (longExponent (2*a-1) tstar)+Δ/4+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ := HeckeDetectorCountFromMoments.count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε tstar T allowance Δ ν C height i hU ha hδcap hε hεsmall ht ht' hΔ hΔ' hν hC hh hf
    Label Slot _ B moments
  apply B.card_bound (fiberConstant C height K₀) _
    (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU)
  intro bin j J K hne
  exact hcount a ε tstar T allowance Δ ν C height i hU ha hδcap hε hεsmall ht ht' hΔ hΔ' hν hC hh hf
    (B.fiber bin j J K hne) (moments bin j J K hne)

end SevenEighths.HeckeDetectorBatchCount

end

end OAI
end OAIOriginalModule2118

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorFixedAmplitudeCount
Source SHA256: baabf13565f77b3ae8bde6808c3ccab92d91499c967c05e474d00fb02768a447
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2119





namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeDetectorFixedAmplitudeCount
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorRowCount

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

lemma fiber_mean_eq (B : Batch M H Label Slot U a ε tstar T allowance i) (q : ℝ)
    (hq : ∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
      (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q)
    (bin : B.Bin) (j : Label) (J K : Fin (dyadicLength U))
    (hne : (B.fiberRows bin j J K).Nonempty) : (B.fiber bin j J K hne).q=q := by
  let u := hne.choose
  have hu : u ∈ B.fiberRows bin j J K := hne.choose_spec
  have huR : u∈B.rows := (Finset.mem_filter.mp hu).1
  rw [←hq u huR]
  unfold Fiber.q rowMean weightedMean
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  exact congrArg (fun g=>B.widths s*g) ((B.fiber bin j J K hne).fixed_bin u hu s hs).symm

lemma batch_mean_bounds (B : Batch M H Label Slot U a ε tstar T allowance i)
    (hne : B.rows.Nonempty) (ha : 1/2≤a) (q : ℝ)
    (hq : ∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
      (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) :
    0≤q ∧ q≤(2*a-1)/2 := by
  obtain ⟨u,hu⟩ := hne
  rw [←hq u hu]
  apply weightedMean_bounds B.slots B.widths _ (2*a-1)
    (fun s hs=>(B.widths_pos s hs).le) (by linarith [B.supply])
  intro s hs
  exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by linarith)

theorem fixed_amplitude_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀(a ε tstar T allowance Δ ν C height q : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤5/6 → 0≤ε → ε≤1/1000 →
      1≤tstar → tstar≤3/2 → 0≤Δ → Δ≤1/8 → 0<ν → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      ∀{Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε tstar T allowance i),
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2* fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(max (shortExponent (2*a-1) (q/(2*a-1)) tstar) (longExponent (2*a-1) tstar)+
          Δ/4+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ := HeckeDetectorCountFromMoments.count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε tstar T allowance Δ ν C height q i hU ha hd hε hε' ht ht' hΔ hΔ' hν hC hh hf Label Slot _ B hq moments
  have hb := B.card_bound (fiberConstant C height K₀)
    (fun _=>max (shortExponent (2*a-1) (q/(2*a-1)) tstar) (longExponent (2*a-1) tstar)+
      Δ/4+159*ε+εm+B.mesh+7*ν)
    (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
      intro bin j J K hne
      have hc' := hcount a ε tstar T allowance Δ ν C height i hU ha hd hε hε' ht ht' hΔ hΔ' hν hC hh hf
        (B.fiber bin j J K hne) (moments bin j J K hne)
      rw [fiber_mean_eq B q hq bin j J K hne] at hc'
      exact hc')
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hb
end SevenEighths.HeckeDetectorFixedAmplitudeCount

end

end OAI
end OAIOriginalModule2119

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorHighCount
Source SHA256: 38232c049a7d7440e58f4900c79e971e42a64ba46dcf3a6f35bbfade355f98b6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2120



namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeDetectorHighCount
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorRowCount

theorem high_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ C height : ℝ) (i : ℕ),
      1<U → 5/6≤2*a-1 → a≤1 → 0≤ε → ε≤1/1000 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type*} (F : Fiber M H Label Slot U a ε (3/2) T allowance i),
      Moments F Δ c κ C height εm →
      (F.rows.card : ℝ)≤fiberConstant C height K₀*U^(1-(2*a-1)+78*ε+εm) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hamp⟩ := HeckeDetectorNoSlotInverseCount.no_slot_inverse_count
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB 2 εm (by norm_num) hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hamp] with U hamp
  intro a ε T allowance Δ C height i hU ha ha' hε hεsmall hC hh hf Label Slot F moments
  have hgeom := F.lengths hU
  have hr0 : 0≤F.r := by linarith [hgeom.2.2.2.1]
  have hr2 : F.r≤2 := by linarith [hgeom.2.1]
  obtain ⟨hconst,_,_,hconstI⟩ := fiberConstant_bounds C height K₀ hC hh hK
  have hi := hamp F.rows F.family a ε (3/2) T allowance i hU (by linarith)
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    hr0 hr2 F.rowData F.reverse C height hC hh hf F.row_norm F.row_coeff moments.inverse_raw
  have hb : (F.rows.card : ℝ)≤fiberConstant C height K₀*
      U^(max 1 ((1+5*F.r)/6)-(2*a-1)*F.r+(2*ε+εm)) := by
    apply hi.trans
    convert mul_le_mul_of_nonneg_right hconstI
      (Real.rpow_nonneg (zero_lt_one.trans hU).le
        (max 1 ((1+5*F.r)/6)-(2*a-1)*F.r+2*ε+εm)) using 1 <;> congr 2; ring
  have hout := high_bin_count hconst hU.le ha (show 2*a-1≤1 by linarith)
    (show 0≤76*ε by positivity) (show 1-76*ε≤F.r by linarith [hgeom.2.2.2.1]) hb
  convert hout using 1; congr 2; ring

end SevenEighths.HeckeDetectorHighCount

end

end OAI
end OAIOriginalModule2120

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorHighBatchCount
Source SHA256: e89b70a440ff42d51af62ab0b5ecee37c2009fa4acf59a828adca8b5d762733b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2121




namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeDetectorHighBatchCount
open HeckeDetectorBatch
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorRowCount

theorem high_batch_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ C height : ℝ) (i : ℕ),
      1<U → 5/6≤2*a-1 → a≤1 → 0≤ε → ε≤1/1000 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε (3/2) T allowance i),
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card : ℝ)≤(Fintype.card Label:ℝ)*(HeckeDetectorWitnessRows.dyadicLength U:ℝ)^2*
        fiberConstant C height K₀*(Fintype.card B.Bin:ℝ)*U^(1-(2*a-1)+78*ε+εm) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ := HeckeDetectorHighCount.high_count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance Δ C height i hU ha ha' hε hε' hC hh hf Label Slot _ B moments
  have hb := B.card_bound (fiberConstant C height K₀) (fun _=>1-(2*a-1)+78*ε+εm)
    (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
      intro bin j J K hne
      exact hcount a ε T allowance Δ C height i hU ha ha' hε hε' hC hh hf
        (B.fiber bin j J K hne) (moments bin j J K hne))
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hb
end SevenEighths.HeckeDetectorHighBatchCount

end

end OAI
end OAIOriginalModule2121

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.SignalBounds
Source SHA256: a3afa01a42b1a3936fcba0eda033b4b5377cd64478620fdf61f80777e58c36ef
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2122



namespace OAI

noncomputable section
open scoped Topology
open MeasureTheory Set Filter Asymptotics
namespace SevenEighths.HeckeSignalBounds
open HeckeFamily HeckeSignal Continuation

theorem contour_shift_left (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8<s.re})
    (hb : ∀ s : ℂ, 7/8<s.re → ‖H s-1‖ ≤ 1/2)
    (c a : ℝ) (ha : (7/8 : ℝ)<a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta<a) {x : ℝ} (hx : 1≤x) :
    signal χ H c x = (1/(2*Real.pi) : ℂ)*
      ∫ y : ℝ, gaussianContourIntegrand (quotient χ H) c x ((a : ℂ)+y*Complex.I) := by
  obtain ⟨C,hC,hbound⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  exact HeckeSignalShift.contour_shift_left χ H hH hb c a C 2 ha ha2 hβ hC
    (fun s hs _ => hbound s hs) hx

theorem signal_isBigO_atTop (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8<s.re})
    (hb : ∀ s : ℂ, 7/8<s.re → ‖H s-1‖ ≤ 1/2)
    (c a : ℝ) (ha : (7/8 : ℝ)<a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta<a) :
    signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)) := by
  obtain ⟨C,hC,hbound⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  exact HeckeSignalShift.signal_isBigO_atTop χ H hH hb c a C 2 ha ha2 hβ hC
    (fun s hs _ => hbound s hs)

end SevenEighths.HeckeSignalBounds

end

end OAI
end OAIOriginalModule2122

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialRawDictionary
Source SHA256: 105bd240eb1ab8d0afaeb953710d51124ab6fffa8e56027970aaee372169dc77
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2123




namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialRawDictionary
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge HeckeRowClosure
open InverseInitialPoissonBridge InverseInitialConjugateEnergy
open ConcretePrimeRowBridge CompletedGauss UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

def twistedProfile (W : ℝ → ℂ) (σ freq : ℝ) (x : ℝ) : ℂ :=
  W x*(x:ℂ)^(-shift σ freq)

theorem finite_source_cover (W : ℝ → ℂ) (D b : ℝ) (hD : 0<D)
    (hW : ∀x,W x≠0 → x≤b) (I : Ideal O) (hI : I≠0)
    (hi : W ((I.absNorm:ℝ)/D)≠0) : I∈idealsUpTo ⌈D*b⌉₊ := by
  apply mem_idealsUpTo.mpr
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI),?_⟩
  have hb := (div_le_iff₀ hD).mp (hW _ hi)
  have hn : (I.absNorm:ℝ)≤(⌈D*b⌉₊:ℝ) := by
    calc
      (I.absNorm:ℝ)≤D*b := by simpa only [mul_comm] using hb
      _≤(⌈D*b⌉₊:ℝ) := Nat.le_ceil _
  exact_mod_cast hn

theorem normalization_eq (Z r : ℝ) (hZ : 0<Z) :
    ((Z^r:ℝ):ℂ)^(-(1/2:ℂ))=((Z^(-r/2):ℝ):ℂ) := by
  have he : (-(1/2:ℂ))=((-(1/2:ℝ)):ℂ) := by norm_num
  calc
    _ = (((Z^r)^(-(1/2:ℝ)):ℝ):ℂ) := by
      simpa only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_one,
        Complex.ofReal_ofNat] using (Complex.ofReal_cpow
          (Real.rpow_nonneg hZ.le r) (-(1/2:ℝ))).symm
    _ = _ := ?_
  rw [←Real.rpow_mul hZ.le]
  congr 2
  ring

theorem inverse_eq_initial_source (η : Ideal O →* ℂ) (χ : Character) (u : O)
    (hrow : ∀I,idealCoeff χ I=η I*CanonicalRowCompletion.idealRowHom u I)
    (W : ℝ → ℂ) (Z r σ freq : ℝ) (hZ : 0<Z) (S : Finset (Ideal O))
    (hcover : ∀I:Ideal O,I≠0 → W ((I.absNorm:ℝ)/Z^r)≠0 → I∈S) :
    polynomial χ true W (Z^r) σ freq=
      originalTotalPolynomial S 1 η (fun _=>1)
        (twistedProfile W σ freq) Z r 0 u := by
  rw [polynomial_eq_finite χ true W (Z^r) σ freq S hcover,normalization_eq Z r hZ]
  unfold originalTotalPolynomial
  simp only [add_zero,map_one,mul_one]
  apply congrArg (fun x:ℂ=>((Z^(-r/2):ℝ):ℂ)*x)
  apply Finset.sum_congr rfl
  intro I hI
  simp only [coefficient,ite_true,hrow,heckeIdealCharacter_apply,
    twistedProfile]
  ring

theorem canonical_inverse_eq_initial_source (η χ : Character) (m f z : O)
    (hrow : ∀n:O,elementCoeff χ n=
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n)
    (W : ℝ → ℂ) (Z r σ freq b : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0 → x≤b) :
    polynomial χ true W (Z^r) σ freq=
      originalTotalPolynomial (idealsUpTo ⌈Z^r*b⌉₊) 1
        (idealCoeff η).toMonoidHom (fun _=>1)
        (twistedProfile W σ freq) Z r 0 (m^6*f^4*z) := by
  apply inverse_eq_initial_source (idealCoeff η).toMonoidHom χ (m^6*f^4*z)
    (HeckeRowClosure.idealCoeff_eq_row η χ m f z hrow) W Z r σ freq hZ
  exact finite_source_cover W (Z^r) b (Real.rpow_pos_of_pos hZ r) hW

theorem inverse_times_mark_eq_initial (η : Ideal O →* ℂ) (χ : Character) (u : O)
    (hrow : ∀I,idealCoeff χ I=η I*CanonicalRowCompletion.idealRowHom u I)
    (W : ℝ → ℂ) (Z r z σ freq : ℝ) (hZ : 0<Z)
    (S P : Finset (Ideal O)) (A : Ideal O → ℂ)
    (hcover : ∀I:Ideal O,I≠0 → W ((I.absNorm:ℝ)/Z^r)≠0 → I∈S) :
    polynomial χ true W (Z^r) σ freq*(Z^(-z/2):ℝ)*
      (∑p∈P,A p*idealCoeff χ p)=
      ∑p∈P,A p*originalTotalPolynomial S p η
        (fun _=>1) (twistedProfile W σ freq) Z r z u := by
  rw [inverse_eq_initial_source η χ u hrow W Z r σ freq hZ S hcover]
  have hn : ((Z^(-r/2):ℝ):ℂ)*((Z^(-z/2):ℝ):ℂ)=
      ((Z^(-(r+z)/2):ℝ):ℂ) := by
    rw [←Complex.ofReal_mul,←Real.rpow_add hZ]
    congr 2
    ring
  unfold originalTotalPolynomial
  simp only [add_zero,map_one,mul_one,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro I hI
  rw [hrow p]
  simp only [heckeIdealCharacter_apply]
  calc
    _ = (((Z^(-r/2):ℝ):ℂ)*((Z^(-z/2):ℝ):ℂ))*
      (A p*((moebius I:ℂ)*(η I*CanonicalRowCompletion.idealRowHom u I)*
      (η p*CanonicalRowCompletion.idealRowHom u p)*
      twistedProfile W σ freq ((I.absNorm:ℝ)/Z^r))) := by ring
    _ = _ := by rw [hn];ring

theorem originalTotal_supported_source (S : Finset (Ideal O)) (P : Ideal O)
    (η : Ideal O →* ℂ) (hη : ∀I,¬CanonicalQuadraticSieve.Supported I → η I=0)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z : ℝ) (u : O) :
    originalTotalPolynomial S P η a W Z r z u=
      originalTotalPolynomial (S.filter CanonicalQuadraticSieve.Supported) P η a W Z r z u := by
  unfold originalTotalPolynomial
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs with hi
  · rfl
  · simp only [heckeIdealCharacter_apply,hη I hi,zero_mul,mul_zero]

def fixedBase (η : Character) (m f : O) : Ideal O →* ℂ :=
  heckeIdealCharacter (idealCoeff η).toMonoidHom (m^6*f^4)

theorem fixedBase_row (η χ : Character) (m f z : O)
    (hrow : ∀n:O,elementCoeff χ n=
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n) (I : Ideal O) :
    idealCoeff χ I=fixedBase η m f I*CanonicalRowCompletion.idealRowHom z I := by
  rw [HeckeRowClosure.idealCoeff_eq_row η χ m f z hrow,
    CanonicalRowCompletion.idealRowHom_argument_mul]
  change idealCoeff η I*(CanonicalRowCompletion.idealRowHom (m^6*f^4) I*
    CanonicalRowCompletion.idealRowHom z I)=
    (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*f^4) I)*
    CanonicalRowCompletion.idealRowHom z I
  ring

theorem fixedBase_zero_unsupported (η : Character) (m f : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (I : Ideal O) (hI : ¬CanonicalQuadraticSieve.Supported I) : fixedBase η m f I=0 := by
  by_cases hi : I=0
  · subst I
    change idealCoeff η 0*_=0
    rw [map_zero,zero_mul]
  let n := ConcretePrimeRowBridge.idealGenerator I
  have hn : n≠0 := ConcretePrimeRowBridge.idealGenerator_ne_zero I hi
  have hs : Ideal.span {n}=I := ConcretePrimeRowBridge.span_idealGenerator I
  have he := CanonicalRowCompletion.rowTwist_zero_of_not_supported
    (elementHom η) m f 1 n hmLam hm2 (by rwa [hs])
  change elementCoeff η n*CanonicalRowCompletion.idealRowHom (m^6*f^4*1)
    (Ideal.span {n})=0 at he
  rw [mul_one,hs,←idealCoeff_span η hn,hs] at he
  exact he

theorem canonical_inverse_eq_supported_initial (η χ : Character) (m f z : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (hrow : ∀n:O,elementCoeff χ n=
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n)
    (W : ℝ → ℂ) (Z r σ freq b : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0 → x≤b) :
    polynomial χ true W (Z^r) σ freq=
      originalTotalPolynomial ((idealsUpTo ⌈Z^r*b⌉₊).filter CanonicalQuadraticSieve.Supported)
        1 (fixedBase η m f) (fun _=>1) (twistedProfile W σ freq) Z r 0 z := by
  rw [inverse_eq_initial_source (fixedBase η m f) χ z (fixedBase_row η χ m f z hrow)
    W Z r σ freq hZ (idealsUpTo ⌈Z^r*b⌉₊)
    (finite_source_cover W (Z^r) b (Real.rpow_pos_of_pos hZ r) hW)]
  exact originalTotal_supported_source _ _ _ (fixedBase_zero_unsupported η m f hmLam hm2)
    _ _ _ _ _ _

theorem inverse_times_conjugate_row_mark_norm (η : Ideal O →* ℂ) (χ : Character) (u : O)
    (hrow : ∀I,idealCoeff χ I=η I*CanonicalRowCompletion.idealRowHom u I)
    (W : ℝ → ℂ) (Z r z σ freq : ℝ) (hZ : 0<Z)
    (S P : Finset (Ideal O)) (A : Ideal O → ℂ)
    (hη : ∀p∈P,A p≠0 → η p≠0)
    (hcover : ∀I:Ideal O,I≠0 → W ((I.absNorm:ℝ)/Z^r)≠0 → I∈S) :
    ‖polynomial χ true W (Z^r) σ freq*(Z^(-z/2):ℝ)*
      (∑p∈P,A p*star (CanonicalRowCompletion.idealRowHom u p))‖=
    ‖∑p∈P,(star (A p)/η p)*originalTotalPolynomial S p η
      (fun _=>1) (twistedProfile W σ freq) Z r z u‖ := by
  have hm : (∑p∈P,(star (A p)/η p)*idealCoeff χ p)=
      star (∑p∈P,A p*star (CanonicalRowCompletion.idealRowHom u p)) := by
    simp only [star_sum,star_mul,star_star]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases ha : A p=0
    · simp [ha]
    · rw [hrow p]
      field_simp [hη p hp ha]
  rw [←inverse_times_mark_eq_initial η χ u hrow W Z r z σ freq hZ S P
    (fun p=>star (A p)/η p) hcover,hm]
  simp only [norm_mul,norm_star]

end SevenEighths.InverseInitialRawDictionary

end

end OAI
end OAIOriginalModule2123

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWindow
Source SHA256: ed0c37bc7fc0291b6711f61d964591a07ccf4dc147af53bf61b9bf732ca158b2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2124



namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open SevenEighths.InverseInitialOverlap SevenEighths.InverseInitialRayAttachment
open SevenEighths.InverseInitialPoissonBridge SevenEighths.InverseInitialKernelBridge SevenEighths.InverseInitialEnergyCallerPool
namespace SevenEighths.InverseInitialEnergyCallerWindow
local notation "Eis" => ActualEisensteinCubic.O

def originalSource (Z r b : ℝ) : Finset (Ideal Eis) :=
  (idealsUpTo ⌈Z^r*b⌉₊).filter Supported

theorem originalSource_supported (Z r b : ℝ) :
    ∀n∈originalSource Z r b,Squarefree n→Supported n := by
  intro n hn _
  exact (Finset.mem_filter.mp hn).2

theorem residual_window_eq (W : ℝ→ℂ) {P j c : Ideal Eis}
    (hP : Squarefree P) (hj : j∣P) (hc : residual P j∣c)
    (Z r z G : ℝ) (hZ : 0<Z) :
    residualOverlapWindow P j W Z z G ((c.absNorm:ℝ)/Z^(r+z-2*G)) =
      W (((reconstruct P j c).absNorm:ℝ)/Z^r) := by
  unfold residualOverlapWindow
  rw [←scaled_cutoff_argument hP hj hc hZ r z G]

theorem reconstructed_mem_originalSource
    (W : ℝ→ℂ) (Z r z G b : ℝ) (hZ : 0<Z) (hW : ∀x,W x≠0→x≤b)
    {P j c : Ideal Eis} (hP : Admissible P) (hj : j∣P)
    (hc : Admissible c) (hPc : residual P j∣c)
    (hlive : residualOverlapWindow P j W Z z G ((c.absNorm:ℝ)/Z^(r+z-2*G))≠0) :
    reconstruct P j c∈originalSource Z r b := by
  have hs : Supported (reconstruct P j c) :=
    (supported_mul_iff _ _).mpr
      ⟨admissible_supported (admissible_of_dvd hP hj),
        admissible_supported (admissible_of_dvd hc (idealQuotient_dvd hPc))⟩
  apply Finset.mem_filter.mpr
  refine ⟨InverseInitialRawDictionary.finite_source_cover W (Z^r) b
    (Real.rpow_pos_of_pos hZ r) hW _ hs.1 ?_,hs⟩
  rwa [residual_window_eq W hP.2.1 hj hPc Z r z G hZ] at hlive

theorem original_selector_window
    (W : ℝ→ℂ) (Z r z G b : ℝ) (hZ : 0<Z) (hW : ∀x,W x≠0→x≤b)
    {P j : Ideal Eis} (hP : Admissible P) (hj : j∣P)
    (hne : (columns (originalSource Z r b) P j).Nonempty)
    (a : Ideal Eis→ℂ) (A : Finset (primePool (columns (originalSource Z r b) P j))) :
    reconstructedSelector (originalSource Z r b) P j a A *
      rowCoprimeMask (fun i : primePool (columns (originalSource Z r b) P j)=>i.val)
        A (primaryGenerator j) *
      residualOverlapWindow P j W Z z G (((∏ i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) =
    a (reconstruct P j (∏ i∈A,i.val)) *
      InverseMoment.primeMark (forcedSlots (originalSource Z r b) P j) (fun i=>{i})
        (fun _ _=>(1:ℂ)) A *
      rowCoprimeMask (fun i : primePool (columns (originalSource Z r b) P j)=>i.val)
        A (primaryGenerator j) *
      residualOverlapWindow P j W Z z G (((∏ i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) := by
  have hF : ∀I∈columns (originalSource Z r b) P j,Admissible I :=
    fun I hI=>columns_admissible _ hP hj (originalSource_supported Z r b) hI
  have hA := InitialMeanSquare.poolProduct_admissible _ hF A
  apply original_selector_forced_slots _ hP hj hne a
    (fun c=>residualOverlapWindow P j W Z z G ((c.absNorm:ℝ)/Z^(r+z-2*G))) A hA.2.1
  intro hPc hlive _
  exact reconstructed_mem_originalSource W Z r z G b hZ hW hP hj hA hPc hlive

end SevenEighths.InverseInitialEnergyCallerWindow

end

end OAI
end OAIOriginalModule2124

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialCommonPool
Source SHA256: d1edcc7cb9a714550eb981c31409cf92347c346f2e213e3a9d6b7cee33f045b7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2125


namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open UniqueFactorizationMonoid SecondPassArithmetic
namespace SevenEighths.InverseInitialCommonPool
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialRayAttachment
local notation "Eis"=>ActualEisensteinCubic.O

def commonColumns (S Ps : Finset (Ideal Eis)) (j : Ideal Eis) : Finset (Ideal Eis) :=
  Ps.biUnion (fun P=>columns S P j)

theorem columns_subset (S Ps : Finset (Ideal Eis)) (j : Ideal Eis)
    {P : Ideal Eis} (hP : P∈Ps) : columns S P j⊆commonColumns S Ps j := by
  intro c hc
  exact Finset.mem_biUnion.mpr ⟨P,hP,hc⟩

theorem common_admissible (S Ps : Finset (Ideal Eis)) (j : Ideal Eis)
    (hPs : ∀P∈Ps,Admissible P) (hj : ∀P∈Ps,j∣P)
    (hS : ∀n∈S,Squarefree n→Supported n) :
    ∀c∈commonColumns S Ps j,Admissible c := by
  intro c hc
  obtain ⟨P,hP,hc⟩ := Finset.mem_biUnion.mp hc
  exact columns_admissible S (hPs P hP) (hj P hP) hS hc

theorem common_coprime (S Ps : Finset (Ideal Eis)) (j : Ideal Eis)
    (hPs : ∀P∈Ps,Admissible P) (hj : ∀P∈Ps,j∣P) :
    ∀c∈commonColumns S Ps j,IsCoprime c j := by
  intro c hc
  obtain ⟨P,hP,hc⟩ := Finset.mem_biUnion.mp hc
  exact ((mem_columns (hPs P hP).2.1 (hj P hP)).mp hc).2.1

theorem residual_eq_common_input
    (S F : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Admissible P) (hj : j∣P) (hF : ∀I∈F,Admissible I)
    (hcop : ∀I∈F,IsCoprime I j) (hsub : columns S P j⊆F)
    (η : Ideal Eis→*ℂ) (a : Ideal Eis→ℂ) (W : ℝ→ℂ)
    (Z r z G : ℝ) (u : Eis) :
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    residualNormalizedPolynomial S P j η a W Z r z G u =
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>if (∏i∈A,i.val)∈columns S P j then
          a (reconstruct P j (∏i∈A,i.val))*residualOverlapWindow P j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0) u := by
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  let H : Ideal Eis→ℂ := fun c=>if c∈columns S P j then
    a (reconstruct P j c)*residualOverlapWindow P j W Z z G
      ((c.absNorm:ℝ)/Z^(r+z-2*G)) else 0
  have hfilter : F.filter (fun c=>c∈columns S P j)=columns S P j := by
    ext c
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun h=>hsub h)
  have he : (∑c∈columns S P j,
      overlapResidualCoefficient P j η a W Z r z G c*star (CanonicalRowCompletion.idealRowHom u c))=
      ∑c∈F,(moebius c:ℂ)*η c*H c*star (CanonicalRowCompletion.idealRowHom u c) := by
    conv_rhs => arg 2;ext c;dsimp only [H];simp only [mul_ite,mul_zero,ite_mul,zero_mul]
    rw [←Finset.sum_filter,hfilter]
    apply Finset.sum_congr rfl
    intro c hc
    rw [overlapCoefficient_residual]
    unfold bareOverlapCoefficient
    ring
  unfold residualNormalizedPolynomial
  rw [he,selected_conjugate_row F hF j (admissible_of_dvd hP hj) hcop η H u]
  apply congrArg (fun v:ℂ=>((Z^(-(r+z-2*G)/2):ℝ):ℂ)*v)
  congr 1
  funext A
  dsimp [H]
  by_cases hc : (∏i∈A,i.val)∈columns S P j
  · simp only [hc,hsub hc,ite_true]
  · simp only [hc,ite_false,ite_self]

end SevenEighths.InverseInitialCommonPool

end

end OAI
end OAIOriginalModule2125

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialCommonForcing
Source SHA256: 3e21dcfc7cd49ab09905f7408fcda6a8ecfe0fffdcc1f6da82d74dec6909a007
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2126


namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open FirstCauchyArithmetic SecondPassArithmetic
namespace SevenEighths.InverseInitialCommonForcing
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialRayAttachment InverseInitialArithmetic InverseInitialCommonPool
open InverseInitialEnergyCallerWindow InverseInitialEnergyCallerSelector
local notation "Eis"=>ActualEisensteinCubic.O

theorem common_selector_window
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    {P j:Ideal Eis}(hP:Admissible P)(hj:j∣P)
    (F:Finset (Ideal Eis))(hF:∀I∈F,Admissible I)(A:Finset (primePool F)) :
    (if (∏i∈A,i.val)∈columns (originalSource Z r b) P j then
      residualOverlapWindow P j W Z z G (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)*
      rowCoprimeMask (fun i:primePool F=>i.val) A (primaryGenerator j) =
    (if residual P j∣(∏i∈A,i.val) then
      residualOverlapWindow P j W Z z G (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)*
      rowCoprimeMask (fun i:primePool F=>i.val) A (primaryGenerator j) := by
  by_cases hm : rowCoprimeMask (fun i:primePool F=>i.val) A (primaryGenerator j)=0
  · simp only [hm,mul_zero]
  by_cases hw : residualOverlapWindow P j W Z z G (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G))=0
  · simp only [hw,ite_self,zero_mul]
  have hA := InitialMeanSquare.poolProduct_admissible F hF A
  have hcop := mask_nonzero_coprime F j (admissible_of_dvd hP hj) A hm
  by_cases hd : residual P j∣(∏i∈A,i.val)
  · have hmem := (mem_columns hP.2.1 hj).mpr ⟨hA.2.1,hcop,hd,
      reconstructed_mem_originalSource W Z r z G b hZ hW hP hj hA hd hw⟩
    simp only [hd,hmem,ite_true]
  · have hn : (∏i∈A,i.val)∉columns (originalSource Z r b) P j :=
      fun h=>hd ((mem_columns hP.2.1 hj).mp h).2.2.1
    simp only [hd,hn,ite_false]

theorem residual_eq_common_forcing
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    {P j:Ideal Eis}(hP:Admissible P)(hj:j∣P)
    (F:Finset (Ideal Eis))(hF:∀I∈F,Admissible I)
    (hcop:∀I∈F,IsCoprime I j)(hsub:columns (originalSource Z r b) P j⊆F)
    (η:Ideal Eis→*ℂ)(u:Eis) :
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    residualNormalizedPolynomial (originalSource Z r b) P j η (fun _=>1) W Z r z G u =
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>if residual P j∣(∏i∈A,i.val) then
          residualOverlapWindow P j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0) u := by
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  rw [residual_eq_common_input _ F hP hj hF hcop hsub η (fun _=>1) W Z r z G u]
  simp only [one_mul]
  apply congrArg (fun v:ℂ=>((Z^(-(r+z-2*G)/2):ℝ):ℂ)*v)
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF),
    initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  have he := common_selector_window W Z r z G b hZ hW hP hj F hF A
  have hm : rowCoprimeMask (fun i:primePool F=>Ideal.span {poolPrimary F i}) A
      (primaryGenerator j)=rowCoprimeMask (fun i:primePool F=>i.val) A
        (primaryGenerator j) := by
    congr 1
    funext i
    exact poolPrimary_span F hF i
  dsimp only
  rw [hm]
  linear_combination
    (supportMobius (fun i:primePool F=>Ideal.span {poolPrimary F i}) A *
      elementCharacter η (∏i∈A,poolPrimary F i) *
      star (finiteSquarefreeRow (fun i:primePool F=>Ideal.span {poolPrimary F i})
        (poolPrimary_good F hF) A u))*he

end SevenEighths.InverseInitialCommonForcing

end

end OAI
end OAIOriginalModule2126

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialCommonTuples
Source SHA256: 950973775b4275c48e43104b0d6255b8ca5ee4387d9297daf4396ede7838922b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2127


namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open FirstCauchyArithmetic SecondPassArithmetic
namespace SevenEighths.InverseInitialCommonTuples
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialRayAttachment InverseInitialArithmetic InverseInitialCommonPool
open InverseInitialEnergyCallerWindow InverseInitialCommonForcing
local notation "Eis"=>ActualEisensteinCubic.O
variable {κ ι : Type*} [DecidableEq ι]

theorem input_finset_sum (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,goodLambda∉Ideal.span {p i})(F:Finset ι)(Ψ:Eis→*ℂ)(j u:Eis)
    (T:Finset κ)(a:κ→ℂ)(H:κ→Finset ι→ℂ) :
    inputConjugateRow p hg F Ψ j 1 1 (fun A=>∑k∈T,a k*H k A) u=
      ∑k∈T,a k*inputConjugateRow p hg F Ψ j 1 1 (H k) u := by
  simp_rw [initial_input_row p hg]
  unfold supportConjugateSum
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro A hA
  ring

def tupleColumns (S:Finset (Ideal Eis))(T:Finset κ)(P:κ→Ideal Eis)(j:Ideal Eis) :
    Finset (Ideal Eis) := T.biUnion (fun k=>columns S (P k) j)

theorem tupleColumns_admissible (S:Finset (Ideal Eis))(T:Finset κ)(P:κ→Ideal Eis)
    (j:Ideal Eis)(hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (hS:∀n∈S,Squarefree n→Supported n) :
    ∀c∈tupleColumns S T P j,Admissible c := by
  intro c hc
  obtain ⟨k,hk,hc⟩ := Finset.mem_biUnion.mp hc
  exact columns_admissible S (hP k hk) (hj k hk) hS hc

theorem tupleColumns_coprime (S:Finset (Ideal Eis))(T:Finset κ)(P:κ→Ideal Eis)
    (j:Ideal Eis)(hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k) :
    ∀c∈tupleColumns S T P j,IsCoprime c j := by
  intro c hc
  obtain ⟨k,hk,hc⟩ := Finset.mem_biUnion.mp hc
  exact ((mem_columns (hP k hk).2.1 (hj k hk)).mp hc).2.1

theorem original_tuples_common_input
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    (T:Finset κ)(P:κ→Ideal Eis)(j:Ideal Eis)
    (hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (η:Ideal Eis→*ℂ)(a:κ→ℂ)(u:Eis) :
    let S := originalSource Z r b
    let F := tupleColumns S T P j
    let hF := tupleColumns_admissible S T P j hP hj (originalSource_supported Z r b)
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    (∑k∈T,a k*residualNormalizedPolynomial S (P k) j η (fun _=>1) W Z r z G u)=
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>∑k∈T,a k*(if residual (P k) j∣(∏i∈A,i.val) then
          residualOverlapWindow (P k) j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) u := by
  intro S F hF
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  erw [input_finset_sum (p := poolPrimary F)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [residual_eq_common_forcing W Z r z G b hZ hW (hP k hk) (hj k hk) F hF
    (tupleColumns_coprime S T P j hP hj)
    (fun c hc=>Finset.mem_biUnion.mpr ⟨k,hk,hc⟩) η u]
  ring

end SevenEighths.InverseInitialCommonTuples

end

end OAI
end OAIOriginalModule2127

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialCommonLists
Source SHA256: d975c83f2abc645e180c762d56fe4d7e0459668ff15fd7cba39c4038db8785ab
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2128



namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
namespace SevenEighths.InverseInitialCommonLists
open InverseMoment
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

def poolList (F:Finset (Ideal Eis))(L:Finset (Ideal Eis)) : Finset (primePool F) :=
  Finset.univ.filter (fun i=>i.val∈L)

theorem outside_pool_not_dvd (F:Finset (Ideal Eis))(A:Finset (primePool F))
    {P:Ideal Eis}(hP:Prime P)(hn:P∉primePool F) : ¬P∣∏i∈A,i.val := by
  intro hd
  obtain ⟨i,hi,hd⟩ := hP.dvd_finsetProd_iff (fun i:primePool F=>i.val) |>.mp hd
  have hip : Prime i.val := Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
  have he := (prime_dvd_prime_iff_eq hP hip).mp hd
  exact hn (he ▸ i.property)

theorem dividing_list_image (F:Finset (Ideal Eis))(L:Finset (Ideal Eis))
    (hL:∀P∈L,Prime P)(A:Finset (primePool F)) :
    ((poolList F L).filter (fun i=>i∈A)).image Subtype.val=
      L.filter (fun P=>P∣∏i∈A,i.val) := by
  ext P
  constructor
  · intro h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hiL,hiA⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hiL).2,Finset.dvd_prod_of_mem _ hiA⟩
  · intro h
    obtain ⟨hPL,hd⟩ := Finset.mem_filter.mp h
    obtain ⟨i,hi,hd⟩ := (hL P hPL).dvd_finsetProd_iff (fun i:primePool F=>i.val) |>.mp hd
    have hip : Prime i.val := Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
    have he := (prime_dvd_prime_iff_eq (hL P hPL) hip).mp hd
    refine Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨?_,hi⟩,he.symm⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he ▸ hPL⟩

theorem original_ideal_slot (F:Finset (Ideal Eis))(L:Finset (Ideal Eis))
    (hL:∀P∈L,Prime P)(a:Ideal Eis→ℂ)(A:Finset (primePool F)) :
    (∑P∈L,if P∣∏i∈A,i.val then a P else 0)=
      primeSlot (poolList F L) (fun i=>a i.val) A := by
  rw [←Finset.sum_filter,←dividing_list_image F L hL A,
    Finset.sum_image (fun i _ j _ h=>Subtype.val_injective h)]
  simp only [primeSlot,←Finset.sum_filter]

theorem original_ideal_mark (F:Finset (Ideal Eis))(I:Finset σ)
    (L:σ→Finset (Ideal Eis))(hL:∀i∈I,∀P∈L i,Prime P)
    (a:σ→Ideal Eis→ℂ)(A:Finset (primePool F)) :
    indexedIdealMark id I L a (∏i∈A,i.val)=
      primeMark I (fun i=>poolList F (L i)) (fun i q=>a i q.val) A := by
  unfold indexedIdealMark primeMark
  apply Finset.prod_congr rfl
  intro i hi
  exact original_ideal_slot F (L i) (hL i hi) (a i) A

end SevenEighths.InverseInitialCommonLists

end

end OAI
end OAIOriginalModule2128

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialCommonRatios
Source SHA256: 0e4700f64d1a624962d46f1d1d75aea7e1b459357894d892baee522b1458e67a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2129


namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve
namespace SevenEighths.InverseInitialCommonRatios
open InverseInitialOverlap InverseInitialKernelBridge
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

def survivingProduct (I:Finset σ)(q:∀i∈I,Ideal Eis) : Ideal Eis :=
  ∏i∈I.attach,q i.val i.property

omit [DecidableEq σ] in
theorem actual_residual_product (I:Finset σ)(q:∀i∈I,Ideal Eis)
    (j:Ideal Eis)(hj:j≠0) : residual (j*survivingProduct I q) j=survivingProduct I q :=
  quotient_mul_cancel hj

omit [DecidableEq σ] in
theorem residual_ratio_product (I:Finset σ)(q:∀i∈I,Ideal Eis)
    (j:Ideal Eis)(hj:j≠0)(ell:σ→ℝ)(Z z G:ℝ)(hZ:0<Z)
    (hell:∑i∈I,ell i=z-G) :
    ((residual (j*survivingProduct I q) j).absNorm:ℝ)/Z^(z-G)=
      ∏i∈I.attach,((q i.val i.property).absNorm:ℝ)/Z^(ell i.val) := by
  rw [actual_residual_product I q j hj,Finset.prod_div_distrib]
  have hp : (∏i∈I.attach,Z^(ell i.val))=Z^(z-G) := by
    rw [←Real.rpow_sum_of_pos hZ]
    rw [Finset.sum_attach,hell]
  rw [hp]
  congr 1
  simp only [survivingProduct,map_prod,Nat.cast_prod]

omit [DecidableEq σ] in
theorem original_residual_window (I:Finset σ)(q:∀i∈I,Ideal Eis)
    (j:Ideal Eis)(hj:j≠0)(ell:σ→ℝ)(W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0<Z)
    (hell:∑i∈I,ell i=z-G)(c:Ideal Eis) :
    residualOverlapWindow (j*survivingProduct I q) j W Z z G
      ((c.absNorm:ℝ)/Z^(r+z-2*G))=
      W (((j.absNorm:ℝ)/Z^G)*((c.absNorm:ℝ)/Z^(r+z-2*G))/
        (∏i∈I.attach,((q i.val i.property).absNorm:ℝ)/Z^(ell i.val))) := by
  unfold residualOverlapWindow
  rw [residual_ratio_product I q j hj ell Z z G hZ hell]

end SevenEighths.InverseInitialCommonRatios

end

end OAI
end OAIOriginalModule2129

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialCommonProfile
Source SHA256: d9626f5f93a189486b91487db6f5a7e25902d78f76f6f6e358f75c1cbcc0c4f5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2130




namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
namespace SevenEighths.InverseInitialCommonProfile
open InverseMoment InverseInitialCommonLists InverseInitialCommonRatios
open InverseInitialOverlapFourier InverseInitialOverlapIdealFourier
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

def slotRatio (Z:ℝ)(ell:σ→ℝ)(i:σ)(P:Ideal Eis) : ℝ := (P.absNorm:ℝ)/Z^(ell i)

omit [DecidableEq σ] in
theorem slotRatio_pos (Z:ℝ)(hZ:0<Z)(ell:σ→ℝ)(i:σ){P:Ideal Eis}(hP:Prime P) :
    0<slotRatio Z ell i P := by
  apply div_pos _ (Real.rpow_pos_of_pos hZ _)
  exact_mod_cast Nat.pos_of_ne_zero (fun h=>hP.ne_zero (Ideal.absNorm_eq_zero_iff.mp h))

theorem common_profile_separation
    (W:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (F:Finset (Ideal Eis))(I:Finset σ)(L:σ→Finset (Ideal Eis))
    (hL:∀i∈I,∀P∈L i,Prime P)(a:σ→Ideal Eis→ℂ)
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime
      (fun i:I=>q i.val i.property)))
    (Z:ℝ)(hZ:0<Z)(ell:σ→ℝ)(A:Finset (primePool F))
    (yj yc:ℝ)(hj:0<yj)(hc:0<yc) :
    (∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
      (if survivingProduct I q∣(∏i∈A,i.val) then
        W (yj*yc/(∏i∈I.attach,slotRatio Z ell i.val (q i.val i.property))) else 0)) =
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW)
        (Real.log yj) t*logPhase t (Real.log yc)*
        primeMark I (fun i=>poolList F (L i))
          (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A := by
  have hm (t:ℝ) : primeMark I (fun i=>poolList F (L i))
      (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A =
      primeMark I L (fun i P=>a i P*logPhase (-t) (Real.log (slotRatio Z ell i P)))
        (activeIndices id I L (∏i∈A,i.val)) :=
    (original_ideal_mark F I L hL
      (fun i P=>a i P*logPhase (-t) (Real.log (slotRatio Z ell i P))) A).symm.trans
      (indexed_mark_active id I L _ _)
  simp_rw [hm]
  have he := actual_overlap_separation W a₀ b₀ ha₀ hs hW I L a (slotRatio Z ell)
    (fun i hi P hP=>slotRatio_pos Z hZ ell i (hL i hi P hP))
    (activeIndices id I L (∏i∈A,i.val)) yj yc hj hc
  rw [←he]
  apply Finset.sum_congr rfl
  intro q hq
  have hprod : (∏i∈I.attach,if q i.val i.property∈activeIndices id I L (∏i∈A,i.val)
      then a i.val (q i.val i.property) else 0)=
      if survivingProduct I q∣(∏i∈A,i.val) then
        ∏i∈I.attach,a i.val (q i.val i.property) else 0 := by
    calc
      _ = ∏i∈I.attach,if q i.val i.property∣(∏i∈A,i.val) then a i.val (q i.val i.property) else 0 := by
        apply Finset.prod_congr rfl
        intro i hi
        simp only [activeIndices_mem id I L _ i.property ((Finset.mem_pi.mp hq) i.val i.property),id_eq]
      _ = _ := by
        convert! tuple_gate_product id I a q (∏i∈A,i.val) (hcop q hq) using 1
  rw [hprod]
  split_ifs <;> simp

theorem common_profile_integrable (g:𝓢(ℝ,ℂ))
    (F:Finset (Ideal Eis))(I:Finset σ)(L:σ→Finset (Ideal Eis))
    (a:σ→Ideal Eis→ℂ)(Z:ℝ)(ell:σ→ℝ)(A:Finset (primePool F))(yj yc:ℝ) :
    Integrable (fun t:ℝ=>density g (Real.log yj) t*logPhase t (Real.log yc)*
      primeMark I (fun i=>poolList F (L i))
        (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A) :=
  overlap_mode_integrable g I (fun i=>poolList F (L i)) (fun i q=>a i q.val)
    (fun i q=>Real.log (slotRatio Z ell i q.val)) A (Real.log yj) (Real.log yc)

end SevenEighths.InverseInitialCommonProfile

end

end OAI
end OAIOriginalModule2130

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialCommonCutoff
Source SHA256: d25a54ac14a4e7eb0004a2d8a6a573fb31faa8b5d9a07a1380d7252d6600e803
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2131



namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic
namespace SevenEighths.InverseInitialCommonCutoff
open InverseMoment InverseInitialCommonProfile InverseInitialCommonRatios
open InverseInitialOverlapIdealFourier InverseInitialOverlapSource
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

def tupleProfile (I:Finset σ)(L:σ→Finset (Ideal Eis))(a:σ→Ideal Eis→ℂ)
    (Z:ℝ)(ell:σ→ℝ)(W:ℝ→ℂ)(yj yc:ℝ)(c:Ideal Eis) : ℂ :=
  ∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
    (if survivingProduct I q∣c then
      W (yj*yc/(∏i∈I.attach,slotRatio Z ell i.val (q i.val i.property))) else 0)

theorem tupleProfile_gates (I:Finset σ)(L:σ→Finset (Ideal Eis))(a:σ→Ideal Eis→ℂ)
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=>q i.val i.property)))
    (Z:ℝ)(ell:σ→ℝ)(W:ℝ→ℂ)(yj yc:ℝ)(c:Ideal Eis) :
    tupleProfile I L a Z ell W yj yc c=
      ∑q∈I.pi L,
        (∏i∈I.attach,if q i.val i.property∈activeIndices id I L c then a i.val (q i.val i.property) else 0)*
          W (yj*yc/(∏i∈I.attach,slotRatio Z ell i.val (q i.val i.property))) := by
  apply Finset.sum_congr rfl
  intro q hq
  have hg : (∏i∈I.attach,if q i.val i.property∈activeIndices id I L c then a i.val (q i.val i.property) else 0)=
      if survivingProduct I q∣c then ∏i∈I.attach,a i.val (q i.val i.property) else 0 := by
    calc
      _ = ∏i∈I.attach,if q i.val i.property∣c then a i.val (q i.val i.property) else 0 := by
        apply Finset.prod_congr rfl
        intro i hi
        simp only [activeIndices_mem id I L _ i.property ((Finset.mem_pi.mp hq) i.val i.property),id_eq]
      _ = _ := by
        convert! tuple_gate_product id I a q c (hcop q hq) using 1
  rw [hg]
  split_ifs <;> simp

theorem tupleProfile_insert_fresh
    (I:Finset σ)(L:σ→Finset (Ideal Eis))(a:σ→Ideal Eis→ℂ)
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=>q i.val i.property)))
    (Z:ℝ)(ell lo hi:σ→ℝ)(W wFresh:ℝ→ℂ)(a₀ b₀ jlo jhi:ℝ)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (ha:∀i∈I,∀q∈L i,a i q≠0→slotRatio Z ell i q∈Set.Icc (lo i) (hi i))
    (hFresh:∀(v:σ→ℝ)(yj yc:ℝ),(∀i∈I,v i∈Set.Icc (lo i) (hi i))→
      yj∈Set.Icc jlo jhi→0<yc→W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1)
    (yj yc:ℝ)(hj:yj∈Set.Icc jlo jhi)(hc:0<yc)(c:Ideal Eis) :
    wFresh yc*tupleProfile I L a Z ell W yj yc c=tupleProfile I L a Z ell W yj yc c := by
  rw [tupleProfile_gates I L a hcop]
  exact insert_original_fresh I L a (slotRatio Z ell) lo hi W wFresh a₀ b₀ jlo jhi
    hs ha hFresh (activeIndices id I L c) yj yc hj hc

end SevenEighths.InverseInitialCommonCutoff

end

end OAI
end OAIOriginalModule2131

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialCommonTransform
Source SHA256: 4dbfe0cb1619f492a4cdba7620831a0e55f09a7fb7d429e0dac07b5965451f94
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2132


namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open ConcretePrimeRowBridge FirstCauchyArithmetic SecondPassArithmetic FirstPassCubeLabels
namespace SevenEighths.InverseInitialCommonTransform
open InverseMoment InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonProfile
open InverseInitialCommonCutoff InverseInitialCommonTuples InverseInitialOverlapFourier
open InverseInitialOverlapInputFourier InverseInitialRayAttachment InverseInitialArithmetic
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialEnergyCallerWindow
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

theorem original_profile_point
    (W wFresh:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (F:Finset (Ideal Eis))(I:Finset σ)(L:σ→Finset (Ideal Eis))
    (hL:∀i∈I,∀P∈L i,Prime P)(a:σ→Ideal Eis→ℂ)
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=>q i.val i.property)))
    (Z:ℝ)(hZ:0<Z)(ell lo hi:σ→ℝ)(jlo jhi:ℝ)
    (ha:∀i∈I,∀q∈L i,a i q≠0→slotRatio Z ell i q∈Set.Icc (lo i) (hi i))
    (hFresh:∀(v:σ→ℝ)(yj yc:ℝ),(∀i∈I,v i∈Set.Icc (lo i) (hi i))→
      yj∈Set.Icc jlo jhi→0<yc→W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1)
    (A:Finset (primePool F))(yj yc:ℝ)(hj:yj∈Set.Icc jlo jhi)(hjpos:0<yj)(hc:0<yc) :
    tupleProfile I L a Z ell W yj yc (∏i∈A,i.val)=
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW) (Real.log yj) t*
        (primeMark I (fun i=>poolList F (L i))
          (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A*
          childLogTest wFresh t yc) := by
  have he := common_profile_separation W a₀ b₀ ha₀ hs hW F I L hL a hcop Z hZ ell A yj yc hjpos hc
  have hcut := tupleProfile_insert_fresh I L a hcop Z ell lo hi W wFresh a₀ b₀ jlo jhi hs ha hFresh yj yc hj hc (∏i∈A,i.val)
  rw [←hcut]
  unfold tupleProfile
  rw [he,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  unfold childLogTest
  ring

theorem original_tuples_fourier
    (W wFresh:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (I:Finset σ)(L:σ→Finset (Ideal Eis))(hL:∀i∈I,∀P∈L i,Prime P)
    (a:σ→Ideal Eis→ℂ)(j:Ideal Eis)(hj0:j≠0)
    (hP:∀q∈I.pi L,Admissible (j*survivingProduct I q))
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=>q i.val i.property)))
    (η:Ideal Eis→*ℂ)(u:Eis)(Z r z G:ℝ)(hZ:0<Z)(ell lo hi:σ→ℝ)
    (hell:∑i∈I,ell i=z-G)(jlo jhi:ℝ)
    (hj:((j.absNorm:ℝ)/Z^G)∈Set.Icc jlo jhi)
    (ha:∀i∈I,∀q∈L i,a i q≠0→slotRatio Z ell i q∈Set.Icc (lo i) (hi i))
    (hFresh:∀(v:σ→ℝ)(yj yc:ℝ),(∀i∈I,v i∈Set.Icc (lo i) (hi i))→
      yj∈Set.Icc jlo jhi→0<yc→W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1) :
    let S := originalSource Z r b₀
    let P := fun q:∀i∈I,Ideal Eis=>j*survivingProduct I q
    let F := tupleColumns S (I.pi L) P j
    let hF := tupleColumns_admissible S (I.pi L) P j hP
      (fun q _=>dvd_mul_right j _) (originalSource_supported Z r b₀)
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    (∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
      residualNormalizedPolynomial S (P q) j η (fun _=>1) W Z r z G u)=
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW)
        (Real.log ((j.absNorm:ℝ)/Z^G)) t*
        (((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
          (poolPrimary F) (poolPrimary_good F hF) Finset.univ
          (elementCharacter η) (primaryGenerator j) 1 1
          (initialTest (poolPrimary F)
            (primeMark I (fun i=>poolList F (L i))
              (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))))
            (childLogTest wFresh t) Z (r+z-2*G)) u) := by
  intro S P F hF
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have hjpos : 0<(j.absNorm:ℝ)/Z^G := by
    apply div_pos _ (Real.rpow_pos_of_pos hZ G)
    exact_mod_cast Nat.pos_of_ne_zero (fun h=>hj0 (Ideal.absNorm_eq_zero_iff.mp h))
  let g := CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW
  let H : Finset (primePool F)→ℝ→ℂ := fun A t=>density g (Real.log ((j.absNorm:ℝ)/Z^G)) t*
    (primeMark I (fun i=>poolList F (L i))
      (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A*
      childLogTest wFresh t (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)))
  have hHi (A:Finset (primePool F)) : Integrable (H A) := by
    have hh := (common_profile_integrable g F I L a Z ell A
      ((j.absNorm:ℝ)/Z^G) (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G))).const_mul
      (wFresh (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)))
    convert hh using 1
    funext t
    dsimp [H,childLogTest]
    ring
  have hpoint (A:Finset (primePool F)) :
      (∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
        (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
          (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0))=∫t:ℝ,H A t := by
    dsimp only [P]
    simp_rw [actual_residual_product I _ j hj0,original_residual_window I _ j hj0 ell W Z r z G hZ hell]
    apply original_profile_point W wFresh a₀ b₀ ha₀ hs hW F I L hL a hcop Z hZ ell lo hi jlo jhi ha hFresh A
      ((j.absNorm:ℝ)/Z^G) (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) hj hjpos
    apply div_pos _ (Real.rpow_pos_of_pos hZ _)
    exact_mod_cast Nat.pos_of_ne_zero (fun h=>(InitialMeanSquare.poolProduct_admissible F hF A).1
      (Ideal.absNorm_eq_zero_iff.mp h))
  rw [original_tuples_common_input W Z r z G b₀ hZ (fun x hx=>(hs hx).2)
    (I.pi L) P j hP (fun q _=>dvd_mul_right j _) η (fun q=>∏i∈I.attach,a i.val (q i.val i.property)) u]
  change ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
    (poolPrimary F) (poolPrimary_good F hF) Finset.univ
    (elementCharacter η) (primaryGenerator j) 1 1
    (fun A=>∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
      (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
        (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) u = _
  rw [show (fun A:Finset (primePool F)=>∑q∈I.pi L,
    (∏i∈I.attach,a i.val (q i.val i.property))*
      (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
        (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) = (fun A=>∫t:ℝ,H A t)
    from funext hpoint]
  rw [input_integral (poolPrimary F) (poolPrimary_good F hF) Finset.univ
    (elementCharacter η) (primaryGenerator j) u H (fun A _=>hHi A),←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  dsimp only [H]
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF),
    initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  simp only [Finset.mul_sum,initialTest,InitialMeanSquare.poolPrimary_norm F hF]
  apply Finset.sum_congr rfl
  intro A hA
  ring

end SevenEighths.InverseInitialCommonTransform

end

end OAI
end OAIOriginalModule2132

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialExcludedPolynomial
Source SHA256: 4ed3b93565bf3df5ed5a33ab05398968ba57ef9d0743c729cd1d9b3322c77f5e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2133




namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialExcludedPolynomial
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge
open InverseInitialExcludedSource IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O"=>HeckeFamily.O

theorem prime_product_squarefree (S:Finset (Ideal O))(hS:∀P∈S,Prime P):
    Squarefree (∏P∈S,P) := by
  have hz:(∏P∈S,P)≠0:=Finset.prod_ne_zero_iff.mpr (fun P hP=>(hS P hP).ne_zero)
  apply (squarefree_iff_nodup_normalizedFactors hz).mpr
  have he:normalizedFactors (∏P∈S,P)=S.val:=by
    simpa using normalizedFactors_prod_of_prime (m:=S.val) (fun P hP=>hS P hP)
  rw [he]
  exact S.nodup

theorem deleted_coefficient_product (χ:Character)(S:Finset (Ideal O))
    (hS:∀P∈S,Prime P)(I:Ideal O):
    idealCoeff (χ.excludePrimes S hS) I=
      if IsCoprime I (∏P∈S,P) then idealCoeff χ I else 0 := by
  rw [idealCoeff_excludePrimes,IsCoprime.prod_right_iff]
  congr 1

theorem residual_source (χ:Character)(S A:Finset (Ideal O))(hS:∀P∈S,Prime P)
    {j:Ideal O}(hj:j∣∏P∈S,P)(W:ℝ→ℂ)(X:ℝ)
    (hcover:∀I:Ideal O,I≠0→W ((I.absNorm:ℝ)/X)≠0→I∈A):
    (∑c∈columns A (∏P∈S,P) j,(moebius c:ℂ)*idealCoeff χ c*
      W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))))=
    ∑'c:Ideal O,(moebius c:ℂ)*idealCoeff (χ.excludePrimes S hS) c*
      W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))) := by
  have hP:=prime_product_squarefree S hS
  have hj0:=ne_zero_of_dvd_ne_zero hP.ne_zero hj
  symm
  calc
    _ = ∑c∈columns A (∏P∈S,P) j,(moebius c:ℂ)*idealCoeff (χ.excludePrimes S hS) c*
        W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))) := by
      apply tsum_eq_sum
      intro c hc
      by_cases hcs:Squarefree c
      · by_cases hcp:IsCoprime c (∏P∈S,P)
        · have hw:W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ)))=0:=by
            by_contra hw
            apply hc
            apply (mem_columns hP hj).mpr
            refine ⟨hcs,hcp,hcover (j*c) (mul_ne_zero hj0 hcs.ne_zero) ?_⟩
            rwa [cutoff_argument]
          rw [hw,mul_zero]
        · rw [deleted_coefficient_product,ite_eq_right hcp,mul_zero,zero_mul]
      · rw [moebius_of_not_squarefree hcs,Int.cast_zero,zero_mul,zero_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [deleted_coefficient_product,ite_eq_left ((mem_columns hP hj).mp hc).2.1]

theorem source_decomposition (χ:Character)(S A:Finset (Ideal O))(hS:∀P∈S,Prime P)
    (W:ℝ→ℂ)(X:ℝ)(hcover:∀I:Ideal O,I≠0→W ((I.absNorm:ℝ)/X)≠0→I∈A):
    (∑I∈A,(moebius I:ℂ)*idealCoeff χ I*W ((I.absNorm:ℝ)/X))=
    ∑j∈idealDivisors (∏P∈S,P),((moebius j:ℂ)*idealCoeff χ j)*
      ∑'c:Ideal O,(moebius c:ℂ)*idealCoeff (χ.excludePrimes S hS) c*
        W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))) := by
  have he:=polynomial_decomposition A (prime_product_squarefree S hS)
    (idealCoeff χ).toMonoidHom (fun _=>1) W X
  simp only [mul_one] at he
  trans ∑j∈idealDivisors (∏P∈S,P),((moebius j:ℂ)*idealCoeff χ j)*
    ∑c∈columns A (∏P∈S,P) j,(moebius c:ℂ)*idealCoeff χ c*
      W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ)))
  · exact he
  apply Finset.sum_congr rfl
  intro j hj
  rw [residual_source χ S A hS ((mem_idealDivisors (prime_product_squarefree S hS).ne_zero).mp hj) W X hcover]

theorem polynomial_all_ideals (χ:Character)(W:ℝ→ℂ)(X σ t:ℝ):
    polynomial χ true W X σ t=(X:ℂ)^(-(1/2:ℂ))*
      ∑'I:Ideal O,(moebius I:ℂ)*idealCoeff χ I*
        (W ((I.absNorm:ℝ)/X)*(((I.absNorm:ℝ)/X:ℝ):ℂ)^(-shift σ t)) := by
  unfold polynomial
  congr 1
  let f:Ideal O→ℂ:=fun I=>(moebius I:ℂ)*idealCoeff χ I*
    (W ((I.absNorm:ℝ)/X)*(((I.absNorm:ℝ)/X:ℝ):ℂ)^(-shift σ t))
  have hf:Function.support f⊆{I:Ideal O|I≠0}:=by
    intro I hi hz
    subst I
    exact hi (by simp only [f,map_zero,mul_zero,zero_mul])
  have he:=tsum_subtype_eq_of_support_subset hf
  calc
    _=∑'I:{I:Ideal O//I≠0},f I.val:=by
      apply tsum_congr
      intro I
      simp only [summand,coefficient,ite_true,HeckeDyadic.norm,f]
      ring
    _=_:=he

theorem scale_normalization (X n:ℝ)(hX:0<X)(hn:0<n):
    (n:ℂ)^(-(1/2:ℂ))*((X/n:ℝ):ℂ)^(-(1/2:ℂ))=(X:ℂ)^(-(1/2:ℂ)) := by
  rw [←Complex.mul_cpow_ofReal_nonneg hn.le (div_pos hX hn).le,
    ←Complex.ofReal_mul,mul_div_cancel₀ _ hn.ne']

theorem inverse_polynomial_decomposition (χ:Character)(S:Finset (Ideal O))
    (hS:∀P∈S,Prime P)(W:ℝ→ℂ)(X σ t b:ℝ)(hX:0<X)
    (hW:∀x,W x≠0→x≤b):
    polynomial χ true W X σ t=
    ∑j∈idealDivisors (∏P∈S,P),
      ((moebius j:ℂ)*idealCoeff χ j*(j.absNorm:ℂ)^(-(1/2:ℂ)))*
        polynomial (χ.excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t := by
  let A:=ConcretePrimeRowBridge.idealsUpTo ⌈X*b⌉₊
  let V:ℝ→ℂ:=fun x=>W x*(x:ℂ)^(-shift σ t)
  have hc:∀I:Ideal O,I≠0→W ((I.absNorm:ℝ)/X)≠0→I∈A:=
    InverseInitialRawDictionary.finite_source_cover W X b hX hW
  have hcv:∀I:Ideal O,I≠0→V ((I.absNorm:ℝ)/X)≠0→I∈A:=by
    intro I hi hv
    apply hc I hi
    intro hw
    exact hv (by simp [V,hw])
  rw [polynomial_eq_finite χ true W X σ t A hc]
  have hsource:=source_decomposition χ S A hS V X hcv
  have hfinite:(∑I∈A,coefficient χ true I*W ((I.absNorm:ℝ)/X)*
      (((I.absNorm:ℝ)/X:ℝ):ℂ)^(-shift σ t))=
      ∑I∈A,(moebius I:ℂ)*idealCoeff χ I*V ((I.absNorm:ℝ)/X):=by
    apply Finset.sum_congr rfl
    intro I hi
    simp only [coefficient,ite_true,V]
    ring
  rw [hfinite,hsource,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjd: j∣∏P∈S,P:=(mem_idealDivisors (prime_product_squarefree S hS).ne_zero).mp hj
  have hj0:j≠0:=ne_zero_of_dvd_ne_zero (prime_product_squarefree S hS).ne_zero hjd
  have hjpos:0<(j.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj0)
  rw [polynomial_all_ideals]
  have hn:=scale_normalization X (j.absNorm:ℝ) hX hjpos
  simp only [Complex.ofReal_natCast] at hn
  dsimp only [V]
  rw [←hn]
  ring

end SevenEighths.InverseInitialExcludedPolynomial

end

end OAI
end OAIOriginalModule2133

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialExcludedEnergy
Source SHA256: 51070863dc442d6655736179678ad4f129b8ff99853a703bbb540d0d6240ce13
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2134


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialExcludedEnergy
open HeckeFamily HeckeDyadic InverseInitialExcludedPolynomial
open IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O"=>HeckeFamily.O

def deletionWeight (χ:Character)(j:Ideal O):ℂ:=
  (moebius j:ℂ)*idealCoeff χ j*(j.absNorm:ℂ)^(-(1/2:ℂ))

theorem deletionWeight_norm_le_one (χ:Character){j:Ideal O}(hj:j≠0):
    ‖deletionWeight χ j‖≤1 := by
  have hn:1≤(j.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj)
  have hp:0<(j.absNorm:ℝ):=lt_of_lt_of_le zero_lt_one hn
  have hw:‖(j.absNorm:ℂ)^(-(1/2:ℂ))‖≤1:=by
    rw [←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hp]
    apply Real.rpow_le_one_of_one_le_of_nonpos hn
    norm_num
  dsimp [deletionWeight]
  rw [norm_mul,norm_mul]
  calc
    _≤1*1:=mul_le_mul
      (by simpa only [one_mul] using (mul_le_mul (CubicEisenstein.norm_ideal_moebius_le_one j)
        (idealCoeff_norm_le_one χ j) (norm_nonneg _) zero_le_one)) hw
      (norm_nonneg _) (by positivity)
    _=1:=one_mul _

theorem marked_pointwise (χ:Character)(S:Finset (Ideal O))(hS:∀P∈S,Prime P)
    (W:ℝ→ℂ)(X σ t b:ℝ)(hX:0<X)(hW:∀x,W x≠0→x≤b)(mark:ℂ):
    ‖polynomial χ true W X σ t*mark‖^2≤
    ((idealDivisors (∏P∈S,P)).card:ℝ)*
      ∑j∈idealDivisors (∏P∈S,P),
        ‖polynomial (χ.excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t*mark‖^2 := by
  rw [inverse_polynomial_decomposition χ S hS W X σ t b hX hW,Finset.sum_mul]
  have hn:‖∑j∈idealDivisors (∏P∈S,P),
      ((moebius j:ℂ)*idealCoeff χ j*(j.absNorm:ℂ)^(-(1/2:ℂ)))*
        polynomial (χ.excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t*mark‖≤
      ∑j∈idealDivisors (∏P∈S,P),
        ‖polynomial (χ.excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t*mark‖:=by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro j hj
    change ‖deletionWeight χ j*polynomial _ _ _ _ _ _*mark‖≤_
    rw [mul_assoc,norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    apply deletionWeight_norm_le_one χ
    exact ne_zero_of_dvd_ne_zero (prime_product_squarefree S hS).ne_zero
      ((mem_idealDivisors (prime_product_squarefree S hS).ne_zero).mp hj)
  have hh:=Finset.sum_mul_sq_le_sq_mul_sq (idealDivisors (∏P∈S,P))
    (fun _=>(1:ℝ)) (fun j=>‖polynomial (χ.excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t*mark‖)
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hh
  exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _=>norm_nonneg _))).mpr hn |>.trans
    hh

theorem marked_family {ι:Type*}(rows:Finset ι)(χ:ι→Character)
    (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(W:ℝ→ℂ)(X σ t b:ℝ)
    (hX:0<X)(hW:∀x,W x≠0→x≤b)(mark:ι→ℂ)(weight:ι→ℝ)
    (hw:∀u∈rows,0≤weight u):
    (∑u∈rows,weight u*‖polynomial (χ u) true W X σ t*mark u‖^2)≤
      ((idealDivisors (∏P∈S,P)).card:ℝ)*
      ∑j∈idealDivisors (∏P∈S,P),∑u∈rows,weight u*
        ‖polynomial ((χ u).excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t*mark u‖^2 := by
  calc
    _≤∑u∈rows,weight u*(((idealDivisors (∏P∈S,P)).card:ℝ)*
      ∑j∈idealDivisors (∏P∈S,P),
        ‖polynomial ((χ u).excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t*mark u‖^2):=by
      apply Finset.sum_le_sum
      intro u hu
      exact mul_le_mul_of_nonneg_left (marked_pointwise (χ u) S hS W X σ t b hX hW (mark u)) (hw u hu)
    _=_:=by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro u hu
      ring

end SevenEighths.InverseInitialExcludedEnergy

end

end OAI
end OAIOriginalModule2134

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialExcludedGeometry
Source SHA256: 9d118674c8a153c99ca10a67930a93b771b8558aa51840d815114de68e4ede38
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2135


namespace OAI

noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace SevenEighths.InverseInitialExcludedGeometry
open HeckeFamily InverseInitialExcludedPolynomial IdealMobiusDivisorSum
local notation "O"=>HeckeFamily.O

def adjustedLength (Z r:ℝ)(j:Ideal O):ℝ:=r-Real.log (j.absNorm:ℝ)/Real.log Z

theorem adjusted_scale (Z r:ℝ)(hZ:1<Z){j:Ideal O}(hj:j≠0):
    Z^adjustedLength Z r j=Z^r/(j.absNorm:ℝ) := by
  have hjpos:0<(j.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj)
  have hzpos:=lt_trans zero_lt_one hZ
  rw [adjustedLength,Real.rpow_sub hzpos]
  congr 1
  rw [Real.rpow_def_of_pos hzpos]
  have hl:Real.log Z≠0:=(Real.log_pos hZ).ne'
  rw [mul_div_cancel₀ _ hl,Real.exp_log hjpos]

theorem divisor_norm_bounds {P j:Ideal O}(hP:P≠0)(hj:j∣P):
    1≤(j.absNorm:ℝ) ∧ (j.absNorm:ℝ)≤(P.absNorm:ℝ) := by
  have hj0:=ne_zero_of_dvd_ne_zero hP hj
  constructor
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj0)
  · exact_mod_cast Nat.le_of_dvd
      (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hP))
      (map_dvd Ideal.absNorm hj)

theorem adjustedLength_bounds (Z r η:ℝ)(hZ:1<Z){P j:Ideal O}
    (hP:P≠0)(hj:j∣P)(hlarge:Real.log (P.absNorm:ℝ)≤η*Real.log Z):
    r-η≤adjustedLength Z r j ∧ adjustedLength Z r j≤r := by
  obtain ⟨hn,hnP⟩:=divisor_norm_bounds hP hj
  have hl:0≤Real.log (j.absNorm:ℝ):=Real.log_nonneg hn
  have hu:Real.log (j.absNorm:ℝ)≤η*Real.log Z:=
    (Real.log_le_log (lt_of_lt_of_le zero_lt_one hn) hnP).trans hlarge
  have hd:Real.log (j.absNorm:ℝ)/Real.log Z≤η:=(div_le_iff₀ (Real.log_pos hZ)).mpr hu
  have hd0:0≤Real.log (j.absNorm:ℝ)/Real.log Z:=div_nonneg hl (Real.log_pos hZ).le
  dsimp [adjustedLength]
  constructor <;> linarith

theorem adjustedLength_eventually (P:Ideal O)(hP:P≠0)(η:ℝ)(hη:0<η):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀r:ℝ,∀j∈idealDivisors P,
      r-η≤adjustedLength Z r j ∧ adjustedLength Z r j≤r := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.log (P.absNorm:ℝ)/η))] with Z hZ hlog
  refine ⟨hZ,fun r j hj=>adjustedLength_bounds Z r η hZ hP ((mem_idealDivisors hP).mp hj) ?_⟩
  exact (div_le_iff₀ hη).mp hlog |>.trans_eq (mul_comm _ _)

theorem prime_coprime_of_norm_gt {P I:Ideal O}(hP:Prime P)(hI:I≠0)
    (hN:(I.absNorm:ℝ)<(P.absNorm:ℝ)):IsCoprime P I := by
  apply Ideal.coprime_of_no_prime_ge
  intro J hPJ hIJ hJ
  have hmax:=(Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  have heq:=hmax.eq_of_le hJ.ne_top hPJ
  rw [←heq] at hIJ
  have hd:P∣I:=Ideal.dvd_iff_le.mpr hIJ
  exact (not_le_of_gt hN) (divisor_norm_bounds hI hd).2

theorem live_prime_deleted_coefficient (χ:Character)(S:Finset (Ideal O))
    (hS:∀P∈S,Prime P)(V:ℝ→ℂ)(a Y:ℝ)(hY:0<Y)
    (hV:∀x,V x≠0→a≤x)(hlarge:((∏Q∈S,Q).absNorm:ℝ)<a*Y)
    (P:Ideal O)(hP:Prime P)(hvp:V ((P.absNorm:ℝ)/Y)≠0):
    idealCoeff (χ.excludePrimes S hS) P=idealCoeff χ P := by
  rw [deleted_coefficient_product,ite_eq_left]
  apply prime_coprime_of_norm_gt hP (prime_product_squarefree S hS).ne_zero
  exact hlarge.trans_le ((le_div_iff₀ hY).mp (hV _ hvp))

theorem prime_slot_unchanged (χ:Character)(S:Finset (Ideal O))
    (hS:∀P∈S,Prime P)(V:ℝ→ℂ)(a Y:ℝ)(hY:0<Y)
    (hV:∀x,V x≠0→a≤x)(hlarge:((∏Q∈S,Q).absNorm:ℝ)<a*Y)
    (P:Ideal O)(hP:Prime P):
    idealCoeff (χ.excludePrimes S hS) P*V ((P.absNorm:ℝ)/Y)=
      idealCoeff χ P*V ((P.absNorm:ℝ)/Y) := by
  by_cases hv:V ((P.absNorm:ℝ)/Y)=0
  · rw [hv,mul_zero,mul_zero]
  · rw [live_prime_deleted_coefficient χ S hS V a Y hY hV hlarge P hP hv]

end SevenEighths.InverseInitialExcludedGeometry

end

end OAI
end OAIOriginalModule2135

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialExcludedPeriod
Source SHA256: 6117215462c6dc54bea95092141366fe24ffe9fcd717bd33ed6e6721f6e86785
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2136



namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialExcludedPeriod
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open CanonicalCoefficientClass ConcretePrimeRowBridge IdealMobiusDivisorSum
open UniqueFactorizationMonoid HeckeFamily
local notation "O" => ActualEisensteinCubic.O

def deletedPeriod (q:ℕ):ℕ := 2592*q^2

theorem deletedPeriod_ne_zero (q:ℕ)(hq:q≠0):deletedPeriod q≠0 := by
  unfold deletedPeriod
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ hq)

theorem fixed_bad_divides_reflection (q:ℕ)(P:Ideal O)(hP:P∈fixedBadPrimes):
    P∣Ideal.span {reflectionConductor q} := by
  change P∈({Ideal.span {goodLambda},Ideal.span {(2:O)}}:Finset (Ideal O)) at hP
  rcases Finset.mem_insert.mp hP with rfl|hP
  · apply Ideal.dvd_iff_le.mpr
    apply Ideal.span_singleton_le_span_singleton.mpr
    have h3:goodLambda∣(3:O):=CubicEisenstein.halfPrimary_lambda_dvd_three
    apply h3.trans
    refine ⟨(864*q:ℕ),?_⟩
    unfold reflectionConductor
    push_cast
    ring
  · rw [Finset.mem_singleton.mp hP]
    apply Ideal.dvd_iff_le.mpr
    apply Ideal.span_singleton_le_span_singleton.mpr
    refine ⟨(1296*q:ℕ),?_⟩
    unfold reflectionConductor
    push_cast
    ring

theorem excluded_mem_iff (q:ℕ)(hq:q≠0)(P:Ideal O):
    P∈reflectionExcludedPrimes q ↔ Prime P ∧ P∣Ideal.span {reflectionConductor q} := by
  constructor
  · intro hP
    refine ⟨reflectionExcludedPrimes_prime q P hP,?_⟩
    rcases Finset.mem_union.mp hP with hb|hp
    · exact fixed_bad_divides_reflection q P hb
    · exact dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hp)
  · rintro ⟨hp,hd⟩
    exact reflectionConductor_prime_mem q hq P hp hd

theorem excluded_product_divides_reflection (q:ℕ)(hq:q≠0):
    (∏P∈reflectionExcludedPrimes q,P)∣Ideal.span {reflectionConductor q} := by
  apply support_product_dvd (Ideal.span_singleton_eq_bot.not.mpr (reflectionConductor_ne_zero q hq))
  intro P hP
  apply Multiset.mem_toFinset.mpr
  apply (Ideal.mem_normalizedFactors_iff
    (Ideal.span_singleton_eq_bot.not.mpr (reflectionConductor_ne_zero q hq))).mpr
  obtain ⟨hp,hd⟩:= (excluded_mem_iff q hq P).mp hP
  exact ⟨Ideal.isPrime_of_prime hp,Ideal.dvd_iff_le.mp hd⟩

theorem deleted_reflection_ideal (q:ℕ):
    Ideal.span {reflectionConductor (deletedPeriod q)}=
      (Ideal.span {reflectionConductor q}:Ideal O)^2 := by
  rw [Ideal.span_singleton_pow]
  congr 1
  unfold reflectionConductor deletedPeriod
  push_cast
  ring_nf

theorem deleted_excluded_eq (q:ℕ)(hq:q≠0):
    reflectionExcludedPrimes (deletedPeriod q)=reflectionExcludedPrimes q := by
  ext P
  rw [excluded_mem_iff _ (deletedPeriod_ne_zero q hq),excluded_mem_iff q hq,
    deleted_reflection_ideal]
  constructor
  · rintro ⟨hp,hd⟩
    exact ⟨hp,hp.dvd_of_dvd_pow hd⟩
  · rintro ⟨hp,hd⟩
    exact ⟨hp,hd.trans (dvd_pow_self _ (by decide:2≠0))⟩

theorem deleted_period_ideal (q:ℕ):
    (Ideal.span {(deletedPeriod q:O)}:Ideal O)=
      Ideal.span {(q:O)}*Ideal.span {reflectionConductor q} := by
  rw [Ideal.span_singleton_mul_span_singleton]
  congr 1
  unfold deletedPeriod reflectionConductor
  push_cast
  ring_nf

theorem deleted_period_le_modulus (χ:Character)(q:ℕ)(hq:q≠0)
    (hperiod:Ideal.span {(q:O)}≤χ.modulus):
    Ideal.span {(deletedPeriod q:O)}≤
      (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)).modulus := by
  change Ideal.span {(deletedPeriod q:O)}≤χ.modulus*(∏P∈reflectionExcludedPrimes q,P)
  rw [deleted_period_ideal]
  exact Ideal.mul_mono hperiod (Ideal.dvd_iff_le.mp (excluded_product_divides_reflection q hq))

theorem deleted_element_period (χ:Character)(q:ℕ)(hq:q≠0)
    (hperiod:Ideal.span {(q:O)}≤χ.modulus):
    FactorsModulo (fixedBaseConductor (deletedPeriod q))
      (HeckeRowClosure.elementHom
        (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))) := by
  intro x y hxy
  apply HeckeRowClosure.elementHom_periodic
  exact deleted_period_le_modulus χ q hq hperiod (Ideal.mul_le_left hxy)

theorem deleted_base_gates (χ:Character)(q:ℕ)(hq:q≠0)
    (hperiod:Ideal.span {(q:O)}≤χ.modulus):
    deletedPeriod q≠0 ∧ reflectionExcludedPrimes (deletedPeriod q)=reflectionExcludedPrimes q ∧
    (∀x,‖HeckeRowClosure.elementHom
      (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)) x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod q))
      (HeckeRowClosure.elementHom
        (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))) := by
  exact ⟨deletedPeriod_ne_zero q hq,deleted_excluded_eq q hq,
    HeckeRowClosure.elementHom_norm _,deleted_element_period χ q hq hperiod⟩

end SevenEighths.InverseInitialExcludedPeriod

end

end OAI
end OAIOriginalModule2136

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialExcludedElement
Source SHA256: f0cc33bb400ff2739b90b0511a7e6f522e63dd8d415591e33b5ca3bfe578cb04
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2137



namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialExcludedPeriod
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open CanonicalCoefficientClass HeckeFamily InverseInitialRayAttachment
local notation "O"=>ActualEisensteinCubic.O

theorem elementCharacter_eq_elementHom (χ:Character)(hproper:χ.modulus≠⊤):
    elementCharacter (idealCoeff χ).toMonoidHom=HeckeRowClosure.elementHom χ := by
  let:Nontrivial (O⧸χ.modulus):=Ideal.Quotient.nontrivial_iff.mpr hproper
  ext z
  change idealCoeff χ (Ideal.span {z})=elementCoeff χ z
  by_cases hz:z=0
  · subst z
    simp only [Ideal.span_singleton_zero,←Ideal.zero_eq_bot,
      elementCoeff,map_zero,MulChar.map_zero]
  · exact idealCoeff_span χ hz

theorem deleted_modulus_proper (χ:Character)(q:ℕ):
    (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)).modulus≠⊤ := by
  have htwo:(Ideal.span {(2:O)}:Ideal O)∈reflectionExcludedPrimes q:=
    reflectionExcludedPrimes_bad q (by simp [fixedBadPrimes])
  have hle:(χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)).modulus≤
      Ideal.span {(2:O)}:=by
    change χ.modulus*(∏P∈reflectionExcludedPrimes q,P)≤Ideal.span {(2:O)}
    exact Ideal.mul_le_right.trans (Ideal.dvd_iff_le.mp (Finset.dvd_prod_of_mem (fun P=>P) htwo))
  intro he
  exact twoIdeal_maximal.ne_top (top_le_iff.mp (he ▸ hle))

theorem deleted_physical_element_eq (χ:Character)(q:ℕ):
    elementCharacter (idealCoeff
      (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))).toMonoidHom=
      HeckeRowClosure.elementHom
        (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)) :=
  elementCharacter_eq_elementHom _ (deleted_modulus_proper χ q)

theorem deleted_physical_base_gates (χ:Character)(q:ℕ)(hq:q≠0)
    (hperiod:Ideal.span {(q:O)}≤χ.modulus):
    deletedPeriod q≠0 ∧ reflectionExcludedPrimes (deletedPeriod q)=reflectionExcludedPrimes q ∧
    (∀x,‖elementCharacter (idealCoeff
      (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))).toMonoidHom x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod q))
      (elementCharacter (idealCoeff
        (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))).toMonoidHom) := by
  rw [deleted_physical_element_eq]
  exact deleted_base_gates χ q hq hperiod

end SevenEighths.InverseInitialExcludedPeriod

end

end OAI
end OAIOriginalModule2137

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialLargePool
Source SHA256: 6e3011923fa8d25d1ab6bde05db5653c196f883c282f978acdca2b39dec61a5f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2138


namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open FirstCauchyArithmetic SecondPassArithmetic UniqueFactorizationMonoid CanonicalRowCompletion
namespace SevenEighths.InverseInitialLargePool
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialRayAttachment InverseInitialArithmetic InverseInitialCommonPool
open InverseInitialEnergyCallerWindow InverseInitialCommonForcing InverseInitialCommonTuples
local notation "Eis"=>ActualEisensteinCubic.O
local notation "O"=>ActualEisensteinCubic.O
theorem selected_conjugate_row_supported (F : Finset (Ideal O))
    (hF : ∀ I ∈ F,Admissible I) (j : Ideal O) (hj : Admissible j)
    (η : Ideal O →* ℂ) (H : Ideal O → ℂ)
    (hcop : ∀ I ∈ F,H I≠0→IsCoprime I j) (u : O) :
    let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    (∑ I ∈ F,(moebius I : ℂ)*η I*H I*star (idealRowHom u I)) =
      inputConjugateRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A => if (∏ i ∈ A,i.val)∈F then H (∏ i ∈ A,i.val) else 0) u := by
  let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have he : (fun i : primePool F => Ideal.span {poolPrimary F i}) =
      (fun i : primePool F => i.val) := funext (poolPrimary_span F hF)
  dsimp only
  rw [InitialMeanSquare.sum_selected_ideals F (fun I hI => (hF I hI).2.1)]
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  dsimp only
  rw [elementCharacter_product]
  simp only [he]
  by_cases hAF : (∏ i ∈ A,i.val)∈F
  · simp only [hAF,ite_true]
    by_cases hh:H (∏i∈A,i.val)=0
    · simp only [hh,mul_zero,zero_mul]
    rw [selected_mask F j hj A (hcop _ hAF hh),mul_one]
    rw [idealRowHom_eq_idealSexticRow F hF hAF]
    simp only [supportMobius,idealSexticRow,InitialMeanSquare.pool_support_product]
    ring
  · simp only [hAF,ite_false,mul_zero,zero_mul]

theorem residual_eq_large_input
    (S F : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Admissible P) (hj : j∣P) (hF : ∀I∈F,Admissible I)
    (hsub : columns S P j⊆F)
    (η : Ideal Eis→*ℂ) (a : Ideal Eis→ℂ) (W : ℝ→ℂ)
    (Z r z G : ℝ) (u : Eis) :
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    residualNormalizedPolynomial S P j η a W Z r z G u =
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>if (∏i∈A,i.val)∈columns S P j then
          a (reconstruct P j (∏i∈A,i.val))*residualOverlapWindow P j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0) u := by
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  let H : Ideal Eis→ℂ := fun c=>if c∈columns S P j then
    a (reconstruct P j c)*residualOverlapWindow P j W Z z G
      ((c.absNorm:ℝ)/Z^(r+z-2*G)) else 0
  have hfilter : F.filter (fun c=>c∈columns S P j)=columns S P j := by
    ext c
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun h=>hsub h)
  have he : (∑c∈columns S P j,
      overlapResidualCoefficient P j η a W Z r z G c*star (CanonicalRowCompletion.idealRowHom u c))=
      ∑c∈F,(moebius c:ℂ)*η c*H c*star (CanonicalRowCompletion.idealRowHom u c) := by
    conv_rhs => arg 2;ext c;dsimp only [H];simp only [mul_ite,mul_zero,ite_mul,zero_mul]
    rw [←Finset.sum_filter,hfilter]
    apply Finset.sum_congr rfl
    intro c hc
    rw [overlapCoefficient_residual]
    unfold bareOverlapCoefficient
    ring
  unfold residualNormalizedPolynomial
  have hcH : ∀I∈F,H I≠0→IsCoprime I j := by
    intro I hIF hHI
    by_cases hi:I∈columns S P j
    · exact ((mem_columns hP.2.1 hj).mp hi).2.1
    · exact False.elim (hHI (by simp [H,hi]))
  rw [he,selected_conjugate_row_supported F hF j (admissible_of_dvd hP hj) η H hcH u]
  apply congrArg (fun v:ℂ=>((Z^(-(r+z-2*G)/2):ℝ):ℂ)*v)
  congr 1
  funext A
  dsimp [H]
  by_cases hc : (∏i∈A,i.val)∈columns S P j
  · simp only [hc,hsub hc,ite_true]
  · simp only [hc,ite_false,ite_self]

theorem residual_eq_large_forcing
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    {P j:Ideal Eis}(hP:Admissible P)(hj:j∣P)
    (F:Finset (Ideal Eis))(hF:∀I∈F,Admissible I)
    (hsub:columns (originalSource Z r b) P j⊆F)
    (η:Ideal Eis→*ℂ)(u:Eis) :
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    residualNormalizedPolynomial (originalSource Z r b) P j η (fun _=>1) W Z r z G u =
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>if residual P j∣(∏i∈A,i.val) then
          residualOverlapWindow P j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0) u := by
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  rw [residual_eq_large_input _ F hP hj hF hsub η (fun _=>1) W Z r z G u]
  simp only [one_mul]
  apply congrArg (fun v:ℂ=>((Z^(-(r+z-2*G)/2):ℝ):ℂ)*v)
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF),
    initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  have he := common_selector_window W Z r z G b hZ hW hP hj F hF A
  have hm : rowCoprimeMask (fun i:primePool F=>Ideal.span {poolPrimary F i}) A
      (primaryGenerator j)=rowCoprimeMask (fun i:primePool F=>i.val) A
        (primaryGenerator j) := by
    congr 1
    funext i
    exact poolPrimary_span F hF i
  dsimp only
  rw [hm]
  linear_combination
    (supportMobius (fun i:primePool F=>Ideal.span {poolPrimary F i}) A *
      elementCharacter η (∏i∈A,poolPrimary F i) *
      star (finiteSquarefreeRow (fun i:primePool F=>Ideal.span {poolPrimary F i})
        (poolPrimary_good F hF) A u))*he

variable {κ:Type*}
theorem original_tuples_large_input
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    (T:Finset κ)(P:κ→Ideal Eis)(j:Ideal Eis)
    (hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (F:Finset (Ideal Eis))(hF:∀I∈F,Admissible I)
    (hsub:tupleColumns (originalSource Z r b) T P j⊆F)
    (η:Ideal Eis→*ℂ)(a:κ→ℂ)(u:Eis) :
    let S := originalSource Z r b
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    (∑k∈T,a k*residualNormalizedPolynomial S (P k) j η (fun _=>1) W Z r z G u)=
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>∑k∈T,a k*(if residual (P k) j∣(∏i∈A,i.val) then
          residualOverlapWindow (P k) j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) u := by
  intro S
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  rw [input_finset_sum (poolPrimary F) (poolPrimary_good F hF)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [residual_eq_large_forcing W Z r z G b hZ hW (hP k hk) (hj k hk) F hF
    (fun c hc=>hsub (Finset.mem_biUnion.mpr ⟨k,hk,hc⟩)) η u]
  ring

end SevenEighths.InverseInitialLargePool

end

end OAI
end OAIOriginalModule2138

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialLargeFourier
Source SHA256: 7eee425238b0df174f668893377bb22c9a635447cc3b5d1cc7f09f15f73a3814
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2139


namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open ConcretePrimeRowBridge FirstCauchyArithmetic SecondPassArithmetic FirstPassCubeLabels
namespace SevenEighths.InverseInitialLargeFourier
open InverseMoment InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonProfile
open InverseInitialCommonCutoff InverseInitialCommonTuples InverseInitialOverlapFourier
open InverseInitialOverlapInputFourier InverseInitialRayAttachment InverseInitialArithmetic
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialEnergyCallerWindow
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

open InverseInitialCommonTransform InverseInitialLargePool
theorem original_tuples_large_fourier
    (W wFresh:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (I:Finset σ)(L:σ→Finset (Ideal Eis))(hL:∀i∈I,∀P∈L i,Prime P)
    (a:σ→Ideal Eis→ℂ)(j:Ideal Eis)(hj0:j≠0)
    (hP:∀q∈I.pi L,Admissible (j*survivingProduct I q))
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=>q i.val i.property)))
    (η:Ideal Eis→*ℂ)(u:Eis)(Z r z G:ℝ)(hZ:0<Z)(ell lo hi:σ→ℝ)
    (hell:∑i∈I,ell i=z-G)(jlo jhi:ℝ)
    (hj:((j.absNorm:ℝ)/Z^G)∈Set.Icc jlo jhi)
    (ha:∀i∈I,∀q∈L i,a i q≠0→slotRatio Z ell i q∈Set.Icc (lo i) (hi i))
    (hFresh:∀(v:σ→ℝ)(yj yc:ℝ),(∀i∈I,v i∈Set.Icc (lo i) (hi i))→
      yj∈Set.Icc jlo jhi→0<yc→W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1)
    (F:Finset (Ideal Eis))(hF:∀c∈F,Admissible c)
    (hsub:tupleColumns (originalSource Z r b₀) (I.pi L)
      (fun q:∀i∈I,Ideal Eis=>j*survivingProduct I q) j⊆F) :
    let S := originalSource Z r b₀
    let P := fun q:∀i∈I,Ideal Eis=>j*survivingProduct I q
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    (∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
      residualNormalizedPolynomial S (P q) j η (fun _=>1) W Z r z G u)=
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW)
        (Real.log ((j.absNorm:ℝ)/Z^G)) t*
        (((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
          (poolPrimary F) (poolPrimary_good F hF) Finset.univ
          (elementCharacter η) (primaryGenerator j) 1 1
          (initialTest (poolPrimary F)
            (primeMark I (fun i=>poolList F (L i))
              (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))))
            (childLogTest wFresh t) Z (r+z-2*G)) u) := by
  intro S P
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have hjpos : 0<(j.absNorm:ℝ)/Z^G := by
    apply div_pos _ (Real.rpow_pos_of_pos hZ G)
    exact_mod_cast Nat.pos_of_ne_zero (fun h=>hj0 (Ideal.absNorm_eq_zero_iff.mp h))
  let g := CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW
  let H : Finset (primePool F)→ℝ→ℂ := fun A t=>density g (Real.log ((j.absNorm:ℝ)/Z^G)) t*
    (primeMark I (fun i=>poolList F (L i))
      (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A*
      childLogTest wFresh t (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)))
  have hHi (A:Finset (primePool F)) : Integrable (H A) := by
    have hh := (common_profile_integrable g F I L a Z ell A
      ((j.absNorm:ℝ)/Z^G) (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G))).const_mul
      (wFresh (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)))
    convert hh using 1
    funext t
    dsimp [H,childLogTest]
    ring
  have hpoint (A:Finset (primePool F)) :
      (∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
        (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
          (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0))=∫t:ℝ,H A t := by
    dsimp only [P]
    simp_rw [actual_residual_product I _ j hj0,original_residual_window I _ j hj0 ell W Z r z G hZ hell]
    apply original_profile_point W wFresh a₀ b₀ ha₀ hs hW F I L hL a hcop Z hZ ell lo hi jlo jhi ha hFresh A
      ((j.absNorm:ℝ)/Z^G) (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) hj hjpos
    apply div_pos _ (Real.rpow_pos_of_pos hZ _)
    exact_mod_cast Nat.pos_of_ne_zero (fun h=>(InitialMeanSquare.poolProduct_admissible F hF A).1
      (Ideal.absNorm_eq_zero_iff.mp h))
  rw [original_tuples_large_input W Z r z G b₀ hZ (fun x hx=>(hs hx).2)
    (I.pi L) P j hP (fun q _=>dvd_mul_right j _) F hF hsub η (fun q=>∏i∈I.attach,a i.val (q i.val i.property)) u]
  change ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
    (poolPrimary F) (poolPrimary_good F hF) Finset.univ
    (elementCharacter η) (primaryGenerator j) 1 1
    (fun A=>∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
      (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
        (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) u = _
  rw [show (fun A:Finset (primePool F)=>∑q∈I.pi L,
    (∏i∈I.attach,a i.val (q i.val i.property))*
      (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
        (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) = (fun A=>∫t:ℝ,H A t)
    from funext hpoint]
  rw [input_integral (poolPrimary F) (poolPrimary_good F hF) Finset.univ
    (elementCharacter η) (primaryGenerator j) u H (fun A _=>hHi A),←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  dsimp only [H]
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF),
    initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  simp only [Finset.mul_sum,initialTest,InitialMeanSquare.poolPrimary_norm F hF]
  apply Finset.sum_congr rfl
  intro A hA
  ring

end SevenEighths.InverseInitialLargeFourier

end

end OAI
end OAIOriginalModule2139

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialCompletePool
Source SHA256: a142f316fc490c7319eb4a0272e367e80f774b3cba70b8a257262af8122febf5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2140



namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialCompletePool
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialLargePool
open InverseInitialCommonTuples InverseInitialEnergyCallerWindow
local notation "Eis"=>ActualEisensteinCubic.O

private theorem bad_prime (P:Ideal Eis)(hP:P∈fixedBadPrimes) : Prime P := by
  rcases Finset.mem_insert.mp hP with hP|hP
  · subst P
    exact Ideal.prime_of_isPrime
      (Ideal.span_singleton_eq_bot.not.mpr PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero)
      lambdaIdeal_maximal.isPrime
  · have he := Finset.mem_singleton.mp hP
    subst P
    exact Ideal.prime_of_isPrime
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (2:Eis)≠0))
      twoIdeal_maximal.isPrime

theorem admissible_mem_complete {I:Ideal Eis}(hI:Admissible I)(D:ℕ)
    (hD:I.absNorm≤D) : I∈InitialMeanSquare.outsideSquarefreeIdeals fixedBadPrimes D := by
  apply Finset.mem_filter.mpr
  refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,hD,?_⟩,hI.2.1⟩
  · exact Nat.one_le_iff_ne_zero.mpr (fun h=>hI.1 (Ideal.absNorm_eq_zero_iff.mp h))
  · intro P hP hPI
    have hp := bad_prime P hP
    let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hfac := (mem_normalizedFactors_iff hI.1).mpr ⟨hp,hPI⟩
    exact (prime_good_iff_not_bad P).mp (hI.2.2 P hfac) hP

theorem original_column_norm_bound (S:Finset (Ideal Eis)){P j c:Ideal Eis}
    (hP:Admissible P)(hj:j∣P)(hc:c∈columns S P j) :
    c.absNorm≤S.sup Ideal.absNorm*P.absNorm := by
  obtain ⟨hcs,hcj,hres,hnS⟩ := (mem_columns hP.2.1 hj).mp hc
  have hn := norm_reconstruct hres
  have hj0 := (admissible_of_dvd hP hj).1
  have hjpos : 1≤j.absNorm := Nat.one_le_iff_ne_zero.mpr
    (fun h=>hj0 (Ideal.absNorm_eq_zero_iff.mp h))
  have hnn : (reconstruct P j c).absNorm≤S.sup Ideal.absNorm := Finset.le_sup hnS
  have hPN : (residual P j).absNorm≤P.absNorm := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (fun h=>hP.1 (Ideal.absNorm_eq_zero_iff.mp h)))
    (map_dvd Ideal.absNorm (idealQuotient_dvd hj))
  calc
    c.absNorm≤j.absNorm*c.absNorm := Nat.le_mul_of_pos_left _ hjpos
    _=(reconstruct P j c).absNorm*(residual P j).absNorm := hn.symm
    _≤_ := Nat.mul_le_mul hnn hPN

theorem exists_complete_pool {κ:Type*}(S:Finset (Ideal Eis))(T:Finset κ)
    (P:κ→Ideal Eis)(j:Ideal Eis)(hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (hS:∀n∈S,Squarefree n→Supported n)(bmax Xmax:ℝ)(hb:0≤bmax)(_hX:0≤Xmax) :
    ∃D:ℕ,tupleColumns S T P j⊆InitialMeanSquare.outsideSquarefreeIdeals fixedBadPrimes D ∧
      ∀b X:ℝ,0≤b→b≤bmax→0≤X→X≤Xmax→b*X≤(D:ℝ) := by
  let D := max (S.sup Ideal.absNorm*T.sup (fun k=>(P k).absNorm)) ⌈bmax*Xmax⌉₊
  refine ⟨D,?_,?_⟩
  · intro c hc
    obtain ⟨k,hk,hc⟩ := Finset.mem_biUnion.mp hc
    apply admissible_mem_complete (columns_admissible S (hP k hk) (hj k hk) hS hc)
    exact (original_column_norm_bound S (hP k hk) (hj k hk) hc).trans
      ((Nat.mul_le_mul_left (S.sup Ideal.absNorm)
        (Finset.le_sup (f:=fun k=>(P k).absNorm) hk)).trans (le_max_left _ _))
  · intro b X hb0 hbb hX0 hXX
    apply (mul_le_mul hbb hXX hX0 hb).trans
    exact (Nat.le_ceil (bmax*Xmax)).trans (by exact_mod_cast (le_max_right
      (S.sup Ideal.absNorm*T.sup (fun k=>(P k).absNorm)) ⌈bmax*Xmax⌉₊))

end SevenEighths.InverseInitialCompletePool

end

end OAI
end OAIOriginalModule2140

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialExcludedPool
Source SHA256: fbad197169150c4d213d48315a2ad6b33dd319f4341a03b98b1014e1b25a3a3f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2141



namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialExcludedPool
open InverseInitialOverlap InverseInitialCommonTuples InverseInitialCompletePool InverseInitialPoissonBridge
local notation "O"=>ActualEisensteinCubic.O

def outside (E:Finset (Ideal O))(I:Ideal O):Prop:=∀P∈E,¬P∣I

def originalOutside (A E:Finset (Ideal O)):Finset (Ideal O):=A.filter (outside E)

theorem column_outside (A E:Finset (Ideal O)){P j c:Ideal O}
    (hE:∀Q∈E,Prime Q)(hj:j∣P)(hP:outside E P)
    (hA:∀n∈A,outside E n)(hc:c∈columns A P j):outside E c := by
  obtain ⟨n,hn,rfl⟩:=Finset.mem_image.mp hc
  obtain ⟨hnA,hns,hg⟩:=mem_original.mp hn
  have hjn:j∣n:=hg ▸ GCDMonoid.gcd_dvd_left n P
  intro Q hQ hd
  rcases (hE Q hQ).dvd_mul.mp hd with hn|hpr
  · exact hA n hnA Q hQ (hn.trans (idealQuotient_dvd hjn))
  · exact hP Q hQ (hpr.trans (idealQuotient_dvd hj))

theorem admissible_mem_excluded_complete (E:Finset (Ideal O)){I:Ideal O}
    (hI:Admissible I)(hout:outside E I)(D:ℕ)(hD:I.absNorm≤D):
    I∈InitialMeanSquare.outsideSquarefreeIdeals E D := by
  apply Finset.mem_filter.mpr
  refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,hD,hout⟩,hI.2.1⟩
  exact Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)

theorem exists_excluded_complete_pool {κ:Type*}(A E:Finset (Ideal O))(T:Finset κ)
    (P:κ→Ideal O)(j:Ideal O)(hE:∀Q∈E,Prime Q)
    (hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (hPE:∀k∈T,outside E (P k))
    (hA:∀n∈A,Squarefree n→Supported n)(bmax Xmax:ℝ)(hb:0≤bmax)(_hX:0≤Xmax):
    ∃D:ℕ,tupleColumns (originalOutside A E) T P j⊆
      InitialMeanSquare.outsideSquarefreeIdeals E D ∧
      ∀b X:ℝ,0≤b→b≤bmax→0≤X→X≤Xmax→b*X≤(D:ℝ) := by
  let D:=max (A.sup Ideal.absNorm*T.sup (fun k=>(P k).absNorm)) ⌈bmax*Xmax⌉₊
  refine ⟨D,?_,?_⟩
  · intro c hc
    obtain ⟨k,hk,hc⟩:=Finset.mem_biUnion.mp hc
    have hcA:c∈columns A (P k) j:=by
      obtain ⟨n,hn,he⟩:=Finset.mem_image.mp hc
      refine Finset.mem_image.mpr ⟨n,?_,he⟩
      obtain ⟨hnA,hns,hg⟩:=mem_original.mp hn
      exact mem_original.mpr ⟨(Finset.mem_filter.mp hnA).1,hns,hg⟩
    apply admissible_mem_excluded_complete E
      (columns_admissible A (hP k hk) (hj k hk) hA hcA)
      (column_outside _ E hE (hj k hk) (hPE k hk)
        (fun n hn=>(Finset.mem_filter.mp hn).2) hc)
    exact (original_column_norm_bound A (hP k hk) (hj k hk) hcA).trans
      ((Nat.mul_le_mul_left (A.sup Ideal.absNorm)
        (Finset.le_sup (f:=fun k=>(P k).absNorm) hk)).trans (le_max_left _ _))
  · intro b X hb0 hbb hX0 hXX
    apply (mul_le_mul hbb hXX hX0 hb).trans
    exact (Nat.le_ceil (bmax*Xmax)).trans (by exact_mod_cast (le_max_right
      (A.sup Ideal.absNorm*T.sup (fun k=>(P k).absNorm)) ⌈bmax*Xmax⌉₊))

end SevenEighths.InverseInitialExcludedPool

end

end OAI
end OAIOriginalModule2141

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialExcludedOverlap
Source SHA256: d425248d8dba5dbce1171b79c2a954fdfc0ed6964193ae7d3263dc3375522984
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2142


namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialExcludedOverlap
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialExcludedPool
open HeckeFamily InverseInitialExcludedPolynomial
local notation "O"=>ActualEisensteinCubic.O

theorem reconstruct_outside (E:Finset (Ideal O)){P j c:Ideal O}
    (hE:∀Q∈E,Prime Q)(hj:j∣P)(hP:outside E P)(hc:outside E c)
    (hres:residual P j∣c):outside E (reconstruct P j c) := by
  intro Q hQ hQn
  rcases (hE Q hQ).dvd_mul.mp hQn with hQj|hQc
  · exact hP Q hQ (hQj.trans hj)
  · exact hc Q hQ (hQc.trans (idealQuotient_dvd hres))

theorem columns_filter (A E:Finset (Ideal O)){P j:Ideal O}
    (hE:∀Q∈E,Prime Q)(hPs:Squarefree P)(hj:j∣P)(hP:outside E P):
    columns (originalOutside A E) P j=(columns A P j).filter (outside E) := by
  ext c
  constructor
  · intro hc
    have hd:=(mem_columns hPs hj).mp hc
    apply Finset.mem_filter.mpr
    refine ⟨(mem_columns hPs hj).mpr ⟨hd.1,hd.2.1,hd.2.2.1,?_⟩,?_⟩
    · exact (Finset.mem_filter.mp hd.2.2.2).1
    · exact column_outside _ E hE hj hP (fun n hn=>(Finset.mem_filter.mp hn).2) hc
  · intro hc
    obtain ⟨hcA,hout⟩:=Finset.mem_filter.mp hc
    obtain ⟨hcs,hcj,hres,hnA⟩:=(mem_columns hPs hj).mp hcA
    exact (mem_columns hPs hj).mpr ⟨hcs,hcj,hres,
      Finset.mem_filter.mpr ⟨hnA,reconstruct_outside E hE hj hP hout hres⟩⟩

theorem deleted_zero_outside (χ:Character)(E:Finset (Ideal O))
    (hE:∀Q∈E,Prime Q)(I:Ideal O)(hn:¬outside E I):
    idealCoeff (χ.excludePrimes E hE) I=0 := by
  rw [idealCoeff_excludePrimes]
  apply ite_eq_right
  intro hc
  apply hn
  intro Q hQ hd
  have hu:IsUnit Q:=(hc Q hQ).isRelPrime hd (dvd_refl Q)
  exact (hE Q hQ).not_isUnit hu

theorem residual_filtered (A E:Finset (Ideal O)){P j:Ideal O}
    (hE:∀Q∈E,Prime Q)(hPs:Squarefree P)(hj:j∣P)(hP:outside E P)
    (η:Ideal O→*ℂ)(hη:∀I,¬outside E I→η I=0)
    (a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z G:ℝ)(u:O):
    residualNormalizedPolynomial A P j η a W Z r z G u=
    residualNormalizedPolynomial (originalOutside A E) P j η a W Z r z G u := by
  unfold residualNormalizedPolynomial
  rw [columns_filter A E hE hPs hj hP,Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hout:outside E c
  · rw [ite_eq_left hout]
  · rw [ite_eq_right hout]
    simp only [overlapResidualCoefficient,hη c hout,mul_zero,zero_mul]

theorem residual_deleted_filtered (χ:Character)(A E:Finset (Ideal O)){P j:Ideal O}
    (hE:∀Q∈E,Prime Q)(hPs:Squarefree P)(hj:j∣P)(hP:outside E P)
    (a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z G:ℝ)(u:O):
    residualNormalizedPolynomial A P j (idealCoeff (χ.excludePrimes E hE)).toMonoidHom a W Z r z G u=
    residualNormalizedPolynomial (originalOutside A E) P j
      (idealCoeff (χ.excludePrimes E hE)).toMonoidHom a W Z r z G u :=
  residual_filtered A E hE hPs hj hP _ (deleted_zero_outside χ E hE) a W Z r z G u

end SevenEighths.InverseInitialExcludedOverlap

end

end OAI
end OAIOriginalModule2142

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialExcludedForcing
Source SHA256: 467b525fe91f52766ca6e18d01871ad5c1e5f827d43897d764f9c68a14d3fadd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2143


namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open FirstCauchyArithmetic SecondPassArithmetic UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialExcludedForcing
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialRayAttachment InverseInitialArithmetic InverseInitialCommonPool
open InverseInitialEnergyCallerWindow InverseInitialCommonForcing InverseInitialLargePool
open InverseInitialExcludedPool InverseInitialExcludedOverlap
open InverseInitialCommonTuples InverseInitialCommonTransform
local notation "O"=>ActualEisensteinCubic.O

theorem pool_product_outside (F E:Finset (Ideal O))(hE:∀Q∈E,Prime Q)
    (hF:∀I∈F,outside E I)(A:Finset (primePool F)):
    outside E (∏i∈A,i.val) := by
  intro Q hQ hd
  obtain ⟨i,hi,hQi⟩:=((hE Q hQ).dvd_finsetProd_iff (fun i:primePool F=>i.val)).mp hd
  obtain ⟨I,hIF,hfactor⟩:=mem_primePool_iff.mp i.property
  exact hF I hIF Q hQ (hQi.trans (dvd_of_mem_normalizedFactors hfactor))

theorem residual_excluded_forcing
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    (E:Finset (Ideal O))(hE:∀Q∈E,Prime Q)
    {P j:Ideal O}(hP:Admissible P)(hj:j∣P)(hPE:outside E P)
    (F:Finset (Ideal O))(hF:∀I∈F,Admissible I)(hFE:∀I∈F,outside E I)
    (hsub:columns (originalOutside (originalSource Z r b) E) P j⊆F)
    (η:Ideal O→*ℂ)(hη:∀I,¬outside E I→η I=0)(u:O):
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    residualNormalizedPolynomial (originalSource Z r b) P j η (fun _=>1) W Z r z G u=
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>if residual P j∣(∏i∈A,i.val) then
          residualOverlapWindow P j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0) u := by
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  rw [residual_filtered _ E hE hP.2.1 hj hPE η hη,
    residual_eq_large_input _ F hP hj hF hsub η (fun _=>1) W Z r z G u]
  simp only [one_mul]
  apply congrArg (fun v:ℂ=>((Z^(-(r+z-2*G)/2):ℝ):ℂ)*v)
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF),
    initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  have he:=common_selector_window W Z r z G b hZ hW hP hj F hF A
  have hm:rowCoprimeMask (fun i:primePool F=>Ideal.span {poolPrimary F i}) A
      (primaryGenerator j)=rowCoprimeMask (fun i:primePool F=>i.val) A (primaryGenerator j):=by
    congr 1
    funext i
    exact poolPrimary_span F hF i
  have hmem:((∏i∈A,i.val)∈columns (originalOutside (originalSource Z r b) E) P j)↔
      ((∏i∈A,i.val)∈columns (originalSource Z r b) P j):=by
    rw [columns_filter _ E hE hP.2.1 hj hPE,Finset.mem_filter]
    exact and_iff_left (pool_product_outside F E hE hFE A)
  dsimp only
  simp only [hm,hmem]
  linear_combination
    (supportMobius (fun i:primePool F=>Ideal.span {poolPrimary F i}) A *
      elementCharacter η (∏i∈A,poolPrimary F i) *
      star (finiteSquarefreeRow (fun i:primePool F=>Ideal.span {poolPrimary F i})
        (poolPrimary_good F hF) A u))*he

variable {κ:Type*}
theorem original_tuples_excluded_input
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    (E:Finset (Ideal O))(hE:∀Q∈E,Prime Q)
    (T:Finset κ)(P:κ→Ideal O)(j:Ideal O)
    (hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (hPE:∀k∈T,outside E (P k))
    (F:Finset (Ideal O))(hF:∀I∈F,Admissible I)(hFE:∀I∈F,outside E I)
    (hsub:tupleColumns (originalOutside (originalSource Z r b) E) T P j⊆F)
    (η:Ideal O→*ℂ)(hη:∀I,¬outside E I→η I=0)(a:κ→ℂ)(u:O) :
    let S := originalSource Z r b
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    (∑k∈T,a k*residualNormalizedPolynomial S (P k) j η (fun _=>1) W Z r z G u)=
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>∑k∈T,a k*(if residual (P k) j∣(∏i∈A,i.val) then
          residualOverlapWindow (P k) j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) u := by
  intro S
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  rw [input_finset_sum (poolPrimary F) (poolPrimary_good F hF)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [residual_excluded_forcing W Z r z G b hZ hW E hE (hP k hk) (hj k hk) (hPE k hk) F hF hFE
    (fun c hc=>hsub (Finset.mem_biUnion.mpr ⟨k,hk,hc⟩)) η hη u]
  ring

end SevenEighths.InverseInitialExcludedForcing

end

end OAI
end OAIOriginalModule2143

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialExcludedFourier
Source SHA256: 989f63e9d0f99ae54f71ef76f66d8044510787920c531fe385f1bea6439ecf0e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2144


namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open ConcretePrimeRowBridge FirstCauchyArithmetic SecondPassArithmetic FirstPassCubeLabels
namespace SevenEighths.InverseInitialExcludedFourier
open InverseMoment InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonProfile
open InverseInitialCommonCutoff InverseInitialCommonTuples InverseInitialOverlapFourier
open InverseInitialOverlapInputFourier InverseInitialRayAttachment InverseInitialArithmetic
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialEnergyCallerWindow
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

open InverseInitialCommonTransform InverseInitialLargePool
open InverseInitialExcludedPool InverseInitialExcludedForcing
theorem original_tuples_excluded_fourier
    (W wFresh:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (E:Finset (Ideal Eis))(hE:∀Q∈E,Prime Q)
    (I:Finset σ)(L:σ→Finset (Ideal Eis))(hL:∀i∈I,∀P∈L i,Prime P)
    (a:σ→Ideal Eis→ℂ)(j:Ideal Eis)(hj0:j≠0)
    (hP:∀q∈I.pi L,Admissible (j*survivingProduct I q))
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=>q i.val i.property)))
    (hPE:∀q∈I.pi L,outside E (j*survivingProduct I q))
    (η:Ideal Eis→*ℂ)(hη:∀c,¬outside E c→η c=0)(u:Eis)(Z r z G:ℝ)(hZ:0<Z)(ell lo hi:σ→ℝ)
    (hell:∑i∈I,ell i=z-G)(jlo jhi:ℝ)
    (hj:((j.absNorm:ℝ)/Z^G)∈Set.Icc jlo jhi)
    (ha:∀i∈I,∀q∈L i,a i q≠0→slotRatio Z ell i q∈Set.Icc (lo i) (hi i))
    (hFresh:∀(v:σ→ℝ)(yj yc:ℝ),(∀i∈I,v i∈Set.Icc (lo i) (hi i))→
      yj∈Set.Icc jlo jhi→0<yc→W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1)
    (F:Finset (Ideal Eis))(hF:∀c∈F,Admissible c)(hFE:∀c∈F,outside E c)
    (hsub:tupleColumns (originalOutside (originalSource Z r b₀) E) (I.pi L)
      (fun q:∀i∈I,Ideal Eis=>j*survivingProduct I q) j⊆F) :
    let S := originalSource Z r b₀
    let P := fun q:∀i∈I,Ideal Eis=>j*survivingProduct I q
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    (∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
      residualNormalizedPolynomial S (P q) j η (fun _=>1) W Z r z G u)=
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW)
        (Real.log ((j.absNorm:ℝ)/Z^G)) t*
        (((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
          (poolPrimary F) (poolPrimary_good F hF) Finset.univ
          (elementCharacter η) (primaryGenerator j) 1 1
          (initialTest (poolPrimary F)
            (primeMark I (fun i=>poolList F (L i))
              (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))))
            (childLogTest wFresh t) Z (r+z-2*G)) u) := by
  intro S P
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have hjpos : 0<(j.absNorm:ℝ)/Z^G := by
    apply div_pos _ (Real.rpow_pos_of_pos hZ G)
    exact_mod_cast Nat.pos_of_ne_zero (fun h=>hj0 (Ideal.absNorm_eq_zero_iff.mp h))
  let g := CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW
  let H : Finset (primePool F)→ℝ→ℂ := fun A t=>density g (Real.log ((j.absNorm:ℝ)/Z^G)) t*
    (primeMark I (fun i=>poolList F (L i))
      (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A*
      childLogTest wFresh t (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)))
  have hHi (A:Finset (primePool F)) : Integrable (H A) := by
    have hh := (common_profile_integrable g F I L a Z ell A
      ((j.absNorm:ℝ)/Z^G) (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G))).const_mul
      (wFresh (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)))
    convert hh using 1
    funext t
    dsimp [H,childLogTest]
    ring
  have hpoint (A:Finset (primePool F)) :
      (∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
        (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
          (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0))=∫t:ℝ,H A t := by
    dsimp only [P]
    simp_rw [actual_residual_product I _ j hj0,original_residual_window I _ j hj0 ell W Z r z G hZ hell]
    apply original_profile_point W wFresh a₀ b₀ ha₀ hs hW F I L hL a hcop Z hZ ell lo hi jlo jhi ha hFresh A
      ((j.absNorm:ℝ)/Z^G) (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) hj hjpos
    apply div_pos _ (Real.rpow_pos_of_pos hZ _)
    exact_mod_cast Nat.pos_of_ne_zero (fun h=>(InitialMeanSquare.poolProduct_admissible F hF A).1
      (Ideal.absNorm_eq_zero_iff.mp h))
  rw [original_tuples_excluded_input W Z r z G b₀ hZ (fun x hx=>(hs hx).2) E hE
    (I.pi L) P j hP (fun q _=>dvd_mul_right j _) hPE F hF hFE hsub η hη (fun q=>∏i∈I.attach,a i.val (q i.val i.property)) u]
  change ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
    (poolPrimary F) (poolPrimary_good F hF) Finset.univ
    (elementCharacter η) (primaryGenerator j) 1 1
    (fun A=>∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
      (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
        (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) u = _
  rw [show (fun A:Finset (primePool F)=>∑q∈I.pi L,
    (∏i∈I.attach,a i.val (q i.val i.property))*
      (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
        (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) = (fun A=>∫t:ℝ,H A t)
    from funext hpoint]
  rw [input_integral (poolPrimary F) (poolPrimary_good F hF) Finset.univ
    (elementCharacter η) (primaryGenerator j) u H (fun A _=>hHi A),←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  dsimp only [H]
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF),
    initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  simp only [Finset.mul_sum,initialTest,InitialMeanSquare.poolPrimary_norm F hF]
  apply Finset.sum_congr rfl
  intro A hA
  ring

end SevenEighths.InverseInitialExcludedFourier

end

end OAI
end OAIOriginalModule2144

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialResidualPool
Source SHA256: ff3226c303060df6da85c90eecb93c30d5cb398f288c1e26f0e7b4d549c79d4d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2145



namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialResidualPool
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
open InverseInitialExcludedPool InverseInitialCommonTuples InverseInitialEnergyCallerWindow
local notation "O"=>ActualEisensteinCubic.O

theorem exists_original_complete_pool {κ:Type*}
    (q:ℕ)(Z r b cap Btree:ℝ)(hZ:0<Z)(hBtree:0≤Btree)
    (T:Finset κ)(P:κ→Ideal O)(j:Ideal O)
    (hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (hPE:∀k∈T,outside (reflectionExcludedPrimes q) (P k)):
    ∃Dpool:ℕ,Btree*Z^(cap+1)≤Dpool ∧
      tupleColumns (originalOutside (originalSource Z r b) (reflectionExcludedPrimes q)) T P j⊆
        InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool:=by
  obtain ⟨D,hcover,hsize⟩:=exists_excluded_complete_pool (originalSource Z r b)
    (reflectionExcludedPrimes q) T P j (reflectionExcludedPrimes_prime q) hP hj hPE
    (originalSource_supported Z r b) Btree (Z^(cap+1)) hBtree (Real.rpow_nonneg hZ.le _)
  exact ⟨D,hsize Btree (Z^(cap+1)) hBtree le_rfl (Real.rpow_nonneg hZ.le _) le_rfl,hcover⟩

end SevenEighths.InverseInitialResidualPool

end

end OAI
end OAIOriginalModule2145

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialResidualTupleEnergy
Source SHA256: f3ac466186ec68b827c4050f80c02589a0fa30f63538086c606d84197a836b5b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2146




namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialResidualTupleEnergy
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=>ActualEisensteinCubic.O

open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment
open MeasureTheory FourierBridge JointLogSeparation InverseInitialOverlapFourier
open InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonTuples
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialExcludedPool
open InverseInitialCommonProfile InverseInitialEnergyCallerWindow
theorem original_residual_tuple_energy
    (Woriginal W:ℝ→ℂ)(ao bo:ℝ)(hao:0<ao)
    (hso:Function.support Woriginal⊆Set.Icc ao bo)(hWo:ContDiff ℝ ∞ Woriginal)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (hW:ContDiff ℝ ∞ W)(Φ:𝓢(ℝ,ℂ))
    (hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (B₀:ℝ)(hB₀:0≤B₀)(hb:∀x,‖W x‖≤B₀)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let _p:=poolPrimary F;
    let _hp:=poolPrimary_ne_zero F hF;
    let _hcop:=poolPrimary_coprime F hF;
    let _hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(L:σ→Finset (Ideal O))(Hslot:σ→ℝ)(coeff:σ→Ideal O→ℂ),
      (all:Set σ).PairwiseDisjoint L→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈L i,(P.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈L i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀χ:Ideal O→*ℂ,(∀u,‖elementCharacter χ u‖≤1)→
      FactorsModulo (fixedBaseConductor q) (elementCharacter χ)→
      (∀c,¬outside (reflectionExcludedPrimes q) c→χ c=0)→
    ∀(D m r:ℝ),0≤m→m≤cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤cap→
    ∀(rows:Finset O),(∀u∈rows,‖eisEmbedding u‖^2≤Z^m)→
    ∀(j:Ideal O),Admissible j→Ideal.span {assignedElement assigned qelem}=j→
    ∀(lo hi:σ→ℝ)(jlo jhi:ℝ),
      ((j.absNorm:ℝ)/Z^(assignedCenter assigned z))∈Set.Icc jlo jhi→
      (∀i∈all\assigned,∀P∈L i,Prime P)→
      (∀i∈all\assigned,∀P∈L i,coeff i P≠0→slotRatio Z z i P∈Set.Icc (lo i) (hi i))→
      (∀v:σ→ℝ,∀yj yc:ℝ,(∀i∈all\assigned,v i∈Set.Icc (lo i) (hi i))→
        yj∈Set.Icc jlo jhi→0<yc→Woriginal (yj*yc/(∏i∈all\assigned,v i))≠0→W yc=1)→
      (∀t∈(all\assigned).pi L,Admissible (j*survivingProduct (all\assigned) t))→
      (∀t∈(all\assigned).pi L,Pairwise (Function.onFun IsCoprime
        (fun i:↥(all\assigned)=>t i.val i.property)))→
      (∀t∈(all\assigned).pi L,outside (reflectionExcludedPrimes q)
        (j*survivingProduct (all\assigned) t))→
      tupleColumns (originalOutside (originalSource Z r bo) (reflectionExcludedPrimes q))
        ((all\assigned).pi L) (fun t=>j*survivingProduct (all\assigned) t) j⊆F→
    ∀θ:ℝ,
      (∑u∈rows,‖∑t∈(all\assigned).pi L,
        (∏i∈(all\assigned).attach,coeff i.val (t i.val i.property))*
        residualNormalizedPolynomial (originalSource Z r bo)
          (j*survivingProduct (all\assigned) t) j χ (fun _=>1)
          (childLogTest Woriginal θ) Z r (assignedCenter all z) (assignedCenter assigned z) u‖^2)≤
        C*Z^(m+15*η+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨J,Btree,hBtree,henergy⟩:=InverseInitialTotalFourier.original_fourier_energy_bound
    (CubicReflectionKernel.logSchwartz Woriginal ao bo hao hso hWo)
    W a₀ b₀ bcap ha₀ hbcap hs hW Φ hΦ hone B₀ hB₀ hb
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  refine ⟨J,Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,henergy⟩:=henergy q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK L Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive χ hχ hperiod hout
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows
    j hj hspan lo hi jlo jhi hjratio hL hcoeff hFresh hP hcopTuple hPE hsub θ
  have hZp:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hdisPool:(all:Set σ).PairwiseDisjoint (fun i=>poolList F (L i)):=by
    intro i hi k hk hik
    apply Finset.disjoint_left.mpr
    intro P hPi hPk
    exact (Finset.disjoint_left.mp (hdis hi hk hik))
      (Finset.mem_filter.mp hPi).2 (Finset.mem_filter.mp hPk).2
  have he:=henergy Z hZ Dpool hD all assigned hassigned hK
    (fun i=>poolList F (L i)) Hslot (fun i P=>coeff i P.val) hdisPool hHs
    (fun i hi P hP=>hPs i hi P.val (Finset.mem_filter.mp hP).2)
    (fun i hi P hP=>hac i hi P.val (Finset.mem_filter.mp hP).2)
    qelem z al bl primeW hz hqe hprimeW hprimeLive (elementCharacter χ) hχ hperiod
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows
    (fun i P=>Real.log (slotRatio Z z i P.val)) (Real.log ((j.absNorm:ℝ)/Z^(assignedCenter assigned z))) θ
  have hsum:∑i∈all\assigned,z i=assignedCenter all z-assignedCenter assigned z:=by
    have hh:=Finset.sum_sdiff (f:=z) hassigned
    dsimp [assignedCenter]
    linarith
  have hgj:Ideal.span {primaryGenerator j}=Ideal.span {assignedElement assigned qelem}:=
    (primaryGenerator_spec j (primaryGenerator_admissible j hj)).1.trans hspan.symm
  have hid (u:O):
      (∑t∈(all\assigned).pi L,(∏i∈(all\assigned).attach,coeff i.val (t i.val i.property))*
        residualNormalizedPolynomial (originalSource Z r bo)
          (j*survivingProduct (all\assigned) t) j χ (fun _=>1)
          (childLogTest Woriginal θ) Z r (assignedCenter all z) (assignedCenter assigned z) u)=
      ∫t:ℝ,density (frequencyTwist (CubicReflectionKernel.logSchwartz Woriginal ao bo hao hso hWo) θ)
