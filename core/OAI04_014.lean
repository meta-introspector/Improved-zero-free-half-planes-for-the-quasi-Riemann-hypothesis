

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
local notation "O"=>ActualEisensteinCubic.O

def priorityCellScalar (Z Y L X ell Ractive j t eta eps epsmass B:ℝ) (ray:ℂ) (d:BlockIndex):ℝ :=
  (Real.exp (6*L)*‖(Y:ℂ)*ray*((scales d 1*scales d 2*Z^(secondCellColumnExponent Z X d):ℝ):ℂ)⁻¹‖)*
    Z^((secondCount ell Ractive j t (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)*(1+epsmass))*
    Z^(2*(max 0 (secondCellColumnExponent Z X d)+
      (secondFormalLabel B (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta))+eps)

theorem source_cell_joint_bound {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn)) (hk:∀x∈source,x.second.frequency≠0)
    (b X:ℝ) (hgeom:∀x∈source,primeProductNorm p x.second.sourceCommon*
      primeProductNorm p x.second.overlap≤b*X) (d:BlockIndex) (hd:d∈keys p source):
    scales d 0*scales d 2≤b*X := by
  obtain ⟨x,hx⟩:=(mem_keys_iff p source d).mp hd
  have h0:scales d 0≤primeProductNorm p x.second.sourceCommon:=by
    simpa [outerNorms,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 0).1
  have h2:scales d 2≤primeProductNorm p x.second.overlap:=by
    simpa [outerNorms,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 2).1
  exact (mul_le_mul h0 h2 (dyadScale_pos _).le (primeProductNorm_pos p hp _).le).trans
    (hgeom x (cell_subset p source d hx))

theorem priority_source_scalar_budget (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) :
    ∃ Cbin:ℝ,0≤Cbin ∧ ∀ {ι:Type*} [DecidableEq ι]
    (p:ι→O) (_hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn))
    (Z M r ell V delta A B Ractive j t eta tau pi eps epsmass b C:ℝ)
    (ray:ℂ), 2≤Z → 0≤C → 1≤b → b≤Z^(6*eta) →
    (∀x∈source,x.second.frequency≠0) →
    (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
    (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*Z^(r-A-B-t)) →
    (∀d∈keys p source,epsmass*(secondCount ell Ractive j t (secondCellExponent Z d 0)
      (secondCellExponent Z d 1)+11*eta/2)≤pi) →
    C*Z^(firstKappa M r ell V delta A B Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))*
      (∑d∈keys p source,priorityCellScalar Z (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau))
        (eta*Real.log Z) (Z^(r-A-B-t)) ell Ractive j t eta eps epsmass B ray d) ≤
    C*‖ray‖*(1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+eps) := by
  refine ⟨capConstant caps,capConstant_nonneg caps hcaps,?_⟩
  intro ι _ p hp _ Jo Jn source Z M r ell V delta A B Ractive j t eta tau pi eps epsmass b C
    ray hZ hC hb hthreshold hk hnorm hgeom hmass
  have hZ':1<Z:=lt_of_lt_of_le (by norm_num) hZ
  have hz:0<Z:=zero_lt_one.trans hZ'
  have hcard:((keys p source).card:ℝ)≤(1+capConstant caps*Real.log Z)^4:=by
    have h:=keys_card_le_product p hp source hk caps Z hnorm
    have hr:((keys p source).card:ℝ)≤∏i:Fin 4,((dyadIndex (Z^(caps i)):ℝ)+1):=by exact_mod_cast h
    apply hr.trans
    calc
      _≤∏_i:Fin 4,(1+capConstant caps*Real.log Z):=
        Finset.prod_le_prod₀ (fun _ _=>by positivity) (fun i _=>cap_bin_bound caps hcaps Z hZ i)
      _= _:=by simp
  rw [Finset.mul_sum]
  calc
    _≤∑_d∈keys p source,C*‖ray‖*Z^(r+3*ell+V+48*eta+tau+pi+eps):=by
      apply Finset.sum_le_sum
      intro d hd
      have he:=priority_cell_physical_budget Z hZ' d M r ell V delta A B Ractive j t eta tau pi eps epsmass b C
        ray hC hb (source_cell_joint_bound p hp source hk b _ hgeom d hd) hthreshold (hmass d hd)
      convert he using 1 ; dsimp only [priorityCellScalar] ; ring
    _= ((keys p source).card:ℝ)*(C*‖ray‖*Z^(r+3*ell+V+48*eta+tau+pi+eps)):=by simp
    _≤ (1+capConstant caps*Real.log Z)^4*(C*‖ray‖*Z^(r+3*ell+V+48*eta+tau+pi+eps)):=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _= _:=by ring

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0748

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ActualChildState
Source SHA256: 67a07562d44da69e8137d98fbbb4ca40270a9b586781b7f423b1bf59b7801ad3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0749





namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def actualCellLabelExponent (Z B j eta : ℝ) (d : BlockIndex) : ℝ :=
  secondFormalLabel B (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta

def actualCellTotalExponent (Z X B j eta : ℝ) (d : BlockIndex) : ℝ :=
  max 0 (secondCellColumnExponent Z X d)+actualCellLabelExponent Z B j eta d

def actualCellClipping (Z X : ℝ) (d : BlockIndex) : ℝ :=
  max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d

lemma actual_cell_total_transition (Z r ell V A B t j eta : ℝ) (d : BlockIndex) (hZ : 1<Z) :
    actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d=
      childF (r+3*ell+V) ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j
        (actualCellClipping Z (Z^(r-A-B-t)) d+4*eta) := by
  unfold actualCellTotalExponent actualCellLabelExponent actualCellClipping
  rw [second_cell_formal_column Z r A B t d hZ]
  unfold childF decrease secondFormalColumn secondFormalLabel
  ring

lemma actual_cell_label_nonneg (Z B j eta : ℝ) (d : BlockIndex)
    (hZ : 1<Z) (hB : 0≤B) (hj : 0≤j) (heta : 0≤eta) :
    0≤actualCellLabelExponent Z B j eta d := by
  have h1 := secondCellExponent_nonneg Z d 1 hZ
  have h2 := secondCellExponent_nonneg Z d 2 hZ
  unfold actualCellLabelExponent secondFormalLabel
  positivity

variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
include hp

omit [DecidableEq ι] in
theorem actual_cell_norm_centers {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Z eta : ℝ) (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (i : Fin 4) :
    Z^(secondCellExponent Z d i-eta)≤outerNorms p x i ∧
      outerNorms p x i≤Z^(secondCellExponent Z d i+eta) := by
  have hr := cell_ratios p hp source hk d x hx i
  have hz : 0<Z := zero_lt_one.trans hZ
  have hlo := (le_div_iff₀ (dyadScale_pos (d i))).mp hr.1
  have hhi := (div_le_iff₀ (dyadScale_pos (d i))).mp hr.2.le
  constructor
  · apply (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith : secondCellExponent Z d i-eta≤secondCellExponent Z d i)).trans
    simpa only [second_cell_scale_rpow Z d i hZ,one_mul,scales] using hlo
  · calc
      _ ≤ 2*scales d i := hhi
      _ ≤ Z^eta*scales d i := mul_le_mul_of_nonneg_right hbin (dyadScale_pos _).le
      _ = _ := by rw [←second_cell_scale_rpow Z d i hZ,←Real.rpow_add hz];congr 1;ring

theorem actual_cell_child_margins
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (u v : Oˣ) (m : O) (hm : m≠0)
    (Z r ell V M Q z c A B t j eta : ℝ) (hZ : 1<Z)
    (hparent : CanonicalMargins (r+3*ell+V) M Q z c)
    (hA : 0≤A) (ht : 0≤t) (hV : 0≤V) (hj : 0≤j) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Q)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient:ℝ)≤Z^(t+eta)) :
    CanonicalMargins (actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d)
      (childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta)
      (actualSecondPunctureWidth Z m (actualSecondChild p u v x).1) z (c-7*eta) := by
  have hxs := cell_subset p source d hx
  have hG := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).2
  have hD := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).1
  rw [actual_cell_total_transition Z r ell V A B t j eta d hZ]
  apply actual_second_child_margins_from_cubes p hp hpr x (hs.second_divisor x hxs)
    (hs.quotient_nonzero x hxs) u v m hm Z (r+3*ell+V) M Q z c ell A t
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j _ eta hZ hparent hA ht hV hj
    (by unfold actualCellClipping;have := le_max_right 0 (secondCellColumnExponent Z (Z^(r-A-B-t)) d);linarith)
    heta hQ h1 h2 hT
  · simpa only [outerNorms,Matrix.cons_val_zero] using hG
  · simpa only [outerNorms,Matrix.cons_val_one,Matrix.cons_val_zero] using hD

theorem actual_cell_child_total_upper {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hs : ActualSecondSourceConditions p source)
    (hk : ∀x∈source,x.second.frequency≠0) (d : BlockIndex)
    (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Z r ell V A B t j eta b : ℝ) (hZ : 1<Z)
    (hA : 0≤A) (ht : 0≤t) (hell : 0≤ell) (hV : 0≤V) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hb : 1≤b) (hthreshold : b≤Z^(6*eta))
    (hgeom : ∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*Z^(r-A-B-t))
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hJ : Z^(j-eta)≤‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d≤(r+3*ell+V)+15*eta := by
  have hxs := cell_subset p source d hx
  have hG := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).2
  have hD := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).1
  have hgt := actual_second_common_center p hp x (hs.second_divisor x hxs) Z
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta hZ
    (by simpa [outerNorms] using hG) (by simpa [outerNorms] using hD)
  have hj := actual_second_label_center p hp x Z ell j eta hZ h1 h2 hJ
  have hd : d∈keys p source := (mem_keys_iff p source d).mpr ⟨x,hx⟩
  have hc := second_cell_clipping_width Z (Z^(r-A-B-t)) b eta d hZ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hb
    (source_cell_joint_bound p hp source hk b _ hgeom d hd) hthreshold
  rw [actual_cell_total_transition Z r ell V A B t j eta d hZ]
  unfold childF decrease actualCellClipping
  linarith

end SevenEighths.InverseMoment
end

end OAI
end OAIOriginalModule0749

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ActualChildStateLabels
Source SHA256: 759992e4943048668c69cee1bbdf4f18f67771c7e0bd806b49f163fdc0a2a506
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0750


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

def actualCellLabels {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) : Finset (Ideal O) :=
  (cell p source d).image (fun x=>(actualSecondChild p 1 1 x).2.1)

lemma actual_cell_labels_cover {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d) :
    (actualSecondChild p 1 1 x).2.1∈actualCellLabels p source d :=
  Finset.mem_image.mpr ⟨x,hx,rfl⟩

theorem actual_cell_labels_bound (hp : ∀i,p i≠0) {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (Z B j eta : ℝ) (hZ : 1<Z) (hbin : 2≤Z^eta)
    (hC : ∀x∈source,primeProductNorm p x.firstCommon≤Z^(B+eta))
    (hJ : ∀x∈source,‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2≤Z^(j+eta)) :
    ∀I∈actualCellLabels p source d,(Ideal.absNorm I:ℝ)≤Z^(actualCellLabelExponent Z B j eta d) := by
  intro I hI
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hI
  exact actual_cell_child_label_power p hp source hk d x hx 1 1 Z B j eta hZ hbin
    (hC x (cell_subset p source d hx)) (hJ x (cell_subset p source d hx))

theorem actual_cell_squarefree_labels (hp : ∀i,p i≠0) {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (Z B j eta : ℝ) (hZ : 1<Z) (hbin : 2≤Z^eta)
    (hC : ∀x∈source,primeProductNorm p x.firstCommon≤Z^(B+eta))
    (hJ : ∀x∈source,‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2≤Z^(j+eta)) :
    ∀I∈(actualCellLabels p source d).filter Squarefree,
      Squarefree I ∧ I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^(actualCellLabelExponent Z B j eta d) := by
  intro I hI
  have hi := Finset.mem_filter.mp hI
  exact ⟨hi.2,hi.2.ne_zero,actual_cell_labels_bound p hp source hk d Z B j eta hZ hbin hC hJ I hi.1⟩

theorem actual_cell_nonzero_weight_label (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (d : BlockIndex)
    (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Ψ : O→*ℂ) (m : O) (ray : SecondRayIndex)
    (hw : actualSecondSignedWeight p hp hcop hg Ψ m ray x≠0) :
    (actualSecondChild p 1 1 x).2.1∈(actualCellLabels p source d).filter Squarefree := by
  have hxs := cell_subset p source d hx
  exact Finset.mem_filter.mpr ⟨actual_cell_labels_cover p source d x hx,
    actual_second_nonzero_weight_squarefree p hp hcop hg Ψ m ray x
      (hs.common_disjoint x hxs) (hs.second_divisor x hxs) hw 1 1⟩

end SevenEighths.InverseMoment
end

end OAI
end OAIOriginalModule0750

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ActualChildStateSupport
Source SHA256: 7abb40fd7255bfd6527ab9d71ec684014e9dee0337d808385ea5e4419f6372ab
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0751




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
include hp

theorem actual_cell_label_support {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d) (u v : Oˣ)
    (Z B j eta : ℝ) (hZ : 1<Z) (hbin : 2≤Z^eta)
    (hC : primeProductNorm p x.firstCommon≤Z^(B+eta))
    (hJ : ‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2≤Z^(j+eta)) :
    (Ideal.absNorm (actualSecondChild p u v x).2.1:ℝ)≤Z^(actualCellLabelExponent Z B j eta d) :=
  actual_cell_child_label_power p hp source hk d x hx u v Z B j eta hZ hbin hC hJ

theorem actual_cell_correlated_row_support
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hk : ∀x∈source,x.second.frequency≠0) (d : BlockIndex)
    (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d) (u v : Oˣ)
    (Z M r ell V delta A B j t eta tau L : ℝ) (hZ : 1<Z)
    (heta : 0≤eta) (hbin : 2≤Z^eta) (hL0 : 0≤L)
    (hd : ‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)‖^2≤Z^(delta+eta))
    (hL : L≤Z^(r-A-B-t+4*eta))
    (hgate : x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (correlatedSecondRadius p (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)
        x.second.sourceCommon x.second.divisor L
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau))) :
    (actualSecondChild p u v x).2.2∈nonzeroChildFrequencyBall 1
      (Z^(childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta)) := by
  have hE := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).2
  have hG := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).1
  have hr := second_correlated_radius_childM p hp
    (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor) x.second.sourceCommon x.second.divisor
    Z M r ell V delta A B j t (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta tau L
    (zero_lt_one.trans hZ) hL0 hd (by simpa [outerNorms] using hE) (by simpa [outerNorms] using hG) hL
  apply (actual_second_row_ball p hp hpr x u v _).mp
  have hb := (mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) _ _).mp hgate
  exact (mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) _ _).mpr ⟨hb.1,hb.2.trans hr⟩

omit hp in

lemma actual_child_row_length_nonneg (Z M : ℝ) (hZ : 1<Z) (k : O)
    (hk : k∈nonzeroChildFrequencyBall 1 (Z^M)) : 0≤M := by
  have hb := (mem_nonzeroChildFrequencyBall 1 one_ne_zero (Z^M) k).mp hk
  simp only [one_mul] at hb
  have hk0 : k≠0 := (Finset.mem_erase.mp hk).1
  have hn := EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq k hk0
  have hpow : Z^(0:ℝ)≤Z^M := by simpa only [Real.rpow_zero,one_mul] using hn.trans hb.2
  exact (Real.rpow_le_rpow_left_iff hZ).mp hpow

theorem actual_cell_row_decrease {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hs : ActualSecondSourceConditions p source)
    (hk : ∀x∈source,x.second.frequency≠0) (d : BlockIndex)
    (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Z M ell A t V j eta cutoff : ℝ) (hZ : 1<Z)
    (hA : 0≤A) (ht : 0≤t) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hterminal : cutoff≤ell+V) (hsmall : eta≤cutoff/16)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hJ : Z^(j-eta)≤‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta+3*cutoff/2≤M := by
  have hG := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).2
  have hD := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).1
  have hh := actual_second_row_decrease p hp x (hs.second_divisor x (cell_subset p source d hx)) Z M ell A t
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta cutoff hZ hA ht hterminal hsmall
    (by simpa [outerNorms] using hG) (by simpa [outerNorms] using hD) h1 h2 hJ
  linarith

theorem actual_cell_triple_puncture_nonzero
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (d : BlockIndex) (m : O) (hm : m≠0)
    (γ : OuterTriple) (hγ : γ∈actualSecondTriples p 1 1 (cell p source d)) :
    actualSecondInheritedRadicalPuncture m γ≠0 := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
  exact radicalGenerator_ne_zero _ (actual_second_inherited_puncture_ne_zero p hp hpr x
    (hs.quotient_nonzero x (cell_subset p source d hx)) 1 1 m hm)

end SevenEighths.InverseMoment
end

end OAI
end OAIOriginalModule0751

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ActualChildStateDepth
Source SHA256: 7c7e1c44cb12fea788c2f39195a87aff9aa5da790d24509e1e1ad3541ff4db35
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0752


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem actual_cell_path_lengths {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (Jo Jn : ℕ→ℕ) (source : (k : ℕ)→Finset (MarkedSecondSource ι (Jo k) (Jn k)))
    (cellIndex : ℕ→BlockIndex) (x : (k : ℕ)→MarkedSecondSource ι (Jo k) (Jn k))
    (F M r ell V A B t j b : ℕ→ℝ) (Z eta cutoff : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (hsmall : eta≤cutoff/16) (n : ℕ)
    (hsource : ∀k<n,
      ActualSecondSourceConditions p (source k) ∧
      (∀y∈source k,y.second.frequency≠0) ∧ x k∈cell p (source k) (cellIndex k) ∧
      F k=r k+3*ell k+V k ∧
      0≤A k ∧ 0≤t k ∧ 0≤ell k ∧ 0≤V k ∧ cutoff≤ell k+V k ∧
      1≤b k ∧ b k≤Z^(6*eta) ∧
      (∀y∈source k,primeProductNorm p y.second.sourceCommon*primeProductNorm p y.second.overlap≤
        b k*Z^(r k-A k-B k-t k)) ∧
      ‖eisEmbedding (primeProduct p (x k).cube.support (x k).cube.leftExponent)‖^2≤Z^(ell k+eta) ∧
      ‖eisEmbedding (primeProduct p (x k).cube.support (x k).cube.rightExponent)‖^2≤Z^(ell k+eta) ∧
      Z^(j k-eta)≤‖eisEmbedding (jLabel p (x k).cube.support
        (fun i=>(x k).cube.leftExponent i+(x k).cube.rightExponent i)
        (x k).cube.leftBit (x k).cube.rightBit)‖^2)
    (hF : ∀k<n,F (k+1)=actualCellTotalExponent Z (Z^(r k-A k-B k-t k)) (B k) (j k) eta (cellIndex k))
    (hM : ∀k<n,M (k+1)=childM (M k) (ell k) (A k) (t k)
      (secondCellExponent Z (cellIndex k) 0) (secondCellExponent Z (cellIndex k) 1) (V k) (j k) eta) :
    F n≤F 0+15*(n:ℝ)*eta ∧ M n+3*(n:ℝ)*cutoff/2≤M 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : n<n+1 := Nat.lt_succ_self n
    obtain ⟨hs,hk,hx,hparent,hA,ht,hell,hV,hterm,hb,hthreshold,hgeom,h1,h2,hj⟩ := hsource n hn
    have hi := ih (fun k hk=>hsource k (Nat.lt_trans hk hn))
      (fun k hk=>hF k (Nat.lt_trans hk hn)) (fun k hk=>hM k (Nat.lt_trans hk hn))
    have hf := actual_cell_child_total_upper p hp (source n) hs hk (cellIndex n) (x n) hx
      Z (r n) (ell n) (V n) (A n) (B n) (t n) (j n) eta (b n) hZ hA ht hell hV heta hbin
      hb hthreshold hgeom h1 h2 hj
    have hm := actual_cell_row_decrease p hp (source n) hs hk (cellIndex n) (x n) hx
      Z (M n) (ell n) (A n) (t n) (V n) (j n) eta cutoff hZ hA ht heta hbin hterm hsmall h1 h2 hj
    rw [←hF n hn,←hparent] at hf
    rw [←hM n hn] at hm
    push_cast
    constructor <;> linarith [hi.1,hi.2]

theorem actual_cell_depth_caps (F M N V F0 M0 eta : ℝ) (n depth : ℕ)
    (hn : n≤depth) (heta : 0≤eta) (hF : F≤F0+15*(n:ℝ)*eta)
    (hM : M≤M0) (hN : 0≤N) (hV : 0≤V) (hsum : F=N+V) :
    N≤F0+15*(depth:ℝ)*eta ∧ V≤F0+15*(depth:ℝ)*eta ∧ M≤M0 := by
  have hn' : (n:ℝ)≤depth := by exact_mod_cast hn
  have he := mul_le_mul_of_nonneg_right hn' heta
  constructor
  · linarith
  constructor
  · linarith
  · exact hM

theorem actual_cell_depth_bound (M M0 cutoff : ℝ) (n : ℕ) (hcutoff : 0<cutoff)
    (hM : 0≤M) (hpath : M+3*(n:ℝ)*cutoff/2≤M0) :
    (n:ℝ)≤2*M0/(3*cutoff) := by
  apply (le_div_iff₀ (by positivity : 0<3*cutoff)).mpr
  nlinarith

end SevenEighths.InverseMoment
end

end OAI
end OAIOriginalModule0752

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ActualChildStatePuncture
Source SHA256: 251dfa71388ea2acaf2e8baf9c2b7dcd73a9e181a62014c99a9d8e6ab33f6c73
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0753


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic InverseSecondFibers CompletedGauss
local notation "O" => ActualEisensteinCubic.O

lemma actual_inherited_puncture_dvd (m : O) (γ : OuterTriple) :
    m∣actualSecondInheritedPuncture m γ := by
  refine ⟨ConcretePrimeRowBridge.idealGenerator γ.quotient*primaryGenerator γ.q0*
    primaryGenerator γ.residual,?_⟩
  unfold actualSecondInheritedPuncture actualSecondPuncture
  ring

lemma actual_inherited_radical_puncture_span (m : O) (γ : OuterTriple) :
    Ideal.span {actualSecondInheritedRadicalPuncture m γ}=
      (Ideal.span {actualSecondInheritedPuncture m γ}:Ideal O).radical :=
  ConcretePrimeRowBridge.span_idealGenerator _

lemma actual_inherited_radical_preserves_support (m : O) (γ : OuterTriple) :
    (Ideal.span {m}:Ideal O).radical∣Ideal.span {actualSecondInheritedRadicalPuncture m γ} := by
  rw [actual_inherited_radical_puncture_span,Ideal.dvd_iff_le]
  apply Ideal.radical_mono
  apply Ideal.span_singleton_le_span_singleton.mpr
  exact actual_inherited_puncture_dvd m γ

lemma actual_inherited_radical_preserves_fixed (m : O) (γ : OuterTriple) (Q : Ideal O)
    (hQ : Q.radical=Q) (hparent : Q∣Ideal.span {m}) :
    Q∣Ideal.span {actualSecondInheritedRadicalPuncture m γ} := by
  apply dvd_trans _ (actual_inherited_radical_preserves_support m γ)
  rw [Ideal.dvd_iff_le,←hQ]
  exact Ideal.radical_mono (Ideal.dvd_iff_le.mp hparent)

lemma actual_inherited_radical_is_radical (m : O) (γ : OuterTriple) :
    (Ideal.span {actualSecondInheritedRadicalPuncture m γ}:Ideal O).radical=
      Ideal.span {actualSecondInheritedRadicalPuncture m γ} := by
  rw [actual_inherited_radical_puncture_span,Ideal.radical_idem]

end SevenEighths.InverseMoment
end

end OAI
end OAIOriginalModule0753

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ActualChildStateRadius
Source SHA256: b380f3af17e0f0a280b98cfc05ceea7ee08ed5ed4ea73663b12b47e69bdc95c1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0754


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def actualCellRowExponent (Z M ell A t V j eta : ℝ) (d : BlockIndex) : ℝ :=
  childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta

def actualCellRowRadius (Z M ell A t V j eta : ℝ) (d : BlockIndex) : ℝ :=
  Z^(actualCellRowExponent Z M ell A t V j eta d)

lemma actual_cell_row_radius_pos (Z M ell A t V j eta : ℝ) (d : BlockIndex) (hZ : 0<Z) :
    0<actualCellRowRadius Z M ell A t V j eta d := Real.rpow_pos_of_pos hZ _

theorem actual_cell_correlated_source_gates {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (Z M r ell V delta A B j t eta tau L : ℝ) (hZ : 1<Z)
    (heta : 0≤eta) (hbin : 2≤Z^eta) (hL0 : 0≤L)
    (hd : ∀x∈source,‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)‖^2≤Z^(delta+eta))
    (hL : L≤Z^(r-A-B-t+4*eta))
    (hgate : ∀x∈source,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (correlatedSecondRadius p (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)
        x.second.sourceCommon x.second.divisor L
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau))) :
    ∀d,∀x∈cell p source d,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell A t V j eta d) := by
  have hk : ∀x∈source,x.second.frequency≠0 := fun x hx=>(Finset.mem_erase.mp (hgate x hx)).1
  intro d x hx
  have hxs := cell_subset p source d hx
  exact (actual_second_row_ball p hp hpr x 1 1 _).mpr
    (actual_cell_correlated_row_support p hp hpr source hk d x hx 1 1
      Z M r ell V delta A B j t eta tau L hZ heta hbin hL0 (hd x hxs) hL (hgate x hxs))

theorem actual_cell_radius_nonnegative_on_keys {ι : Type*} [DecidableEq ι]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (Z M ell A t V j eta : ℝ) (hZ : 1<Z)
    (hrows : ∀d,∀x∈cell p source d,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell A t V j eta d)) :
    ∀d∈keys p source,0≤actualCellRowExponent Z M ell A t V j eta d := by
  intro d hd
  obtain ⟨x,hx⟩ := (mem_keys_iff p source d).mp hd
  have hr := actual_second_row_radius_one p (cell p source d)
    (actualCellRowRadius Z M ell A t V j eta d) ⟨x,hx⟩ (hrows d)
  exact (Real.rpow_le_rpow_left_iff hZ).mp (by simpa only [Real.rpow_zero,actualCellRowRadius] using hr)

end SevenEighths.InverseMoment
end

end OAI
end OAIOriginalModule0754

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ActualChildStateTriples
Source SHA256: c1288d90a55f3e7d3103e4e635ef7cc792247778e99237d1fefcd4895ecccdeb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0755



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
include hp

theorem actual_cell_triple_margins
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (m : O) (hm : m≠0)
    (Z r ell V M Q z c A B t j eta : ℝ) (hZ : 1<Z)
    (hparent : CanonicalMargins (r+3*ell+V) M Q z c)
    (hA : 0≤A) (ht : 0≤t) (hV : 0≤V) (hj : 0≤j) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Q)
    (h1 : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hT : ∀x∈source,(Ideal.absNorm x.quotient:ℝ)≤Z^(t+eta))
    (γ : OuterTriple) (hγ : γ∈actualSecondTriples p 1 1 (cell p source d)) :
    actualSecondInheritedRadicalPuncture m γ≠0 ∧
    0≤actualSecondPunctureWidth Z m γ ∧
    ‖eisEmbedding (actualSecondInheritedRadicalPuncture m γ)‖^2=Z^(actualSecondPunctureWidth Z m γ) ∧
    CanonicalMargins (actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d)
      (childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta)
      (actualSecondPunctureWidth Z m γ) z (c-7*eta) := by
  have hn := actual_cell_triple_puncture_nonzero p hp hpr source hs d m hm γ hγ
  refine ⟨hn,?_,?_,?_⟩
  · exact Real.logb_nonneg hZ (EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ hn)
  · exact (Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
      (sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hn)))).symm
  · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
    have hxs := cell_subset p source d hx
    exact actual_cell_child_margins p hp hpr source hs hk d x hx 1 1 m hm
      Z r ell V M Q z c A B t j eta hZ hparent hA ht hV hj heta hbin hQ
      (h1 x hxs) (h2 x hxs) (hT x hxs)

omit hp in

theorem actual_child_enlarged_row_bounds (Z M : ℝ) (hZ : 1<Z) (k : O)
    (hk : k∈nonzeroChildFrequencyBall 1 (Z^M)) :
    k≠0 ∧ ‖eisEmbedding k‖^2≤Z^M ∧ 0≤M := by
  have hb := (mem_nonzeroChildFrequencyBall 1 one_ne_zero _ k).mp hk
  simp only [one_mul] at hb
  exact ⟨(Finset.mem_erase.mp hk).1,hb.2,actual_child_row_length_nonneg Z M hZ k hk⟩

omit hp in

theorem actual_child_size_caps (F M Q z c cap : ℝ)
    (hinv : CanonicalMargins F M Q z c) (hM : 0≤M) (hQ : 0≤Q) (hz : 0≤z)
    (hc : 0≤c) (hF : F≤cap) : M≤cap ∧ Q≤cap ∧ z≤cap := by
  obtain ⟨h1,h2⟩ := hinv
  constructor
  · linarith
  constructor <;> linarith

end SevenEighths.InverseMoment
end

end OAI
end OAIOriginalModule0755

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ActualDepthBudget
Source SHA256: 86b66c81fd90749655b835ae3fbd976d5f3a0f2c2e8ca4eb7cdcd7420ad1cf72
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0756



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment

def actualDepth (Mmax cutoff : ℝ) : ℕ := ⌈2*Mmax/(3*cutoff)⌉₊+1

lemma actualDepth_pos (Mmax cutoff : ℝ) : 0<actualDepth Mmax cutoff := by
  exact Nat.succ_pos _

lemma actualDepth_strict (Mmax cutoff : ℝ) :
    2*Mmax/(3*cutoff)<(actualDepth Mmax cutoff:ℝ) := by
  have h := Nat.le_ceil (2*Mmax/(3*cutoff))
  unfold actualDepth
  push_cast
  linarith

theorem actual_depth_parameters (depth : ℕ) (cutoff c eps : ℝ)
    (hd : 0<cutoff) (hc : 0<c) (heps : 0<eps) :
    ∃eta tau pi : ℝ,0<eta ∧ 0<tau ∧ 0<pi ∧ eta≤cutoff/16 ∧
      (depth:ℝ)*7*eta≤c/2 ∧ (depth:ℝ)*15*eta≤1 ∧
      (depth:ℝ)*(100*eta+4*tau+4*pi)≤eps/4 := by
  let D : ℝ := (depth:ℝ)+1
  have hD : 0<D := by dsimp [D];positivity
  have hn : 0≤(depth:ℝ) := Nat.cast_nonneg _
  have hnD : (depth:ℝ)≤D := by dsimp [D];linarith
  let eta := min (cutoff/16) (min (c/(28*D)) (min (1/(30*D)) (eps/(1600*D))))
  let tau := eps/(128*D)
  have heta : 0<eta := by dsimp [eta];positivity
  have htau : 0<tau := by dsimp [tau];positivity
  have he1 : eta≤cutoff/16 := min_le_left _ _
  have he2 : eta≤c/(28*D) := (min_le_right _ _).trans (min_le_left _ _)
  have he3 : eta≤1/(30*D) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have he4 : eta≤eps/(1600*D) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hb2 : eta*(28*D)≤c := (le_div_iff₀ (by positivity)).mp he2
  have hb3 : eta*(30*D)≤1 := (le_div_iff₀ (by positivity)).mp he3
  have hb4 : eta*(1600*D)≤eps := (le_div_iff₀ (by positivity)).mp he4
  have ht : tau*(128*D)=eps := by dsimp [tau];field_simp
  have hne : (depth:ℝ)*eta≤D*eta := mul_le_mul_of_nonneg_right hnD heta.le
  have hnt : (depth:ℝ)*tau≤D*tau := mul_le_mul_of_nonneg_right hnD htau.le
  refine ⟨eta,tau,tau,heta,htau,htau,he1,?_,?_,?_⟩ <;> nlinarith

theorem actual_depth_margin_size (depth n : ℕ) (hn : n≤depth)
    (c eta F0 : ℝ) (heta : 0≤eta)
    (hmargin : (depth:ℝ)*7*eta≤c/2) (hsize : (depth:ℝ)*15*eta≤1) :
    c/2≤c-7*(n:ℝ)*eta ∧ F0+15*(n:ℝ)*eta≤F0+1 := by
  have hnn : (n:ℝ)≤depth := by exact_mod_cast hn
  have hh := mul_le_mul_of_nonneg_right hnn heta
  constructor <;> nlinarith

theorem actual_depth_uniform_caps (depth n : ℕ) (hn : n≤depth)
    (F M N V Q z c F0 M0 eta : ℝ) (heta : 0≤eta) (hc : 0<c)
    (hmargin : (depth:ℝ)*7*eta≤c/2) (hsize : (depth:ℝ)*15*eta≤1)
    (hF : F≤F0+15*(n:ℝ)*eta) (hM0 : M≤M0)
    (hN : 0≤N) (hV : 0≤V) (hM : 0≤M) (hQ : 0≤Q) (hz : 0≤z)
    (hsum : F=N+V) (hinv : CanonicalMargins F M Q z (c-7*(n:ℝ)*eta)) :
    N≤F0+1 ∧ V≤F0+1 ∧ M≤min M0 (F0+1) ∧ Q≤F0+1 ∧ z≤F0+1 := by
  have hh := actual_depth_margin_size depth n hn c eta F0 heta hmargin hsize
  have hFcap : F≤F0+1 := hF.trans hh.2
  have hcaps := actual_child_size_caps F M Q z (c-7*(n:ℝ)*eta) (F0+1)
    hinv hM hQ hz (by linarith [hh.1]) hFcap
  refine ⟨?_,?_,le_min hM0 hcaps.1,hcaps.2.1,hcaps.2.2⟩ <;> linarith

theorem actual_depth_retained_loss (depth n : ℕ) (hn : n≤depth)
    (eta tau pi epsChild eps : ℝ) (he : 0≤eta) (ht : 0≤tau) (hp : 0≤pi)
    (hc : 0≤epsChild) (hbudget : (depth:ℝ)*(100*eta+4*tau+4*pi)≤eps/4)
    (hchild : (depth:ℝ)*epsChild≤eps/4) :
    (n:ℝ)*(48*eta+tau+pi+epsChild)≤eps/2 := by
  have hn' : (n:ℝ)≤depth := by exact_mod_cast hn
  have h1 := mul_le_mul_of_nonneg_right hn' (show 0≤48*eta+tau+pi+epsChild by positivity)
  have h2 : (depth:ℝ)*(48*eta+tau+pi)≤(depth:ℝ)*(100*eta+4*tau+4*pi) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    linarith
  nlinarith

theorem actual_depth_row_negative (M Mmax cutoff : ℝ) (n : ℕ) (hd : 0<cutoff)
    (hn : actualDepth Mmax cutoff≤n)
    (hpath : M+3*(n:ℝ)*cutoff/2≤Mmax) : M<0 := by
  have hn' : (actualDepth Mmax cutoff:ℝ)≤n := by exact_mod_cast hn
  have hs := (actualDepth_strict Mmax cutoff).trans_le hn'
  have hs' := (div_lt_iff₀ (by positivity : 0<3*cutoff)).mp hs
  nlinarith

end SevenEighths.InverseMoment
end

end OAI
end OAIOriginalModule0756

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalPunctureMask
Source SHA256: a4b8a01c507243d5b479f78673f4f88c280f0a618625eac8184d96fd51d1194a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0757



namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge CanonicalQuadraticSieve
open InverseInitialClippedColumns
local notation "Eis" => ActualEisensteinCubic.O

section General
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,goodLambda∉Ideal.span {p i})

omit [DecidableEq ι] in
theorem rowCoprimeMask_redundant_mul (S : Finset ι) (m c : Eis)
    (hc : ∀ i∈S,c∈Ideal.span {p i}→m∈Ideal.span {p i}) :
    rowCoprimeMask (fun i=>Ideal.span {p i}) S (m*c)=
      rowCoprimeMask (fun i=>Ideal.span {p i}) S m := by
  have he : (∃i∈S,m*c∈Ideal.span {p i}) ↔ ∃i∈S,m∈Ideal.span {p i} := by
    constructor
    · rintro ⟨i,hi,hm⟩
      exact ⟨i,hi,((inferInstance : (Ideal.span {p i}).IsPrime).mem_or_mem hm).elim id (hc i hi)⟩
    · rintro ⟨i,hi,hm⟩
      exact ⟨i,hi,Ideal.mul_mem_right _ _ hm⟩
  simp only [rowCoprimeMask,he]

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_redundant_puncture
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m c f k : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X : ℝ)
    (hc : ∀ i∈pool,c∈Ideal.span {p i}→m∈Ideal.span {p i}) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ (m*c) f k slots lists a W X=
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a W X := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  apply Finset.sum_congr rfl
  intro S hS
  have hm := rowCoprimeMask_redundant_mul p S m c
    (fun i hi=>hc i (Finset.mem_powerset.mp hS hi))
  simp only [secondChildColumn,hm]

omit [DecidableEq σ] in
theorem normalizedColumnEnergy_redundant_puncture
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m c : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis→ℝ)
    (W : ℝ→ℂ) (X Z F : ℝ)
    (hc : ∀ i∈pool,c∈Ideal.span {p i}→m∈Ideal.span {p i}) :
    normalizedColumnEnergy p hp hcop hg pool Ψ (m*c) slots lists a labels rows D W X Z F=
      normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D W X Z F := by
  simp only [normalizedColumnEnergy,finiteCanonicalMarkedRow_redundant_puncture
    p hp hcop hg pool Ψ m c _ _ slots lists a W X hc]

omit [DecidableEq ι] in
theorem puncture_mem_of_radical_dvd (m c : Eis)
    (hc : (Ideal.span {c}:Ideal Eis).radical∣(Ideal.span {m}:Ideal Eis).radical)
    (i : ι) (hi : c∈Ideal.span {p i}) : m∈Ideal.span {p i} := by
  rw [←Ideal.span_singleton_le_iff_mem]
  apply Ideal.le_radical.trans
  apply (Ideal.dvd_iff_le.mp hc).trans
  exact (inferInstance : (Ideal.span {p i}).IsPrime).radical_le_iff.mpr
    (by rwa [Ideal.span_singleton_le_iff_mem])

omit [DecidableEq ι] in
theorem inherited_puncture_redundant_mem (m c : Eis)
    (γ : InverseSecondFibers.OuterTriple)
    (hc : (Ideal.span {c}:Ideal Eis).radical∣Ideal.span {m})
    (i : ι) (hi : c∈Ideal.span {p i}) :
    actualSecondInheritedRadicalPuncture m γ∈Ideal.span {p i} := by
  have hd := actual_inherited_radical_preserves_fixed m γ (Ideal.span {c}).radical
    (Ideal.radical_idem _) hc
  apply puncture_mem_of_radical_dvd p _ c _ i hi
  rw [actual_inherited_radical_is_radical]
  exact hd

end General

theorem outside_pool_redundant_puncture {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal Eis)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (hSp : ∀P∈S,Prime P)
    (pool : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (Ψ : Eis →* ℂ) (m f k : Eis) (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (W : ℝ→ℂ) (X : ℝ) :
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    finiteCanonicalMarkedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) pool Ψ
      (m*excludedGenerator S) f k slots lists a W X=
    finiteCanonicalMarkedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) pool Ψ m f k slots lists a W X := by
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  apply finiteCanonicalMarkedRow_redundant_puncture
  intro i hi hc
  rw [poolPrimary_span _ (InitialMeanSquare.outsideSquarefree_admissible S D hbad)] at hc
  exact False.elim (excludedGenerator_not_mem_pool S D hSp i hc)

end SevenEighths.InverseMoment
end

end OAI
end OAIOriginalModule0757

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalPunctureMaskEnergy
Source SHA256: 7a7c8c090d9e3aec46cded9e2f1618d5c876fc1cb63cbfe0de311d1e61161cc8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0758


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve InverseInitialClippedColumns
local notation "Eis" => ActualEisensteinCubic.O

theorem outside_pool_redundant_energy {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal Eis)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (hSp : ∀P∈S,Prime P)
    (pool : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (Ψ : Eis →* ℂ) (m : Eis) (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (weight : Ideal Eis→ℝ)
    (W : ℝ→ℂ) (X Z Fexp : ℝ) :
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) pool Ψ
      (m*excludedGenerator S) slots lists a labels rows weight W X Z Fexp=
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) pool Ψ
      m slots lists a labels rows weight W X Z Fexp := by
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  apply normalizedColumnEnergy_redundant_puncture
  intro i hi hc
  rw [poolPrimary_span F hF i] at hc
  exact False.elim (excludedGenerator_not_mem_pool S D hSp i hc)

theorem reflection_pool_mask_energy {σ : Type*} [DecidableEq σ]
    (q D : ℕ)
    (pool : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
    (Ψ : Eis →* ℂ) (m : Eis) (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (weight : Ideal Eis→ℝ)
    (W : ℝ→ℂ) (X Z Fexp : ℝ) :
    let S:=reflectionExcludedPrimes q
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q)
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) pool Ψ
      (ActualFiber.maskElement q m) slots lists a labels rows weight W X Z Fexp=
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) pool Ψ
      m slots lists a labels rows weight W X Z Fexp :=
  outside_pool_redundant_energy (reflectionExcludedPrimes q) D
    (reflectionExcludedPrimes_bad q) (reflectionExcludedPrimes_prime q)
    pool Ψ m slots lists a labels rows weight W X Z Fexp

theorem inherited_radical_mask_energy {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι→Eis) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Ψ : Eis→*ℂ) (m c : Eis) (γ : InverseSecondFibers.OuterTriple)
    (hc : (Ideal.span {c}:Ideal Eis).radical∣Ideal.span {m})
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (weight : Ideal Eis→ℝ)
    (W : ℝ→ℂ) (X Z Fexp : ℝ) :
    normalizedColumnEnergy p hp hcop hg pool Ψ
      (actualSecondInheritedRadicalPuncture m γ*c) slots lists a labels rows weight W X Z Fexp=
    normalizedColumnEnergy p hp hcop hg pool Ψ
      (actualSecondInheritedRadicalPuncture m γ) slots lists a labels rows weight W X Z Fexp :=
  normalizedColumnEnergy_redundant_puncture p hp hcop hg pool Ψ _ c
    slots lists a labels rows weight W X Z Fexp
    (fun i _=>inherited_puncture_redundant_mem p m c γ hc i)

end SevenEighths.InverseMoment
end

end OAI
end OAIOriginalModule0758

/-! Original module: OAI.NumberTheory.DirichletL.Descent.PriorityRetainedMovingRadius
Source SHA256: ac27c0601724572013c4b2c29e180702f3f30e4c2dcecb042ab312e0ffb25707
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0759



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem actual_priority_retained_moving_radius
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (J K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (_hs : ActualSecondSourceConditions p source),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R (index p x))) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤Z → 1≤b → b≤Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t) Φ Y X)‖ ≤
      C*A*‖secondRayCoefficient z‖*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,hC,henergy⟩:=
    actual_priority_source_moving_radius (ι:=ι) (σ:=σ) om Φ lo hi hlo hsupport negative B₀ hB₀ J K εmass hεmass
  obtain ⟨Cbin,hCbin,hbudget⟩:=priority_source_scalar_budget caps hcaps
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,36*(2:ℝ)^(2*K)*C,Cbin,by positivity,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b
    ρ t w labels A hd₁ hd₂ hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have he:=henergy p hp hcop hg hpr hinj hc source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X εchild Vlabel ell Ractive j tcount eta ρ t w labels A
    hd₁ hd₂ hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  let H:ℝ:=(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)
  have hheight:(1+‖-priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J*
      (1+‖priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J=H:=by
    cases negative <;> simp [priorityHeight,H,two_mul,pow_add]
  let D:ℝ:=36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*C*H
  have hD:0≤D:=by dsimp [D,H];positivity
  let S:ℝ:=∑d∈keys p source,priorityCellScalar Z Y L X ell Ractive j tcount eta εchild εmass Bfirst (secondRayCoefficient z) d
  have hfactor:
      (∑d∈keys p source,(Real.exp (6*L)*‖(Y:ℂ)*secondRayCoefficient z*
          ((scales d 1*scales d 2*Z^(secondCellColumnExponent Z X d):ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 (secondCellColumnExponent Z X d)+Vlabel d)+εchild))*
          Z^((ell+Ractive/2-j+tcount+secondCellExponent Z d 0-secondCellExponent Z d 1+11*eta/2)*(1+εmass)))*
          (C*((1+‖-priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J*
            (1+‖priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J))))=D*S:=by
    dsimp only [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [hheight,hVe d]
    dsimp only [D,priorityCellScalar,secondCount]
    ring
  simp only [pow_zero,div_one] at he
  rw [hfactor] at he
  have hbnd:=hbudget p hp source Z M r ell V delta Acol Bfirst Ractive j tcount eta tau pi εchild εmass b D
    (secondRayCoefficient z) hZ2 hD hb hthreshold
    (fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx)) hnorm
    (by simpa only [hXe] using hgeom) hmass
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  have hP:0≤P:=by dsimp [P];positivity
  have hconst:D≤(36*(2:ℝ)^(2*K)*C)*A*H:=by
    have h1:(2:ℝ)^slots₁.card≤2^K:=pow_le_pow_right₀ (by norm_num) hslots₁
    have h2:(2:ℝ)^slots₂.card≤2^K:=pow_le_pow_right₀ (by norm_num) hslots₂
    calc
      _≤36*(2:ℝ)^K*(2:ℝ)^K*A*C*H:=by dsimp only [D];gcongr
      _= _:=by rw [show 2*K=K+K by omega,pow_add];ring
  calc
    _≤P*(D*S):=mul_le_mul_of_nonneg_left he hP
    _≤D*‖secondRayCoefficient z‖*(1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild):=by
      convert hbnd using 1 ; dsimp only [P,S] ; rw [hYe,hXe,hLe] ; ring
    _≤((36*(2:ℝ)^(2*K)*C)*A*H)*‖secondRayCoefficient z‖*(1+Cbin*Real.log Z)^4*
        Z^(r+3*ell+V+48*eta+tau+pi+εchild):=by gcongr
    _= _:=by dsimp only [H];ring

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0759

/-! Original module: OAI.NumberTheory.DirichletL.Descent.PriorityRetainedMovingRadiusWindowOrder
Source SHA256: f3c70c5a0e6a64a6f71385aae2f678947c04ba28fac6f209aed6b85a51e8fb6a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0760




namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem actual_priority_retained_moving_radius_window_order
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (_hs : ActualSecondSourceConditions p source),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R (index p x))) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤Z → 1≤b → b≤Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t) Φ Y X)‖ ≤
      C*A*‖secondRayCoefficient z‖*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    actual_priority_source_moving_radius_window_order (ι:=ι) (σ:=σ) om Φ lo hi hlo hsupport negative B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,hC,henergy⟩:=hordered J
  obtain ⟨Cbin,hCbin,hbudget⟩:=priority_source_scalar_budget caps hcaps
  refine ⟨36*(2:ℝ)^(2*K)*C,Cbin,by positivity,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b
    ρ t w labels A hd₁ hd₂ hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have he:=henergy p hp hcop hg hpr hinj hc source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X εchild Vlabel ell Ractive j tcount eta ρ t w labels A
    hd₁ hd₂ hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  let H:ℝ:=(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)
  have hheight:(1+‖-priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J*
      (1+‖priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J=H:=by
    cases negative <;> simp [priorityHeight,H,two_mul,pow_add]
  let D:ℝ:=36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*C*H
  have hD:0≤D:=by dsimp [D,H];positivity
  let S:ℝ:=∑d∈keys p source,priorityCellScalar Z Y L X ell Ractive j tcount eta εchild εmass Bfirst (secondRayCoefficient z) d
  have hfactor:
      (∑d∈keys p source,(Real.exp (6*L)*‖(Y:ℂ)*secondRayCoefficient z*
          ((scales d 1*scales d 2*Z^(secondCellColumnExponent Z X d):ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 (secondCellColumnExponent Z X d)+Vlabel d)+εchild))*
          Z^((ell+Ractive/2-j+tcount+secondCellExponent Z d 0-secondCellExponent Z d 1+11*eta/2)*(1+εmass)))*
          (C*((1+‖-priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J*
            (1+‖priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J))))=D*S:=by
    dsimp only [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [hheight,hVe d]
    dsimp only [D,priorityCellScalar,secondCount]
    ring
  simp only [pow_zero,div_one] at he
  rw [hfactor] at he
  have hbnd:=hbudget p hp source Z M r ell V delta Acol Bfirst Ractive j tcount eta tau pi εchild εmass b D
    (secondRayCoefficient z) hZ2 hD hb hthreshold
    (fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx)) hnorm
    (by simpa only [hXe] using hgeom) hmass
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  have hP:0≤P:=by dsimp [P];positivity
  have hconst:D≤(36*(2:ℝ)^(2*K)*C)*A*H:=by
    have h1:(2:ℝ)^slots₁.card≤2^K:=pow_le_pow_right₀ (by norm_num) hslots₁
    have h2:(2:ℝ)^slots₂.card≤2^K:=pow_le_pow_right₀ (by norm_num) hslots₂
    calc
      _≤36*(2:ℝ)^K*(2:ℝ)^K*A*C*H:=by dsimp only [D];gcongr
      _= _:=by rw [show 2*K=K+K by omega,pow_add];ring
  calc
    _≤P*(D*S):=mul_le_mul_of_nonneg_left he hP
    _≤D*‖secondRayCoefficient z‖*(1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild):=by
      convert hbnd using 1 ; dsimp only [P,S] ; rw [hYe,hXe,hLe] ; ring
    _≤((36*(2:ℝ)^(2*K)*C)*A*H)*‖secondRayCoefficient z‖*(1+Cbin*Real.log Z)^4*
        Z^(r+3*ell+V+48*eta+tau+pi+εchild):=by gcongr
    _= _:=by dsimp only [H];ring

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0760

/-! Original module: OAI.NumberTheory.DirichletL.Descent.PriorityRetainedMovingRadiusWindowOrderUniform
Source SHA256: cf8081d5c66a68ef0df02dc59932aae7e8a19b64688418acecdcdbd6fa2a0f50
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0761






namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
local notation "Eis" => ActualEisensteinCubic.O
theorem actual_priority_retained_moving_radius_window_order_uniform_types
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (_hs : ActualSecondSourceConditions p source),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R (index p x))) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤Z → 1≤b → b≤Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t) Φ Y X)‖ ≤
      C*A*‖secondRayCoefficient z‖*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    actual_priority_source_moving_radius_window_order_uniform_types  om Φ lo hi hlo hsupport negative B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,hC,henergy⟩:=hordered J
  obtain ⟨Cbin,hCbin,hbudget⟩:=priority_source_scalar_budget caps hcaps
  refine ⟨36*(2:ℝ)^(2*K)*C,Cbin,by positivity,hCbin,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b
    ρ t w labels A hd₁ hd₂ hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have he:=henergy p hp hcop hg hpr hinj hc source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X εchild Vlabel ell Ractive j tcount eta ρ t w labels A
    hd₁ hd₂ hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  let H:ℝ:=(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)
  have hheight:(1+‖-priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J*
      (1+‖priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J=H:=by
    cases negative <;> simp [priorityHeight,H,two_mul,pow_add]
  let D:ℝ:=36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*C*H
  have hD:0≤D:=by dsimp [D,H];positivity
  let S:ℝ:=∑d∈keys p source,priorityCellScalar Z Y L X ell Ractive j tcount eta εchild εmass Bfirst (secondRayCoefficient z) d
  have hfactor:
      (∑d∈keys p source,(Real.exp (6*L)*‖(Y:ℂ)*secondRayCoefficient z*
          ((scales d 1*scales d 2*Z^(secondCellColumnExponent Z X d):ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 (secondCellColumnExponent Z X d)+Vlabel d)+εchild))*
          Z^((ell+Ractive/2-j+tcount+secondCellExponent Z d 0-secondCellExponent Z d 1+11*eta/2)*(1+εmass)))*
          (C*((1+‖-priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J*
            (1+‖priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J))))=D*S:=by
    dsimp only [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [hheight,hVe d]
    dsimp only [D,priorityCellScalar,secondCount]
    ring
  simp only [pow_zero,div_one] at he
  rw [hfactor] at he
  have hbnd:=hbudget p hp source Z M r ell V delta Acol Bfirst Ractive j tcount eta tau pi εchild εmass b D
    (secondRayCoefficient z) hZ2 hD hb hthreshold
    (fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx)) hnorm
    (by simpa only [hXe] using hgeom) hmass
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  have hP:0≤P:=by dsimp [P];positivity
  have hconst:D≤(36*(2:ℝ)^(2*K)*C)*A*H:=by
    have h1:(2:ℝ)^slots₁.card≤2^K:=pow_le_pow_right₀ (by norm_num) hslots₁
    have h2:(2:ℝ)^slots₂.card≤2^K:=pow_le_pow_right₀ (by norm_num) hslots₂
    calc
      _≤36*(2:ℝ)^K*(2:ℝ)^K*A*C*H:=by dsimp only [D];gcongr
      _= _:=by rw [show 2*K=K+K by omega,pow_add];ring
  calc
    _≤P*(D*S):=mul_le_mul_of_nonneg_left he hP
    _≤D*‖secondRayCoefficient z‖*(1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild):=by
      convert hbnd using 1 ; dsimp only [P,S] ; rw [hYe,hXe,hLe] ; ring
    _≤((36*(2:ℝ)^(2*K)*C)*A*H)*‖secondRayCoefficient z‖*(1+Cbin*Real.log Z)^4*
        Z^(r+3*ell+V+48*eta+tau+pi+εchild):=by gcongr
    _= _:=by dsimp only [H];ring

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0761

/-! Original module: OAI.NumberTheory.DirichletL.Descent.PrioritySourceEnergy
Source SHA256: 5db226576fb44e309288111122110e7dbe1b29bafed2031f6caa37d3a8877647
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0762



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem actual_priority_source_recursive
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (J K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∃ C : ℝ,0 ≤ C ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (_hs : ActualSecondSourceConditions p source),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (Y R L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t) Φ Y X)‖ ≤
      ∑d∈keys p source,(Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*(((scales d 1)*(scales d 2)*(Z^(secondCellColumnExponent Z X d)) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 (secondCellColumnExponent Z X d)+(Vlabel d))+εchild))*
          Z^((ell+Ractive/2-j+tcount+(secondCellExponent Z d 0)-(secondCellExponent Z d 1)+11*eta/2)*(1+εmass)))*
          (C*((1+‖(-priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J *
            (1+‖(priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*(scales d 3)/((scales d 1)*(scales d 2)^2*(Z^(secondCellColumnExponent Z X d))^2))^0)) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,hC,henergy⟩:=
    actual_priority_cell_recursive (ι:=ι) (σ:=σ) om Φ lo hi hlo hsupport negative B₀ hB₀ 0 J K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,hC,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X εchild Vlabel ell Ractive j tcount eta ρ t w labels A
    hd₁ hd₂ hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have hz:0<Z:=zero_lt_one.trans hZ
  have hk:∀x∈source,x.second.frequency≠0:=fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx)
  rw [physical_source_partition p hp hcop hg source pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ w]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  have hin : cell p source d⊆source:=cell_subset p source d
  have hcommon:∀x∈cell p source d,primeProductNorm p x.second.sourceCommon≤Z^(secondCellExponent Z d 0+eta):=by
    intro x hx
    have hr:primeProductNorm p x.second.sourceCommon≤2*scales d 0:=
      (div_le_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 0).2.le
    apply hr.trans
    rw [Real.rpow_add hz,second_cell_scale_rpow Z d 0 hZ]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hbin (show 0≤scales d 0 from (dyadScale_pos _).le)
  have hdiv:∀x∈cell p source d,Z^(secondCellExponent Z d 1-eta)≤primeProductNorm p x.second.divisor:=by
    intro x hx
    have hr:scales d 1≤primeProductNorm p x.second.divisor:=by
      simpa [outerNorms,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 1).1
    have hh:Z^(secondCellExponent Z d 1-eta)≤Z^(secondCellExponent Z d 1):=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    rw [second_cell_scale_rpow Z d 1 hZ] at hh
    exact hh.trans hr
  exact henergy p hp hcop hg hpr hinj hc (cell p source d) (cell_conditions p source hs d) d
    (fun x hx=>(mem_cell p source d x).mp hx |>.2) pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X (Vlabel d) εchild ell Ractive j tcount
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta ρ t w (labels d) A
    (fun x hx=>hd₁ x (hin hx)) (fun x hx=>hd₂ x (hin hx)) hρ hL hZ hX hY
    (fun x hx=>hrows x (hin hx)) (fun x hx=>hcube₁ x (hin hx)) (fun x hx=>hcube₂ x (hin hx))
    (fun x hx=>hactive x (hin hx)) (fun x hx=>hj x (hin hx)) (fun x hx=>hquot x (hin hx))
    hcommon hdiv hΨ (fun x hx=>hw x (hin hx)) ha₁ ha₂ (hlabels d hd) ho hslots₁ hslots₂ hA
    (hleft d hd) (hright d hd)

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0762

/-! Original module: OAI.NumberTheory.DirichletL.Descent.PriorityRetainedBound
Source SHA256: fa41ff469d2718568942e72646ae69dd9607de785487c01b1c3c30897d4ae1ef
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0763



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem actual_priority_retained_bound
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (J K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (_hs : ActualSecondSourceConditions p source),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (Y R L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤Z → 1≤b → b≤Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t) Φ Y X)‖ ≤
      C*A*‖secondRayCoefficient z‖*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,hC,henergy⟩:=
    actual_priority_source_recursive (ι:=ι) (σ:=σ) om Φ lo hi hlo hsupport negative B₀ hB₀ J K εmass hεmass
  obtain ⟨Cbin,hCbin,hbudget⟩:=priority_source_scalar_budget caps hcaps
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,36*(2:ℝ)^(2*K)*C,Cbin,by positivity,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b
    ρ t w labels A hd₁ hd₂ hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have he:=henergy p hp hcop hg hpr hinj hc source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X εchild Vlabel ell Ractive j tcount eta ρ t w labels A
    hd₁ hd₂ hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  let H:ℝ:=(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)
  have hheight:(1+‖-priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J*
      (1+‖priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J=H:=by
    cases negative <;> simp [priorityHeight,H,two_mul,pow_add]
  let D:ℝ:=36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*C*H
  have hD:0≤D:=by dsimp [D,H];positivity
  let S:ℝ:=∑d∈keys p source,priorityCellScalar Z Y L X ell Ractive j tcount eta εchild εmass Bfirst (secondRayCoefficient z) d
  have hfactor:
      (∑d∈keys p source,(Real.exp (6*L)*‖(Y:ℂ)*secondRayCoefficient z*
          ((scales d 1*scales d 2*Z^(secondCellColumnExponent Z X d):ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 (secondCellColumnExponent Z X d)+Vlabel d)+εchild))*
          Z^((ell+Ractive/2-j+tcount+secondCellExponent Z d 0-secondCellExponent Z d 1+11*eta/2)*(1+εmass)))*
          (C*((1+‖-priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J*
            (1+‖priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J))))=D*S:=by
    dsimp only [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [hheight,hVe d]
    dsimp only [D,priorityCellScalar,secondCount]
    ring
  simp only [pow_zero,div_one] at he
  rw [hfactor] at he
  have hbnd:=hbudget p hp source Z M r ell V delta Acol Bfirst Ractive j tcount eta tau pi εchild εmass b D
    (secondRayCoefficient z) hZ2 hD hb hthreshold
    (fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx)) hnorm
    (by simpa only [hXe] using hgeom) hmass
  have hs: C*0≤C*0:=le_refl _
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  have hP:0≤P:=by dsimp [P];positivity
  have hconst:D≤(36*(2:ℝ)^(2*K)*C)*A*H:=by
    have h1:(2:ℝ)^slots₁.card≤2^K:=pow_le_pow_right₀ (by norm_num) hslots₁
    have h2:(2:ℝ)^slots₂.card≤2^K:=pow_le_pow_right₀ (by norm_num) hslots₂
    calc
      _≤36*(2:ℝ)^K*(2:ℝ)^K*A*C*H:=by dsimp only [D];gcongr
      _= _:=by rw [show 2*K=K+K by omega,pow_add];ring
  calc
    _≤P*(D*S):=mul_le_mul_of_nonneg_left he hP
    _≤D*‖secondRayCoefficient z‖*(1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild):=by
      convert hbnd using 1 ; dsimp only [P,S] ; rw [hYe,hXe,hLe] ; ring
    _≤((36*(2:ℝ)^(2*K)*C)*A*H)*‖secondRayCoefficient z‖*(1+Cbin*Real.log Z)^4*
        Z^(r+3*ell+V+48*eta+tau+pi+εchild):=by gcongr
    _= _:=by dsimp only [H];ring

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0763

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.SecondUniformCutoff
Source SHA256: b21189713b950928c76421771c7eea66e9e7892a10cb73e6bf83f3d900c9af4f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0764





namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.InverseSecondUniformCutoff
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseSecondSourceBlocks InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def uniformSecondRadius {ι : Type*} [DecidableEq ι] (p : ι→O)
    (Z delta eta : ℝ) (G E : Finset ι) (L Y H : ℝ) : ℝ :=
  Z^(delta+eta)*(primeProductNorm p E/primeProductNorm p G)^2*L^2*H/Y

lemma uniformSecondRadius_nonneg {ι : Type*} [DecidableEq ι] (p : ι→O)
    (Z delta eta : ℝ) (G E : Finset ι) (L Y H : ℝ)
    (hZ : 0≤Z) (hY : 0≤Y) (hH : 0≤H) :
    0≤uniformSecondRadius p Z delta eta G E L Y H := by
  unfold uniformSecondRadius
  positivity

theorem correlated_le_uniform {ι : Type*} [DecidableEq ι] (p : ι→O)
    (Z delta eta : ℝ) (d : O) (G E : Finset ι) (L Y H : ℝ)
    (hY : 0<Y) (hH : 0≤H) (hd : ‖eisEmbedding d‖^2≤Z^(delta+eta)) :
    correlatedSecondRadius p d G E L Y H≤uniformSecondRadius p Z delta eta G E L Y H := by
  unfold correlatedSecondRadius uniformSecondRadius
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (sq_nonneg _)) (sq_nonneg _)) hH) hY.le

theorem uniform_radius_bound {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (G E : Finset ι) (Z delta theta g s Hc eta tau L : ℝ)
    (hZ : 0<Z) (hL0 : 0≤L)
    (hE : primeProductNorm p E≤Z^(theta+eta))
    (hG : Z^(g-eta)≤primeProductNorm p G) (hL : L≤Z^(s+4*eta)) :
    uniformSecondRadius p Z delta eta G E L (Z^(Hc+12*eta+tau)) (Z^tau)≤
      Z^(2*(s-g)-Hc+delta+2*theta+eta) := by
  have hratio : primeProductNorm p E/primeProductNorm p G≤Z^(theta-g+2*eta) := by
    calc
      _≤Z^(theta+eta)/Z^(g-eta):=div_le_div₀
        (Real.rpow_pos_of_pos hZ _).le hE (Real.rpow_pos_of_pos hZ _) hG
      _= _:=by rw [←Real.rpow_sub hZ];congr 1;ring
  have hratio0 : 0≤primeProductNorm p E/primeProductNorm p G :=
    div_nonneg (primeProductNorm_pos p hp E).le (primeProductNorm_pos p hp G).le
  have hsq (x : ℝ) : (Z^x)^2=Z^(2*x) := by
    rw [pow_two,←Real.rpow_add hZ]
    congr 1
    ring
  calc
    _≤Z^(delta+eta)*(Z^(theta-g+2*eta))^2*(Z^(s+4*eta))^2*Z^tau/Z^(Hc+12*eta+tau):=by
      unfold uniformSecondRadius
      gcongr
    _= _:=by
      rw [hsq,hsq,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_sub hZ]
      congr 1
      ring

theorem uniform_radius_childM {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (G E : Finset ι) (Z M r ell V delta A B j t g theta eta tau L : ℝ)
    (hZ : 0<Z) (hL0 : 0≤L)
    (hE : primeProductNorm p E≤Z^(theta+eta))
    (hG : Z^(g-eta)≤primeProductNorm p G) (hL : L≤Z^(r-A-B-t+4*eta)) :
    uniformSecondRadius p Z delta eta G E L
      (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau)≤
      Z^(childM M ell A t g theta V j eta) := by
  have hb:=uniform_radius_bound p hp G E Z delta theta g (r-A-B-t)
    (firstPhysicalHeight M r ell V delta B j) eta tau L hZ hL0 hE hG hL
  convert hb using 1
  congr 1
  unfold childM decrease firstPhysicalHeight
  ring

theorem actual_cell_uniform_source_gates {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (Z M r ell V delta A B j t eta tau L : ℝ) (hZ : 1<Z)
    (heta : 0≤eta) (hbin : 2≤Z^eta) (hL0 : 0≤L)
    (hL : L≤Z^(r-A-B-t+4*eta))
    (hgate : ∀x∈source,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (uniformSecondRadius p Z delta eta x.second.sourceCommon x.second.divisor L
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau))) :
    ∀d,∀x∈cell p source d,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell A t V j eta d) := by
  have hk : ∀x∈source,x.second.frequency≠0 := fun x hx=>(Finset.mem_erase.mp (hgate x hx)).1
  intro d x hx
  have hxs:=cell_subset p source d hx
  have hE:=(actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).2
  have hG:=(actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).1
  have hr:=uniform_radius_childM p hp x.second.sourceCommon x.second.divisor
    Z M r ell V delta A B j t (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta tau L
    (zero_lt_one.trans hZ) hL0 (by simpa [outerNorms] using hE) (by simpa [outerNorms] using hG) hL
  have hb:=(mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) _ _).mp (hgate x hxs)
  exact (mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) _ _).mpr ⟨hb.1,hb.2.trans hr⟩

theorem actual_cell_uniform_child_rows {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (Z M r ell V delta A B j t eta tau L : ℝ) (hZ : 1<Z)
    (heta : 0≤eta) (hbin : 2≤Z^eta) (hL0 : 0≤L)
    (hL : L≤Z^(r-A-B-t+4*eta))
    (hgate : ∀x∈source,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (uniformSecondRadius p Z delta eta x.second.sourceCommon x.second.divisor L
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau))) :
    ∀d,∀x∈cell p source d,∀u v:Oˣ,(actualSecondChild p u v x).2.2∈nonzeroChildFrequencyBall 1
      (actualCellRowRadius Z M ell A t V j eta d) := by
  intro d x hx u v
  exact (actual_second_row_ball p hp hpr x u v _).mp
    (actual_cell_uniform_source_gates p hp source Z M r ell V delta A B j t eta tau L
      hZ heta hbin hL0 hL hgate d x hx)

theorem actual_cell_uniform_radius_nonnegative {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (Z M r ell V delta A B j t eta tau L : ℝ) (hZ : 1<Z)
    (heta : 0≤eta) (hbin : 2≤Z^eta) (hL0 : 0≤L)
    (hL : L≤Z^(r-A-B-t+4*eta))
    (hgate : ∀x∈source,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (uniformSecondRadius p Z delta eta x.second.sourceCommon x.second.divisor L
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau))) :
    ∀d∈keys p source,0≤actualCellRowExponent Z M ell A t V j eta d :=
  actual_cell_radius_nonnegative_on_keys p source Z M ell A t V j eta hZ
    (actual_cell_uniform_source_gates p hp source Z M r ell V delta A B j t eta tau L
      hZ heta hbin hL0 hL hgate)

theorem full_second_uniform_tail (order : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct : ℝ),0<Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀a,‖Ψ a‖≤1)
      (Z delta eta : ℝ) (m c d : O) (_hd : d≠0)
      (_hdyad : ‖eisEmbedding d‖^2≤Z^(delta+eta))
      (Hcol : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (B Y H L : ℝ),
      0≤B → 0<Y → 0≤H → 1≤L →
      (∀U,‖Hcol U‖≤B) → (∀U,Hcol U≠0→primeProductNorm p U≤L) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y
        (fun G E=>childFrequencyBall
          (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E)
          (uniformSecondRadius p Z delta eta G E L Y H))‖≤
        (128*L)^4*(B^2*(Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
          (1+L^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,he⟩:=full_second_correlated_tail order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ Z delta eta m c d hd hdyad Hcol W B Y H L hB hY hH hL hcol hsupp
  exact he p hp hg hinj hc F Ψ hΨ m c d hd Hcol W B Y H L
    (fun G E=>uniformSecondRadius p Z delta eta G E L Y H) hB hY hH hL hcol hsupp
    (fun G _ E=>correlated_le_uniform p Z delta eta d G E.val L Y H hY hH hdyad)

end SevenEighths.InverseSecondUniformCutoff
end

end OAI
end OAIOriginalModule0764

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.TerminalWidths
Source SHA256: 036914430149334df2c08329b0a2a8973528dd0af98cbe021268170489ee9eda
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0765



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseTerminalWidths
open ActualEisensteinCubic CompletedGauss UniqueFactorizationMonoid
open InverseMoment CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

lemma norm_one_le (I : Ideal O) (hI : I ≠ 0) : (1 : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

theorem physical_residual_width (I Q : Ideal O) (hI : I ≠ 0)
    (Z M O₀ H Ck CO CH : ℝ) (hZ : 1 < Z) (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ))
    (hres : Z ^ H / CH ≤ (Ideal.absNorm (rowResidualPart I Q) : ℝ)) :
    H ≤ M - O₀ + Real.log (CH * Ck * CO) / Real.log Z := by
  have hz0 : 0 < Z := by linarith
  have hp := (div_le_iff₀ hCO).mp hpow
  have hr := (div_le_iff₀ hCH).mp hres
  have hs : Z ^ (H + O₀) ≤ (CH * Ck * CO) * Z ^ M := by
    calc
      _ = Z ^ H * Z ^ O₀ := Real.rpow_add hz0 _ _
      _ ≤ ((Ideal.absNorm (rowResidualPart I Q) : ℝ) * CH) *
          ((Ideal.absNorm (rowPowerfulPart I) : ℝ) * CO) :=
        mul_le_mul hr hp (Real.rpow_nonneg hz0.le _) (by positivity)
      _ = (CH * CO) * ((Ideal.absNorm (rowPowerfulPart I) : ℝ) *
          (Ideal.absNorm (rowResidualPart I Q) : ℝ)) := by ring
      _ ≤ (CH * CO) * (Ideal.absNorm I : ℝ) :=
        mul_le_mul_of_nonneg_left (by simpa only [mul_comm] using actual_residual_norm_width I Q hI) (by positivity)
      _ ≤ (CH * CO) * (Ck * Z ^ M) := mul_le_mul_of_nonneg_left hk (by positivity)
      _ = _ := by ring
  have hl := Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos hz0 _) hs
  rw [Real.logb_rpow hz0 (ne_of_gt hZ), Real.logb_mul (by positivity) (by positivity),
    Real.logb_rpow hz0 (ne_of_gt hZ)] at hl
  unfold Real.logb at hl
  linarith

theorem constant_log_error (C η : ℝ) (_hC : 0 < C) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → Real.log C / Real.log Z ≤ η := by
  refine ⟨max 2 (Real.exp (Real.log C / η)), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro Z hZ
  have hz : 1 < Z := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hZ)
  have he : Real.exp (Real.log C / η) ≤ Z := (le_max_right _ _).trans hZ
  have hl := Real.log_le_log (Real.exp_pos _) he
  rw [Real.log_exp] at hl
  apply (div_le_iff₀ (Real.log_pos hz)).mpr
  have hh := (div_le_iff₀ hη).mp hl
  nlinarith

def activeCharge (j : ℕ) (e : Fin 3) : ℤ :=
  if j = 4 then (if e = 2 then -2 else 1) else if j = 0 then 1 else 2

theorem activeCharge_le_two (j : ℕ) (e : Fin 3) : activeCharge j e ≤ 2 := by
  unfold activeCharge
  split_ifs <;> norm_num

theorem activeCharge_le_one (j : ℕ) (e : Fin 3) (hj : j = 0 ∨ j = 4) :
    activeCharge j e ≤ 1 := by
  rcases hj with rfl | rfl
  · simp [activeCharge]
  · simp only [activeCharge, ite_true]
    split_ifs <;> norm_num

theorem reflectionLocalCost_eq_charge (q : ℝ) (_hq : 0 < q) (j : ℕ) (e : Fin 3) :
    reflectionLocalCost q j e = q ^ (activeCharge j e : ℝ) := by
  unfold reflectionLocalCost activeCharge
  split_ifs <;> norm_num [Real.rpow_neg, Real.rpow_two]

theorem surviving_local_piece (P : Ideal O) [P.IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ P) (j : ℕ) (e : Fin 3) (n b : O)
    (hne : reflectedLocalPiece P hg j e n b ≠ 0) :
    (j ≠ 4 → e = 0) ∧ (j = 4 → e = 1 → n ∈ P) ∧
      (j = 4 → e = 2 → n ∉ P ∧ b ∈ P) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hj
    by_contra he
    exact hne (by simp [reflectedLocalPiece, hj, he])
  · intro hj he
    by_contra hn
    exact hne (by simp [reflectedLocalPiece, exceptionalPiece, hj, he, hn])
  · intro hj he
    by_contra hn
    exact hne (by simp [reflectedLocalPiece, exceptionalPiece, hj, he, hn])

def normWidth (Z : ℝ) (I : Ideal O) : ℝ := Real.logb Z (Ideal.absNorm I : ℝ)

def reflectionWidth {ι : Type*} [Fintype ι] (Z : ℝ)
    (P : ι → Ideal O) (j : ι → ℕ) (e : ι → Fin 3) : ℝ :=
  2 * normWidth Z (∏ i, P i) - normWidth Z (reflectionExtractedDivisor P j e 1) -
    normWidth Z (reflectionExtractedDivisor P j e 0) -
      4 * normWidth Z (reflectionExtractedDivisor P j e 2)

theorem reflectionConductorCost_pos {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) (hP : ∀ i, P i ≠ 0) (j : ι → ℕ) (e : ι → Fin 3) :
    0 < reflectionConductorCost P j e := by
  have hp := actual_ideal_norm_pos (∏ i, P i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hP i))
  have hd (v : Fin 3) := actual_ideal_norm_pos (reflectionExtractedDivisor P j e v)
    (reflectionExtractedDivisor_ne_zero P hP j e v)
  have h₀ := hd 0
  have h₁ := hd 1
  have h₂ := hd 2
  unfold reflectionConductorCost
  positivity

theorem logb_reflectionConductorCost {ι : Type*} [Fintype ι]
    (Z : ℝ) (P : ι → Ideal O) (hP : ∀ i, P i ≠ 0) (j : ι → ℕ) (e : ι → Fin 3) :
    Real.logb Z (reflectionConductorCost P j e) = reflectionWidth Z P j e := by
  have hp := actual_ideal_norm_pos (∏ i, P i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hP i))
  have hd (v : Fin 3) := actual_ideal_norm_pos (reflectionExtractedDivisor P j e v)
    (reflectionExtractedDivisor_ne_zero P hP j e v)
  have h₀ := hd 0
  have h₁ := hd 1
  have h₂ := hd 2
  unfold reflectionConductorCost reflectionWidth normWidth
  rw [Real.logb_div (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (hd 1).ne' (hd 0).ne', Real.logb_pow, Real.logb_pow]
  norm_num
  ring

theorem reflection_charge_width {ι : Type*} [Fintype ι]
    (I F B R : Ideal O) (hI : I ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * (B * F * R))
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I (B * F * R)) (e : ι → Fin 3)
    (Z : ℝ) (hZ : 1 < Z) :
    2 * normWidth Z (rowResidualPart I (B * F * R)) +
      reflectionWidth Z P (fun i => completedLocalExponent I F (P i)) e ≤
      normWidth Z B + 2 * normWidth Z I - normWidth Z (rowPowerfulPart I) +
        normWidth Z F + normWidth Z R := by
  have hi := actual_ideal_norm_pos I hI
  have hf := actual_ideal_norm_pos F hF
  have hb := actual_ideal_norm_pos B hB
  have hr := actual_ideal_norm_pos R hR
  have hp := actual_ideal_norm_pos (rowPowerfulPart I) (rowPowerfulPart_ne_zero I)
  have hx := actual_ideal_norm_pos (rowResidualPart I (B * F * R))
    (squarefreeResidualPart_ne_zero (rowSimplePart I) (B * F * R))
  have hc := reflectionConductorCost_pos P (fun i => NeZero.ne (P i))
    (fun i => completedLocalExponent I F (P i)) e
  have hh := Real.logb_le_logb_of_le hZ (mul_pos (sq_pos_of_pos hx) hc)
    (actual_common_width_charge_label_puncture I F R B hI hF hR hB P hcop hpool hres e)
  rw [Real.logb_mul (by positivity) hc.ne', Real.logb_pow,
    logb_reflectionConductorCost Z P (fun i => NeZero.ne (P i)),
    Real.logb_mul (by positivity) hr.ne', Real.logb_mul (by positivity) hf.ne',
    Real.logb_mul hb.ne' (by positivity), Real.logb_div (by positivity) hp.ne',
    Real.logb_pow] at hh
  unfold normWidth
  norm_num at hh ⊢
  linarith

theorem normWidth_upper (I : Ideal O) (hI : I ≠ 0) (Z C E : ℝ)
    (hZ : 1 < Z) (hC : 0 < C) (h : (Ideal.absNorm I : ℝ) ≤ C * Z ^ E) :
    normWidth Z I ≤ E + Real.logb Z C := by
  have hz0 : 0 < Z := by linarith
  have hh := Real.logb_le_logb_of_le hZ (actual_ideal_norm_pos I hI) h
  rw [Real.logb_mul hC.ne' (by positivity), Real.logb_rpow hz0 (ne_of_gt hZ)] at hh
  unfold normWidth
  linarith

theorem normWidth_lower (I : Ideal O) (Z C E : ℝ)
    (hZ : 1 < Z) (hC : 0 < C) (h : Z ^ E / C ≤ (Ideal.absNorm I : ℝ)) :
    E - Real.logb Z C ≤ normWidth Z I := by
  have hz0 : 0 < Z := by linarith
  have hh := Real.logb_le_logb_of_le hZ (div_pos (Real.rpow_pos_of_pos hz0 E) hC) h
  rwa [Real.logb_div (by positivity) hC.ne', Real.logb_rpow hz0 (ne_of_gt hZ)] at hh

def terminalDualWidth {ι : Type*} [Fintype ι] (Z H za Nstar : ℝ)
    (P : ι → Ideal O) (j : ι → ℕ) (e : ι → Fin 3) : ℝ :=
  2 * H + 2 * normWidth Z (∏ i, P i) + 2 * za - Nstar -
    normWidth Z (reflectionExtractedDivisor P j e 1) -
      3 * normWidth Z (reflectionExtractedDivisor P j e 2)

def widthConstant (B : Ideal O) (Ck CO CH Cf : ℝ) : ℝ :=
  CH ^ 2 * (Ideal.absNorm B : ℝ) * Ck ^ 2 * CO * Cf

theorem logb_widthConstant (Z : ℝ) (B : Ideal O) (hB : B ≠ 0)
    (Ck CO CH Cf : ℝ) (hk : 0 < Ck) (ho : 0 < CO) (hh : 0 < CH) (hf : 0 < Cf) :
    Real.logb Z (widthConstant B Ck CO CH Cf) =
      2 * Real.logb Z CH + normWidth Z B + 2 * Real.logb Z Ck +
        Real.logb Z CO + Real.logb Z Cf := by
  have hb := actual_ideal_norm_pos B hB
  unfold widthConstant normWidth
  rw [Real.logb_mul (by positivity) hf.ne', Real.logb_mul (by positivity) ho.ne',
    Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) hb.ne',
    Real.logb_pow, Real.logb_pow]
  norm_num

theorem terminal_common_width {ι : Type*} [Fintype ι]
    (I F B R : Ideal O) (hI : I ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * (B * F * R))
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I (B * F * R)) (e : ι → Fin 3)
    (Z M O₀ H V za Nstar Ck CO CH Cf : ℝ) (hZ : 1 < Z)
    (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH) (hCf : 0 < Cf)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ))
    (hrow : Z ^ H / CH ≤ (Ideal.absNorm (rowResidualPart I (B * F * R)) : ℝ))
    (hf : (Ideal.absNorm F : ℝ) ≤ Cf * Z ^ V) :
    terminalDualWidth Z H za Nstar P (fun i => completedLocalExponent I F (P i)) e -
      normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 0) -
      normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 2) ≤
        2 * M - O₀ + normWidth Z R + V - Nstar + 2 * za +
          Real.log (widthConstant B Ck CO CH Cf) / Real.log Z := by
  have hb := reflection_charge_width I F B R hI hF hB hR P hcop hpool hres e Z hZ
  have h₁ := normWidth_upper I hI Z Ck M hZ hCk hk
  have h₂ := normWidth_lower (rowPowerfulPart I) Z CO O₀ hZ hCO hpow
  have h₃ := normWidth_lower (rowResidualPart I (B * F * R)) Z CH H hZ hCH hrow
  have h₄ := normWidth_upper F hF Z Cf V hZ hCf hf
  change _ ≤ 2 * M - O₀ + normWidth Z R + V - Nstar + 2 * za +
    Real.logb Z (widthConstant B Ck CO CH Cf)
  rw [logb_widthConstant Z B hB Ck CO CH Cf hCk hCO hCH hCf]
  unfold terminalDualWidth reflectionWidth at *
  linarith

theorem normWidth_nonneg (Z : ℝ) (hZ : 1 < Z) (I : Ideal O) (hI : I ≠ 0) :
    0 ≤ normWidth Z I := Real.logb_nonneg hZ (norm_one_le I hI)

theorem rpow_reflectionWidth {ι : Type*} [Fintype ι]
    (Z : ℝ) (hZ : 1 < Z) (P : ι → Ideal O) (hP : ∀ i, P i ≠ 0)
    (j : ι → ℕ) (e : ι → Fin 3) :
    Z ^ reflectionWidth Z P j e = reflectionConductorCost P j e := by
  rw [← logb_reflectionConductorCost Z P hP j e]
  exact Real.rpow_logb (by linarith) (ne_of_gt hZ) (reflectionConductorCost_pos P hP j e)

theorem width_error_threshold (B : Ideal O) (hB : B ≠ 0)
    (Ck CO CH Cf η : ℝ) (hk : 0 < Ck) (ho : 0 < CO) (hh : 0 < CH)
    (hf : 0 < Cf) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      Real.log (CH * Ck * CO) / Real.log Z ≤ η ∧
      Real.log (widthConstant B Ck CO CH Cf) / Real.log Z ≤ η := by
  have hb := actual_ideal_norm_pos B hB
  obtain ⟨a, ha, h₁⟩ := constant_log_error (CH * Ck * CO) η (by positivity) hη
  obtain ⟨b, hb', h₂⟩ := constant_log_error (widthConstant B Ck CO CH Cf) η
    (by unfold widthConstant; positivity) hη
  exact ⟨max a b, ha.trans_le (le_max_left _ _), fun Z hZ =>
    ⟨h₁ Z ((le_max_left _ _).trans hZ), h₂ Z ((le_max_right _ _).trans hZ)⟩⟩

theorem canonical_active_pool (I Q Q₀ : Ideal O) (hI : I ≠ 0) (hQ : Q ≠ 0)
    (e : FreeReflection.pool I Q Q₀ → Fin 6)
    (P : FreeReflection.reflectionActivePool I Q Q₀ e) :
    P.val ∣ I * Q ∧ ¬ P.val ∣ rowResidualPart I Q ∧
      ConcretePrimeRowBridge.goodLambda ∉ P.val ∧
        ringChar (O ⧸ P.val) ≠ 2 ∧ ¬ Q₀ ≤ P.val := by
  let p : FreeReflection.pool I Q Q₀ :=
    ⟨P.val, FreeReflection.reflectionActivePool_subset I Q Q₀ e P.property⟩
  exact ⟨FreeReflection.pool_divides I Q Q₀ hI hQ p,
    FreeReflection.pool_nonresidual I Q Q₀ p, FreeReflection.pool_good I Q Q₀ p,
    FreeReflection.pool_odd I Q Q₀ p, FreeReflection.pool_free I Q Q₀ p⟩

theorem surviving_inactive_exponent (I F Q Q₀ : Ideal O)
    (e : FreeReflection.pool I Q Q₀ → Fin 6)
    (hne : FreeReflection.reflectionSixInactiveWeight I F Q Q₀ e ≠ 0)
    (P : FreeReflection.pool I Q Q₀) (hP : ¬ reflectionSixActive (e P)) :
    completedLocalExponent I F P.val = 0 := by
  have he : reflectionSixValid e := by
    by_contra he
    exact hne (by simp [FreeReflection.reflectionSixInactiveWeight, he])
  have hp : FreeReflection.reflectionInactiveStratumWeight I F Q Q₀ (reflectionSixSupport e) ≠ 0 := by
    simpa only [FreeReflection.reflectionSixInactiveWeight, ite_eq_left he] using hne
  rw [FreeReflection.reflectionInactiveStratumWeight_formula] at hp
  have hm : P ∈ (Finset.univ : Finset (FreeReflection.pool I Q Q₀)) \ reflectionSixSupport e := by
    simp [reflectionSixSupport, hP]
  have ht := (Finset.prod_ne_zero_iff.mp hp) P hm
  by_contra hj
  exact ht (by simp [hj])

theorem surviving_reflected_branch {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ P i)
    (I F : Ideal O) (e : ι → Fin 3) (n b : O)
    (hne : reflectedBranch P hg (fun i => completedLocalExponent I F (P i)) e n b ≠ 0) :
    ∀ i, (completedLocalExponent I F (P i) ≠ 4 → e i = 0) ∧
      (completedLocalExponent I F (P i) = 4 → e i = 1 → n ∈ P i) ∧
      (completedLocalExponent I F (P i) = 4 → e i = 2 → n ∉ P i ∧ b ∈ P i) := by
  intro i
  apply surviving_local_piece (P i) (hg i) _ (e i) n b
  exact (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)

theorem canonical_terminal_common_width
    (I F B R Q₀ : Ideal O) (hI : I ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (e : FreeReflection.pool I (B * F * R) Q₀ → Fin 6)
    (Z M O₀ H V za Nstar Ck CO CH Cf : ℝ) (hZ : 1 < Z)
    (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH) (hCf : 0 < Cf)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ))
    (hrow : Z ^ H / CH ≤ (Ideal.absNorm (rowResidualPart I (B * F * R)) : ℝ))
    (hf : (Ideal.absNorm F : ℝ) ≤ Cf * Z ^ V) :
    let P := fun p : FreeReflection.reflectionActivePool I (B * F * R) Q₀ e => p.val
    let j := fun p : FreeReflection.reflectionActivePool I (B * F * R) Q₀ e =>
      completedLocalExponent I F p.val
    let l := FreeReflection.reflectionActiveLabel I (B * F * R) Q₀ e
    terminalDualWidth Z H za Nstar P j l -
      normWidth Z (reflectionExtractedDivisor P j l 0) -
      normWidth Z (reflectionExtractedDivisor P j l 2) ≤
        2 * M - O₀ + normWidth Z R + V - Nstar + 2 * za +
          Real.log (widthConstant B Ck CO CH Cf) / Real.log Z := by
  let Q := B * F * R
  have hQ : Q ≠ 0 := mul_ne_zero (mul_ne_zero hB hF) hR
  let A := FreeReflection.reflectionActivePool I Q Q₀ e
  let : ∀ p : A, p.val.IsMaximal := fun p => FreeReflection.pool_maximal I Q Q₀
    ⟨p.val, FreeReflection.reflectionActivePool_subset I Q Q₀ e p.property⟩
  have hcop : Pairwise (fun p q : A => IsCoprime p.val q.val) := by
    intro p q hpq
    exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hpq)
  exact terminal_common_width I F B R hI hF hB hR (fun p : A => p.val) hcop
    (fun p => (canonical_active_pool I Q Q₀ hI hQ e p).1)
    (fun p => (canonical_active_pool I Q Q₀ hI hQ e p).2.1)
    (FreeReflection.reflectionActiveLabel I Q Q₀ e)
    Z M O₀ H V za Nstar Ck CO CH Cf hZ hCk hCO hCH hCf hk hpow hrow hf

def hybridSaving (v za : ℝ) : ℝ := min v (min za ((v + za) / 3))

def reflectedExponent (O₀ H S₀ B₀ za v ell el Td : ℝ) : ℝ :=
  O₀ / 2 + max H (v + ell) - S₀ - B₀ + za - hybridSaving v za - ell -
    2 * el / 3 - max 0 (Td - v - 3 * ell - el) / 2

theorem hybridSaving_nonneg {v za : ℝ} (hv : 0 ≤ v) (hz : 0 ≤ za) :
    0 ≤ hybridSaving v za := by unfold hybridSaving; positivity

theorem hybridSaving_half {v za : ℝ} (hv : 0 ≤ v)
    (hu : hybridSaving v za ≠ za) : v / 2 ≤ hybridSaving v za := by
  unfold hybridSaving at *
  rcases le_total v (min za ((v + za) / 3)) with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h] at *
    rcases le_total za ((v + za) / 3) with hz | hz
    · exact (hu (min_eq_left hz)).elim
    · rw [min_eq_right hz]
      linarith

theorem terminal_width_from_invariant
    {F₀ N V M Q z₀ c O₀ za Nstar hhat d η Td S₀ B₀ : ℝ}
    (hinv : CanonicalMargins F₀ M Q z₀ c) (hF : F₀ = N + V)
    (hscale : Nstar = N - 3 * hhat) (hV : V ≤ d) (hh : hhat ≤ d + η)
    (hwidth : Td - S₀ - B₀ ≤ 2 * M - O₀ + Q + V - Nstar + 2 * za + η) :
    Td - S₀ - B₀ ≤ M - O₀ + 2 * za - z₀ - c + 5 * d + 4 * η := by
  have hi := hinv.1
  linarith

theorem reflected_row_bound {O₀ H S₀ B₀ za v ell el Td M η : ℝ}
    (hO : 0 ≤ O₀) (hS : 0 ≤ S₀) (hB : 0 ≤ B₀)
    (hz : 0 ≤ za) (hv : 0 ≤ v) (hl : 0 ≤ ell) (he : -η ≤ el)
    (hrow : v + ell ≤ H) (hH : H ≤ M - O₀ + η) :
    reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤ M + za + 5 * η / 3 := by
  have hu := hybridSaving_nonneg hv hz
  have hm := le_max_left 0 (Td - v - 3 * ell - el)
  unfold reflectedExponent
  rw [max_eq_left hrow]
  linarith

theorem reflected_column_full_bound {O₀ H S₀ B₀ za v ell el Td η τ : ℝ}
    (hl : 0 ≤ ell) (he : -η ≤ el) (hcol : H ≤ v + ell)
    (hu : hybridSaving v za = za) (hret : v + 3 * ell + el ≤ Td + τ) :
    reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤
      O₀ / 2 + (Td - S₀ - B₀) + 5 * η / 3 + τ := by
  have hm := le_max_left 0 (Td - v - 3 * ell - el)
  unfold reflectedExponent
  rw [max_eq_right hcol, hu]
  linarith

theorem reflected_column_partial_bound {O₀ H S₀ B₀ za v ell el Td η τ : ℝ}
    (hS : 0 ≤ S₀) (hB : 0 ≤ B₀) (hv : 0 ≤ v) (hl : 0 ≤ ell)
    (he : -η ≤ el) (hcol : H ≤ v + ell)
    (hu : hybridSaving v za ≠ za) (hret : v + 3 * ell + el ≤ Td + τ) :
    reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤
      O₀ / 2 + (Td - S₀ - B₀) / 2 + za + 7 * η / 6 + τ / 2 := by
  have hu' := hybridSaving_half hv hu
  have hm := le_max_left 0 (Td - v - 3 * ell - el)
  unfold reflectedExponent
  rw [max_eq_right hcol]
  linarith

theorem reflected_terminal_cases
    {F₀ M Q z₀ c O₀ H S₀ B₀ za v ell el Td d η τ : ℝ}
    (hinv : CanonicalMargins F₀ M Q z₀ c) (hQ : 0 ≤ Q)
    (hO : 0 ≤ O₀) (hS : 0 ≤ S₀) (hB : 0 ≤ B₀)
    (hz : 0 ≤ za) (hzcap : za ≤ z₀) (hv : 0 ≤ v) (hl : 0 ≤ ell)
    (he : -η ≤ el) (hret : v + 3 * ell + el ≤ Td + τ)
    (hH : H ≤ M - O₀ + η)
    (hT : Td - S₀ - B₀ ≤ M - O₀ + 2 * za - z₀ - c + 5 * d + 4 * η) :
    (v + ell ≤ H → reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤ F₀ - c + 5 * η / 3) ∧
    (H ≤ v + ell → hybridSaving v za = za →
      reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤ F₀ - 2 * c + 5 * d + 17 * η / 3 + τ) ∧
    (H ≤ v + ell → hybridSaving v za ≠ za →
      reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤
        F₀ - M / 4 - 3 * c / 4 + 5 * d / 2 + 19 * η / 6 + τ / 2) := by
  obtain ⟨hi₁, hi₂⟩ := hinv
  refine ⟨?_, ?_, ?_⟩
  · intro hrow
    have hb := reflected_row_bound hO hS hB hz hv hl he hrow hH (Td := Td)
    linarith
  · intro hcol hu
    have hb := reflected_column_full_bound hl he hcol hu hret (O₀ := O₀) (S₀ := S₀) (B₀ := B₀)
    linarith
  · intro hcol hu
    have hb := reflected_column_partial_bound hS hB hv hl he hcol hu hret (O₀ := O₀)
    linarith

theorem reflected_terminal_saving
    {F₀ M Q z₀ c cstar O₀ H S₀ B₀ za v ell el Td d η τ π : ℝ}
    (hinv : CanonicalMargins F₀ M Q z₀ c) (hQ : 0 ≤ Q) (hM : 0 ≤ M)
    (hO : 0 ≤ O₀) (hS : 0 ≤ S₀) (hB : 0 ≤ B₀)
    (hz : 0 ≤ za) (hzcap : za ≤ z₀) (hv : 0 ≤ v) (hl : 0 ≤ ell)
    (he : -η ≤ el) (hret : v + 3 * ell + el ≤ Td + τ)
    (hH : H ≤ M - O₀ + η)
    (hT : Td - S₀ - B₀ ≤ M - O₀ + 2 * za - z₀ - c + 5 * d + 4 * η)
    (hc : 0 < cstar) (hmargin : cstar / 2 ≤ c) (hd : d ≤ cstar / 200)
    (hη : η ≤ cstar / 1000) (hτ : τ ≤ cstar / 1000) (hπ : π ≤ cstar / 1000) :
    reflectedExponent O₀ H S₀ B₀ za v ell el Td + π ≤ F₀ - cstar / 4 := by
  obtain ⟨hr, hf, hp⟩ := reflected_terminal_cases hinv hQ hO hS hB hz hzcap hv hl he hret hH hT
  rcases le_total (v + ell) H with h | h
  · have := hr h
    linarith
  · by_cases hu : hybridSaving v za = za
    · have := hf h hu
      linarith
    · have := hp h hu
      linarith

def ramifiedWidth (Z : ℝ) (m : ℕ) : ℝ := ((m : ℝ) - 4) * Real.logb Z 3

theorem rpow_ramifiedWidth (Z : ℝ) (hZ : 1 < Z) (m : ℕ) :
    Z ^ ramifiedWidth Z m = (3 : ℝ) ^ ((m : ℝ) - 4) := by
  unfold ramifiedWidth
  rw [mul_comm, Real.rpow_mul (by linarith : 0 ≤ Z),
    Real.rpow_logb (by linarith : 0 < Z) (ne_of_gt hZ) (by norm_num : (0 : ℝ) < 3)]

theorem fractionalThetaPoint_norm_width (Z : ℝ) (hZ : 1 < Z)
    (u : Oˣ) (m : ℕ) (n b : O) :
    ‖fractionalThetaPoint u m n b‖ ^ 2 =
      Z ^ ramifiedWidth Z m * ‖ConcreteTraceCRT.eisEmbedding n‖ ^ 2 *
        (‖ConcreteTraceCRT.eisEmbedding b‖ ^ 2) ^ 3 := by
  rw [rpow_ramifiedWidth Z hZ]
  exact fractionalThetaPoint_norm_sq u m n b

theorem ramified_width_threshold (η : ℝ) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → ∀ m : ℕ, -η ≤ ramifiedWidth Z m := by
  obtain ⟨Z₀, hZ₀, hlog⟩ := constant_log_error ((3 : ℝ) ^ (4 : ℕ)) η (by norm_num) hη
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZ m
  have hz := hZ₀.trans_le hZ
  have hl := hlog Z hZ
  change Real.logb Z ((3 : ℝ) ^ (4 : ℕ)) ≤ η at hl
  rw [Real.logb_pow] at hl
  have hn : 0 ≤ Real.logb Z 3 := Real.logb_nonneg hz (by norm_num)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold ramifiedWidth
  norm_num at hl
  nlinarith

theorem terminal_error_threshold (B : Ideal O) (hB : B ≠ 0)
    (Ck CO CH Cf η : ℝ) (hk : 0 < Ck) (ho : 0 < CO) (hh : 0 < CH)
    (hf : 0 < Cf) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      Real.log (CH * Ck * CO) / Real.log Z ≤ η ∧
      Real.log (widthConstant B Ck CO CH Cf) / Real.log Z ≤ η ∧
      ∀ m : ℕ, -η ≤ ramifiedWidth Z m := by
  obtain ⟨a, ha, h₁⟩ := width_error_threshold B hB Ck CO CH Cf η hk ho hh hf hη
  obtain ⟨b, hb, h₂⟩ := ramified_width_threshold η hη
  refine ⟨max a b, ha.trans_le (le_max_left _ _), fun Z hZ => ?_⟩
  exact ⟨(h₁ Z ((le_max_left _ _).trans hZ)).1,
    (h₁ Z ((le_max_left _ _).trans hZ)).2, h₂ Z ((le_max_right _ _).trans hZ)⟩

theorem actual_terminal_saving {ι : Type*} [Fintype ι]
    (I F B R : Ideal O) (hI : I ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * (B * F * R))
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I (B * F * R)) (e : ι → Fin 3)
    (Z F₀ N V M z₀ c cstar O₀ H za Nstar hhat v ell el d η τ π Ck CO CH Cf : ℝ)
    (hZ : 1 < Z) (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH) (hCf : 0 < Cf)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ))
    (hrow : Z ^ H / CH ≤ (Ideal.absNorm (rowResidualPart I (B * F * R)) : ℝ))
    (hf : (Ideal.absNorm F : ℝ) ≤ Cf * Z ^ V)
    (hlogH : Real.log (CH * Ck * CO) / Real.log Z ≤ η)
    (hlogT : Real.log (widthConstant B Ck CO CH Cf) / Real.log Z ≤ η)
    (hinv : CanonicalMargins F₀ M (normWidth Z R) z₀ c) (hF₀ : F₀ = N + V)
    (hscale : Nstar = N - 3 * hhat) (hV : V ≤ d) (hh : hhat ≤ d + η)
    (hM : 0 ≤ M) (hO : 0 ≤ O₀) (hz : 0 ≤ za) (hzcap : za ≤ z₀)
    (hv : 0 ≤ v) (hl : 0 ≤ ell) (he : -η ≤ el)
    (hret : v + 3 * ell + el ≤
      terminalDualWidth Z H za Nstar P (fun i => completedLocalExponent I F (P i)) e + τ)
    (hc : 0 < cstar) (hmargin : cstar / 2 ≤ c) (hd : d ≤ cstar / 200)
    (hη : η ≤ cstar / 1000) (hτ : τ ≤ cstar / 1000) (hπ : π ≤ cstar / 1000) :
    reflectedExponent O₀ H
      (normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 0))
      (normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 2))
      za v ell el (terminalDualWidth Z H za Nstar P (fun i => completedLocalExponent I F (P i)) e) + π ≤
        F₀ - cstar / 4 := by
  have hH := physical_residual_width I (B * F * R) hI Z M O₀ H Ck CO CH hZ hCk hCO hCH hk hpow hrow
  have hT := terminal_common_width I F B R hI hF hB hR P hcop hpool hres e
    Z M O₀ H V za Nstar Ck CO CH Cf hZ hCk hCO hCH hCf hk hpow hrow hf
  have hT' := terminal_width_from_invariant (O₀ := O₀) (za := za) (η := η)
    (Td := terminalDualWidth Z H za Nstar P (fun i => completedLocalExponent I F (P i)) e)
    (S₀ := normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 0))
    (B₀ := normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 2))
    hinv hF₀ hscale hV hh (hT.trans (by linarith))
  exact reflected_terminal_saving hinv (normWidth_nonneg Z hZ R hR) hM hO
    (normWidth_nonneg Z hZ _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) _ e 0))
    (normWidth_nonneg Z hZ _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) _ e 2))
    hz hzcap hv hl he hret (by linarith) hT' hc hmargin hd hη hτ hπ

theorem residual_admissible_of_fixed_bad (I F B R : Ideal O)
    (hbad : ∀ P ∈ fixedBadPrimes, P ∣ B) :
    Admissible (rowResidualPart I (B * F * R)) := by
  apply rowResidualPart_admissible
  intro P hP
  exact (hbad P hP).trans ((dvd_mul_right B F).trans (dvd_mul_right (B * F) R))

def canonicalDualWidth (I F B R Q₀ : Ideal O)
    (e : FreeReflection.pool I (B * F * R) Q₀ → Fin 6)
    (Z H za Nstar : ℝ) : ℝ :=
  terminalDualWidth Z H za Nstar
    (fun p : FreeReflection.reflectionActivePool I (B * F * R) Q₀ e => p.val)
    (fun p => completedLocalExponent I F p.val)
    (FreeReflection.reflectionActiveLabel I (B * F * R) Q₀ e)

def canonicalExtractedWidth (I F B R Q₀ : Ideal O)
    (e : FreeReflection.pool I (B * F * R) Q₀ → Fin 6) (Z : ℝ) (a : Fin 3) : ℝ :=
  normWidth Z (reflectionExtractedDivisor
    (fun p : FreeReflection.reflectionActivePool I (B * F * R) Q₀ e => p.val)
    (fun p => completedLocalExponent I F p.val)
    (FreeReflection.reflectionActiveLabel I (B * F * R) Q₀ e) a)

theorem canonical_terminal_saving
    (I F B R Q₀ : Ideal O) (hI : I ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (hbad : ∀ P ∈ fixedBadPrimes, P ∣ B)
    (e : FreeReflection.pool I (B * F * R) Q₀ → Fin 6) (m : ℕ)
    (Z F₀ N V M z₀ c cstar O₀ H za Nstar hhat v ell d η τ π Ck CO CH Cf : ℝ)
    (hZ : 1 < Z) (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH) (hCf : 0 < Cf)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ))
    (hrow : Z ^ H / CH ≤ (Ideal.absNorm (rowResidualPart I (B * F * R)) : ℝ))
    (hf : (Ideal.absNorm F : ℝ) ≤ Cf * Z ^ V)
    (herr : Real.log (CH * Ck * CO) / Real.log Z ≤ η ∧
      Real.log (widthConstant B Ck CO CH Cf) / Real.log Z ≤ η ∧
      ∀ a : ℕ, -η ≤ ramifiedWidth Z a)
    (hinv : CanonicalMargins F₀ M (normWidth Z R) z₀ c) (hF₀ : F₀ = N + V)
    (hscale : Nstar = N - 3 * hhat) (hV : V ≤ d) (hh : hhat ≤ d + η)
    (hM : 0 ≤ M) (hO : 0 ≤ O₀) (hz : 0 ≤ za) (hzcap : za ≤ z₀)
    (hv : 0 ≤ v) (hl : 0 ≤ ell)
    (hret : v + 3 * ell + ramifiedWidth Z m ≤ canonicalDualWidth I F B R Q₀ e Z H za Nstar + τ)
    (hc : 0 < cstar) (hmargin : cstar / 2 ≤ c) (hd : d ≤ cstar / 200)
    (hη : η ≤ cstar / 1000) (hτ : τ ≤ cstar / 1000) (hπ : π ≤ cstar / 1000) :
    Admissible (rowResidualPart I (B * F * R)) ∧
    reflectedExponent O₀ H (canonicalExtractedWidth I F B R Q₀ e Z 0)
      (canonicalExtractedWidth I F B R Q₀ e Z 2) za v ell (ramifiedWidth Z m)
      (canonicalDualWidth I F B R Q₀ e Z H za Nstar) + π ≤ F₀ - cstar / 4 := by
  refine ⟨residual_admissible_of_fixed_bad I F B R hbad, ?_⟩
  let Q := B * F * R
  have hQ : Q ≠ 0 := mul_ne_zero (mul_ne_zero hB hF) hR
  let A := FreeReflection.reflectionActivePool I Q Q₀ e
  let : ∀ p : A, p.val.IsMaximal := fun p => FreeReflection.pool_maximal I Q Q₀
    ⟨p.val, FreeReflection.reflectionActivePool_subset I Q Q₀ e p.property⟩
  have hcop : Pairwise (fun p q : A => IsCoprime p.val q.val) := by
    intro p q hpq
    exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hpq)
  exact actual_terminal_saving I F B R hI hF hB hR (fun p : A => p.val) hcop
    (fun p => (canonical_active_pool I Q Q₀ hI hQ e p).1)
    (fun p => (canonical_active_pool I Q Q₀ hI hQ e p).2.1)
    (FreeReflection.reflectionActiveLabel I Q Q₀ e)
    Z F₀ N V M z₀ c cstar O₀ H za Nstar hhat v ell (ramifiedWidth Z m) d η τ π Ck CO CH Cf
    hZ hCk hCO hCH hCf hk hpow hrow hf herr.1 herr.2.1 hinv hF₀ hscale hV hh hM hO hz hzcap
    hv hl (herr.2.2 m) hret hc hmargin hd hη hτ hπ

end SevenEighths.InverseTerminalWidths

end

end OAI
end OAIOriginalModule0765

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowReflectedExponent
Source SHA256: ab497dc85da3ae547aac9dfcf8a0b06c23a498be18bf8648bf5657aa1239a6fd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0766


namespace OAI

namespace SevenEighths.ProbeLowReflected
open InverseTerminalWidths

lemma hybrid_half_with_error {v za ε : ℝ} (hv : -ε≤v) (hε : 0≤ε)
    (hu : hybridSaving v za≠za) : v/2-ε/2≤hybridSaving v za := by
  unfold hybridSaving at *
  rcases le_total v (min za ((v+za)/3)) with h|h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h] at *
    rcases le_total za ((v+za)/3) with hz|hz
    · exact (hu (min_eq_left hz)).elim
    · rw [min_eq_right hz]
      have hzv := min_le_left za ((v+za)/3)
      rw [min_eq_right hz] at hzv
      linarith

lemma retained_kernel_quarter (Td y : ℝ) : Td/4≤y/4+max 0 (Td-y)/2 := by
  have h0 := le_max_left 0 (Td-y)
  have h1 := le_max_right 0 (Td-y)
  linarith

theorem compensated_reflected_exponent (d O₀ H A₀ N₀ S₀ B₀ za v ell el θ ε : ℝ)
    (hd : 0≤d) (_hd1 : d≤1/6) (hε : 0≤ε)
    (hO : -ε≤O₀) (hH : H≤(5/6-2*d)-O₀+ε)
    (hA : 2*A₀≤O₀+ε) (hN : 0≤N₀) (hNA : N₀≤A₀)
    (hS : 0≤S₀) (hB : 0≤B₀) (hz : za≤1/6-d)
    (hv : -ε≤v) (hl : -ε≤ell) (he : -ε≤el) (hθ : |θ|≤ε)
    (hret : v+3*ell+el≤2*H+2*A₀+2*za-1-(1/6-d)-θ-N₀-3*B₀+ε) :
    reflectedExponent O₀ H S₀ B₀ za v ell el
      (2*H+2*A₀+2*za-1-(1/6-d)-θ-N₀-3*B₀)≤5/6-2*d+20*ε := by
  let Td := 2*H+2*A₀+2*za-1-(1/6-d)-θ-N₀-3*B₀
  have hθlo : -ε≤θ := (abs_le.mp hθ).1
  have hθhi : θ≤ε := (abs_le.mp hθ).2
  have hTd : Td≤H-3*d+3*ε := by dsimp [Td];linarith
  have hcol : v+ell≤H+7*ε := by dsimp [Td] at hTd;linarith
  have hmax : max H (v+ell)≤H+7*ε := max_le (by linarith) hcol
  have hk := le_max_left 0 (Td-v-3*ell-el)
  by_cases hu : hybridSaving v za=za
  · unfold reflectedExponent
    rw [hu]
    change O₀/2+max H (v+ell)-S₀-B₀+za-za-ell-2*el/3-max 0 (Td-v-3*ell-el)/2≤_
    linarith
  · have hhalf := hybrid_half_with_error hv hε hu
    have hquarter := retained_kernel_quarter Td (v+3*ell+el)
    have hcharge : Td/4-17*ε/12≤
        hybridSaving v za+ell+2*el/3+max 0 (Td-v-3*ell-el)/2 := by
      have heq : Td-(v+3*ell+el)=Td-v-3*ell-el := by ring
      rw [heq] at hquarter
      linarith
    have hbound : reflectedExponent O₀ H S₀ B₀ za v ell el Td≤
        O₀/2+H-S₀-B₀+za-Td/4+(7+17/12)*ε := by
      unfold reflectedExponent
      linarith
    change reflectedExponent O₀ H S₀ B₀ za v ell el Td≤_
    apply hbound.trans
    dsimp [Td]
    linarith

end SevenEighths.ProbeLowReflected

end OAI
end OAIOriginalModule0766

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowReflectedLength
Source SHA256: 4b78ca2d011881e543b7f2d9feb1e4de13b9cc61aba98524561a84dcc549908c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0767


namespace OAI

namespace SevenEighths.ProbeLowReflected
open InverseTerminalWidths

theorem compensated_reflected_exponent_with_length (d ell₀ O₀ H A₀ N₀ S₀ B₀ za v ell el θ ε : ℝ)
    (hd : 0≤d) (_hd1 : d≤1/6) (hε : 0≤ε)
    (hO : -ε≤O₀) (hH : H≤(5/6-2*d)-O₀+ε)
    (hA : 2*A₀≤O₀+ε) (hN : 0≤N₀) (hNA : N₀≤A₀)
    (hS : 0≤S₀) (hB : 0≤B₀) (hell : ell₀≤1/6-d+ε) (hz : za≤ell₀+ε)
    (hv : -ε≤v) (hl : -ε≤ell) (he : -ε≤el) (hθ : |θ|≤ε)
    (hret : v+3*ell+el≤2*H+2*A₀+2*za-1-ell₀-θ-N₀-3*B₀+ε) :
    reflectedExponent O₀ H S₀ B₀ za v ell el
      (2*H+2*A₀+2*za-1-ell₀-θ-N₀-3*B₀)≤5/6-2*d+40*ε := by
  let Td := 2*H+2*A₀+2*za-1-ell₀-θ-N₀-3*B₀
  have hθlo : -ε≤θ := (abs_le.mp hθ).1
  have hθhi : θ≤ε := (abs_le.mp hθ).2
  have hTd : Td≤H-3*d+6*ε := by dsimp [Td];linarith
  have hcol : v+ell≤H+10*ε := by dsimp [Td] at hTd;linarith
  have hmax : max H (v+ell)≤H+10*ε := max_le (by linarith) hcol
  have hk := le_max_left 0 (Td-v-3*ell-el)
  by_cases hu : hybridSaving v za=za
  · unfold reflectedExponent
    rw [hu]
    change O₀/2+max H (v+ell)-S₀-B₀+za-za-ell-2*el/3-max 0 (Td-v-3*ell-el)/2≤_
    linarith
  · have hhalf := hybrid_half_with_error hv hε hu
    have hquarter := retained_kernel_quarter Td (v+3*ell+el)
    have hcharge : Td/4-17*ε/12≤
        hybridSaving v za+ell+2*el/3+max 0 (Td-v-3*ell-el)/2 := by
      have heq : Td-(v+3*ell+el)=Td-v-3*ell-el := by ring
      rw [heq] at hquarter
      linarith
    have hbound : reflectedExponent O₀ H S₀ B₀ za v ell el Td≤
        O₀/2+H-S₀-B₀+za-Td/4+(10+17/12)*ε := by
      unfold reflectedExponent
      linarith
    change reflectedExponent O₀ H S₀ B₀ za v ell el Td≤_
    apply hbound.trans
    dsimp [Td]
    linarith

end SevenEighths.ProbeLowReflected

end OAI
end OAIOriginalModule0767

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.WholePriorityRapidTail
Source SHA256: eb84141144393fab491600905024ba2daa9aede9f8974dbbd6a2958aa2f1613e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0768




namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseWholePriorityRapidTail
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseMoment InversePrincipalEnergy InverseSecondPrincipalCaller
local notation "O" => ActualEisensteinCubic.O

theorem marked_rapid_tail (Lcap tau saving : ℝ) (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct : ℝ),0<Ct ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F : Finset ι) (Ψ : O→*ℂ), (∀u,‖Ψ u‖≤1) →
      ∀ (m c d : O),d≠0 → ∀ (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      ∀ (om W : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo)
      (hs : Function.support om⊆Set.Icc lo hi) (negative : Bool) (height X M Y Z : ℝ)
      (R : Finset ι→Finset ι→ℝ),
      0<X → hi≤Real.exp M → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
      (∀G∈F.powerset,∀E:G.powerset,
        correlatedSecondRadius p d G E.val (X*Real.exp M) Y (Z^tau)≤R G E.val) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d
        (markedRadial p slots lists a ∅ (principalWindow om lo hi hlo hs negative height) X) W Y
        (fun G E=>childFrequencyBall (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E) (R G E))‖≤
      Ct*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*(SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_rapid_correlated_tail Lcap tau (saving+Lcap) hLcap htau
  obtain ⟨Cm,hCm,hmark⟩ := marked_radial_uniform_bound (1/2) (by norm_num)
  refine ⟨s,Ct*Cm^2,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc F Ψ hΨ m c d hd slots lists a hslots ha
    om W lo hi hlo hs negative height X M Y Z R hX hhi hZ hY hL hy hyi hl hR
  let L:=X*Real.exp M
  have hLpos : 0<L := mul_pos hX (Real.exp_pos _)
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hv := principalWindow_upper om lo hi hlo hs M hhi negative height
  have hm := hmark p hp hcop slots lists a hslots ha ∅
    (principalWindow om lo hi hlo hs negative height) X M hX hv
  simp only [Finset.card_empty,pow_zero,one_mul,principalWindow_seminorm_zero] at hm
  have ht := htail p hp hg hinj hc F Ψ hΨ m c d hd _ W Z
    (Cm*L^(1/2:ℝ)*SchwartzMap.seminorm ℝ 0 0 om) Y L R hZ (by positivity) hY hL hy hyi hl hm
    (markedRadial_support p slots lists a ∅ _ X M hX hv) hR
  have hp : (L^(1/2:ℝ))^2=L := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hLpos.le]
    norm_num
  have habsorb : L*Z^(-(saving+Lcap))≤Z^(-saving) := by
    calc
      _≤Z^Lcap*Z^(-(saving+Lcap)) := mul_le_mul_of_nonneg_right hl (by positivity)
      _=Z^(-saving) := by rw [←Real.rpow_add hz];congr 1;ring
  apply ht.trans
  calc
    _=(Ct*Cm^2*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*(SchwartzMap.seminorm ℝ 0 0 om)^2)*
        (L*Z^(-(saving+Lcap))) := by rw [mul_pow,mul_pow,hp];ring
    _≤_ := by
      exact mul_le_mul_of_nonneg_left habsorb (by positivity)

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def wholePriorityTailEnergy (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (om W : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo)
    (hs : Function.support om⊆Set.Icc lo hi) (X t Y : ℝ)
    (R : Finset ι→Finset ι→Finset ι→ℝ) : ℝ :=
  let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  (32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
    (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑core:FirstCoreIndex,
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit negative Ψ m D core‖*
      ∑J∈slots.powerset,‖primeMark J lists a (A∪D)‖^2*
        ‖secondSourceTail p hp hg hinj pool
          (firstCoreTwist negative (if negative then r.1 else r.2) Ψ core)
          ((m*b0Label p b.support (fun i=>b.leftExponent i+b.rightExponent i)
            b.leftBit b.rightBit)*∏i∈D,p i)
          ((∏i∈C,p i)*jLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i)
            b.leftBit b.rightBit) d
          (markedRadial p (slots\J) (fun i=>lists i\(A∪D)) a ∅
            (principalWindow om lo hi hlo hs negative t) X) W Y
          (fun G E=>childFrequencyBall (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E) (R D G E))‖

theorem whole_priority_tail_weighted (Lcap tau saving : ℝ) (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct : ℝ),0<Ct ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
      (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
      (selector : Finset ι→ℂ) (om W : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo)
      (hs : Function.support om⊆Set.Icc lo hi) (M t X Y Z : ℝ)
      (R : Finset ι→Finset ι→Finset ι→ℝ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀u,‖Ψ u‖≤1) → d≠0 → hi≤Real.exp M → 0<X → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
      (∀D∈pool.powerset,selector D≠0 → ∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p d G E.val (X*Real.exp M) Y (Z^tau)≤R D G E.val) →
      wholePriorityTailEnergy p hp hg hinj pool b C extra negative Ψ m d slots lists a
        selector om W lo hi hlo hs X t Y R ≤
      Ct*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(SchwartzMap.seminorm ℝ 0 0 om)^2)*
        Z^(-saving)*(∑D∈pool.powerset,‖selector D‖*primeProductNorm p
          ((extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := marked_rapid_tail Lcap tau saving hLcap htau
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_small_power (1/2) (by norm_num)
  refine ⟨s,((32*512:ℝ)^2*512)*Ct*Cm^2,by positivity,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc pool b C extra negative Ψ m d slots lists a selector
    om W lo hi hlo hs M t X Y Z R hslots ha hΨ hd hhi hX hZ hY hL hy hyi hl hR
  let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  let P:=Ct*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*(SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving)
  have hP : 0≤P := by dsimp [P];positivity
  have hn (D : Finset ι) : 0≤primeProductNorm p (A∪D) := (primeProductNorm_pos p hp _).le
  have hm (J : Finset σ) (hJ : J∈slots.powerset) (D : Finset ι) :
      ‖primeMark J lists a (A∪D)‖^2≤Cm^2*primeProductNorm p (A∪D) := by
    have hj:=Finset.mem_powerset.mp hJ
    have hh:=hmark p hp hcop J lists a (fun i hi j hj' hij=>hslots (hj hi) (hj hj') hij)
      (fun i hi=>ha i (hj hi)) (A∪D)
    have he : ((primeProductNorm p (A∪D))^(1/2:ℝ))^2=primeProductNorm p (A∪D) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (hn D)]
      norm_num
    calc
      _≤(Cm*(primeProductNorm p (A∪D))^(1/2:ℝ))^2 := pow_le_pow_left₀ (norm_nonneg _) hh 2
      _=_ := by rw [mul_pow,he]
  unfold wholePriorityTailEnergy
  dsimp only
  calc
    _≤(32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
      (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑core:FirstCoreIndex,
        ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative Ψ m D core‖*
        ((2:ℝ)^slots.card*(Cm^2*primeProductNorm p (A∪D)*P)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro D hD
      by_cases hsel : selector D=0
      · simp only [hsel,norm_zero,mul_zero,zero_mul,le_refl]
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro core hcore
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        calc
          _≤∑J∈slots.powerset,Cm^2*primeProductNorm p (A∪D)*P := by
            apply Finset.sum_le_sum
            intro J hJ
            have ht := htail p hp hcop hg hinj hc pool
              (firstCoreTwist negative (if negative then r.1 else r.2) Ψ core)
              (fun z=>(firstCoreTwist_norm_le negative _ Ψ core z).trans (hΨ z))
              ((m*b0Label p b.support (fun i=>b.leftExponent i+b.rightExponent i)
                b.leftBit b.rightBit)*∏i∈D,p i)
              ((∏i∈C,p i)*jLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i)
                b.leftBit b.rightBit) d hd (slots\J) (fun i=>lists i\(A∪D)) a
              (residual_lists_pairwise slots J lists A D hslots)
              (residual_coeff_bound slots J lists a A D ha) om W lo hi hlo hs negative t X M Y Z (R D)
              hX hhi hZ hY hL hy hyi hl (hR D hD hsel)
            exact mul_le_mul (hm J hJ D) ht (norm_nonneg _) (mul_nonneg (sq_nonneg _) (hn D))
          _=_ := by simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    _≤(32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
      (‖crossCoeff r.1 r.2‖*‖selector D‖)*
        ((32*512)*((2:ℝ)^slots.card*(Cm^2*primeProductNorm p (A∪D)*P))) := by
      gcongr with r hr D hD
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (firstCoreOuter_mass p hg b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D (hΨ _))
        (mul_nonneg (pow_nonneg (by norm_num) _)
          (mul_nonneg (mul_nonneg (sq_nonneg _) (hn D)) hP))
    _=((32*512:ℝ)^2)*((2:ℝ)^slots.card)^2*Cm^2*P*
      (∑r:RayCharacter×RayCharacter,‖crossCoeff r.1 r.2‖)*
      (∑D∈pool.powerset,‖selector D‖*primeProductNorm p (A∪D)) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm (s:=pool.powerset)]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro D hD
      ring
    _≤((32*512:ℝ)^2)*((2:ℝ)^slots.card)^2*Cm^2*P*512*
      (∑D∈pool.powerset,‖selector D‖*primeProductNorm p (A∪D)) := by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left
        · simpa only [Fintype.sum_prod_type] using crossCoeff_sum_norm_le
        · positivity
      · exact Finset.sum_nonneg (fun D hD=>mul_nonneg (norm_nonneg _) (hn D))
    _=_ := by
      have he : ((2:ℝ)^slots.card)^2=(4:ℝ)^slots.card := by rw [←pow_mul,pow_mul'];norm_num
      rw [he]
      dsimp only [P,A]
      ring

theorem whole_priority_tail_bound (Lcap tau saving : ℝ) (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct : ℝ),0<Ct ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
      (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
      (selector : Finset ι→ℂ) (om W : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo)
      (hs : Function.support om⊆Set.Icc lo hi) (M t X Y Z : ℝ)
      (R : Finset ι→Finset ι→Finset ι→ℝ) (B T S : ℝ),
      b.Admissible → extra⊆b.support → 0≤B → 0<T → 0≤S →
      ‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B →
      ‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B →
      (∀D∈pool.powerset,‖selector D‖≤S) →
      (∀D∈pool.powerset,selector D≠0 → primeProductNorm p D≤T) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀u,‖Ψ u‖≤1) → d≠0 → hi≤Real.exp M → 0<X → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
      (∀D∈pool.powerset,selector D≠0 → ∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p d G E.val (X*Real.exp M) Y (Z^tau)≤R D G E.val) →
      wholePriorityTailEnergy p hp hg hinj pool b C extra negative Ψ m d slots lists a
        selector om W lo hi hlo hs X t Y R ≤
      Ct*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(SchwartzMap.seminorm ℝ 0 0 om)^2)*
        S*(B^2*primeProductNorm p C)*T^2*Z^(-saving) := by
  obtain ⟨s,Ct,hCt,htail⟩ := whole_priority_tail_weighted Lcap tau saving hLcap htau
  refine ⟨s,128*Ct,by positivity,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc pool b C extra negative Ψ m d slots lists a selector
    om W lo hi hlo hs M t X Y Z R B T S hb he hB hT hS hb₁ hb₂ hsel hsupp
    hslots ha hΨ hd hhi hX hZ hY hL hy hyi hl hR
  have hn := first_whole_extracted_norm p hp b hb C extra he negative B hB hb₁ hb₂
  have hmass := first_selector_weighted_mass p hp hinj pool
    (extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)) selector
    (B^2*primeProductNorm p C) T S 1 (mul_nonneg (sq_nonneg _) (primeProductNorm_pos p hp C).le)
    hT hS (by norm_num) hn hsel hsupp
  simp only [Real.rpow_one] at hmass
  have ht := htail p hp hg hinj hcop hc pool b C extra negative Ψ m d slots lists a selector
    om W lo hi hlo hs M t X Y Z R hslots ha hΨ hd hhi hX hZ hY hL hy hyi hl hR
  apply ht.trans
  have hh := mul_le_mul_of_nonneg_left hmass
    (show 0≤Ct*(4:ℝ)^slots.card*
      (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(SchwartzMap.seminorm ℝ 0 0 om)^2)*Z^(-saving) by positivity)
  convert hh using 1
  ring

theorem whole_priority_tail_rapid (Lcap tau saving : ℝ) (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct : ℝ),0<Ct ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
      (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
      (selector : Finset ι→ℂ) (om W : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo)
      (hs : Function.support om⊆Set.Icc lo hi) (M t X Y Z : ℝ)
      (R : Finset ι→Finset ι→Finset ι→ℝ) (B T S : ℝ),
      b.Admissible → extra⊆b.support → 0≤B → 0<T → 0≤S →
      ‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B →
      ‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B →
      (∀D∈pool.powerset,‖selector D‖≤S) →
      (∀D∈pool.powerset,selector D≠0 → primeProductNorm p D≤T) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀u,‖Ψ u‖≤1) → d≠0 → hi≤Real.exp M → 0<X → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
      (∀D∈pool.powerset,selector D≠0 → ∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p d G E.val (X*Real.exp M) Y (Z^tau)≤R D G E.val) →
      B^2*primeProductNorm p C≤Z^Lcap → T≤Z^Lcap →
      wholePriorityTailEnergy p hp hg hinj pool b C extra negative Ψ m d slots lists a
        selector om W lo hi hlo hs X t Y R ≤
      Ct*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(SchwartzMap.seminorm ℝ 0 0 om)^2)*
        S*Z^(-saving) := by
  obtain ⟨s,Ct,hCt,htail⟩ := whole_priority_tail_bound Lcap tau (saving+3*Lcap) hLcap htau
  refine ⟨s,Ct,hCt,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc pool b C extra negative Ψ m d slots lists a selector
    om W lo hi hlo hs M t X Y Z R B T S hb he hB hT hS hb₁ hb₂ hsel hsupp
    hslots ha hΨ hd hhi hX hZ hY hL hy hyi hl hR hEcap hTcap
  have ht := htail p hp hg hinj hcop hc pool b C extra negative Ψ m d slots lists a selector
    om W lo hi hlo hs M t X Y Z R B T S hb he hB hT hS hb₁ hb₂ hsel hsupp
    hslots ha hΨ hd hhi hX hZ hY hL hy hyi hl hR
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have habsorb : (B^2*primeProductNorm p C)*T^2*Z^(-(saving+3*Lcap))≤Z^(-saving) := by
    calc
      _≤Z^Lcap*(Z^Lcap)^2*Z^(-(saving+3*Lcap)) := by gcongr
      _=Z^(-saving) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hz.le,←Real.rpow_add hz,←Real.rpow_add hz]
        congr 1
        ring
  apply ht.trans
  have hh := mul_le_mul_of_nonneg_left habsorb
    (show 0≤Ct*(4:ℝ)^slots.card*
      (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(SchwartzMap.seminorm ℝ 0 0 om)^2)*S by positivity)
  convert hh using 1
  ring

def wholeFreshError (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (b : CubeCoordinates ι) (C extra D : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (R : Finset ι→Finset ι→ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex) : ℂ :=
  let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  let H:=markedRadial p (slots\J) (fun i=>lists i\(A∪D)) a ∅
    (principalWindow om lo hi hlo hs negative t) X
  let Ψ₀:=firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
  let m₀:=(m*b0Label p b.support (fun i=>b.leftExponent i+b.rightExponent i)
    b.leftBit b.rightBit)*∏i∈D,p i
  let c₀:=(∏i∈C,p i)*jLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
  firstFreshSecondPoisson p hp hg hinj pool D b.support (fun i=>b.leftExponent i+b.rightExponent i)
    b.leftBit b.rightBit negative (if negative then r.1 else r.2) Ψ m
    (primeMark (slots\J) (fun i=>lists i\(A∪D)) a) om X (∏i∈C,p i) d core t Y -
  truncatedSecondSource p hp hg hinj pool Ψ₀ m₀ c₀ d H rowMajorant Y
    (fun G E=>childFrequencyBall (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E) (R G E))

lemma wholeFreshError_eq_tail (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool : Finset ι) (b : CubeCoordinates ι) (C extra D : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (R : Finset ι→Finset ι→ℝ)
    (r : RayCharacter×RayCharacter) (core : FirstCoreIndex) :
    wholeFreshError p hp hg hinj pool b C extra D negative Ψ m d slots J lists a
      om lo hi hlo hs X t Y R r core =
    let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
    secondSourceTail p hp hg hinj pool (firstCoreTwist negative (if negative then r.1 else r.2) Ψ core)
      ((m*b0Label p b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit)*∏i∈D,p i)
      ((∏i∈C,p i)*jLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit) d
      (markedRadial p (slots\J) (fun i=>lists i\(A∪D)) a ∅
        (principalWindow om lo hi hlo hs negative t) X) rowMajorant Y
      (fun G E=>childFrequencyBall (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E) (R G E)) := by
  let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  have he := first_fresh_radial_truncated p hp hg hinj hc pool D b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
    (if negative then r.1 else r.2) Ψ m (slots\J) (fun i=>lists i\(A∪D)) a
    (fun i _=>residual_lists_avoid lists A D i) om lo hi hlo hs X t Y hX hY
    (∏i∈C,p i) d core
    (fun G E=>childFrequencyBall (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E) (R G E))
  dsimp only at he
  unfold wholeFreshError
  dsimp only
  rw [he,add_sub_cancel_left]

theorem wholePriorityTailEnergy_eq_original_errors
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo)
    (hs : Function.support om⊆Set.Icc lo hi) (X t Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (R : Finset ι→Finset ι→Finset ι→ℝ) :
    wholePriorityTailEnergy p hp hg hinj pool b C extra negative Ψ m d slots lists a selector
      om rowMajorant lo hi hlo hs X t Y R =
    let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
    (32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
      (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑core:FirstCoreIndex,
        ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative Ψ m D core‖*
        ∑J∈slots.powerset,‖primeMark J lists a (A∪D)‖^2*
          ‖wholeFreshError p hp hg hinj pool b C extra D negative Ψ m d slots J lists a
            om lo hi hlo hs X t Y (R D) r core‖ := by
  simp_rw [wholeFreshError_eq_tail p hp hg hinj hc pool b C extra _ negative Ψ m d slots _
    lists a om lo hi hlo hs X t Y hX hY]
  rfl

end SevenEighths.InverseWholePriorityRapidTail

end

end OAI
end OAIOriginalModule0768

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.WholePriorityValidSource
Source SHA256: e8350ab7ac886eb026f2e7894e04d9a2bf6008fbd4d985d4080e74a13295fc8e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0769


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseWholePriorityValidSource
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents InversePrioritySecondSource
open InverseMomentWholePriorityParents InverseMomentWholePriorityPhysical
open RayFourExpansion InversePrincipalEnergy InverseSecondPrincipalCaller
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable {Jo : ℕ}

def activeFixedSource (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector : Finset ι→ℂ) :
    Finset (Source ι Jo) :=
  (fixedSource pool b C E old).filter (fun x=>selector x.quotientSupport≠0)

omit [DecidableEq ι] in
theorem activeFixedSource_eq_image (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector : Finset ι→ℂ) :
    activeFixedSource pool b C E old selector=
      (pool.powerset.filter (fun D=>selector D≠0)).image (fixedPoint b C E old) := by
  rw [activeFixedSource,fixedSource,Finset.filter_image]
  rfl

omit [DecidableEq ι] in
theorem mem_activeFixedSource (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector : Finset ι→ℂ) (x : Source ι Jo) :
    x∈activeFixedSource pool b C E old selector ↔
      ∃ D∈pool.powerset,selector D≠0 ∧ fixedPoint b C E old D=x := by
  rw [activeFixedSource_eq_image]
  simp only [Finset.mem_image,Finset.mem_filter]
  aesop

omit [DecidableEq ι] in
theorem sum_activeFixedSource {A : Type*} [AddCommMonoid A]
    (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector : Finset ι→ℂ) (H : Source ι Jo→A) :
    ∑ x∈activeFixedSource pool b C E old selector,H x=
      ∑ D∈pool.powerset.filter (fun D=>selector D≠0),H (fixedPoint b C E old D) := by
  rw [activeFixedSource_eq_image,Finset.sum_image (fun _ _ _ _ h=>fixedPoint_injective b C E old h)]

variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

omit [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem activeFixedSource_valid (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector : Finset ι→ℂ)
    (hb : b.Admissible) (hC : Disjoint C b.support) (hE : E⊆C∪b.support)
    (hold : ∀ D∈pool.powerset,selector D≠0 → ∀ i,(old i).val∣
      sourceIdeal p b.support*sourceIdeal p C*sourceIdeal p D) :
    ∀ x∈activeFixedSource pool b C E old selector,SourceValid p x := by
  intro x hx
  obtain ⟨D,hD,hs,rfl⟩ := (mem_activeFixedSource pool b C E old selector x).mp hx
  exact ⟨hb,hC,hE,hold D hD hs⟩

omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem activeFixedSource_extra (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector : Finset ι→ℂ)
    (extra : CubeCoordinates ι→Finset ι) (he : extra b⊆b.support) :
    ∀ x∈activeFixedSource pool b C E old selector,extra x.cube⊆x.cube.support := by
  intro x hx
  obtain ⟨D,hD,hs,rfl⟩ := (mem_activeFixedSource pool b C E old selector x).mp hx
  exact he

theorem active_retained_conditions (hp : ∀ i,p i≠0)
    (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector : Finset ι→ℂ)
    (hb : b.Admissible) (hC : Disjoint C b.support) (hE : E⊆C∪b.support)
    (hold : ∀ D∈pool.powerset,selector D≠0 → ∀ i,(old i).val∣
      sourceIdeal p b.support*sourceIdeal p C*sourceIdeal p D)
    (extra : CubeCoordinates ι→Finset ι) (he : extra b⊆b.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) :
    ActualSecondSourceConditions p
      (retainedPool p pool (wholeAssignedParents p (fun x=>extra x.cube)
        (activeFixedSource pool b C E old selector) negative J lists) R label residual j) :=
  InverseMomentWholeRetainedSource.retained_conditions p hp extra _
    (activeFixedSource_valid p pool b C E old selector hb hC hE hold)
    (activeFixedSource_extra pool b C E old selector extra he) negative J lists pool R label residual j

theorem active_retained_deleted_support
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector : Finset ι→ℂ)
    (hb : b.Admissible) (hC : Disjoint C b.support) (hE : E⊆C∪b.support)
    (hold : ∀ D∈pool.powerset,selector D≠0 → ∀ i,(old i).val∣
      sourceIdeal p b.support*sourceIdeal p C*sourceIdeal p D)
    (extra : CubeCoordinates ι→Finset ι) (he : extra b⊆b.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈retainedPool p pool (wholeAssignedParents p (fun x=>extra x.cube)
      (activeFixedSource pool b C E old selector) negative J lists) R label residual j) :
    ∀ i∈InverseMomentWholeRetainedSource.deleted p extra negative x,
      i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient :=
  InverseMomentWholeRetainedSource.retained_deleted_support p hinj extra _
    (activeFixedSource_valid p pool b C E old selector hb hC hE hold)
    (activeFixedSource_extra pool b C E old selector extra he) negative J lists pool R label residual j x hx

variable (hp : ∀ i,p i≠0) (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem priorityOuter_zero (b : CubeCoordinates ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (selector : Finset ι→ℂ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (D : Finset ι) (hD : selector D=0) : priorityOuter p hg b negative Ψ m selector r core D=0 := by
  simp only [priorityOuter,hD,norm_zero,mul_zero,zero_mul]

def wholePriorityPoisson (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (b : CubeCoordinates ι) (C E extra : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : ℝ→ℂ) (X t Y : ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex) (D : Finset ι) : ℂ :=
  firstFreshSecondPoisson p hp hg hinj pool D b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
    (if negative then r.1 else r.2) Ψ m
    (fun U=>primeMark (slots\J)
      (fun i=>lists i\((extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)) a U)
    om X (∏ i∈C,p i) (primeSubsetGenerator (fun i=>Ideal.span {p i}) E) core t Y

theorem parentPoisson_fixed_whole (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (b : CubeCoordinates ι) (C E extra D : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : ℝ→ℂ) (X t Y : ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex) :
    parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra) a om X t Y r core
      (parent p (fixedPoint b C E old D)) =
    wholePriorityPoisson p hp hg hinj pool b C E extra negative Ψ m slots J lists a om X t Y r core D := by
  have hl : residualLists p negative (fun i=>lists i\extra)
      (parent p (fixedPoint b C E old D)) =
      (fun i=>lists i\((extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)) := by
    funext i
    unfold residualLists
    rw [quotientSupport_parent p hinj]
    change (lists i\extra)\(((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)=_
    ext k
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  unfold parentPoisson wholePriorityPoisson
  rw [quotientSupport_parent p hinj,hl]
  rfl

variable (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))

theorem whole_priority_complex_slice [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (extra : CubeCoordinates ι→Finset ι) (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots J : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (selector : Finset ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ) :
    (∑ D∈pool.powerset,(priorityOuter p hg b negative Ψ m selector r core D:ℂ)*
      (‖primeMark J lists a ((extra b∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)‖^2:ℝ)*
      wholePriorityPoisson p hp hg hinj pool b C E (extra b) negative Ψ m slots J lists a om X t Y r core D) =
    ∑ y∈wholeAssignedParents p (fun x=>extra x.cube) (activeFixedSource pool b C E old selector) negative J lists,
      coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)) y *
        fullPhysical p hp hcop hg hinj extra pool negative Ψ m slots J lists a
          (principalWindow om lo hi hlo hs negative t) X Y r core R label y := by
  let H (D : Finset ι) : ℂ := (priorityOuter p hg b negative Ψ m selector r core D:ℂ)*
    (‖primeMark J lists a ((extra b∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)‖^2:ℝ)*
    wholePriorityPoisson p hp hg hinj pool b C E (extra b) negative Ψ m slots J lists a om X t Y r core D
  have hfilter : ∑ D∈pool.powerset,H D=∑ D∈pool.powerset.filter (fun D=>selector D≠0),H D := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro D hD
    by_cases hn : selector D≠0
    · rw [ite_eq_left hn]
    · have hz : selector D=0 := not_ne_iff.mp hn
      simp only [ite_eq_right hn,H,priorityOuter_zero p hg b negative Ψ m selector r core D hz,
        Complex.ofReal_zero,zero_mul]
  calc
    _ = ∑ D∈pool.powerset.filter (fun D=>selector D≠0),H D := hfilter
    _ = ∑ x∈activeFixedSource pool b C E old selector,
        (priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)*
        (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
        parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube) a om X t Y r core (parent p x) := by
      rw [sum_activeFixedSource]
      apply Finset.sum_congr rfl
      intro D hD
      rw [parentPoisson_fixed_whole p hp hg hinj]
      simp only [H,fixedPoint,wholeExtractedSupport,extractedSupport,Finset.union_assoc]
    _ = _ := whole_signed_source_full p hp hcop hg hinj hc hpr extra pool _ _ negative Ψ m slots J lists a
      om lo hi hlo hs X t Y hX hY r core R label

theorem whole_priority_real_slice [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (extra : CubeCoordinates ι→Finset ι) (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots J : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (selector : Finset ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ) :
    (∑ D∈pool.powerset,priorityOuter p hg b negative Ψ m selector r core D*
      ‖primeMark J lists a ((extra b∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)‖^2*
      (wholePriorityPoisson p hp hg hinj pool b C E (extra b) negative Ψ m slots J lists a om X t Y r core D).re) =
    (∑ y∈wholeAssignedParents p (fun x=>extra x.cube) (activeFixedSource pool b C E old selector) negative J lists,
      coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)) y *
        fullPhysical p hp hcop hg hinj extra pool negative Ψ m slots J lists a
          (principalWindow om lo hi hlo hs negative t) X Y r core R label y).re := by
  have h := congrArg Complex.re (whole_priority_complex_slice p hp hg hcop hinj hc hpr pool b C E
    extra old negative Ψ m slots J lists a selector om lo hi hlo hs X t Y hX hY r core R label)
  simpa only [Complex.re_sum,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero] using h

theorem whole_priority_energy_reassembly [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (extra : CubeCoordinates ι→Finset ι) (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (selector : Finset ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ) :
    firstWholePrioritySecondEnergy p hp hg hinj pool b C (extra b) negative Ψ m
      (primeSubsetGenerator (fun i=>Ideal.span {p i}) E) slots lists a selector om X t Y =
    (32*512)*(2:ℝ)^slots.card * ∑ r : RayCharacter×RayCharacter,
      ∑ core : FirstCoreIndex,∑ J∈slots.powerset,
        (∑ y∈wholeAssignedParents p (fun x=>extra x.cube) (activeFixedSource pool b C E old selector) negative J lists,
          coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)) y *
            fullPhysical p hp hcop hg hinj extra pool negative Ψ m slots J lists a
              (principalWindow om lo hi hlo hs negative t) X Y r core R label y).re := by
  simp_rw [←whole_priority_real_slice p hp hg hcop hinj hc hpr pool b C E extra old negative Ψ m slots
    _ lists a selector om lo hi hlo hs X t Y hX hY _ _ R label]
  unfold firstWholePrioritySecondEnergy
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro core hcore
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro D hD
  unfold priorityOuter wholePriorityPoisson
  ring

end SevenEighths.InverseWholePriorityValidSource

end

end OAI
end OAIOriginalModule0769

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.WholePriorityRetainedSource
Source SHA256: 1cb49f206a6689ef6ca49237d274381a6c687a944ea6638e11ec21e037c17e5b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0770


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseWholePriorityRetainedSource
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents InversePrioritySecondSource
open InverseMomentWholePriorityParents InverseMomentWholePriorityPhysical
open InverseWholePriorityValidSource RayFourExpansion InversePrincipalEnergy InverseSecondPrincipalCaller
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable {Jo : ℕ} (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

def unifiedSource (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ) :
    Finset (MarkedSecondSource ι Jo 0) :=
  attachedSecondFamily parents (fun y=>secondExpansionPool pool
    (fun G E=>(secondVariableCutoff p y (R y) G E).erase 0))

omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem mem_unifiedSource (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ) (x : MarkedSecondSource ι Jo 0) :
    x∈unifiedSource p pool parents R ↔ secondParentOf x∈parents ∧
      x.second.sourceCommon⊆pool ∧ x.second.divisor⊆x.second.sourceCommon ∧
      x.second.overlap⊆pool ∧ x.second.frequency∈nonzeroChildFrequencyBall
        (actualSecondMultiplier p x) (R (secondParentOf x) x.second.sourceCommon x.second.divisor) := by
  rw [unifiedSource,mem_attachedSecondFamily,mem_secondExpansionPool]
  rfl

omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem unified_frequency_ne_zero (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ) (x : MarkedSecondSource ι Jo 0)
    (hx : x∈unifiedSource p pool parents R) : x.second.frequency≠0 :=
  (Finset.mem_erase.mp ((mem_unifiedSource p pool parents R x).mp hx).2.2.2.2).1

omit [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem unified_mem_sector
    (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (x : MarkedSecondSource ι Jo 0) (hx : x∈unifiedSource p pool parents R) :
    x∈retainedPool p pool parents R label (x.second.sourceCommon\x.second.divisor)
      (label (secondParentOf x) (x.second.sourceCommon\x.second.divisor) x.second) := by
  obtain ⟨hy,hz⟩ := (mem_attachedSecondFamily _ _ x).mp hx
  apply (mem_retainedPool p _ _ _ _ _ _ x).mpr
  exact ⟨hy,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hz,rfl⟩,rfl⟩⟩

omit [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem sectors_sum [Fintype κ]
    (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (H : MarkedSecondSource ι Jo 0→ℂ) :
    (∑ residual∈pool.powerset,∑ j : κ,∑ x∈retainedPool p pool parents R label residual j,H x)=
      ∑ x∈unifiedSource p pool parents R,H x := by
  simp only [retainedPool,unifiedSource,sum_attachedSecondFamily]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_comm]
  simp_rw [sum_secondDyadicSector]
  exact sum_secondExpansionSector pool _ _

omit [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem parent_retained_sum [Fintype κ]
    (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (w : SecondParentSource ι Jo→ℂ) (H : MarkedSecondSource ι Jo 0→ℂ) :
    (∑ y∈parents,w y*(∑ residual∈pool.powerset,∑ j : κ,
      ∑ x∈(secondDyadicSector pool (secondVariableCutoff p y (R y)) residual (label y) j).image
        (attachSecondExpansion y),H x)) =
      ∑ x∈unifiedSource p pool parents R,w (secondParentOf x)*H x := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext residual; rw [Finset.sum_comm]
  simp_rw [←Finset.mul_sum,retained_sum]
  exact sectors_sum p pool parents R label _

theorem unified_conditions (hp : ∀ i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (source : Finset (Source ι Jo))
    (hs : ∀ x∈source,SourceValid p x) (he : ∀ x∈source,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ) :
    ActualSecondSourceConditions p (unifiedSource p pool
      (wholeAssignedParents p (fun x=>extra x.cube) source negative J lists) R) := by
  apply whole_assigned_family_conditions p hp (fun x=>extra x.cube) source hs he negative J lists
  intro y hy x hx
  exact ((mem_secondExpansionPool _ _ x).mp hx).2.1

theorem unified_deleted_support
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (source : Finset (Source ι Jo))
    (hs : ∀ x∈source,SourceValid p x) (he : ∀ x∈source,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈unifiedSource p pool (wholeAssignedParents p (fun x=>extra x.cube)
      source negative J lists) R) :
    ∀ i∈InverseMomentWholeRetainedSource.deleted p extra negative x,
      i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient := by
  exact InverseMomentWholeRetainedSource.retained_deleted_support p hinj extra source hs he
    negative J lists pool R (fun _ _ _=>()) _ () x
    (unified_mem_sector p pool _ R (fun _ _ _=>()) x hx)

omit [DecidableEq σ] [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem deleted_lists (extra : CubeCoordinates ι→Finset ι) (negative : Bool)
    (lists : σ→Finset ι) (x : MarkedSecondSource ι Jo 0) :
    residualLists p negative (fun i=>lists i\extra x.cube) (secondParentOf x)=
      fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x := by
  funext i
  ext k
  simp only [residualLists,InverseMomentWholeRetainedSource.deleted,Finset.mem_sdiff,Finset.mem_union]
  tauto

def wholeRow (hp : ∀ i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : ℝ→ℂ) (X Y : ℝ) (ray : SecondRayIndex) (x : MarkedSecondSource ι Jo 0) : ℂ :=
  retainedRow p hp hcop hg pool negative Ψ m slots J (fun i=>lists i\extra x.cube) a V X Y ray x

theorem wholeRow_eq (hp : ∀ i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : ℝ→ℂ) (X Y : ℝ) (ray : SecondRayIndex) (x : MarkedSecondSource ι Jo 0) :
    wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a V X Y ray x =
      actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x *
      actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
        (slots\J) (slots\J)
        (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x)
        (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x)
        a a V V rowMajorant Y X := by
  unfold wholeRow retainedRow
  rw [deleted_lists]

theorem whole_retained_sum [Fintype κ] (hp : ∀ i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (parents : Finset (SecondParentSource ι Jo)) (w : SecondParentSource ι Jo→ℂ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots J : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (V : ℝ→ℂ) (X Y : ℝ)
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ) :
    (∑ y∈parents,w y*(∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector pool (secondVariableCutoff p y (R y)) residual (label y) j).image
          (attachSecondExpansion y),
          retainedRow p hp hcop hg pool negative Ψ m slots J (fun i=>lists i\extra y.cube)
            a V X Y ray x)) =
    ∑ ray : SecondRayIndex,(Y:ℂ)*secondRayCoefficient ray *
      ∑ x∈unifiedSource p pool parents R,w (secondParentOf x)*
        wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a V X Y ray x := by
  have hrow (y : SecondParentSource ι Jo) (ray : SecondRayIndex) (residual : Finset ι) (j : κ) :
      (∑ x∈(secondDyadicSector pool (secondVariableCutoff p y (R y)) residual (label y) j).image
          (attachSecondExpansion y),
          retainedRow p hp hcop hg pool negative Ψ m slots J (fun i=>lists i\extra y.cube)
            a V X Y ray x) =
      ∑ x∈(secondDyadicSector pool (secondVariableCutoff p y (R y)) residual (label y) j).image
          (attachSecondExpansion y),
          wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a V X Y ray x := by
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    rfl
  simp_rw [hrow,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ray hray
  simp_rw [←Finset.mul_sum]
  simp_rw [mul_left_comm _ ((Y:ℂ)*secondRayCoefficient ray),←Finset.mul_sum]
  congr 1
  exact parent_retained_sum p pool parents R label w _

def activeParents (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (b : CubeCoordinates ι) (C E : Finset ι) (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector : Finset ι→ℂ) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) :=
  wholeAssignedParents p (fun x=>extra x.cube)
    (activeFixedSource pool b C E old selector) negative J lists

theorem active_conditions (hp : ∀ i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (b : CubeCoordinates ι) (C E : Finset ι) (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector : Finset ι→ℂ) (hb : b.Admissible) (hC : Disjoint C b.support) (hE : E⊆C∪b.support)
    (hold : ∀ D∈pool.powerset,selector D≠0 → ∀ i,(old i).val∣
      sourceIdeal p b.support*sourceIdeal p C*sourceIdeal p D)
    (he : extra b⊆b.support) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ) :
    ActualSecondSourceConditions p (unifiedSource p pool
      (activeParents p extra pool b C E old selector negative J lists) R) :=
  unified_conditions p hp extra _ (activeFixedSource_valid p pool b C E old selector hb hC hE hold)
    (activeFixedSource_extra pool b C E old selector extra he) negative J lists pool R

theorem active_deleted_support
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (b : CubeCoordinates ι) (C E : Finset ι) (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector : Finset ι→ℂ) (hb : b.Admissible) (hC : Disjoint C b.support) (hE : E⊆C∪b.support)
    (hold : ∀ D∈pool.powerset,selector D≠0 → ∀ i,(old i).val∣
      sourceIdeal p b.support*sourceIdeal p C*sourceIdeal p D)
    (he : extra b⊆b.support) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈unifiedSource p pool (activeParents p extra pool b C E old selector negative J lists) R) :
    ∀ i∈InverseMomentWholeRetainedSource.deleted p extra negative x,
      i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient :=
  unified_deleted_support p hinj extra _
    (activeFixedSource_valid p pool b C E old selector hb hC hE hold)
    (activeFixedSource_extra pool b C E old selector extra he) negative J lists pool R x hx

def coefficientBound : ℝ := 512*(32*512)

theorem coefficientBound_pos : 0<coefficientBound := by norm_num [coefficientBound]

variable (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem priorityOuter_norm (b : CubeCoordinates ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (selector : Finset ι→ℂ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex) (D : Finset ι)
    (hselector : ‖selector D‖≤1) (hΨ : ‖Ψ (∏ i∈D,p i)‖≤1) :
    ‖(priorityOuter p hg b negative Ψ m selector r core D:ℂ)‖≤coefficientBound := by
  have hr : ‖crossCoeff r.1 r.2‖≤512 :=
    (Finset.single_le_sum (fun j _=>norm_nonneg (crossCoeff r.1 j)) (Finset.mem_univ r.2)).trans
      ((Finset.single_le_sum (fun j _=>Finset.sum_nonneg (fun k _=>norm_nonneg (crossCoeff j k)))
        (Finset.mem_univ r.1)).trans crossCoeff_sum_norm_le)
  have hc : ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
      b.leftBit b.rightBit negative Ψ m D core‖≤32*512 :=
    (Finset.single_le_sum (fun c _=>norm_nonneg (firstCoreOuter p hg b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D c))
      (Finset.mem_univ core)).trans
      (firstCoreOuter_mass p hg b.support _ b.leftBit b.rightBit negative Ψ m D hΨ)
  rw [Complex.norm_real,Real.norm_of_nonneg (by unfold priorityOuter; positivity)]
  unfold priorityOuter coefficientBound
  exact mul_le_mul ((mul_le_of_le_one_right (norm_nonneg _) hselector).trans hr) hc
    (norm_nonneg _) (by norm_num)

def sourceWeight (b : CubeCoordinates ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (selector : Finset ι→ℂ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (J : Finset σ) (a : σ→ι→ℂ) (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0) : ℂ :=
  coefficient p J a (fun original=>(priorityOuter p hg b negative Ψ m selector r core
    original.quotientSupport:ℂ)) (secondParentOf x)

theorem sourceWeight_norm
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (b : CubeCoordinates ι) (C E : Finset ι) (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector : Finset ι→ℂ) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ha : ∀ i∈J,∀ k∈lists i,‖a i k‖≤1)
    (hselector : ∀ D∈pool.powerset,‖selector D‖≤1)
    (hΨ : ∀ D∈pool.powerset,selector D≠0 → ‖Ψ (∏ i∈D,p i)‖≤1)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈unifiedSource p pool (activeParents p extra pool b C E old selector negative J lists) R) :
    ‖sourceWeight p hg b negative Ψ m selector r core J a x‖≤coefficientBound := by
  apply InverseMomentWholeRetainedSource.whole_coefficient_norm p hinj (fun x=>extra x.cube)
    (activeFixedSource pool b C E old selector) negative J lists a _ coefficientBound ha
  · intro y hy
    obtain ⟨D,hD,hs,rfl⟩ := (mem_activeFixedSource pool b C E old selector y).mp hy
    exact priorityOuter_norm p hg b negative Ψ m selector r core D (hselector D hD) (hΨ D hD hs)
  · exact ((mem_unifiedSource p pool _ R x).mp hx).1

def normalizedWeight (b : CubeCoordinates ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (selector : Finset ι→ℂ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (J : Finset σ) (a : σ→ι→ℂ) (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0) : ℂ :=
  sourceWeight p hg b negative Ψ m selector r core J a x/(coefficientBound:ℂ)

theorem normalizedWeight_norm
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (b : CubeCoordinates ι) (C E : Finset ι) (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector : Finset ι→ℂ) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ha : ∀ i∈J,∀ k∈lists i,‖a i k‖≤1)
    (hselector : ∀ D∈pool.powerset,‖selector D‖≤1)
    (hΨ : ∀ D∈pool.powerset,selector D≠0 → ‖Ψ (∏ i∈D,p i)‖≤1)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈unifiedSource p pool (activeParents p extra pool b C E old selector negative J lists) R) :
    ‖normalizedWeight p hg b negative Ψ m selector r core J a x‖≤1 := by
  rw [normalizedWeight,norm_div,Complex.norm_real,Real.norm_of_nonneg coefficientBound_pos.le]
  exact (div_le_one coefficientBound_pos).mpr
    (sourceWeight_norm p hg hinj extra pool b C E old selector negative Ψ m r core J lists a
      ha hselector hΨ R x hx)

omit [DecidableEq σ] in

theorem source_sum_normalized
    (b : CubeCoordinates ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (selector : Finset ι→ℂ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (J : Finset σ) (a : σ→ι→ℂ) (source : Finset (MarkedSecondSource ι (Jo+(J.card+J.card)) 0))
    (H : MarkedSecondSource ι (Jo+(J.card+J.card)) 0→ℂ) :
    (∑ x∈source,sourceWeight p hg b negative Ψ m selector r core J a x*H x)=
      (coefficientBound:ℂ)*∑ x∈source,normalizedWeight p hg b negative Ψ m selector r core J a x*H x := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  unfold normalizedWeight
  have hc : (coefficientBound:ℂ)≠0 := by exact_mod_cast coefficientBound_pos.ne'
  field_simp

theorem fullPhysical_unified [Fintype κ] (hp : ∀ i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (parents : Finset (SecondParentSource ι Jo)) (w : SecondParentSource ι Jo→ℂ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots J : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (V : 𝓢(ℝ,ℂ)) (X Y : ℝ)
    (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ) :
    let Ψ₀ := firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
    let H := fun y : SecondParentSource ι Jo=>markedRadial p (slots\J)
      (residualLists p negative (fun i=>lists i\extra y.cube) y) a ∅ V X
    let K := fun y : SecondParentSource ι Jo=>secondVariableCutoff p y R
    (∑ y∈parents,w y*fullPhysical p hp hcop hg hinj extra pool negative Ψ m slots J lists a
      V X Y r core R label y) =
      (∑ y∈parents,w y*truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
        (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)) +
      (∑ ray : SecondRayIndex,(Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈unifiedSource p pool parents (fun _=>R),w (secondParentOf x)*
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots J lists a V X Y ray x) +
      (∑ y∈parents,w y*secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
        (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)) := by
  intro Ψ₀ H K
  simp only [fullPhysical,mul_add,Finset.sum_add_distrib]
  rw [whole_retained_sum p hp hcop hg extra pool parents w negative Ψ₀ m slots J lists a
    V X Y (fun _=>R) (fun _=>label)]

theorem actual_retained_normalized [Fintype κ] (hp : ∀ i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (b : CubeCoordinates ι) (C E : Finset ι) (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector : Finset ι→ℂ) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : ℝ→ℂ) (X Y : ℝ)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ) :
    let parents := activeParents p extra pool b C E old selector negative J lists
    let Ψ₀ := firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
    (∑ y∈parents,
      coefficient p J a (fun original=>(priorityOuter p hg b negative Ψ m selector r core
        original.quotientSupport:ℂ)) y *
      (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
        (Y:ℂ)*secondRayCoefficient ray *
          ∑ x∈(secondDyadicSector pool (secondVariableCutoff p y (R y)) residual (label y) j).image
            (attachSecondExpansion y),
            retainedRow p hp hcop hg pool negative Ψ₀ m slots J (fun i=>lists i\extra y.cube)
              a V X Y ray x)) =
    (coefficientBound:ℂ)*(∑ ray : SecondRayIndex,(Y:ℂ)*secondRayCoefficient ray *
      ∑ x∈unifiedSource p pool parents R,normalizedWeight p hg b negative Ψ m selector r core J a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots J lists a V X Y ray x) := by
  intro parents Ψ₀
  rw [whole_retained_sum p hp hcop hg extra pool parents _ negative Ψ₀ m slots J lists a V X Y R label]
  change (∑ ray : SecondRayIndex,(Y:ℂ)*secondRayCoefficient ray *
      ∑ x∈unifiedSource p pool parents R,sourceWeight p hg b negative Ψ m selector r core J a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots J lists a V X Y ray x)=_
  simp_rw [source_sum_normalized]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ray hray
  ring

end SevenEighths.InverseWholePriorityRetainedSource

end

end OAI
end OAIOriginalModule0770

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPrioritySource
Source SHA256: 394b3a3d5d4d6a25e3f2bf7ccf65dbbf2167fad3d8b49fe3b1d12baf0f9aedbf
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0771


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open InverseFirstPriorityParents InverseMomentWholePriorityParents InverseWholePriorityRetainedSource
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→O)[∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def globalPriorityOuter (negative:Bool)(Ψ:O→*ℂ)(m:O)
    (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(w:Source ι Jo→ℂ)(x:Source ι Jo):ℂ:=
  w x*(priorityOuter p hg x.cube negative Ψ m (fun _=>1) ray core x.quotientSupport:ℂ)

def globalPriorityWeight (negative:Bool)(Ψ:O→*ℂ)(m:O)
    (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(w:Source ι Jo→ℂ)
    (J:Finset σ)(a:σ→ι→ℂ)(x:MarkedSecondSource ι (Jo+(J.card+J.card)) 0):ℂ:=
  coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) (secondParentOf x)

def normalizedGlobalPriorityWeight (negative:Bool)(Ψ:O→*ℂ)(m:O)
    (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(w:Source ι Jo→ℂ)
    (J:Finset σ)(a:σ→ι→ℂ)(x:MarkedSecondSource ι (Jo+(J.card+J.card)) 0):ℂ:=
  globalPriorityWeight p hg negative Ψ m ray core w J a x/(coefficientBound:ℂ)

theorem globalPriorityWeight_norm
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι)(original:Finset (Source ι Jo))(pool:Finset ι)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)
    (w:Source ι Jo→ℂ)(hw:∀x∈original,‖w x‖≤1)(hΨ:∀u,‖Ψ u‖≤1)
    (J:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(ha:∀i∈J,∀k∈lists i,‖a i k‖≤1)
    (R:SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (x:MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx:x∈unifiedSource p pool (wholeAssignedParents p (fun x=>extra x.cube) original negative J lists) R):
    ‖globalPriorityWeight p hg negative Ψ m ray core w J a x‖≤coefficientBound:=by
  apply InverseMomentWholeRetainedSource.whole_coefficient_norm p hinj (fun x=>extra x.cube)
    original negative J lists a _ coefficientBound ha
  · intro y hy
    rw [globalPriorityOuter,norm_mul]
    have hn:=priorityOuter_norm p hg y.cube negative Ψ m (fun _=>1) ray core y.quotientSupport
      (by simp) (hΨ _)
    exact (mul_le_mul (hw y hy) hn (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · exact ((mem_unifiedSource p pool _ R x).mp hx).1

theorem normalizedGlobalPriorityWeight_norm
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι)(original:Finset (Source ι Jo))(pool:Finset ι)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)
    (w:Source ι Jo→ℂ)(hw:∀x∈original,‖w x‖≤1)(hΨ:∀u,‖Ψ u‖≤1)
    (J:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(ha:∀i∈J,∀k∈lists i,‖a i k‖≤1)
    (R:SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (x:MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx:x∈unifiedSource p pool (wholeAssignedParents p (fun x=>extra x.cube) original negative J lists) R):
    ‖normalizedGlobalPriorityWeight p hg negative Ψ m ray core w J a x‖≤1:=by
  rw [normalizedGlobalPriorityWeight,norm_div,Complex.norm_real,Real.norm_of_nonneg coefficientBound_pos.le]
  exact (div_le_one coefficientBound_pos).mpr
    (globalPriorityWeight_norm p hg hinj extra original pool negative Ψ m ray core w hw hΨ J lists a ha R x hx)

omit [DecidableEq σ] in
theorem globalPriority_sum_normalized
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)
    (w:Source ι Jo→ℂ)(J:Finset σ)(a:σ→ι→ℂ)
    (source:Finset (MarkedSecondSource ι (Jo+(J.card+J.card)) 0))
    (H:MarkedSecondSource ι (Jo+(J.card+J.card)) 0→ℂ):
    (∑x∈source,globalPriorityWeight p hg negative Ψ m ray core w J a x*H x)=
      (coefficientBound:ℂ)*∑x∈source,normalizedGlobalPriorityWeight p hg negative Ψ m ray core w J a x*H x:=by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  unfold normalizedGlobalPriorityWeight
  have hn:(coefficientBound:ℂ)≠0:=by exact_mod_cast coefficientBound_pos.ne'
  field_simp
end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0771

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityEnergy
Source SHA256: 859e3848934076d3000247134e8f9cc5bdd03055f3e3d6ef64afc521205f15a7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0772




namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem global_priority_retained_moving_radius
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (J K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis) (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:SecondParentSource ι (Jo+(assigned.card+assigned.card))→Finset ι→Finset ι→ℝ)
,
    let source:=unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) cutoff
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    ∀(z:SecondRayIndex)
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R (index p x))) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo+(assigned.card+assigned.card) ≤ 2*K → (slots\assigned).card ≤ K → (slots\assigned).card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤Z → 1≤b → b≤Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖(Y:ℂ)*secondRayCoefficient z *
        ∑x∈source,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖ ≤
      C*A*‖secondRayCoefficient z‖*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,Cbin,hC,hCbin,he⟩:=
    actual_priority_retained_moving_radius (ι:=ι) (σ:=σ) om rowMajorant lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ J K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,coefficientBound*C,Cbin,mul_nonneg coefficientBound_pos.le hC,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
    Ψ m ray core slots assigned lists a cutoff source Ψ₀ z
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A
    haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hsource:ActualSecondSourceConditions p source:=
    unified_conditions p hp extra original hvalid hextra negative assigned lists pool cutoff
  have hd:∀x∈source,∀i∈InverseMomentWholeRetainedSource.deleted p extra negative x,
      i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient:=
    unified_deleted_support p hinj extra original hvalid hextra negative assigned lists pool cutoff
  have hw:∀x∈source,‖normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a x‖≤1:=
    fun x hx=>normalizedGlobalPriorityWeight_norm p hg hinj extra original pool negative Ψ m ray core w hwOriginal hΨ
      assigned lists a haassigned cutoff x hx
  have hΨ₀:∀n,‖Ψ₀ n‖≤1:=fun n=>(firstCoreTwist_norm_le negative (if negative then ray.1 else ray.2)
    Ψ core n).trans (hΨ n)
  have he₀:=he p hp hcop hg hpr hinj hc source hsource pool Ψ₀ m z (slots\assigned) (slots\assigned)
    lists lists a a (InverseMomentWholeRetainedSource.deleted p extra negative)
    (InverseMomentWholeRetainedSource.deleted p extra negative)
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t
    (normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a) labels A
    hd hd hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ₀ hw
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hrow:∀x:MarkedSecondSource ι (Jo+(assigned.card+assigned.card)) 0,wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
      (principalWindow om lo hi hlo hsupport negative t) X Y z x=
      actualSecondSignedWeight p hp hcop hg Ψ₀ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x*
      actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ₀ m z)
        (slots\assigned) (slots\assigned)
        (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x)
        (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x) a a
        (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t)
        rowMajorant Y X:=fun x=>wholeRow_eq p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a _ X Y z x
  rw [globalPriority_sum_normalized p hg negative Ψ m ray core w assigned a source]
  rw [show (Y:ℂ)*secondRayCoefficient z*((coefficientBound:ℂ)*
      ∑x∈source,normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a x*
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
          (principalWindow om lo hi hlo hsupport negative t) X Y z x)=
      (coefficientBound:ℂ)*((Y:ℂ)*secondRayCoefficient z*
        ∑x∈source,normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a x*
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x) by ring]
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg coefficientBound_pos.le]
  simp_rw [hrow,←mul_assoc]
  convert mul_le_mul_of_nonneg_left he₀ coefficientBound_pos.le using 1 <;> ring_nf

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0772

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityPhysical
Source SHA256: ab115afca7821d08fc058bc74a080397659dff4b576bcd28a9ab2b3d6b3b9096
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0773


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open InverseFirstPriorityParents InverseMomentWholePriorityParents InverseWholePriorityRetainedSource
open InverseMomentWholePriorityPhysical InversePrioritySecondSource InversePrincipalEnergy InverseSecondPrincipalCaller
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem global_priority_physical_source
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)
    (w:Source ι Jo→ℂ)(slots J:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ)(hX:0<X)(hY:0<Y)(R:Finset ι→Finset ι→ℝ):
    let parents:=wholeAssignedParents p (fun x=>extra x.cube) original negative J lists
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    let V:=principalWindow om lo hi hlo hs negative t
    let H:=fun y:SecondParentSource ι (Jo+(J.card+J.card))=>markedRadial p (slots\J)
      (residualLists p negative (fun i=>lists i\extra y.cube) y) a ∅ V X
    let K:=fun y:SecondParentSource ι (Jo+(J.card+J.card))=>secondVariableCutoff p y R
    let coeff:=coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w)
    (∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube)
        a om X t Y ray core (parent p x))=
    (∑y∈parents,coeff y*truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y))+
    (∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z*
      ∑x∈unifiedSource p pool parents (fun _=>R),globalPriorityWeight p hg negative Ψ m ray core w J a x*
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots J lists a V X Y z x)+
    (∑y∈parents,coeff y*secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)):=by
  intro parents Ψ₀ V H K coeff
  rw [whole_signed_source_full p hp hcop hg hinj hc hpr extra pool original
    (globalPriorityOuter p hg negative Ψ m ray core w) negative Ψ m slots J lists a
    om lo hi hlo hs X t Y hX hY ray core R (fun _ _=>())]
  exact fullPhysical_unified p hg hp hcop hinj extra pool parents coeff negative Ψ m slots J lists a
    V X Y ray core R (fun _ _=>())
end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0773

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalParentSource
Source SHA256: 891b92430a3269def4e399f6cf3300a9be7acb5d42c1a1df59e26761114bb8cd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0774


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open InverseFirstPriorityParents
variable {ι:Type*} [DecidableEq ι] {Jo:ℕ}
def eraseFirstQuotient (x:Source ι Jo):Source ι Jo:= {x with quotientSupport:=∅}
def fillFirstQuotient (x:Source ι Jo)(D:Finset ι):Source ι Jo:={x with quotientSupport:=D}
omit [DecidableEq ι] in
@[simp] theorem erase_fillFirstQuotient (x:Source ι Jo)(D:Finset ι):
    eraseFirstQuotient (fillFirstQuotient x D)=eraseFirstQuotient x:=rfl
omit [DecidableEq ι] in
@[simp] theorem eraseFirstQuotient_eq (x:Source ι Jo)(hx:x.quotientSupport=∅):
    eraseFirstQuotient x=x:=by cases x;simpa [eraseFirstQuotient] using hx.symm

def globalParentSource (outer:Finset (Source ι Jo))(pool:Finset ι)
    (selector:Source ι Jo→Finset ι→ℂ):Finset (Source ι Jo):=
  outer.biUnion (fun x=>(pool.powerset.filter (fun D=>selector x D≠0)).image (fillFirstQuotient x))

omit [DecidableEq ι] in
theorem sum_globalParentSource {A:Type*}[AddCommMonoid A]
    (outer:Finset (Source ι Jo))(pool:Finset ι)(selector:Source ι Jo→Finset ι→ℂ)
    (houter:∀x∈outer,x.quotientSupport=∅)(H:Source ι Jo→A):
    ∑x∈globalParentSource outer pool selector,H x=
      ∑x∈outer,∑D∈pool.powerset.filter (fun D=>selector x D≠0),H (fillFirstQuotient x D):=by
  unfold globalParentSource
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro x hx
    exact Finset.sum_image (fun D hD E hE he=>congrArg Source.quotientSupport he)
  · intro x hx y hy hxy
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨D,hD,rfl⟩:=Finset.mem_image.mp hz
    obtain ⟨E,hE,he⟩:=Finset.mem_image.mp hz'
    have he':=congrArg eraseFirstQuotient he
    simp only [erase_fillFirstQuotient,eraseFirstQuotient_eq _ (houter x hx),
      eraseFirstQuotient_eq _ (houter y hy)] at he'
    exact hxy he'.symm

omit [DecidableEq ι] in
theorem mem_globalParentSource
    (outer:Finset (Source ι Jo))(pool:Finset ι)(selector:Source ι Jo→Finset ι→ℂ)
    (houter:∀x∈outer,x.quotientSupport=∅)(x:Source ι Jo):
    x∈globalParentSource outer pool selector ↔
      eraseFirstQuotient x∈outer ∧ x.quotientSupport⊆pool ∧
        selector (eraseFirstQuotient x) x.quotientSupport≠0:=by
  constructor
  · intro hx
    obtain ⟨y,hy,hyx⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨D,hD,rfl⟩:=Finset.mem_image.mp hyx
    simp only [erase_fillFirstQuotient,eraseFirstQuotient_eq _ (houter y hy)]
    exact ⟨hy,Finset.mem_powerset.mp (Finset.mem_filter.mp hD).1,(Finset.mem_filter.mp hD).2⟩
  · rintro ⟨hx,hD,hs⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨eraseFirstQuotient x,hx,Finset.mem_image.mpr ⟨x.quotientSupport,?_,?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hD,hs⟩
    · cases x;rfl
end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0774

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalParentEnergy
Source SHA256: 40121df6d7a7ca0b8908b0ff36d8f326f422331951968759f631d06e60a7c786
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0775


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
open InverseFirstPriorityParents InverseMomentWholePriorityParents InverseWholePriorityValidSource
