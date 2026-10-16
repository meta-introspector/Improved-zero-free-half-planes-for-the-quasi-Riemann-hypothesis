    norm_num
    ring
  · ring

end CubicEisenstein

namespace CubicKubota

open scoped Classical MatrixGroups

section
open ActualEisensteinCubic
open CubicEisenstein

def levelThreeInTwo : Subgroup levelTwo := levelThree.comap levelTwo.subtype

instance levelThreeInTwo_normal : levelThreeInTwo.Normal := by
  constructor
  intro n hn g
  exact (levelThreeConjugate (g:SL(2,ActualEisensteinCubic.O)) ⟨(n:SL(2,ActualEisensteinCubic.O)),hn⟩).property

instance levelThreeInTwo_finiteIndex : levelThreeInTwo.FiniteIndex := by
  let : levelThree.FiniteIndex := levelThree_finiteIndex
  change (levelThree.comap levelTwo.subtype).FiniteIndex
  infer_instance

def rationalLift : SL(2,ℤ)→*levelTwo where
  toFun r := ⟨rationalEmbedding r,rational_mem_levelTwo r⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

def rationalQuotient : SL(2,ℤ)→*(levelTwo ⧸ levelThreeInTwo) :=
  (QuotientGroup.mk' levelThreeInTwo).comp rationalLift

theorem rationalQuotient_surjective : Function.Surjective rationalQuotient := by
  intro q
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective levelThreeInTwo q
  obtain ⟨n,r,hr⟩ := g.property
  refine ⟨r,?_⟩
  let n2 : levelTwo := ⟨(n:SL(2,ActualEisensteinCubic.O)),levelThree_le_levelTwo n.property⟩
  have he : g=n2*rationalLift r := Subtype.ext hr.symm
  have hn : QuotientGroup.mk' levelThreeInTwo n2=1 :=
    (QuotientGroup.eq_one_iff n2).mpr n.property
  change QuotientGroup.mk' levelThreeInTwo (rationalLift r)=_
  rw [he,map_mul,hn,one_mul]

def rationalCongruenceThree : Subgroup (SL(2,ℤ)) := rationalQuotient.ker

instance rationalCongruenceThree_normal : rationalCongruenceThree.Normal := by
  unfold rationalCongruenceThree
  infer_instance

theorem mem_rationalCongruenceThree (r : SL(2,ℤ)) :
    r∈rationalCongruenceThree ↔ rationalEmbedding r∈levelThree := by
  change QuotientGroup.mk' levelThreeInTwo (rationalLift r)=1 ↔ _
  exact QuotientGroup.eq_one_iff _

def rationalQuotientEquiv : (SL(2,ℤ) ⧸ rationalCongruenceThree) ≃*
    (levelTwo ⧸ levelThreeInTwo) :=
  QuotientGroup.quotientKerEquivOfSurjective rationalQuotient rationalQuotient_surjective

instance rationalCongruenceThree_finiteIndex : rationalCongruenceThree.FiniteIndex := by
  have he : rationalCongruenceThree=levelThree.comap rationalEmbedding := by
    ext r
    exact mem_rationalCongruenceThree r
  rw [he]
  let : levelThree.FiniteIndex := levelThree_finiteIndex
  infer_instance

theorem finite_rational_representatives : ∃R : Finset (SL(2,ℤ)),
    ∀g : levelTwo,∃r∈R,(g:SL(2,ActualEisensteinCubic.O))*(rationalEmbedding r)⁻¹∈levelThree := by
  let : Fintype (levelTwo ⧸ levelThreeInTwo) := Fintype.ofFinite _
  let sectionMap : (levelTwo ⧸ levelThreeInTwo)→SL(2,ℤ) :=
    fun q => (rationalQuotient_surjective q).choose
  have hsection : ∀q,rationalQuotient (sectionMap q)=q :=
    fun q => (rationalQuotient_surjective q).choose_spec
  refine ⟨Finset.univ.image sectionMap,fun g => ?_⟩
  let q := QuotientGroup.mk' levelThreeInTwo g
  refine ⟨sectionMap q,Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩,?_⟩
  have he : QuotientGroup.mk' levelThreeInTwo (g*(rationalLift (sectionMap q))⁻¹)=1 := by
    rw [map_mul,map_inv]
    change q*(rationalQuotient (sectionMap q))⁻¹=1
    rw [hsection,mul_inv_cancel]
  exact (QuotientGroup.eq_one_iff (N:=levelThreeInTwo)
    (g*(rationalLift (sectionMap q))⁻¹)).mp he

end

open ActualEisensteinCubic

lemma three_dvd_intCast_iff (a : ℤ) : (3:ActualEisensteinCubic.O)∣(a:ActualEisensteinCubic.O) ↔ (3:ℤ)∣a := by
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨u,v,huv⟩ := ActualEisensteinCoordinates.exists_coordinates x
    have he : ActualEisensteinCoordinates.eval a 0=
        ActualEisensteinCoordinates.eval (3*u) (3*v) := by
      dsimp [ActualEisensteinCoordinates.eval]
      rw [hx,huv]
      push_cast
      ring
    exact ⟨u,(ActualEisensteinCoordinates.unique_coordinates he).1⟩
  · rintro ⟨b,hb⟩
    refine ⟨(b:ActualEisensteinCubic.O),?_⟩
    simpa only [Int.cast_mul,Int.cast_ofNat] using congrArg (fun z : ℤ => (z:ActualEisensteinCubic.O)) hb

lemma mem_levelThree_iff_entries (g : SL(2,ActualEisensteinCubic.O)) : g∈levelThree ↔
    ∀i j,(3:ActualEisensteinCubic.O)∣g i j-(if i=j then 1 else 0) := by
  constructor
  · intro hg i j
    exact levelThree_entry ⟨g,hg⟩ i j
  · intro h
    change Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:ActualEisensteinCubic.O)})) g=1
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change Ideal.Quotient.mk (Ideal.span {(3:ActualEisensteinCubic.O)}) (g i j)=
      (1:Matrix (Fin 2) (Fin 2) (ActualEisensteinCubic.O ⧸ Ideal.span {(3:ActualEisensteinCubic.O)})) i j
    rw [Matrix.one_apply]
    have he := (Ideal.Quotient.mk_eq_mk_iff_sub_mem (g i j) (if i=j then 1 else 0)).mpr
      (Ideal.mem_span_singleton.mpr (h i j))
    simpa only [apply_ite,map_one,map_zero] using he

def rationalReductionThree : SL(2,ℤ)→*SL(2,ZMod 3) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3))

lemma rationalReductionThree_eq_one_iff (g : SL(2,ℤ)) :
    rationalReductionThree g=1 ↔ g∈rationalCongruenceThree := by
  rw [mem_rationalCongruenceThree,mem_levelThree_iff_entries]
  constructor
  · intro hg i j
    have he := congrArg (fun h : SL(2,ZMod 3) => h i j) hg
    change (g i j:ZMod 3)=(1:Matrix (Fin 2) (Fin 2) (ZMod 3)) i j at he
    rw [Matrix.one_apply] at he
    have hd : (3:ℤ)∣g i j-(if i=j then 1 else 0) := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
      simpa only [Int.cast_sub,Int.cast_ite,Int.cast_one,Int.cast_zero] using sub_eq_zero.mpr he
    have hO := (three_dvd_intCast_iff (g i j-(if i=j then 1 else 0))).mpr hd
    simpa only [rationalEmbedding,Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply,Matrix.map_apply,Int.coe_castRingHom,
      Int.cast_sub,Int.cast_ite,Int.cast_one,Int.cast_zero] using hO
  · intro hg
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change (g i j:ZMod 3)=(1:Matrix (Fin 2) (Fin 2) (ZMod 3)) i j
    rw [Matrix.one_apply]
    apply sub_eq_zero.mp
    have hd : (3:ℤ)∣g i j-(if i=j then 1 else 0) := by
      apply (three_dvd_intCast_iff _).mp
      simpa only [rationalEmbedding,Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply,Matrix.map_apply,Int.coe_castRingHom,
        Int.cast_sub,Int.cast_ite,Int.cast_one,Int.cast_zero] using hg i j
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hd
    simpa only [Int.cast_sub,Int.cast_ite,Int.cast_one,Int.cast_zero] using hz

abbrev RationalBruhatIndex := Fin 2 × (Fin 3 ⊕ (Fin 3 × Fin 3))

def rationalBruhatRep (i : RationalBruhatIndex) : SL(2,ℤ) :=
  ModularGroup.S^(2*i.1.val) * match i.2 with
    | Sum.inl a => ModularGroup.T^a.val
    | Sum.inr ab => ModularGroup.T^ab.1.val*ModularGroup.S*ModularGroup.T^ab.2.val

lemma rationalBruhat_complete : ∀g : SL(2,ZMod 3),
    ∃i : RationalBruhatIndex,rationalReductionThree (rationalBruhatRep i)=g := by
  decide +kernel

lemma rationalReductionThree_surjective : Function.Surjective rationalReductionThree := by
  intro g
  obtain ⟨i,hi⟩ := rationalBruhat_complete g
  exact ⟨rationalBruhatRep i,hi⟩

lemma rationalBruhat_injective : Function.Injective
    (fun i : RationalBruhatIndex => rationalReductionThree (rationalBruhatRep i)) := by
  decide +kernel

def rationalBruhatEquiv : RationalBruhatIndex ≃ SL(2,ZMod 3) :=
  Equiv.ofBijective (fun i => rationalReductionThree (rationalBruhatRep i))
    ⟨rationalBruhat_injective,rationalBruhat_complete⟩

lemma card_SLThree : Fintype.card (SL(2,ZMod 3))=24 := by
  rw [←Fintype.card_congr rationalBruhatEquiv]
  decide

lemma rationalCongruenceThree_eq_ker : rationalCongruenceThree=rationalReductionThree.ker := by
  ext g
  exact (rationalReductionThree_eq_one_iff g).symm

def rationalCongruenceEquivSLThree : (SL(2,ℤ) ⧸ rationalCongruenceThree) ≃* SL(2,ZMod 3) :=
  (QuotientGroup.quotientMulEquivOfEq rationalCongruenceThree_eq_ker).trans
    (QuotientGroup.quotientKerEquivOfSurjective rationalReductionThree rationalReductionThree_surjective)

def sourceQuotientEquivSLThree : (levelTwo ⧸ levelThreeInTwo) ≃* SL(2,ZMod 3) :=
  rationalQuotientEquiv.symm.trans rationalCongruenceEquivSLThree

lemma sourceQuotient_card : Nat.card (levelTwo ⧸ levelThreeInTwo)=24 := by
  rw [Nat.card_congr sourceQuotientEquivSLThree.toEquiv,Nat.card_eq_fintype_card,card_SLThree]

lemma levelThreeInTwo_index : levelThreeInTwo.index=24 := sourceQuotient_card

theorem twentyFour_rational_representatives (g : levelTwo) :
    ∃i : RationalBruhatIndex,
      (g:SL(2,ActualEisensteinCubic.O))*(rationalEmbedding (rationalBruhatRep i))⁻¹∈levelThree := by
  obtain ⟨r,hr⟩ := rationalQuotient_surjective (QuotientGroup.mk' levelThreeInTwo g)
  obtain ⟨i,hi⟩ := rationalBruhat_complete (rationalReductionThree r)
  refine ⟨i,?_⟩
  have hred : rationalReductionThree (r*(rationalBruhatRep i)⁻¹)=1 := by
    rw [map_mul,map_inv,hi,mul_inv_cancel]
  have hker := (rationalReductionThree_eq_one_iff _).mp hred
  have hquot : rationalQuotient r=rationalQuotient (rationalBruhatRep i) := by
    have hz : rationalQuotient (r*(rationalBruhatRep i)⁻¹)=1 := hker
    rw [map_mul,map_inv,mul_inv_eq_one] at hz
    exact hz
  have he : QuotientGroup.mk' levelThreeInTwo
      (g*(rationalLift (rationalBruhatRep i))⁻¹)=1 := by
    rw [map_mul,map_inv,←hr,hquot]
    exact mul_inv_cancel _
  exact (QuotientGroup.eq_one_iff (N:=levelThreeInTwo)
    (g*(rationalLift (rationalBruhatRep i))⁻¹)).mp he

end CubicKubota

open scoped BigOperators Classical MatrixGroups
namespace CubicKubota
open ActualEisensteinCubic
open CubicEisenstein

lemma rationalQuotient_eq_iff_reduction (r s : SL(2,ℤ)) :
    rationalQuotient r=rationalQuotient s ↔
      rationalReductionThree r=rationalReductionThree s := by
  have hleft : rationalQuotient r=rationalQuotient s ↔ r*s⁻¹∈rationalCongruenceThree := by
    change _ ↔ rationalQuotient (r*s⁻¹)=1
    rw [map_mul,map_inv,mul_inv_eq_one]
  rw [hleft,←rationalReductionThree_eq_one_iff,map_mul,map_inv,mul_inv_eq_one]

lemma levelTwoComplexCharacter_rationalLift (r : SL(2,ℤ)) :
    levelTwoComplexCharacter (rationalLift r)=1 := levelTwoComplexCharacter_rational r

def rationalCosetEquiv : RationalBruhatIndex ≃ (levelTwo ⧸ levelThreeInTwo) :=
  Equiv.ofBijective (fun i => rationalQuotient (rationalBruhatRep i)) ⟨by
    intro i j h
    exact rationalBruhat_injective ((rationalQuotient_eq_iff_reduction _ _).mp h),by
    intro q
    obtain ⟨r,hr⟩ := rationalQuotient_surjective q
    obtain ⟨i,hi⟩ := rationalBruhat_complete (rationalReductionThree r)
    exact ⟨i,((rationalQuotient_eq_iff_reduction _ _).mpr hi).trans hr⟩⟩

instance sourceQuotientFintype : Fintype (levelTwo ⧸ levelThreeInTwo) := Fintype.ofFinite _

def sourceRationalSection (q : levelTwo ⧸ levelThreeInTwo) : SL(2,ℤ) :=
  rationalBruhatRep (rationalCosetEquiv.symm q)

lemma sourceRationalSection_spec (q : levelTwo ⧸ levelThreeInTwo) :
    rationalQuotient (sourceRationalSection q)=q := rationalCosetEquiv.apply_symm_apply q

def sourceProjection (f : HyperbolicSpace→ℂ) (w : HyperbolicSpace) : ℂ :=
  (24:ℂ)⁻¹ * ∑q : levelTwo ⧸ levelThreeInTwo,
    f (integralComplexMatrix (rationalEmbedding (sourceRationalSection q)) • w)

lemma sourceProjection_eq_twentyFour (f : HyperbolicSpace→ℂ) (w : HyperbolicSpace) :
    sourceProjection f w=(24:ℂ)⁻¹ * ∑i : RationalBruhatIndex,
      f (integralComplexMatrix (rationalEmbedding (rationalBruhatRep i)) • w) := by
  unfold sourceProjection
  congr 1
  rw [←rationalCosetEquiv.sum_comp]
  simp only [sourceRationalSection,Equiv.symm_apply_apply]

lemma sourceSection_translate (f : HyperbolicSpace→ℂ)
    (hf : ∀n : levelThree,∀w,f (complexMatrix n • w)=complexCharacter n*f w)
    (q : levelTwo ⧸ levelThreeInTwo) (g : levelTwo) (w : HyperbolicSpace) :
    f (integralComplexMatrix (rationalEmbedding (sourceRationalSection q)) •
      (integralComplexMatrix (g:SL(2,ActualEisensteinCubic.O)) • w)) =
    levelTwoComplexCharacter g *
      f (integralComplexMatrix (rationalEmbedding (sourceRationalSection
        (q*QuotientGroup.mk' levelThreeInTwo g))) • w) := by
  let r := sourceRationalSection q
  let s := sourceRationalSection (q*QuotientGroup.mk' levelThreeInTwo g)
  let n2 : levelTwo := rationalLift r*g*(rationalLift s)⁻¹
  have hn2 : n2∈levelThreeInTwo := by
    apply (QuotientGroup.eq_one_iff (N:=levelThreeInTwo) n2).mp
    change QuotientGroup.mk' levelThreeInTwo (rationalLift r*g*(rationalLift s)⁻¹)=1
    rw [map_mul,map_mul,map_inv]
    change rationalQuotient r * QuotientGroup.mk' levelThreeInTwo g *
      (rationalQuotient s)⁻¹=1
    rw [sourceRationalSection_spec,sourceRationalSection_spec,mul_inv_cancel]
  let n : levelThree := ⟨(n2:SL(2,ActualEisensteinCubic.O)),hn2⟩
  have hc : complexCharacter n=levelTwoComplexCharacter g := by
    rw [←levelTwoComplexCharacter_restrict n]
    change levelTwoComplexCharacter (rationalLift r*g*(rationalLift s)⁻¹)=_
    rw [map_mul,map_mul,←map_inv rationalLift]
    change levelTwoComplexCharacter (rationalLift r)*levelTwoComplexCharacter g*
      levelTwoComplexCharacter (rationalLift s⁻¹)=_
    rw [levelTwoComplexCharacter_rationalLift,levelTwoComplexCharacter_rationalLift,one_mul,mul_one]
  have he : rationalEmbedding r*(g:SL(2,ActualEisensteinCubic.O))=(n:SL(2,ActualEisensteinCubic.O))*rationalEmbedding s := by
    change _=(rationalEmbedding r*(g:SL(2,ActualEisensteinCubic.O))*(rationalEmbedding s)⁻¹)*rationalEmbedding s
    group
  change f (integralComplexMatrix (rationalEmbedding r) •
    (integralComplexMatrix (g:SL(2,ActualEisensteinCubic.O)) • w))=
    levelTwoComplexCharacter g*f (integralComplexMatrix (rationalEmbedding s) • w)
  rw [←mul_smul,←map_mul,he,map_mul,integralComplexMatrix_levelThree,mul_smul,hf,hc]

theorem sourceProjection_automorphy (f : HyperbolicSpace→ℂ)
    (hf : ∀n : levelThree,∀w,f (complexMatrix n • w)=complexCharacter n*f w)
    (g : levelTwo) (w : HyperbolicSpace) :
    sourceProjection f (integralComplexMatrix (g:SL(2,ActualEisensteinCubic.O)) • w)=
      levelTwoComplexCharacter g * sourceProjection f w := by
  unfold sourceProjection
  simp_rw [sourceSection_translate f hf]
  rw [←Finset.mul_sum]
  rw [Function.Bijective.sum_comp
    (Group.mulRight_bijective (QuotientGroup.mk' levelThreeInTwo g))
    (fun q => f (integralComplexMatrix (rationalEmbedding (sourceRationalSection q)) • w))]
  ring

theorem sourceProjection_fixed (f : HyperbolicSpace→ℂ)
    (hf : ∀g : levelTwo,∀w,f (integralComplexMatrix (g:SL(2,ActualEisensteinCubic.O)) • w)=
      levelTwoComplexCharacter g*f w) (w : HyperbolicSpace) : sourceProjection f w=f w := by
  unfold sourceProjection
  have he : ∀q : levelTwo ⧸ levelThreeInTwo,
      f (integralComplexMatrix (rationalEmbedding (sourceRationalSection q)) • w)=f w := by
    intro q
    have hh := hf (rationalLift (sourceRationalSection q)) w
    rw [levelTwoComplexCharacter_rationalLift,one_mul] at hh
    exact hh
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc : Fintype.card (levelTwo ⧸ levelThreeInTwo)=24 := by
    simpa only [Nat.card_eq_fintype_card] using sourceQuotient_card
  rw [hc]
  push_cast
  ring

lemma sourceProjection_idempotent (f : HyperbolicSpace→ℂ)
    (hf : ∀n : levelThree,∀w,f (complexMatrix n • w)=complexCharacter n*f w) :
    sourceProjection (sourceProjection f)=sourceProjection f := by
  funext w
  exact sourceProjection_fixed _ (sourceProjection_automorphy f hf) w

def sourceEisenstein (s : ℂ) : HyperbolicSpace→ℂ := sourceProjection (hyperbolicEisenstein s)

theorem sourceEisenstein_automorphy (s : ℂ) (hs : 2<s.re) (g : levelTwo) (w : HyperbolicSpace) :
    sourceEisenstein s (integralComplexMatrix (g:SL(2,ActualEisensteinCubic.O)) • w)=
      levelTwoComplexCharacter g*sourceEisenstein s w :=
  sourceProjection_automorphy _ (fun n w => hyperbolicEisenstein_automorphy n s hs w) g w

end CubicKubota

end

end OAI
end OAIOriginalModule0266

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.ScatteringResidues
Source SHA256: 34ef8abe76d4592ff9277f30808d74cefd8c5bd16fff87c433425328ccd50544
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0267



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
open scoped BigOperators Classical Topology

section

lemma scalar_residue_sub_continuous (f g : ℂ→ℂ) (z r : ℂ)
    (hf : Tendsto (fun s => (s-z)*f s) (𝓝[≠] z) (𝓝 r)) (hg : ContinuousAt g z) :
    Tendsto (fun s => (s-z)*(f s-g s)) (𝓝[≠] z) (𝓝 r) := by
  have hlin : Tendsto (fun s : ℂ => s-z) (𝓝[≠] z) (𝓝 (0:ℂ)) := by
    simpa only [id_eq,sub_self] using (tendsto_id.sub_const z).mono_left
      (show 𝓝[≠] z≤𝓝 z from nhdsWithin_le_nhds)
  have hz : Tendsto (fun s => (s-z)*g s) (𝓝[≠] z) (𝓝 (0:ℂ)) := by
    simpa only [zero_mul] using hlin.mul (hg.tendsto.mono_left nhdsWithin_le_nhds)
  simpa only [mul_sub,sub_zero] using hf.sub hz

lemma weightedOutgoingConstant_residue_limit (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) :
    Tendsto (fun s : ℂ => (s-4/3)*weightedOutgoingConstant a b ha ρ s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (kernelCuspHeightFourier a b ha ρ 0 cubicEisensteinResidue)) := by
  apply scalar_residue_sub_continuous _ _ _ _ (kernelCuspHeightFourierFamily_residue_limit a b ha ρ 0)
  exact continuousAt_const.mul
    ((compactHeightMellin_differentiable a b ha ρ).continuous.continuousAt.comp
      (continuousAt_id.sub_const 3))

lemma baseOutgoingConstant_residue_limit :
    Tendsto (fun s : ℂ => (s-4/3)*baseOutgoingConstant s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 cuspConstantAverageResidue) := by
  have hf := kernelCuspAverageFamily_residue_limit 2 3 (by norm_num) (by norm_num)
  change Tendsto _ _ (𝓝 (kernelCuspStripAverage cubicEisensteinResidue)) at hf
  rw [cubicEisensteinResidue_cusp_average] at hf
  apply scalar_residue_sub_continuous _ _ _ _ hf
  exact continuousAt_const.mul
    (cuspMainHeightFactor_differentiableAt (4/3:ℂ) (by norm_num)).continuousAt

theorem kernelCuspHeightFourier_zero_residue (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) :
    kernelCuspHeightFourier a b ha ρ 0 cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(3*(Real.pi:ℂ))*constantArithmeticResidue*
        (∫v in Set.Icc a b,ρ v*(v:ℂ)^(-(4/3:ℂ)-1)) := by
  have hbase : Tendsto cuspScatterHeightFactor (𝓝[≠] (4/3:ℂ))
      (𝓝 (cuspScatterHeightFactor (4/3:ℂ))) :=
    (cuspScatterHeightFactor_differentiableAt (4/3:ℂ) (by norm_num)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hweight : Tendsto (fun s : ℂ => compactHeightMellin a b ρ (-s-1)) (𝓝[≠] (4/3:ℂ))
      (𝓝 (compactHeightMellin a b ρ (-(4/3:ℂ)-1))) :=
    ((compactHeightMellin_differentiable a b ha ρ).continuous.continuousAt.comp
      (continuousAt_id.neg.sub_const 1)).tendsto.mono_left nhdsWithin_le_nhds
  have hleft := ((weightedOutgoingConstant_residue_limit a b ha ρ).mul hbase).comp
    upperVertical_tendsto_cubic_punctured
  have hright := (baseOutgoingConstant_residue_limit.mul hweight).comp
    upperVertical_tendsto_cubic_punctured
  have hevent : (fun t : ℝ =>
      (((4/3:ℂ)+(t:ℂ)*Complex.I-4/3)*weightedOutgoingConstant a b ha ρ ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspScatterHeightFactor ((4/3:ℂ)+(t:ℂ)*Complex.I))
      =ᶠ[𝓝[>] (0:ℝ)] (fun t : ℝ =>
      (((4/3:ℂ)+(t:ℂ)*Complex.I-4/3)*baseOutgoingConstant ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        compactHeightMellin a b ρ (-((4/3:ℂ)+(t:ℂ)*Complex.I)-1)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have hs : (4/3:ℂ)+(t:ℂ)*Complex.I∈{s : ℂ | 1<s.re ∧ 0<s.im} := by
      constructor
      · norm_num
      · simpa using ht
    have he := weightedOutgoingConstant_cross_identity a b ha ρ hs
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*he
  have heq : kernelCuspHeightFourier a b ha ρ 0 cubicEisensteinResidue*cuspScatterHeightFactor (4/3:ℂ)=
      cuspConstantAverageResidue*compactHeightMellin a b ρ (-(4/3:ℂ)-1) :=
    tendsto_nhds_unique_of_eventuallyEq hleft hright hevent
  have hne : cuspScatterHeightFactor (4/3:ℂ)≠0 := by
    intro he
    have hpos := cuspScatterHeightFactor_center_re_pos
    rw [he,Complex.zero_re] at hpos
    exact lt_irrefl 0 hpos
  apply mul_right_cancel₀ hne
  rw [heq,cuspConstantAverageResidue]
  change _=(((9*Real.sqrt 3/2:ℝ):ℂ)*(3*(Real.pi:ℂ))*constantArithmeticResidue*
    compactHeightMellin a b ρ (-(4/3:ℂ)-1))*cuspScatterHeightFactor (4/3:ℂ)
  ring

lemma kernelCuspHeightFourier_zero_residue_seven_thirds (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) :
    kernelCuspHeightFourier a b ha ρ 0 cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(3*(Real.pi:ℂ))*constantArithmeticResidue*
        (∫v in Set.Icc a b,ρ v*(v:ℂ)^(-(7/3:ℂ))) := by
  convert kernelCuspHeightFourier_zero_residue a b ha ρ using 2
  congr 1
  norm_num

local notation "O" => ActualEisensteinCubic.O

def cubicResidualFullModeAmplitude (v : ℝ) (h : ActualEisensteinCubic.O) : ℂ :=
  if h=0 then (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ)
  else cubicResidualFourierCoefficient h*(v:ℂ)*
    schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)

lemma cubicResidualFullModeAmplitude_zero (v : ℝ) :
    cubicResidualFullModeAmplitude v 0=
      (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ) := by
  simp only [cubicResidualFullModeAmplitude,ite_true]

lemma cubicResidualFullModeAmplitude_nonzero (v : ℝ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    cubicResidualFullModeAmplitude v h=cubicResidualFourierCoefficient h*(v:ℂ)*
      schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v) := by
  rw [cubicResidualFullModeAmplitude,ite_eq_right hh]

lemma cubicResidualFullModeAmplitude_zero_density (v : ℝ) (hv : 0<v) :
    cubicResidualFullModeAmplitude v 0/(v:ℂ)^3=
      (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(-(7/3:ℂ)) := by
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hp : (v:ℂ)^(-(7/3:ℂ))=(v:ℂ)^(2/3:ℂ)/(v:ℂ)^3 := by
    rw [show -(7/3:ℂ)=(2/3:ℂ)-3 by ring,Complex.cpow_sub _ _ hv0]
    congr 1
    exact Complex.cpow_natCast _ 3
  rw [cubicResidualFullModeAmplitude_zero,hp]
  ring

lemma cubicResidualFullModeAmplitude_nonzero_density (v : ℝ) (hv : 0<v)
    (h : ActualEisensteinCubic.O) (hh : h≠0) :
    cubicResidualFullModeAmplitude v h/(v:ℂ)^3=cubicResidualFourierCoefficient h*
      (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
  rw [cubicResidualFullModeAmplitude_nonzero v h hh]
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  field_simp

theorem kernelCuspHeightFourier_residue_full (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*
        (∫v in Set.Icc a b,ρ v*(cubicResidualFullModeAmplitude v h/(v:ℂ)^3)) := by
  by_cases hh : h=0
  · subst h
    rw [kernelCuspHeightFourier_zero_residue_seven_thirds a b ha ρ]
    have he : (∫v in Set.Icc a b,ρ v*(cubicResidualFullModeAmplitude v 0/(v:ℂ)^3))=
        ((3*(Real.pi:ℂ))*constantArithmeticResidue)*
          (∫v in Set.Icc a b,ρ v*(v:ℂ)^(-(7/3:ℂ))) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Icc
      intro v hv
      dsimp only
      rw [cubicResidualFullModeAmplitude_zero_density v (ha.trans_le hv.1)]
      ring
    rw [he]
    ring
  · rw [kernelCuspHeightFourier_residue_bessel a b ha ρ h hh]
    have he : (∫v in Set.Icc a b,ρ v*(cubicResidualFullModeAmplitude v h/(v:ℂ)^3))=
        cubicResidualFourierCoefficient h*(∫v in Set.Icc a b,
          ρ v*(schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2)) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Icc
      intro v hv
      dsimp only
      rw [cubicResidualFullModeAmplitude_nonzero_density v (ha.trans_le hv.1) h hh]
      ring
    rw [he]
    ring

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def cubicResidualFunction (w : HyperbolicSpace) : ℂ :=
  (3*Real.pi:ℂ)*constantArithmeticResidue*(hyperbolicHeight w:ℂ)^(2/3:ℂ)+
    cubicResidualNonzeroFunction w

lemma cubicResidualFunction_continuous : Continuous cubicResidualFunction := by
  have hp : Continuous (fun w : HyperbolicSpace => (hyperbolicHeight w:ℂ)^(2/3:ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro w
    exact (Complex.continuousAt_ofReal_cpow_const (hyperbolicHeight w) (2/3:ℂ)
      (Or.inr (hyperbolicHeight_pos w).ne')).comp (f := hyperbolicHeight) hyperbolicHeight_continuous.continuousAt
  exact (continuous_const.mul hp).add cubicResidualNonzeroFunction_continuous

lemma cubicResidualNonzeroSeries_height_continuous (v : ℝ) (hv : 0<v) :
    Continuous (fun z : ℂ => cubicResidualNonzeroSeries (v,z)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hopen : IsOpen {p : ℝ × ℂ | 0<p.1} := isOpen_lt continuous_const continuous_fst
  exact (cubicResidualNonzeroSeries_continuousOn.continuousAt (hopen.mem_nhds hv)).comp
    (f := fun z : ℂ => (v,z)) (by fun_prop)

lemma periodDomain_integrable_of_continuous (f : ℂ→ℂ) (hf : Continuous f) :
    IntegrableOn f periodDomain volume := by
  apply (hf.continuousOn.integrableOn_compact
    (isCompact_closedBall (0:ℂ) (∑i,‖periodBasis i‖))).mono_set
  intro z hz
  simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain z hz

lemma cubicResidualFunction_fourier (v : ℝ) (hv : 0<v) (k : ActualEisensteinCubic.O) :
    (∫z in periodDomain,cubicResidualFunction (upperPoint z v hv)*ShortDraftTrace.breveE (-cuspFrequency k*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(if k=0 then
        (3*Real.pi:ℂ)*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ) else cubicResidualModeAmplitude v k) := by
  have hphase : Continuous (fun z : ℂ => ShortDraftTrace.breveE (-cuspFrequency k*z)) := by
    change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-cuspFrequency k*z)+starRingEnd ℂ (-cuspFrequency k*z))))
    fun_prop
  have hc0 := periodDomain_integrable_of_continuous
    (fun z => ((3*Real.pi:ℂ)*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ))*
      ShortDraftTrace.breveE (-cuspFrequency k*z)) (continuous_const.mul hphase)
  have hcn := periodDomain_integrable_of_continuous
    (fun z => cubicResidualNonzeroSeries (v,z)*ShortDraftTrace.breveE (-cuspFrequency k*z))
    ((cubicResidualNonzeroSeries_height_continuous v hv).mul hphase)
  simp_rw [cubicResidualFunction,cubicResidualNonzeroFunction,
    hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint,add_mul]
  rw [integral_add hc0 hcn,integral_const_mul,integral_cusp_character,cubicResidualNonzeroSeries_fourier v hv k]
  by_cases hk : k=0
  · simp only [ite_eq_left hk,cubicResidualModeAmplitude,mul_zero]
    ring
  · simp only [ite_eq_right hk,mul_zero,zero_add]

lemma cubicResidualFunction_heightFourier (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    (∫w in cuspPeriodStrip a b,cubicResidualFunction w*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(∫v in Set.Icc a b,ρ v*
        ((if h=0 then (3*Real.pi:ℂ)*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ)
          else cubicResidualModeAmplitude v h)/(v:ℂ)^3)) := by
  let g : HyperbolicSpace→ℂ := fun w => cubicResidualFunction w*cuspWeightedFourierPhase ρ h w
  have hg : Continuous g := cubicResidualFunction_continuous.mul (cuspWeightedFourierPhase_continuous ρ h)
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha g hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha g hg),←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos := ha.trans_le hv.1
  have hinner : (∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
      ρ v*(((9*Real.sqrt 3/2:ℝ):ℂ)*(if h=0 then
        (3*Real.pi:ℂ)*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ) else cubicResidualModeAmplitude v h)) := by
    simp_rw [g,cuspCoordinateLift_positive v _ hpos,cuspWeightedFourierPhase,
      hyperbolicHeight_upperPoint,cuspFourierPhase,hyperbolicHorizontal_upperPoint]
    calc
      _ = ρ v*(∫z in periodDomain,cubicResidualFunction (upperPoint z v hpos)*
          ShortDraftTrace.breveE (-cuspFrequency h*z)) := by
        rw [←integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun z => by ring)
      _ = _ := by rw [cubicResidualFunction_fourier v hpos h]
  dsimp only
  rw [hinner]
  ring

lemma cubicResidualFunction_period (v : ℝ) (hv : 0<v) (z : ℂ) (n : ActualEisensteinCubic.O) :
    cubicResidualFunction (upperPoint (z+3*ConcreteTraceCRT.eisEmbedding n) v hv)=
      cubicResidualFunction (upperPoint z v hv) := by
  simp only [cubicResidualFunction,cubicResidualNonzeroFunction,
    hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint,cubicResidualNonzeroSeries_period]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding

lemma kernelCuspHeightPullback_memLp (a b : ℝ) (ha : 0<a) (F : KernelQuotientL2) :
    MemLp (fun w => F (integralOrbitProjection globalKubotaKernel w)) 2
      (hyperbolicVolume.restrict (cuspPeriodStrip a b)) :=
  MemLp.ae_eq (kernelCuspHeightPullback_ae a b ha F)
    (MeasureTheory.Lp.memLp (kernelCuspHeightPullback a b ha F))

lemma kernelCuspCoordinates_memLp (a b : ℝ) (ha : 0<a) (F : KernelQuotientL2) :
    MemLp (fun q : ℝ × ℂ => F (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift q))) 2
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict periodDomain)) := by
  have hm := euclideanToHyperbolic_measurePreserving_on (positiveEuclideanStrip a b)
    (positiveEuclideanStrip_measurable a b) (positiveEuclideanStrip_positive a b ha)
  rw [positiveEuclideanStrip_preimage] at hm
  have hF := (kernelCuspHeightPullback_memLp a b ha F).comp_measurePreserving hm
  have hvol := euclideanVolume_le_heightCube_hyperbolic (positiveEuclideanStrip a b)
    (positiveEuclideanStrip_measurable a b) (positiveEuclideanStrip_positive a b ha)
    (max 1 b) (by positivity) (fun p hp => hp.1.2.trans (le_max_right 1 b))
  have hFE := (hF.smul_measure (c := ENNReal.ofReal ((max 1 b)^3)) ENNReal.ofReal_ne_top).mono_measure hvol
  have hsplit := spatialComplexSplit_preserves_volume.restrict_preimage (s := Set.Icc a b ×ˢ periodDomain)
    (measurableSet_Icc.prod periodDomain_measurable)
  have hback := hsplit.symm
  have hpull := hFE.comp_measurePreserving hback
  simpa only [Measure.prod_restrict, Measure.volume_eq_prod, Function.comp_def,
    positiveEuclideanStrip, cuspCoordinateLift] using hpull

section ProductSections
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {«μ» : Measure α} {ν : Measure β} [SFinite «μ»] [SFinite ν]

lemma complex_memLp_two_sections {f : α × β → ℂ} (hf : MemLp f 2 («μ».prod ν)) :
    ∀ᵐx ∂«μ», MemLp (fun y => f (x,y)) 2 ν := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_left,
    hf.norm.integrable_sq.prod_right_ae] with x hx hi
  exact (memLp_two_iff_integrable_sq_norm hx).mpr hi

end ProductSections

lemma kernelCuspSections_memLp (a b : ℝ) (ha : 0<a) (F : KernelQuotientL2) :
    ∀ᵐv ∂volume.restrict (Set.Icc a b),
      MemLp (fun z : ℂ => F (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v,z)))) 2
        (volume.restrict periodDomain) :=
  complex_memLp_two_sections (kernelCuspCoordinates_memLp a b ha F)

lemma cuspCoordinateLift_measurable : Measurable cuspCoordinateLift :=
  euclideanToHyperbolic_measurable.comp spatialComplexSplit.symm.measurable

lemma kernelCuspFourierCoordinate_integrable (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    IntegrableOn (fun q : ℝ × ℂ =>
      (F (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift q))*
        cuspWeightedFourierPhase ρ h (cuspCoordinateLift q))/(q.1:ℂ)^3)
      (Set.Icc a b ×ˢ periodDomain) volume := by
  let := periodDomain_finiteMeasure
  have hF := (kernelCuspCoordinates_memLp a b ha F).integrable (by norm_num : (1:ℝ≥0∞)≤2)
  have hm : Measurable (fun q : ℝ × ℂ =>
      cuspWeightedFourierPhase ρ h (cuspCoordinateLift q)/(q.1:ℂ)^3) :=
    ((cuspWeightedFourierPhase_continuous ρ h).measurable.comp cuspCoordinateLift_measurable).div
      (by fun_prop)
  have hb : ∀ᵐq ∂((volume.restrict (Set.Icc a b)).prod (volume.restrict periodDomain)),
      ‖cuspWeightedFourierPhase ρ h (cuspCoordinateLift q)/(q.1:ℂ)^3‖≤‖ρ‖/a^3 := by
    rw [Measure.prod_restrict, ←Measure.volume_eq_prod]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod periodDomain_measurable)] with q hq
    have hpos : 0<q.1 := ha.trans_le hq.1.1
    rw [norm_div,norm_pow,Complex.norm_of_nonneg hpos.le]
    calc
      _ ≤ ‖ρ‖/q.1^3 := div_le_div_of_nonneg_right
        (cuspWeightedFourierPhase_bound ρ h (cuspCoordinateLift q)) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
        (pow_le_pow_left₀ ha.le hq.1.1 3)
  have hi := hF.mul_bdd hm.aestronglyMeasurable hb
  simpa only [IntegrableOn, Measure.prod_restrict, ←Measure.volume_eq_prod, mul_div_assoc] using hi

def kernelCuspSliceCoefficient (F : KernelQuotientL2) (h : ActualEisensteinCubic.O) (v : ℝ) : ℂ :=
  (∫z in periodDomain, F (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v,z)))*
    ShortDraftTrace.breveE (-cuspFrequency h*z))/(v:ℂ)^3

lemma kernelCuspHeightFourier_eq_slice_integral (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    kernelCuspHeightFourier a b ha ρ h F =
      ∫v in Set.Icc a b, ρ v*kernelCuspSliceCoefficient F h v := by
  rw [kernelCuspHeightFourier_integral]
  have hg : StronglyMeasurable (fun w =>
      F (integralOrbitProjection globalKubotaKernel w)*cuspWeightedFourierPhase ρ h w) :=
    ((MeasureTheory.Lp.stronglyMeasurable F).comp_measurable (measurable_integralOrbitProjection _)).mul
      (cuspWeightedFourierPhase_continuous ρ h).stronglyMeasurable
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha _ hg.aestronglyMeasurable
    (kernelCuspFourierCoordinate_integrable a b ha ρ h F)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos : 0<v := ha.trans_le hv.1
  simp only [kernelCuspSliceCoefficient]
  rw [←mul_div_assoc]
  congr 1
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only
    rw [cuspWeightedFourierPhase,cuspFourierPhase,cuspCoordinateLift_positive v z hpos,
      hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
    ring)

lemma kernelCuspSliceCoefficient_integrable (a b : ℝ) (ha : 0<a)
    (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    IntegrableOn (kernelCuspSliceCoefficient F h) (Set.Icc a b) volume := by
  have hi := kernelCuspFourierCoordinate_integrable a b ha 1 h F
  rw [IntegrableOn, Measure.volume_eq_prod, ←Measure.prod_restrict] at hi
  apply hi.integral_prod_left.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  have hpos : 0<v := ha.trans_le hv.1
  rw [integral_div, kernelCuspSliceCoefficient]
  apply congrArg (fun c : ℂ => c/(v:ℂ)^3)
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only [kernelCuspSliceCoefficient]
    rw [cuspWeightedFourierPhase,cuspFourierPhase,cuspCoordinateLift_positive v z hpos,
      hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
    simp)

end

section

open scoped BigOperators Classical
open EisensteinEmbedding (omega3)
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma third_character_eq_one_iff_basis (ψ:AddChar (Eis⧸Ideal.span {(3:Eis)}) ℂ) :
    ψ=1 ↔ ψ (Ideal.Quotient.mk _ (1:Eis))=1 ∧
      ψ (Ideal.Quotient.mk _ omega)=1 := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h1,hw⟩
    ext x
    obtain ⟨z,rfl⟩:=Ideal.Quotient.mk_surjective x
    rw [←ActualEisensteinCoordinates.eval_coords z]
    change ψ (Ideal.Quotient.mk _
      (((ActualEisensteinCoordinates.coords z).1:Eis)+
       ((ActualEisensteinCoordinates.coords z).2:Eis)*omega))=1
    rw [map_add,AddChar.map_add_eq_mul]
    have hA:Ideal.Quotient.mk (Ideal.span {(3:Eis)})
        ((ActualEisensteinCoordinates.coords z).1:Eis)=
        (ActualEisensteinCoordinates.coords z).1 • Ideal.Quotient.mk _ (1:Eis):=by
      rw [←map_zsmul]
      simp
    have hB:Ideal.Quotient.mk (Ideal.span {(3:Eis)})
        (((ActualEisensteinCoordinates.coords z).2:Eis)*omega)=
        (ActualEisensteinCoordinates.coords z).2 • Ideal.Quotient.mk _ omega:=by
      rw [←map_zsmul]
      simp only [zsmul_eq_mul]
    rw [hA,hB,AddChar.map_zsmul_eq_zpow,AddChar.map_zsmul_eq_zpow,h1,hw]
    simp

lemma omega3_pow_exp_eq_one_iff (t:ℕ) (b:ℤ) :
    omega3^t*Complex.exp (2*Real.pi*Complex.I*(b:ℂ)/3)=1 ↔
      (3:ℤ)∣(t:ℤ)+b := by
  have hω:omega3=Complex.exp (2*Real.pi*Complex.I/3):=by
    rw [←TraceLambdaPhase.exp_minus_four_pi_div_three]
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    refine ⟨-1,?_⟩
    push_cast
    ring
  rw [hω,←Complex.exp_nat_mul,←Complex.exp_add]
  have he:(t:ℂ)*(2*Real.pi*Complex.I/3)+2*Real.pi*Complex.I*(b:ℂ)/3=
      2*Real.pi*Complex.I*(((t:ℤ)+b:ℤ):ℂ)/3:=by push_cast;ring
  rw [he]
  constructor
  · intro hh
    have hh':Complex.exp (2*Real.pi*Complex.I*((((t:ℤ)+b:ℤ):ℂ)/3))=1:=by
      convert hh using 1 ;ring_nf
    obtain ⟨v,hv⟩:=GeneralPrimitiveTrace.complex_exp_trace_integer hh'
    have hc:(((t:ℤ)+b:ℤ):ℂ)=3*(v:ℂ):=by linear_combination 3*hv
    have hi:(t:ℤ)+b=3*v:=by exact_mod_cast hc
    exact ⟨v,hi⟩
  · rintro ⟨v,hv⟩
    rw [hv]
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨v,?_⟩
    push_cast
    ring

lemma eisEmbedding_omega_actual : eisEmbedding omega=omega3 := by
  have hω:omega=ActualEisensteinCoordinates.eval 0 1:=by
    simp only [ActualEisensteinCoordinates.eval,Int.cast_zero,Int.cast_one,zero_add,one_mul]
    rfl
  rw [hω,eisEmbedding_eval]
  norm_num

lemma trace_third_coordinate (k:Eis) :
    eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
      3 (by norm_num) (Ideal.Quotient.mk _ k)=
      Complex.exp (2*Real.pi*Complex.I*((ActualEisensteinCoordinates.coords k).2:ℂ)/3) := by
  rw [eisTraceModChar,IdealGaussCRT.traceModChar_mk]
  have hh:=breveE_real_trace_of_O 3 k
  norm_num at hh
  convert hh using 1 ;simp only [map_ofNat] ;congr 1 ;ring

end

open scoped BigOperators Classical
open EisensteinEmbedding (omega3)
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma ramified_symbol_primaryCoord (u:Eisˣ) (n j:ℕ)
    (hu:(u:Eis)=omega^j ∨ (u:Eis)=-(omega^j)) (A B:ℤ) :
    symbol (u.val*lambda^n) (primaryCoord A B)=
      (cubicExp (2*A-B))^j*(cubicExp A)^n := by
  have hp:=primaryCoord_primary A B
  rw [symbol_mul_numerator _ _ _ hp,symbol_pow_numerator _ _ hp,
    symbol_lambda_eq_linearRay _ hp,linearRay_primaryCoord]
  norm_num only [one_mul,zero_mul,add_zero]
  congr 1
  rcases hu with hu|hu
  · rw [hu,symbol_pow_numerator _ _ hp,symbol_omega_eq_linearRay _ hp,
      linearRay_primaryCoord]
    ring_nf
  · rw [hu,symbol_neg_numerator _ _ hp,symbol_pow_numerator _ _ hp,
      symbol_omega_eq_linearRay _ hp,linearRay_primaryCoord]
    ring_nf

lemma ramified_symbol_at_one (u:Eisˣ) (n j:ℕ)
    (hu:(u:Eis)=omega^j ∨ (u:Eis)=-(omega^j)) :
    symbol (u.val*lambda^n) (1+3*(1:Eis))=omega^(2*j+n) := by
  have he:(1+3*(1:Eis))=primaryCoord 1 0:=by rw [primaryCoord_eq];norm_num
  rw [he,ramified_symbol_primaryCoord u n j hu]
  norm_num [cubicExp]
  rw [←pow_mul,←pow_add]

lemma ramified_symbol_at_omega (u:Eisˣ) (n j:ℕ)
    (hu:(u:Eis)=omega^j ∨ (u:Eis)=-(omega^j)) :
    symbol (u.val*lambda^n) (1+3*omega)=omega^(2*j) := by
  have he:(1+3*omega)=primaryCoord 0 1:=by rw [primaryCoord_eq];norm_num
  rw [he,ramified_symbol_primaryCoord u n j hu]
  norm_num [cubicExp]
  rw [←pow_mul]

lemma ramifiedFrequencyChar_mk (k:Eis) (u:Eisˣ) (n:ℕ) (x:Eis) :
    ramifiedFrequencyChar k u n (Ideal.Quotient.mk _ x)=
      eisEmbedding (symbol (u.val*lambda^n) (1+3*x))*
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
        3 (by norm_num) (Ideal.Quotient.mk _ (k*x)) := by
  rw [ramifiedFrequencyChar,AddChar.mul_apply,ramifiedQuotientChar,
    IdealGaussCRT.quotientAddChar_mk,AddChar.mulShift_apply,←map_mul]
  rfl

lemma coords_mul_omega_second (k:Eis) :
    (ActualEisensteinCoordinates.coords (k*omega)).2=
      (ActualEisensteinCoordinates.coords k).1-(ActualEisensteinCoordinates.coords k).2 := by
  conv_lhs => rw [←ActualEisensteinCoordinates.eval_coords k]
  have hw:omega=ActualEisensteinCoordinates.eval 0 1:=by
    simp only [ActualEisensteinCoordinates.eval,Int.cast_zero,Int.cast_one,zero_add,one_mul]
    rfl
  rw [hw,ActualEisensteinCoordinates.eval_mul,ShortDraftLatticeCount.coords_eval]
  ring

def ramifiedCongruence (k:Eis) (j n:ℕ):Prop:=
  (3:ℤ)∣(2*(j:ℤ)+(n:ℤ)+(ActualEisensteinCoordinates.coords k).2) ∧
  (3:ℤ)∣(2*(j:ℤ)+(ActualEisensteinCoordinates.coords k).1-
    (ActualEisensteinCoordinates.coords k).2)

lemma ramifiedFrequencyChar_eq_one_iff (k:Eis) (u:Eisˣ) (n j:ℕ)
    (hu:(u:Eis)=omega^j ∨ (u:Eis)=-(omega^j)) :
    ramifiedFrequencyChar k u n=1 ↔ ramifiedCongruence k j n := by
  rw [third_character_eq_one_iff_basis,ramifiedFrequencyChar_mk,
    ramifiedFrequencyChar_mk,ramified_symbol_at_one u n j hu,
    ramified_symbol_at_omega u n j hu,map_pow,map_pow,eisEmbedding_omega_actual,
    mul_one,trace_third_coordinate,trace_third_coordinate,coords_mul_omega_second,
    omega3_pow_exp_eq_one_iff,omega3_pow_exp_eq_one_iff]
  unfold ramifiedCongruence
  push_cast
  simp only [add_sub_assoc]

theorem ramified_arithmetic_explicit_table (h k:Eis) (u:Eisˣ) (n j:ℕ)
    (hn:2≤n) (hu:(u:Eis)=omega^j ∨ (u:Eis)=-(omega^j))
    (hk:3*h=(u.val*lambda^n)*k) :
    arithmeticResidueSum h (u.val*lambda^n)=
      if ramifiedCongruence k j n then ((3^n:ℕ):ℂ)*residueAdditive k 3 1 else 0 := by
  rw [ramified_arithmetic_character_test h k u n hn hk]
  simp only [ramifiedFrequencyChar_eq_one_iff k u n j hu]

def ramifiedUnitIndex (u:Eisˣ):Fin 3:=Classical.choose (unit_eq_sign_omega u)

lemma ramifiedUnitIndex_spec (u:Eisˣ) :
    (u:Eis)=omega^(ramifiedUnitIndex u).val ∨
      (u:Eis)=-(omega^(ramifiedUnitIndex u).val):=
  Classical.choose_spec (unit_eq_sign_omega u)

def explicitRamifiedCoefficient (h:Eis) (u:Eisˣ) (n:ℕ):ℂ:=
  if hd:u.val*lambda^n∣3*h then
    let k:=Classical.choose hd
    if ramifiedCongruence k (ramifiedUnitIndex u).val n then
      ((3^n:ℕ):ℂ)*residueAdditive k 3 1 else 0
  else 0

theorem arithmeticResidueSum_eq_explicitRamifiedCoefficient (h:Eis) (u:Eisˣ)
    (n:ℕ) (hn:2≤n) :
    arithmeticResidueSum h (u.val*lambda^n)=explicitRamifiedCoefficient h u n := by
  unfold explicitRamifiedCoefficient
  split_ifs with hd
  · exact ramified_arithmetic_explicit_table h (Classical.choose hd) u n
      (ramifiedUnitIndex u).val hn (ramifiedUnitIndex_spec u) (Classical.choose_spec hd)
  · by_contra hne
    exact hd (ramified_arithmetic_support h u n hn hne)

theorem scatteringCoefficient_explicit_ramified (s:ℂ) (hs:2<s.re)
    (h:Eis) (hh:h≠0) :
    scatteringCoefficient s h=
      (∑'u:Eisˣ,∑n∈Finset.range (ramifiedFrequencyBound h+1),
        ((3^(n+2):ℕ):ℂ)^(-s)*explicitRamifiedCoefficient h u (n+2)*
          unramifiedCubicGaussSeries s (h*(9*(u.val*lambda^(n+2)))))/
        ((9*Real.sqrt 3/2:ℝ):ℂ) := by
  rw [scatteringCoefficient_unramified_gauss s hs h hh]
  congr 1
  apply tsum_congr
  intro u
  apply Finset.sum_congr rfl
  intro n hn
  rw [arithmeticResidueSum_eq_explicitRamifiedCoefficient h u (n+2) (by omega)]

end CubicEisenstein

end

end OAI
end OAIOriginalModule0267

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.SourceQuotient
Source SHA256: b12e6da893af919f830e88bc51d9201bfd55c33b627220b1ca89a07f7811b7c1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0268


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
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise

open CubicKubota
local notation "O" => ActualEisensteinCubic.O

abbrev SourceKernelQuotient := IntegralOrbitQuotient globalKubotaKernel

def sourceComplexMatrix : levelTwo→*SL(2,ℂ) :=
  integralComplexMatrix.comp levelTwo.subtype

lemma globalKubotaKernel_source_conjugate_mem (M : levelTwo) (N : globalKubotaKernel) :
    (M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹∈globalKubotaKernel :=
  CubicKubota.globalKubotaKernel_conjugate M N N.property

def kernelSourceConjugate (M : levelTwo) : globalKubotaKernel ≃* globalKubotaKernel where
  toFun N := ⟨(M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹,globalKubotaKernel_source_conjugate_mem M N⟩
  invFun N := ⟨(M⁻¹:levelTwo)*(N:SL(2,ActualEisensteinCubic.O))*(M⁻¹:levelTwo)⁻¹,globalKubotaKernel_source_conjugate_mem M⁻¹ N⟩
  left_inv N := by apply Subtype.ext; simp [mul_assoc]
  right_inv N := by apply Subtype.ext; simp [mul_assoc]
  map_mul' N P := by apply Subtype.ext; simp [mul_assoc]

lemma kernelSourceConjugate_coe (M : levelTwo) (N : globalKubotaKernel) :
    (kernelSourceConjugate M N : SL(2,ActualEisensteinCubic.O))=(M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹ := rfl

lemma source_action_respects_kernel (M : levelTwo) (u v : HyperbolicSpace)
    (h : (integralOrbitRel globalKubotaKernel).r u v) :
    (integralOrbitRel globalKubotaKernel).r (sourceComplexMatrix M • u) (sourceComplexMatrix M • v) := by
  obtain ⟨N,hN⟩ := h
  refine ⟨kernelSourceConjugate M N,?_⟩
  change integralComplexMatrix ((M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹) •
    (sourceComplexMatrix M • u)=sourceComplexMatrix M • v
  rw [map_mul,map_mul,map_inv,mul_smul,mul_smul]
  change sourceComplexMatrix M • (integralComplexMatrix (N:SL(2,ActualEisensteinCubic.O)) •
    ((sourceComplexMatrix M)⁻¹ • (sourceComplexMatrix M • u)))=_
  rw [inv_smul_smul,hN]

def kernelSourceAction (M : levelTwo) : SourceKernelQuotient→SourceKernelQuotient :=
  Quotient.map' (fun w => sourceComplexMatrix M • w) (source_action_respects_kernel M)

lemma kernelSourceAction_mk (M : levelTwo) (w : HyperbolicSpace) :
    kernelSourceAction M (integralOrbitProjection globalKubotaKernel w)=
      integralOrbitProjection globalKubotaKernel (sourceComplexMatrix M • w) := rfl

lemma kernelSourceAction_one (q : SourceKernelQuotient) : kernelSourceAction 1 q=q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection globalKubotaKernel (sourceComplexMatrix 1 • w)=integralOrbitProjection globalKubotaKernel w
    rw [map_one,one_smul]

lemma kernelSourceAction_mul (M N : levelTwo) (q : SourceKernelQuotient) :
    kernelSourceAction (M*N) q=kernelSourceAction M (kernelSourceAction N q) := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection globalKubotaKernel (sourceComplexMatrix (M*N) • w)=
      integralOrbitProjection globalKubotaKernel (sourceComplexMatrix M • (sourceComplexMatrix N • w))
    rw [map_mul,mul_smul]

lemma kernelSourceAction_continuous (M : levelTwo) : Continuous (kernelSourceAction M) :=
  (continuous_hyperbolic_action (sourceComplexMatrix M)).quotient_map' (source_action_respects_kernel M)

def kernelSourceHomeomorph (M : levelTwo) : SourceKernelQuotient ≃ₜ SourceKernelQuotient where
  toFun := kernelSourceAction M
  invFun := kernelSourceAction M⁻¹
  left_inv q := by rw [←kernelSourceAction_mul,inv_mul_cancel,kernelSourceAction_one]
  right_inv q := by rw [←kernelSourceAction_mul,mul_inv_cancel,kernelSourceAction_one]
  continuous_toFun := kernelSourceAction_continuous M
  continuous_invFun := kernelSourceAction_continuous M⁻¹

lemma kernelSourceAction_fundamentalDomain (M : levelTwo) :
    IsFundamentalDomain globalKubotaKernel
      ((fun w : HyperbolicSpace => sourceComplexMatrix M • w) '' hyperbolicFundamentalSet globalKubotaKernel)
      hyperbolicVolume := by
  apply (hyperbolicFundamentalSet_isFundamentalDomain globalKubotaKernel
    globalKubotaKernel_le_levelThree).image_of_equiv (MulAction.toPerm (sourceComplexMatrix M))
    (show Measure.QuasiMeasurePreserving (MulAction.toPerm (sourceComplexMatrix M)).symm hyperbolicVolume hyperbolicVolume from by
      exact (measurePreserving_smul (sourceComplexMatrix M)⁻¹ hyperbolicVolume).quasiMeasurePreserving)
    (kernelSourceConjugate M⁻¹).toEquiv
  intro N w
  change sourceComplexMatrix M • (integralComplexMatrix
    ((M⁻¹:levelTwo)*(N:SL(2,ActualEisensteinCubic.O))*(M⁻¹:levelTwo)⁻¹) • w)=
      integralComplexMatrix (N:SL(2,ActualEisensteinCubic.O)) • (sourceComplexMatrix M • w)
  simp only [Subgroup.coe_inv,map_mul,map_inv]
  change sourceComplexMatrix M • (((sourceComplexMatrix M)⁻¹*integralComplexMatrix (N:SL(2,ActualEisensteinCubic.O))*
    ((sourceComplexMatrix M)⁻¹)⁻¹) • w)=_
  simp only [inv_inv,mul_smul,smul_inv_smul]

lemma kernelSourceAction_measurePreserving (M : levelTwo) :
    MeasurePreserving (kernelSourceAction M) (integralQuotientVolume globalKubotaKernel)
      (integralQuotientVolume globalKubotaKernel) := by
  refine ⟨(kernelSourceAction_continuous M).measurable,?_⟩
  let act : HyperbolicSpace→HyperbolicSpace := fun w => sourceComplexMatrix M • w
  have hmap := (measurePreserving_smul (sourceComplexMatrix M) hyperbolicVolume).restrict_image_emb
    (measurableEmbedding_const_smul (sourceComplexMatrix M)) (hyperbolicFundamentalSet globalKubotaKernel)
  have heq : kernelSourceAction M ∘ integralOrbitProjection globalKubotaKernel=
      integralOrbitProjection globalKubotaKernel ∘ act := by ext w; rfl
  change Measure.map (kernelSourceAction M)
    (Measure.map (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)))=_
  rw [Measure.map_map (kernelSourceAction_continuous M).measurable
    (measurable_integralOrbitProjection _),heq,
    ←Measure.map_map (measurable_integralOrbitProjection _) (continuous_hyperbolic_action _).measurable]
  change Measure.map (integralOrbitProjection globalKubotaKernel)
    (Measure.map act (hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)))=_
  rw [hmap.map_eq]
  exact integralQuotientVolume_independent globalKubotaKernel globalKubotaKernel_le_levelThree _
    (kernelSourceAction_fundamentalDomain M)

end CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open CubicKubota

def kernelSourcePullback (M : levelTwo) : KernelQuotientL2 →ₗᵢ[ℂ] KernelQuotientL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (kernelSourceAction M) (kernelSourceAction_measurePreserving M)

lemma kernelSourcePullback_ae_eq (M : levelTwo) (F : KernelQuotientL2) :
    kernelSourcePullback M F=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => F (kernelSourceAction M q) :=
  Lp.coeFn_compMeasurePreserving F (kernelSourceAction_measurePreserving M)

lemma kernelSourcePullback_one (F : KernelQuotientL2) : kernelSourcePullback 1 F=F := by
  apply Lp.ext
  filter_upwards [kernelSourcePullback_ae_eq 1 F] with q hq
  simpa only [kernelSourceAction_one] using hq

lemma kernelSourcePullback_comp (M N : levelTwo) (F : KernelQuotientL2) :
    kernelSourcePullback M (kernelSourcePullback N F)=kernelSourcePullback (N*M) F := by
  have hcomp := (kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp
    (kernelSourcePullback_ae_eq N F)
  apply Lp.ext
  filter_upwards [kernelSourcePullback_ae_eq M (kernelSourcePullback N F),hcomp,
    kernelSourcePullback_ae_eq (N*M) F] with q hp hn hnm
  rw [hp,hnm]
  exact hn.trans (congrArg F (kernelSourceAction_mul N M q).symm)

lemma kernelSourcePullback_surjective (M : levelTwo) : Function.Surjective (kernelSourcePullback M) := by
  intro F
  refine ⟨kernelSourcePullback M⁻¹ F,?_⟩
  rw [kernelSourcePullback_comp,inv_mul_cancel,kernelSourcePullback_one]

def kernelSourceUnitary (M : levelTwo) : KernelQuotientL2 ≃ₗᵢ[ℂ] KernelQuotientL2 :=
  LinearIsometryEquiv.ofSurjective (kernelSourcePullback M) (kernelSourcePullback_surjective M)

lemma kernelSourceUnitary_apply (M : levelTwo) (F : KernelQuotientL2) :
    kernelSourceUnitary M F=kernelSourcePullback M F := rfl

local notation "O" => ActualEisensteinCubic.O

lemma kernelSourceAction_of_kernel (g : levelTwo)
    (hg : (g:SL(2,ActualEisensteinCubic.O))∈globalKubotaKernel) (q : SourceKernelQuotient) :
    kernelSourceAction g q=q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    exact integralOrbitProjection_eq globalKubotaKernel ⟨(g:SL(2,ActualEisensteinCubic.O)),hg⟩ w

lemma rationalCongruenceThree_in_kernel (r : SL(2,ℤ)) (hr : r∈rationalCongruenceThree) :
    rationalEmbedding r∈globalKubotaKernel := by
  have hr3 := (mem_rationalCongruenceThree r).mp hr
  exact (globalKubotaKernel_mem _).mpr ⟨hr3,complexCharacter_rational_intersection r hr3⟩

lemma kernelSourceAction_rational_eq (r s : SL(2,ℤ))
    (hrs : rationalReductionThree r=rationalReductionThree s) (q : SourceKernelQuotient) :
    kernelSourceAction (rationalLift r) q=kernelSourceAction (rationalLift s) q := by
  have hd : r*s⁻¹∈rationalCongruenceThree := by
    apply (rationalReductionThree_eq_one_iff _).mp
    rw [map_mul,map_inv,hrs,mul_inv_cancel]
  have hk := rationalCongruenceThree_in_kernel _ hd
  have he : rationalLift r=rationalLift (r*s⁻¹)*rationalLift s := by
    rw [←map_mul,inv_mul_cancel_right]
  rw [he,kernelSourceAction_mul]
  exact kernelSourceAction_of_kernel _ hk _

lemma kernelSourcePullback_rational_eq (r s : SL(2,ℤ))
    (hrs : rationalReductionThree r=rationalReductionThree s) (F : KernelQuotientL2) :
    kernelSourcePullback (rationalLift r) F=kernelSourcePullback (rationalLift s) F := by
  apply Lp.ext
  filter_upwards [kernelSourcePullback_ae_eq (rationalLift r) F,
    kernelSourcePullback_ae_eq (rationalLift s) F] with q hr hs
  rw [hr,hs,kernelSourceAction_rational_eq r s hrs]

def kernelSourceProjection : KernelQuotientL2 →L[ℂ] KernelQuotientL2 :=
  (24:ℂ)⁻¹ • ∑q : levelTwo ⧸ levelThreeInTwo,
    (kernelSourcePullback (rationalLift (sourceRationalSection q))).toContinuousLinearMap

lemma kernelSourceProjection_apply (F : KernelQuotientL2) :
    kernelSourceProjection F=(24:ℂ)⁻¹ • ∑q : levelTwo ⧸ levelThreeInTwo,
      kernelSourcePullback (rationalLift (sourceRationalSection q)) F := by
  simp only [kernelSourceProjection,_root_.smul_apply,_root_.sum_apply,
    LinearIsometry.coe_toContinuousLinearMap]

lemma kernelSourceProjection_eq_twentyFour (F : KernelQuotientL2) :
    kernelSourceProjection F=(24:ℂ)⁻¹ • ∑i : RationalBruhatIndex,
      kernelSourcePullback (rationalLift (rationalBruhatRep i)) F := by
  rw [kernelSourceProjection_apply]
  congr 1
  rw [←rationalCosetEquiv.sum_comp]
  simp only [sourceRationalSection,Equiv.symm_apply_apply]

lemma norm_kernelSourceProjection_apply (F : KernelQuotientL2) :
    ‖kernelSourceProjection F‖≤‖F‖ := by
  rw [kernelSourceProjection_apply,norm_smul]
  calc
    _ ≤ ‖(24:ℂ)⁻¹‖ * ∑q : levelTwo ⧸ levelThreeInTwo,
      ‖kernelSourcePullback (rationalLift (sourceRationalSection q)) F‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = ‖F‖ := by
      simp only [LinearIsometry.norm_map,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      have hc : Fintype.card (levelTwo ⧸ levelThreeInTwo)=24 := by
        simpa only [Nat.card_eq_fintype_card] using sourceQuotient_card
      rw [hc]
      norm_num
      ring

lemma norm_kernelSourceProjection : ‖kernelSourceProjection‖≤1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (fun F => by simpa using norm_kernelSourceProjection_apply F)

lemma sourceSection_mul_reduction (q : levelTwo ⧸ levelThreeInTwo) (r : SL(2,ℤ)) :
    rationalReductionThree (sourceRationalSection q*r)=
      rationalReductionThree (sourceRationalSection (q*rationalQuotient r)) := by
  apply (rationalQuotient_eq_iff_reduction _ _).mp
  rw [map_mul,sourceRationalSection_spec,sourceRationalSection_spec]

lemma kernelSourcePullback_projection (r : SL(2,ℤ)) (F : KernelQuotientL2) :
    kernelSourcePullback (rationalLift r) (kernelSourceProjection F)=kernelSourceProjection F := by
  rw [kernelSourceProjection_apply,map_smul,map_sum]
  apply congrArg (fun v : KernelQuotientL2 => (24:ℂ)⁻¹ • v)
  simp_rw [kernelSourcePullback_comp,←map_mul]
  have he : ∀q : levelTwo ⧸ levelThreeInTwo,
      kernelSourcePullback (rationalLift (sourceRationalSection q*r)) F=
      kernelSourcePullback (rationalLift (sourceRationalSection (q*rationalQuotient r))) F :=
    fun q => kernelSourcePullback_rational_eq _ _ (sourceSection_mul_reduction q r) F
  simp_rw [he]
  exact Function.Bijective.sum_comp (Group.mulRight_bijective (rationalQuotient r))
    (fun q => kernelSourcePullback (rationalLift (sourceRationalSection q)) F)

lemma kernelSourceProjection_fixed (F : KernelQuotientL2)
    (hF : ∀r : SL(2,ℤ),kernelSourcePullback (rationalLift r) F=F) :
    kernelSourceProjection F=F := by
  rw [kernelSourceProjection_apply]
  simp only [hF,Finset.sum_const,Finset.card_univ]
  have hc : Fintype.card (levelTwo ⧸ levelThreeInTwo)=24 := by
    simpa only [Nat.card_eq_fintype_card] using sourceQuotient_card
  rw [hc]
  rw [←Nat.cast_smul_eq_nsmul ℂ,smul_smul]
  norm_num

lemma kernelSourceProjection_idempotent (F : KernelQuotientL2) :
    kernelSourceProjection (kernelSourceProjection F)=kernelSourceProjection F :=
  kernelSourceProjection_fixed _ (fun r => kernelSourcePullback_projection r F)

end CubicEisenstein

namespace CubicKubota
open ActualEisensteinCubic

def sourceLevelInclusion : levelThree→*levelTwo where
  toFun n := ⟨(n:SL(2,ActualEisensteinCubic.O)),levelThree_le_levelTwo n.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

lemma sourceLevelInclusion_character (n : levelThree) :
    levelTwoComplexCharacter (sourceLevelInclusion n)=complexCharacter n :=
  levelTwoComplexCharacter_restrict n

lemma sourceSection_factor (q : levelTwo ⧸ levelThreeInTwo) (g : levelTwo) :
    ∃n : levelThree,
      rationalLift (sourceRationalSection q)*g=
        sourceLevelInclusion n*rationalLift (sourceRationalSection
          (q*QuotientGroup.mk' levelThreeInTwo g)) ∧
      complexCharacter n=levelTwoComplexCharacter g := by
  let r := sourceRationalSection q
  let s := sourceRationalSection (q*QuotientGroup.mk' levelThreeInTwo g)
  let n2 : levelTwo := rationalLift r*g*(rationalLift s)⁻¹
  have hn2 : n2∈levelThreeInTwo := by
    apply (QuotientGroup.eq_one_iff (N:=levelThreeInTwo) n2).mp
    change QuotientGroup.mk' levelThreeInTwo (rationalLift r*g*(rationalLift s)⁻¹)=1
    rw [map_mul,map_mul,map_inv]
    change rationalQuotient r * QuotientGroup.mk' levelThreeInTwo g *
      (rationalQuotient s)⁻¹=1
    rw [sourceRationalSection_spec,sourceRationalSection_spec,mul_inv_cancel]
  let n : levelThree := ⟨(n2:SL(2,ActualEisensteinCubic.O)),hn2⟩
  refine ⟨n,?_,?_⟩
  · change rationalLift r*g=(rationalLift r*g*(rationalLift s)⁻¹)*rationalLift s
    group
  · rw [←levelTwoComplexCharacter_restrict n]
    change levelTwoComplexCharacter (rationalLift r*g*(rationalLift s)⁻¹)=_
    rw [map_mul,map_mul,←map_inv rationalLift]
    change levelTwoComplexCharacter (rationalLift r)*levelTwoComplexCharacter g*
      levelTwoComplexCharacter (rationalLift s⁻¹)=_
    rw [levelTwoComplexCharacter_rationalLift,levelTwoComplexCharacter_rationalLift,one_mul,mul_one]
end CubicKubota

namespace CubicEisenstein
open CubicKubota

theorem kernelSourceProjection_covariance (F : KernelQuotientL2)
    (hF : ∀n : levelThree,kernelSourcePullback (sourceLevelInclusion n) F=
      complexCharacter n • F) (g : levelTwo) :
    kernelSourcePullback g (kernelSourceProjection F)=
      levelTwoComplexCharacter g • kernelSourceProjection F := by
  rw [kernelSourceProjection_apply,map_smul,map_sum]
  simp_rw [kernelSourcePullback_comp]
  have he : ∀q : levelTwo ⧸ levelThreeInTwo,
      kernelSourcePullback (rationalLift (sourceRationalSection q)*g) F=
      levelTwoComplexCharacter g •
        kernelSourcePullback (rationalLift (sourceRationalSection
          (q*QuotientGroup.mk' levelThreeInTwo g))) F := by
    intro q
    obtain ⟨n,hn,hc⟩ := sourceSection_factor q g
    rw [hn,←kernelSourcePullback_comp,hF,map_smul,hc]
  simp_rw [he]
  rw [←Finset.smul_sum]
  rw [Function.Bijective.sum_comp
    (Group.mulRight_bijective (QuotientGroup.mk' levelThreeInTwo g))
    (fun q => kernelSourcePullback (rationalLift (sourceRationalSection q)) F)]
  rw [smul_comm]

lemma kernelSourceProjection_ae_eq (F : KernelQuotientL2) :
    kernelSourceProjection F=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun x => (24:ℂ)⁻¹ * ∑q : levelTwo ⧸ levelThreeInTwo,
        F (kernelSourceAction (rationalLift (sourceRationalSection q)) x) := by
  rw [kernelSourceProjection_apply]
  have hsum := (Lp.coeFn_finsetSum Finset.univ
    (fun q : levelTwo ⧸ levelThreeInTwo =>
      kernelSourcePullback (rationalLift (sourceRationalSection q)) F)).trans
    (eventuallyEq_sum (fun q _ =>
      kernelSourcePullback_ae_eq (rationalLift (sourceRationalSection q)) F))
  filter_upwards [(Lp.coeFn_smul (24:ℂ)⁻¹ _).trans (hsum.const_smul (24:ℂ)⁻¹)] with x hx
  simpa only [Pi.smul_apply,Finset.sum_apply,smul_eq_mul] using hx

lemma kernelSourceProjection_representative (F : KernelQuotientL2)
    (f : SourceKernelQuotient→ℂ)
    (hf : F=ᵐ[integralQuotientVolume globalKubotaKernel] f) :
    kernelSourceProjection F=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun x => (24:ℂ)⁻¹ * ∑q : levelTwo ⧸ levelThreeInTwo,
        f (kernelSourceAction (rationalLift (sourceRationalSection q)) x) := by
  apply (kernelSourceProjection_ae_eq F).trans
  have hh : (∑q : levelTwo ⧸ levelThreeInTwo, fun x =>
      F (kernelSourceAction (rationalLift (sourceRationalSection q)) x))
      =ᵐ[integralQuotientVolume globalKubotaKernel]
      (∑q : levelTwo ⧸ levelThreeInTwo, fun x =>
      f (kernelSourceAction (rationalLift (sourceRationalSection q)) x)) :=
    eventuallyEq_sum (fun q _ =>
      (kernelSourceAction_measurePreserving (rationalLift (sourceRationalSection q))).quasiMeasurePreserving.ae_eq_comp hf)
  filter_upwards [hh.const_smul (24:ℂ)⁻¹] with x hx
  simpa only [Pi.smul_apply,Finset.sum_apply,smul_eq_mul] using hx

lemma kernelSourceProjection_hyperbolic_average (f : SourceKernelQuotient→ℂ) (w : HyperbolicSpace) :
    (24:ℂ)⁻¹ * ∑q : levelTwo ⧸ levelThreeInTwo,
      f (kernelSourceAction (rationalLift (sourceRationalSection q))
        (integralOrbitProjection globalKubotaKernel w)) =
    sourceProjection (f ∘ integralOrbitProjection globalKubotaKernel) w := rfl

end CubicEisenstein
end

open scoped Classical

namespace CubicEisenstein
open CubicKubota

lemma kernelSourceAction_level (n : levelThree) :
    kernelSourceAction (sourceLevelInclusion n)=kernelLevelAction n := rfl

lemma kernelSourcePullback_level (n : levelThree) :
    kernelSourcePullback (sourceLevelInclusion n)=kernelLevelPullback n := rfl

theorem kernelSourceProjection_covariance_of_level (F : KernelQuotientL2)
    (hF : ∀n : levelThree,kernelLevelPullback n F=complexCharacter n • F) (g : levelTwo) :
    kernelSourcePullback g (kernelSourceProjection F)=
      levelTwoComplexCharacter g • kernelSourceProjection F := by
  apply kernelSourceProjection_covariance F
  intro n
  rw [kernelSourcePullback_level]
  exact hF n

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding

namespace CubicEisenstein
open EisensteinSchwartzPoisson ActualEisensteinCubic ConcreteTraceCRT Module

def periodVector : (Fin 2 → ℝ) ≃L[ℝ] ℂ := periodBasis.equivFunL.symm

lemma periodVector_apply (x : Fin 2 → ℝ) :
    periodVector x = 3 * ((x 0 : ℂ) + (x 1 : ℂ) * omega3) := by
  change periodBasis.equivFun.symm x = _
  rw [Basis.equivFun_symm_apply, Fin.sum_univ_two, periodBasis_zero, periodBasis_one]
  simp only [Complex.real_smul]
  ring

def periodTorus (z : ℂ) : UnitAddTorus (Fin 2) :=
  fun i => (periodBasis.equivFunL z i : UnitAddCircle)

lemma periodTorus_periodVector (x : Fin 2 → ℝ) :
    periodTorus (periodVector x) = fun i => (x i : UnitAddCircle) := by
  change (fun i => ((periodBasis.equivFunL (periodBasis.equivFunL.symm x)) i : UnitAddCircle)) = _
  rw [periodBasis.equivFunL.apply_symm_apply]

def periodFrequencyEquiv : (Fin 2 → ℤ) ≃ ActualEisensteinCubic.O :=
  (finTwoArrowEquiv ℤ).trans dualFrequencyEquiv

lemma periodFrequencyEquiv_apply (n : Fin 2 → ℤ) :
    periodFrequencyEquiv n = dualFrequencyEquiv (n 0, n 1) := rfl

lemma periodVector_character (n : Fin 2 → ℤ) (x : Fin 2 → ℝ) :
    ShortDraftTrace.breveE (cuspFrequency (periodFrequencyEquiv n) * periodVector x) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((n 0 : ℂ) * (x 0 : ℂ) + (n 1 : ℂ) * (x 1 : ℂ))) := by
  have hlam : eisLam ≠ 0 := by
    exact eisLam_ne_zero
  have harg : cuspFrequency (periodFrequencyEquiv n) * periodVector x =
      (eisEmbedding (dualFrequencyEquiv (n 0,n 1)) *
        ((x 0 : ℂ) + (x 1 : ℂ) * omega3)) / eisLam := by
    rw [cuspFrequency, periodVector_apply, periodFrequencyEquiv_apply]
    field_simp
  rw [harg, ←paperE, paperE_eq_exp, dualFrequencyEquiv_coordinates]
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hw : omega3.re = -(1/2:ℝ) := by norm_num [omega3]
  congr 1
  simp only [complexPoint, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, hw, omega3_im]
  push_cast
  field_simp
  ring

lemma periodTorus_mFourier (n : Fin 2 → ℤ) (z : ℂ) :
    UnitAddTorus.mFourier n (periodTorus z) =
      ShortDraftTrace.breveE (cuspFrequency (periodFrequencyEquiv n) * z) := by
  obtain ⟨x, rfl⟩ := periodVector.surjective z
  rw [periodTorus_periodVector, periodVector_character]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Fin.prod_univ_two,
    fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [←Complex.exp_add]
  congr 1
  ring

lemma periodFrequencyEquiv_neg (n : Fin 2 → ℤ) :
    periodFrequencyEquiv (-n) = -periodFrequencyEquiv n := by
  apply eisEmbedding_injective
  change eisEmbedding (ActualEisensteinCoordinates.eval (-n 0 + -n 1) (-n 0)) =
    eisEmbedding (-ActualEisensteinCoordinates.eval (n 0 + n 1) (n 0))
  rw [map_neg, eisEmbedding_eval, eisEmbedding_eval]
  push_cast
  ring

lemma cuspFrequency_neg (h : ActualEisensteinCubic.O) : cuspFrequency (-h) = -cuspFrequency h := by
  simp only [cuspFrequency, map_neg, neg_div]

lemma periodVector_eq_lattice (x : Fin 2 → ℝ) :
    periodVector x = eisensteinLatticeMap 3 (by norm_num) (Complex.measurableEquivPi.symm x) := by
  rw [periodVector_apply]
  simp [eisensteinLatticeMap, Complex.measurableEquivPi_symm_apply, mul_comm]

lemma periodVector_map_volume :
    Measure.map periodVector volume = ENNReal.ofReal (2/(9*Real.sqrt 3)) • volume := by
  have heq : (periodVector : (Fin 2 → ℝ) → ℂ) =
      eisensteinLatticeMap 3 (by norm_num) ∘ Complex.measurableEquivPi.symm :=
    funext periodVector_eq_lattice
  rw [heq, ←Measure.map_map (eisensteinLatticeMap 3 (by norm_num)).continuous.measurable
    Complex.measurableEquivPi.symm.measurable, Complex.volume_preserving_equiv_pi.symm.map_eq]
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar volume
    (eisensteinLatticeMap 3 (by norm_num)).toLinearEquiv.isUnit_det'.ne_zero
  change Measure.map (eisensteinLatticeMap 3 (by norm_num)) volume =
    ENNReal.ofReal (inverseJacobian (eisensteinLatticeMap 3 (by norm_num))) • volume at hmap
  rw [hmap, eisenstein_inverseJacobian]
  norm_num [mul_comm]

def periodCube : Set (Fin 2 → ℝ) := {x | ∀i, x i ∈ Set.Ico 0 1}

lemma periodVector_preimage_domain : periodVector ⁻¹' periodDomain = periodCube := by
  ext x
  change (∀i, periodBasis.repr (periodBasis.equivFun.symm x) i ∈ Set.Ico 0 1) ↔ _
  simp only [←Basis.equivFun_apply, periodBasis.equivFun.apply_symm_apply]
  rfl

lemma periodDomain_integral_coordinates (f : ℂ → ℂ) :
    (2/(9*Real.sqrt 3):ℝ) • (∫z in periodDomain, f z) =
      ∫x in periodCube, f (periodVector x) := by
  have h := periodVector.toHomeomorph.toMeasurableEquiv.measurableEmbedding.setIntegral_map
    f periodDomain («μ» := (volume : Measure (Fin 2 → ℝ)))
  change (∫z in periodDomain, f z ∂Measure.map periodVector volume) =
    ∫x in periodVector ⁻¹' periodDomain, f (periodVector x) at h
  rw [periodVector_map_volume, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), periodVector_preimage_domain] at h
  exact h

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma periodCube_ae_Ioc : periodCube =ᵐ[volume]
    {x : Fin 2 → ℝ | ∀i, x i ∈ Set.Ioc 0 1} := by
  rw [volume_pi]
  have h := Measure.ae_eq_set_pi («μ» := fun _ : Fin 2 => (volume : Measure ℝ))
    (I := Set.univ) (s := fun _ => Set.Ico (0:ℝ) 1) (t := fun _ => Set.Ioc (0:ℝ) 1)
    (fun _ _ => Ico_ae_eq_Ioc)
  simpa only [Set.pi, Set.mem_univ, forall_true_left, periodCube] using h

lemma periodTorus_integral (f : UnitAddTorus (Fin 2) → ℂ) :
    (∫t, f t) = (2/(9*Real.sqrt 3):ℝ) • (∫z in periodDomain, f (periodTorus z)) := by
  rw [periodDomain_integral_coordinates, UnitAddTorus.integral_preimage f (fun _ => 0)]
  simp only [zero_add, periodTorus_periodVector]
  exact setIntegral_congr_set periodCube_ae_Ioc.symm

lemma periodTorus_fourierCoeff (f : UnitAddTorus (Fin 2) → ℂ) (n : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff f n = (2/(9*Real.sqrt 3):ℝ) •
      (∫z in periodDomain, f (periodTorus z) *
        ShortDraftTrace.breveE (-cuspFrequency (periodFrequencyEquiv n)*z)) := by
  rw [UnitAddTorus.mFourierCoeff, periodTorus_integral]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only
    rw [periodTorus_mFourier, periodFrequencyEquiv_neg, cuspFrequency_neg]
    exact mul_comm _ _)

lemma periodTorus_L2_ext (F G : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (h : ∀h : ActualEisensteinCubic.O,
      (∫z in periodDomain, F (periodTorus z)*ShortDraftTrace.breveE (-cuspFrequency h*z)) =
      ∫z in periodDomain, G (periodTorus z)*ShortDraftTrace.breveE (-cuspFrequency h*z)) : F=G := by
  apply UnitAddTorus.mFourierBasis.repr.injective
  ext n
  rw [UnitAddTorus.mFourierBasis_repr, UnitAddTorus.mFourierBasis_repr,
    periodTorus_fourierCoeff, periodTorus_fourierCoeff, h]

end CubicEisenstein

end

end OAI
end OAIOriginalModule0268

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.OppositeCusp
Source SHA256: a9405a37a1c385d5c32bd3cbdf6f8904d0ed100f59e283fb11984fd9cc9ad155
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0269


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

open scoped BigOperators Classical MatrixGroups Matrix
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

abbrev PrimaryLower:={c:Eis//(3:Eis)∣c-1}
abbrev OppositeData:=Σc:PrimaryLower,{x:Eis//IsCoprime c.val x}

lemma primaryLower_primary (c:PrimaryLower):lambda^2∣c.val-1:=lambda_sq_dvd_three.trans c.2
lemma primaryLower_ne_zero (c:PrimaryLower):c.val≠0:=primary_ne_zero c.val (primaryLower_primary c)

def oppositeDataToPrimitive (p:OppositeData):PrimitiveRow:=
  ⟨![-3*p.2.val,p.1.val],by
    change IsCoprime (-3*p.2.val) p.1.val ∧ (3:Eis)∣-3*p.2.val ∧ (3:Eis)∣p.1.val-1
    refine ⟨?_,⟨-p.2.val,by ring⟩,p.1.2⟩
    simpa only [neg_mul] using
      ((primary_coprime_three p.1.val (primaryLower_primary p.1)).mul_right p.2.2).symm.neg_left⟩

lemma oppositeDataToPrimitive_bijective:Function.Bijective oppositeDataToPrimitive:=by
  constructor
  · rintro ⟨c,x,hx⟩ ⟨d,y,hy⟩ h
    have hrow:=congrArg Subtype.val h
    have hcd:c=d:=by
      apply Subtype.ext
      exact congrFun hrow 1
    subst d
    have hxy:x=y:=by
      have he:-(3:Eis)*x=-(3:Eis)*y:=congrFun hrow 0
      exact mul_left_cancel₀ (by norm_num : -(3:Eis)≠0) he
    subst y
    rfl
  · intro r
    obtain ⟨t,ht⟩:=r.2.2.1
    let c:PrimaryLower:=⟨r.1 1,r.2.2.2⟩
    have hx:IsCoprime c.val (-t):=by
      have hh:IsCoprime c.val (3*t):=by simpa only [c,ht] using r.2.1.symm
      exact (hh.of_isCoprime_of_dvd_right (dvd_mul_left t 3)).neg_right
    refine ⟨⟨c,-t,hx⟩,Subtype.ext ?_⟩
    funext i
    fin_cases i
    · change -3*(-t)=r.1 0
      rw [ht]
      ring
    · rfl

def oppositeDataEquiv:OppositeData≃PrimitiveRow:=
  Equiv.ofBijective oppositeDataToPrimitive oppositeDataToPrimitive_bijective

def oppositeMatrix:SL(2,ℂ):=⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩

lemma rowOperator_opposite (v:Fin 2→ℂ):rowOperator oppositeMatrix v=![v 1,-v 0]:=by
  rw [rowOperator_apply]
  funext i
  fin_cases i <;> simp [oppositeMatrix,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

def oppositeEisenstein (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ):ℂ:=
  eisenstein (oppositeMatrix*upperSection z v hv) s

lemma rowHeight_eq_shiftedHeightKernel (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ)
    (c d:Eis) (hc:c≠0):
    ((v/(‖eisEmbedding c*z+eisEmbedding d‖^2+‖eisEmbedding c‖^2*v^2):ℝ):ℂ)^s=
      ((‖eisEmbedding c‖^2:ℝ):ℂ)^(-s)*
        shiftedHeightKernel v s (eisEmbedding d/eisEmbedding c) z:=by
  have hc':=eisEmbedding_ne_zero hc
  have hnorm:0<‖eisEmbedding c‖^2:=sq_pos_of_pos (norm_pos_iff.mpr hc')
  have hfac:eisEmbedding c*z+eisEmbedding d=eisEmbedding c*(z+eisEmbedding d/eisEmbedding c):=by field_simp
  have heq:v/(‖eisEmbedding c*z+eisEmbedding d‖^2+‖eisEmbedding c‖^2*v^2)=
      ((‖eisEmbedding c‖^2*v)*(1+‖(z+eisEmbedding d/eisEmbedding c)/(v:ℂ)‖^2))⁻¹:=by
    rw [hfac,norm_mul,mul_pow,norm_div,Complex.norm_real,Real.norm_of_nonneg hv.le]
    field_simp
    ;ring
  unfold shiftedHeightKernel hyperbolicKernel
  rw [heq,Complex.ofReal_inv,Complex.inv_cpow_ofReal_nonneg (by positivity),←Complex.cpow_neg]
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (mul_nonneg hnorm.le hv.le) (by positivity),
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hnorm.le hv.le]
  ring

def oppositeTerm (z:ℂ) (v:ℝ) (s:ℂ) (c x:Eis):ℂ:=
  eisEmbedding (symbol (3*x) c)*
    ((v/(‖eisEmbedding c*z+eisEmbedding (3*x)‖^2+‖eisEmbedding c‖^2*v^2):ℝ):ℂ)^s

lemma oppositeTerm_eq_shifted (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ)
    (c x:Eis) (hc:c≠0):
    oppositeTerm z v s c x=
      (eisEmbedding (symbol (3*x) c)*((‖eisEmbedding c‖^2:ℝ):ℂ)^(-s))*
        shiftedHeightKernel v s (eisEmbedding (3*x)/eisEmbedding c) z:=by
  rw [oppositeTerm,rowHeight_eq_shiftedHeightKernel z v hv s c (3*x) hc]
  ring

lemma opposite_summand (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) (p:OppositeData):
    summand (oppositeMatrix*upperSection z v hv) s
      (primitiveRowEquiv.symm (oppositeDataEquiv p))=
      oppositeTerm z v s p.1.val p.2.val:=by
  let r:Fin 2→ℂ:=![eisEmbedding p.1.val,eisEmbedding (3*p.2.val)]
  have hr:rowOperator oppositeMatrix
      (embeddedRow (primitiveRowEquiv.symm (oppositeDataEquiv p)))=r:=by
    rw [embeddedRow, primitiveRowEquiv_symm_row, rowOperator_opposite]
    funext i
    fin_cases i <;>
      simp [oppositeDataEquiv, Equiv.ofBijective_apply, oppositeDataToPrimitive, r, map_mul]
  have hr0:r≠0:=by
    intro hh
    have he:=congrFun hh 0
    exact eisEmbedding_ne_zero (primaryLower_ne_zero p.1) he
  have hp:0<heightDenominator z v r:=heightDenominator_pos z v hv r hr0
  have hphase:(cosetCharacter (primitiveRowEquiv.symm (oppositeDataEquiv p)))⁻¹=
      eisEmbedding (symbol (3*p.2.val) p.1.val):=by
    rw [inverse_cosetCharacter_eq_row_symbol,primitiveRowEquiv_symm_row]
    change eisEmbedding (symbol (-3*p.2.val) p.1.val)=_
    rw [neg_mul,symbol_neg_numerator _ _ (primaryLower_primary p.1)]
  rw [summand,←rowOperator_mul,hr,rowEnergy_upperSection,hphase]
  change _=eisEmbedding (symbol (3*p.2.val) p.1.val)*
    ((v/heightDenominator z v r:ℝ):ℂ)^s
  have hi:((v/heightDenominator z v r:ℝ):ℂ)=
      (((heightDenominator z v r/v:ℝ):ℂ))⁻¹:=by
    simp only [Complex.ofReal_div,inv_div]
  rw [hi,Complex.inv_cpow_ofReal_nonneg (div_nonneg hp.le hv.le),Complex.cpow_neg]

theorem oppositeEisenstein_eq_rows (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ):
    oppositeEisenstein z v hv s=∑'p:OppositeData,oppositeTerm z v s p.1.val p.2.val:=by
  rw [oppositeEisenstein,eisenstein,←primitiveRowEquiv.symm.tsum_eq,
    ←oppositeDataEquiv.tsum_eq]
  exact tsum_congr (opposite_summand z v hv s)

theorem opposite_rows_summable_norm (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re):
    Summable (fun p:OppositeData=>‖oppositeTerm z v s p.1.val p.2.val‖):=by
  have hh:=(oppositeDataEquiv.trans primitiveRowEquiv.symm).summable_iff.mpr
    (summable_norm_summand (oppositeMatrix*upperSection z v hv) s hs)
  exact hh.congr (fun p=>congrArg norm (opposite_summand z v hv s p))

def primaryLowerIdealEquiv:PrimaryLower≃GoodIdeal where
  toFun c:=⟨Ideal.span {c.val},by rw [primaryGenerator_span c.val (primaryLower_ne_zero c) (primaryLower_primary c)];exact primaryLower_ne_zero c⟩
  invFun I:=⟨primaryGenerator I.val,three_dvd_primary_sub_one _ (primaryGenerator_spec I.val I.2).2⟩
  left_inv c:=Subtype.ext (primaryGenerator_span c.val (primaryLower_ne_zero c) (primaryLower_primary c))
  right_inv I:=Subtype.ext (primaryGenerator_spec I.val I.2).1

end

section

open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

abbrev CoprimeElement (c:Eis):={x:Eis//IsCoprime c x}

def cubicResidueElementMap (c:Eis) (p:CubicUnitResidue c×Eis):CoprimeElement c:=
  ⟨GaussianShiftedPartition.representative c p.1.val+c*p.2,by
    apply (isUnit_quotient_span_iff c _).mp
    have hc:Ideal.Quotient.mk (Ideal.span {c}) c=0:=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    simpa only [map_add,map_mul,hc,zero_mul,add_zero,
      GaussianShiftedPartition.representative_spec] using p.1.2⟩

lemma cubicResidueElementMap_bijective (c:Eis) (hc:c≠0):
    Function.Bijective (cubicResidueElementMap c):=by
  have hmod (r:CubicUnitResidue c) (n:Eis):
      Ideal.Quotient.mk (Ideal.span {c})
        (GaussianShiftedPartition.representative c r.val+c*n)=r.val:=by
    have hzero:Ideal.Quotient.mk (Ideal.span {c}) c=0:=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    rw [map_add,map_mul,hzero,zero_mul,add_zero,GaussianShiftedPartition.representative_spec]
  constructor
  · rintro ⟨r,n⟩ ⟨t,m⟩ h
    have he:=congrArg Subtype.val h
    change GaussianShiftedPartition.representative c r.val+c*n=
      GaussianShiftedPartition.representative c t.val+c*m at he
    have hrt:r=t:=Subtype.ext (by
      simpa only [hmod] using congrArg (Ideal.Quotient.mk (Ideal.span {c})) he)
    subst t
    have hnm:n=m:=mul_left_cancel₀ hc (add_left_cancel he)
    subst m
    rfl
  · intro x
    let r:CubicUnitResidue c:=⟨Ideal.Quotient.mk (Ideal.span {c}) x.val,
      (isUnit_quotient_span_iff c x.val).mpr x.2⟩
    have hdiv:c∣x.val-GaussianShiftedPartition.representative c r.val:=by
      apply Ideal.mem_span_singleton.mp
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      exact (GaussianShiftedPartition.representative_spec c r.val).symm
    obtain ⟨n,hn⟩:=hdiv
    refine ⟨(r,n),Subtype.ext ?_⟩
    change GaussianShiftedPartition.representative c r.val+c*n=x.val
    linear_combination -hn

def cubicResidueElementEquiv (c:Eis) (hc:c≠0):
    CubicUnitResidue c×Eis≃CoprimeElement c:=
  Equiv.ofBijective (cubicResidueElementMap c) (cubicResidueElementMap_bijective c hc)

lemma oppositeTerm_shift (z:ℂ) (v:ℝ) (s:ℂ) (c x n:Eis):
    oppositeTerm z v s c (x+c*n)=oppositeTerm (z+3*eisEmbedding n) v s c x:=by
  have hsym:symbol (3*(x+c*n)) c=symbol (3*x) c:=symbol_congr ⟨3*n,by ring⟩
  have harg:eisEmbedding c*z+eisEmbedding (3*(x+c*n))=
      eisEmbedding c*(z+3*eisEmbedding n)+eisEmbedding (3*x):=by
    simp only [map_mul,map_add,map_ofNat]
    ring
  rw [oppositeTerm,oppositeTerm,hsym,harg]

def oppositeGaussSum (h c:Eis):ℂ:=
  ∑'r:CubicUnitResidue c,
    eisEmbedding (symbol (3*GaussianShiftedPartition.representative c r.val) c)*
      residueAdditive h c (3*GaussianShiftedPartition.representative c r.val)

theorem oppositeGaussSum_eq (h:Eis) (c:PrimaryLower):
    oppositeGaussSum h c.val=cubicUnitGaussSum (9*h) c.val:=by
  have hp:=primaryLower_primary c
  have hc:=primaryLower_ne_zero c
  have he:oppositeGaussSum h c.val=
      eisEmbedding (symbol 3 c.val)*cubicUnitGaussSum h c.val:=by
    rw [oppositeGaussSum,cubicUnitGaussSum,←tsum_mul_left]
    apply tsum_congr
    intro r
    rw [symbol_mul_numerator _ _ _ hp,map_mul]
    have hadd:residueAdditive h c.val (3*GaussianShiftedPartition.representative c.val r.val)=
        residueAdditive (3*h) c.val (GaussianShiftedPartition.representative c.val r.val):=by
      unfold residueAdditive cuspFrequency
      simp only [map_mul,map_ofNat]
      congr 1
      ring
    rw [hadd]
    ring
  rw [he]
  have hs:=cubicUnitGaussSum_phase_shift h 1 c.val hc hp (by
    simpa only [mul_one] using (primary_coprime_three c.val hp).symm)
  simpa only [symbol_one_numerator c.val hp,map_one,one_mul,mul_one,mul_comm h 9] using hs

def oppositeArithmeticSeries (s:ℂ) (h:Eis):ℂ:=
  ∑'c:PrimaryLower,((‖eisEmbedding c.val‖^2:ℝ):ℂ)^(-s)*oppositeGaussSum h c.val

theorem oppositeArithmeticSeries_eq (s:ℂ) (h:Eis):
    oppositeArithmeticSeries s h=unramifiedCubicGaussSeries s (9*h):=by
  rw [oppositeArithmeticSeries,←primaryLowerIdealEquiv.symm.tsum_eq,unramifiedCubicGaussSeries]
  apply tsum_congr
  intro I
  rw [oppositeGaussSum_eq]
  change ((‖eisEmbedding (primaryGenerator I.val)‖^2:ℝ):ℂ)^(-s)*
    cubicUnitGaussSum (9*h) (primaryGenerator I.val)=_
  rw [eisEmbedding_norm_sq_eq_absNorm_span,(primaryGenerator_spec I.val I.2).1,
    Complex.ofReal_natCast]

end

section

open MeasureTheory Set Filter Module
open scoped BigOperators Classical ENNReal MatrixGroups Matrix
open ActualEisensteinCubic ConcreteTraceCRT

lemma continuous_inverse_fixed_left_operator (a:SL(2,ℂ)) (v:ℝ) (hv:0<v):
    Continuous (fun z:ℂ=>rowOperator (a*upperSection z v hv)⁻¹):=by
  have he (z:ℂ):rowOperator (a*upperSection z v hv)⁻¹=
      (rowOperator a⁻¹).comp (rowOperator (upperSection z v hv)⁻¹):=by
    ext u
    simp only [mul_inv_rev,ContinuousLinearMap.comp_apply,rowOperator_mul]
  simp_rw [he]
  exact continuous_const.clm_comp (continuous_inverse_upper_operator v hv)

lemma exists_fixed_left_rowBound (a:SL(2,ℂ)) (v:ℝ) (hv:0<v):
    ∃C:ℝ,0<C ∧ ∀z∈periodDomain,rowBound (a*upperSection z v hv)≤C:=by
  have hc:Continuous (fun z:ℂ=>rowBound (a*upperSection z v hv)):=
    continuous_const.mul (continuous_const.add (continuous_inverse_fixed_left_operator a v hv).norm)
  let R:ℝ:=∑i:Fin 2,‖periodBasis i‖
  obtain ⟨C,hC⟩:=(isCompact_closedBall (0:ℂ) R).bddAbove_image hc.continuousOn
  refine ⟨max 1 C,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro z hz
  apply (hC ?_).trans (le_max_right _ _)
  exact ⟨z,by simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain z hz,rfl⟩

lemma continuous_fixed_left_summand (a:SL(2,ℂ)) (v:ℝ) (hv:0<v)
    (s:ℂ) (x:CuspCosets):
    Continuous (fun z:ℂ=>summand (a*upperSection z v hv) s x):=by
  simp_rw [summand,←rowOperator_mul,rowEnergy_upperSection]
  apply continuous_const.mul
  apply Continuous.cpow
  · apply Complex.continuous_ofReal.comp
    unfold heightDenominator
    fun_prop
  · exact continuous_const
  · intro z
    apply Complex.ofReal_mem_slitPlane.mpr
    exact div_pos (heightDenominator_pos z v hv _
      (rowOperator_ne_zero a _ (embeddedRow_ne_zero x))) hv

lemma fixed_left_summable_majorant (a:SL(2,ℂ)) (v:ℝ) (hv:0<v)
    (s:ℂ) (hs:2<s.re):
    ∃M:CuspCosets→ℝ,Summable M ∧ (∀x,0≤M x) ∧
      ∀z∈periodDomain,∀x,‖summand (a*upperSection z v hv) s x‖≤M x:=by
  obtain ⟨C,hC,hbound⟩:=exists_fixed_left_rowBound a v hv
  refine ⟨fun x=>C^(2*s.re)*‖rowCoordinates (cosetRow x)‖^(-(2*s.re)),?_,?_,?_⟩
  · have hsumm:=summable_integer_four_rpow (2*s.re) (by linarith)
    have hinj:Function.Injective (fun x:CuspCosets=>rowCoordinates (cosetRow x)):=
      rowCoordinates_injective.comp cosetRow_injective
    exact (hsumm.comp_injective hinj).mul_left _
  · intro x
    positivity
  · intro z hz x
    apply (norm_summand_bound (a*upperSection z v hv) s (by linarith) x).trans
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (rowBound_pos _).le (hbound z hz) (by linarith)) (by positivity)

theorem hasSum_integral_fixed_left_Eisenstein (a:SL(2,ℂ)) (v:ℝ) (hv:0<v)
    (s freq:ℂ) (hs:2<s.re):
    HasSum (fun x:CuspCosets=>∫z in periodDomain,
      summand (a*upperSection z v hv) s x*ShortDraftTrace.breveE (-freq*z))
      (∫z in periodDomain,eisenstein (a*upperSection z v hv) s*ShortDraftTrace.breveE (-freq*z)):=by
  let:Countable CuspCosets:=(rowCoordinates_injective.comp cosetRow_injective).countable
  let:=periodDomain_finiteMeasure
  obtain ⟨M,hM,hMnonneg,hbound⟩:=fixed_left_summable_majorant a v hv s hs
  have hchar:Continuous (fun z:ℂ=>ShortDraftTrace.breveE (-freq*z)):=by
    change Continuous (fun z:ℂ=>Complex.exp (2*Real.pi*Complex.I*((-freq*z)+starRingEnd ℂ (-freq*z))))
    fun_prop
  exact hasSum_integral_of_dominated_convergence
    («μ»:=volume.restrict periodDomain)
    (fun (x:CuspCosets) (_:ℂ)=>M x)
    (fun x=>((continuous_fixed_left_summand a v hv s x).mul hchar).aestronglyMeasurable.restrict)
    (fun x=>(ae_restrict_mem periodDomain_measurable).mono fun z hz=>by
      simpa only [Pi.mul_apply,norm_mul,breveE_norm,mul_one] using hbound z hz x)
    (Eventually.of_forall fun _=>hM)
    (integrable_const (∑'x,M x))
    (Eventually.of_forall fun z=>(summable_summand (a*upperSection z v hv) s hs).hasSum.mul_right
      (ShortDraftTrace.breveE (-freq*z)))

end

section

open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def oppositeIntegral (v:ℝ) (s freq:ℂ) (c x:Eis):ℂ:=
  ∫z in periodDomain,oppositeTerm z v s c x*ShortDraftTrace.breveE (-freq*z)

theorem hasSum_oppositeIntegrals (v:ℝ) (hv:0<v) (s freq:ℂ) (hs:2<s.re):
    HasSum (fun p:OppositeData=>oppositeIntegral v s freq p.1.val p.2.val)
      (∫z in periodDomain,oppositeEisenstein z v hv s*ShortDraftTrace.breveE (-freq*z)):=by
  have hh:=(oppositeDataEquiv.trans primitiveRowEquiv.symm).hasSum_iff.mpr
    (hasSum_integral_fixed_left_Eisenstein oppositeMatrix v hv s freq hs)
  apply hh.congr_fun
  intro p
  apply integral_congr_ae
  exact Eventually.of_forall fun z=>by
    dsimp only [Equiv.trans_apply]
    rw [opposite_summand]

lemma oppositeTerm_integrable (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (c x:Eis) (hc:c≠0):Integrable (fun z=>oppositeTerm z v s c x):=by
  simp_rw [oppositeTerm_eq_shifted _ v hv s c x hc]
  exact (shiftedHeightKernel_integrable v hv s _ hs).const_mul _

lemma oppositeIntegral_sum_translate (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (h c x:Eis) (hc:c≠0):
    (∑'n:Eis,oppositeIntegral v s (cuspFrequency h) c (x+c*n))=
      ∫z:ℂ,oppositeTerm z v s c x*ShortDraftTrace.breveE (-cuspFrequency h*z):=by
  have hint:=trace_mul_integrable (fun z=>oppositeTerm z v s c x)
    (oppositeTerm_integrable v hv s hs c x hc) (cuspFrequency h)
  rw [integral_eq_period_integrals _ hint]
  apply tsum_congr
  intro n
  apply integral_congr_ae
  exact Eventually.of_forall fun z=>by
    dsimp only [oppositeIntegral]
    rw [oppositeTerm_shift,cuspFrequency_negative_period]

lemma oppositeTerm_fourier_integral (v:ℝ) (hv:0<v) (s freq:ℂ)
    (c x:Eis) (hc:c≠0):
    (∫z:ℂ,oppositeTerm z v s c x*ShortDraftTrace.breveE (-freq*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (freq*v))*
        ((‖eisEmbedding c‖^2:ℝ):ℂ)^(-s)*
        (eisEmbedding (symbol (3*x) c)*
          ShortDraftTrace.breveE (freq*eisEmbedding (3*x)/eisEmbedding c)):=by
  simp_rw [oppositeTerm_eq_shifted _ v hv s c x hc,mul_assoc]
  rw [integral_const_mul,integral_const_mul,
    traceIntegral_shiftedHeightKernel v hv s (eisEmbedding (3*x)/eisEmbedding c) freq]
  ring_nf

lemma oppositeDenominator_integral_formula (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re)
    (h:Eis) (c:PrimaryLower):
    (∑'x:CoprimeElement c.val,oppositeIntegral v s (cuspFrequency h) c.val x.val)=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*
        ((‖eisEmbedding c.val‖^2:ℝ):ℂ)^(-s)*oppositeGaussSum h c.val:=by
  have hf:Summable (fun x:CoprimeElement c.val=>oppositeIntegral v s (cuspFrequency h) c.val x.val):=
    (hasSum_oppositeIntegrals v hv s (cuspFrequency h) hs).summable.sigma_factor c
  have hsum:=(cubicResidueElementEquiv c.val (primaryLower_ne_zero c)).summable_iff.mpr hf
  change Summable (fun q:CubicUnitResidue c.val×Eis=>
    oppositeIntegral v s (cuspFrequency h) c.val
      (GaussianShiftedPartition.representative c.val q.1.val+c.val*q.2)) at hsum
  rw [←(cubicResidueElementEquiv c.val (primaryLower_ne_zero c)).tsum_eq]
  change (∑'q:CubicUnitResidue c.val×Eis,
    oppositeIntegral v s (cuspFrequency h) c.val
      (GaussianShiftedPartition.representative c.val q.1.val+c.val*q.2))=_
  rw [hsum.tsum_prod]
  change (∑'r:CubicUnitResidue c.val,∑'n:Eis,
    oppositeIntegral v s (cuspFrequency h) c.val
      (GaussianShiftedPartition.representative c.val r.val+c.val*n))=_
  simp_rw [oppositeIntegral_sum_translate v hv s (by linarith) h c.val _ (primaryLower_ne_zero c),
    oppositeTerm_fourier_integral v hv s (cuspFrequency h) c.val _ (primaryLower_ne_zero c)]
  exact tsum_mul_left

lemma unramifiedCubicGaussSeries_twentySeven (s:ℂ) (h:Eis):
    unramifiedCubicGaussSeries s (27*h)=unramifiedCubicGaussSeries s h:=by
  apply tsum_congr
  intro I
  congr 1
  have hp:lambda^2∣primaryGenerator I.val-1:=(primaryGenerator_spec I.val I.2).2
  simpa only [show (3:Eis)^3=27 by norm_num,mul_comm h 27] using
    cubicUnitGaussSum_cube_shift h (primaryGenerator I.val) 3 I.2 hp
      (primary_coprime_three _ hp)

theorem oppositeEisenstein_fourier (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) (h:Eis):
    (∫z in periodDomain,oppositeEisenstein z v hv s*
      ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*
        unramifiedCubicGaussSeries s (9*h):=by
  have hh:=hasSum_oppositeIntegrals v hv s (cuspFrequency h) hs
  rw [←hh.tsum_eq,hh.summable.tsum_sigma]
  simp_rw [oppositeDenominator_integral_formula v hv s hs h]
  rw [←oppositeArithmeticSeries_eq s h,oppositeArithmeticSeries]
  have he (c:PrimaryLower):
      (v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v)*
        ((‖eisEmbedding c.val‖^2:ℝ):ℂ)^(-s)*oppositeGaussSum h c.val=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*
        (((‖eisEmbedding c.val‖^2:ℝ):ℂ)^(-s)*oppositeGaussSum h c.val):=by ring
  simp_rw [he]
  exact tsum_mul_left

theorem oppositeEisenstein_fourier_unramified (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) (h:Eis):
    (∫z in periodDomain,oppositeEisenstein z v hv s*
      ShortDraftTrace.breveE (-(eisEmbedding h/eisLam)*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s ((eisEmbedding h/eisLam)*v))*
        unramifiedCubicGaussSeries s h:=by
  have hf:cuspFrequency (3*h)=eisEmbedding h/eisLam:=by
    unfold cuspFrequency
    rw [map_mul,map_ofNat]
    field_simp
  have hh:=oppositeEisenstein_fourier v hv s hs (3*h)
  rw [hf,show (9:Eis)*(3*h)=27*h by ring,unramifiedCubicGaussSeries_twentySeven] at hh
  exact hh

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev PeriodTorusL2 := Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))

def periodIocCube : Set (Fin 2→ℝ) := {x | ∀i,x i∈Set.Ioc 0 (0+1)}

def periodCovolumeDensity : ℝ≥0∞ := ENNReal.ofReal (2/(9*Real.sqrt 3))

lemma periodCovolumeDensity_ne_zero : periodCovolumeDensity≠0 := by
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))

lemma periodIocCube_measurable : MeasurableSet periodIocCube :=
  MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)

lemma periodIocCube_ae : periodCube=ᵐ[volume]periodIocCube := by
  simpa only [periodIocCube,zero_add] using periodCube_ae_Ioc

def periodSection (t : UnitAddTorus (Fin 2)) : ℂ :=
  periodVector ((UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0:ℝ)) t).val)

lemma periodSection_measurableEmbedding : MeasurableEmbedding periodSection :=
  periodVector.toHomeomorph.toMeasurableEquiv.measurableEmbedding.comp
    ((MeasurableEmbedding.subtype_coe periodIocCube_measurable).comp
      (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0:ℝ))).measurableEmbedding)

lemma periodTorus_measurable : Measurable periodTorus := by
  apply Measurable.of_eval
  intro i
  exact AddCircle.measurable_mk'.comp
    ((measurable_pi_apply i).comp periodBasis.equivFunL.continuous.measurable)

lemma periodTorus_section (t : UnitAddTorus (Fin 2)) : periodTorus (periodSection t)=t := by
  rw [periodSection,periodTorus_periodVector]
  exact (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0:ℝ))).symm_apply_apply t

lemma periodVector_Ioc_measurePreserving :
    MeasurePreserving periodVector (volume.restrict periodIocCube)
      (periodCovolumeDensity • volume.restrict periodDomain) := by
  refine ⟨periodVector.continuous.measurable,?_⟩
  rw [←Measure.restrict_congr_set periodIocCube_ae,←periodVector_preimage_domain,
    ←Measure.restrict_map periodVector.continuous.measurable periodDomain_measurable,
    periodVector_map_volume,Measure.restrict_smul]
  rfl

lemma periodSection_measurePreserving :
    MeasurePreserving periodSection volume
      (periodCovolumeDensity • volume.restrict periodDomain) :=
  periodVector_Ioc_measurePreserving.comp
    ((measurePreserving_subtype_coe periodIocCube_measurable).comp
      (UnitAddTorus.measurePreserving_equivPiIoc (fun _ : Fin 2 => (0:ℝ))))

lemma periodTorus_measurePreserving :
    MeasurePreserving periodTorus (periodCovolumeDensity • volume.restrict periodDomain) volume := by
  refine ⟨periodTorus_measurable,?_⟩
  rw [←periodSection_measurePreserving.map_eq,
    Measure.map_map periodTorus_measurable periodSection_measurableEmbedding.measurable]
  have he : periodTorus ∘ periodSection=id := funext periodTorus_section
  rw [he,Measure.map_id]

lemma periodSection_torus_ae :
    (fun z => periodSection (periodTorus z))=ᵐ[volume.restrict periodDomain] (fun z : ℂ => z) := by
  apply (Measure.ae_ennreal_smul_measure_iff periodCovolumeDensity_ne_zero).mp
  rw [←periodSection_measurePreserving.map_eq]
  apply periodSection_measurableEmbedding.ae_map_iff.mpr
  exact Eventually.of_forall (fun t => by dsimp only; rw [periodTorus_section])

lemma periodSection_memLp (f : ℂ→ℂ) (hf : MemLp f 2 (volume.restrict periodDomain)) :
    MemLp (f ∘ periodSection) 2 volume :=
  (hf.smul_measure (by simp [periodCovolumeDensity])).comp_measurePreserving
    periodSection_measurePreserving

def periodTorusL2Lift (f : ℂ→ℂ) (hf : MemLp f 2 (volume.restrict periodDomain)) : PeriodTorusL2 :=
  (periodSection_memLp f hf).toLp (f ∘ periodSection)

lemma periodTorusL2Lift_ae (f : ℂ→ℂ) (hf : MemLp f 2 (volume.restrict periodDomain)) :
    periodTorusL2Lift f hf=ᵐ[volume]f ∘ periodSection :=
  MemLp.coeFn_toLp (periodSection_memLp f hf)

lemma periodTorusL2Lift_pullback (f : ℂ→ℂ) (hf : MemLp f 2 (volume.restrict periodDomain)) :
    (fun z => periodTorusL2Lift f hf (periodTorus z))=ᵐ[volume.restrict periodDomain]f := by
  have he := periodTorus_measurePreserving.quasiMeasurePreserving.ae_eq_comp (periodTorusL2Lift_ae f hf)
  have he' := (Measure.ae_ennreal_smul_measure_iff periodCovolumeDensity_ne_zero).mp he
  filter_upwards [he',periodSection_torus_ae] with z hz hsec
  change periodTorusL2Lift f hf (periodTorus z)=f (periodSection (periodTorus z)) at hz
  rw [hsec] at hz
  exact hz

lemma periodTorusL2Lift_frequency_integral (f : ℂ→ℂ)
    (hf : MemLp f 2 (volume.restrict periodDomain)) (h : ActualEisensteinCubic.O) :
    (∫z in periodDomain,periodTorusL2Lift f hf (periodTorus z)*
      ShortDraftTrace.breveE (-cuspFrequency h*z))=
    ∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency h*z) := by
  apply integral_congr_ae
  filter_upwards [periodTorusL2Lift_pullback f hf] with z hz
  rw [hz]

lemma periodTorusL2Lift_fourierCoeff (f : ℂ→ℂ) (hf : MemLp f 2 (volume.restrict periodDomain))
    (n : Fin 2→ℤ) :
    UnitAddTorus.mFourierCoeff (periodTorusL2Lift f hf) n=(2/(9*Real.sqrt 3):ℝ) •
      (∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency (periodFrequencyEquiv n)*z)) := by
  rw [periodTorus_fourierCoeff]
  congr 1
  apply integral_congr_ae
  filter_upwards [periodTorusL2Lift_pullback f hf] with z hz
  rw [hz]

theorem periodDomain_L2_ext (f g : ℂ→ℂ)
    (hf : MemLp f 2 (volume.restrict periodDomain))
    (hg : MemLp g 2 (volume.restrict periodDomain))
    (h : ∀h : ActualEisensteinCubic.O,
      (∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency h*z))=
        ∫z in periodDomain,g z*ShortDraftTrace.breveE (-cuspFrequency h*z)) :
    f=ᵐ[volume.restrict periodDomain]g := by
  have he : periodTorusL2Lift f hf=periodTorusL2Lift g hg := by
    apply periodTorus_L2_ext
    intro hfreq
    rw [periodTorusL2Lift_frequency_integral,periodTorusL2Lift_frequency_integral,h]
  filter_upwards [periodTorusL2Lift_pullback f hf,periodTorusL2Lift_pullback g hg] with z hz hz'
  rw [←hz,←hz',he]

end CubicEisenstein

end

end OAI
end OAIOriginalModule0269

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.ResidualFourierExpansion
Source SHA256: 412e4049ef936e30bad3e286d9e73a6e6e70c5bf66a18ee355844c06413581a1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0270



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
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O

lemma cubicResidualFullMode_density_integrable (a b : ℝ) (ha : 0<a) (h : ActualEisensteinCubic.O) :
    IntegrableOn (fun v : ℝ => cubicResidualFullModeAmplitude v h/(v:ℂ)^3)
      (Set.Icc a b) volume := by
  by_cases hh : h=0
  · subst h
    have hi : IntegrableOn (fun v : ℝ =>
        (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(-(7/3:ℂ)))
        (Set.Icc a b) volume := by
      apply ContinuousOn.integrableOn_Icc
      intro v hv
      exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const v
        (-(7/3:ℂ)) (Or.inr (ha.trans_le hv.1).ne'))).continuousWithinAt
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (cubicResidualFullModeAmplitude_zero_density v (ha.trans_le hv.1)).symm
  · apply ((cubicBesselHeight_integrable a b ha h hh).const_mul
      (cubicResidualFourierCoefficient h)).congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (cubicResidualFullModeAmplitude_nonzero_density v (ha.trans_le hv.1) h hh).symm

lemma cubicEisensteinResidue_slice_coefficient_ae (a b : ℝ) (ha : 0<a) (h : ActualEisensteinCubic.O) :
    kernelCuspSliceCoefficient cubicEisensteinResidue h =ᵐ[volume.restrict (Set.Icc a b)]
      (fun v => ((9*Real.sqrt 3/2:ℝ):ℂ)*(cubicResidualFullModeAmplitude v h/(v:ℂ)^3)) := by
  apply interval_ae_eq_of_boundedContinuous_height_tests a b _ _
    (kernelCuspSliceCoefficient_integrable a b ha h cubicEisensteinResidue)
    ((cubicResidualFullMode_density_integrable a b ha h).const_mul _)
  intro ρ
  rw [←kernelCuspHeightFourier_eq_slice_integral a b ha ρ h cubicEisensteinResidue,
    kernelCuspHeightFourier_residue_full a b ha ρ h,←integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun v => by ring)

lemma cubicEisensteinResidue_all_slice_coefficients_ae (a b : ℝ) (ha : 0<a) :
    ∀ᵐv ∂volume.restrict (Set.Icc a b), ∀h : ActualEisensteinCubic.O,
      kernelCuspSliceCoefficient cubicEisensteinResidue h v =
        ((9*Real.sqrt 3/2:ℝ):ℂ)*(cubicResidualFullModeAmplitude v h/(v:ℂ)^3) := by
  let : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  exact ae_all_iff.mpr (fun h => cubicEisensteinResidue_slice_coefficient_ae a b ha h)

lemma cubicEisensteinResidue_all_fourier_integrals_ae (a b : ℝ) (ha : 0<a) :
    ∀ᵐv ∂volume.restrict (Set.Icc a b), ∀h : ActualEisensteinCubic.O,
      (∫z in periodDomain,
        cubicEisensteinResidue (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v,z)))*
          ShortDraftTrace.breveE (-cuspFrequency h*z)) =
        ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicResidualFullModeAmplitude v h := by
  filter_upwards [cubicEisensteinResidue_all_slice_coefficients_ae a b ha,
    ae_restrict_mem measurableSet_Icc] with v hv hvmem
  intro h
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ha.trans_le hvmem.1).ne'
  have he := hv h
  unfold kernelCuspSliceCoefficient at he
  rw [←mul_div_assoc] at he
  exact (div_left_inj' (pow_ne_zero 3 hv0)).mp he

end

local notation "O" => ActualEisensteinCubic.O

lemma cubicResidualFunction_fourier_full (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) :
    (∫z in periodDomain,cubicResidualFunction (upperPoint z v hv)*
      ShortDraftTrace.breveE (-cuspFrequency h*z)) =
        ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicResidualFullModeAmplitude v h := by
  rw [cubicResidualFunction_fourier v hv h]
  congr 1
  by_cases hh : h=0
  · simp only [hh,cubicResidualFullModeAmplitude,ite_true]
  · simp only [hh,cubicResidualFullModeAmplitude,cubicResidualModeAmplitude,ite_false]

lemma cubicResidualFunction_height_continuous (v : ℝ) (hv : 0<v) :
    Continuous (fun z : ℂ => cubicResidualFunction (upperPoint z v hv)) := by
  have hc := cubicResidualNonzeroSeries_height_continuous v hv
  simp only [cubicResidualFunction,cubicResidualNonzeroFunction,
    hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
  fun_prop

lemma cubicResidualFunction_height_memLp (v : ℝ) (hv : 0<v) :
    MemLp (fun z : ℂ => cubicResidualFunction (cuspCoordinateLift (v,z))) 2
      (volume.restrict periodDomain) := by
  simp_rw [cuspCoordinateLift_positive v _ hv]
  have hc := cubicResidualFunction_height_continuous v hv
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hn : Continuous (fun z : ℂ => ‖cubicResidualFunction (upperPoint z v hv)‖^2) := by
    fun_prop
  apply (hn.continuousOn.integrableOn_compact
    (isCompact_closedBall (0:ℂ) (∑i,‖periodBasis i‖))).mono_set
  intro z hz
  simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain z hz

theorem cubicEisensteinResidue_cell_slices_ae (a b : ℝ) (ha : 0<a) :
    ∀ᵐv ∂volume.restrict (Set.Icc a b),
      (fun z : ℂ => cubicEisensteinResidue
        (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v,z))))
      =ᵐ[volume.restrict periodDomain]
        (fun z => cubicResidualFunction (cuspCoordinateLift (v,z))) := by
  filter_upwards [cubicEisensteinResidue_all_fourier_integrals_ae a b ha,
    kernelCuspSections_memLp a b ha cubicEisensteinResidue,
    ae_restrict_mem measurableSet_Icc] with v hfour hL hv
  have hpos : 0<v := ha.trans_le hv.1
  apply periodDomain_L2_ext _ _ hL (cubicResidualFunction_height_memLp v hpos)
  intro h
  rw [hfour h]
  symm
  simpa only [cuspCoordinateLift_positive v _ hpos] using
    cubicResidualFunction_fourier_full v hpos h

theorem cubicEisensteinResidue_cell_product_ae (a b : ℝ) (ha : 0<a) :
    (fun q : ℝ × ℂ => cubicEisensteinResidue
      (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift q)))
    =ᵐ[(volume.restrict (Set.Icc a b)).prod (volume.restrict periodDomain)]
      (fun q => cubicResidualFunction (cuspCoordinateLift q)) := by
  apply (Measure.ae_prod_iff_ae_ae ?_).mpr
  · exact cubicEisensteinResidue_cell_slices_ae a b ha
  · exact measurableSet_eq_fun
      ((MeasureTheory.Lp.stronglyMeasurable cubicEisensteinResidue).measurable.comp
        ((measurable_integralOrbitProjection _).comp cuspCoordinateLift_measurable))
      (cubicResidualFunction_continuous.measurable.comp cuspCoordinateLift_measurable)

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal Pointwise MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota

lemma periodDomain_memLp_of_continuous (f : ℂ→ℂ) (hf : Continuous f) :
    MemLp f 2 (volume.restrict periodDomain) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable.restrict).mpr
  apply (((hf.norm.pow 2).continuousOn).integrableOn_compact
    (isCompact_closedBall (0:ℂ) (∑i,‖periodBasis i‖))).mono_set
  intro z hz
  simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain z hz

lemma upperTranslation_mem_kernel (n : ActualEisensteinCubic.O) :
    (upperTranslation n : SL(2,ActualEisensteinCubic.O))∈globalKubotaKernel := by
  exact (globalKubotaKernel_mem _).mpr
    ⟨(upperTranslation n).property,complexCharacter_upperTranslation n⟩

lemma kernelProjection_upper_period (v : ℝ) (hv : 0<v) (z : ℂ) (n : ActualEisensteinCubic.O) :
    integralOrbitProjection globalKubotaKernel (upperPoint (z+3*eisEmbedding n) v hv)=
      integralOrbitProjection globalKubotaKernel (upperPoint z v hv) := by
  let M : globalKubotaKernel := ⟨upperTranslation n,upperTranslation_mem_kernel n⟩
  have ha : integralComplexMatrix (M:SL(2,ActualEisensteinCubic.O)) • upperPoint z v hv=
      upperPoint (z+3*eisEmbedding n) v hv := by
    change (QuotientGroup.mk (complexMatrix (upperTranslation n)*upperSection z v hv) : HyperbolicSpace)=_
    rw [upperTranslation_section]
    rfl
  rw [←ha,integralOrbitProjection_eq]

lemma ae_eq_of_periodDomain_eq (f g : ℂ→ℂ)
    (hf : ∀(n : ActualEisensteinCubic.O)(z : ℂ),f (z+3*eisEmbedding n)=f z)
    (hg : ∀(n : ActualEisensteinCubic.O)(z : ℂ),g (z+3*eisEmbedding n)=g z)
    (he : f=ᵐ[volume.restrict periodDomain]g) : f=ᵐ[volume]g := by
  have hp (p : periodLattice) (z : ℂ) : f (p+ᵥz)=f z ∧ g (p+ᵥz)=g z := by
    obtain ⟨n,rfl⟩ := periodEquiv.surjective p
    change f (3*eisEmbedding n+z)=f z ∧ g (3*eisEmbedding n+z)=g z
    rw [add_comm]
    exact ⟨hf n z,hg n z⟩
  have hi : ∀p : periodLattice,p+ᵥ{z : ℂ | f z≠g z}={z : ℂ | f z≠g z} := by
    intro p
    ext z
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change (f ((-p)+ᵥz)≠g ((-p)+ᵥz)) ↔ f z≠g z
    rw [(hp (-p) z).1,(hp (-p) z).2]
  have hz : volume ({z : ℂ | f z≠g z}∩periodDomain)=0 := by
    change ∀ᵐz ∂volume.restrict periodDomain,f z=g z at he
    rw [ae_restrict_iff' periodDomain_measurable] at he
    rw [ae_iff] at he
    have hs : {z : ℂ | f z≠g z}∩periodDomain =
        {z : ℂ | ¬(z∈periodDomain → f z=g z)} := by
      ext z
      simp only [Set.mem_ofPred_eq,Set.mem_inter_iff]
      tauto
    rw [hs]
    exact he
  change ∀ᵐz ∂volume,f z=g z
  rw [ae_iff]
  exact periodDomain_fundamental.measure_zero_of_invariant _ hi hz

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding

lemma positive_height_interval_cover :
    Set.Ioi (0:ℝ) = ⋃n : ℕ,Set.Icc (1/((n:ℝ)+1)) ((n:ℝ)+1) := by
  ext v
  constructor
  · intro hv
    obtain ⟨n,hn⟩ := exists_nat_gt (max v (1/v))
    have hN : 0<(n:ℝ)+1 := by positivity
    have hvp : 0<v := hv
    have hvN : v≤(n:ℝ)+1 := by linarith [le_max_left v (1/v)]
    have hinv : 1/v≤(n:ℝ)+1 := by linarith [le_max_right v (1/v)]
    have hlow : 1/((n:ℝ)+1)≤v := by
      apply (div_le_iff₀ hN).mpr
      have hh := (div_le_iff₀ hvp).mp hinv
      nlinarith
    exact Set.mem_iUnion.mpr ⟨n,hlow,hvN⟩
  · intro hv
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hv
    exact lt_of_lt_of_le (by positivity : 0<(1:ℝ)/((n:ℝ)+1)) hn.1

lemma hyperbolic_ae_of_coordinate_ae (f g : HyperbolicSpace→ℂ)
    (hf : Measurable f) (hg : Measurable g)
    (he : ∀ᵐq ∂(volume.restrict (Set.Ioi (0:ℝ))).prod (volume : Measure ℂ),
      f (cuspCoordinateLift q)=g (cuspCoordinateLift q)) : f=ᵐ[hyperbolicVolume]g := by
  have hm := spatialComplexSplit_preserves_volume.restrict_preimage
    (s := Set.Ioi (0:ℝ) ×ˢ (Set.univ : Set ℂ)) (measurableSet_Ioi.prod MeasurableSet.univ)
  have htarget : (volume : Measure (ℝ × ℂ)).restrict (Set.Ioi 0 ×ˢ (Set.univ : Set ℂ)) =
      (volume.restrict (Set.Ioi (0:ℝ))).prod (volume : Measure ℂ) := by
    rw [Measure.volume_eq_prod,←Measure.prod_restrict,Measure.restrict_univ]
  have hsource : spatialComplexSplit ⁻¹' (Set.Ioi (0:ℝ) ×ˢ (Set.univ : Set ℂ)) = euclideanUpperHalf := by
    ext p
    simp only [Set.mem_preimage,Set.mem_prod,Set.mem_univ,and_true,Set.mem_Ioi,
      spatialComplexSplit_fst,euclideanUpperHalf,Set.mem_ofPred_eq]
  rw [htarget,hsource] at hm
  have heuc := hm.quasiMeasurePreserving.ae he
  have heuc' : ∀ᵐp ∂volume.restrict euclideanUpperHalf,
      f (euclideanToHyperbolic p)=g (euclideanToHyperbolic p) := by
    simpa only [cuspCoordinateLift,spatialComplexSplit.symm_apply_apply] using heuc
  have hweighted : ∀ᵐp ∂hyperbolicEuclideanVolume,
      f (euclideanToHyperbolic p)=g (euclideanToHyperbolic p) :=
    heuc'.filter_mono (withDensity_absolutelyContinuous
      (volume.restrict euclideanUpperHalf) hyperbolicDensity).ae_le
  change ∀ᵐw ∂Measure.map euclideanToHyperbolic hyperbolicEuclideanVolume,f w=g w
  exact (ae_map_iff euclideanToHyperbolic_measurable.aemeasurable (measurableSet_eq_fun hf hg)).mpr hweighted

lemma hyperbolic_eq_ae_of_period_cells (f g : HyperbolicSpace→ℂ)
    (hf : Measurable f) (hg : Measurable g)
    (hfp : ∀(v : ℝ)(hv : 0<v)(z : ℂ)(n : ActualEisensteinCubic.O),
      f (upperPoint (z+3*ConcreteTraceCRT.eisEmbedding n) v hv)=f (upperPoint z v hv))
    (hgp : ∀(v : ℝ)(hv : 0<v)(z : ℂ)(n : ActualEisensteinCubic.O),
      g (upperPoint (z+3*ConcreteTraceCRT.eisEmbedding n) v hv)=g (upperPoint z v hv))
    (he : ∀(a b : ℝ)(_ha : 0<a),∀ᵐv ∂volume.restrict (Set.Icc a b),
      (fun z => f (cuspCoordinateLift (v,z)))=ᵐ[volume.restrict periodDomain]
        (fun z => g (cuspCoordinateLift (v,z)))) : f=ᵐ[hyperbolicVolume]g := by
  have hplanes (a b : ℝ) (ha : 0<a) : ∀ᵐv ∂volume.restrict (Set.Icc a b),
      ∀ᵐz ∂volume,f (cuspCoordinateLift (v,z))=g (cuspCoordinateLift (v,z)) := by
    filter_upwards [he a b ha,ae_restrict_mem measurableSet_Icc] with v hv hvm
    have hvp : 0<v := ha.trans_le hvm.1
    apply ae_eq_of_periodDomain_eq _ _ _ _ hv
    · intro n z
      simpa only [cuspCoordinateLift_positive v _ hvp] using hfp v hvp z n
    · intro n z
      simpa only [cuspCoordinateLift_positive v _ hvp] using hgp v hvp z n
  have hheights : ∀ᵐv ∂volume.restrict (Set.Ioi (0:ℝ)),
      ∀ᵐz ∂volume,f (cuspCoordinateLift (v,z))=g (cuspCoordinateLift (v,z)) := by
    rw [positive_height_interval_cover,ae_restrict_iUnion_iff]
    intro n
    exact hplanes _ _ (by positivity)
  apply hyperbolic_ae_of_coordinate_ae f g hf hg
  exact (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (hf.comp cuspCoordinateLift_measurable) (hg.comp cuspCoordinateLift_measurable))).mpr hheights

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

theorem cubicEisensteinResidue_continuous_representative :
    (fun w => cubicEisensteinResidue (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] cubicResidualFunction := by
  apply hyperbolic_eq_ae_of_period_cells _ _
    ((MeasureTheory.Lp.stronglyMeasurable cubicEisensteinResidue).measurable.comp
      (measurable_integralOrbitProjection _)) cubicResidualFunction_continuous.measurable
  · intro v hv z n
    exact congrArg cubicEisensteinResidue (kernelProjection_upper_period v hv z n)
  · exact cubicResidualFunction_period
  · exact cubicEisensteinResidue_cell_slices_ae

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise
open Finset AddChar MulChar EisensteinEmbedding

lemma kernelProjection_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (integralOrbitProjection globalKubotaKernel)
      hyperbolicVolume (integralQuotientVolume globalKubotaKernel) := by
  let proj := integralOrbitProjection globalKubotaKernel
  have hp : Measurable proj := measurable_integralOrbitProjection _
  refine ⟨hp,Measure.AbsolutelyContinuous.mk fun S hS hzero => ?_⟩
  rw [Measure.map_apply hp hS]
  have hd : hyperbolicVolume ((proj ⁻¹' S)∩hyperbolicFundamentalSet globalKubotaKernel)=0 := by
    simpa only [integralQuotientVolume,proj,
      Measure.map_apply (measurable_integralOrbitProjection _) hS,
      Measure.restrict_apply ((measurable_integralOrbitProjection _) hS)] using hzero
  have hinv : ∀M : globalKubotaKernel,M • (proj ⁻¹' S)=proj ⁻¹' S := by
    intro M
    ext w
    constructor
    · rintro ⟨u,hu,rfl⟩
      change proj (M • u)∈S
      change proj u∈S at hu
      rwa [show proj (M • u)=proj u from integralOrbitProjection_eq _ M u]
    · intro hw
      refine ⟨M⁻¹ • w,?_,smul_inv_smul M w⟩
      change proj (M⁻¹ • w)∈S
      rwa [show proj (M⁻¹ • w)=proj w from integralOrbitProjection_eq _ M⁻¹ w]
  exact globalKubotaKernel_isFundamentalDomain.measure_zero_of_invariant (proj ⁻¹' S) hinv hd

lemma kernelLevel_character_ae_on_hyperbolic (F : KernelQuotientL2)
    (M : CubicKubota.levelThree)
    (hchar : kernelLevelPullback M F=CubicKubota.complexCharacter M • F) :
    (fun w : HyperbolicSpace => F (integralOrbitProjection globalKubotaKernel
      (complexMatrix M • w))) =ᵐ[hyperbolicVolume]
      (fun w => CubicKubota.complexCharacter M*
        F (integralOrbitProjection globalKubotaKernel w)) := by
  have he : (fun q => F (kernelLevelAction M q))
      =ᵐ[integralQuotientVolume globalKubotaKernel]
        (fun q => CubicKubota.complexCharacter M*F q) := by
    filter_upwards [kernelLevelPullback_ae_eq M F,
      Lp.coeFn_smul (CubicKubota.complexCharacter M) F] with q hq hs
    rw [hchar] at hq
    exact hq.symm.trans hs
  have hl := kernelProjection_quasiMeasurePreserving.ae_eq_comp he
  simpa only [Function.comp_def,kernelLevelAction_mk] using hl

lemma kernelLevel_character_continuous_representative (F : KernelQuotientL2)
    (f : HyperbolicSpace→ℂ) (hf : Continuous f)
    (hrep : (fun w => F (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] f)
    (M : CubicKubota.levelThree)
    (hchar : kernelLevelPullback M F=CubicKubota.complexCharacter M • F)
    (w : HyperbolicSpace) :
    f (complexMatrix M • w)=CubicKubota.complexCharacter M*f w := by
  have hcomp := (measurePreserving_smul (complexMatrix M)
    hyperbolicVolume).quasiMeasurePreserving.ae_eq_comp hrep
  have he : (fun p : HyperbolicSpace => f (complexMatrix M • p))
      =ᵐ[hyperbolicVolume] (fun p => CubicKubota.complexCharacter M*f p) := by
    filter_upwards [hcomp,kernelLevel_character_ae_on_hyperbolic F M hchar,hrep] with p hp hc hr
    exact hp.symm.trans (hc.trans (congrArg (fun z => CubicKubota.complexCharacter M*z) hr))
  have hfun := Measure.eq_of_ae_eq he
    (hf.comp (continuous_hyperbolic_action (complexMatrix M)))
    (continuous_const.mul hf)
  exact congrFun hfun w

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

theorem cubicResidualFunction_automorphy (M : CubicKubota.levelThree) (w : HyperbolicSpace) :
    cubicResidualFunction (complexMatrix M • w)=
      CubicKubota.complexCharacter M*cubicResidualFunction w :=
  kernelLevel_character_continuous_representative cubicEisensteinResidue
    cubicResidualFunction cubicResidualFunction_continuous
    cubicEisensteinResidue_continuous_representative M (cubicEisensteinResidue_character M) w

lemma cubicResidualFunction_ne_zero : cubicResidualFunction≠0 := by
  intro hz
  have he := cubicResidualFunction_fourier_full 1 (by norm_num) 0
  have hconst : (((9*Real.sqrt 3/2:ℝ):ℂ)*
      ((3*(Real.pi:ℂ))*constantArithmeticResidue))≠0 := by
    apply mul_ne_zero
    · exact Complex.ofReal_ne_zero.mpr (by positivity)
    · exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        constantArithmeticResidue_ne_zero
  apply hconst
  simpa only [hz,Pi.zero_apply,zero_mul,integral_zero,
    cubicResidualFullModeAmplitude_zero,Complex.ofReal_one,Complex.one_cpow,mul_one] using he.symm

lemma cubicResidualFunction_exists_ne_zero : ∃w : HyperbolicSpace,cubicResidualFunction w≠0 := by
  by_contra h
  apply cubicResidualFunction_ne_zero
  funext w
  exact not_not.mp (not_exists.mp h w)

open CubicKubota

lemma sourceProjection_continuous (f : HyperbolicSpace→ℂ) (hf : Continuous f) :
    Continuous (sourceProjection f) := by
  unfold sourceProjection
  apply continuous_const.mul
  apply continuous_finsetSum
  intro q hq
  exact hf.comp (continuous_hyperbolic_action _)

lemma sourceProjection_congr_ae (f g : HyperbolicSpace→ℂ)
    (h : f=ᵐ[hyperbolicVolume]g) : sourceProjection f=ᵐ[hyperbolicVolume]sourceProjection g := by
  have htrans (q : levelTwo ⧸ levelThreeInTwo) :
      (fun w => f (integralComplexMatrix (rationalEmbedding (sourceRationalSection q)) • w))
        =ᵐ[hyperbolicVolume]
      (fun w => g (integralComplexMatrix (rationalEmbedding (sourceRationalSection q)) • w)) :=
    (measurePreserving_smul _ hyperbolicVolume).quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [ae_all_iff.mpr htrans] with w hw
  unfold sourceProjection
  congr 1
  exact Finset.sum_congr rfl (fun q _ => hw q)

lemma kernelSourceProjection_hyperbolic_representative (F : KernelQuotientL2)
    (f : HyperbolicSpace→ℂ)
    (hrep : (fun w => F (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] f) :
    (fun w => kernelSourceProjection F (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] sourceProjection f := by
  have he := kernelProjection_quasiMeasurePreserving.ae_eq_comp
    (kernelSourceProjection_ae_eq F)
  change (fun w => kernelSourceProjection F (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume]
      sourceProjection (fun w => F (integralOrbitProjection globalKubotaKernel w)) at he
  exact he.trans (sourceProjection_congr_ae _ _ hrep)

def cubicSourceResidualFunction : HyperbolicSpace→ℂ := sourceProjection cubicResidualFunction

lemma cubicSourceResidualFunction_continuous : Continuous cubicSourceResidualFunction :=
  sourceProjection_continuous cubicResidualFunction cubicResidualFunction_continuous

theorem cubicSourceResidualFunction_automorphy (M : levelTwo) (w : HyperbolicSpace) :
    cubicSourceResidualFunction (integralComplexMatrix (M:SL(2,ActualEisensteinCubic.O)) • w)=
      levelTwoComplexCharacter M*cubicSourceResidualFunction w :=
  sourceProjection_automorphy cubicResidualFunction cubicResidualFunction_automorphy M w

lemma cubicSourceResidualFunction_rational_invariant (M : SL(2,ℤ)) (w : HyperbolicSpace) :
    cubicSourceResidualFunction (integralComplexMatrix (rationalEmbedding M) • w)=
      cubicSourceResidualFunction w := by
  have he := cubicSourceResidualFunction_automorphy (rationalLift M) w
  rw [levelTwoComplexCharacter_rationalLift,one_mul] at he
  exact he

theorem cubicSourceResidualFunction_represents_projection :
    (fun w => kernelSourceProjection cubicEisensteinResidue
      (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] cubicSourceResidualFunction :=
  kernelSourceProjection_hyperbolic_representative cubicEisensteinResidue
    cubicResidualFunction cubicEisensteinResidue_continuous_representative

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def rationalUnipotent (t : ℤ) : SL(2,ℤ) :=
  ⟨!![1,t;0,1],by simp [Matrix.det_fin_two]⟩

lemma rationalUnipotent_add (a b : ℤ) :
    rationalUnipotent (a+b)=rationalUnipotent a*rationalUnipotent b := by
  apply Subtype.ext
  change (!![1,a+b;0,1] : Matrix (Fin 2) (Fin 2) ℤ) =
    (!![1,a;0,1] : Matrix (Fin 2) (Fin 2) ℤ) * !![1,b;0,1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,add_comm]

lemma rationalUnipotent_zero : rationalUnipotent 0=1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [rationalUnipotent]

lemma rationalUnipotent_neg (a : ℤ) : rationalUnipotent (-a)=(rationalUnipotent a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [←rationalUnipotent_add,neg_add_cancel,rationalUnipotent_zero]

lemma rationalUnipotent_one : rationalUnipotent 1=ModularGroup.T := rfl

lemma row_unipotent_conjugate (t : ℤ) (M : levelThree) :
    row (levelThreeConjugate (rationalEmbedding (rationalUnipotent (-t))) M)=
      Matrix.vecMul (row M) (rationalEmbedding (rationalUnipotent t):SL(2,ActualEisensteinCubic.O)) := by
  have hmap (u : ℤ) :
      (rationalEmbedding (rationalUnipotent u) : Matrix (Fin 2) (Fin 2) O) =
        !![1,(u : O);0,1] := by
    apply Matrix.ext
    intro i j
    change (Int.castRingHom O) ((!![1,u;0,1] : Matrix (Fin 2) (Fin 2) ℤ) i j) = _
    fin_cases i <;> fin_cases j <;> simp
  change ((rationalEmbedding (rationalUnipotent (-t)) * (M : SL(2,O)) *
      (rationalEmbedding (rationalUnipotent (-t)))⁻¹ : SL(2,O)) : Matrix (Fin 2) (Fin 2) O) 1 =
    Matrix.vecMul ((M : SL(2,O)) 1)
      (rationalEmbedding (rationalUnipotent t) : Matrix (Fin 2) (Fin 2) O)
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    hmap, Matrix.adjugate_fin_two]
  funext j
  fin_cases j <;> simp [Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

def cuspUnipotentTranslate (t : ℤ) : CuspCosets→CuspCosets :=
  Quotient.map (fun M => levelThreeConjugate (rationalEmbedding (rationalUnipotent (-t))) M) (by
    intro M N h
    change row (levelThreeConjugate _ M)=row (levelThreeConjugate _ N)
    rw [row_unipotent_conjugate,row_unipotent_conjugate,show row M=row N from h])

lemma cuspUnipotentTranslate_inverse (t : ℤ) (x : CuspCosets) :
    cuspUnipotentTranslate (-t) (cuspUnipotentTranslate t x)=x := by
  induction x using Quotient.inductionOn with
  | _ M =>
    change cosetOf (levelThreeConjugate (rationalEmbedding (rationalUnipotent (- -t)))
      (levelThreeConjugate (rationalEmbedding (rationalUnipotent (-t))) M))=cosetOf M
    rw [←levelThreeConjugate_mul,←map_mul,←rationalUnipotent_add]
    simp only [neg_neg,add_neg_cancel,rationalUnipotent_zero,map_one,levelThreeConjugate_one]

def cuspUnipotentEquiv (t : ℤ) : CuspCosets≃CuspCosets where
  toFun := cuspUnipotentTranslate t
  invFun := cuspUnipotentTranslate (-t)
  left_inv := cuspUnipotentTranslate_inverse t
  right_inv x := by simpa only [neg_neg] using cuspUnipotentTranslate_inverse (-t) x

lemma cosetRow_cuspUnipotentEquiv (t : ℤ) (x : CuspCosets) :
    cosetRow (cuspUnipotentEquiv t x)=
      Matrix.vecMul (cosetRow x) (rationalEmbedding (rationalUnipotent t):SL(2,ActualEisensteinCubic.O)) := by
  induction x using Quotient.inductionOn with
  | _ M => exact row_unipotent_conjugate t M

lemma cosetCharacter_cuspUnipotentEquiv (t : ℤ) (x : CuspCosets) :
    cosetCharacter (cuspUnipotentEquiv t x)=cosetCharacter x := by
  induction x using Quotient.inductionOn with
  | _ M => exact complexCharacter_conjugate_rational (rationalUnipotent (-t)) M

lemma embeddedRow_cuspUnipotentEquiv (t : ℤ) (x : CuspCosets) :
    embeddedRow (cuspUnipotentEquiv t x)=
      Matrix.vecMul (embeddedRow x) (integralComplexMatrix (rationalEmbedding (rationalUnipotent t)):SL(2,ℂ)) := by
  funext j
  simp only [embeddedRow,Function.comp_def,cosetRow_cuspUnipotentEquiv,
    Matrix.vecMul,dotProduct,map_sum,map_mul,integralComplexMatrix_apply]

lemma summand_unipotent (t : ℤ) (g : SL(2,ℂ)) (s : ℂ) (x : CuspCosets) :
    summand (integralComplexMatrix (rationalEmbedding (rationalUnipotent t))*g) s x=
      summand g s (cuspUnipotentEquiv t x) := by
  rw [summand,summand,cosetCharacter_cuspUnipotentEquiv,
    embeddedRow_cuspUnipotentEquiv,←rowOperator_apply,rowOperator_mul]

theorem eisenstein_unipotent (t : ℤ) (g : SL(2,ℂ)) (s : ℂ) :
    eisenstein (integralComplexMatrix (rationalEmbedding (rationalUnipotent t))*g) s=eisenstein g s := by
  unfold eisenstein
  simp_rw [summand_unipotent]
  exact (cuspUnipotentEquiv t).tsum_eq _

theorem hyperbolicEisenstein_unipotent (t : ℤ) (s : ℂ) (w : HyperbolicSpace) :
    hyperbolicEisenstein s (integralComplexMatrix (rationalEmbedding (rationalUnipotent t)) • w)=
      hyperbolicEisenstein s w := by
  induction w using Quotient.inductionOn with
  | _ g => exact eisenstein_unipotent t g s

end CubicEisenstein

end

end OAI
end OAIOriginalModule0270

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.ArbitraryCuspPullback
Source SHA256: c6525efbc1321162a539e9b085fc2cb85c857a0e1657da5626af0d71d504ce54
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0271


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
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma ramified_omega_relation : omega^2+omega+1=(0:Eis) := by
  apply eisEmbedding_injective
  simp only [map_add,map_pow,map_one,map_zero,eisEmbedding_omega_actual]
  exact EisensteinEmbedding.omega3_sq

def lowerCuspMatrix (t : Eis) : SL(2,Eis) :=
  ⟨!![1,0;t,1],by simp [Matrix.det_fin_two]⟩

def ramifiedParabolic (t x : Eis) : levelThree := by
  let M : SL(2,Eis) := ⟨!![1-3*t*x,3*x;-3*t^2*x,1+3*t*x],by
    rw [Matrix.det_fin_two]
    change (1-3*t*x)*(1+3*t*x)-(3*x)*(-3*t^2*x)=1
    ring⟩
  refine ⟨M,levelThree_of_entries M ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨-t*x,by change 1-3*t*x-1=3*(-t*x);ring⟩
  · exact ⟨x,by change 3*x-0=3*x;ring⟩
  · exact ⟨-t^2*x,by change -3*t^2*x-0=3*(-t^2*x);ring⟩
  · exact ⟨t*x,by change 1+3*t*x-1=3*(t*x);ring⟩

lemma ramifiedParabolic_mul_lower (t x : Eis) :
    (ramifiedParabolic t x : SL(2,Eis))*lowerCuspMatrix t=
      lowerCuspMatrix t*(upperTranslation x : SL(2,Eis)) := by
  apply Subtype.ext
  change (ramifiedParabolic t x : Matrix (Fin 2) (Fin 2) Eis) *
    (lowerCuspMatrix t : Matrix (Fin 2) (Fin 2) Eis) =
    (lowerCuspMatrix t : Matrix (Fin 2) (Fin 2) Eis) *
      (upperTranslation x : Matrix (Fin 2) (Fin 2) Eis)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [ramifiedParabolic,lowerCuspMatrix,upperTranslation,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

lemma ramifiedParabolic_character (t x : Eis) :
    complexCharacter (ramifiedParabolic t x)=
      eisEmbedding (symbol (-t) (1-3*t*x)) := by
  simp only [complexCharacter,MonoidHom.comp_apply,character,ramifiedParabolic]
  apply congrArg eisEmbedding
  apply symbol_congr
  refine ⟨t,?_⟩
  change (-3*t^2*x)-(-t)=(1-3*t*x)*t
  ring

lemma ramifiedParabolic_omega_value (A B : ℤ) :
    complexCharacter (ramifiedParabolic omega (ActualEisensteinCoordinates.eval A B))=
      eisEmbedding (cubicExp (A+B)) := by
  rw [ramifiedParabolic_character]
  have hd : 1-3*omega*ActualEisensteinCoordinates.eval A B=primaryCoord B (B-A) := by
    rw [primaryCoord_eq]
    change 1-3*omega*((A:Eis)+(B:Eis)*omega)=_
    push_cast
    linear_combination -3*(B:Eis)*ramified_omega_relation
  rw [hd,symbol_neg_numerator _ _ (primaryCoord_primary _ _),
    symbol_omega_eq_linearRay _ (primaryCoord_primary _ _),linearRay_primaryCoord]
  congr 2
  ring

lemma ramifiedParabolic_omega_sq_value (A B : ℤ) :
    complexCharacter (ramifiedParabolic (omega^2) (ActualEisensteinCoordinates.eval A B))=
      eisEmbedding (cubicExp (-(A+B))) := by
  rw [ramifiedParabolic_character]
  have hd : 1-3*omega^2*ActualEisensteinCoordinates.eval A B=primaryCoord (A-B) A := by
    rw [primaryCoord_eq]
    change 1-3*omega^2*((A:Eis)+(B:Eis)*omega)=_
    push_cast
    linear_combination -3*((A:Eis)+(B:Eis)*omega-(B:Eis))*ramified_omega_relation
  rw [hd,symbol_neg_numerator _ _ (primaryCoord_primary _ _),
    symbol_pow_numerator _ _ (primaryCoord_primary _ _) 2,
    symbol_omega_eq_linearRay _ (primaryCoord_primary _ _),linearRay_primaryCoord]
  have he : cubicExp (2*((A-B)*2+(-1)*A))=cubicExp (-(A+B)) := by
    apply cubicExp_eq_of_dvd_sub
    exact ⟨A-B,by ring⟩
  have hs : cubicExp ((A-B)*2+(-1)*A)^2=cubicExp (2*((A-B)*2+(-1)*A)) := by
    rw [pow_two,←cubicExp_add]
    congr 1
    ring
  convert congrArg eisEmbedding (hs.trans he) using 1 ; congr 2 ; ring_nf

def ramifiedSourceFunction (t : Eis) (w : HyperbolicSpace) : ℂ :=
  cubicSourceResidualFunction (integralComplexMatrix (lowerCuspMatrix t) • w)

lemma ramifiedSourceFunction_continuous (t : Eis) : Continuous (ramifiedSourceFunction t) :=
  cubicSourceResidualFunction_continuous.comp (continuous_const_smul _)

lemma ramifiedSourceFunction_translate (t x : Eis) (w : HyperbolicSpace) :
    ramifiedSourceFunction t (complexMatrix (upperTranslation x) • w)=
      eisEmbedding (symbol (-t) (1-3*t*x))*ramifiedSourceFunction t w := by
  have he := cubicSourceResidualFunction_automorphy
    (sourceLevelInclusion (ramifiedParabolic t x))
    (integralComplexMatrix (lowerCuspMatrix t) • w)
  rw [sourceLevelInclusion_character,ramifiedParabolic_character] at he
  change cubicSourceResidualFunction
    (integralComplexMatrix (ramifiedParabolic t x : SL(2,Eis)) •
      (integralComplexMatrix (lowerCuspMatrix t) • w))=_ at he
  rw [←mul_smul,←map_mul,ramifiedParabolic_mul_lower,map_mul,mul_smul] at he
  exact he

lemma ramifiedSourceFunction_omega_translate (A B : ℤ) (w : HyperbolicSpace) :
    ramifiedSourceFunction omega
      (complexMatrix (upperTranslation (ActualEisensteinCoordinates.eval A B)) • w)=
      eisEmbedding (cubicExp (A+B))*ramifiedSourceFunction omega w := by
  rw [ramifiedSourceFunction_translate]
  rw [←ramifiedParabolic_character,ramifiedParabolic_omega_value]

lemma ramifiedSourceFunction_omega_sq_translate (A B : ℤ) (w : HyperbolicSpace) :
    ramifiedSourceFunction (omega^2)
      (complexMatrix (upperTranslation (ActualEisensteinCoordinates.eval A B)) • w)=
      eisEmbedding (cubicExp (-(A+B)))*ramifiedSourceFunction (omega^2) w := by
  rw [ramifiedSourceFunction_translate]
  rw [←ramifiedParabolic_character,ramifiedParabolic_omega_sq_value]

end

section
open MeasureTheory Filter
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CubicRamified
open EisensteinEmbedding (omega3)
local notation "Eis" => ActualEisensteinCubic.O

lemma embedding_cubicExp (n : ℤ) :
    eisEmbedding (cubicExp n)=Complex.exp (2*Real.pi*Complex.I*(n:ℂ)/3) := by
  have hw : omega3=Complex.exp (2*Real.pi*Complex.I/3) := by
    rw [←TraceLambdaPhase.exp_minus_four_pi_div_three]
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    exact ⟨-1,by push_cast;ring⟩
  rw [cubicExp,map_pow,eisEmbedding_omega_actual,hw,←Complex.exp_nat_mul]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨-(n/3),?_⟩
  have hn : (n%3).toNat=(n%3) := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have hnc : ((n%3).toNat:ℂ)=((n%3:ℤ):ℂ) := by exact_mod_cast hn
  have he : ((n%3:ℤ):ℂ)=(n:ℂ)-3*((n/3:ℤ):ℂ) := by
    have he0 : n%3=n-3*(n/3) := by omega
    exact_mod_cast he0
  rw [hnc,he]
  push_cast
  ring

def ramifiedShift10 : ℂ := eisEmbedding (omega-1)/(9*eisLam)

def ramifiedShift19 : ℂ := eisEmbedding (-2-omega)/(9*eisLam)

lemma ramifiedShift10_explicit : ramifiedShift10=-(omega3^2)/9 := by
  unfold ramifiedShift10
  apply (div_eq_iff (mul_ne_zero (by norm_num : (9:ℂ)≠0) eisLam_ne_zero)).mpr
  rw [map_sub,eisEmbedding_omega_actual,map_one]
  change omega3-1=-(omega3^2)/9*(9*(1+2*omega3))
  linear_combination (2*omega3-1)*EisensteinEmbedding.omega3_sq

lemma ramifiedShift19_explicit : ramifiedShift19=omega3/9 := by
  unfold ramifiedShift19
  apply (div_eq_iff (mul_ne_zero (by norm_num : (9:ℂ)≠0) eisLam_ne_zero)).mpr
  rw [map_sub,map_neg,map_ofNat,eisEmbedding_omega_actual]
  change -2-omega3=omega3/9*(9*(1+2*omega3))
  linear_combination -2*EisensteinEmbedding.omega3_sq

lemma ramifiedShift10_period (A B : ℤ) :
    ShortDraftTrace.breveE (ramifiedShift10*(3*eisEmbedding (ActualEisensteinCoordinates.eval A B)))=
      eisEmbedding (cubicExp (A+B)) := by
  have he : ramifiedShift10*(3*eisEmbedding (ActualEisensteinCoordinates.eval A B))=
      eisEmbedding ((omega-1)*ActualEisensteinCoordinates.eval A B)/eisLam/3 := by
    rw [ramifiedShift10,map_mul]
    ring
  have ht := breveE_real_trace_of_O (3:ℝ) ((omega-1)*ActualEisensteinCoordinates.eval A B)
  norm_num only [Complex.ofReal_ofNat] at ht
  rw [he,ht]
  have hcoords : (ActualEisensteinCoordinates.coords
      ((omega-1)*ActualEisensteinCoordinates.eval A B)).2=A-2*B := by
    have hw : omega-1=ActualEisensteinCoordinates.eval (-1) 1 := by
      simp only [ActualEisensteinCoordinates.eval,Int.cast_neg,Int.cast_one,one_mul]
      change omega-1=-1+omega
      ring
    rw [hw,ActualEisensteinCoordinates.eval_mul,ShortDraftLatticeCount.coords_eval]
    ring
  rw [hcoords,←embedding_cubicExp]
  exact congrArg eisEmbedding (cubicExp_eq_of_dvd_sub ⟨-B,by ring⟩)

lemma ramifiedShift19_period (A B : ℤ) :
    ShortDraftTrace.breveE (ramifiedShift19*(3*eisEmbedding (ActualEisensteinCoordinates.eval A B)))=
      eisEmbedding (cubicExp (-(A+B))) := by
  have he : ramifiedShift19*(3*eisEmbedding (ActualEisensteinCoordinates.eval A B))=
      eisEmbedding ((-2-omega)*ActualEisensteinCoordinates.eval A B)/eisLam/3 := by
    rw [ramifiedShift19,map_mul]
    ring
  have ht := breveE_real_trace_of_O (3:ℝ) ((-2-omega)*ActualEisensteinCoordinates.eval A B)
  norm_num only [Complex.ofReal_ofNat] at ht
  rw [he,ht]
  have hcoords : (ActualEisensteinCoordinates.coords
      ((-2-omega)*ActualEisensteinCoordinates.eval A B)).2=-(A+B) := by
    have hw : -2-omega=ActualEisensteinCoordinates.eval (-2) (-1) := by
      simp only [ActualEisensteinCoordinates.eval,Int.cast_neg,Int.cast_one,Int.cast_ofNat,neg_mul,one_mul]
      change -2-omega=-2+-omega
      ring
    rw [hw,ActualEisensteinCoordinates.eval_mul,ShortDraftLatticeCount.coords_eval]
    ring
  rw [hcoords,embedding_cubicExp]

lemma ramifiedSourceFunction_upper_shift10 (x : Eis) (z : ℂ) (v : ℝ) (hv : 0<v) :
    ramifiedSourceFunction omega (upperPoint (z+3*eisEmbedding x) v hv)=
      ShortDraftTrace.breveE (ramifiedShift10*(3*eisEmbedding x))*
        ramifiedSourceFunction omega (upperPoint z v hv) := by
  let A := (ActualEisensteinCoordinates.coords x).1
  let B := (ActualEisensteinCoordinates.coords x).2
  have hx : x=ActualEisensteinCoordinates.eval A B := (ActualEisensteinCoordinates.eval_coords x).symm
  rw [hx,ramifiedShift10_period]
  have he : upperPoint (z+3*eisEmbedding (ActualEisensteinCoordinates.eval A B)) v hv=
      complexMatrix (upperTranslation (ActualEisensteinCoordinates.eval A B)) • upperPoint z v hv :=
    congrArg (fun g : SL(2,ℂ)=>(g:HyperbolicSpace))
      (upperTranslation_section (ActualEisensteinCoordinates.eval A B) z v hv).symm
  rw [he,ramifiedSourceFunction_omega_translate]

lemma ramifiedSourceFunction_upper_shift19 (x : Eis) (z : ℂ) (v : ℝ) (hv : 0<v) :
    ramifiedSourceFunction (omega^2) (upperPoint (z+3*eisEmbedding x) v hv)=
      ShortDraftTrace.breveE (ramifiedShift19*(3*eisEmbedding x))*
        ramifiedSourceFunction (omega^2) (upperPoint z v hv) := by
  let A := (ActualEisensteinCoordinates.coords x).1
  let B := (ActualEisensteinCoordinates.coords x).2
  have hx : x=ActualEisensteinCoordinates.eval A B := (ActualEisensteinCoordinates.eval_coords x).symm
  rw [hx,ramifiedShift19_period]
  have he : upperPoint (z+3*eisEmbedding (ActualEisensteinCoordinates.eval A B)) v hv=
      complexMatrix (upperTranslation (ActualEisensteinCoordinates.eval A B)) • upperPoint z v hv :=
    congrArg (fun g : SL(2,ℂ)=>(g:HyperbolicSpace))
      (upperTranslation_section (ActualEisensteinCoordinates.eval A B) z v hv).symm
  rw [he,ramifiedSourceFunction_omega_sq_translate]

lemma trace_dephase_periodic (f : ℂ→ℂ) (shift : ℂ)
    (hf : ∀ x : Eis,∀z, f (z+3*eisEmbedding x)=
      ShortDraftTrace.breveE (shift*(3*eisEmbedding x))*f z) :
    ∀x:Eis,∀z,(f (z+3*eisEmbedding x)*ShortDraftTrace.breveE (-shift*(z+3*eisEmbedding x)))=
      f z*ShortDraftTrace.breveE (-shift*z) := by
  intro x z
  rw [hf,mul_add,AddChar.map_add_eq_mul]
  have hn : -shift*(3*eisEmbedding x)=-(shift*(3*eisEmbedding x)) := by ring
  rw [hn,AddChar.map_neg_eq_inv]
  have hne : ShortDraftTrace.breveE (shift*(3*eisEmbedding x))≠0 :=
    Complex.exp_ne_zero _
  calc
    _ = (ShortDraftTrace.breveE (shift*(3*eisEmbedding x))*
      (ShortDraftTrace.breveE (shift*(3*eisEmbedding x)))⁻¹)*
        (f z*ShortDraftTrace.breveE (-shift*z)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hne,one_mul]

lemma ramifiedSourceFunction_dephase10_periodic (v : ℝ) (hv : 0<v) :
    ∀x:Eis,∀z,ramifiedSourceFunction omega (upperPoint (z+3*eisEmbedding x) v hv)*
      ShortDraftTrace.breveE (-ramifiedShift10*(z+3*eisEmbedding x))=
    ramifiedSourceFunction omega (upperPoint z v hv)*ShortDraftTrace.breveE (-ramifiedShift10*z) :=
  trace_dephase_periodic (fun z => ramifiedSourceFunction omega (upperPoint z v hv))
    ramifiedShift10 (fun x z=>ramifiedSourceFunction_upper_shift10 x z v hv)

lemma ramifiedSourceFunction_dephase19_periodic (v : ℝ) (hv : 0<v) :
    ∀x:Eis,∀z,ramifiedSourceFunction (omega^2) (upperPoint (z+3*eisEmbedding x) v hv)*
      ShortDraftTrace.breveE (-ramifiedShift19*(z+3*eisEmbedding x))=
    ramifiedSourceFunction (omega^2) (upperPoint z v hv)*ShortDraftTrace.breveE (-ramifiedShift19*z) :=
  trace_dephase_periodic (fun z => ramifiedSourceFunction (omega^2) (upperPoint z v hv))
    ramifiedShift19 (fun x z=>ramifiedSourceFunction_upper_shift19 x z v hv)

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups ENNReal

def arbitraryCuspCompact (M : SL(2,ℂ)) (a b : ℝ) : Set HyperbolicSpace :=
  (M • ·) '' cuspHeightCompact a b

lemma arbitraryCuspCompact_isCompact (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a) :
    IsCompact (arbitraryCuspCompact M a b) :=
  (cuspHeightCompact_isCompact a b ha).image (continuous_const_smul M)

lemma arbitraryCusp_image_restrict_le (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a) :
    hyperbolicVolume.restrict ((M • ·) '' cuspPeriodStrip a b)≤
      (1:ℝ≥0∞) • hyperbolicVolume.restrict (arbitraryCuspCompact M a b) := by
  simpa only [one_smul,arbitraryCuspCompact] using Measure.restrict_mono_set hyperbolicVolume
    (Set.image_mono (cuspPeriodStrip_subset_heightCompact a b ha))

lemma arbitraryCusp_smul_measurePreserving (M : SL(2,ℂ)) (a b : ℝ) :
    MeasurePreserving (M • ·) (hyperbolicVolume.restrict (cuspPeriodStrip a b))
      (hyperbolicVolume.restrict ((M • ·) '' cuspPeriodStrip a b)) :=
  (measurePreserving_smul M hyperbolicVolume).restrict_image_emb
    (measurableEmbedding_const_smul M) _

def arbitraryCuspPullback (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a) :
    KernelQuotientL2→L[ℂ]CuspHeightStripL2 a b :=
  (Lp.compMeasurePreservingₗᵢ ℂ (M • ·) (arbitraryCusp_smul_measurePreserving M a b)).toContinuousLinearMap.comp
    ((dominatedComplexL2 (by simp : (1:ℝ≥0∞)≠⊤)
      (arbitraryCusp_image_restrict_le M a b ha)).comp
      (kernelCompactPullbackCLM (arbitraryCuspCompact M a b)
        (arbitraryCuspCompact_isCompact M a b ha)))

lemma arbitraryCuspPullback_ae (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (F : KernelQuotientL2) :
    arbitraryCuspPullback M a b ha F=ᵐ[hyperbolicVolume.restrict (cuspPeriodStrip a b)]
      fun w => F (integralOrbitProjection globalKubotaKernel (M • w)) := by
  have h1 := dominatedComplexL2_ae (by simp : (1:ℝ≥0∞)≠⊤)
    (arbitraryCusp_image_restrict_le M a b ha)
    (kernelCompactPullbackCLM (arbitraryCuspCompact M a b)
      (arbitraryCuspCompact_isCompact M a b ha) F)
  have h2 := (Measure.absolutelyContinuous_of_le_smul
    (arbitraryCusp_image_restrict_le M a b ha)).ae_eq
      (kernelCompactPullbackCLM_ae (arbitraryCuspCompact M a b)
        (arbitraryCuspCompact_isCompact M a b ha) F)
  exact (Lp.coeFn_compMeasurePreserving _ (arbitraryCusp_smul_measurePreserving M a b)).trans
    ((arbitraryCusp_smul_measurePreserving M a b).quasiMeasurePreserving.ae_eq_comp (h1.trans h2))

lemma arbitraryCusp_quasiMeasurePreserving (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a) :
    Measure.QuasiMeasurePreserving
      (fun w => integralOrbitProjection globalKubotaKernel (M • w))
      (hyperbolicVolume.restrict (cuspPeriodStrip a b))
      (integralQuotientVolume globalKubotaKernel) := by
  have hcompact : Measure.QuasiMeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (arbitraryCuspCompact M a b))
      (integralQuotientVolume globalKubotaKernel) :=
    ⟨measurable_integralOrbitProjection _,Measure.absolutelyContinuous_of_le_smul
      (kernelCompactMultiplicity_spec _ (arbitraryCuspCompact_isCompact M a b ha))⟩
  have himage : Measure.QuasiMeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict ((M • ·) '' cuspPeriodStrip a b))
      (integralQuotientVolume globalKubotaKernel) :=
    ⟨hcompact.measurable,((Measure.absolutelyContinuous_of_le_smul
      (arbitraryCusp_image_restrict_le M a b ha)).map
        (measurable_integralOrbitProjection _)).trans hcompact.absolutelyContinuous⟩
  exact himage.comp (arbitraryCusp_smul_measurePreserving M a b).quasiMeasurePreserving

def arbitraryCuspQuotientCompact (M : SL(2,ℂ)) (a b : ℝ) : Set KernelQuotient :=
  integralOrbitProjection globalKubotaKernel '' arbitraryCuspCompact M a b

lemma arbitraryCuspQuotientCompact_isCompact (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a) :
    IsCompact (arbitraryCuspQuotientCompact M a b) :=
  (arbitraryCuspCompact_isCompact M a b ha).image (continuous_integralOrbitProjection _)

lemma arbitraryCusp_mem_compact (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (w : HyperbolicSpace) (hw : w∈cuspPeriodStrip a b) :
    integralOrbitProjection globalKubotaKernel (M • w)∈arbitraryCuspQuotientCompact M a b :=
  ⟨M • w,⟨w,cuspPeriodStrip_subset_heightCompact a b ha hw,rfl⟩,rfl⟩

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace ENNReal

def arbitraryCuspWeightedPhase (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ)
    (w : HyperbolicSpace) : ℂ :=
  ρ (hyperbolicHeight w)*ShortDraftTrace.breveE (-freq*hyperbolicHorizontal w)

lemma arbitraryCuspWeightedPhase_continuous (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) :
    Continuous (arbitraryCuspWeightedPhase ρ freq) := by
  unfold arbitraryCuspWeightedPhase
  apply (ρ.continuous.comp hyperbolicHeight_continuous).mul
  change Continuous (fun w : HyperbolicSpace =>
    Complex.exp (2*Real.pi*Complex.I*((-freq*hyperbolicHorizontal w)+
      starRingEnd ℂ (-freq*hyperbolicHorizontal w))))
  have hh := hyperbolicHorizontal_continuous
  fun_prop

lemma arbitraryCuspWeightedPhase_bound (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ)
    (w : HyperbolicSpace) : ‖arbitraryCuspWeightedPhase ρ freq w‖≤‖ρ‖ := by
  rw [arbitraryCuspWeightedPhase,norm_mul,breveE_norm,mul_one]
  exact ρ.norm_coe_le_norm _

lemma arbitraryCuspFourierTest_memLp (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) :
    MemLp (fun w => star (arbitraryCuspWeightedPhase ρ freq w)) 2
      (hyperbolicVolume.restrict (cuspPeriodStrip a b)) := by
  let := cuspPeriodStripFiniteVolume a b ha
  apply MemLp.of_bound (arbitraryCuspWeightedPhase_continuous ρ freq).star.aestronglyMeasurable ‖ρ‖
  exact Eventually.of_forall (fun w => by rw [norm_star];exact arbitraryCuspWeightedPhase_bound ρ freq w)

def arbitraryCuspFourierTestL2 (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) : CuspHeightStripL2 a b :=
  (arbitraryCuspFourierTest_memLp a b ha ρ freq).toLp
    (fun w => star (arbitraryCuspWeightedPhase ρ freq w))

def arbitraryCuspHeightFourier (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) : KernelQuotientL2→L[ℂ]ℂ :=
  (innerSL ℂ (arbitraryCuspFourierTestL2 a b ha ρ freq)).comp
    (arbitraryCuspPullback M a b ha)

lemma arbitraryCuspHeightFourier_integral (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) (F : KernelQuotientL2) :
    arbitraryCuspHeightFourier M a b ha ρ freq F=
      ∫w in cuspPeriodStrip a b,
        F (integralOrbitProjection globalKubotaKernel (M • w))*
          arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume := by
  change inner ℂ (arbitraryCuspFourierTestL2 a b ha ρ freq) (arbitraryCuspPullback M a b ha F)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (arbitraryCuspFourierTest_memLp a b ha ρ freq),
    arbitraryCuspPullback_ae M a b ha F] with w hw hp
  rw [RCLike.inner_apply,arbitraryCuspFourierTestL2,hw,hp]
  simp only [starRingEnd_apply,star_star]

lemma arbitraryCuspHeightFourier_restrict (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) (F : KernelQuotientL2) :
    arbitraryCuspHeightFourier M a b ha ρ freq
      (kernelMassRestrictionCLM (arbitraryCuspQuotientCompact M a b)
        (arbitraryCuspQuotientCompact_isCompact M a b ha).measurableSet F)=
      arbitraryCuspHeightFourier M a b ha ρ freq F := by
  rw [arbitraryCuspHeightFourier_integral,arbitraryCuspHeightFourier_integral]
  have he := (arbitraryCusp_quasiMeasurePreserving M a b ha).ae_eq_comp
    (kernelMassRestriction_coe (arbitraryCuspQuotientCompact M a b)
      (arbitraryCuspQuotientCompact_isCompact M a b ha).measurableSet F)
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwm
  exact congrArg (fun z : ℂ => z*arbitraryCuspWeightedPhase ρ freq w)
    (hw.trans (Set.indicator_of_mem (arbitraryCusp_mem_compact M a b ha w hwm) _))

def arbitraryCuspHeightFamily (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) (s : ℂ) : ℂ :=
  arbitraryCuspHeightFourier M a b ha ρ freq
    (kernelLocalCorrectedSeed (arbitraryCuspQuotientCompact M a b)
      (arbitraryCuspQuotientCompact_isCompact M a b ha) 2 3 (by norm_num) (by norm_num) s)

lemma arbitraryCuspHeightFamily_analyticAt (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (arbitraryCuspHeightFamily M a b ha ρ freq) s :=
  (ContinuousLinearMap.analyticAt (𝕜:=ℂ) (E:=KernelQuotientL2) (F:=ℂ)
    (arbitraryCuspHeightFourier M a b ha ρ freq) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal _
        (arbitraryCuspQuotientCompact_isCompact M a b ha)
        2 3 (by norm_num) (by norm_num) s hs hi) rfl

lemma arbitraryCuspHeightFamily_residue_limit (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) :
    Tendsto (fun s : ℂ => (s-4/3)*arbitraryCuspHeightFamily M a b ha ρ freq s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (arbitraryCuspHeightFourier M a b ha ρ freq cubicEisensteinResidue)) := by
  have hh := (arbitraryCuspHeightFourier M a b ha ρ freq).continuous.continuousAt.tendsto.comp
    (cubicEisensteinResidue_local_limit _ (arbitraryCuspQuotientCompact_isCompact M a b ha))
  simpa only [Function.comp_def,map_smul,smul_eq_mul,arbitraryCuspHeightFourier_restrict,
    arbitraryCuspHeightFamily] using hh

lemma arbitraryCuspHeightFamily_initial (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    arbitraryCuspHeightFamily M a b ha ρ freq s=
      ∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (M • w)*
        arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume := by
  rw [arbitraryCuspHeightFamily,arbitraryCuspHeightFourier_integral]
  have he := (arbitraryCusp_quasiMeasurePreserving M a b ha).ae_eq_comp
    (cubicEisensteinLocalFamily_initial_ae (arbitraryCuspQuotientCompact M a b)
      (arbitraryCuspQuotientCompact_isCompact M a b ha) s hs hi)
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwm
  dsimp only [Function.comp_def] at hw
  rw [hw,Set.indicator_of_mem (arbitraryCusp_mem_compact M a b ha w hwm),kernelQuotientEisenstein_mk]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

private lemma inner_projection_sandwich {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : E →L[ℂ] G) (K : Submodule ℂ E) [K.HasOrthogonalProjection] (x y : G) :
    inner ℂ x (A (K.starProjection (A.adjoint y))) =
      inner ℂ (A (K.starProjection (A.adjoint x))) y := by
  rw [← A.adjoint_inner_left, ← A.adjoint_inner_right]
  exact (K.inner_starProjection_left_eq_right _ _).symm

lemma kernelThetaMassProjection_symmetric (F D : KernelQuotientL2) :
    inner ℂ F (kernelThetaMassProjection D)=inner ℂ (kernelThetaMassProjection F) D :=
  inner_projection_sandwich kernelEnergyMass kernelThetaNull F D

lemma kernelThetaMassProjection_eigenvector (F : KernelQuotientL2)
    (hF : (F,(8/9:ℂ) • F)∈kernelEnergyLaplacian.graph) :
    kernelThetaMassProjection F=(9/17:ℂ) • F := by
  let u : kernelEnergyLaplacian.domain := ⟨F,LinearPMap.mem_domain_of_mem_graph hF⟩
  have hu : kernelEnergyLaplacian u=(8/9:ℂ) • F :=
    kernelEnergyLaplacian.mem_graph_snd_inj (kernelEnergyLaplacian.mem_graph u) hF rfl
  let E : KernelEnergyGraph := kernelVariationalSolution (kernelEnergyLaplacian u+u)
  have hE : E∈kernelThetaNull := by
    change kernelSpectralFormOperator (8/9:ℂ) E=0
    dsimp only [E]
    rw [kernelSpectralFormOperator_of_domain,hu]
    change kernelVariationalSolution ((8/9:ℂ) • F-(8/9:ℂ) • F)=0
    rw [sub_self,map_zero]
  have hmass : kernelEnergyMass E=F := kernelEnergyLaplacian_resolvent_relation u
  have hscale : kernelEnergyMass.adjoint F=(9/17:ℂ) • E := by
    dsimp [E]
    rw [hu]
    change kernelVariationalSolution F=(9/17:ℂ) • kernelVariationalSolution ((8/9:ℂ) • F+F)
    rw [map_add,map_smul,smul_add,smul_smul]
    module
  change kernelEnergyMass (kernelThetaNull.starProjection (kernelEnergyMass.adjoint F))=_
  rw [hscale,map_smul,kernelThetaNull.starProjection_eq_self_iff.mpr hE,map_smul,hmass]

theorem kernelEisensteinResidueVector_pairing (a b : ℝ) (ha : 0<a) (hab : a<b)
    (F : KernelQuotientL2) (hF : (F,(8/9:ℂ) • F)∈kernelEnergyLaplacian.graph) :
    inner ℂ F (kernelEisensteinResidueVector a b ha hab)=
      (3/2:ℂ)*inner ℂ F (kernelL2Defect a b ha hab (4/3)) := by
  rw [kernelEisensteinResidueVector,inner_smul_right,kernelThetaMassProjection_symmetric,
    kernelThetaMassProjection_eigenvector F hF,inner_smul_left]
  simp only [map_div₀,map_ofNat]
  ring

theorem kernelEisensteinResidueVector_orthogonal_of_defect (a b : ℝ) (ha : 0<a) (hab : a<b)
    (F : KernelQuotientL2) (hF : (F,(8/9:ℂ) • F)∈kernelEnergyLaplacian.graph)
    (hzero : inner ℂ F (kernelL2Defect a b ha hab (4/3))=0) :
    inner ℂ F (kernelEisensteinResidueVector a b ha hab)=0 := by
  rw [kernelEisensteinResidueVector_pairing a b ha hab F hF,hzero,mul_zero]

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

lemma kernelLocalCorrectedSeed_initial_eq
    (S : Set KernelQuotient) (hS : IsCompact S)
    (a b c d : ℝ) (ha : 1<a) (hab : a<b) (hc : 1<c) (hcd : c<d)
    (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelLocalCorrectedSeed S hS a b (by linarith) hab s=
      kernelLocalCorrectedSeed S hS c d (by linarith) hcd s := by
  have h1 := kernelLocalCorrectedSeed_ae_eq S hS a b (by linarith) hab s
  have h2 := kernelLocalCorrectedSeed_ae_eq S hS c d (by linarith) hcd s
  have h3 := kernelEisensteinL2Correction_initial_overlap a b ha hab s hs hi
  have h4 := kernelEisensteinL2Correction_initial_overlap c d hc hcd s hs hi
  apply Lp.ext
  filter_upwards [h1,h2,h3,h4] with q hq1 hq2 hq3 hq4
  rw [hq1,hq2]
  by_cases hq : q∈S
  · simp only [Set.indicator_of_mem hq,kernelCorrectedSeed,hq3,hq4]
    ring
  · simp only [Set.indicator_of_notMem hq]

lemma kernelLocalCorrectedSeed_cutoff_eq
    (S : Set KernelQuotient) (hS : IsCompact S)
    (a b c d : ℝ) (ha : 1<a) (hab : a<b) (hc : 1<c) (hcd : c<d) :
    ∀s∈cuspUpperParameterRegion,
      kernelLocalCorrectedSeed S hS a b (by linarith) hab s=
        kernelLocalCorrectedSeed S hS c d (by linarith) hcd s := by
  have h1 : AnalyticOnNhd ℂ
      (kernelLocalCorrectedSeed S hS a b (by linarith) hab) cuspUpperParameterRegion := by
    intro s hs
    exact kernelLocalCorrectedSeed_analyticAt_nonreal S hS a b (by linarith) hab s
      (by linarith [hs.1]) hs.2.ne'
  have h2 : AnalyticOnNhd ℂ
      (kernelLocalCorrectedSeed S hS c d (by linarith) hcd) cuspUpperParameterRegion := by
    intro s hs
    exact kernelLocalCorrectedSeed_analyticAt_nonreal S hS c d (by linarith) hcd s
      (by linarith [hs.1]) hs.2.ne'
  have hV : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have he : (kernelLocalCorrectedSeed S hS a b (by linarith) hab)
      =ᶠ[𝓝 (5+Complex.I:ℂ)] (kernelLocalCorrectedSeed S hS c d (by linarith) hcd) := by
    filter_upwards [hV.mem_nhds (by norm_num)] with s hs
    exact kernelLocalCorrectedSeed_initial_eq S hS a b c d ha hab hc hcd s hs.1 hs.2
  exact h1.eqOn_of_preconnected_of_eventuallyEq h2 cuspUpperParameterRegion_convex.isPreconnected
    (by norm_num [cuspUpperParameterRegion]) he

lemma kernelEisensteinResidueVector_restrict_cutoff_eq
    (S : Set KernelQuotient) (hS : IsCompact S)
    (a b c d : ℝ) (ha : 1<a) (hab : a<b) (hc : 1<c) (hcd : c<d) :
    kernelMassRestrictionCLM S hS.measurableSet
        (kernelEisensteinResidueVector a b (by linarith) hab)=
      kernelMassRestrictionCLM S hS.measurableSet
        (kernelEisensteinResidueVector c d (by linarith) hcd) := by
  have h1 := (kernelLocalCorrectedSeed_residue_limit S hS a b (by linarith) hab).comp
    thetaApproach_tendsto_complex_punctured
  have h2 := (kernelLocalCorrectedSeed_residue_limit S hS c d (by linarith) hcd).comp
    thetaApproach_tendsto_complex_punctured
  have he : (fun t : ℝ =>
      ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I-4/3) •
        kernelLocalCorrectedSeed S hS a b (by linarith) hab
          ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I))
      =ᶠ[𝓝[>] (0:ℝ)] (fun t : ℝ =>
      ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I-4/3) •
        kernelLocalCorrectedSeed S hS c d (by linarith) hcd
          ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    rw [kernelLocalCorrectedSeed_cutoff_eq S hS a b c d ha hab hc hcd _
      (by constructor <;> simp [] <;> linarith)]
  exact tendsto_nhds_unique h1 (h2.congr' he.symm)

lemma kernelL2_eq_of_compact_restrictions (F G : KernelQuotientL2)
    (h : ∀S : Set KernelQuotient, ∀hS : IsCompact S,
      kernelMassRestrictionCLM S hS.measurableSet F=
        kernelMassRestrictionCLM S hS.measurableSet G) : F=G := by
  let S : ℕ→Set KernelQuotient := fun n => {q | kernelQuotientBarrier 2 3 q≤n}
  have hS (n : ℕ) : IsCompact (S n) := kernelBarrier_sublevel_isCompact n
  have he (n : ℕ) : ∀ᵐq∂integralQuotientVolume globalKubotaKernel, q∈S n → F q=G q := by
    have hi := h (S n) (hS n)
    have hf := kernelMassRestriction_coe (S n) (hS n).measurableSet F
    have hg := kernelMassRestriction_coe (S n) (hS n).measurableSet G
    filter_upwards [hf,hg] with q hf hg hq
    rw [Set.indicator_of_mem hq] at hf hg
    change kernelMassRestrictionCLM (S n) (hS n).measurableSet F q=F q at hf
    change kernelMassRestrictionCLM (S n) (hS n).measurableSet G q=G q at hg
    rw [hi] at hf
    exact hf.symm.trans hg
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr he] with q hq
  obtain ⟨n,hn⟩ := exists_nat_ge (kernelQuotientBarrier 2 3 q)
  exact hq n hn

theorem kernelEisensteinResidueVector_cutoff_independent
    (a b c d : ℝ) (ha : 1<a) (hab : a<b) (hc : 1<c) (hcd : c<d) :
    kernelEisensteinResidueVector a b (by linarith) hab=
      kernelEisensteinResidueVector c d (by linarith) hcd := by
  apply kernelL2_eq_of_compact_restrictions
  intro S hS
  exact kernelEisensteinResidueVector_restrict_cutoff_eq S hS a b c d ha hab hc hcd

end CubicEisenstein

end

end OAI
end OAIOriginalModule0271

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.CuspDilation
Source SHA256: d5e0ea6d1486278f3d2d75e7c50ba55977543ae117af5197a1b79455f8dc392e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0272


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

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedTraceLambda : Eis := 1+2*omega

lemma ramifiedEmbedding_traceLambda : eisEmbedding ramifiedTraceLambda=eisLam := by
  change eisEmbedding (1+2*omega)=1+2*EisensteinEmbedding.omega3
  rw [map_add,map_one,map_mul,map_ofNat,eisEmbedding_omega_actual]

lemma breveE_embedding_third_eval (A B : ℤ) :
    ShortDraftTrace.breveE (eisEmbedding (ActualEisensteinCoordinates.eval A B)/3)=
      eisEmbedding (cubicExp (2*A-B)) := by
  have htrace : ramifiedTraceLambda=ActualEisensteinCoordinates.eval 1 2 := by
    change 1+2*omega=(1:Eis)+(2:Eis)*omega
    rfl
  have h := breveE_real_trace_of_O (3:ℝ)
    (ActualEisensteinCoordinates.eval A B*ramifiedTraceLambda)
  rw [map_mul,ramifiedEmbedding_traceLambda,mul_div_cancel_right₀ _ eisLam_ne_zero] at h
  rw [htrace,ActualEisensteinCoordinates.eval_mul,ShortDraftLatticeCount.coords_eval] at h
  norm_num only [Complex.ofReal_ofNat] at h
  rw [h,embedding_cubicExp]
  congr 3
  ring_nf

lemma primary_add_three (a r : Eis) (ha : lambda^2∣a-1) :
    lambda^2∣a+3*r-1 := by
  have h3 : (3:Eis)∣a-1 := three_dvd_lambda_sq.trans ha
  exact lambda_sq_dvd_three.trans (by
    convert dvd_add h3 (dvd_mul_right (3:Eis) r) using 1 ;ring)

lemma symbol_omega_pow_primary_shift (j : ℕ) (a r : Eis) (ha : lambda^2∣a-1) :
    eisEmbedding (symbol (omega^j) (a+3*r))=
      eisEmbedding (symbol (omega^j) a)*
        ShortDraftTrace.breveE ((j:ℂ)*eisEmbedding r/3) := by
  obtain ⟨A,B,rfl⟩ := exists_primaryCoord a ha
  let C := (ActualEisensteinCoordinates.coords r).1
  let D := (ActualEisensteinCoordinates.coords r).2
  have hr : r=ActualEisensteinCoordinates.eval C D := (ActualEisensteinCoordinates.eval_coords r).symm
  have hsum : primaryCoord A B+3*r=primaryCoord (A+C) (B+D) := by
    rw [hr,primaryCoord_eq,primaryCoord_eq]
    change 1+3*(A:Eis)+3*(B:Eis)*omega+3*((C:Eis)+(D:Eis)*omega)=_
    push_cast
    ring
  rw [hsum,symbol_pow_numerator _ _ (primaryCoord_primary _ _) j,
    symbol_pow_numerator _ _ (primaryCoord_primary _ _) j,
    symbol_omega_eq_linearRay _ (primaryCoord_primary _ _),
    symbol_omega_eq_linearRay _ (primaryCoord_primary _ _),
    linearRay_primaryCoord,linearRay_primaryCoord,map_pow,map_pow]
  have hp : ShortDraftTrace.breveE ((j:ℂ)*eisEmbedding r/3)=
      (ShortDraftTrace.breveE (eisEmbedding r/3))^j := by
    simpa only [nsmul_eq_mul,mul_div_assoc] using
      AddChar.map_nsmul_eq_pow ShortDraftTrace.breveE j (eisEmbedding r/3)
  rw [hp,hr,breveE_embedding_third_eval]
  rw [show 2*(A+C)+(-1)*(B+D)=(2*A+(-1)*B)+(2*C-D) by ring,
    cubicExp_add,map_mul,mul_pow]

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

def ninthCuspFrequency (h : Eis) : ℂ := cuspFrequency h/3

def unitLowerGauss (h : Eis) (u : Eisˣ) (a : Eis) : ℂ :=
  ∑'r:CubicUnitResidue a,
    (eisEmbedding (symbol (u:Eis) (a+3*GaussianShiftedPartition.representative a r.val))*
      eisEmbedding (symbol (a+3*GaussianShiftedPartition.representative a r.val) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*
        eisEmbedding (a+3*GaussianShiftedPartition.representative a r.val)/eisEmbedding ((u:Eis)*a))

lemma unitLower_phase_identity (h a r k : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda) :
    ShortDraftTrace.breveE ((j:ℂ)*eisEmbedding r/3)*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*r)/eisEmbedding ((u:Eis)*a))=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*residueAdditive (3*k) a r := by
  have ha0 := eisEmbedding_ne_zero ha
  have hu0 := eisEmbedding_ne_zero u.ne_zero
  have hui : eisEmbedding (↑u⁻¹:Eis)=(eisEmbedding (u:Eis))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [←map_mul]
    simp
  have hk' : 3*eisEmbedding k=eisEmbedding h/(eisEmbedding (u:Eis))+
      (j:ℂ)*eisEmbedding a*eisLam := by
    have he := congrArg eisEmbedding hk
    simpa only [map_mul,map_add,map_ofNat,map_natCast,hui,ramifiedEmbedding_traceLambda,
      div_eq_mul_inv] using he
  have hkk : eisEmbedding k=(eisEmbedding h/eisEmbedding (u:Eis)+
      (j:ℂ)*eisEmbedding a*eisLam)/3 := by
    apply (eq_div_iff (by norm_num : (3:ℂ)≠0)).mpr
    linear_combination hk'
  rw [←AddChar.map_add_eq_mul]
  unfold residueAdditive
  rw [←AddChar.map_add_eq_mul]
  apply congrArg ShortDraftTrace.breveE
  simp only [ninthCuspFrequency,cuspFrequency,map_add,map_mul,map_ofNat]
  rw [hkk]
  field_simp [ha0,hu0,eisLam_ne_zero]
  ;ring

lemma unitLowerGauss_factor (h a k : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hu : (u:Eis)=omega^j)
    (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda) :
    unitLowerGauss h u a=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
        (eisEmbedding (symbol (u:Eis) a)*eisEmbedding (symbol 3 a))*cubicUnitGaussSum k a := by
  rw [unitLowerGauss,cubicUnitGaussSum,←tsum_mul_left]
  apply tsum_congr
  intro r
  let x := GaussianShiftedPartition.representative a r.val
  have hchar : eisEmbedding (symbol (u:Eis) (a+3*x))=
      eisEmbedding (symbol (u:Eis) a)*ShortDraftTrace.breveE ((j:ℂ)*eisEmbedding x/3) := by
    rw [hu]
    exact symbol_omega_pow_primary_shift j a x hprimary
  have hs : symbol (a+3*x) a=symbol (3*x) a := symbol_congr ⟨1,by ring⟩
  change (eisEmbedding (symbol (u:Eis) (a+3*x))*eisEmbedding (symbol (a+3*x) a))*
    ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding ((u:Eis)*a))=_
  rw [hchar,hs,symbol_mul_numerator _ _ _ hprimary,map_mul]
  have hp := unitLower_phase_identity h a x k u j ha hk
  calc
    _ = (eisEmbedding (symbol (u:Eis) a)*eisEmbedding (symbol 3 a)*eisEmbedding (symbol x a))*
      (ShortDraftTrace.breveE ((j:ℂ)*eisEmbedding x/3)*
        ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding ((u:Eis)*a))) := by ring
    _ = _ := by rw [hp];ring

theorem unitLowerGauss_eq_unramified (h a k : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hu : (u:Eis)=omega^j)
    (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda) :
    unitLowerGauss h u a=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
        cubicUnitGaussSum (3*h*(u:Eis)) a := by
  rw [unitLowerGauss_factor h a k u j ha hprimary hu hk]
  have hu3 : (u:Eis)^3=1 := by
    rw [hu,←pow_mul,mul_comm j 3,pow_mul,omega_primitive.pow_eq_one,one_pow]
  have hu4 : (u:Eis)^4=(u:Eis) := by
    rw [show (4:ℕ)=3+1 by rfl,pow_add,hu3,pow_one,one_mul]
  have hcop : IsCoprime (3*(u:Eis)^2) a :=
    (isCoprime_mul_unit_right_left (u.isUnit.pow 2) 3 a).mpr
      (primary_coprime_three a hprimary).symm
  have hphase := cubicUnitGaussSum_phase_shift k ((u:Eis)^2) a ha hprimary hcop
  have hchars : eisEmbedding (symbol ((u:Eis)^2) a)*eisEmbedding (symbol (3*(u:Eis)^2) a)=
      eisEmbedding (symbol (u:Eis) a)*eisEmbedding (symbol 3 a) := by
    rw [←map_mul,←symbol_mul_numerator _ _ a hprimary]
    rw [show (u:Eis)^2*(3*(u:Eis)^2)=3*(u:Eis)^4 by ring,hu4,
      symbol_mul_numerator _ _ a hprimary,map_mul]
    ring
  rw [hchars] at hphase
  have hcong : a∣k*(9*(u:Eis)^2)-3*h*(u:Eis) := by
    refine ⟨3*(j:Eis)*ramifiedTraceLambda*(u:Eis)^2,?_⟩
    have hi : (↑u⁻¹:Eis)*(u:Eis)^2=(u:Eis) := by
      rw [pow_two,←mul_assoc]
      simp
    have he := congrArg (fun z:Eis=>3*(u:Eis)^2*z) hk
    have hi' : (u:Eis)^2*(↑u⁻¹:Eis)=(u:Eis) := by simpa only [mul_comm] using hi
    linear_combination he+3*h*hi'
  have hg := cubicUnitGaussSum_frequency_congr (k*(9*(u:Eis)^2)) (3*h*(u:Eis)) a ha hcong
  calc
    _ = ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
      (eisEmbedding (symbol (u:Eis) a)*eisEmbedding (symbol 3 a)*cubicUnitGaussSum k a) := by ring
    _ = _ := by rw [hphase,hg]

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def UnitCuspFrequency (h : Eis) (u : Eisˣ) (j : ℕ) : Prop :=
  (3:Eis)∣h*(↑u⁻¹:Eis)+(j:Eis)*ramifiedTraceLambda

lemma unitCuspFrequency_lift (h a : Eis) (u : Eisˣ) (j : ℕ)
    (ha : lambda^2∣a-1) (hh : UnitCuspFrequency h u j) :
    ∃k:Eis,3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda := by
  obtain ⟨q,hq⟩ := hh
  obtain ⟨r,hr⟩ := three_dvd_lambda_sq.trans ha
  refine ⟨q+(j:Eis)*r*ramifiedTraceLambda,?_⟩
  linear_combination -hq-(j:Eis)*ramifiedTraceLambda*hr

lemma unitLowerGauss_eq_unramified_of_frequency (h : Eis) (a : PrimaryLower)
    (u : Eisˣ) (j : ℕ) (hu : (u:Eis)=omega^j) (hh : UnitCuspFrequency h u j) :
    unitLowerGauss h u a.val=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
        cubicUnitGaussSum (3*h*(u:Eis)) a.val := by
  obtain ⟨k,hk⟩ := unitCuspFrequency_lift h a.val u j (primaryLower_primary a) hh
  exact unitLowerGauss_eq_unramified h a.val k u j (primaryLower_ne_zero a)
    (primaryLower_primary a) hu hk

def unitCuspArithmeticSeries (s : ℂ) (h : Eis) (u : Eisˣ) : ℂ :=
  ∑'a:PrimaryLower,((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s)*unitLowerGauss h u a.val

theorem unitCuspArithmeticSeries_eq (s : ℂ) (h : Eis) (u : Eisˣ) (j : ℕ)
    (hu : (u:Eis)=omega^j) (hh : UnitCuspFrequency h u j) :
    unitCuspArithmeticSeries s h u=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
        unramifiedCubicGaussSeries s (3*h*(u:Eis)) := by
  rw [unitCuspArithmeticSeries,←primaryLowerIdealEquiv.symm.tsum_eq,
    unramifiedCubicGaussSeries,←tsum_mul_left]
  apply tsum_congr
  intro I
  rw [unitLowerGauss_eq_unramified_of_frequency h _ u j hu hh]
  change ((‖eisEmbedding (primaryGenerator I.val)‖^2:ℝ):ℂ)^(-s)*
    (ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
      cubicUnitGaussSum (3*h*(u:Eis)) (primaryGenerator I.val))=_
  rw [eisEmbedding_norm_sq_eq_absNorm_span,(primaryGenerator_spec I.val I.2).1,
    Complex.ofReal_natCast]
  ring

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

lemma cuspTransition_dilate (A : ℝ) (hA : A≠0) :
    cuspTransition A (2*A)=fun v => cuspTransition 1 2 (v/A) := by
  funext v
  unfold cuspTransition
  congr 1
  field_simp

lemma cuspTransition_dilate_deriv (A v : ℝ) (hA : A≠0) :
    deriv (cuspTransition A (2*A)) v=deriv (cuspTransition 1 2) (v/A)/A := by
  rw [cuspTransition_dilate A hA]
  have hd := (((cuspTransition_contDiff 1 2).differentiable (by simp) (v/A)).hasDerivAt).comp v
    ((hasDerivAt_id v).div_const A)
  simpa [Function.comp_def,id_eq,div_eq_mul_inv] using hd.deriv

lemma cuspTransition_dilate_second (A v : ℝ) (hA : A≠0) :
    deriv (deriv (cuspTransition A (2*A))) v=
      deriv (deriv (cuspTransition 1 2)) (v/A)/A^2 := by
  have he : deriv (cuspTransition A (2*A))=
      fun x => deriv (cuspTransition 1 2) (x/A)/A := by
    funext x
    exact cuspTransition_dilate_deriv A x hA
  rw [he]
  have hc := (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff 1 2)).2
  have hd := (((hc.differentiable (by simp) (v/A)).hasDerivAt).comp v
    ((hasDerivAt_id v).div_const A)).div_const A
  simp only [Function.comp_def,id_eq] at hd
  convert hd.deriv using 1; field_simp

def cuspBaseDefectFactor (s : ℂ) (x : ℝ) : ℂ :=
  (x:ℂ)^2*(deriv (deriv (cuspTransition 1 2)) x:ℝ)+
    (2*s-1)*(x:ℂ)*(deriv (cuspTransition 1 2) x:ℝ)

lemma cuspBaseDefectFactor_continuous (s : ℂ) : Continuous (cuspBaseDefectFactor s) := by
  have h1 := (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff 1 2)).2
  have h2 := (contDiff_infty_iff_deriv.mp h1).2
  unfold cuspBaseDefectFactor
  exact ((Complex.continuous_ofReal.pow 2).mul (Complex.continuous_ofReal.comp h2.continuous)).add
    ((continuous_const.mul Complex.continuous_ofReal).mul (Complex.continuous_ofReal.comp h1.continuous))

lemma cuspBaseDefectFactor_compact (s : ℂ) : HasCompactSupport (cuspBaseDefectFactor s) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Set.Icc (1:ℝ) 2))
  intro x hx
  by_contra hn
  have hout : x<1 ∨ 2<x := by simpa only [Set.mem_Icc,not_and_or,not_le] using hn
  obtain ⟨h1,h2⟩ := cuspTransition_derivatives 1 2 x (by norm_num) hout
  exact hx (by simp [cuspBaseDefectFactor,h1,h2])

lemma cuspSeedDefectProfile_dilate (A v : ℝ) (hA : A≠0) (s : ℂ) :
    cuspSeedDefectProfile A (2*A) s v=
      positiveHeightPower s v*cuspBaseDefectFactor s (v/A) := by
  rw [cuspSeedDefectProfile,cuspTransition_dilate_deriv A v hA,cuspTransition_dilate_second A v hA]
  unfold cuspBaseDefectFactor
  push_cast
  field_simp

theorem cuspSeedDefectProfile_dilate_bound :
    ∃C : ℝ,0≤C ∧ ∀A : ℝ,1≤A → ∀v : ℝ,
      ‖cuspSeedDefectProfile A (2*A) (4/3) v‖≤C*A^2 := by
  obtain ⟨B,hB⟩ := (cuspBaseDefectFactor_compact (4/3)).exists_bound_of_continuous
    (cuspBaseDefectFactor_continuous (4/3))
  let C := max B 0
  have hC : 0≤C := le_max_right _ _
  have hbound (x : ℝ) : ‖cuspBaseDefectFactor (4/3) x‖≤C := (hB x).trans (le_max_left _ _)
  refine ⟨4*C,by positivity,fun A hA v => ?_⟩
  have hApos : 0<A := lt_of_lt_of_le zero_lt_one hA
  by_cases hv : v∈Set.Icc A (2*A)
  · have hv1 : 1≤v := hA.trans hv.1
    have hvpos : 0<v := hApos.trans_le hv.1
    have hp : ‖positiveHeightPower (4/3) v‖≤v^2 := by
