        (X*sourceCuspRadialLength (thetaFullFrequency t)/(27*Q^2))*
      (-(Q:ℂ)/(eisEmbedding c)^2*
        ((star (eisEmbedding (symbol c0 ((g (fun _=>1):SL(2,Eis)) 0 0)))*
          A4BadPhase c0 hc0 ((g (fun _=>1):SL(2,Eis)) 1 1) U (ramifiedTraceLambda*thetaFullFrequency t))*
        ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (σ i)*
          phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (ε i)*
          bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i)
            (Ideal.Quotient.mk _ (ramifiedTraceLambda*thetaFullFrequency t)))) := by
  dsimp only
  let c:=c0*∏i,p i
  let Q:ℝ:=‖eisEmbedding c‖^2
  have hc:∀v,(g v:SL(2,Eis)) 1 0≠0:=fun v=>by
    rw [hC v];exact mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
  let d:=fun v:∀i,(Eis⧸Ideal.span {p i})ˣ=>principalCuspDatum (g v) (hc v)
  let weight:=fun v:∀i,(Eis⧸Ideal.span {p i})ˣ=>
    ∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i))
      (fun t=>(actualSextic (Ideal.span {p i}) (hg i)^j i) t) (v i)
  have hheight:∀v,(d v).heightScale=Q:=by
    intro v
    rw [principalCuspDatum_height,hC v]
  have hcol:=sum_smoothedKernel_common_cusp d weight 0 Q (fun _=>rfl) hheight
    W lo hi hlo hsupp hW X hX
  change (∑v,weight v*(d v).smoothedKernel W X)=_
  rw [hcol]
  congr 1
  apply tsum_congr
  intro t
  simp only [sourceCuspScale,Matrix.cons_val_zero,Complex.ofReal_one,div_one,one_pow,mul_one]
  congr 1
  let x:=ramifiedTraceLambda*thetaFullFrequency t
  have hlocal:=principal_stratum_multiplier p hp hcop hg hchar c0 U w x hc0 hr hbez
    g hC hA hD σ ε hfreq hε j hj
  calc
    _=(-(Q:ℂ)/(eisEmbedding c)^2)*
        ∑v,weight v*star (complexCharacter (g v))*
          ShortDraftTrace.breveE (-(eisEmbedding ((g v:SL(2,Eis)) 1 1)*(eisEmbedding x/eisLam^4))/
            (eisEmbedding c0*eisEmbedding (∏i,p i))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      change weight v*((principalCuspDatum (g v) (hc v)).multiplier*(Q:ℂ))*
        ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency t)*(principalCuspDatum (g v) (hc v)).dualPoint)=_
      rw [principalCuspDatum_multiplier,principalCuspDatum_phase,hC v,map_mul]
      dsimp only [c,x]
      rw [map_mul]
      ring
    _=_:=by rw [hlocal]

end CubicEisenstein

open scoped Classical BigOperators MatrixGroups

namespace ShortDraftCRT
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT PrimaryIdealUnitReindex
local notation "Eis" => ActualEisensteinCubic.O

lemma exists_primary_unit_multiple (x:Eis) (hx:¬lambda∣x) :
    ∃u:Eisˣ,lambda^2∣u.val*x-1 := by
  have hg:primaryGenerator (Ideal.span {x})≠0:=primaryGenerator_span_ne_zero_iff x |>.mpr hx
  have hspec:=primaryGenerator_spec (Ideal.span {x}) hg
  have ha:Associated x (primaryGenerator (Ideal.span {x})):=
    Ideal.span_singleton_eq_span_singleton.mp hspec.1.symm
  obtain ⟨u,hu⟩:=ha
  refine ⟨u,?_⟩
  rw [mul_comm,hu]
  exact hspec.2

lemma normalize_coprime_pair (a c:Eis) (hcop:IsCoprime a c) :
    ∃u:Eisˣ,IsCoprime (u.val*a) (u.val*c) ∧
      (lambda∣u.val*c→lambda^2∣u.val*a-1) ∧
      (¬lambda∣u.val*c→lambda^2∣u.val*c-1) := by
  have hunit (u:Eisˣ):IsCoprime (u.val*a) (u.val*c) := by
    obtain ⟨r,s,hrs⟩:=hcop
    refine ⟨r*(↑u⁻¹:Eis),s*(↑u⁻¹:Eis),?_⟩
    calc
      _=((↑u⁻¹:Eis)*u.val)*(r*a+s*c):=by ring
      _=1:=by rw [Units.inv_mul,hrs,mul_one]
  have hd (u:Eisˣ):lambda∣u.val*c↔lambda∣c := by
    constructor
    · intro h
      have hh:=dvd_mul_of_dvd_right h (↑u⁻¹:Eis)
      simpa only [←mul_assoc,Units.inv_mul,one_mul] using hh
    · intro h
      exact dvd_mul_of_dvd_right h u.val
  by_cases hc:lambda∣c
  · have ha:¬lambda∣a:=fun h=>lambda_prime_actual.not_isUnit (hcop.isUnit_of_dvd' h hc)
    obtain ⟨u,hu⟩:=exists_primary_unit_multiple a ha
    exact ⟨u,hunit u,fun _=>hu,fun hn=>False.elim (hn ((hd u).mpr hc))⟩
  · obtain ⟨u,hu⟩:=exists_primary_unit_multiple c hc
    exact ⟨u,hunit u,fun h=>False.elim (hc ((hd u).mp h)),fun _=>hu⟩

theorem exists_normalized_rational_cusp (a c:Eis) (hc:c≠0) :
    ∃a0 c0:Eis,c0≠0 ∧ c0∣c ∧ IsCoprime a0 c0 ∧
      eisEmbedding a0/eisEmbedding c0=eisEmbedding a/eisEmbedding c ∧
      (lambda∣c0→lambda^2∣a0-1) ∧ (¬lambda∣c0→lambda^2∣c0-1) := by
  let d:Eis:=IsBezout.gcd a c
  obtain ⟨a',ha⟩:=IsBezout.gcd_dvd_left a c
  obtain ⟨c',hc'⟩:=IsBezout.gcd_dvd_right a c
  change a=d*a' at ha
  change c=d*c' at hc'
  have hd:d≠0:=by intro hz; exact hc (by rw [hc',hz,zero_mul])
  have hcp:c'≠0:=by intro hz; exact hc (by rw [hc',hz,mul_zero])
  obtain ⟨r,s,hrs⟩:=IsBezout.gcd_eq_sum a c
  have hred:IsCoprime a' c':=by
    refine ⟨r,s,?_⟩
    apply mul_left_cancel₀ hd
    change d*(r*a'+s*c')=d*1
    calc
      _=r*a+s*c:=by rw [ha,hc'];ring
      _=d:=hrs
      _=_:=by ring
  obtain ⟨u,hu,hua,huc⟩:=normalize_coprime_pair a' c' hred
  refine ⟨u.val*a',u.val*c',mul_ne_zero u.ne_zero hcp,?_,hu,?_,hua,huc⟩
  · refine ⟨d*(↑u⁻¹:Eis),?_⟩
    rw [hc']
    calc
      d*c'=((u.val*(↑u⁻¹:Eis))*d)*c':=by rw [Units.mul_inv,one_mul]
      _=_:=by ring
  · rw [ha,hc',map_mul,map_mul,map_mul,map_mul]
    have he:=eisEmbedding_ne_zero hd
    have hf:=eisEmbedding_ne_zero hcp
    have hu0:=eisEmbedding_ne_zero u.ne_zero
    field_simp

end ShortDraftCRT

end

end OAI
end OAIOriginalModule0321

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.FixedConductor
Source SHA256: f644f63b1e9d735658f616059dffaab6bc22d4323ad79edcb2ab73d8a9cfe467
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0322


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

open scoped Classical

namespace CubicEisenstein

section
open ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O

lemma divisor_principal_norm_le (c0 c:Eis) (hc:c≠0) (hdiv:c0∣c) :
    (Ideal.absNorm (Ideal.span {c0}):ℝ)≤(Ideal.absNorm (Ideal.span {c}):ℝ) := by
  have hp:0<Ideal.absNorm (Ideal.span {c}):=Nat.pos_of_ne_zero (by
    intro hz
    exact hc (Ideal.span_singleton_eq_bot.mp (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hd:Ideal.absNorm (Ideal.span {c0})∣Ideal.absNorm (Ideal.span {c}) := by
    obtain ⟨d,hd⟩:=hdiv
    rw [hd,←Ideal.span_singleton_mul_span_singleton,map_mul]
    exact dvd_mul_right _ _
  exact_mod_cast Nat.le_of_dvd hp hd

def fixedCuspLevelBound (c:Eis) : ℝ :=
  243*(Ideal.absNorm (Ideal.span {c}):ℝ)^2

def fixedCuspLevelScale (j:Fin 3) (c0:Eis) : ℝ :=
  27*(sourceCuspScale j)^2*(Ideal.absNorm (Ideal.span {c0}):ℝ)^2

lemma fixedCuspLevelBound_ge_one (c:Eis) (hc:c≠0) : 1≤fixedCuspLevelBound c := by
  have hp:1≤Ideal.absNorm (Ideal.span {c}):=Nat.one_le_iff_ne_zero.mpr (by
    intro hz
    exact hc (Ideal.span_singleton_eq_bot.mp (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hr:(1:ℝ)≤(Ideal.absNorm (Ideal.span {c}):ℝ):=by exact_mod_cast hp
  unfold fixedCuspLevelBound
  nlinarith

lemma fixedCuspLevelScale_pos (j:Fin 3) (c0:Eis) (hc0:c0≠0) : 0<fixedCuspLevelScale j c0 := by
  have hp:0<Ideal.absNorm (Ideal.span {c0}):=Nat.pos_of_ne_zero (by
    intro hz
    exact hc0 (Ideal.span_singleton_eq_bot.mp (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hr:(0:ℝ)<(Ideal.absNorm (Ideal.span {c0}):ℝ):=by exact_mod_cast hp
  have hs:=sourceCuspScale_pos j
  unfold fixedCuspLevelScale
  positivity

lemma fixedCuspLevelScale_le (j:Fin 3) (c0 c:Eis) (hc:c≠0) (hdiv:c0∣c) :
    fixedCuspLevelScale j c0≤fixedCuspLevelBound c := by
  have hd:=divisor_principal_norm_le c0 c hc hdiv
  have hs:(sourceCuspScale j)^2≤9:=by fin_cases j <;> norm_num [sourceCuspScale]
  unfold fixedCuspLevelScale fixedCuspLevelBound
  calc
    27*(sourceCuspScale j)^2*(Ideal.absNorm (Ideal.span {c0}):ℝ)^2≤
      27*9*(Ideal.absNorm (Ideal.span {c}):ℝ)^2:=by gcongr
    _=_:=by ring

end

section
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O

lemma A4_traceLambda_pow_four : ramifiedTraceLambda^4=(9:Eis) := by
  apply eisEmbedding_injective
  rw [map_pow,map_ofNat,ramifiedEmbedding_traceLambda]
  calc
    _=(eisLam^2)^2:=by ring
    _=9:=by rw [TraceLambdaPhase.eisLam_sq];norm_num

structure PrincipalStratumArithmetic {ι:Type*} [Fintype ι]
    (p:ι→Eis) (N a0 c0:Eis) where
  lift : (∀i,(Eis⧸Ideal.span {p i})ˣ)→ι→Eis
  lift_period : ∀v i,N^2∣lift v i
  lift_residue : ∀v i,Ideal.Quotient.mk (Ideal.span {p i}) (lift v i)=(v i:Eis⧸Ideal.span {p i})
  U : Eis
  w : Eis
  bezout : U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1
  sigma : ∀i,(Eis⧸Ideal.span {p i})ˣ
  epsilon : ∀i,(Eis⧸Ideal.span {p i})ˣ
  sigma_value : ∀i,(sigma i:Eis⧸Ideal.span {p i})=
    Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^2*c0*cofactor p i)
  epsilon_value : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i)*
    (sigma i:Eis⧸Ideal.span {p i})*(epsilon i:Eis⧸Ideal.span {p i})=-1
  gamma : (∀i,(Eis⧸Ideal.span {p i})ˣ)→levelThree
  numerator : ∀v,(gamma v:SL(2,Eis)) 0 0=finiteCrossNumerator a0 c0 ramifiedTraceLambda p (lift v)
  denominator : ∀v,(gamma v:SL(2,Eis)) 1 0=c0*∏i,p i
  numerator_fixed : ∀v,(9:Eis)*c0∣(gamma v:SL(2,Eis)) 0 0-(gamma (fun _=>1):SL(2,Eis)) 0 0
  inverse_fixed : ∀v,ramifiedTraceLambda^3*c0∣(gamma v:SL(2,Eis)) 1 1-(gamma (fun _=>1):SL(2,Eis)) 1 1

theorem exists_principalStratumArithmetic {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hprimary:∀i,lambda^2∣p i-1)
    (N a0 c0:Eis) (hc0:c0≠0) (hc3:(3:Eis)∣c0)
    (hN:(9:Eis)*c0∣N) (ha0:lambda^2∣a0-1) (hac:IsCoprime a0 c0)
    (hNp:∀i,IsCoprime N (p i)) :
    Nonempty (PrincipalStratumArithmetic p N a0 c0) := by
  have h9N:(9:Eis)∣N:=(dvd_mul_right 9 c0).trans hN
  have hcN:c0∣N:=(dvd_mul_left c0 9).trans hN
  have hD9:ramifiedTraceLambda^3*c0∣(9:Eis)*c0 := by
    refine ⟨ramifiedTraceLambda,?_⟩
    rw [←A4_traceLambda_pow_four]
    ring
  have hDN:ramifiedTraceLambda^3*c0∣N:=hD9.trans hN
  have hl9:ramifiedTraceLambda∣(9:Eis) := by
    rw [←A4_traceLambda_pow_four]
    exact dvd_pow_self _ (by decide)
  have hlN:ramifiedTraceLambda∣N:=hl9.trans h9N
  have hstdN:lambda^2∣N:=lambda_sq_dvd_three.trans
    ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9N)
  let r:Eis:=∏i,p i
  have hr:lambda^2∣r-1:=primary_finset_product Finset.univ p (fun i _=>hprimary i)
  have hNr:IsCoprime N r:=IsCoprime.prod_right (fun i _=>hNp i)
  have hrNc:IsCoprime r (N*c0):=hNr.symm.mul_right
    (hNr.symm.of_isCoprime_of_dvd_right hcN)
  obtain ⟨U,w,huw⟩:=hNr.symm.of_isCoprime_of_dvd_right hDN
  have hbez:U*r+(ramifiedTraceLambda^3*w)*c0=1 := by
    linear_combination huw
  obtain ⟨σ,ε,hσ,hε⟩:=exists_A4_local_units p hp hcop c0 U w hbez
  have hlf (v:∀i,(Eis⧸Ideal.span {p i})ˣ):=
    exists_strong_unit_frequency_lifts N p hNp v
  choose lift hlift hres hlcop using hlf
  let a:=fun v=>finiteCrossNumerator a0 c0 ramifiedTraceLambda p (lift v)
  have hap:∀v,lambda^2∣a v-1 := by
    intro v
    have hfixed:N∣a v-a0*r:=finiteCrossNumerator_fixed N a0 c0 ramifiedTraceLambda p (lift v)
      (fun i=>(dvd_pow_self N (by decide : (2:ℕ)≠0)).trans (hlift v i))
    have hbase:=primary_mul a0 r ha0 hr
    convert dvd_add (hstdN.trans hfixed) hbase using 1 ; ring
  have hpairs:Pairwise (Function.onFun IsCoprime p):=by
    intro i k hik
    exact (Ideal.isCoprime_span_singleton_iff _ _).mp (hcop hik)
  have hacop:∀v,IsCoprime (a v) (c0*r) := by
    intro v
    exact finiteCrossNumerator_coprime a0 c0 ramifiedTraceLambda p (lift v) hac hpairs
      (fun i=>(hNp i).of_isCoprime_of_dvd_left hcN)
      (fun i=>(hNp i).of_isCoprime_of_dvd_left hlN) (hlcop v)
  obtain ⟨b,d,C,hdet,hb,hd,hmat⟩:=exists_primary_numerator_sector_completions
    N c0 hc0 h9N (fun (_:∀i,(Eis⧸Ideal.span {p i})ˣ)=>()) a (fun _=>r)
    hap (fun _=>hr) hacop (fun _=>hrNc)
    (fun v z _=>finiteCrossNumerator_fixed_sector N a0 c0 ramifiedTraceLambda p (lift v)
      p (lift z) hcN (hlift v) (hlift z) (by simp))
    (fun _ _ _=>by simp)
  let mat:=fun v=>controlledCompletionMatrix (a v) (b v) (c0*r) (d v) (hdet v)
  have hm:∀v,mat v∈levelThree:=by
    intro v
    apply A3_principal_mem_levelThree (mat v)
    · exact three_dvd_primary_sub_one (a v) (hap v)
    · exact (show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans (hb v)
    · exact dvd_mul_of_dvd_left hc3 r
    · exact hd v
  let gamma:=fun v=>(⟨mat v,hm v⟩:levelThree)
  have hentry (v:∀i,(Eis⧸Ideal.span {p i})ˣ) (i j:Fin 2):
      N∣(mat v) i j-(mat (fun _=>1)) i j := by
    have he:=congrArg (fun T:Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {N})=>T i j)
      ((hmat v).trans (hmat (fun _=>1)).symm)
    change Ideal.Quotient.mk (Ideal.span {N}) ((mat v) i j)=
      Ideal.Quotient.mk (Ideal.span {N}) ((mat (fun _=>1)) i j) at he
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  exact ⟨{
    lift := lift
    lift_period := hlift
    lift_residue := hres
    U := U
    w := w
    bezout := hbez
    sigma := σ
    epsilon := ε
    sigma_value := hσ
    epsilon_value := hε
    gamma := gamma
    numerator := fun _=>rfl
    denominator := fun _=>rfl
    numerator_fixed := fun v=>hN.trans (hentry v 0 0)
    inverse_fixed := fun v=>hDN.trans (hentry v 1 1)
  }⟩

lemma PrincipalStratumArithmetic.frequency_congruence {ι:Type*} [Fintype ι]
    {p:ι→Eis} {N a0 c0:Eis} (D:PrincipalStratumArithmetic p N a0 c0)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) (i:ι) :
    Ideal.Quotient.mk (Ideal.span {p i}) ((D.gamma v:SL(2,Eis)) 0 0)=
      (D.sigma i:Eis⧸Ideal.span {p i})*(v i:Eis⧸Ideal.span {p i}) := by
  rw [D.numerator,finiteCrossNumerator_local,D.sigma_value,D.lift_residue]

end

open scoped BigOperators Classical ContDiff MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CompletedDyadic
open CubicKubota CubicJacobiGlobal ShortDraftCusp LocalReflectionBrackets FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
namespace PrincipalStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis}

noncomputable def datum (D:PrincipalStratumArithmetic p N a0 c0)
    (hp:∀i,p i≠0) (hc0:c0≠0) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : SourceCuspDatum :=
  principalCuspDatum (D.gamma v) (by
    rw [D.denominator];exact mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))

lemma datum_point (D:PrincipalStratumArithmetic p N a0 c0)
    (hp:∀i,p i≠0) (hc0:c0≠0) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    (D.datum hp hc0 v).point=eisEmbedding a0/eisEmbedding c0+
      eisLam^2*∑i,eisEmbedding (D.lift v i)/eisEmbedding (p i) := by
  rw [SourceCuspDatum.point,datum,principalCuspDatum_matrix,
    integralComplexMatrix_apply,integralComplexMatrix_apply,D.numerator,D.denominator]
  simpa only [ramifiedEmbedding_traceLambda] using
    ShortDraftCRT.finiteCrossNumerator_fraction a0 c0 ramifiedTraceLambda p (D.lift v) hc0 hp

noncomputable def smoothedValue (D:PrincipalStratumArithmetic p N a0 c0)
    [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0) (hc0:c0≠0)
    (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,
    (∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i))
      (fun t=>(actualSextic (Ideal.span {p i}) (hg i)^j i) t) (v i))*
    (D.datum hp hc0 v).smoothedKernel W X

noncomputable def reflectedValue (D:PrincipalStratumArithmetic p N a0 c0)
    [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0) (hc0:c0≠0)
    (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  letI (i:ι):Field (Eis⧸Ideal.span {p i}):=Ideal.Quotient.field _
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  let c:=c0*∏i,p i
  let Q:ℝ:=‖eisEmbedding c‖^2
  exact fixedRadialCoefficientScalar*∑'t:ThetaFullIndex,
    ((fixedConjugateCuspArray 0 t.1 t.2.1 t.2.2.1.val t.2.2.2.val*
      sourceFrequencyAngle (thetaFullFrequency t))/
      ((ramifiedScale 1 completedRamifiedStep t.2.1*
        Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ))*
    CubicReflectionKernel.paperKernel (Vstar W)
      (X*sourceCuspRadialLength (thetaFullFrequency t)/(27*Q^2))*
    (-(Q:ℂ)/(eisEmbedding c)^2*
      ((star (eisEmbedding (symbol c0 ((D.gamma (fun _=>1):SL(2,Eis)) 0 0)))*
        A4BadPhase c0 hc0 ((D.gamma (fun _=>1):SL(2,Eis)) 1 1) D.U (ramifiedTraceLambda*thetaFullFrequency t))*
      ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
        phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i)*
        bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i)
          (Ideal.Quotient.mk _ (ramifiedTraceLambda*thetaFullFrequency t))))

theorem smoothed_eq_reflected (D:PrincipalStratumArithmetic p N a0 c0)
    [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0) (hc0:c0≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hr:lambda^2∣(∏i,p i)-1) (j:ι→ℕ) (hj:∀i,j i<6)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    D.smoothedValue hp hc0 hg j W X=D.reflectedValue hp hc0 hg j W X := by
  simpa only [smoothedValue,reflectedValue,datum] using
    principal_stratum_smoothed p hp hcop hg hchar c0 D.U D.w hc0 hr D.bezout
      D.gamma D.denominator D.numerator_fixed D.inverse_fixed D.sigma D.epsilon
      D.frequency_congruence D.epsilon_value j hj W lo hi hlo hsupp hW X hX

end PrincipalStratumArithmetic

theorem exists_constructed_principal_reflection {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hprimary:∀i,lambda^2∣p i-1)
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (N a0 c0:Eis) (hc0:c0≠0) (hc3:(3:Eis)∣c0)
    (hN:(9:Eis)*c0∣N) (ha0:lambda^2∣a0-1) (hac:IsCoprime a0 c0)
    (hNp:∀i,IsCoprime N (p i)) :
    ∃D:PrincipalStratumArithmetic p N a0 c0,
      ∀j:ι→ℕ,(∀i,j i<6)→∀(W:ℝ→ℂ)(lo hi:ℝ),0<lo→
        Function.support W⊆Set.Icc lo hi→ContDiff ℝ ∞ W→∀X:ℝ,0<X→
        D.smoothedValue hp hc0 hg j W X=D.reflectedValue hp hc0 hg j W X := by
  obtain ⟨D⟩:=exists_principalStratumArithmetic p hp hcop hprimary N a0 c0 hc0 hc3 hN ha0 hac hNp
  refine ⟨D,?_⟩
  intro j hj W lo hi hlo hsupp hW X hX
  exact D.smoothed_eq_reflected hp hc0 hcop hg hchar
    (primary_finset_product Finset.univ p (fun i _=>hprimary i)) j hj W lo hi hlo hsupp hW X hX

end CubicEisenstein

open scoped BigOperators Classical

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

abbrev BasePrimeIndex (I Q:Ideal Eis) := {P:PrimeIndex I // Q≤P.val}
abbrev FreePrimeIndex (I Q:Ideal Eis) := {P:PrimeIndex I // ¬Q≤P.val}

def basePrimeRow (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) : Eis→*ℂ where
  toFun n:=∏P:BasePrimeIndex I Q,
    (actualSextic P.val.val ((supported_factors_good I hI P.val.val
      (Multiset.mem_toFinset.mp P.val.property)).2.1)^((normalizedFactors I).count P.val.val%6))
        (Ideal.Quotient.mk P.val.val n)
  map_one' := by simp only [map_one,Finset.prod_const_one]
  map_mul' x y := by simp only [map_mul,Finset.prod_mul_distrib]

def freePrimeRow (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) : Eis→*ℂ where
  toFun n:=∏P:FreePrimeIndex I Q,
    (actualSextic P.val.val ((supported_factors_good I hI P.val.val
      (Multiset.mem_toFinset.mp P.val.property)).2.1)^((normalizedFactors I).count P.val.val%6))
        (Ideal.Quotient.mk P.val.val n)
  map_one' := by simp only [map_one,Finset.prod_const_one]
  map_mul' x y := by simp only [map_mul,Finset.prod_mul_distrib]

lemma basePrimeRow_norm (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) (n:Eis) :
    ‖basePrimeRow I hI Q n‖≤1 := by
  change ‖∏P:BasePrimeIndex I Q,_‖≤1
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro P hP;exact norm_nonneg _
  · intro P hP;exact FiniteRayExpansion.norm_char_le_one _ _

lemma freePrimeRow_norm (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) (n:Eis) :
    ‖freePrimeRow I hI Q n‖≤1 := by
  change ‖∏P:FreePrimeIndex I Q,_‖≤1
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro P hP;exact norm_nonneg _
  · intro P hP;exact FiniteRayExpansion.norm_char_le_one _ _

lemma basePrimeRow_periodic (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) :
    CanonicalCoefficientClass.FactorsModulo Q (basePrimeRow I hI Q) := by
  intro x y hxy
  change (∏P:BasePrimeIndex I Q,_)=∏P:BasePrimeIndex I Q,_
  apply Finset.prod_congr rfl
  intro P hP
  have he:Ideal.Quotient.mk P.val.val x=Ideal.Quotient.mk P.val.val y:=
    Ideal.Quotient.eq.mpr (P.property hxy)
  rw [he]

lemma idealRowHom_fixed_conductor_split (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) (n:Eis) :
    idealRowHom n I=basePrimeRow I hI Q n*freePrimeRow I hI Q n := by
  rw [idealRowHom_eq_prime_count_product I hI n]
  exact (Fintype.prod_subtype_mul_prod_subtype (fun P:PrimeIndex I=>Q≤P.val)
    (fun P:PrimeIndex I=>(actualSextic P.val ((supported_factors_good I hI P.val
      (Multiset.mem_toFinset.mp P.property)).2.1)^((normalizedFactors I).count P.val%6))
      (Ideal.Quotient.mk P.val n))).symm

lemma freePrimeIndex_pairwise_coprime (I Q:Ideal Eis) :
    Pairwise (Function.onFun IsCoprime (fun P:FreePrimeIndex I Q=>P.val.val)) := by
  intro P R hPR
  exact Ideal.isCoprime_of_isMaximal (fun he=>hPR (Subtype.ext (Subtype.ext he)))

lemma freePrimeIndex_coprime (I Q:Ideal Eis) (P:FreePrimeIndex I Q) :
    IsCoprime Q P.val.val := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra ht
  have he:P.val.val=Q⊔P.val.val:=
    (show P.val.val.IsMaximal from inferInstance).eq_of_le ht le_sup_right
  exact P.property (le_sup_left.trans he.symm.le)

lemma freePrimeProduct_coprime (I Q:Ideal Eis) :
    IsCoprime Q (∏P:FreePrimeIndex I Q,P.val.val) :=
  IsCoprime.prod_right (fun P _=>freePrimeIndex_coprime I Q P)

lemma freePrimeRow_eq_principalSexticRow (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) (n:Eis) :
    freePrimeRow I hI Q n=
      principalSexticRow (fun P:FreePrimeIndex I Q=>P.val.val) (freePrimeIndex_pairwise_coprime I Q)
        (fun P=>(supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.1)
        (fun P=>(normalizedFactors I).count P.val.val%6)
        (finitePrimeModulus (fun P:FreePrimeIndex I Q=>P.val.val))
        (span_finitePrimeModulus _) (Ideal.Quotient.mk _ n) := by
  rw [principalSexticRow_mk]
  rfl

theorem fixed_conductor_absorb_shared_primes (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis)
    (φ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ) (hφn:∀n,‖φ n‖≤1) :
    CanonicalCoefficientClass.FactorsModulo Q (φ*basePrimeRow I hI Q) ∧
    (∀n,‖(φ*basePrimeRow I hI Q) n‖≤1) ∧
    IsCoprime Q (∏P:FreePrimeIndex I Q,P.val.val) ∧
    (∀n,φ n*idealRowHom n I=(φ*basePrimeRow I hI Q) n*freePrimeRow I hI Q n) := by
  refine ⟨?_,?_,freePrimeProduct_coprime I Q,?_⟩
  · intro x y hxy
    change φ x*basePrimeRow I hI Q x=φ y*basePrimeRow I hI Q y
    rw [hφ x y hxy,basePrimeRow_periodic I hI Q x y hxy]
  · intro n
    change ‖φ n*basePrimeRow I hI Q n‖≤1
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hφn n)).trans (basePrimeRow_norm I hI Q n)
  · intro n
    rw [idealRowHom_fixed_conductor_split I hI Q n]
    exact (mul_assoc _ _ _).symm

end
section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

lemma freePrimeRow_periodic (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) :
    CanonicalCoefficientClass.FactorsModulo (∏P:FreePrimeIndex I Q,P.val.val) (freePrimeRow I hI Q) := by
  intro x y hxy
  change (∏P:FreePrimeIndex I Q,_)=∏P:FreePrimeIndex I Q,_
  apply Finset.prod_congr rfl
  intro P hP
  have hm:x-y∈P.val.val:=
    (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ P))) hxy
  rw [Ideal.Quotient.eq.mpr hm]

lemma fixedFreeRow_periodic (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis)
    (φ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ) :
    CanonicalCoefficientClass.FactorsModulo (Q*(∏P:FreePrimeIndex I Q,P.val.val))
      (φ*freePrimeRow I hI Q) := by
  intro x y hxy
  change φ x*freePrimeRow I hI Q x=φ y*freePrimeRow I hI Q y
  rw [hφ x y (Ideal.mul_le_left hxy),freePrimeRow_periodic I hI Q x y (Ideal.mul_le_right hxy)]

lemma fixedFreeRow_norm (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis)
    (φ:Eis→*ℂ) (hφ:∀n,‖φ n‖≤1) (n:Eis) : ‖(φ*freePrimeRow I hI Q) n‖≤1 := by
  change ‖φ n*freePrimeRow I hI Q n‖≤1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hφ n)).trans (freePrimeRow_norm I hI Q n)

theorem exists_actual_coprime_row (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(I:Ideal Eis)(hI:Supported I)(φ:Eis→*ℂ),
      CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)}) φ ∧
      (∀n,‖φ n‖≤1) ∧
      IsCoprime (Q*Ideal.span {(72:Eis)})
        (∏P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)}),P.val.val) ∧
      (∀n,lambda^2∣n-1 → rowTwist Ψ m f z n=φ n*freePrimeRow I hI (Q*Ideal.span {(72:Eis)}) n) := by
  obtain ⟨I,hI,φ,hφ,hφn,hrow⟩:=exists_fixed_twist_principal_row Ψ Q hΨ hΨnorm m f z hm hf hz hmLam hm2
  obtain ⟨hperiod,hnorm,hcop,hprod⟩:=fixed_conductor_absorb_shared_primes I hI _ φ hφ hφn
  refine ⟨I,hI,φ*basePrimeRow I hI _,hperiod,hnorm,hcop,?_⟩
  intro n hpn
  rw [hrow n hpn,←idealRowHom_eq_principalSexticRow I hI n,hprod n]

theorem exists_actual_coprime_completed_row (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hQ:Q≠0) (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(I:Ideal Eis)(hI:Supported I)(φ:Eis→*ℂ),
      CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)}) φ ∧
      (∀n,‖φ n‖≤1) ∧
      IsCoprime (Q*Ideal.span {(72:Eis)})
        (∏P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)}),P.val.val) ∧
      (Q*Ideal.span {(72:Eis)}*(∏P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)}),P.val.val))≠0 ∧
      CanonicalCoefficientClass.FactorsModulo
        (Q*Ideal.span {(72:Eis)}*(∏P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)}),P.val.val))
        (φ*freePrimeRow I hI (Q*Ideal.span {(72:Eis)})) ∧
      (∀n,‖(φ*freePrimeRow I hI (Q*Ideal.span {(72:Eis)})) n‖≤1) ∧
      (∀W X,completedT (rowTwist Ψ m f z) W X=
        completedT (φ*freePrimeRow I hI (Q*Ideal.span {(72:Eis)})) W X) := by
  obtain ⟨I,hI,φ,hφ,hφn,hcop,hrow⟩:=exists_actual_coprime_row Ψ Q hΨ hΨnorm m f z hm hf hz hmLam hm2
  refine ⟨I,hI,φ,hφ,hφn,hcop,?_,fixedFreeRow_periodic I hI _ φ hφ,
    fixedFreeRow_norm I hI _ φ hφn,?_⟩
  · apply mul_ne_zero
    · apply mul_ne_zero hQ
      simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
      norm_num
    · exact finite_prime_product_ne_bot (fun P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)})=>P.val.val)
  · intro W X
    exact completedT_congr_primary _ _ hrow W X

def fixedQuotientValue (Q:Ideal Eis) (φ:Eis→*ℂ) (x:Eis⧸Q) : ℂ := φ (Quotient.out x)

lemma fixedQuotientValue_mk (Q:Ideal Eis) (φ:Eis→*ℂ)
    (hφ:CanonicalCoefficientClass.FactorsModulo Q φ) (n:Eis) :
    fixedQuotientValue Q φ (Ideal.Quotient.mk Q n)=φ n :=
  hφ _ _ (Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out _))

lemma fixedQuotientValue_norm (Q:Ideal Eis) (φ:Eis→*ℂ) (hφ:∀n,‖φ n‖≤1) (x:Eis⧸Q) :
    ‖fixedQuotientValue Q φ x‖≤1 := hφ _

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
open ConcretePrimeRowBridge
local notation "Eis" => ActualEisensteinCubic.O

def goodMaskMovingIdeal (g r:Eis) : Ideal Eis := (Ideal.span {g})^6*Ideal.span {r}

lemma goodMaskMovingIdeal_supported (g r:Eis)
    (hg:Supported (Ideal.span {g})) (hr:Supported (Ideal.span {r})) :
    Supported (goodMaskMovingIdeal g r) := by
  exact (supported_mul_iff _ _).mpr ⟨supported_pow hg 6,hr⟩

lemma good_odd_prime_two_not_mem (P:Ideal Eis) [P.IsMaximal]
    (hodd:ringChar (Eis⧸P)≠2) : (2:Eis)∉P := by
  intro ht
  have he:=maximal_ideal_eq_span_of_mem P inferInstance (2:Eis) twoIdeal_maximal ht
  exact hodd (he ▸ twoIdeal_characteristic)

lemma count_span_eq_zero_of_not_mem (P:Ideal Eis) (x:Eis) (hx:x∉P) :
    (normalizedFactors (Ideal.span {x})).count P=0 := by
  apply Multiset.count_eq_zero.mpr
  intro hm
  have h0:(Ideal.span {x}:Ideal Eis)≠0:=by
    apply Ideal.span_singleton_eq_bot.not.mpr
    intro he
    exact hx (he ▸ P.zero_mem)
  exact hx (Ideal.dvd_span_singleton.mp
    ((UniqueFactorizationMonoid.mem_normalizedFactors_iff h0).mp hm).2)

lemma good_factor_count (P:Ideal Eis) [P.IsMaximal]
    (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r})) :
    (normalizedFactors (Ideal.span {u.val*lambda^a*(2:Eis)^b*r})).count P=
      (normalizedFactors (Ideal.span {r})).count P := by
  have hl:(Ideal.span {lambda}:Ideal Eis)≠0:=
    Ideal.span_singleton_eq_bot.not.mpr PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero
  have ht:(Ideal.span {(2:Eis)}:Ideal Eis)≠0:=Ideal.span_singleton_eq_bot.not.mpr (by norm_num)
  have hcl:=count_span_eq_zero_of_not_mem P lambda hgood
  have hct:=count_span_eq_zero_of_not_mem P 2 (good_odd_prime_two_not_mem P hodd)
  rw [show u.val*lambda^a*(2:Eis)^b*r=u.val*(lambda^a*(2:Eis)^b*r) by ring,
    Ideal.span_singleton_mul_left_unit u.isUnit,
    ←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_mul_span_singleton,
    ←Ideal.span_singleton_pow,←Ideal.span_singleton_pow,
    normalizedFactors_mul (mul_ne_zero (pow_ne_zero _ hl) (pow_ne_zero _ ht)) hr.1,
    normalizedFactors_mul (pow_ne_zero _ hl) (pow_ne_zero _ ht)]
  simp only [Multiset.count_add,normalizedFactors_pow,Multiset.count_nsmul,hcl,hct,mul_zero,zero_add]

theorem goodMaskMovingIdeal_count (I F:Ideal Eis) (hI:I≠0) (hF:F≠0)
    (m f z:Eis) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (P:Ideal Eis) [P.IsMaximal] (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count P=
      6*(normalizedFactors (Ideal.span {m})).count P+
        4*(normalizedFactors F).count P+(normalizedFactors I).count P := by
  have hmc:(normalizedFactors (Ideal.span {m})).count P=(normalizedFactors (Ideal.span {g})).count P:=by
    rw [hm]
    exact good_factor_count P hgood hodd um am bm g hg
  have hrc:(normalizedFactors (Ideal.span {r})).count P=
      4*(normalizedFactors F).count P+(normalizedFactors I).count P:=by
    have hh:=good_factor_count P hgood hodd u a b r hr
    rw [←hx,←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_pow,hf,hz,
      normalizedFactors_mul (pow_ne_zero 4 hF) hI] at hh
    simpa only [Multiset.count_add,normalizedFactors_pow,Multiset.count_nsmul] using hh.symm
  rw [goodMaskMovingIdeal,normalizedFactors_mul (pow_ne_zero 6 hg.1) hr.1]
  simp only [Multiset.count_add,normalizedFactors_pow,Multiset.count_nsmul,←hmc,hrc]
  omega

lemma squarefree_prime_count_indicator (F P:Ideal Eis) (hF:Squarefree F) (hP:Prime P) :
    (normalizedFactors F).count P=if P∣F then 1 else 0 := by
  have hle:=Multiset.nodup_iff_count_le_one.mp ((squarefree_iff_nodup_normalizedFactors hF.ne_zero).mp hF) P
  by_cases hPF:P∣F
  · rw [ite_eq_left hPF]
    have hp:=Multiset.count_pos.mpr
      ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hF.ne_zero).mpr ⟨hP,hPF⟩)
    omega
  · rw [ite_eq_right hPF]
    apply Multiset.count_eq_zero.mpr
    intro hm
    exact hPF ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hF.ne_zero).mp hm).2

theorem goodMaskMovingIdeal_exponent (I F:Ideal Eis) (hI:I≠0) (hF:Squarefree F)
    (m f z:Eis) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (P:Ideal Eis) [P.IsMaximal] (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count P%6=completedLocalExponent I F P := by
  rw [goodMaskMovingIdeal_count I F hI hF.ne_zero m f z hf hz um am bm g hg hm u a b r hr hx P hgood hodd,
    squarefree_prime_count_indicator F P hF (Ideal.prime_of_isPrime (NeZero.ne P) inferInstance)]
  unfold completedLocalExponent
  omega

theorem goodMaskMovingIdeal_generator_exponent (I F:Ideal Eis) (hI:I≠0) (hF:Squarefree F)
    (m:Eis) (v:Eisˣ)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:(idealGenerator F)^4*(v.val*idealGenerator I)=u.val*lambda^a*(2:Eis)^b*r)
    (P:Ideal Eis) [P.IsMaximal] (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count P%6=completedLocalExponent I F P := by
  exact goodMaskMovingIdeal_exponent I F hI hF m (idealGenerator F) (v.val*idealGenerator I)
    (span_idealGenerator F) (by rw [Ideal.span_singleton_mul_left_unit v.isUnit,span_idealGenerator])
    um am bm g hg hm u a b r hr hx P hgood hodd

end CanonicalRowCompletion

end

end OAI
end OAIOriginalModule0322

/-! Original module: OAI.NumberTheory.DirichletL.RowCompletion.FixedCuspBranches
Source SHA256: b8aefff6f7ce990f97b7695b1f7f147ea53fb7de98846fd5f459cd18b44053cb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0323


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

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
open ConcretePrimeRowBridge
local notation "Eis" => ActualEisensteinCubic.O

lemma prime_dvd_iff_factor_count_pos (P A:Ideal Eis) (hP:Prime P) (hA:A≠0) :
    P∣A ↔ 0<(normalizedFactors A).count P := by
  simp only [Multiset.count_pos,UniqueFactorizationMonoid.mem_normalizedFactors_iff hA,hP,true_and]

theorem goodMaskMovingIdeal_dvd_iff (I F:Ideal Eis) (hI:I≠0) (hF:F≠0)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (P:Ideal Eis) [P.IsMaximal] (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2) :
    P∣goodMaskMovingIdeal g r ↔ P∣I*(Ideal.span {m}*F) := by
  have hP:Prime P:=Ideal.prime_of_isPrime (NeZero.ne P) inferInstance
  have hmI:(Ideal.span {m}:Ideal Eis)≠0:=Ideal.span_singleton_eq_bot.not.mpr hm0
  rw [prime_dvd_iff_factor_count_pos P _ hP (goodMaskMovingIdeal_supported g r hg hr).1,
    prime_dvd_iff_factor_count_pos P _ hP (mul_ne_zero hI (mul_ne_zero hmI hF)),
    goodMaskMovingIdeal_count I F hI hF m f z hf hz um am bm g hg hm u a b r hr hx P hgood hodd,
    normalizedFactors_mul hI (mul_ne_zero hmI hF),normalizedFactors_mul hmI hF]
  simp only [Multiset.count_add]
  omega

theorem goodMaskMovingIdeal_primeSupport (I F:Ideal Eis) (hI:I≠0) (hF:F≠0)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r) :
    IdealMobiusDivisorSum.primeSupport (goodMaskMovingIdeal g r)=
      (IdealMobiusDivisorSum.primeSupport (I*(Ideal.span {m}*F))).filter
        (fun P=>lambda∉P ∧ ringChar (Eis⧸P)≠2) := by
  have hs:=goodMaskMovingIdeal_supported g r hg hr
  have hmI:(Ideal.span {m}:Ideal Eis)≠0:=Ideal.span_singleton_eq_bot.not.mpr hm0
  have hprod:=mul_ne_zero hI (mul_ne_zero hmI hF)
  ext P
  simp only [IdealMobiusDivisorSum.primeSupport,Finset.mem_filter,Multiset.mem_toFinset]
  constructor
  · intro hP
    obtain ⟨hmax,hgood,hodd⟩:=supported_factors_good _ hs P hP
    let:P.IsMaximal:=hmax
    have hp:Prime P:=prime_of_normalized_factor P hP
    have hd: P∣goodMaskMovingIdeal g r:=
      ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hs.1).mp hP).2
    exact ⟨(UniqueFactorizationMonoid.mem_normalizedFactors_iff hprod).mpr ⟨hp,
      (goodMaskMovingIdeal_dvd_iff I F hI hF m f z hm0 hf hz um am bm g hg hm
        u a b r hr hx P hgood hodd).mp hd⟩,hgood,hodd⟩
  · rintro ⟨hP,hgood,hodd⟩
    have hp:Prime P:=prime_of_normalized_factor P hP
    let:P.IsMaximal:=(Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hd:=((UniqueFactorizationMonoid.mem_normalizedFactors_iff hprod).mp hP).2
    exact (UniqueFactorizationMonoid.mem_normalizedFactors_iff hs.1).mpr ⟨hp,
      (goodMaskMovingIdeal_dvd_iff I F hI hF m f z hm0 hf hz um am bm g hg hm
        u a b r hr hx P hgood hodd).mpr hd⟩

def goodMaskNonresidualPool (I F:Ideal Eis) (m g r:Eis) : Finset (Ideal Eis) :=
  (IdealMobiusDivisorSum.primeSupport (goodMaskMovingIdeal g r)).filter
    (fun P=>¬P∣rowResidualPart I (Ideal.span {m}*F))

theorem goodMaskNonresidualPool_eq (I F:Ideal Eis) (hI:I≠0) (hF:F≠0)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r) :
    goodMaskNonresidualPool I F m g r=completedReflectionPool I (Ideal.span {m}*F) := by
  rw [goodMaskNonresidualPool,
    goodMaskMovingIdeal_primeSupport I F hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx]
  ext P
  simp only [Finset.mem_filter,completedReflectionPool]
  tauto

theorem goodMaskNonresidualPool_eq_on_fiber (I J F:Ideal Eis)
    (hI:I≠0) (hJ:J≠0) (hF:F≠0) (m f z w:Eis) (hm0:m≠0)
    (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I) (hw:Ideal.span {w}=J)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (u':Eisˣ) (a' b':ℕ) (r':Eis) (hr':Supported (Ideal.span {r'}))
    (hx':f^4*w=u'.val*lambda^a'*(2:Eis)^b'*r')
    (hA:rowPowerfulPart I=rowPowerfulPart J)
    (hT:rowMaskPart I (Ideal.span {m}*F)=rowMaskPart J (Ideal.span {m}*F)) :
    goodMaskNonresidualPool I F m g r=goodMaskNonresidualPool J F m g r' := by
  rw [goodMaskNonresidualPool_eq I F hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx,
    goodMaskNonresidualPool_eq J F hJ hF m f w hm0 hf hw um am bm g hg hm u' a' b' r' hr' hx']
  exact completedReflectionPool_eq_on_fiber I J (Ideal.span {m}*F) hI hJ
    (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm0) hF) hA hT

theorem goodMaskNonresidualPool_free_eq (I F Q0:Ideal Eis) (hI:I≠0) (hF:F≠0)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r) :
    (goodMaskNonresidualPool I F m g r).filter (fun P=>¬Q0≤P)=
      (completedReflectionPool I (Ideal.span {m}*F)).filter (fun P=>¬Q0≤P) := by
  rw [goodMaskNonresidualPool_eq I F hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx]

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
open ConcretePrimeRowBridge CanonicalUnitEuler
local notation "Eis" => ActualEisensteinCubic.O

theorem goodMaskMovingIdeal_principal_row (I F:Ideal Eis) (hI:I≠0) (hF:Squarefree F)
    (m f z:Eis) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r) (n:Eis) :
    idealRowHom n (goodMaskMovingIdeal g r)=
      principalSexticRow (fun P:PrimeIndex (goodMaskMovingIdeal g r)=>P.val)
        (primeIndex_pairwise_coprime (goodMaskMovingIdeal g r))
        (fun P=>(supported_factors_good _ (goodMaskMovingIdeal_supported g r hg hr)
          P.val (Multiset.mem_toFinset.mp P.property)).2.1)
        (fun P=>completedLocalExponent I F P.val)
        (finitePrimeModulus (fun P:PrimeIndex (goodMaskMovingIdeal g r)=>P.val))
        (span_finitePrimeModulus _) (Ideal.Quotient.mk _ n) := by
  rw [idealRowHom_eq_principalSexticRow _ (goodMaskMovingIdeal_supported g r hg hr)]
  have he:(fun P:PrimeIndex (goodMaskMovingIdeal g r)=>(normalizedFactors (goodMaskMovingIdeal g r)).count P.val%6)=
      (fun P=>completedLocalExponent I F P.val):=by
    funext P
    have hdata:=supported_factors_good _ (goodMaskMovingIdeal_supported g r hg hr)
      P.val (Multiset.mem_toFinset.mp P.property)
    exact goodMaskMovingIdeal_exponent I F hI hF m f z hf hz um am bm g hg hm
      u a b r hr hx P.val hdata.2.1 hdata.2.2
  rw [he]

theorem rowTwist_eq_computed_principal_row
    (Ψ:Eis→*ℂ) (I F:Ideal Eis) (hI:I≠0) (hF:Squarefree F)
    (m f z:Eis) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (hmLam:lambda∣m) (hm2:(2:Eis)∣m)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hpr:lambda^2∣r-1) (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (n:Eis) (hpn:lambda^2∣n-1) :
    rowTwist Ψ m f z n=(Ψ*numeratorBadTwist u a b r hr) n *
      principalSexticRow (fun P:PrimeIndex (goodMaskMovingIdeal g r)=>P.val)
        (primeIndex_pairwise_coprime (goodMaskMovingIdeal g r))
        (fun P=>(supported_factors_good _ (goodMaskMovingIdeal_supported g r hg hr)
          P.val (Multiset.mem_toFinset.mp P.property)).2.1)
        (fun P=>completedLocalExponent I F P.val)
        (finitePrimeModulus (fun P:PrimeIndex (goodMaskMovingIdeal g r)=>P.val))
        (span_finitePrimeModulus _) (Ideal.Quotient.mk _ n) := by
  rw [rowTwist_eq_fixed_times_good_row_primary Ψ m f z hmLam hm2 um am bm g hg hm
    u a b r hr hpr hx n hpn]
  change _*idealRowHom n (goodMaskMovingIdeal g r)=_
  rw [goodMaskMovingIdeal_principal_row I F hI hF m f z hf hz um am bm g hg hm u a b r hr hx n]

theorem goodMaskMovingIdeal_exponent_eq_on_fiber
    (I J F:Ideal Eis) (hI:I≠0) (hJ:J≠0) (hF:Squarefree F)
    (m f z w:Eis) (hm0:m≠0)
    (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I) (hw:Ideal.span {w}=J)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (u':Eisˣ) (a' b':ℕ) (r':Eis) (hr':Supported (Ideal.span {r'}))
    (hx':f^4*w=u'.val*lambda^a'*(2:Eis)^b'*r')
    (hA:rowPowerfulPart I=rowPowerfulPart J)
    (hT:rowMaskPart I (Ideal.span {m}*F)=rowMaskPart J (Ideal.span {m}*F))
    (P:completedReflectionPool I (Ideal.span {m}*F)) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count P.val%6=
      (normalizedFactors (goodMaskMovingIdeal g r')).count P.val%6 := by
  let:P.val.IsMaximal:=completedReflectionPool_maximal I (Ideal.span {m}*F) P
  have hgood:=completedReflectionPool_good I (Ideal.span {m}*F) P
  have hodd:=completedReflectionPool_odd I (Ideal.span {m}*F) P
  rw [goodMaskMovingIdeal_exponent I F hI hF m f z hf hz um am bm g hg hm u a b r hr hx P.val hgood hodd,
    goodMaskMovingIdeal_exponent J F hJ hF m f w hf hw um am bm g hg hm u' a' b' r' hr' hx' P.val hgood hodd]
  exact completedReflectionPool_exponent_eq I J F (Ideal.span {m}*F) hI hJ
    (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm0) hF.ne_zero) hA hT P

end CanonicalRowCompletion

namespace CubicEisenstein

section
open scoped Classical BigOperators MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT CompletedGauss CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

lemma amplitude_source_nonzero (p:ThetaFullIndex)
    (hp:s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val≠0) :
    (sourceCuspCoefficients s.index).value (thetaFullFrequency p)≠0 := by
  intro hz
  apply hp
  have hz':(sourceCuspCoefficients s.index).value
      (fixedCuspArrayIndex p.1 p.2.1 p.2.2.1.val p.2.2.2.val)=0:=by
    simpa only [thetaFullFrequency_eq_fixedCuspArrayIndex] using hz
  simp only [amplitude,fixedConjugateCuspArray,fixedCuspArray,hz',zero_div,ite_self,
    star_zero,zero_mul]

lemma amplitude_integral_phase (p:ThetaFullIndex) (c d:Eis) (hc:c≠0) :
    s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val *
      ShortDraftTrace.breveE (cuspFrequency (thetaFullFrequency p)*eisEmbedding (s.upper 0 0)^2*
        (eisEmbedding d/eisEmbedding c)/(sourceCuspScale s.index:ℂ)) =
    s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val *
      ShortDraftTrace.breveE (-(eisEmbedding d*
        (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/
          eisEmbedding c) := by
  by_cases hp:s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val=0
  · rw [hp,zero_mul,zero_mul]
  · rw [sourceCuspPhaseNumerator_phase s.index (s.upper 0 0) (thetaFullFrequency p) c d hc
      (s.amplitude_source_nonzero p hp)]

lemma datum_integral_phase (g:levelTwo) (c:Eis) (hc:c≠0)
    (hg:((g:SL(2,Eis))*H) 1 0=c) (p:ThetaFullIndex) :
    (fixedConjugateCuspArray s.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
      sourceFrequencyAngle (thetaFullFrequency p))*
      ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
        ((s.datum g (by rwa [hg])).dualPoint/(sourceCuspScale s.index:ℂ))) =
    s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
      ShortDraftTrace.breveE (-(eisEmbedding (((g:SL(2,Eis))*H) 1 1)*
        (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/
          eisEmbedding c) := by
  have hphase:=s.datum_additive_phase g (by rwa [hg])
    (cuspFrequency (thetaFullFrequency p)) (sourceCuspScale s.index:ℂ)
  simp only [hg] at hphase
  calc
    _=s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
        ShortDraftTrace.breveE (cuspFrequency (thetaFullFrequency p)*eisEmbedding (s.upper 0 0)^2*
          (eisEmbedding (((g:SL(2,Eis))*H) 1 1)/eisEmbedding c)/(sourceCuspScale s.index:ℂ)) := by
      rw [show -cuspFrequency (thetaFullFrequency p)*
          ((s.datum g (by rwa [hg])).dualPoint/(sourceCuspScale s.index:ℂ))=
        -cuspFrequency (thetaFullFrequency p)*(s.datum g (by rwa [hg])).dualPoint/
          (sourceCuspScale s.index:ℂ) by ring,hphase]
      unfold amplitude
      rw [←thetaFullFrequency_eq_fixedCuspArrayIndex]
      ring
    _=_:=s.amplitude_integral_phase p c _ hc

def stratumShapeFactor (c:Eis) : ℂ :=
  -star (levelTwoComplexCharacter s.gamma)*eisEmbedding (s.upper 0 0)^2*
    ((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ)/eisEmbedding c^2

lemma datum_common_row_factor (g:levelTwo) (c:Eis) (hc:c≠0)
    (hg:((g:SL(2,Eis))*H) 1 0=c) :
    (s.datum g (by rwa [hg])).multiplier*((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ)=
      s.stratumShapeFactor c*star (levelTwoComplexCharacter g) := by
  have hm:=s.smoothed_row_factor g (by rwa [hg])
  simp only [s.datum_heightScale,hg,ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] at hm
  rw [hm]
  unfold stratumShapeFactor
  ring

end FixedCuspShape
end

open scoped Classical BigOperators ContDiff MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT CompletedGauss CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

theorem sum_smoothedKernel_integral_phase {ι:Type*} [Fintype ι]
    (g:ι→levelTwo) (c:Eis) (hc:c≠0) (hC:∀v,((g v:SL(2,Eis))*H) 1 0=c)
    (w:ι→ℂ) (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    (∑v,w v*(s.datum (g v) (by rw [hC v];exact hc)).smoothedKernel W X)=
      fixedRadialCoefficientScalar*s.stratumShapeFactor c*
      ∑'p:ThetaFullIndex,
        (s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val /
          ((ramifiedScale 1 completedRamifiedStep p.2.1*
            Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ))*
        CubicReflectionKernel.paperKernel (Vstar W)
          ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2))*
            (ramifiedScale 1 completedRamifiedStep p.2.1)^3*
            (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3)*
        (∑v,w v*star (levelTwoComplexCharacter (g v))*
          ShortDraftTrace.breveE (-(eisEmbedding (((g v:SL(2,Eis))*H) 1 1)*
            (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/
              eisEmbedding c)) := by
  let d:ι→SourceCuspDatum:=fun v=>s.datum (g v) (by rw [hC v];exact hc)
  have hindex:∀v,(d v).index=s.index:=fun _=>rfl
  have hheight:∀v,(d v).heightScale=(Ideal.absNorm (Ideal.span {c}):ℝ):=by
    intro v
    dsimp only [d]
    rw [s.datum_heightScale,hC v,ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  have he:=sum_smoothedKernel_common_cusp d w s.index (Ideal.absNorm (Ideal.span {c}):ℝ)
    hindex hheight W a b ha hsupp hW X hX
  rw [he]
  conv_rhs => rw [mul_assoc]
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*z)
  rw [←tsum_mul_left]
  apply tsum_congr
  intro p
  rw [sourceCusp_full_index_kernel_argument p s.index (Ideal.absNorm (Ideal.span {c}):ℝ) X]
  let A:ℂ:=fixedConjugateCuspArray s.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
    sourceFrequencyAngle (thetaFullFrequency p)
  let B:ℂ:=s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val
  let lengthScale:ι→ℂ:=fun v=>w v*((d v).multiplier*((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ))*
    ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*((d v).dualPoint/(sourceCuspScale s.index:ℂ)))
  let R:ι→ℂ:=fun v=>w v*star (levelTwoComplexCharacter (g v))*
    ShortDraftTrace.breveE (-(eisEmbedding (((g v:SL(2,Eis))*H) 1 1)*
      (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/eisEmbedding c)
  have hs:A*(∑v,lengthScale v)=s.stratumShapeFactor c*B*(∑v,R v):=by
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    dsimp only [lengthScale,R]
    calc
      _=w v*(((d v).multiplier*((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ))*
          (A*ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
            ((d v).dualPoint/(sourceCuspScale s.index:ℂ))))):=by ring
      _=w v*((s.stratumShapeFactor c*star (levelTwoComplexCharacter (g v)))*
          (B*ShortDraftTrace.breveE (-(eisEmbedding (((g v:SL(2,Eis))*H) 1 1)*
            (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/eisEmbedding c))):=by
        rw [s.datum_common_row_factor (g v) c hc (hC v),s.datum_integral_phase (g v) c hc (hC v) p]
      _=_:=by ring
  let D:ℂ:=((ramifiedScale 1 completedRamifiedStep p.2.1*
    Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ)
  let K:ℂ:=CubicReflectionKernel.paperKernel (Vstar W)
    ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2))*
      (ramifiedScale 1 completedRamifiedStep p.2.1)^3*
      (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3)
  change A/D*K*(∑v,lengthScale v)=s.stratumShapeFactor c*(B/D*K*(∑v,R v))
  calc
    _=(A*(∑v,lengthScale v))/D*K:=by ring
    _=(s.stratumShapeFactor c*B*(∑v,R v))/D*K:=by rw [hs]
    _=_:=by ring

lemma stratumShapeFactor_norm (c:Eis) (hc:c≠0) : ‖s.stratumShapeFactor c‖=1 := by
  have hu:‖eisEmbedding (s.upper 0 0)‖=1:=by
    rcases s.upper_unit with ⟨u,hu⟩
    rw [←hu]
    exact GaussGeneratorTransport.norm_eisEmbedding_unit u
  have hn:‖eisEmbedding c‖^2≠0:=pow_ne_zero _ (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc))
  rw [stratumShapeFactor,norm_div,norm_mul,norm_mul,norm_neg,norm_star,
    norm_levelTwoComplexCharacter,norm_pow,hu,one_pow,one_mul,one_mul,norm_pow,
    Complex.norm_real,Real.norm_of_nonneg (Nat.cast_nonneg _),
    ←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  exact div_self hn

end FixedCuspShape
end CubicEisenstein

open scoped BigOperators Classical ContDiff

namespace CompletedGauss

section
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

def fixedCuspArrayWithPhase (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis) : ℂ :=
  phaseArray m n b*fixedConjugateCuspArray cusp u m n b

lemma fixedCuspArrayWithPhase_norm_le_one (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (m:ℕ) (n b:Ideal Eis) : ‖fixedCuspArrayWithPhase cusp u phaseArray m n b‖≤1 := by
  rw [fixedCuspArrayWithPhase,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (hphase m n b)).trans (fixedConjugateCuspArray_norm_le_one cusp u m n b)

lemma fixedCuspArrayWithPhase_zero (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis)
    (h:¬fixedCuspArrayEligible n b) : fixedCuspArrayWithPhase cusp u phaseArray m n b=0 := by
  simp only [fixedCuspArrayWithPhase,fixedConjugateCuspArray,
    fixedCuspArray_zero_of_ineligible _ _ _ _ _ h,star_zero,mul_zero]

namespace ReflectedBranchData

def extractedFixedCuspArrayWithPhase {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis) : ℂ :=
  fixedCuspArrayWithPhase cusp u phaseArray m
    (reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 1*n)
    (reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 2*b)

lemma extractedFixedCuspArrayWithPhase_norm_le_one {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (m:ℕ) (n b:Ideal Eis) : ‖d.extractedFixedCuspArrayWithPhase cusp u phaseArray m n b‖≤1 :=
  fixedCuspArrayWithPhase_norm_le_one cusp u phaseArray hphase m _ _

lemma extractedFixedCuspArrayWithPhase_eq {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis) :
    d.extractedFixedCuspArrayWithPhase cusp u phaseArray m n b=
      phaseArray m
        (reflectionExtractedDivisor (fun p:d.primes=>p.val)
          (fun p=>completedLocalExponent I F p.val) d.label 1*n)
        (reflectionExtractedDivisor (fun p:d.primes=>p.val)
          (fun p=>completedLocalExponent I F p.val) d.label 2*b)*
      d.extractedFixedCuspArray cusp u m n b := rfl

lemma extractedFixedCuspArrayWithPhase_zero {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis)
    (h:¬fixedCuspArrayEligible
      (reflectionExtractedDivisor (fun p:d.primes=>p.val)
        (fun p=>completedLocalExponent I F p.val) d.label 1*n)
      (reflectionExtractedDivisor (fun p:d.primes=>p.val)
        (fun p=>completedLocalExponent I F p.val) d.label 2*b)) :
    d.extractedFixedCuspArrayWithPhase cusp u phaseArray m n b=0 :=
  fixedCuspArrayWithPhase_zero cusp u phaseArray m _ _ h

def withExtractedFixedCuspArrayWithPhase {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀m k,‖rowPhase m k‖≤1) : ReflectedBranchData levelBound K I F Q :=
  d.withCanonicalCuspArray (d.extractedFixedCuspArrayWithPhase cusp u phaseArray)
    (fun m n b=>d.extractedFixedCuspArrayWithPhase_norm_le_one cusp u phaseArray hphase m n.val b.val)
    rowPhase hrow

lemma withExtractedFixedCuspArrayWithPhase_amplitude {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀m k,‖rowPhase m k‖≤1) (i:ℕ×ℕ×ℕ) (n b:Ideal Eis) :
    (d.withExtractedFixedCuspArrayWithPhase cusp u phaseArray hphase rowPhase hrow).amplitude i n b=
      d.extractedFixedCuspArrayWithPhase cusp u phaseArray i.1 n b := rfl

theorem withExtractedFixedCuspArrayWithPhase_value {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀m k,‖rowPhase m k‖≤1)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hsupp:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W)
    (X ρ q:ℝ) (hX:0<X) (hρ:0<ρ) (hq:1<q)
    (hK:0<completedResidualScale K I Q)
    (k:idealRange (completedResidualScale K I Q))
    (hk:completedResidualScale K I Q/2≤(Ideal.absNorm k.val:ℝ)) :
    (d.withExtractedFixedCuspArrayWithPhase cusp u phaseArray hphase rowPhase hrow).value W X ρ q k=
      d.rawValue (d.extractedFixedCuspArrayWithPhase cusp u phaseArray) rowPhase W X ρ q k :=
  d.withCanonicalCuspArray_value (d.extractedFixedCuspArrayWithPhase cusp u phaseArray)
    (fun m n b=>d.extractedFixedCuspArrayWithPhase_norm_le_one cusp u phaseArray hphase m n.val b.val)
    rowPhase hrow W a b ha hsupp hW X ρ q hX hρ hq hK k hk

end ReflectedBranchData
end
section

open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

def sixPhaseFixedCuspBranch (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    ReflectedBranchData levelBound K I F Q :=
  (sixReflectedBranch I F Q hI hQ K levelBound levelScale hlevel hbound e
    (fixedCuspArrayWithPhase cusp u phaseArray)
    (fixedCuspArrayWithPhase_norm_le_one cusp u phaseArray hphase) rowPhase hrow).withExtractedFixedCuspArrayWithPhase cusp u phaseArray hphase rowPhase hrow

lemma sixPhaseFixedCuspBranch_primes (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    (sixPhaseFixedCuspBranch I F Q hI hQ K levelBound levelScale hlevel hbound e cusp u
      phaseArray hphase rowPhase hrow).primes=reflectionActivePool I Q e := rfl

lemma sixPhaseFixedCuspBranch_amplitude (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1)
    (i:ℕ×ℕ×ℕ) (n b:Ideal Eis) :
    let d:=sixPhaseFixedCuspBranch I F Q hI hQ K levelBound levelScale hlevel hbound e cusp u
      phaseArray hphase rowPhase hrow
    let D:=reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 1
    let E:=reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 2
    d.amplitude i n b=phaseArray i.1 (D*n) (E*b)*fixedConjugateCuspArray cusp u i.1 (D*n) (E*b) := rfl

lemma sixPhaseFixedCuspBranch_scale (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K X levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    let d:=sixPhaseFixedCuspBranch I F Q hI hQ K levelBound levelScale hlevel hbound e cusp u
      phaseArray hphase rowPhase hrow
    completedBranchScale K (X/d.levelScale) I F Q (fun P:d.primes=>P.val) d.label=
      completedBranchScale K (X/levelScale) I F Q
        (fun P:reflectionActivePool I Q e=>P.val) (reflectionActiveLabel I Q e) := rfl

end

open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

def sixPhaseFixedCuspFiber (rays:ℕ) (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound:ℝ) (levelScale:SixReflectionIndex rays I Q→ℝ)
    (hlevel:∀x,0<levelScale x) (hlevelBound:∀x,levelScale x≤levelBound)
    (cusp:SixReflectionIndex rays I Q→Fin 3) (unit:SixReflectionIndex rays I Q→Eisˣ)
    (phaseArray:SixReflectionIndex rays I Q→ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hphase:∀x m n b,‖phaseArray x m n b‖≤1)
    (rayWeight:SixReflectionIndex rays I Q→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:SixReflectionIndex rays I Q→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1) : ReflectedFiberData rays levelBound K I F Q where
  pool:=completedReflectionPool I Q
  maximal:=completedReflectionPool_maximal I Q
  divides:=completedReflectionPool_divides I Q hI hQ
  branch:=fun x=>sixPhaseFixedCuspBranch I F Q hI hQ K levelBound (levelScale x) (hlevel x) (hlevelBound x)
    x.2 (cusp x) (unit x) (phaseArray x) (hphase x) (rowPhase x) (hrow x)
  weight:=fun x=>rayWeight x*reflectionSixInactiveWeight I F Q x.2
  weight_bound:=by
    intro x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (hray x)).trans (reflectionSixInactiveWeight_norm_le_one I F Q x.2)

theorem sixPhaseFixedCuspFiber_value (rays:ℕ) (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound:ℝ) (levelScale:SixReflectionIndex rays I Q→ℝ)
    (hlevel:∀x,0<levelScale x) (hlevelBound:∀x,levelScale x≤levelBound)
    (cusp:SixReflectionIndex rays I Q→Fin 3) (unit:SixReflectionIndex rays I Q→Eisˣ)
    (phaseArray:SixReflectionIndex rays I Q→ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hphase:∀x m n b,‖phaseArray x m n b‖≤1)
    (rayWeight:SixReflectionIndex rays I Q→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:SixReflectionIndex rays I Q→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1)
    (W:ℝ→ℂ) (X ρ q:ℝ) (k:idealRange (completedResidualScale K I Q)) :
    let d:=sixPhaseFixedCuspFiber rays I F Q hI hQ K levelBound levelScale hlevel hlevelBound
      cusp unit phaseArray hphase rayWeight hray rowPhase hrow
    d.value W X ρ q k=
      ∑t:Fin rays,∑A:Finset (completedReflectionPool I Q),∑e:A→Fin 3,
        reflectionInactiveStratumWeight I F Q A*rayWeight (t,encodeReflectionSix ⟨A,e⟩)*
          (d.branch (t,encodeReflectionSix ⟨A,e⟩)).value W X ρ q k := by
  dsimp only
  rw [ReflectedFiberData.value,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  calc
    _=∑e:completedReflectionPool I Q→Fin 6,reflectionSixInactiveWeight I F Q e*
      (rayWeight (t,e)*(sixPhaseFixedCuspBranch I F Q hI hQ K levelBound (levelScale (t,e))
        (hlevel (t,e)) (hlevelBound (t,e)) e (cusp (t,e)) (unit (t,e))
        (phaseArray (t,e)) (hphase (t,e)) (rowPhase (t,e)) (hrow (t,e))).value W X ρ q k) := by
          apply Finset.sum_congr rfl
          intro e _
          dsimp only [sixPhaseFixedCuspFiber]
          ring
    _=_ := by
      rw [sum_reflectionSixInactiveWeight_unpad]
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro e _
      dsimp only [sixPhaseFixedCuspFiber]
      exact (mul_assoc _ _ _).symm

end CompletedGauss

end

end OAI
end OAIOriginalModule0323

/-! Original module: OAI.NumberTheory.DirichletL.Cusp.StaticReflectionPhases
Source SHA256: 0cf6e362b173a959bf7e5f2e980e29149e29ce36032fdf92f317d91135850161
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0324


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

section
open scoped BigOperators Classical MatrixGroups

namespace ShortDraftCusp
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma A4PhaseFromResidue_norm (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {ramifiedTraceLambda^3*c0}) (x:Eis) :
    ‖A4PhaseFromResidue c0 hc0 v x‖=1 := by
  let:Finite (Eis⧸Ideal.span {ramifiedTraceLambda^3*c0}):=
    finite_quotient_span (A4_bad_modulus_ne_zero c0 hc0)
  unfold A4PhaseFromResidue
  exact AddChar.norm_apply _ _
end ShortDraftCusp

namespace CubicEisenstein
open ActualEisensteinCubic CompletedGauss ShortDraftCusp ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceFrequencyAngle_norm_le_one (h:Eis) : ‖sourceFrequencyAngle h‖≤1 := by
  by_cases hh:h=0
  · simp only [hh,sourceFrequencyAngle,map_zero,norm_zero,Complex.ofReal_zero,div_zero]
    norm_num
  · exact (sourceFrequencyAngle_norm h hh).le

namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

def reflectionStaticPhase (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {ramifiedTraceLambda^3*c0})
    (dualNumerator:ℕ→Ideal Eis→Ideal Eis→Eis) (u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) : ℂ :=
  sourceFrequencyAngle (fixedCuspArrayIndex u m I J)*
    ShortDraftTrace.breveE (-cuspFrequency (fixedCuspArrayIndex u m I J)*
      eisEmbedding (s.upper 0 0*s.upper 0 1)/(sourceCuspScale s.index:ℂ))*
    A4PhaseFromResidue c0 hc0 v (dualNumerator m I J)

lemma reflectionStaticPhase_norm_le_one (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {ramifiedTraceLambda^3*c0})
    (dualNumerator:ℕ→Ideal Eis→Ideal Eis→Eis) (u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) : ‖s.reflectionStaticPhase c0 hc0 v dualNumerator u m I J‖≤1 := by
  simp only [reflectionStaticPhase,norm_mul,breveE_norm,A4PhaseFromResidue_norm,mul_one]
  exact sourceFrequencyAngle_norm_le_one _

lemma fixedCuspArrayWithPhase_reflectionStaticPhase (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {ramifiedTraceLambda^3*c0})
    (dualNumerator:ℕ→Ideal Eis→Ideal Eis→Eis) (u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) :
    fixedCuspArrayWithPhase s.index u (s.reflectionStaticPhase c0 hc0 v dualNumerator u) m I J=
      s.amplitude u m I J*A4PhaseFromResidue c0 hc0 v (dualNumerator m I J) := by
  unfold fixedCuspArrayWithPhase reflectionStaticPhase amplitude
  ring

end FixedCuspShape
end CubicEisenstein
end

open scoped Classical BigOperators

namespace CanonicalRowCompletion
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalCoefficientClass
local notation "Eis" => ActualEisensteinCubic.O

def reflectionConductor (q:ℕ) : Eis := (2592*q:ℕ)

def reflectionExcludedPrimes (q:ℕ) : Finset (Ideal Eis) :=
  gcdMaskPrimes (Ideal.span {reflectionConductor q})

lemma reflectionConductor_ne_zero (q:ℕ) (hq:q≠0) : reflectionConductor q≠0 := by
  unfold reflectionConductor
  exact_mod_cast Nat.mul_ne_zero (by decide : 2592≠0) hq

lemma reflectionConductor_ideal (q:ℕ) :
    Ideal.span {reflectionConductor q}=
      Ideal.span {(9:Eis)}*(fixedBaseConductor q*Ideal.span {(72:Eis)}) := by
  rw [fixedBaseConductor_principal,Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_mul_span_singleton]
  congr 1
  unfold reflectionConductor
  push_cast
  ring_nf

lemma reflectionExcludedPrimes_bad (q:ℕ) :
    fixedBadPrimes⊆reflectionExcludedPrimes q := Finset.subset_union_left

lemma reflectionExcludedPrimes_prime (q:ℕ) (P:Ideal Eis)
    (hP:P∈reflectionExcludedPrimes q) : Prime P := by
  let:P.IsMaximal:=gcdMaskPrimes_maximal _ ⟨P,hP⟩
  exact Ideal.prime_of_isPrime (NeZero.ne P) inferInstance

lemma reflectionConductor_prime_mem (q:ℕ) (hq:q≠0) (P:Ideal Eis)
    (hP:Prime P) (hd:P∣Ideal.span {reflectionConductor q}) :
    P∈reflectionExcludedPrimes q := by
  apply Finset.mem_union_right
  apply Multiset.mem_toFinset.mpr
  apply (Ideal.mem_normalizedFactors_iff (Ideal.span_singleton_eq_bot.not.mpr
    (reflectionConductor_ne_zero q hq))).mpr
  exact ⟨Ideal.isPrime_of_prime hP,Ideal.dvd_iff_le.mp hd⟩

lemma reflectionExcludedGenerator_ne_zero (q:ℕ) :
    excludedGenerator (reflectionExcludedPrimes q)≠0 := by
  apply ConcretePrimeRowBridge.idealGenerator_ne_zero
  exact Finset.prod_ne_zero_iff.mpr (fun P hP=>(reflectionExcludedPrimes_prime q P hP).ne_zero)

lemma reflectionExcludedGenerator_bad (q:ℕ) :
    lambda∣excludedGenerator (reflectionExcludedPrimes q) ∧
      (2:Eis)∣excludedGenerator (reflectionExcludedPrimes q) := by
  constructor
  · apply Ideal.mem_span_singleton.mp
    exact excludedGenerator_mem _ (reflectionExcludedPrimes_bad q (by simp [fixedBadPrimes]))
  · apply Ideal.mem_span_singleton.mp
    exact excludedGenerator_mem _ (reflectionExcludedPrimes_bad q (by simp [fixedBadPrimes]))

lemma reflectionConductor_coprime_of_not_excluded (q:ℕ) (hq:q≠0)
    (P:Ideal Eis) [P.IsMaximal] (hP:P∉reflectionExcludedPrimes q) :
    IsCoprime (Ideal.span {reflectionConductor q}) P := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra ht
  have he:P=Ideal.span {reflectionConductor q}⊔P:=
    (show P.IsMaximal from inferInstance).eq_of_le ht le_sup_right
  exact hP (reflectionConductor_prime_mem q hq P
    (Ideal.prime_of_isPrime (NeZero.ne P) inferInstance)
    (Ideal.dvd_iff_le.mpr (le_sup_left.trans he.symm.le)))

lemma reflectionConductor_coprime_primary (q:ℕ) (hq:q≠0)
    (p:Eis) [(Ideal.span {p}).IsMaximal]
    (hp:Ideal.span {p}∉reflectionExcludedPrimes q) :
    IsCoprime (reflectionConductor q) p :=
  (Ideal.isCoprime_span_singleton_iff _ _).mp
    (reflectionConductor_coprime_of_not_excluded q hq _ hp)

lemma reflectionLevelBound_ge_one (q:ℕ) (hq:q≠0) :
    1≤CubicEisenstein.fixedCuspLevelBound (reflectionConductor q) :=
  CubicEisenstein.fixedCuspLevelBound_ge_one _ (reflectionConductor_ne_zero q hq)

end CanonicalRowCompletion

open scoped BigOperators Classical

namespace CompletedGauss
open ActualEisensteinCubic UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma prime_dvd_rowResidualPart_iff (I Q P:Ideal Eis) (hP:Prime P) :
    P∣rowResidualPart I Q ↔ P∈normalizedFactors (rowSimplePart I) ∧ ¬P∣Q := by
  have hm:=UniqueFactorizationMonoid.mem_normalizedFactors_iff
    (squarefreeResidualPart_ne_zero (rowSimplePart I) Q) (p:=P)
  simp only [hP,true_and] at hm
  change P∣squarefreeResidualPart (rowSimplePart I) Q ↔ _
  rw [←hm]
  simp only [normalizedFactors_squarefreeResidualPart,Multiset.mem_filter]

lemma rowResidualPart_prime_fixed_mask (I Q Q0 P:Ideal Eis)
    (hP:Prime P) (hfree:¬Q0≤P) :
    P∣rowResidualPart I (Q0*Q) ↔ P∣rowResidualPart I Q := by
  have hnd:¬P∣Q0:=by simpa only [Ideal.dvd_iff_le] using hfree
  rw [prime_dvd_rowResidualPart_iff I (Q0*Q) P hP,
    prime_dvd_rowResidualPart_iff I Q P hP,hP.dvd_mul]
  simp only [hnd,false_or]

theorem completedReflectionPool_fixed_mask_filter (I Q Q0:Ideal Eis)
    (hI:I≠0) (hQ:Q≠0) (hQ0:Q0≠0) :
    (completedReflectionPool I (Q0*Q)).filter (fun P=>¬Q0≤P)=
      (completedReflectionPool I Q).filter (fun P=>¬Q0≤P) := by
  ext P
  simp only [Finset.mem_filter,mem_completedReflectionPool I (Q0*Q) P hI (mul_ne_zero hQ0 hQ),
    mem_completedReflectionPool I Q P hI hQ]
  by_cases hP:Prime P
  · by_cases hfree:¬Q0≤P
    · have hnd:¬P∣Q0:=by simpa only [Ideal.dvd_iff_le] using hfree
      have hdiv:P∣I*(Q0*Q) ↔ P∣I*Q:=by
        rw [hP.dvd_mul,hP.dvd_mul,hP.dvd_mul]
        simp only [hnd,false_or]
      rw [hdiv,rowResidualPart_prime_fixed_mask I Q Q0 P hP hfree]
    · simp only [hfree,and_false]
  · simp only [hP,false_and]

end CompletedGauss

namespace CanonicalRowCompletion
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

theorem goodMaskNonresidualPool_full_mask (I F Q0:Ideal Eis)
    (hI:I≠0) (hF:F≠0) (hQ0:Q0≠0)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r) :
    (goodMaskNonresidualPool I F m g r).filter (fun P=>¬Q0≤P)=
      (completedReflectionPool I (Q0*(Ideal.span {m}*F))).filter (fun P=>¬Q0≤P) := by
  rw [completedReflectionPool_fixed_mask_filter I (Ideal.span {m}*F) Q0 hI
    (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm0) hF) hQ0]
  exact goodMaskNonresidualPool_free_eq I F Q0 hI hF m f z hm0 hf hz
    um am bm g hg hm u a b r hr hx

end CanonicalRowCompletion

open scoped BigOperators Classical MatrixGroups Matrix

namespace ShortDraftCusp

section
open ActualEisensteinCubic CubicEisenstein CubicKubota CubicJacobiGlobal ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem A3_ramified_character_of_relative_level (M:SL(2,Eis)) (u q r:Eis)
    (hG:M*(lowerCuspMatrix u)⁻¹∈levelThree)
    (ha:lambda^2∣M 0 0-1) (hr:lambda^2∣r-1) (hC:M 1 0=(u*q)*r) :
    complexCharacter ⟨M*(lowerCuspMatrix u)⁻¹,hG⟩=
      eisEmbedding (symbol (-u) (M 0 0-u*M 0 1)*symbol q (M 0 0))*
        eisEmbedding (symbol (M 0 0) r) := by
  have hA:=levelThree_primary ⟨M*(lowerCuspMatrix u)⁻¹,hG⟩
  change lambda^2∣(((M*(lowerCuspMatrix u)⁻¹:SL(2,Eis)):Matrix (Fin 2) (Fin 2) Eis) 0 0)-1 at hA
  rw [A3_ramified_relative_matrix] at hA
  have hdet:M 0 0*M 1 1-M 0 1*(u*(q*r))=1 := by
    have hd:=M.property
    simp only [Matrix.det_fin_two,hC] at hd
    linear_combination hd
  rw [A3_ramified_literal_character,hC,show (u*q)*r=u*(q*r) by ring,
    A3_ramified_global_factor _ _ _ _ _ _ hdet ha hA hr,map_mul]

theorem A3_unramified_character_of_relative_level (M:SL(2,Eis)) (u c0 r:Eis)
    (hG:M*(A3WeylCusp u)⁻¹∈levelThree)
    (hc:lambda^2∣M 1 0-1) (h9:(9:Eis)∣M 0 0*M 1 1) (hC:M 1 0=c0*r) :
    complexCharacter ⟨M*(A3WeylCusp u)⁻¹,hG⟩=
      eisEmbedding (symbol (M 0 0) c0)*eisEmbedding (symbol (M 0 0) r) := by
  have hb:=levelThree_primary ⟨M*(A3WeylCusp u)⁻¹,hG⟩
  change lambda^2∣(((M*(A3WeylCusp u)⁻¹:SL(2,Eis)):Matrix (Fin 2) (Fin 2) Eis) 0 0)-1 at hb
  rw [A3_unramified_relative_matrix] at hb
  have hdet:M 0 0*M 1 1-M 0 1*(c0*r)=1 := by
    simpa only [Matrix.det_fin_two,hC] using M.property
  rw [hC] at hc
  rw [A3_unramified_literal_character,A3_unramified_global_factor _ _ _ _ _ hdet hb hc h9,map_mul]

end

section
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
open CompletedGauss CubicKubota CubicJacobiGlobal LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance stratumMultiplierField (P:Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance stratumMultiplierFintype (P:Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

theorem stratum_multiplier_of_cubic_factor {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (c0 U w x d0:Eis) (hc0:c0≠0)
    (hbez:U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1)
    (a b d:(∀i,(Eis⧸Ideal.span {p i})ˣ)→Eis)
    (κ:(∀i,(Eis⧸Ideal.span {p i})ˣ)→ℂ) (κ0:ℂ)
    (hκ:∀v,κ v=κ0*eisEmbedding (symbol (a v) (∏i,p i)))
    (hdet:∀v,a v*d v-b v*(c0*∏i,p i)=1)
    (hD:∀v,ramifiedTraceLambda^3*c0∣d v-d0)
    (σ ε:∀i,(Eis⧸Ideal.span {p i})ˣ)
    (hfreq:∀v i,Ideal.Quotient.mk (Ideal.span {p i}) (a v)=
      (σ i:Eis⧸Ideal.span {p i})*(v i:Eis⧸Ideal.span {p i}))
    (hε:∀i,Ideal.Quotient.mk (Ideal.span {p i})
      (ramifiedTraceLambda^3*c0*cofactor p i)*(σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1)
    (j:ι→ℕ) (hj:∀i,j i<6) :
    (∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,
      (∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i))
        (fun t=>(actualSextic (Ideal.span {p i}) (hg i)^j i) t) (v i))*
      star (κ v)*ShortDraftTrace.breveE (-(eisEmbedding (d v)*(eisEmbedding x/eisLam^4))/
        (eisEmbedding c0*eisEmbedding (∏i,p i)))) =
    (star κ0*A4BadPhase c0 hc0 d0 U x)*
    ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (σ i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (ε i)*
      bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i) (Ideal.Quotient.mk _ x) := by
  let C:=star κ0*A4BadPhase c0 hc0 d0 U x
  let f:=fun i (v:(Eis⧸Ideal.span {p i})ˣ)=>frequencyRow
    (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i)
    (σ i) (ε i) (Ideal.Quotient.mk _ x) v
  have hpoint (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
      star (κ v)*ShortDraftTrace.breveE (-(eisEmbedding (d v)*(eisEmbedding x/eisLam^4))/
        (eisEmbedding c0*eisEmbedding (∏i,p i)))=
      C*∏i,frequencyMultiplier (actualSextic (Ideal.span {p i}) (hg i))
        (quotientTrace (p i) (hp i)) (σ i) (ε i) (Ideal.Quotient.mk _ x) (v i) := by
    have hbad:A4BadPhase c0 hc0 (d v) U x=A4BadPhase c0 hc0 d0 U x := by
      apply A4BadPhase_eq_of_residue
      convert dvd_mul_of_dvd_left (hD v) U using 1 ; ring
    have hlocal:=A3_A4_frequency_product p hp hcop hg (a v) (b v) c0 (d v)
      U w x hc0 (hdet v) hbez σ ε (fun i=>(v i:Eis⧸Ideal.span {p i})) (hfreq v) hε
    rw [hκ,star_mul]
    calc
      _=star κ0*(star (eisEmbedding (symbol (a v) (∏i,p i)))*
        ShortDraftTrace.breveE (-(eisEmbedding (d v)*(eisEmbedding x/eisLam^4))/
          (eisEmbedding c0*eisEmbedding (∏i,p i)))) := by ring
      _=_ := by rw [hlocal,hbad];dsimp only [C];ring
  calc
    _=C*∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,∏i,f i (v i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [mul_assoc,hpoint]
      simp only [f,frequencyRow,Finset.prod_mul_distrib]
      ring
    _=C*∏i,∑v:(Eis⧸Ideal.span {p i})ˣ,f i v := by rw [Fintype.prod_sum]
    _=_ := by
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      exact canonical_frequencyRow_units (Ideal.span {p i}) (hg i) (hchar i)
        (quotientTrace (p i) (hp i))
        (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i)) (j i) (hj i) (σ i) (ε i) _

end

open ActualEisensteinCubic CubicEisenstein CubicKubota CubicJacobiGlobal ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma A3_ramified_relative_primary (M:SL(2,Eis)) (u:Eis)
    (hG:M*(lowerCuspMatrix u)⁻¹∈levelThree) :
    lambda^2∣(M 0 0-u*M 0 1)-1 := by
  have hA:=levelThree_primary ⟨M*(lowerCuspMatrix u)⁻¹,hG⟩
  change lambda^2∣(((M*(lowerCuspMatrix u)⁻¹:SL(2,Eis)):Matrix (Fin 2) (Fin 2) Eis) 0 0)-1 at hA
  rw [A3_ramified_relative_matrix] at hA
  exact hA

theorem A3_ramified_fixed_sector_character (M M0:SL(2,Eis)) (N u q r:Eis)
    (hG:M*(lowerCuspMatrix u)⁻¹∈levelThree)
    (hG0:M0*(lowerCuspMatrix u)⁻¹∈levelThree)
    (ha:lambda^2∣M 0 0-1) (ha0:lambda^2∣M0 0 0-1)
    (hr:lambda^2∣r-1) (hC:M 1 0=(u*q)*r)
    (h9N:(9:Eis)∣N) (hqN:q∣N) (huN:u∣N)
    (hA:N∣M 0 0-M0 0 0) (hB:N∣M 0 1-M0 0 1) :
    complexCharacter ⟨M*(lowerCuspMatrix u)⁻¹,hG⟩=
      eisEmbedding (symbol (-u) (M0 0 0-u*M0 0 1)*symbol q (M0 0 0))*
        eisEmbedding (symbol (M 0 0) r) := by
  rw [A3_ramified_character_of_relative_level M u q r hG ha hr hC]
  rw [A3_ramified_fixed_factor_congr N q u (M 0 0) (M0 0 0) (M 0 1) (M0 0 1)
    h9N hqN huN ha ha0 (A3_ramified_relative_primary M u hG)
    (A3_ramified_relative_primary M0 u hG0) hA hB]

theorem A3_unramified_fixed_sector_character (M M0:SL(2,Eis)) (u c0 r:Eis)
    (hG:M*(A3WeylCusp u)⁻¹∈levelThree)
    (hc:lambda^2∣M 1 0-1) (h9:(9:Eis)∣M 0 0*M 1 1) (hC:M 1 0=c0*r)
    (hA:c0∣M 0 0-M0 0 0) :
    complexCharacter ⟨M*(A3WeylCusp u)⁻¹,hG⟩=
      eisEmbedding (symbol (M0 0 0) c0)*eisEmbedding (symbol (M 0 0) r) := by
  rw [A3_unramified_character_of_relative_level M u c0 r hG hc h9 hC,
    symbol_congr hA]

end ShortDraftCusp

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O

structure ControlledStratumArithmetic {ι:Type*} [Fintype ι]
    (p:ι→Eis) (N a0 c0:Eis) (numeratorMode:Bool) where
  lift : (∀i,(Eis⧸Ideal.span {p i})ˣ)→ι→Eis
  lift_period : ∀v i,N^2∣lift v i
  lift_residue : ∀v i,Ideal.Quotient.mk (Ideal.span {p i}) (lift v i)=(v i:Eis⧸Ideal.span {p i})
  U : Eis
  w : Eis
  bezout : U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1
  sigma : ∀i,(Eis⧸Ideal.span {p i})ˣ
  epsilon : ∀i,(Eis⧸Ideal.span {p i})ˣ
  sigma_value : ∀i,(sigma i:Eis⧸Ideal.span {p i})=
    Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^2*c0*cofactor p i)
  epsilon_value : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i)*
    (sigma i:Eis⧸Ideal.span {p i})*(epsilon i:Eis⧸Ideal.span {p i})=-1
  matrix : (∀i,(Eis⧸Ideal.span {p i})ˣ)→SL(2,Eis)
  numerator : ∀v,matrix v 0 0=finiteCrossNumerator a0 c0 ramifiedTraceLambda p (lift v)
  denominator : ∀v,matrix v 1 0=c0*∏i,p i
  matrix_fixed : ∀v i j,N∣matrix v i j-matrix (fun _=>1) i j
  conditions : ∀v,if numeratorMode then
    (9:Eis)∣matrix v 0 1 ∧ (3:Eis)∣matrix v 1 1-1
    else (3:Eis)∣matrix v 0 1+1 ∧ (9:Eis)∣matrix v 1 1

theorem exists_controlledStratumArithmetic {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hprimary:∀i,lambda^2∣p i-1)
    (N a0 c0:Eis) (hc0:c0≠0) (hN:(9:Eis)*c0∣N)
    (mode:Bool) (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (hac:IsCoprime a0 c0) (hNp:∀i,IsCoprime N (p i)) :
    Nonempty (ControlledStratumArithmetic p N a0 c0 mode) := by
  have h9N:(9:Eis)∣N:=(dvd_mul_right 9 c0).trans hN
  have hcN:c0∣N:=(dvd_mul_left c0 9).trans hN
  have hD9:ramifiedTraceLambda^3*c0∣(9:Eis)*c0 := by
    refine ⟨ramifiedTraceLambda,?_⟩
    rw [←A4_traceLambda_pow_four]
    ring
  have hDN:ramifiedTraceLambda^3*c0∣N:=hD9.trans hN
  have hl9:ramifiedTraceLambda∣(9:Eis) := by
    rw [←A4_traceLambda_pow_four]
    exact dvd_pow_self _ (by decide)
  have hlN:ramifiedTraceLambda∣N:=hl9.trans h9N
  have hstdN:lambda^2∣N:=lambda_sq_dvd_three.trans
    ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9N)
  let r:Eis:=∏i,p i
  have hr:lambda^2∣r-1:=primary_finset_product Finset.univ p (fun i _=>hprimary i)
  have hNr:IsCoprime N r:=IsCoprime.prod_right (fun i _=>hNp i)
  have hrNc:IsCoprime r (N*c0):=hNr.symm.mul_right
    (hNr.symm.of_isCoprime_of_dvd_right hcN)
  obtain ⟨U,w,huw⟩:=hNr.symm.of_isCoprime_of_dvd_right hDN
  have hbez:U*r+(ramifiedTraceLambda^3*w)*c0=1 := by linear_combination huw
  obtain ⟨σ,ε,hσ,hε⟩:=exists_A4_local_units p hp hcop c0 U w hbez
  have hlf (v:∀i,(Eis⧸Ideal.span {p i})ˣ):=exists_strong_unit_frequency_lifts N p hNp v
  choose lift hlift hres hlcop using hlf
  let a:=fun v=>finiteCrossNumerator a0 c0 ramifiedTraceLambda p (lift v)
  have hap (ha0:lambda^2∣a0-1):∀v,lambda^2∣a v-1 := by
    intro v
    have hfixed:N∣a v-a0*r:=finiteCrossNumerator_fixed N a0 c0 ramifiedTraceLambda p (lift v)
      (fun i=>(dvd_pow_self N (by decide : (2:ℕ)≠0)).trans (hlift v i))
    have hbas:=primary_mul a0 r ha0 hr
    convert dvd_add (hstdN.trans hfixed) hbas using 1 ; ring
  have hpairs:Pairwise (Function.onFun IsCoprime p):=by
    intro i k hik
    exact (Ideal.isCoprime_span_singleton_iff _ _).mp (hcop hik)
  have hacop:∀v,IsCoprime (a v) (c0*r) := by
    intro v
    exact finiteCrossNumerator_coprime a0 c0 ramifiedTraceLambda p (lift v) hac hpairs
      (fun i=>(hNp i).of_isCoprime_of_dvd_left hcN)
      (fun i=>(hNp i).of_isCoprime_of_dvd_left hlN) (hlcop v)
  have hfixed:∀v z,(fun (_:∀i,(Eis⧸Ideal.span {p i})ˣ)=>()) v=()→N*c0∣a v-a z := by
    intro v z _
    exact finiteCrossNumerator_fixed_sector N a0 c0 ramifiedTraceLambda p (lift v)
      p (lift z) hcN (hlift v) (hlift z) (by simp)
  have hcompletes:∃(b d:(∀i,(Eis⧸Ideal.span {p i})ˣ)→Eis)
      (C:Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {N})),
      (∀v,a v*d v-b v*(c0*r)=1) ∧
      (∀v,if mode then (9:Eis)∣b v ∧ (3:Eis)∣d v-1 else (3:Eis)∣b v+1 ∧ (9:Eis)∣d v) ∧
      ∀v,(!![a v,b v;c0*r,d v]:Matrix (Fin 2) (Fin 2) Eis).map (Ideal.Quotient.mk (Ideal.span {N}))=C := by
    cases mode
    · obtain ⟨b,d,C,hd,hb,hz,hm⟩:=exists_primary_denominator_sector_completions N c0 h9N hbase
        (fun (_:∀i,(Eis⧸Ideal.span {p i})ˣ)=>()) a (fun _=>r)
        (fun _=>hr) hacop (fun _=>hrNc) (fun v z _=>hfixed v z rfl) (fun _ _ _=>by simp)
      exact ⟨b,d,C (),hd,fun v=>⟨hb v,hz v⟩,hm⟩
    · obtain ⟨b,d,C,hd,hb,hz,hm⟩:=exists_primary_numerator_sector_completions N c0 hc0 h9N
        (fun (_:∀i,(Eis⧸Ideal.span {p i})ˣ)=>()) a (fun _=>r)
        (hap hbase) (fun _=>hr) hacop (fun _=>hrNc)
        (fun v z _=>hfixed v z rfl) (fun _ _ _=>by simp)
      exact ⟨b,d,C (),hd,fun v=>⟨hb v,hz v⟩,hm⟩
  obtain ⟨b,d,C,hdet,hconditions,hmat⟩:=hcompletes
  let mat:=fun v=>controlledCompletionMatrix (a v) (b v) (c0*r) (d v) (hdet v)
  have hentry (v:∀i,(Eis⧸Ideal.span {p i})ˣ) (i j:Fin 2):
      N∣(mat v) i j-(mat (fun _=>1)) i j := by
    have he:=congrArg (fun T:Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {N})=>T i j)
      ((hmat v).trans (hmat (fun _=>1)).symm)
    change Ideal.Quotient.mk (Ideal.span {N}) ((mat v) i j)=
      Ideal.Quotient.mk (Ideal.span {N}) ((mat (fun _=>1)) i j) at he
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  exact ⟨{
    lift := lift
    lift_period := hlift
    lift_residue := hres
    U := U
    w := w
    bezout := hbez
    sigma := σ
    epsilon := ε
    sigma_value := hσ
    epsilon_value := hε
    matrix := mat
    numerator := fun _=>rfl
    denominator := fun _=>rfl
    matrix_fixed := hentry
    conditions := hconditions
  }⟩

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}

lemma frequency_congruence (D:ControlledStratumArithmetic p N a0 c0 mode)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) (i:ι) :
    Ideal.Quotient.mk (Ideal.span {p i}) (D.matrix v 0 0)=
      (D.sigma i:Eis⧸Ideal.span {p i})*(v i:Eis⧸Ideal.span {p i}) := by
  rw [D.numerator,finiteCrossNumerator_local,D.sigma_value,D.lift_residue]

lemma numerator_congruence (D:ControlledStratumArithmetic p N a0 c0 mode)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    N∣D.matrix v 0 0-a0*∏i,p i := by
  rw [D.numerator]
  exact finiteCrossNumerator_fixed N a0 c0 ramifiedTraceLambda p (D.lift v)
    (fun i=>(dvd_pow_self N (by decide : (2:ℕ)≠0)).trans (D.lift_period v i))

lemma numerator_mod_three (D:ControlledStratumArithmetic p N a0 c0 mode)
    (h3N:(3:Eis)∣N) (hr:lambda^2∣(∏i,p i)-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : (3:Eis)∣D.matrix v 0 0-a0 := by
  have hprod:=three_dvd_primary_sub_one (∏i,p i) hr
  convert dvd_add (h3N.trans (D.numerator_congruence v))
    (dvd_mul_of_dvd_right hprod a0) using 1 ; ring

lemma numerator_primary (D:ControlledStratumArithmetic p N a0 c0 mode)
    (h3N:(3:Eis)∣N) (hr:lambda^2∣(∏i,p i)-1) (ha:lambda^2∣a0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : lambda^2∣D.matrix v 0 0-1 := by
  convert dvd_add (lambda_sq_dvd_three.trans (D.numerator_mod_three h3N hr v)) ha using 1 ; ring

lemma denominator_primary (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hr:lambda^2∣(∏i,p i)-1) (hc:lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : lambda^2∣D.matrix v 1 0-1 := by
  rw [D.denominator]
  exact primary_mul c0 (∏i,p i) hc hr

lemma ramified_relative (D:ControlledStratumArithmetic p N a0 c0 true)
    (h3N:(3:Eis)∣N) (hr:lambda^2∣(∏i,p i)-1) (ha:lambda^2∣a0-1)
    (u:Eis) (hcu:(3:Eis)∣c0-u) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    D.matrix v*(lowerCuspMatrix u)⁻¹∈levelThree := by
  have hcond := D.conditions v
  simp only [ ↓reduceIte] at hcond
  apply A3_ramified_mem_levelThree
  · exact three_dvd_primary_sub_one _ (D.numerator_primary h3N hr ha v)
  · exact (show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans hcond.1
  · rw [D.denominator]
    have hprod:=three_dvd_primary_sub_one (∏i,p i) hr
    convert dvd_add (dvd_mul_of_dvd_right hprod c0) hcu using 1 ; ring
  · exact hcond.2

lemma unramified_relative (D:ControlledStratumArithmetic p N a0 c0 false)
    (h3N:(3:Eis)∣N) (hr:lambda^2∣(∏i,p i)-1) (hc:lambda^2∣c0-1)
    (u:Eis) (hau:(3:Eis)∣a0-u) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    D.matrix v*(A3WeylCusp u)⁻¹∈levelThree := by
  have hcond := D.conditions v
  simp only [Bool.false_eq_true, ↓reduceIte] at hcond
  apply A3_unramified_mem_levelThree
  · convert dvd_add (D.numerator_mod_three h3N hr v) hau using 1 ; ring
  · exact hcond.1
  · exact three_dvd_primary_sub_one _ (D.denominator_primary hr hc v)
  · exact (show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans hcond.2

lemma inverse_fixed (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    ramifiedTraceLambda^3*c0∣D.matrix v 1 1-D.matrix (fun _=>1) 1 1 := by
  have hD9:ramifiedTraceLambda^3*c0∣(9:Eis)*c0 := by
    refine ⟨ramifiedTraceLambda,?_⟩
    rw [←A4_traceLambda_pow_four]
    ring
  exact (hD9.trans hN).trans (D.matrix_fixed v 1 1)

lemma determinant (D:ControlledStratumArithmetic p N a0 c0 mode)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    D.matrix v 0 0*D.matrix v 1 1-D.matrix v 0 1*(c0*∏i,p i)=1 := by
  simpa only [Matrix.det_fin_two,D.denominator] using (D.matrix v).property

def ramifiedFixedFactor (D:ControlledStratumArithmetic p N a0 c0 true) (u q:Eis) : ℂ :=
  eisEmbedding (symbol (-u) (D.matrix (fun _=>1) 0 0-u*D.matrix (fun _=>1) 0 1)*
    symbol q (D.matrix (fun _=>1) 0 0))

def unramifiedFixedFactor (D:ControlledStratumArithmetic p N a0 c0 false) : ℂ :=
  eisEmbedding (symbol (D.matrix (fun _=>1) 0 0) c0)

theorem ramified_character (D:ControlledStratumArithmetic p N a0 c0 true)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1) (ha:lambda^2∣a0-1)
    (u q:Eis) (hc0:c0=u*q) (hcu:(3:Eis)∣c0-u)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    complexCharacter ⟨D.matrix v*(lowerCuspMatrix u)⁻¹,
      D.ramified_relative ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans
        ((dvd_mul_right 9 c0).trans hN)) hr ha u hcu v⟩=
      D.ramifiedFixedFactor u q*eisEmbedding (symbol (D.matrix v 0 0) (∏i,p i)) := by
  have h9N:(9:Eis)∣N:=(dvd_mul_right 9 c0).trans hN
  have h3N:(3:Eis)∣N:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9N
  have hcN:c0∣N:=(dvd_mul_left c0 9).trans hN
  exact A3_ramified_fixed_sector_character (D.matrix v) (D.matrix (fun _=>1)) N u q (∏i,p i)
    (D.ramified_relative h3N hr ha u hcu v) (D.ramified_relative h3N hr ha u hcu (fun _=>1))
    (D.numerator_primary h3N hr ha v) (D.numerator_primary h3N hr ha (fun _=>1)) hr
    (by rw [D.denominator,hc0]) h9N
    ((hc0 ▸ dvd_mul_left q u).trans hcN) ((hc0 ▸ dvd_mul_right u q).trans hcN)
    (D.matrix_fixed v 0 0) (D.matrix_fixed v 0 1)

theorem unramified_character (D:ControlledStratumArithmetic p N a0 c0 false)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1) (hc:lambda^2∣c0-1)
    (u:Eis) (hau:(3:Eis)∣a0-u) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    complexCharacter ⟨D.matrix v*(A3WeylCusp u)⁻¹,
      D.unramified_relative ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans
        ((dvd_mul_right 9 c0).trans hN)) hr hc u hau v⟩=
      D.unramifiedFixedFactor*eisEmbedding (symbol (D.matrix v 0 0) (∏i,p i)) := by
  have h9N:(9:Eis)∣N:=(dvd_mul_right 9 c0).trans hN
  have h3N:(3:Eis)∣N:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9N
  have hcond:=D.conditions v
  simp only [Bool.false_eq_true, ↓reduceIte] at hcond
  exact A3_unramified_fixed_sector_character (D.matrix v) (D.matrix (fun _=>1)) u c0 (∏i,p i)
    (D.unramified_relative h3N hr hc u hau v) (D.denominator_primary hr hc v)
    (dvd_mul_of_dvd_right hcond.2 _) (D.denominator v)
    (((dvd_mul_left c0 9).trans hN).trans (D.matrix_fixed v 0 0))

end ControlledStratumArithmetic
end CubicEisenstein

end

end OAI
end OAIOriginalModule0324

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.FixedFrequencyExpansion
Source SHA256: 147b6a869c1a68f126f68b8430b9446d7bccd34402ef2deb51d6352f3b0f200a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0325


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

section
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}

def fixedCusp (a0 c0:Eis) (mode:Bool) : SL(2,Eis) :=
  if mode then lowerCuspMatrix c0 else A3WeylCusp a0

lemma relative (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    D.matrix v*(fixedCusp a0 c0 mode)⁻¹∈levelThree := by
  have h3N:(3:Eis)∣N:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans
    ((dvd_mul_right 9 c0).trans hN)
  cases mode
  · exact D.unramified_relative h3N hr hbase a0 (by simp) v
  · exact D.ramified_relative h3N hr hbase c0 (by simp) v

def relativeGamma (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : levelThree :=
  ⟨D.matrix v*(fixedCusp a0 c0 mode)⁻¹,D.relative hN hr hbase v⟩

lemma relativeGamma_mul (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    (D.relativeGamma hN hr hbase v:SL(2,Eis))*fixedCusp a0 c0 mode=D.matrix v := by
  exact inv_mul_cancel_right (D.matrix v) (fixedCusp a0 c0 mode)

def fixedFactor (D:ControlledStratumArithmetic p N a0 c0 mode) : ℂ :=
  if mode then
    eisEmbedding (symbol (-c0) (D.matrix (fun _=>1) 0 0-c0*D.matrix (fun _=>1) 0 1)*
      symbol 1 (D.matrix (fun _=>1) 0 0))
  else eisEmbedding (symbol (D.matrix (fun _=>1) 0 0) c0)

theorem relative_character (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    complexCharacter (D.relativeGamma hN hr hbase v)=
      D.fixedFactor*eisEmbedding (symbol (D.matrix v 0 0) (∏i,p i)) := by
  cases mode
  · simpa only [relativeGamma,fixedCusp,fixedFactor,Bool.false_eq_true,↓reduceIte,
      unramifiedFixedFactor] using D.unramified_character hN hr hbase a0 (by simp) v
  · simpa only [relativeGamma,fixedCusp,fixedFactor,Bool.true_eq,↓reduceIte,
      ramifiedFixedFactor] using D.ramified_character hN hr hbase c0 1 (by simp) (by simp) v

theorem fixedFactor_norm (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1) : ‖D.fixedFactor‖=1 := by
  have h3N:(3:Eis)∣N:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans
    ((dvd_mul_right 9 c0).trans hN)
  cases mode
  · exact norm_A3_unramified_fixed_factor _ _ _ _ _ (D.determinant (fun _=>1)) hbase
  · apply norm_A3_ramified_fixed_factor _ _ 1 (∏i,p i) _ c0
    · simpa only [one_mul] using D.determinant (fun _=>1)
    · exact D.numerator_primary h3N hr hbase (fun _=>1)
    · exact A3_ramified_relative_primary (D.matrix (fun _=>1)) c0
        (D.ramified_relative h3N hr hbase c0 (by simp) (fun _=>1))

noncomputable def fourierWeight [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : ℂ := by
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i))
    (fun t=>(actualSextic (Ideal.span {p i}) (hg i)^j i) t) (v i)

noncomputable def multiplierSum (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (x:Eis) : ℂ := by
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,
    fourierWeight hp hg j v*star (complexCharacter (D.relativeGamma hN hr hbase v))*
      ShortDraftTrace.breveE (-(eisEmbedding (D.matrix v 1 1)*(eisEmbedding x/eisLam^4))/
        (eisEmbedding c0*eisEmbedding (∏i,p i)))

noncomputable def bracketProduct (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (x:Eis) : ℂ := by
  letI (i:ι):Field (Eis⧸Ideal.span {p i}):=Ideal.Quotient.field _
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
    phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i)*
    bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i) (Ideal.Quotient.mk _ x)

theorem multiplierSum_eq (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (hp:∀i,p i≠0) (hc0:c0≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (j:ι→ℕ) (hj:∀i,j i<6) (x:Eis) :
    D.multiplierSum hN hr hbase hp hg j x=
      (star D.fixedFactor*A4BadPhase c0 hc0 (D.matrix (fun _=>1) 1 1) D.U x)*
        D.bracketProduct hp hg j x := by
  exact stratum_multiplier_of_cubic_factor p hp hcop hg hchar c0 D.U D.w x
    (D.matrix (fun _=>1) 1 1) hc0 D.bezout
    (fun v=>D.matrix v 0 0) (fun v=>D.matrix v 0 1) (fun v=>D.matrix v 1 1)
    (fun v=>complexCharacter (D.relativeGamma hN hr hbase v)) D.fixedFactor
    (D.relative_character hN hr hbase) D.determinant (D.inverse_fixed hN)
    D.sigma D.epsilon D.frequency_congruence D.epsilon_value j hj

end ControlledStratumArithmetic
end

section
open scoped BigOperators Classical ContDiff MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CompletedDyadic CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}

def sourceGamma (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : levelTwo :=
  sourceLevelInclusion (D.relativeGamma hN hr hbase v)

lemma sourceGamma_mul (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    (D.sourceGamma hN hr hbase v:SL(2,Eis))*fixedCusp a0 c0 mode=D.matrix v :=
  D.relativeGamma_mul hN hr hbase v

lemma sourceGamma_character (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    levelTwoComplexCharacter (D.sourceGamma hN hr hbase v)=
      complexCharacter (D.relativeGamma hN hr hbase v) :=
  sourceLevelInclusion_character _

def datum (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : SourceCuspDatum :=
  s.datum (D.sourceGamma hN hr hbase v) (by
    rw [D.sourceGamma_mul,D.denominator]
    exact mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))

lemma datum_point (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    (D.datum hN hr hbase s hp hc0 v).point=eisEmbedding a0/eisEmbedding c0+
      eisLam^2*∑i,eisEmbedding (D.lift v i)/eisEmbedding (p i) := by
  rw [datum,s.datum_point,D.sourceGamma_mul,D.numerator,D.denominator]
  simpa only [ramifiedEmbedding_traceLambda] using
    finiteCrossNumerator_fraction a0 c0 ramifiedTraceLambda p (D.lift v) hc0 hp

noncomputable def smoothedValue (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,fourierWeight hp hg j v*
    (D.datum hN hr hbase s hp hc0 v).smoothedKernel W X

noncomputable def reflectedValue (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) : ℂ :=
  fixedRadialCoefficientScalar*s.stratumShapeFactor (c0*∏i,p i)*
    ∑'t:ThetaFullIndex,
      (s.amplitude t.1 t.2.1 t.2.2.1.val t.2.2.2.val /
        ((ramifiedScale 1 completedRamifiedStep t.2.1*
          Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ))*
      CubicReflectionKernel.paperKernel (Vstar W)
        ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c0*∏i,p i}):ℝ)^2))*
          (ramifiedScale 1 completedRamifiedStep t.2.1)^3*
          (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ)^3)*
      ((star D.fixedFactor*A4BadPhase c0 hc0 (D.matrix (fun _=>1) 1 1) D.U
        (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t)))*
          D.bracketProduct hp hg j
            (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t)))

theorem smoothed_eq_reflected (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (j:ι→ℕ) (hj:∀i,j i<6)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    D.smoothedValue hN hr hbase s hp hc0 hg j W X=D.reflectedValue s hp hc0 hg j W X := by
  let (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  have hc:c0*(∏i,p i)≠0:=mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
  have hC:∀v,((D.sourceGamma hN hr hbase v:SL(2,Eis))*fixedCusp a0 c0 mode) 1 0=c0*∏i,p i := by
    intro v
    rw [D.sourceGamma_mul,D.denominator]
  have he:=s.sum_smoothedKernel_integral_phase (D.sourceGamma hN hr hbase) _ hc hC
    (fourierWeight hp hg j) W lo hi hlo hsupp hW X hX
  change D.smoothedValue hN hr hbase s hp hc0 hg j W X=_ at he
  rw [he]
  unfold reflectedValue
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*s.stratumShapeFactor (c0*∏i,p i)*z)
  apply tsum_congr
  intro t
  apply congrArg (fun z:ℂ=>
    (s.amplitude t.1 t.2.1 t.2.2.1.val t.2.2.2.val /
      ((ramifiedScale 1 completedRamifiedStep t.2.1*
        Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ))*
      CubicReflectionKernel.paperKernel (Vstar W)
        ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c0*∏i,p i}):ℝ)^2))*
          (ramifiedScale 1 completedRamifiedStep t.2.1)^3*
          (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ)^3)*z)
  simpa only [multiplierSum,D.sourceGamma_character,D.sourceGamma_mul,map_mul] using
    D.multiplierSum_eq hN hr hbase hp hc0 hcop hg hchar j hj
      (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t))

end ControlledStratumArithmetic

theorem exists_constructed_stratum_reflection {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hprimary:∀i,lambda^2∣p i-1)
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (N a0 c0:Eis) (hc0:c0≠0) (hN:(9:Eis)*c0∣N)
    (mode:Bool) (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (hac:IsCoprime a0 c0) (hNp:∀i,IsCoprime N (p i)) :
    ∃s:FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode),
      ∃D:ControlledStratumArithmetic p N a0 c0 mode,
      ∀j:ι→ℕ,(∀i,j i<6)→∀(W:ℝ→ℂ)(lo hi:ℝ),0<lo→
        Function.support W⊆Set.Icc lo hi→ContDiff ℝ ∞ W→∀X:ℝ,0<X→
        D.smoothedValue hN (primary_finset_product Finset.univ p (fun i _=>hprimary i))
          hbase s hp hc0 hg j W X=D.reflectedValue s hp hc0 hg j W X := by
  obtain ⟨s⟩:=exists_fixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode)
  obtain ⟨D⟩:=exists_controlledStratumArithmetic p hp hcop hprimary N a0 c0 hc0 hN mode hbase hac hNp
  refine ⟨s,D,?_⟩
  intro j hj W lo hi hlo hsupp hW X hX
  exact D.smoothed_eq_reflected hN _ hbase s hp hc0 hcop hg hchar j hj W lo hi hlo hsupp hW X hX

end

section
open scoped Classical BigOperators MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ShortDraftCusp
local notation "Eis" => ActualEisensteinCubic.O

structure FixedFourierGeometry (c:Eis) (h:Eis⧸Ideal.span {c}) where
  a0 : Eis
  c0 : Eis
  denominator_ne_zero : c0≠0
  denominator_dvd : c0∣c
  coprime : IsCoprime a0 c0
  point : eisEmbedding a0/eisEmbedding c0=thetaFourierTranslation c h
  mode : Bool
  primary : if mode then lambda^2∣a0-1 else lambda^2∣c0-1
  shape : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode)

lemma exists_fixedFourierGeometry (c:Eis) (hc:c≠0) (h:Eis⧸Ideal.span {c}) :
    Nonempty (FixedFourierGeometry c h) := by
  obtain ⟨a0,c0,hc0,hdiv,hcop,hpoint,ha,hcp⟩:=
    ShortDraftCRT.exists_normalized_rational_cusp (-3*Quotient.out h) c hc
  have hp:eisEmbedding a0/eisEmbedding c0=thetaFourierTranslation c h := by
    rw [hpoint,thetaFourierTranslation,TraceLambdaPhase.eisLam_sq]
    simp only [map_mul,map_neg,map_ofNat]
  by_cases hl:lambda∣c0
  · obtain ⟨s⟩:=exists_fixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 true)
    exact ⟨⟨a0,c0,hc0,hdiv,hcop,hp,true,ha hl,s⟩⟩
  · obtain ⟨s⟩:=exists_fixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 false)
    exact ⟨⟨a0,c0,hc0,hdiv,hcop,hp,false,hcp hl,s⟩⟩

def fixedFourierGeometry (c:Eis) (hc:c≠0) (h:Eis⧸Ideal.span {c}) :
    FixedFourierGeometry c h := Classical.choice (exists_fixedFourierGeometry c hc h)

namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)

abbrev PhaseResidue := Eis⧸Ideal.span {ramifiedTraceLambda^3*G.c0}

instance phaseResidue_finite : Finite G.PhaseResidue :=
  finite_quotient_span (A4_bad_modulus_ne_zero G.c0 G.denominator_ne_zero)

def levelScale : ℝ := fixedCuspLevelScale G.shape.index G.c0

lemma levelScale_pos : 0<G.levelScale :=
  fixedCuspLevelScale_pos G.shape.index G.c0 G.denominator_ne_zero

lemma levelScale_le (hc:c≠0) : G.levelScale≤fixedCuspLevelBound c :=
  fixedCuspLevelScale_le G.shape.index G.c0 c hc G.denominator_dvd

def dualNumerator (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : Eis :=
  sourceCuspPhaseNumerator G.shape.index (G.shape.upper 0 0)
    (fixedCuspArrayIndex u m I J)

def staticPhase (v:G.PhaseResidue) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  G.shape.reflectionStaticPhase G.c0 G.denominator_ne_zero v (G.dualNumerator u) u m I J

lemma staticPhase_norm_le_one (v:G.PhaseResidue) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    ‖G.staticPhase v u m I J‖≤1 :=
  G.shape.reflectionStaticPhase_norm_le_one G.c0 G.denominator_ne_zero v _ u m I J

def array (v:G.PhaseResidue) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  fixedCuspArrayWithPhase G.shape.index u (G.staticPhase v u) m I J

lemma array_norm_le_one (v:G.PhaseResidue) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    ‖G.array v u m I J‖≤1 :=
  fixedCuspArrayWithPhase_norm_le_one G.shape.index u _ (G.staticPhase_norm_le_one v u) m I J

lemma array_eq (v:G.PhaseResidue) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    G.array v u m I J=G.shape.amplitude u m I J*
      A4PhaseFromResidue G.c0 G.denominator_ne_zero v (G.dualNumerator u m I J) :=
  G.shape.fixedCuspArrayWithPhase_reflectionStaticPhase G.c0 G.denominator_ne_zero v _ u m I J

end FixedFourierGeometry

def FixedReflectionRay (c:Eis) (hc:c≠0) :=
  Σh:Eis⧸Ideal.span {c},(fixedFourierGeometry c hc h).PhaseResidue×Eisˣ

instance fixedReflectionRay_finite (c:Eis) (hc:c≠0) : Finite (FixedReflectionRay c hc) := by
  let:Finite (Eis⧸Ideal.span {c}):=finite_quotient_span hc
  let:Finite Eisˣ:=PrimaryIdealUnitReindex.finite_units
  unfold FixedReflectionRay
  infer_instance

noncomputable instance fixedReflectionRay_fintype (c:Eis) (hc:c≠0) :
    Fintype (FixedReflectionRay c hc) := Fintype.ofFinite _

def fixedReflectionRayCount (c:Eis) (hc:c≠0) : ℕ := Fintype.card (FixedReflectionRay c hc)

def fixedReflectionRayEquiv (c:Eis) (hc:c≠0) :
    FixedReflectionRay c hc≃Fin (fixedReflectionRayCount c hc) := Fintype.equivFin _

lemma fixedReflectionRayCount_subpower (c:Eis) (hc:c≠0) (z:ℂ) (κ:ℝ) (hκ:0≤κ) :
    ∃C:ℝ,0≤C ∧ ∀Z:ℝ,1≤Z→
      (fixedReflectionRayCount c hc:ℝ)^2*‖z‖^2≤C*Z^κ := by
  refine ⟨(fixedReflectionRayCount c hc:ℝ)^2*‖z‖^2,by positivity,?_⟩
  intro Z hZ
  have hz:1≤Z^κ:=Real.one_le_rpow hZ hκ
  exact le_mul_of_one_le_right (by positivity) hz

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem completedT_of_finite_cusp_profiles
    (Ψ:Eis→*ℂ) (hΨ:∀x,‖Ψ x‖≤1)
    (Q:Ideal Eis) (hperiod:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    {ι:Type*} [Fintype ι] (d:ι→SourceCuspDatum) (w:ι→ℂ)
    (hFG:∀v:ℝ,0<v→completedBesselProfile Ψ thetaBesselScale v=
      ∑i,w i*cuspBarProfile cubicSourceConjugateFunction (d i).point v)
    (W:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hWs:Function.support W⊆Set.Icc v0 v1) (hW:ContDiff ℝ ∞ W)
    (X:ℝ) (hX:0<X) :
    completedT Ψ W X=∑i,w i*(d i).smoothedKernel W X := by
  let : Countable Eis := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let G:ι→ℝ→ℂ:=fun h=>
    cuspBarProfile cubicSourceConjugateFunction (d h).point
  have hG (h:ι) : ∀s:ℂ,MellinConvergent (G h) s:=
    (d h).cuspBarProfile_mellin_entire.1
  have hF:=completedBesselProfile_mellin_entire_of_periodic Ψ Q hperiod c hc hcQ
  have hVs:=Vstar_support W v0 v1 hWs
  have hV:=Vstar_contDiff W v0 v1 hv0 hWs hW
  let J:ι→ℝ→ℂ:=fun h t=>
    besselSmoothingIntegrand (G h) thetaBesselScale (Vstar W) X ((-1:ℂ)+t*Complex.I)
  have hi (h:ι) : Integrable (J h):=
    besselSmoothingIntegrand_reflected_integrable (G h) sourceCuspRadialLength
      sourceCuspRadialLength_pos (sourceCuspRadialCoefficient (d h).index (d h).dualPoint)
      thetaBesselScale (sourceCuspRadialScale (d h).index) (d h).heightScale
      thetaBesselScale_pos (sourceCuspRadialScale_pos _) (d h).heightScale_pos
      (d h).multiplier (d h).reflection_radial
      (sourceCuspRadialCoefficient_weighted_summable _ _) (Vstar W) v0 v1 hv0 hVs hV X hX
  have hireal (h:ι) : Integrable (fun t:ℝ=>
      besselSmoothingIntegrand (G h) thetaBesselScale (Vstar W) X (((-1:ℝ):ℂ)+t*Complex.I)):=by
    simpa only [Complex.ofReal_neg,Complex.ofReal_one,J] using hi h
  have hleft:=besselSmoothingIntegrand_finite_integrable
    (completedBesselProfile Ψ thetaBesselScale) G w hFG thetaBesselScale (Vstar W) X (-1)
    (fun h t=>hG h _) hireal
  have hshift:=completedT_mellin_shift Ψ hΨ thetaBesselScale thetaBesselScale_pos hF.1 hF.2
    W v0 v1 hv0 hWs hW X hX (-1) (by norm_num) hleft
  have hline (h:ι) : (1/(2*Real.pi):ℂ)*(∫t:ℝ,J h t)=(d h).smoothedKernel W X:=by
    exact besselSmoothingIntegral_reflected_kernel (G h) sourceCuspRadialLength
      sourceCuspRadialLength_pos (sourceCuspRadialCoefficient (d h).index (d h).dualPoint)
      thetaBesselScale (sourceCuspRadialScale (d h).index) (d h).heightScale
      thetaBesselScale_pos (sourceCuspRadialScale_pos _) (d h).heightScale_pos
      (d h).multiplier (d h).reflection_radial
      (sourceCuspRadialCoefficient_weighted_summable _ _) (Vstar W) v0 v1 hv0 hVs hV X hX
  calc
    _=(1/(2*Real.pi):ℂ)*∫t:ℝ,
        besselSmoothingIntegrand (completedBesselProfile Ψ thetaBesselScale)
          thetaBesselScale (Vstar W) X ((-1:ℂ)+t*Complex.I):=by
      simpa only [Complex.ofReal_neg,Complex.ofReal_one] using hshift
    _=(1/(2*Real.pi):ℂ)*∫t:ℝ,∑h,w h*J h t:=by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      exact besselSmoothingIntegrand_finite_sum
        (completedBesselProfile Ψ thetaBesselScale) G w hFG thetaBesselScale (Vstar W) X _
        (fun h=>hG h _)
    _=∑h,w h*((1/(2*Real.pi):ℂ)*∫t:ℝ,J h t):=by
      rw [integral_finsetSum Finset.univ (fun h _=>(hi h).const_mul (w h)),Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [integral_const_mul]
      ring
    _=∑h,w h*(d h).smoothedKernel W X:=by simp_rw [hline]

end CubicEisenstein

open scoped BigOperators Classical

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss
open CubicEisenstein hiding summand
local notation "Eis" => ActualEisensteinCubic.O

def fixedRowFourierPhase (c:Eis) (hc:c≠0) (h:Eis⧸Ideal.span {c}) (n:Eis) : ℂ :=
  quotientTrace c hc (h*Ideal.Quotient.mk _ n)

def fixedRowFourierCoeff (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ:Eis→*ℂ) (h:Eis⧸Ideal.span {c}) : ℂ :=
  finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedQuotientValue (Ideal.span {c}) φ) h

lemma fixedRowFourierCoeff_norm (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ:Eis→*ℂ) (hφ:∀n,‖φ n‖≤1) (h:Eis⧸Ideal.span {c}) :
    ‖fixedRowFourierCoeff c hc φ h‖≤1 :=
  finiteAdditiveFourierCoeff_norm _ _ (fixedQuotientValue_norm _ φ hφ) h

lemma fixedRowFourierCoeff_mass (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ:Eis→*ℂ) (hφ:∀n,‖φ n‖≤1) :
    (∑h:Eis⧸Ideal.span {c},‖fixedRowFourierCoeff c hc φ h‖)≤
      (Fintype.card (Eis⧸Ideal.span {c}):ℝ) := by
  calc
    _≤∑_h:Eis⧸Ideal.span {c},(1:ℝ):=
      Finset.sum_le_sum (fun h _=>fixedRowFourierCoeff_norm c hc φ hφ h)
    _=_:=by simp

lemma fixedRowFourierPhase_norm (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})] (h:Eis⧸Ideal.span {c}) (n:Eis) :
    ‖fixedRowFourierPhase c hc h n‖=1 := AddChar.norm_apply _ _

lemma fixedRowFourierPhase_translation (c:Eis) (hc:c≠0) (h:Eis⧸Ideal.span {c}) (n:Eis) :
    fixedRowFourierPhase c hc h n=
      ShortDraftTrace.breveE (-cuspFrequency n*thetaFourierTranslation c h) :=
  (thetaFourierTranslation_phase c hc h n).symm

lemma fixedRowFourier_inversion (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo (Ideal.span {c}) φ) (n:Eis) :
    (∑h:Eis⧸Ideal.span {c},fixedRowFourierCoeff c hc φ h*fixedRowFourierPhase c hc h n)=φ n := by
  rw [show (∑h:Eis⧸Ideal.span {c},fixedRowFourierCoeff c hc φ h*fixedRowFourierPhase c hc h n)=
      fixedQuotientValue (Ideal.span {c}) φ (Ideal.Quotient.mk _ n) from
    finiteAdditiveFourier_inversion (quotientTrace c hc)
      (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc)
      (fixedQuotientValue (Ideal.span {c}) φ) _]
  exact fixedQuotientValue_mk _ φ hφ n

lemma summand_mul_fixed_twist (φ χ:Eis→*ℂ) (W:ℝ→ℂ) (X:ℝ) (I J:Ideal Eis) :
    summand (φ*χ) W X I J=
      φ (primaryGenerator I*(primaryGenerator J)^3)*summand χ W X I J := by
  have he (η:Eis→*ℂ) : cubeWeight η J=
      star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3*
        η (primaryGenerator J)^3/(Ideal.absNorm J:ℂ):=rfl
  rw [summand,summand,he,he]
  simp only [columnWeight,MonoidHom.mul_apply,map_mul,map_pow,mul_pow]
  ring

def completedFixedFrequency (χ:Eis→*ℂ) (c:Eis) (hc:c≠0)
    (h:Eis⧸Ideal.span {c}) (W:ℝ→ℂ) (X:ℝ) : ℂ :=
  ∑'p:Ideal Eis×Ideal Eis,summand χ W X p.1 p.2*
    fixedRowFourierPhase c hc h (primaryGenerator p.1*(primaryGenerator p.2)^3)

lemma completedFixedFrequency_summable (χ:Eis→*ℂ) (c:Eis) (hc:c≠0)
    (h:Eis⧸Ideal.span {c}) (W:ℝ→ℂ) (hW:HasCompactSupport W) (X:ℝ) (hX:0<X) :
    Summable (fun p:Ideal Eis×Ideal Eis=>summand χ W X p.1 p.2*
      fixedRowFourierPhase c hc h (primaryGenerator p.1*(primaryGenerator p.2)^3)) := by
  apply summable_of_hasFiniteSupport
  apply (completedT_finite_support χ W hW X hX).subset
  intro p hp
  exact left_ne_zero_of_mul hp

theorem completedT_fixed_fourier (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ χ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo (Ideal.span {c}) φ)
    (W:ℝ→ℂ) (hW:HasCompactSupport W) (X:ℝ) (hX:0<X) :
    completedT (φ*χ) W X=
      ∑h:Eis⧸Ideal.span {c},fixedRowFourierCoeff c hc φ h*completedFixedFrequency χ c hc h W X := by
  have hp (p:Ideal Eis×Ideal Eis) : summand (φ*χ) W X p.1 p.2=
      ∑h:Eis⧸Ideal.span {c},fixedRowFourierCoeff c hc φ h*
        (summand χ W X p.1 p.2*
          fixedRowFourierPhase c hc h (primaryGenerator p.1*(primaryGenerator p.2)^3)) := by
    rw [summand_mul_fixed_twist,←fixedRowFourier_inversion c hc φ hφ,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  calc
    completedT (φ*χ) W X=∑'p:Ideal Eis×Ideal Eis,summand (φ*χ) W X p.1 p.2 :=
      (completedT_summable (φ*χ) W hW X hX).tsum_prod.symm
    _=∑'p:Ideal Eis×Ideal Eis,∑h:Eis⧸Ideal.span {c},fixedRowFourierCoeff c hc φ h*
        (summand χ W X p.1 p.2*
          fixedRowFourierPhase c hc h (primaryGenerator p.1*(primaryGenerator p.2)^3)) :=
      tsum_congr hp
    _=∑h:Eis⧸Ideal.span {c},∑'p:Ideal Eis×Ideal Eis,fixedRowFourierCoeff c hc φ h*
        (summand χ W X p.1 p.2*
          fixedRowFourierPhase c hc h (primaryGenerator p.1*(primaryGenerator p.2)^3)) :=
      Summable.tsum_finsetSum (fun h _=>(completedFixedFrequency_summable χ c hc h W hW X hX).mul_left _)
    _=_:=by simp only [tsum_mul_left,completedFixedFrequency]

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open CubicEisenstein hiding summand
local notation "Eis" => ActualEisensteinCubic.O

theorem actual_completedT_fixed_fourier (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (Ψ:Eis→*ℂ) (Q:Ideal Eis) (hQ:Q≠0)
    (hcQ:Ideal.span {c}≤Q*Ideal.span {(72:Eis)})
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(I:Ideal Eis)(hI:Supported I)(φ:Eis→*ℂ),
      CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)}) φ ∧
      (∀n,‖φ n‖≤1) ∧
      IsCoprime (Q*Ideal.span {(72:Eis)})
        (∏P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)}),P.val.val) ∧
      (∀h:Eis⧸Ideal.span {c},‖fixedRowFourierCoeff c hc φ h‖≤1) ∧
      (∀(W:ℝ→ℂ),HasCompactSupport W→∀X:ℝ,0<X→
        completedT (rowTwist Ψ m f z) W X=
          ∑h:Eis⧸Ideal.span {c},fixedRowFourierCoeff c hc φ h*
            completedFixedFrequency (freePrimeRow I hI (Q*Ideal.span {(72:Eis)})) c hc h W X) := by
  obtain ⟨I,hI,φ,hφ,hφn,hcop,hmod,hperiod,hnorm,hT⟩:=
    exists_actual_coprime_completed_row Ψ Q hQ hΨ hΨnorm m f z hm hf hz hmLam hm2
  refine ⟨I,hI,φ,hφ,hφn,hcop,fixedRowFourierCoeff_norm c hc φ hφn,?_⟩
  intro W hW X hX
  rw [hT W X]
  exact completedT_fixed_fourier c hc φ _ (fun x y hxy=>hφ x y (hcQ hxy)) W hW X hX

end CanonicalRowCompletion

end

end OAI
end OAIOriginalModule0325

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.FixedThetaTwists
Source SHA256: 8aa61529274beb6f42b7584ffe317de37c7649ab99514866dc8eb2a87b96352f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0326


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
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
local notation "Eis" => ActualEisensteinCubic.O

lemma fixedThetaTwist_mul (φ χ:Eis→*ℂ) (n:Eis) :
    fixedThetaTwist (φ*χ) n=fixedThetaTwist φ n*χ n := by
  by_cases hn:lambda^2∣n-1
  · rw [fixedThetaTwist_primary _ n hn,fixedThetaTwist_primary _ n hn,MonoidHom.mul_apply]
    ring
  · rw [fixedThetaTwist_not_primary _ n hn,fixedThetaTwist_not_primary _ n hn,zero_mul]

def fixedThetaRowCoeff (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ:Eis→*ℂ) (h:Eis⧸Ideal.span {c}) : ℂ :=
  finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient φ c) h

lemma fixedThetaRowCoeff_norm (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ:Eis→*ℂ) (hφ:∀n,‖φ n‖≤1) (h:Eis⧸Ideal.span {c}) :
    ‖fixedThetaRowCoeff c hc φ h‖≤1 :=
  finiteAdditiveFourierCoeff_norm _ _ (fixedThetaQuotient_norm_le_one φ hφ c) h

theorem fixedThetaTwist_fixed_fourier (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (Q:Ideal Eis) (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (φ χ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ) (n:Eis) :
    fixedThetaTwist (φ*χ) n=
      ∑h:Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc φ h*fixedRowFourierPhase c hc h n*χ n := by
  rw [←Finset.sum_mul,fixedThetaTwist_mul]
  congr 1
  have h:=finiteAdditiveFourier_inversion (quotientTrace c hc)
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc) (fixedThetaQuotient φ c)
    (Ideal.Quotient.mk _ n)
  rw [fixedThetaQuotient_mk φ Q hφ c hcQ n] at h
  exact h.symm

theorem fixedThetaTwist_free_fourier (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (Q:Ideal Eis) (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (I:Ideal Eis) (hI:CanonicalQuadraticSieve.Supported I)
    (φ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ) (n:Eis) :
    fixedThetaTwist (φ*freePrimeRow I hI Q) n=
      (∑h:Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc φ h*fixedRowFourierPhase c hc h n)*
      ActualEisensteinCubic.principalSexticRow (fun P:FreePrimeIndex I Q=>P.val.val)
        (freePrimeIndex_pairwise_coprime I Q)
        (fun P=>(supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.1)
        (fun P=>(UniqueFactorizationMonoid.normalizedFactors I).count P.val.val%6)
        (ActualEisensteinCubic.finitePrimeModulus (fun P:FreePrimeIndex I Q=>P.val.val))
        (ActualEisensteinCubic.span_finitePrimeModulus _) (Ideal.Quotient.mk _ n) := by
  rw [fixedThetaTwist_fixed_fourier c hc Q hcQ φ _ hφ n,←Finset.sum_mul,
    freePrimeRow_eq_principalSexticRow I hI Q n]

theorem actual_fixedTheta_fourier (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(I:Ideal Eis)(hI:CanonicalQuadraticSieve.Supported I)(φ:Eis→*ℂ),
      CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)}) φ ∧
      (∀n,‖φ n‖≤1) ∧
      IsCoprime (Q*Ideal.span {(72:Eis)})
        (∏P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)}),P.val.val) ∧
      (∀h:Eis⧸Ideal.span {c},‖fixedThetaRowCoeff c hc φ h‖≤1) ∧
      (∀n,fixedThetaTwist (rowTwist Ψ m f z) n=
        ∑h:Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc φ h*fixedRowFourierPhase c hc h n*
          freePrimeRow I hI (Q*Ideal.span {(72:Eis)}) n) := by
  obtain ⟨I,hI,φ,hφ,hφn,hcop,hrow⟩:=exists_actual_coprime_row Ψ Q hΨ hΨnorm m f z hm hf hz hmLam hm2
  refine ⟨I,hI,φ,hφ,hφn,hcop,fixedThetaRowCoeff_norm c hc φ hφn,?_⟩
  have he:fixedThetaTwist (rowTwist Ψ m f z)=
      fixedThetaTwist (φ*freePrimeRow I hI (Q*Ideal.span {(72:Eis)})):=
    fixedThetaTwist_congr_primary _ _ hrow
  intro n
  rw [he]
  exact fixedThetaTwist_fixed_fourier c hc _ hcQ φ _ hφ n

end CubicEisenstein

namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge
open UniqueFactorizationMonoid LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

lemma admissiblePrimeGood (K:Ideal Eis) (hK:Admissible K) (P:PrimeIndex K) : lambda∉P.val :=
  (hK.2.2 P.val (Multiset.mem_toFinset.mp P.property)).1

theorem quadraticRow_eq_primeIndex (K:Ideal Eis) (hK:Admissible K) (x:Eis) :
    quadraticRow K x=finiteSexticRow (fun P:PrimeIndex K=>P.val)
      (admissiblePrimeGood K hK) (fun _=>3) x := by
  have hs:∀I∈({K}:Finset (Ideal Eis)),Admissible I:=by
    intro I hI
    simpa only [Finset.mem_singleton.mp hI] using hK
  have heq:primePool ({K}:Finset (Ideal Eis))=primeSupport K:=by
    simp [primePool,primeSupport]
  let e:primePool ({K}:Finset (Ideal Eis))≃PrimeIndex K:={
    toFun:=fun P=>⟨P.val,heq ▸ P.property⟩
    invFun:=fun P=>⟨P.val,heq.symm ▸ P.property⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }
  rw [quadraticRow_eq_pool {K} hs K (Finset.mem_singleton_self K) x,
    idealSupport_singleton_univ]
  simp only [QuadraticInitialBound.quadraticRow,finiteSquarefreeRow,Finset.prod_pow,
    finiteSexticRow,MulChar.pow_apply' _ (by decide : (3:ℕ)≠0)]
  congr 1
  exact Fintype.prod_equiv e _ _ (fun P=>rfl)

theorem completedLocalExponent_residual (I F Q:Ideal Eis) (hFQ:F∣Q)
    (P:PrimeIndex (rowResidualPart I Q)) : completedLocalExponent I F P.val=1 := by
  have h:=rowResidualPart_prime_exponent I Q P.val (Multiset.mem_toFinset.mp P.property)
  have hnot:¬P.val∣F:=fun hd=>h.2.2 (hd.trans hFQ)
  simp only [completedLocalExponent,h.2.1,ite_eq_right hnot,mul_zero,add_zero,Nat.reduceMod]

theorem residual_bracket_eq_quadraticRow (I F Q:Ideal Eis) (hFQ:F∣Q)
    (hbad:∀P∈fixedBadPrimes,P∣Q) (x:Eis) :
    (∏P:PrimeIndex (rowResidualPart I Q),
      bracket (actualSextic P.val
        (admissiblePrimeGood _ (rowResidualPart_admissible I Q hbad) P))
        (completedLocalExponent I F P.val) (Ideal.Quotient.mk P.val x))=
      quadraticRow (rowResidualPart I Q) x := by
  simp_rw [completedLocalExponent_residual I F Q hFQ,bracket_one_eq_quadratic]
  rw [quadraticRow_eq_primeIndex _ (rowResidualPart_admissible I Q hbad)]
  simp only [finiteSexticRow,MulChar.pow_apply' _ (by decide : (3:ℕ)≠0)]

def residualQuadraticPhase (K:Ideal Eis) (u:Eisˣ) (m:ℕ) (D E:Ideal Eis) : ℂ :=
  quadraticRow K ((u.val*lambda^m)*primaryGenerator (D*E))

lemma residualQuadraticPhase_norm_le_one (K:Ideal Eis) (u:Eisˣ) (m:ℕ) (D E:Ideal Eis) :
    ‖residualQuadraticPhase K u m D E‖≤1 := quadraticRow_norm_le_one _ _

theorem residual_bracket_extracted_columns (I F Q:Ideal Eis) (hFQ:F∣Q)
    (hbad:∀P∈fixedBadPrimes,P∣Q) (u:Eisˣ) (m:ℕ) (D E n b:Ideal Eis) :
    (∏P:PrimeIndex (rowResidualPart I Q),
      bracket (actualSextic P.val
        (admissiblePrimeGood _ (rowResidualPart_admissible I Q hbad) P))
        (completedLocalExponent I F P.val)
        (Ideal.Quotient.mk P.val
          ((u.val*lambda^m)*primaryGenerator (D*n)*(primaryGenerator (E*b))^3)))=
      residualQuadraticPhase (rowResidualPart I Q) u m D E *
        quadraticRow (rowResidualPart I Q) (primaryGenerator (n*b)) := by
  simp_rw [completedLocalExponent_residual I F Q hFQ]
  rw [residual_bracket_product]
  rw [←quadraticRow_eq_primeIndex _ (rowResidualPart_admissible I Q hbad),
    ←quadraticRow_eq_primeIndex _ (rowResidualPart_admissible I Q hbad)]
  simp only [primaryGenerator_mul,residualQuadraticPhase,
    canonical_quadraticRow_argument_mul _ (rowResidualPart_admissible I Q hbad)]
  ring

end

section
open ActualEisensteinCubic CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

def actualResidualModelRow (K:ℝ) (I Q:Ideal Eis) (hI:I≠0)
    (hbad:∀P∈fixedBadPrimes,P∣Q) (hIK:(Ideal.absNorm I:ℝ)≤K) :
    idealRange (completedResidualScale K I Q) := by
  refine ⟨rowResidualPart I Q,mem_idealRange.mpr ⟨rowResidualPart_admissible I Q hbad,?_⟩⟩
  rw [rowResidualPart_norm I Q hI,completedResidualScale]
  exact div_le_div_of_nonneg_right hIK (by positivity)

lemma actualResidualModelRow_val (K:ℝ) (I Q:Ideal Eis) (hI:I≠0)
    (hbad:∀P∈fixedBadPrimes,P∣Q) (hIK:(Ideal.absNorm I:ℝ)≤K) :
    (actualResidualModelRow K I Q hI hbad hIK).val=rowResidualPart I Q := rfl

lemma actualResidualModelRow_shell (K:ℝ) (I Q:Ideal Eis) (hI:I≠0)
    (hbad:∀P∈fixedBadPrimes,P∣Q) (hIK:(Ideal.absNorm I:ℝ)≤K)
    (hlo:K/2≤(Ideal.absNorm I:ℝ)) :
    completedResidualScale K I Q/2≤(Ideal.absNorm (actualResidualModelRow K I Q hI hbad hIK).val:ℝ) := by
  change completedResidualScale K I Q/2≤(Ideal.absNorm (rowResidualPart I Q):ℝ)
  rw [rowResidualPart_norm I Q hI,completedResidualScale]
  have h:=div_le_div_of_nonneg_right hlo
    (show 0≤(Ideal.absNorm (rowPowerfulPart I):ℝ)*(Ideal.absNorm (rowMaskPart I Q):ℝ) by positivity)
  convert h using 1 ; ring

theorem completedBranchScale_raw_argument {ι:Type*} [Fintype ι]
    (K X c r:ℝ) (I F Q:Ideal Eis) (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (e:ι→Fin 3) (k n b:Ideal Eis) (hK:0<completedResidualScale K I Q)
    (hc:0<c) (hk:k≠0) :
    ((completedBranchScale K (X/c) I F Q P e)⁻¹*
      (completedResidualScale K I Q/(Ideal.absNorm k:ℝ))^2)*r^3*
      (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3=
    X*r^3*
      (Ideal.absNorm (reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e 1*n):ℝ)*
      (Ideal.absNorm (reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e 2*b):ℝ)^3/
      (c*(Ideal.absNorm k:ℝ)^2*(Ideal.absNorm (∏i,P i):ℝ)^2) := by
  have hkN:(Ideal.absNorm k:ℝ)≠0:=by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hk)
  have hpN:(Ideal.absNorm (∏i,P i):ℝ)≠0:=by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr (fun i _=>NeZero.ne (P i))))
  simp only [completedBranchScale,inv_div,map_mul,Nat.cast_mul]
  field_simp [hK.ne',hc.ne',hkN,hpN]

end

open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

def residualModelRowPhase {K:ℝ} (rowPhase:ℕ→idealRange K→ℂ)
    (u:Eisˣ) (D E:Ideal Eis) (m:ℕ) (k:idealRange K) : ℂ :=
  rowPhase m k*residualQuadraticPhase k.val u m D E

lemma residualModelRowPhase_norm_le_one {K:ℝ} (rowPhase:ℕ→idealRange K→ℂ)
    (hphase:∀m k,‖rowPhase m k‖≤1) (u:Eisˣ) (D E:Ideal Eis) (m:ℕ) (k:idealRange K) :
    ‖residualModelRowPhase rowPhase u D E m k‖≤1 := by
  rw [residualModelRowPhase,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (hphase m k)).trans (residualQuadraticPhase_norm_le_one k.val u m D E)

theorem residual_coefficient_eq_canonical {ι:Type*} [Fintype ι]
    (I F Q:Ideal Eis) (hFQ:F∣Q) (hbad:∀P∈fixedBadPrimes,P∣Q)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (ρ q:ℝ) (u:Eisˣ)
    (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (rowPhase:ℕ→ℂ) (m:ℕ) (n b:Ideal Eis) :
    let D:=reflectionExtractedDivisor P j e 1
    let E:=reflectionExtractedDivisor P j e 2
    (rowPhase m*(∏p:PrimeIndex (rowResidualPart I Q),
        bracket (actualSextic p.val (admissiblePrimeGood _ (rowResidualPart_admissible I Q hbad) p))
          (completedLocalExponent I F p.val)
          (Ideal.Quotient.mk p.val ((u.val*lambda^m)*primaryGenerator (D*n)*(primaryGenerator (E*b))^3))) *
      η m (D*n) (E*b)*reflectedBranch P hg j e (primaryGenerator (D*n)) (primaryGenerator (E*b)))/
        ((ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm (D*n):ℝ)*(Ideal.absNorm (E*b):ℝ):ℝ):ℂ)=
      4*canonicalRawBranchCoefficient P hg j e ρ q
        (fun l a c=>η l (D*a) (E*c))
        (fun l=>rowPhase l*residualQuadraticPhase (rowResidualPart I Q) u l D E)
        (rowResidualPart I Q) m n b := by
  dsimp only
  rw [residual_bracket_extracted_columns I F Q hFQ hbad]
  unfold canonicalRawBranchCoefficient reflectedDyadicCoefficient
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  norm_num
  ring

end CompletedGauss

open scoped Classical BigOperators ContDiff

namespace CompletedGauss.FreeReflection

section
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

def pool (I Q Q0:Ideal Eis) : Finset (Ideal Eis) :=
  (completedReflectionPool I Q).filter (fun P=>¬Q0≤P)

lemma pool_subset (I Q Q0:Ideal Eis) : pool I Q Q0⊆completedReflectionPool I Q :=
  Finset.filter_subset _ _
lemma pool_maximal (I Q Q0:Ideal Eis) (P:pool I Q Q0) : P.val.IsMaximal :=
  completedReflectionPool_maximal I Q ⟨P.val,pool_subset I Q Q0 P.property⟩
lemma pool_good (I Q Q0:Ideal Eis) (P:pool I Q Q0) : lambda∉P.val :=
  completedReflectionPool_good I Q ⟨P.val,pool_subset I Q Q0 P.property⟩
lemma pool_odd (I Q Q0:Ideal Eis) (P:pool I Q Q0) : ringChar (Eis⧸P.val)≠2 :=
  completedReflectionPool_odd I Q ⟨P.val,pool_subset I Q Q0 P.property⟩
lemma pool_divides (I Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0) (P:pool I Q Q0) : P.val∣I*Q :=
  completedReflectionPool_divides I Q hI hQ ⟨P.val,pool_subset I Q Q0 P.property⟩
lemma pool_nonresidual (I Q Q0:Ideal Eis) (P:pool I Q Q0) : ¬P.val∣rowResidualPart I Q :=
  completedReflectionPool_nonresidual I Q ⟨P.val,pool_subset I Q Q0 P.property⟩
lemma pool_free (I Q Q0:Ideal Eis) (P:pool I Q Q0) : ¬Q0≤P.val :=
  (Finset.mem_filter.mp P.property).2

lemma pool_eq_on_fiber (I J Q Q0:Ideal Eis) (hI:I≠0) (hJ:J≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart I=rowPowerfulPart J) (hT:rowMaskPart I Q=rowMaskPart J Q) :
    pool I Q Q0=pool J Q Q0 := by
  unfold pool
  rw [completedReflectionPool_eq_on_fiber I J Q hI hJ hQ hA hT]

end

section
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

def reflectionChoiceValue (I Q Q0:Ideal Eis) (e:pool I Q Q0→Fin 6)
    (P:Ideal Eis) : Fin 6 :=
  if h:P∈pool I Q Q0 then e ⟨P,h⟩ else 0

def reflectionActivePool (I Q Q0:Ideal Eis) (e:pool I Q Q0→Fin 6) : Finset (Ideal Eis) :=
  (pool I Q Q0).filter (fun P=>reflectionSixActive (reflectionChoiceValue I Q Q0 e P))

lemma reflectionActivePool_subset (I Q Q0:Ideal Eis) (e:pool I Q Q0→Fin 6) :
    reflectionActivePool I Q Q0 e⊆pool I Q Q0 := Finset.filter_subset _ _

lemma mem_reflectionActivePool (I Q Q0:Ideal Eis) (e:pool I Q Q0→Fin 6)
    (P:pool I Q Q0) :
    P.val∈reflectionActivePool I Q Q0 e ↔ reflectionSixActive (e P) := by
  rw [reflectionActivePool, Finset.mem_filter]
  simp only [P.property, true_and]
  rw [reflectionChoiceValue, dite_eq_left P.property]

lemma reflectionActivePool_encode (I Q Q0:Ideal Eis)
    (A:Finset (pool I Q Q0)) (e:A→Fin 3) :
    reflectionActivePool I Q Q0 (encodeReflectionSix ⟨A,e⟩)=A.image Subtype.val := by
  ext P
  constructor
  · intro hP
    let p:pool I Q Q0:=⟨P,reflectionActivePool_subset I Q Q0 _ hP⟩
    have hp:p∈A:=(reflectionSixActive_encode ⟨A,e⟩ p).mp
      ((mem_reflectionActivePool I Q Q0 _ p).mp hP)
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  · intro hP
    obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp hP
    exact (mem_reflectionActivePool I Q Q0 _ p).mpr ((reflectionSixActive_encode ⟨A,e⟩ p).mpr hp)

def reflectionActiveLabel (I Q Q0:Ideal Eis) (e:pool I Q Q0→Fin 6)
    (P:reflectionActivePool I Q Q0 e) : Fin 3 :=
  reflectionSixLabel (e ⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩)

def sixReflectedBranch (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:pool I Q Q0→Fin 6)
    (amplitude:ℕ→Ideal Eis→Ideal Eis→ℂ) (hamp:∀m n b,‖amplitude m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    ReflectedBranchData levelBound K I F Q where
  levelScale:=levelScale
  levelScale_pos:=hlevel
  levelScale_le:=hbound
  primes:=reflectionActivePool I Q Q0 e
  maximal:=fun P=>pool_maximal I Q Q0 ⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩
  good:=fun P=>pool_good I Q Q0 ⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩
  coprime:=by
    intro P R hPR
    let : P.val.IsMaximal:=pool_maximal I Q Q0 ⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩
    let : R.val.IsMaximal:=pool_maximal I Q Q0 ⟨R.val,reflectionActivePool_subset I Q Q0 e R.property⟩
    exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hPR)
  divides:=fun P=>pool_divides I Q Q0 hI hQ ⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩
  nonresidual:=fun P=>pool_nonresidual I Q Q0 ⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩
  label:=reflectionActiveLabel I Q Q0 e
  nColumns:=fun i=>dualIdealDyad i.2.2
  bColumns:=fun i=>dualIdealDyad i.2.1
  nBounds:=fun i n hn=>dualIdealDyad_bounds i.2.2 n hn
  bBounds:=fun i b hb=>dualIdealDyad_bounds i.2.1 b hb
  amplitude:=fun i=>amplitude i.1
  amplitude_bound:=fun i n _ b _=>hamp i.1 n b
  rowPhase:=fun i=>rowPhase i.1
  rowPhase_bound:=fun i k=>hrow i.1 k

end

section
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

def sixPhaseFixedCuspBranch (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:pool I Q Q0→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    ReflectedBranchData levelBound K I F Q :=
  (sixReflectedBranch I F Q Q0 hI hQ K levelBound levelScale hlevel hbound e
    (fixedCuspArrayWithPhase cusp u phaseArray)
    (fixedCuspArrayWithPhase_norm_le_one cusp u phaseArray hphase) rowPhase hrow).withExtractedFixedCuspArrayWithPhase cusp u phaseArray hphase rowPhase hrow

lemma sixPhaseFixedCuspBranch_primes (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:pool I Q Q0→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    (sixPhaseFixedCuspBranch I F Q Q0 hI hQ K levelBound levelScale hlevel hbound e cusp u
      phaseArray hphase rowPhase hrow).primes=reflectionActivePool I Q Q0 e := rfl

lemma sixPhaseFixedCuspBranch_amplitude (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:pool I Q Q0→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1)
    (i:ℕ×ℕ×ℕ) (n b:Ideal Eis) :
    let d:=sixPhaseFixedCuspBranch I F Q Q0 hI hQ K levelBound levelScale hlevel hbound e cusp u
      phaseArray hphase rowPhase hrow
    let D:=reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 1
    let E:=reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 2
    d.amplitude i n b=phaseArray i.1 (D*n) (E*b)*fixedConjugateCuspArray cusp u i.1 (D*n) (E*b) := rfl

lemma sixPhaseFixedCuspBranch_scale (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K X levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:pool I Q Q0→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    let d:=sixPhaseFixedCuspBranch I F Q Q0 hI hQ K levelBound levelScale hlevel hbound e cusp u
      phaseArray hphase rowPhase hrow
    completedBranchScale K (X/d.levelScale) I F Q (fun P:d.primes=>P.val) d.label=
      completedBranchScale K (X/levelScale) I F Q
        (fun P:reflectionActivePool I Q Q0 e=>P.val) (reflectionActiveLabel I Q Q0 e) := rfl

end
section

open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
local instance poolMaximal (I Q Q0:Ideal Eis) (P:pool I Q Q0) : P.val.IsMaximal :=
  pool_maximal I Q Q0 P
noncomputable local instance poolField (I Q Q0:Ideal Eis) (P:pool I Q Q0) : Field (Eis⧸P.val) :=
  Ideal.Quotient.field P.val
noncomputable local instance poolFintype (I Q Q0:Ideal Eis) (P:pool I Q Q0) : Fintype (Eis⧸P.val) :=
  Fintype.ofFinite _

def reflectionInactiveStratumWeight (I F Q Q0:Ideal Eis) (A:Finset (pool I Q Q0)) : ℂ :=
  ∏P∈(Finset.univ:Finset (pool I Q Q0))\A,
    zeroFourierCoefficient (actualSextic P.val (pool_good I Q Q0 P))
      (completedLocalExponent I F P.val)

lemma reflectionInactiveStratumWeight_norm_le_one (I F Q Q0:Ideal Eis)
    (A:Finset (pool I Q Q0)) : ‖reflectionInactiveStratumWeight I F Q Q0 A‖≤1 := by
  rw [reflectionInactiveStratumWeight,norm_prod]
  apply Finset.prod_le_one₀ (fun _ _=>norm_nonneg _)
  intro P _
  by_cases hj:completedLocalExponent I F P.val=0
  · rw [hj]
    exact zeroFourierCoefficient_zero_norm_le_one _
  · have he:=canonical_zeroFourierCoefficient P.val (pool_good I Q Q0 P)
      (pool_odd I Q Q0 P) (completedLocalExponent I F P.val)
      (Nat.mod_lt _ (by decide : 0<6))
    have hz:zeroFourierCoefficient (actualSextic P.val (pool_good I Q Q0 P))
        (completedLocalExponent I F P.val)=0 := by
      simpa only [actualSextic,ite_eq_right hj] using he
    rw [hz]
    simp

def reflectionSixInactiveWeight (I F Q Q0:Ideal Eis) (e:pool I Q Q0→Fin 6) : ℂ :=
  if reflectionSixValid e then reflectionInactiveStratumWeight I F Q Q0 (reflectionSixSupport e) else 0

lemma reflectionSixInactiveWeight_norm_le_one (I F Q Q0:Ideal Eis)
    (e:pool I Q Q0→Fin 6) : ‖reflectionSixInactiveWeight I F Q Q0 e‖≤1 := by
  unfold reflectionSixInactiveWeight
  split_ifs
  · exact reflectionInactiveStratumWeight_norm_le_one I F Q Q0 _
  · simp

lemma sum_reflectionSixInactiveWeight_unpad (I F Q Q0:Ideal Eis)
    (G:(pool I Q Q0→Fin 6)→ℂ) :
    (∑e:pool I Q Q0→Fin 6,reflectionSixInactiveWeight I F Q Q0 e*G e)=
      ∑A:Finset (pool I Q Q0),∑e:A→Fin 3,
        reflectionInactiveStratumWeight I F Q Q0 A*G (encodeReflectionSix ⟨A,e⟩) := by
  rw [sum_active_exceptional_eq_six]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he:reflectionSixValid e
  · rw [ite_eq_left he,encode_decodeReflectionSix e he]
    simp only [reflectionSixInactiveWeight,ite_eq_left he,decodeReflectionSix]
  · simp only [ite_eq_right he,reflectionSixInactiveWeight,zero_mul]

abbrev SixReflectionIndex (rays:ℕ) (I Q Q0:Ideal Eis) :=
  Fin rays×(pool I Q Q0→Fin 6)

end

open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

def sixPhaseFixedCuspFiber (rays:ℕ) (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound:ℝ) (levelScale:SixReflectionIndex rays I Q Q0→ℝ)
    (hlevel:∀x,0<levelScale x) (hlevelBound:∀x,levelScale x≤levelBound)
    (cusp:SixReflectionIndex rays I Q Q0→Fin 3) (unit:SixReflectionIndex rays I Q Q0→Eisˣ)
    (phaseArray:SixReflectionIndex rays I Q Q0→ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hphase:∀x m n b,‖phaseArray x m n b‖≤1)
    (rayWeight:SixReflectionIndex rays I Q Q0→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:SixReflectionIndex rays I Q Q0→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1) : ReflectedFiberData rays levelBound K I F Q where
  pool:=pool I Q Q0
  maximal:=pool_maximal I Q Q0
  divides:=pool_divides I Q Q0 hI hQ
  branch:=fun x=>sixPhaseFixedCuspBranch I F Q Q0 hI hQ K levelBound (levelScale x) (hlevel x) (hlevelBound x)
    x.2 (cusp x) (unit x) (phaseArray x) (hphase x) (rowPhase x) (hrow x)
  weight:=fun x=>rayWeight x*reflectionSixInactiveWeight I F Q Q0 x.2
  weight_bound:=by
    intro x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (hray x)).trans (reflectionSixInactiveWeight_norm_le_one I F Q Q0 x.2)

theorem sixPhaseFixedCuspFiber_value (rays:ℕ) (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound:ℝ) (levelScale:SixReflectionIndex rays I Q Q0→ℝ)
    (hlevel:∀x,0<levelScale x) (hlevelBound:∀x,levelScale x≤levelBound)
    (cusp:SixReflectionIndex rays I Q Q0→Fin 3) (unit:SixReflectionIndex rays I Q Q0→Eisˣ)
    (phaseArray:SixReflectionIndex rays I Q Q0→ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hphase:∀x m n b,‖phaseArray x m n b‖≤1)
    (rayWeight:SixReflectionIndex rays I Q Q0→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:SixReflectionIndex rays I Q Q0→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1)
    (W:ℝ→ℂ) (X ρ q:ℝ) (k:idealRange (completedResidualScale K I Q)) :
    let d:=sixPhaseFixedCuspFiber rays I F Q Q0 hI hQ K levelBound levelScale hlevel hlevelBound
      cusp unit phaseArray hphase rayWeight hray rowPhase hrow
    d.value W X ρ q k=
      ∑t:Fin rays,∑A:Finset (pool I Q Q0),∑e:A→Fin 3,
        reflectionInactiveStratumWeight I F Q Q0 A*rayWeight (t,encodeReflectionSix ⟨A,e⟩)*
          (d.branch (t,encodeReflectionSix ⟨A,e⟩)).value W X ρ q k := by
  dsimp only
  rw [ReflectedFiberData.value,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  calc
    _=∑e:pool I Q Q0→Fin 6,reflectionSixInactiveWeight I F Q Q0 e*
      (rayWeight (t,e)*(sixPhaseFixedCuspBranch I F Q Q0 hI hQ K levelBound (levelScale (t,e))
        (hlevel (t,e)) (hlevelBound (t,e)) e (cusp (t,e)) (unit (t,e))
        (phaseArray (t,e)) (hphase (t,e)) (rowPhase (t,e)) (hrow (t,e))).value W X ρ q k) := by
          apply Finset.sum_congr rfl
          intro e _
          dsimp only [sixPhaseFixedCuspFiber]
          ring
    _=_ := by
      rw [sum_reflectionSixInactiveWeight_unpad]
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro e _
      dsimp only [sixPhaseFixedCuspFiber]
      exact (mul_assoc _ _ _).symm

end CompletedGauss.FreeReflection

end

end OAI
end OAIOriginalModule0326

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.FixedRayFibers
Source SHA256: 7c6fa56f60cb842441dafc8e727ee46be05bde1335f59d1104b058ce64421c7c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0327


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

open scoped Classical BigOperators ContDiff

namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

abbrev FixedBranchIndex (c:Eis) (hc:c≠0) (I Q Q0:Ideal Eis) :=
  FixedReflectionRay c hc×(pool I Q Q0→Fin 6)

def fixedRayFiber (c:Eis) (hc:c≠0) (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K:ℝ)
    (rayWeight:FixedBranchIndex c hc I Q Q0→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:FixedBranchIndex c hc I Q Q0→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1) :
    ReflectedFiberData (fixedReflectionRayCount c hc) (fixedCuspLevelBound c) K I F Q := by
  let R:SixReflectionIndex (fixedReflectionRayCount c hc) I Q Q0→FixedReflectionRay c hc:=
    fun x=>(fixedReflectionRayEquiv c hc).symm x.1
  let G:=fun x=>fixedFourierGeometry c hc (R x).1
  exact sixPhaseFixedCuspFiber (fixedReflectionRayCount c hc) I F Q Q0 hI hQ K
    (fixedCuspLevelBound c) (fun x=>(G x).levelScale)
    (fun x=>(G x).levelScale_pos) (fun x=>(G x).levelScale_le hc)
    (fun x=>(G x).shape.index) (fun x=>(R x).2.2)
    (fun x=>(G x).staticPhase (R x).2.1 (R x).2.2)
    (fun x=>(G x).staticPhase_norm_le_one (R x).2.1 (R x).2.2)
    (fun x=>rayWeight (R x,x.2)) (fun x=>hray (R x,x.2))
    (fun x=>rowPhase (R x,x.2)) (fun x=>hrow (R x,x.2))

lemma fixedRayFiber_pool (c:Eis) (hc:c≠0) (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K:ℝ)
    (rayWeight:FixedBranchIndex c hc I Q Q0→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:FixedBranchIndex c hc I Q Q0→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1) :
    (fixedRayFiber c hc I F Q Q0 hI hQ K rayWeight hray rowPhase hrow).pool=pool I Q Q0 := rfl

theorem fixedRayFiber_value (c:Eis) (hc:c≠0) (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K:ℝ)
    (rayWeight:FixedBranchIndex c hc I Q Q0→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:FixedBranchIndex c hc I Q Q0→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1)
    (W:ℝ→ℂ) (X ρ q:ℝ) (k:idealRange (completedResidualScale K I Q)) :
    let d:=fixedRayFiber c hc I F Q Q0 hI hQ K rayWeight hray rowPhase hrow
    d.value W X ρ q k=
      ∑r:FixedReflectionRay c hc,∑A:Finset (pool I Q Q0),∑e:A→Fin 3,
        reflectionInactiveStratumWeight I F Q Q0 A*rayWeight (r,encodeReflectionSix ⟨A,e⟩)*
          (d.branch (fixedReflectionRayEquiv c hc r,encodeReflectionSix ⟨A,e⟩)).value W X ρ q k := by
  dsimp only
  rw [ReflectedFiberData.value,Fintype.sum_prod_type]
  calc
    _=∑r:FixedReflectionRay c hc,∑e:pool I Q Q0→Fin 6,
        reflectionSixInactiveWeight I F Q Q0 e*
          (rayWeight (r,e)*((fixedRayFiber c hc I F Q Q0 hI hQ K rayWeight hray rowPhase hrow).branch
            (fixedReflectionRayEquiv c hc r,e)).value W X ρ q k) := by
      apply Fintype.sum_equiv (fixedReflectionRayEquiv c hc).symm
      intro t
      apply Finset.sum_congr rfl
      intro e he
      simp only [Equiv.apply_symm_apply]
      change (rayWeight ((fixedReflectionRayEquiv c hc).symm t,e)*
        reflectionSixInactiveWeight I F Q Q0 e)*_= _
      ring
    _=_:=by
      apply Finset.sum_congr rfl
      intro r hr
      rw [sum_reflectionSixInactiveWeight_unpad]
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro e he
      exact (mul_assoc _ _ _).symm

end CompletedGauss.FreeReflection

open scoped BigOperators Classical

namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

def residualArgumentPhase (K:Ideal Eis) (z:Eis) (D E:Ideal Eis) : ℂ :=
  quadraticRow K (z*primaryGenerator (D*E))

lemma residualArgumentPhase_norm_le_one (K:Ideal Eis) (z:Eis) (D E:Ideal Eis) :
    ‖residualArgumentPhase K z D E‖≤1 := quadraticRow_norm_le_one _ _

theorem residual_bracket_extracted_argument (I F Q:Ideal Eis) (hFQ:F∣Q)
    (hbad:∀P∈fixedBadPrimes,P∣Q) (z:Eis) (D E n b:Ideal Eis) :
    (∏P:PrimeIndex (rowResidualPart I Q),
      bracket (actualSextic P.val
        (admissiblePrimeGood _ (rowResidualPart_admissible I Q hbad) P))
        (completedLocalExponent I F P.val)
        (Ideal.Quotient.mk P.val
          (z*primaryGenerator (D*n)*(primaryGenerator (E*b))^3)))=
      residualArgumentPhase (rowResidualPart I Q) z D E *
        quadraticRow (rowResidualPart I Q) (primaryGenerator (n*b)) := by
  simp_rw [completedLocalExponent_residual I F Q hFQ]
  rw [residual_bracket_product]
  rw [←quadraticRow_eq_primeIndex _ (rowResidualPart_admissible I Q hbad),
    ←quadraticRow_eq_primeIndex _ (rowResidualPart_admissible I Q hbad)]
  simp only [primaryGenerator_mul,residualArgumentPhase,
    canonical_quadraticRow_argument_mul _ (rowResidualPart_admissible I Q hbad)]
  ring

def residualArgumentRowPhase {K:ℝ} (rowPhase:ℕ→idealRange K→ℂ)
    (residualArgument:ℕ→Eis) (D E:Ideal Eis) (m:ℕ) (k:idealRange K) : ℂ :=
  rowPhase m k*residualArgumentPhase k.val (residualArgument m) D E

lemma residualArgumentRowPhase_norm_le_one {K:ℝ} (rowPhase:ℕ→idealRange K→ℂ)
    (hphase:∀m k,‖rowPhase m k‖≤1) (residualArgument:ℕ→Eis)
    (D E:Ideal Eis) (m:ℕ) (k:idealRange K) :
    ‖residualArgumentRowPhase rowPhase residualArgument D E m k‖≤1 := by
  rw [residualArgumentRowPhase,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (hphase m k)).trans (residualArgumentPhase_norm_le_one k.val _ D E)

theorem residual_coefficient_eq_canonical_argument {ι:Type*} [Fintype ι]
    (I F Q:Ideal Eis) (hFQ:F∣Q) (hbad:∀P∈fixedBadPrimes,P∣Q)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (ρ q:ℝ) (residualArgument:ℕ→Eis)
    (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (rowPhase:ℕ→ℂ) (m:ℕ) (n b:Ideal Eis) :
    let D:=reflectionExtractedDivisor P j e 1
    let E:=reflectionExtractedDivisor P j e 2
    (rowPhase m*(∏p:PrimeIndex (rowResidualPart I Q),
        bracket (actualSextic p.val (admissiblePrimeGood _ (rowResidualPart_admissible I Q hbad) p))
          (completedLocalExponent I F p.val)
          (Ideal.Quotient.mk p.val (residualArgument m*primaryGenerator (D*n)*(primaryGenerator (E*b))^3))) *
      η m (D*n) (E*b)*reflectedBranch P hg j e (primaryGenerator (D*n)) (primaryGenerator (E*b)))/
        ((ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm (D*n):ℝ)*(Ideal.absNorm (E*b):ℝ):ℝ):ℂ)=
      4*canonicalRawBranchCoefficient P hg j e ρ q
        (fun l a c=>η l (D*a) (E*c))
        (fun l=>rowPhase l*residualArgumentPhase (rowResidualPart I Q) (residualArgument l) D E)
        (rowResidualPart I Q) m n b := by
  dsimp only
  rw [residual_bracket_extracted_argument I F Q hFQ hbad]
  unfold canonicalRawBranchCoefficient reflectedDyadicCoefficient
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  norm_num
  ring

end

section
open ActualEisensteinCubic CubicEisenstein LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

lemma reflectedBranch_local_support {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (n b:Eis) (hne:reflectedBranch P hg j e n b≠0) :
    (∀i,j i=4 → e i=1 → n∈P i) ∧
    (∀i,j i=4 → e i=2 → n∉P i ∧ b∈P i) := by
  have hi (i:ι):reflectedLocalPiece (P i) (hg i) (j i) (e i) n b≠0:=
    (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)
  constructor
  · intro i hj he
    by_contra hn
    exact hi i (by simp [reflectedLocalPiece,hj,exceptionalPiece,he,hn])
  · intro i hj he
    by_contra hn
    exact hi i (by simp [reflectedLocalPiece,hj,exceptionalPiece,he,hn])

lemma reflectionExtractedDivisor_dvd_of_local {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hcop:Pairwise (fun i k=>IsCoprime (P i) (P k)))
    (j:ι→ℕ) (e:ι→Fin 3) (v:Fin 3) (A:Ideal Eis)
    (hA:∀i,(j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0) → P i∣A) :
    reflectionExtractedDivisor P j e v∣A := by
  unfold reflectionExtractedDivisor
  apply Fintype.prod_dvd_of_coprime
  · intro i k hik
    change IsCoprime (reflectionExtractedPrime (P i) (j i) (e i) v)
      (reflectionExtractedPrime (P k) (j k) (e k) v)
    unfold reflectionExtractedPrime
    by_cases hi:(j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0)
    · rw [ite_eq_left hi]
      by_cases hk:(j k=4 ∧ e k=v) ∨ (j k=0 ∧ v=0)
      · rw [ite_eq_left hk]
        exact hcop hik
      · rw [ite_eq_right hk]
        exact isCoprime_one_right
    · rw [ite_eq_right hi]
      exact isCoprime_one_left
  · intro i
    unfold reflectionExtractedPrime
    split_ifs with hi
    · exact hA i hi
    · exact one_dvd _

theorem reflectedBranch_extracted_divisibility {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (hcop:Pairwise (fun i k=>IsCoprime (P i) (P k)))
    (j:ι→ℕ) (e:ι→Fin 3) (n b:Eis) (hne:reflectedBranch P hg j e n b≠0) :
    reflectionExtractedDivisor P j e 1∣Ideal.span {n} ∧
    reflectionExtractedDivisor P j e 2∣Ideal.span {b} ∧
    (∀i,j i=4 → e i=2 → n∉P i) := by
  have hs:=reflectedBranch_local_support P hg j e n b hne
  refine ⟨reflectionExtractedDivisor_dvd_of_local P hcop j e 1 _ ?_,
    reflectionExtractedDivisor_dvd_of_local P hcop j e 2 _ ?_,fun i hj he=>(hs.2 i hj he).1⟩
  · intro i hi
    have h:j i=4 ∧ e i=1:=by simpa using hi
    exact Ideal.dvd_span_singleton.mpr (hs.1 i h.1 h.2)
  · intro i hi
    have h:j i=4 ∧ e i=2:=by simpa using hi
    exact Ideal.dvd_span_singleton.mpr (hs.2 i h.1 h.2).2

def fixedCuspBranchNumerator {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis) : ℂ :=
  fixedCuspArrayWithPhase cusp u phaseArray m n b *
    reflectedBranch P hg j e (primaryGenerator n) (primaryGenerator b)

theorem fixedCuspBranchNumerator_support {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (hcop:Pairwise (fun i k=>IsCoprime (P i) (P k)))
    (j:ι→ℕ) (e:ι→Fin 3) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis)
    (hne:fixedCuspBranchNumerator P hg j e cusp u phaseArray m n b≠0) :
    reflectionExtractedDivisor P j e 1∣n ∧ reflectionExtractedDivisor P j e 2∣b ∧
    (∀i,j i=4 → e i=2 → primaryGenerator n∉P i) := by
  have hn:(fixedCuspArrayWithPhase cusp u phaseArray m n b)≠0:=
    (mul_ne_zero_iff.mp hne).1
  have he:fixedCuspArrayEligible n b:=by
    by_contra he
    exact hn (fixedCuspArrayWithPhase_zero cusp u phaseArray m n b he)
  have hb:reflectedBranch P hg j e (primaryGenerator n) (primaryGenerator b)≠0:=
    (mul_ne_zero_iff.mp hne).2
  have hs:=reflectedBranch_extracted_divisibility P hg hcop j e _ _ hb
  rwa [(primaryGenerator_spec n he.2.1).1,(primaryGenerator_spec b he.2.2).1] at hs

end

open ActualEisensteinCubic CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

def nonzeroDualDilation (D E:Ideal Eis) (hD:D≠0) (hE:E≠0)
    (x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal) : ℕ×NonzeroDualIdeal×NonzeroDualIdeal :=
  (x.1,⟨D*x.2.1.val,mul_ne_zero hD x.2.1.property⟩,
    ⟨E*x.2.2.val,mul_ne_zero hE x.2.2.property⟩)

lemma nonzeroDualDilation_injective (D E:Ideal Eis) (hD:D≠0) (hE:E≠0) :
    Function.Injective (nonzeroDualDilation D E hD hE) := by
  intro x y h
  apply Prod.ext
  · have ht:=congrArg (fun t:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>t.1) h
    exact ht
  · apply Prod.ext
    · apply Subtype.ext
      exact mul_left_cancel₀ hD (congrArg (fun t:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>t.2.1.val) h)
    · apply Subtype.ext
      exact mul_left_cancel₀ hE (congrArg (fun t:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>t.2.2.val) h)

theorem tsum_nonzeroDualDilation (D E:Ideal Eis) (hD:D≠0) (hE:E≠0)
    (f:(ℕ×NonzeroDualIdeal×NonzeroDualIdeal)→ℂ)
    (hsupport:∀x,f x≠0 → D∣x.2.1.val ∧ E∣x.2.2.val) :
    (∑'x,f x)=∑'x,f (nonzeroDualDilation D E hD hE x) := by
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun x:Function.support (fun y=>f (nonzeroDualDilation D E hD hE y))=>
      nonzeroDualDilation D E hD hE x.val)
  · exact (nonzeroDualDilation_injective D E hD hE).comp Subtype.val_injective
  · intro x hx
    obtain ⟨hn,hb⟩:=hsupport x hx
    obtain ⟨n,hn⟩:=hn
    obtain ⟨b,hb⟩:=hb
    have hn0:n≠0:=by
      intro hz
      apply x.2.1.property
      rw [hn,hz,mul_zero]
    have hb0:b≠0:=by
      intro hz
      apply x.2.2.property
      rw [hb,hz,mul_zero]
    let y:ℕ×NonzeroDualIdeal×NonzeroDualIdeal:=(x.1,⟨n,hn0⟩,⟨b,hb0⟩)
    have hy:nonzeroDualDilation D E hD hE y=x:=by
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · exact Subtype.ext hn.symm
        · exact Subtype.ext hb.symm
    refine ⟨⟨y,?_⟩,hy⟩
    change f (nonzeroDualDilation D E hD hE y)≠0
    rwa [hy]
  · intro x
    rfl

theorem fixedCuspBranch_tsum_extract {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (hcop:Pairwise (fun i k=>IsCoprime (P i) (P k)))
    (j:ι→ℕ) (e:ι→Fin 3) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ)
    (kernel:(ℕ×NonzeroDualIdeal×NonzeroDualIdeal)→ℂ) :
    let D:=reflectionExtractedDivisor P j e 1
    let E:=reflectionExtractedDivisor P j e 2
    let hD:=reflectionExtractedDivisor_ne_zero P (fun i=>NeZero.ne (P i)) j e 1
    let hE:=reflectionExtractedDivisor_ne_zero P (fun i=>NeZero.ne (P i)) j e 2
    (∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      fixedCuspBranchNumerator P hg j e cusp u phaseArray x.1 x.2.1.val x.2.2.val*kernel x)=
    ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      fixedCuspBranchNumerator P hg j e cusp u phaseArray x.1 (D*x.2.1.val) (E*x.2.2.val)*
        kernel (nonzeroDualDilation D E hD hE x) := by
  dsimp only
  apply tsum_nonzeroDualDilation
  intro x hx
  have hcoeff:fixedCuspBranchNumerator P hg j e cusp u phaseArray x.1 x.2.1.val x.2.2.val≠0:=
    (mul_ne_zero_iff.mp hx).1
  have hs:=fixedCuspBranchNumerator_support P hg hcop j e cusp u phaseArray x.1 x.2.1.val x.2.2.val hcoeff
  exact ⟨hs.1,hs.2.1⟩

end CompletedGauss

open scoped BigOperators Classical MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic CompletedGauss CubicKubota CubicJacobiGlobal ConcreteTraceCRT
open LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

lemma fixedConjugateCuspArray_nonzero (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:fixedConjugateCuspArray j u m I J≠0) :
    fixedCuspArrayEligible I J ∧
      (sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)≠0 := by
  have helig:fixedCuspArrayEligible I J:=by
    by_contra he
    apply h
    simp only [fixedConjugateCuspArray,fixedCuspArray,ite_eq_right he,star_zero]
  refine ⟨helig,?_⟩
  intro hz
  apply h
  simp only [fixedConjugateCuspArray,fixedCuspArray,ite_eq_left helig,hz,zero_div,star_zero]

lemma fixedCusp_ramified_index_pos (j:Fin 3) (hj:j≠0) (u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) (helig:fixedCuspArrayEligible I J)
    (h:(sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)≠0) : 0<m := by
  apply Nat.pos_of_ne_zero
  intro hm
  have hp:lambda∣ramifiedTraceLambda:=by
    change lambda∣paperLambda
    rw [paperLambda_eq]
    exact dvd_mul_left lambda _
  have hd:=hp.trans (sourceCuspCoefficients_ramified_divisibility j hj _ h)
  simp only [fixedCuspArrayIndex,hm,pow_zero,mul_one] at hd
  have hu:IsCoprime lambda (u:Eis):=⟨0,(↑u⁻¹:Eis),by simp⟩
  have hni:IsCoprime lambda (primaryGenerator I):=coprime_of_dvd_sub_one lambda _
    ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans (primaryGenerator_spec I helig.2.1).2)
  have hnj:IsCoprime lambda (primaryGenerator J):=coprime_of_dvd_sub_one lambda _
    ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans (primaryGenerator_spec J helig.2.2).2)
  exact residue_lambda_prime.not_isUnit (((hu.mul_right hni).mul_right hnj.pow_right).isUnit_of_dvd hd)

def sourcePhaseUnit (j:Fin 3) (w u:Eisˣ) : Eisˣ :=
  if j=0 then paperLambdaUnit*w^2*u else -(w^2*u*paperLambdaUnit⁻¹)

def sourcePhaseExponent (j:Fin 3) (m:ℕ) : ℕ :=
  if j=0 then m+1 else m-1

lemma paperLambdaQuotient_succ (u:Eisˣ) (m:ℕ) (n b:Eis) :
    paperLambdaQuotient ((u.val*lambda^(m+1))*n*b^3)=
      (paperLambdaUnit⁻¹:Eisˣ).val*u.val*lambda^m*n*b^3 := by
  have hp:ramifiedTraceLambda*((paperLambdaUnit⁻¹:Eisˣ).val*u.val*lambda^m*n*b^3)=
      (u.val*lambda^(m+1))*n*b^3 := by
    change paperLambda*((paperLambdaUnit⁻¹:Eisˣ).val*u.val*lambda^m*n*b^3)=_
    rw [paperLambda_eq,pow_succ]
    have hi:(paperLambdaUnit:Eis)*(paperLambdaUnit⁻¹:Eisˣ)=1:=by simp
    calc
      _=((paperLambdaUnit:Eis)*(paperLambdaUnit⁻¹:Eisˣ))*(u.val*lambda^m*lambda*n*b^3):=by ring
      _=_:=by rw [hi,one_mul];ring
  have hd:ramifiedTraceLambda∣(u.val*lambda^(m+1))*n*b^3:=⟨_,hp.symm⟩
  have hn:ramifiedTraceLambda≠0:=by
    intro hz
    have he:=ramifiedEmbedding_traceLambda
    rw [hz,map_zero] at he
    exact eisLam_ne_zero he.symm
  apply mul_left_cancel₀ hn
  rw [paperLambdaQuotient_mul _ hd,hp]

theorem sourceCuspPhaseNumerator_columns (j:Fin 3) (w u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) (helig:fixedCuspArrayEligible I J)
    (h:(sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)≠0) :
    sourceCuspPhaseNumerator j w.val (fixedCuspArrayIndex u m I J)=
      ((sourcePhaseUnit j w u).val*lambda^(sourcePhaseExponent j m))*
        (primaryGenerator I*(primaryGenerator J)^3) := by
  by_cases hj:j=0
  · subst j
    simp only [sourceCuspPhaseNumerator,sourcePhaseUnit,sourcePhaseExponent,ite_true,
      fixedCuspArrayIndex,Units.val_mul,Units.val_pow_eq_pow_val]
    change paperLambda*w.val^2*((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)=_
    rw [paperLambda_eq,pow_succ]
    ring
  · have hm:=fixedCusp_ramified_index_pos j hj u m I J helig h
    cases m with
    | zero => omega
    | succ m =>
      simp only [sourceCuspPhaseNumerator,sourcePhaseUnit,sourcePhaseExponent,ite_eq_right hj,
        fixedCuspArrayIndex,Nat.succ_sub_succ_eq_sub,Nat.sub_zero,Units.val_neg,Units.val_mul,
        Units.val_pow_eq_pow_val]
      rw [paperLambdaQuotient_succ]
      ring

theorem fixedCuspArray_phase_brackets {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i) (exponent:ι→ℕ)
    (j:Fin 3) (w u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    fixedConjugateCuspArray j u m I J*
      (∏i,bracket (actualSextic (P i) (hg i)) (exponent i)
        (Ideal.Quotient.mk (P i) (sourceCuspPhaseNumerator j w.val (fixedCuspArrayIndex u m I J))))=
    fixedConjugateCuspArray j u m I J*
      ramifiedBranchPhase P hg exponent (sourcePhaseUnit j w u) (sourcePhaseExponent j m)*
      ∑e:ι→Fin 3,reflectedBranch P hg exponent e (primaryGenerator I) (primaryGenerator J) := by
  by_cases hz:fixedConjugateCuspArray j u m I J=0
  · rw [hz,zero_mul,zero_mul,zero_mul]
  · obtain ⟨he,hh⟩:=fixedConjugateCuspArray_nonzero j u m I J hz
    rw [sourceCuspPhaseNumerator_columns j w u m I J he hh,
      ramified_bracket_full_expansion]
    ring

end

open ActualEisensteinCubic CompletedGauss CompletedDyadic CubicKubota CubicJacobiGlobal ConcreteTraceCRT
open LocalReflectionBrackets ShortDraftCusp
local notation "Eis" => ActualEisensteinCubic.O

namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

def phaseUpperUnit : Eisˣ := s.upper_unit.unit

lemma phaseUpperUnit_val : (s.phaseUpperUnit:Eis)=s.upper 0 0 := s.upper_unit.unit_spec

def modelDualNumerator (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : Eis :=
  sourceCuspPhaseNumerator s.index (s.upper 0 0) (fixedCuspArrayIndex u m I J)

theorem model_array_brackets {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (c0:Eis) (hc0:c0≠0) (d U:Eis) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    (s.amplitude u m I J*A4BadPhase c0 hc0 d U (s.modelDualNumerator u m I J))*
      (∏i,bracket (actualSextic (P i) (hg i)) (j i)
        (Ideal.Quotient.mk (P i) (s.modelDualNumerator u m I J)))=
    ramifiedBranchPhase P hg j (sourcePhaseUnit s.index s.phaseUpperUnit u)
      (sourcePhaseExponent s.index m)*
      ∑e:ι→Fin 3,
        fixedCuspArrayWithPhase s.index u
          (s.reflectionStaticPhase c0 hc0 (Ideal.Quotient.mk _ (-d*U)) (s.modelDualNumerator u) u) m I J*
        reflectedBranch P hg j e (primaryGenerator I) (primaryGenerator J) := by
  let φ:=s.reflectionStaticPhase c0 hc0 (Ideal.Quotient.mk _ (-d*U)) (s.modelDualNumerator u) u
  have hA:φ m I J*fixedConjugateCuspArray s.index u m I J=
      s.amplitude u m I J*A4BadPhase c0 hc0 d U (s.modelDualNumerator u m I J) := by
    rw [A4BadPhase_as_fixed_residue]
    exact s.fixedCuspArrayWithPhase_reflectionStaticPhase c0 hc0 _ _ u m I J
  have hbr:=fixedCuspArray_phase_brackets P hg j s.index s.phaseUpperUnit u m I J
  rw [s.phaseUpperUnit_val] at hbr
  change fixedConjugateCuspArray s.index u m I J*
    (∏i,bracket (actualSextic (P i) (hg i)) (j i) (Ideal.Quotient.mk (P i) (s.modelDualNumerator u m I J)))=_ at hbr
  rw [←hA]
  calc
    _=φ m I J*(fixedConjugateCuspArray s.index u m I J*
      (∏i,bracket (actualSextic (P i) (hg i)) (j i) (Ideal.Quotient.mk (P i) (s.modelDualNumerator u m I J)))) := by ring
    _=φ m I J*(fixedConjugateCuspArray s.index u m I J*
      ramifiedBranchPhase P hg j (sourcePhaseUnit s.index s.phaseUpperUnit u)
        (sourcePhaseExponent s.index m)*
        ∑e:ι→Fin 3,reflectedBranch P hg j e (primaryGenerator I) (primaryGenerator J)) := by rw [hbr]
    _=_ := by
      simp only [fixedCuspArrayWithPhase]
      rw [←Finset.mul_sum]
      dsimp only [φ]
      ring

end FixedCuspShape

namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}
noncomputable local instance coefficientField (P:Ideal Eis) [P.IsMaximal] : Field (Eis⧸P) :=
  Ideal.Quotient.field P
noncomputable local instance coefficientFintype (P:Ideal Eis) [P.IsMaximal] : Fintype (Eis⧸P) :=
  Fintype.ofFinite _

def activePhase (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) : ℂ :=
  ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
    phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i)

lemma activePhase_norm (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2) (j:ι→ℕ) (hj:∀i,j i<6) :
    ‖D.activePhase hp hg j‖=1 := by
  rw [activePhase,norm_prod]
  have he (i:ι):‖(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i)‖=1 := by
    rw [norm_mul,FiniteRayExpansion.norm_char_unit,one_mul]
    exact canonical_phase_norm (Ideal.span {p i}) (hg i) (hchar i) (quotientTrace (p i) (hp i))
      (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i)) (j i) (hj i) (D.epsilon i)
  simp only [he,Finset.prod_const_one]

lemma bracketProduct_eq (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (x:Eis) :
    D.bracketProduct hp hg j x=D.activePhase hp hg j*
      ∏i,bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i) (Ideal.Quotient.mk _ x) := by
  exact Finset.prod_mul_distrib

def modelRowPhase (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (u:Eisˣ) (m:ℕ) : ℂ :=
  star D.fixedFactor*D.activePhase hp hg j*
    ramifiedBranchPhase (fun i=>Ideal.span {p i}) hg j
      (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)

theorem modelRowPhase_norm (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (u:Eisˣ) (m:ℕ) : ‖D.modelRowPhase s hp hg j u m‖=1 := by
  rw [modelRowPhase,norm_mul,norm_mul,norm_star,D.fixedFactor_norm hN hr hbase,
    D.activePhase_norm hp hg hchar j hj,ramifiedBranchPhase_norm,one_mul,one_mul]

theorem model_coefficient (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    s.amplitude u m I J*
      (star D.fixedFactor*A4BadPhase c0 hc0 (D.matrix (fun _=>1) 1 1) D.U (s.modelDualNumerator u m I J))*
      D.bracketProduct hp hg j (s.modelDualNumerator u m I J)=
    D.modelRowPhase s hp hg j u m*
      ∑e:ι→Fin 3,
        fixedCuspArrayWithPhase s.index u
          (s.reflectionStaticPhase c0 hc0 (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U))
            (s.modelDualNumerator u) u) m I J*
        reflectedBranch (fun i=>Ideal.span {p i}) hg j e (primaryGenerator I) (primaryGenerator J) := by
  rw [D.bracketProduct_eq]
  have he:=s.model_array_brackets (fun i=>Ideal.span {p i}) hg j c0 hc0
    (D.matrix (fun _=>1) 1 1) D.U u m I J
  calc
    _=(star D.fixedFactor*D.activePhase hp hg j)*
      ((s.amplitude u m I J*A4BadPhase c0 hc0 (D.matrix (fun _=>1) 1 1) D.U (s.modelDualNumerator u m I J))*
        (∏i,bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i)
          (Ideal.Quotient.mk _ (s.modelDualNumerator u m I J)))) := by ring
    _=_ := by rw [he];dsimp only [modelRowPhase];ring

end ControlledStratumArithmetic

lemma fixed_stratum_kernel_scale (j:Fin 3) (c0 r:Eis) :
    27*(sourceCuspScale j)^2*(Ideal.absNorm (Ideal.span {c0*r}):ℝ)^2=
      fixedCuspLevelScale j c0*(Ideal.absNorm (Ideal.span {r}):ℝ)^2 := by
  rw [←Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul,mul_pow,fixedCuspLevelScale]
  ring

end CubicEisenstein

end

end OAI
end OAIOriginalModule0327

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.ReflectionFibers
Source SHA256: d585663bd9772292150668fb218adfe3ba055a71f229a6e374f9de01a0058049
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0328


namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
