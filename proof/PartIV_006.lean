    rw [hh]
    decide
  · rw [map_Pb]; exact modb_irreducible
lemma PB_rat_irreducible : Irreducible (PB.map (Int.castRingHom ℚ)) :=
  (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast PB_primitive).mp PB_irreducible
lemma Pb_rat_irreducible : Irreducible (Pb.map (Int.castRingHom ℚ)) :=
  (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast Pb_primitive).mp Pb_irreducible

lemma boundary_elimination (t : ℝ) (ht : CombineV22.Uniform.InInterval t) :
    (18*t+9)^3*(7884*(CombineV22Optimality.boundary t)^3-
      18819*(CombineV22Optimality.boundary t)^2+
      14643*CombineV22Optimality.boundary t-3686) =
    108*CombineV22Optimality.cubic t := by
  let d := 18*t+9
  let n := 18*t+7
  have hd : d ≠ 0 := by dsimp [d]; linarith [ht.1]
  change d^3*(7884*(n/d)^3-18819*(n/d)^2+14643*(n/d)-3686)=_
  field_simp [hd]
  dsimp [d,n,CombineV22Optimality.cubic]
  ring
lemma b_elimination (t : ℝ) (ht : CombineV22.Uniform.InInterval t) :
    (9*(1+2*t)*(5+(-20)*t+24*t^2))^3*
      (53835237*(CombineV22.Uniform.b t)^3+381756141*(CombineV22.Uniform.b t)^2+
      94706196*CombineV22.Uniform.b t-17602208) =
    36000*CombineV22Optimality.cubic t*
      (435749760*t^6-2473186176*t^5+3937305744*t^4-2941434872*t^3+
        1160674488*t^2-234149130*t+18966825) := by
  let d := 9*(1+2*t)*(5+(-20)*t+24*t^2)
  let n := 8*(-1+3*t)*(15+(-40)*t+12*t^2)
  have hd : d ≠ 0 := by
    have h1 := CombineV22.Uniform.base0_pos t ht
    have h2 := CombineV22.Uniform.base2_pos t ht
    dsimp [d]
    positivity
  change d^3*(53835237*(n/d)^3+381756141*(n/d)^2+94706196*(n/d)-17602208)=_
  field_simp [hd]
  dsimp [d,n,CombineV22Optimality.cubic]
  ring

lemma boundary_root :
    7884*(CombineV22Optimality.boundary CombineV22Optimality.xiInf)^3-
      18819*(CombineV22Optimality.boundary CombineV22Optimality.xiInf)^2+
      14643*CombineV22Optimality.boundary CombineV22Optimality.xiInf-3686=0 := by
  have he := boundary_elimination _ CombineV22Optimality.xiInf_mem_small
  rw [CombineV22Optimality.cubic_xiInf,mul_zero] at he
  have hd : 18*CombineV22Optimality.xiInf+9 ≠ 0 := by
    linarith [CombineV22Optimality.xiInf_mem_small.1]
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero 3 hd)
lemma b_root :
    53835237*(CombineV22.Uniform.b CombineV22Optimality.xiInf)^3+
      381756141*(CombineV22.Uniform.b CombineV22Optimality.xiInf)^2+
      94706196*CombineV22.Uniform.b CombineV22Optimality.xiInf-17602208=0 := by
  have he := b_elimination _ CombineV22Optimality.xiInf_mem_small
  rw [CombineV22Optimality.cubic_xiInf,mul_zero,zero_mul] at he
  have hd : 9*(1+2*CombineV22Optimality.xiInf)*
      (5+(-20)*CombineV22Optimality.xiInf+24*CombineV22Optimality.xiInf^2) ≠ 0 := by
    have h1 := CombineV22.Uniform.base0_pos _ CombineV22Optimality.xiInf_mem_small
    have h2 := CombineV22.Uniform.base2_pos _ CombineV22Optimality.xiInf_mem_small
    positivity
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero 3 hd)

lemma root_minpoly_degree {p : ℚ[X]} {x : ℝ} (hp : Irreducible p)
    (hx : p.aeval x=0) (hd : p.natDegree=3) : (minpoly ℚ x).natDegree=3 := by
  rw [← minpoly.eq_of_irreducible hp hx,
    natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hp.ne_zero))]
  exact hd
lemma degree_three_irrational {x : ℝ} (hd : (minpoly ℚ x).natDegree=3) : Irrational x := by
  intro h
  have he : (minpoly ℚ x).natDegree=1 := minpoly.natDegree_eq_one_iff.mpr h
  omega

lemma boundary_aeval : (PB.map (Int.castRingHom ℚ)).aeval
    (CombineV22Optimality.boundary CombineV22Optimality.xiInf)=0 := by
  simpa [sub_eq_add_neg,PB,Polynomial.aeval_def,eval₂_add,eval₂_mul,eval₂_pow,eval₂_C,eval₂_X] using boundary_root
lemma b_aeval : (Pb.map (Int.castRingHom ℚ)).aeval
    (CombineV22.Uniform.b CombineV22Optimality.xiInf)=0 := by
  simpa [sub_eq_add_neg,Pb,Polynomial.aeval_def,eval₂_add,eval₂_mul,eval₂_pow,eval₂_C,eval₂_X] using b_root
lemma boundary_degree :
    (minpoly ℚ (CombineV22Optimality.boundary CombineV22Optimality.xiInf)).natDegree=3 := by
  apply root_minpoly_degree PB_rat_irreducible boundary_aeval
  rw [natDegree_map_eq_of_injective (Int.cast_injective)]
  exact natDegree_cubic (by norm_num)
lemma b_degree :
    (minpoly ℚ (CombineV22.Uniform.b CombineV22Optimality.xiInf)).natDegree=3 := by
  apply root_minpoly_degree Pb_rat_irreducible b_aeval
  rw [natDegree_map_eq_of_injective (Int.cast_injective)]
  exact natDegree_cubic (by norm_num)
lemma boundary_irrational : Irrational (CombineV22Optimality.boundary CombineV22Optimality.xiInf) :=
  degree_three_irrational boundary_degree
lemma b_irrational : Irrational (CombineV22.Uniform.b CombineV22Optimality.xiInf) :=
  degree_three_irrational b_degree
#print axioms boundary_degree
#print axioms b_degree
#print axioms boundary_irrational
#print axioms b_irrational

def Pl : ℤ[X] := C 657*X^3+C (-954)*X^2+C 21*X+C 20
def modl : (ZMod 7)[X] := C 6*X^3+C 5*X^2+C 0*X+C 6
lemma map_Pl : Pl.map (Int.castRingHom (ZMod 7))=modl := by
  have h0 : (657:ZMod 7)=6 := by decide
  have h1 : (-954:ZMod 7)=5 := by decide
  have h2 : (21:ZMod 7)=0 := by decide
  have h3 : (20:ZMod 7)=6 := by decide
  simp only [Pl,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X]
  change C (657:ZMod 7)*X^3+C (-954)*X^2+C 21*X+C 20=modl
  rw [h0,h1,h2,h3]
  rfl
lemma modl_no_root (x : ZMod 7) : ¬ modl.IsRoot x := by
  simp only [IsRoot,modl,eval_add,eval_mul,eval_pow,eval_C,eval_X]
  fin_cases x <;> decide
lemma modl_irreducible : Irreducible modl := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have h : modl.natDegree=3 := natDegree_cubic (by decide : (6:ZMod 7)≠0)
    simp [h]
  · exact modl_no_root
lemma Pl_primitive : Pl.IsPrimitive := by
  intro r hr
  have h0 := (C_dvd_iff_dvd_coeff r Pl).mp hr 0
  have h3 := (C_dvd_iff_dvd_coeff r Pl).mp hr 3
  norm_num [Pl,coeff_X] at h0 h3
  apply isUnit_of_dvd_one
  have h := dvd_add (dvd_mul_of_dvd_right h0 (230:ℤ)) (dvd_mul_of_dvd_right h3 (-7:ℤ))
  norm_num at h
  exact h
lemma Pl_irreducible : Irreducible Pl := by
  apply primitive_irreducible_of_map (Int.castRingHom (ZMod 7)) Pl_primitive
  · have hh : Pl.leadingCoeff = 657 := leadingCoeff_cubic (by norm_num)
    rw [hh]
    decide
  · rw [map_Pl]; exact modl_irreducible
lemma Pl_rat_irreducible : Irreducible (Pl.map (Int.castRingHom ℚ)) :=
  (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast Pl_primitive).mp Pl_irreducible
lemma ell_boundary_relation (t : ℝ) (ht : CombineV22.Uniform.InInterval t) :
    CombineV22.Uniform.ell t=11/3-4*CombineV22Optimality.boundary t := by
  have he : CombineV22Optimality.boundary t=CombineV22.Uniform.boundary t := by
    unfold CombineV22Optimality.boundary CombineV22.Uniform.boundary
    congr 1 <;> ring
  rw [he,CombineV22.Uniform.geometry_boundary t ht]
  ring
lemma ell_root :
    657*(CombineV22.Uniform.ell CombineV22Optimality.xiInf)^3-
      954*(CombineV22.Uniform.ell CombineV22Optimality.xiInf)^2+
      21*CombineV22.Uniform.ell CombineV22Optimality.xiInf+20=0 := by
  rw [ell_boundary_relation _ CombineV22Optimality.xiInf_mem_small]
  linear_combination (-16/3:ℝ)*boundary_root
lemma ell_aeval : (Pl.map (Int.castRingHom ℚ)).aeval
    (CombineV22.Uniform.ell CombineV22Optimality.xiInf)=0 := by
  simpa [sub_eq_add_neg,Pl,Polynomial.aeval_def,eval₂_add,eval₂_mul,eval₂_pow,eval₂_C,eval₂_X] using ell_root
lemma ell_degree :
    (minpoly ℚ (CombineV22.Uniform.ell CombineV22Optimality.xiInf)).natDegree=3 := by
  apply root_minpoly_degree Pl_rat_irreducible ell_aeval
  rw [natDegree_map_eq_of_injective (Int.cast_injective)]
  exact natDegree_cubic (by norm_num)
lemma ell_irrational : Irrational (CombineV22.Uniform.ell CombineV22Optimality.xiInf) :=
  degree_three_irrational ell_degree

lemma root_finrank {p : ℚ[X]} {x : ℝ} (hp : Irreducible p)
    (hx : p.aeval x=0) (hd : p.natDegree=3) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {x})=3 := by
  have hi : IsIntegral ℚ x := ⟨p*C p.leadingCoeff⁻¹,
    monic_mul_leadingCoeff_inv hp.ne_zero, by
      change (aeval x) (p*C p.leadingCoeff⁻¹)=0
      rw [map_mul,hx,zero_mul]⟩
  rw [IntermediateField.adjoin.finrank hi]
  exact root_minpoly_degree hp hx hd
lemma boundary_field_degree :
    Module.finrank ℚ (IntermediateField.adjoin ℚ
      {CombineV22Optimality.boundary CombineV22Optimality.xiInf})=3 := by
  apply root_finrank PB_rat_irreducible boundary_aeval
  rw [natDegree_map_eq_of_injective (Int.cast_injective)]
  exact natDegree_cubic (by norm_num)
lemma b_field_degree :
    Module.finrank ℚ (IntermediateField.adjoin ℚ
      {CombineV22.Uniform.b CombineV22Optimality.xiInf})=3 := by
  apply root_finrank Pb_rat_irreducible b_aeval
  rw [natDegree_map_eq_of_injective (Int.cast_injective)]
  exact natDegree_cubic (by norm_num)
lemma ell_field_degree :
    Module.finrank ℚ (IntermediateField.adjoin ℚ
      {CombineV22.Uniform.ell CombineV22Optimality.xiInf})=3 := by
  apply root_finrank Pl_rat_irreducible ell_aeval
  rw [natDegree_map_eq_of_injective (Int.cast_injective)]
  exact natDegree_cubic (by norm_num)
#print axioms ell_irrational
#print axioms boundary_field_degree
#print axioms b_field_degree
#print axioms ell_field_degree

end
end CombineV22.AlgebraicParameters

end PartIVBlock12

/- BEGIN consolidated SystemEndpoint.lean -/
section PartIVBlock13

namespace CombineV22.SystemEndpoint
noncomputable section
open RHBootstrapCount
open CombineV22Optimality
open CombineV22.System
namespace U
abbrev kap := CombineV22.Uniform.kappa
end U

lemma kap_eq (t : ℝ) : kap t = Uniform.kappa t := by
  unfold kap denom Uniform.kappa
  congr 1 <;> ring
lemma boundary_eq (t : ℝ) : boundary t = Uniform.boundary t := by
  unfold boundary Uniform.boundary
  congr 1 <;> ring

lemma shifted_count (t d u : ℝ) (ht : Uniform.InInterval t) :
    countR (5/6) (2/(3*Uniform.kappa t)) d u = Uniform.R t d (1/2-u) := by
  rw [← Uniform.moment_coefficient t ht]
  have hD : D (Uniform.c t) u = Uniform.D t (1/2-u) := by unfold D Uniform.D; ring
  have hP : P (Uniform.c t) u = Uniform.P t (1/2-u) := by unfold P Uniform.P; ring
  have hJ : J (5/6) (Uniform.c t) d u = Uniform.J t d (1/2-u) := by
    unfold J Uniform.J; rw [hD,hP]
  unfold countR Uniform.R
  rw [hP,hJ]

lemma all_central (t d u z : ℝ) (ht : Uniform.InInterval t)
    (hd : 0 ≤ d) (hd1 : d ≤ 5/6) (_hu : 0 ≤ u) (hu1 : u ≤ 1/2) :
    physical (boundary t) (Uniform.lx t) (Uniform.ly t) (Uniform.ell t)
      d (d*u) (countR (5/6) (2/(3*kap t)) d u) z (1-Uniform.lx t+Uniform.ell t) ≤ 0 := by
  have he := Uniform.universal_endpoint t d (1/2-u) ht hd hd1 (by linarith)
  rw [kap_eq,shifted_count t d u ht,boundary_eq]
  convert he using 1
  unfold physical Uniform.E
  rw [Uniform.geometry_boundary t ht,Uniform.geometry_h t ht,
    Uniform.geometry_C0 t ht,Uniform.geometry_ly t ht,Uniform.geometry_lx t ht]
  ring

lemma full_direct_eq (t : ℝ) (ht : Uniform.InInterval t) :
    fullLow (Uniform.lx t) (Uniform.ly t) (Uniform.ell t) = boundary t := by
  obtain ⟨hb,he,he1,hx,hgram,_⟩ := Uniform.side_reserves t ht
  have hxy : Uniform.lx t+Uniform.ly t = 1-Uniform.ell t := by
    rw [Uniform.geometry_ly t ht,Uniform.geometry_lx t ht]; ring
  have hdiff : Uniform.ly t-Uniform.lx t = Uniform.b t := by
    rw [Uniform.geometry_ly t ht]; ring
  have hk0 : fullK (Uniform.lx t+Uniform.ly t) (Uniform.ell t) = 0 := by
    have h1 : (1+3*Uniform.ell t-2*(Uniform.lx t+Uniform.ly t))/4 ≤ 0 := by
      rw [hxy]; linarith
    have h2 : Uniform.lx t+Uniform.ly t+Uniform.ell t-1 = 0 := by rw [hxy]; ring
    have h3 : (3*Uniform.ell t-1)/2 ≤ 0 := by linarith
    rw [fullK,max_eq_left h1,h2,max_eq_left h3,max_self]
  have hg : fullG (Uniform.lx t) (Uniform.ly t) = Uniform.b t/12 := by
    unfold fullG
    rw [hdiff,max_eq_right (by linarith : 0 ≤ Uniform.b t/12),max_eq_left (by linarith)]
  unfold fullLow
  rw [hk0,hg,boundary_eq,Uniform.geometry_boundary t ht,Uniform.geometry_lx t ht]
  ring

def dataAt (x : ℝ) (hx : Uniform.InInterval x)
    (hcompat : boundary x ≤ (1+kap x)/2) : ComparisonData := by
  have hxi : x ∈ Set.Icc (19/50:ℝ) (39/100:ℝ) := by
    constructor <;> linarith [hx.1,hx.2]
  have hk : 13/18 ≤ kap x ∧ kap x ≤ 1 := by
    rw [kap_eq]
    constructor <;> linarith [Uniform.kappa_lower_lower x hx, Uniform.kappa_upper_lower x hx]
  have hk0 : 0 < kap x := by linarith [hk.1]
  have hc0 : 0 < 2/(3*kap x) := by positivity
  have hc1 : 2/(3*kap x) < 1 := by
    apply (div_lt_iff₀ (by positivity : 0 < 3*kap x)).2
    linarith [hk.1]
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hx1 : x < 5/6 := by linarith [hx.2]
  have hr : critical (kap x) x = 0 :=
    (critical_iff_kap (kap x) x (denom_pos hxi).ne').2 rfl
  have hcut := tstar_range (5/6) (2/(3*kap x)) x (1/2) hc0 hc1
    (by norm_num) (by norm_num) hx0 hx1
  have hheight : 0 < 1-Uniform.lx x+Uniform.ell x := by
    obtain ⟨hb,he,_⟩ := Uniform.side_reserves x hx
    rw [Uniform.geometry_lx x hx]
    linarith
  refine {
    k := kap x
    x := x
    lx := Uniform.lx x
    ly := Uniform.ly x
    ell := Uniform.ell x
    B := boundary x
    t := tstar (5/6) (2/(3*kap x)) x (1/2)
    C := 2/3
    z := 17/50
    k_lower := hk.1
    k_upper := by linarith [hk.2]
    x_interval := hxi
    critical_root := hr
    endpoint := hcompat
    cutoff_lower := hcut.1
    cutoff_upper := hcut.2
    height_positive := hheight
    direct := (full_direct_eq x hx).le
    count_certificate := ?_
  }
  have hcount := balanced_count_certificate (2/(3*kap x)) x hc0 hc1 hx0 hx1
  rw [critical_count_eq (kap x) x hk.1 (by linarith [hk.2]) hxi hr] at hcount
  exact hcount


def rootData : ComparisonData := dataAt xiInf xiInf_mem_small (by linarith [root_fixed_point])

lemma rootData_boundary : rootData.B = boundary xiInf := rfl

def certificateAt (x : ℝ) (hx : Uniform.InInterval x)
    (hcompat : boundary x ≤ (1+kap x)/2) : DisplayedCertificate := by
  have hxi : x ∈ Set.Icc (19/50:ℝ) (39/100:ℝ) := by
    constructor <;> linarith [hx.1,hx.2]
  have hk : 13/18 ≤ kap x ∧ kap x ≤ 1 := by
    rw [kap_eq]
    constructor <;> linarith [Uniform.kappa_lower_lower x hx,Uniform.kappa_upper_lower x hx]
  have hs := Uniform.side_reserves x hx
  have hb := hs.1
  have he := hs.2.1
  have hxres := hs.2.2.2.1
  refine {
    toComparisonData := dataAt x hx hcompat
    ell_positive := he
    lx_gt_ell := by change Uniform.ell x < Uniform.lx x; linarith
    ly_gt_lx := by
      change Uniform.lx x < Uniform.ly x
      rw [Uniform.geometry_ly x hx]
      linarith
    comparison := Or.inl ?_
  }
  change physical (boundary x) (Uniform.lx x) (Uniform.ly x) (Uniform.ell x)
    x (x/2) (2/3) (17/50) (1-Uniform.lx x+Uniform.ell x) ≤ 0
  have he := all_central x x (1/2) (17/50) hx
    (by linarith [hxi.1]) (by linarith [hxi.2]) (by norm_num) (by norm_num)
  have hr : critical (kap x) x = 0 :=
    (critical_iff_kap _ _ (denom_pos hxi).ne').2 rfl
  rw [critical_count_eq _ _ hk.1 (by linarith [hk.2]) hxi hr] at he
  simpa only [div_eq_mul_inv,one_mul] using he


def rootCertificate : DisplayedCertificate :=
  certificateAt xiInf xiInf_mem_small (by linarith [root_fixed_point])

/-- Besides satisfying all five-alternative necessity conditions, the attaining
geometry supplies every central deficit/amplitude comparison, not just the critical class. -/
theorem root_all_classes (d u z : ℝ) (hd : 0 ≤ d) (hd1 : d ≤ 5/6)
    (hu : 0 ≤ u) (hu1 : u ≤ 1/2) :
    physical rootCertificate.B rootCertificate.lx rootCertificate.ly rootCertificate.ell
      d (d*u) (countR (5/6) (2/(3*rootCertificate.k)) d u) z
      (1-rootCertificate.lx+rootCertificate.ell) ≤ 0 :=
  all_central xiInf d u z xiInf_mem_small hd hd1 hu hu1

theorem displayed_system_infimum :
    sInf (Set.range (fun q : DisplayedCertificate => q.B)) = boundary xiInf := by
  have hmem : boundary xiInf ∈ Set.range (fun q : DisplayedCertificate => q.B) :=
    ⟨rootCertificate,rfl⟩
  have hlow : ∀ b ∈ Set.range (fun q : DisplayedCertificate => q.B), boundary xiInf ≤ b := by
    rintro b ⟨q,rfl⟩
    exact displayed_certificate_lower_bound q
  exact le_antisymm (csInf_le ⟨boundary xiInf,hlow⟩ hmem)
    (le_csInf ⟨boundary xiInf,hmem⟩ hlow)

/-- The critical-class relaxation strengthened by the complete balanced central
comparison on every deficit/amplitude class. This is an explicit scalar system;
it does not encode every analytic hypothesis in the manuscript's class A. -/
structure FullCentralCertificate extends DisplayedCertificate where
  central_for_all : ∀ d u z : ℝ, 0≤ d → d≤5/6 → 0≤ u → u≤1/2 →
    physical B lx ly ell d (d*u) (countR (5/6) (2/(3*k)) d u) z (1-lx+ell) ≤ 0

def fullCertificateAt (x : ℝ) (hx : Uniform.InInterval x)
    (hc : boundary x≤(1+kap x)/2) : FullCentralCertificate where
  toDisplayedCertificate := certificateAt x hx hc
  central_for_all := by
    intro d u z hd0 hd1 hu0 hu1
    exact all_central x d u z hx hd0 hd1 hu0 hu1

def rootFullCertificate : FullCentralCertificate :=
  fullCertificateAt xiInf xiInf_mem_small (by linarith [root_fixed_point])

theorem full_central_system_infimum :
    sInf (Set.range (fun q : FullCentralCertificate => q.B)) = boundary xiInf := by
  have hmem : boundary xiInf ∈ Set.range (fun q : FullCentralCertificate => q.B) :=
    ⟨rootFullCertificate,rfl⟩
  have hlow : ∀ B ∈ Set.range (fun q : FullCentralCertificate => q.B), boundary xiInf ≤ B := by
    rintro B ⟨q,rfl⟩
    exact displayed_certificate_lower_bound q.toDisplayedCertificate
  exact le_antisymm (csInf_le ⟨boundary xiInf,hlow⟩ hmem)
    (le_csInf ⟨boundary xiInf,hmem⟩ hlow)

/-- Every fixed scalar construction parameter belongs to the embedded rational field. -/
def RationalParameters (q : DisplayedCertificate) : Prop :=
  q.k ∈ (⊥ : IntermediateField ℚ ℝ) ∧ q.x ∈ (⊥ : IntermediateField ℚ ℝ) ∧
  q.lx ∈ (⊥ : IntermediateField ℚ ℝ) ∧ q.ly ∈ (⊥ : IntermediateField ℚ ℝ) ∧
  q.ell ∈ (⊥ : IntermediateField ℚ ℝ) ∧ q.B ∈ (⊥ : IntermediateField ℚ ℝ) ∧
  q.t ∈ (⊥ : IntermediateField ℚ ℝ) ∧ q.C ∈ (⊥ : IntermediateField ℚ ℝ) ∧
  q.z ∈ (⊥ : IntermediateField ℚ ℝ)

lemma certificateAt_rational (q : ℚ) (hx : Uniform.InInterval (q:ℝ))
    (hc : boundary (q:ℝ) ≤ (1+kap (q:ℝ))/2) :
    RationalParameters (certificateAt (q:ℝ) hx hc) := by
  let F : IntermediateField ℚ ℝ := ⊥
  have hq : (q:ℝ) ∈ F := F.algebraMap_mem q
  change kap (q:ℝ) ∈ F ∧ (q:ℝ) ∈ F ∧ Uniform.lx (q:ℝ) ∈ F ∧
    Uniform.ly (q:ℝ) ∈ F ∧ Uniform.ell (q:ℝ) ∈ F ∧ boundary (q:ℝ) ∈ F ∧
    tstar (5/6) (2/(3*kap (q:ℝ))) (q:ℝ) (1/2) ∈ F ∧ (2/3:ℝ) ∈ F ∧ (17/50:ℝ) ∈ F
  refine ⟨?_,hq,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals try simp only [kap,denom,Uniform.lx,Uniform.ly,Uniform.ell,boundary,tstar,J,D,P]
  all_goals repeat' first
    | exact hq
    | exact F.one_mem
    | exact F.zero_mem
    | exact F.natCast_mem _
    | apply F.inv_mem
    | apply pow_mem
    | apply F.add_mem
    | apply F.sub_mem
    | apply F.mul_mem
    | apply F.div_mem
    | apply neg_mem

lemma boundary_lipschitz (x y : ℝ) (hx : 0≤ x) (hy : 0≤ y) (hxy : x≤ y) :
    boundary y-boundary x ≤ y-x := by
  let dx := 18*x+9
  let dy := 18*y+9
  let nx := 18*x+7
  let ny := 18*y+7
  have hdx : 0< dx := by dsimp [dx]; linarith
  have hdy : 0< dy := by dsimp [dy]; linarith
  have he : (boundary y-boundary x)*(dx*dy)=36*(y-x) := by
    change (ny/dy-nx/dx)*(dx*dy)=36*(y-x)
    field_simp [hdx.ne',hdy.ne']
    dsimp [dx,dy,nx,ny]
    ring
  have hd : 36 ≤ dx*dy := by dsimp [dx,dy]; nlinarith [mul_nonneg hx hy]
  have hprod : 0< dx*dy := mul_pos hdx hdy
  rw [(eq_div_iff hprod.ne').2 he]
  apply (div_le_iff₀ hprod).2
  calc
    36*(y-x) ≤ (dx*dy)*(y-x) := mul_le_mul_of_nonneg_right hd (sub_nonneg.mpr hxy)
    _ = (y-x)*(dx*dy) := by ring

lemma compatible_of_root_le (x : ℝ) (hx : Uniform.InInterval x) (hle : xiInf≤ x) :
    boundary x ≤ (1+kap x)/2 := by
  have hw : x ∈ Set.Icc (19/50:ℝ) (39/100:ℝ) := by
    constructor <;> linarith [hx.1,hx.2]
  have hp : cubic x ≤ 0 := (cubic_nonpos_iff x hw).2 hle
  have hd := denom_pos hw
  have hden : 0<18*(2*x+1)*denom x := by
    have hx0 : 0< x := by linarith [hw.1]
    positivity
  have hf := fixed_point_identity x (boundary_den_pos hw).ne' hd.ne'
  have hn := div_nonneg (neg_nonneg.mpr hp) hden.le
  linarith

lemma rational_cap_above : xiInf < (3885836/10000000:ℝ) := by
  have hc : cubic (3885836/10000000:ℝ)<0 := by norm_num [cubic]
  have hm : (3885836/10000000:ℝ) ∈ Set.Icc (19/50:ℝ) (39/100:ℝ) := by norm_num
  have hh : xiInf≤(3885836/10000000:ℝ) := (cubic_nonpos_iff _ hm).1 hc.le
  by_contra hn
  have he : xiInf=(3885836/10000000:ℝ) := le_antisymm hh (le_of_not_gt hn)
  rw [← he,cubic_xiInf] at hc
  linarith

/-- Rational certificates approach the algebraic optimum from above, with κ<3/4
and the complete uniform family endpoint certificate. -/
theorem rational_certificates_approach (epsilon : ℝ) (hepsilon : 0< epsilon) :
    ∃ q : FullCentralCertificate, RationalParameters q.toDisplayedCertificate ∧ q.k<3/4 ∧
      q.B < boundary xiInf+epsilon := by
  have hm : xiInf < min (3885836/10000000:ℝ) (xiInf+epsilon) :=
    lt_min rational_cap_above (by linarith)
  obtain ⟨r,hr0,hr1⟩ := exists_rat_btwn hm
  have hrU := lt_of_lt_of_le hr1 (min_le_left _ _)
  have hrE := lt_of_lt_of_le hr1 (min_le_right _ _)
  have hi : Uniform.InInterval (r:ℝ) := by
    constructor <;> linarith [xiInf_mem_small.1]
  have hc := compatible_of_root_le (r:ℝ) hi hr0.le
  refine ⟨fullCertificateAt (r:ℝ) hi hc,certificateAt_rational r hi hc,?_,?_⟩
  · change kap (r:ℝ)<3/4
    have hw : (r:ℝ) ∈ Set.Icc (19/50:ℝ) (39/100:ℝ) := by
      constructor <;> linarith [hi.1,hi.2]
    have hcW : (3885836/10000000:ℝ) ∈ Set.Icc (19/50:ℝ) (39/100:ℝ) := by norm_num
    have hk := kap_strictMono hw hcW hrU
    have hkU : kap (3885836/10000000:ℝ)<3/4 := by norm_num [kap,denom]
    linarith
  · change boundary (r:ℝ)< boundary xiInf+epsilon
    have hL := boundary_lipschitz xiInf (r:ℝ)
      (by linarith [xiInf_mem_small.1]) (by linarith [hi.1]) hr0.le
    linarith

def rationalValues : Set ℝ :=
  {B | ∃ q : FullCentralCertificate, RationalParameters q.toDisplayedCertificate ∧ q.B=B}

theorem rational_system_infimum : sInf rationalValues = boundary xiInf := by
  have hnonempty : rationalValues.Nonempty := by
    obtain ⟨q,hq,_,_⟩ := rational_certificates_approach 1 (by norm_num)
    exact ⟨q.B,q,hq,rfl⟩
  have hlower : ∀ B∈rationalValues, boundary xiInf≤ B := by
    rintro B ⟨q,_,rfl⟩
    exact displayed_certificate_lower_bound q.toDisplayedCertificate
  have hbdd : BddBelow rationalValues := ⟨boundary xiInf,hlower⟩
  apply le_antisymm ?_ (le_csInf hnonempty hlower)
  by_contra hn
  have he : 0< sInf rationalValues-boundary xiInf := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨q,hq,_,hB⟩ := rational_certificates_approach
    (sInf rationalValues-boundary xiInf) he
  have hle : sInf rationalValues≤ q.B := csInf_le hbdd ⟨q,hq,rfl⟩
  linarith

lemma boundary_strictMono : StrictMonoOn boundary (Set.Icc (19/50:ℝ) (39/100:ℝ)) := by
  intro x hx y hy hxy
  unfold boundary
  apply (div_lt_div_iff₀ (boundary_den_pos hx) (boundary_den_pos hy)).2
  nlinarith

lemma full_three_branches (q : FullCentralCertificate) :
    low₀ (q.lx+q.ly) q.ell≤ q.B ∧ CombineV22Optimality.lowK (q.lx+q.ly) q.ell≤ q.B ∧
    high q.x (q.lx+q.ly) q.ell≤ q.B := by
  obtain ⟨h0,hK⟩ := full_direct_branches q.lx q.ly q.ell q.B q.direct
  have he := q.central_for_all q.x (1/2) q.z (by linarith [q.x_interval.1])
    (by linarith [q.x_interval.2]) (by norm_num) (by norm_num)
  rw [critical_count_eq q.k q.x q.k_lower q.k_upper q.x_interval q.critical_root] at he
  have he' : physical q.B q.lx q.ly q.ell q.x (q.x/2) (2/3) q.z
      (1-q.lx+q.ell)≤0 := by simpa only [div_eq_mul_inv,one_mul] using he
  exact ⟨h0,hK,critical_necessary_branch q.B q.lx q.ly q.ell q.x (2/3) q.z
    q.height_positive (le_refl _) he'⟩

/-- Equality in the full central system forces the unique critical deficit and
length; in particular rational lengths cannot attain the optimum. -/
theorem equality_rigidity (q : FullCentralCertificate) (hB : q.B=boundary xiInf) :
    q.x=xiInf ∧ q.ell=Uniform.ell xiInf := by
  obtain ⟨h0,hK,hH⟩ := full_three_branches q
  have hopt := endpoint_compatible_optimality q.k q.x (q.lx+q.ly) q.ell q.B
    q.x_interval q.critical_root h0 hK hH q.endpoint
  have hk : q.k=kap q.x :=
    (critical_iff_kap q.k q.x (denom_pos q.x_interval).ne').1 q.critical_root
  have hlo : xiInf≤ q.x := by
    by_contra hn
    have hh := kap_strictMono q.x_interval xiInf_mem (lt_of_not_ge hn)
    rw [← hk] at hh
    linarith [hopt.1]
  have hhi : q.x≤ xiInf := by
    by_contra hn
    have hh := boundary_strictMono xiInf_mem q.x_interval (lt_of_not_ge hn)
    have hdual := dual_lower_bound q.x (q.lx+q.ly) q.ell q.B q.x_interval h0 hK hH
    rw [hB] at hdual
    linarith
  have heqx : q.x=xiInf := le_antisymm hhi hlo
  refine ⟨heqx,?_⟩
  rw [hB] at h0 hK hH
  rw [heqx] at hH
  have hd := boundary_den_pos xiInf_mem
  have hs := (div_eq_iff hd.ne').1 (dual_identity xiInf (q.lx+q.ly) q.ell hd.ne')
  have hw : 0<4+18*xiInf := by linarith [xiInf_mem_small.1]
  have hm : (4+18*xiInf)*(boundary xiInf-low₀ (q.lx+q.ly) q.ell)≤0 := by
    nlinarith only [hs,hK,hH]
  have hz : boundary xiInf-low₀ (q.lx+q.ly) q.ell≤0 :=
    nonpos_of_mul_nonpos_right hm hw
  have he0 : low₀ (q.lx+q.ly) q.ell=boundary xiInf := by linarith
  rw [he0] at hs
  have heK : CombineV22Optimality.lowK (q.lx+q.ly) q.ell=boundary xiInf := by
    nlinarith only [hs,hH,hK]
  obtain ⟨hr0,hrK,_⟩ := equal_branches xiInf hd.ne'
  have hell : q.ell=length xiInf := by
    simp only [low₀,CombineV22Optimality.lowK] at he0 heK hr0 hrK
    linarith
  rw [hell]
  unfold length Uniform.ell
  congr 1 <;> ring

theorem rational_length_not_attaining (q : FullCentralCertificate)
    (hq : q.ell ∈ (⊥ : IntermediateField ℚ ℝ)) : q.B≠boundary xiInf := by
  intro hB
  rw [(equality_rigidity q hB).2] at hq
  exact AlgebraicParameters.ell_irrational (IntermediateField.mem_bot.mp hq)

theorem rational_system_not_attaining (q : FullCentralCertificate)
    (hq : RationalParameters q.toDisplayedCertificate) : q.B≠boundary xiInf :=
  rational_length_not_attaining q hq.2.2.2.2.1

/-- Even allowing arbitrary real values for every parameter except ell, the
infimum is unchanged and is not attained. -/
def rationalLengthValues : Set ℝ :=
  {B | ∃ q : FullCentralCertificate, q.ell ∈ (⊥ : IntermediateField ℚ ℝ) ∧ q.B=B}

theorem rational_lengths_infimum : sInf rationalLengthValues=boundary xiInf := by
  have hnonempty : rationalLengthValues.Nonempty := by
    obtain ⟨q,hq,_,_⟩ := rational_certificates_approach 1 (by norm_num)
    exact ⟨q.B,q,hq.2.2.2.2.1,rfl⟩
  have hlower : ∀ B∈rationalLengthValues, boundary xiInf≤ B := by
    rintro B ⟨q,_,rfl⟩
    exact displayed_certificate_lower_bound q.toDisplayedCertificate
  have hbdd : BddBelow rationalLengthValues := ⟨boundary xiInf,hlower⟩
  apply le_antisymm ?_ (le_csInf hnonempty hlower)
  by_contra hn
  have he : 0< sInf rationalLengthValues-boundary xiInf := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨q,hq,_,hB⟩ := rational_certificates_approach
    (sInf rationalLengthValues-boundary xiInf) he
  have hle : sInf rationalLengthValues≤ q.B := csInf_le hbdd ⟨q,hq.2.2.2.2.1,rfl⟩
  linarith

#print axioms equality_rigidity
#print axioms rational_length_not_attaining
#print axioms rational_lengths_infimum

#print axioms full_central_system_infimum
#print axioms rational_certificates_approach
#print axioms rational_system_infimum

#print axioms full_direct_eq
#print axioms root_all_classes
#print axioms displayed_system_infimum
end
end CombineV22.SystemEndpoint

end PartIVBlock13

/- BEGIN consolidated Iteration.lean -/
section PartIVBlock14

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 0
namespace CombineV22.Iteration
noncomputable section
open Filter Set
open scoped Topology
open CombineV22.Uniform

lemma kappa_hasDerivAt (t : ℝ) (ht : InInterval t) :
    HasDerivAt kappa (kappa_derivative t) t := by
  have hd : 150+(-468)*t+216*t^2 ≠ 0 := by
    have hp := base3_pos t ht
    nlinarith
  have hn := ((hasDerivAt_const t (20:ℝ)).add ((hasDerivAt_id t).const_mul (-57))).add
    (((hasDerivAt_id t).pow 2).const_mul 18)
  have hh := ((hasDerivAt_const t (150:ℝ)).add ((hasDerivAt_id t).const_mul (-468))).add
    (((hasDerivAt_id t).pow 2).const_mul 216)
  convert hn.div hh hd using 1
  · rfl
  · dsimp
    unfold kappa_derivative
    have hbase := (base3_pos t ht).ne'
    have hs := sq_pos_of_pos (base3_pos t ht)
    have hdsq := sq_pos_of_pos (show 0 < 150+(-468)*t+216*t^2 by nlinarith [base3_pos t ht])
    ring_nf at hd hbase hs hdsq
    field_simp <;> ring_nf <;> field_simp <;> ring

lemma boundary_hasDerivAt (t : ℝ) (ht : InInterval t) :
    HasDerivAt boundary (boundary_derivative t) t := by
  have hd : 9+18*t ≠ 0 := by linarith [base0_pos t ht]
  have hn := (hasDerivAt_const t (7:ℝ)).add ((hasDerivAt_id t).const_mul 18)
  have hh := (hasDerivAt_const t (9:ℝ)).add ((hasDerivAt_id t).const_mul 18)
  convert hn.div hh hd using 1
  · rfl
  · dsimp
    unfold boundary_derivative
    have hbase := (base0_pos t ht).ne'
    have hdsq := sq_pos_of_pos (show 0 < 9+18*t by linarith [base0_pos t ht])
    have hbsq := sq_pos_of_pos (base0_pos t ht)
    ring_nf at hd hbase hdsq hbsq
    field_simp <;> ring_nf <;> field_simp <;> ring

lemma contraction_identity (t : ℝ) (ht : InInterval t) :
    kappa_derivative t-1000*boundary_derivative t=contraction_derivative t := by
  have h0 := (base0_pos t ht).ne'
  have h3 := (base3_pos t ht).ne'
  unfold kappa_derivative boundary_derivative contraction_derivative
  have h0s := sq_pos_of_pos (base0_pos t ht)
  have h3s := sq_pos_of_pos (base3_pos t ht)
  have hprod := mul_pos h0s h3s
  ring_nf at h0 h3 h0s h3s hprod
  field_simp <;> ring_nf <;> field_simp <;> ring

lemma derivative_bounds (t : ℝ) (ht : InInterval t) :
    0 < deriv kappa t ∧ 0 < deriv boundary t ∧
    1000*deriv boundary t < deriv kappa t := by
  rw [(kappa_hasDerivAt t ht).deriv,(boundary_hasDerivAt t ht).deriv]
  have hk := kappa_derivative_lower t ht
  have hb := boundary_derivative_lower t ht
  have hc := contraction_derivative_lower t ht
  rw [← contraction_identity t ht] at hc
  constructor
  · linarith
  constructor <;> linarith

lemma contraction_ratio (t : ℝ) (ht : InInterval t) :
    0 < 2*deriv boundary t/deriv kappa t ∧
    2*deriv boundary t/deriv kappa t < (1/500:ℝ) := by
  obtain ⟨hk,hb,hc⟩ := derivative_bounds t ht
  constructor
  · positivity
  · apply (div_lt_iff₀ hk).2
    linarith

#print axioms kappa_hasDerivAt
#print axioms boundary_hasDerivAt
#print axioms contraction_ratio

lemma kap_eq : CombineV22Optimality.kap = kappa := by
  funext t
  unfold CombineV22Optimality.kap CombineV22Optimality.denom kappa
  congr 1 <;> ring
lemma boundary_eq : CombineV22Optimality.boundary = boundary := by
  funext t
  unfold CombineV22Optimality.boundary boundary
  congr 1 <;> ring

open CombineV22Optimality (kap xiInf critical critical_root_exists critical_iff_kap
  denom denom_pos xiInf_mem xiInf_mem_small kap_xiInf_range root_fixed_point
  kap_strictMono boundary_monotone boundary_den_pos fixed_point_identity
  cubic cubic_xiInf cubic_strictAnti root_unique)
abbrev B := CombineV22Optimality.boundary

def Valid (k : ℝ) : Prop := kap xiInf ≤ k ∧ k ≤ 3/4
def inverse (k : ℝ) : ℝ :=
  if hk : k ∈ Icc (13/18:ℝ) 1 then Classical.choose (critical_root_exists k hk) else xiInf

lemma inverse_spec (k : ℝ) (hk : k ∈ Icc (13/18:ℝ) 1) :
    inverse k ∈ Icc (19/50:ℝ) (39/100:ℝ) ∧ kap (inverse k)=k := by
  have hs := Classical.choose_spec (critical_root_exists k hk)
  have he : inverse k=Classical.choose (critical_root_exists k hk) := by simp [inverse,hk]
  rw [he]
  exact ⟨hs.1,((critical_iff_kap _ _ (denom_pos hs.1).ne').mp hs.2).symm⟩

lemma small_large {x : ℝ} (hx : InInterval x) : x ∈ Icc (19/50:ℝ) (39/100:ℝ) := by
  constructor <;> linarith [hx.1,hx.2]

lemma inverse_range (k : ℝ) (hk : Valid k) :
    InInterval (inverse k) ∧ xiInf ≤ inverse k ∧ kap (inverse k)=k := by
  have hkd : k ∈ Icc (13/18:ℝ) 1 := ⟨le_trans kap_xiInf_range.1 hk.1,by linarith [hk.2]⟩
  obtain ⟨hx,hkap⟩ := inverse_spec k hkd
  have hlow : xiInf ≤ inverse k := by
    by_contra hn
    have hm := kap_strictMono hx xiInf_mem (lt_of_not_ge hn)
    linarith [hk.1]
  have hhigh : inverse k ≤ (38859/100000:ℝ) := by
    by_contra hn
    have hU : (38859/100000:ℝ) ∈ Icc (19/50:ℝ) (39/100:ℝ) := by constructor <;> norm_num
    have hkapU : (3/4:ℝ) < kap (38859/100000) := by norm_num [kap,denom]
    have hm := kap_strictMono hU hx (lt_of_not_ge hn)
    linarith [hk.2]
  exact ⟨⟨le_trans xiInf_mem_small.1 hlow,hhigh⟩,hlow,hkap⟩

def next (k : ℝ) : ℝ := 2*B (inverse k)-1
lemma next_bounds (k : ℝ) (hk : Valid k) : kap xiInf ≤ next k ∧ next k ≤ k := by
  obtain ⟨hx,hlo,hkap⟩ := inverse_range k hk
  have hxlarge := small_large hx
  have hb := boundary_monotone xiInf_mem hxlarge hlo
  have hp : cubic (inverse k) ≤ 0 := by
    rcases eq_or_lt_of_le hlo with he | he
    · rw [← he,cubic_xiInf]
    · have hp := cubic_strictAnti xiInf_mem hxlarge he
      rw [cubic_xiInf] at hp
      exact hp.le
  have hden : 0 < 18*(2*inverse k+1)*denom (inverse k) := by
    have hh : 0 < 2*inverse k+1 := by linarith [hx.1]
    exact mul_pos (mul_pos (by norm_num) hh) (denom_pos hxlarge)
  have hf := fixed_point_identity (inverse k) (boundary_den_pos hxlarge).ne' (denom_pos hxlarge).ne'
  have hquot : 0 ≤ -cubic (inverse k)/(18*(2*inverse k+1)*denom (inverse k)) :=
    div_nonneg (neg_nonneg.mpr hp) hden.le
  dsimp [next,B]
  constructor
  · linarith [root_fixed_point]
  · linarith

lemma inverse_mono {a b : ℝ} (ha : Valid a) (hb : Valid b) (hab : a ≤ b) :
    inverse a ≤ inverse b := by
  obtain ⟨hxa,_,hka⟩ := inverse_range a ha
  obtain ⟨hxb,_,hkb⟩ := inverse_range b hb
  by_contra hn
  have h := kap_strictMono (small_large hxb) (small_large hxa) (lt_of_not_ge hn)
  linarith

def K : ℕ → ℝ
  | 0 => 3/4
  | n+1 => next (K n)
def X (n : ℕ) : ℝ := inverse (K n)
def Bseq (n : ℕ) : ℝ := B (X n)
lemma K_valid (n : ℕ) : Valid (K n) := by
  induction n with
  | zero => exact ⟨kap_xiInf_range.2,le_rfl⟩
  | succ n ih =>
    have h := next_bounds (K n) ih
    exact ⟨h.1,le_trans h.2 ih.2⟩
lemma K_antitone : Antitone K := by
  apply antitone_nat_of_succ_le
  intro n
  exact (next_bounds (K n) (K_valid n)).2
lemma X_range (n : ℕ) : InInterval (X n) ∧ xiInf ≤ X n ∧ kap (X n)=K n :=
  inverse_range (K n) (K_valid n)
lemma X_antitone : Antitone X := by
  intro m n hmn
  exact inverse_mono (K_valid n) (K_valid m) (K_antitone hmn)
lemma Bseq_antitone : Antitone Bseq := by
  intro m n hmn
  exact boundary_monotone (small_large (X_range n).1) (small_large (X_range m).1) (X_antitone hmn)
lemma recurrence (n : ℕ) : kap (X (n+1))=2*B (X n)-1 := (X_range (n+1)).2.2
lemma X_bdd : BddBelow (range X) := ⟨xiInf,by rintro _ ⟨n,rfl⟩; exact (X_range n).2.1⟩
def Xlimit : ℝ := ⨅n, X n
lemma Xlimit_bounds : InInterval Xlimit ∧ xiInf ≤ Xlimit := by
  have hl : xiInf ≤ Xlimit := le_ciInf (fun n=>(X_range n).2.1)
  have hu : Xlimit ≤ X 0 := ciInf_le X_bdd 0
  exact ⟨⟨le_trans xiInf_mem_small.1 hl,le_trans hu (X_range 0).1.2⟩,hl⟩
lemma X_tendsto : Tendsto X atTop (𝓝 Xlimit) := tendsto_atTop_ciInf X_antitone X_bdd
lemma kap_continuousAt (t : ℝ) (ht : InInterval t) : ContinuousAt kap t := by
  rw [kap_eq]
  exact (kappa_hasDerivAt t ht).continuousAt
lemma B_continuousAt (t : ℝ) (ht : InInterval t) : ContinuousAt B t := by
  change ContinuousAt CombineV22Optimality.boundary t
  rw [boundary_eq]
  exact (boundary_hasDerivAt t ht).continuousAt
lemma Xlimit_fixed : kap Xlimit=2*B Xlimit-1 := by
  have hk := (kap_continuousAt Xlimit Xlimit_bounds.1).tendsto.comp
    (X_tendsto.comp (tendsto_add_atTop_nat 1))
  have hb := ((B_continuousAt Xlimit Xlimit_bounds.1).tendsto.comp X_tendsto).const_mul 2
  have hb' := hb.sub_const 1
  have he : (fun n=> kap (X (n+1)))=(fun n=>2*B (X n)-1) := funext recurrence
  change Tendsto (fun n=> kap (X (n+1))) atTop (𝓝 (kap Xlimit)) at hk
  rw [he] at hk
  exact tendsto_nhds_unique hk hb'
lemma Xlimit_eq : Xlimit=xiInf := by
  have hx := small_large Xlimit_bounds.1
  have hf := fixed_point_identity Xlimit (boundary_den_pos hx).ne' (denom_pos hx).ne'
  rw [Xlimit_fixed,sub_self] at hf
  have hp : cubic Xlimit=0 := by
    have hh := (div_eq_zero_iff).mp hf.symm
    rcases hh with hh | hh
    · linarith
    · exfalso
      have hlin : 0 < 2*Xlimit+1 := by linarith [hx.1]
      exact (ne_of_gt (mul_pos (mul_pos (by norm_num : (0:ℝ)<18) hlin) (denom_pos hx))) hh
  exact root_unique Xlimit hx hp
lemma X_converges : Tendsto X atTop (𝓝 xiInf) := by simpa only [Xlimit_eq] using X_tendsto
lemma K_converges : Tendsto K atTop (𝓝 (kap xiInf)) := by
  have h := (kap_continuousAt xiInf xiInf_mem_small).tendsto.comp X_converges
  simpa only [Function.comp_def,(X_range _).2.2] using h
lemma Bseq_converges : Tendsto Bseq atTop (𝓝 (B xiInf)) :=
  (B_continuousAt xiInf xiInf_mem_small).tendsto.comp X_converges

#print axioms K_antitone
#print axioms K_converges
#print axioms Bseq_antitone
#print axioms Bseq_converges

lemma X_zero : X 0=RHV2.dc := by
  have hd : RHV2.dc ∈ Icc (19/50:ℝ) (39/100:ℝ) := by
    unfold RHV2.dc
    constructor <;> linarith [RHV2.s_bounds.1,RHV2.s_bounds.2]
  have hp : critical (3/4) RHV2.dc=0 := by
    unfold critical
    nlinarith [RHV2.critical_quadratic]
  have hk : kap RHV2.dc=(3/4:ℝ) :=
    ((critical_iff_kap _ _ (denom_pos hd).ne').mp hp).symm
  apply kap_strictMono.injOn (small_large (X_range 0).1) hd
  rw [(X_range 0).2.2,hk]
  rfl
lemma B_zero : Bseq 0=RHV2.boundary := by
  change B (X 0)=RHV2.boundary
  rw [X_zero]
  unfold B CombineV22Optimality.boundary
  apply (div_eq_iff (show 18*RHV2.dc+9 ≠ 0 by linarith [RHV2.dual_den_pos])).2
  unfold RHV2.dc RHV2.boundary
  ring_nf
  rw [RHV2.s_sq]
  ring

/-- Every finite scalar iterate is available to a supplied one-step theorem.
The actual analytic one-step theorem is instantiated by FinalConclusions. -/
lemma finite_bounds (beta : ℝ) (hinit : beta ≤ (7/8:ℝ))
    (hstep : ∀ t, InInterval t → kap t ≤ (3/4:ℝ) →
      beta ≤ (1+kap t)/2 → beta ≤ B t) :
    ∀ n, beta ≤ (1+K n)/2 ∧ beta ≤ Bseq n := by
  have hp : ∀ n, beta ≤ (1+K n)/2 := by
    intro n
    induction n with
    | zero => norm_num [K]; exact hinit
    | succ n ih =>
      have hs := hstep (X n) (X_range n).1
        (by rw [(X_range n).2.2]; exact (K_valid n).2)
        (by rw [(X_range n).2.2]; exact ih)
      change beta ≤ (1+(2*B (X n)-1))/2
      linarith
  intro n
  exact ⟨hp n,hstep (X n) (X_range n).1
    (by rw [(X_range n).2.2]; exact (K_valid n).2)
    (by rw [(X_range n).2.2]; exact hp n)⟩

lemma long_alpha_hasDerivAt (a d r : ℝ) :
    HasDerivAt (fun v=> RHBootstrapCount.longCount v d r) (r-1) a := by
  have h := ((hasDerivAt_const a (1:ℝ)).sub (hasDerivAt_id a)).add
    (((hasDerivAt_id a).sub_const d).mul_const r)
  convert h using 1
  · rfl
  · ring

lemma count_alpha_hasDerivAt (a c d u : ℝ) (hJ : RHBootstrapCount.J a c d u ≠ 0) :
    HasDerivAt (fun v=> RHBootstrapCount.countR v c d u)
      (d^2*(RHBootstrapCount.P c u)^2/(2*(RHBootstrapCount.J a c d u)^2)) a := by
  have hn := (((hasDerivAt_id a).sub_const d).mul_const d).mul_const (RHBootstrapCount.P c u)
  have hd := ((((hasDerivAt_id a).sub_const d).mul_const (RHBootstrapCount.D c u)).add_const
    (d*RHBootstrapCount.P c u)).const_mul 2
  have hden : 2*RHBootstrapCount.J a c d u ≠ 0 := mul_ne_zero (by norm_num) hJ
  have h := (hasDerivAt_const a (1-d)).add (hn.div hd hden)
  convert h using 1
  · rfl
  · dsimp
    change d^2*(RHBootstrapCount.P c u)^2/(2*(RHBootstrapCount.J a c d u)^2)=
      0+((1*d)*RHBootstrapCount.P c u*(2*RHBootstrapCount.J a c d u)-
        (a-d)*d*RHBootstrapCount.P c u*(2*(1*RHBootstrapCount.D c u)))/
        (2*RHBootstrapCount.J a c d u)^2
    field_simp [hJ]
    unfold RHBootstrapCount.J
    ring

lemma count_alpha_derivative_positive (a c d u : ℝ)
    (hd : 0 < d) (hP : 0 < RHBootstrapCount.P c u) (hJ : RHBootstrapCount.J a c d u ≠ 0) :
    0 < deriv (fun v=> RHBootstrapCount.countR v c d u) a := by
  rw [(count_alpha_hasDerivAt a c d u hJ).deriv]
  have hs : 0 < (RHBootstrapCount.J a c d u)^2 := sq_pos_of_ne_zero hJ
  positivity

#print axioms X_zero
#print axioms B_zero
#print axioms finite_bounds
#print axioms count_alpha_hasDerivAt
#print axioms count_alpha_derivative_positive
#print axioms long_alpha_hasDerivAt
end
end CombineV22.Iteration

end PartIVBlock14

/- BEGIN consolidated variable_moments/FullRangeCount.lean -/
section PartIVBlock15
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.IVFullHeckeDetectorCountFromMoments
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBranchBudget
open HeckeDetectorRowCount

theorem variable_plain_marked_count
    {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
    {U a ε tstar T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {k c κ C height εm : ℝ} (moments : Moments F ((k-3/4)/2) c κ C height εm)
    (hU : 1< U) (ha : 1/2≤ a) (hk : 0≤ k) (hC : 0≤ C) (hh : 0≤ height)
    (hf : 2*Real.pi*allowance+(3*i : ℕ)*T≤ height)
    (z : ℝ) (hz : 0≤ z) (hz' : z≤7/37) (hcap : 2*F.m+6*k*z≤1) :
    (F.rows.card : ℝ)≤(192*(1+height)*C)*U^(1-2*(2*a-1)*F.m-2*F.q*z+4*ε+(2*a-1)*F.mesh+εm) := by
  have heq : 3/4+2*((k-3/4)/2)=k := by ring
  apply HeckeDetectorPlainFiberCount.plain_fiber_count M H F.rows F.nonempty F.family U a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    F.slots (fun u => u.val) F.profile F.upper F.widths F.bin F.external F.mesh F.binWidth z k εm C height
    F.mesh_nonneg F.binWidth_pos F.widths_pos F.widths_mesh (by linarith [F.supply])
    hz (hz'.trans F.supply) F.fixed_bin hk hC hh hf hcap
  simpa only [heq,Fiber.m,Fiber.physicalProduct] using moments.plain_marked

theorem variable_plain_requested_capacity (k c x t r m ε ν : ℝ)
    (hk : 13/18≤ k) (hc : c=2/(3*k)) (hx : 0≤ x) (hx1 : x≤1/2)
    (ht : 1≤ t) (ht1 : t≤3/2) (hr : r≤ RHBootstrapCount.rstar c x t)
    (hleft : t-r-ε≤ m) (hε : ε≤1/12) (hν : 0≤ν) (hνcap : ν<(1-2*m)/(6*k)) :
    0≤(1-2*m)/(6*k)-ν ∧ (1-2*m)/(6*k)-ν≤7/37 ∧
      2*m+6*k*((1-2*m)/(6*k)-ν)≤1 := by
  have hk0 : 0< k := by linarith
  have hc0 : 0< c := by rw [hc]; positivity
  have hc1 : c<1 := by rw [hc];apply (div_lt_one (by positivity)).2;linarith
  have hlength := RHBootstrapCount.plain_length_bounds c x t hc0 hc1 hx hx1 ht ht1
  have hm : 1/4≤ m := by linarith
  have hd : 0<6*k := by positivity
  have hcap : (1-2*m)/(6*k)≤7/37 := (div_le_iff₀ hd).mpr (by nlinarith)
  refine ⟨by linarith,by linarith,?_⟩
  rw [mul_sub,mul_div_cancel₀ _ hd.ne']
  nlinarith [mul_nonneg hd.le hν]

theorem full_inverse_requested_capacity (r ν : ℝ) (hr : 8/13≤ r) (_hr1 : r<1)
    (hν : 0<ν) (hνcap : ν<(1-r)/2) :
    0≤(1-r)/2-ν ∧ (1-r)/2-ν≤1/5 ∧
      r+2*((1-r)/2-ν)<1 ∧ 2*r+8*((1-r)/2-ν)<3 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem full_inverse_marked_count
    {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
    {U a ε tstar T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {Δ c κ C height εm : ℝ} (moments : Moments F Δ c κ C height εm)
    (hsupply : (1/5:ℝ)≤∑s∈F.slots,F.widths s)
    (hU : 1< U) (ha : 1/2≤ a) (hC : 0≤ C) (hh : 0≤ height)
    (hf : 2*Real.pi*allowance+(3*i : ℕ)*T≤ height)
    (z : ℝ) (hz : 0≤ z) (hz' : z≤1/5) (hcap1 : F.r+2*z<1) (hcap2 : 2*F.r+8*z<3) :
    (F.rows.card : ℝ)≤(12*(1+height)*C)*U^(1-(2*a-1)*F.r-2*F.q*z+2*ε+(2*a-1)*F.mesh+εm) := by
  exact HeckeDetectorInverseFiberCount.inverse_fiber_count M H F.rows F.nonempty F.family U a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    F.slots (fun u => u.val) F.profile F.upper F.widths F.bin F.external F.mesh F.binWidth z εm C height
    F.mesh_nonneg F.binWidth_pos F.widths_pos F.widths_mesh (by linarith [F.supply])
    hz (hz'.trans hsupply) F.fixed_bin hC hh hf hcap1 hcap2 moments.inverse_marked

theorem count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤ B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0< c ∧ c≤1 ∧ 0<κ ∧ 0≤ K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε tstar T allowance k ν C height : ℝ) (i : ℕ),
      1< U → 1/2< a → 2*a-1≤5/6 → 0≤ε → ε≤1/1000 →
      1≤ tstar → tstar≤3/2 → 13/18≤ k → k≤1 → 0<ν → 0≤ C → 0≤ height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤ height →
      ∀ {Label Slot : Type*} (F : Fiber M H Label Slot U a ε tstar T allowance i),
      (1/5:ℝ)≤∑s∈F.slots,F.widths s →
      Moments F ((k-3/4)/2) c κ C height εm →
      (F.rows.card : ℝ)≤ fiberConstant C height K₀*
        U^(max (RHBootstrapCount.shortCount (2/(3*k)) (2*a-1) (F.q/(2*a-1)) tstar)
          (RHBootstrapCount.longCount (5/6) (2*a-1) tstar)+159*ε+εm+F.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hamp⟩ := HeckeDetectorNoSlotInverseCount.no_slot_inverse_count
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB 2 εm (by norm_num) hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hamp] with U hamp
  intro a ε tstar T allowance k ν C height i hU ha hδcap hε hεsmall ht ht' hk hk' hν hC hh hf
    Label Slot F hsupply moments
  let δ := 2*a-1
  let x := F.q/δ
  let cplain := 2/(3*k)
  have hk0 : 0< k := by linarith
  have hc0 : 0< cplain := by dsimp [cplain]; positivity
  have hc1 : cplain<1 := by
    dsimp [cplain]; apply (div_lt_one (by positivity)).2; linarith
  have hcLower : 2/3≤ cplain := by
    dsimp [cplain]; apply (le_div_iff₀ (by positivity)).2; nlinarith
  have hrbase : 8/13≤(6-cplain)/(10-2*cplain) := by
    apply (le_div_iff₀ (by linarith)).2; linarith
  have hδ : 0<δ := by dsimp [δ]; linarith
  have ha' : 1/2≤ a := by linarith
  have hδ1 : δ≤1 := by dsimp [δ]; linarith
  obtain ⟨hq0,hqδ⟩ := F.mean_bounds ha'
  have hx : 0≤ x := div_nonneg hq0 hδ.le
  have hx' : x≤1/2 := (div_le_iff₀ hδ).mpr (by dsimp [δ]; linarith)
  have hqx : δ*x=F.q := by dsimp [x]; field_simp
  have hgeom := F.lengths hU
  have hr0 : 0≤ F.r := by linarith [hgeom.2.2.2.1]
  have hr2 : F.r≤2 := by linarith [hgeom.2.1]
  have hUp : 0< U := zero_lt_one.trans hU
  obtain ⟨hconst,hconstP,hconstI,hconstI0⟩ := fiberConstant_bounds C height K₀ hC hh hK
  have promote (C' p q : ℝ) (hC' : C'≤ fiberConstant C height K₀)
      (hb : (F.rows.card : ℝ)≤ C'*U^p) (hpq : p≤ q) :
      (F.rows.card : ℝ)≤ fiberConstant C height K₀*U^q := by
    exact hb.trans ((mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg hUp.le _)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hpq) hconst))
  have hi0 := hamp F.rows F.family a ε tstar T allowance i hU ha'
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    hr0 hr2 F.rowData F.reverse C height hC hh hf F.row_norm F.row_coeff moments.inverse_raw
  have hI0 : (F.rows.card : ℝ)≤ fiberConstant C height K₀*
      U^(max 1 ((1+5*F.r)/6)-δ*F.r+commonLoss ε εm F.mesh ν) := by
    apply promote _ _ _ hconstI0 hi0
    exact no_slot_inverse_loss F.r δ ε εm F.mesh ν hε F.mesh_nonneg hν.le
  have hp0 := F.plain_unmarked_count moments hU (by linarith) hC hh hf
  have hP0 : (F.rows.card : ℝ)≤ fiberConstant C height K₀*
      U^(1-2*δ*F.m+commonLoss ε εm F.mesh ν) := by
    apply promote _ _ _ hconstP hp0
    exact no_slot_plain_loss F.m δ ε εm F.mesh ν hε hgeom.2.2.1 F.mesh_nonneg hν.le
  have hI : (6-cplain)/(10-2*cplain)≤ F.r → F.r<1 → ν<(1-F.r)/2 →
      (F.rows.card : ℝ)≤ fiberConstant C height K₀*
        U^(1-δ*RHBootstrapCount.invGain x F.r+commonLoss ε εm F.mesh ν) := by
    intro hr hr1 hv
    obtain ⟨hz,hz',hcap1,hcap2⟩ := full_inverse_requested_capacity F.r ν (hrbase.trans hr) hr1 hν hv
    have hb := full_inverse_marked_count F moments hsupply hU ha' hC hh hf ((1-F.r)/2-ν) hz hz' hcap1 hcap2
    apply promote _ _ _ hconstI hb
    have hl := inverse_marked_loss F.r δ x ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
    rw [hqx] at hl
    convert hl using 1 <;> unfold inverseExponent RHBootstrapCount.invGain <;> ring
  have hP : F.r≤ RHBootstrapCount.rstar cplain x tstar → F.m<1/2 → ν<(1-2*F.m)/(6*k) →
      (F.rows.card : ℝ)≤ fiberConstant C height K₀*
        U^(1-2*δ*F.m-2*(δ*x)*(1-2*F.m)/(6*k)+commonLoss ε εm F.mesh ν) := by
    intro hr hm hv
    obtain ⟨hz,hz',hcap⟩ := variable_plain_requested_capacity k cplain x tstar F.r F.m ε ν hk rfl hx hx' ht ht'
      hr hgeom.1 (by linarith) hν.le hv
    have hb := variable_plain_marked_count F moments hU ha' (by linarith) hC hh hf
      ((1-2*F.m)/(6*k)-ν) hz hz' hcap
    apply promote _ _ _ hconstP hb
    have hl := plain_marked_loss F.m δ x ((k-3/4)/2) ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
    have heq : 9/2+12*((k-3/4)/2)=6*k := by ring
    simpa only [hqx,heq] using hl
  have hc' := CombineV22.VariableCount.count_bound_of_four_branches (F.rows.card : ℝ)
    (fiberConstant C height K₀) U δ x k cplain tstar F.r F.m
    (commonLoss ε εm F.mesh ν) ν ε hconst hU.le hδ.le hδcap hx hx' hk (by linarith) rfl
    ht ht' hν.le hε hgeom.1 hgeom.2.1 hI0 hP0 hI hP
  convert hc' using 1; congr 2
  unfold commonLoss
  ring

end SevenEighths.IVFullHeckeDetectorCountFromMoments
end
end OAI
#print axioms OAI.SevenEighths.IVFullHeckeDetectorCountFromMoments.count_from_raw_moments

end PartIVBlock15

/- BEGIN consolidated variable_moments/FullRangeBatch.lean -/
section PartIVBlock16
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.IVFullHeckeDetectorFixedAmplitudeCount
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorRowCount

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

lemma fiber_mean_eq (B : Batch M H Label Slot U a ε tstar T allowance i) (q : ℝ)
    (hq : ∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
      (physical M H (fun u : FreeRow=> u.val) B.profile B.upper B.widths B.external U) u=q)
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
  exact congrArg (fun g=> B.widths s*g) ((B.fiber bin j J K hne).fixed_bin u hu s hs).symm

lemma batch_mean_bounds (B : Batch M H Label Slot U a ε tstar T allowance i)
    (hne : B.rows.Nonempty) (ha : 1/2≤ a) (q : ℝ)
    (hq : ∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
      (physical M H (fun u : FreeRow=> u.val) B.profile B.upper B.widths B.external U) u=q) :
    0≤ q ∧ q≤(2*a-1)/2 := by
  obtain ⟨u,hu⟩ := hne
  rw [←hq u hu]
  apply weightedMean_bounds B.slots B.widths _ (2*a-1)
    (fun s hs=>(B.widths_pos s hs).le) (by linarith [B.supply])
  intro s hs
  exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by linarith)

theorem fixed_amplitude_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃c κ K₀ : ℝ,0< c ∧ c≤1 ∧ 0<κ ∧ 0≤ K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀(a ε tstar T allowance k ν C height q : ℝ) (i : ℕ),
      1< U → 1/2< a → 2*a-1≤5/6 → 0≤ε → ε≤1/1000 →
      1≤ tstar → tstar≤3/2 → 13/18≤ k → k≤1 → 0<ν → 0≤ C → 0≤ height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤ height →
      ∀{Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε tstar T allowance i),
      (1/5:ℝ)≤∑s∈B.slots,B.widths s →
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=> u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) ((k-3/4)/2) c κ C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2* fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(max (RHBootstrapCount.shortCount (2/(3*k)) (2*a-1) (q/(2*a-1)) tstar) (RHBootstrapCount.longCount (5/6) (2*a-1) tstar)+
          159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ := IVFullHeckeDetectorCountFromMoments.count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε tstar T allowance k ν C height q i hU ha hd hε hε' ht ht' hk hk' hν hC hh hf Label Slot _ B hsupply hq moments
  have hb := B.card_bound (fiberConstant C height K₀)
    (fun _=> max (RHBootstrapCount.shortCount (2/(3*k)) (2*a-1) (q/(2*a-1)) tstar) (RHBootstrapCount.longCount (5/6) (2*a-1) tstar)+
      159*ε+εm+B.mesh+7*ν)
    (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
      intro bin j J K hne
      have hc' := hcount a ε tstar T allowance k ν C height i hU ha hd hε hε' ht ht' hk hk' hν hC hh hf
        (B.fiber bin j J K hne) hsupply (moments bin j J K hne)
      rw [fiber_mean_eq B q hq bin j J K hne] at hc'
      exact hc')
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hb
end SevenEighths.IVFullHeckeDetectorFixedAmplitudeCount
end
end OAI
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.IVFullProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorRowCount IVAdaptiveCutoff

theorem balanced_adaptive_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃c κ K₀ : ℝ,0< c ∧ c≤1 ∧ 0<κ ∧ 0≤ K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀(a ε T allowance k ν C height q : ℝ) (i : ℕ),
      1< U → 1/2< a → 2*a-1≤5/6 → 0≤ε → ε≤1/1000 →
      13/18≤ k → k≤1 → 0<ν → 0≤ C → 0≤ height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤ height →
      ∀{Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff k (2*a-1) q) T allowance i),
      (1/5:ℝ)≤∑s∈B.slots,B.widths s →
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=> u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) ((k-3/4)/2) c κ C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2* fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(RHBootstrapCount.countR (5/6) (2/(3*k)) (2*a-1) (q/(2*a-1))+
          159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ :=
    IVFullHeckeDetectorFixedAmplitudeCount.fixed_amplitude_count_from_raw_moments
      M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance k ν C height q i hU ha hd hε hε' hk hk' hν hC hh hf Label Slot _ B hsupply hne hq hmom
  have hδ : 0<2*a-1 := by linarith
  have hqb := IVFullHeckeDetectorFixedAmplitudeCount.batch_mean_bounds B hne (by linarith) q hq
  have hx : 0≤ q/(2*a-1) := div_nonneg hqb.1 hδ.le
  have hx' : q/(2*a-1)≤1/2 := (div_le_iff₀ hδ).mpr (by linarith [hqb.2])
  have ht := IVAdaptiveCutoff.cutoff_bounds k (2*a-1) q hk hδ.le
  have hc' := hcount a ε (cutoff k (2*a-1) q) T allowance k ν C height q i
    hU ha hd hε hε' ht.1 ht.2 hk hk' hν hC hh hf B hsupply hq hmom
  have he : max (RHBootstrapCount.shortCount (2/(3*k)) (2*a-1) (q/(2*a-1)) (cutoff k (2*a-1) q))
      (RHBootstrapCount.longCount (5/6) (2*a-1) (cutoff k (2*a-1) q)) =
      RHBootstrapCount.countR (5/6) (2/(3*k)) (2*a-1) (q/(2*a-1)) := by
    rw [IVAdaptiveCutoff.cutoff_eq_balanced k (2*a-1) q hδ hd hqb.1 hqb.2]
    exact IVAdaptiveCutoff.balanced_count_identity k (2*a-1) (q/(2*a-1)) hk hδ.le hd hx hx'
  rw [he] at hc'
  exact hc'


end SevenEighths.IVFullProbeHighRowFamily
end
end OAI

#print axioms OAI.SevenEighths.IVFullProbeHighRowFamily.balanced_adaptive_count_from_raw_moments

end PartIVBlock16

/- BEGIN consolidated variable_moments/FullRangeSourceCount.lean -/
section PartIVBlock17
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.IVFullProbeHighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorRowCount IVAdaptiveCutoff

theorem balanced_source_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm : ℝ) (hεm : 0<εm)
    (Label : Type*) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0< dmin) (hdmax : 0< dmax) (hτ : 0<τ)
    (hl : 0< logCost) (hh : τ< heightCost) (hb : 0< binWidth) :
    ∃c κ K : ℝ,0< c ∧ c≤1 ∧ 0<κ ∧ 0< K ∧ ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax →
      ∀(a ε kMoment ν C q : ℝ) (i : ℕ),i≤ n → 1/2< a → 2*a-1≤5/6 → a≤1 → 0≤ε → ε≤1/1000 →
      13/18≤ kMoment → kMoment≤1 → 0<ν → 0≤ C →
      ∀{Slot : Type*} (B : Batch M H Label Slot (Z^d) a ε
        (cutoff kMoment (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
      (1/5:ℝ)≤∑s∈B.slots,B.widths s →
      B.slots.card≤ N → B.binWidth=binWidth →
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=> u.val) B.profile B.upper B.widths B.external (Z^d)) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) ((kMoment-3/4)/2) c κ (C*Z^momentCost) (Z^heightCost) εm) →
      (B.rows.card:ℝ)≤ K*C*Z^(logCost+heightCost+momentCost)*(Z^d)^(RHBootstrapCount.countR (5/6) (2/(3*kMoment)) (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK₀,hcount⟩ := balanced_adaptive_count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  obtain ⟨K,hK,hpref⟩ := source_count_prefactor_eventually (Label:=Label)
    N dmin dmax logCost heightCost momentCost binWidth K₀ hdmin hdmax hl (by linarith) hb
  refine ⟨c,κ,K,hc,hc1,hκ,hK,?_⟩
  filter_upwards [eventually_all_rpow_ge hcount dmin hdmin,hpref,
    source_count_frequency_eventually n dmax τ heightCost hdmax hτ hh,
    eventually_all_rpow_ge (eventually_gt_atTop (1:ℝ)) dmin hdmin,
    eventually_ge_atTop (1:ℝ)] with Z hcount hpref hfreq hU hZ
  intro d hd hd' a ε kMoment ν C q i hi ha haδ ha' hε hε' hkMoment hkMoment' hν hC Slot B hsupply hslots hbin hne hq hmom
  have hcard := hcount d hd a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) kMoment ν
    (C*Z^momentCost) (Z^heightCost) q i (hU d hd) ha haδ hε hε' hkMoment hkMoment' hν (by positivity)
    (by positivity) (hfreq d hd' i hi) B hsupply hne hq hmom
  apply hcard.trans
  exact mul_le_mul_of_nonneg_right
    (hpref d hd hd' C a ε (cutoff kMoment (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i
      hC ha' B hslots hbin) (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _)


lemma actual_batch_supply
    {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {Label : Type*} {N : ℕ}
    {U a ε tstar T allowance : ℝ} {i : ℕ}
    (B : Batch M H Label (Fin N) U a ε tstar T allowance i)
    (ell : Fin N→ℝ) (L d rho : ℝ)
    (hslots : B.slots=Finset.univ) (hwidths : B.widths=fun j=> ell j/d)
    (hsum : ∑j,ell j=L) (hsupply : 1/5+rho≤ L/d) (hrho : 0≤ rho) :
    (1/5:ℝ)≤∑s∈B.slots,B.widths s := by
  rw [hslots,hwidths,←Finset.sum_div,hsum]
  linarith

end SevenEighths.IVFullProbeHighRowFamily
end
end OAI
#print axioms OAI.SevenEighths.IVFullProbeHighRowFamily.balanced_source_count_from_raw_moments

end PartIVBlock17

/- BEGIN consolidated variable_moments/FullRangeMoments.lean -/
section PartIVBlock18
set_option linter.unusedSectionVars false
noncomputable section
namespace RHIVProbe
class FullMomentParameter where
  kappa : ℝ
  lower : 13/18≤ kappa
  upper : kappa≤1
variable [FullMomentParameter]
def fullMomentKappa : ℝ := FullMomentParameter.kappa
lemma full_moment_range : 13/18≤ fullMomentKappa ∧ fullMomentKappa≤1 :=
  ⟨FullMomentParameter.lower,FullMomentParameter.upper⟩
end RHIVProbe
variable [RHIVProbe.Geometry] [RHIVProbe.FullMomentParameter]
local instance : RHIVProbe.MomentParameter := ⟨3/4, by norm_num, le_rfl⟩
-- Parametric source adaptation: V2MomentCertificateAdapters

-- Adapted data-generic source wrapper from DetectorMomentPrimeGeometry.lean

/-! Actual perturbed source prime geometry. The generic separation, capacity,
large-prime and fixed-character norm results are reused unchanged. Only the
window/SourceData wrappers are rederived at the genuine new slot lengths. -/
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.IVFullHeckeDetectorMomentPrimeGeometry
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialPhysicalSlots
open HeckeDetectorBatch HeckeDetectorRawFiber HeckeDetectorFiberPartition ProbeHighRowFamily
local notation "O" => HeckeFamily.O

theorem sourceMoment_primeProfile_norm {Δ : ℝ} {D : RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}
    (F : RHZeroFreeExtension.AnalyticHigh.IV.SourceData D) (X : ℝ) (ζ : ℂ) (hz : ζ.re≤1)
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

theorem sourceMoment_live_disjoint {Δ : ℝ} {D : RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}
    (F : RHZeroFreeExtension.AnalyticHigh.IV.SourceData D) {ι : Type*} (ell : ι→ℝ)
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

theorem sourceMoment_live_denominator {Δ : ℝ} {D : RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}
    (F : RHZeroFreeExtension.AnalyticHigh.IV.SourceData D) {ι : Type*} [Fintype ι]
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

theorem sourceMoment_live_quotient_norm {Δ : ℝ} {D : RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}
    (F : RHZeroFreeExtension.AnalyticHigh.IV.SourceData D) {ι : Type*} [Fintype ι]
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
    {Δ : ℝ} {D : RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ} (F : RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)
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
end SevenEighths.IVFullHeckeDetectorMomentPrimeGeometry
end
end OAI

#print axioms OAI.SevenEighths.IVFullHeckeDetectorMomentPrimeGeometry.sourceMoment_fiber_prime_geometry_eventually

-- Adapted data-generic source wrapper from NaturalFixedRaySourceFixedIdeal.lean

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators

namespace SevenEighths.IVFullCenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

variable {Δ : ℝ} {D : RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}

def sourceFixedIdeal (F : RHZeroFreeExtension.AnalyticHigh.IV.SourceData D) : Ideal O :=
  F.modulus⊓Ideal.span {(72:O)}

lemma sourceFixedIdeal_ne_zero (F : RHZeroFreeExtension.AnalyticHigh.IV.SourceData D) : sourceFixedIdeal F≠0 :=
  Ideal.inf_ne_bot_of_ne_bot (NeZero.ne F.modulus)
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0))

lemma sourceFixedIdeal_ne_top (F : RHZeroFreeExtension.AnalyticHigh.IV.SourceData D) : sourceFixedIdeal F≠⊤ := by
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

lemma sourceFixedIdeal_le_modulus (F : RHZeroFreeExtension.AnalyticHigh.IV.SourceData D) : sourceFixedIdeal F≤ F.modulus := inf_le_left
lemma sourceFixedIdeal_le_72 (F : RHZeroFreeExtension.AnalyticHigh.IV.SourceData D) : sourceFixedIdeal F≤ Ideal.span {(72:O)} := inf_le_right

def sourceExceptional (F : RHZeroFreeExtension.AnalyticHigh.IV.SourceData D) (η : Character) (u : FreeRow) : Prop :=
  FixedInducingRow η (internalQ (sourceFixedIdeal F) η)
    (fixedBadMask*idealGenerator 1) 1 u.val

theorem source_retained_sector_nonprincipal (F : RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)
    (η : Character) (u : FreeRow) (hu : ¬sourceExceptional F η u)
    (θ : RayQuotient.Characters F.modulus ⊤) :
    ((naturalRow η u.val u.property.1).character.product
      (relativeCharacter F.modulus ⊤ le_top η θ)).residue≠1 :=
  internal_sector_nonprincipal F.modulus ⊤ le_top (naturalRow η u.val u.property.1)
    η θ (sourceFixedIdeal F) 1 (sourceFixedIdeal_le_modulus F) one_ne_zero u.property.1 hu

theorem source_energy_split (F : RHZeroFreeExtension.AnalyticHigh.IV.SourceData D) (η : Character)
    (rows : Finset FreeRow) (f : FreeRow→ℂ) :
    (∑u∈rows,‖f u‖^2)=
      (∑u∈rows.filter (fun u=>¬sourceExceptional F η u),‖f u‖^2)+
      ∑u∈rows.filter (sourceExceptional F η),‖f u‖^2 := by
  simpa only [not_not] using
    (Finset.sum_filter_add_sum_filter_not rows (fun u=>¬sourceExceptional F η u)
      (fun u=>‖f u‖^2)).symm

end SevenEighths.IVFullCenteredMomentNaturalFixedRaySource

end

end OAI

-- Adapted data-generic source wrapper from NaturalFixedRaySourceBatch.lean

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators ComplexConjugate Topology
open Filter

namespace SevenEighths.IVFullCenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentNaturalRowSource CenteredMomentDetectorDictionary
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open ProbeHighRowFamily HeckeDetectorDyadicProfiles CenteredMomentPrimeSlot HeckeDetectorRowwisePolynomial
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem eventually_source_batch_plain_sectors {N : ℕ}
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (hM : M=∏P∈S,P)
    (η : Character) (ell : Fin N→ℝ) (hell : ∀s,0< ell s)
    (W : Fin N→ℝ→ℂ) (hW : ∀s,Function.support (W s)⊆Set.Ici 1) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,d≠0→∀a ε tstar T allowance : ℝ,∀i : ℕ,
      ∀B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N) (Z^d) a ε tstar T allowance i,
      B.data=sourceMomentData M H hH S hS η→B.widths=(fun s=> ell s/d)→B.profile=W→
      ∀bin label J K,∀hne : (B.fiberRows bin label J K).Nonempty,
      ∀selected : Finset (Fin N),∀j k : ℕ,∀σ t : ℝ,
      let F:=B.fiber bin label J K hne
      let η₀:=sourceMomentBase M H hH S hS η label
      (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) ((Z^d)^F.m) σ t*
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) ((Z^d)^F.m) σ t*
          F.physicalProduct selected u‖^2)≤
        ∑θ : selected→RayQuotient.Characters M H,‖averageWeight (ι:=selected) M H‖*
          ∑u∈F.rows,‖fiberSector hH F η₀ selected j k σ t θ u‖^2 := by
  have hMm : M≤ Ideal.span {rowMaskElement} := by
    rw [hM]
    exact source_product_le_rowMask S hbad
  filter_upwards [eventually_source_slots_coprime M H hH S hS η ell hell 1 (by norm_num),
    eventually_gt_atTop (0:ℝ)] with Z hz hZ
  intro d hd a ε tstar T allowance i B hdata hwidth hprofile bin label J K hne selected j k σ t
  dsimp only
  convert fiber_plain_sector_energy hH (B.fiber bin label J K hne)
    (sourceMomentBase M H hH S hS η label) ?_ hMm (Real.rpow_pos_of_pos hZ _) selected j k σ t ?_ using 1
  · congr 2 ; apply Subsingleton.elim
  · change B.data label=momentData (sourceMomentBase M H hH S hS η label)
    rw [hdata,sourceMomentData_base]
  · intro s hs P hP hp
    change P∈primePool M H (B.upper s) ((Z^d)^(B.widths s)) at hP
    change B.profile s ((P.absNorm:ℝ)/((Z^d)^(B.widths s)))≠0 at hp
    rw [hwidth] at hP
    rw [hwidth,hprofile] at hp
    exact hz label s d hd (W s) (B.upper s) (hW s) P hP hp

theorem sourceData_batch_gate {Δ : ℝ} {D : RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}
    (F : RHZeroFreeExtension.AnalyticHigh.IV.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,d≠0→∀a ε tstar T allowance : ℝ,∀i : ℕ,
      ∀B : Batch F.modulus ⊤ (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i,
      B.data=sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η→
      B.widths=(fun s=> D.ell s/d)→B.profile=(fun _ y=>(F.w y:ℂ))→
      ∀bin label J K,∀hne : (B.fiberRows bin label J K).Nonempty,
      ∀selected : Finset (Fin D.N),∀j k : ℕ,∀σ t : ℝ,
      let Bf:=B.fiber bin label J K hne
      let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
      (∑u∈Bf.rows,‖polynomial (Bf.family u Bf.label) false ((logProfile^[j]) positiveAnnular) ((Z^d)^Bf.m) σ t*
        polynomial (Bf.family u Bf.label) false ((logProfile^[k]) positiveAnnular) ((Z^d)^Bf.m) σ t*
          Bf.physicalProduct selected u‖^2)≤
        ∑θ : selected→RayQuotient.Characters F.modulus ⊤,‖averageWeight (ι:=selected) F.modulus ⊤‖*
          ∑u∈Bf.rows,‖fiberSector le_top Bf η₀ selected j k σ t θ u‖^2 := by
  apply eventually_source_batch_plain_sectors F.modulus ⊤ le_top F.S F.exclusions.prime
    F.exclusions.bad rfl η D.ell (fun s=>(D.slots_bounds s).1) (fun _ y=>(F.w y:ℂ))
  intro s y hy
  have hn : F.w y≠0 := by
    intro h
    apply hy
    simp only [h,Complex.ofReal_zero]
  exact (F.support hn).1.le

end SevenEighths.IVFullCenteredMomentNaturalFixedRaySource

end

end OAI

-- Adapted data-generic source wrapper from DetectorPlainSlotProfile.lean

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentDetectorPlainSlotProfile
open RHZeroFreeExtension.AnalyticHigh

open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
namespace SevenEighths.IVFullCenteredMomentDetectorPlainSlotProfile
open HeckeFamily HeckeInverseAmplification HeckeDyadic CenteredMomentDetectorDictionary
open CenteredMomentRetainedEnergy
local notation "O"=> HeckeFamily.O
variable {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}

lemma conjugate_source_support (F:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D):
    Function.support (fun x=> conj (F.W x))⊆Set.Icc (1:ℝ) 2 := by
  intro x hx
  exact F.complex_support (by simpa using hx)

private lemma conjugate_source_smooth (F : RHZeroFreeExtension.AnalyticHigh.IV.SourceData D) :
    ContDiff ℝ ∞ (fun x => conj (F.W x)) := by
  exact Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)

def slotSchwartz (F:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(ζ:ℂ):𝓢(ℝ,ℂ):=
  interpolatedProfile (fun x=> conj (F.W x)) 1 2 (by norm_num)
    (conjugate_source_support F) (conjugate_source_smooth F)
    (1-ζ.re) (-ζ.im)

theorem slotSchwartz_apply (F:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(ζ:ℂ)(x:ℝ):
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

theorem slotSchwartz_support (F:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(ζ:ℂ):
    Function.support (slotSchwartz F ζ:ℝ→ℂ)⊆Set.Icc (1:ℝ) 2 := by
  intro x hx
  apply F.complex_support
  intro hw
  exact hx (by rw [slotSchwartz_apply,hw,zero_mul,map_zero])

theorem slotSchwartz_smooth (F:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(ζ:ℂ):
    ContDiff ℝ ∞ (slotSchwartz F ζ:ℝ→ℂ):=(slotSchwartz F ζ).smooth ⊤

theorem slotSchwartz_norm (F:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(ζ:ℂ)(hζ:ζ.re≤1)(x:ℝ):
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

theorem physical_coefficient (F:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(η:Character)
    (P:ℝ)(ζ:ℂ)(I:Ideal O):
    physicalSlotCoefficient η F.W P ζ I=
      idealCoeff η.inverse I*slotSchwartz F ζ ((I.absNorm:ℝ)/P) := by
  rw [slotSchwartz_apply]
  rfl

theorem physical_coefficient_norm (F:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(η:Character)
    (P:ℝ)(ζ:ℂ)(hζ:ζ.re≤1)(I:Ideal O):
    ‖physicalSlotCoefficient η F.W P ζ I‖≤1 := by
  rw [physical_coefficient,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (idealCoeff_norm_le_one η.inverse I)).trans (slotSchwartz_norm F ζ hζ _)

theorem slotSchwartz_uniform (F:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(S:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃C:ℝ,0< C ∧ ∀ζ:ℂ,ζ.re∈Set.Icc (0:ℝ) 1 →
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (slotSchwartz F ζ)≤ C*(1+‖ζ.im‖)^J := by
  obtain ⟨J,C,hC,hbound⟩:=interpolatedProfile_uniform (fun x=> conj (F.W x)) 1 2 (by norm_num)
    (conjugate_source_support F) (conjugate_source_smooth F) S
  refine ⟨J,C,hC,?_⟩
  intro ζ hζ
  have hh:=hbound (1-ζ.re) ⟨by linarith [hζ.2],by linarith [hζ.1]⟩ (-ζ.im)
  simpa only [slotSchwartz,norm_neg] using hh

theorem slotSchwartz_height_uniform (F:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(S:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃C:ℝ,0< C ∧ ∀{ι:Type*}(ζ:ι→ℂ)(height:ℝ),0≤ height →
      (∀i,(ζ i).re=17/50) → (∀i,|(ζ i).im|≤ height) → ∀i,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (slotSchwartz F (ζ i))≤ C*(1+height)^J := by
  obtain ⟨J,C,hC,hbound⟩:=slotSchwartz_uniform F S
  refine ⟨J,C,hC,?_⟩
  intro ι ζ height hheight hreal him i
  refine (hbound (ζ i) (by rw [hreal i];norm_num)).trans ?_
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact pow_le_pow_left₀ (by positivity) (by simp only [Real.norm_eq_abs];linarith [him i]) J

theorem physical_positive_row {ι:Type*}[Fintype ι][DecidableEq ι]
    (F:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(η η₀:Character)(m A z:O)
    (W₁ W₂:ℝ→ℂ)(S:ι→Finset (Ideal O))(P:ι→ℝ)(ζ:ι→ℂ)(t X₁ X₂:ℝ):
    positiveSlotRow η m A z W₁ W₂ S (fun i=> physicalSlotCoefficient η₀ F.W (P i) (ζ i)) P t X₁ X₂=
      positiveSlotRow η m A z W₁ W₂ S
        (fun i I=> idealCoeff η₀.inverse I*slotSchwartz F (ζ i) ((I.absNorm:ℝ)/P i)) P t X₁ X₂ := by
  congr 1
  funext i I
  exact physical_coefficient F η₀ (P i) (ζ i) I

end SevenEighths.IVFullCenteredMomentDetectorPlainSlotProfile

end

end OAI

-- Adapted data-generic source wrapper from DetectorPlainCapacity.lean

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentDetectorPlainCapacity
open OAI.SevenEighths.CenteredMomentDetectorPlainSlotProfile
open RHZeroFreeExtension.AnalyticHigh

open scoped Classical BigOperators ContDiff ComplexConjugate
namespace SevenEighths.IVFullCenteredMomentDetectorPlainCapacity
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorDictionary IVFullCenteredMomentDetectorPlainSlotProfile
local notation "O"=> HeckeFamily.O
variable {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}

theorem physical_annular_all (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(η₀:Character)
    (P:ℝ)(hP:0< P)(ζ:ℂ)(I:Ideal O):
    physicalSlotCoefficient η₀ S.W P ζ I=
      idealCoeff η₀.inverse I*annularWeight (fun x=> conj (S.W x)) P (1-ζ.re) (-ζ.im) I := by
  by_cases hI:I=0
  · subst I
    have hw:S.W 0=0:=by
      by_contra hh
      have hs:=S.complex_support hh
      norm_num at hs
    simp [physicalSlotCoefficient,annularWeight,hw]
  · exact physicalSlotCoefficient_annular η₀ S.W P ζ I hI hP

theorem selected_physical_annular {ι:Type*}
    (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(J:Finset ι)(η η₀:Character)(m A z:O)
    (W₁ W₂:ℝ→ℂ)(pools:ι→Finset (Ideal O))(P:ι→ℝ)(hP:∀i,0< P i)
    (ζ:ι→ℂ)(t X₁ X₂:ℝ):
    selectedProduct J η m A z W₁ W₂ pools
      (fun i=> physicalSlotCoefficient η₀ S.W (P i) (ζ i)) P t X₁ X₂=
    selectedProduct J η m A z W₁ W₂ pools
      (fun i I=> idealCoeff η₀.inverse I*
        annularWeight (fun x=> conj (S.W x)) (P i) (1-(ζ i).re) (-(ζ i).im) I) P t X₁ X₂ := by
  congr 1
  funext i I
  exact physical_annular_all S η₀ (P i) (hP i) (ζ i) I

variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)
include hH

theorem physical_capacity_removal {ι:Type*}[Fintype ι][DecidableEq ι]
    (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(Lmod Lslot ε κ:ℝ)
    (hLm:0≤ Lmod)(hLs:0≤ Lslot)(hε:0<ε)
    (hbeta:(51/100:ℝ)≤ beta)(hκ:2*beta-1≤κ):
    ∃degree:ℕ,∃C:ℝ,0< C ∧ ∀η₀:Character,∃Z₀:ℝ,1< Z₀ ∧
    ∀(J:Finset ι)(w:ι→ℝ)(n₁ n₂ width mesh:ℝ),0≤ mesh →
      (∀i,0≤ w i) → (∀i,w i≤ mesh) → (∀i,w i≤ Lslot) →
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤ width) ∧
      κ*(∑i∈R,w i)≤ CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh ∧
    ∀Z:ℝ,Z₀≤ Z → ∀η:Character,∀z:O,z≠0 → ∀F:NaturalRow η z,
      (F.character.modulus.absNorm:ℝ)≤ Z^Lmod →
    ∀Q:Ideal O,Q≤ M → Q≤η₀.modulus → ¬FixedInducingRow η Q fixedBadMask 1 z →
    ∀(ζ:ι→ℂ)(t V:ℝ),(∀i,(ζ i).re∈Set.Icc (0:ℝ) 1) → 0≤ V → (∀i,|(ζ i).im|≤ V) →
    ∀(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ),
      let P:=fun i=> Z^(w i)
      let pools:=fun i=> primePool M H 2 (P i)
      let coeff:=fun i=> physicalSlotCoefficient η₀ S.W (P i) (ζ i)
      ‖selectedProduct J η fixedBadMask 1 z W₁ W₂ pools coeff P t X₁ X₂‖^2≤
        C*(1+|t|+V)^degree*Z^(ε+CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)*
          ‖selectedProduct (J\R) η fixedBadMask 1 z W₁ W₂ pools coeff P t X₁ X₂‖^2 := by
  obtain ⟨degree,C,hC,hbound⟩:=CenteredMomentRelativeCapacityRemoval.actual_relative_capacity_removal
    M H hH (ι:=ι) (fun _ x=> conj (S.W x)) (fun _=>1) (fun _=>2) (fun _=> by norm_num)
    (fun _=> conjugate_source_support S) (fun _=> Complex.conjCLE.contDiff.comp (S.W.smooth ⊤))
    Lmod Lslot ε 0 1 κ hLm hLs hε hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro η₀
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound (fun _=>η₀.inverse)
  refine ⟨Z₀,hZ₀,?_⟩
  intro J w n₁ n₂ width mesh hmesh hw hwm hwcap
  obtain ⟨R,hR,hremaining,hcost,henergy⟩:=hbound J w n₁ n₂ width mesh hmesh hw hwm hwcap
  refine ⟨R,hR,hremaining,hcost,?_⟩
  intro Z hZ η z hz F hcond Q hQM hQη hex ζ t V hζ hV him W₁ W₂ X₁ X₂
  dsimp only
  have hZp:0< Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hP (i:ι):0< Z^(w i):=Real.rpow_pos_of_pos hZp _
  rw [selected_physical_annular S J η η₀ fixedBadMask 1 z W₁ W₂ _ _ hP ζ t X₁ X₂,
    selected_physical_annular S (J\R) η η₀ fixedBadMask 1 z W₁ W₂ _ _ hP ζ t X₁ X₂]
  exact henergy Z hZ η z hz F hcond Q hQM (fun _=> hQη) hex
    (fun i=>1-(ζ i).re) (fun i=>-(ζ i).im) t V
    (fun i=> by linarith [(hζ i).2]) (fun i=> by linarith [(hζ i).1]) hV
    (fun i=> by simpa only [abs_neg] using him i) W₁ W₂ X₁ X₂

end SevenEighths.IVFullCenteredMomentDetectorPlainCapacity

end

end OAI

-- Adapted data-generic source wrapper from InverseMarkedReferencePrimeGates.lean

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
namespace SevenEighths.IVFullDetectorDictionaryInverseMarkedReference
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

theorem deleted_source_live_prime {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}
    (F:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(data:RowData)
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
  exact IVFullHeckeDetectorMomentPrimeGeometry.sourceMoment_primeProfile_norm F X ζ hζ P

end SevenEighths.IVFullDetectorDictionaryInverseMarkedReference

end

end OAI

#print axioms OAI.SevenEighths.IVFullDetectorDictionaryInverseMarkedReference.deleted_source_live_prime

-- Adapted data-generic source wrapper from NaturalFixedRaySourceCapacity.lean

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.IVFullCenteredMomentNaturalFixedRaySource
open HeckeFamily HeckePrimeScale HeckeInverseAmplification
open CenteredMomentNaturalRowSource CenteredMomentDetectorDictionary
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

def sectorConductorFactor (η₀ : Character) : ℕ :=
  η₀.modulus.absNorm*fixedConductorFactor*(M.absNorm*η₀.modulus.absNorm)

lemma initial_sector_modulus (η₀ : Character) (u : FreeRow) (θ : RayQuotient.Characters M H) :
    ((naturalRow η₀ u.val u.property.1).character.product (relativeCharacter M H hH η₀ θ)).modulus.absNorm≤
      sectorConductorFactor M η₀*(Ideal.span {u.val}).absNorm := by
  have hn:=(naturalRow η₀ u.val u.property.1).natural_modulus_bound
  have hs:=relativeCharacter_modulus M H hH η₀ θ
  apply (product_modulus_bound _ _).trans
  apply (Nat.mul_le_mul hn hs).trans_eq
  unfold sectorConductorFactor
  ring

theorem eventually_source_sector_capacity
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character)
    (margin : ℝ) (hmargin : 0< margin) :
    ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters M H),∀d : ℝ,∀u : FreeRow,
      ((Ideal.span {u.val}).absNorm:ℝ)≤ Z^(d-margin)→
      ∀θ : RayQuotient.Characters M H,
      (((naturalRow (sourceMomentBase M H hH S hS η label) u.val u.property.1).character.product
        (relativeCharacter M H hH (sourceMomentBase M H hH S hS η label) θ)).modulus.absNorm:ℝ)≤ Z^d := by
  have hc : ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters M H),
      (sectorConductorFactor M (sourceMomentBase M H hH S hS η label):ℝ)≤ Z^margin := by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop hmargin).eventually (eventually_ge_atTop _)
  filter_upwards [hc,eventually_gt_atTop (0:ℝ)] with Z hz hZ
  intro label d u hu θ
  have hb : (((naturalRow (sourceMomentBase M H hH S hS η label) u.val u.property.1).character.product
      (relativeCharacter M H hH (sourceMomentBase M H hH S hS η label) θ)).modulus.absNorm:ℝ)≤
      (sectorConductorFactor M (sourceMomentBase M H hH S hS η label):ℝ)*((Ideal.span {u.val}).absNorm:ℝ) := by
    exact_mod_cast initial_sector_modulus M H hH (sourceMomentBase M H hH S hS η label) u θ
  apply hb.trans
  calc
    _≤ Z^margin*Z^(d-margin) := mul_le_mul (hz label) hu (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)
    _=Z^d := by rw [←Real.rpow_add hZ]; congr 1; ring

theorem sourceData_fiber_sector_capacity {Δ : ℝ} {D : RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}
    (F : RHZeroFreeExtension.AnalyticHigh.IV.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀d a ε tstar T allowance : ℝ,∀i : ℕ,
      ∀B : HeckeDetectorBatch.Batch F.modulus ⊤
        (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i,
      (∀u∈B.rows,ProbeHighRowFamily.rowNorm u≤ Z^(d-D.t))→
      ∀bin label J K,∀hne : (B.fiberRows bin label J K).Nonempty,
      ∀u∈(B.fiber bin label J K hne).rows,∀θ : RayQuotient.Characters F.modulus ⊤,
      (((naturalRow (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label)
        u.val u.property.1).character.product
        (relativeCharacter F.modulus ⊤ le_top
          (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label) θ)).modulus.absNorm:ℝ)≤ Z^d := by
  filter_upwards [eventually_source_sector_capacity F.modulus ⊤ le_top
    F.S F.exclusions.prime η D.t D.t_pos] with Z hz
  intro d a ε tstar T allowance i B hcap bin label J K hne u hu θ
  apply hz label d u ?_ θ
  simp only [HeckeDetectorBatch.Batch.fiber, HeckeDetectorFiberPartition.toFiber,
    HeckeDetectorFiberPartition.fiber, Finset.mem_filter] at hu
  have hmem : u∈B.rows := hu.1
  exact hcap u hmem

end SevenEighths.IVFullCenteredMomentNaturalFixedRaySource

end

end OAI

-- Adapted data-generic source wrapper from NaturalFixedRaySourceFreeExceptional.lean

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.IVFullCenteredMomentNaturalFixedRaySource
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

variable {Δ : ℝ} {D : RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}

def sourceExceptionalBound (F : RHZeroFreeExtension.AnalyticHigh.IV.SourceData D) (η : Character) : ℕ :=
  HeckeExceptionalRows.bound (normalizedFactors (internalQ (sourceFixedIdeal F) η)).toFinset

lemma source_exceptional_norm (F : RHZeroFreeExtension.AnalyticHigh.IV.SourceData D) (η : Character)
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

theorem eventually_source_no_exceptional (F : RHZeroFreeExtension.AnalyticHigh.IV.SourceData D) (η : Character) :
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

theorem eventually_source_sector_gate (F : RHZeroFreeExtension.AnalyticHigh.IV.SourceData D) (η : Character) :
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

end SevenEighths.IVFullCenteredMomentNaturalFixedRaySource

end

end OAI

-- Adapted data-generic source wrapper from DetectorEnergyInitialState.lean

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentDetectorEnergyInitialState
open OAI.SevenEighths.CenteredMomentDetectorPlainFiberSource
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators SchwartzMap Topology
open Filter

namespace SevenEighths.IVFullCenteredMomentDetectorEnergyInitialState
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentRadialEligibleEnergy
open CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open IVFullCenteredMomentNaturalFixedRaySource ConcretePrimeRowBridge
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

variable {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}

theorem source_label_modulus_eventually (F:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)
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

lemma source_keep_iff (F:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(η:Character)(u:FreeRow):
    initialKeep η (internalQ (sourceFixedIdeal F) η) u.val↔¬sourceExceptional F η u:=by
  exact and_iff_right u.property.1

lemma source_fixed_gates (F:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(η:Character):
    internalQ (sourceFixedIdeal F) η≠0 ∧
    internalQ (sourceFixedIdeal F) η≤ F.modulus ∧
    internalQ (sourceFixedIdeal F) η≤η.modulus ∧
    internalQ (sourceFixedIdeal F) η≤ Ideal.span {(72:O)}:=
  ⟨internalQ_ne_zero _ (sourceFixedIdeal_ne_zero F) η,
    inf_le_left.trans (sourceFixedIdeal_le_modulus F),inf_le_right,
    inf_le_left.trans (sourceFixedIdeal_le_72 F)⟩

theorem source_energy_split_state (F:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(η:Character)
    (rows:Finset FreeRow)(f:FreeRow→ℂ):
    (∑u∈rows,‖f u‖^2)=
      (∑u∈rows.filter (fun u=> initialKeep η (internalQ (sourceFixedIdeal F) η) u.val),‖f u‖^2)+
      ∑u∈rows.filter (sourceExceptional F η),‖f u‖^2:=by
  simpa only [source_keep_iff] using source_energy_split F η rows f

theorem source_initial_states (F:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D):
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

end SevenEighths.IVFullCenteredMomentDetectorEnergyInitialState

end

end OAI

-- Adapted data-generic source wrapper from NaturalFixedRaySourcePrimeGate.lean

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.IVFullCenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily HeckePrimeRay
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentFixedRowMask CenteredMomentFixedRayInducingTransport
local notation "O" => HeckeFamily.O

def relativeBase (η : Character) (u : FreeRow) : Character :=
  (naturalRow η u.val u.property.1).character.product η.inverse

variable {Δ : ℝ} {D : RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}

theorem source_relativeBase_twists (F : RHZeroFreeExtension.AnalyticHigh.IV.SourceData D) (η : Character)
    (u : FreeRow) (hu : ¬sourceExceptional F η u) :
    ∀θ : RayQuotient.Characters F.modulus ⊤,
      (twistedFamily F.modulus ⊤ le_top (relativeBase η u) θ).residue≠1 := by
  have hn : ¬FixedInducingRow η (internalQ (sourceFixedIdeal F) η) fixedBadMask 1 u.val := by
    intro h
    apply hu
    exact (fixedInducingRow_mul_mask_iff η _ fixedBadMask (idealGenerator 1) 1 u.val
      fixedBadMask_ne_zero (idealGenerator_ne_zero _ one_ne_zero) one_ne_zero u.property.1
      (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr h
  have hn' : ¬FixedInducingRow (η.product η.inverse) (internalQ (sourceFixedIdeal F) η)
      fixedBadMask 1 u.val :=
    (not_fixedInducingRow_product_iff η η.inverse _ fixedBadMask 1 u.val inf_le_right
      fixedBadMask_ne_zero one_ne_zero u.property.1 (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hn
  apply CenteredMomentRayNonprincipal.all_ray_twists_nonprincipal F.modulus ⊤ le_top
    (η.product η.inverse) (relativeBase η u) (internalQ (sourceFixedIdeal F) η)
    fixedBadMask 1 u.val ?_ (inf_le_left.trans (sourceFixedIdeal_le_modulus F)) hn'
  exact product_row_presentation η (naturalRow η u.val u.property.1).character η.inverse
    fixedBadMask 1 u.val (by simpa only [one_mul] using (naturalRow η u.val u.property.1).element)

lemma relativeBase_modulus (M : Ideal O) [NeZero M] (η : Character) (u : FreeRow) :
    (relativeBase η u).modulus.absNorm≤ sectorConductorFactor M η*(Ideal.span {u.val}).absNorm := by
  have hb:=(HeckePrimeScale.product_modulus_bound (naturalRow η u.val u.property.1).character η.inverse).trans
    (Nat.mul_le_mul_right η.modulus.absNorm (naturalRow η u.val u.property.1).natural_modulus_bound)
  have hM : 1≤ M.absNorm := Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (NeZero.ne M))
  have hm : η.modulus.absNorm≤ M.absNorm*η.modulus.absNorm := by nlinarith
  change (relativeBase η u).modulus.absNorm≤_
  apply hb.trans
  unfold sectorConductorFactor
  calc
    _=(η.modulus.absNorm*fixedConductorFactor*η.modulus.absNorm)*(Ideal.span {u.val}).absNorm := by ring
    _≤_ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hm)

theorem eventually_source_relativeBase_gate (F : RHZeroFreeExtension.AnalyticHigh.IV.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      ∀d : ℝ,∀u : FreeRow,Z^(1/100:ℝ)≤ rowNorm u → rowNorm u≤ Z^(d-D.t) →
      let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
      ((relativeBase η₀ u).modulus.absNorm:ℝ)≤ Z^d ∧
        ∀θ : RayQuotient.Characters F.modulus ⊤,
          (twistedFamily F.modulus ⊤ le_top (relativeBase η₀ u) θ).residue≠1 := by
  have hc : ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      (sectorConductorFactor F.modulus (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ)≤ Z^D.t := by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop D.t_pos).eventually (eventually_ge_atTop _)
  filter_upwards [hc,eventually_source_no_exceptional F η,eventually_gt_atTop (0:ℝ)] with Z hc hn hZ
  intro label d u hlo hhi
  refine ⟨?_,source_relativeBase_twists F _ u (hn label u hlo)⟩
  have hb : ((relativeBase (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label) u).modulus.absNorm:ℝ)≤
      (sectorConductorFactor F.modulus (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ)*rowNorm u := by
    change _≤_*((Ideal.span {u.val}).absNorm:ℝ)
    exact_mod_cast relativeBase_modulus F.modulus _ u
  apply hb.trans
  calc
    _≤ Z^D.t*Z^(d-D.t) := mul_le_mul (hc label) hhi (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)
    _=Z^d := by rw [←Real.rpow_add hZ]; congr 1; ring

end SevenEighths.IVFullCenteredMomentNaturalFixedRaySource

end

end OAI

-- Adapted data-generic source wrapper from InverseMarkedReferenceDeletedEnergy.lean

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff Topology
namespace SevenEighths.IVFullDetectorDictionaryInverseMarkedReference
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

theorem deleted_source_energy {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}
    (F:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)
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

end SevenEighths.IVFullDetectorDictionaryInverseMarkedReference

end

end OAI

#print axioms OAI.SevenEighths.IVFullDetectorDictionaryInverseMarkedReference.deleted_source_energy

-- Adapted data-generic source wrapper from DetectorPlainExceptional.lean

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

namespace SevenEighths.IVFullCenteredMomentDetectorPlainExceptional
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSource
open CenteredMomentDetectorPlainFiberSource IVFullCenteredMomentDetectorEnergyInitialState
open CenteredMomentRetainedEnergy CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentUncenteredTerminal CenteredMomentHeckeColumnWindow
open CenteredMomentSourceRectangleEnergy CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open IVFullCenteredMomentNaturalFixedRaySource ProbeHighRowFamily HeckeDetectorRawFiber HeckeDetectorBatch
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

variable {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}

theorem source_fibers_eventually_retained (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(η:Character):
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

theorem source_exceptional_energy_eventually_zero (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(η:Character):
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

theorem source_batch_plain_retained (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(η:Character):
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

end SevenEighths.IVFullCenteredMomentDetectorPlainExceptional

end

end OAI

-- Adapted data-generic source wrapper from NaturalFixedRaySourcePrimeBound.lean

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators ComplexConjugate ContDiff Topology
open Filter

namespace SevenEighths.IVFullCenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily HeckePrimeRay
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot HeckeZeroSupremum
local notation "O" => HeckeFamily.O
variable {Δ : ℝ} {D : RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}

theorem source_physical_slot_bound (F : RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)
    (loss lo hi κ : ℝ) (hloss : 0< loss) (hbeta : (51/100:ℝ)≤ beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0< C ∧ ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),∀d : ℝ,d≤1 →
      ∀u : FreeRow,Z^(1/100:ℝ)≤ rowNorm u → rowNorm u≤ Z^(d-D.t) →
      ∀P t : ℝ,1≤ P → P≤ Z → ∀z : ℂ,lo≤1-z.re → 1-z.re≤ hi →
      let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
      ‖normalizedSlot η₀ fixedBadMask 1 u.val (primePool F.modulus ⊤ 2 P)
        (physicalSlotCoefficient η₀ F.W P z) t P‖^2≤
        C*(1+|t|+|z.im|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,hbound⟩:=CenteredMomentPrimeHeight.ray_prime_all_height_squared
    F.modulus ⊤ le_top F.W 1 2 (by norm_num) F.complex_support (F.W.smooth ⊤)
    1 1 loss lo hi κ (by norm_num) (by norm_num) hloss hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro η
  filter_upwards [eventually_source_relativeBase_gate F η,eventually_ge_atTop Z₀,
    eventually_ge_atTop (1:ℝ)] with Z hgate hZ0 hZ
  intro label d hd u hlo hhi P t hP hPZ z hzlo hzhi
  let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
  obtain ⟨hc,hn⟩:=hgate label d u hlo hhi
  have hc' : ((relativeBase η₀ u).modulus.absNorm:ℝ)≤ Z^(1:ℝ) :=
    hc.trans (Real.rpow_le_rpow_of_exponent_le hZ hd)
  have hb:=hbound Z P hZ0 hP (by simpa only [Real.rpow_one] using hPZ)
    (relativeBase η₀ u) hc' hn (1-z.re) (t-z.im) hzlo hzhi
  have hconj : (fun y=> conj (F.W y))=(F.W:ℝ→ℂ) := by
    funext y
    rw [F.complex_eq]
    simp
  dsimp only
  rw [physicalSlot_eq_relativeRay F.modulus ⊤ η₀ (naturalRow η₀ u.val u.property.1).character
    fixedBadMask 1 u.val (by simpa only [one_mul] using (naturalRow η₀ u.val u.property.1).element)
    F.W 2 P t z (zero_lt_one.trans_le hP),hconj,norm_mul,
    CenteredMomentTwist.norm_real_imaginary_power P t (zero_lt_one.trans_le hP),one_mul]
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hP) _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  apply mul_le_mul_of_nonneg_left _ hC.le
  have habs : |t-z.im|≤|t|+|z.im| := by simpa using (abs_sub_le t 0 z.im)
  exact pow_le_pow_left₀ (by positivity) (by linarith) degree

end SevenEighths.IVFullCenteredMomentNaturalFixedRaySource

end

end OAI

-- Adapted data-generic source wrapper from DetectorPlainMarkedState.lean

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentDetectorPlainCapacity
open OAI.SevenEighths.CenteredMomentDetectorPlainExceptional
open OAI.SevenEighths.CenteredMomentDetectorPlainFiberSource
open OAI.SevenEighths.CenteredMomentDetectorPlainMarkedState
open OAI.SevenEighths.CenteredMomentDetectorPlainSlotProfile
open OAI.SevenEighths.CenteredMomentDetectorPlainStateDictionary
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators SchwartzMap ComplexConjugate Topology ContDiff
open Filter

namespace SevenEighths.IVFullCenteredMomentDetectorPlainMarkedState
open HeckeFamily HeckeDyadic HeckeDetectorRawFiber HeckeDetectorBatch HeckePrimeAnnular
open HeckeInverseAmplification HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorPlainStateDictionary IVFullCenteredMomentDetectorPlainExceptional
open CenteredMomentDetectorPlainFiberSource IVFullCenteredMomentDetectorPlainCapacity
open IVFullCenteredMomentDetectorPlainSlotProfile IVFullCenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorDictionary CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional IVFullCenteredMomentNaturalFixedRaySource
open ConcretePrimeRowBridge ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}
variable {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}

theorem source_slot_coefficient (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (hprofile:∀s x,F.profile s x=S.W x)(η:Character)(s:Slot)
    (hreal:(F.external s).re=17/50)(hU:0< U)(I:Ideal O):
    idealCoeff η.inverse I*slotWindow F s ((I.absNorm:ℝ)/(U^(F.widths s)))=
      idealCoeff η.inverse I*annularWeight (fun x=> conj (S.W x))
        (U^(F.widths s)) (33/50) (-(F.external s).im) I := by
  have he:=physical_annular_all S η (U^(F.widths s)) (Real.rpow_pos_of_pos hU _)
    (F.external s) I
  rw [hreal] at he
  norm_num at he
  simpa only [physicalSlotCoefficient,slotWindow,hprofile] using he

theorem retained_eq_initial_energy (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (hprofile:∀s x,F.profile s x=S.W x)(hupper:∀s,F.upper s=2)
    (η:Character)(Q:Ideal O)(selected:Finset Slot)
    (hreal:∀s∈selected,(F.external s).re=17/50)
    (Φ:𝓢(ℝ,ℂ))(bΦ δ:ℝ)(hU:1≤ U)(hδ:0≤δ)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0≤(Φ x).re)
    (hη:(η.modulus.absNorm:ℝ)≤ U^δ)(j k:ℕ)(σ t:ℝ):
    let state:=initialState η Q Φ bΦ U δ hU hδ hs hp hη
    IVFullCenteredMomentDetectorPlainExceptional.retainedSourceEnergy state.radial.keep F η selected j k σ t Φ=
      energy state.character state.mask 1 0
        ((detectorProfiles F.reverse j k σ t).profile 0)
        ((detectorProfiles F.reverse j k σ t).profile 1)
        (fun s:selected=> CenteredMomentPrimeSlot.primePool M H 2 (U^(F.widths s.val)))
        (fun (s:selected) I=> idealCoeff η.inverse I*
          annularWeight (fun x=> conj (S.W x)) (U^(F.widths s.val)) (33/50)
            (-(F.external s.val).im) I)
        (fun s:selected=> U^(F.widths s.val)) (U^F.m) (U^F.m)
        state.radial.keep state.radial.profile state.radial.scale := by
  dsimp only
  change CenteredMomentDetectorPlainExceptional.retainedSourceEnergy
    (initialState η Q Φ bΦ U δ hU hδ hs hp hη).radial.keep F η selected j k σ t Φ = _
  rw [CenteredMomentDetectorPlainStateDictionary.retainedSourceEnergy_eq_energy _ _ _ _ _ _ _ _ _ (zero_lt_one.trans_le hU)]
  have hc:(fun (s:selected) I=> idealCoeff η.inverse I*
      slotWindow F s.val ((I.absNorm:ℝ)/(U^(F.widths s.val))))=
      (fun (s:selected) I=> idealCoeff η.inverse I*
        annularWeight (fun x=> conj (S.W x)) (U^(F.widths s.val)) (33/50)
          (-(F.external s.val).im) I):=by
    funext s I
    exact source_slot_coefficient S F hprofile η s.val (hreal s.val s.property)
      (zero_lt_one.trans_le hU) I
  rw [hc]
  simp only [hupper,plainProfile_eq_detectorSchwartz,initialState,NaturalState.mask,
    detectorProfiles,reduceIte,Fin.one_eq_zero_iff]
  norm_num

theorem plain_length_eq [NeZero M]
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(hU:1< U):
    length U (U^F.m)=F.m := by
  have hm:0≤ F.m:=(F.lengths hU).2.2.2.2
  rw [length,max_eq_right (Real.one_le_rpow hU.le hm),
    Real.logb_rpow (zero_lt_one.trans hU) hU.ne']

theorem marked_capacity [NeZero M]
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(hU:1< U)
    (selected:Finset Slot)(κ δ:ℝ)(hδ:0≤δ)
    (hcap:2*F.m+6*κ*(∑s∈selected,F.widths s)≤1):
    length U (U^F.m)+length U (U^F.m)+6*κ*(∑s:selected,F.widths s.val)≤1+δ := by
  rw [plain_length_eq F hU,Finset.sum_coe_sort]
  linarith

theorem selected_widths (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(hselected:selected⊆F.slots):
    (∀s:selected,0< F.widths s.val) ∧ (∀s:selected,F.widths s.val≤ F.mesh) :=
  ⟨fun s=> F.widths_pos s.val (hselected s.property),
    fun s=> F.widths_mesh s.val (hselected s.property)⟩

theorem source_profile_uniform (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(Hsemin:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃C:ℝ,0< C ∧ ∀{ι:Type*}(ζ:ι→ℂ)(height:ℝ),0≤ height→
      (∀s,(ζ s).re=17/50)→(∀s,|(ζ s).im|≤ height)→∀s,
      Hsemin.sup (schwartzSeminormFamily ℝ ℝ ℂ) (slotSchwartz S (ζ s))≤
        C*(1+height)^J :=
  slotSchwartz_height_uniform S Hsemin

theorem source_relative_fixed_gates (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(η:Character):
    internalQ (sourceFixedIdeal S) η≠0 ∧
    internalQ (sourceFixedIdeal S) η≤ S.modulus ∧
    internalQ (sourceFixedIdeal S) η≤η.inverse.modulus ∧
    internalQ (sourceFixedIdeal S) η≤ Ideal.span {(72:O)} :=
  source_fixed_gates S η

theorem fixed_window_data (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D):
    Function.support (fun x=> conj (S.W x))⊆Set.Icc (1:ℝ) 2 ∧
    ContDiff ℝ ∞ (fun x=> conj (S.W x)) ∧ ∀x,‖conj (S.W x)‖≤1 := by
  refine ⟨conjugate_source_support S,
    Complex.conjCLE.contDiff.comp (S.W.smooth ⊤),?_⟩
  intro x
  rw [RCLike.norm_conj,S.complex_eq,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (S.bounded x).1]
  exact (S.bounded x).2

theorem source_batch_marked_initial (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D):
    ∃bΦ:ℝ,0< bΦ ∧ ∀η:Character,∀δ:ℝ,0<δ→
      ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀d:ℝ,(1/200:ℝ)≤ d→∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=> D.ell s/d)→
      (∀s,B.upper s=2)→(∀s,(B.external s).re=17/50)→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      ∀selected:Finset (Fin D.N),selected⊆B.slots→
      let F:=B.fiber bin label J K hne;
      2*F.m+6*(RHIVProbe.fullMomentKappa)*(∑s∈selected,F.widths s)≤1→
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      ∃state:NaturalState (Z^d) 0 bΦ,
        state.character=η₀ ∧ state.fixedModulus=internalQ (sourceFixedIdeal S) η₀ ∧
        state.puncture=1 ∧ state.radial.profile=radialMajorant ∧ state.radial.scale=Z^d ∧
        state.radial.keep=initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀) ∧
        state.width=1+δ ∧
        length (Z^d) ((Z^d)^F.m)+length (Z^d) ((Z^d)^F.m)+
          6*(RHIVProbe.fullMomentKappa)*(∑s:selected,F.widths s.val)≤ state.width ∧
        (∀s:selected,0< F.widths s.val ∧ F.widths s.val≤ F.mesh) ∧
        ∀j k:ℕ,∀σ t:ℝ,
        (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
          ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
          ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2)≤
          energy state.character state.mask 1 0
            ((detectorProfiles F.reverse j k σ t).profile 0)
            ((detectorProfiles F.reverse j k σ t).profile 1)
            (fun s:selected=> CenteredMomentPrimeSlot.primePool S.modulus ⊤ 2 ((Z^d)^(F.widths s.val)))
            (fun (s:selected) I=> idealCoeff η₀.inverse I*
              annularWeight (fun x=> conj (S.W x)) ((Z^d)^(F.widths s.val)) (33/50)
                (-(F.external s.val).im) I)
            (fun s:selected=>(Z^d)^(F.widths s.val)) ((Z^d)^F.m) ((Z^d)^F.m)
            state.radial.keep state.radial.profile state.radial.scale := by
  obtain ⟨bΦ,hbΦ,hs⟩:=radialMajorant_support_bound
  refine ⟨bΦ,hbΦ,?_⟩
  intro η δ hδ
  filter_upwards [source_label_modulus_eventually S η δ hδ,source_batch_plain_retained S η] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro rows hrows d hd a ε tstar T allowance i B hB hdata hprofile hwidth hupper hreal
    bin label J K hne selected hselected F hcap η₀
  have hdpos:0< d:=by linarith
  have hU:1< Z^d:=Real.one_lt_rpow hz.1 hdpos
  have hη:(η₀.modulus.absNorm:ℝ)≤(Z^d)^δ:=hz.2 label d hd
  let state:=initialState η₀ (internalQ (sourceFixedIdeal S) η₀) radialMajorant bΦ
    (Z^d) δ hU.le hδ.le hs radialMajorant_nonneg hη
  refine ⟨state,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_⟩
  · exact marked_capacity F hU selected _ δ hδ.le hcap
  · intro s
    exact ⟨F.widths_pos s.val (hselected s.property),F.widths_mesh s.val (hselected s.property)⟩
  · intro j k σ t
    have hb:=hr.2 rows hrows d hdpos.ne' a ε tstar T allowance i B hB hdata hprofile hwidth
      bin label J K hne selected j k σ t
    have hprof:∀s x,F.profile s x=S.W x:=by
      intro s x
      change B.profile s x=S.W x
      rw [hprofile,S.complex_eq]
    have he:=retained_eq_initial_energy S F hprof hupper η₀ (internalQ (sourceFixedIdeal S) η₀) selected
      (fun s _=> hreal s) radialMajorant bΦ δ hU.le hδ.le hs radialMajorant_nonneg hη j k σ t
    exact hb.trans_eq he

end SevenEighths.IVFullCenteredMomentDetectorPlainMarkedState

end

end OAI

-- Adapted data-generic source wrapper from InverseMarkedReferenceFiberEnergy.lean

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.IVFullDetectorDictionaryInverseMarkedReference
open DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeInverseAmplification HeckeDyadic HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer InverseMoment InverseInitialProfile
open ConcreteTraceCRT ConcretePrimeRowBridge CanonicalRowCompletion
open DetectorDictionaryInverseRawInitialGates DetectorDictionaryInverseMarkedPhysicalRows
open InverseInitialPhysicalSlots IdealMobiusDivisorSum
local notation "O"=> HeckeFamily.O

theorem fiber_reference_energy {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}
    (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)
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

end SevenEighths.IVFullDetectorDictionaryInverseMarkedReference

end

end OAI

#print axioms OAI.SevenEighths.IVFullDetectorDictionaryInverseMarkedReference.fiber_reference_energy

-- Adapted data-generic source wrapper from DetectorPlainMomentParameters.lean

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentDetectorPlainMarkedState
open OAI.SevenEighths.CenteredMomentDetectorPlainMomentParameters
open OAI.SevenEighths.CenteredMomentDetectorPlainUnmarkedState
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.IVFullCenteredMomentDetectorPlainMomentParameters
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open CenteredMomentDetectorDictionary
open CenteredMomentEnergyState CenteredMomentEnergyBands
open IVFullCenteredMomentDetectorEnergyInitialState IVFullCenteredMomentDetectorPlainMarkedState
open CenteredMomentDetectorPlainUnmarkedState IVFullCenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

variable {Δ:ℝ}

def delta (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ):ℝ := D.t/4
def stageError (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ):ℝ := D.t/4
def kappaPlain (_D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ):ℝ := RHIVProbe.fullMomentKappa

theorem fixed_parameters (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ):
    0< delta D ∧ delta D≤1/4 ∧ 0< stageError D ∧
    delta D+stageError D≤ D.t ∧ 13/18≤ kappaPlain D ∧ 0< kappaPlain D := by
  have hk := RHIVProbe.full_moment_range
  dsimp [delta,stageError,kappaPlain]
  constructor
  · exact div_pos D.t_pos (by norm_num)
  constructor
  · linarith [D.t_small]
  constructor
  · exact div_pos D.t_pos (by norm_num)
  constructor
  · linarith [D.t_pos]
  constructor <;> linarith

lemma source_base_gt_one (_D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ)(Z d:ℝ)
    (hZ:1< Z)(hd:(1/200:ℝ)≤ d):1< Z^d :=
  Real.one_lt_rpow hZ (by linarith)

lemma witness_length_cap (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ):
    1/2+75*D.ε≤(23/40:ℝ) := by linarith [D.epsilon_small]

lemma original_width_bounds (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ)(d:ℝ)
    (hd:(1/200:ℝ)≤ d)(s:Fin D.N):0< D.ell s/d ∧ D.ell s/d≤ D.t := by
  have hdpos:0< d:=by linarith
  refine ⟨div_pos (D.slots_bounds s).1 hdpos,(div_le_iff₀ hdpos).mpr ?_⟩
  have hs: D.ell s≤(1/200:ℝ)*D.t:=(D.slots_bounds s).2.2
  nlinarith [D.t_pos]

variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label:Type*}
variable {U a tstar T heightAllowance:ℝ}{i:ℕ}

theorem actual_fiber_lengths (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)(hU:1< U):
    0≤ F.m ∧ F.m≤1/2+75*D.ε ∧ F.m≤23/40 ∧
    1≤ U^F.m ∧ U^F.m≤ U ∧ length U (U^F.m)=F.m := by
  have hm:=F.lengths hU
  have hcap:=hm.2.2.1.trans (witness_length_cap D)
  refine ⟨hm.2.2.2.2,hm.2.2.1,hcap,Real.one_le_rpow hU.le hm.2.2.2.2,?_,?_⟩
  · simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hU.le (show F.m≤1 by linarith)
  · exact IVFullCenteredMomentDetectorPlainMarkedState.plain_length_eq F hU

theorem batch_fiber_parameters (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ)(Z d:ℝ)
    (hZ:1< Z)(hd:(1/200:ℝ)≤ d)
    (B:Batch M H Label (Fin D.N) (Z^d) a D.ε tstar T heightAllowance i)
    (hwidth:B.widths=(fun s=> D.ell s/d))
    (bin label J K)(hne:(B.fiberRows bin label J K).Nonempty):
    let F:=B.fiber bin label J K hne;
    1< Z^d ∧ 0≤ F.m ∧ F.m≤1/2+75*D.ε ∧ F.m≤23/40 ∧
    1≤(Z^d)^F.m ∧ (Z^d)^F.m≤ Z^d ∧ length (Z^d) ((Z^d)^F.m)=F.m ∧
    (∀s,0< F.widths s ∧ F.widths s≤ D.t) ∧
    (∀selected:Finset (Fin D.N),∀s:selected,0< F.widths s.val ∧ F.widths s.val≤ D.t) := by
  dsimp only
  have hU:=source_base_gt_one D Z d hZ hd
  have hf:=actual_fiber_lengths D (B.fiber bin label J K hne) hU
  have hw:∀s,0<(B.fiber bin label J K hne).widths s ∧
      (B.fiber bin label J K hne).widths s≤ D.t:=by
    intro s
    change 0< B.widths s ∧ B.widths s≤ D.t
    rw [hwidth]
    exact original_width_bounds D d hd s
  exact ⟨hU,hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,hf.2.2.2.2.2,
    hw,fun _ s=> hw s.val⟩

lemma width_bands (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ)(m:ℝ)(hm:m≤23/40):
    1≤1+delta D ∧ 1+delta D≤2 ∧
    1≤ max 1 (2*m)+delta D ∧ max 1 (2*m)+delta D≤2 := by
  have hδ:0< delta D:=(fixed_parameters D).1
  have hd:delta D≤1/4:=(fixed_parameters D).2.1
  have hmax:max 1 (2*m)≤23/20:=max_le (by norm_num) (by linarith)
  have hlo:=le_max_left (1:ℝ) (2*m)
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem marked_state_admission (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ:ℝ)(hU:1< U)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0≤(Φ x).re)
    (hη:(η.modulus.absNorm:ℝ)≤ U^(delta D))
    (selected:Finset (Fin D.N))
    (hcap:2*F.m+6*(kappaPlain D)*(∑s∈selected,F.widths s)≤1):
    let s:=initialState η Q Φ bΦ U (delta D) hU.le (fixed_parameters D).1.le hs hp hη;
    s.character=η ∧ s.fixedModulus=Q ∧ s.puncture=1 ∧
    s.radial.profile=Φ ∧ s.radial.scale=U ∧ s.radial.keep=initialKeep η Q ∧
    s.width=1+delta D ∧ 1≤ s.width ∧ s.width≤2 ∧
    1≤ U^F.m ∧ U^F.m≤ U ∧
    length U (U^F.m)+length U (U^F.m)+
      6*(kappaPlain D)*(∑s:selected,F.widths s.val)≤ s.width := by
  dsimp only
  have hf:=actual_fiber_lengths D F hU
  have hw:=width_bands D F.m hf.2.2.1
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,hw.1,hw.2.1,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  exact IVFullCenteredMomentDetectorPlainMarkedState.marked_capacity F hU selected (kappaPlain D) (delta D) (fixed_parameters D).1.le hcap

theorem unmarked_state_admission (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ:ℝ)(hU:1< U)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0≤(Φ x).re)
    (hη:(η.modulus.absNorm:ℝ)≤ U^(delta D)):
    let s:=state F η Q Φ bΦ (delta D) hU.le (fixed_parameters D).1.le hs hp hη;
    s.character=η ∧ s.fixedModulus=Q ∧ s.puncture=1 ∧
    s.radial.profile=Φ ∧ s.radial.scale=U ∧ s.radial.keep=initialKeep η Q ∧
    s.width=max 1 (2*F.m)+delta D ∧ 1≤ s.width ∧ s.width≤2 ∧
    1≤ U^F.m ∧ U^F.m≤ U ∧ 2*length U (U^F.m)≤ s.width := by
  dsimp only
  have hf:=actual_fiber_lengths D F hU
  have hw:=width_bands D F.m hf.2.2.1
  have he:(state F η Q Φ bΦ (delta D) hU.le (fixed_parameters D).1.le hs hp hη).width=
      max 1 (2*F.m)+delta D:=padded_width _ _
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,he,?_,?_,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  · rw [he];exact hw.2.2.1
  · rw [he];exact hw.2.2.2
  · rw [he,hf.2.2.2.2.2]
    exact (le_max_right 1 (2*F.m)).trans (le_add_of_nonneg_right (fixed_parameters D).1.le)

theorem source_label_fixed_allowance (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ)
    (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀label:Sum Bool (RayQuotient.Characters S.modulus ⊤),∀d:ℝ,(1/200:ℝ)≤ d→
      ((sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label).modulus.absNorm:ℝ)
        ≤(Z^d)^(delta D) :=
  source_label_modulus_eventually S η (delta D) (fixed_parameters D).1

lemma final_exponent_budget (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ)(base:ℝ):
    base+delta D+stageError D≤ base+D.t := by
  linarith [(fixed_parameters D).2.2.2.1]

end SevenEighths.IVFullCenteredMomentDetectorPlainMomentParameters

end

end OAI

-- Adapted data-generic source wrapper from DetectorInverseMarkedField.lean

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.ProbeDetectorInverseMarkedField
open RHZeroFreeExtension.AnalyticHigh

open scoped Classical BigOperators Topology SchwartzMap ContDiff
namespace SevenEighths.IVFullProbeDetectorInverseMarkedField
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorCoefficientTransfer
open ProbeHighRowFamily ProbeFinalAssembly Filter
open DetectorDictionaryInverseMarkedReference DetectorDictionaryInverseClippedUniform
local notation "O"=> HeckeFamily.O

variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)
local instance:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _

theorem source_batch_inverse_marked {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}
    (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D):
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
  obtain ⟨Jref,hreference⟩:=IVFullDetectorDictionaryInverseMarkedReference.fiber_reference_energy S referenceWindow (1/18) (13/4)
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
    IVFullHeckeDetectorMomentPrimeGeometry.sourceMoment_fiber_prime_geometry_eventually M H hH S η D.t D.t_pos] with Z hZ hscale hlarge hgeom
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

end SevenEighths.IVFullProbeDetectorInverseMarkedField

end

end OAI

-- Adapted data-generic source wrapper from DetectorPlainMarkedFineField.lean

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentDetectorPlainFiberSource
open OAI.SevenEighths.CenteredMomentDetectorPlainMarkedState
open OAI.SevenEighths.CenteredMomentDetectorPlainMomentParameters
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open OAI.SevenEighths.ProbeDetectorPlainMarkedFineField
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter

namespace SevenEighths.IVFullProbeDetectorPlainMarkedFineField
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles ProbeHighRowFamily ProbeFinalAssembly
open QuadraticInitialBound CenteredMomentDetectorDictionary
open CenteredMomentEnergyBands CenteredMomentEnergyState CenteredMomentInductionEnergy
open IVFullCenteredMomentDetectorEnergyInitialState IVFullCenteredMomentDetectorPlainMarkedState
open IVFullCenteredMomentDetectorPlainMomentParameters IVFullCenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorPlainFiberSource
local notation "O"=> HeckeFamily.O

def PositiveFineSourceInput {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}(S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(mesh:ℝ):Prop:=
  ∀bΦ:ℝ,0< bΦ→∃degree:ℕ,∃seminorms:Finset (ℕ×ℕ),
    ∀η₀:Character,∃C:ℝ,0< C ∧ ∀ᶠU:ℝ in atTop,
      PositiveAt (α:=Fin D.N) S.modulus ⊤ le_top (fun x=> conj (S.W x))
        2 (1/4) (9/4) bΦ 0 1 mesh (33/50) (33/50) 2 (stageError D)
        (kappaPlain D) U η₀ (sourceFixedIdeal S) degree seminorms C

theorem source_batch_plain_marked_fine {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}
    (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(mesh:ℝ)(hmesh:0< mesh)(hfine:∀j,D.ell j≤ mesh/200)
    (henergy:PositiveFineSourceInput S mesh):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,
    1< Z ∧ ∀rows:Finset FreeRow,(∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
    ∀d:ℝ,(1/200:ℝ)≤ d→∀(a tstar T allowance:ℝ)(i:ℕ)
    (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
      (Z^d) a D.ε tstar T allowance i),B.rows⊆rows→
    B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
    B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=> D.ell s/d)→
    (∀s,B.upper s=2)→(∀s,(B.external s).re=17/50)→
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤ height→(∀s,|(B.external s).im|≤ height)→
    let F:=B.fiber bin label left right hne;
    ∀selected:Finset (Fin D.N),selected⊆F.slots→
      2*F.m+6*(RHIVProbe.fullMomentKappa)*(∑s∈selected,F.widths s)≤1→
    ∀j k:ℕ,j+k≤2→∀σ∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2)≤
        (C*(1+height)^J)*(Z^d)^(1+D.t):=by
  obtain ⟨bΦ,hbΦ,hsource⟩:=source_batch_marked_initial S
  obtain ⟨degree,seminorms,henergy⟩:=henergy bΦ hbΦ
  obtain ⟨J,Cprofile,hCprofile,hprofile⟩:=
    CenteredMomentDetectorPlainProfileControl.source_height_factor seminorms
  refine ⟨J+degree,?_⟩
  intro η
  let data:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η
  choose C hC hbound using fun label=> henergy (data label)
  choose U₀ hU₀ using fun label=> Filter.eventually_atTop.mp (hbound label)
  let Csum:ℝ:=1+∑label,C label
  have hCsum:0< Csum:=by
    have h:=Finset.sum_nonneg (fun label (_:label∈Finset.univ)=>(hC label).le)
    dsimp [Csum];linarith
  have hClabel (label):C label≤ Csum:=by
    have h:=Finset.single_le_sum (fun label (_:label∈Finset.univ)=>(hC label).le)
      (Finset.mem_univ label)
    dsimp [Csum];linarith
  have hscale:∀ᶠZ:ℝ in atTop,∀label,∀d:ℝ,(1/200:ℝ)≤ d→U₀ label≤ Z^d:=by
    apply Filter.eventually_all.mpr
    intro label
    exact HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) (U₀ label) (by norm_num)
  let Cfinal:=Csum*(1+diagonalControl radialMajorant)*Cprofile
  have hdiag:0≤ diagonalControl radialMajorant:=diagonalControl_nonneg _
  refine ⟨Cfinal,by dsimp [Cfinal];positivity,?_⟩
  filter_upwards [hsource η (delta D) (fixed_parameters D).1,hscale] with Z hs hscale
  refine ⟨hs.1,?_⟩
  intro rows hrows d hd a tstar T allowance i B hB hdata hprof hwidth hupper hreal
    bin label left right hne height hheight hexternal F selected hselected hcap j k hjk σ hσ t ht
  have hU:1< Z^d:=source_base_gt_one D Z d hs.1 hd
  obtain ⟨state,hchar,hQ,hpuncture,hΦ,hK,hkeep,hwidthstate,hcapacity,hwidths,hrow⟩:=
    hs.2 rows hrows d hd a D.ε tstar T allowance i B hB hdata hprof hwidth hupper hreal
      bin label left right hne selected hselected hcap
  have hf:=actual_fiber_lengths D F hU
  have hstate:state.width≤2:=by rw [hwidthstate];exact (width_bands D F.m hf.2.2.1).2.1
  have hw (s:selected):0≤ F.widths s.val:=(hwidths s).1.le
  have hwcap (s:selected):F.widths s.val≤ mesh:=by
    change B.widths s.val≤ mesh
    rw [hwidth]
    exact (RHZeroFreeExtension.AnalyticHigh.IV.fine_slot_widths D (fun _=> mesh) hmesh hfine d hd s.val).2
  have hpos:=hU₀ label (Z^d) (hscale label d hd) selected (fun _=>1)
    (fun s=> F.widths s.val) (fun _=>(33/50:ℝ)) (fun s=>-(F.external s.val).im)
    0 height hw hwcap (fun _=> le_rfl) (fun _=> le_rfl) hheight
    (fun s=> by change |-(B.external s.val).im|≤ height; simpa only [abs_neg] using hexternal s.val)
    state hQ hstate (detectorProfiles F.reverse j k σ t) ((Z^d)^F.m) ((Z^d)^F.m)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _) (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _)
    (by simpa only [Real.rpow_one] using hf.2.2.2.2.1)
    (by simpa only [Real.rpow_one] using hf.2.2.2.2.1) hcapacity
  have heq:=CenteredMomentDetectorPlainRelativeClass.energy_eq S.modulus ⊤ le_top
    state.character (data label) (fun (_:selected)=>1) state.mask 1
    ((detectorProfiles F.reverse j k σ t).profile 0)
    ((detectorProfiles F.reverse j k σ t).profile 1)
    (fun _=>2) (fun s:selected=>(Z^d)^(F.widths s.val))
    (fun s I=> HeckePrimeAnnular.annularWeight (fun x=> conj (S.W x))
      ((Z^d)^(F.widths s.val)) (33/50) (-(F.external s.val).im) I)
    0 ((Z^d)^F.m) ((Z^d)^F.m) state.radial.keep state.radial.profile state.radial.scale
  have hnorm:=hprofile degree F.reverse j k hjk σ hσ height t hheight (abs_le.mpr ht)
  have hp:0≤(detectorProfiles F.reverse j k σ t).control seminorms ^2:=sq_nonneg _
  have hexp:state.width+stageError D≤1+D.t:=by
    rw [hwidthstate];linarith [(fixed_parameters D).2.2.2.1]
  calc
    _≤_:=hrow j k σ t
    _≤ C label*diagonalControl state.radial.profile*
        (detectorProfiles F.reverse j k σ t).control seminorms ^2*
        (1+|(0:ℝ)|+height)^degree*(Z^d)^(state.width+stageError D):=by
      exact heq.le.trans hpos
    _≤(Cfinal*(1+height)^(J+degree))*(Z^d)^(1+D.t):=by
      rw [hΦ]
      have hpow:=Real.rpow_le_rpow_of_exponent_le hU.le hexp
      calc
        _=(C label*diagonalControl radialMajorant)*
          ((detectorProfiles F.reverse j k σ t).control seminorms ^2*
            (1+|(0:ℝ)|+height)^degree)*(Z^d)^(state.width+stageError D):=by ring
        _≤(Csum*(1+diagonalControl radialMajorant))*
          (Cprofile*(1+height)^(J+degree))*(Z^d)^(1+D.t):=by
          apply mul_le_mul _ hpow (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
          apply mul_le_mul _ hnorm (by positivity) (by positivity)
          exact mul_le_mul (hClabel label) (by linarith) hdiag hCsum.le
        _=_:=by dsimp [Cfinal];ring
end SevenEighths.IVFullProbeDetectorPlainMarkedFineField

end

end OAI

-- Adapted data-generic source wrapper from DetectorInverseFields.lean

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.ProbeDetectorInverseFields
open RHZeroFreeExtension.AnalyticHigh

open scoped Classical BigOperators Topology
namespace SevenEighths.IVFullProbeDetectorInverseFields
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

theorem source_batch_inverse_fields {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}
    (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(counts:IVRawCountParameters M H D.t):
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
  obtain ⟨Jr,hr⟩ := IVProbeDetectorInverseRawField.source_batch_inverse_raw
    M H hH S.S S.exclusions.prime D.t counts
  obtain ⟨Jm,hm⟩ := IVFullProbeDetectorInverseMarkedField.source_batch_inverse_marked M H hH S
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

end SevenEighths.IVFullProbeDetectorInverseFields

end

end OAI

-- Adapted data-generic source wrapper from DetectorPlainUnmarkedField.lean

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentDetectorPlainExceptional
open OAI.SevenEighths.CenteredMomentDetectorPlainFiberSource
open OAI.SevenEighths.CenteredMomentDetectorPlainMomentParameters
open OAI.SevenEighths.CenteredMomentDetectorPlainProfileControl
open OAI.SevenEighths.CenteredMomentDetectorPlainUnmarkedState
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open OAI.SevenEighths.ProbeDetectorPlainUnmarkedField
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.IVFullProbeDetectorPlainUnmarkedField
open HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorDictionary IVFullCenteredMomentDetectorEnergyInitialState
open IVFullCenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainUnmarkedState
open IVFullCenteredMomentDetectorPlainMomentParameters CenteredMomentDetectorPlainProfileControl
open CenteredMomentEnergyState CenteredMomentEnergyBands IVFullCenteredMomentNaturalFixedRaySource
open QuadraticInitialBound
local notation "O" => HeckeFamily.O

def radialSupportUpper : ℝ := Classical.choose radialMajorant_support_bound

theorem radialSupportUpper_spec : 0< radialSupportUpper ∧
    Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic radialSupportUpper :=
  Classical.choose_spec radialMajorant_support_bound

lemma unmarked_power_eq (U m e:ℝ)(hU:1≤ U):
    U^(max 1 (2*m)+e)=max U ((U^m)^2)*U^e := by
  have hpos:0< U:=zero_lt_one.trans_le hU
  rw [Real.rpow_add hpos]
  congr 1
  have hs:(U^m)^2=U^(2*m):=by
    rw [←Real.rpow_natCast,←Real.rpow_mul hpos.le]
    congr 1
    norm_num
    ring
  rw [hs]
  by_cases hm:1≤2*m
  · rw [max_eq_right hm,max_eq_right]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU hm
  · have hm':2*m≤1:=le_of_not_ge hm
    rw [max_eq_left hm',max_eq_left]
    · exact Real.rpow_one U
    · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU hm'

variable {Δ:ℝ}

theorem retained_unmarked_bound (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ)
    {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label:Type*}
    {U a tstar T heightAllowance:ℝ}{i:ℕ}
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(hU:1< U)
    (hη:(η.modulus.absNorm:ℝ)≤ U^(delta D))
    (degree:ℕ)(S:Finset (ℕ×ℕ))(A:ℝ)
    (hzero:ZeroAt Q (1/4) (9/4) radialSupportUpper 0 1 2 (stageError D) U degree S A)
    (j k:ℕ)(σ t:ℝ):
    CenteredMomentDetectorPlainExceptional.retainedSourceEnergy (initialKeep η Q) F η ∅ j k σ t radialMajorant ≤
      A*diagonalControl radialMajorant*(detectorProfiles F.reverse j k σ t).control S ^2*
        U^(max 1 (2*F.m)+delta D+stageError D) := by
  let s:=state F η Q radialMajorant radialSupportUpper (delta D) hU.le
    (fixed_parameters D).1.le radialSupportUpper_spec.2 radialMajorant_nonneg hη
  have hs:=unmarked_state_admission D F η Q radialMajorant radialSupportUpper hU
    radialSupportUpper_spec.2 radialMajorant_nonneg hη
  have hwidth:s.width=max 1 (2*F.m)+delta D:=hs.2.2.2.2.2.2.1
  have hband:s.width≤2:=hs.2.2.2.2.2.2.2.2.1
  have hscale:1≤ U^F.m ∧ U^F.m≤ U:=⟨hs.2.2.2.2.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.2.2.2.1⟩
  have hz:=hzero s rfl hband (detectorProfiles F.reverse j k σ t) 0 (U^F.m) (U^F.m)
    (zero_lt_one.trans_le hscale.1) (zero_lt_one.trans_le hscale.1)
    (by simpa only [Real.rpow_one] using hscale.2)
    (by simpa only [Real.rpow_one] using hscale.2)
  change CenteredMomentDetectorPlainExceptional.retainedSourceEnergy
    (CenteredMomentDetectorEnergyInitialState.initialKeep η Q) F η ∅ j k σ t radialMajorant ≤ _
  rw [actual_source_eq F η Q radialMajorant radialSupportUpper (delta D) hU.le
    (fixed_parameters D).1.le radialSupportUpper_spec.2 radialMajorant_nonneg hη j k σ t]
  have hrad:s.radial.profile=radialMajorant:=rfl
  simpa only [hwidth,hrad,norm_zero,add_zero,one_pow,mul_one,
    CenteredMomentDetectorEnergyInitialState.detectorProfiles,
    IVFullCenteredMomentDetectorEnergyInitialState.detectorProfiles] using hz

theorem source_batch_plain_unmarked (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ)
    (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)
    (henergy:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀Q:Ideal O,
      ∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
        ZeroAt Q (1/4) (9/4) radialSupportUpper 0 1 2 (D.t/4) U degree control A):
    ∃Jheight:ℕ,∀η:Character,∃C:ℝ,0< C ∧
    ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀d:ℝ,(1/200:ℝ)≤ d→∀(a tstar T heightAllowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a D.ε tstar T heightAllowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=> D.ell s/d)→
      ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
      ∀height:ℝ,0≤ height→∀j k:ℕ,j+k≤2→
      ∀σ∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let F:=B.fiber bin label left right hne;
      let value:=∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t‖^2;
      value≤ C*(1+height)^Jheight*(Z^d)^(max 1 (2*F.m)+D.t) ∧
      value≤ C*(1+height)^Jheight*max (Z^d) (((Z^d)^F.m)^2)*(Z^d)^D.t := by
  obtain ⟨degree,control,henergy⟩:=henergy
  obtain ⟨Jheight,Cp,hCp,hprofiles⟩:=paired_control control
  refine ⟨Jheight,?_⟩
  intro η
  let :Fintype (Sum Bool (RayQuotient.Characters S.modulus ⊤)):=Fintype.ofFinite _
  let η₀:=fun label=> sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label
  let Q:=fun label=> internalQ (sourceFixedIdeal S) (η₀ label)
  choose A hA hzero using (fun label=> henergy (Q label))
  let Amax:ℝ:=1+∑label,A label
  have hsum:0≤∑label,A label:=Finset.sum_nonneg (fun j _=>(hA j).le)
  have hAmax:0< Amax:=by dsimp [Amax];linarith
  have hA_bound (label):A label≤ Amax:=by
    have hh:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hA j).le) (Finset.mem_univ label)
    dsimp [Amax];linarith
  let C:=Amax*(1+diagonalControl radialMajorant)*Cp
  have hdiag:0≤ diagonalControl radialMajorant:=diagonalControl_nonneg _
  have hC:0< C:=mul_pos (mul_pos hAmax (by linarith)) hCp
  have hC_bound (label):A label*diagonalControl radialMajorant*Cp≤ C:=by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hA_bound label) (by linarith) hdiag hAmax.le) hCp.le
  have hscales:∀ᶠZ:ℝ in atTop,∀label,∀d:ℝ,(1/200:ℝ)≤ d→
      ZeroAt (Q label) (1/4) (9/4) radialSupportUpper 0 1 2 (stageError D)
        (Z^d) degree control (A label):=by
    apply Filter.eventually_all.mpr
    intro label
    obtain ⟨U₀,hU₀⟩:=eventually_atTop.mp (hzero label)
    filter_upwards [HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) U₀ (by norm_num)]
      with Z hz
    intro d hd
    exact hU₀ (Z^d) (hz d hd)
  refine ⟨C,hC,?_⟩
  filter_upwards [source_batch_plain_retained S η,source_label_fixed_allowance D S η,hscales]
    with Z hret hmod hscales
  refine ⟨hret.1,?_⟩
  intro rows hrows d hd a tstar T heightAllowance i B hB hdata hprofile hwidth
    bin label left right hne height hheight j k hjk σ hσ t ht F value
  have hU:1< Z^d:=source_base_gt_one D Z d hret.1 hd
  have hnorm:‖t‖≤ height:=by simpa only [Real.norm_eq_abs] using abs_le.mpr ht
  have hp:(detectorProfiles F.reverse j k σ t).control control ^2≤ Cp*(1+height)^Jheight:=by
    apply (hprofiles F.reverse j k hjk σ hσ t).trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl hnorm) Jheight) hCp.le
  have hcompare:value≤ CenteredMomentDetectorPlainExceptional.retainedSourceEnergy (initialKeep (η₀ label) (Q label))
      F (η₀ label) ∅ j k σ t radialMajorant:=by
    simpa only [Fiber.physicalProduct,Finset.prod_empty,mul_one,
      CenteredMomentDetectorPlainExceptional.retainedSourceEnergy,
      IVFullCenteredMomentDetectorPlainExceptional.retainedSourceEnergy,
      CenteredMomentDetectorEnergyInitialState.initialKeep,
      IVFullCenteredMomentDetectorEnergyInitialState.initialKeep] using
      hret.2 rows hrows d (by linarith) a D.ε tstar T heightAllowance i B hB hdata hprofile hwidth
        bin label left right hne ∅ j k σ t
  have hb:=retained_unmarked_bound D F (η₀ label) (Q label) hU (hmod.2 label d hd)
    degree control (A label) (hscales label d hd) j k σ t
  have hpow:(Z^d)^(max 1 (2*F.m)+delta D+stageError D)≤
      (Z^d)^(max 1 (2*F.m)+D.t):=
    Real.rpow_le_rpow_of_exponent_le hU.le (final_exponent_budget D _)
  have hfinal:value≤ C*(1+height)^Jheight*(Z^d)^(max 1 (2*F.m)+D.t):=by
    apply hcompare.trans (hb.trans ?_)
    calc
      _≤(A label*diagonalControl radialMajorant*(Cp*(1+height)^Jheight))*
          (Z^d)^(max 1 (2*F.m)+D.t):=by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hp (mul_nonneg (hA label).le hdiag)
        · exact hpow
        · exact Real.rpow_nonneg (zero_lt_one.trans hU).le _
        · exact mul_nonneg (mul_nonneg (hA label).le hdiag)
            (mul_nonneg hCp.le (by positivity))
      _=(A label*diagonalControl radialMajorant*Cp)*(1+height)^Jheight*
          (Z^d)^(max 1 (2*F.m)+D.t):=by ring
      _≤_:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hC_bound label) (by positivity)) (by positivity)
  refine ⟨hfinal,?_⟩
  simpa only [unmarked_power_eq _ _ _ hU.le,mul_assoc] using hfinal

end SevenEighths.IVFullProbeDetectorPlainUnmarkedField

end

end OAI

-- Adapted data-generic source wrapper from DetectorPlainUnmarkedRestrictedField.lean

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentDetectorPlainExceptional
open OAI.SevenEighths.CenteredMomentDetectorPlainFiberSource
open OAI.SevenEighths.CenteredMomentDetectorPlainMomentParameters
open OAI.SevenEighths.CenteredMomentDetectorPlainProfileControl
open OAI.SevenEighths.CenteredMomentDetectorPlainUnmarkedState
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open OAI.SevenEighths.ProbeDetectorPlainUnmarkedField
open OAI.SevenEighths.ProbeDetectorPlainUnmarkedRestrictedField
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.IVFullProbeDetectorPlainUnmarkedRestrictedField
open HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorDictionary IVFullCenteredMomentDetectorEnergyInitialState
open IVFullCenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainUnmarkedState
open IVFullCenteredMomentDetectorPlainMomentParameters CenteredMomentDetectorPlainProfileControl
open CenteredMomentEnergyState CenteredMomentEnergyBands IVFullCenteredMomentNaturalFixedRaySource
open QuadraticInitialBound
local notation "O" => HeckeFamily.O

open IVFullProbeDetectorPlainUnmarkedField
variable {Δ:ℝ}

theorem source_zero_from_gated (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ)
    (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)
    (henergy:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,
      Q≤ S.modulus→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤ Ideal.span {(72:O)}→
      ∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
        ZeroAt (internalQ Q η₀) (1/4) (9/4) IVFullProbeDetectorPlainUnmarkedField.radialSupportUpper 0 1 2 (D.t/4)
          U degree control A):
    ∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,
      ∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
        ZeroAt (internalQ (sourceFixedIdeal S) η₀) (1/4) (9/4) IVFullProbeDetectorPlainUnmarkedField.radialSupportUpper
          0 1 2 (D.t/4) U degree control A:=by
  obtain ⟨degree,control,henergy⟩:=henergy
  refine ⟨degree,control,?_⟩
  intro η₀
  exact henergy η₀ (sourceFixedIdeal S) (sourceFixedIdeal_le_modulus S)
    (source_fixed_gates S η₀).1
    (internalQ_ne_top _ (sourceFixedIdeal_ne_top S) η₀)
    (source_fixed_gates S η₀).2.2.2

theorem source_batch_plain_unmarked (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ)
    (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)
    (henergy:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,
      ∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
        ZeroAt (internalQ (sourceFixedIdeal S) η₀) (1/4) (9/4) IVFullProbeDetectorPlainUnmarkedField.radialSupportUpper 0 1 2 (D.t/4) U degree control A):
    ∃Jheight:ℕ,∀η:Character,∃C:ℝ,0< C ∧
    ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀d:ℝ,(1/200:ℝ)≤ d→∀(a tstar T heightAllowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a D.ε tstar T heightAllowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=> D.ell s/d)→
      ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
      ∀height:ℝ,0≤ height→∀j k:ℕ,j+k≤2→
      ∀σ∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let F:=B.fiber bin label left right hne;
      let value:=∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t‖^2;
      value≤ C*(1+height)^Jheight*(Z^d)^(max 1 (2*F.m)+D.t) ∧
      value≤ C*(1+height)^Jheight*max (Z^d) (((Z^d)^F.m)^2)*(Z^d)^D.t := by
  obtain ⟨degree,control,henergy⟩:=henergy
  obtain ⟨Jheight,Cp,hCp,hprofiles⟩:=paired_control control
  refine ⟨Jheight,?_⟩
  intro η
  let :Fintype (Sum Bool (RayQuotient.Characters S.modulus ⊤)):=Fintype.ofFinite _
  let η₀:=fun label=> sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label
  let Q:=fun label=> internalQ (sourceFixedIdeal S) (η₀ label)
  choose A hA hzero using (fun label=> henergy (η₀ label))
  let Amax:ℝ:=1+∑label,A label
  have hsum:0≤∑label,A label:=Finset.sum_nonneg (fun j _=>(hA j).le)
  have hAmax:0< Amax:=by dsimp [Amax];linarith
  have hA_bound (label):A label≤ Amax:=by
    have hh:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hA j).le) (Finset.mem_univ label)
    dsimp [Amax];linarith
  let C:=Amax*(1+diagonalControl radialMajorant)*Cp
  have hdiag:0≤ diagonalControl radialMajorant:=diagonalControl_nonneg _
  have hC:0< C:=mul_pos (mul_pos hAmax (by linarith)) hCp
  have hC_bound (label):A label*diagonalControl radialMajorant*Cp≤ C:=by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hA_bound label) (by linarith) hdiag hAmax.le) hCp.le
  have hscales:∀ᶠZ:ℝ in atTop,∀label,∀d:ℝ,(1/200:ℝ)≤ d→
      ZeroAt (Q label) (1/4) (9/4) IVFullProbeDetectorPlainUnmarkedField.radialSupportUpper 0 1 2 (stageError D)
        (Z^d) degree control (A label):=by
    apply Filter.eventually_all.mpr
    intro label
    obtain ⟨U₀,hU₀⟩:=eventually_atTop.mp (hzero label)
    filter_upwards [HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) U₀ (by norm_num)]
      with Z hz
    intro d hd
    exact hU₀ (Z^d) (hz d hd)
  refine ⟨C,hC,?_⟩
  filter_upwards [source_batch_plain_retained S η,source_label_fixed_allowance D S η,hscales]
    with Z hret hmod hscales
  refine ⟨hret.1,?_⟩
  intro rows hrows d hd a tstar T heightAllowance i B hB hdata hprofile hwidth
    bin label left right hne height hheight j k hjk σ hσ t ht F value
  have hU:1< Z^d:=source_base_gt_one D Z d hret.1 hd
  have hnorm:‖t‖≤ height:=by simpa only [Real.norm_eq_abs] using abs_le.mpr ht
  have hp:(detectorProfiles F.reverse j k σ t).control control ^2≤ Cp*(1+height)^Jheight:=by
    apply (hprofiles F.reverse j k hjk σ hσ t).trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl hnorm) Jheight) hCp.le
  have hcompare:value≤ CenteredMomentDetectorPlainExceptional.retainedSourceEnergy (initialKeep (η₀ label) (Q label))
      F (η₀ label) ∅ j k σ t radialMajorant:=by
    simpa only [Fiber.physicalProduct,Finset.prod_empty,mul_one,
      CenteredMomentDetectorPlainExceptional.retainedSourceEnergy,
      IVFullCenteredMomentDetectorPlainExceptional.retainedSourceEnergy,
      CenteredMomentDetectorEnergyInitialState.initialKeep,
      IVFullCenteredMomentDetectorEnergyInitialState.initialKeep] using
      hret.2 rows hrows d (by linarith) a D.ε tstar T heightAllowance i B hB hdata hprofile hwidth
        bin label left right hne ∅ j k σ t
  have hb:=retained_unmarked_bound D F (η₀ label) (Q label) hU (hmod.2 label d hd)
    degree control (A label) (hscales label d hd) j k σ t
  have hpow:(Z^d)^(max 1 (2*F.m)+delta D+stageError D)≤
      (Z^d)^(max 1 (2*F.m)+D.t):=
    Real.rpow_le_rpow_of_exponent_le hU.le (final_exponent_budget D _)
  have hfinal:value≤ C*(1+height)^Jheight*(Z^d)^(max 1 (2*F.m)+D.t):=by
    apply hcompare.trans (hb.trans ?_)
    calc
      _≤(A label*diagonalControl radialMajorant*(Cp*(1+height)^Jheight))*
          (Z^d)^(max 1 (2*F.m)+D.t):=by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hp (mul_nonneg (hA label).le hdiag)
        · exact hpow
        · exact Real.rpow_nonneg (zero_lt_one.trans hU).le _
        · exact mul_nonneg (mul_nonneg (hA label).le hdiag)
            (mul_nonneg hCp.le (by positivity))
      _=(A label*diagonalControl radialMajorant*Cp)*(1+height)^Jheight*
          (Z^d)^(max 1 (2*F.m)+D.t):=by ring
      _≤_:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hC_bound label) (by positivity)) (by positivity)
  refine ⟨hfinal,?_⟩
  simpa only [IVFullProbeDetectorPlainUnmarkedField.unmarked_power_eq _ _ _ hU.le,mul_assoc] using hfinal

end SevenEighths.IVFullProbeDetectorPlainUnmarkedRestrictedField

end

end OAI

set_option linter.unusedVariables false
namespace OAI

noncomputable section
open OAI.SevenEighths
open RHZeroFreeExtension.AnalyticHigh.IV
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter

namespace SevenEighths.IVFullProbeFinalAssemblyCertifiedBands
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open ProbeFinalAssembly ProbeHighRowFamily Parameters
open CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyWidthSchedule IVFullCenteredMomentDetectorPlainMomentParameters
open CenteredMomentNaturalFixedRaySource
open IVFullCenteredMomentDetectorEnergyInitialState IVFullCenteredMomentNaturalFixedRaySource
open IVFullProbeDetectorPlainMarkedFineField IVFullProbeDetectorPlainUnmarkedField
local notation "O"=> HeckeFamily.O

def detectorMesh (_Δ t:ℝ):ℝ:=fineMesh 2 0 1 (RHIVProbe.fullMomentKappa) (t/4)

lemma detectorMesh_pos {Δ t:ℝ}(_hΔ:0<Δ)(ht:0< t):0< detectorMesh Δ t:=by
  exact (bounds 2 (finalSourceCap 2 0 1 (t/4)) (RHIVProbe.fullMomentKappa) (t/4)
    (by norm_num) (sourceCap_nonneg 2 0 1 (by norm_num) (by norm_num) _)
    (by linarith [RHIVProbe.full_moment_range.1]) (by positivity)).2.2.2.2.1

theorem plain_inputs {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}(F:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)
    (hcert:∀bΦ:ℝ,0< bΦ→CertifiedBand (α:=Fin D.N) F.modulus ⊤ le_top
      (fun x=> conj (F.W x)) 2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2
      (kappaPlain D) (stageError D) (count 2 (stageError D))):
    PositiveFineSourceInput F (detectorMesh Δ D.t) ∧
    (∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) radialSupportUpper
        0 1 2 (D.t/4) U degree control A):=by
  have hp:=fixed_parameters D
  have ht (bΦ:ℝ)(hbΦ:0< bΦ):=
    certified_terminal F.modulus ⊤ le_top (fun x=> conj (F.W x))
      2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2 (kappaPlain D) (stageError D)
      (by norm_num) (by norm_num) hp.2.2.2.2.2.le hp.2.2.1 (hcert bΦ hbΦ)
  have hactual (bΦ:ℝ)(hbΦ:0< bΦ):
      ∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,
      ∃Czero Cpositive:ℝ,0< Czero ∧ 0< Cpositive ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) bΦ 0 1 2
        (stageError D) U degree control Czero ∧
      PositiveAt (α:=Fin D.N) F.modulus ⊤ le_top (fun x=> conj (F.W x))
        2 (1/4) (9/4) bΦ 0 1 (detectorMesh Δ D.t) (33/50) (33/50) 2
        (stageError D) (kappaPlain D) U η₀ (sourceFixedIdeal F) degree control Cpositive:=by
    obtain ⟨degree,control,hbound⟩:=ht bΦ hbΦ
    refine ⟨degree,control,?_⟩
    intro η₀
    obtain ⟨Cz,Cp,hCz,hCp,hbound⟩:=hbound η₀ (sourceFixedIdeal F)
      (sourceFixedIdeal_le_modulus F) (source_fixed_gates F η₀).1
      (internalQ_ne_top _ (sourceFixedIdeal_ne_top F) η₀) (source_fixed_gates F η₀).2.2.2
    exact ⟨Cz,Cp,hCz,hCp,hbound.mono (fun U h=>⟨h.2.1,h.2.2⟩)⟩
  constructor
  · intro bΦ hbΦ
    obtain ⟨degree,control,h⟩:=hactual bΦ hbΦ
    refine ⟨degree,control,?_⟩
    intro η₀
    obtain ⟨Cz,Cp,hCz,hCp,h⟩:=h η₀
    exact ⟨Cp,hCp,h.mono (fun U h=> h.2)⟩
  · obtain ⟨degree,control,h⟩:=hactual radialSupportUpper radialSupportUpper_spec.1
    refine ⟨degree,control,?_⟩
    intro η₀
    obtain ⟨Cz,Cp,hCz,hCp,h⟩:=h η₀
    exact ⟨Cz,hCz,h.mono (fun U h=> h.1)⟩


end SevenEighths.IVFullProbeFinalAssemblyCertifiedBands
end
end OAI

#print axioms OAI.SevenEighths.IVFullProbeDetectorPlainMarkedFineField.source_batch_plain_marked_fine

#print axioms OAI.SevenEighths.IVFullProbeFinalAssemblyCertifiedBands.plain_inputs


namespace RHZeroFreeExtension.AnalyticHigh.IV
open scoped Classical BigOperators ContDiff ComplexConjugate
open OAI OAI.SevenEighths
open CenteredMomentEnergyCertifiedExistenceIV CenteredMomentEnergyWidthSchedule
open CenteredMomentEnergyCappedWidthInduction

theorem full_kappa_terminal_certificate {gap : ℝ} (D : HighData gap)
    (F : SourceData D) (hOld : HeckeZeroSupremum.beta ≤ (1+RHIVProbe.fullMomentKappa)/2)
    (hBeta : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) (bPhi : ℝ) (hbPhi : 0 < bPhi) :
    CertifiedBand (α := Fin D.N) F.modulus ⊤ le_top (fun x => conj (F.W x))
      2 (1/4) (9/4) bPhi 0 1 (33/50) (33/50) 2 RHIVProbe.fullMomentKappa (D.t/4)
      (count 2 (D.t/4)) := by
  apply terminal_certificate (α := Fin D.N) F.modulus ⊤ le_top
    (fun x => conj (F.W x)) 1 2 (1/4) (9/4) bPhi 0 1 (33/50) (33/50) 2 RHIVProbe.fullMomentKappa (D.t/4)
  · norm_num
  · intro x hx
    have hh : x ∈ Function.support (F.W : ℝ → ℂ) := by
      change conj (F.W x) ≠ 0 at hx
      change F.W x ≠ 0
      intro hz
      exact hx (by rw [hz]; simp)
    exact F.complex_support hh
  · exact Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
