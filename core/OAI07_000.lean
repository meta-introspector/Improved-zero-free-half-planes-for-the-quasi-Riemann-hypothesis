import core.OAI06
-- import Mathlib.Algebra.BigOperators.Group.Finset.Basic
-- import Mathlib.Analysis.Complex.PhragmenLindelof
-- import Mathlib.Analysis.Complex.RemovableSingularity
-- import Mathlib.Analysis.InnerProductSpace.Calculus
-- import Mathlib.Analysis.MellinInversion
-- import Mathlib.Analysis.Normed.Group.FunctionSeries
-- import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
-- import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
-- import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- import Mathlib.MeasureTheory.Constructions.Polish.Basic
-- import Mathlib.MeasureTheory.Function.LocallyIntegrable
-- import Mathlib.RingTheory.Radical.Basic

/-! Pinned OAI dependency closure, consolidated without changing public namespaces.
Original module boundaries and hashes are preserved below. -/

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedCancellation
Source SHA256: ca7305c7bcbf881ec53c7d49afb8992d30fdbc9bde2156ba24244ca7b34925ba
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1935


namespace OAI

noncomputable section
namespace SevenEighths.ProbeLocal
theorem compensated_phase_error_bound (V W D P B q vInv : ℂ) (T : ℝ)
    (_hT : 0 ≤ T) (hV : ‖V‖ ≤ 1 / 2) (hW : ‖W‖ ≤ 1)
    (hD : ‖D‖ ≤ 1 / 2) (hq : ‖q‖ ≤ 1)
    (hVT : ‖V‖ ≤ T) (hDT : ‖D‖ ≤ T)
    (hE : ‖P + D‖ ≤ 28 * T) (hBE : ‖B‖ * ‖P + D‖ ≤ 28 * T)
    (hv : ‖vInv‖≤1) (hBD : B * D = vInv) (hWq : vInv*W = q) :
    ‖compensatedReplacement V W D P B q + continuedCorrection V W D P*vInv‖ ≤ 720 * T := by
  have h1V : ‖1 - V‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) V
    simp only [norm_one] at this
    linarith
  have h1W : ‖1 - W‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) W
    simp only [norm_one] at this
    linarith
  have h1q : ‖vInv - q‖ ≤ 2 := by
    have := norm_sub_le vInv q
    linarith
  have hiV := inv_one_sub_norm_le_two V hV
  have hiD := inv_one_sub_norm_le_two D hD
  have hfac : ‖(1 - V) * (1 - W) / (1 - D)‖ ≤ 8 := by
    rw [div_eq_mul_inv, norm_mul, norm_mul]
    calc
      ‖1 - V‖ * ‖1 - W‖ * ‖(1 - D)⁻¹‖ ≤ (2 : ℝ) * 2 * 2 := by gcongr
      _ = 8 := by norm_num
  have hleft : ‖(vInv - q) * (V / (1 - V) - D)‖ ≤ 6 * T := by
    calc
      _ = ‖vInv - q‖ * ‖V / (1 - V) - D‖ := norm_mul _ _
      _ ≤ 2 * (‖V‖ * 2 + ‖D‖) := by
        gcongr
        calc
          _ ≤ ‖V / (1 - V)‖ + ‖D‖ := norm_sub_le _ _
          _ ≤ _ := by rw [div_eq_mul_inv, norm_mul]; gcongr
      _ ≤ 6 * T := by linarith
  have hright : ‖(B + vInv - q) * (P + D)‖ ≤ 84 * T := by
    have hc : ‖B + vInv - q‖ ≤ ‖B‖ + 2 := by
      calc
        _ = ‖B + (vInv - q)‖ := by congr 1; ring
        _ ≤ ‖B‖ + ‖vInv - q‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    calc
      _ = ‖B + vInv - q‖ * ‖P + D‖ := norm_mul _ _
      _ ≤ (‖B‖ + 2) * ‖P + D‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ ≤ 84 * T := by nlinarith
  have hid := continued_normalized_cancellation V W D P B q vInv
    (one_sub_ne_zero_of_norm_le_half V hV) (one_sub_ne_zero_of_norm_le_half D hD)
    hBD hWq
  rw [hid, norm_mul]
  calc
    _ ≤ 8 * (‖(vInv - q) * (V / (1 - V) - D)‖ + ‖(B + vInv - q) * (P + D)‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ 720 * T := by linarith

end SevenEighths.ProbeLocal
end

end OAI
end OAIOriginalModule1935

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsCentralCancellation
Source SHA256: 7725f7dbef619a609bd867acc993b377b67b19d9e35ef312dcadbf5c97e21ee8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1936


namespace OAI

noncomputable section
namespace SevenEighths.ProbeLocal

theorem central_phase_error_bound (V W D P B q vInv : ℂ) (A T : ℝ)
    (hA : 1≤A) (hV : ‖V‖≤1/2) (hD : ‖D‖≤1/2)
    (hW : ‖W‖≤A) (hq : ‖q‖≤A) (hv : ‖vInv‖≤1)
    (hVT : A^2*‖V‖≤T) (hDT : A^2*‖D‖≤T)
    (hET : A^2*‖P+D‖≤28*T) (hBET : A*‖B‖*‖P+D‖≤28*T)
    (hBD : B*D=vInv) (hWq : vInv*W=q) :
    ‖compensatedReplacement V W D P B q+continuedCorrection V W D P*vInv‖≤720*T := by
  have hA0 : 0≤A := by linarith
  have hT : 0≤T := (mul_nonneg (sq_nonneg A) (norm_nonneg V)).trans hVT
  have h1V : ‖1-V‖≤2 := by
    have hh := norm_sub_le (1:ℂ) V
    rw [norm_one] at hh
    linarith
  have h1W : ‖1-W‖≤2*A := by
    have hh := norm_sub_le (1:ℂ) W
    rw [norm_one] at hh
    linarith
  have hdiff : ‖vInv-q‖≤2*A := (norm_sub_le vInv q).trans (by linarith)
  have hfac : ‖(1-V)*(1-W)/(1-D)‖≤8*A := by
    rw [div_eq_mul_inv,norm_mul,norm_mul]
    have hi := inv_one_sub_norm_le_two D hD
    calc
      _ ≤ 2*(2*A)*2 := by gcongr
      _ = _ := by ring
  have hleft : ‖(vInv-q)*(V/(1-V)-D)‖≤2*A*(2*‖V‖+‖D‖) := by
    rw [norm_mul]
    apply mul_le_mul hdiff _ (norm_nonneg _) (by positivity)
    calc
      _ ≤ ‖V/(1-V)‖+‖D‖ := norm_sub_le _ _
      _ ≤ _ := by
        rw [div_eq_mul_inv,norm_mul]
        have hi := inv_one_sub_norm_le_two V hV
        nlinarith [mul_le_mul_of_nonneg_left hi (norm_nonneg V)]
  have hright : ‖(B+vInv-q)*(P+D)‖≤(‖B‖+2*A)*‖P+D‖ := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ = ‖B+(vInv-q)‖ := by congr 1;ring
      _ ≤ ‖B‖+‖vInv-q‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  rw [continued_normalized_cancellation V W D P B q vInv
    (one_sub_ne_zero_of_norm_le_half V hV) (one_sub_ne_zero_of_norm_le_half D hD) hBD hWq,norm_mul]
  calc
    _ ≤ (8*A)*(2*A*(2*‖V‖+‖D‖)+(‖B‖+2*A)*‖P+D‖) := by
      apply mul_le_mul hfac _ (norm_nonneg _) (by positivity)
      exact (norm_add_le _ _).trans (add_le_add hleft hright)
    _ = 32*(A^2*‖V‖)+16*(A^2*‖D‖)+8*(A*‖B‖*‖P+D‖)+16*(A^2*‖P+D‖) := by ring
    _ ≤ 720*T := by linarith

end SevenEighths.ProbeLocal
end

end OAI
end OAIOriginalModule1936

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedError
Source SHA256: 93d1ec301f9630f44e8599cf3b90d6187d7cab55b8aa0734a0b6ef8e0be8a483
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1937



namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ProbeLocal

def unramifiedMarked (Q : ℝ) (A eta v x w z : ℂ) : ℂ :=
  markedFactor (coordR Q A x z) (coordV Q z) (Q:ℂ)⁻¹ (coordK Q eta x w)
    (-coordD Q eta v x+coordW Q v w*coordR Q A x z) 1

lemma unramifiedMarked_selected_error (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖unramifiedMarked Q A eta v x w z+coordD Q eta v x‖≤28 ∧
    ‖star eta*(Q:ℂ)^x‖*‖unramifiedMarked Q A eta v x w z+coordD Q eta v x‖≤28 := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  let R := coordR Q A x z
  let V := coordV Q z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  let B := star eta*(Q:ℂ)^x
  have hR : ‖R‖≤Q^(4-6*x.re-6*z.re) := coordR_norm_le Q hQ0 A x z hA
  have hV : ‖V‖=Q^(-6*z.re) := coordV_norm Q hQ0 z
  have hD : ‖D‖≤Q^(-x.re) := coordD_norm_le Q hQ0 eta v x heta hv
  have hW : ‖W‖≤1 := (coordW_norm_le Q hQ0 v w hv).trans
    (Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith))
  have hK : ‖K‖≤Q^(1-x.re-w.re) := coordK_norm_le Q hQ1 eta x w heta
  have hB : ‖B‖≤Q^x.re := by
    dsimp only [B]
    rw [norm_mul,norm_star,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  have hRh : ‖R‖≤1/2 := hR.trans (rpow_le_half Q _ hQ (by linarith))
  have hVh : ‖V‖≤1/2 := by rw [hV];exact rpow_le_half Q _ hQ (by linarith)
  have hDh : ‖D‖≤1/2 := hD.trans (rpow_le_half Q _ hQ (by linarith))
  have hqi : ‖(Q:ℂ)⁻¹‖≤1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ0,←one_div]
    exact (div_le_one hQ0).mpr hQ1
  have hprod (a b aa bb : ℝ) (ha : 0≤a) (hb : 0≤b)
      (haa : a≤Q^aa) (hbb : b≤Q^bb) (he : aa+bb≤0) : a*b≤1 := by
    calc
      a*b≤Q^aa*Q^bb := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _=Q^(aa+bb) := (Real.rpow_add hQ0 _ _).symm
      _≤1 := Real.rpow_le_one_of_one_le_of_nonpos hQ1 he
  have hKV : ‖K‖*‖V‖≤1 := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV.le (by linarith)
  have hBR : ‖B‖*‖R‖≤1 := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hB hR (by linarith)
  have hKV' : ‖K‖*‖V‖≤Q^(1-x.re-w.re-6*z.re) := by
    calc
      _≤Q^(1-x.re-w.re)*Q^(-6*z.re) := mul_le_mul hK hV.le (norm_nonneg _) (Real.rpow_nonneg hQ0.le _)
      _=_ := by rw [←Real.rpow_add hQ0];congr 1;ring
  have hBKV : ‖B‖*(‖K‖*‖V‖)≤1 := hprod _ _ _ _ (norm_nonneg _) (by positivity) hB hKV' (by linarith)
  have hE := unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
  change ‖unramifiedMarked Q A eta v x w z+D‖≤_ at hE
  have hE' : ‖unramifiedMarked Q A eta v x w z+D‖≤24*‖R‖+4*(‖K‖*‖V‖) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg R)]
  constructor
  · change ‖unramifiedMarked Q A eta v x w z+D‖≤28
    linarith
  · have hh := mul_le_mul_of_nonneg_left hE' (norm_nonneg B)
    change ‖B‖*‖unramifiedMarked Q A eta v x w z+D‖≤28
    nlinarith

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1937

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedUnramified
Source SHA256: 99172118c423a4e2975b949ddc53b238f8b59645587f7839b5b7e853fac2a087
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1938


namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ProbeLocal

def unramifiedSelected (Q : ℝ) (A eta v x w z : ℂ) : ℂ :=
  compensatedReplacement (coordV Q z) (coordW Q v w) (coordD Q eta v x)
    (unramifiedMarked Q A eta v x w z) (star eta*(Q:ℂ)^x) ((Q:ℂ)^(-w))

lemma selected_phase_identities (Q : ℝ) (eta v x w : ℂ)
    (hQ : 0<Q) (heta : ‖eta‖=1) (hv : ‖v‖=1) :
    (star eta*(Q:ℂ)^x)*coordD Q eta v x=star v ∧
      star v*coordW Q v w=(Q:ℂ)^(-w) := by
  have hQ0 : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  constructor
  · unfold coordD
    calc
      _=(star eta*eta)*((Q:ℂ)^x*(Q:ℂ)^(-x))*star v := by ring
      _=star v := by rw [PrincipalSlotEstimate.unit_phase_inverse eta heta,←Complex.cpow_add _ _ hQ0];simp
  · unfold coordW
    rw [←mul_assoc,PrincipalSlotEstimate.unit_phase_inverse v hv,one_mul]

lemma unramifiedSelected_error_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (heta : ‖eta‖=1) (hv : ‖v‖=1)
    (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖unramifiedSelected Q A eta v x w z+unramifiedClosed Q A eta v x w z*star v‖≤720 := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  have hV : ‖coordV Q z‖≤1/2 := by
    rw [coordV_norm Q hQ0]
    exact rpow_le_half Q _ hQ (by linarith)
  have hD : ‖coordD Q eta v x‖≤1/2 :=
    (coordD_norm_le Q hQ0 eta v x heta.le hv.le).trans (rpow_le_half Q _ hQ (by linarith))
  have hW : ‖coordW Q v w‖≤1 :=
    (coordW_norm_le Q hQ0 v w hv.le).trans (Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith))
  have hq : ‖(Q:ℂ)^(-w)‖≤1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith)
  have he := unramifiedMarked_selected_error Q A eta v x w z hQ hA heta.le hv.le hx hw hz
  have hi := selected_phase_identities Q eta v x w hQ0 heta hv
  have hh := compensated_phase_error_bound (coordV Q z) (coordW Q v w) (coordD Q eta v x)
    (unramifiedMarked Q A eta v x w z) (star eta*(Q:ℂ)^x) ((Q:ℂ)^(-w)) (star v) 1
    (by norm_num) hV hW hD hq (by linarith) (by linarith)
    (by simpa using he.1) (by simpa using he.2) (by rw [norm_star,hv]) hi.1 hi.2
  simpa only [mul_one,unramifiedSelected,unramifiedClosed,unramifiedMarked] using hh

lemma unramifiedSelected_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (heta : ‖eta‖=1) (hv : ‖v‖=1)
    (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖unramifiedSelected Q A eta v x w z‖≤961 := by
  have hd := unramifiedClosed_first_region_bound Q A eta v x w z (1/4) hQ hA heta.le hv.le
    (by norm_num) (by linarith) hz (by linarith) (by linarith)
  have hpow : Q^(-1-min (1/4:ℝ) (1/50))≤1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hH : ‖unramifiedClosed Q A eta v x w z‖≤241 := by
    have hh := norm_add_le (unramifiedClosed Q A eta v x w z-1) (1:ℂ)
    rw [sub_add_cancel,norm_one] at hh
    nlinarith
  have he := unramifiedSelected_error_bound Q A eta v x w z hQ hA heta hv hx hw hz
  have hh := norm_sub_le
    (unramifiedSelected Q A eta v x w z+unramifiedClosed Q A eta v x w z*star v)
    (unramifiedClosed Q A eta v x w z*star v)
  rw [add_sub_cancel_right,norm_mul,norm_star,hv,mul_one] at hh
  linarith

lemma unramifiedSelected_zero (Q : ℝ) (v x w z : ℂ) :
    unramifiedSelected Q 0 0 v x w z= -(Q:ℂ)^(-w)*(1-coordV Q z*coordW Q v w) := by
  simp only [unramifiedSelected,unramifiedMarked,coordR,coordD,coordK,zero_mul,
    neg_zero,add_zero,markedFactor,zero_sub,sub_zero,div_one,mul_zero,
    star_zero,compensatedReplacement]
  ring

lemma unramifiedSelected_zero_bound (Q : ℝ) (v x w z : ℂ)
    (hQ : 4≤Q) (hv : ‖v‖≤1) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖unramifiedSelected Q 0 0 v x w z‖≤2 := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  have hV : ‖coordV Q z‖≤1 := by
    rw [coordV_norm Q hQ0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith)
  have hW : ‖coordW Q v w‖≤1 :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith))
  have hq : ‖(Q:ℂ)^(-w)‖≤1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith)
  rw [unramifiedSelected_zero,norm_mul,norm_neg]
  have ht := norm_sub_le (1:ℂ) (coordV Q z*coordW Q v w)
  rw [norm_one,norm_mul] at ht
  have hp : ‖coordV Q z‖*‖coordW Q v w‖≤1 := by nlinarith [norm_nonneg (coordV Q z)]
  nlinarith [norm_nonneg (1-coordV Q z*coordW Q v w)]

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1938

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsCentralError
Source SHA256: 3142ea14e8cc02190934f9dc25ad7bf09554aca99c845fb5f5dce9fcd53a66d1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1939



namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ProbeLocal

lemma central_unramified_error_weights (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 4≤Q) (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    let L := Q^(6*e)
    let E := unramifiedMarked Q A eta v x w z+coordD Q eta v x
    L^2*‖coordV Q z‖≤Q^(-(51/100:ℝ)) ∧
    L^2*‖coordD Q eta v x‖≤Q^(-(51/100:ℝ)) ∧
    L^2*‖E‖≤28*Q^(-(51/100:ℝ)) ∧
    L*‖star eta*(Q:ℂ)^x‖*‖E‖≤28*Q^(-(51/100:ℝ)) := by
  dsimp only
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  let R := coordR Q A x z
  let V := coordV Q z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  let B := star eta*(Q:ℂ)^x
  let L : ℝ := Q^(6*e)
  have hL : 1≤L := Real.one_le_rpow hQ1 (by positivity)
  have hL0 : 0≤L := by positivity
  have hR := coordR_norm_le Q hQ0 A x z hA
  have hV := coordV_norm Q hQ0 z
  have hD := coordD_norm_le Q hQ0 eta v x heta hv
  have hK := coordK_norm_le Q hQ1 eta x w heta
  have hW : ‖W‖≤L := (coordW_norm_le Q hQ0 v w hv).trans
    (Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith))
  have hB : ‖B‖≤Q^x.re := by
    dsimp only [B]
    rw [norm_mul,norm_star,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  have hRh : ‖R‖≤1/2 := hR.trans (rpow_le_half Q _ hQ (by rw [hx,hz];linarith))
  have hVh : ‖V‖≤1/2 := hV.le.trans (rpow_le_half Q _ hQ (by rw [hz];norm_num))
  have hDh : ‖D‖≤1/2 := hD.trans (rpow_le_half Q _ hQ (by rw [hx];linarith))
  have hqi : ‖(Q:ℂ)⁻¹‖≤1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ0,←one_div]
    exact (div_le_one hQ0).mpr hQ1
  have hE : ‖unramifiedMarked Q A eta v x w z+D‖≤24*L*‖R‖+4*‖K‖*‖V‖ := by
    have hh := unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    apply hh.trans
    nlinarith [mul_le_mul_of_nonneg_left (show 1+‖W‖≤2*L by linarith) (norm_nonneg R)]
  have weighted (k r : ℝ) (N : ℝ) (hN : N≤Q^r) (hexp : k+r≤-(51/100:ℝ)) :
      Q^k*N≤Q^(-(51/100:ℝ)) := by
    calc
      _ ≤ Q^k*Q^r := mul_le_mul_of_nonneg_left hN (Real.rpow_nonneg hQ0.le _)
      _ = Q^(k+r) := (Real.rpow_add hQ0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hQ1 hexp
  have hLR : L^3*‖R‖≤Q^(-(51/100:ℝ)) := by
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hR (by rw [hx,hz];linarith)
  have hLKV : L^2*(‖K‖*‖V‖)≤Q^(-(51/100:ℝ)) := by
    have hkv : ‖K‖*‖V‖≤Q^(1-x.re-w.re-6*z.re) := by
      calc
        _ ≤ Q^(1-x.re-w.re)*Q^(-6*z.re) := mul_le_mul hK hV.le (norm_nonneg _) (Real.rpow_nonneg hQ0.le _)
        _ = _ := by rw [←Real.rpow_add hQ0];congr 1;ring
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hkv (by rw [hx,hw,hz];linarith)
  have hLBR : L^2*(‖B‖*‖R‖)≤Q^(-(51/100:ℝ)) := by
    have hbr : ‖B‖*‖R‖≤Q^(4-5*x.re-6*z.re) := by
      calc
        _ ≤ Q^x.re*Q^(4-6*x.re-6*z.re) := mul_le_mul hB hR (norm_nonneg _) (Real.rpow_nonneg hQ0.le _)
        _ = _ := by rw [←Real.rpow_add hQ0];congr 1;ring
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hbr (by rw [hx,hz];linarith)
  have hLBKV : L*(‖B‖*‖K‖*‖V‖)≤Q^(-(51/100:ℝ)) := by
    have hbkv : ‖B‖*‖K‖*‖V‖≤Q^(1-w.re-6*z.re) := by
      calc
        _ ≤ Q^x.re*Q^(1-x.re-w.re)*Q^(-6*z.re) := by
          gcongr
          exact hV.le
        _ = _ := by rw [←Real.rpow_add hQ0,←Real.rpow_add hQ0];congr 1;ring
    exact weighted _ _ _ hbkv (by rw [hw,hz];linarith)
  refine ⟨?_,?_,?_,?_⟩
  · change L^2*‖V‖≤_
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hV.le (by rw [hz];linarith)
  · change L^2*‖D‖≤_
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hD (by rw [hx];linarith)
  · have hh := mul_le_mul_of_nonneg_left hE (sq_nonneg L)
    change L^2*‖unramifiedMarked Q A eta v x w z+D‖≤_
    nlinarith [hLR,hLKV]
  · have hh := mul_le_mul_of_nonneg_left hE (mul_nonneg hL0 (norm_nonneg B))
    change L*‖B‖*‖unramifiedMarked Q A eta v x w z+D‖≤_
    nlinarith [hLBR,hLBKV]

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1939

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsCentralSelected
Source SHA256: 5fefd31772b8d30c7e46f1cb4f1038bb2142f514390e5e8437189551bde642b4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1940


namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ProbeLocal

lemma unramifiedSelected_central_error (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 4≤Q) (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hA : ‖A‖≤1) (heta : ‖eta‖=1) (hv : ‖v‖=1)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    ‖unramifiedSelected Q A eta v x w z+unramifiedClosed Q A eta v x w z*star v‖≤
      720*Q^(-(51/100:ℝ)) := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  have hL : 1≤Q^(6*e) := Real.one_le_rpow hQ1 (by positivity)
  have hV : ‖coordV Q z‖≤1/2 := by
    rw [coordV_norm Q hQ0]
    exact rpow_le_half Q _ hQ (by rw [hz];norm_num)
  have hD : ‖coordD Q eta v x‖≤1/2 :=
    (coordD_norm_le Q hQ0 eta v x heta.le hv.le).trans
      (rpow_le_half Q _ hQ (by rw [hx];linarith))
  have hW : ‖coordW Q v w‖≤Q^(6*e) := (coordW_norm_le Q hQ0 v w hv.le).trans
    (Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith))
  have hq : ‖(Q:ℂ)^(-w)‖≤Q^(6*e) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith)
  obtain ⟨hVT,hDT,hET,hBET⟩ := central_unramified_error_weights Q a e A eta v x w z
    hQ ha ha1 he he1 hA heta.le hv.le hx hw hz
  have hi := selected_phase_identities Q eta v x w hQ0 heta hv
  have hh := central_phase_error_bound (coordV Q z) (coordW Q v w) (coordD Q eta v x)
    (unramifiedMarked Q A eta v x w z) (star eta*(Q:ℂ)^x) ((Q:ℂ)^(-w)) (star v)
    (Q^(6*e)) (Q^(-(51/100:ℝ))) hL hV hD hW hq (by rw [norm_star,hv])
    hVT hDT hET hBET hi.1 hi.2
  simpa only [unramifiedSelected,unramifiedClosed,unramifiedMarked] using hh

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1940

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsCentralQuotient
Source SHA256: 74e747c8a4410722b01e663dc4d9a31ca12447f522a6ff688051af6e8e05e3f5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1941


namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma unramifiedClosed_central_lower (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 480≤Q) (ha : (51/100:ℝ)≤a) (ha1 : a≤1)
    (he : 0<e) (he1 : e≤1/1000) (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    1/2≤‖unramifiedClosed Q A eta v x w z‖ := by
  have hQ0 : 0<Q := by linarith
  have hd := unramifiedClosed_first_region_bound Q A eta v x w z (10*e)
    (by linarith) hA heta hv (by positivity) (by rw [hx];linarith)
    (by rw [hz]) (by rw [hw];linarith) (by rw [hx,hw];linarith)
  have hp : Q^(-1-min (10*e) (1/50:ℝ))≤Q^(-1:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by
      have hm : 0≤min (10*e) (1/50:ℝ) := by positivity
      linarith)
  have hi : Q^(-1:ℝ)≤1/480 := by
    rw [Real.rpow_neg_one,←one_div]
    exact one_div_le_one_div_of_le (by norm_num) hQ
  have ht := norm_sub_le (1:ℂ) (unramifiedClosed Q A eta v x w z)
  have ht' := norm_add_le (1-unramifiedClosed Q A eta v x w z)
    (unramifiedClosed Q A eta v x w z)
  rw [sub_add_cancel,norm_one,norm_sub_rev] at ht'
  nlinarith

lemma unramifiedSelected_central_quotient (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 480≤Q) (ha : (51/100:ℝ)≤a) (ha1 : a≤1)
    (he : 0<e) (he1 : e≤1/1000) (hA : ‖A‖≤1) (heta : ‖eta‖=1) (hv : ‖v‖=1)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    ‖unramifiedSelected Q A eta v x w z/unramifiedClosed Q A eta v x w z+star v‖≤
      1440*Q^(-(51/100:ℝ)) := by
  have hh := unramifiedClosed_central_lower Q a e A eta v x w z hQ ha ha1 he he1 hA heta.le hv.le hx hw hz
  have hn : unramifiedClosed Q A eta v x w z≠0 := by
    intro hz;rw [hz,norm_zero] at hh;norm_num at hh
  have hp : 0<‖unramifiedClosed Q A eta v x w z‖ := by linarith
  have hb := unramifiedSelected_central_error Q a e A eta v x w z
    (by linarith) ha ha1 he he1 hA heta hv hx hw hz
  have hid : unramifiedSelected Q A eta v x w z/unramifiedClosed Q A eta v x w z+star v=
      (unramifiedSelected Q A eta v x w z+unramifiedClosed Q A eta v x w z*star v)/
      unramifiedClosed Q A eta v x w z := by field_simp
  rw [hid,norm_div]
  apply (div_le_iff₀ hp).mpr
  have ht : 0≤Q^(-(51/100:ℝ)) := Real.rpow_nonneg (by linarith) _
  nlinarith
end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1941

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedActual
Source SHA256: 4191225d6d759e0c253d8fbc609ba7f3b27979d9be9b47fb633373e4f77c4982
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1942



namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma elementCoeff_zero_or_norm_one (eta : HeckeFamily.Character) (p : O) :
    HeckeFamily.elementCoeff eta p=0 ∨ ‖HeckeFamily.elementCoeff eta p‖=1 := by
  by_cases h : HeckeFamily.elementCoeff eta p=0
  · exact Or.inl h
  · right
    let : Finite (O ⧸ eta.modulus) := Ring.HasFiniteQuotients.finiteQuotient eta.modulus_ne_bot
    let : Fintype (O ⧸ eta.modulus) := Fintype.ofFinite _
    have hu : IsUnit (Ideal.Quotient.mk eta.modulus p) := eta.residue.apply_ne_zero_iff.mp h
    obtain ⟨u,hu⟩ := hu
    change ‖eta.residue (Ideal.Quotient.mk eta.modulus p)‖=1
    rw [←hu]
    exact FiniteRayExpansion.norm_char_unit eta.residue u

def actualUnramifiedSelected (eta : HeckeFamily.Character) (p u : O)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p}) (x w z : ℂ) : ℂ :=
  unramifiedSelected (Ideal.absNorm (Ideal.span {p})) (actualAPhase eta p)
    (HeckeFamily.elementCoeff eta p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ u)) x w z

theorem actualUnramifiedSelected_bound (eta : HeckeFamily.Character) (p u : O)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hu : IsCoprime u p)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (x w z : ℂ)
    (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖actualUnramifiedSelected eta p u hg x w z‖≤961 := by
  have hv := Complex.norm_eq_one_of_pow_eq_one (ProbePhysical.actualSextic_unit_six p u hg hc hu) (by decide : (6:ℕ)≠0)
  unfold actualUnramifiedSelected
  rcases elementCoeff_zero_or_norm_one eta p with heta|heta
  · have hA : actualAPhase eta p=0 := by simp [actualAPhase,heta]
    rw [heta,hA]
    exact (unramifiedSelected_zero_bound _ _ x w z hQ hv.le hw hz).trans (by norm_num)
  · exact unramifiedSelected_bound _ _ _ _ x w z hQ (actualAPhase_norm_le_one eta p) heta hv hx hw hz

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1942

/-! Original module: OAI.NumberTheory.DirichletL.Detector.SelectedPrimeSums
Source SHA256: b9cdb1a0cd961906852b6bf2809c39bcccc566e0db35bdd9bcab4d0cfaae81bf
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1943



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeSelectedPrimeSums
local notation "O" => ActualEisensteinCubic.O

lemma finite_ideal_count (S : Finset (Ideal O)) (H : ℝ) (hH : 0≤H)
    (hS : ∀I∈S,I≠0) (hN : ∀I∈S,(Ideal.absNorm I:ℝ)≤H) :
    (S.card:ℝ)≤128*H := by
  by_cases hh : 1≤H
  · exact DescentFiberCost.finite_ideal_count_real S H hh hS hN
  · have he : S=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro I hI
      have hp : (1:ℝ)≤Ideal.absNorm I := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hI))
      have := hN I hI
      linarith
    simp only [he,Finset.card_empty,Nat.cast_zero]
    positivity

lemma ramified_card_bound (eps : ℝ) (heps : 0<eps) :
    ∃C : ℝ, 0<C ∧ ∀ (U : Ideal O), U≠0 → ∀S : Finset (Ideal O),
      ((S.filter (fun P=>P∣U)).card:ℝ)≤C*(Ideal.absNorm U:ℝ)^eps := by
  obtain ⟨C,hC,hb⟩ := IdealDivisorBound.ideal_divisor_small_power eps heps
  refine ⟨C,hC,?_⟩
  intro U hU S
  apply (show ((S.filter (fun P=>P∣U)).card:ℝ)≤(IdealMobiusDivisorSum.idealDivisors U).card from ?_).trans (hb U hU)
  exact_mod_cast Finset.card_le_card (show S.filter (fun P=>P∣U)⊆IdealMobiusDivisorSum.idealDivisors U from by
    intro P hP
    exact (IdealMobiusDivisorSum.mem_idealDivisors hU).mpr (Finset.mem_filter.mp hP).2)

def annularPower (a b r : ℝ) : ℝ := max (a^r) (b^r)

lemma annularPower_nonneg (a b r : ℝ) (ha : 0<a) : 0≤annularPower a b r :=
  (Real.rpow_nonneg ha.le _).trans (le_max_left _ _)

lemma annular_rpow (a b P q r : ℝ) (ha : 0<a) (hb : 0<b) (hP : 0<P)
    (hqa : a*P≤q) (hqb : q≤b*P) : q^r≤annularPower a b r*P^r := by
  have hq : 0<q := (mul_pos ha hP).trans_le hqa
  by_cases hr : 0≤r
  · calc
      q^r≤(b*P)^r := Real.rpow_le_rpow hq.le hqb hr
      _=b^r*P^r := Real.mul_rpow hb.le hP.le
      _≤annularPower a b r*P^r := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hP.le _)
  · calc
      q^r≤(a*P)^r := Real.rpow_le_rpow_of_nonpos (mul_pos ha hP) hqa (by linarith)
      _=a^r*P^r := Real.mul_rpow ha.le hP.le
      _≤annularPower a b r*P^r := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hP.le _)

theorem annular_slot_majorant (eps a b r d : ℝ) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hd : d≤1) :
    ∃C : ℝ, 0<C ∧ ∀(U : Ideal O), U≠0 → ∀P : ℝ, 1≤P →
    ∀S : Finset (Ideal O), (∀I∈S,I≠0) →
      (∀I∈S,a*P≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤b*P) →
      (∑I∈S,(Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1))
        ≤C*(Ideal.absNorm U:ℝ)^eps*P^r := by
  obtain ⟨D,hD,hdiv⟩ := ramified_card_bound eps heps
  let A := annularPower a b (r-1)
  let B := annularPower a b (r-1+d)
  have hA : 0≤A := annularPower_nonneg a b _ ha
  have hB : 0≤B := annularPower_nonneg a b _ ha
  refine ⟨1+128*b*A+D*B,by positivity,?_⟩
  intro U hU P hP S hS hSP
  have hP0 : 0<P := by linarith
  have hU1 : (1:ℝ)≤Ideal.absNorm U := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hU)
  have hUpow : 1≤(Ideal.absNorm U:ℝ)^eps := Real.one_le_rpow hU1 heps.le
  have hq (I : Ideal O) (hI : I∈S) : 0<(Ideal.absNorm I:ℝ) :=
    (mul_pos ha hP0).trans_le (hSP I hI).1
  have hc := finite_ideal_count S (b*P) (by positivity) hS (fun I hI=>(hSP I hI).2)
  have heP : P*P^(r-1)=P^r := by
    calc
      _=P^(1:ℝ)*P^(r-1) := by rw [Real.rpow_one]
      _=P^r := by rw [←Real.rpow_add hP0];congr 1;ring
  have hfirst : (∑I∈S,(Ideal.absNorm I:ℝ)^(r-1))≤128*b*A*P^r := by
    calc
      _≤∑_I∈S,A*P^(r-1) := Finset.sum_le_sum (fun I hI=>annular_rpow a b P _ _ ha hb hP0 (hSP I hI).1 (hSP I hI).2)
      _=(S.card:ℝ)*(A*P^(r-1)) := by simp
      _≤(128*(b*P))*(A*P^(r-1)) := mul_le_mul_of_nonneg_right hc (by positivity)
      _=128*b*A*(P*P^(r-1)) := by ring
      _=128*b*A*P^r := by rw [heP]
  have hsecond : (∑I∈S.filter (fun I=>I∣U),(Ideal.absNorm I:ℝ)^(r-1+d))≤
      D*B*(Ideal.absNorm U:ℝ)^eps*P^r := by
    have hpP : P^(r-1+d)≤P^r := Real.rpow_le_rpow_of_exponent_le hP (by linarith)
    calc
      _≤∑_I∈S.filter (fun I=>I∣U),B*P^(r-1+d) := by
        apply Finset.sum_le_sum
        intro I hI
        exact annular_rpow a b P _ _ ha hb hP0 (hSP I (Finset.mem_filter.mp hI).1).1 (hSP I (Finset.mem_filter.mp hI).1).2
      _=((S.filter (fun I=>I∣U)).card:ℝ)*(B*P^(r-1+d)) := by simp
      _≤(D*(Ideal.absNorm U:ℝ)^eps)*(B*P^r) := by
        gcongr
        exact hdiv U hU S
      _=D*B*(Ideal.absNorm U:ℝ)^eps*P^r := by ring
  have hsum : (∑I∈S,(Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1))≤
      (∑I∈S,(Ideal.absNorm I:ℝ)^(r-1))+
        ∑I∈S.filter (fun I=>I∣U),(Ideal.absNorm I:ℝ)^(r-1+d) := by
    rw [Finset.sum_filter,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro I hI
    split_ifs
    · rw [←Real.rpow_add (hq I hI)]
      exact le_add_of_nonneg_left (by positivity)
    · simp only [mul_one,add_zero,le_refl]
  apply hsum.trans
  have hup : 128*b*A*P^r≤128*b*A*(Ideal.absNorm U:ℝ)^eps*P^r := by
    nlinarith [mul_nonneg (show 0≤128*b*A*P^r by positivity) (show 0≤(Ideal.absNorm U:ℝ)^eps-1 by linarith)]
  nlinarith [mul_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ)≤Ideal.absNorm U) eps) (Real.rpow_nonneg hP0.le r)]

theorem weighted_slot_bound (eps a b r d B K : ℝ) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hd : d≤1) (hB : 0≤B) (hK : 0≤K) :
    ∃C : ℝ, 0<C ∧ ∀(U : Ideal O), U≠0 → ∀P : ℝ, 1≤P →
    ∀(S : Finset (Ideal O)), (∀I∈S,I≠0) → ∀(W : ℝ→ℂ),
      Function.support W⊆Set.Icc a b → (∀y,‖W y‖≤B) →
    ∀(G : Ideal O→ℂ), (∀I∈S,‖G I‖≤K*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1)) →
    ∀z : ℂ, z.re=r →
      (∑I∈S,‖W ((Ideal.absNorm I:ℝ)/P)*(Ideal.absNorm I:ℂ)^(z-1)*G I‖)
        ≤C*(Ideal.absNorm U:ℝ)^eps*P^r := by
  obtain ⟨C,hC,hmajor⟩ := annular_slot_majorant eps a b r d heps ha hb hd
  refine ⟨(B*K+1)*C,by positivity,?_⟩
  intro U hU P hP S hS W hWS hWB G hG z hz
  have hP0 : 0<P := by linarith
  let T := S.filter (fun I=>W ((Ideal.absNorm I:ℝ)/P)≠0)
  have hTS : T⊆S := Finset.filter_subset _ _
  have hbounds (I : Ideal O) (hI : I∈T) : a*P≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤b*P := by
    have ht := hWS (show (Ideal.absNorm I:ℝ)/P∈Function.support W from (Finset.mem_filter.mp hI).2)
    exact ⟨(le_div_iff₀ hP0).mp ht.1,(div_le_iff₀ hP0).mp ht.2⟩
  have he : (∑I∈S,‖W ((Ideal.absNorm I:ℝ)/P)*(Ideal.absNorm I:ℂ)^(z-1)*G I‖)=
      ∑I∈T,‖W ((Ideal.absNorm I:ℝ)/P)*(Ideal.absNorm I:ℂ)^(z-1)*G I‖ := by
    symm
    apply Finset.sum_subset hTS
    intro I hI hn
    have hw : W ((Ideal.absNorm I:ℝ)/P)=0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hI,hh⟩)
    simp only [hw,zero_mul,norm_zero]
  rw [he]
  have hpoint (I : Ideal O) (hI : I∈T) :
      ‖W ((Ideal.absNorm I:ℝ)/P)*(Ideal.absNorm I:ℂ)^(z-1)*G I‖≤
        (B*K)*((Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1)) := by
    have hN : (0:ℝ)<Ideal.absNorm I := (mul_pos ha hP0).trans_le (hbounds I hI).1
    have hc : ‖(Ideal.absNorm I:ℂ)^(z-1)‖=(Ideal.absNorm I:ℝ)^(r-1) := by
      simpa only [Complex.ofReal_natCast,Complex.sub_re,Complex.one_re,hz] using
        Complex.norm_cpow_eq_rpow_re_of_pos hN (z-1)
    simp only [norm_mul,hc]
    calc
      _≤B*(Ideal.absNorm I:ℝ)^(r-1)*(K*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1)) := by
        gcongr
        · exact hWB _
        · exact hG I (hTS hI)
      _=_ := by ring
  have hmain := hmajor U hU P hP T (fun I hI=>hS I (hTS hI)) hbounds
  calc
    _≤∑I∈T,(B*K)*((Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1)) :=
      Finset.sum_le_sum hpoint
    _=(B*K)*∑I∈T,(Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1) :=
      (Finset.mul_sum _ _ _).symm
    _≤(B*K)*(C*(Ideal.absNorm U:ℝ)^eps*P^r) := mul_le_mul_of_nonneg_left hmain (mul_nonneg hB hK)
    _≤((B*K+1)*C)*(Ideal.absNorm U:ℝ)^eps*P^r := by
      nlinarith [mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (by positivity : (0:ℝ)≤Ideal.absNorm U) eps))
        (Real.rpow_nonneg hP0.le r)]

end SevenEighths.ProbeSelectedPrimeSums
end

end OAI
end OAIOriginalModule1943

/-! Original module: OAI.NumberTheory.DirichletL.Detector.SelectedPrimeIndexed
Source SHA256: 9f5cea7597fcf4769345e3c27da5f39b34b0fc2ad9cb109674a0b28aab6f5295
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1944


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeSelectedPrimeSums
local notation "O" => ActualEisensteinCubic.O

lemma weighted_slot_bound_indexed (eps a b r d B K : ℝ) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hd : d≤1) (hB : 0≤B) (hK : 0≤K) :
    ∃C : ℝ, 0<C ∧ ∀{ι : Type*} (f : ι→Ideal O), Function.Injective f →
    ∀(U : Ideal O), U≠0 → ∀P : ℝ, 1≤P →
    ∀(S : Finset ι), (∀i∈S,f i≠0) → ∀(W : ℝ→ℂ),
      Function.support W⊆Set.Icc a b → (∀y,‖W y‖≤B) →
    ∀(G : ι→ℂ), (∀i∈S,‖G i‖≤K*(if f i∣U then (Ideal.absNorm (f i):ℝ)^d else 1)) →
    ∀z : ℂ, z.re=r →
      (∑i∈S,‖W ((Ideal.absNorm (f i):ℝ)/P)*(Ideal.absNorm (f i):ℂ)^(z-1)*G i‖)
        ≤C*(Ideal.absNorm U:ℝ)^eps*P^r := by
  obtain ⟨C,hC,hmain⟩ := weighted_slot_bound eps a b r d B K heps ha hb hd hB hK
  refine ⟨C,hC,?_⟩
  intro ι f hf U hU P hP S hS W hWS hWB G hG z hz
  let G' : Ideal O→ℂ := Function.extend f G (fun _=>0)
  have he (i : ι) : G' (f i)=G i := hf.extend_apply G (fun _=>0) i
  have hI (I : Ideal O) (hI : I∈S.image f) : I≠0 := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    exact hS i hi
  have hg (I : Ideal O) (hI : I∈S.image f) :
      ‖G' I‖≤K*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1) := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    rw [he]
    exact hG i hi
  have hh := hmain U hU P hP (S.image f) hI W hWS hWB G' hg z hz
  rw [Finset.sum_image hf.injOn] at hh
  simpa only [he] using hh

end SevenEighths.ProbeSelectedPrimeSums
end

end OAI
end OAIOriginalModule1944

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.Selected
Source SHA256: 221e743460b517bf875aec1988a8717ad933a3acea47c7a8769fb0fa5ea06f7c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1945





namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def continuedCompensatedLocal (η : Character) (u : FreeRow) (P : PrimeIdeal) (hs : Supported P.val)
    (x w z B q : ℂ) : ℂ :=
  ProbeLocal.compensatedReplacement (coordV P.val.absNorm z)
    (coordW P.val.absNorm (idealRowHom u.val P.val) w)
    (coordD P.val.absNorm (idealCoeff η P.val) (idealRowHom u.val P.val) x)
    (continuedMarkedLocal η u P hs x w z) B q

theorem localNormalization_coordinates (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) :
    localNormalization η u P x w z=
      (1-coordV P.val.absNorm z)*(1-coordW P.val.absNorm (idealRowHom u.val P.val) w)/
        (1-coordD P.val.absNorm (idealCoeff η P.val) (idealRowHom u.val P.val) x) := by
  unfold localNormalization coordV coordW coordD CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero,ite_false,Complex.ofReal_natCast]
  rw [show -(6*z)=(-6:ℂ)*z by ring]
  rfl

theorem row_phase_ramified (u : FreeRow) (P : PrimeIdeal) (hP : P.val∣Ideal.span {u.val}) :
    idealRowHom u.val P.val=0 := by
  have hu : u.val∈P.val := (Ideal.dvd_iff_le.mp hP) (Ideal.subset_span (by simp))
  exact idealRowHom_zero_of_dvd u.val P.property (dvd_refl _) hu

theorem continuedCompensatedLocal_ramified (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hP : P.val∣Ideal.span {u.val}) (x w z : ℂ) :
    let p := primaryGenerator P.val
    let hp := supported_primeGenerator_prime P hs
    letI : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    let hg := (supported_prime_data p hp ((span_primaryGenerator_of_supported P.val hs).symm ▸ hs)).1
    continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))=
      ramifiedSelected p hp hg (targetMonoid η p) (actualACube η p)
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
        x w z (multiplicity p u.val) := by
  dsimp only
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have he := ramifiedSelected_eq_replacement p hp hg.1 (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ (unitPart u p hp))) x w z (multiplicity p u.val)
  rw [he]
  unfold continuedCompensatedLocal
  rw [row_phase_ramified u P hP]
  simp only [coordW,coordD,zero_mul,mul_zero,star_zero]
  rw [←targetMonoid_primaryGenerator η P.val hs]
  unfold continuedMarkedLocal
  simp only [hspan]
  rfl

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1945

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.SelectedUnramified
Source SHA256: 77e1db98265a3aba0b6f6b46516b2cb14caf1255b56622197dbbef0ccb34300f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1946


namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem continuedMarkedLocal_unramified (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) (x w z : ℂ)
    (hV : ‖coordV P.val.absNorm z‖<1)
    (hR : ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1) :
    continuedMarkedLocal η u P hs x w z=
      unramifiedMarked P.val.absNorm (actualAPhase η (primaryGenerator P.val))
        (idealCoeff η P.val) (idealRowHom u.val P.val) x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hnot : ¬p∣u.val := by
    intro hd
    apply hn
    rw [Ideal.dvd_iff_le,←hspan,Ideal.span_singleton_le_span_singleton]
    exact hd
  have hj := multiplicity_eq_zero_of_not_dvd hnot
  have hb : unitPart u p hp=u.val := by
    have he := (unitPart_spec u p hp).1
    rw [hj,pow_zero,one_mul] at he
    exact he.symm
  have hu : IsCoprime u.val p := by rw [←hb]; exact unitPart_coprime u p hp
  have hρ := actualSextic_unit_six p u.val hg.1 hg.2 hu
  have hQ0 : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) :=
    HeckeDyadic.norm_pos ⟨Ideal.span {p},Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero⟩
  have hr := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ0 (actualACube η p) x z
  simp only [Complex.ofReal_natCast] at hr
  have hR' : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) (actualACube η p)
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1 := by
    rw [hr,actualACube_sq,hspan]
    exact hR
  have hv' : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1 := by rw [hspan];exact hV
  have hh := rowClosedMarked_unramified p hp hg.1 hg.2 (targetMonoid η p) (actualACube η p)
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
    (coordV (Ideal.absNorm (Ideal.span {p})) z) _ hρ hv' hR'
  have hk := coordK_eq_geometric (Ideal.absNorm (Ideal.span {p}):ℝ) hQ0 (targetMonoid η p) x w
  simp only [Complex.ofReal_natCast] at hk
  have hi : (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val))⁻¹=
      star (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val)) :=
    Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hρ (by decide))
  have heta : idealCoeff η P.val=targetMonoid η p :=
    (targetMonoid_primaryGenerator η P.val hs).symm
  have hphase : idealRowHom u.val P.val=
      actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val) := by
    conv_lhs => rw [←hspan]
    exact idealRowHom_prime u.val (Ideal.span {p}) hg.1
  simp only [hspan] at hh hr hk
  unfold continuedMarkedLocal
  change rowClosedMarked p hp hg.1 (targetMonoid η p) (actualACube η p)
    ((P.val.absNorm:ℂ)^(-x)) ((P.val.absNorm:ℂ)^(-w)) (coordV P.val.absNorm z)
    (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ (unitPart u p hp))) (multiplicity p u.val)=_
  rw [hj,hb,hh,hr,←hk,actualACube_sq,heta,hphase]
  simp only [unramifiedMarked,coordD,coordW,div_eq_mul_inv,hi,Complex.ofReal_natCast]
  congr 1; ring

theorem continuedCompensatedLocal_unramified (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) (x w z : ℂ)
    (hV : ‖coordV P.val.absNorm z‖<1)
    (hR : ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1) :
    continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))=
      unramifiedSelected P.val.absNorm (actualAPhase η (primaryGenerator P.val))
        (idealCoeff η P.val) (idealRowHom u.val P.val) x w z := by
  rw [continuedCompensatedLocal,continuedMarkedLocal_unramified η u P hs hn x w z hV hR]
  rfl

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1946

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.SelectedAgreement
Source SHA256: 4fa9badab209da472ae006324f82d9156baa6f2e826cdd6a72c0607aa0683785
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1947


namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def finiteLocalCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal) (hs : Supported P.val)
    (x w z : ℂ) : ℂ :=
  ProbeLocal.continuedCorrection (coordV P.val.absNorm z)
    (coordW P.val.absNorm (idealRowHom u.val P.val) w)
    (coordD P.val.absNorm (idealCoeff η P.val) (idealRowHom u.val P.val) x)
    (continuedMarkedLocal η u P hs x w z)

theorem continuedCompensatedLocal_eq_difference (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z B q : ℂ) :
    continuedCompensatedLocal η u P hs x w z B q=
      B*continuedMarkedLocal η u P hs x w z*localNormalization η u P x w z-
        q*finiteLocalCorrection η u P hs x w z := by
  rw [localNormalization_coordinates]
  unfold continuedCompensatedLocal finiteLocalCorrection ProbeLocal.compensatedReplacement ProbeLocal.continuedCorrection
  ring

theorem ramifiedCorrection_eq_marked (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    ramifiedCorrection η u P hs x w z=
      1+(1-coordV P.val.absNorm z)*continuedMarkedLocal η u P hs x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := (supported_prime_data p hp hsp).1
  have hnorm : Ideal.absNorm (Ideal.span {p})=P.val.absNorm := congrArg Ideal.absNorm hspan
  change ramifiedClosed p hp hg (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp))) x w z (multiplicity p u.val)=
    1+(1-coordV P.val.absNorm z)*rowClosedMarked p hp hg (targetMonoid η p) (actualACube η p)
      ((P.val.absNorm:ℂ)^(-x)) ((P.val.absNorm:ℂ)^(-w)) (coordV P.val.absNorm z)
      (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp))) (multiplicity p u.val)
  unfold ramifiedClosed
  rw [hnorm]

theorem finiteLocalCorrection_ramified (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hP : P.val∣Ideal.span {u.val}) (x w z : ℂ) :
    finiteLocalCorrection η u P hs x w z=ramifiedCorrection η u P hs x w z := by
  rw [ramifiedCorrection_eq_marked]
  unfold finiteLocalCorrection
  rw [row_phase_ramified u P hP]
  simp only [coordW,coordD,star_zero,mul_zero,zero_mul,ProbeLocal.continuedCorrection,
    sub_zero,mul_one,div_one]

theorem finiteLocalCorrection_unramified (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) (x w z : ℂ)
    (hV : ‖coordV P.val.absNorm z‖<1)
    (hR : ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1) :
    finiteLocalCorrection η u P hs x w z=idealUnramifiedCorrection η u P x w z := by
  rw [finiteLocalCorrection,continuedMarkedLocal_unramified η u P hs hn x w z hV hR]
  rfl

theorem initial_marked_geometry (η : Character) (P : PrimeIdeal) (x z : ℂ)
    (hx : 3/2<x.re) (hz : 1/6<z.re) :
    ‖coordV P.val.absNorm z‖<1 ∧
      ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1 := by
  have hQ : (1:ℝ)<P.val.absNorm := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (1:ℕ)<2) (SmoothMobiusCorrection.prime_norm_two_le P))
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  constructor
  · rw [coordV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  · apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η _)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)

theorem finiteLocalCorrection_eq_initial (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    finiteLocalCorrection η u P hs x w z=localCorrection η u P x w z := by
  by_cases hP : P.val∣Ideal.span {u.val}
  · rw [finiteLocalCorrection_ramified η u P hs hP]
    exact (localCorrection_eq_ramified η u P hs hP x w z hx hw hz).symm
  · have hg := initial_marked_geometry η P x z hx hz
    rw [finiteLocalCorrection_unramified η u P hs hP x w z hg.1 hg.2]
    exact (localCorrection_unramified_ideal η u P hs (supported_prime_coprime P hs u.val hP)
      x w z hx hw hz).symm

theorem continuedCompensatedLocal_eq_initial (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z B q : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    continuedCompensatedLocal η u P hs x w z B q=compensatedLocalCorrection η u P x w z B q := by
  rw [continuedCompensatedLocal_eq_difference,
    continuedMarkedLocal_eq_initial η u P hs x w z hx hw hz,
    finiteLocalCorrection_eq_initial η u P hs x w z hx hw hz]
  unfold compensatedLocalCorrection markedLocalCorrection
  ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1947

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.MarkedContinuation
Source SHA256: a548f9d9deac0f542435642545b0a3ceb91f90491602c986303ed1a322e193bd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1948



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def continuedCompensatedRow (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ) : ℂ :=
  (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
    HeckeOrigin.continued (rowCharacter S hS.prime u) w*
    HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
  (continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
    ∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z (B P.val) (q P.val))

theorem continuedCompensatedRow_eq_initial (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    continuedCompensatedRow S hS T hT η u x w z B q=spectralCompensatedRow S T η u.val x w z B q := by
  have hx0 : x≠0 := by intro h; simp only [h,Complex.zero_re] at hx;linarith
  have hx1 : x≠1 := by intro h; simp only [h,Complex.one_re] at hx;linarith
  have hw0 : w≠0 := by intro h; simp only [h,Complex.zero_re] at hw;linarith
  have hw1 : w≠1 := by intro h; simp only [h,Complex.one_re] at hw;linarith
  unfold continuedCompensatedRow
  rw [HeckeOrigin.continued_eq _ hw0 hw1,HeckeReciprocal.reciprocal_eq_inv _ hx0 hx1,
    continuedCorrection_eq_initial (markExclusions S T) (markedSourceExclusions S hS T) η u x w z hx hw hz]
  simp_rw [continuedCompensatedLocal_eq_initial η u _ _ x w z _ _ hx hw hz]
  rw [Finset.prod_attach T (fun P=>compensatedLocalCorrection η u P x w z (B P) (q P)),spectralCompensatedRow_original_L_factorization S hS.prime hS.bad T hT η u x w z B q hx hw hz,
    div_eq_mul_inv]

theorem continuedCompensatedRow_eq_indexed {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let hT : ∀Q∈Finset.univ.image P,Q.val∉S := by
      intro Q hQ
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
      exact hPS i
    continuedCompensatedRow S hS (Finset.univ.image P) hT η u x w z
      (fun Q=>star (idealCoeff η Q.val)*(Q.val.absNorm:ℂ)^x)
      (fun Q=>(Q.val.absNorm:ℂ)^(-w))=
      indexedCompensatedHigh η S (fun i=>CompletedGauss.primaryGenerator (P i).val) u.val x w z := by
  dsimp only
  rw [continuedCompensatedRow_eq_initial _ _ _ _ _ _ _ _ _ _ _ hx hw hz,
    indexedCompensatedHigh_eq_spectral η S P hP
      (fun i=>outside_prime_supported S hS.bad (P i) (hPS i)) u.val x w z]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1948

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.SelectedAnalytic
Source SHA256: 7c32cf66016a77406594548d5b96705cbb467eb3227dfa8a579261cda4439854
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1949


namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

theorem continuedMarkedLocal_eq_quotient (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) (hV : 1-coordV P.val.absNorm z≠0) :
    continuedMarkedLocal η u P hs x w z=(ramifiedCorrection η u P hs x w z-1)/(1-coordV P.val.absNorm z) := by
  rw [ramifiedCorrection_eq_marked]
  field_simp
  ring

theorem selected_V_ne_zero (P : PrimeIdeal) (hQ : (4:ℝ)≤P.val.absNorm) (z : ℂ)
    (hz : (4/25:ℝ)≤z.re) : 1-coordV P.val.absNorm z≠0 := by
  apply ProbeLocal.one_sub_ne_zero_of_norm_le_half
  rw [coordV_norm _ (by linarith : (0:ℝ)<P.val.absNorm)]
  apply rpow_le_half _ _ hQ
  linarith

theorem continuedMarkedLocal_analyticAt_x (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : (7/8:ℝ)<x.re) (hz : (4/25:ℝ)≤z.re) :
    AnalyticAt ℂ (fun x=>continuedMarkedLocal η u P hs x w z) x := by
  have he : (fun x=>continuedMarkedLocal η u P hs x w z)=
      (fun x=>(ramifiedCorrection η u P hs x w z-1)/(1-coordV P.val.absNorm z)) :=
    funext (fun x=>continuedMarkedLocal_eq_quotient η u P hs x w z (selected_V_ne_zero P hQ z hz))
  rw [he]
  exact (((ramifiedCorrection_analytic_x η u P hs hQ w z hz) x hx).sub analyticAt_const).div_const

theorem continuedMarkedLocal_differentiable_w (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x z : ℂ)
    (hx : (7/8:ℝ)≤x.re) (hz : (4/25:ℝ)≤z.re) :
    Differentiable ℂ (fun w=>continuedMarkedLocal η u P hs x w z) := by
  have he : (fun w=>continuedMarkedLocal η u P hs x w z)=
      (fun w=>(ramifiedCorrection η u P hs x w z-1)/(1-coordV P.val.absNorm z)) :=
    funext (fun w=>continuedMarkedLocal_eq_quotient η u P hs x w z (selected_V_ne_zero P hQ z hz))
  rw [he]
  exact ((ramifiedCorrection_analytic_w η u P hs hQ x z hx hz).sub_const 1).div_const _

theorem continuedMarkedLocal_analyticAt_z (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : (7/8:ℝ)≤x.re) (hz : (4/25:ℝ)<z.re) :
    AnalyticAt ℂ (fun z=>continuedMarkedLocal η u P hs x w z) z := by
  have hcv := (coordV_differentiable (P.val.absNorm:ℝ) (by linarith)).analyticAt z
  have ha : AnalyticAt ℂ (fun t=>(ramifiedCorrection η u P hs x w t-1)/(1-coordV P.val.absNorm t)) z :=
    (((ramifiedCorrection_analytic_z η u P hs hQ x w hx) z hz).sub analyticAt_const).div
    (analyticAt_const.sub hcv) (selected_V_ne_zero P hQ z hz.le)
  apply ha.congr
  filter_upwards [(Complex.isOpen_re_gt (4/25)).mem_nhds hz] with t ht
  exact (continuedMarkedLocal_eq_quotient η u P hs x w t (selected_V_ne_zero P hQ t ht.le)).symm

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1949

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.SelectedBounds
Source SHA256: e444da75b1ec0f7d91f5eb9ac4b8949221545c9fd09722de8ea5c72a4c6a233e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1950



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma continuedCompensatedLocal_ramified_bound (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hP : P.val∣Ideal.span {u.val}) (hQ : (4:ℝ)≤P.val.absNorm)
    (x w z : ℂ) (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))‖≤
        385*(P.val.absNorm:ℝ)^(max (1-w.re) 0) := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have ha : ‖actualACube η p‖≤1 := by
    have h := actualAPhase_norm_le_one η p
    rw [←actualACube_sq,norm_pow] at h
    nlinarith [norm_nonneg (actualACube η p)]
  rw [continuedCompensatedLocal_ramified η u P hs hP x w z]
  have hb := ramifiedSelected_bound p hp hg.1 hg.2 _ _ _ x w z
    (hspan.symm ▸ hQ) (targetMonoid_norm_le_one η p) ha
    (actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp)) hx hw hz
    (multiplicity p u.val) (multiplicity_lt_six u p hp)
  simpa only [hspan] using hb

lemma continuedCompensatedLocal_unramified_bound (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hP : ¬P.val∣Ideal.span {u.val}) (hQ : (4:ℝ)≤P.val.absNorm)
    (x w z : ℂ) (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))‖≤961 := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hnot : ¬p∣u.val := by
    intro hd
    apply hP
    rw [Ideal.dvd_iff_le,←hspan,Ideal.span_singleton_le_span_singleton]
    exact hd
  have hu : IsCoprime u.val p := (hp.irreducible.coprime_iff_not_dvd.mpr hnot).symm
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hV : ‖coordV P.val.absNorm z‖<1 := by
    exact (first_region_V_half _ hQ z hz).trans_lt (by norm_num)
  have hR : ‖coordR P.val.absNorm (actualAPhase η p) x z‖<1 := by
    apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η p)).trans_lt
    exact (rpow_le_half _ _ hQ (by linarith)).trans_lt (by norm_num)
  rw [continuedCompensatedLocal_unramified η u P hs hP x w z hV hR]
  have hb := actualUnramifiedSelected_bound η p u.val hg.1 hg.2 hu (hspan.symm ▸ hQ) x w z hx hw hz
  have he : idealCoeff η P.val=elementCoeff η p := by rw [←hspan,idealCoeff_span η hp.ne_zero]
  have hv : idealRowHom u.val P.val=actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val) := by
    rw [←hspan,idealRowHom_prime u.val (Ideal.span {p}) hg.1]
  simpa only [actualUnramifiedSelected,hspan,he,hv] using hb

lemma continuedCompensatedLocal_bound (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm)
    (x w z : ℂ) (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))‖≤
        961*(if P.val∣Ideal.span {u.val} then (P.val.absNorm:ℝ)^(max (1-w.re) 0) else 1) := by
  by_cases hp : P.val∣Ideal.span {u.val}
  · rw [ite_eq_left hp]
    apply (continuedCompensatedLocal_ramified_bound η u P hs hp hQ x w z hx hw hz).trans
    gcongr
    norm_num
  · simpa only [ite_eq_right hp,mul_one] using continuedCompensatedLocal_unramified_bound η u P hs hp hQ x w z hx hw hz

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule1950

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CentralRamified
Source SHA256: fc83e69dc7c0f72a966a9a83d3672879bc193f9b62d09609797fc6a3ac579eb4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1951



namespace OAI

noncomputable section
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge

theorem actual_central_ramified_normalized (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hP : P.val∣Ideal.span {u.val}) (hQ : (4:ℝ)≤P.val.absNorm)
    (alpha eps : ℝ) (x w z : ℂ)
    (hsmall : 198*(P.val.absNorm:ℝ)^(-10*eps)≤1/2)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50) :
    1/2≤‖ramifiedCorrection η u P hs x w z‖ ∧
    (P.val.absNorm:ℝ)^(-1:ℝ)*
      ‖continuedCompensatedLocal η u P hs x w z
        (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w)) /
        ramifiedCorrection η u P hs x w z‖≤
      800*(P.val.absNorm:ℝ)^(-(1/2:ℝ))+
        (if 2≤multiplicity (primaryGenerator P.val) u.val then 12*(P.val.absNorm:ℝ)^(-w.re) else 0) := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal HeckeFamily.O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have ha : ‖actualACube η p‖≤1 := by
    have h := actualAPhase_norm_le_one η p
    rw [←actualACube_sq,norm_pow] at h
    nlinarith [norm_nonneg (actualACube η p)]
  have hρ := actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp)
  have hnorm : Ideal.absNorm (Ideal.span {p})=P.val.absNorm := congrArg Ideal.absNorm hspan
  constructor
  · have hb := ramifiedClosed_central_lower p hp hg.1 hg.2 _ _ _ x w z alpha eps
      (hspan.symm ▸ hQ) (by simpa only [hnorm] using hsmall) (targetMonoid_norm_le_one η p) ha hρ
      halpha halpha1 heps heps1 hx hw hz (multiplicity p u.val) (multiplicity_lt_six u p hp)
    exact hb
  · rw [continuedCompensatedLocal_ramified η u P hs hP x w z]
    have hb := ramifiedSelected_central_quotient p hp hg.1 hg.2 _ _ _ x w z alpha eps
      (hspan.symm ▸ hQ) (by simpa only [hnorm] using hsmall) (targetMonoid_norm_le_one η p) ha hρ
      halpha halpha1 heps heps1 hx hw hz (multiplicity p u.val) (multiplicity_lt_six u p hp)
    dsimp only at hb
    simpa only [ramifiedCorrection,p,hnorm] using hb
end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule1951

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.SelectedHolomorphic
Source SHA256: cd5fee1af1dbdf98b234cbe3c20af93fe5e7b1a810ec5a82cd1401b269e301c2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1952


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => HeckeFamily.O

theorem continuedCompensatedLocal_differentiableAt_x (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : (7/8:ℝ)<x.re) (hz : (4/25:ℝ)≤z.re) :
    DifferentiableAt ℂ (fun x=>continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))) x := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hQc : (P.val.absNorm:ℂ)≠0 := by exact_mod_cast hQ0.ne'
  have hM := (continuedMarkedLocal_analyticAt_x η u P hs hQ x w z hx hz).differentiableAt
  have hD := coordD_differentiable (P.val.absNorm:ℝ) hQ0 (idealCoeff η P.val) (idealRowHom u.val P.val)
  have hB : Differentiable ℂ (fun x:ℂ=>star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) :=
    (differentiable_id.const_cpow (Or.inl hQc)).const_mul _
  have hd := (open_region_denominators (P.val.absNorm:ℝ) 0 (idealCoeff η P.val)
    (idealRowHom u.val P.val) x z hQ (by simp) (idealCoeff_norm_le_one η _)
    (idealRowHom_norm u.val _) hx.le hz).2.2
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement
  fun_prop (disch := first | assumption | exact Or.inl hQc)

theorem continuedCompensatedLocal_differentiable_w (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x z : ℂ)
    (hx : (7/8:ℝ)≤x.re) (hz : (4/25:ℝ)≤z.re) :
    Differentiable ℂ (fun w=>continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))) := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hQc : (P.val.absNorm:ℂ)≠0 := by exact_mod_cast hQ0.ne'
  have hM := continuedMarkedLocal_differentiable_w η u P hs hQ x z hx hz
  have hW := coordW_differentiable (P.val.absNorm:ℝ) hQ0 (idealRowHom u.val P.val)
  have hq : Differentiable ℂ (fun w:ℂ=>(P.val.absNorm:ℂ)^(-w)) :=
    differentiable_id.neg.const_cpow (Or.inl hQc)
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement
  fun_prop

theorem continuedCompensatedLocal_differentiableAt_z (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : (7/8:ℝ)≤x.re) (hz : (4/25:ℝ)<z.re) :
    DifferentiableAt ℂ (fun z=>continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))) z := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hM := (continuedMarkedLocal_analyticAt_z η u P hs hQ x w z hx hz).differentiableAt
  have hV := coordV_differentiable (P.val.absNorm:ℝ) hQ0
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement
  fun_prop

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1952

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.MarkedHolomorphic
Source SHA256: dfe0826f8205ad4900214616ea5d6171a69b31534e21c7823a58231aa4458b78
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1953



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def physicalCompensatedRow (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) : ℂ :=
  continuedCompensatedRow S hS T hT η u x w z
    (fun P=>star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x)
    (fun P=>(P.val.absNorm:ℂ)^(-w))

theorem physicalCompensatedRow_first_differentiableAt_x (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : (7/8:ℝ)<x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) (hbeta : HeckeZeroSupremum.beta<x.re) :
    DifferentiableAt ℂ (fun x=>physicalCompensatedRow S hS T hT η u x w z) x := by
  unfold physicalCompensatedRow continuedCompensatedRow
  apply DifferentiableAt.mul
  · exact (HeckeReciprocal.reciprocal_differentiableAt _ hbeta).const_mul _
  · apply DifferentiableAt.mul
    · exact (continuedCorrection_first_boundary_x eps heps (markExclusions S T)
        (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
        (by linarith) hw hz hxw).differentiableAt
    · apply DifferentiableAt.fun_finsetProd
      intro P hP
      exact continuedCompensatedLocal_differentiableAt_x η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x w z hx (by linarith)

theorem physicalCompensatedRow_first_differentiableAt_w (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : (7/8:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) (hpole : w≠1 ∨ (rowCharacter S hS.prime u).residue≠1) :
    DifferentiableAt ℂ (fun w=>physicalCompensatedRow S hS T hT η u x w z) w := by
  unfold physicalCompensatedRow continuedCompensatedRow
  apply DifferentiableAt.mul
  · exact ((HeckeOrigin.continued_differentiableAt _ hpole).const_mul _).mul_const _
  · apply DifferentiableAt.mul
    · exact (continuedCorrection_first_boundary_w eps heps (markExclusions S T)
        (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
        (by linarith) hw hz hxw).differentiableAt
    · apply DifferentiableAt.fun_finsetProd
      intro P hP
      exact (continuedCompensatedLocal_differentiable_w η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x z hx (by linarith)) w

theorem physicalCompensatedRow_first_differentiableAt_z (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : (7/8:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    DifferentiableAt ℂ (fun z=>physicalCompensatedRow S hS T hT η u x w z) z := by
  have hz0 : 6*z≠0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [Complex.mul_re] at hh
    linarith
  have hz1 : 6*z≠1 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [Complex.mul_re] at hh
    linarith
  unfold physicalCompensatedRow continuedCompensatedRow
  apply DifferentiableAt.mul
  · exact (((LFunction_differentiableAt (fixedSourcePrincipal S hS.prime) hz0 (Or.inl hz1)).comp z
      (differentiableAt_id.const_mul 6)).mul_const _).mul_const _
  · apply DifferentiableAt.mul
    · exact (continuedCorrection_first_boundary_z eps heps (markExclusions S T)
        (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
        (by linarith) hw hz hxw).differentiableAt
    · apply DifferentiableAt.fun_finsetProd
      intro P hP
      exact continuedCompensatedLocal_differentiableAt_z η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x w z hx (by linarith)

theorem unselectedCorrection_subpower (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (T : Finset PrimeIdeal) (η : Character) (u : FreeRow) (x w z : ℂ),
      (7/8:ℝ)≤x.re → (19/20:ℝ)≤w.re → (33/200:ℝ)≤z.re →
      ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤
        C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^δ := by
  obtain ⟨C,hC,hbound⟩ := continuedCorrection_subpower δ hδ
  exact ⟨C,hC,fun S hS T η u x w z hx hw hz=>
    hbound (markExclusions S T) (markedSourceExclusions S hS T) η u x w z hx hw hz⟩

theorem unselectedCorrection_first_subpower (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀ (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (_hfirst : FirstTail eps S) (T : Finset PrimeIdeal) (η : Character) (u : FreeRow) (x w z : ℂ),
      (51/100:ℝ)≤x.re → -(1/100:ℝ)≤w.re → (17/50:ℝ)≤z.re → 1+eps≤x.re+w.re →
      ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤
        C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^δ := by
  obtain ⟨C,hC,hbound⟩ := continuedCorrection_first_subpower δ hδ
  exact ⟨C,hC,fun eps S hS hfirst T η u x w z hx hw hz hxw=>
    hbound eps (markExclusions S T) (markedSourceExclusions S hS T) (marked_firstTail eps S hfirst T)
      η u x w z hx hw hz hxw⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1953

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.SelectedFirst
Source SHA256: 4b7c9d62a0b651a0462f40d7f3e01027da230f1f47e91f23dcab077dc17d5cb8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1954



namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => HeckeFamily.O

theorem continuedMarkedLocal_first_analyticAt_x (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : (1/2:ℝ)<x.re) (hz : (1/3:ℝ)≤z.re) :
    AnalyticAt ℂ (fun x=>continuedMarkedLocal η u P hs x w z) x := by
  have he : (fun x=>continuedMarkedLocal η u P hs x w z)=
      (fun x=>(ramifiedCorrection η u P hs x w z-1)/(1-coordV P.val.absNorm z)) :=
    funext (fun x=>continuedMarkedLocal_eq_quotient η u P hs x w z (selected_V_ne_zero P hQ z (by linarith)))
  rw [he]
  exact (((ramifiedCorrection_first_analytic_x η u P hs hQ w z hz) x hx).sub analyticAt_const).div_const

theorem continuedMarkedLocal_first_differentiable_w (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x z : ℂ)
    (hx : (1/2:ℝ)≤x.re) (hz : (1/3:ℝ)≤z.re) :
    Differentiable ℂ (fun w=>continuedMarkedLocal η u P hs x w z) := by
  have he : (fun w=>continuedMarkedLocal η u P hs x w z)=
      (fun w=>(ramifiedCorrection η u P hs x w z-1)/(1-coordV P.val.absNorm z)) :=
    funext (fun w=>continuedMarkedLocal_eq_quotient η u P hs x w z (selected_V_ne_zero P hQ z (by linarith)))
  rw [he]
  exact ((ramifiedCorrection_first_analytic_w η u P hs hQ x z hx hz).sub_const 1).div_const _

theorem continuedMarkedLocal_first_analyticAt_z (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : (1/2:ℝ)≤x.re) (hz : (1/3:ℝ)<z.re) :
    AnalyticAt ℂ (fun z=>continuedMarkedLocal η u P hs x w z) z := by
  have hcv := (coordV_differentiable (P.val.absNorm:ℝ) (by linarith)).analyticAt z
  have ha : AnalyticAt ℂ (fun t=>(ramifiedCorrection η u P hs x w t-1)/(1-coordV P.val.absNorm t)) z :=
    (((ramifiedCorrection_first_analytic_z η u P hs hQ x w hx) z hz).sub analyticAt_const).div
    (analyticAt_const.sub hcv) (selected_V_ne_zero P hQ z (by linarith))
  apply ha.congr
  filter_upwards [(Complex.isOpen_re_gt (1/3)).mem_nhds hz] with t ht
  exact (continuedMarkedLocal_eq_quotient η u P hs x w t (selected_V_ne_zero P hQ t (by linarith))).symm

theorem continuedCompensatedLocal_first_differentiableAt_x (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : (1/2:ℝ)<x.re) (hz : (1/3:ℝ)≤z.re) :
    DifferentiableAt ℂ (fun x=>continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))) x := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hQc : (P.val.absNorm:ℂ)≠0 := by exact_mod_cast hQ0.ne'
  have hM := (continuedMarkedLocal_first_analyticAt_x η u P hs hQ x w z hx hz).differentiableAt
  have hD := coordD_differentiable (P.val.absNorm:ℝ) hQ0 (idealCoeff η P.val) (idealRowHom u.val P.val)
  have hB : Differentiable ℂ (fun x:ℂ=>star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) :=
    (differentiable_id.const_cpow (Or.inl hQc)).const_mul _
  have hd := (first_open_region_denominators (P.val.absNorm:ℝ) 0 (idealCoeff η P.val)
    (idealRowHom u.val P.val) x z hQ (by simp) (idealCoeff_norm_le_one η _)
    (idealRowHom_norm u.val _) hx.le hz).2.2
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement
  fun_prop (disch := first | assumption | exact Or.inl hQc)

theorem continuedCompensatedLocal_first_differentiable_w (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x z : ℂ)
    (hx : (1/2:ℝ)≤x.re) (hz : (1/3:ℝ)≤z.re) :
    Differentiable ℂ (fun w=>continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))) := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hQc : (P.val.absNorm:ℂ)≠0 := by exact_mod_cast hQ0.ne'
  have hM := continuedMarkedLocal_first_differentiable_w η u P hs hQ x z hx hz
  have hW := coordW_differentiable (P.val.absNorm:ℝ) hQ0 (idealRowHom u.val P.val)
  have hq : Differentiable ℂ (fun w:ℂ=>(P.val.absNorm:ℂ)^(-w)) :=
    differentiable_id.neg.const_cpow (Or.inl hQc)
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement
  fun_prop

theorem continuedCompensatedLocal_first_differentiableAt_z (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : (1/2:ℝ)≤x.re) (hz : (1/3:ℝ)<z.re) :
    DifferentiableAt ℂ (fun z=>continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))) z := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hM := (continuedMarkedLocal_first_analyticAt_z η u P hs hQ x w z hx hz).differentiableAt
  have hV := coordV_differentiable (P.val.absNorm:ℝ) hQ0
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement
  fun_prop

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1954

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.SelectedFirstBounds
Source SHA256: 2889b50093d14e95cfb3526b59e4f29ce341ff3a54eb2005f4b6699974aaaef6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1955


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CanonicalRowCompletion

lemma compensatedReplacement_crude (V W D M B q : ℂ) (A E : ℝ)
    (hA : 0≤A) (hE : 0≤E) (hV : ‖V‖≤1) (hW : ‖W‖≤A)
    (hD : ‖D‖≤1/2) (hM : ‖M‖≤388) (hB : ‖B‖≤E) (hq : ‖q‖≤A) :
    ‖ProbeLocal.compensatedReplacement V W D M B q‖≤
      2*((E+A)*2*(1+A)*388+A*(1+A)) := by
  have h1V : ‖1-V‖≤2 := by have h := norm_sub_le (1:ℂ) V;rw [norm_one] at h;linarith
  have h1W : ‖1-W‖≤1+A := by have h := norm_sub_le (1:ℂ) W;rw [norm_one] at h;linarith
  have h1VW : ‖1-V*W‖≤1+A := by
    apply (norm_sub_le (1:ℂ) (V*W)).trans
    rw [norm_one,norm_mul]
    have hm := (mul_le_mul hV hW (norm_nonneg _) (by norm_num)).trans_eq (one_mul A)
    linarith
  have hi := ProbeLocal.inv_one_sub_norm_le_two D hD
  unfold ProbeLocal.compensatedReplacement
  rw [div_eq_mul_inv,norm_mul]
  calc
    _ ≤ ((‖B-q‖*‖1-V‖*‖1-W‖*‖M‖)+‖q‖*‖1-V*W‖)*2 := by
      apply mul_le_mul _ hi (norm_nonneg _) (by positivity)
      simpa only [norm_mul] using norm_sub_le ((B-q)*(1-V)*(1-W)*M) (q*(1-V*W))
    _ ≤ ((E+A)*2*(1+A)*388+A*(1+A))*2 := by
      have hbq : ‖B-q‖≤E+A := (norm_sub_le B q).trans (add_le_add hB hq)
      gcongr
    _ = _ := by ring

def selectedFirstBound (Q R : ℝ) : ℝ :=
  2*((Q^R+Q^(1/100:ℝ))*2*(1+Q^(1/100:ℝ))*388+Q^(1/100:ℝ)*(1+Q^(1/100:ℝ)))

lemma selectedFirstBound_nonneg (Q R : ℝ) (hQ : 0≤Q) : 0≤selectedFirstBound Q R := by
  unfold selectedFirstBound
  positivity

theorem continuedCompensatedLocal_first_bound (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (R : ℝ) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hxR : x.re≤R) (hw : -(1/100:ℝ)≤w.re)
    (hz : (17/50:ℝ)≤z.re) (hxw : 1≤x.re+w.re) :
    ‖continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))‖≤
        selectedFirstBound P.val.absNorm R := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hQ1 : (1:ℝ)≤P.val.absNorm := by linarith
  have hV := first_region_V_half _ hQ z hz
  have hD : ‖coordD P.val.absNorm (idealCoeff η P.val) (idealRowHom u.val P.val) x‖≤1/2 :=
    (coordD_norm_le _ hQ0 _ _ x (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _)).trans
      (rpow_le_half _ _ hQ (by linarith))
  have hM : ‖continuedMarkedLocal η u P hs x w z‖≤388 := by
    rw [continuedMarkedLocal_eq_quotient η u P hs x w z
      (ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV),div_eq_mul_inv,norm_mul]
    have hH := ramifiedCorrection_first_bound η u P hs hQ x w z hx hw hz hxw
    have hn : ‖ramifiedCorrection η u P hs x w z-1‖≤194 := by
      have h := norm_sub_le (ramifiedCorrection η u P hs x w z) (1:ℂ)
      rw [norm_one] at h
      linarith
    exact (mul_le_mul hn (ProbeLocal.inv_one_sub_norm_le_two _ hV) (norm_nonneg _) (by norm_num)).trans (by norm_num)
  have hW : ‖coordW P.val.absNorm (idealRowHom u.val P.val) w‖≤(P.val.absNorm:ℝ)^(1/100:ℝ) :=
    (coordW_norm_le _ hQ0 _ w (idealRowHom_norm u.val _)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hq : ‖(P.val.absNorm:ℂ)^(-w)‖≤(P.val.absNorm:ℝ)^(1/100:ℝ) := by
    rw [show (P.val.absNorm:ℂ)=((P.val.absNorm:ℝ):ℂ) from by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hB : ‖star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x‖≤(P.val.absNorm:ℝ)^R := by
    rw [norm_mul,norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η _)).trans
    rw [show (P.val.absNorm:ℂ)=((P.val.absNorm:ℝ):ℂ) from by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 hxR
  exact compensatedReplacement_crude _ _ _ _ _ _ _ _ (by positivity) (by positivity)
    (hV.trans (by norm_num)) hW hD hM hB hq

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1955

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.SlotSums
Source SHA256: eb5af8ffcf2ceb8cdecf67b8a272979e41fcd05168cc8445e3a90d031c865975
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1956



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem continued_selected_slot_bound (eps a b r B : ℝ) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hr : (17/50:ℝ)≤r) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) (T : Finset PrimeIdeal)
      (hT : ∀P∈T,Supported P.val ∧ (4:ℝ)≤P.val.absNorm)
      (Y : ℝ),1≤Y → ∀(W : ℝ→ℂ),Function.support W⊆Set.Icc a b →
      (∀y,‖W y‖≤B) → ∀(x w z : ℂ),(7/8:ℝ)≤x.re → (1/2:ℝ)≤w.re → z.re=r →
      (∑P : T,‖W ((P.val.val.absNorm:ℝ)/Y)*(P.val.val.absNorm:ℂ)^(z-1)*
        continuedCompensatedLocal η u P.val (hT P.val P.property).1 x w z
          (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w))‖)
      ≤C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*Y^r := by
  obtain ⟨C,hC,hmain⟩ := ProbeSelectedPrimeSums.weighted_slot_bound_indexed eps a b r (1/2) B 961
    heps ha hb (by norm_num) hB (by norm_num)
  refine ⟨C,hC,?_⟩
  intro η u T hT Y hY W hWS hWB x w z hx hw hz
  let f : T→Ideal O := fun P=>P.val.val
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    exact Subtype.ext h
  let G : T→ℂ := fun P=>continuedCompensatedLocal η u P.val (hT P.val P.property).1 x w z
    (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w))
  have hg (P : T) (_ : P∈Finset.univ) : ‖G P‖≤
      961*(if f P∣Ideal.span {u.val} then (Ideal.absNorm (f P):ℝ)^(1/2:ℝ) else 1) := by
    have hh := continuedCompensatedLocal_bound η u P.val (hT P.val P.property).1
      (hT P.val P.property).2 x w z hx hw (by rw [hz];exact hr)
    apply hh.trans
    by_cases hp : f P∣Ideal.span {u.val}
    · simp only [show P.val.val=f P from rfl,ite_eq_left hp]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.rpow_le_rpow_of_exponent_le (by have := (hT P.val P.property).2;change 1≤(P.val.val.absNorm:ℝ);linarith)
        (max_le (by linarith) (by norm_num))
    · simp only [show P.val.val=f P from rfl,ite_eq_right hp,le_refl]
  exact hmain f hf (Ideal.span {u.val}) (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
    Y hY Finset.univ (fun P _=>P.val.property.ne_zero) W hWS hWB G hg z hz

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule1956

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.TupleFactor
Source SHA256: a49753c5cca61f4bd41ecd88bdd122aa61b5e7beeb89c98e817f7999b85b4fc0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1957


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem physicalCompensatedRow_indexed {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ) :
    let hT : ∀Q∈Finset.univ.image P,Q.val∉S := by
      intro Q hQ
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
      exact hPS i
    physicalCompensatedRow S hS (Finset.univ.image P) hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (continuedCorrection (markExclusions S (Finset.univ.image P))
        (markedSourceExclusions S hS (Finset.univ.image P)) η u x w z*
        ∏i,continuedCompensatedLocal η u (P i)
          (outside_prime_supported S hS.bad (P i) (hPS i)) x w z
          (star (idealCoeff η (P i).val)*((P i).val.absNorm:ℂ)^x)
          (((P i).val.absNorm:ℂ)^(-w))) := by
  dsimp only
  unfold physicalCompensatedRow continuedCompensatedRow
  congr 2
  symm
  apply Finset.prod_bij (fun i _=>⟨P i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
  · intro i _; exact Finset.mem_attach _ _
  · intro i _ j _ h; exact hP (congrArg Subtype.val h)
  · intro Q _
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp Q.property
    exact ⟨i,hi,Subtype.ext he⟩
  · intro i _; rfl

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule1957

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.TupleSums
Source SHA256: 004d013705ad0f9c9ea2afdd781f2422bd17ca4f51000db26204021e1a72ace8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1958


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem continued_selected_tuple_bound (K : ℕ) (eps a b r B : ℝ) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hr : (17/50:ℝ)≤r) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) (T : Fin K→Finset PrimeIdeal)
      (hT : ∀i P,P∈T i→Supported P.val ∧ (4:ℝ)≤P.val.absNorm)
      (Y : Fin K→ℝ), (∀i,1≤Y i) → ∀(W : Fin K→ℝ→ℂ),
      (∀i,Function.support (W i)⊆Set.Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀(x w z : ℂ),(7/8:ℝ)≤x.re → (1/2:ℝ)≤w.re → z.re=r →
      (∑P : (∀i, T i),‖∏i,
        W i (((P i).val.val.absNorm:ℝ)/Y i)*((P i).val.val.absNorm:ℂ)^(z-1)*
        continuedCompensatedLocal η u (P i).val (hT i (P i).val (P i).property).1 x w z
          (star (idealCoeff η (P i).val.val)*((P i).val.val.absNorm:ℂ)^x)
          (((P i).val.val.absNorm:ℂ)^(-w))‖)
      ≤C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*∏i,(Y i)^r := by
  let d : ℝ := eps/((K:ℝ)+1)
  have hd : 0<d := div_pos heps (by positivity)
  obtain ⟨C,hC,hmain⟩ := continued_selected_slot_bound d a b r B hd ha hb hr hB
  refine ⟨C^K,pow_pos hC K,?_⟩
  intro η u T hT Y hY W hWS hWB x w z hx hw hz
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hN : 1≤N := by
    dsimp [N]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  have hdK : d*(K:ℝ)≤eps := by
    dsimp [d]
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : (0:ℝ)<(K:ℝ)+1)]
    nlinarith
  have hpow : (N^d)^K≤N^eps := by
    rw [←Real.rpow_mul_natCast (by linarith : 0≤N)]
    exact Real.rpow_le_rpow_of_exponent_le hN hdK
  let F : ∀i:Fin K,T i→ℂ := fun i P=>
    W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
      continuedCompensatedLocal η u P.val (hT i P.val P.property).1 x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w))
  change (∑P:(∀i,T i),‖∏i,F i (P i)‖)≤C^K*N^eps*∏i,(Y i)^r
  simp_rw [norm_prod]
  rw [←Fintype.prod_sum (fun i P=>‖F i P‖)]
  calc
    _ ≤ ∏i:Fin K, (C*N^d*(Y i)^r) := by
      apply Finset.prod_le_prod₀
      · intro i _; exact Finset.sum_nonneg fun _ _=>norm_nonneg _
      · intro i _; exact hmain η u (T i) (hT i) (Y i) (hY i) (W i) (hWS i) (hWB i) x w z hx hw hz
    _ = C^K*(N^d)^K*∏i:Fin K,(Y i)^r := by
      simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    _ ≤ C^K*N^eps*∏i:Fin K,(Y i)^r := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity))
        (Finset.prod_nonneg fun i _=>Real.rpow_nonneg (by linarith [hY i]) _)

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule1958

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.TupleBound
Source SHA256: a0ae48749526bab88ea7b05e5c08893137335ef7b83cac75077f0c401d80fdf3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1959



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

theorem continued_selected_tuple_with_correction (K : ℕ) (δ a b r B : ℝ)
    (hδ : 0<δ) (ha : 0<a) (hb : 0<b) (hr : (17/50:ℝ)≤r) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (_hfirst : FirstTail eps S) (η : Character) (u : FreeRow)
      (T : Fin K→Finset PrimeIdeal)
      (hT : ∀i P,P∈T i→Supported P.val ∧ (4:ℝ)≤P.val.absNorm)
      (Y : Fin K→ℝ), (∀i,1≤Y i) → ∀(W : Fin K→ℝ→ℂ),
      (∀i,Function.support (W i)⊆Set.Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀(x w z : ℂ),(7/8:ℝ)≤x.re → (1/2:ℝ)≤w.re → z.re=r →
      1+eps≤x.re+w.re →
      (∑P : (∀i,T i),‖continuedCorrection
        (markExclusions S (Finset.univ.image (fun i=>(P i).val)))
        (markedSourceExclusions S hS (Finset.univ.image (fun i=>(P i).val))) η u x w z*
        ∏i,W i (((P i).val.val.absNorm:ℝ)/Y i)*((P i).val.val.absNorm:ℂ)^(z-1)*
          continuedCompensatedLocal η u (P i).val (hT i (P i).val (P i).property).1 x w z
            (star (idealCoeff η (P i).val.val)*((P i).val.val.absNorm:ℂ)^x)
            (((P i).val.val.absNorm:ℂ)^(-w))‖)
      ≤C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^δ*∏i,(Y i)^r := by
  obtain ⟨C₁,hC₁,hmain⟩ := continued_selected_tuple_bound K (δ/2) a b r B (by linarith) ha hb hr hB
  obtain ⟨C₂,hC₂,hcorr⟩ := unselectedCorrection_first_subpower (δ/2) (by linarith)
  refine ⟨C₂*C₁,mul_pos hC₂ hC₁,?_⟩
  intro eps S hS hfirst η u T hT Y hY W hWS hWB x w z hx hw hz hxw
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hN : 0<N := by
    dsimp [N]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  let F : (∀i,T i)→ℂ := fun P=>∏i,
    W i (((P i).val.val.absNorm:ℝ)/Y i)*((P i).val.val.absNorm:ℂ)^(z-1)*
      continuedCompensatedLocal η u (P i).val (hT i (P i).val (P i).property).1 x w z
        (star (idealCoeff η (P i).val.val)*((P i).val.val.absNorm:ℂ)^x)
        (((P i).val.val.absNorm:ℂ)^(-w))
  calc
    _ ≤ ∑P:(∀i,T i),(C₂*N^(δ/2))*‖F P‖ := by
      apply Finset.sum_le_sum
      intro P _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hcorr eps S hS hfirst (Finset.univ.image (fun i=>(P i).val)) η u x w z
          (by linarith) (by linarith) (by rw [hz];exact hr) hxw) (norm_nonneg _)
    _ = (C₂*N^(δ/2))*∑P:(∀i,T i),‖F P‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ (C₂*N^(δ/2))*(C₁*N^(δ/2)*∏i,(Y i)^r) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hmain η u T hT Y hY W hWS hWB x w z hx hw hz
    _ = (C₂*C₁)*N^δ*∏i,(Y i)^r := by
      have hp : N^(δ/2)*N^(δ/2)=N^δ := by
        rw [←Real.rpow_add hN]
        congr 1
        ring
      calc
        _ = (C₂*C₁)*(N^(δ/2)*N^(δ/2))*∏i,(Y i)^r := by ring
        _ = _ := by rw [hp]

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule1959

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.WeightedTuple
Source SHA256: 3895f373e22a29a484c883bd5f03c420381fc10de00fc296e9084c02eb178fc5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1960


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem tupleOutside {K : ℕ} (S : Finset (Ideal O)) (P : Fin K→PrimeIdeal)
    (hPS : ∀i,(P i).val∉S) : ∀Q∈Finset.univ.image P,Q.val∉S := by
  intro Q hQ
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
  exact hPS i

def calibratedTupleValue {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) : ℂ :=
  star ((calibrationForSet S hmax).residueMonoid u.val)*
  (∏i,W i (((P i).val.absNorm:ℝ)/Y i)*((P i).val.absNorm:ℂ)^(z-1))*
  physicalCompensatedRow S hS (Finset.univ.image P) (tupleOutside S P hPS) η u x w z

theorem calibratedTupleValue_factor {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow)
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) :
    calibratedTupleValue S hS hmax η u P hPS W Y x w z=
      (star ((calibrationForSet S hmax).residueMonoid u.val)*
        (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
          HeckeOrigin.continued (rowCharacter S hS.prime u) w*
          HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x))*
      (continuedCorrection (markExclusions S (Finset.univ.image P))
        (markedSourceExclusions S hS (Finset.univ.image P)) η u x w z*
        ∏i,W i (((P i).val.absNorm:ℝ)/Y i)*((P i).val.absNorm:ℂ)^(z-1)*
          continuedCompensatedLocal η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z
            (star (idealCoeff η (P i).val)*((P i).val.absNorm:ℂ)^x)
            (((P i).val.absNorm:ℂ)^(-w))) := by
  unfold calibratedTupleValue
  rw [physicalCompensatedRow_indexed S hS P hP hPS]
  simp only [Finset.prod_mul_distrib]
  ring

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule1960

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.Measurable
Source SHA256: 25d2eb1bd498bb29f7c0abf0b0c81e1fc21facb51d814c54e9c04a8ed48057a5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1961



namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => HeckeFamily.O

@[fun_prop] lemma measurable_const_cpow {α : Type*} [MeasurableSpace α]
    (Q : ℂ) (hQ : Q≠0) (f : α→ℂ) (hf : Measurable f) : Measurable (fun t=>Q^(f t)) :=
  ((continuous_id.const_cpow (Or.inl hQ)).measurable).comp hf

lemma rowClosedMarked_measurable {α : Type*} [MeasurableSpace α]
    (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda∉Ideal.span {p}) (η a ρ : ℂ) (j : ℕ)
    (X W V : α→ℂ) (hX : Measurable X) (hW : Measurable W) (hV : Measurable V) :
    Measurable (fun t=>rowClosedMarked p hp hg η a (X t) (W t) (V t) ρ j) := by
  unfold rowClosedMarked rowBaseFinite rowMarkedTerm rowWeightedScalar weightedScalar evenRatio
  simp only [Nat.reduceAdd,Nat.reduceMul,OfNat.ofNat_ne_zero,Nat.one_ne_zero,ite_false]
  fun_prop

lemma continuedMarkedLocal_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (u : FreeRow) (P : PrimeIdeal) (hs : Supported P.val)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>continuedMarkedLocal η u P hs (x t) (w t) (z t)) := by
  have hQ : (P.val.absNorm:ℂ)≠0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold continuedMarkedLocal
  apply rowClosedMarked_measurable
  · exact measurable_const_cpow _ hQ _ hx.neg
  · exact measurable_const_cpow _ hQ _ hw.neg
  · unfold coordV
    apply measurable_const_cpow _ (by exact_mod_cast hQ)
    fun_prop

lemma ramifiedCorrection_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (u : FreeRow) (P : PrimeIdeal) (hs : Supported P.val)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>ramifiedCorrection η u P hs (x t) (w t) (z t)) := by
  have hm := continuedMarkedLocal_measurable η u P hs x w z hx hw hz
  have hQ : ((P.val.absNorm:ℝ):ℂ)≠0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  simp_rw [ramifiedCorrection_eq_marked]
  unfold coordV
  fun_prop (disch := exact hQ)

lemma idealUnramifiedCorrection_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>idealUnramifiedCorrection η u P (x t) (w t) (z t)) := by
  have hQ : ((P.val.absNorm:ℝ):ℂ)≠0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  unfold idealUnramifiedCorrection unramifiedClosed ProbeLocal.continuedCorrection markedFactor
    coordV coordR coordW coordD coordK
  fun_prop (disch := exact hQ)

lemma continuedCorrection_measurable {α : Type*} [MeasurableSpace α]
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) (u : FreeRow)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>continuedCorrection S hS η u (x t) (w t) (z t)) := by
  unfold continuedCorrection ramifiedProduct unramifiedProduct
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro P hP
    exact ramifiedCorrection_measurable η u P.val _ x w z hx hw hz
  · apply Measurable.tprod
    intro P
    unfold unramifiedFactor
    split_ifs
    · exact measurable_const
    · exact idealUnramifiedCorrection_measurable η u P.val x w z hx hw hz

lemma continuedCompensatedLocal_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (u : FreeRow) (P : PrimeIdeal) (hs : Supported P.val)
    (x w z B q : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z)
    (hB : Measurable B) (hq : Measurable q) :
    Measurable (fun t=>continuedCompensatedLocal η u P hs (x t) (w t) (z t) (B t) (q t)) := by
  have hM := continuedMarkedLocal_measurable η u P hs x w z hx hw hz
  have hQ : ((P.val.absNorm:ℝ):ℂ)≠0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement coordV coordW coordD
  fun_prop (disch := exact hQ)

lemma LFunction_measurable (χ : Character) : Measurable (LFunction χ) := by
  apply measurable_of_countable_not_continuousAt
  apply ((Set.finite_singleton (1:ℂ)).insert 0).countable.mono
  intro s hs
  by_contra hn
  have h0 : s≠0 := fun h=>hn (by simp [h])
  have h1 : s≠1 := fun h=>hn (by simp [h])
  exact hs (LFunction_differentiableAt χ h0 (Or.inl h1)).continuousAt

lemma regularizedL_measurable (χ : Character) : Measurable (HeckeReciprocal.regularizedL χ) := by
  apply measurable_of_countable_not_continuousAt
  apply (Set.countable_singleton (0:ℂ)).mono
  intro s hs
  by_contra hn
  exact hs (HeckeReciprocal.regularizedL_differentiableAt χ (by simpa using hn)).continuousAt

lemma reciprocal_measurable (χ : Character) : Measurable (HeckeReciprocal.reciprocal χ) := by
  have hL := LFunction_measurable χ
  have hR := regularizedL_measurable χ
  unfold HeckeReciprocal.reciprocal
  split_ifs <;> fun_prop

lemma continuedL_measurable (χ : Character) : Measurable (HeckeOrigin.continued χ) := by
  have hL := LFunction_measurable χ
  have hR := (HeckeOrigin.poleRemoved_entire χ).continuous.measurable
  unfold HeckeOrigin.continued
  split_ifs <;> fun_prop

lemma physicalCompensatedRow_measurable {α : Type*} [MeasurableSpace α]
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>physicalCompensatedRow S hS T hT η u (x t) (w t) (z t)) := by
  unfold physicalCompensatedRow continuedCompensatedRow
  apply Measurable.mul
  · exact (((LFunction_measurable _).comp (by fun_prop)).mul
      ((continuedL_measurable _).comp hw)).mul ((reciprocal_measurable _).comp hx)
  · apply Measurable.mul
    · exact continuedCorrection_measurable _ _ η u x w z hx hw hz
    · apply Finset.measurable_prod
      intro P hP
      have hQ : (P.val.val.absNorm:ℂ)≠0 := by
        exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.val.property.ne_zero)
      apply continuedCompensatedLocal_measurable _ _ _ _ x w z _ _ hx hw hz
      · exact (measurable_const_cpow _ hQ x hx).const_mul _
      · exact measurable_const_cpow _ hQ _ hw.neg

lemma calibratedTupleValue_measurable {α : Type*} [MeasurableSpace α] {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>calibratedTupleValue S hS hmax η u P hPS W Y (x t) (w t) (z t)) := by
  unfold calibratedTupleValue
  apply Measurable.mul
  · apply Measurable.const_mul
    apply Finset.measurable_prod
    intro i hi
    apply Measurable.const_mul
    apply measurable_const_cpow _ _ _ (hz.sub measurable_const)
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr (P i).property.ne_zero)
  · exact physicalCompensatedRow_measurable S hS _ _ η u x w z hx hw hz

lemma calibratedTupleValue_onLines_aestronglyMeasurable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (σ υ ξ : ℝ)
    (μ : Measure ((ℝ×ℝ)×ℝ)) :
    AEStronglyMeasurable (fun t : (ℝ×ℝ)×ℝ=>
      calibratedTupleValue S hS hmax η u P hPS W Y
        ((σ:ℂ)+t.1.1*Complex.I) ((υ:ℂ)+t.2*Complex.I) ((ξ:ℂ)+t.1.2*Complex.I)) μ :=
  (calibratedTupleValue_measurable S hS hmax η u P hPS W Y _ _ _
    (by fun_prop) (by fun_prop) (by fun_prop)).aestronglyMeasurable

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1961

/-! Original module: OAI.NumberTheory.DirichletL.RayPrimeNormalizer
Source SHA256: 687d40a238d0963b8734a8a8c258fd32afc7c77fe8d66e06fe178c3802d4bebe
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1962



namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Classical Topology ContDiff
namespace SevenEighths.RayPrimeNormalizer
open HeckeFamily
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

def normalizer (S : Finset (Ideal O)) (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  PNT.AnnularPrimeMass.weightedPrimeSumDeleted (RayQuotient.identityClass M H) S W x

include hH

theorem asymptotic (S : Finset (Ideal O)) (W : ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ => Real.log x / x ^ (1/6 : ℝ) * normalizer M H S W x)
      atTop (𝓝 ((RayQuotient.classNumber M H : ℝ)⁻¹ * ∫ y : ℝ, W y * y ^ (-5/6 : ℝ))) :=
  PNT.AnnularPrimeMass.weightedPrimeSumDeleted_tendsto _ S
    (HeckeRayPrimes.quotientClassCoeff_ratio_tendsto M H hH) W hW hc hp

theorem eventually_lower_bound (S : Finset (Ideal O)) (W : ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0)
    (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c * x ^ (1/6 : ℝ) / Real.log x ≤ normalizer M H S W x := by
  apply PNT.AnnularPrimeMass.weightedPrimeSumDeleted_eventually_lower_bound _ S
    (show 0 < (RayQuotient.classNumber M H : ℝ)⁻¹ from inv_pos.mpr (by
      exact_mod_cast RayQuotient.classNumber_pos M H))
    (HeckeRayPrimes.quotientClassCoeff_ratio_tendsto M H hH) W hW hc hp hW0 hWne

theorem eventually_pos (S : Finset (Ideal O)) (W : ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0)
    (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    ∀ᶠ x : ℝ in atTop, 0 < normalizer M H S W x := by
  apply PNT.AnnularPrimeMass.weightedPrimeSumDeleted_eventually_pos _ S
    (show 0 < (RayQuotient.classNumber M H : ℝ)⁻¹ from inv_pos.mpr (by
      exact_mod_cast RayQuotient.classNumber_pos M H))
    (HeckeRayPrimes.quotientClassCoeff_ratio_tendsto M H hH) W hW hc hp hW0 hWne

end SevenEighths.RayPrimeNormalizer

end

end OAI
end OAIOriginalModule1962

/-! Original module: OAI.NumberTheory.DirichletL.Moments.PrimePool
Source SHA256: 5147e754c3107eec3c8f49f62c4af701b9a7f9ff0e54a5025832466aca3744e7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1963



namespace OAI

noncomputable section
open scoped BigOperators Classical Topology ContDiff
open Filter
namespace SevenEighths.CenteredMomentPrimePool
open HeckeFamily PNT.AnnularPrimeMass CenteredMomentAmplificationCount

def primePool (M : Ideal O) [NeZero M]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) (a b x : ℝ) : Finset (Ideal O) :=
  annularPrimeIdeals (RayQuotient.identityClass M H) a b x \ S

theorem annular_weighted_card_bound (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) (a b B x : ℝ) (ha : 0 < a) (hab : a ≤ b) (hB : 0 ≤ B)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hW : ∀ y, W y ≤ B) (hx : 0 < x) :
    weightedPrimeSumDeleted C S W x ≤
      ((annularPrimeIdeals C a b x \ S).card : ℝ) * (B * a^(-5/6 : ℝ)) * x^(-5/6 : ℝ) := by
  rw [weightedPrimeSumDeleted_eq_annular C S W ha hab hsupp hx]
  calc
    _ ≤ ∑ _P ∈ annularPrimeIdeals C a b x \ S, B*(a*x)^(-5/6 : ℝ) := by
      apply Finset.sum_le_sum
      intro P hP
      have hn := (norm_bounds_of_mem_annularPrimeIdeals ha.le hab hx (Finset.mem_sdiff.mp hP).1).1
      apply mul_le_mul (hW _) _ (Real.rpow_nonneg (Nat.cast_nonneg _) _) hB
      exact Real.rpow_le_rpow_of_nonpos (mul_pos ha hx) (by nlinarith) (by norm_num)
    _ = _ := by
      rw [Finset.sum_const,nsmul_eq_mul,Real.mul_rpow ha.le hx.le]
      ring

section FixedRay
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

include hH

theorem eventually_primePool_card (S : Finset (Ideal O)) (W : ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0)
    (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0)
    (a b B : ℝ) (ha : 0 < a) (hab : a ≤ b) (hB : 0 < B)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hbound : ∀ y, W y ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c*x/Real.log x ≤ (primePool M H S a b x).card := by
  obtain ⟨c,hcpos,hlower⟩ := RayPrimeNormalizer.eventually_lower_bound M H hH S W hW hc hp hW0 hWne
  let D : ℝ := B*a^(-5/6 : ℝ)
  have hD : 0 < D := mul_pos hB (Real.rpow_pos_of_pos ha _)
  refine ⟨c/D,div_pos hcpos hD,?_⟩
  filter_upwards [hlower,eventually_gt_atTop (1 : ℝ)] with x hlow hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hu := annular_weighted_card_bound (RayQuotient.identityClass M H) S W a b B x
    ha hab hB.le hsupp hbound hx0
  change weightedPrimeSumDeleted _ S W x ≤ (primePool M H S a b x).card * D * x^(-5/6 : ℝ) at hu
  change c*x^(1/6 : ℝ)/Real.log x ≤ weightedPrimeSumDeleted _ S W x at hlow
  have hpower : x*x^(-5/6 : ℝ) = x^(1/6 : ℝ) := by
    calc
      _ = x^(1 : ℝ)*x^(-5/6 : ℝ) := by rw [Real.rpow_one]
      _ = x^((1 : ℝ)+(-5/6)) := (Real.rpow_add hx0 _ _).symm
      _ = _ := by norm_num
  have hmul : (c*x/Real.log x)*x^(-5/6 : ℝ) ≤
      ((primePool M H S a b x).card * D)*x^(-5/6 : ℝ) := by
    calc
      _ = c*(x*x^(-5/6 : ℝ))/Real.log x := by ring
      _ = _ := by rw [hpower]
      _ ≤ _ := hlow.trans hu
  have hcancel := le_of_mul_le_mul_right hmul (Real.rpow_pos_of_pos hx0 (-5/6 : ℝ))
  convert (div_le_iff₀ hD).mpr hcancel using 1 ; ring

end FixedRay

def eligiblePool (P : Finset (Ideal O)) (R : Ideal O) : Finset (Ideal O) :=
  P.filter (fun Q => ¬Q ∣ R)

theorem eligiblePool_card_lower (P : Finset (Ideal O)) (hp : ∀ Q ∈ P, Prime Q)
    (R : Ideal O) (hR : R ≠ 0) (Z ℓ B : ℝ) (hZ : 1 < Z) (hℓ : 0 < ℓ)
    (hlower : ∀ Q ∈ P, Z^ℓ ≤ (Ideal.absNorm Q : ℝ))
    (hupper : (Ideal.absNorm R : ℝ) ≤ Z^B) :
    (P.card : ℝ) - B/ℓ ≤ (eligiblePool P R).card := by
  have hbad := large_prime_divisor_count (P.filter (fun Q => Q ∣ R))
    (fun Q hQ => hp Q (Finset.mem_filter.mp hQ).1) R hR
    (fun Q hQ => (Finset.mem_filter.mp hQ).2) Z ℓ B hZ hℓ
    (fun Q hQ => hlower Q (Finset.mem_filter.mp hQ).1) hupper
  have he := Finset.card_filter_add_card_filter_not (s := P) (fun Q => Q ∣ R)
  have her : ((P.filter (fun Q => Q ∣ R)).card : ℝ) + (eligiblePool P R).card = P.card := by
    exact_mod_cast he
  linarith

theorem eligiblePool_half (P : Finset (Ideal O)) (hp : ∀ Q ∈ P, Prime Q)
    (R : Ideal O) (hR : R ≠ 0) (Z ℓ B : ℝ) (hZ : 1 < Z) (hℓ : 0 < ℓ)
    (hlower : ∀ Q ∈ P, Z^ℓ ≤ (Ideal.absNorm Q : ℝ))
    (hupper : (Ideal.absNorm R : ℝ) ≤ Z^B) (hsize : 2*(B/ℓ) ≤ P.card) :
    (P.card : ℝ)/2 ≤ (eligiblePool P R).card := by
  have h := eligiblePool_card_lower P hp R hR Z ℓ B hZ hℓ hlower hupper
  linarith

end SevenEighths.CenteredMomentPrimePool

end

end OAI
end OAIOriginalModule1963

/-! Original module: OAI.NumberTheory.DirichletL.Moments.PrimeElements
Source SHA256: 5d0d52de73f648b4593ba0f52cb95f17d50db88e546d26e01566e37bdeea2147
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1964


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentPrimeElements
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentPrimePool CenteredMomentAmplificationGlobal
local notation "O" => ActualEisensteinCubic.O

def elementPool (P : Finset (Ideal O)) : Finset O := P.image primaryPrime

theorem primaryPrime_data (P : Ideal O) (hp : Prime P) (hbad : P ∉ fixedBadPrimes) :
    Prime (primaryPrime P) ∧ Ideal.span {primaryPrime P} = P ∧
    ConcretePrimeRowBridge.goodLambda^2 ∣ primaryPrime P - 1 ∧
    Supported (Ideal.span {primaryPrime P}) ∧
    ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {primaryPrime P} ∧
    ringChar (O ⧸ Ideal.span {primaryPrime P}) ≠ 2 := by
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hg := (prime_good_iff_not_bad P).mpr hbad
  have hn := primaryPrime_ne_zero P hg.1
  have hs := (primaryPrime_spec P hn).2.2
  have hsupport : Supported P := by
    refine ⟨hp.ne_zero,?_⟩
    intro Q hQ
    have he : Q = P := by
      simpa only [UniqueFactorizationMonoid.normalizedFactors_irreducible hp.irreducible,
        normalize_eq,Multiset.mem_singleton] using hQ
    subst Q
    exact hg
  refine ⟨?_,hs.1,hs.2,?_,?_,?_⟩
  · apply (Ideal.span_singleton_prime hn).mp
    rw [hs.1]
    infer_instance
  · rwa [hs.1]
  · rw [hs.1]
    exact hg.1
  · rw [hs.1]
    exact hg.2

theorem elementPool_card (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes) :
    (elementPool P).card = P.card := by
  apply Finset.card_image_of_injOn
  intro Q hQ R hR he
  rw [← (primaryPrime_data Q (hp Q hQ) (hbad Q hQ)).2.1,
    ← (primaryPrime_data R (hp R hR) (hbad R hR)).2.1,he]

theorem elementPool_data (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (p : O) (hpm : p ∈ elementPool P) :
    Prime p ∧ Ideal.span {p} ∈ P ∧
    ConcretePrimeRowBridge.goodLambda^2 ∣ p-1 ∧
    Supported (Ideal.span {p}) ∧
    ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p} ∧
    ringChar (O ⧸ Ideal.span {p}) ≠ 2 := by
  obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hpm
  obtain ⟨hpr,hspan,hprim,hs,hg,hc⟩ := primaryPrime_data Q (hp Q hQ) (hbad Q hQ)
  exact ⟨hpr,hspan.symm ▸ hQ,hprim,hs,hg,hc⟩

theorem eligible_not_dvd (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (R : Ideal O) (h : O) (hh : Ideal.span {h} ∣ R)
    (p : O) (hpm : p ∈ elementPool (eligiblePool P R)) : ¬p ∣ h := by
  have hd := elementPool_data (eligiblePool P R)
    (fun Q hQ => hp Q (Finset.mem_filter.mp hQ).1)
    (fun Q hQ => hbad Q (Finset.mem_filter.mp hQ).1) p hpm
  intro hph
  apply (Finset.mem_filter.mp hd.2.1).2
  exact (Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr hph)).trans hh

theorem primePool_data (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (hS : fixedBadPrimes ⊆ S) (a b x : ℝ)
    (Q : Ideal O) (hQ : Q ∈ primePool M H S a b x) :
    Prime Q ∧ Q ∉ fixedBadPrimes := by
  obtain ⟨hQ,hQS⟩ := Finset.mem_sdiff.mp hQ
  exact ⟨((PNT.AnnularPrimeMass.mem_annularPrimeIdeals _ _ _ _ _).mp hQ).2.1,
    fun hbad => hQS (hS hbad)⟩

theorem elementPool_eligible (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (R : Ideal O) :
    (elementPool P).filter (fun p => ¬Ideal.span {p} ∣ R) =
      elementPool (eligiblePool P R) := by
  ext p
  simp only [elementPool,eligiblePool,Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨⟨Q,hQ,rfl⟩,hnot⟩
    refine ⟨Q,⟨hQ,?_⟩,rfl⟩
    rwa [← (primaryPrime_data Q (hp Q hQ) (hbad Q hQ)).2.1]
  · rintro ⟨Q,⟨hQ,hnot⟩,rfl⟩
    refine ⟨⟨Q,hQ,rfl⟩,?_⟩
    rwa [(primaryPrime_data Q (hp Q hQ) (hbad Q hQ)).2.1]

theorem eligible_element_card_half (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (R : Ideal O) (hR : R ≠ 0) (Z ell B : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hlower : ∀ Q ∈ P, Z^ell ≤ (Ideal.absNorm Q : ℝ))
    (hupper : (Ideal.absNorm R : ℝ) ≤ Z^B) (hsize : 2*(B/ell) ≤ P.card) :
    (P.card : ℝ)/2 ≤ ((elementPool P).filter (fun p => ¬Ideal.span {p} ∣ R)).card := by
  rw [elementPool_eligible P hp hbad R,elementPool_card (eligiblePool P R)
    (fun Q hQ => hp Q (Finset.mem_filter.mp hQ).1)
    (fun Q hQ => hbad Q (Finset.mem_filter.mp hQ).1)]
  exact eligiblePool_half P hp R hR Z ell B hZ hell hlower hupper hsize

theorem ideal_pool_polynomial_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (P : Finset (Ideal O)) (hne : P.Nonempty)
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (h : O) (hh : ∀ Q ∈ P, ¬Q ∣ Ideal.span {h}) :
    ‖CenteredMomentGaussEnergy.gaussPolynomial S a ha c h‖^2 ≤ (4/(P.card : ℝ))*
      ∑ p ∈ elementPool P,
        (‖CenteredMomentGaussEnergy.gaussPolynomial S a ha c (p^6*h)‖^2 +
        ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 1 h‖^2 +
        ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 6 h‖^2 +
        ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 7 h‖^2) := by
  have he := polynomial_pool_bound S a ha c (elementPool P) (Finset.Nonempty.image hne _)
    (fun p hpm => (elementPool_data P hp hbad p hpm).1)
    (fun p hpm => (elementPool_data P hp hbad p hpm).2.2.2.1)
    (fun p hpm => (elementPool_data P hp hbad p hpm).2.2.2.2.1)
    (fun p hpm => (elementPool_data P hp hbad p hpm).2.2.2.2.2) h (by
      intro p hpm hph
      apply hh (Ideal.span {p}) (elementPool_data P hp hbad p hpm).2.1
      exact Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr hph))
  simpa only [elementPool_card P hp hbad] using he

end SevenEighths.CenteredMomentPrimeElements

end

end OAI
end OAIOriginalModule1964

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationEnergy
Source SHA256: 805dd6717ecfea9de33eb2398e2b1d7f0504dddd379f899bf73e485b136f0c59
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1965


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationCount
local notation "O" => ActualEisensteinCubic.O

def eligiblePairs (rows P : Finset O) (allow : O → O → Prop) : Finset (O × O) :=
  (rows.product P).filter (fun x => allow x.1 x.2)

def outputRow (x : O × O) : O := x.2^6*x.1

theorem outputRow_norm (x : O × O) (Z M L : ℝ) (hZ : 0 < Z)
    (hh : (Ideal.absNorm (Ideal.span {x.1}) : ℝ) ≤ Z^M)
    (hp : (Ideal.absNorm (Ideal.span {x.2}) : ℝ) ≤ Z^L) :
    (Ideal.absNorm (Ideal.span {outputRow x}) : ℝ) ≤ Z^(M+6*L) := by
  calc
    _ = (Ideal.absNorm (Ideal.span {x.2}) : ℝ)^6 *
        (Ideal.absNorm (Ideal.span {x.1}) : ℝ) := by
      simp only [outputRow,← Ideal.span_singleton_mul_span_singleton,
        ← Ideal.span_singleton_pow,map_mul,map_pow,Nat.cast_mul,Nat.cast_pow]
    _ ≤ (Z^L)^6 * Z^M := mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hp 6) hh
      (Nat.cast_nonneg _) (by positivity)
    _ = Z^(M+6*L) := by
      rw [← Real.rpow_mul_natCast hZ.le,← Real.rpow_add hZ]
      congr 1
      ring

theorem amplified_energy_pushforward (rows P : Finset O) (allow : O → O → Prop)
    (hrows : ∀ h ∈ rows, h ≠ 0) (hp : ∀ p ∈ P, Prime p)
    (hprimary : ∀ p ∈ P, ConcretePrimeRowBridge.goodLambda^2 ∣ p-1)
    (Z ell M L : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hpl : ∀ p ∈ P, Z^ell ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ))
    (hpu : ∀ p ∈ P, (Ideal.absNorm (Ideal.span {p}) : ℝ) ≤ Z^L)
    (hhu : ∀ h ∈ rows, (Ideal.absNorm (Ideal.span {h}) : ℝ) ≤ Z^M)
    (H : O → ℂ) :
    (∑ x ∈ eligiblePairs rows P allow, ‖H (outputRow x)‖^2) ≤
      ((M+6*L)/ell)*∑ y ∈ (eligiblePairs rows P allow).image outputRow, ‖H y‖^2 := by
  apply positive_pushforward_bound _ outputRow (fun y => ‖H y‖^2) _ (fun _ _ => sq_nonneg _)
  intro y hy
  obtain ⟨x,hx,hxy⟩ := Finset.mem_image.mp hy
  have hxm := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
  have hy0 : y ≠ 0 := by
    rw [← hxy]
    exact mul_ne_zero (pow_ne_zero _ (hp x.2 hxm.2).ne_zero) (hrows x.1 hxm.1)
  apply amplified_row_fiber_count _ y hy0
  · intro z hz
    exact hp z.2 (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).2
  · intro z hz
    exact hprimary z.2 (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).2
  · intro z hz
    exact (Finset.mem_filter.mp hz).2
  · exact hZ
  · exact hell
  · intro z hz
    exact hpl z.2 (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).2
  · rw [← hxy]
    exact outputRow_norm x Z M L (zero_lt_one.trans hZ) (hhu x.1 hxm.1) (hpu x.2 hxm.2)

theorem sum_eligiblePairs (rows P : Finset O) (allow : O → O → Prop) (f : O → O → ℝ) :
    (∑ h ∈ rows, ∑ p ∈ P.filter (allow h), f h p) =
      ∑ x ∈ eligiblePairs rows P allow, f x.1 x.2 := by
  simp only [eligiblePairs,Finset.sum_filter]
  exact (Finset.sum_product rows P (fun x : O × O => if allow x.1 x.2 then f x.1 x.2 else 0)).symm

def errorEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) (h p : O) : ℝ :=
  ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 1 h‖^2 +
  ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 6 h‖^2 +
  ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 7 h‖^2

theorem gauss_energy_amplification {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (rows P : Finset O) (allow : O → O → Prop)
    (hrows : ∀ h ∈ rows, h ≠ 0) (hp : ∀ p ∈ P, Prime p)
    (hs : ∀ p ∈ P, Supported (Ideal.span {p}))
    (hg : ∀ p ∈ P, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p})
    (hc : ∀ p ∈ P, ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : ∀ p ∈ P, ConcretePrimeRowBridge.goodLambda^2 ∣ p-1)
    (hallow : ∀ h ∈ rows, ∀ p ∈ P, allow h p → ¬p ∣ h)
    (κ : ℝ) (hκ : 0 < κ) (hsize : ∀ h ∈ rows, κ ≤ (P.filter (allow h)).card)
    (Z ell M L : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hpl : ∀ p ∈ P, Z^ell ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ))
    (hpu : ∀ p ∈ P, (Ideal.absNorm (Ideal.span {p}) : ℝ) ≤ Z^L)
    (hhu : ∀ h ∈ rows, (Ideal.absNorm (Ideal.span {h}) : ℝ) ≤ Z^M) :
    (∑ h ∈ rows, ‖gaussPolynomial S a ha c h‖^2) ≤ (4/κ)*
      (((M+6*L)/ell)*(∑ y ∈ (eligiblePairs rows P allow).image outputRow,
        ‖gaussPolynomial S a ha c y‖^2) +
        ∑ x ∈ eligiblePairs rows P allow, errorEnergy S a ha c x.1 x.2) := by
  have hj : (∑ h ∈ rows, ‖gaussPolynomial S a ha c h‖^2) ≤
      (4/κ)*∑ x ∈ eligiblePairs rows P allow,
        (‖gaussPolynomial S a ha c (outputRow x)‖^2 + errorEnergy S a ha c x.1 x.2) := by
    change _ ≤ (4/κ)*∑ x ∈ eligiblePairs rows P allow,
      (‖gaussPolynomial S a ha c (x.2^6*x.1)‖^2 + errorEnergy S a ha c x.1 x.2)
    rw [← sum_eligiblePairs rows P allow (fun h p =>
      ‖gaussPolynomial S a ha c (p^6*h)‖^2 + errorEnergy S a ha c h p),Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h hh
    have hn : (P.filter (allow h)).Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp (hκ.trans_le (hsize h hh)))
    have hb := polynomial_pool_bound S a ha c (P.filter (allow h)) hn
      (fun p hpP => hp p (Finset.mem_filter.mp hpP).1)
      (fun p hpP => hs p (Finset.mem_filter.mp hpP).1)
      (fun p hpP => hg p (Finset.mem_filter.mp hpP).1)
      (fun p hpP => hc p (Finset.mem_filter.mp hpP).1) h
      (fun p hpP => hallow h hh p (Finset.mem_filter.mp hpP).1 (Finset.mem_filter.mp hpP).2)
    calc
      _ ≤ (4 / ((P.filter (allow h)).card : ℝ)) *
          ∑ p ∈ P.filter (allow h), (‖gaussPolynomial S a ha c (p^6*h)‖^2 + errorEnergy S a ha c h p) := by
        simpa only [errorEnergy,add_assoc] using hb
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by norm_num) hκ (hsize h hh))
        (Finset.sum_nonneg (fun p _ => add_nonneg (sq_nonneg _) (by unfold errorEnergy; positivity)))
  have hf := amplified_energy_pushforward rows P allow hrows hp hprimary Z ell M L hZ hell
    hpl hpu hhu (gaussPolynomial S a ha c)
  apply hj.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.sum_add_distrib]
  exact add_le_add hf le_rfl

end SevenEighths.CenteredMomentAmplificationEnergy

end

end OAI
end OAIOriginalModule1965

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationShortening
Source SHA256: 690b6d41b0f4b27f114990708e67eebb81725c20e7e51474065932900a479d77
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1966



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationShortening
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentGaussEnergy CenteredMomentSupportedCorrelation CenteredMomentUnequal
open CenteredMomentAmplification CenteredMomentAmplificationLocal CenteredMomentAmplificationGlobal
open ProbePhysical
local notation "O" => ActualEisensteinCubic.O

def residualCharacter (p : O) (k : ℕ) (u : O) : ℂ :=
  sexticReciprocityPhase p u ^ k * idealRowHom u (Ideal.span {p}) ^ (2*k)

theorem crossFactor_primary (p u : O) (k : ℕ)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hpp : goodLambda^2 ∣ p-1) (hup : goodLambda^2 ∣ u-1) :
    idealRowHom u (Ideal.span {p^k}) * idealRowHom (p^k) (Ideal.span {u}) =
      residualCharacter p k u := by
  rw [← Ideal.span_singleton_pow,map_pow,idealRowHom_argument_pow p k _ hu,
    idealRowHom_primary_reciprocity u p hup hpp hu hp,
    sexticReciprocityPhase_symm u p,mul_pow]
  unfold residualCharacter
  rw [show 2*k=k+k by omega,pow_add]
  ring

theorem gauss_primary_power_product (p u : O) (k : ℕ)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hpp : goodLambda^2 ∣ p-1) (hup : goodLambda^2 ∣ u-1)
    (hcop : IsCoprime p u) (h : O) :
    sexticGauss (p^k*u) (mul_ne_zero (pow_ne_zero _ (supportedElement_ne_zero p hp))
      (supportedElement_ne_zero u hu)) h =
      residualCharacter p k u * sexticGauss (p^k) (pow_ne_zero _ (supportedElement_ne_zero p hp)) h *
        sexticGauss u (supportedElement_ne_zero u hu) h := by
  rw [sexticGauss_coprime_product (p^k) u (supported_power p hp k) hu hcop.pow_left,
    crossFactor_primary p u k hp hu hpp hup]

theorem residualCharacter_six (p u : O) (hp : Supported (Ideal.span {p})) :
    residualCharacter p 6 u = sexticReciprocityPhase p u ^ 6 *
      coprimalityMask u p := by
  unfold residualCharacter
  norm_num only
  rw [twelfth_power_mask p hp u]

def primeRoot (p : O) (k : ℕ) : ℂ :=
  (Real.sqrt ((Ideal.absNorm (Ideal.span {p}) : ℝ)^k) : ℂ)

theorem primeRoot_sq (p : O) (k : ℕ) :
    primeRoot p k * primeRoot p k = (Ideal.absNorm (Ideal.span {p}) : ℂ)^k := by
  rw [primeRoot,← Complex.ofReal_mul,Real.mul_self_sqrt (by positivity),Complex.ofReal_pow,
    Complex.ofReal_natCast]

theorem modulusRoot_product (p u : O) (k : ℕ) :
    (Real.sqrt (Ideal.absNorm (Ideal.span {p^k*u}) : ℝ) : ℂ) =
      primeRoot p k * (Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ) : ℂ) := by
  simp only [← Ideal.span_singleton_mul_span_singleton,← Ideal.span_singleton_pow,
    map_mul,map_pow,Nat.cast_mul,Nat.cast_pow,Real.sqrt_mul (by positivity :
      0 ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ)^k),Complex.ofReal_mul,primeRoot]

theorem gaussRow_shortening (p u : O) (k : ℕ)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hpp : goodLambda^2 ∣ p-1) (hup : goodLambda^2 ∣ u-1)
    (hcop : IsCoprime p u) (h : O) :
    gaussRow (p^k*u) (supported_mul_elements _ _ (supported_power p hp k) hu) h =
      residualCharacter p k u *
        (sexticGauss (p^k) (pow_ne_zero _ (supportedElement_ne_zero p hp)) h / primeRoot p k) *
          gaussRow u hu h := by
  unfold gaussRow
  rw [gauss_primary_power_product p u k hp hu hpp hup hcop h,modulusRoot_product]
  ring

theorem central_error_shortening (p u : O) (n : ℕ)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hpp : goodLambda^2 ∣ p-1) (hup : goodLambda^2 ∣ u-1)
    (hcop : IsCoprime p u) (h : O) :
    (gaussRow (p^(n+1)*u) (supported_mul_elements _ _ (supported_power p hp (n+1)) hu) h -
      gaussRow (p^(n+1)*u) (supported_mul_elements _ _ (supported_power p hp (n+1)) hu) (p^6*h)) /
        primeRoot p (n+1) =
      (centralLocal p (supportedElement_ne_zero p hp) n h -
        centralLocal p (supportedElement_ne_zero p hp) n (p^6*h)) *
          (residualCharacter p (n+1) u * gaussRow u hu h) := by
  rw [gaussRow_shortening p u (n+1) hp hu hpp hup hcop,
    gaussRow_shortening p u (n+1) hp hu hpp hup hcop]
  have hinv : gaussRow u hu (p^6*h) = gaussRow u hu h := by
    unfold gaussRow
    rw [gauss_sixth_frequency u hu p h hcop]
  rw [hinv]
  unfold centralLocal
  rw [← primeRoot_sq p (n+1)]
  ring

theorem supported_phase_sq (p u : O) (hp : Supported (Ideal.span {p}))
    (hu : Supported (Ideal.span {u})) : sexticReciprocityPhase p u ^ 2 = 1 := by
  unfold sexticReciprocityPhase
  exact_mod_cast QuadraticAllOddCRT.quadraticRaySign_sq _ _
    (supported_residue_odd p hp) (supported_residue_odd u hu)

theorem residualCharacter_moving (p u : O) (k : ℕ)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hpp : goodLambda^2 ∣ p-1) (hup : goodLambda^2 ∣ u-1) :
    residualCharacter p k u = sexticReciprocityPhase p u ^ k *
      idealRowHom (p^(2*k)) (Ideal.span {u}) := by
  rw [residualCharacter,idealRowHom_argument_pow p (2*k) _ hu,
    idealRowHom_primary_reciprocity p u hpp hup hp hu,mul_pow,
    pow_mul,supported_phase_sq p u hp hu,one_pow,one_mul]

def errorScalar (p : O) (hp : p ≠ 0) (n : ℕ) (h : O) : ℂ :=
  centralLocal p hp n h - centralLocal p hp n (p^6*h)

theorem centralLocal_unit_zero (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ) (hn : n ≠ 0)
    (h : O) (hph : ¬p ∣ h) : centralLocal p hp.ne_zero n h = 0 := by
  unfold centralLocal
  rw [← mul_one h,sexticGauss_unit_scale _ (supported_power p hs (n+1)) h 1
    ((hp.irreducible.coprime_iff_not_dvd.mpr hph).symm.pow_right),
    gauss_prime_power_one p hp hg hc]
  simp only [hn,ite_false,mul_zero,zero_div]

theorem centralLocal_six_zero (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ) (hn5 : n ≠ 5) (hn6 : n ≠ 6)
    (h : O) (hph : ¬p ∣ h) : centralLocal p hp.ne_zero n (p^6*h) = 0 := by
  unfold centralLocal
  rw [mul_comm (p^6) h,sexticGauss_unit_scale _ (supported_power p hs (n+1)) h (p^6)
    ((hp.irreducible.coprime_iff_not_dvd.mpr hph).symm.pow_right),
    gauss_prime_power_six p hp hg hc]
  simp only [hn5,hn6,ite_false,mul_zero,zero_div]

theorem errorScalar_norms (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (h : O) (hph : ¬p ∣ h) :
    ‖errorScalar p hp.ne_zero 0 h‖^2 = (Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹ ∧
    ‖errorScalar p hp.ne_zero 5 h‖^2 = (1-(Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹)^2 ∧
    ‖errorScalar p hp.ne_zero 6 h‖^2 = (Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹ := by
  unfold errorScalar
  rw [centralLocal_six_zero p hp hs hg hc 0 (by decide) (by decide) h hph,
    centralLocal_unit_zero p hp hs hg hc 5 (by decide) h hph,
    centralLocal_unit_zero p hp hs hg hc 6 (by decide) h hph,
    sub_zero,zero_sub,zero_sub,norm_neg,norm_neg,mul_comm (p^6) h]
  exact ⟨centralLocal_one_norm_sq p hp hs hg hc h hph,
    centralLocal_six_norm_sq p hp hs hg hc h hph,
    centralLocal_seven_norm_sq p hp hs hg hc h hph⟩

theorem error_polynomial_shortening {α : Type*} (S : Finset α)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (n : ℕ) (u : α → O)
    (hu : ∀ i, Supported (Ideal.span {u i})) (hup : ∀ i, goodLambda^2 ∣ u i-1)
    (hcop : ∀ i, IsCoprime p (u i)) (c : α → ℂ) (h : O) :
    amplificationError S (fun i => p^(n+1)*u i)
      (fun i => supported_mul_elements _ _ (supported_power p hs (n+1)) (hu i))
      (fun i => c i / primeRoot p (n+1)) (fun i => multiplicity p (p^(n+1)*u i)) p (n+1) h =
      errorScalar p hp.ne_zero n h *
        gaussPolynomial S u hu (fun i => c i * residualCharacter p (n+1) (u i)) h := by
  unfold amplificationError gaussPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hv : multiplicity p (p^(n+1)*u i) = n+1 := by
    rw [multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp
      (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (supportedElement_ne_zero _ (hu i)))),
      multiplicity_pow_self_of_prime hp,
      multiplicity_eq_zero_of_not_dvd (hp.irreducible.coprime_iff_not_dvd.mp (hcop i)),add_zero]
  dsimp only
  simp only [ite_eq_left hv]
  have he := central_error_shortening p (u i) n hs (hu i) hpp (hup i) (hcop i) h
  change _ = errorScalar p hp.ne_zero n h *
    (c i * residualCharacter p (n+1) (u i) * gaussRow (u i) (hu i) h)
  calc
    _ = c i * ((gaussRow (p^(n+1)*u i)
        (supported_mul_elements _ _ (supported_power p hs (n+1)) (hu i)) h -
      gaussRow (p^(n+1)*u i)
        (supported_mul_elements _ _ (supported_power p hs (n+1)) (hu i)) (p^6*h)) /
        primeRoot p (n+1)) := by ring
    _ = _ := by rw [he]; unfold errorScalar; ring

end SevenEighths.CenteredMomentAmplificationShortening

end

end OAI
end OAIOriginalModule1966

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationAllocation
Source SHA256: 6d5afba9b28fe2aac2e73c822cc868807b5bad99dc2826b0b49cac6064550c38
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1967


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationAllocation
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

theorem primaryGenerator_power (I : Ideal O) (n : ℕ) :
    primaryGenerator (I^n) = primaryGenerator I ^ n := map_pow primaryGeneratorHom I n

theorem primeRemainder_primary (p : O) (hp : Prime p) (hpp : goodLambda^2 ∣ p-1)
    (a : O) (ha : Supported (Ideal.span {a})) (hpa : goodLambda^2 ∣ a-1) :
    goodLambda^2 ∣ primeRemainder p hp a (supported_element_ne_zero a ha)-1 := by
  let r := primeRemainder p hp a (supported_element_ne_zero a ha)
  have hr := primeRemainder_supported p hp a ha
  have hgen := supported_primaryGenerator_ne_zero (Ideal.span {r}) hr
  have he : a = p^(multiplicity p a)*primaryGenerator (Ideal.span {r}) := by
    calc
      a = primaryGenerator (Ideal.span {a}) := (primaryGenerator_span a
        (supported_element_ne_zero a ha) hpa).symm
      _ = _ := by
        conv_lhs => rw [(primeRemainder_spec p hp a (supported_element_ne_zero a ha)).1]
        rw [← Ideal.span_singleton_mul_span_singleton,primaryGenerator_mul,
          ← Ideal.span_singleton_pow,primaryGenerator_power,primaryGenerator_span p hp.ne_zero hpp]
  have hre : r = primaryGenerator (Ideal.span {r}) := by
    apply mul_left_cancel₀ (pow_ne_zero (multiplicity p a) hp.ne_zero)
    exact (primeRemainder_spec p hp a (supported_element_ne_zero a ha)).1.symm.trans he
  change goodLambda^2 ∣ r-1
  rw [hre]
  exact (primaryGenerator_spec _ hgen).2

theorem plain_product_valuation (p : O) (hp : Prime p) (q a b : O)
    (hq : q ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hpq : ¬p ∣ q) :
    multiplicity p (q*a*b) = multiplicity p a + multiplicity p b := by
  rw [multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp (mul_ne_zero (mul_ne_zero hq ha) hb)),
    multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp (mul_ne_zero hq ha)),
    multiplicity_eq_zero_of_not_dvd hpq,zero_add]

theorem plain_product_remainder (p : O) (hp : Prime p) (q a b : O)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    q*a*b = p^(multiplicity p a + multiplicity p b) *
      (q*primeRemainder p hp a ha*primeRemainder p hp b hb) := by
  conv_lhs => rw [(primeRemainder_spec p hp a ha).1,(primeRemainder_spec p hp b hb).1]
  rw [pow_add]
  ring

theorem split_plain_valuation {α β : Type*} (S : Finset α) (T : Finset β)
    (v : α → ℕ) (w : β → ℕ) (k : ℕ) (c : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, if v i + w j = k then c i j else 0) =
      ∑ r ∈ Finset.range (k+1), ∑ i ∈ S, ∑ j ∈ T,
        if v i = r ∧ w j = k-r then c i j else 0 := by
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hk : v i + w j = k
  · rw [ite_eq_left hk,Finset.sum_eq_single (v i)]
    · simp only [true_and]
      rw [ite_eq_left (by omega)]
    · intro r hr hne
      rw [ite_eq_right (fun h => hne h.1.symm)]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · rw [ite_eq_right hk]
    symm
    apply Finset.sum_eq_zero
    intro r hr
    rw [ite_eq_right]
    intro h
    exact hk (by have hh := Finset.mem_range.mp hr; omega)

theorem split_actual_plain_product {α β : Type*} (S : Finset α) (T : Finset β)
    (p : O) (hp : Prime p) (q : O) (hq : q ≠ 0) (hpq : ¬p ∣ q)
    (a : α → O) (ha : ∀ i, a i ≠ 0) (b : β → O) (hb : ∀ j, b j ≠ 0)
    (k : ℕ) (c : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, if multiplicity p (q*a i*b j) = k then c i j else 0) =
      ∑ r ∈ Finset.range (k+1), ∑ i ∈ S, ∑ j ∈ T,
        if multiplicity p (a i) = r ∧ multiplicity p (b j) = k-r then c i j else 0 := by
  simp_rw [plain_product_valuation p hp q _ _ hq (ha _) (hb _) hpq]
  exact split_plain_valuation S T _ _ k c

theorem error_allocation_count (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    (Finset.range (k+1)).card ≤ 8 := by
  rw [Finset.card_range]
  rcases hk with rfl | rfl | rfl <;> omega

end SevenEighths.CenteredMomentAmplificationAllocation

end

end OAI
end OAIOriginalModule1967

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationRectangle
Source SHA256: 0b81edbeea72cc93f83ce462bd1ddea5d8c3441246d48b9ad9ac34b28809be8d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1968


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentAmplificationRectangle
open CenteredMomentRectangle CenteredMomentExtraction CenteredMomentAmplificationShortening
local notation "O" => ActualEisensteinCubic.O

theorem centralRoot_extract (p : O) (hp : p ≠ 0) (k : ℕ) (T : ℝ) (hT : 0 < T) :
    (Real.sqrt T : ℂ)⁻¹ = (primeRoot p k)⁻¹ *
      (Real.sqrt (T / (Ideal.absNorm (Ideal.span {p}) : ℝ)^k) : ℂ)⁻¹ := by
  have hN : 0 < (Ideal.absNorm (Ideal.span {p}) : ℝ) := Nat.cast_pos.mpr
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp)))
  have hroot : Real.sqrt T = Real.sqrt ((Ideal.absNorm (Ideal.span {p}) : ℝ)^k) *
      Real.sqrt (T / (Ideal.absNorm (Ideal.span {p}) : ℝ)^k) := by
    rw [← Real.sqrt_mul (pow_nonneg hN.le k)]
    congr 1
    field_simp
  rw [hroot,Complex.ofReal_mul,mul_inv,primeRoot]

theorem centered_coefficient_prime_extract (p : O) (hp : p ≠ 0)
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ T : ℝ) (hT : 0 < T)
    (Q I J : Ideal O) (k j : ℕ) (hj : j ≤ k) :
    (Real.sqrt T : ℂ)⁻¹ *
      (idealWeight c χ R t (Q * ((Ideal.span {p})^j*I) * ((Ideal.span {p})^(k-j)*J)) *
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂
          ((Ideal.span {p})^j*I) ((Ideal.span {p})^(k-j)*J)) =
      (idealWeight c χ R t ((Ideal.span {p})^k) / primeRoot p k) *
        ((Real.sqrt (T/(Ideal.absNorm (Ideal.span {p}) : ℝ)^k) : ℂ)⁻¹ *
          (idealWeight c χ R t (Q*I*J) *
            idealRectangle W₁ W₂
              (X₁/(Ideal.absNorm (Ideal.span {p}) : ℝ)^j)
              (X₂/(Ideal.absNorm (Ideal.span {p}) : ℝ)^(k-j))
              (Y₁/(Ideal.absNorm (Ideal.span {p}) : ℝ)^j)
              (Y₂/(Ideal.absNorm (Ideal.span {p}) : ℝ)^(k-j)) I J)) := by
  rw [extracted_rectangle_coefficient,centralRoot_extract p hp k T hT]
  have hprod : Q*(Ideal.span {p})^j*(Ideal.span {p})^(k-j) = Q*(Ideal.span {p})^k := by
    rw [mul_assoc,← pow_add,Nat.add_sub_of_le hj]
  rw [hprod]
  simp only [idealWeight_mul,map_pow,Nat.cast_pow]
  ring

theorem centered_product_prime_extract (p : O) (k j : ℕ) (hj : j ≤ k)
    (X₁ X₂ Y₁ Y₂ T : ℝ) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) :
    (X₁/(Ideal.absNorm (Ideal.span {p}) : ℝ)^j) *
      (X₂/(Ideal.absNorm (Ideal.span {p}) : ℝ)^(k-j)) =
        T/(Ideal.absNorm (Ideal.span {p}) : ℝ)^k ∧
    (Y₁/(Ideal.absNorm (Ideal.span {p}) : ℝ)^j) *
      (Y₂/(Ideal.absNorm (Ideal.span {p}) : ℝ)^(k-j)) =
        T/(Ideal.absNorm (Ideal.span {p}) : ℝ)^k := by
  simp only [div_mul_div_comm,← pow_add,Nat.add_sub_of_le hj,hX,hY,and_self]

end SevenEighths.CenteredMomentAmplificationRectangle

end

end OAI
end OAIOriginalModule1968

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationMask
Source SHA256: 4c5690d301bc881610a7669d54011a1b78f7f53521b9fc6decebf7b0a74d484b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1969


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentAmplificationMask
open CenteredMomentRectangle CenteredMomentAmplificationRectangle CenteredMomentAmplificationShortening
local notation "O" => ActualEisensteinCubic.O

theorem whole_product_divisibility (p : O) (s Q I J : Ideal O)
    (hcop : IsCoprime s (Ideal.span {p})) (k j : ℕ) (hj : j ≤ k) :
    s∣Q*((Ideal.span {p})^j*I)*((Ideal.span {p})^(k-j)*J) ↔ s∣Q*I*J := by
  have he : Q*((Ideal.span {p})^j*I)*((Ideal.span {p})^(k-j)*J) =
      (Ideal.span {p})^k*(Q*I*J) := by
    calc
      _ = ((Ideal.span {p})^j*(Ideal.span {p})^(k-j))*(Q*I*J) := by ring
      _ = _ := by rw [← pow_add,Nat.add_sub_of_le hj]
  rw [he]
  exact (hcop.pow_right (n := k)).dvd_mul_left_iff

theorem masked_centered_coefficient_prime_extract (p : O) (hp : p ≠ 0)
    (s : Ideal O) (hcop : IsCoprime s (Ideal.span {p}))
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ T : ℝ) (hT : 0 < T)
    (Q I J : Ideal O) (k j : ℕ) (hj : j ≤ k) :
    (Real.sqrt T:ℂ)⁻¹ *
      (idealWeight c χ R t (Q*((Ideal.span {p})^j*I)*((Ideal.span {p})^(k-j)*J))*
        CenteredMomentRectangle.idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂
          ((Ideal.span {p})^j*I) ((Ideal.span {p})^(k-j)*J)) *
      (if s∣Q*((Ideal.span {p})^j*I)*((Ideal.span {p})^(k-j)*J) then (1:ℂ) else 0) =
      (idealWeight c χ R t ((Ideal.span {p})^k)/primeRoot p k)*
        ((Real.sqrt (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^k):ℂ)⁻¹ *
          (idealWeight c χ R t (Q*I*J)*
            CenteredMomentRectangle.idealRectangle W₁ W₂
              (X₁/(Ideal.absNorm (Ideal.span {p}):ℝ)^j)
              (X₂/(Ideal.absNorm (Ideal.span {p}):ℝ)^(k-j))
              (Y₁/(Ideal.absNorm (Ideal.span {p}):ℝ)^j)
              (Y₂/(Ideal.absNorm (Ideal.span {p}):ℝ)^(k-j)) I J)*
          (if s∣Q*I*J then (1:ℂ) else 0)) := by
  simp only [whole_product_divisibility p s Q I J hcop k j hj]
  rw [centered_coefficient_prime_extract p hp c χ R t W₁ W₂ X₁ X₂ Y₁ Y₂ T hT Q I J k j hj]
  ring

end SevenEighths.CenteredMomentAmplificationMask

end

end OAI
end OAIOriginalModule1969

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationSource
Source SHA256: 2d8df260bd82004ee3f367c7ee1e0cc7c9f36e606ee2b2b37eb1dd6b2fdaf831
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1970



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationSource
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationAllocation CenteredMomentGaussEnergy
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentLiveDomain
local notation "O" => ActualEisensteinCubic.O

 theorem primeRoot_ne_zero (p : O) (hp : p ≠ 0) (k : ℕ) : primeRoot p k ≠ 0 := by
  unfold primeRoot
  apply Complex.ofReal_ne_zero.mpr
  apply Real.sqrt_ne_zero'.mpr
  apply pow_pos
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hp))

theorem original_error_shortening {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hap : ∀ i, goodLambda^2 ∣ a i-1) (c : α → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (n : ℕ) (h : O) :
    amplificationError S a ha c (fun i => multiplicity p (a i)) p (n+1) h =
      (primeRoot p (n+1)*errorScalar p hp.ne_zero n h)*
        gaussPolynomial S
          (fun i => primeRemainder p hp (a i) (supported_element_ne_zero _ (ha i)))
          (fun i => primeRemainder_supported p hp (a i) (ha i))
          (fun i => if multiplicity p (a i)=n+1 then
            c i*residualCharacter p (n+1)
              (primeRemainder p hp (a i) (supported_element_ne_zero _ (ha i))) else 0) h := by
  unfold amplificationError gaussPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  by_cases hv : multiplicity p (a i)=n+1
  · simp only [ite_eq_left hv]
    let r := primeRemainder p hp (a i) (supported_element_ne_zero _ (ha i))
    have hr := primeRemainder_supported p hp (a i) (ha i)
    have hcop : IsCoprime p r := hp.irreducible.coprime_iff_not_dvd.mpr
      (primeRemainder_spec p hp (a i) (supported_element_ne_zero _ (ha i))).2
    have hf : a i=p^(n+1)*r := by
      simpa only [hv] using (primeRemainder_spec p hp (a i) (supported_element_ne_zero _ (ha i))).1
    have he := central_error_shortening p r n hs hr hpp
      (primeRemainder_primary p hp hpp (a i) (ha i) (hap i)) hcop h
    have he' : gaussRow (a i) (ha i) h-gaussRow (a i) (ha i) (p^6*h) =
        primeRoot p (n+1)*(errorScalar p hp.ne_zero n h *
          (residualCharacter p (n+1) r*gaussRow r hr h)) := by
      have hh := (div_eq_iff (primeRoot_ne_zero p hp.ne_zero (n+1))).mp he
      simp only [hf,errorScalar]
      exact hh.trans (by ring)
    rw [he']
    ring
  · simp only [ite_eq_right hv,zero_mul,mul_zero]

theorem source_error_shortening (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (n : ℕ) (h : O) :
    amplificationError Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => c I)
      (fun I => multiplicity p (sourceGenerator S I)) p (n+1) h =
      (primeRoot p (n+1)*errorScalar p hp.ne_zero n h)*
        gaussPolynomial Finset.univ
          (fun I : supportedColumns S => primeRemainder p hp (sourceGenerator S I)
            (supported_element_ne_zero _ (sourceGenerator_supported S I)))
          (fun I => primeRemainder_supported p hp (sourceGenerator S I) (sourceGenerator_supported S I))
          (fun I => if multiplicity p (sourceGenerator S I)=n+1 then
            c I*residualCharacter p (n+1)
              (primeRemainder p hp (sourceGenerator S I)
                (supported_element_ne_zero _ (sourceGenerator_supported S I))) else 0) h := by
  apply original_error_shortening _ _ _ _ _ p hp hs hpp n h
  intro I
  exact (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I
    (Finset.mem_filter.mp I.property).2)).2

end SevenEighths.CenteredMomentAmplificationSource

end

end OAI
end OAIOriginalModule1970

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationSourceDomain
Source SHA256: 1937ee17f56e794f2035249a73318cd614a980dcbc18cc77203a7efe9bc7d8c9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1971


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationSourceDomain
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationAllocation CenteredMomentGaussEnergy
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentLiveDomain
local notation "O" => ActualEisensteinCubic.O

def residualIdeal (p : O) (hp : Prime p) (I : Ideal O) : Ideal O :=
  if hI : Supported I then Ideal.span {primeRemainder p hp (primaryGenerator I)
    (supported_primaryGenerator_ne_zero I hI)} else 0

theorem residualIdeal_supported (p : O) (hp : Prime p) (I : Ideal O) (hI : Supported I) :
    Supported (residualIdeal p hp I) := by
  rw [residualIdeal,dite_eq_left hI]
  exact primeRemainder_supported p hp (primaryGenerator I)
    (by rw [primary_span_supported I hI];exact hI)

theorem residualIdeal_generator (p : O) (hp : Prime p) (hpp : goodLambda^2 ∣ p-1)
    (I : Ideal O) (hI : Supported I) :
    primaryGenerator (residualIdeal p hp I) =
      primeRemainder p hp (primaryGenerator I) (supported_primaryGenerator_ne_zero I hI) := by
  rw [residualIdeal,dite_eq_left hI]
  apply primaryGenerator_span
  · apply supported_element_ne_zero
    simpa only [residualIdeal,dite_eq_left hI] using residualIdeal_supported p hp I hI
  · exact primeRemainder_primary p hp hpp (primaryGenerator I)
      (by rw [primary_span_supported I hI];exact hI)
      (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).2

theorem residualIdeal_reconstruct (p : O) (hp : Prime p) (I : Ideal O) (hI : Supported I) :
    (Ideal.span {p})^(multiplicity p (primaryGenerator I))*residualIdeal p hp I=I := by
  rw [residualIdeal,dite_eq_left hI,Ideal.span_singleton_pow,
    Ideal.span_singleton_mul_span_singleton,
    ← (primeRemainder_spec p hp (primaryGenerator I) (supported_primaryGenerator_ne_zero I hI)).1]
  exact primary_span_supported I hI

def valuationColumns (S : Finset (Ideal O)) (p : O) (k : ℕ) : Finset (Ideal O) :=
  (supportedColumns S).filter (fun I => multiplicity p (primaryGenerator I)=k)

def residualColumns (S : Finset (Ideal O)) (p : O) (hp : Prime p) (k : ℕ) : Finset (Ideal O) :=
  (valuationColumns S p k).image (residualIdeal p hp)

theorem valuationColumns_supported (S : Finset (Ideal O)) (p : O) (k : ℕ)
    (I : Ideal O) (hI : I∈valuationColumns S p k) : Supported I :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2

theorem residualIdeal_injOn (S : Finset (Ideal O)) (p : O) (hp : Prime p) (k : ℕ) :
    Set.InjOn (residualIdeal p hp) (valuationColumns S p k) := by
  intro I hI J hJ he
  have hi := residualIdeal_reconstruct p hp I (valuationColumns_supported S p k I hI)
  have hj := residualIdeal_reconstruct p hp J (valuationColumns_supported S p k J hJ)
  rw [(Finset.mem_filter.mp hI).2] at hi
  rw [(Finset.mem_filter.mp hJ).2] at hj
  exact hi.symm.trans ((congrArg (fun x => (Ideal.span {p})^k*x) he).trans hj)

theorem residualColumns_supported (S : Finset (Ideal O)) (p : O) (hp : Prime p) (k : ℕ)
    (I : Ideal O) (hI : I∈residualColumns S p hp k) : Supported I := by
  obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
  exact residualIdeal_supported p hp J (valuationColumns_supported S p k J hJ)

theorem residual_column_sum (S : Finset (Ideal O)) (p : O) (hp : Prime p) (k : ℕ)
    (c f : Ideal O → ℂ) :
    (∑ I∈valuationColumns S p k,c I*f (residualIdeal p hp I))=
      ∑ I∈residualColumns S p hp k,c ((Ideal.span {p})^k*I)*f I := by
  rw [residualColumns,Finset.sum_image (residualIdeal_injOn S p hp k)]
  apply Finset.sum_congr rfl
  intro I hI
  have hi := residualIdeal_reconstruct p hp I (valuationColumns_supported S p k I hI)
  rw [(Finset.mem_filter.mp hI).2] at hi
  rw [hi]

end SevenEighths.CenteredMomentAmplificationSourceDomain

end

end OAI
end OAIOriginalModule1971

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationSourcePolynomial
Source SHA256: fbeb1b39ba5d85c9d17f4e7f28d343c2e923feeb4d5d59904843592746090e45
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1972


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationSourcePolynomial
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationSource CenteredMomentAmplificationSourceDomain
open CenteredMomentGaussEnergy CenteredMomentSupportedCorrelation
open CenteredMomentSourceRow CenteredMomentLiveDomain
local notation "O" => ActualEisensteinCubic.O

 theorem residual_primaryGaussRow (p : O) (hp : Prime p)
    (hpp : goodLambda^2 ∣ p-1) (I : Ideal O) (hI : Supported I) (h : O) :
    primaryGaussRow (residualIdeal p hp I) h=
      gaussRow (primeRemainder p hp (primaryGenerator I)
        (supported_primaryGenerator_ne_zero I hI))
        (primeRemainder_supported p hp (primaryGenerator I)
          (by rw [primary_span_supported I hI];exact hI)) h := by
  simp only [primaryGaussRow,dite_eq_left (residualIdeal_supported p hp I hI),
    residualIdeal_generator p hp hpp I hI]

 theorem supported_residualColumns (S : Finset (Ideal O)) (p : O) (hp : Prime p) (k : ℕ) :
    supportedColumns (residualColumns S p hp k)=residualColumns S p hp k := by
  apply Finset.filter_eq_self.mpr
  exact residualColumns_supported S p hp k

theorem remainder_polynomial (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hpp : goodLambda^2 ∣ p-1) (k : ℕ) (h : O) :
    gaussPolynomial Finset.univ
      (fun I : supportedColumns S => primeRemainder p hp (sourceGenerator S I)
        (supported_element_ne_zero _ (sourceGenerator_supported S I)))
      (fun I => primeRemainder_supported p hp (sourceGenerator S I) (sourceGenerator_supported S I))
      (fun I => if multiplicity p (sourceGenerator S I)=k then
        c I*residualCharacter p k
          (primeRemainder p hp (sourceGenerator S I)
            (supported_element_ne_zero _ (sourceGenerator_supported S I))) else 0) h =
      gaussPolynomial Finset.univ (sourceGenerator (residualColumns S p hp k))
        (sourceGenerator_supported (residualColumns S p hp k))
        (fun I : supportedColumns (residualColumns S p hp k) =>
          c ((Ideal.span {p})^k*I)*residualCharacter p k (primaryGenerator I)) h := by
  let f : Ideal O → ℂ := fun I => residualCharacter p k (primaryGenerator I)*primaryGaussRow I h
  have he := residual_column_sum S p hp k c f
  have hl : (∑ I∈valuationColumns S p k,c I*f (residualIdeal p hp I))=
      gaussPolynomial Finset.univ
        (fun I : supportedColumns S => primeRemainder p hp (sourceGenerator S I)
          (supported_element_ne_zero _ (sourceGenerator_supported S I)))
        (fun I => primeRemainder_supported p hp (sourceGenerator S I) (sourceGenerator_supported S I))
        (fun I => if multiplicity p (sourceGenerator S I)=k then
          c I*residualCharacter p k
            (primeRemainder p hp (sourceGenerator S I)
              (supported_element_ne_zero _ (sourceGenerator_supported S I))) else 0) h := by
    rw [valuationColumns,Finset.sum_filter]
    unfold gaussPolynomial
    rw [← Finset.sum_coe_sort (supportedColumns S)]
    apply Finset.sum_congr rfl
    intro I hI
    dsimp only [sourceGenerator]
    rw [show f (residualIdeal p hp I)=
      residualCharacter p k (primeRemainder p hp (primaryGenerator I)
        (supported_primaryGenerator_ne_zero I (Finset.mem_filter.mp I.property).2))*
      gaussRow (primeRemainder p hp (primaryGenerator I)
        (supported_primaryGenerator_ne_zero I (Finset.mem_filter.mp I.property).2))
        (primeRemainder_supported p hp (primaryGenerator I)
          (by rw [primary_span_supported I (Finset.mem_filter.mp I.property).2]
              exact (Finset.mem_filter.mp I.property).2)) h by
      dsimp only [f]
      rw [residualIdeal_generator p hp hpp I (Finset.mem_filter.mp I.property).2,
        residual_primaryGaussRow p hp hpp I (Finset.mem_filter.mp I.property).2 h]]
    split_ifs with hk <;> simp only [hk, ite_true, ite_false, zero_mul]
    ring
  refine hl.symm.trans (he.trans ?_)
  have hh := source_gaussPolynomial (residualColumns S p hp k)
    (fun I => c ((Ideal.span {p})^k*I)*residualCharacter p k (primaryGenerator I)) h
  refine Eq.trans ?_ hh.symm
  rw [supported_residualColumns]
  apply Finset.sum_congr rfl
  intro I hI
  dsimp only [f]
  ring

end SevenEighths.CenteredMomentAmplificationSourcePolynomial

end

end OAI
end OAIOriginalModule1972

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationSourcePool
Source SHA256: 47feb47f42de198798355f65c16e7af9fe4823ef2dd41ef77359a1be7b2ca1ae
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1973


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationSourcePool
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationAllocation CenteredMomentAmplificationSourceDomain
open CenteredMomentSourceRow CenteredMomentLiveDomain CenteredMomentFirstSectors
open CenteredMomentSupportedCorrelation CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

theorem residualIdeal_coprime (p : O) (hp : Prime p) (I : Ideal O) (hI : Supported I) :
    IsCoprime (Ideal.span {p}) (residualIdeal p hp I) := by
  rw [residualIdeal,dite_eq_left hI,Ideal.isCoprime_span_singleton_iff]
  exact hp.irreducible.coprime_iff_not_dvd.mpr
    (primeRemainder_spec p hp (primaryGenerator I) (supported_primaryGenerator_ne_zero I hI)).2

theorem residualColumns_eq (S : Finset (Ideal O)) (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (hpp : goodLambda^2 ∣ p-1) (k : ℕ) :
    residualColumns S p hp k=
      (supportedColumns (residualPool ((Ideal.span {p})^k) (pow_ne_zero k hs.1) S)).filter
        (fun I => IsCoprime (Ideal.span {p}) I) := by
  ext I
  constructor
  · intro hI
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    have hsJ := valuationColumns_supported S p k J hJ
    have hh := residualIdeal_reconstruct p hp J hsJ
    rw [(Finset.mem_filter.mp hJ).2] at hh
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_,residualIdeal_supported p hp J hsJ⟩,
      residualIdeal_coprime p hp J hsJ⟩
    apply (mem_residualPool _ _ S _).mpr
    rw [hh]
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hJ).1).1
  · intro hI
    obtain ⟨hI,hcop⟩ := Finset.mem_filter.mp hI
    obtain ⟨hpool,hsI⟩ := Finset.mem_filter.mp hI
    have hIS := (mem_residualPool _ _ S I).mp hpool
    let J := (Ideal.span {p})^k*I
    have hsJ : Supported J := by
      rw [supported_mul_iff]
      constructor
      · simpa only [← Ideal.span_singleton_pow] using supported_power p hs k
      · exact hsI
    have hgen : primaryGenerator J=p^k*primaryGenerator I := by
      rw [show J=(Ideal.span {p})^k*I from rfl,primaryGenerator_mul,primaryGenerator_power,
        primaryGenerator_span p hp.ne_zero hpp]
    have hcop' : IsCoprime p (primaryGenerator I) := by
      apply (Ideal.isCoprime_span_singleton_iff _ _).mp
      rw [primary_span_supported I hsI]
      exact hcop
    have hv : multiplicity p (primaryGenerator J)=k := by
      rw [hgen,multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp
        (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (supported_primaryGenerator_ne_zero I hsI))),
        multiplicity_pow_self_of_prime hp,
        multiplicity_eq_zero_of_not_dvd (hp.irreducible.coprime_iff_not_dvd.mp hcop'),add_zero]
    have hj : J∈valuationColumns S p k :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hIS,hsJ⟩,hv⟩
    refine Finset.mem_image.mpr ⟨J,hj,?_⟩
    apply mul_left_cancel₀ (pow_ne_zero k hs.1)
    have hh := residualIdeal_reconstruct p hp J hsJ
    simpa only [hv] using hh

end SevenEighths.CenteredMomentAmplificationSourcePool

end

end OAI
end OAIOriginalModule1973

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationSourceError
Source SHA256: 9a2e2ac7e52368def38b3f35a6cead2faedae8da3d6819fafbc1d32a8ee7075f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1974





namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationSourceError
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationSource CenteredMomentAmplificationSourceDomain
open CenteredMomentAmplificationSourcePolynomial CenteredMomentAmplificationSourcePool
open CenteredMomentAmplificationRectangle CenteredMomentGaussNormalization
open CenteredMomentGaussEnergy CenteredMomentSupportedCorrelation CenteredMomentSourceRow
local notation "O" => ActualEisensteinCubic.O

 theorem source_error_residual (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (n : ℕ) (h : O) :
    amplificationError Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => c I)
      (fun I => multiplicity p (sourceGenerator S I)) p (n+1) h =
      (primeRoot p (n+1)*errorScalar p hp.ne_zero n h)*
        gaussPolynomial Finset.univ (sourceGenerator (residualColumns S p hp (n+1)))
          (sourceGenerator_supported (residualColumns S p hp (n+1)))
          (fun I : supportedColumns (residualColumns S p hp (n+1)) =>
            c ((Ideal.span {p})^(n+1)*I)*residualCharacter p (n+1) (primaryGenerator I)) h := by
  rw [source_error_shortening S c p hp hs hpp n h,
    remainder_polynomial S c p hp hpp (n+1) h]

theorem normalized_source_error (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (n : ℕ) (h : O) (T : ℝ) (hT : 0<T) :
    amplificationError Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => (Real.sqrt T:ℂ)⁻¹*c I)
      (fun I => multiplicity p (sourceGenerator S I)) p (n+1) h =
      errorScalar p hp.ne_zero n h *
        gaussPolynomial Finset.univ (sourceGenerator (residualColumns S p hp (n+1)))
          (sourceGenerator_supported (residualColumns S p hp (n+1)))
          (fun I : supportedColumns (residualColumns S p hp (n+1)) =>
            (Real.sqrt (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)):ℂ)⁻¹*
            (c ((Ideal.span {p})^(n+1)*I)*residualCharacter p (n+1) (primaryGenerator I))) h := by
  rw [source_error_residual S (fun I => (Real.sqrt T:ℂ)⁻¹*c I) p hp hs hpp n h]
  simp only [mul_assoc,gaussPolynomial_const_mul]
  rw [centralRoot_extract p hp.ne_zero (n+1) T hT]
  have hr := primeRoot_ne_zero p hp.ne_zero (n+1)
  field_simp

theorem normalized_source_error_sq (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (n : ℕ) (h : O) (T : ℝ) (hT : 0<T) :
    ‖amplificationError Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => (Real.sqrt T:ℂ)⁻¹*c I)
      (fun I => multiplicity p (sourceGenerator S I)) p (n+1) h‖^2 =
      ‖errorScalar p hp.ne_zero n h‖^2 *
        ‖gaussPolynomial Finset.univ (sourceGenerator (residualColumns S p hp (n+1)))
          (sourceGenerator_supported (residualColumns S p hp (n+1)))
          (fun I : supportedColumns (residualColumns S p hp (n+1)) =>
            (Real.sqrt (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)):ℂ)⁻¹*
            (c ((Ideal.span {p})^(n+1)*I)*residualCharacter p (n+1) (primaryGenerator I))) h‖^2 := by
  rw [normalized_source_error S c p hp hs hpp n h T hT,norm_mul,mul_pow]

end SevenEighths.CenteredMomentAmplificationSourceError

end

end OAI
end OAIOriginalModule1974

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationErrorPool
Source SHA256: b0c51b96893627d551e19e00409aa3e77ca35c25855a277abe5eead530af8b24
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1975


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationErrorPool
open CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentAmplificationSourceDomain CenteredMomentAmplificationSourcePolynomial
open CenteredMomentAmplificationSourcePool CenteredMomentSourceRow CenteredMomentLiveDomain
open CenteredMomentGaussEnergy CenteredMomentFirstSectors CenteredMomentOriginalChildEnergy
local notation "O" => ActualEisensteinCubic.O

 theorem residual_polynomial_eq_punctured (S : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (k : ℕ) (hk : 0<k) (h : O) :
    gaussPolynomial Finset.univ (sourceGenerator (residualColumns S p hp k))
      (sourceGenerator_supported (residualColumns S p hp k))
      (fun I : supportedColumns (residualColumns S p hp k) => c ((Ideal.span {p})^k*I)*f I) h=
    gaussPolynomial Finset.univ
      (sourceGenerator (residualPool ((Ideal.span {p})^k) (pow_ne_zero k hs.1) S))
      (sourceGenerator_supported (residualPool ((Ideal.span {p})^k) (pow_ne_zero k hs.1) S))
      (fun I : supportedColumns (residualPool ((Ideal.span {p})^k) (pow_ne_zero k hs.1) S) =>
        (if IsCoprime ((Ideal.span {p})^k) (I:Ideal O) then c ((Ideal.span {p})^k*I) else 0)*f I) h := by
  let C := (Ideal.span {p})^k
  let Q := residualPool C (pow_ne_zero k hs.1) S
  refine (source_gaussPolynomial _ (fun I => c (C*I)*f I) h).trans ?_
  refine Eq.trans ?_ (source_gaussPolynomial Q
    (fun I => (if IsCoprime C I then c (C*I) else 0)*f I) h).symm
  rw [supported_residualColumns,residualColumns_eq S p hp hs hpp k,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  dsimp only [C]
  rw [IsCoprime.pow_left_iff hk]
  split_ifs <;> simp only [zero_mul]

 theorem residual_energy_eq_punctured (S : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (k : ℕ) (hk : 0<k) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy (residualColumns S p hp k) (fun I => c ((Ideal.span {p})^k*I)) f W K=
      sourceGaussEnergy (residualPool ((Ideal.span {p})^k) (pow_ne_zero k hs.1) S)
        (fun I => if IsCoprime ((Ideal.span {p})^k) I then c ((Ideal.span {p})^k*I) else 0) f W K := by
  unfold sourceGaussEnergy gaussEnergy
  apply tsum_congr
  intro h
  rw [residual_polynomial_eq_punctured S c f p hp hs hpp k hk h]

end SevenEighths.CenteredMomentAmplificationErrorPool

end

end OAI
end OAIOriginalModule1975

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationErrorEnergy
Source SHA256: 605997206b7c71eef7fa1cf0e8231a64cf3c3a7589eef9a60bcd5de4e1d5820b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1976



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationErrorEnergy
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationSourceError CenteredMomentAmplificationSourceDomain
open CenteredMomentGaussEnergy CenteredMomentGaussNormalization
open CenteredMomentSourceRow CenteredMomentOriginalChildEnergy
local notation "O" => ActualEisensteinCubic.O

def localErrorCost (p : O) (n : ℕ) : ℝ :=
  if n=5 then (1-(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹)^2
  else (Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹

theorem localErrorCost_nonneg (p : O) (n : ℕ) : 0≤localErrorCost p n := by
  unfold localErrorCost
  split_ifs <;> positivity

theorem localErrorCost_exact (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6)
    (h : O) (hh : ¬p∣h) : ‖errorScalar p hp.ne_zero n h‖^2=localErrorCost p n := by
  have he := errorScalar_norms p hp hs hg hc h hh
  rcases hn with rfl|rfl|rfl
  · simpa only [localErrorCost,show ¬(0:ℕ)=5 by decide,ite_false] using he.1
  · simpa only [localErrorCost,ite_true] using he.2.1
  · simpa only [localErrorCost,show ¬(6:ℕ)=5 by decide,ite_false] using he.2.2

theorem finite_original_error_energy (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hpp : goodLambda^2 ∣ p-1)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) (T : ℝ) (hT : 0<T)
    (rows : Finset O) (hrows : ∀ h∈rows,¬p∣h)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (hmajor : ∀ z∈rows,1≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (∑ h∈rows,‖amplificationError Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => (Real.sqrt T:ℂ)⁻¹*c I)
      (fun I => multiplicity p (sourceGenerator S I)) p (n+1) h‖^2)≤
      localErrorCost p n *
        ((sourceGaussEnergy (residualColumns S p hp (n+1))
          (fun I => c ((Ideal.span {p})^(n+1)*I))
          (fun I => residualCharacter p (n+1) (primaryGenerator I)) W K).re /
          (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1))) := by
  let Q := residualColumns S p hp (n+1)
  let T' := T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)
  let d : supportedColumns Q → ℂ := fun I =>
    c ((Ideal.span {p})^(n+1)*I)*residualCharacter p (n+1) (primaryGenerator I)
  have ht : 0<T' := by
    apply div_pos hT
    apply pow_pos
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs.1)
  have he : (∑ h∈rows,‖amplificationError Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => (Real.sqrt T:ℂ)⁻¹*c I)
      (fun I => multiplicity p (sourceGenerator S I)) p (n+1) h‖^2)=
      localErrorCost p n *∑ h∈rows,
        ‖gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
          (fun I => (Real.sqrt T':ℂ)⁻¹*d I) h‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    rw [normalized_source_error_sq S c p hp hs hpp n h T hT,
      localErrorCost_exact p hp hs hg hc n hn h (hrows h hh)]
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (localErrorCost_nonneg p n)
  have hh := finite_energy_le_gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I => (Real.sqrt T':ℂ)⁻¹*d I) W K hK rows hW hmajor
  rw [gaussEnergy_central _ _ _ d T' ht] at hh
  exact hh

end SevenEighths.CenteredMomentAmplificationErrorEnergy

end

end OAI
end OAIOriginalModule1976

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationFamily
Source SHA256: bfa5185e14091e4addb40ffcf6e2085aa646b9e563b74b882d3e68947f80438d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1977




namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationFamily
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentAmplificationShortening CenteredMomentFixedRay
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow
open CenteredMomentSecondChildProfile CenteredMomentSourceRow CenteredMomentChildRows
local notation "O" => ActualEisensteinCubic.O

def amplificationPhase (p : O) (k : ℕ) (r : RayRing) : ℂ :=
  (QuadraticAllOddCRT.quadraticRaySign (ActualEisensteinCoordinates.residue p)
    (QuadraticGaussRay.residueQuotientFour r):ℂ)^k

theorem amplificationPhase_mk (p u : O) (k : ℕ) :
    amplificationPhase p k (Ideal.Quotient.mk _ u)=sexticReciprocityPhase p u^k := by
  simp only [amplificationPhase,QuadraticGaussRay.residueQuotientFour_mk,sexticReciprocityPhase]

theorem amplificationPhase_norm (p : O) (k : ℕ) (r : RayRing) :
    ‖amplificationPhase p k r‖≤1 := by
  unfold amplificationPhase QuadraticAllOddCRT.quadraticRaySign
  split_ifs <;> cases k <;> simp

theorem amplificationPhase_mass (p : O) (k : ℕ) :
    (∑ χ : RayCharacter,‖phaseCoeff (amplificationPhase p k) χ‖)≤16 := by
  simpa only [mul_one] using phaseCoeff_sum_norm_le (amplificationPhase p k) 1
    (fun u => amplificationPhase_norm p k u)

theorem amplificationPhase_expansion (p u : O) (k : ℕ)
    (hu : Supported (Ideal.span {u})) :
    sexticReciprocityPhase p u^k=
      ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*rayCharacter χ u := by
  have he := phase_expansion (amplificationPhase p k) u
  simpa only [supported_rayMask u hu,one_mul,amplificationPhase_mk] using he

theorem exists_amplification_family (η : Character) (m p : O)
    (hm : m≠0) (hp : p≠0) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) (k : ℕ) :
    ∃ τ : RayCharacter → Character,
      (∀ χ, (τ χ).modulus.absNorm≤rowConductorBound (childCharacter η χ) m 1 (p^(2*k))) ∧
      ∀ I : Ideal O,Supported I → ∀ t : ℝ,
        rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I)=
          ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I := by
  choose τ hN hτ using fun χ : RayCharacter =>
    exists_second_height_character η χ m (p^(2*k)) hm (pow_ne_zero _ hp) hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro I hI t
  have hn := supported_primaryGenerator_ne_zero I hI
  have hgen : Supported (Ideal.span {primaryGenerator I}) := by
    rw [primary_span_supported I hI];exact hI
  rw [residualCharacter_moving p _ k hs hgen hpp (primaryGenerator_spec I hn).2,
    primary_span_supported I hI,amplificationPhase_expansion p _ k hgen]
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [hτ χ I hI t]
  ring

theorem original_column_family (η : Character) (m p : O) (k : ℕ)
    (τ : RayCharacter → Character)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I)=
        ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I)
    (C I : Ideal O) (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) :
    (β (C*I)*rowWeight η m 1 1 t (C*I))*residualCharacter p k (primaryGenerator I)=
      rowWeight η m 1 1 t C *
        ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*(β (C*I)*heightCoeff (τ χ) t I) := by
  rw [map_mul]
  calc
    _ = rowWeight η m 1 1 t C *
      (β (C*I)*(rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I))) := by ring
    _ = _ := by rw [hτ I hI t,Finset.mul_sum];congr 1;apply Finset.sum_congr rfl;intro χ hχ;ring

end SevenEighths.CenteredMomentAmplificationFamily

end

end OAI
end OAIOriginalModule1977

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationFamilyEnergy
Source SHA256: 43d14ddaa1678a66e662b2f3b46a1850d21f20f37f61b28122321c6cefd1e714
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1978




namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationFamilyEnergy
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentAmplificationShortening CenteredMomentAmplificationFamily
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow
open CenteredMomentSourceRow CenteredMomentChildRows CenteredMomentOriginalChildEnergy
open CenteredMomentGaussEnergy CenteredMomentSourceSmoothedAllocation CenteredMomentGaussNormalization
local notation "O" => ActualEisensteinCubic.O

theorem amplification_family_energy (η : Character) (m p : O) (k : ℕ)
    (τ : RayCharacter → Character)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I)=
        ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I)
    (Q : Finset (Ideal O)) (C : Ideal O) (hC : C≠0) (β : Ideal O → ℂ) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (sourceGaussEnergy Q (fun I => β (C*I)*rowWeight η m 1 1 t (C*I))
      (fun I => residualCharacter p k (primaryGenerator I)) W K).re≤
      16*∑ χ : RayCharacter,
        (sourceGaussEnergy Q (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re := by
  let b : RayCharacter → ℂ := fun χ => rowWeight η m 1 1 t C*phaseCoeff (amplificationPhase p k) χ
  let d : RayCharacter → supportedColumns Q → ℂ := fun χ I => β (C*I)*heightCoeff (τ χ) t I
  have he (I : supportedColumns Q) :
      (β (C*I)*rowWeight η m 1 1 t (C*I))*residualCharacter p k (primaryGenerator I)=
        ∑ χ,b χ*d χ I := by
    rw [original_column_family η m p k τ hτ C I (Finset.mem_filter.mp I.property).2 β t,Finset.mul_sum]
    simp only [b,d,mul_assoc]
  have hb (χ : RayCharacter) : ‖b χ‖≤1 := by
    dsimp only [b]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η m 1 1 t C hC)).trans
      (phaseCoeff_norm_le _ 1 (fun u => amplificationPhase_norm p k u) χ)
  have hd (χ : RayCharacter) : 0≤(sourceGaussEnergy Q (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re :=
    sourceGaussEnergy_nonneg _ _ _ W K hK hW
  have hh := smoothed_allocation_energy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) b d W K hK hW
  change (gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) _ W K).re≤_
  rw [funext he]
  apply hh.trans
  apply mul_le_mul
  · exact_mod_cast rayCharacter_card_le
  · apply Finset.sum_le_sum
    intro χ hχ
    apply mul_le_of_le_one_left (hd χ)
    nlinarith [hb χ,norm_nonneg (b χ)]
  · exact Finset.sum_nonneg (fun χ _ => mul_nonneg (sq_nonneg _) (hd χ))
  · norm_num

theorem exists_amplification_energy_family (η : Character) (m p : O)
    (hm : m≠0) (hp : p≠0) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) (k : ℕ) :
    ∃ τ : RayCharacter → Character,
      (∀ χ, (τ χ).modulus.absNorm≤rowConductorBound (childCharacter η χ) m 1 (p^(2*k))) ∧
      ∀ (Q : Finset (Ideal O)) (C : Ideal O),C≠0 → ∀ (β : Ideal O → ℂ) (t : ℝ)
        (W : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (sourceGaussEnergy Q (fun I => β (C*I)*rowWeight η m 1 1 t (C*I))
        (fun I => residualCharacter p k (primaryGenerator I)) W K).re≤
        16*∑ χ : RayCharacter,
          (sourceGaussEnergy Q (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re := by
  obtain ⟨τ,hN,hτ⟩ := exists_amplification_family η m p hm hp hs hpp hmLam hm2 k
  exact ⟨τ,hN,fun Q C hC β t W K hK hW => amplification_family_energy η m p k τ hτ Q C hC β t W K hK hW⟩

end SevenEighths.CenteredMomentAmplificationFamilyEnergy

end

end OAI
end OAIOriginalModule1978

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationActiveFactor
Source SHA256: 98794e51462cec8ba464c548d197688a87183e46802d31ce3969bb8cef7d8854
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1979



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationActiveFactor
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationShortening CenteredMomentSupportedCorrelation
open CenteredMomentAmplificationSourceDomain CenteredMomentAmplificationSourcePool
open CenteredMomentSourceRow
local notation "O" => ActualEisensteinCubic.O

def errorMovingExponent (n : ℕ) : ℕ := if n=5 then 0 else 1

theorem residual_six_unit (p u : O)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hcop : IsCoprime p u) : residualCharacter p 6 u=residualCharacter p 0 u := by
  have hx := idealRowHom_sixth_mask u (Ideal.span {p}) hp
  rw [idealRowHom_argument_pow u 6 _ hp,Ideal.isCoprime_span_singleton_iff,ite_eq_left hcop] at hx
  have hphase := supported_phase_sq p u hp hu
  unfold residualCharacter
  norm_num only
  calc
    _ = (sexticReciprocityPhase p u^2)^3*(idealRowHom u (Ideal.span {p})^6)^2 := by ring
    _ = 1 := by rw [hphase,hx];norm_num
    _ = _ := by simp

theorem residual_seven_unit (p u : O)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hcop : IsCoprime p u) : residualCharacter p 7 u=residualCharacter p 1 u := by
  have hx := idealRowHom_sixth_mask u (Ideal.span {p}) hp
  rw [idealRowHom_argument_pow u 6 _ hp,Ideal.isCoprime_span_singleton_iff,ite_eq_left hcop] at hx
  have hphase := supported_phase_sq p u hp hu
  unfold residualCharacter
  norm_num only
  calc
    _ = (sexticReciprocityPhase p u^2)^3*sexticReciprocityPhase p u*
        (idealRowHom u (Ideal.span {p})^6)^2*idealRowHom u (Ideal.span {p})^2 := by ring
    _ = _ := by rw [hphase,hx];ring

theorem error_residual_factor (p u : O)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hcop : IsCoprime p u) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    residualCharacter p (n+1) u=residualCharacter p (errorMovingExponent n) u := by
  rcases hn with rfl|rfl|rfl
  · rfl
  · exact residual_six_unit p u hp hu hcop
  · exact residual_seven_unit p u hp hu hcop

theorem residualColumns_coprime (S : Finset (Ideal O)) (p : O) (hp : Prime p)
    (k : ℕ) (I : Ideal O) (hI : I∈residualColumns S p hp k) :
    IsCoprime (Ideal.span {p}) I := by
  obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
  exact residualIdeal_coprime p hp J (valuationColumns_supported S p k J hJ)

theorem residual_column_active (S : Finset (Ideal O)) (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6)
    (I : Ideal O) (hI : I∈residualColumns S p hp (n+1)) :
    residualCharacter p (n+1) (primaryGenerator I)=
      residualCharacter p (errorMovingExponent n) (primaryGenerator I) := by
  have hsI := residualColumns_supported S p hp (n+1) I hI
  apply error_residual_factor p _ hs _ _ n hn
  · rw [primary_span_supported I hsI];exact hsI
  · apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [primary_span_supported I hsI]
    exact residualColumns_coprime S p hp (n+1) I hI

end SevenEighths.CenteredMomentAmplificationActiveFactor

end

end OAI
end OAIOriginalModule1979

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationActiveFamily
Source SHA256: d19fc7ef187f586f4d53ca391452eab90c7e86b571424d6127328c1b8c890faf
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1980


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationActiveFamily
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentAmplificationShortening CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationFamilyEnergy CenteredMomentAmplificationSourceDomain
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentSourceRow CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

 theorem actual_error_energy_active (S : Finset (Ideal O)) (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6)
    (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy (residualColumns S p hp (n+1)) c
      (fun I => residualCharacter p (n+1) (primaryGenerator I)) W K=
    sourceGaussEnergy (residualColumns S p hp (n+1)) c
      (fun I => residualCharacter p (errorMovingExponent n) (primaryGenerator I)) W K := by
  let Q := residualColumns S p hp (n+1)
  apply congrArg (fun f : supportedColumns Q → ℂ =>
    gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) f W K)
  funext I
  dsimp only
  rw [residual_column_active S p hp hs n hn I (Finset.mem_filter.mp I.property).1]

theorem exists_actual_error_family (η : Character) (m p : O)
    (hm : m≠0) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤rowConductorBound (childCharacter η χ) m 1
        (p^(2*errorMovingExponent n))) ∧
      ∀ (S : Finset (Ideal O)) (C : Ideal O),C≠0 → ∀ (β : Ideal O → ℂ) (t : ℝ)
        (W : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (sourceGaussEnergy (residualColumns S p hp (n+1))
        (fun I => β (C*I)*rowWeight η m 1 1 t (C*I))
        (fun I => residualCharacter p (n+1) (primaryGenerator I)) W K).re≤
        16*∑ χ : RayCharacter,
          (sourceGaussEnergy (residualColumns S p hp (n+1))
            (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re := by
  obtain ⟨τ,hN,hτ⟩ := exists_amplification_energy_family η m p hm hp.ne_zero hs hpp hmLam hm2
    (errorMovingExponent n)
  refine ⟨τ,hN,?_⟩
  intro S C hC β t W K hK hW
  rw [actual_error_energy_active S p hp hs n hn]
  exact hτ (residualColumns S p hp (n+1)) C hC β t W K hK hW

end SevenEighths.CenteredMomentAmplificationActiveFamily

end

end OAI
end OAIOriginalModule1980

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationOriginalErrors
Source SHA256: 5253f00127d73cc147eb8b18d7ec3d0d732b99f7f0c747b2219af1994c77282f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1981




namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationOriginalErrors
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationActiveFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationChildEnergy CenteredMomentAmplificationErrorPool
open CenteredMomentAmplificationSourceDomain CenteredMomentOriginalChildEnergy
