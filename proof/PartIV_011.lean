    (hpole : s ≠ 1 ∨ chi.residue ≠ 1) : LFunction chi s ≠ 0 :=
  HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt chi (beta_star_le.trans_lt hs) hpole

theorem dirichlet_nonzero (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q) (s : ℂ)
    (hs : limitingBoundary < s.re) (hpole : ¬(chi=1 ∧ s=1)) :
    chi.LFunction s ≠ 0 :=
  RHZeroFreeExtension.ActualDirichletTransfer.dirichlet_nonzero_of_hecke_bound
    limitingBoundary limitingBoundary_positive hecke_nonzero q chi s hs hpole

theorem zeta_nonzero (s : ℂ) (hs : limitingBoundary < s.re) (_hpole : s ≠ 1) :
    riemannZeta s ≠ 0 :=
  RHZeroFreeExtension.ActualDirichletTransfer.zeta_nonzero_of_hecke_bound
    limitingBoundary limitingBoundary_positive hecke_nonzero s hs

/-- The rational checkpoint has its own one-step physical proof from Part III. -/
theorem rational_checkpoint_one_step : HeckeZeroSupremum.beta ≤ Checkpoint.boundary := by
  letI : RHIVProbe.Geometry := CheckpointGeometry.geometry
  letI : RHIVProbe.HighGeometry := CheckpointGeometry.highGeometry
  letI : RHIVProbe.MomentParameter := CheckpointGeometry.momentParameter
  letI : RHIVProbe.CountGeometry := CheckpointGeometry.countGeometry
  have hp : HeckeZeroSupremum.beta ≤ (1+RHIVProbe.momentKappa)/2 := by
    change HeckeZeroSupremum.beta ≤ (1+Checkpoint.kappa)/2
    exact RHV2.beta_star_le.trans Checkpoint.moment_premise.le
  have h := RHZeroFreeExtension.AnalyticHigh.IV.beta_le_of_previous_bound hp
  change HeckeZeroSupremum.beta ≤ @RHIVProbe.boundary CheckpointGeometry.geometry at h
  rw [CheckpointGeometry.physical_boundary] at h
  exact h

#print axioms one_step
#print axioms bootstrap_finite_bounds
#print axioms beta_star_le
#print axioms hecke_nonzero
#print axioms dirichlet_nonzero
#print axioms zeta_nonzero
#print axioms rational_checkpoint_one_step
end
end CombineV22

end PartIVBlock22
