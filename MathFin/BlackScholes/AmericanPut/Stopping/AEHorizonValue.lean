/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ExerciseRegion

/-! # Almost-sure versus pointwise finite-horizon stopping rules

The financial convention permits a stopping time to exceed maturity on a
null set. Clipping at maturity gives a pointwise bounded rule with the same
reward almost everywhere. Consequently the stopping value and exercise
threshold are unchanged. No PDE or boundary regularity is used.

## Result

Public entry points include `aeAmericanPutValue_eq` and `aeExerciseThreshold_eq`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory Set
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A stopping time for `𝓕`, valued in `WithTop ℝ≥0`, that is bounded by the horizon `T`
only `P`-almost surely. -/
structure AEBoundedRule (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (T : ℝ≥0) where
  /-- The stopping time, possibly infinite. -/
  time : Ω → WithTop ℝ≥0
  stopping : IsStoppingTime 𝓕 time
  ae_le_horizon : ∀ᵐ ω ∂P, time ω ≤ T

namespace AEBoundedRule

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T : ℝ≥0}

/-- The value at infinity is immaterial, since infinity occurs only on a null set. -/
noncomputable def finiteTime (θ : AEBoundedRule P 𝓕 T) (ω : Ω) : ℝ≥0 :=
  (θ.time ω).untopD 0

/-- The rule truncated at the horizon: the pointwise bounded rule with time
`min (θ.time ω) T`. -/
noncomputable def clip (θ : AEBoundedRule P 𝓕 T) : BoundedRule 𝓕 T :=
  BoundedRule.ofWithTop (fun ω => min (θ.time ω) T)
    (θ.stopping.min_const T) (fun ω => min_le_right (θ.time ω) T)

theorem clip_time_coe (θ : AEBoundedRule P 𝓕 T) (ω : Ω) :
    ((θ.clip.time ω : ℝ≥0) : WithTop ℝ≥0) = min (θ.time ω) T :=
  BoundedRule.ofWithTop_coe_time _ _ _ ω

theorem clip_time_coe_ae_eq (θ : AEBoundedRule P 𝓕 T) :
    (fun ω => ((θ.clip.time ω : ℝ≥0) : WithTop ℝ≥0)) =ᵐ[P] θ.time := by
  filter_upwards [θ.ae_le_horizon] with ω hω
  rw [θ.clip_time_coe,min_eq_left hω]

theorem clip_time_ae_eq (θ : AEBoundedRule P 𝓕 T) : θ.clip.time =ᵐ[P] θ.finiteTime := by
  filter_upwards [θ.clip_time_coe_ae_eq] with ω hω
  have he := congrArg (fun x : WithTop ℝ≥0 => x.untopD 0) hω
  simpa only [WithTop.untopD_coe,finiteTime] using he

theorem clip_expectedReward (θ : AEBoundedRule P 𝓕 T)
    (W : ℝ≥0 → Ω → ℝ) (K r q σ S : ℝ) :
    (∫ ω, putReward W K r q σ S θ.clip.time ω ∂P) =
      ∫ ω, putReward W K r q σ S θ.finiteTime ω ∂P := by
  apply integral_congr_ae
  filter_upwards [θ.clip_time_ae_eq] with ω hω
  simp only [putReward,hω]

theorem reward_integrable [IsFiniteMeasure P] (θ : AEBoundedRule P 𝓕 T)
    {W : ℝ≥0 → Ω → ℝ} (hW : Measurable W.uncurry) {K r q σ S : ℝ}
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) :
    Integrable (fun ω => putReward W K r q σ S θ.finiteTime ω) P := by
  apply (putReward_integrable (q := q) (σ := σ) hW P hK hr hS θ.clip.measurable_time).congr
  filter_upwards [θ.clip_time_ae_eq] with ω hω
  simp only [putReward,hω]

end AEBoundedRule

namespace BoundedRule

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T : ℝ≥0}

/-- A pointwise bounded rule read as an almost-surely bounded one. -/
def toAEBoundedRule (θ : BoundedRule 𝓕 T) : AEBoundedRule P 𝓕 T where
  time := fun ω => θ.time ω
  stopping := θ.stopping
  ae_le_horizon := Filter.Eventually.of_forall (fun ω => WithTop.coe_le_coe.mpr (θ.le_horizon ω))

theorem toAEBoundedRule_finiteTime (θ : BoundedRule 𝓕 T) :
    (θ.toAEBoundedRule (P := P)).finiteTime = θ.time := by
  funext ω
  simp only [AEBoundedRule.finiteTime,toAEBoundedRule,WithTop.untopD_coe]

end BoundedRule

/-- The expected discounted put rewards ranging over all almost-surely bounded rules. -/
noncomputable def aeExerciseValues (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℝ≥0 → Ω → ℝ) (K r q σ S : ℝ) (T : ℝ≥0) : Set ℝ :=
  range (fun θ : AEBoundedRule P 𝓕 T => ∫ ω, putReward W K r q σ S θ.finiteTime ω ∂P)

/-- Supremum of `aeExerciseValues`, the put value over almost-surely bounded rules. -/
noncomputable def aeAmericanPutValue (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℝ≥0 → Ω → ℝ) (K r q σ S : ℝ) (T : ℝ≥0) : ℝ :=
  sSup (aeExerciseValues P 𝓕 W K r q σ S T)

theorem aeExerciseValues_eq (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℝ≥0 → Ω → ℝ) (K r q σ S : ℝ) (T : ℝ≥0) :
    aeExerciseValues P 𝓕 W K r q σ S T = exerciseValues P 𝓕 W K r q σ S T := by
  apply Subset.antisymm
  · rintro _ ⟨θ,rfl⟩
    exact ⟨θ.clip,θ.clip_expectedReward W K r q σ S⟩
  · rintro _ ⟨θ,rfl⟩
    refine ⟨θ.toAEBoundedRule,?_⟩
    change (∫ ω, putReward W K r q σ S (θ.toAEBoundedRule (P := P)).finiteTime ω ∂P) = _
    rw [θ.toAEBoundedRule_finiteTime]

theorem aeAmericanPutValue_eq (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℝ≥0 → Ω → ℝ) (K r q σ S : ℝ) (T : ℝ≥0) :
    aeAmericanPutValue P 𝓕 W K r q σ S T = americanPutValue P 𝓕 W K r q σ S T := by
  unfold aeAmericanPutValue americanPutValue
  rw [aeExerciseValues_eq]

theorem aeExerciseValues_nonempty (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℝ≥0 → Ω → ℝ) (K r q σ S : ℝ) (T : ℝ≥0) :
    (aeExerciseValues P 𝓕 W K r q σ S T).Nonempty := by
  rw [aeExerciseValues_eq]
  exact exerciseValues_nonempty

theorem aeExerciseValues_bddAbove (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) {W : ℝ≥0 → Ω → ℝ}
    (hW : Measurable W.uncurry) {K r q σ S : ℝ} (T : ℝ≥0)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) :
    BddAbove (aeExerciseValues P 𝓕 W K r q σ S T) := by
  rw [aeExerciseValues_eq]
  exact exerciseValues_bddAbove hW hK hr hS

/-- Supremum of the spots `S` in `[0,K]` at which `aeAmericanPutValue` equals the immediate
payoff `K-S`. -/
noncomputable def aeExerciseThreshold (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℝ≥0 → Ω → ℝ) (K r q σ : ℝ) (T : ℝ≥0) : ℝ :=
  sSup {S | 0 ≤ S ∧ S ≤ K ∧ aeAmericanPutValue P 𝓕 W K r q σ S T = K-S}

theorem aeExerciseThreshold_eq (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℝ≥0 → Ω → ℝ) (K r q σ : ℝ) (T : ℝ≥0) :
    aeExerciseThreshold P 𝓕 W K r q σ T = exerciseThreshold P 𝓕 W K r q σ T := by
  unfold aeExerciseThreshold exerciseThreshold exerciseSet
  simp only [aeAmericanPutValue_eq]

end MathFin.BlackScholes.AmericanPut.Stopping
