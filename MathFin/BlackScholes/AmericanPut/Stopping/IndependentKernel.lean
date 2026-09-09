/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Independence.Integration

/-! # Averaging an independent increment with a past-measurable starting state 
## Result

Public entry points include `integral_pair_of_indep_bounded`, `condExp_independent_kernel`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

theorem integral_pair_of_indep_bounded {A : Ω → ℝ × ℝ} {Y : Ω → ℝ}
    (hA : Measurable A) (hY : Measurable Y) (hi : IndepFun A Y P)
    {G : (ℝ × ℝ) × ℝ → ℝ} (hG : Measurable G) {C : ℝ} (hb : ∀ z, ‖G z‖ ≤ C) :
    (∫ ω, G (A ω,Y ω) ∂P) = ∫ ω, ∫ y, G (A ω,y) ∂P.map Y ∂P := by
  have hint : Integrable G ((P.map A).prod (P.map Y)) :=
    (integrable_const C).mono' hG.aestronglyMeasurable (Eventually.of_forall hb)
  rw [← integral_map (hA.prodMk hY).aemeasurable hG.aestronglyMeasurable,
    hi.map_prod_eq_prod_map_map hA.aemeasurable hY.aemeasurable,
    integral_prod _ hint,integral_map hA.aemeasurable hG.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable]

theorem condExp_independent_kernel (hm : m ≤ mΩ)
    {X Y : Ω → ℝ} (hX : Measurable[m] X) (hY : Measurable Y)
    (hi : Indep (MeasurableSpace.comap Y (borel ℝ)) m P)
    {H : ℝ × ℝ → ℝ} (hH : Measurable H) {C : ℝ} (hb : ∀ z, ‖H z‖ ≤ C) :
    P[fun ω => H (X ω,Y ω) | m] =ᵐ[P]
      fun ω => ∫ y, H (X ω,y) ∂P.map Y := by
  letI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hC : 0 ≤ C := (norm_nonneg (H (0,0))).trans (hb (0,0))
  have hK : StronglyMeasurable (fun x => ∫ y, H (x,y) ∂P.map Y) :=
    hH.stronglyMeasurable.integral_prod_right'
  have hKb (x : ℝ) : ‖∫ y, H (x,y) ∂P.map Y‖ ≤ C := by
    simpa using norm_integral_le_of_norm_le_const
      (μ := P.map Y) (Eventually.of_forall (fun y => hb (x,y)))
  have hint : Integrable (fun ω => H (X ω,Y ω)) P :=
    (integrable_const C).mono' (hH.comp ((hX.mono hm le_rfl).prodMk hY)).aestronglyMeasurable
      (Eventually.of_forall (fun ω => hb (X ω,Y ω)))
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hint
    (fun _ _ _ => ((integrable_const C).mono'
      (hK.comp_measurable (hX.mono hm le_rfl)).aestronglyMeasurable
      (Eventually.of_forall (fun ω => hKb (X ω)))).integrableOn) ?_
    (hK.comp_measurable hX).aestronglyMeasurable).symm
  intro s hs _
  let A : Ω → ℝ × ℝ := fun ω => (X ω,s.indicator (fun _ => (1 : ℝ)) ω)
  have hA : Measurable[m] A := hX.prodMk (measurable_const.indicator hs)
  let G : (ℝ × ℝ) × ℝ → ℝ :=
    {z | z.1.2 = 1}.indicator (fun z => H (z.1.1,z.2))
  have hG : Measurable G :=
    (hH.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).indicator
      (measurableSet_eq_fun (measurable_snd.comp measurable_fst) measurable_const)
  have hGb (z : (ℝ × ℝ) × ℝ) : ‖G z‖ ≤ C := by
    by_cases hz : z.1.2 = 1
    · simpa [G,hz] using hb (z.1.1,z.2)
    · simpa [G,hz] using hC
  have hiA : IndepFun A Y P := by
    apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
    intro u v hu hv
    have hh := hi.symm
    rw [Indep_iff] at hh
    exact hh _ _ (hA hu)
      ((Measurable.of_comap_le le_rfl : Measurable[MeasurableSpace.comap Y (borel ℝ)] Y) hv)
  have he := integral_pair_of_indep_bounded (hA.mono hm le_rfl) hY hiA hG hGb
  have hleft : (fun ω => G (A ω,Y ω)) = s.indicator (fun ω => H (X ω,Y ω)) := by
    funext ω
    by_cases hω : ω ∈ s <;> simp [G,A,hω]
  have hright : (fun ω => ∫ y, G (A ω,y) ∂P.map Y) =
      s.indicator (fun ω => ∫ y, H (X ω,y) ∂P.map Y) := by
    funext ω
    by_cases hω : ω ∈ s <;> simp [G,A,hω]
  rw [hleft,hright,integral_indicator (hm _ hs),integral_indicator (hm _ hs)] at he
  exact he.symm

end MathFin.BlackScholes.AmericanPut.Stopping
