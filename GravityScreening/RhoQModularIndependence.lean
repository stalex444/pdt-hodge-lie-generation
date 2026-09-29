module
public import GravityScreening.QuarticModularAnalyticFlow

@[expose] public section

/-!
# Arithmetic independence of the cubic and quartic modular clocks

The positive roots of `X^3-X-1` and `X^4-X-1` generate number fields of
coprime degrees.  This file proves that their integer powers have no nontrivial
multiplicative relation and consequently that the ratio of their logarithmic
frequencies is irrational.
-/

namespace GravityScreening

open Polynomial

theorem cubicSelmerPolynomial_irreducible :
    Irreducible (X ^ 3 - X - 1 : ℚ[X]) :=
  X_pow_sub_X_sub_one_irreducible_rat (by norm_num)

theorem quarticSelmerPolynomial_irreducible :
    Irreducible (X ^ 4 - X - 1 : ℚ[X]) :=
  X_pow_sub_X_sub_one_irreducible_rat (by norm_num)

/-- A real cubic Selmer root is an algebraic integer. -/
theorem cubicSelmerRoot_isIntegral {rho : ℝ}
    (hrho : rho ^ 3 = rho + 1) : IsIntegral ℤ rho :=
  ⟨X ^ 3 - X - 1, by monicity!, by
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_one]
    linarith⟩

/-- The inverse of a cubic Selmer root is also an algebraic integer. -/
theorem cubicSelmerRoot_inv_isIntegral {rho : ℝ}
    (hrho : rho ^ 3 = rho + 1) : IsIntegral ℤ rho⁻¹ := by
  have h : rho⁻¹ = rho ^ 2 - 1 := by
    apply inv_eq_of_mul_eq_one_right
    linear_combination hrho
  rw [h]
  exact ((cubicSelmerRoot_isIntegral hrho).pow 2).sub isIntegral_one

/-- A positive unit larger than one cannot have a nonzero positive power in
`ℚ` when both it and its inverse are algebraic integers. -/
theorem integralUnit_pow_ne_ratCast {x : ℝ}
    (hx1 : 1 < x) (hi : IsIntegral ℤ x) (hi' : IsIntegral ℤ x⁻¹)
    {n : ℕ} (hn : n ≠ 0) (c : ℚ) : x ^ n ≠ c := by
  intro h
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, Rat.cast_zero] at h
    exact (pow_pos (by linarith : (0 : ℝ) < x) n).ne' h
  have hc : IsIntegral ℤ c := by
    rw [← isIntegral_algebraMap_iff (A := ℚ) (B := ℝ),
      eq_ratCast, ← h]
    exact hi.pow n
  have hc' : IsIntegral ℤ c⁻¹ := by
    rw [← isIntegral_algebraMap_iff (A := ℚ) (B := ℝ),
      map_inv₀, eq_ratCast, ← h, ← inv_pow]
    exact hi'.pow n
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hc
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.mp hc'
  have hmk : m * k = 1 := by
    have h1 : algebraMap ℤ ℚ m * algebraMap ℤ ℚ k = 1 := by
      rw [hm, hk]
      exact mul_inv_cancel₀ hc0
    simp only [eq_intCast] at h1
    exact_mod_cast h1
  have h1 : 1 < x ^ n := one_lt_pow₀ hx1 hn
  rw [h, ← hm] at h1
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hmk with rfl | rfl
  · norm_num at h1
  · norm_num at h1

/-- The cubic and quartic real root fields meet only in `ℚ`. -/
theorem rhoQ_adjoin_inf_eq_bot {rho q : ℝ}
    (hrho : rho ^ 3 = rho + 1) (hq : q ^ 4 = q + 1) :
    IntermediateField.adjoin ℚ {rho} ⊓
      IntermediateField.adjoin ℚ {q} = ⊥ := by
  have hrho0 : aeval rho (X ^ 3 - X - 1 : ℚ[X]) = 0 := by
    simp only [map_sub, map_pow, map_one, aeval_X]
    linarith
  have hq0 : aeval q (X ^ 4 - X - 1 : ℚ[X]) = 0 := by
    simp only [map_sub, map_pow, map_one, aeval_X]
    linarith
  have hrhoi : IsIntegral ℚ rho :=
    ⟨X ^ 3 - X - 1, by monicity!, by rwa [← aeval_def]⟩
  have hqi : IsIntegral ℚ q :=
    ⟨X ^ 4 - X - 1, by monicity!, by rwa [← aeval_def]⟩
  have h1 : minpoly ℚ rho = X ^ 3 - X - 1 :=
    (minpoly.eq_of_irreducible_of_monic cubicSelmerPolynomial_irreducible
      hrho0 (by monicity!)).symm
  have h2 : minpoly ℚ q = X ^ 4 - X - 1 :=
    (minpoly.eq_of_irreducible_of_monic quarticSelmerPolynomial_irreducible
      hq0 (by monicity!)).symm
  apply IntermediateField.LinearDisjoint.inf_eq_bot
  apply IntermediateField.LinearDisjoint.of_finrank_coprime
  rw [IntermediateField.adjoin.finrank hrhoi,
    IntermediateField.adjoin.finrank hqi, h1, h2,
    show (X ^ 3 - X - 1 : ℚ[X]).natDegree = 3 by compute_degree!,
    show (X ^ 4 - X - 1 : ℚ[X]).natDegree = 4 by compute_degree!]
  decide

/-- The two positive real roots are multiplicatively independent. -/
theorem rhoQ_mul_independent {rho q : ℝ}
    (hrho : rho ^ 3 = rho + 1) (hrho1 : 1 < rho)
    (hq : q ^ 4 = q + 1) (hq1 : 1 < q)
    (a b : ℤ) (h : rho ^ a * q ^ b = 1) : a = 0 ∧ b = 0 := by
  have hx : rho ^ a ∈ IntermediateField.adjoin ℚ {rho} ⊓
      IntermediateField.adjoin ℚ {q} := by
    rw [IntermediateField.mem_inf]
    constructor
    · exact zpow_mem (IntermediateField.mem_adjoin_simple_self ℚ rho) a
    · have hrhoq : rho ^ a = q ^ (-b) := by
        rw [zpow_neg]
        exact eq_inv_of_mul_eq_one_left h
      rw [hrhoq]
      exact zpow_mem (IntermediateField.mem_adjoin_simple_self ℚ q) (-b)
  rw [rhoQ_adjoin_inf_eq_bot hrho hq, IntermediateField.mem_bot] at hx
  obtain ⟨c, hc⟩ := hx
  have ha : a = 0 := by
    by_contra ha
    have hi := cubicSelmerRoot_isIntegral hrho
    have hi' := cubicSelmerRoot_inv_isIntegral hrho
    rcases Int.eq_nat_or_neg a with ⟨n, rfl | rfl⟩
    · have hn : n ≠ 0 := by omega
      apply integralUnit_pow_ne_ratCast hrho1 hi hi' hn c
      rw [← eq_ratCast (algebraMap ℚ ℝ) c, hc, zpow_natCast]
    · have hn : n ≠ 0 := by omega
      apply integralUnit_pow_ne_ratCast hrho1 hi hi' hn c⁻¹
      rw [Rat.cast_inv, ← eq_ratCast (algebraMap ℚ ℝ) c, hc,
        zpow_neg, zpow_natCast, inv_inv]
  subst ha
  refine ⟨rfl, ?_⟩
  rw [zpow_zero, one_mul] at h
  exact zpow_right_injective₀ (by linarith) hq1.ne'
    (h.trans (zpow_zero q).symm)

/-- The logarithmic modular frequencies of the cubic and quartic roots have
irrational ratio.  This is the arithmetic condition that prevents their
joint discrete modular spectrum from collapsing to one cyclic scale. -/
theorem rhoQ_log_ratio_irrational {rho q : ℝ}
    (hrho : rho ^ 3 = rho + 1) (hrho1 : 1 < rho)
    (hq : q ^ 4 = q + 1) (hq1 : 1 < q) :
    Irrational (Real.log rho / Real.log q) := by
  rw [irrational_iff_ne_rational]
  intro a b hb hratio
  have hrhopos : 0 < rho := lt_trans zero_lt_one hrho1
  have hqpos : 0 < q := lt_trans zero_lt_one hq1
  have hlogq : Real.log q ≠ 0 := (Real.log_pos hq1).ne'
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hlogs : (b : ℝ) * Real.log rho = (a : ℝ) * Real.log q := by
    field_simp [hlogq, hbR] at hratio
    linarith
  have hpowers : rho ^ b = q ^ a := by
    calc
      rho ^ b = rho ^ (b : ℝ) := (Real.rpow_intCast rho b).symm
      _ = Real.exp (Real.log rho * (b : ℝ)) :=
        Real.rpow_def_of_pos hrhopos _
      _ = Real.exp ((b : ℝ) * Real.log rho) := by ring_nf
      _ = Real.exp ((a : ℝ) * Real.log q) := by rw [hlogs]
      _ = Real.exp (Real.log q * (a : ℝ)) := by ring_nf
      _ = q ^ (a : ℝ) := (Real.rpow_def_of_pos hqpos _).symm
      _ = q ^ a := Real.rpow_intCast q a
  have hrelation : rho ^ b * q ^ (-a) = 1 := by
    calc
      rho ^ b * q ^ (-a) = q ^ a * q ^ (-a) := by rw [hpowers]
      _ = q ^ (a + (-a)) := (zpow_add₀ hqpos.ne' a (-a)).symm
      _ = 1 := by simp
  have hind := rhoQ_mul_independent hrho hrho1 hq hq1 b (-a) hrelation
  exact hb hind.1

/-- The synchronized one-step frequency is the logarithm of the joint `rho*q`
ruler. -/
theorem rhoQ_synchronized_modular_frequency {rho q : ℝ}
    (hrho : 0 < rho) (hq : 0 < q) :
    Real.log rho + Real.log q = Real.log (rho * q) := by
  rw [Real.log_mul hrho.ne' hq.ne']

#print axioms GravityScreening.rhoQ_adjoin_inf_eq_bot
#print axioms GravityScreening.rhoQ_mul_independent
#print axioms GravityScreening.rhoQ_log_ratio_irrational
#print axioms GravityScreening.rhoQ_synchronized_modular_frequency

end GravityScreening
