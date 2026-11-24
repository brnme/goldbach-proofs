import Mathlib

/-!
# L-hash collision: the "seven thresholds" lemma

For `k : ℕ`, the ordered zero-sum integer triples `(x, y, z)` with `x ≤ y ≤ z`,
`x + y + z = 0` and Eisenstein norm `x^2 + x*y + y^2 = 7 * 4^k` have their
maximal entry pinned to one of two thresholds: `z = 2 * 2^k` or `z = 3 * 2^k`.

Route (human-verified):
* Eliminate `x, y` for `d := y - x`: `d^2 + 3*z^2 = 28 * 4^k`, `0 ≤ d ≤ 3z`,
  `1 ≤ z`, and `2 ∣ (d - z)`.
* Descend by ordinary induction on `k` (halving `d, z` while both are even;
  parity contradictions mod 4 / mod 8 otherwise); base `k = 0` enumerates
  `z ∈ {1, 2, 3}` with `z = 1` excluded by `d ≤ 3z`.
* Reverse direction: explicit witnesses `(-3t, t)` and `(-2t, -t)` with
  `t = 2^k`.
-/

/-- An odd integer squares to `1` modulo `8`. -/
private theorem PEqualNP.Outside.sq_mod_eight_of_odd {n : ℤ} (h : n % 2 = 1) :
    n ^ 2 % 8 = 1 := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, n = 2 * m + 1 := ⟨n / 2, by omega⟩
  subst hm
  rcases (show m % 2 = 0 ∨ m % 2 = 1 by omega) with hm2 | hm2
  · obtain ⟨j, hj⟩ : ∃ j : ℤ, m = 2 * j := ⟨m / 2, by omega⟩
    subst hj
    have e : (2 * (2 * j) + 1) ^ 2 = 8 * (2 * j * j + j) + 1 := by ring
    rw [e]
    omega
  · obtain ⟨j, hj⟩ : ∃ j : ℤ, m = 2 * j + 1 := ⟨m / 2, by omega⟩
    subst hj
    have e : (2 * (2 * j + 1) + 1) ^ 2 = 8 * (2 * j * j + 3 * j + 1) + 1 := by ring
    rw [e]
    omega

/-- An even integer squares to `0` modulo `4`. -/
private theorem PEqualNP.Outside.sq_mod_four_of_even {n : ℤ} (h : n % 2 = 0) :
    n ^ 2 % 4 = 0 := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, n = 2 * m := ⟨n / 2, by omega⟩
  subst hm
  have e : (2 * m) ^ 2 = 4 * (m * m) := by ring
  rw [e]
  omega

/-- Descent step and base case: the `(d, z)` system forces `z` to a threshold. -/
private theorem PEqualNP.Outside.lab_seven_thresholds_aux :
    ∀ (k : ℕ) (d z : ℤ), 0 ≤ d → d ≤ 3 * z → 1 ≤ z → d ^ 2 + 3 * z ^ 2 = 28 * (4:ℤ) ^ k →
      (2:ℤ) ∣ d - z → z = 2 * (2:ℤ) ^ k ∨ z = 3 * (2:ℤ) ^ k := by
  intro k
  induction k with
  | zero =>
    intro d z hd0 hdle hz1 heq hdvd
    rw [pow_zero] at heq
    norm_num at heq
    -- bound z ≤ 3 from 3 * z^2 ≤ 28
    have hz_le3 : z ≤ 3 := by
      by_contra hcon
      push_neg at hcon
      have hsq : 0 ≤ (z - 4) ^ 2 := sq_nonneg (z - 4)
      have hsd : 0 ≤ d ^ 2 := sq_nonneg d
      nlinarith [hsq, hsd]
    rcases (show z = 1 ∨ z = 2 ∨ z = 3 by omega) with h | h | h
    · -- z = 1 forces d = 5, contradicting d ≤ 3 * z
      subst h
      norm_num at heq
      nlinarith [hd0, hdle]
    · subst h
      left
      norm_num
    · subst h
      right
      norm_num
  | succ k ih =>
    intro d z hd0 hdle hz1 heq hdvd
    have hmod8 : (d ^ 2 + 3 * z ^ 2) % 8 = 0 := by
      rw [heq, pow_succ (4:ℤ) k]
      omega
    rcases (show d % 2 = 0 ∨ d % 2 = 1 by omega) with hd2 | hd2
    · rcases (show z % 2 = 0 ∨ z % 2 = 1 by omega) with hz2 | hz2
      · -- both even: halve and descend
        obtain ⟨d', hd'⟩ : ∃ d' : ℤ, d = 2 * d' := ⟨d / 2, by omega⟩
        obtain ⟨z', hz'⟩ : ∃ z' : ℤ, z = 2 * z' := ⟨z / 2, by omega⟩
        subst hd'
        subst hz'
        have hp : (4:ℤ) ^ (k + 1) = 4 * (4:ℤ) ^ k := pow_succ (4:ℤ) k
        rw [hp] at heq
        have e1 : (2 * d') ^ 2 + 3 * (2 * z') ^ 2 = 4 * (d' ^ 2 + 3 * z' ^ 2) := by ring
        have e2 : (28:ℤ) * (4 * (4:ℤ) ^ k) = 4 * (28 * (4:ℤ) ^ k) := by ring
        rw [e1, e2] at heq
        have hnew : d' ^ 2 + 3 * z' ^ 2 = 28 * (4:ℤ) ^ k := by linarith
        obtain ⟨w, hw⟩ := hdvd
        have ihz := ih d' z' (by omega) (by omega) (by omega) hnew
          (⟨w, by omega⟩ : (2:ℤ) ∣ d' - z')
        rcases ihz with h | h
        · left
          rw [h, pow_succ (2:ℤ) k]
        · right
          rw [h, pow_succ (2:ℤ) k]
          ring
      · -- d even, z odd: d^2 + 3*z^2 ≡ 3 (mod 4), contradiction
        exfalso
        have hd4 : d ^ 2 % 4 = 0 := PEqualNP.Outside.sq_mod_four_of_even hd2
        have hz4 : z ^ 2 % 4 = 1 := by
          have h8 := PEqualNP.Outside.sq_mod_eight_of_odd hz2
          omega
        omega
    · rcases (show z % 2 = 0 ∨ z % 2 = 1 by omega) with hz2 | hz2
      · -- d odd, z even: d^2 + 3*z^2 ≡ 1 (mod 4), contradiction
        exfalso
        have hd4 : d ^ 2 % 4 = 1 := by
          have h8 := PEqualNP.Outside.sq_mod_eight_of_odd hd2
          omega
        have hz4 : z ^ 2 % 4 = 0 := PEqualNP.Outside.sq_mod_four_of_even hz2
        omega
      · -- both odd: d^2 + 3*z^2 ≡ 4 (mod 8), contradiction
        exfalso
        have hd8 : d ^ 2 % 8 = 1 := PEqualNP.Outside.sq_mod_eight_of_odd hd2
        have hz8 : z ^ 2 % 8 = 1 := PEqualNP.Outside.sq_mod_eight_of_odd hz2
        omega

theorem PEqualNP.Outside.L_hash_collision_lab_seven_thresholds :
    ∀ (k : ℕ) (z : ℤ), (∃ x y : ℤ, x≤y ∧ y≤z ∧ x+y+z=0 ∧ x^2+x*y+y^2=7*(4:ℤ)^k) ↔ z=2*(2:ℤ)^k ∨ z=3*(2:ℤ)^k := by
  intro k z
  constructor
  · -- forward: eliminate x, y in favor of d = y - x
    intro hex
    obtain ⟨x, y, hxy, hyz, hsum, hnorm⟩ := hex
    have hd0 : 0 ≤ y - x := by omega
    have hdle : y - x ≤ 3 * z := by omega
    have h4ne : (4:ℤ) ^ k ≠ 0 := by
      induction k with
      | zero => rw [pow_zero]; norm_num
      | succ m ih => rw [pow_succ]; exact mul_ne_zero (by norm_num) ih
    have hz1 : 1 ≤ z := by
      by_contra hc
      push_neg at hc
      have hx0 : x = 0 := by omega
      have hy0 : y = 0 := by omega
      rw [hx0, hy0] at hnorm
      norm_num at hnorm
      exact (mul_ne_zero (by norm_num : (7:ℤ) ≠ 0) h4ne) hnorm.symm
    have hcore : (y - x) ^ 2 + 3 * z ^ 2 = 28 * (4:ℤ) ^ k := by
      linear_combination 4 * hnorm - 3 * (x + y - z) * hsum
    have hdvd : (2:ℤ) ∣ (y - x) - z := by
      refine ⟨y, ?_⟩
      omega
    exact PEqualNP.Outside.lab_seven_thresholds_aux k (y - x) z hd0 hdle hz1 hcore hdvd
  · -- backward: explicit witnesses, t = 2^k
    intro h
    have ht : (0:ℤ) ≤ (2:ℤ) ^ k := by
      induction k with
      | zero => rw [pow_zero]; norm_num
      | succ m ih => rw [pow_succ]; exact mul_nonneg (by norm_num) ih
    have h4 : ((2:ℤ) ^ k) ^ 2 = (4:ℤ) ^ k := by
      have hbb : (2:ℤ) * (2:ℤ) = (4:ℤ) := by norm_num
      rw [pow_two ((2:ℤ) ^ k), ← mul_pow (2:ℤ) (2:ℤ) k, hbb]
    rcases h with h | h
    · -- z = 2 * 2^k: witness triple (-3t, t, 2t)
      subst h
      refine ⟨-(3 * (2:ℤ) ^ k), (2:ℤ) ^ k, ?_, ?_, ?_, ?_⟩
      · linarith [ht]
      · linarith [ht]
      · ring
      · linear_combination 7 * h4
    · -- z = 3 * 2^k: witness triple (-2t, -t, 3t)
      subst h
      refine ⟨-(2 * (2:ℤ) ^ k), -((2:ℤ) ^ k), ?_, ?_, ?_, ?_⟩
      · linarith [ht]
      · linarith [ht]
      · ring
      · linear_combination 7 * h4
