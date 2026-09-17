set_option maxRecDepth 10000

/-
Copyright (c) 2026 golfyx. Formalization of an explicit catalog witness.

JSP-000598, as currently worded in the prize catalog:

  Can two distinct central binomial coefficients have exactly the same
  prime divisors?

The answer is yes. This file checks

  binom 174 87    and    binom 176 88

i.e. the pair (n, m) = (87, 88) recorded in the literature around
Erdős–Graham–Ruzsa–Straus. A catalog-correction thread notes that the
original Erdős problem #730 asks for infinitely many such pairs; infinitude
is out of scope. Mathematical discovery is not claimed.
-/

namespace JSP000598

/-- Central binomial coefficient via the product formula
`C(n,k) = Π_{i=0}^{k-1} (n-i)/(i+1)`, which stays integral. -/
def binom (n k : Nat) : Nat :=
  (List.range k).foldl (fun acc i => acc * (n - i) / (i + 1)) 1


/-- A prime is an integer `p ≥ 2` whose only positive divisors are `1` and `p`. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ n, n ∣ p → n = 1 ∨ n = p

theorem isPrime_of_fin (p : Nat) (hp : 2 ≤ p)
    (h : ∀ n : Fin p, n.val ∣ p → n.val = 1) : IsPrime p := by
  refine ⟨hp, ?_⟩
  intro n hd
  have ppos : 0 < p := Nat.lt_of_lt_of_le (by decide : 0 < 2) hp
  have nle : n ≤ p := Nat.le_of_dvd ppos hd
  rcases Nat.lt_or_eq_of_le nle with hlt | rfl
  · exact Or.inl (h ⟨n, hlt⟩ hd)
  · exact Or.inr rfl

theorem gcd_eq_one_or_self {p a : Nat} (hp : IsPrime p) :
    Nat.gcd p a = 1 ∨ Nat.gcd p a = p := by
  have hdiv : Nat.gcd p a ∣ p := Nat.gcd_dvd_left p a
  cases hp.2 (Nat.gcd p a) hdiv with
  | inl h1 => exact Or.inl h1
  | inr hp' => exact Or.inr hp'

theorem not_dvd_one {p : Nat} (hp : IsPrime p) : ¬ p ∣ 1 := by
  intro h
  have : p ≤ 1 := Nat.le_of_dvd (by decide) h
  have : 2 ≤ p := hp.1
  omega

theorem prime_dvd_prime {p q : Nat} (hp : IsPrime p) (hq : IsPrime q)
    (h : p ∣ q) : p = q := by
  cases hq.2 p h with
  | inl h1 =>
    have : 2 ≤ p := hp.1
    omega
  | inr hq' => exact hq'

theorem prime_dvd_mul {p a b : Nat} (hp : IsPrime p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  rcases gcd_eq_one_or_self (a := a) hp with h1 | hp'
  · exact Or.inr ((Nat.coprime_iff_gcd_eq_one.mpr h1).dvd_of_dvd_mul_left h)
  · exact Or.inl (hp' ▸ Nat.gcd_dvd_right p a)

theorem prime_dvd_pow {p a n : Nat} (hp : IsPrime p) (h : p ∣ a ^ n) : p ∣ a := by
  induction n with
  | zero =>
    rw [Nat.pow_zero] at h
    exact (not_dvd_one hp h).elim
  | succ n ih =>
    rw [Nat.pow_succ] at h
    rcases prime_dvd_mul hp h with hpow | ha
    · exact ih hpow
    · exact ha


def PrimeDivisorsEq (a b : Nat) : Prop :=
  ∀ p, IsPrime p → (p ∣ a ↔ p ∣ b)

def Question : Prop :=
  ∃ n m, n ≠ m ∧ PrimeDivisorsEq (binom (2 * n) n) (binom (2 * m) m)

theorem prime_2 : IsPrime 2 := isPrime_of_fin 2 (by decide) (by decide)
theorem prime_3 : IsPrime 3 := isPrime_of_fin 3 (by decide) (by decide)
theorem prime_5 : IsPrime 5 := isPrime_of_fin 5 (by decide) (by decide)
theorem prime_7 : IsPrime 7 := isPrime_of_fin 7 (by decide) (by decide)
theorem prime_11 : IsPrime 11 := isPrime_of_fin 11 (by decide) (by decide)
theorem prime_13 : IsPrime 13 := isPrime_of_fin 13 (by decide) (by decide)
theorem prime_19 : IsPrime 19 := isPrime_of_fin 19 (by decide) (by decide)
theorem prime_23 : IsPrime 23 := isPrime_of_fin 23 (by decide) (by decide)
theorem prime_31 : IsPrime 31 := isPrime_of_fin 31 (by decide) (by decide)
theorem prime_47 : IsPrime 47 := isPrime_of_fin 47 (by decide) (by decide)
theorem prime_53 : IsPrime 53 := isPrime_of_fin 53 (by decide) (by decide)
theorem prime_89 : IsPrime 89 := isPrime_of_fin 89 (by decide) (by decide)
theorem prime_97 : IsPrime 97 := isPrime_of_fin 97 (by decide) (by decide)
theorem prime_101 : IsPrime 101 := isPrime_of_fin 101 (by decide) (by decide)
theorem prime_103 : IsPrime 103 := isPrime_of_fin 103 (by decide) (by decide)
theorem prime_107 : IsPrime 107 := isPrime_of_fin 107 (by decide) (by decide)
theorem prime_109 : IsPrime 109 := isPrime_of_fin 109 (by decide) (by decide)
theorem prime_113 : IsPrime 113 := isPrime_of_fin 113 (by decide) (by decide)
theorem prime_127 : IsPrime 127 := isPrime_of_fin 127 (by decide) (by decide)
theorem prime_131 : IsPrime 131 := isPrime_of_fin 131 (by decide) (by decide)
theorem prime_137 : IsPrime 137 := isPrime_of_fin 137 (by decide) (by decide)
theorem prime_139 : IsPrime 139 := isPrime_of_fin 139 (by decide) (by decide)
theorem prime_149 : IsPrime 149 := isPrime_of_fin 149 (by decide) (by decide)
theorem prime_151 : IsPrime 151 := isPrime_of_fin 151 (by decide) (by decide)
theorem prime_157 : IsPrime 157 := isPrime_of_fin 157 (by decide) (by decide)
theorem prime_163 : IsPrime 163 := isPrime_of_fin 163 (by decide) (by decide)
theorem prime_167 : IsPrime 167 := isPrime_of_fin 167 (by decide) (by decide)
theorem prime_173 : IsPrime 173 := isPrime_of_fin 173 (by decide) (by decide)

def N87 : Nat := (((((((((((((((((((((((((((2 ^ 5 * 3) * 5) * 7) * 11 ^ 2) * 13 ^ 2) * 19) * 23) * 31) * 47) * 53) * 89) * 97) * 101) * 103) * 107) * 109) * 113) * 127) * 131) * 137) * 139) * 149) * 151) * 157) * 163) * 167) * 173)
def N88 : Nat := (((((((((((((((((((((((((((2 ^ 3 * 3) * 5 ^ 3) * 7 ^ 2) * 11) * 13 ^ 2) * 19) * 23) * 31) * 47) * 53) * 89) * 97) * 101) * 103) * 107) * 109) * 113) * 127) * 131) * 137) * 139) * 149) * 151) * 157) * 163) * 167) * 173)

theorem eq_N87 : N87 = (((((((((((((((((((((((((((2 ^ 5 * 3) * 5) * 7) * 11 ^ 2) * 13 ^ 2) * 19) * 23) * 31) * 47) * 53) * 89) * 97) * 101) * 103) * 107) * 109) * 113) * 127) * 131) * 137) * 139) * 149) * 151) * 157) * 163) * 167) * 173) := rfl
theorem eq_N88 : N88 = (((((((((((((((((((((((((((2 ^ 3 * 3) * 5 ^ 3) * 7 ^ 2) * 11) * 13 ^ 2) * 19) * 23) * 31) * 47) * 53) * 89) * 97) * 101) * 103) * 107) * 109) * 113) * 127) * 131) * 137) * 139) * 149) * 151) * 157) * 163) * 167) * 173) := rfl

theorem choose_87 : binom 174 87 = N87 := by decide
theorem choose_88 : binom 176 88 = N88 := by decide

theorem dvd_87_2 : 2 ∣ N87 := ⟨N87 / 2, by decide⟩
theorem dvd_87_3 : 3 ∣ N87 := ⟨N87 / 3, by decide⟩
theorem dvd_87_5 : 5 ∣ N87 := ⟨N87 / 5, by decide⟩
theorem dvd_87_7 : 7 ∣ N87 := ⟨N87 / 7, by decide⟩
theorem dvd_87_11 : 11 ∣ N87 := ⟨N87 / 11, by decide⟩
theorem dvd_87_13 : 13 ∣ N87 := ⟨N87 / 13, by decide⟩
theorem dvd_87_19 : 19 ∣ N87 := ⟨N87 / 19, by decide⟩
theorem dvd_87_23 : 23 ∣ N87 := ⟨N87 / 23, by decide⟩
theorem dvd_87_31 : 31 ∣ N87 := ⟨N87 / 31, by decide⟩
theorem dvd_87_47 : 47 ∣ N87 := ⟨N87 / 47, by decide⟩
theorem dvd_87_53 : 53 ∣ N87 := ⟨N87 / 53, by decide⟩
theorem dvd_87_89 : 89 ∣ N87 := ⟨N87 / 89, by decide⟩
theorem dvd_87_97 : 97 ∣ N87 := ⟨N87 / 97, by decide⟩
theorem dvd_87_101 : 101 ∣ N87 := ⟨N87 / 101, by decide⟩
theorem dvd_87_103 : 103 ∣ N87 := ⟨N87 / 103, by decide⟩
theorem dvd_87_107 : 107 ∣ N87 := ⟨N87 / 107, by decide⟩
theorem dvd_87_109 : 109 ∣ N87 := ⟨N87 / 109, by decide⟩
theorem dvd_87_113 : 113 ∣ N87 := ⟨N87 / 113, by decide⟩
theorem dvd_87_127 : 127 ∣ N87 := ⟨N87 / 127, by decide⟩
theorem dvd_87_131 : 131 ∣ N87 := ⟨N87 / 131, by decide⟩
theorem dvd_87_137 : 137 ∣ N87 := ⟨N87 / 137, by decide⟩
theorem dvd_87_139 : 139 ∣ N87 := ⟨N87 / 139, by decide⟩
theorem dvd_87_149 : 149 ∣ N87 := ⟨N87 / 149, by decide⟩
theorem dvd_87_151 : 151 ∣ N87 := ⟨N87 / 151, by decide⟩
theorem dvd_87_157 : 157 ∣ N87 := ⟨N87 / 157, by decide⟩
theorem dvd_87_163 : 163 ∣ N87 := ⟨N87 / 163, by decide⟩
theorem dvd_87_167 : 167 ∣ N87 := ⟨N87 / 167, by decide⟩
theorem dvd_87_173 : 173 ∣ N87 := ⟨N87 / 173, by decide⟩
theorem dvd_88_2 : 2 ∣ N88 := ⟨N88 / 2, by decide⟩
theorem dvd_88_3 : 3 ∣ N88 := ⟨N88 / 3, by decide⟩
theorem dvd_88_5 : 5 ∣ N88 := ⟨N88 / 5, by decide⟩
theorem dvd_88_7 : 7 ∣ N88 := ⟨N88 / 7, by decide⟩
theorem dvd_88_11 : 11 ∣ N88 := ⟨N88 / 11, by decide⟩
theorem dvd_88_13 : 13 ∣ N88 := ⟨N88 / 13, by decide⟩
theorem dvd_88_19 : 19 ∣ N88 := ⟨N88 / 19, by decide⟩
theorem dvd_88_23 : 23 ∣ N88 := ⟨N88 / 23, by decide⟩
theorem dvd_88_31 : 31 ∣ N88 := ⟨N88 / 31, by decide⟩
theorem dvd_88_47 : 47 ∣ N88 := ⟨N88 / 47, by decide⟩
theorem dvd_88_53 : 53 ∣ N88 := ⟨N88 / 53, by decide⟩
theorem dvd_88_89 : 89 ∣ N88 := ⟨N88 / 89, by decide⟩
theorem dvd_88_97 : 97 ∣ N88 := ⟨N88 / 97, by decide⟩
theorem dvd_88_101 : 101 ∣ N88 := ⟨N88 / 101, by decide⟩
theorem dvd_88_103 : 103 ∣ N88 := ⟨N88 / 103, by decide⟩
theorem dvd_88_107 : 107 ∣ N88 := ⟨N88 / 107, by decide⟩
theorem dvd_88_109 : 109 ∣ N88 := ⟨N88 / 109, by decide⟩
theorem dvd_88_113 : 113 ∣ N88 := ⟨N88 / 113, by decide⟩
theorem dvd_88_127 : 127 ∣ N88 := ⟨N88 / 127, by decide⟩
theorem dvd_88_131 : 131 ∣ N88 := ⟨N88 / 131, by decide⟩
theorem dvd_88_137 : 137 ∣ N88 := ⟨N88 / 137, by decide⟩
theorem dvd_88_139 : 139 ∣ N88 := ⟨N88 / 139, by decide⟩
theorem dvd_88_149 : 149 ∣ N88 := ⟨N88 / 149, by decide⟩
theorem dvd_88_151 : 151 ∣ N88 := ⟨N88 / 151, by decide⟩
theorem dvd_88_157 : 157 ∣ N88 := ⟨N88 / 157, by decide⟩
theorem dvd_88_163 : 163 ∣ N88 := ⟨N88 / 163, by decide⟩
theorem dvd_88_167 : 167 ∣ N88 := ⟨N88 / 167, by decide⟩
theorem dvd_88_173 : 173 ∣ N88 := ⟨N88 / 173, by decide⟩

theorem prime_dvd_N87 {p : Nat} (hp : IsPrime p) (h : p ∣ N87) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 19 ∨ p = 23 ∨ p = 31 ∨ p = 47 ∨ p = 53 ∨ p = 89 ∨ p = 97 ∨ p = 101 ∨ p = 103 ∨ p = 107 ∨ p = 109 ∨ p = 113 ∨ p = 127 ∨ p = 131 ∨ p = 137 ∨ p = 139 ∨ p = 149 ∨ p = 151 ∨ p = 157 ∨ p = 163 ∨ p = 167 ∨ p = 173 := by
  have hN : p ∣ (((((((((((((((((((((((((((2 ^ 5 * 3) * 5) * 7) * 11 ^ 2) * 13 ^ 2) * 19) * 23) * 31) * 47) * 53) * 89) * 97) * 101) * 103) * 107) * 109) * 113) * 127) * 131) * 137) * 139) * 149) * 151) * 157) * 163) * 167) * 173) := (eq_N87).symm ▸ h
  rcases prime_dvd_mul hp hN with hL | hR
  ·
    rcases prime_dvd_mul hp hL with hL | hR
    ·
      rcases prime_dvd_mul hp hL with hL | hR
      ·
        rcases prime_dvd_mul hp hL with hL | hR
        ·
          rcases prime_dvd_mul hp hL with hL | hR
          ·
            rcases prime_dvd_mul hp hL with hL | hR
            ·
              rcases prime_dvd_mul hp hL with hL | hR
              ·
                rcases prime_dvd_mul hp hL with hL | hR
                ·
                  rcases prime_dvd_mul hp hL with hL | hR
                  ·
                    rcases prime_dvd_mul hp hL with hL | hR
                    ·
                      rcases prime_dvd_mul hp hL with hL | hR
                      ·
                        rcases prime_dvd_mul hp hL with hL | hR
                        ·
                          rcases prime_dvd_mul hp hL with hL | hR
                          ·
                            rcases prime_dvd_mul hp hL with hL | hR
                            ·
                              rcases prime_dvd_mul hp hL with hL | hR
                              ·
                                rcases prime_dvd_mul hp hL with hL | hR
                                ·
                                  rcases prime_dvd_mul hp hL with hL | hR
                                  ·
                                    rcases prime_dvd_mul hp hL with hL | hR
                                    ·
                                      rcases prime_dvd_mul hp hL with hL | hR
                                      ·
                                        rcases prime_dvd_mul hp hL with hL | hR
                                        ·
                                          rcases prime_dvd_mul hp hL with hL | hR
                                          ·
                                            rcases prime_dvd_mul hp hL with hL | hR
                                            ·
                                              rcases prime_dvd_mul hp hL with hL | hR
                                              ·
                                                rcases prime_dvd_mul hp hL with hL | hR
                                                ·
                                                  rcases prime_dvd_mul hp hL with hL | hR
                                                  ·
                                                    rcases prime_dvd_mul hp hL with hL | hR
                                                    ·
                                                      rcases prime_dvd_mul hp hL with hL | hR
                                                      ·
                                                        exact Or.inl (prime_dvd_prime hp prime_2 (prime_dvd_pow hp hL))
                                                      · exact Or.inr (Or.inl (prime_dvd_prime hp prime_3 hR))
                                                    · exact Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_5 hR)))
                                                  · exact Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_7 hR))))
                                                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_11 (prime_dvd_pow hp hR))))))
                                              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_13 (prime_dvd_pow hp hR)))))))
                                            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_19 hR)))))))
                                          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_23 hR))))))))
                                        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_31 hR)))))))))
                                      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_47 hR))))))))))
                                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_53 hR)))))))))))
                                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_89 hR))))))))))))
                                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_97 hR)))))))))))))
                              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_101 hR))))))))))))))
                            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_103 hR)))))))))))))))
                          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_107 hR))))))))))))))))
                        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_109 hR)))))))))))))))))
                      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_113 hR))))))))))))))))))
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_127 hR)))))))))))))))))))
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_131 hR))))))))))))))))))))
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_137 hR)))))))))))))))))))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_139 hR))))))))))))))))))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_149 hR)))))))))))))))))))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_151 hR))))))))))))))))))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_157 hR)))))))))))))))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_163 hR))))))))))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_167 hR)))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (prime_dvd_prime hp prime_173 hR)))))))))))))))))))))))))))

theorem prime_dvd_N88 {p : Nat} (hp : IsPrime p) (h : p ∣ N88) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 19 ∨ p = 23 ∨ p = 31 ∨ p = 47 ∨ p = 53 ∨ p = 89 ∨ p = 97 ∨ p = 101 ∨ p = 103 ∨ p = 107 ∨ p = 109 ∨ p = 113 ∨ p = 127 ∨ p = 131 ∨ p = 137 ∨ p = 139 ∨ p = 149 ∨ p = 151 ∨ p = 157 ∨ p = 163 ∨ p = 167 ∨ p = 173 := by
  have hN : p ∣ (((((((((((((((((((((((((((2 ^ 3 * 3) * 5 ^ 3) * 7 ^ 2) * 11) * 13 ^ 2) * 19) * 23) * 31) * 47) * 53) * 89) * 97) * 101) * 103) * 107) * 109) * 113) * 127) * 131) * 137) * 139) * 149) * 151) * 157) * 163) * 167) * 173) := (eq_N88).symm ▸ h
  rcases prime_dvd_mul hp hN with hL | hR
  ·
    rcases prime_dvd_mul hp hL with hL | hR
    ·
      rcases prime_dvd_mul hp hL with hL | hR
      ·
        rcases prime_dvd_mul hp hL with hL | hR
        ·
          rcases prime_dvd_mul hp hL with hL | hR
          ·
            rcases prime_dvd_mul hp hL with hL | hR
            ·
              rcases prime_dvd_mul hp hL with hL | hR
              ·
                rcases prime_dvd_mul hp hL with hL | hR
                ·
                  rcases prime_dvd_mul hp hL with hL | hR
                  ·
                    rcases prime_dvd_mul hp hL with hL | hR
                    ·
                      rcases prime_dvd_mul hp hL with hL | hR
                      ·
                        rcases prime_dvd_mul hp hL with hL | hR
                        ·
                          rcases prime_dvd_mul hp hL with hL | hR
                          ·
                            rcases prime_dvd_mul hp hL with hL | hR
                            ·
                              rcases prime_dvd_mul hp hL with hL | hR
                              ·
                                rcases prime_dvd_mul hp hL with hL | hR
                                ·
                                  rcases prime_dvd_mul hp hL with hL | hR
                                  ·
                                    rcases prime_dvd_mul hp hL with hL | hR
                                    ·
                                      rcases prime_dvd_mul hp hL with hL | hR
                                      ·
                                        rcases prime_dvd_mul hp hL with hL | hR
                                        ·
                                          rcases prime_dvd_mul hp hL with hL | hR
                                          ·
                                            rcases prime_dvd_mul hp hL with hL | hR
                                            ·
                                              rcases prime_dvd_mul hp hL with hL | hR
                                              ·
                                                rcases prime_dvd_mul hp hL with hL | hR
                                                ·
                                                  rcases prime_dvd_mul hp hL with hL | hR
                                                  ·
                                                    rcases prime_dvd_mul hp hL with hL | hR
                                                    ·
                                                      rcases prime_dvd_mul hp hL with hL | hR
                                                      ·
                                                        exact Or.inl (prime_dvd_prime hp prime_2 (prime_dvd_pow hp hL))
                                                      · exact Or.inr (Or.inl (prime_dvd_prime hp prime_3 hR))
                                                    · exact Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_5 (prime_dvd_pow hp hR))))
                                                  · exact Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_7 (prime_dvd_pow hp hR)))))
                                                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_11 hR)))))
                                              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_13 (prime_dvd_pow hp hR)))))))
                                            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_19 hR)))))))
                                          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_23 hR))))))))
                                        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_31 hR)))))))))
                                      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_47 hR))))))))))
                                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_53 hR)))))))))))
                                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_89 hR))))))))))))
                                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_97 hR)))))))))))))
                              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_101 hR))))))))))))))
                            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_103 hR)))))))))))))))
                          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_107 hR))))))))))))))))
                        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_109 hR)))))))))))))))))
                      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_113 hR))))))))))))))))))
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_127 hR)))))))))))))))))))
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_131 hR))))))))))))))))))))
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_137 hR)))))))))))))))))))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_139 hR))))))))))))))))))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_149 hR)))))))))))))))))))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_151 hR))))))))))))))))))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_157 hR)))))))))))))))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_163 hR))))))))))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime hp prime_167 hR)))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (prime_dvd_prime hp prime_173 hR)))))))))))))))))))))))))))

theorem dvd_of_eq_N87 {p : Nat} (h : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 19 ∨ p = 23 ∨ p = 31 ∨ p = 47 ∨ p = 53 ∨ p = 89 ∨ p = 97 ∨ p = 101 ∨ p = 103 ∨ p = 107 ∨ p = 109 ∨ p = 113 ∨ p = 127 ∨ p = 131 ∨ p = 137 ∨ p = 139 ∨ p = 149 ∨ p = 151 ∨ p = 157 ∨ p = 163 ∨ p = 167 ∨ p = 173) : p ∣ N87 := by
  rcases h with hl | hr
  · subst hl; exact dvd_87_2
  ·
    rcases hr with hrl | hrr
    · subst hrl; exact dvd_87_3
    ·
      rcases hrr with hrrl | hrrr
      · subst hrrl; exact dvd_87_5
      ·
        rcases hrrr with hrrrl | hrrrr
        · subst hrrrl; exact dvd_87_7
        ·
          rcases hrrrr with hrrrrl | hrrrrr
          · subst hrrrrl; exact dvd_87_11
          ·
            rcases hrrrrr with hrrrrrl | hrrrrrr
            · subst hrrrrrl; exact dvd_87_13
            ·
              rcases hrrrrrr with hrrrrrrl | hrrrrrrr
              · subst hrrrrrrl; exact dvd_87_19
              ·
                rcases hrrrrrrr with hrrrrrrrl | hrrrrrrrr
                · subst hrrrrrrrl; exact dvd_87_23
                ·
                  rcases hrrrrrrrr with hrrrrrrrrl | hrrrrrrrrr
                  · subst hrrrrrrrrl; exact dvd_87_31
                  ·
                    rcases hrrrrrrrrr with hrrrrrrrrrl | hrrrrrrrrrr
                    · subst hrrrrrrrrrl; exact dvd_87_47
                    ·
                      rcases hrrrrrrrrrr with hrrrrrrrrrrl | hrrrrrrrrrrr
                      · subst hrrrrrrrrrrl; exact dvd_87_53
                      ·
                        rcases hrrrrrrrrrrr with hrrrrrrrrrrrl | hrrrrrrrrrrrr
                        · subst hrrrrrrrrrrrl; exact dvd_87_89
                        ·
                          rcases hrrrrrrrrrrrr with hrrrrrrrrrrrrl | hrrrrrrrrrrrrr
                          · subst hrrrrrrrrrrrrl; exact dvd_87_97
                          ·
                            rcases hrrrrrrrrrrrrr with hrrrrrrrrrrrrrl | hrrrrrrrrrrrrrr
                            · subst hrrrrrrrrrrrrrl; exact dvd_87_101
                            ·
                              rcases hrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrr
                              · subst hrrrrrrrrrrrrrrl; exact dvd_87_103
                              ·
                                rcases hrrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrrr
                                · subst hrrrrrrrrrrrrrrrl; exact dvd_87_107
                                ·
                                  rcases hrrrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrrrr
                                  · subst hrrrrrrrrrrrrrrrrl; exact dvd_87_109
                                  ·
                                    rcases hrrrrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrrrrr
                                    · subst hrrrrrrrrrrrrrrrrrl; exact dvd_87_113
                                    ·
                                      rcases hrrrrrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrrrrrr
                                      · subst hrrrrrrrrrrrrrrrrrrl; exact dvd_87_127
                                      ·
                                        rcases hrrrrrrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrrrrrrr
                                        · subst hrrrrrrrrrrrrrrrrrrrl; exact dvd_87_131
                                        ·
                                          rcases hrrrrrrrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrrrrrrrr
                                          · subst hrrrrrrrrrrrrrrrrrrrrl; exact dvd_87_137
                                          ·
                                            rcases hrrrrrrrrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrrrrrrrrr
                                            · subst hrrrrrrrrrrrrrrrrrrrrrl; exact dvd_87_139
                                            ·
                                              rcases hrrrrrrrrrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrrrrrrrrrr
                                              · subst hrrrrrrrrrrrrrrrrrrrrrrl; exact dvd_87_149
                                              ·
                                                rcases hrrrrrrrrrrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrrrrrrrrrrr
                                                · subst hrrrrrrrrrrrrrrrrrrrrrrrl; exact dvd_87_151
                                                ·
                                                  rcases hrrrrrrrrrrrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrrrrrrrrrrrr
                                                  · subst hrrrrrrrrrrrrrrrrrrrrrrrrl; exact dvd_87_157
                                                  ·
                                                    rcases hrrrrrrrrrrrrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrrrrrrrrrrrrr
                                                    · subst hrrrrrrrrrrrrrrrrrrrrrrrrrl; exact dvd_87_163
                                                    ·
                                                      rcases hrrrrrrrrrrrrrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrrrrrrrrrrrrrr
                                                      · subst hrrrrrrrrrrrrrrrrrrrrrrrrrrl; exact dvd_87_167
                                                      ·
                                                        subst hrrrrrrrrrrrrrrrrrrrrrrrrrrr
                                                        exact dvd_87_173

theorem dvd_of_eq_N88 {p : Nat} (h : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 19 ∨ p = 23 ∨ p = 31 ∨ p = 47 ∨ p = 53 ∨ p = 89 ∨ p = 97 ∨ p = 101 ∨ p = 103 ∨ p = 107 ∨ p = 109 ∨ p = 113 ∨ p = 127 ∨ p = 131 ∨ p = 137 ∨ p = 139 ∨ p = 149 ∨ p = 151 ∨ p = 157 ∨ p = 163 ∨ p = 167 ∨ p = 173) : p ∣ N88 := by
  rcases h with hl | hr
  · subst hl; exact dvd_88_2
  ·
    rcases hr with hrl | hrr
    · subst hrl; exact dvd_88_3
    ·
      rcases hrr with hrrl | hrrr
      · subst hrrl; exact dvd_88_5
      ·
        rcases hrrr with hrrrl | hrrrr
        · subst hrrrl; exact dvd_88_7
        ·
          rcases hrrrr with hrrrrl | hrrrrr
          · subst hrrrrl; exact dvd_88_11
          ·
            rcases hrrrrr with hrrrrrl | hrrrrrr
            · subst hrrrrrl; exact dvd_88_13
            ·
              rcases hrrrrrr with hrrrrrrl | hrrrrrrr
              · subst hrrrrrrl; exact dvd_88_19
              ·
                rcases hrrrrrrr with hrrrrrrrl | hrrrrrrrr
                · subst hrrrrrrrl; exact dvd_88_23
                ·
                  rcases hrrrrrrrr with hrrrrrrrrl | hrrrrrrrrr
                  · subst hrrrrrrrrl; exact dvd_88_31
                  ·
                    rcases hrrrrrrrrr with hrrrrrrrrrl | hrrrrrrrrrr
                    · subst hrrrrrrrrrl; exact dvd_88_47
                    ·
                      rcases hrrrrrrrrrr with hrrrrrrrrrrl | hrrrrrrrrrrr
                      · subst hrrrrrrrrrrl; exact dvd_88_53
                      ·
                        rcases hrrrrrrrrrrr with hrrrrrrrrrrrl | hrrrrrrrrrrrr
                        · subst hrrrrrrrrrrrl; exact dvd_88_89
                        ·
                          rcases hrrrrrrrrrrrr with hrrrrrrrrrrrrl | hrrrrrrrrrrrrr
                          · subst hrrrrrrrrrrrrl; exact dvd_88_97
                          ·
                            rcases hrrrrrrrrrrrrr with hrrrrrrrrrrrrrl | hrrrrrrrrrrrrrr
                            · subst hrrrrrrrrrrrrrl; exact dvd_88_101
                            ·
                              rcases hrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrr
                              · subst hrrrrrrrrrrrrrrl; exact dvd_88_103
                              ·
                                rcases hrrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrrr
                                · subst hrrrrrrrrrrrrrrrl; exact dvd_88_107
                                ·
                                  rcases hrrrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrrrr
                                  · subst hrrrrrrrrrrrrrrrrl; exact dvd_88_109
                                  ·
                                    rcases hrrrrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrrrrr
                                    · subst hrrrrrrrrrrrrrrrrrl; exact dvd_88_113
                                    ·
                                      rcases hrrrrrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrrrrrr
                                      · subst hrrrrrrrrrrrrrrrrrrl; exact dvd_88_127
                                      ·
                                        rcases hrrrrrrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrrrrrrr
                                        · subst hrrrrrrrrrrrrrrrrrrrl; exact dvd_88_131
                                        ·
                                          rcases hrrrrrrrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrrrrrrrr
                                          · subst hrrrrrrrrrrrrrrrrrrrrl; exact dvd_88_137
                                          ·
                                            rcases hrrrrrrrrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrrrrrrrrr
                                            · subst hrrrrrrrrrrrrrrrrrrrrrl; exact dvd_88_139
                                            ·
                                              rcases hrrrrrrrrrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrrrrrrrrrr
                                              · subst hrrrrrrrrrrrrrrrrrrrrrrl; exact dvd_88_149
                                              ·
                                                rcases hrrrrrrrrrrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrrrrrrrrrrr
                                                · subst hrrrrrrrrrrrrrrrrrrrrrrrl; exact dvd_88_151
                                                ·
                                                  rcases hrrrrrrrrrrrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrrrrrrrrrrrr
                                                  · subst hrrrrrrrrrrrrrrrrrrrrrrrrl; exact dvd_88_157
                                                  ·
                                                    rcases hrrrrrrrrrrrrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrrrrrrrrrrrrr
                                                    · subst hrrrrrrrrrrrrrrrrrrrrrrrrrl; exact dvd_88_163
                                                    ·
                                                      rcases hrrrrrrrrrrrrrrrrrrrrrrrrrr with hrrrrrrrrrrrrrrrrrrrrrrrrrrl | hrrrrrrrrrrrrrrrrrrrrrrrrrrr
                                                      · subst hrrrrrrrrrrrrrrrrrrrrrrrrrrl; exact dvd_88_167
                                                      ·
                                                        subst hrrrrrrrrrrrrrrrrrrrrrrrrrrr
                                                        exact dvd_88_173

theorem same_primes {p : Nat} (hp : IsPrime p) : p ∣ N87 ↔ p ∣ N88 := by
  constructor
  · intro h
    exact dvd_of_eq_N88 (prime_dvd_N87 hp h)
  · intro h
    exact dvd_of_eq_N87 (prime_dvd_N88 hp h)

theorem witness_87_88 :
    PrimeDivisorsEq (binom 174 87) (binom 176 88) := by
  intro p hp
  rw [choose_87, choose_88]
  exact same_primes hp

theorem jsp_000598 : Question :=
  ⟨87, 88, by decide, by
    simpa [Nat.mul_comm] using witness_87_88⟩

theorem question_true : Question := jsp_000598

end JSP000598
