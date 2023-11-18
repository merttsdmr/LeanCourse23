import LeanCourse.Common
set_option linter.unusedVariables false
open Nat

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 2, sections 3, 4 and 5
  Read chapter 3, sections 1, 2, 4, 5.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 27.10.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/
lemma exercise2_1 {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  {
    constructor
    · intro h
      obtain ⟨ x,hx ⟩  :=h
      obtain h1|h2 := hx
      left
      · use x
      right
      · use x
    · intro h
      obtain h1|h2 := h
      obtain ⟨ x,hx ⟩ := h1
      use x
      exact Or.inl hx
      obtain ⟨ x,hx ⟩ := h2
      use x
      exact Or.inr hx
  }
lemma exercise2_a {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  {
   exact exists_or
  }

section Surjectivity

/- Lean's mathematical library knows what a surjective function is, but let's define it here
ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
  `simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

lemma exercise2_2 (h : SurjectiveFunction (g ∘ f)) : SurjectiveFunction g := by
  {
    rw [SurjectiveFunction]
    rw [SurjectiveFunction] at h
    intro y
    have h1: (g ∘ f) x = g (f x) := by simp
    specialize h y
    obtain ⟨ x, hx ⟩ :=h
    use f x
    exact hx
  }
/- Hint: you are allowed to use the previous exercise in this exercise! -/
lemma exercise2_3 (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by
  {
    constructor
    · intro h y
      specialize h y
      obtain ⟨ x, hx ⟩ :=h
      use f x
      exact hx
    · intro h z
      specialize h z
      obtain ⟨ y, hx⟩ := h
      specialize hf y
      obtain ⟨ x , hfx⟩ :=hf
      use x
      simp [hx, hfx]

  }

/- Composing a surjective function by a linear function to the left and the right will still result
in a surjective function. The `ring` tactic will be very useful here! -/
lemma exercise2_4 (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by
  {
  let m (x : ℝ) : ℝ := 3 * (x + 4)
  let n (x : ℝ) : ℝ := 2*x+1
  have m_surjective : SurjectiveFunction m := by{
    intro y
    use (y / 3 - 4)
    simp
    ring
  }
  have n_surjective : SurjectiveFunction n := by{
    intro y
    use ((y-1)/2)
    simp
    ring
  }
  let fm (x : ℝ) : ℝ := f (m x)
  let nfm (x : ℝ) : ℝ := n (f (m x))
  -- Prove the surjectivity of f ∘ m using exercise2_2
  have fm_surjective (hm : SurjectiveFunction m) (hf : SurjectiveFunction f) : SurjectiveFunction fm :=
  by{
    intro z
    specialize fm z
    obtain ⟨x, hx⟩ := fm
    specialize hf z
    obtain ⟨ y , hfx⟩ :=hf
    specialize hm y
    obtain ⟨ x, hmx ⟩ := hm
    use x
    simp[hmx ,hx]
    simp [hfx, hx]
  }
  have nfm_surjective (hn : SurjectiveFunction n) (hf : SurjectiveFunction fm) : SurjectiveFunction nfm := by{
    intro z
    specialize nfm z
    obtain ⟨ y, hx ⟩ := nfm
    specialize hn z
    obtain ⟨ y, hnx ⟩ := hn
    specialize hf y
    obtain ⟨ x, hfx⟩ :=hf
    use x
    simp[hfx,hx]
    simp[hnx,hx]


  }
  exact nfm_surjective n_surjective (fm_surjective m_surjective hf)
  }
end Surjectivity





section Growth

/- Given two sequences of natural numbers `s` and `t`. We say that `s` eventually grows faster than
  `t` if for all `k : ℕ`, `s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

variable {s t : ℕ → ℕ} {k : ℕ}

/- Hint: `simp` can help you simplify expressions like the following.
  Furthermore, `gcongr` will be helpful! -/
example : (fun n ↦ n * s n) k = k * s k := by simp

lemma exercise2_5 : EventuallyGrowsFaster (fun n ↦ n * s n) s := by
  {
    intros k
    use k -- Let N = k
    intros n hn
  -- You can use the example you provided earlier to simplify the goal
    have h1 : (fun n ↦ n * s n) k = k * s k := by simp
    exact Nat.mul_le_mul_right (s n) hn

  }

/- For the following exercise, it will be useful to know that you can write `max a b`
  to take the maximum of `a` and `b`, and that this lemma holds  -/
lemma useful_fact (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

lemma exercise2_6 {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by
  {
    intros k
    specialize h₁ k -- Applying the definition of EventuallyGrowsFaster to h₁
    specialize h₂ k -- Applying the definition of EventuallyGrowsFaster to h₂

    choose N₁ hN₁ using h₁ -- Choose N₁ and unpack the proof using the choose tactic
    choose N₂ hN₂ using h₂ -- Choose N₂ and unpack the proof using the choose tactic

    let N := max N₁ N₂-- Choose N as the maximum of N₁ and N₂
    use N -- Use N as the witness for the combined sequence

    intros n hn
    have h₁ := hN₁ n (le_trans (le_max_left _ _) hn) -- Applying the chosen N₁
    have h₂ := hN₂ n (le_trans (le_max_right _ _) hn) -- Applying the chosen N₂


    calc
      k * (t₁ + t₂) n = k * t₁ n + k * t₂ n := by {
      rw [← Nat.mul_add]
      rw [@Pi.add_apply]}
      _ ≤ s₁ n + s₂ n := by gcongr

  }


/- Optional hard exercise 1:
Find a function that is nowhere zero and grows faster than itself when shifted by one. -/
lemma exercise2_7 : ∃ (s : ℕ → ℕ), EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by
  sorry


/- Optional hard exercise 2:
Show that a function that satisfies the conditions of the last
exercise, then it must necessarily tend to infinity.
The following fact will be useful. Also, the first step of the proof is already given. -/

lemma useful_fact2 {n m : ℕ} (hn : n ≥ m + 1) : ∃ k ≥ m, k + 1 = n := by
  use n - 1
  constructor
  · exact?
  · have : 1 ≤ n := by exact?
    exact?

lemma exercise2_8 (hs : EventuallyGrowsFaster (fun n ↦ s (n+1)) s) (h2s : ∀ n, s n ≠ 0) :
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, s n ≥ k := by
  have h3s : ∀ n, 1 ≤ s n := by
    intro n
    exact?
  sorry



end Growth