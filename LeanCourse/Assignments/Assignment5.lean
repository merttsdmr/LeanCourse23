import LeanCourse.Common
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.FieldTheory.Minpoly.Basic
set_option linter.unusedVariables false
noncomputable section
open Real Function BigOperators
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 7 and 8, all sections.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 17.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


section LinearMap

variable {R M₁ M₂ N : Type*} [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N]
  [Module R M₁] [Module R M₂] [Module R N]

/- Define the coproduct of two linear maps that send (x, y) ↦ f x + g y. -/

def exercise5_1 (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) : M₁ × M₂ →ₗ[R] N where
  toFun := fun (x : M₁ × M₂) ↦ f x.1 +g x.2
  map_add' := by
    intro x y
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    rw [@add_add_add_comm]
  map_smul' := by
    intro r x
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply, smul_add]


example (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) (x : M₁) (y : M₂) :
  exercise5_1 f g (x, y) = f x + g y := rfl -- should be rfl


end LinearMap

section Ring
variable {R : Type*} [CommRing R]


/- Let's define ourselves what it means to be a unit in a ring and then
  prove that the units of a ring form a group.
  Hint: I recommend that you first prove that the product of two units is again a unit,
  and that you define the inverse of a unit separately using `Exists.choose`.
  Hint 2: to prove associativity, use something like `intros; ext; apply mul_assoc`
  (`rw` doesn't work well because of the casts) -/

#check Exists.choose
#check Exists.choose_spec
def IsAUnit (x : R) : Prop := ∃ y, y * x = 1


def unit_inverse (x : R) (hx : IsAUnit x) : R :=
  (Exists.choose hx)


lemma mul_is_unit {x y : R} (hx : IsAUnit x) (hy : IsAUnit y) : IsAUnit (x * y) := by
      rw[IsAUnit] at hx
      rw[IsAUnit] at hy
      rw[IsAUnit]
      obtain ⟨z1, hxx⟩ := hx
      obtain ⟨z2, hyy⟩ := hy
      use z2*z1
      sorry

lemma unit_inverse_is_unit {x : R} (hx : IsAUnit x) : IsAUnit (unit_inverse x hx) :=by
  rw[IsAUnit] at *
  rw[unit_inverse] at *
  obtain ⟨y, hy⟩ :=hx
  use x
  rw[mul_comm]
  exact Exists.choose_spec hx






instance exercise5_2 : Group {x : R // IsAUnit x} where
  mul x y := ⟨ x.1*y.1, mul_is_unit x.2 y.2⟩
  mul_assoc x y z:= by {intros; ext; apply mul_assoc}
  one := ⟨1, by {
  use 1
  simp}⟩
  one_mul x := by ext; apply one_mul
  mul_one x := by ext; apply mul_one
  inv x := ⟨unit_inverse x.1 x.2, unit_inverse_is_unit x.2 ⟩
  mul_left_inv x:= by
   ext
   simp
   sorry

-- you have the correct group structure if this is true by `rfl`
example (x y : {x : R // IsAUnit x}) : (↑(x * y) : R) = ↑x * ↑y := rfl

end Ring



/- The Frobenius morphism in a field of characteristic p is the map `x ↦ x ^ p`.
Let's prove that the Frobenius morphism is additive, without using that
fact from the library. -/
#check CharP.cast_eq_zero_iff
#check Finset.sum_congr
variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharP K p] in
open Nat Finset in
lemma exercise5_3 (x y : K) : (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow]
  have h2 : p.Prime := hp.out
  have h3 : 0 < p := h2.pos
  have h4 : range p = insert 0 (Ioo 0 p)
  · ext (_|_) <;> simp [h3]
  have h5 : ∀ i ∈ Ioo 0 p, p ∣ Nat.choose p i := by sorry

  have h6 : ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i = 0 :=
  calc
    _ =  ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * 0 := by sorry
    _ = 0 := by {
      simp
    }
  have h7 : ∑ m in range (p + 1), x ^ m * y ^ (p - m) * ↑(Nat.choose p m)= x^p+∑ m in Ioo 0 p, x ^ m * y ^ (p - m) * ↑(Nat.choose p m)+y^p := by sorry
  /-from h7 we have  the middle term is zero hence we have the result.-/
  rw[h7]
  rw[h6]
  simp


/- Let's prove that if `M →ₗ[R] M` forms a module over `R`, then `R` must be a commutative ring.
  To prove this we have to additionally assume that `M` contains at least two elements, and
`smul_eq_zero : r • x = 0 ↔ r = 0 ∨ x = 0` (this is given by the `NoZeroSMulDivisors` class).
-/
#check exists_ne
lemma exercise5_4 {R M M' : Type*} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial M]
    [NoZeroSMulDivisors R M] [Module R (M →ₗ[R] M)]
    (h : ∀ (r : R) (f : M →ₗ[R] M) (x : M), (r • f) x = r • f x)
    (r s : R) : r * s = s * r := by {
  obtain ⟨m1, m2, h1⟩ : ∃ (m1 m2 : M), m1 ≠ m2 := exists_pair_ne M
  let f := (LinearMap.id : M →ₗ[R] M)
  have h1 : s • r • m1 = s• r• f m1 :=by exact rfl
  have h2 : s• r• f m1 = s• f (r • m1) := by exact h1
  have h2 :  s• f (r • m1) =  f (s• r • m1) := by exact h1
  have h3 : f (s• r • m1) = s• f (r • m1) := by exact h1
  have h4 : s• f (r • m1) =r• s• f m1 := by sorry
  have h5 : (s• r - r • s)• m1 = 0 := by {
    rw [@sub_smul]
    sorry
    }
  have h6 : m1 ≠ 0 := by sorry
  sorry
  /-i tried to make a proper proof but in some places i struggled to find appropriate function.-/

}
