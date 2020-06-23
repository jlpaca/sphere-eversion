import analysis.normed_space.finite_dimension
import analysis.calculus.times_cont_diff
import measure_theory.set_integral

/-!
# Basic definitions and properties of loops
-/

section uncurry
open function

variables {α β γ δ : Type*}

example (f : α → β → γ → δ) : (α × β) × γ → δ :=
(uncurry ∘ uncurry) f 

/-- Records a way to turn an element of `α` into a function from `β` to `γ`. -/
class has_uncurry (α : Type*) (β : out_param Type*) (γ : out_param Type*) := (uncurry : α → (β → γ))

notation `↿`:max x:max := has_uncurry.uncurry x

instance has_uncurry_base : has_uncurry (α → β) α β := ⟨id⟩

instance has_uncurry_induction [has_uncurry β γ δ] : has_uncurry (α → β) (α × γ) δ := 
⟨λ f p, ↿(f p.1) p.2⟩

variables (f : α → β → γ) (g : α → β → γ → δ)

example (a : α) (b : β) :  ↿f (a, b)=  f a b := rfl

example (a : α) (b : β) (c : γ) :  ↿g (a, b, c)=  g a b c := rfl

example :  ↿f = uncurry f := funext (λ _, rfl)

end uncurry

open set function finite_dimensional
open_locale big_operators topological_space

def nhds_set {α : Type*} [topological_space α] (s : set α) : filter α :=
Sup (nhds '' s)

variables {E : Type*} [normed_group E] [normed_space ℝ E]
          {F : Type*} [normed_group F] [normed_space ℝ F] [finite_dimensional ℝ F]

local notation `d` := findim ℝ F

local notation `smooth_on` := times_cont_diff_on ℝ ⊤

def smooth_at (f : E → F) (x : E) : Prop := ∃ s ∈ 𝓝 x, smooth_on f s

section surrounding_points

def affinely_independent {n : ℕ} (p : fin n → F) : Prop :=
sorry

-- def:surrounds_points
structure surrounding_pts (f : F) (p : fin (d + 1) → F) (w : fin (d + 1) → ℝ) : Prop :=
(indep : affinely_independent p)
(w_pos : ∀ i, 0 < w i)
(w_sum : ∑ i, w i = 1)
(avg : ∑ i, (w i) • (p i) = f)


def surrounded (f : F) (s : set F) : Prop :=
∃ p w, surrounding_pts f p w ∧ ∀ i, p i ∈ s

-- lem:int_cvx alternative formulation, compare int_cvx.lean
lemma surrounded_of_convex_hull {f : F} {s : set F} (hs : is_open s) (hsf : f ∈ convex_hull s) : surrounded f s :=
begin
  
  sorry
end

-- lem:smooth_convex_hull
lemma smooth_surrounding {x : F} {p w} (h : surrounding_pts x p w) : 
  ∃ w : F → (fin (d+1) → F) → (fin (d+1) → ℝ),
  ∀ᶠ y in 𝓝 x, ∀ᶠ q in  𝓝 p, smooth_at (uncurry w) (y, q) ∧ 
                              ∀ i, w y q i ∈ Ioo (0 : ℝ) 1 ∧ 
                              ∑ i, w y q i • q i = y :=
begin
  sorry
end

end surrounding_points

set_option old_structure_cmd true

variables (E F)

structure loop :=
(to_fun : ℝ → F)
(per' : ∀ t, to_fun (t + 1) = to_fun t)

instance : has_coe_to_fun (loop F) := ⟨_, λ γ, γ.to_fun⟩

/-- Any function `φ : α → loop F` can be seen as a function `α × ℝ → F`. -/
instance has_uncurry_loop {α : Type*} : has_uncurry (α → loop F) (α × ℝ) F := ⟨λ φ p, φ p.1 p.2⟩

variables {E F}

namespace loop

/-- Periodicity of loops restated in terms of the function coercion. -/
lemma per (γ : loop F) : ∀ t, γ (t + 1) = γ t :=
loop.per' γ

/-- The average value of a loop. -/
noncomputable
def average [measurable_space F] [borel_space F] (γ : loop F) : F := ∫ x in Icc 0 1, (γ x)

/-- A loop `γ` surrounds a point `x` if `x` is surrounded by values of `γ`. -/
def surrounds (γ : loop F) (x : F) : Prop := 
  ∃ t w : fin (d + 1) → ℝ, surrounding_pts x (γ ∘ t) w

end loop

local notation `I` := Icc (0 : ℝ) 1

lemma surrounding_loop_of_convex_hull {f b : F} {O : set F} (hs : is_open O) (hsf : f ∈ convex_hull O) (hb : b ∈ O) : 
∃ γ : ℝ → loop F, continuous_on ↿γ (set.prod I univ) ∧ 
                  ∀ t, γ t 0 = b ∧
                  ∀ s, γ 0 s = b ∧
                  ∀ (t ∈ I) s, γ t s ∈ O ∧
                  (γ 1).surrounds f :=
begin
  sorry
end

structure surrounding_family (g b : E → F) (γ : E → ℝ → loop F) (U : set E) : Prop :=
(base : ∀ x t, γ x t 0 = b x)
(t₀ : ∀ x s, γ x 0 s = b x)
(surrounds : ∀ x, (γ x 1).surrounds $ g x)
(cont : continuous ↿γ)

variables {g b : E → F} {Ω : set (E × F)} {U K : set E}

lemma local_loops
  {x₀ : E}
  (hΩ_op : ∀ᶠ x in 𝓝 x₀, is_open (prod.mk x ⁻¹' Ω)) 
  (hg : ∀ᶠ x in 𝓝 x₀, continuous_at g x) (hb : ∀ᶠ x in 𝓝 x₀, continuous_at b x)
  (hb_in : ∀ᶠ x in 𝓝 x₀, (x, b x) ∈ Ω) 
  (hconv : ∀ᶠ x in 𝓝 x₀, g x ∈ convex_hull (prod.mk x ⁻¹' Ω)) :
∃ γ : E → ℝ → loop F, ∀ᶠ x in 𝓝 x₀, ∀ (t ∈ I) s, 
  (x, γ x t s) ∈ Ω ∧
  γ x 0 s = b x ∧
  (γ x 1).surrounds (g x) ∧
  continuous_at ↿γ ((x, t, s) : E × ℝ × ℝ) :=
begin
  
  sorry
end

lemma satisfied_or_refund {γ₀ γ₁ : E → ℝ → loop F} (h₀ : surrounding_family g b γ₀ U) :
∃ γ : ℝ → E → ℝ → loop F, 
  (∀ τ ∈ I, surrounding_family g b (γ τ) U) ∧ 
  γ 0 = γ₀ ∧
  γ 1 = γ₁ ∧
  (∀ (τ ∈ I) (x ∈ U) (t ∈ I) s, continuous_at ↿γ (τ, x, t, s)) :=
begin
  
  sorry
end

-- Manque 1.13, 1.14, 1.15

lemma exists_loops [measurable_space F] [borel_space F] 
  (hU : is_open U) (hK : compact K) (hKU : K ⊆ U) 
  (hΩ_op : ∀ x ∈ U, is_open (prod.mk x ⁻¹' Ω))
  (hΩ_conn : ∀ x ∈ U, is_connected (prod.mk x ⁻¹' Ω)) 
  (hg : ∀ x ∈ U, smooth_at g x) (hb : ∀ x ∈ U, smooth_at b x) (hb_in : ∀ x ∈ U, (x, b x) ∈ Ω) 
  (hgK : ∀ᶠ x in nhds_set K, g x = b x) (hconv : ∀ x ∈ U, g x ∈ convex_hull (prod.mk x ⁻¹' Ω)) :
  ∃ γ : E → ℝ → loop F, (∀ (x ∈ U) (t ∈ I) s, (x, γ x t s) ∈ Ω ∧
                                              γ x 0 s = b x ∧
                                              (γ x 1).average = g x ∧
                                              smooth_at ↿γ ((x, t, s) : E × ℝ × ℝ)) ∧
                        (∀ᶠ x in nhds_set K, ∀ (t ∈ I) s, γ x t s = b x)  :=
begin
  
  sorry
end
