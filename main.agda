{-# OPTIONS --without-K #-}

-- Universes
open import Agda.Primitive

module main where

-- I don't really understand exactly which equality gets imported in agda if
-- I try to import the builtin, so define the sane MLTT one here.

infixl 4 _≡_
data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a
{-# BUILTIN EQUALITY _≡_ #-}

-- Lemma 2.1.1 all paths have inverses
inv : {A : Set} {a b : A} → a ≡ b → b ≡ a
inv refl = refl

-- This is painful to type so I'll just stick with inv most of the time
_⁻¹ = inv

-- Lemma 2.1.2 any two paths with connecting endpoint compose
trans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl p = p

_∙_ = trans
infixl 50 _∙_

-- Lemma 2.1.4 types are groupoids
-- (i) left and right identity laws
left-id : {A : Set} {a b : A} → (p : a ≡ b) → refl ∙ p ≡ p
left-id refl = refl

right-id : {A : Set} {a b : A} → (p : a ≡ b) → p ∙ refl ≡ p
right-id refl = refl

-- (ii) inverses compose to identity
left-inv : {A : Set} {a b : A} → (p : a ≡ b) → (inv p) ∙ p ≡ refl
left-inv refl = refl

right-inv : {A : Set} {a b : A} → (p : a ≡ b) → p ∙ (inv p) ≡ refl
right-inv refl = refl

-- (iii) inverse of inverse gives an equal path
inv-inv : {A : Set} {a b : A} → (p : a ≡ b) → inv (inv p) ≡ p
inv-inv refl = refl

-- (iv) associativity of path composition
assoc :
  {A : Set} {a b c d : A} →
  (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) →
  p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
assoc refl q r = refl

-- Theorem 2.1.6 Eckmann-Hilton
loop-space : (A : Set) (a : A) → Set
loop-space A a = a ≡ a

Ω = loop-space

loop-space-2d : (A : Set) (a : A) → Set
loop-space-2d A a = loop-space (a ≡ a) (refl {a = a})

Ω² = loop-space-2d

_∙ᵣ_ :
  {A : Set} {a b c : A} {p q : a ≡ b} →
  (α : p ≡ q) (r : b ≡ c) →
  (p ∙ r ≡ q ∙ r)
α ∙ᵣ refl = (right-id _) ∙ α ∙ (inv (right-id _))

-- My emacs setup doesn't show subscript l for some reason, or I typed it wrong
_∙ₗ_ :
  {A : Set} {a b c : A} {r s : b ≡ c} →
  (q : a ≡ b) (β : r ≡ s) →
  (q ∙ r ≡ q ∙ s)
refl ∙ₗ β = β

horizontal-comp : {A : Set} {a b c : A} →
  {p q : a ≡ b} {r s : b ≡ c} →
  (α : p ≡ q) (β : r ≡ s) →
  (p ∙ r ≡ q ∙ s)
horizontal-comp {q = q} {r = r} α β = (α ∙ᵣ r) ∙ (q ∙ₗ β)

_⋆_ = horizontal-comp

horizontal-comp' : {A : Set} {a b c : A}
  {p q : a ≡ b} {r s : b ≡ c} →
  (α : p ≡ q) (β : r ≡ s) →
  (p ∙ r ≡ q ∙ s)
horizontal-comp' {p = p} {s = s} α β = (p ∙ₗ β) ∙ (α ∙ᵣ s)

_⋆'_ = horizontal-comp'

-- two compositions agree
comp-agree : {A : Set} {a : A} → (α β : loop-space-2d A a) → α ⋆ β ≡ α ⋆' β
comp-agree α β = comp-agree' α β
  where
    -- (more generally at two free endpoints, or we won't get path induction)
    comp-agree' : {A : Set} {a : A} {p r : a ≡ a} → (α : p ≡ refl) (β : refl ≡ r) → α ⋆ β ≡ α ⋆' β
    comp-agree' refl refl = refl

eckmann-hilton : {A : Set} {a : A} → (α β : loop-space-2d A a) → α ∙ β ≡ β ∙ α
eckmann-hilton α β = (inv horizontal-comp-simp) ∙ (comp-agree α β) ∙ horizontal-comp-simp'
  where
    -- not hard, just annoying to do directly.
    remove-annoying-refl :
      {A : Set} {a b c : A} (p : a ≡ b) (q : b ≡ c) → (p ∙ refl) ∙ q ≡ p ∙ q
    remove-annoying-refl refl refl = refl
    remove-annoying-refl' :
      {A : Set} {a b c : A} (p : a ≡ b) (q : b ≡ c) → p ∙ (q ∙ refl) ≡ p ∙ q
    remove-annoying-refl' refl refl = refl

    horizontal-comp-simp : α ⋆ β ≡ α ∙ β
    horizontal-comp-simp = remove-annoying-refl α β

    horizontal-comp-simp' : α ⋆' β ≡ β ∙ α
    horizontal-comp-simp' = remove-annoying-refl' β α

-- Lemma 2.2.1 action on paths preserve path equality
ap :
  {A B : Set} {x y : A} →
  (f : A → B) (p : x ≡ y) → f x ≡ f y
ap f refl = refl

-- Lemma 2.2.2 functions are functors
-- (i) functions preserves composition
ap-preserves-composition :
  {A B : Set} {x y z : A} {f : A → B} →
  (p : x ≡ y) (q : y ≡ z) →
  ap f (p ∙ q) ≡ (ap f p) ∙ (ap f q)
ap-preserves-composition refl q = refl

-- (ii) functions preserves inverses
ap-preserves-inverses :
  {A B : Set} {x y z : A} {f : A → B} →
  (p : x ≡ y) →
  ap f (inv p) ≡ inv (ap f p)
ap-preserves-inverses refl = refl

-- (iii) functors compose
_∘_ :
  {A B C : Set} →
  (g : B → C) (f : A → B) →
  A → C
(g ∘ f) x = g (f x)

ap-preserves-function-composition :
  {A B C : Set} {x y z : A} {f : A → B} {g : B → C} →
  (p : x ≡ y) →
  ap g (ap f p) ≡ ap (g ∘ f) p
ap-preserves-function-composition refl = refl

-- (iv) identity maps to identity
ap-identity-map :
  {A B : Set} {x y : A} →
  (p : x ≡ y) →
  ap (λ x → x) p ≡ p
ap-identity-map refl = refl


