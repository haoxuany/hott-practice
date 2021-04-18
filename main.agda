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
  ∀ {n m p} {A : Set n} {B : A → Set m} {C : (x : A) → B x → Set p} →
  (g : {x : A} → (y : B x) → C x y) (f : (x : A) → B x) →
  (x : A) → C x (f x)
(g ∘ f) x = g (f x)

ap-preserves-function-composition :
  {A B C : Set} {x y z : A} {f : A → B} {g : B → C} →
  (p : x ≡ y) →
  ap g (ap f p) ≡ ap (g ∘ f) p
ap-preserves-function-composition refl = refl

-- (iv) identity maps to identity
ap-identity-map :
  {A : Set} {x y : A} →
  (p : x ≡ y) →
  ap (λ x → x) p ≡ p
ap-identity-map refl = refl

-- Lemma 2.3.1 transport
transport :
  {A : Set} {x y : A} →
  (P : A → Set) (p : x ≡ y) →
  P x → P y
transport _ refl x = x

-- Lemma 2.3.4 dependent action on paths
apd :
  {A : Set} {B : A → Set} {x y : A} →
  (f : (x : A) → B x) →
  (p : x ≡ y) →
  transport B p (f x) ≡ f y
apd f refl = refl

-- Lemma 2.3.5 non-dependent transport moves around ap path
transport-const :
  {A B : Set} {x y : A} →
  (p : x ≡ y) (b : B) →
  transport (λ _ → B) p b ≡ b
transport-const refl b = refl

-- Lemma 2.3.8 relation between dependent and nondependent transport
apd-ap :
  {A B : Set} {x y : A} →
  (f : A → B) (p : x ≡ y) →
  apd f p ≡ (transport-const p (f x)) ∙ (ap f p)
apd-ap f refl = refl

-- Lemma 2.3.9 transport unrolling
transport-unroll :
  {A : Set} {P : A → Set} {x y z : A} →
  (p : x ≡ y) (q : y ≡ z) →
  {u : P x} → transport P q (transport P p u) ≡ transport P (p ∙ q) u
transport-unroll refl refl = refl

-- Lemma 2.3.10 transport over ap
transport-ap :
  {A B : Set} {P : B → Set} {x y : A} →
  (f : A → B) (p : x ≡ y) →
  {u : P (f x)} → transport (P ∘ f) p u ≡ transport P (ap f p) u
transport-ap f refl = refl

-- Lemma 2.3.11 transport naturality
transport-natural :
  {A : Set} {P Q : A → Set} {x y : A} →
  (f : (x : A) → P x → Q x) (p : x ≡ y) →
  {u : P x} → transport Q p (f x u) ≡ f y (transport P p u)
transport-natural f refl = refl

-- Definition 2.4.1 homotopy between functions
homotopy : {A : Set} {P : A → Set} → (f g : (x : A) → P x) → Set
homotopy {A = A} f g = (x : A) → f x ≡ g x

_~_ = homotopy
infixl 30 _~_

-- Lemma 2.4.2 homotopy is an equivalence relation
homotopy-refl :
  {A : Set} {P : A → Set} →
  (f : (x : A) → P x) → f ~ f
homotopy-refl f x = refl

homotopy-sym :
  {A : Set} {P : A → Set} →
  (f g : (x : A) → P x) → f ~ g → g ~ f
homotopy-sym f g f-g-hom x = inv (f-g-hom x)

homotopy-trans :
  {A : Set} {P : A → Set} →
  (f g h : (x : A) → P x) → f ~ g → g ~ h → f ~ h
homotopy-trans f g h f-g-hom g-h-hom x = (f-g-hom x) ∙ (g-h-hom x)

-- Lemma 2.4.3 homotopies are natural transformations between functions
homotopy-natural :
  {A B : Set} {x y : A} {p : x ≡ y} →
  (f g : A → B) (H : f ~ g) →
  (H x) ∙ (ap g p) ≡ (ap f p) ∙ (H y)
homotopy-natural {x = x} {p = refl} f g h = right-id (h x)

-- Corollary 2.4.4 naturality over identity
homotopy-natural-id :
  {A : Set} →
  (f : A → A) (H : f ~ (λ x → x)) →
  {x : A} → H (f x) ≡ ap f (H x)
homotopy-natural-id f H {x = x} = remove-ends (H x) (inv commute-square)
  where
    f-x-path : f x ≡ x
    f-x-path = H x

    -- annoying to reason about, not hard
    replace-inline :
      {A : Set} {x y z : A} →
      {p : x ≡ y} {q q' : y ≡ z} {r : x ≡ z} →
      p ∙ q ≡ r → q ≡ q' → p ∙ q' ≡ r
    replace-inline {p = refl} q-r q-q' = (inv q-q') ∙ q-r

    commute-square : (ap f (H x)) ∙ (H x) ≡ (H (f x)) ∙ (H x)
    commute-square = inv
      (replace-inline
      (homotopy-natural {p = f-x-path} f (λ x → x) H)
      (ap-identity-map (H x)))

    -- annoying to reason about, not hard
    remove-ends :
      {A : Set} {x y z : A} →
      {p p' : x ≡ y} → (q : y ≡ z) →
      p ∙ q ≡ p' ∙ q → p ≡ p'
    remove-ends {p = p} {p' = p'} refl p-q-eq-p'-eq =
      (inv (right-id p)) ∙ p-q-eq-p'-eq ∙ (right-id p')
