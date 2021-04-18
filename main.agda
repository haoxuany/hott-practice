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
    horizontal-comp-simp : α ⋆ β ≡ α ∙ β
    horizontal-comp-simp = remove α β
      where
        -- not hard, just annoying to do directly.
        remove :
          {A : Set} {a b c : A} (p : a ≡ b) (q : b ≡ c) → (p ∙ refl) ∙ q ≡ p ∙ q
        remove refl refl = refl

    horizontal-comp-simp' : α ⋆' β ≡ β ∙ α
    horizontal-comp-simp' = remove β α
      where
        remove :
          {A : Set} {a b c : A} (p : a ≡ b) (q : b ≡ c) → p ∙ (q ∙ refl) ≡ p ∙ q
        remove refl refl = refl

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
infixl 10 _~_

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

-- Definition 2.4.6 quasi-inverse
record qinv {A B : Set} (f : A → B) : Set where
  constructor _st_and_
  field
    g : B → A
    α : f ∘ g ~ λ x → x
    β : g ∘ f ~ λ x → x

-- Example 2.4.7 the identity function is a quasi-inverse
id-qinv : {A : Set} → qinv {A} {A} (λ x → x)
id-qinv = (λ x → x) st (λ x → refl) and (λ x → refl)

-- Example 2.4.8 path concats are quasi-inverses
preconcat-qinv :
  {A : Set} {x y z : A} →
  (p : x ≡ y) → qinv (λ (q : y ≡ z) → p ∙ q)
preconcat-qinv {x = x} {y = y} {z = z} p =
  g st α and β
  where
    f : y ≡ z → x ≡ z
    f q = p ∙ q

    g : x ≡ z → y ≡ z
    g pq = (inv p) ∙ pq

    α : (f ∘ g) ~ λ x → x
    α refl = simpl p
      where
        simpl : {A : Set} {x y : A} → (p : x ≡ y) → p ∙ ((inv p) ∙ refl) ≡ refl
        simpl refl = refl

    β : (g ∘ f) ~ λ x → x
    β refl = simpl p
      where
        simpl : {A : Set} {x y : A} → (p : x ≡ y) → (inv p) ∙ (p ∙ refl) ≡ refl
        simpl refl = refl

postconcat-qinv :
  {A : Set} {x y z : A} →
  (p : x ≡ y) → qinv (λ (q : z ≡ x) → q ∙ p)
postconcat-qinv {x = x} {y = y} {z = z} p =
  g st α and β
  where
    f : z ≡ x → z ≡ y
    f q = q ∙ p

    g : z ≡ y → z ≡ x
    g qp = qp ∙ (inv p)

    α : (f ∘ g) ~ λ x → x
    α refl = left-inv p

    β : (g ∘ f) ~ λ x → x
    β refl = right-inv p

-- Example 2.4.9 transport over paths induces a quasi-inverse over the inverse path
transport-qinv :
  {A : Set} {x y : A} →
  (P : A → Set) (p : x ≡ y) →
  qinv (transport P p)
transport-qinv {x = x} {y = y} P p =
  g st α and β
    where
      f : P x → P y
      f = transport P p

      g : P y → P x
      g = transport P (inv p)

      transport-equiv-paths :
        {A : Set} {x y : A} →
        (P : A → Set) (p q : x ≡ y) →
        p ≡ q → {n : P x} → transport P p n ≡ transport P q n
      transport-equiv-paths P p .p refl = refl

      transport-refl-paths :
        {A : Set} {x : A} →
        (P : A → Set) (p : x ≡ x) →
        p ≡ refl → {n : P x} → transport P p n ≡ n
      transport-refl-paths P p p-refl {n = n} =
        transport-equiv-paths P p refl p-refl {n = n}

      α : (f ∘ g) ~ λ x → x
      α x =
        (transport-unroll {P = P} (inv p) p) ∙
        (transport-refl-paths P ((inv p) ∙ p) (left-inv p) {n = x})

      β : (g ∘ f) ~ λ x → x
      β x =
        (transport-unroll {P = P} p (inv p)) ∙
        (transport-refl-paths P _ (right-inv p))

-- 2.4.10 a specific definition of equivalence
record isequiv {A B : Set} (f : A → B) : Set where
  constructor _st_also_st_
  field
    g : B → A
    α : f ∘ g ~ λ x → x
    h : B → A
    β : h ∘ f ~ λ x → x

-- (i) quasi-inverses induce equivalences
qinv-to-isequiv :
  {A B : Set} → (f : A → B) → qinv f → isequiv f
qinv-to-isequiv f (g st α and β) = g st α also g st β

-- (ii) equivalences induce quasi-inverses
isequiv-to-qinv :
  {A B : Set} → (f : A → B) → isequiv f → qinv f
isequiv-to-qinv {A} {B} f (g st α also h st β) = g st α and β'
  where
    g~h∘f∘g : g ~ (h ∘ (f ∘ g))
    g~h∘f∘g x = inv (β (g x))

    h∘f∘g~h : (h ∘ (f ∘ g)) ~ h
    h∘f∘g~h x = ap h (α x)

    g~h : g ~ h
    g~h = homotopy-trans _ _ _ g~h∘f∘g h∘f∘g~h

    β' : g ∘ f ~ λ x → x
    β' x = g~h (f x) ∙ (β x)

-- Definition 2.4.11 equivalence between types
record _≃_ (A B : Set) : Set where
  constructor _withequiv_
  field
    f : A → B
    e : isequiv f

-- Lemma 2.4.12 type equivalence is a equivalence relation
equiv-refl : {A : Set} → A ≃ A
equiv-refl =
  (λ x → x) withequiv
  (qinv-to-isequiv (λ x → x) ((λ x → x) st (λ x → refl) and (λ x → refl)))

equiv-sym : {A B : Set} → A ≃ B → B ≃ A
equiv-sym (f withequiv equiv) with (isequiv-to-qinv f equiv)
... | g st α and β = g withequiv qinv-to-isequiv g (f st β and α)

equiv-trans : {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
equiv-trans (fab withequiv equivab) (fbc withequiv equivbc)
  with (isequiv-to-qinv fab equivab) | (isequiv-to-qinv fbc equivbc)
... | gab st αab and βab | gbc st αbc and βbc =
      (fbc ∘ fab) withequiv
      (qinv-to-isequiv (fbc ∘ fab) ((gab ∘ gbc)
        st (λ x → ap fbc (αab (gbc x)) ∙ (αbc x))
        and λ x → ap gab (βbc (fab x)) ∙ (βab x)))
