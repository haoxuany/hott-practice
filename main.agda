{-# OPTIONS --without-K #-}

-- Universes
open import Agda.Primitive

module main where

-- I don't really understand exactly which equality gets imported in agda if
-- I try to import the builtin, so define the sane MLTT one here.

infixl 4 _≡_
data _≡_ {n : Level} {A : Set n} : A → A → Set n where
  refl : {a : A} → a ≡ a
{-# BUILTIN EQUALITY _≡_ #-}

-- Lemma 2.1.1 all paths have inverses
inv : ∀ {n} {A : Set n} {a b : A} → a ≡ b → b ≡ a
inv refl = refl

-- This is painful to type so I'll just stick with inv most of the time
_⁻¹ = inv

-- Lemma 2.1.2 any two paths with connecting endpoint compose
trans : ∀ {n} {A : Set n} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl p = p

_∙_ = trans
infixl 50 _∙_

-- Lemma 2.1.4 types are groupoids
-- (i) left and right identity laws
left-id : ∀ {n} {A : Set n} {a b : A} → (p : a ≡ b) → refl ∙ p ≡ p
left-id refl = refl

right-id : ∀ {n} {A : Set n} {a b : A} → (p : a ≡ b) → p ∙ refl ≡ p
right-id refl = refl

-- (ii) inverses compose to identity
left-inv : ∀ {n} {A : Set n} {a b : A} → (p : a ≡ b) → (inv p) ∙ p ≡ refl
left-inv refl = refl

right-inv : ∀ {n} {A : Set n} {a b : A} → (p : a ≡ b) → p ∙ (inv p) ≡ refl
right-inv refl = refl

-- (iii) inverse of inverse gives an equal path
inv-inv : ∀ {n} {A : Set n} {a b : A} → (p : a ≡ b) → inv (inv p) ≡ p
inv-inv refl = refl

-- (iv) associativity of path composition
assoc :
  ∀ {n} {A : Set n} {a b c d : A} →
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
  ∀ {n} {A : Set n} {a b c : A} {p q : a ≡ b} →
  (α : p ≡ q) (r : b ≡ c) →
  (p ∙ r ≡ q ∙ r)
α ∙ᵣ refl = (right-id _) ∙ α ∙ (inv (right-id _))

-- My emacs setup doesn't show subscript l for some reason, or I typed it wrong
_∙ₗ_ :
  ∀ {n} {A : Set n} {a b c : A} {r s : b ≡ c} →
  (q : a ≡ b) (β : r ≡ s) →
  (q ∙ r ≡ q ∙ s)
refl ∙ₗ β = β

horizontal-comp : ∀ {n} {A : Set n} {a b c : A} →
  {p q : a ≡ b} {r s : b ≡ c} →
  (α : p ≡ q) (β : r ≡ s) →
  (p ∙ r ≡ q ∙ s)
horizontal-comp {q = q} {r = r} α β = (α ∙ᵣ r) ∙ (q ∙ₗ β)

_⋆_ = horizontal-comp

horizontal-comp' : ∀ {n} {A : Set n} {a b c : A}
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
  ∀ {n m} {A : Set n} {B : Set m} {x y : A} →
  (f : A → B) (p : x ≡ y) → f x ≡ f y
ap f refl = refl

-- Lemma 2.2.2 functions are functors
-- (i) functions preserves composition
ap-preserves-composition :
  ∀ {n m} {A : Set n} {B : Set m} {x y z : A} {f : A → B} →
  (p : x ≡ y) (q : y ≡ z) →
  ap f (p ∙ q) ≡ (ap f p) ∙ (ap f q)
ap-preserves-composition refl q = refl

-- (ii) functions preserves inverses
ap-preserves-inverses :
  ∀ {n m} {A : Set n} {B : Set m} {x y z : A} {f : A → B} →
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
  ∀ {n} {A B C : Set n} {x y z : A} {f : A → B} {g : B → C} →
  (p : x ≡ y) →
  ap g (ap f p) ≡ ap (g ∘ f) p
ap-preserves-function-composition refl = refl

-- (iv) identity maps to identity
ap-identity-map :
  ∀ {n} {A : Set n} {x y : A} →
  (p : x ≡ y) →
  ap (λ x → x) p ≡ p
ap-identity-map refl = refl

-- Lemma 2.3.1 transport
transport :
  ∀ {n m} {A : Set n} {x y : A} →
  (P : A → Set m) (p : x ≡ y) →
  P x → P y
transport _ refl x = x

-- Lemma 2.3.4 dependent action on paths
apd :
  ∀ {n m} {A : Set n} {B : A → Set m} {x y : A} →
  (f : (x : A) → B x) →
  (p : x ≡ y) →
  transport B p (f x) ≡ f y
apd f refl = refl

-- Lemma 2.3.5 non-dependent transport moves around ap path
transport-const :
  ∀ {n} {A B : Set n} {x y : A} →
  (p : x ≡ y) (b : B) →
  transport (λ _ → B) p b ≡ b
transport-const refl b = refl

-- Lemma 2.3.8 relation between dependent and nondependent transport
apd-ap :
  ∀ {n} {A B : Set n} {x y : A} →
  (f : A → B) (p : x ≡ y) →
  apd f p ≡ (transport-const p (f x)) ∙ (ap f p)
apd-ap f refl = refl

-- Lemma 2.3.9 transport unrolling
transport-unroll :
  ∀ {n m} {A : Set n} {P : A → Set m} {x y z : A} →
  (p : x ≡ y) (q : y ≡ z) →
  {u : P x} → transport P q (transport P p u) ≡ transport P (p ∙ q) u
transport-unroll refl refl = refl

-- Lemma 2.3.10 transport over ap
transport-ap :
  ∀ {n m} {A B : Set n} {P : B → Set m} {x y : A} →
  (f : A → B) (p : x ≡ y) →
  {u : P (f x)} → transport (P ∘ f) p u ≡ transport P (ap f p) u
transport-ap f refl = refl

-- Lemma 2.3.11 transport naturality
transport-natural :
  ∀ {n m} {A : Set n} {P Q : A → Set m} {x y : A} →
  (f : (x : A) → P x → Q x) (p : x ≡ y) →
  {u : P x} → transport Q p (f x u) ≡ f y (transport P p u)
transport-natural f refl = refl

-- Definition 2.4.1 homotopy between functions
homotopy : ∀ {n m} {A : Set n} {P : A → Set m} → (f g : (x : A) → P x) → Set (n ⊔ m)
homotopy {A = A} f g = (x : A) → f x ≡ g x

_~_ = homotopy
infixl 10 _~_

-- Lemma 2.4.2 homotopy is an equivalence relation
homotopy-refl :
  ∀ {n m} {A : Set n} {P : A → Set m} →
  (f : (x : A) → P x) → f ~ f
homotopy-refl f x = refl

homotopy-sym :
  ∀ {n m} {A : Set n} {P : A → Set m} →
  (f g : (x : A) → P x) → f ~ g → g ~ f
homotopy-sym f g f-g-hom x = inv (f-g-hom x)

homotopy-trans :
  ∀ {n m} {A : Set n} {P : A → Set m} →
  (f g h : (x : A) → P x) → f ~ g → g ~ h → f ~ h
homotopy-trans f g h f-g-hom g-h-hom x = (f-g-hom x) ∙ (g-h-hom x)

-- Lemma 2.4.3 homotopies are natural transformations between functions
homotopy-natural :
  ∀ {n} {A B : Set n} {x y : A} {p : x ≡ y} →
  (f g : A → B) (H : f ~ g) →
  (H x) ∙ (ap g p) ≡ (ap f p) ∙ (H y)
homotopy-natural {x = x} {p = refl} f g h = right-id (h x)

-- Corollary 2.4.4 naturality over identity
homotopy-natural-id :
  ∀ {n} {A : Set n} →
  (f : A → A) (H : f ~ (λ x → x)) →
  {x : A} → H (f x) ≡ ap f (H x)
homotopy-natural-id f H {x = x} = remove-ends (H x) (inv commute-square)
  where
    f-x-path : f x ≡ x
    f-x-path = H x

    -- annoying to reason about, not hard
    replace-inline :
      ∀ {n} {A : Set n} {x y z : A} →
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
      ∀ {n} {A : Set n} {x y z : A} →
      {p p' : x ≡ y} → (q : y ≡ z) →
      p ∙ q ≡ p' ∙ q → p ≡ p'
    remove-ends {p = p} {p' = p'} refl p-q-eq-p'-eq =
      (inv (right-id p)) ∙ p-q-eq-p'-eq ∙ (right-id p')

-- Definition 2.4.6 quasi-inverse
record qinv {n m : Level} {A : Set n} {B : Set m} (f : A → B) : Set (n ⊔ m) where
  constructor _st_and_
  field
    g : B → A
    α : f ∘ g ~ λ x → x
    β : g ∘ f ~ λ x → x

-- Example 2.4.7 the identity function is a quasi-inverse
id-qinv : ∀ {n} {A : Set n} → qinv {A = A} {B = A} (λ x → x)
id-qinv = (λ x → x) st (λ x → refl) and (λ x → refl)

-- Example 2.4.8 path concats are quasi-inverses
preconcat-qinv :
  ∀ {n} {A : Set n} {x y z : A} →
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
        simpl : ∀ {n} {A : Set n} {x y : A} → (p : x ≡ y) → p ∙ ((inv p) ∙ refl) ≡ refl
        simpl refl = refl

    β : (g ∘ f) ~ λ x → x
    β refl = simpl p
      where
        simpl : ∀ {n} {A : Set n} {x y : A} → (p : x ≡ y) → (inv p) ∙ (p ∙ refl) ≡ refl
        simpl refl = refl

postconcat-qinv :
  ∀ {n} {A : Set n} {x y z : A} →
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
  ∀ {n m} {A : Set n} {x y : A} →
  (P : A → Set m) (p : x ≡ y) →
  qinv (transport P p)
transport-qinv {x = x} {y = y} P p =
  g st α and β
    where
      f : P x → P y
      f = transport P p

      g : P y → P x
      g = transport P (inv p)

      transport-equiv-paths :
        ∀ {n m} {A : Set n} {x y : A} →
        (P : A → Set m) (p q : x ≡ y) →
        p ≡ q → {n : P x} → transport P p n ≡ transport P q n
      transport-equiv-paths P p .p refl = refl

      transport-refl-paths :
        ∀ {n m} {A : Set n} {x : A} →
        (P : A → Set m) (p : x ≡ x) →
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
record isequiv {n m : Level} {A : Set n} {B : Set m} (f : A → B) : Set (n ⊔ m) where
  constructor _st_also_st_
  field
    g : B → A
    α : f ∘ g ~ λ x → x
    h : B → A
    β : h ∘ f ~ λ x → x

-- (i) quasi-inverses induce equivalences
qinv-to-isequiv :
  ∀ {n m} {A : Set n} {B : Set m} → (f : A → B) → qinv f → isequiv f
qinv-to-isequiv f (g st α and β) = g st α also g st β

-- (ii) equivalences induce quasi-inverses
isequiv-to-qinv :
  ∀ {n m} {A : Set n} {B : Set m} → (f : A → B) → isequiv f → qinv f
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
record _≃_ {n : Level} (A B : Set n) : Set n where
  constructor _withequiv_
  field
    f : A → B
    e : isequiv f

-- Lemma 2.4.12 type equivalence is a equivalence relation
equiv-refl : ∀ {n} {A : Set n} → A ≃ A
equiv-refl =
  (λ x → x) withequiv
  (qinv-to-isequiv (λ x → x) ((λ x → x) st (λ x → refl) and (λ x → refl)))

equiv-sym : ∀ {n} {A B : Set n} → A ≃ B → B ≃ A
equiv-sym (f withequiv equiv) with (isequiv-to-qinv f equiv)
... | g st α and β = g withequiv qinv-to-isequiv g (f st β and α)

equiv-trans : ∀ {n} {A B C : Set n} → A ≃ B → B ≃ C → A ≃ C
equiv-trans (fab withequiv equivab) (fbc withequiv equivbc)
  with (isequiv-to-qinv fab equivab) | (isequiv-to-qinv fbc equivbc)
... | gab st αab and βab | gbc st αbc and βbc =
      (fbc ∘ fab) withequiv
      (qinv-to-isequiv (fbc ∘ fab) ((gab ∘ gbc)
        st (λ x → ap fbc (αab (gbc x)) ∙ (αbc x))
        and λ x → ap gab (βbc (fab x)) ∙ (βab x)))

record _×_ {n m : Level} (A : Set n) (B : Set m) : Set (n ⊔ m) where
  constructor _,,_
  field
    fst : A
    snd : B

fst : ∀ {n m} {A : Set n} {B : Set m} → A × B → A
fst (fst ,, snd) = fst

snd : ∀ {n m} {A : Set n} {B : Set m} → A × B → B
snd (fst ,, snd) = snd

-- Function 2.6.1 a path between products induces a pair of paths between elements
product-path-to-elem-path :
  ∀ {n m} {A : Set n} {B : Set m} {x y : A × B} →
  x ≡ y → (fst x ≡ fst y) × (snd x ≡ snd y)
product-path-to-elem-path refl = refl ,, refl

-- Theorem 2.6.2 product path to element paths is an equivalence
product-path-to-elem-path-equiv :
  ∀ {n m} {A : Set n} {B : Set m} {x y : A × B} →
  isequiv (product-path-to-elem-path {A = A} {B = B} {x = x} {y = y})
product-path-to-elem-path-equiv {A = A} {B = B} {x = x} {y = y} =
  qinv-to-isequiv product-path-to-elem-path (g st α and β)
    where
      f = product-path-to-elem-path

      g : (fst x ≡ fst y) × (snd x ≡ snd y) → x ≡ y
      g = g' x y
        where
          g' : (x y : A × B) → (fst x ≡ fst y) × (snd x ≡ snd y) → x ≡ y
          g' (fst₁ ,, snd₁) (.fst₁ ,, .snd₁) (refl ,, refl) = refl

      α : f ∘ g ~ λ x → x
      α (refl ,, refl) = refl

      β : g ∘ f ~ λ x → x
      β refl = refl

-- Theorem 2.6.4 transport over a path to a product fiber is a product of fibers over a path
product-transport :
  ∀ {n m} {Z : Set n} {A B : Z → Set m} {z w : Z} →
  (p : z ≡ w) (x : (A z) × (B z))  →
  transport (λ z → (A z) × (B z)) p x ≡ (transport A p (fst x) ,, transport B p (snd x))
product-transport refl (fst ,, snd) = refl

-- Definition of pair⁼
pair⁼ :
  ∀ {n m} {A : Set n} {B : Set m} {x y : A × B} →
  (fst x ≡ fst y) × (snd x ≡ snd y) →
  x ≡ y
pair⁼ {A = A} {B = B} {x = x} {y = y} =
  isequiv.g (product-path-to-elem-path-equiv {A = A} {B = B} {x = x} {y = y})

-- Theorem 2.6.5 functions are functors over products
function-functor-pair :
  {A B A' B' : Set} →
  (g : A → A') (h : B → B') →
  {x y : A × B} {p : fst x ≡ fst y} {q : snd x ≡ snd y} →
  ap (λ x → (g (fst x) ,, h (snd x))) (pair⁼ (p ,, q)) ≡ pair⁼ (ap g p ,, ap h q)
function-functor-pair g h {x = fstx ,, sndx} {y = .fstx ,, .sndx} {p = refl} {q = refl} = refl

-- Theorem 2.7.2 dependent functions are fibrations over Σ-types
record Sigma (A : Set) (B : A → Set) : Set where
  constructor _,,_
  field
    pr1 : A
    pr2 : B pr1

syntax Sigma A (λ x → y) = Σ x of A , y

pr1 : {A : Set} {B : A → Set} → Σ x of A , B x → A
pr1 (left ,, right) = left

pr2 : {A : Set} {B : A → Set} → (v : Σ x of A , B x) → B (pr1 {A} {B} v)
pr2 (left ,, right) = right

-- Theorem 2.7.2 dependent functions are functors over fibrations
function-fibration-product :
  {A : Set} {P : A → Set} {w w' : Σ x of A , P x} →
  (w ≡ w') ≃ (Σ p of (pr1 w ≡ pr1 w') , (transport P p (pr2 w) ≡ pr2 w'))
function-fibration-product {A = A} {P = P} {w = w} {w' = w'} =
  f withequiv qinv-to-isequiv f (g st α and β)
  where
    f :
      {w w' : Σ x of A , P x} →
      (w ≡ w') → (Σ p of (pr1 w ≡ pr1 w') , (transport P p (pr2 w) ≡ pr2 w'))
    f refl = refl ,, refl

    g :
      {w w' : Σ x of A , P x} →
      (Σ p of (pr1 w ≡ pr1 w') , (transport P p (pr2 w) ≡ pr2 w')) → (w ≡ w')
    g {w = w1 ,, w2} {w' = .w1 ,, .w2} (refl ,, refl) = refl

    α : f ∘ g ~ λ x → x
    α (refl ,, refl) = refl

    β : g ∘ f ~ λ x → x
    β refl = refl

-- Corollary 2.7.3 computation rule for Σ types
computation-sigma :
  {A : Set} {P : A → Set} →
  (z : Σ x of A , P x) → z ≡ (pr1 z ,, pr2 z)
computation-sigma z =
  isequiv.g (_≃_.e function-fibration-product)
  (refl ,, refl)

-- Theorem 2.8.1 : only one path between unit elements
record Unit : Set where
  constructor unit

single-path-between-unit : {x y : Unit} → (x ≡ y) ≃ Unit
single-path-between-unit {x = x} {y = y} =
  f withequiv qinv-to-isequiv f
  (g st α and β)
  where
    f : x ≡ y → Unit
    f _ = unit

    g : {x y : Unit} → Unit → x ≡ y
    g {x = unit} {y = unit} _ = refl

    α : f ∘ g ~ λ x → x
    α unit = refl

    β : g ∘ f ~ λ x → x
    β refl = refl

-- Theorem 2.9.2 path between functions are homotopies
happly :
  ∀ {n m} {A : Set n} {B : A → Set m} {f g : (x : A) → B x} →
  (f ≡ g) → f ~ g
happly refl x = refl

-- Axiom 2.9.3 function extensionality
postulate
  funext-equiv : ∀ {n m} {A : Set n} {B : A → Set m} {f g : (x : A) → B x} →
    isequiv (happly {A = A} {B = B} {f = f} {g = g})

funext :
  ∀ {n m} {A : Set n} {B : A → Set m} {f g : (x : A) → B x} →
  f ~ g → f ≡ g
funext = isequiv.g funext-equiv

-- Lemma 2.9.6
function-path-transport-equiv :
  ∀ {n m} {X : Set n} {A B : X → Set m} {x y : X} →
  {p : x ≡ y} (f : A x → B x) (g : A y → B y) →
  (transport (λ x → A x → B x) p f ≡ g) ≃
    ((a : A x) → (transport B p (f a) ≡ g (transport A p a)))
function-path-transport-equiv {p = refl} f g = happly withequiv funext-equiv

-- Lemma 2.10.1 paths between types are equivalences.
id-to-equiv : ∀ {n} {A B : Set n} → A ≡ B → A ≃ B
id-to-equiv refl = equiv-refl

-- Axiom 2.10.3 univalence axiom.
postulate univalence-equiv : ∀ {n} {A B : Set n} → isequiv (id-to-equiv {A = A} {B = B})
