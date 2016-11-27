{-# OPTIONS --without-K --rewriting #-}

module PathInduction where

open import Base public

-- The rewriting relation
{-<rewrite>-}
postulate
  _↦_ : ∀ {i} {A : Type i} → A → A → Type i

{-# BUILTIN REWRITE _↦_ #-}
{-</>-}

-- We redefine concatenation of paths to use induction on both paths, in order
-- to make unification more powerful
infixr 80 _∙_
_∙_ : ∀ {i} {A : Type i} {a b c : A} (p : a == b) (q : b == c) → a == c
idp ∙ idp = idp

record Coh {i} (A : Type i) : Type i where
  field
    & : A
open Coh public

instance
  J→ : ∀ {i j k} {A : Type i} {B : A → Type j} {f : (a : A) → B a} {P : {g : (a : A) → B a} (h : (a : A) → f a == g a) → Type k}
    → Coh (P (λ a → idp)) → Coh ({g : (a : A) → B a} → (h : (a : A) → f a == g a) → P h)
  & (J→ {A = A} {B} {f} {P = P} d) h = transport P (λ= (app=-β h)) (J-aux (λ= h)) where

    J-aux : {g : (a : A) → B a} (h : f == g) → P (app= h)
    J-aux idp = & d

  J→! : ∀ {i j k} {A : Type i} {B : A → Type j} {f : (a : A) → B a} {P : {g : (a : A) → B a} (h : (a : A) → g a == f a) → Type k}
    → Coh (P (λ a → idp)) → Coh ({g : (a : A) → B a} → (h : (a : A) → g a == f a) → P h)
  & (J→! {A = A} {B} {f} {P = P} d) h = transport P (λ= (app=-β h)) (J-aux (λ= h)) where

    J-aux : {g : (a : A) → B a} (h : g == f) → P (app= h)
    J-aux idp = & d

module _ {i j} {A : Type i} {a : A} where

 instance

  J- : {B : (a' : A) → a == a' → Type j}
    → Coh (B a idp) → Coh ({a' : A} (p : a == a') → B a' p)
  & (J- d) idp = & d

  J! : {B : (a' : A) → a' == a → Type j}
    → Coh (B a idp) → Coh ({a' : A} (p : a' == a) → B a' p)
  & (J! d) idp = & d

  J□ : {B : {b c d : A} {p : a == b} {q : a == c} {r : b == d} {s : c == d} → Square p q r s → Type j}
    → Coh (B ids) → Coh ({b c d : A} {p : a == b} {q : a == c} {r : b == d} {s : c == d} (sq : Square p q r s) → B sq)
  & (J□ {B = B} d) ids = & d

  J□i : {B : {b c d : A} {p : a == b} {q : a == c} {r : b == d} {s : c == d} → Square p q r s → Type j}
    → Coh (B ids) → Coh ({b c d : A} {p : a == b} {q : a == c} {r : b == d} {s : c == d} {sq : Square p q r s} → B sq)
  & (J□i {B = B} d) {sq = ids} = & d

  J□1 : {B : (p : a == a) → Square p idp idp idp → Type j}
    → Coh (B idp ids) → Coh ({p : a == a} (sq : Square p idp idp idp) → B p sq)
  & (J□1 {B = B} d) c = aux B (& d) c  where

    e : {a b c d : A} (q : a == c) (r : b == d) (s : c == d) → Square (q ∙ s ∙ ! r) q r s
    e idp idp idp = ids

    aux : {a b c d : A} {q : a == c} {r : b == d} {s : c == d} (B : (p : a == b) → Square p q r s → Type j)
       → B (q ∙ s ∙ ! r) (e q r s) → {p : a == b} (sq : Square p q r s) → B p sq
    aux B d ids = d

  J□2 : {B : (p : a == a) → Square idp p idp idp → Type j}
    → Coh (B idp ids) → Coh ({p : a == a} (sq : Square idp p idp idp) → B p sq)
  & (J□2 {B = B} d) c = aux B (& d) c  where

    e : {a b c d : A} (p : a == b) (r : b == d) (s : c == d) → Square p (p ∙ r ∙ ! s) r s
    e idp idp idp = ids

    aux : {a b c d : A} {p : a == b} {r : b == d} {s : c == d} (B : (q : a == c) → Square p q r s → Type j)
       → B (p ∙ r ∙ ! s) (e p r s) → {q : a == c} (sq : Square p q r s) → B q sq
    aux B d ids = d

  J□3 : {B : (p : a == a) → Square idp idp p idp → Type j}
    → Coh (B idp ids) → Coh ({p : a == a} (sq : Square idp idp p idp) → B p sq)
  & (J□3 {B = B} d) c = aux B (& d) c  where

    e : {a b c d : A} (p : a == b) (q : a == c) (s : c == d) → Square p q (! p ∙ q ∙ s) s
    e idp idp idp = ids

    aux : {a b c d : A} {p : a == b} {q : a == c} {s : c == d} (B : (r : b == d) → Square p q r s → Type j)
       → B (! p ∙ q ∙ s) (e p q s) → {r : b == d} (sq : Square p q r s) → B r sq
    aux B d ids = d

  J□4 : {B : (p : a == a) → Square idp idp idp p → Type j}
    → Coh (B idp ids) → Coh ({p : a == a} (sq : Square idp idp idp p) → B p sq)
  & (J□4 {B = B} d) c = aux B (& d) c  where

    e : {a b c d : A} (p : a == b) (q : a == c) (r : b == d) → Square p q r (! q ∙ p ∙ r)
    e idp idp idp = ids

    aux : {a b c d : A} {p : a == b} {q : a == c} {r : b == d} (B : (s : c == d) → Square p q r s → Type j)
       → B (! q ∙ p ∙ r) (e p q r) → {s : c == d} (sq : Square p q r s) → B s sq
    aux B d ids = d

instance
  idp-Coh : ∀ {i} {A : Type i} {a : A} → Coh (a == a)
  & idp-Coh = idp

  ids-Coh : ∀ {i} {A : Type i} {a : A} → Coh (Square {a₀₀ = a} idp idp idp idp)
  & ids-Coh = ids

  idc-Coh : ∀ {i} {A : Type i} {a : A} → Coh (Cube {a₀₀₀ = a} ids ids ids ids ids ids)
  & idc-Coh = idc

  -- Allows us to put the initial [a] in the [Coh]
  strip-a : ∀ {i j} {A : Type i} {P : A → A → Type j} → ((a : A) → Coh ({b : A} → P a b)) → Coh ({a b : A} → P a b)
  & (strip-a z) = & (z _)

  -- Allows us to put the initial [A] in the [Coh]
  strip-A : ∀ {i j} {P : Type i → Type j} → ((A : Type i) → Coh (P A)) → Coh ({A : Type i} → P A)
  & (strip-A z) = & (z _)

  -- Allows us to have implicit arguments
  implicit : ∀ {i j k} {A : Type i} {B : A → Type j} {C : (a : A) → B a → Type k} → Coh ({a : A} (b : B a) → C a b) → Coh ({a : A} {b : B a} → C a b)
  & (implicit d) = & d _

path-induction : ∀ {i} {A : Type i} {{a : A}} → A
path-induction {{a}} = a

-- Rules for cubes

instance
  idsidc1-Coh : ∀ {i} {A : Type i} {a : A} → Coh (Σ (Square (idp {a = a}) idp idp idp) (λ left → Cube left ids ids ids ids ids))
  & idsidc1-Coh = (ids , idc)

  idsidc2-Coh : ∀ {i} {A : Type i} {a : A} → Coh (Σ (Square (idp {a = a}) idp idp idp) (λ right → Cube ids right ids ids ids ids))
  & idsidc2-Coh = (ids , idc)

  idsidc6-Coh : ∀ {i} {A : Type i} {a : A} → Coh (Σ (Square (idp {a = a}) idp idp idp) (λ front → Cube ids ids ids ids ids front))
  & idsidc6-Coh = (ids , idc)

module _ {i j} {A : Type i} {a : A} where
 instance

  JCube1 : {B : (p : Square {a₀₀ = a} idp idp idp idp) → Cube p ids ids ids ids ids → Type j}
    → Coh (B ids idc) → Coh ({p : Square {a₀₀ = a} idp idp idp idp} (cube : Cube p ids ids ids ids ids) → B p cube)
  & (JCube1 {B = B} d) c = aux B (& d) c  where

    comp : Coh ({a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
           {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
           {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
           (right : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁)

           {a₀₀₀ : A} {p₀₀₋ : a₀₀₀ == a₀₀₁}
           {a₀₁₀ : A} {p₀₁₋ : a₀₁₀ == a₀₁₁}
           {a₁₀₀ : A} {p₁₀₋ : a₁₀₀ == a₁₀₁}
           {a₁₁₀ : A} {p₁₁₋ : a₁₁₀ == a₁₁₁}

           {p₀₋₀ : a₀₀₀ == a₀₁₀}
           (back : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁)
           {p₋₀₀ : a₀₀₀ == a₁₀₀}
           (top : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁)
           {p₋₁₀ : a₀₁₀ == a₁₁₀}
           (bottom : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁)
           {p₁₋₀ : a₁₀₀ == a₁₁₀}
           (front : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁)
           → Σ (Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀) (λ left → Cube left right back top bottom front))
    comp = path-induction

    aux :  {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
           {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
           {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
           -- missing left

           {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
           {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
           {right : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁}

           {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
           {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
           {back : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁}
           {top : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁}
           {bottom : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁}
           {front : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁}
           → (B : (left : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀) → Cube left right back top bottom front → Type j)
           → uncurry B (& comp right back top bottom front)
           → ({left : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} (cube : Cube left right back top bottom front) → B left cube)
    aux B d idc = d

  JCube2 : {B : (p : Square {a₀₀ = a} idp idp idp idp) → Cube ids p ids ids ids ids → Type j}
    → Coh (B ids idc) → Coh ({p : Square {a₀₀ = a} idp idp idp idp} (cube : Cube ids p ids ids ids ids) → B p cube)
  & (JCube2 {B = B} d) c = aux B (& d) c  where

    comp : Coh ({a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ : A}
           {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
           {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
           (left : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀)

           {a₀₀₁ : A} {p₀₀₋ : a₀₀₀ == a₀₀₁}
           {a₀₁₁ : A} {p₀₁₋ : a₀₁₀ == a₀₁₁}
           {a₁₀₁ : A} {p₁₀₋ : a₁₀₀ == a₁₀₁}
           {a₁₁₁ : A} {p₁₁₋ : a₁₁₀ == a₁₁₁}

           {p₀₋₁ : a₀₀₁ == a₀₁₁}
           (back : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁)
           {p₋₀₁ : a₀₀₁ == a₁₀₁}
           (top : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁)
           {p₋₁₁ : a₀₁₁ == a₁₁₁}
           (bottom : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁)
           {p₁₋₁ : a₁₀₁ == a₁₁₁}
           (front : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁)
           → Σ (Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁) (λ right → Cube left right back top bottom front))
    comp = path-induction

    aux :  {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
           {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
           {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
           {left : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀}

           {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
           {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}


           {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
           {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
           {back : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁}
           {top : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁}
           {bottom : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁}
           {front : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁}
           → (B : (right : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁) → Cube left right back top bottom front → Type j)
           → uncurry B (& comp left back top bottom front)
           → ({right : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} (cube : Cube left right back top bottom front) → B right cube)
    aux B d idc = d

  JCube6 : {B : (p : Square {a₀₀ = a} idp idp idp idp) → Cube ids ids ids ids ids p → Type j}
    → Coh (B ids idc) → Coh ({p : Square {a₀₀ = a} idp idp idp idp} (cube : Cube ids ids ids ids ids p) → B p cube)
  & (JCube6 {B = B} d) c = aux B (& d) c  where

    comp : Coh ({a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ : A}
           {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
           {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
           (left : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀)

           {a₀₀₁ : A} {p₀₀₋ : a₀₀₀ == a₀₀₁}
           {a₀₁₁ : A} {p₀₁₋ : a₀₁₀ == a₀₁₁}
           {a₁₀₁ : A} {p₁₀₋ : a₁₀₀ == a₁₀₁}
           {a₁₁₁ : A} {p₁₁₋ : a₁₁₀ == a₁₁₁}

           {p₀₋₁ : a₀₀₁ == a₀₁₁}
           (back : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁)
           {p₋₀₁ : a₀₀₁ == a₁₀₁}
           (top : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁)
           {p₋₁₁ : a₀₁₁ == a₁₁₁}
           (bottom : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁)
           {p₁₋₁ : a₁₀₁ == a₁₁₁}
           (right : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁)
           → Σ (Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁) (λ front → Cube left right back top bottom front))
    comp = path-induction

    aux :  {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
           {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
           {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
           {left : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀}

           {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
           {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
           {right : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁}

           {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
           {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
           {back : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁}
           {top : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁}
           {bottom : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁}
           → (B : (front : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁) → Cube left right back top bottom front → Type j)
           → uncurry B (& comp left back top bottom right)
           → ({front : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} (cube : Cube left right back top bottom front) → B front cube)
    aux B d idc = d

-- Flat cubes (cubes where the four lateral faces are actually only 2-dimensional paths
data FlatCube {i} {A : Type i} {a : A} :
  {b c d : A} {p p' : a == b} {q q' : a == c} {r r' : b == d} {s s' : c == d}
  → Square p q r s → Square p' q' r' s' → p == p' → q == q' → r == r' → s == s' → Type i where
  idfc : FlatCube ids ids idp idp idp idp

instance
  idfc-Coh : ∀ {i} {A : Type i} {a : A} → Coh (FlatCube {a = a} ids ids idp idp idp idp)
  & idfc-Coh = idfc

  JFlatCube1 : ∀ {i j} {A : Type i} {a : A} {B : (p : Square {a₀₀ = a} idp idp idp idp) → FlatCube p ids idp idp idp idp → Type j}
    → Coh (B ids idfc) → Coh ({p : Square {a₀₀ = a} idp idp idp idp} (cube : FlatCube p ids idp idp idp idp) → B p cube)
  & (JFlatCube1 {i} {j} {B = B} d) c = aux B (& d) c  where

    comp : {A : Type i} {a b c d : A} {p' : a == b} {q' : a == c} {r' : b == d} {s' : c == d} (sq' : Square p' q' r' s')
           {p : a == b} (p= : p == p') {q : a == c} (q= : q == q') {r : b == d} (r= : r == r') {s : c == d} (s= : s == s')
         → Square p q r s
    comp ids idp idp idp idp = ids

    fill : {A : Type i} {a b c d : A} {p' : a == b} {q' : a == c} {r' : b == d} {s' : c == d} (sq' : Square p' q' r' s')
           {p : a == b} (p= : p == p') {q : a == c} (q= : q == q') {r : b == d} (r= : r == r') {s : c == d} (s= : s == s')
         → FlatCube (comp sq' p= q= r= s=) sq' p= q= r= s=
    fill ids idp idp idp idp = idfc

    aux : {A : Type i} {a b c d : A} {p' : a == b} {q' : a == c} {r' : b == d} {s' : c == d} {sq' : Square p' q' r' s'}
          {p : a == b} {p= : p == p'} {q : a == c} {q= : q == q'} {r : b == d} {r= : r == r'} {s : c == d} {s= : s == s'}
         (B : (sq : Square p q r s) (fil : FlatCube sq sq' p= q= r= s=) → Type j)
          → B (comp sq' p= q= r= s=) (fill sq' p= q= r= s=)
          → {sq : Square p q r s} (fil : FlatCube sq sq' p= q= r= s=) → B sq fil
    aux B d idfc = d

  JFlatCube2 : ∀ {i j} {A : Type i} {a : A} {B : (p : Square {a₀₀ = a} idp idp idp idp) → FlatCube ids p idp idp idp idp → Type j}
    → Coh (B ids idfc) → Coh ({p : Square {a₀₀ = a} idp idp idp idp} (cube : FlatCube ids p idp idp idp idp) → B p cube)
  & (JFlatCube2 d) idfc = & d

ap-∙ : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {a b c : A} (p : a == b) (q : b == c) → ap f (p ∙ q) == ap f p ∙ ap f q
ap-∙ f idp idp = idp

ap-∙! : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {a b : A} (p : a == b) {c : A} (q : c == b) → ap f (p ∙ ! q) == ap f p ∙ ! (ap f q)
ap-∙! f idp idp = idp

ap-shape-∙! : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {a b c : A} {p : a == b} {q : a == c} {r : b == c}
  → p == q ∙ ! r → ap f p == ap f q ∙ ! (ap f r)
ap-shape-∙! f {q = idp} {r = idp} idp = idp

ap-!∙ : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {a b : A} (p : b == a) {c : A} (q : b == c) → ap f (! p ∙ q) == ! (ap f p) ∙ ap f q
ap-!∙ f idp idp = idp

∘-ap : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (g : B → C) (f : A → B)
  {x y : A} (p : x == y) → ap g (ap f p) == ap (g ∘ f) p
∘-ap f g p = ! (ap-∘ f g p)

∙idp : ∀ {i} {A : Type i} {a b : A} {p : a == b} → p ∙ idp == p
∙idp {p = idp} = idp

idp∙ : ∀ {i} {A : Type i} {a a' : A} {p : a == a'} → idp ∙ p == p
idp∙ {p = idp} = idp

!-inv-r : ∀ {i} {A : Type i} {a b : A} {p : a == b} → p ∙ ! p == idp
!-inv-r {p = idp} = idp

!-inv-l : ∀ {i} {A : Type i} {a b : A} {p : a == b} → ! p ∙ p == idp
!-inv-l {p = idp} = idp

module _ {i} {A : Type i} where

  horiz-degen-square : {a a' : A} {p q : a == a'}
    → p == q → Square p idp idp q
  horiz-degen-square idp = hid-square

  vert-degen-square : {a a' : A} {p q : a == a'}
    → p == q → Square idp p q idp
  vert-degen-square idp = vid-square

  horiz-degen-path : {a a' : A} {p q : a == a'}
    → Square p idp idp q → p == q
  horiz-degen-path {p = idp} ids = idp

  horiz-degen-square-idp : {a a' : A} {p : a == a'}
    → horiz-degen-square (idp {a = p}) == hid-square
  horiz-degen-square-idp {p = idp} = idp

  horiz-degen-square-β : {a a' : A} {p q : a == a'} {sq : Square p idp idp q} → horiz-degen-square (horiz-degen-path sq) == sq
  horiz-degen-square-β {p = idp} {sq = ids} = idp

  horiz-degen-square-η : {a a' : A} {p q : a == a'} {r : p == q} → horiz-degen-path (horiz-degen-square r) == r
  horiz-degen-square-η {p = idp} {r = idp} = idp

module _ {i j} {A : Type i} {B : Type j} {f g : A → B} where

  natural-square : (h : (a : A) → f a == g a)
    {x y : A} (p : x == y)
    → {fp : f x == f y} (fp= : ap f p == fp)
    → {gp : g x == g y} (gp= : ap g p == gp)
    → Square (h x) fp gp (h y)
  natural-square h idp idp idp = hid-square

  ↓-='-to-square : {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
    → {fp : f x == f y} (fp= : ap f p == fp)
    → {gp : g x == g y} (gp= : ap g p == gp)
    → u == v [ (λ z → f z == g z) ↓ p ]
    → Square u fp gp v
  ↓-='-to-square {p = idp} idp idp α = horiz-degen-square α

  ↓-='-from-square : {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
    → {fp : f x == f y} (fp= : ap f p == fp)
    → {gp : g x == g y} (gp= : ap g p == gp)
    → Square u fp gp v
    → u == v [ (λ z → f z == g z) ↓ p ]
  ↓-='-from-square {p = idp} idp idp sq = horiz-degen-path sq

  {- Used for getting square equivalents of glue-β terms -}
  natural-square-β : (h : (a : A) → f a == g a)
    {x y : A} (p : x == y)
    {fp : f x == f y} {fp= : ap f p == fp}
    {gp : g x == g y} {gp= : ap g p == gp}
    {sq : Square (h x) fp gp (h y)}
    → apd h p == ↓-='-from-square fp= gp= sq
    → natural-square h p fp= gp= == sq
  natural-square-β _ idp {fp= = idp} {gp= = idp} α = ! horiz-degen-square-idp ∙ ap horiz-degen-square α ∙ horiz-degen-square-β

module _ {i j k} {A : Type i} {B : Type j} (C : B → Type k) (f : A → B) where

  ↓-ap-in2 : {x y : A} {p : x == y} {u : C (f x)} {v : C (f y)}
    {fp : f x == f y} (fp= : ap f p == fp)
    → u == v [ C ∘ f ↓ p ]
    → u == v [ C ↓ fp ]
  ↓-ap-in2 {p = idp} idp idp = idp

module _ {i j k} {A : Type i} {B : Type j} (C : B → Type k) {f : A → B} where

  ↓-ap-in-coh : {X : Type i} {g : X → A} {x y : X} {p : x == y} {gp : g x == g y} {p-β : ap g p == gp} (h : (a : A) → C (f a))
    → ↓-ap-in C f (apd h gp) == ↓-ap-in2 C (f ∘ g) (ap-∘ f g p ∙ ap (ap f) p-β) (apd (h ∘ g) p)
  ↓-ap-in-coh {p = idp} {p-β = idp} h = idp

↓-PathOver-from-square : ∀ {i j} {A X : Type i} {P : A → Type j} {a b : X → A}
  {q : (x : X) → a x == b x} {f : (x : X) → P (a x)} {g : (x : X) → P (b x)}
  {x y : X} {p : x == y} {u : PathOver P (q x) (f x) (g x)} {v : PathOver P (q y) (f y) (g y)}
  {a-p : a x == a y} {ap= : ap a p == a-p}
  {b-p : b x == b y} {bp= : ap b p == b-p}
  → SquareOver P (natural-square q p ap= bp=) u (↓-ap-in2 P a {p = p} ap= (apd f p)) (↓-ap-in2 P b bp= (apd g p)) v
  → u == v [ (λ z → f z == g z [ P ↓ q z ]) ↓ p ]
↓-PathOver-from-square {p = idp} {ap= = idp} {bp= = idp} pq = coh pq  where

  coh : ∀ {i j} {A : Type i} {P : A → Type j} {a b : A} {q : a == b} {f : P a} {g : P b} {u v : f == g [ P ↓ q ]}
      → SquareOver P hid-square u idp idp v → u == v
  coh {q = idp} {u = idp} ids = idp

adapt-SquareOver : ∀ {i j} {A : Type i} {P : A → Type j} {a b c d : A}
  {p : a == b} {q : a == c} {r : b == d} {s : c == d} {sq : Square p q r s}
  {a' : P a} {b' : P b} {c' : P c} {d' : P d}
  {p' : a' == b' [ P ↓ p ]} {q' q'2 : a' == c' [ P ↓ q ]}
  {r' r'2 : b' == d' [ P ↓ r ]} {s' : c' == d' [ P ↓ s ]}
  (q'= : q' == q'2) (r'= : r' == r'2)
  → SquareOver P sq p' q' r' s'
  → SquareOver P sq p' q'2 r'2 s'
adapt-SquareOver {sq = ids} idp idp ids = ids

ap-square-natural-square : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : B → C) →
  Coh ({a b : A} (p : a == b) {u v : A → B} (g : (x : A) → u x == v x)
      {up : u a == u b} {up= : ap u p == up}
      {vp : v a == v b} {vp= : ap v p == vp}
      {fup : ap (λ z → f (u z)) p == ap f up} (fup= : ap-∘ f u p ∙ ap (ap f) up= == fup)
      {fvp : ap (λ z → f (v z)) p == ap f vp} (fvp= : ap-∘ f v p ∙ ap (ap f) vp= == fvp)
    → ap-square f (natural-square g p up= vp=) == natural-square (ap f ∘ g) p fup fvp)
ap-square-natural-square {i} {j} {k} f = path-induction

ap-square-horiz-degen-square : ∀ {i j} {A : Type i} {B : Type j} {f : A → B} {a a' : A} {p p' : a == a'} (p= : p == p') → ap-square f (horiz-degen-square p=) == horiz-degen-square (ap (ap f) p=)
ap-square-horiz-degen-square {p = idp} idp = idp

adapt-square : ∀ {i} {A : Type i} {a b c d : A} {p : a == b} {q : a == c} {r : b == d} {s : c == d} (sq : Square p q r s)
               {q' : a == c} (q= : q == q') {r' : b == d} (r= : r == r')
             → Square p q' r' s
adapt-square ids idp idp = ids

ap2-idf : ∀ {i} → Coh ({A : Type i} {x y : A} {p q : x == y} {r : p == q} → Square (ap (ap (λ z → z)) r) (ap-idf _) (ap-idf _) r)
ap2-idf = path-induction


ap-∘3 : ∀ {i j k l} {A : Type i} {B : Type j} {C : Type k} {D : Type l}
        (f : C → D) (g : B → C) (h : A → B) {a b : A} (p : a == b)
      → Square (ap-∘ f (g ∘ h) p) (ap-∘ (f ∘ g) h p) (ap (ap f) (ap-∘ g h p)) (ap-∘ f g (ap h p))
ap-∘3 f g h idp = ids

_∙□_ : ∀ {i} {A : Type i} {a b c d e f : A} {p : a == b} {q : a == c} {r : b == d} {s : c == d} {t : c == e} {u : d == f} {v : e == f}
         (sq1 : Square p q r s) (sq2 : Square s t u v)
       → Square p (q ∙ t) (r ∙ u) v
ids ∙□ ids = ids

_|∙_ : ∀ {i} {A : Type i} {a b c d : A} {p p' : a == b} {q : a == c} {r : b == d} {s : c == d}
         (p= : p == p') (sq1 : Square p' q r s)
       → Square p q r s
idp |∙ ids = ids

_∙|_ : ∀ {i} {A : Type i} {a b c d : A} {p : a == b} {q : a == c} {r : b == d} {s s' : c == d}
         (sq1 : Square p q r s) (s= : s == s')
       → Square p q r s'
ids ∙| idp = ids

infixr 80 _∙□_ _|∙_ _∙|_

_∙³x_ : ∀ {i} {A : Type i}
  {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ a₀₀₂ a₀₁₂ a₁₀₂ a₁₁₂ : A}
  {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
  {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
  {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

  {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
  {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
  {sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- middle

  {p₀₋₂ : a₀₀₂ == a₀₁₂} {p₋₀₂ : a₀₀₂ == a₁₀₂}
  {p₋₁₂ : a₀₁₂ == a₁₁₂} {p₁₋₂ : a₁₀₂ == a₁₁₂}
  {sq₋₋₂ : Square p₀₋₂ p₋₀₂ p₋₁₂ p₁₋₂} -- right

  {p₀₀l : a₀₀₀ == a₀₀₁} {p₀₁l : a₀₁₀ == a₀₁₁}
  {p₁₀l : a₁₀₀ == a₁₀₁} {p₁₁l : a₁₁₀ == a₁₁₁}
  {sq₀₋l : Square p₀₋₀ p₀₀l p₀₁l p₀₋₁} -- backl
  {sq₋₀l : Square p₋₀₀ p₀₀l p₁₀l p₋₀₁} -- topl
  {sq₋₁l : Square p₋₁₀ p₀₁l p₁₁l p₋₁₁} -- bottoml
  {sq₁₋l : Square p₁₋₀ p₁₀l p₁₁l p₁₋₁} -- frontl

  {p₀₀r : a₀₀₁ == a₀₀₂} {p₀₁r : a₀₁₁ == a₀₁₂}
  {p₁₀r : a₁₀₁ == a₁₀₂} {p₁₁r : a₁₁₁ == a₁₁₂}
  {sq₀₋r : Square p₀₋₁ p₀₀r p₀₁r p₀₋₂} -- backr
  {sq₋₀r : Square p₋₀₁ p₀₀r p₁₀r p₋₀₂} -- topr
  {sq₋₁r : Square p₋₁₁ p₀₁r p₁₁r p₋₁₂} -- bottomr
  {sq₁₋r : Square p₁₋₁ p₁₀r p₁₁r p₁₋₂} -- frontr

  → Cube sq₋₋₀ sq₋₋₁ sq₀₋l sq₋₀l sq₋₁l sq₁₋l
  → Cube sq₋₋₁ sq₋₋₂ sq₀₋r sq₋₀r sq₋₁r sq₁₋r
  → Cube sq₋₋₀ sq₋₋₂ (sq₀₋l ∙□ sq₀₋r) (sq₋₀l ∙□ sq₋₀r)
         (sq₋₁l ∙□ sq₋₁r) (sq₁₋l ∙□ sq₁₋r)
idc ∙³x idc = idc

infixr 80 _∙³x_

x-degen-cube : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀}
  {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  {sq₋₋₀ sq₋₋₁ : Square p₀₋ p₋₀ p₋₁ p₁₋}
  → sq₋₋₀ == sq₋₋₁
  → Cube sq₋₋₀ sq₋₋₁ hid-square hid-square hid-square hid-square
x-degen-cube {sq₋₋₀ = ids} idp = idc

natural-cube-η∞ : ∀ {i j} {A : Type i} {B : Type j}
  {u : A → B}
  {r : (a : A) → u a == u a}
  (p : ∀ a → r a == idp)
  {x y : A} (q : x == y)
  {uq : u x == u y} {uq= : ap u q == uq}
  → Cube (horiz-degen-square (p x)) (horiz-degen-square (p y))
         (natural-square r q uq= uq=) vid-square vid-square vid-square
natural-cube-η∞ p idp {uq= = idp} = x-degen-cube idp

natural-square-∘ : ∀ {i} {A B C : Type i} {a b : C} (p : a == b) (k : C → A) →
         Coh ({f g : A → B} (h : (a : A) → f a == g a)
              {fkp : _} {fkp= : ap (f ∘ k) p == fkp}
              {gkp : _} {gkp= : ap (g ∘ k) p == gkp}
              {fkp2 : _} (fkp2= : ∘-ap f k p ∙ fkp= == fkp2)
              {gkp2 : _} (gkp2= : ∘-ap g k p ∙ gkp= == gkp2)
         → natural-square (h ∘ k) p fkp= gkp= == natural-square h (ap k p) fkp2 gkp2)
natural-square-∘ idp = path-induction

_-∙³_ : ∀ {i} {A : Type i}
  {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
  {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
  {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
  {sq₋₋₀ sq₋₋₀' : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

  {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
  {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
  {sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- right

  {p₀₀ : a₀₀₀ == a₀₀₁} {p₀₁ : a₀₁₀ == a₀₁₁}
  {p₁₀ : a₁₀₀ == a₁₀₁} {p₁₁ : a₁₁₀ == a₁₁₁}
  {sq₀₋ : Square p₀₋₀ p₀₀ p₀₁ p₀₋₁} -- back
  {sq₋₀ : Square p₋₀₀ p₀₀ p₁₀ p₋₀₁} -- top
  {sq₋₁ : Square p₋₁₀ p₀₁ p₁₁ p₋₁₁} -- bottom
  {sq₁₋ : Square p₁₋₀ p₁₀ p₁₁ p₁₋₁} -- front

  → (sq₋₋₀ == sq₋₋₀')
  → Cube sq₋₋₀' sq₋₋₁ sq₀₋ sq₋₀ sq₋₁ sq₁₋
  → Cube sq₋₋₀  sq₋₋₁ sq₀₋ sq₋₀ sq₋₁ sq₁₋
idp -∙³ idc = idc

_-|∙³_ : ∀ {i} {A : Type i} → {a₀₀₀ a₀₁₀ : A}
  {a b p₀₋₀ p₁₋₀ : a₀₀₀ == a₀₁₀}
  {p : a == b} {q : a == p₀₋₀} {r : b == p₁₋₀}
  {sq₋₋₀ : p₀₋₀ == p₁₋₀} -- left

  (α : Square p q r sq₋₋₀)

  {a₀₀₁ : A} {p₀₀₋ : a₀₀₀ == a₀₀₁}
  {a₀₁₁ : A} {p₀₁₋ : a₀₁₀ == a₀₁₁}
  {a₁₀₁ : A} {p₁₀₋ : a₀₀₀ == a₁₀₁}
  {a₁₁₁ : A} {p₁₁₋ : a₀₁₀ == a₁₁₁}

  {p₀₋₁ : a₀₀₁ == a₀₁₁}
  {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁} -- back
  {p₋₀₁ : a₀₀₁ == a₁₀₁}
  {sq₋₀₋ : Square idp p₀₀₋ p₁₀₋ p₋₀₁} -- top
  {p₋₁₁ : a₀₁₁ == a₁₁₁}
  {sq₋₁₋ : Square idp p₀₁₋ p₁₁₋ p₋₁₁} -- bottom
  {p₁₋₁ : a₁₀₁ == a₁₁₁}
  {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} -- front

  {sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- right
    → Cube (horiz-degen-square sq₋₋₀) sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
    → Cube (horiz-degen-square p) sq₋₋₁ (q |∙ sq₀₋₋ ) sq₋₀₋ sq₋₁₋ (r |∙ sq₁₋₋)
ids -|∙³ idc = idc

infixr 80 _-|∙³_

adapt-cube : ∀ {i} {A : Type i} {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
  {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
  {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
  {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

  {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
  {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
  {sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- right

  {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
  {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
  {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁} -- back
  {sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁} -- top
  {sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁} -- bottom
  {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} -- front
  (cube : Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋ )

  {p₀₀₋' : a₀₀₀ == a₀₀₁} (p₀₀₋= : p₀₀₋ == p₀₀₋') {p₀₁₋' : a₀₁₀ == a₀₁₁} (p₀₁₋= : p₀₁₋ == p₀₁₋')
  {p₁₀₋' : a₁₀₀ == a₁₀₁} (p₁₀₋= : p₁₀₋ == p₁₀₋') {p₁₁₋' : a₁₁₀ == a₁₁₁} (p₁₁₋= : p₁₁₋ == p₁₁₋')
  {sq₀₋₋' : Square p₀₋₀ p₀₀₋' p₀₁₋' p₀₋₁} (sq₀₋₋= : adapt-square sq₀₋₋ p₀₀₋= p₀₁₋= == sq₀₋₋') -- back
  {sq₋₀₋' : Square p₋₀₀ p₀₀₋' p₁₀₋' p₋₀₁} (sq₋₀₋= : adapt-square sq₋₀₋ p₀₀₋= p₁₀₋= == sq₋₀₋') -- top
  {sq₋₁₋' : Square p₋₁₀ p₀₁₋' p₁₁₋' p₋₁₁} (sq₋₁₋= : adapt-square sq₋₁₋ p₀₁₋= p₁₁₋= == sq₋₁₋') -- bottom
  {sq₁₋₋' : Square p₁₋₀ p₁₀₋' p₁₁₋' p₁₋₁} (sq₁₋₋= : adapt-square sq₁₋₋ p₁₀₋= p₁₁₋= == sq₁₋₋') -- front

  → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋' sq₋₀₋' sq₋₁₋' sq₁₋₋'
adapt-cube idc idp idp idp idp idp idp idp idp = idc

adapt-cube-idp : ∀ {i} {A : Type i} {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
  {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
  {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
  {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

  {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
  {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
  {sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- right

  {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
  {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
  {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁} -- back
  {sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁} -- top
  {sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁} -- bottom
  {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} -- front
  (cube : Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋ )

  {sq₀₋₋' : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁} (sq₀₋₋= : sq₀₋₋ == sq₀₋₋') -- back
  {sq₋₀₋' : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁} (sq₋₀₋= : sq₋₀₋ == sq₋₀₋') -- top
  {sq₋₁₋' : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁} (sq₋₁₋= : sq₋₁₋ == sq₋₁₋') -- bottom
  {sq₁₋₋' : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} (sq₁₋₋= : sq₁₋₋ == sq₁₋₋') -- front

  → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋' sq₋₀₋' sq₋₁₋' sq₁₋₋'
adapt-cube-idp idc idp idp idp idp = idc

{- A SquareOver between paths can be represented as a cube -}
module _ {i j} {A : Type i} {B : Type j} {f g : A → B}
  where

  cube-to-↓-square : {a : A} {a= : f a == g a}
    {b : A} {p : a == b} {c : A} {q : a == c} {d : A} {r : b == d} {s : c == d}
    {sq : Square p q r s}
    {fp : _} {fp= : ap f p == fp}
    {fq : _} {fq= : ap f q == fq}
    {fr : _} {fr= : ap f r == fr}
    {fs : _} {fs= : ap f s == fs}
    {b= : f b == g b}
    (p= : Square fp a= b= (ap g p))
    {c= : f c == g c}
    {q= : Square fq a= c= (ap g q)}
    {q□ : PathOver (λ z → f z == g z) q a= c=}
    (q□= : q□ == ↓-='-from-square fq= idp (square-symmetry q=))
    {d= : f d == g d}
    {r= : Square b= fr (ap g r) d=}
    {r□ : PathOver (λ z → f z == g z) r b= d=}
    (r□= : r□ == ↓-='-from-square fr= idp r=)
    (s= : Square fs c= d= (ap g s))
    → Cube (ap-square f sq) (ap-square g sq) (fp= |∙ p=) (fq= |∙ q=) (fr= |∙ square-symmetry r=) (fs= |∙ s=)
    → SquareOver (λ z → f z == g z) sq (↓-='-from-square fp= idp (square-symmetry p=))
                                       q□
                                       r□
                                       (↓-='-from-square fs= idp (square-symmetry s=))
  cube-to-↓-square {sq = ids} {fp= = idp} {fq= = idp} {fr= = idp} {fs= = idp} p= idp idp s= cube = & coh cube (& coh2)  where

    coh : Coh ({A : Type j} {x y : A} {a= b= : x == y} {p= : Square idp a= b= idp} {c= : x == y} {q= : Square idp a= c= idp} {d= : x == y} {r= : Square b= idp idp d=} {s=' : Square idp c= d= idp}
        → Cube ids ids (idp |∙ p=) (idp |∙ q=) (idp |∙ square-symmetry r=) s='
        → {s= : Square idp c= d= idp} (s== : s= == s=')
        → Square (horiz-degen-path (square-symmetry p=))
                 (horiz-degen-path (square-symmetry q=))
                 (horiz-degen-path r=)
                 (horiz-degen-path (square-symmetry s=)))
    coh = path-induction

    coh2 : Coh ({A : Type j} {a b c d : A} {p : a == b} {q : a == c} {r : b == d} {s : c == d} {sq : Square p q r s} → sq == idp |∙ sq)
    coh2 = path-induction

x-degen-cube-in : ∀ {i} → Coh ({A : Type i} {a b c d : A}
  {p : a == b} {q : a == c}
  {r : b == d} {s : c == d}
  {sq sq' : Square p q r s}
  → sq == sq'
  → Cube sq sq' hid-square hid-square hid-square hid-square)
x-degen-cube-in = path-induction

x-degen-cube-out : ∀ {i} → Coh ({A : Type i} {a b c d : A}
  {p : a == b} {q : a == c}
  {r : b == d} {s : c == d}
  {sq sq' : Square p q r s}
  → Cube sq sq' hid-square hid-square hid-square hid-square
  → sq == sq')
x-degen-cube-out = path-induction

{- A pathover between squares can be represented as a cube -}
module _ {i j} {A : Type i} {B : Type j} {b₀₀ b₀₁ b₁₀ b₁₁ : A → B}
  {p₀₋ : (a : A) → b₀₀ a == b₀₁ a} {p₋₀ : (a : A) → b₀₀ a == b₁₀ a}
  {p₋₁ : (a : A) → b₀₁ a == b₁₁ a} {p₁₋ : (a : A) → b₁₀ a == b₁₁ a}
  where

  cube-to-↓-path : {x y : A} {q : x == y}
    {sqx : Square (p₀₋ x) (p₋₀ x) (p₋₁ x) (p₁₋ x)}
    {sqy : Square (p₀₋ y) (p₋₀ y) (p₋₁ y) (p₁₋ y)}
    {b₀₀q : b₀₀ x == b₀₀ y} (b₀₀q= : ap b₀₀ q == b₀₀q)
    {b₀₁q : b₀₁ x == b₀₁ y} (b₀₁q= : ap b₀₁ q == b₀₁q)
    {b₁₀q : b₁₀ x == b₁₀ y} (b₁₀q= : ap b₁₀ q == b₁₀q)
    {b₁₁q : b₁₁ x == b₁₁ y} (b₁₁q= : ap b₁₁ q == b₁₁q)
    → Cube sqx sqy
           (natural-square p₀₋ q b₀₀q= b₀₁q=) (natural-square p₋₀ q b₀₀q= b₁₀q=)
           (natural-square p₋₁ q b₀₁q= b₁₁q=) (natural-square p₁₋ q b₁₀q= b₁₁q=)
    → sqx == sqy [ (λ z → Square (p₀₋ z) (p₋₀ z) (p₋₁ z) (p₁₋ z)) ↓ q ]
  cube-to-↓-path {q = idp} idp idp idp idp cu = & x-degen-cube-out cu



_|∙³_ : ∀ {i} {A : Type i}
  {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
  {p₀₋₀ p₀₋₀' : a₀₀₀ == a₀₁₀} {p₋₀₀ p₋₀₀' : a₀₀₀ == a₁₀₀}
  {p₋₁₀ p₋₁₀' : a₀₁₀ == a₁₁₀} {p₁₋₀ p₁₋₀' : a₁₀₀ == a₁₁₀}
  {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

  {p₀₋₀= : p₀₋₀ == p₀₋₀'} {p₋₀₀= : p₋₀₀ == p₋₀₀'}
  {p₋₁₀= : p₋₁₀ == p₋₁₀'} {p₁₋₀= : p₁₋₀ == p₁₋₀'}
  {sq₋₋₀' : Square p₀₋₀' p₋₀₀' p₋₁₀' p₁₋₀'} -- middle

  {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
  {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
  {sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- right

  {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
  {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
  {sq₀₋₋ : Square p₀₋₀' p₀₀₋ p₀₁₋ p₀₋₁} -- back
  {sq₋₀₋ : Square p₋₀₀' p₀₀₋ p₁₀₋ p₋₀₁} -- top
  {sq₋₁₋ : Square p₋₁₀' p₀₁₋ p₁₁₋ p₋₁₁} -- bottom
  {sq₁₋₋ : Square p₁₋₀' p₁₀₋ p₁₁₋ p₁₋₁} -- front

  → FlatCube sq₋₋₀ sq₋₋₀' p₀₋₀= p₋₀₀= p₋₁₀= p₁₋₀=
  → Cube sq₋₋₀' sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
  → Cube sq₋₋₀ sq₋₋₁ (p₀₋₀= |∙ sq₀₋₋) (p₋₀₀= |∙ sq₋₀₋) (p₋₁₀= |∙ sq₋₁₋) (p₁₋₀= |∙ sq₁₋₋)
idfc |∙³ idc = idc

_/∙³_ : ∀ {i} {A : Type i} {a b c d : A} {p p' : a == b} {q q' : a == c} {r r' : b == d} {s s' : c == d}
  {sq sq2 : Square p q r s} (sq= : sq == sq2)
  {sq' : Square p' q' r' s'} {p= : p == p'} {q= : q == q'} {r= : r == r'} {s= : s == s'}
  → FlatCube sq2 sq' p= q= r= s=
  → FlatCube sq sq' p= q= r= s=
idp /∙³ idfc = idfc

_∙³/_ : ∀ {i} {A : Type i} {a b c d : A} {p p' : a == b} {q q' : a == c} {r r' : b == d} {s s' : c == d}
  {sq : Square p q r s}
  {sq' : Square p' q' r' s'} {p= : p == p'} {q= : q == q'} {r= : r == r'} {s= : s == s'}
  → FlatCube sq sq' p= q= r= s=
  → {sq'2 : Square p' q' r' s'} → sq' == sq'2
  → FlatCube sq sq'2 p= q= r= s=
idfc ∙³/ idp = idfc

_∙fc_ : ∀ {i} {A : Type i} {a b c d : A} {p p' p'' : a == b} {q q' q'' : a == c} {r r' r'' : b == d} {s s' s'' : c == d}
  {sq : Square p q r s} {sq' : Square p' q' r' s'} {sq'' : Square p'' q'' r'' s''}
  {p= : p == p'} {q= : q == q'} {r= : r == r'} {s= : s == s'}
  {p=' : p' == p''} {q=' : q' == q''} {r=' : r' == r''} {s=' : s' == s''}
  → FlatCube sq  sq'  p=  q=  r=  s=
  → FlatCube sq' sq'' p=' q=' r=' s='
  → FlatCube sq  sq'' (p= ∙ p=') (q= ∙ q=') (r= ∙ r=') (s= ∙ s=')
idfc ∙fc idfc = idfc

infixr 80 _|∙³_ _-∙³_ _/∙³_ _∙fc_ _∙³/_

adapt-flatcube : ∀ {i} {A : Type i} {a b c d : A} {p p' : a == b} {q q' : a == c} {r r' : b == d} {s s' : c == d}
  {p= p=' : p == p'} (p== : p= == p=')
  {q= q=' : q == q'} (q== : q= == q=')
  {r= r=' : r == r'} (r== : r= == r=')
  {s= s=' : s == s'} (s== : s= == s=')
  {sq : Square p q r s} {sq' : Square p' q' r' s'}
  → FlatCube sq sq' p= q= r= s=
  → FlatCube sq sq' p=' q=' r=' s='
adapt-flatcube idp idp idp idp idfc = idfc

!² : ∀ {i} {A : Type i} {a b c d : A} {p : a == b} {q : a == c} {r : b == d} {s : c == d}
  → Square p q r s → Square s (! q) (! r) p
!² ids = ids

!³ : ∀ {i} {A : Type i}
  {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
  {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
  {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
  {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

  {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
  {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
  {sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- right

  {p₀₀ : a₀₀₀ == a₀₀₁} {p₀₁ : a₀₁₀ == a₀₁₁}
  {p₁₀ : a₁₀₀ == a₁₀₁} {p₁₁ : a₁₁₀ == a₁₁₁}
  {sq₀₋ : Square p₀₋₀ p₀₀ p₀₁ p₀₋₁} -- back
  {sq₋₀ : Square p₋₀₀ p₀₀ p₁₀ p₋₀₁} -- top
  {sq₋₁ : Square p₋₁₀ p₀₁ p₁₁ p₋₁₁} -- bottom
  {sq₁₋ : Square p₁₋₀ p₁₀ p₁₁ p₁₋₁} -- front
  → Cube sq₋₋₀ sq₋₋₁ sq₀₋ sq₋₀ sq₋₁ sq₁₋
  → Cube sq₋₋₁ sq₋₋₀ (!² sq₀₋) (!² sq₋₀) (!² sq₋₁) (!² sq₁₋)
!³ idc = idc

natural-square-homotopy : ∀ {i j} {A : Type i} {B : Type j} {a : A}
  → Coh ({u v : A → B} {f g : (x : A) → u x == v x} (h : (x : A) → f x == g x)
      {b : A} (p : a == b)
      {up : u a == u b} {up= : ap u p == up}
      {vp : v a == v b} {vp= : ap v p == vp}
      → FlatCube (natural-square f p up= vp=) (natural-square g p up= vp=) (h a) idp idp (h b))
natural-square-homotopy = path-induction

natural-cube2 : ∀ {i j} {A : Type i} {B : Type j} {a : A} →
  Coh ({f g : A → B} (h : (a : A) → f a == g a) {b : A} {p : a == b} {c : A} {q : a == c} {d : A} {r : b == d}
  {s : c == d} (sq : Square p q r s)
  {fp : f a == f b} {fp= : ap f p == fp} {gp : g a == g b} {gp= : ap g p == gp}
  {fq : f a == f c} {fq= : ap f q == fq} {gq : g a == g c} {gq= : ap g q == gq}
  {fr : f b == f d} {fr= : ap f r == fr} {gr : g b == g d} {gr= : ap g r == gr}
  {fs : f c == f d} {fs= : ap f s == fs} {gs : g c == g d} {gs= : ap g s == gs}
  {fsq : Square fp fq fr fs} (fsq= : FlatCube (ap-square f sq) fsq fp= fq= fr= fs=)
  {gsq : Square gp gq gr gs} (gsq= : FlatCube (ap-square g sq) gsq gp= gq= gr= gs=)
  → Cube (natural-square h p fp= gp=) (natural-square h s fs= gs=) (natural-square h q fq= gq=) fsq gsq (natural-square h r fr= gr=))
natural-cube2 = path-induction

ap-square-idf : ∀ {i} {A : Type i} {a b c d : A} {p : a == b} {q : a == c} {r : b == d} {s : c == d}
  (sq : Square p q r s)
  → FlatCube (ap-square (λ z → z) sq) sq (ap-idf p) (ap-idf q) (ap-idf r) (ap-idf s)
ap-square-idf ids = idfc

hid-flatcube : ∀ {i} {A : Type i} {a b c d : A} {p : a == b} {q : a == c} {r : b == d} {s : c == d} (sq : Square p q r s)
  → FlatCube sq sq idp idp idp idp
hid-flatcube ids = idfc

module _ {i j} {A : Type i} {B : Type j} where

  natural-square= : Coh ({f g : A → B} (h : (a : A) → f a == g a)
          {x y : A} {p p' : x == y} (p= : p == p')
          → {fp : f x == f y} {fp= : ap f p == fp} {fp' : f x == f y} {fp=' : ap f p' == fp'}
          → {gp : g x == g y} {gp= : ap g p == gp} {gp' : g x == g y} {gp=' : ap g p' == gp'}
          → {fp=fp' : fp == fp'} (fp=fp'= : Square (ap (ap f) p=) fp= fp=' fp=fp')
          → {gp=gp' : gp == gp'} (gp=gp'= : Square (ap (ap g) p=) gp= gp=' gp=gp')
          → FlatCube (natural-square h p fp= gp=) (natural-square h p' fp=' gp=') idp fp=fp' gp=gp' idp)
  natural-square= = path-induction

  -- More or less a special case of the previous one
  natural-square== : Coh ({f g : A → B} (h : (a : A) → f a == g a)
          {x y : A} (p : x == y)
          → {fp : f x == f y} {fp= : ap f p == fp} {fp' : f x == f y} {fp=' : ap f p == fp'}
          → {gp : g x == g y} {gp= : ap g p == gp} {gp' : g x == g y} {gp=' : ap g p == gp'}
          → {fpp' : fp == fp'} (fpp'= : ! fp= ∙ fp=' == fpp')
          → {gpp' : gp == gp'} (gpp'= : ! gp= ∙ gp=' == gpp')
          → FlatCube (natural-square h p fp= gp=) (natural-square h p fp=' gp=') idp fpp' gpp' idp)
  natural-square== = path-induction


∘-ap-square : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (g : B → C) (f : A → B)
  {a b c d : A} {p : a == b} {q : a == c} {r : b == d} {s : c == d} (sq : Square p q r s)
  → FlatCube (ap-square g (ap-square f sq)) (ap-square (g ∘ f) sq) (∘-ap g f p) (∘-ap g f q) (∘-ap g f r) (∘-ap g f s)
∘-ap-square g f ids = idfc

ap-square-∘ : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (g : B → C) (f : A → B)
  {a b c d : A} {p : a == b} {q : a == c} {r : b == d} {s : c == d} (sq : Square p q r s)
  → FlatCube (ap-square (g ∘ f) sq) (ap-square g (ap-square f sq)) (ap-∘ g f p) (ap-∘ g f q) (ap-∘ g f r) (ap-∘ g f s)
ap-square-∘ g f ids = idfc

-- Similar to [ap-square-natural-square]
natural-square-ap : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : B → C) →
  Coh ({a b : A} (p : a == b) {u v : A → B} (g : (x : A) → u x == v x)
      {fup : _} {fup= : ap (f ∘ u) p == fup}
      {fvp : _} {fvp= : ap (f ∘ v) p == fvp}
      {up : _} {up= : ap u p == up}
      {vp : _} {vp= : ap v p == vp}
      {apfup : ap f up == fup} (apfup= : Square (∘-ap f u p) (ap (ap f) up=) fup= apfup)
      {apfvp : ap f vp == fvp} (apfvp= : Square (∘-ap f v p) (ap (ap f) vp=) fvp= apfvp)
    → natural-square (ap f ∘ g) p fup= fvp= == adapt-square (ap-square f (natural-square g p up= vp=)) apfup apfvp)
natural-square-ap f = path-induction

cube-rotate : ∀ {i} {A : Type i}
  {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
  {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
  {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
  {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

  {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
  {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
  {sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- right

  {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
  {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
  {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁} -- back
  {sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁} -- top
  {sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁} -- bottom
  {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} -- front
  → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
  → Cube sq₀₋₋ sq₁₋₋ sq₋₋₀ (square-symmetry sq₋₀₋) (square-symmetry sq₋₁₋) sq₋₋₁
cube-rotate idc = idc

horiz-degen-path-hid-square : ∀ {i} → Coh ({A : Type i} {x y : A} {p : x == y} → idp == horiz-degen-path (horiz-degen-square (idp {a = p})))
horiz-degen-path-hid-square = path-induction

module _ {i j k} {A : Type i} {B : Type j} {C : Type k} {g h : B → C} (f : A → B) where

  ↓-ap-in-=' : {x y : A} {p : x == y} (k : (x : A) → g (f x) == h (f x))
               {gfp : g (f x) == g (f y)} {gfp= : ap g (ap f p) == gfp}
    → ↓-ap-in (λ z → g z == h z) f (apd k p) == ↓-='-from-square gfp= idp (natural-square k p (ap-∘ g f p ∙ gfp=) (ap-∘ h f p))
  ↓-ap-in-=' {p = idp} k {gfp= = idp} = & horiz-degen-path-hid-square



module _ {i j} {A : Type i} {a : A} where
 instance
  JCubehorizdegensquare : {B : (p : idp {a = a} == idp) → Cube ids (horiz-degen-square p) ids ids ids ids → Type j}
    → Coh (B idp idc) → Coh ({p : idp == idp} (cube : Cube ids (horiz-degen-square p) ids ids ids ids) → B p cube)
  & (JCubehorizdegensquare {B} d) cube = B= (! horiz-degen-square-η) (! horiz-degen-square-β) horiz-degen-square-◂ cube (& (JCube2 {B = B'} d) cube) where

    B' : (p : Square {a₀₀ = a} idp idp idp idp) → Cube ids p ids ids ids ids → Type j
    B' p c = B (horiz-degen-path p) (c ∙³x & x-degen-cube-in (! horiz-degen-square-β))

    horiz-degen-square-◂ : ∀ {i} {A : Type i} {a a' : A} {p q : a == a'} {r : p == q} → ap horiz-degen-square (! (horiz-degen-square-η {r = r})) == ! horiz-degen-square-β
    horiz-degen-square-◂ {p = idp} {r = idp} = idp

    B= : {p' p : idp == idp} (p= : p == p') (p=' : horiz-degen-square p == horiz-degen-square p') (p== : ap horiz-degen-square p= == p=')
         (c : Cube ids (horiz-degen-square p) ids ids ids ids)
         → B p' (c ∙³x & x-degen-cube-in p=') → B p c
    B= idp _ idp c = transport (B _) (& eq c)  where

      eq : Coh ({sq : Square (idp {a = a}) idp idp idp} (c : Cube ids sq ids ids ids ids) → c ∙³x & x-degen-cube-in idp == c)
      eq = path-induction
