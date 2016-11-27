{-# OPTIONS --without-K --rewriting #-}

module Base where

{-
With the HoTT-Agda library, the following import can be used instead:

open import HoTT using
  (Type; lmax; lsucc;
   _==_; idp; !;
   ap; apd;
   Square; ids; vid-square; hid-square; SquareOver; ↓-ap-in; apd-square;
   app=; λ=; app=-β;
   transport;
   ℕ; O; S; ℕ-reader;
   _×_; _,_; fst; snd;
   _∘_; ap-∘; ap-!;
   PathOver; ↓-cst-in; apd=cst-in; ap-idf; ap-cst; square-symmetry; uncurry; ap-square;
   Cube; idc; ap-cube;
   is-contr) public
-}

open import Agda.Primitive public using (lzero)
  renaming (Level to ULevel; lsuc to lsucc; _⊔_ to lmax)

Type : (i : ULevel) → Set (lsucc i)
Type i = Set i

Type₀ : Set (lsucc lzero)
Type₀ = Type lzero

infix 30 _==_
data _==_ {i} {A : Type i} (a : A) : A → Type i where
  idp : a == a

PathOver : ∀ {i j} {A : Type i} (B : A → Type j)
  {x y : A} (p : x == y) (u : B x) (v : B y) → Type j
PathOver B idp u v = (u == v)

infix 30 PathOver
syntax PathOver B p u v =
  u == v [ B ↓ p ]

ap : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x y : A}
  → (x == y → f x == f y)
ap f idp = idp

apd : ∀ {i j} {A : Type i} {B : A → Type j} (f : (a : A) → B a) {x y : A}
  → (p : x == y) → f x == f y [ B ↓ p ]
apd f idp = idp

transport : ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : x == y)
  → (B x → B y)
transport B idp u = u

infixr 60 _,_

record Σ {i j} (A : Type i) (B : A → Type j) : Type (lmax i j) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

_×_ : ∀ {i j} (A : Type i) (B : Type j) → Type (lmax i j)
A × B = Σ A (λ _ → B)

data ℕ : Type lzero where
  O : ℕ
  S : (n : ℕ) → ℕ

Nat = ℕ

{-# BUILTIN NATURAL ℕ #-}

infixr 80 _∘_

_∘_ : ∀ {i j k} {A : Type i} {B : A → Type j} {C : (a : A) → (B a → Type k)}
  → (g : {a : A} → (x : B a) → (C a x)) → (f : (x : A) → B x) → (x : A) → C x (f x)
g ∘ f = λ x → g (f x)

uncurry : ∀ {i j k} {A : Type i} {B : A → Type j} {C : (x : A) → B x → Type k}
  → (∀ x y → C x y) → (∀ s → C (fst s) (snd s))
uncurry f (x , y) = f x y

record FromNat {i} (A : Type i) : Type (lsucc i) where
  field
    in-range : ℕ → Type i
    read : ∀ n → ⦃ _ : in-range n ⦄ → A

open FromNat ⦃...⦄ public using () renaming (read to from-nat)

{-# BUILTIN FROMNAT from-nat #-}

record ⊤ : Type lzero where
  instance constructor unit

Unit = ⊤

instance
  ℕ-reader : FromNat ℕ
  FromNat.in-range ℕ-reader _ = ⊤
  FromNat.read ℕ-reader n = n

! : ∀ {i} {A : Type i} {x y : A} → x == y → y == x
! idp = idp

data Square {i} {A : Type i} {a₀₀ : A} : {a₀₁ a₁₀ a₁₁ : A}
  → a₀₀ == a₀₁ → a₀₀ == a₁₀ → a₀₁ == a₁₁ → a₁₀ == a₁₁ → Type i
  where
  ids : Square idp idp idp idp

hid-square : ∀ {i} {A : Type i} {a₀₀ a₀₁ : A} {p : a₀₀ == a₀₁}
  → Square p idp idp p
hid-square {p = idp} = ids

vid-square : ∀ {i} {A : Type i} {a₀₀ a₁₀ : A} {p : a₀₀ == a₁₀}
  → Square idp p p idp
vid-square {p = idp} = ids

ap-square : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
  {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  → Square p₀₋ p₋₀ p₋₁ p₁₋
  → Square (ap f p₀₋) (ap f p₋₀) (ap f p₋₁) (ap f p₁₋)
ap-square f ids = ids

SquareOver : ∀ {i j} {A : Type i} (B : A → Type j) {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
  {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁}
  (q₀₋ : b₀₀ == b₀₁ [ B ↓ p₀₋ ]) (q₋₀ : b₀₀ == b₁₀ [ B ↓ p₋₀ ])
  (q₋₁ : b₀₁ == b₁₁ [ B ↓ p₋₁ ]) (q₁₋ : b₁₀ == b₁₁ [ B ↓ p₁₋ ])
  → Type j
SquareOver B ids = Square

apd-square : ∀ {i j} {A : Type i} {B : A → Type j} (f : (x : A) → B x)
  {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
  → SquareOver B sq (apd f p₀₋) (apd f p₋₀) (apd f p₋₁) (apd f p₁₋)
apd-square f ids = ids

square-symmetry : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
    → Square p₀₋ p₋₀ p₋₁ p₁₋ → Square p₋₀ p₀₋ p₁₋ p₋₁
square-symmetry ids = ids

module _ {i j k} {A : Type i} {B : Type j} (C : B → Type k) (f : A → B) where

  ↓-ap-in : {x y : A} {p : x == y} {u : C (f x)} {v : C (f y)}
    → u == v [ C ∘ f ↓ p ]
    → u == v [ C ↓ ap f p ]
  ↓-ap-in {p = idp} idp = idp

-- We postulate function extensionality

module _ {i j} {A : Type i} {P : A → Type j} {f g : (x : A) → P x} where

  app= : (p : f == g) (x : A) → f x == g x
  app= p x = ap (λ u → u x) p

  postulate
    λ= : (h : (x : A) → f x == g x) → f == g
    app=-β : (h : (x : A) → f x == g x) (x : A) → app= (λ= h) x == h x

ap-∘ : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (g : B → C) (f : A → B)
  {x y : A} (p : x == y) → ap (g ∘ f) p == ap g (ap f p)
ap-∘ f g idp = idp

ap-cst : ∀ {i j} {A : Type i} {B : Type j} (b : B) {x y : A} (p : x == y)
  → ap (λ _ → b) p == idp
ap-cst b idp = idp

ap-idf : ∀ {i} {A : Type i} {u v : A} (p : u == v) → ap (λ x → x) p == p
ap-idf idp = idp

module _ {i j} {A : Type i} {B : Type j} (f : A → B) where

  ap-! : {x y : A} (p : x == y)
    → ap f (! p) == ! (ap f p)
  ap-! idp = idp

module _ {i j} {A : Type i} {B : Type j} where

  ↓-cst-in : {x y : A} {p : x == y} {u v : B}
    → u == v
    → u == v [ (λ _ → B) ↓ p ]
  ↓-cst-in {p = idp} q = q

{- Used for defining the recursor from the eliminator for 1-HIT -}
apd=cst-in : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
  {a a' : A} {p : a == a'} {q : f a == f a'}
  → apd f p == ↓-cst-in q → ap f p == q
apd=cst-in {p = idp} x = x

data Cube {i} {A : Type i} {a₀₀₀ : A} :
  {a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
  {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
  {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
  (sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀) -- left

  {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
  {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
  (sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁) -- right

  {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
  {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
  (sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁) -- back
  (sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁) -- top
  (sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁) -- bottom
  (sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁) -- front
  → Type i

  where
  idc : Cube ids ids ids ids ids ids

ap-cube : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
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
  → Cube (ap-square f sq₋₋₀) (ap-square f sq₋₋₁) (ap-square f sq₀₋₋)
         (ap-square f sq₋₀₋) (ap-square f sq₋₁₋) (ap-square f sq₁₋₋)
ap-cube f idc = idc
