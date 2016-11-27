{-
Comments of the following form are parsed automatically by [extract.py] in order
to convert them to LaTeX and include them in the pdf.

{-<nameofbloc>-}
code
code
code
{-</>-}

-}

{-# OPTIONS --without-K --rewriting #-}

open import PathInduction
open import Pushout

module JamesTwoMaps {i} (A : Type i) (⋆A : A) where

-- We first define [J], [ι], [α] and [β].
-- We need [JS] to make the termination checker happy.

{-<defJiab>-}
J   : ℕ → Type i
JS  : ℕ → Type i
ι   : (n : ℕ) → J n → JS n
α   : (n : ℕ) → A → J n → JS n
β   : (n : ℕ) (x : J n) → α n ⋆A x == ι n x

data J0 : Type i where
  ε : J0

J 0 = J0
J (S n) = JS n

JS 0 = A
JS (S n) = Pushout (span (A × JS n) (JS n) X f g)  module JS where

  X : Type i
  X = Pushout (span (A × J n) (JS n) (J n) (λ x → (⋆A , x)) (ι n))

  f : X → A × JS n
  f = Pushout-rec (λ {(a , x) → (a , ι n x)}) (λ y → (⋆A , y)) (λ x → idp)

  g : X → JS n
  g = Pushout-rec (λ {(a , x) → α n a x}) (λ y → y) (β n)

ι 0 ε = ⋆A
ι (S n) x = inr x

α 0 a ε = a
α (S n) a x = inl (a , x)

β 0 ε = idp
β (S n) x = push (inr x)
{-</>-}

-- We can now define [γ] and [η]

{-<defge>-}
γ : (n : ℕ) (a : A) (x : J n) → α (S n) a (ι n x) == ι (S n) (α n a x)
γ n a x = push (inl (a , x))

η : (n : ℕ) (x : J n)
  → Square (γ n ⋆A x) idp (ap (ι (S n)) (β n x)) (β (S n) (ι n x))
η n x = natural-square push (push x) α-f-push ι-g-push  where

  α-f-push : ap (uncurry (α (S n)) ∘ JS.f n) (push x) == idp
  α-f-push =  ap-∘ (uncurry (α (S n))) (JS.f n) (push x)
              ∙ ap (ap (uncurry (α (S n)))) (push-β _)

  ι-g-push : ap (ι (S n) ∘ JS.g n) (push x) == ap (ι (S n)) (β n x)
  ι-g-push =  ap-∘ (ι (S n)) (JS.g n) (push x)
              ∙ ap (ap (ι (S n))) (push-β _)
{-</>-}

-- We define the more convenient elimination principle for JSS n:

{-<JSSElim>-}
module _ {l} (n : ℕ) {P : JS (S n) → Type l}
  (ι* : (x : JS n) → P (ι (S n) x))
  (α* : (a : A) (x : JS n) → P (α (S n) a x))
  (β* : (x : JS n) → α* ⋆A x == ι* x [ P ↓ β (S n) x ])
  (γ* : (a : A) (x : J n) → α* a (ι n x) == ι* (α n a x) [ P ↓ γ n a x ])
  (η* : (x : J n) → SquareOver P (η n x)  (γ* ⋆A x)
                                          idp
                                          (↓-ap-in P inr (apd ι* (β n x)))
                                          (β* (ι n x)))
  where

  JSS-elim : (x : JS (S n)) → P x
  JSS-elim = Pushout-elim (uncurry α*) ι* JSS-elim-push  where

    JSS-elim-push : (x : JS.X n) → uncurry α* (JS.f n x) == ι* (JS.g n x) [ P ↓ push x ]
    JSS-elim-push = Pushout-elim (uncurry γ*) β*
          (λ x → ↓-PathOver-from-square
               (adapt-SquareOver
                 (↓-ap-in-coh P (uncurry α*)) (↓-ap-in-coh P ι*)
                 (η* x)))
{-</>-}

{-<JSSRec>-}
module _ {l} (n : ℕ) {X : Type l}
  (ι* : JS n → X)
  (α* : A → JS n → X)
  (β* : (x : JS n) → α* ⋆A x == ι* x)
  (γ* : (a : A) (x : J n) → α* a (ι n x) == ι* (α n a x))
  (η* : (x : J n) → Square (γ* ⋆A x) idp (ap ι* (β n x)) (β* (ι n x)))
  where

  JSS-rec : JS (S n) → X
  JSS-rec = Pushout-rec (uncurry α*) ι* JSS-rec-push  module _ where

    JSS-rec-push : (c : JS.X n) → uncurry α* (JS.f n c) == ι* (JS.g n c)
    JSS-rec-push = Pushout-elim (uncurry γ*) β* (λ x → ↓-='-from-square (α-f-push x) (ι-g-push x) (η* x))  where

      α-f-push : (x : J n) → ap ((uncurry α*) ∘ (JS.f n)) (push x) == idp
      α-f-push x = ap-∘ _ _ (push x) ∙ ap (ap (uncurry α*)) (push-β x)

      ι-g-push : (x : J n) → ap (ι* ∘ (JS.g n)) (push x) == ap ι* (β n x)
      ι-g-push x = ap-∘ ι* _ (push x) ∙ ap (ap ι*) (push-β x)

module _ {l} (n : ℕ) {X : Type l}
  {ι* : JS n → X}
  {α* : A → JS n → X}
  {β* : (x : JS n) → α* ⋆A x == ι* x}
  {γ* : (a : A) (x : J n) → α* a (ι n x) == ι* (α n a x)}
  {η* : (x : J n) → Square (γ* ⋆A x) idp (ap ι* (β n x)) (β* (ι n x))}
  where

  private JSS-rec' = JSS-rec n ι* α* β* γ* η*
  private JSS-rec-push' = JSS-rec-push n ι* α* β* γ* η*

  β-β : (x : JS n) → ap JSS-rec' (β (S n) x) == β* x
  β-β x = push-β (inr x)

  γ-β : (a : A) (x : J n) → ap JSS-rec' (γ n a x) == γ* a x
  γ-β a x = push-β (inl (a , x))

  η-β : (x : J n) → FlatCube (ap-square JSS-rec' (η n x))
                             (η* x)
                             (γ-β ⋆A x)
                             idp
                             (∘-ap JSS-rec' inr (β n x))
                             (β-β (ι n x))
  η-β x = adapt-flatcube ∙idp
                         (& coh (ap-∘3 JSS-rec' inl  _ (push x)) (natural-square (ap-∘ JSS-rec' inl)  (push-β x) idp (ap-∘ (ap JSS-rec') (ap inl)  _)) (ap-∙ _ _ _))
                         (& coh (ap-∘3 JSS-rec' inr _ (push x)) (natural-square (ap-∘ JSS-rec' inr) (push-β x) idp (ap-∘ (ap JSS-rec') (ap inr) _)) (ap-∙ _ _ _))
                         ∙idp
            ((& (ap-square-natural-square JSS-rec') (push x) push idp idp
            /∙³ & natural-square-homotopy push-β (push x)
            ∙fc & natural-square== JSS-rec-push' (push x) idp idp
            ∙³/ natural-square-β JSS-rec-push' (push x) (push-βd x)))  where

    coh : Coh ({A : Type l} {a b c d : A} {p : a == b} {q : a == c} {r : b == d} {s : c == d} (sq1 : Square p q r s)
                {e : A} {t : c == e} {f : A} {u : d == f} {v : e == f} (sq2 : Square s t u v)
                {ru : b == f} (ru= : ru == r ∙ u)
                → idp ∙ ! (p ∙ ru) ∙ q ∙ t == ! v)
    coh = path-induction
{-</>-}

-- Let’s now define JA

{-<defJA>-}
postulate
  JA  : Type i
  εJ  : JA
  αJ  : A → JA → JA
  δJ  : (x : JA) → x == αJ ⋆A x

module _ {l} {P : JA → Type l}
  (εJ*  : P εJ)
  (αJ*  : (a : A) (x : JA) → P x → P (αJ a x))
  (δJ*  : (x : JA) (y : P x) → y == αJ* ⋆A x y [ P ↓ (δJ x)]) where

  postulate
    JA-elim  : (x : JA) → P x
    εJ-β     : JA-elim εJ ↦ εJ*
    αJ-β     : (a : A) (x : JA) → JA-elim (αJ a x) ↦ αJ* a x (JA-elim x)
    {-# REWRITE εJ-β #-}
    {-# REWRITE αJ-β #-}
    δJ-βd'   : (x : JA) → apd JA-elim (δJ x) == δJ* x (JA-elim x)
{-</>-}

δJ-βd : ∀ {l} {P : JA → Type l}
  {εJ* : P εJ}
  {αJ* : (a : A) (x : JA) → P x → P (αJ a x)}
  {δJ* : (x : JA) (y : P x) → y == αJ* ⋆A x y [ P ↓ (δJ x)]}
  → (x : JA) → apd (JA-elim εJ* αJ* δJ*) (δJ x) == δJ* x (JA-elim εJ* αJ* δJ* x)
δJ-βd = δJ-βd' _ _ _

JA-rec : ∀ {l} {P : Type l}
  (εJ* : P)
  (αJ* : (a : A) → P → P)
  (δJ* : (y : P) → y == αJ* ⋆A y)
  → JA → P
JA-rec εJ* αJ* δJ* = JA-elim εJ* (λ a x y → αJ* a y) (λ x y → ↓-cst-in (δJ* y))

δJ-β : ∀ {l} {P : Type l}
  {εJ* : P}
  {αJ* : (a : A) → P → P}
  {δJ* : (y : P) → y == αJ* ⋆A y}
  → (x : JA) → ap (JA-rec εJ* αJ* δJ*) (δJ x) == δJ* (JA-rec εJ* αJ* δJ* x)
δJ-β x = apd=cst-in (δJ-βd x)


-- We define the structure on JA

{-<defgJeJ>-}
module _ {i} {X : Type i} (α : A → X → X) (δ : (x : X) → x == α ⋆A x) where

  γ-ify : (a : A) (x : X) → α a (α ⋆A x) == α ⋆A (α a x)
  γ-ify a x = ! (ap (α a) (δ x)) ∙ δ (α a x)

  η-ify : (x : X) → γ-ify ⋆A x == idp
  η-ify = λ x → & coh (natural-square δ (δ x) (ap-idf (δ x)) idp)  module ηIfy where

    coh : Coh  ({A : Type i} {a b : A} {p : a == b}
               {c : A} {q r : b == c} (sq : Square p p q r)
               → ! q ∙ r == idp)
    coh = path-induction

γJ : (a : A) (x : JA) → αJ a (αJ ⋆A x) == αJ ⋆A (αJ a x)
γJ = γ-ify αJ δJ

ηJ : (x : JA) → γJ ⋆A x == idp
ηJ = η-ify αJ δJ
{-</>-}

-- The functions [inJS-ι], [inJS-α] and [inJS-β] are to be thought of as
-- reduction rules.
{-<definJpushJ>-}
inJ   : (n : ℕ) → J n → JA
inJS  : (n : ℕ) → J (S n) → JA

inJS-ι  : (n : ℕ) (x : J n) → inJS n (ι n x) == αJ ⋆A (inJ n x)
inJS-α  : (n : ℕ) (a : A) (x : J n) → inJS n (α n a x) == αJ a (inJ n x)
inJS-β  : (n : ℕ) (x : J n) → Square (ap (inJS n) (β n x)) (inJS-α n ⋆A x) (inJS-ι n x) idp

inJ 0 ε = εJ
inJ (S n) x = inJS n x

inJS 0 a = αJ a εJ
inJS (S n) = JSS-rec n ι* α* β* γ* η*  module InJS where

  ι* : JS n → JA
  ι* x = αJ ⋆A (inJS n x)

  α* : A → JS n → JA
  α* a x = αJ a (inJS n x)

  β* : (x : JS n) → α* ⋆A x == ι* x
  β* x = idp

  γ* : (a : A) (x : J n) → α* a (ι n x) == ι* (α n a x)
  γ* a x = ap (αJ a) (inJS-ι n x) ∙ γJ a (inJ n x) ∙ ! (ap (αJ ⋆A) (inJS-α n a x))

  η* : (x : J n) → Square (γ* ⋆A x) idp (ap (αJ ⋆A ∘ inJS n) (β n x)) (β* (ι n x))
  η* x = & coh  (ηJ (inJ n x))
                (ap-square (αJ ⋆A) (inJS-β n x))
                (ap-∘ (αJ ⋆A) (inJS n) _)  module η* where

        coh :  Coh  ({A : Type i} {a b : A} {p : a == b} {c : A} {r : c == b}
                    {q : b == b} (q= : q == idp) {t : c == a} (sq : Square t r p idp)
                    {t' : c == a} (t= : t' == t)
               → Square (p ∙ q ∙ ! r) idp t' idp)
        coh = path-induction

inJS-ι 0 ε = idp
inJS-ι (S n) x = idp

inJS-α 0 a ε = idp
inJS-α (S n) a x = idp

inJS-β 0 ε = ids
inJS-β (S n) x = horiz-degen-square (push-β _)


pushJ : (n : ℕ) (x : J n) → inJ n x == inJ (S n) (ι n x)
pushJ n x = δJ (inJ n x) ∙ ! (inJS-ι n x)
{-</>-}

-- [inJS-β] applied for [n = S n] gives a degenerate square.
-- It is sometimes more convenient to see it as a 2-path as belown.
inJS-βS : (n : ℕ) (x : J (S n)) → ap (inJS (S n)) (β (S n) x) == idp
inJS-βS n x = push-β _


-- We give reduction rules for [inJS (S n)] applied to [γ] and [η] which are
-- more convenient to use

inJSS-γ : (n : ℕ) (a : A) (x : J n) → Square (ap (inJS (S n)) (γ n a x)) (ap (αJ a) (inJS-ι n x)) (ap (αJ ⋆A) (inJS-α n a x)) (γJ a (inJ n x))
inJSS-γ n a x = & coh (γ-β n a x)  module InJSγ where

  coh : Coh ({A : Type i} {a c : A} {q : a == c} {d : A} {s : c == d} {b : A} {r : b == d} {p : a == b}
        → p == q ∙ s ∙ ! r
        → Square p q r s)
  coh = path-induction


ap-inJSS-ι : (n : ℕ) {x y : J (S n)} (p : x == y) → ap (inJS (S n)) (ap (ι (S n)) p) == ap (αJ ⋆A) (ap (inJS n) p)
ap-inJSS-ι n p = ∘-ap (inJS (S n)) (ι (S n)) p ∙ ap-∘ (αJ ⋆A) (inJS n) p

inJSS-η : (n : ℕ) (x : J n) → Cube (ap-square (inJS (S n)) (η n x))
                                   (horiz-degen-square (ηJ (inJ n x)))
                                   (inJSS-γ n ⋆A x)
                                   vid-square
                                   (ap-inJSS-ι n (β n x) |∙ ap-square (αJ ⋆A) (inJS-β n x))
                                   (inJS-βS n (ι n x) |∙ vid-square)
inJSS-η n x = & coh (η-β n x)  where

  coh : {A : Type i} {a : A} → Coh ({r : a == a} {right : r == idp}
        {b : A} {s : b == a} {c : A} {t : b == c} {u : c == c} {to : u == idp}
        {s' : b == a} {down : s == s'} {s'' : b == a} {down' : s' == s''}
        {p : a == c} {down2 : Square s'' t p idp}
        {q : a == b} {sq : q == p ∙ u ∙ ! t} {from : Square q idp s r}
        → FlatCube from (& (InJS.η*.coh n x) to down2 down') sq idp down right
        → Cube from (horiz-degen-square to) (& (InJSγ.coh n ⋆A x) sq) vid-square ((down ∙ down') |∙ down2) (right |∙ vid-square))
  coh = path-induction

-- This function is used to apply a function to the result of [inJSS-η]
ap-shapeInJSη : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {a : A}
  → Coh ({r : a == a} {right : r == idp} {b : A} {q : a == b}
  {c : A} {p : a == c} {u : c == c} {to : u == idp} {t : b == c} {left : Square q p t u}
  {s' : b == a} {down3 : Square s' t p idp} {s : b == a} {down1 : s == s'}
  {from : Square q idp s r}
  → Cube from (horiz-degen-square to) left vid-square (down1 |∙ down3) (right |∙ vid-square)
  → {ft : f b == f c} (ft= : ap f t == ft) {fp : f a == f c} (fp= : ap f p == fp)
  → Cube (ap-square f from) (horiz-degen-square (ap (ap f) to))
         (adapt-square (ap-square f left) fp= ft=) vid-square
         (adapt-square (ap (ap f) down1 |∙ ap-square f down3) ft= fp=) (ap (ap f) right |∙ vid-square))
ap-shapeInJSη f = path-induction

-- Definition of J∞A

{-<defJiA>-}
postulate
  J∞A    : Type i
  in∞    : (n : ℕ) (x : J n) → J∞A
  push∞  : (n : ℕ) (x : J n) → in∞ n x == in∞ (S n) (ι n x)

module _ {l} {P : J∞A → Type l}
  (in∞*    : (n : ℕ) (x : J n) → P (in∞ n x))
  (push∞*  : (n : ℕ) (x : J n) → in∞* n x == in∞* (S n) (ι n x) [ P ↓ (push∞ n x) ])  where

  postulate
    J∞A-elim   : (x : J∞A) → P x
    in∞-β      : (n : ℕ) (x : J n) → J∞A-elim (in∞ n x) ↦ in∞* n x
    {-# REWRITE in∞-β #-}
    push∞-βd'  : (n : ℕ) (x : J n) → apd J∞A-elim (push∞ n x) == push∞* n x
{-</>-}

push∞-βd : ∀ {l} {P : J∞A → Type l}
  {in∞* : (n : ℕ) (x : J n) → P (in∞ n x)}
  {push∞* : (n : ℕ) (x : J n) → in∞* n x == in∞* (S n) (ι n x) [ P ↓ (push∞ n x) ]}
  → (n : ℕ) (x : J n) → apd (J∞A-elim in∞* push∞*) (push∞ n x) == push∞* n x
push∞-βd = push∞-βd' _ _

J∞A-rec : ∀ {l} {P : Type l}
  (in∞* : (n : ℕ) (x : J n) → P)
  (push∞* : (n : ℕ) (x : J n) → in∞* n x == in∞* (S n) (ι n x))
  → J∞A → P
J∞A-rec in∞* push∞* = J∞A-elim in∞* (λ n x → ↓-cst-in (push∞* n x))

push∞-β : ∀ {l} {P : Type l}
  {in∞* : (n : ℕ) (x : J n) → P}
  {push∞* : (n : ℕ) (x : J n) → in∞* n x == in∞* (S n) (ι n x)}
  → (n : ℕ) (x : J n) → ap (J∞A-rec in∞* push∞*) (push∞ n x) == push∞* n x
push∞-β n x = apd=cst-in (push∞-βd n x)


-- Structure on J∞A

{-<defstructinf>-}
ε∞ : J∞A
ε∞ = in∞ 0 ε


α∞ : A → J∞A → J∞A
α∞ a = J∞A-rec α∞-in∞ α∞-push∞  module _ where

  α∞-in∞ : (n : ℕ) (x : J n) → J∞A
  α∞-in∞ n x = in∞ (S n) (α n a x)

  α∞-push∞ : (n : ℕ) (x : J n) → α∞-in∞ n x == α∞-in∞ (S n) (ι n x)
  α∞-push∞ n x = push∞ (S n) (α n a x) ∙ ! (ap (in∞ (S (S n))) (γ n a x))


δ∞ : (x : J∞A) → x == α∞ ⋆A x
δ∞ = J∞A-elim δ∞-in∞ (λ n x → ↓-='-from-square (ap-idf (push∞ n x)) idp (δ∞-push∞ n x))
  module _ where

  δ∞-in∞ : (n : ℕ) (x : J n) → in∞ n x == α∞ ⋆A (in∞ n x)
  δ∞-in∞ n x = push∞ n x ∙ ! (ap (in∞ (S n)) (β n x))

  δ∞-push∞ : (n : ℕ) (x : J n) → Square  (δ∞-in∞ n x)
                                         (push∞ n x)
                                         (ap (α∞ ⋆A) (push∞ n x))
                                         (δ∞-in∞ (S n) (ι n x))
  δ∞-push∞ = λ n x →
    & coh  (push∞ n x)
           (ap-square (in∞ (S (S n))) (η n x))
           (natural-square (push∞ (S n)) (β n x) idp (ap-∘ _ _ _))
           (push∞-β n x)
             module δ∞Push∞ where

    coh : Coh  ({A : Type i} {a b : A} (p : a == b) {d : A} {s : d == b}
               {c : A} {r : b == c} {f : A} {u : f == c} {e : A} {t : e == c}
               {w : f == e} (eta : Square w idp t u)
               {v : d == e} (nat : Square v s t r)
               {vw : d == f} (vw= : vw == v ∙ ! w)
               → Square (p ∙ ! s) p vw (r ∙ ! u))
    coh = path-induction
{-</>-}

    ap-coh : {A B : Type i} (g : A → B) →
             Coh ({a b : A} {p : a == b} {d : A} {s : d == b}
                 {c : A} {r : b == c} {f : A} {u : f == c} {e : A} {t : e == c}
                 {w : f == e} {eta : Square w idp t u}
                 {v : d == e} {nat : Square v s t r}
                 {vw : d == f} {vw= : vw == v ∙ ! w}
                 → FlatCube (ap-square g (& coh p eta nat vw=))
                            (& coh (ap g p) (ap-square g eta) (ap-square g nat) (ap-shape-∙! g vw=))
                            (ap-∙! g p s) idp idp (ap-∙! g r u))
    ap-coh g = path-induction


ap-α∞-in∞ : (n : ℕ) (a : A) {x y : J n} (p : x == y) → ap (α∞ a) (ap (in∞ n) p) == ap (in∞ (S n)) (ap (α n a) p)
ap-α∞-in∞ n a p = ∘-ap _ _ _ ∙ ap-∘ _ _ _

δ∞-in∞-β : (n : ℕ) (x : J n) → Square (δ∞ (in∞ n x)) idp (ap (in∞ (S n)) (β n x)) (push∞ n x)
δ∞-in∞-β = λ n x → & coh  module δ∞Inβ where

  coh : Coh ({A : Type i} {a b : A} {p : a == b} {c : A} {q : c == b} → Square (p ∙ ! q) idp q p)
  coh = path-induction


-- [γ∞] and the reduction rule for [γ∞ a (in∞ n x)] (3.2.6)

{-<gammainfin>-}
γ∞ : (a : A) (x : J∞A) → α∞ a (α∞ ⋆A x) == α∞ ⋆A (α∞ a x)
γ∞ = γ-ify α∞ δ∞

γ∞-in  : (a : A) (n : ℕ) (x : J n)
       → Square  (γ∞ a (in∞ n x))
                 (ap (in∞ (S (S n))) (ap (α (S n) a) (β n x)))
                 (ap (in∞ (S (S n))) (β (S n) (α n a x)))
                 (ap (in∞ (S (S n))) (γ n a x))
γ∞-in = λ a n x → & coh (push∞-β n x) (ap-∙! _ _ _) (ap-α∞-in∞ (S n) a (β n x))
                  module γ∞In where

  coh : Coh  ({A : Type i} {a d : A} {r : a == d} {b : A} {s : b == d}
             {c : A} {t' : c == b} {e : A} {u : e == d}
             {rs' : a == b} (rs= : rs' == r ∙ ! s)
             {fpq : a == c} (fpq= : fpq == rs' ∙ ! t')
             {t : c == b} (t= : t' == t)
             → Square (! fpq ∙ (r ∙ ! u)) t u s)
  coh = path-induction
{-</>-}

-- [η∞] and the reduction rule for [η∞ a (in∞ n x)] (3.2.7)

comp-square : {A : Type i} {a b c : A} {p : a == b} {q : b == c} → Square idp p (p ∙ q) q
comp-square {p = idp} {q = idp} = ids

skew : ∀ {i} {A : Type i} {a b c d : A} {p : a == b} {q : a == c} {r : b == d} {s : c == d} → Square p q r s → Square idp q (p ∙ r) s
skew ids = ids

ope1 : {A B : Type i} (f : A → B) {a b c : A} {p : a == b} {q : c == b}
       {fp : _} (fp= : ap f p == fp)
       {fq : _} (fq= : ap f q == fq)
       {fpq : _} (fpq= : ap f (p ∙ ! q) == fpq)
       → fpq == fp ∙ ! fq
ope1 f {p = idp} {q = idp} idp idp idp = idp

_∙!²_ : {A : Type i} {a b c : A} {p p' : a == b} (p= : p == p') {q q' : c == b} (q= : q == q')
        → (p ∙ ! q) == (p' ∙ ! q')
idp ∙!² idp = idp

ope1-idf : {A B : Type i} (f : A → B) → Coh ({b c : A} {q : c == b} {a : B} {p : a == f b}
         → ope1 (λ z → z) (ap-idf p) (∘-ap (λ z → z) f q ∙ idp) (ap-idf (p ∙ ! (ap f q))) == idp)
ope1-idf f = path-induction

natural-square-∙! : {A B : Type i} {a b c : A} (p : a == b) (q : c == b) → Coh ({f g : A → B} (h : (a : A) → f a == g a)
         {fp : _} {fp= : ap f p == fp}
         {gp : _} {gp= : ap g p == gp}
         {fq : _} {fq= : ap f q == fq}
         {gq : _} {gq= : ap g q == gq}
         {fpq : _ } {fpq= : ap f (p ∙ ! q) == fpq}
         {gpq : _ } {gpq= : ap g (p ∙ ! q) == gpq}
         → FlatCube (natural-square h (p ∙ ! q) fpq= gpq=) (natural-square h p fp= gp= ∙□ !² (natural-square h q fq= gq=)) idp (ope1 f fp= fq= fpq=) (ope1 g gp= gq= gpq=) idp)
natural-square-∙! {a = a} idp idp = path-induction

vcomp! : {A : Type i} {a b c d e f : A} {p : a == b} {q : a == c} {r : b == d} {s : c == d} {t : e == b} {u : f == d} {v : e == f}
         (sq1 : Square p q r s) (sq2 : Square t v r u)
       → Square (p ∙ ! t) q v (s ∙ ! u)
vcomp! {t = idp} ids ids = ids

natural-square∙! : {A B : Type i} {a b : A} (p : a == b)
       → Coh ({f g : A → B} (k : (a : A) → f a == g a) {h : A → B} (l : (a : A) → h a == g a)
              {fp : _} {fp= : ap f p == fp}
              {gp : _} {gp= : ap g p == gp}
              {hp : _} {hp= : ap h p == hp}
             → natural-square (λ x → k x ∙ ! (l x)) p fp= hp= == vcomp! (natural-square k p fp= gp=) (natural-square l p hp= gp=))
natural-square∙! {a = a} idp = path-induction

η∞ : (x : J∞A) → γ∞ ⋆A x == idp
η∞ = η-ify α∞ δ∞

η∞-in  : (n : ℕ) (x : J n)
       → Cube  (horiz-degen-square (η∞ (in∞ n x)))
               (ap-square (in∞ (S (S n))) (η n x))
               (γ∞-in ⋆A n x)
               vid-square
               comp-square
               (skew (ap-square (in∞ (S (S n))) (natural-square (β (S n)) (β n x) idp idp)))
η∞-in n x = & coh  (push∞-β n x)
                   (& (coh-ope1 (α∞ ⋆A)))
                   (& (ope1-idf (in∞ (S n))))
                   (natural-square-β δ∞ (push∞ n x) (push∞-βd n x))
                   (& (ap-square-natural-square (in∞ (S (S n)))) (β n x) (β (S n)) ∙idp ∙idp)
                   (& (natural-square∙! (β n x)) (push∞ (S n)) (ap (in∞ (S (S n))) ∘ β (S n)))
                   (& (natural-square-∘ (β n x) (in∞ (S n))) δ∞ idp idp)
                   (& (natural-square-∙! (push∞ n x) (ap (in∞ (S n)) (β n x))) δ∞)
                where

  coh-ope1 : {A B : Type i} (f : A → B)
           → Coh ({x y : A} {p : x == y}
                  {z : A} {q : z == y} {fq : f z == f y} {r : ap f q == fq}
                  → ap-∙! f p q == ope1 f idp r idp ∙ (idp ∙!² ! r))
  coh-ope1 f = path-induction

  -- X = apin∞SS
  coh : Coh ({A : Type i} {a b : A} {push∞Sα : a == b} {c : A} {apin∞Sβ : a == c} {d : A} {XapιSβ : b == d}
        {f : A} {Xγ : f == b} {XβSι : f == d} {apinη : Square Xγ idp XapιSβ XβSι}
        {push∞Sι : c == d} {natpush∞Sβ : Square push∞Sα apin∞Sβ XapιSβ push∞Sι}
        {e : A} {XβSα : e == b} {XapαSβ : e == f} {natβSβ : Square XβSα XapαSβ XapιSβ XβSι}
        {g : A} {p : g == c}
        {rs : a == f}
        (rs= : rs == push∞Sα ∙ ! Xγ)
        {z : _}
        {z= : z == rs ∙ ! XapαSβ}
        {t : _} {t= : t == XapαSβ}
        {fpq= : z == rs ∙ ! t}
        (fpq== : fpq= == z= ∙ (idp ∙!² ! t=))
        {pq=' : _} (pq== : pq=' == idp)
        {α' : _} (α= : α' == (& δ∞Push∞.coh p apinη natpush∞Sβ rs=))
        {γ' : _} (γ= : natβSβ == γ')
        {βγ : _} (βγ=comp : βγ == vcomp! natpush∞Sβ γ')
        {βγ' : _} (βγ= : βγ == βγ')
        {sq : _} (sq= : FlatCube sq (α' ∙□ !² βγ') idp pq=' z= idp)
      → Cube (horiz-degen-square (& (ηIfy.coh α∞ δ∞) sq))
             apinη
             (& γ∞In.coh rs= fpq= t=)
             vid-square
             comp-square
             (skew natβSβ))
  coh = path-induction


-- The two maps

{-<twomaps>-}
to : J∞A → JA
to = J∞A-rec inJ pushJ

from : JA → J∞A
from = JA-rec ε∞ α∞ δ∞
{-</>-}

-- Rules which better match the intuitive definition of [pushJ n x]
to-push∞ : (n : ℕ) (x : J n) → Square (ap to (push∞ n x)) idp (inJS-ι n x) (δJ (inJ n x))
to-push∞ n x = & coh (push∞-β n x)  where

  coh : Coh ({A : Type i} {a b : A} {p : a == b} {c : A} {q : c == b} {r : a == c} (r= : r == p ∙ ! q) → Square r idp q p)
  coh = path-induction

to-push∞-S : (n : ℕ) (x : J (S n)) → ap to (push∞ (S n) x) == δJ (inJ (S n) x)
to-push∞-S n x = horiz-degen-path (to-push∞ (S n) x)


ap-from-αJ : (a : A) {x y : JA} (p : x == y) → ap from (ap (αJ a) p) == ap (α∞ a) (ap from p)
ap-from-αJ a p = ∘-ap _ _ _ ∙ ap-∘ _ _ _

ap-square-from-αJ : (a : A) {x y z t : JA} {p : x == y} {q : x == z} {r : y == t} {s : z == t} (sq : Square p q r s)
  → FlatCube (ap-square from (ap-square (αJ a) sq))
             (ap-square (α∞ a) (ap-square from sq))
             (ap-from-αJ _ _) (ap-from-αJ _ _)
             (ap-from-αJ _ _) (ap-from-αJ _ _)
ap-square-from-αJ a ids = idfc

-- Abbreviation for the natural square of [δJ]
ap-δJ : {x y : JA} (p : x == y) → Square (δJ x) p (ap (αJ ⋆A) p) (δJ y)
ap-δJ p = natural-square δJ p (ap-idf p) idp
