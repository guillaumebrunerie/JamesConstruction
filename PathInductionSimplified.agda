{-# OPTIONS --without-K --rewriting #-}

open import Base using (Type; Type₀; _==_; idp)

module PathInductionSimplified where

{-<pathinduction>-}
record Coh {i} (A : Type i) : Type i where
  field & : A
open Coh public

instance
  J : ∀ {i j} {A : Type i} {a : A} {B : (a' : A) → a == a' → Type j}
    → Coh (B a idp)
    → Coh ({a' : A} (p : a == a') → B a' p)
  & (J d) idp = & d

  idp-Coh : ∀ {i} {A : Type i} {a : A} → Coh (a == a)
  & idp-Coh = idp

path-induction : ∀ {i} {A : Type i} {{a : A}} → A
path-induction {{a}} = a

composition : ∀ {i} {A : Type i} {a : A}
     → Coh ({b : A} (p : a == b) {c : A} (q : b == c) → a == c)
composition = path-induction

postulate
  A : Type₀
  a b c : A
  p : a == b
  q : b == c

pq : a == c
pq = & composition p q
{-</>-}
