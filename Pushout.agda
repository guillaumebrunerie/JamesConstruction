{-# OPTIONS --without-K --rewriting #-}

open import PathInduction

module Pushout {i} {j} {k} where

{-<Pushout>-}
record Span : Type (lsucc (lmax (lmax i j) k)) where
  constructor span
  field
    A  : Type i
    B  : Type j
    C  : Type k
    f  : C → A
    g  : C → B

postulate
  Pushout : Span → Type (lmax (lmax i j) k)

module _ {d : Span} where

  open Span d

  postulate
    inl   : A → Pushout d
    inr   : B → Pushout d
    push  : (c : C) → inl (f c) == inr (g c)

  module _ {l} {P : Pushout d → Type l}
    (inl*   : (a : A) → P (inl a))
    (inr*   : (b : B) → P (inr b))
    (push*  : (c : C) → inl* (f c) == inr* (g c) [ P ↓ push c ])  where

    postulate
      Pushout-elim  : (x : Pushout d) → P x
      inl-β         : (a : A) → (Pushout-elim (inl a) ↦ inl* a)
      inr-β         : (b : B) → (Pushout-elim (inr b) ↦ inr* b)
      {-# REWRITE inl-β #-}
      {-# REWRITE inr-β #-}
      push-βd'      : (c : C) → (apd Pushout-elim (push c) == push* c)
{-</>-}

  -- Makes the arguments of [push-βd] implicit
  push-βd : ∀ {l} {P : Pushout d → Type l}
    {inl*  : (a : A) → P (inl a)}
    {inr*  : (b : B) → P (inr b)}
    {push* : (c : C) → inl* (f c) == inr* (g c) [ P ↓ push c ]}
    → (c : C) → apd (Pushout-elim inl* inr* push*) (push c) == push* c
  push-βd = push-βd' _ _ _

  -- Non-dependent elimination rule and corresponding reduction rule

{-<PushoutRec>-}
  Pushout-rec : ∀ {l} {D : Type l}
      (inl*  : A → D)
      (inr*  : B → D)
      (push* : (c : C) → inl* (f c) == inr* (g c))
      → Pushout d → D
  Pushout-rec inl* inr* push* = Pushout-elim inl* inr* (λ c → ↓-cst-in (push* c))

  push-β : ∀ {l} {D : Type l}
      {inl*  : A → D}
      {inr*  : B → D}
      {push* : (c : C) → inl* (f c) == inr* (g c)}
      → (c : C) → ap (Pushout-rec inl* inr* push*) (push c) == push* c
  push-β c = apd=cst-in (push-βd c)
{-</>-}
