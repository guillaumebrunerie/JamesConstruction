{-# OPTIONS --without-K --rewriting #-}

open import PathInduction using (Type; _==_; idp; Square; !; _∙_; Coh; path-induction)

module ExPathInduction {i} where

{-<excoh>-}
coh :  {A : Type i} {a : A} →
       Coh  ({b : A} (p : a == b)
            {d : A} {s : d == b}
            {c : A} {r : b == c}
            {f : A} {u : f == c}
            {e : A} {t : e == c}
            {w : f == e} (ν : Square w idp t u)
            {v : d == e} (α : Square v s t r)
            {vw : d == f} (vw= : vw == v ∙ ! w)
            → Square (p ∙ ! s) p vw (r ∙ ! u))
coh = path-induction
{-</>-}
