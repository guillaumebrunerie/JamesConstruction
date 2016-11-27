{-# OPTIONS --without-K --rewriting #-}

open import PathInduction
open import Pushout

module JamesContractibility {i} (A : Type i) (⋆A : A) where

open import JamesTwoMaps A ⋆A public

-- We do not prove the flattening lemma here, we only prove that the following pushout is contractible

T : Type i
T = Pushout (span JA JA (A × JA) snd (uncurry αJ))

⋆T : T
⋆T = inl εJ

T-contr-inl-ε : inl εJ == ⋆T
T-contr-inl-ε = idp

T-contr-inl-α : (a : A) (x : JA) → inl x == ⋆T → inl (αJ a x) == ⋆T
T-contr-inl-α a x y = push (⋆A , αJ a x) ∙ ! (ap inr (δJ (αJ a x))) ∙ ! (push (a , x)) ∙ y

T-contr-inl-δ : (x : JA) (y : inl x == ⋆T) → Square (ap inl (δJ x)) y (T-contr-inl-α ⋆A x y) idp
T-contr-inl-δ x y = & coh (ap-square inr (& cη (ηJ x))) (natural-square (λ z → push (⋆A , z)) (δJ x) idp (ap-∘ inr (αJ ⋆A) (δJ x)))  where

  coh : Coh ({A : Type i} {a b : A} {p : a == b} {c : A} {q q' : c == b} (q= : Square q q' idp idp)
             {d : A} {r : d == c} {e : A} {s : d == e} {t : d == a} (sq : Square r t q p)
      → Square t s (p ∙ ! q' ∙ ! r ∙ s) idp)
  coh = path-induction

  cη : Coh ({A : Type i} {a b : A} {p : a == b} {c : A} {q : a == c} {r : b == c} (ηJ : ! p ∙ q == r) → Square p q r idp)
  cη = path-induction

T-contr-inl : (x : JA) → inl x == ⋆T
T-contr-inl = JA-elim T-contr-inl-ε T-contr-inl-α (λ x y → ↓-='-from-square idp (ap-cst ⋆T (δJ x)) (square-symmetry (T-contr-inl-δ x y)))

T-contr-inr : (x : JA) → inr x == ⋆T
T-contr-inr x = ap inr (δJ x) ∙ ! (push (⋆A , x)) ∙ T-contr-inl x

T-contr-push : (a : A) (x : JA) → Square (T-contr-inl x) (push (a , x)) idp (T-contr-inr (αJ a x))
T-contr-push a x = & coh  where

  coh : Coh ({A : Type i} {a b : A} {r : a == b} {c : A} {p : c == b} {d : A} {q : d == c} {e : A} {y : d == e}
            → Square y q idp (p ∙ ! r ∙ (r ∙ ! p ∙ ! q ∙ y)))
  coh = path-induction

T-contr : (x : T) → x == ⋆T
T-contr = Pushout-elim T-contr-inl T-contr-inr (λ {(a , x) → ↓-='-from-square (ap-idf (push (a , x))) (ap-cst ⋆T (push (a , x))) (T-contr-push a x)})
