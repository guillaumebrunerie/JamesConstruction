{-# OPTIONS --without-K --rewriting #-}

open import PathInduction
open import Pushout

module JamesSecondComposite {i} (A : Type i) (⋆A : A) where

open import JamesTwoMaps A ⋆A public

-- Second composite

to-ε∞ : to ε∞ == εJ
to-ε∞ = idp

to-α∞-in∞ : (a : A) (n : ℕ) (x : J n) → to (α∞ a (in∞ n x)) == αJ a (inJ n x)
to-α∞-in∞ a n x = inJS-α n a x

to-α∞-push∞ : (a : A) (n : ℕ) (x : J n) → Square (ap to (ap (α∞ a) (push∞ n x))) (inJS-α n a x) idp (ap (αJ a) (ap to (push∞ n x)))
to-α∞-push∞ = λ a n x → & coh (ap-shape-∙! to (push∞-β  {in∞* = α∞-in∞ a} {push∞* = α∞-push∞ a} n x))
                              (to-push∞-S n (α n a x))
                              (ap-δJ (inJS-α n a x))
                              (∘-ap _ _ _)
                              (inJSS-γ n a x)
                              (ap-square (αJ a) (to-push∞ n x))  module Toα∞Push∞ where

  coh : Coh ({A : Type i} {a c : A} {q : a == c} {d : A} {r : a == d}
             {b : A} {s : b == d} {p : a == b} (p= : p == r ∙ ! s)
             {r' : a == d} (y= : r == r') {g : A} {w : d == g}
             {v : c == g} (sq : Square r' q w v) {e : A} {u : c == e}
             {s' : b == d} (s= : s == s') {t : b == e} (u= : Square s' t w (! u ∙ v))
             {x : c == b} (x= : Square x idp t u)
      → Square p q idp x)
  coh = path-induction


to-α∞ : (a : A) (x : J∞A) → to (α∞ a x) == αJ a (to x)
to-α∞ a = J∞A-elim (to-α∞-in∞ a) (λ n x → ↓-='-from-square (ap-∘ to (α∞ a) (push∞ n x)) (ap-∘ (αJ a) to (push∞ n x)) (square-symmetry (to-α∞-push∞ a n x)))

to-δ∞-in∞ : (n : ℕ) (x : J n) → Square (ap to (δ∞ (in∞ n x))) idp (to-α∞ ⋆A (in∞ n x)) (δJ (to (in∞ n x)))
to-δ∞-in∞ = λ n x → & coh (∘-ap _ _ _) (ap-square to (δ∞-in∞-β n x)) (to-push∞ n x) (inJS-β n x)  module Toδ∞In where

  coh : Coh ({A : Type i} {a b : A} {p : a == b} {c : A} {r r' : b == c} (r= : r == r')
             {s : a == c} (sq1 : Square p idp r s) {d : A} {t : c == d}
             {u : a == d} (sq2 : Square s idp t u)
             {rt : b == d} (rt= : Square r' rt t idp)
             → Square p idp rt u)
  coh = path-induction


module _ (n : ℕ) (x : J n) where

  side1 : Square (ap to (push∞ (S n) (α n ⋆A x))) (inJS-α n ⋆A x) (ap (αJ ⋆A) (inJS-α n ⋆A x)) (δJ (αJ ⋆A (inJ n x)))
  side1 = to-push∞-S n (α n ⋆A x) |∙ idp |∙ ap-δJ (inJS-α n ⋆A x)

  side2 : Square (ap to (ap (in∞ (S n)) (β n x))) (inJS-α n ⋆A x) (inJS-ι n x) idp
  side2 = idp |∙ ∘-ap to (in∞ (S n)) (β n x) |∙ inJS-β n x

  side3 : Square (ap to (ap (in∞ (S (S n))) (ap inr (β n x)))) (ap (αJ ⋆A) (inJS-α n ⋆A x)) (ap (αJ ⋆A) (inJS-ι n x)) (ap (αJ ⋆A) idp)
  side3 = idp |∙ (∘-ap to (in∞ (S (S n))) _ ∙ ap-inJSS-ι n (β n x)) |∙ ap-square (αJ ⋆A) (inJS-β n x)

  side4 : Square (ap to (push∞ (S n) (ι n x))) (inJS-ι n x) (ap (λ z → αJ ⋆A z) (inJS-ι n x)) (δJ (αJ ⋆A (inJ n x)))
  side4 = to-push∞-S n (ι n x) |∙ idp |∙ ap-δJ (inJS-ι n x)

  side5 : Square (ap to (ap (in∞ (S (S n))) (γ n ⋆A x))) (ap (αJ ⋆A) (inJS-ι n x)) (ap (αJ ⋆A) (inJS-α n ⋆A x)) (γJ ⋆A (inJ n x))
  side5 = ∘-ap to (in∞ (S (S n))) (γ n ⋆A x) |∙ inJSS-γ n ⋆A x

  side6 : Square (ap to (ap (in∞ (S (S n))) (β (S n) (ι n x)))) (ap (αJ ⋆A) (inJS-ι n x)) (ap (αJ ⋆A) (inJS-ι n x)) idp
  side6 = ∘-ap to (in∞ (S (S n))) _ |∙ inJS-βS n (ι n x) |∙ vid-square

  side7 : Square (ap to (ap (α∞ ⋆A) (push∞ n x))) (inJS-α n ⋆A x) (ap (αJ ⋆A) (inJS-ι n x)) (ap (αJ ⋆A) (δJ (inJ n x)))
  side7 = adapt-square (to-α∞-push∞ ⋆A n x ∙□ ap-square (αJ ⋆A) (to-push∞ n x)) ∙idp idp∙

  to-push∞-βn : Cube (ap-square to (natural-square (push∞ (S n)) (β n x) idp (ap-∘ (in∞ (S (S n))) inr (β n x))))
                    hid-square
                    side1
                    side2
                    side3
                    side4
  to-push∞-βn = & (ap-square-natural-square to) (β n x) (push∞ (S n)) ∙idp idp
               -∙³ & natural-square-homotopy (to-push∞-S n) (β n x)
               |∙³ & (natural-square-∘ (β n x) (inJS n)) δJ idp idp
               -∙³ & natural-square= δJ idp (coh1 to (in∞ (S n)) (β n x)) (coh2 to (in∞ (S (S n))) inr (β n x) (ap-∘ (αJ ⋆A) (inJS n) (β n x)))
               |∙³ & natural-cube2 δJ (inJS-β n x) (ap-square-idf (inJS-β n x)) (hid-flatcube _)  where

    coh1 : {A B C : Type i} (g : B → C) (f : A → B) {x y : A} (p : x == y) → Square idp (∘-ap (λ z → z) (g ∘ f) p ∙ ap-∘ g f p) (ap-idf _) (∘-ap g f p)
    coh1 g f idp = ids

    coh2 : {A B C D : Type i} (h : C → D) (g : B → C) (f : A → B) {x y : A} (p : x == y) {z : h (g (f x)) == h (g (f y))} (q : ap (h ∘ g ∘ f) p == z)
         → Square idp (! q ∙ ap-∘ h (g ∘ f) p ∙ ap (ap h) (ap-∘ g f p)) idp (∘-ap h g (ap f p) ∙ ∘-ap (h ∘ g) f p ∙ q)
    coh2 h g f idp idp = ids

  to-in∞-η : Cube (ap-square to (ap-square (in∞ (S (S n))) (η n x)))
                  (horiz-degen-square (ηJ (inJ n x)))
                  side5
                  vid-square
                  side3
                  side6
  to-in∞-η = adapt-cube-idp (∘-ap-square to (in∞ (S (S n))) (η n x)
                            |∙³ inJSS-η n x)
                            idp (& coh1) (& coh2) idp  where

    coh1 : Coh ({A : Type i} {a b : A} {p : a == b} → idp |∙ vid-square {p = p} == vid-square)
    coh1 = path-induction

    coh2 : Coh ({A : Type i} {a b c d : A} {p : a == b} {q : a == c} {r : b == d} {s : c == d} {sq : Square p q r s}
                {p' : a == b} {p= : p' == p} {p'' : a == b} {p=' : p'' == p'} → p=' |∙ p= |∙ sq == idp |∙ (p=' ∙ p=) |∙ sq)
    coh2 = path-induction

  coh-last-one : Coh ({A : Type i} {a b : A} {p : a == b} {c : A} {q : a == c} → p == q ∙ ! (! p ∙ q))
  coh-last-one = path-induction

  last-one : Cube (horiz-degen-square (ap-shape-∙! to (push∞-β {in∞* = α∞-in∞ ⋆A} {push∞* = α∞-push∞ ⋆A} n x)))
                  (horiz-degen-square (& coh-last-one))
                  side7
                  vid-square
                  vid-square
                  (vcomp! side1 side5)
  last-one = & coh  where

    coh : Coh ({A : Type i} {a : A}
               {c : A} {q : a == c} {d : A} {r : a == d} {b : A} {s : b == d}
               {p : a == b} {p= : p == r ∙ ! s}
               {r' : a == d} {y= : r == r'}
               {g : A} {w : d == g} {v : c == g} {sq : Square r' q w v}
               {e : A} {u : c == e} {s' : b == d} {s= : s == s'}
               {t : b == e} {u= : Square s' t w (! u ∙ v)}
               {x : c == b} {x= : Square x idp t u}
               → Cube (horiz-degen-square p=) (horiz-degen-square (& coh-last-one)) (adapt-square (& Toα∞Push∞.coh p= y= sq s= u= x= ∙□ x=) ∙idp idp∙) vid-square vid-square (vcomp! (y= |∙ idp |∙ sq) (s= |∙ u=)))
    coh = path-induction

  δ∞Push∞Coh-coh : Coh ({A : Type i} {a b : A} {p : a == b} {d : A} {s : d == b}
        {c : A} {r : b == c} {f : A} {u : f == c} {e : A} {t : e == c}
        {w : f == e} {eta : Square w idp t u}
        {v : d == e} {nat : Square v s t r}
        {vw : d == f} {vw-eq : vw == v ∙ ! w}
        {a' : _} {a= : a == a'}
        {b' : _} {b= : b == b'}
        {p' : _} {p= : Square p a= b= p'}
        {d' : _} {d= : d == d'}
        {s' : _} {s= : Square s d= b= s'}
        {c' : _} {c= : c == c'}
        {r' : _} {r= : Square r b= c= r'}
        {f' : _} {f= : f == f'}
        {u' : _} {u= : Square u f= c= u'}
        {e' : _} {e= : e == e'}
        {t' : _} {t= : Square t e= c= t'}
        {w' : _} {w= : Square w f= e= w'}
        {eta' : _} (eta= : Cube eta eta' w= vid-square t= u=)
        {v' : _} {v= : Square v d= e= v'}
        {nat' : _} (nat= : Cube nat nat' v= s= t= r=)
        {vw' : _} {vw= : Square vw d= f= vw'}
        {vw-eq' : _} (vw-eq= : Cube (horiz-degen-square vw-eq) (horiz-degen-square vw-eq') vw= vid-square vid-square (vcomp! v= w=))
        → Cube (& δ∞Push∞.coh p eta nat vw-eq) (& δ∞Push∞.coh p' eta' nat' vw-eq') (vcomp! p= s=) p= vw= (vcomp! r= u=))
  δ∞Push∞Coh-coh = path-induction

  piece1 : FlatCube (ap-square to (& δ∞Push∞.coh (push∞ n x) (ap-square (in∞ (S (S n))) (η n x))
                                                (natural-square (push∞ (S n)) (β n x) idp (ap-∘ _ _ _))
                                                (push∞-β {in∞* = α∞-in∞ ⋆A} {push∞* = α∞-push∞ ⋆A} n x)))
                    (& δ∞Push∞.coh (ap to (push∞ n x))
                                  (ap-square to (ap-square (in∞ (S (S n))) (η n x)))
                                  (ap-square to
                                    (natural-square (push∞ (S n)) (β n x) idp
                                                    (ap-∘ (in∞ (S (S n))) (ι (S n)) (β n x))))
                                  (ap-shape-∙! to (push∞-β {in∞* = α∞-in∞ ⋆A} {push∞* = α∞-push∞ ⋆A} n x)))
                    (ap-∙! _ _ _) idp idp (ap-∙! _ _ _)
  piece1 = & (δ∞Push∞.ap-coh to) {b = in∞ (S n) (ι n x)} {d = in∞ (S n) (α n ⋆A x)}

  piece2 : Cube (& δ∞Push∞.coh (ap to (push∞ n x))
                              (ap-square to (ap-square (in∞ (S (S n))) (η n x)))
                              (ap-square to (natural-square (push∞ (S n)) (β n x) idp (ap-∘ (in∞ (S (S n))) inr (β n x))))
                              (ap-shape-∙! to (push∞-β {in∞* = α∞-in∞ ⋆A} {push∞* = α∞-push∞ ⋆A} n x)))
                (& δ∞Push∞.coh (δJ (inJ n x)) (horiz-degen-square (ηJ (inJ n x))) hid-square (& coh-last-one))
                (vcomp! (to-push∞ n x) side2)
                (to-push∞ n x)
                side7
                (vcomp! side4 side6)
  piece2 = & δ∞Push∞Coh-coh to-in∞-η to-push∞-βn last-one

  piece3 : FlatCube (& δ∞Push∞.coh (δJ (inJ n x)) (horiz-degen-square (ηJ (inJ n x))) hid-square (& coh-last-one))
                    (ap-δJ (δJ (inJ n x)))
                    ∙idp idp idp ∙idp
  piece3 = & coh where

    coh : Coh ({A : Type i} {a b : A} {p : a == b} {c : A} {q q' : b == c} {sq : Square p p q q'}
              → FlatCube (& δ∞Push∞.coh p (horiz-degen-square (& (ηIfy.coh αJ δJ) sq)) hid-square (& coh-last-one)) sq ∙idp idp idp ∙idp)
    coh = path-induction

  piece4 : Cube (ap-δJ (ap to (push∞ n x)))
                (ap-δJ (δJ (inJ n x)))
                hid-square (to-push∞ n x) (ap-square (αJ ⋆A) (to-push∞ n x)) (ap-δJ (inJS-ι n x))
  piece4 = & natural-cube2 δJ (to-push∞ n x) (ap-square-idf _) (hid-flatcube _)

  to-δ∞-push∞ : Cube (ap-square to (natural-square δ∞ (push∞ n x) (ap-idf _) idp))
                    (ap-δJ (ap to (push∞ n x)))
                    (to-δ∞-in∞ n x)
                    hid-square
                    (to-α∞-push∞ ⋆A n x)
                    (to-δ∞-in∞ (S n) (ι n x))
  to-δ∞-push∞ = adapt-cube (ap (ap-square to) (natural-square-β δ∞ (push∞ n x) (push∞-βd n x))
                          -∙³ piece1
                          |∙³ piece2
                          ∙³x piece3
                          |∙³ !³ piece4)
                 idp ∙idp !-inv-r !-inv-r
                 (& coh1 (& (coh-flat to) {b = in∞ (S n) (α n ⋆A x)})) (& coh2) (& coh3) (& coh4 (& (coh-flat to) {a = in∞ (S n) (ι n x)})) where

    flat : Coh ({A : Type i} {a c : A} {s : a == c} {b : A} {r : b == c} {p : a == b} (sq : Square p idp r s) → p == s ∙ ! r)
    flat = path-induction

    coh-flat : {A B : Type i} (f : A → B) → Coh ({a c : A} {s : a == c} {b : A} {r : b == c} → & flat (ap-square f (& δ∞Inβ.coh)) == ap-∙! f s r)
    coh-flat f = path-induction

    coh1 : Coh ({A : Type i} {a b : A} {p : a == b} {c : A} {r r' : b == c} {r= : r == r'}
                {s : a == c} {sq1 : Square p idp r s} {d : A} {t : c == d}
                {u : a == d} {sq2 : Square s idp t u}
                {rt : b == d} {sq3 : Square r' rt t idp}
                {p= : p == s ∙ ! r} (p== : & flat sq1 == p=)
               → adapt-square (p= |∙ vcomp! sq2 (idp |∙ r= |∙ sq3) ∙□ ∙idp |∙ !² hid-square) idp ∙idp == & Toδ∞In.coh r= sq1 sq2 sq3)
    coh1 = path-induction

    coh2 : Coh ({A : Type i} {a b : A} {p : a == b} {c : A} {r : b == c} {s : a == c} {sq : Square p idp r s}
               → adapt-square (idp |∙ sq ∙□ idp |∙ !² sq) idp !-inv-r == hid-square)
    coh2 = path-induction

    coh3 : Coh ({A : Type i} {a b : A} {p : a == b} {c : A} {q : a == c} {s : c == b} {sq1 : Square p q idp s} {d : A} {t : b == d} {u : c == d} {sq2 : Square s idp t u}
                → adapt-square (idp |∙ adapt-square (sq1 ∙□ sq2) ∙idp idp∙ ∙□ idp |∙ !² sq2) ∙idp !-inv-r == sq1)
    coh3 = path-induction

    coh4 : Coh ({A : Type i} {a b c d : A} {p : a == b} {q : a == c} {r : b == d} {s : c == d} {sq : Square p q r s}
                {p' : a == b} {p=□ : Square p' idp idp p} {t : b == b} {t=□ : t == idp} {t' : b == b} {t=' : t' == t}
                {pt' : a == b} {pt=2 : Square pt' idp t' p'} {pt= : pt' == p' ∙ ! t'} (pt== : & flat pt=2 == pt=)
               → adapt-square (pt= |∙ vcomp! (horiz-degen-path p=□ |∙ idp |∙ sq) (t=' |∙ t=□ |∙ vid-square) ∙□ ∙idp |∙ !² sq) !-inv-r !-inv-r
               == & Toδ∞In.coh t=' pt=2 p=□ (horiz-degen-square t=□))
    coh4 = path-induction

natural-square-idp-symm : {A B : Type i} {f : A → B} {x y : A} {p : x == y} → natural-square (λ a → idp {a = f a}) p idp idp == square-symmetry hid-square
natural-square-idp-symm {p = idp} = idp

to-δ∞ : (x : J∞A) → Square (ap to (δ∞ x)) idp (to-α∞ ⋆A x) (δJ (to x))
to-δ∞ = J∞A-elim to-δ∞-in∞ (λ n x → cube-to-↓-path idp (ap-∘ _ _ _) idp (ap-∘ _ _ _)
  (adapt-cube-idp (cube-rotate (to-δ∞-push∞ n x))
                  (& (ap-square-natural-square to) (push∞ n x) δ∞ coh ∙idp)
                  (! natural-square-idp-symm)
                  (! (natural-square-β (to-α∞ ⋆A) (push∞ n x) (push∞-βd n x)))
                  (! (& (natural-square-∘ (push∞ n x) to) δJ coh2 (!-inv-l)))))  where

  coh : {A B : Type i} {f : A → B} {x y : A} {p : x == y} → ap-∘ f (λ z → z) p ∙ ap (ap f) (ap-idf p) == idp
  coh {p = idp} = idp

  coh2 : {A B : Type i} {f : A → B} {x y : A} {p : x == y} → ∘-ap (λ z → z) f p ∙ idp == ap-idf (ap f p)
  coh2 {p = idp} = idp

to-from : (x : JA) → to (from x) == x
to-from = JA-elim to-ε∞
                   (λ a x y → to-α∞ a (from x) ∙ ap (αJ a) y)
                   (λ x y → ↓-='-from-square (ap-∘ to from (δJ x) ∙ ap (ap to) (δJ-β x)) (ap-idf (δJ x))
                     (square-symmetry (adapt-square (to-δ∞ (from x) ∙□ ap-δJ y) idp∙ idp)))

