{-# OPTIONS --without-K --rewriting #-}

open import PathInduction
open import Pushout

module JamesFirstComposite {i} (A : Type i) (⋆A : A) where

open import JamesTwoMaps A ⋆A

ap-from-αJ-δJ : (a : A) (x : JA) → ap from (ap (αJ a) (δJ x)) == ap (α∞ a) (δ∞ (from x))
ap-from-αJ-δJ a x = ap-from-αJ a (δJ x) ∙ ap (ap (α∞ a)) (δJ-β x)

ap-from-γ : (a : A) (x : JA) → ap from (γJ a x) == γ∞ a (from x)
ap-from-γ = λ a x → ap-!∙ from (ap (αJ a) (δJ x)) (δJ (αJ a x)) ∙ & coh (ap-from-αJ-δJ a x) (δJ-β (αJ a x))  module ApFromγ where

  coh : Coh ({A : Type i} {a b : A} {p p' : b == a} (p= : p == p') {c : A} {q q' : b == c} (q= : q == q') → ! p ∙ q == ! p' ∙ q')
  coh = path-induction

ap-from-η : (x : JA) → Square (ap (ap from) (ηJ x)) (ap-from-γ ⋆A x) idp (η∞ (from x))
ap-from-η x = & (η-ify-coh from) (ap-δJ (δJ x)) ∙□ & η-coh-homotopy from-δJ-δJ  where

  -- [ap] commutes with [ηIfy.coh]
  -- This lemma would also be true for arbitrary [αJ], [δJ], [α∞] and [δ∞], but for simplicity
  -- we do not abstract over them. We do abstract over [from] because otherwise Agda uses a
  -- crazy amount of memory.
  η-ify-coh : (from : JA → J∞A) → Coh ({a b : JA} {p : a == b} {c : JA} {q r : b == c} (sq : Square p p q r)
              → Square (ap (ap from) (& (ηIfy.coh αJ δJ) sq)) (ap-!∙ from q r) idp (& (ηIfy.coh α∞ δ∞) (ap-square from sq)))
  η-ify-coh = path-induction

  from-δJ-δJ : FlatCube (ap-square from (natural-square δJ (δJ x) (ap-idf (δJ x)) idp))
              (natural-square δ∞ (δ∞ (from x)) (ap-idf (δ∞ (from x))) idp)
              (δJ-β x)
              (δJ-β x)
              (ap-from-αJ-δJ ⋆A x)
              (δJ-β (αJ ⋆A x))
  from-δJ-δJ = adapt-flatcube ∙idp idp∙ idp∙ ∙idp
           (& (ap-square-natural-square from) (δJ x) δJ (& coh) ∙idp
           /∙³ & natural-square-homotopy (δJ-β) (δJ x)
           ∙fc & (natural-square-∘ (δJ x) from) δ∞ (& coh') idp
           /∙³ & natural-square= δ∞ (δJ-β x) (& ap2-idf) (& coh''))  where

    coh : {A B : Type i} {f : A → B} → Coh ({x y : A} {p : x == y} → ap-∘ f (λ z → z) p ∙ ap (ap f) (ap-idf p) == idp)
    coh = path-induction

    coh' : {A B : Type i} {f : A → B} → Coh ({x y : A} {p : x == y} → ∘-ap (λ z → z) f p ∙ idp == ap-idf _)
    coh' = path-induction

    coh'' : Coh ({A : Type i} {a b : A} {p : a == b} {c : A} {q : c == a} {d : A} {r : c == d}
                 → Square p (! q ∙ r) idp ((! r ∙ q) ∙ p))
    coh'' = path-induction

  -- If [sq] and [sq'] are equal (via a FlatCube), then applying [ηIfy.coh] to them give equal terms
  -- (via a Square).
  η-coh-homotopy : Coh ({a b : J∞A} {p : a == b} {c : J∞A} {q : b == c} {r : b == c} {sq : Square p p q r}
              {p' : a == b} {p= : p == p'} {q' : b == c} {q= : q == q'} {r' : b == c} {r= : r == r'}
              {sq' : Square p' p' q' r'} (cube : FlatCube sq sq' p= p= q= r=)
              → Square (& (ηIfy.coh α∞ δ∞) sq) (& ApFromγ.coh q= r=) idp (& (ηIfy.coh α∞ δ∞) sq'))
  η-coh-homotopy = path-induction

comp-square2 : Coh ({A : Type i} {a b : A} {p : a == b} {c : A} {q : b == c} → Square p idp q (p ∙ q))
comp-square2 = path-induction

ap-square-comp-square2 : {A B : Type i} (f : A → B) → Coh ({a b : A} {p : a == b} {c : A} {q : b == c}
                       → FlatCube (ap-square f (& comp-square2 {p = p} {q = q})) (& comp-square2) idp idp idp (ap-∙ f p q))
ap-square-comp-square2 f = path-induction

{- First composite -}

-- As for [inJ], we need both [from-inJ] and [from-inJS] for the termination checker
from-inJ : (n : ℕ) (x : J n) → from (inJ n x) == in∞ n x
from-inJS : (n : ℕ) (x : J (S n)) → from (inJS n x) == in∞ (S n) x


-- Those three describe [from ∘ inJS] applied to [ι], [α] and [β], in the case [S n] as it is
-- the only one we need.

from-inJSS-ι : (n : ℕ) (x : J (S n)) → from (inJS (S n) (ι (S n) x)) == in∞ (S (S n)) (ι (S n) x)
from-inJSS-ι n x = ap (α∞ ⋆A) (from-inJS n x) ∙ ap (in∞ (S (S n))) (β (S n) x)

from-inJSS-α : (n : ℕ) (a : A) (x : J (S n)) → from (inJS (S n) (α (S n) a x)) == in∞ (S (S n)) (α (S n) a x)
from-inJSS-α n a x = ap (α∞ a) (from-inJS n x)

from-inJSS-β : (n : ℕ) (x : J (S n)) → Square (ap from (ap (inJS (S n)) (β (S n) x))) (from-inJSS-α n ⋆A x) (from-inJSS-ι n x) (ap (in∞ (S (S n))) (β (S n) x))
from-inJSS-β n x = ap (ap from) (inJS-βS n x) |∙ comp-square


-- Those three terms describe what happens when we apply [from-inJS] to [ι], [α] or [β].
-- Note that the naming scheme is slightly ambiguous, they do *not* describe [from (inJS (ι _ _))] as above.
-- They are defined later, as we need to know the definition of [from-inJS].

from-inJS-ι : (n : ℕ) (x : J n) → Square (from-inJS n (ι n x)) (ap from (inJS-ι n x)) idp (ap (α∞ ⋆A) (from-inJ n x) ∙ ap (in∞ (S n)) (β n x))
from-inJS-α : (n : ℕ) (a : A) (x : J n) → Square (from-inJS n (α n a x)) (ap from (inJS-α n a x)) idp (ap (α∞ a) (from-inJ n x))
from-inJS-β : (n : ℕ) (x : J n) → Cube (natural-square (from-inJS n) (β n x) (ap-∘ from (inJS n) (β n x)) idp) (& comp-square2) (from-inJS-α n ⋆A x) (ap-square from (inJS-β n x)) hid-square (from-inJS-ι n x)

-- The following three terms show that the two ways of reducing [from ∘ inJS (S n) ∘ (ι (S n) | α (S n) a) ∘ (ι n | α n a)]
-- are equal. For some reason, we don’t need it with α twice

side1 : (n : ℕ) (a : A) (x : J n) → ap (α∞ a) (ap from (inJS-ι n x)) ∙
                                    ap (α∞ a) (ap (α∞ ⋆A) (from-inJ n x)) ∙
                                    ap (in∞ (S (S n))) (ap (α (S n) a) (β n x))
                                    == from-inJSS-α n a (ι n x)
side1 n = λ a x → & coh (ap-∙ _ _ _) (ap-square (α∞ a) (from-inJS-ι n x)) (ap-α∞-in∞ (S n) a (β n x))  module Side1 where

  coh : Coh ({A : Type i} {a c : A} {q : a == c} {d : A} {s1 : c == d} {b : A} {s2 : d == b} {s : c == b} (s= : s == s1 ∙ s2)
             {p : a == b} (sq : Square p q idp s) {s2' : d == b} (s2= : s2 == s2')
            → q ∙ s1 ∙ s2' == p)
  coh = path-induction


side2 : (n : ℕ) (a : A) (x : J n) → ap (α∞ ⋆A) (ap from (inJS-α n a x)) ∙
                                    ap (α∞ ⋆A) (ap (α∞ a) (from-inJ n x)) ∙
                                    ap (in∞ (S (S n))) (β (S n) (α n a x))
                                    == from-inJSS-ι n (α n a x)
side2 n = λ a x → & coh (ap-square (α∞ ⋆A) (from-inJS-α n a x))  module Side2 where

  coh : Coh ({A : Type i} {a b : A} {p : a == b} {c : A} {q : a == c} {s : c == b} (sq : Square p q idp s) {e : A} {t : b == e}
            → q ∙ s ∙ t == p ∙ t)
  coh = path-induction

side3 : (n : ℕ) (x : J n) → ap (α∞ ⋆A) (ap from (inJS-ι n x)) ∙
                            ap (α∞ ⋆A) (ap (α∞ ⋆A) (from-inJ n x)) ∙
                            ap (in∞ (S (S n))) (β (S n) (α n ⋆A x)) ∙
                            ap (in∞ (S (S n))) (ap (ι (S n)) (β n x))
                            == from-inJSS-ι n (ι n x)
side3 n = λ x → & coh (ap-∙ _ _ _) (ap-α∞-in∞ (S n) ⋆A (β n x)) (ap-square (α∞ ⋆A) (from-inJS-ι n x))
                      (ap-square (in∞ (S (S n))) (natural-square (β (S n)) (β n x) idp idp))  module Side3 where

  coh : Coh ({A : Type i} {a c : A} {q : a == c} {d : A} {s : c == d} {b : A} {r : d == b} {rs : c == b} (rs= : rs == s ∙ r)
             {r' : d == b} (r= : r == r') {p : a == b} (sq : Square p q idp rs)
             {e : A} {t : d == e} {f : A} {u : e == f} {v : b == f} (sq2 : Square t r' u v)
            → q ∙ s ∙ t ∙ u == p ∙ v)
  coh = path-induction



piece1 : (n : ℕ) (a : A) (x : J n) → Square (ap from (ap (inJS (S n)) (γ n a x)))
                                            (ap (α∞ a) (ap from (inJS-ι n x)))
                                            (ap (α∞ ⋆A) (ap from (inJS-α n a x)))
                                            (ap from (γJ a (inJ n x)))
piece1 n a x = adapt-square (ap-square from (inJSS-γ n a x)) (ap-from-αJ a (inJS-ι n x)) (ap-from-αJ ⋆A (inJS-α n a x))

from-inJSS-γ : (n : ℕ) (a : A) (x : J n) → Square (ap from (ap (inJS (S n)) (γ n a x))) (from-inJSS-α n a (ι n x)) (from-inJSS-ι n (α n a x)) (ap (in∞ (S (S n))) (γ n a x))
from-inJSS-γ n a x = adapt-square (piece1 n a x
                                  ∙□ ap-from-γ a (inJ n x)
                                  |∙ natural-square (γ∞ a) (from-inJ n x) (ap-∘ (α∞ a) (α∞ ⋆A) (from-inJ n x)) (ap-∘ (α∞ ⋆A) (α∞ a) (from-inJ n x))
                                  ∙□ γ∞-in a n x)
                                  (side1 n a x) (side2 n a x)

adapt-eq : Coh ({A : Type i} {a b : A} {q : a == b} {sq : Square idp q q idp} (sq= : sq == vid-square) {q' : a == b} {p : q == q'} → adapt-square sq p p == vid-square)
adapt-eq = path-induction

natural-square-idp : {A B : Type i} {f : A → B} {x y : A} {p : x == y} {fp : f x == f y} {fp= : ap f p == fp} → natural-square (λ a → idp {a = f a}) p fp= fp= == vid-square
natural-square-idp {p = idp} {fp= = idp} = idp

vid-square∙□vid-square∙□vid-square : Coh ({A : Type i} {a b : A} {p : a == b} {c : A} {q : b == c} {d : A} {r : c == d} → vid-square {p = p} ∙□ vid-square {p = q} ∙□ vid-square {p = r} == vid-square {p = p ∙ q ∙ r})
vid-square∙□vid-square∙□vid-square = path-induction

adapt-square-natural-square : ∀ {i j} {A : Type i} {B : Type j} → Coh ({f g : A → B} {h : (a : A) → f a == g a}
                                {x y : A} {p : x == y} {pf' : f x == f y} {q : ap f p == pf'} {pg' : g x == g y} {r : ap g p == pg'}
                              → adapt-square (natural-square h p idp idp) q r == natural-square h p q r)
adapt-square-natural-square = path-induction

piece1-η : (n : ℕ) (x : J n) → Cube (ap-square from (ap-square (inJS (S n)) (η n x)))
                                    (horiz-degen-square (ap (ap from) (ηJ (inJ n x))))
                                    (piece1 n ⋆A x) vid-square _ _
piece1-η n x = & (ap-shapeInJSη from) {to = ηJ (inJ n x)} (inJSS-η n x) (ap-from-αJ ⋆A (inJS-α n ⋆A x)) (ap-from-αJ ⋆A (inJS-ι n x))


coh-blip : {A B : Type i} {a b : A} (p : a == b)
       → Coh ({f g : A → B} {k : (a : A) → f a == g a} {h : A → B} {l : (a : A) → g a == h a}
              {fp : _} {fp= : ap f p == fp}
              {gp : _} (gp= : ap g p == gp)
              {hp : _} {hp= : ap h p == hp}
             → square-symmetry (natural-square (λ x → k x ∙ l x) p fp= hp=) == square-symmetry (natural-square k p fp= gp=) ∙□ square-symmetry (natural-square l p gp= hp=))
coh-blip {a = a} idp = path-induction

ap-square-hid : {A B : Type i} {f : A → B} {x y : A} {p : x == y} → ap-square f (hid-square {p = p}) == hid-square
ap-square-hid {p = idp} = idp

from-inJSS-η : (n : ℕ) (x : J n) → Cube (ap-square from (ap-square (inJS (S n)) (η n x)))
                                        (ap-square (in∞ (S (S n))) (η n x))
                                        (from-inJSS-γ n ⋆A x)
                                        vid-square
                                        (square-symmetry (natural-square (from-inJSS-ι n) (β n x) (ap-∘ _ _ _ ∙ ap-∘ _ _ _) (ap-∘ _ _ _)))
                                        (from-inJSS-β n (ι n x))
from-inJSS-η n x =
  adapt-cube (piece1-η n x
             ∙³x  ap-from-η (inJ n x)
             -|∙³ natural-cube-η∞ η∞ (from-inJ n x)
             ∙³x  η∞-in n x)
    (side1 n ⋆A x) (side2 n ⋆A x) (side1 n ⋆A x) (side3 n x)
    idp
    (& adapt-eq (& vid-square∙□vid-square∙□vid-square))
    (& coh4 (ap-square-from-αJ ⋆A (inJS-β n x)) (& (ap-square-comp-square2 (α∞ ⋆A))) ap-square-hid (ap-cube (α∞ ⋆A) (from-inJS-β n x))
            eq1
            eq2
      ∙ ! (& (coh-blip (β n x)) (ap-∘ (in∞ (S (S n))) (α (S n) ⋆A) (β n x))))
    (& coh (ap (ap from) (inJS-βS n (ι n x))))  where

  coh : {A : Type i} {a : A} → Coh ({p : a == a} (sq : p == idp) {b : A} {s : a == b}
        {c : A} {q : b == c} {d : A} {u u'' : c == d} {u= : u'' == u} {u' : b == d} {u'= : u' == q ∙ u''}
        {e : A} {t : c == e} {f : A} {v : e == f} {w : d == f} {ββ : Square t u v w} {k : a == d} {X : Square k s idp u'}
      → adapt-square ((sq |∙ vid-square {p = s}) ∙□ idp |∙ vid-square {p = q} ∙□ skew ββ) (& (Side1.coh n) u'= X u=) (& (Side3.coh n) u'= u= X ββ)
        == sq |∙ comp-square)
  coh = path-induction

  eq1 : natural-square (λ a₁ → ap (α∞ ⋆A) (from-inJS n a₁)) (β n x)
           (ap-∘ (from ∘ inJS (S n)) inr (β n x) ∙
            ap-∘ from (inJS (S n)) (ap inr (β n x)))
           (ap-∘ (in∞ (S (S n))) (α (S n) ⋆A) (β n x))
         == adapt-square (ap-square (α∞ ⋆A) (natural-square (from-inJS n) (β n x) (ap-∘ from (inJS n) (β n x)) idp)) (! (ap-from-αJ ⋆A (ap (inJS n) (β n x))) ∙ ! (ap (ap from) (ap-inJSS-ι n (β n x)))) (ap-α∞-in∞ (S n) ⋆A (β n x))
  eq1 = & (natural-square-ap (α∞ ⋆A)) (β n x) (from-inJS n) (coh' (β n x)) (coh'' (β n x))  where

    coh' : {x y : _} (p : x == y)
         → Square (∘-ap (α∞ ⋆A) (λ z → from (inJS n z)) p)
                  (ap (ap (α∞ ⋆A)) (ap-∘ from (inJS n) p))
                  (ap-∘ (from ∘ inJS (S n)) inr p
                    ∙ ap-∘ from (inJS (S n)) (ap inr p))
                  (! (ap-from-αJ ⋆A (ap (inJS n) p))
                    ∙ ! (ap (ap from) (ap-inJSS-ι n p)))
    coh' idp = ids

    coh'' : {x y : _} (p : x == y)
          → Square (∘-ap (α∞ ⋆A) (λ z → in∞ (S n) z) p)
                   idp
                   (ap-∘ (in∞ (S (S n))) (α (S n) ⋆A) p)
                   (ap-α∞-in∞ (S n) ⋆A p)
    coh'' idp = ids


  eq2 : ap-square (in∞ (S (S n))) (natural-square (β (S n)) (β n x) idp idp)
         == natural-square (λ a₁ → ap (in∞ (S (S n))) (β (S n) a₁)) (β n x)
                           (ap-∘ (in∞ (S (S n))) (α (S n) ⋆A) (β n x))
                           (ap-∘ (in∞ (S (S n))) inr (β n x))
  eq2 = & (ap-square-natural-square (in∞ (S (S n)))) (β n x) (β (S n)) ∙idp ∙idp

  coh4 : Coh ({A : Type i} {a b : A} {p : a == b} {c : A} {q q'' : a == c} {q''= : q'' == q} {q' : a == c}
         {q'= : q' == q''} {d : A} {r r' : b == d} {r= : r == r'}
         {s : c == d} {sq1 : Square p q r s} {e : A} {t : b == e} {f : A} {u : e == f} {v : d == f}
         {sqββ : Square t r' u v} {g : A} {k k' : a == g} {k= : k == k'} {l : c == g}
         {sq2 : Square q'' k l idp} {l' : c == g} {l= : l == l'} {u : g == b} {sqα : Square p k' idp u}
         {ur : g == d} {ur= : ur == u ∙ r} {sq3 : Square q k' l' idp}
         (cube-right : FlatCube sq2 sq3 q''= k= l= idp)
         {comp-square2' : _} (comp-square2'= : FlatCube comp-square2' (& comp-square2) idp idp idp ur=)
         {hid' : _} (hid'= : hid' == hid-square)
         {sqι : Square s l' idp ur} (cube-left : Cube sq1 comp-square2' sqα sq3 hid' sqι)
         {sqx : _} (eq1 : sqx == adapt-square sq1 (! q''= ∙ ! q'=) r=)
         {sqy : _} (eq2 : sqββ == sqy)
       → adapt-square (adapt-square (q'= |∙ sq2) k= l= ∙□ vid-square {p = u} ∙□ comp-square) (& (Side2.coh n) sqα) (& (Side3.coh n) ur= r= sqι sqββ)
         == square-symmetry sqx ∙□ square-symmetry sqy)
  coh4 = path-induction

from-inJ O ε = idp
from-inJ (S n) x = from-inJS n x

hdpssvs : Coh ({A : Type i} {x y : A} {p : x == y} → idp == horiz-degen-path (square-symmetry (vid-square {p = p})))
hdpssvs = path-induction


from-inJS O a = idp
from-inJS (S n) =
  JSS-elim n (from-inJSS-ι n)
             (from-inJSS-α n)
             (λ x   → ↓-='-from-square (ap-∘ from (inJS (S n)) (β (S n) x)) idp (square-symmetry (from-inJSS-β n x)))
             (λ a x → ↓-='-from-square (ap-∘ from (inJS (S n)) (γ n a x))   idp (square-symmetry (from-inJSS-γ n a x)))
             (λ x → cube-to-↓-square (from-inJSS-γ n ⋆A x)
                                     (& hdpssvs)
                                     (↓-ap-in-=' (ι (S n)) (from-inJSS-ι n))
                                     (from-inJSS-β n (ι n x))
                                     (ap-square-∘ from (inJS (S n)) (η n x) |∙³ from-inJSS-η n x))


from-inJS-ι O ε = ids
from-inJS-ι (S n) x = hid-square

from-inJS-α O a ε = ids
from-inJS-α (S n) a x = hid-square

from-inJS-β O ε = idc
from-inJS-β (S n) x = & coh (ap-square-horiz-degen-square (inJS-βS n x))
                            (natural-square-β (from-inJS (S n)) (β (S n) x) (push-βd _)) where

  coh : Coh ({A : Type i} {a b : A} {p : a == b} {q : a == a} {k : q == idp}
             {k' : Square q idp idp idp} (k= : k' == horiz-degen-square k)
             {c : A} {r : b == c} {sq : Square p q r (p ∙ r)} → sq == square-symmetry (k |∙ comp-square)
        → Cube sq (& comp-square2) hid-square k' hid-square hid-square)
  coh = path-induction


from-pushJ : (n : ℕ) (x : J n) → Square (ap from (pushJ n x)) (from-inJ n x) (from-inJ (S n) (ι n x)) (push∞ n x)
from-pushJ n x = & coh (δJ-β (inJ n x)) (ap from (inJS-ι n x)) (ap-∙! from _ _)
                       (natural-square δ∞ (from-inJ n x) (ap-idf (from-inJ n x)) idp) (from-inJS-ι n x)  where

  coh : Coh ({A : Type i} {a d : A} {p p' : a == d} (p= : p == p')
             {b : A} (q : b == d) {pq : a == b} (pq= : pq == p ∙ ! q)
             {c : A} {r : a == c} {f : A} {u : c == f} {e : A} {v : e == f}
             {s : d == e} (sq : Square p' r s (u ∙ ! v)) {t : b == f} (sq2 : Square t q idp (s ∙ v))
            → Square pq r t u)
  coh = path-induction

from-to : (x : J∞A) → from (to x) == x
from-to = J∞A-elim from-inJ (λ n x → ↓-='-from-square (ap-∘ from to (push∞ n x) ∙ ap (ap from) (push∞-β n x)) (ap-idf (push∞ n x)) (square-symmetry (from-pushJ n x)))
