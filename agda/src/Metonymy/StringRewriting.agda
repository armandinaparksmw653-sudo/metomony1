{-# OPTIONS --safe --cubical --guardedness -WnoUnsupportedIndexedMatch #-}

-- String rewriting over lists of identifiers. Given oriented rules (left-hand sides and right-hand sides
-- as lists), we prove from the critical-pair conditions that one-step rewriting is locally confluent
-- (the critical pair lemma, via Levi's lemma), that reducibility is decidable, and that rewriting
-- terminates when every rule shortens the string. Together with Metonymy.Rewriting this gives a
-- normal-form function that respects the equivalence.
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-suc ; discreteℕ)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; length ; map)
open import Cubical.Data.List.Properties using (discreteList)
open import Agda.Builtin.Maybe
open import Cubical.Data.List.Properties using (++-assoc ; cons-inj₁ ; cons-inj₂ ; ¬cons≡nil ; ¬nil≡cons)
open import Cubical.Relation.Nullary using (Dec ; yes ; no)
import Cubical.Data.Empty as E
import Metonymy.Rewriting as Rew

module Metonymy.StringRewriting (RuleId : Type) (lhsN rhsN : RuleId → List ℕ) where

------------------------------------------------------------------------------
-- The rewriting relation on strings

infix 4 _⇒s_
_⇒s_ : List ℕ → List ℕ → Type
u ⇒s v = Σ RuleId (λ ρ → Σ (List ℕ) (λ p → Σ (List ℕ) (λ t →
           (u ≡ p ++ (lhsN ρ ++ t)) × (v ≡ p ++ (rhsN ρ ++ t)))))

open Rew {List ℕ} _⇒s_ public

intro : ∀ ρ p t → (p ++ (lhsN ρ ++ t)) ⇒s (p ++ (rhsN ρ ++ t))
intro ρ p t = ρ , p , t , refl , refl

step≡ : ∀ {u u' v v'} → u ≡ u' → v ≡ v' → u' ⇒s v' → u ⇒s v
step≡ e1 e2 (ρ , p , t , a , b) = ρ , p , t , e1 ∙ a , e2 ∙ b

→*≡ˡ : ∀ {u u' w} → u ≡ u' → u' →* w → u →* w
→*≡ˡ e h = subst (λ s → s →* _) (sym e) h

joinable≡ : ∀ {a a' b b'} → a ≡ a' → b ≡ b' → Joinable a' b' → Joinable a b
joinable≡ ea eb (w , h1 , h2) = w , →*≡ˡ ea h1 , →*≡ˡ eb h2

joinable-sym : ∀ {a b} → Joinable a b → Joinable b a
joinable-sym (w , h1 , h2) = w , h2 , h1

------------------------------------------------------------------------------
-- Rewriting inside a context

private
  rearr : ∀ (a p l t b : List ℕ) → a ++ ((p ++ (l ++ t)) ++ b) ≡ (a ++ p) ++ (l ++ (t ++ b))
  rearr a p l t b =
    cong (a ++_) (++-assoc p (l ++ t) b ∙ cong (p ++_) (++-assoc l t b)) ∙ sym (++-assoc a p (l ++ (t ++ b)))

⇒s-ctx : ∀ {u v} → u ⇒s v → ∀ a b → (a ++ (u ++ b)) ⇒s (a ++ (v ++ b))
⇒s-ctx (ρ , p , t , eu , ev) a b =
  ρ , (a ++ p) , (t ++ b)
  , (cong (λ x → a ++ (x ++ b)) eu ∙ rearr a p (lhsN ρ) t b)
  , (cong (λ x → a ++ (x ++ b)) ev ∙ rearr a p (rhsN ρ) t b)

→*-ctx : ∀ {u v} → u →* v → ∀ a b → (a ++ (u ++ b)) →* (a ++ (v ++ b))
→*-ctx ε       a b = ε
→*-ctx (r ▹ h) a b = ⇒s-ctx r a b ▹ →*-ctx h a b

------------------------------------------------------------------------------
-- Levi's lemma

levi : ∀ (x y z w : List ℕ) → x ++ y ≡ z ++ w
     → (Σ (List ℕ) (λ u → (x ≡ z ++ u) × (w ≡ u ++ y))) ⊎ (Σ (List ℕ) (λ u → (z ≡ x ++ u) × (y ≡ u ++ w)))
levi []       y z        w e = inr (z , refl , e)
levi (a ∷ x') y []       w e = inl (a ∷ x' , refl , sym e)
levi (a ∷ x') y (b ∷ z') w e with levi x' y z' w (cons-inj₂ e)
... | inl (u , xe , we) = inl (u , cong₂ _∷_ (cons-inj₁ e) xe , we)
... | inr (u , ze , ye) = inr (u , cong₂ _∷_ (sym (cons-inj₁ e)) ze , ye)

------------------------------------------------------------------------------
-- Local confluence from the critical pairs

module Confluence
  -- proper overlap: a suffix of one left-hand side is a prefix of the other
  (CP₁ : ∀ ρa ρb u v x → lhsN ρb ≡ u ++ v → lhsN ρa ≡ v ++ x → Joinable (u ++ rhsN ρa) (rhsN ρb ++ x))
  -- inclusion: one left-hand side occurs inside the other
  (CP₂ : ∀ ρa ρb u y → lhsN ρb ≡ u ++ (lhsN ρa ++ y) → Joinable (u ++ (rhsN ρa ++ y)) (rhsN ρb))
  where

  -- Redex b's left-hand side reaches into redex a: a proper overlap or an inclusion.
  coreA : ∀ ρa pa ta ρb pb tb u v
        → pa ≡ pb ++ u → lhsN ρb ≡ u ++ v → lhsN ρa ++ ta ≡ v ++ tb
        → Joinable (pa ++ (rhsN ρa ++ ta)) (pb ++ (rhsN ρb ++ tb))
  coreA ρa pa ta ρb pb tb u v pe lbe eqv with levi (lhsN ρa) ta v tb eqv
  coreA ρa pa ta ρb pb tb u v pe lbe eqv | inl (x , lae , tbe) with CP₁ ρa ρb u v x lbe lae
  coreA ρa pa ta ρb pb tb u v pe lbe eqv | inl (x , lae , tbe) | w0 , h1 , h2 =
    let Ea : pa ++ (rhsN ρa ++ ta) ≡ pb ++ ((u ++ rhsN ρa) ++ ta)
        Ea = cong (λ q → q ++ (rhsN ρa ++ ta)) pe ∙ ++-assoc pb u (rhsN ρa ++ ta)
             ∙ cong (pb ++_) (sym (++-assoc u (rhsN ρa) ta))
        Eb : pb ++ (rhsN ρb ++ tb) ≡ pb ++ ((rhsN ρb ++ x) ++ ta)
        Eb = cong (λ q → pb ++ (rhsN ρb ++ q)) tbe ∙ cong (pb ++_) (sym (++-assoc (rhsN ρb) x ta))
    in pb ++ (w0 ++ ta) , →*≡ˡ Ea (→*-ctx h1 pb ta) , →*≡ˡ Eb (→*-ctx h2 pb ta)
  coreA ρa pa ta ρb pb tb u v pe lbe eqv | inr (y , vle , tae) with CP₂ ρa ρb u y (lbe ∙ cong (u ++_) vle)
  coreA ρa pa ta ρb pb tb u v pe lbe eqv | inr (y , vle , tae) | w0 , h1 , h2 =
    let Ea : pa ++ (rhsN ρa ++ ta) ≡ pb ++ ((u ++ (rhsN ρa ++ y)) ++ tb)
        Ea = cong (λ q → q ++ (rhsN ρa ++ ta)) pe ∙ ++-assoc pb u (rhsN ρa ++ ta)
             ∙ cong (λ q → pb ++ (u ++ (rhsN ρa ++ q))) tae
             ∙ cong (pb ++_) (cong (u ++_) (sym (++-assoc (rhsN ρa) y tb)) ∙ sym (++-assoc u (rhsN ρa ++ y) tb))
    in pb ++ (w0 ++ tb) , →*≡ˡ Ea (→*-ctx h1 pb tb) , →*-ctx h2 pb tb

  -- The case where redex a starts at or after the start of redex b.
  core : ∀ ρa pa ta ρb pb tb u
       → pa ≡ pb ++ u → lhsN ρb ++ tb ≡ u ++ (lhsN ρa ++ ta)
       → Joinable (pa ++ (rhsN ρa ++ ta)) (pb ++ (rhsN ρb ++ tb))
  core ρa pa ta ρb pb tb u pe le with levi (lhsN ρb) tb u (lhsN ρa ++ ta) le
  -- redex b ends before redex a starts: they commute
  core ρa pa ta ρb pb tb u pe le | inr (v , ue , tbe) =
    let X  = rhsN ρa ++ ta
        w  = pb ++ (rhsN ρb ++ (v ++ X))
        E1 : pa ++ X ≡ pb ++ (lhsN ρb ++ (v ++ X))
        E1 = cong (λ q → q ++ X) pe ∙ cong (λ q → (pb ++ q) ++ X) ue
             ∙ ++-assoc pb (lhsN ρb ++ v) X ∙ cong (pb ++_) (++-assoc (lhsN ρb) v X)
        E2 : pb ++ (rhsN ρb ++ tb) ≡ (pb ++ (rhsN ρb ++ v)) ++ (lhsN ρa ++ ta)
        E2 = cong (λ q → pb ++ (rhsN ρb ++ q)) tbe ∙ cong (pb ++_) (sym (++-assoc (rhsN ρb) v (lhsN ρa ++ ta)))
             ∙ sym (++-assoc pb (rhsN ρb ++ v) (lhsN ρa ++ ta))
        E3 : w ≡ (pb ++ (rhsN ρb ++ v)) ++ X
        E3 = cong (pb ++_) (sym (++-assoc (rhsN ρb) v X)) ∙ sym (++-assoc pb (rhsN ρb ++ v) X)
    in w , (step≡ E1 refl (intro ρb pb (v ++ X)) ▹ ε)
         , (step≡ E2 E3 (intro ρa (pb ++ (rhsN ρb ++ v)) ta) ▹ ε)
  core ρa pa ta ρb pb tb u pe le | inl (v , lbe , eqv) = coreA ρa pa ta ρb pb tb u v pe lbe eqv

  -- Local confluence of one-step rewriting.
  LCs : ∀ {r s1 s2} → r ⇒s s1 → r ⇒s s2 → Joinable s1 s2
  LCs (ρ1 , p1 , t1 , er1 , es1) (ρ2 , p2 , t2 , er2 , es2)
    with levi p1 (lhsN ρ1 ++ t1) p2 (lhsN ρ2 ++ t2) (sym er1 ∙ er2)
  ... | inl (u , pe , le) = joinable≡ es1 es2 (core ρ1 p1 t1 ρ2 p2 t2 u pe le)
  ... | inr (u , pe , le) = joinable≡ es1 es2 (joinable-sym (core ρ2 p2 t2 ρ1 p1 t1 u pe le))

------------------------------------------------------------------------------
-- Termination from a shrinking measure

private
  len-++ : ∀ (a b : List ℕ) → length (a ++ b) ≡ length a + length b
  len-++ []       b = refl
  len-++ (x ∷ a) b = cong suc (len-++ a b)

Shrinks : Type
Shrinks = ∀ ρ → length (rhsN ρ) < length (lhsN ρ)

step-shrinks : Shrinks → ∀ {u v} → u ⇒s v → length v < length u
step-shrinks sh {u} {v} (ρ , p , t , eu , ev) =
  subst2 (λ a b → suc a ≤ b) (sym (cong length ev ∙ eR)) (sym (cong length eu ∙ eL)) base
  where
    eR : length (p ++ (rhsN ρ ++ t)) ≡ length p + (length (rhsN ρ) + length t)
    eR = len-++ p (rhsN ρ ++ t) ∙ cong (length p +_) (len-++ (rhsN ρ) t)
    eL : length (p ++ (lhsN ρ ++ t)) ≡ length p + (length (lhsN ρ) + length t)
    eL = len-++ p (lhsN ρ ++ t) ∙ cong (length p +_) (len-++ (lhsN ρ) t)
    base : suc (length p + (length (rhsN ρ) + length t)) ≤ length p + (length (lhsN ρ) + length t)
    base = subst (_≤ length p + (length (lhsN ρ) + length t)) (+-suc (length p) (length (rhsN ρ) + length t))
             (≤-k+ {k = length p} (≤-+k {k = length t} (sh ρ)))

snLen : Shrinks → ∀ (n : ℕ) (u : List ℕ) → length u ≤ n → SN u
snLen sh zero    u h = sn (λ v st → E.rec (¬-<-zero (≤-trans (step-shrinks sh st) h)))
snLen sh (suc n) u h = sn (λ v st → snLen sh n v (pred-≤-pred (≤-trans (step-shrinks sh st) h)))

terminatesS : Shrinks → ∀ u → SN u
terminatesS sh u = snLen sh (length u) u ≤-refl

------------------------------------------------------------------------------
-- Decidable reducibility

-- Does the list l begin the list u?
prefix? : (l u : List ℕ) → Dec (Σ (List ℕ) (λ t → u ≡ l ++ t))
prefix? []       u        = yes (u , refl)
prefix? (a ∷ l') []       = no (λ { (t , e) → ¬nil≡cons e })
prefix? (a ∷ l') (b ∷ u') with discreteℕ a b
... | no  a≢b = no (λ { (t , e) → a≢b (sym (cons-inj₁ e)) })
... | yes ab with prefix? l' u'
...   | yes (t , e) = yes (t , cong₂ _∷_ (sym ab) e)
...   | no  ¬p      = no (λ { (t , e) → ¬p (t , cons-inj₂ e) })

-- Does l occur inside u?
factor? : (l u : List ℕ) → Dec (Σ (List ℕ) (λ p → Σ (List ℕ) (λ t → u ≡ p ++ (l ++ t))))
factor? l u with prefix? l u
... | yes (t , e) = yes ([] , t , e)
factor? l []       | no ¬p = no (λ { ([] , t , e) → ¬p (t , e) ; (x ∷ p , t , e) → ¬nil≡cons e })
factor? l (b ∷ u') | no ¬p with factor? l u'
...   | yes (p , t , e) = yes (b ∷ p , t , cong (b ∷_) e)
...   | no  ¬f = no (λ { ([] , t , e) → ¬p (t , e) ; (x ∷ p , t , e) → ¬f (p , t , cons-inj₂ e) })

-- Membership in a finite list of rules.
data Mem {X : Type} (x : X) : List X → Type where
  here  : ∀ {xs} → Mem x (x ∷ xs)
  there : ∀ {y xs} → Mem x xs → Mem x (y ∷ xs)

module Search (rules : List RuleId) (rules-complete : ∀ ρ → Mem ρ rules) where

  -- Is there a redex for one of the given rules?
  search : (rs : List RuleId) (u : List ℕ)
         → Dec (Σ RuleId (λ ρ → Mem ρ rs × Σ (List ℕ) (λ p → Σ (List ℕ) (λ t → u ≡ p ++ (lhsN ρ ++ t)))))
  search []        u = no (λ { (ρ , () , _) })
  search (σ ∷ rs)  u with factor? (lhsN σ) u
  ... | yes (p , t , e) = yes (σ , here , p , t , e)
  ... | no  ¬f with search rs u
  ...   | yes (ρ , m , d) = yes (ρ , there m , d)
  ...   | no  ¬s = no (λ { (ρ , here , p , t , e) → ¬f (p , t , e)
                         ; (ρ , there m , d) → ¬s (ρ , m , d) })

  -- Reducibility of a string is decidable.
  step? : ∀ u → Dec (Σ (List ℕ) (λ v → u ⇒s v))
  step? u with search rules u
  ... | yes (ρ , _ , p , t , e) = yes (p ++ (rhsN ρ ++ t) , ρ , p , t , e , refl)
  ... | no  ¬s = no (λ { (v , ρ , p , t , e , _) → ¬s (ρ , rules-complete ρ , p , t , e) })

  -- The normal-form function for strings.
  module Norm (sh : Shrinks)
              (CP₁ : ∀ ρa ρb u v x → lhsN ρb ≡ u ++ v → lhsN ρa ≡ v ++ x → Joinable (u ++ rhsN ρa) (rhsN ρb ++ x))
              (CP₂ : ∀ ρa ρb u y → lhsN ρb ≡ u ++ (lhsN ρa ++ y) → Joinable (u ++ (rhsN ρa ++ y)) (rhsN ρb))
              where

    open Confluence CP₁ CP₂ using (LCs)
    module N = Normalize step?

    normS : List ℕ → List ℕ
    normS = N.norm LCs (terminatesS sh)

    normS-reduces : ∀ u → u →* normS u
    normS-reduces = N.norm-reduces LCs (terminatesS sh)

    normS-isNF : ∀ u → IsNF (normS u)
    normS-isNF = N.norm-isNF LCs (terminatesS sh)

    normS-resp : ∀ {u v} → u ↔* v → normS u ≡ normS v
    normS-resp = N.norm-resp LCs (terminatesS sh)

    -- Strings with a common reduct have the same normal form.
    normS-joinable : ∀ {u v} → Joinable u v → normS u ≡ normS v
    normS-joinable (w , h1 , h2) = normS-resp (↔-trans (→*⇒↔* h1) (↔-sym (→*⇒↔* h2)))

------------------------------------------------------------------------------
-- A computational check of the critical-pair conditions
--
-- All splittings of the left-hand sides are enumerated and every resulting critical pair is joined by
-- greedy reduction (leftmost reducible step, with fuel). A successful run is evidence of joinability, so
-- soundness needs no confluence argument.

private
  cancelˡ : ∀ (a b c : List ℕ) → a ++ b ≡ a ++ c → b ≡ c
  cancelˡ []       b c h = h
  cancelˡ (x ∷ a) b c h = cancelˡ a b c (cons-inj₂ h)

-- All ways of writing a list as a concatenation.
splits : List ℕ → List (List ℕ × List ℕ)
splits []       = ([] , []) ∷ []
splits (a ∷ xs) = ([] , a ∷ xs) ∷ map (λ { (u , v) → (a ∷ u , v) }) (splits xs)

-- Every splitting is enumerated.
splits-complete : ∀ (xs u v : List ℕ) → xs ≡ u ++ v → Mem (u , v) (splits xs)
splits-complete xs [] v e = subst (λ w → Mem ([] , v) (splits w)) (sym e) (here0 v)
  where
    here0 : ∀ w → Mem ([] , w) (splits w)
    here0 []       = here
    here0 (a ∷ w') = here
splits-complete []       (a ∷ u) v e = E.rec (¬nil≡cons e)
splits-complete (b ∷ xs) (a ∷ u) v e =
  subst (λ c → Mem (a ∷ u , v) (splits (c ∷ xs))) (sym (cons-inj₁ e))
    (there (mapMem (splits-complete xs u v (cons-inj₂ e))))
  where
    mapMem : ∀ {ys : List (List ℕ × List ℕ)} {p} → Mem p ys
           → Mem (a ∷ fst p , snd p) (map (λ { (u' , v') → (a ∷ u' , v') }) ys)
    mapMem here      = here
    mapMem (there m) = there (mapMem m)

-- A universal statement over a finite list, checked member by member.
forallM : ∀ {X : Type} (xs : List X) (P : X → Type) → (∀ x → Maybe (P x)) → Maybe (∀ x → Mem x xs → P x)
forallM []       P f = just (λ _ ())
forallM (y ∷ ys) P f with f y | forallM ys P f
... | just py | just rest = just (λ { _ here → py ; _ (there m) → rest _ m })
... | _       | _         = nothing

-- The critical-pair conditions.
CP1 CP2 : Type
CP1 = ∀ ρa ρb u v x → lhsN ρb ≡ u ++ v → lhsN ρa ≡ v ++ x → Joinable (u ++ rhsN ρa) (rhsN ρb ++ x)
CP2 = ∀ ρa ρb u y → lhsN ρb ≡ u ++ (lhsN ρa ++ y) → Joinable (u ++ (rhsN ρa ++ y)) (rhsN ρb)

module Checker (rules : List RuleId) (rules-complete : ∀ ρ → Mem ρ rules) (fuel : ℕ) where
  open Search rules rules-complete

  -- Greedy reduction with fuel: a chain of steps to some string.
  greedy : ℕ → (u : List ℕ) → Σ (List ℕ) (λ w → u →* w)
  greedy zero    u = u , ε
  greedy (suc n) u with step? u
  ... | no  _ = u , ε
  ... | yes (v , r) with greedy n v
  ...   | w , c = w , (r ▹ c)

  -- Evidence that two strings are joinable, if greedy reduction finds it.
  joinableG : ℕ → (a b : List ℕ) → Maybe (Joinable a b)
  joinableG n a b with greedy n a | greedy n b
  ... | wa , ca | wb , cb with discreteList discreteℕ wa wb
  ...   | yes e = just (wa , ca , subst (λ w → b →* w) (sym e) cb)
  ...   | no  _ = nothing

  -- Overlaps: a suffix of one left-hand side is a prefix of the other.
  Pair1 : RuleId → RuleId → List ℕ × List ℕ → List ℕ × List ℕ → Type
  Pair1 ρa ρb (u , v) (v' , x) = v ≡ v' → Joinable (u ++ rhsN ρa) (rhsN ρb ++ x)

  chk1 : ∀ ρa ρb uv vx → Maybe (Pair1 ρa ρb uv vx)
  chk1 ρa ρb (u , v) (v' , x) with discreteList discreteℕ v v'
  ... | no ne = just (λ e → E.rec (ne e))
  ... | yes _ with joinableG fuel (u ++ rhsN ρa) (rhsN ρb ++ x)
  ...   | just j  = just (λ _ → j)
  ...   | nothing = nothing

  All1 : Type
  All1 = ∀ ρa → Mem ρa rules → ∀ ρb → Mem ρb rules → ∀ uv → Mem uv (splits (lhsN ρb))
       → ∀ vx → Mem vx (splits (lhsN ρa)) → Pair1 ρa ρb uv vx

  check1 : Maybe All1
  check1 = forallM rules
    (λ ρa → ∀ ρb → Mem ρb rules → ∀ uv → Mem uv (splits (lhsN ρb)) → ∀ vx → Mem vx (splits (lhsN ρa)) → Pair1 ρa ρb uv vx)
    (λ ρa → forallM rules
      (λ ρb → ∀ uv → Mem uv (splits (lhsN ρb)) → ∀ vx → Mem vx (splits (lhsN ρa)) → Pair1 ρa ρb uv vx)
      (λ ρb → forallM (splits (lhsN ρb))
        (λ uv → ∀ vx → Mem vx (splits (lhsN ρa)) → Pair1 ρa ρb uv vx)
        (λ uv → forallM (splits (lhsN ρa)) (λ vx → Pair1 ρa ρb uv vx) (λ vx → chk1 ρa ρb uv vx))))

  cp1-from : All1 → CP1
  cp1-from all ρa ρb u v x eb ea =
    all ρa (rules-complete ρa) ρb (rules-complete ρb) (u , v) (splits-complete (lhsN ρb) u v eb)
        (v , x) (splits-complete (lhsN ρa) v x ea) refl

  -- Inclusions: one left-hand side occurs inside the other.
  Pair2 : RuleId → RuleId → List ℕ × List ℕ → Type
  Pair2 ρa ρb (u , rest) = ∀ y → rest ≡ lhsN ρa ++ y → Joinable (u ++ (rhsN ρa ++ y)) (rhsN ρb)

  chk2 : ∀ ρa ρb ur → Maybe (Pair2 ρa ρb ur)
  chk2 ρa ρb (u , rest) with prefix? (lhsN ρa) rest
  ... | no ¬p = just (λ y e → E.rec (¬p (y , e)))
  ... | yes (y0 , e0) with joinableG fuel (u ++ (rhsN ρa ++ y0)) (rhsN ρb)
  ...   | just j  = just (λ y e → subst (λ z → Joinable (u ++ (rhsN ρa ++ z)) (rhsN ρb))
                                      (cancelˡ (lhsN ρa) y0 y (sym e0 ∙ e)) j)
  ...   | nothing = nothing

  All2 : Type
  All2 = ∀ ρa → Mem ρa rules → ∀ ρb → Mem ρb rules → ∀ ur → Mem ur (splits (lhsN ρb)) → Pair2 ρa ρb ur

  check2 : Maybe All2
  check2 = forallM rules
    (λ ρa → ∀ ρb → Mem ρb rules → ∀ ur → Mem ur (splits (lhsN ρb)) → Pair2 ρa ρb ur)
    (λ ρa → forallM rules
      (λ ρb → ∀ ur → Mem ur (splits (lhsN ρb)) → Pair2 ρa ρb ur)
      (λ ρb → forallM (splits (lhsN ρb)) (λ ur → Pair2 ρa ρb ur) (λ ur → chk2 ρa ρb ur)))

  cp2-from : All2 → CP2
  cp2-from all ρa ρb u y eb =
    all ρa (rules-complete ρa) ρb (rules-complete ρb) (u , lhsN ρa ++ y) (splits-complete (lhsN ρb) u (lhsN ρa ++ y) eb) y refl

  -- If the check succeeds, both critical-pair conditions hold.
  cpDecide : Maybe (CP1 × CP2)
  cpDecide with check1 | check2
  ... | just a1 | just a2 = just (cp1-from a1 , cp2-from a2)
  ... | _       | _       = nothing
