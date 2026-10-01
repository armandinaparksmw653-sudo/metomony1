{-# OPTIONS --safe --cubical --guardedness #-}

-- Abstract rewriting. For a terminating, locally confluent relation with a decidable reducibility test
-- we prove Newman's lemma, the Church-Rosser property of the equivalence closure, uniqueness of normal
-- forms, and that the normal-form function respects the equivalence. This is the standard route from
-- "terminating and locally confluent" to "decidable word problem".
open import Cubical.Foundations.Prelude

module Metonymy.Rewriting {X : Type} (_→ᵣ_ : X → X → Type) where

open import Cubical.Data.Sigma
import Cubical.Data.Empty as E
open import Cubical.Relation.Nullary using (Dec ; yes ; no)

infix 4 _→*_ _↔*_

-- Reflexive-transitive closure.
data _→*_ : X → X → Type where
  ε   : ∀ {x} → x →* x
  _▹_ : ∀ {x y z} → x →ᵣ y → y →* z → x →* z

infixr 5 _▹_ _++*_

_++*_ : ∀ {x y z} → x →* y → y →* z → x →* z
ε       ++* q = q
(r ▹ p) ++* q = r ▹ (p ++* q)

-- Equivalence closure.
data _↔*_ : X → X → Type where
  ↔-refl  : ∀ {x} → x ↔* x
  ↔-sym   : ∀ {x y} → x ↔* y → y ↔* x
  ↔-trans : ∀ {x y z} → x ↔* y → y ↔* z → x ↔* z
  ↔-step  : ∀ {x y} → x →ᵣ y → x ↔* y

→*⇒↔* : ∀ {x y} → x →* y → x ↔* y
→*⇒↔* ε       = ↔-refl
→*⇒↔* (r ▹ p) = ↔-trans (↔-step r) (→*⇒↔* p)

-- Strong normalization (accessibility).
data SN (x : X) : Type where
  sn : (∀ y → x →ᵣ y → SN y) → SN x

IsNF : X → Type
IsNF x = ∀ y → x →ᵣ y → E.⊥

Joinable : X → X → Type
Joinable x y = Σ X (λ w → (x →* w) × (y →* w))

-- A normal form reaches nothing but itself.
nf-stuck : ∀ {n w} → IsNF n → n →* w → n ≡ w
nf-stuck nf ε       = refl
nf-stuck nf (r ▹ _) = E.rec (nf _ r)

module _ (LC : ∀ {x y z} → x →ᵣ y → x →ᵣ z → Joinable y z) where

  -- Newman's lemma: local confluence and termination give confluence.
  newman : ∀ {x} → SN x → ∀ {y z} → x →* y → x →* z → Joinable y z
  newman (sn f) {y} {z} ε q = z , q , ε
  newman (sn f) {y} {z} (r1 ▹ p') ε = y , ε , (r1 ▹ p')
  newman (sn f) {y} {z} (_▹_ {y = y1} r1 p') (_▹_ {y = z1} r2 q') with LC r1 r2
  ... | w1 , a , b with newman (f y1 r1) p' a
  ...   | u , pu , w1u with newman (f z1 r2) (b ++* w1u) q'
  ...     | v , uv , zv = v , (pu ++* uv) , zv

  -- Church-Rosser: equivalent elements have a common reduct.
  church-rosser : (∀ x → SN x) → ∀ {x y} → x ↔* y → Joinable x y
  church-rosser sns ↔-refl      = _ , ε , ε
  church-rosser sns (↔-sym h)   with church-rosser sns h
  ... | w , a , b = w , b , a
  church-rosser sns (↔-step r)  = _ , (r ▹ ε) , ε
  church-rosser sns (↔-trans {y = y} h k) with church-rosser sns h | church-rosser sns k
  ... | w1 , x1 , y1 | w2 , y2 , z2 with newman (sns y) y1 y2
  ...   | u , w1u , w2u = u , (x1 ++* w1u) , (z2 ++* w2u)

  -- Normal forms are unique.
  nf-unique : (∀ x → SN x) → ∀ {x n1 n2} → IsNF n1 → IsNF n2 → x →* n1 → x →* n2 → n1 ≡ n2
  nf-unique sns nf1 nf2 p q with newman (sns _) p q
  ... | w , a , b = nf-stuck nf1 a ∙ sym (nf-stuck nf2 b)

-- Normalization, given a decision procedure for reducibility.
module Normalize (step? : ∀ x → Dec (Σ X (λ y → x →ᵣ y))) where

  nfSN : ∀ {x} → SN x → Σ X (λ n → (x →* n) × IsNF n)
  nfSN {x} (sn f) with step? x
  ... | no ¬e = x , ε , (λ y r → ¬e (y , r))
  ... | yes (y , r) with nfSN (f y r)
  ...   | n , red , isnf = n , (r ▹ red) , isnf

  module _ (LC : ∀ {x y z} → x →ᵣ y → x →ᵣ z → Joinable y z) (sns : ∀ x → SN x) where

    norm : X → X
    norm x = fst (nfSN (sns x))

    norm-reduces : ∀ x → x →* norm x
    norm-reduces x = fst (snd (nfSN (sns x)))

    norm-isNF : ∀ x → IsNF (norm x)
    norm-isNF x = snd (snd (nfSN (sns x)))

    -- Equivalent elements have the same normal form.
    norm-resp : ∀ {x y} → x ↔* y → norm x ≡ norm y
    norm-resp {x} {y} h with church-rosser LC sns h
    ... | w , xw , yw with newman LC (sns x) (norm-reduces x) xw
    ...   | u , nu , wu =
      let nx≡u = nf-stuck (norm-isNF x) nu
          wnx  = subst (λ t → w →* t) (sym nx≡u) wu
      in nf-unique LC sns (norm-isNF x) (norm-isNF y) (yw ++* wnx) (norm-reduces y)
