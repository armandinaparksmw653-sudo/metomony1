{-# OPTIONS --safe --cubical --guardedness #-}

-- T14. Counting in the image of a coercion is counting in a quotient.
-- For c : X -> Y into a set, X modulo "same image" is equivalent to the image of c, and the count
-- "three P" under c coincides with three distinct elements of the image.
module Metonymy.Image where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as E using ()
open import Cubical.HITs.SetQuotients as SQ using (_/_ ; [_] ; eq/ ; squash/ ; elimProp)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁ ; isPropPropTrunc)
open import Cubical.HITs.PropositionalTruncation.Properties using (rec→Set)

open import Metonymy.Counting using (_≢_ ; ThreeUnder)

module _ {X Y : Type} (isSetY : isSet Y) (c : X → Y) where

  -- Two referents are identified when the coercion maps them to the same thing.
  Ker : X → X → Type
  Ker x x' = c x ≡ c x'

  -- The image of the coercion.
  Im : Type
  Im = Σ Y (λ y → ∥ fiber c y ∥₁)

  isSetIm : isSet Im
  isSetIm = isSetΣ isSetY (λ _ → isProp→isSet isPropPropTrunc)

  private
    fun : X / Ker → Im
    fun = SQ.rec isSetIm (λ x → c x , ∣ x , refl ∣₁) (λ x x' p → Σ≡Prop (λ _ → isPropPropTrunc) p)

    constF : ∀ y (a b : fiber c y) → Path (X / Ker) [ fst a ] [ fst b ]
    constF y (x , e) (x' , e') = eq/ x x' (e ∙ sym e')

    inv : Im → X / Ker
    inv (y , p) = rec→Set squash/ (λ a → [ fst a ]) (constF y) p

    sec : ∀ i → fun (inv i) ≡ i
    sec (y , p) = PT.elim {P = λ p → fun (inv (y , p)) ≡ (y , p)}
                    (λ p → isSetIm _ _) (λ { (x , e) → Σ≡Prop (λ _ → isPropPropTrunc) e }) p

    ret : ∀ q → inv (fun q) ≡ q
    ret = elimProp (λ q → squash/ _ _) (λ x → refl)

  -- X modulo equal image is the image.
  quotientImage : (X / Ker) ≃ Im
  quotientImage = isoToEquiv (iso fun inv sec ret)

  -- Three elements of the image, pairwise distinct, each satisfying Q.
  ThreeIm : (Y → Type) → Type
  ThreeIm Q = ∥ Σ Im (λ a → Σ Im (λ b → Σ Im (λ d →
                 Q (fst a) × Q (fst b) × Q (fst d)
               × (fst a ≢ fst b) × (fst a ≢ fst d) × (fst b ≢ fst d)))) ∥₁

  -- "three P" under c, for a predicate that depends on the coerced referent only,
  -- is three distinct elements of the image.
  count⇒image : ∀ (Q : Y → Type) → ThreeUnder c (λ x → Q (c x)) → ThreeIm Q
  count⇒image Q = PT.rec isPropPropTrunc λ { (x , y , z , qx , qy , qz , dxy , dxz , dyz) →
    ∣ (c x , ∣ x , refl ∣₁) , (c y , ∣ y , refl ∣₁) , (c z , ∣ z , refl ∣₁) , qx , qy , qz , dxy , dxz , dyz ∣₁ }

  image⇒count : ∀ (Q : Y → Type) → ThreeIm Q → ThreeUnder c (λ x → Q (c x))
  image⇒count Q = PT.rec isPropPropTrunc λ { ((a , pa) , (b , pb) , (d , pd) , qa , qb , qd , dab , dad , dbd) →
    PT.rec isPropPropTrunc (λ { (x , ex) →
      PT.rec isPropPropTrunc (λ { (y , ey) →
        PT.rec isPropPropTrunc (λ { (z , ez) →
          ∣ x , y , z
          , subst Q (sym ex) qa , subst Q (sym ey) qb , subst Q (sym ez) qd
          , (λ p → dab (sym ex ∙ p ∙ ey)) , (λ p → dad (sym ex ∙ p ∙ ez)) , (λ p → dbd (sym ey ∙ p ∙ ez)) ∣₁ }) pd }) pb }) pa }
