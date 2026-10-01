{-# OPTIONS --safe --cubical --guardedness #-}

-- T15 (re-encoding of the ontology). If the referents of a model are re-encoded by equivalences that
-- carry the edge relations along, then every route means the same thing before and after, and the
-- soundness of the declared equivalences is preserved. Proved directly, by induction on routes.
open import Metonymy.Graph

module Metonymy.Reencode (G : Graph) (R : Rules G) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Data.Sigma
open import Cubical.Functions.Logic
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁ ; isPropPropTrunc)

open Graph G
open Routes G
open Rules R
open Equiv G R
open import Metonymy.Semantics G R

module _ (M M' : Model)
         (e  : ∀ A → ⟨ Model.Car M A ⟩ ≃ ⟨ Model.Car M' A ⟩)
         (rc : ∀ ed x y → Model.EdgeRel M ed x y
                        ≡ Model.EdgeRel M' ed (equivFun (e (src ed)) x) (equivFun (e (tgt ed)) y))
         where

  private
    module A = Model M
    module B = Model M'

  interp-equivariant : ∀ {X Y} (r : Route X Y) (x : ⟨ A.Car X ⟩) (y : ⟨ A.Car Y ⟩)
                     → interpR M r x y ≡ interpR M' r (equivFun (e X) x) (equivFun (e Y) y)
  interp-equivariant {X} nil x y =
    ⇔toPath (λ p → cong (equivFun (e X)) p) (λ q → invEq (congEquiv (e X)) q)
  interp-equivariant {X} {Y} (cons ed r) x z =
    ⇔toPath fwd bwd
    where
      fwd : ⟨ interpR M (cons ed r) x z ⟩ → ⟨ interpR M' (cons ed r) (equivFun (e X) x) (equivFun (e Y) z) ⟩
      fwd = PT.rec isPropPropTrunc λ { (y , h1 , h2) →
        ∣ equivFun (e (tgt ed)) y
        , subst ⟨_⟩ (rc ed x y) h1
        , subst ⟨_⟩ (interp-equivariant r y z) h2 ∣₁ }

      bwd : ⟨ interpR M' (cons ed r) (equivFun (e X) x) (equivFun (e Y) z) ⟩ → ⟨ interpR M (cons ed r) x z ⟩
      bwd = PT.rec isPropPropTrunc λ { (y' , h1' , h2') →
        let y  = invEq (e (tgt ed)) y'
            s  = secEq (e (tgt ed)) y'
            h1 : ⟨ B.EdgeRel ed (equivFun (e (src ed)) x) (equivFun (e (tgt ed)) y) ⟩
            h1 = subst (λ t → ⟨ B.EdgeRel ed (equivFun (e (src ed)) x) t ⟩) (sym s) h1'
            h2 : ⟨ interpR M' r (equivFun (e (tgt ed)) y) (equivFun (e Y) z) ⟩
            h2 = subst (λ t → ⟨ interpR M' r t (equivFun (e Y) z) ⟩) (sym s) h2'
        in ∣ y , subst ⟨_⟩ (sym (rc ed x y)) h1 , subst ⟨_⟩ (sym (interp-equivariant r y z)) h2 ∣₁ }

  -- Soundness of the declared equivalences is invariant under re-encoding.
  sound-transfer : SoundRules M → SoundRules M'
  sound-transfer sr ρ = funExt λ x' → funExt λ y' →
    let x = invEq (e (rsrc ρ)) x'
        y = invEq (e (rtgt ρ)) y'
        sx = secEq (e (rsrc ρ)) x'
        sy = secEq (e (rtgt ρ)) y'
    in cong₂ (interpR M' (lhs ρ)) (sym sx) (sym sy)
       ∙ sym (interp-equivariant (lhs ρ) x y)
       ∙ cong (λ f → f x y) (sr ρ)
       ∙ interp-equivariant (rhs ρ) x y
       ∙ cong₂ (interpR M' (rhs ρ)) sx sy
