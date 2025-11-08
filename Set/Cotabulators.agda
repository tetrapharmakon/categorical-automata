{-# OPTIONS --cubical #-}

module Set.Cotabulators where

open import Set.Automata
open import Set.LimitAutomata
open import Set.Functors
open import Set.DoubleCategory
open import Level
open import Function

open import Data.Empty
open import Data.Product
open import Data.Sum hiding (map)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality

-- Uses quotients from cubical
open import Cubical.HITs.TypeQuotients
open import Cubical.Data.Equality.Conversion

private
  variable
    X Y Z U V A B C A' B' A'' B'' : Set
    lv rv lv' rv' : A → B

record Cotabulator {X Y} (M : Mealy X Y) : Set (suc zero) where
  private
    module M = Mealy M
  field
    cotab : Set
    p   : X → cotab
    q   : Y → cotab
    τ   : Cell p q M idMealy
    --
    universal : ∀ {U} {f : X → U} {g : Y → U} (ξ : Cell f g M idMealy) →
      (cotab → U)
    fst-commute₁ : ∀ {U} {f : X → U} {g : Y → U} (ξ : Cell f g M idMealy) →
      (universal ξ) ∘ p ≡ f
    snd-commute₁ : ∀ {U} {f : X → U} {g : Y → U} (ξ : Cell f g M idMealy) →
      (universal ξ) ∘ q ≡ g
    commute₂ : ∀ {U} {f : X → U} {g : Y → U} (ξ : Cell f g M idMealy) →
      Cell≡ ξ (subst₂ (λ Q R → Cell Q R M idMealy) (fst-commute₁ ξ) (snd-commute₁ ξ) (τ ⊙ᵥ idH (universal ξ)))

cotabs : (M : Mealy X Y) → Cotabulator M
cotabs {X = X} {Y = Y} M = let module M = Mealy M in record
  { cotab = (X ⊎ Y) /ₜ λ { (inj₁ x) (inj₁ x₁) → ⊥
                        ; (inj₁ x) (inj₂ y) → ∃[ e ] y ≡ M.s (x , e)
                        ; (inj₂ y) (inj₁ x) → ⊥
                        ; (inj₂ y) (inj₂ y₁) → ⊥ }
  ; p = λ x → [ inj₁ x ]
  ; q = λ x → [ inj₂ x ]
  ; τ = record
    { α = λ _ → tt
    ; com-s = λ { {x} {e} → pathToEq (eq/ (inj₁ x) (inj₂ (M.s (x , e))) (e , refl)) }
    ; com-d = refl
    }
  ; universal = λ { {f = f} ξ [ inj₁ x ] → f x
                  ; {g = g} ξ [ inj₂ y ] → g y
                  ; {f = f} {g = g} ξ (eq/ (inj₁ x) (inj₂ y) (fst , refl) i) → eqToPath (Cell.com-s ξ {x = x} {y = fst}) i
                  ; {f = f} {g = g} ξ (eq/ (inj₂ y) (inj₁ x) () i)
                  ; {f = f} {g = g} ξ (eq/ (inj₂ y) (inj₂ y₁) () i) }
  ; fst-commute₁ = λ _ → refl
  ; snd-commute₁ = λ _ → refl
  ; commute₂ = λ ξ → record { eq = refl }
  }
