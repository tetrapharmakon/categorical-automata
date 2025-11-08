{-# OPTIONS --allow-unsolved-metas #-}
module Set.Fail.Comma where

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

open import Set.Equality

private
  variable
    X Y Z U V A B C A' B' A'' B'' : Set
    lv rv lv' rv' : A → B

record DoubleComma (f : A → X) (M : Mealy B X) : Set (suc zero) where
  field
    comma : Set
    P : Mealy comma A
    q : comma → B -- two projections
    φ : Cell q f P M
    --
    h-universal₁ : ∀ {h : U → A} {g : U → B} (ξ : Cell g (f ∘ h) idMealy M) → (U → comma)
    h-commute₀ : ∀ {h : U → A} {g : U → B} (ξ : Cell g (f ∘ h) idMealy M) → q ∘ (h-universal₁ ξ) ≡ g
    h-universal₂ : ∀ {h : U → A} {g : U → B} (ξ : Cell g (f ∘ h) idMealy M) → Cell (h-universal₁ ξ) h idMealy P
    h-commute : ∀ {h : U → A} {g : U → B} (ξ : Cell g (f ∘ h) idMealy M) → Cell≡ ξ (subst (λ t → Cell t (f ∘ h) idMealy M) (h-commute₀ ξ) (h-universal₂ ξ ⊙ᵥ φ))

candidateDblComma : (f : A → X) (M : Mealy B X) (C : Set) → DoubleComma f M
candidateDblComma f M C = record
 { comma = C
 ; P = record
   { E = {! !}
   ; d = {! !}
   ; s = {! !}
   }
 ; q = {! !}
 ; φ = {! !}
 ; h-universal₁ = {! !}
 ; h-commute₀ = {! !}
 ; h-universal₂ = {! !}
 ; h-commute = {! !}
 }
