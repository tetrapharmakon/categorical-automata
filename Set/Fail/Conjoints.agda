module Set.Fail.Conjoints where

open import Level
open import Data.Product using (_,_; _×_; proj₁; proj₂; curry)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; cong; trans; sym)
open import Data.List.NonEmpty using (List⁺; _∷_; _∷⁺_; toList; [_])
open import Data.List using (List; []; _∷_)
open import Function using (id; _∘_; flip)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; head; _∷ʳ_; _∷_; foldl; replicate)

open import Set.Automata
open import Set.LimitAutomata
open import Set.Soft
open import Set.Utils
open import Set.Equality
open import Set.Functors
open import Set.DoubleCategory

open import Set.Fail.CoLimits

private
  variable
    I O A B C : Set
    Mre : Moore A B
    Mly : Mealy A B

record Conjoint {A B} (f : A → B) : Set (suc zero) where
  field
    conj : Mealy B A -- the loose arrow
    Λ : Cell f id idMealy conj -- the first cell filling the square
    Ξ : Cell id f conj idMealy -- the second cell filling the square
  module Λ = Cell Λ
  module Ξ = Cell Ξ
  field
    zig : Cell≡ (idH f) (Λ ⊙ᵥ Ξ)
    zag : Cell≡ (unitorᴿ⁻¹ conj ⊙ᵥ ((Ξ ⊙ₕ Λ) ⊙ᵥ unitorᴸ⁻¹ conj)) (idCell conj)

conjoint : (f : A → B) → (a : A) → Conjoint f
conjoint {A} {B} f a = record
  { conj = record
    { E = A × B
    ; d = λ { (b , (a , b')) → a , f a }
    ; s = λ { (b , (a , b')) → a }
    }
  ; Λ = record
    { α = λ { tt → a , f a }
    ; com-s = λ { {x} {tt} → {!  !} }
    ; com-d = refl
    }
  ; Ξ = record
    { α = λ { x → tt }
    ; com-s = λ { {b} {(a , b')} → {!  !} } -- b ≡ f a
    ; com-d = refl
    }
  ; zig = record { eq = refl }
  ; zag = record { eq = {!  !} }
  }
