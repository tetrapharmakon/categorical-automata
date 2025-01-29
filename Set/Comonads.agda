
{-# OPTIONS --allow-unsolved-metas #-}
module Set.Comonads where

open import Set.Automata
open import Set.LimitAutomata
open import Set.Functors
open import Set.DoubleCategory
open import Set.CrossedModules
open import Level
open import Function

open import Data.Empty
open import Data.Product
open import Data.List
open import Data.List.NonEmpty
open import Data.Sum hiding (map)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

private
  variable
    X Y Z A B C A' B' A'' B'' S : Set
    lv rv lv' rv' : A → B


{-
* ------- M ------- *
|                   |
|         σ         |
|                   |
* ---M--- * ---M--- *
|         |         |
|         |         |
|         |         |
* ------- * ------- *
-}

record DoubleComonad A : Set (suc zero) where
  field
    M : Mealy A A
    ε : Cell id id M idMealy
    σ : Cell id id M (M ⋄ M)
    counitᴸ : Cell≡ (σ ⊙ᵥ ((idCell M ⊙ₕ ε) ⊙ᵥ unitorᴿ M)) (idCell M)
    counitᴿ : Cell≡ (σ ⊙ᵥ ((ε ⊙ₕ idCell M) ⊙ᵥ unitorᴸ⁻¹ M)) (idCell M)
    σ-coassoc : Cell≡ (σ ⊙ᵥ (idCell M ⊙ₕ σ)) ((σ ⊙ᵥ (σ ⊙ₕ idCell M)) ⊙ᵥ assoc M M M)


candidateComonad : (X : Set) → Mealy A A
candidateComonad X = record
  { E = X
  ; d = proj₂ -- can be any action
  ; s = proj₁
  }

-- Canonical comonad structure
fleshoutComonad : ∀ A → DoubleComonad A
fleshoutComonad A = record
  { M = candidateComonad A
  ; ε = record
    { α = λ { x → tt }
    ; com-s = refl -- works only if s is the projection
    ; com-d = refl
    }
  ; σ = record
    { α = λ { x → x , x }
    ; com-s = λ { {a} {e} → refl }
-- M.s (M.s (a , proj₁ (σ e)) , proj₂ (σ e)) ≡ M.s (a , e)
    ; com-d = λ { {a} {e} → refl }
-- (M.d (a , proj₁ (σ e)) , M.d (M.s (a , proj₁ (σ e)) , proj₂ (σ e))) ≡ σ (M.d (a , e))
    }
  ; counitᴸ = record { eq = refl }
  ; counitᴿ = record { eq = refl }
  ; σ-coassoc = record { eq = λ { {x} → refl } }
  }
