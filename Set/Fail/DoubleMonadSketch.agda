{-# OPTIONS --allow-unsolved-metas #-}
module Set.Fail.DoubleMonadSketch where

open import Set.Automata
open import Set.Automata.Properties
open import Set.Monads

open import Set.DoubleCategory
open import Set.CrossedModules
open import Level
open import Function

open import Data.Empty
open import Data.Product using (curry; uncurry; _×_; _,_; proj₁; proj₂)
open import Data.Product.Properties using (,-injectiveʳ; ,-injectiveˡ)
open import Data.List
open import Data.List.Properties using (++-identityʳ; ++-assoc; reverse-++; foldl-++; map-++)
open import Data.Sum hiding (map)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

private
  variable
    X Y Z A B C A' B' A'' B'' S : Set
    lv rv lv' rv' : A → B

 {-
 map (λ e → F.d (a , e)) es

 map (λ e → F.d (foldr (flip (curry F.s)) a (reverse xs) , e)) es
 -}

module _ (F : Mealy A A) where
  module F = Mealy F

  dd : A → List (Mealy.E F) → List (Mealy.E F)
  dd a = map (λ e → F.d (a , e))

  ss : A → List (Mealy.E F) → A
  ss = foldl (curry F.s)

  extension : (F : Mealy A A) → Mealy A A
  extension F = record
    { E = List F.E
    ; d = uncurry dd
    ; s = uncurry ss
    }

  doubleMonad : (F : Mealy A A) → DoubleMonad A
  doubleMonad F = record
    { M = extension F
    ; η = record
      { α = λ { x → [] }
      ; com-s = λ { {a} {tt} → refl }
      ; com-d = λ { {a} {tt} → refl }
      }
    ; μ = record
      { α = λ { (xs , ys) → xs ++ ys }
      ; com-s = λ { {a} {xs , es} → foldl-++ (curry F.s) a xs es }
      ; com-d = λ { {a} {xs , es} → begin
         map (λ e → F.d (a , e)) (xs ++ es) ≡⟨ map-++ _ xs es ⟩
         map (λ e → F.d (a , e)) xs ++ map (λ e → F.d (      a , e)) es ≡⟨ cong (map (λ e → F.d (a , e)) xs ++_) {!   !} ⟩
         map (λ e → F.d (a , e)) xs ++ map (λ e → F.d (ss a xs , e)) es ∎ } -- ""
      }
    ; unitᴸ = record { eq = refl }
    ; unitᴿ = record { eq = ++-identityʳ _ }
    ; μ-assoc = record { eq = λ { {xs , ys , zs} → sym (++-assoc xs ys zs) } }
    }
