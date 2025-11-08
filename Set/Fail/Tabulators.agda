{-# OPTIONS --allow-unsolved-metas #-}
module Set.Fail.Tabulators where

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

open import Set.Limits

private
  variable
    X Y Z U V A B C A' B' A'' B'' : Set
    lv rv lv' rv' : A → B

record SubobjectOfInterest (M : Mealy X Y) : Set (suc zero) where
  private
    module M = Mealy M
  field
    e : M.E
    fix-d   : ∀ {x} → M.d (x , e) ≡ e
    se-surj : ∀ {y} → ∃[ x ] (M.s (x , e) ≡ y)

tabulators : (M : Mealy X Y) → (SOI : SubobjectOfInterest M) → Tabulator M
tabulators {X = X} {Y = Y} M SOI =
  let module M = Mealy M
      module SOI = SubobjectOfInterest SOI in
    record
      { tab = X × Y
      ; p = proj₁
      ; q = proj₂
      ; τ = record
        { α = λ { _ → SOI.e }
        ; com-s = λ { {x , y} → {! proj₂ (SOI.se-surj {y}) !} }
        ; com-d = λ { {x , y} {tt} → SOI.fix-d }
        }
      ; universal = λ { {f = f} {g = g} ξ → < f , g > }
      ; fst-commute₁ = λ { ξ → refl }
      ; snd-commute₁ = λ { ξ → refl }
      ; commute₂ = record { eq = λ { {x} → {! !} } } --impossible
      }
