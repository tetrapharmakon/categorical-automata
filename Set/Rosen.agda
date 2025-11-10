module Set.Rosen where

open import Set.Automata
open import Data.Sum
open import Data.Product

record MR (I : Set) (O : Set) : Set₁ where
  eta-equality
  field
    f : I → O
    ϕ : O → (I → O)

open MR

private
  variable
    A B C I O : Set

⟦_⟧ : MR I O → Mealy I O 
⟦_⟧ {I} {O} M = record 
  { E = I → O 
  ; d = λ { (i , y) i' → M.ϕ (y i) i' } 
  ; s = λ { (i , y) → y i } 
  } where module M = MR M

