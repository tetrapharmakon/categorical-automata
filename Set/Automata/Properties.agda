
module Set.Automata.Properties where

open import Set.Automata

open import Level
open import Data.Product using (map₂; _,_; _×_)
open import Data.Unit using (⊤)
open import Data.List using (List; _∷_; []; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

private
  variable
    ℓ : Level
    I O A B A′ B′ C D : Set ℓ

module _ (X : Mealy A B) where
  open Mealy X

  d⁺-assoc : ∀ {a x y} → d⁺ (x , d⁺ (y , a)) ≡ d⁺ (x ++ y , a)
  d⁺-assoc {a = a} {x = []} {y = bs} = refl
  d⁺-assoc {a = a} {x = x ∷ as} {y = []} = cong (λ t → d (x , d⁺ (t , a))) (sym (++-identityʳ as))
  d⁺-assoc {a = a} {x = x ∷ as} {y = b ∷ bs} = cong (λ t → d (x , t)) (d⁺-assoc {a = a} {x = as} {y = b ∷ bs})
