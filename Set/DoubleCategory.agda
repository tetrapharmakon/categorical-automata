module Set.DoubleCategory where

open import Set.Automata
open import Level


open import Data.Product using (map₁; map₂; map; <_,_>; _,_; _×_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)

record Cell {A B A' B' : Set} (lv : A → A') (rv : B → B') (lh : Mealy A B) (rh : Mealy A' B') : Set (suc zero) where
  module lh = Mealy lh 
  module rh = Mealy rh
  field
    α  : lh.E → rh.E
    --com : ∀ {x y} → < rh.d , rh.s > (map lv α (x , y)) ≡ map α rv (< lh.d , lh.s > (x , y))
    com-s : ∀ {x y} → rh.s (lv x , α y) ≡ rv (lh.s (x , y))
    com-d : ∀ {x y} → rh.d (lv x , α y) ≡  α (lh.d (x , y))


record Tabulator {X Y} (M : Mealy X Y) : Set (suc zero) where
  module M = Mealy M
  field
    tab : Set
    x   : tab → X
    y   : tab → Y
    τ   : Cell x y idMealy M


