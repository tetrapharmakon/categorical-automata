{-# OPTIONS --allow-unsolved-metas #-}
module Set.Fail.Colimits where

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

record DoubleInitial : Set (suc zero) where
  field
    Ø : Set
    universal₁ : ∀ {X Y} (M : Mealy X Y) → (Ø → X) × (Ø → Y)
    universal₂ : ∀ {X Y} (M : Mealy X Y) → Cell (proj₁ (universal₁ M)) (proj₂ (universal₁ M)) idMealy M
    unique : ∀ {X Y} {M : Mealy X Y} {c : Cell (proj₁ (universal₁ M)) (proj₂ (universal₁ M)) idMealy M} → Cell≡ c (universal₂ M)

record DoubleSum (A B : Set) : Set (suc zero) where
  field
    sum : Set
    in₁ : A → sum
    in₂ : B → sum
    ι₁ : Cell in₁ in₁ idMealy idMealy
    ι₂ : Cell in₂ in₂ idMealy idMealy
    universal₁ : ∀ {u : Mealy X Y} {a : A → X} {a' : A → Y} {b : B → X} {b' : B → Y} →
      (ξ₁ : Cell a a' idMealy u) (ξ₂ : Cell b b' idMealy u) →
      (sum → X) × (sum → Y)
    universal₂ : ∀ {u : Mealy X Y} {a : A → X} {a' : A → Y} {b : B → X} {b' : B → Y} →
      (ξ₁ : Cell a a' idMealy u) (ξ₂ : Cell b b' idMealy u)  →
      (Cell (proj₁ (universal₁ ξ₁ ξ₂)) (proj₂ (universal₁ ξ₁ ξ₂)) idMealy u)
    fst-commute₁ : ∀ {u : Mealy X Y} {a : A → X} {a' : A → Y} {b : B → X} {b' : B → Y} →
      (ξ₁ : Cell a a' idMealy u) (ξ₂ : Cell b b' idMealy u)  →
      (proj₁ (universal₁ ξ₁ ξ₂) ∘ in₁ ≡ a) × (proj₂ (universal₁ ξ₁ ξ₂) ∘ in₁ ≡ a')
    snd-commute₁ : ∀ {u : Mealy X Y} {a : A → X} {a' : A → Y} {b : B → X} {b' : B → Y} →
      (ξ₁ : Cell a a' idMealy u) (ξ₂ : Cell b b' idMealy u)  →
      (proj₁ (universal₁ ξ₁ ξ₂) ∘ in₂ ≡ b) × (proj₂ (universal₁ ξ₁ ξ₂) ∘ in₂ ≡ b')
    fst-commute₂ : ∀ {u : Mealy X Y} {a : A → X} {a' : A → Y} {b : B → X} {b' : B → Y} →
      (ξ₁ : Cell a a' idMealy u) (ξ₂ : Cell b b' idMealy u)  →
      (Cell≡ ξ₁ (subst₂ (λ Q R → Cell Q R idMealy u) (proj₁ (fst-commute₁ ξ₁ ξ₂)) (proj₂ (fst-commute₁ ξ₁ ξ₂)) (ι₁ ⊙ᵥ universal₂ ξ₁ ξ₂)))
    snd-commute₂ : ∀ {u : Mealy X Y} {a : A → X} {a' : A → Y} {b : B → X} {b' : B → Y} →
      (ξ₁ : Cell a a' idMealy u) (ξ₂ : Cell b b' idMealy u)  →
      (Cell≡ ξ₂ (subst₂ (λ Q R → Cell Q R idMealy u) (proj₁ (snd-commute₁ ξ₁ ξ₂)) (proj₂ (snd-commute₁ ξ₁ ξ₂)) (ι₂ ⊙ᵥ universal₂ ξ₁ ξ₂)))

testInitial : (M : Mealy X Y) → (e : Mealy.E M) → DoubleInitial
testInitial M e = record
  { Ø = ⊥
  ; universal₁ = λ { M → (λ { () }) , λ { () } }
  ; universal₂ = λ { M → record
    { α = λ { tt → {! e !} }
    ; com-s = λ { {()} }
    ; com-d = λ { {()} }
    } }
  ; unique = record { eq = λ { {tt} → {!  !} } }
  }

candidateDblSum :
  (pointedness : ∀ {X} {Y} (M : Mealy X Y) → Mealy.E M)
  → DoubleSum A B
candidateDblSum {A = A} {B = B} pointedness = record
  { sum = A ⊎ B
  ; in₁ = inj₁
  ; in₂ = inj₂
  ; ι₁ = record
    { α = λ { x → x }
    ; com-s = refl
    ; com-d = refl
    }
  ; ι₂ = record
    { α = λ { x → tt }
    ; com-s = refl
    ; com-d = refl
    }
  ; universal₁ = λ { {a = a} {a' = a'} {b = b} {b' = b'}
    ξ₁ ξ₂ → (λ { (inj₁ x) → a x
               ; (inj₂ y) → b y })
          , (λ { (inj₁ x) → a' x
               ; (inj₂ y) → b' y }) }
  ; universal₂ = λ { {u = u} {a = a} {a' = a'} {b = b} {b' = b'}
       ξ₁ ξ₂ → record
            { α = λ { tt → pointedness u }
            ; com-s = λ { {inj₁ x} {tt} → {! Cell.com-s ξ₁  !}
                        ; {inj₂ y} {tt} → {! Cell.com-s ξ₂ !} }
            ; com-d = λ { {x} {tt} → {! !} }
            } }
  ; fst-commute₁ = λ { ξ₁ ξ₂ → refl , refl }
  ; snd-commute₁ = λ { ξ₁ ξ₂ → refl , refl}
  ; fst-commute₂ = λ { ξ₁ ξ₂ → record { eq = {! !} } }
  ; snd-commute₂ = λ { ξ₁ ξ₂ → record { eq = {! !} } }
  }
  -- for each u, choose a point on u's carrier, which is always the same;
  -- clearly, this cannot be done if u.E has more than one element.
