module Set.Fail.Adjoints where

open import Data.Product using (_,_; _×_; proj₁; proj₂; curry)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; cong; trans; sym)
open import Data.List.NonEmpty using (List⁺; _∷_; _∷⁺_; toList; [_])
open import Data.List using (List; []; _∷_)
open import Function using (id; _∘_; flip)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; head; _∷ʳ_; _∷_; foldl; replicate)

open import Set.Automata
open import Set.LimitAutomata
open import Set.Soft
open import Set.Utils
open import Set.Equality
open import Set.Functors

private
  variable
    I O A B C : Set
    Mre : Moore A B
    Mly : Mealy A B

module Adjunctions where

  i⊣𝕂 : (M : Moore A B)
      → (soft : Soft M)
      → (N : Moore A B)
      → (Moore⇒ M N) ≅ (Moore⇒ M (P∞ _ ⋈ N))
  i⊣𝕂 M soft N =
      let module M = Moore M
          module N = Moore N in record
    { to = λ α → let module α = Moore⇒ α in record { hom = λ x → (α.hom x) , (homP∞ (α.X.s x))
      ; d-eq = λ {(a , e) → cong₂ _,_ (α.d-eq (a , e)) (cong homP∞ (soft))}
      ; s-eq = λ {e → refl} }
    ; from = λ β → let module β = Moore⇒ β in record { hom = λ x → proj₁ (β.hom x)
      ; d-eq = λ {(a , e) → cong proj₁ (β.d-eq (a , e)) }
      ; s-eq = λ {e → trans {!   !} (β.s-eq e) } }
    ; to∘from=1 = λ {x → let module x = Moore⇒ x in
                  Moore⇒-≡ _ x (extensionality λ t
                                  → cong (λ v → (proj₁ (x.hom t) , v))
                                        (P∞-≡ (homP∞ (x.X.s t))
                                                (proj₂ (x.hom t))
                                                (extensionality (λ { [] → sym (x.s-eq t)
                                                                    ; (x ∷ w) → sym (P∞carrier.eq (proj₂ (x.hom t)) (x ∷ w))
                                                                    }))))}
    ; from∘to=1 = λ x → Moore⇒-≡ _ x refl
    } where
        homP∞ : B → (P∞carrier B)
        homP∞ b = record
          { f = λ { [] → b
                  ; (x ∷ tail) → x}
          ; eq = λ t → refl
          }
