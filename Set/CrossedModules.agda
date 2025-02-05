{-# OPTIONS --allow-unsolved-metas #-}
module Set.CrossedModules where

open import Level
open import Data.Product
open import Data.List
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Set.Automata

private
  variable
    A B C X Y Z M₀ : Set

record IsMonoid (Carrier : Set) : Set (suc zero) where
  field
    _∙_ : Carrier → Carrier → Carrier
    u : Carrier
    --
    unitᴿ : ∀ {x : Carrier} → x ∙ u ≡ x
    unitᴸ : ∀ {x : Carrier} → u ∙ x ≡ x
    assoc : ∀ {x y z : Carrier} → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

record Monoid : Set (suc zero) where
  field
    Carrier : Set
    isMonoid : IsMonoid Carrier

record _actsOnᴸ_ (M : IsMonoid M₀) (A : Set) : Set (suc zero) where
  open module M = IsMonoid M
  field
    act : M₀ → A → A
    unit : ∀ {a} → act u a ≡ a
    assoc : ∀ {a x y} → act x (act y a) ≡ act (x ∙ y) a

record _actsOnᴿ_ (M : IsMonoid M₀) (A : Set) : Set (suc zero) where
  open module M = IsMonoid M
  field
    act : A → M₀ → A
    unit : ∀ {a} → act a u ≡ a
    assoc : ∀ {a x y} → act (act a x) y ≡ act a (x ∙ y)

--record LeftModule {M : IsMonoid} : Set (suc zero) where
  --open module M = IsMonoid M
  --field
    --S : Set
    --_⋆_ : M.Carrier → S → S
    --act₁ : ∀ {s : S} → M.e ⋆ s ≡ s
    --act∙ : ∀ {x y : M.Carrier} {s : S} → (_∙_ x y) ⋆ s ≡ x ⋆ (y ⋆ s)

record MonadInMealy (A : Set) : Set (suc zero) where
  field
    E : Set
    _⊗_ : A → E → E
    _⊙_ : A → E → A
    monE : IsMonoid E

  open IsMonoid monE

  field
    act-⊗ : ∀ {a e e'} → a ⊗ (e ∙ e') ≡ ((a ⊗ e) ∙ ((a ⊙ e) ⊗ e'))
    act-⊙ : ∀ {a e e'} → a ⊙ (e ∙ e') ≡ (a ⊙ e) ⊙ e'
    id-u : ∀ {a} → a ⊗ u ≡ u
    id-a : ∀ {a} → a ⊙ u ≡ a

  d∞ : List A → E → E
  d∞ [] e = e
  d∞ (x ∷ xs) e = x ⊗ d∞ xs e

  s∞ : List A → E → List A
  s∞ [] e = []
  s∞ (a ∷ as) e = (a ⊙ d∞ as e) ∷ s∞ as e

  d∞-id : ∀ as → d∞ as u ≡ u
  d∞-id [] = refl
  d∞-id (x ∷ as) = trans (cong (x ⊗_) (d∞-id as)) id-u

  s∞-id : ∀ as → s∞ as u ≡ as
  s∞-id [] = refl
  s∞-id (x ∷ as) = cong₂ _∷_ (trans (cong (x ⊙_) (d∞-id as)) id-a) (s∞-id as)

  _⊗⋆_ : List A → E → E
  as ⊗⋆ e = d∞ as e

  _⊙⋆_ : List A → E → List A
  as ⊙⋆ e = s∞ as e

  _∙⋆_ : E → E → E
  e ∙⋆ e' = e ∙ e'

  d∞-++ : ∀ xs ys h → d∞ (xs ++ ys) h ≡ d∞ xs (d∞ ys h)
  d∞-++ [] ys h = refl
  d∞-++ (x ∷ xs) ys h = cong (x ⊗_) (d∞-++ xs ys h)

  s∞-++ : ∀ xs ys h → s∞ (xs ++ ys) h ≡ s∞ xs (d∞ ys h) ++ s∞ ys h
  s∞-++ [] ys h = refl
  s∞-++ (x ∷ xs) ys h = cong₂ _∷_ (cong (x ⊙_) (d∞-++ xs ys h)) (s∞-++ xs ys h)

  ⊗⋆-act : ∀ k h h' → k ⊗⋆ (h ∙ h') ≡ ((k ⊗⋆ h) ∙ ((k ⊙⋆ h) ⊗⋆ h'))
  ⊗⋆-act [] h h' = refl
  ⊗⋆-act (x ∷ xs) h h' =
    begin x ⊗ d∞ xs (h ∙ h')
            ≡⟨ cong (λ t → x ⊗ t) (⊗⋆-act xs h h') ⟩
          x ⊗ (d∞ xs h ∙ d∞ (s∞ xs h) h')
            ≡⟨ act-⊗ ⟩
          ((x ∷ xs) ⊗⋆ h) ∙ (((x ∷ xs) ⊙⋆ h) ⊗⋆ h')
            ∎

  ⊙⋆-act : ∀ k h h' → k ⊙⋆ (h ∙ h') ≡ (k ⊙⋆ h) ⊙⋆ h'
  ⊙⋆-act [] h h' = refl
  ⊙⋆-act (x ∷ k) h h' = cong₂ _∷_
    (begin x ⊙ d∞ k (h ∙ h') ≡⟨ cong (x ⊙_) (⊗⋆-act k h h') ⟩
           x ⊙ (d∞ k h ∙ d∞ (s∞ k h) h') ≡⟨ act-⊙ ⟩
           (x ⊙ d∞ k h) ⊙ d∞ (s∞ k h) h' ∎)
    (⊙⋆-act k h h')

  ⊙⋆-resp-++ : ∀ {k k' h} → (k ++ k') ⊙⋆ h ≡ (k ⊙⋆ (k' ⊗⋆ h)) ++ (k' ⊙⋆ h)
  ⊙⋆-resp-++ {[]} {[]} {h} = refl
  ⊙⋆-resp-++ {[]} {x ∷ k'} {h} = refl
  ⊙⋆-resp-++ {x ∷ k} {[]} {h} =
    begin (x ⊙ d∞ (k ++ []) h) ∷ s∞ (k ++ []) h
            ≡⟨ cong (λ t → (x ⊙ d∞ t h) ∷ s∞ t h) (++-identityʳ k) ⟩
          (x ⊙ d∞ k ([] ⊗⋆ h)) ∷ s∞ k ([] ⊗⋆ h)
            ≡⟨ sym (++-identityʳ _) ⟩
          (x ⊙ d∞ k ([] ⊗⋆ h)) ∷ s∞ k ([] ⊗⋆ h) ++ ([] ⊙⋆ h)
            ∎
  ⊙⋆-resp-++ {x ∷ xs} {y ∷ ys} {h} =
    begin (x ⊙ d∞ (xs ++ y ∷ ys) h) ∷ s∞ (xs ++ y ∷ ys) h
            ≡⟨ cong (λ t → (x ⊙ d∞ (xs ++ y ∷ ys) h) ∷ t) (⊙⋆-resp-++ {xs} {y ∷ ys} {h}) ⟩
          (x ⊙ d∞ (xs ++ y ∷ ys) h) ∷ s∞ xs (y ⊗ d∞ ys h) ++ (y ⊙ d∞ ys h) ∷ s∞ ys h
            ≡⟨ cong (λ t → t ∷ (s∞ xs (y ⊗ d∞ ys h) ++ (y ⊙ d∞ ys h) ∷ s∞ ys h)) (cong (λ r → x ⊙ r) (d∞-++ xs (y ∷ ys) h)) ⟩
          (x ⊙ d∞ xs ((y ∷ ys) ⊗⋆ h)) ∷ s∞ xs ((y ∷ ys) ⊗⋆ h) ++ ((y ∷ ys) ⊙⋆ h)
            ∎

  BiCrossed : IsMonoid (E × List A)
  BiCrossed = record
    { _∙_ = λ { (x , as) (x' , bs) → (_∙_ x (as ⊗⋆ x')) , (as ⊙⋆ x') ++ bs }
    ; u = u , []
    ; unitᴿ = λ { {x , as} →
        begin
          (x ∙ (as ⊗⋆ u)) , (as ⊙⋆ u) ++ []
            ≡⟨ cong (λ t → (x ∙ d∞ as u) , t) (++-identityʳ (s∞ as u)) ⟩
          x ∙ d∞ as u , s∞ as u
            ≡⟨ cong₂ _,_ (trans (cong (λ t → x ∙ t) (d∞-id as)) unitᴿ)
                        (s∞-id as) ⟩
          x , as
            ∎ }
    ; unitᴸ = λ { {x , as} → cong (λ t → t , as) unitᴸ }
    ; assoc = λ { {x , as} {y , bs} {z , cs} → begin
            (x ∙ d∞ as y) ∙ d∞ (s∞ as y ++ bs) z   , s∞ (s∞ as y ++ bs) z ++ cs
              ≡⟨ cong₂ _,_ (trans assoc (cong (λ t → (x ∙ (d∞ as y ∙ t))) (d∞-++ (s∞ as y) bs z)))
                           (cong (_++ cs) (s∞-++ (s∞ as y) bs z)) ⟩
            x ∙ (d∞ as y ∙ d∞ (s∞ as y) (d∞ bs z)) , (s∞ (s∞ as y) (d∞ bs z) ++ s∞ bs z) ++ cs
              ≡⟨ cong₂ _,_ (cong (x ∙_) (sym (⊗⋆-act as y (d∞ bs z))))
                           (trans (cong (λ t → (t ++ s∞ bs z) ++ cs)
                                  (sym (⊙⋆-act as y (d∞ bs z))))
                                  (++-assoc (s∞ as (y ∙ d∞ bs z)) (s∞ bs z) cs)) ⟩
            x ∙ d∞ as (y ∙ d∞ bs z)                , s∞ as (y ∙ d∞ bs z) ++ s∞ bs z ++ cs ∎ }
    }

  BicrossedActsOnE : BiCrossed actsOnᴸ E
  BicrossedActsOnE = record
    { act = λ { (m , as) x → as ⊗⋆ (m ∙ x) }
    ; unit = unitᴸ --unitᴿ
    ; assoc = λ { {a} {x} {y} → lemma {a} {x} {y} }
    -- λ { {a} {x , x'} {y , y'} →
    --   begin d∞ x' (d∞ y' (a ∙ y) ∙ x) ≡⟨ cong (λ t → d∞ x' (t ∙ x)) (⊗⋆-act y' a y) ⟩
    --         d∞ x' ((d∞ y' a ∙ d∞ (s∞ y' a) y) ∙ x) ≡⟨ ⊗⋆-act x' _ _ ⟩
    --         d∞ x' (d∞ y' a ∙ d∞ (s∞ y' a) y) ∙ d∞ (s∞ x' (d∞ y' a ∙ d∞ (s∞ y' a) y)) x ≡⟨ cong (_∙ d∞ (s∞ x' (d∞ y' a ∙ d∞ (s∞ y' a) y)) x) (⊗⋆-act x' _ _) ⟩
    --         (d∞ x' (d∞ y' a) ∙ d∞ (s∞ x' (d∞ y' a)) (d∞ (s∞ y' a) y)) ∙ d∞ (s∞ x' (d∞ y' a ∙ d∞ (s∞ y' a) y)) x ≡⟨ assoc ⟩
    --         d∞ x' (d∞ y' a) ∙ (d∞ (s∞ x' (d∞ y' a)) (d∞ (s∞ y' a) y) ∙ d∞ (s∞ x' (d∞ y' a ∙ d∞ (s∞ y' a) y)) x)
    --           ≡⟨ {!  !} ⟩
    --         {!   !} ≡⟨ {!   !} ⟩
    --         {!   !} ≡⟨ {! ⊗⋆-act (s∞ x' y) _ _  !} ⟩
    --         d∞ (s∞ x' y) (d∞ y' a) ∙ (d∞ (s∞ (s∞ x' y) (d∞ y' a)) (d∞ (s∞ y' a) x) ∙ d∞ (s∞ (s∞ (s∞ x' y) (d∞ y' a)) (d∞ (s∞ y' a) x)) (d∞ (s∞ (s∞ y' a) x) (d∞ x' y)))
    --           ≡⟨ cong (λ t → d∞ (s∞ x' y) (d∞ y' a) ∙ t) (sym (⊗⋆-act (s∞ (s∞ x' y) (d∞ y' a)) _ _)) ⟩
    --         (d∞ (s∞ x' y) (d∞ y' a) ∙ d∞ (s∞ (s∞ x' y) (d∞ y' a)) (d∞ (s∞ y' a) x ∙ d∞ (s∞ (s∞ y' a) x) (d∞ x' y)))
    --           ≡⟨ cong (λ t → d∞ (s∞ x' y) (d∞ y' a) ∙ d∞ (s∞ (s∞ x' y) (d∞ y' a)) t) (sym (⊗⋆-act (s∞ y' a) x (d∞ x' y))) ⟩
    --         d∞ (s∞ x' y) (d∞ y' a) ∙ d∞ (s∞ (s∞ x' y) (d∞ y' a)) (d∞ (s∞ y' a) (x ∙ d∞ x' y)) ≡⟨ sym (⊗⋆-act (s∞ x' y) _ _) ⟩
    --         d∞ (s∞ x' y) (d∞ y' a ∙ d∞ (s∞ y' a) (x ∙ d∞ x' y)) ≡⟨ cong (d∞ (s∞ x' y)) (sym (⊗⋆-act y' a _)) ⟩
    --         d∞ (s∞ x' y) (d∞ y' (a ∙ (x ∙ d∞ x' y))) ≡⟨ sym (d∞-++ (s∞ x' y) y' _ ) ⟩
    --         d∞ (s∞ x' y ++ y') (a ∙ (x ∙ d∞ x' y)) ∎ }
    } where
    lemma : ∀ {a : E} {x y : E × List A} → _
    lemma {a} {x , []} {y , v} = {!   !}
    lemma {a} {x , x₁ ∷ c} {y , []} = {!   !}
    lemma {a} {x , x₁ ∷ c} {y , x₂ ∷ v} = {!   !}
