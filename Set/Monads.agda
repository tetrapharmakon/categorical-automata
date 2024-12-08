{-# OPTIONS --allow-unsolved-metas #-}
module Set.Monads where

open import Set.Automata
open import Set.Automata.Properties
--open import Set.LimitAutomata
--open import Set.Functors
open import Set.DoubleCategory
open import Set.CrossedModules
open import Level
open import Function

open import Data.Empty
open import Data.Product
open import Data.List
open import Data.List.NonEmpty
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.Sum hiding (map)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

private
  variable
    X Y Z A B C A' B' A'' B'' S : Set
    lv rv lv' rv' : A → B

record DoubleMonad (A : Set) : Set (suc zero) where
  field
    M : Mealy A A
    η : Cell id id idMealy M
    μ : Cell id id (M ⋄ M) M
    unitᴸ : Cell≡ (unitorᴸ M ⊙ᵥ ((η ⊙ₕ idCell M) ⊙ᵥ μ)) (idCell M)
    unitᴿ : Cell≡ (unitorᴿ⁻¹ M ⊙ᵥ ((idCell M ⊙ₕ η) ⊙ᵥ μ)) (idCell M)
    μ-assoc : Cell≡ ((idCell M ⊙ₕ μ) ⊙ᵥ μ) (assoc⁻¹ M M M ⊙ᵥ ((μ ⊙ₕ idCell M) ⊙ᵥ μ))

-- fleshout di una monade
fleshoutMonad : {A : Set}
  (M : Mealy A A)
  (e₀ : ⊤ → Mealy.E M)
  (m : Mealy.E M × Mealy.E M → Mealy.E M) → DoubleMonad A
fleshoutMonad M e₀ m = record
  { M = M -- M : A × E --⟨d,s⟩-→ E × A;
    -- d : A × E → E | action of List A on E
    -- s : A × E → A | action of E on A
  ; η = record
    { α = e₀ -- ⊤ → E
    ; com-s = {!  !}
    -- ∀ {a : A} → s (a , e) ≡ a
    -- a ◁ e ≡ a
    ; com-d = {! !}
    -- ∀ {a : A} → d (a , e) ≡ e
    -- the identity of (E, ∙) is a fixpoint for d
    }
  ; μ = record
    { α = m
    ; com-s = λ { {a} {e , e′} → {! !} }
    -- s (a , m (e , e′)) ≡ s (s (a , e) , e′)
    -- s (a , e ∙ e′) ≡ s (s (a , e) , e′ )
    -- a ◁ (e ∙ e′) ≡ (a ◁ e) ◁ e′
    ; com-d = λ { {a} {e , e′} → {! !} }
    -- d (a , m (e , e′)) ≡ m (d (a , e) , d (s (a , e) , e′))
    -- a ⊛ (e ∙ e′) ≡ (a ⊛ e) ∙ ((a ◁ e) ⊛ e′)
    }
  ; unitᴸ = record { eq = {! !} } -- m (e , x) ≡ x
  ; unitᴿ = record { eq = {! !} } -- m (x , e) ≡ x
  ; μ-assoc = record { eq = λ { {e , e′ , e′'} → {! !} } }
    -- PROBABLY m (e , m (e′ , e′')) ≡ m (m(e , e′) , e′')
  } where module M = Mealy M

record Algebra {X} (M : DoubleMonad A) : Set (suc zero) where
  private
    module M = DoubleMonad M
  field
    a : Mealy X A
    θ : Cell id id (M.M ⋄ a) a
    --
    θ-unit : Cell≡ ((idCell a ⊙ₕ M.η) ⊙ᵥ θ) (unitorᴿ a)
    θ-assoc : Cell≡ ((θ ⊙ₕ idCell M.M) ⊙ᵥ θ) (assoc M.M M.M a ⊙ᵥ ((idCell a ⊙ₕ M.μ) ⊙ᵥ θ))

{-
-- Theorem: Let M be a monad; an algebra is a set on which the bicrossed
-- product obtained from M acts
-}

--thing : (M : MonadInMealy) →
  --(a : Algebra {X = S} M) →
  --(List A × E) × Mealy.E (Algebra.a a) → Mealy.E (Algebra.a a)
--thing a M ((as , e) , s) = Cell.α θ (s , {! MonadInMealy.d∞ as e !})
  --where open module a = Algebra M

----------- Interlude on list monoids (TODO: remove this) -----------

ListMonoid : ∀ A → IsMonoid (List A)
ListMonoid A = record
  { _∙_ = _++_
  ; u = []
  ; unitᴿ = λ {x} → ++-identityʳ x
  ; unitᴸ = refl
  ; assoc = λ {x y z} → ++-assoc x y z
  }

ListActsOnE : (X : Mealy A B) → (ListMonoid A) actsOnᴸ (Mealy.E X)
ListActsOnE X = record
  { act = λ { as e → X.d⁺ (as , e) }
  ; unit = refl
  ; assoc = λ {a x y} → d⁺-assoc X {a} {x} {y}
  } where module X = Mealy X

module _ (DM : DoubleMonad A) where
  open DoubleMonad DM
  open Mealy M

  module μ = Cell μ
  module η = Cell η

  _⊗_ : A → E → E
  a ⊗ e = d (a , e)

  _⊗⁺_ : List A → E → E
  as ⊗⁺ e = d⁺ (as , e)

  e₀ : E
  e₀ = η.α tt

  d⁺-fixpoint : ∀ {as} → as ⊗⁺ e₀ ≡ e₀
  d⁺-fixpoint {as = []} = refl
  d⁺-fixpoint {as = x ∷ as} = trans (cong (λ t → d (x , t)) (d⁺-fixpoint {as = as})) η.com-d

  infixr 20 _⊙⁺_

  _⊙⁺_ : List A → E → List A
  [] ⊙⁺ e = []
  (x ∷ xs) ⊙⁺ e = s (x , xs ⊗⁺ e) ∷ (xs ⊙⁺ e)

  _◦_ : E → E → E
  e ◦ e′ = μ.α (e , e′)

  Emonoid : IsMonoid E
  Emonoid = record
    { _∙_ = _◦_
    ; u = e₀
    ; unitᴿ = Cell≡.eq unitᴿ
    ; unitᴸ = Cell≡.eq unitᴸ
    ; assoc = sym (Cell≡.eq μ-assoc)
    }

  {-
  fleshoutAlgebra : (a : Mealy X A) → (α : Mealy.E a × E → Mealy.E a) → Algebra DM
  fleshoutAlgebra a α = record
    { a = a
    ; θ = record
      { α = α -- λ { (a , m) → {! !} } -- mappa di azione di E su S = Mealy.E a
      ; com-s = λ { {x} {a , m} → {! !} } -- s (x , α (a , m)) ≡ M.s (s (x , a) , m) le due azioni sono "bilanciate"
      ; com-d = λ { {x} {a , m} → {! !} } } -- d (x , α (a , m)) ≡ α (d (x , a) , M.d (s (x , a) , m))
      -- x ⊗ (a ★ m) ≡ (x ⊗ a) ★ (aˣ ⊗ m)
    ; θ-unit = record { eq = λ { {e , tt} → {! !} } }
    ; θ-assoc = record { eq = λ { {(e , m) , m'} → {!  !} } }
    } where open module a = Mealy a
  -}

  lemmaruolo : (as : List A) (e e' : E) →
    as ⊗⁺ (e ◦ e') ≡ (as ⊗⁺ e) ◦ ((as ⊙⁺ e) ⊗⁺ e')
  lemmaruolo [] e e' =
    begin _ ≡⟨ sym (cong (e ◦_) {!   !}) ⟩
          _ ≡⟨ sym (cong₂ _◦_ refl (cong (λ t → t ⊗⁺ e) refl)) ⟩
          _ ∎
  lemmaruolo (a ∷ as) e e' =
    begin _ ≡⟨ cong (λ t → d (a , t)) (lemmaruolo as e e') ⟩
          _ ≡⟨ μ.com-d ⟩
          _ ∎

  s∞-actR : {as : List A} {x y : E} → (as ⊙⁺ x) ⊙⁺ y ≡ as ⊙⁺ (x ◦ y)
  s∞-actR {as = []} {x} {y} = refl
  s∞-actR {as = a ∷ as} {x} {y} = cong₂ _∷_  (cong s (cong₂ _,_ {!   !} 
      (begin {! !} ≡⟨ {! !} ⟩ 
             {! !} ≡⟨ sym (lemmaruolo as x y)  ⟩ 
             {! !} ∎)
    )) s∞-actR

  sUnitAxiom : ∀ {as} → as ⊙⁺ e₀ ≡ as
  sUnitAxiom {[]} = refl
  sUnitAxiom {x ∷ as} =
    begin _ ≡⟨ cong (s (x , (as ⊗⁺ η.α tt)) ∷_) sUnitAxiom ⟩
          _ ≡⟨ cong (λ t → s (x , t) ∷ as) (d⁺-fixpoint {as = as}) ⟩
          _ ≡⟨ cong (λ t → t ∷ as) η.com-s ⟩
          _ ∎

  sActsRList : ∀ {as x y} → (as ⊙⁺ x) ⊙⁺ y ≡ as ⊙⁺ (x ◦ y)
  sActsRList {as = []} {x} {y} = refl
  sActsRList {as = a ∷ as} {x} {y} = cong₂ _∷_ {! μ.com-d  !} s∞-actR

  EactsOnLists : Emonoid actsOnᴿ (List A)
  EactsOnLists = record
    { act = _⊙⁺_
    ; unit = sUnitAxiom
    ; assoc = sActsRList
    }

  miliorfo-lemma : ∀ {as} → (e : E) → e ◦ (as ⊗⁺ e₀) ≡ e
  miliorfo-lemma {[]} e = Cell≡.eq unitᴿ
  miliorfo-lemma {a ∷ as} e =
    begin _ ≡⟨ cong (λ t → e ◦ t) (d⁺-fixpoint {as = _}) ⟩
          _ ≡⟨ Cell≡.eq unitᴿ ⟩
          _ ∎

  bicrossedMonoid : IsMonoid (E × List A)
  bicrossedMonoid = record
    { _∙_ = λ { (x , as) (x' , bs) → x ◦ (as ⊗⁺ x') , (as ⊙⁺ x') ++ bs }
    ; u = e₀ , []
    ; unitᴿ = λ { {e , as} → cong₂ _,_ (miliorfo-lemma {as = as} e) (trans (++-identityʳ _) (sUnitAxiom {as = _})) }
    ; unitᴸ = λ { {e , as} → cong₂ _,_ (Cell≡.eq unitᴸ) refl }
    ; assoc = λ { {x , as} {y , bs} {z , cs} → cong₂ _,_ {!  !} {!  !} }
    }
