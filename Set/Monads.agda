{-# OPTIONS --allow-unsolved-metas #-} 
module Set.Monads where

open import Set.Automata
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
open import Data.Sum hiding (map)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

private
  variable
    X Y Z A B C A' B' A'' B'' S : Set
    lv rv lv' rv' : A → B

record DoubleMonad {A : Set} : Set (suc zero) where 
  field
    M : Mealy A A
    η : Cell id id idMealy M
    μ : Cell id id (M ⋄ M) M
    unitᴸ : Cell≡ (unitorᴸ M ⊙ᵥ ((η ⊙ₕ idCell M) ⊙ᵥ μ)) (idCell M)
    unitᴿ : Cell≡ (unitorᴿ⁻¹ M ⊙ᵥ ((idCell M ⊙ₕ η) ⊙ᵥ μ)) (idCell M)
    μ-assoc : Cell≡ ((idCell M ⊙ₕ μ) ⊙ᵥ μ) (assoc⁻¹ ⊙ᵥ ((μ ⊙ₕ idCell M) ⊙ᵥ μ))

-- fleshout di una monade
fleshoutMonad : {A : Set} 
  (M : Mealy A A) 
  (e₀ : ⊤ → Mealy.E M) 
  (m : Mealy.E M × Mealy.E M → Mealy.E M) → DoubleMonad {A}
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
    ; com-s = λ { {a} {e , e'} → {! !} }
    -- s (a , m (e , e')) ≡ s (s (a , e) , e')
    -- s (a , e ∙ e') ≡ s (s (a , e) , e' )
    -- a ◁ (e ∙ e') ≡ (a ◁ e) ◁ e'
    ; com-d = λ { {a} {e , e'} → {! !} }
    -- d (a , m (e , e')) ≡ m (d (a , e) , d (s (a , e) , e'))
    -- a ⊛ (e ∙ e') ≡ (a ⊛ e) ∙ ((a ◁ e) ⊛ e')
    } 
  ; unitᴸ = record { eq = {! !} } -- m (e , x) ≡ x
  ; unitᴿ = record { eq = {! !} } -- m (x , e) ≡ x
  ; μ-assoc = record { eq = λ { {e , e' , e''} → {! !} } } 
    -- PROBABLY m (e , m (e' , e'')) ≡ m (m(e , e') , e'')
  } where module M = Mealy M

record Algebra {X} (M : DoubleMonad {A}) : Set (suc zero) where 
  module M = DoubleMonad M
  field 
    a : Mealy X A 
    θ : Cell id id (M.M ⋄ a) a 
    -- 
    θ-unit : Cell≡ ((idCell a ⊙ₕ M.η) ⊙ᵥ θ) (unitorᴿ a) 
    θ-assoc : Cell≡ ((θ ⊙ₕ idCell M.M) ⊙ᵥ θ) (assoc ⊙ᵥ ((idCell a ⊙ₕ M.μ) ⊙ᵥ θ))

fleshoutAlgebra : (a : Mealy X A) → 
  (M : DoubleMonad {A}) → 
  (α : Mealy.E a × Mealy.E (DoubleMonad.M M) → Mealy.E a) → Algebra M
fleshoutAlgebra a M α = record 
  { a = a 
  ; θ = record 
    { α = α -- λ { (a , m) → {! !} } -- mappa di azione di E su S = Mealy.E a
    ; com-s = λ { {x} {a , m} → {! !} } -- s (x , α (a , m)) ≡ M.s (s (x , a) , m) le due azioni sono "bilanciate"
    ; com-d = λ { {x} {a , m} → {! !} } } -- d (x , α (a , m)) ≡ α (d (x , a) , M.d (s (x , a) , m))
    -- x ⊗ (a ★ m) ≡ (x ⊗ a) ★ (aˣ ⊗ m)
  ; θ-unit = record { eq = λ { {e , tt} → {! !} } } 
  ; θ-assoc = record { eq = λ { {(e , m) , m'} → {! !} } }
  } where open module M = DoubleMonad M
          open module a = Mealy a


{- 
-- Theorem: Let M be a monad; an algebra is a set on which the bicrossed 
-- product obtained from M acts 
-}

--thing : (M : MonadInMealy) → 
  --(a : Algebra {X = S} M) →
  --(List A × Mealy.E (DoubleMonad.M M)) × Mealy.E (Algebra.a a) → Mealy.E (Algebra.a a)
--thing a M ((as , e) , s) = Cell.α θ (s , {! MonadInMealy.d∞ as e !})
  --where open module a = Algebra M

dExt : {M : Mealy A B} → (List A) × Mealy.E M → Mealy.E M 
dExt ([] , e) = e
dExt {M = M} (x ∷ xs , e) = M.d (x , dExt (xs , e))
  where module M = Mealy M

_⊗_ : {M : DoubleMonad {A}} → A → Mealy.E (DoubleMonad.M M) → Mealy.E (DoubleMonad.M M)
_⊗_ {M = M} a e = M.d (a , e) 
  where module M = Mealy (DoubleMonad.M M)

_⊗⁺_ : {M : DoubleMonad {A}} → List A → Mealy.E (DoubleMonad.M M) → Mealy.E (DoubleMonad.M M)
as ⊗⁺ e = dExt (as , e)

dExt-fixpoint : {M : DoubleMonad {A}} {as : List A} → dExt (as , Cell.α (DoubleMonad.η M) tt) ≡ Cell.α (DoubleMonad.η M) tt 
dExt-fixpoint {as = []} = refl
dExt-fixpoint {M = M} {as = x ∷ as} = trans (cong (λ t → MM.d (x , t)) dExt-fixpoint) (Cell.com-d M.η)
  where module M = DoubleMonad M
        module MM = Mealy (DoubleMonad.M M)

unitR : (x : List A) → x ++ [] ≡ x 
unitR [] = refl 
unitR (x ∷ xs) = cong (λ t → x ∷ t) (unitR xs)

dExt-assoc : {X : Mealy A B} {a : Mealy.E X} {x y : List A} → dExt (x , dExt (y , a)) ≡ dExt (x ++ y , a)
dExt-assoc {a = e} {x = []} {y = bs} = refl
dExt-assoc {X = X} {a = e} {x = a ∷ as} {y = []} = cong (λ t → X.d (a , dExt (t , e))) (sym (unitR as))
  where module X = Mealy X
dExt-assoc {X = X} {a = e} {x = a ∷ as} {y = b ∷ bs} = cong (λ t → X.d (a , t)) dExt-assoc
  where module X = Mealy X

sExt : {M : Mealy A B} → (List⁺ A) × Mealy.E M → B 
sExt {M = M} (x ∷ xs , e) = M.s (x , dExt (xs , e))
  where module M = Mealy M

_⊙_ : {M : DoubleMonad {A}} → (List A) → Mealy.E (DoubleMonad.M M) → List A
_⊙_ {M = M} [] e = []
_⊙_ {M = M} (x ∷ xs) e = M.s (x , xs ⊗⁺ e) ∷ (xs ⊙ e)
  where module M = Mealy (DoubleMonad.M M)

s∞ : {M : DoubleMonad {A}} → (List A) → Mealy.E (DoubleMonad.M M) → List A
s∞ [] e = []
s∞ {M = M} (x ∷ xs) e = M.s (x , dExt (xs , e)) ∷ s∞ xs e 
  where module M = Mealy (DoubleMonad.M M)

s∞-acta : {M : DoubleMonad {A}} {as : List A} {x y : Mealy.E (DoubleMonad.M M)} → s∞ (s∞ as y) x ≡ s∞ as (Cell.α (DoubleMonad.μ M) (x , y))
s∞-acta {M = M} {as = []} {x} {y} = refl
s∞-acta {M = M} {as = a ∷ as} {x} {y} = cong₂ _∷_ (cong MM.s (cong₂ _,_ {! !} {! !})) s∞-acta
  where module MM = Mealy (DoubleMonad.M M)
        module M = DoubleMonad M

ListMonoid : {A} → IsMonoid (List A)
ListMonoid {A = A} = record { isMonoid = record 
  { _∙_ = λ { xs ys → xs ++ ys } 
  ; u = [] 
  ; unitᴿ = λ { {x} → unitR x }
  ; unitᴸ = λ { {x} → refl }
  ; assoc = {!  !} 
  } }

Emonoid : (M : DoubleMonad {A}) → IsMonoid (Mealy.E (DoubleMonad.M M))
Emonoid M = record { isMonoid = record 
  { _∙_ = λ { x y → Cell.α M.μ (x , y) } 
  ; u = Cell.α M.η tt 
  ; unitᴿ = λ { {x} → Cell≡.eq M.unitᴿ }
  ; unitᴸ = λ { {x} → Cell≡.eq M.unitᴸ }
  ; assoc = λ { {x} {y} {z} → sym (Cell≡.eq M.μ-assoc) }
  } } where module M = DoubleMonad M

ListActsOnE : (X : Mealy A B) → (IsMonoid.isMonoid (ListMonoid {A})) actsOnᴸ (Mealy.E X)
ListActsOnE X = record 
  { act = λ { as e → dExt (as , e) } 
  ; unit = refl 
  ; assoc = dExt-assoc 
  }

rallo : {M : DoubleMonad {A}} {as : List A} → s∞ as (Cell.α (DoubleMonad.η M) tt) ≡ as
rallo {A} {M} {[]} = refl
rallo {A} {M} {x ∷ as} = 
  begin _ ≡⟨ cong₂ _∷_ refl rallo ⟩
        _ ≡⟨ cong (λ t → MM.s (x , t) ∷ as) dExt-fixpoint ⟩
        _ ≡⟨ cong (λ t → t ∷ as) (Cell.com-s M.η) ⟩
        _ ∎
  where module MM = Mealy (DoubleMonad.M M)
        module M = DoubleMonad M

sbollo : {M : DoubleMonad {A}} {as : List A} {x y : Mealy.E (DoubleMonad.M M)} → s∞ (s∞ as y) x ≡ s∞ as (Cell.α (DoubleMonad.μ M) (x , y))
sbollo {M = M} {as = []} {x} {y} = refl
sbollo {M = M} {as = a ∷ as} {x} {y} = cong₂ (_∷_) (cong MM.s {! !}) s∞-acta
  where module MM = Mealy (DoubleMonad.M M)
        module M = DoubleMonad M

--s (s (a , dExt  (as , y)) , dExt  (s∞ as y , x)) ≡ s (a , dExt  (as , Cell.α M.μ (x , y)))
EactsOnLists : (M : DoubleMonad {A}) → IsMonoid.isMonoid (Emonoid M) actsOnᴸ (List A)
EactsOnLists M = record 
  { act = λ x y → s∞ y x
  ; unit = rallo
  ; assoc = sbollo 
  } where module M = DoubleMonad M
          module MM = Mealy (DoubleMonad.M M)

bicrossedMonoid : (M : DoubleMonad {A}) → Monoid (Mealy.E (DoubleMonad.M M) × List A) 
bicrossedMonoid M = record
  { _∙_ = λ { (x , as) (x' , bs) → {! !} } -- (M._∙_ x (as ⊗⋆ x')) , (as ⊙⋆ x') ++ bs }
  ; u = Cell.α M.η tt , [] 
  ; unitᴿ = λ { {x , as} → {! !} }
  ; unitᴸ = λ { {x , as} → {! !} }
  ; assoc = λ { {x , as} {y , bs} {z , cs} → {! !} }
  } where module M = DoubleMonad M
          module MM = Mealy (DoubleMonad.M M)

