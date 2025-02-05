{-# OPTIONS --allow-unsolved-metas #-}
module Set.Monads where

open import Set.Automata
open import Set.Automata.Properties
open import Set.DoubleCategory
open import Set.CrossedModules
open import Level
open import Function

open import Data.Empty
open import Data.Product using (curry; uncurry; _×_; _,_; proj₁; proj₂)
open import Data.Product.Properties using (,-injectiveʳ; ,-injectiveˡ)
open import Data.List
open import Data.List.Properties using (++-identityʳ; ++-assoc; reverse-++; foldr-++; map-++)
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
  module unitᴸ = Cell≡ unitᴸ
  module unitᴿ = Cell≡ unitᴿ
  module μ-assoc = Cell≡ μ-assoc

record Algebraᴿ {X} (M : DoubleMonad A) : Set (suc zero) where
  private
    module M = DoubleMonad M
  field
    P : Mealy X A
    θ : Cell id id (M.M ⋄ P) P
    --
    θ-unit : Cell≡ ((idCell P ⊙ₕ M.η) ⊙ᵥ θ) (unitorᴿ P)
    θ-assoc : Cell≡ ((θ ⊙ₕ idCell M.M) ⊙ᵥ θ) (assoc M.M M.M P ⊙ᵥ ((idCell P ⊙ₕ M.μ) ⊙ᵥ θ))

record Algebraᴸ {X} (M : DoubleMonad A) : Set (suc zero) where
  private
    module M = DoubleMonad M
  field
    P : Mealy A X
    θ : Cell id id (P ⋄ M.M) P
    --
    θ-unit : Cell≡ ((M.η ⊙ₕ idCell P) ⊙ᵥ θ) (unitorᴸ⁻¹ P)
    θ-assoc : Cell≡ ((idCell M.M ⊙ₕ θ) ⊙ᵥ θ) (assoc⁻¹ P M.M M.M ⊙ᵥ ((M.μ ⊙ₕ idCell P) ⊙ᵥ θ))

{-
-- Theorem: Let M be a monad; an algebra is a set on which the bicrossed
-- product obtained from M acts
-}

----------- Interlude on list monoids -----------

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
  -- the definition must be such that: s ⊙⁺ (e ◦ e') ≡ (as ⊙⁺ e)

  infixr 30 _◦_

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

  d⁺-nact : (as : List A) (e e' : E) →
    as ⊗⁺ (e ◦ e') ≡ (as ⊗⁺ e) ◦ ((as ⊙⁺ e) ⊗⁺ e')
  d⁺-nact [] e e' = refl
  d⁺-nact (a ∷ as) e e' =
    begin _ ≡⟨ cong (λ t → d (a , t)) (d⁺-nact as e e') ⟩
          _ ≡⟨ μ.com-d ⟩
          _ ≡⟨ cong (λ t → μ.α (d (a , d⁺ (as , e)) , t)) refl ⟩
          _ ∎

  s∞-nactR : {as bs : List A} {x : E} →
    (as ++ bs) ⊙⁺ x ≡ (as ⊙⁺ d⁺ (bs , x)) ++ (bs ⊙⁺ x)
  s∞-nactR {as = []} {bs = bs} {x} = refl
  s∞-nactR {as = a ∷ as} {bs = bs} {x} =
    cong₂ _∷_
      (cong (λ t → s (a , t)) (sym (d⁺-assoc M {x = as} {y = bs})))
      (s∞-nactR {as = as})

  sUnitAxiom : ∀ {as} → as ⊙⁺ e₀ ≡ as
  sUnitAxiom {[]} = refl
  sUnitAxiom {x ∷ as} =
    begin _ ≡⟨ cong (s (x , (as ⊗⁺ η.α tt)) ∷_) sUnitAxiom ⟩
          _ ≡⟨ cong (λ t → s (x , t) ∷ as) (d⁺-fixpoint {as = as}) ⟩
          _ ≡⟨ cong (λ t → t ∷ as) η.com-s ⟩
          _ ∎

  cancel-⊗e₀ : ∀ {as} → (e : E) → e ◦ (as ⊗⁺ e₀) ≡ e
  cancel-⊗e₀ {[]} e = Cell≡.eq unitᴿ
  cancel-⊗e₀ {a ∷ as} e =
    begin _ ≡⟨ cong (λ t → e ◦ d (a , t)) (d⁺-fixpoint {as = as}) ⟩
          _ ≡⟨ cong (λ t → e ◦ t) η.com-d ⟩
          _ ≡⟨ Cell≡.eq unitᴿ ⟩
          _ ∎

  ⊙⁺-act : ∀ {as x y} → (as ⊙⁺ y) ⊙⁺ x ≡ as ⊙⁺ μ.α (y , x)
  ⊙⁺-act {[]} = refl
  ⊙⁺-act {x ∷ as} =
    begin s (s (x , d⁺ (as , _)) , d⁺ (as ⊙⁺ _ , _)) ∷ (as ⊙⁺ _) ⊙⁺ _
            ≡⟨ cong (λ t → t ∷ (as ⊙⁺ _) ⊙⁺ _) (sym μ.com-s) ⟩
          s (x , μ.α (d⁺ (as , _) , d⁺ (as ⊙⁺ _ , _))) ∷ _
            ≡⟨ cong (λ t → s (x , t) ∷ (as ⊙⁺ _) ⊙⁺ _) (sym (d⁺-nact as _ _)) ⟩
          s (x , d⁺ (as , μ.α (_ , _))) ∷ (as ⊙⁺ _) ⊙⁺ _
            ≡⟨ cong (λ t → s (x , d⁺ (as , μ.α (_ , _))) ∷ t) (⊙⁺-act {as}) ⟩
          s (x , d⁺ (as , μ.α (_ , _))) ∷ as ⊙⁺ μ.α (_ , _) ∎

  bicrossedMonoid : IsMonoid (E × List A)
  bicrossedMonoid = record
    { _∙_ = λ { (x , as) (x' , bs) → x ◦ (as ⊗⁺ x') , (as ⊙⁺ x') ++ bs }
    ; u = e₀ , []
    ; unitᴿ = λ { {e , as} → cong₂ _,_ (cancel-⊗e₀ {as = as} e) (trans (++-identityʳ _) (sUnitAxiom {as = _})) }
    ; unitᴸ = λ { {e , as} → cong₂ _,_ (Cell≡.eq unitᴸ) refl }
    ; assoc = λ { {x , as} {y , bs} {z , cs} →
      cong₂ _,_
        (begin (x ◦ d⁺ (as , y)) ◦ d⁺ (as ⊙⁺ y ++ bs , z) ≡⟨ cong ((x ◦ d⁺ (as , y)) ◦_) (sym (d⁺-assoc M {a = z} {x = as ⊙⁺ y} {y = bs})) ⟩
               (x ◦ (d⁺ (as , y))) ◦ d⁺ (as ⊙⁺ y , d⁺ (bs , z)) ≡⟨ sym μ-assoc.eq ⟩
               x ◦ (d⁺ (as , y)) ◦ d⁺ (as ⊙⁺ y , d⁺ (bs , z)) ≡⟨ cong (λ t → μ.α (x , t)) (sym (d⁺-nact as y (d⁺ (bs , z)))) ⟩
               x ◦ d⁺ (as , y ◦ d⁺ (bs , z)) ∎)
        (begin (as ⊙⁺ y ++ bs) ⊙⁺ z ++ cs
                 ≡⟨ cong (λ t → t ++ cs) (s∞-nactR {as = as ⊙⁺ y} {bs = bs} {x = z}) ⟩
               ((as ⊙⁺ y) ⊙⁺ d⁺ (bs , z) ++ bs ⊙⁺ z) ++ cs
                 ≡⟨ ++-assoc ((as ⊙⁺ y) ⊙⁺ d⁺ (bs , z)) (bs ⊙⁺ z) cs ⟩
               ((as ⊙⁺ y) ⊙⁺ d⁺ (bs , z)) ++ bs ⊙⁺ z ++ cs
                 ≡⟨ cong (λ t → t ++ (bs ⊙⁺ z ++ cs)) (⊙⁺-act {as = as} {x = d⁺ (bs , z)} {y = y}) ⟩
               (as ⊙⁺ μ.α (y , d⁺ (bs , z))) ++ bs ⊙⁺ z ++ cs ∎) }
    }

record DoubleMonadMap (M : DoubleMonad A) (N : DoubleMonad B) : Set (suc zero) where
  module M = DoubleMonad M
  module N = DoubleMonad N
  field
    U : Mealy A B
    Ω : Cell id id (U ⋄ M.M) (N.M ⋄ U)
    -- eqn
    μ-compat : Cell≡ ((M.μ ⊙ₕ idCell U) ⊙ᵥ Ω) ((assoc U M.M M.M ⊙ᵥ (idCell M.M ⊙ₕ Ω)) ⊙ᵥ ((assoc⁻¹ N.M U M.M ⊙ᵥ (Ω ⊙ₕ idCell N.M)) ⊙ᵥ (assoc N.M N.M U ⊙ᵥ (idCell U ⊙ₕ N.μ))))
    η-compat : Cell≡ (unitorᴸ U ⊙ᵥ ((M.η ⊙ₕ idCell U) ⊙ᵥ Ω)) (unitorᴿ⁻¹ U ⊙ᵥ (idCell U ⊙ₕ N.η))

record DoubleDistroLaw (M : DoubleMonad A) (N : DoubleMonad A) : Set (suc zero) where
  private
    module M = DoubleMonad M
    module N = DoubleMonad N
  field
    Ω : Cell id id (N.M ⋄ M.M) (M.M ⋄ N.M) -- intertwina

    ηM-compat : Cell≡ (unitorᴸ N.M ⊙ᵥ (M.η ⊙ₕ idCell N.M) ⊙ᵥ Ω) (unitorᴿ⁻¹ N.M ⊙ᵥ (idCell N.M ⊙ₕ M.η))
    ηN-compat : Cell≡ (unitorᴿ⁻¹ M.M ⊙ᵥ (idCell M.M ⊙ₕ N.η) ⊙ᵥ Ω) (unitorᴸ M.M ⊙ᵥ (N.η ⊙ₕ idCell M.M))

    μM-compat : Cell≡
      ((M.μ ⊙ₕ idCell N.M) ⊙ᵥ Ω)
      (assoc N.M M.M M.M ⊙ᵥ ((idCell M.M ⊙ₕ Ω) ⊙ᵥ ((assoc⁻¹ M.M N.M M.M ⊙ᵥ ((Ω ⊙ₕ idCell M.M) ⊙ᵥ assoc M.M M.M N.M)) ⊙ᵥ (idCell N.M ⊙ₕ M.μ))))
    μN-compat : Cell≡
      ((idCell M.M ⊙ₕ N.μ) ⊙ᵥ Ω)
      (assoc⁻¹ N.M N.M M.M ⊙ᵥ ((Ω ⊙ₕ idCell N.M) ⊙ᵥ ((assoc N.M M.M N.M ⊙ᵥ ((idCell N.M ⊙ₕ Ω) ⊙ᵥ assoc⁻¹ M.M N.M N.M)) ⊙ᵥ (N.μ ⊙ₕ idCell M.M))))
  module Ω = Cell Ω
  module ηM-compat = Cell≡ ηM-compat
  module ηN-compat = Cell≡ ηN-compat
  module μM-compat = Cell≡ μM-compat
  module μN-compat = Cell≡ μN-compat

module _ {M N : DoubleMonad A} (D : DoubleDistroLaw M N) where
  module M = DoubleMonad M
  module N = DoubleMonad N
  module DL = DoubleDistroLaw D
  module Nμ = Cell N.μ
  module Mμ = Cell M.μ
  module Nη = Cell N.η
  module Mη = Cell M.η

  QuagliaPapero : DoubleMonad A
  QuagliaPapero = record
    { M = M.M ⋄ N.M
    ; η = unitorᴸ idMealy ⊙ᵥ (N.η ⊙ₕ M.η)
    ; μ = assoc (M.M ⋄ N.M) M.M N.M
      ⊙ᵥ (idCell N.M ⊙ₕ assoc⁻¹ M.M N.M M.M)
      ⊙ᵥ (idCell N.M ⊙ₕ DL.Ω ⊙ₕ idCell M.M)
      ⊙ᵥ (idCell N.M ⊙ₕ assoc M.M M.M N.M)
      ⊙ᵥ assoc⁻¹ (M.M ⋄ M.M) N.M N.M
      ⊙ᵥ N.μ ⊙ₕ M.μ
    ; unitᴸ = record { eq = λ { {n , m} →
      begin Nμ.α (Nη.α tt , DL.Ω.α (Mη.α tt , n) .proj₁) ,
            Mμ.α (DL.Ω.α (Mη.α tt , n) .proj₂ , m)
              ≡⟨ cong₂ _,_ (cong (λ t → Nμ.α (Nη.α tt , t .proj₁)) (DL.ηM-compat.eq))
                           (cong (λ t → Mμ.α (t .proj₂ , m)) DL.ηM-compat.eq) ⟩
            Nμ.α (Nη.α tt , n) , Mμ.α (Mη.α tt , m)
              ≡⟨ cong₂ _,_ N.unitᴸ.eq M.unitᴸ.eq ⟩
            n , m ∎ } }
    ; unitᴿ =  record { eq = λ { {n , m} →
      begin Nμ.α (n , DL.Ω.α (m , Nη.α tt) .proj₁) ,
            Mμ.α (DL.Ω.α (m , Nη.α tt) .proj₂ , Mη.α tt)
              ≡⟨ cong₂ _,_ (cong (λ t → Nμ.α  (n , t .proj₁)) DL.ηN-compat.eq)
                           (cong (λ t → Mμ.α (t .proj₂ , Mη.α tt)) DL.ηN-compat.eq) ⟩
            Nμ.α (n , Nη.α tt) , Mμ.α (m , Mη.α tt)   ≡⟨ cong₂ _,_ N.unitᴿ.eq M.unitᴿ.eq ⟩
            n , m ∎ } }
    ; μ-assoc = record { eq = λ { {(n , m) , (n' , m') , (n'' , m'')} →
      let (e , r) =  DL.Ω.α (m' , n'') in
      let (e' , r') = DL.Ω.α (m , n') in
       begin Nμ.α (n , DL.Ω.α (m , Nμ.α (n' , e)) .proj₁) ,
             Mμ.α (DL.Ω.α (m , Nμ.α (n' , e)) .proj₂ , Mμ.α (r , m''))
               ≡⟨ cong₂ _,_ (cong (λ t → Nμ.α (_ , t)) (,-injectiveˡ DL.μN-compat.eq))
                            (cong (λ t → Mμ.α (t , Mμ.α (r , m''))) (,-injectiveʳ DL.μN-compat.eq)) ⟩
             Nμ.α (n , Nμ.α (e' , DL.Ω.α (r' , e) .proj₁)) ,
             Mμ.α (DL.Ω.α (r' , e) .proj₂ , Mμ.α (r , m'')) ≡⟨ cong₂ _,_ N.μ-assoc.eq M.μ-assoc.eq ⟩
             Nμ.α (Nμ.α (n , e') , DL.Ω.α (r' , e) .proj₁) ,
             Mμ.α (Mμ.α (DL.Ω.α (r' , e) .proj₂ , r) , m'')
               ≡⟨ cong₂ _,_ (cong (λ t → Nμ.α (Nμ.α (n , e') , t)) (sym (,-injectiveˡ DL.μM-compat.eq)))
                            (cong (λ t → Mμ.α (t , m'')) (sym (,-injectiveʳ DL.μM-compat.eq))) ⟩
             Nμ.α (Nμ.α (n , e') , DL.Ω.α (Mμ.α (r' , m') , n'') .proj₁) ,
               Mμ.α (DL.Ω.α (Mμ.α (r' , m') , n'') .proj₂ , m'') ∎
      } }
    }
