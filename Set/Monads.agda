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

--thing : (M : MonadInMealy) →
  --(a : Algebra {X = S} M) →
  --(List A × E) × Mealy.E (Algebra.a a) → Mealy.E (Algebra.a a)
--thing a M ((as , e) , s) = Cell.α θ (s , {! MonadInMealy.d∞ as e !})
  --where open module a = Algebra M

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
  module μ-assoc = Cell≡ μ-assoc

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
{-
  module _ (U : Algebraᴿ DM) where
    open Algebraᴿ U

    module θ = Cell θ

    superchiappe : (as bs : List A) {x : Mealy.E a} {e e' : E} →
      θ.α (θ.α (x , d⁺ (as , e)) , d⁺ (bs , e')) ≡ θ.α (x , d⁺ (as ⊙⁺ e' ++ bs , μ.α (e , d⁺ (as , e'))))
    superchiappe [] [] {x = x} {e = e} {e' = e'} = Cell≡.eq θ-assoc {x = (x , e) , e'}
    superchiappe [] (b ∷ []) {x = x} {e = e} {e' = e'} = trans (Cell≡.eq θ-assoc) (cong (λ t → θ.α (x , t)) {! !})
    superchiappe [] (b ∷ (b' ∷ bs)) {x = x} {e = e} {e' = e'} = trans (Cell≡.eq θ-assoc) (cong (λ t → θ.α (x , t)) {! !})
    superchiappe (a ∷ as) [] {x = x} {e = e} {e' = e'} = {! !}
    superchiappe (a ∷ as) (b ∷ bs) = {! !}



    fattoide : bicrossedMonoid actsOnᴿ (Mealy.E a)
    fattoide = record
      { act = λ { x (e , as) → θ.α (x , d⁺ (as , e)) }
      ; unit = λ { {a} → Cell≡.eq θ-unit }
      ; assoc = λ { {a} {e , as} {e' , bs} → superchiappe as bs }
      }
-}

module _ (F : Mealy A A) where
  module F = Mealy F

  dd : A → List (Mealy.E F) → List (Mealy.E F)
  dd a = map (λ e → F.d (a , e))

  ss : A → List (Mealy.E F) → A
  ss a = foldr (flip (curry F.s)) a ∘ reverse

  extension : (F : Mealy A A) → Mealy A A
  extension F = record
    { E = List F.E
    ; d = uncurry dd
    ; s = uncurry ss
    }

  fattoideCruciale : (F : Mealy A A) → DoubleMonad A
  fattoideCruciale F = record
    { M = extension F
    ; η = record
      { α = λ { x → [] }
      ; com-s = λ { {a} {tt} → refl }
      ; com-d = λ { {a} {tt} → refl }
      }
    ; μ = record
      { α = λ { (xs , ys) → xs ++ ys }
      ; com-s = λ { {a} {xs , es} → begin
          foldr (flip (curry F.s)) a
            (reverse (xs ++ es))
            ≡⟨ cong (foldr (flip (curry F.s)) a) (reverse-++ xs es) ⟩
          foldr (flip (curry F.s)) a (reverse es ++ reverse xs)
            ≡⟨ foldr-++ (flip (curry F.s)) a (reverse es) (reverse xs) ⟩
          foldr (flip (curry F.s))
               (foldr (flip (curry F.s)) a (reverse xs))
               (reverse es) ∎ } -- ""
      ; com-d = λ { {a} {xs , es} → begin
         map (λ e → F.d (a , e)) (xs ++ es) ≡⟨ map-++ _ xs es ⟩
         map (λ e → F.d (a , e)) xs ++ map (λ e → F.d (a , e)) es
           ≡⟨ cong (map (λ e → F.d (a , e)) xs ++_)
             {!   !} ⟩
         {!   !} ≡⟨ {!   !} ⟩
         map (λ e → F.d (a , e)) xs
          ++ map {!  !} es ∎ } -- ""
      }
    ; unitᴸ = record { eq = refl }
    ; unitᴿ = record { eq = ++-identityʳ _ }
    ; μ-assoc = record { eq = λ { {xs , ys , zs} → sym (++-assoc xs ys zs) } }
    }


{-
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
  module M = DoubleMonad M
  module N = DoubleMonad N
  field
    Ω : Cell id id (N.M ⋄ M.M) (M.M ⋄ N.M) -- intertwina
    -- eqn
    --μ-compat : Cell≡ ((M.μ ⊙ₕ idCell U) ⊙ᵥ Ω) ((assoc U M.M M.M ⊙ᵥ (idCell M.M ⊙ₕ Ω)) ⊙ᵥ ((assoc⁻¹ N.M U M.M ⊙ᵥ (Ω ⊙ₕ idCell N.M)) ⊙ᵥ (assoc N.M N.M U ⊙ᵥ (idCell U ⊙ₕ N.μ))))
    ηM-compat : Cell≡ (unitorᴸ N.M ⊙ᵥ ((M.η ⊙ₕ idCell N.M) ⊙ᵥ Ω)) (unitorᴿ⁻¹ N.M ⊙ᵥ (idCell N.M ⊙ₕ M.η))
    ηN-compat : Cell≡ (unitorᴿ⁻¹ M.M ⊙ᵥ ((idCell M.M ⊙ₕ N.η) ⊙ᵥ Ω)) (unitorᴸ M.M ⊙ᵥ (N.η ⊙ₕ idCell M.M))
    μM-compat : Cell≡
      ((M.μ ⊙ₕ idCell N.M) ⊙ᵥ Ω)
      (assoc N.M M.M M.M ⊙ᵥ ((idCell M.M ⊙ₕ Ω) ⊙ᵥ ((assoc⁻¹ M.M N.M M.M ⊙ᵥ ((Ω ⊙ₕ idCell M.M) ⊙ᵥ assoc M.M M.M N.M)) ⊙ᵥ (idCell N.M ⊙ₕ M.μ))))
    μN-compat : Cell≡
      ((idCell M.M ⊙ₕ N.μ) ⊙ᵥ Ω)
      (assoc⁻¹ N.M N.M M.M ⊙ᵥ ((Ω ⊙ₕ idCell N.M) ⊙ᵥ ((assoc N.M M.M N.M ⊙ᵥ ((idCell N.M ⊙ₕ Ω) ⊙ᵥ assoc⁻¹ M.M N.M N.M)) ⊙ᵥ (N.μ ⊙ₕ idCell M.M))))

{-
coalesce : {E : Set} → (f : A × E → E × B) → Mealy A B
coalesce {E = E} f = record
  { E = E
  ; d = proj₁ ∘ f
  ; s = proj₂ ∘ f
  }



fleshoutMonadMap : (M : DoubleMonad A) (N : DoubleMonad B) (U : Mealy A B) →
  (g : Σ (Mealy.E (DoubleMonad.M M)) (λ x → Mealy.E U) → Σ (Mealy.E U) (λ x → Mealy.E (DoubleMonad.M N))) →
  DoubleMonadMap M N
fleshoutMonadMap M N U g = record
  { U = U
  ; Ω = record
    { α = g -- works E × X → X × E' if E = carrier of M, E' = carrier of N, X = carrier of U
    -- is a Mealy E --> It 'between the carriers of the monads, with X as state space
    -- δ : E × X → X and σ : E × X → E'
    -- through U, List A acts on X
    -- through g, List |E| (E is already a monoid, via M) acts on X
    -- through M, there exists a bicrossed E ⋈ List A
    -- through N, there exists a bicrossed E' ⋈ List B
    --
    ; com-s = λ { {a} {e , x} → {!  !} }
      -- N.s (U.s (a , δ (e , x)) , σ (e , x)) ≡ U.s (M.s (a , e) , x)
    ; com-d = λ { {a} {e , x} → {!  !} }
      -- (U.d (a , δ (e , x)) , N.d (U.s (a , δ (e , x)) , σ (e , x))) ≡ g (M.d (a , e) , U.d (M.s (a , e) , x))
      -- translates into two separate eqns:
      -- δ (M.d (a , e) , U.d (M.s (a , e) , x)) ≡ U.d (a , δ (e , x))
      -- σ (M.d (a , e) , U.d (M.s (a , e) , x)) ≡ N.d (U.s (a , δ (e , x)) , σ (e , x)))
    }
  ; μ-compat = record { eq = λ { {(e1 , e2) , x} → {!  !} } }
    -- g (M.μ (e1 , e2) , x) ≡ (δ (e1 , δ (e2 , x)) , N.μ (σ (e1 , δ (e2 , x)) , σ (e2 , x)))
    -- translates into two separate eqns:
    --
    -- δ (M.μ (e1 , e2) , x) ≡ δ (e1 , δ (e2 , x))
    -- action axiom: E agisce su X
    --
    -- σ (M.μ (e1 , e2) , x) ≡ N.μ (σ (e1 , δ (e2 , x)) , σ (e2 , x))
    -- (e1 ∙ e2) ⊙ₘ x ≡ (σ (e1 , e2 ⊗ x)) ∙ (σ (e2 , x))
    -- fugality
  ; η-compat = record { eq = λ { {x} → {!  !} } }
    -- δ (e₀ , x) ≡ x (identity of the monoid M)
    -- σ (e₀ , x) ≡ e₀' (identity of the monoid N)
  } where module M = Mealy (DoubleMonad.M M)
          module N = Mealy (DoubleMonad.M N)
          module U = Mealy U

fleshoutDL : (M N : DoubleMonad A) (g : Mealy.E (DoubleMonad.M M) × Mealy.E (DoubleMonad.M N) → Mealy.E (DoubleMonad.M N) × Mealy.E (DoubleMonad.M M)) → DoubleDistroLaw M N
fleshoutDL M N g = record
  { Ω = record
    { α = g
    ; com-s = λ { {a} {m , n} → {!  !} } -- M.s (N.s (a , g (m , n) .proj₁) , g (m , n) .proj₂) ≡ N.s (M.s (a , m) , n)
    ; com-d = λ { {a} {m , n} → {!  !} } -- (N.d (a , g (m , n) .proj₁) , M.d (N.s (a , g (m , n) .proj₁) , g (m , n) .proj₂)) ≡ g (M.d (a , m) , N.d (M.s (a , m) , n))
    }
  ; ηM-compat = record { eq = λ { {n} → {!  !} } }
  ; ηN-compat = record { eq = λ { {m} → {!  !} } }
  ; μM-compat = record { eq = λ { {(m , m') , n} → {!  !} } }
  ; μN-compat = record { eq = λ { {m , n , n'} → {!  !} } }
  } where module M = Mealy (DoubleMonad.M M)
          module N = Mealy (DoubleMonad.M N)
          module 𝕄 = DoubleMonad M
          module ℕ = DoubleMonad N

-}

open DoubleDistroLaw

QuagliaPapero : {M : DoubleMonad A} {N : DoubleMonad A} → DoubleDistroLaw M N → DoubleMonad A
QuagliaPapero {M = M} {N = N} DL = record
  { M = 𝕄.M ⋄ ℕ.M
  ; η = unitorᴸ idMealy ⊙ᵥ (ℕ.η ⊙ₕ 𝕄.η)
  ; μ = ((assoc (DL.M.M ⋄ DL.N.M) DL.M.M DL.N.M ⊙ᵥ (idCell DL.N.M ⊙ₕ assoc⁻¹ DL.M.M DL.N.M DL.M.M)) ⊙ᵥ ((idCell ℕ.M ⊙ₕ (DL.Ω ⊙ₕ idCell 𝕄.M)) ⊙ᵥ ((idCell DL.N.M ⊙ₕ assoc DL.M.M DL.M.M DL.N.M) ⊙ᵥ assoc⁻¹ (DL.M.M ⋄ DL.M.M) DL.N.M DL.N.M))) ⊙ᵥ (ℕ.μ ⊙ₕ 𝕄.μ)
  ; unitᴸ = record { eq = λ { {n , m} → cong₂ _,_
      (begin {!  !} ≡⟨ cong (λ t → Cell.α DL.N.μ (Cell.α DL.N.η tt , t .proj₁)) (Cell≡.eq DL.ηM-compat) ⟩
            {!  !} ≡⟨ Cell≡.eq ℕ.unitᴸ ⟩
            {!  !} ∎)
      (begin {!  !} ≡⟨ cong (λ t → Cell.α DL.M.μ (t .proj₂ , m)) (Cell≡.eq DL.ηM-compat) ⟩
            {!  !} ≡⟨ Cell≡.eq 𝕄.unitᴸ ⟩
            {!  !} ∎)
    } }
  ; unitᴿ = record { eq = λ { {n , m} → cong₂ _,_
    (begin {!  !} ≡⟨ cong (λ t → Cell.α DL.N.μ (n , t .proj₁)) (Cell≡.eq DL.ηN-compat) ⟩
           {!  !} ≡⟨ Cell≡.eq ℕ.unitᴿ ⟩
           {!  !} ∎)
    (begin {!  !} ≡⟨ cong (λ t → Cell.α DL.M.μ (t .proj₂ , Cell.α DL.M.η tt)) (Cell≡.eq DL.ηN-compat) ⟩
           {!  !} ≡⟨ Cell≡.eq 𝕄.unitᴿ ⟩
           {!  !} ∎)
    } }
  ; μ-assoc = record { eq = λ { {(n , m) , (n' , m') , (n'' , m'')} → {!  !} } }
  } where module MM = Mealy (DoubleMonad.M M)
          module NN = Mealy (DoubleMonad.M N)
          module 𝕄 = DoubleMonad M
          module ℕ = DoubleMonad N
          open module DL = DoubleDistroLaw DL
-}
