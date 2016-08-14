module Basics where

open import Relation.Binary.PropositionalEquality
open import Data.Nat using (ℕ ; zero ; suc)

infixr 1 _=>_
infixr 5 _∈_
infixl 1 _⊆_
infixl 4 _,_
infixl 3 _++_
infixl 2 _∧_

------------------------
-- Types and Contexts --
------------------------

data Types : Set where
  simple : Types
  modal : Types

data Ty : Types -> Set where
  P : ∀ {T} ->  ℕ -> Ty T
  _=>_ : ∀ {T} -> Ty T -> Ty T -> Ty T
  _∧_ : ∀ {T} -> Ty T -> Ty T -> Ty T
  □_ :  Ty modal -> Ty modal
  T : Ty simple

data Cx : Types -> Set where
  · : ∀ {T} -> Cx T
  _,_ : ∀ {T : Types} (Γ : Cx T) (A : Ty T) → Cx T

data _∈_ : ∀ {T : Types} (A : Ty T) (Γ : Cx T) -> Set where
  top : ∀ {T} {Γ : Cx T} {A : Ty T} → A ∈ (Γ , A)
  pop : ∀ {T} {Γ : Cx T} {A B : Ty T} (i : A ∈ Γ) -> A ∈ (Γ , B)

_⊆_ : ∀ {T} (Γ Δ : Cx T) -> Set
Γ ⊆ Δ = ∀ {A} -> A ∈ Γ -> A ∈ Δ
  
-- Functions on contexts.

boxcx : Cx modal -> Cx modal
boxcx · = ·
boxcx (Γ , A) = boxcx Γ , □ A

_++_ : ∀ {T} -> Cx T -> Cx T -> Cx T
Δ ++ · = Δ
Δ ++ (Γ , A) = (Δ ++ Γ) , A

leftid++ : ∀ {T} (Δ : Cx T) -> (· ++ Δ) ≡ Δ
leftid++ · = refl
leftid++ (Δ , A) = cong (λ Δ -> Δ , A) (leftid++ Δ)

box∈cx : ∀ {Γ : Cx modal} {A : Ty modal} -> A ∈ Γ -> □ A ∈ boxcx Γ
box∈cx top = top
box∈cx (pop d) = pop (box∈cx d)

subsetdef :  ∀ {T} {Γ Δ : Cx T} {A} -> A ∈ Γ -> Γ ⊆ Δ -> A ∈ Δ
subsetdef d f = f d

subsetempty : ∀ {T} {Γ : Cx T} -> · ⊆ Γ
subsetempty ()

subsetid : ∀ {T} {Γ : Cx T} -> Γ ⊆ Γ
subsetid = λ {Γ} {A} z → z

weakone : ∀ {T} {Γ Δ : Cx T} {A} -> Γ ⊆ Δ -> Γ ⊆ (Δ , A)
weakone p = λ {A} z → pop (p z)

weakboth : ∀ {T} {Γ Δ : Cx T} {A} -> Γ ⊆ Δ -> Γ , A ⊆ Δ , A
weakboth p top = top
weakboth p (pop x) = subsetdef x (weakone p)

weakmany : ∀ {T} (Γ Δ : Cx T) -> Γ ⊆ Γ ++ Δ
weakmany Γ · x = x
weakmany Γ (Δ , A) x = pop (weakmany Γ Δ x)


concat-subset-1 : ∀ {T} (Γ Δ : Cx T) -> Γ ⊆ Γ ++ Δ
concat-subset-1 Γ · x = x
concat-subset-1 Γ (Δ , A) x = subsetdef x (weakone (concat-subset-1 Γ Δ))

concat-subset-2 : ∀ {T} (Γ Δ : Cx T) -> Δ ⊆ Γ ++ Δ
concat-subset-2 Γ · ()
concat-subset-2 Γ (Δ , A) x = subsetdef x (weakboth (concat-subset-2 Γ Δ))

incl-trans : ∀ {T} {Γ Γ' Γ'' : Cx T} -> Γ ⊆ Γ' -> Γ' ⊆ Γ'' -> Γ ⊆ Γ''
incl-trans p q x = q (p x)

swap-last : ∀ {T} {Γ : Cx T} {A B} -> Γ , A , B ⊆ Γ , B , A
swap-last {_} {·} top = pop top
swap-last {_} {·} (pop top) = top
swap-last {_} {·} (pop (pop x)) = pop (pop x)
swap-last {_} {Γ , A} top = pop top
swap-last {_} {Γ , A} (pop top) = top
swap-last {_} {Γ , A} (pop (pop x)) = pop (pop x)

cx-exch : ∀ {T} {Γ Δ : Cx T} {A B} -> (Γ , A , B) ++ Δ ⊆ (Γ , B , A) ++ Δ
cx-exch {Δ = ·} d = swap-last d
cx-exch {Δ = Δ , A₁} top = top
cx-exch {Δ = Δ , A₁} (pop d) = subsetdef d (weakone (cx-exch {Δ = Δ}))

cx-contr : ∀ {T} {Γ Δ : Cx T} {A} -> (Γ , A , A) ++ Δ ⊆ (Γ , A) ++ Δ
cx-contr {Δ = ·} top = top
cx-contr {Δ = ·} (pop d) = d
cx-contr {Δ = Δ , A₁} top = top
cx-contr {Δ = Δ , A₁} (pop d) = subsetdef d (weakone (cx-contr {Δ = Δ}))

swap-out : ∀ {T} (Δ Γ : Cx T) (A : Ty T) -> (Δ , A) ++ Γ ⊆ (Δ ++ Γ) , A
swap-out Δ · A x = x
swap-out Δ (Γ , B) A x = swap-last (subsetdef x (weakboth (swap-out Δ Γ A)))


-- Translations

trans-ty : Ty modal -> Ty simple
trans-ty (P x) = P x
trans-ty (A => B) = trans-ty A => trans-ty B
trans-ty (A ∧ B) = trans-ty A ∧ trans-ty B
trans-ty (□ A) = T => trans-ty A

trans-cx : Cx modal -> Cx simple
trans-cx · = ·
trans-cx (Γ , A) = trans-cx Γ , trans-ty A

∈-trans-cx : ∀ {Γ : Cx modal} {A : Ty modal} -> A ∈ Γ -> trans-ty A ∈ trans-cx Γ
∈-trans-cx top = top
∈-trans-cx (pop d) = pop (∈-trans-cx d)

unitize-cx : Cx simple -> Cx simple
unitize-cx · = ·
unitize-cx (Γ , A) = unitize-cx Γ , (T => A)

∈-unitize-cx : ∀ {Γ A} -> A ∈ Γ -> (T => A) ∈ unitize-cx Γ
∈-unitize-cx top = top
∈-unitize-cx (pop p) = pop (∈-unitize-cx p) 
