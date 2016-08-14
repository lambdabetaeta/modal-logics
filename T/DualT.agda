module T.DualT where

infixl 0 _/_⊢_

open import Basics
open import Relation.Binary.PropositionalEquality

-- Definition

data _/_⊢_ (Δ Γ : Cx modal) :  Ty modal -> Set where

  DT-var : ∀ {A}
  
     -> A ∈ Γ
    -------------
    -> Δ / Γ ⊢ A

  DT-modal-var : ∀ {A}
  
     -> A ∈ Δ
    ------------
    -> Δ / Γ ⊢ A
               
  DT-app : ∀ {A B}
  
    -> Δ / Γ ⊢ A => B    -> Δ / Γ ⊢ A
    ---------------------------------
          -> Δ / Γ ⊢ B
                          
  DT-lam : ∀ {A B}
  
     -> Δ / (Γ , A) ⊢ B
     ------------------
     -> Δ / Γ ⊢ A => B
               
  DT-prod : ∀ {A B}
  
    -> Δ / Γ ⊢ A    -> Δ / Γ ⊢ B
    ----------------------------
       -> Δ / Γ ⊢ A ∧ B
                     
  DT-fst : ∀ {A B}
  
    -> Δ / Γ ⊢ A ∧ B
    -----------------
      -> Δ / Γ ⊢ A
                 
  DT-snd : ∀ {A B}
  
    -> Δ / Γ ⊢ A ∧ B
    ----------------
      -> Δ / Γ ⊢ B
                 
  DT-boxI : ∀ {A}
  
     -> · / Δ ⊢ A
    ---------------
    -> Δ / Γ ⊢ □ A
               
  DT-boxE : ∀ {A C}
  
    -> Δ / Γ ⊢ □ A    -> (Δ , A) / Γ ⊢ C
    ------------------------------------
              -> Δ / Γ ⊢ C


-- Weakening and exchange.


exch : ∀ {Δ Γ A B C} (Γ' : Cx modal)

  -> Δ / (Γ , A , B) ++ Γ' ⊢ C
  -----------------------------
  -> Δ / (Γ , B , A) ++ Γ' ⊢ C

exch Γ' (DT-var x) = DT-var (cx-exch {Δ = Γ'} x)
exch Γ' (DT-modal-var x) = DT-modal-var x
exch Γ' (DT-app d d₁) = DT-app (exch Γ' d) (exch Γ' d₁)
exch {C = A => B} Γ' (DT-lam d) = DT-lam (exch (Γ' , A) d)
exch Γ' (DT-prod d d₁) = DT-prod (exch Γ' d) (exch Γ' d₁)
exch Γ' (DT-fst d) = DT-fst (exch Γ' d)
exch Γ' (DT-snd d) = DT-snd (exch Γ' d)
exch Γ' (DT-boxI d) = DT-boxI d
exch Γ' (DT-boxE d d₁) = DT-boxE (exch Γ' d) (exch Γ' d₁)


exch-modal : ∀ {Δ Γ A B C} (Δ' : Cx modal)

  -> (Δ , A , B) ++ Δ' / Γ ⊢ C
  -----------------------------
  -> (Δ , B , A) ++ Δ' / Γ ⊢ C
                    
exch-modal Δ' (DT-var x) = DT-var x
exch-modal Δ' (DT-modal-var x) =
  DT-modal-var (subsetdef x (cx-exch {Δ = Δ'}))
exch-modal Δ' (DT-app d e) =
  DT-app (exch-modal Δ' d) (exch-modal Δ' e)
exch-modal Δ' (DT-lam d) = DT-lam (exch-modal Δ' d)
exch-modal Δ' (DT-prod d e) =
  DT-prod (exch-modal Δ' d) (exch-modal Δ' e)
exch-modal Δ' (DT-fst d) = DT-fst (exch-modal Δ' d)
exch-modal Δ' (DT-snd d) = DT-snd (exch-modal Δ' d)
exch-modal Δ' (DT-boxI d) = DT-boxI (exch Δ' d)
exch-modal Δ' (DT-boxE d e) =
  DT-boxE (exch-modal Δ' d) (exch-modal (Δ' , _) e)


weak : ∀ {Δ Γ Γ' A}

    -> Δ / Γ ⊢ A    -> Γ ⊆ Γ'
    -------------------------
        -> (Δ / Γ' ⊢ A)

weak (DT-var x) f = DT-var (f x)
weak (DT-modal-var x) f = DT-modal-var x
weak (DT-app d e) f = DT-app (weak d f) (weak e f)
weak (DT-lam d) f = DT-lam (weak d (weakboth f))
weak (DT-prod d e) f = DT-prod (weak d f) (weak e f)
weak (DT-fst d) f = DT-fst (weak d f)
weak (DT-snd d) f = DT-snd (weak d f)
weak (DT-boxI d) f = DT-boxI d
weak (DT-boxE d e) f =
  DT-boxE (weak d f) (weak e f)


weak-modal : ∀ {Δ Δ' Γ A}

 -> Δ / Γ ⊢ A    -> Δ ⊆ Δ'
 -------------------------
      -> Δ' / Γ ⊢ A

weak-modal (DT-var p) x = DT-var p
weak-modal (DT-modal-var p) x = DT-modal-var (x p)
weak-modal (DT-app t u) x = DT-app (weak-modal t x)
                                     (weak-modal u x)
weak-modal (DT-lam t) x = DT-lam (weak-modal t x)
weak-modal (DT-prod t u) x = DT-prod (weak-modal t x)
                                       (weak-modal u x)
weak-modal (DT-fst t) x = DT-fst (weak-modal t x)
weak-modal (DT-snd t) x = DT-snd (weak-modal t x)
weak-modal (DT-boxI t) x = DT-boxI (weak t x)
weak-modal (DT-boxE t u) x =
  DT-boxE (weak-modal t x)
           (weak-modal u (weakboth x))


-- Cut.

cut : ∀ {Δ Γ A B} -> (Γ' : Cx modal)

  -> Δ / Γ ⊢ A    -> Δ / Γ , A ++ Γ' ⊢ B
  ---------------------------------------
            -> Δ / Γ ++ Γ' ⊢ B

cut · d (DT-var top) = d
cut · d (DT-var (pop x)) = DT-var x
cut (Γ' , B) d (DT-var top) = DT-var top
cut (Γ' , A') d (DT-var (pop x)) =
  weak (cut Γ' d (DT-var x)) (weakone subsetid)
cut Γ' d (DT-modal-var p) = DT-modal-var p
cut Γ' d (DT-app t u) = DT-app (cut Γ' d t) (cut Γ' d u)
cut Γ' d (DT-lam e) = DT-lam (cut (Γ' , _) d e)
cut Γ' d (DT-prod t u) = DT-prod (cut Γ' d t) (cut Γ' d u)
cut Γ' d (DT-fst e) = DT-fst (cut Γ' d e)
cut Γ' d (DT-snd e) = DT-snd (cut Γ' d e)
cut Γ' d (DT-boxI e) = DT-boxI e
cut Γ' d (DT-boxE t u) =
  DT-boxE (cut Γ' d t)
           (cut Γ' (weak-modal d (weakone (subsetid ))) u)


ruleT :  ∀ {Δ Γ A}  -> (Δ' : Cx modal)

  -> Δ' / Δ ++ Γ ⊢ A
  ------------------
  -> Δ' ++ Δ / Γ ⊢ A

ruleT {Γ = ·} Δ' (DT-var x) = DT-modal-var (concat-subset-2 _ _ x)
ruleT {Γ = Γ , A} Δ' (DT-var top) = DT-var top
ruleT {Γ = Γ , B} Δ' (DT-var (pop x)) =
  weak (ruleT {Γ = Γ} Δ' (DT-var x)) (weakone subsetid)
ruleT {Δ} Δ' (DT-modal-var x) = DT-modal-var (concat-subset-1 Δ' Δ x)
ruleT Δ' (DT-app p q) = DT-app (ruleT Δ' p) (ruleT Δ' q)
ruleT {Δ} {Γ} {A => B} Δ' (DT-lam p) = DT-lam (ruleT Δ' p)
ruleT Δ' (DT-prod p q) = DT-prod (ruleT Δ' p) (ruleT Δ' q)
ruleT Δ' (DT-fst p) = DT-fst (ruleT Δ' p)
ruleT Δ' (DT-snd p) = DT-snd (ruleT Δ' p)
ruleT {Δ} Δ' (DT-boxI p) = DT-boxI (weak p (concat-subset-1 Δ' Δ))
ruleT {Δ} Δ' (DT-boxE p q) =
  DT-boxE (ruleT _ p) (weak-modal (ruleT _ q) (swap-out Δ' Δ _))


cut-modal : ∀ {Δ Γ A B} -> (Δ' : Cx modal)

  -> · / Δ ⊢ A    -> Δ , A ++ Δ' / Γ  ⊢ B
  ---------------------------------------
           -> Δ ++ Δ' / Γ ⊢ B

cut-modal Δ' d (DT-var x) = DT-var x
cut-modal {B = B} · d (DT-modal-var top) =
  let p = ruleT · d in
  let q = subst (λ Δ -> Δ / · ⊢ B) (leftid++ _) p in
    weak q subsetempty
cut-modal · d (DT-modal-var (pop x)) = DT-modal-var x
cut-modal (Δ' , B) d (DT-modal-var top) = DT-modal-var top
cut-modal (Δ' , A') d (DT-modal-var (pop x)) =
  weak-modal (cut-modal Δ' d (DT-modal-var x)) (weakone subsetid)
cut-modal Δ' d (DT-app p q) =
  DT-app (cut-modal Δ' d p) (cut-modal Δ' d q)
cut-modal Δ' d (DT-lam e) = DT-lam (cut-modal Δ' d e)
cut-modal Δ' d (DT-prod p q) =
  DT-prod (cut-modal Δ' d p) (cut-modal Δ' d q)
cut-modal Δ' d (DT-fst e) = DT-fst (cut-modal Δ' d e)
cut-modal Δ' d (DT-snd e) = DT-snd (cut-modal Δ' d e)
cut-modal Δ' d (DT-boxI e) = DT-boxI (cut Δ' d e)
cut-modal Δ' d (DT-boxE p q) =
  DT-boxE (cut-modal Δ' d p) (cut-modal (Δ' , _) d q)
