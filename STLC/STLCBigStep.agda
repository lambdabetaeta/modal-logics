module STLC.STLCBigStep where

open import Agda.Builtin.Unit public using (⊤; tt)
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to pair)
open import Basics
open import STLC.STLC

-- Big Step Normalisation

get-right-val : ∀ {Γ Θ A} -> (A ∈ Θ) -> (Γ ⊩ Θ) -> Val Γ A
get-right-val top (smth q x) = x
get-right-val (pop p) (smth q x) = get-right-val p q

-- E ⊢ M ⇓ v is to be read as "in environment E, M evaluates to whnf (val) v."

mutual

  data _⊢_⇓_ : ∀ {Θ Γ A} -> (Γ ⊩ Θ) -> (Θ ⊢ A) -> (Val Γ A) -> Set where


    whnf-var : ∀ {Γ Θ A} {E : Γ ⊩ Θ}
                                   -> (p : A ∈ Θ)
                   ------------------------------------------
                      ->  E ⊢ (STLC-var p) ⇓ (get-right-val p E)


    whnf-lam : ∀ {Γ Θ A B} {m : Θ , A ⊢ B}  {E :  Γ ⊩ Θ}

                   -----------------------------------------------------
                      ->  E ⊢ (STLC-lam  m) ⇓ (STLC-val-lam E m)

    whnf-app : ∀ {Θ Γ A B} {E : Γ ⊩ Θ} {m : Θ ⊢ A => B} {n : Θ ⊢ A}
                                 {f : Val Γ (A => B)} {x : Val Γ A} {v}

                     -> E ⊢ m ⇓ f    -> E ⊢ n ⇓ x     -> f $ x >> v
                   ------------------------------------------------------
                                -> E ⊢ (STLC-app m n) ⇓ v

    whnf-prod1 : ∀ {Γ Θ A B}  {E : Γ ⊩ Θ}
                   {m : Θ ⊢ A} {n : Θ ⊢ B}

                   -----------------------------------------------
                    -> E ⊢ (STLC-prod1 m n) ⇓ (STLC-val-prod1 E m n)

    whnf-prod2 : ∀ {Γ Θ A B} {m : Θ ⊢ A ∧ B} {E : Γ ⊩ Θ} {v w}

                     ->  E ⊢ m ⇓ v      -> fst v >> w
                   -----------------------------------
                     -> E ⊢ (STLC-prod2 m) ⇓ w


    whnf-prod3 : ∀ {Γ Θ A B} {m : Θ ⊢ A ∧ B} {E : Γ ⊩ Θ} {v w}

                      -> E ⊢ m ⇓ v      -> snd v >> w     
                   ------------------------------------
                        -> E ⊢ (STLC-prod3 m) ⇓ w

    whnf-unit : ∀ {Γ Θ}  {E : Γ ⊩ Θ} ->
                   ------------------------------------
                           E ⊢ (STLC-unit) ⇓ (STLC-val-unit)


  -- Dealing with arrow elimination.
  
  data _$_>>_ {Γ A B} :  Val Γ (A => B) -> Val Γ A -> Val Γ B -> Set where

    eval-app-ne : ∀ {m v} ->  STLC-val-ne m $ v >> (STLC-val-ne (STLC-ne-app m v))

    eval-app-lam : ∀ {Θ} {E : Γ ⊩ Θ} {m v w} -> (smth E v) ⊢ m ⇓ w -> (STLC-val-lam E m) $ v >> w


  _$_ : ∀ {Γ A B v} -> (f : Val Γ (A => B)) -> (x : Val Γ A) -> (f $ x >> v) -> Σ (Val Γ B) (λ w -> w ≡ v)

  (STLC-val-ne m $ v) eval-app-ne = pair (STLC-val-ne (STLC-ne-app m v)) refl
  (STLC-val-lam E t $ v) (eval-app-lam p) = pair _ refl

  -- Dealing with first projection.
  
  data fst_>>_ {Γ A B} :  Val Γ (A ∧ B) -> Val Γ A -> Set where

    eval-fst-ne : ∀ {x} -> fst (STLC-val-ne x) >> (STLC-val-ne (STLC-ne-prod2 x))
    eval-fst-prod1 : ∀ {Θ} {E : Γ ⊩ Θ} {a b v} -> E ⊢ a ⇓ v -> fst (STLC-val-prod1 E a b) >> v

  fst-val-str : ∀ {Γ A B v} -> (x : Val Γ (A ∧ B)) -> (p : fst x >> v) -> Σ (Val Γ A) (λ w -> w ≡ v)

  fst-val-str (STLC-val-ne x) eval-fst-ne = pair (STLC-val-ne (STLC-ne-prod2 x)) refl
  fst-val-str (STLC-val-prod1 E m n) (eval-fst-prod1 p) = eval-str E m p

  -- Dealing with second projection.

  data snd_>>_ {Γ A B} : Val Γ (A ∧ B) -> Val Γ B -> Set where

    eval-snd-ne : ∀ {x} -> snd (STLC-val-ne x) >> (STLC-val-ne (STLC-ne-prod3 x))
    eval-snd-prod1 : ∀ {Θ} {E : Γ ⊩ Θ} {a b v} -> E ⊢ b ⇓ v -> snd (STLC-val-prod1 E a b) >> v

  snd-val-str : ∀ {Γ A B v} -> (x : Val Γ (A ∧ B)) -> (p : snd x >> v) -> Σ (Val Γ B) (λ w -> w ≡ v)
  snd-val-str (STLC-val-ne x) eval-snd-ne = pair (STLC-val-ne (STLC-ne-prod3 x)) refl
  snd-val-str (STLC-val-prod1 E m n) (eval-snd-prod1 p) = eval-str E n p


  -- Evaluating to whnf.

  eval-str : ∀ {Γ Θ A v} -> (E : Γ ⊩ Θ)
         -> (t : Θ ⊢ A) ->  E ⊢ t ⇓ v -> Σ (Val Γ A) (λ w -> w ≡ v)

  eval-str E (STLC-var p) (whnf-var .p) = pair (get-right-val p E) refl
  eval-str E (STLC-app t u) (whnf-app p q r) with (eval-str E t p) | (eval-str E u q)
  eval-str E (STLC-app t u) (whnf-app p q r)     | pair f refl | pair x refl = (f $ x) r
  eval-str E (STLC-lam m) whnf-lam = pair (STLC-val-lam E m) refl
  eval-str E (STLC-prod1 m n) whnf-prod1 = pair (STLC-val-prod1 E m n) refl
  eval-str E (STLC-prod2 t) (whnf-prod2 p x) with (eval-str E t p)
  eval-str E (STLC-prod2 t) (whnf-prod2 p x)    | pair v refl = fst-val-str v x
  eval-str E (STLC-prod3 t) (whnf-prod3 p x) with (eval-str E t p)
  eval-str E (STLC-prod3 t) (whnf-prod3 p x)    | pair v refl = snd-val-str v x
  eval-str E (STLC-unit) (whnf-unit) = pair STLC-val-unit refl

  -- v ↓ w is to be read "whnf v evaluates to nf w"

  data _↓_  {Γ} : ∀ {A} -> (Val Γ A) -> (Nf Γ A) -> Set where

    nf-ne : ∀ {A v} {m : Ne Γ Val A}
                              -> m ↓ne v
               -------------------------------------
                  -> (STLC-val-ne m) ↓ (STLC-nf-ne v)

    nf-lam : ∀ {A B v w} {f : Val Γ (A => B)}
    
               -> (val-weak-many-right f (weakone (subsetid _))) $ (STLC-val-ne (STLC-ne-var top)) >> v   -> v ↓ w
               -------------------------------------------------------------------
                                -> f ↓ (STLC-nf-lam w)

    nf-prod1 : ∀ {A B v' w'}
                 {m : Val Γ (A ∧ B)}
                 {v : Val Γ A} {w : Val Γ B}
    
                -> fst m >> v   -> snd m >> w   -> v ↓ v'   -> w ↓ w'
               -------------------------------------------------------
                            -> m ↓ (STLC-nf-prod1 v' w')

    nf-unit : STLC-val-unit ↓ STLC-nf-unit


  data _↓ne_  {Γ} : ∀ {A} -> (Ne Γ Val A) -> (Ne Γ Nf A) -> Set where
  
      nf-var : ∀ {A} {x : A ∈ Γ}
      
               -------------------------------------
                  -> (STLC-ne-var x) ↓ne (STLC-ne-var x)

      nf-app : ∀ {A B} {t : Ne Γ Val (A => B)}
                       {v : Ne Γ Nf (A => B)}
                       {u : Val Γ A}
                       {w : Nf Γ A}
      
                  -> t ↓ne v              -> u ↓ w
               -------------------------------------------
                  -> (STLC-ne-app t u) ↓ne (STLC-ne-app v w)
                  
      nf-prod2 : ∀ {A B} {t : Ne Γ Val (A ∧ B)}
                         {v : Ne Γ Nf (A ∧ B)}
      
                                -> t ↓ne v
               -------------------------------------------
                  -> (STLC-ne-prod2 t) ↓ne (STLC-ne-prod2 v)

      nf-prod3 : ∀ {A B} {t : Ne Γ Val (A ∧ B)}
                         {v : Ne Γ Nf (A ∧ B)}
      
                                -> t ↓ne v
               -------------------------------------------
                  -> (STLC-ne-prod3 t) ↓ne (STLC-ne-prod3 v)


  quote-str : ∀ {Γ A w} -> (v : Val Γ A) -> v ↓ w -> Σ (Nf Γ A) (λ w' -> w ≡ w')

  quote-str (STLC-val-ne x) (nf-ne y) = pair (STLC-nf-ne _) refl
  quote-str (STLC-val-ne x) (nf-lam p q) = pair (STLC-nf-lam _) refl
  quote-str (STLC-val-ne x) (nf-prod1 p q r s) = pair (STLC-nf-prod1 _ _) refl
  quote-str (STLC-val-lam E t) (nf-lam p q) = pair (STLC-nf-lam _) refl
  quote-str (STLC-val-prod1 E t u) (nf-prod1 p q r s) = pair (STLC-nf-prod1 _ _) refl
  quote-str STLC-val-unit nf-unit = pair STLC-nf-unit refl

  quote-ne-str : ∀ {Γ A w} -> (v : Ne Γ Val A)
                 -> v ↓ne w -> Σ (Ne Γ Nf A) (λ w' -> w ≡ w')

  quote-ne-str (STLC-ne-var x) nf-var = pair (STLC-ne-var x) refl
  quote-ne-str (STLC-ne-app t u) (nf-app p x) = pair (STLC-ne-app _ _) refl
  quote-ne-str (STLC-ne-prod2 t) (nf-prod2 p) = pair (STLC-ne-prod2 _) refl
  quote-ne-str (STLC-ne-prod3 t) (nf-prod3 p) = pair (STLC-ne-prod3 _) refl



nf-to-val : ∀ {Γ A} -> (Nf Γ A) -> (Val Γ A)
nf-to-term : ∀ {Γ A} -> (Nf Γ A) -> (Γ ⊢ A)
ne-nf-to-val-nf : ∀ {Γ A} -> (Ne Γ Nf A) -> (Ne Γ Val A)
ne-nf-to-term :  ∀ {Γ A} -> (Ne Γ Nf A) -> (Γ ⊢ A)

nf-to-val (STLC-nf-ne x) = STLC-val-ne (ne-nf-to-val-nf x)
nf-to-val (STLC-nf-lam t) = STLC-val-lam (id-ctxt _) (nf-to-term t)
nf-to-val (STLC-nf-prod1 t u) = STLC-val-prod1 (id-ctxt _) (nf-to-term t) (nf-to-term u)
nf-to-val STLC-nf-unit = STLC-val-unit

nf-to-term (STLC-nf-ne p) = ne-nf-to-term p
nf-to-term (STLC-nf-lam t) = STLC-lam (nf-to-term t)
nf-to-term (STLC-nf-prod1 t u) = STLC-prod1 (nf-to-term t) (nf-to-term u)
nf-to-term STLC-nf-unit = STLC-unit

ne-nf-to-val-nf (STLC-ne-var p) = STLC-ne-var p
ne-nf-to-val-nf (STLC-ne-app t u) = STLC-ne-app (ne-nf-to-val-nf t) (nf-to-val u)
ne-nf-to-val-nf (STLC-ne-prod2 t) = STLC-ne-prod2 (ne-nf-to-val-nf t)
ne-nf-to-val-nf (STLC-ne-prod3 t) = STLC-ne-prod3 (ne-nf-to-val-nf t)

ne-nf-to-term (STLC-ne-var p) = STLC-var p
ne-nf-to-term (STLC-ne-app t u) = STLC-app (ne-nf-to-term t) (nf-to-term u)
ne-nf-to-term (STLC-ne-prod2 t) = STLC-prod2 (ne-nf-to-term t)
ne-nf-to-term (STLC-ne-prod3 t) = STLC-prod3 (ne-nf-to-term t)


SCV : ∀ (Γ : Cx simple) -> (A : Ty simple) -> Val Γ A -> Set

SCV Γ (P i) v = Σ (Nf Γ (P i)) (λ w -> v ↓ w)
SCV Γ (A => B) f =
  ∀ {Γ'} {v : Val (Γ ++ Γ') A}
  -> SCV (Γ ++ Γ') A v
  -> Σ (Val (Γ ++ Γ') B)
       (λ w -> (val-weak-many-right f (concat-subset-1 Γ Γ') $ v >> w) × SCV (Γ ++ Γ') B w)
SCV Γ (A ∧ B) v = Σ (Val Γ A) (λ w -> Σ (Val Γ B) (λ z -> (SCV Γ A w) × (SCV Γ B z) × (fst v >> w) × (snd v >> z)))
SCV Γ T v = Σ (Nf Γ T) (λ w -> v ↓ w)

SCE : ∀ (Γ Θ : Cx simple) -> (E : Γ ⊩ Θ) -> Set

SCE Γ .· empty = ⊤
SCE Γ (Θ , A) (smth E t) = SCE Γ Θ E × SCV Γ A t 

lemma-nf : ∀ {Γ Γ' A} {n : Val Γ A} {a : Nf Γ A} {p : Γ ⊆ Γ'}
             -> n ↓ a -> (val-weak-many-right n p) ↓ (nf-weak-many-right a p)
lemma-ne : ∀ {Γ Γ' A} {n : Ne Γ Val A} {a : Ne Γ Nf A} {p : Γ ⊆ Γ'}
             -> n ↓ne a -> (ne-weak-many-right n p) ↓ne (ne-weak-many-right-nf a p)

lemma-nf (nf-ne p) = {!!}
lemma-nf (nf-lam p q) = {!!}
lemma-nf (nf-prod1 a b p q) = {!!}
lemma-nf nf-unit = {!!}

lemma-ne nf-var = nf-var
lemma-ne (nf-app p q) = nf-app (lemma-ne p) (lemma-nf q)
lemma-ne (nf-prod2 p) = nf-prod2 (lemma-ne p)
lemma-ne (nf-prod3 p) = nf-prod3 (lemma-ne p)

scv-thm-1 : ∀ {Γ} (A : Ty simple) (v : Val Γ A) -> SCV Γ A v -> Σ (Nf Γ A) (λ w -> v ↓ w)
scv-thm-2 : ∀ {Γ} (A : Ty simple) (v : Ne Γ Val A) -> Σ (Ne Γ Nf A) (λ w -> v ↓ne w) -> SCV Γ A (STLC-val-ne v)

scv-thm-1 (P i) v p = p
scv-thm-1 (A => B) t p
  with p {Γ' = (· , A)} (scv-thm-2 A (STLC-ne-var top) (pair (STLC-ne-var top) nf-var))
... | pair a (pair b c) = pair (STLC-nf-lam (proj₁ (scv-thm-1 B a c))) (nf-lam b (proj₂ (scv-thm-1 B a c)))
scv-thm-1 (A ∧ B) v (pair w (pair z (pair a (pair b (pair c d))))) =
  let x = scv-thm-1 A w a in
  let y = scv-thm-1 B z b in
  pair (STLC-nf-prod1 (proj₁ x) (proj₁ y)) (nf-prod1 c d (proj₂ x) (proj₂ y))
scv-thm-1 T v p = p
  
scv-thm-2 (P i) v (pair a b) = pair (STLC-nf-ne a) (nf-ne b)
scv-thm-2 (A => B) n (pair a b) {Γ'} {v} x =
  let p = concat-subset-1 _ Γ' in
  let y = (STLC-ne-app (ne-weak-many-right n p) v) in
  let z = scv-thm-1 A v x in
  let f = scv-thm-2 B y in
  pair (STLC-val-ne y)
       (pair eval-app-ne (f (pair (STLC-ne-app (ne-weak-many-right-nf a p) (proj₁ z))
                                  (nf-app (lemma-ne b) (proj₂ z)))))

scv-thm-2 (A ∧ B) v (pair a b) =
  pair (STLC-val-ne (STLC-ne-prod2 v))
       (pair (STLC-val-ne (STLC-ne-prod3 v))
             (pair (scv-thm-2 A (STLC-ne-prod2 v) (pair (STLC-ne-prod2 a) (nf-prod2 b)))
                   (pair (scv-thm-2 B (STLC-ne-prod3 v) (pair (STLC-ne-prod3 a) (nf-prod3 b)))
                         (pair eval-fst-ne eval-snd-ne))))

scv-thm-2 T v (pair a b) = pair (STLC-nf-ne a) (nf-ne b)
                   
sce-val-is-scv : ∀ {Γ Θ A} -> (q : Σ (Γ ⊩ Θ) (λ E -> SCE Γ Θ E)) -> (p : A ∈ Θ) -> SCV Γ A (get-right-val p (proj₁ q))
sce-val-is-scv (pair empty q) ()
sce-val-is-scv (pair (smth E x) (pair a b)) top = b
sce-val-is-scv (pair (smth E x) q) (pop p) = sce-val-is-scv (pair E (proj₁ q)) p

main-thm : ∀ {Γ Θ A} -> (q : Σ (Γ ⊩ Θ) (λ E -> SCE Γ Θ E)) -> (t : Θ ⊢ A)  -> Σ (Val Γ A) (λ v -> proj₁ q ⊢ t ⇓ v × SCV Γ A v)

main-thm q (STLC-var x) = pair (get-right-val x (proj₁ q)) (pair (whnf-var x) (sce-val-is-scv q x))

main-thm q (STLC-app t u)
 with main-thm q t | main-thm q u
... | pair a (pair b c) | pair e (pair d f)
  with c {Γ' = ·} f
... | pair v (pair w z) = pair v (pair (whnf-app b d (subst ((λ x -> x $  e >> v)) {!!} w)) z)

main-thm (pair E p) (STLC-lam t) =
  let r = main-thm (pair (ctxt-insert-right _ _ E) (pair {!!} {!!})) t in
    pair (STLC-val-lam E t) (pair whnf-lam ((λ q -> pair {!!} {!!}) ))
    
main-thm (pair E p) (STLC-prod1 t u)
  with main-thm (pair E p) t | main-thm (pair E p) u
... | pair a (pair b c) | pair e (pair d f) = pair (STLC-val-prod1 E t u)
      (pair whnf-prod1 (pair a (pair e (pair c (pair f (pair (eval-fst-prod1 b) (eval-snd-prod1 d)))))))
main-thm (pair E p) (STLC-prod2 t)
  with main-thm (pair E p) t
... | pair a (pair b (pair c (pair d (pair e (pair g (pair h j)))))) = pair c (pair (whnf-prod2 b h) e)
main-thm (pair E p) (STLC-prod3 t)
  with main-thm (pair E p) t
... | pair a (pair b (pair c (pair d (pair e (pair g (pair h j)))))) = pair d (pair (whnf-prod3 b j) g)
main-thm (pair E p) (STLC-unit) = pair STLC-val-unit (pair whnf-unit (pair STLC-nf-unit nf-unit))

