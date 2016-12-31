module GL.HilbertGL where

open import Basics

----------------------------------------
-- Hilbert system for constructive GL --
----------------------------------------

-- Definition.

data ThmGL (Γ : Cx modal) :  Ty modal -> Set where

  GL-var : ∀ {A : Ty modal} -> (A ∈ Γ) -> ThmGL Γ A
  GL-k : ∀ {A B : Ty modal} ->  ThmGL Γ (A => (B => A))
  GL-s : ∀ {A B C : Ty modal} -> ThmGL Γ ((A => B => C) => (A => B) => (A => C))
  GL-MP : ∀ {A B : Ty modal} -> ThmGL Γ (A => B) -> ThmGL Γ A -> ThmGL Γ B
  GL-NEC : ∀ {A : Ty modal} -> ThmGL · A -> ThmGL Γ (□ A)
  GL-prod1 : ∀ {A B : Ty modal} -> ThmGL Γ (A => B => A ∧ B)
  GL-prod2 : ∀ {A B : Ty modal} -> ThmGL Γ (A ∧ B => A)
  GL-prod3 : ∀ {A B : Ty modal} -> ThmGL Γ (A ∧ B => B)
  GL-axK : ∀ {A B : Ty modal} -> ThmGL Γ (□(A => B) => □ A => □ B)
  GL-axW : ∀ {A : Ty modal} -> ThmGL Γ (□ (□ A => A) => □ A) 
  

-- Weakening, exchange, and contraction.

GL-weak : ∀ {Γ Δ} {A}

  -> Γ ⊆ Δ    -> ThmGL Γ A
  ------------------------
       -> ThmGL Δ A

GL-weak p (GL-var x) = GL-var (subsetdef x p)
GL-weak p GL-k = GL-k
GL-weak p GL-s = GL-s
GL-weak p (GL-MP d d₁) = GL-MP (GL-weak p d) (GL-weak p d₁)
GL-weak p (GL-NEC d) = GL-NEC d
GL-weak p GL-axK = GL-axK
GL-weak p GL-prod1 = GL-prod1
GL-weak p GL-prod2 = GL-prod2
GL-weak p GL-prod3 = GL-prod3
GL-weak p GL-axW = GL-axW


GL-exch : ∀ {Γ} {A B C} (Γ' : Cx modal)

    -> ThmGL (Γ , A , B ++ Γ') C
    ---------------------------
    -> ThmGL (Γ , B , A ++ Γ') C
    
GL-exch Γ' (GL-var p) = GL-var (cx-exch {Δ = Γ'} p)
GL-exch Γ' GL-k = GL-k
GL-exch Γ' GL-s = GL-s
GL-exch Γ' (GL-MP p p₁) = GL-MP (GL-exch Γ' p) (GL-exch Γ' p₁)
GL-exch Γ' (GL-NEC p) = GL-NEC p
GL-exch Γ' GL-prod1 = GL-prod1
GL-exch Γ' GL-prod2 = GL-prod2
GL-exch Γ' GL-prod3 = GL-prod3
GL-exch Γ' GL-axK = GL-axK
GL-exch Γ' GL-axW = GL-axW


GL-contr : ∀ {Γ} {A C} (Γ' : Cx modal)

  -> ThmGL (Γ , A , A ++ Γ') C
  ----------------------------
    -> ThmGL (Γ , A ++ Γ') C

GL-contr Γ' (GL-var p) = GL-var (cx-contr {Δ = Γ'} p)
GL-contr Γ' GL-k = GL-k
GL-contr Γ' GL-s = GL-s
GL-contr Γ' (GL-MP p q) = GL-MP (GL-contr Γ' p) (GL-contr Γ' q)
GL-contr Γ' (GL-NEC p) = GL-NEC p
GL-contr Γ' GL-prod1 = GL-prod1
GL-contr Γ' GL-prod2 = GL-prod2
GL-contr Γ' GL-prod3 = GL-prod3
GL-contr Γ' GL-axK = GL-axK
GL-contr Γ' GL-axW = GL-axW


-- Deduction Theorem.

GL-dedthm :  ∀ {Γ : Cx modal} {A B : Ty modal}

   -> ThmGL (Γ , A) B
   -------------------
   -> ThmGL Γ (A => B)

GL-dedthm {Γ} {A} {.A} (GL-var top) = GL-MP (GL-MP GL-s GL-k) (GL-k {Γ} {A} {A})
GL-dedthm (GL-var (pop x)) = GL-MP GL-k (GL-var x)
GL-dedthm GL-k = GL-MP GL-k GL-k
GL-dedthm GL-s = GL-MP GL-k GL-s
GL-dedthm (GL-MP p q) = GL-MP (GL-MP GL-s (GL-dedthm p)) (GL-dedthm q)
GL-dedthm (GL-NEC d) = GL-MP GL-k (GL-NEC d)
GL-dedthm GL-prod1 = GL-MP GL-k GL-prod1
GL-dedthm GL-prod2 = GL-MP GL-k GL-prod2
GL-dedthm GL-prod3 = GL-MP GL-k GL-prod3
GL-dedthm GL-axK = GL-MP GL-k GL-axK
GL-dedthm GL-axW = GL-MP GL-k GL-axW

                       
-- Admissibility of Scott's rule.

GL-Scott : ∀ {Γ : Cx modal} {A : Ty modal}

          -> ThmGL Γ A
    ------------------------
    -> ThmGL (boxcx Γ) (□ A)
                 
GL-Scott (GL-var x) = GL-var (box∈cx x)
GL-Scott GL-k = GL-NEC GL-k
GL-Scott GL-s = GL-NEC GL-s
GL-Scott (GL-MP d e) =
  let x = GL-Scott d in
  let y = GL-Scott e in
    GL-MP (GL-MP GL-axK x) y
GL-Scott (GL-NEC d) = GL-NEC (GL-NEC d)
GL-Scott GL-prod1 = GL-NEC GL-prod1
GL-Scott GL-prod2 = GL-NEC GL-prod2
GL-Scott GL-prod3 = GL-NEC GL-prod3
GL-Scott GL-axK = GL-NEC GL-axK
GL-Scott GL-axW = GL-NEC GL-axW


-- Derivability of
-- (a) composition
-- (b) "normality"
-- (c) the natural deduction rules for product
-- (d) the K4 axiom

GL-comp : ∀ {Γ} {A} (B : Ty modal) {C}

   -> ThmGL Γ (A => B)   -> ThmGL Γ (B => C)
   ---------------------------------------
            -> ThmGL Γ (A => C)

GL-comp B d e = GL-MP (GL-MP GL-s (GL-MP GL-k e)) d


GL-normal-der : ∀ {Γ} {A B}

    -> ThmGL Γ (□ (A => B))
    -----------------------
    -> ThmGL Γ (□ A => □ B)
    
GL-normal-der d = GL-MP GL-axK d


GL-prod-der : ∀ {Γ} {A B}

    -> ThmGL Γ A    -> ThmGL Γ B
    ----------------------------
        -> ThmGL Γ (A ∧ B)

GL-prod-der p q = GL-MP (GL-MP GL-prod1 p) q


GL-snd-der : ∀ {Γ} {A B}

    -> ThmGL Γ (A ∧ B)
    ------------------
      -> ThmGL Γ B

GL-snd-der p = GL-MP GL-prod3 p


GL-prov4-lem1 :  ∀ {A} -> ThmGL (· , □(□ A ∧ A)) (□ A)

GL-prov4-lem1 = GL-Scott (GL-snd-der (GL-var top))


GL-prov4-lem2 : ∀ {A} -> ThmGL (· , A , □(□ A ∧ A))  (□ A ∧ A)

GL-prov4-lem2 =
  GL-prod-der (GL-exch · (GL-weak (weakone subsetid) GL-prov4-lem1))
              (GL-var (pop top))

GL-prov4-lem3 : ∀ {Γ A} -> ThmGL Γ (□ A => □ (□(□ A ∧ A) => (□ A ∧ A)))

GL-prov4-lem3 =
  GL-normal-der (GL-NEC (GL-dedthm (GL-dedthm GL-prov4-lem2)))


GL-prov4-lem4 :  ∀ {Γ A} -> ThmGL Γ (□ A => □(□ A ∧ A))
GL-prov4-lem4 = GL-comp _ GL-prov4-lem3 GL-axW


GL-prov4-lem5 : ∀ {Γ A} -> ThmGL Γ (□(□ A ∧ A) => □ □ A)
GL-prov4-lem5 = GL-MP GL-axK (GL-NEC GL-prod2)


GL-prov4 : ∀ {Γ} {A} -> ThmGL Γ (□ A => □ □ A)
GL-prov4 = GL-comp _ GL-prov4-lem4 GL-prov4-lem5


-- Admissibility of the Four Rule.

GL-Four : ∀ {Γ : Cx modal} {A : Ty modal}

   -> ThmGL (boxcx Γ ++ Γ) A
   --------------------------
   -> ThmGL (boxcx Γ) (□ A)

GL-Four {·} (GL-var x) = GL-NEC (GL-var x)
GL-Four {Γ , A} (GL-var top) = GL-var top
GL-Four {Γ , A} (GL-var (pop x))
  with subsetdef x (swap-out (boxcx Γ) Γ (□ A))
... | top = GL-MP GL-prov4 (GL-var top)
... | pop q = GL-weak (concat-subset-1 (boxcx Γ) (· , □ A))
                      (GL-Four (GL-var q))
GL-Four GL-k = GL-NEC GL-k
GL-Four GL-s = GL-NEC GL-s
GL-Four (GL-MP p q) =
  GL-MP (GL-MP GL-axK (GL-Four p)) (GL-Four q)
GL-Four (GL-NEC d) = GL-NEC (GL-NEC d)
GL-Four GL-prod1 = GL-NEC GL-prod1
GL-Four GL-prod2 = GL-NEC GL-prod2
GL-Four GL-prod3 = GL-NEC GL-prod3
GL-Four GL-axK = GL-NEC GL-axK
GL-Four GL-axW = GL-NEC GL-axW


-- Variant of the Four Rule.

GL-Four-v : ∀ {Γ : Cx modal} {A : Ty modal}

     -> ThmGL (boxcx Γ) A
   ------------------------
   -> ThmGL (boxcx Γ) (□ A)

GL-Four-v {Γ} p =
  GL-Four (GL-weak (concat-subset-1 (boxcx Γ) Γ) p)


-- Admissibility of Lob's Rule.

GL-lob : ∀ {Γ : Cx modal} {A : Ty modal}

  -> ThmGL (boxcx Γ ++ Γ , □ A) A
  -------------------------------
     -> ThmGL (boxcx Γ) (□ A)

GL-lob p = GL-MP GL-axW (GL-Four (GL-dedthm p))

-- Variant of Lob's rule.

GL-lob-v : ∀ {Γ : Cx modal} {A : Ty modal}

  -> ThmGL (boxcx Γ , □ A) A
  ---------------------------
   -> ThmGL (boxcx Γ) (□ A)

GL-lob-v {Γ} p =
  GL-lob (GL-weak (weakboth (concat-subset-1 (boxcx Γ) Γ)) p)


-- Admissibility of the cut rule.

GL-cut : ∀ {Γ : Cx modal} {A B : Ty modal}

  -> ThmGL Γ A    -> ThmGL (Γ , A) B
  -----------------------------------
          -> ThmGL Γ B
                    
GL-cut d (GL-var top) = d
GL-cut d (GL-var (pop x)) = GL-var x
GL-cut d GL-k = GL-k
GL-cut d GL-s = GL-s
GL-cut d (GL-MP e e₁) = GL-MP (GL-cut d e) (GL-cut d e₁)
GL-cut d (GL-NEC e) = GL-NEC e
GL-cut d GL-prod1 = GL-prod1
GL-cut d GL-prod2 = GL-prod2
GL-cut d GL-prod3 = GL-prod3
GL-cut d GL-axK = GL-axK
GL-cut d GL-axW = GL-axW

