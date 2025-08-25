{-# OPTIONS --rewriting #-}

{-
  -------------------------------- !!! !!! --------------------------------
  This module extends rewriting.AbstractBindingTree with variable kinding
  -------------------------------- +++ +++ --------------------------------
-}
open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate) renaming (map to lmap)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_; _≟_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; suc-injective)
open import Data.Product using (_×_; proj₁; proj₂; ∃-syntax; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no; contradiction)
open import ScopedTuple
open import Sig
open import Var
open import Function using (case_of_)
open import Structures using (extensionality)

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module rewriting.AbstractBindingTreeWithKind {ℓ}
  -- Parameters of the module
  (Op : Set ℓ)
  (sig : Op → List Sig)
  (VarKind : Set)
  (kind-eq? : ∀ (𝑘 𝑗 : VarKind) → Dec (𝑘 ≡ 𝑗)) where

data Args : List Sig → Set ℓ

data ABT : Set ℓ where
  `_of_ : Var → VarKind → ABT
  _⦅_⦆ : (op : Op) → Args (sig op) → ABT

data Arg : Sig → Set ℓ where
  ast : ABT → Arg ■
  bind : ∀{b} → VarKind → Arg b → Arg (ν b)

data Args where
  nil : Args []
  cons : ∀{b bs} → Arg b → Args bs → Args (b ∷ bs)

{----------------------------------------------------------------------------
 Renaming
----------------------------------------------------------------------------}

Rename : Set
Rename = Var → Var

infixr 6 _•ᵣ_
_•ᵣ_ : Var → Rename → Rename
(y •ᵣ ρ) 0 = y
(y •ᵣ ρ) (suc x) = ρ x

⟰ᵣ : Rename → Rename
⟰ᵣ ρ x = suc (ρ x)

extr : Rename → Rename
extr ρ = 0 •ᵣ ⟰ᵣ ρ

rename : Rename → VarKind → ABT → ABT
rename-arg : Rename → VarKind → {b : Sig} → Arg b → Arg b
rename-args : Rename → VarKind → {bs : List Sig} → Args bs → Args bs

rename ρ 𝑘 (` x of 𝑗) with kind-eq? 𝑘 𝑗
... | yes refl = ` (ρ x) of 𝑗    -- we only rename the correct kind of variables
... | no _     = ` x of 𝑗
rename ρ 𝑘 (op ⦅ args ⦆) = op ⦅ rename-args ρ 𝑘 args ⦆
rename-arg ρ 𝑘 (ast M) = ast (rename ρ 𝑘 M)
rename-arg ρ 𝑘 (bind 𝑗 M) with kind-eq? 𝑘 𝑗
... | yes refl = bind 𝑗 (rename-arg (extr ρ) 𝑘 M)
... | no _     = bind 𝑗 (rename-arg ρ 𝑘 M)
rename-args ρ 𝑘 nil = nil
rename-args ρ 𝑘 (cons arg args) = cons (rename-arg ρ 𝑘 arg) (rename-args ρ 𝑘 args)

{----------------------------------------------------------------------------
 Substitution
----------------------------------------------------------------------------}

Subst : Set ℓ
Subst = Var → ABT

infixr 6 _•_
_•_ : ABT → Subst → Subst
(M • σ) 0 = M
(M • σ) (suc x) = σ x

{----------------------------------------------------------------------------
 The following module is for internal use only.
 ----------------------------------------------------------------------------}
module Private where

  ⟰ : Subst → VarKind → Subst
  ⟰ σ 𝑘 x = rename suc 𝑘 (σ x)

  exts : Subst → VarKind → Subst
  exts σ 𝑘 = (` 0 of 𝑘) • (⟰ σ 𝑘)

  sub : Subst → VarKind → ABT → ABT
  sub-arg : Subst → VarKind → {b : Sig} → Arg b → Arg b
  sub-args : Subst → VarKind → {bs : List Sig} → Args bs → Args bs

  sub σ 𝑘 (` x of 𝑗) with kind-eq? 𝑘 𝑗
  ... | yes refl = σ x
  ... | no _     = ` x of 𝑗
  sub σ 𝑘 (op ⦅ args ⦆) = op ⦅ sub-args σ 𝑘 args ⦆
  sub-arg σ 𝑘 (ast M) = ast (sub σ 𝑘 M)
  sub-arg σ 𝑘 (bind 𝑗 M) with kind-eq? 𝑘 𝑗
  ... | yes refl = bind 𝑗 (sub-arg (exts σ 𝑗) 𝑘 M)
  ... | no _     = bind 𝑗 (sub-arg σ 𝑘 M)
  sub-args σ 𝑘 nil = nil
  sub-args σ 𝑘 (cons arg args) = cons (sub-arg σ 𝑘 arg) (sub-args σ 𝑘 args)

  {- TODO: make ren abstract -}
  ren : Rename → VarKind → Subst
  ren ρ 𝑘 x = ` (ρ x) of 𝑘

  abstract
    infixr 5 _⨟_of_
    _⨟_of_ : Subst → Subst → VarKind → Subst
    (σ ⨟ τ of 𝑘) x = sub τ 𝑘 (σ x)

  abstract
    seq-def : ∀ σ τ 𝑘 x → (σ ⨟ τ of 𝑘) x ≡ sub τ 𝑘 (σ x)
    seq-def σ τ 𝑘 x = refl
  {-# REWRITE seq-def #-}

  cons-seq-dist : ∀ σ τ 𝑘 M → (M • σ) ⨟ τ of 𝑘 ≡ sub τ 𝑘 M • (σ ⨟ τ of 𝑘)
  cons-seq-dist σ τ 𝑘 M = extensionality ♠
      where
      ♠ : ∀ x → ((M • σ) ⨟ τ of 𝑘) x ≡ (sub τ 𝑘 M • (σ ⨟ τ of 𝑘)) x
      ♠ zero = refl
      ♠ (suc x) = refl
  {-# REWRITE cons-seq-dist #-}

  ext-ren : ∀{ρ 𝑘} → (` 0 of 𝑘) • (⟰ (ren ρ 𝑘) 𝑘) ≡ ren (extr ρ) 𝑘
  ext-ren {ρ} {𝑘} = extensionality ♠
      where
      ♠ : ∀ x → exts (ren ρ 𝑘) 𝑘 x ≡ ren (extr ρ) 𝑘 x
      ♠ zero = refl
      ♠ (suc x) with kind-eq? 𝑘 𝑘
      ... | yes refl = refl
      ... | no neq = contradiction refl neq
  {-# REWRITE ext-ren #-}

  rename-ren : ∀{ρ 𝑘 M} → rename ρ 𝑘 M ≡ sub (ren ρ 𝑘) 𝑘 M
  rename-ren-arg : ∀{ρ 𝑘 b}{arg : Arg b} → rename-arg ρ 𝑘 arg ≡ sub-arg (ren ρ 𝑘) 𝑘 arg
  rename-ren-args : ∀{ρ 𝑘 bs}{args : Args bs}
     → rename-args ρ 𝑘 args ≡ sub-args (ren ρ 𝑘) 𝑘 args
  rename-ren {ρ} {𝑘} {` x of 𝑗} with kind-eq? 𝑘 𝑗
  ... | yes refl = refl
  ... | no neq = refl
  rename-ren {ρ} {𝑘} {op ⦅ args ⦆} = cong ((λ X → op ⦅ X ⦆)) rename-ren-args
  rename-ren-arg {ρ} {𝑘} {.■} {ast M} = cong ast (rename-ren {ρ} {𝑘} {M})
  rename-ren-arg {ρ} {𝑘} {.(ν _)} {bind 𝑗 arg} with kind-eq? 𝑘 𝑗
  ... | yes refl = cong (bind 𝑘) (rename-ren-arg {_} {𝑘} {_} {arg})
  ... | no neq = cong (bind 𝑗) (rename-ren-arg {ρ} {𝑘} {_} {arg})
  rename-ren-args {ρ} {𝑘} {.[]} {nil} = refl
  rename-ren-args {ρ} {𝑘} {.(_ ∷ _)} {cons arg args} =
      cong₂ cons (rename-ren-arg {ρ} {𝑘} {_} {arg}) rename-ren-args
  {-# REWRITE rename-ren #-}


  ext-ren-sub : ∀ {ρ}{τ}{𝑘} → exts (ren ρ 𝑘) 𝑘 ⨟ exts τ 𝑘 of 𝑘 ≡ exts (ren ρ 𝑘 ⨟ τ of 𝑘) 𝑘
  ext-ren-sub {ρ}{τ}{𝑘} = {!!}
    -- extensionality (aux{ρ}{τ})
    --   where
    --   aux : ∀{ρ}{τ} → ∀ x → (exts (ren ρ) ⨟ exts τ) x ≡ exts (ren ρ ⨟ τ) x
    --   aux {ρ} {τ} zero = refl
    --   aux {ρ} {τ} (suc x) = refl
  {-# REWRITE ext-ren-sub #-}

  private
    ext-ren-η : ∀ {ρ 𝑘} → ((` 0 of 𝑘) • (λ x → ` suc (ρ x) of 𝑘)) ≡ ren (extr ρ) 𝑘
    ext-ren-η {ρ}{𝑘} = extensionality ♠
      where
      ♠ : ∀ x → ((` 0 of 𝑘) • (λ y → ` suc (ρ y) of 𝑘)) x ≡ ren (extr ρ) 𝑘 x
      ♠ zero = refl
      ♠ (suc x) = refl

  ren-sub : ∀ {τ ρ 𝑘 M} → sub τ 𝑘 (sub (ren ρ 𝑘) 𝑘 M) ≡ sub (ren ρ 𝑘 ⨟ τ of 𝑘) 𝑘 M
  ren-sub-arg : ∀ {τ ρ 𝑘 b}{arg : Arg b}
     → sub-arg τ 𝑘 (sub-arg (ren ρ 𝑘) 𝑘 arg) ≡ sub-arg (ren ρ 𝑘 ⨟ τ of 𝑘) 𝑘 arg
  ren-sub-args : ∀ {τ ρ 𝑘 bs}{args : Args bs}
     → sub-args τ 𝑘 (sub-args (ren ρ 𝑘) 𝑘 args) ≡ sub-args (ren ρ 𝑘 ⨟ τ of 𝑘) 𝑘 args

  ren-sub {τ} {ρ} {𝑘} {` x of 𝑗} with kind-eq? 𝑘 𝑗
  ... | yes refl = refl
  ... | no k≠j with kind-eq? 𝑘 𝑗
  ... | yes k=j = contradiction k=j k≠j
  ... | no _ = refl
  ren-sub {τ} {ρ} {𝑘} {op ⦅ args ⦆} = cong ((λ X → op ⦅ X ⦆)) ren-sub-args
  ren-sub-arg {τ} {ρ} {𝑘} {.■} {ast M} = cong ast (ren-sub{τ}{ρ}{𝑘}{M})
  ren-sub-arg {τ} {ρ} {𝑘} {.(ν _)} {bind 𝑗 arg} with kind-eq? 𝑘 𝑗
  ... | yes refl with kind-eq? 𝑘 𝑘
  ...   | yes refl = cong (bind 𝑘) ♣
    where
    ♣ : sub-arg (exts τ 𝑗) 𝑗 (sub-arg ((` 0 of 𝑗) • (λ x → ` suc (ρ x) of 𝑗)) 𝑗 arg) ≡
                sub-arg (exts (ren ρ 𝑗 ⨟ τ of 𝑗) 𝑗) 𝑗 arg
    ♣ rewrite ext-ren-η {ρ} {𝑗} = ren-sub-arg {exts τ 𝑘} {extr ρ} {𝑘} {arg = arg}
  ...   | no k≠k = contradiction refl k≠k
  ren-sub-arg {τ} {ρ} {𝑘} {.(ν _)} {bind 𝑗 arg} | no k≠j with kind-eq? 𝑘 𝑗
  ... | yes k=j = contradiction k=j k≠j
  ... | no k≠j  = cong (bind 𝑗) (ren-sub-arg {τ} {ρ} {𝑘} {arg = arg})
  ren-sub-args {τ} {ρ} {𝑘} {.[]} {nil} = refl
  ren-sub-args {τ} {ρ} {𝑘} {.(_ ∷ _)} {cons arg args} =
     cong₂ cons (ren-sub-arg {arg = arg}) ren-sub-args
  {-# REWRITE ren-sub #-}

--   sub-ren : ∀{ρ σ M} → sub (ren ρ) (sub σ M) ≡ sub (σ ⨟ ren ρ) M
--   sub-ren-arg : ∀{ρ σ b}{arg : Arg b} → sub-arg (ren ρ) (sub-arg σ arg) ≡ sub-arg (σ ⨟ ren ρ) arg
--   sub-ren-args : ∀{ρ σ bs}{args : Args bs} → sub-args (ren ρ) (sub-args σ args) ≡ sub-args (σ ⨟ ren ρ) args
--   sub-ren {ρ} {σ} {` x} = refl
--   sub-ren {ρ} {σ} {op ⦅ args ⦆} = cong (λ X → op ⦅ X ⦆) sub-ren-args
--   sub-ren-arg {ρ} {σ} {.■} {ast M} = cong ast (sub-ren{ρ}{σ}{M})
--   sub-ren-arg {ρ} {σ} {.(ν _)} {bind arg} = cong bind sub-ren-arg
--   sub-ren-args {ρ} {σ} {.[]} {nil} = refl
--   sub-ren-args {ρ} {σ} {.(_ ∷ _)} {cons arg args} = cong₂ cons sub-ren-arg sub-ren-args
--   {-# REWRITE sub-ren #-}

--   sub-sub : ∀{σ τ M} → sub τ (sub σ M) ≡ sub (σ ⨟ τ) M
--   sub-sub-arg : ∀{σ τ b}{arg : Arg b} → sub-arg τ (sub-arg σ arg) ≡ sub-arg (σ ⨟ τ) arg
--   sub-sub-args : ∀{σ τ bs}{args : Args bs} → sub-args τ (sub-args σ args) ≡ sub-args (σ ⨟ τ) args
--   sub-sub {σ} {τ} {` x} = refl
--   sub-sub {σ} {τ} {op ⦅ args ⦆} = cong (λ X → op ⦅ X ⦆) sub-sub-args
--   sub-sub-arg {σ} {τ} {.■} {ast M} = cong ast (sub-sub{σ}{τ}{M})
--   sub-sub-arg {σ} {τ} {.(ν _)} {bind arg} = cong bind sub-sub-arg
--   sub-sub-args {σ} {τ} {.[]} {nil} = refl
--   sub-sub-args {σ} {τ} {.(_ ∷ _)} {cons arg args} = cong₂ cons sub-sub-arg sub-sub-args
--   {-# REWRITE sub-sub #-}

--   shift-seq : ∀{σ} → ⟰ σ ≡ σ ⨟ ren suc
--   shift-seq {σ} = refl

--   idᵣ : Rename
--   idᵣ x = x

--   extr-id : (0 •ᵣ ⟰ᵣ idᵣ) ≡ idᵣ {- extr idᵣ ≡ idᵣ -}
--   extr-id = extensionality aux
--     where
--     aux : ∀ x → extr idᵣ x ≡ idᵣ x
--     aux zero = refl
--     aux (suc x) = refl
--   {-# REWRITE extr-id #-}

--   id : Subst
--   id x = ` x

--   ext-id : exts id ≡ id
--   ext-id = refl

--   sub-id : ∀ {M} → sub id M ≡ M
--   sub-arg-id : ∀ {b}{arg : Arg b} → sub-arg id arg ≡ arg
--   sub-args-id : ∀ {bs}{args : Args bs} → sub-args id args ≡ args
--   sub-id {` x} = refl
--   sub-id {op ⦅ args ⦆} = cong (λ X → op ⦅ X ⦆) sub-args-id
--   sub-arg-id {.■} {ast M} = cong ast sub-id
--   sub-arg-id {.(ν _)} {bind arg} = cong bind sub-arg-id
--   sub-args-id {.[]} {nil} = refl
--   sub-args-id {.(_ ∷ _)} {cons arg args} = cong₂ cons sub-arg-id sub-args-id
--   {-# REWRITE sub-id #-}

-- {----------------------------------------------------------------------------
--  Public
-- ----------------------------------------------------------------------------}

-- abstract {- experimenting with making ren abstract -Jeremy -}
--   ren : Rename → Subst
--   ren = Private.ren

--   ren-def : ∀ ρ x → ren ρ x ≡ ` ρ x
--   ren-def ρ x = refl

-- ↑ : Subst
-- ↑ = ren suc

-- up-def : ↑ ≡ ren suc
-- up-def = refl

-- abstract
--   infixr 5 _⨟_
--   _⨟_ : Subst → Subst → Subst
--   σ ⨟ τ = Private._⨟_ σ τ

--   id : Subst
--   id = Private.id
    
-- ext : Subst → Subst
-- ext σ = ` 0 • (σ ⨟ ↑)

-- abstract
--   -- Phil: you're using semicolon, so this should be postfix
--   ⟪_⟫ : Subst → ABT → ABT
--   ⟪ σ ⟫ M = Private.sub σ M

--   -- Phil: try switching + to *
--   ⟪_⟫₊ : Subst → {bs : List Sig} → Args bs → Args bs
--   ⟪ σ ⟫₊ args = Private.sub-args σ args

--   ⟪_⟫ₐ : Subst → {b : Sig} → Arg b → Arg b
--   ⟪ σ ⟫ₐ arg = Private.sub-arg σ arg

--   id-var : ∀{x} → id x ≡ ` x
--   id-var {x} = refl
--   {-# REWRITE id-var #-}
  
--   sub-var : ∀ σ x → ⟪ σ ⟫ (` x) ≡ σ x
--   sub-var σ x = refl
--   {- REWRITE sub-var -}
  
--   sub-op : ∀{σ : Subst}{op : Op}{args : Args (sig op)}
--      → ⟪ σ ⟫ (op ⦅ args ⦆) ≡ op ⦅ ⟪ σ ⟫₊ args ⦆
--   sub-op {σ}{op}{args} = refl
--   {-# REWRITE sub-op #-}

--   sub-arg-ast : ∀{σ M} → ⟪ σ ⟫ₐ (ast M) ≡ ast (⟪ σ ⟫ M)
--   sub-arg-ast {σ}{M} = refl
--   {-# REWRITE sub-arg-ast #-}
  
--   sub-arg-bind : ∀{σ b}{arg : Arg b}
--      → ⟪ σ ⟫ₐ (bind arg) ≡ bind (⟪ ext σ ⟫ₐ arg)
--   sub-arg-bind {σ}{b}{arg} = refl
--   {-# REWRITE sub-arg-bind #-}

--   sub-args-nil : ∀{σ} → ⟪ σ ⟫₊ nil ≡ nil
--   sub-args-nil {σ} = refl
--   {-# REWRITE sub-args-nil #-}

--   sub-args-cons : ∀{σ}{b}{bs}{arg : Arg b}{args : Args bs}
--      → ⟪ σ ⟫₊ (cons arg args) ≡ cons (⟪ σ ⟫ₐ arg) (⟪ σ ⟫₊ args)
--   sub-args-cons {σ}{arg}{args} = refl
--   {-# REWRITE sub-args-cons #-}

--   sub-head : ∀ σ M → ⟪ M • σ ⟫ (` 0) ≡ M
--   sub-head σ M = refl
--   {-# REWRITE sub-head #-}

--   sub-tail : ∀ σ M → ↑ ⨟ M • σ ≡ σ
--   sub-tail σ M = extensionality (aux{σ}{M})
--       where
--       aux : ∀{σ M} → ∀ x → (↑ ⨟ M • σ) x ≡ σ x
--       aux {σ} {M} zero = refl
--       aux {σ} {M} (suc x) = refl
--   {-# REWRITE sub-tail #-}

--   sub-id : ∀ M → ⟪ id ⟫ M ≡ M
--   sub-id M = Private.sub-id
--   {-# REWRITE sub-id #-}  

--   sub-eta : ∀ σ → (⟪ σ ⟫ (` 0)) • (↑ ⨟ σ) ≡ σ
--   sub-eta σ = extensionality aux
--     where
--     aux : ∀ {σ} x → ((⟪ σ ⟫ (` 0)) • (↑ ⨟ σ)) x ≡ σ x
--     aux {σ} zero = refl
--     aux {σ} (suc x) = refl
--   {-# REWRITE sub-eta #-}  

--   sub-id-right : ∀ (σ : Subst) → σ ⨟ id ≡ σ 
--   sub-id-right σ = refl
--   {-# REWRITE sub-id-right #-}  

--   sub-id-left : (σ : Subst) → id ⨟ σ ≡ σ
--   sub-id-left σ = refl
--   {-# REWRITE sub-id-left #-}

--   sub-assoc : ∀ σ τ θ → (σ ⨟ τ) ⨟ θ ≡ σ ⨟ τ ⨟ θ
--   sub-assoc σ τ θ = refl
--   {-# REWRITE sub-assoc #-}
  
--   cons-seq : ∀ σ τ M → (M • σ) ⨟ τ ≡ ⟪ τ ⟫ M • (σ ⨟ τ)
--   cons-seq σ τ M = refl
--   {-# REWRITE cons-seq #-}  

--   compose-sub : ∀ σ τ M → ⟪ τ ⟫ (⟪ σ ⟫ M) ≡ ⟪ σ ⨟ τ ⟫ M
--   compose-sub σ τ M = refl
--   {-# REWRITE compose-sub #-}  

--   cons-zero-up : ` 0 • ↑ ≡ id
--   cons-zero-up = refl
--   {-# REWRITE cons-zero-up #-}  

--   seq-def : ∀ σ τ x → (σ ⨟ τ) x ≡ ⟪ τ ⟫ (σ x)
--   seq-def σ τ x = refl

--   up-var : ∀ x → ↑ x ≡ ` suc x
--   up-var x = refl

--   ext-ren-extr : ∀ ρ → (` 0) • (ren ρ ⨟ ↑) ≡ ren (extr ρ)
--   ext-ren-extr ρ = refl
--   -- {-# REWRITE ext-ren-extr #-}
  
--   ren-extr-def : ∀ ρ → ren (extr ρ) ≡ ` 0 • (ren ρ ⨟ ↑)
--   ren-extr-def ρ = refl
--   {-# REWRITE ren-extr-def #-}

--   ren-extr-zero : ∀ ρ → ren (extr ρ) 0 ≡ ` 0
--   ren-extr-zero ρ = refl
--   {- REWRITE ren-extr-zero -}

--   ren-extr-suc : ∀ ρ x → ren (extr ρ) (suc x) ≡ ` suc (ρ x)
--   ren-extr-suc ρ x = refl
--   {- REWRITE ren-extr-suc -}

--   seq-up-ren-suc : ∀ σ x → (σ ⨟ ↑) x ≡ Private.sub (Private.ren suc) (σ x)  
--   seq-up-ren-suc σ x = refl

--   ren-seq-up : ∀ ρ x → (ren ρ ⨟ ↑) x ≡ ` suc (ρ x)
--   ren-seq-up ρ x = refl
--   {- REWRITE ren-seq-up -}

-- _[_] : ABT → ABT → ABT
-- N [ M ] =  ⟪ M • id ⟫ N

-- _〔_〕 : ABT → ABT → ABT
-- _〔_〕 N M = ⟪ ext (M • id) ⟫ N

-- substitution : ∀{M N L} → M [ N ] [ L ] ≡ M 〔 L 〕 [ N [ L ] ]
-- substitution {M}{N}{L} = refl

-- exts-sub-cons : ∀ {σ N V} → (⟪ ext σ ⟫ N) [ V ] ≡ ⟪ V • σ ⟫ N
-- exts-sub-cons {σ}{N}{V} = refl

-- {----------------------------------------------------------------------------
--  Free variables
-- ----------------------------------------------------------------------------}

-- FV? : ABT → Var → Bool
-- FV-arg? : ∀{b} → Arg b → Var → Bool
-- FV-args? : ∀{bs} → Args bs → Var → Bool
-- FV? (` x) y
--     with x ≟ y
-- ... | yes xy = true
-- ... | no xy = false
-- FV? (op ⦅ args ⦆) y = FV-args? args y
-- FV-arg? (ast M) y = FV? M y
-- FV-arg? (bind arg) y = FV-arg? arg (suc y)
-- FV-args? nil y = false
-- FV-args? (cons arg args) y = FV-arg? arg y ∨ FV-args? args y

-- {- Predicate Version -}

-- FV : ABT → Var → Set
-- FV-arg : ∀{b} → Arg b → Var → Set
-- FV-args : ∀{bs} → Args bs → Var → Set
-- FV (` x) y = x ≡ y
-- FV (op ⦅ args ⦆) y = FV-args args y
-- FV-arg (ast M) y = FV M y
-- FV-arg (bind arg) y = FV-arg arg (suc y)
-- FV-args nil y = ⊥
-- FV-args (cons arg args) y = FV-arg arg y ⊎ FV-args args y

-- FV-rename-fwd : ∀ (ρ : Rename) M y → FV M y
--    → FV (rename ρ M) (ρ y)
-- FV-rename-fwd ρ (` x) y refl = refl
-- FV-rename-fwd ρ (op ⦅ args ⦆) y fvMy = fvr-args ρ (sig op) args y fvMy
--   where
--   fvr-arg : ∀ (ρ : Rename) b (arg : Arg b) y
--       → FV-arg arg y → FV-arg (rename-arg ρ arg) (ρ y)
--   fvr-args : ∀ (ρ : Rename) bs (args : Args bs) y
--       → FV-args args y → FV-args (rename-args ρ args) (ρ y)
--   fvr-arg ρ ■ (ast M) y fvarg = FV-rename-fwd ρ M y fvarg
--   fvr-arg ρ (ν b) (bind arg) y fvarg =
--       fvr-arg (extr ρ) b arg (suc y) fvarg
--   fvr-args ρ [] nil y ()
--   fvr-args ρ (b ∷ bs) (cons arg args) y (inj₁ fvargy) =
--       inj₁ (fvr-arg ρ b arg y fvargy)
--   fvr-args ρ (b ∷ bs) (cons arg args) y (inj₂ fvargsy) =
--       inj₂ (fvr-args ρ bs args y fvargsy)

-- FV-rename : ∀ (ρ : Rename) M y → FV (rename ρ M) y
--    → Σ[ x ∈ Var ] ρ x ≡ y × FV M x
-- FV-rename ρ (` x) y refl = ⟨ x , ⟨ refl , refl ⟩ ⟩
-- FV-rename ρ (op ⦅ args ⦆) y fv = fvr-args ρ (sig op) args y fv
--   where
--   fvr-arg : ∀ (ρ : Rename) b (arg : Arg b) y
--      → FV-arg (rename-arg ρ arg) y → Σ[ x ∈ Var ] (ρ) x ≡ y × FV-arg arg x
--   fvr-args : ∀ (ρ : Rename) bs (args : Args bs) y
--      → FV-args (rename-args ρ args) y → Σ[ x ∈ Var ] (ρ) x ≡ y × FV-args args x
--   fvr-arg ρ b (ast M) y fv = FV-rename ρ M y fv 
--   fvr-arg ρ (ν b) (bind arg) y fv 
--       with fvr-arg (extr ρ) b arg (suc y) fv
--   ... | ⟨ 0 , eq ⟩  
--       with eq
--   ... | ()
--   fvr-arg ρ (ν b) (bind arg) y fv 
--       | ⟨ suc x , ⟨ eq , sx∈arg ⟩ ⟩ =
--         ⟨ x , ⟨ suc-injective eq , sx∈arg ⟩ ⟩
--   fvr-args ρ [] nil y ()
--   fvr-args ρ (b ∷ bs) (cons arg args) y (inj₁ fv)
--       with fvr-arg ρ b arg y fv
--   ... | ⟨ x , ⟨ ρx , x∈arg ⟩ ⟩ = 
--         ⟨ x , ⟨ ρx , (inj₁ x∈arg) ⟩ ⟩
--   fvr-args ρ (b ∷ bs) (cons arg args) y (inj₂ fv)
--       with fvr-args ρ bs args y fv
--   ... | ⟨ x , ⟨ ρx , x∈args ⟩ ⟩ = 
--         ⟨ x , ⟨ ρx , (inj₂ x∈args) ⟩ ⟩

-- rename-FV-⊥ : ∀ y (ρ : Rename) M → (∀ x → (ρ) x ≢ y) → FV (rename ρ M) y → ⊥
-- rename-FV-⊥ y ρ M ρx≢y fvρM 
--     with FV-rename ρ M y fvρM
-- ... | ⟨ x , ⟨ ρxy , x∈M ⟩ ⟩ = ⊥-elim (ρx≢y x ρxy)

-- FV-↑1-0 : ∀ M → FV (rename suc M) 0 → ⊥
-- FV-↑1-0 M = rename-FV-⊥ 0 suc M (λ { x () })

-- abstract
--   FV-ren : ∀ (ρ : Rename) M y → FV (⟪ ren ρ ⟫ M) y
--      → ∃[ x ] ρ x ≡ y × FV M x
--   FV-ren ρ M y y∈FVρM = FV-rename ρ M y y∈FVρM

--   FV-ren-fwd : ∀ (ρ : Rename) M y → FV M y
--      → FV (⟪ ren ρ ⟫ M) (ρ y)
--   FV-ren-fwd ρ M y y∈M = FV-rename-fwd ρ M y y∈M

--   FV-suc-0 : ∀ M → FV (⟪ ren suc ⟫ M) 0 → ⊥
--   FV-suc-0 M = rename-FV-⊥ 0 suc M (λ { x () })



