-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Data.Fin.Core where

open import Core
open import Data.Nat.Core
  using (ℕ; suc; zero)
import Data.Nat.Core as N


data Fin : ℕ → Set where
  fsuc  : {n : ℕ} → Fin n → Fin (suc n)
  fzero : {n : ℕ} → Fin (suc n)

instance
  Fin-Number : {n : ℕ} → Number (Fin (suc n))
  Fin-Number {n} =
    record {
      Constraint = λ x → x N.≤ n;
      fromNat = f n
    }

    where
    f : ∀ n x {{_ : x N.≤ n}} → Fin (suc n)
    f n .0 {{N.0≤s}} = fzero
    f (suc n) (suc x) {{N.s≤s p}} = fsuc (f n x {{p}})
