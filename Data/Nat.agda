-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Data.Nat where

open import Algebra.Group
open import Core
open import Data.Nat.Core
open import Data.Nat.Core public
  using (ℕ; ℕ-Number; suc; zero)


ℕ,+ : Monoid
ℕ,+ =
  record {
    semigroup = record {
      A = ℕ;
      Eq = PropEq ℕ;
      semigroupOver = record {
        _⋄_ = _+_;
        ⋄-cong = cong2 _+_;
        assoc = Props.+-assoc
      }
    };
    isMonoid = record {
      id = 0;
      left-id = Props.+-left-id;
      right-id = Props.+-right-id
    }
  }


ℕ,* : Monoid
ℕ,* =
  record {
    semigroup = record {
      A = ℕ;
      Eq = PropEq ℕ;
      semigroupOver = record {
        _⋄_ = _*_;
        ⋄-cong = cong2 _*_;
        assoc = Props.*-assoc
      }
    };
    isMonoid = record {
      id = 1;
      left-id = Props.*-left-id;
      right-id = Props.*-right-id
    }
  }
