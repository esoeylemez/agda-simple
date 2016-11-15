-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Data.Int where

open import Algebra.Group
open import Classes
open import Core
open import Data.Int.Core
open import Data.Int.Core public
  using (ℤ; ℤ-Negative; ℤ-Number; negsuc; pos)


ℤ,+ : Group
ℤ,+ =
  record {
    semigroup = record {
      A = ℤ;
      Eq = PropEq ℤ;
      semigroupOver = record {
        _⋄_ = _+_;
        ⋄-cong = cong2 _+_;
        assoc = Props.+-assoc
      }
    };
    isGroup = record {
      isMonoid = record {
        id = 0;
        left-id = Props.+-left-id;
        right-id = Props.+-right-id
      };
      iso = λ x → record {
        inv = neg x;
        left-inv = Props.+-left-inv x;
        right-inv = Props.+-right-inv x
      };
      inv-cong = cong neg
    }
  }


ℤ,* : Monoid
ℤ,* =
  record {
    semigroup = record {
      A = ℤ;
      Eq = PropEq ℤ;
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
