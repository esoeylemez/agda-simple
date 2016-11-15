-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Classes where


record Plus {a} (A : Set a) : Set a where
  field
    _+_ : A → A → A

  infixl 6 _+_

open Plus {{...}} public


record Times {a} (A : Set a) : Set a where
  field
    {{plus}} : Plus A
    _*_ : A → A → A

  infixl 7 _*_

open Times {{...}} public
