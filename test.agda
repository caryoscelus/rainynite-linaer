module test where

open import Data.Empty
open import Data.Unit

import IO.Primitive as Prim
import IO

open import Function

{-# FOREIGN GHC
  import T ( everything )
  #-}


postulate
  everything : Prim.IO ⊤

{-# COMPILE GHC everything = T.everything #-}

main = run $ do
  lift everything
  where
    open IO
