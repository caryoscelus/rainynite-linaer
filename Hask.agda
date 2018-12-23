{-- Hask.agda - common haskell bindings
 -- Copyright (C) 2018 caryoscelus
 --
 -- This program is free software: you can redistribute it and/or modify
 -- it under the terms of the GNU General Public License as published by
 -- the Free Software Foundation, either version 3 of the License, or
 -- (at your option) any later version.
 --
 -- This program is distributed in the hope that it will be useful,
 -- but WITHOUT ANY WARRANTY; without even the implied warranty of
 -- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 -- GNU General Public License for more details.
 --
 -- You should have received a copy of the GNU General Public License
 -- along with this program.  If not, see <http://www.gnu.org/licenses/>.
 --}

module Hask where

postulate
  Float Double Int Integer : Set
  Isuc Ipred : Int → Int
  _Imod_ _Idiv_ : Int → Int → Int

{-# COMPILE GHC Float = type Float #-}
{-# COMPILE GHC Double = type Double #-}
{-# COMPILE GHC Int = type Int #-}
{-# COMPILE GHC Integer = type Integer #-}
{-# COMPILE GHC Isuc = succ #-}
{-# COMPILE GHC Ipred = pred #-}
{-# COMPILE GHC _Imod_ = mod #-}
{-# COMPILE GHC _Idiv_ = div #-}
