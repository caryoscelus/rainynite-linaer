{-- FCLabels.agda - some bindings to FCLabels
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

module FCLabels where
{-# FOREIGN GHC
    import Data.Label
  #-}

postulate
  _፦_ : (F A : Set) → Set
  set : {A F : Set} (lens : F ፦ A) → A → F → F
  get : {A F : Set} (lens : F ፦ A) → F → A

{-# COMPILE GHC _፦_ = type (:->) #-}
{-# COMPILE GHC set = \_ _ -> set #-}
{-# COMPILE GHC get = \_ _ -> get #-}
