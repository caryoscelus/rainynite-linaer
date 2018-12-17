{-- Util.hs - basic util functions which probably belong elsewhere
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

{-# LANGUAGE
  NoMonomorphismRestriction,
  ScopedTypeVariables,
  TypeFamilies,
  LambdaCase,
  GADTs,
  FlexibleContexts
  #-}

module Util where

foreverTil :: Monad m => m Bool -> m a -> m a
foreverTil cond m = do
  r <- m
  e <- cond
  if not e then
    foreverTil cond m
  else
    pure r

modifyAt :: Int -> (a -> a) -> [a] -> [a]
modifyAt n f l = take n l <> [f (l !! n)] <> drop (n + 1) l
