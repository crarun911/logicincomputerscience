module Occ

where

import Parser
import Data.List (intercalate)
import System.IO.Unsafe (unsafePerformIO)
import qualified Data.Map.Strict as Map
import MapAux
import Formula
import State

type SI = S Int

substTCond :: SI Bool -> Term -> Term -> Term -> SI Term
substTCond test old new = stc 
   where 
     stc t = if t == old
                then move (+1) (mif test (return new) (return t))
                else case t of
                      {
                        Fun f ts -> do { 
                                         ts' <- sequence (map stc ts) ; 
                                         return (Fun f ts')
                                       } ; 
                        _        -> return t
                      }

substFCond :: SI Bool -> Term -> Term -> Formula -> SI Formula
substFCond test old new = sfc 
  where 
   stc = substTCond test old new
   sfc f = case f of
             {
               Atom p ts -> do { 
                                 ts' <- sequence (map stc ts) ; 
                                 return (Atom p ts')
                               } ;
               Or f g    -> do { f' <- sfc f ; g' <- sfc g ; return (Or f' g') } ;
               And f g   -> do { f' <- sfc f ; g' <- sfc g ; return (And f' g') } ;
               Imp f g   -> do { f' <- sfc f ; g' <- sfc g ; return (Imp f' g') } ;
               Bot       -> return Bot ;
               All x f   -> do { f' <- sfc f ; return (All x f') } ;
               Ex x f    -> do { f' <- sfc f ; return (Ex x f') }
             }

-- substOcc [1,3] old new t = 
-- replace in t the first and third occurrence of old by new (from left to right)
substTOcc :: [Int] -> Term -> Term -> Term -> Term
substTOcc is old new t = get (substTCond (mfun (`elem` is)) old new t) 0

substTAll :: Term -> Term -> Term -> Term
substTAll old new t = get (substTCond (return True) old new t) 0

substFOcc :: [Int] -> Term -> Term -> Formula -> Formula 
substFOcc is old new f = get (substFCond (mfun (`elem` is)) old new f) 0

substFAll :: Term -> Term -> Formula -> Formula
substFAll old new f = get (substFCond (return True) old new f) 0


 
