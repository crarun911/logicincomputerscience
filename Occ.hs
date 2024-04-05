module Occ

where

import Parser
import Data.List (intercalate)
import System.IO.Unsafe (unsafePerformIO)
import qualified Data.Map.Strict as Map
import MapAux
import Formula
-- import State
import Control.Applicative
import Control.Monad (liftM, ap)
-- import qualified Control.Monad.State.Lazy as S
-- import qualified Control.Monad.ST.Lazy as S
-- import qualified Control.Monad.Trans.State.Lazy as S
-- import qualified Control.Monad.State as S


{-
newtype State s a = State {

    runState' :: s -> (#a, s#)

}
get :: State s s
gets :: (s -> a) -> State s a
put :: s -> State s ()
modify :: (s -> s) -> State s ()
evalState :: State s a -> s -> a
-}

newtype St s a = S (s -> (a,s))

get :: St s s
get = S (\s -> (s,s))

put :: s -> St s ()
put s = S (\_ -> ((),s))

evalSt :: St s a -> s -> a
evalSt (S f) s = fst (f s) 

instance Monad (St s) where
  return a = S (\s -> (a,s))
  S f >>= g = S (\s -> let {(a,s') = f s ; S f' = g a } in f' s')

instance Functor (St s) where
  fmap = liftM
instance Applicative (St s) where
  pure = return
  (<*>) = ap


replaceTCond :: (Int -> Bool) -> Term -> Term -> Term -> St Int Term
replaceTCond test old new = stc 
   where 
     stc t = if t == old
             then do { 
                       s <- get ; let {s' = s + 1} ; put s' ;
                       return (if test s' then new else t)
                     } 
             else case t of
                   {
                     Fun f ts -> do { 
                                      ts' <- sequence (map stc ts) ; 
                                      return (Fun f ts')
                                    } ; 
                     _        -> return t
                   }

replaceFCond :: (Int -> Bool) -> Term -> Term -> Formula -> St Int Formula
replaceFCond test old new = sfc 
  where 
   stc = replaceTCond test old new
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

-- replaceOcc [1,3] old new t = 
-- replace in t the first and third occurrence of old by new (from left to right)
replaceTOcc :: [Int] -> Term -> Term -> Term -> Term
replaceTOcc is old new t = evalSt (replaceTCond (`elem` is) old new t) 0

replaceTAll :: Term -> Term -> Term -> Term
replaceTAll old new t = evalSt (replaceTCond (return True) old new t) 0

replaceFOcc :: [Int] -> Term -> Term -> Formula -> Formula 
replaceFOcc is old new f = evalSt (replaceFCond (`elem` is) old new f) 0

replaceFAll :: Term -> Term -> Formula -> Formula
replaceFAll old new f = evalSt (replaceFCond (return True) old new f) 0

antisubstFOcc :: [Int] -> Term -> String -> Formula -> Maybe Formula
antisubstFOcc is old x f =
     let {
           g  = replaceFOcc is old (Var x) f ;
           f' = substituteFormula x old g
         }
     in if equalFormula f f' then Just g else Nothing

antisubstFAll :: Term -> String -> Formula -> Maybe Formula
antisubstFAll old x f =
     let {
           g  = replaceFAll old (Var x) f ;
           f' = substituteFormula x old g
         }
     in if equalFormula f f' then Just g else Nothing

-- all variables of a formula, free and bound
fbv :: Formula -> [String]
fbv f = case f of
  {
   Atom w ts -> unions (map vars ts);
   And f1 f2 -> fbv f1 `union` fbv f2;
   Or f1 f2  -> fbv f1 `union` fbv f2;
   Imp f1 f2 -> fbv f1 `union` fbv f2;
   Bot       -> [];
   All x g   -> [x] `union` (fbv g);
   Ex x g    -> [x] `union` (fbv g)
  }


antisubstFOccDefault :: [Int] -> Term -> Formula -> Maybe (String,Formula)
antisubstFOccDefault is old f =
     let {
           x  = freshVar "x" (fbv f) ;
           g  = replaceFOcc is old (Var x) f ;
           f' = substituteFormula x old g
         }
     in if equalFormula f f' then Just (x,g) else Nothing


{-  
Example s
*Occ> let t = Fun "f" [Fun "g" [Var "z"], Var "x", Fun "g" [Var "z"]]
*Occ> let old = Fun "g" [Var "z"]
*Occ> let new = Var "y"
*Occ> replaceTOcc [1,2] old new t 
Fun "f" [Var "y",Var "x",Var "y"]
*Occ> replaceTOcc [1] old new t 
Fun "f" [Var "y",Var "x",Fun "g" [Const "c"]]
*Occ> replaceTOcc [2] old new t 
Fun "f" [Fun "g" [Const "c"],Var "x",Var "y"]
*Occ> replaceTOcc [] old new t 
Fun "f" [Fun "g" [Const "c"],Var "x",Fun "g" [Const "c"]]
*Occ> replaceTAll old new t 
Fun "f" [Var "y",Var "x",Var "y"]

*Occ> let f = And (All "x" (Atom "P" [Fun "f" [Var "x",Var "y"]])) (Ex "y" (Atom "P" [Fun "f" [Var "x",Var "y"]]))
*Occ> antisubstFOcc [1] (Var "x") "z" f
Nothing
*Occ> antisubstFOcc [2] (Var "x") "z" f
Just (And (All "x" (Atom "P" [Fun "f" [Var "x",Var "y"]])) (Ex "y" (Atom "P" [Fun "f" [Var "z",Var "y"]])))
*Occ> antisubstFOcc [1] (Var "y") "z" f
Just (And (All "x" (Atom "P" [Fun "f" [Var "x",Var "z"]])) (Ex "y" (Atom "P" [Fun "f" [Var "x",Var "y"]])))
*Occ> antisubstFOcc [2] (Var "y") "z" f
Nothing
*Occ> antisubstFOcc [2] (Var "x") "y" f
Nothing
-}
