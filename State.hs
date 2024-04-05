-- State Monad

module State

where

newtype S s a = S (s -> (a,s)) 

run :: S s a -> s -> (a,s)
run (S f) = f

instance Monad (S s) where
  return x0 = S (\s -> (x0,s)) 
  x >>= f = S(\s -> let {(x0,s') = run x s} in run (f x0) s')    

get :: S s a -> s -> a
get x = fst . run x  

move :: (s -> s) -> S s a -> S s a
move next x = S(run x . next) 

mfun :: (s -> a) -> S s a
mfun f = S(\s -> (f s,s))

--

mif :: Monad m => m Bool -> m a -> m a -> m a
mif b x y = do { b0 <- b ; if b0 then x else y }

{-
Relation to Control.Monad.State.Lazy (https://wiki.haskell.org/State_Monad)

State    Control.Monad.State.Lazy      

S         State
run       runState
mfun      gets
get       evalState
-}


