module Perhaps
-- ==================
-- Defines the Perhaps data type for communicating a result 
-- of a computation or an error message in case of failure 

-- ==================
-- exec execloop look Perhaps

 where

import Control.Applicative
-- import qualified Control.Monad.Fail as Fail

data Perhaps a = Success a | Failure String
               deriving (Show, Eq)

instance Functor Perhaps where
  fmap f (Success a) = Success (f a)
  fmap f (Failure s) = Failure s

instance Applicative Perhaps where
  pure a = Success a

  Success f <*> a = fmap f a
  Failure s <*> _ = Failure s

  Success a *> b = b
  Failure s *> _ = Failure s
  
instance Monad Perhaps where
   px >>= f = case px of 
               {
                Success x -> f x;
                Failure s -> Failure s
               }
   return x = Success x
--   fail s   = Failure s

instance MonadFail Perhaps where
   fail s = Failure s

look :: (Eq a, Show a) => a -> [(a,b)] -> Perhaps b
look x []               = Failure ("not found:" ++ show x)
look x ((x0,y0):xys)    = if x == x0
                          then Success y0
                          else look x xys

exec :: (a -> IO ()) -> Perhaps a -> IO ()
exec f px = case px of
             {
              Success x -> f x ;
              Failure s -> putStrLn s
             }

execloop :: IO a -> (a -> Perhaps b) -> (b -> IO c) -> IO c
execloop act f g = do {
                        x <- act ;
                        case f x of
                          {
                           Success y -> g y ;
                           Failure s -> putStrLn s >> execloop act f g 
                          }
                       }
                       
