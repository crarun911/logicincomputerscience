module MapAux
-- ====================
-- Enhances existing Map library with utility functions 

-- ====================

where 

import Control.Applicative
import qualified Data.Map.Strict as Map


consistentUnion :: (Ord k, Eq a) => Map.Map k a -> Map.Map k a -> 
                                                      Maybe (Map.Map k a)
consistentUnion m1 m2 = let {m = m1 `Map.union` m2} 
                        in if Map.isSubmapOf m1 m  && Map.isSubmapOf m2 m  
                           then Just m
                           else Nothing

consistentUnions :: (Ord k, Eq a) => [Map.Map k a] -> Maybe (Map.Map k a)
consistentUnions ms = let {m = Map.unions ms} 
                      in if and [Map.isSubmapOf mi m | mi <- ms]
                         then Just m
                         else Nothing

{-
*Main> consistentUnions (map Map.fromList [[(3,4)],[(3,3)],[(2,6)]])
Nothing
*Main> consistentUnions (map Map.fromList [[(3,4)],[(3,4)],[(2,6)]])
Just (fromList [(2,6),(3,4)])
-}
