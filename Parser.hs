module Parser
-- =====================
-- A library of monadic parser combinators

-- =====================

-- alphanum bind bracket chainr1 chainp char digit first 
-- ident identifier inbrackets infi infixL infixN infixR item 
-- letter lower many many1 nat neword Orientation  
-- P parse Parser(P) parseStrings pl plus pluss plusss plusst prefix 
-- runP result sat spaces spacesOnly string strings times token 
-- upper word zero 

 where

import qualified Control.Applicative as Appl
import Control.Monad

data Parser a = P (String -> [(a,String)]) 

runP :: Parser a -> String -> [(a,String)]
runP (P f) = f 

runP0 :: Parser a -> String -> a
runP0 (P f) inp = 
  let { res = f inp } 
  in case [x | (x,"") <- res] of 
        { 
          (x:_) ->  x ; 
           _    ->  error ("runP0: " ++ show (map snd res))
        }
result :: a -> Parser a
result v = P (\inp -> [(v,inp)])

bind :: Parser a -> (a -> Parser b) -> Parser b
p `bind` f = 
  P (\inp -> concat [runP (f v) inp' | (v,inp') <- runP p inp])

bind_ :: Parser a -> Parser b -> Parser b
p `bind_` q = p `bind` \_ -> q

zero :: Parser a
zero = P (\inp -> [])

plus :: Parser a -> Parser a -> Parser a
p `plus` q = P (\inp -> (runP p inp ++ runP q inp))

item :: Parser Char
item = P (\inp -> case inp of 
                  {
                   [] -> []; 
                   (x:xs) -> [(x,xs)]
                  })
               
sat :: (Char -> Bool) -> Parser Char
sat test = item `bind` \x -> if test x then result x else zero

char :: Char -> Parser Char
char x = sat (x ==)

instance Functor Parser where
  fmap f (P fa) = P ((map (\(a, s) -> (f a, s))) . fa)
  
instance Appl.Applicative Parser where
     pure = result
     (<*>) = ap
     m *> k = bind m (\_ -> k)
     
instance Monad Parser where
     return = result
     (>>=)  = bind

-- some further basic parsers 

string :: String -> Parser String
string ""     = return ""
string (x:xs) = do {char x; string xs; return (x:xs)}

digit, lower, upper, letter, alphanum :: Parser Char
digit = sat (\c ->  '0' <= c && c <= '9')
lower = sat (\c ->  'a' <= c && c <= 'z')
upper = sat (\c ->  'A' <= c && c <= 'Z')
letter = lower `plus` upper
alphanum = letter `plus` digit


-- iteration

many :: Parser a -> Parser [a]
many p = do {x<- p; xs <- many p; return (x:xs)} `plus` 
         do {string ""; return []}

many1 :: Parser a -> Parser [a]
many1 p = do {x<- p; xs<- many p; return (x:xs)}


-- iteration, a fixed number of times

times :: Int -> Parser a -> Parser [a]
times n p = if n <= 0 
            then return []
            else do {x <- p ; xs <- times (n-1) p ; return (x:xs)}


-- words, identifiers, numbers 
 
word :: Parser String
word = many letter

neword :: Parser String
neword = many1 letter

ident :: Parser String
ident = do {x<- lower; xs <- many alphanum; return (x:xs)}

identifier :: Parser String
identifier = do {
                  xs <- neword; 
                  us  <- many (char '_'); 
                  ys <- many alphanum; 
                  zs <- many (char '\'');
                  let {
                        ys' = if null us || null ys 
                              then ys 
                              else ("_{" ++ ys ++ "}")
                      } ;
                  return (xs ++ ys' ++ zs)
                }

nat :: Parser Int
nat = do {xs <- many1 digit; return (read xs)}


-- only first result (improves efficiency)

first :: Parser a -> Parser a
first p = P (\inp-> case runP p inp of 
                     {
                      [] -> []; 
                      (x:xs) -> [x]
                     })

pluss :: Parser a -> Parser a -> Parser a
p `pluss` q = first (p `plus` q)

-- running a list of parsers in parallel

plusss :: [Parser a] -> Parser a
plusss = foldr plus zero


-- ignoring space

spaces :: Parser ()
spaces = do {many1 (sat (`elem` " \n\t")); return ()}

parse, token :: Parser a -> Parser a
parse p = do {many spaces; p}
token p = do {x<- p; many spaces; return x}

plusst :: Parser a -> Parser a -> Parser a
p `plusst` q = token (p `pluss` q)

strings :: [String] -> Parser String
strings strs = plusss (map string strs)

parseStrings :: [String] -> Parser String
parseStrings strs = plusss (map (parse . string) strs)

spacesOnly :: String -> Bool
spacesOnly = and . map (== ' ') 

-- chaining, right associative

chainr1 :: Parser a -> Parser (a -> a -> a) -> Parser a
p `chainr1` op = 
  do {x<- p; 
      do {f<- op; y<- p `chainr1` op; return (f x y)} `pluss` return x
     }

-- chaining, with priorities

chainp :: Parser a -> Parser (Int,(a -> a -> a)) -> Parser a
p `chainp` op = 
  do { 
       x<- p; 
       do { 
            (n,f)<- op; 
            do { 
                 y<- p ; 
                 (m,g) <- op; 
                 z <- p `chainp` op; 
                 return (if n<m then (x `f` (y `g` z)) 
                                else ((x `f` y) `g` z))
               } 
            `pluss`
            do {(_,f)<- op; y<- p ; return (f x y)}
          } 
       `pluss` 
       return x
      }
      
  

-- bracketing


bracket :: Parser a -> Parser b -> Parser c -> Parser b
-- bracket open p close = do {open; x<- p; close; return x}
bracket open p close = do {token open; x<- p; close; return x}

inbrackets :: Parser a -> Parser a
inbrackets p =  bracket (char '(') p (char ')') `plusst`
                bracket (char '[') p (char ']') `plusst`
                bracket (char '{') p (char '}') 


-- separation by symbol (comma, semicolon, etc.)

sepby :: Parser b -> Parser a -> Parser [a]
sepby sep p =
  do { 
       x <- p ;
       do { sep; xs <- sepby sep p; return (x:xs)} `pluss` return [x] }
-- prefix with fixed arity

prefix :: Parser ([a] -> b , Int) -> Parser a -> Parser b
prefix pref p = do { (f,n) <- pref ; as <- n `times` p ; return (f as) }

-- infix, not associative

infixN :: Parser (a -> b -> c) -> Parser a -> Parser b -> Parser c
infixN inf p q = do { x <- p ; f <- inf ; y <- q ; return (f x y) }


-- infix, left associative

infixL :: Parser (a -> b -> a) -> Parser a -> Parser b -> Parser a
infixL inf p q = p >>= aux   where

-- aux :: a -> Parser a
   aux x = do { f <- inf ; y <- q ; aux (f x y) `plus` return (f x y) }


-- infix, right associative

infixR :: Parser (a -> b -> b) -> Parser a -> Parser b -> Parser b
infixR inf p q = do { x <- p ; f <- inf ; 
                      y <- (infixR inf p q `plus` q) ; return (f x y) }

-- infix, any orientation

data Orientation = N | L | R

infi :: Orientation -> 
         Parser (a -> a -> a) -> Parser a -> Parser a -> Parser a
infi o = case o of {N -> infixN ; L -> infixL ; R -> infixR}


-- a parser for 
-- * prioritised infix operations, each either left assoc, right assoc, 
--   or without assoc
-- * prefix operations, each with with fixed arity and with higher priority
--   than any infix operation 
-- * disambiguation by parentheses

-- Example: if A,B,C,D,E are nullary, ! is unary, ->, |, & are 
-- infix prioritised in that order, -> right assoc, |, & left assoc, then
-- !!(!A->B&C|D|E) parses to !(!(->(!(A),|(|(&(B,C),D),E)))) 

p1 :: (Int,Int) -> 
      Parser ([a] -> a, Int) -> 
      [(Parser (a -> a -> a) , Int, Orientation)] ->  
         Parser a
p1 (minBind,maxBind) pref infs = pup minBind  

 where

-- pup :: Int -> Parser a
   pup k = plusss (brack : ppref : 
             [pinf p n o | (p,n,o) <- infs , n >= k, n <= maxBind ])   

-- brack :: Parser a
   brack = inbrackets (pup minBind)

-- ppref :: Parser a
   ppref = prefix pref (brack `plus` ppref)


-- pinf :: Parser a -> Int -> Orientation -> Parser a
   pinf p n o = let {q = pup (n+1)} in infi o p q q


----------------------------------------
-- Substitution

copy :: Parser String
copy = P(\inp -> [(inp,"")])

(+++) :: Parser String -> Parser String -> Parser String
p +++ q = do { str1 <- p ; str2 <- q ; return (str1 ++ str2) }

shift :: Parser String -> Parser String
shift p = do { c <- item ; str <- p ; return (c:str) }

replacefront1 :: (String,String) -> Parser String
replacefront1 (old,new) = do {string old ; return new} 

replacefront :: [(String,String)] -> Parser String
replacefront subst = first (plusss (map replacefront1 subst))

repl :: [(String,String)] -> Parser String
repl subst =
  (replacefront subst +++ repl subst)
  `pluss`
  shift (repl subst)
  `pluss` 
  copy

{-
runP (repl [("#name","Berger"),("#stno","123")]) "Author: #name (#stno)"
[("Author: Berger (123)","")]
-}

{-
replace :: [(String,String)] -> Parser String
replace subst =
  do {str1 <- replacefront subst ; str2 <- replace subst ; return (str1 ++ str2)}
  `pluss`
  do {c <- item ; str <- replace subst ; return (c:str)}
  `pluss` 
  copy
-}
