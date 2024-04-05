module Formula
-- ==================================
-- Defines data types for formulas and terms, 
-- performs operations with terms and variables 
-- in a formula and provides parsing for formulas 
-- using the parser combinators in the Parser module

-- ==================================
-- Term (Var Const) Formula (Atom And Bot Imp Or All Ex) FormulaS(AtomS OpS QuantS) Substitution

-- botstrings notstrings andstrings orstrings impstrings allstrings exstrings
-- botstr notstr andstr orstr impstr allstr exstr

-- vars fv free union unions remove substituteTerm freshVar addPrimes substituteFormula
-- compareVars compareTerms compareFVar compareF showTerm showTerms analyseFormula
-- matchVar matchTerm matchTerms matchFormula matchFormulas equalFormula matchtest matchVarFormula
-- isvarstring variable parseTerm parseTerms 
-- atomform botform basicform negation allquantifier exquantifier
-- logop1 logop2 logop2p inform insubform logop1form informp insubformp logo1ormp iform iformp 
-- logoppref logopinfix parseFormula forS showFormula showFormulas 

  where

import Parser
import Data.List (intercalate)
import System.IO.Unsafe (unsafePerformIO)
import qualified Data.Map.Strict as Map
import MapAux

data Term = Var String | Const String | Fun String [Term]
           deriving (Show,Eq)

data Formula = Atom String [Term]  
               | And Formula Formula
               | Or Formula Formula
               | Imp Formula Formula
               | Bot
               | All String Formula
               | Ex String Formula
           deriving (Show,Eq)

type Substitution = Map.Map String Term

instance Read Formula  where
--  readsPrec _ = runP iformp
--  readsPrec _ = runP iform
  readsPrec _ = runP parseFormula

instance Read Term where
--  readsPrec _ = runP iformp
--  readsPrec _ = runP iform
  readsPrec _ = runP parseTerm
                 
vars :: Term -> [String]
vars t = case t of
  {
   Var x    -> [x];
   Const _  -> [];
   Fun _ ts -> unions (map vars ts)
  }
  
-- free variables
fv :: Formula -> [String]
fv f = case f of
  {
   Atom w ts -> unions (map vars ts);
   And f1 f2 -> fv f1 `union` fv f2;
   Or f1 f2  -> fv f1 `union` fv f2;
   Imp f1 f2 -> fv f1 `union` fv f2;
   Bot       -> [];
   All x g   -> remove x (fv g);
   Ex x g    -> remove x (fv g)
  }
  
free :: String -> Formula -> Bool
free x f = x `elem` (fv f)

-- union of lists
-- append to xs all elements of ys that are not already in xs
union :: Eq a => [a] -> [a] -> [a]
union xs ys = xs ++ [y | y <- ys, not (y `elem` xs)]

unions :: Eq a => [[a]] -> [a]
unions []  = []
unions (xs:xss) = xs `union` unions xss

-- removes all x from xs
remove :: Eq a => a -> [a] -> [a]
remove x xs = [y | y <- xs, y /= x]

-- 
substituteTerm :: String -> Term -> Term -> Term
substituteTerm s newt targett = 
  case targett of
   {
    Const c -> targett;
    Var v -> if s == v then newt
             else targett;   
    Fun fun ts -> Fun fun (map (substituteTerm s newt) ts)
   }

-- generates a new variable name
freshVar :: String -> [String] -> String
freshVar v vs =
  if not (v `elem` vs)
     then v
  else
     let {
          freshVar' v vs n = if addPrimes v n `elem` vs 
                             then freshVar' v vs (n + 1)
                             else addPrimes v n
          }
     in freshVar' v vs 0
     
addPrimes :: String -> Int -> String
addPrimes v n = v ++ take n (repeat '\'')

substituteFormula :: String -> Term -> Formula -> Formula
substituteFormula s newt f =
  case f of
   {
    Atom w ts -> Atom w (map (substituteTerm s newt) ts);
    And f1 f2 -> And (substituteFormula s newt f1) (substituteFormula s newt f2);
    Or f1 f2  -> Or (substituteFormula s newt f1) (substituteFormula s newt f2);
    Imp f1 f2 -> Imp (substituteFormula s newt f1) (substituteFormula s newt f2);
    Bot       -> Bot;
    All x g   -> if s == x then All x g
                 else 
                   if x `elem` vars newt
                   then
                     let newx = freshVar x (union (vars newt) (fv g)) in
                     All newx (substituteFormula s newt (substituteFormula x (Var newx) g))
                   else All x (substituteFormula s newt g);
    Ex x g    -> if s == x then Ex x g
                 else
                   if x `elem` vars newt
                   then
                      let newx = freshVar x (union(vars newt) (fv g)) in
                      Ex newx (substituteFormula s newt (substituteFormula x (Var newx) g))
                   else Ex x (substituteFormula s newt g)
   }

-- comparison of formulas
compareVars :: [(String, String)] -> String -> String -> Bool
compareVars [] x y = x == y
compareVars ((x1, y1):xs) x2 y2 = 
   if x1 == x2 && y1 == y2
   then True
   else if x1 == x2 || y1 == y2
   then False
   else compareVars xs x2 y2
   

compareTerms :: [(String, String)] -> Term -> Term -> Bool
compareTerms l t1 t2 =
  case (t1, t2) of
   {
    (Const x, Const y) -> x == y;
    (Var x, Var y) -> compareVars l x y; -- t(x,y)
    (Fun fun1 ts1, Fun fun2 ts2) -> fun1 == fun2 && length ts1 == length ts2 &&
                                   (and [compareTerms l t1i t2i | (t1i, t2i) <- zip ts1 ts2]);
    _ -> False
   }
  
compareFVar :: [(String, String)] -> Formula -> Formula -> Bool
compareFVar l f g = 
  case (f, g) of
   {
    (Atom w1 ts1, Atom w2 ts2) ->
       if w1 == w2 && length ts1 == length ts2
       then and (zipWith (compareTerms l) ts1 ts2)
       else False;
    (And f1 f2, And g1 g2) -> compareFVar l f1 g1 && compareFVar l f2 g2;
    (Or f1 f2, Or g1 g2) -> compareFVar l f1 g1 && compareFVar l f2 g2;
    (Imp f1 f2, Imp g1 g2) -> compareFVar l f1 g1 && compareFVar l f2 g2;
    (Bot, Bot) -> True;
    (All x f1, All y g1) -> compareFVar ((x, y):l) f1 g1;
    (Ex x f1, Ex y g1) -> compareFVar ((x, y):l) f1 g1;
    _ -> False
   }
   
compareF :: Formula -> Formula -> Bool
compareF f1 f2 = compareFVar [] f1 f2

botstrings, notstrings, andstrings, orstrings, impstrings, allstrings, exstrings :: [String]
botstrings = ["bot", "\\bot", "Bot", "F", "_|_"] 
notstrings = ["not", "\\neg", "-"] 
andstrings = ["&", "and", "\\land"]
orstrings  = ["or", "|", "\\lor"]
impstrings = ["->", "\\to"]
allstrings = ["all", "All", "For all", "for all", "\\forall"]
exstrings = ["ex", "Ex", "Exists", "\\exists"]

botstr, notstr, andstr, orstr, impstr, allstr, exstr :: String
botstr = head botstrings
notstr = head notstrings
andstr = head andstrings
orstr  = head orstrings
impstr = head impstrings
allstr = head allstrings
exstr = head exstrings

{-
data HeadInfo = OpInfo String 
               | AtomInfo String [String]
               | QuantInfo String String
-}

showTerm :: Term -> String
showTerm t = case t of
   {
    Const c    -> c;
    Var x      -> x;
    Fun fun ts -> fun ++ " (" ++ (intercalate "," (map showTerm ts)) ++ ") "
   }
   
showTerms :: [Term] -> String
showTerms [] = []
showTerms (t:ts) = 
  "(" ++ showTerm t ++ concat ["," ++ showTerm s |  s <- ts] ++ ")"

analyseFormula :: Formula -> (String,[Formula])
analyseFormula f = case f of
  {
   Atom w ts   -> (w ++ showTerms ts, []);
   And f1 f2   -> (andstr,[f1,f2]);
   Imp f1 f2   -> (impstr,[f1,f2]);
   Or  f1 f2   -> (orstr ,[f1,f2]);
   Bot         -> (botstr,[]);
   All x f     -> (allstr ++ " " ++ x ++ ".", [f]);
   Ex x f      -> (exstr ++ " " ++ x ++ ".", [f])
  }
   
matchVar :: [(String, String)] -> String -> Term -> Maybe Substitution
matchVar [] x t = if t == Var x
                  then Just Map.empty else
                  Just (Map.singleton x t)
matchVar ((x1, y1):xs) x t =
   if x == x1 && t == Var y1
   then Just Map.empty
   else if x == x1 && t /= Var y1
   then Nothing
   else if x /= x1 && y1 `elem` vars t
   then Nothing
   else matchVar xs x t

matchTerm :: [(String, String)] -> Term -> Term -> Maybe Substitution
matchTerm l t1 t2 =
   case (t1, t2) of
    {
     (Const c, Const d)           -> if c == d then Just Map.empty else Nothing;
     (Var x, t)                   -> matchVar l x t;
     (Fun fun1 ts1, Fun fun2 ts2) -> if fun1 == fun2
                                     then matchTerms l ts1 ts2
                                     else Nothing;
      _                           -> Nothing
     }

matchTerms :: [(String, String)] -> [Term] -> [Term] -> Maybe Substitution
matchTerms l ts1 ts2 =
    if length ts1 == length ts2
    then do {
             thetas <- sequence [matchTerm l t1i t2i |
                                     (t1i, t2i) <- zip ts1 ts2];
             consistentUnions thetas
            }
    else Nothing

matchFormula :: [(String, String)] -> Formula -> Formula -> Maybe Substitution
matchFormula l f g =
   case (f, g) of
    {
     (Atom w1 ts1, Atom w2 ts2) -> if w1 == w2
                                   then matchTerms l ts1 ts2
                                   else Nothing;
     (And f1 f2, And g1 g2)     -> matchFormulas l [f1,f2] [g1,g2];
     (Or f1 f2, Or g1 g2)       -> matchFormulas l [f1,f2] [g1,g2];
     (Imp f1 f2, Imp g1 g2)     -> matchFormulas l [f1,f2] [g1,g2];
     (Bot, Bot)                 -> Just Map.empty;
     (All x f1, All y g1)       -> matchFormula ((x, y):l) f1 g1;
     (Ex x f1, Ex y g1)         -> matchFormula ((x, y):l) f1 g1;
     _                          -> Nothing
    }

matchFormulas :: [(String, String)] -> [Formula] -> [Formula] ->
                                                     Maybe Substitution
matchFormulas l fs gs =
    if length fs == length gs
    then do {
             thetas <- sequence [matchFormula l fi gi | (fi, gi) <- zip fs gs];
             consistentUnions thetas
            }
    else Nothing

-- alpha-equality of formulas expressed via matching
equalFormula :: Formula -> Formula -> Bool
equalFormula f g = case matchFormula [] f g of
                      {
                        Just theta -> Map.null theta;
                        Nothing    -> False
                      }

-- testing whether formula g is of the form substituteFormula x t f for some t
-- can be used to implement All-elimination rule backwards
matchtest :: String -> Formula -> Formula -> Bool
matchtest x f g = case matchFormula [] f g of
                   {
                     Nothing    -> False ;
                     Just theta -> all (== x) (Map.keys theta)
                   }
matchVarFormula :: String -> Formula -> Formula -> Maybe Term
matchVarFormula x f g = case matchFormula [] f g of
                   {
                     Just theta -> case Map.toList theta of
                                     {
                                       []      -> Just (Var "x") ;
                                       [(y,t)] -> if y == x
                                                  then Just t
                                                  else Nothing ;
                                       _       -> Nothing
                                     } ;
                     Nothing    -> Nothing
                   }

-- Parsing

-- terms

isvarstring :: String -> Bool
isvarstring w = head w `elem`"xyz"

variable :: Parser String
variable = do { w <- identifier ; if isvarstring w then return w else zero }

parseTerm :: [String] -> Parser Term
parseTerm xs = parseFun xs   -- xs = variable context 
               `plus` do { 
                           w <- identifier ; 
                           if w `elem` xs 
                           then return (Var w)
                           else return (Const w)
                         }

parseFun :: [String] -> Parser Term
parseFun xs = do { 
                   w <- identifier;
                   args <- bracket 
                             (char '(') 
                             (sepby (parse (token (char ','))) (parseTerm xs)) 
                             (char ')');
                   return (Fun w args)
                 }
               
parseTerms :: [String] -> Parser [Term]
parseTerms xs = inbrackets (sepby (parse (token (char ','))) (parseTerm xs)) 
                `plus`
                return []

{-
*Formula> runP0 parseFormula "P(John,x,y)->C"
Imp (Atom "P" [Const "John",Var "x",Var "y"]) (Atom "C" [])
-}
-- basic formulas

atomform :: [String] -> Parser Formula
-- atomform = do { w <- word ; return (Atom w) }
atomform xs = do { 
                   w <- identifier ; 
                   if not (w `elem` botstrings) 
                   then do {ts <- parseTerms xs; return (Atom w ts)} 
                   else zero
                 }

{-
*Formula> runP atomform "P(John,x,y)"
[(Atom "P" [Const "John",Var "x",Var "y"],"")]
-}
botform :: Parser Formula
botform = strings botstrings >> return Bot

basicform :: [String] -> Parser Formula
basicform xs = atomform xs `plus` botform

-- unary logical operators

negation, allquantifier, exquantifier :: Parser ([String],Formula -> Formula)
negation = strings notstrings >> return ([],`Imp` Bot)
allquantifier = do {
                    token (strings allstrings) ;
                    x <- token identifier ; 
                    return ([x],All x)
                   }
exquantifier = do {
                    token (strings exstrings) ;
                    x <- token identifier ; 
                    return ([x],Ex x)
                  }
logop1 :: Parser ([String],Formula -> Formula)
logop1 = token (plusss [negation,allquantifier,exquantifier])

-- binary logical operators

logop2 :: Parser (Formula -> Formula -> Formula)
logop2 = token ((strings andstrings >> return And)  `plusst` 
                (strings orstrings  >> return Or)   `plusst`
                (strings impstrings >> return Imp))

-- binary logical operators with priorities

logop2p :: Parser (Int,Formula -> Formula -> Formula)
logop2p = token ((strings andstrings >> return (10,And))  `plusst` 
                 (strings orstrings  >> return (9,Or))    `plusst`
                 (strings impstrings >> return (5,Imp)))


-- arbitrary infix formulas
                 
inform :: [String] -> Parser Formula
inform xs = logop1form xs `plusst` (insubform xs `chainr1` logop2)

insubform :: [String] -> Parser Formula
insubform xs = inbrackets (inform xs) `plusst` atomform xs

logop1form :: [String] -> Parser Formula
logop1form xs = token (do {(ys,f) <- logop1; 
                           sf <- insubform (xs ++ ys); 
                           return (f sf)})


-- arbitrary infix formulas with priorities
                 
informp :: [String] -> Parser Formula
informp xs = logop1formp xs `plusst` (insubformp xs `chainp` logop2p)

insubformp :: [String] -> Parser Formula
insubformp xs = inbrackets (informp xs) `plusst` atomform xs

logop1formp :: [String) -> Parser Formula
logop1formp xs = token (do {(ys,f) <- logop1; 
                            sf <- insubformp (xs ++ ys); 
                            return (f sf)})


-- ignoring leading spaces

iform :: Parser Formula
iform = parse (inform [])

iformp :: Parser Formula
iformp = parse (informp [])

logoppref :: Parser ([Formula] -> Formula, Int)
logoppref =  token (do {a <- basicform ; return (const a,0)}) `plus`
             do {(xs,f) <- logop1 ; return (f.head,1)} 
                                                

logopinfix :: [(Parser (Formula -> Formula -> Formula) , Int, Orientation)]
logopinfix = [(token (strings andstrings >> return And),3,R), 
              (token (strings orstrings  >> return Or) ,2,R), 
              (token (strings impstrings >> return Imp),1,R)] 

parseFormula :: Parser Formula
parseFormula = p1 (1,3) logoppref logopinfix


-- Showing

data FormulaS = AtomS String | OpS String [FormulaS] | QuantS String FormulaS

forS :: Formula -> FormulaS
forS f = case f of
   {
    Atom w ts  -> AtomS (fst (analyseFormula f));
    And f1 f2  -> OpS andstr (forS f1 : forSop andstr f2);
    Or  f1 f2  -> OpS orstr  (forS f1 : forSop orstr  f2);
    Imp f1 f2  -> OpS impstr (forS f1 : forSop impstr f2);
    Bot        -> AtomS botstr;
    All x g    -> QuantS (fst (analyseFormula f)) (forS g);
    Ex x g     -> QuantS (fst (analyseFormula f)) (forS g)
   }
  where

   forSop :: String -> Formula -> [FormulaS]
   forSop op f = let (op',fs) = analyseFormula f 
                 in if op' == op
                    then forS (fs !! 0) : forSop op (fs !! 1)
                    else [forS f]
    
showFormula :: Formula -> String
showFormula f = showFormulaS (forS f) "" where

  showFormulaS :: FormulaS -> String -> String
  showFormulaS (AtomS  w)  str = w ++ str
  showFormulaS (OpS op fs) str = showFormulaSop op fs str
  showFormulaS (QuantS s f) str = s ++ showFormulaS f str

  showFormulaSop :: String -> [FormulaS] -> String -> String      
  showFormulaSop op [f]    str = showFormulaSB f str
  showFormulaSop op (f:fs) str = showFormulaSB f (" " ++ op ++ " " ++ showFormulaSop op fs str)

  showFormulaSB :: FormulaS -> String -> String
  showFormulaSB (AtomS w) str = w ++ str
  showFormulaSB f         str = "(" ++ showFormulaS f (")" ++ str)


