module Step
-- ======================
-- Defines data types of a rule, a state of a proof; 
-- executes user commands, etc.

-- ======================

-- Introduce list of variables as extra component of State
-- type State = (Output,IPS,PlProof,[String],Int)

-- Rule(AssuR AndiR AndelR AnderR OrilR OrirR OreR ImpiR ImpeR EfqR RaaR AlliR AlleR ExiR ExeR)
-- Input(TextI RuleI)
-- Assi
-- Output(OkO StartO ErrorO CompleteO Unsound)
-- Err(IncorrectFormE NoTextExpE UnknownAssuE RuleNotApplicableE ProofCompleteE TextExpE)
-- IPS(OkS StartS CompleteS UseS ImpiS ImpeS AndelS AnderS OreS AlleS AlliS ExiS ExeS)
-- State 

-- startState startPP rep step steps check unsound unsounds counterexamples mkimps atoms 
-- val allassis pmap app union completeCheck newGoalSymbols startGoalSymbol 
-- readFormula readTerm useF useT startProcess

-- A set of functions *Process (* stands for use, andel, ander, ore, impi, impe, alle, exi)
-- startProcess useProcess andelProcess anderProcess impeProcess oreProcess 
-- alleProcess exiProcess exeProcess

-- A set of functions *RuleAp (* stands for andi, oril, orir, efq, raa, alli)
-- andiRuleAp orilRuleAp orirRuleAp efqRuleAp raaRuleAp alliRuleAp


  where

import Perhaps
import Parser
import Formula hiding (union)
import Proof
import Buss
import Occ
-- import InteractiveProof

import System.IO.Unsafe

data Rule = AssuR 
          | AndiR | AndelR | AnderR 
          | OrilR | OrirR  | OreR 
          | ImpiR | ImpeR  
          | EfqR  | RaaR  
          | AlliR | AlleR | AlleRF
          | ExiR  | ExeR
  deriving (Show, Read)


data Input = TextI String | RuleI Rule 
  deriving (Show, Read)
{-
data Output = OkO | StartO | ErrorO Err | CompleteO
  deriving (Show, Read)
-}

type Assi = [(String,Bool)] -- Assignment

data Output = OkO | StartO | ErrorO Err | CompleteO | Unsound [(Goal,Assi)]
  deriving (Show, Read)


-- !! data Err = IncorrectFormE | NoTextExpE | UnknownAssuE | RuleNotApplicableE
data Err = IncorrectTermE |IncorrectFormE | NoTextExpE | UnknownAssuE | RuleNotApplicableE
         | ProofCompleteE | TextExpE | RefinementE String
  deriving (Show, Read)

data IPS = OkS | StartS | CompleteS   -- Interactive Proof State
         | UseS | ImpiS | ImpeS | AndelS | AnderS | OreS 
         | AlleS | AlleSF | ExiS | ExeS
  deriving (Show, Read)
  
-- !! type State = (Output,IPS,PlProof,Int)
-- Introduce list of variables as extra component
type State = (Output,IPS,PlProof,[String],Int)

startState :: State
-- !! startState = (StartO,StartS,startPP,0)
startState = (StartO,StartS,startPP,[],0)

startPP :: PlProof
startPP = start startGoalSymbol (Atom "X" [])

rep :: (a -> b -> b) -> [a] -> b -> b
rep f (x:xs) y = rep f xs (f x y)
rep f []     y = y
-- rep f xs y = (flip (foldr f) (reverse xs) y

steps :: [Input] -> State -> State
steps = rep step


step :: Input -> State -> State
-- !! step inp state@(out,ips,pp,n) = 
step inp state@(out,ips,pp,xs,n) = 
--  unsafePerformIO $ do { 
--  putStrLn $ show inp ++ "  " ++ (show state); 
--  putStrLn (show state');
--  return $ check state' }
     check state'
  where
   state' =
     case inp of
       TextI s     -> 
         let {s0 = unwords (words s)} 
                     -- removes excess spaces, i.p. leading & trailing ones 
         in case ips of
            {
             StartS     -> useF startProcess s0 state; 
-- useF: use string s0 as formula
-- !!             OkS        -> (ErrorO NoTextExpE,ips,pp,n);
             OkS        -> (ErrorO NoTextExpE,ips,pp,xs,n);
             UseS       -> useProcess s0 state;
             ImpiS      -> impiProcess s0 state;
             ImpeS      -> useF impeProcess s0 state; 
             AndelS     -> useF andelProcess s0 state;
             AnderS     -> useF anderProcess s0 state;
             OreS       -> useF oreProcess s0 state;
             AlleSF     -> useF alleFProcess s0 state;
             AlleS      -> useT alleProcess s0 state;
             ExiS       -> useT exiProcess s0 state;
-- useT: use string s0 as term
             ExeS       -> useF exeProcess s0 state;
-- !!             CompleteS  -> (ErrorO ProofCompleteE,ips,pp,n)
             CompleteS  -> (ErrorO ProofCompleteE,ips,pp,xs,n)
            }
       RuleI rule  ->
         case ips of
-- !!       CompleteS -> (ErrorO ProofCompleteE,ips,pp,n)
          CompleteS -> (ErrorO ProofCompleteE,ips,pp,xs,n)
          _         -> 
            case rule of
             {
              AssuR  -> (OkO,UseS,pp,xs,n);
              AndiR  -> andiRuleAp state;
              AndelR -> (OkO,AndelS,pp,xs,n);
              AnderR -> (OkO,AnderS,pp,xs,n);
              OrilR  -> orilRuleAp state;
              OrirR  -> orirRuleAp state;
              OreR   -> (OkO,OreS,pp,xs,n);
              ImpiR  -> (OkO,ImpiS,pp,xs,n);
              ImpeR  -> (OkO,ImpeS,pp,xs,n);
              EfqR   -> efqRuleAp state;
              RaaR   -> raaRuleAp state;
              AlliR  -> alliRuleAp state;
              AlleR  -> (OkO,AlleS,pp,xs,n);
              AlleRF -> (OkO,AlleSF,pp,xs,n);
              ExiR   -> (OkO,ExiS,pp,xs,n); 
              ExeR   -> (OkO,ExeS,pp,xs,n) 
             }  
-- check :: State - > State
check :: State -> State
-- !! check state@(out,ips,pp,n) =
check state@(out,ips,pp,xs,n) =
       if null (goalstack pp) 
-- !!       then (OkO,CompleteS,pp,xs,n) 
       then (OkO,CompleteS,pp,xs,n) 
       else state
-- switch off unsound
--       else case unsounds pp of 
--              {
--               []       -> state ;
--                _       -> (Unsound (unsounds pp), ips, pp, xs, n)
--              }   


unsounds :: PlProof -> [(Goal,Assi)]
unsounds (goals, gamma, _) = 
  pmap unsound [(assu,gamma' ++ gamma) | (assu,gamma') <- goals ]

unsound :: Goal -> Maybe (Goal,Assi)
unsound goal@((u,f),gamma) 
  = case counterexamples (mkimps (map snd gamma) f) of
     {
       (alpha:_)  -> Just (goal,alpha) ;
       []         -> Nothing
     } 

counterexamples :: Formula -> [Assi]
counterexamples f = filter (not . val f) (allassis (atoms f))

mkimps :: [Formula] -> Formula -> Formula
mkimps []     f = f
mkimps (g:gs) f = Imp g (mkimps gs f) 

atoms :: Formula -> [String]
atoms (Atom a [])  = [a] 
atoms (Atom _ _) = []
atoms (And f g) = atoms f `union` atoms g
atoms (Or  f g) = atoms f `union` atoms g
atoms (Imp f g) = atoms f `union` atoms g
atoms Bot       = []
atoms (All x g) = atoms g
atoms (Ex x g) = atoms g

val :: Formula -> Assi -> Bool
val f assi = case f of
               {
                 Atom a []  -> app assi a ; 
                 Atom _ _   -> True ; -- !!!!!!!CHECK THIS
                 And f1 f2  -> val f1 assi && val f2 assi ;
                 Or  f1 f2  -> val f1 assi || val f2 assi ;
                 Imp f1 f2  -> not (val f1 assi) || val f2 assi ;
                 Bot        -> False;
                 All x g    -> val g assi;
                 Ex x g     -> val g assi
               }

allassis :: [String] -> [Assi]
allassis []     = [[]]
allassis (x:xs) = [ (x,b):alpha | b <- [True,False] , alpha <- allassis xs]


pmap :: (a -> Maybe b) -> [a] -> [b]
pmap f xs = [ y | Just y <- map f xs ]

app :: (Eq a, Show a) => [(a,b)] -> a -> b 
app xys x = case lookup x xys of 
             {
             Just y -> y ; 
              _ -> error ("app: " ++ show x)
             } 
            
union :: Eq a => [a] -> [a] -> [a]
union xs ys = xs ++ [y | y <- ys, not (y `elem` xs)]
                
completeCheck :: State -> State
-- !! completeCheck state@(out,ips,pp,n) =
completeCheck state@(out,ips,pp,xs,n) =
-- !!  if null (goalstack pp) then (OkO,CompleteS,pp,n) else state  
  if null (goalstack pp) then (OkO,CompleteS,pp,xs,n) else state  

newGoalSymbols :: Int -> Int -> [String]
newGoalSymbols n k = ["?" ++ show (n+i) | i <- [1..k]] 

startGoalSymbol :: String
startGoalSymbol = head (newGoalSymbols (-1) 1)
      
readFormula :: String -> Perhaps Formula
readFormula str = 
   case [f | (f,"") <- reads str] of
    {
     (f:_) -> return f;
     _     -> fail "Incorrrect formula, try again!"
    }
     
readTerm :: String -> Perhaps Term
readTerm str = 
   case [t | (t,"") <- reads str] of
    { 
     (t:_) -> return t;
     _     -> fail "Incorrrect term, try again!"
    }

useF :: (Formula -> State -> State) -> 
          String -> State -> State 
useF process str state@(out,ips,pp,xs,n) = 
  case readFormula str of
   {
    Success f -> process (activateFormula xs f) state;
    Failure _ -> (ErrorO IncorrectFormE, ips, pp,xs, n)
   }

useT :: (Term -> State -> State) -> 
          String -> State -> State 
useT process str state@(out,ips,pp,xs,n) = 
  case readTerm str of
   {
    Success t -> process (activateTerm xs t) state;
    Failure _ -> (ErrorO IncorrectTermE, ips, pp, xs, n)
   }
-- Formula is the missing formula   

startProcess :: Formula -> State -> State
startProcess f _ = 
  (OkO, OkS, start (head (newGoalSymbols (-1) 1)) f, [], 0)

-- processes for the step function 
useProcess :: AnVar -> State -> State
useProcess av (out,ips,pp,xs,n) =
  case refine pp (AssumptBW av) of
   {
    Success pp' -> (OkO,OkS,pp', xs, n);
    Failure _   -> (ErrorO UnknownAssuE,ips,pp,xs,n)
   }

andelProcess :: Formula -> State -> State
andelProcess f (out,ips,pp,xs,n) =
  let { [gl] = newGoalSymbols n 1 }
  in case refine pp (AndElilBW gl f) of 
   { 
    Success pp' -> (OkO,OkS, pp', xs, n+1);
    Failure s   -> error s -- should never be called
   }
      
anderProcess :: Formula -> State -> State
anderProcess f (out,ips,pp,xs,n) = 
  let { [gl] = newGoalSymbols n 1 }
  in case refine pp (AndElirBW gl f) of
   {   
    Success pp' -> (OkO, OkS, pp',xs, n+1);
    Failure s   -> error s -- should never be called
   }
      
oreProcess :: Formula -> State -> State
oreProcess f (out,ips,pp,xs,n) =
  let { [gl1,gl2,gl3] = newGoalSymbols n 3 }
  in case refine pp (OrElimBW gl1 gl2 gl3 f) of
   {
    Success pp' -> (OkO,OkS, pp',xs, n+3);
    Failure _   -> (ErrorO IncorrectFormE,ips,pp,xs,n)
   }   
impiProcess :: AnVar -> State -> State
impiProcess av (out,ips,pp,xs,n) =
  let { [gl] = newGoalSymbols n 1 }
  in case refine pp (ImpIntrBW gl av) of
   {
    Success pp' -> (OkO,OkS, pp',xs, n+1);
    Failure _   -> (ErrorO RuleNotApplicableE,ips,pp,xs,n) 
   }
  
impeProcess :: Formula -> State -> State
impeProcess f (out,ips,pp,xs,n) = 
  let { [gl1,gl2] = newGoalSymbols n 2 }
  in case refine pp (ImpElimBW gl1 gl2 f) of
   {
    Success pp' -> (OkO,OkS, pp',xs, n+2);
    Failure s   -> error s -- should never be called
   }
 

alleProcess :: Term -> State -> State
alleProcess t (out,ips,pp,xs,n) = 
    case currentGoal pp of
     {
      Success cg ->
        let { 
              g = assumpt_formula (goal_assumpt cg) ;
              x = case t of { Var x -> x ; _ -> freshVarF g } 
            }
        in case antisubstFAll t x g of
         {
          Just f -> let { [gl] = newGoalSymbols n 1} 
            in case refine pp (AllElimBW gl (All x f) t) of 
             {
              Success pp' -> (OkO,OkS, pp',xs, n+1);
              Failure _   -> (ErrorO IncorrectFormE,ips,pp,xs,n)
             }; 
          Nothing -> (ErrorO IncorrectFormE,ips,pp,xs,n)
         };
      Failure _ -> error ("No current goal.")
     };
 

alleFProcess :: Formula -> State -> State
alleFProcess f (out,ips,pp,xs,n) = case f of
  {
   All s f1 -> 
    case currentGoal pp of
     {
      Success cg ->
        let g = assumpt_formula (goal_assumpt cg)
        in case matchVarFormula s f1 g of
         {
          Just t -> let { [gl] = newGoalSymbols n 1} 
            in case refine pp (AllElimBW gl f t) of 
             {
              Success pp' -> (OkO,OkS, pp', s:xs, n+1);
              Failure _   -> (ErrorO IncorrectFormE,ips,pp,xs,n)
             }; 
          Nothing -> (ErrorO IncorrectFormE,ips,pp,xs,n)
         };
      Failure _ -> error ("No current goal.")
     };
   _ -> (ErrorO IncorrectFormE,ips,pp,xs,n)
  }
 
 
exiProcess :: Term -> State -> State
exiProcess t (out,ips,pp,xs,n) = 
  let { [gl] = newGoalSymbols n 1}
  in case refine pp (ExIntrBW gl t) of 
   {
    Success pp' -> (OkO,OkS, pp',xs, n+1);
    Failure s   -> (ErrorO (RefinementE s),ips,pp,xs,n)
   }    
exeProcess :: Formula -> State -> State
exeProcess f (out,ips,pp,xs,n) = 
  let { [gl1,gl2] = newGoalSymbols n 2}
  in case refine pp (ExElimBW gl1 gl2 f) of 
   {
    Success pp' -> (OkO,OkS, pp', xs, n+2);
    Failure s   -> (ErrorO (RefinementE s),ips,pp,xs,n)
   }   
-- rules application for the step function
andiRuleAp :: State -> State
andiRuleAp (out,ips,pp,xs,n) =                 
  let { [gl1,gl2] = newGoalSymbols n 2 }
  in case refine pp (AndIntrBW gl1 gl2) of
   {
    Success pp' -> (OkO,OkS,pp',xs,n+2);
    Failure _   -> (ErrorO RuleNotApplicableE,ips,pp,xs,n)
   }
   
orilRuleAp :: State -> State
orilRuleAp (out,ips,pp,xs,n) =
  let { [gl] = newGoalSymbols n 1 }
  in case refine pp (OrIntrlBW gl) of
   {
    Success pp' -> (OkO,OkS,pp',xs,n+1);
    Failure _   -> (ErrorO RuleNotApplicableE,ips,pp,xs,n)
   }
          
orirRuleAp :: State -> State
orirRuleAp (out,ips,pp,xs,n) =
  let { [gl] = newGoalSymbols n 1 }
  in case refine pp (OrIntrrBW gl) of
   {
    Success pp' -> (OkO,OkS,pp',xs,n+1);
    Failure _   -> (ErrorO RuleNotApplicableE,ips,pp,xs,n)
   }
   
efqRuleAp :: State -> State
efqRuleAp (out,ips,pp,xs,n) =
  let { [gl] = newGoalSymbols n 1 }
  in case refine pp (ExFQBW gl) of
   {
    Success pp' -> (OkO,OkS,pp',xs,n+1);
    Failure s   -> error s -- should never be called
   }
            
raaRuleAp :: State -> State
raaRuleAp (out,ips,pp,xs,n) =
  let { [gl] = newGoalSymbols n 1 }
  in case refine pp (ReAABW gl) of
   {
    Success pp' -> (OkO,OkS,pp',xs,n+1);
    Failure s   -> error s -- should never be called
   }

alliRuleAp :: State -> State
alliRuleAp (out,ips,pp,xs,n) =             
  let { 
        [gl] = newGoalSymbols n 1 ;
        ((a0,c0):gs,ctx,p) = pp ;
        x    = case assumpt_formula a0 of { All v _ -> v ; _ -> "xxx" }
      }        -- hack!
  in case refine pp (AllIntrBW gl) of
   {
    Success pp' -> (OkO,OkS,pp',x:xs,n+1);
    Failure _   -> (ErrorO RuleNotApplicableE,ips,pp,xs,n)
   }
