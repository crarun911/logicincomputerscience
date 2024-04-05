module SystemW
-- ================
-- Operating system interface implementation for Windows

-- ================
-- displayPP helpDoc watchPP

  where

--import GHC.IOBase
import GHC.IO
import System.Process
import System.Exit

displayPP :: IO String -- :: IO System.Exit.ExitCode
displayPP = readProcess "latex" ["pproof.tex"] "" -- system "latex pproof.tex"

-- syscopy :: String -> String -> IO GHC.IO.Exception.ExitCode
syscopy src dest = system $ "copy " ++ src ++ " " ++ dest

runlatex filename = system ("pdflatex " ++ filename ++ " > NUL") 
runpdflatex filename = system ("pdflatex " ++ filename ++ " > NUL") 

watchPP, helpDoc :: IO ()
watchPP   = return ()
helpDoc   = return () 


