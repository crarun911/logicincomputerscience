module SystemL   
-- ================
-- Operating system interface implementation for Linux

-- ================
-- displayPP helpDoc watchPP

  where

-- import GHC.IOBase
import GHC.IO
-- import System.Cmd  -- deprecated
import System.Process
import System.Exit

-- displayPP:: IO GHC.IOBase.ExitCode
-- displayPP:: IO GHC.IO.Exception.ExitCode
-- displayPP = system "latex pproof.tex > /dev/null"
-- displayPP = system "latex pproof.tex"

-- syscopy :: String -> String -> IO GHC.IO.Exception.ExitCode
syscopy src dest = system $ "cp " ++ src ++ " " ++ dest

-- runlatex filename = system ("pdflatex " ++ filename ++ " > /dev/null") 
-- runpdflatex filename = system ("pdflatex " ++ filename ++ " > /dev/null") 

-- watchPP :: IO GHC.IOBase.ExitCode
-- watchPP :: IO GHC.IO.Exception.ExitCode
-- watchPP   = system "xdvi -watchfile 1 pproof.dvi &"

-- helpDoc :: IO GHC.IOBase.ExitCode
-- helpDoc :: IO GHC.IO.Exception.ExitCode
-- helpDoc   = system "xdvi help.dvi &"






