module Fst where
import qualified Main as M
import PrettyPrint
import Syntax
import Type
ppTy :: Type -> String
ppTy (TAtm (TCon c)) = c
ppTy (TAtm (TVar v)) = v
ppTy (TBin TCom a b) = "(" ++ ppTy a ++ " -> " ++ ppTy b ++ ")"
main :: IO ()
main = mapM_ (\(e,t) -> putStrLn (toCLI e ++ "  ::  " ++ ppTy t)) M.candidatosFst
