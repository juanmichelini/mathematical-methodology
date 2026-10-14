module Conj where
import qualified Main as M
import PrettyPrint
import Syntax
import Type
import Prove
import Propose
import Util
import Data.List
ppTy :: Type -> String
ppTy (TAtm (TCon c)) = c
ppTy (TAtm (TVar v)) = v
ppTy (TBin TCom a b) = "(" ++ ppTy a ++ " -> " ++ ppTy b ++ ")"
ppAff :: Affirm -> String
ppAff (Affirm vts l r) = intercalate " " [v ++ ":" ++ ppTy t | (v,t) <- vts] ++ " |- " ++ toCLI l ++ " = " ++ toCLI r
main :: IO ()
main = mapM_ (\(i,(f,t)) -> do
    putStrLn ("## cand " ++ show i)
    let batches = plemas [(Var "f", f)] ((Atm (Var "f"), t) : M.cerothTEnv) M.datas M.paciencia M.cerothRec (Var "f")
    mapM_ (\(j,b) -> do putStrLn ("# batch " ++ show j); mapM_ (putStrLn . ppAff) b) (zip [0::Int ..] batches)
  ) (zip [0::Int ..] M.candidatosFst)
