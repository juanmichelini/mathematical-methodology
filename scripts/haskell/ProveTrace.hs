-- provell with a trace, for the first-search candidates: for every conjecture that is
-- actually tried, the smallest paciencia at which `prove` completes it (or "fail").
-- Ground truth for Strategic/FindLemmas.lean.  The logic of provellT is Prove.provell's.
module ProveTrace where
import qualified Main as M
import PrettyPrint
import Syntax
import Type
import Prove
import Propose
import Compute (Env)
import Data.List
import Data.Maybe

ppTy :: Type -> String
ppTy (TAtm (TCon c)) = c
ppTy (TAtm (TVar v)) = v
ppTy (TBin TCom a b) = "(" ++ ppTy a ++ " -> " ++ ppTy b ++ ")"

ppAff :: Affirm -> String
ppAff (Affirm vts l r) = intercalate " " [v ++ ":" ++ ppTy t | (v,t) <- vts] ++ " |- " ++ toCLI l ++ " = " ++ toCLI r

need :: Env -> [DatasH] -> Rec -> Affirm -> String
need env ds rec c = case find (\n -> proofCompleto (prove n ds env rec c)) [1..60] of
                      Nothing -> "fail"
                      Just n -> show n

provellT :: Env -> [DatasH] -> Int -> Rec -> [[Affirm]] -> IO [Proof]
provellT env ds n rec [] = return []
provellT env ds n rec (ls:lls) = do
  let ls' = filter (isNothing . applyRec env rec) ls
      ps = map (prove n ds env rec) ls'
  mapM_ (\(c,p) -> putStrLn ("  " ++ (if proofCompleto p then "OK   " else "fail ") ++ need env ds rec c ++ " " ++ ppAff c)) (zip ls' ps)
  case find proofCompleto ps of
    Nothing -> do putStrLn "# none"; provellT env ds n rec lls
    Just k -> do putStrLn ("# chose " ++ ppAff (headProof k))
                 r <- provellT env ds n (addAffirms env rec [headProof k]) lls
                 return (k:r)

main :: IO ()
main = mapM_ (\(i,(f,t)) -> do
    let env = [(Var "f", f)]
        tenv = (Atm (Var "f"), t) : M.cerothTEnv
        batches = plemas env tenv M.datas M.paciencia M.cerothRec (Var "f")
    putStrLn ("## cand " ++ show i)
    ps <- provellT env M.datas M.paciencia M.cerothRec batches
    let ref = findlemas env tenv M.datas M.paciencia M.cerothRec (Var "f")
    if map headProof ps == map headProof ref then putStrLn ("# lemmas " ++ show (length ps)) else error "provellT differs from findlemas"
  ) (zip [0::Int ..] M.candidatosFst)
