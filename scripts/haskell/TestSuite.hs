-- foundations Test.hs: the 35 hand-written lemmas (each proved with lemascomp and the
-- lemmas before it as hypotheses: Test.provelemas) with the smallest budget at which each
-- is proved, and the lemma chains found for the functions of Test.env (suma; mult with the
-- lemmas of suma; flipexp with those of mult; min; max; absr; and; or; not; concat; rev with
-- those of concat), with finished-proof counts.  Ground truth for Examples/TestSuite.lean.
module TestSuite where
import qualified Test as T
import PrettyPrint
import Syntax
import Type
import Prove
import Propose
import Data.List
import Data.Maybe

ppTy :: Type -> String
ppTy (TAtm (TCon c)) = c
ppTy (TAtm (TVar v)) = v
ppTy (TBin TCom a b) = "(" ++ ppTy a ++ " -> " ++ ppTy b ++ ")"

ppAff :: Affirm -> String
ppAff (Affirm vts l r) = intercalate " " [v ++ ":" ++ ppTy t | (v,t) <- vts] ++ " |- " ++ toCLI l ++ " = " ++ toCLI r

dones :: Proof -> Int
dones PDone = 1
dones PFail = 0
dones (PStep _ _ p) = dones p
dones (PInd _ _ cs) = sum [dones p | (_, (_, p)) <- cs]

need :: Rec -> Affirm -> String
need rec c = case find (\n -> proofCompleto (prove n T.datas T.env rec c)) [1..60] of
               Nothing -> "fail"
               Just n -> show n

chain :: String -> [Proof] -> IO ()
chain name ps = do
  putStrLn ("## " ++ name)
  mapM_ (putStrLn . ("lemma " ++) . ppAff . headProof) ps
  putStrLn ("done " ++ show (sum (map dones ps)))

main :: IO ()
main = do
  putStrLn ("## lemas " ++ show (length T.lemas))
  mapM_ (\(n, l) -> do
      let rec = addAffirms T.env emptyRec (T.lemascomp ++ take n T.lemas)
          p = prove 30 T.datas T.env rec l
      putStrLn ((if proofCompleto p then "OK   " else "fail ") ++ need rec l ++ " " ++ ppAff l)
    ) (zip [0..] T.lemas)
  chain "suma" T.lsumad
  chain "mult" T.lmultd
  chain "flipexp" T.lexpd
  chain "min" T.lmind
  chain "max" T.lmaxd
  chain "absr" T.labsrd
  chain "and" T.landd
  chain "or" T.lord
  chain "not" T.lnotd
  chain "concat" T.lconcatd
  chain "rev" T.lrevd
