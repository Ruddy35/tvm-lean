import TvmLean.Model
import TvmLean.Semantics.Exec.Common
import TvmLean.Semantics.Exec.Stack
import TvmLean.Semantics.Exec.Cont
import TvmLean.Semantics.Exec.Cell
import TvmLean.Semantics.Exec.Flow
import TvmLean.Semantics.Exec.Arith
import TvmLean.Semantics.Exec.Tuple
import TvmLean.Semantics.Exec.CellOp
import TvmLean.Semantics.Exec.TonEnv
import TvmLean.Semantics.Exec.Crypto
import TvmLean.Semantics.Exec.Msg
import TvmLean.Semantics.Exec.Misc
import TvmLean.Semantics.Exec.Debug
import TvmLean.Semantics.Exec.Exception
import TvmLean.Semantics.Exec.Dict

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstr (i : Instr) : VM Unit :=
  execInstrStack i <|
    execInstrCont i <|
      execInstrCell i <|
        execInstrFlow i <|
          execInstrArith i <|
            execInstrTuple i <|
              execInstrCellOp i <|
                execInstrTonEnv i <|
                  execInstrCrypto i <|
                    execInstrMsg i <|
                      execInstrMisc i <|
                      execInstrDebug i <|
                      execInstrException i <|
                        execInstrDict i <|
                          VM.unimplementedInstr { name := Instr.pretty i } "no exec handler"

end TvmLean
