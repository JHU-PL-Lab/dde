open Logs

(* controls whether to generate logs:
   "logs" in _build/default/program_analysis/tests *)
let gen_logs = ref false
let debug_plain msg = if !gen_logs then debug (fun m -> m msg)
let debug msg = if !gen_logs then debug msg
let info_plain msg = if !gen_logs then info msg
let info msg = if !gen_logs then info msg
