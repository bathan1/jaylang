(** Redirect stdout to [/dev/null] and get back fd of stdout at call time. *)
let mute_stdout () =
 let devnull =
    Core_unix.openfile "/dev/null" ~mode:[Core_unix.O_WRONLY]
  in
  let saved = Core_unix.dup Core_unix.stdout in
  Core_unix.dup2 ~src:devnull ~dst:Core_unix.stdout ~close_on_exec:true ();
  Core_unix.close devnull;
  saved

(** "Unmutes" stdout by [dup2]ing STDOUT to SAVE_FD. *)
let unmute_stdout (save_fd : Unix.file_descr) =
  Core_unix.dup2 ~src:save_fd ~dst:Core_unix.stdout ();
  Core_unix.close save_fd

(** Get the average microseconds taken to run proc F over N trials labeled with human readable LABEL, muting [Benchmark]'s output to [stdout] when SILENT (default [true]). *)
let avg_latency_n
  ?(silent = true)
  (n : int64)
  ~(label : string)
  ~(f : unit -> unit)
  : float =
  let saved =
    if silent then Some (mute_stdout ())
    else None
  in
    Fun.protect
    ~finally:(fun () ->
      match saved with
      | Some fd -> unmute_stdout fd
      | None -> ()
    )
    (fun () ->
      [ (label, f, ()) ]
      |> Benchmark.latencyN n
      |> function
        | [ (_, [ t ]) ] ->
          t.Benchmark.wall *. 1_000_000.0 /. Int64.to_float n
        | _ -> failwith "Unexpected latencyN output"
    )
