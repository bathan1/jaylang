external ffi_empty : unit -> unit = "ffi_empty"

let () =
    let n = 50_000_000 in
    let t0 = Unix.gettimeofday () in
    for _ = 1 to n do
        Sys.opaque_identity (ffi_empty ())
    done;
    let t1 = Unix.gettimeofday () in
    Printf.printf "Calls: %d  Time: %.3fs  ns/call: %.1f\n"
    n (t1 -. t0) (1e9 *. (t1 -. t0) /. float n)