open Core

let () =
  let dir = ref "" in
  Arg.parse [ ("-dir", Arg.Set_string dir, "") ] (fun _ -> ()) "";
  Sys_unix.ls_dir !dir
  |> List.map ~f:(Filename.concat !dir)
  |> List.map ~f:(fun fname -> (fname, Core.In_channel.read_lines fname))
  |> List.map ~f:(fun (fname, ls) ->
         ( String.drop_suffix fname 31,
           let runtime =
             ls
             |> List.map ~f:String.lowercase
             |> List.filter ~f:(fun l ->
                    String.is_prefix l ~prefix:"analysis r")
           in
           assert (List.length runtime = 1);
           runtime |> List.hd_exn
           |> String.chop_prefix_if_exists ~prefix:"analysis ran for: "
           |> String.chop_prefix_if_exists ~prefix:"analysis run for: "
           |> String.chop_suffix_if_exists ~suffix:"ms"
           |> String.chop_suffix_if_exists ~suffix:" milliseconds"
           |> Int.of_string ))
  |> List.sort ~compare:(fun (fname1, _) (fname2, _) ->
         String.ascending fname1 fname2)
  |> List.group ~break:(fun (fname1, _) (fname2, _) ->
         String.(fname1 <> fname2))
  |> List.map ~f:(fun group ->
         group |> List.unzip |> fun (fnames, runtimes) ->
         ( List.hd_exn fnames,
           runtimes |> List.map ~f:Float.of_int
           |> List.fold ~init:0. ~f:( +. )
           |> Fn.flip ( /. ) (runtimes |> List.length |> Float.of_int) ))
  |> List.iter ~f:(fun (fname, runtime) ->
         Format.printf "%s: %f\n" fname runtime)
