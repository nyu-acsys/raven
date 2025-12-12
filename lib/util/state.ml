open Base

(*type ('a, 'b) t = 'a -> 'a * 'b*)

let return a s = (s, a)

module Syntax = struct
  (* For ppx_let *)

  let return = return

  module Let_syntax = struct
    let bind m ~f sin =
      let sout, res = m sin in
      f res sout

    let return a s = return

    let map m ~f sin =
      let sout, res = m sin in
      (sout, f res)

    let both m1 m2 sin =
      let s1, res1 = m1 sin in
      let s2, res2 = m2 s1 in
      (s2, (res1, res2))
  end

  open Let_syntax

  let ( let+ ) (m : 'c -> 'c * 'a) (f : 'a -> 'b) :
      'c -> 'c * 'b =
    map m ~f

  let ( and+ ) = both

  let ( let* ) (m : 'c -> 'c * 'a)
      (f : 'a -> 'c -> 'c * 'b) : 'c -> 'c * 'b =
    bind m ~f

  let ( and* ) = both

  let ( |+> ) m f = map m ~f

  let ( |*> ) (m : 'c -> 'c * 'a) f = bind m ~f

  let get_state s = (s, s)

  let set_state s' _ = (s', ())

  let map_state ~f s = (f s, ())
end

let eval m s = m s

module List = struct
  let map (xs : 'a list) ~(f : 'a -> 'c -> 'c * 'b) : 'c -> 'c * 'b list =
   fun s -> List.fold_map xs ~init:s ~f:(fun s x -> f x s)

  let map2 (xs : 'a list) (ys : 'b list) ~f s =
    match List.zip xs ys with
    | Ok xs_ys ->
        let s, res = List.fold_map xs_ys ~init:s ~f:(fun s (x, y) -> f x y s) in
        (s, Base.List.Or_unequal_lengths.Ok res)
    | Unequal_lengths -> (s, Unequal_lengths)

  let map2_exn (xs : 'a list) (ys : 'b list) ~f s =
    match map2 xs ys ~f s with
    | (s, Base.List.Or_unequal_lengths.Ok zs) -> (s, zs)
    | _ -> failwith "State.List.map2 unequal length"

  let fold_right (xs : 'a list) ~(init : 'b) ~f : 'c -> 'c * 'b =
   fun s -> List.fold_right xs ~f:(fun x (s, acc) -> f x acc s) ~init:(s, init)

  let fold_left (xs : 'a list) ~(init : 'b) ~f : 'c -> 'c * 'b =
   fun s -> List.fold_left xs ~f:(fun (s, acc) x -> f acc x s) ~init:(s, init)

  let fold_map xs ~init ~f s =
    let (s, acc), ys =
      List.fold_map xs ~init:(s, init) ~f:(fun (s, acc) x ->
          let s, (acc, y) = f acc x s in
          ((s, acc), y))
    in
    (s, (acc, ys))

  let fold2 (xs : 'a list) (ys : 'b list) ~(init : 'acc) ~f :
      ('c -> 'c * 'acc Base.List.Or_unequal_lengths.t) =
   fun s ->
    match List.zip xs ys with
    | Ok xs_ys ->
        let s, res =
          List.fold_left xs_ys ~init:(s, init) ~f:(fun (s, acc) (x, y) ->
              f acc x y s)
        in
        (s, Base.List.Or_unequal_lengths.Ok res)
    | Unequal_lengths -> (s, Unequal_lengths)

  let iter xs ~f s =
    ( List.fold_left xs ~init:s ~f:(fun s x ->
          let res, () = f x s in
          res),
      () )

  let exists xs ~f =
    let rec ex xs s =
      match xs with
      | [] -> (s, false)
      | x :: ys ->
          let s, b = f x s in
          if b then (s, b) else ex ys s
    in
    ex xs

  let for_all xs ~f =
    let rec ex xs s =
      match xs with
      | [] -> (s, true)
      | x :: ys ->
          let s, b = f x s in
          if b then ex ys s else (s, b)
    in
    ex xs
end
