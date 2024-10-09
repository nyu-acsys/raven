open Base

module type Vertex = sig
  type t

  val hash : t -> int

  include Comparable.S with type t := t
  include Sexpable.S with type t := t
end

(*module type Graph = sig
    type vertex
    type t

    module VertexSet = Set.M(String)
    module VertexMap = Set.M(String).t

    type t = VertexSet.t * VertexSet.t VertexMap.t

  end*)

module Make (V : Vertex) = struct
  module VertexSet = Set.M (V)
  module VertexMap = Map.M (V)
  module H = Hashtbl.M (V)

  type vertex = V.t
  type t = VertexSet.t * VertexSet.t VertexMap.t

  let vertices (vs, _) = vs
  let empty_vertex_set = Set.empty (module V)
  let empty_vertex_map = Map.empty (module V)
  let empty = (empty_vertex_set, empty_vertex_map)

  let add_vertex (vs, es) (v : vertex) : t =
    (Set.add vs v, Map.add_exn ~key:v ~data:empty_vertex_set es)

  let add_edge (vs, es) (src : vertex) (dst : vertex) : t =
    ( Set.add vs src,
      Map.update es src ~f:(fun old_dsts_opt ->
          let old_dsts = Option.value old_dsts_opt ~default:empty_vertex_set in
          Set.add old_dsts dst) )

  let add_edges (vs, es) (src : vertex) dsts : t =
    ( Set.add vs src,
      Map.update es src ~f:(fun old_dsts_opt ->
          let old_dsts = Option.value old_dsts_opt ~default:empty_vertex_set in
          Set.union old_dsts dsts) )

  let union (vs1, es1) (vs2, es2) =
    Set.union vs1 vs2,
    Map.merge es1 es2 ~f:(fun ~key m ->
        Map.Merge_element.values m ~left_default:empty_vertex_set ~right_default:empty_vertex_set
        |> (fun (e1, e2) -> Some (Set.union e1 e2)))
  
  let succs (vs, es) v : VertexSet.t =
    Map.find es v |> Option.value ~default:empty_vertex_set
  
  let targets (vs, es) : VertexSet.t =
    Map.fold es ~f:(fun ~key ~data -> Set.union data) ~init:empty_vertex_set

  let pr pr_v ppf (vs, es) =
    let pr_es ppf (v, vs) = Stdlib.Format.fprintf ppf "%a -> %a" pr_v v (Print.pr_list_comma pr_v) (Set.elements vs) in
    Print.pr_list_nl pr_es ppf (Map.to_alist es)

  
  let topsort ((vs, es) : t) : V.t list list =
    let index = ref 0 in
    let indexes = Hashtbl.create (module V) in
    let lowlinks = Hashtbl.create (module V) in
    let s = Stack.create () in

    let rec tarjan (sccs : V.t list list) (v : V.t) =
      Hashtbl.set indexes ~key:v ~data:!index;
      Hashtbl.set lowlinks ~key:v ~data:!index;
      Int.incr index;
      let succs = Map.find es v |> Option.value ~default:empty_vertex_set in
      Stack.push s v;
      let sccs1 : V.t list list =
        Set.fold
          ~f:(fun sccs v' ->
            if not (Hashtbl.mem indexes v') then (
              let sccs1 = tarjan sccs v' in
              Hashtbl.set lowlinks ~key:v
                ~data:
                  (min
                     (Hashtbl.find_exn lowlinks v)
                     (Hashtbl.find_exn lowlinks v'));
              sccs1)
            else (
              if Stack.exists s ~f:(fun y -> V.(v' = y)) then
                Hashtbl.set lowlinks ~key:v
                  ~data:
                    (min
                       (Hashtbl.find_exn lowlinks v)
                       (Hashtbl.find_exn indexes v'));
              sccs))
          succs ~init:sccs
      in
      if Hashtbl.find_exn lowlinks v = Hashtbl.find_exn indexes v then
        let rec loop acc =
          let v' = Stack.pop_exn s in
          if V.(v = v') then v' :: acc else loop (v' :: acc)
        in
        loop [] :: sccs1
      else sccs1
    in
    let sccs =
      Set.fold
        ~f:(fun sccs v ->
          if not (Hashtbl.mem indexes v) then tarjan sccs v else sccs)
        vs ~init:[]
    in
    List.rev sccs
end
