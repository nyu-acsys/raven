open Base
    
module type Vertex = sig
  type t
  val hash: t -> int

  include Comparable.S with type t := t
  include Sexpable.S with type t := t
  
end

module Make(V: Vertex) = struct

  module VertexSet = Set.M(V)
  
  module VertexMap = Map.M(V)

  module H = Hashtbl.M(V)
      
  type t = VertexSet.t * VertexSet.t VertexMap.t

  let vertices (vs, _) = vs

  let empty_vertex_set = Set.empty (module V)
  let empty_vertex_map = Map.empty (module V)
  
  let empty =
    empty_vertex_set, empty_vertex_map

  let add_vertex (vs, es) v = (Set.add v vs, Map.add ~key:v ~data:empty_vertex_set es)
      
  let add_edge (vs, es) src dst =
    (vs,
     Map.update es src ~f:(fun old_dsts_opt ->
         let old_dsts = Option.value old_dsts_opt ~default:empty_vertex_set in
         Set.add old_dsts dst))

  let add_edges (vs, es) src dsts =
    (vs, Map.update es src ~f:(fun old_dsts_opt ->
         let old_dsts = Option.value old_dsts_opt ~default:empty_vertex_set in
         Set.union old_dsts dsts))
       
  let topsort ((vs, es): t) : V.t list list =
    let index = ref 0 in
    let indexes = Hashtbl.create (module V) in
    let lowlinks = Hashtbl.create (module V) in
    let s = Stack.create () in
    
    let rec tarjan (sccs: V.t list list) (v: V.t) = 
      Hashtbl.set indexes ~key:v ~data:!index;
      Hashtbl.set lowlinks ~key:v ~data:!index;
      Int.incr index;
      let succs = Map.find_exn es v in
      Stack.push s v;
      begin
        let sccs1: V.t list list = Set.fold
            ~f:(fun sccs v' ->
              if not (Hashtbl.mem indexes v') then (
                let sccs1 = tarjan sccs v' in
                Hashtbl.set lowlinks ~key:v ~data:(min (Hashtbl.find_exn lowlinks v) (Hashtbl.find_exn lowlinks v'));
                sccs1
               ) else begin 
                 if Stack.exists s ~f:(fun y -> V.(v' = y)) then
                   Hashtbl.set lowlinks ~key:v ~data:(min (Hashtbl.find_exn lowlinks v) (Hashtbl.find_exn indexes v'));
                 sccs
               end
            ) succs ~init:sccs
        in
        if Hashtbl.find_exn lowlinks v = Hashtbl.find_exn indexes v 
        then begin
          let rec loop acc = 
            let v' = Stack.pop_exn s in
            if V.(v = v') then v' :: acc
            else loop (v' :: acc)
          in
          (loop []) :: sccs1
        end
        else sccs1
      end
    in
    let sccs =
      Set.fold
        ~f:(fun sccs v ->   
          if not (Hashtbl.mem indexes v)
          then tarjan sccs v
          else sccs
        ) vs ~init:[]
    in
    List.rev sccs
end
