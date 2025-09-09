module type Core = sig
  type 'a t

  val return : 'a -> 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val prod : 'a t -> 'b t -> ('a * 'b) t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
end

module type S = sig
  include Core

  module LetSyntax : sig
    val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t
    val ( and+ ) : 'a t -> 'b t -> ('a * 'b) t
    val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  end
end

module Make (C : Core) : S with type 'a t = 'a C.t = struct
  include C

  module LetSyntax = struct
    let ( let+ ) m f = map f m
    let ( and+ ) = prod
    let ( let* ) = bind
  end
end

module Identity : sig
  include S with type 'a t = private 'a

  val run : 'a t -> 'a
end = struct
  include Make (struct
    type 'a t = 'a

    let return x = x
    let map f m = f m
    let prod m1 m2 = m1, m2
    let bind m f = f m
  end)

  let run m = m
end

module type StateType = sig
  type t
end

module State (T : StateType) : sig
  type s = T.t

  include S with type 'a t = private s -> 'a * s

  val get : s t
  val put : s -> unit t
  val modify : (s -> s) -> unit t
  val gets : (s -> 'a) -> 'a t
  val run : 'a t -> s -> 'a * s
end = struct
  type s = T.t

  include Make (struct
    type 'a t = s -> 'a * s

    let return x s = x, s

    let map f m s =
      let x, s = m s in
      f x, s

    let prod m1 m2 s =
      let x, s = m1 s in
      let y, s = m2 s in
      (x, y), s

    let bind m f s =
      let x, s = m s in
      f x s
  end)

  let get s = s, s
  let put s _ = (), s
  let modify f s = (), f s
  let gets f s = f s, s
  let run m s = m s
end
