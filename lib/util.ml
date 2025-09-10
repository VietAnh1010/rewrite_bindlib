open Syntax

module type MakeMSHType = sig
  type t

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
end

module MakeMSH (T : MakeMSHType) = struct
  module M = Map.Make (T)
  module S = Set.Make (T)
  module H = Hashtbl.Make (T)
end

module IntMSH = MakeMSH (Int)
module IntMap = IntMSH.M
module IntSet = IntMSH.S
module IntHashtbl = IntMSH.H
module MetavarMSH = MakeMSH (Metavar)
module MetavarMap = MetavarMSH.M
module MetavarSet = MetavarMSH.S
module MetavarHashtbl = MetavarMSH.H
module SymbolMSH = MakeMSH (Symbol)
module SymbolMap = SymbolMSH.M
module SymbolSet = SymbolMSH.S
module SymbolHashtbl = SymbolMSH.H
