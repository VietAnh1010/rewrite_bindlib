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

module MetaMSH = MakeMSH (Meta)
module MetaMap = MetaMSH.M
module MetaSet = MetaMSH.S
module MetaHashtbl = MetaMSH.H

module SymbolMSH = MakeMSH (Symbol)
module SymbolMap = SymbolMSH.M
module SymbolSet = SymbolMSH.S
module SymbolHashtbl = SymbolMSH.H
