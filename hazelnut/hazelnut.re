open Sexplib.Std;
open Monad_lib.Monad; // Uncomment this line to use the maybe monad

let compare_string = String.compare;
let compare_int = Int.compare;

module Htyp = {
  [@deriving (sexp, compare)]
  type t =
    | Arrow(t, t)
    | Num
    | Hole;
};

module Hexp = {
  [@deriving (sexp, compare)]
  type t =
    | Var(string)
    | Lam(string, t)
    | Ap(t, t)
    | Lit(int)
    | Plus(t, t)
    | Asc(t, Htyp.t)
    | EHole
    | NEHole(t);
};

module Ztyp = {
  [@deriving (sexp, compare)]
  type t =
    | Cursor(Htyp.t)
    | LArrow(t, Htyp.t)
    | RArrow(Htyp.t, t);
};

module Zexp = {
  [@deriving (sexp, compare)]
  type t =
    | Cursor(Hexp.t)
    | Lam(string, t)
    | LAp(t, Hexp.t)
    | RAp(Hexp.t, t)
    | LPlus(t, Hexp.t)
    | RPlus(Hexp.t, t)
    | LAsc(t, Htyp.t)
    | RAsc(Hexp.t, Ztyp.t)
    | NEHole(t);
};

module Child = {
  [@deriving (sexp, compare)]
  type t =
    | One
    | Two;
};

module Dir = {
  [@deriving (sexp, compare)]
  type t =
    | Child(Child.t)
    | Parent;
};

module Shape = {
  [@deriving (sexp, compare)]
  type t =
    | Arrow
    | Num
    | Asc
    | Var(string)
    | Lam(string)
    | Ap
    | Lit(int)
    | Plus
    | NEHole;
};

module Action = {
  [@deriving (sexp, compare)]
  type t =
    | Move(Dir.t)
    | Construct(Shape.t)
    | Del
    | Finish;
};

module TypCtx = Map.Make(String);
type typctx = TypCtx.t(Htyp.t);

exception Unimplemented;

let rec erase_exp = (e: Zexp.t): Hexp.t => {
  switch(e) {
    | Cursor(t) => t;
    | Lam(s, t) => Hexp.Lam(s, erase_exp(t));
    | LAp(t, ht) => Hexp.Ap(erase_exp(t), ht);
    | RAp(ht, t) => Hexp.Ap(ht, erase_exp(t));
    | LPlus(t, ht) => Hexp.Plus(erase_exp(t), ht);
    | RPlus(ht, t) => Hexp.Plus(ht, erase_exp(t));
    | LAsc(t, ht) =>  Hexp.Asc(erase_exp(t), ht);
    | RAsc(ht, t) => Hexp.Asc(ht, erase_type(t));
    | NEHole(t) => Hexp.NEHole(erase_exp(t));
  }
}
and erase_type = (t: Ztyp.t): Htyp.t => {
    switch(t) {
    | Cursor(t) => t;
    | LArrow(t, ht) =>  Htyp.Arrow(erase_type(t), ht);
    | RArrow(ht, t) => Htyp.Arrow(ht, erase_type(t));
    }

};
let extract_arrow_components = (t: Htyp.t): option((Htyp.t, Htyp.t)) =>
  switch (t) {
    | Arrow(t1, t2) => Some((t1, t2))
    | _ => None
  };

let rec syn = (ctx: typctx, e: Hexp.t): option(Htyp.t) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  switch(e){
    // Rule 1a
    | Var(name) => TypCtx.find_opt(name, ctx) 
    // Rule 1b
    | Ap(e1, e2) => {
      let* t1 = syn(ctx, e1);
      let* arrowed_t2_and_t =  mat(t1);
      let* (t2, t) = extract_arrow_components(arrowed_t2_and_t);
      ana(ctx, e2, t2) ? Some(t) : None;
      }
    // Rule 1c
    | Lit(_) => Some(Num)
    // Rule 1d
    | Plus(e1, e2) => (ana(ctx, e1, Num) && ana(ctx, e2, Num)) ? Some(Num) : None
    // Rule 1e
    | Asc(e, t) => ana(ctx, e, t) ? Some(t) : None
    // Rule 1f
    | EHole => Some(Hole)
    // Rule 1g
    | NEHole(e) => Option.is_some(syn(ctx, e)) ? Some(Hole) : None
    | _ =>  None;
  };

}

and ana = (ctx: typctx, e: Hexp.t, t: Htyp.t): bool => {
  // Used to suppress unused variable warnings
  // Okay to remove
  switch(e, t){
    // Rule 2a
    | (Lam(_, ep), _) => {
      let* arrowed_t1_and_t2 =  mat(t);
      let+ (_, t2) = extract_arrow_components(arrowed_t1_and_t2);
      // (TypCtx.find(name, ctx) == t1) && ana(ctx, ep, t2);
      ana(ctx, ep, t2)
      } == Some(true);
    // Rule 2b
    | (_, _) =>  {
      let+ tp = syn(ctx, e);
      consistent(t, tp);
      } == Some(true);
  }
}

and consistent = (t: Htyp.t, tp: Htyp.t): bool => {
  // Used to suppress unused variable warnings
  // Okay to remove
  switch (t, tp){
    // Rule 3a
    | (_, Hole) => true
    // Rule 3b
    | (Hole, _) => true
    // Rule 3c
    | (_, _) when t == tp => true
    // Rule 3d
    | (Arrow(t1, t2), Arrow(tp1, tp2)) => consistent(t1, tp1) && consistent(t2, tp2) 
    | (_, _) => false
  };
}

and mat = (t: Htyp.t): option(Htyp.t) => {
  switch (t){
    // Rule 4a
    | Hole => Some(Arrow(Hole, Hole))
    // Rule 4b
    | Arrow(t1, t2) => Some(Arrow(t1, t2))
    | _ => None
  };
};

let syn_action =
    (ctx: typctx, (e: Zexp.t, t: Htyp.t), a: Action.t)
    : option((Zexp.t, Htyp.t)) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  let _ = ctx;
  let _ = e;
  let _ = t;
  let _ = a;

  raise(Unimplemented);
}

and ana_action =
    (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  let _ = ctx;
  let _ = e;
  let _ = a;
  let _ = t;

  raise(Unimplemented);
};

