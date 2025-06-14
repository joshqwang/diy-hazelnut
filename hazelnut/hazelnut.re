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
  switch (e) {
  | Cursor(t) => t
  | Lam(s, t) => Hexp.Lam(s, erase_exp(t))
  | LAp(t, ht) => Hexp.Ap(erase_exp(t), ht)
  | RAp(ht, t) => Hexp.Ap(ht, erase_exp(t))
  | LPlus(t, ht) => Hexp.Plus(erase_exp(t), ht)
  | RPlus(ht, t) => Hexp.Plus(ht, erase_exp(t))
  | LAsc(t, ht) => Hexp.Asc(erase_exp(t), ht)
  | RAsc(ht, t) => Hexp.Asc(ht, erase_type(t))
  | NEHole(t) => Hexp.NEHole(erase_exp(t))
  };
}
and erase_type = (t: Ztyp.t): Htyp.t => {
  switch (t) {
  | Cursor(t) => t
  | LArrow(t, ht) => Htyp.Arrow(erase_type(t), ht)
  | RArrow(ht, t) => Htyp.Arrow(ht, erase_type(t))
  };
};
let extract_arrow_components = (t: Htyp.t): option((Htyp.t, Htyp.t)) =>
  switch (t) {
  | Arrow(t1, t2) => Some((t1, t2))
  | _ => None
  };

let rec syn = (ctx: typctx, e: Hexp.t): option(Htyp.t) => {
  switch (e) {
  // Rule 1a
  | Var(name) => TypCtx.find_opt(name, ctx)
  // Rule 1b
  | Ap(e1, e2) =>
    let* t1 = syn(ctx, e1);
    let* arrowed_t2_and_t = mat(t1);
    let* (t2, t) = extract_arrow_components(arrowed_t2_and_t);
    ana(ctx, e2, t2) ? Some(t) : None;
  // Rule 1c
  | Lit(_) => Some(Num)
  // Rule 1d
  | Plus(e1, e2) =>
    ana(ctx, e1, Num) && ana(ctx, e2, Num) ? Some(Num) : None
  // Rule 1e
  | Asc(e, t) => ana(ctx, e, t) ? Some(t) : None
  // Rule 1f
  | EHole => Some(Hole)
  // Rule 1g
  | NEHole(e) => Option.is_some(syn(ctx, e)) ? Some(Hole) : None
  | _ => None
  };
}

and ana = (ctx: typctx, e: Hexp.t, t: Htyp.t): bool => {
  // Used to suppress unused variable warnings
  // Okay to remove
  switch (e, t) {
  // Rule 2a
  | (Lam(_, ep), _) =>
    {
      let* arrowed_t1_and_t2 = mat(t);
      let+ (_, t2) = extract_arrow_components(arrowed_t1_and_t2);
      // (TypCtx.find(name, ctx) == t1) && ana(ctx, ep, t2);
      ana(ctx, ep, t2);
    }
    == Some(true)
  // Rule 2b
  | (_, _) =>
    {
      let+ tp = syn(ctx, e);
      consistent(t, tp);
    }
    == Some(true)
  };
}

and consistent = (t: Htyp.t, tp: Htyp.t): bool => {
  switch (t, tp) {
  // Rule 3a
  | (_, Hole) => true
  // Rule 3b
  | (Hole, _) => true
  // Rule 3c
  | (_, _) when t == tp => true
  // Rule 3d
  | (Arrow(t1, t2), Arrow(tp1, tp2)) =>
    consistent(t1, tp1) && consistent(t2, tp2)
  | (_, _) => false
  };
}

and mat = (t: Htyp.t): option(Htyp.t) => {
  switch (t) {
  // Rule 4a
  | Hole => Some(Arrow(Hole, Hole))
  // Rule 4b
  | Arrow(t1, t2) => Some(Arrow(t1, t2))
  | _ => None
  };
};

let rec syn_action =
        (ctx: typctx, (e: Zexp.t, t: Htyp.t), a: Action.t)
        : option((Zexp.t, Htyp.t)) => {
  let _ = ctx;
  switch (e, t, a) {
  // Rule 13a - Ascription
  | (Cursor(e), _, Construct(Asc)) => Some((RAsc(e, Cursor(t)), t))
  // Rule 13c - Variables
  | (Cursor(EHole), Hole, Construct(Var(x))) => {
    let+ hypothesized_type = TypCtx.find_opt(x, ctx);
    (Zexp.Cursor(Var(x)), hypothesized_type);};
  // Rule 18g - Type position of Ascripiton
  | (RAsc(e, t_hat), _, _) =>
    let* tp = type_action(t_hat, a);
    let t_hat_erasure = erase_type(tp);
    if (ana(ctx, e, t_hat_erasure)) {
      Some((Zexp.RAsc(e, tp), erase_type(t_hat)));
    } else {
      None;
    };
  | _ => None
  };
}

and ana_action =
    (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  switch (e, a, t) {
  // Rule 13b - Ascription
  | (Cursor(e), Construct(Asc), _) => Some(RAsc(e, Cursor(t)))
  // Rule 13d - Variables
  | (Cursor(EHole), Construct(Var(x)), _) => {
    let* hypothesized_type = TypCtx.find_opt(x, ctx);
    (!consistent(hypothesized_type, t)) ? Some(Zexp.NEHole(Cursor(Var(x)))) : None;
  };
  // Rule 5 - Action Subsumption
  | _ => action_subsumption(ctx, e, a)
  };
}

and type_action = (t: Ztyp.t, a: Action.t): option(Ztyp.t) => {
  switch (t, a) {
  // Rules 6a and 6b
  | (Cursor(Arrow(t1, t2)), Move(Child(child_num))) =>
    switch (child_num) {
    | One => Some(LArrow(Cursor(t1), t2))
    | Two => Some(RArrow(t1, Cursor(t2)))
    }
  // Rules 6c and 6d
  | (LArrow(Cursor(t1), t2), Move(Parent))
  | (RArrow(t1, Cursor(t2)), Move(Parent)) => Some(Cursor(Arrow(t1, t2)))
  // Rules 12a, 12b
  | (Cursor(t), Construct(Arrow)) => Some(RArrow(t, Cursor(Hole)))
  | (Cursor(Hole), Construct(Num)) => Some(Cursor(Num))
  | _ => None
  };
}

and expr_movement = (e: Zexp.t, a: Action.t): option(Zexp.t) => {
  switch (e, a) {
  // Rule 8a, 8b - Ascription
  | (Cursor(Asc(e, t)), Move(Child(child_num))) =>
    switch (child_num) {
    | One => Some(LAsc(Cursor(e), t))
    | Two => Some(RAsc(e, Cursor(t)))
    }
  // Rule 8c, 8d
  | (LAsc(Cursor(e), t), Move(Parent))
  | (RAsc(e, Cursor(t)), Move(Parent)) => Some(Cursor(Asc(e, t)))
  // Rule 8e, 8f - Lambda
  | (Cursor(Lam(name, e)), Move(Child(One))) =>
    Some(Lam(name, Cursor(e)))
  | (Lam(name, Cursor(e)), Move(Parent)) => Some(Cursor(Lam(name, e)))
  // Rule 8g, 8h - Application
  | (Cursor(Ap(e1, e2)), Move(Child(One))) => Some(LAp(Cursor(e1), e2))
  | (Cursor(Ap(e1, e2)), Move(Child(Two))) => Some(RAp(e1, Cursor(e2)))
  // Rule 8i, 8j
  | (LAp(Cursor(e1), e2), Move(Parent))
  | (RAp(e1, Cursor(e2)), Move(Parent)) => Some(Cursor(Ap(e1, e2)))
  // Rule 8k, 8l - Plus
  | (Cursor(Plus(e1, e2)), Move(Child(One))) =>
    Some(LPlus(Cursor(e1), e2))
  | (Cursor(Plus(e1, e2)), Move(Child(Two))) =>
    Some(RPlus(e1, Cursor(e2)))
  // Rule 8m, 8n
  | (LPlus(Cursor(e1), e2), Move(Parent))
  | (RPlus(e1, Cursor(e2)), Move(Parent)) => Some(Cursor(Plus(e1, e2)))
  // Rule 8o, 8p - NEHole
  | (Cursor(NEHole(e)), Move(Child(One))) => Some(NEHole(Cursor(e)))
  | (NEHole(Cursor(e)), Move(Parent)) => Some(Cursor(NEHole(e)))
  | _ => None
  };
}
and action_subsumption =
    (ctx: typctx, e: Zexp.t, a: Action.t): option(Zexp.t) => {
  let* tp = syn(ctx, erase_exp(e));
  let* (ep, tpp) = syn_action(ctx, (e, tp), a);
  if (consistent(tp, tpp)) {
    Some(ep);
  } else {
    None;
  };
};

let _ = expr_movement;
let _ = type_action;
