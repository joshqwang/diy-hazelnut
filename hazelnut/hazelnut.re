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

let rec syn = (ctx: typctx, e: Hexp.t): option(Htyp.t) => {
  switch (e) {
  // Rule 1a
  | Var(name) => TypCtx.find_opt(name, ctx)
  // Rule 1b
  | Ap(e1, e2) =>
    let* t1 = syn(ctx, e1);
    let* (t2, t) = mat(t1);
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
  | (Lam(x, e), _) =>
    {
      let+ (t1, t2) = mat(t);
      // (TypCtx.find(name, ctx) == t1) && ana(ctx, ep, t2);
      ana(TypCtx.add(x, t1, ctx), e, t2);
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
  | (_, _) when Htyp.compare(t, tp) == 0 => true
  // Rule 3d
  | (Arrow(t1, t2), Arrow(tp1, tp2)) =>
    consistent(t1, tp1) && consistent(t2, tp2)
  | _ => false
  };
}

and mat = (t: Htyp.t): option((Htyp.t, Htyp.t)) => {
  switch (t) {
  // Rule 4a
  | Hole => Some((Hole, Hole))
  // Rule 4b
  | Arrow(t1, t2) => Some((t1, t2))
  | _ => None
  };
};

let rec syn_action =
        (ctx: typctx, (e: Zexp.t, t: Htyp.t), a: Action.t)
        : option((Zexp.t, Htyp.t)) => {
  let base_synthesis =
    switch (a) {
    | Move(_) => syn_movement(e, a, t)
    | Construct(s) => syn_construction(ctx, (e, t), s)
    | Del => syn_del(e)
    | Finish => syn_finish(ctx, (e, t))
    };
  if (Option.is_some(base_synthesis)) {
    base_synthesis;
  } else {
    switch (e, t, a) {
    //Rule 18b - Application Zipper
    | (LAp(e_hat, e), _, _) =>
      let* t2 = syn(ctx, erase_exp(e_hat));
      let* (ep, t3) = syn_action(ctx, (e_hat, t2), a);
      let* (t4, t5) = mat(t3);
      ana(ctx, e, t4) ? Some((Zexp.LAp(ep, e), t5)) : None;
    //Rule 18c
    | (RAp(e, e_hat), _, _) =>
      let* t2 = syn(ctx, erase_exp(e_hat));
      let* (t3, t4) = mat(t2);
      let* ep = ana_action(ctx, e_hat, a, t3);
      Some((Zexp.RAp(e, ep), t4));
    //Rule 18d - Addition zipper
    | (LPlus(e_hat, e), Num, _) =>
      let* ep = ana_action(ctx, e_hat, a, Num);
      Some((Zexp.LPlus(ep, e), Htyp.Num));
    // Rule 18e
    | (RPlus(e, e_hat), Num, _) =>
      let* ep = ana_action(ctx, e_hat, a, Num);
      Some((Zexp.RPlus(e, ep), Htyp.Num));
    // Rule 18f - Expression position of Ascription
    | (LAsc(e_hat, ascr_t), _, _) when Htyp.compare(t, ascr_t) == 0 =>
      let* ep = ana_action(ctx, e_hat, a, ascr_t);
      Some((Zexp.LAsc(ep, t), t));
    // Rule 18g - Type position of Ascripiton
    | (RAsc(e, t_hat), _, _) =>
      let* tp = type_action(t_hat, a);
      let t_hat_erasure = erase_type(tp);
      ana(ctx, e, t_hat_erasure)
        ? Some((Zexp.RAsc(e, tp), erase_type(tp))) : None;
    // Rule 18h - Zipper NEHole
    | (NEHole(e_hat), Hole, a) =>
      let* t = syn(ctx, erase_exp(e_hat));
      let* (e_p, _) = syn_action(ctx, (e_hat, t), a);
      Some((Zexp.NEHole(e_p), Htyp.Hole));
    | _ => None
    };
  };
}

and ana_action =
    (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  let base_analysis =
    switch (a) {
    | Construct(s) => ana_construction(ctx, e, s, t)
    | Del => ana_del(e)
    | Finish => ana_finish(ctx, e, t)
    | Move(_) => expr_movement(e, a)
    };
  if (Option.is_some(base_analysis)) {
    base_analysis;
  } else {
    let rec_analysis =
      switch (e, a, t) {
      | (Lam(x, e), _, _) =>
        let* (t1, t2) = mat(t);
        let* ep = ana_action(TypCtx.add(x, t1, ctx), e, a, t2);
        Some(Zexp.Lam(x, ep));
      | _ => None
      };
    Option.is_some(rec_analysis)
      ? rec_analysis : action_subsumption(ctx, e, a, t);
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
  // Rule 14 - Deletion
  | (Cursor(_), Del) => Some(Cursor(Hole))
  // Rule 17a, b - Zipper cases
  | (LArrow(t_hat, t), _) =>
    let+ zipped = type_action(t_hat, a);
    Ztyp.LArrow(zipped, t);
  | (RArrow(t, t_hat), _) =>
    let+ zipped = type_action(t_hat, a);
    Ztyp.RArrow(t, zipped);
  | _ => None
  };
}

and syn_movement =
    (e: Zexp.t, a: Action.t, t: Htyp.t): option((Zexp.t, Htyp.t)) => {
  let+ movement_result = expr_movement(e, a);
  (movement_result, t);
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
  | (Cursor(Hexp.Lam(x, e)), Move(Child(One))) =>
    Some(Lam(x, Cursor(e)))
  | (Zexp.Lam(x, Cursor(e)), Move(Parent)) => Some(Cursor(Lam(x, e)))
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
    (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  let* tp = syn(ctx, erase_exp(e));
  let* (ep, tpp) = syn_action(ctx, (e, tp), a);
  if (consistent(t, tpp)) {
    Some(ep);
  } else {
    None;
  };
}

and syn_construction =
    (ctx: typctx, (e: Zexp.t, t: Htyp.t), s: Shape.t)
    : option((Zexp.t, Htyp.t)) => {
  // Rule 13a - Ascription
  switch (e, t, s) {
  | (Cursor(e), _, Asc) => Some((RAsc(e, Cursor(t)), t))
  // Rule 13c - Variables
  | (Cursor(EHole), Hole, Var(x)) =>
    let+ hypothesized_type = TypCtx.find_opt(x, ctx);
    (Zexp.Cursor(Var(x)), hypothesized_type);
  // Rule 13e - Lambda construction
  | (Cursor(EHole), Hole, Lam(x)) =>
    Some((
      RAsc(Lam(x, EHole), LArrow(Cursor(Hole), Hole)),
      Arrow(Hole, Hole),
    ))
  // Rule 13h - Application
  | (Cursor(NEHole(e)), _, Ap) =>
    Option.is_some(mat(t))
      ? Some((RAp(e, Cursor(EHole)), Hole))
      : Some((RAp(NEHole(e), Cursor(EHole)), Hole))
  // Rule 13j - Literals
  | (Cursor(EHole), Hole, Lit(n)) => Some((Cursor(Lit(n)), Num))
  //Rule 13l - Plus
  | (Cursor(e), _, Plus) =>
    consistent(t, Num)
      ? Some((RPlus(e, Cursor(EHole)), Num))
      : Some((NEHole(RPlus(e, Cursor(EHole))), Num))
  | (Cursor(e), _, NEHole) => Some((NEHole(Cursor(e)), Hole))
  | _ => None
  };
}
and ana_construction =
    (ctx: typctx, e: Zexp.t, s: Shape.t, t: Htyp.t): option(Zexp.t) => {
  // Rule 13b - Ascription
  switch (e, s, t) {
  | (Cursor(e), Asc, _) => Some(RAsc(e, Cursor(t)))
  // Rule 13d - Variables
  | (Cursor(EHole), Var(x), _) =>
    let* hypothesized_type = TypCtx.find_opt(x, ctx);
    !consistent(hypothesized_type, t)
      ? Some(Zexp.NEHole(Cursor(Var(x)))) : None;
  // Rule 13f, g - Lambdas
  | (Cursor(EHole), Lam(x), _) =>
    if (Option.is_some(mat(t))) {
      Some(Lam(x, Cursor(EHole)));
    } else {
      Some(NEHole(RAsc(Lam(x, EHole), LArrow(Cursor(Hole), Hole))));
    }
  // Rule 13k - Literals
  | (Cursor(EHole), Lit(n), t) when !consistent(t, Num) =>
    Some(NEHole(Cursor(Lit(n))))
  | _ => None
  };
}
and syn_del = (e: Zexp.t): option((Zexp.t, Htyp.t)) => {
  switch (e) {
  | Cursor(_) => Some((Cursor(EHole), Hole))
  | _ => None
  };
}
and syn_finish =
    (ctx: typctx, (e: Zexp.t, t: Htyp.t)): option((Zexp.t, Htyp.t)) => {
  switch (e, t) {
  | (Cursor(NEHole(e)), Hole) =>
    let* synthesized_type = syn(ctx, e);
    Some((Zexp.Cursor(e), synthesized_type));
  | _ => None
  };
}

and ana_del = (e: Zexp.t): option(Zexp.t) => {
  switch (e) {
  | Cursor(_) => Some(Cursor(EHole))
  | _ => None
  };
}
and ana_finish = (ctx: typctx, e: Zexp.t, t: Htyp.t): option(Zexp.t) => {
  switch (e) {
  | Cursor(NEHole(e)) when ana(ctx, e, t) => Some(Cursor(e))
  | _ => None
  };
};
