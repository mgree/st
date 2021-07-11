#![allow(dead_code)]

use super::syntax::*;

pub struct ConstraintGenerator {
    next_tvar: TVar,
}

impl Default for ConstraintGenerator {
    fn default() -> Self {
        ConstraintGenerator { next_tvar: 0 }
    }
}

impl ConstraintGenerator {
    pub fn new() -> Self {
        ConstraintGenerator::default()
    }

    fn fresh_tvar(&mut self) -> Type {
        let tvar = self.next_tvar;
        self.next_tvar += 1;
        Type::Var(tvar)
    }

    pub fn cgen(&mut self, ctx: &Ctx, e: &Expr) -> (Type, Vec<Constraint>) {
        match e {
            Expr::Var(x) => (ctx.get(x).clone(), Vec::new()),
            Expr::Ctor(c, es) => {
                let (typs, cs): (Vec<Type>, Vec<Vec<Constraint>>) =
                    es.iter().map(|ei| self.cgen(ctx, ei)).unzip();

                (Type::Ctor(c.clone(), typs), cs.concat())
            }
            Expr::Let(x, e1, e2) => {
                let (t1, mut cs) = self.cgen(ctx, e1);
                let (t2, cs2) = self.cgen(&ctx.extend(x, t1), e2);
                cs.extend(cs2);

                (t2, cs)
            }
            Expr::Letrec(bindings, e_body) => {
                let bindings: Vec<(&str, Type, &Fun)> = bindings
                    .iter()
                    .map(|(x, f)| (x.as_ref(), self.fresh_tvar(), f))
                    .collect();

                let ctx = ctx.extend_many(
                    bindings
                        .iter()
                        .map(|(x, t, _f)| (String::from(*x), t.clone())),
                );

                let mut cs: Vec<Constraint> = bindings
                    .iter()
                    .map(|(_x, t_ctx, f)| {
                        let (t_got, mut cs) = self.cgen_fun(&ctx, f);
                        cs.push(Constraint::eq(t_ctx.clone(), t_got));
                        cs
                    })
                    .flatten()
                    .collect();

                let (t_e, cs_e) = self.cgen(&ctx, e_body);
                cs.extend(cs_e);

                (t_e, cs)
            }
            Expr::Fun(f) => self.cgen_fun(ctx, f),
            Expr::App(e_fun, e_args) => {
                let (t_fun, mut cs) = self.cgen(ctx, e_fun);

                let (ts_args, cs_args): (Vec<Type>, Vec<Vec<Constraint>>) =
                    e_args.iter().map(|e| self.cgen(ctx, e)).unzip();
                // C1 ... Cn
                cs.extend(cs_args.concat());

                let (tvar_args, cs_arg_tvars): (Vec<Type>, Vec<Constraint>) = ts_args
                    .into_iter()
                    .map(|t_got| {
                        let tvar = self.fresh_tvar();

                        (tvar.clone(), Constraint::Sub(t_got, tvar))
                    })
                    .unzip();
                // tau2 <= alpha2 ... taun <= alphan
                cs.extend(cs_arg_tvars);

                // alpha
                let tvar_ret = self.fresh_tvar();

                // t1 = (...) -> ...
                cs.push(Constraint::eq(
                    t_fun,
                    Type::Fun(tvar_args, Box::new(tvar_ret.clone())),
                ));

                // beta
                let tvar_final = self.fresh_tvar();

                cs.push(Constraint::Sub(tvar_final.clone(), tvar_ret));

                (tvar_final, cs)
            }
            Expr::Case(e_scrutinee, clauses) => {
                // ??? ignoring the type of the scrutinee?
                let (_t_scrutinee, mut cs) = self.cgen(ctx, e_scrutinee);

                // beta
                let t_ret = self.fresh_tvar();

                let cs_clauses: Vec<Constraint> = clauses
                    .iter()
                    .map(|(p, e)| {
                        let bindings: Vec<(&str, Type)> = p
                            .vars()
                            .into_iter()
                            .map(|x| (x, self.fresh_tvar()))
                            .collect();

                        let ctx = ctx.extend_many(
                            bindings.iter().map(|(x, t)| (String::from(*x), t.clone())),
                        );

                        let mut cs_p = self.cgen_pat(&ctx, p);
                        let (t_e, cs_e) = self.cgen(&ctx, e);
                        cs_p.extend(cs_e);
                        // beta = beta_i
                        cs_p.push(Constraint::eq(t_ret.clone(), t_e));
                        // ??? what are tau_i?

                        Constraint::And(cs_p)
                    })
                    .collect();

                cs.push(Constraint::Or(cs_clauses));

                (t_ret, cs)
            }
        }
    }

    fn cgen_fun(&mut self, ctx: &Ctx, f: &Fun) -> (Type, Vec<Constraint>) {
        let bindings: Vec<(&str, Type)> = f
            .args
            .iter()
            .map(|x| (x.as_ref(), self.fresh_tvar()))
            .collect();

        let ctx = ctx.extend_many(bindings.iter().map(|(x, t)| (String::from(*x), t.clone())));

        let (t_body, cs) = self.cgen(&ctx, &f.body);

        let t = self.fresh_tvar();

        (
            t.clone(),
            vec![Constraint::eq(
                t.clone(),
                Type::Fun(
                    bindings.into_iter().map(|(_, t)| t).collect(),
                    Box::new(Type::When(Box::new(t_body), cs)), // or is the when scoped on the whole thing?!
                ),
            )],
        )
    }

    fn cgen_pat(&mut self, ctx: &Ctx, p: &Pat) -> Vec<Constraint> {
        // ??? this rule makes no sense
        //
        // `p.pattern` (the p' part)  can only be typed with Var and Struct so
        // there are no constraints, and C_p is always empty. okay. and who
        // cares about tau?
        //
        // so we really only need to generate constraints for the guard
        self.cgen_guard(ctx, &p.guard)
    }

    fn cgen_guard(&mut self, ctx: &Ctx, g: &Guard) -> Vec<Constraint> {
        match g {
            Guard::And(g1, g2) => {
                let mut cs = self.cgen_guard(ctx, g1);
                cs.extend(self.cgen_guard(ctx, g2));

                cs
            }
            Guard::True => Vec::new(),
            Guard::Is(g, x) => {
                let t_x = ctx.get(x);

                vec![Constraint::Sub(t_x.clone(), g.into())]
            }
            Guard::Eq(x, y) => {
                let t_x = ctx.get(x);
                let t_y = ctx.get(y);

                vec![Constraint::eq(t_x.clone(), t_y.clone())]
            }
        }
    }
}

impl Sol {
    pub fn sol(&self, t: &Type) -> Type {
        match (self, t) {
            (Sol::Bottom, _) => panic!("applied empty solution"),
            (_, Type::Any) | (_, Type::None) | (_, Type::Pred(_)) => t.clone(),
            (Sol::Mapping(sol), Type::Var(v)) => match sol.get(v) {
                Some(t) => t.clone(),
                None => Type::Any,
            },
            (Sol::Mapping(_), Type::Ctor(c, args)) => {
                Type::Ctor(c.clone(), args.iter().map(|t| self.sol(t)).collect())
            }
            (Sol::Mapping(_), Type::Fun(args, ret)) => Type::Fun(
                args.iter().map(|t| self.sol(t)).collect(),
                Box::new(self.sol(ret)),
            ),
            (Sol::Mapping(_), Type::Union(t1, t2)) => {
                Type::Union(Box::new(self.sol(t1)), Box::new(self.sol(t2)))
            }
            (Sol::Mapping(_), Type::When(t, _c)) => {
                self.sol(t) // should we ensure that we've satisfied c?
            }
        }
    }

    pub fn solves_conj<'a, I>(&'a self, cs: I) -> bool
    where
        I: IntoIterator<Item = &'a Constraint>,
    {
        cs.into_iter().all(|c| self.solves1(&c))
    }

    pub fn solves1(&self, c: &Constraint) -> bool {
        if let Sol::Bottom = self {
            return false;
        }

        match c {
            Constraint::Sub(t1, t2) => {
                let t1 = self.sol(t1);
                let t2 = self.sol(t2);

                !t1.is_none() && t1.sub(&t2)
            }
            Constraint::And(cs) => self.solves_conj(cs),
            Constraint::Or(cs) => cs.iter().any(|c| self.solves1(c)),
        }
    }

    pub fn solve(&mut self, c: &Constraint) {
        if let Sol::Bottom = self {
            return;
        }

        match c {
            Constraint::Sub(t_alpha, t_beta) => {
                let sol_alpha = self.sol(&t_alpha);
                let sol_beta = self.sol(&t_beta);

                if !sol_alpha.sub(&sol_beta) {
                    let t = sol_alpha.intersect(&sol_beta);

                    if t.is_none() {
                        eprintln!("{:?} <= {:?} as {:?} <= {:?} yields intersection {:?} bottom", t_alpha, t_beta, sol_alpha, sol_beta, t);
                        *self = Sol::Bottom;
                    } else {
                        match t_alpha {
                            Type::Var(v) => self.extend(*v, t),
                            _ => panic!(
                                "resolved {:?} <= {:?} as {:?}, unsure how to update solution",
                                t_alpha, t_beta, t
                            ),
                        }
                    }
                } else {
                    eprintln!("resolved {:?} <= {:?} trivially, as {:?} <= {:?}", t_alpha, t_beta, sol_alpha, sol_beta);
                }
            }
            Constraint::And(cs) => {
                // solve(Sol, Conj) =
                //  / Sol                 when        solve_conj(solve(Sol, Conj)) = Sol
                //  \ solve(Sol', Conj)   when Sol' = solve_conj(solve(Sol, Conj)) = Sol

                // this, of course, makes no sense. but i guess they're saying
                // solve and _resolve_ until fixpoint?
                let mut orig = self.clone();

                loop {
                    self.solve_conj(cs);

                    if self == &orig {
                        return;
                    } else {
                        orig = self.clone();
                    }
                }
            }
            Constraint::Or(cs) => {
                let sols: Vec<Sol> = cs
                    .iter()
                    .map(|c| {
                        let mut sol = self.clone();
                        sol.solve(c);
                        sol
                    })
                    .filter(|sol| sol.is_mapping())
                    .collect();

                if sols.is_empty() {
                    *self = Sol::Bottom;
                } else {
                    *self = sols
                        .into_iter()
                        .reduce(|sol1, sol2| sol1.union(sol2))
                        .unwrap();
                }
            }
        }
    }

    pub fn solve_conj<'a, I>(&'a mut self, cs: I)
    where
        I: IntoIterator<Item = &'a Constraint>,
    {
        if let Sol::Bottom = self {
            return;
        }

        for c in cs.into_iter() {
            self.solve(c);

            if let Sol::Bottom = self {
                return;
            }
        }
    }
}
