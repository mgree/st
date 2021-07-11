mod cgen;
mod syntax;

fn main() {}

#[cfg(test)]
mod test {
    use super::syntax::*;
    use super::cgen::*;

    #[test]
    fn sec42_and() {
        let true_e: Expr = Expr::Ctor("true".into(), vec![]);
        let false_e: Expr = Expr::Ctor("false".into(), vec![]);
        let true_pat: Pat = Pattern::Ctor("true".into(), vec![]).into();
        let false_pat: Pat = Pattern::Ctor("false".into(), vec![]).into();
        let x: String = "x".into();
        let y: String = "y".into();

        let and_e = Expr::Fun(Box::new(Fun {
            args: vec![x.clone(), y.clone()],
            body: Expr::Case(
                Box::new(Expr::Var(x.clone())),
                vec![
                    (
                        true_pat.clone(),
                        Expr::Case(
                            Box::new(Expr::Var(y.clone())),
                            vec![
                                (true_pat.clone(), true_e),
                                (Pat::wildcard(), false_e.clone()),
                            ],
                        ),
                    ),
                    (false_pat.clone(), false_e.clone()),
                    (
                        Pat::wildcard(),
                        Expr::Case(
                            Box::new(Expr::Var(y.clone())),
                            vec![(false_pat.clone(), false_e)],
                        ),
                    ),
                ],
            ),
        }));

        let mut cgen = ConstraintGenerator::new();
        let (t, cs) = cgen.cgen(&Ctx::new(), &and_e);

        eprintln!("t = {:?}", t);
        eprintln!("cs = {:?}", cs);
    }
}