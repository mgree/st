#![allow(dead_code)]

use std::collections::HashMap;

/// Corresponds to metavariable `A`.
#[derive(Clone, Debug)]
pub struct Ctx(HashMap<Var, Type>);

impl Default for Ctx {
    fn default() -> Self {
        Ctx(HashMap::new())
    }
}

impl Ctx {
    pub fn new() -> Self {
        Ctx::default()
    }

    /// Look up a value in a context.
    pub fn lookup<S>(&self, var: S) -> Option<&Type>
    where
        S: AsRef<str>,
    {
        self.0.get(var.as_ref())
    }

    pub fn get<S>(&self, var: S) -> &Type
    where
        S: AsRef<str>,
    {
        self.0
            .get(var.as_ref())
            .unwrap_or_else(|| panic!("unbound variable '{}'", var.as_ref()))
    }

    /// Return a new context that is equal to this one, but with `var` mapped to
    /// `typ`.
    pub fn extend<S>(&self, var: S, typ: Type) -> Self
    where
        S: AsRef<str>,
    {
        let mut ctx = self.clone();
        ctx.0.insert(var.as_ref().into(), typ);

        ctx
    }

    pub fn extend_many<I>(&self, bindings: I) -> Self
    where
        I: IntoIterator<Item = (String, Type)>,
    {
        let mut ctx = self.clone();

        for (var, typ) in bindings.into_iter() {
            ctx.0.insert(var, typ);
        }

        ctx
    }
}

/// Corresponds to metavariable `c`.
pub type Ctor = String;

/// Corresponds to metavariable `V`.
pub type TVar = usize;

/// Corresponds to metavariable `T`.
#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    None,
    Any,
    Var(TVar),
    Ctor(Ctor, Vec<Type>),
    Fun(Vec<Type>, Box<Type>),
    Union(Box<Type>, Box<Type>),
    When(Box<Type>, Vec<Constraint>),
    Pred(Pred),
}

impl Type {
    /// Converst any remaining type variables to `any`
    pub fn default_to_any(&mut self) {
        match self {
            Type::None | Type::Pred(_) | Type::Any => (),
            Type::Var(_) => *self = Type::Any,
            Type::Ctor(_, args) => {
                for t in args {
                    t.default_to_any()
                }
            }
            Type::Fun(args, ret) => {
                for t in args {
                    t.default_to_any()
                }
                ret.default_to_any();
            }
            Type::Union(t1, t2) => {
                t1.default_to_any();
                t2.default_to_any();
            }
            Type::When(t, _) => {
                t.default_to_any();
                *self = *t.clone();
            }
        }
    }

    pub fn is_none(&self) -> bool {
        match self {
            Type::None => true,
            Type::Ctor(_, args) => args.iter().any(|t| t.is_none()),
            Type::Fun(args, ret) => args.iter().any(|t| t.is_none()) || ret.is_none(),
            Type::Union(t1, t2) => t1.is_none() && t2.is_none(),
            Type::When(t, _cs) => t.is_none(), // look at cs?
            Type::Pred(_) | Type::Any => false,
            Type::Var(_) => false,
        }
    }

    pub fn sub(&self, other: &Type) -> bool {
        use Type::*;
        match (self, other) {
            (None, _) => true,
            (_, None) => false,
            (_, Any) => true,
            (Any, _) => false,
            (Var(v1), Var(v2)) => v1 == v2,
            (Var(_), _) | (_, Var(_)) => false,
            (Ctor(c1, args1), Ctor(c2, args2)) => {
                c1 == c2
                    && args1.len() == args2.len()
                    && args1.iter().zip(args2).all(|(t1, t2)| t1.sub(t2))
            }
            (Fun(args1, ret1), Fun(args2, ret2)) => {
                args1.len() == args2.len()
                    // contravariant?
                    && args1.iter().zip(args2).all(|(t1, t2)| t2.sub(t1))
                    && ret1.sub(ret2)
            }
            (Union(t11, t12), t2) => t11.sub(t2) && t12.sub(t2),
            (t1, Union(t21, t22)) => t1.sub(t21) || t1.sub(t22),
            (When(t1, _), t2) => t1.sub(t2),
            (t1, When(t2, _cs)) => t1.sub(t2), // ??? constraints should already be resolved...
            (Fun(_, _), Type::Pred(super::syntax::Pred::Ground(Ground::Fun))) => true,
            (Pred(p1), Pred(p2)) => p1 == p2,
            (Pred(..), Ctor(..))
            | (Ctor(..), Pred(..))
            | (Pred(..), Fun(..))
            | (Fun(..), Pred(..))
            | (Ctor(..), Fun(..))
            | (Fun(..), Ctor(..)) => false,
        }
    }

    pub fn union(t1: Type, t2: Type) -> Type {
        if t1 == t2 || t2.sub(&t1) {
            t1
        } else if t1.sub(&t2) {
            t2
        } else {
            // union limit?

            Type::Union(Box::new(t1), Box::new(t2))
        }
    }

    pub fn intersect(&self, other: &Type) -> Type {
        use Type::*;
        match (self, other) {
            (None, _) | (_, None) => Type::None,
            (t, Any) | (Any, t) => t.clone(),
            (Var(v1), Var(v2)) if v1 == v2 => self.clone(),
            (Var(_), t) | (t, Var(_)) => t.clone(),
            (Ctor(c1, args1), Ctor(c2, args2)) => {
                if c1 == c2 && args1.len() == args2.len() {
                    Type::Ctor(
                        c1.clone(),
                        args1
                            .iter()
                            .zip(args2)
                            .map(|(t1, t2)| t1.intersect(t2))
                            .collect(),
                    )
                } else {
                    Type::None
                }
            }
            (Fun(args1, ret1), Fun(args2, ret2)) => {
                if args1.len() == args2.len() {
                    Type::Fun(
                        args1
                            .iter()
                            .zip(args2)
                            .map(|(t1, t2)| Type::Union(Box::new(t1.clone()), Box::new(t2.clone())))
                            .collect(),
                        Box::new(ret1.intersect(ret2)),
                    )
                } else {
                    Type::None
                }
            }
            (Union(t11, t12), t2) => Type::union(t11.intersect(t2), t12.intersect(t2)),
            (t1, Union(t21, t22)) => Type::union(t1.intersect(t21), t1.intersect(t22)),
            (When(t1, cs), t2) => Type::When(Box::new(t1.intersect(t2)), cs.clone()),
            (t1, When(t2, cs)) => Type::When(Box::new(t1.intersect(t2)), cs.clone()),
            (Fun(..), Type::Pred(super::syntax::Pred::Ground(Ground::Fun))) => self.clone(),
            (Pred(p1), Pred(p2)) => {
                if p1 == p2 {
                    self.clone()
                } else {
                    Type::None
                }
            }
            (Pred(..), Ctor(..))
            | (Ctor(..), Pred(..))
            | (Pred(..), Fun(..))
            | (Fun(..), Pred(..))
            | (Ctor(..), Fun(..))
            | (Fun(..), Ctor(..)) => Type::None,
        }
    }
}

/// Doesn't correspond to anything in the system.
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Ground {
    Atom,
    Integer,
    Float,
    Fun,
}

impl From<&Ground> for Type {
    fn from(g: &Ground) -> Self {
        Type::Pred(Pred::Ground(g.clone()))
    }
}

/// Corresponds to metavariable `P`.
#[derive(Clone, Debug, PartialEq)]
pub enum Pred {
    Ground(Ground),
    //    Pid, // ???
    Constant(Constant),
}

/// Corresponds to metavariable `C`.
#[derive(Clone, Debug, PartialEq)]
pub enum Constraint {
    Sub(Type, Type),
    And(Vec<Constraint>),
    Or(Vec<Constraint>),
}

impl Constraint {
    pub fn eq(t1: Type, t2: Type) -> Self {
        Constraint::And(vec![
            Constraint::Sub(t1.clone(), t2.clone()),
            Constraint::Sub(t2, t1),
        ])
    }
}

/// Corresponds to metavariable `Sol`.
#[derive(Clone, Debug)]
pub enum Sol {
    Bottom,
    Mapping(HashMap<TVar, Type>),
}

impl Default for Sol {
    fn default() -> Self {
        Sol::Mapping(HashMap::new())
    }
}

impl Sol {
    pub fn new() -> Self {
        Sol::default()
    }

    pub fn extend(&mut self, v: TVar, t: Type) {
        match self {
            Sol::Bottom => panic!("extended bottom with {:?} |-> {:?}", v, t),
            Sol::Mapping(sol) => {
                sol.insert(v, t);
            }
        }
    }

    pub fn is_mapping(&self) -> bool {
        matches!(self, Sol::Mapping(_))
    }

    pub fn union(self, other: Self) -> Self {
        match (self, other) {
            (Sol::Bottom, m) | (m, Sol::Bottom) => m,
            (Sol::Mapping(mut lhs), Sol::Mapping(rhs)) => {
                for (k, vr) in rhs {
                    match lhs.get_mut(&k) {
                        None => {
                            lhs.insert(k, vr);
                        }
                        Some(vl) => *vl = Type::union(vl.clone(), vr),
                    }
                }

                Sol::Mapping(lhs)
            }
        }
    }
}

impl PartialEq for Sol {
    fn eq(&self, other: &Sol) -> bool {
        match (self, other) {
            (Sol::Bottom, Sol::Bottom) => true,
            (Sol::Mapping(lhs), Sol::Mapping(rhs)) => {
                for (k, vl) in lhs {
                    match rhs.get(&k) {
                        Some(vr) => {
                            if vl != vr {
                                return false;
                            }
                        }
                        None => return false,
                    }
                }

                for k in rhs.keys() {
                    if !lhs.contains_key(k) {
                        return false;
                    }
                }

                true
            }
            (Sol::Bottom, Sol::Mapping(..)) | (Sol::Mapping(..), Sol::Bottom) => false,
        }
    }
}

/// Corresponds to metavariable `X`.
pub type Var = String;

/// Corresponds to metavariable `e` (and maybe also `b`, in the rule for case)
#[derive(Clone, Debug)]
pub enum Expr {
    Var(Var),
    Ctor(Ctor, Vec<Expr>),
    App(Box<Expr>, Vec<Expr>),
    Fun(Box<Fun>),
    Let(Var, Box<Expr>, Box<Expr>),
    Letrec(Vec<(Var, Fun)>, Box<Expr>),
    Case(Box<Expr>, Vec<(Pat, Expr)>),
}

/// Corresponds to metavariable `f`.
#[derive(Clone, Debug)]
pub struct Fun {
    pub args: Vec<Var>,
    pub body: Expr,
}

/// Corresponds to metavariable `p`
#[derive(Clone, Debug)]
pub struct Pat {
    pub pattern: Pattern,
    pub guard: Guard,
}

impl Pat {
    pub fn vars(&self) -> Vec<&str> {
        self.pattern.vars()
    }

    pub fn wildcard() -> Self {
        Pattern::wildcard().into()
    }
}

/// Corresponds to metavariable `p'`
#[derive(Clone, Debug)]
pub enum Pattern {
    Var(Var),
    Ctor(Ctor, Vec<Pattern>),
}

impl From<Pattern> for Pat {
    fn from(pattern: Pattern) -> Self {
        Pat {
            pattern,
            guard: Guard::True,
        }
    }
}

impl Pattern {
    pub fn wildcard() -> Self {
        Pattern::Var("_".into())
    }

    pub fn vars(&self) -> Vec<&str> {
        match self {
            Pattern::Var(v) => vec![v],
            Pattern::Ctor(_c, args) => args.iter().map(|p| p.vars()).flatten().collect(),
        }
    }
}

/// Corresponds to metavariable `g`
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Guard {
    And(Box<Guard>, Box<Guard>),
    Eq(Var, Var),
    True,
    Is(Ground, Var),
}

/// Does not correspond to any metavariable, but appears in predicates `P` and,
/// presumably, expressions `e`.
#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum Constant {
    Integer(i64),
    Float(f64),
    Atom(String),
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Type::None => write!(f, "none"),
            Type::Any => write!(f, "any"),
            Type::Var(v) => write!(f, "t{}", v),
            Type::Ctor(c, args) => {
                write!(f, "{}(", c)?;
                fmt_slice(f, args, &", ")?;
                write!(f, ")")
            }
            Type::Fun(args, ret) => {
                write!(f, "((")?;
                fmt_slice(f, args, &", ")?;
                write!(f, ") -> {})", ret)
            }
            Type::Union(t1, t2) => write!(f, "{} ∪ {}", t1, t2),
            Type::When(t, cs) => {
                write!(f, "({} when ", t)?;

                fmt_slice(f, cs, &", ")?;
                write!(f, ")")
            }
            Type::Pred(p) => write!(f, "{}()", p),
        }
    }
}

impl std::fmt::Display for Constraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Constraint::Sub(t1, t2) => write!(f, "{} ⊆ {}", t1, t2),
            Constraint::And(cs) => fmt_slice(f, cs, &" ∧ "),
            Constraint::Or(cs) => fmt_slice(f, cs, &" ∨ "),
        }
    }
}

impl std::fmt::Display for Pred {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Pred::Constant(c) => write!(f, "{}", c),
            Pred::Ground(g) => write!(f, "is_{}", g),
        }
    }
}

impl std::fmt::Display for Constant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Constant::Atom(s) => write!(f, "{}", s),
            Constant::Integer(n) => write!(f, "{}", n),
            Constant::Float(n) => write!(f, "{}", n),
        }
    }
}

impl std::fmt::Display for Ground {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Ground::Atom => write!(f, "atom"),
            Ground::Float => write!(f, "float"),
            Ground::Fun => write!(f, "fun"),
            Ground::Integer => write!(f, "int"),
        }
    }
}

fn fmt_slice<'a, T, S>(
    f: &mut std::fmt::Formatter<'a>,
    vs: &[T],
    sep: &S,
) -> Result<(), std::fmt::Error>
where
    T: std::fmt::Display,
    S: std::fmt::Display,
{
    if vs.is_empty() {
        return Ok(());
    }

    for v in &vs[0..vs.len() - 1] {
        write!(f, "{}{}", v, sep)?;
    }
    write!(f, "{})", vs[vs.len() - 1])
}
