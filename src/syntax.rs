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
#[derive(Clone, Debug)]
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
#[derive(Clone, Debug)]
pub enum Pred {
    Ground(Ground),
    //    Pid, // ???
    Constant(Constant),
}

/// Corresponds to metavariable `C`.
#[derive(Clone, Debug)]
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
