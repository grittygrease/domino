// SPDX-License-Identifier: MIT OR Apache-2.0

use std::convert::Infallible;

use crate::{
    expressions::{Expression, ExpressionKind},
    identifier::{pkg_ident::PackageIdentifier, Identifier},
    package::Composition,
    parser::package::ForComp,
    statement::{
        Assignment, AssignmentRhs, CodeBlock, IfThenElse, InvokeOracle, Pattern, Statement,
    },
};

pub struct Transformation<'a>(pub &'a Composition);

impl super::Transformation for Transformation<'_> {
    type Err = Infallible;
    type Aux = ();

    fn transform(&self) -> Result<(Composition, ()), Infallible> {
        let insts = self.0.pkgs.iter().map(|inst| {
            let mut newinst = inst.clone();
            newinst.pkg.oracles.iter_mut().for_each(|oracle| {
                oracle.code = unroll(&oracle.code, &Vec::new());
            });
            newinst
        });
        Ok((
            Composition {
                pkgs: insts.collect(),
                ..self.0.clone()
            },
            (),
        ))
    }
}

fn unroll(cb: &CodeBlock, subst: &Vec<(&Identifier, &Identifier)>) -> CodeBlock {
    let mut newcode = Vec::new();

    let fn_subst = |expr: Expression| {
        if let Some(ident) = expr.as_identifier() {
            if let Some((_, sub)) = subst.iter().find(|(old, _)| &ident == old) {
                (*sub).clone().into()
            } else {
                expr
            }
        } else {
            expr
        }
    };

    for stmt in &cb.0 {
        match stmt {
            Statement::For(ident, lower, upper, code, span) => {
                if let (
                    ExpressionKind::IntegerLiteral(lower),
                    ExpressionKind::IntegerLiteral(upper),
                ) = (lower.kind(), upper.kind())
                {
                    let (start_comp, end_comp) = loop_comparisons(ident);
                    if let Some((start, end)) =
                        inclusive_literal_bounds(*lower, start_comp, *upper, end_comp)
                    {
                        let gen_ident =
                            Identifier::Generated(ident.ident(), ident.get_type().clone());

                        let mut newsubst = subst.clone();
                        newsubst.push((ident, &gen_ident));
                        let loopcode = unroll(code, &newsubst);

                        for i in start..=end {
                            newcode.push(Statement::Assignment(
                                Assignment {
                                    pattern: Pattern::Ident(gen_ident.clone()),
                                    rhs: AssignmentRhs::Expression(Expression::integer(i)),
                                },
                                *span,
                            ));
                            newcode.extend(loopcode.0.iter().cloned());
                        }
                    }
                } else {
                    newcode.push(Statement::For(
                        ident.clone(),
                        lower.map(fn_subst),
                        upper.map(fn_subst),
                        unroll(code, subst),
                        *span,
                    ));
                }
            }
            Statement::IfThenElse(ite) => {
                newcode.push(Statement::IfThenElse(IfThenElse {
                    cond: ite.cond.map(fn_subst),
                    then_block: unroll(&ite.then_block, subst),
                    else_block: unroll(&ite.else_block, subst),
                    ..ite.clone()
                }));
            }
            Statement::Assignment(assign, span) => {
                let pattern = if let Pattern::Table { ident, index } = &assign.pattern {
                    Pattern::Table {
                        ident: ident.clone(),
                        index: index.map(fn_subst),
                    }
                } else {
                    assign.pattern.clone()
                };
                let rhs = match assign.rhs.clone() {
                    AssignmentRhs::Expression(e) => AssignmentRhs::Expression(e.map(fn_subst)),
                    r @ AssignmentRhs::Sample { .. } => r,
                    AssignmentRhs::Invoke {
                        oracle_name,
                        args,
                        edge,
                        return_type,
                    } => AssignmentRhs::Invoke {
                        oracle_name,
                        args: args.iter().map(|expr| expr.map(fn_subst)).collect(),
                        edge,
                        return_type,
                    },
                };
                newcode.push(Statement::Assignment(Assignment { pattern, rhs }, *span));
            }
            Statement::InvokeOracle(io) => {
                newcode.push(Statement::InvokeOracle(InvokeOracle {
                    args: io.args.iter().map(|expr| expr.map(fn_subst)).collect(),
                    ..io.clone()
                }));
            }
            Statement::Return(expr, span) => newcode.push(Statement::Return(
                expr.as_ref().map(|expr| expr.map(fn_subst)),
                *span,
            )),
            Statement::Abort(_) => newcode.push(stmt.clone()),
        }
    }

    CodeBlock(newcode)
}

fn loop_comparisons(ident: &Identifier) -> (ForComp, ForComp) {
    match ident {
        Identifier::PackageIdentifier(PackageIdentifier::CodeLoopVar(loopvar)) => {
            (loopvar.start_comp, loopvar.end_comp)
        }
        _ => unreachable!("a loop variable carries its two comparisons"),
    }
}

/// Inclusive first and last values allowed by the two comparisons.
/// `None` when that set is empty, including when a strict bound has no
/// neighboring integer.
fn inclusive_literal_bounds(
    lower: i64,
    start_comp: ForComp,
    upper: i64,
    end_comp: ForComp,
) -> Option<(i64, i64)> {
    let start = match start_comp {
        ForComp::Lte => lower,
        ForComp::Lt => lower.checked_add(1)?,
    };
    let end = match end_comp {
        ForComp::Lte => upper,
        ForComp::Lt => upper.checked_sub(1)?,
    };
    (start <= end).then_some((start, end))
}

#[cfg(test)]
mod test {
    use std::collections::HashMap;

    use crate::{
        expressions::ExpressionKind,
        parser::tests::{games, packages},
        statement::{AssignmentRhs, Pattern, Statement},
        transforms::Transformation as _,
    };

    fn unrolled_values(pkg_code: &str) -> Vec<i64> {
        let game_code = r#"composition ToyGame {
    instance pkg = Toy {}

    compose {
        adversary: {
            Go: pkg,
        }
    }
}
"#;
        let (name, pkg) = packages::parse(pkg_code, "Toy.pkg.ssp");
        let pkg_map = HashMap::from([(name, pkg)]);
        let comp = games::parse(game_code, "ToyGame.comp.ssp", &pkg_map);
        let (comp, _) = super::Transformation(&comp).transform().unwrap();
        let code = &comp.pkgs[0].pkg.oracles[0].code.0;

        code.iter()
            .map(|stmt| match stmt {
                Statement::Assignment(assign, _) => {
                    let Pattern::Ident(ident) = &assign.pattern else {
                        panic!("expected the loop variable, got {:?}", assign.pattern);
                    };
                    assert_eq!(ident.ident(), "i");
                    let AssignmentRhs::Expression(expr) = &assign.rhs else {
                        panic!("expected an integer assignment, got {:?}", assign.rhs);
                    };
                    let ExpressionKind::IntegerLiteral(value) = expr.kind() else {
                        panic!("expected an integer literal, got {expr:?}");
                    };
                    *value
                }
                other => panic!("expected an assignment of the loop variable, got {other:?}"),
            })
            .collect()
    }

    #[test]
    fn unrolls_lower_inclusive_and_upper_inclusive() {
        let pkg_code = r#"package Toy {
    oracle Go() {
        for i: 0 <= i <= 1 {
        }
    }
}
"#;
        assert_eq!(unrolled_values(pkg_code), vec![0, 1]);
    }

    #[test]
    fn unrolls_lower_inclusive_and_upper_exclusive() {
        let pkg_code = r#"package Toy {
    oracle Go() {
        for i: 0 <= i < 2 {
        }
    }
}
"#;
        assert_eq!(unrolled_values(pkg_code), vec![0, 1]);
    }

    #[test]
    fn unrolls_lower_exclusive_and_upper_inclusive() {
        let pkg_code = r#"package Toy {
    oracle Go() {
        for i: 0 < i <= 2 {
        }
    }
}
"#;
        assert_eq!(unrolled_values(pkg_code), vec![1, 2]);
    }

    #[test]
    fn unrolls_lower_exclusive_and_upper_exclusive() {
        let pkg_code = r#"package Toy {
    oracle Go() {
        for i: 0 < i < 2 {
        }
    }
}
"#;
        assert_eq!(unrolled_values(pkg_code), vec![1]);
    }

    #[test]
    fn unrolls_empty_exclusive_range() {
        let pkg_code = r#"package Toy {
    oracle Go() {
        for i: 0 < i < 1 {
        }
    }
}
"#;
        assert_eq!(unrolled_values(pkg_code), Vec::<i64>::new());
    }

    #[test]
    fn unrolls_equal_bounds_inclusive_and_one_strict() {
        let inclusive = r#"package Toy {
    oracle Go() {
        for i: 1 <= i <= 1 {
        }
    }
}
"#;
        assert_eq!(unrolled_values(inclusive), vec![1]);

        let one_strict = r#"package Toy {
    oracle Go() {
        for i: 1 <= i < 1 {
        }
    }
}
"#;
        assert_eq!(unrolled_values(one_strict), Vec::<i64>::new());
    }

    #[test]
    fn unrolls_upper_bound_below_lower() {
        let pkg_code = r#"package Toy {
    oracle Go() {
        for i: 2 <= i <= 1 {
        }
    }
}
"#;
        assert_eq!(unrolled_values(pkg_code), Vec::<i64>::new());
    }

    #[test]
    fn unrolls_largest_integer_as_both_bounds() {
        let pkg_code = r#"package Toy {
    oracle Go() {
        for i: 9223372036854775807 <= i <= 9223372036854775807 {
        }
    }
}
"#;
        assert_eq!(unrolled_values(pkg_code), vec![i64::MAX]);
    }

    #[test]
    fn unrolls_strict_lower_at_largest_integer() {
        let pkg_code = r#"package Toy {
    oracle Go() {
        for i: 9223372036854775807 < i <= 9223372036854775807 {
        }
    }
}
"#;
        assert_eq!(unrolled_values(pkg_code), Vec::<i64>::new());
    }
}
