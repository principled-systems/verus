use std::sync::Arc;

use crate::ast::{HereFocus, Query, QueryX, Stmt, StmtX};

struct HandleHereState {
    pending: Option<HereFocus>,
}

fn make_dummy_stmt() -> Stmt {
    Arc::new(StmtX::Block(Default::default()))
}

fn handle_here_recursive(state: &mut HandleHereState, stmt: &Stmt) -> Option<Stmt> {
    match stmt.as_ref() {
        StmtX::HereMarker => {
            if let Some(_here) = &state.pending {
                panic!("internal error: multiple here markers found");
            };

            state.pending = Some(HereFocus);
            None
        }
        StmtX::Assert(id, msg, filter, prev, expr) => {
            let stmt = match state.pending.take() {
                None => stmt.clone(),
                here_focus => {
                    if let Some(_here) = prev {
                        panic!("internal error: previous here marker detected");
                    };

                    Arc::new(StmtX::Assert(
                        id.clone(),
                        msg.clone(),
                        filter.clone(),
                        here_focus,
                        expr.clone(),
                    ))
                }
            };
            Some(stmt)
        }
        StmtX::DeadEnd(inner) => {
            let inner = handle_here_recursive(state, inner).unwrap_or_else(make_dummy_stmt);
            Some(Arc::new(StmtX::DeadEnd(inner)))
        }
        StmtX::Breakable(ident, inner) => {
            let inner = handle_here_recursive(state, inner).unwrap_or_else(make_dummy_stmt);
            Some(Arc::new(StmtX::Breakable(ident.clone(), inner)))
        }
        StmtX::Block(items) => {
            let items = items.iter().flat_map(|stmt| handle_here_recursive(state, stmt)).collect();
            Some(Arc::new(StmtX::Block(Arc::new(items))))
        }
        StmtX::Switch(items) => {
            let items = items.iter().flat_map(|stmt| handle_here_recursive(state, stmt)).collect();
            Some(Arc::new(StmtX::Switch(Arc::new(items))))
        }
        _ => Some(stmt.clone()),
    }
}

/// Removes the [here marker](`StmtX::HereMarker`) statement from the query and marks the next
/// assertion with [`HereFocus`].
///
/// This function guarantees that the produced query will not contain any `HereMarker` statements,
/// yet failure to find a corresponding assertion for a removed `HereMarker` is *not* considered an
/// error and does not result in a panic.
///
/// In cases where the here marker cannot be removed, i.e. when it is not inside a block or switch
/// statement, it is instead replaced by an empty block statement.
///
/// # Panics
/// This function may panic if there are multiple here markers in the query.
pub(crate) fn handle_query(query: &Query) -> Query {
    let QueryX { local, assertion } = query.as_ref();
    let mut state = HandleHereState { pending: None };
    let stmt_opt = handle_here_recursive(&mut state, assertion);
    let assertion = stmt_opt.unwrap_or_else(make_dummy_stmt);
    let local = local.clone();
    Arc::new(QueryX { local, assertion })
}
