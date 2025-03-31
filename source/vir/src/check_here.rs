use crate::{
    ast::{Expr, Function},
    ast_visitor::{function_visitor_dfs, VisitorScopeMap},
    visitor::VisitorControlFlow,
};

#[derive(Debug, Clone)]
pub struct HereMarker {
    pub expr: Expr,
    pub function: Function,
}

pub fn check_here(vir_krate: &crate::ast::Krate) -> Vec<HereMarker> {
    let mut markers = Vec::new();
    let mut map = VisitorScopeMap::new();

    for function in &vir_krate.functions {
        function_visitor_dfs(&function, &mut map, &mut |_map, expr| {
            let crate::ast::ExprX::Here { .. } = expr.x else {
                return VisitorControlFlow::Recurse::<()>;
            };

            markers.push(HereMarker { expr: expr.clone(), function: function.clone() });

            VisitorControlFlow::Recurse::<()>
        });
    }

    markers
}
