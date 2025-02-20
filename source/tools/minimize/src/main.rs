use std::{
    collections::{HashMap, HashSet}, env::current_dir, fmt::Debug, ops::RangeInclusive, path::PathBuf, rc::Rc, thread::{sleep, yield_now, JoinHandle}
};

use indicatif::{ProgressBar, ProgressStyle};
use serde::{Deserialize, Serialize};
use syn_verus::{spanned::Spanned, visit::Visit, Attribute, File, Meta, MetaList, Signature};

struct Config {
    print_all: bool,
    #[allow(dead_code)]
    json: bool,
    no_external_by_default: bool,
    delimiters_are_layout: bool,
    permutations_dir: std::path::PathBuf,
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let program = args[0].clone();

    let mut opts = getopts::Options::new();
    opts.optflag("h", "help", "print this help menu");
    opts.optflag("p", "print-all", "print all the annotated files");
    opts.optflag("", "no-external-by-default", "do not ignore items outside of verus! by default");
    opts.reqopt("", "permutations-dir", "the directory to store the source permutations to test", "DIR");
    opts.optflag("", "json", "output as machine-readable json");
    opts.optflag("", "delimiters-are-layout", "consider delimiter-only lines as layout");

    let matches = match opts.parse(&args[1..]) {
        Ok(m) => m,
        Err(f) => {
            panic!("{}", f.to_string())
        }
    };

    fn print_usage(program: &str, opts: getopts::Options) {
        let brief = format!("Usage: {} DEPS_FILE.d [options]", program);
        print!("{}", opts.usage(&brief));
    }

    if matches.opt_present("h") {
        print_usage(&program, opts);
        return;
    }

    let deps_path = if !matches.free.is_empty() {
        matches.free[0].clone()
    } else {
        print_usage(&program, opts);
        return;
    };
    
    let permutations_dir = PathBuf::from(matches.opt_str("permutations-dir").expect("permutations-dir is required"));
    
    let config = Config {
        print_all: matches.opt_present("p"),
        json: matches.opt_present("json"),
        no_external_by_default: matches.opt_present("no-external-by-default"),
        delimiters_are_layout: matches.opt_present("delimiters-are-layout"),
        permutations_dir,
    };

    match run(config, &std::path::Path::new(&deps_path)) {
        Ok(()) => (),
        Err(err) => {
            eprintln!("error: {}", err);
            std::process::exit(1);
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, PartialOrd, Ord)]
enum CodeKind {
    Trusted,
    Spec,
    Proof,
    Exec,
    Directives,
    Definitions,
    Comment,
    Layout,
}

impl CodeKind {
    fn join_prefer_left(&self, other: CodeKind) -> CodeKind {
        match (self, other) {
            (CodeKind::Spec, _) => CodeKind::Spec,
            (_, CodeKind::Spec) => CodeKind::Spec,
            (CodeKind::Proof, _) => CodeKind::Proof,
            (_, CodeKind::Proof) => CodeKind::Proof,
            (CodeKind::Exec, _) => CodeKind::Exec,
            (_, CodeKind::Exec) => CodeKind::Exec,
            (other, _) => *other,
        }
    }
}

trait ToCodeKind {
    fn to_code_kind(&self) -> CodeKind;
}

impl ToCodeKind for syn_verus::DataMode {
    fn to_code_kind(&self) -> CodeKind {
        match self {
            syn_verus::DataMode::Ghost(_) => CodeKind::Spec,
            syn_verus::DataMode::Tracked(_) => CodeKind::Proof,
            syn_verus::DataMode::Exec(_) => CodeKind::Exec,
            syn_verus::DataMode::Default => CodeKind::Exec,
        }
    }
}

impl ToCodeKind for syn_verus::FnMode {
    fn to_code_kind(&self) -> CodeKind {
        match self {
            syn_verus::FnMode::Spec(_) | syn_verus::FnMode::SpecChecked(_) => CodeKind::Spec,
            syn_verus::FnMode::Proof(_) => CodeKind::Proof,
            syn_verus::FnMode::Exec(_) | syn_verus::FnMode::Default => CodeKind::Exec,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum StateMachineCode {
    NameAndFields,
    Transition,
    Property,
    StructWithInvariantBody,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum LineContent {
    Const(CodeKind),
    Code(CodeKind),
    DatatypeDecl,
    TypeDefinition,
    Trait,
    ProofBlock,
    ProofDirective, // Assert, Assume, Reveal, ...
    ProofBinding,
    Impl,
    Signature(CodeKind),
    FunctionSpec,
    Body(CodeKind),
    Directive,
    MacroDefinition,
    GhostTracked(CodeKind),
    Comment,
    StateMachine(StateMachineCode),
    Atomic,
}

struct LineInfo {
    kinds: HashSet<CodeKind>,
    #[allow(dead_code)]
    path: String,
    line_content: HashSet<LineContent>,
    text: String,
}

#[derive(Debug, Clone, Serialize)]
struct Lines {
    lines: RangeInclusive<usize>,
}

// implement Lines to Vec<usize>
impl From<Lines> for Vec<usize> {
    fn from(lines: Lines) -> Vec<usize> {
        lines.lines.collect()
    }
}

impl std::fmt::Display for Lines {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}-{}", self.lines.start(), self.lines.end())
    }
}

struct FileData {
    contents: String,
    lines: Box<[LineInfo]>,
    // each assert/assert_forall is some lines
    asserts: Vec<Lines>,
}

fn to_lines_range(spanned: &impl Spanned) -> RangeInclusive<usize> {
    let span = spanned.span();
    let proc_macro2::LineColumn { line: start_line, column: _ } = span.start();
    let proc_macro2::LineColumn { line: end_line, column: _ } = span.end();
    (start_line - 1)..=(end_line - 1)
}

impl FileData {
    #[allow(dead_code)]
    fn mark_kind(&mut self, spanned: &impl Spanned, kind: CodeKind) {
        for l in to_lines_range(spanned) {
            self.lines[l]
                .kinds
                .retain(|x| !matches!(x, CodeKind::Spec | CodeKind::Proof | CodeKind::Exec));
            self.lines[l].kinds.insert(kind);
        }
    }

    #[allow(dead_code)]
    fn mark_additional_kind(&mut self, spanned: &impl Spanned, kind: CodeKind) {
        for l in to_lines_range(spanned) {
            self.lines[l].kinds.insert(kind);
        }
    }

    fn mark_content(&mut self, spanned: &impl Spanned, content: LineContent) {
        for l in to_lines_range(spanned) {
            self.lines[l].line_content.insert(content);
        }
    }

    fn mark(&mut self, spanned: &(impl Spanned + Debug), kind: CodeKind, content: LineContent) {
        for l in to_lines_range(spanned) {
            self.lines[l]
                .kinds
                .retain(|x| !matches!(x, CodeKind::Spec | CodeKind::Proof | CodeKind::Exec));
            self.lines[l].kinds.insert(kind);
            self.lines[l].line_content.insert(content);
        }
    }

    fn mark_with_additional_kind(
        &mut self,
        spanned: &impl Spanned,
        kind: CodeKind,
        content: LineContent,
    ) {
        for l in to_lines_range(spanned) {
            self.lines[l].kinds.insert(kind);
            self.lines[l].line_content.insert(content);
        }
    }

    fn mark_assert(&mut self, spaned: &impl Spanned) {
        let lines = to_lines_range(spaned);
        let start = *lines.start();
        let end = *lines.end();
        self.asserts.push(Lines { lines: (start..=end) });
    }
}

struct Visitor<'f> {
    inside_verus_macro_or_verify_or_consider: u64,
    file_stats: &'f mut FileData,
    in_body: Option<CodeKind>,
    trusted: u64,
    in_proof_directive: u64,
    in_state_machine_macro: u64,
    inside_line_count_ignore_or_external: u64,
    config: Rc<Config>,
}

impl<'f> Visitor<'f> {
    fn active(&self) -> bool {
        self.inside_line_count_ignore_or_external == 0
            && (self.inside_verus_macro_or_verify_or_consider > 0
                || self.config.no_external_by_default)
    }

    #[allow(dead_code)]
    fn mark_kind(&mut self, spanned: &impl Spanned, kind: CodeKind) {
        if self.active() {
            self.file_stats.mark_kind(spanned, kind);
        }
    }

    #[allow(dead_code)]
    fn mark_additional_kind(&mut self, spanned: &impl Spanned, kind: CodeKind) {
        if self.active() {
            self.file_stats.mark_additional_kind(spanned, kind)
        }
    }

    fn mark_content(&mut self, spanned: &impl Spanned, content: LineContent) {
        if self.active() {
            self.file_stats.mark_content(spanned, content);
        }
    }

    fn mark(&mut self, spanned: &(impl Spanned + Debug), kind: CodeKind, content: LineContent) {
        if self.active() {
            self.file_stats.mark(spanned, kind, content);
        }
    }

    fn mark_with_additional_kind(
        &mut self,
        spanned: &impl Spanned,
        kind: CodeKind,
        content: LineContent,
    ) {
        if self.active() {
            self.file_stats.mark_with_additional_kind(spanned, kind, content);
        }
    }

    fn mark_assert(&mut self, spanned: &impl Spanned) {
        if self.active() {
            self.file_stats.mark_assert(spanned);
        }
    }
}

impl<'ast, 'f> syn_verus::visit::Visit<'ast> for Visitor<'f> {
    fn visit_assert(&mut self, i: &'ast syn_verus::Assert) {
        self.in_proof_directive += 1;
        self.mark(i, self.mode_or_trusted(CodeKind::Proof), LineContent::ProofDirective);
        syn_verus::visit::visit_assert(self, i);
        self.in_proof_directive -= 1;
        self.mark_assert(i);
    }

    fn visit_assert_forall(&mut self, i: &'ast syn_verus::AssertForall) {
        self.in_proof_directive += 1;
        self.mark(i, self.mode_or_trusted(CodeKind::Proof), LineContent::ProofDirective);
        syn_verus::visit::visit_assert_forall(self, i);
        self.in_proof_directive -= 1;
        self.mark_assert(i);
    }

    fn visit_assume(&mut self, i: &'ast syn_verus::Assume) {
        self.in_proof_directive += 1;
        self.mark(i, self.mode_or_trusted(CodeKind::Proof), LineContent::ProofDirective);
        syn_verus::visit::visit_assume(self, i);
        self.in_proof_directive -= 1;
    }

    #[allow(unreachable_code)]
    fn visit_data(&mut self, _i: &'ast syn_verus::Data) {
        panic!("data unsupported");
        syn_verus::visit::visit_data(self, _i);
    }

    fn visit_decreases(&mut self, i: &'ast syn_verus::Decreases) {
        // self.mark(i, self.mode_or_trusted(CodeKind::Spec), LineContent::FunctionSpec);
        syn_verus::visit::visit_decreases(self, i);
    }

    fn visit_ensures(&mut self, i: &'ast syn_verus::Ensures) {
        // self.mark(i, self.mode_or_trusted(CodeKind::Spec), LineContent::FunctionSpec);
        syn_verus::visit::visit_ensures(self, i);
    }

    fn visit_block(&mut self, i: &'ast syn_verus::Block) {
        if let Some(content_code_kind) = self.in_body {
            if self.in_proof_directive == 0 {
                self.mark(
                    &i,
                    self.mode_or_trusted(content_code_kind),
                    LineContent::Code(content_code_kind),
                )
            }
        }
        syn_verus::visit::visit_block(self, i);
    }

    fn visit_expr(&mut self, i: &'ast syn_verus::Expr) {
        if let Some(content_code_kind) = self.in_body {
            if self.in_proof_directive == 0 {
                self.mark(
                    &i,
                    self.mode_or_trusted(content_code_kind),
                    LineContent::Code(content_code_kind),
                )
            }
        }
        let entered_proof_directive = match i {
            syn_verus::Expr::Unary(syn_verus::ExprUnary {
                op: syn_verus::UnOp::Proof(..),
                attrs: _,
                expr,
            }) => {
                self.mark(expr, self.mode_or_trusted(CodeKind::Proof), LineContent::ProofBlock);
                self.in_proof_directive += 1;
                true
            }
            _ => false,
        };
        syn_verus::visit::visit_expr(self, i);
        if entered_proof_directive {
            self.in_proof_directive -= 1;
        }
    }

    fn visit_expr_block(&mut self, i: &'ast syn_verus::ExprBlock) {
        syn_verus::visit::visit_expr_block(self, i);
    }

    fn visit_expr_call(&mut self, i: &'ast syn_verus::ExprCall) {
        // Ghost / Tracked ?
        if let syn_verus::Expr::Path(path) = &*i.func {
            if let Some(wrapper_code_kind) = (path.path.segments.len() == 1)
                .then(|| path.path.segments[0].ident.to_string())
                .and_then(|c| match c.as_str() {
                    "Ghost" => {
                        if self.in_body == Some(CodeKind::Spec) {
                            Some(self.mode_or_trusted(CodeKind::Spec))
                        } else {
                            Some(self.mode_or_trusted(CodeKind::Proof))
                        }
                    }
                    "Tracked" => Some(self.mode_or_trusted(CodeKind::Proof)),
                    _ => None,
                })
            {
                self.mark_with_additional_kind(
                    i,
                    wrapper_code_kind,
                    LineContent::GhostTracked(wrapper_code_kind),
                );
                return;
            }
        }
        syn_verus::visit::visit_expr_call(self, i);
    }

    fn visit_expr_closure(&mut self, i: &'ast syn_verus::ExprClosure) {
        // TODO
        syn_verus::visit::visit_expr_closure(self, i);
    }

    fn visit_expr_loop(&mut self, i: &'ast syn_verus::ExprLoop) {
        if let Some(decreases) = &i.decreases {
            self.mark(
                decreases,
                self.mode_or_trusted(CodeKind::Proof),
                LineContent::ProofDirective,
            );
        }
        if let Some(invariant_except_break) = &i.invariant_except_break {
            self.mark(
                &invariant_except_break,
                self.mode_or_trusted(CodeKind::Proof),
                LineContent::ProofDirective,
            );
        }
        if let Some(invariant) = &i.invariant {
            self.mark(
                &invariant,
                self.mode_or_trusted(CodeKind::Proof),
                LineContent::ProofDirective,
            );
        }
        if let Some(invariant_ensures) = &i.invariant_ensures {
            self.mark(
                &invariant_ensures,
                self.mode_or_trusted(CodeKind::Proof),
                LineContent::ProofDirective,
            );
        }
        if let Some(ensures) = &i.ensures {
            self.mark(&ensures, self.mode_or_trusted(CodeKind::Proof), LineContent::ProofDirective);
        }
        self.visit_block(&i.body);
    }

    fn visit_expr_while(&mut self, i: &'ast syn_verus::ExprWhile) {
        if let Some(decreases) = &i.decreases {
            self.mark(
                decreases,
                self.mode_or_trusted(CodeKind::Proof),
                LineContent::ProofDirective,
            );
        }
        if let Some(invariant_except_break) = &i.invariant_except_break {
            self.mark(
                &invariant_except_break,
                self.mode_or_trusted(CodeKind::Proof),
                LineContent::ProofDirective,
            );
        }
        if let Some(invariant) = &i.invariant {
            self.mark(
                &invariant,
                self.mode_or_trusted(CodeKind::Proof),
                LineContent::ProofDirective,
            );
        }
        if let Some(invariant_ensures) = &i.invariant_ensures {
            self.mark(
                &invariant_ensures,
                self.mode_or_trusted(CodeKind::Proof),
                LineContent::ProofDirective,
            );
        }
        if let Some(ensures) = &i.ensures {
            self.mark(&ensures, self.mode_or_trusted(CodeKind::Proof), LineContent::ProofDirective);
        }
        self.visit_expr(&i.cond);
        self.visit_block(&i.body);
    }

    fn visit_impl_item_fn(&mut self, i: &'ast syn_verus::ImplItemFn) {
        let content_code_kind = i.sig.mode.to_code_kind();
        let exit = self.item_attr_enter(&i.attrs);
        let code_kind = self.mode_or_trusted(content_code_kind);
        // self.mark(&i.block, code_kind, LineContent::Code(content_code_kind));
        self.mark_content(&i.block, LineContent::Body(content_code_kind));
        self.handle_signature(content_code_kind, code_kind, &i.sig);
        self.in_body = Some(content_code_kind);
        self.visit_block(&i.block);
        self.in_body = None;
        exit.exit(self);
    }

    fn visit_item(&mut self, i: &'ast syn_verus::Item) {
        match i {
            syn_verus::Item::Impl(_) => {
                self.mark_content(i, LineContent::Impl);
            }
            _ => (),
        }
        syn_verus::visit::visit_item(self, i);
    }

    fn visit_item_const(&mut self, i: &'ast syn_verus::ItemConst) {
        let exit = self.item_attr_enter(&i.attrs);
        self.mark(
            i,
            self.mode_or_trusted(i.mode.to_code_kind()),
            LineContent::Const(i.mode.to_code_kind()),
        );
        syn_verus::visit::visit_item_const(self, i);
        exit.exit(self);
    }

    fn visit_item_enum(&mut self, i: &'ast syn_verus::ItemEnum) {
        let exit = self.item_attr_enter(&i.attrs);
        self.mark(&i, self.mode_or_trusted(i.mode.to_code_kind()), LineContent::DatatypeDecl);
        syn_verus::visit::visit_item_enum(self, i);
        exit.exit(self);
    }

    fn visit_item_extern_crate(&mut self, i: &'ast syn_verus::ItemExternCrate) {
        let exit = self.item_attr_enter(&i.attrs);
        syn_verus::visit::visit_item_extern_crate(self, i);
        exit.exit(self);
    }

    fn visit_item_fn(&mut self, i: &'ast syn_verus::ItemFn) {
        let exit = self.item_attr_enter(&i.attrs);
        let content_code_kind = self.fn_code_kind(i.sig.mode.to_code_kind());
        let code_kind = self.mode_or_trusted(content_code_kind);
        // self.mark(&i.block, code_kind, LineContent::Code(content_code_kind));
        self.mark_content(&i.block, LineContent::Body(content_code_kind));
        self.handle_signature(content_code_kind, code_kind, &i.sig);
        self.in_body = Some(content_code_kind);
        self.visit_block(&i.block);
        self.in_body = None;
        exit.exit(self);
    }

    fn visit_item_foreign_mod(&mut self, i: &'ast syn_verus::ItemForeignMod) {
        let exit = self.item_attr_enter(&i.attrs);
        syn_verus::visit::visit_item_foreign_mod(self, i);
        exit.exit(self);
    }

    fn visit_item_impl(&mut self, i: &'ast syn_verus::ItemImpl) {
        let exit = self.item_attr_enter(&i.attrs);
        syn_verus::visit::visit_item_impl(self, i);
        exit.exit(self);
    }

    fn visit_item_macro(&mut self, i: &'ast syn_verus::ItemMacro) {
        syn_verus::visit::visit_item_macro(self, i);
    }

    fn visit_item_mod(&mut self, i: &'ast syn_verus::ItemMod) {
        let exit = self.item_attr_enter(&i.attrs);
        if i.content.is_none() {
            self.mark(&i, CodeKind::Directives, LineContent::Directive);
        }
        syn_verus::visit::visit_item_mod(self, i);
        exit.exit(self);
    }

    fn visit_item_static(&mut self, i: &'ast syn_verus::ItemStatic) {
        let exit = self.item_attr_enter(&i.attrs);
        syn_verus::visit::visit_item_static(self, i);
        exit.exit(self);
    }

    fn visit_item_struct(&mut self, i: &'ast syn_verus::ItemStruct) {
        let exit = self.item_attr_enter(&i.attrs);
        self.mark(&i, self.mode_or_trusted(i.mode.to_code_kind()), LineContent::DatatypeDecl);
        syn_verus::visit::visit_item_struct(self, i);
        exit.exit(self);
    }

    fn visit_item_trait(&mut self, i: &'ast syn_verus::ItemTrait) {
        let exit = self.item_attr_enter(&i.attrs);
        self.mark_content(&i, LineContent::Trait);
        if self.trusted > 0 {
            self.mark_kind(&i, CodeKind::Trusted);
        }
        syn_verus::visit::visit_item_trait(self, i);
        exit.exit(self);
    }

    fn visit_field(&mut self, i: &'ast syn_verus::Field) {
        if let syn_verus::Type::Path(path) = &i.ty {
            if let Some(wrapper_code_kind) = (path.path.segments.len() == 1)
                .then(|| path.path.segments[0].ident.to_string())
                .and_then(|c| match c.as_str() {
                    "Ghost" => {
                        if self.in_body == Some(CodeKind::Spec) {
                            Some(self.mode_or_trusted(CodeKind::Spec))
                        } else {
                            Some(self.mode_or_trusted(CodeKind::Proof))
                        }
                    }
                    "Tracked" => Some(self.mode_or_trusted(CodeKind::Proof)),
                    _ => None,
                })
            {
                self.mark(i, wrapper_code_kind, LineContent::GhostTracked(wrapper_code_kind));
                return;
            }
        }
        syn_verus::visit::visit_field(self, i);
    }

    fn visit_item_trait_alias(&mut self, i: &'ast syn_verus::ItemTraitAlias) {
        let exit = self.item_attr_enter(&i.attrs);
        syn_verus::visit::visit_item_trait_alias(self, i);
        exit.exit(self);
    }

    fn visit_item_type(&mut self, i: &'ast syn_verus::ItemType) {
        let exit = self.item_attr_enter(&i.attrs);
        syn_verus::visit::visit_item_type(self, i);
        exit.exit(self);
    }

    fn visit_item_use(&mut self, i: &'ast syn_verus::ItemUse) {
        let exit = self.item_attr_enter(&i.attrs);
        syn_verus::visit::visit_item_use(self, i);
        exit.exit(self);
    }

    fn visit_label(&mut self, i: &'ast syn_verus::Label) {
        syn_verus::visit::visit_label(self, i);
    }

    fn visit_lifetime(&mut self, i: &'ast syn_verus::Lifetime) {
        syn_verus::visit::visit_lifetime(self, i);
    }

    fn visit_lit(&mut self, i: &'ast syn_verus::Lit) {
        syn_verus::visit::visit_lit(self, i);
    }

    fn visit_lit_bool(&mut self, i: &'ast syn_verus::LitBool) {
        syn_verus::visit::visit_lit_bool(self, i);
    }

    fn visit_lit_byte(&mut self, i: &'ast syn_verus::LitByte) {
        syn_verus::visit::visit_lit_byte(self, i);
    }

    fn visit_lit_byte_str(&mut self, i: &'ast syn_verus::LitByteStr) {
        syn_verus::visit::visit_lit_byte_str(self, i);
    }

    fn visit_lit_char(&mut self, i: &'ast syn_verus::LitChar) {
        syn_verus::visit::visit_lit_char(self, i);
    }

    fn visit_lit_float(&mut self, i: &'ast syn_verus::LitFloat) {
        syn_verus::visit::visit_lit_float(self, i);
    }

    fn visit_lit_int(&mut self, i: &'ast syn_verus::LitInt) {
        syn_verus::visit::visit_lit_int(self, i);
    }

    fn visit_lit_str(&mut self, i: &'ast syn_verus::LitStr) {
        syn_verus::visit::visit_lit_str(self, i);
    }

    fn visit_local(&mut self, i: &'ast syn_verus::Local) {
        if i.ghost.is_some() || i.tracked.is_some() {
            self.mark(i, self.mode_or_trusted(CodeKind::Proof), LineContent::ProofBinding);
        }
        syn_verus::visit::visit_local(self, i);
    }

    fn visit_macro(&mut self, i: &'ast syn_verus::Macro) {
        let mut entered_state_machine_macro = false;
        let mut entered_struct_with_invariants = false;
        let outer_last_segment = i.path.segments.last().map(|s| s.ident.to_string());
        if outer_last_segment == Some("macro_rules".into()) {
            self.mark(i, self.mode_or_trusted(CodeKind::Definitions), LineContent::MacroDefinition);
        } else if outer_last_segment == Some("verus".into()) {
            let source_toks = &i.tokens;
            let macro_content: File = syn_verus::parse2(source_toks.clone())
                .map_err(|e| {
                    dbg!(&e.span().start(), &e.span().end());
                    format!("failed to parse file macro contents: {} {:?}", e, e.span())
                })
                .expect("unexpected verus! macro content");
            self.inside_verus_macro_or_verify_or_consider += 1;
            self.visit_file(&macro_content);
            self.inside_verus_macro_or_verify_or_consider -= 1;
        } else if outer_last_segment == Some("tokenized_state_machine".into())
            || outer_last_segment == Some("state_machine".into())
        {
            // self.mark(
            //     i,
            //     self.mode_or_trusted(CodeKind::Spec),
            //     LineContent::StateMachine(StateMachineCode::NameAndFields),
            // );
            entered_state_machine_macro = true;
            self.inside_verus_macro_or_verify_or_consider += 1;
            self.in_state_machine_macro += 1;
            use proc_macro2::TokenTree;
            for tok in i.tokens.clone() {
                match tok {
                    TokenTree::Group(g) => {
                        let mut g_stream = g.stream().into_iter().peekable();
                        if !(g.delimiter() == proc_macro2::Delimiter::Brace
                            && g_stream.next().map(|t| t.to_string()) == Some("fields".into()))
                        {
                            continue;
                        }
                        if let Some(fields_g) = g_stream.next() {
                            if let TokenTree::Group(g) = fields_g {
                                self.mark(
                                    &g,
                                    self.mode_or_trusted(CodeKind::Spec),
                                    LineContent::StateMachine(StateMachineCode::NameAndFields),
                                );
                            } else {
                                continue;
                            }
                        } else {
                            continue;
                        }
                        // let mut next_t = g_stream.next();
                        let content_as_file: Option<syn_verus::File> =
                            syn_verus::parse2(proc_macro2::TokenStream::from_iter(g_stream)).ok();
                        if let Some(content_as_file) = content_as_file {
                            // self.visit_file(&content_as_file);
                            for item in content_as_file.items {
                                match item {
                                    syn_verus::Item::Macro(m) => {
                                        let last_segment =
                                            m.mac.path.segments.last().map(|s| s.ident.to_string());
                                        if last_segment == Some("transition".into())
                                            || last_segment == Some("init".into())
                                        {
                                            self.mark(
                                                &m,
                                                self.mode_or_trusted(CodeKind::Spec),
                                                LineContent::StateMachine(
                                                    StateMachineCode::Transition,
                                                ),
                                            );
                                        } else if last_segment == Some("property".into()) {
                                            self.mark(
                                                &m,
                                                self.mode_or_trusted(CodeKind::Spec),
                                                LineContent::StateMachine(
                                                    StateMachineCode::Property,
                                                ),
                                            );
                                        }
                                    }
                                    _ => self.visit_item(&item),
                                }
                            }
                        }
                    }
                    TokenTree::Ident(ident) => {
                        self.mark(
                            &ident,
                            self.mode_or_trusted(CodeKind::Spec),
                            LineContent::StateMachine(StateMachineCode::NameAndFields),
                        );
                    }
                    TokenTree::Punct(_) => (),
                    TokenTree::Literal(_) => (),
                }
            }
        } else if outer_last_segment == Some("struct_with_invariants".into()) {
            entered_struct_with_invariants = true;
            self.inside_verus_macro_or_verify_or_consider += 1;

            let mut found_braced_group = false;
            let mut tokens_here = i.tokens.clone().into_iter();
            let s = proc_macro2::TokenStream::from_iter(tokens_here.by_ref().take_while(|t| {
                match t {
                    proc_macro2::TokenTree::Group(g) => {
                        if g.delimiter() == proc_macro2::Delimiter::Brace {
                            found_braced_group = true;
                            return true;
                        }
                    }
                    _ => (),
                }
                !found_braced_group
            }));
            let content_as_file: Option<syn_verus::File> = syn_verus::parse2(s).ok();
            if let Some(content_as_file) = content_as_file {
                for item in content_as_file.items {
                    self.visit_item(&item);
                }
            }
            for tok in tokens_here {
                self.mark(
                    &tok.span(),
                    CodeKind::Spec,
                    LineContent::StateMachine(StateMachineCode::StructWithInvariantBody),
                );
            }
        } else if outer_last_segment == Some("atomic_with_ghost".into())
            || outer_last_segment == Some("my_atomic_with_ghost".into())
        // for mem allocator
        {
            let mut tokens_here = i.tokens.clone().into_iter();
            for tok in proc_macro2::TokenStream::from_iter(
                tokens_here.by_ref().take_while(|t| t.to_string() != ";"),
            ) {
                self.mark(&tok.span(), CodeKind::Exec, LineContent::Atomic);
            }
            for tok in tokens_here {
                self.mark(&tok.span(), CodeKind::Proof, LineContent::Atomic);
            }
        } else if outer_last_segment == Some("tld_get_mut".into())
            || outer_last_segment == Some("page_get_mut_inner".into())
            || outer_last_segment == Some("unused_page_get_mut_prev".into())
            || outer_last_segment == Some("unused_page_get_mut_inner".into())
            || outer_last_segment == Some("unused_page_get_mut_next".into())
            || outer_last_segment == Some("unused_page_get_mut_count".into())
            || outer_last_segment == Some("unused_page_get_mut".into())
            || outer_last_segment == Some("used_page_get_mut_prev".into())
            || outer_last_segment == Some("heap_get_pages".into())
            || outer_last_segment == Some("heap_get_pages_free_direct".into())
            || outer_last_segment == Some("used_page_get_mut_next".into())
            || outer_last_segment == Some("segment_get_mut_main".into())
            || outer_last_segment == Some("segment_get_mut_main2".into())
            || outer_last_segment == Some("segment_get_mut_local".into())
        {
            for tok in i.tokens.clone().into_iter() {
                match tok.clone() {
                    proc_macro2::TokenTree::Group(g) => {
                        if g.delimiter() == proc_macro2::Delimiter::Brace {
                            let content_as_block: Option<syn_verus::Block> =
                                syn_verus::parse2(tok.into()).ok();
                            if let Some(content_as_block) = content_as_block {
                                self.visit_block(&content_as_block);
                            }
                        }
                    }
                    _ => (),
                }
            }
        }
        syn_verus::visit::visit_macro(self, i);
        if entered_state_machine_macro {
            self.in_state_machine_macro -= 1;
            self.inside_verus_macro_or_verify_or_consider -= 1;
        }
        if entered_struct_with_invariants {
            self.inside_verus_macro_or_verify_or_consider -= 1;
        }
    }

    fn visit_macro_delimiter(&mut self, i: &'ast syn_verus::MacroDelimiter) {
        syn_verus::visit::visit_macro_delimiter(self, i);
    }

    fn visit_member(&mut self, i: &'ast syn_verus::Member) {
        syn_verus::visit::visit_member(self, i);
    }

    fn visit_meta(&mut self, i: &'ast syn_verus::Meta) {
        syn_verus::visit::visit_meta(self, i);
    }

    fn visit_meta_list(&mut self, i: &'ast syn_verus::MetaList) {
        syn_verus::visit::visit_meta_list(self, i);
    }

    fn visit_meta_name_value(&mut self, i: &'ast syn_verus::MetaNameValue) {
        syn_verus::visit::visit_meta_name_value(self, i);
    }

    fn visit_mode(&mut self, i: &'ast syn_verus::Mode) {
        syn_verus::visit::visit_mode(self, i);
    }

    fn visit_mode_exec(&mut self, i: &'ast syn_verus::ModeExec) {
        syn_verus::visit::visit_mode_exec(self, i);
    }

    fn visit_mode_ghost(&mut self, i: &'ast syn_verus::ModeGhost) {
        syn_verus::visit::visit_mode_ghost(self, i);
    }

    fn visit_mode_proof(&mut self, i: &'ast syn_verus::ModeProof) {
        syn_verus::visit::visit_mode_proof(self, i);
    }

    fn visit_mode_spec(&mut self, i: &'ast syn_verus::ModeSpec) {
        syn_verus::visit::visit_mode_spec(self, i);
    }

    fn visit_mode_spec_checked(&mut self, i: &'ast syn_verus::ModeSpecChecked) {
        syn_verus::visit::visit_mode_spec_checked(self, i);
    }

    fn visit_mode_tracked(&mut self, i: &'ast syn_verus::ModeTracked) {
        syn_verus::visit::visit_mode_tracked(self, i);
    }

    fn visit_open(&mut self, i: &'ast syn_verus::Open) {
        syn_verus::visit::visit_open(self, i);
    }

    fn visit_open_restricted(&mut self, i: &'ast syn_verus::OpenRestricted) {
        syn_verus::visit::visit_open_restricted(self, i);
    }

    fn visit_parenthesized_generic_arguments(
        &mut self,
        i: &'ast syn_verus::ParenthesizedGenericArguments,
    ) {
        syn_verus::visit::visit_parenthesized_generic_arguments(self, i);
    }

    fn visit_pat(&mut self, i: &'ast syn_verus::Pat) {
        syn_verus::visit::visit_pat(self, i);
    }

    fn visit_pat_ident(&mut self, i: &'ast syn_verus::PatIdent) {
        syn_verus::visit::visit_pat_ident(self, i);
    }

    fn visit_pat_or(&mut self, i: &'ast syn_verus::PatOr) {
        syn_verus::visit::visit_pat_or(self, i);
    }

    fn visit_pat_slice(&mut self, i: &'ast syn_verus::PatSlice) {
        syn_verus::visit::visit_pat_slice(self, i);
    }

    fn visit_pat_struct(&mut self, i: &'ast syn_verus::PatStruct) {
        syn_verus::visit::visit_pat_struct(self, i);
    }

    fn visit_pat_tuple(&mut self, i: &'ast syn_verus::PatTuple) {
        syn_verus::visit::visit_pat_tuple(self, i);
    }

    fn visit_pat_tuple_struct(&mut self, i: &'ast syn_verus::PatTupleStruct) {
        syn_verus::visit::visit_pat_tuple_struct(self, i);
    }

    fn visit_pat_type(&mut self, i: &'ast syn_verus::PatType) {
        syn_verus::visit::visit_pat_type(self, i);
    }

    fn visit_pat_wild(&mut self, i: &'ast syn_verus::PatWild) {
        syn_verus::visit::visit_pat_wild(self, i);
    }

    fn visit_path(&mut self, i: &'ast syn_verus::Path) {
        syn_verus::visit::visit_path(self, i);
    }

    fn visit_path_arguments(&mut self, i: &'ast syn_verus::PathArguments) {
        syn_verus::visit::visit_path_arguments(self, i);
    }

    fn visit_path_segment(&mut self, i: &'ast syn_verus::PathSegment) {
        syn_verus::visit::visit_path_segment(self, i);
    }

    fn visit_predicate_lifetime(&mut self, i: &'ast syn_verus::PredicateLifetime) {
        syn_verus::visit::visit_predicate_lifetime(self, i);
    }

    fn visit_predicate_type(&mut self, i: &'ast syn_verus::PredicateType) {
        syn_verus::visit::visit_predicate_type(self, i);
    }

    fn visit_publish(&mut self, i: &'ast syn_verus::Publish) {
        syn_verus::visit::visit_publish(self, i);
    }

    fn visit_qself(&mut self, i: &'ast syn_verus::QSelf) {
        syn_verus::visit::visit_qself(self, i);
    }

    fn visit_range_limits(&mut self, i: &'ast syn_verus::RangeLimits) {
        syn_verus::visit::visit_range_limits(self, i);
    }

    fn visit_receiver(&mut self, i: &'ast syn_verus::Receiver) {
        syn_verus::visit::visit_receiver(self, i);
    }

    fn visit_recommends(&mut self, i: &'ast syn_verus::Recommends) {
        // self.mark(i, self.mode_or_trusted(CodeKind::Spec), LineContent::FunctionSpec);
        syn_verus::visit::visit_recommends(self, i);
    }

    fn visit_requires(&mut self, i: &'ast syn_verus::Requires) {
        // self.mark(i, self.mode_or_trusted(CodeKind::Spec), LineContent::FunctionSpec);
        syn_verus::visit::visit_requires(self, i);
    }

    fn visit_return_type(&mut self, i: &'ast syn_verus::ReturnType) {
        syn_verus::visit::visit_return_type(self, i);
    }

    fn visit_reveal_hide(&mut self, i: &'ast syn_verus::RevealHide) {
        syn_verus::visit::visit_reveal_hide(self, i);
    }

    fn visit_signature(&mut self, i: &'ast syn_verus::Signature) {
        syn_verus::visit::visit_signature(self, i);
    }

    fn visit_signature_decreases(&mut self, i: &'ast syn_verus::SignatureDecreases) {
        syn_verus::visit::visit_signature_decreases(self, i);
    }

    fn visit_signature_invariants(&mut self, i: &'ast syn_verus::SignatureInvariants) {
        syn_verus::visit::visit_signature_invariants(self, i);
    }

    fn visit_span(&mut self, i: &proc_macro2::Span) {
        syn_verus::visit::visit_span(self, i);
    }

    fn visit_specification(&mut self, i: &'ast syn_verus::Specification) {
        syn_verus::visit::visit_specification(self, i);
    }

    fn visit_stmt(&mut self, i: &'ast syn_verus::Stmt) {
        match i {
            syn_verus::Stmt::Local(syn_verus::Local {
                attrs: _,
                let_token: _,
                tracked,
                ghost,
                pat: _,
                init,
                semi_token: _,
            }) => {
                if tracked.is_some() {
                    self.mark(i, CodeKind::Proof, LineContent::GhostTracked(CodeKind::Proof));
                    return;
                }
                if ghost.is_some() {
                    if self.in_body == Some(CodeKind::Spec) {
                        self.mark(i, CodeKind::Spec, LineContent::GhostTracked(CodeKind::Spec));
                    } else {
                        self.mark(i, CodeKind::Proof, LineContent::GhostTracked(CodeKind::Proof));
                    }
                    return;
                }
                // let a = Ghost(...)
                if let Some(right) = init {
                    if right.diverge.is_some() {
                        // the else branch of let
                        warn("else branch in let currently not supported");
                    }
                    match &*right.expr {
                        syn_verus::Expr::Call(call_expr) => {
                            let syn_verus::ExprCall { attrs: _, func, paren_token: _, args: _ } =
                                &*call_expr;
                            if let syn_verus::Expr::Path(path) = &**func {
                                if let Some(wrapper_code_kind) = (path.path.segments.len() == 1)
                                    .then(|| path.path.segments[0].ident.to_string())
                                    .and_then(|c| match c.as_str() {
                                        "Ghost" => {
                                            if self.in_body == Some(CodeKind::Spec) {
                                                Some(self.mode_or_trusted(CodeKind::Spec))
                                            } else {
                                                Some(self.mode_or_trusted(CodeKind::Proof))
                                            }
                                        }
                                        "Tracked" => Some(self.mode_or_trusted(CodeKind::Proof)),
                                        _ => None,
                                    })
                                {
                                    self.mark(
                                        i,
                                        wrapper_code_kind,
                                        LineContent::GhostTracked(wrapper_code_kind),
                                    );
                                    return;
                                }
                            }
                        }
                        _ => (),
                    }
                }
            }
            _ => (),
        }
        syn_verus::visit::visit_stmt(self, i);
    }

    fn visit_trait_bound(&mut self, i: &'ast syn_verus::TraitBound) {
        syn_verus::visit::visit_trait_bound(self, i);
    }

    fn visit_trait_bound_modifier(&mut self, i: &'ast syn_verus::TraitBoundModifier) {
        syn_verus::visit::visit_trait_bound_modifier(self, i);
    }

    fn visit_trait_item(&mut self, i: &'ast syn_verus::TraitItem) {
        syn_verus::visit::visit_trait_item(self, i);
    }

    fn visit_trait_item_const(&mut self, i: &'ast syn_verus::TraitItemConst) {
        syn_verus::visit::visit_trait_item_const(self, i);
    }

    fn visit_trait_item_macro(&mut self, i: &'ast syn_verus::TraitItemMacro) {
        syn_verus::visit::visit_trait_item_macro(self, i);
    }

    fn visit_trait_item_fn(&mut self, i: &'ast syn_verus::TraitItemFn) {
        let exit = self.item_attr_enter(&i.attrs);
        let content_code_kind = i.sig.mode.to_code_kind();
        let code_kind = self.mode_or_trusted(content_code_kind);
        self.mark_content(&i, LineContent::Trait);
        // self.mark(&i.default, code_kind, LineContent::Code(content_code_kind));
        self.mark_content(&i.default, LineContent::Body(content_code_kind));
        self.handle_signature(content_code_kind, code_kind, &i.sig);
        self.in_body = Some(content_code_kind);
        if let Some(default) = &i.default {
            self.visit_block(default);
        }
        syn_verus::visit::visit_trait_item_fn(self, i);
        self.in_body = None;
        exit.exit(self);
    }

    fn visit_trait_item_type(&mut self, i: &'ast syn_verus::TraitItemType) {
        self.mark(&i, CodeKind::Definitions, LineContent::TypeDefinition);
        syn_verus::visit::visit_trait_item_type(self, i);
    }

    fn visit_type(&mut self, i: &'ast syn_verus::Type) {
        // self.mark(&i, CodeKind::Definitions, LineContent::TypeDefinition);
        syn_verus::visit::visit_type(self, i);
    }

    fn visit_use_tree(&mut self, i: &'ast syn_verus::UseTree) {
        self.mark(i, CodeKind::Directives, LineContent::Directive);
        syn_verus::visit::visit_use_tree(self, i);
    }

    fn visit_view(&mut self, i: &'ast syn_verus::View) {
        syn_verus::visit::visit_view(self, i);
    }

    fn visit_where_clause(&mut self, i: &'ast syn_verus::WhereClause) {
        syn_verus::visit::visit_where_clause(self, i);
    }

    fn visit_where_predicate(&mut self, i: &'ast syn_verus::WherePredicate) {
        syn_verus::visit::visit_where_predicate(self, i);
    }
}

struct ItemAttrExit {
    entered_trusted: bool,
    entered_ignore: bool,
    entered_verify: bool,
    entered_external: bool,
    entered_consider: bool,
}

impl ItemAttrExit {
    fn exit(self, visitor: &mut Visitor) {
        if self.entered_trusted {
            visitor.trusted -= 1;
        }
        if self.entered_ignore {
            visitor.inside_line_count_ignore_or_external -= 1;
        }
        if self.entered_verify {
            visitor.inside_verus_macro_or_verify_or_consider -= 1;
        }
        if self.entered_external {
            visitor.inside_line_count_ignore_or_external -= 1;
        }
        if self.entered_consider {
            visitor.inside_verus_macro_or_verify_or_consider -= 1;
        }
    }
}

impl<'f> Visitor<'f> {
    fn item_attr_enter(&mut self, attrs: &Vec<Attribute>) -> ItemAttrExit {
        for attr in attrs.iter() {
            if let Meta::Path(path) = &attr.meta {
                let mut path_iter = path.segments.iter();
                match (path_iter.next(), path_iter.next(), path_iter.next()) {
                    (Some(first), Some(second), None)
                        if first.ident == "verus" && second.ident == "trusted" =>
                    {
                        self.trusted += 1;
                        return ItemAttrExit {
                            entered_trusted: true,
                            entered_ignore: false,
                            entered_verify: false,
                            entered_external: false,
                            entered_consider: false,
                        };
                    }
                    (Some(first), Some(second), Some(third))
                        if first.ident == "verus"
                            && second.ident == "line_count"
                            && third.ident == "ignore" =>
                    {
                        self.inside_line_count_ignore_or_external += 1;
                        return ItemAttrExit {
                            entered_trusted: false,
                            entered_ignore: true,
                            entered_verify: false,
                            entered_external: false,
                            entered_consider: false,
                        };
                    }
                    (Some(first), Some(second), Some(third))
                        if first.ident == "verus"
                            && second.ident == "line_count"
                            && third.ident == "consider" =>
                    {
                        self.inside_verus_macro_or_verify_or_consider += 1;
                        return ItemAttrExit {
                            entered_trusted: false,
                            entered_ignore: false,
                            entered_verify: false,
                            entered_external: false,
                            entered_consider: true,
                        };
                    }
                    (Some(first), Some(second), None)
                        if first.ident == "verifier" && second.ident == "verify" =>
                    {
                        self.inside_verus_macro_or_verify_or_consider += 1;
                        return ItemAttrExit {
                            entered_trusted: false,
                            entered_ignore: false,
                            entered_verify: true,
                            entered_external: false,
                            entered_consider: false,
                        };
                    }
                    (Some(first), Some(second), None)
                        if first.ident == "verifier" && second.ident == "external" =>
                    {
                        self.inside_line_count_ignore_or_external += 1;
                        return ItemAttrExit {
                            entered_trusted: false,
                            entered_ignore: false,
                            entered_verify: false,
                            entered_external: true,
                            entered_consider: false,
                        };
                    }
                    _ => {}
                }
            }

            if attr.path().segments.first().map(|x| x.ident == "doc").unwrap_or(false) {
            } else {
                self.mark(
                    &attr,
                    self.mode_or_trusted(CodeKind::Directives),
                    LineContent::Directive,
                );
            }
        }
        ItemAttrExit {
            entered_trusted: false,
            entered_ignore: false,
            entered_verify: false,
            entered_external: false,
            entered_consider: false,
        }
    }

    fn fn_code_kind(&self, kind: CodeKind) -> CodeKind {
        if self.in_state_machine_macro > 0 {
            kind.join_prefer_left(CodeKind::Spec)
        } else {
            kind
        }
    }

    fn mode_or_trusted(&self, kind: CodeKind) -> CodeKind {
        if self.trusted > 0 {
            CodeKind::Trusted
        } else {
            kind
        }
    }

    fn handle_signature(
        &mut self,
        content_code_kind: CodeKind,
        code_kind: CodeKind,
        sig: &Signature,
    ) {
        self.mark(&sig, code_kind, LineContent::Signature(content_code_kind));
        if code_kind != CodeKind::Spec {
            if let Some(requires) = &sig.spec.requires {
                self.mark(
                    requires,
                    self.mode_or_trusted(CodeKind::Spec),
                    LineContent::FunctionSpec,
                );
            }
            if let Some(ensures) = &sig.spec.ensures {
                self.mark(ensures, self.mode_or_trusted(CodeKind::Spec), LineContent::FunctionSpec);
            }
            if let Some(decreases) = &sig.spec.decreases {
                self.mark(
                    decreases,
                    self.mode_or_trusted(CodeKind::Spec),
                    LineContent::FunctionSpec,
                );
            }
        }
        for p in &sig.inputs {
            match &p.kind {
                syn_verus::FnArgKind::Receiver(_) => (),
                syn_verus::FnArgKind::Typed(pt) => {
                    if let syn_verus::Type::Path(path) = &*pt.ty {
                        if let Some(wrapper_code_kind) = (path.path.segments.len() == 1)
                            .then(|| path.path.segments[0].ident.to_string())
                            .and_then(|c| match c.as_str() {
                                "Ghost" => {
                                    if self.in_body == Some(CodeKind::Spec) {
                                        Some(self.mode_or_trusted(CodeKind::Spec))
                                    } else {
                                        Some(self.mode_or_trusted(CodeKind::Proof))
                                    }
                                }
                                "Tracked" => Some(self.mode_or_trusted(CodeKind::Proof)),
                                _ => None,
                            })
                        {
                            self.mark_additional_kind(&pt, wrapper_code_kind);
                        }
                    }
                }
            }
        }
    }
}

fn cut_string(s: String, len: usize) -> String {
    s.chars().take(len).collect()
}

fn hash_map_to_fit_string<V: std::fmt::Debug>(h: &[V], len: usize) -> String {
    if h.len() != 0 {
        let each_len = (len / h.len()) - 1;
        h.iter().map(|x| cut_string(format!("{:?}", x), each_len)).collect::<Vec<_>>().join(" ")
    } else {
        "".into()
    }
}

// parse the .d file and returns a vector of files names required to generate the crate
fn get_dependencies(
    dep_file_path: &std::path::Path,
) -> Result<(std::path::PathBuf, Vec<std::path::PathBuf>), String> {
    use std::path::{Path, PathBuf};
use std::hash::{Hash, Hasher};
use std::collections::hash_map::DefaultHasher;

    let file = std::fs::File::open(dep_file_path)
        .map_err(|x| format!("{}, dependency file name: {:?}", x, dep_file_path))?;
    let mut reader = std::io::BufReader::new(file);
    let mut dependencies = String::new();
    std::io::BufRead::read_line(&mut reader, &mut dependencies).map_err(|x| {
        format!("Could not read the first line of the dependency file with message: {}", x)
    })?;
    let dep_file_folder = dep_file_path
        .parent()
        .ok_or(format!("invalid dependencies file path {}", dep_file_path.display()))?;
    let result: Vec<_> = dependencies
        .split_whitespace()
        .skip(1)
        .map(|x| dep_file_folder.join(Path::new(x)))
        .collect();
    assert!(result.len() > 0);

    if result.len() == 1 {
        return Ok((PathBuf::new(), vec![result[0].clone()]));
    }

    let mut path_iters: Vec<_> = result.iter().map(|x| x.iter()).collect();
    let mut chomp_components = 0;
    loop {
        let common = path_iters
            .iter_mut()
            .map(|x| x.next())
            .reduce(|acc, x| acc.and_then(|a| if Some(a) == x { Some(a) } else { None }))
            .flatten();
        if common.is_some() {
            chomp_components += 1;
        } else {
            break;
        }
    }
    let result_chomped: Vec<PathBuf> =
        result.iter().map(|p| PathBuf::from_iter(p.components().skip(chomp_components))).collect();
    let chomped = PathBuf::from_iter(result[0].iter().take(chomp_components));

    Ok((chomped, result_chomped))
}

#[derive(Debug, Clone)]
struct Summary {
    lines_by_kind: HashMap<Vec<CodeKind>, usize>,
}

impl std::ops::Add for Summary {
    type Output = Summary;

    fn add(self, rhs: Self) -> Self::Output {
        Summary {
            lines_by_kind: {
                let mut lines_by_kind = HashMap::new();
                for (kinds, count) in self.lines_by_kind.into_iter() {
                    *lines_by_kind.entry(kinds).or_default() += count;
                }
                for (kinds, count) in rhs.lines_by_kind.into_iter() {
                    *lines_by_kind.entry(kinds).or_default() += count;
                }
                lines_by_kind
            },
        }
    }
}

impl std::iter::Sum for Summary {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Summary { lines_by_kind: HashMap::new() }, |a, b| a + b)
    }
}

fn hash_set_to_sorted_vec<V: Clone + Ord>(h: &HashSet<V>) -> Vec<V> {
    let mut v: Vec<_> = h.iter().cloned().collect();
    v.sort();
    v
}

fn process_file(config: Rc<Config>, input_path: &std::path::Path) -> Result<FileData, String> {
    // TODO check that input_path is relative to the project root
    let file_content = std::fs::read_to_string(input_path)
        .map_err(|e| format!("cannot read {} ({})", input_path.display(), e))?;

    let file = syn_verus::parse_file(&file_content).map_err(|e| {
        dbg!(&e.span().start(), &e.span().end());
        format!("failed to parse file {}: {}", input_path.display(), e)
    })?;

    let mut file_stats = FileData {
        contents: file_content,
        lines: file_content
            .lines()
            .map(|x| LineInfo {
                kinds: HashSet::new(),
                path: input_path.to_string_lossy().into_owned(),
                line_content: HashSet::new(),
                text: x.into(),
            })
            .collect::<Vec<_>>()
            .into_boxed_slice(),
        asserts: Vec::new(),
    };
    let mut visitor = Visitor {
        file_stats: &mut file_stats,
        in_body: None,
        trusted: 0,
        in_proof_directive: 0,
        inside_verus_macro_or_verify_or_consider: 0,
        in_state_machine_macro: 0,
        inside_line_count_ignore_or_external: 0,
        config: config.clone(),
    };
    for attr in file.attrs.iter() {
        match &attr.meta {
            Meta::Path(path) => {
                let mut path_iter = path.segments.iter();
                match (path_iter.next(), path_iter.next()) {
                    (Some(first), Some(second))
                        if first.ident == "verus" && second.ident == "trusted" =>
                    {
                        visitor.trusted += 1;
                    }
                    _ => {}
                }
            }
            Meta::List(MetaList { path, delimiter: _, tokens }) => {
                let mut path_iter = path.segments.iter();
                match (path_iter.next(), path_iter.next()) {
                    (Some(first), None) if first.ident == "cfg_attr" => {
                        let nested = attr.parse_args_with(syn_verus::punctuated::Punctuated::<Meta, syn_verus::Token![,]>::parse_terminated)
                            .map_err(|e| {
                                dbg!(&e.span().start(), &e.span().end());
                                format!("failed to parse attribute: {} {:?}", e, e.span())
                            })?;
                        let mut nested_iter = nested.iter();
                        match (nested_iter.next(), nested_iter.next()) {
                            (Some(Meta::Path(first)), Some(Meta::Path(second)))
                                if first
                                    .segments
                                    .iter()
                                    .next()
                                    .as_ref()
                                    .map(|x| x.ident == "verus_keep_ghost")
                                    .unwrap_or(false) =>
                            {
                                let mut path_iter = second.segments.iter();
                                match (path_iter.next(), path_iter.next()) {
                                    (Some(first), Some(second))
                                        if first.ident == "verus" && second.ident == "trusted" =>
                                    {
                                        visitor.trusted += 1;
                                    }
                                    _ => {}
                                }
                            }
                            _ => {}
                        }
                    }
                    _ => (),
                }
            }
            _ => (),
        }
    }
    for item in file.items.into_iter() {
        match item {
            syn_verus::Item::Macro(ref m) => {
                if m.mac
                    .path
                    .segments
                    .last()
                    .map(|s| s.ident.to_string() == "verus")
                    .unwrap_or(false)
                {
                    let source_toks = &m.mac.tokens;
                    let macro_content: File =
                        syn_verus::parse2(source_toks.clone()).map_err(|e| {
                            dbg!(&e.span().start(), &e.span().end());
                            format!(
                                "failed to parse file {}: {} {:?}",
                                input_path.display(),
                                e,
                                e.span()
                            )
                        })?;
                    visitor.inside_verus_macro_or_verify_or_consider += 1;
                    visitor.visit_file(&macro_content);
                    visitor.inside_verus_macro_or_verify_or_consider -= 1;
                } else {
                    visitor.visit_item(&item);
                }
            }
            _ => {
                visitor.visit_item(&item);
            }
        }
    }
    let mut multiline_comment = 0;
    let mut kind_multiline_override = None;
    let override_re = regex::Regex::new(r"\$line_count\$(([A-Za-z,]*)(\$\{)?\$)|(\}\$)").unwrap();
    for line in file_stats.lines.iter_mut() {
        let trimmed = line.text.trim();
        let mut start_not_comment = (multiline_comment == 0).then(|| 0);
        let mut all_comment_indices = trimmed
            .match_indices("/*")
            .map(|(m, _)| (m, true))
            .chain(trimmed.match_indices("*/").map(|(m, _)| (m + 2, false)))
            .collect::<Vec<_>>();
        all_comment_indices.sort_by_key(|(m, _)| *m);
        let mut entirely_comment = true;
        let had_comment_start_end = all_comment_indices.len() > 0;
        for (i, s) in all_comment_indices {
            if !s {
                multiline_comment -= 1;
                if multiline_comment == 0 {
                    start_not_comment = Some(i);
                }
            } else {
                multiline_comment += 1;
                if multiline_comment == 1 {
                    if let Some(_) = start_not_comment
                        .take()
                        .map(|x| line.text[x..i].trim())
                        .filter(|x| x.is_empty())
                    {
                    } else {
                        entirely_comment = false;
                    }
                }
            }
        }
        let entirely_comment = entirely_comment && (multiline_comment > 0 || had_comment_start_end);
        if entirely_comment {
            line.line_content = HashSet::from([LineContent::Comment]);
            line.kinds = HashSet::from([CodeKind::Comment])
        }
        if trimmed.starts_with("//") {
            line.line_content = HashSet::from([LineContent::Comment]);
            line.kinds = HashSet::from([CodeKind::Comment])
        }
        if trimmed == "" {
            if !line.kinds.is_empty() {
                line.kinds = HashSet::from([CodeKind::Layout])
            }
        }
        if config.delimiters_are_layout
            && trimmed
                .chars()
                .all(|c| c == '(' || c == ')' || c == '{' || c == '}' || c == '[' || c == ']')
        {
            if !line.kinds.is_empty() {
                line.kinds = HashSet::from([CodeKind::Layout])
            }
        }
        if let Some(captures) = override_re.captures(trimmed) {
            if captures.get(1).is_some() {
                let kinds_str = captures.get(2).unwrap().as_str();
                let kinds = if kinds_str != "" {
                    kinds_str
                        .split(',')
                        .map(|x| match x {
                            "Trusted" => CodeKind::Trusted,
                            "Spec" => CodeKind::Spec,
                            "Proof" => CodeKind::Proof,
                            "Exec" => CodeKind::Exec,
                            "Comment" => CodeKind::Comment,
                            "Layout" => CodeKind::Layout,
                            "Directives" => CodeKind::Directives,
                            "Definitions" => CodeKind::Definitions,
                            _ => panic!("unknown code kind {}", x),
                        })
                        .collect::<HashSet<_>>()
                } else {
                    HashSet::new()
                };
                if captures.get(3).is_some() {
                    kind_multiline_override = Some(kinds);
                } else {
                    line.kinds = kinds.clone();
                }
            }
            if captures.get(4).is_some() {
                kind_multiline_override = None;
            }
        }
        if let Some(kinds) = &kind_multiline_override {
            if line.kinds != HashSet::from([CodeKind::Comment])
                && line.kinds != HashSet::from([CodeKind::Layout])
                && line.kinds != HashSet::from([])
            {
                line.kinds = kinds.clone();
            }
        }
    }
    Ok(file_stats)
}

fn warn(msg: &str) {
    eprintln!("warning: {}", msg);
}

fn run(config: Config, deps_path: &std::path::Path) -> Result<(), String> {
    let config = Rc::new(config);
    let (root_path, files) = get_dependencies(deps_path)?;
    
    if config.permutations_dir.is_dir() {
        panic!("permutations directory already exists");
    }

    let file_stats = files
        .iter()
        .map(|f| process_file(config.clone(), &root_path.join(f)).map(|fs| (f, fs)))
        .collect::<Result<Vec<_>, String>>()?;

    if config.print_all {
        eprintln!("{:18} | {:30} | {}", "Category", "Detailed contents", "");
        eprintln!();
        for (file, file_stats) in file_stats.iter() {
            eprintln!("# {}", file.display());
            for l in file_stats.lines.iter() {
                eprintln!(
                    "{:18} | {:30} | {}",
                    hash_map_to_fit_string(&hash_set_to_sorted_vec(&l.kinds)[..], 30),
                    hash_map_to_fit_string(&hash_set_to_sorted_vec(&l.line_content)[..], 30),
                    l.text
                );
            }
            eprintln!();
        }
    }

    let num_asserts = file_stats.iter().map(|(_, fs)| fs.asserts.len()).sum::<usize>();
    
    // comment out each assert and run verus
    // if it succeeded, keep it commented out, if not, revert
    let pb = ProgressBar::new(num_asserts as u64);
    pb.set_style(
        ProgressStyle::default_bar()
            .template(
                "{spinner:.green} [{elapsed_precise}] [{wide_bar:.cyan/blue}] {pos}/{len} ({eta})",
            )
            .unwrap()
            .progress_chars("#>-"),
    );

    let mut commented_asserts = 0;

    // run verus for the first time
    if let Err(e) = run_verus(&root_path, 8) {
        return Err(format!("verus failed to verify before minimization: {}", e));
    }
    
    let num_threads: usize = std::thread::available_parallelism().expect("we need to know how many threads are available") - 1;
    
    let mut queue = std::collections::VecDeque::from_iter(file_stats.iter().enumerate());
    let mut running: Vec<JoinHandle<()>> = Vec<JoinHandle<()>>::new();
    
    while !queue.is_empty() {
        if running.len() < num_threads {
            let next = queue.pop_front().expect("queue was not empty");
            running.push(std::thread::spawn(|| {
                std::fs::create_dir(config.permutations_dir.join(i)).expect("create directory");
                for (path, _) in file_stats.iter() {
                    let file_path = config.permutations_dir.join(i).join(path);
                    std::fs::write(&file_path, file_stats.contents.clone()).expect("write file");
                }
                
                for lines in file_stats.asserts.iter() {
                    pb.inc(1);
                    println!("commenting out line {:?} in {:?}", lines, file);
                    let _ = comment_lines_out(&root_path.join(config.permutations_dir.join(i).join(file)), &lines.to_owned().into());
                    commented_asserts += 1;
                    if run_verus(&config.permutations_dir.join(i), 1).is_err() {
                        println!("verus failed, reverting");
                        commented_asserts -= 1;
                        let _ = uncomment_lines(&root_path.join(file), &lines.to_owned().into());
                    }
                }
                std::fs::::remove_dir_all(config.permutations_dir.join(i)).expect("remove directory");
            }));
        } else {
            sleep(duration::from_millis(100));
        }
        running.retain(|x| !x.is_finished());
    }
    
    for (i, (file, file_stats)) in  {
        // TODO maybe defensively check file path is relative (lib.d should have been generated at the root of the project)
        
    }
    pb.finish_with_message("Done!");

    Ok(())
}

fn comment_lines_out(file_path: &std::path::Path, lines: &Vec<usize>) -> Result<(), String> {
    let file_content = std::fs::read_to_string(file_path)
        .map_err(|e| format!("cannot read {} ({})", file_path.display(), e))?;
    let lines: HashSet<_> = lines.iter().cloned().collect();
    let new_content: String = file_content
        .lines()
        .enumerate()
        .map(|(i, l)| if lines.contains(&(i)) { format!("//{}", l) } else { l.into() })
        .collect::<Vec<_>>()
        .join("\n");
    std::fs::write(file_path, new_content)
        .map_err(|e| format!("cannot write to {} ({})", file_path.display(), e))?;
    Ok(())
}

fn uncomment_lines(file_path: &std::path::Path, lines: &Vec<usize>) -> Result<(), String> {
    let file_content = std::fs::read_to_string(file_path)
        .map_err(|e| format!("cannot read {} ({})", file_path.display(), e))?;
    let lines: HashSet<_> = lines.iter().cloned().collect();
    let mut new_content: String = file_content
        .lines()
        .enumerate()
        .map(|(i, l)| if lines.contains(&(i)) { l.strip_prefix("//").unwrap_or(l) } else { l })
        .collect::<Vec<_>>()
        .join("\n");
    new_content.push('\n');
    std::fs::write(file_path, new_content)
        .map_err(|e| format!("cannot write to {} ({})", file_path.display(), e))?;
    Ok(())
}

#[derive(Debug, Deserialize, Serialize)]
struct VerificationResults {
    #[serde(rename = "encountered-vir-error")]
    encountered_vir_error: bool,
    success: bool,
    verified: u32,
    errors: u32,
    #[serde(rename = "is-verifying-entire-crate")]
    is_verifying_entire_crate: bool,
}

#[derive(Debug, Deserialize, Serialize)]
struct VerificationTime {
    #[serde(rename = "total")]
    total: u32,
}

#[derive(Debug, Deserialize, Serialize)]
struct JsonRoot {
    #[serde(rename = "verification-results")]
    verification_results: VerificationResults,
    #[serde(rename = "times-ms")]
    times_ms: VerificationTime,
}

fn run_verus(proj_path: &std::path::Path, num_threads: usize) -> Result<(), String> {
    let file_path = proj_path.join("lib.rs");

    let verus_path = current_dir().unwrap().join("../../../target-verus/release/verus");

    // anvil command:
    // verus -L dependency=deps_hack/target/debug/deps --extern=deps_hack="deps_hack/target/debug/libdeps_hack.rlib" anvil.rs --crate-type=lib --time

    // let cmd = std::process::Command::new(verus_path)
    //     .current_dir(proj_path)
    //     .arg("-L")
    //     .arg("dependency=deps_hack/target/debug/deps")
    //     .arg("--extern=deps_hack=deps_hack/target/debug/libdeps_hack.rlib")
    //     .arg("anvil.rs")
    //     .arg("--crate-type=lib")
    //     .arg("--output-json")
    //     .arg("--time")
    //     .stdout(std::process::Stdio::piped())
    //     .output()
    //     .map_err(|e| format!("failed to run verus: {}", e))?;

    let cmd = std::process::Command::new(verus_path)
        .arg("--crate-type=dylib")
        .arg("--output-json")
        .arg("--time")
        .arg(file_path)
        .arg("--rlimit")
        .arg("20")
        .arg("--threads")
        .arg(num_threads.to_string())
        .stdout(std::process::Stdio::piped())
        .output()
        .map_err(|e| format!("failed to run verus: {}", e))?;

    let output: JsonRoot = serde_json::from_slice(&cmd.stdout)
        .map_err(|e| format!("failed to parse verus output: {}", e))?;
    if output.verification_results.success {
        println!("verus succeeded with time: {}ms", output.times_ms.total);
        Ok(())
    } else {
        Err("verus failed to verify".into())
    }
}
