#![allow(dead_code)]

use std::{
    collections::{BTreeSet, HashMap},
    fs::File,
    io::{BufRead, BufReader, BufWriter, Write},
};

use either::*;
use smt_scope::{
    display_with::{DisplayConfiguration, DisplayWithCtxt, SymbolReplacement},
    items::CdclKind,
    LogParser,
};
use z3tracer::{
    error::RawResult,
    lexer::Lexer,
    parser::{LogVisitor, Parser, ParserConfig},
    syntax::{Equality, Ident, Literal, Meaning, QiFrame, QiInstance, QiKey, Term, VarName},
    Model, ModelConfig,
};

#[derive(Debug)]
struct LightConflict {
    lits: Vec<Literal>,
    name: String,
}

struct LightModel {
    conflicts: Vec<LightConflict>,
}

impl LogVisitor for &mut LightModel {
    fn add_term(&mut self, _id: Ident, _term: Term) -> RawResult<()> {
        Ok(())
    }

    fn add_instantiation(&mut self, _key: QiKey, _frame: QiFrame) -> RawResult<()> {
        Ok(())
    }

    fn start_instance(&mut self, _key: QiKey, _instance: QiInstance) -> RawResult<()> {
        Ok(())
    }

    fn end_instance(&mut self) -> RawResult<()> {
        Ok(())
    }

    fn add_equality(&mut self, _id: Ident, _eq: Equality) -> RawResult<()> {
        Ok(())
    }

    fn attach_meaning(&mut self, _id: Ident, _meaning: Meaning) -> RawResult<()> {
        Ok(())
    }

    fn attach_var_names(&mut self, _id: Ident, _names: Vec<VarName>) -> RawResult<()> {
        Ok(())
    }

    fn attach_enode(&mut self, _id: Ident, _generation: u64) -> RawResult<()> {
        Ok(())
    }

    fn tool_version(&mut self, _s1: String, _s2: String) -> RawResult<()> {
        Ok(())
    }

    fn begin_check(&mut self, _i: u64) -> RawResult<()> {
        Ok(())
    }

    fn assign(&mut self, _lit: Literal, _s: String) -> RawResult<()> {
        Ok(())
    }

    fn conflict(&mut self, lits: Vec<Literal>, s: String) -> RawResult<()> {
        let conflict = LightConflict { lits, name: s };
        self.conflicts.push(conflict);
        Ok(())
    }

    fn push(&mut self, _i: u64) -> RawResult<()> {
        Ok(())
    }

    fn pop(&mut self, _i: u64, _j: u64) -> RawResult<()> {
        Ok(())
    }

    fn resolve_lit(&mut self, _i: u64, _lit: Literal) -> RawResult<()> {
        Ok(())
    }

    fn resolve_process(&mut self, _lit: Literal) -> RawResult<()> {
        Ok(())
    }
}

impl LightModel {
    pub fn new() -> Self {
        LightModel { conflicts: Vec::new() }
    }

    pub fn process(
        &mut self,
        path: Option<String>,
        input: impl BufRead,
        line_count: usize,
    ) -> Result<(), z3tracer::Error> {
        let config = ParserConfig {
            skip_z3_version_check: true,
            ignore_invalid_lines: true,
            show_progress_bar: false,
        };

        let lexer = Lexer::new(path, input, line_count);
        Parser::new(config, lexer, self).parse()
    }
}

pub struct TraceAnalyser {}

impl TraceAnalyser {
    pub fn from_path_old(path: &str) -> Result<Self, String> {
        dbg!(path);

        let file = BufReader::new(File::open(path).expect("Failed to open prover trace log"));
        let line_count = file.lines().map(|r| _ = r.unwrap()).count();

        let file = BufReader::new(File::open(path).expect("Failed to open prover trace log"));

        // let mut model = LightModel::new();
        // if let Err(err) = model.process(Some(path.to_owned()), file, line_count) {
        //     return Err(format!("Failed to process trace log: {}", err));
        // }

        let config = ModelConfig {
            parser_config: ParserConfig {
                ignore_invalid_lines: true,
                skip_z3_version_check: true,
                show_progress_bar: false,
            },
            with_qi_variables: true,
            with_qi_triggers: true,
            with_qi_produced_terms: true,
            with_qi_used_terms: true,
            ..ModelConfig::default()
        };

        let mut model = Model::new(config);
        if let Err(err) = model.process(Some(path.to_owned()), file, line_count) {
            return Err(format!("Failed to process trace log: {}", err));
        }

        for scope in model.scopes() {
            if let Some(conflict) = &scope.conflict {
                eprintln!(" >>> {:?}", conflict.lits);
            }
        }

        Ok(Self {})
    }

    pub fn from_path(path: &str, _cmds: &crate::ast::Commands) -> Result<Self, String> {
        let mut parser = smt_scope::Z3Parser::default();
        let file = File::open(path).expect("Failed to open prover trace log");
        let reader = BufReader::new(file);

        for (index, line) in reader.lines().enumerate() {
            let line = line.expect("Failed to read line");
            if let Err(_) = parser.process_line(&line, index) {
                continue;
            }
        }

        parser.end_of_file();

        let ctxt = smt_scope::display_with::DisplayCtxt {
            parser: &parser,
            term_display: &Default::default(),
            config: DisplayConfiguration {
                debug: false,
                display_quantifier_name: true,
                replace_symbols: SymbolReplacement::Math,
                input: None,
                enode_char_limit: None,
                ast_depth_limit: None,
            },
        };

        let output = File::create("trace-output.smt2").unwrap();
        let mut writer = BufWriter::new(output);

        eprintln!("Resolving term scopes");
        let mut scope_term_map = HashMap::<_, Vec<_>>::new();
        for (idx, term) in parser.terms().iter_enumerated() {
            scope_term_map.entry(term.frame).or_default().push(idx);
        }

        eprintln!("Writing quantifier instantiations");
        writeln!(&mut writer, ";; quantifier instantiations").unwrap();
        for inst in parser.instantiations() {
            for enode_idx in inst.yields_terms.iter() {
                writeln!(&mut writer, "{}", enode_idx.with(&ctxt)).unwrap();
            }
        }

        eprintln!("Resolving CDCL path");
        let mut path_nodes = BTreeSet::new();
        let mut curr_node = parser.cdcls().last_key_value();
        while let Some((cidx, cdcl)) = curr_node {
            path_nodes.insert(cidx);
            curr_node = match cdcl.backlink(cidx).backtrack {
                Some(idx) => Some((idx, &parser[idx])),
                _ => None,
            }
        }

        eprintln!("Writing CDCL path");
        writeln!(&mut writer, "\n\n;; CDCL path").unwrap();
        for node_idx in &path_nodes {
            let back = &parser[*node_idx].backlink(*node_idx);
            writeln!(&mut writer, " * {node_idx:?} ({back:?})").unwrap();
        }

        eprintln!("Writing CDCL tree");
        writeln!(&mut writer, "\n\n;; CDCL tree").unwrap();
        for (idx, cdcl) in parser.cdcls().iter_enumerated() {
            match path_nodes.get(&idx) {
                Some(_) => write!(&mut writer, ">>>").unwrap(),
                _ => write!(&mut writer, "###").unwrap(),
            }

            write!(&mut writer, " {idx:?} ").unwrap();
            let tail = match &cdcl.kind {
                CdclKind::Root => {
                    write!(&mut writer, "ROOT").unwrap();
                    None
                }
                CdclKind::BeginCheck(cdcl_idx) => {
                    write!(&mut writer, "BEGIN-CHECK {cdcl_idx:?}").unwrap();
                    None
                }
                CdclKind::Empty(cdcl_idx) => {
                    write!(&mut writer, "EMPTY {cdcl_idx:?}").unwrap();
                    None
                }
                CdclKind::Decision(lit_idx) => {
                    write!(&mut writer, "DECISION").unwrap();
                    Some(Left(lit_idx))
                }
                CdclKind::Conflict(conflict) => {
                    write!(&mut writer, "CONFLICT {}", conflict.backtrack).unwrap();
                    Some(Right(&conflict.cut))
                }
            };

            writeln!(&mut writer, " (frame: {:?})", cdcl.frame).unwrap();

            match tail {
                Some(Left(lit_idx)) => writeln!(&mut writer, "{}", lit_idx.with(&ctxt)).unwrap(),
                Some(Right(cut)) => {
                    for assign in cut {
                        writeln!(&mut writer, "{}", assign.with(&ctxt)).unwrap()
                    }
                }
                _ => {}
            }

            for lit_idx in cdcl.propagates.iter() {
                writeln!(&mut writer, "{}", lit_idx.with(&ctxt)).unwrap()
            }

            writeln!(&mut writer, "").unwrap();
        }

        // eprintln!("Writing terms generated on CDCL path");
        // writeln!(&mut writer, "\n\n;; terms generated on CDCL path").unwrap();
        // for cdcl_idx in &path_nodes {
        //     let cdcl = &parser[*cdcl_idx];
        //     for term_idx in &scope_term_map[&cdcl.frame] {
        //         writeln!(&mut writer, "{}", term_idx.with(&ctxt)).unwrap();
        //     }
        // }

        Ok(Self {})
    }
}
