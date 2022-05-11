use indexmap::IndexMap;
use std::collections::VecDeque;

use kclvm_ast::{ast, walker::MutSelfTypedResultWalker};

mod node;

#[cfg(test)]
mod tests;

pub const WHITESPACE: &str = " ";
pub const TAB: &str = "\t";
pub const NEWLINE: &str = "\n";

#[derive(Debug, Clone)]
pub enum Indentation {
    Indent = 0,
    Dedent = 1,
    Newline = 2,
    IndentWithNewline = 3,
    DedentWithNewline = 4,
    Fill = 5,
}

/// Printer config
#[derive(Debug)]
pub struct Config {
    pub tab_len: usize,
    pub indent_len: usize,
    pub use_spaces: bool,
    pub print_comments: bool,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            tab_len: 4,
            indent_len: 4,
            use_spaces: true,
            print_comments: true,
        }
    }
}

#[derive(Copy, Clone)]
pub struct NoHook;

impl PrinterHook for NoHook {}

pub enum ASTNode<'p> {
    Stmt(&'p ast::NodeRef<ast::Stmt>),
    Expr(&'p ast::NodeRef<ast::Expr>),
}

pub trait PrinterHook {
    fn pre(&self, _printer: &mut Printer<'_>, _node: ASTNode<'_>) {}
    fn post(&self, _printer: &mut Printer<'_>, _node: ASTNode<'_>) {}
}

pub struct Printer<'p> {
    /// Output string buffer.
    pub out: String,
    pub indent: usize,
    pub cfg: Config,
    /// Print comments,
    pub last_ast_line: u64,
    pub comments: VecDeque<ast::NodeRef<ast::Comment>>,
    pub import_spec: IndexMap<String, String>,
    pub hook: &'p (dyn PrinterHook + 'p),
}

impl Default for Printer<'_> {
    fn default() -> Self {
        Self {
            out: Default::default(),
            indent: Default::default(),
            cfg: Default::default(),
            last_ast_line: Default::default(),
            comments: Default::default(),
            import_spec: Default::default(),
            hook: &NoHook,
        }
    }
}

impl<'p> Printer<'p> {
    pub fn new(cfg: Config, hook: &'p (dyn PrinterHook + 'p)) -> Self {
        Self {
            out: "".to_string(),
            indent: 0,
            cfg,
            last_ast_line: 0,
            comments: VecDeque::default(),
            import_spec: IndexMap::default(),
            hook,
        }
    }

    // --------------------------
    // Write functions
    // --------------------------

    /// Write a string
    #[inline]
    pub fn write(&mut self, text: &str) {
        self.print_string(text);
    }

    /// Print a word
    #[inline]
    pub fn writeln(&mut self, text: &str) {
        self.print_string(text);
        self.print_string(NEWLINE);
    }

    /// Fill a indent
    pub fn fill(&mut self, text: &str) {
        if self.cfg.use_spaces {
            self.write(&format!(
                "{}{}",
                WHITESPACE.repeat(self.indent * self.cfg.indent_len),
                text
            ));
        } else {
            self.write(&format!("{}{}", TAB.repeat(self.indent), text));
        }
    }

    /// Print string
    #[inline]
    pub fn print_string(&mut self, string: &str) {
        self.out.push_str(string);
    }

    pub fn print_indentation(&mut self, indentation: Indentation) {
        match indentation {
            Indentation::Indent => self.enter(),
            Indentation::Dedent => self.leave(),
            Indentation::Newline => self.writeln(""),
            Indentation::IndentWithNewline => {
                self.enter();
                self.writeln("")
            }
            Indentation::DedentWithNewline => {
                self.leave();
                self.writeln("");
            }
            Indentation::Fill => self.fill(""),
        }
    }

    /// Print string
    #[inline]
    pub fn print_value<T: std::fmt::Display>(&mut self, value: T) {
        self.write(&format!("{}", value));
    }

    /// Print string
    #[inline]
    pub fn print_node(&mut self, node: ASTNode<'_>) {
        match node {
            ASTNode::Stmt(stmt) => self.stmt(stmt),
            ASTNode::Expr(expr) => self.expr(expr),
        }
    }

    /// Print string
    #[inline]
    pub fn print_module(&mut self, module: &ast::Module) {
        self.walk_module(module);
        loop {
            match self.comments.pop_front() {
                Some(comment) => {
                    self.writeln(&comment.node.text);
                    self.fill("");
                }
                None => break,
            }
        }
    }

    pub fn print_ast_comments<T>(&mut self, node: &ast::NodeRef<T>) {
        if !self.cfg.print_comments {
            return;
        }
        if node.line > self.last_ast_line {
            self.last_ast_line = node.line;
            let mut index = None;
            for (i, comment) in self.comments.iter().enumerate() {
                if comment.line <= node.line {
                    index = Some(i);
                } else {
                    break;
                }
            }
            if let Some(index) = index {
                let mut count = index;
                while count > 0 {
                    match self.comments.pop_front() {
                        Some(comment) => {
                            self.writeln(&comment.node.text);
                        }
                        None => break,
                    }
                    count -= 1;
                }
            }
        }
    }

    // --------------------------
    // Indent and scope functions
    // --------------------------

    /// Enter with a indent
    pub fn enter(&mut self) {
        self.indent += 1;
    }

    /// Leave with a dedent
    pub fn leave(&mut self) {
        self.indent -= 1;
    }
}
