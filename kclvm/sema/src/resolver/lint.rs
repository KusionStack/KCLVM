//! This file is the implementation of KCLLint, which is used to perform some additional checks on KCL code.
//! The main structures of the file are Lint, LintPass, CombinedLintPass and Linter.
//! For details see the: https://github.com/KusionStack/KCLVM/issues/109
//!
//! Steps to define a new lint:
//! 1. Define a static instance of the `Lint` structure，e.g.,
//!    
//!     ```rust,no_run
//!    pub static IMPORT_Position: &Lint = &Lint {
//!         ...
//!    }
//!    ```
//!
//! 2. Define a lintpass, which is used to implement the checking process，e.g.,
//!    
//!     ```rust,no_run
//!    declare_lint_pass!(ImportPosition => [IMPORT_POSITION]);
//!    ```
//!
//!    The `ImportPosition` is the defined LintPass structure and the `IMPORT_POSITION` is the `Lint` structure
//!    defined in step 1. Here is a `LintArray`, which means that multiple lint checks can be implemented
//!    in a single lintpass.
//!
//! 3. Implement the lintpass check process, e.g.,
//!
//!    ```rust,no_run
//!    impl LintPass for ImportPosition{
//!        fn check_module(&mut self, diags: &mut IndexSet<Diagnostic>, ctx: &mut LintContext,module: &ast::Module){
//!            ...
//!        }
//!    }
//!    ```
//!
//! 4. Add the `check_*` methods in lintpass to the macro `lint_methods`, or skip it if it exists
//!
//!    ```rust,no_run
//!    macro_rules! lint_methods {
//!        ($macro:path, $args:tt) => (
//!            $macro!($args, [
//!                fn check_module(module: &ast::Module);
//!            ]);
//!        )
//!    }
//!    ```
//!
//! 5. Add the new lintpass to the macro `default_lint_passes`, noting that `:` is preceded and followed by
//! the name of the lintpass. e.g.,
//!
//!    ```rust,no_run
//!    macro_rules! default_lint_passes {
//!        ($macro:path, $args:tt) => {
//!            $macro!(
//!                $args,
//!                [
//!                    ImportPosition: ImportPosition,
//!                ]
//!            );
//!        };
//!    }
//!    ```
//!
//! 6. If new `check_*` method was added in step 4, it needs to override the walk_* method in Linter.
//! In addition to calling the self.pass.check_* function, the original walk method in MutSelfWalker
//! should be copied here so that it can continue to traverse the child nodes.
//!

use super::Resolver;
use indexmap::{IndexMap, IndexSet};
use kclvm_ast::ast;
use kclvm_ast::walker::MutSelfWalker;
use kclvm_ast::{walk_if, walk_list};
use kclvm_error::{Diagnostic, DiagnosticId, Level, Message, Position, Style, WarningKind};
use regex::Regex;

/// A summary of the methods that need to be implemented in lintpass, to be added when constructing new lint
/// lint and lintpass. When defining lintpass, the default implementation of these methods is provided: null
/// check (see macro `expand_default_lint_pass_methods`). So what need to do is to override the specific
/// `check_*` function.
#[macro_export]
macro_rules! lint_methods {
    ($macro:path, $args:tt) => (
        $macro!($args, [
            fn check_module(module: &ast::Module);
            fn check_module_post(module: &ast::Module);
            /*
            * Stmt
            */

            // fn check_stmt(stmt: ast::Node<ast::Stmt>);
            // fn check_expr_stmt(expr_stmt: ast::ExprStmt);
            // fn check_unification_stmt(unification_stmt: ast::UnificationStmt);
            // fn check_type_alias_stmt(type_alias_stmt: ast::TypeAliasStmt);
            // fn check_assign_stmt(assign_stmt: ast::AssignStmt);
            // fn check_aug_assign_stmt(aug_assign_stmt: ast::AugAssignStmt);
            // fn check_assert_stmt(assert_stmt: ast::AssertStmt);
            // fn check_if_stmt(if_stmt: ast::IfStmt);
            // fn check_import_stmt(import_stmt: ast::ImportStmt);
            // fn check_schema_stmt(schema_stmt: ast::SchemaStmt);
            // fn check_rule_stmt(rule_stmt: ast::RuleStmt);

            /*
            * Expr
            */

            // fn check_expr(expr: ast::Node<ast::Expr>);
            // fn check_quant_expr(quant_expr: ast::QuantExpr);
            fn check_schema_attr(schema_attr: &ast::SchemaAttr);
            // fn check_if_expr(if_expr: ast::IfExpr);
            // fn check_unary_expr(unary_expr: ast::UnaryExpr);
            // fn check_binary_expr(binary_expr: ast::BinaryExpr);
            // fn check_selector_expr(selector_expr: ast::SelectorExpr);
            // fn check_call_expr(call_expr: ast::CallExpr);
            // fn check_subscript(subscript: ast::Subscript);
            // fn check_paren_expr(paren_expr: ast::ParenExpr);
            // fn check_list_expr(list_expr: ast::ListExpr);
            // fn check_list_comp(list_comp: ast::ListComp);
            // fn check_list_if_item_expr(list_if_item_expr: ast::ListIfItemExpr);
            // fn check_starred_expr(starred_expr: ast::StarredExpr);
            // fn check_dict_comp(dict_comp: ast::DictComp);
            // fn check_config_if_entry_expr(config_if_entry_expr: ast::ConfigIfEntryExpr,
            // );
            // fn check_comp_clause(comp_clause: ast::CompClause);
            // fn check_schema_expr(schema_expr: ast::SchemaExpr);
            // fn check_config_expr(config_expr: ast::ConfigExpr);
            // fn check_check_expr(check_expr: ast::CheckExpr);
            // fn check_lambda_expr(lambda_expr: ast::LambdaExpr);
            // fn check_keyword(keyword: ast::Keyword);
            // fn check_arguments(arguments: ast::Arguments);
            // fn check_compare(compare: ast::Compare);
            fn check_identifier(id: &ast::Identifier);
            // fn check_number_lit(number_lit: ast::NumberLit);
            // fn check_string_lit(string_lit: ast::StringLit);
            // fn check_name_constant_lit(name_constant_lit: ast::NameConstantLit);
            // fn check_joined_string(joined_string: ast::JoinedString);
            // fn check_formatted_value(formatted_value: ast::FormattedValue);
            // fn check_comment(comment: ast::Comment);
        ]);
    )
}

/// Definition of `Lint` struct
/// Note that Lint declarations don't carry any "state" - they are merely global identifiers and descriptions of lints.
pub struct Lint {
    /// A string identifier for the lint.
    pub name: &'static str,

    /// Level for the lint.
    pub level: Level,

    /// Description of the lint or the issue it detects.
    /// e.g., "imports that are never used"
    pub desc: &'static str,

    // Error/Warning code
    pub code: &'static str,

    // Suggest methods to fix this problem
    pub note: Option<&'static str>,
}

pub type LintArray = Vec<&'static Lint>;

/// Declares a static `LintArray` and return it as an expression.
#[macro_export]
macro_rules! lint_array {
    ($( $lint:expr ),* ,) => { lint_array!( $($lint),* ) };
    ($( $lint:expr ),*) => {{
        vec![$($lint),*]
    }}
}

/// Provide a default implementation of the methods in lint_methods for each lintpass: null checking
macro_rules! expand_default_lint_pass_methods {
    ($diag:ty, $ctx:ty, [$($(#[$attr:meta])* fn $name:ident($($param:ident: $arg:ty),*);)*]) => (
        $(#[inline(always)] fn $name(&mut self, diags: &mut $diag, ctx: &mut $ctx, $($param: $arg),*) {})*
    )
}

/// Definition of `LintPass` trait
macro_rules! declare_default_lint_pass_impl {
    ([], [$($methods:tt)*]) => (
        pub trait LintPass {
            expand_default_lint_pass_methods!(IndexSet<Diagnostic>, LintContext, [$($methods)*]);
        }
    )
}

lint_methods!(declare_default_lint_pass_impl, []);

/// The macro to define the LintPass and bind a set of corresponding Lint.
///
/// Here is a `LintArray`, which means that multiple lint checks can be implemented in a single lintpass.
#[macro_export]
macro_rules! declare_lint_pass {
    ($(#[$m:meta])* $name:ident => [$($lint:expr),* $(,)?]) => {
        $(#[$m])* #[derive(Copy, Clone)] pub struct $name;
        $crate::impl_lint_pass!($name => [$($lint),*]);
    };
}

/// Implements `LintPass for $ty` with the given list of `Lint` statics.
#[macro_export]
macro_rules! impl_lint_pass {
    ($ty:ty => [$($lint:expr),* $(,)?]) => {
        impl $ty {
            pub fn get_lints() -> LintArray { $crate::lint_array!($($lint),*) }
        }
    };
}

/// Call the `check_*` method of each lintpass in CombinedLintLass.check_*.
///
/// ```rust,no_run
///     fn check_ident(&mut self, diags: &mut IndexSet<diagnostics>, ctx: &mut LintContext, id: &ast::Identifier, ){
///         self.LintPassA.check_ident(diags, ctx, id);
///         self.LintPassB.check_ident(diags, ctx, id);
///         ...
///     }
/// ```
#[macro_export]
macro_rules! expand_combined_lint_pass_method {
    ([$($passes:ident),*], $self: ident, $name: ident, $params:tt) => ({
        $($self.$passes.$name $params;)*
    })
}

/// Expand all methods defined in macro `lint_methods` in the `CombinedLintLass`.
///
/// ```rust,no_run
///     fn check_ident(&mut self, diags: &mut IndexSet<diagnostics>, ctx: &mut LintContext, id: &ast::Identifier){};
///     fn check_stmt(&mut self, diags: &mut IndexSet<diagnostics>, ctx: &mut LintContext, module: &ast::Module){};
///     ...
///  ```
#[macro_export]
macro_rules! expand_combined_lint_pass_methods {
    ($diags:ty, $ctx:ty, $passes:tt, [$($(#[$attr:meta])* fn $name:ident($($param:ident: $arg:ty),*);)*]) => (
        $(fn $name(&mut self, diags: &mut $diags, ctx: &mut $ctx, $($param: $arg),*) {
            expand_combined_lint_pass_method!($passes, self, $name, (diags, ctx, $($param),*));
        })*
    )
}

/// Expand all definitions of `CombinedLintPass`. The results are as follows：
///
/// ```rust,no_run
/// pub struct CombinedLintPass {
///     LintPassA: LintPassA;
///     LintPassB: LintPassB;
///     ...
/// }
///
/// impl CombinedLintPass{
///     pub fn new() -> Self {
///        Self {
///            LintPassA: LintPassA,
///            LintPassB: LintPassB,
///            ...
///        }
///     }
///     pub fn get_lints() -> LintArray {
///         let mut lints = Vec::new();
///         lints.extend_from_slice(&LintPassA::get_lints());
///         lints.extend_from_slice(&LintPassB::get_lints());
///         ...
///         lints
///      }
///  }
///
/// impl LintPass for CombinedLintPass {
///     fn check_ident(&mut self, diags: &mut IndexSet<diagnostics>, ctx: &mut LintContext, id: &ast::Identifier, ){
///         self.LintPassA.check_ident(diags, ctx, id);
///         self.LintPassB.check_ident(diags, ctx, id);
///         ...
///     }
///     fn check_stmt(&mut self, diags: &mut IndexSet<diagnostics>, ctx: &mut LintContext, module: &ast::Module){
///         self.LintPassA.check_stmt(diags, ctx, stmt);
///         self.LintPassB.check_stmt(diags, ctx, stmt);
///         ...
///     }
///     ...
/// }
/// ```
#[macro_export]
macro_rules! declare_combined_lint_pass {
    ([$v:vis $name:ident, [$($passes:ident: $constructor:expr,)*]], $methods:tt) => (
        #[allow(non_snake_case)]
        $v struct $name {
            $($passes: $passes,)*
        }

        impl $name {
            $v fn new() -> Self {
                Self {
                    $($passes: $constructor,)*
                }
            }

            $v fn get_lints() -> LintArray {
                let mut lints = Vec::new();
                $(lints.extend_from_slice(&$passes::get_lints());)*
                lints
            }
        }

        impl LintPass for $name {
            expand_combined_lint_pass_methods!(IndexSet<Diagnostic>, LintContext,[$($passes),*], $methods);
        }
    )
}

macro_rules! default_lint_passes {
    ($macro:path, $args:tt) => {
        $macro!(
            $args,
            [ImportPosition: ImportPosition, UnusedImport: UnusedImport,]
        );
    };
}

macro_rules! declare_combined_default_pass {
    ([$name:ident], $passes:tt) => (
        lint_methods!(declare_combined_lint_pass, [pub $name, $passes]);
    )
}

// Define `CombinedLintPass`.
default_lint_passes!(declare_combined_default_pass, [CombinedLintPass]);

/// The struct `Linter` is used to traverse the AST and call the `check_*` method defined in `CombinedLintPass`.
pub struct Linter<'l, T: LintPass> {
    pass: T,
    diags: &'l mut IndexSet<Diagnostic>,
    ctx: LintContext,
}

/// Record the information at `LintContext` when traversing the AST for analysis across AST nodes, e.g., record
/// used importstmt(used_import_names) when traversing `ast::Identifier` and `ast::SchemaAttr`, and detect unused
/// importstmt after traversing the entire module.
pub struct LintContext {
    /// What source file are we in.
    pub filename: String,
    /// Import pkgpath and name
    pub import_names: IndexMap<String, IndexMap<String, String>>,
    /// Used import nams
    pub used_import_names: IndexMap<String, IndexSet<String>>,
}

impl<'l> Linter<'l, CombinedLintPass> {
    pub fn new(diags: &'l mut IndexSet<Diagnostic>, ctx: LintContext) -> Self {
        Linter::<'l, CombinedLintPass> {
            pass: CombinedLintPass::new(),
            diags,
            ctx,
        }
    }
}

impl<'ctx> Resolver<'ctx> {
    pub fn lint_check_module(&mut self, module: &ast::Module) {
        let ctx = LintContext {
            filename: self.ctx.filename.clone(),
            import_names: self.ctx.import_names.clone(),
            used_import_names: IndexMap::new(),
        };
        let mut linter = Linter::<CombinedLintPass>::new(&mut self.handler.diagnostics, ctx);
        linter.walk_module(module)
    }
}

impl<'ctx> MutSelfWalker<'ctx> for Linter<'_, CombinedLintPass> {
    fn walk_module(&mut self, module: &'ctx ast::Module) {
        self.pass
            .check_module(&mut self.diags, &mut self.ctx, module);
        walk_list!(self, walk_stmt, module.body);
        self.pass
            .check_module_post(&mut self.diags, &mut self.ctx, module);
    }

    fn walk_identifier(&mut self, id: &'ctx ast::Identifier) {
        self.pass
            .check_identifier(&mut self.diags, &mut self.ctx, id);
    }

    fn walk_schema_attr(&mut self, schema_attr: &'ctx ast::SchemaAttr) {
        self.pass
            .check_schema_attr(&mut self.diags, &mut self.ctx, schema_attr);
        walk_list!(self, walk_call_expr, schema_attr.decorators);
        walk_if!(self, walk_expr, schema_attr.value);
    }
}

pub static IMPORT_POSITION: &Lint = &Lint {
    name: stringify!("IMPORT_POSITION"),
    level: Level::Warning,
    desc: "Check for importstmt that are not defined at the top of file",
    code: "W0413",
    note: Some("Consider moving tihs statement to the top of the file"),
};

declare_lint_pass!(ImportPosition => [IMPORT_POSITION]);

impl LintPass for ImportPosition {
    fn check_module(
        &mut self,
        diags: &mut IndexSet<Diagnostic>,
        ctx: &mut LintContext,
        module: &ast::Module,
    ) {
        let mut first_non_importstmt = std::u64::MAX;
        for stmt in &module.body {
            match &stmt.node {
                ast::Stmt::Import(_import_stmt) => {}
                _ => {
                    if stmt.line < first_non_importstmt {
                        first_non_importstmt = stmt.line
                    }
                }
            }
        }
        for stmt in &module.body {
            if let ast::Stmt::Import(_import_stmt) = &stmt.node {
                if stmt.line > first_non_importstmt {
                    diags.insert(Diagnostic {
                        level: Level::Warning,
                        messages: (&[Message {
                            pos: Position {
                                filename: module.filename.clone(),
                                line: stmt.line,
                                column: None,
                            },
                            style: Style::Line,
                            message: format!(
                                "Importstmt should be placed at the top of the module"
                            ),
                            note: Some(
                                ImportPosition::get_lints()[0]
                                    .note
                                    .unwrap()
                                    .clone()
                                    .to_string(),
                            ),
                        }])
                            .to_vec(),
                        code: Some(DiagnosticId::Warning(WarningKind::ImportPositionWarning)),
                    });
                }
            }
        }
    }
}

pub static UNUSED_IMPORT: &Lint = &Lint {
    name: stringify!("UNUSED_IMPORT"),
    level: Level::Warning,
    desc: "Check for unused importstmt",
    code: "W0411",
    note: Some("Consider removing this statement"),
};

declare_lint_pass!(UnusedImport => [UNUSED_IMPORT]);

fn record_use(name: &String, ctx: &mut LintContext) {
    let re = Regex::new(r"[|:\[\]\{\}]").unwrap();
    // # SchemaAttr.types, A|B, [A|B], {A|B:C}
    let types: Vec<&str> = re.split(name).collect();
    for t in types {
        let t = t.to_string();
        // name: a.b.c
        let name: Vec<&str> = t.split(".").collect();
        let firstname = name[0];
        if let Some(import_names) = ctx.import_names.get(&ctx.filename) {
            if import_names.contains_key(firstname) {
                ctx.used_import_names
                    .get_mut(&ctx.filename)
                    .unwrap()
                    .insert(firstname.to_string());
            }
        }
    }
}

impl LintPass for UnusedImport {
    fn check_module(
        &mut self,
        diags: &mut IndexSet<Diagnostic>,
        ctx: &mut LintContext,
        module: &ast::Module,
    ) {
        ctx.used_import_names
            .insert(ctx.filename.clone(), IndexSet::default());
    }

    fn check_module_post(
        &mut self,
        diags: &mut IndexSet<Diagnostic>,
        ctx: &mut LintContext,
        module: &ast::Module,
    ) {
        let used_import_names = ctx.used_import_names.get(&ctx.filename).unwrap();
        for stmt in &module.body {
            if let ast::Stmt::Import(import_stmt) = &stmt.node {
                if !used_import_names.contains(&import_stmt.name) {
                    diags.insert(Diagnostic {
                        level: Level::Warning,
                        messages: (&[Message {
                            pos: Position {
                                filename: module.filename.clone(),
                                line: stmt.line,
                                column: None,
                            },
                            style: Style::Line,
                            message: format!("Module '{}' imported but unused.", import_stmt.name),
                            note: Some(
                                UnusedImport::get_lints()[0]
                                    .note
                                    .unwrap()
                                    .clone()
                                    .to_string(),
                            ),
                        }])
                            .to_vec(),
                        code: Some(DiagnosticId::Warning(WarningKind::UnusedImportWarning)),
                    });
                }
            }
        }
    }

    fn check_identifier(
        &mut self,
        diags: &mut IndexSet<Diagnostic>,
        ctx: &mut LintContext,
        id: &ast::Identifier,
    ) {
        if id.names.len() >= 2 {
            let id_firstname = &id.names[0];
            record_use(&id_firstname, ctx);
        }
    }

    fn check_schema_attr(
        &mut self,
        diags: &mut IndexSet<Diagnostic>,
        ctx: &mut LintContext,
        schema_attr: &ast::SchemaAttr,
    ) {
        record_use(&schema_attr.type_str.node, ctx);
    }
}
