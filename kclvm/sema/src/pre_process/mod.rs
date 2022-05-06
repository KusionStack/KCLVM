mod config;
mod identifier;

use indexmap::IndexMap;
use kclvm_ast::ast;

#[cfg(test)]
mod tests;

pub use config::{fix_config_expr_nest_attr, merge_program};
pub use identifier::{fix_qualified_identifier, fix_raw_identifier_prefix};

/// Pre-process AST program.
pub fn pre_process_program(program: &mut ast::Program) {
    for (pkgpath, modules) in program.pkgs.iter_mut() {
        let mut import_names = IndexMap::default();
        for module in modules.iter_mut() {
            if pkgpath != kclvm_ast::MAIN_PKG {
                import_names.clear();
            }
            fix_qualified_identifier(module, &mut import_names);
            fix_raw_identifier_prefix(module);
            fix_config_expr_nest_attr(module);
        }
    }
    merge_program(program);
}
