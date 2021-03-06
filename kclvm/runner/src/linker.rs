use crate::command::Command;

/// KclvmLinker is mainly responsible for linking the libs generated by KclvmAssembler.
pub struct KclvmLinker;
impl KclvmLinker {
    /// Link the libs generated by method "gen_bc_or_ll_file".
    pub fn link_all_libs(lib_paths: Vec<String>, lib_path: String) -> String {
        let mut cmd = Command::new();
        cmd.link_libs(&lib_paths, &lib_path)
    }
}
