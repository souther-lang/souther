package souther.lsp.analysis;

import souther.compiler.meta.ModulePath;

/**
 * The compiled modules a workspace compile reads from outside the workspace: where they are, and
 * which observation of what is there.
 *
 * <p>A compile keeps what it read of these classes for as long as it lives, and it is kept between
 * edits for as long as this value is equal. So this has to change whenever what a reader of the
 * path would read changes, and the path cannot say that: it is where the classes are, and a build
 * writes new classes to the same place. The revision is the rest of it — it moves each time the
 * workspace is told that a class output, or the set of roots it is looked for under, changed.
 *
 * <p>The revision stays out of {@link ModulePath}. That is where a module is looked for, a value the
 * compiler reasons about; when the editor last saw the files change is the language server's.
 */
public record ModulesOnThePath(ModulePath path, long revision) {

    /** Nothing on the path, as a compile of one document outside any workspace has. */
    public static final ModulesOnThePath NONE = new ModulesOnThePath(ModulePath.EMPTY, 0);
}
