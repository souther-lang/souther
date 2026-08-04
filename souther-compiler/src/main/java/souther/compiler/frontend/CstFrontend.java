package souther.compiler.frontend;

import souther.compiler.ast.Ast;
import souther.compiler.cst.CstError;
import souther.compiler.cst.CstParser;
import souther.compiler.cst.LineIndex;
import souther.compiler.cst.SyntaxNode;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The front-end facade: source → lossless CST → the compiler's {@link Ast}. This is the single
 * entry the compiler pipeline calls in place of the older {@code syntax.Parser}. Syntax errors are
 * accumulated by the CST parser rather than thrown; at this batch boundary the first one is raised
 * as a {@link CompileException}, so callers keep their fail-fast behaviour while the same CST feeds
 * the formatter and the LSP without a throw.
 */
public final class CstFrontend {

    private CstFrontend() {
    }

    /** Parses one compilation unit, naming a header-less source {@code defaultModuleName} (a
     * {@code null} default makes the {@code module} header required).
     *
     * <p>The positions it makes name no source. A caller that has a name for the text it is handing
     * over — a compile reading one of its own sources — parses through
     * {@link #parseWithSlices(String, String, String)} instead, so that what it gets back says which
     * file each position was read from. A caller here has no such name: the standard library and a
     * module read back off the module path are in no source of the compile that is reading them. */
    public static Ast.Module parse(String source, String defaultModuleName) {
        CstParser.Result result = CstParser.parse(source);
        if (!result.errors().isEmpty()) {
            throw firstError(source, null, result.errors().get(0));
        }
        return ImplicitUnits.expand(
                AstBuilder.build(result.root(), source, defaultModuleName, null));
    }

    /** As {@link #parse(String, String)} with the default module name {@code Main}. */
    public static Ast.Module parse(String source) {
        return parse(source, "Main");
    }

    /**
     * The module, and the source each of its top-level declarations was written as, filed under the
     * name that declaration declares. The CST keeps every character, so a declaration comes back
     * character for character, with the whitespace around it dropped. A comment goes with the
     * declaration it precedes: one written after a declaration on its own line, or on the same line
     * as its last token, belongs to whatever is declared next, since that is where the CST puts it.
     *
     * <p>A module publishes what it declares by carrying these into its jar; the importing project
     * parses them back, rather than reading a second description of the same syntax. Each name comes
     * from the node the same way the builder takes it, so a slice cannot end up filed under its
     * neighbour's name.
     */
    public static Parsed parseWithSlices(String source, String defaultModuleName) {
        return parseWithSlices(source, defaultModuleName, null);
    }

    /**
     * As {@link #parseWithSlices(String, String)}, with every position it makes naming
     * {@code sourceId}.
     *
     * <p>A compile that holds several sources has a name for each of them, and this is where that
     * name reaches the positions. It has to be here: a module's writings do not all stay in the file
     * they were written in — an attached {@code examples for} file's rows, tables and values join the
     * module they are for — and after that a line and a column no longer say which file they were
     * read from. Read at the one place a position is made from a text, the answer never has to be
     * worked out again.
     */
    public static Parsed parseWithSlices(String source, String defaultModuleName, String sourceId) {
        CstParser.Result result = CstParser.parse(source);
        if (!result.errors().isEmpty()) {
            throw firstError(source, sourceId, result.errors().get(0));
        }
        Ast.Module module = ImplicitUnits.expand(
                AstBuilder.build(result.root(), source, defaultModuleName, sourceId));
        String header = "module " + module.name();   // a source with no header is named for its file
        List<String> imports = new ArrayList<>();
        Map<String, String> defs = new LinkedHashMap<>();
        Map<String, String> behaviors = new LinkedHashMap<>();
        Map<String, String> fns = new LinkedHashMap<>();
        for (SyntaxNode n : result.root().childNodes()) {
            switch (n.kind()) {
                case MODULE_HEADER -> header = n.text().strip();
                case IMPORT_DECL -> imports.add(n.text().strip());
                case DATA_DEF -> defs.put(AstBuilder.firstIdentText(n), n.text().strip());
                case BEHAVIOR_DEF -> behaviors.put(AstBuilder.firstIdentText(n), n.text().strip());
                case FN_DEF -> fns.put(AstBuilder.firstIdentText(n), n.text().strip());
                default -> { /* examples and fakes are not declarations to publish */ }
            }
        }
        // a unit only named (spec 8.4) has no slice of its own; what it declares is its name, so
        // that is what an importing project reads back
        for (Ast.Def def : module.defs()) {
            defs.computeIfAbsent(def.name(), name -> "data " + name);
        }
        return new Parsed(module, new Slices(header, imports, defs, behaviors, fns));
    }

    /** A parsed module together with the source of each declaration in it. */
    public record Parsed(Ast.Module module, Slices slices) {}

    /**
     * The source a module's declarations were written as, by the name each declares. {@code header}
     * is the {@code module … exposing ( … )} line as written, which is more than the exposed names:
     * a composition's declared output is written there too, and reassembling the clause from the
     * names alone would lose it.
     */
    public record Slices(String header, List<String> imports, Map<String, String> defs,
                         Map<String, String> behaviors, Map<String, String> fns) {}

    /** The parser's first error, positioned in {@code sourceId}. The index is built here rather than
     * taken off the builder — the build never ran — so this is the one position of a source that
     * would otherwise not say which file it is in, and a syntax error would be the single kind of
     * mistake still reported against whatever file the reader guessed at. */
    private static CompileException firstError(String source, String sourceId, CstError e) {
        LineIndex lines = new LineIndex(source, sourceId);
        Diagnostic diag = Diagnostic.of(null, e.messageKey()).title("parse.title")
                .at(lines.posOf(e.offset()), e.width()).args(e.args()).build();
        return CompileException.of(diag, e.legacyMessage());
    }
}
