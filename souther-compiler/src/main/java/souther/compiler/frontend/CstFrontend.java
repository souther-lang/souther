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
     * {@code null} default makes the {@code module} header required). */
    public static Ast.Module parse(String source, String defaultModuleName) {
        CstParser.Result result = CstParser.parse(source);
        if (!result.errors().isEmpty()) {
            throw firstError(source, result.errors().get(0));
        }
        return AstBuilder.build(result.root(), source, defaultModuleName);
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
        CstParser.Result result = CstParser.parse(source);
        if (!result.errors().isEmpty()) {
            throw firstError(source, result.errors().get(0));
        }
        Ast.Module module = AstBuilder.build(result.root(), source, defaultModuleName);
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

    private static CompileException firstError(String source, CstError e) {
        LineIndex lines = new LineIndex(source);
        Diagnostic diag = Diagnostic.of(null, e.messageKey()).title("parse.title")
                .at(lines.posOf(e.offset()), e.width()).args(e.args()).build();
        return CompileException.of(diag, e.legacyMessage());
    }
}
