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
        return parseWithSlices(source, defaultModuleName).module();
    }

    /** As {@link #parse(String, String)} with the default module name {@code Main}. */
    public static Ast.Module parse(String source) {
        return parse(source, "Main");
    }

    /**
     * The module, and the source text each of its top-level declarations was written as. The CST
     * keeps every character, so a declaration comes back exactly as the author wrote it, comments
     * included.
     *
     * <p>A module publishes what it declares by carrying these into its jar; the importing project
     * parses them back, rather than reading a second description of the same syntax. Taking both
     * from one parse is what keeps a slice and its declaration the same thing.
     */
    public static Parsed parseWithSlices(String source, String defaultModuleName) {
        CstParser.Result result = CstParser.parse(source);
        if (!result.errors().isEmpty()) {
            throw firstError(source, result.errors().get(0));
        }
        Ast.Module module = AstBuilder.build(result.root(), source, defaultModuleName);
        List<String> imports = new ArrayList<>();
        List<String> defs = new ArrayList<>();
        List<String> behaviors = new ArrayList<>();
        List<String> fns = new ArrayList<>();
        for (SyntaxNode n : result.root().childNodes()) {
            switch (n.kind()) {
                case IMPORT_DECL -> imports.add(n.text().strip());
                case DATA_DEF -> defs.add(n.text().strip());
                case BEHAVIOR_DEF -> behaviors.add(n.text().strip());
                case FN_DEF -> fns.add(n.text().strip());
                default -> { /* the header, examples and fakes are not declarations to publish */ }
            }
        }
        // The lists come out of the same walk the AST was built from, so the n-th of each pair is
        // the same declaration; keying by name here means later passes may add or reorder without
        // the slices drifting away from what they describe.
        return new Parsed(module, new Slices(imports, byName(module.defs(), defs, Ast.Def::name),
                byName(module.behaviors(), behaviors, Ast.BehaviorDef::name),
                byName(module.fns(), fns, Ast.FnDef::name)));
    }

    private static <T> Map<String, String> byName(List<T> declared, List<String> texts,
                                                  java.util.function.Function<T, String> name) {
        Map<String, String> out = new LinkedHashMap<>();
        for (int i = 0; i < declared.size() && i < texts.size(); i++) {
            out.put(name.apply(declared.get(i)), texts.get(i));
        }
        return out;
    }

    /** A parsed module together with the source of each declaration in it. */
    public record Parsed(Ast.Module module, Slices slices) {}

    /** The source a module's declarations were written as, by the name each declares. */
    public record Slices(List<String> imports, Map<String, String> defs,
                         Map<String, String> behaviors, Map<String, String> fns) {}

    private static CompileException firstError(String source, CstError e) {
        LineIndex lines = new LineIndex(source);
        Diagnostic diag = Diagnostic.of(null, e.messageKey()).title("parse.title")
                .at(lines.posOf(e.offset()), e.width()).args(e.args()).build();
        return CompileException.of(diag, e.legacyMessage());
    }
}
