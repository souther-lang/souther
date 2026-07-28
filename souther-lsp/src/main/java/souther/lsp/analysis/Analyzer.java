package souther.lsp.analysis;

import souther.compiler.Compiler;
import souther.compiler.check.Resolve;
import souther.compiler.query.Compilation;
import souther.compiler.query.Names;
import souther.compiler.types.TypeName;
import souther.compiler.ast.Ast;
import souther.compiler.cst.CstError;
import souther.compiler.cst.CstLexer;
import souther.compiler.cst.CstParser;
import souther.compiler.cst.GreenToken;
import souther.compiler.cst.LineIndex;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticRenderer;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.cst.SyntaxElement;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.cst.SyntaxNode;
import souther.compiler.cst.SyntaxToken;
import souther.compiler.fmt.Formatter;
import souther.compiler.frontend.CstFrontend;
import souther.lsp.protocol.CodeAction;
import souther.lsp.protocol.CompletionItem;
import souther.lsp.protocol.DocumentSymbol;
import souther.lsp.protocol.Hover;
import souther.lsp.protocol.Location;
import souther.lsp.protocol.LspDiagnostic;
import souther.lsp.protocol.Position;
import souther.lsp.protocol.Range;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * The language-analysis core, independent of the LSP transport: pure functions from source text to
 * the data an editor asks for. Diagnostics come from the recovering CST parser (all syntax errors)
 * and, when the syntax is clean, a best-effort compile that surfaces the first semantic error
 * (the type checker does not recover yet, ADR-deferred).
 */
public final class Analyzer {

    /**
     * The workspace's compile, kept between edits. An answer is recomputed only when something it
     * read has changed, so a keystroke costs what it reached rather than a whole workspace — and a
     * source that is edited back to what it said costs nothing at all.
     *
     * <p>Null until the first workspace-wide diagnose; a single-document analysis does not build
     * one, because it is a compile of one file with nothing else in sight.
     */
    private Compilation workspaceCompile;
    /** Which module path {@link #workspaceCompile} was built for. A different one is a different
     * set of modules to resolve an import against, so the compile is started again. */
    private souther.compiler.meta.ModulePath compiledAgainst;

    /** All diagnostics for a document: every syntax error, or — when there are none — the first
     * semantic error a compile turns up. */
    public List<LspDiagnostic> diagnostics(String text) {
        LineIndex lines = new LineIndex(text);
        List<LspDiagnostic> out = new ArrayList<>();

        try {
            for (CstError e : CstParser.parse(text).errors()) {
                out.add(new LspDiagnostic(range(lines, e.offset(), e.offset() + e.width()),
                        LspDiagnostic.ERROR, null, e.legacyMessage()));
            }
        } catch (RuntimeException | StackOverflowError e) {
            return List.of(internalError(lines, e));   // the parse itself did not finish
        }
        if (!out.isEmpty()) {
            return out;   // don't chase semantics through a broken parse
        }

        try {
            Ast.Module module = CstFrontend.parse(text, "Main");
            if (!module.imports().isEmpty()) {
                return out;   // a multi-module program can't be resolved from a single file yet
            }
            if (module.exampleFileTarget() != null) {
                return out;   // an `examples for` file needs its target module, absent from one file
            }
            // A self-contained module compiles fully here, so its inline `example`s are evaluated
            // on save and a failing one (E1805) surfaces as an editor diagnostic.
            Compiler.compile(text, "Main");
        } catch (CompileException e) {
            out.addAll(fromCompile(lines, e));
        } catch (RuntimeException | StackOverflowError e) {
            out.add(internalError(lines, e));
        }
        return out;
    }

    /**
     * A marker for the compiler answering with something that is not a diagnostic. Analysis must not
     * take the session with it, but staying silent is its own failure: the author is left looking at
     * a file the editor calls clean. {@code StackOverflowError} is included deliberately — it is an
     * {@code Error}, not a {@code RuntimeException}, and a deeply nested expression raises it.
     */
    private LspDiagnostic internalError(LineIndex lines, Throwable t) {
        return new LspDiagnostic(range(lines, 0, 1), LspDiagnostic.ERROR, null,
                "the compiler could not finish reading this file ("
                        + t.getClass().getSimpleName() + ")");
    }

    /**
     * Diagnostics for every file in a workspace, resolved across imports the way the batch compiler
     * links a module set. Each file's syntax errors come from its own recovering parse; a file with a
     * syntax error stays out of the shared compile (it cannot join the graph). The remaining files are
     * compiled together, and each semantic diagnostic is published on the file of the module that owns
     * it — so an error in an imported module lands on that module's document, not on its importer.
     */
    public Map<String, List<LspDiagnostic>> diagnostics(ModuleGraph graph) {
        return diagnostics(graph, souther.compiler.meta.ModulePath.EMPTY);
    }

    /** As {@link #diagnostics(ModuleGraph)}, resolving an import that names no module in the
     * workspace against {@code path} — what the projects beside this one have already built — so
     * an import the build resolves is not reported here as unknown. */
    public Map<String, List<LspDiagnostic>> diagnostics(ModuleGraph graph,
                                                       souther.compiler.meta.ModulePath path) {
        Map<String, List<LspDiagnostic>> out = new LinkedHashMap<>();
        Map<String, String> compileSet = new LinkedHashMap<>();   // uri -> text, syntactically clean only
        Set<String> brokenModules = new HashSet<>();   // names of files held out for their syntax errors

        for (String uri : graph.uris()) {
            String text = graph.text(uri);
            LineIndex lines = new LineIndex(text);
            List<LspDiagnostic> syntax = new ArrayList<>();
            boolean readable = true;
            try {
                for (CstError e : CstParser.parse(text).errors()) {
                    syntax.add(new LspDiagnostic(range(lines, e.offset(), e.offset() + e.width()),
                            LspDiagnostic.ERROR, null, e.legacyMessage()));
                }
            } catch (RuntimeException | StackOverflowError e) {
                syntax.add(internalError(lines, e));   // the parse itself did not finish
                readable = false;
            }
            out.put(uri, syntax);
            if (readable && syntax.isEmpty()) {
                compileSet.put(uri, text);   // a syntactically broken file cannot join the compile
            } else {
                String name = Compiler.moduleNameFromHeader(text);
                if (name != null) {
                    brokenModules.add(name);   // present but unparseable; importers skip, not cascade
                }
            }
        }

        Map<String, List<Diagnostic>> byUri;
        try {
            byUri = compileOf(path, compileSet, brokenModules).diagnostics();
        } catch (RuntimeException | StackOverflowError e) {
            // Which file broke the walk is not known here, so every file that entered the compile is
            // marked. Silence would leave the whole workspace looking clean.
            for (String uri : compileSet.keySet()) {
                out.get(uri).add(internalError(new LineIndex(graph.text(uri)), e));
            }
            return out;
        }
        for (Map.Entry<String, List<Diagnostic>> e : byUri.entrySet()) {
            List<LspDiagnostic> list = out.get(e.getKey());
            if (list == null) {
                continue;
            }
            LineIndex lines = new LineIndex(graph.text(e.getKey()));
            for (Diagnostic d : e.getValue()) {
                list.add(fromDiagnostic(lines, d));
            }
        }
        return out;
    }

    /** The workspace's compile, brought up to date with what the documents now say. */
    private Compilation compileOf(souther.compiler.meta.ModulePath path,
                                  Map<String, String> sources, Set<String> broken) {
        if (workspaceCompile == null || !path.equals(compiledAgainst)) {
            workspaceCompile = Compilation.ofDocuments(sources, broken, path);
            compiledAgainst = path;
        } else {
            workspaceCompile.update(sources, broken);
        }
        return workspaceCompile;
    }

    /**
     * The same compile, for a request that arrives with a graph and no path — navigation. A file
     * that will not parse is left out of it, as it is for diagnostics: it cannot join a module set.
     * The path is whichever the last diagnose used, which is current, because a diagnose runs on
     * every change.
     */
    private Compilation compileOf(ModuleGraph graph) {
        Map<String, String> clean = new LinkedHashMap<>();
        Set<String> broken = new HashSet<>();
        for (String uri : graph.uris()) {
            String text = graph.text(uri);
            boolean readable;
            try {
                readable = CstParser.parse(text).errors().isEmpty();
            } catch (RuntimeException | StackOverflowError e) {
                readable = false;
            }
            if (readable) {
                clean.put(uri, text);
            } else {
                String name = Compiler.moduleNameFromHeader(text);
                if (name != null) {
                    broken.add(name);
                }
            }
        }
        return compileOf(compiledAgainst == null ? souther.compiler.meta.ModulePath.EMPTY
                : compiledAgainst, clean, broken);
    }

    /** What the cursor is on, as the compiler answers it: the type a name at {@code pos} denotes,
     * or the declaration whose own name is there. Null when the compiler cannot say — a file that
     * does not compile, or a name in the value namespace, which is still matched by spelling. */
    private TypeName typeUnderCursor(Compilation compilation, String uri, ModuleGraph graph,
                                     Position pos) {
        String text = graph.text(uri);
        String module = text == null ? null : Compiler.moduleNameFromHeader(text);
        if (module == null) {
            return null;
        }
        SourcePos at = new SourcePos(pos.line() + 1, pos.character() + 1);
        return compilation.db().ask(new Names.TypeAt(module, at)).value();
    }

    /** The range of one written name, counting only its last segment: renaming a type rewrites the
     * {@code Amount} of {@code up.Amount}, never the {@code up}. */
    private Range writtenRange(Resolve.Denotation denotation) {
        int line = denotation.pos().line() - 1;
        int start = denotation.pos().column() - 1 + denotation.written().lastIndexOf('.') + 1;
        return new Range(new Position(line, start),
                new Position(line, denotation.pos().column() - 1 + denotation.written().length()));
    }

    /**
     * Quick-fix code actions overlapping {@code requested}: currently, replacing a misspelled name
     * with the compiler's did-you-mean suggestion. The suggestion lives on the structured compiler
     * diagnostic — which the published {@link LspDiagnostic} drops — so this recomputes the first
     * semantic error to recover it. The type checker reports only that first error, so at most one
     * fix is offered per compile.
     */
    public List<CodeAction> codeActions(String uri, String text, Range requested) {
        List<CodeAction> out = new ArrayList<>();
        if (!CstParser.parse(text).errors().isEmpty()) {
            return out;   // a semantic suggestion needs a clean parse
        }
        Diagnostic d = firstSemanticDiagnostic(text);
        if (d == null || d.suggestion() == null || d.region() == null) {
            return out;
        }
        Range diagRange = rangeOf(new LineIndex(text), d);
        if (overlaps(diagRange, requested)) {
            out.add(new CodeAction("Replace with '" + d.suggestion() + "'", uri, diagRange, d.suggestion()));
        }
        return out;
    }

    /** The first semantic error a self-contained compile turns up, as the structured compiler
     * {@link Diagnostic} (carrying its suggestion and region), or {@code null} when there is none —
     * mirrors the semantic path of {@link #diagnostics(String)}. */
    private Diagnostic firstSemanticDiagnostic(String text) {
        try {
            Ast.Module module = CstFrontend.parse(text, "Main");
            if (!module.imports().isEmpty() || module.exampleFileTarget() != null) {
                return null;   // a multi-module or examples file cannot be resolved from one file
            }
            Compiler.compile(text, "Main");
            return null;
        } catch (CompileException e) {
            return e.diagnostic();
        } catch (RuntimeException | StackOverflowError _) {
            return null;   // no suggestion to recover; the diagnostics pass reports the failure
        }
    }

    private static boolean overlaps(Range a, Range b) {
        return !before(a.end(), b.start()) && !before(b.end(), a.start());
    }

    private static boolean before(Position p, Position q) {
        return p.line() < q.line() || (p.line() == q.line() && p.character() < q.character());
    }

    /** The document's canonical formatting (see {@link Formatter}), or empty when it has a syntax
     * error — the formatter re-derives layout from a clean parse, so a broken document is left as-is. */
    public Optional<String> format(String text) {
        CstParser.Result parsed = CstParser.parse(text);
        if (!parsed.errors().isEmpty()) {
            return Optional.empty();
        }
        return Optional.of(Formatter.format(parsed.root()));
    }

    /**
     * Go-to-definition across the workspace: resolves the identifier under the cursor to the document
     * and name range of the top-level definition it names. A name defined in the current file resolves
     * locally; otherwise it is resolved through the file's imports to the module that exposes it, and
     * the target's own document supplies the range.
     */
    public Optional<Location> definition(String uri, Position pos, ModuleGraph graph) {
        String text = graph.text(uri);
        if (text == null) {
            return Optional.empty();
        }
        Optional<Location> answered = declarationOf(uri, pos, graph);
        if (answered.isPresent()) {
            return answered;
        }
        LineIndex lines = new LineIndex(text);
        SyntaxNode root = CstParser.parse(text).root();
        SyntaxToken ident = identAt(root, lines.offsetOf(pos.line(), pos.character()));
        if (ident == null) {
            return Optional.empty();
        }
        SyntaxNode local = declaringDef(root, ident.text());
        if (local != null) {
            SyntaxToken name = nameToken(local);
            return name == null ? Optional.empty() : Optional.of(new Location(uri, tokenRange(lines, name)));
        }
        String targetModule = importedFrom(text, ident.text());
        if (targetModule == null) {
            return Optional.empty();
        }
        String targetUri = uriOfModule(graph, targetModule);
        if (targetUri == null) {
            return Optional.empty();
        }
        String targetText = graph.text(targetUri);
        SyntaxNode def = declaringDef(CstParser.parse(targetText).root(), ident.text());
        if (def == null) {
            return Optional.empty();
        }
        SyntaxToken name = nameToken(def);
        return name == null ? Optional.empty()
                : Optional.of(new Location(targetUri, tokenRange(new LineIndex(targetText), name)));
    }

    /**
     * Find-references across the workspace: every use of the top-level symbol the cursor names, in the
     * defining module and in every module that imports it. Resolution respects namespaces — a type
     * mention and a value of the same spelling are different symbols — and scope: a use inside a
     * definition that binds the name locally (a param or a {@code let}) is that local, not the symbol,
     * and is excluded. The declaration itself is included only when {@code includeDeclaration} is set.
     */
    public List<Location> references(String uri, Position pos, ModuleGraph graph, boolean includeDeclaration) {
        String text = graph.text(uri);
        if (text == null) {
            return List.of();
        }
        List<Location> answered = usesOf(uri, pos, graph, includeDeclaration);
        if (answered != null) {
            return answered;
        }
        SyntaxNode root = CstParser.parse(text).root();
        SyntaxToken ident = identAt(root, new LineIndex(text).offsetOf(pos.line(), pos.character()));
        if (ident == null) {
            return List.of();
        }
        String name = ident.text();
        String definingModule = declaringDef(root, name) != null
                ? Compiler.moduleNameFromHeader(text) : importedFrom(text, name);
        if (definingModule == null) {
            return List.of();
        }
        String definingUri = uriOfModule(graph, definingModule);
        if (definingUri == null) {
            return List.of();
        }
        boolean isType = isTypeDef(declaringDef(CstParser.parse(graph.text(definingUri)).root(), name));

        List<Location> out = new ArrayList<>();
        for (String u : graph.uris()) {
            String t = graph.text(u);
            boolean owns = definingModule.equals(Compiler.moduleNameFromHeader(t));
            if (!owns && !definingModule.equals(importedFrom(t, name))) {
                continue;   // this file neither defines nor imports the symbol
            }
            collectReferences(CstParser.parse(t).root(), name, isType, u, new LineIndex(t),
                    includeDeclaration && owns, out);
        }
        return out;
    }

    /**
     * The edit ranges for renaming the top-level symbol under the cursor, grouped by document uri:
     * every reference to it plus its declaration. Empty when the cursor is not on a renameable
     * top-level symbol (a local param or {@code let} is out of scope, as it is for find-references).
     */
    public Map<String, List<Range>> renameEdits(String uri, Position pos, ModuleGraph graph) {
        Map<String, List<Range>> byUri = new LinkedHashMap<>();
        for (Location loc : references(uri, pos, graph, true)) {
            byUri.computeIfAbsent(loc.uri(), k -> new ArrayList<>()).add(loc.range());
        }
        if (byUri.isEmpty()) {
            return byUri;   // not a renameable top-level symbol
        }
        // references() treats a name in an `exposing`/`import` list as a binding site, not a use, and
        // skips it. Rename must still update those, or the module stops exposing (and importers stop
        // importing) the renamed symbol, breaking the build.
        //
        // Which module those belong to is the same question the references were found by, and it has
        // to be answered the same way: renaming from a qualified use renames the module the
        // reference names, and matching the spelling here would edit this module's own `exposing`
        // instead — leaving both modules uncompilable.
        TypeName target = typeUnderCursor(compileOf(graph), uri, graph, pos);
        if (target != null) {
            addExposingAndImportSites(target.name(), target.module(), graph, byUri);
            return byUri;
        }
        String text = graph.text(uri);
        SyntaxNode root = CstParser.parse(text).root();
        SyntaxToken ident = identAt(root, new LineIndex(text).offsetOf(pos.line(), pos.character()));
        if (ident != null) {
            String name = ident.text();
            String definingModule = declaringDef(root, name) != null
                    ? Compiler.moduleNameFromHeader(text) : importedFrom(text, name);
            if (definingModule != null) {
                addExposingAndImportSites(name, definingModule, graph, byUri);
            }
        }
        return byUri;
    }

    /**
     * Where the type under the cursor is declared, as the compiler answers it. Empty when it cannot
     * say: the workspace does not compile, or the cursor is on a name in the value namespace, which
     * is still matched by spelling below.
     */
    private Optional<Location> declarationOf(String uri, Position pos, ModuleGraph graph) {
        Compilation compilation = compileOf(graph);
        TypeName target = typeUnderCursor(compilation, uri, graph, pos);
        if (target == null) {
            return Optional.empty();
        }
        String targetUri = compilation.sourceIdOf(target.module());
        String targetText = targetUri == null ? null : graph.text(targetUri);
        if (targetText == null) {
            return Optional.empty();
        }
        // Which module and which name is the compiler's answer — the part a spelling match gets
        // wrong. Where in that file the name is written is the syntax tree's, which is what knows
        // about characters; a module declares a name once, so there is nothing to choose between.
        SyntaxNode def = declaringDef(CstParser.parse(targetText).root(), target.name());
        SyntaxToken name = def == null ? null : nameToken(def);
        return name == null ? Optional.empty()
                : Optional.of(new Location(targetUri,
                        tokenRange(new LineIndex(targetText), name)));
    }

    /**
     * Every place the type under the cursor is named, as the compiler answers it, or null when it
     * cannot say. A name resolves to one declaration wherever it is written, so a module that
     * declares its own type of the same spelling is not swept up, and a qualified reference to
     * another module's is.
     */
    private List<Location> usesOf(String uri, Position pos, ModuleGraph graph,
                                  boolean includeDeclaration) {
        Compilation compilation = compileOf(graph);
        TypeName target = typeUnderCursor(compilation, uri, graph, pos);
        if (target == null) {
            return null;
        }
        List<Location> out = new ArrayList<>();
        if (includeDeclaration) {
            declarationOf(uri, pos, graph).ifPresent(out::add);
        }
        for (String module : compilation.modules()) {
            String moduleUri = compilation.sourceIdOf(module);
            if (moduleUri == null || graph.text(moduleUri) == null) {
                continue;
            }
            for (Resolve.Denotation use
                    : compilation.db().ask(new Names.UsesOf(module, target)).value()) {
                out.add(new Location(moduleUri, writtenRange(use)));
            }
        }
        return out;
    }

    /** Adds the {@code exposing ( name )} occurrence in the module that defines {@code name}, and each
     * {@code import <definingModule> ( name )} occurrence in the modules that import it — the binding
     * sites find-references skips but rename must carry along. */
    private void addExposingAndImportSites(String name, String definingModule, ModuleGraph graph,
                                           Map<String, List<Range>> byUri) {
        for (String u : graph.uris()) {
            String t = graph.text(u);
            SyntaxNode root = CstParser.parse(t).root();
            LineIndex lines = new LineIndex(t);
            boolean owns = definingModule.equals(Compiler.moduleNameFromHeader(t));
            for (SyntaxNode top : root.childNodes()) {
                if (top.kind() == SyntaxKind.MODULE_HEADER && owns) {
                    top.child(SyntaxKind.EXPOSING_CLAUSE).ifPresent(clause -> {
                        for (SyntaxNode entry : clause.childNodes()) {
                            if (entry.kind() != SyntaxKind.EXPOSED_ENTRY) {
                                continue;
                            }
                            entry.child(SyntaxKind.QUALIFIED_NAME).ifPresent(qn -> {
                                SyntaxToken tok = nameToken(qn);
                                if (tok != null && tok.text().equals(name)) {
                                    byUri.computeIfAbsent(u, k -> new ArrayList<>()).add(tokenRange(lines, tok));
                                }
                            });
                        }
                    });
                } else if (top.kind() == SyntaxKind.IMPORT_DECL) {
                    SyntaxNode module = top.child(SyntaxKind.QUALIFIED_NAME).orElse(null);
                    if (module != null && definingModule.equals(dottedName(module))) {
                        top.child(SyntaxKind.NAME_LIST).ifPresent(list -> {
                            for (SyntaxElement e : list.children()) {
                                if (e instanceof SyntaxToken tok && tok.kind() == SyntaxKind.IDENT
                                        && tok.text().equals(name)) {
                                    byUri.computeIfAbsent(u, k -> new ArrayList<>()).add(tokenRange(lines, tok));
                                }
                            }
                        });
                    }
                }
            }
        }
    }

    /** The dotted spelling of a {@code QUALIFIED_NAME} node (its identifier tokens joined by {@code .}). */
    private String dottedName(SyntaxNode qualifiedName) {
        StringBuilder sb = new StringBuilder();
        for (SyntaxElement e : qualifiedName.children()) {
            if (e instanceof SyntaxToken t && t.kind() == SyntaxKind.IDENT) {
                if (sb.length() > 0) {
                    sb.append('.');
                }
                sb.append(t.text());
            }
        }
        return sb.toString();
    }

    /**
     * Completion candidates at the cursor: the language keywords, the top-level names defined in this
     * file (types, behaviors, functions), the names its imports bring in, and the params and
     * {@code let} bindings of the definition the cursor sits in. Deduplicated by label, in that order.
     * This is name completion, not context-sensitive member completion — a {@code .} field list is
     * ADR-deferred, so every visible name is offered regardless of the position's expected type.
     */
    public List<CompletionItem> completions(String text, Position pos) {
        LinkedHashMap<String, CompletionItem> byLabel = new LinkedHashMap<>();
        for (String keyword : CstLexer.keywords()) {
            byLabel.putIfAbsent(keyword, new CompletionItem(keyword, CompletionItem.KEYWORD));
        }
        SyntaxNode root = CstParser.parse(text).root();
        for (SyntaxNode def : root.childNodes()) {
            switch (def.kind()) {
                case DATA_DEF -> addName(byLabel, def, CompletionItem.CLASS);
                case BEHAVIOR_DEF -> addName(byLabel, def, CompletionItem.INTERFACE);
                case FN_DEF -> addName(byLabel, def, CompletionItem.FUNCTION);
                default -> { /* header, imports, error nodes contribute no completion name */ }
            }
        }
        try {
            for (Ast.Import imp : CstFrontend.parse(text, "Main").imports()) {
                for (String name : imp.names()) {
                    byLabel.putIfAbsent(name, new CompletionItem(name, CompletionItem.FUNCTION));
                }
            }
        } catch (RuntimeException | StackOverflowError _) {
            // a file that does not parse cleanly exposes no imports; the rest of the list still stands
        }
        SyntaxNode enclosing = enclosingDef(root, new LineIndex(text).offsetOf(pos.line(), pos.character()));
        if (enclosing != null) {
            collectLocalBindings(enclosing, byLabel);
        }
        return new ArrayList<>(byLabel.values());
    }

    private void addName(Map<String, CompletionItem> out, SyntaxNode def, int kind) {
        SyntaxToken name = nameToken(def);
        if (name != null) {
            out.putIfAbsent(name.text(), new CompletionItem(name.text(), kind));
        }
    }

    /** The top-level definition whose span contains {@code offset}, or {@code null} at the file level. */
    private SyntaxNode enclosingDef(SyntaxNode root, int offset) {
        for (SyntaxNode def : root.childNodes()) {
            if ((def.kind() == SyntaxKind.DATA_DEF || def.kind() == SyntaxKind.BEHAVIOR_DEF
                    || def.kind() == SyntaxKind.FN_DEF)
                    && offset >= def.start() && offset <= def.end()) {
                return def;
            }
        }
        return null;
    }

    /** Adds every param and {@code let} name bound anywhere inside {@code node} as a variable candidate. */
    private void collectLocalBindings(SyntaxNode node, Map<String, CompletionItem> out) {
        for (SyntaxElement e : node.children()) {
            if (e instanceof SyntaxNode child) {
                if (VALUE_BINDINGS.contains(child.kind())) {
                    SyntaxToken bound = firstIdent(child);
                    if (bound != null) {
                        out.putIfAbsent(bound.text(),
                                new CompletionItem(bound.text(), CompletionItem.VARIABLE));
                    }
                }
                collectLocalBindings(child, out);
            }
        }
    }

    /** Whether {@code name} is a legal rename target: a single identifier token, not a keyword. The
     * lexer decides, so a non-ASCII name (Souther identifiers may be Japanese) is judged correctly. */
    public boolean isValidName(String name) {
        if (name == null || name.isBlank()) {
            return false;
        }
        CstLexer.Result lexed = CstLexer.lex(name);
        if (!lexed.errors().isEmpty()) {
            return false;
        }
        GreenToken sole = null;
        for (GreenToken t : lexed.tokens()) {
            if (t.kind().isTrivia() || t.kind() == SyntaxKind.EOF) {
                continue;
            }
            if (sole != null) {
                return false;   // more than one token: not a bare identifier
            }
            sole = t;
        }
        return sole != null && sole.kind() == SyntaxKind.IDENT;
    }

    private boolean isTypeDef(SyntaxNode def) {
        return def != null && def.kind() == SyntaxKind.DATA_DEF;
    }

    /** Node kinds where an identifier names a type. */
    private static final java.util.Set<SyntaxKind> TYPE_POSITIONS = java.util.Set.of(
            SyntaxKind.TYPE_REF, SyntaxKind.TYPE_ARGS, SyntaxKind.SUM_BODY, SyntaxKind.NEWTYPE_BODY,
            SyntaxKind.CONSTRUCTS_CLAUSE, SyntaxKind.REQUIRES_CLAUSE, SyntaxKind.NEW_DATA_EXPR,
            SyntaxKind.PATTERN_CTOR);

    /** Node kinds where an identifier binds a value name (a param or a {@code let}). A pattern puts
     * each name it binds in its own node, so a tuple's second name is a binder like its first. */
    private static final java.util.Set<SyntaxKind> VALUE_BINDINGS = java.util.Set.of(
            SyntaxKind.PARAM, SyntaxKind.FN_PARAM, SyntaxKind.LAMBDA_EXPR, SyntaxKind.LET_STMT,
            SyntaxKind.PATTERN_NAME, SyntaxKind.PATTERN_FIELD);

    /** Appends every occurrence of {@code name} in {@code root} that refers to the target symbol. A
     * value use inside a top-level definition that binds {@code name} locally is shadowed and skipped. */
    private void collectReferences(SyntaxNode root, String name, boolean isType, String uri,
                                   LineIndex lines, boolean includeDeclaration, List<Location> out) {
        for (SyntaxNode def : root.childNodes()) {
            if (def.kind() == SyntaxKind.MODULE_HEADER || def.kind() == SyntaxKind.IMPORT_DECL) {
                continue;   // names in the header's exposing list or an import list are not uses
            }
            boolean shadows = !isType && defBindsName(def, name);
            collectInNode(def, name, isType, uri, lines, includeDeclaration, shadows, out);
        }
    }

    private void collectInNode(SyntaxNode node, String name, boolean isType, String uri, LineIndex lines,
                               boolean includeDeclaration, boolean shadowed, List<Location> out) {
        SyntaxKind parent = node.kind();
        for (SyntaxElement e : node.children()) {
            if (e instanceof SyntaxNode child) {
                collectInNode(child, name, isType, uri, lines, includeDeclaration, shadowed, out);
            } else {
                SyntaxToken t = (SyntaxToken) e;
                if (t.kind() != SyntaxKind.IDENT || !t.text().equals(name)) {
                    continue;
                }
                if (isDeclarationName(node, t)) {
                    if (includeDeclaration) {
                        out.add(new Location(uri, tokenRange(lines, t)));
                    }
                } else if (isType) {
                    if (TYPE_POSITIONS.contains(parent)) {
                        out.add(new Location(uri, tokenRange(lines, t)));
                    }
                } else if (!VALUE_BINDINGS.contains(parent) && !TYPE_POSITIONS.contains(parent) && !shadowed) {
                    out.add(new Location(uri, tokenRange(lines, t)));
                }
            }
        }
    }

    /** Whether {@code t} is the name token of the top-level definition {@code node}. */
    private boolean isDeclarationName(SyntaxNode node, SyntaxToken t) {
        return (node.kind() == SyntaxKind.DATA_DEF || node.kind() == SyntaxKind.BEHAVIOR_DEF
                || node.kind() == SyntaxKind.FN_DEF) && t == nameToken(node);
    }

    /** Whether a top-level definition binds {@code name} as a param or a {@code let} anywhere inside it. */
    private boolean defBindsName(SyntaxNode def, String name) {
        for (SyntaxElement e : def.children()) {
            if (e instanceof SyntaxNode child) {
                if (VALUE_BINDINGS.contains(child.kind())) {
                    // `{ qty = n }` binds `n`; the first name is the field it reads
                    SyntaxToken bound = child.kind() == SyntaxKind.PATTERN_FIELD
                            ? lastIdent(child)
                            : firstIdent(child);
                    if (bound != null && bound.text().equals(name)) {
                        return true;
                    }
                }
                if (defBindsName(child, name)) {
                    return true;
                }
            }
        }
        return false;
    }

    /** The last identifier directly under {@code node} — the bound name of a {@code f = x} field
     * pattern, where the first is the field it reads. */
    private SyntaxToken lastIdent(SyntaxNode node) {
        SyntaxToken last = null;
        for (SyntaxElement e : node.children()) {
            if (e instanceof SyntaxToken t && t.kind() == SyntaxKind.IDENT) {
                last = t;
            }
        }
        return last;
    }

    private SyntaxToken firstIdent(SyntaxNode node) {
        for (SyntaxElement e : node.children()) {
            if (e instanceof SyntaxToken t && t.kind() == SyntaxKind.IDENT) {
                return t;
            }
            if (e instanceof SyntaxNode child) {
                SyntaxToken inner = firstIdent(child);
                if (inner != null) {
                    return inner;
                }
            }
        }
        return null;
    }

    /** The module a name is imported from in {@code text}, or {@code null} if no import exposes it. */
    private String importedFrom(String text, String name) {
        try {
            for (Ast.Import imp : CstFrontend.parse(text, "Main").imports()) {
                if (imp.names().contains(name)) {
                    return imp.module();
                }
            }
        } catch (RuntimeException | StackOverflowError _) {
            // a file that does not parse cleanly resolves no imports; go-to-def simply misses
        }
        return null;
    }

    /** The document URI of the module declared with {@code moduleName}, or {@code null} if none. */
    private String uriOfModule(ModuleGraph graph, String moduleName) {
        for (String uri : graph.uris()) {
            if (moduleName.equals(Compiler.moduleNameFromHeader(graph.text(uri)))) {
                return uri;
            }
        }
        return null;
    }

    /** Go-to-definition within one document: resolves the identifier under the cursor to the name
     * range of the top-level definition it names, if any. The workspace-aware
     * {@link #definition(String, Position, ModuleGraph)} resolves across imports as well. */
    public Optional<Range> definition(String text, Position pos) {
        LineIndex lines = new LineIndex(text);
        SyntaxNode root = CstParser.parse(text).root();
        SyntaxToken ident = identAt(root, lines.offsetOf(pos.line(), pos.character()));
        if (ident == null) {
            return Optional.empty();
        }
        SyntaxNode def = declaringDef(root, ident.text());
        if (def == null) {
            return Optional.empty();
        }
        SyntaxToken name = nameToken(def);
        return name == null ? Optional.empty() : Optional.of(tokenRange(lines, name));
    }

    /** Hover: shows the signature line of the definition the identifier under the cursor names. */
    public Optional<Hover> hover(String text, Position pos) {
        LineIndex lines = new LineIndex(text);
        SyntaxNode root = CstParser.parse(text).root();
        int offset = lines.offsetOf(pos.line(), pos.character());
        SyntaxToken ident = identAt(root, offset);
        if (ident == null) {
            return Optional.empty();
        }
        String signature;
        SyntaxNode parent = ident.parent();
        if (parent != null && (parent.kind() == SyntaxKind.FIELD
                || parent.kind() == SyntaxKind.PARAM || parent.kind() == SyntaxKind.FN_PARAM)) {
            // a declaration site: show the binding's own `name: Type`, read straight from the tree
            signature = signatureLine(text, parent);
        } else {
            SyntaxNode def = declaringDef(root, ident.text());
            signature = def != null ? signatureLine(text, def) : ident.text();
        }
        String contents = "```souther\n" + signature + "\n```";
        return Optional.of(new Hover(contents, tokenRange(lines, ident)));
    }

    /** The definition's first source line, from its first real token (leading comments dropped). */
    private String signatureLine(String text, SyntaxNode def) {
        SyntaxToken first = firstMeaningfulToken(def);
        if (first == null) {
            return def.text().strip();
        }
        int start = first.start();
        int newline = text.indexOf('\n', start);
        int end = newline < 0 ? def.end() : Math.min(newline, def.end());
        return text.substring(start, end).strip();
    }

    private SyntaxNode declaringDef(SyntaxNode file, String name) {
        for (SyntaxNode def : file.childNodes()) {
            if (def.kind() == SyntaxKind.DATA_DEF || def.kind() == SyntaxKind.BEHAVIOR_DEF
                    || def.kind() == SyntaxKind.FN_DEF) {
                SyntaxToken n = nameToken(def);
                if (n != null && n.text().equals(name)) {
                    return def;
                }
            }
        }
        return null;
    }

    /** The identifier token covering {@code offset}, descending only into the node that contains it. */
    private SyntaxToken identAt(SyntaxNode node, int offset) {
        for (SyntaxElement e : node.children()) {
            if (e instanceof SyntaxNode child) {
                if (offset >= child.start() && offset < child.end()) {
                    SyntaxToken found = identAt(child, offset);
                    if (found != null) {
                        return found;
                    }
                }
            } else {
                SyntaxToken t = (SyntaxToken) e;
                if (t.kind() == SyntaxKind.IDENT && offset >= t.start() && offset < t.end()) {
                    return t;
                }
            }
        }
        return null;
    }

    private SyntaxToken firstMeaningfulToken(SyntaxNode node) {
        for (SyntaxElement e : node.children()) {
            if (e instanceof SyntaxToken t && !t.isTrivia()) {
                return t;
            }
            if (e instanceof SyntaxNode child) {
                SyntaxToken inner = firstMeaningfulToken(child);
                if (inner != null) {
                    return inner;
                }
            }
        }
        return null;
    }

    /** The semantic-token legend, in index order. Declared to the client in the server capabilities
     * and referenced by the numbers in {@link #semanticTokens}. */
    public static final List<String> TOKEN_TYPES = List.of(
            "namespace", "type", "typeParameter", "parameter", "variable", "property",
            "function", "keyword", "string", "number", "comment", "operator");

    private static final int T_NAMESPACE = 0;
    private static final int T_TYPE = 1;
    private static final int T_TYPEPARAM = 2;
    private static final int T_PARAMETER = 3;
    private static final int T_VARIABLE = 4;
    private static final int T_PROPERTY = 5;
    private static final int T_FUNCTION = 6;
    private static final int T_KEYWORD = 7;
    private static final int T_STRING = 8;
    private static final int T_NUMBER = 9;
    private static final int T_COMMENT = 10;
    private static final int T_OPERATOR = 11;

    /**
     * The document's semantic tokens as the LSP delta-encoded {@code data} array (five integers per
     * token: {@code deltaLine, deltaStartChar, length, tokenType, tokenModifiers}). Classification
     * reads the CST — an identifier's role (a type, a parameter, a call target) comes from its parent
     * node — which a regex grammar cannot see, so this is where highlighting gains precision over the
     * TextMate grammar. Multi-line tokens (a string literal spanning lines) are dropped, since a
     * semantic token may not cross a line.
     */
    public int[] semanticTokens(String text) {
        LineIndex lines = new LineIndex(text);
        SyntaxNode root = CstParser.parse(text).root();
        List<int[]> tokens = new ArrayList<>();
        collectTokens(root, lines, tokens);

        int[] data = new int[tokens.size() * 5];
        int prevLine = 0;
        int prevChar = 0;
        int i = 0;
        for (int[] t : tokens) {
            int deltaLine = t[0] - prevLine;
            int deltaChar = deltaLine == 0 ? t[1] - prevChar : t[1];
            data[i++] = deltaLine;
            data[i++] = deltaChar;
            data[i++] = t[2];
            data[i++] = t[3];
            data[i++] = 0;   // no modifiers
            prevLine = t[0];
            prevChar = t[1];
        }
        return data;
    }

    /** Pre-order walk, appending {@code {line, startChar, length, tokenType}} for each classifiable
     * token in source order. */
    private void collectTokens(SyntaxNode node, LineIndex lines, List<int[]> out) {
        collectTokens(node, lines, out, node.kind());
    }

    /**
     * {@code enclosing} is the nearest ancestor that is not a pattern. A pattern says what a value is
     * made of, not what its names are for: the same {@code (a, b)} binds parameters in a lambda's
     * head and locals in a {@code let}, so classification has to see past it.
     */
    private void collectTokens(SyntaxNode node, LineIndex lines, List<int[]> out,
                               SyntaxKind enclosing) {
        SyntaxKind outer = isPatternNode(node.kind()) ? enclosing : node.kind();
        boolean seenIdent = false;
        for (SyntaxElement e : node.children()) {
            if (e instanceof SyntaxNode child) {
                collectTokens(child, lines, out, outer);
            } else {
                SyntaxToken token = (SyntaxToken) e;
                int type = classify(token, node.kind(), outer, seenIdent);
                if (token.kind() == SyntaxKind.IDENT) {
                    seenIdent = true;
                }
                if (type < 0) {
                    continue;
                }
                int line = lines.lspLine(token.start());
                if (line != lines.lspLine(token.end())) {
                    continue;   // a semantic token may not span lines
                }
                out.add(new int[]{line, lines.lspColumn(token.start()),
                        token.end() - token.start(), type});
            }
        }
    }

    /** The token type index for a leaf, or {@code -1} to emit nothing (punctuation, whitespace). */
    private static boolean isPatternNode(SyntaxKind k) {
        return k == SyntaxKind.PATTERN_NAME || k == SyntaxKind.PATTERN_TUPLE
                || k == SyntaxKind.PATTERN_CTOR || k == SyntaxKind.PATTERN_RECORD
                || k == SyntaxKind.PATTERN_FIELD;
    }

    private int classify(SyntaxToken token, SyntaxKind parent, SyntaxKind enclosing,
                         boolean afterFirstIdent) {
        SyntaxKind k = token.kind();
        if (k == SyntaxKind.LINE_COMMENT) {
            return T_COMMENT;
        }
        if (k == SyntaxKind.STRING_LIT) {
            return T_STRING;
        }
        if (k == SyntaxKind.INT_LIT || k == SyntaxKind.DECIMAL_LIT) {
            return T_NUMBER;
        }
        if (k == SyntaxKind.TYPEVAR) {
            return T_TYPEPARAM;
        }
        if (isKeyword(k)) {
            return T_KEYWORD;
        }
        if (isOperator(k)) {
            return T_OPERATOR;
        }
        if (k == SyntaxKind.IDENT) {
            return classifyIdent(parent, enclosing, afterFirstIdent);
        }
        return -1;   // braces, parens, commas, colons, dots
    }

    private int classifyIdent(SyntaxKind parent, SyntaxKind enclosing, boolean afterFirstIdent) {
        // a name a pattern binds is a parameter where the pattern is one, and a local otherwise
        if (parent == SyntaxKind.PATTERN_NAME) {
            return enclosing == SyntaxKind.LAMBDA_EXPR || enclosing == SyntaxKind.FN_PARAM
                    || enclosing == SyntaxKind.PARAM ? T_PARAMETER : T_VARIABLE;
        }
        // `{ a }` and `{ a = n }`: the first name is the field read, the second the name it binds
        if (parent == SyntaxKind.PATTERN_FIELD) {
            return afterFirstIdent ? T_VARIABLE : T_PROPERTY;
        }
        return switch (parent) {
            case TYPE_REF, TYPE_ARGS, SUM_BODY, NEWTYPE_BODY, CONSTRUCTS_CLAUSE, REQUIRES_CLAUSE,
                 DATA_DEF, NEW_DATA_EXPR, PATTERN_CTOR -> T_TYPE;
            case BEHAVIOR_DEF, FN_DEF, STAGE, CALL_EXPR -> T_FUNCTION;
            case PARAM, FN_PARAM, LAMBDA_EXPR -> T_PARAMETER;
            case FIELD, FIELD_INIT, FIELD_ACCESS, FIELD_GETTER -> T_PROPERTY;
            case MODULE_HEADER, QUALIFIED_NAME, IMPORT_DECL -> T_NAMESPACE;
            default -> T_VARIABLE;
        };
    }

    private static boolean isKeyword(SyntaxKind k) {
        return switch (k) {
            case MODULE_KW, IMPORT_KW, EXPOSING_KW, DATA_KW, INVARIANT_KW, AS_KW, LET_KW, REQUIRE_KW,
                 ELSE_KW, TRUE_KW, FALSE_KW, IF_KW, THEN_KW, BEHAVIOR_KW, REQUIRES_KW, CONSTRUCTS_KW,
                 MATCH_KW, WITH_KW -> true;
            default -> false;
        };
    }

    private static boolean isOperator(SyntaxKind k) {
        return switch (k) {
            case EQ, NE, LT, LE, GT, GE, AND, OR, PLUS, MINUS, STAR, SLASH, PLUSPLUS, ARROW, LARROW,
                 PIPEFWD, VPIPE, PIPE -> true;
            default -> false;
        };
    }

    /** The document outline: one symbol per top-level definition, a data type's fields as children. */
    public List<DocumentSymbol> documentSymbols(String text) {
        LineIndex lines = new LineIndex(text);
        SyntaxNode file = CstParser.parse(text).root();
        List<DocumentSymbol> out = new ArrayList<>();
        for (SyntaxNode def : file.childNodes()) {
            switch (def.kind()) {
                case DATA_DEF -> out.add(dataSymbol(lines, def));
                case BEHAVIOR_DEF -> symbol(lines, def, DocumentSymbol.INTERFACE).ifPresent(out::add);
                case FN_DEF -> symbol(lines, def, DocumentSymbol.FUNCTION).ifPresent(out::add);
                default -> { /* module header, imports, error nodes */ }
            }
        }
        return out;
    }

    private DocumentSymbol dataSymbol(LineIndex lines, SyntaxNode def) {
        SyntaxToken name = nameToken(def);
        List<DocumentSymbol> fields = new ArrayList<>();
        def.child(SyntaxKind.PRODUCT_BODY).ifPresent(body -> {
            for (SyntaxNode member : body.childNodes()) {
                if (member.kind() == SyntaxKind.FIELD) {
                    SyntaxToken fieldName = nameToken(member);
                    if (fieldName != null) {
                        fields.add(new DocumentSymbol(fieldName.text(), DocumentSymbol.FIELD,
                                nodeRange(lines, member), tokenRange(lines, fieldName), List.of()));
                    }
                }
            }
        });
        String label = name != null ? name.text() : "?";
        Range selection = name != null ? tokenRange(lines, name) : nodeRange(lines, def);
        return new DocumentSymbol(label, DocumentSymbol.CLASS, nodeRange(lines, def), selection, fields);
    }

    private Optional<DocumentSymbol> symbol(LineIndex lines, SyntaxNode def, int kind) {
        SyntaxToken name = nameToken(def);
        if (name == null) {
            return Optional.empty();
        }
        return Optional.of(new DocumentSymbol(name.text(), kind,
                nodeRange(lines, def), tokenRange(lines, name), List.of()));
    }

    private SyntaxToken nameToken(SyntaxNode node) {
        for (SyntaxElement e : node.children()) {
            if (e instanceof SyntaxToken t && t.kind() == SyntaxKind.IDENT) {
                return t;
            }
        }
        return null;
    }

    private Range nodeRange(LineIndex lines, SyntaxNode node) {
        return range(lines, node.start(), node.end());
    }

    private Range tokenRange(LineIndex lines, SyntaxToken token) {
        return range(lines, token.start(), token.end());
    }

    /** Every diagnostic the compile error carries, each as its own editor marker — a compile stops at
     * the first error, but a pass that finds several at once (each failing {@code example} row) is
     * squiggled row by row rather than collapsed onto the first. */
    private List<LspDiagnostic> fromCompile(LineIndex lines, CompileException e) {
        if (e.diagnostic() != null) {
            List<LspDiagnostic> out = new ArrayList<>();
            for (Diagnostic d : e.diagnostics()) {
                out.add(fromDiagnostic(lines, d));
            }
            return out;
        }
        return List.of(new LspDiagnostic(rangeOf(lines, null), LspDiagnostic.ERROR, null,
                cleanMessage(e.getMessage())));
    }

    /** An LSP diagnostic from a structured {@link Diagnostic}: its range from the region, its code
     * from the stable identity, its message rendered from the catalog (or the compatibility literal).
     * A found-vs-expected diff (a type mismatch, a failing example) is appended, since the catalog body
     * alone omits the two values — the detail the editor needs to see what went wrong. */
    private LspDiagnostic fromDiagnostic(LineIndex lines, Diagnostic d) {
        String message = DiagnosticRenderer.body(d, Locale.ENGLISH);
        if (d.diff() != null) {
            message = message + " (expected " + d.diff().expectedType()
                    + ", but was " + d.diff().actualType() + ")";
        }
        int severity = d.severity() == souther.compiler.diag.Severity.WARNING
                ? LspDiagnostic.WARNING : LspDiagnostic.ERROR;
        return new LspDiagnostic(rangeOf(lines, d), severity, d.code(), message);
    }

    private Range rangeOf(LineIndex lines, Diagnostic d) {
        if (d != null && d.region() != null) {
            Region r = d.region();
            return new Range(position(r.start()), position(r.end()));
        }
        if (d != null && d.pos() != null) {
            Position p = position(d.pos());
            return new Range(p, p);
        }
        Position origin = new Position(0, 0);
        return new Range(origin, origin);
    }

    /** A 1-based compiler {@link SourcePos} as a 0-based LSP position. */
    private Position position(SourcePos p) {
        return new Position(Math.max(0, p.line() - 1), Math.max(0, p.column() - 1));
    }

    private Range range(LineIndex lines, int startOffset, int endOffset) {
        return new Range(
                new Position(lines.lspLine(startOffset), lines.lspColumn(startOffset)),
                new Position(lines.lspLine(endOffset), lines.lspColumn(endOffset)));
    }

    /** Strips the {@code line:col} and {@code Ennnn:} prefixes the compiler's message carries, since
     * the LSP conveys the position through the range and the code through its own field. */
    private static String cleanMessage(String message) {
        String m = message.replaceFirst("^\\d+:\\d+ ", "");
        m = m.replaceFirst("^[A-Z]\\d+: ", "");
        return m;
    }
}
