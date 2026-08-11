package souther.lsp.analysis;

import souther.compiler.Compiler;
import souther.compiler.check.Resolve;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Names;
import souther.compiler.query.Shapes;
import souther.compiler.check.ClauseDischarge;
import souther.compiler.types.TypeName;
import souther.compiler.types.ValueName;
import souther.compiler.Reserved;
import souther.compiler.ast.Ast;
import souther.compiler.ast.WrittenName;
import souther.compiler.cst.CstError;
import souther.compiler.cst.CstLexer;
import souther.compiler.cst.CstParser;
import souther.compiler.cst.GreenToken;
import souther.compiler.cst.LineIndex;
import souther.compiler.diag.CompileException;
import souther.compiler.editor.EditorSymbols;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticRenderer;
import souther.compiler.diag.DiagnosticView;
import souther.compiler.diag.Messages;
import souther.compiler.diag.Located;
import souther.compiler.diag.Spot;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.cst.SyntaxElement;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.cst.SyntaxNode;
import souther.compiler.cst.SyntaxToken;
import souther.compiler.fmt.Formatter;
import souther.compiler.frontend.CstFrontend;
import souther.lsp.protocol.CodeAction;
import souther.lsp.protocol.CodeLens;
import souther.lsp.protocol.CompletionItem;
import souther.lsp.protocol.DocumentSymbol;
import souther.lsp.protocol.Hover;
import souther.lsp.protocol.Location;
import souther.lsp.protocol.LspDiagnostic;
import souther.lsp.protocol.Position;
import souther.lsp.protocol.Range;
import souther.lsp.protocol.TextEdit;

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
     * The language an editor's markers are written in.
     *
     * <p>The server's policy, in the server, and English rather than resolved. A language server is
     * told which files the workspace holds and nothing about which language its user reads, so there
     * is no answer here to resolve from; reaching for {@code SOUTHER_LANG} would let whichever shell
     * happened to launch the editor decide what the editor shows. Named once, because a marker's
     * text and a linked location's label are the same answer.
     */
    private static final Locale EDITOR_LANGUAGE = Locale.ENGLISH;

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

    /**
     * How much of what the rows cover this editor was told to measure. Off by default.
     *
     * <p>Off because measuring costs what it costs and an editor recompiles on every keystroke:
     * `witness` reads what the compile already ran, and `all` generates a second set of classes and
     * runs every row again on every save. Whichever is asked for, it is decided before anything is
     * asked of a compile — the answers are memoised, so a compile cannot be told halfway through.
     */
    private Adequacy.Asked measure = Adequacy.Asked.NOTHING;

    /** Whether anything is being measured, which is what decides if an offer can exist where there
     * is no diagnostic to fix. */
    public boolean measuring() {
        return measure.level().reports();
    }

    /** What this editor measures from now on. A change starts the workspace compile again, because
     * what it already answered was answered under the old setting. */
    public void measure(Adequacy.Asked asked) {
        if (!this.measure.equals(asked)) {
            this.measure = asked;
            this.workspaceCompile = null;
        }
    }

    /** All diagnostics for a document: every syntax error, or — when there are none — the first
     * semantic error a compile turns up, or the warnings a clean compile found. */
    public List<LspDiagnostic> diagnostics(String text) {
        LineIndex lines = new LineIndex(text);
        List<LspDiagnostic> out = new ArrayList<>();

        try {
            out.addAll(syntaxOf(text, lines));
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
            for (Located w : Compiler.compileWithWarnings(text, "Main").locatedWarnings()) {
                out.add(fromDiagnostic(lines, w.diagnostic()));
            }
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
    /**
     * What the recovering parser found, as the editor reads it.
     *
     * <p>One reader for both routes. The single-file route and the workspace route asked the parser
     * the same question and built the answer twice, which is how one of them came to hand over the
     * code and the other a null: a reader in an editor met a syntax error with nothing to look up,
     * and only in a workspace. What is tested is one route, and what makes that cover the other is
     * that there is only one of these.
     */
    private List<LspDiagnostic> syntaxOf(String text, LineIndex lines) {
        List<LspDiagnostic> found = new ArrayList<>();
        for (CstError<?> e : CstParser.parse(text).errors()) {
            found.add(new LspDiagnostic(range(lines, e.offset(), e.offset() + e.width()),
                    LspDiagnostic.ERROR, e.code().name(),
                    Messages.render(e.said(), EDITOR_LANGUAGE)));
        }
        return found;
    }

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
                syntax.addAll(syntaxOf(text, lines));
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

        Map<String, List<Located>> byUri;
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
        Map<String, LineIndex> indexes = new LinkedHashMap<>();
        java.util.function.Function<String, LineIndex> linesOf = uri -> {
            if (uri == null) {
                return null;
            }
            return indexes.computeIfAbsent(uri, at -> {
                String text = graph.text(at);
                return text == null ? null : new LineIndex(text);
            });
        };
        for (Map.Entry<String, List<Located>> e : byUri.entrySet()) {
            List<LspDiagnostic> list = out.get(e.getKey());
            if (list == null) {
                continue;
            }
            for (Located loc : e.getValue()) {
                // A workspace names its sources by document URI, so a source id is already the name
                // the editor opens.
                list.add(project(loc.diagnostic(), loc.primarySourceId(), e.getKey(),
                        linesOf, uri -> graph.text(uri) == null ? null : uri));
            }
        }
        return out;
    }

    /** The workspace's compile, brought up to date with what the documents now say. */
    private Compilation compileOf(souther.compiler.meta.ModulePath path,
                                  Map<String, String> sources, Set<String> broken) {
        if (workspaceCompile == null || !path.equals(compiledAgainst)) {
            workspaceCompile = Compilation.ofDocuments(sources, broken, path);
            workspaceCompile.measure(measure);
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

    /** Where the cursor is, in the terms the compiler answers about: a place in a file, not a line
     * and a column that any file might have. */
    private static SourcePos cursor(String uri, Position pos) {
        return new SourcePos(pos.line() + 1, pos.character() + 1, uri);
    }

    /** What the cursor is on, as the compiler answers it: the type a name at {@code pos} denotes,
     * or the declaration whose own name is there. Null when the compiler cannot say — a file it
     * could not read, or a name in the value namespace. */
    private TypeName typeUnderCursor(Compilation compilation, String uri, Position pos) {
        return compilation.db().ask(new Names.TypeAt(cursor(uri, pos))).value();
    }

    /**
     * The characters one written name occupies, counting only its last segment: renaming a type
     * rewrites the {@code Amount} of {@code up.Amount}, never the {@code up}.
     *
     * <p>Read off the tokens the name is written with, not measured in the name. The two differ by
     * however many combining marks the author typed, and by whatever the grammar lets stand between
     * a qualifier and the name it qualifies — a space, a comment, a line break — so an offset
     * counted in the name lands inside the qualifier at one end and short of the last character at
     * the other.
     */
    private Range writtenRange(WrittenName written) {
        Region segment = written.lastSegment();
        return new Range(editorPosition(segment.start()), editorPosition(segment.end()));
    }

    /** A compiler position as an editor counts, both of its numbers being one less. */
    private static Position editorPosition(SourcePos at) {
        return new Position(at.line() - 1, at.column() - 1);
    }

    /**
     * The document a compiler answer is about: the file its position names, or — for a position
     * that names none — the file of the module it was asked of. Null when neither is a document
     * this editor has open.
     *
     * <p>Every answer that carries a position carries the file it was written in, and what a module
     * is made of is not all written in one file: its own source and every attached {@code examples
     * for} file beside it. Filing an answer under the module's own source is right exactly while a
     * module is one file, and nothing checks that it is.
     */
    private String documentOf(SourcePos written, String moduleUri, ModuleGraph graph) {
        String uri = written != null && written.sourceId() != null ? written.sourceId() : moduleUri;
        return uri != null && graph.text(uri) != null ? uri : null;
    }

    /**
     * Where a name the compiler answered about is written, as a place an editor can open.
     *
     * <p>Which file, which characters and how many of them all come from the compiler's answer,
     * which carries the occurrence the name was read from. This used to take a name and a position
     * and look through the syntax tree for a token at or after it spelling that name, because the
     * position it was given was the start of a form rather than of a name. Two things went wrong
     * with that and both were invisible until someone wrote a decomposed name: the token was
     * compared to the name, so a declaration spelled one way was never found from a reference
     * spelled the other; and the range came out as wide as the name rather than as the spelling.
     */
    private Optional<Location> nameAt(WrittenName written, String moduleUri, ModuleGraph graph) {
        if (written == null || !written.authored()) {
            return Optional.empty();
        }
        String uri = documentOf(written.pos(), moduleUri, graph);
        return uri == null ? Optional.empty()
                : Optional.of(new Location(uri, writtenRange(written)));
    }

    /**
     * What each behavior in this document has been pinned down to, as a line above its declaration.
     *
     * <p>Where the author is working is where the numbers are worth reading. The same figures are in
     * {@code souther examples}, and a report in another window is a report nobody opens while writing
     * the behavior it is about.
     *
     * <p>Empty unless there is a workspace compile and this editor was asked to measure. One document
     * is not enough to answer from: a behavior's rows are written across its module's own source and
     * any number of attached files, and reading one file would report what another covers as
     * uncovered — which is worse than saying nothing, being wrong rather than absent.
     */
    public List<CodeLens> codeLenses(String uri, ModuleGraph graph) {
        if (!measure.level().reports()) {
            return List.of();
        }
        Compilation compilation = compileOf(graph);
        String module = moduleOf(compilation, graph, uri);
        if (module == null) {
            return List.of();
        }
        Ast.Module written = compilation.db().ask(new Shapes.Prepared(module)).value();
        if (written == null) {
            return List.of();
        }
        Adequacy.Of adequacy = compilation.adequacy(module);
        LineIndex lines = new LineIndex(graph.text(uri));
        List<CodeLens> out = new ArrayList<>();
        for (Ast.BehaviorDef behavior : written.behaviors()) {
            // A module's declarations need not all be in this document, and a line number from
            // another file read against this one's index points somewhere arbitrary.
            if (!uri.equals(documentOf(behavior.pos(), null, graph))) {
                continue;
            }
            String title = lensTitle(compilation, module, behavior.name(), adequacy);
            if (title != null) {
                out.add(new CodeLens(pointRange(lines, behavior.pos()), title));
            }
        }
        return out;
    }

    /**
     * The module this document is part of — the one it declares, or the one an attached
     * {@code examples for} file's rows are for.
     *
     * <p>The compile's answer, with the header read only for a file the compile does not have: one
     * held out for its syntax errors, which is the one case where there is nothing to ask. Reading
     * the header first is what left a cursor in an attached file belonging to no module and being
     * asked nothing.
     */
    private String moduleOf(Compilation compilation, ModuleGraph graph, String uri) {
        String known = compilation.moduleOf(uri);
        if (known != null) {
            return known;
        }
        String text = graph.text(uri);
        return text == null ? null : Compiler.moduleNameFromHeader(text);
    }

    /**
     * One behavior's line, or null where there is nothing to say about it.
     *
     * <p>A measure that could not be made is left out rather than printed as a zero. A behavior with
     * no rows has no numbers at all, and a lens reading {@code out 0/2} over one nobody has exampled
     * yet reports the model as failing something it was never asked.
     */
    private static String lensTitle(Compilation compilation, String module, String behavior,
                                    Adequacy.Of adequacy) {
        int rows = 0;
        int pending = 0;
        for (String sourceId : compilation.exampleSourcesOf(module)) {
            souther.compiler.query.Output.Examples.Of observed = compilation.db()
                    .ask(souther.compiler.query.Output.Examples.asked(
                            compilation.db(), module, sourceId)).value();
            if (observed == null) {
                continue;
            }
            for (souther.compiler.observe.RowOutcome row : observed.rows()) {
                if (row.target().equals(behavior)) {
                    rows++;
                    pending += row.disposition() == souther.compiler.observe.Disposition.PENDING
                            ? 1 : 0;
                }
            }
        }
        if (rows == 0) {
            return null;
        }
        List<String> parts = new ArrayList<>();
        parts.add(rows + (rows == 1 ? " row" : " rows"));
        if (pending > 0) {
            parts.add(pending + " pending");
        }
        Adequacy.SignatureEvidence signature =
                adequacy.signatures() == null ? null : adequacy.signatures().get(behavior);
        if (signature != null && !signature.output().declared().isEmpty()) {
            parts.add("out " + signature.output().specified().size() + "/"
                    + signature.output().declared().size());
        }
        souther.compiler.query.PartitionEvidence partition =
                adequacy.partitions() == null ? null : adequacy.partitions().get(behavior);
        if (partition != null) {
            long measured = partition.boundaries().stream()
                    .filter(b -> settled(b.coverage())).count();
            long met = partition.boundaries().stream()
                    .filter(b -> settled(b.coverage()))
                    .filter(b -> b.coverage().hit()).count();
            if (measured > 0) {
                parts.add("boundary " + met + "/" + measured);
            }
        }
        Adequacy.BranchEvidence branch =
                adequacy.branches() == null ? null : adequacy.branches().get(behavior);
        if (branch != null
                && branch.status() == souther.compiler.observe.MeasurementStatus.COMPLETE) {
            parts.add("branch " + branch.coveredObligations() + "/" + branch.obligations());
        }
        return String.join(" · ", parts);
    }

    /**
     * Whether a line came to an answer against the rows.
     *
     * <p>Hit or missed, and nothing else. A line waiting on the arms has no answer to show beside a
     * declaration, and one whose value could not be read has no answer either — a lens counting it
     * would put a number in front of an author that says a row is missing at a value nothing was able
     * to look at. The report can afford to include such a line because it writes "undecided" beside
     * the count; one number on one line has nowhere to put that word.
     */
    private static boolean settled(souther.compiler.query.BoundaryAssessment.Coverage coverage) {
        return coverage instanceof souther.compiler.query.BoundaryAssessment.Coverage.Hit
                || coverage instanceof souther.compiler.query.BoundaryAssessment.Coverage.Missed;
    }

    /** The caret at one position, as a range of no width. */
    private static Range pointRange(LineIndex lines, SourcePos pos) {
        Position at = new Position(pos.line() - 1, pos.column() - 1);
        return new Range(at, at);
    }

    /**
     * Quick-fix code actions overlapping {@code requested}: currently, replacing a misspelled name
     * with the compiler's did-you-mean suggestion. The suggestion lives on the structured compiler
     * diagnostic — which the published {@link LspDiagnostic} drops — so this recomputes the first
     * semantic error to recover it. The type checker reports only that first error, so at most one
     * fix is offered per compile.
     */
    public List<CodeAction> codeActions(String uri, String text, Range requested) {
        return codeActions(uri, text, requested, null);
    }

    /**
     * The same, with the workspace in reach: what a behavior's rows do not cover can be filled in
     * from here.
     *
     * <p>{@code graph} may be null, and is where the request arrived without one. The generated rows
     * need the whole workspace — the values a row writes are built through the module's derived
     * decoders, and its imports are part of that — so with one document there is nothing to offer.
     */
    public List<CodeAction> codeActions(String uri, String text, Range requested,
                                        ModuleGraph graph) {
        List<CodeAction> out = new ArrayList<>();
        if (!CstParser.parse(text).errors().isEmpty()) {
            return out;   // a semantic suggestion needs a clean parse
        }
        if (graph != null) {
            out.addAll(rowsToWrite(uri, text, requested, graph));
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

    /**
     * An offer to write the rows nothing covers, on the behavior the cursor is in.
     *
     * <p>The same block {@code souther examples --generate} prints, put where it goes rather than on
     * a terminal for someone to copy. It arrives commented out, with each answer left as a hole that
     * is not a term — the compiler does not know what the model owes, and a row it filled in would be
     * an assertion nobody made.
     *
     * <p>Inserted at the end of the document. Where rows belong is the author's choice — this
     * module's own source or an attached file — and moving a block is easier than finding out why one
     * landed somewhere surprising.
     */
    private List<CodeAction> rowsToWrite(String uri, String text, Range requested,
                                         ModuleGraph graph) {
        if (!measure.level().reports()) {
            return List.of();
        }
        Compilation compilation = compileOf(graph);
        String module = moduleOf(compilation, graph, uri);
        if (module == null) {
            return List.of();
        }
        Ast.Module written = compilation.db().ask(new Shapes.Prepared(module)).value();
        if (written == null) {
            return List.of();
        }
        LineIndex lines = new LineIndex(text);
        for (Ast.BehaviorDef behavior : written.behaviors()) {
            // The cursor is in this document, so a declaration written in another one is not what
            // it is on, however the lines happen to line up.
            if (!uri.equals(documentOf(behavior.pos(), null, graph))
                    || !overlaps(pointRange(lines, behavior.pos()), requested)) {
                continue;
            }
            // An id stands for itself here: a workspace compilation is keyed on the document URIs
            // this server was given, so what identifies a source is already what this server calls
            // it.
            String block = souther.compiler.report.GeneratedRows.of(compilation, module,
                    behavior.name(), true,
                    souther.compiler.diag.SourceNameResolver.identity());
            if (block.isBlank()) {
                continue;
            }
            Position end = new Position((int) text.lines().count(), 0);
            return List.of(new CodeAction(
                    "Write the rows `" + behavior.name() + "` does not cover", uri,
                    new Range(end, end), System.lineSeparator() + block));
        }
        return List.of();
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
        try {
            CstParser.Result parsed = CstParser.parse(text);
            if (!parsed.errors().isEmpty()) {
                return Optional.empty();
            }
            return Optional.of(Formatter.format(parsed.root()));
        } catch (RuntimeException | StackOverflowError _) {
            // The one entry point here that answered a document it could not walk with an error
            // reply rather than by leaving the document alone. The reason it could not is already
            // the author's to see, as a diagnostic; a failed format on top of it says nothing more.
            return Optional.empty();
        }
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
        Compilation compilation = compileOf(graph);
        if (resolves(compilation, uri)) {
            TypeName type = typeUnderCursor(compilation, uri, pos);
            if (type != null) {
                return declarationOf(compilation, type, graph);
            }
            Optional<Location> value = valueDeclarationOf(compilation, uri, pos, graph);
            if (value.isPresent()) {
                return value;
            }
        }
        LineIndex lines = new LineIndex(text);
        SyntaxNode root = CstParser.parse(text).root();
        SyntaxToken ident = identAt(meaningfulTokens(root), lines, lines.offsetOf(pos.line(), pos.character()));
        if (ident == null) {
            return Optional.empty();
        }
        SyntaxNode local = declaringDef(root, nameOf(ident));
        if (local != null) {
            SyntaxToken name = nameToken(local);
            return name == null ? Optional.empty() : Optional.of(new Location(uri, tokenRange(lines, name)));
        }
        String targetModule = importedFrom(text, nameOf(ident));
        if (targetModule == null) {
            return Optional.empty();
        }
        String targetUri = uriOfModule(compilation, graph, targetModule);
        if (targetUri == null) {
            return Optional.empty();
        }
        String targetText = graph.text(targetUri);
        SyntaxNode def = declaringDef(CstParser.parse(targetText).root(), nameOf(ident));
        if (def == null) {
            return Optional.empty();
        }
        SyntaxToken name = nameToken(def);
        return name == null ? Optional.empty()
                : Optional.of(new Location(targetUri, tokenRange(new LineIndex(targetText), name)));
    }

    /**
     * Find-references across the workspace: every use of the name the cursor is on, in the module
     * that declares it and in every module that names it. Namespaces are respected — a type mention
     * and a value of the same spelling are different names — and so is scope: a local is the binding
     * it is, so the uses of one body's {@code x} are not another's. The declaration itself is
     * included only when {@code includeDeclaration} is set, and a behavior has two of them.
     *
     * <p>A local is in reach, which it was not while this matched by spelling: a scan of top-level
     * declarations cannot see a name bound inside one. Where resolution has nothing to say — a
     * pipeline's stages and a behavior's own declaration lines are written outside any body, so it
     * never read them — the spelling is still what answers.
     */
    public List<Location> references(String uri, Position pos, ModuleGraph graph, boolean includeDeclaration) {
        String text = graph.text(uri);
        if (text == null) {
            return List.of();
        }
        Compilation compilation = compileOf(graph);
        if (resolves(compilation, uri)) {
            List<Location> uses = usesOf(compilation, uri, pos, graph, includeDeclaration);
            if (uses != null) {
                return uses;
            }
            List<Location> values = valueUsesOf(compilation, uri, pos, graph, includeDeclaration);
            if (!values.isEmpty()) {
                return values;
            }
            // Nothing found is not nothing here: the resolve pass records the value names written
            // in a body, and a composition's stages and a declaration's own name are not those, so
            // the cursor may be on a name it never saw. Matching the spelling still answers those.
        }
        SyntaxNode root = CstParser.parse(text).root();
        LineIndex lines = new LineIndex(text);
        SyntaxToken ident = identAt(meaningfulTokens(root), lines, lines.offsetOf(pos.line(), pos.character()));
        if (ident == null) {
            return List.of();
        }
        String name = nameOf(ident);
        String definingModule = declaringDef(root, name) != null
                ? moduleOf(compilation, graph, uri) : importedFrom(text, name);
        if (definingModule == null) {
            return List.of();
        }
        String definingUri = uriOfModule(compilation, graph, definingModule);
        if (definingUri == null) {
            return List.of();
        }
        boolean isType = isTypeDef(declaringDef(CstParser.parse(graph.text(definingUri)).root(), name));

        List<Location> out = new ArrayList<>();
        for (String u : graph.uris()) {
            String t = graph.text(u);
            boolean owns = definingModule.equals(moduleOf(compilation, graph, u));
            if (!owns && !definingModule.equals(importedFrom(t, name))) {
                continue;   // this file neither defines nor imports the symbol
            }
            collectReferences(CstParser.parse(t).root(), name, isType, u, new LineIndex(t),
                    includeDeclaration && owns, out);
        }
        return out;
    }

    /**
     * The edits for renaming the name under the cursor to {@code newName}, grouped by document uri:
     * every reference to it plus every line that declares it. Empty when the cursor is not on a
     * name.
     *
     * <p>A local is renameable, from its binding as much as from a use of it — the same reach
     * find-references has, for the same reason.
     *
     * <p>Each edit says what to write as well as where, because those differ. A record pattern's
     * {@code { right }} names the field it reads and binds the value under that same spelling, and
     * once the two are no longer spelled alike the field has to be named: what goes there is
     * {@code right = r}. Answering with places alone left the caller to write one name over all of
     * them, which is right everywhere else and silently produced a module reading a field that does
     * not exist here.
     */
    public Map<String, List<TextEdit>> renameEdits(String uri, Position pos, ModuleGraph graph,
                                                   String newName) {
        Map<String, List<TextEdit>> out = new LinkedHashMap<>();
        for (Map.Entry<String, List<Range>> e : renameRanges(uri, pos, graph).entrySet()) {
            List<TextEdit> edits = new ArrayList<>();
            SyntaxNode root = CstParser.parse(graph.text(e.getKey())).root();
            LineIndex lines = new LineIndex(graph.text(e.getKey()));
            List<SyntaxToken> tokens = meaningfulTokens(root);
            for (Range range : e.getValue()) {
                String field = fieldTakenAsName(tokens, lines,
                        lines.offsetOf(range.start().line(), range.start().character()));
                edits.add(new TextEdit(range,
                        field == null ? newName : field + " = " + newName));
            }
            out.put(e.getKey(), edits);
        }
        return out;
    }

    /**
     * The field a binding takes its name from, or null where the binding is written as a name of
     * its own.
     *
     * <p>Which characters are there is the syntax tree's question, being what knows about
     * characters, and this is the one place where what a rename writes is not the name it was given.
     */
    private String fieldTakenAsName(List<SyntaxToken> tokens, LineIndex lines, int offset) {
        SyntaxToken token = identAt(tokens, lines, offset);
        SyntaxNode parent = token == null ? null : token.parent();
        if (parent == null || token.start() != offset) {
            return null;
        }
        if (parent.kind() == SyntaxKind.PATTERN_FIELD) {
            // `{ f }` writes one name for both jobs; `{ f = x }` writes the binding's own
            return onlyIdent(parent) ? token.text() : null;
        }
        if (parent.kind() == SyntaxKind.MATCH_CASE) {
            // an arm's fields are the case's own tokens: `Flat { f }` against `Flat { f = x }`
            return standsAlone(parent, token) ? token.text() : null;
        }
        return null;
    }

    /** Whether {@code node} holds one identifier and no other. */
    private boolean onlyIdent(SyntaxNode node) {
        int found = 0;
        for (SyntaxElement e : node.children()) {
            if (e instanceof SyntaxToken t && t.kind() == SyntaxKind.IDENT) {
                found++;
            }
        }
        return found == 1;
    }

    /** Whether {@code token} is a field written with nothing beside it — the previous and next
     * tokens that are not trivia open or separate the list rather than assign to it. */
    private boolean standsAlone(SyntaxNode node, SyntaxToken token) {
        SyntaxToken before = null;
        boolean past = false;
        for (SyntaxElement e : node.children()) {
            if (!(e instanceof SyntaxToken t) || t.isTrivia()) {
                continue;
            }
            if (past) {
                return (t.kind() == SyntaxKind.COMMA || t.kind() == SyntaxKind.RBRACE)
                        && before != null
                        && (before.kind() == SyntaxKind.LBRACE || before.kind() == SyntaxKind.COMMA);
            }
            if (t == token) {
                past = true;
                continue;
            }
            before = t;
        }
        return false;
    }

    /** Where renaming touches, before what to write there is decided. */
    private Map<String, List<Range>> renameRanges(String uri, Position pos, ModuleGraph graph) {
        Map<String, List<Range>> byUri = new LinkedHashMap<>();
        for (Location loc : references(uri, pos, graph, true)) {
            byUri.computeIfAbsent(loc.uri(), k -> new ArrayList<>()).add(loc.range());
        }
        if (byUri.isEmpty()) {
            return byUri;   // nothing under the cursor to rename
        }
        // references() treats a name in an `exposing`/`import` list as a binding site, not a use, and
        // skips it. Rename must still update those, or the module stops exposing (and importers stop
        // importing) the renamed symbol, breaking the build.
        //
        // Which module those belong to is the same question the references were found by, and it has
        // to be answered the same way: renaming from a qualified use renames the module the
        // reference names, and matching the spelling here would edit this module's own `exposing`
        // instead — leaving both modules uncompilable.
        Compilation compilation = compileOf(graph);
        TypeName type = typeUnderCursor(compilation, uri, pos);
        if (type != null) {
            addExposingAndImportSites(compilation, type.name(), type.module(), graph, byUri);
            return byUri;
        }
        ValueName value = valueUnderCursor(compilation, uri, pos);
        if (value != null) {
            String declaring = switch (value) {
                case ValueName.Helper h -> h.module();
                case ValueName.Behavior b -> b.module();
                // a local is named where it is bound and nowhere else; the library and the language
                // are not this workspace's to rename
                case ValueName.Local _, ValueName.Stdlib _, ValueName.OfType _,
                        ValueName.Builtin _, ValueName.Unresolved _ -> null;
            };
            if (declaring != null) {
                addExposingAndImportSites(compilation, value.name(), declaring, graph, byUri);
            }
            return byUri;
        }
        String text = graph.text(uri);
        SyntaxNode root = CstParser.parse(text).root();
        LineIndex lines = new LineIndex(text);
        SyntaxToken ident = identAt(meaningfulTokens(root), lines, lines.offsetOf(pos.line(), pos.character()));
        if (ident != null) {
            String name = nameOf(ident);
            String definingModule = declaringDef(root, name) != null
                    ? moduleOf(compilation, graph, uri) : importedFrom(text, name);
            if (definingModule != null) {
                addExposingAndImportSites(compilation, name, definingModule, graph, byUri);
            }
        }
        return byUri;
    }

    /** What the cursor is on in the value namespace, as the compiler answers it, or null when
     * nothing there is a name in it. */
    private ValueName valueUnderCursor(Compilation compilation, String uri, Position pos) {
        return compilation.db().ask(new Names.ValueAt(cursor(uri, pos))).value();
    }

    /**
     * Where what the cursor names as a value is written, as the compiler answers it: the binding
     * that introduced a local, or the {@code let} or {@code behavior} that declares it.
     *
     * <p>A local was out of reach while this was matched by spelling — one spelling may be bound in
     * several bodies, and nothing said which binding a use belonged to. Resolution says.
     */
    private Optional<Location> valueDeclarationOf(Compilation compilation, String uri, Position pos,
                                                  ModuleGraph graph) {
        ValueName target = valueUnderCursor(compilation, uri, pos);
        if (target == null) {
            return Optional.empty();
        }
        return valueDeclarationOf(compilation, target, uri, graph);
    }

    private Optional<Location> valueDeclarationOf(Compilation compilation, ValueName target,
                                                  String uri, ModuleGraph graph) {
        WrittenName at = compilation.db().ask(new Names.ValueDeclaredAt(target)).value();
        return nameAt(at, declaringFile(compilation, target, uri), graph);
    }

    /**
     * Every place the value's own name is written as a declaration.
     *
     * <p>More than one where a behavior is what it names: the {@code behavior} line and the
     * {@code let} line both write it. Renaming from a use has to reach both, or the module goes on
     * naming something that is no longer there — and matching the spelling, which is what answered
     * this before, saw both because it saw every line the name was on.
     */
    private List<Location> valueDeclarationsOf(Compilation compilation, ValueName target,
                                               String uri, ModuleGraph graph) {
        List<WrittenName> written =
                compilation.db().ask(new Names.ValueDeclarationsOf(target)).value();
        if (written == null) {
            return List.of();
        }
        List<Location> out = new ArrayList<>();
        for (WrittenName at : written) {
            nameAt(at, declaringFile(compilation, target, uri), graph).ifPresent(out::add);
        }
        return out;
    }

    /** The file a value's declaration is in where its position does not name one. */
    private String declaringFile(Compilation compilation, ValueName target, String uri) {
        return switch (target) {
            case ValueName.Local _ -> uri;   // bound in the body the cursor is in
            case ValueName.Helper h -> compilation.sourceIdOf(h.module());
            case ValueName.Behavior b -> compilation.sourceIdOf(b.module());
            case ValueName.Stdlib _, ValueName.OfType _, ValueName.Builtin _,
                    ValueName.Unresolved _ -> null;
        };
    }

    /**
     * The name an identifier token spells.
     *
     * <p>The one door from a token to a name in the paths that read the tree of characters rather
     * than the compiler's answer — an import list entry, a file the compile could not read.
     * Canonically equivalent spellings are one name, and a token is characters, so every one of
     * those paths turns a token into a name exactly here.
     *
     * <p>Canonicalizing at the comparison instead — which is where it was — leaves whichever side
     * came from a cursor raw, so a cursor on a decomposed spelling found no declaration and a
     * cursor on a composed one found it. Which spelling the author's cursor happened to be on is
     * not a thing an editor may answer differently.
     */
    private static String nameOf(SyntaxToken token) {
        return token == null ? null : Reserved.name(token.text());
    }

    /** Whether an identifier token spells {@code name}, which is canonical. */
    private static boolean spells(SyntaxToken token, String name) {
        return token != null && name.equals(nameOf(token));
    }

    /**
     * Whether the compile read this document and answered about the names in it.
     *
     * <p>This is what decides whether an unanswered question is a question with no answer or a
     * question nothing could be asked of. Where the compile read the file, its silence is the
     * answer: nothing is named under the cursor. Where it could not — a file with a syntax error is
     * held out of the module set, and a module whose names would not resolve has no answers to give
     * — matching the spelling is all there is, and it goes on being what an author gets while a file
     * is half-typed.
     */
    private boolean resolves(Compilation compilation, String uri) {
        String module = compilation.moduleOf(uri);
        return module != null && compilation.db().ask(new Names.Resolution(module)).present();
    }

    /** Where a type is declared, as the compiler answers it. */
    private Optional<Location> declarationOf(Compilation compilation, TypeName target,
                                             ModuleGraph graph) {
        // Which module, which name and where it was written is the compiler's answer — the part a
        // spelling match gets wrong.
        WrittenName at = compilation.db().ask(new Names.DeclaredAt(target)).value();
        return nameAt(at, compilation.sourceIdOf(target.module()), graph);
    }

    /**
     * Every place the type under the cursor is named, as the compiler answers it, or null when the
     * cursor is not on a type. A name resolves to one declaration wherever it is written, so a
     * module that declares its own type of the same spelling is not swept up, and a qualified
     * reference to another module's is.
     */
    private List<Location> usesOf(Compilation compilation, String uri, Position pos,
                                  ModuleGraph graph, boolean includeDeclaration) {
        TypeName target = typeUnderCursor(compilation, uri, pos);
        if (target == null) {
            return null;
        }
        List<Location> out = new ArrayList<>();
        if (includeDeclaration) {
            declarationOf(compilation, target, graph).ifPresent(out::add);
        }
        for (String module : compilation.modules()) {
            String moduleUri = compilation.sourceIdOf(module);
            for (Resolve.Denotation use
                    : compilation.db().ask(new Names.UsesOf(module, target)).value()) {
                String at = documentOf(use.pos(), moduleUri, graph);
                if (at != null) {
                    out.add(new Location(at, writtenRange(use.written())));
                }
            }
        }
        return out;
    }

    /**
     * Every place the value under the cursor is named, as the compiler answers it. Empty when the
     * cursor is not on one.
     *
     * <p>{@link #usesOf} for the value namespace, and the reason a local can be asked about at all:
     * a use denotes a binding, so the uses of one body's {@code x} are not another's. Matching the
     * spelling could only ever answer about top-level names, and answered about the wrong one where
     * two modules spelled a name alike.
     */
    private List<Location> valueUsesOf(Compilation compilation, String uri, Position pos,
                                       ModuleGraph graph, boolean includeDeclaration) {
        ValueName target = valueUnderCursor(compilation, uri, pos);
        if (target == null) {
            return List.of();
        }
        List<Location> out = new ArrayList<>();
        if (includeDeclaration) {
            out.addAll(valueDeclarationsOf(compilation, target, uri, graph));
        }
        for (String module : compilation.modules()) {
            String moduleUri = compilation.sourceIdOf(module);
            for (Resolve.ValueUse use
                    : compilation.db().ask(new Names.ValueUsesOf(module, target)).value()) {
                String at = documentOf(use.pos(), moduleUri, graph);
                if (at != null) {
                    out.add(new Location(at, writtenRange(use.written())));
                }
            }
        }
        return out;
    }

    /** Adds the {@code exposing ( name )} occurrence in the module that defines {@code name}, and each
     * {@code import <definingModule> ( name )} occurrence in the modules that import it — the binding
     * sites find-references skips but rename must carry along. */
    private void addExposingAndImportSites(Compilation compilation, String name,
                                           String definingModule, ModuleGraph graph,
                                           Map<String, List<Range>> byUri) {
        for (String u : graph.uris()) {
            String t = graph.text(u);
            SyntaxNode root = CstParser.parse(t).root();
            LineIndex lines = new LineIndex(t);
            boolean owns = definingModule.equals(moduleOf(compilation, graph, u));
            for (SyntaxNode top : root.childNodes()) {
                if (top.kind() == SyntaxKind.MODULE_HEADER && owns) {
                    top.child(SyntaxKind.EXPOSING_CLAUSE).ifPresent(clause -> {
                        for (SyntaxNode entry : clause.childNodes()) {
                            if (entry.kind() != SyntaxKind.EXPOSED_ENTRY) {
                                continue;
                            }
                            entry.child(SyntaxKind.QUALIFIED_NAME).ifPresent(qn -> {
                                SyntaxToken tok = nameToken(qn);
                                if (spells(tok, name)) {
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
                                        && spells(tok, name)) {
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
                sb.append(nameOf(t));
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
            out.putIfAbsent(nameOf(name), new CompletionItem(nameOf(name), kind));
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
                        out.putIfAbsent(nameOf(bound),
                                new CompletionItem(nameOf(bound), CompletionItem.VARIABLE));
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
            SyntaxKind.CONSTRUCTS_CLAUSE, SyntaxKind.DEPENDS_CLAUSE, SyntaxKind.NEW_DATA_EXPR,
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
                if (t.kind() != SyntaxKind.IDENT || !spells(t, name)) {
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
                    if (spells(bound, name)) {
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

    /** The document the module {@code moduleName} is declared in, or {@code null} if none — the
     * compile's answer, with the headers read only for a module whose file the compile could not
     * read. */
    private String uriOfModule(Compilation compilation, ModuleGraph graph, String moduleName) {
        String declared = compilation.sourceIdOf(moduleName);
        if (declared != null && graph.text(declared) != null) {
            return declared;
        }
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
        SyntaxToken ident = identAt(meaningfulTokens(root), lines, lines.offsetOf(pos.line(), pos.character()));
        if (ident == null) {
            return Optional.empty();
        }
        SyntaxNode def = declaringDef(root, nameOf(ident));
        if (def == null) {
            return Optional.empty();
        }
        SyntaxToken name = nameToken(def);
        return name == null ? Optional.empty() : Optional.of(tokenRange(lines, name));
    }

    /**
     * Hover: on a clause of an invariant, how that clause can be discharged at compile time; anywhere
     * else, the signature line of the definition the identifier under the cursor names.
     *
     * <p>The clause answer is the compiler's, because the classification is a fact about the language
     * and not something a reader of the syntax can work out. The rest stays syntactic: a hover that
     * only shows what is written does not need a compile, and this one asks for one only where it has
     * something semantic to say.
     */
    public Optional<Hover> hover(String uri, String text, Position pos, ModuleGraph graph) {
        Optional<Hover> clause = invariantClauseHover(uri, text, pos, graph);
        return clause.isPresent() ? clause : hover(text, pos);
    }

    /** The discharge classification of the invariant clause the cursor is in, or empty when it is not
     * in one. */
    private Optional<Hover> invariantClauseHover(String uri, String text, Position pos,
                                                 ModuleGraph graph) {
        LineIndex lines = new LineIndex(text);
        SyntaxNode root = CstParser.parse(text).root();
        int offset = lines.offsetOf(pos.line(), pos.character());
        SyntaxNode clause = enclosing(root, offset, SyntaxKind.INVARIANT_CLAUSE);
        if (clause == null) {
            return Optional.empty();
        }
        SyntaxNode data = enclosing(root, offset, SyntaxKind.DATA_DEF);
        SyntaxToken name = data == null ? null : nameToken(data);
        Compilation compilation = compileOf(graph);
        String module = moduleOf(compilation, graph, uri);
        if (name == null || module == null) {
            return Optional.empty();
        }
        Map<TypeName, List<ClauseDischarge>> byType =
                compilation.db().ask(new Shapes.InvariantCapabilities(module)).value();
        List<ClauseDischarge> clauses = byType == null
                ? null : byType.get(new TypeName(module, nameOf(name)));
        if (clauses == null || clauses.isEmpty()) {
            return Optional.empty();
        }
        // The clauses are in the order they are written, so the one the cursor is in is the last that
        // starts at or before it.
        ClauseDischarge found = null;
        for (ClauseDischarge c : clauses) {
            if (lines.offsetOf(c.clause().line() - 1, c.clause().column() - 1) <= offset) {
                found = c;
            }
        }
        if (found == null) {
            return Optional.empty();
        }
        return Optional.of(new Hover(dischargeContents(found), nodeRange(lines, clause)));
    }

    /** What a clause's classification says, in the terms an author acts on. */
    private String dischargeContents(ClauseDischarge clause) {
        String head = switch (clause.kind()) {
            case DERIVABLE -> "**Static discharge: derivable**\n\n"
                    + "The checker can prove this clause from numeric relations when the constructed "
                    + "value is nameable, so any guard that implies it discharges the construction.";
            case EXACT_MATCH -> "**Static discharge: exact match**\n\n"
                    + "The checker can discharge this clause only from a guard establishing the same "
                    + "canonical property. Nothing weaker discharges it.";
            case RUNTIME_ONLY -> "**Static discharge: runtime only**\n\n"
                    + "This clause cannot be represented by the static checker and is enforced only "
                    + "at construction time. No guard discharges it.";
        };
        String body = clause.reason().map(why -> head + "\n\n" + why + ".").orElse(head);
        // What the clause is called is what an attempted construction's arm and a boundary issue read,
        // so it belongs beside how the clause discharges.
        return clause.name()
                .map(n -> body + "\n\nDeparted from by name: `| " + n + " -> ...`.")
                .orElse(body);
    }

    /** The innermost node of {@code kind} whose span contains {@code offset}, or null. */
    private SyntaxNode enclosing(SyntaxNode node, int offset, SyntaxKind kind) {
        SyntaxNode found = node.kind() == kind ? node : null;
        for (SyntaxElement e : node.children()) {
            if (e instanceof SyntaxNode child && offset >= child.start() && offset < child.end()) {
                SyntaxNode inner = enclosing(child, offset, kind);
                if (inner != null) {
                    found = inner;
                }
            }
        }
        return found;
    }

    /** Hover: shows the signature line of the definition the identifier under the cursor names. */
    public Optional<Hover> hover(String text, Position pos) {
        LineIndex lines = new LineIndex(text);
        SyntaxNode root = CstParser.parse(text).root();
        int offset = lines.offsetOf(pos.line(), pos.character());
        SyntaxToken ident = identAt(meaningfulTokens(root), lines, offset);
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
            SyntaxNode def = declaringDef(root, nameOf(ident));
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
                if (spells(n, name)) {
                    return def;
                }
            }
        }
        return null;
    }

    /**
     * The identifier a cursor at {@code offset} is on.
     *
     * <p>Read as the name it spells and asked of that name. The dotted run of identifiers around the
     * cursor is one written name, and {@link WrittenName#partAt} says which of its parts a cursor is
     * on — including where it stops being on one, which is a rule about ends that belongs in one
     * place. This path had a rule of its own twice and it disagreed with the compiler's both times:
     * once by stopping a character early at the end of a name, once by counting the character after
     * a qualifier.
     *
     * <p>What it cannot do is tell {@code up.Amount} from {@code x.field}: one is a name and the
     * other is a field taken off a value, and which it is has to be resolved, which is the thing
     * that is missing whenever this runs. So a dotted run is read as a name, and the boundary inside
     * one is a separator. Said rather than left to be found: this is an approximation the syntax
     * forces, not a second opinion about where a name ends.
     */
    private SyntaxToken identAt(List<SyntaxToken> tokens, LineIndex lines, int offset) {
        DottedRun run = dottedRun(tokens, offset);
        if (run.parts().isEmpty()) {
            return null;
        }
        WrittenName name = spelledBy(run.parts().get(0), lines);
        for (int i = 1; i < run.parts().size(); i++) {
            name = name.then(spelledBy(run.parts().get(i), lines));
        }
        SourcePos at = lines.posOf(offset);
        // A run a dot continues is a name the author is still writing, and the end of what is
        // written of it is not the end of the name — the member is what comes next, and a caret
        // waiting for it means neither the qualifier nor the name.
        int part = run.unfinished() ? name.partWithin(at) : name.partAt(at);
        return part < 0 ? null : run.parts().get(part);
    }

    /** The identifiers of one dotted name, and whether a dot carries it past the last of them —
     *  which is what a name being typed looks like and what a written one never does. */
    private record DottedRun(List<SyntaxToken> parts, boolean unfinished) {

        static DottedRun none() {
            return new DottedRun(List.of(), false);
        }
    }

    /** One token's name, where it is written. */
    private static WrittenName spelledBy(SyntaxToken token, LineIndex lines) {
        return WrittenName.of(token.text(), lines.posOf(token.start()));
    }

    /**
     * The identifiers of the dotted run the cursor is at, in order, or none where it is at no
     * identifier at all.
     *
     * <p>Generous about the ends, because what a cursor at a boundary means is the name's to say
     * and not this walk's. Two identifiers cannot touch — the grammar puts something between them —
     * so at most one answers.
     */
    private DottedRun dottedRun(List<SyntaxToken> tokens, int offset) {
        int at = -1;
        for (int i = 0; i < tokens.size() && at < 0; i++) {
            SyntaxToken t = tokens.get(i);
            if (t.kind() == SyntaxKind.IDENT && offset >= t.start() && offset <= t.end()) {
                at = i;
            }
        }
        if (at < 0) {
            return DottedRun.none();
        }
        int first = at;
        while (first >= 2 && tokens.get(first - 1).kind() == SyntaxKind.DOT
                && tokens.get(first - 2).kind() == SyntaxKind.IDENT) {
            first -= 2;
        }
        int last = at;
        while (last + 2 < tokens.size() && tokens.get(last + 1).kind() == SyntaxKind.DOT
                && tokens.get(last + 2).kind() == SyntaxKind.IDENT) {
            last += 2;
        }
        List<SyntaxToken> parts = new ArrayList<>();
        for (int i = first; i <= last; i += 2) {
            parts.add(tokens.get(i));
        }
        boolean unfinished = last + 1 < tokens.size()
                && tokens.get(last + 1).kind() == SyntaxKind.DOT;
        return new DottedRun(parts, unfinished);
    }

    /** Every token of {@code root} that is not trivia, in the order they are written — read once
     *  per parse and asked many times, since a rename asks about every place it touches. */
    private List<SyntaxToken> meaningfulTokens(SyntaxNode root) {
        List<SyntaxToken> out = new ArrayList<>();
        meaningfulTokens(root, out);
        return out;
    }

    private void meaningfulTokens(SyntaxNode node, List<SyntaxToken> out) {
        for (SyntaxElement e : node.children()) {
            if (e instanceof SyntaxNode child) {
                meaningfulTokens(child, out);
            } else if (e instanceof SyntaxToken t && !t.isTrivia()) {
                out.add(t);
            }
        }
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
        collectTokens(node, lines, out, node.kind(), false);
    }

    /**
     * {@code enclosing} is the nearest ancestor that is not a pattern. A pattern says what a value is
     * made of, not what its names are for: the same {@code (a, b)} binds parameters in a lambda's
     * head and locals in a {@code let}, so classification has to see past it.
     *
     * <p>{@code callee} says this node is what an application applies. It cannot be worked out from
     * the parent alone: a qualified callee is a field read, and only its last name is the function —
     * {@code Map.mapValues(f, m)} names a namespace and then a function in it. So it is carried down, to
     * the field a read takes and not to what the read is taken off.
     */
    private void collectTokens(SyntaxNode node, LineIndex lines, List<int[]> out,
                               SyntaxKind enclosing, boolean callee) {
        SyntaxKind outer = isPatternNode(node.kind()) ? enclosing : node.kind();
        boolean seenIdent = false;
        boolean seenChildNode = false;
        for (SyntaxElement e : node.children()) {
            if (e instanceof SyntaxNode child) {
                boolean applied = node.kind() == SyntaxKind.APPLY_EXPR ? !seenChildNode
                        : callee && node.kind() == SyntaxKind.PAREN_EXPR;
                seenChildNode = true;
                collectTokens(child, lines, out, outer, applied);
            } else {
                SyntaxToken token = (SyntaxToken) e;
                int type = classify(token, node.kind(), outer, seenIdent, callee);
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

    private static boolean isPatternNode(SyntaxKind k) {
        return k == SyntaxKind.PATTERN_NAME || k == SyntaxKind.PATTERN_TUPLE
                || k == SyntaxKind.PATTERN_CTOR || k == SyntaxKind.PATTERN_RECORD
                || k == SyntaxKind.PATTERN_FIELD;
    }

    /** The token type index for a leaf, or {@code -1} to emit nothing (punctuation, whitespace). */
    private int classify(SyntaxToken token, SyntaxKind parent, SyntaxKind enclosing,
                         boolean afterFirstIdent, boolean callee) {
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
        if (EditorSymbols.isOperator(k)) {
            return T_OPERATOR;
        }
        if (k == SyntaxKind.IDENT) {
            return classifyIdent(parent, enclosing, afterFirstIdent, callee);
        }
        return -1;   // the punctuation an editor leaves alone, and whitespace
    }

    private int classifyIdent(SyntaxKind parent, SyntaxKind enclosing, boolean afterFirstIdent,
                              boolean callee) {
        // what an application applies: the bare name, or the last name of a qualified one. The
        // qualifier in front of it is not the function and is classified as what it is written as.
        if (callee && (parent == SyntaxKind.VAR_EXPR || parent == SyntaxKind.FIELD_ACCESS)) {
            return T_FUNCTION;
        }
        // a name a pattern binds is a parameter where the pattern is one, and a local otherwise
        if (parent == SyntaxKind.PATTERN_NAME) {
            return enclosing == SyntaxKind.LAMBDA_EXPR || enclosing == SyntaxKind.FN_PARAM
                    || enclosing == SyntaxKind.PARAM ? T_PARAMETER : T_VARIABLE;
        }
        // `{ a }` and `{ a = n }`: the first name is the field read, the second the name it binds
        if (parent == SyntaxKind.PATTERN_FIELD) {
            return afterFirstIdent ? T_VARIABLE : T_PROPERTY;
        }
        // `depends on f`: the `on` lexes as an identifier but is the second word of the keyword
        if (parent == SyntaxKind.DEPENDS_CLAUSE && !afterFirstIdent) {
            return T_KEYWORD;
        }
        return switch (parent) {
            case TYPE_REF, TYPE_ARGS, SUM_BODY, NEWTYPE_BODY, CONSTRUCTS_CLAUSE, DEPENDS_CLAUSE,
                 DATA_DEF, NEW_DATA_EXPR, PATTERN_CTOR -> T_TYPE;
            case BEHAVIOR_DEF, FN_DEF, STAGE -> T_FUNCTION;
            case PARAM, FN_PARAM, LAMBDA_EXPR -> T_PARAMETER;
            case FIELD, FIELD_INIT, FIELD_ACCESS, FIELD_GETTER -> T_PROPERTY;
            case MODULE_HEADER, QUALIFIED_NAME, IMPORT_DECL -> T_NAMESPACE;
            default -> T_VARIABLE;
        };
    }

    private static boolean isKeyword(SyntaxKind k) {
        return switch (k) {
            case MODULE_KW, IMPORT_KW, EXPOSING_KW, DATA_KW, INVARIANT_KW, AS_KW, LET_KW, GUARD_KW,
                 ELSE_KW, TRUE_KW, FALSE_KW, IF_KW, THEN_KW, BEHAVIOR_KW, DEPENDS_KW, CONSTRUCTS_KW,
                 MATCH_KW, WITH_KW, UNREACHABLE_KW -> true;
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

    /**
     * An LSP diagnostic from a structured {@link Diagnostic} for a document read on its own:
     * everything it points at is in that document, so it is its own published source.
     *
     * <p>No linked locations. A link is a URI, and a document compiled from its text alone has none
     * to give — the workspace path is where a marker can point somewhere the editor can open.
     */
    private LspDiagnostic fromDiagnostic(LineIndex lines, Diagnostic d) {
        return project(d, null, null, id -> lines, id -> null);
    }

    /**
     * One diagnostic as the file {@code publishedUri} reads it: the range is the place it points at
     * in that file, and every other place it points at becomes a linked location.
     *
     * <p>Which region is the range depends on which file is asking. A problem written in two of them
     * is published in both, and on the second the primary region is the one that is elsewhere — so
     * the two change places rather than the second file getting a marker on a line that has nothing
     * to do with it.
     *
     * @param primarySourceId the source the primary region is in, null when the compile named none
     * @param publishedUri the file this marker is being put in, null for a single-document compile
     * @param linesOf the line index of a source, for turning its positions into ranges
     * @param uriOf the editor's name for a source, null when it has none to link to
     */
    private LspDiagnostic project(Diagnostic d, String primarySourceId, String publishedUri,
                                  java.util.function.Function<String, LineIndex> linesOf,
                                  java.util.function.Function<String, String> uriOf) {
        String message = DiagnosticRenderer.body(d, EDITOR_LANGUAGE);
        if (d.diff() != null) {
            message = message + " (expected " + d.diff().expectedType()
                    + ", but was " + d.diff().actualType() + ")";
        }
        int severity = d.severity() == souther.compiler.diag.Severity.WARNING
                ? LspDiagnostic.WARNING : LspDiagnostic.ERROR;
        DiagnosticView view = DiagnosticView.of(d, primarySourceId, publishedUri);
        List<LspDiagnostic.Related> related = new ArrayList<>();
        for (Spot other : view.others()) {
            String uri = other.sourceId() == null ? publishedUri : uriOf.apply(other.sourceId());
            LineIndex lines = linesOf.apply(other.sourceId());
            if (uri == null || lines == null || other.region() == null) {
                continue;   // nothing the editor could open, so nothing to link to
            }
            related.add(new LspDiagnostic.Related(uri, rangeOfRegion(other.region()),
                    other.labelled()
                            ? Messages.render(other.said(), EDITOR_LANGUAGE)
                            : message));
        }
        Range range = view.anchor().region() != null
                ? rangeOfRegion(view.anchor().region())
                : rangeOf(linesOf.apply(view.anchor().sourceId()), d);
        return new LspDiagnostic(range, severity, d.code(), message, tagsOf(d), related);
    }

    /** What an editor should do with a diagnostic's range beyond marking it. An unused import names
     * text that is there and does nothing, so the name is faded rather than only listed. */
    private static List<Integer> tagsOf(Diagnostic d) {
        return "E1922".equals(d.code()) ? List.of(LspDiagnostic.UNNECESSARY) : List.of();
    }

    private Range rangeOfRegion(Region r) {
        return new Range(position(r.start()), position(r.end()));
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
