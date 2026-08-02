package souther.compiler.query;

import souther.compiler.Prelude;
import souther.compiler.ast.Ast;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.SourcePos;
import souther.compiler.check.Exposing;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.meta.ModulePath;
import souther.compiler.meta.PublishedModule;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Getting from text to a set of named modules: the inputs, the parse of each source, which module
 * each source declares, and the modules this compilation reaches that no source declares.
 *
 * <p>Everything here is about sources and names. Nothing yet knows what a name means — that starts
 * at {@link Names}.
 */
public final class Front {

    private Front() {}

    /** The namespace the compiler ships. A user module may not take a reserved name, or it could
     * grant itself the core's privileges. */
    private static final String RESERVED = "souther";

    /** Every source id this compilation was given, in the order they were given. The order is the
     * index a diagnostic names when it says which file it came from. */
    public record Ids() implements Input<List<String>> {}

    /** The text of one source. */
    public record Text(String id) implements Input<String> {
        @Override
        public String sourceId() {
            return id;
        }
    }

    /** The compiled modules of the projects this one depends on. */
    public record Path() implements Input<ModulePath> {}

    /**
     * The name a source with no {@code module} header takes. Absent means a header is required,
     * which is what linking a set of sources needs: a module reached by an import has to be named.
     */
    public record DefaultName() implements Input<String> {}

    /**
     * Modules the caller has already found unusable and did not hand over — a file an editor holds
     * out of the compile because of its own syntax errors.
     *
     * <p>An importer of one is left alone rather than told the module is unknown: the error belongs
     * to the file that will not parse, which reports it separately, and saying it again on the
     * importer sends the author to a file that is fine.
     */
    public record Broken() implements Input<Set<String>> {}

    /**
     * Whether these sources are the compiler's own. The reserved namespace is what keeps a user
     * module from granting itself the core's privileges; the core modules are in it by definition,
     * so compiling them is the one case where the name is theirs to take.
     */
    public record Core() implements Input<Boolean> {}

    /** One source, parsed, with the text of each declaration kept for publishing. */
    public record Parsed(String id) implements Key<CstFrontend.Parsed> {
        @Override
        public String sourceId() {
            return id;
        }

        @Override
        public Answer<CstFrontend.Parsed> compute(Db db) {
            Answer<String> text = db.ask(new Text(id));
            if (!text.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(CstFrontend.parseWithSlices(
                        text.value(), db.ask(new DefaultName()).value()));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
        }
    }

    /**
     * Which source declares which module. An {@code examples for X} file declares no module of its
     * own — it contributes rows to X — so it is listed apart, under the module it names.
     *
     * <p>A source that will not parse is in neither list. Its own error is reported where it is
     * parsed, and here it is simply a module this compilation does not have: an importer of it gets
     * the absence, not a second copy of the syntax error.
     */
    public record Layout() implements Key<Layout.Of> {

        /**
         * @param idOfModule the source each module was declared in
         * @param exampleFilesOf the {@code examples for} sources contributing to each module
         * @param exampleFileTargets the module each {@code examples for} source names, by source id
         */
        public record Of(Map<String, String> idOfModule,
                         Map<String, List<String>> exampleFilesOf,
                         Map<String, String> exampleFileTargets) {}

        @Override
        public Answer<Of> compute(Db db) {
            List<String> ids = db.ask(new Ids()).value();
            if (ids == null) {
                return Answer.absent();
            }
            Map<String, String> idOfModule = new LinkedHashMap<>();
            Map<String, List<String>> exampleFilesOf = new LinkedHashMap<>();
            Map<String, String> exampleFileTargets = new LinkedHashMap<>();
            for (String id : ids) {
                Answer<CstFrontend.Parsed> parsed = db.ask(new Parsed(id));
                if (!parsed.present()) {
                    continue;   // reported where it was parsed
                }
                Ast.Module m = parsed.value().module();
                if (m.exampleFileTarget() != null) {
                    exampleFileTargets.put(id, m.exampleFileTarget());
                    exampleFilesOf.computeIfAbsent(m.exampleFileTarget(), k -> new ArrayList<>()).add(id);
                    continue;
                }
                idOfModule.putIfAbsent(m.name(), id);
            }
            return Answer.of(new Of(Ordered.map(idOfModule), Ordered.map(exampleFilesOf),
                    Ordered.map(exampleFileTargets)));
        }
    }

    /**
     * One module as its source declared it, with the standard-library {@code exposing} lines already
     * rewritten and its name checked against the reserved namespace.
     *
     * <p>The rows of every {@code examples for} file naming it are appended here, so a module's
     * examples are its examples wherever they were written. Which file a row came from is
     * {@link Names.Examples}' business, not this one's.
     */
    public record Exposed(String name) implements Key<Ast.Module> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Ast.Module> compute(Db db) {
            Layout.Of layout = db.ask(new Layout()).value();
            if (layout == null) {
                return Answer.absent();
            }
            String id = layout.idOfModule().get(name);
            if (id == null) {
                return Answer.absent();   // not declared by any source; the path may still have it
            }
            Answer<CstFrontend.Parsed> parsed = db.ask(new Parsed(id));
            if (!parsed.present()) {
                return Answer.absent();
            }
            Ast.Module raw = parsed.value().module();
            if (!Boolean.TRUE.equals(db.ask(new Core()).value())) {
                Report reserved = reservedNamespace(raw.name(), raw.pos());
                if (reserved != null) {
                    return Answer.absent(reserved);
                }
            }
            Exposing.Validated imports = Exposing.read(raw);
            Ast.Module m = Exposing.withoutLibraryImports(raw, imports.kept());
            return Answer.of(withAttachedRows(db, m, layout.exampleFilesOf()
                    .getOrDefault(name, List.of())));
        }

        /**
         * The module with every attached file's examples, fakes and values appended.
         *
         * <p>The values join the module the rows join, as the fakes do: a module's own values are what its
         * attached files' rows name, and the other way round. Nothing outside can reach them either way —
         * an attached file is not a module and is not imported, and the values it declares are in no
         * {@code exposing}.
         */
        private Ast.Module withAttachedRows(Db db, Ast.Module m, List<String> files) {
            if (files.isEmpty()) {
                return m;
            }
            List<Ast.Example> examples = new ArrayList<>(m.examples());
            List<Ast.Fake> fakes = new ArrayList<>(m.fakes());
            List<Ast.FnDef> fns = new ArrayList<>(m.fns());
            Set<String> taken = new LinkedHashSet<>();
            for (Ast.FnDef fn : m.fns()) {
                taken.add(fn.name());
            }
            for (String id : files) {
                Answer<CstFrontend.Parsed> file = db.ask(new Parsed(id));
                if (!file.present()) {
                    continue;
                }
                examples.addAll(file.value().module().examples());
                fakes.addAll(file.value().module().fakes());
                for (Ast.FnDef value : file.value().module().fns()) {
                    // A name already declared is not merged, so the module has no duplicate to report
                    // against a position in a file it cannot quote — the attached file's own key reports
                    // it, where the position and the file agree (see Output.Examples).
                    if (taken.add(value.name())) {
                        fns.add(value);
                    }
                }
            }
            return new Ast.Module(m.name(), m.exposing(), m.exposedOutputs(), m.imports(), m.defs(),
                    m.behaviors(), fns, examples, fakes, m.exampleFileTarget(), m.pos());
        }
    }

    /**
     * The modules this compilation reaches that no source declares, read off the path. A module
     * found there brings its own reaches with it, so a dependency of a dependency arrives too.
     *
     * <p>Which of its behaviors are injection targets comes with it: no {@code let} is published, so
     * that cannot be read off a module here the way it is read off a source.
     */
    public record FromPath() implements Key<FromPath.Of> {

        public record Of(Map<String, Ast.Module> modules, Map<String, Set<String>> injected) {}

        @Override
        public Answer<Of> compute(Db db) {
            Layout.Of layout = db.ask(new Layout()).value();
            ModulePath path = db.ask(new Path()).value();
            if (layout == null || path == null) {
                return Answer.of(new Of(Map.of(), Map.of()));
            }
            PublishedModule.Classes classes = path.declarations();
            Map<String, Ast.Module> found = new LinkedHashMap<>();
            Map<String, Set<String>> injected = new LinkedHashMap<>();
            List<Report> reports = new ArrayList<>();
            // What is waiting to be read, and — for one a module off the path needs — which module
            // needs it, so an incomplete path is reported as that rather than as an import nobody
            // wrote.
            Deque<String> pending = new ArrayDeque<>();
            Map<String, String> neededBy = new LinkedHashMap<>();
            for (String declared : layout.idOfModule().keySet()) {
                Ast.Module m = db.ask(new Exposed(declared)).value();
                if (m != null) {
                    pending.addAll(reaches(m));
                }
            }
            Set<String> tried = new HashSet<>();
            while (!pending.isEmpty()) {
                String name = pending.poll();
                if (layout.idOfModule().containsKey(name) || found.containsKey(name)
                        || !tried.add(name)) {
                    continue;
                }
                PublishedModule published = PublishedModule.read(name, classes);
                if (published == null) {
                    if (neededBy.containsKey(name) && !Prelude.isQualifier(name)) {
                        reports.add(Report.of(Diagnostic.of(null, "check.module.pathincomplete")
                                .title("check.module.title").args(name, neededBy.get(name))
                                .hint("check.module.pathincomplete.hint", name).build()));
                    }
                    continue;   // written in a source being compiled: still that import's own error
                }
                Report reserved = reservedNamespace(published.module().name(),
                        published.module().pos());
                if (reserved != null) {
                    reports.add(reserved);
                    continue;
                }
                Ast.Module m = Exposing.withoutLibraryImports(published.module(),
                        Exposing.read(published.module()).kept());
                found.put(name, m);
                injected.put(name, published.injectedBehaviors());
                for (String reach : reaches(m)) {
                    neededBy.putIfAbsent(reach, name);
                    pending.add(reach);
                }
            }
            return Answer.of(new Of(Ordered.map(found), Ordered.map(injected)), reports);
        }
    }

    /**
     * A module of this compilation, wherever it came from: declared by a source, or read off the
     * path. Absent when nothing here has it, which is what an import of an unknown module sees.
     *
     * <p>A source module reaches here with its qualified behavior references already bound to
     * imports ({@link Names.Bound}); a path module has none to bind, because a behavior reference
     * is not published.
     */
    public record Available(String name) implements Key<Ast.Module> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Ast.Module> compute(Db db) {
            Answer<Ast.Module> bound = db.ask(new Names.Bound(name));
            if (bound.present()) {
                return Answer.of(bound.value());
            }
            FromPath.Of path = db.ask(new FromPath()).value();
            Ast.Module fromPath = path == null ? null : path.modules().get(name);
            return fromPath == null ? Answer.absent() : Answer.of(fromPath);
        }
    }

    /**
     * The modules a module imports, named once each, in the order it names them.
     *
     * <p>Its own question for the same reason {@link Exposes} is: what reads this wants the shape of
     * the workspace around a module, and that shape survives almost every edit to the module itself.
     * Reading the module here would put every body on the far side of an answer about its header.
     */
    public record ImportedModules(String name) implements Key<List<String>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<List<String>> compute(Db db) {
            Ast.Module m = db.ask(new Available(name)).value();
            if (m == null) {
                return Answer.of(List.of());
            }
            Set<String> imported = new LinkedHashSet<>();
            for (Ast.Import imp : m.imports()) {
                imported.add(imp.module());
            }
            return Answer.of(List.copyOf(imported));
        }
    }

    /**
     * The type names a module exposes.
     *
     * <p>Its own question, not a read of the module. Everything that resolves a name against another
     * module asks this, and a module changes far more often than its {@code exposing} line does —
     * reading the whole module here would mean a new behavior in one module rebuilding every module
     * that imports a type from it.
     */
    /**
     * The library names a module's imports let it write bare, keyed by the bare spelling.
     *
     * <p>Read from the module as its source declared it, because {@link Exposed} drops the import
     * lines once it has checked them: what they brought in outlives the lines themselves.
     */
    public record LibraryNames(String name) implements Key<Map<String, String>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, String>> compute(Db db) {
            Layout.Of layout = db.ask(new Layout()).value();
            if (layout == null) {
                return Answer.absent();
            }
            String id = layout.idOfModule().get(name);
            if (id == null) {
                return Answer.of(Map.of());   // read from the path, where the lines are already gone
            }
            Answer<CstFrontend.Parsed> parsed = db.ask(new Parsed(id));
            if (!parsed.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(Ordered.map(Exposing.read(parsed.value().module()).exposed()));
            } catch (CompileException e) {
                return Answer.absent(e);   // reported where the import is checked
            }
        }
    }

    public record Exposes(String name) implements Key<Set<String>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Set<String>> compute(Db db) {
            Ast.Module m = db.ask(new Available(name)).value();
            return Answer.of(m == null ? Set.of()
                    : souther.compiler.check.Registry.baseNames(m.exposing()));
        }
    }

    /**
     * The behavior names a module declares.
     *
     * <p>Read where a {@code >->} stage or a {@code depends on} is resolved, which is why it asks
     * {@link Exposed} rather than {@link Available}: binding a module's own stages is what
     * {@link Available} does, and a module whose stage names another module's behavior would
     * otherwise be waiting on itself. Nothing between the two changes which behaviors a module
     * declares.
     */
    public record Behaviors(String name) implements Key<Set<String>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Set<String>> compute(Db db) {
            Ast.Module m = db.ask(new Exposed(name)).value();
            if (m == null) {
                FromPath.Of path = db.ask(new FromPath()).value();
                m = path == null ? null : path.modules().get(name);
            }
            return m == null ? Answer.absent() : Answer.of(Names.behaviorNames(m));
        }
    }

    /**
     * The module a source declares, when it is the source that declares it. A second source naming
     * the same module is the one reported: the first has a claim on the name, and the message
     * belongs on the file the author would have to change.
     */
    public record Declares(String id) implements Key<String> {
        @Override
        public String sourceId() {
            return id;
        }

        @Override
        public Answer<String> compute(Db db) {
            Answer<CstFrontend.Parsed> parsed = db.ask(new Parsed(id));
            Layout.Of layout = db.ask(new Layout()).value();
            if (!parsed.present() || layout == null
                    || parsed.value().module().exampleFileTarget() != null) {
                return Answer.absent();
            }
            Ast.Module m = parsed.value().module();
            if (id.equals(layout.idOfModule().get(m.name()))) {
                return Answer.of(m.name());
            }
            return Answer.absent(Report.raised(
                    Diagnostic.of(null, "check.module.duplicate").title("check.module.title")
                            .at(m.pos()).args(m.name()).build(),
                    "duplicate module `" + m.name() + "`"));
        }
    }

    /**
     * Which source each of a module's example rows was written in, in the order the rows appear.
     * A row that came from an {@code examples for} file is reported on that file, not on the module
     * it contributes to.
     */
    public record ExampleOrigins(String name) implements Key<List<String>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<List<String>> compute(Db db) {
            Layout.Of layout = db.ask(new Layout()).value();
            if (layout == null) {
                return Answer.of(List.of());
            }
            String own = layout.idOfModule().get(name);
            List<String> origins = new ArrayList<>();
            if (own != null) {
                CstFrontend.Parsed parsed = db.ask(new Parsed(own)).value();
                if (parsed != null) {
                    for (int i = 0; i < parsed.module().examples().size(); i++) {
                        origins.add(own);
                    }
                }
            }
            for (String id : layout.exampleFilesOf().getOrDefault(name, List.of())) {
                CstFrontend.Parsed file = db.ask(new Parsed(id)).value();
                if (file == null) {
                    continue;
                }
                for (int i = 0; i < file.module().examples().size(); i++) {
                    origins.add(id);
                }
            }
            return Answer.of(List.copyOf(origins));
        }
    }

    /**
     * Whether an {@code examples for} file has a module to attach to. The rows contribute to a
     * module this compilation does not have, so there is nothing to run them against.
     */
    public record AttachedTo(String id) implements Key<String> {
        @Override
        public String sourceId() {
            return id;
        }

        @Override
        public Answer<String> compute(Db db) {
            Layout.Of layout = db.ask(new Layout()).value();
            if (layout == null) {
                return Answer.absent();
            }
            String target = layout.exampleFileTargets().get(id);
            if (target == null) {
                return Answer.absent();   // not an `examples for` file
            }
            if (layout.idOfModule().containsKey(target)) {
                return Answer.of(target);
            }
            SourcePos pos = db.ask(new Parsed(id)).present()
                    ? db.ask(new Parsed(id)).value().module().pos() : null;
            return Answer.absent(Report.raised(
                    Diagnostic.of("E1907", "check.example.notarget").title("check.example.title")
                            .at(pos).args(target).build(),
                    "an `examples for " + target + "` file names a module that is not being compiled"));
        }
    }

    /**
     * A source module that also exists on the path. Which one an import means would be decided by
     * nothing the author wrote, and the two would be different types under one name — the same
     * reason two sources may not share a name.
     */
    public record ShadowsPath(String name) implements Key<Boolean> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Boolean> compute(Db db) {
            Layout.Of layout = db.ask(new Layout()).value();
            ModulePath path = db.ask(new Path()).value();
            if (layout == null || path == null || !layout.idOfModule().containsKey(name)) {
                return Answer.of(Boolean.FALSE);
            }
            if (PublishedModule.read(name, path.declarations()) == null) {
                return Answer.of(Boolean.FALSE);
            }
            return Answer.absent(Report.raised(
                    Diagnostic.of(null, "check.module.shadowspath").title("check.module.title")
                            .args(name).hint("check.module.shadowspath.hint", name).build(),
                    "module `" + name + "` is compiled here and is also on the path"));
        }
    }

    /** Every module name this compilation knows — declared by a source or read off the path. */
    public record ModuleNames() implements Key<Set<String>> {
        @Override
        public Answer<Set<String>> compute(Db db) {
            Layout.Of layout = db.ask(new Layout()).value();
            FromPath.Of path = db.ask(new FromPath()).value();
            Set<String> names = new LinkedHashSet<>();
            if (layout != null) {
                names.addAll(layout.idOfModule().keySet());
            }
            if (path != null) {
                names.addAll(path.modules().keySet());
            }
            return Answer.of(Ordered.set(names));
        }
    }

    /** The names a source module declares — every module this compilation could compile. */
    public record Declared() implements Key<List<String>> {
        @Override
        public Answer<List<String>> compute(Db db) {
            Layout.Of layout = db.ask(new Layout()).value();
            return layout == null ? Answer.of(List.of())
                    : Answer.of(List.copyOf(layout.idOfModule().keySet()));
        }
    }

    /**
     * Every module name {@code m} names: the ones it imports, the qualifier of every type it writes
     * with one, and the qualifier of every behavior it names that way. Neither kind of qualified
     * reference needs an import line, so reading only the import lines would leave a module it
     * reaches unread.
     */
    static Set<String> reaches(Ast.Module m) {
        Set<String> names = new LinkedHashSet<>();
        Map<String, String> aliases = new HashMap<>();
        for (Ast.Import imp : m.imports()) {
            names.add(imp.module());
            if (imp.alias() != null) {
                aliases.put(imp.alias(), imp.module());
            }
        }
        List<String> written = new ArrayList<>();
        for (Ast.TypeRef ref : Names.typeRefs(m)) {
            written.add(ref.name());
        }
        for (Ast.BehaviorDef b : m.behaviors()) {
            List<Ast.Var> named = switch (b) {
                case Ast.PipeBehavior pipe -> pipe.stages();
                case Ast.SpecBehavior spec -> spec.dependsOn();
            };
            for (Ast.Var ref : named) {
                written.add(ref.name());
            }
        }
        for (String name : written) {
            int dot = name.lastIndexOf('.');
            if (dot > 0) {
                String qualifier = name.substring(0, dot);
                names.add(aliases.getOrDefault(qualifier, qualifier));
            }
        }
        names.remove(m.name());
        return names;
    }

    /** A module in the reserved namespace, or one named like a standard-library qualifier — or null
     * when the name is the module's to take. */
    static Report reservedNamespace(String name, SourcePos pos) {
        if (name.equals(RESERVED) || name.startsWith(RESERVED + ".")) {
            return Report.raised(
                    Diagnostic.of(null, "check.module.reserved").title("check.module.title")
                            .at(pos).args(name).build(),
                    "module `" + name + "` is in the reserved `" + RESERVED + "` namespace: the"
                            + " compiler ships souther.string / souther.list / souther.map /"
                            + " souther.bool, and a user module cannot take a reserved name.");
        }
        // The short qualifiers are how the standard library is reached (`List.map`, `import
        // String`); a user module by one of these names would shadow the library and could not be
        // imported.
        if (Prelude.isQualifier(name)) {
            return Report.raised(
                    Diagnostic.of(null, "check.module.qualifier").title("check.module.title")
                            .at(pos).args(name).build(),
                    "module `" + name + "` uses a name reserved for the standard-library qualifier `"
                            + name + "` (as in `" + name + ".…` / `import " + name + " { … }`); pick"
                            + " another module name.");
        }
        return null;
    }
}
