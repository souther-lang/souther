package souther.compiler.query;

import souther.compiler.Prelude;
import souther.compiler.ast.Ast;
import souther.compiler.check.HelperInliner;
import souther.compiler.check.Registry;
import souther.compiler.check.Resolve;
import souther.compiler.check.Suggest;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeChecker;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.TypeName;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What the names in a module mean: which module a qualifier names, which declarations an import
 * brings in, and — once those are settled — the module with every written type name resolved to the
 * declaration it denotes.
 *
 * <p>Each of these is asked once per module and answered once. That is the point of putting them
 * here: {@link souther.compiler.check.Symbols} is built at several stages of a compile, and before
 * this every stage revalidated the same imports and rebuilt the same scope, so a bad import was
 * found two or three times and whichever came first decided what the author read.
 */
public final class Names {

    private Names() {}

    /** Which stage of a module's declarations a registry reads. The names a module declares are the
     * same at every stage; what changes is what each declaration holds. */
    public enum Stage { AVAILABLE, RESOLVED, DERIVED }

    /** A registry over this compilation, reading each module's declarations at {@code stage}. */
    public static Registry registry(Db db, Stage stage) {
        return new Registry() {
            @Override
            public Ast.Def declaration(TypeName named) {
                Answer<Ast.Def> def = switch (stage) {
                    case AVAILABLE -> db.ask(new Declaration(named));
                    case RESOLVED -> db.ask(new ResolvedDeclaration(named));
                    case DERIVED -> db.ask(new Shapes.DerivedDef(named));
                };
                return def.present() ? def.value() : null;
            }

            @Override
            public Map<String, Ast.Def> declaredIn(String moduleName) {
                Answer<Map<String, Ast.Def>> defs = switch (stage) {
                    case AVAILABLE -> db.ask(new Declarations(moduleName));
                    case RESOLVED -> db.ask(new ResolvedDeclarations(moduleName));
                    case DERIVED -> db.ask(new Shapes.DerivedDeclarations(moduleName));
                };
                return defs.present() ? defs.value() : Map.of();
            }

            @Override
            public Set<String> exposedBy(String moduleName) {
                // `exposing` is written in the source and no pass rewrites it, so which stage this
                // registry reads makes no difference to the answer.
                Set<String> exposed = db.ask(new Front.Exposes(moduleName)).value();
                return exposed == null ? Set.of() : exposed;
            }

            @Override
            public Set<String> moduleNames() {
                Set<String> names = db.ask(new Front.ModuleNames()).value();
                return names == null ? Set.of() : names;
            }
        };
    }

    /**
     * A source module with every name in the value namespace — a {@code >->} stage, a
     * {@code depends on} — resolved to the behavior it denotes, and the module a qualified one came
     * from recorded as an import.
     *
     * <p>A behavior's name is a member name in the generated class, so the bare form is what the
     * rest of the compiler reaches it by; the qualifier only says which module to take it from, which
     * is exactly what an import says. Both are in the answer: the resolved name says what the stage
     * means, and the synthesized import is how the borrowed signature and the injected field are
     * found.
     *
     * <p>A name that denotes no behavior is reported here, once, and denotes nothing from here on.
     * The answer is still present — a stage nobody declares is one definition's mistake, and the
     * definitions around it are checked as they would be without it. What must not happen, emitting
     * a module with a hole in it, is stopped by {@link Sound}.
     */
    public record Bound(String name) implements Key<Ast.Module> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Ast.Module> compute(Db db) {
            Answer<Ast.Module> exposed = db.ask(new Front.Exposed(name));
            if (!exposed.present()) {
                return Answer.absent();
            }
            Ast.Module m = exposed.value();
            Binding binding = new Binding(db, m);
            List<Ast.BehaviorDef> behaviors = new ArrayList<>();
            for (Ast.BehaviorDef b : m.behaviors()) {
                switch (b) {
                    case Ast.PipeBehavior pipe -> {
                        List<Ast.ValueRef> stages = new ArrayList<>();
                        for (Ast.ValueRef stage : pipe.stages()) {
                            stages.add(binding.stage(stage));
                        }
                        behaviors.add(new Ast.PipeBehavior(pipe.name(), stages, pipe.declaredOut(),
                                pipe.pos()));
                    }
                    case Ast.SpecBehavior spec -> {
                        List<Ast.ValueRef> dependsOn = new ArrayList<>();
                        for (Ast.ValueRef req : spec.dependsOn()) {
                            dependsOn.add(binding.required(req, spec.name()));
                        }
                        behaviors.add(new Ast.SpecBehavior(spec.name(), spec.params(), spec.ret(),
                                spec.constructs(), dependsOn, spec.pos()));
                    }
                }
            }
            Ast.Module bound = new Ast.Module(m.name(), m.exposing(), m.exposedOutputs(),
                    binding.imports(), m.defs(), behaviors, m.fns(), m.examples(), m.fakes(),
                    m.exampleFileTarget(), m.pos());
            return Answer.of(bound, binding.reports());
        }
    }

    /**
     * The behaviors a module can name without a qualifier: its own, and the ones its imports bring
     * in, each under the bare name it is reached by.
     *
     * <p>{@code whole} is false when an import could not be followed, so a name that is not here may
     * still have come from somewhere — the difference between "nothing declares this" and "this
     * compilation cannot say".
     */
    public record BehaviorsInScope(String name) implements Key<BehaviorsInScope.Of> {

        public record Of(Map<String, ValueName.Behavior> byName, boolean whole) {}

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Of> compute(Db db) {
            Ast.Module m = db.ask(new Front.Exposed(name)).value();
            if (m == null) {
                return Answer.absent();
            }
            Map<String, ValueName.Behavior> byName = new LinkedHashMap<>();
            for (String own : behaviorNames(m)) {
                byName.put(own, new ValueName.Behavior(name, own));
            }
            boolean whole = true;
            for (Ast.Import imp : m.imports()) {
                Answer<Set<String>> declared = db.ask(new Front.Behaviors(imp.module()));
                if (!declared.present()) {
                    whole = false;
                    continue;
                }
                for (String imported : imp.names()) {
                    if (declared.value().contains(imported)) {
                        // a name this module declares itself is the one it means
                        byName.putIfAbsent(imported,
                                new ValueName.Behavior(imp.module(), imported));
                    }
                }
            }
            return Answer.of(new Of(Ordered.map(byName), whole));
        }
    }

    /**
     * Resolving one module's behavior names: which behavior each stage and each {@code depends on}
     * denotes, and which imports naming them through a module asks for.
     */
    private static final class Binding {

        private final Db db;
        private final Ast.Module m;
        private final Map<String, String> qualifiers = new HashMap<>();
        private final Map<String, Set<String>> taken = new LinkedHashMap<>();  // module → its names
        private final Map<String, Set<String>> added = new LinkedHashMap<>();
        private final Map<String, SourcePos> at = new LinkedHashMap<>();
        private final List<Report> reports = new ArrayList<>();

        Binding(Db db, Ast.Module m) {
            this.db = db;
            this.m = m;
            for (Ast.Import imp : m.imports()) {
                if (imp.alias() != null) {
                    qualifiers.put(imp.alias(), imp.module());
                }
                taken.computeIfAbsent(imp.module(), k -> new LinkedHashSet<>()).addAll(imp.names());
            }
        }

        List<Report> reports() {
            return reports;
        }

        /** The module's imports, plus one for each module a qualified reference named. */
        List<Ast.Import> imports() {
            if (added.isEmpty()) {
                return m.imports();
            }
            List<Ast.Import> imports = new ArrayList<>(m.imports());
            for (Map.Entry<String, Set<String>> e : added.entrySet()) {
                imports.add(new Ast.Import(e.getKey(), null, List.copyOf(e.getValue()),
                        at.get(e.getKey())));
            }
            return imports;
        }

        /**
         * A {@code >->} stage. {@code X.decoder} / {@code X.encoder} name a codec, which is a
         * boundary edge rather than a behavior (spec 14.1) — said here, where the question is what
         * the name denotes, so nothing further down has a spelling to test for it.
         */
        Ast.ValueRef stage(Ast.ValueRef ref) {
            String written = ref.written();
            int dot = written.lastIndexOf('.');
            // Only a qualified one: `decoder` on its own is an ordinary name, and a module may
            // declare a behavior by it.
            String last = dot < 0 ? "" : written.substring(dot + 1);
            if (last.equals("decoder") || last.equals("encoder")) {
                return nothing(ref, Report.raised(
                        Diagnostic.of(null, "check.pipe.boundary").title("check.pipe.title")
                                .at(ref.pos()).build(),
                        "decode/encode are boundary edges, not pipeline stages; `>->` composes"
                                + " behaviors only (spec 14.1)"));
            }
            return behavior(ref, this::unknownBehavior);
        }

        /**
         * A name a {@code depends on} clause writes. It must name an injection target, and whether the
         * behavior it names is one is the check's to say (E1607); that nothing declares the name at
         * all is settled here, in the same message, because it is the same question — what does this
         * name denote — asked of a clause rather than of a stage.
         */
        Ast.ValueRef required(Ast.ValueRef ref, String by) {
            return behavior(ref, (name, candidates) -> Report.raised(
                    Diagnostic.of("E1607", "e1607.unknown").title("e1607.title")
                            .at(name.pos(), name.written().length()).args(by, name.written())
                            .suggestion(Suggest.candidate(name.written(), candidates))
                            .hint("e1607.unknown.hint").build(),
                    "`behavior " + by + "` declares `depends on " + name.written() + "`, which is not a"
                            + " behavior in scope" + Suggest.hint(name.written(), candidates)));
        }

        /** A name that must denote a behavior, with what to say when none does. */
        private Ast.ValueRef behavior(Ast.ValueRef ref, Unknown unknown) {
            String written = ref.written();
            int dot = written.lastIndexOf('.');
            if (dot < 0) {
                return bare(ref, written, unknown);
            }
            String bare = written.substring(dot + 1);
            String qualifier = written.substring(0, dot);
            if (Prelude.isQualifier(qualifier)) {
                // a standard-library qualifier names a function, and a function is not a behavior
                return nothing(ref, unknown.report(ref, Set.of()));
            }
            String target = qualifiers.getOrDefault(qualifier, qualifier);
            if (target.equals(m.name())) {
                return bare(ref, bare, unknown);   // this module, named through itself
            }
            if (!db.ask(new Front.ModuleNames()).value().contains(target)) {
                return nothing(ref, Report.raised(
                        Diagnostic.of(null, "check.qualified.unknownmodule").title("check.module.title")
                                .at(ref.pos()).args(qualifier, bare).build(),
                        "no module named `" + qualifier + "`"));
            }
            Answer<Set<String>> declared = db.ask(new Front.Behaviors(target));
            if (!declared.present()) {
                // The module is one this compilation has and could not read. What is wrong with it
                // is reported on its own source; saying anything here sends the author to a file
                // that is fine.
                return ref.denoting(new ValueName.Unresolved(written));
            }
            if (!declared.value().contains(bare)) {
                return nothing(ref, unknown.report(ref, declared.value()));
            }
            if (!taken.getOrDefault(target, Set.of()).contains(bare)) {
                added.computeIfAbsent(target, k -> new LinkedHashSet<>()).add(bare);
                at.putIfAbsent(target, ref.pos());
            }
            return ref.denoting(new ValueName.Behavior(target, bare));
        }

        /** A bare name: this module's own behavior, or one an import brought in. */
        private Ast.ValueRef bare(Ast.ValueRef ref, String written, Unknown unknown) {
            BehaviorsInScope.Of scope = db.ask(new BehaviorsInScope(m.name())).value();
            if (scope == null) {
                return ref.denoting(new ValueName.Unresolved(written));
            }
            ValueName.Behavior named = scope.byName().get(written);
            if (named != null) {
                return ref.denoting(named);
            }
            if (!scope.whole()) {
                // An import that could not be followed may have been where this name came from.
                // Whatever is wrong with that module is reported there.
                return ref.denoting(new ValueName.Unresolved(written));
            }
            return nothing(ref, unknown.report(ref, scope.byName().keySet()));
        }

        /** What to say about a name no behavior answers to, given the names that were reachable. */
        private interface Unknown {
            Report report(Ast.ValueRef ref, Set<String> candidates);
        }

        private Report unknownBehavior(Ast.ValueRef ref, Set<String> candidates) {
            String written = ref.written();
            return Report.raised(
                    Diagnostic.of(null, "check.unknown.behavior.msg").title("check.unknown.title")
                            .at(ref.pos(), written.length()).args(written)
                            .suggestion(Suggest.candidate(written, candidates)).build(),
                    "unknown behavior `" + written + "` in pipeline"
                            + Suggest.hint(written, candidates));
        }

        /** Records why a name denotes nothing, and gives it the name that says so. */
        private Ast.ValueRef nothing(Ast.ValueRef ref, Report report) {
            reports.add(report);
            return ref.denoting(new ValueName.Unresolved(ref.written()));
        }
    }

    /** What a module declares, by the name written there — checked once, here, because the names
     * are the same at every stage and every later registry reads them through this. */
    public record Declarations(String name) implements Key<Map<String, Ast.Def>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, Ast.Def>> compute(Db db) {
            if (cyclic(db, name)) {
                // What this module declares depends on the module it names, which depends on this
                // one. Reported by InCycle; nothing below here can be answered, and going on would
                // ask a question that is answering itself.
                return Answer.absent();
            }
            Answer<Ast.Module> m = db.ask(new Front.Available(name));
            if (!m.present()) {
                return Answer.absent();
            }
            // A declaration the module may not have is reported and left out; the ones it may have
            // are what it declares. So a name written twice does not take every other name in the
            // file with it.
            TypeChecker.Declared declared = TypeChecker.declared(m.value());
            List<Report> reports = new ArrayList<>();
            for (CompileException rejected : declared.rejected()) {
                reports.addAll(Report.of(rejected));
            }
            return Answer.of(declared.defs(), reports);
        }
    }

    /**
     * Whether a module takes part in an import cycle — absent, with the error, when it does.
     *
     * <p>{@link Cycles} finds them all in one walk; this is where one module's share of that is
     * reported, so the error lands on the source that closes the cycle like any other.
     */
    public record InCycle(String name) implements Key<Boolean> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Boolean> compute(Db db) {
            Cycles.Of cycles = db.ask(new Cycles()).value();
            Report found = cycles == null ? null : cycles.reported().get(name);
            if (found != null) {
                return Answer.absent(found);
            }
            return cyclic(db, name) ? Answer.absent() : Answer.of(Boolean.FALSE);
        }
    }

    /**
     * One declaration, as the module wrote it.
     *
     * <p>Its own question, so that reading it is a dependency on it and not on everything declared
     * beside it. Whether the work behind it is done for one declaration or for the module is not
     * this key's business: what a reader depends on is the answer, and this answer says what one
     * declaration says.
     */
    public record Declaration(TypeName named) implements Key<Ast.Def> {
        @Override
        public String module() {
            return named.module();
        }

        @Override
        public Answer<Ast.Def> compute(Db db) {
            Answer<Map<String, Ast.Def>> defs = db.ask(new Declarations(named.module()));
            if (!defs.present()) {
                return Answer.absent();
            }
            Ast.Def def = defs.value().get(named.name());
            return def == null ? Answer.absent() : Answer.of(def);
        }
    }

    /** The same, with every written name in it resolved. */
    public record ResolvedDeclaration(TypeName named) implements Key<Ast.Def> {
        @Override
        public String module() {
            return named.module();
        }

        @Override
        public Answer<Ast.Def> compute(Db db) {
            Answer<Map<String, Ast.Def>> defs = db.ask(new ResolvedDeclarations(named.module()));
            if (!defs.present()) {
                return Answer.absent();
            }
            Ast.Def def = defs.value().get(named.name());
            return def == null ? Answer.absent() : Answer.of(def);
        }
    }

    /** The same declarations, with every written name in them resolved. */
    public record ResolvedDeclarations(String name) implements Key<Map<String, Ast.Def>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, Ast.Def>> compute(Db db) {
            Answer<Ast.Module> m = db.ask(new Resolved(name));
            return m.present() ? Answer.of(defsOf(m.value())) : Answer.absent();
        }
    }

    /** A module's definitions by name, taking the names as already checked. */
    static Map<String, Ast.Def> defsOf(Ast.Module m) {
        Map<String, Ast.Def> defs = new LinkedHashMap<>();
        for (Ast.Def def : m.defs()) {
            defs.putIfAbsent(def.name(), def);
        }
        return Ordered.map(defs);
    }

    /**
     * What each bare name means in a module: its own declarations plus the ones its imports bring
     * in, and which module each {@code import ... as} alias names.
     *
     * <p>Every import is validated here and nowhere else — that it names a module this compilation
     * has, that the module exposes what is asked for, that no two imports bring in the same name.
     */
    public record Imports(String name) implements Key<Imports.Of> {

        public record Of(Map<String, TypeName> scope, Map<String, String> aliases) {}

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Of> compute(Db db) {
            Answer<Ast.Module> module = db.ask(new Front.Available(name));
            if (!module.present()) {
                return Answer.absent();
            }
            Ast.Module m = module.value();
            Registry registry = registry(db, Stage.AVAILABLE);
            Map<String, TypeName> scope = new HashMap<>();
            for (String own : registry.declaredIn(name).keySet()) {
                scope.put(own, new TypeName(name, own));
            }
            Set<String> ownNames = Ordered.set(scope.keySet());
            // Which import brought each name in, so a second one naming it is reported against that
            // import rather than against a local definition the module may not have.
            Map<String, Ast.Import> from = new HashMap<>();
            Map<String, String> aliases = new HashMap<>();
            Set<String> broken = db.ask(new Front.Broken()).value();
            // An import line that is wrong is reported and skipped, and the ones that are fine still
            // bring in what they bring in. A half-typed import is as ordinary as a half-typed name,
            // and taking the whole scope away would leave every name in the file meaning nothing —
            // which is when an author most wants to be told what one means.
            List<Report> reports = new ArrayList<>();
            for (Ast.Import imp : m.imports()) {
                if (broken != null && broken.contains(imp.module())) {
                    nameless(scope, imp.names());
                    continue;   // the file that will not parse reports its own error
                }
                Ast.Module src = db.ask(new Front.Available(imp.module())).value();
                if (src == null || !db.ask(new Declarations(imp.module())).present()) {
                    // Not being part of this compilation and being part of it while saying nothing
                    // usable are different things, and only the first is the importer's business.
                    // Whatever is wrong with a module that is here is reported on its own source;
                    // saying it again here sends the author to a file that is fine.
                    if (!registry.moduleNames().contains(imp.module())) {
                        reports.add(unknownModule(imp));
                    }
                    nameless(scope, imp.names());
                    continue;
                }
                if (imp.alias() != null) {
                    Report clash = aliasTaken(imp, aliases, registry.moduleNames());
                    if (clash != null) {
                        reports.add(clash);
                        nameless(scope, imp.names());
                        continue;   // an alias that names two things names neither here
                    }
                    aliases.put(imp.alias(), imp.module());
                }
                Set<String> exposed = registry.exposedBy(imp.module());
                for (String imported : imp.names()) {
                    if (!exposed.contains(imported)) {
                        reports.add(Report.raised(
                                Diagnostic.of(null, "check.import.notexposed").title("check.module.title")
                                        .at(imp.pos()).args(imported, imp.module()).build(),
                                "`" + imported + "` is not exposed by `" + imp.module() + "`"));
                        nameless(scope, List.of(imported));
                        continue;
                    }
                    // asked one name at a time: what else that module declares is not what this
                    // import is about, and reading it would make this module depend on it
                    if (registry.declaration(new TypeName(imp.module(), imported)) == null) {
                        // a behavior import is resolved separately; it is not a data Def, so it does
                        // not go into the symbols map.
                        // a behavior import is resolved separately, and so is a value: neither is a
                        // data Def, so neither goes into the symbols map
                        if (behaviorNames(src).contains(imported) || valueNames(src).contains(imported)) {
                            continue;
                        }
                        reports.add(Report.raised(
                                Diagnostic.of(null, "check.import.notdefined").title("check.module.title")
                                        .at(imp.pos()).args(imported, imp.module()).build(),
                                "`" + imported + "` is not defined in `" + imp.module() + "`"));
                        nameless(scope, List.of(imported));
                        continue;
                    }
                    TypeName standingIn = scope.get(imported);
                    if (standingIn != null && !standingIn.isUnresolved()) {
                        reports.add(importCollision(imported, imp,
                                ownNames.contains(imported) ? null : from.get(imported)));
                        continue;   // the first claim on the name keeps it
                    }
                    // A name a failed import line only stood in for is not a claim on it: an import
                    // that can do the job takes it, and says nothing about the line that could not.
                    scope.put(imported, new TypeName(imp.module(), imported));
                    from.put(imported, imp);
                }
            }
            if (!reports.isEmpty()) {
                return Answer.of(new Of(Ordered.map(scope), Ordered.map(aliases)), reports);
            }
            return Answer.of(new Of(Ordered.map(scope), Ordered.map(aliases)));
        }
    }

    /**
     * Puts {@code names} in scope as names that denote nothing.
     *
     * <p>An import line that could not do its job was reported on that line. A name it was to bring
     * in is in scope all the same, denoting nothing — so a use of it takes the error type and says
     * nothing more. Leaving it out of scope instead would report an unknown type at every use, which
     * sends the author to a field when what is wrong is the import.
     */
    private static void nameless(Map<String, TypeName> scope, List<String> names) {
        for (String written : names) {
            scope.putIfAbsent(written, TypeName.unresolved(written));
        }
    }

    /** What names mean in a module, over declarations at {@code stage}. */
    static Answer<Symbols> symbols(Db db, String name, Stage stage) {
        Answer<Imports.Of> imports = db.ask(new Imports(name));
        if (!imports.present()) {
            return Answer.absent();
        }
        return Answer.of(Symbols.of(name, registry(db, stage), imports.value().scope(),
                imports.value().aliases()));
    }

    /** What names mean in a module before anything is derived from it — what {@link Resolved}
     * resolves against. */
    public record NameScope(String name) implements Key<Symbols> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Symbols> compute(Db db) {
            return symbols(db, name, Stage.RESOLVED);
        }
    }

    /**
     * The module with every written type name resolved to the declaration it denotes. A name that
     * denotes nothing is reported here, so nothing downstream ever reads an unresolved one.
     */
    public record Resolution(String name) implements Key<Resolve.Resolved> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Resolve.Resolved> compute(Db db) {
            Answer<Ast.Module> available = db.ask(new Front.Available(name));
            if (!available.present()) {
                return Answer.absent();
            }
            // Resolution reads other modules' declarations as they were written, not as they will
            // be resolved: a name written there is that module's to resolve, and asking for its
            // resolved form here would be this module waiting on its own.
            Answer<Symbols> scope = symbols(db, name, Stage.AVAILABLE);
            if (!scope.present()) {
                return Answer.absent();
            }
            Resolve.Resolved resolution;
            try {
                resolution = Resolve.resolving(available.value(), scope.value(),
                        reachableValues(db, available.value()));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
            // A name that denotes nothing is reported here and the tree carries on with the error
            // type in its place. The answer is present, so an editor can still say what the names
            // around the mistake mean; what must not happen — emitting a module with a hole in it —
            // is stopped where the module is checked.
            List<Report> reports = new ArrayList<>();
            for (CompileException unresolved : resolution.unresolved()) {
                reports.addAll(Report.of(unresolved));
            }
            return Answer.of(resolution, reports);
        }
    }

    /**
     * Whether everything the compiler worked out about a module's names came out.
     *
     * <p>One question, asked in one place, so that whether a module may be emitted does not become a
     * list of conditions appended to over time. Each of these has already said what was wrong where
     * it found it; this only asks whether any of them did.
     *
     * <p>It is transitive. A module built against one that was rejected is built against declarations
     * nothing will emit, so it cannot be emitted either — its classes would name a class that is not
     * there, and its examples would fail for a reason that is not its own. An import that could not be
     * followed counts the same way, whether or not anything was reported here about it. An import cycle
     * is settled before this recurses, so following imports terminates.
     */
    public record Sound(String name) implements Key<Boolean> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Boolean> compute(Db db) {
            List<Answer<?>> asked = List.of(
                    db.ask(new Front.Exposed(name)),
                    db.ask(new Front.ShadowsPath(name)),
                    db.ask(new InCycle(name)),
                    db.ask(new Bound(name)),
                    db.ask(new Declarations(name)),
                    db.ask(new Imports(name)),
                    db.ask(new Resolution(name)));
            for (Answer<?> answer : asked) {
                if (answer.hasError()) {
                    return Answer.of(Boolean.FALSE);
                }
            }
            // Whether anything was reported here is not the whole question. A name that denotes
            // nothing because the module it would have come from cannot be read is reported on that
            // module, and leaves a hole here that nothing said anything about — so the names are
            // asked as well as the reports.
            if (Boolean.TRUE.equals(db.ask(new Nameless(name)).value())) {
                return Answer.of(Boolean.FALSE);
            }
            Ast.Module m = db.ask(new Front.Available(name)).value();
            if (m != null) {
                for (Ast.Import imp : m.imports()) {
                    // An import that could not be followed at all — the module is not here, or the
                    // caller is holding its file back — leaves the names it was to bring denoting
                    // nothing, whether or not anything was reported here to say so.
                    if (!db.ask(new Front.Available(imp.module())).present()
                            || Boolean.FALSE.equals(db.ask(new Sound(imp.module())).value())) {
                        return Answer.of(Boolean.FALSE);
                    }
                }
            }
            return Answer.of(Boolean.TRUE);
        }
    }

    /**
     * Whether a module writes a name in the value namespace that denotes nothing.
     *
     * <p>Asked because a report is not the only way a hole gets there. A stage naming a module this
     * compilation has and cannot read is reported on that module — the author of this one has
     * nothing to fix — and this module is left with a composition that has no meaning, which nothing
     * here said. Emitting it would emit a call to a behavior that does not exist.
     */
    public record Nameless(String name) implements Key<Boolean> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Boolean> compute(Db db) {
            Ast.Module m = db.ask(new Bound(name)).value();
            if (m == null) {
                return Answer.of(Boolean.FALSE);   // there is no module here to have a hole in
            }
            for (Ast.BehaviorDef b : m.behaviors()) {
                List<Ast.ValueRef> named = switch (b) {
                    case Ast.PipeBehavior pipe -> pipe.stages();
                    case Ast.SpecBehavior spec -> spec.dependsOn();
                };
                for (Ast.ValueRef ref : named) {
                    if (ref.unresolved()) {
                        return Answer.of(Boolean.TRUE);
                    }
                }
            }
            return Answer.of(Boolean.FALSE);
        }
    }

    /** What a module's bodies can name without a binding: its own helpers, and every behavior it can
     * reach — its own and the ones its imports bring in. */
    private static Resolve.Values reachableValues(Db db, Ast.Module m) {
        // A behavior's `let` is not a helper: it implements the behavior, and the name reaches the
        // behavior. Asked the same way as HelperInliner.helpersOf, which decides what is expanded —
        // two answers to one question is how a name came to denote a helper here and a behavior
        // there.
        Set<String> helpers = new LinkedHashSet<>(HelperInliner.helpersOf(m).keySet());
        // A value another module publishes is named here bare, like one of this module's own: it is
        // substituted at the reference, so nothing else about it has to travel (ADR-0072).
        for (Ast.Import imp : m.imports()) {
            Ast.Module from = db.ask(new Front.Available(imp.module())).value();
            if (from == null) {
                continue;
            }
            helpers.addAll(Bodies.publishedValues(from, imp.names()).keySet());
        }
        BehaviorsInScope.Of behaviors = db.ask(new BehaviorsInScope(m.name())).value();
        return new Resolve.Values(m.name(), helpers,
                behaviors == null ? Map.of() : behaviors.byName());
    }

    /** The resolved module — {@link Resolution} without the record of how it got there. */
    public record Resolved(String name) implements Key<Ast.Module> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Ast.Module> compute(Db db) {
            Answer<Resolve.Resolved> resolution = db.ask(new Resolution(name));
            return resolution.present() ? Answer.of(resolution.value().module()) : Answer.absent();
        }
    }

    /**
     * What the name written at {@code offset} in a module's source denotes, or absent when nothing
     * there is a name of a declared type.
     *
     * <p>This is what an editor is asking when the cursor is on an identifier. It reads the answers
     * the resolve pass already gave, so a qualified reference names the module it names and not
     * whatever this module happens to declare by the same spelling.
     */
    public record DenotedAt(String name, SourcePos at) implements Key<Resolve.Denotation> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Resolve.Denotation> compute(Db db) {
            Answer<Resolve.Resolved> resolution = db.ask(new Resolution(name));
            if (!resolution.present()) {
                return Answer.absent();
            }
            Resolve.Denotation innermost = null;
            for (Resolve.Denotation d : resolution.value().denotations()) {
                if (!spans(d.pos(), d.written(), at)) {
                    continue;
                }
                // A container writes its element's name inside its own span, so the shortest match
                // is the one the cursor is actually on.
                if (innermost == null || d.written().length() < innermost.written().length()) {
                    innermost = d;
                }
            }
            return innermost == null ? Answer.absent() : Answer.of(innermost);
        }
    }

    /**
     * The type the cursor is on at {@code offset}: the one a name there denotes, or — when the
     * cursor is on a declaration's own name — that declaration.
     *
     * <p>One question, so an editor's go-to-definition, find-references and rename all agree about
     * what the cursor is on. They used to each decide for themselves, by spelling.
     */
    public record TypeAt(String name, SourcePos at) implements Key<TypeName> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<TypeName> compute(Db db) {
            Answer<Map<String, Ast.Def>> defs = db.ask(new Declarations(name));
            if (defs.present()) {
                for (Ast.Def def : defs.value().values()) {
                    if (spans(def.pos(), def.name(), at)) {
                        return Answer.of(new TypeName(name, def.name()));
                    }
                }
            }
            Resolve.Denotation denoted = db.ask(new DenotedAt(name, at)).value();
            return denoted == null ? Answer.absent() : Answer.of(denoted.denotes());
        }
    }

    /** Every place a module names {@code denoted}, wherever it was declared. */
    public record UsesOf(String name, TypeName denoted) implements Key<List<Resolve.Denotation>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<List<Resolve.Denotation>> compute(Db db) {
            Answer<Resolve.Resolved> resolution = db.ask(new Resolution(name));
            if (!resolution.present()) {
                return Answer.of(List.of());
            }
            List<Resolve.Denotation> uses = new ArrayList<>();
            for (Resolve.Denotation d : resolution.value().denotations()) {
                if (denoted.equals(d.denotes())) {
                    uses.add(d);
                }
            }
            return Answer.of(List.copyOf(uses));
        }
    }

    /**
     * What the name used as a value at {@code at} denotes, or absent when nothing there is one.
     *
     * <p>What {@link DenotedAt} answers for a type. An editor asking about a name in a body reads
     * the answer resolution already gave, so a binding is the binding it is and not whatever else
     * in the module happens to be spelled the same.
     */
    public record ValueDenotedAt(String name, SourcePos at) implements Key<Resolve.ValueUse> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Resolve.ValueUse> compute(Db db) {
            Answer<Resolve.Resolved> resolution = db.ask(new Resolution(name));
            if (!resolution.present()) {
                return Answer.absent();
            }
            for (Resolve.ValueUse use : resolution.value().values()) {
                if (spans(use.pos(), use.written(), at)) {
                    return Answer.of(use);
                }
            }
            return Answer.absent();
        }
    }

    /**
     * Where what {@code denoted} names is written: the {@code let} or {@code behavior} that declares
     * it, or the binding that introduced a local.
     */
    public record ValueDeclaredAt(ValueName denoted) implements Key<SourcePos> {
        @Override
        public String module() {
            return switch (denoted) {
                case ValueName.Helper h -> h.module();
                case ValueName.Behavior b -> b.module();
                case ValueName.Local _, ValueName.Stdlib _, ValueName.OfType _,
                        ValueName.Builtin _, ValueName.Unresolved _ -> null;
            };
        }

        @Override
        public Answer<SourcePos> compute(Db db) {
            if (denoted instanceof ValueName.Local local) {
                return local.binder() == null ? Answer.absent() : Answer.of(local.binder());
            }
            String in = module();
            if (in == null) {
                return Answer.absent();   // the library and the language declare their own names
            }
            Ast.Module m = db.ask(new Front.Available(in)).value();
            if (m == null) {
                return Answer.absent();
            }
            for (Ast.BehaviorDef b : m.behaviors()) {
                if (b.name().equals(denoted.name())) {
                    return Answer.of(b.pos());
                }
            }
            for (Ast.FnDef fn : m.fns()) {
                if (fn.name().equals(denoted.name())) {
                    return Answer.of(fn.pos());
                }
            }
            return Answer.absent();
        }
    }

    /** Whether the name {@code written} starting at {@code start} covers {@code at}. A name is one
     * line's worth of text, so a position on another line is not on it. */
    static boolean spans(SourcePos start, String written, SourcePos at) {
        return start != null && at != null && start.line() == at.line()
                && at.column() >= start.column()
                && at.column() <= start.column() + written.length();
    }
    public record DeclaredAt(TypeName denoted) implements Key<SourcePos> {
        @Override
        public String module() {
            return denoted.module();
        }

        @Override
        public Answer<SourcePos> compute(Db db) {
            Answer<Map<String, Ast.Def>> defs = db.ask(new Declarations(denoted.module()));
            if (!defs.present()) {
                return Answer.absent();
            }
            Ast.Def def = defs.value().get(denoted.name());
            return def == null || def.pos() == null ? Answer.absent() : Answer.of(def.pos());
        }
    }

    /**
     * Which modules take part in an import cycle, and the error to report at each. A cycle is
     * followed through imports and through qualified type references alike: a qualified reference
     * needs no import line, so reading only the import lines would let a cycle through unseen.
     */
    public record Cycles() implements Key<Cycles.Of> {

        /**
         * @param reported the error for each module a cycle was closed at — one per cycle, on the
         *                 source that wrote the reference that closes it
         * @param members every module taking part in one, which is more: the error belongs to one
         *                of them, but none of them can be compiled
         */
        public record Of(Map<String, Report> reported, Set<String> members) {}

        @Override
        public Answer<Of> compute(Db db) {
            List<String> declared = db.ask(new Front.Declared()).value();
            if (declared == null) {
                return Answer.of(new Of(Map.of(), Set.of()));
            }
            Set<String> modules = db.ask(new Front.ModuleNames()).value();
            Map<String, List<Dependency>> deps = new LinkedHashMap<>();
            for (String name : declared) {
                Ast.Module m = db.ask(new Front.Available(name)).value();
                if (m != null) {
                    deps.put(name, dependencies(m, modules));
                }
            }
            Map<String, Report> found = new LinkedHashMap<>();
            Set<String> members = new LinkedHashSet<>();
            Set<String> done = new LinkedHashSet<>();
            List<String> stack = new ArrayList<>();
            for (String name : declared) {
                visit(name, deps, done, stack, found, members);
            }
            return Answer.of(new Of(Ordered.map(found), Ordered.set(members)));
        }

        private void visit(String name, Map<String, List<Dependency>> deps, Set<String> done,
                           List<String> stack, Map<String, Report> found, Set<String> members) {
            if (done.contains(name) || !deps.containsKey(name)) {
                return;
            }
            stack.add(name);
            for (Dependency dep : deps.get(name)) {
                int closes = stack.indexOf(dep.module());
                if (closes >= 0) {
                    // The reference that closes the cycle is written here, so this is the file to
                    // quote. Everything from the module it names round to this one is in the cycle,
                    // and none of them can be compiled — each needs an answer from the next.
                    found.putIfAbsent(name, Report.raised(
                            Diagnostic.literal(dep.pos(), "E1501",
                                    "Cyclic module dependency detected."),
                            "Cyclic module dependency detected."));
                    members.addAll(stack.subList(closes, stack.size()));
                    continue;
                }
                visit(dep.module(), deps, done, stack, found, members);
            }
            stack.remove(stack.size() - 1);
            done.add(name);
        }
    }

    /** Whether {@code name} takes part in an import cycle, so nothing about it can be worked out. */
    static boolean cyclic(Db db, String name) {
        Cycles.Of cycles = db.ask(new Cycles()).value();
        return cycles != null && cycles.members().contains(name);
    }

    /** One module reaching another, and where it does so. */
    private record Dependency(String module, SourcePos pos) {}

    private static List<Dependency> dependencies(Ast.Module m, Set<String> modules) {
        List<Dependency> deps = new ArrayList<>();
        Map<String, String> qualifiers = new HashMap<>();
        for (Ast.Import imp : m.imports()) {
            deps.add(new Dependency(imp.module(), imp.pos()));
            if (imp.alias() != null) {
                qualifiers.put(imp.alias(), imp.module());
            }
        }
        for (Ast.TypeRef ref : typeRefs(m)) {
            int dot = ref.name().lastIndexOf('.');
            if (dot < 0) {
                continue;
            }
            String qualifier = ref.name().substring(0, dot);
            String target = qualifiers.getOrDefault(qualifier, qualifier);
            if (modules.contains(target) && !target.equals(m.name())) {
                deps.add(new Dependency(target, ref.pos()));
            }
        }
        return deps;
    }

    static Set<String> behaviorNames(Ast.Module m) {
        Set<String> names = new LinkedHashSet<>();
        for (Ast.BehaviorDef b : m.behaviors()) {
            names.add(b.name());
        }
        return names;
    }

    /** The values a module declares — a {@code let} with no parameter list. Like a behavior, one is
     * a name in the value namespace and not a data, so an import of it resolves elsewhere. */
    static Set<String> valueNames(Ast.Module m) {
        Set<String> behaviors = behaviorNames(m);
        Set<String> names = new LinkedHashSet<>();
        for (Ast.FnDef fn : m.fns()) {
            if (fn.params().isEmpty() && !behaviors.contains(fn.name())) {
                names.add(fn.name());
            }
        }
        return names;
    }

    static Report unknownModule(Ast.Import imp) {
        return Report.raised(
                Diagnostic.of(null, "check.import.unknownmodule").title("check.module.title")
                        .at(imp.pos()).args(imp.module()).build(),
                "unknown module `" + imp.module() + "`");
    }

    /**
     * An alias must be a qualifier nothing else already is: another alias, a module in this
     * compilation, or a standard-library qualifier. Left to win silently it would take over what
     * {@code List.map} or {@code billing.Amount} means here.
     */
    private static Report aliasTaken(Ast.Import imp, Map<String, String> aliases,
                                     Set<String> modules) {
        String taken = aliases.containsKey(imp.alias()) ? aliases.get(imp.alias())
                : modules.contains(imp.alias()) ? imp.alias()
                : Prelude.isQualifier(imp.alias()) ? "souther" : null;
        if (taken == null) {
            return null;
        }
        return Report.raised(
                Diagnostic.of(null, "check.import.aliastaken").title("check.module.title")
                        .at(imp.pos()).args(imp.alias(), taken)
                        .hint("check.import.aliastaken.hint").build(),
                "the alias `" + imp.alias() + "` is already how `" + taken + "` is named here");
    }

    /**
     * The name arrived twice. {@code earlier} is the import that already brought it in, or null when
     * the module defines it itself. Either way the way out is inside the module: keep at most one of
     * them bare and name the other through its module.
     */
    private static Report importCollision(String name, Ast.Import imp, Ast.Import earlier) {
        if (earlier == null) {
            return Report.raised(
                    Diagnostic.of(null, "check.import.conflict").title("check.module.title")
                            .at(imp.pos()).args(name).hint("check.import.conflict.hint").build(),
                    "imported `" + name + "` conflicts with a local definition");
        }
        Diagnostic.Builder b = Diagnostic.of(null, "check.import.duplicate")
                .title("check.module.title").at(imp.pos()).args(name, earlier.module(), imp.module())
                .secondary(Region.point(earlier.pos()), "check.import.duplicate.first", name,
                        earlier.module());
        return Report.raised(
                (earlier.module().equals(imp.module())
                        ? b.hint("check.import.duplicate.same.hint")
                        : b.hint("check.import.duplicate.hint", name, imp.module())).build(),
                "`" + name + "` is imported from both `" + earlier.module() + "` and `"
                        + imp.module() + "`; one name cannot stand for two types");
    }

    /** Every type written in {@code m}: its data's fields, and its behaviors' and fns' signatures. */
    static List<Ast.TypeRef> typeRefs(Ast.Module m) {
        List<Ast.TypeRef> refs = new ArrayList<>();
        for (Ast.Def def : m.defs()) {
            if (def instanceof Ast.Data d) {
                for (Ast.Field f : d.fields()) {
                    collectTypeRefs(f.type(), refs);
                }
            }
        }
        for (Ast.BehaviorDef b : m.behaviors()) {
            if (b instanceof Ast.SpecBehavior spec) {
                for (Ast.Param p : spec.params()) {
                    collectRetType(p.type(), refs);
                }
                collectRetType(spec.ret(), refs);
            } else if (b instanceof Ast.PipeBehavior pipe) {
                collectRetType(pipe.declaredOut(), refs);
            }
        }
        for (Ast.FnDef fn : m.fns()) {
            for (Ast.FnParam p : fn.params()) {
                if (p.type() instanceof Ast.RetType rt) {
                    collectRetType(rt, refs);
                } else if (p.type() instanceof Ast.FnType ft) {
                    ft.params().forEach(pt -> collectRetType(pt, refs));
                    collectRetType(ft.result(), refs);
                }
            }
            collectRetType(fn.declaredReturn(), refs);
        }
        return refs;
    }

    private static void collectRetType(Ast.RetType ret, List<Ast.TypeRef> refs) {
        if (ret != null) {
            ret.cases().forEach(c -> collectTypeRefs(c, refs));
        }
    }

    private static void collectTypeRefs(Ast.TypeRef ref, List<Ast.TypeRef> refs) {
        if (ref == null) {
            return;
        }
        if (ref.name() != null) {
            refs.add(ref);
        }
        collectTypeRefs(ref.arg(), refs);
        if (ref.tupleElems() != null) {
            ref.tupleElems().forEach(e -> collectTypeRefs(e, refs));
        }
    }
}
