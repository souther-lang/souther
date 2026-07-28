package souther.compiler.query;

import souther.compiler.Prelude;
import souther.compiler.ast.Ast;
import souther.compiler.check.Registry;
import souther.compiler.check.Resolve;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeChecker;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.TypeName;

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
     * A source module with every qualified behavior reference — a {@code >->} stage or a
     * {@code requires} naming another module's behavior — rewritten to the bare name, and the module
     * it came from recorded as an import.
     *
     * <p>A behavior's name is a member name in the generated class, so the bare form is what the
     * rest of the compiler needs; the qualifier only says which module to take it from, which is
     * exactly what an import says.
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
            Set<String> modules = db.ask(new Front.ModuleNames()).value();
            Ast.Module m = exposed.value();
            List<Report> reports = new ArrayList<>();
            Map<String, String> qualifiers = new HashMap<>();
            for (Ast.Import imp : m.imports()) {
                if (imp.alias() != null) {
                    qualifiers.put(imp.alias(), imp.module());
                }
            }
            Map<String, Set<String>> taken = new LinkedHashMap<>();   // module → names it brings
            for (Ast.Import imp : m.imports()) {
                taken.computeIfAbsent(imp.module(), k -> new LinkedHashSet<>()).addAll(imp.names());
            }
            Map<String, Set<String>> added = new LinkedHashMap<>();
            Map<String, SourcePos> at = new LinkedHashMap<>();
            List<Ast.BehaviorDef> behaviors = new ArrayList<>();
            boolean rewrote = false;
            for (Ast.BehaviorDef b : m.behaviors()) {
                switch (b) {
                    case Ast.PipeBehavior pipe -> {
                        List<String> stages = new ArrayList<>();
                        for (String stage : pipe.stages()) {
                            stages.add(bind(stage, qualifiers, modules, m, pipe.pos(), taken, added,
                                    at, reports));
                        }
                        rewrote |= !stages.equals(pipe.stages());
                        behaviors.add(new Ast.PipeBehavior(pipe.name(), stages, pipe.declaredOut(),
                                pipe.pos()));
                    }
                    case Ast.SpecBehavior spec -> {
                        List<String> requires = new ArrayList<>();
                        for (String req : spec.requires()) {
                            requires.add(bind(req, qualifiers, modules, m, spec.pos(), taken, added,
                                    at, reports));
                        }
                        rewrote |= !requires.equals(spec.requires());
                        behaviors.add(new Ast.SpecBehavior(spec.name(), spec.params(), spec.ret(),
                                spec.constructs(), requires, spec.pos()));
                    }
                }
            }
            if (!reports.isEmpty()) {
                return Answer.absent(reports);
            }
            if (!rewrote) {
                return Answer.of(m);
            }
            List<Ast.Import> imports = new ArrayList<>(m.imports());
            for (Map.Entry<String, Set<String>> e : added.entrySet()) {
                imports.add(new Ast.Import(e.getKey(), null, List.copyOf(e.getValue()),
                        at.get(e.getKey())));
            }
            return Answer.of(new Ast.Module(m.name(), m.exposing(), m.exposedOutputs(), imports,
                    m.defs(), behaviors, m.fns(), m.examples(), m.fakes(), m.exampleFileTarget(),
                    m.pos()));
        }

        /** One written behavior name: the bare form it binds to, collecting the import it needs. */
        private String bind(String written, Map<String, String> qualifiers, Set<String> modules,
                            Ast.Module m, SourcePos pos, Map<String, Set<String>> taken,
                            Map<String, Set<String>> added, Map<String, SourcePos> at,
                            List<Report> reports) {
            int dot = written.lastIndexOf('.');
            if (dot < 0) {
                return written;
            }
            String bare = written.substring(dot + 1);
            // `X.decoder` / `X.encoder` name a codec, not a behavior of a module called X — a stage
            // that writes one gets its own answer, which reading it as an import would hide, and
            // would hide the more so where a module happens to be named like the type.
            if (bare.equals("decoder") || bare.equals("encoder")) {
                return written;
            }
            String qualifier = written.substring(0, dot);
            if (Prelude.isQualifier(qualifier)) {
                return written;   // a standard-library qualifier: a function, not a behavior
            }
            String target = qualifiers.getOrDefault(qualifier, qualifier);
            if (target.equals(m.name())) {
                return bare;      // this module, named through itself
            }
            if (!modules.contains(target)) {
                reports.add(Report.raised(
                        Diagnostic.of(null, "check.qualified.unknownmodule").title("check.module.title")
                                .at(pos).args(qualifier, bare).build(),
                        "no module named `" + qualifier + "`"));
                return bare;
            }
            if (!taken.getOrDefault(target, Set.of()).contains(bare)) {
                added.computeIfAbsent(target, k -> new LinkedHashSet<>()).add(bare);
                at.putIfAbsent(target, pos);
            }
            return bare;
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
                if (src == null) {
                    reports.add(unknownModule(imp));
                    nameless(scope, imp.names());
                    continue;
                }
                if (!db.ask(new Declarations(imp.module())).present()) {
                    // The module is there but says nothing usable. Whatever is wrong with it is
                    // reported on its own source; repeating it here would send the author to a file
                    // that is fine.
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
                Map<String, Ast.Def> srcDefs = registry.declaredIn(imp.module());
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
                    if (!srcDefs.containsKey(imported)) {
                        // a behavior import is resolved separately; it is not a data Def, so it does
                        // not go into the symbols map.
                        if (behaviorNames(src).contains(imported)) {
                            continue;
                        }
                        reports.add(Report.raised(
                                Diagnostic.of(null, "check.import.notdefined").title("check.module.title")
                                        .at(imp.pos()).args(imported, imp.module()).build(),
                                "`" + imported + "` is not defined in `" + imp.module() + "`"));
                        nameless(scope, List.of(imported));
                        continue;
                    }
                    if (scope.containsKey(imported)) {
                        reports.add(importCollision(imported, imp,
                                ownNames.contains(imported) ? null : from.get(imported)));
                        continue;   // the first claim on the name keeps it
                    }
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
                resolution = Resolve.resolving(available.value(), scope.value());
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
