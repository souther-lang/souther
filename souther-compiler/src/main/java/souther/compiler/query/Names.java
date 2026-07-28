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
                Ast.Module m = db.ask(new Front.Available(moduleName)).value();
                // `exposing` is written in the source and no pass rewrites it, so which stage this
                // registry reads makes no difference to the answer.
                return m == null ? Set.of() : Registry.baseNames(m.exposing());
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
                return exposed;
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
            Answer<Ast.Module> m = db.ask(new Front.Available(name));
            if (!m.present()) {
                return Answer.absent(m.reports());
            }
            try {
                return Answer.of(TypeChecker.ownDefs(m.value()));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
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
                return Answer.absent(module.reports());
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
            for (Ast.Import imp : m.imports()) {
                if (broken != null && broken.contains(imp.module())) {
                    return Answer.absent();   // the file that will not parse reports its own error
                }
                Ast.Module src = db.ask(new Front.Available(imp.module())).value();
                if (src == null) {
                    return Answer.absent(unknownModule(imp));
                }
                if (!db.ask(new Declarations(imp.module())).present()) {
                    // The module is there but says nothing usable. Whatever is wrong with it is
                    // reported on its own source; repeating it here would send the author to a file
                    // that is fine.
                    return Answer.absent();
                }
                if (imp.alias() != null) {
                    Report clash = aliasTaken(imp, aliases, registry.moduleNames());
                    if (clash != null) {
                        return Answer.absent(clash);
                    }
                    aliases.put(imp.alias(), imp.module());
                }
                Map<String, Ast.Def> srcDefs = registry.declaredIn(imp.module());
                Set<String> exposed = registry.exposedBy(imp.module());
                for (String imported : imp.names()) {
                    if (!exposed.contains(imported)) {
                        return Answer.absent(Report.raised(
                                Diagnostic.of(null, "check.import.notexposed").title("check.module.title")
                                        .at(imp.pos()).args(imported, imp.module()).build(),
                                "`" + imported + "` is not exposed by `" + imp.module() + "`"));
                    }
                    if (!srcDefs.containsKey(imported)) {
                        // a behavior import is resolved separately; it is not a data Def, so it does
                        // not go into the symbols map.
                        if (behaviorNames(src).contains(imported)) {
                            continue;
                        }
                        return Answer.absent(Report.raised(
                                Diagnostic.of(null, "check.import.notdefined").title("check.module.title")
                                        .at(imp.pos()).args(imported, imp.module()).build(),
                                "`" + imported + "` is not defined in `" + imp.module() + "`"));
                    }
                    if (scope.put(imported, new TypeName(imp.module(), imported)) != null) {
                        return Answer.absent(importCollision(imported, imp,
                                ownNames.contains(imported) ? null : from.get(imported)));
                    }
                    from.put(imported, imp);
                }
            }
            return Answer.of(new Of(Ordered.map(scope), Ordered.map(aliases)));
        }
    }

    /** What names mean in a module, over declarations at {@code stage}. */
    static Answer<Symbols> symbols(Db db, String name, Stage stage) {
        Answer<Imports.Of> imports = db.ask(new Imports(name));
        if (!imports.present()) {
            return Answer.absent(imports.reports());
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
    public record Resolved(String name) implements Key<Ast.Module> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Ast.Module> compute(Db db) {
            Answer<Ast.Module> available = db.ask(new Front.Available(name));
            if (!available.present()) {
                return Answer.absent(available.reports());
            }
            // Resolution reads other modules' declarations as they were written, not as they will
            // be resolved: a name written there is that module's to resolve, and asking for its
            // resolved form here would be this module waiting on its own.
            Answer<Symbols> scope = symbols(db, name, Stage.AVAILABLE);
            if (!scope.present()) {
                return Answer.absent(scope.reports());
            }
            try {
                return Answer.of(Resolve.module(available.value(), scope.value()));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
        }
    }

    /**
     * Which modules take part in an import cycle, and the error to report at each. A cycle is
     * followed through imports and through qualified type references alike: a qualified reference
     * needs no import line, so reading only the import lines would let a cycle through unseen.
     */
    public record Cycles() implements Key<Map<String, Report>> {
        @Override
        public Answer<Map<String, Report>> compute(Db db) {
            List<String> declared = db.ask(new Front.Declared()).value();
            if (declared == null) {
                return Answer.of(Map.of());
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
            Set<String> done = new LinkedHashSet<>();
            Set<String> onStack = new LinkedHashSet<>();
            for (String name : declared) {
                visit(name, deps, done, onStack, found);
            }
            return Answer.of(Ordered.map(found));
        }

        private void visit(String name, Map<String, List<Dependency>> deps, Set<String> done,
                           Set<String> onStack, Map<String, Report> found) {
            if (done.contains(name) || !deps.containsKey(name)) {
                return;
            }
            onStack.add(name);
            for (Dependency dep : deps.get(name)) {
                if (onStack.contains(dep.module())) {
                    // the reference that closes the cycle is written here, so this is the file to
                    // quote
                    found.putIfAbsent(name, Report.raised(
                            Diagnostic.literal(dep.pos(), "E1501",
                                    "Cyclic module dependency detected."),
                            "Cyclic module dependency detected."));
                    continue;
                }
                visit(dep.module(), deps, done, onStack, found);
            }
            onStack.remove(name);
            done.add(name);
        }
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
