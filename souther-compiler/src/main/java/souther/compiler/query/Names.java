package souther.compiler.query;

import souther.compiler.check.Prelude;
import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.ast.WrittenName;
import souther.compiler.check.DeclaredNames;
import souther.compiler.check.HelperInliner;
import souther.compiler.check.Registry;
import souther.compiler.check.Resolve;
import souther.compiler.check.Suggest;
import souther.compiler.check.SyntaxSymbols;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeChecker;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.DeclarationMessage;
import souther.compiler.diag.msg.DataMessage;
import souther.compiler.diag.msg.NameMessage;
import souther.compiler.diag.msg.BehaviorMessage;
import souther.compiler.diag.msg.ModuleMessage;
import souther.compiler.diag.msg.ImportMessage;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Denotation;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
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

    /** Which stage of a module's resolved declarations a registry reads. The names a module declares
     * are the same at every stage; what changes is what each declaration holds.
     *
     * <p>There is no entry here for the declarations as they were written. Those are a different
     * representation rather than an earlier stage of this one, and {@link #writtenRegistry} is what
     * answers with them — so a reader holding one of these cannot be handed a declaration nothing
     * has resolved. */
    public enum Stage { RESOLVED, DERIVED }

    /** A registry over this compilation, reading each module's declarations at {@code stage}. */
    public static Registry<Hir.Def> registry(Db db, Stage stage) {
        return new Registry<Hir.Def>() {
            @Override
            public Hir.Def declaration(TypeKey address) {
                Answer<Hir.Def> def = switch (stage) {
                    case RESOLVED -> db.ask(new ResolvedDeclaration(address));
                    case DERIVED -> db.ask(new Shapes.DerivedDef(address));
                };
                return def.present() ? def.value() : null;
            }

            @Override
            public Map<String, Hir.Def> declaredIn(String moduleName) {
                Answer<Map<String, Hir.Def>> defs = switch (stage) {
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
     * A registry over this compilation, reading each module's declarations as they were written.
     *
     * <p>What {@code Resolve} reads other modules by. A name written there is that module's to
     * resolve, and asking for its resolved form here would be this module waiting on its own.
     */
    public static Registry<Ast.Def> writtenRegistry(Db db) {
        return new Registry<Ast.Def>() {
            @Override
            public Ast.Def declaration(TypeKey address) {
                Answer<Ast.Def> def = db.ask(new Declaration(address));
                return def.present() ? def.value() : null;
            }

            @Override
            public Map<String, Ast.Def> declaredIn(String moduleName) {
                Answer<Map<String, Ast.Def>> defs = db.ask(new Declarations(moduleName));
                return defs.present() ? defs.value() : Map.of();
            }

            @Override
            public Set<String> exposedBy(String moduleName) {
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
            DeclaredNames.Of<Ast.Def> declared = DeclaredNames.of(m.value().defs(),
                    Ast.Def::name, Ast.Def::written, Ast.Def::pos);
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
    public record Declaration(TypeKey named) implements Key<Ast.Def> {
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
    public record ResolvedDeclaration(TypeKey named) implements Key<Hir.Def> {
        @Override
        public String module() {
            return named.module();
        }

        @Override
        public Answer<Hir.Def> compute(Db db) {
            Answer<Map<String, Hir.Def>> defs = db.ask(new ResolvedDeclarations(named.module()));
            if (!defs.present()) {
                return Answer.absent();
            }
            Hir.Def def = defs.value().get(named.name());
            return def == null ? Answer.absent() : Answer.of(def);
        }
    }

    /** The same declarations, with every written name in them resolved. */
    public record ResolvedDeclarations(String name) implements Key<Map<String, Hir.Def>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, Hir.Def>> compute(Db db) {
            Answer<souther.compiler.check.Resolved> m = db.ask(new Resolved(name));
            return m.present() ? Answer.of(defsOf(m.value().module())) : Answer.absent();
        }
    }

    /** A module's definitions by name, taking the names as already checked. */
    static Map<String, Hir.Def> defsOf(Hir.Module m) {
        Map<String, Hir.Def> defs = new LinkedHashMap<>();
        for (Hir.Def def : m.defs()) {
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

        public record Of(Map<String, Denotation> scope, Map<String, String> aliases) {}

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
            List<Ast.Import> imports = importsOf(db, name);
            Registry<Ast.Def> registry = writtenRegistry(db);
            Map<String, Denotation> scope = new HashMap<>();
            for (Ast.Def own : registry.declaredIn(name).values()) {
                scope.put(own.name(),
                        new Denotation.Denotes(TypeSymbols.declared(own.declaredKey())));
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
            for (Ast.Import imp : imports) {
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
                        reports.add(Report.raised(Diagnostic.say(new ModuleMessage.TheModuleDoesNotExposeIt(imported, imp.module()))
                                        .at(imp.pos()).build()));
                        nameless(scope, List.of(imported));
                        continue;
                    }
                    // asked one name at a time: what else that module declares is not what this
                    // import is about, and reading it would make this module depend on it
                    TypeSymbol brought = registry.identify(new TypeKey(imp.module(), imported));
                    if (brought == null) {
                        // a behavior import is resolved separately, and so is a value or a helper:
                        // none of them is a data Def, so none goes into the symbols map
                        if (behaviorNames(src).contains(imported) || valueNames(src).contains(imported)) {
                            continue;
                        }
                        reports.add(Report.raised(Diagnostic.say(new ModuleMessage.TheModuleDeclaresNoSuchName(imported, imp.module()))
                                        .at(imp.pos()).build()));
                        nameless(scope, List.of(imported));
                        continue;
                    }
                    Denotation standingIn = scope.get(imported);
                    if (standingIn instanceof Denotation.Denotes) {
                        reports.add(importCollision(imported, imp,
                                ownNames.contains(imported) ? null : from.get(imported)));
                        continue;   // the first claim on the name keeps it
                    }
                    // A name a failed import line only stood in for is not a claim on it: an import
                    // that can do the job takes it, and says nothing about the line that could not.
                    scope.put(imported, new Denotation.Denotes(brought));
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
    private static void nameless(Map<String, Denotation> scope, List<String> names) {
        for (String written : names) {
            scope.putIfAbsent(written, Denotation.STANDS_FOR_NOTHING);
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

    /** The same, over the declarations as they were written — what {@code Resolve} resolves
     * against. */
    static Answer<SyntaxSymbols> writtenSymbols(Db db, String name) {
        Answer<Imports.Of> imports = db.ask(new Imports(name));
        if (!imports.present()) {
            return Answer.absent();
        }
        return Answer.of(SyntaxSymbols.of(name, writtenRegistry(db), imports.value().scope(),
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
    public record Resolution(String name) implements Key<Resolve.Resolution> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Resolve.Resolution> compute(Db db) {
            Answer<Ast.Module> available = db.ask(new Front.Available(name));
            if (!available.present()) {
                return Answer.absent();
            }
            // Resolution reads other modules' declarations as they were written, not as they will
            // be resolved: a name written there is that module's to resolve, and asking for its
            // resolved form here would be this module waiting on its own.
            Answer<SyntaxSymbols> scope = writtenSymbols(db, name);
            if (!scope.present()) {
                return Answer.absent();
            }
            Resolve.Resolution resolution;
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
            List<Report> reports = new ArrayList<>(
                    valueNamespaceCollisions(db, available.value()));
            for (CompileException unresolved : resolution.unresolved()) {
                reports.addAll(Report.of(unresolved));
            }
            return Answer.of(resolution, reports);
        }
    }

    /**
     * What resolution worked out about the names a module writes.
     *
     * <p>This is what a reader outside the compiler is answered from, and it is asked for on its
     * own so that such a reader never holds the tree. The two are not the same artifact and do not
     * come and go together: a module the compiler will not build on is still a module an editor has
     * to say things about, and every name that did resolve in it is a name it can be told about.
     */
    public record Facts(String name) implements Key<Resolve.ResolutionIndex> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Resolve.ResolutionIndex> compute(Db db) {
            Answer<Resolve.Resolution> resolution = db.ask(new Resolution(name));
            return resolution.present() ? Answer.of(resolution.value().index()) : Answer.absent();
        }
    }

    /**
     * One declaration as its meaning was settled, or absent where it was not settled.
     *
     * <p>The unit a name is answered for is the declaration. A definition is here when every name
     * written in it was answered and every declaration it reaches has one of these too; otherwise
     * there is nothing to hand a later pass, and it is not built rather than built around what is
     * missing.
     */
    public record Definition(TypeKey named) implements Key<Hir.Def> {
        @Override
        public String module() {
            return named.module();
        }

        @Override
        public Answer<Hir.Def> compute(Db db) {
            Answer<Resolve.Resolution> resolution = db.ask(new Resolution(named.module()));
            Answer<Set<String>> unbuilt = db.ask(new Unbuilt(named.module()));
            if (!resolution.present() || !unbuilt.present()
                    || unbuilt.value().contains(named.name())) {
                return Answer.absent();
            }
            for (Hir.Def def : resolution.value().module().module().defs()) {
                if (def.name().equals(named.name())) {
                    return Answer.of(def);
                }
            }
            return Answer.absent();
        }
    }

    /**
     * The declarations of a module that have no meaning to give.
     *
     * <p>Two ways in, and both are about what a declaration is made of rather than about what was
     * reported. A name written in it was not answered, so what it is made of is not there; or what
     * it reaches is one of these, so what that is made of is not there either. A module that will
     * not be emitted for some other reason has declarations that mean what they say, and they are
     * not in here.
     *
     * <p>Asked of a whole module at once because the reaching is a relation among its own
     * declarations, and following it one declaration at a time would ask a question of itself where
     * two of them are made of each other. Across modules there is no such loop to close: an import
     * cycle is settled before this, so a module's declarations reach another's and stop.
     *
     * <p>Not part of what a reader outside this file asks. Whether a declaration has a meaning is
     * {@link Definition}'s to answer and is answered by handing one over or not; a reader that could
     * ask which ones have none would be a reader deciding for itself what to do about it, which is
     * how the question of what a name means came to be answered in several places at once.
     */
    record Unbuilt(String name) implements Key<Set<String>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Set<String>> compute(Db db) {
            if (cyclic(db, name)) {
                return Answer.absent();
            }
            Answer<Resolve.Resolution> resolution = db.ask(new Resolution(name));
            if (!resolution.present()) {
                return Answer.absent();
            }
            Map<String, Resolve.OfDeclaration> declarations = resolution.value().declarations();
            Set<String> unbuilt = new LinkedHashSet<>();
            Map<String, Set<String>> elsewhere = new LinkedHashMap<>();
            for (Map.Entry<String, Resolve.OfDeclaration> declared : declarations.entrySet()) {
                if (!declared.getValue().answered()) {
                    unbuilt.add(declared.getKey());
                    continue;
                }
                for (TypeSymbol reached : declared.getValue().reaches()) {
                    if (reached.module().equals(name)) {
                        continue;
                    }
                    Set<String> there = elsewhere.computeIfAbsent(reached.module(),
                            m -> unbuiltIn(db, m));
                    if (there.contains(reached.name())) {
                        unbuilt.add(declared.getKey());
                        break;
                    }
                }
            }
            // What reaches one of these has nothing to stand on either, and so has what reaches
            // that. Held to the declarations of this module, which is where the relation is.
            boolean more = true;
            while (more) {
                more = false;
                for (Map.Entry<String, Resolve.OfDeclaration> declared : declarations.entrySet()) {
                    if (unbuilt.contains(declared.getKey())) {
                        continue;
                    }
                    for (TypeSymbol reached : declared.getValue().reaches()) {
                        if (reached.module().equals(name) && unbuilt.contains(reached.name())) {
                            unbuilt.add(declared.getKey());
                            more = true;
                            break;
                        }
                    }
                }
            }
            return Answer.of(Set.copyOf(unbuilt));
        }

        /** What another module could not build, or nothing where it could not be read — what is
         * wrong there is reported there, and a name reaching into it is answered by its absence. */
        private static Set<String> unbuiltIn(Db db, String module) {
            Answer<Set<String>> there = db.ask(new Unbuilt(module));
            return there.present() ? there.value() : Set.of();
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
            souther.compiler.check.Resolved m = db.ask(new Resolved(name)).value();
            if (m == null) {
                return Answer.of(Boolean.FALSE);   // there is no module here to have a hole in
            }
            for (Hir.BehaviorDef b : m.module().behaviors()) {
                List<Hir.Var> named = switch (b) {
                    case Hir.PipeBehavior pipe -> pipe.stages();
                    case Hir.SpecBehavior spec -> spec.dependsOn();
                };
                for (Hir.Var ref : named) {
                    if (ref.unresolved()) {
                        return Answer.of(Boolean.TRUE);
                    }
                }
            }
            return Answer.of(Boolean.FALSE);
        }
    }

    /**
     * A name on an import list that the module never writes bare — reported at the name, as a
     * warning.
     *
     * <p>The question is the reverse of {@link Imports}'. That one asks what each written name means
     * and answers it against the exporting module; this asks, of the importing module's own body,
     * whether anything said the name at all. Nothing else asks it, which is why an import list could
     * claim a vocabulary the module does not speak and no one was told.
     *
     * <p>Being written bare is the whole test, and it is narrower than being mentioned. What another
     * module declares is reachable qualified whether or not it is imported (spec §modules), so
     * {@code Stock.Sku} is a use of the declaration and not of the import: take {@code Sku} off the
     * list and that line still compiles. An entry earns its place by being the spelling something
     * below actually used, which is why a use is matched on what was written as well as on what it
     * denotes.
     */
    public record UnusedImports(String name) implements Key<Boolean> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Boolean> compute(Db db) {
            // Said only of a module whose names all came out. A name that denotes nothing may be the
            // misspelt use of the very import in question, and "this import is unused" is the wrong
            // thing to tell someone whose mistake is a typo four lines down. Sound is where that
            // judgement already lives — it asks the imports, the resolution and the bound stages
            // together, and it asks nothing about types, rows or coverage, so a failing example does
            // not silence this.
            if (!Boolean.TRUE.equals(db.ask(new Sound(name)).value())) {
                return Answer.of(true);
            }
            List<Ast.Import> written = writtenImports(db, name);
            if (written.isEmpty()) {
                return Answer.of(true);
            }
            Set<Use> used = usesIn(db, name);
            if (used == null) {
                return Answer.of(true);
            }
            List<Report> reports = new ArrayList<>();
            for (Ast.Import imp : written) {
                for (Ast.ImportedName imported : imp.importedNames()) {
                    // A name with no position was not written on any list — it was synthesized from
                    // a qualified reference, and there is nothing for anyone to delete.
                    if (imported.pos() == null
                            || used.contains(new Use(imported.text(), imp.module(), imported.text()))) {
                        continue;
                    }
                    reports.add(Report.of(Diagnostic.say(new ModuleMessage.ImportedButNeverUsedUnderThisName(imported.written().quoted()))
                            .at(imported.written().reportedAt())
                            
                            .hint(new ModuleMessage.TakeItOffTheImportList())
                            .build()));
                }
            }
            return Answer.of(true, reports);
        }

        /**
         * The import lines as the source wrote them.
         *
         * <p>Read off the parsed source rather than off {@link Front.Available}, because the module
         * that arrives from there has had its standard-library import lines taken out
         * ({@link souther.compiler.check.Exposing#withoutLibraryImports}) — an unused
         * {@code import List ( fold )} would be invisible to a check that read the module. An
         * attached {@code examples for} file writes no imports, so the declaring source's lines are
         * all of them.
         */
        private static List<Ast.Import> writtenImports(Db db, String module) {
            Front.Layout.Of layout = db.ask(new Front.Layout()).value();
            String id = layout == null ? null : layout.idOfModule().get(module);
            if (id == null) {
                return List.of();
            }
            Answer<souther.compiler.frontend.CstFrontend.Parsed> parsed = db.ask(new Front.Parsed(id));
            return parsed.present() ? parsed.value().module().imports() : List.of();
        }
    }

    /**
     * One name written in a module and the declaration it turned out to mean: the spelling, and the
     * qualifier and name a reference would have reached that declaration by written out in full.
     *
     * <p>The qualifier and not the declaring module, because that is what an import line writes and
     * an import line is what these are compared against. For a user module the two are the same
     * name; for the standard library they are not — {@code souther.list} declares {@code foldFrom}
     * and a line writes {@code import List ( foldFrom )} — and it is the alias every side of this
     * comparison holds.
     *
     * <p>The spelling is half of it because an import list entry is a claim about a spelling. Two
     * uses of one declaration — {@code Sku} and {@code Stock.Sku} — are the same declaration and
     * different claims, and only the first is what an import list entry buys.
     */
    private record Use(String written, String qualifier, String name) {}

    /** Every name {@code module} writes, paired with what it denotes, or null when the module could
     * not be read. */
    private static Set<Use> usesIn(Db db, String module) {
        Answer<Resolve.ResolutionIndex> facts = db.ask(new Facts(module));
        if (!facts.present()) {
            return null;
        }
        Set<Use> used = new HashSet<>();
        for (Resolve.TypeUse d : facts.value().types()) {
            used.add(new Use(d.written().canonical(), d.denotes().module(), d.denotes().name()));
        }
        for (Resolve.ValueUse v : facts.value().values()) {
            switch (v.denotes()) {
                case ValueName.Behavior b ->
                        used.add(new Use(v.written().canonical(), b.module(), b.name()));
                case ValueName.Helper h ->
                        used.add(new Use(v.written().canonical(), h.module(), h.name()));
                // `List.map` and a bare `map` an import brought in both denote the same library
                // function. Its qualifier is the alias the library publishes it under, asked of the
                // name — which holds it — rather than taken back out of the two rendered together.
                // A namespace applied is not a member of anything and no list entry names one.
                case ValueName.Stdlib s when !s.isNamespace() ->
                        used.add(new Use(v.written().canonical(), s.alias(), s.operation()));
                default -> { }   // a local, a builtin, a type used as a value (recorded as a type)
            }
        }
        // A `>->` stage and a `depends on` name a behavior, and resolution answers both like any
        // other name in the value namespace — so they are in the record above, and reading the tree
        // for them again would be a second place that says which import is used.
        return used;
    }

    /** What a module's bodies can name without a binding: its own helpers, and every behavior it can
     * reach — its own and the ones its imports bring in. */
    private static Resolve.Values reachableValues(Db db, Ast.Module m) {
        // A behavior's `let` is not a helper: it implements the behavior, and the name reaches the
        // behavior. Asked the same way as HelperInliner.helpersOf, which decides what is expanded —
        // two answers to one question is how a name came to denote a helper here and a behavior
        // there.
        Set<String> behaviorNames = new LinkedHashSet<>();
        for (Ast.BehaviorDef b : m.behaviors()) {
            behaviorNames.add(b.name());
        }
        Map<String, ValueName.Helper> helpers = new LinkedHashMap<>();
        for (Ast.FnDef fn : m.fns()) {
            if (HelperInliner.isHelperName(behaviorNames, fn.name())) {
                helpers.put(fn.name(), new ValueName.Helper(m.name(), fn.name()));
            }
        }
        // A definition another module publishes is written here bare, like one of this module's own —
        // a value substituted at its reference, a helper expanded at its call (ADR-0072). What it
        // denotes is the module that declares it: the bare spelling is this module's way of writing
        // it, and the pair (module, name) is what the definition is. A reader that spells one of its
        // own the same way is a name clash, which the import check reports.
        for (Ast.Import imp : m.imports()) {
            Ast.Module from = db.ask(new Front.Available(imp.module())).value();
            if (from == null) {
                continue;
            }
            for (String published : Bodies.publishedNames(from, imp.names())) {
                helpers.putIfAbsent(published, new ValueName.Helper(from.name(), published));
            }
        }
        BehaviorsInScope.Of behaviors = db.ask(new BehaviorsInScope(m.name())).value();
        Map<String, ValueName.Stdlib> exposed = db.ask(new Front.LibraryNames(m.name())).value();
        return new Resolve.Values(m.name(), helpers,
                behaviors == null ? Map.of() : behaviors.byName(),
                behaviors != null && behaviors.whole(),
                exposed == null ? Map.of() : exposed,
                new Resolve.Elsewhere() {
                    @Override
                    public boolean hasModule(String name) {
                        return db.ask(new Front.ModuleNames()).value().contains(name);
                    }

                    @Override
                    public Set<String> behaviorsOf(String module) {
                        Answer<Set<String>> declared = db.ask(new Front.Behaviors(module));
                        return declared.present() ? declared.value() : null;
                    }
                });
    }

    /** The resolved module — {@link Resolution} without the record of how it got there. */
    public record Resolved(String name) implements Key<souther.compiler.check.Resolved> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<souther.compiler.check.Resolved> compute(Db db) {
            Answer<Resolve.Resolution> resolution = db.ask(new Resolution(name));
            return resolution.present() ? Answer.of(resolution.value().module()) : Answer.absent();
        }
    }

    /**
     * The module a question about a place is a question about, or null when this compilation does
     * not have the file — including a question that names no file at all, which names no place and
     * so has no module to be asked of.
     */
    private static String moduleAt(Db db, SourcePos at) {
        return at == null || at.sourceId() == null
                ? null : db.ask(new Front.ModuleOf(at.sourceId())).value();
    }

    /**
     * What the name written at {@code at} denotes, or absent when nothing there is a name of a
     * declared type.
     *
     * <p>This is what an editor is asking when the cursor is on an identifier. It reads the answers
     * the resolve pass already gave, so a qualified reference names the module it names and not
     * whatever this module happens to declare by the same spelling.
     *
     * <p>Asked about a place, not about a module and a place. Which module answers is the file's to
     * settle — an attached {@code examples for} file declares none and is part of one all the same,
     * and a caller that had to name the module first was a caller that could name the wrong one.
     */
    public record DenotedAt(SourcePos at) implements Key<Resolve.TypeUse> {
        @Override
        public String sourceId() {
            return at == null ? null : at.sourceId();
        }

        @Override
        public Answer<Resolve.TypeUse> compute(Db db) {
            String name = moduleAt(db, at);
            if (name == null) {
                return Answer.absent();
            }
            Answer<Resolve.ResolutionIndex> facts = db.ask(new Facts(name));
            if (!facts.present()) {
                return Answer.absent();
            }
            Resolve.TypeUse innermost = null;
            for (Resolve.TypeUse d : facts.value().types()) {
                if (!spans(d.written(), at)) {
                    continue;
                }
                // A container writes its element's name inside its own span, so the one written
                // inside the other is the one the cursor is actually on.
                if (innermost == null || d.written().within(innermost.written())) {
                    innermost = d;
                }
            }
            return innermost == null ? Answer.absent() : Answer.of(innermost);
        }
    }

    /**
     * The type the cursor is on at {@code at}: the one a name there denotes, or — when the cursor is
     * on a declaration's own name — that declaration.
     *
     * <p>One question, so an editor's go-to-definition, find-references and rename all agree about
     * what the cursor is on. They used to each decide for themselves, by spelling.
     */
    public record TypeAt(SourcePos at) implements Key<TypeSymbol> {
        @Override
        public String sourceId() {
            return at == null ? null : at.sourceId();
        }

        @Override
        public Answer<TypeSymbol> compute(Db db) {
            String name = moduleAt(db, at);
            if (name == null) {
                return Answer.absent();
            }
            Answer<Map<String, Ast.Def>> defs = db.ask(new Declarations(name));
            if (defs.present()) {
                for (Ast.Def def : defs.value().values()) {
                    if (spans(def.written(), at)) {
                        // Asked of the declaration world this came out of, rather than made from the
                        // address it answers to.
                        return Answer.of(writtenRegistry(db).identify(def.declaredKey()));
                    }
                }
            }
            Resolve.TypeUse denoted = db.ask(new DenotedAt(at)).value();
            return denoted == null ? Answer.absent() : Answer.of(denoted.denotes());
        }
    }

    /** Every place a module names {@code denoted}, wherever it was declared. */
    public record UsesOf(String name, TypeSymbol denoted) implements Key<List<Resolve.TypeUse>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<List<Resolve.TypeUse>> compute(Db db) {
            Answer<Resolve.ResolutionIndex> facts = db.ask(new Facts(name));
            if (!facts.present()) {
                return Answer.of(List.of());
            }
            List<Resolve.TypeUse> uses = new ArrayList<>();
            for (Resolve.TypeUse d : facts.value().types()) {
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
    public record ValueDenotedAt(SourcePos at) implements Key<Resolve.ValueUse> {
        @Override
        public String sourceId() {
            return at == null ? null : at.sourceId();
        }

        @Override
        public Answer<Resolve.ValueUse> compute(Db db) {
            String name = moduleAt(db, at);
            if (name == null) {
                return Answer.absent();
            }
            Answer<Resolve.ResolutionIndex> facts = db.ask(new Facts(name));
            if (!facts.present()) {
                return Answer.absent();
            }
            for (Resolve.ValueUse use : facts.value().values()) {
                if (spans(use.written(), at)) {
                    return Answer.of(use);
                }
            }
            return Answer.absent();
        }
    }

    /**
     * Every place a module names {@code denoted} as a value, wherever it was declared.
     *
     * <p>{@link UsesOf} for the value namespace. A local is answered here as readily as a top-level
     * name: what a use denotes is a binding and not a spelling, so the uses of one {@code let}'s
     * {@code x} are not the uses of another's.
     */
    public record ValueUsesOf(String name, ValueName denoted) implements Key<List<Resolve.ValueUse>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<List<Resolve.ValueUse>> compute(Db db) {
            Answer<Resolve.ResolutionIndex> facts = db.ask(new Facts(name));
            if (!facts.present()) {
                return Answer.of(List.of());
            }
            List<Resolve.ValueUse> uses = new ArrayList<>();
            for (Resolve.ValueUse use : facts.value().values()) {
                if (denoted.equals(use.denotes())) {
                    uses.add(use);
                }
            }
            return Answer.of(List.copyOf(uses));
        }
    }

    /**
     * The value the cursor is on at {@code at}: the one a name there denotes, or — when the cursor
     * is on a binding — the binding itself.
     *
     * <p>{@link TypeAt} for the value namespace, and for the same reason: a reader asking about a
     * binding is asking from one end or the other, and the two ends are one question. Answering
     * only where a name is read would put a local within reach from its uses and out of reach from
     * the {@code let} that binds it.
     */
    public record ValueAt(SourcePos at) implements Key<ValueName> {
        @Override
        public String sourceId() {
            return at == null ? null : at.sourceId();
        }

        @Override
        public Answer<ValueName> compute(Db db) {
            String name = moduleAt(db, at);
            if (name == null) {
                return Answer.absent();
            }
            Answer<Resolve.ResolutionIndex> facts = db.ask(new Facts(name));
            if (!facts.present()) {
                return Answer.absent();
            }
            Map<BindingId, Resolve.BoundName> binders = facts.value().binders();
            for (Map.Entry<BindingId, Resolve.BoundName> bound : binders.entrySet()) {
                Resolve.BoundName written = bound.getValue();
                if (answerable(bound.getKey(), binders)
                        && spans(written.written(), at)) {
                    ValueName local =
                            new ValueName.Local(written.written().canonical(), bound.getKey());
                    return Answer.of(local);
                }
            }
            Resolve.ValueUse use = db.ask(new ValueDenotedAt(at)).value();
            if (use == null) {
                return Answer.absent();
            }
            if (use.denotes() instanceof ValueName.Local local
                    && !answerable(local.id(), binders)) {
                return Answer.absent();
            }
            return Answer.of(use.denotes());
        }

        /**
         * Whether a reader can be told about this binding at all.
         *
         * <p>Two things have to hold, and both are about what the resolve pass read rather than
         * about what an editor would like. The binding's name has to be one the author wrote —
         * absent from {@code binders} means a desugaring invented it, and a name nobody wrote is
         * under no cursor and cannot be renamed. And it has to be a binding whose uses this pass
         * records: a field's are not names in scope but reads resolved by the type of what they are
         * read from, and only the ones inside an {@code invariant} come through here. A field
         * answered from what is written here would be renamed at its declaration and nowhere else.
         */
        private static boolean answerable(BindingId id, Map<BindingId, Resolve.BoundName> binders) {
            return binders.containsKey(id) && !(id.owner() instanceof BindingOwner.OfFields);
        }
    }

    /**
     * Every place the name of what {@code denoted} names is written as a declaration.
     *
     * <p>More than one, because a behavior is declared twice: the {@code behavior} line says what it
     * is and the {@code let} line says what it does, and both write the name. A reader sent to the
     * declaration wants the first of them; a rename has to rewrite all of them, or the module goes
     * on naming something that is no longer there.
     */
    public record ValueDeclarationsOf(ValueName denoted) implements Key<List<WrittenName>> {
        @Override
        public String module() {
            return switch (denoted) {
                case ValueName.Helper h -> h.module();
                case ValueName.Behavior b -> b.module();
                case ValueName.Local l -> l.id().owner().module();
                case ValueName.Stdlib _, ValueName.OfType _, ValueName.Builtin _ -> null;
            };
        }

        @Override
        public Answer<List<WrittenName>> compute(Db db) {
            // a binding is not a position, so where it was written is asked of the pass that
            // answered it rather than read off the name
            if (denoted instanceof ValueName.Local local) {
                Answer<Resolve.ResolutionIndex> facts =
                        db.ask(new Facts(local.id().owner().module()));
                if (!facts.present()) {
                    return Answer.absent();
                }
                Resolve.BoundName binder = facts.value().binders().get(local.id());
                return binder == null ? Answer.absent() : Answer.of(List.of(binder.written()));
            }
            String in = module();
            if (in == null) {
                return Answer.absent();   // the library and the language declare their own names
            }
            Ast.Module m = db.ask(new Front.Available(in)).value();
            if (m == null) {
                return Answer.absent();
            }
            List<WrittenName> written = new ArrayList<>();
            for (Ast.BehaviorDef b : m.behaviors()) {
                if (b.name().equals(denoted.name()) && b.written().authored()) {
                    written.add(b.written());
                }
            }
            for (Ast.FnDef fn : m.fns()) {
                if (fn.name().equals(denoted.name()) && fn.written().authored()) {
                    written.add(fn.written());
                }
            }
            return written.isEmpty() ? Answer.absent() : Answer.of(List.copyOf(written));
        }
    }

    /**
     * Where what {@code denoted} names is written: the {@code behavior} that declares it, the
     * {@code let} where it has no signature, or the binding that introduced a local.
     *
     * <p>The first of {@link ValueDeclarationsOf}, which is the one to send a reader to. A behavior
     * has two, and its signature says more about it than its body does.
     */
    public record ValueDeclaredAt(ValueName denoted) implements Key<WrittenName> {
        @Override
        public String module() {
            return new ValueDeclarationsOf(denoted).module();
        }

        @Override
        public Answer<WrittenName> compute(Db db) {
            Answer<List<WrittenName>> written = db.ask(new ValueDeclarationsOf(denoted));
            return written.present() ? Answer.of(written.value().get(0)) : Answer.absent();
        }
    }

    /**
     * Whether the occurrence {@code written} covers {@code at}. A name is one line's worth of text,
     * so a position on another line is not on it — and a name in another file is not on it either,
     * however the line numbers happen to line up.
     *
     * <p>How far it reaches is the characters that spell it, not the name they spell. A decomposed
     * spelling is wider than the composed name it denotes, so measuring in the name puts the far end
     * of every such name out of reach of a cursor sitting on it.
     *
     * <p>A name nobody wrote is under no cursor. A desugaring's binding is anchored on the form it
     * was rewriting, and that form is holding something else — so a reader answered from one would
     * be answered about a name that is not there, at a width that is not its.
     *
     * <p>The file matters here for the reason it matters anywhere: what a module is made of is not
     * all written in one file. An attached {@code examples for} file's rows, tables and values join
     * the module they are for, and a question asked of the module reads all of them, so line 8
     * column 14 is two places and an editor asking about one of them was answered about whichever
     * came first. What was under the cursor and what the answer described were then two different
     * names.
     *
     * <p>A question that names no file names no place either. Every question about a cursor now
     * arrives as one, because the module it is answered about is read off the file it names, so
     * there is no longer a caller with only a line and a column to give.
     */
    static boolean spans(WrittenName written, SourcePos at) {
        return written != null && written.authored() && written.covers(at);
    }

    /** The occurrence of a type's own name, in the declaration that declares it. */
    public record DeclaredAt(TypeSymbol denoted) implements Key<WrittenName> {
        @Override
        public String module() {
            return denoted.module();
        }

        @Override
        public Answer<WrittenName> compute(Db db) {
            Answer<Map<String, Ast.Def>> defs = db.ask(new Declarations(denoted.module()));
            if (!defs.present()) {
                return Answer.absent();
            }
            // The occurrence of the name, not where the declaration starts: a reader sent to a
            // declaration is being sent to the name it declares, the keyword in front of it is not
            // what they asked about, and how far the name reaches is the characters that spell it.
            Ast.Def def = defs.value().get(denoted.name());
            return def == null || !def.written().authored()
                    ? Answer.absent() : Answer.of(def.written());
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
                    found.putIfAbsent(name, Report.raised(Diagnostic.at(dep.pos()).say(new DeclarationMessage.CyclicModuleDependency()).build()));
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
        Map<String, String> qualifiers = aliases(m);
        for (Ast.Import imp : m.imports()) {
            deps.add(new Dependency(imp.module(), imp.pos()));
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
        for (Ast.Var ref : qualifiedBehaviorRefs(m)) {
            String target = moduleNamedBy(ref.name(), qualifiers);
            if (modules.contains(target) && !target.equals(m.name())) {
                deps.add(new Dependency(target, ref.pos()));
            }
        }
        return deps;
    }

    /** Each import alias, against the module it stands for. */
    private static Map<String, String> aliases(Ast.Module m) {
        Map<String, String> qualifiers = new HashMap<>();
        for (Ast.Import imp : m.imports()) {
            if (imp.alias() != null) {
                qualifiers.put(imp.alias(), imp.module());
            }
        }
        return qualifiers;
    }

    /** The module a qualified spelling names, by its qualifier — an alias, or a module named under
     * its own name. Null where the spelling carries no qualifier. */
    private static String moduleNamedBy(String written, Map<String, String> qualifiers) {
        int dot = written.lastIndexOf('.');
        if (dot < 0) {
            return null;
        }
        String qualifier = written.substring(0, dot);
        return qualifiers.getOrDefault(qualifier, qualifier);
    }

    /** Every name the behavior namespace writes with a qualifier: a {@code >->} stage, a
     *  {@code depends on}. */
    private static List<Ast.Var> qualifiedBehaviorRefs(Ast.Module m) {
        List<Ast.Var> out = new ArrayList<>();
        for (Ast.BehaviorDef b : m.behaviors()) {
            List<Ast.Var> refs = switch (b) {
                case Ast.PipeBehavior pipe -> pipe.stages();
                case Ast.SpecBehavior spec -> spec.dependsOn();
            };
            for (Ast.Var ref : refs) {
                if (ref.name().lastIndexOf('.') >= 0 && !Resolve.namesABoundaryEdge(ref.name())) {
                    out.add(ref);
                }
            }
        }
        return out;
    }

    /**
     * The behaviors this module names through another module's name, by that module.
     *
     * <p>Naming one is reaching into that module whether or not an import line says so: the borrowed
     * signature and the injected field are found by an import, and the module is a dependency for
     * the same reason. So it is answered here, off the spellings the header writes, rather than
     * below resolution — what modules this one reaches has to be settled before anything resolves
     * against them.
     *
     * <p>Whether the behavior is there at all is not asked. A name that reaches into a module names
     * that module either way, and what it turned out to denote is {@code Resolution}'s to say.
     */
    public record Borrowed(String name) implements Key<Map<String, Set<String>>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, Set<String>>> compute(Db db) {
            Answer<Ast.Module> exposed = db.ask(new Front.Exposed(name));
            if (!exposed.present()) {
                return Answer.absent();
            }
            Ast.Module m = exposed.value();
            Set<String> modules = db.ask(new Front.ModuleNames()).value();
            Map<String, String> qualifiers = aliases(m);
            Map<String, Set<String>> out = new LinkedHashMap<>();
            for (Ast.Var ref : qualifiedBehaviorRefs(m)) {
                String written = ref.name();
                String target = moduleNamedBy(written, qualifiers);
                if (target == null || target.equals(name)
                        || modules == null || !modules.contains(target)) {
                    continue;
                }
                String bare = written.substring(written.lastIndexOf('.') + 1);
                // A name that module does not declare is borrowed from nowhere. That it names
                // nothing is reported where the clause is read, and an import synthesized for it
                // would say the same thing a second time against a line nobody wrote.
                Answer<Set<String>> declared = db.ask(new Front.Behaviors(target));
                if (!declared.present() || !declared.value().contains(bare)) {
                    continue;
                }
                out.computeIfAbsent(target, k -> new LinkedHashSet<>()).add(bare);
            }
            return Answer.of(Map.copyOf(out));
        }
    }

    /**
     * The imports a module has: the ones it wrote, and the ones a qualified reference in its header
     * asked for.
     *
     * <p>What a reader wanting "which modules does this reach, and which of their names" asks. The
     * second kind carries no import line, and a reader that read only the lines would miss the
     * borrowed signature it has to hold.
     */
    public static List<Ast.Import> importsOf(Db db, String name) {
        Answer<Ast.Module> module = db.ask(new Front.Available(name));
        if (!module.present()) {
            return List.of();
        }
        List<Ast.Import> imports = new ArrayList<>(module.value().imports());
        Map<String, Set<String>> borrowed = db.ask(new Borrowed(name)).value();
        if (borrowed == null) {
            return imports;
        }
        for (Map.Entry<String, Set<String>> e : borrowed.entrySet()) {
            Set<String> already = new LinkedHashSet<>();
            for (Ast.Import imp : module.value().imports()) {
                if (imp.module().equals(e.getKey())) {
                    already.addAll(imp.names());
                }
            }
            List<Ast.ImportedName> names = new ArrayList<>();
            for (String bare : e.getValue()) {
                if (!already.contains(bare)) {
                    // No position on a synthesized name: nobody wrote it on an import list. The
                    // qualified reference that asked for it is where it came from.
                    names.add(new Ast.ImportedName(bare, null));
                }
            }
            if (!names.isEmpty()) {
                imports.add(new Ast.Import(e.getKey(), null, names, module.value().pos()));
            }
        }
        return imports;
    }

    static Set<String> behaviorNames(Ast.Module m) {
        Set<String> names = new LinkedHashSet<>();
        for (Ast.BehaviorDef b : m.behaviors()) {
            names.add(b.name());
        }
        return names;
    }

    /** The same, of a module resolution has been over. */
    static Set<String> behaviorNames(Hir.Module m) {
        Set<String> names = new LinkedHashSet<>();
        for (Hir.BehaviorDef b : m.behaviors()) {
            names.add(b.name());
        }
        return names;
    }

    /** The definitions a module declares in the value namespace — its values and its helpers. Like a
     * behavior, one is a name in that namespace and not a data, so an import of it resolves
     * elsewhere. */
    static Set<String> valueNames(Ast.Module m) {
        Set<String> behaviors = behaviorNames(m);
        Set<String> names = new LinkedHashSet<>();
        for (Ast.FnDef fn : m.fns()) {
            if (HelperInliner.isHelperName(behaviors, fn.name())) {
                names.add(fn.name());
            }
        }
        return names;
    }

    static Report unknownModule(Ast.Import imp) {
        return Report.raised(Diagnostic.say(new ModuleMessage.UnknownModule(imp.module()))
                        .at(imp.pos()).build());
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
        return Report.raised(Diagnostic.say(new ModuleMessage.TheAliasIsAlreadyTaken(imp.alias(), taken))
                        .at(imp.pos())
                        .hint(new ModuleMessage.AnAliasIsANameNothingElseAnswersTo()).build());
    }

    /**
     * Every way a spelling reaches this module's value namespace, and a report for each spelling that
     * reaches it twice.
     *
     * <p>A data reaches it — a unit data is a value, a newtype is applied to what it wraps, a record
     * is constructed by its name — and so do a {@code let}, a behavior, a definition another module
     * publishes, and a standard-library qualifier. One name means one thing there, whichever way it
     * arrived. A spelling with two meanings is answered by whichever reader looks first, which is how
     * a name could be a unit data where it stood alone and an imported helper where it was applied.
     *
     * <p>Asked here because this is where the namespace is assembled (see {@link #reachableValues}).
     * A rule stated per arrival would have to be restated for each new way in.
     *
     * <p>A behavior and a {@code let} of one name are not two: they are the declaration and the
     * implementation of one thing (ADR-0072).
     */
    private static List<Report> valueNamespaceCollisions(Db db, Ast.Module m) {
        List<Report> reports = new ArrayList<>();
        Map<String, Ast.Def> declared = new LinkedHashMap<>();
        for (Ast.Def def : m.defs()) {
            // A standard-library qualifier is the only spelling that reaches the library, so a data
            // of that name hides it — from every module, since the qualifier is not this module's to
            // shadow. Refused where it is declared, as a reserved module name is (see Front).
            if (Prelude.isQualifier(def.name())) {
                reports.add(Report.raised(Diagnostic
                                .at(def.pos()).say(new DataMessage.ADataTakesTheStandardLibraryQualifier(def.name())).build()));
            }
            declared.put(def.name(), def);
        }
        Set<String> implementing = new HashSet<>();
        for (Ast.BehaviorDef b : m.behaviors()) {
            implementing.add(b.name());
        }
        for (Ast.FnDef fn : m.fns()) {
            if (implementing.contains(fn.name()) || !declared.containsKey(fn.name())) {
                continue;
            }
            reports.add(Report.raised(Diagnostic
                            .at(fn.pos()).say(new DataMessage.ALetAndADataShareOneSpelling(fn.name())).build()));
        }
        // What this module declares under a name, whichever kind of declaration it is: a data, a
        // `let`, a behavior. A behavior and its `let` are one of them, so the set is what is asked
        // rather than a count.
        Set<String> ownNames = new LinkedHashSet<>(declared.keySet());
        ownNames.addAll(implementing);
        for (Ast.FnDef fn : m.fns()) {
            ownNames.add(fn.name());
        }
        // A name an import brings in is written here bare (ADR-0075), so it arrives in this
        // namespace exactly as one of this module's own does — and collides the same way. Which kind
        // of thing each side is does not enter into it: the reader writes one spelling, and one
        // spelling here means one thing.
        for (Ast.Import imp : m.imports()) {
            for (String imported : importedIntoValues(db, imp)) {
                if (ownNames.contains(imported)) {
                    reports.add(importCollision(imported, imp, null));
                }
            }
        }
        return reports;
    }

    /**
     * The names {@code imp} brings into the value namespace: the definitions the module publishes,
     * the behaviors it declares and the types it declares, all of which a reader writes bare. A type
     * is one of them because a unit data is a value, a newtype is applied to what it wraps and a
     * record is constructed by its name — the type namespace refuses a type against a type, so what
     * a type adds here is a type against a {@code let} or a behavior.
     *
     * <p>Only what {@code from} exposes, and only what the line asks for. A name the line names and
     * the module does not expose is nothing this import brought in, and reporting a collision for it
     * would tell the author to rename a definition that is not what is wrong — the line is answered
     * by {@code check.import.notexposed}, which is the whole of it.
     *
     * <p>A library import is not here. Those lines are read where the table they fill is built
     * ({@link Exposing}) and are gone from the module by the time this is asked.
     */
    private static Set<String> importedIntoValues(Db db, Ast.Import imp) {
        Ast.Module from = db.ask(new Front.Available(imp.module())).value();
        if (from == null) {
            return Set.of();
        }
        Set<String> names = new LinkedHashSet<>(Bodies.publishedNames(from, imp.names()));
        Set<String> declared = new LinkedHashSet<>(behaviorNames(from));
        for (Ast.Def def : from.defs()) {
            declared.add(def.name());
        }
        Set<String> exposed = new HashSet<>(from.exposing());
        for (String name : imp.names()) {
            if (declared.contains(name) && exposed.contains(name)) {
                names.add(name);
            }
        }
        return names;
    }

    /**
     * The name arrived twice. {@code earlier} is the import that already brought it in, or null when
     * the module defines it itself. Either way the way out is inside the module: keep at most one of
     * them bare and name the other through its module.
     */
    private static Report importCollision(String name, Ast.Import imp, Ast.Import earlier) {
        if (earlier == null) {
            return Report.raised(Diagnostic.at(imp.pos())
                            .say(new ImportMessage.ImportedNameCollidesWithADeclaration(name))
                            .hint(new ImportMessage.RenameOrQualifyTheCollidingName())
                            .build());
        }
        Diagnostic.Builder b = Diagnostic.at(imp.pos())
                .secondary(Region.point(earlier.pos()), new ModuleMessage.ItWasAlreadyImportedHere(name, earlier.module()));
        return Report.raised((earlier.module().equals(imp.module())
                        ? b.hint(new ModuleMessage.TheSameNameIsImportedTwiceFromOneModule())
                        : b.hint(new ModuleMessage.ImportAtMostOneAndQualifyTheOther(name, imp.module()))).say(new ModuleMessage.TheNameIsImportedFromTwoModules(name, earlier.module(), imp.module())).build());
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
                collectRetType(p.type(), refs);
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

    private static void collectTypeRefs(Ast.TypeTerm term, List<Ast.TypeRef> refs) {
        if (term instanceof Ast.FnType fn) {
            fn.params().forEach(p -> collectRetType(p, refs));
            collectRetType(fn.result(), refs);
            return;
        }
        if (!(term instanceof Ast.TypeRef ref)) {
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
