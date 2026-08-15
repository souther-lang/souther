package souther.compiler.query;

import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.check.BehaviorRequirement;
import souther.compiler.check.DataChecker;
import souther.compiler.check.HelperInliner;
import souther.compiler.check.HelperGraph;
import souther.compiler.check.HelperNames;
import souther.compiler.check.HelperTable;
import souther.compiler.check.InjectionSigs;
import souther.compiler.check.InliningPolicy;
import souther.compiler.check.InvariantChecker;
import souther.compiler.check.Lower;
import souther.compiler.check.PipelineSigs;
import souther.compiler.check.ReqSig;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeChecker;
import souther.compiler.check.TypeOps;
import souther.compiler.check.Unanswerable;
import souther.compiler.core.Core;
import souther.compiler.core.GrowingFold;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.ModuleMessage;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.SequencedSet;
import java.util.Set;

/**
 * What the code in a module comes to: the signatures of the behaviors it declares and of the ones
 * it borrows, the bodies with their helper calls expanded, and the result of checking them.
 */
public final class Bodies {

    private Bodies() {}

    /** The behaviors of a module that are injection targets — declared with a spec and no fn, so
     * something else supplies the body. */
    public record Injected(String name) implements Key<Set<String>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Set<String>> compute(Db db) {
            Front.FromPath.OnThePath onThePath = Front.onThePath(db, name);
            if (onThePath != null) {
                // A module off the path published which of its behaviors are injection targets,
                // because the fn that decides is not published with it.
                return Answer.of(onThePath.injectedBehaviors());
            }
            Ast.Module m = db.ask(new Front.Available(name)).value();
            if (m == null) {
                return Answer.of(Set.of());
            }
            Set<String> fns = new LinkedHashSet<>();
            for (Ast.FnDef f : m.fns()) {
                fns.add(f.name());
            }
            Set<String> injected = new LinkedHashSet<>();
            for (Ast.BehaviorDef b : m.behaviors()) {
                if (b instanceof Ast.SpecBehavior && !fns.contains(b.name())) {
                    injected.add(b.name());
                }
            }
            return Answer.of(Ordered.set(injected));
        }
    }

    /**
     * The behaviors of a module a body may call by name: the ones whose requirement set is empty
     * (spec {@code [#calling-a-behavior]}). Those are the behaviors written with a {@code let} and
     * no {@code depends on} — an injection target requires itself, and one that writes the clause is
     * reached through that clause instead.
     *
     * <p>A composition is not here. Its requirements are inferred from its stages rather than
     * written, so a caller resting on one would take on a set that changes when an upstream stage
     * changes — the reason a composition may not be named in {@code depends on} either.
     *
     * <p>A module read from the path published no {@code let}, so which of its behaviors are
     * injection targets is asked of {@link Injected} rather than read off the fns, exactly as that
     * key does. What it did publish is the declaration, so its {@code depends on} is here to read.
     */
    public record Callable(String name) implements Key<Set<String>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Set<String>> compute(Db db) {
            Ast.Module m = db.ask(new Front.Available(name)).value();
            if (m == null) {
                return Answer.of(Set.of());
            }
            Set<String> injected = db.ask(new Injected(name)).value();
            Set<String> callable = new LinkedHashSet<>();
            for (Ast.BehaviorDef b : m.behaviors()) {
                if (b instanceof Ast.SpecBehavior spec
                        && (injected == null || !injected.contains(spec.name()))
                        && spec.dependsOn().isEmpty()) {
                    callable.add(spec.name());
                }
            }
            return Answer.of(Ordered.set(callable));
        }
    }

    /**
     * The behaviors of a module whose requirement set is not empty — what a {@code depends on} clause
     * may name (spec {@code [#depends-on]}). An injection target is one because it requires itself; a
     * behavior written with a {@code let} is one when it writes a {@code depends on} of its own.
     *
     * <p>A composition is not here. Its requirements are inferred from its stages rather than
     * written, so a caller resting on one would take on a set that changes when an upstream stage
     * changes.
     */
    public record Dependencies(String name) implements Key<Set<String>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Set<String>> compute(Db db) {
            Ast.Module m = db.ask(new Front.Available(name)).value();
            if (m == null) {
                return Answer.of(Set.of());
            }
            Set<String> injected = db.ask(new Injected(name)).value();
            Set<String> result = new LinkedHashSet<>();
            for (Ast.BehaviorDef b : m.behaviors()) {
                if (!(b instanceof Ast.SpecBehavior spec)) {
                    continue;
                }
                if ((injected != null && injected.contains(spec.name()))
                        || !spec.dependsOn().isEmpty()) {
                    result.add(spec.name());
                }
            }
            return Answer.of(Ordered.set(result));
        }
    }

    /** The behaviors a module borrows whose requirement set is not empty where they are declared. */
    public record ImportedDependencies(String name) implements Key<Set<String>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Set<String>> compute(Db db) {
            if (db.ask(new Front.Available(name)).value() == null) {
                return Answer.of(Set.of());
            }
            Set<String> result = new LinkedHashSet<>();
            for (Ast.Import imp : Names.importsOf(db, name)) {
                Set<String> deps = db.ask(new Dependencies(imp.module())).value();
                if (deps == null) {
                    continue;
                }
                for (String bare : imp.names()) {
                    if (deps.contains(bare)) {
                        result.add(bare);
                    }
                }
            }
            return Answer.of(Ordered.set(result));
        }
    }

    /** The behaviors a module borrows that may be called by name where they are declared. */
    public record ImportedCallable(String name) implements Key<Set<String>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Set<String>> compute(Db db) {
            if (db.ask(new Front.Available(name)).value() == null) {
                return Answer.of(Set.of());
            }
            Set<String> result = new LinkedHashSet<>();
            for (Ast.Import imp : Names.importsOf(db, name)) {
                Set<String> callable = db.ask(new Callable(imp.module())).value();
                if (callable == null) {
                    continue;
                }
                for (String bare : imp.names()) {
                    if (callable.contains(bare)) {
                        result.add(bare);
                    }
                }
            }
            return Answer.of(Ordered.set(result));
        }
    }

    /** The signatures of the behaviors a module declares. */
    public record Signatures(String name) implements Key<Map<String, Sig>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, Sig>> compute(Db db) {
            Answer<souther.compiler.check.Desugared.Module> desugared =
                    db.ask(new Shapes.Desugared(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<String, Sig>> imported = db.ask(new Imported(name));
            if (!desugared.present() || !scope.present() || !imported.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(PipelineSigs.signatures(desugared.value().behaviors(),
                        scope.value(), imported.value()));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
        }
    }

    /**
     * The signatures of the behaviors a module borrows from others, under the bare names it reaches
     * them by. A qualified behavior reference has already become an import, so the imports are the
     * whole list.
     */
    public record Imported(String name) implements Key<Map<String, Sig>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, Sig>> compute(Db db) {
            // A module in a cycle borrows a signature from a module that borrows one from it. This
            // is where that would be asked, so this is where it stops; the cycle itself is reported
            // by Names.InCycle.
            if (Names.cyclic(db, name)) {
                return Answer.absent();
            }
            if (db.ask(new Front.Available(name)).value() == null) {
                return Answer.absent();
            }
            Map<String, Sig> result = new LinkedHashMap<>();
            Map<String, String> fromModule = new LinkedHashMap<>();   // bare name → its module
            for (Ast.Import imp : Names.importsOf(db, name)) {
                Ast.Module src = db.ask(new Front.Available(imp.module())).value();
                if (src == null) {
                    continue;   // the unknown module is reported where the scope is worked out
                }
                Set<String> declared = Names.behaviorNames(src);
                for (String bare : imp.names()) {
                    if (!declared.contains(bare)) {
                        continue;   // a type import, or a name the module does not declare
                    }
                    Map<String, Sig> sigs = db.ask(new Signatures(imp.module())).value();
                    Sig sig = sigs == null ? null : sigs.get(bare);
                    if (sig == null) {
                        continue;
                    }
                    String earlier = fromModule.put(bare, imp.module());
                    if (earlier != null && !earlier.equals(imp.module())) {
                        return Answer.absent(collision(bare, earlier, imp));
                    }
                    result.put(bare, sig);
                }
            }
            return Answer.of(Ordered.map(result));
        }

        /**
         * The same bare behavior name arrived from two modules. Unlike a type, a behavior name is
         * also a member name in the generated class — an injected behavior is a field, and a stage
         * that is one becomes a field here too — so the two cannot both be reached.
         */
        private Report collision(String bare, String earlier, Ast.Import imp) {
            return Report.raised(Diagnostic.say(new ModuleMessage.ABehaviorIsNamedFromTwoModules(bare, earlier, imp.module()))
                            .at(imp.pos())
                            .hint(new ModuleMessage.ABehaviorsNameIsAlsoItsInjectedField(bare)).build());
        }
    }

    /** The behaviors a module borrows that are injection targets where they are declared, so a
     * composition here inherits them as requirements of its own. */
    public record ImportedInjected(String name) implements Key<Set<String>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Set<String>> compute(Db db) {
            if (db.ask(new Front.Available(name)).value() == null) {
                return Answer.of(Set.of());
            }
            Set<String> result = new LinkedHashSet<>();
            for (Ast.Import imp : Names.importsOf(db, name)) {
                Set<String> injected = db.ask(new Injected(imp.module())).value();
                if (injected == null) {
                    continue;
                }
                for (String bare : imp.names()) {
                    if (injected.contains(bare)) {
                        result.add(bare);
                    }
                }
            }
            return Answer.of(Ordered.set(result));
        }
    }

    /**
     * What each behavior of a module requires injected to be constructed, and which definitions ask
     * for it ({@link Requirements}).
     *
     * <p>The order is the injecting constructor's parameter order, so it is also the order an
     * example passes its fakes in: the emitter and the example verifier ask this one question rather
     * than each walking the stages, because a fake bound to the wrong parameter is not something
     * either side would notice.
     *
     * <p>Read off the lowered module — the same tree the backend emits from — so the two cannot be
     * looking at different behaviors.
     */
    public record Requirements(String name) implements Key<Map<String, List<BehaviorRequirement>>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, List<BehaviorRequirement>>> compute(Db db) {
            Answer<Lower.Lowered> lowering = db.ask(new Lowering(name));
            Answer<Set<String>> injected = db.ask(new ImportedInjected(name));
            if (!lowering.present() || !injected.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(Ordered.map(souther.compiler.check.Requirements.of(
                        lowering.value().lowered(), injected.value())));
            } catch (CompileException e) {
                // A composition that reaches itself has no requirement set to work out. The cycle is
                // reported where it is written; nothing is emitted for the module either way.
                return Answer.absent(e);
            }
        }
    }

    /**
     * The signatures of the behaviors a module injects — its own targets and the imported ones it names (spec
     * §injected-behavior, §composition-with-requirements). What a call to one of them is typed against, both
     * where a helper's parameter types are settled and in the check itself.
     *
     * <p>A signature that does not build is not reported here: the check reports it where it reports
     * it today, and settling reads what it can and leaves the rest to the annotation rule. Answering
     * with nothing at all would make every helper in the module undetermined on top of the real
     * error.
     */
    public record ReqSigs(String name) implements Key<Map<String, ReqSig>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, ReqSig>> compute(Db db) {
            Answer<souther.compiler.check.Prepared> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<String, Sig>> imported = db.ask(new Imported(name));
            Answer<Set<String>> own = db.ask(new Dependencies(name));
            Answer<Set<String>> borrowed = db.ask(new ImportedDependencies(name));
            if (!prepared.present() || !scope.present() || !imported.present()
                    || !own.present() || !borrowed.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(InjectionSigs.dependencies(prepared.value().behaviors(), scope.value(),
                        own.value(), imported.value(), borrowed.value()));
            } catch (CompileException _) {
                return Answer.of(Map.of());
            }
        }
    }

    /**
     * The signatures of the behaviors a body may call by name — its own and the imported ones it
     * names. The sibling of {@link ReqSigs}: what a call is typed against when the behavior requires
     * nothing and so arrives by being built rather than by being injected.
     *
     * <p>What this reads of the callee is its declaration. A behavior's body is not among the
     * questions here, so editing one does not re-check the behaviors that call it.
     */
    public record CalleeSigs(String name) implements Key<Map<String, ReqSig>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, ReqSig>> compute(Db db) {
            Answer<souther.compiler.check.Prepared> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<String, Sig>> imported = db.ask(new Imported(name));
            Answer<Set<String>> own = db.ask(new Callable(name));
            Answer<Set<String>> borrowed = db.ask(new ImportedCallable(name));
            if (!prepared.present() || !scope.present() || !imported.present()
                    || !own.present() || !borrowed.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(InjectionSigs.callable(prepared.value().behaviors(), scope.value(), own.value(),
                        imported.value(), borrowed.value()));
            } catch (CompileException _) {
                return Answer.of(Map.of());
            }
        }
    }

    /**
     * How many inputs each behavior a body of this module may name takes.
     *
     * <p>A name written where a value goes becomes the function it names, and all that becoming one
     * needs is how many arguments it takes (spec {@code [#blocks]}). {@link CalleeSigs} already says
     * which behaviors may be named here and what they take; this is that answer with the types
     * dropped, because the expansion is written before anything is typed.
     *
     * <p>Its own question rather than a read of {@link CalleeSigs} at the expansion, so a change to a
     * behavior's input <em>types</em> does not expand every body of the module again.
     */
    public record NamedBehaviorArity(String name) implements Key<Map<String, Integer>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, Integer>> compute(Db db) {
            Answer<Map<String, ReqSig>> sigs = db.ask(new CalleeSigs(name));
            if (!sigs.present()) {
                return Answer.absent();
            }
            return Answer.of(Ordered.map(InjectionSigs.arities(sigs.value())));
        }
    }

    /** A module with every helper parameter the author left unwritten carrying the type its body
     * gives it — the surface tree the check reads its declarations from. */
    public record Settled(String name) implements Key<Hir.Module> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Hir.Module> compute(Db db) {
            Answer<souther.compiler.check.Prepared> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<String, ReqSig>> reqSigs = db.ask(new ReqSigs(name));
            if (!prepared.present() || !scope.present() || !reqSigs.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(Lower.settle(prepared.value(), scope.value(), reqSigs.value()));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
        }
    }

    /**
     * The definitions some module wrote that a body of this one can name, settled, keyed by the name
     * it reaches each of them by: what this module has as fns of its own, and what its imports publish
     * to it.
     *
     * <p>Not what the module owns. A definition another module publishes is one this module expands
     * at the call and not one it declares or emits, so a reader asking what the module holds is asking
     * something else and must not read this. The table a body is expanded against is handed the two
     * apart, and {@link Expanding} is where that is done.
     *
     * <p>Not everything a name reaches, either. The standard library is under every module and is
     * written nowhere here; it joins where a table is built, under {@link InliningPolicy#FULL}, so
     * {@link HelperTable#reachable()} is the wider set and is what "reachable" means.
     *
     * <p>Its own question, and a map of definitions rather than an inliner, because that is what makes
     * it an answer two bodies can share: a helper says what it says whatever the behavior beside it
     * was edited to, so a body that reads this is left alone. An inliner cannot do that job — nothing
     * says when two of them are the same, so every reader of one would run again whatever changed.
     */
    public record ModuleDefinitions(String name) implements Key<Map<String, Hir.FnDef>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, Hir.FnDef>> compute(Db db) {
            Answer<Hir.Module> settled = db.ask(new Settled(name));
            if (!settled.present()) {
                return Answer.absent();
            }
            Answer<Map<String, Hir.FnDef>> imported = db.ask(new ImportedDefinitions(name));
            if (!imported.present()) {
                return Answer.absent();
            }
            Map<String, Hir.FnDef> helpers = new LinkedHashMap<>(imported.value());
            // What this module has, both components of it: a body may name a helper it took on to
            // emit exactly as it names one it declared, and a row may apply either.
            helpers.putAll(HelperInliner.helpersOf(settled.value()));
            helpers.putAll(HelperInliner.takenOnBy(settled.value()));
            return Answer.of(helpers);
        }
    }

    /**
     * What the modules this one imports publish to it, each closed where it was written and named by
     * the module that declares it.
     *
     * <p>A definition another module publishes is expanded here like one of this module's own: a value
     * is substituted at its references (ADR-0072), a helper at its call sites (spec §blocks). What
     * arrives is closed — the body with its own module's definitions already substituted into it — so
     * the only name of the declaring module that reaches this one is the definition's own. A body
     * carrying those names would be read against the definitions here, and a reader that happens to
     * spell one the same way would change what the definition means (ADR-0067).
     *
     * <p>What a published body does not close over is a recursive helper, which is a method rather
     * than an expression. Those come too, under the name of the module that declares them, and so does
     * every recursive helper they reach in turn — a mutually-recursive group arrives whole, and one
     * the reader never imported arrives because the body it was published inside calls it. The reader
     * emits them as its own methods (see {@link Shapes.Prepared}).
     *
     * <p>Read from the imports of the resolved module, which is the earliest answer carrying them.
     * What a module imports is written down and is not something desugaring or settling decides, so
     * reading it there is what leaves every later stage free to read this — {@link Shapes.Derived}
     * among them, which settles the invariants and would ask through itself for any answer below it.
     */
    public record ImportedDefinitions(String name) implements Key<Map<String, Hir.FnDef>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, Hir.FnDef>> compute(Db db) {
            // A module in a cycle takes a published body from a module that takes one from it. This is
            // where that would be asked, so this is where it stops; the cycle itself is reported by
            // Names.InCycle.
            if (Names.cyclic(db, name)) {
                return Answer.absent();
            }
            Answer<Hir.Module> resolved = db.ask(new Names.Resolved(name));
            if (!resolved.present()) {
                return Answer.absent();
            }
            Map<String, Hir.FnDef> out = new LinkedHashMap<>();
            for (Hir.Import imp : resolved.value().imports()) {
                Answer<Hir.Module> from = db.ask(new Settled(imp.module()));
                // Closed against the table that module's own bodies are expanded against, which is
                // everything it can name and not only what it declares: a published body may call a
                // helper that module imported in turn, and a chain of three is where a table of its
                // own definitions leaves the middle one unexpanded.
                //
                // Its table and not a map of the same entries. A map says which declarations are
                // there and nothing about which relation each is in, so handing one over is handing
                // over the question of what it means — and the answer taken here would be this
                // module's guess about another module's declarations.
                Answer<Expanding.Of> against =
                        db.ask(new Expanding(imp.module(), InliningPolicy.FULL));
                if (!from.present() || !against.present()) {
                    continue;
                }
                // Two imports reaching one definition reach one definition: the name it is keyed by
                // is the module that declares it and its own name, so the second arrival is the same
                // entry rather than a second copy of the method.
                publishedClosure(from.value(), imp.names(), against.value())
                        .forEach(out::putIfAbsent);
            }
            return Answer.of(out);
        }
    }

    /**
     * The values and helpers {@code from} publishes among {@code wanted}, each closed over its own
     * module.
     *
     * <p>Closing them there is what keeps a published definition meaning what it meant where it was
     * written. It is substituted at its references, so a body still naming its module's own
     * definitions would be read against the reader's, and a reader that spells one the same way would
     * silently change it. Expanding it first leaves a body that names nothing of the declaring
     * module — except a recursive helper, which is a method rather than an expression and so is left
     * standing as a call under its declaring module's qualified name (see {@link
     * HelperInliner#closeAcross}); the reader emits that method as its own.
     *
     * <p>The value and the helper are told apart by the one predicate that decides it anywhere — a
     * written parameter list — and not by a second record of the same line. What each becomes in the
     * reader follows from the same shape: a definition with no parameters is substituted where it is
     * named, one with parameters is expanded where it is called.
     */
    public static Map<String, Hir.FnDef> publishedDefinitions(Hir.Module from, List<String> wanted,
                                                              Expanding.Of against) {
        Map<String, Hir.FnDef> out = new LinkedHashMap<>();
        HelperInliner inliner = null;
        for (Hir.FnDef fn : publishable(from, wanted)) {
            if (inliner == null) {
                inliner = HelperInliner.over(against.table(), against.graph());
            }
            Hir.FnDef closed = inliner.closeAcross(fn, from.name());
            out.put(closed.name(), closed);
        }
        return out;
    }

    /**
     * The definitions {@code from} publishes among {@code wanted}, together with every recursive
     * helper of {@code from} they reach.
     *
     * <p>Closing a body removes every name of the declaring module from it except a recursive helper's,
     * which is a method and stays a call. That call has to land on something, so the helper travels
     * with the body that calls it — and, since a recursive helper may call another, so does everything
     * it reaches in turn. A mutually-recursive group therefore arrives whole: each member is reached
     * from the others, so following the calls collects all of them.
     */
    public static Map<String, Hir.FnDef> publishedClosure(Hir.Module from, List<String> wanted,
                                                          Expanding.Of against) {
        Map<String, Hir.FnDef> out = publishedDefinitions(from, wanted, against);
        if (out.isEmpty()) {
            return out;
        }
        HelperInliner inliner = HelperInliner.over(against.table(), against.graph());
        Deque<String> work = new ArrayDeque<>(out.keySet());
        while (!work.isEmpty()) {
            for (ValueName.Helper reached : HelperNames.helpersReached(out.get(work.poll()).writtenBody())) {
                String qualified = HelperNames.qualified(reached.module(), reached.name());
                if (out.containsKey(qualified)) {
                    continue;
                }
                // The declaring module decides both how the helper is keyed in {@code from}'s own
                // table and whether it still has to be closed: one of `from`'s own is written bare
                // there and closed here, one that reached `from` from further up is already keyed and
                // closed by the module that declares it, and is passed along as it stands.
                boolean ownHelper = reached.module().equals(from.name());
                // Asked of what the name reaches there, which is the one relation this module has any
                // business asking of another module's table.
                Hir.FnDef def =
                        against.table().reached(ownHelper ? reached.name() : qualified);
                if (def == null) {
                    continue;   // a prelude helper, which every module emits for itself
                }
                out.put(qualified, ownHelper ? inliner.closeAcross(def, from.name()) : def);
                work.add(qualified);
            }
        }
        return out;
    }

    /** The bare names {@code from} publishes among {@code wanted} — what a reader writes for them.
     * Asked on its own where only the names are wanted, so resolving a module's names does not close
     * every body the modules around it publish. */
    public static Set<String> publishedNames(Hir.Module from, List<String> wanted) {
        Set<String> out = new java.util.LinkedHashSet<>();
        for (Hir.FnDef fn : publishable(from, wanted)) {
            out.add(fn.name());
        }
        return out;
    }

    /** The definitions {@code from} offers among {@code wanted}: its values and helpers that it
     * exposes. A behavior's own {@code let} is not among them whatever its shape — it is an
     * implementation, and what a reader reaches is the behavior, which it calls (ADR-0005). */
    private static List<Hir.FnDef> publishable(Hir.Module from, List<String> wanted) {
        Set<String> exposed = new java.util.HashSet<>(from.exposing());
        List<Hir.FnDef> out = new java.util.ArrayList<>();
        for (Hir.FnDef fn : HelperInliner.helpersOf(from).values()) {
            if (HelperInliner.publishes(exposed, fn.name(),
                    fn.body() instanceof Hir.FnBody.Written, wanted)) {
                out.add(fn);
            }
        }
        return out;
    }

    /** The helpers a module emits as methods rather than expanding: the ones that recurse (spec
     * 13.1), including the prelude ones it has taken on as its own. Answered in declaration order:
     * a check that reports one member of a mutual cycle reports the first, so the order is part of
     * the answer and is said in the type. */
    public record RecursiveHelpers(String name) implements Key<SequencedSet<String>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<SequencedSet<String>> compute(Db db) {
            Answer<HelperInliner> inliner = expanding(db, name, InliningPolicy.FULL);
            return inliner.present() ? Answer.of(inliner.value().recursiveHelpers())
                    : Answer.absent();
        }
    }

    /**
     * What a body of {@code module} is expanded against: which declaration each name reaches, and
     * which of them recurse.
     *
     * <p>Both are facts about the module's declarations and neither is about any one body, so they
     * are worked out once. Before this every question that expanded something built its own —
     * walking each of the standard library's hundred-odd bodies again for each — and the answers only
     * agreed because they were computed the same way.
     *
     * <p>Keyed by the policy as well as the module, because the two policies are two tables: the
     * discharge representation leaves the language's own operations standing, so it does not have
     * them to call and does not find them recursive. One answer shared by both would put the fold
     * that {@code List.map} is into the tree the discharge rules read.
     */
    public record Expanding(String name, InliningPolicy policy) implements Key<Expanding.Of> {

        /** @param table which declaration each name reaches
         *  @param graph what each of them calls, and which of them recurse */
        public record Of(HelperTable table, HelperGraph graph) {}

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Of> compute(Db db) {
            Answer<Hir.Module> settled = db.ask(new Settled(name));
            Answer<Map<String, Hir.FnDef>> imported = db.ask(new ImportedDefinitions(name));
            if (!settled.present() || !imported.present()) {
                return Answer.absent();
            }
            // The two are handed over apart, which is what {@link ModuleDefinitions} has already joined: a
            // definition another module publishes is one this module expands and not one it has as a
            // fn of its own. Joined here, a table built for this module would answer that it holds a
            // published helper, and the table the check builds — which is handed the same two apart —
            // would answer that it does not.
            HelperTable table = HelperTable.of(settled.value(), imported.value(), policy);
            return Answer.of(new Of(table, HelperGraph.of(table)));
        }
    }

    /** An inliner over {@link Expanding}'s answer — a fresh one, because an expansion writes bindings
     * as it runs and what it writes belongs to the body it is written into. */
    private static Answer<HelperInliner> expanding(Db db, String module, InliningPolicy policy) {
        Answer<Expanding.Of> against = db.ask(new Expanding(module, policy));
        return against.present()
                ? Answer.of(HelperInliner.over(against.value().table(), against.value().graph()))
                : Answer.absent();
    }

    /**
     * The methods a module emits for its rows: one per operand, answering with the value that
     * operand is.
     *
     * <p>The names come from the correspondence the preparation constructed, not from a count of the
     * settled module's rows: a second count is a second numbering, and a row would run the operand
     * beside the one it wrote.
     *
     * <p>Nothing else is here. A helper a row names is expanded into the operand's own definition,
     * the way it is expanded into any body, so it needs no method of its own; a recursive one it
     * reaches is a method already, for the reason every recursion is.
     */
    public record RowMethods(String name) implements Key<Set<String>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Set<String>> compute(Db db) {
            Answer<souther.compiler.check.Prepared> prepared = db.ask(new Shapes.Prepared(name));
            return prepared.present()
                    ? Answer.of(new LinkedHashSet<>(prepared.value().operandMethods().values()))
                    : Answer.absent();
        }
    }

    /**
     * One settled fn, so what a body is expanded from is the fn itself and not the module it sits in.
     *
     * <p>A projection, not a settling of its own: the module is settled together — one helper's
     * settled type can settle the next one's — and this reads one fn out of the result. The
     * difference matters because it is what a reader depends on that decides how far an edit
     * travels, not what the work was. Settling per definition, if it is ever worth it, goes behind
     * this without any reader noticing.
     */
    public record SettledFn(String module, String fn) implements Key<Hir.FnDef> {

        @Override
        public Answer<Hir.FnDef> compute(Db db) {
            Answer<Hir.Module> settled = db.ask(new Settled(module));
            if (!settled.present()) {
                return Answer.absent();
            }
            // Either component: a body is asked for by name, and a helper the module took on to emit
            // has one to expand exactly as one it declared does.
            for (List<Hir.FnDef> component : List.of(
                    settled.value().fns(), settled.value().takenOn())) {
                for (Hir.FnDef candidate : component) {
                    if (candidate.name().equals(fn)) {
                        return Answer.of(candidate);
                    }
                }
            }
            return Answer.absent();
        }
    }

    /**
     * One body as the backend emits it: its helper calls expanded and its comprehensions desugared.
     *
     * <p>What it reads is the fn itself and the helpers around it, so editing another body in the same
     * module does not expand this one again.
     */
    public record LoweredBody(String module, String fn) implements Key<Hir.FnDef> {

        @Override
        public Answer<Hir.FnDef> compute(Db db) {
            Answer<Hir.FnDef> def = db.ask(new SettledFn(module, fn));
            Answer<HelperInliner> inliner = expanding(db, module, InliningPolicy.FULL);
            Answer<SequencedSet<String>> recursive = db.ask(new RecursiveHelpers(module));
            Answer<Map<String, Integer>> behaviors = db.ask(new NamedBehaviorArity(module));
            if (!def.present() || !inliner.present() || !recursive.present()
                    || !behaviors.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(Lower.body(def.value(),
                        inliner.value().namingBehaviors(behaviors.value()),
                        recursive.value().contains(fn), dependencyParams(db, module, fn)));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
        }
    }

    /**
     * One body as the invariant-discharge analysis reads it: the module's own helpers expanded, the
     * language's own operations left standing ({@link InliningPolicy#DISCHARGE}).
     *
     * <p>Not the tree the backend emits. That one has been expanded until nothing it cannot emit is
     * left, and reading it is reading algorithms — a {@code List.map} is a fold there, and a rule
     * about what {@code List.map} does to a length has nothing to match. This is the same body at the
     * level the rules are written at.
     */
    public record BodyForInvariantDischarge(String module, String fn) implements Key<Hir.FnDef> {

        @Override
        public Answer<Hir.FnDef> compute(Db db) {
            Answer<Hir.FnDef> def = db.ask(new SettledFn(module, fn));
            Answer<HelperInliner> inliner = expanding(db, module, InliningPolicy.DISCHARGE);
            Answer<SequencedSet<String>> recursive = db.ask(new RecursiveHelpers(module));
            Answer<Map<String, Integer>> behaviors = db.ask(new NamedBehaviorArity(module));
            if (!def.present() || !inliner.present() || !recursive.present()
                    || !behaviors.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(Lower.body(def.value(),
                        inliner.value().namingBehaviors(behaviors.value()),
                        recursive.value().contains(fn), dependencyParams(db, module, fn)));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
        }
    }

    /**
     * A module with every helper call expanded into the body that called it, and with the parameter
     * types those expansions settled written back into the declarations.
     *
     * <p>The bodies are asked for one at a time; what is left here is which fns survive to the
     * backend — a behavior's implementation and a recursive helper — which is a fact about the module
     * rather than about any one of them.
     */
    public record Lowering(String name) implements Key<Lower.Lowered> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Lower.Lowered> compute(Db db) {
            Answer<Hir.Module> settled = db.ask(new Settled(name));
            Answer<SequencedSet<String>> recursive = db.ask(new RecursiveHelpers(name));
            Answer<Set<String>> rowMethods = db.ask(new RowMethods(name));
            if (!settled.present() || !recursive.present() || !rowMethods.present()) {
                return Answer.absent();
            }
            Set<String> behaviors = Names.behaviorNames(settled.value());
            // A name is one question, so a name written twice is asked once and answered by the
            // first. The check reports the duplicate and this module is not emitted; what it must
            // not do is carry the same body twice. Shared across both components because a module
            // that took on a helper it also declares would otherwise emit two of it.
            Set<String> taken = new LinkedHashSet<>();
            List<List<Hir.FnDef>> lowered = new ArrayList<>();
            // Both, and each stays where it was: what becomes a method is one question and what this
            // module declared is another, and the backend reads the first while every rule about the
            // declaring module reads the second.
            for (List<Hir.FnDef> component : List.of(
                    settled.value().fns(), settled.value().takenOn())) {
                List<Hir.FnDef> fns = new ArrayList<>();
                for (Hir.FnDef fn : component) {
                    // A non-recursive helper is fully inlined at its call sites and never
                    // emitted — it has no body of its own down here, so nothing asks for one. What
                    // survives beside the behaviors is a recursion, which cannot be inlined, and a
                    // method a row's operand is, which is the row's value and has no call site.
                    if (!behaviors.contains(fn.name()) && !recursive.value().contains(fn.name())
                            && !rowMethods.value().contains(fn.name())) {
                        continue;
                    }
                    if (!taken.add(fn.name())) {
                        continue;
                    }
                    Answer<Hir.FnDef> body = db.ask(new LoweredBody(name, fn.name()));
                    if (!body.present()) {
                        // Why is the body's to say, and it said it. A module with a body that does
                        // not expand has none to emit.
                        return Answer.absent();
                    }
                    fns.add(body.value());
                }
                lowered.add(fns);
            }
            return Answer.of(new Lower.Lowered(settled.value(),
                    Lower.lowered(settled.value(), lowered.get(0), lowered.get(1))));
        }
    }

    /** The signatures of a module's recursive helpers — what a self- or mutual call is typed
     * against, and what every body that calls one reads. */
    public record RecursiveHelperSigs(String name) implements Key<Map<String, Type>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, Type>> compute(Db db) {
            Answer<HelperInliner> inliner = expanding(db, name, InliningPolicy.FULL);
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            if (!inliner.present() || !scope.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(TypeChecker.recursiveHelperSigs(inliner.value(), scope.value()));
            } catch (CompileException e) {
                // A recursive helper that does not say what it returns costs the signatures of all of
                // them, and there is no module to check without them.
                return Answer.absent(e);
            }
        }
    }

    /** What each recursive helper constructs, transitively. A recursive helper is not inlined, so its
     * constructions are attributed to the behavior that calls it (spec §blocks). */
    public record RecursiveHelperConstructs(String name)
            implements Key<Map<String, DataChecker.Constructs>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, DataChecker.Constructs>> compute(Db db) {
            Answer<HelperInliner> inliner = expanding(db, name, InliningPolicy.FULL);
            Answer<Map<String, Type>> sigs = db.ask(new RecursiveHelperSigs(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            if (!inliner.present() || !sigs.present() || !scope.present()) {
                return Answer.absent();
            }
            Map<String, Hir.Expr> bodies = new LinkedHashMap<>();
            for (String helper : sigs.value().keySet()) {
                Answer<Hir.FnDef> body = db.ask(new LoweredBody(name, helper));
                if (!body.present()) {
                    return Answer.absent();
                }
                bodies.put(helper, body.value().writtenBody());
            }
            try {
                return Answer.of(TypeChecker.recursiveHelperConstructs(sigs.value().keySet(), bodies,
                        inliner.value(), scope.value()));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
        }
    }

    /** The names of the behaviors a module declares — what a body reads to tell a call to one of them
     * from a call to anything else. */
    public record BehaviorNames(String name) implements Key<Set<String>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Set<String>> compute(Db db) {
            Answer<Hir.Module> settled = db.ask(new Settled(name));
            return settled.present()
                    ? Answer.of(Names.behaviorNames(settled.value())) : Answer.absent();
        }
    }

    /** What {@code fn}'s behavior declares in {@code depends on}, or nothing where {@code fn}
     * implements no behavior — a helper has no such parameters (spec §depends-on). */
    private static Set<String> dependencyParams(Db db, String module, String fn) {
        Answer<Hir.SpecBehavior> spec = db.ask(new Spec(module, fn));
        if (!spec.present()) {
            return Set.of();
        }
        Set<String> names = new HashSet<>();
        for (Hir.Var req : spec.value().dependsOn()) {
            // Reported where it is written; it names no parameter for a body to be held to.
            if (req.answered() instanceof Hir.Var.Denoting named) {
                names.add(named.bare());
            }
        }
        return names;
    }

    /** One behavior's declaration, so what a body is checked against is the behavior it implements
     * and not the module it sits in. */
    public record Spec(String module, String behavior) implements Key<Hir.SpecBehavior> {

        @Override
        public Answer<Hir.SpecBehavior> compute(Db db) {
            Answer<Hir.Module> settled = db.ask(new Settled(module));
            if (!settled.present()) {
                return Answer.absent();
            }
            for (Hir.BehaviorDef b : settled.value().behaviors()) {
                if (b instanceof Hir.SpecBehavior spec && spec.name().equals(behavior)) {
                    return Answer.of(spec);
                }
            }
            return Answer.absent();
        }
    }

    /**
     * One behavior's body checked against the behavior it implements, as the Core the backend emits.
     *
     * <p>What it reads is the behavior, its {@code let}, and what the module around it means. Not
     * another body — so a mistake in one behavior is that behavior's, and editing one leaves the rest
     * of the file alone.
     */
    public record CheckedBehavior(String module, String behavior) implements Key<Core> {

        @Override
        public Answer<Core> compute(Db db) {
            Answer<Hir.SpecBehavior> spec = db.ask(new Spec(module, behavior));
            Answer<Hir.FnDef> fn = db.ask(new SettledFn(module, behavior));
            Answer<Hir.FnDef> body = db.ask(new LoweredBody(module, behavior));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(module));
            Answer<Map<String, ReqSig>> calleeSigs = db.ask(new CalleeSigs(module));
            Answer<Map<String, ReqSig>> reqSigs = db.ask(new ReqSigs(module));
            Answer<HelperInliner> inliner = expanding(db, module, InliningPolicy.FULL);
            Answer<Map<String, Type>> sigs = db.ask(new RecursiveHelperSigs(module));
            Answer<Map<String, DataChecker.Constructs>> constructs =
                    db.ask(new RecursiveHelperConstructs(module));
            Answer<Hir.FnDef> discharge = db.ask(new BodyForInvariantDischarge(module, behavior));
            Answer<Map<TypeSymbol, List<Hir.InvariantClause>>> dischargeInvariants =
                    db.ask(new Shapes.InvariantsForDischarge(module));
            if (!spec.present() || !fn.present() || !body.present() || !scope.present()
                    || !calleeSigs.present() || !reqSigs.present() || !inliner.present()
                    || !sigs.present() || !constructs.present()) {
                return Answer.absent();
            }
            // The invariant-discharge analysis reads its own representation of the body and of the
            // invariants (spec §invariant-discharge). Where it is not available the check is skipped
            // rather than run against the emitted tree, whose operations are no longer operations.
            InvariantChecker.Source dischargeSource = discharge.present()
                    ? new InvariantChecker.Source(discharge.value().writtenBody(),
                            dischargeInvariants.present() ? dischargeInvariants.value() : Map.of())
                    : null;
            List<Diagnostic> warnings = new ArrayList<>();
            try {
                Core core = TypeChecker.checkBehavior(spec.value(), fn.value(), body.value().writtenBody(),
                        dischargeSource, scope.value(), calleeSigs.value(), reqSigs.value(),
                        inliner.value(), sigs.value(), constructs.value(),
                        warnings);
                List<Report> reports = new ArrayList<>();
                for (Diagnostic warning : warnings) {
                    reports.add(Report.of(warning));
                }
                // The last thing done to a body before it is emitted, and the only one that is not a
                // check: a fold that only grows a list is turned into a build (see GrowingFold).
                return Answer.of(GrowingFold.rewrite(core), reports);
            } catch (Unanswerable _) {
                // The name it rested on was reported where it was written. This body has no meaning
                // to emit, which the absence says, and nothing further to add.
                return Answer.absent();
            } catch (CompileException e) {
                return Answer.absent(e);
            }
        }
    }

    /**
     * What a module's own check found: its declarations, its helpers, its {@code exposing} line, its
     * compositions — everything that is not one behavior's body.
     *
     * <p>It answers whatever it found, because what it found is the answer. Whether there is a module
     * to emit is {@link Checked}'s to say, from this and every body together.
     */
    public record ModuleCheck(String name) implements Key<ModuleCheck.Of> {

        /**
         * @param emittedHelpers the bodies it elaborated, which the backend emits as methods
         * @param sound whether it found nothing wrong. An abandoned unit is wrong and says nothing
         *              of its own, so this is not the same as having reported nothing
         * @param stopped whether it stopped rather than finished, leaving the bodies nothing to be
         *                checked against
         */
        public record Of(Map<String, Core> emittedHelpers, boolean sound, boolean stopped) {}

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Of> compute(Db db) {
            Answer<Lower.Lowered> lowering = db.ask(new Lowering(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            // The signatures the check reads are the ones every other reader reads. Asked for here
            // rather than built here: a second construction would answer the boundary's question a
            // second time, and what a phase below the check is handed would be a different answer
            // that happens to agree. Absent where they did not build, which the check is told by
            // being handed nothing — it goes as far as it can without one and abandons the module
            // there, and what went wrong was reported where signatures are made.
            Answer<Map<String, Sig>> signatures = db.ask(new Signatures(name));
            Answer<Set<String>> injected = db.ask(new ImportedInjected(name));
            Answer<Map<String, ReqSig>> reqSigs = db.ask(new ReqSigs(name));
            Answer<Map<String, Type>> sigs = db.ask(new RecursiveHelperSigs(name));
            Answer<Map<String, ReqSig>> calleeSigs = db.ask(new CalleeSigs(name));
            Answer<Map<String, Hir.FnDef>> published = db.ask(new ImportedDefinitions(name));
            if (!lowering.present() || !scope.present()
                    || !injected.present() || !reqSigs.present() || !sigs.present()
                    || !calleeSigs.present() || !published.present()) {
                return Answer.absent();
            }
            TypeChecker.Reported reported;
            try {
                // The declarations that have a meaning to check, asked for one at a time. What has
                // none is not here and nothing here asks why: a reader of a declaration knows there
                // is one or there is not, and the reasons belong to the pass that settles them.
                Set<String> settled = new LinkedHashSet<>();
                for (Hir.Def def : lowering.value().settled().defs()) {
                    if (db.ask(new Names.Definition(def.declaredKey())).present()) {
                        settled.add(def.name());
                    }
                }
                Answer<souther.compiler.check.Prepared> prepared =
                        db.ask(new Shapes.Prepared(name));
                reported = TypeChecker.checkModule(lowering.value().settled(), scope.value(),
                        signatures.present() ? signatures.value() : null,
                        injected.value(), lowering.value().lowered(),
                        reqSigs.value(), calleeSigs.value(), sigs.value(), published.value(),
                        settled);
            } catch (CompileException e) {
                return Answer.absent(e);
            }
            List<Report> reports = new ArrayList<>();
            for (CompileException e : reported.errors()) {
                reports.addAll(Report.of(e));
            }
            boolean sound = reported.errors().isEmpty() && reported.abandoned().isEmpty();
            Map<String, Core> helperBodies = new LinkedHashMap<>();
            reported.emittedHelpers().forEach((h, core) -> helperBodies.put(h, GrowingFold.rewrite(core)));
            return Answer.of(new Of(helperBodies, sound, reported.stopped()), reports);
        }
    }

    /**
     * The result of type-checking a module. Absent when anything in it is wrong: a module that does
     * not check must not reach codegen, and an importer of it is skipped rather than compiled
     * against a broken module.
     *
     * <p>What each body came to is asked for one body at a time, and each of those reports what it
     * found. What is left here is the decision they and the module's own check come to together:
     * whether there is a module to emit.
     */
    /**
     * What a successful check produced for the backend (issue #81): the Core of every body it typed,
     * carrying the type decided for each node. The backend emits from these rather than translating
     * the AST and inferring the same types a second time.
     *
     * <p>Held here, where the check that produces one is asked. What makes a module's bodies these
     * is a conjunction {@link Checked} evaluates — every name came out, every body was typed, the
     * module is sound, and no type nobody could name is left in it — so this is minted there and
     * nowhere else. Somewhere a caller could build one is somewhere the conjunction is not what makes
     * it true.
     *
     * <p>Whether the check established that is the answer being there. {@code Answer} says it
     * already: absent is a check that did not, present is one that did, and this is what the one
     * that did produced. A reader wanting only the fact asks whether the answer is present.
     *
     * <p>What the check found is not in here. A warning belongs to the question that raised it, which
     * is one body, and a caller that wants them reads them from there.
     */
    public static final class Elaborated {

        private final Map<String, Core> behaviorBodies;
        private final Map<String, Core> emittedHelpers;

        private Elaborated(Map<String, Core> behaviorBodies, Map<String, Core> emittedHelpers) {
            this.behaviorBodies = behaviorBodies;
            this.emittedHelpers = emittedHelpers;
        }

        /** The Core of each behavior body, by the behavior's name. */
        public Map<String, Core> behaviorBodies() {
            return behaviorBodies;
        }

        /** The Core of each helper the module emits as a method of its own. */
        public Map<String, Core> emittedHelpers() {
            return emittedHelpers;
        }
    }

    public record Checked(String name) implements Key<Elaborated> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Elaborated> compute(Db db) {
            Answer<Hir.Module> settled = db.ask(new Settled(name));
            // Asked before any body, so a module told about its own mistakes is told about them
            // first: an author reads the file from the top, and the check of a body it declares
            // cannot come before the declaration it rests on.
            Answer<ModuleCheck.Of> module = db.ask(new ModuleCheck(name));
            if (!settled.present() || !module.present()) {
                return Answer.absent();
            }
            // Whether anything about this module's names came out wrong decides whether it can be
            // emitted, and nothing else. It must not decide whether the module is checked: the error
            // type absorbs so that the check can carry on, and stopping here would mean a mistake in
            // one declaration silencing every other definition in the file.
            boolean named = Boolean.TRUE.equals(db.ask(new Names.Sound(name)).value());
            Set<String> implemented = new LinkedHashSet<>();
            for (Hir.FnDef fn : settled.value().fns()) {
                implemented.add(fn.name());
            }
            Map<String, Core> bodies = new LinkedHashMap<>();
            boolean bodiesCheck = true;
            // A module whose own check stopped built nothing for a body to be checked against, so
            // asking would report not being able to see what has already been reported missing.
            if (!module.value().stopped()) {
                // In the order they are declared, so what the backend emits does not move with what
                // the check happened to ask for first.
                for (Hir.BehaviorDef b : settled.value().behaviors()) {
                    // An injection target has no body here — something else supplies it (spec §injected-behavior)
                    // — so there is nothing to check and nothing missing when there is none.
                    if (!(b instanceof Hir.SpecBehavior spec) || !implemented.contains(spec.name())) {
                        continue;
                    }
                    Answer<Core> core = db.ask(new CheckedBehavior(name, spec.name()));
                    if (core.present()) {
                        bodies.put(spec.name(), core.value());
                    } else {
                        bodiesCheck = false;
                    }
                }
            }
            // A unit the check could not read at all leaves the module without a meaning to emit,
            // and says nothing of its own: the name it rested on was reported where it was written.
            // Whatever else the check found is still reported, which is the point of carrying on.
            // Both, and both after the check. Sound says nothing about this module's names came out
            // wrong; the tree says it holds no type nobody could name, which can happen with nothing
            // reported here at all — an import of a module that is here and unusable leaves a hole,
            // and what is wrong was reported on that module.
            boolean sound = named
                    && bodiesCheck
                    && module.value().sound()
                    && !TypeOps.holdsAnErroneousType(settled.value());
            return sound
                    ? Answer.of(new Elaborated(bodies, module.value().emittedHelpers()))
                    : Answer.absent();
        }
    }
}
