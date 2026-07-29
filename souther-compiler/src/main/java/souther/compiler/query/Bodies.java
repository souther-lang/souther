package souther.compiler.query;

import souther.compiler.ast.Ast;
import souther.compiler.check.HelperInliner;
import souther.compiler.check.InjectionSigs;
import souther.compiler.check.Lower;
import souther.compiler.check.PipelineSigs;
import souther.compiler.check.ReqSig;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeChecker;
import souther.compiler.check.TypeOps;
import souther.compiler.check.Unanswerable;
import souther.compiler.core.Core;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
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
            Front.FromPath.Of path = db.ask(new Front.FromPath()).value();
            if (path != null && path.injected().containsKey(name)) {
                // A module off the path published which of its behaviors are injection targets,
                // because the fn that decides is not published with it.
                return Answer.of(path.injected().get(name));
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
            Ast.Module m = db.ask(new Front.Available(name)).value();
            if (m == null) {
                return Answer.of(Set.of());
            }
            Set<String> result = new LinkedHashSet<>();
            for (Ast.Import imp : m.imports()) {
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
            Ast.Module m = db.ask(new Front.Available(name)).value();
            if (m == null) {
                return Answer.of(Set.of());
            }
            Set<String> result = new LinkedHashSet<>();
            for (Ast.Import imp : m.imports()) {
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
            Answer<Ast.Module> desugared = db.ask(new Shapes.Desugared(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<String, Sig>> imported = db.ask(new Imported(name));
            if (!desugared.present() || !scope.present() || !imported.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(PipelineSigs.signatures(desugared.value(), scope.value(),
                        imported.value()));
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
            Ast.Module m = db.ask(new Front.Available(name)).value();
            if (m == null) {
                return Answer.absent();
            }
            Map<String, Sig> result = new LinkedHashMap<>();
            Map<String, String> fromModule = new LinkedHashMap<>();   // bare name → its module
            for (Ast.Import imp : m.imports()) {
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
            return Report.raised(
                    Diagnostic.of(null, "check.import.behaviordup").title("check.module.title")
                            .at(imp.pos()).args(bare, earlier, imp.module())
                            .hint("check.import.behaviordup.hint", bare).build(),
                    "behavior `" + bare + "` is named from both `" + earlier + "` and `"
                            + imp.module() + "`; one behavior name is one injected field, so this"
                            + " module cannot take both");
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
            Ast.Module m = db.ask(new Front.Available(name)).value();
            if (m == null) {
                return Answer.of(Set.of());
            }
            Set<String> result = new LinkedHashSet<>();
            for (Ast.Import imp : m.imports()) {
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
     * The signatures of the behaviors a module injects — its own targets and the imported ones it
     * names (spec 13.2, 14.3). What a call to one of them is typed against, both where a helper's
     * parameter types are settled and in the check itself.
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
            Answer<Ast.Module> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<String, Sig>> imported = db.ask(new Imported(name));
            Answer<Set<String>> own = db.ask(new Dependencies(name));
            Answer<Set<String>> borrowed = db.ask(new ImportedDependencies(name));
            if (!prepared.present() || !scope.present() || !imported.present()
                    || !own.present() || !borrowed.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(InjectionSigs.dependencies(prepared.value(), scope.value(),
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
            Answer<Ast.Module> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<String, Sig>> imported = db.ask(new Imported(name));
            Answer<Set<String>> own = db.ask(new Callable(name));
            Answer<Set<String>> borrowed = db.ask(new ImportedCallable(name));
            if (!prepared.present() || !scope.present() || !imported.present()
                    || !own.present() || !borrowed.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(InjectionSigs.callable(prepared.value(), scope.value(), own.value(),
                        imported.value(), borrowed.value()));
            } catch (CompileException _) {
                return Answer.of(Map.of());
            }
        }
    }

    /** A module with every helper parameter the author left unwritten carrying the type its body
     * gives it — the surface tree the check reads its declarations from. */
    public record Settled(String name) implements Key<Ast.Module> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Ast.Module> compute(Db db) {
            Answer<Ast.Module> prepared = db.ask(new Shapes.Prepared(name));
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
     * The module's helpers, settled — what every body in it expands its calls against.
     *
     * <p>Its own question, and a map of definitions rather than an inliner, because that is what makes
     * it an answer two bodies can share: a helper says what it says whatever the behavior beside it
     * was edited to, so a body that reads this is left alone. An inliner cannot do that job — nothing
     * says when two of them are the same, so every reader of one would run again whatever changed.
     */
    public record Helpers(String name) implements Key<Map<String, Ast.FnDef>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, Ast.FnDef>> compute(Db db) {
            Answer<Ast.Module> settled = db.ask(new Settled(name));
            if (!settled.present()) {
                return Answer.absent();
            }
            Map<String, Ast.FnDef> helpers =
                    new LinkedHashMap<>(HelperInliner.helpersOf(settled.value()));
            // A value another module publishes is expanded here like one of this module's own: it is
            // substituted at its references (ADR-0072), so what an importer needs is the body, and
            // what it names is already settled in the module that wrote it (ADR-0067).
            for (Ast.Import imp : settled.value().imports()) {
                Answer<Ast.Module> from = db.ask(new Settled(imp.module()));
                if (!from.present()) {
                    continue;
                }
                Set<String> exposed = new java.util.HashSet<>(from.value().exposing());
                for (Ast.FnDef fn : from.value().fns()) {
                    if (fn.params().isEmpty() && exposed.contains(fn.name())
                            && imp.names().contains(fn.name())) {
                        // and whatever that body reaches for on the way. Those are the published
                        // value's own workings — the reader never names them, and does not have to
                        // import them for the value to stand for what it stands for.
                        reachedValues(from.value(), fn, helpers);
                    }
                }
            }
            return Answer.of(helpers);
        }
    }

    /** Puts {@code value} and every definition of {@code from} its body reaches into {@code out}. */
    private static void reachedValues(Ast.Module from, Ast.FnDef value, Map<String, Ast.FnDef> out) {
        if (value.body() == null || out.putIfAbsent(value.name(), value) != null) {
            return;
        }
        Map<String, Ast.FnDef> declared = HelperInliner.helpersOf(from);
        for (String name : referencedNames(value.body())) {
            Ast.FnDef next = declared.get(name);
            if (next != null) {
                reachedValues(from, next, out);
            }
        }
    }

    /** Every name {@code e} writes as a value, a spread or a call, whatever each turns out to be. */
    private static Set<String> referencedNames(Ast.Expr e) {
        Set<String> names = new LinkedHashSet<>();
        collectNames(e, names);
        return names;
    }

    private static void collectNames(Ast.Expr e, Set<String> out) {
        if (e == null) {
            return;
        }
        switch (e) {
            case Ast.Var v -> out.add(v.name());
            case Ast.Call c -> out.add(c.fn());
            case Ast.NewData nd -> nd.spreads().forEach(s -> out.add(s.bare()));
            default -> { }
        }
        Ast.forEachChild(e, c -> collectNames(c, out));
    }

    /** The helpers a module emits as methods rather than expanding: the ones that recurse (spec
     * 13.1), including the prelude ones it has taken on as its own. */
    public record RecursiveHelpers(String name) implements Key<Set<String>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Set<String>> compute(Db db) {
            Answer<Map<String, Ast.FnDef>> helpers = db.ask(new Helpers(name));
            if (!helpers.present()) {
                return Answer.absent();
            }
            return Answer.of(HelperInliner.forHelpers(helpers.value()).recursiveHelpers());
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
    public record SettledFn(String module, String fn) implements Key<Ast.FnDef> {

        @Override
        public Answer<Ast.FnDef> compute(Db db) {
            Answer<Ast.Module> settled = db.ask(new Settled(module));
            if (!settled.present()) {
                return Answer.absent();
            }
            for (Ast.FnDef candidate : settled.value().fns()) {
                if (candidate.name().equals(fn)) {
                    return Answer.of(candidate);
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
    public record LoweredBody(String module, String fn) implements Key<Ast.FnDef> {

        @Override
        public Answer<Ast.FnDef> compute(Db db) {
            Answer<Ast.FnDef> def = db.ask(new SettledFn(module, fn));
            Answer<Map<String, Ast.FnDef>> helpers = db.ask(new Helpers(module));
            Answer<Set<String>> recursive = db.ask(new RecursiveHelpers(module));
            if (!def.present() || !helpers.present() || !recursive.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(Lower.body(def.value(), HelperInliner.forHelpers(helpers.value()),
                        recursive.value().contains(fn)));
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
            Answer<Ast.Module> settled = db.ask(new Settled(name));
            Answer<Set<String>> recursive = db.ask(new RecursiveHelpers(name));
            if (!settled.present() || !recursive.present()) {
                return Answer.absent();
            }
            Set<String> behaviors = Names.behaviorNames(settled.value());
            Set<String> taken = new LinkedHashSet<>();
            List<Ast.FnDef> fns = new ArrayList<>();
            for (Ast.FnDef fn : settled.value().fns()) {
                // A non-recursive helper is fully inlined at its call sites and never emitted — it has
                // no body of its own down here, so nothing asks for one.
                if (!behaviors.contains(fn.name()) && !recursive.value().contains(fn.name())) {
                    continue;
                }
                // A name is one question, so a name written twice is asked once and answered by the
                // first. The check reports the duplicate and this module is not emitted; what it must
                // not do is carry the same body twice.
                if (!taken.add(fn.name())) {
                    continue;
                }
                Answer<Ast.FnDef> body = db.ask(new LoweredBody(name, fn.name()));
                if (!body.present()) {
                    // Why is the body's to say, and it said it. A module with a body that does not
                    // expand has none to emit.
                    return Answer.absent();
                }
                fns.add(body.value());
            }
            return Answer.of(new Lower.Lowered(settled.value(),
                    Lower.lowered(settled.value(), fns)));
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
            Answer<Map<String, Ast.FnDef>> helpers = db.ask(new Helpers(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            if (!helpers.present() || !scope.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(TypeChecker.recursiveHelperSigs(
                        HelperInliner.forHelpers(helpers.value()), scope.value()));
            } catch (CompileException e) {
                // A recursive helper that does not say what it returns costs the signatures of all of
                // them, and there is no module to check without them.
                return Answer.absent(e);
            }
        }
    }

    /** What each recursive helper constructs, transitively. A recursive helper is not inlined, so its
     * constructions are attributed to the behavior that calls it (spec 12.5). */
    public record RecursiveHelperConstructs(String name)
            implements Key<Map<String, Map<TypeName, String>>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, Map<TypeName, String>>> compute(Db db) {
            Answer<Map<String, Ast.FnDef>> helpers = db.ask(new Helpers(name));
            Answer<Map<String, Type>> sigs = db.ask(new RecursiveHelperSigs(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            if (!helpers.present() || !sigs.present() || !scope.present()) {
                return Answer.absent();
            }
            Map<String, Ast.Expr> bodies = new LinkedHashMap<>();
            for (String helper : sigs.value().keySet()) {
                Answer<Ast.FnDef> body = db.ask(new LoweredBody(name, helper));
                if (!body.present()) {
                    return Answer.absent();
                }
                bodies.put(helper, body.value().body());
            }
            try {
                return Answer.of(TypeChecker.recursiveHelperConstructs(sigs.value().keySet(), bodies,
                        HelperInliner.forHelpers(helpers.value()), scope.value()));
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
            Answer<Ast.Module> settled = db.ask(new Settled(name));
            return settled.present()
                    ? Answer.of(Names.behaviorNames(settled.value())) : Answer.absent();
        }
    }

    /** One behavior's declaration, so what a body is checked against is the behavior it implements
     * and not the module it sits in. */
    public record Spec(String module, String behavior) implements Key<Ast.SpecBehavior> {

        @Override
        public Answer<Ast.SpecBehavior> compute(Db db) {
            Answer<Ast.Module> settled = db.ask(new Settled(module));
            if (!settled.present()) {
                return Answer.absent();
            }
            for (Ast.BehaviorDef b : settled.value().behaviors()) {
                if (b instanceof Ast.SpecBehavior spec && spec.name().equals(behavior)) {
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
            Answer<Ast.SpecBehavior> spec = db.ask(new Spec(module, behavior));
            Answer<Ast.FnDef> fn = db.ask(new SettledFn(module, behavior));
            Answer<Ast.FnDef> body = db.ask(new LoweredBody(module, behavior));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(module));
            Answer<Map<String, ReqSig>> calleeSigs = db.ask(new CalleeSigs(module));
            Answer<Map<String, ReqSig>> reqSigs = db.ask(new ReqSigs(module));
            Answer<Map<String, Ast.FnDef>> helpers = db.ask(new Helpers(module));
            Answer<Map<String, Type>> sigs = db.ask(new RecursiveHelperSigs(module));
            Answer<Map<String, Map<TypeName, String>>> constructs =
                    db.ask(new RecursiveHelperConstructs(module));
            if (!spec.present() || !fn.present() || !body.present() || !scope.present()
                    || !calleeSigs.present() || !reqSigs.present() || !helpers.present()
                    || !sigs.present() || !constructs.present()) {
                return Answer.absent();
            }
            List<Diagnostic> warnings = new ArrayList<>();
            try {
                Core core = TypeChecker.checkBehavior(spec.value(), fn.value(), body.value().body(),
                        scope.value(), calleeSigs.value(), reqSigs.value(),
                        HelperInliner.forHelpers(helpers.value()), sigs.value(), constructs.value(),
                        warnings);
                List<Report> reports = new ArrayList<>();
                for (Diagnostic warning : warnings) {
                    reports.add(Report.of(warning));
                }
                return Answer.of(core, reports);
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
         * @param recursiveHelpers the bodies it elaborated, which the backend emits as methods
         * @param sound whether it found nothing wrong. An abandoned unit is wrong and says nothing
         *              of its own, so this is not the same as having reported nothing
         * @param stopped whether it stopped rather than finished, leaving the bodies nothing to be
         *                checked against
         */
        public record Of(Map<String, Core> recursiveHelpers, boolean sound, boolean stopped) {}

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Of> compute(Db db) {
            Answer<Lower.Lowered> lowering = db.ask(new Lowering(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<String, Sig>> imported = db.ask(new Imported(name));
            Answer<Set<String>> injected = db.ask(new ImportedInjected(name));
            Answer<Map<String, ReqSig>> reqSigs = db.ask(new ReqSigs(name));
            Answer<Map<String, Type>> sigs = db.ask(new RecursiveHelperSigs(name));
            Answer<Map<String, ReqSig>> calleeSigs = db.ask(new CalleeSigs(name));
            if (!lowering.present() || !scope.present() || !imported.present()
                    || !injected.present() || !reqSigs.present() || !sigs.present()
                    || !calleeSigs.present()) {
                return Answer.absent();
            }
            TypeChecker.Reported reported;
            try {
                reported = TypeChecker.checkModule(lowering.value().settled(), scope.value(),
                        imported.value(), injected.value(), lowering.value().lowered(),
                        reqSigs.value(), calleeSigs.value(), sigs.value());
            } catch (CompileException e) {
                return Answer.absent(e);
            }
            List<Report> reports = new ArrayList<>();
            for (CompileException e : reported.errors()) {
                reports.addAll(Report.of(e));
            }
            boolean sound = reported.errors().isEmpty() && reported.abandoned().isEmpty();
            return Answer.of(
                    new Of(reported.recursiveHelpers(), sound, reported.stopped()),
                    reports);
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
    public record Checked(String name) implements Key<TypeChecker.Checked> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<TypeChecker.Checked> compute(Db db) {
            Answer<Ast.Module> settled = db.ask(new Settled(name));
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
            for (Ast.FnDef fn : settled.value().fns()) {
                implemented.add(fn.name());
            }
            Map<String, Core> bodies = new LinkedHashMap<>();
            boolean bodiesCheck = true;
            // A module whose own check stopped built nothing for a body to be checked against, so
            // asking would report not being able to see what has already been reported missing.
            if (!module.value().stopped()) {
                // In the order they are declared, so what the backend emits does not move with what
                // the check happened to ask for first.
                for (Ast.BehaviorDef b : settled.value().behaviors()) {
                    // An injection target has no body here — something else supplies it (spec 13.2)
                    // — so there is nothing to check and nothing missing when there is none.
                    if (!(b instanceof Ast.SpecBehavior spec) || !implemented.contains(spec.name())) {
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
                    ? Answer.of(new TypeChecker.Checked(bodies, module.value().recursiveHelpers()))
                    : Answer.absent();
        }
    }
}
