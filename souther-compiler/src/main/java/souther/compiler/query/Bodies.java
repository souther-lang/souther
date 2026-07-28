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
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

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
            Answer<Set<String>> injected = db.ask(new ImportedInjected(name));
            if (!prepared.present() || !scope.present() || !imported.present()
                    || !injected.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(InjectionSigs.of(prepared.value(), scope.value(), imported.value(),
                        injected.value()));
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
            return settled.present()
                    ? Answer.of(HelperInliner.helpersOf(settled.value())) : Answer.absent();
        }
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

    /** One settled fn, so what a body is expanded from is the fn itself and not the module it sits
     * in. */
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

    /**
     * The result of type-checking a module. Absent when anything in it is wrong: a module that does
     * not check must not reach codegen, and an importer of it is skipped rather than compiled
     * against a broken module.
     *
     * <p>Warnings ride on a present answer, which is how an invariant-discharge warning reaches the
     * author of a module that compiled.
     */
    public record Checked(String name) implements Key<TypeChecker.Checked> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<TypeChecker.Checked> compute(Db db) {
            Answer<Lower.Lowered> lowering = db.ask(new Lowering(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<String, Sig>> imported = db.ask(new Imported(name));
            Answer<Set<String>> injected = db.ask(new ImportedInjected(name));
            if (!lowering.present() || !scope.present() || !imported.present()
                    || !injected.present()) {
                return Answer.absent();
            }
            // Whether anything about this module's names came out wrong decides whether it can be
            // emitted, and nothing else. It must not decide whether the module is checked: the error
            // type absorbs so that the check can carry on, and stopping here would mean a mistake in
            // one declaration silencing every other definition in the file.
            boolean named = Boolean.TRUE.equals(db.ask(new Names.Sound(name)).value());
            TypeChecker.Reported reported;
            try {
                reported = TypeChecker.checkReporting(lowering.value().settled(), scope.value(),
                        imported.value(), injected.value(), lowering.value().lowered());
            } catch (CompileException e) {
                return Answer.absent(e);
            }
            List<Report> reports = new ArrayList<>();
            for (CompileException e : reported.errors()) {
                reports.addAll(Report.of(e));
            }
            for (Diagnostic warning : reported.checked().warnings()) {
                reports.add(Report.of(warning));
            }
            // A unit the check could not read at all leaves the module without a meaning to emit,
            // and says nothing of its own: the name it rested on was reported where it was written.
            // Whatever else the check found is still reported, which is the point of carrying on.
            // Both, and both after the check. Sound says nothing about this module's names came out
            // wrong; the tree says it holds no type nobody could name, which can happen with nothing
            // reported here at all — an import of a module that is here and unusable leaves a hole,
            // and what is wrong was reported on that module.
            boolean sound = named
                    && !TypeOps.holdsAnErroneousType(lowering.value().settled())
                    && reported.errors().isEmpty()
                    && reported.abandoned().isEmpty();
            return sound ? Answer.of(reported.checked(), reports) : Answer.absent(reports);
        }
    }
}
