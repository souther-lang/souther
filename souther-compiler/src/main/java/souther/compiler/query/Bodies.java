package souther.compiler.query;

import souther.compiler.ast.Ast;
import souther.compiler.check.Lower;
import souther.compiler.check.PipelineSigs;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeChecker;
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
     * A module with every helper call expanded into the body that called it, and with the parameter
     * types those expansions settled written back into the declarations.
     */
    public record Lowering(String name) implements Key<Lower.Lowered> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Lower.Lowered> compute(Db db) {
            Answer<Ast.Module> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<String, Sig>> imported = db.ask(new Imported(name));
            Answer<Set<String>> injected = db.ask(new ImportedInjected(name));
            if (!prepared.present() || !scope.present() || !imported.present()
                    || !injected.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(Lower.run(prepared.value(), scope.value(), imported.value(),
                        injected.value()));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
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
            return reported.errors().isEmpty()
                    ? Answer.of(reported.checked(), reports)
                    : Answer.absent(reports);
        }
    }
}
