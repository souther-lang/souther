package souther.compiler.query;

import souther.compiler.ast.Ast;
import souther.compiler.check.HelperInliner;
import souther.compiler.check.NewtypeDesugar;
import souther.compiler.check.TypeChecker;
import souther.compiler.check.Symbols;
import souther.compiler.derive.Deriver;
import souther.compiler.diag.CompileException;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

/**
 * What each declaration becomes before anything is checked against it: its codecs derived, the
 * invariants of the types it spreads settled into it, and its newtype constructors turned into
 * constructions.
 *
 * <p>These used to be three passes over a whole module in a fixed order, and getting that order
 * wrong was its own class of defect. Here the order is not written anywhere: each answer names what
 * it reads, and reading it is what makes it happen first.
 */
public final class Shapes {

    private Shapes() {}

    /**
     * A module with its codecs derived and the invariants of every type it spreads settled into the
     * spreading declaration.
     *
     * <p>The two go together because settling reads the spread source through the same symbols the
     * derive produced: an invariant that arrives by spread is part of the declaration from here on,
     * and a later pass that read the declaration before settling would read a type without it.
     */
    public record Derived(String name) implements Key<Ast.Module> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Ast.Module> compute(Db db) {
            Answer<Ast.Module> resolved = db.ask(new Names.Resolved(name));
            if (!resolved.present()) {
                return Answer.absent();
            }
            Answer<Symbols> scope = Names.symbols(db, name, Names.Stage.RESOLVED);
            if (!scope.present()) {
                return Answer.absent();
            }
            try {
                Ast.Module declared = onlyWhatItDeclares(resolved.value());
                Ast.Module derived = Deriver.derive(declared, scope.value());
                return Answer.of(HelperInliner.withSettledInvariants(derived, scope.value()));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
        }

        /**
         * The module carrying only the declarations it may have. A name written twice keeps the first,
         * reported by {@link Names.Declarations}; the second is not a declaration, so nothing below
         * here should read it and find it disagreeing with the one that is.
         *
         * <p>Which those are is {@link TypeChecker#declared}'s to say, and it says it once — asking it
         * again here rather than repeating the rule is what keeps the tree and the scope agreeing about
         * what the module declares.
         */
        private Ast.Module onlyWhatItDeclares(Ast.Module m) {
            Collection<Ast.Def> kept = TypeChecker.declared(m).defs().values();
            if (kept.size() == m.defs().size()) {
                return m;
            }
            return new Ast.Module(m.name(), m.exposing(), m.exposedOutputs(), m.imports(),
                    List.copyOf(kept), m.behaviors(), m.fns(), m.examples(), m.fakes(),
                    m.exampleFileTarget(), m.pos());
        }
    }

    /** A derived module's declarations by name — what every later stage resolves a type against. */
    public record DerivedDeclarations(String name) implements Key<Map<String, Ast.Def>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, Ast.Def>> compute(Db db) {
            Answer<Ast.Module> m = db.ask(new Derived(name));
            return m.present() ? Answer.of(Names.defsOf(m.value())) : Answer.absent();
        }
    }

    /**
     * A module with each newtype construction — {@code 金額(500)} — rewritten to a construction of
     * that type. Only the module's fns change; what it declares is what {@link Derived} left, which
     * is why every stage below reads its declarations from there and not from here.
     */
    public record Desugared(String name) implements Key<Ast.Module> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Ast.Module> compute(Db db) {
            Answer<Ast.Module> derived = db.ask(new Derived(name));
            if (!derived.present()) {
                return Answer.absent();
            }
            Answer<Symbols> scope = Names.symbols(db, name, Names.Stage.DERIVED);
            if (!scope.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(NewtypeDesugar.rewrite(derived.value(), scope.value()));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
        }
    }

    /**
     * The module a check and a codegen actually run over: the desugared one, plus the recursive
     * prelude helpers it reaches, as its own fns under their qualified names.
     *
     * <p>A recursive prelude helper cannot be inlined — it would expand forever — so it is emitted
     * as one of the module's methods, the same as a module-own recursive helper. Only the reached
     * ones are added; a module that never folds gets none.
     */
    public record Prepared(String name) implements Key<Ast.Module> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Ast.Module> compute(Db db) {
            Answer<Ast.Module> desugared = db.ask(new Desugared(name));
            if (!desugared.present()) {
                return Answer.absent();
            }
            Ast.Module m = desugared.value();
            try {
                Map<String, Ast.FnDef> injected =
                        HelperInliner.forModule(m).injectedRecursiveHelpers();
                if (injected.isEmpty()) {
                    return Answer.of(m);
                }
                List<Ast.FnDef> fns = new ArrayList<>(m.fns());
                fns.addAll(injected.values());
                return Answer.of(new Ast.Module(m.name(), m.exposing(), m.exposedOutputs(),
                        m.imports(), m.defs(), m.behaviors(), fns, m.examples(), m.fakes(),
                        m.exampleFileTarget(), m.pos()));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
        }
    }

    /** What names mean in a module once everything is derived — the scope a check runs in. */
    public record Scope(String name) implements Key<Symbols> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Symbols> compute(Db db) {
            return Names.symbols(db, name, Names.Stage.DERIVED);
        }
    }
}
