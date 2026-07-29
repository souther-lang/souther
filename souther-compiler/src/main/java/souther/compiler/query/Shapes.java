package souther.compiler.query;

import souther.compiler.ast.Ast;
import souther.compiler.check.HelperInliner;
import souther.compiler.check.NewtypeDesugar;
import souther.compiler.check.TypeChecker;
import souther.compiler.check.Symbols;
import souther.compiler.derive.Deriver;
import souther.compiler.diag.CompileException;
import souther.compiler.types.TypeName;

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

    /**
     * One declaration with its codecs derived and its spreads settled — what every later stage
     * resolves a type to.
     *
     * <p>Its own question, so a reader depends on the declaration it named and not on everything
     * declared beside it. A module still derives its declarations together; that is how the answer
     * is worked out, not what the answer is about, and moving that apart changes nothing here.
     */
    public record DerivedDef(TypeName named) implements Key<Ast.Def> {
        @Override
        public String module() {
            return named.module();
        }

        @Override
        public Answer<Ast.Def> compute(Db db) {
            Answer<Map<String, Ast.Def>> defs = db.ask(new DerivedDeclarations(named.module()));
            if (!defs.present()) {
                return Answer.absent();
            }
            Ast.Def def = defs.value().get(named.name());
            return def == null ? Answer.absent() : Answer.of(def);
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
     * The module a check and a codegen actually run over: the desugared one with every imported name
     * written as the definition it denotes, plus the recursive helpers it reaches, as its own fns
     * under those names.
     *
     * <p>A recursive helper cannot be inlined — it would expand forever — so it is emitted as one of
     * this module's methods. That holds whoever declared it: a prelude {@code List.foldFrom}, and a
     * helper another module published or published something else that calls. The declaring module is
     * the helper's identity and not where the method goes; the method goes on the {@code $Fns} of
     * whichever module is being compiled, which is what keeps that class package-private and leaves no
     * new way to reach a construction from Java. Only the reached ones are added; a module that never
     * folds gets none.
     */
    public record Prepared(String name) implements Key<Ast.Module> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Ast.Module> compute(Db db) {
            Answer<Ast.Module> desugared = db.ask(new Desugared(name));
            Answer<Map<String, Ast.FnDef>> imported = db.ask(new Bodies.ImportedDefinitions(name));
            if (!desugared.present()) {
                return Answer.absent();
            }
            // A module whose imports form a cycle takes nothing from them — the cycle is reported
            // where it is found, and this module is not compiled either way.
            Map<String, Ast.FnDef> published = imported.present() ? imported.value() : Map.of();
            // An imported definition is written here bare and denotes the module that declares it.
            // Spelling it that way, once, is what lets everything downstream — the table a call
            // expands against, the method a recursive helper becomes — read the identity by reading
            // the name.
            Ast.Module m = HelperInliner.qualifyImports(desugared.value());
            try {
                Map<String, Ast.FnDef> injected =
                        HelperInliner.forModule(m, published).injectedRecursiveHelpers();
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
