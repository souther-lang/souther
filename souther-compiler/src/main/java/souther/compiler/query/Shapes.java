package souther.compiler.query;

import souther.compiler.ast.Ast;
import souther.compiler.check.ClauseDischarge;
import souther.compiler.check.HelperInliner;
import souther.compiler.check.HelperInvariants;
import souther.compiler.check.HelperNames;
import souther.compiler.check.InliningPolicy;
import souther.compiler.check.InvariantChecker;
import souther.compiler.check.NewtypeDesugar;
import souther.compiler.check.TypeChecker;
import souther.compiler.check.ValueCycles;
import souther.compiler.check.Symbols;
import souther.compiler.derive.Deriver;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.TypeName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
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
     *
     * <p>Settling substitutes what the modules this one imports publish to it, as lowering a body
     * does. The dependency runs the other way from the rest of this file — a shape reaching into
     * bodies — and it is the imported module's bodies it reaches, never this one's: what a module
     * imports is read off its resolved form, so nothing here is asked through itself.
     */
    public record Derived(String name) implements Key<Ast.Module> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Ast.Module> compute(Db db) {
            // The module to expand, which is the resolved one where its values are well founded.
            // Everything below here expands a body of it.
            Answer<Ast.Module> resolved = db.ask(new Expandable(name));
            if (!resolved.present()) {
                return Answer.absent();
            }
            Answer<Symbols> scope = Names.symbols(db, name, Names.Stage.RESOLVED);
            if (!scope.present()) {
                return Answer.absent();
            }
            Answer<Map<String, Ast.FnDef>> imported = db.ask(new Bodies.ImportedDefinitions(name));
            // A module whose imports form a cycle takes nothing from them. The cycle is reported where
            // it is found; an invariant naming an imported definition is left unsettled and reported
            // as the unknown name it then is, which is the same answer every other stage gives there.
            Map<String, Ast.FnDef> published = imported.present() ? imported.value() : Map.of();
            try {
                Ast.Module declared = onlyWhatItDeclares(resolved.value());
                Ast.Module derived = Deriver.derive(declared, scope.value());
                // The invariants are whole here — spread in, imports substituted, helpers expanded —
                // and this is where a newtype construction written `金額(500)` becomes the
                // construction it is. A construction reaching an invariant through a helper is
                // written in that helper's body, which this module has not desugared yet, so
                // normalizing here rather than with the bodies is what leaves one spelling for every
                // check over an invariant to read.
                return Answer.of(NewtypeDesugar.rewriteInvariants(
                        HelperInvariants.withSettledInvariants(derived, scope.value(), published),
                        scope.value()));
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
     * The module, where a body of it may be expanded — which is where no value of it is defined in
     * terms of itself.
     *
     * <p>A value is substituted at each of its references (ADR-0072), so one that reaches itself is
     * substituted into itself and there is no body to reach the end of. Everything that expands a body
     * of this module needs that to be false, and needs to know before it expands anything: left until
     * the expansion runs out of stack, what comes back names a nesting the author did not write.
     *
     * <p>It hands over the module rather than answering whether. The rule used to be checked wherever
     * an expansion table was built, which is eleven places in a compile, so the refusal was raised by
     * whichever of them ran first — from inside whatever question that was, which passed it on as a
     * failure of its own. Answering whether moved the problem rather than removing it: three questions
     * read the module and expand it, each said the condition over again, and one of them said it and
     * two did not. A condition a reader has to remember is a condition a reader can forget.
     *
     * <p>So there is one thing to ask for and it is the thing they want. A question that expands a
     * body asks for a module to expand and gets one or gets nothing; there is no answer here that
     * hands over a module without having checked it, and nothing left to remember beside it.
     *
     * <p>Read off the resolved module, which is the earliest form that says what each name denotes —
     * and what a name denotes is what decides whether it is an edge at all.
     */
    public record Expandable(String name) implements Key<Ast.Module> {
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
            Answer<Map<String, Ast.FnDef>> imported = db.ask(new Bodies.ImportedDefinitions(name));
            try {
                ValueCycles.rejectIn(resolved.value(),
                        imported.present() ? imported.value() : Map.of());
                return Answer.of(resolved.value());
            } catch (CompileException e) {
                return Answer.absent(e);
            }
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
            Ast.Module m = HelperNames.qualifyImports(desugared.value());
            try {
                HelperInliner inliner = HelperInliner.forModule(m, published);
                Map<String, Ast.FnDef> injected =
                        new java.util.LinkedHashMap<>(inliner.injectedRecursiveHelpers());
                // A helper an example row applies is emitted for that reason (ADR-0077); one this
                // module does not declare is taken on here, as a recursive one it reaches is.
                inliner.injectedExampleHelpers().forEach(injected::putIfAbsent);
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

    /**
     * How each clause of each invariant this module declares can be discharged at compile time (spec
     * §invariant-discharge-capability), in the order the clauses are written.
     *
     * <p>Only this module's own declarations. The classification is the clause's, and a clause is
     * written where its type is declared; a reader in another module asks that module.
     */
    public record InvariantCapabilities(String name)
            implements Key<Map<TypeName, List<ClauseDischarge>>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<TypeName, List<ClauseDischarge>>> compute(Db db) {
            Answer<Ast.Module> resolved = db.ask(new Expandable(name));
            Answer<Symbols> scope = Names.symbols(db, name, Names.Stage.RESOLVED);
            if (!resolved.present() || !scope.present()) {
                return Answer.absent();
            }
            Answer<Map<String, Ast.FnDef>> imported = db.ask(new Bodies.ImportedDefinitions(name));
            Map<String, Ast.FnDef> published = imported.present() ? imported.value() : Map.of();
            // What the clause says is what the check reads, so an imported bound is substituted here
            // as it is where the invariant is settled. A clause left naming it would be classified as
            // a rule this analysis cannot read, and a construction the bound rejects would compile.
            Ast.Module declaring = HelperNames.withQualifiedInvariants(resolved.value());
            try {
                Map<TypeName, List<ClauseDischarge>> out = new LinkedHashMap<>();
                for (Ast.Def def : declaring.defs()) {
                    if (!(def instanceof Ast.Data data) || data.invariants().isEmpty()) {
                        continue;
                    }
                    // The clause is classified in the representation the check reads, and reported at
                    // the position it is written — an expansion carries positions of its own, and the
                    // author is looking at the source.
                    HelperInliner inliner = HelperInliner.forHelpers(name,
                            HelperInliner.helpersOf(declaring), published, InliningPolicy.DISCHARGE);
                    List<ClauseDischarge> clauses = new ArrayList<>();
                    // A declared clause is one rule to depart by and may still be several conjuncts to
                    // discharge, so `a && b` under one name is classified twice under that name: what
                    // discharges each half is what an author needs, and the name is what a caller reads.
                    for (Ast.InvariantClause declared : data.invariants()) {
                        for (Ast.Expr written : HelperInvariants.conjunctsOf(declared.expr())) {
                            clauses.add(InvariantChecker.capabilityOf(
                                    inliner.inline(written, new BindingOwner.OfData(
                                            new TypeName(name, data.name()))),
                                    leftmost(written), data, scope.value()).named(declared.name()));
                        }
                    }
                    out.put(new TypeName(name, data.name()), List.copyOf(clauses));
                }
                return Answer.of(Map.copyOf(out));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
        }
    }

    /** Where a clause begins: the earliest position anything in it carries. A node's own position is
     * where its operator is written, and a reader points at the clause. */
    private static SourcePos leftmost(Ast.Expr e) {
        SourcePos[] found = {e.pos()};
        Ast.forEachChild(e, child -> {
            SourcePos inner = leftmost(child);
            if (inner != null && (found[0] == null || earlier(inner, found[0]))) {
                found[0] = inner;
            }
        });
        return found[0];
    }

    private static boolean earlier(SourcePos a, SourcePos b) {
        return a.line() != b.line() ? a.line() < b.line() : a.column() < b.column();
    }

    /**
     * The invariants this module declares, in the representation the invariant-discharge analysis
     * reads ({@link souther.compiler.check.InliningPolicy#DISCHARGE}) — beside the settled form that
     * every other stage sees on the declaration itself.
     *
     * <p>Only the clauses this module declares. What another module publishes arrives settled, which
     * is what makes an imported clause fall outside the statically dischargeable fragment: the
     * analysis reads what it is given, and there the operations have already become the folds they
     * are. A clause declared here that names an imported definition is this module's clause and stays
     * inside the fragment — the definition is substituted, as it is everywhere the invariant is read.
     */
    public record InvariantsForDischarge(String name)
            implements Key<Map<TypeName, List<Ast.InvariantClause>>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<TypeName, List<Ast.InvariantClause>>> compute(Db db) {
            Answer<Ast.Module> resolved = db.ask(new Expandable(name));
            Answer<Symbols> scope = Names.symbols(db, name, Names.Stage.RESOLVED);
            if (!resolved.present() || !scope.present()) {
                return Answer.absent();
            }
            Answer<Map<String, Ast.FnDef>> imported = db.ask(new Bodies.ImportedDefinitions(name));
            Map<String, Ast.FnDef> published = imported.present() ? imported.value() : Map.of();
            try {
                return Answer.of(HelperInvariants.invariantsForDischarge(
                        resolved.value(), scope.value(), published));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
        }
    }
}
