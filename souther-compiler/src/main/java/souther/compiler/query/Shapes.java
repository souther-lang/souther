package souther.compiler.query;

import souther.compiler.ast.Hir;
import souther.compiler.check.ClauseDischarge;
import souther.compiler.check.InvariantSettled;
import souther.compiler.check.Resolved;
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
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;

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
     * spreading declaration — the form each declaration is read from, before what one of them wrote
     * is normalized.
     *
     * <p>Not what a later stage reads. This is how {@link DerivedDeclarations} works its answers
     * out, and a mistake reached here is a mistake in the module rather than in any one
     * declaration: the derive and the settling read every declaration to answer about each.
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
    record Settling(String name) implements Key<InvariantSettled> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<InvariantSettled> compute(Db db) {
            // The module to expand, which is the resolved one where its values are well founded.
            // Everything below here expands a body of it.
            Answer<souther.compiler.check.Expandable> expandable = db.ask(new Expandable(name));
            if (!expandable.present()) {
                return Answer.absent();
            }
            Answer<Symbols> scope = Names.symbols(db, name, Names.Stage.RESOLVED);
            if (!scope.present()) {
                return Answer.absent();
            }
            Answer<Map<String, Hir.FnDef>> imported = db.ask(new Bodies.ImportedDefinitions(name));
            // A module whose imports form a cycle takes nothing from them. The cycle is reported where
            // it is found; an invariant naming an imported definition is left unsettled and reported
            // as the unknown name it then is, which is the same answer every other stage gives there.
            Map<String, Hir.FnDef> published = imported.present() ? imported.value() : Map.of();
            try {
                return Answer.of(
                        InvariantSettled.settle(expandable.value(), scope.value(), published));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
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
     * <p>What it answers with says so. The check is {@link souther.compiler.check.Expandable#check},
     * which is the only way to that state, so this question is where the check is asked for and not
     * where it is remembered.
     *
     * <p>Read off the resolved module, which is the earliest form that says what each name denotes —
     * and what a name denotes is what decides whether it is an edge at all.
     */
    public record Expandable(String name) implements Key<souther.compiler.check.Expandable> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<souther.compiler.check.Expandable> compute(Db db) {
            Answer<Resolved> resolved = db.ask(new Names.Resolved(name));
            if (!resolved.present()) {
                return Answer.absent();
            }
            Answer<Map<String, Hir.FnDef>> imported = db.ask(new Bodies.ImportedDefinitions(name));
            try {
                return Answer.of(souther.compiler.check.Expandable.check(resolved.value(),
                        imported.present() ? imported.value() : Map.of()));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
        }
    }

    /**
     * One declaration with its codecs derived and its spreads settled — what every later stage
     * resolves a type to.
     *
     * <p>Its own question, so its failure is the named declaration's and not the ones beside it: a
     * clause that cannot be read costs the declaration that wrote it this answer and costs the rest
     * nothing. A module still derives its declarations together, and this is read through that, so
     * what it depends on is still the module — what it is about is the one declaration.
     */
    public record DerivedDef(TypeKey named) implements Key<Hir.Def> {
        @Override
        public String module() {
            return named.module();
        }

        @Override
        public Answer<Hir.Def> compute(Db db) {
            Answer<Map<String, Hir.Def>> defs = db.ask(new DerivedDeclarations(named.module()));
            if (!defs.present()) {
                return Answer.absent();
            }
            Hir.Def def = defs.value().get(named.name());
            return def == null ? Answer.absent() : Answer.of(def);
        }
    }

    /**
     * A module's declarations by name, each in the form every later stage resolves a type against,
     * and only the ones that came out.
     *
     * <p>This is where a newtype construction written {@code 金額(500)} becomes the construction it
     * is. A construction reaching an invariant through a helper is written in that helper's body,
     * which this module has not desugared yet, so normalizing here rather than with the bodies is
     * what leaves one spelling for every check over an invariant to read.
     *
     * <p>A declaration at a time, so what is wrong with one clause is wrong with the declaration
     * that wrote it. Every declaration is worked out whether or not the one before it came out —
     * stopping at the first would leave the declarations after it without an answer, and each of
     * them owns what it has to say.
     */
    public record DerivedDeclarations(String name) implements Key<Map<String, Hir.Def>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, Hir.Def>> compute(Db db) {
            Answer<InvariantSettled> settling = db.ask(new Settling(name));
            Answer<Symbols> scope = Names.symbols(db, name, Names.Stage.RESOLVED);
            if (!settling.present() || !scope.present()) {
                return Answer.absent();
            }
            Map<String, Hir.Def> out = new LinkedHashMap<>();
            List<Report> reports = new ArrayList<>();
            for (Hir.Def def : settling.value().defs()) {
                try {
                    out.put(def.name(), NewtypeDesugar.rewriteInvariantsOf(def, scope.value()));
                } catch (CompileException e) {
                    reports.addAll(Report.of(e));
                }
            }
            return Answer.of(Map.copyOf(out), reports);
        }
    }

    /**
     * The module every later stage reads, where every declaration in it came out.
     *
     * <p>An assembly and not a stage of its own: each declaration is answered on its own and says
     * what it has to say there, and this is the conjunction of those answers. One that did not come
     * out leaves no module to hand over — a module missing a declaration it writes would be read as
     * one that does not declare it, which is a different thing to say and not a true one — while the
     * declarations beside it keep the answers they have.
     */
    public record Derived(String name) implements Key<Hir.Module> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Hir.Module> compute(Db db) {
            Answer<InvariantSettled> settling = db.ask(new Settling(name));
            Answer<Map<String, Hir.Def>> declarations = db.ask(new DerivedDeclarations(name));
            if (!settling.present() || !declarations.present()) {
                return Answer.absent();
            }
            Hir.Module assembled = settling.value().withEachDeclarationDerived(declarations.value());
            return assembled == null ? Answer.absent() : Answer.of(assembled);
        }
    }

    /**
     * A module with each newtype construction — {@code 金額(500)} — rewritten to a construction of
     * that type. Only the module's fns change; what it declares is what {@link Derived} left, which
     * is why every stage below reads its declarations from there and not from here.
     */
    public record Desugared(String name) implements Key<Hir.Module> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Hir.Module> compute(Db db) {
            Answer<Hir.Module> derived = db.ask(new Derived(name));
            Answer<Map<String, Hir.FnDef>> fns = db.ask(new DesugaredFns(name));
            if (!derived.present() || !fns.present()) {
                return Answer.absent();
            }
            List<Hir.FnDef> out = new ArrayList<>();
            for (Hir.FnDef fn : derived.value().fns()) {
                Hir.FnDef came = fns.value().get(fn.name());
                if (came == null) {
                    return Answer.absent();
                }
                out.add(came);
            }
            Hir.Module m = derived.value();
            return Answer.of(new Hir.Module(m.name(), m.exposing(), m.exposedOutputs(), m.imports(),
                    m.defs(), m.behaviors(), out, m.takenOn(), m.examples(), m.fakes(),
                    m.exampleFileTarget(), m.pos()));
        }
    }

    /**
     * A module's definitions by name, each with the newtype constructions written in its body
     * rewritten to the constructions they are, and only the ones that came out.
     *
     * <p>A definition at a time, and every one of them worked out whether or not the one before it
     * came out. What it reads about the declarations it names is asked for a declaration at a time
     * too, so a declaration that did not come out leaves the definitions that do not name it with
     * their answers.
     */
    public record DesugaredFns(String name) implements Key<Map<String, Hir.FnDef>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, Hir.FnDef>> compute(Db db) {
            Answer<InvariantSettled> settling = db.ask(new Settling(name));
            Answer<Symbols> scope = Names.symbols(db, name, Names.Stage.DERIVED);
            if (!settling.present() || !scope.present()) {
                return Answer.absent();
            }
            Map<String, Hir.FnDef> out = new LinkedHashMap<>();
            List<Report> reports = new ArrayList<>();
            for (Hir.FnDef fn : settling.value().fns()) {
                try {
                    out.put(fn.name(), NewtypeDesugar.rewriteOf(fn, scope.value()));
                } catch (CompileException e) {
                    reports.addAll(Report.of(e));
                }
            }
            return Answer.of(Map.copyOf(out), reports);
        }
    }

    /**
     * One definition with the newtype constructions in its body rewritten — its own question, so
     * its failure is the named definition's and not the ones beside it. It is read through
     * {@link DesugaredFns}, which works every definition out, so what it depends on is still the
     * module; what it is about is the one definition.
     */
    public record DesugaredFn(String module, String fn) implements Key<Hir.FnDef> {
        @Override
        public String module() {
            return module;
        }

        @Override
        public Answer<Hir.FnDef> compute(Db db) {
            Answer<Map<String, Hir.FnDef>> fns = db.ask(new DesugaredFns(module));
            if (!fns.present()) {
                return Answer.absent();
            }
            Hir.FnDef came = fns.value().get(fn);
            return came == null ? Answer.absent() : Answer.of(came);
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
    public record Prepared(String name) implements Key<Hir.Module> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Hir.Module> compute(Db db) {
            Answer<Hir.Module> desugared = db.ask(new Desugared(name));
            Answer<Map<String, Hir.FnDef>> imported = db.ask(new Bodies.ImportedDefinitions(name));
            if (!desugared.present()) {
                return Answer.absent();
            }
            // A module whose imports form a cycle takes nothing from them — the cycle is reported
            // where it is found, and this module is not compiled either way.
            Map<String, Hir.FnDef> published = imported.present() ? imported.value() : Map.of();
            // An imported definition is written here bare and denotes the module that declares it.
            // Spelling it out, once, settles the name this module reaches it by, which is what the
            // table a call expands against is keyed by and what the method a recursive helper becomes
            // is called. It settles nothing about where the definition came from: the fns below hold
            // declarations of several modules under names of one shape, and which module wrote each is
            // carried on the declaration (Hir.FnDef.declaredIn).
            Hir.Module m = HelperNames.qualifyImports(desugared.value());
            try {
                HelperInliner inliner = HelperInliner.forModule(m, published);
                Map<String, Hir.FnDef> injected =
                        new java.util.LinkedHashMap<>(inliner.injectedRecursiveHelpers());
                // A helper an example row applies is emitted for that reason (ADR-0077); one this
                // module does not declare is taken on here, as a recursive one it reaches is.
                inliner.injectedExampleHelpers().forEach(injected::putIfAbsent);
                if (injected.isEmpty()) {
                    return Answer.of(m);
                }
                // Beside what the module declared, not among it. Both are emitted and only the first
                // was written here, and a reader asking which is which asks the component it is in
                // rather than the shape of a name.
                return Answer.of(new Hir.Module(m.name(), m.exposing(), m.exposedOutputs(),
                        m.imports(), m.defs(), m.behaviors(), m.fns(),
                        List.copyOf(injected.values()), m.examples(), m.fakes(),
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
            implements Key<Map<TypeSymbol, List<ClauseDischarge>>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<TypeSymbol, List<ClauseDischarge>>> compute(Db db) {
            Answer<souther.compiler.check.Expandable> expandable = db.ask(new Expandable(name));
            Answer<Symbols> scope = Names.symbols(db, name, Names.Stage.RESOLVED);
            if (!expandable.present() || !scope.present()) {
                return Answer.absent();
            }
            Answer<Map<String, Hir.FnDef>> imported = db.ask(new Bodies.ImportedDefinitions(name));
            Map<String, Hir.FnDef> published = imported.present() ? imported.value() : Map.of();
            // What the clause says is what the check reads, so an imported bound is substituted here
            // as it is where the invariant is settled. A clause left naming it would be classified as
            // a rule this analysis cannot read, and a construction the bound rejects would compile.
            Hir.Module declaring = expandable.value().withQualifiedInvariants();
            try {
                Map<TypeSymbol, List<ClauseDischarge>> out = new LinkedHashMap<>();
                for (Hir.Def def : declaring.defs()) {
                    if (!(def instanceof Hir.Data data) || data.invariants().isEmpty()) {
                        continue;
                    }
                    // The clause is classified in the representation the check reads, and reported at
                    // the position it is written — an expansion carries positions of its own, and the
                    // author is looking at the source.
                    HelperInliner inliner = HelperInliner.forHelpers(name,
                            HelperInliner.helpersOf(declaring), published, InliningPolicy.DISCHARGE);
                    List<ClauseDischarge> clauses = new ArrayList<>();
                    TypeSymbol named = data.declares();
                    // A declared clause is one rule to depart by and may still be several conjuncts to
                    // discharge, so `a && b` under one name is classified twice under that name: what
                    // discharges each half is what an author needs, and the name is what a caller reads.
                    for (Hir.InvariantClause declared : data.invariants()) {
                        for (Hir.Expr written : HelperInvariants.conjunctsOf(declared.expr())) {
                            clauses.add(InvariantChecker.capabilityOf(
                                    inliner.inline(written, new BindingOwner.OfData(named)),
                                    leftmost(written), named, data, scope.value())
                                    .named(declared.name()));
                        }
                    }
                    out.put(named, List.copyOf(clauses));
                }
                return Answer.of(Map.copyOf(out));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
        }
    }

    /** Where a clause begins: the earliest position anything in it carries. A node's own position is
     * where its operator is written, and a reader points at the clause. */
    private static SourcePos leftmost(Hir.Expr e) {
        SourcePos[] found = {e.pos()};
        Hir.forEachChild(e, child -> {
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
            implements Key<Map<TypeSymbol, List<Hir.InvariantClause>>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<TypeSymbol, List<Hir.InvariantClause>>> compute(Db db) {
            Answer<souther.compiler.check.Expandable> expandable = db.ask(new Expandable(name));
            Answer<Symbols> scope = Names.symbols(db, name, Names.Stage.RESOLVED);
            if (!expandable.present() || !scope.present()) {
                return Answer.absent();
            }
            Answer<Map<String, Hir.FnDef>> imported = db.ask(new Bodies.ImportedDefinitions(name));
            Map<String, Hir.FnDef> published = imported.present() ? imported.value() : Map.of();
            try {
                return Answer.of(HelperInvariants.invariantsForDischarge(
                        expandable.value(), scope.value(), published));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
        }
    }
}
