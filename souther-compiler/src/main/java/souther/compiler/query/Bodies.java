package souther.compiler.query;

import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.check.BehaviorChecker;
import souther.compiler.check.BehaviorContract;
import souther.compiler.check.BehaviorRequirement;
import souther.compiler.check.ClausesForDischarge;
import souther.compiler.check.StatedContract;
import souther.compiler.check.ContractDischarge;
import souther.compiler.check.DataChecker;
import souther.compiler.check.HelperInliner;
import souther.compiler.check.HelperGraph;
import souther.compiler.check.HelperNames;
import souther.compiler.check.HelperTable;
import souther.compiler.check.InjectionSigs;
import souther.compiler.check.InliningPolicy;
import souther.compiler.check.InvariantChecker;
import souther.compiler.check.Lower;
import souther.compiler.check.ModuleUniverse;
import souther.compiler.check.PipelineSigs;
import souther.compiler.check.ModuleUniverse.InSight.Read.PublishedHelper;
import souther.compiler.check.ReqSig;
import souther.compiler.check.Resolve;
import souther.compiler.check.Scoping;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeChecker;
import souther.compiler.check.TypeOps;
import souther.compiler.check.Unanswerable;
import souther.compiler.core.Core;
import souther.compiler.core.GrowingFold;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.SourcePos;
import souther.compiler.diag.msg.ModuleMessage;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.ArrayDeque;
import java.util.Collection;
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
    public record ImportedDependencies(String name) implements Key<Set<ValueName.Behavior>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Set<ValueName.Behavior>> compute(Db db) {
            if (db.ask(new Front.Available(name)).value() == null) {
                return Answer.of(Set.of());
            }
            return Answer.of(Ordered.set(borrowedWhere(db, name, Dependencies::new)));
        }
    }

    /**
     * The behaviors this module borrows, each as the declaration it is.
     *
     * <p>Read off what the import lines settled, and not worked out from the lines again. Walked
     * here, a module that declares a behavior and does not offer it answers yes to "do you declare
     * one" — so a line refused for that was borrowed from all the same, and an author was told the
     * module does not expose the name and then told two modules were offering it.
     *
     * <p>A set of declarations and not a table under the names this module writes. Two modules
     * declaring a behavior of one name are two behaviors, and a qualified reference says which is
     * meant; keyed by the spelling, the second to arrive stood for both. What a bare name written
     * here reaches is settled where the lines are, and one spelling two lines both claim is refused
     * there — which is a question about what is written, not about what is declared.
     */
    private static Set<ValueName.Behavior> borrowed(Db db, String module) {
        Set<ValueName.Behavior> out = new LinkedHashSet<>();
        Answer<Scoping.Scoped> scoped = db.ask(new Names.ModuleScope(module));
        if (scoped.present()) {
            out.addAll(scoped.value().imports().behaviors().values());
        }
        // And the ones a qualified reference reaches, which claim no bare spelling and so were
        // settled by no contest. They are borrowed all the same: naming a behavior through its
        // module reaches it, and the signature and the injected field come with it.
        for (Resolve.QualifiedUse each : reachedByAQualifier(db, module)) {
            out.add(each.named());
        }
        return out;
    }

    /**
     * The behaviors this module borrows that {@code asks} answers yes about where they are
     * declared — an injection target, one that may be called by name, one that requires something.
     *
     * <p>One walk for the three, so that which of them a borrowed behavior falls into is asked of
     * the module that declares it in one way. Asked of the declaration and not of a name: the
     * question is about that module's own behavior, so the name it goes by there is the whole of
     * what is handed over, and what this module happens to write for it never enters.
     */
    private static Set<ValueName.Behavior> borrowedWhere(
            Db db, String module, java.util.function.Function<String, Key<Set<String>>> asks) {
        Set<ValueName.Behavior> out = new LinkedHashSet<>();
        for (ValueName.Behavior each : borrowed(db, module)) {
            Set<String> there = db.ask(asks.apply(each.module())).value();
            if (there != null && there.contains(each.name())) {
                out.add(each);
            }
        }
        return out;
    }

    /**
     * The behaviors a qualified reference reaches, as resolution answered them.
     *
     * <p>Read as the answer rather than found among the module's imports. An import is synthesized
     * for each module a reference reaches, to record the dependency — and a dependency the module
     * already has is not recorded twice, so a behavior named through its module was invisible here
     * whenever a line happened to name the same module and name. Which is exactly when the bare
     * spelling had been refused and the qualified reference was the only way the behavior was
     * reached at all.
     *
     * <p>Each occurrence, and not one per module. An import stands where the first reference to
     * that module is written, so a second one elsewhere was reported at the first one's line.
     */
    private static List<Resolve.QualifiedUse> reachedByAQualifier(Db db, String module) {
        Answer<List<Resolve.QualifiedUse>> reached =
                db.ask(new Names.QualifiedBehaviors(module));
        return reached.present() ? reached.value() : List.of();
    }

    /** The leave each definition this module imported carries, by the bare name it writes for
     *  it. What may be read from another module is what this module was left with. */
    private static Map<String, PublishedHelper> leaves(Db db, String module) {
        Answer<Scoping.Scoped> scoped = db.ask(new Names.ModuleScope(module));
        return scoped.present() ? scoped.value().imports().leaves() : Map.of();
    }


    /** The behaviors a module borrows that may be called by name where they are declared. */
    public record ImportedCallable(String name) implements Key<Set<ValueName.Behavior>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Set<ValueName.Behavior>> compute(Db db) {
            if (db.ask(new Front.Available(name)).value() == null) {
                return Answer.of(Set.of());
            }
            return Answer.of(Ordered.set(borrowedWhere(db, name, Callable::new)));
        }
    }

    /**
     * The signature of every behavior this module can name — its own and the ones it borrows — each
     * under the declaration it belongs to.
     *
     * <p>What a composition's stages are typed against. A stage says which behavior it reaches and
     * two behaviors of one name are two declarations, so this is keyed by the declaration: a table
     * under the names written here answers one entry for both, and which one it is falls to
     * whichever was written into it last.
     */
    public record Reachable(String name) implements Key<Map<ValueName.Behavior, Sig>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<ValueName.Behavior, Sig>> compute(Db db) {
            Answer<souther.compiler.check.Desugared.Module> desugared =
                    db.ask(new Shapes.Desugared(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<ValueName.Behavior, Sig>> imported = db.ask(new Imported(name));
            if (!desugared.present() || !scope.present() || !imported.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(PipelineSigs.signatures(name, desugared.value().behaviors(),
                        scope.value(), imported.value()));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
        }
    }

    /**
     * What each of a module's behaviors declares about its answer, by the name it is declared under.
     *
     * <p>The one reading of a module's {@code ensures} clauses. A clause is resolved, typed, and
     * split into the cases the answer can be, and every reader of that wants the same split: the
     * emitter that turns a rule into the check a violation is found by, the classification that says
     * how much of it a caller can assume, the editor that shows that classification, and the analysis
     * that assumes it at a call. Read once here, so none of them goes back to the declaration to work
     * out what a case means or what the parameters are called.
     *
     * <p>A behavior declaring nothing is not here. Absence says it states nothing, which is what a
     * reader asking "is there a check to emit" is asking; an empty contract would be a second way to
     * say the same thing, and the two would have to be kept agreeing.
     *
     * <p>The reports are this answer's own. Reading a clause is what finds a clause that cannot be
     * read, so the two arrive together — a caller that got the contracts and left the reports behind
     * would hold a module's declarations while nothing said that one of them was refused. Nobody
     * re-raises them: a reader asks for the contracts and what the reading found comes with them,
     * which is why the reading is not repeated at the reader that happens to be first.
     */
    public record Contracts(String name) implements Key<Map<String, BehaviorContract>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, BehaviorContract>> compute(Db db) {
            Answer<Lower.Lowered> lowering = db.ask(new Lowering(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<String, Sig>> signatures = db.ask(new Signatures(name));
            Answer<Map<String, Type>> helpers = db.ask(new RecursiveHelperSigs(name));
            if (!lowering.present() || !scope.present() || !signatures.present()
                    || !helpers.present()) {
                return Answer.absent();
            }
            Map<String, BehaviorContract> contracts = new LinkedHashMap<>();
            List<Report> reports = new ArrayList<>();
            for (Hir.BehaviorDef behavior : lowering.value().settled().behaviors()) {
                if (!(behavior instanceof Hir.SpecBehavior spec) || spec.ensures().isEmpty()) {
                    continue;
                }
                // Behavior by behavior, and one that cannot be read leaves the rest readable. Two
                // behaviors each carrying a wrong clause are two things for an author to fix, and a
                // reading that stopped at the first would turn one build into two.
                try {
                    contracts.put(spec.name(), BehaviorChecker.contractOf(spec, name,
                            signatures.value().get(spec.name()), scope.value(), helpers.value()));
                } catch (Unanswerable _) {
                    // Rests on something already reported where it went wrong. Said again here it
                    // would be that one mistake seen from a second angle.
                } catch (CompileException e) {
                    reports.addAll(Report.of(e));
                }
            }
            return Answer.of(Ordered.map(contracts), reports);
        }
    }

    /**
     * How much of what each behavior of a module declares the check can read, by the name the
     * behavior is declared under (spec §ensures-discharge-capability).
     *
     * <p>Read in the representation the discharge analysis reads ({@link InliningPolicy#DISCHARGE}),
     * which is not the one that runs: an operation the language defines the meaning of stays an
     * operation here, and the classification is of what the author wrote rather than of the algorithm
     * it becomes. That is the same reading a data's clauses are classified in
     * ({@link Shapes.InvariantCapabilities}).
     *
     * <p>Only this module's own behaviors. The classification is the declaration's, and a reader in
     * another module asks that module.
     *
     * <p>Nothing is reported from here. Whether a clause is well formed was decided by
     * {@link Contracts}, which owns both the contracts and what reading them found; a behavior whose
     * declaration cannot be read is left out of this rather than refused a second time.
     */
    public record ContractCapabilities(String name)
            implements Key<Map<String, ContractDischarge>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, ContractDischarge>> compute(Db db) {
            Answer<Map<String, StatedContract>> stated = db.ask(new StatedContracts(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            if (!stated.present() || !scope.present()) {
                return Answer.absent();
            }
            Map<String, ContractDischarge> out = new LinkedHashMap<>();
            stated.value().forEach((behavior, rules) ->
                    out.put(behavior, ContractDischarge.of(rules, scope.value())));
            return Answer.of(Ordered.map(out));
        }
    }

    /**
     * What one behavior states about its answer, asked of the module that declares it.
     *
     * <p>The unit a reader depends on. A body is checked against the contracts of the behaviors it
     * reaches, so what it depends on is those behaviors one at a time. A table of every contract its
     * module can see is an index, and reading one as a value makes an edit to any entry an edit to
     * all of them: every body of the module, and of every module importing it, is re-checked because
     * one clause elsewhere was written differently.
     *
     * <p>Recomputing this is not the same as its answer changing. It reads the module's table, so the
     * table is rebuilt whenever any clause in that file is edited, and this stops the rebuild from
     * reaching a reader wherever it comes out equal. What is left is the cost of rebuilding the
     * table, which is a question about this producer and not about who depends on it.
     *
     * <p>How far that reaches is narrower than it looks, and measured: a contract carries the source
     * positions of its terms and the coverage ordinals numbered over the module, so an edit above the
     * declaration moves both — a blank line moves the positions, and a clause gaining a term moves
     * every ordinal after it. Editing a behavior written <em>below</em> this one comes out equal here
     * and stops; editing one written above does not. What a caller assumes of an answer is neither of
     * those things, so the reach is a property of what the value happens to carry rather than of what
     * a caller depends on.
     *
     * <p>Absent where the behavior states nothing, and where the module that declares it could not be
     * read. Absence is what a caller wanting to know "is there anything to assume" is asking, and an
     * empty contract would be a second way to say it.
     */
    public record Stated(ValueName.Behavior behavior) implements Key<StatedContract> {
        @Override
        public String module() {
            return behavior.module();
        }

        @Override
        public Answer<StatedContract> compute(Db db) {
            Map<String, StatedContract> declared =
                    db.ask(new StatedContracts(behavior.module())).value();
            StatedContract stated = declared == null ? null : declared.get(behavior.name());
            return stated == null ? Answer.absent() : Answer.of(stated);
        }
    }

    /**
     * The behaviors a call in one body can reach — this module's own and the ones it borrows.
     *
     * <p>Read off the body the discharge analysis is given, because that is the tree the contract
     * lookup runs over: what it finds is a call whose function is a name denoting a behavior, so what
     * it can find is what is written there. That tree has its helper calls expanded, which widens
     * nothing on its own — a helper cannot call a behavior (E1818). What reading it buys is that the
     * frontier is taken from the tree the lookup walks rather than from one that agrees with it.
     *
     * <p>Every behavior a name reaches, and not the ones that may be called by name. A behavior
     * arrives at a body by being built and called or by being injected, and which of the two decides
     * how the call is typed rather than whose contract is read — {@link CalleeSigs} and
     * {@link ReqSigs} split them for the first question, and this is the second.
     *
     * <p>An injected one is reached through the parameter {@code depends on} gave the body, so the
     * name written at the call denotes that parameter and not the behavior. What it stands for is
     * read off the declaration, which is the only place the two are put together before the call is
     * typed, and it is the binding that says so: a binding in force wins over the declaration it
     * shadows (spec §fn-rules), which is the same reading {@link Lower} takes of the same clause.
     *
     * <p>Every behavior a name reaches, applied or not. A behavior named where a value goes becomes
     * the function it names, and whether some later step applies it is not something this can see;
     * a name that is never applied brings a contract nobody consults, which costs a dependency the
     * body has not got rather than losing one it has.
     *
     * <p>Empty where the body is not there to read: the analysis that reads contracts is skipped
     * then, so nothing is checked against one.
     */
    public record BehaviorsReached(String module, String behavior)
            implements Key<Set<ValueName.Behavior>> {

        @Override
        public Answer<Set<ValueName.Behavior>> compute(Db db) {
            Answer<Hir.FnDef> body = db.ask(new BodyForInvariantDischarge(module, behavior));
            if (!body.present()) {
                return Answer.of(Set.of());
            }
            Map<BindingId, ValueName.Behavior> injected =
                    injectedInto(db, module, behavior, body.value());
            Set<ValueName.Behavior> reached = new LinkedHashSet<>();
            List<Hir.Expr> todo = new ArrayList<>();
            todo.add(body.value().writtenBody());
            while (!todo.isEmpty()) {
                Hir.Expr at = todo.remove(todo.size() - 1);
                if (at == null) {
                    continue;
                }
                if (at instanceof Hir.Var.Denoting name) {
                    ValueName denotes = name.denotes();
                    if (denotes instanceof ValueName.Behavior each) {
                        reached.add(each);
                    } else if (denotes instanceof ValueName.Local local) {
                        ValueName.Behavior each = injected.get(local.id());
                        if (each != null) {
                            reached.add(each);
                        }
                    }
                }
                Hir.forEachChild(at, todo::add);
            }
            return Answer.of(Ordered.set(reached));
        }
    }

    /**
     * The behaviors {@code depends on} hands {@code body}, by the binding each arrives as.
     *
     * <p>By the binding and not by the spelling. A name in the body is one of these only when it was
     * answered with that binding, because a binding in force wins over the declaration it shadows —
     * which is the reading {@link Lower#body} takes of the same clause, and taking a different one
     * here would be two answers to keep agreeing.
     *
     * <p>Not {@link #dependencyParams}, which asks the same clause a different question: that one is
     * which parameters the body has, and a clause naming something that is not a behavior still
     * names one of those. This is which behaviors those parameters stand for, and a clause that
     * names no behavior contributes none.
     */
    private static Map<BindingId, ValueName.Behavior> injectedInto(Db db, String module,
                                                                   String behavior,
                                                                   Hir.FnDef body) {
        Answer<Hir.SpecBehavior> spec = db.ask(new Spec(module, behavior));
        if (!spec.present()) {
            return Map.of();
        }
        Map<String, ValueName.Behavior> declared = new LinkedHashMap<>();
        for (Hir.Var req : spec.value().dependsOn()) {
            // Reported where it is written; it names no parameter for a body to reach it through.
            if (req.answered() instanceof Hir.Var.Denoting named
                    && named.denotes() instanceof ValueName.Behavior each) {
                declared.put(each.name(), each);
            }
        }
        Map<BindingId, ValueName.Behavior> out = new LinkedHashMap<>();
        for (Hir.FnParam param : body.params()) {
            ValueName.Behavior each = declared.get(param.name());
            if (each != null) {
                out.put(param.binder().id(), each);
            }
        }
        return out;
    }

    /**
     * What the behaviors one body reaches state about their answers, by the name each is called
     * under.
     *
     * <p>A caller that has matched a case may take the rules about that case as holding, which is
     * what a declared relation is for (spec §ensures). What it may take is what the module that
     * declared the behavior said, so a borrowed one is read from the module that declares it and not
     * from anything this one holds. A module reached through its published classes answers the same
     * question: the declaration it published is read back by this front end, and what its author
     * wrote is what comes back (spec §published-modules).
     *
     * <p>Asked as a question of its own rather than assembled where it is used, so what a body was
     * checked against is a named answer in the graph: which behaviors it depends on the declarations
     * of is then something to read and to hold a test to, rather than something to work out from the
     * shape of a {@code compute}.
     */
    public record ContractsForBody(String module, String behavior)
            implements Key<Map<ValueName.Behavior, StatedContract>> {

        @Override
        public Answer<Map<ValueName.Behavior, StatedContract>> compute(Db db) {
            Answer<Set<ValueName.Behavior>> targets = db.ask(new BehaviorsReached(module, behavior));
            if (!targets.present()) {
                return Answer.absent();
            }
            Map<ValueName.Behavior, StatedContract> out = new LinkedHashMap<>();
            for (ValueName.Behavior each : targets.value()) {
                Answer<StatedContract> stated = db.ask(new Stated(each));
                if (stated.present()) {
                    out.put(each, stated.value());
                }
            }
            return Answer.of(Ordered.map(out));
        }
    }

    /**
     * What each behavior of a module states about its answer, read into the representation the
     * analysis has rules about and typed there, by the name the behavior is declared under.
     *
     * <p>The one reading of a rule as a term. Two readers want it — the editor, which shows how much
     * of each rule the check can read, and the check at a call, which takes what it may assume — and
     * both want the same thing of it: the rule as the analysis holds it, placed where its author
     * wrote it. Read twice, what an author is shown and what a caller is given would be two answers
     * to keep agreeing.
     *
     * <p>Nothing is reported from here. Whether a clause is well formed was decided by
     * {@link Contracts}, which owns both the contracts and what reading them found; a behavior whose
     * declaration cannot be read is left out of this rather than refused a second time.
     */
    public record StatedContracts(String name) implements Key<Map<String, StatedContract>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, StatedContract>> compute(Db db) {
            Answer<souther.compiler.check.Expandable> expandable = db.ask(new Shapes.Expandable(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<String, Sig>> signatures = db.ask(new Signatures(name));
            Answer<Map<String, Type>> helpers = db.ask(new RecursiveHelperSigs(name));
            if (!expandable.present() || !scope.present() || !signatures.present()
                    || !helpers.present()) {
                return Answer.absent();
            }
            Answer<Map<String, Hir.FnDef>> imported = db.ask(new ImportedDefinitions(name));
            Map<String, Hir.FnDef> published = imported.present() ? imported.value() : Map.of();
            Map<String, StatedContract> out = new LinkedHashMap<>();
            try {
                ClausesForDischarge declaring =
                        ClausesForDischarge.of(expandable.value(), scope.value(), published);
                for (Map.Entry<String, Hir.SpecBehavior> each
                        : declaring.behaviorsThatState().entrySet()) {
                    try {
                        BehaviorContract contract = BehaviorChecker.contractAsRead(each.getValue(),
                                name, signatures.value().get(each.getKey()), scope.value());
                        out.put(each.getKey(), StatedContract.of(contract, declaring, scope.value(),
                                helpers.value()));
                    } catch (Unanswerable | CompileException _) {
                        // The declaration could not be read, which is said where it is held to its
                        // rules. There is nothing to read into a term, and a behavior that cannot be
                        // read leaves the rest of the module's readable.
                    }
                }
            } catch (CompileException e) {
                return Answer.absent(e);
            }
            return Answer.of(Ordered.map(out));
        }
    }

    /**
     * The signatures of the behaviors a module declares, by the name each is declared under.
     *
     * <p>A projection of {@link Reachable} onto this module's own declarations, which is what a
     * reader walking the module's behaviors asks for. The bare name is a key here because the
     * module every one of them belongs to is the one being asked about.
     */
    public record Signatures(String name) implements Key<Map<String, Sig>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, Sig>> compute(Db db) {
            Answer<Map<ValueName.Behavior, Sig>> reachable = db.ask(new Reachable(name));
            if (!reachable.present()) {
                return Answer.absent();
            }
            Map<String, Sig> own = new LinkedHashMap<>();
            reachable.value().forEach((behavior, sig) -> {
                if (behavior.module().equals(name)) {
                    own.put(behavior.name(), sig);
                }
            });
            return Answer.of(Ordered.map(own));
        }
    }

    /**
     * The signatures of the behaviors a module borrows from others, each under the declaration it
     * is. A qualified behavior reference reaches one as much as an import line does, so both are
     * here.
     *
     * <p>Nothing is refused here for sharing a name. One bare spelling claimed by two import lines
     * is a question about what this module writes, and is settled where the lines are; a behavior
     * reached through its module claims no spelling, and is not in that contest.
     */
    public record Imported(String name) implements Key<Map<ValueName.Behavior, Sig>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<ValueName.Behavior, Sig>> compute(Db db) {
            // A module in a cycle borrows a signature from a module that borrows one from it. This
            // is where that would be asked, so this is where it stops; the cycle itself is reported
            // by Names.InCycle.
            if (Names.cyclic(db, name)) {
                return Answer.absent();
            }
            if (db.ask(new Front.Available(name)).value() == null) {
                return Answer.absent();
            }
            Map<ValueName.Behavior, Sig> result = new LinkedHashMap<>();
            for (ValueName.Behavior each : borrowed(db, name)) {
                Map<String, Sig> sigs = db.ask(new Signatures(each.module())).value();
                Sig sig = sigs == null ? null : sigs.get(each.name());
                if (sig != null) {
                    result.put(each, sig);
                }
            }
            return Answer.of(Ordered.map(result));
        }
    }

    /** The behaviors a module borrows that are injection targets where they are declared, so a
     * composition here inherits them as requirements of its own. */
    public record ImportedInjected(String name) implements Key<Set<ValueName.Behavior>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Set<ValueName.Behavior>> compute(Db db) {
            if (db.ask(new Front.Available(name)).value() == null) {
                return Answer.of(Set.of());
            }
            return Answer.of(Ordered.set(borrowedWhere(db, name, Injected::new)));
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
            Answer<Set<ValueName.Behavior>> injected = db.ask(new ImportedInjected(name));
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
    public record ReqSigs(String name) implements Key<Map<ValueName.Behavior, ReqSig>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<ValueName.Behavior, ReqSig>> compute(Db db) {
            Answer<souther.compiler.check.Prepared> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<ValueName.Behavior, Sig>> imported = db.ask(new Imported(name));
            Answer<Set<String>> own = db.ask(new Dependencies(name));
            Answer<Set<ValueName.Behavior>> borrowed = db.ask(new ImportedDependencies(name));
            if (!prepared.present() || !scope.present() || !imported.present()
                    || !own.present() || !borrowed.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(InjectionSigs.dependencies(name, prepared.value().behaviors(),
                        scope.value(), own.value(), imported.value(), borrowed.value()));
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
    public record CalleeSigs(String name) implements Key<Map<ValueName.Behavior, ReqSig>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<ValueName.Behavior, ReqSig>> compute(Db db) {
            Answer<souther.compiler.check.Prepared> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<ValueName.Behavior, Sig>> imported = db.ask(new Imported(name));
            Answer<Set<String>> own = db.ask(new Callable(name));
            Answer<Set<ValueName.Behavior>> borrowed = db.ask(new ImportedCallable(name));
            if (!prepared.present() || !scope.present() || !imported.present()
                    || !own.present() || !borrowed.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(InjectionSigs.callable(name, prepared.value().behaviors(),
                        scope.value(), own.value(), imported.value(), borrowed.value()));
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
    public record NamedBehaviorArity(String name)
            implements Key<Map<ValueName.Behavior, Integer>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<ValueName.Behavior, Integer>> compute(Db db) {
            Answer<Map<ValueName.Behavior, ReqSig>> sigs = db.ask(new CalleeSigs(name));
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
            Answer<Map<ValueName.Behavior, ReqSig>> reqSigs = db.ask(new ReqSigs(name));
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
            // Which definitions of another module this one may read is what its import lines
            // were left with, and it is settled where claims are settled. Asked of that module
            // again, a definition it publishes could be read under a spelling no line got — the
            // claim having lost a contest, or come in on a line that was refused — and the leave
            // would be granted a second time to a claim that did not stand.
            Map<String, List<PublishedHelper>> byModule = new LinkedHashMap<>();
            leaves(db, name).values().forEach(leave -> byModule
                    .computeIfAbsent(leave.module(), k -> new ArrayList<>()).add(leave));
            Map<String, Hir.FnDef> out = new LinkedHashMap<>();
            for (Map.Entry<String, List<PublishedHelper>> allowed : byModule.entrySet()) {
                Answer<Hir.Module> from = db.ask(new Settled(allowed.getKey()));
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
                        db.ask(new Expanding(allowed.getKey(), InliningPolicy.FULL));
                if (!from.present() || !against.present()) {
                    continue;
                }
                // Two imports reaching one definition reach one definition: the name it is keyed by
                // is the module that declares it and its own name, so the second arrival is the same
                // entry rather than a second copy of the method.
                publishedClosure(from.value(), allowed.getValue(), against.value())
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
    private static Map<String, Hir.FnDef> publishedDefinitions(Hir.Module from,
                                                               Collection<PublishedHelper> allowed,
                                                               Expanding.Of against) {
        Map<String, Hir.FnDef> out = new LinkedHashMap<>();
        HelperInliner inliner = null;
        for (Hir.FnDef fn : bodiesOf(from, allowed)) {
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
    public static Map<String, Hir.FnDef> publishedClosure(Hir.Module from,
                                                          Collection<PublishedHelper> allowed,
                                                          Expanding.Of against) {
        Map<String, Hir.FnDef> out = publishedDefinitions(from, allowed, against);
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

    /**
     * The bodies {@code from} was given leave to hand over, in the order it declared them.
     *
     * <p>Nothing here decides what is published. Each of {@code allowed} is a
     * {@link PublishedHelper}, which only a reading of that module can make — so this reads the
     * bodies it was told it may read and has no way to reach any other. What it does decide is the
     * order, and that is the declaring module's: these become methods of the reader, and the module
     * that wrote them is what says which comes first.
     */
    private static List<Hir.FnDef> bodiesOf(Hir.Module from, Collection<PublishedHelper> allowed) {
        Map<String, Hir.FnDef> helpers = HelperInliner.helpersOf(from);
        // Every leave is redeemed, and redeeming one is the only way to a body. Reading the module
        // first and keeping whichever definitions a leave happened to name would let a leave for
        // something that module has not got go by unnoticed, which is the disagreement worth
        // knowing about.
        Map<String, Hir.FnDef> found = new LinkedHashMap<>();
        for (PublishedHelper each : allowed) {
            found.put(each.name(), bodyOf(from, helpers, each));
        }
        List<Hir.FnDef> out = new java.util.ArrayList<>();
        for (String declared : helpers.keySet()) {
            Hir.FnDef fn = found.get(declared);
            if (fn != null) {
                out.add(fn);
            }
        }
        return out;
    }

    /**
     * A leave to read a definition, and a module that has no such definition to hand over.
     *
     * <p>Not a limit of an analysis. A reading said that module publishes the name, and a reading
     * is what every reader of that module is answered from — so a settled module without the body
     * is the compiler holding two answers to one question, and the reader that swallowed it would
     * publish nothing and look exactly like a reader that had nothing to publish.
     */
    static final class ALeaveAndAModuleDisagree extends RuntimeException
            implements souther.compiler.diag.TheCompilerDisagreesWithItself {

        private static final long serialVersionUID = 1L;

        ALeaveAndAModuleDisagree(String message) {
            super(message);
        }
    }

    /**
     * The body {@code leave} is leave to read.
     *
     * <p>Takes the leave rather than the name, so that reaching a definition of another module and
     * being allowed to are one step. What it checks is that the two agree about whose module this
     * is: a leave is about one module, and read against another's tree it would hand back a
     * definition nobody published under a name that happens to be spelt the same.
     *
     * <p>A body that is not written here is the reading and the settled module disagreeing about
     * what is published, which is not something either of them may recover from — the reading said
     * a body would be here to hand over.
     */
    private static Hir.FnDef bodyOf(Hir.Module from, Map<String, Hir.FnDef> helpers,
                                    PublishedHelper leave) {
        if (!from.name().equals(leave.module())) {
            throw new ALeaveAndAModuleDisagree("`" + leave
                    + "` is leave to read a definition of `" + leave.module()
                    + "`, read against `" + from.name() + "`");
        }
        Hir.FnDef fn = helpers.get(leave.name());
        if (fn == null || !(fn.body() instanceof Hir.FnBody.Written)) {
            throw new ALeaveAndAModuleDisagree("`" + leave
                    + "` is published, and the settled module has no body written for it");
        }
        return fn;
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
            Answer<Map<ValueName.Behavior, Integer>> behaviors =
                    db.ask(new NamedBehaviorArity(module));
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
            Answer<Map<ValueName.Behavior, Integer>> behaviors =
                    db.ask(new NamedBehaviorArity(module));
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
                names.add(named.denotes().name());
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
            Answer<Map<ValueName.Behavior, ReqSig>> calleeSigs = db.ask(new CalleeSigs(module));
            Answer<Map<ValueName.Behavior, ReqSig>> reqSigs = db.ask(new ReqSigs(module));
            Answer<HelperInliner> inliner = expanding(db, module, InliningPolicy.FULL);
            Answer<Map<String, Type>> sigs = db.ask(new RecursiveHelperSigs(module));
            Answer<Map<String, DataChecker.Constructs>> constructs =
                    db.ask(new RecursiveHelperConstructs(module));
            Answer<Hir.FnDef> discharge = db.ask(new BodyForInvariantDischarge(module, behavior));
            Answer<Map<TypeSymbol, List<Hir.InvariantClause>>> dischargeInvariants =
                    db.ask(new Shapes.InvariantsForDischarge(module));
            // What the behaviors this body reaches state about their answers, and only those: a
            // relation declared by a behavior it does not call is no part of what it is checked
            // against, and depending on one would re-check this body whenever that one was edited.
            Answer<Map<ValueName.Behavior, StatedContract>> contracts =
                    db.ask(new ContractsForBody(module, behavior));
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
                            dischargeInvariants.present() ? dischargeInvariants.value() : Map.of(),
                            contracts.present() ? contracts.value() : Map.of())
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
     * Every claim a module's bodies make that the model's own rules contradict.
     *
     * <p>Where a premise that cannot hold belongs: a claim the rules refute is a model whose own
     * signature admits an input it aborts on, and that is a mistake in the model rather than a note
     * about how well it is covered. Read from the bodies as they are emitted, which is what every
     * measure reads, so that a claim is judged in the shape it is acted on — a claim written in a
     * helper this body calls is judged against the input the call gave it.
     *
     * <p>Nothing is said where the signature is not in hand: a behavior whose signature did not work
     * out has been reported on for that.
     */
    private static Map<String, souther.compiler.claims.Claims> judged(
            Db db, String module, Hir.Module settled, Map<String, Core> bodies) {
        Answer<Symbols> scope = db.ask(new Shapes.Scope(module));
        Answer<Map<String, souther.compiler.inputs.InputDomain>> inputs =
                db.ask(new souther.compiler.query.Adequacy.Inputs(module));
        if (!scope.present() || !inputs.present()) {
            return Map.of();
        }
        // The same numbering every measure is taken over, so a claim and the reading that judges it
        // name one arm. Built from the same bodies, which is what makes the two agree.
        //
        // Made here rather than asked for. What arrives is read off the checked bodies, so the
        // query that answers it for a report depends on this one and cannot be asked from inside
        // it. Both routes call one function over one input; what is not shared is the memo.
        souther.compiler.coverage.CoverageSites.Plan plan =
                souther.compiler.coverage.CoverageSites.of(bodies);
        Map<String, souther.compiler.claims.Claims> out = new LinkedHashMap<>();
        for (Hir.BehaviorDef behavior : settled.behaviors()) {
            souther.compiler.inputs.InputDomain read = inputs.value().get(behavior.name());
            Core body = bodies.get(behavior.name());
            if (!(behavior instanceof Hir.SpecBehavior) || read == null || body == null) {
                continue;
            }
            Hir.FnDef fn = db.ask(new SettledFn(module, behavior.name())).value();
            out.put(behavior.name(), souther.compiler.claims.Claims.of(
                    souther.compiler.claims.UnreachableClaims.of(body, read, scope.value(), plan),
                    souther.compiler.check.PathReachability.of(
                            body, (Hir.SpecBehavior) behavior, fn, plan, read, scope.value())));
        }
        // In the order the module declares them, which is the order a reader meets the diagnostics
        // these carry. `Map.copyOf` keeps the entries and not the order (see `Ordered`), so a
        // module with two refused claims reported them in whichever order the hashes fell.
        return Ordered.map(out);
    }

    /** The claims a model's own rules contradict, as reports. Read from the judging above rather
     *  than judged again: what refuses a build and what a report prints are one answer. */
    private static List<Report> contradicted(Db db, String module,
                                             Map<String, souther.compiler.claims.Claims> claims) {
        Answer<Map<String, souther.compiler.inputs.InputDomain>> inputs =
                db.ask(new souther.compiler.query.Adequacy.Inputs(module));
        if (!inputs.present()) {
            return List.of();
        }
        List<Report> out = new ArrayList<>();
        claims.forEach((behavior, judged) -> {
            for (Diagnostic refused : souther.compiler.claims.ClaimDiagnostics.refusals(
                    judged, inputs.value().get(behavior))) {
                out.add(Report.of(refused));
            }
        });
        return List.copyOf(out);
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
            Answer<Set<ValueName.Behavior>> injected = db.ask(new ImportedInjected(name));
            Answer<Map<ValueName.Behavior, ReqSig>> reqSigs = db.ask(new ReqSigs(name));
            Answer<Map<String, Type>> sigs = db.ask(new RecursiveHelperSigs(name));
            Answer<Map<ValueName.Behavior, ReqSig>> calleeSigs = db.ask(new CalleeSigs(name));
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
            // What a behavior declares about its answer is read by its own key, which owns both the
            // contracts and what reading them found. Asked here so that a module with a clause that
            // cannot be read is a module that does not reach codegen: the reports are that key's and
            // are not repeated, and what is read off them here is whether there was a refusal.
            Answer<Map<String, BehaviorContract>> contracts = db.ask(new Contracts(name));
            boolean sound = reported.errors().isEmpty() && reported.abandoned().isEmpty()
                    && contracts.present() && !contracts.hasError();
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
        private final Map<String, souther.compiler.claims.Claims> claims;

        private Elaborated(Map<String, Core> behaviorBodies, Map<String, Core> emittedHelpers,
                           Map<String, souther.compiler.claims.Claims> claims) {
            this.behaviorBodies = behaviorBodies;
            this.emittedHelpers = emittedHelpers;
            this.claims = claims;
        }

        /** The Core of each behavior body, by the behavior's name. */
        public Map<String, Core> behaviorBodies() {
            return behaviorBodies;
        }

        /** The Core of each helper the module emits as a method of its own. */
        public Map<String, Core> emittedHelpers() {
            return emittedHelpers;
        }

        /**
         * What each body declares cannot arrive, judged against the reading of its input.
         *
         * <p>Made here because this is where the bodies are: the refusal of a contradicted claim is
         * a report of this check, and a report of a confirmed or an unproven one is the measure's,
         * and both read this. Made twice they would be two answers to one question, and the one
         * that refuses a build and the one a report prints are the last two that should differ.
         */
        public Map<String, souther.compiler.claims.Claims> claims() {
            return claims;
        }
    }

    /**
     * What each behavior of one module declared cannot arrive, in the words a report writes.
     *
     * <p>A projection of the judging the body check already made, and the only way out of it: what
     * a report holds is what was said about a case, and not the verdicts a measure could act on.
     * One entry per case of a position, however many arms declared it.
     */
    public record Claimed(String name) implements Key<Map<String, ClaimAnnotations>> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, ClaimAnnotations>> compute(Db db) {
            Elaborated checked = db.ask(new Checked(name)).value();
            if (checked == null) {
                return Answer.absent();
            }
            Map<String, ClaimAnnotations> out = new LinkedHashMap<>();
            checked.claims().forEach((behavior, claims) ->
                    out.put(behavior, ClaimAnnotations.of(claims)));
            return Answer.of(Ordered.map(out));
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
            if (!sound) {
                return Answer.absent();
            }
            // What each body declares cannot arrive, held against what its input's own declarations
            // leave. Judged here rather than beside each body: it reads the signature, which is the
            // module's, and a body's own answer must not move when the one beside it is edited.
            //
            // Only of a module that came out whole. A model with a hole in it has been reported on
            // where the hole is, and what a case can arrive at cannot be read through one — asked
            // anyway, the reading meets a shape no position can have and says so about this
            // compiler, which is true and is not what the author of a mistyped model needs.
            Map<String, souther.compiler.claims.Claims> claims =
                    judged(db, name, settled.value(), bodies);
            return Answer.of(new Elaborated(bodies, module.value().emittedHelpers(), claims),
                    contradicted(db, name, claims));
        }
    }
}
