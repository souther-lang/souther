package souther.compiler.query;

import souther.compiler.check.ClauseLocations;
import souther.compiler.check.InvariantFinding;
import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.ast.Ast;
import souther.compiler.ast.DefinitionName;
import souther.compiler.ast.Hir;
import souther.compiler.check.AnalysisBody;
import souther.compiler.check.Expansion;
import souther.compiler.check.BehaviorChecker;
import souther.compiler.check.BindingEvidence;
import souther.compiler.check.ParameterFact;
import souther.compiler.check.SpecChecker;
import souther.compiler.check.SpecImplementation;
import souther.compiler.check.CheckSurface;
import souther.compiler.check.InvariantSettled;
import souther.compiler.check.SettledInvariant;
import souther.compiler.check.BehaviorContract;
import souther.compiler.check.CheckedEnsures;
import souther.compiler.core.EnsuresEnforcement;
import souther.compiler.check.BehaviorRequirement;
import souther.compiler.check.AssumedContract;
import souther.compiler.check.ClausesForDischarge;
import souther.compiler.check.StatedContract;
import souther.compiler.check.ContractDischarge;
import souther.compiler.check.DataChecker;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.SignatureDeclarations;
import souther.compiler.check.HelperEntry;
import souther.compiler.check.HelperInliner;
import souther.compiler.check.Preserved;
import souther.compiler.check.ValueEntries;
import souther.compiler.core.CompleteSignature;
import souther.compiler.check.CarriedBodyDependencies;
import souther.compiler.check.DeclarationKinds;
import souther.compiler.check.PublishedDeclarations;
import souther.compiler.check.Expansion;
import souther.compiler.check.HelperGraph;
import souther.compiler.check.HelperNames;
import souther.compiler.copied.CopyTarget;
import souther.compiler.check.HelperTable;
import souther.compiler.check.InjectionSigs;
import souther.compiler.inputs.InputDomain;
import souther.compiler.check.InliningPolicy;
import souther.compiler.check.InvariantChecker;
import souther.compiler.check.Lower;
import souther.compiler.check.LoweredDefinition;
import souther.compiler.check.LoweringRole;
import souther.compiler.check.PipelineSigs;
import souther.compiler.check.ModuleUniverse.InSight.Read.PublishedHelper;
import souther.compiler.check.ReqSig;
import souther.compiler.check.Resolve;
import souther.compiler.check.Scoping;
import souther.compiler.check.BehaviorBodies;
import souther.compiler.check.BehaviorImplementation;
import souther.compiler.check.Sig;
import souther.compiler.check.SpecChecker;
import souther.compiler.check.DerivedSymbols;
import souther.compiler.check.TypeChecker;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TemplateChecker;
import souther.compiler.check.Unanswerable;
import souther.compiler.core.Contract;
import souther.compiler.core.Core;
import souther.compiler.core.GrowingFold;
import souther.compiler.core.ValueShape;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.Message;
import souther.compiler.diag.msg.ModuleMessage;
import souther.compiler.diag.msg.Reported;
import souther.compiler.meta.ModuleReadback;
import souther.compiler.claims.ClaimDiagnostics;
import souther.compiler.claims.Claims;
import souther.compiler.claims.UnreachableClaims;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.EmittedDefinition;
import souther.compiler.check.Expandable;
import souther.compiler.check.PathReachability;
import souther.compiler.check.UninhabitableTypes;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.DecisionSource;
import souther.compiler.coverage.DecisionSources;
import souther.compiler.coverage.ModuleBodies;
import souther.compiler.coverage.NumberingIdentity;
import souther.compiler.coverage.SuppliedRules;
import souther.compiler.sites.SemanticSnapshot;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.BindingId;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Collections;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * What the code in a module comes to: the signatures of the behaviors it declares and of the ones
 * it borrows, the bodies with their helper calls expanded, and the result of checking them.
 */
public final class Bodies {

    private Bodies() {}

    /**
     * Where each behavior of a module gets its body: written here, Souther's to write and not
     * written, or Java's to supply (spec §injected-behavior, §unwritten-behavior).
     *
     * <p>The one place a behavior is classified. Every reader asks this, so that the two things an
     * absent {@code let} can mean are two answers rather than one — and so that a module read off
     * the path, whose tree carries no {@code let} at all, is answered with what it published rather
     * than classified again from a tree that cannot say.
     */
    public record Implementation(String name) implements Key<BehaviorBodies> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<BehaviorBodies> compute(Db db) {
            Front.FromPath.OnThePath onThePath = Front.onThePath(db, name);
            if (onThePath != null) {
                // A module off the path published where each of its behaviors gets its body,
                // because the fn that decides is not published with it.
                return Answer.of(new BehaviorBodies(name, onThePath.behaviorImplementations()));
            }
            Ast.Module m = db.ask(new Front.Available(name)).value();
            if (m == null) {
                return Answer.of(new BehaviorBodies(name, Map.of()));
            }
            return Answer.of(BehaviorBodies.fromSource(m));
        }
    }

    /** The behaviors of a module Java supplies, read off {@link Implementation}. */
    public record Injected(String name) implements Key<Set<String>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Set<String>> compute(Db db) {
            return where(db, name, BehaviorImplementation::isInjectionTarget);
        }
    }

    /** The behaviors of a module Souther is to implement and nobody has, read off the same. */
    public record Unwritten(String name) implements Key<Set<String>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Set<String>> compute(Db db) {
            return where(db, name, s -> s == BehaviorImplementation.UNIMPLEMENTED);
        }
    }

    private static Answer<Set<String>> where(Db db, String module,
                                             Predicate<BehaviorImplementation> is) {
        Answer<BehaviorBodies> states = db.ask(new Implementation(module));
        // Absent rather than empty. A module whose classification could not be asked has not been
        // shown to have no unwritten behaviors, and a caller told there are none rests on it: the
        // rule that nothing built here may hold one would then pass for want of an answer.
        if (!states.present() || states.value() == null) {
            return Answer.absent();
        }
        Set<String> named = new LinkedHashSet<>();
        states.value().states().forEach((name, state) -> {
            if (is.test(state)) {
                named.add(name);
            }
        });
        return Answer.of(Ordered.set(named));
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
            return borrowedWhere(db, name, Dependencies::new);
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
     * declared — an injection target, one that may be called by name, one that requires something,
     * one nobody has written.
     *
     * <p>One walk for the four, so that which of them a borrowed behavior falls into is asked of
     * the module that declares it in one way. Asked of the declaration and not of a name: the
     * question is about that module's own behavior, so the name it goes by there is the whole of
     * what is handed over, and what this module happens to write for it never enters.
     *
     * <p>A module with no source borrows nothing, and that is the answer rather than an absence.
     */
    private static Answer<Set<ValueName.Behavior>> borrowedWhere(
            Db db, String module, Function<String, Key<Set<String>>> asks) {
        if (db.ask(new Front.Available(module)).value() == null) {
            return Answer.of(Set.of());
        }
        Set<ValueName.Behavior> out = new LinkedHashSet<>();
        for (ValueName.Behavior each : borrowed(db, module)) {
            Set<String> there = db.ask(asks.apply(each.module())).value();
            if (there != null && there.contains(each.name())) {
                out.add(each);
            }
        }
        return Answer.of(Ordered.set(out));
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
            return borrowedWhere(db, name, Callable::new);
        }
    }

    /**
     * What each behavior this module declares was admitted as: its parameters as they are written,
     * beside the shapes they arrive as, and what it answers.
     *
     * <p>Where a declaration is admitted, and the only place. A reader that pairs a signature with
     * the declaration it was made from asks for this rather than for the two separately — the
     * pairing is what the walk had in hand, and asking for it is how a reader gets it instead of
     * working it out again from two lists.
     *
     * <p>Compositions are not here. One declares stages and takes what its first stage takes, so it
     * has no parameters of its own to name; its signature is worked out in {@link Reachable}.
     *
     * <p>Read where the behaviors are settled and not from the assembly: what a row's positions are
     * read against is worked out here, so the assembly asks this and this cannot ask the assembly.
     * No rung at or below the settling rewrites a behavior, and what each takes and answers with is
     * read off its declaration — so a module one of whose data did not come out has signatures all
     * the same.
     */
    public record DeclaredSignatures(String name) implements Key<Map<String, DeclaredSig>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, DeclaredSig>> compute(Db db) {
            Answer<InvariantSettled> settling = db.ask(new Shapes.Settling(name));
            Answer<DerivedSymbols> scope = Names.derivedSymbols(db, name);
            if (!settling.present() || !scope.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(Ordered.map(SignatureDeclarations.of(
                        settling.value().behaviors(), scope.value(),
                        Shapes.declarationKinds(db), Shapes.publishedDeclarations(db))));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
        }
    }

    /**
     * One behavior's declared signature, read out of its module's index of them.
     *
     * <p>The index is the module's identity: declaring a behavior beside this one changes it, and a
     * reader that took it would answer about this behavior again for a declaration this behavior
     * says nothing about. Read here and projected, the index is still built once and what comes out
     * of this is the same answer until this signature moves.
     */
    public record DeclaredSignature(String module, String behavior) implements Key<DeclaredSig> {

        @Override
        public Answer<DeclaredSig> compute(Db db) {
            Answer<Map<String, DeclaredSig>> declared = db.ask(new DeclaredSignatures(module));
            if (!declared.present()) {
                return Answer.absent();
            }
            DeclaredSig one = declared.value().get(behavior);
            return one == null ? Answer.absent() : Answer.of(one);
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
            Answer<InvariantSettled> settling = db.ask(new Shapes.Settling(name));
            Answer<DerivedSymbols> scope = Names.derivedSymbols(db, name);
            Answer<Map<String, DeclaredSig>> declared = db.ask(new DeclaredSignatures(name));
            Answer<Map<ValueName.Behavior, Sig>> imported = db.ask(new Imported(name));
            if (!settling.present() || !scope.present() || !declared.present()
                    || !imported.present()) {
                return Answer.absent();
            }
            Map<String, Sig> boundaries = new LinkedHashMap<>();
            declared.value().forEach((behavior, sig) -> boundaries.put(behavior, sig.boundary()));
            try {
                return Answer.of(PipelineSigs.signatures(name, settling.value().behaviors(),
                        boundaries, scope.value(), Shapes.publishedDeclarations(db),
                        Shapes.declarationKinds(db), imported.value()));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
        }
    }

    /**
     * What this module's declarations say about each parameter its {@code let}s wrote.
     *
     * <p>A question about the revision and about nothing else. What it comes to is read by an editor
     * asking about one position — which parameter a hint stands after, what type a name in a body
     * has — and a reader that worked it out where it asked would work out what every other behavior
     * of the module declares to answer about one of them. So the table is the answer to a question
     * of its own, and the second reader of a revision is handed the first reader's.
     *
     * <p>Asked here rather than kept on the snapshot that reads it. A {@link
     * SemanticSnapshot} is built where it is used and dropped there, which is
     * what makes it safe to ask about a buffer mid-edit; a field on one would live for one question.
     *
     * <p>Absent where the module's names are not resolved or its signatures could not be worked out.
     * That is this reading having nothing to say, which is not the same as a module whose {@code
     * let}s wrote no parameters.
     */
    public record DeclaredParameters(String name) implements Key<List<ParameterFact>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<List<ParameterFact>> compute(Db db) {
            Answer<Hir.Module> resolved = db.ask(new Names.Resolved(name));
            Answer<Map<String, DeclaredSig>> signatures = db.ask(new DeclaredSignatures(name));
            if (!resolved.present() || !signatures.present()) {
                return Answer.absent();
            }
            Answer<Map<ValueName.Behavior, Sig>> reachable = db.ask(new Reachable(name));
            return Answer.of(ParameterFact.of(resolved.value(), signatures.value(),
                    reachable.present() ? reachable.value() : Map.of()));
        }
    }

    /**
     * What a body's names are declared to be, for the parameters of every behavior of this module.
     *
     * <p>The cut {@link DeclaredParameters} is read through by the walk that says what an expression
     * is declared to be. That walk is handed bindings and asks after the one it is looking at, so
     * what it needs is the table under the binding rather than the list the declarations were read
     * off — and building that from the list is work proportional to the module, which put back at
     * each reader is the thing being answered once here.
     *
     * <p>The injected parameters as well as the inputs. A name a body reads is a name whatever it
     * stands for, and one standing for a behavior the module was handed has a type as much as one
     * standing for an input does — so a reader asking what {@code dep(x).field} is gets the same
     * answer here as it would for a call written any other way.
     *
     * <p>A parameter nothing here types is left out, which is a fact being absent rather than the
     * parameter being. What is wrong with a definition the declaration does not account for is
     * reported where it is written.
     */
    public record DeclaredParameterBindings(String name)
            implements Key<Map<BindingId, BindingEvidence>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<BindingId, BindingEvidence>> compute(Db db) {
            Answer<List<ParameterFact>> facts = db.ask(new DeclaredParameters(name));
            if (!facts.present()) {
                return Answer.absent();
            }
            Map<BindingId, BindingEvidence> declared = new LinkedHashMap<>();
            for (ParameterFact fact : facts.value()) {
                switch (fact) {
                    case ParameterFact.TypedInput(Hir.FnParam written, Type arrives) ->
                            declared.put(written.binder().id(),
                                    new BindingEvidence.DeclaredAs(arrives));
                    case ParameterFact.TypedInjection(Hir.FnParam written, Type takes) ->
                            declared.put(written.binder().id(),
                                    new BindingEvidence.DeclaredAs(takes));
                    case ParameterFact.Untyped _ -> { }
                }
            }
            return Answer.of(Ordered.map(declared));
        }
    }

    /**
     * What every behavior this module can name declares of its answer — its own and the ones it
     * borrows — each under the declaration it belongs to.
     *
     * <p>What a stand-in is held to. A {@code fake} row and a {@code with} state what a dependency
     * answers, and that dependency may be declared in another module, whose clause is the one the
     * value has to keep; the check it is held by is emitted where the behavior is declared, so the
     * module travels with the contract rather than being taken from wherever the row was written.
     *
     * <p>Beside {@link Contracts} and not in place of it: a module's own contracts are what its
     * emitter and its report read, and widening that answer would hand every reader of it clauses
     * belonging to somewhere else.
     */
    public record ReachableContracts(String name)
            implements Key<Map<ValueName.Behavior, CheckedEnsures>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<ValueName.Behavior, CheckedEnsures>> compute(Db db) {
            Answer<Map<String, CheckedEnsures>> own = db.ask(new Contracts(name));
            if (!own.present()) {
                return Answer.absent();
            }
            Map<ValueName.Behavior, CheckedEnsures> out = new LinkedHashMap<>();
            own.value().forEach((behavior, ensures) ->
                    out.put(new ValueName.Behavior(name, behavior), ensures));
            for (ValueName.Behavior each : borrowed(db, name)) {
                Map<String, CheckedEnsures> there = db.ask(new Contracts(each.module())).value();
                CheckedEnsures ensures = there == null ? null : there.get(each.name());
                if (ensures != null) {
                    out.put(each, ensures);
                }
            }
            return Answer.of(Ordered.map(out));
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
    public record Contracts(String name) implements Key<Map<String, CheckedEnsures>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, CheckedEnsures>> compute(Db db) {
            Answer<Lower.Lowered> lowering = db.ask(new Lowering(name));
            Answer<DerivedSymbols> scope = Names.derivedSymbols(db, name);
            Answer<Map<String, DeclaredSig>> signatures = db.ask(new DeclaredSignatures(name));
            Answer<Map<String, Type>> helpers = db.ask(new RecursiveCallSigs(name, InliningPolicy.FULL));
            if (!lowering.present() || !scope.present() || !signatures.present()
                    || !helpers.present()) {
                return Answer.absent();
            }
            Map<String, CheckedEnsures> contracts = new LinkedHashMap<>();
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
                            signatures.value().get(spec.name()), scope.value(),
                            Shapes.publishedDeclarations(db), Shapes.declarationKinds(db),
                            helpers.value()));
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
            Answer<DerivedSymbols> scope = Names.derivedSymbols(db, name);
            Answer<RuleReadingSource> reading =
                    Shapes.ruleReading(db, name);
            if (!stated.present() || !scope.present() || !reading.present()) {
                return Answer.absent();
            }
            Map<String, ContractDischarge> out = new LinkedHashMap<>();
            // One world for every behavior of the module, since every rule of every one of them is
            // read in it.
            RuleReadingContext ruleReading = RuleReadingContext.of(reading.value(),
                    db.ask(new Front.Reading()).value(), db.readings());
            stated.value().forEach((behavior, rules) ->
                    out.put(behavior, ContractDischarge.of(rules, ruleReading)));
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
     * <p>Answered as what a caller may assume ({@link AssumedContract}), which is a different reading
     * from the one the declaration holds. A contract as the declaration holds it carries where its
     * terms were written, the ordinals the module numbered them with, and which clause each rule was
     * written under, and on that value nothing below an edit ever comes out equal: a blank line moves
     * every position under it, and a clause gaining a term moves every ordinal under it. A caller
     * reads none of them — it substitutes its own arguments into the terms and reads what they say.
     *
     * <p>A reading of its own rather than the same value compared loosely. An answer whose equality
     * says one thing and whose value says another is one a reader can tell apart after the store has
     * decided they are the same, and the store decides that on behalf of everything downstream. What
     * this hands over is a reading with nothing to ask about where a term stands, so the value and
     * what it is compared by are one. The declaration's own reading, with its places, is
     * {@link StatedContracts}, which is what an editor and a diagnostic want.
     *
     * <p>Absent where the behavior states nothing, and where the module that declares it could not be
     * read. Absence is what a caller wanting to know "is there anything to assume" is asking, and an
     * empty contract would be a second way to say it.
     */
    public record Assumptions(ValueName.Behavior behavior) implements Key<AssumedContract> {
        @Override
        public String module() {
            return behavior.module();
        }

        @Override
        public Answer<AssumedContract> compute(Db db) {
            Map<String, StatedContract> declared =
                    db.ask(new StatedContracts(behavior.module())).value();
            StatedContract stated = declared == null ? null : declared.get(behavior.name());
            return stated == null ? Answer.absent()
                    : Answer.of(stated.assumptions());
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
     * name written at the call denotes that parameter and not the behavior. Which parameter stands
     * for which behavior is asked of the division of the implementation's parameters rather than
     * worked out again: which of them the clause fills is {@link SpecImplementation}'s to say and
     * not a suffix measured here, the parameters are not paired with the clause by name because two
     * modules may declare a behavior of one name, and the answer is a binding because a
     * binding in force wins over the declaration it shadows (spec §fn-rules). Neither is a
     * difference a program can show here — a {@code depends on} its body never calls is refused
     * (E1603), so a shadow of that spelling has the parameter beside it — which is why it is asked
     * of the one place that decides it rather than settled again by whatever agrees today.
     *
     * <p>Every name, and not every application. A behavior named where a value goes becomes the
     * function it names, and what applies it may be a binding away, so a walk that only read
     * applications would miss one the body really does call. Measured: reached through a binding
     * that is then applied, and not reached at all where nothing reads the binding — a binding
     * nothing reads is not in the tree this walks. So the frontier is drawn wider than the
     * applications and comes out the same size, and a name that could be left in it costs a
     * dependency this body has not got rather than losing one it has.
     *
     * <p>Absent where the body or the declaration is not there to read, which is not the same
     * answer as reaching nothing: the check that reads contracts is skipped where the body is,
     * and a body that reaches no behavior is checked with none. Saying "nothing" for both would
     * let a reader take the first for the second.
     */
    public record BehaviorsReached(String module, String behavior)
            implements Key<Set<ValueName.Behavior>> {

        @Override
        public Answer<Set<ValueName.Behavior>> compute(Db db) {
            Answer<Expansion<Hir.FnDef>> body =
                    db.ask(new BodyForInvariantDischarge(module, behavior));
            Answer<Hir.SpecBehavior> spec = db.ask(new Spec(module, behavior));
            if (!body.present() || !spec.present()) {
                return Answer.absent();
            }
            Map<BindingId, ValueName.Behavior> injected = SpecImplementation
                    .align(spec.value(), body.value().value()).injectedBindings();
            Set<ValueName.Behavior> reached = new LinkedHashSet<>();
            List<Hir.Expr> todo = new ArrayList<>();
            todo.add(body.value().value().writtenBody());
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
            implements Key<Map<ValueName.Behavior, AssumedContract>> {

        @Override
        public Answer<Map<ValueName.Behavior, AssumedContract>> compute(Db db) {
            Answer<Set<ValueName.Behavior>> targets = db.ask(new BehaviorsReached(module, behavior));
            if (!targets.present()) {
                return Answer.absent();
            }
            Map<ValueName.Behavior, AssumedContract> out = new LinkedHashMap<>();
            for (ValueName.Behavior each : targets.value()) {
                Answer<AssumedContract> assumed = db.ask(new Assumptions(each));
                if (assumed.present()) {
                    out.put(each, assumed.value());
                }
            }
            return Answer.of(Ordered.map(out));
        }
    }

    /**
     * What the behaviors one body names take, by the name each is called under.
     *
     * <p>{@link CalleeSigs} is the module's index of everything callable in it, and a body wants the
     * entries for what it calls. Read whole, it hands this body the module's identity: declaring a
     * behavior no body calls changes the index, and every body of the module is checked again
     * against signatures none of them names differently. Read here and projected, the index is still
     * built once and what comes out of this is the same answer until one of these signatures moves.
     *
     * <p>Over what the body reaches rather than what it applies, which is the frontier
     * {@link BehaviorsReached} draws and the same one a body's contracts are read at. That frontier
     * is taken over the representation the discharge analysis reads, and this is handed to a check
     * that reads the fully expanded one — which is the same set of names, because a helper cannot
     * reach a behavior at all (E1818), so expanding one into a body brings no name the other tree
     * has not got.
     *
     * <p>One lookup by name is all the check does with it, so a body that named something not in
     * here would be told there is no such behavior — which is what a body naming something outside
     * its own frontier would have to be. Nothing iterates it, so nothing sees a smaller module.
     */
    public record CalleeSigsForBody(String module, String behavior)
            implements Key<Map<ValueName.Behavior, ReqSig>> {

        @Override
        public Answer<Map<ValueName.Behavior, ReqSig>> compute(Db db) {
            Answer<Set<ValueName.Behavior>> targets = db.ask(new BehaviorsReached(module, behavior));
            Answer<Map<ValueName.Behavior, ReqSig>> callable = db.ask(new CalleeSigs(module));
            if (!targets.present() || !callable.present()) {
                return Answer.absent();
            }
            Map<ValueName.Behavior, ReqSig> out = new LinkedHashMap<>();
            for (ValueName.Behavior each : targets.value()) {
                ReqSig sig = callable.value().get(each);
                if (sig != null) {
                    out.put(each, sig);
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
            Answer<Expandable> expandable = db.ask(new Shapes.Expandable(name));
            Answer<DerivedSymbols> scope = Names.derivedSymbols(db, name);
            Answer<Map<String, DeclaredSig>> signatures = db.ask(new DeclaredSignatures(name));
            Answer<Map<String, Type>> helpers = db.ask(new RecursiveCallSigs(name, InliningPolicy.FULL));
            if (!expandable.present() || !scope.present() || !signatures.present()
                    || !helpers.present()) {
                return Answer.absent();
            }
            Answer<Map<String, Hir.FnDef>> imported = db.ask(new ImportedDefinitions(name));
            Map<String, Hir.FnDef> published = imported.present() ? imported.value() : Map.of();
            Map<String, StatedContract> out = new LinkedHashMap<>();
            try {
                ClausesForDischarge declaring =
                        ClausesForDischarge.of(expandable.value(), scope.value(),
                                Shapes.publishedDeclarations(db), Shapes.declarationKinds(db),
                                published);
                for (Map.Entry<String, Hir.SpecBehavior> each
                        : declaring.behaviorsThatState().entrySet()) {
                    try {
                        BehaviorContract contract = BehaviorChecker.contractAsRead(each.getValue(),
                                name, signatures.value().get(each.getKey()),
                                Shapes.publishedDeclarations(db), Shapes.declarationKinds(db));
                        out.put(each.getKey(), StatedContract.of(contract, declaring, scope.value(),
                                Shapes.declarationAccess(db), helpers.value()));
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
     * What one behavior states about its answer, read out of its module's index of them.
     *
     * <p>Absent where the behavior states nothing, which is what a behavior with no clauses of its
     * own says, and absent again where its declaration could not be read — both are the same thing
     * to a reader, which has no rule of this behavior's to take.
     *
     * <p>The index is the module's identity: a clause the behavior beside this one states changes
     * it, and a reader that took it would answer about this behavior again for a rule that is not
     * about it.
     */
    public record Stated(String module, String behavior) implements Key<StatedContract> {

        @Override
        public Answer<StatedContract> compute(Db db) {
            Answer<Map<String, StatedContract>> stated = db.ask(new StatedContracts(module));
            if (!stated.present()) {
                return Answer.absent();
            }
            StatedContract one = stated.value().get(behavior);
            return one == null ? Answer.absent() : Answer.of(one);
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
            return borrowedWhere(db, name, Injected::new);
        }
    }

    /** The behaviors a module borrows that Souther is to implement and nobody has where they are
     * declared, so nothing here may rest on one. */
    public record ImportedUnwritten(String name) implements Key<Set<ValueName.Behavior>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Set<ValueName.Behavior>> compute(Db db) {
            return borrowedWhere(db, name, Unwritten::new);
        }
    }

    /**
     * The injection targets a module builds against: the imported ones it names, whose base lives
     * in the module that declares them, and its own (spec §injected-behavior,
     * §composition-with-requirements).
     *
     * <p>Whether a name is something to inject or something to construct. The requirement walk, the
     * placement of each {@code ensures} check and the emitter all decide it by this set, so they
     * cannot disagree about one behavior — and none of them decides it from a tree, which for a
     * module read off the path carries no {@code let} to tell an implemented behavior from one Java
     * supplies.
     */
    public record InjectionTargets(String name) implements Key<Set<ValueName.Behavior>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Set<ValueName.Behavior>> compute(Db db) {
            Answer<Set<ValueName.Behavior>> imported = db.ask(new ImportedInjected(name));
            Answer<Set<String>> own = db.ask(new Injected(name));
            if (!imported.present() || !own.present()) {
                return Answer.absent();
            }
            Set<ValueName.Behavior> injected = new LinkedHashSet<>(imported.value());
            for (String behavior : own.value()) {
                injected.add(new ValueName.Behavior(name, behavior));
            }
            return Answer.of(Ordered.set(injected));
        }
    }

    /**
     * What each behavior of a module requires injected to be constructed, and which definitions ask
     * for it ({@link Requirements}).
     *
     * <p>An entry for every behavior the module declares, an injected one answered with nothing.
     * So a reader asks for a behavior's entry and takes a missing one as this answer not holding
     * together, rather than working out from the behavior's implementation which of the two a
     * missing entry is.
     *
     * <p>The order is the injecting constructor's parameter order, so it is also the order an
     * example passes its fakes in: the emitter and the example verifier ask this one question rather
     * than each walking the stages, because a fake bound to the wrong parameter is not something
     * either side would notice.
     *
     * <p>Read off the lowered module — the same tree the backend emits from — so the two cannot be
     * looking at different behaviors.
     *
     * <p>A module read off the path is answered from what it published. It carries what each of its
     * behaviors requires and not which of its definitions asked, so each dependency is asked for by
     * the behavior it is published for. A module that imports it reads the dependencies and not the
     * requesters, and reads the same ones whichever way the module arrived.
     */
    public record Requirements(String name) implements Key<Map<String, List<BehaviorRequirement>>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, List<BehaviorRequirement>>> compute(Db db) {
            Front.FromPath.OnThePath onThePath = Front.onThePath(db, name);
            if (onThePath != null) {
                // What a module built against another version of its dependencies says it requires
                // is not taken in. Why is said where the module is held to them (BuiltAgainst).
                return db.ask(new BuiltAgainst(name)).present()
                        ? published(onThePath) : Answer.absent();
            }
            Answer<Lower.Lowered> lowering = db.ask(new Lowering(name));
            Answer<Set<ValueName.Behavior>> injected = db.ask(new InjectionTargets(name));
            Answer<Map<ValueName.Behavior, List<ValueName.Behavior>>> foreign =
                    db.ask(new ForeignStageRequirements(name));
            if (!lowering.present() || !injected.present() || !foreign.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(Ordered.map(souther.compiler.check.Requirements.of(
                        lowering.value().lowered(), injected.value(), foreign.value())));
            } catch (CompileException e) {
                // A composition that reaches itself has no requirement set to work out. The cycle is
                // reported where it is written; nothing is emitted for the module either way.
                return Answer.absent(e);
            }
        }
    }

    /**
     * What a module read off the path published each of its behaviors as requiring, taken as
     * published once the module has been held to what it was built against ({@link BuiltAgainst}).
     */
    private static Answer<Map<String, List<BehaviorRequirement>>> published(
            Front.FromPath.OnThePath onThePath) {
        Map<String, List<BehaviorRequirement>> published = new LinkedHashMap<>();
        onThePath.behaviorRequirements().forEach((behavior, dependencies) -> {
            List<BehaviorRequirement> each = new ArrayList<>();
            for (ValueName.Behavior dependency : dependencies) {
                each.add(new BehaviorRequirement(dependency, List.of(behavior)));
            }
            published.put(behavior, List.copyOf(each));
        });
        return Answer.of(Ordered.map(published));
    }

    /**
     * Whether what a module read off the path requires injected names behaviors the modules it names
     * declare (spec {@code [#a-reached-name-is-declared-by-its-module]}).
     *
     * <p>A question about names, beside the one about linkage ({@link Linkages.Held}). What a
     * behavior requires is what a composition built from it here is handed, whatever the module's
     * classes link against, so a requirement naming a behavior its module no longer declares is said
     * as that: the module was built against another version of the module it names.
     *
     * <p>Asked of every module read off the path, where the compilation's problems are gathered, and
     * not by whoever goes on to use some of the module. What a module was built against is a fact
     * about all of it.
     *
     * <p>A module compiled here is built against what it is compiled with, and agrees.
     */
    public record BuiltAgainst(String name) implements Key<Boolean> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Boolean> compute(Db db) {
            Front.FromPath.OnThePath onThePath = Front.onThePath(db, name);
            if (onThePath == null) {
                return Answer.of(Boolean.TRUE);
            }
            List<Report> reports = new ArrayList<>();
            for (List<ValueName.Behavior> required : onThePath.behaviorRequirements().values()) {
                for (ValueName.Behavior dependency : required) {
                    // A module nothing in this compilation has is said where the path is read.
                    Ast.Module there = db.ask(new Front.Available(dependency.module())).value();
                    if (there != null && !declaresBehavior(there, dependency.name())) {
                        reports.add(Report.raised(builtAgainstAnother(
                                new ModuleMessage.ItWasBuiltRequiringWhatTheModuleDoesNotDeclare(
                                        name, dependency.name(), dependency.module()),
                                name, dependency.module())));
                    }
                }
            }
            return reports.isEmpty() ? Answer.of(Boolean.TRUE) : Answer.absent(reports);
        }

        /** Whether {@code module} declares a behavior of that name — whether there is one, and
         *  nothing about what it is. */
        private static boolean declaresBehavior(Ast.Module module, String behavior) {
            for (Ast.BehaviorDef each : module.behaviors()) {
                if (each.name().equals(behavior)) {
                    return true;
                }
            }
            return false;
        }

        /** {@code said} about {@code module}, which was built against another version of
         *  {@code dependency}: said about the artifact to rebuild, whose code nobody here holds. */
        static <M extends Message & Reported> Diagnostic builtAgainstAnother(
                M said, String module, String dependency) {
            return Diagnostic.say(said)
                    .hint(new ModuleMessage.RebuildItAgainstTheModuleThisCompilationReads(
                            module, dependency))
                    .atCodeWrittenOutOfSight(ModuleReadback.provenanceOf(module))
                    .build();
        }
    }

    /**
     * What each stage of this module's compositions that another module declares requires, as that
     * module answered it ({@link Requirements}), in the order it takes them.
     *
     * <p>Two readers, one answer. The composition here requires what its stages do, and the
     * composition builds each stage — so the list that goes into this module's requirement sets is
     * the same list the stage's constructor is handed. Only the dependencies cross; which of the
     * declaring module's definitions asked for one does not.
     */
    public record ForeignStageRequirements(String name)
            implements Key<Map<ValueName.Behavior, List<ValueName.Behavior>>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<ValueName.Behavior, List<ValueName.Behavior>>> compute(Db db) {
            if (Names.cyclic(db, name)) {
                return Answer.absent();
            }
            Answer<Lower.Lowered> lowering = db.ask(new Lowering(name));
            Answer<Set<ValueName.Behavior>> injected = db.ask(new ImportedInjected(name));
            if (!lowering.present() || !injected.present()) {
                return Answer.absent();
            }
            Map<ValueName.Behavior, List<ValueName.Behavior>> out = new LinkedHashMap<>();
            for (ValueName.Behavior stage : souther.compiler.check.Requirements.foreignStages(
                    lowering.value().lowered(), injected.value())) {
                Answer<Map<String, List<BehaviorRequirement>>> there =
                        db.ask(new Requirements(stage.module()));
                if (!there.present()) {
                    return Answer.absent();
                }
                List<BehaviorRequirement> requirements = there.value().get(stage.name());
                if (requirements == null) {
                    throw new IllegalStateException("`" + stage.module() + "` answered no"
                            + " requirement set for `" + stage.name() + "`, which it declares and"
                            + " does not leave to Java");
                }
                out.put(stage, souther.compiler.check.Requirements.names(requirements));
            }
            return Answer.of(Ordered.map(out));
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
            // The behaviors, which the assembly carries and no rung rewrites: what each requires is
            // read off its declaration, and a module one of whose data did not come out declares
            // them all the same.
            Answer<CheckSurface> surface = db.ask(new Shapes.CheckSurface(name));
            Answer<DerivedSymbols> scope = Names.derivedSymbols(db, name);
            Answer<Map<ValueName.Behavior, Sig>> imported = db.ask(new Imported(name));
            Answer<Set<String>> own = db.ask(new Dependencies(name));
            Answer<Set<ValueName.Behavior>> borrowed = db.ask(new ImportedDependencies(name));
            if (!surface.present() || !scope.present() || !imported.present()
                    || !own.present() || !borrowed.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(InjectionSigs.dependencies(name, surface.value().behaviors(),
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
            Answer<CheckSurface> surface = db.ask(new Shapes.CheckSurface(name));
            Answer<DerivedSymbols> scope = Names.derivedSymbols(db, name);
            Answer<Map<ValueName.Behavior, Sig>> imported = db.ask(new Imported(name));
            Answer<Set<String>> own = db.ask(new Callable(name));
            Answer<Set<ValueName.Behavior>> borrowed = db.ask(new ImportedCallable(name));
            if (!surface.present() || !scope.present() || !imported.present()
                    || !own.present() || !borrowed.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(InjectionSigs.callable(name, surface.value().behaviors(),
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
     *
     * <p>The module's index, and no expansion reads it. What one body wants is the entries for the
     * behaviors it reaches, which {@link BehaviorAritiesForBody} projects out of this — read whole,
     * a behavior declared anywhere in the module would expand every body in it again.
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

    /**
     * The declarations one body's expansion writes into it, and the ones those write into
     * themselves.
     *
     * <p>What ends up in this body's tree, asked once. Two of the answers a body is checked against
     * are the module's index narrowed to the names its tree holds, and each narrowing is the same
     * question about the same body. Worked out where each is wanted, it is one walk written twice,
     * and two walks that have to agree about what an expansion writes in are two chances for one of
     * them to be wrong about it.
     *
     * <p>Over every name that reaches a declaration rather than over what is applied. A value is
     * handed over by writing its name and is substituted there, so a walk that followed only calls
     * would miss the definition that carries something in — and the closure, because what is
     * substituted may itself name something that is.
     *
     * <p><b>It stops at a recursion.</b> A call to a helper that recurses is left standing and
     * lowered to a method of its own, so what that helper's body names is written into that method
     * and not into this one. Followed through, this would hand a body the names of everything its
     * recursions reach and make an edit to one of those an edit to this body — which is the breadth
     * a narrowing is for.
     *
     * <p>Which definitions a body writes in is what the policy decides, so the policy is part of the
     * question: the discharge representation leaves the language's own operations standing where the
     * emitted one expands them.
     */
    public record WrittenIntoBody(String module, String fn, InliningPolicy policy)
            implements Key<Set<ReachName.Declaration>> {

        @Override
        public Answer<Set<ReachName.Declaration>> compute(Db db) {
            Answer<Hir.FnDef> def = db.ask(new SettledFn(module, fn));
            Answer<Expanding.Of> against = db.ask(new Expanding(module, policy));
            if (!def.present() || !against.present()) {
                return Answer.absent();
            }
            return Answer.of(Ordered.set(walked(def.value(), against.value(), false)));
        }
    }

    /**
     * The recursions one body's expansion leaves standing in it.
     *
     * <p>The calls that are still calls when the expansion is done. A helper that recurses is not
     * written into whoever called it — it is lowered to a method of its own and the call stays — so
     * a body holds the ones its own tree calls, through whatever non-recursive definitions were
     * written into it, and no others.
     *
     * <p><b>Not the closure through them.</b> What one of these constructs is attributed to whoever
     * calls it, and what the recursions <em>it</em> calls construct is already in that answer: the
     * index says what each recursion constructs transitively, so one entry carries the chain. A body
     * handed the entries of everything down that chain would be handed a recursion its tree never
     * names, and an edit to that one would be an edit to this body.
     *
     * <p>Which definitions a body reaches is what the policy decides, so the policy is part of the
     * question.
     */
    public record StandingRecursionsOfBody(String module, String fn, InliningPolicy policy)
            implements Key<Set<ReachName.Declaration>> {

        @Override
        public Answer<Set<ReachName.Declaration>> compute(Db db) {
            Answer<Hir.FnDef> def = db.ask(new SettledFn(module, fn));
            Answer<Expanding.Of> against = db.ask(new Expanding(module, policy));
            if (!def.present() || !against.present()) {
                return Answer.absent();
            }
            return Answer.of(Ordered.set(walked(def.value(), against.value(), true)));
        }
    }

    /**
     * The declarations reached from {@code def} without going into a recursion, answering with the
     * ones that recurse or the ones that do not.
     *
     * <p>One walk, because the walk is the same: a recursion is where it stops either way, and what
     * differs is which side of that boundary the caller wants. Written as two, the two would have to
     * go on agreeing about what an expansion writes into a body.
     */
    private static Set<ReachName.Declaration> walked(Hir.FnDef def, Expanding.Of against,
                                                     boolean wantingTheRecursions) {
        HelperTable table = against.table();
        Set<ReachName.Declaration> out = new LinkedHashSet<>();
        Set<ReachName.Declaration> walked = new LinkedHashSet<>();
        Deque<Hir.FnDef> todo = new ArrayDeque<>();
        todo.add(def);
        while (!todo.isEmpty()) {
            for (ReachName.Declaration each : writtenInto(todo.poll(), table)) {
                if (!walked.add(each)) {
                    continue;
                }
                if (against.graph().recurses(each)) {
                    // Left where it was called and lowered to a method of its own. Neither its body
                    // nor what that body reaches arrives here.
                    if (wantingTheRecursions) {
                        out.add(each);
                    }
                    continue;
                }
                if (!wantingTheRecursions) {
                    out.add(each);
                }
                Hir.FnDef written = table.reached(each);
                if (written != null) {
                    todo.add(written);
                }
            }
        }
        return out;
    }

    /**
     * The declarations one step of an expansion writes into {@code def}.
     *
     * <p>Two relations and both of them. A call is written out where it is called, and which calls
     * those are is {@link HelperInliner#helperCallsIn} — the same walk the graph of a module's
     * helpers is built from, so what is counted here is what the expansion counts and not a second
     * reading of it. A name that is not applied is the other: a value is substituted where it is
     * written, and nothing in the graph of calls says so.
     */
    private static Set<ReachName.Declaration> writtenInto(Hir.FnDef def, HelperTable table) {
        Set<ReachName.Declaration> out = new LinkedHashSet<>();
        if (!(def.body() instanceof Hir.FnBody.Written written)) {
            return out;
        }
        HelperInliner.helperCallsIn(table.library(), written.expr(), table.reachable(), out);
        for (ReachName.Declaration each : namesIn(def, new LinkedHashSet<>())) {
            if (table.reached(each) != null) {
                out.add(each);
            }
        }
        return out;
    }

    /**
     * How many inputs each behavior one body names takes, by the name it names each under.
     *
     * <p>{@link NamedBehaviorArity} is the module's index of what every behavior in it takes, and an
     * expansion wants the entries for the names its own body wrote. Read whole, it hands this body
     * the module's identity: declaring a behavior nothing here names moves the index, and every body
     * of the module is expanded again against arities none of them wrote differently.
     *
     * <p>Over the tree the expansion walks and not over the one the author wrote. A definition this
     * body names is written into it, so a behavior named in one of those is a behavior this body's
     * expansion asks the arity of: taken from the body alone, a value written {@code let f = twice}
     * and handed on would be left standing as a name where it has to become the behavior it denotes.
     * {@link WrittenIntoBody} is what those definitions are — which stops where a recursion does,
     * because a behavior named inside one is named in the method that recursion is lowered to and
     * not here.
     */
    public record BehaviorAritiesForBody(String module, String fn, InliningPolicy policy)
            implements Key<Map<ValueName.Behavior, Integer>> {

        @Override
        public Answer<Map<ValueName.Behavior, Integer>> compute(Db db) {
            Answer<Hir.FnDef> def = db.ask(new SettledFn(module, fn));
            Answer<Expanding.Of> against = db.ask(new Expanding(module, policy));
            Answer<Set<ReachName.Declaration>> written =
                    db.ask(new WrittenIntoBody(module, fn, policy));
            Answer<Map<ValueName.Behavior, Integer>> arities =
                    db.ask(new NamedBehaviorArity(module));
            if (!def.present() || !against.present() || !written.present()
                    || !arities.present()) {
                return Answer.absent();
            }
            Set<ValueName.Behavior> named = new LinkedHashSet<>();
            namesIn(def.value(), named);
            for (ReachName.Declaration each : written.value()) {
                Hir.FnDef into = against.value().table().reached(each);
                if (into != null) {
                    namesIn(into, named);
                }
            }
            Map<ValueName.Behavior, Integer> out = new LinkedHashMap<>();
            for (ValueName.Behavior each : named) {
                Integer takes = arities.value().get(each);
                if (takes != null) {
                    out.put(each, takes);
                }
            }
            return Answer.of(Ordered.map(out));
        }
    }

    /**
     * What each recursion one body calls is typed as, by the name it is held under.
     *
     * <p>{@link RecursiveCallSigs} is the module's index of every recursion in it, and a body wants
     * the entries for the ones its own expansion left standing. Read whole, a recursive helper
     * declared anywhere in the module checks every behavior of it again.
     */
    public record RecursiveCallSigsForBody(String module, String behavior)
            implements Key<Map<String, Type>> {

        @Override
        public Answer<Map<String, Type>> compute(Db db) {
            Answer<Map<String, Type>> sigs =
                    db.ask(new RecursiveCallSigs(module, InliningPolicy.FULL));
            Answer<Set<ReachName.Declaration>> reached =
                    db.ask(new StandingRecursionsOfBody(module, behavior, InliningPolicy.FULL));
            if (!sigs.present() || !reached.present()) {
                return Answer.absent();
            }
            Map<String, Type> out = new LinkedHashMap<>();
            for (String each : heldAt(reached.value())) {
                Type sig = sigs.value().get(each);
                if (sig != null) {
                    out.put(each, sig);
                }
            }
            return Answer.of(Ordered.map(out));
        }
    }

    /**
     * What the recursions one body calls construct, by the name each is held under.
     *
     * <p>A recursion is not inlined, so what it constructs is attributed to the behavior that calls
     * it (spec §blocks) — which is this body, for the ones this body reaches. {@link
     * RecursiveHelperConstructs} is the module's index of all of them.
     */
    public record RecursiveHelperConstructsForBody(String module, String behavior)
            implements Key<Map<String, DataChecker.Constructs>> {

        @Override
        public Answer<Map<String, DataChecker.Constructs>> compute(Db db) {
            Answer<Map<String, DataChecker.Constructs>> constructs =
                    db.ask(new RecursiveHelperConstructs(module));
            Answer<Set<ReachName.Declaration>> reached =
                    db.ask(new StandingRecursionsOfBody(module, behavior, InliningPolicy.FULL));
            // What the expansion of this body left standing as well, which is a value the tree calls
            // the method of: a value is on no cycle, so what the graph says stands is not it.
            Answer<Expansion<LoweredDefinition>> lowered =
                    db.ask(new LoweredBody(module, new DefinitionName(behavior)));
            if (!constructs.present() || !reached.present() || !lowered.present()) {
                return Answer.absent();
            }
            Set<ReachName.Declaration> standing = new LinkedHashSet<>(reached.value());
            standing.addAll(lowered.value().standing());
            Set<String> held = heldAt(standing);
            // A value another module declares is named where the body reads it and is not among what
            // an expansion left standing, since nothing of it is expanded or called from here.
            for (ValueName.Helper named : HelperNames.helpersReached(
                    lowered.value().value().definition().writtenBody())) {
                held.add(HelperNames.qualified(named.module(), named.name()));
            }
            Map<String, DataChecker.Constructs> out = new LinkedHashMap<>();
            for (String each : held) {
                DataChecker.Constructs built = constructs.value().get(each);
                if (built != null) {
                    out.put(each, built);
                }
            }
            return Answer.of(Ordered.map(out));
        }
    }

    /** The addresses {@code reached} is held at, which is what both indexes of recursions are keyed
     *  by. */
    private static Set<String> heldAt(Set<ReachName.Declaration> reached) {
        Set<String> out = new LinkedHashSet<>();
        reached.forEach(each -> out.add(DefinitionName.of(each).text()));
        return out;
    }

    /**
     * What {@code def}'s body names: the behaviors into {@code named}, and the declarations it
     * reaches as the answer. A kernel the language ships writes no body here and names nothing.
     */
    private static Set<ReachName.Declaration> namesIn(Hir.FnDef def,
                                                      Set<ValueName.Behavior> named) {
        Set<ReachName.Declaration> reaches = new LinkedHashSet<>();
        List<Hir.Expr> todo = new ArrayList<>();
        switch (def.body()) {
            case Hir.FnBody.Written written -> todo.add(written.expr());
            case Hir.FnBody.Intrinsic _ -> { }
        }
        while (!todo.isEmpty()) {
            Hir.Expr at = todo.remove(todo.size() - 1);
            if (at == null) {
                continue;
            }
            if (at instanceof Hir.Var.Denoting name) {
                if (name.denotes() instanceof ValueName.Behavior each) {
                    named.add(each);
                }
                ReachName.Declaration reached = name.reachesADeclaration();
                if (reached != null) {
                    reaches.add(reached);
                }
            }
            Hir.forEachChild(at, todo::add);
        }
        return reaches;
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
            // The assembly and not the state built on it. What this settles is helper parameter
            // types across a tree, which says nothing about whether every declaration came out —
            // and a module where one did not is still read for what its other definitions say.
            Answer<CheckSurface> surface = db.ask(new Shapes.CheckSurface(name));
            Answer<DerivedSymbols> scope = Names.derivedSymbols(db, name);
            Answer<Map<ValueName.Behavior, ReqSig>> reqSigs = db.ask(new ReqSigs(name));
            if (!surface.present() || !scope.present() || !reqSigs.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(Lower.settle(surface.value(), scope.value(),
                        Shapes.publishedDeclarations(db), Shapes.declarationKinds(db),
                        reqSigs.value()));
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
            // What this module declared. A recursion it emits without having declared one is not
            // here: it is reached under the name of the module that wrote it, which is a name this
            // table already answers with that declaration, and which of them this module emits is
            // settled after its trees are expanded rather than being carried here.
            helpers.putAll(HelperInliner.helpersOf(settled.value()));
            return Answer.of(helpers);
        }
    }

    /**
     * What the modules this one imports publish to it, each closed where it was written and named by
     * the module that declares it.
     *
     * <p>A definition another module publishes is held here like one of this module's own: a value
     * is one declaration that every reference to it reaches (ADR-0072), a helper is expanded at its
     * call sites (spec §blocks). What arrives is closed over names — the helpers in the body are
     * expanded and every name of the declaring module that remains is written under that module —
     * so a reader that happens to spell one the same way reaches its own definition and not this one
     * (ADR-0067).
     *
     * <p>What a published body cannot expand is a recursive helper, which is a method rather than an
     * expression, and what it does not expand is a value, which is one definition however many bodies
     * name it. Those come too, under the name of the module that declares them, and so does every
     * one of them they reach in turn — a mutually-recursive group arrives whole, and one the reader
     * never imported arrives because the body it was published inside names it. A recursive helper
     * is carried so that the analyses can read the published definition, and the reader emits it as
     * a method of its own only where its own executable tree reaches it (see {@link
     * Shapes.Prepared}). A published value is not executed here: it runs in the module that
     * declares it, together with any recursive helper it calls, and the reader calls the entry that
     * module publishes for it. Its body comes for the analyses, which read a value by its
     * template.
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
            // And what a clause a spread takes in left standing, which this module runs and so
            // emits. No import line names it — the clause's module may keep it to itself — and it
            // is handed over all the same, the way a helper a published body reaches is.
            Answer<Map<TypeSymbol.AtModule, List<SettledInvariant>>> takenIn =
                    db.ask(new Shapes.ClausesTakenIn(name));
            if (!takenIn.present()) {
                return Answer.absent();
            }
            Map<String, Set<String>> standingIn = new LinkedHashMap<>();
            for (List<SettledInvariant> clauses : takenIn.value().values()) {
                for (SettledInvariant clause : clauses) {
                    for (ReachName.Declaration standing : clause.callsLeftStanding()) {
                        if (standing.denotes() instanceof ValueName.Helper helper) {
                            standingIn.computeIfAbsent(helper.module(),
                                    k -> new LinkedHashSet<>()).add(helper.name());
                        }
                    }
                }
            }
            Set<String> modules = new LinkedHashSet<>(byModule.keySet());
            modules.addAll(standingIn.keySet());
            Map<String, Hir.FnDef> out = new LinkedHashMap<>();
            for (String module : modules) {
                Answer<Hir.Module> from = db.ask(new Settled(module));
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
                        db.ask(new Expanding(module, InliningPolicy.FULL));
                if (!from.present() || !against.present()) {
                    continue;
                }
                List<Hir.FnDef> roots = new ArrayList<>(
                        bodiesOf(from.value(), byModule.getOrDefault(module, List.of())));
                roots.addAll(standingBodies(from.value(),
                        standingIn.getOrDefault(module, Set.of()), roots));
                // Two imports reaching one definition reach one definition: the name it is keyed by
                // is the module that declares it and its own name, so the second arrival is the same
                // entry rather than a second copy of the method.
                carriedClosure(from.value(), roots, against.value()).forEach(out::putIfAbsent);
            }
            return Answer.of(out);
        }
    }

    /**
     * The values and helpers {@code from} publishes among {@code wanted}, each closed over its own
     * module.
     *
     * <p>Closing them there is what keeps a published definition meaning what it meant where it was
     * written. A body still naming its module's own definitions by a bare name would be read against
     * the reader's, and a reader that spells one the same way would silently change it. Expanding
     * the helpers first leaves a body that names nothing of the declaring module bare — except a
     * recursive helper, which is a method rather than an expression, and a value, which is one
     * definition and not a body to copy. Both are left standing under their declaring module's
     * qualified name (see {@link HelperInliner#closeAcross}). A value is called through the entry
     * of the module that declares it and a recursive helper is emitted by the reader only where its
     * own executable tree reaches it.
     *
     * <p>The value and the helper are told apart by the one predicate that decides it anywhere — a
     * written parameter list — and not by a second record of the same line. What each becomes in the
     * reader follows from the same shape: a definition with no parameters is named where it is used
     * and emitted once, one with parameters is expanded where it is called.
     */
    private static Map<String, Hir.FnDef> publishedDefinitions(Hir.Module from,
                                                               Collection<Hir.FnDef> roots,
                                                               HelperInliner inliner,
                                                               Map<String, SortedSet<CopyTarget>> absorbed) {
        Map<String, Hir.FnDef> out = new LinkedHashMap<>();
        for (Hir.FnDef fn : roots) {
            Expansion<Hir.FnDef> closed = inliner.closedAcross(fn, from.name());
            out.put(closed.value().name(), closed.value());
            absorbed.put(closed.value().name(), new TreeSet<>(closed.copied()));
        }
        return out;
    }

    /**
     * The definitions {@code from} publishes among {@code wanted}, together with every recursive
     * helper of {@code from} they reach.
     *
     * <p>Closing a body leaves every name of the declaring module in it qualified, and the ones that
     * stay are a recursive helper's, which is a method and stays a call, and a value's, which stays a
     * reference. Each has to land on something, so it travels with the body that names it — and,
     * since one may name another, so does everything it reaches in turn. A mutually-recursive group
     * therefore arrives whole: each member is reached from the others, so following the names
     * collects all of them.
     */
    public static Map<String, Hir.FnDef> publishedClosure(Hir.Module from,
                                                          Collection<PublishedHelper> allowed,
                                                          Expanding.Of against) {
        return carriedClosure(from, bodiesOf(from, allowed), against);
    }

    /**
     * What travels with {@code roots}, which are definitions of {@code from} it hands over: each
     * closed over its own module, and every recursive helper of {@code from} they reach.
     *
     * <p>The one computation of what a reader is given. The reader asks it for the definitions it
     * holds leave to read ({@link #publishedClosure}); the module that publishes asks it for the
     * ones it exposes, to hold what it ships to the question of whether another module can run it.
     * Two computations of one set would agree only until the closing changed.
     */
    public static Map<String, Hir.FnDef> carriedClosure(Hir.Module from,
                                                        Collection<Hir.FnDef> roots,
                                                        Expanding.Of against) {
        return carrying(from, roots, against).definitions();
    }

    /**
     * What travels with {@code roots}, and what closing each of them copied of other modules'
     * declarations.
     *
     * @param definitions what {@link #carriedClosure} answers
     * @param absorbed    for each definition this closed, by the name it is carried under, every
     *                    declaration of another module the closing expanded into it. A reader that
     *                    copies the definition copies those along with it: the closed body holds
     *                    what they said, and nothing in it names them as a declaration any more
     */
    public record Carried(Map<String, Hir.FnDef> definitions,
                          Map<String, SortedSet<CopyTarget>> absorbed) {
        public Carried {
            definitions = Collections.unmodifiableMap(new LinkedHashMap<>(definitions));
            Map<String, SortedSet<CopyTarget>> each = new LinkedHashMap<>();
            absorbed.forEach((name, copied) ->
                    each.put(name, Collections.unmodifiableSortedSet(new TreeSet<>(copied))));
            absorbed = Collections.unmodifiableMap(each);
        }
    }

    /** {@link #carriedClosure}, with what closing each definition copied. */
    public static Carried carrying(Hir.Module from, Collection<Hir.FnDef> roots,
                                   Expanding.Of against) {
        HelperInliner inliner = HelperInliner.over(against.table(), against.graph());
        Map<String, SortedSet<CopyTarget>> absorbed = new LinkedHashMap<>();
        Map<String, Hir.FnDef> out = publishedDefinitions(from, roots, inliner, absorbed);
        if (out.isEmpty()) {
            return new Carried(out, absorbed);
        }
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
                Hir.FnDef def = against.table().reached(ownHelper
                        ? new ReachName.Own(reached) : new ReachName.OfModule(reached));
                if (def == null) {
                    continue;   // a prelude helper, which every module emits for itself
                }
                if (ownHelper) {
                    Expansion<Hir.FnDef> closed = inliner.closedAcross(def, from.name());
                    out.put(qualified, closed.value());
                    absorbed.put(qualified, new TreeSet<>(closed.copied()));
                } else {
                    out.put(qualified, def);
                }
                work.add(qualified);
            }
        }
        return new Carried(out, absorbed);
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
     * The definitions of {@code from} named {@code standing}, which a clause of {@code from} left a
     * call to, other than those among {@code already}.
     *
     * <p>A call left standing is to a definition the module that settled the clause has, so one it
     * has not got is two of this compiler's answers disagreeing, as a leave to nothing is.
     */
    private static List<Hir.FnDef> standingBodies(Hir.Module from, Set<String> standing,
                                                  List<Hir.FnDef> already) {
        Map<String, Hir.FnDef> helpers = HelperInliner.helpersOf(from);
        Set<String> taken = new HashSet<>();
        for (Hir.FnDef fn : already) {
            taken.add(fn.name());
        }
        List<Hir.FnDef> out = new ArrayList<>();
        for (String each : standing) {
            Hir.FnDef fn = helpers.get(each);
            if (fn == null) {
                throw new IllegalStateException("a clause of `" + from.name()
                        + "` left a call to `" + each + "` standing, which it does not define");
            }
            if (taken.add(each)) {
                out.add(fn);
            }
        }
        return out;
    }

    /**
     * A leave to read a definition, and a module that has no such definition to hand over.
     *
     * <p>A reading said that module publishes the name, and a reading is what every reader of that
     * module is answered from. So a settled module without the body is two of this compiler's
     * answers to one question standing at once, and a reader that went on from it would publish
     * nothing — which is what a reader with nothing to publish does.
     */
    static final class ALeaveAndAModuleDisagree extends IllegalStateException {

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

        /** The helpers a module offers an expansion, read.
         *
         *  @param table which declaration each name reaches
         *  @param graph what each of them calls, and which of them recurse */
        public record Of(HelperTable table, HelperGraph graph) {}

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Expanding.Of> compute(Db db) {
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
            HelperTable table = HelperTable.of(settled.value(), imported.value(), policy,
                    db.ask(new Front.Library()).value());
            return Answer.of(new Expanding.Of(table, HelperGraph.of(table)));
        }
    }

    /**
     * Whether what {@code name} hands over to run in another module can be run there.
     *
     * <p>A published helper is expanded into its reader, so the classes the reader generates name
     * whatever the closed body builds. Only the types a module exposes are public, so a body that
     * builds one the module keeps to itself is a class the reader cannot link against. This asks
     * the set the reader is given ({@link #carriedClosure}), from the roots the module publishes,
     * and holds each body in it to that.
     *
     * <p>A value is not among what is asked: it runs where it is declared, and its reader calls an
     * entry there. It is one definition of the closure only because a helper may be closed over it.
     */
    public record PublishedBodiesRunElsewhere(String name) implements Key<Boolean> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Boolean> compute(Db db) {
            Answer<Hir.Module> settled = db.ask(new Settled(name));
            Answer<Expanding.Of> against = db.ask(new Expanding(name, InliningPolicy.FULL));
            if (!settled.present() || !against.present()) {
                return Answer.absent();
            }
            Hir.Module from = settled.value();
            // Every declaration of the module is a class of its own, whichever form it was written
            // in, and only the ones it publishes are public.
            Set<String> publishing = from.published();
            Set<String> kept = new LinkedHashSet<>();
            for (Hir.Def def : from.defs()) {
                if (!publishing.contains(def.declares().name())) {
                    kept.add(def.declares().name());
                }
            }
            // A module that keeps no class to itself has nothing a body could name that its reader
            // cannot reach, and typing every helper body to find that out is the cost of asking.
            if (kept.isEmpty()) {
                return Answer.of(Boolean.TRUE);
            }
            List<Hir.FnDef> roots = new ArrayList<>();
            for (Hir.FnDef fn : HelperInliner.helpersOf(from).values()) {
                if (fn.body() instanceof Hir.FnBody.Written && !fn.params().isEmpty()
                        && publishing.contains(fn.name())) {
                    roots.add(fn);
                }
            }
            if (roots.isEmpty()) {
                return Answer.of(Boolean.TRUE);
            }
            Answer<DerivedSymbols> symbols = Names.derivedSymbols(db, name);
            Answer<Map<String, Type>> standing =
                    db.ask(new RecursiveCallSigs(name, InliningPolicy.FULL));
            Answer<ModuleCheck.Of> checked = db.ask(new ModuleCheck(name));
            // A module that did not check has said why; what its helpers name is not asked of it.
            if (!symbols.present() || !standing.present() || !checked.present()
                    || !checked.value().sound()) {
                return Answer.absent();
            }
            // A closed body names this module's own recursive helpers qualified, which is how a
            // reader reaches them, so the calls left standing are typed under that spelling too.
            Map<String, Type> standingCalls = new LinkedHashMap<>(standing.value());
            standing.value().forEach((helper, type) ->
                    standingCalls.putIfAbsent(HelperNames.qualified(name, helper), type));
            Set<String> published = new HashSet<>();
            for (Hir.FnDef root : roots) {
                published.add(HelperNames.qualified(name, root.name()));
            }
            PublishedDeclarations declarations = Shapes.publishedDeclarations(db);
            DeclarationKinds kinds = Shapes.declarationKinds(db);
            List<Report> reports = new ArrayList<>();
            for (Hir.FnDef carried : carriedClosure(from, roots, against.value()).values()) {
                if (carried.params().isEmpty()) {
                    continue;
                }
                // What this module emits as a method of its own is what its reader emits too, and
                // the check has already settled it: it is read as that and not typed a second time.
                String prefix = name + ".";
                EmittedDefinition emitted = carried.name().startsWith(prefix)
                        ? checked.value().emittedDefinitions()
                        .get(carried.name().substring(prefix.length())) : null;
                Set<TypeSymbol.AtModule> named = emitted != null
                        ? CarriedBodyDependencies.of(emitted, symbols.value(), declarations, kinds)
                        : CarriedBodyDependencies.of(carried, symbols.value(), declarations, kinds,
                        standingCalls);
                for (TypeSymbol.AtModule built : named) {
                    if (built.module().equals(name) && kept.contains(built.name())) {
                        String helper = carried.written().canonical();
                        reports.add(Report.raised(Diagnostic.at(carried.pos())
                                .say(published.contains(carried.name())
                                        ? new ModuleMessage.APublishedHelperBuildsWhatIsKept(
                                                helper, built.name())
                                        : new ModuleMessage.ACarriedHelperBuildsWhatIsKept(
                                                helper, built.name()))
                                .build()));
                    }
                }
            }
            return reports.isEmpty() ? Answer.of(Boolean.TRUE) : Answer.absent(reports);
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
     * The definitions this compilation mints for a module, by the name each is emitted under: the
     * operand of each row and the entry of each value the module publishes.
     *
     * <p>What they have in common is mechanism. No source declares them, they are made once for the
     * module, they go through the passes a definition goes through, and each is emitted as a method.
     * What each is for is its role's to say ({@link Hir.FnDef#role}), and a rule that differs
     * between them asks that and not which family answered.
     *
     * <p>Their own family. None is a declaration a name resolves to — which is why it is not among
     * what the module has as fns of its own and is not in the table a call expands against. Such a
     * definition rode there once, to be carried through the passes a fn is carried through, and
     * every rule keyed on what the module holds had a synthetic method among its subjects.
     *
     * <p>Read from the one walk that built them, which built the correspondence beside them
     * ({@link RowMethods}) — a second reading would be a second numbering, and a row would run the
     * operand beside the one it wrote.
     */
    public record MintedDefs(String name) implements Key<Map<String, Hir.FnDef>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, Hir.FnDef>> compute(Db db) {
            Answer<CheckSurface> surface = db.ask(new Shapes.CheckSurface(name));
            if (!surface.present()) {
                return Answer.absent();
            }
            Map<String, Hir.FnDef> out = new LinkedHashMap<>();
            for (Hir.FnDef def : surface.value().mintedDefs()) {
                out.put(def.name(), def);
            }
            return Answer.of(Ordered.map(out));
        }
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
            // The assembly decided these, so this asks the assembly. Asked of the state built on it,
            // a module one of whose declarations did not come out would have no row methods rather
            // than the ones its rows were given, and every reading below would stop there.
            Answer<CheckSurface> surface = db.ask(new Shapes.CheckSurface(name));
            return surface.present()
                    ? Answer.of(new LinkedHashSet<>(surface.value().operandMethods().values()))
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
            // What this module wrote.
            for (Hir.FnDef candidate : settled.value().fns()) {
                if (candidate.name().equals(fn)) {
                    return Answer.of(candidate);
                }
            }
            // A definition this compilation minted, which is no declaration and is in no table.
            Answer<Map<String, Hir.FnDef>> minted = db.ask(new MintedDefs(module));
            if (minted.present() && minted.value().containsKey(fn)) {
                return Answer.of(minted.value().get(fn));
            }
            // A declaration this module reaches and has not taken on. Its body is the declaring
            // module's and was settled there; what changes here is the name it answers to, which is
            // the name this module reaches it by and the name a method is emitted under. Read from
            // the table rather than from a component, so asking for a body does not depend on the
            // module having already been told it needs one.
            Answer<Expanding.Of> against = db.ask(new Expanding(module, InliningPolicy.FULL));
            if (!against.present()) {
                return Answer.absent();
            }
            // Asked at the address this module holds it under, which is what this query is keyed
            // by. What comes back is the entry, so the reference it is reached by is read off that
            // rather than worked out of the address — a library operation is held under the alias
            // it is published as and declared in a module the alias says nothing about.
            HelperEntry held = against.value().table().at(new DefinitionName(fn));
            return held == null ? Answer.absent()
                    : Answer.of(held.definition().reachedAs(held.reachedAs()));
        }
    }

    /**
     * What the definition {@code module} holds at {@code fn} runs as.
     *
     * <p>One answer for every reader that lowers the definition or asks why a call to it was left
     * standing, whatever representation it reads the definition in: what a definition is does not
     * depend on which of the module's expansions is looking at it.
     */
    public record LoweringRoleOf(String module, String fn) implements Key<LoweringRole> {

        @Override
        public Answer<LoweringRole> compute(Db db) {
            Answer<Hir.FnDef> def = db.ask(new SettledFn(module, fn));
            if (!def.present()) {
                return Answer.absent();
            }
            return Answer.of(LoweringRole.of(def.value(), module,
                    db.ask(new Spec(module, fn)).present()));
        }
    }

    /**
     * One body as the backend emits it: its helper calls expanded and its comprehensions desugared.
     *
     * <p>What it reads is the fn itself and the helpers around it, so neither editing another body
     * in the same module nor declaring a behavior beside it expands this one again.
     */
    public record LoweredBody(String module, DefinitionName fn)
            implements Key<Expansion<LoweredDefinition>> {

        @Override
        public Answer<Expansion<LoweredDefinition>> compute(Db db) {
            Answer<Hir.FnDef> def = db.ask(new SettledFn(module, fn.text()));
            Answer<LoweringRole> role = db.ask(new LoweringRoleOf(module, fn.text()));
            Answer<Expanding.Of> against = db.ask(new Expanding(module, InliningPolicy.FULL));
            Answer<Map<ValueName.Behavior, Integer>> behaviors =
                    db.ask(new BehaviorAritiesForBody(module, fn.text(), InliningPolicy.FULL));
            Answer<DerivedSymbols> scope = Names.derivedSymbols(db, module);
            if (!def.present() || !role.present() || !against.present() || !behaviors.present()
                    || !scope.present()) {
                return Answer.absent();
            }
            // Whether this body is a recursion, asked of the graph rather than of the set the module
            // took on. The two agree for every fn that has a body here, and the graph does not have
            // to be told what the module reaches — which is what makes what the module reaches
            // askable in terms of this.
            // Which reference this module reaches what it holds here by, off the entry that was
            // filed at this address. There is no working one out of the address: an operation the
            // library publishes under an alias is held under that alias and declared elsewhere.
            HelperEntry held = against.value().table().at(fn);
            boolean recursive = held != null
                    && against.value().graph().recurses(held.reachedAs());
            try {
                HelperInliner inliner = HelperInliner.over(against.value().table(),
                        against.value().graph())
                        .callingValuesAsMethodsWhereEmitted(scope.value());
                // A value runs as a method that takes the values its root region demands; every
                // other definition runs as the body it was written with.
                return Answer.of(switch (role.value()) {
                    case LoweringRole.ValueHome _, LoweringRole.ValueDeclaredElsewhere _ ->
                            Lower.valueMethod(def.value(),
                                    inliner.namingBehaviors(behaviors.value()));
                    case LoweringRole.Behavior _, LoweringRole.Helper _, LoweringRole.RowValue _,
                         LoweringRole.PublishedValueEntry _ ->
                            Lower.asWritten(Lower.body(def.value(),
                                    inliner.namingBehaviors(behaviors.value()),
                                    recursive, dependencyParams(db, module, fn.text())));
                });
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
    public record BodyForInvariantDischarge(String module, String fn)
            implements Key<Expansion<Hir.FnDef>> {

        @Override
        public Answer<Expansion<Hir.FnDef>> compute(Db db) {
            Answer<Hir.FnDef> def = db.ask(new SettledFn(module, fn));
            Answer<LoweringRole> role = db.ask(new LoweringRoleOf(module, fn));
            Answer<Expanding.Of> against = db.ask(new Expanding(module, InliningPolicy.DISCHARGE));
            Answer<Map<ValueName.Behavior, Integer>> behaviors =
                    db.ask(new BehaviorAritiesForBody(module, fn, InliningPolicy.DISCHARGE));
            Answer<DerivedSymbols> scope = Names.derivedSymbols(db, module);
            if (!def.present() || !role.present() || !against.present() || !behaviors.present()
                    || !scope.present()) {
                return Answer.absent();
            }
            // Whether this body is a recursion, asked of the graph of the representation it is being
            // read in. A recursion is a cycle among the declarations in reach, and which
            // declarations those are is what the policy decides.
            HelperInliner inliner = HelperInliner.over(against.value().table(),
                    against.value().graph()).buildingValuesAsTemplatesWhereAnalysed(scope.value());
            HelperEntry held = against.value().table().at(new DefinitionName(fn));
            boolean recursive = held != null
                    && against.value().graph().recurses(held.reachedAs());
            try {
                // A value the analysis reads by its template; every other definition by the body
                // it was written with.
                return Answer.of(switch (role.value()) {
                    case LoweringRole.ValueHome _, LoweringRole.ValueDeclaredElsewhere _ ->
                            Lower.valueTemplate(def.value(),
                                    inliner.namingBehaviors(behaviors.value()));
                    case LoweringRole.Behavior _, LoweringRole.Helper _, LoweringRole.RowValue _,
                         LoweringRole.PublishedValueEntry _ ->
                            Lower.body(def.value(), inliner.namingBehaviors(behaviors.value()),
                                    recursive, dependencyParams(db, module, fn));
                });
            } catch (CompileException e) {
                return Answer.absent(e);
            }
        }
    }

    /**
     * What the value {@code value} means as the analysis reads it, typed.
     *
     * <p>Asked of the value and not of the body that builds it, so it is typed once for the module
     * however many behaviors build it, and a body that builds it is checked again only when the
     * value's own template changes. Absent where the value's expansion or its check is.
     */
    public record AnalysisTemplate(String module, String value)
            implements Key<InvariantChecker.Template> {

        @Override
        public Answer<InvariantChecker.Template> compute(Db db) {
            Answer<Expansion<Hir.FnDef>> lowered =
                    db.ask(new BodyForInvariantDischarge(module, value));
            Answer<DerivedSymbols> scope = Names.derivedSymbols(db, module);
            Answer<Map<ValueName.Behavior, ReqSig>> reqSigs = db.ask(new ReqSigs(module));
            Answer<Map<String, Type>> sigs = db.ask(new RecursiveCallSigsForBody(module, value));
            Answer<ModuleCheck.Of> valuesChecked = db.ask(new ModuleCheck(module));
            if (!lowered.present() || !scope.present() || !reqSigs.present() || !sigs.present()
                    || !valuesChecked.present()) {
                return Answer.absent();
            }
            Hir.FnDef template = lowered.value().value();
            Type declared = template.declaredReturn() == null
                    ? null : TypeOps.successType(template.declaredReturn());
            try {
                return Answer.of(TemplateChecker.check(
                        template.writtenBody(), declared, lowered.value().provenance(),
                        scope.value(), Shapes.declarationAccess(db),
                        reqSigs.value(), sigs.value(), valuesChecked.value().settledValues()));
            } catch (Unanswerable _) {
                return Answer.absent();
            } catch (CompileException e) {
                return Answer.absent(e);
            }
        }
    }

    /**
     * The template of every value the analysis of {@code body} builds, and of every value those
     * build in turn, each once.
     *
     * <p>Asked one value at a time, so a value more than one body builds is expanded once for the
     * lot and a chain of them costs the links it has. Absent where the expansion of any of them is.
     */
    private static Answer<SequencedMap<ReachName.Declaration, InvariantChecker.Template>>
            templatesBuiltBy(Db db, String module, Hir.Expr body) {
        Answer<Expanding.Of> against = db.ask(new Expanding(module, InliningPolicy.DISCHARGE));
        if (!against.present()) {
            return Answer.absent();
        }
        SequencedMap<ReachName.Declaration, InvariantChecker.Template> out =
                new LinkedHashMap<>();
        ArrayDeque<Hir.Expr> toRead = new ArrayDeque<>();
        toRead.add(body);
        while (!toRead.isEmpty()) {
            for (ReachName.Declaration each : HelperInliner.valuesBuiltIn(toRead.remove())) {
                if (out.containsKey(each)) {
                    continue;
                }
                Hir.FnDef value = against.value().table().reached(each);
                // What is built inside a value is found off its expansion, which is asked for
                // apart from its typing so that finding it does not wait on the check.
                Answer<Expansion<Hir.FnDef>> lowered =
                        db.ask(new BodyForInvariantDischarge(module, value.name()));
                Answer<InvariantChecker.Template> template =
                        db.ask(new AnalysisTemplate(module, value.name()));
                if (!lowered.present() || !template.present()) {
                    return Answer.absent();
                }
                out.put(each, template.value());
                toRead.add(lowered.value().value().writtenBody());
            }
        }
        return Answer.of(out);
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
            Answer<List<ReachName.Declaration>> recursive = db.ask(new RequiredRecursiveDefs(name));
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
            Map<BindingId, ValueName.Helper> carried = new LinkedHashMap<>();
            Map<String, LoweringRole> roles = new LinkedHashMap<>();
            // What this module emits and did not declare: every recursion its own expansions left
            // standing that it has no declaration for, under the name it reaches each by — which is
            // the name a call in the emitted tree already holds, and so the name the method is
            // written under. This is the one place a declaration of another module becomes a method
            // of this one, so it is the one place the renaming happens.
            List<Hir.FnDef> beyond = new ArrayList<>();
            Set<String> declaredHere = new LinkedHashSet<>();
            for (Hir.FnDef fn : settled.value().fns()) {
                declaredHere.add(fn.name());
            }
            // The addresses this module holds its recursions at. The walk below is over the
            // definitions this module carries and asks of each whether it is one of them, which is
            // a question about where they sit rather than about what reaches them.
            Set<String> recursiveAt = new LinkedHashSet<>();
            for (ReachName.Declaration reference : recursive.value()) {
                String required = DefinitionName.of(reference).text();
                recursiveAt.add(required);
                if (!declaredHere.contains(required)) {
                    Answer<Hir.FnDef> def = db.ask(new SettledFn(name, required));
                    if (!def.present()) {
                        return Answer.absent();
                    }
                    beyond.add(def.value());
                }
            }
            // What this compilation minted for the module — a row's operand, the entry of a value —
            // is emitted beside these for the same reason: nothing inlines it, because nothing in
            // this module calls it.
            Answer<Map<String, Hir.FnDef>> minted = db.ask(new MintedDefs(name));
            if (!minted.present()) {
                return Answer.absent();
            }
            beyond.addAll(minted.value().values());
            // What every non-behavior definition this module declares runs as, whether or not it
            // survives to be emitted as a method of its own: a helper fully inlined at its call
            // sites is still checked standalone and still has an answer here, which is what
            // TypeChecker checks every one of these against (Bodies.LoweringRoleOf, kept — never
            // asked again from the shape of what was lowered). Not narrowed to what a module emits:
            // most of these never are, and narrowing here would make this map claim an emission
            // that only the checker, settling which of them a body survives to be, gets to decide.
            for (Hir.FnDef fn : settled.value().fns()) {
                if (behaviors.contains(fn.name())) {
                    // Emitted as the behavior, never as a method of its own, so it has no role
                    // among these — the same reason it is not among toCheck's helpers either.
                    continue;
                }
                Answer<LoweringRole> role = db.ask(new LoweringRoleOf(name, fn.name()));
                if (!role.present()) {
                    return Answer.absent();
                }
                roles.put(fn.name(), role.value());
            }
            for (Hir.FnDef fn : beyond) {
                Answer<LoweringRole> role = db.ask(new LoweringRoleOf(name, fn.name()));
                if (!role.present()) {
                    return Answer.absent();
                }
                roles.put(fn.name(), role.value());
            }
            // What the methods below carry of other modules' declarations: what each expansion
            // copied, and each method that is another module's helper taken on whole.
            Set<CopyTarget> copied = new LinkedHashSet<>();
            // Both, and each stays where it was: what becomes a method is one question and what this
            // module declared is another, and the backend reads the first while every rule about the
            // declaring module reads the second.
            for (List<Hir.FnDef> component : List.of(settled.value().fns(), beyond)) {
                List<Hir.FnDef> fns = new ArrayList<>();
                for (Hir.FnDef fn : component) {
                    // A non-recursive helper is fully inlined at its call sites and never
                    // emitted — it has no body of its own down here, so nothing asks for one. What
                    // survives beside the behaviors is a recursion, which cannot be inlined, and a
                    // method a row's operand is, which is the row's value and has no call site.
                    if (!behaviors.contains(fn.name()) && !recursiveAt.contains(fn.name())
                            && !rowMethods.value().contains(fn.name())
                            && !minted.value().containsKey(fn.name())) {
                        continue;
                    }
                    if (!taken.add(fn.name())) {
                        continue;
                    }
                    Answer<Expansion<LoweredDefinition>> body =
                            db.ask(new LoweredBody(name, fn.address()));
                    if (!body.present()) {
                        // Why is the body's to say, and it said it. A module with a body that does
                        // not expand has none to emit.
                        return Answer.absent();
                    }
                    fns.add(body.value().value().definition());
                    carried.putAll(body.value().value().carried());
                    copied.addAll(body.value().copied());
                    if (roles.get(fn.name()) instanceof LoweringRole.Helper helper) {
                        ValueName.Helper takenOn =
                                CopyTarget.declaredElsewhere(helper.declaration(), name);
                        if (takenOn != null) {
                            copied.add(new CopyTarget.Helper(takenOn));
                        }
                    }
                }
                lowered.add(fns);
            }
            return Answer.of(new Lower.Lowered(settled.value(),
                    Lower.lowered(settled.value(), lowered.get(0), lowered.get(1)), carried, roles,
                    new TreeSet<>(copied)));
        }
    }

    /**
     * The signatures every recursive helper this representation can reach would be called under.
     *
     * <p>What typing a call left standing needs, and nothing about what this module turned out to
     * reach. A call is left standing because its callee recurses — which is a fact about the
     * declarations in reach and is what {@link HelperGraph#recursive()} answers — so the names a body
     * of this module could hold a standing call to are those, whether or not any body holds one. Read
     * off the table rather than found by walking the module: a walk over the places a module writes
     * expressions is a second statement of what a module is made of, and the one that was here
     * answered that a rule reaching a fold needed nothing.
     *
     * <p>Wider than {@link RequiredRecursiveDefs}, and not a replacement for it. That one answers
     * which helpers this module processes and emits, which is what a reader wanting a body needs;
     * this one answers which names can be typed, which is what a reader holding a call needs. Kept
     * apart because a signature for a helper nobody called costs an entry in a map, and a body for
     * one costs a body that does not exist.
     *
     * <p>Keyed by the policy as {@link Expanding} is: the discharge representation leaves the
     * language's own operations standing rather than expanding them into the fold they become, so its
     * table holds none of the library and its recursive set is not the emitted representation's.
     */
    public record RecursiveCallSigs(String name, InliningPolicy policy)
            implements Key<Map<String, Type>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, Type>> compute(Db db) {
            Answer<Expanding.Of> against = db.ask(new Expanding(name, policy));
            Answer<DerivedSymbols> scope = Names.derivedSymbols(db, name);
            if (!against.present() || !scope.present()) {
                return Answer.absent();
            }
            try {
                return Answer.of(TypeChecker.recursiveCallSigs(against.value().table(),
                        against.value().graph().recursive(), scope.value()));
            } catch (CompileException e) {
                // A recursive helper that does not say what it returns costs the signatures of all of
                // them, and there is no module to check without them.
                return Answer.absent(e);
            }
        }
    }

    /**
     * The recursive helpers this module has to process and emit: the ones it declared, and the ones
     * an expansion of its own left a call standing to.
     *
     * <p>Made of what the expansions did, not of a prediction about what they would do. Every tree
     * this module is made of is expanded somewhere, and each of those expansions answers with the
     * recursions it could not remove ({@link Expansion}); this is those answers joined, and the
     * bodies of what they name expanded in turn until nothing new is named.
     *
     * <p>The seeds are the trees, and there are two kinds. A definition's body is expanded by {@link
     * LoweredBody}, which answers with what it left standing. A clause — a data's {@code invariant},
     * a behavior's {@code ensures} — is not a definition and is in no table, so what it reaches is
     * known only to the expansion that read it, and it travels with the clause: a data's clauses out
     * of {@link Shapes.SettledInvariantsGoverning}, which is what a construction of the data checks
     * and which holds the clauses a spread brings in from another module, and a behavior's out of
     * {@link Shapes.Settling}. The
     * walk that was here instead listed the places a module writes expressions and did not list
     * {@code ensures}, so a rule reaching a fold asked for no fold.
     *
     * <p>The closure is the expansion's, not the call graph's. A body reaches a recursion by
     * applying it and by reading a value whose own body applies it, and only the first is a call —
     * so a graph of calls answers about a narrower relation than the one that decides this, and a
     * recursion behind a value is reached by the expansion and by nothing that could see it. Each
     * required recursion is therefore expanded in its turn: it is emitted as a method, so its body
     * is expanded on its own rather than into anything, and what that leaves standing is required
     * too.
     *
     * <p>Being required and having been read are two things. A recursion this module declared is
     * required before the walk begins, and its body still goes through it — a walk that took its
     * result set for its work list would never read one.
     *
     * <p>A helper this module declared is here whether or not anything reaches it: its source is
     * this module's to check and to publish, which is not a question about use. Only what it did not
     * declare is decided by use.
     */
    public record RequiredRecursiveDefs(String name) implements Key<List<ReachName.Declaration>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<List<ReachName.Declaration>> compute(Db db) {
            Answer<Expanding.Of> against = db.ask(new Expanding(name, InliningPolicy.FULL));
            Answer<Hir.Module> settled = db.ask(new Settled(name));
            Answer<InvariantSettled> settling = db.ask(new Shapes.Settling(name));
            Answer<Map<TypeSymbol.AtModule, List<SettledInvariant>>> governing =
                    db.ask(new Shapes.SettledInvariantsGoverning(name));
            Answer<Set<String>> rows = db.ask(new RowMethods(name));
            if (!against.present() || !settled.present() || !settling.present()
                    || !governing.present() || !rows.present()) {
                return Answer.absent();
            }
            HelperGraph graph = against.value().graph();
            HelperTable table = against.value().table();
            Set<ReachName.Declaration> required = new LinkedHashSet<>();
            Deque<ReachName.Declaration> pending = new ArrayDeque<>();
            Set<ReachName.Declaration> processed = new HashSet<>();

            // What this module declared that recurses. Required whether or not anything reaches it:
            // its source is this module's to check and to publish, which is not a question about
            // use. Its body still goes through the walk below — being required is not being read.
            for (HelperEntry declared : against.value().table().declarations().values()) {
                if (graph.recurses(declared.reachedAs())) {
                    require(db, name, graph, required, pending, declared.reachedAs());
                }
            }
            // The trees that survive to run: a behavior's implementation, a row's operand, and the
            // clauses. Nothing else is a root. A helper that does not recurse is expanded into
            // whatever reaches it, so what it leaves standing is answered by that expansion — and a
            // helper nothing reaches leaves nothing standing anywhere, which is why one that folds
            // and is never called asks for no fold.
            //
            // A data's clauses are read off the answer its constructions are checked against, and
            // not off this module's settling: a clause a spread brings in was settled by the module
            // that wrote it, and what it left standing is run here, under the route this module has
            // to it.
            for (List<SettledInvariant> clauses : governing.value().values()) {
                for (SettledInvariant clause : clauses) {
                    for (ReachName.Declaration standing : clause.callsLeftStanding()) {
                        require(db, name, graph, required, pending, standing);
                    }
                }
            }
            for (ReachName.Declaration standing : settling.value().standingInEnsures()) {
                require(db, name, graph, required, pending, standing);
            }
            Set<String> behaviors = Names.behaviorNames(settled.value());
            Set<String> roots = new LinkedHashSet<>(rows.value());
            // A value published for other modules to read is run from outside this one, so what its
            // entry leaves standing is required whether or not anything here names it.
            Answer<Map<String, Hir.FnDef>> minted = db.ask(new MintedDefs(name));
            if (!minted.present()) {
                return Answer.absent();
            }
            roots.addAll(minted.value().keySet());
            for (Hir.FnDef fn : settled.value().fns()) {
                if (behaviors.contains(fn.name())) {
                    roots.add(fn.name());
                }
            }
            for (String root : roots) {
                Answer<Expansion<LoweredDefinition>> body =
                        db.ask(new LoweredBody(name, new DefinitionName(root)));
                if (!body.present()) {
                    // Why is the body's to say, and it said it where it went wrong.
                    return Answer.absent();
                }
                for (ReachName.Declaration standing :body.value().standing()) {
                    require(db, name, graph, required, pending, standing);
                }
            }
            // A required definition is emitted as a method, so its own body is expanded on its own
            // rather than into anything — and what that expansion leaves standing is required too.
            // Followed here, by expanding it, and not by reading edges off the call graph: a body
            // reaches a recursion by applying it and by reading a value whose body applies it, and
            // only the first is a call. Reading the graph instead, a recursion behind a value was
            // reached by the expansion and by nothing that could see it.
            while (!pending.isEmpty()) {
                ReachName.Declaration next = pending.removeFirst();
                if (!processed.add(next)) {
                    continue;
                }
                // Reached one way, held at one address: the reference chose the definition and the
                // address is where its body is asked for. Working the address out of the reference
                // is what this walk does, and it is the direction that holds.
                Answer<Expansion<LoweredDefinition>> body =
                        db.ask(new LoweredBody(name, DefinitionName.of(next)));
                if (!body.present()) {
                    return Answer.absent();
                }
                for (ReachName.Declaration standing :body.value().standing()) {
                    require(db, name, graph, required, pending, standing);
                }
            }
            // In the graph's order, which is declaration order: a check reporting one member of a
            // mutual cycle reports the first, and the order is part of the answer. The walk above
            // finds them in the order it happened to reach them, which is not that.
            Set<ReachName.Declaration> ordered = new LinkedHashSet<>();
            for (ReachName.Declaration recursive : graph.recursive()) {
                if (required.contains(recursive)) {
                    ordered.add(recursive);
                }
            }
            // What is required without being on a cycle — a value emitted as a method — follows, in
            // the table's declaration order too, and not in the order the walk above happened to
            // meet it: the walk's work list is seeded from roots read off an IdentityHashMap
            // (RowFixtures.Emitted#methods), whose iteration order is the roots' identity hashes and
            // is not the same from one compile of the same source to the next.
            for (ReachName.Declaration reachable : table.reachable().keySet()) {
                if (required.contains(reachable)) {
                    ordered.add(reachable);
                }
            }
            return Answer.of(List.copyOf(ordered));
        }

        /** Takes {@code standing} on, and queues its body to be expanded the first time. */
        private static void require(Db db, String module, HelperGraph graph,
                                    Set<ReachName.Declaration> required,
                                    Deque<ReachName.Declaration> pending,
                                    ReachName.Declaration standing) {
            // A value the emitted tree calls the method of is left standing without being on a cycle:
            // what makes a call a call here is that a method is emitted for it, and a value is emitted
            // as one wherever a tree that runs names it from a region that needs nothing else.
            Answer<LoweringRole> role =
                    db.ask(new LoweringRoleOf(module, DefinitionName.of(standing).text()));
            boolean aValue = role.present() && switch (role.value()) {
                case LoweringRole.ValueHome _, LoweringRole.ValueDeclaredElsewhere _ -> true;
                case LoweringRole.Behavior _, LoweringRole.Helper _, LoweringRole.RowValue _,
                     LoweringRole.PublishedValueEntry _ -> false;
            };
            if (!graph.recurses(standing) && !aValue) {
                // An expansion answers with what it left standing, and a call is left standing
                // because its callee recurses. One that does not is this compiler disagreeing with
                // itself about why the call is still a call, and nothing here can be right about it.
                throw new IllegalStateException("`" + standing + "` was left standing by an"
                        + " expansion and does not recurse");
            }
            if (required.add(standing)) {
                pending.addLast(standing);
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
            // The recursions this module processes, which is what has bodies here. A signature is a
            // wider answer — it says what a call could be typed against, including a recursion
            // nothing here reaches — and a body for one of those is a body nobody wrote.
            Answer<List<ReachName.Declaration>> required = db.ask(new RequiredRecursiveDefs(name));
            Answer<DerivedSymbols> scope = Names.derivedSymbols(db, name);
            if (!inliner.present() || !required.present() || !scope.present()) {
                return Answer.absent();
            }
            Map<String, Hir.Expr> bodies = new LinkedHashMap<>();
            for (ReachName.Declaration helper : required.value()) {
                DefinitionName at = DefinitionName.of(helper);
                Answer<Expansion<LoweredDefinition>> body = db.ask(new LoweredBody(name, at));
                if (!body.present()) {
                    return Answer.absent();
                }
                bodies.put(at.text(), body.value().value().definition().writtenBody());
            }
            // A value another module declares is called and not expanded, so what it constructs is
            // not in any body here. What it constructs is read off the definition the module was
            // handed for it, which carries its construction as the declaring module made it.
            Answer<Map<String, Hir.FnDef>> handed = db.ask(new ImportedDefinitions(name));
            if (!handed.present()) {
                return Answer.absent();
            }
            Set<String> elsewhere = new LinkedHashSet<>();
            handed.value().forEach((at, definition) -> {
                if (definition.params().isEmpty() && definition.body() != null
                        && definition.declaredIn() != null && !definition.declaredIn().equals(name)) {
                    bodies.putIfAbsent(at, definition.writtenBody());
                    elsewhere.add(at);
                }
            });
            try {
                // At the addresses the bodies above were put under, which is what this walk is over.
                Set<String> at = new LinkedHashSet<>();
                required.value().forEach(
                        reference -> at.add(DefinitionName.of(reference).text()));
                at.addAll(elsewhere);
                return Answer.of(TypeChecker.recursiveHelperConstructs(at, bodies,
                        inliner.value(), scope.value()));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
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
            if (req instanceof Hir.Var.Denoting named) {
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
     * The behaviors of {@code module} whose bodies are checked, in the order they are declared.
     *
     * <p>One answer to which those are, because asking is what makes {@link CheckedBehavior} an
     * answer this store holds. A reader that worked the set out a second time would ask about a body
     * the check never made — computing it where nothing else has it, and saying whatever that comes
     * to about a module that was never checked this far.
     *
     * <p>Two things decide it. An injection target has no body here — something else supplies it
     * (spec §injected-behavior) — so there is nothing to check and nothing missing when there is
     * none; and a module whose own check stopped built nothing for a body to be checked against, so
     * none of its bodies is checked at all.
     */
    private static List<String> bodiesCheckedIn(Db db, String module) {
        Answer<Hir.Module> settled = db.ask(new Settled(module));
        Answer<ModuleCheck.Of> checked = db.ask(new ModuleCheck(module));
        if (!settled.present() || !checked.present() || checked.value().stopped()) {
            return List.of();
        }
        Set<String> implemented = new LinkedHashSet<>();
        for (Hir.FnDef fn : settled.value().fns()) {
            implemented.add(fn.name());
        }
        List<String> bodies = new ArrayList<>();
        for (Hir.BehaviorDef b : settled.value().behaviors()) {
            if (b instanceof Hir.SpecBehavior spec && implemented.contains(spec.name())) {
                bodies.add(spec.name());
            }
        }
        return List.copyOf(bodies);
    }

    /**
     * What the invariant check found in one module's bodies, said where the rules it is about are
     * written now.
     *
     * <p>A question whose whole answer is its warnings, which is why it is one. What a body means is
     * settled without asking where any rule it is judged against is written ({@link CheckedBody});
     * a caret under one of those rules is where it is written and nowhere else. Held in one answer,
     * an edit that moves a rule and changes nothing it states would either reach every body judged
     * against it or leave the warning quoting the line the rule used to be on — the two cannot both
     * be right, and they are not one question.
     *
     * <p>So this reads the findings and points at them, and depends on where every rule it points at
     * is written. That dependency is what it is for.
     *
     * <p>Asked of the module rather than of each body, the way every other warning-only question
     * here is asked ({@link Compilation#answerWarnings}). What a finding costs to say is a lookup
     * per clause, so which body it came from decides nothing about what this repeats.
     */
    public record InvariantWarnings(String module) implements Key<Boolean> {

        @Override
        public String module() {
            return module;
        }

        @Override
        public Answer<Boolean> compute(Db db) {
            ClauseLocations written = Shapes.clauseLocations(db);
            List<Report> reports = new ArrayList<>();
            for (String behavior : bodiesCheckedIn(db, module)) {
                Answer<CheckedBody> checked = db.ask(new CheckedBehavior(module, behavior));
                if (!checked.present()) {
                    continue;
                }
                for (InvariantFinding found : checked.value().found()) {
                    reports.add(Report.of(found.reportedAs(written)));
                }
            }
            return Answer.of(true, reports);
        }
    }

    /**
     * One behavior's body checked against the behavior it implements, as the Core the backend emits.
     *
     * <p>What it reads is the behavior, its {@code let}, and what the module around it means. Not
     * another body — so a mistake in one behavior is that behavior's, and editing one leaves the rest
     * of the file alone.
     */
    public record CheckedBehavior(String module, String behavior) implements Key<CheckedBody> {

        @Override
        public Answer<CheckedBody> compute(Db db) {
            Answer<Hir.SpecBehavior> spec = db.ask(new Spec(module, behavior));
            Answer<Hir.FnDef> fn = db.ask(new SettledFn(module, behavior));
            Answer<Expansion<LoweredDefinition>> body =
                    db.ask(new LoweredBody(module, new DefinitionName(behavior)));
            Answer<DerivedSymbols> scope = Names.derivedSymbols(db, module);
            // What this body names, and not what its module happens to have callable in it: a
            // signature it never names is no part of what it is checked against, and depending on
            // the module's index would re-check this body whenever a behavior beside it was declared.
            Answer<Map<ValueName.Behavior, ReqSig>> calleeSigs =
                    db.ask(new CalleeSigsForBody(module, behavior));
            Answer<Map<ValueName.Behavior, ReqSig>> reqSigs = db.ask(new ReqSigs(module));
            Answer<HelperInliner> inliner = expanding(db, module, InliningPolicy.FULL);
            // The recursions this body's expansion left standing, and not the module's index of all
            // of them: a recursive helper this body never calls is no part of what it is checked
            // against, and depending on the index would check this body again whenever one was
            // declared anywhere in the module.
            Answer<Map<String, Type>> sigs = db.ask(new RecursiveCallSigsForBody(module, behavior));
            Answer<Map<String, DataChecker.Constructs>> constructs =
                    db.ask(new RecursiveHelperConstructsForBody(module, behavior));
            Answer<Expansion<Hir.FnDef>> discharge =
                    db.ask(new BodyForInvariantDischarge(module, behavior));
            // What each value of the module was settled as: a reference to one that the emitted tree
            // calls the method of is typed by it.
            Answer<ModuleCheck.Of> valuesChecked = db.ask(new ModuleCheck(module));
            // What the behaviors this body reaches state about their answers, and only those: a
            // relation declared by a behavior it does not call is no part of what it is checked
            // against, and depending on one would re-check this body whenever that one was edited.
            Answer<Map<ValueName.Behavior, AssumedContract>> contracts =
                    db.ask(new ContractsForBody(module, behavior));
            if (!spec.present() || !fn.present() || !body.present() || !scope.present()
                    || !calleeSigs.present() || !reqSigs.present() || !inliner.present()
                    || !sigs.present() || !constructs.present() || !valuesChecked.present()) {
                return Answer.absent();
            }
            ReadingPolicy policy = db.ask(new Front.Reading()).value();
            // The invariant-discharge analysis reads its own representation of the body and of the
            // invariants (spec §invariant-discharge). Where the body's is not available the check is
            // skipped rather than run against the emitted tree, whose operations are no longer
            // operations.
            //
            // The clauses are not a second thing to wait for. They are asked for one declaration at a
            // time, wherever it was written, and a declaration whose module could not be expanded
            // answers nothing rather than answering wrongly — so there is no representation here to
            // arrive late, and nothing this body reads turns on a declaration beside the ones it
            // names.
            // What each value the body builds means, asked once for every build of it. Where any of
            // them cannot be expanded the body is not analysed, as one whose own expansion could
            // not be made is not.
            Answer<SequencedMap<ReachName.Declaration, InvariantChecker.Template>> templates =
                    discharge.present()
                            ? templatesBuiltBy(db, module, discharge.value().value().writtenBody())
                            : Answer.absent();
            InvariantChecker.Source dischargeSource =
                    discharge.present() && templates.present()
                    ? new InvariantChecker.Source(discharge.value().value().writtenBody(),
                            discharge.value().provenance(),
                            // A source of this check's own, over the scope everything below the
                            // check reads. Not the one a module's rules are counted under, which is
                            // over the declarations as resolution left them: the two are different
                            // scopes, so a reading made here is not a reading made there and says
                            // so.
                            RuleReadingContext.of(
                                    new RuleReadingSource(scope.value(),
                                            Shapes.expandedClauses(db),
                                            Shapes.declarationAccess(db),
                                            Shapes.declarationNewtypes(db),
                                            Shapes.fieldBindings(db),
                                            Shapes.clauseLocations(db)),
                                    policy, db.readings()),
                            contracts.present() ? contracts.value() : Map.of(),
                            templates.value())
                    : null;
            try {
                SpecChecker.Checked checked =
                        TypeChecker.checkBehavior(spec.value(), fn.value(),
                        body.value().value().definition().writtenBody(),
                        policy,
                        dischargeSource, scope.value(), Shapes.declarationAccess(db),
                        calleeSigs.value(), reqSigs.value(),
                        inliner.value(), sigs.value(), constructs.value(),
                        valuesChecked.value().settledValues());
                Core core = checked.emitted();
                // The last thing done to a body before it is emitted, and the only one that is not a
                // check: a fold that only grows a list is turned into a build (see GrowingFold).
                // What the operations of the language hand their closures, read here because here
                // is where they are still operations. The rewrite below turns a fold that only
                // grows a collection into a walk over a builder and joins two such walks into one,
                // after which nothing in the tree says which container an element came from. It
                // renames no binding, so what is read now is as true of what it answers with.
                return Answer.of(new CheckedBody(
                        GrowingFold.rewrite(core, scope.value().theWalk()),
                        ElementBindings.of(core,
                                body.value().provenance(), Shapes.declarationNewtypes(db)),
                        // Who owns the rule each fork decides by, read off the declarations that
                        // wrote them. Read here because here is where the declarations are: after
                        // expansion a fork carries the argument the call site put in and says
                        // nothing about whether that argument was the rule or what the rule reads.
                        // The behavior's own declaration beside the ones it can reach: its forks
                        // are written in it and nowhere else, and a reading without it leaves every
                        // one of them to whatever answer absence is given.
                        DecisionSources.of(
                                inliner.value().reachable(),
                                // Reached as this module reaches its own behavior, which is bare —
                                // the forks below are looked up by the reference a call carries,
                                // and this declaration is the one nothing calls.
                                Map.of(new ReachName.Own(
                                        new ValueName.Behavior(module, behavior)), fn.value())),
                        body.value().supplied(),
                        // The same body as the analysis reads it, which is a different tree and is
                        // kept as one. What a rule about this behavior's inputs means is read
                        // there: the language's own operations stand as themselves, and the tree
                        // beside it has expanded them into what they do.
                        //
                        // Not rewritten the way the emitted one is. A fold turned into a build is
                        // what a backend writes out, and the analysis reads the operation.
                        checked.analysis(),
                        // What the analysis found, carried and not reported. Saying it here would
                        // mean asking where every clause it is about is written, and this answer
                        // is what a body means rather than what a reader is shown of it — an edit
                        // that moves one of those clauses would then reach every body judged
                        // against it. InvariantWarnings asks, because it is the one pointing.
                        checked.found()));
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
     *
     * <p>The plan is handed in rather than derived. What a claim says it is about is an arm, and
     * the arms it names travel out of here inside the answer the check publishes — so the numbering
     * they are addresses of has to be the one that answer carries, and a numbering decided here
     * would be a second one of the same module for every later reader to hold a claim against.
     */
    private static Map<String, Claims> judged(
            Db db, ModuleBodies of, Hir.Module settled,
            CoverageSites.Plan plan) {
        String module = of.module();
        Map<String, Core> bodies = of.bodies();
        ReadingPolicy policy = db.ask(new Front.Reading()).value();
        Answer<DerivedSymbols> scope = Names.derivedSymbols(db, module);
        Answer<Map<String, InputDomain>> inputs =
                db.ask(new Adequacy.Inputs(module));
        Answer<Map<String, Sig>> sigs = db.ask(new Signatures(module));
        Answer<RuleReadingSource> reading =
                Shapes.ruleReading(db, module);
        if (!scope.present() || !inputs.present() || !sigs.present() || !reading.present()) {
            return Map.of();
        }
        Map<String, Claims> out = new LinkedHashMap<>();
        // One world for every behavior of the module, since every walk below reads in it.
        RuleReadingContext ruleReading =
                RuleReadingContext.of(reading.value(), policy, db.readings());
        for (Hir.BehaviorDef behavior : settled.behaviors()) {
            Core body = bodies.get(behavior.name());
            // What this compilation worked out about the behavior's boundary, read off the one
            // classification. A composition has no body of its own and a behavior whose input was
            // not read has nothing for a claim to be judged against; both come back as no local
            // reading, and neither is decided here — the other reader of this same walk decides it
            // from the same value.
            if (body == null
                    || !(BoundaryForMeasurement.of(sigs.value(), inputs.value(), behavior)
                    instanceof BoundaryForMeasurement.Derived(
                            Sig _, InputForMeasurement.Local(
                                    Hir.SpecBehavior spec, InputDomain read)))) {
                continue;
            }
            Hir.FnDef fn = db.ask(new SettledFn(module, spec.name())).value();
            out.put(spec.name(), Claims.of(
                    UnreachableClaims.of(body, read, scope.value(),
                            ruleReading.source().newtypes(), plan),
                    PathReachability.of(body,
                            fn == null ? null : SpecImplementation.align(spec, fn),
                            plan, read, ruleReading)));
        }
        // In the order the module declares them, which is the order a reader meets the diagnostics
        // these carry. `Map.copyOf` keeps the entries and not the order (see `Ordered`), so a
        // module with two refused claims reported them in whichever order the hashes fell.
        return Ordered.map(out);
    }

    /** The claims a model's own rules contradict, as reports. Read from the judging above rather
     *  than judged again: what refuses a build and what a report prints are one answer. */
    private static List<Report> contradicted(Db db, String module,
                                             Map<String, Claims> claims) {
        Answer<Map<String, InputDomain>> inputs =
                db.ask(new Adequacy.Inputs(module));
        if (!inputs.present()) {
            return List.of();
        }
        List<Report> out = new ArrayList<>();
        claims.forEach((behavior, judged) -> {
            for (Diagnostic refused : ClaimDiagnostics.refusals(
                    judged, inputs.value().get(behavior))) {
                out.add(Report.of(refused));
            }
        });
        return List.copyOf(out);
    }

    /**
     * What each value another module declares was settled as, for the values this module reads.
     *
     * <p>The declaring module's own answer and no other. A value has one place it runs and one check
     * of its body, so a module that reads it is told what that check came to rather than checking a
     * copy. What is asked of the declaring module is what it answers for its values; nothing of how
     * it came to it is read here.
     */
    public record ValuesDeclaredElsewhere(String name) implements Key<Preserved.SettledValues> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Preserved.SettledValues> compute(Db db) {
            Answer<Map<String, Hir.FnDef>> published = db.ask(new ImportedDefinitions(name));
            if (!published.present()) {
                return Answer.absent();
            }
            Set<String> declaring = new LinkedHashSet<>();
            for (Hir.FnDef definition : published.value().values()) {
                if (definition.declaredIn() != null && !definition.declaredIn().equals(name)) {
                    declaring.add(definition.declaredIn());
                }
            }
            Map<ValueName, CompleteSignature> answers = new LinkedHashMap<>();
            for (String declared : declaring) {
                // One answer wherever the module came from: what its own check settled, read off
                // that check where this compilation holds the module's source and off what it
                // published where it does not.
                Front.FromPath.OnThePath onThePath = Front.onThePath(db, declared);
                Preserved.SettledValues settled;
                if (onThePath != null) {
                    settled = onThePath.valueAnswers();
                } else {
                    Answer<ModuleCheck.Of> checked = db.ask(new ModuleCheck(declared));
                    if (!checked.present()) {
                        continue;
                    }
                    settled = checked.value().settledValues();
                }
                // What the module publishes and nothing it settled for its own purposes: the
                // definitions minted for its rows and entries are not values a reader can name.
                Answer<Hir.Module> declarer = db.ask(new Settled(declared));
                if (!declarer.present()) {
                    continue;
                }
                Set<String> offered = ValueEntries.publishedValues(declarer.value());
                settled.signatures().forEach((value, signature) -> {
                    if (value instanceof ValueName.Helper helper && helper.module().equals(declared)
                            && offered.contains(helper.name())) {
                        answers.put(value, signature);
                    }
                });
            }
            return Answer.of(new Preserved.SettledValues(answers));
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
         * What checking one module came to.
         *
         * @param emittedDefinitions the definitions it elaborated, which the backend emits as
         *                           methods
         * @param sound whether it found nothing wrong. An abandoned unit is wrong and says nothing
         *              of its own, so this is not the same as having reported nothing
         * @param stopped whether it stopped rather than finished, leaving the bodies nothing to be
         *                checked against
         */
        public record Of(Map<String, EmittedDefinition> emittedDefinitions, boolean sound,
                         boolean stopped, Preserved.SettledValues settledValues) {}

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<ModuleCheck.Of> compute(Db db) {
            Answer<Lower.Lowered> lowering = db.ask(new Lowering(name));
            Answer<DerivedSymbols> scope = Names.derivedSymbols(db, name);
            // The signatures the check reads are the ones every other reader reads. Asked for here
            // rather than built here: a second construction would answer the boundary's question a
            // second time, and what a phase below the check is handed would be a different answer
            // that happens to agree. Absent where they did not build, which the check is told by
            // being handed nothing — it goes as far as it can without one and abandons the module
            // there, and what went wrong was reported where signatures are made.
            Answer<Map<String, Sig>> signatures = db.ask(new Signatures(name));
            // Where each behavior gets its body, as the module was classified. The tree the check
            // walks cannot say, since one read off the path carries no `let`.
            Answer<BehaviorBodies> bodies = db.ask(new Implementation(name));
            Answer<Set<ValueName.Behavior>> unwritten = db.ask(new ImportedUnwritten(name));
            Answer<Map<ValueName.Behavior, ReqSig>> reqSigs = db.ask(new ReqSigs(name));
            Answer<Map<String, Type>> sigs = db.ask(new RecursiveCallSigs(name, InliningPolicy.FULL));
            Answer<Map<ValueName.Behavior, ReqSig>> calleeSigs = db.ask(new CalleeSigs(name));
            Answer<Map<String, Hir.FnDef>> published = db.ask(new ImportedDefinitions(name));
            Answer<Preserved.SettledValues> elsewhere = db.ask(new ValuesDeclaredElsewhere(name));
            // Which of this module's declarations no value satisfies, asked for rather than worked
            // out here. What the check reads is that fact; the clauses it was read from are not
            // something a body's answer turns on, and depending on them would re-check every body
            // beside a declaration that cannot change it.
            Answer<UninhabitableTypes.WithNoValue> withNoValue =
                    db.ask(new Shapes.TypesWithNoValue(name));
            if (!lowering.present() || !scope.present()
                    || !bodies.present() || !unwritten.present()
                    || !reqSigs.present() || !sigs.present() || !withNoValue.present()
                    || !calleeSigs.present() || !published.present() || !elsewhere.present()) {
                return Answer.absent();
            }
            // What must hold of a value of each declared data, elaborated once. The check reads it
            // rather than asking a clause what it comes to a second time, and what it says about a
            // clause it could not read is that the data is not in here — which is what the reading
            // that decides a type has no value is gated on, and what says this module does not
            // reach codegen.
            Answer<Map<TypeSymbol.AtModule, ValueShape>> shapes =
                    db.ask(new Shapes.ValueShapes(name));
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
                reported = TypeChecker.checkModule(lowering.value().settled(), scope.value(),
                        Shapes.declarationAccess(db),
                        withNoValue.value(), Shapes.declarationLocations(db),
                        db.ask(new Front.Reading()).value(),
                        signatures.present() ? signatures.value() : null,
                        bodies.value(), unwritten.value(), lowering.value().lowered(),
                        lowering.value().carried(), lowering.value().roles(), reqSigs.value(),
                        calleeSigs.value(), sigs.value(), published.value(),
                        settled, shapes.present() ? shapes.value() : Map.of(),
                        elsewhere.value());
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
            Answer<Map<String, CheckedEnsures>> contracts = db.ask(new Contracts(name));
            boolean sound = reported.errors().isEmpty() && reported.abandoned().isEmpty()
                    && contracts.present() && !contracts.hasError()
                    && shapes.present() && !shapes.hasError();
            Map<String, EmittedDefinition> definitions = new LinkedHashMap<>();
            reported.emittedDefinitions().forEach((h, definition) ->
                    definitions.put(h, new EmittedDefinition(
                            GrowingFold.rewrite(definition.body(), scope.value().theWalk()),
                            definition.parameters(), definition.role())));
            return Answer.of(new ModuleCheck.Of(definitions, sound, reported.stopped(),
                    reported.settledValues().snapshot()),
                    reports);
        }
    }

    /**
     * Whether the check of one module found nothing wrong with it.
     *
     * <p>Its own key so that what reads only this — whether to emit a module that imports this one —
     * is recomputed when the answer changes and not when a body does. It carries no reports: they are
     * {@link ModuleCheck}'s, said once where that is asked.
     */
    public record Sound(String name) implements Key<Boolean> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Boolean> compute(Db db) {
            Answer<ModuleCheck.Of> checked = db.ask(new ModuleCheck(name));
            return checked.present() && checked.value().sound()
                    ? Answer.of(Boolean.TRUE) : Answer.absent();
        }
    }

    /**
     * One body as the backend emits it, and what its operations handed their closures.
     *
     * <p>Together because the second cannot be read off the first. What handed a closure an element
     * is gone from the tree the rewrite answers with, so a caller given only the body would have to
     * recognise the shapes that rewrite produces — which is what carrying the pair avoids.
     *
     * <p>And the body an analysis reads, beside the one the backend emits, for the same reason: it
     * cannot be read off the other. The language's own operations are expanded into what they do in
     * the emitted tree, so a reader after what a rule <em>means</em> would be looking at a walk
     * where an operation stood.
     *
     * @param body     the tree the backend emits, with the language's own operations expanded into
     *                 what they do
     * @param analysis the same body as an analysis reads it, with those operations standing as
     *                 themselves, or null where this behavior has no such representation. Two trees
     *                 and not one, and which is which is said by the type rather than by which
     *                 accessor a reader happened to call
     * @param found    what the invariant check found about the constructions in it, said nowhere yet.
     *                 Part of what checking this body came to and not a report of it: a finding is
     *                 about this body and the rules it is judged against, and where those rules are
     *                 written is a question {@link InvariantWarnings} asks when it points at one
     */
    public record CheckedBody(Core body, ElementBindings elements,
                             DecisionSources decisions,
                             SuppliedRules supplied,
                             AnalysisBody analysis,
                             List<InvariantFinding> found) {

        public CheckedBody {
            found = List.copyOf(found);
        }
    }

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
     * <p>What the check found is not in here. A warning belongs to the question that says it, which
     * is the one that has somewhere to point ({@link InvariantWarnings}), and a caller that wants
     * them reads them from there.
     */
    public static final class Elaborated {

        private final ModuleBodies of;
        private final Map<String, EmittedDefinition> emittedDefinitions;
        private final Map<String, Claims> claims;
        private final Map<String, ElementBindings> elements;
        private final DecisionSources decisions;
        private final SuppliedRules supplied;
        private final Map<String, AnalysisBody> analysed;
        private final CoverageSites.Plan plan;
        private final Set<String> emits;

        private Elaborated(ModuleBodies of,
                           Map<String, EmittedDefinition> emittedDefinitions,
                           Map<String, Claims> claims,
                           Map<String, ElementBindings> elements,
                           DecisionSources decisions,
                           SuppliedRules supplied,
                           Map<String, AnalysisBody> analysed,
                           CoverageSites.Plan plan,
                           Set<String> emits) {
            this.of = of;
            this.supplied = supplied;
            this.emittedDefinitions = emittedDefinitions;
            this.claims = claims;
            this.elements = elements;
            this.decisions = decisions;
            this.analysed = Map.copyOf(analysed);
            this.plan = plan;
            this.emits = Ordered.set(new LinkedHashSet<>(emits));
        }

        /**
         * Which of the module's implementations this elaboration entitles a class for.
         *
         * <p>The emission, said once and here. A module emits an implementation for a behavior
         * written with a {@code let} and for one written as a {@code >->} composition, and an
         * elaboration of some of a module is one whose other implementations have no class in it —
         * so what the backend may emit is asked of this rather than worked out beside it. Read off
         * {@link #behaviorBodies()} instead, a composition would be answered for by a map of bodies
         * it is not in, which is how an implementation nobody vouched for came to be emitted.
         *
         * <p>Every name in here is one this module owns. A behavior something outside supplies is
         * not an implementation of this module's and is not entitled to one.
         */
        public Set<String> emits() {
            return emits;
        }

        /**
         * Two of these are one where the check produced the same module for the backend.
         *
         * <p>The question it answers is whether a check that ran again has anything new to emit
         * from. This is what {@link Checked} answers with, and an answer that never equals the one
         * it replaces leaves everything downstream of the check running again — the emitter, what
         * a report says about a claim, and every measure that reads a body.
         *
         * <p>Everything it holds, and not the bodies alone. What a body means to whoever reads it is
         * the Core together with what was decided about it, so two checks that produced one tree and
         * disagreed about which rule a fork decides by produced two modules — and whose module the
         * bodies are is as much part of that as the trees, since a name read off these is a name in
         * that module's words.
         *
         * <p>{@link #plan()} is not among them, and is not left out for being derived. It is an
         * index onto the very {@code Core} objects this answer holds — filed by which objects were
         * put in it — so two answers built from equal trees have plans that address different
         * things and could never compare equal, however alike the modules are. What is stable
         * across two such builds is what the plan is a numbering of, and that is a value: two
         * checks of one module come to one {@link NumberingIdentity}.
         * Reading the plan here would deny every answer its own recomputation and leave everything
         * downstream of the check running on every revision.
         */
        @Override
        public boolean equals(Object other) {
            return other instanceof Elaborated that
                    && of.equals(that.of)
                    && emittedDefinitions.equals(that.emittedDefinitions)
                    && claims.equals(that.claims)
                    && elements.equals(that.elements)
                    && decisions.equals(that.decisions)
                    && supplied.equals(that.supplied)
                    // What it entitles a class for, because that is what is emitted from it. Two
                    // elaborations holding one set of bodies and entitling different classes are
                    // two programs, and a check that came to the second would be taken for the
                    // first.
                    && emits.equals(that.emits);
        }

        @Override
        public int hashCode() {
            return java.util.Objects.hash(of, emittedDefinitions, claims, elements,
                    decisions, supplied, emits);
        }

        /** Whose module these are the bodies of. */
        public String module() {
            return of.module();
        }

        /**
         * Where every arm and every comparison of these bodies is, numbered.
         *
         * <p>An index onto the bodies above, filed by which {@code Core} objects were put in it, so
         * it answers for these trees and for nothing that merely equals them. That is what makes it
         * the check's to hold rather than anybody's to make: it is worth what the graph it points
         * into is worth, and the graph is here.
         *
         * <p>The one the walk that decided the numbering produced, handed over rather than worked
         * out again. There is one plan of a module because there is one check of it, and every
         * caller is looking at that one — so an arm one reader names and an arm another names are
         * one address and not two that agree.
         */
        public CoverageSites.Plan plan() {
            return plan;
        }

        /**
         * The numbering of this module's bodies, which this check issued and every reading of them
         * is of.
         *
         * <p>What a number a run was recorded at means. Taken off the plan rather than held beside
         * it: two fields could be handed over out of step, and a reader would have two answers
         * about one module's arms with no later check able to tell them apart while both were true.
         *
         * <p>This is the half of a plan that outlives the graph it was made from. Where the plan
         * answers for these objects, a numbering says the same places under the same numbers over
         * the same executable, and two builds of one module come to one — which is what lets a
         * recording taken by one build be read by another.
         */
        public NumberingIdentity numberingIdentity() {
            return plan.identity();
        }

        /** Who owns the rule each fork of this module's bodies decides by. */
        public DecisionSources decisions() {
            return decisions;
        }

        /** Which of each body's bindings hold an element of a container, by the behavior's name. */
        public Map<String, ElementBindings> elementBindings() {
            return elements;
        }

        /** The Core of each behavior body, by the behavior's name. */
        public Map<String, Core> behaviorBodies() {
            return of.bodies();
        }

        /**
         * The body an analysis reads, by the behavior's name.
         *
         * <p>Beside {@link #behaviorBodies} and not instead of it, because they are two trees. The
         * one above is the algorithm a backend writes out, with the language's own operations
         * expanded into what they do; this one is the meanings, with those operations standing as
         * themselves. A rule a body writes about its inputs is read here — read off the other,
         * {@code String.startsWith} is a walk and there is no operation left to recognise.
         *
         * <p>A behavior with no reading is absent from this map, and absent is what a reader is
         * answered with. Taking the emitted tree instead is answering a question about meanings
         * with the tree the question is not about.
         */
        public Map<String, AnalysisBody> analysisBodies() {
            return analysed;
        }

        /** Each definition the module emits as a method of its own: its Core and what it takes. */
        public Map<String, EmittedDefinition> emittedDefinitions() {
            return emittedDefinitions;
        }

        /**
         * What each body declares cannot arrive, judged against the reading of its input.
         *
         * <p>Made here because this is where the bodies are: the refusal of a contradicted claim is
         * a report of this check, and a report of a confirmed or an unproven one is the measure's,
         * and both read this. Made twice they would be two answers to one question, and the one
         * that refuses a build and the one a report prints are the last two that should differ.
         */
        public Map<String, Claims> claims() {
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

    /**
     * The implementations one module owns, and which of them may be run.
     *
     * <p>Two sets and not one, because a reader of this asks two questions. What a module owns
     * decides whether a reference to one of its behaviors is a reference to something this compiler
     * was to make; which of those may be run decides whether it was made. A reference to a behavior
     * its module never implements is supplied from outside and is nobody's here to vouch for, and
     * answered with one set those two are the same absence.
     *
     * @param owned    the behaviors of the module an implementation is emitted for, in the order it
     *                 declares them
     * @param runnable the ones of those whose implementation may be made here
     */
    public record Implementations(Set<String> owned, Set<String> runnable) {

        public Implementations {
            owned = Ordered.set(new LinkedHashSet<>(owned));
            runnable = Ordered.set(new LinkedHashSet<>(runnable));
        }

        /**
         * Whether every implementation this module owns may be run.
         *
         * <p>Asked here rather than by whoever wants it, because what it is for is deciding that an
         * evaluation may read the whole module's own check instead of this answer — and a caller
         * deciding that from anything else is deciding it from a narrower question. A module's own
         * check is one of those: a body here is checked against the signatures of what it calls and
         * never against their bodies, so it comes out whole while an implementation it reaches in
         * another module was never made.
         */
        public boolean everyOneRunnable() {
            return runnable.containsAll(owned);
        }
    }

    /**
     * Which of one module's implementations may be run: their own came out, and so did everything
     * the implementation references.
     *
     * <p><b>Over implementations and not over bodies.</b> A module emits an implementation for a
     * behavior written with a {@code let} and for one written as a {@code >->} composition, and
     * both are a class a row is applied through. A composition has no body of its own, so an answer
     * read off the bodies has nothing to say about one — and a composition whose stage is not here
     * is a class referencing one that was not emitted.
     *
     * <p><b>And over what the implementation references, which is what the backend resolves.</b> A
     * body's call and a composition's stage both reach the declaring module's implementation
     * ({@code CodegenContext.cdBehaviorImpl}), whichever module that is. So the closure is taken
     * over {@link ValueName.Behavior} and crosses module boundaries: a caller here reaching an
     * implementation another module owns and did not make is a caller that may not be made either.
     * Cut at this module, the answer would vouch for a class referencing one nothing emitted.
     *
     * <p>A behavior's own check is not the answer. What one body is checked against is the
     * signatures and the stated relations of what it calls ({@link CalleeSigsForBody}) and never
     * another body, so a behavior calling one whose body was refused checks exactly as it would
     * have. So this is a closure and not a predicate of one declaration.
     *
     * <p>Answered by taking away rather than by building up. An implementation that did not come out
     * is out, and so is anything reaching one that is out; what is left over is what may be run.
     * Written the other way, a cycle of clean bodies proves itself and two behaviors calling each
     * other would be runnable on nothing but each other's word.
     *
     * <p>An implementation whose references could not be read is out too. What it reaches is then
     * unknown rather than empty, and reading it as empty is this answer saying something references
     * nothing on the strength of not having looked. A module this one imports that answers nothing
     * is out for the same reason.
     *
     * <p>The walk across modules terminates because the language refuses a cycle of them
     * ({@code E1501}): a module reached from here cannot reach back, so asking it this question
     * cannot arrive here again.
     *
     * <p>Absent where the module did not settle. Nothing of it may be run then either, but that is a
     * different thing to say, and a reader gating on this must not take "nothing may be run" from an
     * answer that was never made.
     */
    public record RunnableImplementations(String name) implements Key<Implementations> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Implementations> compute(Db db) {
            Answer<Hir.Module> settled = db.ask(new Settled(name));
            Answer<ModuleCheck.Of> module = db.ask(new ModuleCheck(name));
            if (!settled.present() || !module.present()) {
                return Answer.absent();
            }
            Set<String> owned = implementationsOwnedBy(db, name);
            // A module this compile did not build. Its implementations were made when it was built
            // and are in the artifact the path holds, so what may be run of it is what it owns —
            // there is no body here for this compile to have failed to make. Asked before the walk
            // because the walk is about what this compile emits: it reads the check of each body,
            // which a module off the path has none of, and would answer that every published
            // implementation cannot be run.
            if (Front.onThePath(db, name) != null) {
                return Answer.of(new Implementations(owned, owned));
            }
            // A module nothing of which can be emitted has no implementation that may be run,
            // whatever became of each body. Said here rather than left to each reader: what this
            // answers is what may be run, and a reader that had to remember to ask this as well
            // would be one place the two could come apart — which is how a caller came to be
            // runnable against a module that emits no class at all.
            if (!emittable(db, name, settled.value(), module.value())) {
                return Answer.of(new Implementations(owned, Set.of()));
            }
            // Written out, because this package declares a `Composition` of its own and an import
            // would make the bare name mean the other one.
            Map<ValueName.Behavior, souther.compiler.core.Composition> composed =
                    db.ask(new Compositions.Of(name)).value();
            Set<String> runnable = new LinkedHashSet<>();
            Map<String, Set<ValueName.Behavior>> references = new LinkedHashMap<>();
            for (String behavior : owned) {
                Set<ValueName.Behavior> reached =
                        implementationReferences(db, name, behavior, composed);
                if (reached == null) {
                    continue;
                }
                references.put(behavior, reached);
                runnable.add(behavior);
            }
            // Until nothing more falls out. One pass takes away only what reaches an implementation
            // directly, and what reached that one is as unrunnable as it is.
            boolean fell = true;
            while (fell) {
                fell = false;
                for (String behavior : List.copyOf(runnable)) {
                    for (ValueName.Behavior each : references.get(behavior)) {
                        if (available(db, name, each, owned, runnable)) {
                            continue;
                        }
                        runnable.remove(behavior);
                        fell = true;
                        break;
                    }
                }
            }
            return Answer.of(new Implementations(owned, runnable));
        }

        /**
         * Which implementations this module's implementation of {@code behavior} constructs, or
         * null where that cannot be read.
         *
         * <p><b>Not what the behavior reaches.</b> {@link BehaviorsReached} answers which behaviors
         * a body names, and the emitter says of the same call that "neither is a question about what
         * the call reaches": a callee implemented elsewhere is constructed, and one supplied to the
         * class being emitted is read off a field of it. Only the first is a class that has to be
         * there. Taken as reachability, a behavior is unrunnable because an implementation it never
         * links against was not made — and a row of it could have run against a stand-in.
         *
         * <p>So what a body declares it depends on is taken away. Those arrive as fields, supplied
         * by whoever constructs this one, and a row supplies them itself; the dependency's own
         * module owes its implementation to whoever asks for it there and not to this class.
         *
         * <p>A composition is every one of its stages. It applies a stage by constructing it, so a
         * stage is a class that has to be there — which is why a composition's references are read
         * from the stages and not from a body it has not got.
         *
         * <p>A {@code let} body's own check has to have come out as well: a body nothing elaborated
         * has no class here whatever it links against. And where the requirements of the module
         * cannot be read, what a body is supplied is unknown rather than nothing — read as nothing,
         * this would take away an implementation on the strength of not having looked.
         */
        private static Set<ValueName.Behavior> implementationReferences(Db db, String module,
                String behavior,
                Map<ValueName.Behavior, souther.compiler.core.Composition> composed) {
            souther.compiler.core.Composition pipe = composed == null ? null
                    : composed.get(new ValueName.Behavior(module, behavior));
            if (pipe != null) {
                Set<ValueName.Behavior> stages = new LinkedHashSet<>();
                pipe.stages().forEach(stage -> stages.add(stage.behavior()));
                return stages;
            }
            Answer<Set<ValueName.Behavior>> reached =
                    db.ask(new BehaviorsReached(module, behavior));
            Map<String, List<BehaviorRequirement>> supplied =
                    db.ask(new Requirements(module)).value();
            if (!db.ask(new CheckedBehavior(module, behavior)).present() || !reached.present()
                    || supplied == null) {
                return null;
            }
            List<BehaviorRequirement> required = supplied.get(behavior);
            if (required == null) {
                throw new IllegalStateException("`" + module + "." + behavior + "` is declared and"
                        + " has no requirement set");
            }
            Set<ValueName.Behavior> injected = new LinkedHashSet<>();
            for (BehaviorRequirement each : required) {
                injected.add(each.dependency());
            }
            Set<ValueName.Behavior> constructs = new LinkedHashSet<>(reached.value());
            constructs.removeAll(injected);
            return constructs;
        }

        /**
         * Whether the implementation {@code reference} names can be run.
         *
         * <p>Asked of the module that declares it, because that is the module that emits it. Its own
         * answer says both halves: a behavior it does not own is supplied from outside and reaching
         * it takes nothing away, and one it owns and cannot run is a class that was not made.
         *
         * <p>A module that answers nothing is out. Nothing of it is emitted, so a reference into it
         * reaches no class — the same as a reference to one it could not make.
         */
        private static boolean available(Db db, String module, ValueName.Behavior reference,
                                         Set<String> ownedHere, Set<String> runnableHere) {
            if (module.equals(reference.module())) {
                return !ownedHere.contains(reference.name())
                        || runnableHere.contains(reference.name());
            }
            Implementations there =
                    db.ask(new RunnableImplementations(reference.module())).value();
            if (there == null) {
                return false;
            }
            return !there.owned().contains(reference.name())
                    || there.runnable().contains(reference.name());
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
            // In the order they are declared, so what the backend emits does not move with what the
            // check happened to ask for first. A module whose own check stopped has none of them —
            // asking would report not being able to see what has already been reported missing.
            List<String> implemented = bodiesCheckedIn(db, name);
            boolean bodiesCheck = true;
            for (String behavior : implemented) {
                if (!db.ask(new CheckedBehavior(name, behavior)).present()) {
                    bodiesCheck = false;
                }
            }
            if (!bodiesCheck || !emittable(db, name, settled.value(), module.value())) {
                return Answer.absent();
            }
            // Every implementation the module owns, because this is the answer for a module that
            // came out whole: what may be emitted from it is what it wrote. Read from the
            // declarations and not from the closure over them, which is a question about what may
            // be run and is asked of an evaluation rather than of a check.
            Elaborated whole = elaborationOf(db, name, settled.value(), module.value(),
                    implemented, implementationsOwnedBy(db, name));
            return Answer.of(whole, contradicted(db, name, whole.claims()));
        }
    }

    /**
     * The elaboration an evaluation of this module's rows may be run against: the bodies that may
     * be run, and nothing of the ones that may not.
     *
     * <p>Beside {@link Checked} and never instead of it. What ships is one module or none, so a
     * body that did not come out leaves nothing to publish; what a row is run against is a program
     * this compile never writes out, and a module holding one body nothing elaborated has the rest
     * of its bodies all the same. So the conditions here are the ones emitting rests on — no name
     * denoting nothing, no type nobody could name — and the universal one {@link Checked} adds over
     * every body of the module is the one this does without.
     *
     * <p><b>The whole module's answer where every implementation of it may be run.</b> Handed back
     * as {@link Checked} came to it, so such a module is observed against the program it ships
     * rather than against a second elaboration equal to it. Built again here, the two would hold
     * equal plans filed under different objects, and what a run recorded would be numbered against
     * one of them and read against the other.
     *
     * <p>Two conditions and not one, because they are two questions. That the module came out whole
     * is what makes there be a shipped program to be identical to; that every implementation it owns
     * may be run is what makes this answer the same one. A module whose own check came out and whose
     * caller of another module's unmade implementation did not is short of the second and not of the
     * first ({@link Implementations#everyOneRunnable}).
     *
     * <p><b>A run is measured in the elaboration that produced the classes it ran.</b> So this is
     * what every measure of a run reads, and {@link Checked} is what publication reads. A plan is an
     * index onto the bodies of one elaboration — a partial image and a whole one are two coordinate
     * systems, whatever the module is called — so a measure that took its numbering from the whole
     * check would be reading a run against numbers nothing wrote, and would put the structure of a
     * program that did not run beside the observation of the one that did. A behavior whose
     * implementation may not be run has no body here, which is what stops a measure inventing
     * evidence about it.
     *
     * <p>Nothing is reported from here. What a contradicted claim refuses is a build, and a build
     * refuses over the module it would ship; a refusal raised from an artifact nothing ships would
     * be this compile refusing a model for the first time while answering what may be observed
     * about it.
     */
    public record Observable(String name) implements Key<Elaborated> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Elaborated> compute(Db db) {
            Answer<Hir.Module> settled = db.ask(new Settled(name));
            Answer<ModuleCheck.Of> module = db.ask(new ModuleCheck(name));
            if (!settled.present() || !module.present()
                    || !emittable(db, name, settled.value(), module.value())) {
                return Answer.absent();
            }
            Implementations runs = db.ask(new RunnableImplementations(name)).value();
            if (runs == null) {
                return Answer.absent();
            }
            // Asked of the closure and not of this module's own check, which is a narrower question
            // than the one being shortcut: a body here checks against the signatures of what it
            // calls, so this module comes out whole while an implementation it reaches in another
            // module was never made. Shortcut on the check, the classes an evaluation loads would
            // hold a caller of a class nothing emitted.
            Answer<Elaborated> whole = db.ask(new Checked(name));
            if (whole.present() && runs.everyOneRunnable()) {
                return Answer.of(whole.value());
            }
            // In the order the module declares them, which is what the numbering is of. Taken from
            // the declarations and filtered, rather than walked out of the set: a set says which
            // bodies these are and nothing about the order they were written in.
            //
            // The bodies alone, because that is what an elaboration holds. Which implementations
            // may be emitted is the wider set beside it, and a composition is in that one and in no
            // map of bodies.
            List<String> elaborating = new ArrayList<>();
            for (String behavior : bodiesCheckedIn(db, name)) {
                if (runs.runnable().contains(behavior)) {
                    elaborating.add(behavior);
                }
            }
            return Answer.of(elaborationOf(db, name, settled.value(), module.value(),
                    elaborating, runs.runnable()));
        }
    }

    /**
     * Which of a module's behaviors it emits an implementation for, in the order it declares them.
     *
     * <p>One reading and not a union of two. A behavior written with a {@code let} and one written
     * as a {@code >->} composition are both a class a row is applied through, and
     * {@link Implementation} is where that is decided for either — asked of the declarations, so a
     * module on the path answers it from what it published and a module being compiled answers it
     * from its source.
     *
     * <p><b>Not read off what the check reached.</b> {@link #bodiesCheckedIn} answers which bodies
     * there are to check and is empty for a module whose own check stopped, which is a fact about
     * how far this compile got. Taken for ownership it says a module owns nothing, and then a caller
     * in another module is told that what it reaches is supplied from outside — which is the one
     * distinction the two sets here exist to keep apart.
     *
     * <p>Which of these may be run is a further question and is not this one
     * ({@link RunnableImplementations}). What a module owns does not move with what happened to
     * check: a behavior whose implementation could not be made is still one this module was to
     * implement, and that is the whole difference between the two absences a row can meet.
     */
    private static Set<String> implementationsOwnedBy(Db db, String module) {
        BehaviorBodies states = db.ask(new Implementation(module)).value();
        Set<String> owned = new LinkedHashSet<>();
        if (states == null) {
            return owned;
        }
        states.states().forEach((behavior, state) -> {
            if (state.hasBody()) {
                owned.add(behavior);
            }
        });
        return owned;
    }

    /**
     * Whether this module's meanings can be emitted at all, which is less than every body of it
     * having come out.
     *
     * <p>Whether anything about this module's names came out wrong decides whether it can be
     * emitted, and nothing else. It must not decide whether the module is checked: the error type
     * absorbs so that the check can carry on, and stopping on it would mean a mistake in one
     * declaration silencing every other definition in the file.
     *
     * <p>Both of the rest, and both after the check. Sound says nothing about this module's names
     * came out wrong; the tree says it holds no type nobody could name, which can happen with
     * nothing reported here at all — an import of a module that is here and unusable leaves a hole,
     * and what is wrong was reported on that module.
     */
    private static boolean emittable(Db db, String name, Hir.Module settled, ModuleCheck.Of module) {
        return Boolean.TRUE.equals(db.ask(new Names.Sound(name)).value())
                && module.sound()
                && !TypeOps.holdsAnErroneousType(settled);
    }

    /**
     * What the named bodies of one module came to, gathered into the one answer everything below
     * the check reads.
     *
     * <p>{@code emitting} is which bodies this elaboration is of, in the order the module declares
     * them. Every one of them is a body that came out: which bodies an elaboration holds is the
     * caller's to decide and whether each of them has a meaning is not, so one named here without
     * a check behind it is this compiler having asked for an answer about nothing.
     *
     * <p>Every number below is made from exactly these bodies. The plan is what the emitter writes
     * into the bytecode and what a report reads back, so an elaboration of some of a module's
     * bodies is numbered over those and over nothing it is not going to emit.
     *
     * <p>{@code emits} is which of the module's implementations this elaboration entitles a class
     * for, which is wider than {@code elaborating}: a {@code >->} composition is an implementation
     * with no body, so it is in the first and in neither the bodies nor any number made from them.
     */
    private static Elaborated elaborationOf(Db db, String name, Hir.Module settled,
                                            ModuleCheck.Of module, List<String> elaborating,
                                            Set<String> emits) {
        java.util.SequencedMap<String, Core> bodies = new LinkedHashMap<>();
        Map<String, AnalysisBody> analysed = new LinkedHashMap<>();
        Map<String, ElementBindings> elements = new LinkedHashMap<>();
        // One reading for the module. Every behavior's check walks the same declarations, so the
        // entries agree wherever two of them wrote one fork; kept as one map so a reader asking
        // about a fork does not have to know which behavior's check happened to reach it.
        Map<SourceConstructOrigin,
                DecisionSource> decisions = new LinkedHashMap<>();
        Map<BindingOwner,
                SuppliedRules.Handed> supplied = new LinkedHashMap<>();
        for (String behavior : elaborating) {
            Answer<CheckedBody> core = db.ask(new CheckedBehavior(name, behavior));
            if (!core.present()) {
                throw new IllegalStateException("`" + name + "." + behavior + "` is named in an"
                        + " elaboration and its body did not come out");
            }
            bodies.put(behavior, core.value().body());
            elements.put(behavior, core.value().elements());
            // Only where there is one. A behavior with no representation for the analysis to read
            // is absent from here, which is what a reader owed the meanings is answered with — the
            // tree beside it is a different question's answer and is not a fallback.
            if (core.value().analysis() != null) {
                analysed.put(behavior, core.value().analysis());
            }
            decisions.putAll(core.value().decisions().byFork());
            supplied.putAll(core.value().supplied().byExpansion());
        }
        // A value emitted as a method of its own is a body a run passes through, and what it
        // compares and forks on is among the places of this module however many behaviors call it.
        // Held apart from the behaviors: it declares no rows and states no answer, and the places of
        // a behavior are its own and those of the methods it calls.
        SequencedMap<String, Core> methods = new LinkedHashMap<>();
        for (Hir.FnDef fn : settled.fns()) {
            EmittedDefinition definition = module.emittedDefinitions().get(fn.name());
            if (definition != null && definition.role() instanceof LoweringRole.ValueHome) {
                methods.put(fn.name(), definition.body());
                // What a body is read with travels with the body. A behavior's check answers with
                // the rules its calls were handed, and the expansion a value method was lowered
                // from answers with the same; a value emitted for another module to call has no
                // behavior whose check would have carried them.
                Answer<Expansion<LoweredDefinition>> lowered =
                        db.ask(new LoweredBody(name, fn.address()));
                if (!lowered.present()) {
                    throw new IllegalStateException("`" + name + "." + fn.name() + "` is emitted"
                            + " as a method and its body did not come out");
                }
                supplied.putAll(lowered.value().supplied().byExpansion());
            }
        }
        // Who decides at each fork of these bodies is read for them as well, against what the
        // module declares: the table holds its values, so a module with no behavior that names one
        // still has each fork answered for.
        if (!methods.isEmpty()) {
            Answer<Expanding.Of> against = db.ask(new Expanding(name, InliningPolicy.FULL));
            if (!against.present()) {
                throw new IllegalStateException("`" + name + "` has value methods and no table its"
                        + " declarations are read against");
            }
            decisions.putAll(DecisionSources.of(against.value().table().reachable(),
                    Map.of()).byFork());
        }
        // What each body declares cannot arrive, held against what its input's own declarations
        // leave. Judged here rather than beside each body: it reads the signature, which is the
        // module's, and a body's own answer must not move when the one beside it is edited.
        //
        // Only of a module whose meanings came out. A model with a hole in it has been reported on
        // where the hole is, and what a case can arrive at cannot be read through one — asked
        // anyway, the reading meets a shape no position can have and says so about this compiler,
        // which is true and is not what the author of a mistyped model needs.
        DecisionSources read =
                new DecisionSources(decisions);
        SuppliedRules handed = new SuppliedRules(supplied);
        // Whose module these bodies are, said once and here: this is where a module's name and
        // its trees are both in hand for the first and only time, and everything below takes
        // the pair rather than two things to put together again.
        ModuleBodies of =
                new ModuleBodies(name, bodies, methods);
        // Where the places of these bodies are, walked here and once. What it is an answer
        // about is the module this check holds, so this is where there is a module to walk;
        // and the claims below name arms of it, so they are addresses of the plan this answer
        // goes on to carry rather than of one more that agrees with it.
        //
        // Handed to the answer whole. The plan is filed by which Core objects were put in it,
        // and the objects are the ones this answer holds, so it is worth what the answer is
        // worth and stops being worth anything the moment it is separated from it. A reader
        // given only what the plan is a numbering of would have to walk these bodies again to
        // get back what this call already came to.
        //
        // Owed by the answer rather than by what is done with it, so nothing conditions it.
        // The judging below stops where the signatures or the reading of the inputs are not in
        // hand, which is a condition on judging a claim and never was one on the bodies having
        // places: a module whose bodies came out has arms whatever else did not come out, and
        // an answer carrying no plan is one every reader of it would walk the bodies for.
        CoverageSites.Plan plan =
                CoverageSites.of(of, read, handed);
        return new Elaborated(of, module.emittedDefinitions(), judged(db, of, settled, plan), elements,
                read, handed, analysed, plan, emits);
    }

    /**
     * Where each of this module's behaviors has its {@code ensures} checked.
     *
     * <p>A decision the language makes, answered once and read by everything that acts on it: the
     * emitter, which puts the check where this says, and a checked program, which says what a
     * behavior declares of its answer and where that is held to. Each reader making it from the
     * contracts and the injected set would be two answers to one question, and the second of them
     * would be made from a set the emitter goes on adding to — a behavior this module gives a body
     * to but reaches as a dependency joins the injected ones, and a reader arriving afterwards
     * finds a bodied behavior among them.
     *
     * <p>{@link InjectionTargets} is the set as the requirements pass answered it, which is the
     * reading the decision is owed.
     *
     * <p>Every behavior this module declares is in here, which is what makes a miss an answer
     * ({@link EnsuresEnforcement#in}) rather than a table that was not filled.
     */
    public record EnsuresChecks(String name) implements Key<Map<ValueName.Behavior,
            EnsuresEnforcement>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<ValueName.Behavior, EnsuresEnforcement>> compute(Db db) {
            Answer<Lower.Lowered> lowering = db.ask(new Lowering(name));
            Answer<Set<ValueName.Behavior>> injectionTargets = db.ask(new InjectionTargets(name));
            Answer<Map<String, CheckedEnsures>> contracts = db.ask(new Contracts(name));
            if (!lowering.present() || !injectionTargets.present() || !contracts.present()) {
                return Answer.absent();
            }
            Hir.Module lowered = lowering.value().lowered();
            Set<ValueName.Behavior> injected = injectionTargets.value();
            // What runs, which is what a check is made from. Where each rule was written stays with
            // the declaration; a reader given that as well would hold a value an unrelated edit
            // moves.
            Map<String, Contract> executable = CheckedEnsures.executable(contracts.value());
            Map<ValueName.Behavior, EnsuresEnforcement> checks = new LinkedHashMap<>();
            for (Hir.BehaviorDef behavior : lowered.behaviors()) {
                ValueName.Behavior named = new ValueName.Behavior(lowered.name(), behavior.name());
                checks.put(named, EnsuresEnforcement.of(named, executable, injected));
            }
            return Answer.of(Ordered.map(checks));
        }
    }
}
