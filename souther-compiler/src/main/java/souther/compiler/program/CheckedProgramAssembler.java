package souther.compiler.program;

import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.check.AtomSpace;
import souther.compiler.check.BehaviorBodies;
import souther.compiler.check.BehaviorImplementation;
import souther.compiler.check.BehaviorRequirement;
import souther.compiler.check.Boundary;
import souther.compiler.check.BoundaryInput;
import souther.compiler.check.BoundaryOutput;
import souther.compiler.check.CoreBinders;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.Derived;
import souther.compiler.check.EmittedDefinition;
import souther.compiler.check.Lower;
import souther.compiler.check.LoweringRole;
import souther.compiler.check.Requirements;
import souther.compiler.check.Sig;
import souther.compiler.check.SpecImplementation;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.derive.CodecShape;
import souther.compiler.derive.Deriver;
import souther.compiler.abort.AbortSites;
import souther.compiler.abort.Constructible;
import souther.compiler.core.Composition;
import souther.compiler.core.Contract;
import souther.compiler.core.Core;
import souther.compiler.core.EnsuresEnforcement;
import souther.compiler.core.KernelContracts;
import souther.compiler.core.ValueShape;
import souther.compiler.diag.SourcePos;
import souther.compiler.meta.ModulePath;
import souther.compiler.observe.Expectation;
import souther.compiler.observe.FieldTypes;
import souther.compiler.observe.Position;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.RowStatement;
import souther.compiler.observe.StoodIn;
import souther.compiler.observe.ValueTypes;
import souther.compiler.query.Acceptance;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Compositions;
import souther.compiler.query.Db;
import souther.compiler.query.Front;
import souther.compiler.query.Names;
import souther.compiler.query.Output;
import souther.compiler.query.Shapes;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Takes the snapshot: reads what the compiler decided and writes it down as a {@link
 * CheckedProgram}.
 *
 * <p>The one place in this package that knows how this compiler answers its own questions. Which
 * key held a checked body, a signature, a composition's routing is how {@code souther-compiler}
 * computes and invalidates, and it is a thing to keep away from the model the snapshot is: a reader
 * of a checked program that had to name a query would be reading a compiler rather than a program.
 *
 * <p>Nothing read here is carried into what is made. The compilation, its {@link Db}, and every
 * answer object still tied to one are gone by the time this returns; what is left is values. A
 * snapshot holding the session it was taken from would answer differently after the session was
 * edited, which is the one thing a snapshot may not do.
 */
final class CheckedProgramAssembler {

    private CheckedProgramAssembler() {}

    static CheckedProgram of(List<String> sources, ModulePath path) {
        Compilation compilation = Compilation.ofSources(sources, path);
        // The language's verdict, asked where a batch compile asks it. Stopping at the check would
        // make this the one reading that accepts a program with a row that disagrees — and an
        // output built on it would ship an artifact for what another output refuses to build.
        Acceptance.of(compilation);
        Db db = compilation.db();
        List<CheckedData> language = languageDataOf(db);
        List<CheckedData> onThePath = declaredOnThePath(db);
        // What each module was checked to be, read before anything is made of it. Every declaration
        // this compile resolved has to be in hand before a row can be written down, because what a
        // row states may hold a value of a data another module declares — and a comparison that
        // could not read that data would read its parts as whatever they happen to look like.
        List<ModuleReading> read = new ArrayList<>();
        for (String module : compilation.modules()) {
            read.add(readingOf(db, module));
        }
        List<CheckedData> everyDeclaration = new ArrayList<>(language);
        everyDeclaration.addAll(onThePath);
        for (ModuleReading module : read) {
            everyDeclaration.addAll(module.data());
        }
        ValueTypes types =
                ValueTypes.over(FieldTypes.over(DeclaredFields.over(everyDeclaration)));
        // Made before the modules, because a module cannot be made without them: a row of one
        // states what it stood in for a dependency with, and where that dependency's arguments
        // stand is read off the dependency's own boundary — which is a behavior of another module
        // as often as one of this.
        Map<ValueName.Behavior, BehaviorTarget> targets = new LinkedHashMap<>();
        List<ModuleBoundaries> boundaries = new ArrayList<>();
        for (ModuleReading module : read) {
            boundaries.add(fileWhatIsChecked(targets, module, db));
        }
        fileWhatIsOnThePath(targets, db);
        List<CheckedModule> modules = new ArrayList<>();
        for (ModuleBoundaries module : boundaries) {
            modules.add(moduleOf(module, types, targets));
        }
        KernelContracts kernels = KernelContracts.of(libraryOf(db).kernelSignatures());
        AbortSites aborts = AbortSites.of(everyCoreRootOf(modules, everyDeclaration), kernels,
                constructible(everyDeclaration));
        return new CheckedProgram(modules, language, onThePath, targets, kernels, aborts);
    }

    /**
     * Every declared type a construction can build, each with whether an {@code invariant} clause
     * names it.
     *
     * <p>Every one, and not only the ones with an invariant: a list of those would leave a type with
     * none and a type it never reached reading the same. Read off the same declarations
     * {@link #languageDataOf} and {@link #dataOf} already answered, and not re-derived from the
     * checker's own state: a second reading of what a type's invariants are would be a second place
     * that could disagree with {@link ValueShape#invariants} about which types have one.
     */
    private static List<Constructible> constructible(List<CheckedData> everyDeclaration) {
        List<Constructible> found = new ArrayList<>();
        for (CheckedData declared : everyDeclaration) {
            if (declared instanceof CheckedData.WithFields fields) {
                found.add(new Constructible(declared.name(), !fields.invariants().isEmpty()));
            }
        }
        return found;
    }

    /**
     * Every {@code Core} a program's outputs are asked to emit: each behavior's body, where it has
     * one this compile wrote, each helper's, each value's and each value entry's, the condition of
     * every clause a declared data holds its values to, and the condition of every rule a behavior
     * declares of its answer.
     *
     * <p>The one list of them, and a list of every place a checked program hands a {@code Core}
     * out: each of those is code some output runs, so each is a site {@link AbortSites} has to
     * answer for. A place added to the program's surface is added here too, and
     * {@code EveryCoreAProgramHandsOutIsASiteAbortsAtAnswersForTest} fails until it is.
     *
     * <p>A clause is emitted wherever a value of its data is built, and a rule wherever its
     * behavior's answer is held to it, which for a behavior another build answers is every
     * crossing into this program. Every declaration is asked, one on the path among them, since a
     * construction of that data runs its clauses in whatever output builds it. A clause a spread
     * takes in is the one {@code Core} in every data that includes it, and it is classified once:
     * what it can end without a value for does not depend on which data is being built.
     *
     * <p>A body only where this compile wrote one. {@link CheckedImplementation.Composed} has no
     * {@code Core} of its own, and what {@link CheckedImplementation.ImplementedElsewhere} and
     * {@link CheckedImplementation.Injected} can end without a value for is a fact about a build
     * this is not, read the same way a call to either answers {@link AbortSet#NONE} at the site
     * that reaches it.
     */
    private static List<Core> everyCoreRootOf(List<CheckedModule> modules,
                                              List<CheckedData> everyDeclaration) {
        List<Core> roots = new ArrayList<>();
        for (CheckedModule module : modules) {
            for (CheckedBehavior behavior : module.behaviors()) {
                if (behavior.implementation() instanceof CheckedImplementation.Body body) {
                    roots.add(body.body());
                }
                Contract declares = behavior.ensures().contract();
                if (declares != null) {
                    for (Contract.Rule rule : declares.rules()) {
                        roots.add(rule.condition());
                    }
                }
            }
            for (CheckedHelper helper : module.helpers()) {
                roots.add(helper.body());
            }
            for (CheckedValue value : module.values()) {
                roots.add(value.body());
            }
            for (CheckedValueEntry entry : module.valueEntries()) {
                roots.add(entry.body());
            }
        }
        for (CheckedData declared : everyDeclaration) {
            if (declared instanceof CheckedData.WithFields fields) {
                for (ValueShape.Invariant clause : fields.invariants()) {
                    roots.add(clause.condition());
                }
            }
        }
        return roots;
    }

    /**
     * What was read of a module, and the call boundary of each behavior it declares.
     *
     * <p>The boundaries in the order the module declares them, which is the order its behaviors are
     * made in. Carried from where they were filed to where the module is made, rather than looked
     * up there: the module is made off the same declarations they were made off, and a second walk
     * of those declarations would be two statements of what the module declares held together by a
     * check.
     */
    private record ModuleBoundaries(ModuleReading read,
                                    Map<ValueName.Behavior, BehaviorTarget> declared) {}

    /**
     * Files the call boundary of every behavior {@code module} declares.
     *
     * <p>What the module declares says which behaviors there are, and the answers this compile
     * worked out say what each of them is — the same three readings a module on the path is read in
     * ({@link #fileWhatIsOnThePath}), and read the same way here. A walk of the signatures instead
     * would let a behavior whose signature this compile failed to answer for leave the program
     * without anything having missed it: what a module declares would be whatever the answer
     * happened to hold.
     *
     * <p>Both answers are read here, beside the name they belong to, and a missing one is refused
     * here. Read further in, at the place that decides what an implementation is made of, a missing
     * answer arrives where a state is being chosen — and it is chosen as one of them.
     */
    private static ModuleBoundaries fileWhatIsChecked(
            Map<ValueName.Behavior, BehaviorTarget> targets, ModuleReading module, Db db) {
        Map<ValueName.Behavior, BehaviorTarget> declares = new LinkedHashMap<>();
        Map<String, SpecImplementation.Implemented> implementations =
                SpecImplementation.implementationsOf(module.bodies());
        for (Hir.BehaviorDef declared : module.bodies().behaviors()) {
            ValueName.Behavior named = new ValueName.Behavior(module.name(), declared.name());
            CheckedSignature signature = switch (declared) {
                case Hir.SpecBehavior _ -> {
                    DeclaredSig written = module.declaredSignatures().get(declared.name());
                    yield written == null ? null : declaredSignatureOf(written, module.name(), db);
                }
                case Hir.PipeBehavior _ -> {
                    Sig composed = module.signatures().get(declared.name());
                    yield composed == null ? null : composedSignatureOf(composed, module.name(), db);
                }
            };
            if (signature == null) {
                // The module was taken as checked and one of the behaviors it declares has no
                // signature. A caller reaches it, so letting it through hands an output a call it
                // cannot emit and says nothing about why.
                throw new IllegalStateException("`" + named + "` was taken as checked and this"
                        + " compile has no reading of it");
            }
            BehaviorImplementation state = module.implementations().of(named);
            CheckedImplementation implementation = implementedAs(state, named, declared,
                    implementations, module.checked(), module.compositions());
            BehaviorTarget target = new BehaviorTarget(signature, implementation,
                    constructionRequirementsOf(named, module.requirements()));
            file(targets, named, target);
            declares.put(named, target);
        }
        return new ModuleBoundaries(module, declares);
    }

    /**
     * Files the call boundary of every behavior every module this compile read off the path
     * declares.
     *
     * <p>The whole of what each declares, and not the part something here calls. Which behaviors a
     * body reaches is a walk, and a snapshot carrying only what one walk found would be right about
     * the calls that walk thought to visit — and an output emitting those bodies would be the
     * second place that decided what belongs.
     *
     * <p>What the module declares says which behaviors there are, and the answers this compile
     * worked out say what each of them is. Three readings and not one: a module read off the path
     * is available here because a module of this compile was checked against it, so a name it
     * declares that this compile has no signature or no implementation state for is this
     * compilation's two readings of that artifact having come apart, and is refused rather than
     * quietly left out of the program.
     */
    private static void fileWhatIsOnThePath(Map<ValueName.Behavior, BehaviorTarget> targets,
                                            Db db) {
        for (String module : readOffThePath(db)) {
            Ast.Module declares = db.ask(new Front.Available(module)).value();
            Map<String, Sig> signatures = db.ask(new Bodies.Signatures(module)).value();
            Map<String, DeclaredSig> declaredSignatures =
                    db.ask(new Bodies.DeclaredSignatures(module)).value();
            BehaviorBodies implementations = db.ask(new Bodies.Implementation(module)).value();
            // The answer a composition here that uses one of these as a stage was worked out from,
            // and not a second reading of what the module published: this is the answer that holds
            // the module to what it was built against.
            Map<String, List<BehaviorRequirement>> requirements =
                    db.ask(new Bodies.Requirements(module)).value();
            if (declares == null || signatures == null || declaredSignatures == null
                    || implementations == null || requirements == null) {
                throw new IllegalStateException("`" + module + "` was read off the path and this"
                        + " compile has nothing to say about the behaviors it declares");
            }
            Map<String, List<ValueName.Behavior>> required = requirementsOf(requirements);
            for (Ast.BehaviorDef declared : declares.behaviors()) {
                ValueName.Behavior named = new ValueName.Behavior(module, declared.name());
                CheckedSignature signature = switch (declared) {
                    case Ast.SpecBehavior _ -> {
                        DeclaredSig written = declaredSignatures.get(declared.name());
                        yield written == null ? null : declaredSignatureOf(written, module, db);
                    }
                    case Ast.PipeBehavior _ -> {
                        Sig composed = signatures.get(declared.name());
                        yield composed == null ? null : composedSignatureOf(composed, module, db);
                    }
                };
                if (signature == null) {
                    throw new IllegalStateException("`" + named + "` is declared by a module this"
                            + " compile read off the path and this compile has no reading of it");
                }
                CheckedImplementation implementation = publishedAs(implementations.of(named));
                file(targets, named, new BehaviorTarget(signature, implementation,
                        constructionRequirementsOf(named, required)));
            }
        }
    }

    /**
     * What constructing {@code named} requires injected, as this compile answered for its module.
     *
     * <p>Read and handed on, and not worked out from the implementation. The answer has an entry
     * for every behavior the module declares, an injected one requiring nothing, so a missing entry
     * is the answer not holding together and is refused rather than read as requiring nothing. An
     * entry that disagrees with the implementation reaches {@link BehaviorTarget}, which refuses it:
     * supplying the value the implementation says it should be would make that refusal one that
     * never runs on what a compile produces.
     */
    private static List<ValueName.Behavior> constructionRequirementsOf(
            ValueName.Behavior named, Map<String, List<ValueName.Behavior>> requirements) {
        List<ValueName.Behavior> required = requirements.get(named.name());
        if (required == null) {
            throw new IllegalStateException("`" + named + "` is declared and this compile has no"
                    + " requirement set for it");
        }
        return required;
    }

    /**
     * Where the implementation of a behavior another compile published comes from.
     *
     * <p>Its three states are the three a behavior is in anywhere. What a call reaches differs in
     * one of them: an implementation this program does not hold, because the build that published
     * the module emitted it. The other two are what they are wherever the behavior was declared —
     * an injected behavior's implementation comes from outside Souther on either side of a path,
     * and an unwritten one is nowhere at all.
     */
    private static CheckedImplementation publishedAs(BehaviorImplementation state) {
        return switch (state) {
            case IMPLEMENTED -> new CheckedImplementation.ImplementedElsewhere();
            case INJECTION_TARGET -> new CheckedImplementation.Injected();
            case UNIMPLEMENTED -> new CheckedImplementation.Unwritten();
        };
    }

    /**
     * Files one call boundary, and refuses a second under the same identity.
     *
     * <p>An identity belongs to one declaration. A module of this compile takes the name over one
     * of the same name on the path, so the two worlds never meet here — and one that did would be
     * called through whichever was filed last with nothing saying the other had been there.
     */
    private static void file(Map<ValueName.Behavior, BehaviorTarget> targets,
                             ValueName.Behavior named, BehaviorTarget target) {
        if (targets.put(named, target) != null) {
            throw new IllegalStateException("`" + named + "` is declared twice");
        }
    }

    /**
     * The modules this compile read off the path.
     *
     * <p>{@link Front.FromPath}'s answer: the ones this compilation may read declarations from,
     * which is not every module on the path and never one it refused. Asked once for everything
     * taken off them, so that what a dependency declares and what its behaviors are are read off
     * one set of modules — two walks with a rule each would agree until either was written again.
     *
     * <p>Empty where nothing was read off a path, which is a compilation given none.
     */
    private static Set<String> readOffThePath(Db db) {
        Front.FromPath.Of read = db.ask(new Front.FromPath()).value();
        return read == null ? Set.of() : read.modules().keySet();
    }

    /** The library this compilation was checked against. Asked for here rather than fetched: what a
     *  name in a checked body denotes was settled against that one, and a second copy could be a
     *  different version of the language. */
    private static Stdlib libraryOf(Db db) {
        Stdlib stdlib = db.ask(new Front.Library()).value();
        if (stdlib == null) {
            throw new IllegalStateException("this compilation was checked against no library");
        }
        return stdlib;
    }

    /**
     * What the language itself declares, as a value of one is laid out.
     *
     * <p>Read off the library this compilation was checked against, and not off a library fetched
     * here: what a name in a checked body denotes was settled against that one, and a second copy
     * could be a different version of the language.
     *
     * <p>Read against a world with no module in it. Which cases a sum descends to is answered by
     * {@link AtomSpace}, which asks the declarations it is given — and the language's own resolve
     * against the library alone, so reading them beside any one module's declarations would be
     * reading them somewhere they could have come out differently.
     */
    private static List<CheckedData> languageDataOf(Db db) {
        Stdlib stdlib = libraryOf(db);
        List<CheckedData> declared = new ArrayList<>();
        for (Hir.Def def : stdlib.languageDeclarations().values()) {
            if (def instanceof Hir.Data product) {
                // The language declares sums and the units under them, and a product of its own
                // would be one nothing here has the fields and clauses of: what a value of a
                // declaration is made of is derived over a compilation's modules, and derivation
                // does not run over the library. Said as what it is, rather than reached as an
                // absent shape — which is also what an assembler that forgot to read the shapes
                // would look like.
                throw new IllegalStateException("the language declares `" + product.declares()
                        + "` as a product, and what a value of one is made of is not derived here");
            }
            declared.add(declaredAs(def, db, Map.of(), Map.of()));
        }
        return declared;
    }

    /**
     * What every module this compile read off the path declares, as a value of one is laid out.
     *
     * <p>Read here and not left to the compile that built the dependency. This one read those
     * declarations already — it had to, to check a module that constructs one of them or reads a
     * field off one — so what is handed over is the reading the checker itself used, and an output
     * laying such a value out places its fields exactly where the check placed them.
     *
     * <p>The whole of what each declares, and not the part something here happens to name. Which
     * declarations a body reaches is a walk, and a snapshot carrying only what one walk found would
     * be right about the names that walk thought to visit.
     */
    private static List<CheckedData> declaredOnThePath(Db db) {
        List<CheckedData> declared = new ArrayList<>();
        for (String module : readOffThePath(db)) {
            Map<String, Derived.Def> defs = db.ask(new Shapes.DerivedDeclarations(module)).value();
            Map<TypeSymbol.AtModule, ValueShape> shapes =
                    db.ask(new Shapes.ValueShapes(module)).value();
            Symbols symbols = Names.derivedSymbols(db, module).value();
            if (defs == null || shapes == null || symbols == null) {
                // This compile read the module and checked a module against it, so what it declares
                // is something this compile already worked out. Letting it through would hand an
                // output a program whose identities it cannot all lay out, which is the thing this
                // is here to end.
                throw new IllegalStateException("`" + module + "` was read off the path and this"
                        + " compile has nothing to say about what it declares");
            }
            for (Derived.Def def : defs.values()) {
                declared.add(declaredAs(def.declaration().node(), db, shapes, defs));
            }
        }
        return declared;
    }

    /**
     * What this compiler answered about one module, and what those answers were made into.
     *
     * <p>Read in one pass so that what a module declares is in hand before what its rows state is
     * written down: the two are made in that order and not in the order the modules were given.
     *
     * @param rowsByBehavior what each of the module's behaviors' rows turned out to be, by behavior
     *             name, in the order the sources were read and the rows written
     */
    private record ModuleReading(String name, Hir.Module bodies, Bodies.Elaborated checked,
                                 Map<String, Sig> signatures,
                                 Map<String, DeclaredSig> declaredSignatures,
                                 BehaviorBodies implementations,
                                 Map<ValueName.Behavior, Composition> compositions,
                                 Map<ValueName.Behavior, EnsuresEnforcement> checks,
                                 List<CheckedData> data,
                                 Map<String, List<Output.RowsRead.ReadRow>> rowsByBehavior,
                                 Map<String, List<ValueName.Behavior>> requirements,
                                 Set<String> published) {}

    /**
     * The rows this compile read for {@code module}, by the behavior each is a row of.
     *
     * <p>Asked for rather than gathered. Which rows a behavior has is an answer over every source
     * the module's rows are written in, and it is one answer: a caller assembling it again decides
     * for itself what a source that did not answer means, and what it decided would be a second
     * statement of one fact. It is also what says a row was not read at all rather than not written.
     *
     * <p>Nothing is evaluated by asking. Running a row applies the helpers its fixtures name, and a
     * second run would apply them again — counted twice against the row and doing whatever they do
     * twice. What comes back is what the compile already answered.
     */
    private static Map<String, List<Output.RowsRead.ReadRow>> rowsOf(Db db, String module) {
        Output.RowsRead.Of read = db.ask(new Output.RowsRead(module)).value();
        if (read == null) {
            throw new IllegalStateException("`" + module + "` was taken as checked and its rows"
                    + " were not read");
        }
        Map<String, List<Output.RowsRead.ReadRow>> byBehavior = new LinkedHashMap<>();
        read.byBehavior().forEach((behavior, its) -> byBehavior.put(behavior, its.rows()));
        return byBehavior;
    }

    private static ModuleReading readingOf(Db db, String module) {
        Bodies.Elaborated checked = db.ask(new Bodies.Checked(module)).value();
        Lower.Lowered lowering = db.ask(new Bodies.Lowering(module)).value();
        Map<String, Sig> signatures = db.ask(new Bodies.Signatures(module)).value();
        // The declarations the signatures above were made from, for the names each parameter is
        // written under: what crosses the boundary is the same answer whatever a parameter is
        // called, so the names are asked of the answer that changes when one is renamed.
        Map<String, DeclaredSig> declaredSignatures =
                db.ask(new Bodies.DeclaredSignatures(module)).value();
        BehaviorBodies implementations = db.ask(new Bodies.Implementation(module)).value();
        Map<ValueName.Behavior, Composition> compositions =
                db.ask(new Compositions.Of(module)).value();
        // What a value of each declared data is made of and must satisfy, and where each behavior's
        // clause is checked. Both are what the language decided and both are read here rather than
        // worked out: the JVM is handed the same two answers, so an output reading this program and
        // the bytecode beside it hold one another's decisions.
        Map<TypeSymbol.AtModule, ValueShape> shapes =
                db.ask(new Shapes.ValueShapes(module)).value();
        // What each field a product or a newtype declares carries across the boundary — the same
        // walk `Shapes.ValueShapes` is read beside, held here so a reader of the program does not
        // re-derive it from a field's bare type.
        Map<String, Derived.Def> codecDefs = db.ask(new Shapes.DerivedDeclarations(module)).value();
        Map<ValueName.Behavior, EnsuresEnforcement> checks =
                db.ask(new Bodies.EnsuresChecks(module)).value();
        Map<String, List<BehaviorRequirement>> requirements =
                db.ask(new Bodies.Requirements(module)).value();
        // What the module's names mean over the derived declarations, which is what a declaration's
        // fields and a sum's cases are read against. It is a way of reaching the compiler's answers
        // and not one of them: it holds a registry that asks `db` for each declaration, so it is
        // read here and dropped here, and nothing it was reached through is carried into what is
        // made.
        Symbols symbols = Names.derivedSymbols(db, module).value();
        if (checked == null || lowering == null || signatures == null
                || declaredSignatures == null || implementations == null
                || compositions == null || symbols == null || shapes == null || checks == null
                || requirements == null || codecDefs == null) {
            // Not a report: the failure above is what a caller is told, and reaching here past it
            // means the two readings of whether this program checked have come apart.
            throw new IllegalStateException("`" + module + "` was taken as checked and is not");
        }
        // Two trees and each is read for what it is the tree for: a declaration comes off the
        // settled one and a body off the lowered one, which is the division `Lower.Lowered` states.
        // They are both `Hir.Module`, so nothing but the name at the call below says which is
        // being handed over — and a declaration read off the tree the backend emits from would
        // agree with the checker only for as long as lowering left declarations alone.
        Hir.Module declarations = lowering.settled();
        Hir.Module bodies = lowering.lowered();
        // What the module publishes, asked of the one answer everything that reaches across a
        // module boundary asks. Read off the `exposing` clause again here, this would be a second
        // reading of a decision the check already made — and the two would agree until one of them
        // learnt something.
        Set<String> published = db.ask(new Front.Exposes(module)).value();
        if (published == null) {
            // The same reading as every other answer above: a module taken as checked is one every
            // question about it has been answered for, and nothing here turns an answer that was
            // never read into a module that publishes nothing.
            throw new IllegalStateException("`" + module + "` was taken as checked and what it"
                    + " publishes was not read");
        }
        return new ModuleReading(module, bodies, checked, signatures, declaredSignatures,
                implementations,
                compositions, checks,
                dataOf(declarations, db, shapes, codecDefs),
                rowsOf(db, module), requirementsOf(requirements), published);
    }

    /**
     * {@code requirements}, projected to the dependency identities alone.
     *
     * <p>{@link BehaviorRequirement#requiredBy} is a compiler diagnostic's provenance for a missing
     * fake, not a fact a checked program's reader wants — every one of those wants the dependency
     * and the order its constructor takes them in, which {@link Requirements#names} already
     * answers.
     */
    private static Map<String, List<ValueName.Behavior>> requirementsOf(
            Map<String, List<BehaviorRequirement>> requirements) {
        Map<String, List<ValueName.Behavior>> byName = new LinkedHashMap<>();
        requirements.forEach((name, reqs) -> byName.put(name, Requirements.names(reqs)));
        return byName;
    }

    /**
     * The module, made from what was read of it.
     *
     * <p>{@code types} is how a value's parts are read wherever one is compared, and it is the whole
     * program's rather than this module's: a row written here may state a value of a data declared
     * elsewhere.
     */
    private static CheckedModule moduleOf(ModuleBoundaries module, ValueTypes types,
                                          Map<ValueName.Behavior, BehaviorTarget> targets) {
        ModuleReading read = module.read();
        Emitted emitted = emittedBy(read.name(), read.checked());
        List<CheckedBehavior> behaviors = new ArrayList<>();
        module.declared().forEach((named, target) ->
                behaviors.add(new CheckedBehavior(named, target,
                        EnsuresEnforcement.in(read.checks(), read.name(), named),
                        rowsOf(read.rowsByBehavior().getOrDefault(named.name(), List.of()), types,
                                target.signature(), targets, emitted.rowValues()))));
        return new CheckedModule(read.name(), behaviors, emitted.helpers(), emitted.values(),
                emitted.valueEntries(), read.data(), read.published());
    }

    /**
     * One behavior's rows, as an output reads them.
     *
     * <p>Written down rather than worked out: what each row states was read where the row was read,
     * and what is made here is the handle a reader holds it by. Each is given what answering
     * {@link CheckedRow.SelfContained#holds} takes — how a value's parts are read, and where this
     * behavior's answer stands — so that asking is not a question about the program the row came
     * from. A row that stands something in for a dependency is given where that dependency's
     * arguments stand as well, for the same reason. And a row that hands over values is given the
     * definition computing each of them, and each value its stand-ins state, out of
     * {@code rowValues}: the helpers of the module the row is written in that compute a row's
     * operand, by the name each was emitted under.
     */
    private static List<CheckedRow> rowsOf(List<Output.RowsRead.ReadRow> read, ValueTypes types,
                                           CheckedSignature signature,
                                           Map<ValueName.Behavior, BehaviorTarget> targets,
                                           Map<String, CheckedHelper> rowValues) {
        List<CheckedRow> rows = new ArrayList<>();
        for (Output.RowsRead.ReadRow row : read) {
            rows.add(new CheckedRow(row.identity(), row.at(),
                    statementOf(row, types, signature, targets, rowValues)));
        }
        return rows;
    }

    /**
     * What the row states, as a reader of a checked program may act on it.
     *
     * <p>A row that stated values is given what asking takes — how a value's parts are read here,
     * and where this behavior's answer stands — and the reading it is given is this program's. The
     * one the compile read the text with is not carried: it is a way of reaching this compiler's
     * answers rather than one of them, and a snapshot holding it would hold the compilation it came
     * from.
     *
     * <p>A switch, so a way of stating a row added later is written down here rather than falling
     * into whichever arm it happens to reach.
     */
    private static CheckedRow.Statement statementOf(Output.RowsRead.ReadRow row, ValueTypes types,
                                                    CheckedSignature signature,
                                                    Map<ValueName.Behavior, BehaviorTarget> targets,
                                                    Map<String, CheckedHelper> rowValues) {
        // A switch over both sums, so a row nothing came back for is written down here rather than
        // being whatever falls out of reading a list of the ones that did — which is a row an output
        // would never hear of, and a behavior reading as having said nothing about an input someone
        // wrote down.
        return switch (row) {
            case Output.RowsRead.ReadRow.Ran ran -> switch (ran.outcome().statement()) {
                // A row whose answer is owed first, because what a reader can do with a row turns on
                // whether there is anything to hold before it turns on what the row needs to run.
                // Sorted the other way, such a row would arrive as one an output applies and asks,
                // and what it asked would be answered against no statement at all.
                case RowStatement.Stated stated
                        when stated.expects() instanceof Expectation.Owed ->
                        new CheckedRow.AnswerOwed(stated,
                                suppliesOf(ran, stated, targets, rowValues), types);
                case RowStatement.Stated stated -> stated.standIns().isEmpty()
                        ? new CheckedRow.SelfContained(stated,
                                suppliesOf(ran, stated, targets, rowValues), types,
                                Position.at(signature.answers()))
                        : new CheckedRow.WithStandIns(stated,
                                suppliesOf(ran, stated, targets, rowValues), types,
                                Position.at(signature.answers()));
                case RowStatement.NotStated why -> new CheckedRow.NotReproducible(why);
                // What acceptance guarantees, asserted where the guarantee is relied on. A row an
                // evaluation stopped before the values of is one the language refuses the program
                // for, so meeting one here is that guarantee having moved — and the row would
                // otherwise be published as a state whose reason is in a compile nobody outside
                // this one can read.
                case RowStatement.StoppedBeforeItsValues _ -> throw new IllegalStateException(
                        "a program the language accepted holds a row its evaluation stopped before"
                                + " the values of: " + ran.outcome().target() + " "
                                + ran.outcome().identity().shown() + " at " + ran.outcome().at());
            };
            case Output.RowsRead.ReadRow.NotRun notRun ->
                    new CheckedRow.NotReproducible(new RowStatement.NotRead(notRun.why()));
        };
    }

    /**
     * What {@code ran}'s row hands over, for whichever arm it is: what computes each input, where
     * each dependency's arguments stand, and what computes each value its stand-ins state.
     *
     * <p>Made the same way for every arm that states values. Whether the row's answer is owed and
     * whether it needs something stood in for are two questions, and what an arm is handed does
     * not turn on the first.
     */
    private static CheckedRow.Supplies suppliesOf(Output.RowsRead.ReadRow.Ran ran,
                                                  RowStatement.Stated stated,
                                                  Map<ValueName.Behavior, BehaviorTarget> targets,
                                                  Map<String, CheckedHelper> rowValues) {
        return new CheckedRow.Supplies(computing(ran, stated, rowValues),
                whereArgumentsStand(stated, targets), computingStandIns(ran, stated, rowValues));
    }

    /**
     * The definition computing each input of {@code ran}'s row, as its module holds it.
     *
     * <p>Looked up by the name the reading of the row says each was emitted under, among the
     * helpers the module holds for a row's operand. One for each value the row states: a program
     * the language accepted had its rows read with the declarations in hand, so a row stating
     * values names what computes each of them. A name with nothing under it is a row read against
     * a module other than the one whose helpers are in hand, which the row would otherwise carry
     * into the program as an input nothing computes.
     */
    private static List<CheckedHelper> computing(Output.RowsRead.ReadRow.Ran ran,
                                                 RowStatement.Stated stated,
                                                 Map<String, CheckedHelper> rowValues) {
        RowOutcome outcome = ran.outcome();
        if (ran.inputDefinitions().size() != stated.inputs().size()) {
            throw new IllegalStateException("a program the language accepted holds a row stating "
                    + stated.inputs().size() + " value(s) whose reading names "
                    + ran.inputDefinitions() + " as computing them: " + outcome.target() + " "
                    + outcome.identity().shown() + " at " + outcome.at());
        }
        List<CheckedHelper> inputs = new ArrayList<>();
        for (String method : ran.inputDefinitions()) {
            inputs.add(definitionNamed(method, rowValues, "an input", outcome));
        }
        return inputs;
    }

    /**
     * What computes each value {@code ran}'s row states a dependency answers, by the dependency.
     *
     * <p>Looked up as {@link #computing} looks up the inputs, among the same helpers. Each entry the
     * reading named is held to the entry of the stand-in it is put beside by where the two say the
     * entry is written, and the answer for the rest the same way: that is what the reading found
     * each of them among the module's tables by. A stand-in the reading named nothing for, or named
     * a different number of entries, an entry written elsewhere, or another answer for the rest
     * for, is the two readings of one row having come apart, and is refused rather than carried in
     * with values something else computes.
     */
    private static Map<ValueName.Behavior, StandsIn.Computed> computingStandIns(
            Output.RowsRead.ReadRow.Ran ran, RowStatement.Stated stated,
            Map<String, CheckedHelper> rowValues) {
        RowOutcome outcome = ran.outcome();
        Map<ValueName.Behavior, StandsIn.Computed> byDependency = new LinkedHashMap<>();
        for (StoodIn stoodIn : stated.standIns()) {
            Output.RowsRead.StandInDefinitions named =
                    ran.standInDefinitions().get(stoodIn.dependency());
            if (named == null || named.entries().size() != stoodIn.entries().size()) {
                throw new IllegalStateException("a program the language accepted holds a row whose"
                        + " stand-in for `" + stoodIn.dependency() + "` states the entries "
                        + stoodIn.entries() + " and whose reading names " + named
                        + " as computing them: " + outcome.target() + " "
                        + outcome.identity().shown() + " at " + outcome.at());
            }
            List<StandsIn.Entry> entries = new ArrayList<>();
            for (int i = 0; i < stoodIn.entries().size(); i++) {
                Output.RowsRead.StandInDefinitions.EntryDefinitions each = named.entries().get(i);
                StoodIn.Entry stoodInEntry = stoodIn.entries().get(i);
                if (!each.at().equals(stoodInEntry.at())) {
                    throw new IllegalStateException("a program the language accepted holds a row"
                            + " whose stand-in for `" + stoodIn.dependency() + "` states the entry"
                            + " at " + stoodInEntry.at() + " where its reading names what computes"
                            + " the entry at " + each.at() + ": " + outcome.target() + " "
                            + outcome.identity().shown() + " at " + outcome.at());
                }
                List<CheckedHelper> arguments = new ArrayList<>();
                for (String method : each.arguments()) {
                    arguments.add(definitionNamed(method, rowValues, "an argument a stand-in states",
                            outcome));
                }
                entries.add(new StandsIn.Entry(stoodInEntry, arguments,
                        definitionNamed(each.answer(), rowValues, "an answer a stand-in states",
                                outcome)));
            }
            byDependency.put(stoodIn.dependency(), new StandsIn.Computed(entries,
                    computingTheRest(stoodIn, named.otherwise(), rowValues, outcome)));
        }
        return byDependency;
    }

    /**
     * What computes what {@code stoodIn} answers for the rest, off what the row's reading named.
     *
     * <p>Over both sums, so that a stand-in answering something for the rest with nothing named to
     * compute it, and one stating nothing with something named, are each refused by name rather
     * than sharing whatever arm the two happen to fall into.
     */
    private static StandsIn.Otherwise computingTheRest(
            StoodIn stoodIn, Output.RowsRead.StandInDefinitions.Otherwise named,
            Map<String, CheckedHelper> rowValues, RowOutcome outcome) {
        return switch (stoodIn.otherwise()) {
            case StoodIn.Otherwise.Answer answer -> switch (named) {
                case Output.RowsRead.StandInDefinitions.Otherwise.Computed(
                        SourcePos at, String method) -> {
                    if (!at.equals(answer.at())) {
                        throw new IllegalStateException("a program the language accepted holds a"
                                + " row whose stand-in for `" + stoodIn.dependency() + "` answers"
                                + " for the rest with what is written at " + answer.at()
                                + " where its reading names what computes the value at " + at
                                + ": " + outcome.target() + " " + outcome.identity().shown()
                                + " at " + outcome.at());
                    }
                    yield new StandsIn.Otherwise.Answers(answer, definitionNamed(method, rowValues,
                            "what a stand-in answers for the rest", outcome));
                }
                case Output.RowsRead.StandInDefinitions.Otherwise.NothingStated _ ->
                        throw new IllegalStateException("a program the language accepted holds a"
                                + " row whose stand-in for `" + stoodIn.dependency() + "` answers"
                                + " for the rest and whose reading names nothing computing it: "
                                + outcome.target() + " " + outcome.identity().shown() + " at "
                                + outcome.at());
            };
            case StoodIn.Otherwise.NothingStated _ -> switch (named) {
                case Output.RowsRead.StandInDefinitions.Otherwise.Computed(
                        SourcePos _, String method) ->
                        throw new IllegalStateException("a program the language accepted holds a"
                                + " row whose stand-in for `" + stoodIn.dependency() + "` states"
                                + " nothing for the rest and whose reading names `" + method
                                + "` as computing it: " + outcome.target() + " "
                                + outcome.identity().shown() + " at " + outcome.at());
                case Output.RowsRead.StandInDefinitions.Otherwise.NothingStated _ ->
                        new StandsIn.Otherwise.NothingStated();
            };
        };
    }

    /**
     * The helper the module holds under {@code method}, which the reading of {@code outcome}'s row
     * named as computing {@code what}. A name with nothing under it is a row read against a module
     * other than the one whose helpers are in hand, which the row would otherwise carry into the
     * program as a value nothing computes.
     */
    private static CheckedHelper definitionNamed(String method, Map<String, CheckedHelper> rowValues,
                                                 String what, RowOutcome outcome) {
        CheckedHelper helper = rowValues.get(method);
        if (helper == null) {
            throw new IllegalStateException(what + " of " + outcome.target() + " "
                    + outcome.identity().shown() + " at " + outcome.at() + " is computed by `"
                    + method + "`, which the module holds no helper for");
        }
        return helper;
    }

    /**
     * Where the arguments of each dependency the row stood in for stand.
     *
     * <p>Off the dependency's own call boundary, which is the one thing this snapshot says about
     * what that behavior takes — so what a stand-in's entries were built against and what a reader
     * compares an argument at are one reading of one declaration, rather than the same declaration
     * written down twice and held to itself by a law.
     *
     * <p>It is what says how a comparison is made as well as how many are: whether an argument that
     * is a sequence is the same one written in another order is what the type reading it says.
     */
    private static Map<ValueName.Behavior, List<Position>> whereArgumentsStand(
            RowStatement.Stated stated, Map<ValueName.Behavior, BehaviorTarget> targets) {
        Map<ValueName.Behavior, List<Position>> stands = new LinkedHashMap<>();
        for (StoodIn stoodIn : stated.standIns()) {
            BehaviorTarget declared = targets.get(stoodIn.dependency());
            if (declared == null) {
                // A row stood in for a behavior no module this compile checked or read declares.
                // Whether the module the row is written in may name that behavior is settled where
                // the names are resolved and is not asked again here; what is asked is whether the
                // program the row is being written into declares it at all.
                throw new IllegalStateException("`" + stoodIn.dependency() + "` was stood in for by"
                        + " a row and no module this compile read declares it");
            }
            List<Position> arguments = new ArrayList<>();
            for (Type takes : declared.signature().takes()) {
                arguments.add(Position.at(takes));
            }
            stands.put(stoodIn.dependency(), arguments);
        }
        return stands;
    }

    /**
     * What the module declares.
     *
     * <p>Each of the four forms is materialised from the answer this compiler already has for it,
     * and neither walk is written again here. A product's fields are
     * {@link TypeOps#fieldTypes}, which flattens what an include brought in; a sum's cases are
     * {@link AtomSpace#subjectAtoms}, which descends a case that is itself a sum and reaches one
     * case once. Both are decisions the language made, and an assembler with a walk of its own
     * would be the second place that made them — which is the thing a reader outside this compiler
     * is being given these to avoid.
     *
     * <p>{@code fieldTypes} answers in the order a value lays its fields out, and that order is
     * carried straight into the list. Nothing between the two holds the fields as a set: an order
     * the answer decided, passed through something that does not keep one, comes out as an order
     * nothing decided.
     *
     * <p>The list is what the module holds and its order is not answered for. A declaration written
     * on its own and one a sum's case list declares reach {@code defs} by different routes, so
     * where either stands among them is how the front end put them there rather than something the
     * language decided. The two orders that are decided are inside a declaration —
     * {@link CheckedData.WithFields#fields} and {@link CheckedData.Sum#cases} — and those are the
     * ones said out loud.
     */
    private static List<CheckedData> dataOf(Hir.Module declarations, Db db,
                                           Map<TypeSymbol.AtModule, ValueShape> shapes,
                                           Map<String, Derived.Def> codecDefs) {
        List<CheckedData> declared = new ArrayList<>();
        for (Hir.Def def : declarations.defs()) {
            declared.add(declaredAs(def, db, shapes, codecDefs));
        }
        return declared;
    }

    /**
     * One declaration, in whichever of the four forms it was written.
     *
     * <p>One reading for both worlds. A module's declaration and the language's are the same kind
     * of thing — they resolve and type alike and a value of either lays out alike — and this is
     * where that stops being something two readings agree about.
     */
    private static CheckedData declaredAs(Hir.Def def, Db db,
                                          Map<TypeSymbol.AtModule, ValueShape> shapes,
                                          Map<String, Derived.Def> codecDefs) {
        return switch (def) {
            case Hir.Data data -> checkedDataOf(data, shapes, codecDefs);
            case Hir.SumData sum -> {
                // Asked of the store and not settled here: this is a `Type -> answer` question, and
                // the answer belongs to whichever check-stage query already answers it for every
                // other reader — never to a second place that works it out again.
                Boundary.Alternatives alternatives = db.ask(new Shapes.TypeAlternatives(
                        sum.declares().key().module(), Type.ref(sum.declares()))).value();
                yield new CheckedData.Sum(sum.declares(), alternatives.atoms(),
                        projectRepresentation(alternatives.representation()));
            }
            case Hir.UnitData unit -> new CheckedData.Unit(unit.declares());
        };
    }

    /**
     * One data built field by field, as the check answered what a value of it is made of and as the
     * author wrote it.
     *
     * <p>Handed over and not rebuilt. The fields, the binding each is read through and the clauses
     * that must hold of a value are one answer of the checker's, and the JVM emits a construction
     * from that same answer — so what an output outside this compiler reads and what the bytecode
     * refuses a value by cannot come apart.
     *
     * <p>Which of the two arms it is, is what the author wrote. A newtype and a one-field product
     * reach here with the same shape, and the shape is what the language says does not decide
     * between them (spec §newtype), so it is read off the declaration — the same answer a derived
     * codec is generated from.
     */
    private static CheckedData checkedDataOf(Hir.Data data,
                                             Map<TypeSymbol.AtModule, ValueShape> shapes,
                                             Map<String, Derived.Def> codecDefs) {
        ValueShape shape = shapes.get(data.declares());
        if (shape == null) {
            // The module was taken as checked, and a declaration of it has no answer for what a
            // value of it is. Handing over a product with no clauses would be saying that anything
            // its fields admit is one of it, which is the opposite of what the author wrote.
            throw new IllegalStateException("`" + data.declares() + "` was taken as checked and"
                    + " the check said nothing about what a value of it is");
        }
        List<CheckedCodecShape> codecShapes = codecShapesOf(data, shape, codecDefs);
        return data.newtype() ? new CheckedData.Newtype(shape, codecShapes)
                : new CheckedData.Product(shape, codecShapes);
    }

    /**
     * What each of {@code shape}'s fields carries across the boundary, in the same order — read
     * off the shape {@link Deriver} already derived rather than derived again here.
     */
    private static List<CheckedCodecShape> codecShapesOf(Hir.Data data, ValueShape shape,
                                                          Map<String, Derived.Def> codecDefs) {
        Derived.Def derived = codecDefs.get(data.declares().name());
        if (!(derived instanceof Derived.Data withCodec)) {
            // Present for every product this compile checked (`Shapes.DerivedDeclarations` only
            // leaves one out where a field of it names no type, which is refused before a module
            // reaches here) — so a product with a `ValueShape` and nothing here is the two readings
            // of this module having come apart, the same disagreement `checkedDataOf` refuses above.
            throw new IllegalStateException("`" + data.declares() + "` was taken as checked and"
                    + " nothing here derived what its fields carry across the boundary");
        }
        Map<String, CodecShape> byField = withCodec.fieldShapes();
        List<CheckedCodecShape> codecShapes = new ArrayList<>(shape.fields().size());
        for (ValueShape.Field field : shape.fields()) {
            CodecShape fieldShape = byField.get(field.name());
            if (fieldShape == null) {
                // The two readings of this declaration's fields — what a value is made of and what
                // each field carries across the boundary — are worked out by two different walks,
                // and a name one of them has that the other does not is those two walks having come
                // apart on this declaration, not a field a reader can be handed nothing for.
                throw new IllegalStateException("`" + data.declares() + "` was taken as checked and"
                        + " nothing here derived what its field `" + field.name()
                        + "` carries across the boundary");
            }
            codecShapes.add(projectCodecShape(fieldShape));
        }
        return codecShapes;
    }

    /** {@code checked}, carried over without the boundary-admission witnesses it was built from. */
    private static CheckedCodecShape projectCodecShape(CodecShape checked) {
        return switch (checked) {
            case CodecShape.Scalar s -> new CheckedCodecShape.Scalar(s.kind());
            case CodecShape.Named n -> new CheckedCodecShape.Named(n.admitted().name());
            case CodecShape.ListOf l ->
                    new CheckedCodecShape.ListOf(projectCodecShape(l.element()));
            case CodecShape.SetOf s -> new CheckedCodecShape.SetOf(projectCodecShape(s.element()));
            case CodecShape.MapOf m -> new CheckedCodecShape.MapOf(m.key().representation(),
                    projectCodecShape(m.value()));
            case CodecShape.OptionOf o ->
                    new CheckedCodecShape.OptionOf((CheckedCodecShape.Bare) projectCodecShape(o.present()));
        };
    }

    /**
     * What the behavior takes and answers, as the checked boundary shape.
     *
     * <p>The compiler's own {@link BoundaryInput}/{@link BoundaryOutput} are projected rather than
     * handed over whole: each holds a witness — which of a {@code Map}'s key readings admitted it —
     * that offers the module as it was parsed, so handing one over whole would put the syntax tree
     * two hops from a behavior's declared output. What is kept is the answer the witness proves,
     * never the witness.
     *
     * <p>Each parameter is carried with the name it was declared under, off the one
     * {@link DeclaredSig.Input} that holds both: the pairing is what the declaration was admitted
     * as, and nothing here lines a name up with a shape by position.
     */
    private static CheckedSignature declaredSignatureOf(DeclaredSig declared, String moduleName,
                                                        Db db) {
        List<CheckedSignature.Parameter> parameters = new ArrayList<>(declared.inputs().size());
        for (DeclaredSig.Input input : declared.inputs()) {
            parameters.add(
                    new CheckedSignature.Parameter(input.name(), projectInput(input.boundary())));
        }
        return CheckedSignature.declared(parameters,
                projectOutput(declared.boundary().out(), moduleName, db));
    }

    /** What a composition takes and answers, projected the same way. It wrote no parameters, so
     *  its inputs have no names to carry. */
    private static CheckedSignature composedSignatureOf(Sig signature, String moduleName, Db db) {
        List<CheckedBoundaryInput> inputs = new ArrayList<>(signature.ins().size());
        for (BoundaryInput in : signature.ins()) {
            inputs.add(projectInput(in));
        }
        return CheckedSignature.composed(inputs, projectOutput(signature.out(), moduleName, db));
    }

    /** {@code checked}, carried over without the admission witness it was made from. */
    private static CheckedBoundaryInput projectInput(BoundaryInput checked) {
        return switch (checked) {
            case BoundaryInput.Scalar s -> new CheckedBoundaryInput.Scalar(s.scalar());
            case BoundaryInput.Nominal n -> new CheckedBoundaryInput.Nominal(n.name());
            case BoundaryInput.ListOf l -> new CheckedBoundaryInput.ListOf(projectInput(l.element()));
            case BoundaryInput.SetOf s -> new CheckedBoundaryInput.SetOf(projectInput(s.element()));
            case BoundaryInput.MapOf m ->
                    new CheckedBoundaryInput.MapOf(m.key().representation(), projectInput(m.value()));
        };
    }

    /**
     * {@code checked}, carried over the same way. A union of cases nobody named together carries
     * its wire cases and their form beside the union itself — asked of the store rather than
     * settled here, the same {@link souther.compiler.query.Shapes.TypeAlternatives} a named sum's
     * cases answer from (spec §sum-discrimination) — rather than left for a reader to work out from
     * the union's own members, which are not descended the way a boundary's cases are.
     */
    private static CheckedBoundaryOutput projectOutput(BoundaryOutput checked, String moduleName, Db db) {
        return switch (checked) {
            case BoundaryOutput.Scalar s -> new CheckedBoundaryOutput.Scalar(s.scalar());
            case BoundaryOutput.Nominal n -> new CheckedBoundaryOutput.Nominal(n.name());
            case BoundaryOutput.ListOf l ->
                    new CheckedBoundaryOutput.ListOf(projectOutput(l.element(), moduleName, db));
            case BoundaryOutput.SetOf s ->
                    new CheckedBoundaryOutput.SetOf(projectOutput(s.element(), moduleName, db));
            case BoundaryOutput.MapOf m -> new CheckedBoundaryOutput.MapOf(
                    m.key().representation(), projectOutput(m.value(), moduleName, db));
            case BoundaryOutput.Cases c -> {
                // `c.type()` answers `Type` — the interface every case here answers — but a union
                // is what this case was admitted from and the only thing it could be.
                Type.Union union = (Type.Union) c.type();
                Boundary.Alternatives alternatives =
                        db.ask(new Shapes.TypeAlternatives(moduleName, union)).value();
                yield new CheckedBoundaryOutput.Cases(union, alternatives.atoms(),
                        projectRepresentation(alternatives.representation()));
            }
        };
    }

    /** {@code representation}, carried over: enumeration or discriminated, and the keys where it is
     *  one (spec §sum-discrimination). */
    private static CheckedAlternativesForm projectRepresentation(Boundary.Representation representation) {
        return switch (representation) {
            case Boundary.Representation.Enumeration _ -> new CheckedAlternativesForm.Enumeration();
            case Boundary.Representation.Discriminated d ->
                    new CheckedAlternativesForm.Discriminated(d.tagKey(), d.contentsKey());
        };
    }

    /**
     * Where this behavior's implementation comes from, for a behavior this compile checked.
     *
     * <p>Never {@link CheckedImplementation.ImplementedElsewhere}: this compile holds what a module
     * it checked is implemented as, and a behavior published by another compile is read by
     * {@link #publishedAs}.
     *
     * <p>Given the state rather than the table it is in, as {@link #publishedAs} is. What a
     * behavior this compile has no reading of comes to is not a state to choose between here — it
     * is a program with nothing to say about one of its own behaviors, said where a behavior's
     * answers are read.
     *
     * <p>What is decided here is the form: the state says a body was written and the check says
     * whether it settled a composition, and a reader handed the two separately would be deciding
     * for itself what an implemented behavior with no Core is.
     */
    private static CheckedImplementation implementedAs(
            BehaviorImplementation state, ValueName.Behavior named, Hir.BehaviorDef declared,
            Map<String, SpecImplementation.Implemented> implementations, Bodies.Elaborated checked,
            Map<ValueName.Behavior, Composition> compositions) {
        String name = declared.name();
        return switch (state) {
            case UNIMPLEMENTED -> new CheckedImplementation.Unwritten();
            case INJECTION_TARGET -> new CheckedImplementation.Injected();
            // A composition is what the behavior is declared as, so what says it is one is that the
            // check settled stages for it and not the absence of a body.
            case IMPLEMENTED -> {
                Composition composed = compositions.get(named);
                yield composed != null
                        ? new CheckedImplementation.Composed(composed)
                        : new CheckedImplementation.Body(
                                inputBindersOf(named, implementations.get(name)),
                                checked.behaviorBodies().get(name));
            }
        };
    }

    /**
     * The bindings this behavior's body reads its declared inputs through.
     *
     * <p>Read off the definition that implements it, and divided from what that definition takes by
     * {@link SpecImplementation} — which is the same reading the JVM emitter binds its parameters
     * from, so the snapshot and the emitted program cannot come to disagree about which local an
     * input arrives in. The division is that rule's and not this one's: a definition's trailing
     * parameters are the behaviors it depends on, and an assembler slicing the list itself would be
     * a second place that knew so.
     *
     * <p>Sliced by what the behavior declares and not by how long its signature is. Sliced by the
     * signature the two lengths would be equal by construction, and {@link BehaviorTarget}'s check
     * of them would be comparing an answer with itself — the disagreement it is there to refuse
     * would arrive instead as a dependency's binder handed over as an input's.
     */
    private static List<Core.Binder> inputBindersOf(ValueName.Behavior named,
                                                    SpecImplementation.Implemented implemented) {
        if (implemented == null) {
            // This behavior was taken as implemented here and by a body of its own, and the module
            // has no definition to read one from. Nothing here can put that right, and letting it
            // through would hand an output a body whose reads resolve to nothing it was given.
            throw new IllegalStateException("`" + named.module() + "." + named.name()
                    + "` was taken as having a body and has no definition to read it from");
        }
        if (!implemented.hasCompleteShape()) {
            // What this assembler takes, said here rather than by the reading that divided the
            // parameters: an editor reads a definition whose parameters do not line up and answers
            // what it can about it, and a checked program holds none.
            throw new IllegalStateException("`" + named.module() + "." + named.name()
                    + "` was taken as checked and its implementation writes parameters the"
                    + " declaration does not account for");
        }
        List<Core.Binder> binders = new ArrayList<>();
        for (Hir.FnParam input : implemented.inputs()) {
            binders.add(CoreBinders.of(input.binder()));
        }
        return binders;
    }

    /**
     * What this module emits as methods of its own: the helpers it carries, the values it builds,
     * and the entries it publishes for them.
     *
     * <p>Which of the three each method is was answered where the method was lowered, and is read
     * here as it was answered. Nothing is worked out again from what a method takes or what it is
     * named: a value's method takes the values its root region demands, and the name a method is
     * filed under is where the module holds it.
     */
    private record Emitted(List<CheckedHelper> helpers, List<CheckedValue> values,
                           List<CheckedValueEntry> valueEntries,
                           Map<String, CheckedHelper> rowValues) {}

    /**
     * {@link Emitted} for {@code module}, off what its check emitted.
     *
     * <p>What each method takes and its body are the check's, read whole; what the calls in this
     * module reach it by is its role's. Both are read here so that a call reaching a method reaches
     * something the snapshot holds.
     *
     * <p>{@link LoweringRole.RowValue} and {@link LoweringRole.PublishedValueEntry} are answered by
     * separate arms even though a row's harness value still comes out as a {@link CheckedHelper}: an
     * entry is not a helper — it is nullary by ADR-0074 and {@link CheckedModule} answers its
     * publication — and folding the two into one arm is the projection issue #1885 refused.
     */
    private static Emitted emittedBy(String module, Bodies.Elaborated checked) {
        List<CheckedHelper> helpers = new ArrayList<>();
        List<CheckedValue> values = new ArrayList<>();
        List<CheckedValueEntry> valueEntries = new ArrayList<>();
        Map<String, CheckedHelper> rowValues = new LinkedHashMap<>();
        checked.emittedDefinitions().forEach((name, emitted) -> {
            switch (emitted.role()) {
                case LoweringRole.ValueHome home ->
                        values.add(new CheckedValue(home.value(), handoversOf(emitted),
                                emitted.body()));
                case LoweringRole.Helper helper ->
                        helpers.add(new CheckedHelper(helper.declaration(), parametersOf(emitted),
                                emitted.body()));
                // What the harness calls, under the name the module holds the method at, which no
                // source declares and which is the only reference to it. A row names it by that
                // name as what computes one of its inputs.
                case LoweringRole.RowValue _ -> {
                    CheckedHelper helper = new CheckedHelper(
                            new ReachName.Own(new ValueName.Helper(module, name)),
                            parametersOf(emitted), emitted.body());
                    helpers.add(helper);
                    rowValues.put(name, helper);
                }
                case LoweringRole.PublishedValueEntry entry -> {
                    if (!emitted.parameters().isEmpty()) {
                        // ADR-0074: the entry takes nothing and answers with the value. A parameter
                        // here is `ValueEntries` having stopped minting the nullary bridge it
                        // promises, which this refuses rather than carries into a program a reader
                        // takes as nullary on that promise.
                        throw new IllegalStateException("`" + entry.value() + "`'s published entry"
                                + " takes " + emitted.parameters().size() + " parameter(s), and ADR-"
                                + "0074 says it takes none");
                    }
                    valueEntries.add(new CheckedValueEntry(entry.value(), emitted.body()));
                }
            }
        });
        return new Emitted(helpers, values, valueEntries, rowValues);
    }

    /** What a helper's method takes: what its source wrote. */
    private static List<CheckedHelper.Parameter> parametersOf(EmittedDefinition emitted) {
        List<CheckedHelper.Parameter> parameters = new ArrayList<>();
        for (EmittedDefinition.Parameter parameter : emitted.parameters()) {
            parameters.add(new CheckedHelper.Parameter(parameter.binder(), parameter.type()));
        }
        return parameters;
    }

    /** What a value's method is handed. {@link EmittedDefinition} holds that it is handed nothing
     *  else. */
    private static List<CheckedValue.Handover> handoversOf(EmittedDefinition emitted) {
        List<CheckedValue.Handover> handovers = new ArrayList<>();
        for (EmittedDefinition.Parameter parameter : emitted.parameters()) {
            switch (parameter) {
                case EmittedDefinition.Handover handover -> handovers.add(new CheckedValue.Handover(
                        handover.binder(), handover.type(), handover.carries()));
                case EmittedDefinition.Declared declared -> throw new IllegalStateException(
                        "a value's method takes `" + declared.binder() + "`, which nothing hands"
                                + " over to it");
            }
        }
        return handovers;
    }
}
