package souther.compiler.program;

import souther.compiler.ast.Hir;
import souther.compiler.check.AtomSpace;
import souther.compiler.check.BehaviorImplementation;
import souther.compiler.check.CoreBinders;
import souther.compiler.check.Lower;
import souther.compiler.check.Sig;
import souther.compiler.check.SpecImplementation;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.core.Composition;
import souther.compiler.core.Core;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Acceptance;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Compositions;
import souther.compiler.query.Db;
import souther.compiler.query.Names;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

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
        List<CheckedModule> modules = new ArrayList<>();
        for (String module : compilation.modules()) {
            modules.add(moduleOf(db, module));
        }
        return new CheckedProgram(modules);
    }

    private static CheckedModule moduleOf(Db db, String module) {
        Bodies.Elaborated checked = db.ask(new Bodies.Checked(module)).value();
        Lower.Lowered lowering = db.ask(new Bodies.Lowering(module)).value();
        Map<String, Sig> signatures = db.ask(new Bodies.Signatures(module)).value();
        Map<String, BehaviorImplementation> implementations =
                db.ask(new Bodies.Implementation(module)).value();
        Map<ValueName.Behavior, Composition> compositions =
                db.ask(new Compositions.Of(module)).value();
        // What the module's names mean over the derived declarations, which is what a declaration's
        // fields and a sum's cases are read against. It is a way of reaching the compiler's answers
        // and not one of them: it holds a registry that asks `db` for each declaration, so it is
        // read here and dropped here, and nothing it was reached through is carried into what is
        // made.
        Symbols symbols = Names.derivedSymbols(db, module).value();
        if (checked == null || lowering == null || signatures == null || implementations == null
                || compositions == null || symbols == null) {
            // Not a report: the failure above is what a caller is told, and reaching here past it
            // means the two readings of whether this program checked have come apart.
            throw new IllegalStateException("`" + module + "` was taken as checked and is not");
        }
        Hir.Module lowered = lowering.lowered();
        List<CheckedBehavior> behaviors = new ArrayList<>();
        for (Hir.BehaviorDef declared : lowered.behaviors()) {
            ValueName.Behavior named = new ValueName.Behavior(module, declared.name());
            behaviors.add(new CheckedBehavior(named, signatureOf(signatures.get(declared.name())),
                    implementationOf(named, declared, lowered, implementations, checked,
                            compositions)));
        }
        return new CheckedModule(module, behaviors, helpersOf(module, lowered, checked),
                dataOf(lowered, symbols));
    }

    /**
     * What the module declares, in the order the declarations are written.
     *
     * <p>Each of the three forms is materialised from the answer this compiler already has for it,
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
     */
    private static List<CheckedData> dataOf(Hir.Module lowered, Symbols symbols) {
        List<CheckedData> declared = new ArrayList<>();
        for (Hir.Def def : lowered.defs()) {
            declared.add(switch (def) {
                case Hir.Data product -> productOf(product, symbols);
                case Hir.SumData sum -> new CheckedData.Sum(sum.declares(),
                        AtomSpace.subjectAtoms(Type.ref(sum.declares()), symbols));
                case Hir.UnitData unit -> new CheckedData.Unit(unit.declares());
            });
        }
        return declared;
    }

    /** One product, its fields in the order {@link TypeOps#fieldTypes} lays them out. */
    private static CheckedData productOf(Hir.Data product, Symbols symbols) {
        List<CheckedData.Field> fields = new ArrayList<>();
        TypeOps.fieldTypes(product, symbols)
                .forEach((field, type) -> fields.add(new CheckedData.Field(field, type)));
        return new CheckedData.Product(product.declares(), fields);
    }

    /**
     * What the behavior takes and answers, as types.
     *
     * <p>The reading of a boundary the compiler's own signature carries as well — which of a
     * {@code Map}'s key readings admitted it, and the witness that says so — is left behind here.
     * That witness offers the module as it was parsed, so a signature handed over whole would put
     * the syntax tree two hops from a behavior's declared output.
     */
    private static CheckedSignature signatureOf(Sig signature) {
        return new CheckedSignature(signature.inputTypes(), signature.outputType());
    }

    /**
     * Which of the four states this behavior's implementation is in.
     *
     * <p>Read in one place, from the state the declarations were read into and the form the check
     * produced. A reader handed the two separately would be deciding for itself what an implemented
     * behavior with no Core is, and it is a composition — which is a fact about the declaration and
     * not something to infer from an absence.
     */
    private static CheckedImplementation implementationOf(
            ValueName.Behavior named, Hir.BehaviorDef declared, Hir.Module lowered,
            Map<String, BehaviorImplementation> implementations, Bodies.Elaborated checked,
            Map<ValueName.Behavior, Composition> compositions) {
        String name = declared.name();
        BehaviorImplementation state = implementations.get(name);
        if (state == null || state == BehaviorImplementation.UNIMPLEMENTED) {
            return new CheckedImplementation.Unwritten();
        }
        if (state == BehaviorImplementation.INJECTION_TARGET) {
            return new CheckedImplementation.Injected();
        }
        Composition composed = compositions.get(named);
        if (composed != null) {
            return new CheckedImplementation.Composed(composed);
        }
        return new CheckedImplementation.Body(inputBindersOf(named, declared, lowered),
                checked.behaviorBodies().get(name));
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
     * signature the two lengths would be equal by construction, and {@link CheckedBehavior}'s check
     * of them would be comparing an answer with itself — the disagreement it is there to refuse
     * would arrive instead as a dependency's binder handed over as an input's.
     */
    private static List<Core.Binder> inputBindersOf(ValueName.Behavior named,
                                                    Hir.BehaviorDef declared, Hir.Module lowered) {
        SpecImplementation.Implemented implemented =
                declared instanceof Hir.SpecBehavior spec
                        ? SpecImplementation.implementedBy(lowered, spec)
                        : null;
        if (implemented == null) {
            // This behavior was taken as implemented here and by a body of its own, and the module
            // has no definition to read one from. Nothing here can put that right, and letting it
            // through would hand an output a body whose reads resolve to nothing it was given.
            throw new IllegalStateException("`" + named.module() + "." + named.name()
                    + "` was taken as having a body and has no definition to read it from");
        }
        List<Core.Binder> binders = new ArrayList<>();
        for (Hir.FnParam input : implemented.inputs()) {
            binders.add(CoreBinders.of(input.binder()));
        }
        return binders;
    }

    /**
     * The helpers this module emits as definitions of their own.
     *
     * <p>A helper's body is the check's; what it takes is the definition's, which the check did not
     * rewrite. Both are read here so that a call reaching a helper reaches something the snapshot
     * holds.
     */
    private static List<CheckedHelper> helpersOf(String module, Hir.Module lowered,
                                                 Bodies.Elaborated checked) {
        Map<String, Hir.FnDef> defined = new LinkedHashMap<>();
        for (Hir.FnDef fn : lowered.fns()) {
            defined.put(fn.name(), fn);
        }
        for (Hir.FnDef fn : lowered.takenOn()) {
            defined.put(fn.name(), fn);
        }
        List<CheckedHelper> helpers = new ArrayList<>();
        checked.emittedHelpers().forEach((name, body) -> {
            Hir.FnDef fn = defined.get(name);
            if (fn == null) {
                // A call in a body reaches this helper by name, so a snapshot without it hands an
                // output a call to something it was never given. Nothing here can put that right,
                // and letting it through is what makes it the reader's problem.
                throw new IllegalStateException("the checked helper `" + module + "." + name
                        + "` has no definition to read what it takes from");
            }
            List<CheckedHelper.Parameter> parameters = new ArrayList<>();
            for (Hir.FnParam parameter : fn.params()) {
                parameters.add(new CheckedHelper.Parameter(CoreBinders.of(parameter.binder()),
                        TypeOps.resolveParamType(parameter.type())));
            }
            helpers.add(new CheckedHelper(new ValueName.Helper(module, name), parameters, body));
        });
        return helpers;
    }
}
