package souther.compiler.program;

import souther.compiler.ast.Ast;
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
import souther.compiler.core.EnsuresEnforcement;
import souther.compiler.core.ValueShape;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Acceptance;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Compositions;
import souther.compiler.query.Db;
import souther.compiler.query.Front;
import souther.compiler.query.Names;
import souther.compiler.query.Shapes;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
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
        List<CheckedModule> modules = new ArrayList<>();
        for (String module : compilation.modules()) {
            modules.add(moduleOf(db, module));
        }
        return new CheckedProgram(modules, languageDataOf(db), declaredOnThePath(db));
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
        Stdlib stdlib = db.ask(new Front.Library()).value();
        if (stdlib == null) {
            throw new IllegalStateException("this compilation was checked against no library");
        }
        Symbols language = Symbols.none(stdlib);
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
            declared.add(declaredAs(def, language, Map.of()));
        }
        return declared;
    }

    /**
     * Every declaration this compile read off the path: the identities it resolved against a module
     * it did not check.
     *
     * <p>Taken from what the front end read rather than from what is left over. A reader asking
     * about one of these is asking about a declaration that was made when that module was compiled,
     * so what is recorded here is that the compile found the name among what that module declares —
     * and an identity nothing declares reaches none of this and is refused instead.
     *
     * <p>The identities and not the declarations. What one is made of belongs to the compile that
     * made it, and reading it here would be this compiler deciding a second time what another one
     * already settled.
     *
     * <p>Each identity comes off the declaration that says which one it is. Paired together out of
     * the module a declaration was read under and the name it is indexed by, it would be this
     * answering for a declaration whatever the two strings came from.
     */
    private static Set<TypeSymbol.AtModule> declaredOnThePath(Db db) {
        Front.FromPath.Of read = db.ask(new Front.FromPath()).value();
        Set<TypeSymbol.AtModule> declared = new LinkedHashSet<>();
        if (read == null) {
            return declared;
        }
        for (Front.FromPath.OnThePath onThePath : read.modules().values()) {
            for (Ast.Def def : onThePath.declarations().values()) {
                declared.add(TypeSymbols.declared(def.declaredKey()));
            }
        }
        return declared;
    }

    private static CheckedModule moduleOf(Db db, String module) {
        Bodies.Elaborated checked = db.ask(new Bodies.Checked(module)).value();
        Lower.Lowered lowering = db.ask(new Bodies.Lowering(module)).value();
        Map<String, Sig> signatures = db.ask(new Bodies.Signatures(module)).value();
        Map<String, BehaviorImplementation> implementations =
                db.ask(new Bodies.Implementation(module)).value();
        Map<ValueName.Behavior, Composition> compositions =
                db.ask(new Compositions.Of(module)).value();
        // What a value of each declared data is made of and must satisfy, and where each behavior's
        // clause is checked. Both are what the language decided and both are read here rather than
        // worked out: the JVM is handed the same two answers, so an output reading this program and
        // the bytecode beside it hold one another's decisions.
        Map<TypeSymbol.AtModule, ValueShape> shapes =
                db.ask(new Shapes.ValueShapes(module)).value();
        Map<ValueName.Behavior, EnsuresEnforcement> checks =
                db.ask(new Bodies.EnsuresChecks(module)).value();
        // What the module's names mean over the derived declarations, which is what a declaration's
        // fields and a sum's cases are read against. It is a way of reaching the compiler's answers
        // and not one of them: it holds a registry that asks `db` for each declaration, so it is
        // read here and dropped here, and nothing it was reached through is carried into what is
        // made.
        Symbols symbols = Names.derivedSymbols(db, module).value();
        if (checked == null || lowering == null || signatures == null || implementations == null
                || compositions == null || symbols == null || shapes == null || checks == null) {
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
        List<CheckedBehavior> behaviors = new ArrayList<>();
        for (Hir.BehaviorDef declared : bodies.behaviors()) {
            ValueName.Behavior named = new ValueName.Behavior(module, declared.name());
            behaviors.add(new CheckedBehavior(named, signatureOf(signatures.get(declared.name())),
                    implementationOf(named, declared, bodies, implementations, checked,
                            compositions),
                    EnsuresEnforcement.in(checks, module, named)));
        }
        return new CheckedModule(module, behaviors, helpersOf(module, bodies, checked),
                dataOf(declarations, symbols, shapes));
    }

    /**
     * What the module declares.
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
     *
     * <p>The list is what the module holds and its order is not answered for. A declaration written
     * on its own and one a sum's case list declares reach {@code defs} by different routes, so
     * where either stands among them is how the front end put them there rather than something the
     * language decided. The two orders that are decided are inside a declaration —
     * {@link CheckedData.Product#fields} and {@link CheckedData.Sum#cases} — and those are the
     * ones said out loud.
     */
    private static List<CheckedData> dataOf(Hir.Module declarations, Symbols symbols,
                                           Map<TypeSymbol.AtModule, ValueShape> shapes) {
        List<CheckedData> declared = new ArrayList<>();
        for (Hir.Def def : declarations.defs()) {
            declared.add(declaredAs(def, symbols, shapes));
        }
        return declared;
    }

    /**
     * One declaration, in whichever of the three forms it was written.
     *
     * <p>One reading for both worlds. A module's declaration and the language's are the same kind
     * of thing — they resolve and type alike and a value of either lays out alike — and this is
     * where that stops being something two readings agree about.
     */
    private static CheckedData declaredAs(Hir.Def def, Symbols symbols,
                                          Map<TypeSymbol.AtModule, ValueShape> shapes) {
        return switch (def) {
            case Hir.Data product -> productOf(product, shapes);
            case Hir.SumData sum -> new CheckedData.Sum(sum.declares(),
                    AtomSpace.subjectAtoms(Type.ref(sum.declares()), symbols));
            case Hir.UnitData unit -> new CheckedData.Unit(unit.declares());
        };
    }

    /**
     * One product, as the check answered what a value of it is made of.
     *
     * <p>Handed over and not rebuilt. The fields, the binding each is read through and the clauses
     * that must hold of a value are one answer of the checker's, and the JVM emits a construction
     * from that same answer — so what an output outside this compiler reads and what the bytecode
     * refuses a value by cannot come apart.
     */
    private static CheckedData productOf(Hir.Data product,
                                         Map<TypeSymbol.AtModule, ValueShape> shapes) {
        ValueShape shape = shapes.get(product.declares());
        if (shape == null) {
            // The module was taken as checked, and a declaration of it has no answer for what a
            // value of it is. Handing over a product with no clauses would be saying that anything
            // its fields admit is one of it, which is the opposite of what the author wrote.
            throw new IllegalStateException("`" + product.declares() + "` was taken as checked and"
                    + " the check said nothing about what a value of it is");
        }
        return new CheckedData.Product(shape);
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
