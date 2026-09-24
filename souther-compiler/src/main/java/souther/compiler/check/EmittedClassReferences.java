package souther.compiler.check;

import souther.compiler.core.BlockReaches;
import souther.compiler.core.Core;
import souther.compiler.types.Refinement;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashSet;
import java.util.Set;

/**
 * The classes of declared types that emitting a typed definition names, read off the tree the
 * emitter reads.
 *
 * <p>Two kinds of thing name a class. What the emitter decides from a form and its types — a
 * construction, a unit data written as a value, the case a {@code match} tests against, the type
 * whose fields are read, and the enumeration a comparison or a sort takes its order from — is asked
 * of the same questions the emitter asks ({@link Ordering}, {@link Comparison}). The enumeration is
 * the reason this is read off a typed body and not the written one: {@code Qualified < Won} names two
 * cases, and the class the order comes from is the sum they belong to, which only the types say.
 *
 * <p>And a value of a declared type is cast to its class wherever it comes out of something the JVM
 * holds as an object: a method's parameter, a call's result, an element of a tuple. That a node has a
 * declared type is not enough to name its class: a local that widens a case to its sum is held and
 * compared as an object and the sum's class is never named. So the type of a node is counted at the
 * kinds of node that cast to it, and nowhere else.
 */
final class EmittedClassReferences {

    private final NewtypeInners inners;
    private final Symbols symbols;
    private final DeclarationKinds kinds;
    private final PublishedDeclarations published;
    private final Set<TypeSymbol.AtModule> found = new LinkedHashSet<>();

    private EmittedClassReferences(NewtypeInners inners, Symbols symbols, DeclarationKinds kinds,
                                   PublishedDeclarations published) {
        this.inners = inners;
        this.symbols = symbols;
        this.kinds = kinds;
        this.published = published;
    }

    /** What a body emitted inline names. */
    static Set<TypeSymbol.AtModule> of(Core body, NewtypeInners inners, Symbols symbols,
                                       DeclarationKinds kinds, PublishedDeclarations published) {
        EmittedClassReferences walk = new EmittedClassReferences(inners, symbols, kinds, published);
        walk.visit(body, null);
        return walk.found;
    }

    /** What a definition emitted as a method of its own names: what it takes, and its body. */
    static Set<TypeSymbol.AtModule> of(EmittedDefinition definition, NewtypeInners inners,
                                       Symbols symbols, DeclarationKinds kinds,
                                       PublishedDeclarations published) {
        EmittedClassReferences walk = new EmittedClassReferences(inners, symbols, kinds, published);
        for (EmittedDefinition.Parameter parameter : definition.parameters()) {
            walk.add(parameter.type());
        }
        walk.visit(definition.body(), null);
        return walk.found;
    }

    /**
     * What each kind of node has the emitter do with a declared type's class. A type held in a local,
     * passed along, or compared for equality is held as an object and names no class, so a node's
     * type is counted only where the emitter casts to it: a value that comes out of a method's result,
     * an element of a tuple, a function's parameter, the bound value of an arm, what a function
     * captures, and the shape a position asks an {@code unreachable} to leave. Listed for every kind
     * rather than left to a default, so that a kind of node added to Core stops compiling here until
     * it is said which it is.
     *
     * @param expected the shape the position this stands in asks for, or null where it asks for
     *                 nothing — which is what the top of an expanded body is asked, its reader's own
     *                 positions naming only what its reader can
     */
    private void visit(Core e, Type expected) {
        switch (e) {
            case Core.Construct built -> add(built.typeName());
            case Core.UnitValue unit -> add(unit.data());
            case Core.Match match -> {
                for (Core.Case arm : match.cases()) {
                    arm.pattern().selectors().forEach(selector -> {
                        if (selector.refinement() instanceof Refinement.Direct) {
                            add(selector.name());
                        }
                    });
                    // What an arm binds is cast to the type it is bound as, where it is cast at all.
                    add(arm.castOnBinding(match.scrutinee().type()));
                }
            }
            case Core.Binary bin -> comparedBy(bin);
            // A result comes back as an object and is cast to the type the call answers — unless the
            // call is the loop it stands for, which is emitted where it is and calls nothing.
            case Core.Call call -> {
                if (call.stepRunWhereItStands(symbols.theWalk()) == null) {
                    add(call.type());
                }
                sortedBy(call);
            }
            case Core.Apply apply -> add(apply.type());
            case Core.TupleGet element -> add(element.type());
            // A field is read off the class of the value it is read from.
            case Core.FieldAccess access -> add(access.target().type());
            // A function handed over as a value is a class of its own: its parameters come in as
            // objects and are cast to their types, and what it reaches of the body around it is a
            // field and a constructor argument. What it reaches is the one answer BlockReaches gives.
            // A step the emitter runs where it stands is not this: it is read by
            // visitStepRunWhereItStands, from the same answer the emitter asks.
            case Core.Block block -> {
                if (block.type() instanceof Type.FnOf fn) {
                    fn.params().forEach(this::add);
                }
                BlockReaches.of(block, Set.of()).bindings().forEach(read -> add(read.type()));
            }
            // The abort leaves a value of the shape its position asks for, cast to it.
            case Core.Unreachable abort -> add(abort.shapeAt(expected));
            case Core.Int _, Core.Decimal _, Core.Str _, Core.Bool _, Core.Temporal _,
                 Core.Read _, Core.MaterialisedValue _, Core.Neg _, Core.PreservedCall _,
                 Core.If _, Core.IfConstructed _, Core.LetIn _, Core.ListLit _,
                 Core.OptionSome _, Core.OptionNone _, Core.Tuple _, Core.Widen _ -> { }
        }
        visitChildren(e, expected);
    }

    /**
     * The children of {@code e}, each asked for what the emitter asks it for. Only a branch, an arm
     * and the body of a {@code let} are asked for the shape their position holds, and a {@code let}
     * asks its value for that value's own type; every other slot asks for nothing.
     */
    private void visitChildren(Core e, Type expected) {
        switch (e) {
            case Core.If iff -> {
                Type want = Core.shapeOf(iff, expected);
                visit(iff.cond(), null);
                visit(iff.then(), want);
                visit(iff.els(), want);
            }
            case Core.IfConstructed attempt -> {
                Type want = Core.shapeOf(attempt, expected);
                visit(attempt.construct(), null);
                visit(attempt.then(), want);
                attempt.els().forEach(arm -> visit(arm.body(), want));
            }
            case Core.Match match -> {
                Type want = Core.shapeOf(match, expected);
                visit(match.scrutinee(), null);
                match.cases().forEach(arm -> visit(arm.body(), want));
            }
            case Core.LetIn binding -> {
                visit(binding.value(), binding.value().type());
                visit(binding.body(), expected);
            }
            // What it holds is asked for what the position it stands in asks for, as the emitter
            // asks it.
            case Core.Widen widen -> visit(widen.value(), expected);
            case Core.Call call -> {
                for (int i = 0; i < call.args().size(); i++) {
                    Core arg = call.args().get(i);
                    if (!(arg.type() instanceof Type.FnOf)) {
                        visit(arg, null);
                        continue;
                    }
                    // What the emitter does with a function it is handed is asked of the call.
                    switch (call.functionArgument(i, symbols.theWalk())) {
                        case RUNS_WHERE_IT_STANDS -> visitStepRunWhereItStands(
                                call.stepRunWhereItStands(symbols.theWalk()));
                        // Replaced by `Fn.NEVER`: no class and no body of it is emitted.
                        case NEVER_APPLIED -> { }
                        case HANDED_OVER -> visit(arg, null);
                    }
                }
            }
            default -> Core.forEachChild(e, child -> visit(child, null));
        }
    }

    /**
     * A step the emitter runs as the loop body: no class is made for it, so what it closes over is
     * read from the frame around it and names nothing. What it is handed is the element of the list,
     * cast to its type, and its body is emitted where it stands.
     */
    private void visitStepRunWhereItStands(Core.Block step) {
        add(((Type.FnOf) step.type()).params().get(1));
        visit(step.body(), null);
    }

    /** The enumeration a comparison that places a value on an order takes it from. */
    private void comparedBy(Core.Binary bin) {
        Comparison comparison = Comparison.of(bin).orElse(null);
        if (comparison != null && comparison.claim() instanceof ComparisonClaim.Cut) {
            Ordering how = Ordering.ofComparison(comparison, inners, symbols, kinds, published);
            if (how != null && how.opened() instanceof Ordering.Places places) {
                add(places.enumeration());
            }
        }
    }

    /**
     * The enumeration a sort, a maximum or a minimum takes its order from: what the checker settled
     * the ordering was checked against, which is the emitter's own reading of the call.
     */
    private void sortedBy(Core.Call call) {
        if (call.settlement() instanceof Core.CallSettlement.OrderingSubject ordered) {
            add(Ordering.enumerationOfHeld(ordered.type(), inners, symbols, kinds, published));
        }
    }

    private void add(Type type) {
        if (type instanceof Type.Ref ref) {
            add(ref.name());
        }
    }

    private void add(TypeSymbol type) {
        if (type instanceof TypeSymbol.AtModule at) {
            found.add(at);
        }
    }
}
