package souther.compiler.check;

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
        walk.visit(body);
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
        walk.visit(definition.body());
        return walk.found;
    }

    /**
     * What each kind of node has the emitter do with a declared type's class. A type held in a local,
     * passed along, or compared for equality is held as an object and names no class, so a node's
     * type is counted only where the emitter casts to it: a value that comes out of a method's result,
     * an element of a tuple, a function's parameter, the bound value of an arm. Listed for every kind
     * rather than left to a default, so that a kind of node added to Core stops compiling here until
     * it is said which it is.
     */
    private void visit(Core e) {
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
                    // What an arm binds is cast to the type it is bound as.
                    if (arm.binder() != null) {
                        add(arm.pattern().bindType());
                    }
                }
            }
            case Core.Binary bin -> comparedBy(bin);
            // A result comes back as an object and is cast to the type the call answers.
            case Core.Call call -> {
                add(call.type());
                sortedBy(call);
            }
            case Core.Apply apply -> add(apply.type());
            case Core.TupleGet element -> add(element.type());
            // A field is read off the class of the value it is read from.
            case Core.FieldAccess access -> add(access.target().type());
            // A function's parameters come in as objects and are cast to their types.
            case Core.Block block -> {
                if (block.type() instanceof Type.FnOf fn) {
                    fn.params().forEach(this::add);
                }
            }
            case Core.Int _, Core.Decimal _, Core.Str _, Core.Bool _, Core.Temporal _,
                 Core.Read _, Core.MaterialisedValue _, Core.Neg _, Core.PreservedCall _,
                 Core.If _, Core.IfConstructed _, Core.LetIn _, Core.ListLit _,
                 Core.OptionSome _, Core.OptionNone _, Core.Tuple _, Core.Unreachable _ -> { }
        }
        Core.forEachChild(e, this::visit);
    }

    /** The enumeration a comparison that places a value on an order takes it from. */
    private void comparedBy(Core.Binary bin) {
        if (Comparison.of(bin).map(Comparison::claim).orElse(null)
                instanceof ComparisonClaim.Cut) {
            Ordering how = Ordering.ofComparison(bin.left().type(), bin.right().type(), inners,
                    symbols, kinds, published);
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
