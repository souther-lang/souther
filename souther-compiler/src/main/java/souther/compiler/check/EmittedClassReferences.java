package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.core.Kernel;
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
 * holds as an object: a method's parameter, a call's result, an element of a collection. So a node
 * whose type is a declared type, and a parameter of one, are counted as they stand and not by asking
 * each place that casts, of which there are several and more may be added.
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

    private void visit(Core e) {
        add(e.type());
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
                }
            }
            case Core.Binary bin -> comparedBy(bin);
            case Core.Call call -> sortedBy(call);
            default -> { }
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

    /** The enumeration a sort, a maximum or a minimum takes its order from. */
    private void sortedBy(Core.Call call) {
        if (call.fn() instanceof Core.Reached.OfKernel(_, Kernel kernel)
                && Ordering.SORT_FAMILY.contains(kernel)) {
            add(Ordering.sortEnumeration(kernel, call.args().get(0).type(), inners, symbols, kinds,
                    published));
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
