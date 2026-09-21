package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.core.Kernel;
import souther.compiler.types.Refinement;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashSet;
import java.util.Set;

/**
 * The classes of declared types that emitting a typed body names, read off the tree the emitter reads.
 *
 * <p>A construction, a unit data written as a value, the case a {@code match} tests against, the
 * type whose fields are read, and the enumeration a comparison or a sort takes its order from are
 * each a class the emitted method refers to. The last is the reason this is read off a typed body
 * and not the written one: {@code Qualified < Won} names two cases, and the class the order comes
 * from is the sum they belong to, which only the types say.
 *
 * <p>Each answer here is the one the emitter arrives at, by asking what it asks — {@link Ordering},
 * {@link Comparison} — and not by a second reading of the same tree.
 */
final class EmittedClassReferences {

    private static final Set<Kernel> ORDERED_BY_COMPARATOR =
            Set.of(Kernel.LIST_SORT, Kernel.LIST_MAX, Kernel.LIST_MIN, Kernel.LIST_SORT_BY);

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

    static Set<TypeSymbol.AtModule> of(Core body, NewtypeInners inners, Symbols symbols,
                                       DeclarationKinds kinds, PublishedDeclarations published) {
        EmittedClassReferences walk = new EmittedClassReferences(inners, symbols, kinds, published);
        walk.visit(body);
        return walk.found;
    }

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
                }
            }
            case Core.FieldAccess access -> {
                if (access.target().type() instanceof Type.Ref owner) {
                    add(owner.name());
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
        if (!(call.fn() instanceof Core.Reached.OfKernel(_, Kernel kernel))
                || !ORDERED_BY_COMPARATOR.contains(kernel)) {
            return;
        }
        Type ordered = kernel == Kernel.LIST_SORT_BY
                ? (call.args().get(0).type() instanceof Type.FnOf key ? key.result() : null)
                : (call.args().get(0).type() instanceof Type.ListOf list ? list.element() : null);
        Ordering how = ordered == null ? null : Ordering.of(ordered, inners, symbols, kinds, published);
        if (how != null && how.asHeld() instanceof Ordering.Places places) {
            add(places.enumeration());
        }
    }

    private void add(TypeSymbol type) {
        if (type instanceof TypeSymbol.AtModule at) {
            found.add(at);
        }
    }
}
