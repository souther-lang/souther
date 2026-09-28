package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.TypeSymbol;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * A count taken the way a compilation takes one: a component at a time, each handed what the
 * components it reads came to.
 *
 * <p>Here so that what a test about counting exercises is the entry a compilation uses. The store
 * holds one answer per component and asks for the components a count reaches as it reaches them
 * ({@code Shapes.CardinalityOf}); this is the same walk with a map where the store's answers would
 * be, so a test needs no store to reach the kernel a compilation runs.
 *
 * <p>What it is not is the whole-graph entry. That one is kept as the oracle a decomposition is
 * checked against ({@link DecomposingACountDoesNotChangeWhatItReportsTest}), and a test that used it
 * to ask what a declaration comes to would be holding a path no compilation takes.
 */
final class CountsByComponent implements TypeCardinality.Counts {

    private final RuleReadingContext reading;
    private final TypeCardinality.Premises premises;
    private final Map<TypeSymbol, Cardinality> known = new HashMap<>();

    private CountsByComponent(RuleReadingContext reading) {
        this.reading = reading;
        this.premises = TypeCardinality.Premises.read(reading);
    }

    /** What {@code declarations} and everything they reach come to. */
    static TypeCardinality.Cardinalities of(List<Hir.Def> declarations, RuleReadingSource source,
                                            ReadingPolicy policy) {
        return of(declarations, RuleReadingContext.unshared(source, policy));
    }

    /** The same, with what somebody has already made of each declaration borrowed from
     *  {@code machines}. */
    static TypeCardinality.Cardinalities of(List<Hir.Def> declarations, RuleReadingSource source,
                                            ReadingPolicy policy, DeclarationReadings machines) {
        return of(declarations, RuleReadingContext.of(source, policy, machines));
    }

    private static TypeCardinality.Cardinalities of(List<Hir.Def> declarations,
                                                    RuleReadingContext reading) {
        CountsByComponent counts = new CountsByComponent(reading);
        return TypeCardinality.assembled(declarations.stream().map(Hir.Def::declares).toList(),
                reading, counts.premises, counts);
    }

    @Override
    public Cardinality of(TypeSymbol name) {
        if (known.containsKey(name)) {
            return known.get(name);
        }
        List<TypeSymbol> component = TypeCardinality.componentOf(name, reading.source());
        if (component.isEmpty()) {
            return null;
        }
        // Answered where the component is named, as the store answers it, so that a component is
        // risen through once however many of its members are asked about.
        if (!component.get(0).equals(name)) {
            of(component.get(0));
            return known.get(name);
        }
        known.putAll(TypeCardinality.ofComponent(component, reading, premises, this));
        return known.get(name);
    }
}
