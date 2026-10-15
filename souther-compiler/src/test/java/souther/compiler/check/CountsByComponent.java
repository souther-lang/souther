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
    private final boolean handsOnWhatANameOpensOnto;
    private final Map<TypeSymbol, Cardinality> known = new HashMap<>();
    private final Map<TypeSymbol, Unwrapping> opened = new HashMap<>();

    private CountsByComponent(RuleReadingContext reading, boolean handsOnWhatANameOpensOnto) {
        this.reading = reading;
        this.premises = TypeCardinality.Premises.read(reading);
        this.handsOnWhatANameOpensOnto = handsOnWhatANameOpensOnto;
    }

    /** What {@code declarations} and everything they reach come to. */
    static TypeCardinality.Cardinalities of(List<Hir.Def> declarations, RuleReadingSource source,
                                            ReadingPolicy policy) {
        return of(declarations, RuleReadingContext.unshared(source, policy), true);
    }

    /** The same, with what somebody has already made of each declaration borrowed from
     *  {@code machines}. */
    static TypeCardinality.Cardinalities of(List<Hir.Def> declarations, RuleReadingSource source,
                                            ReadingPolicy policy, DeclarationReadings machines) {
        return of(declarations, RuleReadingContext.of(source, policy, machines), true);
    }

    /**
     * The same, with every count that reaches a name worn over a value opening it all the way down
     * rather than being handed what opening it found when it was answered.
     *
     * <p>The reading a count makes with nothing handed on, which is what one that is handed what a
     * name opens onto has to come to.
     */
    static TypeCardinality.Cardinalities openingEveryName(List<Hir.Def> declarations,
                                                          RuleReadingSource source,
                                                          ReadingPolicy policy) {
        return of(declarations, RuleReadingContext.unshared(source, policy), false);
    }

    private static TypeCardinality.Cardinalities of(List<Hir.Def> declarations,
                                                    RuleReadingContext reading,
                                                    boolean handsOnWhatANameOpensOnto) {
        CountsByComponent counts = new CountsByComponent(reading, handsOnWhatANameOpensOnto);
        return TypeCardinality.assembled(declarations.stream().map(Hir.Def::declares).toList(),
                reading, counts.premises, counts);
    }

    @Override
    public Cardinality of(TypeSymbol name) {
        answer(name);
        return known.get(name);
    }

    @Override
    public Unwrapping unwrappingOf(TypeSymbol name) {
        if (!handsOnWhatANameOpensOnto) {
            return null;
        }
        answer(name);
        return opened.get(name);
    }

    private void answer(TypeSymbol name) {
        if (known.containsKey(name)) {
            return;
        }
        List<TypeSymbol> component = TypeCardinality.componentOf(name, reading.source());
        if (component.isEmpty()) {
            return;
        }
        // Answered where the component is named, as the store answers it, so that a component is
        // risen through once however many of its members are asked about.
        if (!component.get(0).equals(name)) {
            answer(component.get(0));
            return;
        }
        TypeCardinality.Counted counted =
                TypeCardinality.ofComponent(component, reading, premises, this);
        known.putAll(counted.counts());
        opened.putAll(counted.unwrapping());
    }
}
