package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which declarations have to be answered together, and in which order the rest are answered, is
 * settled by the graph and not by how the graph was put together.
 *
 * <p>The walk chooses twice — which declaration to start from, and which of the ones a declaration
 * reads to go to next — and both were being chosen by the iteration order of a mapping and a set.
 * Neither of those can see the order it was filled in, so two callers holding the same graph could
 * be handed components in two different orders, and in two different orders inside each component,
 * with nothing able to tell the two answers apart. What is downstream of this is a report naming
 * the declarations of a group, so the names an author is shown could come out either way round.
 *
 * <p>The two graphs below hold the same declarations and the same edges and were built in
 * different orders, at both places the walk chooses. What they are answered with is one answer.
 */
class WhichDeclarationsAreAnsweredTogetherIsAnAnswerAboutTheGraphTest {

    private static TypeSymbol named(String name) {
        return TypeSymbols.declared(new TypeKey("demo", name));
    }

    private static final TypeSymbol READS_TWO = named("Aa");
    private static final TypeSymbol ONE_IT_READS = named("Bb");
    private static final TypeSymbol THE_OTHER_IT_READS = named("Cc");
    private static final TypeSymbol ON_ITS_OWN = named("Dd");

    /** {@code Aa} reads {@code Bb} and {@code Cc}; {@code Dd} reads nothing and is read by none. */
    private static Map<TypeSymbol, Set<TypeSymbol>> graph(List<TypeSymbol> declaredIn,
                                                          List<TypeSymbol> readIn) {
        Map<TypeSymbol, Set<TypeSymbol>> edges = new LinkedHashMap<>();
        for (TypeSymbol each : declaredIn) {
            edges.put(each, each.equals(READS_TWO) ? new LinkedHashSet<>(readIn) : Set.of());
        }
        return edges;
    }

    private static Map<TypeSymbol, Set<TypeSymbol>> oneWayRound() {
        return graph(List.of(ON_ITS_OWN, READS_TWO, ONE_IT_READS, THE_OTHER_IT_READS),
                List.of(THE_OTHER_IT_READS, ONE_IT_READS));
    }

    private static Map<TypeSymbol, Set<TypeSymbol>> theOtherWayRound() {
        return graph(List.of(READS_TWO, ONE_IT_READS, THE_OTHER_IT_READS, ON_ITS_OWN),
                List.of(ONE_IT_READS, THE_OTHER_IT_READS));
    }

    /**
     * One graph built two ways is answered once.
     *
     * <p>The two differ at both places the walk chooses: which declaration it starts from, and
     * which of the two {@code Aa} reads it goes to first. A walk reading either off the container
     * it was handed answers these two differently.
     */
    @Test
    void oneGraphBuiltTwoWaysIsAnsweredOnce() {
        assertEquals(oneWayRound(), theOtherWayRound(),
                "the two hold the same declarations and the same edges");
        assertEquals(TypeComponents.of(oneWayRound()), TypeComponents.of(theOtherWayRound()),
                "so what has to be answered together, and in what order, is the same answer");
    }

    /**
     * And the answer it is, which is what says the ordering is by the names rather than by
     * anything left of how either graph was built.
     */
    @Test
    void andEachDeclarationStandsUnderTheNamesItIsKeyedOn() {
        assertEquals(List.of(List.of(ONE_IT_READS), List.of(THE_OTHER_IT_READS),
                        List.of(READS_TWO), List.of(ON_ITS_OWN)),
                TypeComponents.of(oneWayRound()));
    }

    /**
     * The control: what this answers is still every component before any that reads it.
     *
     * <p>An order of its own, and not the one the names are in — what a reader of these needs is
     * that a declaration is answered after everything it is written in terms of. Sorting the
     * components afterwards would give a mapping-shaped answer that satisfied the check above and
     * broke this one.
     */
    @Test
    void andWhatItReadsStillStandsBeforeIt() {
        List<List<TypeSymbol>> components = TypeComponents.of(oneWayRound());
        int reader = components.indexOf(List.of(READS_TWO));
        assertTrue(reader > components.indexOf(List.of(ONE_IT_READS))
                        && reader > components.indexOf(List.of(THE_OTHER_IT_READS)),
                () -> "a declaration is answered after what it reads: " + components);
    }

    /** And two declarations that read each other are one component, whichever way they were put in. */
    @Test
    void andTwoThatReadEachOtherAreOneComponentEitherWayRound() {
        Map<TypeSymbol, Set<TypeSymbol>> together = new LinkedHashMap<>();
        together.put(THE_OTHER_IT_READS, Set.of(ONE_IT_READS));
        together.put(ONE_IT_READS, Set.of(THE_OTHER_IT_READS));
        Map<TypeSymbol, Set<TypeSymbol>> theOtherWay = new LinkedHashMap<>();
        theOtherWay.put(ONE_IT_READS, Set.of(THE_OTHER_IT_READS));
        theOtherWay.put(THE_OTHER_IT_READS, Set.of(ONE_IT_READS));

        assertEquals(TypeComponents.of(together), TypeComponents.of(theOtherWay));
        assertEquals(List.of(List.of(ONE_IT_READS, THE_OTHER_IT_READS)),
                TypeComponents.of(together),
                "the two are answered together, and stand under their names: which of them came"
                        + " off the walk first is a fact about the walk and not about either");
    }
}
