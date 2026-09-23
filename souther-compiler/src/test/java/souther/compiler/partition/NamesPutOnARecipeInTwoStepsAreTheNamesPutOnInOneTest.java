package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeReachName;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A recipe holds the names a position wears as what they come to, and not as the steps that put
 * them on.
 *
 * <p>Which is only sound because the steps have nothing to say the result does not. No names change
 * nothing, names put on in two steps are the same names put on in one, outermost first, and a class
 * with no value keeps what it said about itself whatever is put round it. Each of those is asserted
 * here as an equality of recipes, so that two ways of arriving at one class are one class.
 *
 * <p>Which name goes outside is not decided by any of these — an order reversed everywhere would
 * satisfy all of them. That is pinned against written-out values in {@link
 * ANameGoesBackOnTheWayItCameOffTest}.
 */
class NamesPutOnARecipeInTwoStepsAreTheNamesPutOnInOneTest {

    private static final String MODULE = """
            module demo

            data Rejected
            data Approved = { id: Int }
            data Decision = Approved | Rejected
            data DecisionN = Decision
            data DecisionNN = DecisionN
            """;

    private final RuleReadingSource rules = RuleReadings.ofSource(MODULE);

    private TypeSymbol.AtModule named(String name) {
        return TypeSymbols.declared(new TypeKey(rules.symbols().module(), name));
    }

    private TypeReachName.Written reached(String name) {
        return (TypeReachName.Written) rules.symbols().scope().reach(named(name));
    }

    private final List<TypeReachName.Written> outer = List.of(reached("DecisionNN"));
    private final List<TypeReachName.Written> inner = List.of(reached("DecisionN"));

    private List<TypeReachName.Written> both() {
        List<TypeReachName.Written> out = new ArrayList<>(outer);
        out.addAll(inner);
        return out;
    }

    private RepresentativeSource values() {
        return RepresentativeSource.of(FixtureTemplate.unitCase(reached("Rejected")));
    }

    private RepresentativeSource composed() {
        return new RepresentativeSource.Compose(named("Approved"), List.of());
    }

    private static final RepresentativeSource NOTHING_PRODUCIBLE =
            new RepresentativeSource.NothingProducible("nothing writes one");

    private static final RepresentativeSource NOT_ARRIVED_AT =
            new RepresentativeSource.NotArrivedAt(Set.of(),
                    Set.of(CompositionRepertoire.PLACES_IN_A_RUN_THAT_ARE_NAMED), "stopped");

    @Test
    void noNamesLeaveAValueAsItIs() {
        assertEquals(values(), RepresentativeSource.under(List.of(), values()));
    }

    @Test
    void noNamesLeaveACompositionAsItIs() {
        assertEquals(composed(), RepresentativeSource.under(List.of(), composed()));
    }

    @Test
    void namesPutOnAValueInTwoStepsAreTheNamesPutOnInOne() {
        assertEquals(RepresentativeSource.under(both(), values()),
                RepresentativeSource.under(outer, RepresentativeSource.under(inner, values())));
    }

    @Test
    void namesPutOnACompositionInTwoStepsAreTheNamesPutOnInOne() {
        assertEquals(RepresentativeSource.under(both(), composed()),
                RepresentativeSource.under(outer, RepresentativeSource.under(inner, composed())));
    }

    @Test
    void aNameRoundAClassNothingCanProduceLeavesWhatItSaid() {
        assertEquals(NOTHING_PRODUCIBLE, RepresentativeSource.under(both(), NOTHING_PRODUCIBLE));
    }

    @Test
    void aNameRoundAClassNothingReachedLeavesWhatItSaid() {
        assertEquals(NOT_ARRIVED_AT, RepresentativeSource.under(both(), NOT_ARRIVED_AT));
    }

    /**
     * A class nothing was reached for and nothing stopped is a search that looked everywhere, which
     * is {@link RepresentativeSource.NothingProducible} and says so.
     */
    @Test
    void aClassNothingReachedSaysWhatStoppedTheReaching() {
        assertThrows(IllegalArgumentException.class,
                () -> new RepresentativeSource.NotArrivedAt(Set.of(), Set.of(), "stopped"));
    }
}
