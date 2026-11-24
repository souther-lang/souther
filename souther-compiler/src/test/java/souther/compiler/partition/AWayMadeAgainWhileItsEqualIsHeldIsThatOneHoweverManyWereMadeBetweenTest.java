package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.ResolvedCase;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A condition of several ways made again while an equal one is held is that one, so the ways
 * inside one another are the same objects and comparing two of them stops at the first. A way
 * pushed out by others made since was made again as a second equal object, and the comparison of
 * two went down both through every way inside, as many as there are paths to it.
 */
class AWayMadeAgainWhileItsEqualIsHeldIsThatOneHoweverManyWereMadeBetweenTest {

    private static final ConditionReportAnchor WHERE =
            new ConditionReportAnchor.WhereTheReadingMetIt("m",
                    new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, 0));

    private static final TermPath KIND = TermPath.of("k");

    private static OnTheWay narrowedTo(String name) {
        TypeSymbol leaf = TypeSymbols.declared(new TypeKey("m", name));
        CasesLeft only = CasesLeft.of(ResolvedCase.of(CaseSelector.direct(leaf), List.of(leaf)));
        return new OnTheWay.Narrowed(WHERE, KIND.refine(only), List.of(), List.of(),
                NamedElements.NONE);
    }

    private static OnTheWay.OneOf wayAt(int ordinal) {
        return OnTheWay.OneOf.of(
                new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, ordinal),
                WHERE, List.of(List.of(narrowedTo("A")), List.of(narrowedTo("B"))),
                Optional.empty());
    }

    @Test
    void aWayMadeAgainIsTheOneHeldHoweverManyOthersWereMadeSince() {
        OnTheWay.OneOf held = wayAt(1);
        List<OnTheWay.OneOf> others = new ArrayList<>();
        for (int ordinal = 2; ordinal < 100_000; ordinal++) {
            others.add(wayAt(ordinal));
        }
        assertSame(held, wayAt(1));
        assertSame(others.getLast(), wayAt(99_999));
    }
}
